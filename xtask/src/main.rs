//! FL4 developer tasks: `cargo xtask <command>`.
//!
//! Every kernel run happens inside a QEMU guest (DESIGN.md §12); nothing here
//! boots FL4 on the host.

use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::{exit, Command, Stdio};
use std::time::{Duration, Instant};

const SEL4TEST_MANIFEST: &[(&str, &str, &str)] = &[
    ("projects/musllibc", "https://github.com/seL4/musllibc.git", "b0005f86fecbd6d0257b15363a5b013446914265"),
    ("tools/nanopb", "https://github.com/nanopb/nanopb", "cad3c18ef15a663e30e3e43e3a752b66378adec1"),
    ("projects/seL4_libs", "https://github.com/seL4/seL4_libs.git", "262a34dcb2f3285be01df9e5404d911132d567a6"),
    ("tools/seL4", "https://github.com/seL4/seL4_tools.git", "6493e0c6fab360eb81a8115a49c9ca7bc280c48a"),
    ("projects/sel4_projects_libs", "https://github.com/seL4/sel4_projects_libs", "b9137c0d905ce966a02b1c9a0c6c0e4beb48223b"),
    ("projects/sel4runtime", "https://github.com/seL4/sel4runtime.git", "86489cf6efab9f314964e79468c036e9035394c7"),
    ("projects/util_libs", "https://github.com/seL4/util_libs.git", "ef49a397b7044fc38b609a99a8c6265a97913b8e"),
];

/// Tests that hang on upstream seL4 too under QEMU (sel4test marks them
/// flaky in simulation).
const QEMU_FLAKY: &[&str] = &["INTERRUPT0005"];

/// Tests that fail intermittently on upstream seL4 under QEMU/KVM in the
/// same way (sel4test names them "flaky"): a failure of one of these is
/// reported but does not fail the run.
const UPSTREAM_FLAKY: &[&str] = &["SCHED0000"];

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).parent().unwrap().to_path_buf()
}

fn deps() -> PathBuf {
    env::var_os("FL4_DEPS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env::var("HOME").unwrap()).join("Projects/fl4-deps"))
}

fn run(cmd: &mut Command) {
    eprintln!("+ {:?}", cmd);
    let st = cmd.status().unwrap_or_else(|e| fail(&format!("cannot run {:?}: {e}", cmd)));
    if !st.success() {
        fail(&format!("command failed ({st}): {:?}", cmd));
    }
}

fn fail(msg: &str) -> ! {
    eprintln!("xtask: {msg}");
    exit(1)
}

struct Opts {
    release: bool,
    setup: String,
    smp: u32,
    timeout: u64,
    seeds: u64,
    rest: Vec<String>,
}

fn parse(args: &[String]) -> Opts {
    let mut o = Opts { release: false, setup: "kvm".into(), smp: 1, timeout: 1800, seeds: 200, rest: vec![] };
    let mut i = 0;
    while i < args.len() {
        match args[i].as_str() {
            "--release" => o.release = true,
            "--setup" => {
                i += 1;
                o.setup = args[i].clone();
            }
            "--smp" => {
                i += 1;
                o.smp = args[i].parse().unwrap();
            }
            "--seeds" => {
                i += 1;
                o.seeds = args[i].parse().unwrap();
            }
            "--timeout" => {
                i += 1;
                o.timeout = args[i].parse().unwrap();
            }
            a => o.rest.push(a.to_string()),
        }
        i += 1;
    }
    o
}

/// Build the standalone kernel image (default configuration).
fn build_kernel(o: &Opts) -> PathBuf {
    let r = root();
    let mut c = Command::new("cargo");
    c.current_dir(&r).args(["build", "--release", "-p", "fl4-kernel", "--target", "x86_64-unknown-none"]);
    if o.release {
        c.arg("--features=release-profile");
    }
    run(&mut c);
    let out = r.join("build");
    fs::create_dir_all(&out).unwrap();
    let elf = out.join("kernel.elf");
    run(Command::new("ld").args(["-n", "-static", "--gc-sections", "--build-id=none", "-u", "fl4_boot", "-T"]).arg(r.join("crates/fl4-kernel/linker.ld")).arg("--whole-archive").arg(r.join("target/x86_64-unknown-none/release/libfl4_kernel.a")).arg("-o").arg(&elf));
    let elf32 = out.join("kernel32.elf");
    run(Command::new("objcopy").args(["-O", "elf32-i386"]).arg(&elf).arg(&elf32));
    elf32
}

fn qemu_cmd(setup: &str, smp: u32, kernel: &Path, initrd: Option<&Path>) -> Command {
    let mut c = Command::new("qemu-system-x86_64");
    match setup {
        "kvm" => c.args(["-enable-kvm", "-cpu", "host,+invtsc"]),
        "kvm-reduced" => c.args(["-enable-kvm", "-cpu", "host,-x2apic,-tsc-deadline"]),
        "tcg" => c.args(["-accel", "tcg", "-cpu", "max", "-icount", "shift=auto"]),
        s => fail(&format!("unknown setup {s} (kvm, kvm-reduced, tcg)")),
    };
    c.args(["-m", "3G", "-smp"]).arg(smp.to_string());
    c.args(["-display", "none", "-serial", "stdio", "-no-reboot", "-monitor", "none"]);
    // Extra arguments for debugging, e.g. FL4_QEMU_ARGS=-s for gdb.
    if let Ok(extra) = env::var("FL4_QEMU_ARGS") {
        c.args(extra.split_whitespace());
    }
    c.arg("-kernel").arg(kernel);
    if let Some(i) = initrd {
        c.arg("-initrd").arg(i);
    }
    c
}

/// Run QEMU, echo serial output, stop at `stop` or after `timeout`.
/// Returns the captured output.
fn run_qemu(mut c: Command, timeout: u64, stop: &[&str], log: &Path) -> String {
    use std::io::Read;
    eprintln!("+ {:?}", c);
    let mut child = c.stdout(Stdio::piped()).stdin(Stdio::null()).spawn().unwrap();
    let mut out = child.stdout.take().unwrap();
    let (tx, rx) = std::sync::mpsc::channel::<Vec<u8>>();
    std::thread::spawn(move || {
        let mut buf = [0u8; 4096];
        loop {
            match out.read(&mut buf) {
                Ok(0) | Err(_) => break,
                Ok(n) => {
                    if tx.send(buf[..n].to_vec()).is_err() {
                        break;
                    }
                }
            }
        }
    });
    let start = Instant::now();
    let mut all = Vec::new();
    let mut f = fs::File::create(log).unwrap();
    'outer: loop {
        match rx.recv_timeout(Duration::from_millis(200)) {
            Ok(b) => {
                use std::io::Write;
                std::io::stdout().write_all(&b).ok();
                f.write_all(&b).ok();
                all.extend_from_slice(&b);
                let s = String::from_utf8_lossy(&all);
                if stop.iter().any(|p| s.contains(p)) {
                    // Keep what follows the stop marker (a panic message).
                    while let Ok(b) = rx.recv_timeout(Duration::from_millis(300)) {
                        std::io::stdout().write_all(&b).ok();
                        f.write_all(&b).ok();
                        all.extend_from_slice(&b);
                    }
                    break 'outer;
                }
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {}
            Err(_) => break,
        }
        if start.elapsed().as_secs() > timeout {
            eprintln!("\nxtask: timeout after {timeout}s");
            break;
        }
        if let Ok(Some(_)) = child.try_wait() {
            while let Ok(b) = rx.recv_timeout(Duration::from_millis(100)) {
                all.extend_from_slice(&b);
            }
            break;
        }
    }
    child.kill().ok();
    child.wait().ok();
    String::from_utf8_lossy(&all).into_owned()
}

fn clone_at(ws: &Path, path: &str, url: &str, rev: &str) {
    let dst = ws.join(path);
    if dst.exists() {
        return;
    }
    let gd = ws.join(".gitdirs").join(path.replace('/', "_"));
    // Prefer a local mirror in FL4_DEPS/ws to save the download.
    let local = deps().join("ws").join(path);
    let src = if local.join(".git").exists() { local.to_string_lossy().into_owned() } else { url.to_string() };
    // Separate git dirs: musllibc's build expects `.git` to be a file.
    run(Command::new("git").args(["clone", "-q", "--separate-git-dir"]).arg(&gd).arg(&src).arg(&dst));
    run(Command::new("git").arg("-C").arg(&dst).args(["checkout", "-q", rev]));
}

/// The sel4test workspace: the pinned seL4 projects, sel4test itself and
/// FL4's cmake/ as the kernel.
fn sel4test_ws() -> PathBuf {
    let r = root();
    let ws = r.join("build/sel4test-ws");
    let gitdirs = ws.join(".gitdirs");
    fs::create_dir_all(&gitdirs).unwrap();
    fs::create_dir_all(ws.join("projects")).unwrap();
    fs::create_dir_all(ws.join("tools")).unwrap();
    for (path, url, rev) in SEL4TEST_MANIFEST {
        clone_at(&ws, path, url, rev);
    }
    let sel4test = env::var_os("SEL4TEST").map(PathBuf::from).unwrap_or_else(|| PathBuf::from(env::var("HOME").unwrap()).join("Projects/sel4test"));
    let t = ws.join("projects/sel4test");
    if !t.exists() {
        run(Command::new("git").args(["clone", "-q", "--separate-git-dir"]).arg(gitdirs.join("sel4test")).arg(&sel4test).arg(&t));
    }
    let link = |src: &Path, dst: &Path| {
        let _ = fs::remove_file(dst);
        std::os::unix::fs::symlink(src, dst).unwrap();
    };
    link(&r.join("cmake"), &ws.join("kernel"));
    link(Path::new("tools/seL4/cmake-tool/init-build.sh"), &ws.join("init-build.sh"));
    link(Path::new("projects/sel4test/easy-settings.cmake"), &ws.join("easy-settings.cmake"));
    ws
}

fn python_env(c: &mut Command) {
    let venv = deps().join("venv/bin");
    if venv.exists() {
        let path = format!("{}:{}", venv.display(), env::var("PATH").unwrap());
        c.env("PATH", path);
    }
}

fn sel4test_filter() -> String {
    // POSIX ERE has no negative lookahead: match every name that differs
    // from each skipped name at some position.
    let name = QEMU_FLAKY[0];
    assert_eq!(QEMU_FLAKY.len(), 1);
    let mut alts = vec![];
    for i in 0..name.len() {
        alts.push(format!("{}[^{}]", &name[..i], &name[i..i + 1]));
    }
    format!("^({})", alts.join("|"))
}

fn sel4test_build(o: &Opts) -> PathBuf {
    let ws = sel4test_ws();
    let name = format!("build-{}-smp{}", if o.release { "release" } else { "debug" }, o.smp);
    let b = ws.join(&name);
    if !b.join("build.ninja").exists() {
        fs::create_dir_all(&b).unwrap();
        let mut c = Command::new("../init-build.sh");
        c.current_dir(&b).args(["-DPLATFORM=x86_64", "-DMCS=ON", "-DSIMULATION=OFF"]);
        c.arg(format!("-DRELEASE={}", if o.release { "ON" } else { "OFF" }));
        c.arg(format!("-DSMP={}", if o.smp > 1 { "ON" } else { "OFF" }));
        if o.smp > 1 {
            c.arg(format!("-DNUM_NODES={}", o.smp));
        }
        c.arg(format!("-DLibSel4TestPrinterRegex={}", sel4test_filter()));
        for a in &o.rest {
            c.arg(a);
        }
        python_env(&mut c);
        run(&mut c);
    }
    let mut c = Command::new("ninja");
    c.current_dir(&b);
    python_env(&mut c);
    run(&mut c);
    b
}

fn sel4test(o: &Opts) {
    let b = sel4test_build(o);
    let k = b.join("images/kernel-x86_64-pc99");
    let i = b.join("images/sel4test-driver-image-x86_64-pc99");
    let log = b.join("sel4test.log");
    let stop = ["All is well in the universe", "Test suite failed", "Halting...", "FL4 panic"];
    let out = run_qemu(qemu_cmd(&o.setup, o.smp, &k, Some(&i)), o.timeout, &stop, &log);
    let (passed, failed) = sel4test_results(&out);
    let unexpected: Vec<_> = failed.iter().filter(|t| !UPSTREAM_FLAKY.contains(&t.as_str())).collect();
    eprintln!("\nxtask: sel4test {}: {passed} passed, {} failed", o.setup, failed.len());
    for f in &failed {
        let note = if UPSTREAM_FLAKY.contains(&f.as_str()) { " (flaky upstream too)" } else { "" };
        eprintln!("  {f}{note}");
    }
    let finished = out.contains("All is well in the universe") || out.contains("Test suite failed");
    if !finished {
        fail("sel4test did not complete");
    }
    if !unexpected.is_empty() {
        fail("sel4test failed");
    }
}

/// Passed tests and failed test names. Release builds print only
/// "Starting test N: NAME" and the errors, so a failure belongs to the
/// test that started last.
fn sel4test_results(out: &str) -> (usize, Vec<String>) {
    let mut failed: Vec<String> = Vec::new();
    let mut current: Option<String> = None;
    let mut passed = 0;
    for l in out.lines() {
        let l = l.trim_end();
        if let Some(rest) = l.strip_prefix("Starting test ") {
            current = rest.split(": ").nth(1).map(|n| n.to_string());
        } else if l.starts_with("Test ") && l.ends_with(" passed") {
            passed += 1;
        } else if let Some(i) = l.find(" tests passed") {
            // The suite summary, "... N tests passed" or "... M/N tests passed".
            let n = l[..i].rsplit([' ', '/']).nth(if l[..i].contains('/') { 1 } else { 0 });
            if let Some(n) = n.and_then(|n| n.parse().ok()) {
                passed = n;
            }
        } else if l.starts_with("\tError:") || l.starts_with("\tFailure:") || (l.starts_with("Test ") && l.ends_with(" failed")) {
            if let Some(c) = &current {
                if !failed.contains(c) {
                    failed.push(c.clone());
                }
            }
        }
    }
    (passed, failed)
}

/// Seeds that once found bugs (DESIGN.md §4, "Fixes found while building
/// FL4"): (seed, cores, steps).
const SIM_REGRESSIONS: &[(u64, u64, u64)] = &[(113, 4, 20000)];

/// Deterministic simulation (DESIGN.md §10): the regression seeds, then
/// --seeds seeds (default 200) on --smp cores (default 4), 20000 steps
/// each, serially and then with the cores' kernel entries interleaved
/// (transactions, 8000 steps).
fn sim(o: &Opts) {
    let r = root();
    run(Command::new("cargo").current_dir(&r).args(["build", "--release", "-p", "fl4-sim"]));
    let bin = r.join("target/release/fl4-sim");
    for &(seed, cores, steps) in SIM_REGRESSIONS {
        run(Command::new(&bin).args(["--seeds", "1", "--first", &seed.to_string(), "--cores", &cores.to_string(), "--steps", &steps.to_string()]));
    }
    let cores = if o.smp > 1 { o.smp } else { 4 };
    run(Command::new(&bin).args(["--seeds", &o.seeds.to_string(), "--cores", &cores.to_string(), "--steps", "20000"]));
    run(Command::new(&bin).args(["--seeds", &o.seeds.to_string(), "--cores", &cores.to_string(), "--steps", "8000", "--conc"]));
}

/// The extractability gate (DESIGN.md §6): all of fl4-core goes through
/// Charon and Aeneas without errors, the result typechecks in Lean, and so
/// do the proofs about it. `extract` already fails on any Aeneas error.
fn gate() {
    extract();
    // proofs/lakefile.lean requires Aeneas's Lean library from .deps/aeneas.
    let link = root().join("proofs/.deps/aeneas");
    if !link.exists() {
        fs::create_dir_all(link.parent().unwrap()).unwrap();
        std::os::unix::fs::symlink(deps().join("aeneas/backends/lean"), &link).unwrap();
    }
    // P0: constant values, then a theorem per function (DESIGN.md §9).
    let scripts = root().join("xtask/scripts");
    for g in ["gen_const_specs.py", "gen_p0.py"] {
        run(Command::new("python3").arg(scripts.join(g)).arg(root().join("proofs")));
    }
    let mut c = Command::new("lake");
    c.current_dir(root().join("proofs")).arg("build");
    run(&mut c);
    let status = fs::read_to_string(root().join("proofs/Fl4Proofs/P0/status.json")).unwrap();
    let left = status.matches("\"sorry\": {}").count() == 0;
    eprintln!("xtask: gate passed (proofs/Fl4Proofs/P0/status.json lists the P0 theorems still to prove)");
    if left && env::var_os("FL4_P0_STRICT").is_some() {
        fail("P0 is not complete");
    }
}

fn extract() {
    let r = root();
    let d = deps().join("aeneas");
    let charon = d.join("charon/bin/charon");
    let aeneas = d.join("bin/aeneas");
    let out = r.join("build/llbc");
    fs::create_dir_all(&out).unwrap();
    run(Command::new(&charon).current_dir(r.join("crates/fl4-core")).args(["cargo", "--preset=aeneas", "--include", "fl4_abi", "--dest"]).arg(&out));
    run(Command::new(&aeneas).args(["-backend", "lean", "-split-files", "-dest"]).arg(r.join("proofs/Fl4Core")).arg(out.join("fl4_core.llbc")));
}

fn main() {
    let args: Vec<String> = env::args().skip(1).collect();
    let cmd = args.first().cloned().unwrap_or_default();
    let o = parse(&args[1.min(args.len())..]);
    match cmd.as_str() {
        "kernel" => {
            build_kernel(&o);
        }
        "run" => {
            let k = build_kernel(&o);
            let initrd = o.rest.first().map(PathBuf::from);
            run_qemu(qemu_cmd(&o.setup, o.smp, &k, initrd.as_deref()), o.timeout, &["FL4 halted", "FL4 panic"], &root().join("build/run.log"));
        }
        "sel4test-build" => {
            sel4test_build(&o);
        }
        "sel4test" => sel4test(&o),
        "extract" => extract(),
        "gate" => gate(),
        "sim" => sim(&o),
        _ => {
            eprintln!("usage: cargo xtask <kernel|run|sel4test-build|sel4test|extract|gate|sim> [--release] [--setup kvm|kvm-reduced|tcg] [--smp N] [--timeout S] [--seeds N]");
            exit(2);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::sel4test_results;

    #[test]
    fn debug_log() {
        let log = "Starting test 1: A\nRunning test A (x)\nTest A passed\nStarting test 2: B\n\tError: x at line 1\nTest B failed\nTest suite failed. 1/2 tests passed.\n";
        assert_eq!(sel4test_results(log), (1, vec!["B".to_string()]));
    }

    #[test]
    fn release_log() {
        let log = "Starting test 95: A\nStarting test 96: B\n\tFailure: result == SUCCESS at line 296 of file d/sel4test-driver/src/testtypes.c\nStarting test 97: C\nTest suite failed. 170/171 tests passed.\n";
        assert_eq!(sel4test_results(log), (170, vec!["B".to_string()]));
    }
}
