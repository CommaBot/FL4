//! Audit r8 F1: boot.S's EL2 code on a CPU whose HCR_EL2.E2H is fixed at 1
//! (VHE only, no FEAT_E2H0). There, at EL2, an access to SCTLR_EL1,
//! SPSR_EL1, ELR_EL1, ESR_EL1 or VBAR_EL1 reaches the EL2 register of that
//! name, and only the *_EL12 encodings (op1 = 5) reach EL1's; with E2H 0 the
//! *_EL12 encodings are UNDEFINED. A small interpreter runs the instructions
//! of `fl4_el2_reflect` and the end of `fl4_el_setup` as written in boot.S
//! over a model of those registers, with E2H 0 and 1.

use std::collections::HashMap;

const BOOT: &str = include_str!("../../crates/fl4-kernel-aarch64/src/boot.S");
const SPSR_EL1H_MASKED: u64 = 0x3c5;
const SCTLR_EL1_RES1: u64 = 0x30d00800;

/// Lines of boot.S from `from` (a line of its own) up to `to`, comments
/// left out; labels stay as lines of their own ("11:", "fl4_el2_halt:").
fn code(from: &str, to: &str) -> Vec<String> {
    let at = BOOT.find(from).unwrap_or_else(|| panic!("{from} not found"));
    let end = at + BOOT[at..].find(to).unwrap_or_else(|| panic!("{to} not found"));
    let mut out = vec![];
    let mut comment = false;
    for l in BOOT[at..end].lines() {
        let mut l = l.to_string();
        if comment {
            match l.find("*/") {
                Some(e) => {
                    l = l[e + 2..].to_string();
                    comment = false;
                }
                None => continue,
            }
        }
        while let Some(b) = l.find("/*") {
            match l[b..].find("*/") {
                Some(e) => l.replace_range(b..b + e + 2, ""),
                None => {
                    comment = true;
                    l.truncate(b);
                }
            }
        }
        let mut l = l.trim().to_string();
        if let Some((n, rest)) = l.split_once(':') {
            if !n.contains(' ') && !n.is_empty() {
                out.push(format!("{n}:"));
                l = rest.trim().to_string();
            }
        }
        if !l.is_empty() {
            out.push(l.split_whitespace().collect::<Vec<_>>().join(" "));
        }
    }
    out
}

/// Constant expressions of boot.S: numbers, the .equ names used here,
/// `|`, `<<` and parentheses.
fn eval(e: &str) -> u64 {
    fn expr(t: &[String], i: &mut usize) -> u64 {
        let mut v = shift(t, i);
        while t.get(*i).map(String::as_str) == Some("|") {
            *i += 1;
            v |= shift(t, i);
        }
        v
    }
    fn shift(t: &[String], i: &mut usize) -> u64 {
        let mut v = atom(t, i);
        while t.get(*i).map(String::as_str) == Some("<<") {
            *i += 1;
            v <<= atom(t, i);
        }
        v
    }
    fn atom(t: &[String], i: &mut usize) -> u64 {
        let s = t[*i].clone();
        *i += 1;
        if s == "(" {
            let v = expr(t, i);
            assert_eq!(t[*i], ")");
            *i += 1;
            return v;
        }
        match s.as_str() {
            "SPSR_EL1H_MASKED" => SPSR_EL1H_MASKED,
            "SCTLR_EL1_RES1" => SCTLR_EL1_RES1,
            _ => match s.strip_prefix("0x") {
                Some(h) => u64::from_str_radix(h, 16).unwrap(),
                None => s.parse().unwrap_or_else(|_| panic!("unknown constant {s}")),
            },
        }
    }
    let mut t = vec![];
    let mut cur = String::new();
    let mut chars = e.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '(' | ')' | '|' => {
                if !cur.is_empty() {
                    t.push(std::mem::take(&mut cur));
                }
                t.push(c.to_string());
            }
            '<' => {
                assert_eq!(chars.next(), Some('<'));
                if !cur.is_empty() {
                    t.push(std::mem::take(&mut cur));
                }
                t.push("<<".into());
            }
            ' ' => {
                if !cur.is_empty() {
                    t.push(std::mem::take(&mut cur));
                }
            }
            _ => cur.push(c),
        }
    }
    if !cur.is_empty() {
        t.push(cur);
    }
    let mut i = 0;
    let v = expr(&t, &mut i);
    assert_eq!(i, t.len(), "trailing tokens in {e}");
    v
}

/// EL2's view of the system registers boot.S touches, by the register an
/// access reaches.
struct Cpu {
    e2h: bool,
    sys: HashMap<&'static str, u64>,
    x: HashMap<String, u64>,
}

#[derive(Debug, PartialEq)]
enum End {
    Eret,
    Halt,
}

impl Cpu {
    fn new(e2h: bool) -> Cpu {
        let mut sys = HashMap::new();
        for (r, v) in [
            ("SCTLR_EL1", 0x1111_0000),
            ("SPSR_EL1", 0x2222_0000),
            ("ELR_EL1", 0x3333_0000),
            ("ESR_EL1", 0x4444_0000),
            ("VBAR_EL1", 0xffff_0000_0010_0000),
            ("SCTLR_EL2", 0x5555_0000),
            ("SPSR_EL2", 0x6666_0000),
            ("ELR_EL2", 0x7777_0000),
            ("ESR_EL2", 0x8888_0000),
            ("VBAR_EL2", 0x4008_0800),
            ("TPIDR_EL2", 0x9999_0000),
        ] {
            sys.insert(r, v);
        }
        sys.insert("HCR_EL2", (1 << 31) | ((e2h as u64) << 34));
        Cpu { e2h, sys, x: HashMap::new() }
    }

    /// The register an access to `name` at EL2 reaches. Panics where the
    /// access is UNDEFINED.
    fn reg(&self, name: &str) -> &'static str {
        let el1 = [
            ("sctlr", "s3_5_c1_c0_0", "SCTLR_EL1", "SCTLR_EL2"),
            ("spsr", "s3_5_c4_c0_0", "SPSR_EL1", "SPSR_EL2"),
            ("elr", "s3_5_c4_c0_1", "ELR_EL1", "ELR_EL2"),
            ("esr", "s3_5_c5_c2_0", "ESR_EL1", "ESR_EL2"),
            ("vbar", "s3_5_c12_c0_0", "VBAR_EL1", "VBAR_EL2"),
        ];
        let name = name.to_ascii_lowercase();
        for (n, enc12, r1, r2) in el1 {
            if name == format!("{n}_el1") {
                return if self.e2h { r2 } else { r1 };
            }
            if name == format!("{n}_el12") || name == enc12 {
                assert!(self.e2h, "{name} is UNDEFINED at EL2 with HCR_EL2.E2H 0");
                return r1;
            }
            if name == format!("{n}_el2") {
                return r2;
            }
        }
        match name.as_str() {
            "tpidr_el2" => "TPIDR_EL2",
            "hcr_el2" => "HCR_EL2",
            _ => panic!("the model has no {name}"),
        }
    }

    fn gpr(&self, r: &str) -> u64 {
        if r == "xzr" {
            return 0;
        }
        *self.x.get(r).unwrap_or_else(|| panic!("{r} read before it is written"))
    }

    fn imm(op: &str) -> u64 {
        eval(op.strip_prefix('#').unwrap_or_else(|| panic!("{op} is not an immediate")))
    }

    /// Runs `code` from its first line to an `eret` or a branch to
    /// `fl4_el2_halt`. Labels named in `outside` are addresses only (`adr`).
    fn run(&mut self, code: &[String]) -> End {
        let target = |pc: usize, l: &str| -> Option<usize> {
            if l == "fl4_el2_halt" {
                return None;
            }
            let (n, dir) = l.split_at(l.len() - 1);
            let label = format!("{n}:");
            Some(match dir {
                "f" => pc + code[pc..].iter().position(|c| *c == label).unwrap_or_else(|| panic!("no {label} after {pc}")),
                "b" => code[..pc].iter().rposition(|c| *c == label).unwrap_or_else(|| panic!("no {label} before {pc}")),
                _ => code.iter().position(|c| *c == format!("{l}:")).unwrap_or_else(|| panic!("no {l}")),
            })
        };
        let mut pc = 0;
        let mut flags_z = false;
        for _ in 0..1000 {
            let l = &code[pc];
            pc += 1;
            if l.ends_with(':') {
                continue;
            }
            let (op, args) = l.split_once(' ').unwrap_or((l, ""));
            let a: Vec<&str> = args.splitn(3, ", ").collect();
            let jump = |t: &str| target(pc, t);
            match op {
                "eret" => return End::Eret,
                "isb" => {}
                "msr" => {
                    let v = self.gpr(a[1]);
                    let r = self.reg(a[0]);
                    self.sys.insert(r, v);
                }
                "mrs" => {
                    let r = self.reg(a[1]);
                    self.x.insert(a[0].into(), self.sys[r]);
                }
                "mov" => {
                    let v = if a[1].starts_with('#') { Self::imm(a[1]) } else { self.gpr(a[1]) };
                    self.x.insert(a[0].into(), v);
                }
                "ldr" => {
                    let v = eval(a[1].strip_prefix('=').expect("literal load"));
                    self.x.insert(a[0].into(), v);
                }
                "adr" => {
                    self.x.insert(a[0].into(), 0xadd0_0000);
                }
                "and" | "orr" | "add" => {
                    let (x, y) = (self.gpr(a[1]), Self::imm(a[2]));
                    let v = match op {
                        "and" => x & y,
                        "orr" => x | y,
                        _ => x.wrapping_add(y),
                    };
                    self.x.insert(a[0].into(), v);
                }
                "tst" => flags_z = self.gpr(a[0]) & Self::imm(a[1]) == 0,
                "b.ne" | "b.eq" | "b" | "tbnz" | "tbz" => {
                    let (taken, t) = match op {
                        "b.ne" => (!flags_z, a[0]),
                        "b.eq" => (flags_z, a[0]),
                        "b" => (true, a[0]),
                        _ => {
                            let bit = self.gpr(a[0]) >> Self::imm(a[1]) & 1 == 1;
                            (bit == (op == "tbnz"), a[2])
                        }
                    };
                    if taken {
                        match jump(t) {
                            Some(p) => pc = p,
                            None => return End::Halt,
                        }
                    }
                }
                _ => panic!("the model does not run `{l}`"),
            }
        }
        panic!("no eret within 1000 steps");
    }
}

/// `lines` with boot.S's macros expanded (`\name` replaced by the
/// argument), each expansion's lines as `code` gives them.
fn expand(lines: Vec<String>) -> Vec<String> {
    let mut out = vec![];
    for l in lines {
        let (op, args) = l.split_once(' ').unwrap_or((&l, ""));
        let Some(at) = BOOT.find(&format!("\n.macro {op}")) else {
            out.push(l);
            continue;
        };
        let head = &BOOT[at + 1..at + 1 + BOOT[at + 1..].find('\n').unwrap()];
        let params: Vec<&str> = head[".macro ".len() + op.len()..].split(',').map(str::trim).filter(|p| !p.is_empty()).collect();
        let args: Vec<&str> = args.split(',').map(str::trim).filter(|a| !a.is_empty()).collect();
        assert_eq!(params.len(), args.len(), "{l}");
        let body = code(head, "\n.endm");
        for b in &body[1..] {
            let mut b = b.clone();
            for (p, a) in params.iter().zip(&args) {
                b = b.replace(&format!("\\{p}"), a);
            }
            assert!(!b.contains('\\'), "unexpanded {b}");
            out.push(b);
        }
    }
    out
}

fn reflect_code() -> Vec<String> {
    expand(code("\nfl4_el2_reflect:\n", "\nfl4_el2_halt:\n"))
}

/// A trap from EL0 to EL2 reaches EL1 as an Undefined Instruction exception
/// taken from EL0: SPSR_EL1, ELR_EL1 and ESR_EL1 get the thread's state and
/// the syndrome, EL2 returns to VBAR_EL1 + 0x400 at EL1h with DAIF masked,
/// x0 comes back as it was, and no EL2 register is left changed but the
/// two the exception return takes. Before, with E2H 1 the writes went to
/// SPSR_EL2, ELR_EL2 and ESR_EL2, and the return went to VBAR_EL2 + 0x400
/// (EL2's vectors at their physical address, run at EL1).
#[test]
fn el0_traps_reach_el1_with_e2h_fixed_at_one() {
    let code = reflect_code();
    for e2h in [false, true] {
        for span in [false, true] {
            for pan in [0, 1 << 22] {
                let user_pstate = 0x2000_0000 | pan; // EL0t, C set
                let mut c = Cpu::new(e2h);
                let sctlr = if span { 0x1111_0000 | (1 << 23) } else { 0x1111_0000 };
                c.sys.insert("SCTLR_EL1", sctlr);
                c.sys.insert("SPSR_EL2", user_pstate);
                c.sys.insert("ELR_EL2", 0x40_1234);
                c.x.insert("x0".into(), 0x0123_4567_89ab_cdef);
                let before = c.sys.clone();
                assert_eq!(c.run(&code), End::Eret, "e2h {e2h}");
                let s = &c.sys;
                let what = format!("e2h {e2h} span {span} pan {pan:#x}");
                assert_eq!(c.x["x0"], 0x0123_4567_89ab_cdef, "{what}: x0");
                assert_eq!(s["SPSR_EL1"], user_pstate, "{what}: SPSR_EL1");
                assert_eq!(s["ELR_EL1"], 0x40_1234, "{what}: ELR_EL1");
                assert_eq!(s["ESR_EL1"], 1 << 25, "{what}: ESR_EL1");
                assert_eq!(s["ELR_EL2"], before["VBAR_EL1"] + 0x400, "{what}: return address");
                let pan_after = if span { pan } else { 1 << 22 };
                assert_eq!(s["SPSR_EL2"], SPSR_EL1H_MASKED | pan_after, "{what}: return PSTATE");
                for r in ["SCTLR_EL1", "VBAR_EL1", "SCTLR_EL2", "ESR_EL2", "VBAR_EL2", "HCR_EL2"] {
                    assert_eq!(s[r], before[r], "{what}: {r} changed");
                }
            }
        }
    }
}

/// Anything but AArch64 EL0 stops the core, with E2H either way.
#[test]
fn el2_reflect_halts_unless_from_el0() {
    for e2h in [false, true] {
        for m in [0x4, 0x5, 0x10] {
            let mut c = Cpu::new(e2h);
            c.sys.insert("SPSR_EL2", m);
            c.x.insert("x0".into(), 1);
            assert_eq!(c.run(&reflect_code()), End::Halt);
        }
    }
}

/// `fl4_el_setup` gives EL1 SCTLR_EL1's RES1 value (MMU, caches and
/// alignment checks off, little-endian) before it drops to EL1, and leaves
/// SCTLR_EL2 alone. Before, with E2H 1 the write reached SCTLR_EL2 and EL1
/// started with the reset value of SCTLR_EL1, UNKNOWN where EL2 is
/// implemented.
#[test]
fn el1_sctlr_is_set_before_leaving_el2_with_e2h_fixed_at_one() {
    let setup = code("\nfl4_el_setup:\n", "\nfl4_el2_vectors:\n");
    let from = setup.iter().position(|l| l == "6:").expect("6:");
    let to = from + setup[from..].iter().position(|l| l == "eret").expect("eret");
    let tail = &setup[from..=to];
    for e2h in [false, true] {
        let mut c = Cpu::new(e2h);
        let before = c.sys.clone();
        assert_eq!(c.run(tail), End::Eret);
        assert_eq!(c.sys["SCTLR_EL1"], SCTLR_EL1_RES1, "e2h {e2h}");
        assert_eq!(c.sys["SCTLR_EL2"], before["SCTLR_EL2"], "e2h {e2h}");
        assert_eq!(c.sys["SPSR_EL2"], SPSR_EL1H_MASKED);
        assert_eq!(c.sys["ELR_EL2"], 0xadd0_0000);
    }
}

/// Between `fl4_el_setup`'s EL check and its `eret`, every EL1 register
/// written is one that E2H does not redirect (the pointer authentication
/// keys are written after the `eret`, at EL1). SCTLR_EL1, written on one path
/// per E2H value, is checked by running the code instead.
#[test]
fn el2_setup_writes_no_redirected_el1_register_unguarded() {
    let setup = code("\nfl4_el_setup:\n", "\nfl4_el2_vectors:\n");
    let to = setup.iter().position(|l| l == "eret").unwrap();
    let redirected = ["spsr_el1", "elr_el1", "esr_el1", "vbar_el1", "tcr_el1", "ttbr0_el1", "ttbr1_el1",
        "mair_el1", "amair_el1", "cpacr_el1", "contextidr_el1", "far_el1", "afsr0_el1", "afsr1_el1", "cntkctl_el1",
        "zcr_el1", "trfcr_el1", "tfsr_el1", "pmscr_el1", "sp_el1"];
    for l in &setup[..to] {
        if let Some(r) = l.strip_prefix("msr ").and_then(|a| a.split(", ").next()) {
            assert!(!redirected.contains(&r), "`{l}` at EL2 reaches the EL2 register with E2H 1");
        }
    }
}

/// The reflection uses no general-purpose register but x0, on either path,
/// and gives x0 back from TPIDR_EL2 before every `eret`.
#[test]
fn el2_reflect_uses_only_x0() {
    let r = reflect_code();
    assert_eq!(r.iter().filter(|l| *l == "eret").count(), 2);
    for (i, l) in r.iter().enumerate() {
        if l == "eret" {
            assert_eq!(r[i - 1], "mrs x0, tpidr_el2");
        }
        for op in l.split([' ', ',']).skip(1).filter(|o| !o.is_empty()) {
            let gpr = op.len() > 1 && (op.starts_with('x') || op.starts_with('w')) && op[1..].chars().all(|c| c.is_ascii_digit());
            assert!(!(gpr && op[1..] != *"0") && op != "sp" && op != "wsp", "{l} uses {op}");
        }
    }
}
