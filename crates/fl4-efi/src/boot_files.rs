//! Which files the loader boots from its load options (`rootserver=`,
//! `module=`) and the paths it accepts for them. Free of firmware calls, so
//! host tests run it (xtask/tests/efi_ccel.rs).
//!
//! One path reaches three places: the file opened (`try_read_file`), the
//! descriptor measured before its contents (tcg2.rs `file_descriptor`) and,
//! on x86_64, the module name the root task finds it by (`module_name`).
//! Each of those once cut the path at its own length (255 UCS-2 units, what
//! remained of `DESC_MAX`, 63 bytes), so a long path could open one file,
//! be measured as another path and be named a third thing. Paths beyond
//! those lengths are refused instead, before any file is opened or
//! measured: what is opened, measured and named is always the whole path.

/// The most UCS-2 units of load options the loader takes.
pub const MAX_OPTIONS_UNITS: usize = 1024;

/// The load options as ASCII words (anything else is `?`).
pub struct Words {
    buf: [u8; MAX_OPTIONS_UNITS],
    n: usize,
}

impl Words {
    pub const fn new() -> Words {
        Words { buf: [0; MAX_OPTIONS_UNITS], n: 0 }
    }

    pub fn iter(&self) -> impl Iterator<Item = &[u8]> {
        self.buf[..self.n].split(|&c| c == b' ' || c == b'\t').filter(|w| !w.is_empty())
    }
}

/// The load options in `bytes` (UCS-2 little-endian, up to a NUL unit or
/// their end, at any alignment), whole or not at all: more than
/// `MAX_OPTIONS_UNITS` units before the NUL is an error, not a cut (a cut
/// could fall inside a `rootserver=` or `module=` path and leave a shorter
/// path that opens another file), and so is a half unit at the end with no
/// NUL before it. What follows the NUL is not read.
pub fn load_options(bytes: &[u8]) -> Result<Words, &'static str> {
    let mut w = Words::new();
    let units = bytes.chunks_exact(2);
    let rest = units.remainder();
    for pair in units {
        let c = u16::from_le_bytes([pair[0], pair[1]]);
        if c == 0 {
            return Ok(w);
        }
        if w.n == MAX_OPTIONS_UNITS {
            return Err("load options too long");
        }
        w.buf[w.n] = if c < 0x80 { c as u8 } else { b'?' };
        w.n += 1;
    }
    if !rest.is_empty() {
        return Err("invalid load options");
    }
    Ok(w)
}

/// The longest file path the loader opens: its UCS-2 name buffer holds 255
/// units and a NUL.
pub const MAX_BOOT_PATH: usize = 255;

/// The longest module name (the path after its last `/` or `\`): the
/// kernel keeps 63 bytes and a NUL (mboot.rs `MODULE_NAME_LEN`).
pub const MAX_MODULE_NAME: usize = 63;

/// The files `select` can return: the root task and eight modules.
pub const MAX_FILES: usize = 9;

/// Whether the loader opens and measures `path` at all: not empty (EFI
/// would open the volume's root directory), no NUL (EFI would open the
/// path up to it) and no longer than `MAX_BOOT_PATH`.
pub fn valid_boot_path(path: &[u8]) -> bool {
    !path.is_empty() && path.len() <= MAX_BOOT_PATH && !path.contains(&0)
}

/// The module name of a file at `path`: what follows its last `/` or `\`,
/// at most `MAX_MODULE_NAME` bytes (only names of `Firmware::boot`'s
/// callers can be longer; `select` refuses longer option paths).
pub fn module_name(path: &[u8]) -> &[u8] {
    let name = path.rsplit(|&b| b == b'/' || b == b'\\').next().unwrap_or(path);
    &name[..name.len().min(MAX_MODULE_NAME)]
}

/// Whether an option's `path` is one the loader boots: a valid path whose
/// module name is not empty and not cut.
fn usable(path: &[u8]) -> bool {
    let name = path.rsplit(|&b| b == b'/' || b == b'\\').next().unwrap_or(path);
    valid_boot_path(path) && !name.is_empty() && name.len() <= MAX_MODULE_NAME
}

/// A boot file: (address, bytes, path or name).
pub type BootFile<'a> = (u64, u64, &'a [u8]);

/// The boot files for the load options `opts`, the root task first, and
/// how many there are. Each `rootserver=` and `module=` path is checked,
/// then read (`read`: address and length) and measured (`measure`: role,
/// path, address, length) in option order, before the next one is looked
/// at; the last `rootserver=` is the root task. A refused path, read or
/// measurement ends the selection with its error before anything else is
/// read or measured. An empty `rootserver=` file is refused (after it was
/// read, before it is measured): the embedded root task (`embedded_root`,
/// address and length; 0 bytes for none) stands in only when no
/// `rootserver=` is given. An embedded module (`embedded_module`, the same)
/// comes after the options' modules. A module may be empty.
pub fn select<'a, 'o: 'a>(
    opts: impl IntoIterator<Item = &'o [u8]>,
    embedded_root: (u64, u64),
    embedded_module: (u64, u64),
    mut read: impl FnMut(&'a [u8]) -> Result<(u64, u64), &'static str>,
    mut measure: impl FnMut(&'static [u8], &'a [u8], u64, u64) -> Result<(), &'static str>,
) -> Result<([BootFile<'a>; MAX_FILES], usize), &'static str> {
    let mut files: [BootFile<'a>; MAX_FILES] = [(0, 0, &[][..]); MAX_FILES];
    let mut root = None;
    let mut n = 1;
    for opt in opts {
        let (role, path): (&'static [u8], &'a [u8]) = if let Some(path) = opt.strip_prefix(b"rootserver=") {
            (b"rootserver", path)
        } else if let Some(path) = opt.strip_prefix(b"module=") {
            if n == MAX_FILES {
                return Err("too many boot modules");
            }
            (b"module", path)
        } else {
            continue;
        };
        if !usable(path) {
            return Err("invalid boot file path");
        }
        let (pa, len) = read(path)?;
        if role == b"rootserver" {
            // Measured, it would then be replaced by the embedded root task.
            if len == 0 {
                return Err("empty rootserver");
            }
            measure(role, path, pa, len)?;
            root = Some((pa, len, path));
        } else {
            measure(role, path, pa, len)?;
            files[n] = (pa, len, path);
            n += 1;
        }
    }
    files[0] = match root {
        Some(f) => f,
        None if embedded_root.1 != 0 => (embedded_root.0, embedded_root.1, b"rootserver"),
        None => return Err("no x86_64 root task"),
    };
    // The fallback EFI path has no load options. Allow a boot module to
    // be built in alongside the root task.
    if embedded_module.1 != 0 {
        if n == MAX_FILES {
            return Err("too many boot modules");
        }
        files[n] = (embedded_module.0, embedded_module.1, b"module");
        n += 1;
    }
    Ok((files, n))
}
