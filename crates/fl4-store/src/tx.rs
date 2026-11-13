//! Transactions over kernel memory (DESIGN.md §7): TL2-style, with a
//! striped seqlock table.
//!
//! Every 64-byte line of kernel memory is covered by one entry of `TABLE`:
//! a version (even, a value of `CLOCK`) and a lock bit. A transaction reads
//! the clock when it begins. Its reads are valid if the line's entry is
//! unlocked and no newer than that; otherwise the transaction is doomed and
//! reads return 0 until it ends. Writes are buffered per core. Commit locks
//! the entries of the written lines in table order, checks the read set,
//! writes the buffer out and releases the entries with a new version.
//!
//! All per-core state is used only by its core, with interrupts disabled.
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU64, Ordering};

/// Table entries; a power of two.
pub const ENTRIES: usize = 4096;
/// Cores with transaction state.
pub const MAX_CPUS: usize = 16;
/// Distinct lines a transaction may read, and words it may write. An
/// entry needing more is run under the serial gate instead.
const MAX_READS: usize = 2048;
const WB: usize = 2048;
/// Largest `zero` done inside a transaction (bytes); larger clears go serial.
const MAX_TX_ZERO: u64 = 512;

/// Memory under the store: physical memory through the kernel window on
/// hardware, simulated memory in fl4-sim.
pub trait Mem {
    fn load(&self, addr: u64) -> u64;
    fn store(&self, addr: u64, v: u64);
    /// Called while spinning for a table entry (the simulator switches
    /// cores here).
    fn relax(&self) {
        core::hint::spin_loop();
    }
}

#[repr(C, align(64))]
struct Entry(AtomicU64);

static TABLE: [Entry; ENTRIES] = [const { Entry(AtomicU64::new(0)) }; ENTRIES];
/// Version clock: even values, advanced by 2 per committing writer.
static CLOCK: AtomicU64 = AtomicU64::new(0);

/// The table entry covering `addr`.
#[inline(always)]
pub fn stripe(addr: u64) -> usize {
    let l = addr >> 6;
    ((l ^ (l >> 12)) as usize) & (ENTRIES - 1)
}

const DOOM_NONE: u8 = 0;
/// A read saw a concurrent commit: retry.
const DOOM_CONFLICT: u8 = 1;
/// The entry cannot run as a transaction: rerun it under the serial gate.
const DOOM_SERIAL: u8 = 2;

pub struct TxState {
    active: bool,
    rv: u64,
    doom: u8,
    gen: u32,
    rstamp: [u32; ENTRIES],
    reads: [u16; MAX_READS],
    nreads: usize,
    wstamp: [u32; ENTRIES],
    wsaved: [u64; ENTRIES],
    wstripes: [u16; WB],
    nwstripes: usize,
    // Write buffer: open addressing on the word address.
    wkey: [u64; WB],
    wval: [u64; WB],
    wgen: [u32; WB],
    worder: [u16; WB],
    nw: usize,
}

impl TxState {
    const fn new() -> TxState {
        TxState {
            active: false,
            rv: 0,
            doom: DOOM_NONE,
            gen: 0,
            rstamp: [0; ENTRIES],
            reads: [0; MAX_READS],
            nreads: 0,
            wstamp: [0; ENTRIES],
            wsaved: [0; ENTRIES],
            wstripes: [0; WB],
            nwstripes: 0,
            wkey: [0; WB],
            wval: [0; WB],
            wgen: [0; WB],
            worder: [0; WB],
            nw: 0,
        }
    }
}

struct States(UnsafeCell<[TxState; MAX_CPUS]>);
// SAFETY: each core uses only its own entry, with interrupts disabled.
unsafe impl Sync for States {}
static STATES: States = States(UnsafeCell::new([const { TxState::new() }; MAX_CPUS]));

#[inline(always)]
#[allow(clippy::mut_from_ref)]
fn st(cpu: u64) -> &'static mut TxState {
    unsafe { &mut (*STATES.0.get())[cpu as usize] }
}

/// Start a transaction on `cpu`.
pub fn begin(cpu: u64) {
    let t = st(cpu);
    t.gen = t.gen.wrapping_add(1);
    if t.gen == 0 {
        t.rstamp = [0; ENTRIES];
        t.wstamp = [0; ENTRIES];
        t.wgen = [0; WB];
        t.gen = 1;
    }
    t.nreads = 0;
    t.nwstripes = 0;
    t.nw = 0;
    t.doom = DOOM_NONE;
    t.rv = CLOCK.load(Ordering::Acquire);
    t.active = true;
}

/// End the transaction (after commit, or to give it up).
pub fn end(cpu: u64) {
    st(cpu).active = false;
}

pub fn active(cpu: u64) -> bool {
    st(cpu).active
}

/// The entry must run under the serial gate (an irrevocable operation).
pub fn doom_serial(cpu: u64) {
    let t = st(cpu);
    if t.active {
        t.doom = DOOM_SERIAL;
    }
}

pub fn doomed(cpu: u64) -> bool {
    st(cpu).doom != DOOM_NONE
}

pub fn needs_serial(cpu: u64) -> bool {
    st(cpu).doom == DOOM_SERIAL
}

#[inline(always)]
fn slot_of(addr: u64) -> usize {
    ((addr >> 3).wrapping_mul(0x9E37_79B9_7F4A_7C15) >> 53) as usize & (WB - 1)
}

/// Where `addr` is, or would go, in the write buffer.
fn find(t: &TxState, addr: u64) -> (usize, bool) {
    let mut i = slot_of(addr);
    loop {
        if t.wgen[i] != t.gen {
            return (i, false);
        }
        if t.wkey[i] == addr {
            return (i, true);
        }
        i = (i + 1) & (WB - 1);
    }
}

pub fn read<M: Mem>(cpu: u64, m: &M, addr: u64) -> u64 {
    let t = st(cpu);
    if t.doom != DOOM_NONE {
        return 0;
    }
    if t.nw != 0 {
        let (i, hit) = find(t, addr);
        if hit {
            return t.wval[i];
        }
    }
    let e = stripe(addr);
    let v1 = TABLE[e].0.load(Ordering::Acquire);
    if v1 & 1 != 0 || v1 > t.rv {
        t.doom = DOOM_CONFLICT;
        return 0;
    }
    let v = m.load(addr);
    core::sync::atomic::fence(Ordering::Acquire);
    if TABLE[e].0.load(Ordering::Relaxed) != v1 {
        t.doom = DOOM_CONFLICT;
        return 0;
    }
    if t.rstamp[e] != t.gen {
        if t.nreads == MAX_READS {
            t.doom = DOOM_SERIAL;
            return 0;
        }
        t.rstamp[e] = t.gen;
        t.reads[t.nreads] = e as u16;
        t.nreads += 1;
    }
    v
}

pub fn write(cpu: u64, addr: u64, v: u64) {
    let t = st(cpu);
    if t.doom != DOOM_NONE {
        return;
    }
    let (i, hit) = find(t, addr);
    if !hit {
        // Keep the table at most half full so probes stay short.
        if t.nw >= WB / 2 {
            t.doom = DOOM_SERIAL;
            return;
        }
        t.wgen[i] = t.gen;
        t.wkey[i] = addr;
        t.worder[t.nw] = i as u16;
        t.nw += 1;
        let e = stripe(addr);
        if t.wstamp[e] != t.gen {
            t.wstamp[e] = t.gen;
            t.wstripes[t.nwstripes] = e as u16;
            t.nwstripes += 1;
        }
    }
    t.wval[i] = v;
}

pub fn zero(cpu: u64, addr: u64, len: u64) {
    if len > MAX_TX_ZERO {
        doom_serial(cpu);
        return;
    }
    let mut a = addr;
    while a < addr + len {
        write(cpu, a, 0);
        a += 8;
    }
}

/// Commit the transaction on `cpu`. False if it was doomed or a read is
/// no longer current; nothing is then written.
pub fn commit<M: Mem>(cpu: u64, m: &M) -> bool {
    let t = st(cpu);
    if t.doom != DOOM_NONE {
        return false;
    }
    if t.nw == 0 {
        // Read-only: every read was checked against the start version.
        return true;
    }
    let ws = &mut t.wstripes[..t.nwstripes];
    ws.sort_unstable();
    // Lock the written lines' entries in table order (deadlock free).
    for &e in ws.iter() {
        let e = e as usize;
        loop {
            let v = TABLE[e].0.load(Ordering::Relaxed);
            if v & 1 == 0 && TABLE[e].0.compare_exchange_weak(v, v | 1, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                t.wsaved[e] = v;
                break;
            }
            m.relax();
        }
    }
    let wv = CLOCK.fetch_add(2, Ordering::AcqRel) + 2;
    // Unless no other writer committed since we began, check the reads.
    if wv != t.rv + 2 {
        for i in 0..t.nreads {
            let e = t.reads[i] as usize;
            let ok = if t.wstamp[e] == t.gen {
                t.wsaved[e] <= t.rv
            } else {
                let v = TABLE[e].0.load(Ordering::Acquire);
                v & 1 == 0 && v <= t.rv
            };
            if !ok {
                for &e in t.wstripes[..t.nwstripes].iter() {
                    TABLE[e as usize].0.store(t.wsaved[e as usize], Ordering::Release);
                }
                t.doom = DOOM_CONFLICT;
                return false;
            }
        }
    }
    for k in 0..t.nw {
        let i = t.worder[k] as usize;
        m.store(t.wkey[i], t.wval[i]);
    }
    for &e in t.wstripes[..t.nwstripes].iter() {
        TABLE[e as usize].0.store(wv, Ordering::Release);
    }
    true
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use core::sync::atomic::AtomicU64;

    struct TestMem;
    impl Mem for TestMem {
        fn load(&self, addr: u64) -> u64 {
            unsafe { (*(addr as *const AtomicU64)).load(Ordering::Relaxed) }
        }
        fn store(&self, addr: u64, v: u64) {
            unsafe { (*(addr as *const AtomicU64)).store(v, Ordering::Relaxed) }
        }
    }

    #[repr(align(64))]
    struct Line([AtomicU64; 8]);
    static WORDS: [Line; 64] = [const { Line([const { AtomicU64::new(0) }; 8]) }; 64];

    fn addr(i: usize) -> u64 {
        &WORDS[i / 8].0[i % 8] as *const AtomicU64 as u64
    }

    /// Threads move amounts between random words; every transaction also
    /// checks that the total it sees is the starting total. A torn snapshot
    /// or a lost update breaks one of the two.
    #[test]
    fn transfers_preserve_the_total() {
        const N: usize = 64 * 8;
        const TOTAL: u64 = 1_000_000;
        WORDS[0].0[0].store(TOTAL, Ordering::Relaxed);
        let threads: std::vec::Vec<_> = (0..4u64)
            .map(|cpu| {
                std::thread::spawn(move || {
                    let mut x = cpu * 7919 + 1;
                    let mut commits = 0;
                    let mut aborts = 0u64;
                    while commits < 20_000 {
                        x ^= x << 13;
                        x ^= x >> 7;
                        x ^= x << 17;
                        let a = (x % N as u64) as usize;
                        let b = ((x >> 20) % N as u64) as usize;
                        begin(cpu);
                        let mut sum = 0;
                        for i in 0..N {
                            sum += read(cpu, &TestMem, addr(i));
                        }
                        let va = read(cpu, &TestMem, addr(a));
                        let vb = read(cpu, &TestMem, addr(b));
                        if !doomed(cpu) {
                            assert_eq!(sum, TOTAL, "a transaction saw a torn snapshot");
                            if a != b && va > 0 {
                                write(cpu, addr(a), va - 1);
                                write(cpu, addr(b), vb + 1);
                            }
                        }
                        let ok = commit(cpu, &TestMem);
                        end(cpu);
                        if ok {
                            commits += 1;
                        } else {
                            aborts += 1;
                        }
                    }
                    aborts
                })
            })
            .collect();
        let aborts: u64 = threads.into_iter().map(|t| t.join().unwrap()).sum();
        std::println!("80000 commits, {aborts} aborts");
        let sum: u64 = (0..N).map(|i| TestMem.load(addr(i))).sum();
        assert_eq!(sum, TOTAL);
    }
}
