//! Transactions over kernel memory (DESIGN.md §7): TL2-style, with a
//! striped seqlock table.
//!
//! Every 16-byte region of kernel memory is covered by one entry of `TABLE`:
//! a version (even, a value of `CLOCK`) and a lock bit. A transaction reads
//! the clock when it begins. Its reads are valid if the region's entry is
//! unlocked and no newer than that; otherwise the transaction is doomed and
//! reads return 0 until it ends. Writes are buffered per core. Commit locks
//! the entries of the written regions in table order, checks the read set,
//! writes the buffer out and releases the entries with a new version.
//!
//! All per-core state is used only by its core, with interrupts disabled.
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicU64, Ordering};

// A stripe is no larger than the smallest kernel object (an endpoint).
// Four times as many entries preserve a 256 KiB contiguous stripe span.
const STRIPE_BITS: u32 = 4;
const STRIPE_BYTES: u64 = 1 << STRIPE_BITS;
const TABLE_BITS: u32 = 14;
/// Table entries; a power of two.
pub const ENTRIES: usize = 1 << TABLE_BITS;
/// Cores with transaction state.
pub const MAX_CPUS: usize = 16;
/// Distinct lines a transaction may read, and words it may write. An
/// entry needing more is run under the serial gate instead.
const MAX_READS: usize = 2048;
const WB: usize = 2048;
/// Largest `zero` done inside a transaction (bytes); larger clears go serial.
const MAX_TX_ZERO: u64 = 512;
/// Largest `clear_free` done in place inside a transaction (bytes).
/// Larger clears rerun serially: acquiring thousands of finer stripes
/// costs more than a bulk clear under the existing gate.
const MAX_TX_CLEAR: u64 = 8192;
const CLEAR_LINES: usize = (MAX_TX_CLEAR / STRIPE_BYTES) as usize;

/// Memory under the store: physical memory through the kernel window on
/// hardware, simulated memory in fl4-sim.
pub trait Mem {
    fn load(&self, addr: u64) -> u64;
    fn store(&self, addr: u64, v: u64);
    /// Clear free memory while its stripes are locked; `addr` and `len`
    /// are multiples of 8, as for `Store::clear_free`. The word-wise
    /// default keeps every store visible to the simulator and its TSO model.
    fn clear(&self, addr: u64, len: u64) {
        let mut a = addr;
        while a < addr + len {
            self.store(a, 0);
            a += 8;
        }
    }
    /// Called while spinning for a table entry (the simulator switches
    /// cores here).
    fn relax(&self) {
        core::hint::spin_loop();
    }
    // The runtime's own atomics (version table, clock, serial gate) go
    // through these too, so the simulator can run them on a store-buffer
    // model of x86-TSO (DESIGN.md §10). On hardware they are the
    // operations themselves.
    #[inline(always)]
    fn a_load(&self, a: &AtomicU64, o: Ordering) -> u64 {
        a.load(o)
    }
    #[inline(always)]
    fn a_store(&self, a: &AtomicU64, v: u64, o: Ordering) {
        a.store(v, o)
    }
    #[inline(always)]
    fn a_cas(&self, a: &AtomicU64, old: u64, new: u64, ok: Ordering, err: Ordering) -> Result<u64, u64> {
        a.compare_exchange_weak(old, new, ok, err)
    }
    #[inline(always)]
    fn a_add(&self, a: &AtomicU64, v: u64, o: Ordering) -> u64 {
        a.fetch_add(v, o)
    }
    #[inline(always)]
    fn fence(&self, o: Ordering) {
        core::sync::atomic::fence(o)
    }
}

// Four version words per cache line keep page clears from walking 16 KiB
// of metadata. Stripes stay independent, even when their counters share a
// physical cache line.
#[repr(C, align(16))]
struct Entry(AtomicU64);

static TABLE: [Entry; ENTRIES] = [const { Entry(AtomicU64::new(0)) }; ENTRIES];
/// Version clock: even values, advanced by 2 per committing writer.
static CLOCK: AtomicU64 = AtomicU64::new(0);

/// The table entry covering `addr`.
#[inline(always)]
pub fn stripe(addr: u64) -> usize {
    let l = addr >> STRIPE_BITS;
    // Spread aligned 256 KiB blocks across the table. Just XORing the
    // block number makes equally aligned pages in nearby blocks alias.
    // Multiplying the block number leaves each aligned power-of-two
    // region's stripes contiguous, so clear_free still locks in order.
    ((l ^ (l >> TABLE_BITS).wrapping_mul(0x9e37)) as usize) & (ENTRIES - 1)
}

/// Per core, the last few conflicts, for diagnosing contention: the word
/// whose read saw a newer version, or (top bit set) the stripe a commit's
/// validation failed on. Written only when a transaction aborts.
pub const CONFLICT_LOG: usize = 8;
static CONFLICTS: [[AtomicU64; CONFLICT_LOG]; MAX_CPUS] = [const { [const { AtomicU64::new(0) }; CONFLICT_LOG] }; MAX_CPUS];
static CONFLICT_I: [AtomicU64; MAX_CPUS] = [const { AtomicU64::new(0) }; MAX_CPUS];

fn log_conflict(cpu: u64, what: u64) {
    let i = CONFLICT_I[cpu as usize].fetch_add(1, Ordering::Relaxed) as usize;
    CONFLICTS[cpu as usize][i % CONFLICT_LOG].store(what, Ordering::Relaxed);
}

/// The conflict log of `cpu` (see `CONFLICTS`), most recent last.
pub fn conflicts(cpu: u64) -> [u64; CONFLICT_LOG] {
    let n = CONFLICT_I[cpu as usize].load(Ordering::Relaxed) as usize;
    core::array::from_fn(|k| CONFLICTS[cpu as usize][(n + k) % CONFLICT_LOG].load(Ordering::Relaxed))
}

const DOOM_NONE: u8 = 0;
/// A read saw a concurrent commit: retry.
const DOOM_CONFLICT: u8 = 1;
/// The entry cannot run as a transaction: rerun it under the serial gate.
const DOOM_SERIAL: u8 = 2;

pub struct TxState {
    active: bool,
    rv: u64,
    /// The version the last commit published (for fl4-sim's checker).
    wv: u64,
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
    // `clear_free`: the entries it holds, deduplicated by `zstamp`.
    zgen: u32,
    zstamp: [u32; ENTRIES],
    // Saved versions in zlist order; only held stripes need a slot.
    zsaved: [u64; CLEAR_LINES],
    zlist: [u16; CLEAR_LINES],
}

impl TxState {
    const fn new() -> TxState {
        TxState {
            active: false,
            rv: 0,
            wv: 0,
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
            zgen: 0,
            zstamp: [0; ENTRIES],
            zsaved: [0; CLEAR_LINES],
            zlist: [0; CLEAR_LINES],
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
pub fn begin<M: Mem>(cpu: u64, m: &M) {
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
    t.rv = m.a_load(&CLOCK, Ordering::Acquire);
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

/// The clock value the transaction on `cpu` started at.
pub fn read_version(cpu: u64) -> u64 {
    st(cpu).rv
}

/// The version `cpu`'s last committed writer published; set before its
/// writes reach memory.
pub fn commit_version(cpu: u64) -> u64 {
    st(cpu).wv
}

/// The version clock.
pub fn clock() -> u64 {
    CLOCK.load(Ordering::Acquire)
}

pub fn doomed(cpu: u64) -> bool {
    st(cpu).doom != DOOM_NONE
}

pub fn needs_serial(cpu: u64) -> bool {
    st(cpu).doom == DOOM_SERIAL
}

#[inline(always)]
fn slot_of(addr: u64) -> usize {
    // Keep nearby words nearby; mix in the page to spread aligned objects.
    ((addr >> 3) ^ (addr >> 12)) as usize & (WB - 1)
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
    let v1 = m.a_load(&TABLE[e].0, Ordering::Acquire);
    if v1 & 1 != 0 || v1 > t.rv {
        t.doom = DOOM_CONFLICT;
        log_conflict(cpu, addr);
        return 0;
    }
    let v = m.load(addr);
    m.fence(Ordering::Acquire);
    if m.a_load(&TABLE[e].0, Ordering::Relaxed) != v1 {
        t.doom = DOOM_CONFLICT;
        log_conflict(cpu, addr);
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

/// Zero `[addr, addr + len)`, memory that no live object occupies (an
/// untyped region with no children: `Store::clear_free`), in place rather
/// than through the write buffer.
///
/// The clear is safe even if the transaction later aborts: zeroing memory
/// that holds no live object changes nothing anyone depends on. What must
/// hold is that the region is free in the committed state when it is
/// cleared, which the transaction decided from its reads. So the clear
/// locks the region's table entries (in table order, like a commit),
/// takes a version, checks the read set is still current, clears, and
/// releases the entries at that version: a commit that would make the
/// region live writes into it, so it waits for the entries and lands
/// after the zeros. The transaction's snapshot is then current at the new
/// version, so its read version moves up to it (TL2 timestamp extension)
/// and later reads of the cleared lines stay valid.
pub fn clear_free<M: Mem>(cpu: u64, m: &M, addr: u64, len: u64) {
    let t = st(cpu);
    if t.doom != DOOM_NONE {
        return;
    }
    if len > MAX_TX_CLEAR || (((addr + len + STRIPE_BYTES - 1) >> STRIPE_BITS) - (addr >> STRIPE_BITS)) as usize > CLEAR_LINES {
        t.doom = DOOM_SERIAL;
        return;
    }
    t.zgen = t.zgen.wrapping_add(1);
    if t.zgen == 0 {
        t.zstamp = [0; ENTRIES];
        t.zgen = 1;
    }
    let mut n = 0;
    if len >= STRIPE_BYTES && len.is_power_of_two() && addr & (len - 1) == 0 {
        // An aligned power-of-two region fits inside an aligned 256 KiB
        // block. The hash XORs a constant into its varying low bits,
        // so its stripes form one aligned interval, already in lock order.
        n = (len / STRIPE_BYTES) as usize;
        let first = stripe(addr) & !(n - 1);
        for i in 0..n {
            let e = first + i;
            t.zstamp[e] = t.zgen;
            t.zlist[i] = e as u16;
        }
    } else {
        let mut a = addr & !(STRIPE_BYTES - 1);
        while a < addr + len {
            let e = stripe(a);
            if t.zstamp[e] != t.zgen {
                t.zstamp[e] = t.zgen;
                t.zlist[n] = e as u16;
                n += 1;
            }
            a += STRIPE_BYTES;
        }
        t.zlist[..n].sort_unstable();
    }
    for (slot, &e) in t.zlist[..n].iter().enumerate() {
        let e = e as usize;
        loop {
            let v = m.a_load(&TABLE[e].0, Ordering::Relaxed);
            if v & 1 == 0 && m.a_cas(&TABLE[e].0, v, v | 1, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                t.zsaved[slot] = v;
                break;
            }
            m.relax();
        }
    }
    let wv = m.a_add(&CLOCK, 2, Ordering::AcqRel) + 2;
    for i in 0..t.nreads {
        let e = t.reads[i] as usize;
        let v = if t.zstamp[e] == t.zgen {
            // The stamp identifies an entry in the sorted, unique list.
            let slot = t.zlist[..n].binary_search(&(e as u16)).unwrap();
            t.zsaved[slot]
        } else { m.a_load(&TABLE[e].0, Ordering::Acquire) };
        // (Mutation test: `mutant-clear-no-validate` clears without checking.)
        if (v & 1 != 0 || v > t.rv) && !cfg!(feature = "mutant-clear-no-validate") {
            log_conflict(cpu, (1 << 63) | e as u64);
            for (slot, &e) in t.zlist[..n].iter().enumerate() {
                m.a_store(&TABLE[e as usize].0, t.zsaved[slot], Ordering::Release);
            }
            t.doom = DOOM_CONFLICT;
            return;
        }
    }
    t.wv = wv;
    m.clear(addr, len);
    // Buffered writes into the region came before the clear.
    for k in 0..t.nw {
        let i = t.worder[k] as usize;
        if t.wkey[i] >= addr && t.wkey[i] < addr + len {
            t.wval[i] = 0;
        }
    }
    for &e in t.zlist[..n].iter() {
        m.a_store(&TABLE[e as usize].0, wv, Ordering::Release);
    }
    t.rv = wv;
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
            let v = m.a_load(&TABLE[e].0, Ordering::Relaxed);
            if v & 1 == 0 && m.a_cas(&TABLE[e].0, v, v | 1, Ordering::Acquire, Ordering::Relaxed).is_ok() {
                t.wsaved[e] = v;
                break;
            }
            m.relax();
        }
    }
    let wv = m.a_add(&CLOCK, 2, Ordering::AcqRel) + 2;
    // Unless no other writer committed since we began, check the reads.
    // (Mutation test: `mutant-skip-validation` leaves the check out.)
    if wv != t.rv + 2 && !cfg!(feature = "mutant-skip-validation") {
        for i in 0..t.nreads {
            let e = t.reads[i] as usize;
            let ok = if t.wstamp[e] == t.gen {
                t.wsaved[e] <= t.rv
            } else {
                let v = m.a_load(&TABLE[e].0, Ordering::Acquire);
                v & 1 == 0 && v <= t.rv
            };
            if !ok {
                log_conflict(cpu, (1 << 63) | e as u64);
                for &e in t.wstripes[..t.nwstripes].iter() {
                    m.a_store(&TABLE[e as usize].0, t.wsaved[e as usize], Ordering::Release);
                }
                t.doom = DOOM_CONFLICT;
                return false;
            }
        }
    }
    t.wv = wv;
    for k in 0..t.nw {
        let i = t.worder[k] as usize;
        m.store(t.wkey[i], t.wval[i]);
    }
    for &e in t.wstripes[..t.nwstripes].iter() {
        // (Mutation test: `mutant-no-publish` unlocks at the old version.)
        let v = if cfg!(feature = "mutant-no-publish") { t.wsaved[e as usize] } else { wv };
        m.a_store(&TABLE[e as usize].0, v, Ordering::Release);
    }
    true
}

#[cfg(test)]
mod tests {
    extern crate std;
    use super::*;
    use core::sync::atomic::AtomicU64;
    use std::collections::BTreeMap;
    use std::sync::Mutex;

    // The runtime's table and per-core state are process-global. Each test
    // owns them, while its worker threads still contend with one another.
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[derive(Default)]
    struct SparseMem(core::cell::RefCell<BTreeMap<u64, u64>>);

    impl Mem for SparseMem {
        fn load(&self, addr: u64) -> u64 {
            self.0.borrow().get(&addr).copied().unwrap_or(0)
        }
        fn store(&self, addr: u64, value: u64) {
            self.0.borrow_mut().insert(addr, value);
        }
    }

    #[test]
    fn clear_free_preserves_bounds_and_buffered_writes() {
        let _test = TEST_LOCK.lock().unwrap();
        let m = SparseMem::default();
        for (addr, len) in [(0x100000, STRIPE_BYTES), (0x100000, MAX_TX_CLEAR), (0x13fff8, 4096)] {
            for a in (addr - 8..addr + len + 8).step_by(8) { m.store(a, 7); }
            st(0).zgen = u32::MAX;
            begin(0, &m);
            write(0, addr - 8, 11);
            write(0, addr, 12);
            write(0, addr + len - 8, 13);
            write(0, addr + len, 14);
            clear_free(0, &m, addr, len);
            assert!(!doomed(0));
            assert_eq!(read(0, &m, addr), 0);
            assert_eq!(read(0, &m, addr + len - 8), 0);
            write(0, addr + 8, 15);
            assert!(commit(0, &m));
            end(0);
            assert_eq!(m.load(addr - 8), 11);
            assert_eq!(m.load(addr + len), 14);
            for a in (addr..addr + len).step_by(8) {
                assert_eq!(m.load(a), if a == addr + 8 { 15 } else { 0 });
            }
        }
        // Oversized or over-capacity clears must rerun without touching memory.
        for (addr, len) in [(0x100008, MAX_TX_CLEAR), (0x100000, 65536)] {
            m.store(addr, 99);
            begin(0, &m);
            clear_free(0, &m, addr, len);
            assert!(needs_serial(0));
            assert!(!commit(0, &m));
            end(0);
            assert_eq!(m.load(addr), 99);
        }
    }

    #[test]
    fn clear_free_rejects_stale_reads_and_restores_versions() {
        let _test = TEST_LOCK.lock().unwrap();
        let m = SparseMem::default();
        let base = 0x123000;
        // Cover validation of a held stripe and a stripe outside the clear.
        for marker in [base, base + 0x2000] {
            for i in 0..4 {
                begin(1, &m);
                write(1, base + i * STRIPE_BYTES, i + 1);
                assert!(commit(1, &m));
                end(1);
            }
            begin(0, &m);
            read(0, &m, marker);
            begin(1, &m);
            write(1, marker, 99);
            assert!(commit(1, &m));
            end(1);
            let versions = core::array::from_fn::<_, 4, _>(|i| TABLE[stripe(base + i as u64 * STRIPE_BYTES)].0.load(Ordering::Acquire));
            clear_free(0, &m, base, 64);
            assert!(!commit(0, &m));
            end(0);
            for (i, old) in versions.into_iter().enumerate() {
                let addr = base + i as u64 * STRIPE_BYTES;
                assert_eq!(TABLE[stripe(addr)].0.load(Ordering::Acquire), old);
                assert_eq!(m.load(addr), if addr == marker { 99 } else { i as u64 + 1 });
            }
        }
    }

    #[test]
    fn aligned_clear_stripes_are_one_ordered_interval() {
        // Exercise every high hash value and every supported block size.
        // Compare the shortcut to the actual per-line hash, including
        // addresses beyond the first 256 KiB block.
        for high in 0..ENTRIES as u64 {
            for bits in STRIPE_BITS..=MAX_TX_CLEAR.ilog2() {
                let len = 1u64 << bits;
                let addr = (high << 18) + ((high * 7919) & ((1 << 18) - 1) & !(len - 1));
                let n = (len / STRIPE_BYTES) as usize;
                let first = stripe(addr) & !(n - 1);
                let mut actual: std::vec::Vec<_> = (addr..addr + len).step_by(STRIPE_BYTES as usize).map(stripe).collect();
                actual.sort_unstable();
                assert!(actual.into_iter().eq(first..first + n));
            }
        }
    }

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
        let _test = TEST_LOCK.lock().unwrap();
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
                        begin(cpu, &TestMem);
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

    static REGION: [Line; 64] = [const { Line([const { AtomicU64::new(0) }; 8]) }; 64];
    static GEN: Line = Line([const { AtomicU64::new(0) }; 8]);

    /// The kernel's use of `clear_free`, on threads standing for cores 4..8
    /// (apart from the other test's): a region is either in use, holding
    /// its generation's pattern, or free (GEN's second word). A transaction
    /// finding it in use checks the pattern and frees it, as deleting the
    /// last object of an untyped does; one finding it free clears it in
    /// place, writes the next generation's pattern and marks it in use, as
    /// a reset and retype does. A clear landing after a later generation's
    /// writes, or a snapshot torn by an in-place clear, shows up as a wrong
    /// pattern in a committed reader.
    #[test]
    fn clear_free_keeps_live_data() {
        let _test = TEST_LOCK.lock().unwrap();
        let reg = |i: usize| &REGION[i / 8].0[i % 8] as *const AtomicU64 as u64;
        let gen = &GEN.0[0] as *const AtomicU64 as u64;
        let free = &GEN.0[1] as *const AtomicU64 as u64;
        GEN.0[1].store(1, Ordering::Relaxed);
        let len = (64 * 64) as u64;
        let threads: std::vec::Vec<_> = (4..8u64)
            .map(|cpu| {
                std::thread::spawn(move || {
                    let mut commits = 0;
                    while commits < 5_000 {
                        begin(cpu, &TestMem);
                        let g = read(cpu, &TestMem, gen);
                        let is_free = read(cpu, &TestMem, free) == 1;
                        let mut seen = std::vec::Vec::new();
                        if !is_free {
                            for i in (0..512).step_by(37) {
                                seen.push((read(cpu, &TestMem, reg(i)), g * 1000 + i as u64));
                            }
                            write(cpu, free, 1);
                        } else {
                            clear_free(cpu, &TestMem, reg(0), len);
                            for i in (0..512).step_by(37) {
                                write(cpu, reg(i), (g + 1) * 1000 + i as u64);
                            }
                            write(cpu, gen, g + 1);
                            write(cpu, free, 0);
                        }
                        if commit(cpu, &TestMem) {
                            for (v, want) in seen {
                                assert_eq!(v, want, "a committed reader saw the wrong generation");
                            }
                            commits += 1;
                        }
                        end(cpu);
                    }
                })
            })
            .collect();
        for t in threads {
            t.join().unwrap();
        }
        assert_eq!(GEN.0[0].load(Ordering::Relaxed), 10_000);
    }
}
