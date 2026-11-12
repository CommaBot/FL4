//! GDT, TSS, IDT and the SYSCALL MSRs.
//!
//! Selectors follow Linux (l4h 0028): kernel code 0x10, kernel data 0x18,
//! user 32-bit code 0x23, user data 0x2b, user 64-bit code 0x33, TSS 0x40.
use core::arch::asm;
use core::cell::UnsafeCell;
use fl4_arch_x86_64::cpu::{rdmsr, wrmsr, msr};
use fl4_arch_x86_64::percpu::{self, MAX_CPUS};

pub const KERNEL_CS: u16 = 0x10;
pub const KERNEL_DS: u16 = 0x18;
pub const TSS_SEL: u16 = 0x40;

const GDT_ENTRIES: usize = 10;

#[repr(C, align(16))]
struct Gdt([u64; GDT_ENTRIES]);

#[repr(C, align(16))]
struct Tss([u32; 26]);

#[repr(C, align(16))]
struct Idt([u64; 512]);

struct Tables {
    gdt: [Gdt; MAX_CPUS],
    tss: [Tss; MAX_CPUS],
    idt: Idt,
}

struct Cell(UnsafeCell<Tables>);
unsafe impl Sync for Cell {}

static TABLES: Cell = Cell(UnsafeCell::new(Tables {
    gdt: [const { Gdt([0; GDT_ENTRIES]) }; MAX_CPUS],
    tss: [const { Tss([0; 26]) }; MAX_CPUS],
    idt: Idt([0; 512]),
}));

extern "C" {
    static fl4_vectors: u8;
    fn fl4_syscall_entry();
}

#[repr(C, packed)]
struct Pointer {
    limit: u16,
    base: u64,
}

/// Vectors user code may raise with `int n`: #BP and the trap range.
fn user_gate(v: usize) -> bool {
    v == 3 || (0xa0..0xff).contains(&v)
}

/// Fill the IDT (shared by all cores).
pub fn init_idt() {
    let t = unsafe { &mut *TABLES.0.get() };
    let base = unsafe { &fl4_vectors as *const u8 as u64 };
    for v in 0..256 {
        let h = base + 16 * v as u64;
        let dpl: u64 = if user_gate(v) { 3 } else { 0 };
        let lo = (h & 0xffff) | ((KERNEL_CS as u64) << 16) | ((0x8e | (dpl << 5)) << 40) | (((h >> 16) & 0xffff) << 48);
        t.idt.0[2 * v] = lo;
        t.idt.0[2 * v + 1] = h >> 32;
    }
}

/// Load the GDT, TSS and IDT on core `cpu`, with `stack_top` as the
/// kernel stack for entries from user mode, and set up SYSCALL.
pub fn init_core(cpu: usize, stack_top: u64) {
    let t = unsafe { &mut *TABLES.0.get() };
    let g = &mut t.gdt[cpu].0;
    g[0] = 0;
    g[1] = 0;
    g[2] = 0x00af_9a00_0000_ffff; // 0x10 kernel code
    g[3] = 0x00cf_9200_0000_ffff; // 0x18 kernel data
    g[4] = 0x00cf_fa00_0000_ffff; // 0x20 user code (32-bit)
    g[5] = 0x00cf_f200_0000_ffff; // 0x28 user data
    g[6] = 0x00af_fa00_0000_ffff; // 0x30 user code (64-bit)
    g[7] = 0;
    let tss = &mut t.tss[cpu];
    tss.0 = [0; 26];
    tss.0[1] = stack_top as u32;
    tss.0[2] = (stack_top >> 32) as u32;
    // No I/O permission bitmap: the base is past the limit.
    tss.0[25] = 104 << 16;
    let tb = tss as *const Tss as u64;
    let limit = 103u64;
    g[8] = (limit & 0xffff) | ((tb & 0xff_ffff) << 16) | (0x89 << 40) | (((tb >> 24) & 0xff) << 56);
    g[9] = tb >> 32;

    let gp = Pointer { limit: (GDT_ENTRIES * 8 - 1) as u16, base: g.as_ptr() as u64 };
    let ip = Pointer { limit: (512 * 8 - 1) as u16, base: t.idt.0.as_ptr() as u64 };
    unsafe {
        asm!(
            "lgdt [{gp}]",
            "push {cs}",
            "lea {tmp}, [rip + 2f]",
            "push {tmp}",
            "retfq",
            "2:",
            "mov ds, {ds:e}",
            "mov es, {ds:e}",
            "mov ss, {ds:e}",
            "mov fs, {zero:e}",
            "mov gs, {zero:e}",
            "ltr {tss:x}",
            "lidt [{ip}]",
            gp = in(reg) &gp,
            ip = in(reg) &ip,
            cs = in(reg) KERNEL_CS as u64,
            ds = in(reg) KERNEL_DS as u64,
            zero = in(reg) 0u64,
            tss = in(reg) TSS_SEL as u64,
            tmp = out(reg) _,
        );
    }

    // SYSCALL: CS from STAR[47:32], SYSRET selectors from STAR[63:48].
    wrmsr(msr::EFER, rdmsr(msr::EFER) | 1);
    wrmsr(msr::STAR, (0x23u64 << 48) | ((KERNEL_CS as u64) << 32));
    wrmsr(msr::LSTAR, fl4_syscall_entry as *const () as u64);
    wrmsr(msr::CSTAR, fl4_syscall_entry as *const () as u64);
    // Clear TF, IF, DF, IOPL, NT and AC on entry.
    wrmsr(msr::FMASK, 0x4_7700);
    wrmsr(msr::FS_BASE, 0);
    wrmsr(msr::GS_BASE, 0);
    wrmsr(msr::KERNEL_GS_BASE, percpu::get_for(cpu) as *const _ as u64);
}
