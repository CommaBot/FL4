//! `fl4_core::machine::Arch` on x86_64 hardware.
use crate::{apic, cpu, fpu, ioapic, percpu, serial, timer};
use fl4_core::layout::{irq, PPTR_BASE};
use fl4_core::machine::Arch;

pub struct PhysArch;

/// IRR bits for the vectors the kernel takes as IRQs (0x20..=0x9f).
fn irq_requested() -> bool {
    let mut w = 1;
    while w <= 4 {
        let v = apic::read(apic::REG_IRR + w * 0x10);
        if v != 0 {
            return true;
        }
        w += 1;
    }
    false
}

impl Arch for PhysArch {
    fn now(&mut self) -> u64 {
        timer::now()
    }
    fn set_deadline(&mut self, ticks: u64) {
        timer::set_deadline(ticks)
    }
    fn us_to_ticks(&self, us: u64) -> u64 {
        timer::us_to_ticks(us)
    }
    fn ticks_to_us(&self, ticks: u64) -> u64 {
        timer::ticks_to_us(ticks)
    }
    fn max_us(&self) -> u64 {
        timer::max_us()
    }
    fn kernel_wcet_ticks(&self) -> u64 {
        timer::us_to_ticks(timer::KERNEL_WCET_US)
    }

    fn irq_pending(&mut self) -> bool {
        irq_requested()
    }
    fn take_pending_irq(&mut self) -> u64 {
        let pc = percpu::get();
        pc.polled_irq = percpu::NO_IRQ;
        pc.polling = true;
        cpu::enable_interrupts_briefly();
        let pc = percpu::get();
        pc.polling = false;
        pc.polled_irq
    }
    fn mask_irq(&mut self, irq: u64, mask: bool) {
        ioapic::mask(irq, mask)
    }
    fn ack_irq(&mut self, _irq: u64) {
        apic::eoi()
    }

    fn set_vspace(&mut self, root: u64, asid: u64) {
        let cr3 = root.wrapping_sub(PPTR_BASE);
        let pc = percpu::get();
        if pc.cr3 != cr3 {
            cpu::write_cr3(cr3);
            pc.cr3 = cr3;
        }
        pc.asid = asid;
    }
    fn invalidate_page(&mut self, asid: u64, vaddr: u64) {
        if percpu::get().asid == asid {
            cpu::invlpg(vaddr);
        }
    }
    fn invalidate_asid(&mut self, asid: u64) {
        if percpu::get().asid == asid {
            cpu::write_cr3(cpu::read_cr3());
        }
    }
    fn invalidate_page_structures(&mut self, asid: u64) {
        self.invalidate_asid(asid)
    }

    fn ioapic_map(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64) -> bool {
        if ioapic >= ioapic::count() || pin >= ioapic::pins(ioapic) {
            return false;
        }
        ioapic::map(ioapic, pin, level, polarity, vector, percpu::get_for(0).apic_id, 0, 0);
        true
    }
    fn ioapic_map_remapped(&mut self, ioapic: u64, pin: u64, level: u64, polarity: u64, vector: u64, handle: u64) -> bool {
        if ioapic >= ioapic::count() || pin >= ioapic::pins(ioapic) {
            return false;
        }
        let high = (((handle & 0x7fff) as u32) << 17) | (1 << 16);
        let lo_extra = (((handle >> 15) & 1) as u32) << 11;
        ioapic::map(ioapic, pin, level, polarity, vector, 0, high, lo_extra);
        true
    }
    fn num_ioapics(&self) -> u64 {
        ioapic::count()
    }
    fn ioapic_pins(&self, i: u64) -> u64 {
        ioapic::pins(i)
    }

    fn port_in(&mut self, port: u64, size: u64) -> u64 {
        let p = port as u16;
        match size {
            1 => cpu::inb(p) as u64,
            2 => cpu::inw(p) as u64,
            _ => cpu::inl(p) as u64,
        }
    }
    fn port_out(&mut self, port: u64, size: u64, v: u64) {
        let p = port as u16;
        match size {
            1 => cpu::outb(p, v as u8),
            2 => cpu::outw(p, v as u16),
            _ => cpu::outl(p, v as u32),
        }
    }

    fn fpu_flush(&mut self, tcb: u64) {
        fpu::flush(tcb)
    }
    fn fpu_sanitise(&mut self, tcb: u64) {
        fpu::sanitise(tcb)
    }
    fn fpu_reload(&mut self, tcb: u64) {
        fpu::forget(tcb)
    }
    fn fpu_release(&mut self, tcb: u64) {
        fpu::forget(tcb)
    }

    fn putc(&mut self, c: u64) {
        serial::putc(c as u8)
    }
    fn get_char(&mut self) -> u64 {
        match serial::getc() {
            Some(c) => c as u64,
            None => u64::MAX,
        }
    }
    fn halt(&mut self) {
        for b in b"FL4: halted by seL4_DebugHalt\n" {
            serial::putc(*b);
        }
        cpu::halt_forever()
    }
}

/// Vector of the kernel timer interrupt.
pub const TIMER_VECTOR: u32 = (irq::TIMER + irq::INT_OFFSET) as u32;
