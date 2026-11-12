//! The FL4 kernel image for x86_64.
#![no_std]

use core::fmt::Write;
use fl4_arch_x86_64::{cpu, serial};

core::arch::global_asm!(include_str!("boot.S"), options(att_syntax));

pub struct Console;

impl Write for Console {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for b in s.bytes() {
            serial::putc(b);
        }
        Ok(())
    }
}

#[macro_export]
macro_rules! kprintln {
    ($($arg:tt)*) => {{
        let _ = core::fmt::Write::write_fmt(&mut $crate::Console, format_args!($($arg)*));
        $crate::serial_newline();
    }};
}

pub fn serial_newline() {
    serial::putc(b'\n');
}

#[no_mangle]
pub extern "C" fn fl4_boot(magic: u32, info: u32) -> ! {
    serial::init();
    kprintln!("FL4 kernel (seL4 17.0 API, MCS) booting; multiboot magic {:#x} info {:#x}", magic, info);
    cpu::halt_forever()
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    kprintln!("FL4 panic: {}", info);
    cpu::halt_forever()
}
