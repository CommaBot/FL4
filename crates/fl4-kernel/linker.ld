/* FL4 x86_64 kernel image. The boot section is linked and loaded at its
 * physical address so the 32-bit multiboot entry can run before paging;
 * everything else is linked in the top 2 GiB and loaded right after it. */
OUTPUT_FORMAT(elf64-x86-64)
ENTRY(_start)

KERNEL_PHYS = 0x100000;
KERNEL_OFFSET = 0xffffffff80000000;

PHDRS {
    boot PT_LOAD FLAGS(7);
    text PT_LOAD FLAGS(5);
    rodata PT_LOAD FLAGS(4);
    data PT_LOAD FLAGS(6);
}

SECTIONS
{
    . = KERNEL_PHYS;
    .boot : {
        KEEP(*(.multiboot))
        *(.boot.text)
        *(.boot.data)
        . = ALIGN(4096);
        *(.boot.bss)
    } :boot

    . = ALIGN(4096);
    . += KERNEL_OFFSET;
    .text : AT(ADDR(.text) - KERNEL_OFFSET) {
        *(.text .text.*)
    } :text
    . = ALIGN(4096);
    .rodata : AT(ADDR(.rodata) - KERNEL_OFFSET) {
        *(.rodata .rodata.*)
    } :rodata
    . = ALIGN(4096);
    .data : AT(ADDR(.data) - KERNEL_OFFSET) {
        *(.data .data.*)
    } :data
    .bss : AT(ADDR(.bss) - KERNEL_OFFSET) {
        __bss_start = .;
        *(.bss .bss.*)
        *(COMMON)
        . = ALIGN(4096);
        __bss_end = .;
    } :data
    . = ALIGN(4096);
    __kernel_end = .;
    /DISCARD/ : { *(.eh_frame*) *(.note*) *(.comment) }
}
