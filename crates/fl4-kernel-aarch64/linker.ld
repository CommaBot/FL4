/* FL4 AArch64 kernel image. Linked at KERNEL_VBASE (fl4-bootinfo); the
 * UEFI loader places it at the start of the 2 MiB-aligned kernel region.
 * _start and _ap_start run at their physical addresses with the MMU off,
 * so .boot holds position-independent code only. */
OUTPUT_FORMAT(elf64-littleaarch64)
ENTRY(_start)

KERNEL_VBASE = 0xffffff7f80000000;

PHDRS {
    text PT_LOAD FLAGS(5);
    rodata PT_LOAD FLAGS(4);
    data PT_LOAD FLAGS(6);
}

SECTIONS
{
    . = KERNEL_VBASE;
    __kernel_start = .;
    .text : {
        KEEP(*(.boot.text))
        . = ALIGN(2048);
        KEEP(*(.hyp.text))
        . = ALIGN(4096);
        KEEP(*(.boot.data))
        . = ALIGN(2048);
        KEEP(*(.text.vectors))
        *(.text .text.*)
    } :text
    . = ALIGN(4096);
    __text_end = .;
    .rodata : {
        *(.rodata .rodata.*)
    } :rodata
    . = ALIGN(4096);
    __rodata_end = .;
    .data : {
        *(.data .data.*)
        *(.got .got.*)
    } :data
    .bss : {
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
