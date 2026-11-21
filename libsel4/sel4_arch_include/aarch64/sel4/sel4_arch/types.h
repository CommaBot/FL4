/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/simple_types.h>

typedef seL4_CPtr seL4_ARM_VSpace;

typedef struct seL4_UserContext_ {
    /* frame registers */
    seL4_Word pc, sp, spsr, x0, x1, x2, x3, x4, x5, x6, x7, x8, x16, x17, x18, x29, x30;
    /* other integer registers */
    seL4_Word x9, x10, x11, x12, x13, x14, x15, x19, x20, x21, x22, x23, x24, x25, x26, x27, x28;
    /* Thread ID registers */
    seL4_Word tpidr_el0, tpidrro_el0;
} seL4_UserContext;

typedef struct seL4_ARM_SMCContext_ {
    /* register arguments */
    seL4_Word x0, x1, x2, x3, x4, x5, x6, x7;
} seL4_ARM_SMCContext;

/* Bulk VCPU state transfer layout (1024 bytes, 64-byte aligned).
 * `gprs[37]` order: X0..X30, SP_EL0, ELR_EL1 (PC), SPSR_EL1, FAULT_IP, TPIDR_EL0, TPIDRRO_EL0. */
typedef struct seL4_ARM_VCPUState_ {
    seL4_Word regs[64];
    seL4_Word gprs[37];
    seL4_Word vppi_masked;
    seL4_Word reserved[26];
} seL4_ARM_VCPUState;
