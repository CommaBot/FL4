/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/config.h>

typedef enum _object {
    seL4_ARM_SmallPageObject = seL4_ModeObjectTypeCount,
    seL4_ARM_LargePageObject,
#ifdef CONFIG_ARCH_AARCH32
    seL4_ARM_SectionObject,
    seL4_ARM_SuperSectionObject,
#endif
    seL4_ARM_PageTableObject,
#if defined(CONFIG_ARM_HYPERVISOR_SUPPORT) || defined(CONFIG_ARCH_AARCH64)
    seL4_ARM_VCPUObject,
#endif
#ifdef CONFIG_ARCH_AARCH64
    seL4_ARM_Stage2VSpaceObject,
    /* FL4: TTBR1 EL0 window (seL4_TCB_SetHighVSpace), no EL2 needed. */
    seL4_ARM_HighVSpaceObject,
#endif
#ifdef CONFIG_TK1_SMMU
    seL4_ARM_IOPageTableObject,
#endif
    seL4_ObjectTypeCount
} seL4_ArchObjectType;

typedef seL4_Word object_t;

#if !defined(CONFIG_ARM_HYPERVISOR_SUPPORT) && !defined(CONFIG_ARCH_AARCH64)
#define seL4_ARM_VCPUObject 0xfffe
#endif

#ifndef CONFIG_TK1_SMMU
#define seL4_ARM_IOPageTableObject 0xffff
#endif
