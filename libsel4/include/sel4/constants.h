/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

#pragma once

#include <sel4/config.h>
#include <sel4/macros.h>

#ifndef __ASSEMBLER__

#ifdef CONFIG_HARDWARE_DEBUG_API
/* API arg values for breakpoint API, "type" arguments. */
typedef enum {
    seL4_DataBreakpoint = 0,
    seL4_InstructionBreakpoint,
    seL4_SingleStep,
    seL4_SoftwareBreakRequest,
    SEL4_FORCE_LONG_ENUM(seL4_BreakpointType)
} seL4_BreakpointType;

/* API arg values for breakpoint API, "access" arguments. */
typedef enum {
    seL4_BreakOnRead = 0,
    seL4_BreakOnWrite,
    seL4_BreakOnReadWrite,
    seL4_MaxBreakpointAccess,
    SEL4_FORCE_LONG_ENUM(seL4_BreakpointAccess)
} seL4_BreakpointAccess;

/* Format of a debug-exception message. */
typedef enum {
    seL4_DebugException_FaultIP,
    seL4_DebugException_ExceptionReason,
    seL4_DebugException_TriggerAddress,
    seL4_DebugException_BreakpointNumber,
    seL4_DebugException_Length,
    SEL4_FORCE_LONG_ENUM(seL4_DebugException_Msg)
} seL4_DebugException_Msg;
#endif

enum priorityConstants {
    seL4_InvalidPrio = -1,
    seL4_MinPrio = 0,
    seL4_MaxPrio = CONFIG_NUM_PRIORITIES - 1
};

/* seL4_MessageInfo_t defined in api/shared_types.bf */

enum seL4_MsgLimits {
    seL4_MsgLengthBits = 7,
    seL4_MsgExtraCapBits = 2,
    seL4_MsgMaxLength = 120
};

#define seL4_MsgMaxExtraCaps (LIBSEL4_BIT(seL4_MsgExtraCapBits)-1)

/* seL4_CapRights_t defined in shared_types_*.bf */
#define seL4_CapRightsBits 4

typedef enum {
    seL4_NoFailure = 0,
    seL4_InvalidRoot,
    seL4_MissingCapability,
    seL4_DepthMismatch,
    seL4_GuardMismatch,
    SEL4_FORCE_LONG_ENUM(seL4_LookupFailureType),
} seL4_LookupFailureType;

/* Size in bytes of the FPU save area transferred by seL4_TCB_ReadFPU/WriteFPU. */
#if defined(CONFIG_ARCH_X86)
/* FL4: the standard (uncompacted) XSAVE layout up to and including
 * PKRU, whatever the CPU enables at boot. AMX state is never enabled. */
#define seL4_FPUStateSize 2696
#elif defined(CONFIG_ARCH_AARCH64)
#define seL4_FPUStateSize (64 * 8 + 8)
#elif defined(CONFIG_ARCH_RISCV) && defined(CONFIG_RISCV_EXT_D)
#define seL4_FPUStateSize (32 * 8 + 4 + 4)
#elif defined(CONFIG_ARCH_RISCV)
#define seL4_FPUStateSize (32 * 4 + 4)
#else
#define seL4_FPUStateSize 0
#endif

/* Flags to be used with seL4_TCB_Set_Flags */
typedef enum {
    seL4_TCBFlag_NoFlag = 0x0,
    seL4_TCBFlag_fpuDisabled = 0x1,
    /* Every syscall instruction executed by the thread raises an
     * seL4_Fault_UnknownSyscall instead of being interpreted as an seL4
     * system call. Used to run foreign-ABI (e.g. Linux) user code. */
    seL4_TCBFlag_trapSyscalls = 0x2,

    SEL4_FORCE_LONG_ENUM(seL4_TCBFlag),
    seL4_TCBFlag_MASK = seL4_TCBFlag_NoFlag
                        | seL4_TCBFlag_trapSyscalls
#ifdef CONFIG_HAVE_FPU
                        | seL4_TCBFlag_fpuDisabled
#endif
} seL4_TCBFlag;

#endif /* !__ASSEMBLER__ */

#ifdef CONFIG_KERNEL_MCS
/* Minimum size of a scheduling context (2^{n} bytes) */
#define seL4_MinSchedContextBits 7
#ifndef __ASSEMBLER__
/* The size of a scheduling context, including the minimum 2 refills, excluding
   any extra refills (= 10 words, 2 tick_t, 2 refills (= 2 tick_t each)) */
#define seL4_CoreSchedContextBytes (10 * sizeof(seL4_Word) + (6 * 8))
/* the size of a single extra refill */
#define seL4_RefillSizeBytes (2 * 8)
SEL4_COMPILE_ASSERT(MinSchedContextBits_min_1, seL4_MinSchedContextBits > 1)
SEL4_COMPILE_ASSERT(MinSchedContextBits_sufficient,
                    seL4_CoreSchedContextBytes <= LIBSEL4_BIT(seL4_MinSchedContextBits))
SEL4_COMPILE_ASSERT(MinSchedContextBits_necessary,
                    seL4_CoreSchedContextBytes > LIBSEL4_BIT(seL4_MinSchedContextBits - 1))

/*
 * @brief Calculate the max extra refills a scheduling context can contain for a specific size.
 *
 * @param  size of the schedulding context. Must be >= seL4_MinSchedContextBits
 * @return the max number of extra refills that can be passed to seL4_SchedControl_Configure for
 *         this scheduling context
 */
static inline seL4_Word seL4_MaxExtraRefills(seL4_Word size)
{
    return (LIBSEL4_BIT(size) -  seL4_CoreSchedContextBytes) / seL4_RefillSizeBytes;
}

/* Flags to be used with seL4_SchedControl_ConfigureFlags */
typedef enum {
    seL4_SchedContext_NoFlag = 0x0,
    seL4_SchedContext_Sporadic = 0x1,
    SEL4_FORCE_LONG_ENUM(seL4_SchedContextFlag),
} seL4_SchedContextFlag;

#endif /* !__ASSEMBLER__ */
#endif /* CONFIG_KERNEL_MCS */

#ifdef CONFIG_KERNEL_INVOCATION_REPORT_ERROR_IPC
#define DEBUG_MESSAGE_START 6
#define DEBUG_MESSAGE_MAXLEN 50
#endif

/* FL4: seL4_KernelConfig, what the kernel found and chose at boot. These
 * are the kernel's fl4_abi::consts::kernel_config. Programs can test for
 * the call with #ifdef seL4_KernelConfig_Arch.
 *
 * Keys. One of the other architecture, like any the kernel does not know,
 * is seL4_InvalidArgument. */
/* Both architectures. */
#define seL4_KernelConfig_Arch 0x0001UL
#define seL4_KernelConfig_BuildFlags 0x0002UL
#define seL4_KernelConfig_OnlineCpus 0x0003UL
#define seL4_KernelConfig_MaxCpus 0x0004UL
/* Virtualization. */
#define seL4_KernelConfig_VirtBackend 0x0100UL
#define seL4_KernelConfig_VirtReject 0x0101UL
#define seL4_KernelConfig_VirtFeatures 0x0102UL
/* Virtualization, AArch64 only. */
#define seL4_KernelConfig_VirtS2IpaBits 0x0103UL
#define seL4_KernelConfig_VirtVgicLrs 0x0104UL
/* Confidential VM (0 on AArch64). */
#define seL4_KernelConfig_CvmType 0x0200UL
#define seL4_KernelConfig_CvmFlags 0x0201UL
/* Mitigations, x86_64 only. */
#define seL4_KernelConfig_SpecStatus 0x0300UL
#define seL4_KernelConfig_SpecReject 0x0301UL
#define seL4_KernelConfig_SpecFlags 0x0302UL
#define seL4_KernelConfig_SpecEntryActions 0x0303UL
#define seL4_KernelConfig_SpecVmexitActions 0x0304UL
/* The boot core's MSRs as the kernel left them at boot; 0 for one it does
 * not have or may not read (seL4_KernelConfig_SpecMsrValid). */
#define seL4_KernelConfig_SpecCtrlMsr 0x0305UL
#define seL4_KernelConfig_SpecTsxCtrlMsr 0x0306UL
#define seL4_KernelConfig_SpecMcuOptCtrlMsr 0x0307UL
#define seL4_KernelConfig_SpecEferMsr 0x0308UL
#define seL4_KernelConfig_SpecAmdDeCfgMsr 0x0309UL
#define seL4_KernelConfig_SpecAmdBpCfgMsr 0x030aUL
#define seL4_KernelConfig_SpecMsrValid 0x030bUL
/* Mitigations, AArch64 only. */
#define seL4_KernelConfig_ArmMitigations 0x0380UL
/* CPU and platform, x86_64 only. */
#define seL4_KernelConfig_X86CpuVendor 0x0400UL
#define seL4_KernelConfig_X86CpuFeatures 0x0401UL
#define seL4_KernelConfig_X86FpuXcr0 0x0402UL
#define seL4_KernelConfig_X86FpuSaveInsn 0x0403UL
#define seL4_KernelConfig_X86TscMhz 0x0404UL
#define seL4_KernelConfig_X86TscSource 0x0405UL
#define seL4_KernelConfig_X86MicrocodeRev 0x0406UL
#define seL4_KernelConfig_X86MaxPaddrBits 0x0407UL
#define seL4_KernelConfig_X86IoapicCount 0x0408UL
#define seL4_KernelConfig_X86ArchCapabilities 0x0409UL
/* CPU and platform, AArch64 only. */
#define seL4_KernelConfig_ArmPlatformFlags 0x0480UL
#define seL4_KernelConfig_ArmPaBits 0x0481UL
#define seL4_KernelConfig_ArmGicVersion 0x0482UL
#define seL4_KernelConfig_ArmMaxSpi 0x0483UL
#define seL4_KernelConfig_ArmPsciMethod 0x0484UL
#define seL4_KernelConfig_ArmTimerFreqHz 0x0485UL
/* seL4_KernelConfig_Arch. */
#define seL4_KernelConfig_Arch_X86_64 1UL
#define seL4_KernelConfig_Arch_AArch64 2UL
/* seL4_KernelConfig_BuildFlags: the settings the kernel was built with. */
#define seL4_KernelConfig_BuildFlag_DebugBuild (1UL << 0)
#define seL4_KernelConfig_BuildFlag_Printing (1UL << 1)
#define seL4_KernelConfig_BuildFlag_Smp (1UL << 2)
#define seL4_KernelConfig_BuildFlag_HwDebugApi (1UL << 3)
#define seL4_KernelConfig_BuildFlag_ExportPmcUser (1UL << 4)
#define seL4_KernelConfig_BuildFlag_DangerousMsr (1UL << 5)
/* seL4_KernelConfig_VirtBackend. */
#define seL4_KernelConfig_VirtBackend_None 0UL
#define seL4_KernelConfig_VirtBackend_Vtx 1UL
#define seL4_KernelConfig_VirtBackend_AmdV 2UL
#define seL4_KernelConfig_VirtBackend_El2Vhe 3UL
#define seL4_KernelConfig_VirtBackend_El2Nvhe 4UL
/* seL4_KernelConfig_VirtReject: why there is no virtualization backend (None exactly
 * when there is one). */
#define seL4_KernelConfig_VirtReject_None 0UL
#define seL4_KernelConfig_VirtReject_NoHw 1UL
#define seL4_KernelConfig_VirtReject_DisabledByFirmware 2UL
#define seL4_KernelConfig_VirtReject_MissingFeatures 3UL
#define seL4_KernelConfig_VirtReject_SpecPolicyRejected 4UL
#define seL4_KernelConfig_VirtReject_SkimActive 5UL
#define seL4_KernelConfig_VirtReject_CvmActive 6UL
#define seL4_KernelConfig_VirtReject_VmxonFailed 7UL
#define seL4_KernelConfig_VirtReject_NovirtCmdline 8UL
#define seL4_KernelConfig_VirtReject_NoVgic 9UL
#define seL4_KernelConfig_VirtReject_El1Only 10UL
/* seL4_KernelConfig_VirtFeatures: the same bits mean different features on x86_64 and
 * AArch64. */
#define seL4_KernelConfig_VirtFeature_X86VpidSingle (1UL << 0)
#define seL4_KernelConfig_VirtFeature_X86VpidAll (1UL << 1)
#define seL4_KernelConfig_VirtFeature_X86InveptSingle (1UL << 2)
#define seL4_KernelConfig_VirtFeature_X86SvmVmcbClean (1UL << 3)
#define seL4_KernelConfig_VirtFeature_X86VmxPerfGlobalCtrl (1UL << 4)
#define seL4_KernelConfig_VirtFeature_ArmVirtReady (1UL << 0)
#define seL4_KernelConfig_VirtFeature_ArmVmid16 (1UL << 1)
#define seL4_KernelConfig_VirtFeature_ArmGicv2Vgic (1UL << 2)
#define seL4_KernelConfig_VirtFeature_ArmGicv3Vgic (1UL << 3)
/* seL4_KernelConfig_CvmType. */
#define seL4_KernelConfig_CvmType_None 0UL
#define seL4_KernelConfig_CvmType_Sev 1UL
#define seL4_KernelConfig_CvmType_SevSnp 2UL
#define seL4_KernelConfig_CvmType_Tdx 3UL
/* seL4_KernelConfig_CvmFlags. */
#define seL4_KernelConfig_CvmFlag_Hardened (1UL << 0)
#define seL4_KernelConfig_CvmFlag_SharedDma (1UL << 1)
/* seL4_KernelConfig_SpecStatus. */
#define seL4_KernelConfig_SpecStatus_Incomplete 0UL
#define seL4_KernelConfig_SpecStatus_Complete 1UL
/* seL4_KernelConfig_SpecReject: why seL4_KernelConfig_SpecStatus is Incomplete. */
#define seL4_KernelConfig_SpecReject_None 0UL
#define seL4_KernelConfig_SpecReject_Vendor 1UL
#define seL4_KernelConfig_SpecReject_Meltdown 2UL
#define seL4_KernelConfig_SpecReject_Smep 3UL
#define seL4_KernelConfig_SpecReject_BeforeZen2 4UL
#define seL4_KernelConfig_SpecReject_Ibpb 5UL
#define seL4_KernelConfig_SpecReject_SrsoMicrocode 6UL
#define seL4_KernelConfig_SpecReject_BufferMicrocode 7UL
#define seL4_KernelConfig_SpecReject_ItsMicrocode 8UL
#define seL4_KernelConfig_SpecReject_Lfence 9UL
/* seL4_KernelConfig_SpecFlags. */
#define seL4_KernelConfig_SpecFlag_Skim (1UL << 0)
#define seL4_KernelConfig_SpecFlag_SafeRet (1UL << 1)
#define seL4_KernelConfig_SpecFlag_Retpoline (1UL << 2)
#define seL4_KernelConfig_SpecFlag_Eibrs (1UL << 3)
#define seL4_KernelConfig_SpecFlag_AutoIbrs (1UL << 4)
#define seL4_KernelConfig_SpecFlag_LegacyIbrs (1UL << 5)
#define seL4_KernelConfig_SpecFlag_Stibp (1UL << 6)
#define seL4_KernelConfig_SpecFlag_BhiDisS (1UL << 7)
#define seL4_KernelConfig_SpecFlag_VerwBuffers (1UL << 8)
#define seL4_KernelConfig_SpecFlag_NoSmt (1UL << 9)
#define seL4_KernelConfig_SpecFlag_DisableTsx (1UL << 10)
#define seL4_KernelConfig_SpecFlag_VmexitIbpbDeferred (1UL << 11)
#define seL4_KernelConfig_SpecFlag_EagerFpu (1UL << 12)
/* seL4_KernelConfig_SpecEntryActions and seL4_KernelConfig_SpecVmexitActions. */
#define seL4_KernelConfig_SpecAction_Ibpb (1UL << 0)
#define seL4_KernelConfig_SpecAction_Rsb (1UL << 1)
#define seL4_KernelConfig_SpecAction_Pbrsb (1UL << 2)
#define seL4_KernelConfig_SpecAction_LegacyIbrs (1UL << 3)
#define seL4_KernelConfig_SpecAction_Bhb (1UL << 4)
#define seL4_KernelConfig_SpecAction_Ibhf (1UL << 5)
/* seL4_KernelConfig_SpecMsrValid: the MSRs read or written at boot. */
#define seL4_KernelConfig_SpecMsrValid_ArchCapabilities (1UL << 0)
#define seL4_KernelConfig_SpecMsrValid_SpecCtrl (1UL << 1)
#define seL4_KernelConfig_SpecMsrValid_TsxCtrl (1UL << 2)
#define seL4_KernelConfig_SpecMsrValid_McuOptCtrl (1UL << 3)
#define seL4_KernelConfig_SpecMsrValid_Efer (1UL << 4)
#define seL4_KernelConfig_SpecMsrValid_AmdDeCfg (1UL << 5)
#define seL4_KernelConfig_SpecMsrValid_AmdBpCfg (1UL << 6)
/* seL4_KernelConfig_ArmMitigations. */
#define seL4_KernelConfig_ArmMitigation_Pan (1UL << 0)
#define seL4_KernelConfig_ArmMitigation_Pauth (1UL << 1)
#define seL4_KernelConfig_ArmMitigation_Clrbhb (1UL << 2)
/* seL4_KernelConfig_X86CpuVendor. */
#define seL4_KernelConfig_X86Vendor_Other 0UL
#define seL4_KernelConfig_X86Vendor_Intel 1UL
#define seL4_KernelConfig_X86Vendor_Amd 2UL
#define seL4_KernelConfig_X86Vendor_Hygon 3UL
/* seL4_KernelConfig_X86CpuFeatures: what the kernel turned on, but Hypervisor
 * (CPUID.1:ECX[31]). */
#define seL4_KernelConfig_X86Feature_Nx (1UL << 0)
#define seL4_KernelConfig_X86Feature_Smep (1UL << 1)
#define seL4_KernelConfig_X86Feature_Smap (1UL << 2)
#define seL4_KernelConfig_X86Feature_Fsgsbase (1UL << 3)
#define seL4_KernelConfig_X86Feature_HugePages1G (1UL << 4)
#define seL4_KernelConfig_X86Feature_Pcid (1UL << 5)
#define seL4_KernelConfig_X86Feature_Invpcid (1UL << 6)
#define seL4_KernelConfig_X86Feature_X2apic (1UL << 7)
#define seL4_KernelConfig_X86Feature_TscDeadline (1UL << 8)
#define seL4_KernelConfig_X86Feature_IdlePoll (1UL << 9)
#define seL4_KernelConfig_X86Feature_Hypervisor (1UL << 10)
/* seL4_KernelConfig_X86FpuSaveInsn. */
#define seL4_KernelConfig_X86FpuInsn_Fxsave 0UL
#define seL4_KernelConfig_X86FpuInsn_Xsave 1UL
#define seL4_KernelConfig_X86FpuInsn_Xsaveopt 2UL
#define seL4_KernelConfig_X86FpuInsn_Xsavec 3UL
#define seL4_KernelConfig_X86FpuInsn_Xsaves 4UL
/* seL4_KernelConfig_X86TscSource. */
#define seL4_KernelConfig_X86TscSource_Cpuid 1UL
#define seL4_KernelConfig_X86TscSource_Hypervisor 2UL
#define seL4_KernelConfig_X86TscSource_Pit 3UL
#define seL4_KernelConfig_X86TscSource_Kvm 4UL
/* seL4_KernelConfig_ArmPlatformFlags. */
#define seL4_KernelConfig_ArmPlatformFlag_Asid16 (1UL << 0)
#define seL4_KernelConfig_ArmPlatformFlag_HwAf (1UL << 1)
#define seL4_KernelConfig_ArmPlatformFlag_Gicv3Sre (1UL << 2)
#define seL4_KernelConfig_ArmPlatformFlag_ItsActive (1UL << 3)
#define seL4_KernelConfig_ArmPlatformFlag_TimerLocalAck (1UL << 4)
#define seL4_KernelConfig_ArmPlatformFlag_El2Vhe (1UL << 5)
#define seL4_KernelConfig_ArmPlatformFlag_El2Nvhe (1UL << 6)
/* seL4_KernelConfig_ArmPsciMethod. */
#define seL4_KernelConfig_ArmPsci_Absent 0UL
#define seL4_KernelConfig_ArmPsci_Smc 1UL
#define seL4_KernelConfig_ArmPsci_Hvc 2UL
