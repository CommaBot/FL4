/-
P3 (line mmuAD, gen 24): **the VT-x step theorems at a VM-epoch joint state `JAtZV`** (any `V`, `X`).

Gens 21–23 derived the layout / placement premises of the VT-x step theorems (`JVLay`, `DetAtB`, `FinPl`, `hnd`,
`hhv`, `hhc`, …) from `JAtZ`. `JAtZ` carries `ext : JExt` (every slot cap native, every TCB VCPU word 0), false in
every state where a VCPU is bound or a Vcpu cap exists, so those derivations only applied to degenerate VM
states. None of them reads `ext`: this module re-states each over `JAtZB` (= `JAtZ` without `ext`, P3/JAtZV), proofs
copied verbatim from P3/BufAtJ, P3/JExtVLay, P3/JExtVFin, P3/JExtVList, P3/JExtVListSteps with `JAtZ` → `JAtZB`
(names `JAtZB.<same name>`: `bufWordG`, `rbufU`, `thTcb`, `bufU_rbuf`, `bufU_B`, `bufU_noSlot`, `thH`, `jvLay`,
`nodePl`, `nodeW`, `tw_nBC`, `bufOK`, `detAtB`, `hnd`, `hhv`, `hhc`, `finPl`, `finPlV`, `jwPl`, `detPl`, `hact`,
`hct`, `thrCap`, `hTt`).

New:
* **`JAtZB.hU`** / **`JAtZ.hU`**: the VCPU list head word is no IPC-buffer word (`P1.vHeadA st s ∉ BufU Z σ`) —
  gen 23's last [J] of `vcpu_finalise_vlJ`. Proof: an IPC-buffer word is a `Z.B` word (`bufU_B`: `IpcBufCapOK` +
  `FrameCover`), `KsApart.buf` puts every `Z.B` word off `[ksb, ksb + 13568)`, and the head word is `ksb + 80`
  (`vHead_val`). **`vcpu_finalise_vlJ'`**: `vcpu_finalise_vlJ` with no premise beyond its state facts.
* At `J : JAtZV V X …` (all placement premises discharged):
  **`JAtZV.finalise`** (`vcpu.finalise v`, `v ∈ V`: `JExtV`, `RunVmB`, `v.TCB = 0`, `VList (V \ {v})`; no premise),
  **`JAtZV.detach`** (`DetPost`; no premise), **`JAtZV.settcb`** (`vcpu.decode … X86VCPUSetTCB`; `hexs` [J]: the
  extra cap slots are slots of the typed heap, a syscall front-end fact, P1 `DecPre.extra`),
  **`JAtZV.enterU`** (unbound thread; no premise), **`JAtZV.enter`** (bound thread, every branch incl. the
  signalled one; `hRt` [J]: the entering thread's state word is not `BlockedR` — a fact of the call site, the
  current thread at kernel exit), **`JAtZV.sts`** (`set_thread_state`).
  These give the extension half (`JExtV`, `RunVmB`, `VList`) of `JAtZV` after each VT-x step from a VM-epoch
  state; the `JAtZB` half after these steps is not proved here (open: needs `xtop.rel` over the extended spec).

Named premises: `hexs` [J], `hRt` [J] (both stated where used). No [P] / [W] / [S]. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/BufAtJ `bufOK`, `bufU_B`,
`bufU_noSlot`, `bufU_rbuf`, `bufWordG`, `rbufU`, `thTcb`; P3/JExtVFin `finPl`, `hTt`; P3/JExtVLay `detAtB`, `detPl`,
`hact`, `hct`, `jvLay`, `jwPl`, `nodePl`, `nodeW`, `thH`, `thrCap`, `tw_nBC`; P3/JExtVList `finPlV`; P3/JExtVListSteps
`hhc`, `hhv`, `hnd`.
-/
import Fl4Proofs.P3.JAtZV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

end

section
open fl4_core Classical

end

section
open fl4_core Classical Fl4Proofs.P0.Consts

end

section
open fl4_core Classical Fl4Proofs.P0.Consts

end

section
open fl4_core Classical Fl4Proofs.P0.Consts

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

end

section
open fl4_core Classical

/-- **The head word is no IPC-buffer word** (module docstring; gen 23's `hU` [J], discharged). -/
theorem JAtZB.hU (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) : P1.vHeadA st s ∉ BufU Z σ := by
  intro hu
  obtain ⟨wp, hwp, he⟩ := J.bufU_B hu
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  have hb := J.ks.buf wp hwp
  rw [he, hv] at hb
  omega

/-- `JAtZB.hU` at a native joint state. -/
theorem JAtZ.hU (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : P1.vHeadA st s ∉ BufU Z σ := J.toB.hU

/-- **`vcpu_finalise_vlJ` without `hU`.** -/
theorem vcpu_finalise_vlJ' {ar : machine.Arch A} (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s)
    (Vl : VList st V Z.th s) (a' : A) {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) Z.th r.1 ⦄ :=
  vcpu_finalise_vlJ hA J Jv E R Vl J.hU a' hvV

variable {ar : machine.Arch A}

/-- **`vcpu.finalise` at a VM-epoch joint state** (no premise). -/
theorem JAtZV.finalise (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) Z.th r.1 ⦄ :=
  vcpu_finalise_vl hA (J.base.jvLay J.vm) (J.base.detAtB J.vm) J.extv J.rvm J.vl (J.base.hnd J.vm)
    (J.base.hhv J.vm) (J.base.hhc J.vm J.vl J.base.hU) a' hvV

/-- **`vcpu.detach` at a VM-epoch joint state** (no premise). -/
theorem JAtZV.detach (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) :
    vcpu.detach st ar s a' t ⦃ r => DetPost st V X Z.th (fun _ => BufU Z σ) t s r.1 ⦄ :=
  vcpu_detach_jvB hA (J.base.detPl J.vm) (J.base.detAtB J.vm) J.extv J.rvm a' ht

/-- **`X86VCPUSetTCB` at a VM-epoch joint state**; `hexs` [J]: every nonzero extra cap slot is a slot of the typed
heap (the syscall front end's `lookup_extra_caps`, P1 `DecPre.extra`). -/
theorem JAtZV.settcb (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hvV : v ∈ V)
    (hexs : ∀ x ∈ extra.val, x ≠ 0#u64 → IsSlot Z.th x) :
    vcpu.decode st ar s a' fl4_abi.label.X86VCPUSetTCB len v call buf extra ⦃ r s' _ =>
      JExtV (L := L) V X Z.th s' ∧ RunVmB (L := L) Z.th s' ⦄ :=
  vcpu_decode_settcb_jvB hA (J.base.detPl J.vm) (J.base.detAtB J.vm) J.extv J.rvm a' hvV
    (fun x hx h0 => ⟨hexs x hx h0, J.base.thrCap (hexs x hx h0)⟩) J.base.hct

/-- **`vcpu.enter` of an unbound thread at a VM-epoch joint state** (no premise). -/
theorem JAtZV.enterU (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) (h0 : L.mem s (tVcpuA t) = 0#u64) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ :=
  vcpu_enter_unbound hA (J.base.detPl J.vm) J.extv J.rvm a' ht h0

set_option maxHeartbeats 4000000 in
/-- **`vcpu.enter` of a bound thread at a VM-epoch joint state** (every branch, the signalled one included);
`hRt` [J]: the entering thread's state word is not `BlockedR` (the call site's fact: `vcpu::enter` runs for the
current thread at kernel exit). -/
theorem JAtZV.enter (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hRt : ¬ P1.BlockedR (L.mem s (P1.stA t))) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ := by
  obtain ⟨_, _, hJ⟩ := J.base.jpl
  exact vcpu_enter_boundL hA (J.base.jvLay J.vm) (J.base.detAtB J.vm) J.extv J.rvm a' ht hv0 J.base.blk
    J.base.kern.heap J.vm.heap J.base.hTt (hJ.slotCapW (Sched.tLowSlots_all _)) hRt

/-- **`set_thread_state` at a VM-epoch joint state** (`sts_jv`; to `TS_RUNNING_VM` only for a bound thread). -/
theorem JAtZV.sts (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t x : U64} (ht : Z.th t = some .tcb)
    (hx : x ≠ 8#u64 ∨ L.mem s (tVcpuA t) ≠ 0#u64) :
    sched.set_thread_state st s t x ⦃ s' => JExtV (L := L) V X Z.th s' ∧ RunVmB (L := L) Z.th s' ⦄ :=
  sts_jv (J.base.jwPl J.vm) J.extv J.rvm ht (J.base.hact J.vm) hx

end

end

end

end Fl4Proofs.P3
