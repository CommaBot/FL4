/-
P3 (line mmuAD, gen 37): **the VCPU-cap arm of the syscall-level invocation step at `JAtZV3`** — FL4's
`syscall.decode_invocation … (Cap.Vcpu p) …` (syscall.rs: `cur_thread`, then the cap's `vcpu::decode`) paired with
the extended spec's `fl4DecodeInvocationV` at `.archObjectCap (.vcpuCap p)` (Ext/VirtDispatch: `liftME .vcpu` of
`decodeVcpuInvocation`) and FL4's dispatcher `fl4PerformInvocationVF onCore remoteCur` at `.vcpu inv`
(Ext/VirtKernelF: `liftE` of `performVcpuInvocationF`).

* `zv_sysdec_vcpu`: FL4's `decode_invocation` at a VCPU cap is `vcpu.decode` (the `cur_thread` it reads first is
  total and unused in that arm).
* `zv_decV_vcpu` / `zv_perfV_vcpu`: the spec's extended decoder / perform at a VCPU cap / invocation (definitional).
* **`VInvPost`**: `VDecPostC` (`P3/JAtZV3VDisp`) at the syscall level: for every first-phase flag, cap reference,
  slot, IPC buffer, `onCore` / `remoteCur` oracles and block/call/donate flags, the error case with the extended
  decoder's single outcome `(.error e', σ)`, or success with its single outcome `(.ok (.vcpu inv), σ)` and the
  extended perform's single outcome `(.ok rep, σ')`, `JAtZV3` at FL4's state `s'` and `σ'`, `VDecTail` from `s'`.
* **`JAtZV3.vcpuInvJ`**: FL4's `syscall.decode_invocation … (Cap.Vcpu p) …` from `JAtZV3`, every label, satisfies
  `VInvPost` — gen 37's `JAtZV3.vcpuDecodeJ` lifted through the cap dispatch on both sides. So the VM-epoch
  invocation step has no VCPU gap but `VcpuNyp`'s fields (and the dispatcher's scope).

Premises: exactly `vcpuDecodeJ`'s ([J] `VcpuNyp arI AR`; [P] `ZvVirtAgree`, `ZvSyncKeep`, `∀ a, CapAgree arI a`;
`P0.ArchTotal`, `ARKeep`; scope `BufOut V buf`, the `ex[0]` slot facts, `hct`, EnableIOPort's `IoFresh`). No new
premise; no existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3VDisp
import Fl4Proofs.P3.IrqIssue
import Fl4Proofs.P3.CnodeCopy
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Fl4Spec

theorem zv_decV_vcpu (fp : Bool) (label : Data) (args : List Data) (cref : CapRef) (slot : CslotPtr) (v : ObjRef)
    (ec : List (Cap × CslotPtr)) (buffer : Option ObjRef) :
    fl4DecodeInvocationV (Z := Unit) fp label args cref slot (.archObjectCap (.vcpuCap v)) ec buffer =
      NonDetE.liftME Fl4InvocationV.vcpu (decodeVcpuInvocation label args v ec) := rfl

theorem zv_perfV_vcpu (onCore remoteCur : ObjRef → Bool) (bl ca cd : Bool) (i : VcpuInvocation) :
    fl4PerformInvocationVF (Z := Unit) onCore remoteCur bl ca cd (.vcpu i) =
      NonDetE.liftE (performVcpuInvocationF i) := rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`VDecPostC` at the syscall level** (module docstring). -/
def VInvPost (arI : machine.Arch A) (V X : Set U64) (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap)
    (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (σ : Fl4Spec.State Unit)
    (lbl len p : U64) (call : Bool) (buf : U64) (b : Bool) (c : capability.Cap)
    (r : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ ct : U64, sched.cur_thread st s = ok ct ∧
    ∀ (args : List Fl4Spec.Data) (ec : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), VArgs st s ct buf len args →
      VCaps b c ec →
      ∀ (fp : Bool) (cref : Fl4Spec.CapRef) (slot : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
        (onCore remoteCur : Fl4Spec.ObjRef → Bool) (bl ca cd : Bool),
      (∃ e e', r.1 = .Err e ∧ SysErrRel e e' ∧
        ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp lbl.bv args cref slot
          (.archObjectCap (.vcpuCap p.bv)) ec buffer) σ = ({(.error e', σ)}, False) ∧
        r.2.1 = s ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s r.2.2 σ) ∨
      (∃ (inv : Fl4Spec.VcpuInvocation) (rep : List Fl4Spec.Data) (s' : S) (σ' : Fl4Spec.State Unit)
          (Ac' : Set U64) (Lst' : U64 → List U64), r.1 = .Ok () ∧
        ExceptT.run (Fl4Spec.fl4DecodeInvocationV (Z := Unit) fp lbl.bv args cref slot
          (.archObjectCap (.vcpuCap p.bv)) ec buffer) σ = ({(.ok (.vcpu inv), σ)}, False) ∧
        ExceptT.run (Fl4Spec.fl4PerformInvocationVF (Z := Unit) onCore remoteCur bl ca cd (.vcpu inv)) σ =
          ({(.ok rep, σ')}, False) ∧
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D s' r.2.2 σ' ∧ VDecTail st ct call rep s' r.2.1)

end

section
open Classical
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_sysdec_vcpu (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (p : U64) (block call cd fp : Bool)
    (buf : U64) (ex : Array obj.Slot 3#usize) :
    syscall.decode_invocation st arI s a lbl len slot (.Vcpu p) block call cd fp buf ex =
      vcpu.decode st arI s a lbl len p call buf ex := by
  obtain ⟨ct, hct, -⟩ := P1.spec_ex_fd (P1.sched.cur_thread.spec (st := st) s)
  unfold syscall.decode_invocation
  rw [hct, bind_ok]

/-- **The VCPU-cap arm of the invocation step at `JAtZV3`** (module docstring). -/
theorem JAtZV3.vcpuInvJ (N : VcpuNyp (L := L) arI AR) (hK : ARKeep arI AR) (hSy : ZvSyncKeep arI AR)
    (hVA : ZvVirtAgree arI) (hCap : ∀ a', VirtSanEq.CapAgree arI a') (hAT : P0.ArchTotal arI)
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V) {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (lbl len : U64) (slot : obj.Slot) (block call cd fp : Bool)
    {buf : U64} (hb : BufOut V buf) (ex : Array obj.Slot 3#usize) {sl : obj.Slot} {b : Bool}
    (hsl : Array.index_usize ex 0#usize = ok sl) (hbn : obj.Slot.is_null sl = ok b) {c : capability.Cap}
    (hc : b = false → obj.Slot.cap st sl s = ok c) (hct : ∀ t, c = .Thread t → Z.th t = some .tcb)
    (hIo : lbl = fl4_abi.label.X86VCPUEnableIOPort → IoFresh b c) :
    syscall.decode_invocation st arI s a lbl len slot (.Vcpu p) block call cd fp buf ex ⦃ r =>
      VInvPost (L := L) arI V X AR Z H Cs Ac Lst D s σ lbl len p call buf b c r ⦄ := by
  rw [zv_sysdec_vcpu]
  refine WP.spec_mono (J.vcpuDecodeJ N hK hSy hVA hCap hAT hp hk lbl len call hb ex hsl hbn hc hct hIo) ?_
  rintro r ⟨ct, hct', HH⟩
  refine ⟨ct, hct', fun args ec hA hC fp cref slot' buffer onCore remoteCur bl ca cd => ?_⟩
  rcases HH args ec hA hC with ⟨e, e', h1, h2, h3, h4, h5⟩ | ⟨inv, rep, s', σ', Ac', Lst', h1, h2, h3, h4, h5⟩
  · refine Or.inl ⟨e, e', h1, h2, ?_, h4, h5⟩
    rw [zv_decV_vcpu]
    exact run_liftME_err (h3.trans rfl)
  · refine Or.inr ⟨inv, rep, s', σ', Ac', Lst', h1, ?_, ?_, h4, h5⟩
    · rw [zv_decV_vcpu]
      exact run_liftME_ok (h2.trans rfl)
    · rw [zv_perfV_vcpu]
      exact run_liftE' h3

end

end

end Fl4Proofs.P3
