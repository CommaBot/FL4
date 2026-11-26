/-
P3 (line mmuAD, gen 29): **the extracted `vcpu.detach` and the binding core of `X86VCPUSetTCB` at `JAtZV2`,
paired with the extended spec's `vcpuDetach` / `associateVcpuTcb`** (gen 28's "Next" items 1 and 2).

The extended spec `Fl4Spec.Ext.VirtVcpu` is imported here (gen 29 decision: the virt line imports it in its P3
proof modules too); no spec file is changed.

## Spec side (outcome lemmas)

* `zv_getVcpu_eq`, `zv_vcpuUpdate_eq`: on a VCPU object, `getVcpu` / `vcpuUpdate` have exactly one outcome (the
  `setObject_eq` pattern of P3/NtfnSpec).
* `zv_tcbVcpuOf_eq` / `zv_tcbVcpuOf_none`: `tcbVcpuOf σ t` (a `Classical.choose`) is the unique VCPU object whose
  `tcb` is `t`, or `none` when there is none.
* `zv_vcpuDetach_none`, `zv_vcpuDetach_bound`: `vcpuDetach t` on an unbound thread is the identity; on a bound
  thread not in `runningVM` it is the one `vcpuUpdate v (tcb := none)`.

## FL4 side

* `zv_vcpu_stall_id`: on a single-core `SchedRel` state (every thread of `T` has the current core's affinity,
  P3/ScConfig's `remote_tcb_stall_id`), `vcpu.stall v` writes nothing when `v`'s `TCB` word is 0 or a thread of
  `T`; its arch state keeps `AR` (`ARKeep.vcpu_barrier`). So **no node-word frame is needed** for `vcpu.stall` at a
  `JAtZB` state: its `IPI_PENDING` write happens only for a thread of another core, which `SchedRel` excludes.
* `JAtZB.archV` / `JAtZV.archV` / `JAtZV2.archV`: the joint invariant at another arch state related to the same CR3
  (`JAtZB.arFrS` + `XTopAt.arch`, as P3/XTopJointTcbMisc's `JAtZ.archJ`).
* `JAtZB.specTcb`: a typed-heap TCB is a spec TCB whose state word is `tsCode` of its spec state.
* `JAtZV2.specBound`: under `VOnly` a spec VCPU bound to `t` is the `V` VCPU named by `t`'s VCPU word.
* **`JAtZV2.detachN`**: `vcpu.detach t` (vcpu.rs l. 723-736) at `JAtZV2 V X`, for a typed-heap TCB `t` whose spec
  state is not `runningVM` (`hst`, scope: the `report` branch is not taken): the spec's `vcpuDetach t` has exactly
  one outcome `σ'` and `JAtZV2` holds at the post-state with `σ'`; also `DetSpec σ σ'` (each spec object kept, or
  a VCPU with `tcb := none`) and `DetMem` (t's VCPU word 0, its old VCPU's `TCB` word 0, every other `JW` word
  kept). The whole extracted body: `bound`, `stall` (no write), the state test, the two link writes
  (`JAtZV2.unbind`) and `SVM_CPU := 0` (`JAtZV2.vcpuWr`).
* **`JAtZV2.detach`**: the same without `hst`: the `report` branch (`t` in `TS_RUNNING_VM`; spec `vmReport t 0`
  inside `vcpuDetach`) by the named premise `ReportJ` [J]; the post is `JAtZV2` with some `Ac'`, `Lst'`.
* **`JAtZV2.setTcbCore`**: the binding core of `vcpu.decode` at `X86VCPUSetTCB` (Funs.lean, the `Cap.Thread ptr`
  branch from `remote_tcb_stall` to the `t.VCPU := v` write, verbatim; vcpu.rs l. 853-860) at `JAtZV2 V X`,
  for `v ∈ V` and a typed-heap TCB `t`, both threads involved (`t`, and `v`'s old thread) not in `runningVM`
  (`hst`, `hso`: scope as above): `associateVcpuTcb v t` has exactly one outcome `σ'` and `JAtZV2` holds after.

## Named premises

* **`VOnly V σ` [J]**: every spec VCPU object is at the address of some `v ∈ V`. P2 instantiates `V` with the
  layout's VCPUs (all of them); `JAtZV` carries `JVm` (every `v ∈ V` is a spec VCPU) but not this converse.
  It is needed because `vcpuDetach` reads `tcbVcpuOf`, a choice over *all* spec VCPU objects: without it a spec
  VCPU outside `V` bound to `t` could be the one chosen. Kept by every step proved here (`VOnly.ofDet`).

* **`ReportJ … s a σ t` [J]** (`JAtZV2.detach` only): FL4's `vcpu.report t 0` refines the spec's `vmReport t 0` at a
  `JAtZV2` state — one spec outcome, `JAtZV2` after, the state word no longer 8, no `JW` word written. Not
  derivable from `JAtZV2`: the reported message registers (guest RIP, controls, event / the saved exit) come from
  the VCPU's guest state, and `JAtZV2` relates only the binding (`VBind`), not `VcpuState.fields` / `exit` to the
  VMCS shadow / VMCB words (gen 26: "the `fields` half not defined"). The FL4-side footprint of `vcpu.report` is
  P3/JExtVSteps' `vcpu_report_w` (register words, IPC-buffer user words, `PENDING`, state, `SCHED_ACTION`).

Not covered (scope, not premises): `detachN` / `setTcbCore` exclude the `report` branch by `hst` / `hso`; the decode
front end before the `Thread` cap match and the caller's `TS_RESTART` after the bind.

No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBBind
import Fl4Proofs.P3.JAtZBSched2
import Fl4Proofs.P3.ScConfig
import Fl4Proofs.P3.ArchKeep
import Fl4Proofs.P3.XTopTcbFpu
import Fl4Spec.Ext.VirtVcpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section
open Fl4Spec

theorem zv_vcpuAt_kheap {σ : State Unit} {w : ObjRef} {x : VcpuState} (h : vcpuAt σ w = some x) :
    σ.kheap w = some (.archObj (.vcpu x)) := by
  unfold vcpuAt at h
  split at h
  · rename_i y hy; cases h; exact hy
  · cases h

theorem zv_getVcpu_eq {σ : State Unit} {v : ObjRef} {vs : VcpuState} (hk : σ.kheap v = some (.archObj (.vcpu vs))) :
    getVcpu (Z := Unit) v σ = ({(vs, σ)}, False) := by
  unfold getVcpu
  rw [Notif.nd_bind_one (Notif.getObject_eq hk)]
  rfl

theorem zv_vcpuUpdate_eq {σ : State Unit} {v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (f : VcpuState → VcpuState) :
    vcpuUpdate (Z := Unit) v f σ = ({((), Notif.updK σ v (.archObj (.vcpu (f vs))))}, False) := by
  unfold vcpuUpdate setVcpu
  rw [Notif.nd_bind_one (zv_getVcpu_eq hk)]
  exact Notif.setObject_eq hk rfl

theorem zv_tcbVcpuOf_eq {σ : State Unit} {t v : ObjRef} {vs : VcpuState}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (ht : vs.tcb = some t)
    (hu : ∀ w ws, σ.kheap w = some (.archObj (.vcpu ws)) → ws.tcb = some t → w = v) :
    tcbVcpuOf σ t = some v := by
  have hex : ∃ v st, vcpuAt σ v = some st ∧ VcpuState.tcb st = some t := ⟨v, vs, by simp [vcpuAt, hk], ht⟩
  unfold tcbVcpuOf
  rw [dif_pos hex]
  obtain ⟨x, h1, h2⟩ := Classical.choose_spec hex
  rw [hu _ x (zv_vcpuAt_kheap h1) h2]

theorem zv_tcbVcpuOf_none {σ : State Unit} {t : ObjRef}
    (hn : ∀ w ws, σ.kheap w = some (.archObj (.vcpu ws)) → ws.tcb ≠ some t) :
    tcbVcpuOf σ t = none := by
  unfold tcbVcpuOf
  rw [dif_neg]
  rintro ⟨w, ws, h1, h2⟩
  exact hn w ws (zv_vcpuAt_kheap h1) h2

theorem zv_vcpuDetach_none {σ : State Unit} {t : ObjRef} (h : tcbVcpuOf σ t = none) :
    vcpuDetach (Z := Unit) t σ = ({((), σ)}, False) := by
  unfold vcpuDetach getTcbVcpu
  rw [Notif.nd_gets_bind, h]
  rfl

theorem zv_vcpuDetach_bound {σ : State Unit} {t v : ObjRef} {vs : VcpuState} {xt : Fl4Spec.Tcb}
    (hk : σ.kheap v = some (.archObj (.vcpu vs))) (h : tcbVcpuOf σ t = some v)
    (hkt : σ.kheap t = some (.tcb xt)) (hst : xt.tcbState ≠ .runningVM) :
    vcpuDetach (Z := Unit) t σ = ({((), Notif.updK σ v (.archObj (.vcpu { vs with tcb := none })))}, False) := by
  unfold vcpuDetach getTcbVcpu
  rw [Notif.nd_gets_bind, h]
  dsimp only
  rw [Notif.nd_bind_one (Notif.getThreadState_eq hkt)]
  unfold NonDet.when
  rw [if_neg hst]
  exact (Notif.nd_bind_one (show (NonDet.pure () : NonDet (State Unit) Unit) σ = ({((), σ)}, False) from rfl) _).trans
    (zv_vcpuUpdate_eq hk _)

end

/-- **Every spec VCPU object is one of `V`'s** [J] (module docstring). -/
def VOnly (V : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ p vs, σ.kheap p = some (.archObj (.vcpu vs)) → ∃ v ∈ V, p = v.bv

/-- The spec heap after a detach: each object kept, or a VCPU object with `tcb := none`. -/
def DetSpec (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ vs : Fl4Spec.VcpuState, σ.kheap p = some (.archObj (.vcpu vs)) ∧
    σ'.kheap p = some (.archObj (.vcpu { vs with tcb := none }))

theorem VOnly.ofDet {V : Set U64} {σ σ' : Fl4Spec.State Unit} (h : VOnly V σ) (D : DetSpec σ σ') : VOnly V σ' :=
  fun p vs hp => by
    rcases D p with e | ⟨vs', h1, -⟩
    · rw [e] at hp; exact h p vs hp
    · exact h p vs' h1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- The link words after a detach of `t` (FL4 side). -/
structure DetMem (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap) (t : U64)
    (s s' : S) : Prop where
  w0 : L.mem s' (tVcpuA t) = 0#u64
  b0 : ∀ w ∈ V, L.mem s (tVcpuA t) = w → L.mem s' (vTcbA w) = 0#u64
  keep : ∀ b, JW V th b → b ≠ tVcpuA t → (∀ w ∈ V, L.mem s (tVcpuA t) = w → b ≠ vTcbA w) → L.mem s' b = L.mem s b

/-- **`vcpu.stall` writes nothing on a single-core state** (module docstring). -/
theorem zv_vcpu_stall_id (hK : ARKeep arI AR) {N T C : Set U64} {cc : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C cc s σ) (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c) {v : U64}
    (hvt : L.mem s (vTcbA v) = 0#u64 ∨ L.mem s (vTcbA v) ∈ T) :
    vcpu.stall st arI s a v ⦃ r => r.1 = s ∧ AR r.2 c ⦄ := by
  unfold vcpu.stall
  refine WP.spec_bind (hK.vcpu_barrier a c hAR) fun a1 h1 => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun i ei => ?_
  have ei' : i = L.mem s (vTcbA v) := ei
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec i) fun b eb => ?_
  split
  · exact (WP.spec_ok _).2 ⟨rfl, h1⟩
  · rename_i hb
    have hi0 : i ≠ 0#u64 := by rw [eb] at hb; simpa using hb
    have hiT : i ∈ T := by rw [ei'] at hi0 ⊢; exact hvt.resolve_left hi0
    exact WP.spec_mono (Sched.remote_tcb_stall_id (ar := arI) a1 hS hiT) fun r e => by subst e; exact ⟨rfl, h1⟩

/-- `JAtZB` at another arch state related to the same CR3. -/
theorem JAtZB.archV (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a' σ :=
  J.arFrS (arFr_fpuOwner σ σ.machineState σ.archState.x64CurrentFpuOwner) (J.xtop.arch hAR)

theorem JAtZV.archV (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a' σ :=
  ⟨J.base.archV hAR, J.extv, J.rvm, J.vm, J.vl⟩

theorem JAtZV2.archV (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {a' : A}
    (hAR : AR a' σ.archState.x64CurrentCr3) : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a' σ :=
  ⟨J.zv.archV hAR, J.vb⟩

/-- The arch relation of a `JAtZB` state. -/
theorem JAtZB.ar (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) : AR a σ.archState.x64CurrentCr3 :=
  J.xtop.fin.1.1.2.2.2.2.2.2

/-- A typed-heap TCB is a spec TCB whose state word is `tsCode` of its spec state. -/
theorem JAtZB.specTcb (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb) :
    ∃ x, σ.kheap t.bv = some (.tcb x) ∧ (L.mem s (P1.stA t)).val = Notif.tsCode x.tcbState := by
  obtain ⟨x, hk, -⟩ := J.xtop.rel.2.1.1.tcb t ht
  refine ⟨x, hk, ?_⟩
  rw [Sched.stA_tStA]
  exact (J.xtop.fin.1.1.2.2.1.at_tcb (J.thT t ht) hk).st

/-- A spec TCB not in `runningVM` has a state word other than 8. -/
theorem JAtZB.st8 (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : Z.th t = some .tcb)
    (hst : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbState ≠ .runningVM) : L.mem s (P1.stA t) ≠ 8#u64 := by
  obtain ⟨x, hk, hw⟩ := J.specTcb ht
  intro e
  rw [e] at hw
  refine hst x hk ?_
  cases hx : x.tcbState <;> rw [hx] at hw <;> simp_all [Notif.tsCode]

/-- **A spec VCPU bound to `t` is the `V` VCPU named by `t`'s VCPU word** (under `VOnly`). -/
theorem JAtZV2.specBound (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hO : VOnly V σ) {t : U64}
    (ht : Z.th t = some .tcb) {w : Fl4Spec.ObjRef} {ws : Fl4Spec.VcpuState}
    (hw : σ.kheap w = some (.archObj (.vcpu ws))) (hwt : ws.tcb = some t.bv) :
    ∃ u ∈ V, w = u.bv ∧ L.mem s (tVcpuA t) = u ∧ L.mem s (vTcbA u) = t := by
  obtain ⟨u, hu, rfl⟩ := hO w ws hw
  obtain ⟨vs, hk, hb⟩ := J.vb u hu
  rw [hw] at hk
  cases hk
  rcases hb with ⟨h0, -⟩ | ⟨t', ht0, ht', hm⟩
  · rw [hwt] at h0; cases h0
  · rw [hwt] at ht'
    have e : t = t' := (UScalar.eq_equiv_bv_eq t t').2 (Option.some.inj ht')
    subst e
    rcases J.zv.extv.back u hu with h | ⟨-, h⟩
    · exact absurd (hm.symm.trans h) ht0
    · rw [hm] at h
      exact ⟨u, hu, rfl, h, hm⟩

set_option maxHeartbeats 16000000 in
/-- **`vcpu.detach` at `JAtZV2`, paired with the spec's `vcpuDetach`** (module docstring). -/
theorem JAtZV2.detachN (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hO : VOnly V σ) {t : U64} (ht : Z.th t = some .tcb)
    (hst : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbState ≠ .runningVM) :
    vcpu.detach st arI s a t ⦃ r => ∃ σ', Fl4Spec.vcpuDetach (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      DetSpec σ σ' ∧ JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D r.1 r.2 σ' ∧ DetMem st V Z.th t s r.1 ⦄ := by
  have Jz := J.zv
  have B := Jz.base
  have P := B.jwPl Jz.vm
  have Ly := B.jvLay Jz.vm
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have aT : P1.Aligned (tVcpuA t) := P.jw _ JWt
  have hS := B.xtop.fin.1.1.1
  have h8 : L.mem s (P1.stA t) ≠ 8#u64 := B.st8 ht hst
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  split
  · rename_i hv0
    have h0 : L.mem s (tVcpuA t) = 0#u64 := by rw [← ev']; exact hv0
    refine (WP.spec_ok _).2 ⟨σ, zv_vcpuDetach_none (zv_tcbVcpuOf_none fun w ws hw hwt => ?_),
      fun p => Or.inl rfl, J, ⟨h0, fun w hw e => absurd (e.symm.trans h0) (Jz.extv.nz w hw),
        fun b _ _ _ => rfl⟩⟩
    obtain ⟨u, hu, -, h1, -⟩ := J.specBound hO ht hw hwt
    exact Jz.extv.nz u hu (h1.symm.trans h0)
  rename_i hv0
  have hvne : L.mem s (tVcpuA t) ≠ 0#u64 := by rw [← ev']; exact hv0
  obtain ⟨hvV, hvt⟩ := (Jz.extv.bnd t ht).resolve_left hvne
  rw [← ev'] at hvV hvt
  have hf := Ly.vfit v hvV
  have JWb : JW V Z.th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  have aB : P1.Aligned (vTcbA v) := P.jw _ JWb
  have esv := lay_svm_val hf.2
  have evt := lay_vTcb_val hf.2
  have aS : P1.Aligned (svmA v) := by unfold P1.Aligned; rw [esv]; omega
  have g1 : v.val ≤ (svmA v).val := by rw [esv]; omega
  have g2 : (svmA v).val < v.val + 32768 := by rw [esv]; omega
  have g3 : (svmA v).val ≠ v.val + 20480 ∧ (svmA v).val ≠ v.val + 20488 ∧ (svmA v).val ≠ v.val + 20496 := by
    rw [esv]; omega
  have nJ : ¬ JW V Z.th (svmA v) := (Ly.nJS_v hvV g1 g2 g3.1).1
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar (Or.inr (by rw [hvt]; exact B.thT t ht))) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  refine WP.spec_bind (P1.obj.Tcb.state.spec s t) fun i ei => ?_
  have hne : ¬ (i = sched.TS_RUNNING_VM) := by rw [ei]; simpa [sched.TS_RUNNING_VM] using h8
  simp only [hne, ↓reduceIte, bind_ok, vcpu.set, lift]
  refine WP.spec_bind (P1.LawfulStore.write_spec s _ _) fun s3 e3 => ?_
  subst e3
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  subst e5
  refine (WP.spec_ok _).2 ?_
  -- the spec side
  obtain ⟨vs, hk, hb⟩ := J.vb v hvV
  have hvs : Fl4Spec.VcpuState.tcb vs = some t.bv := by
    rcases hb with ⟨-, h0⟩ | ⟨t', -, h1, h2⟩
    · have e : t = 0#u64 := hvt.symm.trans h0
      subst e
      exact absurd ht (B.detPl Jz.vm).h0
    · have e : t' = t := h2.symm.trans hvt
      rw [h1, e]
  have hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv := zv_tcbVcpuOf_eq hk hvs fun w ws hw hwt => by
    obtain ⟨u, hu, rfl, h1, -⟩ := J.specBound hO ht hw hwt
    rw [← h1, ← ev']
  obtain ⟨xt, hkt, -⟩ := B.specTcb ht
  have hD := zv_vcpuDetach_bound hk hTV hkt (hst xt hkt)
  -- FL4 side
  have J1 := J.archV hAR1
  have J2 := J1.unbind ht hvV ev'.symm hvt h8 hk { vs with tcb := none } rfl
  have J3 := J2.vcpuWr hvV aS g1 g2 g3 0#u64
  have nT : (svmA v).val ≠ (tVcpuA t).val := fun e => nJ (by rw [UScalar.eq_of_val_eq e]; exact JWt)
  have nB : (svmA v).val ≠ (vTcbA v).val := by rw [esv, evt]; omega
  have nTB : (tVcpuA t).val ≠ (vTcbA v).val := fun e => P.vb t ht v hvV (UScalar.eq_of_val_eq e)
  refine ⟨_, hD, fun p => ?_, J3, ⟨?_, ?_, ?_⟩⟩
  · by_cases e : p = v.bv
    · subst e; exact Or.inr ⟨vs, hk, by simp [Notif.updK]⟩
    · exact Or.inl (by simp [Notif.updK, Function.update_of_ne e])
  · show L.mem (L.wr (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (tVcpuA t) = 0#u64
    rw [L.mem_wr_ne aS aT nT, L.mem_wr_same aT]
  · intro w hw e
    rw [← e, ← ev']
    show L.mem (L.wr (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (vTcbA v) = 0#u64
    rw [L.mem_wr_ne aS aB nB, L.mem_wr_ne aT aB nTB, L.mem_wr_same aB]
  · intro b hb h1 h2
    have hW := ((P1.writesIn_wr (st := st) (s := s) (v := 0#u64) aB).trans
      (P1.writesIn_wr (v := 0#u64) aT)).trans (P1.writesIn_wr (v := 0#u64) aS)
    refine hW.mem_eq (P.jw b hb) ?_
    rintro ((e | e) | e)
    · exact h2 v hvV ev'.symm e
    · exact h1 e
    · exact nJ (e ▸ hb)

set_option maxHeartbeats 16000000 in
/-- **The binding core of `X86VCPUSetTCB` at `JAtZV2`, paired with `associateVcpuTcb`** (module docstring). -/
theorem JAtZV2.setTcbCore (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hO : VOnly V σ) {t v : U64} (ht : Z.th t = some .tcb) (hv : v ∈ V)
    (hst : ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbState ≠ .runningVM)
    (hso : ∀ vs o x, σ.kheap v.bv = some (.archObj (.vcpu vs)) → Fl4Spec.VcpuState.tcb vs = some o →
      σ.kheap o = some (.tcb x) → x.tcbState ≠ .runningVM) :
    (do
      let (s3, a2) ← smp.remote_tcb_stall st arI s a t
      let (s4, a3) ← vcpu.detach st arI s3 a2 t
      let i1 ← vcpu.get st s4 v vcpu.TCB
      let b1 ← obj.Tcb.is_null i1
      let (s5, a4) ← if b1 then ok (s4, a3) else vcpu.detach st arI s4 a3 i1
      let s6 ← vcpu.set st s5 v vcpu.TCB t
      let i2 ← layout.tcb.VCPU
      let i3 ← lift (core.num.U64.wrapping_add t i2)
      let s7 ← st.write s6 i3 v
      ok (s7, a4)) ⦃ r => ∃ σ', Fl4Spec.associateVcpuTcb (Z := Unit) v.bv t.bv σ = ({((), σ')}, False) ∧
        JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D r.1 r.2 σ' ⦄ := by
  have Jz := J.zv
  have B := Jz.base
  have P := B.jwPl Jz.vm
  have hS := B.xtop.fin.1.1.1
  have hv0 : v ≠ 0#u64 := Jz.extv.nz v hv
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  refine WP.spec_bind (Sched.remote_tcb_stall_id (ar := arI) a hS (B.thT t ht)) ?_
  rintro ⟨s3, a2⟩ e
  try simp only [uncurry_apply_pair]
  simp only [Prod.mk.injEq] at e
  obtain ⟨e1, e2⟩ := e
  subst s3
  subst a2
  refine WP.spec_bind (J.detachN hK hO ht hst) ?_
  rintro ⟨s4, a3⟩ ⟨σ1, hD1, DS1, J1, DM1⟩
  try simp only [uncurry_apply_pair]
  have hO1 : VOnly V σ1 := hO.ofDet DS1
  obtain ⟨vs1, hk1, hb1⟩ := J1.vb v hv
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s4 _) fun i1 ei1 => ?_
  have ei1' : i1 = L.mem s4 (vTcbA v) := ei1
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec i1) fun b1 eb1 => ?_
  refine WP.spec_bind (Pₘ := fun r => ∃ σ2, Fl4Spec.associateVcpuTcb (Z := Unit) v.bv t.bv σ =
      Fl4Spec.vcpuUpdate (Z := Unit) v.bv (fun x : Fl4Spec.VcpuState => { x with tcb := some t.bv }) σ2 ∧
      JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D r.1 r.2 σ2 ∧ L.mem r.1 (tVcpuA t) = 0#u64 ∧
      L.mem r.1 (vTcbA v) = 0#u64) ?_ ?_
  · split
    · rename_i hb
      have hi0 : i1 = 0#u64 := by rw [eb1] at hb; simpa using hb
      have hm0 : L.mem s4 (vTcbA v) = 0#u64 := ei1'.symm.trans hi0
      have htc : Fl4Spec.VcpuState.tcb vs1 = none := by
        rcases hb1 with ⟨h, -⟩ | ⟨o, ho0, -, hm⟩
        · exact h
        · exact absurd (hm.symm.trans hm0) ho0
      refine (WP.spec_ok _).2 ⟨σ1, ?_, J1, DM1.w0, hm0⟩
      unfold Fl4Spec.associateVcpuTcb
      rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
      try exact Notif.nd_pure_bind' _ _ _
    · rename_i hb
      have hi0 : i1 ≠ 0#u64 := by rw [eb1] at hb; simpa using hb
      obtain ⟨o, ho0, htc, hm⟩ : ∃ o : U64, o ≠ 0#u64 ∧ Fl4Spec.VcpuState.tcb vs1 = some o.bv ∧
          L.mem s4 (vTcbA v) = o := by
        rcases hb1 with ⟨-, h⟩ | h
        · exact absurd (ei1'.trans h) hi0
        · exact h
      have eio : o = i1 := (ei1'.trans hm).symm
      rw [eio] at ho0 htc hm
      obtain ⟨hto, hov⟩ := (J1.zv.extv.back v hv).resolve_left (by rw [hm]; exact ho0)
      rw [hm] at hto hov
      have hne : t ≠ i1 := fun e => hv0 (by rw [← hov, ← e]; exact DM1.w0)
      -- the old thread is not in `runningVM`
      have hst1 : ∀ x, σ1.kheap i1.bv = some (.tcb x) → x.tcbState ≠ .runningVM := by
        intro x hx
        rcases DS1 v.bv with ev | ⟨vs', h1, h2⟩
        · rw [ev] at hk1
          rcases DS1 i1.bv with eo | ⟨vs'', h3, h4⟩
          · rw [eo] at hx
            exact hso vs1 i1.bv x hk1 htc hx
          · rw [h4] at hx; cases hx
        · rw [h2] at hk1
          cases hk1
          simp at htc
      refine WP.spec_mono (J1.detachN hK hO1 hto hst1) ?_
      rintro ⟨s5, a4⟩ ⟨σ2, hD2, -, J2, DM2⟩
      refine ⟨σ2, ?_, J2, ?_, ?_⟩
      · unfold Fl4Spec.associateVcpuTcb
        rw [Notif.nd_bind_one hD1, Notif.nd_bind_one (zv_getVcpu_eq hk1), htc]
        exact Notif.nd_bind_one hD2 _
      · rw [DM2.keep _ JWt (fun e => hne (tVcpuA_inj e)) (fun w hw _ => P.vb t ht w hw)]
        exact DM1.w0
      · exact DM2.b0 v hv hov
  rintro ⟨s5, a4⟩ ⟨σ2, hA2, J2, hw0, hb0⟩
  try simp only [uncurry_apply_pair]
  obtain ⟨vs2, hk2, -⟩ := J2.vb v hv
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s5 _ _) fun s6 e6 => ?_
  subst e6
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
  subst e7
  refine (WP.spec_ok _).2 ⟨_, by rw [hA2]; exact zv_vcpuUpdate_eq hk2 _,
    J2.bind ht hv hw0 hb0 hk2 { vs2 with tcb := some t.bv } rfl⟩


/-- **The `report` branch of `vcpu::detach` refines `vmReport`** [J] (module docstring): at a `JAtZV2` state, FL4's
`vcpu.report t 0` and the spec's `vmReport t 0` have related outcomes — the spec has exactly one, `JAtZV2` holds
after (some `Ac'`, `Lst'`), the thread's state word is no longer 8, and no `JW` word is written. Not derivable from
`JAtZV2`: the reported message registers come from the VCPU's guest state, and `JAtZV2` relates only the VCPU
binding (`VBind`), not the VCPU's fields (`VcpuState.fields` / `exit` ↔ the VMCS / VMCB words). -/
def ReportJ (st : machine.Store S) [L : P1.LawfulStore st] (arI : machine.Arch A) (V X : Set U64)
    (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (t : U64) : Prop :=
  vcpu.report st arI s a t 0#u64 ⦃ s' => ∃ (σr : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
    Fl4Spec.vmReport (Z := Unit) t.bv 0 σ = ({((), σr)}, False) ∧
    JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D s' a σr ∧ L.mem s' (P1.stA t) ≠ 8#u64 ∧
    ∀ b, JW V Z.th b → L.mem s' b = L.mem s b ⦄

set_option maxHeartbeats 16000000 in
/-- **`vcpu.detach` at `JAtZV2`, both branches** (module docstring): `JAtZV2.detachN` without the scope `hst`,
the `report` branch by `ReportJ` [J]. -/
theorem JAtZV2.detach (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hK : ARKeep arI AR)
    (hO : VOnly V σ) {t : U64} (ht : Z.th t = some .tcb)
    (hR : ∀ a', AR a' σ.archState.x64CurrentCr3 → ReportJ st arI V X AR Z H Cs Ac Lst D s a' σ t) :
    vcpu.detach st arI s a t ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
      Fl4Spec.vcpuDetach (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have Jz := J.zv
  have B := Jz.base
  have P := B.jwPl Jz.vm
  have Ly := B.jvLay Jz.vm
  have JWt : JW V Z.th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have hS := B.xtop.fin.1.1.1
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  split
  · rename_i hv0
    have h0 : L.mem s (tVcpuA t) = 0#u64 := by rw [← ev']; exact hv0
    refine (WP.spec_ok _).2 ⟨σ, Ac, Lst, zv_vcpuDetach_none (zv_tcbVcpuOf_none fun w ws hw hwt => ?_), J⟩
    obtain ⟨u, hu, -, h1, -⟩ := J.specBound hO ht hw hwt
    exact Jz.extv.nz u hu (h1.symm.trans h0)
  rename_i hv0
  have hvne : L.mem s (tVcpuA t) ≠ 0#u64 := by rw [← ev']; exact hv0
  obtain ⟨hvV, hvt⟩ := (Jz.extv.bnd t ht).resolve_left hvne
  rw [← ev'] at hvV hvt
  have hf := Ly.vfit v hvV
  have JWb : JW V Z.th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  have esv := lay_svm_val hf.2
  have aS : P1.Aligned (svmA v) := by unfold P1.Aligned; rw [esv]; omega
  have g1 : v.val ≤ (svmA v).val := by rw [esv]; omega
  have g2 : (svmA v).val < v.val + 32768 := by rw [esv]; omega
  have g3 : (svmA v).val ≠ v.val + 20480 ∧ (svmA v).val ≠ v.val + 20488 ∧ (svmA v).val ≠ v.val + 20496 := by
    rw [esv]; omega
  refine WP.spec_bind (zv_vcpu_stall_id (arI := arI) hK hS a B.ar (Or.inr (by rw [hvt]; exact B.thT t ht))) ?_
  rintro ⟨s1, a1⟩ ⟨e1, hAR1⟩
  try simp only [uncurry_apply_pair]
  try simp only at e1 hAR1
  subst s1
  obtain ⟨vs, hk, hb⟩ := J.vb v hvV
  have hvs : Fl4Spec.VcpuState.tcb vs = some t.bv := by
    rcases hb with ⟨-, h0⟩ | ⟨t', -, h1, h2⟩
    · have e : t = 0#u64 := hvt.symm.trans h0
      subst e
      exact absurd ht (B.detPl Jz.vm).h0
    · have e : t' = t := h2.symm.trans hvt
      rw [h1, e]
  have hTV : Fl4Spec.tcbVcpuOf σ t.bv = some v.bv := zv_tcbVcpuOf_eq hk hvs fun w ws hw hwt => by
    obtain ⟨u, hu, rfl, h1, -⟩ := J.specBound hO ht hw hwt
    rw [← h1, ← ev']
  obtain ⟨xt, hkt, hwst⟩ := B.specTcb ht
  have J1 := J.archV hAR1
  refine WP.spec_bind (P1.obj.Tcb.state.spec s t) fun i ei => ?_
  refine WP.spec_bind (Pₘ := fun s2 => ∃ (σ2 : Fl4Spec.State Unit) (Ac' : Set U64) (Lst' : U64 → List U64),
      Fl4Spec.vcpuDetach (Z := Unit) t.bv σ =
        Fl4Spec.vcpuUpdate (Z := Unit) v.bv (fun x : Fl4Spec.VcpuState => { x with tcb := none }) σ2 ∧
      JAtZV2 (L := L) arI V X AR Z H Cs Ac' Lst' D s2 a1 σ2 ∧ L.mem s2 (P1.stA t) ≠ 8#u64 ∧
      L.mem s2 (tVcpuA t) = v ∧ L.mem s2 (vTcbA v) = t) ?_ ?_
  · split
    · rename_i hi
      have e8 : L.mem s (P1.stA t) = 8#u64 := by rw [← ei, hi]; unfold sched.TS_RUNNING_VM; rfl
      have hrv : xt.tcbState = .runningVM := by
        rw [e8] at hwst
        cases hx : xt.tcbState <;> rw [hx] at hwst <;> simp_all [Notif.tsCode]
      refine WP.spec_mono (hR a1 hAR1) ?_
      rintro s2 ⟨σr, Ac', Lst', hRep, J2, h82, hJW⟩
      refine ⟨σr, Ac', Lst', ?_, J2, h82, by rw [hJW _ JWt]; exact ev'.symm, by rw [hJW _ JWb]; exact hvt⟩
      unfold Fl4Spec.vcpuDetach Fl4Spec.getTcbVcpu
      rw [Notif.nd_gets_bind, hTV]
      dsimp only
      rw [Notif.nd_bind_one (Notif.getThreadState_eq hkt)]
      unfold Fl4Spec.NonDet.when
      rw [if_pos hrv]
      exact Notif.nd_bind_one hRep _
    · rename_i hi
      have h8 : L.mem s (P1.stA t) ≠ 8#u64 := by rw [← ei]; simpa [sched.TS_RUNNING_VM] using hi
      have hns : xt.tcbState ≠ .runningVM := fun hx => h8 (by
        apply UScalar.eq_of_val_eq
        rw [hwst, hx]; simp [Notif.tsCode])
      refine (WP.spec_ok _).2 ⟨σ, Ac, Lst, ?_, J1, h8, ev'.symm, hvt⟩
      unfold Fl4Spec.vcpuDetach Fl4Spec.getTcbVcpu
      rw [Notif.nd_gets_bind, hTV]
      dsimp only
      rw [Notif.nd_bind_one (Notif.getThreadState_eq hkt)]
      unfold Fl4Spec.NonDet.when
      rw [if_neg hns]
      exact Notif.nd_bind_one (show (Fl4Spec.NonDet.pure () : Fl4Spec.NonDet (Fl4Spec.State Unit) Unit) σ =
        ({((), σ)}, False) from rfl) _
  rintro s2 ⟨σ2, Ac', Lst', hD2, J2, h82, htv2, hvt2⟩
  obtain ⟨vs2, hk2, -⟩ := J2.vb v hvV
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  subst e5
  refine (WP.spec_ok _).2 ⟨_, Ac', Lst', by rw [hD2]; exact zv_vcpuUpdate_eq hk2 _,
    (J2.unbind ht hvV htv2 hvt2 h82 hk2 { vs2 with tcb := none } rfl).vcpuWr hvV aS g1 g2 g3 0#u64⟩

end

end

end Fl4Proofs.P3
