/-
P3 (line mmuAD, gen 26): **a spec VCPU-object step at `JAtZV`, and the binding half of the VCPU relation.**

* **`JAtZB.arFrS`**: P3/XTopJointFpu's `JAtZ.arFrS` copied over `JAtZB` (generator `scratch/mmu24_jatzb_gen.py`;
  the `VKeep` argument of `cs_frameK` dropped): `JAtZB` across a spec step in the frame `ArFr` (arch objects
  replaced by objects of the same `aaType`, every other component kept) with FL4's store kept, given `XTopAt`
  after.
* **`arFr_vcpu`**: replacing a spec VCPU object by another VCPU object is an `ArFr` step.
* **`JAtZV.vcpuSpec`**: from `JAtZV V X`, the spec step `updK σ p (archObj (vcpu vs'))` for `p ∈ V` (the spec side
  of `vcpuDetach` / `associateVcpuTcb` / `setVcpu` / `vcpuUpdate`: VirtVcpu, VirtState) keeps `JAtZV V X` with
  FL4's store unchanged, given **`hX` [J]: `XTopAt` at the updated spec state**. `JVm` by `JVm.step` (same
  `objBits`); `JExtV`, `RunVmB`, `VList` read FL4 memory only. Composed with `JAtZV.vcpuWr` (FL4's VCPU-word
  writes) this pairs FL4's VCPU-object writes with the spec's VCPU-object update.
* **`VBind V σ m`** (the binding half of the spec–FL4 VCPU relation): every `v ∈ V` is a spec VCPU (`kheap v = archObj (vcpu vs)`, the extended spec's `vcpuAt`) whose `tcb`
  is `none` iff FL4's `TCB` word `vTcbA v` is 0, and otherwise is that word's TCB. **`VBind.empty`**,
  **`VBind.ofKheap`**, **`VBind.set`** (one VCPU's `tcb` and `TCB` word changed together, the others kept: the
  pair of `associateVcpuTcb` / `vcpuDetach` with FL4's bind / unbind write).

What is **not** proved: `hX` (`XTopAt` across a VCPU-object update). `XTopAt`'s parts (`FinX`/`TopSR`,
`RelTopB`, `IpcRel`, `EpSchedApart`) need a frame lemma for a kheap change at an arch object outside the VSpace
sets; no such lemma exists (the existing ones cover tables and pools in the sets, P3/XTopJointFinVs). Nor the
`fields` half of the VCPU relation (VMX/SVM field layout ↔ `VcpuState.fields`).

Named premises: `hX` [J] of `JAtZV.vcpuSpec`. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBRun
import Fl4Proofs.P3.XTopJointFpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across an `ArFr` spec step with FL4's store kept** (XTopJointFinVs's
`finVsJb` with no word written): `XTopAt` after given (at any arch state). -/
theorem JAtZB.arFrS (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {a' : A} {σ' : Fl4Spec.State Unit}
    (F : ArFr σ σ') (hX : XTopAt (L := L) AR Z s a' σ') :
    JAtZB (L := L) arI AR Z H Cs Ac Lst D s a' σ' := by
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s) := SlotsSame.refl _ _
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have k1 : ∀ t ∈ Z.T, L.mem s (mcpA t) = L.mem s (mcpA t) ∧ L.mem s (flagsA t) = L.mem s (flagsA t) := fun _ _ => ⟨rfl, rfl⟩
  have k2 : ∀ t ∈ Z.T, L.mem s (P1.yieldA t) = L.mem s (P1.yieldA t) := fun _ _ => rfl
  have kb : ∀ t ∈ Z.T, L.mem s (tIpcBufA t) = L.mem s (tIpcBufA t) := fun _ _ => rfl
  have k3 : ∀ q ∈ Z.C, L.mem s (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun _ _ => rfl
  have k4 : ∀ r ∈ Z.R, L.mem s (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s (P1.rNextA r) = L.mem s (P1.rNextA r) := fun _ _ => ⟨rfl, rfl⟩
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  have yk : YKeep σ σ' := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ rfl ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) rfl (fun _ _ => rfl) rfl⟩
  have hkern := J.kern_keepA rfl rfl hX.fin.1.1.1 F rfl
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s σ' Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have U := J.utc sl p sb fi dev hsl hcap hdv
    refine ⟨U.pal, U.pfit, U.fiLe, U.high, U.actZ, U.free, U.zero, U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0), ?_, U.dwReg, fun g => by rw [F.gpml4]; exact U.gReg g⟩
    intro g h0 hf0
    rw [F.cdt] at h0
    obtain ⟨r1, r3⟩ := U.rst g h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), r3⟩
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame rfl F.szKeep, hjpl, J.jcov, hkern, hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F,
      J.own.ar F, J.off.ar F, J.act.ar F, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, J.blk⟩
  exact J.cs_frameK (hvn := J.carry.vsNamed) rfl hX F.kback F.ipcFr (J.carry.frame subset_rfl F.ipcFr F.ksz) (JCs.sameB J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy)
    hSS (P1.DbgKeep.refl s) F.idle

end

section
open fl4_core Classical

/-- **A VCPU object replaced by a VCPU object is an `ArFr` step.** -/
theorem arFr_vcpu {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {vs : Fl4Spec.VcpuState}
    (hk : σ.kheap p = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState) :
    ArFr σ (Notif.updK σ p (.archObj (.vcpu vs'))) := by
  refine ⟨fun q => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  by_cases e : q = p
  · subst e
    exact Or.inr ⟨.vcpu vs, .vcpu vs', hk, by simp [Notif.updK], rfl⟩
  · exact Or.inl (by simp [Notif.updK, e])

/-- **A spec VCPU-object step at `JAtZV`** (module docstring); `hX` [J]: `XTopAt` at the updated spec state. -/
theorem JAtZV.vcpuSpec (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ V)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap p.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState) {a' : A}
    (hX : XTopAt (L := L) AR Z s a' (Notif.updK σ p.bv (.archObj (.vcpu vs')))) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a' (Notif.updK σ p.bv (.archObj (.vcpu vs'))) := by
  have F := arFr_vcpu hk vs'
  have B' := J.base.arFrS F hX
  have Jv' : JVm (L := L) V H s (Notif.updK σ p.bv (.archObj (.vcpu vs'))) := by
    refine J.vm.step (fun _ h => h) (fun _ _ => rfl) rfl (fun v hv => ?_) (fun o ko' ho => ?_)
    · by_cases e : v.bv = p.bv
      · exact ⟨vs', by simp [Notif.updK, e]⟩
      · obtain ⟨x, hx⟩ := J.vm.spec v hv
        exact ⟨x, by simp [Notif.updK, e, hx]⟩
    · by_cases e : o = p.bv
      · subst e
        simp only [Notif.updK, Function.update_self, Option.some.injEq] at ho
        subst ho
        exact Or.inl ⟨_, hk, rfl⟩
      · exact Or.inl ⟨ko', by simpa [Notif.updK, e] using ho, rfl⟩
  exact ⟨B', J.extv, J.rvm, Jv', J.vl⟩

/-- **The binding half of the spec–FL4 VCPU relation** (module docstring). -/
def VBind (V : Set U64) (σ : Fl4Spec.State Unit) (m : U64 → U64) : Prop :=
  ∀ v ∈ V, ∃ vs : Fl4Spec.VcpuState, σ.kheap v.bv = some (.archObj (.vcpu vs)) ∧
    ((Fl4Spec.VcpuState.tcb vs = none ∧ m (vTcbA v) = 0#u64) ∨
      ∃ t : U64, t ≠ 0#u64 ∧ Fl4Spec.VcpuState.tcb vs = some t.bv ∧ m (vTcbA v) = t)

theorem VBind.empty (σ : Fl4Spec.State Unit) (m : U64 → U64) : VBind ∅ σ m := by
  unfold VBind; intro v hv; simp at hv

/-- Same spec heap, same `TCB` words. -/
theorem VBind.ofKheap {σ σ' : Fl4Spec.State Unit} {m m' : U64 → U64} (h : VBind V σ m)
    (he : σ'.kheap = σ.kheap) (hm : ∀ v ∈ V, m' (vTcbA v) = m (vTcbA v)) : VBind V σ' m' := by
  unfold VBind at h ⊢
  intro v hv
  obtain ⟨vs, h1, h2⟩ := h v hv
  refine ⟨vs, by rw [he]; exact h1, ?_⟩
  rw [hm v hv]; exact h2

/-- **One VCPU's binding changed on both sides** (module docstring). -/
theorem VBind.set {σ : Fl4Spec.State Unit} {m m' : U64 → U64} (h : VBind V σ m) {p : U64}
    (vs' : Fl4Spec.VcpuState)
    (hm : ∀ v ∈ V, v ≠ p → m' (vTcbA v) = m (vTcbA v))
    (hp : (Fl4Spec.VcpuState.tcb vs' = none ∧ m' (vTcbA p) = 0#u64) ∨ ∃ t : U64, t ≠ 0#u64 ∧ Fl4Spec.VcpuState.tcb vs' = some t.bv ∧ m' (vTcbA p) = t) :
    VBind V (Notif.updK σ p.bv (.archObj (.vcpu vs'))) m' := by
  unfold VBind at h ⊢
  intro v hv
  by_cases e : v = p
  · subst e
    exact ⟨vs', by simp [Notif.updK], hp⟩
  · have e' : v.bv ≠ p.bv := fun h => e (P1.eq_of_bv h)
    obtain ⟨vs, h1, h2⟩ := h v hv
    refine ⟨vs, ?_, by rw [hm v hv e]; exact h2⟩
    simp only [Notif.updK, Function.update_of_ne e']
    exact h1

end

end

end

end Fl4Proofs.P3
