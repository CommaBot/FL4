/-
P3 (line mmuAD, gen 42b2): **the finalisation of a final mapped EPT root cap at `VmEptState`** (goal 3 of 42b2, its
finalise half): FL4's `objects::finalise_cap … (Ept p 0 true asid va) true` (objects.rs l. 266 → `ept::finalise`,
ept.rs l. 229-230 → `vspace::delete_asid`, x86_64/vspace.rs l. 336-354: the tagged pool entry `old & !1 == root`,
`old & 1 != 0` is cleared after `ept::invalidate`, no address-space switch) against the spec's `finaliseCap` of
`.eptCap p 0 (some (asid, va))` (Ext `archFinaliseCap`, X64/VSpace l. 446-448: `when (level = 0) (deleteAsid asid p)`).

* Base half: XTopJointFinVs's **`JAtZB.finVsJb`** (gen 42b3: `JAtZ.finVsJb` generalised in place to `JAtZB`, the
  footprint (`VsW` writes, the TCB VCPU words kept) exposed in its post; `JAtZ.finVsJb` is its corollary) at this
  one cap (VsFin's `fin_ept_root` = VsDel's `delete_asid_relR`, whose nested branch is the tagged entry). No copy.
* Spec half: **`PoolShr σ σ'`** (the ASID table kept; every object kept but ASID pools, whose entries only
  disappear); `ekhF` (heap, ASID table) kept by `setVmRoot` / `hwAsidInvalidate` (`Vs.FK`, VsDom's `dk_step0`);
  `ept_getAsidPool_mem`; **`ept_deleteAsid_shr`** (every outcome of `deleteAsid`); **`ept_finRoot_shr`** (every
  outcome of the cap's `finaliseCap`).
* Placement: `JAtZB.vsFrSpec` (a VSpace frame is a 4 KiB spec pool / page-table object), **`JAtZB.vsW_apart`** (a
  `VsW` word misses an object that every other spec object and the kernel-global area miss: the VCPUs of `V` by
  `JVm.sep` / `ks`, the tables of `X` by `EptCore.sep` / `ks`), `JAtZB.vsW_head` (`VsW` misses the VCPU list head:
  `TopPlaced.disj`, the head word is an `OObj` kernel-global word). `JAtZB.ept_ne0` is P3/XTopJointFinVtJ's (gen 42b3:
  generalised in place, the copy here deleted).
* **`VmEptState.finEptRoot`**: from `VmEptState`, FL4's `finalise_cap` of a slot's mapped level-0 `Ept` cap
  ⦃ the spec's `finaliseCap` has an outcome `σ'` with `VmEptState` at FL4's state and `σ'` ⦄: `VcpuCore` by
  `VcpuCore.ofW`, `EptCore` by `EptCore.frame` (the slot caps kept, `UnmappedEmpty` by `UnmappedEmpty.keep`; the tag
  shrinks: `GuestEntry σ' ⊆ GuestEntry σ` from `PoolShr`).

Not here: the deletion around it (`cdt::delete`'s finalise loop and slot clearing at `VmEptState`, including
SetEPTRoot's delete of the old `SLOT_EPT` cap, tcb.rs l. 416) and detype (`EptCore.shrink`).

Premises: `ArchRefines arI AR` [P] (as `JAtZ.finVsJb`). No new named premise. New file only.
-/
import Fl4Proofs.P3.EptStep3
import Fl4Proofs.P3.JAtZBRecap
import Fl4Proofs.P3.JAtZBWr
import Fl4Proofs.P3.XTopJointFinVs
import Fl4Proofs.P3.SpecCnK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## The spec's side -/

section
open Fl4Spec Fl4Proofs.P3.Vs

/-- **ASID pools only lose entries** (module docstring). -/
def PoolShr (σ σ' : State Unit) : Prop :=
  σ'.archState.x64AsidTable = σ.archState.x64AsidTable ∧
  ∀ q, σ'.kheap q = σ.kheap q ∨ ∃ f f', σ.kheap q = some (.archObj (.asidPool f)) ∧
    σ'.kheap q = some (.archObj (.asidPool f')) ∧ ∀ lo e, f' lo = some e → f lo = some e

theorem PoolShr.refl (σ : State Unit) : PoolShr σ σ := ⟨rfl, fun _ => Or.inl rfl⟩

/-- The heap and the ASID table. -/
def ekhF (σ : State Unit) := (σ.kheap, σ.archState.x64AsidTable)

theorem PoolShr.of_kh {σ σ' : State Unit} (h : ekhF σ' = ekhF σ) : PoolShr σ σ' := by
  simp only [ekhF, Prod.mk.injEq] at h
  exact ⟨h.2, fun q => Or.inl (by rw [h.1])⟩

theorem ekh_doMachineOp {α : Type} (mop : NonDet MachineState α) : FK ekhF (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine dk_bind (dk_gets _) (fun _ => dk_bind (dk_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact dk_bind (dk_modify (fun σ => rfl)) (fun _ => dk_pure _)

theorem ekh_hwAsidInvalidate (a : Asid) (v : ObjRef) : FK ekhF (hwAsidInvalidate (Z := Unit) a v) := by
  unfold hwAsidInvalidate; exact ekh_doMachineOp _

theorem ekh_setVmRoot (t : ObjRef) : FK ekhF (setVmRoot (Z := Unit) t) := by
  unfold setVmRoot getCap findVspaceForAsid getAsidPool getCurrentCr3 setCurrentVspaceRoot setCurrentCr3
  repeat' (first | exact ekh_doMachineOp _ | dk_step0)

/-- A `getAsidPool` outcome: the pool read, the state kept. -/
theorem ept_getAsidPool_mem {p : ObjRef} {σ : State Unit} {y : (AsidLowIndex → Option ObjRef) × State Unit}
    (h : y ∈ (getAsidPool (Z := Unit) p σ).1) : σ.kheap p = some (.archObj (.asidPool y.1)) ∧ y.2 = σ := by
  unfold getAsidPool at h
  obtain ⟨z, hz, h⟩ := h
  obtain ⟨k, hk, rfl⟩ : ∃ k, σ.kheap p = some k ∧ z = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hz
    cases e : σ.kheap p with
    | none => rw [e] at hz; exact False.elim hz
    | some k => rw [e] at hz; exact ⟨k, rfl, Set.mem_singleton_iff.1 hz⟩
  cases k with
  | archObj ao =>
    cases ao with
    | asidPool f =>
      have e := Set.mem_singleton_iff.1 h
      subst e
      exact ⟨hk, rfl⟩
    | _ => exact False.elim h
  | _ => exact False.elim h

/-- **Every outcome of `deleteAsid` only removes pool entries** (module docstring). -/
theorem ept_deleteAsid_shr (a r : ObjRef) (σ : State Unit) (x : Unit × State Unit)
    (hx : x ∈ (deleteAsid (Z := Unit) a r σ).1) : PoolShr σ x.2 := by
  unfold deleteAsid at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  dsimp only at hx
  rcases ht : σ.archState.x64AsidTable (asidHighBitsOf a) with _ | pp
  · simp only [ht] at hx
    rw [Set.mem_singleton_iff.1 hx]; exact PoolShr.refl _
  · simp only [ht] at hx
    obtain ⟨z, hz, hx⟩ := hx
    obtain ⟨hk, hz2⟩ := ept_getAsidPool_mem hz
    rw [show z = (z.1, σ) from Prod.ext rfl hz2] at hx
    generalize z.1 = f at hk hx
    dsimp only at hx
    rcases he : f (asidLowBitsOf a) with _ | e
    · simp only [he] at hx
      rw [Set.mem_singleton_iff.1 hx]; exact PoolShr.refl _
    · simp only [he] at hx
      unfold NonDet.when at hx
      by_cases hc : asidEntryRoot e = r
      · rw [if_pos hc] at hx
        by_cases ht1 : e &&& 1 = 0
        · rw [if_pos ht1] at hx
          obtain ⟨⟨u1, σ2⟩, h1, hx⟩ := hx
          have e1 : ekhF σ2 = ekhF σ := ekh_hwAsidInvalidate _ _ σ (u1, σ2) h1
          obtain ⟨y2, h2, hx⟩ := hx
          rw [Set.mem_singleton_iff.1 h2] at hx
          dsimp only at hx
          obtain ⟨⟨u3, σ4⟩, h3, hx⟩ := hx
          unfold setAsidPool at h3
          have e3 := Fl4Proofs.P3.Ipc.setObject_out h3
          simp only at e3
          have e4 : ekhF x.2 = ekhF σ4 := by
            refine (?_ : FK ekhF _) σ4 x hx
            repeat' (first | exact ekh_setVmRoot _ | dk_step0)
          simp only [ekhF, Prod.mk.injEq] at e1 e4
          refine ⟨by rw [e4.2, e3, e1.2], fun q => ?_⟩
          rw [e4.1, e3]
          by_cases hq : q = pp
          · subst hq
            refine Or.inr ⟨f, Function.update f (asidLowBitsOf a) none, hk, by simp, fun lo e' h => ?_⟩
            by_cases hl : lo = asidLowBitsOf a
            · subst hl; simp at h
            · rwa [Function.update_of_ne hl] at h
          · left; simp only [Function.update_of_ne hq]; rw [e1.1]
        · rw [if_neg ht1] at hx
          obtain ⟨y2, h2, hx⟩ := hx
          rw [Set.mem_singleton_iff.1 h2] at hx
          dsimp only at hx
          obtain ⟨⟨u3, σ4⟩, h3, hx⟩ := hx
          unfold setAsidPool at h3
          have e3 := Fl4Proofs.P3.Ipc.setObject_out h3
          simp only at e3
          have e4 : ekhF x.2 = ekhF σ4 := by
            refine (?_ : FK ekhF _) σ4 x hx
            repeat' (first | exact ekh_setVmRoot _ | dk_step0)
          simp only [ekhF, Prod.mk.injEq] at e4
          refine ⟨by rw [e4.2, e3], fun q => ?_⟩
          rw [e4.1, e3]
          by_cases hq : q = pp
          · subst hq
            refine Or.inr ⟨f, Function.update f (asidLowBitsOf a) none, hk, by simp, fun lo e' h => ?_⟩
            by_cases hl : lo = asidLowBitsOf a
            · subst hl; simp at h
            · rwa [Function.update_of_ne hl] at h
          · left; simp only [Function.update_of_ne hq]
      · rw [if_neg hc] at hx
        rw [Set.mem_singleton_iff.1 hx]; exact PoolShr.refl _

/-- **Every outcome of a mapped EPT root cap's `finaliseCap` only removes pool entries.** -/
theorem ept_finRoot_shr {p asid va : U64} {σ : State Unit} {x : (Cap × Cap) × State Unit}
    (hx : x ∈ (finaliseCap (Z := Unit) (absCap (.Ept p 0#u64 true asid va)) true σ).1) : PoolShr σ x.2 := by
  obtain ⟨y, hy, hx⟩ := hx
  change y ∈ (NonDet.when ((0#u64 : U64).val = 0) (deleteAsid (Z := Unit) asid.bv p.bv) σ).1 at hy
  unfold NonDet.when at hy
  rw [Set.mem_singleton_iff.1 hx]
  split at hy
  · exact ept_deleteAsid_shr _ _ σ y hy
  · rename_i h0; exact absurd rfl h0

variable {σ σ' : State Unit}

theorem PoolShr.arch (h : PoolShr σ σ') {o : ObjRef} {ao : ArchKernelObj} (hk : σ.kheap o = some (.archObj ao))
    (hp : ∀ f, ao ≠ .asidPool f) : σ'.kheap o = σ.kheap o := by
  rcases h.2 o with e | ⟨f, f', k1, -, -⟩
  · exact e
  · rw [hk] at k1; cases k1; exact absurd rfl (hp f)

theorem PoolShr.back (h : PoolShr σ σ') {o : ObjRef} {ko' : KernelObject} (hk : σ'.kheap o = some ko')
    (hp : ∀ f', ko' ≠ .archObj (.asidPool f')) : σ.kheap o = some ko' := by
  rcases h.2 o with e | ⟨f, f', -, k2, -⟩
  · rw [← e]; exact hk
  · rw [hk] at k2; cases k2; exact absurd rfl (hp f')

theorem PoolShr.size (h : PoolShr σ σ') :
    ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ objBits ko' = objBits ko := by
  intro o ko' hk
  rcases h.2 o with e | ⟨f, f', k1, k2, -⟩
  · exact ⟨ko', by rw [← e]; exact hk, rfl⟩
  · rw [hk] at k2; cases k2; exact ⟨_, k1, rfl⟩

theorem PoolShr.entry (h : PoolShr σ σ') : ∀ e, GuestEntry σ' e → GuestEntry σ e := by
  rintro e ⟨hi, q, f', lo, h1, h2, h3⟩
  rw [h.1] at h1
  rcases h.2 q with e' | ⟨f, g', k1, k2, hf⟩
  · exact ⟨hi, q, f', lo, h1, by rw [← e']; exact h2, h3⟩
  · rw [h2] at k2; cases k2; exact ⟨hi, q, f, lo, h1, k1, hf lo e h3⟩

/-- (gen 42b10) A pool entry after is the old entry at the same ASID. -/
theorem PoolShr.poolAt (h : PoolShr σ σ') : ∀ hi lo e, PoolAt σ' hi lo e → e &&& 1 = 1 → PoolAt σ hi lo e := by
  rintro hi lo e ⟨q, f', h1, h2, h3⟩ -
  rw [h.1] at h1
  rcases h.2 q with e' | ⟨f, g', k1, k2, hf⟩
  · exact ⟨q, f', h1, by rw [← e']; exact h2, h3⟩
  · rw [h2] at k2; cases k2; exact ⟨q, f, h1, k1, hf lo e h3⟩

end

/-! ## The `VsW` words against the VCPUs, the tables and the list head -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

section
open Classical Fl4Proofs.P3.Vs

/-- A VSpace frame is a 4 KiB spec ASID pool or page table. -/
theorem JAtZB.vsFrSpec (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {q : U64} (hq : VsFr Z q) :
    ∃ ao, σ.kheap q.bv = some (.archObj ao) ∧ Fl4Spec.objBits (.archObj ao) = 12 ∧
      (∀ l es, ao ≠ .ept l es) ∧ (∀ x, ao ≠ .vcpu x) := by
  have hF := J.xtop.fin
  rcases hq with hq | hq | hq | hq | hq
  · obtain ⟨f, hf, -⟩ := hF.2.1.pool q hq
    exact ⟨_, hf, rfl, fun l es h => (by cases h), fun x h => (by cases h)⟩
  · obtain ⟨f, hf, -⟩ := hF.2.2.1.l4 q hq
    exact ⟨_, hf, rfl, fun l es h => (by cases h), fun x h => (by cases h)⟩
  · obtain ⟨f, hf, -⟩ := hF.2.2.1.l3 q hq
    exact ⟨_, hf, rfl, fun l es h => (by cases h), fun x h => (by cases h)⟩
  · obtain ⟨f, hf, -⟩ := hF.2.2.1.l2 q hq
    exact ⟨_, hf, rfl, fun l es h => (by cases h), fun x h => (by cases h)⟩
  · obtain ⟨f, hf, -⟩ := hF.2.2.1.l1 q hq
    exact ⟨_, hf, rfl, fun l es h => (by cases h), fun x h => (by cases h)⟩

/-- **A `VsW` word misses an object `[t, t + n)` that every other spec object and the kernel-global area miss**, if no
VSpace frame is at `t`. -/
theorem JAtZB.vsW_apart (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} {n : Nat}
    (hsep : ∀ o ko, σ.kheap o = some ko → o ≠ t.bv → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ t.val ∨ t.val + n ≤ o.toNat)
    (hks : t.val + n ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ t.val)
    (hnf : ∀ q, VsFr Z q → q.bv ≠ t.bv) {b : U64} (hb : VsW Z (L.ksb s) b) :
    b.val + 8 ≤ t.val ∨ t.val + n ≤ b.val := by
  have hP := J.xtop.fin.1.2
  rcases vsW_val hP.pt hP.vs hb with ⟨q, hq, -, -, h1, h2, -⟩ | ⟨h1, h2, -⟩
  · obtain ⟨ao, hk, hb12, -, -⟩ := J.vsFrSpec hq
    have e := hsep _ _ hk (hnf q hq)
    rw [hb12] at e
    have hq' : q.bv.toNat = q.val := rfl
    rw [hq'] at e
    have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    rw [h12] at e
    omega
  · omega

/-- A `VsW` word is not the VCPU list head (`TopPlaced.disj`: the head is an `OObj` kernel-global word). -/
theorem JAtZB.vsW_head (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64} (hb : VsW Z (L.ksb s) b) :
    b ≠ P1.vHeadA st s := by
  intro e
  have hP := J.xtop.fin.1.2
  have hv : VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b := by
    rcases hb with ⟨q, hq, i, hi, rfl⟩ | h
    · exact table_vobj hP.pt hq hi _
    · exact vsWrite_vobj hP.vs h
  have hh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b := by
    refine Or.inr (Or.inl ⟨?_, ?_, Or.inl ?_⟩) <;> rw [e, hh] <;> omega
  exact hP.disj b hO hv

end

/-! ## The step at `VmEptState` -/

variable {V X : Set U64} {XL : U64 → Nat}
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **A final mapped EPT root cap's finalisation at `VmEptState`** (module docstring). From `ArchRefines` [P]. -/
theorem VmEptState.finEptRoot [Fl4Proofs.P1.PlainStore st] (hA : ArchRefines arI AR)
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ)
    {sl : Fl4Spec.CslotPtr} {p asid va : U64} (hDS : DState (L := L) Z.th s σ Z.G) (hAs : AbsSlot Z.th sl)
    (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Ept p 0#u64 true asid va)) :
    objects.finalise_cap st arI s a (.Ept p 0#u64 true asid va) true false ⦃ r =>
      r.1.1 = finRem (.Ept p 0#u64 true asid va) true ∧ CleanCap r.1.2 ∧ CapWf r.1.2 ∧ ∃ σ',
        ((absCap r.1.1, absCap r.1.2), σ') ∈
          (Fl4Spec.finaliseCap (Z := Unit) (absCap (.Ept p 0#u64 true asid va)) true σ).1 ∧
        VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D r.2.1 r.2.2 σ' ∧
        SlotsSame Z.th (L.mem s) (L.mem r.2.1) ∧ L.ksb r.2.1 = L.ksb s ⦄ := by
  obtain ⟨⟨B, Cv⟩, C⟩ := J
  have hp0 := B.ept_ne0 hAs.isSlot (capV_of_capAt hc)
  have Ap : VsApart (L := L) Z H Cs s := ⟨fun q z hq hqC => absurd (B.hscC q z hq) hqC⟩
  refine WP.spec_mono (B.finVsJb hA Ap hDS hAs hc (fun _ _ h => by cases h) ⟨rfl, rfl, hp0⟩ ⟨_, rfl⟩ true
    (Or.inl ⟨Or.inl rfl, rfl, fun f l e => by cases e⟩)) ?_
  rintro ⟨⟨rem, cl⟩, s1, a1⟩ ⟨h1, h2, h3, σ1, hm, ⟨E, B1, hE⟩, -, hSS, hkb, hW, hVK⟩
  simp only at h1 h2 h3 hm B1 hSS hkb hW hVK ⊢
  have hE' : E = Z.vx := hE.resolve_right (by rintro ⟨_, _, h⟩; cases h)
  subst hE'
  replace B1 : JAtZB (L := L) arI AR Z H Cs Ac Lst D s1 a1 σ1 := B1
  have hP : PoolShr σ σ1 := ept_finRoot_shr hm
  -- the `VsW` words miss the VCPUs of `V` and the tables of `X`
  have nV : ∀ u ∈ V, ∀ b, VsW Z (L.ksb s) b → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    obtain ⟨x, hx⟩ := Cv.vm.spec u hu
    have := B.vsW_apart (t := u) (n := 32768) (fun o ko hk hne => Cv.vm.sep u hu o ko hk hne) (Cv.vm.ks u hu)
      (fun q hq e => by
        obtain ⟨ao, hk, -, -, hnv⟩ := B.vsFrSpec hq
        rw [e, hx] at hk; cases hk; exact hnv x rfl) hb
    omega
  have nX : ∀ b, VsW Z (L.ksb s) b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val := by
    intro b hb t ht
    obtain ⟨es, hx, -⟩ := C.rel.obj t ht
    have := B.vsW_apart (t := t) (n := 4096) (fun o ko hk hne => C.sep t ht o ko hk hne) (C.ks t ht)
      (fun q hq e => by
        obtain ⟨ao, hk, -, hne, -⟩ := B.vsFrSpec hq
        rw [e, hx] at hk; cases hk; exact hne _ es rfl) hb
    omega
  have hvk : ∀ u ∈ V, σ1.kheap u.bv = σ.kheap u.bv := fun u hu => by
    obtain ⟨x, hx⟩ := Cv.vm.spec u hu
    exact hP.arch hx (by intro f h; cases h)
  have hrv : ∀ o x', σ1.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM := fun o x' ho hx =>
    ⟨x', ⟨hP.back ho (by intro f h; cases h), hx⟩⟩
  have hnv : ∀ q (vs : Fl4Spec.VcpuState), σ1.kheap q = some (.archObj (.vcpu vs)) →
      σ.kheap q = some (.archObj (.vcpu vs)) := fun q vs hq => hP.back hq (by intro f h; cases h)
  refine ⟨h1, h2, h3, σ1, hm, ⟨⟨B1, Cv.ofW B B1 hW hSS nV (fun b hb => B.vsW_head hb) hVK hvk hP.size hrv hnv⟩,
    C.frame hW nX (fun y hy p l a v mm hc => ⟨hy, by rw [← hSS.capV hy]; exact hc⟩)
      (C.exte.of_eq fun y hy => hSS.capV hy) (fun t ht => ?_) (fun r l es hk => ⟨l, es, hP.back hk (by intro f h; cases h)⟩)
      hP.entry hP.size (EptSlotStep.ofSS hSS)
      (C.named.frameA hP.1 hP.poolAt (fun r l es hk => hP.back hk (by intro f h; cases h))
        (fun y p lv a v hy hc _ => ⟨y, hy, by rw [hSS.capV hy]; exact hc⟩)
        (fun y p lv mm a v hy hc => ⟨y, hy, by rw [← hSS.capV hy]; exact hc⟩))⟩, hSS, hkb⟩
  obtain ⟨es, hx, -⟩ := C.rel.obj t ht
  exact hP.arch hx (by intro f h; cases h)

end

end

end Fl4Proofs.P3
