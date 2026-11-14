/-
P3 (DESIGN.md §9), VSpace: **ASIDPool `Assign`**. FL4's `vspace::decode`
on an ASID-pool cap with label `X86ASIDPoolAssign` decodes and performs in
one go; l4v has `decode_x64_asid_pool_invocation` (in
`arch_decode_invocation`), then `set_thread_state cur Restart`, then
`perform_asid_pool_invocation`.

This file: the spec's decode (`decodeAssign_*`: its errors, and its
outcomes for each free offset — l4v picks any free offset, FL4 the first),
the spec's perform (`performAssign_eq`), and FL4's search for a free entry
(`decode_loop1_spec`).
-/
import Fl4Proofs.P3.VsDelPool
import Fl4Proofs.P3.SetCap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec

/-- l4v's free offsets of a pool with base `base`. -/
def freeSet (f : AsidLowIndex → Option ObjRef) (base : Asid) : Set AsidLowIndex :=
  (dom f)ᶜ ∩ {x | ucast asidRepLen x + base ≠ 0}

theorem runE_throw {ε α : Type} (e : ε) (σ : State Unit) :
    ExceptT.run (NonDetE.throwError (σ := State Unit) (α := α) e) σ = ({(.error e, σ)}, False) := rfl

theorem runE_ret {ε α : Type} (a : α) (σ : State Unit) :
    ExceptT.run (NonDetE.returnOk (σ := State Unit) (ε := ε) a) σ = ({(.ok a, σ)}, False) := rfl

theorem runE_whenE_false {ε : Type} {P : Prop} [Decidable P] (h : ¬ P) (m : NonDetE (State Unit) ε Unit)
    (σ : State Unit) : ExceptT.run (NonDetE.whenE P m) σ = ({(.ok (), σ)}, False) := by
  unfold NonDetE.whenE; rw [if_neg h]; rfl

theorem runE_whenE_true {ε : Type} {P : Prop} [Decidable P] (h : P) (m : NonDetE (State Unit) ε Unit)
    (σ : State Unit) : ExceptT.run (NonDetE.whenE P m) σ = ExceptT.run m σ := by
  unfold NonDetE.whenE; rw [if_pos h]

theorem selectExt_mem {D : Type} (a : State DetExt → D) {S' : Set D} {x : D} (hx : x ∈ S') (σ : State Unit) :
    (x, σ) ∈ (selectExt (Z := Unit) a S' σ).1 := by
  simp [selectExt, nd_bind_apply', NonDet.get, NonDet.select, NonDet.assert, hx, StateExt.selectSwitch,
    NonDet.pure, pure]

theorem selectExt_nofail {D : Type} (a : State DetExt → D) (S' : Set D) (σ : State Unit) :
    ¬ (selectExt (Z := Unit) a S' σ).2 := by
  simp [selectExt, nd_bind_apply', NonDet.get, NonDet.select, NonDet.assert, StateExt.selectSwitch,
    NonDet.pure, pure]

/-- Running `liftE m >>= f` in the exception monad: an outcome. -/
theorem runE_liftE_mem {ε α β : Type} {m : NonDet (State Unit) α} {f : α → NonDetE (State Unit) ε β}
    {σ σ1 σ2 : State Unit} {x : α} {b : Except ε β} (h1 : (x, σ1) ∈ (m σ).1)
    (h2 : (b, σ2) ∈ (ExceptT.run (f x) σ1).1) : (b, σ2) ∈ (ExceptT.run (NonDetE.liftE m >>= f) σ).1 := by
  show (b, σ2) ∈ (NonDet.bind (NonDet.bind m (fun a => NonDet.pure (Except.ok a))) (ExceptT.bindCont f) σ).1
  exact ⟨(.ok x, σ1), ⟨(x, σ1), h1, rfl⟩, h2⟩

theorem runE_liftE_nofail {ε α β : Type} {m : NonDet (State Unit) α} {f : α → NonDetE (State Unit) ε β}
    {σ : State Unit} (h1 : ¬ (m σ).2) (h2 : ∀ x σ1, (x, σ1) ∈ (m σ).1 → ¬ (ExceptT.run (f x) σ1).2) :
    ¬ (ExceptT.run (NonDetE.liftE m >>= f) σ).2 := by
  show ¬ (NonDet.bind (NonDet.bind m (fun a => NonDet.pure (Except.ok a))) (ExceptT.bindCont f) σ).2
  rintro (h | ⟨⟨e, t⟩, ⟨⟨x, t0⟩, hx, he⟩, h⟩)
  · rcases h with h | ⟨_, _, h⟩
    · exact h1 h
    · exact h
  · simp only [NonDet.pure, Set.mem_singleton_iff, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h2 x _ hx h

/-- The spec's Assign decode, after the label and the extra cap. -/
def assignBody (p base : ObjRef) (sl : CslotPtr) : SEMonad Unit ArchInvocation := do
  let asidTable ← NonDetE.liftE <| NonDet.gets fun s : State Unit => s.archState.x64AsidTable
  let poolPtr ← NonDetE.returnOk (asidTable (asidHighBitsOf base))
  NonDetE.whenE (poolPtr = none) <| NonDetE.throwError (.failedLookup false .invalidRoot)
  NonDetE.whenE (p ≠ the poolPtr) <| NonDetE.throwError (.invalidCapability 0)
  let pool ← NonDetE.liftE <| getAsidPool p
  let freeSet ← NonDetE.returnOk ((dom pool)ᶜ ∩ {x | ucast asidRepLen x + base ≠ 0})
  NonDetE.whenE (freeSet = ∅) <| NonDetE.throwError .deleteFirst
  let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect pool base) freeSet
  NonDetE.returnOk <| .invokeASIDPool <| .assign (ucast asidRepLen offset + base) p sl

theorem decodeAssign_eq {lbl : Data} (hl : invocationType lbl = .archInvocationLabel .x64ASIDPoolAssign)
    (args : List Data) (xs : CapRef) (cte : CslotPtr) (p base pb : ObjRef) (sl : CslotPtr)
    (rest : List (Cap × CslotPtr)) :
    archDecodeInvocation (Z := Unit) lbl args xs cte (.asidPoolCap p base)
      ((.archObjectCap (.pml4Cap pb none), sl) :: rest) = assignBody p base sl := by
  unfold archDecodeInvocation
  dsimp only
  rw [if_pos hl, if_pos (by simp)]
  rfl

theorem assign_prefix (p base : ObjRef) (sl : CslotPtr) (σ : State Unit) :
    ExceptT.run (assignBody p base sl) σ = ExceptT.run (do
      NonDetE.whenE (σ.archState.x64AsidTable (asidHighBitsOf base) = none) <|
        NonDetE.throwError (.failedLookup false .invalidRoot)
      NonDetE.whenE (p ≠ the (σ.archState.x64AsidTable (asidHighBitsOf base))) <|
        NonDetE.throwError (.invalidCapability 0)
      let pool ← NonDetE.liftE <| getAsidPool p
      let freeSet ← NonDetE.returnOk ((dom pool)ᶜ ∩ {x | ucast asidRepLen x + base ≠ 0})
      NonDetE.whenE (freeSet = ∅) <| NonDetE.throwError .deleteFirst
      let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect pool base) freeSet
      NonDetE.returnOk (ε := SyscallError) <| ArchInvocation.invokeASIDPool <| .assign (ucast asidRepLen offset + base) p sl) σ := by
  unfold assignBody
  rw [runE_bind_ok (runE_liftE (show NonDet.gets _ σ = ({(σ.archState.x64AsidTable, σ)}, False) from rfl)),
    runE_bind_ok (runE_ret _ σ)]

theorem assignBody_noPool {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = none) :
    ExceptT.run (assignBody p base sl) σ = ({(.error (.failedLookup false .invalidRoot), σ)}, False) := by
  rw [assign_prefix, ht]
  exact runE_bind_err (by rw [runE_whenE_true rfl]; exact runE_throw _ σ)

theorem assignBody_wrong {p q base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some q) (hq : p ≠ q) :
    ExceptT.run (assignBody p base sl) σ = ({(.error (.invalidCapability 0), σ)}, False) := by
  rw [assign_prefix, ht, runE_bind_ok (runE_whenE_false (by simp) _ σ)]
  exact runE_bind_err (by rw [runE_whenE_true (show p ≠ Fl4Spec.the (some q) from hq)]; exact runE_throw _ σ)

theorem assign_pool {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) :
    ExceptT.run (assignBody p base sl) σ = ExceptT.run (do
      NonDetE.whenE (freeSet f base = ∅) <| NonDetE.throwError .deleteFirst
      let offset ← NonDetE.liftE <| selectExt (fun _ => freeAsidPoolSelect f base) (freeSet f base)
      NonDetE.returnOk (ε := SyscallError) <| ArchInvocation.invokeASIDPool <| .assign (ucast asidRepLen offset + base) p sl) σ := by
  rw [assign_prefix, ht, runE_bind_ok (runE_whenE_false (by simp) _ σ),
    runE_bind_ok (runE_whenE_false (by simp [the]) _ σ), runE_bind_ok (runE_liftE (getAsidPool_eq hk)),
    runE_bind_ok (runE_ret _ σ)]
  rfl

theorem assignBody_full {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) (hfs : freeSet f base = ∅) :
    ExceptT.run (assignBody p base sl) σ = ({(.error .deleteFirst, σ)}, False) := by
  rw [assign_pool ht hk]
  exact runE_bind_err (by rw [runE_whenE_true hfs]; exact runE_throw _ σ)

theorem assignBody_mem {p base : ObjRef} {sl : CslotPtr} {σ : State Unit}
    (ht : σ.archState.x64AsidTable (asidHighBitsOf base) = some p) {f : AsidLowIndex → Option ObjRef}
    (hk : σ.kheap p = some (.archObj (.asidPool f))) {off : AsidLowIndex} (hoff : off ∈ freeSet f base) :
    (.ok (.invokeASIDPool (.assign (ucast asidRepLen off + base) p sl)), σ) ∈
      (ExceptT.run (assignBody p base sl) σ).1 ∧ ¬ (ExceptT.run (assignBody p base sl) σ).2 := by
  have hne : freeSet f base ≠ ∅ := fun h => by rw [h] at hoff; exact hoff
  rw [assign_pool ht hk, runE_bind_ok (runE_whenE_false hne _ σ)]
  refine ⟨runE_liftE_mem (selectExt_mem _ hoff σ) (by rw [runE_ret]; rfl),
    runE_liftE_nofail (selectExt_nofail _ _ σ) fun x σ1 _ => by rw [runE_ret]; exact id⟩

end Spec


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- FL4's search for a free pool entry: the first `i < 512` with
`base + i ≠ 0` and entry `i` empty, or 512. -/
theorem decode_loop1_spec (s : S) (base pool : U64) (hpf : pool.val + 4096 ≤ 2 ^ 64) :
    vspace.decode_loop1 st s base pool 0#u64 ⦃ i1 => i1.val ≤ 512 ∧
      (∀ j : U64, j.val < i1.val → core.num.U64.wrapping_add base j = 0#u64 ∨ L.mem s (peA pool j) ≠ 0#u64) ∧
      (i1.val < 512 → core.num.U64.wrapping_add base i1 ≠ 0#u64 ∧ L.mem s (peA pool i1) = 0#u64) ⦄ := by
  unfold vspace.decode_loop1
  apply loop.spec_decr_nat (measure := fun i => 512 - i.val)
    (inv := fun i => i.val ≤ 512 ∧
      ∀ j : U64, j.val < i.val → core.num.U64.wrapping_add base j = 0#u64 ∨ L.mem s (peA pool j) ≠ 0#u64)
  · rintro i ⟨hi5, hall⟩
    unfold vspace.decode_loop1.body
    by_cases h1 : i < 512#u64
    · have hi : i.val < 512 := by have := (gt_iff_val).1 h1; simpa using this
      simp only [h1, ↓reduceIte]
      unfold lift
      apply ok_bind_spec
      have ext : ∀ j : U64, j.val < i.val + 1 → j.val < i.val ∨ j = i := fun j hj => by
        by_cases e : j.val = i.val
        · exact Or.inr (UScalar.eq_of_val_eq e)
        · exact Or.inl (by omega)
      by_cases h0 : core.num.U64.wrapping_add base i = 0#u64
      · simp only [h0, ↓reduceIte]
        step as ⟨i2, hi2⟩
        have hi2' : i2.val = i.val + 1 := by simpa using hi2
        refine ⟨by omega, fun j hj => ?_, by omega⟩
        rcases ext j (by omega) with h | rfl
        · exact hall j h
        · exact Or.inl h0
      · simp only [h0, ↓reduceIte]
        step as ⟨i2, hi2⟩
        step as ⟨v, hv⟩
        have he : core.num.U64.wrapping_add pool i2 = peA pool i := by
          apply UScalar.eq_of_val_eq
          rw [peA_val hpf hi]
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hi2]; omega
        rw [he] at hv
        by_cases hv0 : v = 0#u64
        · simp only [hv0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨hi5, hall, fun _ => ⟨h0, hv ▸ hv0⟩⟩
        · have hne : (v != 0#u64) = true := by simp [hv0]
          simp only [hne, ↓reduceIte]
          step as ⟨i5, hi5'⟩
          have hi5v : i5.val = i.val + 1 := by simpa using hi5'
          refine ⟨by omega, fun j hj => ?_, by omega⟩
          rcases ext j (by omega) with h | rfl
          · exact hall j h
          · exact Or.inr (hv ▸ hv0)
    · simp only [h1, ↓reduceIte, WP.spec_ok]
      have hi : i.val = 512 := by
        have : ¬ i.val < 512 := fun h => h1 ((gt_iff_val).2 (by simpa using h))
        omega
      exact ⟨hi5, hall, fun h => by omega⟩
  · exact ⟨by simp, fun j hj => by simp at hj⟩

theorem ucast64_ucast9 (i : U64) (hi : i.val < 512) (base : U64) :
    Fl4Spec.ucast Fl4Spec.asidRepLen (Fl4Spec.ucast 9 i.bv : BitVec 9) + base.bv = (core.num.U64.wrapping_add base i).bv := by
  apply BitVec.eq_of_toNat_eq
  simp only [Fl4Spec.ucast, BitVec.toNat_add, BitVec.toNat_setWidth]
  show (i.val % 2 ^ 9 % 2 ^ 64 + base.val) % 2 ^ 64 = (core.num.U64.wrapping_add base i).val
  rw [core.num.U64.wrapping_add_val_eq]
  simp [U64.size_def, U64.numBits]
  rw [Nat.mod_eq_of_lt hi, Nat.add_comm]

/-- The found entry is one of l4v's free offsets. -/
theorem free_of_found {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    {pool : U64} (hp : pool ∈ P) {f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef}
    (hk : σ.kheap pool.bv = some (.archObj (.asidPool f))) (base i : U64) (hi : i.val < 512)
    (h0 : core.num.U64.wrapping_add base i ≠ 0#u64) (he : m (peA pool i) = 0#u64) :
    (Fl4Spec.ucast 9 i.bv : BitVec 9) ∈ freeSet f base.bv := by
  have hgf : ∀ lo : U64, lo.val < 512 → f (Fl4Spec.ucast 9 lo.bv) = optRef (m (peA pool lo)) := by
    obtain ⟨g, hg, hgf⟩ := hR.pool pool hp
    rw [hk] at hg; injection hg with hg; injection hg with hg; injection hg with hg; subst hg; exact hgf
  refine Set.mem_inter ?_ ?_
  · show ¬ (f (Fl4Spec.ucast 9 i.bv) ≠ none)
    rw [hgf i hi, he, optRef_zero]; simp
  · show Fl4Spec.ucast Fl4Spec.asidRepLen (Fl4Spec.ucast 9 i.bv : BitVec 9) + base.bv ≠ 0
    rw [ucast64_ucast9 i hi base]
    intro h; exact h0 (UScalar.eq_of_val_eq (congrArg BitVec.toNat h))

/-- No entry found: l4v has no free offset. -/
theorem full_of_none {P : Set U64} {m : U64 → U64} {ksb : U64} {σ : Fl4Spec.State Unit} (hR : VsRel P m ksb σ)
    {pool : U64} (hp : pool ∈ P) {f : Fl4Spec.AsidLowIndex → Option Fl4Spec.ObjRef}
    (hk : σ.kheap pool.bv = some (.archObj (.asidPool f))) (base : U64)
    (hall : ∀ j : U64, j.val < 512 → core.num.U64.wrapping_add base j = 0#u64 ∨ m (peA pool j) ≠ 0#u64) :
    freeSet f base.bv = ∅ := by
  have hgf : ∀ lo : U64, lo.val < 512 → f (Fl4Spec.ucast 9 lo.bv) = optRef (m (peA pool lo)) := by
    obtain ⟨g, hg, hgf⟩ := hR.pool pool hp
    rw [hk] at hg; injection hg with hg; injection hg with hg; injection hg with hg; subst hg; exact hgf
  ext x
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hx1, hx2⟩
  have hxl : x.toNat < 512 := by have := x.isLt; simpa [Fl4Spec.asidLowLen] using this
  set j : U64 := ⟨BitVec.ofNat 64 x.toNat⟩
  have hj : j.val = x.toNat := by
    show (BitVec.ofNat 64 x.toNat).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hxj : (Fl4Spec.ucast 9 j.bv : BitVec 9) = x := by
    apply BitVec.eq_of_toNat_eq
    simp only [Fl4Spec.ucast, BitVec.toNat_setWidth]
    show j.val % 2 ^ 9 = _
    rw [hj, Nat.mod_eq_of_lt (by omega)]
  have hjl : j.val < 512 := by rw [hj]; exact hxl
  rcases hall j hjl with h | h
  · apply hx2
    show Fl4Spec.ucast Fl4Spec.asidRepLen x + base.bv = 0
    rw [← hxj, ucast64_ucast9 j hjl base, h]; rfl
  · apply hx1
    show f x ≠ none
    rw [← hxj, hgf j hjl]
    unfold optRef; rw [if_neg h]; simp

end

end

end Fl4Proofs.P3.Vs
