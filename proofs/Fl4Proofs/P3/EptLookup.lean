/-
P3 (line mmuAD, gen 42b8): **FL4's guest-table walk against the spec's** — `ept::lookup` (crates/fl4-core/src/ept.rs
l. 72-84, extracted `ept.lookup` / `ept.lookup_loop`) against `guestLookupSlot` (Fl4Spec/Ext/VirtEptInv l. 108-121),
from a guest-tagged root, at `EptCore` (its `rel` relates every word the walk reads, its `walk` field puts every table
the walk reaches in `X` at the expected level).

* Spec side: `getEpt_eq`, **`go_gt`** (a table read at a shift above the level: the entry's present / large test, then
  the next table), `go_stop` / `go_nil` (the walk stops: the table itself).
* FL4 side: `ept_ix` (the entry address `table + ((gpa >> (shift & 63)) & 511) * 8` is `eptA table (guestIndex gpa
  shift)`), `ew_and` (an FL4 word related by `EptWord` has the spec entry's bits 0, 7 and address bits 51:12: the
  hardware bits `eptHw` are 5 and 6), **`lk_miss`**, **`lk_next`**, **`lk_stop`** (one round of `lookup_loop`).
* **`EptCore.lkStep`**: one walk step from a reachable table of `X` read at the shift `eptChild (XL t)`: both sides
  fail with `MissingCapability shift`, or both go on to the same table `u ∈ X` one level down (`EptCore.walk`).
* **`EptCore.lookup`** — the top: from `EptCore`, a guest-tagged pool entry `e` (the root `asidEntryRoot e`, a table of
  `X` at level 0 by `EptCore.tag`), `gpa < 2^47` (FL4 `LIMIT`; the root entry read is below 256, `eptRootIdx_lt`) and
  `level ∈ {39, 30, 21, 12}`: FL4's `ept.lookup` returns `Ok (eptA t (guestIndex gpa level))` and the spec's
  `guestLookupSlot` the single outcome `ok t` for one reachable table `t ∈ X` at level `lkLvl level` (the root for 39,
  a PDPT for 30, a PD for 21, a PT for 12), or both fail with the same `MissingCapability` shift; σ unchanged.

* **`EptWalk.store`**: the walk field across `storeGuestEntry tb i e` (the other objects and the tagged entries kept),
  given that a new walked entry names a zero spec table one level down (the table map's unmapped table, `ue`); a
  non-walked new entry (0, a large frame entry, a PT entry, a root entry ≥ 256) needs nothing. This is how the map /
  unmap proofs discharge `EptCore.entry`'s `hwk`.

Gen 42b10: `LkOut`'s success arm also carries the walk path (`GPath`) at every ASID whose pool entry is `e`;
`lkStep` / `lkOut_step` / `lkOut_stop` take the path to `t` (`hp`) and give the path one level down.

No named premise. New file only; root import after `P3.EptAssignV`.
-/
import Fl4Proofs.P3.EptStep3
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.NtfnSpec
import Fl4Proofs.P3.Lookup
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- The level of the table a walk for `level` stops at (`ept::lookup`): the root for 39, a PDPT for 30, a PD for 21,
a PT for 12. -/
def lkLvl : Nat → Nat
  | 39 => 0
  | 30 => 39
  | 21 => 30
  | _ => 21

/-! ## Spec side -/

theorem getEpt_eq {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {l : Nat} {es : BitVec 9 → Fl4Spec.Word}
    (hk : σ.kheap p = some (.archObj (.ept l es))) :
    Fl4Spec.getEpt (Z := Unit) p σ = ({((l, es), σ)}, False) := by
  unfold Fl4Spec.getEpt
  rw [nd_bind_single (Notif.getObject_eq hk)]
  rfl

/-- A table read at a shift above the level (`guestLookupSlot.go`'s step). -/
theorem go_gt {σ : Fl4Spec.State Unit} {gpa : Fl4Spec.Word} {level sh : Nat} (rest : List Nat)
    {t : Fl4Spec.ObjRef} {l : Nat} {es : BitVec 9 → Fl4Spec.Word} (hk : σ.kheap t = some (.archObj (.ept l es)))
    (hsh : sh > level) :
    (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa level t (sh :: rest)).run σ =
      if es (Fl4Spec.guestIndex gpa sh) &&& 1 = 0 ∨ es (Fl4Spec.guestIndex gpa sh) &&& 128 ≠ 0 then
        ({(.error (.missingCapability sh), σ)}, False)
      else (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa level
        (Fl4Spec.ptrFromPAddr (es (Fl4Spec.guestIndex gpa sh) &&& Fl4Spec.guestPteAddress)) rest).run σ := by
  rw [Fl4Spec.guestLookupSlot.go, if_pos hsh, run_bind_ok (run_liftE (getEpt_eq hk))]
  by_cases hc : es (Fl4Spec.guestIndex gpa sh) &&& 1 = 0 ∨ es (Fl4Spec.guestIndex gpa sh) &&& 128 ≠ 0
  · rw [if_pos hc]; dsimp only; rw [if_pos hc]; rfl
  · rw [if_neg hc]; dsimp only; rw [if_neg hc]

theorem go_stop {σ : Fl4Spec.State Unit} {gpa : Fl4Spec.Word} {level sh : Nat} (rest : List Nat)
    (t : Fl4Spec.ObjRef) (hsh : ¬ sh > level) :
    (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa level t (sh :: rest)).run σ = ({(.ok t, σ)}, False) := by
  rw [Fl4Spec.guestLookupSlot.go, if_neg hsh]; rfl

theorem go_nil {σ : Fl4Spec.State Unit} {gpa : Fl4Spec.Word} {level : Nat} (t : Fl4Spec.ObjRef) :
    (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa level t []).run σ = ({(.ok t, σ)}, False) := by
  rw [Fl4Spec.guestLookupSlot.go]; rfl

/-! ## FL4 side -/

theorem guestIndex_toNat (gpa : U64) (sh : Nat) :
    (Fl4Spec.guestIndex gpa.bv sh).toNat = (gpa.val >>> sh) % 512 := by
  unfold Fl4Spec.guestIndex
  rw [BitVec.toNat_ofNat, BitVec.toNat_ushiftRight]
  show (gpa.val >>> sh) % 512 % 2 ^ 9 = _
  omega

/-- The entry address of `gpa` at `sh` in `t` (module docstring). -/
theorem ept_ix {β : Type} (t gpa sh : U64) (hsh : sh.val < 64) (k : U64 → Result β) :
    (do
      let i ← lift (sh &&& 63#u64)
      let i1 ← gpa >>> i
      let i2 ← lift (i1 &&& 511#u64)
      let i3 ← i2 * 8#u64
      let i4 ← lift (core.num.U64.wrapping_add t i3)
      k i4) = k (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) := by
  simp only [lift, bind_ok]
  have h63 : (sh &&& 63#u64).val = sh.val := by rw [and63_val]; omega
  obtain ⟨i1, he1, hv1, -⟩ := spec_exists (U64.ShiftRight_spec (x := gpa) (y := sh &&& 63#u64) (by rw [h63]; exact hsh))
  rw [he1, bind_ok]
  have h511 : (i1 &&& 511#u64).val = i1.val % 512 := by
    rw [UScalar.val_and]
    have : (511#u64 : U64).val = 2 ^ 9 - 1 := rfl
    rw [this, Nat.and_two_pow_sub_one_eq_mod]
  obtain ⟨i3, he3, hv3⟩ := spec_exists (U64.mul_spec (x := i1 &&& 511#u64) (y := 8#u64)
    (by rw [h511]; have := Nat.mod_lt i1.val (show 512 > 0 by decide); scalar_tac))
  rw [he3, bind_ok]
  congr 1
  unfold eptA
  congr 1
  apply UScalar.eq_of_val_eq
  have hi : (Fl4Spec.guestIndex gpa.bv sh.val).toNat = i1.val % 512 := by
    rw [guestIndex_toNat, hv1, h63]
  have hv3' : i3.val = (i1 &&& 511#u64).val * 8 := by have := hv3; scalar_tac
  rw [hv3', h511]
  show _ = (BitVec.ofNat 64 (8 * (Fl4Spec.guestIndex gpa.bv sh.val).toNat)).toNat
  rw [BitVec.toNat_ofNat, hi]
  have := Nat.mod_lt i1.val (show 512 > 0 by decide)
  omega

theorem eptHw_cases : eptHw Fl4Spec.virtKind = 0x60 ∨ eptHw Fl4Spec.virtKind = 0 := by
  unfold eptHw; split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- An `EptWord`-related FL4 word has the spec entry's bits under any mask `m` missing bits 5 and 6. -/
theorem ew_and {w e m : Fl4Spec.Word} (h : EptWord Fl4Spec.virtKind w e) (hm : m &&& 0x60 = 0) :
    w &&& m = e &&& m := by
  unfold EptWord at h
  have key : ∀ x : Fl4Spec.Word, x &&& m = (x &&& ~~~(eptHw Fl4Spec.virtKind)) &&& m := by
    intro x
    rw [BitVec.and_assoc]
    congr 1
    rcases eptHw_cases with e0 | e0 <;> rw [e0] <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
    · have := congrArg (fun y => y.getLsbD i) hm
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_zero, hi, decide_true,
        Bool.true_and] at this ⊢
      cases hmi : m.getLsbD i <;> simp_all
    · have h0 : (0 : Fl4Spec.Word).getLsbD i = false := by simp [BitVec.getLsbD]
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, h0, hi, decide_true, Bool.not_false, Bool.true_and]
  rw [key w, key e, h]

theorem mask1_ok : (1 : Fl4Spec.Word) &&& 0x60 = 0 := by decide
theorem mask128_ok : (128 : Fl4Spec.Word) &&& 0x60 = 0 := by decide
theorem maskA_ok : Fl4Spec.guestPteAddress &&& 0x60 = 0 := by decide

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A U64 mask test as a test on the word's bits. -/
theorem u_and_zero (x c : U64) : (x &&& c = 0#u64) ↔ x.bv &&& c.bv = 0 := by
  constructor
  · intro h; have := congrArg UScalar.bv h; rw [UScalar.bv_and] at this; exact this
  · intro h; apply P1.eq_of_bv; exact (UScalar.bv_and x c).trans h

/-- One round of `lookup_loop` at a missing or large entry. -/
theorem lk_miss (s : S) (t gpa level sh : U64) (hgt : sh > level) (h21 : sh.val ≥ 21) (h64 : sh.val < 64)
    (hw : L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 1#u64 = 0#u64 ∨
      ¬ (L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 128#u64 = 0#u64)) :
    ept.lookup_loop st s gpa level t sh = ok (.Err (.MissingCapability sh)) := by
  unfold ept.lookup_loop
  rw [loop]
  have h21' : sh ≥ 21#u64 := by scalar_tac
  simp only [ept.lookup_loop.body, hgt, h21', ↓reduceIte]
  rw [ept_ix t gpa sh h64]
  rw [L.read_eq, bind_ok]
  simp only [lift, bind_ok]
  by_cases h1 : L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 1#u64 = 0#u64
  · rw [if_pos h1]; simp only [bind_ok]
  · rw [if_neg h1]
    have h128 : (L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 128#u64 != 0#u64) = true := by
      rcases hw with hw | hw
      · exact absurd hw h1
      · simpa only [bne_iff_ne, ne_eq] using hw
    rw [if_pos h128]; simp only [bind_ok]

/-- One round of `lookup_loop` at a present, non-large entry: on to the table it names. -/
theorem lk_next (s : S) (t gpa level sh : U64) (hgt : sh > level) (h21 : sh.val ≥ 21) (h64 : sh.val < 64)
    (hw1 : ¬ (L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 1#u64 = 0#u64))
    (hw7 : L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 128#u64 = 0#u64) :
    ∃ sh', sh'.val = sh.val - 9 ∧ ept.lookup_loop st s gpa level t sh =
      ept.lookup_loop st s gpa level
        (core.num.U64.wrapping_add (L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& ept.ADDRESS)
          layout.PPTR_BASE) sh' := by
  obtain ⟨sh', he, hv⟩ := spec_exists (U64.sub_spec (x := sh) (y := 9#u64) (by scalar_tac))
  refine ⟨sh', by have := hv; simp at this; omega, ?_⟩
  unfold ept.lookup_loop
  conv_lhs => rw [loop]
  have h21' : sh ≥ 21#u64 := by scalar_tac
  simp only [ept.lookup_loop.body, hgt, h21', ↓reduceIte]
  rw [ept_ix t gpa sh h64]
  rw [L.read_eq, bind_ok]
  simp only [lift, bind_ok]
  have h128 : ¬ ((L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& 128#u64 != 0#u64) = true) := by
    simpa only [bne_iff_ne, ne_eq, not_not] using hw7
  rw [if_neg hw1, if_neg h128]
  simp only [layout.pptr, bind_ok, he]

/-- `lookup_loop` stops (the shift is at or below the level). -/
theorem lk_stop (s : S) (t gpa level sh : U64) (hle : ¬ sh > level) (hl : level.val < 64) :
    ept.lookup_loop st s gpa level t sh = ok (.Ok (eptA t (Fl4Spec.guestIndex gpa.bv level.val))) := by
  unfold ept.lookup_loop
  rw [loop]
  simp only [ept.lookup_loop.body, hle, ↓reduceIte]
  rw [ept_ix t gpa level hl]
  simp only [bind_ok]

/-- `lookup_loop` stops at shift 12 (below 21) for a level ≥ 12. -/
theorem lk_stop12 (s : S) (t gpa level sh : U64) (hgt : sh > level) (h12 : sh.val < 21) (hl : level.val < 64) :
    ept.lookup_loop st s gpa level t sh = ok (.Ok (eptA t (Fl4Spec.guestIndex gpa.bv level.val))) := by
  unfold ept.lookup_loop
  rw [loop]
  have h21' : ¬ sh ≥ 21#u64 := by scalar_tac
  simp only [ept.lookup_loop.body, hgt, h21', ↓reduceIte]
  rw [ept_ix t gpa level hl]
  simp only [bind_ok]

end

theorem eptChild_cases {l c : Nat} (h : eptChild l = some c) :
    (l = 0 ∧ c = 39) ∨ (l = 39 ∧ c = 30) ∨ (l = 30 ∧ c = 21) := by
  unfold eptChild at h
  split at h <;> (try cases h) <;> simp_all

theorem address_bv : ept.ADDRESS.bv = Fl4Spec.guestPteAddress := by
  unfold ept.ADDRESS; rfl

theorem pptrBase_bv : layout.PPTR_BASE.bv = Fl4Spec.pptrBase := by
  unfold layout.PPTR_BASE; rfl

/-- FL4's next table (`layout::pptr(e & ADDRESS)`) is the spec's (`ptrFromPAddr (e &&& guestPteAddress)`). -/
theorem pptr_next_bv (w : U64) :
    (core.num.U64.wrapping_add (w &&& ept.ADDRESS) layout.PPTR_BASE).bv =
      Fl4Spec.ptrFromPAddr (w.bv &&& Fl4Spec.guestPteAddress) := by
  rw [core.num.U64.wrapping_add_bv_eq, pptrBase_bv]
  have e : (w &&& ept.ADDRESS).bv = w.bv &&& Fl4Spec.guestPteAddress :=
    (UScalar.bv_and w ept.ADDRESS).trans (congrArg (w.bv &&& ·) address_bv)
  exact congrArg (· + Fl4Spec.pptrBase) e

/-- The outcome relation of the two walks (module docstring): the same table `t ∈ X` at the expected level, reachable
from the tagged root, or the same `MissingCapability` shift. -/
def LkOut (X : Set U64) (XL : U64 → Nat) (σ : Fl4Spec.State Unit) (e : Fl4Spec.ObjRef) (gpa level : U64)
    (r : Result (core.result.Result U64 error.LookupFault))
    (o : Set (Except Fl4Spec.LookupFailure Fl4Spec.ObjRef × Fl4Spec.State Unit) × Prop) : Prop :=
  (∃ t ∈ X, XL t = lkLvl level.val ∧ Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) t.bv ∧
    (∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv (lkLvl level.val) t.bv) ∧
    r = ok (.Ok (eptA t (Fl4Spec.guestIndex gpa.bv level.val))) ∧ o = ({(.ok t.bv, σ)}, False)) ∨
  (∃ sh : U64, r = ok (.Err (.MissingCapability sh)) ∧ o = ({(.error (.missingCapability sh.val), σ)}, False))

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **One walk step** from a reachable table of `X` (module docstring). -/
theorem EptCore.lkStep (C : EptCore (L := L) X XL th s σ) {e : Fl4Spec.ObjRef} (he : GuestEntry σ e)
    (h1 : e &&& 1 = 1) {t : U64} (ht : t ∈ X) (hr : Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) t.bv)
    {c : Nat} (hc : eptChild (XL t) = some c) {gpa level sh : U64} (hsh : sh.val = c) (hgt : sh > level)
    (hg : gpa.val < 2 ^ 47) (rest : List Nat)
    (hp : ∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv (XL t) t.bv) :
    (ept.lookup_loop st s gpa level t sh = ok (.Err (.MissingCapability sh)) ∧
      (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa.bv level.val t.bv (c :: rest)).run σ =
        ({(.error (.missingCapability c), σ)}, False)) ∨
    ∃ u ∈ X, XL u = c ∧ Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) u.bv ∧
      (∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv c u.bv) ∧ ∃ sh' : U64, sh'.val = c - 9 ∧ ept.lookup_loop st s gpa level t sh = ept.lookup_loop st s gpa level u sh' ∧
      (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa.bv level.val t.bv (c :: rest)).run σ =
        (Fl4Spec.guestLookupSlot.go (Z := Unit) gpa.bv level.val u.bv rest).run σ := by
  obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
  have hcs := eptChild_cases hc
  have hgt' : c > level.val := by rw [← hsh]; scalar_tac
  have h21 : sh.val ≥ 21 := by rw [hsh]; omega
  have h64 : sh.val < 64 := by rw [hsh]; omega
  have hic : Fl4Spec.guestIndex gpa.bv sh.val = Fl4Spec.guestIndex gpa.bv c := by rw [hsh]
  have hrange : XL t ≠ 0 ∨ (Fl4Spec.guestIndex gpa.bv c).toNat < 256 := by
    by_cases h0 : XL t = 0
    · right
      have h39 : c = 39 := by omega
      rw [guestIndex_toNat, h39, Nat.shiftRight_eq_div_pow]
      exact eptRootIdx_lt hg
    · exact Or.inl h0
  have hw := hwd _ hrange
  have b1 := ew_and hw mask1_ok
  have b7 := ew_and hw mask128_ok
  have bA := ew_and hw maskA_ok
  rw [go_gt rest hk hgt']
  by_cases hm : es (Fl4Spec.guestIndex gpa.bv c) &&& 1 = 0 ∨ es (Fl4Spec.guestIndex gpa.bv c) &&& 128 ≠ 0
  · left
    refine ⟨lk_miss s t gpa level sh hgt h21 h64 ?_, by rw [if_pos hm]⟩
    rw [hic, u_and_zero, u_and_zero]
    exact hm.imp (fun h => (b1.trans h : _)) (fun h e => h (b7.symm.trans e))
  · right
    rw [if_neg hm]
    have hm1 : es (Fl4Spec.guestIndex gpa.bv c) &&& 1 ≠ 0 := fun h => hm (Or.inl h)
    have hm7 : es (Fl4Spec.guestIndex gpa.bv c) &&& 128 = 0 := by
      by_contra h; exact hm (Or.inr h)
    have hgw : GWalkE (XL t) es (Fl4Spec.guestIndex gpa.bv c) := ⟨by rw [hc]; rfl, hrange, hm1, hm7⟩
    obtain ⟨es', hk'⟩ := C.walk e he h1 t.bv hr (XL t) es _ hk hgw c hc
    obtain ⟨u, hu, hub⟩ := C.rel.spec _ c es' hk'
    obtain ⟨esu, hku, -⟩ := C.rel.obj u hu
    have hXu : XL u = c := by rw [hub, hk'] at hku; cases hku; rfl
    have hnext : core.num.U64.wrapping_add (L.mem s (eptA t (Fl4Spec.guestIndex gpa.bv sh.val)) &&& ept.ADDRESS)
        layout.PPTR_BASE = u := by
      apply P1.eq_of_bv
      rw [pptr_next_bv, hub, hic, bA]
    obtain ⟨sh', hsh', hlk⟩ := lk_next s t gpa level sh hgt h21 h64
      (by rw [hic, u_and_zero]; exact fun e => hm1 (b1.symm.trans e))
      (by rw [hic, u_and_zero]; exact b7.trans hm7)
    rw [hnext] at hlk
    refine ⟨u, hu, hXu, hr.tail ⟨XL t, es, _, hk, hgw, hub⟩,
      fun hi lo hpa => by rw [hub]; exact GPath.step (hp hi lo hpa) hk hc hgw, sh', by rw [hsh', hsh], hlk, ?_⟩
    rw [hub]

/-- `LkOut` through one walk step. -/
theorem EptCore.lkOut_step (C : EptCore (L := L) X XL th s σ) {e : Fl4Spec.ObjRef} (he : GuestEntry σ e)
    (h1 : e &&& 1 = 1) {t : U64} (ht : t ∈ X) (hr : Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) t.bv)
    {c : Nat} (hc : eptChild (XL t) = some c) {gpa level sh : U64} (hsh : sh.val = c) (hgt : sh > level)
    (hg : gpa.val < 2 ^ 47) (rest : List Nat)
    (hp : ∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv (XL t) t.bv)
    (hnx : ∀ u ∈ X, XL u = c → Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) u.bv →
      (∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv (XL u) u.bv) → ∀ sh' : U64, sh'.val = c - 9 → LkOut X XL σ e gpa level (ept.lookup_loop st s gpa level u sh')
        ((Fl4Spec.guestLookupSlot.go (Z := Unit) gpa.bv level.val u.bv rest).run σ)) :
    LkOut X XL σ e gpa level (ept.lookup_loop st s gpa level t sh)
      ((Fl4Spec.guestLookupSlot.go (Z := Unit) gpa.bv level.val t.bv (c :: rest)).run σ) := by
  rcases C.lkStep he h1 ht hr hc hsh hgt hg rest hp with ⟨e1, e2⟩ | ⟨u, hu, hXu, hru, hpu, sh', hsh', e1, e2⟩
  · exact Or.inr ⟨sh, e1, by rw [e2, hsh]⟩
  · rw [e1, e2]; exact hnx u hu hXu hru (by rw [hXu]; exact hpu) sh' hsh'

/-- `LkOut` where the walk stops. -/
theorem lkOut_stop {e : Fl4Spec.ObjRef} {t : U64} (ht : t ∈ X) {gpa level sh : U64}
    (hXL : XL t = lkLvl level.val) (hr : Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) t.bv)
    (hp : ∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv (XL t) t.bv) (hle : ¬ sh > level) (hl : level.val < 64) {o : Set (Except Fl4Spec.LookupFailure Fl4Spec.ObjRef ×
      Fl4Spec.State Unit) × Prop} (ho : o = ({(.ok t.bv, σ)}, False)) :
    LkOut X XL σ e gpa level (ept.lookup_loop st s gpa level t sh) o :=
  Or.inl ⟨t, ht, hXL, hr, by rw [← hXL]; exact hp, lk_stop s t gpa level sh hle hl, ho⟩

set_option maxHeartbeats 4000000 in
/-- **FL4's `ept::lookup` against `guestLookupSlot`** from a guest-tagged root (module docstring). -/
theorem EptCore.lookup (C : EptCore (L := L) X XL th s σ) {e : Fl4Spec.ObjRef} (he : GuestEntry σ e)
    (h1 : e &&& 1 = 1) {gpa level : U64} (hg : gpa.val < 2 ^ 47)
    (hl : level.val = 39 ∨ level.val = 30 ∨ level.val = 21 ∨ level.val = 12) :
    ∃ root ∈ X, root.bv = Fl4Spec.asidEntryRoot e ∧ XL root = 0 ∧
      LkOut X XL σ e gpa level (ept.lookup st s root gpa level)
        ((Fl4Spec.guestLookupSlot (Z := Unit) (Fl4Spec.asidEntryRoot e) gpa.bv level.val).run σ) := by
  obtain ⟨root, hrX, hrb, hr0⟩ := C.tag e he h1
  refine ⟨root, hrX, hrb, hr0, ?_⟩
  have hl64 : level.val < 64 := by omega
  have hr : Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot e) root.bv := by
    rw [hrb]
  have hp0 : ∀ hi lo, PoolAt σ hi lo e → GPath σ hi lo gpa.bv (XL root) root.bv := fun hi lo hpa => by
    rw [hr0, hrb]; exact GPath.root hpa h1
  rw [← hrb]
  unfold ept.lookup Fl4Spec.guestLookupSlot
  have h39v : (39#u64 : U64).val = 39 := rfl
  have hc0 : eptChild (XL root) = some 39 := by rw [hr0]; rfl
  rcases hl with h | h | h | h
  · -- level 39: the root
    refine lkOut_stop hrX (by rw [hr0, h]; rfl) hr hp0 (by scalar_tac) hl64 ?_
    rw [go_stop _ _ (by omega)]
  · -- level 30
    refine C.lkOut_step he h1 hrX hr hc0 h39v (by scalar_tac) hg _ hp0 fun u1 hu1 hX1 hr1 hp1 sh1 hs1 => ?_
    refine lkOut_stop hu1 (by rw [hX1, h]; rfl) hr1 hp1 (by scalar_tac) hl64 ?_
    rw [go_stop _ _ (by omega)]
  · -- level 21
    refine C.lkOut_step he h1 hrX hr hc0 h39v (by scalar_tac) hg _ hp0 fun u1 hu1 hX1 hr1 hp1 sh1 hs1 => ?_
    refine C.lkOut_step he h1 hu1 hr1 (c := 30) (by rw [hX1]; rfl) (by omega) (by scalar_tac) hg _ hp1
      fun u2 hu2 hX2 hr2 hp2 sh2 hs2 => ?_
    refine lkOut_stop hu2 (by rw [hX2, h]; rfl) hr2 hp2 (by scalar_tac) hl64 ?_
    rw [go_stop _ _ (by omega)]
  · -- level 12
    refine C.lkOut_step he h1 hrX hr hc0 h39v (by scalar_tac) hg _ hp0 fun u1 hu1 hX1 hr1 hp1 sh1 hs1 => ?_
    refine C.lkOut_step he h1 hu1 hr1 (c := 30) (by rw [hX1]; rfl) (by omega) (by scalar_tac) hg _ hp1
      fun u2 hu2 hX2 hr2 hp2 sh2 hs2 => ?_
    refine C.lkOut_step he h1 hu2 hr2 (c := 21) (by rw [hX2]; rfl) (by omega) (by scalar_tac) hg _ hp2
      fun u3 hu3 hX3 hr3 hp3 sh3 hs3 => ?_
    refine lkOut_stop hu3 (by rw [hX3, h]; rfl) hr3 hp3 (by scalar_tac) hl64 ?_
    rw [go_nil]

end

/-! ## The walk field across one entry write (`storeGuestEntry`) -/

/-- **`EptWalk` across `storeGuestEntry tb i e`** (the table map, the frame map, the unmap): the other objects and the
tagged entries kept, and a new walked entry names a zero table one level down (the table map: an unmapped cap's
table, `UnmappedEmpty`); a non-walked new entry (not present, large, in a PT, or root entry ≥ 256) needs nothing. -/
theorem EptWalk.store {σ σ' : Fl4Spec.State Unit} (hW : EptWalk σ) {tb : Fl4Spec.ObjRef} {l : Nat}
    {es : BitVec 9 → Fl4Spec.Word} (hk : σ.kheap tb = some (.archObj (.ept l es))) {i : BitVec 9}
    {e : Fl4Spec.Word} (hk' : σ'.kheap tb = some (.archObj (.ept l (Function.update es i e))))
    (hoth : ∀ r, r ≠ tb → σ'.kheap r = σ.kheap r) (hge : ∀ x, GuestEntry σ' x → GuestEntry σ x)
    (hnew : GWalkE l (Function.update es i e) i → ∀ c, eptChild l = some c →
      σ.kheap (Fl4Spec.ptrFromPAddr (e &&& Fl4Spec.guestPteAddress)) = some (.archObj (.ept c fun _ => 0))) :
    EptWalk σ' := by
  -- a table of level `eptChild l` is not `tb`
  have hne_tb : ∀ c, eptChild l = some c → ∀ u es', σ.kheap u = some (.archObj (.ept c es')) → u ≠ tb := by
    intro c hc u es' hu e'
    subst e'
    rw [hk] at hu
    cases hu
    rcases eptChild_cases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  -- levels of `σ`'s guest tables persist
  have hlev : ∀ u c es', σ.kheap u = some (.archObj (.ept c es')) → ∃ es'', σ'.kheap u = some (.archObj (.ept c es'')) := by
    intro u c es' hu
    by_cases hut : u = tb
    · subst hut; rw [hk] at hu; cases hu; exact ⟨_, hk'⟩
    · exact ⟨es', by rw [hoth u hut]; exact hu⟩
  intro x hx h1 t ht
  have key : ∀ u, Relation.ReflTransGen (GStep σ') (Fl4Spec.asidEntryRoot x) u →
      Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot x) u ∨
      (u ≠ tb ∧ ∃ c, σ.kheap u = some (.archObj (.ept c fun _ => 0))) := by
    intro u hu
    induction hu with
    | refl => exact Or.inl Relation.ReflTransGen.refl
    | @tail b u' _ hst ih =>
      obtain ⟨l1, es1, j, hk1, hwe, rfl⟩ := hst
      rcases ih with hr | ⟨hbt, c, hz⟩
      · by_cases hbt : b = tb
        · subst hbt
          rw [hk'] at hk1; cases hk1
          by_cases hji : j = i
          · subst hji
            have hz := hnew hwe
            obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hwe.1
            rw [Function.update_self]
            exact Or.inr ⟨hne_tb c hc _ _ (hz c hc), c, hz c hc⟩
          · left
            refine hr.tail ⟨l, es, j, hk, ?_, by rw [Function.update_of_ne hji]⟩
            obtain ⟨a1, a2, a3, a4⟩ := hwe
            rw [Function.update_of_ne hji] at a3 a4
            exact ⟨a1, a2, a3, a4⟩
        · rw [hoth _ hbt] at hk1
          exact Or.inl (hr.tail ⟨l1, es1, j, hk1, hwe, rfl⟩)
      · rw [hoth _ hbt, hz] at hk1; cases hk1
        exact (gWalkE_zero hwe).elim
  intro l1 es1 j hk1 hwe c hc
  rcases key t ht with hr | ⟨htb, c0, hz⟩
  · by_cases htb : t = tb
    · subst htb
      rw [hk'] at hk1; cases hk1
      by_cases hji : j = i
      · subst hji
        have hz := hnew hwe c hc
        rw [Function.update_self]
        exact ⟨_, by rw [hoth _ (hne_tb c hc _ _ hz)]; exact hz⟩
      · have hwe0 : GWalkE l es j := by
          obtain ⟨a1, a2, a3, a4⟩ := hwe
          rw [Function.update_of_ne hji] at a3 a4
          exact ⟨a1, a2, a3, a4⟩
        obtain ⟨es', h'⟩ := hW x (hge x hx) h1 t hr l es j hk hwe0 c hc
        rw [Function.update_of_ne hji]
        exact hlev _ _ _ h'
    · rw [hoth _ htb] at hk1
      obtain ⟨es', h'⟩ := hW x (hge x hx) h1 t hr l1 es1 j hk1 hwe c hc
      exact hlev _ _ _ h'
  · rw [hoth _ htb, hz] at hk1; cases hk1
    exact (gWalkE_zero hwe).elim

end

end Fl4Proofs.P3
