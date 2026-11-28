/-
P3 (line mmuAD, gen 42b1): **`EptCore` at the two record-changing EPT steps — retype of an EPT object (`X` grows) and
ASID-pool assign of an EPT root (a new guest-tagged pool entry)**, stated over the step's footprint (what FL4's
code and the spec step change), not yet the FL4 decode tops.

## Retype (`EptCore.grow`)

FL4: `X86_EPT*Object` / the root object are made by `untyped::retype` from a RAM untyped only (untyped.rs l. 66),
over memory `retype` has zeroed (untyped.rs l. 237-246; x86_64/objects.rs l. 446 "already zero"), and each new cap is
`Cap::Ept { ptr, level, mapped: false, asid: 0, vaddr: 0 }` with `level` fixed by the object type (x86_64/objects.rs
l. 46-50). Spec: `defaultArchObject` makes `.ept l (fun _ => 0)` (Ext Structs l. 472-475). So the new table `t`
joins `X` with `XL t = l`: its 512 words are 0 and its spec entries 0 (`EptWord` holds trivially), the other tables'
words are not written (the retype writes only the untyped's free part, which misses every live object), the old
`Ept` caps name tables of `X` (`exte`), so not `t`, and keep their level under `Function.update XL t l`, and the pools are
unchanged (`tag` kept: its roots are in `X`, not `t`). `ks` / `sep` for `t` come from the untyped's placement (RAM,
free region; `UtCapP3` / `SpecFree`) and are the step's hypotheses.

## ASID-pool assign (`EptCore.frameT`)

FL4 `X86ASIDPoolAssign` on an unmapped level-0 `Ept` cap (vspace.rs l. 1220-1252) writes the pool word `ptr | 1`
(l. 1250) and rewrites the cap at level 0 (l. 1246); the spec (VirtEptInv l. 247-249) writes `r ||| 1` and the cap
`.eptCap r 0 (some (asid, 0))`. No table word is written. `EptCore.frameT` is `EptCore.frame` with the pool hypothesis
weakened: every guest-tagged entry of the new state is an old entry or names a root of `X` at level 0 (for the assign:
`r` is the cap's table, in `X` by `exte`, at level 0 by `capL`). `tag` stays one-directional.

Gen 42b2 (`UnmappedEmpty`): `grow` proves `ue` for the new table (512 zero words `hz` — the object is carved from the
zero free region of a RAM untyped, `UtCapP3.zero`, and `create_object` writes nothing, objects.rs l. 446 —, the spec's `.ept l 0`, one cap `huq`, no tagged entry since `t ∉ X`)
and keeps it for the old ones (caps at the same slot unchanged); `frameT` now takes the assign's footprint (slot `x`'s
unmapped level-0 `Ept r` cap made mapped, every other slot cap kept, new tagged entries naming `r`) and proves `ue`
after it from `ue` before (`r` is not the table of another unmapped cap: uniqueness).

Gen 42b5: `EptCore.growS` — `grow` generalised in place to a set `T` of new tables with their levels `XL'` (the create
loop's objects); `grow` is its `T = {t}` instance, statement unchanged.

Gen 42b10 (`EptCore.named`): `frameT` / `growS` / `grow` take `EptNamed` after the step as their last hypothesis
(`hnm`; the assign proves it in P3/EptAssign, the create loop will from its new tables' single unmapped caps).

No named premise; the hypotheses are the step's footprint facts.
-/
import Fl4Proofs.P3.EptCore
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-- **`EptCore` across an ASID-pool assign of the root `r`** (module docstring): the slot `x`'s unmapped level-0
`Ept r` cap becomes a mapped one, every other slot `Ept` cap is kept, no table word of `X` is written, and every new
guest-tagged pool entry names `r`. -/
theorem EptCore.frameT (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    {x r a0 v0 : U64} (hx : IsSlot th x) (hcx : capV (L.mem s) x = .Ept r 0#u64 false a0 v0)
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      (y = x ∧ p = r ∧ l = 0#u64 ∧ mm = true) ∨ (y ≠ x ∧ IsSlot th y ∧ capV (L.mem s) y = .Ept p l mm a v))
    (hX' : JExtEpt (L := L) X th' s')
    (hxk : ∀ t ∈ X, σ'.kheap t.bv = σ.kheap t.bv)
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → e &&& 1 = 1 → GuestEntry σ e ∨ Fl4Spec.asidEntryRoot e = r.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) X XL th' s' σ' := by
  have hr : r ∈ X ∧ XL r = 0 := by
    have h := C.exte.cap x hx; rw [hcx] at h
    have hl := C.capL x hx r 0#u64 a0 v0 false hcx
    exact ⟨h, by simpa using hl.symm⟩
  have hm : ∀ t ∈ X, ∀ i : BitVec 9, L.mem s' (eptA t i) = L.mem s (eptA t i) := fun t ht i => by
    have hp := C.rel.place t ht
    have e := eptA_val hp.2 i
    have hi9 := i.isLt
    exact hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e]; omega)
      (fun hb => by rcases hW _ hb t ht with h | h <;> omega)
  refine ⟨⟨fun t ht => ?_, fun r' l es hk => ?_, C.rel.place⟩, ?_, hX', ?_, fun t ht => by rw [hw.1]; exact C.ks t ht,
    ?_, ?_, C.eslot.step h5, C.walkZ (Z0 := ∅) (fun t ht _ => hxk t ht) (fun _ h => h.elim)
      (fun r l es hk => Or.inr (hne r l es hk)) (fun e he h1 => (hge e he h1).imp id (fun h =>
        ⟨XL r, by rw [h, hxk r hr.1]; exact (C.ue x hx r 0#u64 a0 v0 hcx).2.1⟩)), hnm, C.tbl⟩
  · obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
    exact ⟨es, (hxk t ht).trans hk, fun i hi => by rw [hm t ht i]; exact hwd i hi⟩
  · obtain ⟨l', es', h⟩ := hne r' l es hk
    exact C.rel.spec r' l' es' h
  · intro y hy p l a v mm hc
    rcases hcap y hy p l a v mm hc with ⟨-, rfl, rfl, -⟩ | ⟨-, hy', hc'⟩
    · simp [hr.2]
    · exact C.capL y hy' p l a v mm hc'
  · intro e he h1
    rcases hge e he h1 with h | h
    · exact C.tag e h h1
    · exact ⟨r, hr.1, h.symm, hr.2⟩
  · intro t ht o ko' ho hne'
    obtain ⟨ko, hko, hb⟩ := hsz o ko' ho
    unfold EptApart; rw [hb]; exact C.sep t ht o ko hko hne'
  · intro y hy p l a v hc
    rcases hcap y hy p l a v false hc with ⟨-, -, -, h⟩ | ⟨hyx, hy0, hc0⟩
    · cases h
    have hpX : p ∈ X := by have h := C.exte.cap y hy0; rw [hc0] at h; exact h
    obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy0 p l a v hc0
    -- the assigned root is not `p` (`UnmappedEmpty`'s uniqueness at the old state: `x ≠ y` holds `Ept r`)
    have hrp : r ≠ p := fun e => by subst e; exact h3 x hx (Ne.symm hyx) 0#u64 false a0 v0 hcx
    refine ⟨fun i => by rw [hm p hpX i]; exact h1 i, by rw [hxk p hpX]; exact h2, ?_, ?_⟩
    · intro y' hy' hne l' mm a' v' hc'
      rcases hcap y' hy' p l' a' v' mm hc' with ⟨-, e, -, -⟩ | ⟨-, hy0', hc0'⟩
      · exact hrp e.symm
      · exact h3 y' hy0' hne l' mm a' v' hc0'
    · intro e he h1'
      rcases hge e he h1' with h | h
      · exact h4 e h h1'
      · rw [h]; intro e'; exact hrp (UScalar.eq_of_val_eq (by show r.bv.toNat = p.bv.toNat; rw [e']))

/-- **`EptCore` across the retype of a set `T` of guest tables** (gen 42b5: `grow` generalised in place to the
create loop's new objects; `XL'` the new levels, `XL` kept on `X`): each `t ∈ T` is zero on both sides, has one cap,
and no tagged entry names it (`t ∉ X`). -/
theorem EptCore.growS (C : EptCore (L := L) X XL th s σ) {T : Set U64} (hTX : ∀ t ∈ T, t ∉ X) (XL' : U64 → Nat)
    (hXL : ∀ u ∈ X, XL' u = XL u)
    {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    (hpl : ∀ t ∈ T, t.val % 4096 = 0 ∧ t.val + 4096 ≤ 2 ^ 64)
    (hz : ∀ t ∈ T, ∀ i : BitVec 9, L.mem s' (eptA t i) = 0#u64)
    (hσt : ∀ t ∈ T, σ'.kheap t.bv = some (.archObj (.ept (XL' t) (fun _ => 0))))
    (hxk : ∀ u ∈ X, σ'.kheap u.bv = σ.kheap u.bv)
    (hne : ∀ r l' es, σ'.kheap r = some (.archObj (.ept l' es)) →
      (∃ t ∈ T, r = t.bv) ∨ ∃ l'' es', σ.kheap r = some (.archObj (.ept l'' es')))
    (hcap : ∀ y, IsSlot th' y → ∀ p l' a v (mm : Bool), capV (L.mem s') y = .Ept p l' mm a v →
      (p ∈ T ∧ l'.val = XL' p) ∨ (IsSlot th y ∧ capV (L.mem s) y = .Ept p l' mm a v))
    (huq : ∀ t ∈ T, ∀ y y', IsSlot th' y → IsSlot th' y' → ∀ l1 l2 a1 a2 v1 v2 (m1 m2 : Bool),
      capV (L.mem s') y = .Ept t l1 m1 a1 v1 → capV (L.mem s') y' = .Ept t l2 m2 a2 v2 → y = y')
    (hX' : JExtEpt (L := L) (T ∪ X) th' s')
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hks : ∀ t ∈ T, t.val + 4096 ≤ (L.ksb s').val ∨ (L.ksb s').val + 304384 ≤ t.val)
    (hsep : ∀ u ∈ T ∪ X, ∀ o ko, σ'.kheap o = some ko → o ≠ u.bv → EptApart u o ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ')
    (htb : ∀ t ∈ T, (XL' t = 0 ∨ XL' t = 39 ∨ XL' t = 30 ∨ XL' t = 21) ∧ Vs.PaM t 4503599627366400#u64) :
    EptCore (L := L) (T ∪ X) XL' th' s' σ' where
  rel := by
    refine ⟨fun u hu => ?_, fun r l' es hk => ?_, fun u hu => ?_⟩
    · rcases hu with hu | hu
      · refine ⟨fun _ => 0, hσt u hu, fun i _ => ?_⟩
        unfold EptWord; rw [hz u hu i]; rfl
      · obtain ⟨es, hk, hwd⟩ := C.rel.obj u hu
        refine ⟨es, by rw [hXL u hu, hxk u hu]; exact hk, fun i hi => ?_⟩
        rw [hXL u hu] at hi
        have hp := C.rel.place u hu
        have e := eptA_val hp.2 i
        have hi9 := i.isLt
        rw [hw.mem_eq (b := eptA u i) (by unfold P1.Aligned; rw [e]; omega)
          (fun hb => by rcases hW _ hb u hu with h | h <;> omega)]
        exact hwd i hi
    · rcases hne r l' es hk with ⟨t, ht, rfl⟩ | ⟨l'', es', h⟩
      · exact ⟨t, Or.inl ht, rfl⟩
      · obtain ⟨u, hu, e⟩ := C.rel.spec r l'' es' h
        exact ⟨u, Or.inr hu, e⟩
    · rcases hu with hu | hu
      · exact hpl u hu
      · exact C.rel.place u hu
  capL y hy p l' a v mm hc := by
    rcases hcap y hy p l' a v mm hc with ⟨-, hl⟩ | ⟨hy', hc'⟩
    · exact hl
    · have hpX : p ∈ X := by have h := C.exte.cap y hy'; rw [hc'] at h; exact h
      rw [hXL p hpX]
      exact C.capL y hy' p l' a v mm hc'
  exte := hX'
  tag e he h1 := by
    obtain ⟨u, hu, h1', h2⟩ := C.tag e (hge e he) h1
    exact ⟨u, Or.inr hu, h1', by rw [hXL u hu]; exact h2⟩
  ks u hu := by
    rcases hu with hu | hu
    · exact hks u hu
    · rw [hw.1]; exact C.ks u hu
  sep := hsep
  ue y hy p l' a v hc := by
    rcases hcap y hy p l' a v false hc with ⟨hpT, -⟩ | ⟨hy0, hc0⟩
    · -- a new table: zero on both sides (retype), one cap (`huq`), named by no tagged entry (`tag`: `p ∉ X`)
      refine ⟨hz p hpT, hσt p hpT, fun y' hy' hne l2 m2 a2 v2 hc2 =>
        hne (huq p hpT y' y hy' hy l2 l' a2 a v2 v m2 false hc2 hc), fun e he h1 he' => ?_⟩
      obtain ⟨u, hu, h2, -⟩ := C.tag e (hge e he) h1
      exact hTX p hpT (by rw [show u = p from UScalar.eq_of_val_eq (by show u.bv.toNat = p.bv.toNat; rw [h2, he'])] at hu; exact hu)
    · have hpX : p ∈ X := by have h := C.exte.cap y hy0; rw [hc0] at h; exact h
      have hpt : p ∉ T := fun h => hTX p h hpX
      obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy0 p l' a v hc0
      refine ⟨fun i => ?_, by rw [hXL p hpX, hxk p hpX]; exact h2, ?_, fun e he h1' => h4 e (hge e he) h1'⟩
      · have hp := C.rel.place p hpX
        have e := eptA_val hp.2 i
        have hi9 := i.isLt
        rw [hw.mem_eq (b := eptA p i) (by unfold P1.Aligned; rw [e]; omega)
          (fun hb => by rcases hW _ hb p hpX with h | h <;> omega)]
        exact h1 i
      · intro y' hy' hne l2 m2 a2 v2 hc2
        rcases hcap y' hy' p l2 a2 v2 m2 hc2 with ⟨e, -⟩ | ⟨hy0', hc0'⟩
        · exact hpt e
        · exact h3 y' hy0' hne l2 m2 a2 v2 hc0'
  eslot := C.eslot.step h5
  walk := C.walkZ (Z0 := T) (fun u hu _ => hxk u hu) (fun t ht => ⟨XL' t, hσt t ht, fun h => (hTX t ht h).elim⟩) hne
    (fun e he _ => Or.inl (hge e he))
  named := hnm
  tbl u hu := by
    rcases hu with hu | hu
    · exact htb u hu
    · rw [hXL u hu]; exact C.tbl u hu

/-- **`EptCore` across the retype of a guest table `t` at level `l`** (`X` grows; module docstring). -/
theorem EptCore.grow (C : EptCore (L := L) X XL th s σ) {t : U64} (htX : t ∉ X) (l : Nat)
    {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    (hpl : t.val % 4096 = 0 ∧ t.val + 4096 ≤ 2 ^ 64)
    (hz : ∀ i : BitVec 9, L.mem s' (eptA t i) = 0#u64)
    (hσt : σ'.kheap t.bv = some (.archObj (.ept l (fun _ => 0))))
    (hxk : ∀ u ∈ X, σ'.kheap u.bv = σ.kheap u.bv)
    (hne : ∀ r l' es, σ'.kheap r = some (.archObj (.ept l' es)) →
      r = t.bv ∨ ∃ l'' es', σ.kheap r = some (.archObj (.ept l'' es')))
    (hcap : ∀ y, IsSlot th' y → ∀ p l' a v (mm : Bool), capV (L.mem s') y = .Ept p l' mm a v →
      (p = t ∧ l'.val = l) ∨ (IsSlot th y ∧ capV (L.mem s) y = .Ept p l' mm a v))
    (huq : ∀ y y', IsSlot th' y → IsSlot th' y' → ∀ l1 l2 a1 a2 v1 v2 (m1 m2 : Bool),
      capV (L.mem s') y = .Ept t l1 m1 a1 v1 → capV (L.mem s') y' = .Ept t l2 m2 a2 v2 → y = y')
    (hX' : JExtEpt (L := L) (insert t X) th' s')
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hks : t.val + 4096 ≤ (L.ksb s').val ∨ (L.ksb s').val + 304384 ≤ t.val)
    (hsep : ∀ u ∈ insert t X, ∀ o ko, σ'.kheap o = some ko → o ≠ u.bv → EptApart u o ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ')
    (htb : (l = 0 ∨ l = 39 ∨ l = 30 ∨ l = 21) ∧ Vs.PaM t 4503599627366400#u64) :
    EptCore (L := L) (insert t X) (Function.update XL t l) th' s' σ' := by
  rw [← Set.singleton_union]
  refine C.growS (T := {t}) (fun u hu => by rw [Set.mem_singleton_iff.1 hu]; exact htX) (Function.update XL t l)
    (fun u hu => Function.update_of_ne (fun (e : u = t) => htX (e ▸ hu)) _ _) hw hW
    (fun u hu => by rw [Set.mem_singleton_iff.1 hu]; exact hpl)
    (fun u hu => by rw [Set.mem_singleton_iff.1 hu]; exact hz)
    (fun u hu => by rw [Set.mem_singleton_iff.1 hu, Function.update_self]; exact hσt) hxk
    (fun r l' es hk => (hne r l' es hk).imp (fun e => ⟨t, rfl, e⟩) id)
    (fun y hy p l' a v mm hc => (hcap y hy p l' a v mm hc).imp
      (fun ⟨e, hl⟩ => ⟨e, by rw [e, Function.update_self]; exact hl⟩) id)
    (fun u hu => by rw [Set.mem_singleton_iff.1 hu]; exact huq)
    (by rw [Set.singleton_union]; exact hX') hge
    (fun u hu => by rw [Set.mem_singleton_iff.1 hu]; exact hks)
    (by rw [Set.singleton_union]; exact hsep) h5 hnm
    (fun u hu => by rw [Set.mem_singleton_iff.1 hu, Function.update_self]; exact htb)

end

end

end Fl4Proofs.P3
