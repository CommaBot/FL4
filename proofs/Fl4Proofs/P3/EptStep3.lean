/-
P3 (line mmuAD, gen 42b1): **`EptCore` at the guest-table writes of map / unmap** — one entry written on both sides
(FL4's `s.write(e, …)` ↔ the spec's `storeGuestEntry`) a table cleared on both sides (FL4's `s.zero(ptr, 4096)`
↔ the spec's `setObject ptr (.ept l 0)`), and a table leaving `X`, stated over the step's footprint.

* **`EptCore.ofObj`**: the generic form — every table of `X` is, after the step, a spec `.ept (XL t) es'` whose related
  words FL4 holds (the new `rel.obj`), and the rest is the frame of `EptCore.frame` (slot `Ept` caps keep pointer
  and level, `JExtEpt X` after, no new spec guest table, no new pool entry, sizes kept).
* **`EptCore.entry`**: FL4 writes the entry `eptA t0 i0` (and words off every table) and the spec stores
  `e` at entry `i0` of `t0` (`storeGuestEntry`, VirtEptInv l. 84-86), FL4's word equal to `e` up to `eptHw`. FL4: the
  table map writes `paddr(ptr) | 7` (ept.rs l. 300) and the spec `GuestPte.encode virtKind (.table …)`
  (VirtEptInv l. 222); the frame map writes `frame_entry …` (l. 161-167, 187) and the spec the frame entry
  (VirtEptInv l. 235); unmap writes 0 (l. 217) and `guestUnmap` stores 0 (VirtEptInv l. 129-145). The equality of
  the two words is the step's hypothesis (`hwd`): it is the encoding agreement of the decode, proved with the decode.
* **`EptCore.shrink`**: a table `t` leaves `X` (EPT delete / detype): no spec guest table at `t`, no slot `Ept` cap and no
  tagged pool entry naming it after the step (the final cap's `finalise` clears the root's pool entry first, ept.rs
  l. 229-230 → vspace.rs l. 344-348; a non-root table's is unmapped from its parent, l. 232).
* **`EptCore.clear`**: FL4 zeroes the 4 KiB of `t0` (ept.rs l. 271) and the spec sets `.ept l (fun _ => 0)` at `t0`
  (VirtEptInv l. 226-230).

The walk (`ept::lookup` against `guestLookupSlot`) that decides *which* entry is written is not here: it reads related
words (`EptRel.obj`) of tables reached through present non-large entries, whose address bits name tables of `X` only
if `EptRel` is strengthened by an entry-target fact (a present table entry of a table of `X` names a table of `X` one
level below). That fact is not a field of `EptCore` yet (see the handoff's open items).

Gen 42b2 (`UnmappedEmpty`): `ofObj` / `entry` / `clear` take `ue` after the step as a hypothesis (map / unmap are
not proved this generation; their decode proofs discharge it: a table map makes the mapped cap's table non-empty
only after the cap is rewritten mapped, a table unmap zeroes the table it rewrites unmapped); `shrink` takes its
caps at the same slot ("same slot, same cap") and proves `ue`.

Gen 42b8 (the walk field `EptCore.walk`): `ofObj` / `entry` / `shrink` take `EptWalk σ'` as their last hypothesis
(`hwk`; map / unmap and deletion discharge it); `clear` proves it (`EptCore.walkZ`: the cleared table is zero after).

Gen 42b10 (the named field `EptCore.named`): `ofObj` / `entry` / `clear` / `shrink` take `EptNamed` after the step
as their last hypothesis (`hnm`).

No named premise.
-/
import Fl4Proofs.P3.EptStep1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

/-- **`EptCore` with the tables' new contents given** (module docstring). -/
theorem EptCore.ofObj (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    (hobj : ∀ t ∈ X, ∃ es, σ'.kheap t.bv = some (.archObj (.ept (XL t) es)) ∧
      ∀ i : BitVec 9, (XL t ≠ 0 ∨ i.toNat < 256) → EptWord Fl4Spec.virtKind (L.mem s' (eptA t i)).bv (es i))
    (hks : L.ksb s' = L.ksb s)
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      ∃ y' a' v' mm', IsSlot th y' ∧ capV (L.mem s) y' = .Ept p l mm' a' v')
    (hX' : JExtEpt (L := L) X th' s')
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hue : UnmappedEmpty th' XL (L.mem s') σ')
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hwk : EptWalk σ') (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) X XL th' s' σ' where
  rel := ⟨hobj, fun r l es hk => by
    obtain ⟨l', es', h⟩ := hne r l es hk
    exact C.rel.spec r l' es' h, C.rel.place⟩
  capL y hy p l a v mm hc := by
    obtain ⟨y', a', v', mm', hy', hc'⟩ := hcap y hy p l a v mm hc
    exact C.capL y' hy' p l a' v' mm' hc'
  exte := hX'
  tag e he h1 := C.tag e (hge e he) h1
  ks t ht := by rw [hks]; exact C.ks t ht
  sep t ht o ko' ho hne' := by
    obtain ⟨ko, hko, hb⟩ := hsz o ko' ho
    unfold EptApart; rw [hb]; exact C.sep t ht o ko hko hne'
  ue := hue
  eslot := C.eslot.step h5
  walk := hwk
  named := hnm
  tbl := C.tbl

/-- A word of a table of `X` misses every other table of `X`. -/
theorem EptCore.inTable (C : EptCore (L := L) X XL th s σ) {t u : U64} (ht : t ∈ X) (hu : u ∈ X) (hne : u ≠ t)
    (i : BitVec 9) : (eptA u i).val < t.val ∨ t.val + 4096 ≤ (eptA u i).val := by
  have pu := C.rel.place u hu
  have pt := C.rel.place t ht
  have e := eptA_val pu.2 i
  have hi := i.isLt
  obtain ⟨esu, hku, -⟩ := C.rel.obj u hu
  have hb : u.bv ≠ t.bv := fun h => hne (UScalar.eq_of_val_eq (by show u.bv.toNat = t.bv.toNat; rw [h]))
  have hs := C.sep t ht u.bv _ hku hb
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  unfold EptApart at hs
  rw [ept_bits, h12] at hs
  have : u.bv.toNat = u.val := rfl
  rw [this] at hs
  omega

set_option maxHeartbeats 4000000 in
/-- **One entry written on both sides** (`storeGuestEntry`; module docstring). -/
theorem EptCore.entry (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    {t0 : U64} (ht0 : t0 ∈ X) {i0 : BitVec 9} {e : Fl4Spec.Word} {es0 : BitVec 9 → Fl4Spec.Word}
    (hk0 : σ.kheap t0.bv = some (.archObj (.ept (XL t0) es0)))
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → b = eptA t0 i0 ∨ ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hwd : EptWord Fl4Spec.virtKind (L.mem s' (eptA t0 i0)).bv e)
    (hk0' : σ'.kheap t0.bv = some (.archObj (.ept (XL t0) (Function.update es0 i0 e))))
    (hxk : ∀ t ∈ X, t ≠ t0 → σ'.kheap t.bv = σ.kheap t.bv)
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      ∃ y' a' v' mm', IsSlot th y' ∧ capV (L.mem s) y' = .Ept p l mm' a' v')
    (hX' : JExtEpt (L := L) X th' s')
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hue : UnmappedEmpty th' XL (L.mem s') σ')
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hwk : EptWalk σ') (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) X XL th' s' σ' := by
  refine C.ofObj (fun t ht => ?_) hw.1 hcap hX' hne hge hsz hue h5 hwk hnm
  obtain ⟨es, hk, hwd0⟩ := C.rel.obj t ht
  have hp := C.rel.place t ht
  by_cases htt : t = t0
  · subst htt
    rw [hk0] at hk
    have hes : es0 = es := by cases hk; rfl
    subst hes
    refine ⟨Function.update es0 i0 e, hk0', fun i hi => ?_⟩
    by_cases hii : i = i0
    · subst hii; rw [Function.update_self]; exact hwd
    · rw [Function.update_of_ne hii]
      have e1 := eptA_val hp.2 i
      have hi9 := i.isLt
      have hneq : eptA t i ≠ eptA t i0 := fun h => by
        obtain ⟨-, h2⟩ := C.eptA_inj ht ht (congrArg UScalar.val h)
        exact hii (BitVec.eq_of_toNat_eq h2)
      rw [hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e1]; omega) (fun hb => by
        rcases hW _ hb with h | h
        · exact hneq h
        · rcases h t ht with h | h <;> omega)]
      exact hwd0 i hi
  · refine ⟨es, by rw [hxk t ht htt]; exact hk, fun i hi => ?_⟩
    have e1 := eptA_val hp.2 i
    have hi9 := i.isLt
    rw [hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e1]; omega) (fun hb => by
      rcases hW _ hb with h | h
      · exact htt (C.eptA_inj ht ht0 (congrArg UScalar.val h)).1
      · rcases h t ht with h | h <;> omega)]
    exact hwd0 i hi

set_option maxHeartbeats 4000000 in
/-- **A table cleared on both sides** (FL4 `zero(ptr, 4096)`, spec `.ept l 0`; module docstring). -/
theorem EptCore.clear (C : EptCore (L := L) X XL th s σ) {th' : TypedHeap} {s' : S} {σ' : Fl4Spec.State Unit}
    {t0 : U64} (ht0 : t0 ∈ X) {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → (t0.val ≤ b.val ∧ b.val < t0.val + 4096) ∨ ∀ t ∈ X, b.val < t.val ∨ t.val + 4096 ≤ b.val)
    (hz : ∀ i : BitVec 9, L.mem s' (eptA t0 i) = 0#u64)
    (hk0' : σ'.kheap t0.bv = some (.archObj (.ept (XL t0) (fun _ => 0))))
    (hxk : ∀ t ∈ X, t ≠ t0 → σ'.kheap t.bv = σ.kheap t.bv)
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      ∃ y' a' v' mm', IsSlot th y' ∧ capV (L.mem s) y' = .Ept p l mm' a' v')
    (hX' : JExtEpt (L := L) X th' s')
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hge : ∀ e, GuestEntry σ' e → GuestEntry σ e)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (hue : UnmappedEmpty th' XL (L.mem s') σ')
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) X XL th' s' σ' := by
  refine C.ofObj (fun t ht => ?_) hw.1 hcap hX' hne hge hsz hue h5
    (C.walkZ (Z0 := {t0}) (fun t ht h => hxk t ht (fun e => h (Set.mem_singleton_iff.2 e)))
      (fun t h => by rw [Set.mem_singleton_iff.1 h]; exact ⟨XL t0, hk0', fun _ => rfl⟩)
      (fun r l es hk => Or.inr (hne r l es hk)) (fun e he _ => Or.inl (hge e he))) hnm
  by_cases htt : t = t0
  · subst htt
    refine ⟨fun _ => 0, hk0', fun i _ => ?_⟩
    unfold EptWord; rw [hz i]; rfl
  · obtain ⟨es, hk, hwd0⟩ := C.rel.obj t ht
    have hp := C.rel.place t ht
    refine ⟨es, by rw [hxk t ht htt]; exact hk, fun i hi => ?_⟩
    have e1 := eptA_val hp.2 i
    have hi9 := i.isLt
    have hap := C.inTable ht0 ht htt i
    rw [hw.mem_eq (b := eptA t i) (by unfold P1.Aligned; rw [e1]; omega) (fun hb => by
      rcases hW _ hb with h | h
      · omega
      · rcases h t ht with h | h <;> omega)]
    exact hwd0 i hi

/-- **`EptCore` across the removal of a table `t` from `X`** (EPT delete / detype: the spec object at `t` is no longer a
guest table, no slot `Ept` cap and no tagged pool entry names it — FL4 clears the root's pool entry in `finalise` →
`delete_asid` (ept.rs l. 229-230, vspace.rs l. 344-348) before the final cap goes, and detypes only cap-free memory). -/
theorem EptCore.shrink (C : EptCore (L := L) X XL th s σ) {t : U64} {th' : TypedHeap} {s' : S}
    {σ' : Fl4Spec.State Unit} {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → ∀ u ∈ X, u ≠ t → b.val < u.val ∨ u.val + 4096 ≤ b.val)
    (hσt : ∀ l es, σ'.kheap t.bv ≠ some (.archObj (.ept l es)))
    (hxk : ∀ u ∈ X, u ≠ t → σ'.kheap u.bv = σ.kheap u.bv)
    (hne : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
      ∃ l' es', σ.kheap r = some (.archObj (.ept l' es')))
    (hcap : ∀ y, IsSlot th' y → ∀ p l a v (mm : Bool), capV (L.mem s') y = .Ept p l mm a v →
      IsSlot th y ∧ capV (L.mem s) y = .Ept p l mm a v)
    (hX' : JExtEpt (L := L) (X \ {t}) th' s')
    (hge : ∀ e, GuestEntry σ' e → e &&& 1 = 1 → GuestEntry σ e ∧ Fl4Spec.asidEntryRoot e ≠ t.bv)
    (hsz : ∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko)
    (h5 : EptSlotStep th th' (L.mem s) (L.mem s')) (hwk : EptWalk σ') (hnm : EptNamed th' (L.mem s') σ') :
    EptCore (L := L) (X \ {t}) XL th' s' σ' where
  rel := by
    refine ⟨fun u hu => ?_, fun r l es hk => ?_, fun u hu => C.rel.place u hu.1⟩
    · have hut : u ≠ t := hu.2
      obtain ⟨es, hk, hwd⟩ := C.rel.obj u hu.1
      refine ⟨es, (hxk u hu.1 hut).trans hk, fun i hi => ?_⟩
      have hp := C.rel.place u hu.1
      have e := eptA_val hp.2 i
      have hi9 := i.isLt
      rw [hw.mem_eq (b := eptA u i) (by unfold P1.Aligned; rw [e]; omega)
        (fun hb => by rcases hW _ hb u hu.1 hut with h | h <;> omega)]
      exact hwd i hi
    · obtain ⟨l', es', h⟩ := hne r l es hk
      obtain ⟨u, hu, e⟩ := C.rel.spec r l' es' h
      refine ⟨u, ⟨hu, fun hut => ?_⟩, e⟩
      have hut' : u = t := hut
      subst hut'
      exact hσt l es (by rw [e]; exact hk)
  capL y hy p l a v mm hc := by
    obtain ⟨hy', hc'⟩ := hcap y hy p l a v mm hc
    exact C.capL y hy' p l a v mm hc'
  exte := hX'
  tag e he h1 := by
    obtain ⟨g, hr⟩ := hge e he h1
    obtain ⟨u, hu, h2, h3⟩ := C.tag e g h1
    refine ⟨u, ⟨hu, fun hut => ?_⟩, h2, h3⟩
    have hut' : u = t := hut
    subst hut'
    exact hr h2.symm
  ks u hu := by rw [hw.1]; exact C.ks u hu.1
  sep u hu o ko' ho hne' := by
    obtain ⟨ko, hko, hb⟩ := hsz o ko' ho
    unfold EptApart; rw [hb]; exact C.sep u hu.1 o ko hko hne'
  ue y hy p l a v hc := by
    obtain ⟨hy0, hc0⟩ := hcap y hy p l a v false hc
    have hpX : p ∈ X \ {t} := by have h := hX'.cap y hy; rw [hc] at h; exact h
    obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy0 p l a v hc0
    refine ⟨fun i => ?_, by rw [hxk p hpX.1 hpX.2]; exact h2, fun y' hy' hne l' mm a' v' hc' =>
      h3 y' (hcap y' hy' p l' a' v' mm hc').1 hne l' mm a' v' (hcap y' hy' p l' a' v' mm hc').2,
      fun e he h1' => h4 e (hge e he h1').1 h1'⟩
    have hp := C.rel.place p hpX.1
    have e := eptA_val hp.2 i
    have hi9 := i.isLt
    rw [hw.mem_eq (b := eptA p i) (by unfold P1.Aligned; rw [e]; omega)
      (fun hb => by rcases hW _ hb p hpX.1 hpX.2 with h | h <;> omega)]
    exact h1 i
  eslot := C.eslot.step h5
  walk := hwk
  named := hnm
  tbl u hu := C.tbl u hu.1

end

end

end Fl4Proofs.P3
