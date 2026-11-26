/-
# P2 (line stpost, generation 13): the entry facts of the CNodeDelete-no-PTE arm

The interface between the plan side (what `localinv.plan` decided at the entry: `InvSeen`) and the decode
block (`InvBlk`): `DelEnt` collects, at the entry state `s`, the invoked CNode cap at the plan's slot, the target
slot `dest` its lookup finds from the first two message registers, `dest`'s cap (a small RAM frame, unmapped or
with ASID 0: no PTE), the walk's closure `C` (with the invoked CNode in it), `dest` a capability slot outside the
objects, and the locks the glue holds on `dest` and its CDT neighbours (each a capability slot).

* `slot_word_val`, **`IoPre.lockSlot`**: a word of a capability slot whose lock the glue holds is in `IoRS`; it is
  in `IoWS` at offsets `≥ 16`, and at offsets `< 16` when the slot is not a TCB's own and holds a Null / Frame cap;
* `nof_of_frame`: a slot decoding to a frame cap holds a `NullOrFrame` word 0;
* `DelEnt` (definition), `InvLk` (the plan's slot is the `CAP` lookup's), `InvQF` (`InvQ ∧ InvLk`);
* the two [J] layout facts the plan side uses, as definitions: `InvMapJ` (a mapped small RAM frame cap with a
  non-zero ASID has a page-table entry `small_page_entry` finds, non-zero) and `InvCdtJ` (a capability slot's
  CDT neighbours are capability slots).

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvVs
import Fl4Proofs.P3.Encode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

section lock
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
variable {Locks : S → U64 → Prop}

theorem slot_word_val {p o : U64} (hp : p.val + 32 ≤ 2 ^ 64) (ho : o.val < 32) :
    (core.num.U64.wrapping_add p o).val = p.val + o.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- (stpost gen 13) **A word of a locked capability slot**: readable; writable at offsets `≥ 16`, and below when
the slot is no TCB's own and holds a Null / Frame cap (rule 2). -/
theorem IoPre.lockSlot (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {p o : U64} (hp : p ∈ K.slots)
    (hl : Locks s p) (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add p o) ∧
      (16 ≤ o.val ∨ (¬ TcbSlot K p ∧ NullOrFrame (L.mem s p)) →
        IoWS (st := st) K Locks s (core.num.U64.wrapping_add p o)) := by
  obtain ⟨p8, pf⟩ := P.lay.slot8 p hp
  have hv := slot_word_val pf ho
  have hin : InW p 32 (core.num.U64.wrapping_add p o) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  have hr := P.lay.slotw p hp _ hin
  have ha : Aligned (core.num.U64.wrapping_add p o) := by unfold Aligned; rw [hv]; omega
  have hd : (core.num.U64.wrapping_add p o).val - p.val = o.val := by rw [hv]; omega
  have hown : own K (L.mem s) (core.num.U64.wrapping_add p o) = slotOwner K (L.mem s) p o.val := by
    simp only [own, hr, hd]
  have hnu := P.region_kernel (b := core.num.U64.wrapping_add p o) (Or.inl (by rw [hr]; simp))
  refine ⟨⟨ha, hnu, ?_⟩, fun hw => ⟨ha, ?_⟩⟩
  · unfold RPerm GateOnly
    rw [hown]
    unfold slotOwner
    by_cases h16 : 16 ≤ o.val
    · rw [if_pos h16]; exact Or.inl hl
    · rw [if_neg h16]
      by_cases hT : TcbSlot K p
      · rw [if_pos hT]; exact Or.inr rfl
      · rw [if_neg hT]
        by_cases hn : NullOrFrame (L.mem s p)
        · rw [if_pos hn]; exact Or.inl hl
        · rw [if_neg hn]; exact Or.inr rfl
  · unfold WPerm
    rw [hown]
    unfold slotOwner
    by_cases h16 : 16 ≤ o.val
    · rw [if_pos h16]; exact hl
    · rw [if_neg h16]
      obtain ⟨hT, hn⟩ := hw.resolve_left h16
      rw [if_neg hT, if_pos hn]; exact hl

/-- A frame cap's first word is `NullOrFrame` (tag 13). -/
theorem nof_of_frame {w0 w1 fp rt asid va : U64} {sz : capability.FrameSize} {d mp e : Bool}
    (h : capability.Cap.decode w0 w1 = ok (.Frame fp sz rt d mp e asid va)) : NullOrFrame w0 := by
  rw [Fl4Proofs.P3.decode_eq] at h
  have h' := ok_inj_ff h
  unfold Fl4Proofs.P3.decodeF at h'
  right
  have key : (w0.bv >>> 59).toNat = 13 := by
    split at h' <;> first | (rename_i heq; exact heq) | simp at h'
  have e1 : (w0.bv >>> 59).toNat = w0.val / 2 ^ 59 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; rfl
  omega

theorem nof_of_frame_slot {sl fp rt asid va : U64} {sz : capability.FrameSize} {d mp e : Bool}
    (h : obj.Slot.cap st sl s = ok (.Frame fp sz rt d mp e asid va)) : NullOrFrame (L.mem s sl) := by
  unfold obj.Slot.cap at h
  rw [L.read_pair_eq] at h
  simp only [bind_ok] at h
  exact nof_of_frame h

/-- (stpost gen 13) **A capability-slot word is not written by the local entry's prefix** (`PreW`: the current
thread's `FAULT_IP`, a TCB word, and the core's `CUR_TIME` / `CONSUMED`, node words): the regions differ. -/
theorem IoPre.slot_notPreW (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {q b : U64} (hq : q ∈ K.slots)
    (hb : InW q 32 b) : ¬ PreW (L := L) s (L.curW s) b := by
  have hr := P.lay.slotw q hq b hb
  rintro (⟨k, hk, e⟩ | e | e)
  · have ht := P.lay.tcbw _ (P.hT _ P.cT) k (by omega) (by omega)
    unfold fld at ht
    rw [← e, hr] at ht
    cases ht
  · have hn := P.lay.node _ _ (P.inNode layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]))
    have hn' : region K b = OwnMap.Region.node (L.cpu s) := by rw [e]; exact hn
    rw [hr] at hn'
    cases hn'
  · have hn := P.lay.node _ _ (P.inNode layout.node.CONSUMED (by simp [layout.node.CONSUMED]))
    have hn' : region K b = OwnMap.Region.node (L.cpu s) := by rw [e]; exact hn
    rw [hr] at hn'
    cases hn'

/-- (stpost gen 13) **Capability-slot words survive the prefix.** -/
theorem IoPre.slot_keep (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {s2 : S}
    (w : WritesIn st s s2 (PreW (L := L) s (L.curW s))) {q b : U64} (hq : q ∈ K.slots) (hb : InW q 32 b)
    (ha : Aligned b) : L.mem s2 b = L.mem s b :=
  w.2.2 b ha (P.slot_notPreW hq hb)

/-- The words `0`, `8`, `16`, `24` of a capability slot lie in it. -/
theorem slot_inW {q o : U64} (hq : q.val + 32 ≤ 2 ^ 64) (ho : o.val < 32) :
    InW q 32 (core.num.U64.wrapping_add q o) := by
  have hv := slot_word_val hq ho
  exact ⟨by rw [hv]; omega, by rw [hv]; omega⟩

end lock

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- (stpost gen 13) **The entry facts of the CNodeDelete-no-PTE arm** at the entry `s` (module docstring): the
invoked CNode cap at the plan's slot; the target `dest` its lookup finds from `R10` / `R8` (the first two message
registers, `sarg0_reg` / `sarg1_reg`); `dest`'s cap, a small RAM frame, unmapped, with ASID 0, or with no PTE `small_page_entry` finds (gen 14: stale
mapped caps); the walk's closure
`C` (the invoked CNode in it, closed, its radix-masked slots capability slots outside the objects); `dest` a
capability slot outside the objects with its lock held; its CDT neighbours (`PREV` word, `Slot.next`), when not
null, capability slots with their locks held. -/
def DelEnt (K : KLayout) (Cs : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (s : S) : Prop :=
  ∃ (cp cr cg cgb dest fp rt asid va : U64) (mp : Bool) (C : U64 → U64 → Prop),
    obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧
    cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
      (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
    obj.Slot.cap st dest s = ok (.Frame fp .Small rt false mp false asid va) ∧
    (mp = false ∨ asid = 0#u64 ∨ localinv.small_page_entry st s asid va = ok none) ∧
    C cp cr ∧ WalkCl (st := st) s C ∧
    (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
      OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
    dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧ Locks s dest ∧
    (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots ∧
      Locks s (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV))) ∧
    (∀ nx, obj.Slot.next st dest s = ok nx → nx ≠ 0#u64 → nx ∈ K.slots ∧ Locks s nx)

variable (st) in
/-- The plan's slot is the slot the current thread's `CAP` register names (`localinv.plan`'s lookup). -/
def InvLk (p : localinv.Plan) (s : S) : Prop :=
  ∃ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) ∧
    x.slot = p.slot

variable (st) in
/-- (stpost gen 13) **The canonical `Q` with the plan's lookup**: `InvQ ∧ InvLk`. -/
def InvQF (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  InvQ st Cs Ω Sg Ac Locks p K m s ∧ InvLk st p s

variable (st) in
/-- (Superseded, gen 14: **false at P3 states** — stale mapped frame caps survive a VSpace root's deletion; no longer
used, replaced by `InvVsJ`.) A mapped small RAM frame cap with a non-zero ASID has its page-table entry:
at a state of `P`, a capability slot holding it has `small_page_entry` find a non-zero entry. -/
def InvMapJ (K : KLayout) (P : S → Prop) : Prop :=
  ∀ s sl fp rt asid va, P s → sl ∈ K.slots →
    obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
    ∃ e, localinv.small_page_entry st s asid va = ok (some e) ∧ e ≠ 0#u64

variable (st) in
/-- [J] **A capability slot's CDT neighbours are capability slots** (P1's CDT well-formedness), at a state of `P`. -/
def InvCdtJ (K : KLayout) (P : S → Prop) : Prop :=
  ∀ s sl, P s → sl ∈ K.slots →
    (L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) ∈ K.slots) ∧
    (∀ nx, obj.Slot.next st sl s = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)

end ent

end Fl4Proofs.P2.PathObl
