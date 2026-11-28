/-
P3 (p1dom): **FL4's one domain (P1's `DomInv`) at every joint state and every
kernel exit** `kernel_entry_reachU29` reaches, and `next_domain`.

* `SchedSpec.domInv` / `SchedRel.domInv`: P3's scheduler relation carries
  `CUR_DOMAIN = 0` and every TCB's `DOMAIN = 0` (`SchedSpec.curDom`, `.tcb`),
  so `DomInv` holds over its TCBs at every state P3 relates (also inside an
  entry, wherever a `SchedRel` is carried: the end of the body, `awaken`).
* `JAtZ.domInv`: at every joint state, over `H`'s TCBs.
* `EntDomAt` / `JAt.entDomAt`: P1's `EntryDomInv` (`EntryInv` ∧ `DomInv`
  over the same sets) at a joint state with the action resume.
* **`kernel_entry_domInvU29`**: `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29)
  with `EntryDomInv` at the entry and `EntDomAt` at the exit of each of its six
  entry kinds.
* `NdDomOK`: the domain schedule's two domain words are 0 and the start index
  is an entry (l4v `valid_domain_list` with one domain; the words
  `DomainScheduleConfigure` (domain.rs:44-63) writes with `dom < NUM_DOMAINS`,
  `DomainScheduleSetStart` (domain.rs:65-81) with `index < NUM_DOMAIN_SCHEDULES`).
  **`sched.next_domain.domInv`**: `next_domain` (sched.rs:566-577), the only
  writer of `CUR_DOMAIN` after boot, keeps `DomInv` and `NdDomOK`.
* (ndd) `NdDomOK` is no open premise: `ndDomOK_of` derives it from `DomRel`
  (carried in P3's relation, `RelTopB`) and `DomListOK` (carried in `SInvX`
  as `SInvA.dom`, kept by every entry from `hnd : numDomains = 1` [P], the
  premise U29 already has); `ndDomOK_of_ndOK` from `NdOK` (what the finish
  bundle gives where `next_domain` runs: `σ.domainTime ≠ 0 ∨ NdOK s σ`);
  `JAtZ.ndDomOK` at every joint state; `EntDomNdAt` / `JAt.entDomNdAt`.
  **`kernel_entry_domNdU29`**: `kernel_entry_domInvU29` (left as it was) with
  `NdDomOK` at the entry and `EntDomNdAt` at the exit of each entry kind.

No premise beyond U29's. No existing statement changed.
-/
import Fl4Proofs.P3.XTopJointEntryInv29
import Fl4Proofs.P3.ScNextDom
import Fl4Proofs.P1.DomInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem cdomA_ksW (s : S) : P1.cdomA st s = ksW (L.ksb s) 8#u64 := by
  unfold P1.cdomA ksW layout.ks.CUR_DOMAIN; rfl

/-! ## `next_domain` -/

/-- The domain schedule's domain words (FL4's two entries) are 0 and the start
index is an entry. -/
def NdDomOK (st : machine.Store S) [L : P1.LawfulStore st] (s : S) : Prop :=
  (∀ i : U64, i.val < 2 → L.mem s (ksW (L.ksb s) (entOff i)) = 0#u64) ∧ (L.mem s (ksW (L.ksb s) 32#u64)).val < 2

/-- The state `next_domain` leaves (index `i`, domain `d`, duration `t`). -/
def ndS2 (s : S) (i d t : U64) : S :=
  L.wr (L.wr (L.wr (L.wr (L.wr s (ksW (L.ksb s) 24#u64) i)
    (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) (ksW (L.ksb s) 40#u64) 0#u64)
    (ksW (L.ksb s) 8#u64) d) (ksW (L.ksb s) 16#u64) t

theorem ndS2_ksb (s : S) (i d t : U64) : L.ksb (ndS2 (L := L) s i d t) = L.ksb s := by
  unfold ndS2; simp only [L.ksb_wr]

/-- The words `next_domain` does not write. -/
theorem ndS2_mem {T : Set U64} {s : S} (hN : P1.NodePlaced st T s (L.cpu s)) (i d t : U64) {b : U64}
    (hb : P1.Aligned b) (n8 : b.val ≠ (L.ksb s).val + 8) (n16 : b.val ≠ (L.ksb s).val + 16)
    (n24 : b.val ≠ (L.ksb s).val + 24) (n40 : b.val ≠ (L.ksb s).val + 40)
    (nR : b.val ≠ L.nodeBase s (L.cpu s) + 56) :
    L.mem (ndS2 (L := L) s i d t) b = L.mem s b := by
  have hf := hN.fits
  have hal := hN.align
  simp only [P1.LawfulStore.nodeBase] at hf hal nR
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  have kv : ∀ (o : U64) (n : Nat), o.val = n → n < 256 → (ksW (L.ksb s) o).val = (L.ksb s).val + n :=
    fun o n e hn => by rw [ksW_val (by omega), e]
  have hRo : layout.node.REPROGRAM.val < 4288 := by simp [layout.node.REPROGRAM]
  have hR8 : layout.node.REPROGRAM.val % 8 = 0 := by simp [layout.node.REPROGRAM]
  have hRv : (L.nodeAt s (L.cpu s) layout.node.REPROGRAM).val = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 + 56 := by
    rw [P1.nodeAt_val hN hRo]; simp [P1.LawfulStore.nodeBase, layout.node.REPROGRAM]
  unfold ndS2
  rw [L.mem_wr_ne (ksW_al (o := 16#u64) hkf hka (by decide) (by decide)) hb (by rw [kv 16#u64 16 rfl (by decide)]; omega),
    L.mem_wr_ne (ksW_al (o := 8#u64) hkf hka (by decide) (by decide)) hb (by rw [kv 8#u64 8 rfl (by decide)]; omega),
    L.mem_wr_ne (ksW_al (o := 40#u64) hkf hka (by decide) (by decide)) hb (by rw [kv 40#u64 40 rfl (by decide)]; omega),
    L.mem_wr_ne (P1.nodeAt_aligned hN hRo hR8) hb (by rw [hRv]; omega),
    L.mem_wr_ne (ksW_al (o := 24#u64) hkf hka (by decide) (by decide)) hb (by rw [kv 24#u64 24 rfl (by decide)]; omega)]

/-- **`next_domain` keeps FL4's one domain** (sched.rs:566-577): the new
`CUR_DOMAIN` is the domain word of the entry it switches to (an entry: the
next one, or the start index), 0 by `NdDomOK`; no `DOMAIN` word and no schedule
entry is written. -/
theorem sched.next_domain.domInv {T Cs Ω : Set U64} {H : P1.Heap} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (s : S) (h0 : P1.SchedQueuesInv st T Cs Ω H s Q R) (h : P1.DomInv st T s)
    (hD : NdDomOK st s) :
    sched.next_domain st s ⦃ s' => P1.DomInv st T s' ∧ NdDomOK st s' ⦄ := by
  have hN := h0.nodes _ h0.cur
  have hf := hN.fits
  have hal := hN.align
  simp only [P1.LawfulStore.nodeBase] at hf hal
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  have kv : ∀ (o : U64) (n : Nat), o.val = n → n < 256 → (ksW (L.ksb s) o).val = (L.ksb s).val + n :=
    fun o n e hn => by rw [ksW_val (by omega), e]
  have kI : layout.ks.DOM_SCHED_IDX = 24#u64 := by unfold layout.ks.DOM_SCHED_IDX; rfl
  have kS : layout.ks.DOM_SCHED_START = 32#u64 := by unfold layout.ks.DOM_SCHED_START; rfl
  have kW : layout.ks.WORK_UNITS = 40#u64 := by unfold layout.ks.WORK_UNITS; rfl
  have kC : layout.ks.CUR_DOMAIN = 8#u64 := by unfold layout.ks.CUR_DOMAIN; rfl
  have kD : layout.ks.DOMAIN_TIME = 16#u64 := by unfold layout.ks.DOMAIN_TIME; rfl
  unfold sched.next_domain
  simp only [kI, kS, kW, kC, kD, ks_get_eq, bind_ok, lift]
  refine WP.spec_bind (Pₘ := fun idx1 : U64 => idx1.val < 2) ?_ fun idx1 hi => ?_
  · split
    · exact (WP.spec_ok _).2 hD.2
    · rename_i hge
      simp only [dur_eq, bind_ok]
      split
      · exact (WP.spec_ok _).2 hD.2
      · refine (WP.spec_ok _).2 ?_
        rw [nds_eq] at hge
        revert hge
        generalize core.num.U64.wrapping_add (L.mem s (ksW (L.ksb s) 24#u64)) 1#u64 = x
        intro hge
        scalar_tac
  simp only [ks_set_eq, set_reprogram_eq, dom_eq, dur_eq, bind_ok, L.ksb_wr, L.cpu_wr, P1.nodeAt_wr]
  -- the store is `ndS2 s idx1 d t`
  have hen := entOff_val hi
  have hN3 : ∀ {b : U64}, P1.Aligned b → b.val ≠ (L.ksb s).val + 24 → b.val ≠ (L.ksb s).val + 40 →
      b.val ≠ L.nodeBase s (L.cpu s) + 56 →
      L.mem (L.wr (L.wr (L.wr s (ksW (L.ksb s) 24#u64) idx1) (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
        (ksW (L.ksb s) 40#u64) 0#u64) b = L.mem s b := by
    intro b hb n24 n40 nR
    have hRo : layout.node.REPROGRAM.val < 4288 := by simp [layout.node.REPROGRAM]
    have hR8 : layout.node.REPROGRAM.val % 8 = 0 := by simp [layout.node.REPROGRAM]
    have hRv : (L.nodeAt s (L.cpu s) layout.node.REPROGRAM).val = L.nodeBase s (L.cpu s) + 56 := by
      rw [P1.nodeAt_val hN hRo]; simp [layout.node.REPROGRAM]
    rw [L.mem_wr_ne (ksW_al (o := 40#u64) hkf hka (by decide) (by decide)) hb (by rw [kv 40#u64 40 rfl (by decide)]; omega),
      L.mem_wr_ne (P1.nodeAt_aligned hN hRo hR8) hb (by rw [hRv]; omega),
      L.mem_wr_ne (ksW_al (o := 24#u64) hkf hka (by decide) (by decide)) hb (by rw [kv 24#u64 24 rfl (by decide)]; omega)]
  have hE : ∀ i : U64, i.val < 2 → P1.Aligned (ksW (L.ksb s) (entOff i)) ∧
      (ksW (L.ksb s) (entOff i)).val = (L.ksb s).val + 192 + 16 * i.val := by
    intro i hi'
    have := entOff_val hi'
    refine ⟨ksW_al hkf hka (by omega) (by omega), by rw [ksW_val (by omega), this]; omega⟩
  have hNB : L.nodeBase s (L.cpu s) = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 := rfl
  have hd : L.mem (L.wr (L.wr (L.wr s (ksW (L.ksb s) 24#u64) idx1) (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64)
      (ksW (L.ksb s) 40#u64) 0#u64) (ksW (L.ksb s) (entOff idx1)) = 0#u64 := by
    obtain ⟨a1, v1⟩ := hE idx1 hi
    rw [hN3 a1 (by omega) (by omega) (by rw [hNB]; omega)]
    exact hD.1 idx1 hi
  rw [WP.spec_ok]
  refine ⟨⟨?_, fun t ht => ?_⟩, fun i hi' => ?_, ?_⟩
  · show L.mem _ (P1.cdomA st (ndS2 (L := L) s idx1 _ _)) = 0#u64
    rw [cdomA_ksW, ndS2_ksb]
    rw [L.mem_wr_ne (ksW_al (o := 16#u64) hkf hka (by decide) (by decide)) (ksW_al (o := 8#u64) hkf hka (by decide) (by decide))
      (by rw [kv 16#u64 16 rfl (by decide), kv 8#u64 8 rfl (by decide)]; omega),
      L.mem_wr_same (ksW_al (o := 8#u64) hkf hka (by decide) (by decide))]
    exact hd
  · have hT := h0.tcbs t ht
    have hv := P1.domA_val hT
    have hk := h0.ksOut t ht
    have hdj := hN.disj t ht
    rw [hNB] at hdj
    show L.mem (ndS2 (L := L) s idx1 _ _) (P1.domA t) = 0#u64
    rw [ndS2_mem hN idx1 _ _ (P1.domA_aligned hT) (by omega) (by omega) (by omega) (by omega) (by rw [hNB]; omega)]
    exact h.2 t ht
  · show L.mem (ndS2 (L := L) s idx1 _ _) (ksW (L.ksb (ndS2 (L := L) s idx1 _ _)) (entOff i)) = 0#u64
    rw [ndS2_ksb]
    obtain ⟨a1, v1⟩ := hE i hi'
    rw [ndS2_mem hN idx1 _ _ a1 (by omega) (by omega) (by omega) (by omega) (by rw [hNB]; omega)]
    exact hD.1 i hi'
  · show (L.mem (ndS2 (L := L) s idx1 _ _) (ksW (L.ksb (ndS2 (L := L) s idx1 _ _)) 32#u64)).val < 2
    rw [ndS2_ksb, ndS2_mem hN idx1 _ _ (ksW_al (o := 32#u64) hkf hka (by decide) (by decide))
      (by rw [kv 32#u64 32 rfl (by decide)]; omega) (by rw [kv 32#u64 32 rfl (by decide)]; omega)
      (by rw [kv 32#u64 32 rfl (by decide)]; omega) (by rw [kv 32#u64 32 rfl (by decide)]; omega)
      (by rw [kv 32#u64 32 rfl (by decide), hNB]; omega)]
    exact hD.2

end

/-! ## At every joint state -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **`NdDomOK` from the domain schedule relation and `DomListOK`**: `DomRel`
gives entry `i`'s spec domain as the word (below `2 ^ 8`) and the start index
as the `DOM_SCHED_START` word, `DomListOK.dom` every entry's domain 0 and
`DomListOK.start` the start index below the length 2. -/
theorem ndDomOK_of (hD : DomRel (L.mem s) (L.ksb s) σ) (hV : DomListOK σ) : NdDomOK st s := by
  obtain ⟨hl, he, hs, -⟩ := hD
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨hg, hlt, -, -⟩ := he i hi
    have h0 := hV.dom _ (List.mem_of_getElem? hg)
    simp only at h0
    have hv : (L.mem s (ksW (L.ksb s) (entOff i))).val = 0 := by
      have h1 : (BitVec.ofNat 8 (L.mem s (ksW (L.ksb s) (entOff i))).val).toNat = 0 := by rw [h0]; rfl
      rw [BitVec.toNat_ofNat] at h1
      omega
    exact UScalar.eq_of_val_eq (by simpa using hv)
  · have := hV.start
    rw [hs, hl] at this
    exact this

/-- `NdOK` (what `next_domain` reads, ScNextDomB) gives `NdDomOK`. -/
theorem ndDomOK_of_ndOK (h : NdOK (L := L) s σ) : NdDomOK st s := ndDomOK_of h.1 h.2.1

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

end

end Fl4Proofs.P3.SInvR.G5
