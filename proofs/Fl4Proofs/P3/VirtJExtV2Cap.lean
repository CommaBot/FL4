/-
P3x for virtualization (line virt, gen 26, item 2): **gen 23's `delete_vcpu_vcapped` from `JExtV2`** — the
`VCapped` / `VList` half of the `Vcpu` delete at the corrected extension, so that a VM-epoch bundle carrying
`JExtV2` (stale IO-port owners allowed) keeps `VList` and `VCapped` across the delete.

* `jw_mono_V`, `vl_ofTcb` (a `VList V'` at the TCB-only heap with `V' ⊆ V`, from a `VList V` at `th` with the
  kernel-state base kept, is a `VList V'` at `th`: the head word is no `JW V th` word).
* **`delete_vcpu_vcapped2`**: `delete_vcpu_vcapped`'s statement with `E : JExtV2 V X th s` and `hT : NoIoTcb`
  for `E : JExtV V X th s` (same proof; `vcpu.finalise` through `vcpu_finalise_vlW` at `thTcb th`,
  P3/VirtJExtV2Del's transfers). `VList V'` and `VCappedM V'` after, `V' ⊆ V`.

Named premises: `hT : NoIoTcb th (L.mem s)` [J] (P3/VirtJExtV2Del's, same justification: no TCB cap slot ever
holds an IO-port cap, tcb.rs l. 68-100 / 121-128 / 189-196 / 410-417, faults.rs l. 57-63); `hnd`, `hhv`, `hhc`,
`hns` [J] unchanged (gen 23/24). No existing statement changed; new file.
-/
import Fl4Proofs.P3.VirtJExtV2Del
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtJExtV2Cap
open fl4_core Classical Fl4Proofs.P0.Consts Fl4Proofs.P3 Fl4Proofs.P3.VirtVCapped Fl4Proofs.P3.VirtVCappedDel
  Fl4Proofs.P3.VirtJExtV2Del

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
variable {V X U : Set U64} {th : TypedHeap}

theorem jw_mono_V {V' : Set U64} (hV : V' ⊆ V) {b : U64} (h : JW V' th b) : JW V th b := by
  rcases h with h | h | ⟨w, hw, e⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨w, hV hw, e⟩)

/-- **A `VList` at the TCB-only heap is one at `th`** (module docstring). -/
theorem vl_ofTcb {V' : Set U64} {s s1 : S} (Vl' : VList st V' (thTcb th) s1) (hV : V' ⊆ V)
    (Vl : VList st V th s) (hk : L.ksb s1 = L.ksb s) : VList st V' th s1 := by
  have ea : P1.vHeadA st s1 = P1.vHeadA st s := by unfold P1.vHeadA; rw [hk]
  refine ⟨Vl'.lst, Vl'.hd.1, fun h => ?_, fun h => Vl'.hd.2.2 (sw_thTcb.2 h)⟩
  rw [ea] at h
  exact Vl.hd.2.1 (jw_mono_V hV h)

variable (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`delete_vcpu_vcapped` from `JExtV2`** (module docstring); `hT` [J]. -/
theorem delete_vcpu_vcapped2 (hA : P0.ArchTotal arI) (Ly : JVLay V th U) {s : S}
    (Da : DetAtB st V th (fun _ => U) s) (E : JExtV2 (L := L) V X th s) (R : RunVmB (L := L) th s)
    (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s))
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b)
    (hT : NoIoTcb th (L.mem s))
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) (hVC : VCappedM V th (L.mem s))
    {a : A} {slot v : U64} {exposed : Bool} (hx : IsSlot th slot) (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st arI s a slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ V', V' ⊆ V ∧ VList st V' th y.2.1 ∧ VCappedM V' th (L.mem y.2.1) := by
  have hP := Ly.pl
  obtain ⟨hy1, fin, s1, a1, hfin, hf0, hf1, he⟩ := delete_vcpu_ok arI hc h
  refine ⟨hy1, ?_⟩
  have hcv : capV (L.mem s) slot = .Vcpu v := capV_of_capAt hc
  have hvV : v ∈ V := by have := E.cap slot hx; rw [hcv] at this; exact this
  have hxm : slot ∈ G.chains.flatten := (hM.members slot).2 ⟨hx, _, hc, vcpu_ne_null v⟩
  -- every other VCPU's cap lies in a slot other than `slot`
  have hoth : ∀ w ∈ V, w ≠ v → ∃ y, IsSlot th y ∧ y ≠ slot ∧ capV (L.mem s) y = .Vcpu w := by
    intro w hw hwv
    obtain ⟨y0, hy0, hc0⟩ := hVC w hw
    refine ⟨y0, hy0, ?_, hc0⟩
    rintro rfl; rw [hcv] at hc0; cases hc0; exact hwv rfl
  -- the state after the finalisation
  obtain ⟨V1, hV1, Vl1, hSS, hk1, hcap1⟩ : ∃ V1, V1 ⊆ V ∧ VList st V1 th s1 ∧
      SlotsSame th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s ∧
      ∀ w ∈ V1, ∃ y, IsSlot th y ∧ y ≠ slot ∧ capV (L.mem s) y = .Vcpu w := by
    cases fin
    · obtain ⟨rfl, rfl⟩ := hf0 rfl
      refine ⟨V, fun _ h => h, Vl, SlotsSame.refl _ _, rfl, fun w hw => ?_⟩
      by_cases hwv : w = v
      · subst hwv
        rcases isFinal_vcpu_false hfin with ⟨hp, hpc⟩ | ⟨hn, hnc⟩
        · obtain ⟨g1, g2⟩ := mdb_prev_slot hP hM hxm hx hp
          exact ⟨_, g1, g2, hpc⟩
        · obtain ⟨g1, g2⟩ := mdb_next_slot hM hxm hn
          exact ⟨_, g1, g2, hnc⟩
      · exact hoth w hw hwv
    · have hhc' : ¬ CW st V (thTcb th) (fun _ => U) s (P1.vHeadA st s) := fun h => hhc (cw_thTcb.1 h)
      have hF := P1.spec_at (vcpu_finalise_vlW hA (lay_thTcb Ly) (detB_thTcb Da) (E.toTcb hT) (rvm_toTcb R)
        (vl_thTcb Vl) hnd hhv hhc' a hvV) (hf1 rfl)
      obtain ⟨-, -, -, Vl', hw0⟩ := hF
      have hw : P1.WritesIn st s s1 (fun b => BW V th b ∨ CW st V th (fun _ => U) s b ∨ LW st V s b) :=
        hw0.mono fun _ hb => hb.imp bw_thTcb.1 (Or.imp cw_thTcb.1 id)
      refine ⟨V \ {v}, Set.diff_subset, vl_ofTcb Vl' Set.diff_subset Vl hw.1,
        slotsSame_of_writes hP hw (finW_nSl Ly hns), hw.1, fun w hw' => ?_⟩
      exact hoth w hw'.1 hw'.2
  -- the slot and its links at `s1`
  have hc1 : capAt (L.mem s1) slot = ok (.Vcpu v) := by rw [hSS.capAt hx]; exact hc
  have hM1 : MdbLinks th (L.mem s1) G := hM.of_same hSS
  have hpv : prevOf (L.mem s1) slot = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s1) slot) ∧ prevOf (L.mem s1) slot ≠ slot) := by
    by_cases hp : prevOf (L.mem s1) slot = 0#u64
    · exact Or.inl hp
    · exact Or.inr (mdb_prev_slot hP hM1 hxm hx hp)
  have hnx : nextOf (L.mem s1) slot = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s1) slot) ∧ nextOf (L.mem s1) slot ≠ slot) := by
    by_cases hn : nextOf (L.mem s1) slot = 0#u64
    · exact Or.inl hn
    · exact Or.inr (mdb_next_slot hM1 hxm hn)
  have hPN : prevOf (L.mem s1) slot ≠ 0#u64 → nextOf (L.mem s1) slot ≠ 0#u64 →
      prevOf (L.mem s1) slot ≠ nextOf (L.mem s1) slot := fun h1 h2 => hM1.prev_ne_next hP hxm h1 h2
  have hEW := (P1.spec_at (empty_slot_mem (ar := arI) hP s1 a1 slot hx _ hc1 (vcpu_ne_null v) hpv hnx hPN) he).1
  have hF2 := (P1.spec_at (Vs.empty_frame2 (ar := arI) hP s1 a1 slot hx _ hc1 (hpv.imp_right And.left)
    (hnx.imp_right And.left)) he).1
  refine ⟨V1, hV1, ?_, fun w hw => ?_⟩
  · -- the list words are no slot words
    have hhd : P1.vHeadA st s1 = P1.vHeadA st s := by unfold P1.vHeadA; rw [hk1]
    refine Vl1.frame hF2.1 (fun b hb => hF2.2.2 b ?_ ?_) (fun _ h => h) (fun _ h => h)
    · rcases hb with e | ⟨w, hw, e | e⟩
      · rw [e, hhd]; exact Vl.hd.1
      · have := lay_next_val (Ly.vfit w (hV1 hw)).2; have := (Ly.vfit w (hV1 hw)).1
        unfold P1.Aligned; rw [e]; omega
      · have := lay_prev_val (Ly.vfit w (hV1 hw)).2; have := (Ly.vfit w (hV1 hw)).1
        unfold P1.Aligned; rw [e]; omega
    · refine not_slotWd_of hP ?_
      rcases hb with e | ⟨w, hw, e | e⟩
      · rw [e, hhd]; exact hns _ (Or.inr (Or.inr rfl))
      · have := lay_next_val (Ly.vfit w (hV1 hw)).2
        exact nSl_v Ly (hV1 hw) (by rw [e]; omega) (by rw [e]; omega)
      · have := lay_prev_val (Ly.vfit w (hV1 hw)).2
        exact nSl_v Ly (hV1 hw) (by rw [e]; omega) (by rw [e]; omega)
  · obtain ⟨y0, hy0, hne, hc0⟩ := hcap1 w hw
    refine ⟨y0, hy0, ?_⟩
    have e0 := hEW y0 hy0 0#u64 off0
    have e8 := hEW y0 hy0 8#u64 off8
    rw [wordOf_zero] at e0
    simp [hne] at e0 e8
    rw [capV_of_words e0 e8, hSS.capV hy0]; exact hc0

end

end
end Fl4Proofs.P3.VirtJExtV2Cap
