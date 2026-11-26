/-
P3 (line mmuAD, gen 34): **the four `report_loop`s of `vcpu::report` at `JAtZV3`** (step 3 of gen 33's plan
toward `ReportJ3`).

Message lists are written `(List.range 30).map F` (`F : Nat → Word` the word of each MR); an overwrite of MR `k <
30` updates `F` at `k` (`v3_mrUpd_set`), an append extends the range (`v3_mrUpd_range`).

* **`JAtZV3.repLoop0`** / **`repLoop2`** (`report_loop0` / `report_loop2`, the same body): MR `i..29` appended,
  the exit record's word (`rdExit`) when `pending || saved`, else 0 (`exitMrN`): from the first `i` words to all 30.
* **`JAtZV3.repLoop1`** / **`repLoop3`**: MR `10 + j` overwritten by GPR `j` (`rdGpr`) for `j < 15` (`gprOv`).

At every step gen 34's `setMrJ3` (P3/JAtZV3MrJ) and the VCPU reads of P3/JAtZV3VRead at the current `JAtZV3` state
(the VCPU object is the spec's `vs` throughout: `jMrSt` changes only the thread's TCB and user memory).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3MrJ
import Fl4Proofs.P3.JAtZV3VRead
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- The word `loop0` writes at MR `j`: the exit record's when `b` (pending or saved), else 0. -/
def exitMrN (b : Bool) (vs : Fl4Spec.VcpuState) (j : Nat) : Fl4Spec.Word :=
  if h : j < 30 then (if b then vs.exit.mrs ⟨j, h⟩ else 0) else 0

/-- MR `i` after `loop1` wrote GPRs `0..n-1` into MR `10..` over `F0`. -/
def gprOv (vs : Fl4Spec.VcpuState) (F0 : Nat → Fl4Spec.Word) (n i : Nat) : Fl4Spec.Word :=
  if h : 10 ≤ i ∧ i < 10 + n ∧ i < 25 then vs.get Fl4Spec.virtKind (.gpr ⟨i - 10, by omega⟩) else F0 i

theorem v3_mrUpd_range (g : Nat → Fl4Spec.Word) (n : Nat) (w : Fl4Spec.Word) (hw : w = g n) :
    mrUpd ((List.range n).map g) n w = (List.range (n + 1)).map g := by
  unfold mrUpd
  rw [if_neg (by simp), List.range_succ, List.map_append, hw]
  rfl

theorem v3_mrUpd_set (F : Nat → Fl4Spec.Word) {n k : Nat} (hk : k < n) (w : Fl4Spec.Word) :
    mrUpd ((List.range n).map F) k w = (List.range n).map (fun i => if i = k then w else F i) := by
  unfold mrUpd
  rw [if_pos (by simp; omega)]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases e : i = k
  · subst e; simp
  · simp [e, Ne.symm e]

theorem v3_map_congr {F G : Nat → Fl4Spec.Word} (n : Nat) (h : ∀ i < n, F i = G i) :
    (List.range n).map F = (List.range n).map G :=
  List.map_congr_left (fun i hi => h i (List.mem_range.1 hi))

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}
variable {σ0 : Fl4Spec.State Unit} {t : U64} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef} {rw : U64}

theorem v3_kv {ms : List Fl4Spec.Word} {v : U64} {vs : Fl4Spec.VcpuState}
    (hkv : σ0.kheap v.bv = some (.archObj (.vcpu vs))) (hvt : v.bv ≠ t.bv) :
    (jMrSt σ0 t.bv x0 pb ms).kheap v.bv = some (.archObj (.vcpu vs)) := by
  rw [jMrSt_other _ _ _ _ _ hvt]; exact hkv

theorem v3_exit_off {j i1 i2 : U64} (hlt : j.val < 30) (hi1 : i1.val = j.val * 8) (hi2 : i2.val = 20992 + i1.val) :
    i2.val = 20992 + 8 * j.val := by omega

set_option maxHeartbeats 8000000 in
/-- **`report_loop0` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.repLoop0 (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p)
    (hb : JBufR Z.B rw pb) {v : U64} {pending saved : Bool} {vs : Fl4Spec.VcpuState}
    (hv : (pending || saved) = true → v ∈ V ∧ σ0.kheap v.bv = some (.archObj (.vcpu vs)) ∧ v.bv ≠ t.bv)
    (i : U64) (hi : i.val ≤ 30) (s1 : S)
    (J1 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (jMrSt σ0 t.bv x0 pb ((List.range i.val).map (exitMrN (pending || saved) vs)))) :
    vcpu.report_loop0 st s1 t v pending rw saved i ⦃ s2 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (exitMrN (pending || saved) vs))) ⦄ := by
  unfold vcpu.report_loop0
  have hE : vcpu.EXIT.val = 20992 := by unfold vcpu.EXIT; rfl
  have hR : vcpu.REGS.val = 20736 := by unfold vcpu.REGS; rfl
  apply loop.spec_decr_nat (measure := fun y : S × U64 => 30 - y.2.val)
    (inv := fun y => y.2.val ≤ 30 ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
      (jMrSt σ0 t.bv x0 pb ((List.range y.2.val).map (exitMrN (pending || saved) vs))))
  · rintro ⟨s2, j⟩ ⟨hj, J2⟩
    try simp only at hj J2
    unfold vcpu.report_loop0.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < 30 := by
        first | (simpa [vcpu.NUM_MRS] using hlt) | scalar_tac | (unfold vcpu.NUM_MRS at hlt; scalar_tac)
      have hlen : ((List.range j.val).map (exitMrN (pending || saved) vs)).length = j.val := by simp
      split
      · rename_i hp
        obtain ⟨hvV, hkv, hvt⟩ := hv (by rw [hp]; rfl)
        step as ⟨i1, hi1⟩
        try simp only [vcpu.EXIT]
        step as ⟨i2, hi2⟩
        rw [v3_get_eq, bind_ok]
        have hw := J2.rdExit hvV (v3_kv hkv hvt) i2 ⟨j.val, hlt'⟩ (by first | omega | scalar_tac | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega) | (simp_all; omega))
        refine WP.spec_bind (setMrJ3 J2 hr hq hb j (by rw [hlen]) (by rw [hlen]; omega) _) ?_
        rintro ⟨_, s3⟩ J3
        try simp only [uncurry_apply_pair]
        step as ⟨j1, hj1⟩
        have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
        refine ⟨by omega, ?_, by omega⟩
        have e := v3_mrUpd_range (exitMrN (pending || saved) vs) j.val (L.mem s2 (core.num.U64.wrapping_add v i2)).bv
          (by rw [hw]; simp [exitMrN, hlt', hp])
        rw [hj1', ← e]; exact J3
      · rename_i hp
        split
        · rename_i hs
          obtain ⟨hvV, hkv, hvt⟩ := hv (by rw [hs]; simp)
          step as ⟨i1, hi1⟩
          try simp only [vcpu.EXIT]
          step as ⟨i2, hi2⟩
          rw [v3_get_eq, bind_ok]
          have hw := J2.rdExit hvV (v3_kv hkv hvt) i2 ⟨j.val, hlt'⟩ (by first | omega | scalar_tac | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega) | (simp_all; omega))
          refine WP.spec_bind (setMrJ3 J2 hr hq hb j (by rw [hlen]) (by rw [hlen]; omega) _) ?_
          rintro ⟨_, s3⟩ J3
          try simp only [uncurry_apply_pair]
          step as ⟨j1, hj1⟩
          have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
          refine ⟨by omega, ?_, by omega⟩
          have e := v3_mrUpd_range (exitMrN (pending || saved) vs) j.val (L.mem s2 (core.num.U64.wrapping_add v i2)).bv
            (by rw [hw]; simp [exitMrN, hlt', hs])
          rw [hj1', ← e]; exact J3
        · rename_i hs
          refine WP.spec_bind (setMrJ3 J2 hr hq hb j (by rw [hlen]) (by rw [hlen]; omega) _) ?_
          rintro ⟨_, s3⟩ J3
          try simp only [uncurry_apply_pair]
          step as ⟨j1, hj1⟩
          have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
          refine ⟨by omega, ?_, by omega⟩
          have e := v3_mrUpd_range (exitMrN (pending || saved) vs) j.val (0#u64 : U64).bv
            (by simp [exitMrN, hlt', hs, hp] <;> rfl)
          rw [hj1', ← e]; exact J3
    · rename_i hge
      have h30 : j.val = 30 := by
        have : ¬ j.val < 30 := by
          intro h; apply hge
          first | (simpa [vcpu.NUM_MRS] using h) | scalar_tac | (unfold vcpu.NUM_MRS; scalar_tac)
        omega
      rw [h30] at J2
      exact (WP.spec_ok _).2 J2
  · exact ⟨hi, J1⟩


set_option maxHeartbeats 8000000 in
/-- **`report_loop2` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.repLoop2 (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p)
    (hb : JBufR Z.B rw pb) {v : U64} {pending saved : Bool} {vs : Fl4Spec.VcpuState}
    (hv : (pending || saved) = true → v ∈ V ∧ σ0.kheap v.bv = some (.archObj (.vcpu vs)) ∧ v.bv ≠ t.bv)
    (i : U64) (hi : i.val ≤ 30) (s1 : S)
    (J1 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (jMrSt σ0 t.bv x0 pb ((List.range i.val).map (exitMrN (pending || saved) vs)))) :
    vcpu.report_loop2 st s1 t v pending rw saved i ⦃ s2 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (exitMrN (pending || saved) vs))) ⦄ := by
  unfold vcpu.report_loop2
  have hE : vcpu.EXIT.val = 20992 := by unfold vcpu.EXIT; rfl
  have hR : vcpu.REGS.val = 20736 := by unfold vcpu.REGS; rfl
  apply loop.spec_decr_nat (measure := fun y : S × U64 => 30 - y.2.val)
    (inv := fun y => y.2.val ≤ 30 ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
      (jMrSt σ0 t.bv x0 pb ((List.range y.2.val).map (exitMrN (pending || saved) vs))))
  · rintro ⟨s2, j⟩ ⟨hj, J2⟩
    try simp only at hj J2
    unfold vcpu.report_loop2.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < 30 := by
        first | (simpa [vcpu.NUM_MRS] using hlt) | scalar_tac | (unfold vcpu.NUM_MRS at hlt; scalar_tac)
      have hlen : ((List.range j.val).map (exitMrN (pending || saved) vs)).length = j.val := by simp
      split
      · rename_i hp
        obtain ⟨hvV, hkv, hvt⟩ := hv (by rw [hp]; rfl)
        step as ⟨i1, hi1⟩
        try simp only [vcpu.EXIT]
        step as ⟨i2, hi2⟩
        rw [v3_get_eq, bind_ok]
        have hw := J2.rdExit hvV (v3_kv hkv hvt) i2 ⟨j.val, hlt'⟩ (by first | omega | scalar_tac | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega) | (simp_all; omega))
        refine WP.spec_bind (setMrJ3 J2 hr hq hb j (by rw [hlen]) (by rw [hlen]; omega) _) ?_
        rintro ⟨_, s3⟩ J3
        try simp only [uncurry_apply_pair]
        step as ⟨j1, hj1⟩
        have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
        refine ⟨by omega, ?_, by omega⟩
        have e := v3_mrUpd_range (exitMrN (pending || saved) vs) j.val (L.mem s2 (core.num.U64.wrapping_add v i2)).bv
          (by rw [hw]; simp [exitMrN, hlt', hp])
        rw [hj1', ← e]; exact J3
      · rename_i hp
        split
        · rename_i hs
          obtain ⟨hvV, hkv, hvt⟩ := hv (by rw [hs]; simp)
          step as ⟨i1, hi1⟩
          try simp only [vcpu.EXIT]
          step as ⟨i2, hi2⟩
          rw [v3_get_eq, bind_ok]
          have hw := J2.rdExit hvV (v3_kv hkv hvt) i2 ⟨j.val, hlt'⟩ (by first | omega | scalar_tac | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega) | (simp_all; omega))
          refine WP.spec_bind (setMrJ3 J2 hr hq hb j (by rw [hlen]) (by rw [hlen]; omega) _) ?_
          rintro ⟨_, s3⟩ J3
          try simp only [uncurry_apply_pair]
          step as ⟨j1, hj1⟩
          have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
          refine ⟨by omega, ?_, by omega⟩
          have e := v3_mrUpd_range (exitMrN (pending || saved) vs) j.val (L.mem s2 (core.num.U64.wrapping_add v i2)).bv
            (by rw [hw]; simp [exitMrN, hlt', hs])
          rw [hj1', ← e]; exact J3
        · rename_i hs
          refine WP.spec_bind (setMrJ3 J2 hr hq hb j (by rw [hlen]) (by rw [hlen]; omega) _) ?_
          rintro ⟨_, s3⟩ J3
          try simp only [uncurry_apply_pair]
          step as ⟨j1, hj1⟩
          have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
          refine ⟨by omega, ?_, by omega⟩
          have e := v3_mrUpd_range (exitMrN (pending || saved) vs) j.val (0#u64 : U64).bv
            (by simp [exitMrN, hlt', hs, hp] <;> rfl)
          rw [hj1', ← e]; exact J3
    · rename_i hge
      have h30 : j.val = 30 := by
        have : ¬ j.val < 30 := by
          intro h; apply hge
          first | (simpa [vcpu.NUM_MRS] using h) | scalar_tac | (unfold vcpu.NUM_MRS; scalar_tac)
        omega
      rw [h30] at J2
      exact (WP.spec_ok _).2 J2
  · exact ⟨hi, J1⟩


theorem v3_gprOv_succ (vs : Fl4Spec.VcpuState) (F0 : Nat → Fl4Spec.Word) {n : Nat} (hn : n < 15) (k : Nat)
    (w : Fl4Spec.Word) (hw : w = vs.get Fl4Spec.virtKind (.gpr ⟨n, hn⟩)) :
    (if k = 10 + n then w else gprOv vs F0 n k) = gprOv vs F0 (n + 1) k := by
  unfold gprOv
  by_cases e : k = 10 + n
  · subst e
    rw [if_pos rfl, dif_pos (by omega), hw]
    exact congrArg (fun i => vs.get Fl4Spec.virtKind (.gpr i)) (Fin.ext (by simp))
  · rw [if_neg e]
    by_cases h1 : 10 ≤ k ∧ k < 10 + n ∧ k < 25
    · rw [dif_pos h1, dif_pos (by omega)]
    · rw [dif_neg h1, dif_neg (by omega)]

set_option maxHeartbeats 8000000 in
/-- **`report_loop1` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.repLoop1 (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p)
    (hb : JBufR Z.B rw pb) {v : U64} {vs : Fl4Spec.VcpuState} (hvV : v ∈ V)
    (hkv : σ0.kheap v.bv = some (.archObj (.vcpu vs))) (hvt : v.bv ≠ t.bv) (F0 : Nat → Fl4Spec.Word)
    (i : U64) (hi : i.val ≤ 15) (s1 : S)
    (J1 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs F0 i.val)))) :
    vcpu.report_loop1 st s1 t v rw i ⦃ s2 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs F0 15))) ⦄ := by
  unfold vcpu.report_loop1
  have hE : vcpu.EXIT.val = 20992 := by unfold vcpu.EXIT; rfl
  have hR : vcpu.REGS.val = 20736 := by unfold vcpu.REGS; rfl
  apply loop.spec_decr_nat (measure := fun y : S × U64 => 15 - y.2.val)
    (inv := fun y => y.2.val ≤ 15 ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs F0 y.2.val))))
  · rintro ⟨s2, j⟩ ⟨hj, J2⟩
    try simp only at hj J2
    unfold vcpu.report_loop1.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < 15 := by first | scalar_tac | (simpa using hlt)
      have hlen : ((List.range 30).map (gprOv vs F0 j.val)).length = 30 := by simp
      step as ⟨k, hk⟩
      step as ⟨i1, hi1⟩
      try simp only [vcpu.REGS]
      step as ⟨i2, hi2⟩
      rw [v3_get_eq, bind_ok]
      have hk' : k.val = 10 + j.val := by first | omega | (simp at hk; omega)
      have hw := J2.rdGpr hvV (v3_kv hkv hvt) i2 ⟨j.val, hlt'⟩ (by first | omega | scalar_tac | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega) | (simp_all; omega))
      refine WP.spec_bind (setMrJ3 J2 hr hq hb k (by rw [hlen]; omega) (by rw [hlen]; omega) _) ?_
      rintro ⟨_, s3⟩ J3
      try simp only [uncurry_apply_pair]
      step as ⟨j1, hj1⟩
      have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
      refine ⟨by omega, ?_, by omega⟩
      rw [v3_mrUpd_set _ (by omega : k.val < 30), hk'] at J3
      have e : (List.range 30).map (fun m => if m = 10 + j.val then (L.mem s2 (core.num.U64.wrapping_add v i2)).bv
          else gprOv vs F0 j.val m) = (List.range 30).map (gprOv vs F0 (j.val + 1)) :=
        v3_map_congr 30 fun m _ => v3_gprOv_succ vs F0 hlt' m _ hw
      rw [hj1', ← e]
      exact J3
    · rename_i hge
      have h15 : j.val = 15 := by
        have : ¬ j.val < 15 := by intro h; apply hge; first | scalar_tac | simpa using h
        omega
      rw [h15] at J2
      exact (WP.spec_ok _).2 J2
  · exact ⟨hi, J1⟩

set_option maxHeartbeats 8000000 in
/-- **`report_loop3` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.repLoop3 (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p)
    (hb : JBufR Z.B rw pb) {v : U64} {vs : Fl4Spec.VcpuState} (hvV : v ∈ V)
    (hkv : σ0.kheap v.bv = some (.archObj (.vcpu vs))) (hvt : v.bv ≠ t.bv) (F0 : Nat → Fl4Spec.Word)
    (i : U64) (hi : i.val ≤ 15) (s1 : S)
    (J1 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs F0 i.val)))) :
    vcpu.report_loop3 st s1 t v rw i ⦃ s2 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s2 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs F0 15))) ⦄ := by
  unfold vcpu.report_loop3
  have hE : vcpu.EXIT.val = 20992 := by unfold vcpu.EXIT; rfl
  have hR : vcpu.REGS.val = 20736 := by unfold vcpu.REGS; rfl
  apply loop.spec_decr_nat (measure := fun y : S × U64 => 15 - y.2.val)
    (inv := fun y => y.2.val ≤ 15 ∧ JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D y.1 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (gprOv vs F0 y.2.val))))
  · rintro ⟨s2, j⟩ ⟨hj, J2⟩
    try simp only at hj J2
    unfold vcpu.report_loop3.body
    dsimp only
    split
    · rename_i hlt
      have hlt' : j.val < 15 := by first | scalar_tac | (simpa using hlt)
      have hlen : ((List.range 30).map (gprOv vs F0 j.val)).length = 30 := by simp
      step as ⟨k, hk⟩
      step as ⟨i1, hi1⟩
      try simp only [vcpu.REGS]
      step as ⟨i2, hi2⟩
      rw [v3_get_eq, bind_ok]
      have hk' : k.val = 10 + j.val := by first | omega | (simp at hk; omega)
      have hw := J2.rdGpr hvV (v3_kv hkv hvt) i2 ⟨j.val, hlt'⟩ (by first | omega | scalar_tac | (simp at hi2; omega) | (simp at hi1; omega) | (simp at hi2 hi1; omega) | (simp_all; omega))
      refine WP.spec_bind (setMrJ3 J2 hr hq hb k (by rw [hlen]; omega) (by rw [hlen]; omega) _) ?_
      rintro ⟨_, s3⟩ J3
      try simp only [uncurry_apply_pair]
      step as ⟨j1, hj1⟩
      have hj1' : j1.val = j.val + 1 := by first | omega | (simp at hj1; omega)
      refine ⟨by omega, ?_, by omega⟩
      rw [v3_mrUpd_set _ (by omega : k.val < 30), hk'] at J3
      have e : (List.range 30).map (fun m => if m = 10 + j.val then (L.mem s2 (core.num.U64.wrapping_add v i2)).bv
          else gprOv vs F0 j.val m) = (List.range 30).map (gprOv vs F0 (j.val + 1)) :=
        v3_map_congr 30 fun m _ => v3_gprOv_succ vs F0 hlt' m _ hw
      rw [hj1', ← e]
      exact J3
    · rename_i hge
      have h15 : j.val = 15 := by
        have : ¬ j.val < 15 := by intro h; apply hge; first | scalar_tac | simpa using h
        omega
      rw [h15] at J2
      exact (WP.spec_ok _).2 J2
  · exact ⟨hi, J1⟩

end

end

end Fl4Proofs.P3
