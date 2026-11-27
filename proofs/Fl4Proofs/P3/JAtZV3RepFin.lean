/-
P3 (line mmuAD, gen 34): **the last steps of `vcpu::report` at `JAtZV3`** (toward `ReportJ3`, gen 33 plan steps 5–6):

* **`JAtZV3.repFin`**: message info, badge, `FAULT_IP := NEXT_IP`, `Running` of a `runningVM` thread (gen 33's
  `regWr` thrice, this gen's `runVmJ`), ending at the spec's `repTail` (P3/JAtZV3RepSpec: FaultIP moved past the
  state change by `v3_stsAct_setReg`).
* **`JAtZV3.repFinP`**: `PENDING := 0` first (gen 33's `pendClr`, spec `VcpuState.reported`), message info 1,
  badge 0.
* `setMrJ3F`: gen 34's `setMrJ3` on a 30-word message `(List.range 30).map F`, overwriting MR `n`.
* `repFinF`, **`JAtZV3.repFinN`**: FL4's `finish_notification` (MR3 := the reason, MR4/6/25/26 := 0, MR5 := 0 unless
  vectoring, message info 0, the badge), with gen 32's [P] `ZvVirtAgree` for the backend.

Premise used: [P] `ZvVirtAgree arI` (P3/JAtZV3Vmcs, gen 32). No new named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3RepSpec
import Fl4Proofs.P3.JAtZV3RunVm
import Fl4Proofs.P3.JAtZV3RepLoop
import Fl4Proofs.P3.JAtZV3Regs
import Fl4Proofs.P3.JAtZV3Pend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- MR `i` after `finish_notification` over `F` (module docstring). -/
def repFinF (vec : Bool) (F : Nat → Fl4Spec.Word) : Nat → Fl4Spec.Word := fun i =>
  if i = 3 then Fl4Spec.vmNotifyReason Fl4Spec.virtKind
  else if i = 4 ∨ i = 6 ∨ i = 25 ∨ i = 26 then 0
  else if i = 5 ∧ vec = false then 0 else F i

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 8000000 in
/-- **Message info, badge, FaultIP, `Running`** (module docstring). -/
theorem JAtZV3.repFin (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x1 : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x1)) (hrs : x1.tcbState = .runningVM) (mi bd : U64) :
    (do
      let s4 ← obj.Tcb.set_reg st t s layout.reg.MSG_INFO mi
      let s5 ← obj.Tcb.set_reg st t s4 layout.reg.BADGE bd
      let next ← obj.Tcb.reg st t s5 layout.reg.NEXT_IP
      let s6 ← obj.Tcb.set_reg st t s5 layout.reg.FAULT_IP next
      sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => ∃ Lst' : U64 → List U64,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a (repTail σ t.bv x1 mi.bv bd.bv) ⦄ := by
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s t _ mi) ?_
  rintro s4 rfl
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t _ bd) ?_
  rintro s5 rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec _ t _) ?_
  rintro nx rfl
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ t _ _) ?_
  rintro s6 rfl
  have J4 := J.regWr ht hk Fl4Spec.msg_info_register mi
  rw [Endp.regIdx_msgInfo] at J4
  have hk4 : (Notif.updK σ t.bv (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv))).kheap t.bv =
      some (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv)) := by simp [Notif.updK]
  have J5 := J4.regWr ht hk4 Fl4Spec.badge_register bd
  rw [Endp.regIdx_badge] at J5
  have hk5 : (Notif.updK (Notif.updK σ t.bv (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv))) t.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv) Fl4Spec.badge_register bd.bv))).kheap t.bv =
      some (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv) Fl4Spec.badge_register bd.bv)) := by
    simp [Notif.updK]
  have B5 := J5.z2.zv.base
  have hnx := ((B5.xtop.irelK B5.ks B5.buf).1.toE.at_tcb ht hk5).regs .nextIP
  rw [show regIdx .nextIP = layout.reg.NEXT_IP by unfold layout.reg.NEXT_IP; rfl] at hnx
  have J6 := J5.regWr ht hk5 .faultIP (L.mem (L.wr (L.wr s (Endp.regA t layout.reg.MSG_INFO) mi)
    (Endp.regA t layout.reg.BADGE) bd) (Endp.regA t layout.reg.NEXT_IP))
  rw [← fault_ip_idx] at J6
  have hk6 := (by simp [Notif.updK] : (Notif.updK (Notif.updK (Notif.updK σ t.bv
      (.tcb (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv))) t.bv
      (.tcb (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv) Fl4Spec.badge_register bd.bv))) t.bv
      (.tcb (Notif.setReg (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv) Fl4Spec.badge_register bd.bv)
        .faultIP (L.mem (L.wr (L.wr s (Endp.regA t layout.reg.MSG_INFO) mi)
          (Endp.regA t layout.reg.BADGE) bd) (Endp.regA t layout.reg.NEXT_IP)).bv))).kheap t.bv =
      some (.tcb (Notif.setReg (Notif.setReg (Notif.setReg x1 Fl4Spec.msg_info_register mi.bv) Fl4Spec.badge_register bd.bv)
        .faultIP (L.mem (L.wr (L.wr s (Endp.regA t layout.reg.MSG_INFO) mi)
          (Endp.regA t layout.reg.BADGE) bd) (Endp.regA t layout.reg.NEXT_IP)).bv)))
  refine WP.spec_mono (J6.runVmJ ht hk6 hrs) fun s7 h7 => ?_
  obtain ⟨Lst', J7⟩ := h7
  refine ⟨Lst', ?_⟩
  unfold repTail
  rw [v3_stsAct_setReg]
  simp only [zv_updK_updK] at J7 ⊢
  rw [← hnx]
  exact J7

set_option maxHeartbeats 8000000 in
/-- **`PENDING := 0`, message info 1, badge 0, FaultIP, `Running`** (module docstring). -/
theorem JAtZV3.repFinP (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T)
    {x1 : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x1)) (hrs : x1.tcbState = .runningVM) {v : U64} (hv : v ∈ V)
    {vs : Fl4Spec.VcpuState} (hkv : σ.kheap v.bv = some (.archObj (.vcpu vs))) :
    (do
      let s8 ← vcpu.set st s v vcpu.PENDING 0#u64
      let s9 ← obj.Tcb.set_reg st t s8 layout.reg.MSG_INFO 1#u64
      let s10 ← obj.Tcb.set_reg st t s9 layout.reg.BADGE 0#u64
      let ip1 ← obj.Tcb.reg st t s10 layout.reg.NEXT_IP
      let s11 ← obj.Tcb.set_reg st t s10 layout.reg.FAULT_IP ip1
      sched.set_thread_state st s11 t sched.TS_RUNNING) ⦃ s' => ∃ Lst' : U64 → List U64,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a
          (repTail (Notif.updK σ v.bv (.archObj (.vcpu vs.reported))) t.bv x1 (1#u64 : U64).bv (0#u64 : U64).bv) ⦄ := by
  have hvt : v.bv ≠ t.bv := fun e => by rw [e, hk] at hkv; cases hkv
  have hf := J.vfitV hv
  unfold vcpu.set
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s _ _) fun s8 e8 => ?_
  subst e8
  have hwp : (core.num.U64.wrapping_add v vcpu.PENDING).val = v.val + 20520 := by
    have hv' : vcpu.PENDING.val = 20520 := by unfold vcpu.PENDING; rfl
    have hs : UScalar.size UScalarTy.U64 = 2 ^ 64 := by simp [U64.size_def, U64.numBits]
    rw [core.num.U64.wrapping_add_val_eq, hv']
    first | omega | (rw [hs]; exact Nat.mod_eq_of_lt (by omega)) | (simp only [hs]; omega)
  have J8 := J.pendClr hv hwp hkv
  have hk8 : (Notif.updK σ v.bv (.archObj (.vcpu vs.reported))).kheap t.bv = some (.tcb x1) := by
    simp only [Notif.updK_kheap]; rw [Function.update_of_ne (Ne.symm hvt)]; exact hk
  exact J8.repFin ht hk8 hrs 1#u64 0#u64

variable {σ0 : Fl4Spec.State Unit} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef} {rw : U64}

/-- **`set_mr` of MR `n < 30` of a 30-word message** (`setMrJ3`, overwrite form). -/
theorem setMrJ3F {t : U64} {F : Nat → Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 t.bv x0 pb ((List.range 30).map F)))
    (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) (hb : JBufR Z.B rw pb)
    (i : U64) (n : Nat) (hn : i.val = n) (h30 : n < 30) (w : U64) :
    msg.set_mr st s t rw i w ⦃ r => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D r.2 a
      (jMrSt σ0 t.bv x0 pb ((List.range 30).map (fun k => if k = n then w.bv else F k))) ⦄ :=
  WP.spec_mono (setMrJ3 J hr hq hb i (by simp; omega) (by simp) w) fun r h => by
    rw [hn, v3_mrUpd_set F h30] at h; exact h

theorem v3_repX_state (x0 : Fl4Spec.Tcb) (ms : List Fl4Spec.Word) : (repX x0 ms).tcbState = x0.tcbState := rfl

set_option maxHeartbeats 16000000 in
/-- `finish_notification`'s writes after the reason word `r` is chosen (module docstring). -/
theorem JAtZV3.repFinN0 {t : U64} {F : Nat → Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 t.bv x0 pb ((List.range 30).map F)))
    (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) (hb : JBufR Z.B rw pb)
    (hrs : x0.tcbState = .runningVM) (badge : U64) (vec : Bool) (r : U64)
    (hrv : r.bv = Fl4Spec.vmNotifyReason Fl4Spec.virtKind) :
    (do
      let (_, s1) ← msg.set_mr st s t rw 3#u64 r
      let (_, s2) ← msg.set_mr st s1 t rw 4#u64 0#u64
      let s3 ←
        if vec
        then ok s2
        else
          do
          let (_, s4) ← msg.set_mr st s2 t rw 5#u64 0#u64
          ok s4
      let (_, s4) ← msg.set_mr st s3 t rw 6#u64 0#u64
      let (_, s5) ← msg.set_mr st s4 t rw 25#u64 0#u64
      let (_, s6) ← msg.set_mr st s5 t rw 26#u64 0#u64
      let s7 ← obj.Tcb.set_reg st t s6 layout.reg.MSG_INFO 0#u64
      let s8 ← obj.Tcb.set_reg st t s7 layout.reg.BADGE badge
      let next ← obj.Tcb.reg st t s8 layout.reg.NEXT_IP
      let s9 ← obj.Tcb.set_reg st t s8 layout.reg.FAULT_IP next
      sched.set_thread_state st s9 t sched.TS_RUNNING) ⦃ s' => ∃ Lst' : U64 → List U64,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a
          (repTail (jMrSt σ0 t.bv x0 pb ((List.range 30).map (repFinF vec F))) t.bv
            (repX x0 ((List.range 30).map (repFinF vec F))) (0#u64 : U64).bv badge.bv) ⦄ := by
  have h0 : (0#u64 : U64).bv = 0 := rfl
  refine WP.spec_bind (setMrJ3F J hr hq hb 3#u64 3 (by simp) (by omega) r) ?_
  rintro ⟨_, s1⟩ J1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (setMrJ3F J1 hr hq hb 4#u64 4 (by simp) (by omega) 0#u64) ?_
  rintro ⟨_, s2⟩ J2
  try simp only [uncurry_apply_pair]
  -- the tail after MR5, for either `vec`
  have tail : ∀ (s3 : S) (G : Nat → Fl4Spec.Word),
      (∀ k < 30, (if k = 26 then (0#u64 : U64).bv else if k = 25 then (0#u64 : U64).bv else
        if k = 6 then (0#u64 : U64).bv else G k) = repFinF vec F k) →
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a (jMrSt σ0 t.bv x0 pb ((List.range 30).map G)) →
      (do
        let (_, s4) ← msg.set_mr st s3 t rw 6#u64 0#u64
        let (_, s5) ← msg.set_mr st s4 t rw 25#u64 0#u64
        let (_, s6) ← msg.set_mr st s5 t rw 26#u64 0#u64
        let s7 ← obj.Tcb.set_reg st t s6 layout.reg.MSG_INFO 0#u64
        let s8 ← obj.Tcb.set_reg st t s7 layout.reg.BADGE badge
        let next ← obj.Tcb.reg st t s8 layout.reg.NEXT_IP
        let s9 ← obj.Tcb.set_reg st t s8 layout.reg.FAULT_IP next
        sched.set_thread_state st s9 t sched.TS_RUNNING) ⦃ s' => ∃ Lst' : U64 → List U64,
          JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a
            (repTail (jMrSt σ0 t.bv x0 pb ((List.range 30).map (repFinF vec F))) t.bv
              (repX x0 ((List.range 30).map (repFinF vec F))) (0#u64 : U64).bv badge.bv) ⦄ := by
    intro s3 G hG J3
    refine WP.spec_bind (setMrJ3F J3 hr hq hb 6#u64 6 (by simp) (by omega) 0#u64) ?_
    rintro ⟨_, s4⟩ J4
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (setMrJ3F J4 hr hq hb 25#u64 25 (by simp) (by omega) 0#u64) ?_
    rintro ⟨_, s5⟩ J5
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (setMrJ3F J5 hr hq hb 26#u64 26 (by simp) (by omega) 0#u64) ?_
    rintro ⟨_, s6⟩ J6
    try simp only [uncurry_apply_pair]
    rw [v3_map_congr 30 hG] at J6
    exact J6.repFin hr (jMrSt_rcv _ _ _ _ _) hrs 0#u64 badge
  cases vec with
  | true =>
    simp only [↓reduceIte, bind_ok]
    refine tail s2 _ (fun k hk => ?_) J2
    unfold repFinF
    rw [h0, hrv]
    by_cases e3 : k = 3 <;> by_cases e4 : k = 4 <;> by_cases e6 : k = 6 <;> by_cases e25 : k = 25 <;>
      by_cases e26 : k = 26 <;> simp_all
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (Pₘ := fun s3 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s3 a (jMrSt σ0 t.bv x0 pb
      ((List.range 30).map (fun k => if k = 5 then (0#u64 : U64).bv else
        if k = 4 then (0#u64 : U64).bv else if k = 3 then r.bv else F k)))) ?_ ?_
    · refine WP.spec_bind (setMrJ3F J2 hr hq hb 5#u64 5 (by simp) (by omega) 0#u64) ?_
      rintro ⟨_, s3⟩ J3
      try simp only [uncurry_apply_pair]
      exact (WP.spec_ok _).2 J3
    intro s3 J3
    refine tail s3 _ (fun k hk => ?_) J3
    unfold repFinF
    rw [h0, hrv]
    by_cases e3 : k = 3 <;> by_cases e4 : k = 4 <;> by_cases e5 : k = 5 <;> by_cases e6 : k = 6 <;>
      by_cases e25 : k = 25 <;> by_cases e26 : k = 26 <;> simp_all

/-- **`finish_notification` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.repFinN (hVA : ZvVirtAgree arI) {t : U64} {F : Nat → Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 t.bv x0 pb ((List.range 30).map F)))
    (hr : t ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) (hb : JBufR Z.B rw pb)
    (hrs : x0.tcbState = .runningVM) (badge : U64) (vec : Bool) :
    vcpu.finish_notification st arI s a t rw badge vec ⦃ s' => ∃ Lst' : U64 → List U64,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D s' a
          (repTail (jMrSt σ0 t.bv x0 pb ((List.range 30).map (repFinF vec F))) t.bv
            (repX x0 ((List.range 30).map (repFinF vec F))) (0#u64 : U64).bv badge.bv) ⦄ := by
  obtain ⟨i, hvi, hi⟩ := hVA a
  unfold vcpu.finish_notification
  rw [hvi, bind_ok]
  by_cases h2 : i = 2#u64
  · rw [if_pos h2]
    exact J.repFinN0 hr hq hb hrs badge vec 96#u64 (by
      rw [Fl4Spec.vmNotifyReason, if_pos (hi.1 h2)]; rfl)
  · rw [if_neg h2]
    exact J.repFinN0 hr hq hb hrs badge vec 1#u64 (by
      rw [Fl4Spec.vmNotifyReason, if_neg (fun h => h2 (hi.2 h))]; rfl)

end

end

end Fl4Proofs.P3
