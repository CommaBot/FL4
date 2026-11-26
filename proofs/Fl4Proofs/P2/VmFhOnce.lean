/-
# P2 (line p3mc, gen 8): the VM-fault tree at a store state whose fault handler is another core's reads each racy word once

`VmOnce.vm_once_alt`'s walk of `R.syscall.handle_vm_fault_local`, for the run at a state `x` agreeing with the entry
`s` only on a read set `Rd` (`VmFh.lean`; the certificate states of `ViewSafeReal.safe_tr_of_states`), with the
handler `d` (the head of the fault endpoint the entry's prefix state finds, in the receive state) off `x`'s core
(`VmFhOff`), and `Once` for **any** read set `Ro` holding `Rd` and `d`'s `AFFINITY`:

* **`vm_fh_once`**: the prefix and the fast path up to `Ep.head` read `Rd` words; then **one** read of `d`'s
  `REPLY_OBJ` (nothing touched before it); then either `false` or `schedulable_here d` reading `Rd` words and `d`'s
  `AFFINITY`, which answers `false`, and the run ends.

No premise: every fact about the state is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.VmFh
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **The run at a state with the handler off its core reads each racy word once** (module docstring). -/
theorem vm_fh_once {Rd Ro User : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b)
    (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q) {s x : S} (G : Ag st Rd s x)
    (rT : Rd (ctA (L := L) s)) (rN : Rd (cnA (L := L) s)) {a : A} {s1 : S} {a1e : A}
    (eu : sched.update_timestamp st ar s a = ok (s1, a1e)) (F : VmFhR st Rd s s1) (hFH : VmFhOff st ar s s1 x a)
    {sl ptr badge : U64} {x' y g gr : Bool}
    (hsl : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr))
    (hst : L.epState s1 ptr = obj.EP_RECV)
    (hAo : Ro (affA (L.mem s1 (epHeadA ptr))) ∧ ¬ User (affA (L.mem s1 (epHeadA ptr))))
    {addr code : U64} {r' : Bool × S × A}
    (h' : interp st ar (R.syscall.handle_vm_fault_local addr code) x a = ok r') :
    Once st ar Ro User ∅ ∅ (R.syscall.handle_vm_fault_local addr code) x a := by
  have hU : ∀ q, Rd q → ¬ User q := fun q hq => (hR0 q hq).2
  have hct : Rd (ctA (L := L) x) := by
    show Rd (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact rT
  have hcn : Rd (cnA (L := L) x) := by
    show Rd (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact rN
  -- the tree
  unfold R.syscall.handle_vm_fault_local at h' ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h' ⊢
  by_cases hd : (layout.NUM_DOMAINS != 1#u64) = true
  · rw [if_pos hd]; simp only [Once]
  rw [if_neg hd] at h' ⊢
  -- update_timestamp
  refine once_step hR0 hU (R.sched.update_timestamp_nz) h' (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st Rd Rd) ar x a hct hct hcn hcn]
    exact h1
  replace h2 := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x1, a1⟩, eu', rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
  obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := F.alt G1 (fun b hb => hb)
  have ecur1 := F.cur_alt G1
  have ecsc : L.cscW x1 = L.cscW s1 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [G1.node]; exact G1.m _ (F.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  have hs := G1.rdHead F.suf
  rw [← ecsc] at hs
  -- cur_sc
  refine once_step hR0 hU (R.sched.cur_sc_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st Rd Rd) x1
      (nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  have ec : csc = L.cscW x1 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  -- consumed
  refine once_step hR0 hU (R.sched.consumed_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st Rd Rd) x1
      (nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h2 := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨u, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  -- sufficient
  refine once_step hR0 hU (R.sporadic.sufficient_nz _ _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st Rd Rd)
      ar x1 a1 (L.cscW x1) u hs]
    exact h1
  replace h2 := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨⟨b, a2⟩, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  all_goals (first
    | (rw [if_neg Bool.false_ne_true]; simp only [Once]; done)
    | (rw [if_pos rfl] at h2 ⊢))
  -- cur_thread
  refine once_step hR0 hU (R.sched.cur_thread_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st Rd Rd) x1
      (nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))]
    exact h1
  replace h2 := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := by rw [← ecur1]; exact (ok_inj_ff et).symm
  subst et'
  -- the two pure steps and `vm_fault`'s fault value
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨i1, x2, a3⟩ := r
  obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢
  simp only [SProg.sbind] at h2 ⊢
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨f, x2, a3⟩ := r
  obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢
  -- the fast path
  unfold R.fastpath_vm.vm_fault at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h2 ⊢
  refine once_step hR0 hU (R.sched.action_nz) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st Rd Rd) x1
      (nd1 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h2 := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  split
  · simp only [Once]
  rename_i hi
  rw [if_neg hi] at h2
  refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
    (fun r h1 hk Wd _ => ?_)
  replace h2 := hk
  obtain ⟨sl', x2, a3⟩ := r
  obtain ⟨esl, e1, e2⟩ := interp_liftR_ok h1
  dsimp only at e1 e2
  subst x2 a3
  dsimp only at h2 ⊢ esl
  rw [hsl] at esl
  have e := ok_inj_ff esl
  subst e
  obtain ⟨r0, r8⟩ := F.sl sl hsl
  refine once_step hR0 hU (R.obj.Slot.cap_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st Rd Rd)
      sl x1 r0 r8]
    exact h1
  replace h2 := hk
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨c, ec, rfl⟩ := bind_shape h1
  rw [cap_congr_ag G1 r0 r8, hcap] at ec
  have e := ok_inj_ff ec
  subst e
  dsimp only at h2 ⊢
  obtain ⟨rts, rhd⟩ := F.ep sl ptr badge x' y g gr hsl hcap
  -- `grant`, else `grant_reply`, leads to the same walk
  cases g
  rw [if_neg Bool.false_ne_true] at h2 ⊢
  cases gr
  · rw [if_neg Bool.false_ne_true]; simp only [Once]
  rw [if_pos rfl] at h2 ⊢
  rotate_left
  rw [if_pos rfl] at h2 ⊢
  all_goals
      refine once_step hR0 hU (R.obj.Ep.state_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
      · rw [R.obj.Ep.state_eq] at h1 ⊢
        rw [obj.Ep.state.guard (gS := PathObl.guard st Rd Rd)
          ptr x1 rts]
        exact h1
      replace h2 := hk
      rw [R.obj.Ep.state_eq] at h1
      obtain ⟨i1, -, rfl⟩ := bind_shape h1
      dsimp only at h2 ⊢
      split
      · simp only [Once]
      rename_i hi1
      rw [if_neg hi1] at h2
      refine once_step hR0 hU (R.obj.Ep.head_nz _) h2 (fun r h1 => ?_) (fun r h1 hk Wd _ => ?_)
      · rw [R.obj.Ep.head_eq] at h1 ⊢
        rw [obj.Ep.head.guard (gS := PathObl.guard st Rd Rd)
          ptr x1 rhd]
        exact h1
      replace h2 := hk
      rw [R.obj.Ep.head_eq] at h1
      obtain ⟨d, ed, rfl⟩ := bind_shape h1
      dsimp only at h2 ⊢
      have hdd : d = L.mem s1 (epHeadA ptr) := by
        rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr)] at ed
        rw [← ok_inj_ff ed]; exact G1.m (epHeadA ptr) rhd
      have rA : (fun b => Rd b ∨ b = affA d) (affA d) := Or.inr rfl
      have hrem : L.mem x1 (affA d) ≠ L.cpu x1 := by
        rw [hdd]; exact hFH x1 a1 eu' sl ptr badge x' y _ _ hsl hcap hst
      have hAd : Ro (affA d) ∧ ¬ User (affA d) := by rw [hdd]; exact hAo
      have hR0d : ∀ q, (fun b => Rd b ∨ b = affA d) q → Ro q ∧ ¬ User q := by
        rintro q (hq | rfl)
        · exact hR0 q hq
        · exact hAd
      have hU0d : ∀ q, (fun b => Rd b ∨ b = affA d) q → ¬ User q := fun q hq => (hR0d q hq).2
      obtain ⟨nd2, dt2, cd2, -, tm2, rh2⟩ := F.alt G1 (R'' := fun b => Rd b ∨ b = affA d) (fun b hb => Or.inl hb)
      -- the reply word: its one read
      unfold R.obj.Tcb.reply_obj at h2 ⊢
      simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
      refine once_step hR0 hU (NoZero.liftR _) h2 (fun r h1 => by rw [interp_liftR_store _ st]; exact h1)
        (fun r h1 hk Wd _ => ?_)
      replace h2 := hk
      obtain ⟨o, x2, a3⟩ := r
      obtain ⟨-, e1, e2⟩ := interp_liftR_ok h1
      dsimp only at e1 e2
      subst x2 a3
      dsimp only at h2 ⊢
      simp only [SProg.sbind, SProg.read] at h2 ⊢
      simp only [interp] at h2
      obtain ⟨v0, hv0, h2⟩ := bok.mp h2
      refine once_rd_first hR0d hU0d _ _ (fun v => by nz_walk) Wd ∅ x1 a1 (Set.notMem_empty _) (fun v hv => ?_)
      rw [hv0] at hv
      have e := ok_inj_ff hv
      subst e
      split
      · exact ⟨_, interp_ret' _ _ _ _ _⟩
      rename_i hz0
      rw [if_neg hz0] at h2
      -- `schedulable_here d` answers `false`
      rw [interp_sbind] at h2 ⊢
      obtain ⟨⟨bh, x3, a4⟩, hh, h3⟩ := bind_eq_ok' h2
      have hh' := hh
      rw [R.fastpath.schedulable_here_eq] at hh'
      obtain ⟨bh', ebh, ebh2⟩ := bind_shape hh'
      cases ebh2
      have hfalse : bh = false := by
        cases bh
        · rfl
        · exact absurd (here_facts (L := L) ebh).aff hrem
      subst hfalse
      rw [R.fastpath.schedulable_here_eq, vm_here_guard (gS := PathObl.guard st (fun b => Rd b ∨ b = affA d) (fun b => Rd b ∨ b = affA d)) x1 d
          (nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
          (nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
          (nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
          tm2 rh2 dt2 cd2 rA (fun hl => absurd hl hrem), ebh]
      refine ⟨(false, x1, a1), ?_⟩
      first
        | rfl
        | simp only [bind_tc_ok, bind_ok, Bool.false_eq_true, ↓reduceIte, interp_ret']
end

end Fl4Proofs.P2.PathObl
