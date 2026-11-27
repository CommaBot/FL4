/-
# P2 (line mmuAD, gen 12): `InsTP` walk tools; the PageMap prefix (`insT_entR` for `R.invBodyPmG`)

* `insTP_gstep`: `MmuADStep.insT_gstep` for `InsTP` with a done set `D` of `G` words: a call run alike on a store
  guarded off `G` keeps `D`;
* `insTP_iteR`, `insTP_liftRR`: `insT_ite` / `insT_liftR` with the run hypothesis;
* `insTP_of_insTF`: an `InsT` run storing into no `G` word (`NP := False`) is `InsTP` from any done set of `G` words;
* **`insTP_entPm`**: `MmuADEnt.insT_entR`'s walk (copied) for `R.invBodyPmG` / `R.invTailPmG` with the rest
  `E2EP.pmRest` (P2/InvPmRoC.lean), for `InsTP … Set.univ ∅`.

No premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.MmuADEnt
import Fl4Proofs.P2.MmuADPm
import Fl4Proofs.P2.InvPmRoD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField oAFFINITY)
open Fl4Proofs.P2.E2E (InsT InsTP insTP_sbind insTP_of_within dU_nG)

section tools
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {G : U64 → Prop} {Q : U64 → U64 → Prop}
  {NP User : U64 → Prop} {E : Set U64}

/-- **A call run alike on a store guarded off `G` keeps the done set.** -/
theorem insTP_gstep {X Y : Type} {D : Set U64} (hGU : ∀ x, G x → ¬ User x) (hDG : ∀ x ∈ D, G x)
    {R0 W0 : U64 → Prop} (hR0 : ∀ q, R0 q → ¬ G q) (hW0 : ∀ q, W0 q → ¬ G q)
    {p : SProg X} {k : X → SProg Y} {s : S} {a : A} {r' : Y × S × A}
    (h : interp st ar (p.sbind k) s a = ok r')
    (hg : ∀ r, interp st ar p s a = ok r → interp (guard st R0 W0) ar p s a = ok r)
    (hk : ∀ r, interp st ar p s a = ok r → interp st ar (k r.1) r.2.1 r.2.2 = ok r' →
      InsTP st ar G Q NP User E D (k r.1) r.2.1 r.2.2) :
    InsTP st ar G Q NP User E D (p.sbind k) s a := by
  rw [interp_sbind] at h
  obtain ⟨r0, h0, hk0⟩ := bind_eq_ok' h
  have w := (interp_guard p s a r0 (hg r0 h0)).2
  refine insTP_sbind p k D s a (insTP_of_within hGU hDG subset_rfl p s a
    (Within.mono (fun b hb => hR0 b hb) (fun b hb => Or.inr (hW0 b hb)) p s a w)) fun r hr => ?_
  rw [h0] at hr
  cases ok_inj_ff hr
  exact hk r0 h0 hk0

/-- A pure step keeps the run hypothesis. -/
theorem insTP_liftRR {X Y : Type} {D : Set U64} {e : Result X} {k : X → SProg Y} {s : S} {a : A}
    {r' : Y × S × A} (h : interp st ar ((SProg.liftR e).sbind k) s a = ok r')
    (hk : ∀ v, e = ok v → interp st ar (k v) s a = ok r' → InsTP st ar G Q NP User E D (k v) s a) :
    InsTP st ar G Q NP User E D ((SProg.liftR e).sbind k) s a := by
  unfold SProg.liftR at h ⊢
  by_cases hx : ∃ v, e = ok v
  · rw [dif_pos hx] at h ⊢
    simp only [SProg.sbind] at h ⊢
    exact hk _ hx.choose_spec h
  · rw [dif_neg hx]
    split <;> simp only [SProg.sbind, InsTP]

/-- An `if` on a pure condition keeps the run hypothesis. -/
theorem insTP_iteR {X : Type} {D : Set U64} {c : Prop} [Decidable c] {p q : SProg X} {s : S} {a : A}
    {r' : X × S × A} (h : interp st ar (if c then p else q) s a = ok r')
    (hp : c → interp st ar p s a = ok r' → InsTP st ar G Q NP User E D p s a)
    (hq : ¬ c → interp st ar q s a = ok r' → InsTP st ar G Q NP User E D q s a) :
    InsTP st ar G Q NP User E D (if c then p else q) s a := by
  by_cases hc : c
  · rw [if_pos hc] at h ⊢; exact hp hc h
  · rw [if_neg hc] at h ⊢; exact hq hc h

/-- **An `InsT` run storing into no `G` word is `InsTP` from any done set of `G` words inside `E`.** -/
theorem insTP_of_insTF {X : Type} (hGU : ∀ x, G x → ¬ User x) (p : SProg X) : ∀ (D : Set U64) (s : S) (a : A),
    (∀ x ∈ D, G x) → D ⊆ E → InsT st ar G Q (fun _ => False) User p s a → InsTP st ar G Q NP User E D p s a := by
  induction p with
  | ret x => intro D s a _ hE _; simp only [InsTP]; exact hE
  | err e => intros; simp only [InsTP]
  | zero q n k ih => intros; simp only [InsTP]
  | clr q n k ih => intros; simp only [InsTP]
  | rd q k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]
    exact fun v hv => ⟨(h v hv).1, ih v D s a hD hE (h v hv).2⟩
  | rdp q k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]
    exact ⟨h.1, h.2.1, fun v hv => ih v D s a hD hE (h.2.2 v hv)⟩
  | wr q v k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]
    have hg : ¬ G q := fun hg => ((h.1 hg).resolve_right id) |> hGU q hg
    refine ⟨fun _ hq => hg (hD q hq), fun s' hs => ?_⟩
    rw [dU_nG hg]; exact ih D s' a hD hE (h.2 s' hs)
  | ksb k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]; exact fun v hv => ih v D s a hD hE (h v hv)
  | cpu k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]; exact fun v hv => ih v D s a hD hE (h v hv)
  | masks k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]; exact fun v hv => ih v D s a hD hE (h v hv)
  | arch op k ih =>
    intro D s a hD hE h; simp only [InsT] at h; simp only [InsTP]
    exact fun v a' hv => ih v D s a' hD hE (h v a' hv)

end tools

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **`InsTP` of an accepted PageMap run at its entry, up to the decode** (`insT_entR` copied). -/
theorem insTP_entPm (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {P : S → Prop}
    {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP User : U64 → Prop}
    (hGU : ∀ x, G x → ¬ User x) (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : ∀ s, P s → ∀ q, (IoRSR st K Locks s q ∨ IoWS (st := st) K Locks s q) → ¬ G q)
    (hSeen : ∀ s, P s → ∀ x, SeenW p x → IoRSR st K Locks s x)
    (hps : ∀ s, P s → IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hdo : ∀ s (a : A) info nx s1 s2 a1 buf length cap (r' : Bool × S × A), P s →
      (∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) →
      msg.msg_info st s (L.curW s) = ok info → InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf → obj.Slot.cap st p.slot s2 = ok cap →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
        else ok info.length) = ok length →
      interp st ar (E2EP.pmRest (L.curW s) info p buf length cap) s2 a1 = ok r' →
      InsTP st ar G Q NP User Set.univ ∅ (E2EP.pmRest (L.curW s) info p buf length cap) s2 a1) :
    ∀ s (a : A) r, P s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
      interp st ar (R.invBodyPmG number p) s a = ok r → InsTP st ar G Q NP User Set.univ ∅ (R.invBodyPmG number p) s a := by
  intro s a r hE hac h
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hPE s hE
  have hR0 : ∀ q, IoRSR st K Locks s q → ¬ G q := fun q hq => hG s hE q (Or.inl hq)
  have hW0 : ∀ q, IoWS (st := st) K Locks s q → ¬ G q := fun q hq => hG s hE q (Or.inr hq)
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  unfold R.invBodyPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the current thread
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [sched.cur_thread.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) s nC]
    exact h1
  replace h := hk
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok] at et
  have et' : t = L.curW s := (ok_inj_ff et).symm
  subst et'
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `MSG_INFO`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) s _
      (P.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1]
    exact h1
  replace h := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, emi, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_iteR h (fun _ _ => by simp only [InsTP, Set.empty_subset]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the flags
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [obj.Tcb.flags.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ s
      (P.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insTP_iteR h (fun _ _ => by simp only [InsTP, Set.empty_subset]) (fun _ h => ?_)
  refine insTP_iteR h (fun _ _ => by simp only [InsTP, Set.empty_subset]) (fun _ h => ?_)
  -- the tail
  unfold R.invTailPmG at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insTP_liftRR h (fun b _ h => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true]; simp only [InsTP, Set.empty_subset]
  rw [if_pos rfl] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `NEXT_IP`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.reg_eq] at h1 ⊢
    rw [obj.Tcb.reg.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ s _
      (P.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.reg_eq] at h1
  obtain ⟨nx, enx, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the `FAULT_IP` write
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ s
      _ _ (P.regR (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x1, es1, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ex1 : x1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [set_reg_ok'] at es1; exact (ok_inj_ff es1).symm
  have hNx1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRSR st K Locks s (L.nodeAt x1 (L.cpu x1) o) ∧ IoWS (st := st) K Locks s (L.nodeAt x1 (L.cpu x1) o) :=
    fun o h1 h2 => by
      rw [ex1, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]; exact P.ndR (Locks := Locks) o h1 h2
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `update_timestamp`
  have hct := hNx1 layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn := hNx1 layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.update_timestamp_eq] at h1 ⊢
    rw [sched.update_timestamp.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      ar x1 a hct.1 hct.2 hcn.1 hcn.2]
    exact h1
  replace h := hk
  rw [R.sched.update_timestamp_eq] at h1
  obtain ⟨⟨x2, a1⟩, eu, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have M := insT_hmidR (Locks := Locks) hA P h0 info nx x1 x2 a1 emi enx es1 eu
  have nd2 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) o) := fun o h1 h2 => by
    rw [M.c, nodeAt_of_ksb M.k]; exact (P.ndR (Locks := Locks) o h1 h2).1
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `cur_sc`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [sched.cur_sc.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h := hk
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, ecs, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have ec : csc = L.cscW x2 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecs; exact (ok_inj_ff ecs).symm
  subst ec
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `action`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i3, ei3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_iteR h (fun _ _ => by simp only [InsTP, Set.empty_subset]) (fun hi3 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `yield_to`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Tcb.yield_to_eq] at h1 ⊢
    rw [obj.Tcb.yield_to.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) _ x2
      M.yld]
    exact h1
  replace h := hk
  rw [R.obj.Tcb.yield_to_eq] at h1
  obtain ⟨i4, ei4, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_iteR h (fun _ _ => by simp only [InsTP, Set.empty_subset]) (fun hi4 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `consumed`, `sufficient`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sched.consumed_eq] at h1 ⊢
    rw [sched.consumed.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s)) x2
      (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
    exact h1
  replace h := hk
  rw [R.sched.consumed_eq] at h1
  obtain ⟨i5, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.sporadic.sufficient_eq] at h1 ⊢
    rw [sporadic.sufficient.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      ar x2 a1 _ i5 M.rh]
    exact h1
  replace h := hk
  rw [R.sporadic.sufficient_eq] at h1
  obtain ⟨b1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_iteR h (fun _ h => ?_) (fun _ _ => by simp only [InsTP, Set.empty_subset])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `schedulable_here`
  have htm : IoRSR st K Locks s (tmA (L := L) x2) := by
    show IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.TIMER_MIN)
    exact nd2 _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : IoRSR st K Locks s (rhA (L := L) x2) := by
    show IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.RELEASE_HEAD)
    exact nd2 _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have hct2 : IoRSR st K Locks s (ctA (L := L) x2) := by
    show IoRSR st K Locks s (L.nodeAt x2 (L.cpu x2) layout.node.CUR_TIME)
    exact nd2 _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
    rw [fastpath.schedulable_here.guard (gS := PathObl.guard st (IoRSR st K Locks s)
      (IoWS (st := st) K Locks s)) x2 _ hct2 htm hrh M.td M.rs M.dt M.cd M.af M.dom M.sc M.inq]
    exact h1
  replace h := hk
  rw [R.fastpath.schedulable_here_eq] at h1
  obtain ⟨b2, eb2, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_iteR h (fun hb2 h => ?_) (fun _ _ => by simp only [InsTP, Set.empty_subset])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `still_holds`
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.localinv.Plan.still_holds_eq] at h1 ⊢
    rw [still_holds_guard p x2 (fun w hw => hSeen s hE w hw)]
    exact h1
  replace h := hk
  rw [R.localinv.Plan.still_holds_eq] at h1
  obtain ⟨b3, eb3, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine insTP_iteR h (fun hb3 h => ?_) (fun _ _ => by simp only [InsTP, Set.empty_subset])
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the IPC buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      x2 false (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  replace h := hk
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨buf, ebuf, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  -- the length
  simp only [SProg.blk, ite_ret, SProg.sbind] at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the invoked slot's cap
  refine insTP_gstep hGU (fun x hx => absurd hx (Set.notMem_empty x)) hR0 hW0 h (fun r h1 => ?_) (fun r h1 hk => ?_)
  · rw [R.obj.Slot.cap_eq] at h1 ⊢
    rw [obj.Slot.cap.guard (gS := PathObl.guard st (IoRSR st K Locks s) (IoWS (st := st) K Locks s))
      p.slot x2 (hps s hE).1 (hps s hE).2]
    exact h1
  rw [R.obj.Slot.cap_eq] at h1
  obtain ⟨cap, ecap, rfl⟩ := bind_shape h1
  have hR := hk
  dsimp only at hR ⊢
  -- the decode onward
  simp only [bne_iff_ne, ne_eq, not_not] at hi3 hi4
  rw [hi3] at ei3
  rw [hi4] at ei4
  rw [hb2] at eb2
  rw [hb3] at eb3
  exact hdo s a info nx x1 x2 a1 buf _ cap _ hE ⟨sA, aA, h0⟩ emi ⟨enx, es1, eu, ei3, ei4, eb2, eb3⟩ ebuf ecap
    (by split <;> (try split) <;> rfl) hR

end walk

end Fl4Proofs.P2.PathObl
