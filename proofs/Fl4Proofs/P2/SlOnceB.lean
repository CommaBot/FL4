/-
# P2 (line slhuf, gen 7): `Once` at an alternative when the decided thread is homed elsewhere — ReplyRecv arm

When the ReplyRecv arm's replied thread `u` (the reply object's `TCB` word, a read-set word) is homed on
another core, its `STATE`, `FAULT_TYPE` and `SC` words are outside the read set. The walk: the prefix
(`sl_pre_once`) and the fast path's checks up to the reply's `TCB` word on `SlRS s ∧ NU K`; then the three
words of `u`, each read once (`u + 3328`, `u + 3376`, `u + 3464`: distinct), with the reply's `NEXT` word
between them on the guard; then `schedulable_here u` on the guard, which answers `false` (`u`'s `AFFINITY`
is not this core), and the run ends.

* `tch_sub_ins`, `wadd_ne`: the touched set after a read, distinct offsets from one base.
* **`rr_away_once`**: `Once` of the ReplyRecv fast path at such a state.
* **`sl_once_rr_away`**: `Once` of the entry's tree at every alternative, ReplyRecv arm, decided thread homed
  elsewhere.

No premises beyond the entry facts (`SlOF`).
-/
import Fl4Proofs.P2.SlOnceA
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

theorem tch_sub_ins {R U : U64 → Prop} {Wd T : Set U64} {q : U64} : E2E.tch R U Wd q T ⊆ insert q T := by
  unfold E2E.tch
  split
  · exact subset_rfl
  · exact Set.subset_insert _ _

theorem wadd_ne {u c1 c2 : U64} (h : c1.val ≠ c2.val) (h1 : c1.val < 4096) (h2 : c2.val < 4096) :
    core.num.U64.wrapping_add u c1 ≠ core.num.U64.wrapping_add u c2 := by
  intro e
  have e' := congrArg UScalar.val e
  have hb := u.hBounds
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at e' hb
  omega

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A} {Rd User : U64 → Prop}

set_option hygiene false in
/-- The end of `rr_away_once`'s walk (after the reply's `NEXT` word, either arm). -/
local macro "rr_away_rest" : tactic => `(tactic| (
    -- the third racy read: `SC`
    unfold R.obj.Tcb.sc at h2 ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
    refine once_liftR h2 (fun isc hisc h2 => ?_)
    rw [eq_ok_of_spec Fl4Proofs.P0.Consts.layout.tcb.SC.spec] at hisc
    have eisc := ok_inj_ff hisc
    subst eisc
    simp only [SProg.sbind, SProg.read] at h2 ⊢
    simp only [Once]
    refine ⟨fun _ hq => ?_, fun v hv => ?_⟩
    · rcases tch_sub_ins hq with e | hq2
      · exact wadd_ne (by simp) (by simp) (by simp) e
      · rcases tch_sub_ins hq2 with e | e
        · exact wadd_ne (by rw [st_val]; simp) (by simp) (by rw [st_val]; omega) e
        · exact Set.notMem_empty _ e
    simp only [interp] at h2
    obtain ⟨v', hv', h2⟩ := bok.mp h2
    have ev := ok_inj_ff (hv.symm.trans hv')
    subst ev
    refine once_liftR h2 (fun b3 _ h2 => ?_)
    by_cases hb3 : b3 = true
    · rw [if_pos hb3]; simp only [Once]
    rw [if_neg hb3] at h2 ⊢
    refine once_step (W0 := fun _ => False) hR0 hW0 (R.fastpath.schedulable_here_nz _) h2 (fun r h1 => ?_)
      (fun r h1 hk Wd _ => ?_)
    · rw [R.fastpath.schedulable_here_eq] at h1 ⊢
      rw [vm_here_guard (gS := PathObl.guard st R0 (fun _ => False)) X _
        (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
        (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
        (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
        D.tm D.rh D.dt D.cd rA (fun hl => absurd hl hrem)]
      exact h1
    replace h2 := hk
    rw [R.fastpath.schedulable_here_eq] at h1
    obtain ⟨b4, eb4, rfl⟩ := bind_shape h1
    dsimp only at h2 ⊢
    have hfalse : b4 = false := by
      cases b4
      · rfl
      · exact absurd (here_facts (L := L) eb4).aff hrem
    subst hfalse
    rw [if_neg Bool.false_ne_true]
    simp only [Once]))

set_option maxHeartbeats 8000000 in
/-- **The ReplyRecv fast path makes three racy reads, of distinct words, when the replied thread is homed
elsewhere** (module docstring). -/
theorem rr_away_once {R0 : U64 → Prop} (hR0 : ∀ q, R0 q → Rd q ∧ ¬ User q) {X : S} {a : A} {t rptr ep : U64}
    (D : RrDecT (L := L) R0 X t rptr ep)
    (hu : L.mem X (rTcbA rptr) ≠ 0#u64 →
      R0 (affA (L.mem X (rTcbA rptr))) ∧ L.mem X (affA (L.mem X (rTcbA rptr))) ≠ L.cpu X)
    {r' : Bool × S × A} (h : interp st ar (R.fastpath.reply_recv_found t rptr ep) X a = ok r') (Wd : Set U64) :
    Once st ar Rd User Wd ∅ (R.fastpath.reply_recv_found t rptr ep) X a := by
  have hW0 : ∀ q, (fun _ => False) q → ¬ User q := fun _ h => h.elim
  unfold R.fastpath.reply_recv_found at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret] at h ⊢
  -- action
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.sched.action_nz) h (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.action_eq] at h1 ⊢
    rw [sched.action.guard (gS := PathObl.guard st R0 (fun _ => False)) X
      (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
    exact h1
  replace h2 := hk
  rw [R.sched.action_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  by_cases hi : (i != sched.ACTION_RESUME_CURRENT) = true
  · rw [if_pos hi]; simp only [Once]
  rw [if_neg hi] at h2 ⊢
  -- is_schedulable
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.sched.is_schedulable_nz _) h2 (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.sched.is_schedulable_eq] at h1 ⊢
    rw [sched.is_schedulable.guard (gS := PathObl.guard st R0 (fun _ => False)) X t D.tSt D.tSc D.tMx D.tIq]
    exact h1
  replace h2 := hk
  rw [R.sched.is_schedulable_eq] at h1
  obtain ⟨b, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  by_cases hb : b = true
  swap
  · rw [if_neg hb]; simp only [Once]
  rw [if_pos hb] at h2 ⊢
  -- msg_info
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.msg.msg_info_nz _) h2 (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [msg.msg_info.guard (gS := PathObl.guard st R0 (fun _ => False)) X t D.tMi]
    exact h1
  replace h2 := hk
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  by_cases hx : (info.extra_caps != 0#u64) = true
  · rw [if_pos hx]; simp only [Once]
  rw [if_neg hx] at h2 ⊢
  by_cases hl : (info.label != 0#u64) = true
  · rw [if_pos hl]; simp only [Once]
  rw [if_neg hl] at h2 ⊢
  -- the reply's thread
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.obj.Reply.tcb_nz _) h2 (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Reply.tcb_eq] at h1 ⊢
    rw [obj.Reply.tcb.guard (gS := PathObl.guard st R0 (fun _ => False)) rptr X D.rRt]
    exact h1
  replace h2 := hk
  rw [R.obj.Reply.tcb_eq] at h1
  obtain ⟨u, eu, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  have hu1 := obj.Reply.tcb.blk (st := st) X rptr
  rw [eu, WP.spec_ok] at hu1
  subst hu1
  refine once_liftR h2 (fun b1 eb1 h2 => ?_)
  by_cases hb1 : b1 = true
  · rw [if_pos hb1]; simp only [Once]
  rw [if_neg hb1] at h2 ⊢
  obtain ⟨rA, hrem⟩ := hu (u_ne0 ⟨b1, eb1, hb1⟩)
  -- the first racy read: `STATE`
  unfold R.obj.Tcb.state at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h2 ⊢
  simp only [Once]
  refine ⟨fun _ hq => Set.notMem_empty _ hq, fun v hv => ?_⟩
  simp only [interp] at h2
  obtain ⟨v', hv', h2⟩ := bok.mp h2
  have ev := ok_inj_ff (hv.symm.trans hv')
  subst ev
  by_cases hs : (v != sched.TS_BLOCKED_ON_REPLY) = true
  · rw [if_pos hs]; simp only [Once]
  rw [if_neg hs] at h2 ⊢
  -- the second racy read: `FAULT_TYPE`
  unfold R.obj.Tcb.fault_type at h2 ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc] at h2 ⊢
  refine once_liftR h2 (fun ift hift h2 => ?_)
  rw [eq_ok_of_spec Fl4Proofs.P0.Consts.layout.tcb.FAULT_TYPE.spec] at hift
  have eift := ok_inj_ff hift
  subst eift
  simp only [SProg.sbind, SProg.read] at h2 ⊢
  simp only [Once]
  refine ⟨fun _ hq => ?_, fun v hv => ?_⟩
  · rcases tch_sub_ins hq with e | e
    · exact wadd_ne (by rw [st_val]; simp) (by simp) (by rw [st_val]; omega) e
    · exact Set.notMem_empty _ e
  simp only [interp] at h2
  obtain ⟨v', hv', h2⟩ := bok.mp h2
  have ev := ok_inj_ff (hv.symm.trans hv')
  subst ev
  by_cases hf : (v != fl4_abi.consts.fault.UnknownSyscall) = true
  · rw [if_pos hf]; simp only [Once]
  rw [if_neg hf] at h2 ⊢
  -- the reply's `NEXT`
  refine once_step (W0 := fun _ => False) hR0 hW0 (R.obj.Reply.next_nz _) h2 (fun r h1 => ?_)
    (fun r h1 hk Wd _ => ?_)
  · rw [R.obj.Reply.next_eq] at h1 ⊢
    rw [obj.Reply.next.guard (gS := PathObl.guard st R0 (fun _ => False)) X rptr D.rNx]
    exact h1
  replace h2 := hk
  rw [R.obj.Reply.next_eq] at h1
  obtain ⟨i4, -, rfl⟩ := bind_shape h1
  dsimp only at h2 ⊢
  by_cases hi4 : (i4 != 0#u64) = true
  · rw [if_pos hi4] at h2 ⊢
    refine once_step (W0 := fun _ => False) hR0 hW0 (R.obj.Reply.next_is_head_nz _) h2 (fun r h1 => ?_)
      (fun r h1 hk Wd _ => ?_)
    · rw [R.obj.Reply.next_is_head_eq] at h1 ⊢
      rw [obj.Reply.next_is_head.guard (gS := PathObl.guard st R0 (fun _ => False)) X rptr D.rNx]
      exact h1
    replace h2 := hk
    rw [R.obj.Reply.next_is_head_eq] at h1
    obtain ⟨b2, -, rfl⟩ := bind_shape h1
    dsimp only at h2 ⊢
    by_cases hb2 : b2 = true
    · rw [if_pos hb2]; simp only [Once]
    rw [if_neg hb2] at h2 ⊢
    rr_away_rest
  · rw [if_neg hi4] at h2 ⊢
    rr_away_rest

end

section alt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`Once` at an alternative, ReplyRecv arm, decided thread homed elsewhere** (module docstring). -/
theorem sl_once_rr_away (hA : P0.ArchTotal ar) {s s' : S} {a : A} {rp ep : U64}
    (F : SlOF (st := st) ar K Locks m0 n (rp, ep) Cs Ω Sg Ac s)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (hS : ¬ SlTrap st s) (hh : L.mem s (affA (slThr st rp s)) ≠ L.cpu s)
    {r' : Bool × S × A} (h : interp st ar (R.syscall.handle_syscall_local n (rp, ep)) s' a = ok r') :
    Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n (rp, ep)) s' a := by
  have E := F.E
  have B := F.B
  have hX := B.regionOKX
  have I := F.I
  have hcur := sl_alt_cur F.P.preG Al
  have hTr := slTrap_alt F.P.preG.fl Al hcur
  have hN' : NodePlaced st K.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  refine sl_pre_once (R0 := SlRN (st := st) K Locks s) (W0 := NU K) (fun q hq => ⟨hq.1, hq.2.2⟩)
    (fun q hq => hq.2) hA E.hT hN' hc' (sl_alt_preDec ar F Al) (sl_alt_hhd ar hA F Al) h
    (fun hS' => absurd (hTr.1 hS') hS) ?_
  intro _ X' a1' a2 LP' h' Wd
  obtain ⟨X, LP, hag, hk, hc⟩ := sl_alt_pre ar hA F Al LP'
  have hag' : ∀ b, SlRN (st := st) K Locks s b → L.mem X' b = L.mem X b := fun b hb => hag b hb.1
  have DT : RrDecT (L := L) (SlRN (st := st) K Locks s) X' (L.curW s) rp ep :=
    RrDecT.congr hk hc hag' (RrDecT.meet (F.D.rT hS a X a1' LP) (RrDec.toT (rrDec_nu ar hA F hS LP)))
  rw [hcur] at h' ⊢
  refine rr_away_once (fun q hq => ⟨hq.1, hq.2.2⟩) DT ?_ h' Wd
  intro hu0
  have DT0 := F.D.rT hS a X a1' LP
  have e1 : L.mem X' (rTcbA rp) = slThr st rp s := by
    rw [hag _ DT0.rRt]; exact slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP
  rw [e1] at hu0 ⊢
  have lv := slLive_rr (st := st) hS hu0
  have af := I.af lv
  obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  refine ⟨⟨af.1, nu_tcb hX (F.N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)⟩, fun e => hh ?_⟩
  rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hc, hcX0]

end alt

end Fl4Proofs.P2.PathObl
