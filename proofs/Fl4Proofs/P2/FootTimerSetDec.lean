/-
# P2: a declined `TCB_SetTimer` local path

* `set_timer_prefix`: the state after the path's prefix (`FAULT_IP`, the timestamp): what stays;
* `set_timer_dec_guard`: at an entry state with P1's invariant and the core-placement facts (`StPre`), a declined run
  that may read the target's deadline and height (the target is not of this core, or disarmed, or armed in this
  core's tree) is the same run on `guard st MaxR (StDec)`: its reads are its own and it writes only `FAULT_IP` and
  the timestamp words;

Premises: `StLay` [J], `hAff` [J] (`P2/FootTimerSetOwn`), and in `StPre` the core-placement facts of p2j's
`P2/InvAff` (`CurAff`, `CurScOf`, `CurScCore`) with the caller neither queued nor blocked on reply [J].
-/
import Fl4Proofs.P2.FootTimerSetOwn
import Fl4Proofs.P2.FootTimerFound
import Fl4Proofs.P2.PathAgree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly ScAcc rhA tmA RdHead tr_bind tr_bind_same tr_ite)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

/-- **The path's prefix**: `FAULT_IP` and the timestamp words change. -/
theorem set_timer_prefix (hA : P0.ArchTotal ar) {s s1 s2 : S} {a a1 : A} {t nx : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (etc : L.curW s = t) (et : sched.cur_thread st s = ok t)
    (es1r : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx localtimer.SYSCALL_INSN_LEN) = ok s1)
    (eu : sched.update_timestamp st ar s1 a = ok (s2, a1)) :
    L.ksb s2 = L.ksb s ∧ L.cpu s2 = L.cpu s ∧
    (∀ {u K : U64}, u ∈ T → K.val < 4096 → K.val % 8 = 0 → (u = t → K.val ≠ 392) →
      L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K)) ∧
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
    (∀ b ∈ Ω, L.mem s2 b = L.mem s b) ∧ BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have htT : t ∈ T := etc ▸ h0.curT
  have ht' := hT t htT
  have es1 := es1r
  rw [insn_len_eq] at es1
  obtain ⟨et2, tK, oK⟩ := inv_prefix ar hT hN hcC et htT es1 eu hA
  obtain ⟨KF, hKF, hW⟩ := lt_prefix ar hT hN htT es1 eu hA
  have uK : ∀ {u K : U64}, u ∈ T → K.val < 4096 → K.val % 8 = 0 → (u = t → K.val ≠ 392) →
      L.mem s2 (core.num.U64.wrapping_add u K) = L.mem s (core.num.U64.wrapping_add u K) :=
    fun huT hK h8 hne => lt_tcbK hKF hT hN htT hW huT hK h8 hne
  have k2 : L.ksb s2 = L.ksb s := hW.1
  have c2 : L.cpu s2 = L.cpu s := hW.2.1
  have hN2 : NodePlaced st T s2 (L.cpu s2) := by rw [c2]; exact hN.ksb k2
  have e2N : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  have pre_node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 40 → o.val ≠ 48 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h40 h48
    refine hW.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (e | e | e)
    · exact tcb_node_ne hN htT ht' (by omega) ho e.symm
    · have e' := congrArg UScalar.val e
      unfold ctA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CUR_TIME])] at e'
      simp [layout.node.CUR_TIME] at e'; omega
    · have e' := congrArg UScalar.val e
      unfold cnA at e'
      rw [nodeAt_val hN ho, nodeAt_val hN (by simp [layout.node.CONSUMED])] at e'
      simp [layout.node.CONSUMED] at e'; omega
  have agΩ2 : ∀ b ∈ Ω, L.mem s2 b = L.mem s b := fun b hb => oK b (h0.omega b hb)
  have hB2 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 := by
    have hI1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
      have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
        ht' (by simp [layout.reg.FAULT_IP])
      rw [es1, WP.spec_ok] at hW1
      obtain ⟨K, hK, e1⟩ := hW1
      have hK' : K.val = 392 := by rw [hK]; simp [layout.reg.FAULT_IP]
      rw [e1]; exact (regW_all (BXI.blk hI) htT (by omega) (by omega) (by omega)).1
    have := sched.update_timestamp.bxc hA s1 a (BlkOK.bxi hI1)
    rw [eu, WP.spec_ok] at this
    try simp only [WP.uncurry'_pair] at this
    exact this.1.1
  exact ⟨k2, c2, uK, pre_node, agΩ2, hB2⟩

/-- **The core-placement facts** [J] at the entry (module docstring). -/
structure StPre (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (s : S) : Prop where
  aff : L.mem s (affA (L.curW s)) = L.cpu s
  nq : ¬ QueuedState (L.mem s (stA (L.curW s)))
  nr : ¬ ReplyState (L.mem s (stA (L.curW s)))
  sct : L.mem s (scA (L.curW s)) = L.cscW s
  csc : L.cscW s ∈ Scs
  core : L.mem s (scCoreA (L.cscW s)) = L.cpu s

/-- The words a declined run writes. -/
def StDec (st : machine.Store S) [L : LawfulStore st] (s : S) (w : U64) : Prop :=
  w = regA (L.curW s) layout.reg.FAULT_IP ∨ w = ctA (L := L) s ∨ w = cnA (L := L) s

set_option maxHeartbeats 16000000 in
/-- **A declined run on the guarded store** (module docstring). -/
theorem set_timer_dec_guard (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {target : U64}
    {lk : S → U64 → Prop} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htg : target ∈ T)
    (hL : StLay K st T Scs Z s) (hP : StPre st Scs s)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (hfar : L.mem s (affA target) ≠ L.cpu s ∨ L.mem s (tdA target) = 0#u64 ∨
      (L.mem s (thA target)).val >>> 8 = (L.cpu s).val)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (false, s', a')) :
    localtimer.handle_set_timer_local (guard st (MaxR K st lk s) (StDec st s)) ar s a n target = ok (false, s', a') := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcC : L.cpu s ∈ Cs := h0.cur
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ hcC
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have hO := hI.2.2.1.1
  have hS := hI.2.2.2.2
  set R : U64 → Prop := MaxR K st lk s with eR
  set W : U64 → Prop := StDec st s with eW
  have gateR : ∀ {x : U64} {k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → GateField k.val →
      R (core.num.U64.wrapping_add x k) := fun hx h1 h2 h8 hg =>
    ⟨Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg]), field_aligned (hT _ hx) h2 h8⟩
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    ⟨Or.inl (held_core (hL.own_node _ h1)), nodeAt_aligned hN h1 h2⟩
  have cR : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      R (core.num.U64.wrapping_add (L.curW s) k) := fun k h1 h2 h3 h4 => by
    have e := caller_own' hL hT hcT hP.aff hP.nq hP.nr h1 h2 h4
    refine ⟨?_, field_aligned ht' h2 h3⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have rR : ∀ r : U64, r.val < 384 → R (regA (L.curW s) r) := fun r hr => by
    obtain ⟨k, hk, e⟩ := regA_eq ht' hr
    rw [e]; exact cR k (by omega) (by omega) (by omega) (by omega)
  have scw : ∀ {p b : U64}, p ∈ Scs → InSC p (Z p) b → L.mem s (scCoreA p) = L.cpu s → Aligned b → R b :=
    fun hp hb hc ha => by
    have e := sc_own hL hp hb hc
    refine ⟨?_, ha⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have scR : ∀ b, InSC (L.cscW s) (Z (L.cscW s)) b → Aligned b → R b := fun b hb ha => scw hP.csc hb hP.core ha
  have hcq := scq_of hO hS hP.csc
  have keyR : ∀ y, y ∈ T → FootLtArmed st s (L.cpu s) y → ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add y k) := fun y hy ha k h1 h2 h3 => by
    refine ⟨Or.inl (held_core ?_), field_aligned (hT y hy) (by omega) h3⟩
    have e := hL.own_tcb hT (L.mem s) hy (k := k) (by omega) (by omega)
    unfold fld at e
    rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
      if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
      if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from fun h => ha.1 (UScalar.eq_of_val_eq h))]
    have e2 := ha.2
    rw [Nat.shiftRight_eq_div_pow] at e2
    exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)
  have rSt : R (stA (L.curW s)) := by rw [stA_eq]; exact cR _ (by simp) (by simp) (by simp) (by simp)
  have rSc : R (scA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rIq : R (inqA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rYt : R (yieldA (L.curW s)) := cR _ (by simp) (by simp) (by simp) (by simp)
  have rMx : R (maxA (L.cscW s)) := scR _ hcq.2.2.2.1 hcq.2.2.2.2
  have rD1 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨Or.inr (by unfold GateOnly; simp only [own, hL.dom]), hL.domA⟩
  have rD2 : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME) :=
    ⟨Or.inr (by unfold GateOnly; simp only [own, hL.dtm]), hL.dtmA⟩
  have rCore : R (scCoreA (L.cscW s)) := by
    obtain ⟨hPl, hz⟩ := hO.sc _ hP.csc
    obtain ⟨h8, h128, -⟩ := sc_lo hPl hz
    have hv := sc_word_val hPl hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    have hcv : layout.sc.CORE.val = 16 := by simp [layout.sc.CORE]
    exact scR _ ⟨by unfold scCoreA; rw [hv]; omega, by unfold scCoreA; rw [hv, hcv]; omega⟩
      (by unfold Aligned scCoreA; rw [hv, hcv]; omega)
  have rAt : R (affA target) := gateR htg (by simp) (by simp) (by simp) (Or.inl (by simp))
  obtain ⟨W0, ct0⟩ := (TInv.rb (BXI.blk hI)).tree _ hcC
  -- the target check
  have gtgt : ∀ b, localtimer.set_timer_target_ok st s (L.cpu s) target = ok b →
      localtimer.set_timer_target_ok (guard st R W) s (L.cpu s) target = ok b := by
    intro b eb
    by_cases hat : L.mem s (affA target) = L.cpu s
    · have hto : L.mem s (tdA target) = 0#u64 ∨ (L.mem s (thA target)).val >>> 8 = (L.cpu s).val :=
        hfar.resolve_left fun hn => hn hat
      have tgR : ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 → R (core.num.U64.wrapping_add target k) := by
        intro k h1 h2 h3
        by_cases hd : L.mem s (tdA target) = 0#u64
        · refine ⟨Or.inl (held_core ?_), field_aligned (hT _ htg) (by omega) h3⟩
          have e := hL.own_tcb hT (L.mem s) htg (k := k) (by omega) (by omega)
          unfold fld at e
          rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
            if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
            if_neg (show ¬ (L.mem s (fld target oTIMER_DEADLINE)).val ≠ 0 from fun h => h (by
              show (L.mem s (tdA target)).val = 0
              rw [hd]; rfl))]
          exact congrArg Owner.core hat
        · exact keyR target htg ⟨hd, hto.resolve_left hd⟩ k h1 h2 h3
      exact set_timer_target_ok.guard ct0 (fun w hw => by
        rcases hw with rfl | rfl | ⟨y, hy, rfl | rfl | rfl⟩
        · exact nR _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])
        · exact nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        · exact keyR y (ct0.inT y hy) ⟨ct0.armed y hy, ct0.core y hy⟩ _ (by simp) (by simp) (by simp)
        · exact keyR y (ct0.inT y hy) ⟨ct0.armed y hy, ct0.core y hy⟩ _ (by simp) (by simp) (by simp)
        · exact keyR y (ct0.inT y hy) ⟨ct0.armed y hy, ct0.core y hy⟩ _ (by simp) (by simp) (by simp))
        rAt (tgR _ (by simp) (by simp) (by simp)) (tgR _ (by simp) (by simp) (by simp)) eb
    · unfold localtimer.set_timer_target_ok at eb ⊢
      rw [PathObl.obj.Tcb.affinity.guard target s rAt]
      rw [aff_ok] at eb ⊢
      simp only [bind_ok] at eb ⊢
      have hne : (L.mem s (affA target) != L.cpu s) = true := by simpa using hat
      rw [if_pos hne] at eb ⊢
      exact eb
  revert h
  unfold localtimer.handle_set_timer_local
  rw [PathObl.sched.cur_thread.guard s (nR _ (by rw [curth_val]; omega) (by rw [curth_val])), cur_thread_ok,
    PathObl.guard_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok, lift]
  rw [PathObl.msg.msg_info.guard s _ (rR _ (by simp [layout.reg.MSG_INFO]))]
  refine tr_bind_same (fun info _ => ?_)
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.obj.Tcb.flags.guard _ s (cR _ (by simp) (by simp) (by simp) (by simp))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.cur_sc.guard s (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc ecsc => ?_)
  have ecsc' : L.cscW s = csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) s)] at ecsc; exact ok_inj_ff ecsc
  subst ecsc'
  refine tr_bind (fun b eb _ => gtgt b eb) (fun b _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [current_ok.guard s (L.cpu s) (L.curW s) (L.cscW s) (cR _ (by simp) (by simp) (by simp) (by simp)) rSt rYt
      (cR _ (by simp) (by simp) (by simp) (by simp)) rSc (by rw [hP.sct]; exact rCore) rCore
      (nR _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]))
      (cR _ (by simp) (by simp) (by simp) (by simp)) rD1]
  refine tr_bind_same (fun b1 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  rw [PathObl.obj.Tcb.state.guard _ s rSt]
  refine tr_bind_same (fun i2 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.is_schedulable.guard s _ rSt rSc (by rw [hP.sct]; exact rMx) rIq]
  refine tr_bind_same (fun b2 eb2 => ?_)
  refine tr_ite (fun hb2 => ?_) (fun _ h => h)
  rw [sched_quiet.guard s (nR _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])) rD2
      (nR _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING]))]
  refine tr_bind_same (fun b3 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  have hmx0 : L.rmax s (L.cscW s) ≠ 0#u64 := by
    subst hb2
    have hs := sched.is_schedulable.spec' (L := L) s (L.curW s)
    rw [eb2, WP.spec_ok] at hs
    obtain ⟨-, -, -, hmax0⟩ := hs rfl
    rw [hP.sct] at hmax0; exact hmax0
  rw [PathObl.obj.Tcb.reg.guard _ s _ (rR _ (by simp [layout.reg.NEXT_IP]))]
  refine tr_bind_same (fun nx _ => ?_)
  rw [PathObl.obj.Tcb.set_reg.guard _ s _ _ (Or.inl rfl)]
  refine tr_bind_same (fun s1 es1 => ?_)
  have e1s : s1 = L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx localtimer.SYSCALL_INSN_LEN) := by
    have e := es1
    rw [PathObl.set_reg_ok'] at e; exact (ok_inj_ff e).symm
  have e1N : ∀ o, L.nodeAt s1 (L.cpu s1) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [e1s]; exact PathObl.nd_wr _ _ _ _
  have ndR : ∀ (Y : S), (∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt s (L.cpu s) o) → ∀ o : U64, o.val < 4288 →
      o.val % 8 = 0 → R (L.nodeAt Y (L.cpu Y) o) := fun Y e o h1 h2 => by rw [e]; exact nR o h1 h2
  rw [PathObl.sched.update_timestamp.guard ar s1 a
      (ndR s1 e1N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (by show W (L.nodeAt s1 (L.cpu s1) _); rw [e1N]; exact Or.inr (Or.inl rfl))
      (ndR s1 e1N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))
      (by show W (L.nodeAt s1 (L.cpu s1) _); rw [e1N]; exact Or.inr (Or.inr rfl))]
  refine tr_bind_same (fun p eu => ?_)
  obtain ⟨s2, a1⟩ := p
  obtain ⟨k2, c2, uK, pre_node, agΩ2, hB2⟩ := set_timer_prefix ar hA hI rfl (cur_thread_ok s) es1 eu
  have e2N : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [c2, nodeAt_of_ksb k2]
  simp only [uncurry_apply_pair]
  rw [PathObl.sched.cur_time.guard s2 (ndR s2 e2N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))]
  refine tr_bind_same (fun now _ => ?_)
  rw [PathObl.msg.syscall_arg.guard_lt s2 _ _ _ (by rw [PathObl.n_msg_regs]; decide) (fun r er => by
      rw [PathObl.msg_register_zero] at er; rw [← ok_inj_ff er]; exact rR _ (by simp [layout.reg.R10]))]
  refine tr_bind_same (fun dl _ => ?_)
  rw [PathObl.msg.syscall_arg.guard_lt s2 _ _ _ (by rw [PathObl.n_msg_regs]; decide) (fun r er => by
      rw [PathObl.msg_register_one] at er; rw [← ok_inj_ff er]; exact rR _ (by simp [layout.reg.R8]))]
  refine tr_bind_same (fun bd _ => ?_)
  rw [PathObl.sched.consumed.guard s2 (ndR s2 e2N _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))]
  refine tr_bind_same (fun cns _ => ?_)
  have hdC : RdHead (L := L) R s2 (L.cscW s) :=
    PathObl.ScAcc.head (W := fun _ => True) ⟨scR, fun _ _ _ => trivial, trivial⟩ ((SCq.agree hcq agΩ2).1 (by
      unfold LawfulStore.rmax; rw [agΩ2 _ (hcq.2.1 _ hcq.2.2.2.2 hcq.2.2.2.1)]; exact hmx0))
  rw [PathObl.sporadic.sufficient.guard ar s2 a1 (L.cscW s) cns hdC]
  refine tr_bind_same (fun b4 _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  have gtdue : localtimer.timer_due (guard st R W) s2 (L.cpu s) now = localtimer.timer_due st s2 (L.cpu s) now := by
    have := timer_due.guard (R := R) (W := W) s2 now
      (ndR s2 e2N _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])) (fun hne => by
        have e : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.TIMER_MIN) =
            L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
          rw [e2N]
          exact pre_node _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
            (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
        rw [e] at hne ⊢
        obtain ⟨q1, q2⟩ := tmin_facts (BXI.blk hI) hcC hne
        exact keyR _ q1 q2 _ (by simp) (by simp) (by simp))
    rwa [c2] at this
  rw [gtdue]
  refine tr_bind_same (fun b5 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  have grdue : localtimer.release_due (guard st R W) s2 (L.cpu s) = localtimer.release_due st s2 (L.cpu s) := by
    have := release_due.guard (R := R) (W := W) s2
      (ndR s2 e2N _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
      (fun hne => by
        have e : L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.RELEASE_HEAD) =
            L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD) := by
          rw [e2N]
          exact pre_node _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
            (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
        rw [e] at hne ⊢
        obtain ⟨r1, r2, r3, r4, r5⟩ := rel_facts hI hne
        have hqr := scq_of hO hS r4
        have es : L.mem s2 (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) =
            L.mem s (scA (L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD))) := by
          rw [scA_eq]; exact uK r1 (by simp) (by simp) (fun _ => by simp)
        rw [es]
        refine ⟨gateR r1 (by simp) (by simp) (by simp) (by simp [GateField]), ?_⟩
        exact PathObl.ScAcc.head (W := fun _ => True)
          ⟨fun b hb ha => scw r4 hb (by rw [hAff _ r1 r3, r2]) ha, fun _ _ _ => trivial, trivial⟩
          ((SCq.agree hqr agΩ2).1 (by
            unfold LawfulStore.rmax; rw [agΩ2 _ (hqr.2.1 _ hqr.2.2.2.2 hqr.2.2.2.1)]; exact r5)))
      (ndR s2 e2N _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    rwa [c2] at this
  rw [grdue]
  refine tr_bind_same (fun b6 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  have acc : ∀ m : machine.Store S, (do
      let s3 ← sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART
      let s4 ← timer.insert st s3 target dl bd
      let s5 ← msg.reply_success_empty st s4 (L.curW s)
      let s6 ← sched.set_thread_state st s5 (L.curW s) sched.TS_RUNNING
      let (s7, a2) ← sched.schedule st ar s6 a1
      let (s8, a3) ← sched.activate_thread st ar s7 a2
      let t1 ← sched.cur_thread st s8
      let (s9, a4) ← vcpu.check st ar s8 a3 t1
      ok (true, s9, a4)) = ok (false, s', a') → False := by
    intro _ h
    obtain ⟨s3, -, h⟩ := bind_eq_ok h
    obtain ⟨s4, -, h⟩ := bind_eq_ok h
    obtain ⟨s5, -, h⟩ := bind_eq_ok h
    obtain ⟨s6, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨s7, a2⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨⟨s8, a3⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨t1, -, h⟩ := bind_eq_ok h
    obtain ⟨⟨s9, a4⟩, -, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    have e := ok_inj_ff h
    simp at e
  refine tr_ite (fun _ => tr_ite (fun _ h => h) (fun _ h => absurd h (acc st))) (fun _ h => absurd h (acc st))

end

end Fl4Proofs.P2
