/-
P3 (DESIGN.md §9): **`ReplyHypMX.succ` for the composite relation**: FL4's
success tail of `handle_invocation` (`reply_success_empty` when called, then
`Running`, for a thread still `Restart`) against the spec's `specTail` with
an empty result, keeping `RX`: `RInv` (VsReplyTop.lean: the CSpace relation,
`FinInv`, `MdbOKV`, the domain schedule and `FinX` at `TopSR`) at some
typed heap holding the current thread.

* `Endp.replyFromKernel_nil`: `reply_from_kernel (0, [])` sets the badge and
  message-info registers.
* `specTail_nil`: the spec's tail, by the thread's state.
* `replyHypMX_succ`.
-/
import Fl4Proofs.P3.VsReplyTop
import Fl4Proofs.P3.HandleTopX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The TCB after `reply_from_kernel (0, [])`. -/
def replyTcbNil (x : Tcb) : Tcb :=
  setReg (setReg x badge_register 0) msg_info_register (messageInfoToData ⟨natToLen 0, 0, 0, 0⟩)

theorem withRegs_nil (x : Tcb) : withRegs x (mrRegs x.tcbArch.tcbContext.userRegs []) = x := by
  have h0 : mrRegs x.tcbArch.tcbContext.userRegs [] = x.tcbArch.tcbContext.userRegs := by
    funext reg; simp [mrRegs]
  rw [h0]; rfl

theorem replyFromKernel_nil {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) :
    replyFromKernel (Z := Unit) t (0, []) σ = ({((), updK σ t (.tcb (replyTcbNil x)))}, False) := by
  have hkA : (updK σ t (.tcb (setReg x badge_register 0))).kheap t = some (.tcb (setReg x badge_register 0)) := by
    simp
  set xA := setReg x badge_register 0
  have hB : ∀ buf, setMrs (Z := Unit) t buf [] (updK σ t (.tcb xA)) =
      ({(natToLen 0, updK σ t (.tcb xA))}, False) := by
    intro buf
    cases buf with
    | none =>
      rw [setMrs_eqN hkA []]
      unfold mrStateN; rw [withRegs_nil, Vs.updK_updK]; rfl
    | some p =>
      rw [setMrs_eq hkA p [] (by intro q hq; simp [mrPairs] at hq)]
      unfold mrState
      rw [withRegs_nil, Vs.updK_updK]
      rfl
  unfold replyFromKernel
  rw [nd_pure_bind']
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hk true), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk),
    nd_bind_one (hB _)]
  unfold setMessageInfo
  rw [Notif.asUser_setRegister_eq _ _ hkA]
  simp only [Vs.updK_updK]
  rfl

end Spec

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

theorem tsCode_two {ts : Fl4Spec.ThreadState} (h : Notif.tsCode ts = 2) : ts = .restart := by
  cases ts <;> simp [Notif.tsCode] at h ⊢

/-- The spec's success tail with an empty result. -/
theorem specTail_nil {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (call : Bool) :
    specTail call t [] σ = (if x.tcbState = .restart then Fl4Spec.setThreadState (Z := Unit) t .running
      (if call then Notif.updK σ t (.tcb (Endp.replyTcbNil x)) else σ) else ({((), σ)}, False)) := by
  unfold specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk)]
  by_cases hrs : x.tcbState = .restart
  · rw [if_pos hrs]; simp only [hrs]
    cases call
    · rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind']; rfl
    · unfold Fl4Spec.NonDet.when; simp only [↓reduceIte]; rw [nd_bind_one (Endp.replyFromKernel_nil hk)]
  · rw [if_neg hrs]
    cases e : x.tcbState <;> first | exact absurd e hrs | rfl

/-- **The relation the reply keeps** (for `ReplyHypMX`): `RInv` at a typed
heap and pool set holding the current thread `ct`, with `ct` the spec's
current thread and the core's scheduler-action word outside the objects. -/
def RX {A : Type} (L4 L3 L2 L1 N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (AR : A → Fl4Spec.Cr3 → Prop) (ct : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th P G, RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ ∧ th ct = some .tcb ∧
    ct.bv = σ.curThread ∧ OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)

theorem RX.relTop {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {ct : U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct s a σ) : RelTopM (L := L) s σ :=
  let ⟨_, _, _, hI, _⟩ := h; hI.relTop

set_option maxHeartbeats 4000000 in
/-- **`ReplyHypMX.succ` for `RX`.** -/
theorem replyHypMX_succ {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} (ct : U64) (is_call : Bool) (s1 : S) (a1 : A)
    (σ' : Fl4Spec.State Unit) (hX : RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct s1 a1 σ') :
    flTail (st := st) ct is_call s1 a1 ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail is_call ct.bv [] σ').1, RelTopM (L := L) res.2.1 z.2 ∧
        RX (L := L) L4 L3 L2 L1 N T C E R B c AR ct res.2.1 res.2.2 z.2 ⦄ := by
  obtain ⟨th, P, G, hI, htcb, hcur, hact⟩ := hX
  obtain ⟨x, hk, -⟩ := hI.1.1.tcb ct htcb
  have hT := hI.2.2.2.2.1.cur_mem hcur
  have hxE := hI.2.2.2.2.1.1.2.1.at_tcb hT hk
  have hne : sched.TS_RUNNING ≠ sched.TS_RESTART := by unfold sched.TS_RUNNING sched.TS_RESTART; decide
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  rw [specTail_nil hk is_call]
  unfold flTail
  refine WP.spec_bind (tcb_state_spec' (st := st) s1 ct) ?_
  rintro i rfl
  by_cases hr : L.mem s1 (stA ct) = sched.TS_RESTART
  · rw [if_pos hr]
    have hrs : x.tcbState = .restart := by
      apply tsCode_two
      rw [← hxE.st]
      show (L.mem s1 (stA ct)).val = 2
      rw [hr]; unfold sched.TS_RESTART; rfl
    rw [if_pos hrs]
    have hrun : ∀ y : Fl4Spec.Tcb, y.tcbState = .restart → Fl4Spec.runnable y.tcbState = true := by
      intro y h; rw [h]; rfl
    cases is_call
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine WP.spec_bind (sts_inv s1 a1 σ' hI ct htcb hcur hk (hrun x hrs) hact .running (by decide) _ hcode) ?_
      rintro s' ⟨hI', -, hnode⟩
      simp only [WP.spec_ok]
      refine ⟨trivial, ((), Notif.stsAct (Notif.updK σ' ct.bv (.tcb { x with tcbState := .running })) ct.bv), ?_,
        hI'.relTop, th, P, G, hI', htcb, ?_, by rw [hnode]; exact hact⟩
      · rw [Notif.setThreadState_eq .running hk]; exact Set.mem_singleton _
      · rw [hcur]; show σ'.curThread = (Notif.stsAct _ _).curThread; unfold Notif.stsAct; split <;> rfl
    · simp only [↓reduceIte]
      have hin : msg.reply_success_empty st s1 ct ⦃ s3 => ∃ w : U64,
          s3 = L.wr (L.wr s1 (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
            (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
          w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 0, 0, 0, 0⟩ ⦄ := by
        unfold msg.reply_success_empty
        refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s1 ct layout.reg.BADGE 0#u64) ?_
        rintro s2 rfl
        unfold msginfo.MessageInfo.new
        simp only [bind_ok]
        refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 0#u64 (by decide)) ?_
        rintro s3 ⟨w, rfl, hw⟩
        refine ⟨w, by rw [Endp.regIdx_badge, Endp.regIdx_msgInfo], ?_⟩
        rw [hw]; congr 1
      refine WP.spec_bind hin ?_
      rintro s3 ⟨w, rfl, hw⟩
      have hI1 := regw_inv s1 a1 σ' hI ct htcb hcur hk (hrun x hrs) Fl4Spec.badge_register 0#u64
      set xA := Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv
      have hkA : (Notif.updK σ' ct.bv (.tcb xA)).kheap ct.bv = some (.tcb xA) := by simp
      have hcurA : ct.bv = (Notif.updK σ' ct.bv (.tcb xA)).curThread := hcur
      have hI2 := regw_inv _ a1 _ hI1 ct htcb hcurA hkA (hrun xA hrs) Fl4Spec.msg_info_register w
      have hxC : Notif.setReg xA Fl4Spec.msg_info_register w.bv = Endp.replyTcbNil x := by
        rw [hw]; rfl
      rw [updK_updK, hxC] at hI2
      have hkC : (Notif.updK σ' ct.bv (.tcb (Endp.replyTcbNil x))).kheap ct.bv =
          some (.tcb (Endp.replyTcbNil x)) := by simp
      have hact2 : OutsideObjects th (L.nodeAt (L.wr (L.wr s1 (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register))
          0#u64) (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w)
          (L.cpu (L.wr (L.wr s1 (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
            (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w)) layout.node.SCHED_ACTION) := by
        simp only [L.cpu_wr]; rw [Sched.nodeAt_ksb (s := s1) (by simp [L.ksb_wr])]; exact hact
      refine WP.spec_bind (sts_inv _ a1 _ hI2 ct htcb hcur hkC (hrun _ hrs) hact2 .running (by decide) _ hcode) ?_
      rintro s' ⟨hI', -, hnode⟩
      simp only [WP.spec_ok]
      rw [updK_updK] at hI'
      refine ⟨trivial, ((), Notif.stsAct (Notif.updK σ' ct.bv
        (.tcb { Endp.replyTcbNil x with tcbState := .running })) ct.bv), ?_, hI'.relTop, th, P, G, hI', htcb, ?_,
        by rw [hnode]; exact hact2⟩
      · rw [Notif.setThreadState_eq .running hkC, updK_updK]; exact Set.mem_singleton _
      · rw [hcur]; show σ'.curThread = (Notif.stsAct _ _).curThread; unfold Notif.stsAct; split <;> rfl
  · rw [if_neg hr]
    have hrs : x.tcbState ≠ .restart := by
      intro h
      apply hr
      apply UScalar.eq_of_val_eq
      rw [show (L.mem s1 (stA ct)).val = Notif.tsCode x.tcbState from hxE.st, h]
      unfold sched.TS_RESTART; rfl
    rw [if_neg hrs]
    simp only [WP.spec_ok]
    exact ⟨trivial, ((), σ'), Set.mem_singleton _, hI.relTop, th, P, G, hI, htcb, hcur, hact⟩

end

end

end Fl4Proofs.P3.Vs
