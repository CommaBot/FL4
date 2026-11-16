/-
P3 (DESIGN.md §9), TCB invocations: **the data reply at the composite
relation** (the labels whose spec result is data and whose decode replies
itself: SetFlags, GetBreakpoint, ConfigureSingleStepping), generalising
VSpace's `reply1_invT` (one word, the badge first) to FL4's TCB order: the
message words by `set_mr` (registers, past `MR3` the caller's IPC buffer),
then `tcb::reply_words` (the badge and the message info), then `Running`.

* `replyStateB`, `replyState`: the spec's state after
  `reply_from_kernel (0, ms)` (`replyFromKernel_eq`), and `specTail_data`.
* `setReg_withRegs_comm`, `mrS_setReg`: the badge register is no message
  register, so FL4's badge write after the message words is the spec's
  before them.
* `setmr_reg_inv`: a message register write keeps `RInv` (VSpace's
  `setmr_inv` without its buffer premises, below `MR4`).
* `reply_tail_inv`: `reply_words` then `Running` keep `RInv`, against
  `specTail true` (`reply_tail_spec`).
* `XTopAt.toRInv`, `XTopAt.ofRInv`: `XTopAt` to VSpace's `RInv` and back
  (the kernel base and the SC objects kept), as `portInTail_xtop`.
-/
import Fl4Proofs.P3.XTopTcbRest
import Fl4Proofs.P3.ReplyFailX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's reply -/

section Spec
open Fl4Spec

theorem badge_not_mr : badge_register ∉ msg_registers := by decide

/-- A register outside the message registers commutes with them. -/
theorem setReg_withRegs_comm (x : Tcb) (ms : List Word) {r : Register} (hr : r ∉ msg_registers) (v : Word) :
    Notif.setReg (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)) r v =
      withRegs (Notif.setReg x r v) (mrRegs (Notif.setReg x r v).tcbArch.tcbContext.userRegs ms) := by
  have hr' : r ∉ msg_registers.take ms.length := fun h => hr (List.mem_of_mem_take h)
  simp only [Notif.setReg, withRegs, archTcbContextSet, archTcbContextGet, archTcbSetRegisters, Notif.setRegUc]
  congr 3
  funext reg
  unfold mrRegs
  by_cases h : reg = r
  · subst h; simp [hr']
  · simp [Function.update_of_ne h]

/-- **The badge write after the message words is the spec's before them.** -/
theorem mrS_setReg (σ : State Unit) (t : ObjRef) (x : Tcb) (buf : Option ObjRef) (ms : List Word)
    {r : Register} (hr : r ∉ msg_registers) (v : Word) :
    Notif.updK (MrS σ t x buf ms) t (.tcb (Notif.setReg (withRegs x (mrRegs x.tcbArch.tcbContext.userRegs ms)) r v)) =
      MrS (Notif.updK σ t (.tcb (Notif.setReg x r v))) t (Notif.setReg x r v) buf ms := by
  rw [setReg_withRegs_comm x ms hr v]
  cases buf <;> simp only [MrS, mrState, mrStateN, setUm, Notif.updK, Function.update_idem]

/-- The spec's state after `reply_from_kernel (0, ms)` with the buffer `buf`. -/
def replyStateB (σ : State Unit) (t : ObjRef) (x : Tcb) (buf : Option ObjRef) (ms : List Word) : State Unit :=
  Notif.updK (MrS (Notif.updK σ t (.tcb (Notif.setReg x badge_register 0))) t (Notif.setReg x badge_register 0)
      buf ms) t
    (.tcb (Notif.setReg (withRegs (Notif.setReg x badge_register 0)
      (mrRegs (Notif.setReg x badge_register 0).tcbArch.tcbContext.userRegs ms)) msg_info_register
      (messageInfoToData ⟨natToLen (mrLen buf ms.length), 0, 0, 0⟩)))

/-- The spec's state after `reply_from_kernel (0, ms)`. -/
abbrev replyState (σ : State Unit) (t : ObjRef) (x : Tcb) (ms : List Word) : State Unit :=
  replyStateB σ t x (ipcBufOf true x) ms

/-- The TCB in `replyStateB`. -/
def replyTcbB (x : Tcb) (buf : Option ObjRef) (ms : List Word) : Tcb :=
  Notif.setReg (withRegs (Notif.setReg x badge_register 0)
    (mrRegs (Notif.setReg x badge_register 0).tcbArch.tcbContext.userRegs ms)) msg_info_register
    (messageInfoToData ⟨natToLen (mrLen buf ms.length), 0, 0, 0⟩)

theorem replyStateB_kheap_t (σ : State Unit) (t : ObjRef) (x : Tcb) (buf : Option ObjRef) (ms : List Word) :
    (replyStateB σ t x buf ms).kheap t = some (.tcb (replyTcbB x buf ms)) := by
  simp [replyStateB, replyTcbB, Notif.updK]

theorem replyStateB_kheap_ne (σ : State Unit) (t : ObjRef) (x : Tcb) (buf : Option ObjRef) (ms : List Word)
    {q : ObjRef} (hq : q ≠ t) : (replyStateB σ t x buf ms).kheap q = σ.kheap q := by
  unfold replyStateB
  rw [Notif.updK_kheap, Function.update_of_ne hq, MrS_kheap_ne _ _ _ _ _ hq, Notif.updK_kheap,
    Function.update_of_ne hq]

theorem replyStateB_cur (σ : State Unit) (t : ObjRef) (x : Tcb) (buf : Option ObjRef) (ms : List Word) :
    (replyStateB σ t x buf ms).curThread = σ.curThread := by
  unfold replyStateB; simp only [Notif.updK]; rw [MrS_cur]

theorem replyTcbB_state (x : Tcb) (buf : Option ObjRef) (ms : List Word) :
    (replyTcbB x buf ms).tcbState = x.tcbState := rfl

/-- **`reply_from_kernel (0, ms)`** has one outcome, `replyState`. -/
theorem replyFromKernel_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (ms : List Word) (hlen : ms.length ≤ msgMaxLength)
    (hfr : ∀ p, ipcBufOf true x = some p → ∀ z ∈ mrPairs ms,
      (bufAddr p z.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p z.1) σ) :
    replyFromKernel (Z := Unit) t (0, ms) σ = ({((), replyState σ t x ms)}, False) := by
  set xA := Notif.setReg x badge_register 0
  have hkA : (Notif.updK σ t (.tcb xA)).kheap t = some (.tcb xA) := by simp
  unfold replyFromKernel
  rw [Notif.nd_pure_bind']
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hk true), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk)]
  unfold replyState replyStateB
  cases hb : ipcBufOf true x with
  | none =>
    rw [nd_bind_one (setMrs_eqN hkA ms)]
    unfold setMessageInfo
    have h' : (mrStateN (Notif.updK σ t (.tcb xA)) t xA ms).kheap t =
        some (.tcb (withRegs xA (mrRegs xA.tcbArch.tcbContext.userRegs ms))) := MrS_kheap_t _ _ _ none ms
    rw [Notif.asUser_setRegister_eq _ _ h']
    rfl
  | some p =>
    rw [nd_bind_one (setMrs_eq hkA p ms (fun q hq => ⟨(hfr p hb q hq).1,
      inUserFrame_updK hk (notDataPage_tcb x) _ (hfr p hb q hq).2⟩))]
    unfold setMessageInfo
    have h' : (mrState (Notif.updK σ t (.tcb xA)) t xA p ms).kheap t =
        some (.tcb (withRegs xA (mrRegs xA.tcbArch.tcbContext.userRegs ms))) := MrS_kheap_t _ _ _ (some p) ms
    rw [Notif.asUser_setRegister_eq _ _ h', show min ms.length msgMaxLength = ms.length by omega]
    rfl

/-- **The spec's success tail with data** of a `Restart` thread, called. -/
theorem specTail_data {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (hrs : x.tcbState = .restart) (ms : List Word) (hlen : ms.length ≤ msgMaxLength)
    (hfr : ∀ p, ipcBufOf true x = some p → ∀ z ∈ mrPairs ms,
      (bufAddr p z.1).toNat % 8 = 0 ∧ inUserFrame (bufAddr p z.1) σ) :
    specTail true t ms σ = ({((), Notif.stsAct (Notif.updK (replyState σ t x ms) t
      (.tcb { replyTcbB x (ipcBufOf true x) ms with tcbState := .running })) t)}, False) := by
  unfold specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk)]
  simp only [hrs]
  unfold NonDet.when; simp only [↓reduceIte]
  rw [nd_bind_one (replyFromKernel_eq hk ms hlen hfr)]
  exact Notif.setThreadState_eq .running (replyStateB_kheap_t _ _ _ _ _)

/-- A spec step changing only the TCB at `t` keeps the SC objects. -/
theorem szKeep_tcbOnly {σ σ' : State Unit} {t : ObjRef} (h : ∀ q, q ≠ t → σ'.kheap q = σ.kheap q)
    (ht : ∃ y, σ'.kheap t = some (.tcb y)) : SzKeep σ σ' := by
  intro q y n hq
  by_cases e : q = t
  · subst e; obtain ⟨y', hy'⟩ := ht; rw [hy'] at hq; cases hq
  · exact ⟨y, by rw [← h q e]; exact hq⟩

end Spec

theorem run_ne_rst : sched.TS_RUNNING ≠ sched.TS_RESTART := by
  unfold sched.TS_RUNNING sched.TS_RESTART; decide

/-! ## `XTopAt` and `RInv` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem XTopAt.toRInv {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) :
    Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR Z.G s a σ :=
  ⟨hX.rel.2.1, hX.rel.2.2.1, hX.rel.2.2.2.2.1, hX.rel.2.2.2.1, hX.fin⟩

/-- **`XTopAt` from `RInv`** at a state with the kernel base and the SC
objects kept (as `portInTail_xtop`). -/
theorem XTopAt.ofRInv {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {G' : MdbGhost}
    (hI : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR G' s' a' σ')
    (hks : L.ksb s' = L.ksb s) (hz : Sched.SzKeep σ σ') :
    XTopAt (L := L) AR { Z with G := G' } s' a' σ' := by
  have hSch := hI.2.2.2.2.1.1.1
  exact ⟨hI.2.2.2.2, ⟨hX.rel.1, hI.1, hI.2.1, hI.2.2.2.1, hI.2.2.1, by rw [hks]; exact hX.rel.2.2.2.2.2.1,
    hX.rel.2.2.2.2.2.2.mono hz⟩,
    IpcRel.of hI.2.2.2.2.1.1.2.2.1 hI.2.2.2.2.1.1.2.1 (sched_sc hSch), hX.esa.mono hks hz⟩

end

/-! ## FL4's reply at `RInv` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **`set_mr` of a message register keeps `RInv`** (`MR0`..`MR3`), the
spec's `set_mrs` state growing by the word. -/
theorem setmr_reg_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) (x0 : Fl4Spec.Tcb)
    (buf : Option Fl4Spec.ObjRef) (w : U64) (s : S) (a : A) (ms : List Fl4Spec.Word)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (i : U64) (hi : i.val = ms.length) (h4 : ms.length < 4) (v : U64) :
    msg.set_mr st s ct w i v ⦃ r => r.1.val = ms.length + 1 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.2 a (MrS σ0 ct.bv x0 buf (ms ++ [v.bv])) ∧
      L.ksb r.2 = L.ksb s ∧ L.cpu r.2 = L.cpu s ⦄ := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  have hcurM : ct.bv = (MrS σ0 ct.bv x0 buf ms).curThread := by rw [MrS_cur]; exact hcur
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  have h4' : i < msg.N_MSG_REGISTERS := (P1.gt_iff_val).2 (by rw [hN]; omega)
  simp only [h4', ↓reduceIte]
  refine WP.spec_bind (Endp.msg_register_spec i (by omega)) ?_
  rintro r rfl
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct _ v) ?_
  rintro s1 rfl
  simp only [lift, bind_ok, WP.spec_ok]
  have hI1 := regw_inv s a _ hI ct htcb hcurM hkx (Endp.mrIdx i.val) v
  refine ⟨?_, ?_, L.ksb_wr _ _ _, L.cpu_wr _ _ _⟩
  · simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · cases buf with
    | none =>
      have e := Endp.mrStateN_snoc_lt σ0 ct.bv x0 ms v.bv i.val hi h4
      simp only [MrS] at hI1 ⊢; rw [← e]; exact hI1
    | some p =>
      have e := Endp.mrState_snoc_lt σ0 ct.bv x0 p ms v.bv i.val hi h4
      simp only [MrS] at hI1 ⊢; rw [← e]; exact hI1

set_option maxHeartbeats 4000000 in
/-- **`reply_words` keeps `RInv`**: the badge and the message info after the
message words, against `replyStateB`. -/
theorem reply_words_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) (x0 : Fl4Spec.Tcb)
    (buf : Option Fl4Spec.ObjRef) (s : S) (a : A) (ms : List Fl4Spec.Word)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (n : U64) (hn : n.val = mrLen buf ms.length) (hn128 : n.val < 128) :
    tcb.reply_words st s ct n ⦃ s' =>
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s' a (replyStateB σ0 ct.bv x0 buf ms) ∧
      L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ⦄ := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  have hcurM : ct.bv = (MrS σ0 ct.bv x0 buf ms).curThread := by rw [MrS_cur]; exact hcur
  unfold tcb.reply_words
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  have hI1 := regw_inv s a _ hI ct htcb hcurM hkx Fl4Spec.badge_register 0#u64
  rw [Endp.regIdx_badge, mrS_setReg σ0 ct.bv x0 buf ms badge_not_mr] at hI1
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at hI1
  set xA := Notif.setReg x0 Fl4Spec.badge_register 0
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s2 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have hkA := MrS_kheap_t (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms
  have hI2 := regw_inv _ a _ hI1 ct htcb (by rw [MrS_cur]; exact hcur) hkA Fl4Spec.msg_info_register v
  refine ⟨?_, by rw [L.ksb_wr, L.ksb_wr], by rw [L.cpu_wr, L.cpu_wr]⟩
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen buf ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  unfold replyStateB
  rw [← hvd]; exact hI2


theorem MrS_nil {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb} (hk : σ.kheap t = some (.tcb x))
    (buf : Option Fl4Spec.ObjRef) : MrS σ t x buf [] = σ := by
  cases buf with
  | none => exact Endp.mrStateN_nil hk
  | some p => exact Endp.mrState_nil hk p

set_option maxHeartbeats 4000000 in
/-- **`reply_words` then `Running` keep `RInv`** (the caller `Restart`),
against the spec's reply then `Running`. -/
theorem reply_tail_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) {x0 : Fl4Spec.Tcb}
    (hrs : x0.tcbState = .restart) (buf : Option Fl4Spec.ObjRef) (s : S) (a : A) (ms : List Fl4Spec.Word)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (n : U64) (hn : n.val = mrLen buf ms.length) (hn128 : n.val < 128) :
    (do
      let s4 ← tcb.reply_words st s ct n
      sched.set_thread_state st s4 ct sched.TS_RUNNING) ⦃ s' =>
      L.mem s' (stA ct) ≠ sched.TS_RESTART ∧ L.ksb s' = L.ksb s ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s' a (Notif.stsAct (Notif.updK
        (replyStateB σ0 ct.bv x0 buf ms) ct.bv (.tcb { replyTcbB x0 buf ms with tcbState := .running })) ct.bv) ⦄ := by
  refine WP.spec_bind (reply_words_inv σ0 ct htcb hcur x0 buf s a ms hI n hn hn128) ?_
  rintro s4 ⟨hI4, hk4, hc4⟩
  have hact4 : OutsideObjects th (L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION) := by
    rw [hc4, Sched.nodeAt_ksb hk4]; exact hact
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_mono (WP.spec_and (sts_inv s4 a _ hI4 ct htcb (by rw [replyStateB_cur]; exact hcur)
    (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]; rfl) hact4 .running (by decide) _ hcode)
    (set_thread_state_cases s4 ct sched.TS_RUNNING)) ?_
  rintro s' ⟨⟨hI', hst', -⟩, hcs⟩
  refine ⟨by rw [hst']; exact run_ne_rst, ?_, hI'⟩
  rcases hcs with rfl | rfl <;> simp [L.ksb_wr, hk4]

end

/-! ## The data tail at `XTop` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 8000000 in
/-- **The data reply at `XTop`, called**: from `XTop` at `σy` (the caller
`Restart`), FL4's message words at `RInv` (the spec's `set_mrs` state from
`σy`, the kernel base and core kept), then `reply_words` and `Running`,
against `specTail true` of the words. -/
theorem data_tail_xtop {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a1 : A} {σy : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a1 σy) {ct : U64} (hcur : ct.bv = σy.curThread) {x : Fl4Spec.Tcb}
    (hk : σy.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION))
    {s2 : S} {G' : MdbGhost} {ms : List Fl4Spec.Word}
    (hI : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR G' s2 a1
      (MrS σy ct.bv x (Endp.ipcBufOf true x) ms))
    (hks : L.ksb s2 = L.ksb s1) (hcpu : L.cpu s2 = L.cpu s1) (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σy)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x) ms.length) (hn128 : n.val < 128) :
    (do
      let s4 ← tcb.reply_words st s2 ct n
      let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1)) ⦃ res =>
      res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail true ct.bv ms σy).1, RelTopM (L := L) res.2.1 z.2 ∧ XTop (L := L) AR res.2.1 res.2.2 z.2 ⦄ := by
  have htcb := (hX.curTcb hcur.symm).1
  have hact2 : OutsideObjects Z.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
    rw [hcpu, Sched.nodeAt_ksb hks]; exact hact
  have hT := reply_tail_inv σy ct htcb hcur hrs _ s2 a1 ms hI hact2 n hn hn128
  rw [← Std.bind_assoc]
  refine WP.spec_bind hT ?_
  rintro s5 ⟨hne, hk5, hI5⟩
  simp only [WP.spec_ok]
  refine ⟨by first | rfl | trivial, hne, _, by rw [specTail_data hk hrs ms hlen hfr]; exact Set.mem_singleton _, hI5.relTop, ?_⟩
  have hz : Sched.SzKeep σy (Notif.stsAct (Notif.updK (replyState σy ct.bv x ms) ct.bv
      (.tcb { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running })) ct.bv) := by
    refine szKeep_tcbOnly (t := ct.bv) (fun q hq => ?_)
      ⟨{ replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running }, by rw [Notif.stsAct_kheap]; simp [Notif.updK]⟩
    rw [Notif.stsAct_kheap, Notif.updK_kheap, Function.update_of_ne hq, replyStateB_kheap_ne _ _ _ _ _ hq]
  exact ⟨_, hX.ofRInv hI5 (hk5.trans hks) hz⟩

set_option maxHeartbeats 8000000 in
/-- **The tail at `XTop`, not called**: `Running`, against `specTail false`
(any words). -/
theorem nodata_tail_xtop {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a1 : A} {σy : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a1 σy) {ct : U64} (hcur : ct.bv = σy.curThread) {x : Fl4Spec.Tcb}
    (hk : σy.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION)) (ms : List Fl4Spec.Word) :
    (do
      let s5 ← sched.set_thread_state st s1 ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a1)) ⦃ res =>
      res.1 = .Ok () ∧ L.mem res.2.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail false ct.bv ms σy).1, RelTopM (L := L) res.2.1 z.2 ∧ XTop (L := L) AR res.2.1 res.2.2 z.2 ⦄ := by
  have htcb := (hX.curTcb hcur.symm).1
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_bind (WP.spec_and (sts_inv s1 a1 σy hX.toRInv ct htcb hcur hk (by rw [hrs]; rfl) hact .running
    (by decide) _ hcode) (set_thread_state_cases s1 ct sched.TS_RUNNING)) ?_
  rintro s5 ⟨⟨hI5, hst5, -⟩, hcs⟩
  have hk5 : L.ksb s5 = L.ksb s1 := by rcases hcs with rfl | rfl <;> simp [L.ksb_wr]
  simp only [WP.spec_ok]
  refine ⟨by first | rfl | trivial, by rw [hst5]; exact run_ne_rst, ((), _), ?_, hI5.relTop,
    ⟨_, hX.ofRInv hI5 hk5 (szKeep_stsAct_tcb _ _ _)⟩⟩
  unfold specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk)]
  simp only [hrs]
  rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind', Notif.setThreadState_eq .running hk]
  exact Set.mem_singleton _

set_option maxHeartbeats 8000000 in
/-- `data_tail_xtop` before the result: the reply and `Running` alone. -/
theorem data_tail_core {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a1 : A} {σy : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a1 σy) {ct : U64} (hcur : ct.bv = σy.curThread) {x : Fl4Spec.Tcb}
    (hk : σy.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION))
    {s2 : S} {G' : MdbGhost} {ms : List Fl4Spec.Word}
    (hI : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR G' s2 a1
      (MrS σy ct.bv x (Endp.ipcBufOf true x) ms))
    (hks : L.ksb s2 = L.ksb s1) (hcpu : L.cpu s2 = L.cpu s1) (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σy)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x) ms.length) (hn128 : n.val < 128) :
    (do
      let s4 ← tcb.reply_words st s2 ct n
      sched.set_thread_state st s4 ct sched.TS_RUNNING) ⦃ s5 =>
      L.mem s5 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail true ct.bv ms σy).1, RelTopM (L := L) s5 z.2 ∧ XTop (L := L) AR s5 a1 z.2 ⦄ := by
  have htcb := (hX.curTcb hcur.symm).1
  have hact2 : OutsideObjects Z.th (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) := by
    rw [hcpu, Sched.nodeAt_ksb hks]; exact hact
  refine WP.spec_mono (reply_tail_inv σy ct htcb hcur hrs _ s2 a1 ms hI hact2 n hn hn128) ?_
  rintro s5 ⟨hne, hk5, hI5⟩
  refine ⟨hne, _, by rw [specTail_data hk hrs ms hlen hfr]; exact Set.mem_singleton _, hI5.relTop, ?_⟩
  have hz : Sched.SzKeep σy (Notif.stsAct (Notif.updK (replyState σy ct.bv x ms) ct.bv
      (.tcb { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running })) ct.bv) := by
    refine szKeep_tcbOnly (t := ct.bv) (fun q hq => ?_)
      ⟨{ replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running }, by rw [Notif.stsAct_kheap]; simp [Notif.updK]⟩
    rw [Notif.stsAct_kheap, Notif.updK_kheap, Function.update_of_ne hq, replyStateB_kheap_ne _ _ _ _ _ hq]
  exact ⟨_, hX.ofRInv hI5 (hk5.trans hks) hz⟩

/-- `data_tail_core` with a continuation. -/
theorem data_tail_k {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a1 : A} {σy : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a1 σy) {ct : U64} (hcur : ct.bv = σy.curThread) {x : Fl4Spec.Tcb}
    (hk : σy.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION))
    {s2 : S} {G' : MdbGhost} {ms : List Fl4Spec.Word}
    (hI : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR G' s2 a1
      (MrS σy ct.bv x (Endp.ipcBufOf true x) ms))
    (hks : L.ksb s2 = L.ksb s1) (hcpu : L.cpu s2 = L.cpu s1) (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σy)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x) ms.length) (hn128 : n.val < 128)
    {β : Type} (k : S → Result β) {Q : β → Prop}
    (hQ : ∀ s5, L.mem s5 (stA ct) ≠ sched.TS_RESTART →
      (∃ z ∈ (specTail true ct.bv ms σy).1, RelTopM (L := L) s5 z.2 ∧ XTop (L := L) AR s5 a1 z.2) → k s5 ⦃ Q ⦄) :
    (do
      let s4 ← tcb.reply_words st s2 ct n
      let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
      k s5) ⦃ Q ⦄ := by
  rw [← Std.bind_assoc]
  exact WP.spec_bind (data_tail_core hX hcur hk hrs hact hI hks hcpu hlen hfr n hn hn128)
    fun s5 h => hQ s5 h.1 h.2

set_option maxHeartbeats 8000000 in
/-- `nodata_tail_xtop` before the result: `Running` alone. -/
theorem nodata_tail_core {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a1 : A} {σy : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a1 σy) {ct : U64} (hcur : ct.bv = σy.curThread) {x : Fl4Spec.Tcb}
    (hk : σy.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION)) (ms : List Fl4Spec.Word) :
    sched.set_thread_state st s1 ct sched.TS_RUNNING ⦃ s5 =>
      L.mem s5 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail false ct.bv ms σy).1, RelTopM (L := L) s5 z.2 ∧ XTop (L := L) AR s5 a1 z.2 ⦄ := by
  have htcb := (hX.curTcb hcur.symm).1
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_mono (WP.spec_and (sts_inv s1 a1 σy hX.toRInv ct htcb hcur hk (by rw [hrs]; rfl) hact .running
    (by decide) _ hcode) (set_thread_state_cases s1 ct sched.TS_RUNNING)) ?_
  rintro s5 ⟨⟨hI5, hst5, -⟩, hcs⟩
  have hk5 : L.ksb s5 = L.ksb s1 := by rcases hcs with rfl | rfl <;> simp [L.ksb_wr]
  refine ⟨by rw [hst5]; exact run_ne_rst, ((), _), ?_, hI5.relTop,
    ⟨_, hX.ofRInv hI5 hk5 (szKeep_stsAct_tcb _ _ _)⟩⟩
  unfold specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk)]
  simp only [hrs]
  rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind', Notif.setThreadState_eq .running hk]
  exact Set.mem_singleton _

end

end

end Fl4Proofs.P3
