/-
P3 (DESIGN.md §9), VSpace, FrameBatch (#71): **the batch's reply**, for the
composite relation. FL4's `decode_frame_batch` ends (after its loop and the
deferred `invalidate_asid`) with the reply of two words when called (the
badge, `MR0` = entries done, `MR1` = the failing entry's code, the message
info) and `set_thread_state Running` (`fbTail`), with no `Restart` before;
the spec's shell runs `reply_from_kernel (0, [done, err])` and
`set_thread_state Running` after its `Restart` (`specTail`).

* `Endp.replyTcb2`, `Endp.replyFromKernel_two`: the spec's reply of two
  words (as VsReplyTop's `replyFromKernel_one`).
* `fbTail_core`: `fbTail` of the current, runnable thread keeps `RInv`
  (as VsReplyTop's `reply1_core`); `fbTail_ksb`.
* `fbTail_inv`: against `specTail` from the spec's `Restart` of that
  thread: the `Restart`, which FL4 omits, is absorbed by the final
  `Running` (`stsAct_twice`, as `tacHypX_top`).
-/
import Fl4Proofs.P3.VsReplyTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The TCB after `reply_from_kernel (0, [d, e])`. -/
def replyTcb2 (x : Tcb) (d e : Word) : Tcb :=
  setReg (setReg (setReg (setReg x badge_register 0) (mrIdx 0) d) (mrIdx 1) e) msg_info_register
    (messageInfoToData ⟨natToLen 2, 0, 0, 0⟩)

theorem withRegs_two (x : Tcb) (d e : Word) :
    withRegs x (mrRegs x.tcbArch.tcbContext.userRegs [d, e]) = setReg (setReg x (mrIdx 0) d) (mrIdx 1) e := by
  have h0 : mrRegs x.tcbArch.tcbContext.userRegs [] = x.tcbArch.tcbContext.userRegs := by
    funext reg; simp [mrRegs]
  have h1 := mrRegs_snoc_lt x.tcbArch.tcbContext.userRegs [] d (by simp)
  simp only [List.nil_append, h0, List.length_nil] at h1
  have h2 := mrRegs_snoc_lt x.tcbArch.tcbContext.userRegs [d] e (by simp)
  simp only [List.singleton_append, List.length_singleton] at h2
  rw [h2, h1]; rfl

/-- **`reply_from_kernel (0, [d, e])`**: one outcome, the TCB's badge, `MR0`,
`MR1` and message-info registers set. -/
theorem replyFromKernel_two {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (d e : Word) :
    replyFromKernel (Z := Unit) t (0, [d, e]) σ = ({((), updK σ t (.tcb (replyTcb2 x d e)))}, False) := by
  have hkA : (updK σ t (.tcb (setReg x badge_register 0))).kheap t = some (.tcb (setReg x badge_register 0)) := by
    simp
  set xA := setReg x badge_register 0
  set xB := setReg (setReg xA (mrIdx 0) d) (mrIdx 1) e
  have hB : ∀ buf, setMrs (Z := Unit) t buf [d, e] (updK σ t (.tcb xA)) =
      ({(natToLen 2, updK (updK σ t (.tcb xA)) t (.tcb xB))}, False) := by
    intro buf
    cases buf with
    | none =>
      rw [setMrs_eqN hkA [d, e]]
      unfold mrStateN; rw [withRegs_two]; rfl
    | some p =>
      rw [setMrs_eq hkA p [d, e] (by intro q hq; simp [mrPairs] at hq)]
      unfold mrState
      rw [withRegs_two]
      rfl
  have hkB : (updK (updK σ t (.tcb xA)) t (.tcb xB)).kheap t = some (.tcb xB) := by simp
  unfold replyFromKernel
  rw [nd_pure_bind']
  dsimp only
  rw [nd_bind_one (lookupIpcBuffer_eq hk true), nd_bind_one (Notif.asUser_setRegister_eq _ _ hk),
    nd_bind_one (hB _)]
  unfold setMessageInfo
  rw [Notif.asUser_setRegister_eq _ _ hkB]
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
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- **FL4's tail of `decode_frame_batch`** (after the deferred invalidation):
the reply of `d` (entries done) and `e` (the failing entry's code) when
called, then `Running`. -/
def fbTail (s : S) (ct : U64) (call : Bool) (d e : U64) : Result S := do
  let s2 ←
    if call
    then
      do
      let rbuf ← msg.lookup_ipc_buffer st s true ct
      let s3 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
      let (_, s4) ← msg.set_mr st s3 ct rbuf 0#u64 d
      let (len, s5) ← msg.set_mr st s4 ct rbuf 1#u64 e
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
      msg.set_msg_info st s5 ct mi
    else ok s
  sched.set_thread_state st s2 ct sched.TS_RUNNING

theorem msg_info_two_bv : (Fl4Spec.messageInfoToData
    ⟨(2#u64 : U64).bv, 0, 0, (0#u64 : U64).bv &&& Fl4Spec.mask Fl4Spec.msgLabelBits⟩) =
    Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 2, 0, 0, 0⟩ := by
  congr 1

/-- `set_mr` of a register word (`i < 4`). -/
theorem set_mr_reg (s1 : S) (ct buf i v : U64) (hi : i.val < 4) (h4 : i < msg.N_MSG_REGISTERS) :
    msg.set_mr st s1 ct buf i v ⦃ r =>
      r = (core.num.U64.wrapping_add i 1#u64, L.wr s1 (Endp.regA ct (Endp.regIdx (Endp.mrIdx i.val))) v) ⦄ := by
  unfold msg.set_mr
  simp only [h4, ↓reduceIte]
  refine WP.spec_bind (Endp.msg_register_spec i hi) ?_
  rintro r0 rfl
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec _ ct _ v) ?_
  rintro s2 rfl
  simp only [lift, bind_ok, WP.spec_ok]

/-- The reply words of `fbTail` (when called). -/
theorem fbTail_words (s : S) (ct d e : U64) :
    (do
      let rbuf ← msg.lookup_ipc_buffer st s true ct
      let s3 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
      let (_, s4) ← msg.set_mr st s3 ct rbuf 0#u64 d
      let (len, s5) ← msg.set_mr st s4 ct rbuf 1#u64 e
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
      msg.set_msg_info st s5 ct mi) ⦃ s5 => ∃ w : U64,
        s5 = L.wr (L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
          (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) d) (Endp.regA ct (Endp.regIdx (Endp.mrIdx 1))) e)
          (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w ∧
        w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 2, 0, 0, 0⟩ ⦄ := by
  refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s true ct L.total) ?_
  rintro buf -
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  refine WP.spec_bind (set_mr_reg _ ct buf 0#u64 d (by decide) (by unfold msg.N_MSG_REGISTERS; decide)) ?_
  rintro r rfl
  refine WP.spec_bind (set_mr_reg _ ct buf 1#u64 e (by decide) (by unfold msg.N_MSG_REGISTERS; decide)) ?_
  rintro r rfl
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 2#u64 (by decide)) ?_
  rintro s3 ⟨w, rfl, hw⟩
  refine ⟨w, ?_, by rw [hw]; exact msg_info_two_bv⟩
  rw [Endp.regIdx_badge, Endp.regIdx_msgInfo]
  rfl

set_option maxHeartbeats 4000000 in
/-- **`fbTail` of the current, runnable thread keeps `RInv`**: the reply
registers when called, then `Running`. -/
theorem fbTail_core {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrx : Fl4Spec.runnable x.tcbState = true)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (call : Bool) (d e : U64) :
    fbTail (st := st) s ct call d e ⦃ s2 => L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧
      RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s2 a (Notif.stsAct (Notif.updK σ ct.bv
        (.tcb { (if call then Endp.replyTcb2 x d.bv e.bv else x) with tcbState := .running })) ct.bv) ⦄ := by
  have hrs : x.tcbState = x.tcbState := rfl
  have hrun : ∀ y : Fl4Spec.Tcb, y.tcbState = x.tcbState → Fl4Spec.runnable y.tcbState = true := by
    intro y h; rw [h]; exact hrx
  have hne : sched.TS_RUNNING ≠ sched.TS_RESTART := by unfold sched.TS_RUNNING sched.TS_RESTART; decide
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  unfold fbTail
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (sts_inv s a σ hI ct htcb hcur hk (hrun x hrs) hact .running (by decide) _ hcode) ?_
    rintro s' ⟨hI', hst', -⟩
    exact ⟨by rw [hst']; exact hne, hI'⟩
  · simp only [↓reduceIte]
    refine WP.spec_bind (fbTail_words s ct d e) ?_
    rintro s3 ⟨w, rfl, hw⟩
    have hI1 := regw_inv s a σ hI ct htcb hcur hk Fl4Spec.badge_register 0#u64
    set xA := Notif.setReg x Fl4Spec.badge_register (0#u64 : U64).bv
    have hkA : (Notif.updK σ ct.bv (.tcb xA)).kheap ct.bv = some (.tcb xA) := by simp
    have hcurA : ct.bv = (Notif.updK σ ct.bv (.tcb xA)).curThread := hcur
    have hI2 := regw_inv _ a _ hI1 ct htcb hcurA hkA (Endp.mrIdx 0) d
    set xB := Notif.setReg xA (Endp.mrIdx 0) d.bv
    have hkB : (Notif.updK (Notif.updK σ ct.bv (.tcb xA)) ct.bv (.tcb xB)).kheap ct.bv = some (.tcb xB) := by simp
    have hI3 := regw_inv _ a _ hI2 ct htcb hcurA hkB (Endp.mrIdx 1) e
    set xC := Notif.setReg xB (Endp.mrIdx 1) e.bv
    have hkC : (Notif.updK (Notif.updK (Notif.updK σ ct.bv (.tcb xA)) ct.bv (.tcb xB)) ct.bv (.tcb xC)).kheap ct.bv =
        some (.tcb xC) := by simp
    have hI4 := regw_inv _ a _ hI3 ct htcb hcurA hkC Fl4Spec.msg_info_register w
    have hxD : Notif.setReg xC Fl4Spec.msg_info_register w.bv = Endp.replyTcb2 x d.bv e.bv := by
      rw [hw]; rfl
    rw [updK_updK, updK_updK, updK_updK, hxD] at hI4
    have hkD : (Notif.updK σ ct.bv (.tcb (Endp.replyTcb2 x d.bv e.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb2 x d.bv e.bv)) := by simp
    have hact4 : OutsideObjects th (L.nodeAt (L.wr (L.wr (L.wr (L.wr s
        (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
        (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) d) (Endp.regA ct (Endp.regIdx (Endp.mrIdx 1))) e)
        (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w)
        (L.cpu (L.wr (L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
          (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) d) (Endp.regA ct (Endp.regIdx (Endp.mrIdx 1))) e)
          (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w)) layout.node.SCHED_ACTION) := by
      simp only [L.cpu_wr]; rw [Sched.nodeAt_ksb (s := s) (by simp [L.ksb_wr])]; exact hact
    refine WP.spec_mono (sts_inv _ a _ hI4 ct htcb hcur hkD (hrun _ hrs) hact4 .running (by decide) _ hcode) ?_
    rintro s' ⟨hI', hst', -⟩
    rw [updK_updK] at hI'
    exact ⟨by rw [hst']; exact hne, hI'⟩

/-- `fbTail` keeps the kernel base. -/
theorem fbTail_ksb (s : S) (ct : U64) (call : Bool) (d e : U64) :
    fbTail (st := st) s ct call d e ⦃ s2 => L.ksb s2 = L.ksb s ⦄ := by
  unfold fbTail
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (set_thread_state_cases s ct sched.TS_RUNNING) ?_
    rintro s' (rfl | rfl) <;> simp
  · simp only [↓reduceIte]
    refine WP.spec_bind (fbTail_words s ct d e) ?_
    rintro s3 ⟨w, rfl, -⟩
    refine WP.spec_mono (set_thread_state_cases _ ct sched.TS_RUNNING) ?_
    rintro s' (rfl | rfl) <;> simp

set_option maxHeartbeats 4000000 in
/-- **`fbTail` against the spec's `specTail` after its `Restart`** of the
current, runnable thread (FL4 has no `Restart`; the spec's is absorbed by
the final `Running`, `stsAct_twice`): `RInv` with an outcome of `specTail`,
the kernel base and the SC objects kept. -/
theorem fbTail_inv {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hI : RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a σ)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ.curThread) {x : Fl4Spec.Tcb}
    (hk : σ.kheap ct.bv = some (.tcb x)) (hrx : Fl4Spec.runnable x.tcbState = true)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) (call : Bool) (d e : U64) :
    fbTail (st := st) s ct call d e ⦃ s2 => L.mem s2 (stA ct) ≠ sched.TS_RESTART ∧ L.ksb s2 = L.ksb s ∧
      ∃ z ∈ (specTail call ct.bv [d.bv, e.bv]
        (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)).1,
        RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s2 a z.2 ∧ Sched.SzKeep σ z.2 ⦄ := by
  refine WP.spec_mono (WP.spec_and (fbTail_core s a σ hI ct htcb hcur hk hrx hact call d e)
    (fbTail_ksb s ct call d e)) ?_
  rintro s2 ⟨⟨hne, hI2⟩, hks2⟩
  refine ⟨hne, hks2, ((), Notif.stsAct (Notif.updK σ ct.bv
    (.tcb { (if call then Endp.replyTcb2 x d.bv e.bv else x) with tcbState := .running })) ct.bv), ?_, hI2,
    szKeep_stsAct_tcb _ _ _⟩
  have hk1 : (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv).kheap ct.bv =
      some (.tcb { x with tcbState := .restart }) := by simp [Notif.stsAct_kheap]
  have hsch : ∀ y : Fl4Spec.Tcb, y.tcbSchedContext = x.tcbSchedContext → Fl4Spec.runnable y.tcbState = true →
      Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) =
        Fl4Spec.schedulable ct.bv (Notif.updK σ ct.bv (.tcb y)) := fun y h1 h2 =>
    schedulable_updK_tcb (by rw [h2]; rfl) h1.symm
  unfold specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk1)]
  dsimp only
  cases call
  · rw [Endp.nd_when_false (by simp), Notif.nd_pure_bind']
    try simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Notif.setThreadState_eq .running hk1, stsAct_twice (hsch { x with tcbState := .running } rfl rfl)]
    exact Set.mem_singleton _
  · unfold Fl4Spec.NonDet.when; simp only [↓reduceIte]
    rw [nd_bind_one (Endp.replyFromKernel_two hk1 d.bv e.bv)]
    have hkC : (Notif.updK (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv) ct.bv
        (.tcb (Endp.replyTcb2 { x with tcbState := .restart } d.bv e.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb2 { x with tcbState := .restart } d.bv e.bv)) := by simp
    rw [Notif.setThreadState_eq .running hkC, updK_updK]
    have ey : ({ Endp.replyTcb2 { x with tcbState := .restart } d.bv e.bv with tcbState := .running } : Fl4Spec.Tcb) =
        { Endp.replyTcb2 x d.bv e.bv with tcbState := .running } := rfl
    rw [ey, stsAct_twice (hsch { Endp.replyTcb2 x d.bv e.bv with tcbState := .running } rfl rfl)]
    exact Set.mem_singleton _

end

end

end Fl4Proofs.P3.Vs
