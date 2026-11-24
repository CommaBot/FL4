/-
# P2: the I/O port invocation's write footprint (line p2io)

On the I/O port run `handle_invocation` (and `after_invocation` of `Ok`, which
does nothing) writes only the current thread's register and `STATE` words
(`IoTW t`: TCB offsets 256..3328), and leaves the action `RESUME_CURRENT`:
every `set_thread_state` it runs sets a runnable state (`RESTART` /
`RUNNING`) and then `schedule_tcb` finds the thread schedulable (bound to an
active SC, not in the release queue: facts at the invocation's entry state the
writes cannot change, `SchedOK`), so it never writes `SCHED_ACTION`.

* `IoTW`, `iotw_field`, `iotw_aligned`; `KeepA s0 t x`: `WritesIn s0 x (IoTW t)` and
  the action `RESUME_CURRENT`, `t`'s state `RESTART` / `RUNNING`;
* `KeepA.wr_reg`, `KeepA.wr_st`, `KeepA.sts` (one write each);
* `ioInTail_keepA`, `ioOutTail_keepA`, `ioArm_keepA`;
* `io_inv_keep`: the whole invocation, from a passing `invocation_ok` at the
  same state with no extra caps.

Premises: none (`SchedOK` is a hypothesis, discharged at the path's entry).
-/
import Fl4Proofs.P2.AccessIoPath
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The register and `STATE` words of `t`. -/
def IoTW (t b : U64) : Prop := (∃ r : U64, r.val < 384 ∧ b = regA t r) ∨ b = stA t

theorem st_val : layout.tcb.STATE.val = 3328 := by simp [layout.tcb.STATE]

theorem iotw_field {t K : U64} (hT : TcbAddr t) (hK : K.val < 4096) (hge : 3328 < K.val) :
    ¬ IoTW t (core.num.U64.wrapping_add t K) := by
  rintro (⟨r, hr, e⟩ | e)
  · have := congrArg UScalar.val e
    rw [tcb_wadd_val hT hK, regA_val hT hr] at this; omega
  · have := congrArg UScalar.val e
    unfold stA at this
    rw [tcb_wadd_val hT hK, tcb_wadd_val hT (by rw [st_val]; omega), st_val] at this; omega

theorem iotw_aligned {t b : U64} (hT : TcbAddr t) (h : IoTW t b) : Aligned b := by
  rcases h with ⟨r, hr, rfl⟩ | rfl
  · obtain ⟨K, hK, e⟩ := regA_eq hT hr
    rw [e]; exact field_aligned hT (by omega) (by omega)
  · unfold stA; exact field_aligned hT (by rw [st_val]; omega) (by rw [st_val])

/-- From `s0`: only `IoTW t` written, the action `RESUME_CURRENT`. -/
def KeepA (s0 : S) (t : U64) (x : S) : Prop :=
  WritesIn st s0 x (IoTW t) ∧ L.actionW x = sched.ACTION_RESUME_CURRENT ∧
    (L.mem x (stA t) = sched.TS_RESTART ∨ L.mem x (stA t) = sched.TS_RUNNING)

/-- The facts at the invocation's entry `s0` that keep `schedule_tcb t` from
writing: `t` the current thread, bound to an active SC, not in the release
queue; the node's words and the SC's `REFILL_MAX` word outside `IoTW t`. -/
structure SchedOK (s0 : S) (t : U64) : Prop where
  tcb : TcbAddr t
  cur : L.curW s0 = t
  sc : L.mem s0 (scA t) ≠ 0#u64
  act : L.rmax s0 (L.mem s0 (scA t)) ≠ 0#u64
  nr : (L.mem s0 (inqA t) &&& sched.Q_RELEASE) = 0#u64
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
    Aligned (L.nodeAt s0 (L.cpu s0) o) ∧ ¬ IoTW t (L.nodeAt s0 (L.cpu s0) o)
  mx : Aligned (maxA (L.mem s0 (scA t))) ∧ ¬ IoTW t (maxA (L.mem s0 (scA t)))

variable {s0 x : S} {t : U64}

theorem KeepA.refl (ha : L.actionW s0 = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem s0 (stA t) = sched.TS_RESTART ∨ L.mem s0 (stA t) = sched.TS_RUNNING) : KeepA (L := L) s0 t s0 :=
  ⟨WritesIn.refl _ _, ha, hr⟩

theorem KeepA.node (h : KeepA (L := L) s0 t x) (o : U64) :
    L.nodeAt x (L.cpu x) o = L.nodeAt s0 (L.cpu s0) o := by
  rw [h.1.2.1, nodeAt_of_ksb h.1.1]

theorem KeepA.mem (h : KeepA (L := L) s0 t x) {b : U64} (hb : Aligned b) (hn : ¬ IoTW t b) :
    L.mem x b = L.mem s0 b := h.1.2.2 b hb hn

theorem KeepA.cur (F : SchedOK (L := L) s0 t) (h : KeepA (L := L) s0 t x) : L.curW x = t := by
  have hn := F.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  unfold LawfulStore.curW
  rw [h.node, h.mem hn.1 hn.2]; exact F.cur

theorem KeepA.wr {b v : U64} (F : SchedOK (L := L) s0 t) (h : KeepA (L := L) s0 t x) (hb : IoTW t b)
    (hs : b = stA t → v = sched.TS_RESTART ∨ v = sched.TS_RUNNING) : KeepA (L := L) s0 t (L.wr x b v) := by
  have ha : Aligned b := iotw_aligned F.tcb hb
  refine ⟨h.1.trans1 ((writesIn_wr ha).mono fun b' hb' => by subst hb'; exact hb), ?_, ?_⟩
  swap
  · by_cases e : b = stA t
    · subst e; rw [L.mem_wr_same ha]; exact hs rfl
    · rw [mem_wr_ne' ha (iotw_aligned F.tcb (Or.inr rfl)) e]; exact h.2.2
  have hsa := F.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  unfold LawfulStore.actionW
  rw [nd_wr, h.node, mem_wr_ne' ha hsa.1 (fun e => hsa.2 (by rw [← e]; exact hb)), ← h.node]
  exact h.2.1

theorem KeepA.wr_reg {r v : U64} (F : SchedOK (L := L) s0 t) (h : KeepA (L := L) s0 t x) (hr : r.val < 384) :
    KeepA (L := L) s0 t (L.wr x (regA t r) v) := h.wr F (Or.inl ⟨r, hr, rfl⟩) fun e => by
    have := congrArg UScalar.val e
    unfold stA at this
    rw [regA_val F.tcb hr, tcb_wadd_val F.tcb (by rw [st_val]; omega), st_val] at this; omega

theorem KeepA.sts {x1 : S} {v : U64} (F : SchedOK (L := L) s0 t) (h : KeepA (L := L) s0 t x)
    (hv : v = sched.TS_RESTART ∨ v = sched.TS_RUNNING)
    (e : sched.set_thread_state st x t v = ok x1) : KeepA (L := L) s0 t x1 := by
  unfold sched.set_thread_state at e
  rw [set_state_ok'] at e; simp only [bind_ok] at e
  have h1 : KeepA (L := L) s0 t (L.wr x (stA t) v) := h.wr F (Or.inr rfl) fun _ => hv
  have hst : L.mem (L.wr x (stA t) v) (stA t) = v := L.mem_wr_same (iotw_aligned F.tcb (Or.inr rfl))
  have hsc : L.mem (L.wr x (stA t) v) (scA t) = L.mem s0 (scA t) :=
    h1.mem (field_aligned F.tcb (by simp) (by simp)) (iotw_field F.tcb (by simp) (by simp))
  have hiq : L.mem (L.wr x (stA t) v) (inqA t) = L.mem s0 (inqA t) :=
    h1.mem (field_aligned F.tcb (by simp) (by simp)) (iotw_field F.tcb (by simp) (by simp))
  have hmx : L.rmax (L.wr x (stA t) v) (L.mem s0 (scA t)) = L.rmax s0 (L.mem s0 (scA t)) := by
    unfold LawfulStore.rmax
    exact h1.mem F.mx.1 F.mx.2
  have hcur := h1.cur F
  have hac := h1.2.1
  revert e h1 hst hsc hiq hmx hcur hac
  generalize L.wr x (stA t) v = y
  intro e h1 hst hsc hiq hmx hcur hac
  have hpos : L.rmax s0 (L.mem s0 (scA t)) > 0#u64 := by
    have := F.act; scalar_tac
  have hsch : sched.is_schedulable st y t = ok true := by
    unfold sched.is_schedulable sched.is_runnable
    rw [state_ok', hst]
    rcases hv with rfl | rfl <;>
    simp only [bind_ok, tcb_sc_ok, hsc, obj.Sc.is_null, F.sc, decide_false, sporadic.sc_active,
      eq_of_spec_fd (obj.Sc.refill_max.spec (L := L) y _), hmx, hpos, inrel_ok, hiq, F.nr,
      ne_eq, not_true_eq_false, decide_true, Bool.not_false, ↓reduceIte, Bool.false_eq_true,
      sched.TS_RESTART, sched.TS_RUNNING] <;>
    simp only [ite_self, bind_ok, not_false_eq_true, decide_true, ↓reduceIte]
  unfold sched.schedule_tcb at e
  rw [cur_thread_ok, hcur] at e
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok, decide_true, ↓reduceIte] at e
  rw [eq_of_spec_fd (sched.action.spec (L := L) y), hac] at e
  simp only [bind_ok, ↓reduceIte, hsch] at e
  rw [← ok_inj_ff e]; exact h1

theorem rB384 : layout.reg.BADGE.val < 384 := lt384 (Or.inr (Or.inr (Or.inl rfl)))
theorem rM384 : layout.reg.MSG_INFO.val < 384 := lt384 (Or.inr (Or.inr (Or.inr rfl)))
theorem rR384 : layout.reg.R10.val < 384 := lt384 (Or.inl rfl)

theorem ioInTail_keepA {A : Type} (ar : machine.Arch A) {a : A} {port size : U64} {call : Bool}
    {y : (core.result.Result Unit error.Exc) × S × A} (F : SchedOK (L := L) s0 t) (hk : KeepA (L := L) s0 t x)
    (h : ioInTail st ar x a t port size call = ok y) : KeepA (L := L) s0 t y.2.1 := by
  unfold ioInTail at h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok h
  have k1 := hk.sts F (Or.inl rfl) hs1
  obtain ⟨⟨v, a1⟩, -, h⟩ := bind_eq_ok h
  try simp only [Aeneas.Std.uncurry_apply_pair] at h
  obtain ⟨s2, hs2, h⟩ := bind_eq_ok h
  have k2 : KeepA (L := L) s0 t s2 := by
    cases call
    · rw [if_neg Bool.false_ne_true] at hs2
      cases ok_inj_ff hs2; exact k1
    · rw [if_pos rfl] at hs2
      obtain ⟨b, -, hs2⟩ := bind_eq_ok hs2
      rw [set_reg_ok'] at hs2; simp only [bind_ok] at hs2
      rw [set_mr0_ok] at hs2; simp only [bind_ok, Aeneas.Std.uncurry_apply_pair] at hs2
      obtain ⟨mi, -, hs2⟩ := bind_eq_ok hs2
      unfold msg.set_msg_info at hs2
      obtain ⟨w, -, hs2⟩ := bind_eq_ok hs2
      rw [set_reg_ok'] at hs2
      cases ok_inj_ff hs2
      exact ((k1.wr_reg F rB384).wr_reg F rR384).wr_reg F rM384
  obtain ⟨s3, hs3, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]
  exact k2.sts F (Or.inr rfl) hs3

theorem ioOutTail_keepA {A : Type} (ar : machine.Arch A) {a : A} {port size raw : U64}
    {y : (core.result.Result Unit error.Exc) × S × A} (F : SchedOK (L := L) s0 t) (hk : KeepA (L := L) s0 t x)
    (h : ioOutTail st ar x a t port size raw = ok y) : KeepA (L := L) s0 t y.2.1 := by
  unfold ioOutTail at h
  obtain ⟨d, -, h⟩ := bind_eq_ok h
  obtain ⟨s1, hs1, h⟩ := bind_eq_ok h
  obtain ⟨a1, -, h⟩ := bind_eq_ok h
  rw [← ok_inj_ff h]
  exact hk.sts F (Or.inl rfl) hs1

theorem ioArm_keepA {A : Type} (ar : machine.Arch A) {a : A} {lbl len f l buf : U64} {call : Bool}
    {y : (core.result.Result Unit error.Exc) × S × A} (F : SchedOK (L := L) s0 t) (hk : KeepA (L := L) s0 t x)
    (h : ioArm st ar x a lbl len f l buf call = ok y) : KeepA (L := L) s0 t y.2.1 := by
  unfold ioArm at h
  rw [cur_thread_ok, hk.cur F] at h
  simp only [bind_ok] at h
  obtain ⟨size, -, h⟩ := bind_eq_ok h
  split at h
  · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  split at h
  · split at h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    simp only [lift, bind_ok] at h
    obtain ⟨r, -, h⟩ := bind_eq_ok h
    obtain ⟨cf, -, h⟩ := bind_eq_ok h
    split at h
    · exact ioInTail_keepA ar F hk h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
  · split at h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    simp only [lift, bind_ok] at h
    obtain ⟨raw, -, h⟩ := bind_eq_ok h
    obtain ⟨r, -, h⟩ := bind_eq_ok h
    obtain ⟨cf, -, h⟩ := bind_eq_ok h
    split at h
    · exact ioOutTail_keepA ar F hk h
    · obtain ⟨r, -, h⟩ := bind_eq_ok h; rw [← ok_inj_ff h]; exact hk

/-- **The I/O port invocation's footprint**: after a passing `invocation_ok`
at the same state with no extra caps, `handle_invocation` writes only `IoTW t`
and leaves the action `RESUME_CURRENT`. -/
theorem io_inv_keep {A : Type} (ar : machine.Arch A) {a : A} {cptr : U64} {info : msginfo.MessageInfo}
    {call blocking cd fp : Bool} {y : (core.result.Result Unit error.Exc) × S × A}
    (F : SchedOK (L := L) s0 t) (ha : L.actionW s0 = sched.ACTION_RESUME_CURRENT)
    (hr : L.mem s0 (stA t) = sched.TS_RESTART ∨ L.mem s0 (stA t) = sched.TS_RUNNING)
    (hmi : msg.msg_info st s0 t = ok info) (hx : info.extra_caps = 0#u64)
    (hinv : ioport.invocation_ok st s0 t cptr info = ok true)
    (h : syscall.handle_invocation st ar s0 a call blocking cd fp cptr = ok y) :
    KeepA (L := L) s0 t y.2.1 := by
  have hk : KeepA (L := L) s0 t s0 := KeepA.refl ha hr
  have hc := F.cur
  subst hc
  obtain ⟨r1, f, l, x, buf, len, size, b, i1, hres, hc, hbuf, hlen, hsz, hz, hb, hl, hi1, hal⟩ :=
    inv_true hinv
  have hlen' : (if info.length > msg.N_MSG_REGISTERS
      then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok len := hlen
  unfold syscall.handle_invocation at h
  rw [cur_thread_ok] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [hmi] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [hres] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [hc] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [hbuf] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [extra_zero_ok s0 _ buf info hx] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [hlen'] at h
  simp only [bind_ok, bind_tc_ok] at h
  rw [decode_inv_ioport_eq] at h
  rw [cur_thread_ok] at h
  simp only [bind_ok, bind_tc_ok] at h
  obtain ⟨⟨r3, s1, a1⟩, hd, h⟩ := bind_eq_ok h
  rw [decode_ioport_eq] at hd
  have e3 : r3 = .Ok () := ioArm_fst ar hsz hz hb hl hi1 hal hd
  have k1 := ioArm_keepA ar F hk hd
  simp only at k1
  subst e3
  try simp only [bind_ok, bind_tc_ok] at h
  try simp only [Aeneas.Std.uncurry_apply_pair] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  split at h
  · obtain ⟨s2, hs2, h⟩ := bind_eq_ok h
    obtain ⟨s3, hs3, h⟩ := bind_eq_ok h
    rw [← ok_inj_ff h]
    have k2 : KeepA (L := L) s0 (L.curW s0) s2 := by
      cases call
      · rw [if_neg Bool.false_ne_true] at hs2
        cases ok_inj_ff hs2; exact k1
      · rw [if_pos rfl] at hs2
        unfold msg.reply_success_empty at hs2
        rw [set_reg_ok'] at hs2; simp only [bind_ok] at hs2
        obtain ⟨mi, -, hs2⟩ := bind_eq_ok hs2
        unfold msg.set_msg_info at hs2
        obtain ⟨w, -, hs2⟩ := bind_eq_ok hs2
        rw [set_reg_ok'] at hs2
        cases ok_inj_ff hs2
        exact (k1.wr_reg F rB384).wr_reg F rM384
    exact k2.sts F (Or.inr rfl) hs3
  · rw [← ok_inj_ff h]; exact k1

/-- A word `K` (3328 < K < 4096) of any TCB `h` is not in `IoTW t`. -/
theorem iotw_tcb {t h K : U64} (hT : TcbAddr t) (hh : TcbAddr h) (hK : K.val < 4096) (hge : 3328 < K.val) :
    ¬ IoTW t (core.num.U64.wrapping_add h K) := by
  have a1 := hT.align; have a2 := hh.align
  rintro (⟨r, hr, e⟩ | e)
  · have := congrArg UScalar.val e
    rw [tcb_wadd_val hh hK, regA_val hT hr] at this; omega
  · have := congrArg UScalar.val e
    unfold stA at this
    rw [tcb_wadd_val hh hK, tcb_wadd_val hT (by rw [st_val]; omega), st_val] at this; omega

/-- The queue heads `finish` reads, outside `IoTW t` (at the invocation's
entry `s0`): the earliest timer and the release head are TCBs, and the
release head's SC head words are aligned and outside `IoTW t`. -/
structure QOK (s0 : S) (t : U64) : Prop where
  tm : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 → TcbAddr (L.mem s0 (tmA (L := L) s0))
  rh : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → TcbAddr (L.mem s0 (rhA (L := L) s0))
  hd : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 →
    Aligned (headA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))) ∧
      ¬ IoTW t (headA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))) ∧
    Aligned (rtA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))
      (L.rhead s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))))) ∧
      ¬ IoTW t (rtA (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))
        (L.rhead s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))))

theorem KeepA.nd (F : SchedOK (L := L) s0 t) (h : KeepA (L := L) s0 t x) (o : U64) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) : L.mem x (L.nodeAt x (L.cpu x) o) = L.mem s0 (L.nodeAt s0 (L.cpu s0) o) := by
  rw [h.node]; exact h.mem (F.nd o ho h8).1 (F.nd o ho h8).2

/-- **`finish`'s queue reads survive the invocation**: `NoDue` and the
deadline / release-head read facts at `s0` hold at `x`. -/
theorem KeepA.fin (F : SchedOK (L := L) s0 t) (Q : QOK (L := L) s0 t) (h : KeepA (L := L) s0 t x)
    {R : U64 → Prop} (hnd : NoDue (L := L) s0)
    (htd : L.mem s0 (tmA (L := L) s0) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s0 (tmA (L := L) s0)) 3528#u64))
    (hrs : L.mem s0 (rhA (L := L) s0) ≠ 0#u64 → R (scA (L.mem s0 (rhA (L := L) s0))) ∧
      RdHead (L := L) R s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))))) :
    NoDue (L := L) x ∧
    (L.mem x (tmA (L := L) x) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem x (tmA (L := L) x)) 3528#u64)) ∧
    (L.mem x (rhA (L := L) x) ≠ 0#u64 → R (scA (L.mem x (rhA (L := L) x))) ∧
      RdHead (L := L) R x (L.mem x (scA (L.mem x (rhA (L := L) x))))) := by
  have eT : L.mem x (tmA (L := L) x) = L.mem s0 (tmA (L := L) s0) :=
    h.nd F _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have eR : L.mem x (rhA (L := L) x) = L.mem s0 (rhA (L := L) s0) :=
    h.nd F _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have eC : L.curTime x = L.curTime s0 := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    exact h.nd F _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have eS : ∀ h0 : L.mem s0 (rhA (L := L) s0) ≠ 0#u64,
      L.mem x (scA (L.mem s0 (rhA (L := L) s0))) = L.mem s0 (scA (L.mem s0 (rhA (L := L) s0))) := fun h0 =>
    h.mem (field_aligned (Q.rh h0) (by simp) (by simp)) (iotw_tcb F.tcb (Q.rh h0) (by simp) (by simp))
  have eH : ∀ h0 : L.mem s0 (rhA (L := L) s0) ≠ 0#u64,
      L.rhead x (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))) =
        L.rhead s0 (L.mem s0 (scA (L.mem s0 (rhA (L := L) s0)))) := fun h0 => by
    unfold LawfulStore.rhead; exact h.mem (Q.hd h0).1 (Q.hd h0).2.1
  obtain ⟨n1, n2⟩ := hnd
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show L.mem x (tmA (L := L) x) = 0#u64 ∨ L.mem x (L.nodeAt x (L.cpu x) layout.node.CUR_TIME) <
      L.mem x (tdA (L.mem x (tmA (L := L) x)))
    rw [eT, h.nd F _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
    by_cases h0 : L.mem s0 (tmA (L := L) s0) = 0#u64
    · exact Or.inl h0
    right
    unfold tdA
    rw [h.mem (field_aligned (Q.tm h0) (by simp) (by simp)) (iotw_tcb F.tcb (Q.tm h0) (by simp) (by simp))]
    exact n1.resolve_left h0
  · show L.mem x (rhA (L := L) x) = 0#u64 ∨ ¬ ((L.refill x (L.mem x (scA (L.mem x (rhA (L := L) x))))
      (L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))))).time ≤ L.curTime x)
    rw [eR, eC]
    by_cases h0 : L.mem s0 (rhA (L := L) s0) = 0#u64
    · exact Or.inl h0
    right
    rw [eS h0, eH h0]
    unfold LawfulStore.refill
    simp only
    rw [h.mem (Q.hd h0).2.2.1 (Q.hd h0).2.2.2]
    exact n2.resolve_left h0
  · rw [eT]; exact htd
  · rw [eR]; intro h0
    refine ⟨(hrs h0).1, ?_⟩
    rw [eS h0]
    unfold RdHead; rw [eH h0]; exact (hrs h0).2

end

end Fl4Proofs.P2.PathObl
