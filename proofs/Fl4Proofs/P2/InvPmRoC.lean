/-
# P2 (line pte, generation 16): `Once` of an accepted PageMap run from the decode on (`roA`, third part)

The walk (`E2E.Once` for the read set `PmRSU s`, user words `K.user`) of the tree `pmRest` (the continuation of
the invoked slot's cap read in `R.invTailPmG`: `R.decPmG`, `R.invPostG`, `after_invocation`, `finish`) at the decode
state `s2` of an accepted run at a `PmPreG` entry:

* `PmRN` / `PmWN`: the guard sets of the decode step, `IoRS (ptU K) s ∪ PmRS s` and `(IoWS (ptU K) s ∪ PmWS s)` off
  `K.user` — no user word, so the whole decode is one `once_gstep` (`pmAccN`: it runs on `guard st PmRN PmWN`);
* **`pm_replyOnce`**: invj's `invU_replyOnce` (P2/InvURoTr.lean) over any `PmNoLk` error, at `IoRS (ptU K)` (the
  `error_mrs` step by `syscall.error_mrs.guardN`; the buffer word read once from the empty touched set, then
  written);
* **`pm_tailOnce`**: invj's `invU_tailOnce` with gen 15's `pmFinG` for the `FinOK` at the reply's end state;
* **`pm_decOnce`**: the decode step, then an `Ok` decode's reply as one more guarded step (`pmAccN`'s reply part),
  or an error decode's `reply_error` (`pm_replyOnce`; the error is a `PmNoLk` one, `dpm_run2`), then the tail.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvPmRoB
import Fl4Proofs.P2.InvPmBlkE
import Fl4Proofs.P2.InvURoTr
import Fl4Proofs.P2.InvPmU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)
open Fl4Proofs.P2.E2E (Once ReadOnce)

noncomputable section

/-- The tree of the PageMap invocation body from the decode on (the continuation of the invoked slot's cap read in
`R.invTailPmG`). -/
noncomputable def pmRest (t : U64) (info : msginfo.MessageInfo) (p : localinv.Plan) (buf length : U64)
    (cap : capability.Cap) : SProg Bool :=
  (R.decPmG info.label length p.slot cap true true true false buf p.extra).sbind fun r =>
    (R.invPostG t r).sbind fun r1 =>
      (R.syscall.after_invocation r1).sbind fun _ =>
        R.syscall.finish.sbind fun _ => SProg.ret true

section sets
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- The decode step's read set: `IoRS (ptU K) s ∪ PmRS s` (no user word). -/
def PmRN (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  IoRS (st := st) K.ptU Locks s b ∨ PmRS st K Locks s b

/-- The decode step's write set: `IoWS (ptU K) s ∪ PmWS s` off `K.user`. -/
def PmWN (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  (IoWS (st := st) K.ptU Locks s b ∨ PmWS st K Locks s b) ∧ b ∉ K.user

end sets

section rest
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- **`reply_error e` read once, for a `PmNoLk` error** (invj's `invU_replyOnce` over any such error; module
docstring): every read but word 7 of the receiver's buffer is an `IoRS (ptU K) s` word (`error_mrs` writes registers
only, `syscall.error_mrs.guardN`); that one user word is read from the empty touched set, then written. -/
theorem pm_replyOnce {s s2 : S} {a1 : A} {Y : Type} {k : Unit → SProg Y} {r' : Y × S × A} {e : error.SysError}
    {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
    (P : IoPre st K.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : GateEp st K s) (he : PmNoLk e)
    (M : InvMid (L := L) (IoRS (st := st) K.ptU Locks s) s s2 (L.curW s))
    (hTail : ∀ x5 Wd' T', syscall.reply_error st s2 (L.curW s) e = ok x5 →
      interp st ar (k ()) x5 a1 = ok r' →
      Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd' T' (k ()) x5 a1)
    (h : interp st ar ((R.syscall.reply_error (L.curW s) e).sbind k) s2 a1 = ok r')
    (Wd : Set U64) :
    Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd ∅
      ((R.syscall.reply_error (L.curW s) e).sbind k) s2 a1 := by
  have hR0 : ∀ q, IoRS (st := st) K.ptU Locks s q → PmRSU st K Locks s q ∧ q ∉ K.user :=
    fun q hq => ⟨pmRSU_ioRS hG hq, fun hu => hq.2.1 (Or.inl hu)⟩
  have hW0 : ∀ q, IoWS (st := st) K.ptU Locks s q → q ∉ K.user := fun q hq hu => P.ioWS_nu hq (Or.inl hu)
  unfold R.syscall.reply_error at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the receiver's buffer
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  refine once_gstep hR0 hW0 (R.msg.lookup_ipc_buffer_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.msg.lookup_ipc_buffer_eq] at h1 ⊢
    rw [msg.lookup_ipc_buffer.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoWS (st := st) K.ptU Locks s))
      s2 true (L.curW s) hbsl M.ib (M.bs _ hbsl).1 (M.bs _ hbsl).2]
    exact h1
  rw [R.msg.lookup_ipc_buffer_eq] at h1
  obtain ⟨b, eb, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- `BADGE`
  refine once_gstep hR0 hW0 (R.obj.Tcb.set_reg_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd2 _ => ?_)
  · rw [R.obj.Tcb.set_reg_eq] at h1 ⊢
    rw [obj.Tcb.set_reg.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoWS (st := st) K.ptU Locks s)) _ s2
      _ _ (P.reg (Locks := Locks) (by simp [layout.reg.BADGE])).2]
    exact h1
  rw [R.obj.Tcb.set_reg_eq] at h1
  obtain ⟨x3, es3, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  -- `error_mrs` (registers only) and the buffer word
  refine once_gstep hR0 hW0 (R.syscall.error_mrs_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd3 _ => ?_)
  · rw [R.syscall.error_mrs_eq] at h1 ⊢
    rw [syscall.error_mrs.guardN (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s)
      (IoWS (st := st) K.ptU Locks s)) x3 (L.curW s) b e he (fun r hr => (P.ioWr (Locks := Locks)).reg r hr)]
    exact h1
  rw [R.syscall.error_mrs_eq] at h1
  obtain ⟨⟨len, x4⟩, em, rfl⟩ := bind_shape h1
  replace h := hk
  dsimp only at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk,
    fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte] at h ⊢
  refine once_ite h (fun hb0 h => ?_) (fun hb0 h => ?_)
  · simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    refine once_liftR h (fun i ei h => ?_)
    unfold R.msg.buf_get at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h ⊢
    simp only [interp] at h
    obtain ⟨w, hv, h⟩ := bok.mp h
    simp only [Once]
    refine ⟨fun _ => Set.notMem_empty _, fun w' hw' => ?_⟩
    rw [hv] at hw'
    obtain rfl := ok_inj_ff hw'
    unfold R.msg.buf_set at h ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.write] at h ⊢
    simp only [interp] at h
    obtain ⟨s4, hs4, h⟩ := bok.mp h
    simp only [Once]
    intro s4' hs4'
    rw [hs4] at hs4'
    obtain rfl := ok_inj_ff hs4'
    refine once_liftR h (fun c ec h => ?_)
    refine once_liftR h (fun mi emi h => ?_)
    refine once_gstep hR0 hW0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoWS (st := st) K.ptU Locks s)) _ _ _
        (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).2]
      exact h1
    rw [R.msg.set_msg_info_eq] at h1
    obtain ⟨x5, es5, rfl⟩ := bind_shape h1
    dsimp only at hk ⊢
    refine hTail x5 _ _ ?_ hk
    unfold syscall.reply_error msg.buf_get msg.buf_set
    simp only [eb, es3, em, bind_ok, lift, uncurry_apply_pair,
      fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte, hb0, ei, ec, hv, hs4, emi, es5]
  · refine once_liftR h (fun c ec h => ?_)
    refine once_liftR h (fun mi emi h => ?_)
    refine once_gstep hR0 hW0 (R.msg.set_msg_info_nz _ _) h (fun r h1 => ?_) (fun r h1 hk Wd5 _ => ?_)
    · rw [R.msg.set_msg_info_eq] at h1 ⊢
      rw [msg.set_msg_info.guard (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoWS (st := st) K.ptU Locks s)) _ _ _
        (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).2]
      exact h1
    rw [R.msg.set_msg_info_eq] at h1
    obtain ⟨x5, es5, rfl⟩ := bind_shape h1
    dsimp only at hk ⊢
    refine hTail x5 _ _ ?_ hk
    unfold syscall.reply_error
    simp only [eb, es3, em, bind_ok, lift, uncurry_apply_pair,
      fl4_abi.config.KERNEL_INVOCATION_REPORT_ERROR_IPC, ↓reduceIte, hb0, ec, Bool.false_eq_true, emi, es5]

/-- **After the reply: `after_invocation (Ok ())` and `finish`** read only `IoRS (ptU K) s` words
(`syscall.finish.guard_resume` with `pmFinG`'s `FinOK` at the reply's end state `z.1`). -/
theorem pm_tailOnce (hA : P0.ArchTotal ar) {p : localinv.Plan} {μ : U64 → U64} {s s1 s2 : S} {a a1 : A}
    {info : msginfo.MessageInfo} {nx buf length : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {r' : Bool × S × A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra =
      ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z)
    (h : interp st ar ((R.syscall.after_invocation (.Ok ())).sbind fun _ =>
      R.syscall.finish.sbind fun _ => SProg.ret true) z.1 z.2.1 = ok r')
    (Wd T : Set U64) :
    Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd T ((R.syscall.after_invocation (.Ok ())).sbind fun _ =>
      R.syscall.finish.sbind fun _ => SProg.ret true) z.1 z.2.1 := by
  have hG := hE.1.2.2
  have P := hE.1.2.1.1.1.1.ptU hG
  obtain ⟨-, F⟩ := pmFinG (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s) (IoWS (st := st) K.ptU Locks s))
    (W := IoWS (st := st) K.ptU Locks s) hA hE (P.ioWr (Locks := Locks)) (SWr.of_W (P.stw (Locks := Locks)).2)
    emi C hcap hy hz
  unfold R.syscall.after_invocation at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep (R0 := IoRS (st := st) K.ptU Locks s) (W0 := IoWS (st := st) K.ptU Locks s)
    (fun q hq => ⟨pmRSU_ioRS hG hq, fun hu => hq.2.1 (Or.inl hu)⟩) (fun q hq hu => P.ioWS_nu hq (Or.inl hu))
    R.syscall.finish_nz h (fun r h1 => ?_) (fun _ _ _ _ _ => by simp only [Once])
  rw [R.syscall.finish_eq] at h1 ⊢
  rw [syscall.finish.guard_resume ar z.1 z.2.1 (nd_at (fun o h1 h2 => P.nd (Locks := Locks) o h1 h2) F.k F.c) F.nd
    F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
  exact h1

/-- **The decode onward of an accepted PageMap run reads once** (module docstring). -/
theorem pm_decOnce (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {μ : U64 → U64} {s s1 s2 : S}
    {a a1 : A} {info : msginfo.MessageInfo} {nx buf length : U64} {cap : capability.Cap} {r' : Bool × S × A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s)
    (hac : ∃ s' a', syscall.handle_invocation_local st ar s a number p = ok (true, s', a'))
    (emi : msg.msg_info st s (L.curW s) = ok info) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (ecap : obj.Slot.cap st p.slot s2 = ok cap)
    (h : interp st ar (pmRest (L.curW s) info p buf length cap) s2 a1 = ok r') (Wd : Set U64) :
    Once st ar (PmRSU st K Locks s) (· ∈ K.user) Wd ∅ (pmRest (L.curW s) info p buf length cap) s2 a1 := by
  have hG := hE.1.2.2
  have hq := hE.1.2.1
  have P := hE.1.2.1.1.1.1.ptU hG
  obtain ⟨sA, aA, h0⟩ := hac
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx s1 s2 a1 emi C.1 C.2.1 C.2.2.1
  obtain ⟨fp, rt, asid, va, mp, x0, root, rasid, e, -, hcs2, -⟩ := pm_s2 hA hE C
  have hcap' : cap = .Frame fp .Small rt false mp false asid va := by
    have := ecap; rw [hcs2] at this; exact (ok_inj_ff this).symm
  subst hcap'
  obtain ⟨-, -, -, -, -, -, -, hlab, -, -⟩ := pm_core hq
  have hlbl := (hlab info emi).1
  have hdI : ∀ m : machine.Store S, interp m ar (R.decPmG info.label length p.slot
      (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra) s2 a1 =
      (syscall.decode_invocation m ar s2 a1 info.label length p.slot (.Frame fp .Small rt false mp false asid va)
        true true true false buf p.extra >>= fun r => ok (r.1, r.2.1, r.2.2)) := by
    intro m
    rw [R.decPmG_eq, hlbl, decInv_eq_Pm]
  have hR0 : ∀ q, PmRN st K Locks s q → PmRSU st K Locks s q ∧ q ∉ K.user := by
    intro q hq'
    rcases hq' with hq' | hq'
    · exact ⟨pmRSU_ioRS hG hq', fun hu => hq'.2.1 (Or.inl hu)⟩
    · exact ⟨pmRS_U hq', hq'.2.1⟩
  have hW0 : ∀ q, PmWN st K Locks s q → q ∉ K.user := fun q hq' => hq'.2
  have hW : IoWr st (PmWN st K Locks s) K.heap.scBits s :=
    (P.ioWr (Locks := Locks)).mono (fun b hb => ⟨Or.inl hb, fun hu => P.ioWS_nu hb (Or.inl hu)⟩)
  have hAcc := fun (y : (core.result.Result Unit error.Exc) × S × A)
      (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot
        (.Frame fp .Small rt false mp false asid va) true true true false buf p.extra = ok y) =>
    pmAccN (R := PmRN st K Locks s) (W := PmWN st K Locks s)
      (gS := PathObl.guard st (PmRN st K Locks s) (PmWN st K Locks s)) hA hE (fun _ h => Or.inl h)
      (fun _ h => Or.inr h) hW (fun b hb => ⟨Or.inl hb, fun hu => P.ioWS_nu hb (Or.inl hu)⟩)
      (fun b hb hu => ⟨Or.inr hb, hu⟩) emi C ecap hy
  unfold pmRest at h ⊢
  refine once_gstep hR0 hW0 (R.decPmG_nz _ _ _ _ _ _ _ _ _ _) h (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [hdI] at h1 ⊢
    obtain ⟨y, hy, -⟩ := bind_eq_ok h1
    rw [(hAcc _ hy).1]
    rw [hy] at h1
    exact h1
  rw [hdI] at h1
  obtain ⟨y, hy, rfl⟩ := bind_shape h1
  obtain ⟨-, hrep, herr⟩ := hAcc _ hy
  obtain ⟨yr, yx, ya⟩ := y
  dsimp only at hk ⊢
  cases yr with
  | Ok u =>
    cases u
    refine once_gstep hR0 hW0 (R.invPostG_nz _ _) hk (fun r h2 => ?_) (fun r h2 hk2 Wd2 _ => ?_)
    · rw [R.invPostG_eq] at h2 ⊢
      obtain ⟨z, hz, -⟩ := bind_eq_ok h2
      have hg2 : invPostG (PathObl.guard st (PmRN st K Locks s) (PmWN st K Locks s)) yx ya (L.curW s) (.Ok ()) =
          ok z := hrep rfl z hz
      rw [hg2]
      rw [hz] at h2
      exact h2
    rw [R.invPostG_eq] at h2
    obtain ⟨z, hz, rfl⟩ := bind_shape h2
    dsimp only at hk2 ⊢
    have hz' : invRep st (L.curW s) yx ya (.Ok ()) = ok z := hz
    obtain ⟨hz2, -⟩ := pmFinG (gS := PathObl.guard st (IoRS (st := st) K.ptU Locks s)
      (IoWS (st := st) K.ptU Locks s)) (W := IoWS (st := st) K.ptU Locks s) (y := (.Ok (), yx, ya)) hA hE
      (P.ioWr (Locks := Locks)) (SWr.of_W (P.stw (Locks := Locks)).2) emi C ecap hy hz'
    rw [hz2] at hk2 ⊢
    exact pm_tailOnce hA hE emi C ecap hy hz' hk2 Wd2 ∅
  | Err er =>
    obtain ⟨hx, ha, se, rfl, hnl⟩ := herr er rfl
    dsimp only at hx ha
    subst hx ha
    unfold R.invPostG at hk ⊢
    simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk] at hk ⊢
    refine pm_replyOnce P hG hnl M (fun x5 Wd' T' er hk' => ?_) hk Wd1
    have hz : invRep st (L.curW s) yx ya (.Err (.Sys se)) = ok (x5, ya, .Ok ()) := by
      unfold invRep
      simp only [er, bind_ok, uncurry_apply_pair]
      try rfl
    exact pm_tailOnce (z := (x5, ya, .Ok ())) hA hE emi C ecap hy hz hk' Wd' T'

end rest

end
end Fl4Proofs.P2.E2EP
