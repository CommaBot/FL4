/-
P3 (line stpost, generation 4): **the ReplyRecv mid state from an accepted fast path**
(StPostRecv's `hMid`).

From a dispatch state `X0` where `fastpath.reply_recv` accepts, with P1's read bundle `RRPre`
(FastRRSame), the placement `RRPl` at every accepted run's checks and the refill-sum bound `RRSum`
(the inputs `rrPre_of_lk` / `rrPre5_ofG` already take), the general path's `handle_invocation`
on the REPLY register ends at the fast run's `X8` (P1 `handle_invocation_rr`, as in
`rr_found_sameG`) and `X8` carries StPostRecv's `RRMidSt`:

* `ct8`, `lk8`, `rt8`, `ep8`, `act8` (≠ RESUME_CURRENT): `RRReads`'s fields;
* the action word ≠ CHOOSE_NEW: `rr_x8G`'s `actionW X8 = u` and `RRReads.ucn`;
* the bound notification: `RRReads.ntfn8` (not active) and **`P1.rr_ntfnSc8`** (new): the
  fast path's check at `X0` (the notification's SC null or not `t`'s) carried to `X8` by
  `rr_x8G`'s `FinKeep` (the notification's SC word an `Ω` word, `t`'s SC word a TCB word above
  the state), as `rr_x8G` derives `ntfn8`.

No premise.
-/
import Fl4Proofs.P3.StPostRecv
import Fl4Proofs.P1.FastRRSame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

set_option maxHeartbeats 1600000 in
/-- (stpost) **The bound notification's SC word at `X8`** (module docstring): the fast path's
check at `X0` carried by `FinKeep`. -/
theorem rr_ntfnSc8 {ty : U64} {X0 X8 : S} {a : A} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (C : RRChecksG st ar ty X0 a t rptr ep u usc)
    (K8 : FinKeep (L := L) T (RΩ Ω Rp) X0 X8 rptr usc (Z usc)) :
    L.mem X8 (boundA t) = L.mem X0 (boundA t) ∧
    (L.mem X0 (boundA t) = 0#u64 ∨ L.mem X8 (ntfnScA (L.mem X0 (boundA t))) = 0#u64 ∨
      L.mem X8 (ntfnScA (L.mem X0 (boundA t))) ≠ L.mem X8 (scA t)) := by
  have ebd : L.mem X8 (boundA t) = L.mem X0 (boundA t) :=
    K8.tcb t P.ht 3368#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have esct : L.mem X8 (scA t) = L.mem X0 (scA t) := K8.tw P.ht 3464#u64 (by decide)
  refine ⟨ebd, ?_⟩
  rcases C.ntfn with ⟨i, hi, hc⟩ | ⟨i, hi, hc, i7, h7, hn7, i8, h8, hsc⟩
  · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X0 t)] at hi
    left; rw [ok_inj_ff hi]; exact UScalar.eq_of_val_eq (by simpa using hc)
  · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) X0 t)] at hi
    have ei := ok_inj_ff hi; subst ei
    have h0 : L.mem X0 (boundA t) ≠ 0#u64 := by simpa using hc
    obtain ⟨hnN, hnE, hnEN, hnΩ⟩ := P.hNt h0
    right
    have hnS := P.hO.ntW _ hnN
    have eNs : L.mem X8 (ntfnScA (L.mem X0 (boundA t))) = L.mem X0 (ntfnScA (L.mem X0 (boundA t))) := by
      refine K8.omg _ ⟨P.hSg.sub _ hnS, ?_⟩ ?_ ?_
      · rintro ⟨r', hr', e | e⟩
        · have := P.hO.ntRp _ hnN r' hr'; rw [e, rPrevA_val (P.hO.rp r' hr')] at this; omega
        · have := P.hO.ntRp _ hnN r' hr'; rw [e, rNextA_val (P.hO.rp r' hr')] at this; omega
      · intro e; have := P.hO.ntRp _ hnN rptr P.hrR; rw [e, rTcbA_val0] at this; omega
      · intro hin; have := P.hO.ntSc _ hnN usc P.hcS; unfold InRing at hin; omega
    rw [eq_of_spec_fd (obj.Ntfn.sc.val (L := L) X0 _)] at h8
    have e8 := ok_inj_ff h8
    rw [eNs, esct, e8]
    rcases hsc with h0' | ⟨h0', i9, h9, hne⟩
    · left; exact UScalar.eq_of_val_eq (by simpa using h0')
    · right
      rw [tcb_sc_ok] at h9
      rw [ok_inj_ff h9]; exact hne

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 3200000 in
/-- (stpost) **StPostRecv's `hMid` at an accepted ReplyRecv dispatch state** (module
docstring). -/
theorem rrMid_of {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {X0 s' : S} {a a' : A}
    (h : fastpath.reply_recv st arI X0 a = ok (true, s', a'))
    (hP : P1.RRPre (L := L) arI X0 a)
    (hPl : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      P1.RRChecks st arI X0 a t rptr ep u usc → P1.RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : P1.RRSum (L := L) Scs X0) :
    ∃ (t : U64) (X8 : S) (a8 : A) (rptr ep : U64), sched.cur_thread st X0 = ok t ∧
      syscall.handle_invocation st arI X0 a false false true true (L.mem X0 (regA t layout.reg.REPLY)) =
        ok (.Ok (), X8, a8) ∧ RRMidSt (st := st) X8 t rptr ep := by
  obtain ⟨t, rptr, ep, hct, hrc, hf⟩ := P1.reply_recv_acc st arI h
  obtain ⟨u, usc, hC, hT⟩ := P1.reply_recv_found_acc st arI hf
  have hRC := P1.reply_caps_some st hrc
  have Pl := hPl t rptr ep u usc hct hrc hC
  obtain ⟨X1, X2, a1, b9, X3, restart, X4, a2, X5, X6, X7, X8, X9, X10, X11, X12, X13, X14, X15,
    e1, e2, e3s, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16⟩ := P1.rrTail_split st arI hT
  obtain ⟨R3, hR⟩ := hP t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3
  obtain ⟨hrs, -⟩ := P1.HfrRestart.restart (st := st) (ar := arI) R3.ft3 R3.lbl3 e4
  subst hrs
  rw [if_pos rfl] at e6
  have R := hR X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  obtain ⟨-, -, K8, -, -, -, -, -, -, -, -, -, hact8, -, -, -, -, -⟩ :=
    P1.rr_x8G arI Pl hC (hS usc Pl.hcS) e1 e2 e3s e3 e4 e5 e6 e7 e8
  obtain ⟨ebd, hnsc⟩ := P1.rr_ntfnSc8 arI Pl hC K8
  have hun : obj.Tcb.is_null u = ok false := by
    obtain ⟨b, hb, hbn⟩ := hC.u0
    rw [Bool.not_eq_true] at hbn; subst hbn; exact hb
  have husc : obj.Sc.is_null usc = ok false := by
    obtain ⟨b, hb, hbn⟩ := hC.sc0
    rw [Bool.not_eq_true] at hbn; subst hbn; exact hb
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, -⟩⟩ := hRC
  have hls : cspace.lookup_slot st X0 t i = ok (core.result.Result.Ok found) := by
    unfold cspace.lookup_slot
    rw [hsl]; simp only [bind_ok]
    rw [hroot]; simp only [bind_ok]
    exact hr
  obtain ⟨info, hmi, hex, -⟩ := hC.info
  have hex' : info.extra_caps = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hex
  obtain ⟨buf, hbuf, -⟩ := P1.spec_ex_fd (P0.msg.lookup_ipc_buffer.p0 st X0 false t L.total)
  have hdrt := P1.do_reply_transfer_rrG st arI (t := t) (g := g) (hty0 := P1.unknown_ne_null) R.rt1 hun R.us1 e2
    R.sc2 e3s e3 R3.ft3 e4 e5 e6 R.sch6 R.sc6 husc R.run6 R.rdy6 R.suf6 R.pst
  have hinv := P1.handle_invocation_rr st arI hct hmi hex' hls hc hbuf e1
    (P1.schedule_tcb_sch (L := L) X1 t R.sch1) hdrt R.st7 e8 (P1.schedule_tcb_nr (L := L) X8 t R.act8)
  have hiv : i = L.mem X0 (regA t layout.reg.REPLY) := by
    rw [P1.reg_ok] at hi; exact (P1.ok_inj_ff hi).symm
  subst hiv
  refine ⟨t, X8, a2, rptr, ep, hct, hinv, ?_⟩
  obtain ⟨j, j1, c0, c1, c3, c4, g', hj1, hlk1, hj, hlk2⟩ := R.lk8
  rw [P1.reg_ok] at hj1 hj
  have ej1 := P1.ok_inj_ff hj1
  have ej := P1.ok_inj_ff hj
  subst ej1 ej
  obtain ⟨n, hbn, hnc⟩ := R.ntfn8
  rw [P1.eq_of_spec_fd (P1.obj.Tcb.bound_ntfn.val (L := L) X8 t)] at hbn
  have en := P1.ok_inj_ff hbn
  subst en
  refine ⟨R.ct8, ?_, ?_, ⟨c0, c1, c3, c4, g', hlk1, hlk2⟩, ?_, ?_, ?_⟩
  · have := R.act8; unfold sched.ACTION_RESUME_CURRENT at this; exact this
  · rw [hact8]; have := R.ucn; unfold sched.ACTION_CHOOSE_NEW at this; exact this
  · have := R.rt8
    rw [P1.eq_of_spec_fd (P1.obj.Reply.tcb.blk (L := L) X8 rptr)] at this
    exact P1.ok_inj_ff this
  · have := R.ep8
    rw [P1.eq_of_spec_fd (P1.obj.Ep.state.spec (L := L) X8 ep)] at this
    have e := P1.ok_inj_ff this
    unfold obj.EP_IDLE at e
    exact e
  · rcases hnc with h0 | ⟨h0, i7, h7, hn7, -⟩
    · exact Or.inl h0
    · refine Or.inr ⟨?_, ?_⟩
      · rw [P1.eq_of_spec_fd (P1.obj.Ntfn.state.spec (L := L) X8 _)] at h7
        intro e; apply hn7; rw [← P1.ok_inj_ff h7]; exact e
      · rcases hnsc with h00 | h1
        · exact absurd (ebd.trans h00) h0
        · show L.mem X8 (P1.ntfnScA (L.mem X8 (P1.boundA t))) = 0#u64 ∨
            L.mem X8 (P1.ntfnScA (L.mem X8 (P1.boundA t))) ≠ L.mem X8 (P1.scA t)
          rw [ebd]; exact h1

end

end

end Fl4Proofs.P3
