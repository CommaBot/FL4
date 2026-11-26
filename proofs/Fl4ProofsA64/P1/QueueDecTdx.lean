-- AArch64 port of Fl4Proofs.P1.QueueDecTdx (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: InvGaps' `tdx` family (#68, `Cap::TdxControl`): `tdx.decode`
(GetReport, ExtendRTMR, GetQuote) keeps the invariants.  Each operation
checks its arguments with the state unchanged, sets the current thread
`Restart`, runs the arch's TDCALL (`ArchTotal`, any result), replies one
status word when it is a call (`XS`: the current thread's registers and IPC
buffer) and sets the thread running: the `ioport.decode` read path.
-/
import Fl4ProofsA64.P1.QueueDecDom
import Fl4ProofsA64.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errT" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

/-- **`tdx.reply`** after the restart: the reply (when a call) writes the
current thread's registers and IPC buffer (`XS`), then the thread is set
running. -/
theorem tdx.reply.bxi (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hE : EntAt st P3Ok s) {s1 : S} (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1)
    (f1 : Foot st T Cs Sg Scs Z ∅ s s1) (hst1 : L.mem s1 (stA (L.curW s)) = sched.TS_RESTART)
    (call : Bool) (status : U64) :
    tdx.reply st s1 (L.curW s) call status ⦃ s' => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  obtain ⟨Q, R, x1⟩ := BXI.xs (sx := 0#u64) (BlkOK.bxi h1) (D.user.ksb f1.1)
  unfold tdx.reply
  refine WP.spec_bind (Pₘ := fun s2 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R 0#u64 s1 s2) ?_ ?_
  · split
    · refine WP.spec_bind (E.buf Ac ∅ Q R s1 _ (hE.xg.foot (f1.mono (Set.empty_subset _))) x1.1 hct) fun b hb => ?_
      refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1 hct (by simp [layout.reg.BADGE, layout.reg.X0]))
        fun s3 x3 => ?_
      refine WP.spec_bind (msg.set_mr.xs x3 hct hb (by simp)) ?_
      rintro ⟨n, s4⟩ ⟨x4, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      unfold msg.set_msg_info
      exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
        obj.Tcb.set_reg.xs (v := w) x4 hct (by simp [layout.reg.MSG_INFO, layout.reg.X1])
    · exact (WP.spec_ok _).2 x1
  intro s2 x2
  have hst : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART := by
    rw [stA_eq, x2.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp) (fun _ => by simp), ← stA_eq, hst1]
  exact sched.set_thread_state.running_bxi x2.bxi hct hst

/-- The restart of the current thread at an invocation (`DecPre`). -/
theorem tdx.restart (s : S) {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧
      Foot st T Cs Sg Scs Z ∅ s s1 ∧ L.mem s1 (stA (L.curW s)) = sched.TS_RESTART ∧
      KeepT st T Cs Rp Scs Nt (L.curW s) s s1 ⦄ :=
  sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk D.bxi.1.choose_spec.choose_spec.curT
    (runnable_ok D.run).1 (runnable_ok D.run).2

set_option maxHeartbeats 4000000 in
/-- **`tdx.get_report`** keeps the invariants. -/
theorem tdx.get_report.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len : U64) (call : Bool) (buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) :
    tdx.get_report st ar s a len call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tdx.get_report
  split
  · errT
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · errT
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun c _ => ?_
  refine WP.spec_bind (P0.tdx.report_frame.p0 c) fun o _ => ?_
  cases o with
  | none => errT
  | some p =>
    try dsimp only
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (tdx.restart s D) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
    refine WP.spec_bind (hA.tdx_report a _ _ _ _ _ _ _ _ _) ?_
    rintro ⟨v, a1⟩ _
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (tdx.reply.bxi E D hE h1 f1 hst1 call v) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)

set_option maxHeartbeats 4000000 in
/-- **`tdx.extend_rtmr`** keeps the invariants. -/
theorem tdx.extend_rtmr.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len : U64) (call : Bool) (buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) :
    tdx.extend_rtmr st ar s a len call buf ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tdx.extend_rtmr
  split
  · errT
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  split
  · errT
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
  refine WP.spec_bind (tdx.restart s D) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
  refine WP.spec_bind (hA.tdx_extend_rtmr a _ _ _ _ _ _ _) ?_
  rintro ⟨v, a1⟩ _
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tdx.reply.bxi E D hE h1 f1 hst1 call v) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)

set_option maxHeartbeats 4000000 in
/-- **`tdx.get_quote`** keeps the invariants. -/
theorem tdx.get_quote.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len : U64) (call : Bool) (buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) :
    tdx.get_quote st ar s a len call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tdx.get_quote
  split
  · errT
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · errT
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun c _ => ?_
  refine WP.spec_bind (P0.tdx.quote_frame.p0 ar a c hA) fun o _ => ?_
  cases o with
  | none => errT
  | some f =>
    obtain ⟨frame, bytes⟩ := f
    try dsimp only
    try simp only [uncurry_apply_pair]
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    have e : ct = L.curW s := ect
    subst e
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun _ _ => ?_
    refine WP.spec_bind (P0.tdx.quote_len_ok.p0 _ _) fun b1 _ => ?_
    split
    · refine WP.spec_bind (tdx.restart s D) fun s1 ⟨h1, f1, hst1, _⟩ => ?_
      refine WP.spec_bind (hA.tdx_get_quote a _ _) ?_
      rintro ⟨v, a1⟩ _
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (tdx.reply.bxi E D hE h1 f1 hst1 call v) fun s3 h3 => ?_
      exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)
    · errT

/-- **`tdx.decode`** keeps the invariants: an inactive TDX or an unknown
label is rejected with the state unchanged. -/
theorem tdx.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len : U64) (call : Bool) (buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) :
    tdx.decode st ar s a lbl len call buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  unfold tdx.decode
  refine WP.spec_bind (hA.tdx_active a) fun b _ => ?_
  split
  · split
    · exact tdx.get_report.dec hA E a len call buf D hE
    split
    · exact tdx.extend_rtmr.dec hA E a len call buf D hE
    split
    · exact tdx.get_quote.dec hA E a len call buf D hE
    · errT
  · errT

/-- **InvGaps' `tdx`, discharged** from the transfer's placement facts (the
IPC buffer of the status reply). -/
theorem decGap_tdx {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .tdx := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact tdx.decode.dec hA E a lbl len call buf D hE

end

end Fl4ProofsA64.P1
