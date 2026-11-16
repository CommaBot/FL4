/-
P3 (DESIGN.md §9), TCB invocations: **the labels whose spec result is data,
replying in the decode** (`TcbOKR`, `TopPostRM` for `X` true), called or
not: ConfigureSingleStepping (`tcb_single_step_r`), GetBreakpoint
(`tcb_get_bp_r`), SetFlags (`tcb_set_flags_r`). FL4's reply writes
(`set_mr`, `reply_words`) and `Running` against the spec's `specTail` of the
result (TcbReplyX's `rm_close`); the work between the restart and the reply
is the label's hypothesis, as a frame (`WFr`).
-/
import Fl4Proofs.P3.TcbReplyX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-! ## ConfigureSingleStepping -/

/-- **The debug-register work of ConfigureSingleStepping** (P1's): FL4's
`configure_single_stepping` after the restart, a `WFr` step. -/
def SingleStepHypW (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1 bp n (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    debug.configure_single_stepping st arI s1 a p bp n false ⦃ r => WFr (L := L) th s1 r.2.1 ⦄

/-- **`tcb::decode` at `TCBConfigureSingleStepping`, called or not**
(`TcbOKR`). -/
theorem tcb_single_step_r (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .configureSingleStepping)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hC : TCtx (L := L) th s ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 2) (hS : SingleStepHypW (L := L) arI th s ct p)
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKR (L := L) arI s ar σ fl4_abi.label.TCBConfigureSingleStepping p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer ct := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKR
  rw [decode_step_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  obtain ⟨n, hn, hns⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 1#u64 (by decide)
  unfold tcb.decode_configure_single_stepping
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [hn]; simp only [bind_ok]
  obtain ⟨s1, σ1, hrc1, hs1, hst1, hRL1, -, hC1, -, -, x1, hk1, hrs1, -⟩ := restart_rl hP hDS hFR hDR hC hct hcur
  rw [hrc1]; simp only [bind_ok]
  have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
      (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv)).run σ =
      ({(.ok (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv)), σ)}, False) := by
    apply run_liftME_ok
    unfold Fl4Spec.decodeFl4ConfigureSingleStepping
    rw [run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 0).run σ = _ from hbs),
      run_bind_ok (show (Fl4Spec.fl4Arg (Z := Unit) buffer 1).run σ = _ from hns)]
    rfl
  have hy : (.ok [0], σ1) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeFl4TCB (.configureSingleStepping p.bv bp.bv n.bv))).run σ1).1 :=
    mem_liftE (x := ([0], σ1)) ⟨Or.inl rfl, rfl⟩
  have hnb : call = true → ∀ q, Endp.ipcBufOf true x1 = some q → ∀ z ∈ Endp.mrPairs [0],
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σ1 :=
    fun _ _ _ z hz => by simp [Endp.mrPairs] at hz
  refine WP.spec_bind (hS s1 bp n ar hs1) ?_
  rintro ⟨consumed, s2, a2⟩ hW2
  have hC2 := hC1.wfr hW2
  -- the reply of one word, then `Running`
  have tail : ∀ (bf v : U64), (do
      let (len, s3) ← msg.set_mr st s2 ct bf 0#u64 v
      let s4 ← tcb.reply_words st s3 ct len
      let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ res =>
        TopPostRM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
          (Fl4Spec.decodeFl4ConfigureSingleStepping (Z := Unit) buffer p.bv)) ct s res ⦄ := by
    intro bf v
    refine WP.spec_bind (set_mr_t hP hC2 (fun h => absurd h (by decide)) (by decide) v) ?_
    rintro ⟨len, s3⟩ ⟨hlen, hW3⟩
    have hC3 := hC2.wfr hW3
    refine WP.spec_bind (reply_words_t hP hC3 len hlen) ?_
    intro s4 hW4
    refine WP.spec_bind (sts_t hP (hC3.wfr hW4) sched.TS_RUNNING) ?_
    rintro s5 ⟨hW5, hst5⟩
    exact (WP.spec_ok _).2 (rm_close hP a2 (DecOut.of_eq hdec) hst1 hRL1 hk1 hrs1 [0] hy hnb
      (hW2.trans (hW3.trans (hW4.trans hW5))) (by rw [hst5]; exact running_ne_restart))
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (sts_t hP hC2 sched.TS_RUNNING) ?_
    rintro s3 ⟨hW3, hst3⟩
    exact (WP.spec_ok _).2 (rm_close hP a2 (DecOut.of_eq hdec) hst1 hRL1 hk1 hrs1 [0] hy hnb (hW2.trans hW3)
      (by rw [hst3]; exact running_ne_restart))
  · simp only [↓reduceIte]
    refine WP.spec_bind (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total) ?_
    rintro bf -
    split
    · split
      · exact tail bf 1#u64
      · exact tail bf 0#u64
    · exact tail bf 0#u64


/-! ## GetBreakpoint -/

/-- **FL4's IPC buffer of the caller at every `WFr` successor** (for the
reply past `MR3`): outside the slots and the domain schedule. -/
def CallerBufHyp (th : TypedHeap) (s : S) (ct : U64) : Prop :=
  ∀ s' rw, WFr (L := L) th s s' → msg.lookup_ipc_buffer st s' true ct = ok rw → BufOutsideHyp (L := L) th s' rw

/-- **`tcb::decode` at `TCBGetBreakpoint`, called or not** (`TcbOKR`). -/
theorem tcb_get_bp_r (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .invalidInvocation)
    (hext : Fl4Spec.fl4TcbExtLabelOf slbl = some .getBreakpoint)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv)
    (hC : TCtx (L := L) th s ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 1) (hG : GetBpHyp (st := st) s ct p)
    (hB : CallerBufHyp (L := L) th s ct) (hBS : BufSpecHyp σ ct.bv)
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk call don : Bool)
    (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    TcbOKR (L := L) arI s ar σ fl4_abi.label.TCBGetBreakpoint p ⟨length, buf, call, slot, extra⟩ blk call don
      slbl args ci sl excaps buffer ct := by
  have hdec0 : specDec false slbl args ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl args (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_ext hlbl hext]; rfl
  unfold TcbOKR
  rw [decode_getbp_eq arI s ar p _ hstall, hdec0]
  obtain ⟨bp, hbp, hbs⟩ := arg_rel hA hct hcur ⟨length, buf, call, slot, extra⟩ rfl 0#u64 (by decide)
  have hsp : (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv).run σ =
      (Fl4Spec.fl4CheckBpNum (Z := Unit) bp.bv >>= fun _ =>
        Fl4Spec.NonDetE.returnOk (Fl4Spec.Fl4TcbInvocation.getBreakpoint p.bv bp.bv)).run σ := by
    unfold Fl4Spec.decodeFl4GetBreakpoint
    exact run_bind_ok hbs _
  unfold tcb.decode_get_breakpoint
  rw [hct]; simp only [bind_ok]; rw [hbp]; simp only [bind_ok]; rw [check_bp_eq]
  by_cases hb : bp ≥ 4#u64
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, bp_err⟩)
    apply run_liftME_err
    rw [hsp]
    exact run_bind_error (by rw [checkBp_run, if_pos hb]) _
  · simp only [hb, ↓reduceIte, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    obtain ⟨s1, σ1, hrc1, hs1, hst1, hRL1, -, hC1, hW1, -, x1, hk1, hrs1, hbs1⟩ :=
      restart_rl hP hDS hFR hDR hC hct hcur
    rw [hrc1]; simp only [bind_ok]
    obtain ⟨r1, hr1⟩ := hG s1 bp hs1
    rw [hr1]; simp only [bind_ok]
    have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)).run σ =
        ({(.ok (.invokeFl4TCB (.getBreakpoint p.bv bp.bv)), σ)}, False) := by
      apply run_liftME_ok
      rw [hsp, run_bind_ok (by rw [checkBp_run, if_neg hb])]
      rfl
    have hy : (.ok [0, 0, 0, 0, 0], σ1) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
        (.invokeFl4TCB (.getBreakpoint p.bv bp.bv))).run σ1).1 :=
      mem_liftE (x := ([0, 0, 0, 0, 0], σ1)) ⟨rfl, rfl⟩
    have hnb := (hbs1 hBS).pairs hk1 call [0, 0, 0, 0, 0]
    refine WP.spec_bind (Pₘ := fun x : core.result.Result Unit error.Exc × S =>
      TopPostRM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
        (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s (x.1, x.2, ar)) ?_
      fun x hx => (WP.spec_ok _).2 hx
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (sts_t hP hC1 sched.TS_RUNNING) ?_
      rintro s2 ⟨hW2, hst2⟩
      exact (WP.spec_ok _).2 (rm_close hP ar (DecOut.of_eq hdec) hst1 hRL1 hk1 hrs1 _ hy hnb hW2
        (by rw [hst2]; exact running_ne_restart))
    · simp only [↓reduceIte]
      obtain ⟨bf, hl, -⟩ := spec_exists (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s1 true ct L.total)
      have hbf : BufOutsideHyp (L := L) th s1 bf := hB s1 bf hW1 hl
      rw [hl]; simp only [bind_ok]
      have no4 : ∀ (s' : S) (i : U64), i.val < 4 → 4 ≤ i.val → BufOutsideHyp (L := L) th s' bf :=
        fun _ _ h1 h2 => absurd h1 (by omega)
      refine WP.spec_bind (set_mr_t hP hC1 (no4 _ 0#u64 (by decide)) (by decide) r1.vaddr) ?_
      rintro ⟨l2, s2⟩ ⟨-, hW2⟩
      have hC2 := hC1.wfr hW2
      refine WP.spec_bind (set_mr_t hP hC2 (no4 _ 1#u64 (by decide)) (by decide) r1.ty) ?_
      rintro ⟨l3, s3⟩ ⟨-, hW3⟩
      have hC3 := hC2.wfr hW3
      refine WP.spec_bind (set_mr_t hP hC3 (no4 _ 2#u64 (by decide)) (by decide) r1.size) ?_
      rintro ⟨l4, s4⟩ ⟨-, hW4⟩
      have hC4 := hC3.wfr hW4
      refine WP.spec_bind (set_mr_t hP hC4 (no4 _ 3#u64 (by decide)) (by decide) r1.rw) ?_
      rintro ⟨l5, s5⟩ ⟨-, hW5⟩
      have hC5 := hC4.wfr hW5
      have hW15 : WFr (L := L) th s1 s5 := hW2.trans (hW3.trans (hW4.trans hW5))
      have hB5 : BufOutsideHyp (L := L) th s5 bf := by
        intro h0 i hi
        obtain ⟨g1, g2, g3⟩ := hbf h0 i hi
        exact ⟨g1, g2, by rw [hW15.2.1]; exact g3⟩
      have tail : ∀ v : U64, (do
          let (len, s6) ← msg.set_mr st s5 ct bf 4#u64 v
          let s7 ← tcb.reply_words st s6 ct len
          let s8 ← sched.set_thread_state st s7 ct sched.TS_RUNNING
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s8)) ⦃ res =>
            TopPostRM (L := L) σ blk true don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
              (Fl4Spec.decodeFl4GetBreakpoint (Z := Unit) buffer p.bv)) ct s (res.1, res.2, ar) ⦄ := by
        intro v
        refine WP.spec_bind (set_mr_t hP hC5 (fun _ => hB5) (by decide) v) ?_
        rintro ⟨len, s6⟩ ⟨hlen, hW6⟩
        have hC6 := hC5.wfr hW6
        refine WP.spec_bind (reply_words_t hP hC6 len hlen) ?_
        intro s7 hW7
        refine WP.spec_bind (sts_t hP (hC6.wfr hW7) sched.TS_RUNNING) ?_
        rintro s8 ⟨hW8, hst8⟩
        exact (WP.spec_ok _).2 (rm_close hP ar (DecOut.of_eq hdec) hst1 hRL1 hk1 hrs1 _ hy hnb
          (hW15.trans (hW6.trans (hW7.trans hW8))) (by rw [hst8]; exact running_ne_restart))
      split
      · exact tail 1#u64
      · exact tail 0#u64


/-! ## SetFlags -/

/-- **The spec's FL4 SetFlags from the restart's state** (the scheduler's and
the FPU model's): an outcome of one word keeping `RL` at every FL4 state, the
caller still `Restart`. -/
def SetFlagsSpecHyp (th : TypedHeap) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ct p : U64) : Prop :=
  ∀ (s1 : S) σ1 (clear set : U64) (blk call don : Bool),
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    RL (L := L) th G s1 σ1 → ∃ w σy x, (.ok [w], σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeFl4TCB (.setFlags p.bv clear.bv set.bv))).run σ1).1 ∧ RL (L := L) th G s1 σy ∧
      σy.kheap ct.bv = some (.tcb x) ∧ x.tcbState = .restart

theorem set_flags_eq (s : S) (t v : U64) :
    obj.Tcb.set_flags st t s v = ok (L.wr s (core.num.U64.wrapping_add t 3456#u64) v) := by
  unfold obj.Tcb.set_flags layout.tcb.FLAGS layout.tcb.F
  have h : (3328#u64 + 128#u64 : Result U64) = ok 3456#u64 := rfl
  rw [h]; simp only [bind_ok, lift]
  exact L.write_eq _ _ _

theorem tflags_val {th : TypedHeap} (hP : Placed th) {t : U64} (ht : th t = some .tcb) :
    (core.num.U64.wrapping_add t 3456#u64).val = t.val + 3456 := by
  have hf := hP.fits t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  rw [core.num.U64.wrapping_add_val_eq]
  have : (3456#u64 : U64).val = 3456 := rfl
  rw [this]; simp [U64.size_def, U64.numBits]; omega

/-- **`tcb::decode` at `TCBSetFlags`, called or not** (`TcbOKR`). -/
theorem tcb_set_flags_r (th : TypedHeap) (hP : Placed th) (hAT : P0.ArchTotal arI)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (p : U64) (hpt : th p = some .tcb) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbSetFlags)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (hC : TCtx (L := L) th s ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar))
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk call don : Bool)
    (hF : SetFlagsSpecHyp (L := L) th G σ ct p)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKR (L := L) arI s ar σ fl4_abi.label.TCBSetFlags p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  unfold TcbOKR
  rw [decode_flags_eq arI s ar p _ hstall, setFlags_dec slbl hlbl]
  by_cases h1 : length < 2#u64
  · unfold tcb.decode_set_flags
    simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage,
      setFlags_trunc σ p.bv _ (by rw [List.length_map, ← hlen]; scalar_tac), Or.inl trivial⟩)
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp only [List.length_nil] at h; scalar_tac
    | [_], h => exfalso; simp only [List.length_singleton] at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  obtain ⟨s1, σ1, hrc1, hs1, hst1, hRL1, -, hC1, -, -, -⟩ := restart_rl hP hDS hFR hDR hC hct hcur
  obtain ⟨w, σy, xy, hy, hRLy, hky, hrsy⟩ := hF s1 σ1 y0 y1 blk call don hst1 hRL1
  have hdec := DecOut.of_eq (setFlags_ok σ p.bv y0.bv y1.bv (rest.map UScalar.bv))
  have hnb : call = true → ∀ q, Endp.ipcBufOf true xy = some q → ∀ z ∈ Endp.mrPairs [w],
      (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σy :=
    fun _ _ _ z hz => by simp [Endp.mrPairs] at hz
  unfold tcb.decode_set_flags
  simp only [h1, ↓reduceIte]
  rw [hct]; simp only [bind_ok]; rw [ha0]; simp only [bind_ok]; rw [ha1]; simp only [bind_ok]
  rw [hrc1]; simp only [bind_ok]
  obtain ⟨f, hf, -⟩ := spec_exists (P0.obj.Tcb.flags.p0 st p s1 L.total)
  rw [hf]; simp only [bind_ok, lift, set_flags_eq]
  set s2 := L.wr s1 (core.num.U64.wrapping_add p 3456#u64)
    ((f &&& ~~~y0) ||| (y1 &&& fl4_abi.consts.tcb_flag.MASK)) with hs2
  have hfv := tflags_val hP hpt
  have ha := hP.align p _ hpt
  have hW2 : WFr (L := L) th s1 s2 :=
    wfr_tcbw hP hC1.ksb hpt (by rw [hfv]; omega) (by rw [hfv]; omega) (by unfold P1.Aligned; rw [hfv]; omega) _
  have hC2 := hC1.wfr hW2
  -- the tail, from the flags written, for any architecture state
  have tail : ∀ a2 : A, (if call = true then (do
        let buf ← msg.lookup_ipc_buffer st s2 true ct
        let (len, s3) ← msg.set_mr st s2 ct buf 0#u64 ((f &&& ~~~y0) ||| (y1 &&& fl4_abi.consts.tcb_flag.MASK))
        let s4 ← tcb.reply_words st s3 ct len
        let s5 ← sched.set_thread_state st s4 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2))
      else (do
        let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2))) ⦃ res =>
        TopPostRM (L := L) σ blk call don (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeFl4TCB
          (Fl4Spec.decodeFl4SetFlags (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) p.bv)) ct s res ⦄ := by
    intro a2
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_bind (sts_t hP hC2 sched.TS_RUNNING) ?_
      rintro s3 ⟨hW3, hst3⟩
      exact (WP.spec_ok _).2 (rm_close' hP a2 hdec hst1 [w] hy hRLy hky hrsy hnb (hW2.trans hW3)
        (by rw [hst3]; exact running_ne_restart))
    · simp only [↓reduceIte]
      obtain ⟨bf, hl, -⟩ := spec_exists (Fl4Proofs.P0.msg.lookup_ipc_buffer.p0 st s2 true ct L.total)
      rw [hl]; simp only [bind_ok]
      refine WP.spec_bind (set_mr_t hP hC2 (fun h => absurd h (by decide)) (by decide) _) ?_
      rintro ⟨len, s3⟩ ⟨hlen, hW3⟩
      have hC3 := hC2.wfr hW3
      refine WP.spec_bind (reply_words_t hP hC3 len hlen) ?_
      intro s4 hW4
      refine WP.spec_bind (sts_t hP (hC3.wfr hW4) sched.TS_RUNNING) ?_
      rintro s5 ⟨hW5, hst5⟩
      exact (WP.spec_ok _).2 (rm_close' hP a2 hdec hst1 [w] hy hRLy hky hrsy hnb
        (hW2.trans (hW3.trans (hW4.trans hW5))) (by rw [hst5]; exact running_ne_restart))
  split
  · refine WP.spec_bind (hAT.fpu_release ar p) ?_
    intro a1 _
    exact tail a1
  · exact tail ar


/-! ## ReadRegisters -/

/-- **FL4's ReadRegisters after the restart** (P1's: the source's suspend
and the register-copy loops into the caller's registers and buffer, then
`Running`): a `WFr` step, the caller `Running`. -/
def ReadRegsFrameHyp (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1 (flags n : U64) (call : Bool) (a : A), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    1 ≤ n.val → n.val ≤ 20 →
    tcb.read_registers st arI s1 a p ((flags &&& 1#u64) != 0#u64) n call ⦃ r =>
      WFr (L := L) th s1 r.1 ∧ L.mem r.1 (stA ct) = sched.TS_RUNNING ⦄

/-- **The spec's ReadRegisters from the restart's state** (the scheduler's:
the source's suspend): an outcome keeping `RL` at every FL4 state, the
caller still `Restart`, its buffer (when called) in a user frame. -/
def ReadRegsSpecHyp (th : TypedHeap) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ct p : U64) : Prop :=
  ∀ (s1 : S) σ1 (flags n : U64) (blk call don : Bool),
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
    RL (L := L) th G s1 σ1 → ∃ rr σy x, (.ok rr, σy) ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don
      (.invokeTCB (.readRegisters p.bv (Fl4Spec.testBit flags.bv 0) n.bv Fl4Spec.ArchDefaultExtraRegisters))).run
        σ1).1 ∧ RL (L := L) th G s1 σy ∧ σy.kheap ct.bv = some (.tcb x) ∧ x.tcbState = .restart ∧
      (call = true → ∀ q, Endp.ipcBufOf true x = some q → ∀ z ∈ Endp.mrPairs rr,
        (Endp.bufAddr q z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr q z.1) σy)

/-- **`tcb::decode` at `TCBReadRegisters`, called or not** (`TcbOKR`). -/
theorem tcb_read_regs_r (th : TypedHeap) (hP : Placed th)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (p : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = .tcbReadRegisters)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (hC : TCtx (L := L) th s ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk call don : Bool)
    (hR : ReadRegsFrameHyp (L := L) arI th s ct p) (hRS : ReadRegsSpecHyp (L := L) th G σ ct p)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (buffer : Option Fl4Spec.ObjRef) :
    TcbOKR (L := L) arI s ar σ fl4_abi.label.TCBReadRegisters p ⟨length, buf, call, slot, extra⟩ blk call don slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hdec0 : specDec false slbl (args.map UScalar.bv) ci sl (.Thread p) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
        (Fl4Spec.decodeReadRegisters (Z := Unit) (args.map UScalar.bv) (.threadCap p.bv)) := by
    show Fl4Spec.fl4DecodeTcbInvocation (Z := Unit) slbl (args.map UScalar.bv) (.threadCap p.bv) sl excaps buffer = _
    rw [fl4DecodeTcb_spec (by rw [hlbl]; decide) (by rw [hlbl]; decide)]
    unfold Fl4Spec.decodeTcbInvocation
    rw [hlbl]
  unfold TcbOKR
  rw [decode_read_eq arI s ar p _ hstall, hdec0]
  unfold tcb.decode_read_registers
  by_cases h1 : length < 2#u64
  · simp only [h1, ↓reduceIte, error.truncated, bind_ok]
    refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, .truncatedMessage, ?_, Or.inl trivial⟩)
    apply run_liftME_err
    have : args.length < 2 := by scalar_tac
    match args, this with
    | [], _ => rfl
    | [_], _ => rfl
  simp only [h1, ↓reduceIte]
  obtain ⟨y0, y1, rest, rfl⟩ : ∃ y0 y1 rest, args = y0 :: y1 :: rest := by
    match args, hlen with
    | y0 :: y1 :: rest, _ => exact ⟨_, _, _, rfl⟩
    | [], h => exfalso; simp at h; scalar_tac
    | [_], h => exfalso; simp at h; scalar_tac
  have ha0 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 0#u64 = ok y0 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 0#u64 y0 (by simp)
  have ha1 : tcb.arg st s ⟨length, buf, call, slot, extra⟩ 1#u64 = ok y1 := by
    unfold tcb.arg; rw [hct]; simp only [bind_ok]; exact hargs 1#u64 y1 (by simp)
  rw [ha0, ha1]; simp only [bind_ok, nregs_eq]
  have hsp : ∀ (k : Unit → Fl4Spec.SEMonad Unit Fl4Spec.TcbInvocation),
      (Fl4Spec.decodeReadRegisters (Z := Unit) ((y0 :: y1 :: rest).map UScalar.bv) (.threadCap p.bv)) =
      (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
        let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
        Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
        Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
          Fl4Spec.ArchDefaultExtraRegisters)) := by
    intro _
    simp only [Fl4Spec.decodeReadRegisters, List.map_cons, nregs_spec, retOk_bind]
  rw [hsp (fun _ => Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.suspend 0))]
  have hrng := range20_iff y1
  by_cases hr : 1 ≤ y1.val ∧ y1.val ≤ 20
  · have hn1 : ¬ y1 < 1#u64 := by scalar_tac
    have hn2 : ¬ y1 > 20#u64 := by scalar_tac
    simp only [hn1, hn2, ↓reduceIte, hct, bind_ok, tcb_eq_ct]
    have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ = ({(.ok (), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_pos (hrng.2 hr)]; rfl
    by_cases hpc : p = ct
    · subst hpc
      simp only [decide_true, ↓reduceIte, error.illegal, bind_ok]
      refine (WP.spec_ok _).2 ?_
      apply Or.inl
      refine ⟨_, rfl, rfl, .illegalOperation, ?_, Or.inl trivial⟩
      apply run_liftME_err
      rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
        s.curThread) rfl), whenE_pos (by show p.bv = σ.curThread; rw [hcur])]
      exact run_bind_error (m := (Fl4Spec.NonDetE.throwError Fl4Spec.SyscallError.illegalOperation :
        Fl4Spec.SEMonad Unit Unit)) rfl _
    · simp only [decide_eq_false hpc, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨s1, σ1, hrc1, hs1, hst1, hRL1, -, -, -, -, -⟩ := restart_rl hP hDS hFR hDR hC hct hcur
      rw [hrc1]; simp only [bind_ok, lift]
      have hdec : (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeTCB
          (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20) >>= fun _ => do
            let self ← Fl4Spec.NonDetE.liftE (Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread)
            Fl4Spec.NonDetE.whenE (p.bv = self) (Fl4Spec.NonDetE.throwError .illegalOperation)
            Fl4Spec.NonDetE.returnOk (Fl4Spec.TcbInvocation.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
              Fl4Spec.ArchDefaultExtraRegisters))).run σ =
          ({(.ok (.invokeTCB (.readRegisters p.bv (Fl4Spec.testBit y0.bv 0) y1.bv
            Fl4Spec.ArchDefaultExtraRegisters)), σ)}, False) := by
        apply run_liftME_ok
        rw [run_bind_ok hrc, run_bind_ok (run_liftE (m := Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit =>
          s.curThread) rfl), whenE_neg (by show ¬ p.bv = σ.curThread; rw [hcur, bv_eq_iff']; exact hpc), retOk_bind]
        rfl
      obtain ⟨rr, σy, xy, hy, hRLy, hky, hrsy, hnb⟩ := hRS s1 σ1 y0 y1 blk call don hst1 hRL1
      refine WP.spec_bind (hR s1 y0 y1 call ar hs1 hr.1 hr.2) ?_
      rintro ⟨s2, a2⟩ ⟨hW2, hst2⟩
      exact (WP.spec_ok _).2 (rm_close' hP a2 (DecOut.of_eq hdec) hst1 rr hy hRLy hky hrsy hnb hW2
        (by rw [hst2]; exact running_ne_restart))
  · have hrc : (Fl4Spec.rangeCheck (Z := Unit) y1.bv 1 (BitVec.ofNat 64 20)).run σ =
        ({(.error (.rangeError 1 (BitVec.ofNat 64 20)), σ)}, False) := by
      unfold Fl4Spec.rangeCheck Fl4Spec.NonDetE.unlessE; rw [if_neg (fun h => hr (hrng.1 h))]; rfl
    have herr : ErrRel (.Sys (.RangeError 1#u64 20#u64)) (.rangeError 1 (BitVec.ofNat 64 20)) :=
      Or.inl ⟨rfl, rfl⟩
    by_cases hn1 : y1 < 1#u64
    · simp only [hn1, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr⟩)
      exact run_liftME_err (run_bind_error hrc _)
    · have hn2 : y1 > 20#u64 := by scalar_tac
      simp only [hn1, hn2, ↓reduceIte, error.range, bind_ok]
      refine (WP.spec_ok _).2 (Or.inl ⟨_, rfl, rfl, _, ?_, herr⟩)
      exact run_liftME_err (run_bind_error hrc _)

/-! ## The Thread cap's branch -/

theorem TopPostRM.toX {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A} (h : TopPostRM (L := L) σ blk call don m ct s res) :
    TopPostRMX (L := L) (fun _ _ _ => True) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6⟩
  · exact Or.inl ⟨e, h1, h2, h3, trivial⟩
  · exact Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, trivial⟩

/-- The labels whose spec result is data (FL4 replies in the decode). -/
def DataLbl (slbl : Fl4Spec.Data) : Prop :=
  Fl4Spec.genInvocationType slbl = .tcbReadRegisters ∨ Fl4Spec.genInvocationType slbl = .tcbSetFlags ∨
    Fl4Spec.fl4TcbExtLabelOf slbl = some .getBreakpoint ∨
    Fl4Spec.fl4TcbExtLabelOf slbl = some .configureSingleStepping

/-- **The Thread cap's branch for `handle_invocation_refinesMX`** (`X` true):
a data label replies in the decode (`DecOKRMX`, from `TcbOKR`); any other
label has an empty spec result (`DecOKDMX`, from `TcbOKF`, the domain
schedule's frame `DomFrame` and `okAll_specDec_thread`). -/
theorem decode_invocation_threadMX (s : S) (ar : A) (σ : Fl4Spec.State Unit) (lbl length slot : U64) (p : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize) (ct : U64)
    (hct : sched.cur_thread st s = ok ct) (slbl : Fl4Spec.Data) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (buffer : Option Fl4Spec.ObjRef)
    (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (hR : DataLbl slbl → fp = false → TcbOKR (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call
      don slbl args ci sl excaps buffer ct)
    (hD : ¬ DataLbl slbl → (fp = false → TcbOKF (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk
      call don slbl args ci sl excaps buffer) ∧
      DomFrame (L := L) arI s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args ci sl excaps buffer) :
    DecOKDMX (L := L) arI (fun _ _ _ => True) s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args
      ci sl excaps buffer ∨
    DecOKRMX (L := L) arI (fun _ _ _ => True) s ar σ lbl length slot (.Thread p) blk call don fp buf extra slbl args
      ci sl excaps buffer ct := by
  by_cases hd : DataLbl slbl
  · exact Or.inr (WP.spec_mono (decode_invocation_thread_r arI s ar σ lbl length slot p blk call don fp buf extra ct
      hct slbl args ci sl excaps buffer (hR hd)) fun _ h => h.toX)
  · obtain ⟨hF, hDom⟩ := hD hd
    refine Or.inl (DecOKDM.toXT arI ((decode_invocation_threadM arI s ar σ lbl length slot p blk call don fp buf
      extra ct hct slbl args ci sl excaps buffer hF).withDom arI hDR hDom) ?_)
    exact okAll_specDec_thread fp slbl args ci sl p excaps buffer (fun h => hd (Or.inl h))
      (fun h => hd (Or.inr (Or.inl h))) (fun h => hd (Or.inr (Or.inr (Or.inl h))))
      (fun h => hd (Or.inr (Or.inr (Or.inr h))))


theorem tcbLabelOf_rr {lbl : U64} (h : tcbLabelOf lbl = .tcbReadRegisters) : lbl.val = 2 := by
  unfold tcbLabelOf at h
  by_cases h2 : lbl.val = 2
  · exact h2
  rw [if_neg h2] at h
  by_cases h3 : lbl.val = 3
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases h4 : lbl.val = 4
  · rw [if_pos h4] at h; cases h
  rw [if_neg h4] at h
  by_cases h5 : lbl.val = 5
  · rw [if_pos h5] at h; cases h
  rw [if_neg h5] at h
  by_cases h6 : lbl.val = 6
  · rw [if_pos h6] at h; cases h
  rw [if_neg h6] at h
  by_cases h7 : lbl.val = 7
  · rw [if_pos h7] at h; cases h
  rw [if_neg h7] at h
  by_cases h8 : lbl.val = 8
  · rw [if_pos h8] at h; cases h
  rw [if_neg h8] at h
  by_cases h9 : lbl.val = 9
  · rw [if_pos h9] at h; cases h
  rw [if_neg h9] at h
  by_cases h10 : lbl.val = 10
  · rw [if_pos h10] at h; cases h
  rw [if_neg h10] at h
  by_cases h11 : lbl.val = 11
  · rw [if_pos h11] at h; cases h
  rw [if_neg h11] at h
  by_cases h12 : lbl.val = 12
  · rw [if_pos h12] at h; cases h
  rw [if_neg h12] at h
  by_cases h13 : lbl.val = 13
  · rw [if_pos h13] at h; cases h
  rw [if_neg h13] at h
  by_cases h14 : lbl.val = 14
  · rw [if_pos h14] at h; cases h
  rw [if_neg h14] at h
  by_cases h15 : lbl.val = 15
  · rw [if_pos h15] at h; cases h
  rw [if_neg h15] at h
  by_cases h20 : lbl.val = 20
  · rw [if_pos h20] at h; cases h
  rw [if_neg h20] at h
  by_cases h21 : lbl.val = 21
  · rw [if_pos h21] at h; cases h
  rw [if_neg h21] at h
  cases h

theorem tcbLabelOf_sf {lbl : U64} (h : tcbLabelOf lbl = .tcbSetFlags) : lbl.val = 21 := by
  unfold tcbLabelOf at h
  by_cases h2 : lbl.val = 2
  · rw [if_pos h2] at h; cases h
  rw [if_neg h2] at h
  by_cases h3 : lbl.val = 3
  · rw [if_pos h3] at h; cases h
  rw [if_neg h3] at h
  by_cases h4 : lbl.val = 4
  · rw [if_pos h4] at h; cases h
  rw [if_neg h4] at h
  by_cases h5 : lbl.val = 5
  · rw [if_pos h5] at h; cases h
  rw [if_neg h5] at h
  by_cases h6 : lbl.val = 6
  · rw [if_pos h6] at h; cases h
  rw [if_neg h6] at h
  by_cases h7 : lbl.val = 7
  · rw [if_pos h7] at h; cases h
  rw [if_neg h7] at h
  by_cases h8 : lbl.val = 8
  · rw [if_pos h8] at h; cases h
  rw [if_neg h8] at h
  by_cases h9 : lbl.val = 9
  · rw [if_pos h9] at h; cases h
  rw [if_neg h9] at h
  by_cases h10 : lbl.val = 10
  · rw [if_pos h10] at h; cases h
  rw [if_neg h10] at h
  by_cases h11 : lbl.val = 11
  · rw [if_pos h11] at h; cases h
  rw [if_neg h11] at h
  by_cases h12 : lbl.val = 12
  · rw [if_pos h12] at h; cases h
  rw [if_neg h12] at h
  by_cases h13 : lbl.val = 13
  · rw [if_pos h13] at h; cases h
  rw [if_neg h13] at h
  by_cases h14 : lbl.val = 14
  · rw [if_pos h14] at h; cases h
  rw [if_neg h14] at h
  by_cases h15 : lbl.val = 15
  · rw [if_pos h15] at h; cases h
  rw [if_neg h15] at h
  by_cases h20 : lbl.val = 20
  · rw [if_pos h20] at h; cases h
  rw [if_neg h20] at h
  by_cases h21 : lbl.val = 21
  · exact h21
  rw [if_neg h21] at h
  cases h

theorem tcbExtOf_gb {lbl : U64} (h : tcbExtOf lbl = some .getBreakpoint) : lbl.val = 17 := by
  unfold tcbExtOf at h
  by_cases h16 : lbl.val = 16
  · rw [if_pos h16] at h; cases h
  rw [if_neg h16] at h
  by_cases h17 : lbl.val = 17
  · exact h17
  rw [if_neg h17] at h
  by_cases h18 : lbl.val = 18
  · rw [if_pos h18] at h; cases h
  rw [if_neg h18] at h
  by_cases h19 : lbl.val = 19
  · rw [if_pos h19] at h; cases h
  rw [if_neg h19] at h
  by_cases h22 : lbl.val = 22
  · rw [if_pos h22] at h; cases h
  rw [if_neg h22] at h
  by_cases h23 : lbl.val = 23
  · rw [if_pos h23] at h; cases h
  rw [if_neg h23] at h
  by_cases h24 : lbl.val = 24
  · rw [if_pos h24] at h; cases h
  rw [if_neg h24] at h
  cases h

theorem tcbExtOf_ss {lbl : U64} (h : tcbExtOf lbl = some .configureSingleStepping) : lbl.val = 19 := by
  unfold tcbExtOf at h
  by_cases h16 : lbl.val = 16
  · rw [if_pos h16] at h; cases h
  rw [if_neg h16] at h
  by_cases h17 : lbl.val = 17
  · rw [if_pos h17] at h; cases h
  rw [if_neg h17] at h
  by_cases h18 : lbl.val = 18
  · rw [if_pos h18] at h; cases h
  rw [if_neg h18] at h
  by_cases h19 : lbl.val = 19
  · exact h19
  rw [if_neg h19] at h
  by_cases h22 : lbl.val = 22
  · rw [if_pos h22] at h; cases h
  rw [if_neg h22] at h
  by_cases h23 : lbl.val = 23
  · rw [if_pos h23] at h; cases h
  rw [if_neg h23] at h
  by_cases h24 : lbl.val = 24
  · rw [if_pos h24] at h; cases h
  rw [if_neg h24] at h
  cases h

theorem ext_some_invalid {slbl : Fl4Spec.Data} {l : Fl4Spec.Fl4TcbExtLabel}
    (h : Fl4Spec.fl4TcbExtLabelOf slbl = some l) : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
  unfold Fl4Spec.fl4TcbExtLabelOf at h
  split_ifs at h with h1
  · exact h1

/-- **`TcbOKR` at a data label**, from each label's work hypothesis. -/
theorem tcbOKR_data (th : TypedHeap) (hP : Placed th) (hAT : P0.ArchTotal arI)
    (s : S) (ar : A) (σ : Fl4Spec.State Unit) (G : MdbGhost) (hDS : DState (L := L) th s σ G)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (lbl p : U64) (hpt : th p = some .tcb) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = tcbLabelOf lbl)
    (hext : Fl4Spec.genInvocationType slbl = .invalidInvocation → Fl4Spec.fl4TcbExtLabelOf slbl = tcbExtOf lbl)
    (hD : DataLbl slbl)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (hcur : σ.curThread = ct.bv) (hC : TCtx (L := L) th s ct)
    (hstall : smp.remote_tcb_stall st arI s ar p = ok (s, ar)) (buffer : Option Fl4Spec.ObjRef)
    (hA : ArgRel (st := st) s σ ct buf buffer 2) (hS : SingleStepHypW (L := L) arI th s ct p)
    (hG : GetBpHyp (st := st) s ct p) (hB : CallerBufHyp (L := L) th s ct) (hBS : BufSpecHyp σ ct.bv)
    (hF : SetFlagsSpecHyp (L := L) th G σ ct p)
    (slot : obj.Slot) (extra : Aeneas.Std.Array obj.Slot 3#usize) (blk call don : Bool)
    (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hRF : ReadRegsFrameHyp (L := L) arI th s ct p) (hRS : ReadRegsSpecHyp (L := L) th G σ ct p) :
    TcbOKR (L := L) arI s ar σ lbl p ⟨length, buf, call, slot, extra⟩ blk call don slbl (args.map UScalar.bv) ci sl
      excaps buffer ct := by
  rcases hD with h | h | h | h
  · have := tcbLabelOf_rr (by rw [← hlbl, h])
    have e : lbl = fl4_abi.label.TCBReadRegisters := UScalar.eq_of_val_eq (by rw [this]; simp)
    subst e
    exact tcb_read_regs_r arI th hP s ar σ G hDS hFR hDR p slbl h length buf ct hct args hlen hargs hcur hC hstall
      slot extra blk call don hRF hRS ci sl excaps buffer
  · have := tcbLabelOf_sf (by rw [← hlbl, h])
    have e : lbl = fl4_abi.label.TCBSetFlags := UScalar.eq_of_val_eq (by rw [this]; simp)
    subst e
    exact tcb_set_flags_r arI th hP hAT s ar σ G hDS hFR hDR p hpt slbl h length buf ct hct args hlen hargs hcur hC
      hstall slot extra blk call don hF ci sl excaps buffer
  · have hg := ext_some_invalid h
    have he : tcbExtOf lbl = some .getBreakpoint := by rw [← hext hg, h]
    have e : lbl = fl4_abi.label.TCBGetBreakpoint :=
      UScalar.eq_of_val_eq (by rw [tcbExtOf_gb he]; simp)
    subst e
    exact tcb_get_bp_r arI th hP s ar σ G hDS hFR hDR p slbl hg h length buf ct hct hcur hC hstall buffer
      (fun i hi => hA i (by omega)) hG hB hBS slot extra blk call don _ ci sl excaps
  · have hg := ext_some_invalid h
    have he : tcbExtOf lbl = some .configureSingleStepping := by rw [← hext hg, h]
    have e : lbl = fl4_abi.label.TCBConfigureSingleStepping :=
      UScalar.eq_of_val_eq (by rw [tcbExtOf_ss he]; simp)
    subst e
    exact tcb_single_step_r arI th hP s ar σ G hDS hFR hDR p slbl hg h length buf ct hct hcur hC hstall buffer hA hS
      slot extra blk call don _ ci sl excaps

end

end

end Fl4Proofs.P3
