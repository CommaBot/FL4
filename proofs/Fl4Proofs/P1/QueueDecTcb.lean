/-
P1: InvGaps' `thread` family, by label.  `tcb.decode`'s `Suspend`,
`Resume`, `UnbindNotification`, `SetPriority`, `SetMCPriority` and
`SetIPCBuffer` keep the invariants (from `DecPre`, the placement facts
`TcbPlace`, and `DelGaps`/`CdtHyps` for the buffer slot); the other
labels are named, one shape (`TcbGap`), in `TcbGaps`.
-/
import Fl4Proofs.P1.QueueDelFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The per-label shape**: `tcb.decode` with the label `lbl` on a thread
cap keeps the invariants (`DecPost`), from `DecPre`. -/
def TcbGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (lbl : U64) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (t len buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize), DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra →
    tcb.decode st ar s a lbl t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-- The thread-family labels P1 does not prove. -/
structure TcbGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  readRegisters : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBReadRegisters
  writeRegisters : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBWriteRegisters
  copyRegisters : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBCopyRegisters
  configure : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBConfigure
  setSchedParams : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetSchedParams
  setTimeoutEndpoint : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetTimeoutEndpoint
  setSpace : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetSpace
  bindNotification : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBBindNotification
  setBreakpoint : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetBreakpoint
  getBreakpoint : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBGetBreakpoint
  unsetBreakpoint : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBUnsetBreakpoint
  configureSingleStepping : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBConfigureSingleStepping
  setTLSBase : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetTLSBase
  setFlags : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetFlags
  readFPU : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBReadFPU
  writeFPU : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBWriteFPU
  setTimer : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetTimer
  setEPTRoot : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetEPTRoot

/-- The placement facts of the priority labels (P3's): TCBs' MCPs are
priorities (seL4's `word8`), the current thread at a decode has an SC, and
the extra caps' slots are cap slots (`SetIPCBuffer`'s insert). -/
structure TcbPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  mcp : ∀ (Ac : Set U64) (s : S) (t : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
    (L.mem s (core.num.U64.wrapping_add t 3440#u64)).val < 256
  curSc : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → L.mem s (scA (L.curW s)) ≠ 0#u64
  /-- The extra caps' slots are cap slots. -/
  extraW : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl

/-- The state after `remote_tcb_stall`, from the decode's start `s`. -/
structure Stalled (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s s1 : S) : Prop where
  bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1
  act : L.actionW s1 = L.actionW s
  cur : L.curW s1 = L.curW s
  csc : L.cscW s1 = L.cscW s
  fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
    L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  node : WritesIn st s s1 (NodeW st s)

/-- The caller's restart after the stall: the invariants, the candidate no
TCB, the current thread kept, `KeepT`. -/
theorem Stalled.restart {s s1 : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.restart_caller st s1 ⦃ s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
      L.curW s2 = L.curW s ∧ KeepT st T Cs Rp Scs Nt (L.curW s) s1 s2 ⦄ := by
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  refine WP.spec_mono (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2)) fun s2 ⟨h2, _, _, k⟩ => ?_
  rw [h1.cur] at k
  refine ⟨h2, fun y hy e => ?_, k.curW.trans h1.cur, k⟩
  rcases k.act with e' | e'
  · rw [e', h1.act, D.act] at e; exact notT_small hT (by simp) (e ▸ hy)
  · rw [e'] at e; exact notT_small hT (by simp) (e ▸ hy)

/-- A result that is not a preemption. -/
def NP {α : Type} (r : core.result.Result α error.Exc) : Prop := ∀ e, r = .Err e → e ≠ .Preempted

theorem tcb.extra_with_length.mem (c : tcb.Ctx) (n : U64) :
    tcb.extra_with_length c 0#usize n ⦃ r => NP r ∧ ∀ x, r = .Ok x → x ∈ c.extra.val ∧ x ≠ 0#u64 ⦄ := by
  unfold tcb.extra_with_length tcb.extra
  have hl0 : (0#usize).val < c.extra.val.length := by rw [c.extra.property]; simp
  simp only [show ¬ (0#usize ≥ 3#usize) by simp, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun o => ∀ x, o = some x → x ∈ c.extra.val ∧ x ≠ 0#u64) ?_ fun o ho => ?_
  · refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec c.extra 0#usize hl0) fun sl hsl => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 fun x e => by cases e
    · rename_i h0
      exact (WP.spec_ok _).2 fun x e => by
        cases e; exact ⟨hsl ▸ List.getElem_mem hl0, by simpa using h0⟩
  rcases o with _ | x
  · simp [error.truncated, NP]
  · simp only
    split
    · exact (WP.spec_ok _).2 ⟨by simp [NP], fun y e => by cases e; exact ho x rfl⟩
    · simp [error.truncated, NP]

theorem tcb.thread_arg.tcb {s s1 : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} {sl pos : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hw : WritesIn st s s1 (NodeW st s))
    (hsl : sl ∈ extra.val) (h0 : sl ≠ 0#u64) :
    tcb.thread_arg st s1 sl pos ⦃ r => NP r ∧ ∀ p, r = .Ok p → p ∈ T ⦄ := by
  unfold tcb.thread_arg
  refine WP.spec_bind (D.extra s1 hw sl hsl h0) fun c hc => ?_
  cases c <;> simp [error.invalid_cap, NP]
  exact hc.2.1 _ rfl

theorem tcb.check_prio.le (s : S) (p auth : U64) :
    tcb.check_prio st s p auth ⦃ r => NP r ∧ (r = .Ok () →
      p.val ≤ (L.mem s (core.num.U64.wrapping_add auth 3440#u64)).val) ⦄ := by
  unfold tcb.check_prio obj.Tcb.mcp layout.tcb.MCP layout.tcb.F
  simp only [lift, bind_ok]
  step as ⟨m, hm⟩
  refine WP.spec_bind (LawfulStore.read_spec _ _) fun v ev => ?_
  have e : core.num.U64.wrapping_add auth m = core.num.U64.wrapping_add auth 3440#u64 := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, hm]
  rw [e] at ev
  split
  · simp [error.range, NP]
  · rename_i hle
    refine (WP.spec_ok _).2 ⟨by simp [NP], fun _ => ?_⟩
    rw [← ev]; simpa using hle


theorem np_ne {e : error.Exc} (h : NP (α := α) (.Err e)) : (core.result.Result.Err e : core.result.Result Unit error.Exc) ≠ .Err .Preempted :=
  fun e' => h _ rfl (by cases e'; rfl)

set_option hygiene false in
/-- An error leaf at the stalled state. -/
local macro "errS" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
     first
     | exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (np_ne hnp))
     | exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))))

set_option maxHeartbeats 2000000 in
/-- **`SetPriority` / `SetMCPriority`** after the stall. -/
theorem tcb.decode_set_priority.dec {A : Type _} {ar : machine.Arch A} {s s1 : S} {a1 : A} {t len buf : U64}
    {call : Bool} {slot : obj.Slot} {extra : Aeneas.Std.Array obj.Slot 3#usize} (prio : Bool)
    (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_priority st ar s1 a1 t { length := len, buf, call, slot, extra } prio ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold tcb.decode_set_priority
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨hnp, hx⟩
  rcases r with x | e
  swap
  · errS
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun p _ => ?_
  refine WP.spec_bind (tcb.thread_arg.tcb (pos := 1#u64) D h1.node hxm hx0) ?_
  clear hnp
  rintro r ⟨hnp, hT2⟩
  rcases r with auth | e
  swap
  · errS
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hauth := hT2 auth rfl
  refine WP.spec_bind (tcb.check_prio.le s1 p auth) ?_
  clear hnp
  rintro r ⟨hnp, hle⟩
  rcases r with u | e
  swap
  · errS
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hv : p.val < 256 := lt_of_le_of_lt (hle rfl) (P.mcp Ac s1 auth h1.bxi hauth)
  refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, hna, ec2, k⟩ => ?_
  have hsc0 := P.curSc Ac s _ _ D
  split
  · unfold tcb.thread_control_sched
    simp only [lift, bind_ok, tcb.SCHED_UPDATE_PRIO, tcb.SCHED_UPDATE_FAULT, tcb.SCHED_UPDATE_MCP,
      tcb.SCHED_UPDATE_SC]
    simp
    have cur : t = L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) → t = L.curW s := fun e => e.trans ec2
    have esc : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
      rw [k.scf hct, scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
    have einq : L.mem s2 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
      rw [k.inqf hct, inqA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
    refine WP.spec_bind (sched.set_priority.blk s2 t p h2 ht hv
      (fun e => by rw [cur e, einq]; exact D.cb.nr)
      (fun e => by rw [cur e, esc]; exact hsc0)
      (fun e => by rw [cur e, esc]; exact D.cb.ac hsc0)) fun s3 ⟨h3, _, _⟩ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  · unfold tcb.thread_control_sched
    simp only [lift, bind_ok, tcb.SCHED_UPDATE_PRIO, tcb.SCHED_UPDATE_FAULT, tcb.SCHED_UPDATE_MCP,
      tcb.SCHED_UPDATE_SC]
    simp
    refine WP.spec_bind (obj.Tcb.set_mcp.blk s2 t p h2 ht) fun s3 ⟨h3, _, _⟩ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))

/-! ## `SetIPCBuffer` -/

/-- The stalled state is a `Cur0` state of the decode. -/
theorem Stalled.cur0 {s s1 : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 := by
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  refine ⟨D.hcsc, Ac, h1.bxi, h1.cur, h1.csc, Or.inl ?_, ?_⟩
  · rw [scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  · rw [h1.act, D.act, h1.cur]; exact fun e => notT_small hT (by simp) (e ▸ hct)

/-- The caller's restart after the stall, as a `Cur0` state. -/
theorem Stalled.restart0 {s s1 : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.restart_caller st s1 ⦃ s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (h1.restart D) fun s2 ⟨h2, hna, ec2, k⟩ => ?_
  refine ⟨D.hcsc, Ac, BlkOK.bxi h2, ec2, k.cscW.trans h1.csc, Or.inl ?_, hna _ (ec2 ▸ hct)⟩
  rw [k.scf hct, scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)

theorem tcb_slotW {t : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    SlotW T Ω Sg (core.num.U64.wrapping_add t (core.num.U64.wrapping_mul 2#u64 32#u64)) := by
  have ha := hT t ht
  have := ha.align; have := ha.fits
  refine ⟨?_, fun o ho h8 => Or.inl ⟨t, ht, core.num.U64.wrapping_add 64#u64 o, ?_, ?_⟩⟩
  · simp [Aligned, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega
  · simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · apply UScalar.eq_of_val_eq
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega

theorem obj.Tcb.set_ipc_buffer.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_ipc_buffer st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3512#u64) v ⦄ := by
  unfold obj.Tcb.set_ipc_buffer layout.tcb.IPC_BUFFER layout.tcb.F
  step as ⟨i, hi⟩
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec _ _ _) fun s' e => ?_
  rw [e]; congr 2
  apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, hi]

theorem tcb.still_valid.nz (s : S) (t sl : U64) (c : capability.Cap) (src : U64) :
    tcb.still_valid st s t sl c src ⦃ b => b = true → src ≠ 0#u64 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  by_cases h0 : src = 0#u64
  · subst h0
    unfold tcb.still_valid
    simp only [obj.Slot.is_null, bind_ok, decide_true, ↓reduceIte]
    exact (WP.spec_ok _).2 fun e => by cases e
  · exact WP.spec_mono (P0.tcb.still_valid.p0 st s t sl c src hS) fun _ _ _ => h0

theorem tcb.derive_for_buffer.slot (s : S) (b bs : U64) :
    tcb.derive_for_buffer st s b bs ⦃ r => ∀ v, r = .Ok v → v.2 = bs ∨ v.2 = 0#u64 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.derive_for_buffer
  split
  · refine WP.spec_bind (P0.obj.Slot.cap.p0 st bs s hS) fun c _ => ?_
    exact (WP.spec_ok _).2 fun v e => by cases e; exact Or.inr rfl
  · refine WP.spec_bind (P0.obj.Slot.cap.p0 st bs s hS) fun c _ => ?_
    refine WP.spec_bind (P0.objects.derive_cap.p0 st s bs c hS) fun r _ => ?_
    rcases r with c' | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (P0.vspace.check_valid_ipc_buffer.p0 b c') fun r1 _ => ?_
      rcases r1 with _ | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        exact (WP.spec_ok _).2 fun v e => by cases e; exact Or.inl rfl
      · simp [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]
    · simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]

set_option hygiene false in
/-- An error leaf at a `Cur0` state `hc`. -/
local macro "errC" hc:term : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post $hc)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, error.truncated, error.illegal]
     exact (WP.spec_ok _).2 (Cur0.post $hc)))

set_option maxHeartbeats 4000000 in
/-- **`SetIPCBuffer`** after the stall, from `DelGaps` (the buffer slot's
delete), `CdtHyps` (the insert) and the extra slots' placement. -/
theorem tcb.decode_set_ipc_buffer.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_ipc_buffer st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have c1 := h1.cur0 D
  unfold tcb.decode_set_ipc_buffer
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · errC c1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun baddr _ => ?_
  refine WP.spec_bind (tcb.derive_for_buffer.slot s1 baddr x) ?_
  rintro r hr
  rcases r with v | e
  swap
  · errC c1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hv2 := hr v rfl
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S × A =>
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2.1) ?_ ?_
  swap
  · rintro ⟨r, s', a'⟩ hr
    dsimp only at hr
    try simp only [uncurry_apply_pair]
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact (WP.spec_ok _).2 hr
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 hr
  -- `install_buffer`
  unfold tcb.install_buffer obj.Tcb.slot
  simp only [lift, bind_ok, layout.tcb.SLOT_BUFFER, cte_size]
  refine WP.spec_bind (cdt.delete.cur0 hA G c2 (tcb_slotW hT ht)) ?_
  rintro ⟨r, s3, a3⟩ c3
  try simp only [uncurry_apply_pair] at c3 ⊢
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c3)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨Ac3, hb3⟩ := c3.bxi
  refine WP.spec_bind (obj.Tcb.set_ipc_buffer.wr s3 t baddr) fun s4 e4 => ?_
  subst e4
  have h4 := (plainW_all (K := 3512#u64) (v := baddr) hb3.blk ht (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)).1
  obtain ⟨vc, vs⟩ := v
  simp only at hv2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tcb.still_valid.nz _ t slot vc vs) fun b hbv => ?_
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac3 s5) ?_ fun s5 h5 => ?_
  · split
    · rename_i hb
      have hvs : vs = x := hv2.resolve_right (hbv hb)
      subst hvs
      have hxW := hxw vs hxm hx0
      have hbW : CapW T Ω Sg (core.num.U64.wrapping_add t (core.num.U64.wrapping_mul 2#u64 32#u64)) := by
        have := (tcb_slotW (Ω := Ω) (Sg := Sg) hT ht).2 0#u64 (by simp) (by simp)
        have h0 : ∀ y : U64, core.num.U64.wrapping_add y 0#u64 = y := fun y => by
          apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rwa [h0] at this
      unfold cdt.insert
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st vs _ hS) fun sc _ => ?_
      exact WP.spec_mono (C.ins Ac3 _ vc sc vs _ (BlkOK.bxi h4) hxW hbW) fun s' w =>
        (blk_of_capw h4 w fun _ hb => hb).1
    · exact (WP.spec_ok _).2 h4
  refine WP.spec_bind (sched.cur_thread.spec s5) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · refine WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h6.1))
  · exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h5))

set_option maxHeartbeats 4000000 in
/-- **`tcb.decode`** keeps the invariants, from `TcbGaps` (the labels P1
does not prove), `TcbPlace`, `DelGaps` and `CdtHyps`. -/
theorem tcb.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z)
    {s : S} {a : A} {lbl t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) :
    tcb.decode st ar s a lbl t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  by_cases g0 : lbl = fl4_abi.label.TCBReadRegisters
  · subst g0; exact G.readRegisters Ac s a t len buf call slot extra D
  by_cases g1 : lbl = fl4_abi.label.TCBWriteRegisters
  · subst g1; exact G.writeRegisters Ac s a t len buf call slot extra D
  by_cases g2 : lbl = fl4_abi.label.TCBCopyRegisters
  · subst g2; exact G.copyRegisters Ac s a t len buf call slot extra D
  by_cases g3 : lbl = fl4_abi.label.TCBConfigure
  · subst g3; exact G.configure Ac s a t len buf call slot extra D
  by_cases g4 : lbl = fl4_abi.label.TCBSetSchedParams
  · subst g4; exact G.setSchedParams Ac s a t len buf call slot extra D
  by_cases g5 : lbl = fl4_abi.label.TCBSetTimeoutEndpoint
  · subst g5; exact G.setTimeoutEndpoint Ac s a t len buf call slot extra D
  by_cases g7 : lbl = fl4_abi.label.TCBSetSpace
  · subst g7; exact G.setSpace Ac s a t len buf call slot extra D
  by_cases g8 : lbl = fl4_abi.label.TCBBindNotification
  · subst g8; exact G.bindNotification Ac s a t len buf call slot extra D
  by_cases g9 : lbl = fl4_abi.label.TCBSetBreakpoint
  · subst g9; exact G.setBreakpoint Ac s a t len buf call slot extra D
  by_cases g10 : lbl = fl4_abi.label.TCBGetBreakpoint
  · subst g10; exact G.getBreakpoint Ac s a t len buf call slot extra D
  by_cases g11 : lbl = fl4_abi.label.TCBUnsetBreakpoint
  · subst g11; exact G.unsetBreakpoint Ac s a t len buf call slot extra D
  by_cases g12 : lbl = fl4_abi.label.TCBConfigureSingleStepping
  · subst g12; exact G.configureSingleStepping Ac s a t len buf call slot extra D
  by_cases g13 : lbl = fl4_abi.label.TCBSetTLSBase
  · subst g13; exact G.setTLSBase Ac s a t len buf call slot extra D
  by_cases g14 : lbl = fl4_abi.label.TCBSetFlags
  · subst g14; exact G.setFlags Ac s a t len buf call slot extra D
  by_cases g15 : lbl = fl4_abi.label.TCBReadFPU
  · subst g15; exact G.readFPU Ac s a t len buf call slot extra D
  by_cases g16 : lbl = fl4_abi.label.TCBWriteFPU
  · subst g16; exact G.writeFPU Ac s a t len buf call slot extra D
  by_cases g17 : lbl = fl4_abi.label.TCBSetTimer
  · subst g17; exact G.setTimer Ac s a t len buf call slot extra D
  by_cases g18 : lbl = fl4_abi.label.TCBSetEPTRoot
  · subst g18; exact G.setEPTRoot Ac s a t len buf call slot extra D
  have ht : t ∈ T := D.cap.2.1 t rfl
  unfold tcb.decode
  refine WP.spec_bind (smp.remote_tcb_stall.bxi hA s a t D.bxi) ?_
  rintro ⟨s1, a1⟩ ⟨hb1, ea, ec, -, ecs, fld, -, wn⟩
  have h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 := ⟨hb1, ea, ec, ecs, fld, wn⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  simp only [g0, g1, g2, g3, g4, g5, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18, ↓reduceIte]
  split
  · -- Suspend
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, hna, _, _⟩ => ?_
    refine WP.spec_bind (sched.suspend.blk s2 a1 t h2 ht (hna t ht)) ?_
    rintro ⟨s3, a2⟩ ⟨h3, _⟩
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  split
  · -- Resume
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (sched.restart.tinv hA s2 a1 t h2 ht) ?_
    rintro ⟨s3, a2⟩ h3
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  split
  · exact tcb.decode_set_priority.dec _ P D h1
  split
  · exact tcb.decode_set_priority.dec _ P D h1
  split
  · exact tcb.decode_set_ipc_buffer.dec hA Gd C (P.extraW Ac s _ _ D) D h1
  split
  · -- UnbindNotification
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s1 t) fun i _ => ?_
    split
    · simp only [error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (notification.unbind_notification.blk s2 t h2 ht) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))

/-- **InvGaps' `thread`, from the per-label gaps** `TcbGaps`, `TcbPlace`, `DelGaps`
and `CdtHyps`. -/
theorem decGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : TcbGaps st ar T Cs Ω H Sg Rp Scs Nt Z U) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U)
    (Gd : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U .thread := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact tcb.decode.dec hA G P Gd C D

end

end Fl4Proofs.P1
