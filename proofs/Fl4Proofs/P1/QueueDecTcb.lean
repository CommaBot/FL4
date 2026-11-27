/-
P1: InvGaps' `thread` family, by label.  `tcb.decode`'s `Suspend`,
`Resume`, `UnbindNotification`, `SetPriority`, `SetMCPriority`,
`SetIPCBuffer`, `SetTLSBase`, `SetFlags`, `SetTimer`, `ReadFPU` and
`WriteFPU` keep the invariants (from `DecPre`, the placement facts
`TcbPlace`, and `DelGaps`/`CdtHyps` for the buffer slot); the other labels
are named, one shape (`TcbGap`), in `TcbGaps`.
-/
import Fl4Proofs.P1.QueueDelFin
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The per-label shape**: `tcb.decode` with the label `lbl` on a thread
cap keeps the invariants (`DecPost`), from `DecPre`. -/
def TcbGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (lbl : U64) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (t len buf : U64) (call : Bool) (slot : obj.Slot)
    (extra : Aeneas.Std.Array obj.Slot 3#usize), DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra →
    tcb.decode st ar s a lbl t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

/-- **`SetSchedParams`' premises**, at a decode's start `s` (the stall and the
caller's restart keep its cap-slot words): the target's old fault-handler cap
is null or an endpoint cap (P3's `FhSlotHyp`), the slot part of the install
from an extra slot (P3's `inst_hslot`), and the target is not the idle
thread. -/
structure SspHyps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  fh : ∀ (Ac : Set U64) (s : S) (t : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra →
    ∀ s1 : S, (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      obj.Slot.cap st (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) s1 ⦃ c => NullOrEp H c ⦄
  slot : ∀ (Ac : Set U64) (s : S) (t : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra →
    ∀ (sl src : U64) (nc : capability.Cap), src ∈ extra.val → src ≠ 0#u64 →
    ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) .Null ⦃ r =>
        WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 t sl nc src ⦃ b1 => b1 = true →
          cdt.insert st r.1 nc src (slotIdx t layout.tcb.SLOT_FAULT_HANDLER) ⦃ s3 =>
            WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄
  idle : ∀ (Ac : Set U64) (s : S) (t : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra → t ≠ L.idleW s

/-- The thread-family labels P1 does not prove (`SetEPTRoot`, VT-x: not yet
refined, DESIGN §5), and `SetSchedParams`' premises (`SspHyps`). -/
structure TcbGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  ssp : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok
  setEPTRoot : TcbGap st ar T Cs Ω H Sg Rp Scs Nt Z U fl4_abi.label.TCBSetEPTRoot

/-- The placement facts of the priority labels (P3's): TCBs' MCPs are
priorities (seL4's `word8`), the current thread at a decode has an SC, and
the extra caps' slots are cap slots (`SetIPCBuffer`'s insert). -/
structure TcbPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- A thread's MCP (at the decode's start; P1 carries it past the stall). -/
  mcp : ∀ (Ac : Set U64) (s : S) (t : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → t ∈ T →
    (L.mem s (core.num.U64.wrapping_add t 3440#u64)).val < 256
  curSc : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → L.mem s (scA (L.curW s)) ≠ 0#u64
  /-- The extra caps' slots are cap slots. -/
  extraW : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl
  /-- `ReadFPU`/`WriteFPU`'s frame: the user words of the frame cap in the
  first extra slot, at the given offset, are user words (`FpuFrameOK`). -/
  fpu : ∀ (Ac : Set U64) (s0 s : S) (c : tcb.Ctx), EntAt st P3Ok s0 → WritesIn st s0 s (NodeW st s0) →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    tcb.extra c 0#usize ⦃ o => ∀ x, o = some x → tcb.arg st s c 0#u64 ⦃ off =>
      obj.Slot.cap st x s ⦃ cp => ∀ ptr sz r d m ep asid va, cp = .Frame ptr sz r d m ep asid va →
        FpuFrameOK U (core.num.U64.wrapping_add ptr off) ⦄ ⦄ ⦄

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
    (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
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
  have hv : p.val < 256 := lt_of_le_of_lt (hle rfl) (by rw [h1.fld auth hauth 3440#u64 (by simp) (by simp)]; exact P.mcp Ac s auth hE D.bxi hauth)
  refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, hna, ec2, k⟩ => ?_
  have hsc0 := P.curSc Ac s _ _ hE D
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
  refine ⟨D.hcsc, Ac, h1.bxi, h1.cur, h1.csc, Or.inl ?_, fun y hy => ?_, ?_,
    WritesIn.mono h1.node fun _ hb => NodeW.cur0w D.bxi.1.choose_spec.choose_spec.cur hb⟩
  · rw [scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  · rw [h1.act, D.act]; exact fun e => notT_small hT (by simp) (e ▸ hy)
  · rw [stA_eq, h1.fld _ hct _ (by simp) (by simp), ← stA_eq]; exact nbr_runnable D.run

/-- The caller's restart after the stall, as a `Cur0` state. -/
theorem Stalled.restart0 {s s1 : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.restart_caller st s1 ⦃ s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  refine WP.spec_mono (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2))
    fun s2 ⟨h2, f2, est2, k⟩ => ?_
  rw [h1.cur] at est2 k
  refine ⟨D.hcsc, Ac, BlkOK.bxi h2, k.curW.trans h1.cur, k.cscW.trans h1.csc, Or.inl ?_, fun y hy => ?_,
    by rw [est2]; exact nbr_restart,
    Cur0W.trans (WritesIn.mono h1.node fun _ hb => NodeW.cur0w D.bxi.1.choose_spec.choose_spec.cur hb)
      (WritesIn.mono f2 fun _ hb => Or.inl (KW.mono hb (Set.empty_subset _)))⟩
  · rw [k.scf hct, scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  · rcases k.act with e | e
    · rw [e, h1.act, D.act]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)
    · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)

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
    (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
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
  refine WP.spec_bind (cdt.delete.cur0 hA (G _ hE) c2 (tcb_slotW hT ht)) ?_
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
  have f4 : Fr0 st T Cs Ω H Sg Scs Z s (L.wr s3 (core.num.U64.wrapping_add t 3512#u64) baddr) :=
    Cur0W.trans c3.fr (WritesIn.mono (writesIn_wr (field_aligned (hT t ht) (by simp) (by simp))) fun _ hb =>
      Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp)))
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
      exact WP.spec_mono (C.ins Ac3 s _ vc sc vs _ hE f4 (BlkOK.bxi h4) hxW hbW) fun s' w =>
        (blk_of_capw h4 w fun _ hb => hb).1
    · exact (WP.spec_ok _).2 h4
  refine WP.spec_bind (sched.cur_thread.spec s5) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · refine WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h6.1))
  · exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h5))

theorem spec_ite {α : Type _} {c : Prop} [Decidable c] {x y : Result α} {P : α → Prop}
    (h1 : c → x ⦃ P ⦄) (h2 : ¬ c → y ⦃ P ⦄) : (if c then x else y) ⦃ P ⦄ := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

/-! ## `SetTimer`, `SetTLSBase`, `ReadFPU`/`WriteFPU`, `SetFlags` -/

/-- Writes of the TCBs' user context (below the fields) keep `BlkOK`, the
candidate, the current thread and the fields. -/
theorem blk_rf {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (w : WritesIn st s s' (XferFoot T ∅)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.actionW s' = L.actionW s ∧ L.curW s' = L.curW s ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) := by
  obtain ⟨⟨Q, R, q⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨q', hB', hX', hS', hSg', ea, ec, -, -, f, -⟩ :=
    xfer_all (U := ∅) q hB hX hS hSg (fun b hb => absurd hb (by simp)) w
  exact ⟨⟨⟨Q, R, q'⟩, hB', hX', hS', hSg'⟩, ea, ec, f⟩

/-- `Cur0` across user-context and user-memory writes. -/
theorem Cur0.xf {s0 s s' : S} {U' : Set U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hU : UserOK st T Cs Ω H U' s) (w : WritesIn st s s' (XferFoot T U')) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  have h' := h
  obtain ⟨-, Ac', ⟨⟨Q, R, q⟩, hB, hX, hSg, hS⟩, -, -, -, -, -⟩ := h'
  obtain ⟨q', hB', hX', hS', hSg', ea, ec, -, ecs, f, -⟩ := xfer_all q hB hX hS hSg hU w
  have hct : L.curW s ∈ T := q.curT
  refine Cur0.mk h ⟨⟨Q, R, q'⟩, hB', hX', hSg', hS'⟩ ec ecs (Or.inl ?_) (Or.inl ea) (Or.inl ?_)
    (WritesIn.mono w fun _ hb => XferFoot.cur0w hU hb)
  · rw [scA_eq]; exact f _ hct _ (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact f _ hct _ (by simp) (by simp) (by simp)

set_option maxHeartbeats 2000000 in
/-- **`SetTimer`** after the stall. -/
theorem tcb.set_timer.dec {A : Type _} {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    (if len < 2#u64 then do
        let r ← error.truncated Unit
        ok (r, s1, a1)
      else do
        let deadline ← tcb.arg st s1 { length := len, buf, call, slot, extra } 0#u64
        let badge ← tcb.arg st s1 { length := len, buf, call, slot, extra } 1#u64
        let s2 ← tcb.restart_caller st s1
        let s3 ← timer.insert st s2 t deadline badge
        ok (core.result.Result.Ok (), s3, a1)) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  split
  · simp only [error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun _ _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun _ _ => ?_
  refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
  refine WP.spec_bind (timer.insert.blk s2 t _ _ h2 ht) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))

set_option maxHeartbeats 2000000 in
/-- **`SetTLSBase`** after the stall. -/
theorem tcb.decode_set_tls_base.dec {A : Type _} {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool}
    {slot : obj.Slot} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    (do
      let (r, s2) ← tcb.decode_set_tls_base st s1 t { length := len, buf, call, slot, extra }
      ok (r, s2, a1)) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S =>
    ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' r.2 ∧ r.1 ≠ .Err .Preempted) ?_ ?_
  swap
  · rintro ⟨r, s2⟩ ⟨Ac', hb, hr⟩
    exact (WP.spec_ok _).2 (DecPost.of_bxi hb hr)
  unfold tcb.decode_set_tls_base
  split
  · simp only [error.truncated, bind_ok]
    exact (WP.spec_ok _).2 ⟨Ac, h1.bxi, by simp⟩
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun base _ => ?_
  refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
  refine WP.spec_bind (P0.regs.sanitise.p0 _ _) fun i _ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.rf (v := i) (s := s2) hT ht
    (by simp [layout.reg.TLS_BASE, layout.reg.FS_BASE])) fun s3 w3 => ?_
  have h3 := (blk_rf h2 w3).1
  refine WP.spec_bind (sched.cur_thread.spec s3) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · refine WP.spec_bind (sched.reschedule_required.blk s3 h3) fun s4 h4 => ?_
    exact (WP.spec_ok _).2 ⟨Ac, BlkOK.bxi h4.1, by simp⟩
  · exact (WP.spec_ok _).2 ⟨Ac, BlkOK.bxi h3, by simp⟩

/-- **`ReadFPU`/`WriteFPU`** after the stall. -/
theorem tcb.fpu_transfer.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s s1 : S} {a1 : A} {t : U64} {c : tcb.Ctx} {tf : Bool}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.fpu_transfer st ar s1 a1 t c tf ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  have hU1 : UserOK st T Cs Ω H U s1 := D.user.ksb h1.node.1
  refine WP.spec_mono (tcb.fpu_transfer.blk hA s1 a1 t c tf h1.bxi.blk ht (est ▸ hr.1) (est ▸ hr.2) hU1
    (P.fpu Ac s s1 c hE h1.node h1.bxi)) ?_
  rintro ⟨r, s', a'⟩ ⟨-, e | ⟨s2, e2, w⟩⟩
  · simp only at e
    subst e
    exact Cur0.post (h1.cur0 D)
  · have c2 : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 := by
      have := h1.restart0 D; rw [e2] at this; exact (WP.spec_ok _).1 this
    have hk : L.ksb s2 = L.ksb s1 := by
      have := h1.restart D; rw [e2] at this; exact ((WP.spec_ok _).1 this).2.2.2.ksb
    exact Cur0.post (c2.xf (hU1.ksb hk) w)

/-- A plain TCB field write (`bxi_field`'s) keeps the candidate, the current
thread and the other TCB fields. -/
theorem fld_wr {s : S} {y K v : U64} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    ANI st s (L.wr s (core.num.U64.wrapping_add y K) v) ∧
      ∀ y' ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (y = y' → K.val ≠ K'.val) →
        L.mem (L.wr s (core.num.U64.wrapping_add y K) v) (core.num.U64.wrapping_add y' K') =
          L.mem s (core.num.U64.wrapping_add y' K') := by
  have q := h.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  refine ⟨ani_wr hN (field_aligned (hT y hy) hK hK8) fun o ho e => ?_, fun y' hy' K' hK' hK8' hne => ?_⟩
  · exact node_ne_field (o := o) hN (by omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e.symm)
  · exact L.mem_wr_ne (field_aligned (hT y hy) hK hK8) (field_aligned (hT y' hy') hK' hK8')
      fun e => field_ne (hT y hy) (hT y' hy') hK hK' hne (UScalar.eq_of_val_eq e)

theorem obj.Tcb.set_flags.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_flags st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3456#u64) v ⦄ := by
  unfold obj.Tcb.set_flags layout.tcb.FLAGS layout.tcb.F
  step as ⟨i, hi⟩
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec _ _ _) fun s' e => ?_
  rw [e]; congr 2
  apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, hi]

theorem msg.set_mr.rf0 {s : S} {t buf v : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    msg.set_mr st s t buf 0#u64 v ⦃ r => WritesIn st s r.2 (XferFoot T ∅) ⦄ := by
  unfold msg.set_mr
  simp only [show (0#u64 : U64) < msg.N_MSG_REGISTERS by simp [msg.N_MSG_REGISTERS], ↓reduceIte]
  refine WP.spec_bind (msg.msg_register.lt 0#u64) fun i hi => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v) (s := s) hT ht hi) fun s1 w1 => ?_
  simp only [lift, bind_ok]
  exact (WP.spec_ok _).2 w1

theorem tcb.reply_words.rf {s : S} {t n : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    tcb.reply_words st s t n ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ := by
  unfold tcb.reply_words msg.set_msg_info
  refine WP.spec_bind (obj.Tcb.set_reg.rf (v := 0#u64) (s := s) hT ht
    (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s1 w1 => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 mi) fun w _ => ?_
  exact WP.spec_mono (obj.Tcb.set_reg.rf (v := w) (s := s1) hT ht
    (by simp [layout.reg.MSG_INFO, layout.reg.RSI])) fun s2 w2 => rf_trans w1 w2

set_option maxHeartbeats 4000000 in
/-- **`SetFlags`** after the stall. -/
theorem tcb.decode_set_flags.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_flags st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  unfold tcb.decode_set_flags
  split
  · simp only [error.truncated, bind_ok]
    exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  have ect' : ct = L.curW s := ect.trans h1.cur
  subst ect'
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun clr _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun sv _ => ?_
  refine WP.spec_bind (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2)) ?_
  rintro s2 ⟨h2, -, est2, k⟩
  rw [h1.cur] at est2 k
  have hna2 : ∀ y ∈ T, L.actionW s2 ≠ y := fun y hy e => by
    rcases k.act with e' | e'
    · rw [e', h1.act, D.act] at e; exact notT_small hT (by simp) (e ▸ hy)
    · rw [e'] at e; exact notT_small hT (by simp) (e ▸ hy)
  have einq2 : L.mem s2 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
    rw [k.inqf hct, inqA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  refine WP.spec_bind (P0.obj.Tcb.flags.p0 st t s2 hS) fun f _ => ?_
  simp only [lift, bind_ok]
  refine WP.spec_bind (obj.Tcb.set_flags.wr s2 t _) fun s3 e3 => ?_
  have hb2 := BlkOK.bxi h2
  obtain ⟨ani3, fr3⟩ := fld_wr (K := 3456#u64) (v := (f &&& ~~~clr ||| (sv &&& fl4_abi.consts.tcb_flag.MASK)))
    hb2 ht (by simp) (by simp)
  rw [← e3] at ani3 fr3
  have hb3 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s3 := by
    rw [e3]; exact bxi_field hb2 ht (by simp) (by simp) (by simp) (by simp)
  have est3 : L.mem s3 (stA (L.curW s)) = sched.TS_RESTART := by
    rw [stA_eq, fr3 _ hct _ (by simp) (by simp) (fun _ => by simp), ← stA_eq, est2]
  have einq3 : L.mem s3 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
    rw [inqA_eq, fr3 _ hct _ (by simp) (by simp) (fun _ => by simp), ← inqA_eq, einq2]
  have hna3 : ∀ y ∈ T, L.actionW s3 ≠ y := fun y hy => by rw [ani3.1]; exact hna2 y hy
  -- the tail: the optional reply words, then running
  have TL : ∀ (s4 : S) (a2 : A), WritesIn st s3 s4 (XferFoot T ∅) →
      (do
        let s5 ← sched.set_thread_state st s4 (L.curW s) sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a2)) ⦃ r s' _ =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := fun s4 a2 w4 => by
    obtain ⟨b4, ea4, -, f4⟩ := blk_rf hb3.blk w4
    have e4 : L.mem s4 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, f4 _ hct _ (by simp) (by simp) (by simp), ← stA_eq, est3]
    have i4 : L.mem s4 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
      rw [inqA_eq, f4 _ hct _ (by simp) (by simp) (by simp), ← inqA_eq, einq3]
    refine WP.spec_bind (sts_bxi (BlkOK.bxi b4) hct not_blocked_running running_ne
      ⟨by rw [e4]; exact not_blocked_restart, by rw [e4]; exact restart_ne.1, by rw [e4]; exact restart_ne.2⟩
      (by rw [i4]; exact D.cb.nq) (by rw [i4]; exact D.cb.nr) (by rw [ea4]; exact hna3 _ hct)) fun s5 ⟨h5, _, _⟩ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h5)
  split
  · refine WP.spec_bind (hA.fpu_release a1 t) fun a2 _ => ?_
    split
    · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s3 true _ hS) fun b _ => ?_
      refine WP.spec_bind (msg.set_mr.rf0 hT hct) ?_
      rintro ⟨n, s4⟩ w4
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (tcb.reply_words.rf hT hct) fun s5 w5 => ?_
      exact TL s5 _ (rf_trans w4 w5)
    · exact TL s3 _ (WritesIn.refl _ _)
  · split
    · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s3 true _ hS) fun b _ => ?_
      refine WP.spec_bind (msg.set_mr.rf0 hT hct) ?_
      rintro ⟨n, s4⟩ w4
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (tcb.reply_words.rf hT hct) fun s5 w5 => ?_
      exact TL s5 _ (rf_trans w4 w5)
    · exact TL s3 _ (WritesIn.refl _ _)

/-! ## `BindNotification`, `UnsetBreakpoint`, `GetBreakpoint` -/

theorem tcb.decode_bind_notification.dec {A : Type _} {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool}
    {slot : obj.Slot} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    (do
      let (r, s2) ← tcb.decode_bind_notification st s1 t { length := len, buf, call, slot, extra }
      ok (r, s2, a1)) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S =>
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2) ?_ ?_
  swap
  · rintro ⟨r, s2⟩ hr
    exact (WP.spec_ok _).2 hr
  unfold tcb.decode_bind_notification
  refine WP.spec_bind (tcb.extra_with_length.mem _ 0#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (obj.Tcb.bound_ntfn.val s1 t) fun i ei => ?_
  split
  · simp only [error.illegal, bind_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  rename_i hi
  have hb0 : L.mem s1 (boundA t) = 0#u64 := by rw [← ei]; exact UScalar.eq_of_val_eq (by simpa using hi)
  refine WP.spec_bind (Pₘ := fun r : core.result.Result obj.Ntfn error.Exc =>
    ∀ n, r = .Ok n → n ∈ Nt ∧ L.mem s1 (ntfnBtA n) = 0#u64) ?_ ?_
  · unfold tcb.bindable_ntfn
    refine WP.spec_bind (D.extra s1 h1.node x hxm hx0) fun c hc => ?_
    cases c <;> dsimp only
    all_goals first | (simp [error.illegal, WP.spec_ok]; done) | skip
    rename_i n b0 b1 rv
    have hn := (hc.1.2.1 n b0 b1 rv rfl).1
    split
    · refine WP.spec_bind (P0.obj.Ntfn.head.p0 st n s1 hS) fun _ _ => ?_
      split
      · simp [error.illegal, WP.spec_ok]
      · refine WP.spec_bind (obj.Ntfn.bound_tcb.val s1 n) fun j ej => ?_
        split
        · simp [error.illegal, WP.spec_ok]
        · rename_i hj
          exact (WP.spec_ok _).2 fun n' e => by cases e; exact ⟨hn, by rw [← ej]; exact UScalar.eq_of_val_eq (by simpa using hj)⟩
    · simp [error.illegal, WP.spec_ok]
  rintro r hr
  rcases r with n | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, k⟩ => ?_
  refine WP.spec_bind (notification.bind_notification.blk s2 t n h2 ht (hr n rfl).1
    (by rw [k.bndf ht]; exact hb0) (by rw [k.ntb _ (hr n rfl).1]; exact (hr n rfl).2)) fun s3 h3 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))

theorem debug.check_bp_num.lt (bp : U64) :
    debug.check_bp_num bp ⦃ r => NP r ∧ (r = .Ok () → bp.val < 4) ⦄ := by
  unfold debug.check_bp_num
  split
  · simp [NP]
  · rename_i h
    refine (WP.spec_ok _).2 ⟨by simp [NP], fun _ => ?_⟩
    simp [debug.N_REGS] at h; exact h

theorem debug.unset_breakpoint.rf {s : S} {t bp : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hbp : bp.val < 4) :
    debug.unset_breakpoint st s t bp ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold debug.unset_breakpoint debug.set_dr7
  refine WP.spec_bind (P0.debug.dr7.p0 st s t hS) fun i _ => ?_
  refine WP.spec_bind (P0.debug.enable_bit.p0 bp) fun i1 _ => ?_
  simp only [lift, bind_ok]
  step as ⟨i4, hi4⟩
  step as ⟨i5, _⟩
  step as ⟨i6, hi6⟩
  step as ⟨i7, _⟩
  refine WP.spec_bind (obj.Tcb.set_debug_reg.rf (s := s) (v := _) hT ht (by simp [debug.DR7])) fun s1 w1 => ?_
  exact WP.spec_mono (obj.Tcb.set_debug_reg.rf (s := s1) (v := 0#u64) hT ht (by omega)) fun s2 w2 => rf_trans w1 w2

theorem tcb.reply_words.xs {Q : U64 → U64 → List U64} {R : U64 → List U64} {X : Set U64} {s0 s : S} {t n : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (ht : t ∈ T) :
    tcb.reply_words st s t n ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  unfold tcb.reply_words msg.set_msg_info
  refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) h ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
    fun s1 h1 => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xs (v := w) h1 ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

set_option maxHeartbeats 4000000 in
/-- **`GetBreakpoint`** after the stall, the reply's buffer from `XferHyps`. -/
theorem tcb.decode_get_breakpoint.dec {A : Type _} (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool}
    {slot : obj.Slot} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    (do
      let (r, s2) ← tcb.decode_get_breakpoint st s1 t { length := len, buf, call, slot, extra }
      ok (r, s2, a1)) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have c1 := h1.cur0 D
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S =>
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2) ?_ ?_
  swap
  · rintro ⟨r, s2⟩ hr
    exact (WP.spec_ok _).2 hr
  unfold tcb.decode_get_breakpoint
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  have ect' : ct = L.curW s := ect.trans h1.cur
  subst ect'
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun bp _ => ?_
  refine WP.spec_bind (debug.check_bp_num.lt bp) ?_
  rintro r ⟨-, -⟩
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2)) ?_
  rintro s2 ⟨h2, f2, est2, k⟩
  rw [h1.cur] at est2 k
  refine WP.spec_bind (P0.debug.get_breakpoint.p0 st s2 t bp hS) fun r1 _ => ?_
  have hU2 : UserOK st T Cs Ω H U s2 := D.user.ksb (k.ksb.trans h1.node.1)
  obtain ⟨Q2, R2, x2⟩ := BXI.xs (BlkOK.bxi h2) hU2
  have TL : ∀ (s3 : S), XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q2 R2 s2 s3 →
      (do
        let s4 ← sched.set_thread_state st s3 (L.curW s) sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s4)) ⦃ r =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := fun s3 x3 => by
    have hst : L.mem s3 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, x3.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp), ← stA_eq, est2]
    refine WP.spec_bind (sched.set_thread_state.running_bxi x3.bxi hct hst) fun s4 h4 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h4)
  split
  · refine WP.spec_bind (E.buf _ _ _ _ s2 (L.curW s)
    ⟨s, hE, Cur0W.trans c1.fr (Foot.cur0w f2 (Set.empty_subset _))⟩ x2.1 hct) fun b hb => ?_
    refine WP.spec_bind (msg.set_mr.xs x2 hct hb (by simp)) ?_
    rintro ⟨_, sa⟩ ⟨xa, -⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (msg.set_mr.xs xa hct hb (by simp)) ?_
    rintro ⟨_, sb⟩ ⟨xb, -⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (msg.set_mr.xs xb hct hb (by simp)) ?_
    rintro ⟨_, sc⟩ ⟨xc, -⟩
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (msg.set_mr.xs xc hct hb (by simp)) ?_
    rintro ⟨_, sd⟩ ⟨xd, -⟩
    try simp only [uncurry_apply_pair]
    split
    · refine WP.spec_bind (msg.set_mr.xs xd hct hb (by simp)) ?_
      rintro ⟨n, se⟩ ⟨xe, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (tcb.reply_words.xs xe hct) fun sf xf => ?_
      exact TL sf xf
    · refine WP.spec_bind (msg.set_mr.xs xd hct hb (by simp)) ?_
      rintro ⟨n, se⟩ ⟨xe, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (tcb.reply_words.xs xe hct) fun sf xf => ?_
      exact TL sf xf
  · exact TL s2 x2

theorem debug.set_breakpoint.rf {s : S} {t bp vaddr ty size rw : U64} (hT : TcbPlaced T) (ht : t ∈ T)
    (hbp : bp.val < 4) :
    debug.set_breakpoint st s t bp vaddr ty size rw ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold debug.set_breakpoint debug.set_dr7
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> first | exact (WP.spec_ok _).2 trivial |
    (split <;> exact (WP.spec_ok _).2 trivial)) fun _ _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact (WP.spec_ok _).2 trivial
    · split
      · exact (WP.spec_ok _).2 trivial
      · split
        · exact (WP.spec_ok _).2 trivial
        · split <;> exact (WP.spec_ok _).2 trivial) fun _ _ => ?_
  refine WP.spec_bind (obj.Tcb.set_debug_reg.rf (s := s) (v := vaddr) hT ht (by omega)) fun s1 w1 => ?_
  refine WP.spec_bind (P0.debug.dr7.p0 st s1 t hS) fun i _ => ?_
  step as ⟨i1, hi1⟩
  step as ⟨i2, _⟩
  step as ⟨i3, hi3⟩
  step as ⟨i4, _⟩
  simp only [lift, bind_ok]
  step as ⟨i7, _⟩
  step as ⟨i8, _⟩
  step as ⟨i10, _⟩
  try simp only [lift, bind_ok]
  exact WP.spec_mono (obj.Tcb.set_debug_reg.rf (s := s1) hT ht (by simp [debug.DR7])) fun s2 w2 => rf_trans w1 w2

set_option maxHeartbeats 40000000 in
/-- **`SetBreakpoint`** after the stall. -/
theorem tcb.set_breakpoint_checked.dec {A : Type _} {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool}
    {slot : obj.Slot} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    (do
      let (r, s2) ← tcb.set_breakpoint_checked st s1 t { length := len, buf, call, slot, extra }
      ok (r, s2, a1)) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have c1 := h1.cur0 D
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S =>
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2) ?_ ?_
  swap
  · rintro ⟨r, s2⟩ hr
    exact (WP.spec_ok _).2 hr
  have KB : ∀ {bp vaddr ty size rw : U64}, bp.val < 4 →
      (do
        let s2 ← tcb.restart_caller st s1
        let s3 ← debug.set_breakpoint st s2 t bp vaddr ty size rw
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3)) ⦃ r =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := fun {bp vaddr ty size rw} hbp => by
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (debug.set_breakpoint.rf (vaddr := vaddr) (ty := ty) (size := size) (rw := rw)
      (s := s2) hT ht hbp) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_rf h2 w3).1))
  unfold tcb.set_breakpoint_checked
  repeat' (first
    | exact (WP.spec_ok _).2 (Cur0.post c1)
    | (simp only [error.invalid_arg, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1))
    | exact KB ‹_›
    | (refine WP.spec_bind (debug.check_bp_num.lt _) ?_
       rintro (_ | e) ⟨-, hbp⟩
       swap
       · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
           core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
           bind_tc_ok]
         exact (WP.spec_ok _).2 (Cur0.post c1)
       simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
       replace hbp := hbp rfl)
    | refine spec_ite (fun _ => ?_) (fun _ => ?_)
    | step
    | scalar_tac)

/-! ## `WriteRegisters`, `CopyRegisters` -/

theorem cast_usize_small {j : U64} (h : j.val < 2 ^ 32) : (UScalar.cast .Usize j : Usize).val = j.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  rcases System.Platform.numBits_eq with e | e <;> simp [e] <;> omega

theorem tcb.write_registers_loop0.rf {s0 s : S} {dest buf ct n i : U64} (hT : TcbPlaced T) (hd : dest ∈ T)
    (h : WritesIn st s0 s (XferFoot T ∅)) :
    tcb.write_registers_loop0 st s dest buf ct n i ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.write_registers_loop0
  apply loop.spec_decr_nat (measure := fun y => 18 - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.write_registers_loop0.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 18 := by simpa [tcb.N_FRAME, tcb.N_GP] using hj
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    have hl : (UScalar.cast .Usize j : Usize).val < regs.FRAME_REGISTERS.val.length := by
      rw [regs.FRAME_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ hl) fun r hr => ?_
    have hr' : r.val < 384 := by
      rw [hr]; unfold regs.FRAME_REGISTERS
      exact regs_lt _ _ (by simp [layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS, layout.reg.RAX,
        layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP,
        layout.reg.R8, layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13,
        layout.reg.R14, layout.reg.R15]) _ (List.getElem_mem _)
    step as ⟨i2, _⟩
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s1 ct buf _ hS) fun v _ => ?_
    refine WP.spec_bind (P0.regs.sanitise.p0 r v) fun v5 _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hd hr') fun s2 w2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨rf_trans h1 w2, by omega⟩
  · exact h

theorem tcb.write_registers_loop1.rf {s0 s : S} {dest buf ct n i : U64} (hT : TcbPlaced T) (hd : dest ∈ T)
    (h : WritesIn st s0 s (XferFoot T ∅)) :
    tcb.write_registers_loop1 st s dest buf ct n i ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.write_registers_loop1
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.write_registers_loop1.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_FRAME, tcb.N_GP] using hj
    step as ⟨i0, _⟩
    split
    swap
    · exact (WP.spec_ok _).2 h1
    simp only [lift, bind_ok]
    have hl : (UScalar.cast .Usize j : Usize).val < regs.GP_REGISTERS.val.length := by
      rw [regs.GP_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ hl) fun r hr => ?_
    have hr' : r.val < 384 := by
      rw [hr]; unfold regs.GP_REGISTERS
      exact regs_lt _ _ (by simp [layout.reg.FS_BASE, layout.reg.GS_BASE]) _ (List.getElem_mem _)
    step as ⟨i2, _⟩
    refine WP.spec_bind (P0.msg.syscall_arg.p0 st s1 ct buf _ hS) fun v _ => ?_
    refine WP.spec_bind (P0.regs.sanitise.p0 r v) fun v5 _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hd hr') fun s2 w2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨rf_trans h1 w2, by omega⟩
  · exact h

theorem tcb.copy_registers_loop0.rf {s0 s : S} {dest src i : U64} (hT : TcbPlaced T) (hd : dest ∈ T)
    (h : WritesIn st s0 s (XferFoot T ∅)) :
    tcb.copy_registers_loop0 st s dest src i ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.copy_registers_loop0
  apply loop.spec_decr_nat (measure := fun y => 18 - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.copy_registers_loop0.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 18 := by simpa [tcb.N_FRAME, tcb.N_GP] using hj
    simp only [lift, bind_ok]
    have hl : (UScalar.cast .Usize j : Usize).val < regs.FRAME_REGISTERS.val.length := by
      rw [regs.FRAME_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ hl) fun r hr => ?_
    have hr' : r.val < 384 := by
      rw [hr]; unfold regs.FRAME_REGISTERS
      exact regs_lt _ _ (by simp [layout.reg.FAULT_IP, layout.reg.RSP, layout.reg.FLAGS, layout.reg.RAX, layout.reg.RBX, layout.reg.RCX, layout.reg.RDX, layout.reg.RSI, layout.reg.RDI, layout.reg.RBP, layout.reg.R8, layout.reg.R9, layout.reg.R10, layout.reg.R11, layout.reg.R12, layout.reg.R13, layout.reg.R14, layout.reg.R15]) _ (List.getElem_mem _)
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (P0.regs.sanitise.p0 r v) fun v5 _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hd hr') fun s2 w2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨rf_trans h1 w2, by omega⟩
  · exact h

theorem tcb.copy_registers_loop1.rf {s0 s : S} {dest src i : U64} (hT : TcbPlaced T) (hd : dest ∈ T)
    (h : WritesIn st s0 s (XferFoot T ∅)) :
    tcb.copy_registers_loop1 st s dest src i ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.copy_registers_loop1
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.copy_registers_loop1.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_FRAME, tcb.N_GP] using hj
    simp only [lift, bind_ok]
    have hl : (UScalar.cast .Usize j : Usize).val < regs.GP_REGISTERS.val.length := by
      rw [regs.GP_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ hl) fun r hr => ?_
    have hr' : r.val < 384 := by
      rw [hr]; unfold regs.GP_REGISTERS
      exact regs_lt _ _ (by simp [layout.reg.FS_BASE, layout.reg.GS_BASE]) _ (List.getElem_mem _)
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (P0.regs.sanitise.p0 r v) fun v5 _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hd hr') fun s2 w2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨rf_trans h1 w2, by omega⟩
  · exact h

theorem tcb.copy_registers_loop2.rf {s0 s : S} {dest src i : U64} (hT : TcbPlaced T) (hd : dest ∈ T)
    (h : WritesIn st s0 s (XferFoot T ∅)) :
    tcb.copy_registers_loop2 st s dest src i ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold tcb.copy_registers_loop2
  apply loop.spec_decr_nat (measure := fun y => 2 - y.2.val)
    (inv := fun y => WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold tcb.copy_registers_loop2.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 2 := by simpa [tcb.N_FRAME, tcb.N_GP] using hj
    simp only [lift, bind_ok]
    have hl : (UScalar.cast .Usize j : Usize).val < regs.GP_REGISTERS.val.length := by
      rw [regs.GP_REGISTERS.property]; rw [cast_usize_small (by omega)]; simp; omega
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ hl) fun r hr => ?_
    have hr' : r.val < 384 := by
      rw [hr]; unfold regs.GP_REGISTERS
      exact regs_lt _ _ (by simp [layout.reg.FS_BASE, layout.reg.GS_BASE]) _ (List.getElem_mem _)
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st src s1 r hS) fun v _ => ?_
    refine WP.spec_bind (P0.regs.sanitise.p0 r v) fun v5 _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := v5) (s := s1) hT hd hr') fun s2 w2 => ?_
    step as ⟨j2, hj2⟩
    exact ⟨rf_trans h1 w2, by omega⟩
  · exact h


theorem tcb.post_modify_registers.rf {s : S} {t : U64} (hT : TcbPlaced T) (ht : t ∈ T) :
    tcb.post_modify_registers st s t ⦃ s' => WritesIn st s s' (XferFoot T ∅) ⦄ := by
  unfold tcb.post_modify_registers
  refine WP.spec_bind (sched.cur_thread.spec s) fun t1 _ => ?_
  refine WP.spec_bind (tcb_ne.blk t t1) fun b _ => ?_
  split
  · exact obj.Tcb.set_reg.rf (v := 0#u64) hT ht (by simp [layout.reg.ERROR])
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

/-- The reschedule tail of the register writes. -/
theorem resched_tail {A : Type _} {s : S} {a : A} {d : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (do
      let t ← sched.cur_thread st s
      let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq d t
      if b then do
        let s6 ← sched.reschedule_required st s
        ok (s6, a)
      else ok (s, a)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  refine WP.spec_bind (sched.cur_thread.spec s) fun t1 _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · exact WP.spec_bind (sched.reschedule_required.blk s h) fun s6 h6 => (WP.spec_ok _).2 h6.1
  · exact (WP.spec_ok _).2 h

set_option maxHeartbeats 2000000 in
theorem tcb.write_registers.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {dest : U64} {resume : Bool} {n buf : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hd : dest ∈ T) :
    tcb.write_registers st ar s a dest resume n buf ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.write_registers
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct _ => ?_
  step as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun nn _ => ?_
  refine WP.spec_bind (tcb.write_registers_loop0.rf (s0 := s) hT hd (WritesIn.refl _ _)) fun s1 w1 => ?_
  refine WP.spec_bind (tcb.write_registers_loop1.rf (s0 := s) hT hd w1) fun s2 w2 => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st dest s2 _ hS) fun pc _ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.rf (v := pc) (s := s2) hT hd (by simp [layout.reg.NEXT_IP])) fun s3 w3 => ?_
  refine WP.spec_bind (tcb.post_modify_registers.rf (s := s3) hT hd) fun s4 w4 => ?_
  have h4 := (blk_rf h (rf_trans (rf_trans w2 w3) w4)).1
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.restart.tinv hA s4 a dest h4 hd) fun r hr => by
        obtain ⟨s5, a5⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h4
  rintro ⟨s5, a5⟩ h5
  exact resched_tail h5

set_option maxHeartbeats 2000000 in
/-- **`WriteRegisters`** after the stall. -/
theorem tcb.decode_write_registers.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_write_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_write_registers
  split
  · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun w _ => ?_
  step as ⟨i, _⟩
  split
  · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
  simp only [lift, bind_ok]
  refine WP.spec_bind (tcb.write_registers.blk hA h2 ht) ?_
  rintro ⟨s3, a3⟩ h3
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))

end

end Fl4Proofs.P1
