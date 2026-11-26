/-
P3 (line jboot, gen 3): **the scheduler and spec-side conjuncts of `JAtZ` at the witness** (`fInitASt`, `w0`;
JBootZ's ghosts: `N = E = R = B = ∅`, `T = T0`, `C = C0`, core 0, `Lst = fun _ => []`).

Spec only (through the boot heap's characterisation `bootHeap_fInit`):
**`fInit_nsc`** (`NSC`), **`fInit_inv`** (`Inv`), **`fInit_curInv`** (`CurInv`), **`fInit_own`** (`CurOwnW`),
**`fInit_off`** (`OffOK`), **`fInit_act`** (`ActIdle`), **`fInit_sv`** (`SchedValid`), **`fInit_isorted`**
(`IpcSorted`), **`fInit_slink`** (`ScLinkHyp`), **`fInit_curRun`** (`CurRunM`), **`fInit_obj`** (`ObjCover`).

With the image `w0` (the idle TCB's yield, MCP, flags and IPC-buffer words and the idle SC's `REPLY` word zero):
**`w0_yld`** (`YieldRel`), **`w0_mcp`** (`McpRel`), **`w0_buf`** (`BufWordRel`), **`w0_call`** (`CallRel`),
**`w0_rfree`** (`RFree`), **`w0_rrecv`** (`RRecv`), **`w0_ipc`** (`IpcRel`, `XTopAt.ipc`), **`w0_esa`**
(`EpSchedApart`, `XTopAt.esa`).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp
  Fl4Proofs.P3.Ipc Fl4Proofs.P2.Wit

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The witness's spec objects -/

/-- Every object of `fInitASt` is the idle TCB, the idle SC, an empty radix-0 CNode or a global table. -/
theorem fInit_objs {p : ObjRef} {o : KernelObject} (h : fInitASt.kheap p = some o) :
    o = .tcb idleTcbV ∨ o = .schedContext idleScV 0 ∨ o = cn0 ∨ o = .archObj (.pageMapL4 globalPml4) ∨
      o = .archObj (.pdPointerTable globalPdpt) ∨ o = .archObj (.pageDirectory globalPd) := by
  have h' : fInitKheap p = some o := h
  rcases bootHeap_fInit.obj _ _ h' with rfl | rfl | e | e | e | e
  · rw [bootHeap_fInit.tcb] at h'; cases h'; exact Or.inl rfl
  · rw [bootHeap_fInit.sc] at h'; cases h'; exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl e))
  · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))

theorem fInit_no_reply {p : ObjRef} {x : Reply} (h : fInitASt.kheap p = some (.reply x)) : False := by
  rcases fInit_objs h with e | e | e | e | e | e <;> cases e

theorem fInit_tcb_of {p : ObjRef} {x : Tcb} (h : fInitASt.kheap p = some (.tcb x)) :
    p = idleThreadPtr ∧ x = idleTcbV := bootHeap_fInit.tcb_of h

theorem fInit_sc_of {p : ObjRef} {y : SchedContext} {n : Nat} (h : fInitASt.kheap p = some (.schedContext y n)) :
    p = idleScPtr ∧ y = idleScV ∧ n = 0 := bootHeap_fInit.sc_of h

theorem fInit_no_ep {p : ObjRef} {x : Endpoint} (h : fInitASt.kheap p = some (.endpoint x)) : False :=
  bootHeap_fInit.no_ep h

theorem fInit_no_ntfn {p : ObjRef} {x : Notification} (h : fInitASt.kheap p = some (.notification x)) : False :=
  bootHeap_fInit.no_ntfn h

theorem fInit_kTcb : fInitASt.kheap idleThreadPtr = some (.tcb idleTcbV) := bootHeap_fInit.tcb
theorem fInit_kSc : fInitASt.kheap idleScPtr = some (.schedContext idleScV 0) := bootHeap_fInit.sc

/-! ## The scheduler invariants (spec only) -/

theorem fInit_nsc : Sched.NSC ∅ C0 fInitASt := fun _ hn => hn.elim

theorem idleSc_rrok : RRok idleScV := by
  refine ⟨by simp [idleScV], ?_, SInvR.minBudget_le_maxPeriod⟩
  have := MAX_PERIOD.isLt
  (simp [idleScV]) <;> omega

/-- **`Inv` at `fInitASt`.** -/
theorem fInit_inv : Sched.Inv fInitASt where
  rq _ _ _ h := (List.not_mem_nil h).elim
  rel _ h := (List.not_mem_nil h).elim
  sorted := List.Pairwise.nil
  rd u x hk hc := by
    obtain ⟨-, rfl⟩ := fInit_tcb_of hk
    exfalso
    rcases hc with h | ⟨n, h⟩ | ⟨e, d, h, -⟩ | ⟨e, r, d, h⟩
    · exact absurd h (by decide)
    all_goals simp [idleTcbV] at h
  refills p y n hk _ hper := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    exact absurd rfl hper
  back u x p hk hp := by
    obtain ⟨rfl, rfl⟩ := fInit_tcb_of hk
    have e : p = idleScPtr := by simp [idleTcbV] at hp; exact hp.symm
    subst e
    exact ⟨idleScV, 0, fInit_kSc, rfl⟩
  ntfnSc _ _ _ h _ := (fInit_no_ntfn h).elim
  ne p y n hk _ := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    simp [idleScV]
  rr p y n hk _ _ := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    exact idleSc_rrok

theorem idle_notIpcBlk : NotIpcBlk idleTcbV.tcbState := by
  unfold NotIpcBlk
  refine ⟨fun q h => ?_, fun e d h => ?_, fun e r d h => ?_⟩ <;> simp [idleTcbV] at h

/-- **`CurInv` at `fInitASt`** (the idle thread current, bound to the idle SC). -/
theorem fInit_curInv : Sched.CurInv fInitASt where
  tcb := ⟨idleTcbV, fInit_kTcb, rfl, idle_notIpcBlk⟩
  sc := ⟨idleScV, 0, fInit_kSc⟩
  active h := absurd rfl h
  notRel := List.not_mem_nil

/-- **`CurOwnW` at `fInitASt`**: the idle TCB owns the current (idle) SC. -/
theorem fInit_own : Sched.CurOwnW T0 C0 fInitASt := by
  refine Or.inl ⟨idT, Set.mem_singleton idT, idleTcbV, fInit_idleTcb, rfl, fun x n hk => ?_,
    fun h => absurd h (by decide)⟩
  obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
  rw [idT_bv]; rfl

/-- **`OffOK` at `fInitASt`** (no consumed time). -/
theorem fInit_off : Sched.OffOK fInitASt := fun h => absurd h (by decide)

/-- **`ActIdle` at `fInitASt`.** -/
theorem fInit_act : Sched.ActIdle fInitASt := by
  unfold ActIdle ActSched IdleOK
  exact ⟨fun _ h => by simp [fInitASt, initASt] at h, ⟨idleTcbV, fInit_kTcb, rfl, rfl, List.not_mem_nil⟩⟩

/-- **`SchedValid` at `fInitASt`.** -/
theorem fInit_sv : Sched.SchedValid fInitASt where
  epQ _ _ h := (fInit_no_ep h).elim
  ntfnQ _ _ h := (fInit_no_ntfn h).elim
  recvQ t x ep ro d hk hs := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hs
  sendQ t x ep pl hk hs := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hs
  ntfnW t x n hk hs := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hs
  recvReply t x ep r d hk hs := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hs
  onReply t x r hk hs := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hs
  replyTcb _ _ _ h _ := (fInit_no_reply h).elim
  replies sc y k r hk hr := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    simp [idleScV, defaultSchedContext] at hr
  scTcb sc y k f hk hf := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    have e : f = idleThreadPtr := by simp [idleScV] at hf; exact hf.symm
    subst e
    exact ⟨idleTcbV, fInit_kTcb⟩
  scNtfn sc y k n hk hf := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    simp [idleScV, defaultSchedContext] at hf
  scYieldFrom sc y k t hk hf := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    simp [idleScV, defaultSchedContext] at hf
  tcbYieldTo t x p hk hy := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hy
  tcbNtfn t x n hk hn := by obtain ⟨-, rfl⟩ := fInit_tcb_of hk; simp [idleTcbV] at hn
  ntfnTcb _ _ _ h _ := (fInit_no_ntfn h).elim
  scSpor sc y k hk hs := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    simp [idleScV, defaultSchedContext] at hs

/-- **`IpcSorted` at `fInitASt`** (no endpoint, no notification). -/
theorem fInit_isorted : Sched.IpcSorted fInitASt :=
  ⟨fun _ _ h => (fInit_no_ep h).elim, fun _ _ h => (fInit_no_ntfn h).elim⟩

/-- **`ScLinkHyp` at `fInitASt`.** -/
theorem fInit_slink : Sched.ScLinkHyp fInitASt := fInit_sv.toLink

/-- **`CurRunM` at `fInitASt`** (the idle thread current). -/
theorem fInit_curRun : CurRunM fInitASt := Or.inr (Or.inr rfl)

/-- **`ObjCover` at `fInitASt`** (`N = E = R = ∅`, `T = T0`, `C = C0`). -/
theorem fInit_obj : Sched.ObjCover ∅ T0 ∅ ∅ C0 fInitASt where
  tcb o x h := by obtain ⟨rfl, -⟩ := fInit_tcb_of h; exact ⟨idT, Set.mem_singleton idT, idT_bv⟩
  ntfn _ _ h := (fInit_no_ntfn h).elim
  ep _ _ h := (fInit_no_ep h).elim
  reply _ _ h := (fInit_no_reply h).elim
  sc o y k h := by obtain ⟨rfl, -⟩ := fInit_sc_of h; exact ⟨idS, Set.mem_singleton idS, idS_bv⟩

/-! ## With the image -/

theorem yield_w0 : wL.mem w0 (yieldA idT) = 0#u64 := by
  unfold yieldA; exact tcbZ _ (by decide) (by decide) (by decide) (by decide)

theorem mcp_w0 : wL.mem w0 (mcpA idT) = 0#u64 := by
  unfold mcpA; exact tcbZ _ (by decide) (by decide) (by decide) (by decide)

theorem flags_w0 : wL.mem w0 (flagsA idT) = 0#u64 := by
  unfold flagsA; exact tcbZ _ (by decide) (by decide) (by decide) (by decide)

theorem ipcBuf_w0 : wL.mem w0 (tIpcBufA idT) = 0#u64 := by
  unfold tIpcBufA; exact tcbZ _ (by decide) (by decide) (by decide) (by decide)

theorem scReply_w0 : wL.mem w0 (scReplyA idS) = 0#u64 := by
  unfold scReplyA layout.sc.REPLY
  rw [scW_v _ (by decide) (by decide)]
  decide

/-- **`YieldRel` at the witness** (no yield: the idle TCB's `YIELD_TO` word 0, the idle SC's `yield_from` none). -/
theorem w0_yld : Sched.YieldRel T0 C0 (wL.mem w0) fInitASt where
  tcb t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    exact ⟨idleTcbV, fInit_idleTcb, by rw [yield_w0, optRef_zero]; rfl⟩
  toSc t ht h := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    exact absurd yield_w0 h
  frm sc hsc y n hk p hp := by
    obtain ⟨-, rfl, -⟩ := fInit_sc_of hk
    simp [idleScV, defaultSchedContext] at hp

/-- **`McpRel` at the witness** (MCP 0, no flags). -/
theorem w0_mcp : Sched.McpRel T0 (wL.mem w0) fInitASt := by
  intro t ht
  rw [T0, Set.mem_singleton_iff] at ht; subst ht
  refine ⟨idleTcbV, fInit_idleTcb, by rw [mcp_w0]; rfl, ?_⟩
  rw [flags_w0]
  ext f
  simp [wordToTcbFlags, idleTcbV]

/-- **`BufWordRel` at the witness** (IPC buffer 0). -/
theorem w0_buf : BufWordRel T0 (wL.mem w0) fInitASt := by
  intro t ht
  rw [T0, Set.mem_singleton_iff] at ht; subst ht
  exact ⟨idleTcbV, fInit_idleTcb, by rw [ipcBuf_w0]; rfl⟩

/-- **`CallRel` at the witness** (no reply; the idle SC's stack empty). -/
theorem w0_call : Sched.CallRel (wL.mem w0) ∅ C0 fInitASt (fun _ => []) where
  stack sc hsc := by
    rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    refine ⟨⟨idleScV, 0, fInit_idleSc, rfl⟩, fun _ h => (List.not_mem_nil h).elim, List.nodup_nil, ?_, ?_⟩
    · rw [scReply_w0]; rfl
    · intro i h; exact absurd h (Nat.not_lt_zero _)
  excl _ _ _ _ _ h := (List.not_mem_nil h).elim
  reply _ h := h.elim
  det _ h := h.elim

theorem w0_rfree : Sched.RFree (wL.mem w0) ∅ C0 fInitASt (fun _ => []) := fun _ h => h.elim

theorem w0_rrecv : Sched.RRecv (wL.mem w0) ∅ fInitASt := fun _ h => h.elim

/-- **`IpcRel` at the witness** (`XTopAt.ipc`). -/
theorem w0_ipc : IpcRel ∅ T0 ∅ ∅ ∅ (wL.mem w0) fInitASt :=
  IpcRel.of w0_ntfnStateRel w0_epStateRel (sched_sc w0_schedRel)

/-- A word outside the idle TCB is no endpoint footprint word. -/
theorem efoot_far {a : U64} (h : a.val < 18446744071562072064 ∨ 18446744071562072064 + 4096 ≤ a.val) :
    ¬ EFoot T0 ∅ ∅ ∅ a := by
  rintro (⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, hf⟩ | ⟨wp, hw, -⟩)
  · exact he
  · exact hr
  · rw [T0, Set.mem_singleton_iff] at ht; subst ht
    rcases hf with ⟨h1, h2⟩ | h3
    · rw [idT_val] at h1 h2; unfold TOffN at h2; omega
    · unfold TL at h3; rw [idT_val] at h3; omega
  · exact hw

theorem ewrite_far {a : U64} (h : a.val < 18446744071562072064 ∨ 18446744071562072064 + 4096 ≤ a.val) :
    ¬ EWrite T0 ∅ ∅ ∅ a := by
  rintro (⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, hf⟩ | ⟨wp, hw, -⟩)
  · exact he
  · exact hr
  · rw [T0, Set.mem_singleton_iff] at ht; subst ht
    rcases hf with ⟨h1, h2⟩ | h3
    · rw [idT_val] at h1 h2; unfold TWOffN at h2; omega
    · unfold TL at h3; rw [idT_val] at h3; omega
  · exact hw

/-- **`EpSchedApart` at the witness** (`XTopAt.esa`): no endpoint word on core 0's node, the domain words or the
idle SC. -/
theorem w0_esa : EpSchedApart wst T0 C0 ∅ ∅ ∅ 0#u64 w0 fInitASt where
  node a h1 h2 := efoot_far (by rw [nodeBase_w0] at h1; omega)
  dom := ewrite_far (by
    unfold curDomA; rw [wa_val (by rw [ksb_w0, fkb_val]; decide), ksb_w0, fkb_val]; decide)
  dt := ewrite_far (by
    unfold dtA; rw [wa_val (by rw [ksb_w0, fkb_val]; decide), ksb_w0, fkb_val]; decide)
  sc sc hsc x n hk a ha := by
    rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    rw [fInit_idleSc] at hk; cases hk
    obtain ⟨h1, h2⟩ := ha
    rw [idS_val] at h1 h2
    simp only [minSchedContextBits] at h2
    exact ewrite_far (by omega)

end

end Fl4Proofs.P3.JBoot
