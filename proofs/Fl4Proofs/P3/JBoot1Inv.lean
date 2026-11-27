/-
P3 (line jboot, gen 4): **the TCB-word relations of `JAtZ` at the richer witness** (`w1`, `σ1`, `T1`, `C1`):
**`w1_yld`** (`YieldRel`), **`w1_mcp`** (`McpRel`), **`w1_buf`** (`BufWordRel`), **`w1_call`** (`CallRel`: both
SCs' call stacks empty, their `REPLY` words 0), **`w1_rfree`**, **`w1_rrecv`**, **`w1_ipc`** (`IpcRel`) and
**`w1_esa`** (`EpSchedApart`).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1Mem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp
  Fl4Proofs.P3.Ipc Fl4Proofs.P2.Wit

noncomputable section

set_option maxHeartbeats 1000000

theorem yield_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (yieldA t) = 0#u64 := by
  unfold yieldA; exact tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem mcp_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (mcpA t) = 0#u64 := by
  unfold mcpA; exact tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem flags_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (flagsA t) = 0#u64 := by
  unfold flagsA; exact tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem ipcBuf_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (tIpcBufA t) = 0#u64 := by
  unfold tIpcBufA; exact tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem scReply_w1 (c : U64) (hc : c ∈ C1) : wL.mem w1 (scReplyA c) = 0#u64 := by
  unfold scReplyA layout.sc.REPLY
  rcases memC1 hc with rfl | rfl
  · rw [scW1_v _ (by decide) (by decide)]; decide
  · rw [rsW_v _ (by decide) (by decide)]; decide

/-- The TCBs of `T1`: their spec objects. -/
theorem tcb1 {t : U64} (ht : t ∈ T1) :
    (t = idT ∧ σ1.kheap t.bv = some (.tcb idleTcbV)) ∨ (t = rT ∧ σ1.kheap t.bv = some (.tcb rootTcbV)) := by
  rcases memT1 ht with rfl | rfl
  · exact Or.inl ⟨rfl, σ1_idleTcb⟩
  · exact Or.inr ⟨rfl, σ1_rootTcb⟩

/-- **`YieldRel` at `w1`** (no yield). -/
theorem w1_yld : Sched.YieldRel T1 C1 (wL.mem w1) σ1 where
  tcb t ht := by
    rcases tcb1 ht with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
    · exact ⟨idleTcbV, hk, by rw [yield_w1 _ ht, optRef_zero]; rfl⟩
    · exact ⟨rootTcbV, hk, by rw [yield_w1 _ ht, optRef_zero]; rfl⟩
  toSc t ht h := absurd (yield_w1 t ht) h
  frm sc hsc y n hk p hp := by
    rcases kh1_sc_of hk with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp [rootScV, idleScV, defaultSchedContext] at hp

/-- **`McpRel` at `w1`** (MCP 0, no flags). -/
theorem w1_mcp : Sched.McpRel T1 (wL.mem w1) σ1 := by
  intro t ht
  rcases tcb1 ht with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · refine ⟨idleTcbV, hk, by rw [mcp_w1 _ ht]; rfl, ?_⟩
    rw [flags_w1 _ ht]; ext f; simp [wordToTcbFlags, idleTcbV]
  · refine ⟨rootTcbV, hk, by rw [mcp_w1 _ ht]; rfl, ?_⟩
    rw [flags_w1 _ ht]; ext f; simp [wordToTcbFlags, rootTcbV, idleTcbV]

/-- **`BufWordRel` at `w1`** (IPC buffers 0). -/
theorem w1_buf : BufWordRel T1 (wL.mem w1) σ1 := by
  intro t ht
  rcases tcb1 ht with ⟨rfl, hk⟩ | ⟨rfl, hk⟩
  · exact ⟨idleTcbV, hk, by rw [ipcBuf_w1 _ ht]; rfl⟩
  · exact ⟨rootTcbV, hk, by rw [ipcBuf_w1 _ ht]; rfl⟩

/-- **`CallRel` at `w1`** (no reply; both SCs' stacks empty). -/
theorem w1_call : Sched.CallRel (wL.mem w1) ∅ C1 σ1 (fun _ => []) where
  stack sc hsc := by
    rcases memC1 hsc with rfl | rfl
    · refine ⟨⟨idleScV, 0, σ1_idleSc', rfl⟩, fun _ h => (List.not_mem_nil h).elim, List.nodup_nil, ?_, ?_⟩
      · rw [scReply_w1 _ hsc]; rfl
      · intro i h; exact absurd h (Nat.not_lt_zero _)
    · refine ⟨⟨rootScV, 0, σ1_rootSc, rfl⟩, fun _ h => (List.not_mem_nil h).elim, List.nodup_nil, ?_, ?_⟩
      · rw [scReply_w1 _ hsc]; rfl
      · intro i h; exact absurd h (Nat.not_lt_zero _)
  excl _ _ _ _ _ h := (List.not_mem_nil h).elim
  reply _ h := h.elim
  det _ h := h.elim

theorem w1_rfree : Sched.RFree (wL.mem w1) ∅ C1 σ1 (fun _ => []) := fun _ h => h.elim

theorem w1_rrecv : Sched.RRecv (wL.mem w1) ∅ σ1 := fun _ h => h.elim

/-- **`IpcRel` at `w1`** (`XTopAt.ipc`). -/
theorem w1_ipc : IpcRel ∅ T1 ∅ ∅ ∅ (wL.mem w1) σ1 :=
  IpcRel.of w1_ntfnStateRel w1_epStateRel (sched_sc w1_schedRel)

theorem efoot1_far {a : U64}
    (h : (a.val < 18446744071562072064 ∨ 18446744071562072064 + 4096 ≤ a.val) ∧
      (a.val < 18446744071562100736 ∨ 18446744071562100736 + 4096 ≤ a.val)) :
    ¬ EFoot T1 ∅ ∅ ∅ a := by
  rintro (⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, hf⟩ | ⟨wp, hw, -⟩)
  · exact he
  · exact hr
  · rcases memT1 ht with rfl | rfl <;> rcases hf with ⟨h1, h2⟩ | h3
    · rw [idT_val] at h1 h2; unfold TOffN at h2; omega
    · unfold TL at h3; rw [idT_val] at h3; omega
    · rw [rT_val] at h1 h2; unfold TOffN at h2; omega
    · unfold TL at h3; rw [rT_val] at h3; omega
  · exact hw

theorem ewrite1_far {a : U64}
    (h : (a.val < 18446744071562072064 ∨ 18446744071562072064 + 4096 ≤ a.val) ∧
      (a.val < 18446744071562100736 ∨ 18446744071562100736 + 4096 ≤ a.val)) :
    ¬ EWrite T1 ∅ ∅ ∅ a := by
  rintro (⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, hf⟩ | ⟨wp, hw, -⟩)
  · exact he
  · exact hr
  · rcases memT1 ht with rfl | rfl <;> rcases hf with ⟨h1, h2⟩ | h3
    · rw [idT_val] at h1 h2; unfold TWOffN at h2; omega
    · unfold TL at h3; rw [idT_val] at h3; omega
    · rw [rT_val] at h1 h2; unfold TWOffN at h2; omega
    · unfold TL at h3; rw [rT_val] at h3; omega
  · exact hw

/-- **`EpSchedApart` at `w1`** (`XTopAt.esa`). -/
theorem w1_esa : EpSchedApart wst T1 C1 ∅ ∅ ∅ 0#u64 w1 σ1 where
  node a h1 h2 := efoot1_far (by rw [nodeBase_w1] at h1; omega)
  dom := ewrite1_far (by
    unfold curDomA; rw [wa_val (by rw [ksb_w1, fkb_val]; decide), ksb_w1, fkb_val]; decide)
  dt := ewrite1_far (by
    unfold dtA; rw [wa_val (by rw [ksb_w1, fkb_val]; decide), ksb_w1, fkb_val]; decide)
  sc sc hsc x n hk a ha := by
    rcases memC1 hsc with rfl | rfl
    · rw [σ1_idleSc'] at hk; cases hk
      obtain ⟨h1, h2⟩ := scObj_val ha
      rw [idS_val] at h1 h2
      exact ewrite1_far (by omega)
    · rw [σ1_rootSc] at hk; cases hk
      obtain ⟨h1, h2⟩ := scObj_val ha
      rw [rS_val] at h1 h2
      exact ewrite1_far (by omega)

end

end Fl4Proofs.P3.JBoot
