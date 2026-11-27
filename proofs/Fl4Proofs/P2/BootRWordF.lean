/-
# P2 (line p3mc, gen 39, unit D): the word-relation and frame `JAtZ` fields at the second boot start

At `(sR, σR)` (P2/BootRSpec, P2/BootRMem) with the ghosts `ZR` (P2/BootRZ: `T = {tiB, tRw}`, `C = {sciB, scRw}`,
`R = ∅`) and the empty call stacks `LstB`, gen 35's `P2/BootWordF` ported:

* `call` (**`ZR_call`**: both SCs' `sc_replies = []`, their `REPLY` words 0; no reply), `rfree`, `rrecv` (no reply);
* `yld` (**`ZR_yld`**: both TCBs' `YIELD_TO` words 0 = `tcb_yield_to = None`, neither SC yielded from), `mcp`
  (`MCP` / `FLAGS` words 0 = MCP 0, no flag), `buf` (`IPC_BUFFER` words 0 = 0);
* `bok` (**`σR_bok`**: both TCBs' IPC frame caps null), `fcov` (`σR` has no data page), `fcap` and `vsc`: every slot
  of `thR` holds the null cap but the root slot (`Thread tRw`) and the timeout-handler slot (`SchedContext scRw 7`),
  neither a frame nor a VSpace cap.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

theorem uD_tR_off {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add tRw k).val = 18446744071562076160 + n :=
  wa_val (by rw [tRw_val, hk]) (by omega)

theorem uD_scR_off {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add scRw k).val = 18446744071562080256 + n :=
  wa_val (by rw [scRw_val, hk]) (by omega)

/-- The idle TCB in `σR`. -/
theorem uD_σR_ti : (σR (Z := Unit)).kheap tiB.bv = some (.tcb idleTcbB) :=
  (kheapR_of_ne (p := tiB.bv) (by decide) (by decide)).trans σB_ti

/-- The idle SC in `σR`. -/
theorem uD_σR_sci : (σR (Z := Unit)).kheap sciB.bv = some (.schedContext idleScB 0) :=
  (kheapR_of_ne (p := sciB.bv) (by decide) (by decide)).trans σB_sci

/-- The root TCB in `σR`. -/
theorem uD_σR_tR : (σR (Z := Unit)).kheap tRw.bv = some (.tcb tcbR) := kheapR_tR

/-- The root SC in `σR`. -/
theorem uD_σR_scR : (σR (Z := Unit)).kheap scRw.bv = some (.schedContext scR 0) := kheapR_scR

/-! ## The call stacks and the replies (no reply) -/

theorem ZR_call : CallRel (bsL.mem sR) ZR.R ZR.C (σR (Z := Unit)) LstB where
  stack sc hsc := by
    rcases ZR_C.1 hsc with rfl | rfl
    · refine ⟨⟨idleScB, 0, uD_σR_sci, rfl⟩, fun r h => (List.not_mem_nil h).elim, List.nodup_nil, ?_, ?_⟩
      · show bsL.mem sR (scReplyA sciB) = 0#u64
        have hv : (scReplyA sciB).val = 18446744071562096640 + 32 :=
          sciB_off (by simp [layout.sc.REPLY]) (by omega)
        rw [memR_at hv (by omega)]; exact wordR_zero_of (by omega)
      · intro i h; exact absurd h (Nat.not_lt_zero _)
    · refine ⟨⟨scR, 0, uD_σR_scR, rfl⟩, fun r h => (List.not_mem_nil h).elim, List.nodup_nil, ?_, ?_⟩
      · show bsL.mem sR (scReplyA scRw) = 0#u64
        have hv : (scReplyA scRw).val = 18446744071562080256 + 32 :=
          uD_scR_off (by simp [layout.sc.REPLY]) (by omega)
        rw [memR_at hv (by omega)]; exact wordR_zero_of (by omega)
      · intro i h; exact absurd h (Nat.not_lt_zero _)
  excl _ _ _ _ r h := (List.not_mem_nil h).elim
  reply _ h := h.elim
  det _ h := h.elim

theorem ZR_rfree : RFree (bsL.mem sR) ZR.R ZR.C (σR (Z := Unit)) LstB := fun _ h => h.elim

theorem ZR_rrecv : RRecv (bsL.mem sR) ZR.R (σR (Z := Unit)) := fun _ h => h.elim

/-! ## The TCBs' words -/

theorem uD_yield_ti : bsL.mem sR (yieldA tiB) = 0#u64 := by
  have hv : (yieldA tiB).val = 18446744071562072064 + 3472 := tiB_off (by decide) (by omega)
  rw [memR_at hv (by omega)]; exact wordR_zero_of (by omega)

theorem uD_yield_tR : bsL.mem sR (yieldA tRw) = 0#u64 := by
  have hv : (yieldA tRw).val = 18446744071562076160 + 3472 := uD_tR_off (by decide) (by omega)
  rw [memR_at hv (by omega)]; exact wordR_zero_of (by omega)

theorem ZR_yld : YieldRel ZR.T ZR.C (bsL.mem sR) (σR (Z := Unit)) where
  tcb t ht := by
    rcases ZR_T.1 ht with rfl | rfl
    · exact ⟨idleTcbB, uD_σR_ti, by rw [uD_yield_ti, optRef_zero]; rfl⟩
    · exact ⟨tcbR, uD_σR_tR, by rw [uD_yield_tR, optRef_zero]; rfl⟩
  toSc t ht h0 := by
    rcases ZR_T.1 ht with rfl | rfl
    · exact absurd uD_yield_ti h0
    · exact absurd uD_yield_tR h0
  frm sc hsc y n hy p hp := by
    rcases ZR_C.1 hsc with rfl | rfl
    · rw [uD_σR_sci] at hy
      cases hy
      rw [show idleScB.scYieldFrom = none from rfl] at hp; cases hp
    · rw [uD_σR_scR] at hy
      cases hy
      rw [show scR.scYieldFrom = none from rfl] at hp; cases hp

theorem ZR_mcp : McpRel ZR.T (bsL.mem sR) (σR (Z := Unit)) := by
  intro t ht
  rcases ZR_T.1 ht with rfl | rfl
  · have hm : (mcpA tiB).val = 18446744071562072064 + 3440 := tiB_off (by decide) (by omega)
    have hf : (flagsA tiB).val = 18446744071562072064 + 3456 := tiB_off (by decide) (by omega)
    refine ⟨idleTcbB, uD_σR_ti, ?_, ?_⟩
    · rw [memR_at hm (by omega), wordR_zero_of (by omega)]; rfl
    · rw [memR_at hf (by omega), wordR_zero_of (by omega)]
      show Fl4Spec.wordToTcbFlags 0 = ∅
      ext f; simp [Fl4Spec.wordToTcbFlags]
  · have hm : (mcpA tRw).val = 18446744071562076160 + 3440 := uD_tR_off (by decide) (by omega)
    have hf : (flagsA tRw).val = 18446744071562076160 + 3456 := uD_tR_off (by decide) (by omega)
    refine ⟨tcbR, uD_σR_tR, ?_, ?_⟩
    · rw [memR_at hm (by omega), wordR_zero_of (by omega)]; rfl
    · rw [memR_at hf (by omega), wordR_zero_of (by omega)]
      show Fl4Spec.wordToTcbFlags 0 = ∅
      ext f; simp [Fl4Spec.wordToTcbFlags]

theorem ZR_buf : Endp.BufWordRel ZR.T (bsL.mem sR) (σR (Z := Unit)) := by
  intro t ht
  rcases ZR_T.1 ht with rfl | rfl
  · have hb : (Endp.tIpcBufA tiB).val = 18446744071562072064 + 3512 := tiB_off (by decide) (by omega)
    refine ⟨idleTcbB, uD_σR_ti, ?_⟩
    rw [memR_at hb (by omega), wordR_zero_of (by omega)]; rfl
  · have hb : (Endp.tIpcBufA tRw).val = 18446744071562076160 + 3512 := uD_tR_off (by decide) (by omega)
    refine ⟨tcbR, uD_σR_tR, ?_⟩
    rw [memR_at hb (by omega), wordR_zero_of (by omega)]; rfl

/-! ## Frames and VSpace caps -/

theorem σR_bok : Endp.IpcBufCapOK (σR (Z := Unit)) := by
  intro t x h dev p R mt vms md hc
  rcases kheapR_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, hb⟩
  · cases e
    simp [tcbR] at hc
  · cases e
  · obtain ⟨-, rfl⟩ := kheapB_tcb hb
    cases hc

theorem ZR_fcov : FrameCover ZR.B (σR (Z := Unit)) := fun _ _ h => by
  rcases kheapR_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, hb⟩
  · cases e
  · cases e
  · exact (kheapB_noPage hb).elim

theorem ZR_fcap : Vs.FrSlots ZR.th (UFr (σR (Z := Unit))) (bsL.mem sR) := fun y hy => by
  rcases slotR_cases hy with rfl | rfl | ⟨hn, -⟩
  · rw [capV_R_root]; trivial
  · rw [capV_R_tmo]; trivial
  · rw [hn]; exact Vs.FrIn.null _

theorem ZR_vsc : Vs.VsSlotsW ZR.th ZR.P ZR.L4 ZR.L3 ZR.L2 ZR.L1 (bsL.mem sR) := fun y hy => by
  rcases slotR_cases hy with rfl | rfl | ⟨hn, -⟩
  · rw [capV_R_root]; trivial
  · rw [capV_R_tmo]; trivial
  · rw [hn]; trivial

end

end Fl4Proofs.P2.BootSt
