/-
# P2 (line p3mc, gen 35): the word-relation and frame `JAtZ` fields at the boot, and the spec start facts at `σB`

At `(sB, σB)` with the ghosts `ZB G` (`P2/BootZCheap`) and the empty call stacks `LstB = fun _ => []`:

* `call` (`CallRel`: the idle SC's `sc_replies = []`, its `REPLY` word 0; no reply), `rfree`, `rrecv` (no reply);
* `yld` (`YieldRel`: the idle TCB's `YIELD_TO` word 0 = `tcb_yield_to = None`, the idle SC yielded from by none),
  `mcp` (`McpRel`: `MCP` / `FLAGS` words 0 = MCP 0, no flag), `buf` (`BufWordRel`: `IPC_BUFFER` word 0 = 0);
* `bok` (`IpcBufCapOK`: the idle TCB's IPC frame cap is null), `fcov` (`FrameCover`: no data page), `fcap`
  (`FrSlots`) and `vsc` (`VsSlotsW`): every slot of `thB` null (`slot_null`);
* the spec facts of `JReachU3.start` / `JReachU17` beyond gen 34's: **`sInvIP_B`** (`SInvIP σB`: P3's `boot_ioi`
  ported, `boot_ioi_B`, and `SpecUtZ` vacuous), **`utPgR_B`** (`UtPgR σB`), **`devRangeS_B`** (`DevRangeS σB`): every
  cap of `σB` is null (`capOpt_B`).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootJpl
import Fl4Proofs.P3.SpecInvUtZW
import Fl4Proofs.P3.SpecInvDvW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Classical

noncomputable section

/-- The boot's call stacks: all empty. -/
def LstB : U64 → List U64 := fun _ => []

/-- A word of `sB` by its address as a number. -/
theorem memB_at {a : U64} {n : Nat} (hv : a.val = n) (h8 : n % 8 = 0) : bsL.mem sB a = wordB n := by
  rw [memB_mem (by show a.val % 8 = 0; rw [hv]; exact h8), hv]

/-- `wrapping_add` without wrap. -/
theorem wa_val {p k : U64} {n : Nat} (h : p.val + k.val = n) (hn : n < 2 ^ 64) :
    (core.num.U64.wrapping_add p k).val = n := by
  simp only [core.num.U64.wrapping_add_val_eq]; simp [U64.size, U64.numBits]; omega

theorem tiB_off {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add tiB k).val = 18446744071562072064 + n :=
  wa_val (by rw [tiB_val, hk]) (by omega)

theorem sciB_off {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add sciB k).val = 18446744071562096640 + n :=
  wa_val (by rw [sciB_val, hk]) (by omega)

theorem σB_kheap : (σB (Z := Unit)).kheap = kheapB := rfl

theorem mem_T {G : MdbGhost} {t : U64} (h : t ∈ (ZB G).T) : t = tiB := h
theorem mem_C {G : MdbGhost} {t : U64} (h : t ∈ (ZB G).C) : t = sciB := h

/-- The idle TCB in `σB`. -/
theorem σB_ti : (σB (Z := Unit)).kheap tiB.bv = some (.tcb idleTcbB) := by rw [tiB_bv]; exact kheapB_ti
/-- The idle SC in `σB`. -/
theorem σB_sci : (σB (Z := Unit)).kheap sciB.bv = some (.schedContext idleScB 0) := by
  rw [sciB_bv]; exact kheapB_sci

theorem optRef_zero : Notif.optRef 0#u64 = none := by unfold Notif.optRef; rw [if_pos rfl]

variable (G : MdbGhost)

/-! ## The call stacks and the replies (no reply) -/

theorem ZB_call : CallRel (bsL.mem sB) (ZB G).R (ZB G).C (σB (Z := Unit)) LstB where
  stack sc hsc := by
    rw [mem_C hsc]
    refine ⟨⟨idleScB, 0, σB_sci, rfl⟩, fun r h => (List.not_mem_nil h).elim, List.nodup_nil, ?_, ?_⟩
    · show bsL.mem sB (scReplyA sciB) = 0#u64
      have hv : (scReplyA sciB).val = 18446744071562096640 + 32 := sciB_off (by simp [layout.sc.REPLY]) (by omega)
      rw [memB_at hv (by omega)]; exact wordB_zero_of (by omega)
    · intro i h; exact absurd h (Nat.not_lt_zero _)
  excl _ _ _ _ r h := (List.not_mem_nil h).elim
  reply _ h := h.elim
  det _ h := h.elim

theorem ZB_rfree : RFree (bsL.mem sB) (ZB G).R (ZB G).C (σB (Z := Unit)) LstB := fun _ h => h.elim

theorem ZB_rrecv : RRecv (bsL.mem sB) (ZB G).R (σB (Z := Unit)) := fun _ h => h.elim

/-! ## The idle TCB's words -/

theorem yieldB0 : bsL.mem sB (yieldA tiB) = 0#u64 := by
  have hv : (yieldA tiB).val = 18446744071562072064 + 3472 := tiB_off (by decide) (by omega)
  rw [memB_at hv (by omega)]; exact wordB_zero_of (by omega)

theorem ZB_yld : YieldRel (ZB G).T (ZB G).C (bsL.mem sB) (σB (Z := Unit)) where
  tcb t ht := by rw [mem_T ht]; exact ⟨idleTcbB, σB_ti, by rw [yieldB0, optRef_zero]; rfl⟩
  toSc t ht h0 := by rw [mem_T ht] at h0; exact absurd yieldB0 h0
  frm sc hsc y n hy p hp := by
    rw [mem_C hsc, σB_sci] at hy
    cases hy
    rw [show idleScB.scYieldFrom = none from rfl] at hp; cases hp

theorem ZB_mcp : McpRel (ZB G).T (bsL.mem sB) (σB (Z := Unit)) := by
  intro t ht
  rw [mem_T ht]
  have hm : (mcpA tiB).val = 18446744071562072064 + 3440 := tiB_off (by decide) (by omega)
  have hf : (flagsA tiB).val = 18446744071562072064 + 3456 := tiB_off (by decide) (by omega)
  refine ⟨idleTcbB, σB_ti, ?_, ?_⟩
  · rw [memB_at hm (by omega), wordB_zero_of (by omega)]; rfl
  · rw [memB_at hf (by omega), wordB_zero_of (by omega)]
    show Fl4Spec.wordToTcbFlags 0 = ∅
    ext f; simp [Fl4Spec.wordToTcbFlags]

theorem ZB_buf : Endp.BufWordRel (ZB G).T (bsL.mem sB) (σB (Z := Unit)) := by
  intro t ht
  rw [mem_T ht]
  have hb : (Endp.tIpcBufA tiB).val = 18446744071562072064 + 3512 := tiB_off (by decide) (by omega)
  refine ⟨idleTcbB, σB_ti, ?_⟩
  rw [memB_at hb (by omega), wordB_zero_of (by omega)]; rfl

/-! ## Frames and VSpace caps (none) -/

theorem kheapB_pml4 : kheapB Fl4Spec.initGlobalPml4 = some (.archObj (.pageMapL4 Fl4Spec.globalPml4)) := by
  unfold kheapB
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), Function.update_self]

theorem kheapB_pdpt : kheapB Fl4Spec.initGlobalPdpt = some (.archObj (.pdPointerTable Fl4Spec.globalPdpt)) := by
  unfold kheapB
  rw [Function.update_of_ne (by decide), Function.update_self]

theorem kheapB_pd : kheapB Fl4Spec.initGlobalPd = some (.archObj (.pageDirectory Fl4Spec.globalPd)) := by
  unfold kheapB
  rw [Function.update_self]

/-- `σB` has no data page. -/
theorem kheapB_noPage {o : Fl4Spec.ObjRef} {d : Bool} {vms : Fl4Spec.VMPageSize}
    (h : kheapB o = some (.archObj (.dataPage d vms))) : False := by
  rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨e, -⟩ | ⟨-, e⟩
  · cases e
  · cases e
  · rcases e with rfl | rfl | rfl
    · rw [kheapB_pml4] at h; cases h
    · rw [kheapB_pdpt] at h; cases h
    · rw [kheapB_pd] at h; cases h
  · cases e

theorem σB_bok : Endp.IpcBufCapOK (σB (Z := Unit)) := by
  intro t x h dev p R mt vms md hc
  obtain ⟨-, rfl⟩ := kheapB_tcb h
  cases hc

theorem ZB_fcov : FrameCover (ZB G).B (σB (Z := Unit)) := fun _ _ h => (kheapB_noPage h).elim

theorem ZB_fcap : Vs.FrSlots (ZB G).th (UFr (σB (Z := Unit))) (bsL.mem sB) := fun y hy => by
  rw [slot_null hy]; exact Vs.FrIn.null _

theorem ZB_vsc : Vs.VsSlotsW (ZB G).th (ZB G).P (ZB G).L4 (ZB G).L3 (ZB G).L2 (ZB G).L1 (bsL.mem sB) :=
  fun y hy => by rw [slot_null hy]; trivial

/-! ## The spec start facts -/

/-- Every cap `capOpt` reads in `σB` is null. -/
theorem capOpt_B {p : Fl4Spec.ObjRef} {c : Fl4Spec.CnodeIndex} {cap : Fl4Spec.Cap}
    (h : capOpt ((σB (Z := Unit)).kheap p) c = some cap) : cap = .nullCap := by
  rw [← SInvDV.dv_capAt_capOpt (σB (Z := Unit)) (p, c)] at h
  exact SInvU.init_capAt_B h

theorem sInvIP_B : SInvR.G5.SInvIP (σB (Z := Unit)) :=
  ⟨SInvIo.boot_ioi_B.1, SInvIo.boot_ioi_B.2, fun _ _ _ _ h => by cases SInvU.init_capAt_B h⟩

theorem utPgR_B : SInvUZ.UtPgR (σB (Z := Unit)) := fun _ _ _ _ _ h => by cases capOpt_B h

theorem devRangeS_B : SInvDV.DevRangeS (σB (Z := Unit)) := fun _ _ _ _ _ h => by cases capOpt_B h

end

end Fl4Proofs.P2.BootSt
