/-
# P2 (line p3mc, gen 39, unit E): `XTopAt.fin`, `ipc`, `esa` and `XTopAt` at the second boot start

At `(sR, σR)` with the ghosts `ZR` (P2/BootRSpec, P2/BootRMem, P2/BootRZ: `T = {tiB, tRw}`, `C = {sciB, scRw}`),
any arch state `a` with `AR a σR.archState.x64CurrentCr3`, gen 35's P2/BootFinF ported:

* the TCB words: the idle TCB (`STATE = 7`, `SC = sciB`) against `idleTcbB`, the root TCB (`STATE = 1` =
  running, `SC = scRw`, slot 0 the thread cap, slot 4 the root SC cap) against `tcbR`; every other word read 0 (no fault, no bound
  notification, registers 0 = `emptyContext`, priority / domain / affinity 0): `uE_tcbRelE_i` / `uE_tcbRelE_r`
  (`TcbRelE`), `uE_tcbRel1_i` / `uE_tcbRel1_r` (`TcbRel1`);
* the SCs: `uE_scRel1` (one proof for both SCs: the idle SC's words, `TCB` the SC's thread), `uE_scRel1_i`
  (`sciB` against `idleScB`), `uE_scRel1_r` (`scRw` against `scR`);
* `uE_schedCore`, `uE_schedSpec`, `uE_schedRel` (`SchedRel` at core 0: `CUR_THREAD = tRw`, `CUR_SC = scRw`,
  `IDLE_THREAD = tiB`, `IDLE_SC = sciB`, empty queues, the two SCs disjoint and outside the TCBs / node / block);
* `uE_epStateRel`, `uE_ntfnStateRel`, `uE_irqRel`, `uE_ioRel`, `uE_kRootRel`, `uE_topPlaced` (with `uE_placed`:
  `Placed thR`), `uE_vsRel`, `uE_ptRel`, `uE_poolsIn`, `uE_curOK` (the current thread `tRw`: its vtable slot
  holds the null cap; slot 4 the root SC's cap), `uE_ipcRel`, `uE_esa`;
* **`xtop_R_of`**: `XTopAt AR ZR sR a σR` from its `rel` component (`hrel`, exactly `XTopAt.rel`'s type at this
  instance; proved by another unit).

No premise (`hAR` and `hrel` are hypotheses of `xtop_R_of` only). No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
import Fl4Proofs.P2.BootFinF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp
open Fl4Proofs.P3.Ipc Classical

noncomputable section

/-! ## Addresses and spec objects -/

theorem uE_tRoff {k : U64} {n : Nat} (hk : k.val = n) (hn : n < 4096) :
    (core.num.U64.wrapping_add tRw k).val = 18446744071562076160 + n :=
  wa_val (by rw [tRw_val, hk]) (by omega)

theorem uE_off {p K : U64} {b k : Nat} (hv : p.val = b) (hK : K.val = k) (hn : b + k < 2 ^ 64) :
    (core.num.U64.wrapping_add p K).val = b + k :=
  wa_val (by rw [hv, hK]) hn

theorem uE_tiBT : tiB ∈ ZR.T := ZR_T.2 (Or.inl rfl)
theorem uE_tRwT : tRw ∈ ZR.T := ZR_T.2 (Or.inr rfl)

theorem uE_tRw_ne0 : tRw ≠ 0#u64 := fun e => by
  have := congrArg UScalar.val e; rw [tRw_val] at this; exact absurd this (by decide)
theorem uE_scRw_ne0 : scRw ≠ 0#u64 := fun e => by
  have := congrArg UScalar.val e; rw [scRw_val] at this; exact absurd this (by decide)

theorem uE_kti : (σR (Z := Unit)).kheap tiB.bv = some (.tcb idleTcbB) := by
  show kheapR tiB.bv = _
  rw [tiB_bv, kheapR_of_ne (by decide) (by decide)]; exact kheapB_ti

theorem uE_ksci : (σR (Z := Unit)).kheap sciB.bv = some (.schedContext idleScB 0) := by
  show kheapR sciB.bv = _
  rw [sciB_bv, kheapR_of_ne (by decide) (by decide)]; exact kheapB_sci

theorem uE_ktR : (σR (Z := Unit)).kheap tRw.bv = some (.tcb tcbR) := kheapR_tR
theorem uE_kscR : (σR (Z := Unit)).kheap scRw.bv = some (.schedContext scR 0) := kheapR_scR

/-- The SCs of `ZR.C` in `σR`: size 0, at the idle SC's or the root SC's address. -/
theorem uE_scK {sc : U64} (hsc : sc ∈ ZR.C) {x : Fl4Spec.SchedContext} {n : Nat}
    (hk : (σR (Z := Unit)).kheap sc.bv = some (.schedContext x n)) :
    n = 0 ∧ (sc.val = 18446744071562096640 ∨ sc.val = 18446744071562080256) := by
  rcases ZR_C.1 hsc with rfl | rfl
  · rw [uE_ksci] at hk; cases hk; exact ⟨rfl, Or.inl sciB_val⟩
  · rw [uE_kscR] at hk; cases hk; exact ⟨rfl, Or.inr scRw_val⟩

/-! ## Words of `sR` -/

/-- A word of a TCB of `ZR.T` past the slots (offset ≥ 200) other than `STATE` / `SC`: 0. -/
theorem uE_tw0 {t : U64} (ht : t ∈ ZR.T) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 4096) (h8 : k % 8 = 0)
    (h0 : 200 ≤ k) (h1 : k ≠ 3328) (h2 : k ≠ 3464) :
    bsL.mem sR (core.num.U64.wrapping_add t K) = 0#u64 := by
  rcases ZR_T.1 ht with rfl | rfl
  · rw [memR_at (tiB_off hK hk) (by omega)]; exact wordR_zero_of (by omega)
  · rw [memR_at (uE_tRoff hK hk) (by omega)]; exact wordR_zero_of (by omega)

theorem uE_regw {t : U64} (ht : t ∈ ZR.T) (i : U64) (hi : i.val < 24) : bsL.mem sR (Endp.regA t i) = 0#u64 := by
  rcases ZR_T.1 ht with rfl | rfl
  · rw [memR_at (Endp.regA_val tiB_addr hi) (by rw [tiB_val]; omega), tiB_val]; exact wordR_zero_of (by omega)
  · rw [memR_at (Endp.regA_val tRw_addr hi) (by rw [tRw_val]; omega), tRw_val]; exact wordR_zero_of (by omega)

theorem uE_st_i : bsL.mem sR (tStA tiB) = 7#u64 := by
  rw [memR_at (a := tStA tiB) (tiB_off (n := 3328) (by simp [layout.tcb.STATE, layout.tcb.F]) (by omega)) (by omega),
    wordR_of (by omega)]
  simp [wordB]

theorem uE_st_r : bsL.mem sR (tStA tRw) = 1#u64 := by
  rw [memR_at (a := tStA tRw) (uE_tRoff (n := 3328) (by simp [layout.tcb.STATE, layout.tcb.F]) (by omega))
    (by omega)]
  unfold wordR
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem uE_sc_i : bsL.mem sR (scA tiB) = sciB := by
  rw [memR_at (a := scA tiB) (tiB_off (n := 3464) (by decide) (by omega)) (by omega), wordR_of (by omega)]
  simp [wordB]

theorem uE_sc_r : bsL.mem sR (scA tRw) = scRw := by
  rw [memR_at (a := scA tRw) (uE_tRoff (n := 3464) (by decide) (by omega)) (by omega)]
  unfold wordR
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos rfl]

/-- A node-0 word of `sR` by offset. -/
theorem uE_nw {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 4288) (h8 : k % 8 = 0) :
    bsL.mem sR (bsL.nodeAt sR 0#u64 o) = wordR (18446744071562114304 + k) :=
  memR_at (by rw [sR_nodeAt_val (by omega), ho]) (by omega)

/-- A node-0 word other than the four thread / SC words: 0. -/
theorem uE_nw0 {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 4288) (h8 : k % 8 = 0) (h1 : k ≠ 0) (h2 : k ≠ 8)
    (h3 : k ≠ 24) (h4 : k ≠ 32) : bsL.mem sR (bsL.nodeAt sR 0#u64 o) = 0#u64 := by
  rw [uE_nw ho hk h8]; exact wordR_zero_of (by omega)

theorem uE_nCur : bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CUR_THREAD) = tRw := by
  rw [uE_nw curth0 (by omega) (by omega)]; simp [wordR]

theorem uE_nIdle : bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.IDLE_THREAD) = tiB := by
  rw [uE_nw (k := 8) (by simp [layout.node.IDLE_THREAD]) (by omega) (by omega), wordR_of (by omega)]
  simp [wordB]

theorem uE_nCurSc : bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CUR_SC) = scRw := by
  rw [uE_nw (k := 24) (by simp [layout.node.CUR_SC]) (by omega) (by omega)]; simp [wordR]

theorem uE_nIdleSc : bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.IDLE_SC) = sciB := by
  rw [uE_nw (k := 32) (by simp [layout.node.IDLE_SC]) (by omega) (by omega), wordR_of (by omega)]
  simp [wordB]

/-- A block word of `sR` by offset. -/
theorem uE_ks {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 13568) (h8 : k % 8 = 0) :
    bsL.mem sR (core.num.U64.wrapping_add kbB o) = wordR (18446744071562100736 + k) :=
  memR_at (a := core.num.U64.wrapping_add kbB o) (ksWB_val ho hk) (by omega)

/-- A block word other than `DOMAIN_TIME`, entry 0's duration, `FEATURES`, `KERNEL_ROOT`: 0. -/
theorem uE_kw0 {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 13568) (h8 : k % 8 = 0) (h1 : k ≠ 16) (h2 : k ≠ 200)
    (h3 : k ≠ 72) (h4 : k ≠ 48) : bsL.mem sR (core.num.U64.wrapping_add kbB o) = 0#u64 := by
  rw [uE_ks ho hk h8]; exact wordR_zero_of (by omega)

/-- An SC word by offset. -/
theorem uE_swd {sc K : U64} {b k : Nat} (hv : sc.val = b) (hK : K.val = k) (hbk : b + k < 2 ^ 64)
    (h8 : (b + k) % 8 = 0) : bsL.mem sR (core.num.U64.wrapping_add sc K) = wordR (b + k) :=
  memR_at (uE_off hv hK hbk) h8

/-! ## The write footprints -/

theorem uE_nwT {t a : U64} {b : Nat} (ha : TcbAddr t) (hv : t.val = b) (hb : b + 4096 < 2 ^ 64)
    (h : a = tStA t ∨ a = tBlockA t ∨ a = badgeRegA t ∨ a = P1.nextA .Ep t ∨ a = P1.prevA .Ep t) :
    b ≤ a.val ∧ a.val < b + 4096 := by
  have hbg := badge_val
  rcases h with rfl | rfl | rfl | rfl | rfl
  · have : (tStA t).val = b + 3328 := uE_off hv (by simp [layout.tcb.STATE, layout.tcb.F]) (by omega)
    omega
  · have : (tBlockA t).val = b + 3336 := uE_off hv (by decide) (by omega)
    omega
  · have : (badgeRegA t).val = t.val + 256 + 8 * layout.reg.BADGE.val := Endp.regA_val ha (by omega)
    omega
  · have : (P1.nextA .Ep t).val = b + 3496 := uE_off hv (by decide) (by omega)
    omega
  · have : (P1.prevA .Ep t).val = b + 3504 := uE_off hv (by decide) (by omega)
    omega

/-- The words the notification code writes lie in the two TCBs. -/
theorem uE_nwrite {a : U64} (h : NWrite ∅ ZR.T a) :
    (18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562076160 ≤ a.val ∧ a.val < 18446744071562076160 + 4096) := by
  rcases h with ⟨n, hn, -⟩ | ⟨t, ht, h⟩
  · exact hn.elim
  · rcases ZR_T.1 ht with rfl | rfl
    · exact Or.inl (uE_nwT tiB_addr tiB_val (by norm_num) h)
    · exact Or.inr (uE_nwT tRw_addr tRw_val (by norm_num) h)

theorem uE_efoot {a : U64} (h : EFoot ZR.T ∅ ∅ ∅ a) :
    (18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562076160 ≤ a.val ∧ a.val < 18446744071562076160 + 4096) := by
  rcases h with ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, -⟩
  · exact he.elim
  · exact hr.elim
  · obtain ⟨h1, h2⟩ := h
    unfold TOffN at h2
    rcases ZR_T.1 ht with rfl | rfl
    · rw [tiB_val] at h1 h2; omega
    · rw [tRw_val] at h1 h2; omega
  · unfold TL at h
    rcases ZR_T.1 ht with rfl | rfl
    · rw [tiB_val] at h; omega
    · rw [tRw_val] at h; omega
  · exact hw.elim

theorem uE_ewrite {a : U64} (h : EWrite ZR.T ∅ ∅ ∅ a) :
    (18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562076160 ≤ a.val ∧ a.val < 18446744071562076160 + 4096) := uE_efoot h.foot

/-! ## The TCBs -/

theorem uE_tcbRelE_i : TcbRelE ∅ (bsL.mem sR) tiB idleTcbB where
  st := by rw [uE_st_i]; rfl
  blk e h := by simp [idleTcbB, Fl4Spec.epBlocked] at h
  send e d h := by simp [idleTcbB] at h
  recv e r d h := by simp [idleTcbB] at h
  reply r h := by simp [idleTcbB] at h
  regs r := by rw [uE_regw uE_tiBT _ (regIdx_lt r)]; rfl
  prio := by
    show (bsL.mem sR (core.num.U64.wrapping_add tiB 3448#u64)).val = _
    rw [uE_tw0 uE_tiBT (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
  fault0 := ⟨fun _ => rfl, fun _ => uE_tw0 uE_tiBT (k := 3376) (by decide) (by omega) (by omega) (by omega)
    (by omega) (by omega)⟩
  faultT := by
    have h0 : bsL.mem sR (tFaultA tiB) = 0#u64 :=
      uE_tw0 uE_tiBT (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨b, hb⟩; simp [idleTcbB] at hb
  bound := by
    show none = optRef (bsL.mem sR (core.num.U64.wrapping_add tiB 3368#u64))
    rw [uE_tw0 uE_tiBT (k := 3368) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega), optRef_zero]
  faultR := by
    show bsL.mem sR (core.num.U64.wrapping_add tiB 3376#u64) = 0#u64
    exact uE_tw0 uE_tiBT (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem uE_tcbRelE_r : TcbRelE ∅ (bsL.mem sR) tRw tcbR where
  st := by rw [uE_st_r]; rfl
  blk e h := by simp [tcbR, Fl4Spec.epBlocked] at h
  send e d h := by simp [tcbR] at h
  recv e r d h := by simp [tcbR] at h
  reply r h := by simp [tcbR] at h
  regs r := by rw [uE_regw uE_tRwT _ (regIdx_lt r)]; rfl
  prio := by
    show (bsL.mem sR (core.num.U64.wrapping_add tRw 3448#u64)).val = _
    rw [uE_tw0 uE_tRwT (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
  fault0 := ⟨fun _ => rfl, fun _ => uE_tw0 uE_tRwT (k := 3376) (by decide) (by omega) (by omega) (by omega)
    (by omega) (by omega)⟩
  faultT := by
    have h0 : bsL.mem sR (tFaultA tRw) = 0#u64 :=
      uE_tw0 uE_tRwT (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨b, hb⟩; simp [tcbR] at hb
  bound := by
    show none = optRef (bsL.mem sR (core.num.U64.wrapping_add tRw 3368#u64))
    rw [uE_tw0 uE_tRwT (k := 3368) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega), optRef_zero]
  faultR := by
    show bsL.mem sR (core.num.U64.wrapping_add tRw 3376#u64) = 0#u64
    exact uE_tw0 uE_tRwT (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem uE_tcbRel1_i : TcbRel1 (bsL.mem sR) tiB idleTcbB where
  st := by rw [uE_st_i]; rfl
  blk n h := by simp [idleTcbB] at h
  badge := by
    show (bsL.mem sR (Endp.regA tiB layout.reg.BADGE)).bv = _
    rw [uE_regw uE_tiBT _ (by rw [badge_val]; omega)]; rfl
  prio := by
    show (bsL.mem sR (core.num.U64.wrapping_add tiB 3448#u64)).val = _
    rw [uE_tw0 uE_tiBT (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl

theorem uE_tcbRel1_r : TcbRel1 (bsL.mem sR) tRw tcbR where
  st := by rw [uE_st_r]; rfl
  blk n h := by simp [tcbR] at h
  badge := by
    show (bsL.mem sR (Endp.regA tRw layout.reg.BADGE)).bv = _
    rw [uE_regw uE_tRwT _ (by rw [badge_val]; omega)]; rfl
  prio := by
    show (bsL.mem sR (core.num.U64.wrapping_add tRw 3448#u64)).val = _
    rw [uE_tw0 uE_tRwT (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl

/-! ## The SCs -/

/-- **An SC with the idle SC's words** (`TCB` its thread) against the idle SC's record or the root SC's. -/
theorem uE_scRel1 {sc : U64} {x : Fl4Spec.SchedContext} {b : Nat} (hv : sc.val = b) (hb : b % 4096 = 0)
    (hbb : b + 4096 < 2 ^ 64) (hx : x = idleScB ∨ x = scR)
    (w0 : ∀ k, k < 128 → k % 8 = 0 → k ≠ 24 → k ≠ 72 → k ≠ 88 → k ≠ 104 → k ≠ 112 → wordR (b + k) = 0#u64)
    (w72 : wordR (b + 72) = 2#u64) (w88 : wordR (b + 88) = 1#u64) (w104 : wordR (b + 104) = maxPB)
    (w112 : wordR (b + 112) = maxPB) (htcb : x.scTcb = optRef (wordR (b + 24))) :
    ScRel1 bst sR sc x 0 := by
  have rmax : bsL.rmax sR sc = 2#u64 := by
    unfold LawfulStore.rmax maxA
    rw [uE_swd hv (k := 72) (by simp [layout.sc.REFILL_MAX]) (by omega) (by omega), w72]
  have rhead : bsL.rhead sR sc = 0#u64 := by
    unfold LawfulStore.rhead headA
    rw [uE_swd hv (k := 80) (by simp [layout.sc.REFILL_HEAD]) (by omega) (by omega)]
    exact w0 80 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have rtail : bsL.rtail sR sc = 1#u64 := by
    unfold LawfulStore.rtail tailA
    rw [uE_swd hv (k := 88) (by simp [layout.sc.REFILL_TAIL]) (by omega) (by omega), w88]
  have wf : RefillsWF bst sR sc (0 + Fl4Spec.minSchedContextBits) :=
    { placed := ⟨by simp [Fl4Spec.minSchedContextBits],
        by rw [hv]; simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow]; omega,
        by rw [hv]; simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow]; omega⟩
      min_le := by rw [rmax]; simp [sporadic.MIN_REFILLS]
      le_abs := by rw [rmax]; simp [absMax, Fl4Spec.minSchedContextBits]
      head_lt := by rw [rhead, rmax]; decide
      tail_lt := by rw [rtail, rmax]; decide }
  have hd : decide ((0#u64 : U64) ≠ 0#u64) = false := by simp
  refine ⟨wf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show _ = (bsL.mem sR (core.num.U64.wrapping_add sc layout.sc.PERIOD)).bv
    rw [uE_swd hv (k := 0) (by simp [layout.sc.PERIOD]) (by omega) (by omega),
      w0 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rcases hx with rfl | rfl <;> rfl
  · show _ = (bsL.mem sR (core.num.U64.wrapping_add sc 8#u64)).bv
    rw [uE_swd hv (k := 8) (by decide) (by omega) (by omega),
      w0 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rcases hx with rfl | rfl <;> rfl
  · show _ = optRef (bsL.mem sR (core.num.U64.wrapping_add sc 24#u64))
    rw [uE_swd hv (k := 24) (by decide) (by omega) (by omega)]
    exact htcb
  · show _ = optRef (bsL.mem sR (core.num.U64.wrapping_add sc 40#u64))
    rw [uE_swd hv (k := 40) (by decide) (by omega) (by omega),
      w0 40 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), optRef_zero]
    rcases hx with rfl | rfl <;> rfl
  · show _ = (bsL.mem sR (core.num.U64.wrapping_add sc 48#u64)).bv
    rw [uE_swd hv (k := 48) (by decide) (by omega) (by omega),
      w0 48 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    rcases hx with rfl | rfl <;> rfl
  · show _ = optRef (bsL.mem sR (core.num.U64.wrapping_add sc 56#u64))
    rw [uE_swd hv (k := 56) (by decide) (by omega) (by omega),
      w0 56 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), optRef_zero]
    rcases hx with rfl | rfl <;> rfl
  · show _ = decide (bsL.mem sR (core.num.U64.wrapping_add sc 64#u64) ≠ 0#u64)
    rw [uE_swd hv (k := 64) (by decide) (by omega) (by omega),
      w0 64 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), hd]
    rcases hx with rfl | rfl <;> rfl
  · rw [rmax]; rcases hx with rfl | rfl <;> rfl
  · obtain ⟨-, -, -, -, -, hin⟩ := wf.inside
    have hix : ∀ k, k < 2 → (bsL.ix sR sc k).val = k := by
      intro k hk
      rw [wf.ix_val, rhead, rmax]
      show (0 + k) % 2 = k
      omega
    have r0 := hin (bsL.ix sR sc 0) (by rw [hix 0 (by omega), rmax]; decide)
    have r1 := hin (bsL.ix sR sc 1) (by rw [hix 1 (by omega), rmax]; decide)
    rw [hix 0 (by omega), hv] at r0
    rw [hix 1 (by omega), hv] at r1
    have hsz : bsL.size sR sc = 2 := by
      unfold LawfulStore.size; rw [rmax, rhead, rtail]; rfl
    simp only [LawfulStore.refills, hsz, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
      LawfulStore.rf, LawfulStore.refill]
    rw [memR_at r0.1 (by omega), memR_at r0.2.1 (by omega), memR_at r1.1 (by omega), memR_at r1.2.1 (by omega)]
    have e1 : wordR (b + 96 + 16 * 0) = 0#u64 := by
      rw [show b + 96 + 16 * 0 = b + 96 by omega]
      exact w0 96 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have e2 : wordR (b + 104 + 16 * 0) = maxPB := by rw [show b + 104 + 16 * 0 = b + 104 by omega]; exact w104
    have e3 : wordR (b + 96 + 16 * 1) = maxPB := by rw [show b + 96 + 16 * 1 = b + 112 by omega]; exact w112
    have e4 : wordR (b + 104 + 16 * 1) = 0#u64 := by
      rw [show b + 104 + 16 * 1 = b + 120 by omega]
      exact w0 120 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [e1, e2, e3, e4]
    rcases hx with rfl | rfl <;> rfl

theorem uE_scRel1_i : ScRel1 bst sR sciB idleScB 0 :=
  uE_scRel1 sciB_val (by norm_num) (by norm_num) (Or.inl rfl)
    (fun k h1 h2 h3 h4 h5 h6 h7 => wordR_zero_of (by omega))
    (by rw [wordR_of (by omega)]; simp [wordB]) (by rw [wordR_of (by omega)]; simp [wordB])
    (by rw [wordR_of (by omega)]; simp [wordB]) (by rw [wordR_of (by omega)]; simp [wordB])
    (by
      rw [wordR_of (by omega)]
      have : wordB (18446744071562096640 + 24) = tiB := by simp [wordB]
      rw [this]
      unfold optRef
      rw [if_neg tiB_ne0', tiB_bv]; rfl)

theorem uE_scRel1_r : ScRel1 bst sR scRw scR 0 :=
  uE_scRel1 scRw_val (by norm_num) (by norm_num) (Or.inr rfl)
    (fun k h1 h2 h3 h4 h5 h6 h7 => wordR_zero_of (by omega))
    (by simp [wordR]) (by simp [wordR]) (by simp [wordR]) (by simp [wordR])
    (by
      have : wordR (18446744071562080256 + 24) = tRw := by simp [wordR]
      rw [this]
      unfold optRef
      rw [if_neg uE_tRw_ne0, tRw_bv]; rfl)

/-- An SC word of `ZR.C` other than the configured ones: 0. -/
theorem uE_scw0 {sc : U64} (hsc : sc ∈ ZR.C) {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 128) (h8 : k % 8 = 0)
    (h1 : k ≠ 24) (h2 : k ≠ 72) (h3 : k ≠ 88) (h4 : k ≠ 104) (h5 : k ≠ 112) :
    bsL.mem sR (core.num.U64.wrapping_add sc K) = 0#u64 := by
  rcases ZR_C.1 hsc with rfl | rfl
  · rw [uE_swd sciB_val hK (by omega) (by omega)]; exact wordR_zero_of (by omega)
  · rw [uE_swd scRw_val hK (by omega) (by omega)]; exact wordR_zero_of (by omega)

/-! ## The scheduler -/

theorem uE_schedCore : SchedCore bst ZR.T 0#u64 sR (fun _ => []) [] where
  tcbs := tcbPlaced_R
  node := ⟨by rw [sR_nodeBase _ rfl], by rw [sR_nodeBase _ rfl]; norm_num, fun t ht => by
    rw [sR_nodeBase _ rfl]
    rcases ZR_T.1 ht with rfl | rfl
    · rw [tiB_val]; omega
    · rw [tRw_val]; omega⟩
  cur := sR_cpu
  aff t ht := uE_tw0 ht (k := 3520) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
  prio t ht := by
    show (bsL.mem sR (core.num.U64.wrapping_add t 3448#u64)).val < 256
    rw [uE_tw0 ht (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; decide
  ready := by
    refine ⟨⟨fun p hp => ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim, ?_, ?_, trivial⟩,
      fun _ _ _ _ _ x h => (List.not_mem_nil h).elim⟩, ⟨fun p hp => ?_, fun i hi => ?_⟩⟩
    · show bsL.mem sR (bsL.nodeAt sR 0#u64 (rqOff p)) = 0#u64
      exact uE_nw0 (rqOff_val hp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · show bsL.mem sR (bsL.nodeAt sR 0#u64 (rqTailOff p)) = 0#u64
      exact uE_nw0 (rqTailOff_val hp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · show (bsL.mem sR (bsL.nodeAt sR 0#u64 (l2Off (p.val / 64)))).bv.getLsbD (p.val % 64) = true ↔ _
      rw [uE_nw0 (l2Off_val (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp
    · show (bsL.mem sR (bsL.nodeAt sR 0#u64 l1Off)).bv.getLsbD i = true ↔ _
      rw [uE_nw0 l1Off_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [LawfulStore.l2W]
      constructor
      · intro h; simp at h
      · rintro ⟨hi4, hne⟩
        exact absurd (uE_nw0 (l2Off_val hi4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hne
  release := by
    refine ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim, ?_, ?_, trivial⟩
    · show bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.RELEASE_HEAD) = 0#u64
      exact uE_nw0 (k := 64) (by simp [layout.node.RELEASE_HEAD]) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    · show bsL.mem sR (bsL.nodeAt sR 0#u64 (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)) = 0#u64
      exact uE_nw0 (k := 72)
        (by simp [layout.node.RELEASE_HEAD, core.num.U64.wrapping_add_val_eq, U64.size, U64.numBits]) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  inQ _ _ _ h := (List.not_mem_nil h).elim
  queued t ht := by
    have h0 : bsL.mem sR (inqA t) = 0#u64 :=
      uE_tw0 ht (k := 3592) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    simp
  released t ht := by
    have h0 : bsL.mem sR (inqA t) = 0#u64 :=
      uE_tw0 ht (k := 3592) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    simp
  excl _ _ h := (List.not_mem_nil h).elim
  curT := by
    show bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CUR_THREAD) ∈ ZR.T
    rw [uE_nCur]; exact uE_tRwT
  idleT := by
    show bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.IDLE_THREAD) ∈ ZR.T
    rw [uE_nIdle]; exact uE_tiBT
  ksOut t ht := by
    rw [sR_ksb, kbB_val]
    rcases ZR_T.1 ht with rfl | rfl
    · rw [tiB_val]; omega
    · rw [tRw_val]; omega

theorem uE_schedSpec : SchedSpec bst ZR.T ZR.C 0#u64 sR (fun _ => []) [] (σR (Z := Unit)) where
  rq _ _ := rfl
  rqDom _ _ _ := rfl
  rel := rfl
  curThread := by
    show _ = (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CUR_THREAD)).bv
    rw [uE_nCur, tRw_bv]; rfl
  curSc := by
    show _ = (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CUR_SC)).bv
    rw [uE_nCurSc, scRw_bv]; rfl
  curTime := by
    show _ = (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CUR_TIME)).bv
    rw [uE_nw0 (k := 48) (by simp [layout.node.CUR_TIME]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; rfl
  consumed := by
    show _ = (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.CONSUMED)).bv
    rw [uE_nw0 (k := 40) (by simp [layout.node.CONSUMED]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; rfl
  curDom := ⟨rfl, by
    show bsL.mem sR (core.num.U64.wrapping_add (bsL.ksb sR) 8#u64) = 0#u64
    rw [sR_ksb]; exact uE_kw0 (k := 8) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  tcb t ht := by
    rcases ZR_T.1 ht with rfl | rfl
    · refine ⟨idleTcbB, uE_kti, rfl,
        uE_tw0 uE_tiBT (k := 3432) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega), ?_, ?_⟩
      · rw [uE_sc_i]; unfold optRef; rw [if_neg sciB_ne0, sciB_bv]; rfl
      · show (bsL.mem sR (core.num.U64.wrapping_add tiB 3448#u64)).val = _
        rw [uE_tw0 uE_tiBT (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
    · refine ⟨tcbR, uE_ktR, rfl,
        uE_tw0 uE_tRwT (k := 3432) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega), ?_, ?_⟩
      · rw [uE_sc_r]; unfold optRef; rw [if_neg uE_scRw_ne0, scRw_bv]; rfl
      · show (bsL.mem sR (core.num.U64.wrapping_add tRw 3448#u64)).val = _
        rw [uE_tw0 uE_tRwT (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
  scMem t ht _ := by
    rcases ZR_T.1 ht with rfl | rfl
    · rw [uE_sc_i]; exact ZR_C.2 (Or.inl rfl)
    · rw [uE_sc_r]; exact ZR_C.2 (Or.inr rfl)
  scs sc hsc := by
    rcases ZR_C.1 hsc with rfl | rfl
    · exact ⟨idleScB, 0, uE_ksci, uE_scRel1_i.toW⟩
    · exact ⟨scR, 0, uE_kscR, uE_scRel1_r.toW⟩
  idleSc := by
    show (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.IDLE_SC)).bv = _
    rw [uE_nIdleSc, sciB_bv]; rfl
  domTime := by
    show _ = (bsL.mem sR (core.num.U64.wrapping_add (bsL.ksb sR) 16#u64)).bv
    rw [sR_ksb, uE_ks (o := 16#u64) (k := 16) (by decide) (by omega) (by omega), wordR_of (by omega)]
    simp [wordB]; rfl
  idleTh := by
    show _ = (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.IDLE_THREAD)).bv
    rw [uE_nIdle, tiB_bv]; rfl

theorem uE_schedRel : SchedRel bst ZR.N ZR.T ZR.C 0#u64 sR (σR (Z := Unit)) where
  placed := ⟨tcbPlaced_R, fun _ h => h.elim, fun _ h => h.elim⟩
  nodeNW o ho h := by
    have := uE_nwrite h
    rw [sR_nodeAt_val ho] at this; omega
  domNW h := by
    have := uE_nwrite h
    have hv : (curDomA bst sR).val = 18446744071562100736 + 8 := ksWB_val (o := 8#u64) (by decide) (by omega)
    omega
  dtNW h := by
    have := uE_nwrite h
    have hv : (dtA bst sR).val = 18446744071562100736 + 16 := ksWB_val (o := 16#u64) (by decide) (by omega)
    omega
  scOut sc hsc x n hk a ha := by
    obtain ⟨rfl, hv⟩ := uE_scK hsc hk
    obtain ⟨g1, g2⟩ := ha
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
    refine ⟨fun h => ?_, ?_, fun t ht => ?_, ?_⟩
    · have := uE_nwrite h; omega
    · rw [sR_nodeBase _ rfl]; omega
    · rcases ZR_T.1 ht with rfl | rfl
      · rw [tiB_val]; omega
      · rw [tRw_val]; omega
    · rw [sR_ksb, kbB_val]; omega
  scDisj sc hsc sc' hsc' hne x n x' n' hk hk' a ha hb := by
    obtain ⟨rfl, hv⟩ := uE_scK hsc hk
    obtain ⟨rfl, hv'⟩ := uE_scK hsc' hk'
    have hne' : sc.val ≠ sc'.val := fun e => hne (eq_of_val'' e)
    obtain ⟨g1, g2⟩ := ha
    obtain ⟨f1, f2⟩ := hb
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2 f2
    omega
  actW := Or.inl (uE_nw0 act_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  act := uE_nw0 act_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  repr := by
    show false = decide (bsL.mem sR (bsL.nodeAt sR 0#u64 layout.node.REPROGRAM) ≠ 0#u64)
    rw [uE_nw0 (k := 56) (by simp [layout.node.REPROGRAM]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; simp
  core sc hsc := uE_scw0 hsc (k := 16) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  lists := ⟨_, _, uE_schedCore, uE_schedSpec⟩

/-! ## The other relations -/

theorem uE_epStateRel : EpStateRel ZR.T ZR.E ZR.R ZR.B (bsL.mem sR) (σR (Z := Unit)) where
  ep _ h := h.elim
  reply _ h := h.elim
  tcb t ht := by
    rcases ZR_T.1 ht with rfl | rfl
    · exact ⟨idleTcbB, uE_kti, uE_tcbRelE_i⟩
    · exact ⟨tcbR, uE_ktR, uE_tcbRelE_r⟩
  buf _ h := h.elim

theorem uE_ntfnStateRel : NtfnStateRel ZR.N ZR.T (bsL.mem sR) (σR (Z := Unit)) where
  ntfn _ h := h.elim
  tcb t ht := by
    rcases ZR_T.1 ht with rfl | rfl
    · exact ⟨idleTcbB, uE_kti, uE_tcbRel1_i⟩
    · exact ⟨tcbR, uE_ktR, uE_tcbRel1_r⟩

theorem uE_irqRel : IrqRel (bsL.mem sR) (bsL.ksb sR) (σR (Z := Unit)) := by
  rw [sR_ksb]
  refine ⟨fun i hi => ?_, σB_irqRel_node⟩
  have hv := irqStA_val (kb := kbB) kbB_fit' hi
  rw [kbB_val] at hv
  rw [memR_at hv (by omega), wordR_zero_of (by omega)]
  exact ((irqSt_inactive _).2 rfl).symm

theorem uE_ioRel : IoRel (bsL.mem sR) (bsL.ksb sR) (σR (Z := Unit)) := by
  rw [sR_ksb]
  intro p hp
  have hw := wI_val hp
  have hv := ioA_val (kb := kbB) (w := wI p) kbB_fit' (by omega)
  rw [kbB_val, hw] at hv
  show false = _
  unfold bitOf
  rw [memR_at hv (by omega), wordR_zero_of (by omega)]
  simp

theorem uE_kRootRel : KRootRel (bsL.mem sR) (bsL.ksb sR) (σR (Z := Unit)) := by
  rw [sR_ksb]
  refine ⟨?_, ?_⟩
  · unfold KRootW
    rw [uE_ks (k := 48) (by simp [layout.ks.KERNEL_ROOT]) (by omega) (by omega), wordR_of (by omega)]
    simp only [wordB]
    simp
    rfl
  · unfold HugeRel
    rw [uE_ks (k := 72) (by simp [layout.ks.FEATURES]) (by omega) (by omega), wordR_of (by omega)]
    have hw : wordB (18446744071562100736 + 72) = 2#u64 := by simp [wordB]
    rw [hw]
    have h2 : (2#u64 &&& layout.ks.FEATURE_HUGE_PAGES) ≠ 0#u64 := by
      intro h; have := congrArg UScalar.val h; simp at this
    have h2' : ((2#u64 &&& layout.ks.FEATURE_HUGE_PAGES) != 0#u64) = true := bne_iff_ne.2 h2
    rw [h2']; rfl

/-! ## Placement and the VSpace relations -/

/-- **`thR` is placed.** -/
theorem uE_placed : P3.Placed thR where
  align p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega
  fits p k hp := by
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;> simp only [P3.objSize, Nat.pow_zero] <;>
      omega
  disj p q kp kq hp hq hne := by
    have hv := U64.ne_of_val hne
    rcases thR_cases hp with ⟨e, rfl⟩ | ⟨e, rfl⟩ | ⟨rfl, g1, g2, g3⟩ <;>
      rcases thR_cases hq with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨rfl, f1, f2, f3⟩ <;>
      simp only [P3.objSize, Nat.pow_zero] <;> omega
  high p k hp := by rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, g1, g2, g3⟩ <;> omega

/-- A slot of `thR`: its 32 bytes in a TCB's slot area or the IRQ node. -/
theorem uE_slot_range {y : U64} (hy : IsSlot thR y) :
    (18446744071562072064 ≤ y.val ∧ y.val + 32 ≤ 18446744071562072064 + 192) ∨
    (18446744071562076160 ≤ y.val ∧ y.val + 32 ≤ 18446744071562076160 + 192) ∨
    (18446744071562100736 + 1248 ≤ y.val ∧ y.val + 32 ≤ 18446744071562100736 + 5344) := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
  · rcases thR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
    · cases e
      simp only [Nat.pow_zero] at hir
      rw [slotOf_val (by omega)]
      right; right; constructor <;> omega
  · rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · simp only [tcbSlots] at hit
      rw [slotOf_val (by omega)]
      right; left; constructor <;> omega
    · simp only [tcbSlots] at hit
      rw [slotOf_val (by omega)]
      left; constructor <;> omega
    · cases e

theorem uE_slotW_range {b : U64} (h : SlotW thR b) : b.val < 18446744071562100736 + 5376 := by
  obtain ⟨x, hx, e | e⟩ := h
  · have := uE_slot_range hx
    rw [e]; omega
  · have := uE_slot_range hx
    rw [e, wa_val (k := 8#u64) (n := x.val + 8) (by rfl) (by omega)]; omega

theorem uE_vobj {a : U64} (h : VObj thR ∅ ∅ ∅ ∅ ∅ kbB a) :
    (18446744071562100736 + 1248 ≤ a.val ∧ a.val < 18446744071562100736 + 5344) ∨
    (18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 192) ∨
    (18446744071562076160 ≤ a.val ∧ a.val < 18446744071562076160 + 192) ∨
    (18446744071562100736 + 288000 ≤ a.val ∧ a.val < 18446744071562100736 + 288000 + 16384) := by
  rcases h with ⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, -⟩ | ⟨h1, h2⟩
  · rcases thR_cases hq with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e
    · cases e; simp only [Nat.pow_zero] at h2; left; omega
  · rcases thR_cases ht with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · right; right; left; omega
    · right; left; omega
    · cases e
  · rcases hq with h | h | h | h | h <;> exact h.elim
  · right; right; right; rw [kbB_val] at h1 h2; omega

theorem uE_oobj {a : U64} (h : OObj bst ZR.N ZR.T ZR.C ZR.E ZR.R ZR.B 0#u64 sR (σR (Z := Unit)) a) :
    (18446744071562114304 ≤ a.val ∧ a.val < 18446744071562114304 + 4288) ∨
    (18446744071562100736 ≤ a.val ∧ a.val < 18446744071562100736 + 13568 ∧
      (a.val < 18446744071562100736 + 1248 ∨ 18446744071562100736 + 5344 ≤ a.val)) ∨
    (18446744071562072064 + 256 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562076160 + 256 ≤ a.val ∧ a.val < 18446744071562076160 + 4096) ∨
    (18446744071562096640 ≤ a.val ∧ a.val < 18446744071562096640 + 128) ∨
    (18446744071562080256 ≤ a.val ∧ a.val < 18446744071562080256 + 128) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨t, ht, h1, h2⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ |
      ⟨sc, hsc, x, n, hk, h1, h2⟩ | ⟨wp, hw, -⟩
  · left; rw [sR_nodeBase _ rfl] at h1 h2; omega
  · right; left; rw [sR_ksb, kbB_val] at h1 h2 h3; omega
  · rcases ZR_T.1 ht with rfl | rfl
    · right; right; left; rw [tiB_val] at h1 h2; omega
    · right; right; right; left; rw [tRw_val] at h1 h2; omega
  · exact he.elim
  · exact hr.elim
  · exact hn.elim
  · obtain ⟨rfl, hv⟩ := uE_scK hsc hk
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at h2
    right; right; right; right; omega
  · exact hw.elim

theorem uE_topPlaced :
    TopPlaced bst ZR.th ZR.P ZR.L4 ZR.L3 ZR.L2 ZR.L1 ZR.N ZR.T ZR.C ZR.E ZR.R ZR.B ZR.c sR (σR (Z := Unit)) where
  ep := ⟨tcbPlaced_R, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
    fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
    fun _ h => h.elim⟩
  vs := ⟨by rw [sR_ksb]; exact kbB_al8, by rw [sR_ksb, kbB_val]; norm_num, fun _ h => h.elim, fun _ h => h.elim⟩
  pt p hp := by rcases hp with h | h | h | h <;> exact h.elim
  pl := uE_placed
  disj a ho hv := by
    rw [sR_ksb] at hv
    have h1 := uE_oobj ho
    have h2 := uE_vobj hv
    omega
  nodeE a h1 h2 h := by
    have := uE_efoot h
    rw [sR_nodeBase ZR.c rfl] at h1 h2; omega
  po b h := by obtain ⟨p, hp, -⟩ := h; rcases hp with h | h | h | h <;> exact h.elim
  ps b h := by obtain ⟨p, hp, -⟩ := h; rcases hp with h | h | h | h <;> exact h.elim
  pv b h := by obtain ⟨p, hp, -⟩ := h; rcases hp with h | h | h | h <;> exact h.elim
  vo b h := by
    rw [sR_ksb] at h
    obtain ⟨g1, g2, g3⟩ := vsWrite_range h
    refine ⟨g3, fun p k hp ⟨h1, h2⟩ => ?_⟩
    rcases thR_in hp h1 h2 with h | h | h <;> omega
  sd b h hs := by
    rw [sR_ksb] at h
    have := vsWrite_range h
    have := uE_slotW_range hs
    omega
  tko t ht := by
    rcases thR_cases ht with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
    · rw [sR_ksb, kbB_val, e]; omega
    · rw [sR_ksb, kbB_val, e]; omega
    · cases e

theorem uE_vsRel : VsRel ZR.P (bsL.mem sR) (bsL.ksb sR) (σR (Z := Unit)) := by
  rw [sR_ksb]
  have h0 : ∀ hi : U64, hi.val < 2048 → bsL.mem sR (atA kbB hi) = 0#u64 := by
    intro hi hh
    rw [memR_at (atA_val (by rw [kbB_val]; norm_num) hh) (by rw [kbB_val]; omega), kbB_val]
    exact wordR_zero_of (by omega)
  refine ⟨fun hi hh => ?_, fun hi hh hne => absurd (h0 hi hh) hne, fun _ h => h.elim⟩
  rw [h0 hi hh, optRef_zero]; rfl

theorem uE_ptRel : PtRel ZR.L4 ZR.L3 ZR.L2 ZR.L1 (bsL.mem sR) (σR (Z := Unit)) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem uE_poolsIn : PoolsIn ZR.P ZR.L4 (bsL.mem sR) := fun _ h => h.elim

/-- **The current thread** `tRw`: a TCB of `thR`, its vtable slot holds the null cap. -/
theorem uE_curOK : Vs.CurOK bst ZR.th sR (σR (Z := Unit)) :=
  ⟨tRw, tRw_bv, thR_tR, fun p asid h => by
    have hs : IsSlot thR (slotOf tRw 1) := ⟨tRw, 1, Or.inr ⟨thR_tR, by decide⟩, rfl⟩
    rcases slotR_cases hs with e | e | ⟨hn, -⟩
    · have := congrArg UScalar.val e
      rw [slotOf_val (by rw [tRw_val]; omega), tRw_val] at this; omega
    · have := congrArg UScalar.val e
      rw [slotOf_val (by rw [tRw_val]; omega), tRw_val, tmoW_val] at this; omega
    · rw [capAt_capV, hn] at h
      cases ok_inj_ff h⟩

/-! ## `ipc`, `esa` and `XTopAt` -/

theorem uE_ipcRel : IpcRel ZR.N ZR.T ZR.E ZR.R ZR.B (bsL.mem sR) (σR (Z := Unit)) :=
  IpcRel.of uE_ntfnStateRel uE_epStateRel (sched_sc (L := bsL) uE_schedRel)

theorem uE_esa : EpSchedApart bst ZR.T ZR.C ZR.E ZR.R ZR.B ZR.c sR (σR (Z := Unit)) where
  node a h1 h2 h := by
    have := uE_efoot h
    rw [sR_nodeBase ZR.c rfl] at h1 h2; omega
  dom h := by
    have := uE_ewrite h
    have hv : (curDomA bst sR).val = 18446744071562100736 + 8 := ksWB_val (o := 8#u64) (by decide) (by omega)
    omega
  dt h := by
    have := uE_ewrite h
    have hv : (dtA bst sR).val = 18446744071562100736 + 16 := ksWB_val (o := 16#u64) (by decide) (by omega)
    omega
  sc sc hsc x n hk a ha h := by
    obtain ⟨rfl, hv⟩ := uE_scK hsc hk
    obtain ⟨g1, g2⟩ := ha
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
    have := uE_ewrite h
    omega

/-- **`XTopAt` at the second boot start**, from its `rel` component. -/
theorem xtop_R_of {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {a : A}
    (hAR : AR a (σR (Z := Unit)).archState.x64CurrentCr3)
    (hrel : Ipc.RelTopB (L := bsL) ZR.th ZR.G ZR.N ZR.T ZR.C ZR.E ZR.R ZR.B ZR.c sR (σR (Z := Unit))) :
    XTopAt (L := bsL) AR ZR sR a (σR (Z := Unit)) :=
  ⟨⟨⟨⟨uE_schedRel, uE_epStateRel, uE_ntfnStateRel, uE_irqRel, uE_ioRel, uE_kRootRel, hAR⟩, uE_topPlaced⟩,
    uE_vsRel, uE_ptRel, uE_poolsIn, uE_curOK⟩, hrel, uE_ipcRel, uE_esa⟩

end

end Fl4Proofs.P2.BootSt
