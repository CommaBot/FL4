/-
# P2 (line p3mc, gen 35): `XTopAt.fin`, `ipc`, `esa` and all of `XTopAt` at the boot

At `(sB, σB)` with the ghosts `ZB G0`, any arch state `a` with `AR a σB.archState.x64CurrentCr3`:

* the idle TCB's words (`STATE = 7`, `SC = sciB`, every other word 0) against `idleTcbB`: **`tcbRelE_B`**
  (`TcbRelE`: idle state, no fault, no bound notification, registers 0 = `emptyContext`), **`tcbRel1_B`**;
* **`schedRel_B`** (`SchedRel`: empty ready / release queues and bitmaps; node 0's `CUR_THREAD` / `IDLE_THREAD` the
  idle TCB, `CUR_SC` / `IDLE_SC` the idle SC, action 0 = resume, `REPROGRAM` / `CUR_TIME` / `CONSUMED` 0,
  `DOMAIN_TIME` 15; the idle SC against `idleScB`, **`scRelW_B`**: period, consumed, badge 0, TCB = the idle
  thread, `REFILL_MAX = 2 ≠ 0`; every scheduler word apart from the notification code's);
* `epStateRel_B`, `ntfnStateRel_B` (no endpoint / notification / reply), `irqRel_B` (IRQ state words 0 = inactive;
  the node: gen 34's `σB_irqRel_node`), `ioRel_B` (bitmap 0 = no port allocated), `kRootRel_B` (`KERNEL_ROOT` =
  the global PML4's physical-map address, `FEATURES` bit 1 = huge pages);
* `topPlaced_B` (`TopPlaced`), `vsRel_B` (ASID table 0 = `initArchState`'s empty table), `ptRel_B` / `poolsIn_B`
  (no table set), `curOK_B`;
* `ipcRel_B`, `esa_B`; **`xtop_B`**: `XTopAt AR (ZB G0) sB a σB`.

No premise (the arch relation `AR` is a hypothesis of `xtop_B` only through `hAR`, discharged by `ART = True`).
No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootRelF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp
open Fl4Proofs.P3.Ipc Classical

noncomputable section

/-! ## Words of `sB` -/

theorem tiB_ne0' : tiB ≠ 0#u64 := fun e => by
  have := congrArg UScalar.val e; rw [tiB_val] at this; exact absurd this (by decide)

/-- An idle-TCB word other than `STATE` / `SC`: 0. -/
theorem tw0 {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 4096) (h8 : k % 8 = 0) (h1 : k ≠ 3328) (h2 : k ≠ 3464) :
    bsL.mem sB (core.num.U64.wrapping_add tiB K) = 0#u64 := by
  rw [memB_at (tiB_off hK hk) (by omega)]; exact wordB_zero_of (by omega)

/-- An idle-SC word other than `TCB`, `REFILL_MAX`, `REFILL_TAIL` and the two `MAX_PERIOD` words: 0. -/
theorem sw0 {K : U64} {k : Nat} (hK : K.val = k) (hk : k < 128) (h8 : k % 8 = 0) (h1 : k ≠ 24) (h2 : k ≠ 72)
    (h3 : k ≠ 88) (h4 : k ≠ 104) (h5 : k ≠ 112) :
    bsL.mem sB (core.num.U64.wrapping_add sciB K) = 0#u64 := by
  rw [memB_at (sciB_off hK (by omega)) (by omega)]; exact wordB_zero_of (by omega)

/-- A node-0 word by offset. -/
theorem nw {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 4288) (h8 : k % 8 = 0) :
    bsL.mem sB (bsL.nodeAt sB 0#u64 o) = wordB (18446744071562114304 + k) :=
  memB_at (by rw [sB_nodeAt_val (by omega), ho]) (by omega)

/-- A node-0 word other than the four thread / SC words: 0. -/
theorem nw0 {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 4288) (h8 : k % 8 = 0) (h1 : k ≠ 0) (h2 : k ≠ 8)
    (h3 : k ≠ 24) (h4 : k ≠ 32) : bsL.mem sB (bsL.nodeAt sB 0#u64 o) = 0#u64 := by
  rw [nw ho hk h8]; exact wordB_zero_of (by omega)

/-- A block word by offset. -/
theorem memB_ks {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 13568) (h8 : k % 8 = 0) :
    bsL.mem sB (core.num.U64.wrapping_add kbB o) = wordB (18446744071562100736 + k) :=
  memB_at (a := core.num.U64.wrapping_add kbB o) (ksWB_val ho hk) (by omega)

/-- A block word other than `DOMAIN_TIME`, entry 0's duration, `FEATURES`, `KERNEL_ROOT`: 0. -/
theorem kw0 {o : U64} {k : Nat} (ho : o.val = k) (hk : k < 13568) (h8 : k % 8 = 0) (h1 : k ≠ 16) (h2 : k ≠ 200)
    (h3 : k ≠ 72) (h4 : k ≠ 48) : bsL.mem sB (core.num.U64.wrapping_add kbB o) = 0#u64 := by
  rw [memB_ks ho hk h8]; exact wordB_zero_of (by omega)

theorem stw : bsL.mem sB (tStA tiB) = 7#u64 := by
  rw [memB_at (a := tStA tiB) (tiB_off (n := 3328) (by simp [layout.tcb.STATE, layout.tcb.F]) (by omega)) (by omega)]
  simp [wordB]

theorem scw : bsL.mem sB (scA tiB) = sciB := by
  rw [memB_at (a := scA tiB) (tiB_off (n := 3464) (by decide) (by omega)) (by omega)]
  simp [wordB]

theorem badge_val : layout.reg.BADGE.val = 0 := by simp [layout.reg.BADGE, layout.reg.RDI]

theorem regw (i : U64) (hi : i.val < 24) : bsL.mem sB (Endp.regA tiB i) = 0#u64 := by
  rw [memB_at (Endp.regA_val tiB_addr hi) (by rw [tiB_val]; omega)]
  rw [tiB_val]; exact wordB_zero_of (by omega)

theorem regIdx_lt (r : Fl4Spec.Register) : (regIdx r).val < 24 := by cases r <;> decide

/-- The words of the idle TCB the notification code writes lie in the idle TCB. -/
theorem nwrite_ti {a : U64} (h : NWrite ∅ {tiB} a) :
    18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 4096 := by
  rcases h with ⟨n, hn, -⟩ | ⟨t, ht, h⟩
  · exact hn.elim
  · have e : t = tiB := ht
    subst e
    have hb := badge_val
    rcases h with rfl | rfl | rfl | rfl | rfl
    · have : (tStA tiB).val = 18446744071562072064 + 3328 :=
        tiB_off (by simp [layout.tcb.STATE, layout.tcb.F]) (by omega)
      omega
    · have : (tBlockA tiB).val = 18446744071562072064 + 3336 := tiB_off (by decide) (by omega)
      omega
    · have : (badgeRegA tiB).val = tiB.val + 256 + 8 * layout.reg.BADGE.val :=
        Endp.regA_val tiB_addr (by omega)
      rw [tiB_val] at this; omega
    · have : (P1.nextA .Ep tiB).val = 18446744071562072064 + 3496 := tiB_off (by decide) (by omega)
      omega
    · have : (P1.prevA .Ep tiB).val = 18446744071562072064 + 3504 := tiB_off (by decide) (by omega)
      omega

theorem efoot_ti {a : U64} (h : EFoot {tiB} ∅ ∅ ∅ a) :
    18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 4096 := by
  rcases h with ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, -⟩
  · exact he.elim
  · exact hr.elim
  · have e : t = tiB := ht
    subst e
    obtain ⟨h1, h2⟩ := h
    unfold TOffN at h2
    rw [tiB_val] at h1 h2; omega
  · have e : t = tiB := ht
    subst e
    unfold TL at h; rw [tiB_val] at h; omega
  · exact hw.elim

theorem ewrite_ti {a : U64} (h : EWrite {tiB} ∅ ∅ ∅ a) :
    18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 4096 := efoot_ti h.foot

/-! ## The idle TCB -/

theorem tcbRelE_B : TcbRelE ∅ (bsL.mem sB) tiB idleTcbB where
  st := by rw [stw]; rfl
  blk e h := by simp [idleTcbB, Fl4Spec.epBlocked] at h
  send e d h := by simp [idleTcbB] at h
  recv e r d h := by simp [idleTcbB] at h
  reply r h := by simp [idleTcbB] at h
  regs r := by rw [regw _ (regIdx_lt r)]; rfl
  prio := by
    show (bsL.mem sB (core.num.U64.wrapping_add tiB 3448#u64)).val = _
    rw [tw0 (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega)]; rfl
  fault0 := ⟨fun _ => rfl, fun _ => tw0 (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega)⟩
  faultT := by
    have h0 : bsL.mem sB (tFaultA tiB) = 0#u64 := tw0 (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    constructor
    · intro h; exact absurd h (by decide)
    · rintro ⟨b, hb⟩; simp [idleTcbB] at hb
  bound := by
    show none = optRef (bsL.mem sB (core.num.U64.wrapping_add tiB 3368#u64))
    rw [tw0 (k := 3368) (by decide) (by omega) (by omega) (by omega) (by omega), optRef_zero]
  faultR := by
    show bsL.mem sB (core.num.U64.wrapping_add tiB 3376#u64) = 0#u64
    exact tw0 (k := 3376) (by decide) (by omega) (by omega) (by omega) (by omega)

theorem tcbRel1_B : TcbRel1 (bsL.mem sB) tiB idleTcbB where
  st := by rw [stw]; rfl
  blk n h := by simp [idleTcbB] at h
  badge := by
    show (bsL.mem sB (Endp.regA tiB layout.reg.BADGE)).bv = _
    rw [regw _ (by rw [badge_val]; omega)]; rfl
  prio := by
    show (bsL.mem sB (core.num.U64.wrapping_add tiB 3448#u64)).val = _
    rw [tw0 (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega)]; rfl

/-! ## The scheduler -/

theorem rmaxB : bsL.rmax sB sciB = 2#u64 := by
  unfold LawfulStore.rmax maxA
  rw [memB_at (sciB_off (n := 72) (by simp [layout.sc.REFILL_MAX]) (by omega)) (by omega)]
  simp [wordB]

theorem rheadB : bsL.rhead sB sciB = 0#u64 := by
  unfold LawfulStore.rhead headA
  exact sw0 (k := 80) (by simp [layout.sc.REFILL_HEAD]) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)

theorem rtailB : bsL.rtail sB sciB = 1#u64 := by
  unfold LawfulStore.rtail tailA
  rw [memB_at (sciB_off (n := 88) (by simp [layout.sc.REFILL_TAIL]) (by omega)) (by omega)]
  simp [wordB]

theorem refillsWF_B : RefillsWF bst sB sciB (0 + Fl4Spec.minSchedContextBits) where
  placed := ⟨by simp [Fl4Spec.minSchedContextBits], by rw [sciB_val]; simp [Fl4Spec.minSchedContextBits],
    by rw [sciB_val]; simp [Fl4Spec.minSchedContextBits]⟩
  min_le := by rw [rmaxB]; simp [sporadic.MIN_REFILLS]
  le_abs := by rw [rmaxB]; simp [absMax, Fl4Spec.minSchedContextBits]
  head_lt := by rw [rheadB, rmaxB]; decide
  tail_lt := by rw [rtailB, rmaxB]; decide

theorem scRel1_B : ScRel1 bst sB sciB idleScB 0 where
  wf := refillsWF_B
  period := by
    show _ = (bsL.mem sB (core.num.U64.wrapping_add sciB layout.sc.PERIOD)).bv
    rw [sw0 (k := 0) (by simp [layout.sc.PERIOD]) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; rfl
  consumed := by
    show _ = (bsL.mem sB (core.num.U64.wrapping_add sciB 8#u64)).bv
    rw [sw0 (k := 8) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
  tcb := by
    show _ = optRef (bsL.mem sB (core.num.U64.wrapping_add sciB 24#u64))
    rw [memB_at (sciB_off (n := 24) (by decide) (by omega)) (by omega)]
    have : wordB (18446744071562096640 + 24) = tiB := by simp [wordB]
    rw [this]
    unfold optRef
    rw [if_neg tiB_ne0', tiB_bv]; rfl
  ntfn := by
    show none = optRef (bsL.mem sB (core.num.U64.wrapping_add sciB 40#u64))
    rw [sw0 (k := 40) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      optRef_zero]
  badge := by
    show _ = (bsL.mem sB (core.num.U64.wrapping_add sciB 48#u64)).bv
    rw [sw0 (k := 48) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; rfl
  yieldFrom := by
    show none = optRef (bsL.mem sB (core.num.U64.wrapping_add sciB 56#u64))
    rw [sw0 (k := 56) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      optRef_zero]
  sporadic := by
    show false = decide (bsL.mem sB (core.num.U64.wrapping_add sciB 64#u64) ≠ 0#u64)
    rw [sw0 (k := 64) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    simp
  max := by rw [rmaxB]; rfl
  refills := by
    obtain ⟨-, -, -, -, -, hin⟩ := refillsWF_B.inside
    have hix : ∀ k, k < 2 → (bsL.ix sB sciB k).val = k := by
      intro k hk
      rw [refillsWF_B.ix_val, rheadB, rmaxB]
      show (0 + k) % 2 = k
      omega
    have r0 := hin (bsL.ix sB sciB 0) (by rw [hix 0 (by omega), rmaxB]; decide)
    have r1 := hin (bsL.ix sB sciB 1) (by rw [hix 1 (by omega), rmaxB]; decide)
    rw [hix 0 (by omega), sciB_val] at r0
    rw [hix 1 (by omega), sciB_val] at r1
    have hsz : bsL.size sB sciB = 2 := by
      unfold LawfulStore.size; rw [rmaxB, rheadB, rtailB]; rfl
    simp only [LawfulStore.refills, hsz, show List.range 2 = [0, 1] from rfl, List.map_cons, List.map_nil,
      LawfulStore.rf, LawfulStore.refill]
    rw [memB_at r0.1 (by omega), memB_at r0.2.1 (by omega), memB_at r1.1 (by omega), memB_at r1.2.1 (by omega)]
    have e1 : wordB (18446744071562096640 + 96 + 16 * 0) = 0#u64 := wordB_zero_of (by omega)
    have e2 : wordB (18446744071562096640 + 104 + 16 * 0) = maxPB := by simp [wordB]
    have e3 : wordB (18446744071562096640 + 96 + 16 * 1) = maxPB := by simp [wordB]
    have e4 : wordB (18446744071562096640 + 104 + 16 * 1) = 0#u64 := wordB_zero_of (by omega)
    rw [e1, e2, e3, e4]
    rfl

theorem scRelW_B : ScRelW bst Fl4Spec.idleScPtr sB sciB idleScB 0 where
  pl := refillsWF_B.placed
  period := scRel1_B.period
  consumed := scRel1_B.consumed
  tcb := scRel1_B.tcb
  ntfn := scRel1_B.ntfn
  badge := scRel1_B.badge
  yieldFrom := scRel1_B.yieldFrom
  sporadic := scRel1_B.sporadic
  spor h := by
    exact absurd (sw0 (k := 64) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)) h
  idle _ := by rw [rmaxB]; decide
  max := scRel1_B.max
  act _ := scRel1_B

theorem tiB_ne0 : tiB ≠ 0#u64 := fun e => by have := congrArg UScalar.val e; rw [tiB_val] at this; exact absurd this (by decide)
theorem sciB_ne0 : sciB ≠ 0#u64 := fun e => by
  have := congrArg UScalar.val e; rw [sciB_val] at this; exact absurd this (by decide)

theorem schedCore_B : SchedCore bst {tiB} 0#u64 sB (fun _ => []) [] where
  tcbs := tcbPlaced_B G0
  node := ⟨by rw [sB_nodeBase _ rfl], by rw [sB_nodeBase _ rfl]; norm_num, fun t ht => by
    rw [show t = tiB from ht, sB_nodeBase _ rfl, tiB_val]; omega⟩
  cur := sB_cpu
  aff t ht := by
    rw [show t = tiB from ht]
    exact tw0 (k := 3520) (by decide) (by omega) (by omega) (by omega) (by omega)
  prio t ht := by
    rw [show t = tiB from ht]
    show (bsL.mem sB (core.num.U64.wrapping_add tiB 3448#u64)).val < 256
    rw [tw0 (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega)]; decide
  ready := by
    refine ⟨⟨fun p hp => ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim, ?_, ?_, trivial⟩,
      fun _ _ _ _ _ x h => (List.not_mem_nil h).elim⟩, ⟨fun p hp => ?_, fun i hi => ?_⟩⟩
    · show bsL.mem sB (bsL.nodeAt sB 0#u64 (rqOff p)) = 0#u64
      exact nw0 (rqOff_val hp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · show bsL.mem sB (bsL.nodeAt sB 0#u64 (rqTailOff p)) = 0#u64
      exact nw0 (rqTailOff_val hp) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    · show (bsL.mem sB (bsL.nodeAt sB 0#u64 (l2Off (p.val / 64)))).bv.getLsbD (p.val % 64) = true ↔ _
      rw [nw0 (l2Off_val (by omega)) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp
    · show (bsL.mem sB (bsL.nodeAt sB 0#u64 l1Off)).bv.getLsbD i = true ↔ _
      rw [nw0 l1Off_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      simp only [LawfulStore.l2W]
      constructor
      · intro h; simp at h
      · rintro ⟨hi4, hne⟩
        exact absurd (nw0 (l2Off_val hi4) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)) hne
  release := by
    refine ⟨List.nodup_nil, fun _ h => (List.not_mem_nil h).elim, ?_, ?_, trivial⟩
    · show bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.RELEASE_HEAD) = 0#u64
      exact nw0 (k := 64) (by simp [layout.node.RELEASE_HEAD]) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega)
    · show bsL.mem sB (bsL.nodeAt sB 0#u64 (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64)) = 0#u64
      exact nw0 (k := 72) (by simp [layout.node.RELEASE_HEAD, core.num.U64.wrapping_add_val_eq, U64.size, U64.numBits]) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
  inQ _ _ _ h := (List.not_mem_nil h).elim
  queued t ht := by
    have h0 : bsL.mem sB (inqA tiB) = 0#u64 := tw0 (k := 3592) (by decide) (by omega) (by omega) (by omega) (by omega)
    rw [show t = tiB from ht, h0]
    simp
  released t ht := by
    have h0 : bsL.mem sB (inqA tiB) = 0#u64 := tw0 (k := 3592) (by decide) (by omega) (by omega) (by omega) (by omega)
    rw [show t = tiB from ht, h0]
    simp
  excl _ _ h := (List.not_mem_nil h).elim
  curT := by
    show bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CUR_THREAD) = tiB
    rw [nw curth0 (by omega) (by omega)]; simp [wordB]
  idleT := by
    show bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.IDLE_THREAD) = tiB
    rw [nw (k := 8) (by simp [layout.node.IDLE_THREAD]) (by omega) (by omega)]; simp [wordB]
  ksOut t ht := by rw [show t = tiB from ht, sB_ksb, kbB_val, tiB_val]; omega

theorem nodeCurSc : bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CUR_SC) = sciB := by
  rw [nw (k := 24) (by simp [layout.node.CUR_SC]) (by omega) (by omega)]; simp [wordB]

theorem nodeIdleSc : bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.IDLE_SC) = sciB := by
  rw [nw (k := 32) (by simp [layout.node.IDLE_SC]) (by omega) (by omega)]; simp [wordB]

theorem schedSpec_B : SchedSpec bst {tiB} {sciB} 0#u64 sB (fun _ => []) [] (σB (Z := Unit)) where
  rq _ _ := rfl
  rqDom _ _ _ := rfl
  rel := rfl
  curThread := by
    show _ = (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CUR_THREAD)).bv
    rw [nw curth0 (by omega) (by omega)]; simp [wordB, tiB_bv]; rfl
  curSc := by
    show _ = (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CUR_SC)).bv
    rw [nodeCurSc, sciB_bv]; rfl
  curTime := by
    show _ = (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CUR_TIME)).bv
    rw [nw0 (k := 48) (by simp [layout.node.CUR_TIME]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; rfl
  consumed := by
    show _ = (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.CONSUMED)).bv
    rw [nw0 (k := 40) (by simp [layout.node.CONSUMED]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; rfl
  curDom := ⟨rfl, by
    show bsL.mem sB (core.num.U64.wrapping_add (bsL.ksb sB) 8#u64) = 0#u64
    rw [sB_ksb]; exact kw0 (k := 8) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  tcb t ht := by
    rw [show t = tiB from ht]
    refine ⟨idleTcbB, σB_ti, rfl, tw0 (k := 3432) (by decide) (by omega) (by omega) (by omega) (by omega), ?_, ?_⟩
    · rw [scw]; unfold optRef; rw [if_neg sciB_ne0, sciB_bv]; rfl
    · show (bsL.mem sB (core.num.U64.wrapping_add tiB 3448#u64)).val = _
      rw [tw0 (k := 3448) (by decide) (by omega) (by omega) (by omega) (by omega)]; rfl
  scMem t ht _ := by rw [show t = tiB from ht, scw]; rfl
  scs sc hsc := by
    rw [show sc = sciB from hsc]
    exact ⟨idleScB, 0, σB_sci, scRelW_B⟩
  idleSc := by
    show (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.IDLE_SC)).bv = _
    rw [nodeIdleSc, sciB_bv]; rfl
  domTime := by
    show _ = (bsL.mem sB (core.num.U64.wrapping_add (bsL.ksb sB) 16#u64)).bv
    rw [sB_ksb, memB_ks (o := 16#u64) (k := 16) (by decide) (by omega) (by omega)]
    simp [wordB]; rfl
  idleTh := by
    show _ = (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.IDLE_THREAD)).bv
    rw [nw (k := 8) (by simp [layout.node.IDLE_THREAD]) (by omega) (by omega)]; simp [wordB, tiB_bv]; rfl

theorem schedRel_B : SchedRel bst ∅ {tiB} {sciB} 0#u64 sB (σB (Z := Unit)) where
  placed := ⟨tcbPlaced_B G0, fun _ h => h.elim, fun _ h => h.elim⟩
  nodeNW o ho h := by
    have := nwrite_ti h
    rw [sB_nodeAt_val ho] at this; omega
  domNW h := by
    have := nwrite_ti h
    have hv : (curDomA bst sB).val = 18446744071562100736 + 8 := ksWB_val (o := 8#u64) (by decide) (by omega)
    omega
  dtNW h := by
    have := nwrite_ti h
    have hv : (dtA bst sB).val = 18446744071562100736 + 16 := ksWB_val (o := 16#u64) (by decide) (by omega)
    omega
  scOut sc hsc x n hk a ha := by
    rw [show sc = sciB from hsc, σB_sci] at hk
    cases hk
    rw [show sc = sciB from hsc] at ha
    obtain ⟨g1, g2⟩ := ha
    rw [sciB_val] at g1 g2
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
    refine ⟨fun h => ?_, ?_, fun t ht => ?_, ?_⟩
    · have := nwrite_ti h; omega
    · rw [sB_nodeBase _ rfl]; omega
    · rw [show t = tiB from ht, tiB_val]; omega
    · rw [sB_ksb, kbB_val]; omega
  scDisj sc hsc sc' hsc' hne := absurd ((show sc = sciB from hsc).trans (show sc' = sciB from hsc').symm) hne
  actW := Or.inl (nw0 act_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  act := nw0 act_val (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  repr := by
    show false = decide (bsL.mem sB (bsL.nodeAt sB 0#u64 layout.node.REPROGRAM) ≠ 0#u64)
    rw [nw0 (k := 56) (by simp [layout.node.REPROGRAM]) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega)]; simp
  core sc hsc := by
    rw [show sc = sciB from hsc]
    exact sw0 (k := 16) (by decide) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  lists := ⟨_, _, schedCore_B, schedSpec_B⟩

/-! ## The other relations -/

theorem epStateRel_B : EpStateRel {tiB} ∅ ∅ ∅ (bsL.mem sB) (σB (Z := Unit)) where
  ep _ h := h.elim
  reply _ h := h.elim
  tcb t ht := by rw [show t = tiB from ht]; exact ⟨idleTcbB, σB_ti, tcbRelE_B⟩
  buf _ h := h.elim

theorem ntfnStateRel_B : NtfnStateRel ∅ {tiB} (bsL.mem sB) (σB (Z := Unit)) where
  ntfn _ h := h.elim
  tcb t ht := by rw [show t = tiB from ht]; exact ⟨idleTcbB, σB_ti, tcbRel1_B⟩

theorem irqRel_B : IrqRel (bsL.mem sB) (bsL.ksb sB) (σB (Z := Unit)) := by
  rw [sB_ksb]
  refine ⟨fun i hi => ?_, σB_irqRel_node⟩
  have hv := irqStA_val (kb := kbB) kbB_fit' hi
  rw [kbB_val] at hv
  rw [memB_at hv (by omega), wordB_zero_of (by omega)]
  exact ((irqSt_inactive _).2 rfl).symm

theorem ioRel_B : IoRel (bsL.mem sB) (bsL.ksb sB) (σB (Z := Unit)) := by
  rw [sB_ksb]
  intro p hp
  have hw := wI_val hp
  have hv := ioA_val (kb := kbB) (w := wI p) kbB_fit' (by omega)
  rw [kbB_val, hw] at hv
  show false = _
  unfold bitOf
  rw [memB_at hv (by omega), wordB_zero_of (by omega)]
  simp

theorem kRootRel_B : KRootRel (bsL.mem sB) (bsL.ksb sB) (σB (Z := Unit)) := by
  rw [sB_ksb]
  refine ⟨?_, ?_⟩
  · unfold KRootW
    rw [memB_ks (k := 48) (by simp [layout.ks.KERNEL_ROOT]) (by omega) (by omega)]
    simp only [wordB]
    simp
    rfl
  · unfold HugeRel
    rw [memB_ks (k := 72) (by simp [layout.ks.FEATURES]) (by omega) (by omega)]
    have hw : wordB (18446744071562100736 + 72) = 2#u64 := by simp [wordB]
    rw [hw]
    have h2 : (2#u64 &&& layout.ks.FEATURE_HUGE_PAGES) ≠ 0#u64 := by
      intro h; have := congrArg UScalar.val h; simp at this
    have h2' : ((2#u64 &&& layout.ks.FEATURE_HUGE_PAGES) != 0#u64) = true := bne_iff_ne.2 h2
    rw [h2']; rfl

/-! ## Placement and the VSpace relations -/

theorem slotW_range {b : U64} (h : SlotW thB b) : b.val < 18446744071562100736 + 5376 := by
  obtain ⟨x, hx, e | e⟩ := h
  · obtain ⟨-, hr⟩ := slot_range hx
    rw [e]; omega
  · obtain ⟨-, hr⟩ := slot_range hx
    rw [e, wa_val (k := 8#u64) (n := x.val + 8) (by rfl) (by omega)]; omega

theorem vsWrite_range {b : U64} (h : VsWrite ∅ kbB b) :
    18446744071562100736 + 288000 ≤ b.val ∧ b.val < 18446744071562100736 + 288000 + 16384 ∧ b.val % 8 = 0 := by
  rcases h with ⟨hi, hh, rfl⟩ | ⟨p, hp, -⟩
  · rw [atA_val (by rw [kbB_val]; norm_num) hh, kbB_val]; omega
  · exact hp.elim

theorem vobj_range {a : U64} (h : VObj thB ∅ ∅ ∅ ∅ ∅ kbB a) :
    (18446744071562100736 + 1248 ≤ a.val ∧ a.val < 18446744071562100736 + 5344) ∨
    (18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 192) ∨
    (18446744071562100736 + 288000 ≤ a.val ∧ a.val < 18446744071562100736 + 288000 + 16384) := by
  rcases h with ⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, -⟩ | ⟨h1, h2⟩
  · rcases thB_cases hq with ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
    · cases e
    · cases e; simp only [Nat.pow_zero] at h2; left; omega
  · rcases thB_cases ht with ⟨e, -⟩ | ⟨e, -⟩
    · right; left; omega
    · cases e
  · rcases hq with h | h | h | h | h <;> exact h.elim
  · right; right; rw [kbB_val] at h1 h2; omega

theorem oobj_range {a : U64} (h : OObj bst ∅ {tiB} {sciB} ∅ ∅ ∅ 0#u64 sB (σB (Z := Unit)) a) :
    (18446744071562114304 ≤ a.val ∧ a.val < 18446744071562114304 + 4288) ∨
    (18446744071562100736 ≤ a.val ∧ a.val < 18446744071562100736 + 13568 ∧
      (a.val < 18446744071562100736 + 1248 ∨ 18446744071562100736 + 5344 ≤ a.val)) ∨
    (18446744071562072064 + 256 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562096640 ≤ a.val ∧ a.val < 18446744071562096640 + 128) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨t, ht, h1, h2⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ |
      ⟨sc, hsc, x, n, hk, h1, h2⟩ | ⟨wp, hw, -⟩
  · left; rw [sB_nodeBase _ rfl] at h1 h2; omega
  · right; left; rw [sB_ksb, kbB_val] at h1 h2 h3; omega
  · right; right; left; rw [show t = tiB from ht, tiB_val] at h1 h2; omega
  · exact he.elim
  · exact hr.elim
  · exact hn.elim
  · rw [show sc = sciB from hsc, σB_sci] at hk
    cases hk
    rw [show sc = sciB from hsc, sciB_val] at h1 h2
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at h2
    right; right; right; omega
  · exact hw.elim

theorem topPlaced_B : TopPlaced bst thB ∅ ∅ ∅ ∅ ∅ ∅ {tiB} {sciB} ∅ ∅ ∅ 0#u64 sB (σB (Z := Unit)) where
  ep := ⟨tcbPlaced_B G0, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
    fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
    fun _ h => h.elim⟩
  vs := ⟨by rw [sB_ksb]; exact kbB_al8, by rw [sB_ksb, kbB_val]; norm_num, fun _ h => h.elim, fun _ h => h.elim⟩
  pt p hp := by rcases hp with h | h | h | h <;> exact h.elim
  pl := placed_B
  disj a ho hv := by
    rw [sB_ksb] at hv
    have h1 := oobj_range ho
    have h2 := vobj_range hv
    omega
  nodeE a h1 h2 h := by
    have := efoot_ti h
    rw [sB_nodeBase _ rfl] at h1 h2; omega
  po b h := by obtain ⟨p, hp, -⟩ := h; rcases hp with h | h | h | h <;> exact h.elim
  ps b h := by obtain ⟨p, hp, -⟩ := h; rcases hp with h | h | h | h <;> exact h.elim
  pv b h := by obtain ⟨p, hp, -⟩ := h; rcases hp with h | h | h | h <;> exact h.elim
  vo b h := by
    rw [sB_ksb] at h
    obtain ⟨g1, g2, g3⟩ := vsWrite_range h
    refine ⟨g3, fun p k hp ⟨h1, h2⟩ => ?_⟩
    rcases thB_in hp h1 h2 with h | h <;> omega
  sd b h hs := by
    rw [sB_ksb] at h
    have := vsWrite_range h
    have := slotW_range hs
    omega
  tko t ht := by
    rcases thB_cases ht with ⟨e, -⟩ | ⟨e, -⟩
    · rw [sB_ksb, kbB_val, e]; omega
    · cases e

theorem vsRel_B : VsRel ∅ (bsL.mem sB) (bsL.ksb sB) (σB (Z := Unit)) := by
  rw [sB_ksb]
  have h0 : ∀ hi : U64, hi.val < 2048 → bsL.mem sB (atA kbB hi) = 0#u64 := by
    intro hi hh
    rw [memB_at (atA_val (by rw [kbB_val]; norm_num) hh) (by rw [kbB_val]; omega), kbB_val]
    exact wordB_zero_of (by omega)
  refine ⟨fun hi hh => ?_, fun hi hh hne => absurd (h0 hi hh) hne, fun _ h => h.elim⟩
  rw [h0 hi hh, optRef_zero]; rfl

theorem ptRel_B : PtRel ∅ ∅ ∅ ∅ (bsL.mem sB) (σB (Z := Unit)) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem poolsIn_B : PoolsIn ∅ ∅ (bsL.mem sB) := fun _ h => h.elim

theorem curOK_B : Vs.CurOK bst thB sB (σB (Z := Unit)) :=
  ⟨tiB, tiB_bv, thB_ti, fun p asid h => by
    rw [slot_capAt ⟨tiB, 1, Or.inr ⟨thB_ti, by decide⟩, rfl⟩] at h
    cases ok_inj_ff h⟩

/-! ## `ipc`, `esa` and `XTopAt` -/

theorem ipcRel_B : IpcRel ∅ {tiB} ∅ ∅ ∅ (bsL.mem sB) (σB (Z := Unit)) :=
  IpcRel.of ntfnStateRel_B epStateRel_B (sched_sc (L := bsL) schedRel_B)

theorem esa_B : EpSchedApart bst {tiB} {sciB} ∅ ∅ ∅ 0#u64 sB (σB (Z := Unit)) where
  node a h1 h2 h := by
    have := efoot_ti h
    rw [sB_nodeBase _ rfl] at h1 h2; omega
  dom h := by
    have := ewrite_ti h
    have hv : (curDomA bst sB).val = 18446744071562100736 + 8 := ksWB_val (o := 8#u64) (by decide) (by omega)
    omega
  dt h := by
    have := ewrite_ti h
    have hv : (dtA bst sB).val = 18446744071562100736 + 16 := ksWB_val (o := 16#u64) (by decide) (by omega)
    omega
  sc sc hsc x n hk a ha h := by
    rw [show sc = sciB from hsc, σB_sci] at hk
    cases hk
    rw [show sc = sciB from hsc] at ha
    obtain ⟨g1, g2⟩ := ha
    rw [sciB_val] at g1 g2
    simp only [Fl4Spec.minSchedContextBits, Nat.zero_add, Nat.reducePow] at g2
    have := ewrite_ti h
    omega

/-- **`XTopAt` at the boot.** -/
theorem xtop_B {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {a : A}
    (hAR : AR a (σB (Z := Unit)).archState.x64CurrentCr3) : XTopAt (L := bsL) AR (ZB G0) sB a (σB (Z := Unit)) :=
  ⟨⟨⟨⟨schedRel_B, epStateRel_B, ntfnStateRel_B, irqRel_B, ioRel_B, kRootRel_B, hAR⟩, topPlaced_B⟩, vsRel_B,
    ptRel_B, poolsIn_B, curOK_B⟩, relTopB_B, ipcRel_B, esa_B⟩

end

end Fl4Proofs.P2.BootSt
