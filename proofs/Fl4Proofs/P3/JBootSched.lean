/-
P3 (line jboot, gen 2): **the scheduler relation `SchedRel` at the witness** (`w0`, `fInitASt`; JBootMem), with
the ghost sets `N = ∅`, `T = {idle TCB}` (`T0`), `C = {idle SC}` (`C0`), core 0, empty ready and release queues.

* **`w0_schedCore`** (`SchedCore`: placement, the node, empty queues and bitmap, the idle TCB current and idle),
* **`w0_scRelW`** (`ScRelW` of the idle SC: placed at `2 ^ 7`, configured with two refills
  `(0, MAX_PERIOD), (MAX_PERIOD, 0)`, `ScRel1`),
* **`w0_schedSpec`** (`SchedSpec`), and **`w0_schedRel`** (`SchedRel`);
* **`w0_tcbRelE`**, **`w0_epStateRel`** (`EpStateRel` at `E = R = B = ∅`), **`w0_ntfnStateRel`**
  (`NtfnStateRel` at `N = ∅`): the idle TCB's state word 7, registers, fault and bound words zero;
* **`w0_othersRel`**: `OthersRel` (scheduler, endpoint, notification, IRQ, IO-port, kernel-root and arch
  relations: the first half of `TopSR`, `XTopAt.fin`'s `SR`), with JBootMem's conjuncts;
* **`w0_tdx`** (`JKern.tdx`: `warI` has no TDX and no DMA RAM, as `initArchState`'s record) and **`w0_c0`**
  (`JAtZ.c0`).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootMem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif Fl4Proofs.P2.Wit

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The ghost sets -/

/-- The idle TCB's address. -/
def idT : U64 := 18446744071562072064#u64
/-- The idle SC's address. -/
def idS : U64 := 18446744071562096640#u64
/-- `T`: the idle TCB. -/
def T0 : Set U64 := {idT}
/-- `C`: the idle SC. -/
def C0 : Set U64 := {idS}

theorem idT_bv : idT.bv = idleThreadPtr := by decide
theorem idS_bv : idS.bv = idleScPtr := by decide
theorem idT_val : idT.val = 18446744071562072064 := rfl
theorem idS_val : idS.val = 18446744071562096640 := rfl

/-! ## Reading the image -/

/-- A wrapping sum below `2 ^ 64`. -/
theorem wa_val {a b : U64} (h : a.val + b.val < 2 ^ 64) : (core.num.U64.wrapping_add a b).val = a.val + b.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem nodeAt_v (o : U64) (ho : o.val < 4288) : (wL.nodeAt w0 0#u64 o).val = 18446744071562147072 + o.val := by
  unfold LawfulStore.nodeAt
  rw [ksb_w0]
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
  omega

/-- A node word of core 0, by offset. -/
theorem nodeW_v (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    nodeW wst w0 0#u64 o = img (18446744071562147072 + o.val) :=
  mem_al (nodeAt_v o ho) (by omega)

theorem img_mp1 : img 18446744071562096744 = mpW := by
  unfold img
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem img_mp2 : img 18446744071562096752 = mpW := by
  unfold img
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- A word of the idle TCB, by offset. -/
theorem tcbW_v (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) :
    wL.mem w0 (core.num.U64.wrapping_add idT K) = img (18446744071562072064 + K.val) :=
  mem_al (by rw [wa_val (by rw [idT_val]; omega), idT_val]) (by omega)

/-- A word of the idle SC, by offset. -/
theorem scW_v (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w0 (core.num.U64.wrapping_add idS K) = img (18446744071562096640 + K.val) :=
  mem_al (by rw [wa_val (by rw [idS_val]; omega), idS_val]) (by omega)

theorem tcb_addr : TcbAddr idT := ⟨by decide, by decide, by decide⟩

theorem tcbPlaced_T0 : TcbPlaced T0 := by
  intro t ht; rw [T0, Set.mem_singleton_iff] at ht; subst ht; exact tcb_addr

theorem nodePlaced_w0 : NodePlaced wst T0 w0 0#u64 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LawfulStore.nodeBase, ksb_w0, fkb_val]
  · simp [LawfulStore.nodeBase, ksb_w0, fkb_val]
  · intro t ht; rw [T0, Set.mem_singleton_iff] at ht; subst ht
    left; simp [LawfulStore.nodeBase, ksb_w0, fkb_val, idT_val]

/-! ## The core part -/

theorem rq_nil (p : U64) (hp : p.val < 256) : wL.rqQ w0 0#u64 p = ⟨0#u64, 0#u64⟩ := by
  unfold LawfulStore.rqQ
  have h1 : (rqOff p).val = 168 + 16 * p.val := by simp [rqOff]; omega
  have h2 : (rqTailOff p).val = 176 + 16 * p.val := by simp [rqTailOff]; omega
  rw [mem_al (nodeAt_v _ (by omega)) (by omega), mem_al (nodeAt_v _ (by omega)) (by omega), h1, h2]
  congr 1 <;> img0

theorem l1_zero : wL.l1W w0 0#u64 = 0#u64 := by
  unfold LawfulStore.l1W
  have h1 : (l1Off).val = 128 := by simp [l1Off]
  rw [mem_al (nodeAt_v _ (by omega)) (by omega), h1]; img0

theorem l2_zero (g : Nat) (hg : g < 4) : wL.l2W w0 0#u64 g = 0#u64 := by
  unfold LawfulStore.l2W
  have h1 : (l2Off g).val = 136 + 8 * (3 - g) := by simp [l2Off]; omega
  rw [mem_al (nodeAt_v _ (by omega)) (by omega), h1]; img0

theorem rel_nil : wL.relQ w0 0#u64 = ⟨0#u64, 0#u64⟩ := by
  unfold LawfulStore.relQ
  have h1 : (layout.node.RELEASE_HEAD).val = 64 := by unfold layout.node.RELEASE_HEAD; rfl
  have h2 : (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64).val = 72 := by
    unfold layout.node.RELEASE_HEAD; rfl
  rw [mem_al (nodeAt_v _ (by omega)) (by omega), mem_al (nodeAt_v _ (by omega)) (by omega), h1, h2]
  congr 1 <;> img0

theorem curT_w0 : nodeW wst w0 0#u64 layout.node.CUR_THREAD = idT := by
  rw [show layout.node.CUR_THREAD = 0#u64 by unfold layout.node.CUR_THREAD; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem idleT_w0 : nodeW wst w0 0#u64 layout.node.IDLE_THREAD = idT := by
  rw [show layout.node.IDLE_THREAD = 8#u64 by unfold layout.node.IDLE_THREAD; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem curSc_w0 : nodeW wst w0 0#u64 layout.node.CUR_SC = idS := by
  rw [show layout.node.CUR_SC = 24#u64 by unfold layout.node.CUR_SC; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem idleSc_w0 : nodeW wst w0 0#u64 layout.node.IDLE_SC = idS := by
  rw [show layout.node.IDLE_SC = 32#u64 by unfold layout.node.IDLE_SC; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem act_w0 : nodeW wst w0 0#u64 layout.node.SCHED_ACTION = 0#u64 := by
  rw [show layout.node.SCHED_ACTION = 16#u64 by unfold layout.node.SCHED_ACTION; rfl,
    nodeW_v _ (by decide) (by decide)]
  decide

theorem repr_w0 : nodeW wst w0 0#u64 layout.node.REPROGRAM = 0#u64 := by
  rw [show layout.node.REPROGRAM = 56#u64 by unfold layout.node.REPROGRAM; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem time_w0 : nodeW wst w0 0#u64 layout.node.CUR_TIME = 0#u64 := by
  rw [show layout.node.CUR_TIME = 48#u64 by unfold layout.node.CUR_TIME; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem cons_w0 : nodeW wst w0 0#u64 layout.node.CONSUMED = 0#u64 := by
  rw [show layout.node.CONSUMED = 40#u64 by unfold layout.node.CONSUMED; rfl, nodeW_v _ (by decide) (by decide)]
  decide

theorem inq_w0 : wL.mem w0 (inqA idT) = 0#u64 := by
  unfold inqA; rw [tcbW_v _ (by decide) (by decide)]; decide

theorem aff_w0 : wL.mem w0 (affA idT) = 0#u64 := by
  unfold affA; rw [tcbW_v _ (by decide) (by decide)]; decide

theorem prio_w0 : wL.mem w0 (prioA idT) = 0#u64 := by
  unfold prioA; rw [tcbW_v _ (by decide) (by decide)]; decide

theorem dom_w0 : wL.mem w0 (domA idT) = 0#u64 := by
  unfold domA; rw [tcbW_v _ (by decide) (by decide)]; decide

theorem sc_w0 : wL.mem w0 (scA idT) = idS := by
  unfold scA; rw [tcbW_v _ (by decide) (by decide)]; decide

/-- **`SchedCore` at the witness.** -/
theorem w0_schedCore : SchedCore wst T0 0#u64 w0 (fun _ => []) [] where
  tcbs := tcbPlaced_T0
  node := nodePlaced_w0
  cur := rfl
  aff t ht := by rw [T0, Set.mem_singleton_iff] at ht; subst ht; exact aff_w0
  prio t ht := by rw [T0, Set.mem_singleton_iff] at ht; subst ht; rw [prio_w0]; decide
  ready := ⟨⟨fun p hp => by rw [rq_nil p hp]; exact QueueRel.nil, fun _ _ _ _ _ x hx => (List.not_mem_nil hx).elim⟩,
    ⟨fun p hp => by
      rw [l2_zero _ (by omega)]
      simp,
    fun i hi => by
      rw [l1_zero]
      simp only [show (0#u64).bv.getLsbD i = false by simp, Bool.false_eq_true, false_iff, not_and, not_not]
      intro h; rw [l2_zero i h]⟩⟩
  release := by rw [rel_nil]; exact QueueRel.nil
  inQ _ _ _ h := (List.not_mem_nil h).elim
  queued t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    rw [inq_w0]; simp
  released t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    rw [inq_w0]; simp
  excl _ _ h := (List.not_mem_nil h).elim
  curT := by rw [curT_w0]; rfl
  idleT := by rw [idleT_w0]; rfl
  ksOut t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    left; rw [ksb_w0, fkb_val, idT_val]; decide

/-! ## The idle SC -/

theorem rmax_w0 : wL.rmax w0 idS = 2#u64 := by
  unfold LawfulStore.rmax maxA layout.sc.REFILL_MAX; rw [scW_v _ (by decide) (by decide)]; decide

theorem rhead_w0 : wL.rhead w0 idS = 0#u64 := by
  unfold LawfulStore.rhead headA layout.sc.REFILL_HEAD; rw [scW_v _ (by decide) (by decide)]; decide

theorem rtail_w0 : wL.rtail w0 idS = 1#u64 := by
  unfold LawfulStore.rtail tailA layout.sc.REFILL_TAIL; rw [scW_v _ (by decide) (by decide)]; decide

theorem rperiod_w0 : wL.rperiod w0 idS = 0#u64 := by
  unfold LawfulStore.rperiod periodA layout.sc.PERIOD; rw [scW_v _ (by decide) (by decide)]; decide

theorem scw_w0 (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w0 (scW idS K) = img (18446744071562096640 + K.val) := scW_v K hK h8

theorem refills_w0 : wL.refills w0 idS = [⟨0#u64, mpW⟩, ⟨mpW, 0#u64⟩] := by
  unfold LawfulStore.refills LawfulStore.size
  rw [rmax_w0, rhead_w0, rtail_w0]
  have e : ringN (2#u64).val (0#u64).val (1#u64).val = 2 := by decide
  rw [e]
  have r0 : wL.rf w0 idS 0 = ⟨0#u64, mpW⟩ := by
    unfold LawfulStore.rf LawfulStore.refill LawfulStore.ix
    rw [rhead_w0, rmax_w0]
    have a1 : (rtA idS (u64 (((0#u64).val + 0) % (2#u64).val))).val = 18446744071562096640 + 96 := by
      unfold rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have a2 : (raA idS (u64 (((0#u64).val + 0) % (2#u64).val))).val = 18446744071562096640 + 104 := by
      unfold raA rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    rw [mem_al a1 (by omega), mem_al a2 (by omega), img_mp1]
    rw [show img (18446744071562096640 + 96) = 0#u64 by decide]
  have r1 : wL.rf w0 idS 1 = ⟨mpW, 0#u64⟩ := by
    unfold LawfulStore.rf LawfulStore.refill LawfulStore.ix
    rw [rhead_w0, rmax_w0]
    have a1 : (rtA idS (u64 (((0#u64).val + 1) % (2#u64).val))).val = 18446744071562096640 + 112 := by
      unfold rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have a2 : (raA idS (u64 (((0#u64).val + 1) % (2#u64).val))).val = 18446744071562096640 + 120 := by
      unfold raA rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    rw [mem_al a1 (by omega), mem_al a2 (by omega), img_mp2]
    rw [show img (18446744071562096640 + 120) = 0#u64 by decide]
  show List.map (wL.rf w0 idS) [0, 1] = _
  rw [List.map_cons, List.map_cons, List.map_nil, r0, r1]

theorem placed_idS : P1.Placed idS (0 + minSchedContextBits) := ⟨by decide, by decide, by decide⟩

theorem wf_idS : RefillsWF wst w0 idS (0 + minSchedContextBits) where
  placed := placed_idS
  min_le := by rw [rmax_w0]; unfold sporadic.MIN_REFILLS; decide
  le_abs := by rw [rmax_w0]; decide
  head_lt := by rw [rhead_w0, rmax_w0]; decide
  tail_lt := by rw [rtail_w0, rmax_w0]; decide

/-- **`ScRel1` of the idle SC.** -/
theorem w0_scRel1 : ScRel1 wst w0 idS idleScV 0 :=
  ScRel1.ofWF wf_idS
    (by rw [rperiod_w0]; rfl)
    (by rw [scw_w0 _ (by decide) (by decide)]; decide)
    (by rw [scw_w0 _ (by decide) (by decide), show img (18446744071562096640 + (24#u64).val) = idT by decide]
        show some idleThreadPtr = optRef idT
        unfold optRef; rw [if_neg (by decide), idT_bv])
    (by rw [scw_w0 _ (by decide) (by decide)]; decide)
    (by rw [scw_w0 _ (by decide) (by decide)]; decide)
    (by rw [scw_w0 _ (by decide) (by decide)]; decide)
    (by rw [scw_w0 _ (by decide) (by decide)]; decide)
    (by rw [rmax_w0]; rfl)
    (by rw [refills_w0]; rfl)

/-- **`ScRelW` of the idle SC.** -/
theorem w0_scRelW : ScRelW wst idleScPtr w0 idS idleScV 0 where
  pl := placed_idS
  period := w0_scRel1.period
  consumed := w0_scRel1.consumed
  tcb := w0_scRel1.tcb
  ntfn := w0_scRel1.ntfn
  badge := w0_scRel1.badge
  yieldFrom := w0_scRel1.yieldFrom
  sporadic := w0_scRel1.sporadic
  spor _ := by rw [rmax_w0]; decide
  idle _ := by rw [rmax_w0]; decide
  max := w0_scRel1.max
  act _ := w0_scRel1

/-! ## The spec side -/

theorem curDom_w0 : wL.mem w0 (curDomA wst w0) = 0#u64 := by
  unfold curDomA
  rw [mem_al (n := 18446744071562133512) (by rw [wa_val (by rw [ksb_w0, fkb_val]; decide), ksb_w0, fkb_val]; rfl)
    (by norm_num)]
  decide

theorem dt_w0 : wL.mem w0 (dtA wst w0) = 15#u64 := by
  unfold dtA
  rw [mem_al (n := 18446744071562133520) (by rw [wa_val (by rw [ksb_w0, fkb_val]; decide), ksb_w0, fkb_val]; rfl)
    (by norm_num)]
  decide

theorem fInit_idleTcb : fInitASt.kheap idT.bv = some (.tcb idleTcbV) := by rw [idT_bv]; exact bootHeap_fInit.tcb

theorem fInit_idleSc : fInitASt.kheap idS.bv = some (.schedContext idleScV 0) := by
  rw [idS_bv]; exact bootHeap_fInit.sc

theorem optRef_idS : optRef idS = some idleScPtr := by unfold optRef; rw [if_neg (by decide), idS_bv]

/-- **`SchedSpec` at the witness.** -/
theorem w0_schedSpec : SchedSpec wst T0 C0 0#u64 w0 (fun _ => []) [] fInitASt where
  rq _ _ := rfl
  rqDom _ _ _ := rfl
  rel := rfl
  curThread := by rw [curT_w0, idT_bv]; rfl
  curSc := by rw [curSc_w0, idS_bv]; rfl
  curTime := by rw [time_w0]; rfl
  consumed := by rw [cons_w0]; rfl
  curDom := ⟨rfl, curDom_w0⟩
  tcb t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    exact ⟨idleTcbV, fInit_idleTcb, rfl, dom_w0, by rw [sc_w0, optRef_idS]; rfl, by rw [prio_w0]; rfl⟩
  scMem t ht _ := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    rw [sc_w0]; rfl
  scs sc hsc := by
    rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    exact ⟨idleScV, 0, fInit_idleSc, w0_scRelW⟩
  idleSc := by rw [idleSc_w0, idS_bv]; rfl
  domTime := by rw [dt_w0]; rfl
  idleTh := by rw [idleT_w0, idT_bv]; rfl

/-! ## The relation -/

theorem tSt_v : (tStA idT).val = 18446744071562072064 + 3328 := by
  unfold tStA layout.tcb.STATE layout.tcb.F; decide
theorem tBlock_v : (tBlockA idT).val = 18446744071562072064 + 3336 := by unfold tBlockA; decide
theorem badgeReg_v : (badgeRegA idT).val = 18446744071562072064 + 256 := by
  unfold badgeRegA layout.tcb.REGS layout.reg.BADGE layout.reg.RDI; decide
theorem nextEp_v : (Fl4Proofs.P1.nextA .Ep idT).val = 18446744071562072064 + 3496 := by unfold Fl4Proofs.P1.nextA nextOff; decide
theorem prevEp_v : (Fl4Proofs.P1.prevA .Ep idT).val = 18446744071562072064 + 3504 := by unfold Fl4Proofs.P1.prevA prevOff; decide

/-- A word outside the idle TCB is no notification write. -/
theorem nw_far {a : U64} (h : a.val < 18446744071562072064 ∨ 18446744071562072064 + 4096 ≤ a.val) :
    ¬ NWrite ∅ T0 a := by
  rintro (⟨n, hn, -⟩ | ⟨t, ht, e⟩)
  · exact hn
  · rw [T0, Set.mem_singleton_iff] at ht; subst ht
    rcases e with e | e | e | e | e <;> have := congrArg UScalar.val e
    · rw [tSt_v] at this; omega
    · rw [tBlock_v] at this; omega
    · rw [badgeReg_v] at this; omega
    · rw [nextEp_v] at this; omega
    · rw [prevEp_v] at this; omega

theorem nodeBase_w0 : wL.nodeBase w0 0#u64 = 18446744071562147072 := by
  simp [LawfulStore.nodeBase, ksb_w0, fkb_val]

/-- **`SchedRel` at the witness** (`N = ∅`, `T = {idle TCB}`, `C = {idle SC}`, core 0). -/
theorem w0_schedRel : SchedRel wst ∅ T0 C0 0#u64 w0 fInitASt where
  placed := ⟨tcbPlaced_T0, fun _ hn => hn.elim, fun _ hn => hn.elim⟩
  nodeNW o ho := nw_far (by rw [nodeAt_v o ho]; omega)
  domNW := nw_far (by
    unfold curDomA; rw [wa_val (by rw [ksb_w0, fkb_val]; decide), ksb_w0, fkb_val]; decide)
  dtNW := nw_far (by
    unfold dtA; rw [wa_val (by rw [ksb_w0, fkb_val]; decide), ksb_w0, fkb_val]; decide)
  scOut sc hsc x n hk a ha := by
    rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    rw [fInit_idleSc] at hk; cases hk
    obtain ⟨h1, h2⟩ := ha
    rw [idS_val] at h1 h2
    simp only [minSchedContextBits] at h2
    refine ⟨nw_far (by omega), ?_, ?_, ?_⟩
    · rw [nodeBase_w0]; omega
    · intro t ht; rw [T0, Set.mem_singleton_iff] at ht; subst ht; rw [idT_val]; omega
    · rw [ksb_w0, fkb_val]; omega
  scDisj sc hsc sc' hsc' hne := by
    rw [C0, Set.mem_singleton_iff] at hsc hsc'; subst hsc hsc'; exact absurd rfl hne
  actW := Or.inl act_w0
  act := by rw [act_w0]; rfl
  repr := by rw [repr_w0]; rfl
  core sc hsc := by
    rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    rw [scw_w0 _ (by decide) (by decide)]; decide
  lists := ⟨_, _, w0_schedCore, w0_schedSpec⟩

/-! ## The endpoint and notification relations' TCB part -/

theorem tcbZ (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hs : K.val ≠ 3328) (hc : K.val ≠ 3464) :
    wL.mem w0 (core.num.U64.wrapping_add idT K) = 0#u64 := by
  rw [tcbW_v K hK h8]; img0

theorem st_w0 : wL.mem w0 (tStA idT) = 7#u64 := by
  unfold tStA layout.tcb.STATE layout.tcb.F; rw [tcbW_v _ (by decide) (by decide)]; decide

theorem reg_w0 (i : U64) (hi : i.val < 32) : wL.mem w0 (Endp.regA idT i) = 0#u64 := by
  have hv : (Endp.regA idT i).val = 18446744071562072064 + 256 + 8 * i.val := by
    unfold Endp.regA layout.tcb.REGS
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, idT_val]
    omega
  rw [mem_al hv (by omega)]; img0

theorem badge_w0 : wL.mem w0 (badgeRegA idT) = 0#u64 := by
  rw [mem_al badgeReg_v (by omega)]; decide

theorem optRef_zero : optRef 0#u64 = none := by unfold optRef; simp

/-- **The idle TCB's endpoint relation** (`TcbRelE`). -/
theorem w0_tcbRelE : Endp.TcbRelE ∅ (wL.mem w0) idT idleTcbV where
  st := by rw [st_w0]; rfl
  blk _ h := by cases h
  send _ _ h := by cases h
  recv _ _ _ h := by cases h
  reply _ h := by cases h
  regs r := by rw [reg_w0 _ (by cases r <;> decide)]; rfl
  prio := by rw [prio_w0]; rfl
  fault0 := by unfold Endp.tFaultA; rw [tcbZ _ (by decide) (by decide) (by decide) (by decide)]; simp [idleTcbV]
  faultT := by unfold Endp.tFaultA; rw [tcbZ _ (by decide) (by decide) (by decide) (by decide)]; simp [idleTcbV]
  bound := by unfold Endp.tBoundA; rw [tcbZ _ (by decide) (by decide) (by decide) (by decide), optRef_zero]; rfl
  faultR := by
    unfold Endp.FaultRel Endp.FaultRel' Endp.tFaultA
    rw [tcbZ _ (by decide) (by decide) (by decide) (by decide)]
    exact rfl

/-- **`EpStateRel` at the witness** (no endpoint, reply or buffer word; the idle TCB). -/
theorem w0_epStateRel : Endp.EpStateRel T0 ∅ ∅ ∅ (wL.mem w0) fInitASt where
  ep _ h := h.elim
  reply _ h := h.elim
  tcb t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    exact ⟨idleTcbV, fInit_idleTcb, w0_tcbRelE⟩
  buf _ h := h.elim

/-- **`NtfnStateRel` at the witness** (no notification; the idle TCB). -/
theorem w0_ntfnStateRel : NtfnStateRel ∅ T0 (wL.mem w0) fInitASt where
  ntfn _ h := h.elim
  tcb t ht := by
    rw [T0, Set.mem_singleton_iff] at ht; subst ht
    exact ⟨idleTcbV, fInit_idleTcb, ⟨(by rw [st_w0]; rfl), (fun _ h => by cases h), (by rw [badge_w0]; rfl),
      (by rw [prio_w0]; rfl)⟩⟩

/-- **`JKern.tdx` at the witness**: `warI` answers no TDX and no DMA RAM, `initArchState`'s record says so. -/
theorem w0_tdx : TdxRel warI fInitASt := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

/-- **`JAtZ.c0` at the witness**: the idle SC is not at 0. -/
theorem w0_c0 : ∀ q ∈ C0, q ≠ 0#u64 := by
  intro q hq; rw [C0, Set.mem_singleton_iff] at hq; subst hq; decide

/-- **`OthersRel` at the witness**: the scheduler, endpoint, notification, IRQ, IO-port and kernel-root
relations and the arch relation (`TopSR`'s first half; `XTopAt.fin`'s `SR`). -/
theorem w0_othersRel (a : MachineState) :
    Vs.OthersRel wst ∅ T0 C0 ∅ ∅ ∅ 0#u64 wAR w0 a fInitASt :=
  ⟨w0_schedRel, w0_epStateRel, w0_ntfnStateRel, w0_irqRel, w0_ioRel, w0_kRootRel, w0_ar a⟩

end

end Fl4Proofs.P3.JBoot
