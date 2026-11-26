/-
P3 (line jboot, gen 4): **the richer witness's memory image `w1`** and the scheduler / IPC-state / kernel-global
relations at `w1` / `σ1` (JBoot1St, JBoot1Spec).

`w1` is `w0` (JBootMem) with twelve words changed (`img1`):
* core 0's node: `CUR_THREAD` = the root TCB `rT`, `CUR_SC` = the root SC `rS` (`IDLE_*` stay the idle ones);
* the root TCB: `STATE` = 1 (`TS_RUNNING`), `SC` = `rS`, slot 0 (the CSpace root) the CNode cap word
  `cnW = 5 << 59 | 1 << 48 | rC & M48` (radix 1, no guard);
* the root SC: the idle SC's refill words (`REFILL_MAX` 2, tail 1, `MAX_PERIOD` twice) and `TCB` = `rT`;
* the root CNode: slot 0 the thread cap `thW_ = 6 << 59 | rT & M48`, slot 1 the SC cap
  `scW_ = 11 << 59 | 7 << 48 | rS & M48` (size 7).
All MDB words are zero: each cap is its own one-slot MDB chain, no cap is revocable.

Ghost sets `T1 = {idle TCB, root TCB}`, `C1 = {idle SC, root SC}` (JBoot1Spec), core 0.
* **`w1_schedRel`** (`SchedRel`), **`w1_epStateRel`**, **`w1_ntfnStateRel`** (the root TCB's state word 1 is
  `Running`), **`w1_irqRel`**, **`w1_ioRel`**, **`w1_kRootRel`**, **`w1_domRel`**, **`w1_othersRel`**,
  **`w1_jkernNum`**, **`w1_tdx`**, **`w1_c0`**.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1Spec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Notif Fl4Proofs.P3.Vs
  Fl4Proofs.P2.Wit

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The image -/

/-- The root CNode cap's first word (type 5, radix 1, pointer `rC`). -/
def cnW : U64 := 2882866709323096064#u64
/-- The root thread cap's first word (type 6, pointer `rT`). -/
def thrW : U64 := 3459045986649800704#u64
/-- The root SC cap's first word (type 11, size 7, pointer `rS`). -/
def sccW : U64 := 6343320073003896832#u64

/-- **The richer image** (module docstring): `img` with twelve words changed. -/
def img1 (a : Nat) : U64 :=
  if a = 18446744071562147072 then rT else
  if a = 18446744071562147096 then rS else
  if a = 18446744071562104064 then 1#u64 else
  if a = 18446744071562104200 then rS else
  if a = 18446744071562100736 then cnW else
  if a = 18446744071562104856 then rT else
  if a = 18446744071562104904 then 2#u64 else
  if a = 18446744071562104920 then 1#u64 else
  if a = 18446744071562104936 then mpW else
  if a = 18446744071562104944 then mpW else
  if a = 18446744071562108928 then thrW else
  if a = 18446744071562108960 then sccW else img a

/-- **The richer witness's FL4 store state**: the image, base `fkb`, CPU 0. -/
def w1 : WSt := { w := fun i => img1 (8 * i.val), kb := fkb, cpu := 0#u64 }

theorem mem_w1 (a : U64) : wL.mem w1 a = img1 (8 * (a.val / 8)) := rfl

theorem mem1_al {a : U64} {n : Nat} (h : a.val = n) (h8 : n % 8 = 0) : wL.mem w1 a = img1 n := by
  rw [mem_w1, h]; congr 1; omega

theorem ksb_w1 : wL.ksb w1 = fkb := rfl
theorem cpu_w1 : wL.cpu w1 = 0#u64 := rfl

/-- `img1` is `img` away from the twelve changed words. -/
theorem img1_old {a : Nat}
    (h1 : a ≠ 18446744071562147072) (h2 : a ≠ 18446744071562147096) (h3 : a ≠ 18446744071562104064)
    (h4 : a ≠ 18446744071562104200) (h5 : a ≠ 18446744071562100736) (h6 : a ≠ 18446744071562104856)
    (h7 : a ≠ 18446744071562104904) (h8 : a ≠ 18446744071562104920) (h9 : a ≠ 18446744071562104936)
    (h10 : a ≠ 18446744071562104944) (h11 : a ≠ 18446744071562108928) (h12 : a ≠ 18446744071562108960) :
    img1 a = img a := by
  unfold img1; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
    if_neg h9, if_neg h10, if_neg h11, if_neg h12]

/-- `img1` away from every nonzero word. -/
theorem img1_zero {a : Nat}
    (h1 : a ≠ 18446744071562147072) (h2 : a ≠ 18446744071562147096) (h3 : a ≠ 18446744071562104064)
    (h4 : a ≠ 18446744071562104200) (h5 : a ≠ 18446744071562100736) (h6 : a ≠ 18446744071562104856)
    (h7 : a ≠ 18446744071562104904) (h8 : a ≠ 18446744071562104920) (h9 : a ≠ 18446744071562104936)
    (h10 : a ≠ 18446744071562104944) (h11 : a ≠ 18446744071562108928) (h12 : a ≠ 18446744071562108960)
    (g1 : a ≠ 18446744071562133504)
    (g2 : a ≠ 18446744071562133520)
    (g3 : a ≠ 18446744071562133552)
    (g4 : a ≠ 18446744071562133576)
    (g5 : a ≠ 18446744071562133704)
    (g7 : a ≠ 18446744071562147080)
    (g9 : a ≠ 18446744071562147104)
    (g10 : a ≠ 18446744071562075392)
    (g11 : a ≠ 18446744071562075528)
    (g12 : a ≠ 18446744071562096664)
    (g13 : a ≠ 18446744071562096712)
    (g14 : a ≠ 18446744071562096728)
    (g15 : a ≠ 18446744071562096744)
    (g16 : a ≠ 18446744071562096752) :
    img1 a = 0#u64 := by
  rw [img1_old h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12]
  exact img_zero g1 g2 g3 g4 g5 h1 g7 h2 g9 g10 g11 g12 g13 g14 g15 g16

/-- `img1` away from its nonzero words, the side conditions by `omega`. -/
macro "img1z" : tactic => `(tactic| (apply img1_zero <;> omega))

/-- **`w1` and `w0` agree away from the changed words.** -/
theorem mem1_old {a : U64}
    (h : a.val < 18446744071562100736 ∨ 18446744071562108928 + 64 ≤ a.val)
    (hc : a.val / 8 ≠ 18446744071562147072 / 8) (hs : a.val / 8 ≠ 18446744071562147096 / 8) :
    wL.mem w1 a = wL.mem w0 a := by
  rw [mem_w1, mem_w0]; apply img1_old <;> omega

/-! ## The interrupt, IO-port and kernel-root words -/

/-- **`IrqRel` at `w1`.** -/
theorem w1_irqRel : IrqRel (wL.mem w1) (wL.ksb w1) σ1 := by
  refine ⟨fun i hi => ?_, fun i hi => fInitASt_irqNode i hi⟩
  have hv := irqStA_val (kb := fkb) fkb_lt hi
  rw [fkb_val] at hv
  rw [ksb_w1, mem1_al hv (by omega), show img1 (18446744071562133504 + 224 + 8 * i.val) = 0#u64 by img1z]
  simp [irqSt, σ1, fInitASt, initASt]

/-- **`IoRel` at `w1`.** -/
theorem w1_ioRel : IoRel (wL.mem w1) (wL.ksb w1) σ1 := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hv := ioA_val (kb := fkb) fkb_lt hw
  rw [fkb_val] at hv
  unfold bitOf
  rw [ksb_w1, mem1_al hv (by omega), show img1 (18446744071562133504 + 5344 + 8 * (wI p).val) = 0#u64 by img1z]
  simp [σ1, fInitASt, initASt, initArchState]

/-- **`KRootRel` at `w1`.** -/
theorem w1_kRootRel : KRootRel (wL.mem w1) (wL.ksb w1) σ1 := by
  refine ⟨?_, ?_⟩
  · unfold KRootW
    have hv : (core.num.U64.wrapping_add fkb layout.ks.KERNEL_ROOT).val = 18446744071562133552 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, fkb_val]
    rw [ksb_w1, mem1_al hv (by omega), show img1 18446744071562133552 = kRootV by decide]
    unfold globCr3
    show makeCr3 (addrFromPPtr kRootV.bv) 0 = makeCr3 (addrFromKPPtr initGlobalPml4) 0
    decide
  · unfold HugeRel
    have hv : (core.num.U64.wrapping_add fkb layout.ks.FEATURES).val = 18446744071562133576 := by
      unfold layout.ks.FEATURES
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, fkb_val]
    rw [ksb_w1, mem1_al hv (by omega), show img1 18446744071562133576 = 2#u64 by decide]
    unfold layout.ks.FEATURE_HUGE_PAGES
    decide

/-- **`DomRel` at `w1`.** -/
theorem w1_domRel : DomRel (wL.mem w1) (wL.ksb w1) σ1 := by
  have ent : ∀ i : U64, i.val < 2 → (ksW fkb (entOff i)).val = 18446744071562133504 + 192 + 16 * i.val := by
    intro i hi
    unfold ksW entOff
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
    omega
  have dur : ∀ i : U64, i.val < 2 → (ksW fkb (durOff i)).val = 18446744071562133504 + 200 + 16 * i.val := by
    intro i hi
    unfold ksW durOff entOff
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
    omega
  have k32 : (ksW fkb 32#u64).val = 18446744071562133536 := by
    rw [ksW_val (by rw [fkb_val]; decide), fkb_val]; rfl
  have k24 : (ksW fkb 24#u64).val = 18446744071562133528 := by
    rw [ksW_val (by rw [fkb_val]; decide), fkb_val]; rfl
  have hl : σ1.domainList = [((0 : BitVec 8), (-1 : BitVec 56)), (0, 0)] := rfl
  refine ⟨rfl, fun i hi => ?_, ?_, ?_⟩
  · rw [ksb_w1, mem1_al (ent i hi) (by omega), mem1_al (dur i hi) (by omega), hl]
    have h01 : i.val = 0 ∨ i.val = 1 := by omega
    rcases h01 with h0 | h1
    · rw [h0, show img1 (18446744071562133504 + 192 + 16 * 0) = 0#u64 by decide,
        show img1 (18446744071562133504 + 200 + 16 * 0) = 72057594037927935#u64 by decide]
      exact ⟨rfl, by decide, by decide, by decide⟩
    · rw [h1, show img1 (18446744071562133504 + 192 + 16 * 1) = 0#u64 by decide,
        show img1 (18446744071562133504 + 200 + 16 * 1) = 0#u64 by decide]
      exact ⟨rfl, by decide, by decide, fun _ => rfl⟩
  · rw [ksb_w1, mem1_al k32 (by omega), show img1 18446744071562133536 = 0#u64 by decide]; rfl
  · rw [ksb_w1, mem1_al k24 (by omega), show img1 18446744071562133528 = 0#u64 by decide]

theorem w1_ar (a : MachineState) : wAR a σ1.archState.x64CurrentCr3 := trivial

/-- **`JKern`'s kernel-state facts at `w1`.** -/
theorem w1_jkernNum :
    (wL.ksb w1).val + 13568 ≤ 2 ^ 64 ∧ (wL.ksb w1).val % 8 = 0 ∧
      (wL.ksb w1).val + 13568 + ((wL.cpu w1).val + 1) * 4288 ≤ 2 ^ 64 ∧ wL.cpu w1 ∈ ({0#u64} : Set U64) ∧
      (∀ c ∈ ({0#u64} : Set U64), c.val < 64) ∧ (0#u64 ∈ ({0#u64} : Set U64)) ∧
      ∃ n : Nat, ∀ c : U64, c ∈ ({0#u64} : Set U64) ↔ c.val < n := w0_jkernNum

/-! ## Reading the words of the objects -/

theorem nodeAt1_v (o : U64) (ho : o.val < 4288) : (wL.nodeAt w1 0#u64 o).val = 18446744071562147072 + o.val :=
  nodeAt_v o ho

theorem nodeW1_v (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    nodeW wst w1 0#u64 o = img1 (18446744071562147072 + o.val) :=
  mem1_al (nodeAt1_v o ho) (by omega)

theorem nodeBase_w1 : wL.nodeBase w1 0#u64 = 18446744071562147072 := nodeBase_w0

/-- A word of the idle TCB. -/
theorem tcbW1_v (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) :
    wL.mem w1 (core.num.U64.wrapping_add idT K) = img1 (18446744071562072064 + K.val) :=
  mem1_al (by rw [wa_val (by rw [idT_val]; omega), idT_val]) (by omega)

/-- A word of the root TCB. -/
theorem rtW_v (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) :
    wL.mem w1 (core.num.U64.wrapping_add rT K) = img1 (18446744071562100736 + K.val) :=
  mem1_al (by rw [wa_val (by rw [rT_val]; omega), rT_val]) (by omega)

/-- A word of the idle SC. -/
theorem scW1_v (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w1 (core.num.U64.wrapping_add idS K) = img1 (18446744071562096640 + K.val) :=
  mem1_al (by rw [wa_val (by rw [idS_val]; omega), idS_val]) (by omega)

/-- A word of the root SC. -/
theorem rsW_v (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w1 (core.num.U64.wrapping_add rS K) = img1 (18446744071562104832 + K.val) :=
  mem1_al (by rw [wa_val (by rw [rS_val]; omega), rS_val]) (by omega)

theorem tcbZ1 (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hs : K.val ≠ 3328) (hc : K.val ≠ 3464) :
    wL.mem w1 (core.num.U64.wrapping_add idT K) = 0#u64 := by
  rw [tcbW1_v K hK h8]; img1z

theorem rtZ (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hs : K.val ≠ 3328) (hc : K.val ≠ 3464)
    (h0 : K.val ≠ 0) : wL.mem w1 (core.num.U64.wrapping_add rT K) = 0#u64 := by
  rw [rtW_v K hK h8]; img1z

/-! ## The core part -/

theorem rq1_nil (p : U64) (hp : p.val < 256) : wL.rqQ w1 0#u64 p = ⟨0#u64, 0#u64⟩ := by
  unfold LawfulStore.rqQ
  have h1 : (rqOff p).val = 168 + 16 * p.val := by simp [rqOff]; omega
  have h2 : (rqTailOff p).val = 176 + 16 * p.val := by simp [rqTailOff]; omega
  rw [mem1_al (nodeAt1_v _ (by omega)) (by omega), mem1_al (nodeAt1_v _ (by omega)) (by omega), h1, h2]
  congr 1 <;> img1z

theorem l1_zero1 : wL.l1W w1 0#u64 = 0#u64 := by
  unfold LawfulStore.l1W
  have h1 : (l1Off).val = 128 := by simp [l1Off]
  rw [mem1_al (nodeAt1_v _ (by omega)) (by omega), h1]; img1z

theorem l2_zero1 (g : Nat) (hg : g < 4) : wL.l2W w1 0#u64 g = 0#u64 := by
  unfold LawfulStore.l2W
  have h1 : (l2Off g).val = 136 + 8 * (3 - g) := by simp [l2Off]; omega
  rw [mem1_al (nodeAt1_v _ (by omega)) (by omega), h1]; img1z

theorem rel1_nil : wL.relQ w1 0#u64 = ⟨0#u64, 0#u64⟩ := by
  unfold LawfulStore.relQ
  have h1 : (layout.node.RELEASE_HEAD).val = 64 := by unfold layout.node.RELEASE_HEAD; rfl
  have h2 : (core.num.U64.wrapping_add layout.node.RELEASE_HEAD 8#u64).val = 72 := by
    unfold layout.node.RELEASE_HEAD; rfl
  rw [mem1_al (nodeAt1_v _ (by omega)) (by omega), mem1_al (nodeAt1_v _ (by omega)) (by omega), h1, h2]
  congr 1 <;> img1z

theorem curT_w1 : nodeW wst w1 0#u64 layout.node.CUR_THREAD = rT := by
  rw [show layout.node.CUR_THREAD = 0#u64 by unfold layout.node.CUR_THREAD; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

theorem idleT_w1 : nodeW wst w1 0#u64 layout.node.IDLE_THREAD = idT := by
  rw [show layout.node.IDLE_THREAD = 8#u64 by unfold layout.node.IDLE_THREAD; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

theorem curSc_w1 : nodeW wst w1 0#u64 layout.node.CUR_SC = rS := by
  rw [show layout.node.CUR_SC = 24#u64 by unfold layout.node.CUR_SC; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

theorem idleSc_w1 : nodeW wst w1 0#u64 layout.node.IDLE_SC = idS := by
  rw [show layout.node.IDLE_SC = 32#u64 by unfold layout.node.IDLE_SC; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

theorem act_w1 : nodeW wst w1 0#u64 layout.node.SCHED_ACTION = 0#u64 := by
  rw [show layout.node.SCHED_ACTION = 16#u64 by unfold layout.node.SCHED_ACTION; rfl,
    nodeW1_v _ (by decide) (by decide)]
  decide

theorem repr_w1 : nodeW wst w1 0#u64 layout.node.REPROGRAM = 0#u64 := by
  rw [show layout.node.REPROGRAM = 56#u64 by unfold layout.node.REPROGRAM; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

theorem time_w1 : nodeW wst w1 0#u64 layout.node.CUR_TIME = 0#u64 := by
  rw [show layout.node.CUR_TIME = 48#u64 by unfold layout.node.CUR_TIME; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

theorem cons_w1 : nodeW wst w1 0#u64 layout.node.CONSUMED = 0#u64 := by
  rw [show layout.node.CONSUMED = 40#u64 by unfold layout.node.CONSUMED; rfl, nodeW1_v _ (by decide) (by decide)]
  decide

/-- The TCB words P3 reads by name, at both TCBs: every one zero but `STATE` and `SC`. -/
theorem inq_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (inqA t) = 0#u64 := by
  rcases ht with rfl | rfl
  · unfold inqA; exact tcbZ1 _ (by decide) (by decide) (by decide) (by decide)
  · unfold inqA; exact rtZ _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem aff_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (affA t) = 0#u64 := by
  rcases ht with rfl | rfl
  · unfold affA; exact tcbZ1 _ (by decide) (by decide) (by decide) (by decide)
  · unfold affA; exact rtZ _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem prio_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (prioA t) = 0#u64 := by
  rcases ht with rfl | rfl
  · unfold prioA; exact tcbZ1 _ (by decide) (by decide) (by decide) (by decide)
  · unfold prioA; exact rtZ _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem dom_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (domA t) = 0#u64 := by
  rcases ht with rfl | rfl
  · unfold domA; exact tcbZ1 _ (by decide) (by decide) (by decide) (by decide)
  · unfold domA; exact rtZ _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem sc_idT1 : wL.mem w1 (scA idT) = idS := by
  unfold scA; rw [tcbW1_v _ (by decide) (by decide)]; decide

theorem sc_rT1 : wL.mem w1 (scA rT) = rS := by
  unfold scA; rw [rtW_v _ (by decide) (by decide)]; decide

theorem memT1 {t : U64} (h : t ∈ T1) : t = idT ∨ t = rT := h
theorem memC1 {c : U64} (h : c ∈ C1) : c = idS ∨ c = rS := h

theorem tcbPlaced_T1 : TcbPlaced T1 := by
  intro t ht
  rcases memT1 ht with rfl | rfl
  · exact tcb_addr
  · exact ⟨by decide, by decide, by decide⟩

theorem nodePlaced_w1 : NodePlaced wst T1 w1 0#u64 := by
  refine ⟨?_, ?_, ?_⟩
  · simp [LawfulStore.nodeBase, ksb_w1, fkb_val]
  · simp [LawfulStore.nodeBase, ksb_w1, fkb_val]
  · intro t ht
    left
    rcases memT1 ht with rfl | rfl <;> simp [LawfulStore.nodeBase, ksb_w1, fkb_val, idT_val, rT_val]

/-- **`SchedCore` at `w1`.** -/
theorem w1_schedCore : SchedCore wst T1 0#u64 w1 (fun _ => []) [] where
  tcbs := tcbPlaced_T1
  node := nodePlaced_w1
  cur := rfl
  aff t ht := aff_w1 t ht
  prio t ht := by rw [prio_w1 t ht]; decide
  ready := ⟨⟨fun p hp => by rw [rq1_nil p hp]; exact QueueRel.nil, fun _ _ _ _ _ x hx => (List.not_mem_nil hx).elim⟩,
    ⟨fun p hp => by
      rw [l2_zero1 _ (by omega)]
      simp,
    fun i hi => by
      rw [l1_zero1]
      simp only [show (0#u64).bv.getLsbD i = false by simp, Bool.false_eq_true, false_iff, not_and, not_not]
      intro h; rw [l2_zero1 i h]⟩⟩
  release := by rw [rel1_nil]; exact QueueRel.nil
  inQ _ _ _ h := (List.not_mem_nil h).elim
  queued t ht := by rw [inq_w1 t ht]; simp
  released t ht := by rw [inq_w1 t ht]; simp
  excl _ _ h := (List.not_mem_nil h).elim
  curT := by rw [curT_w1]; exact rT_mem
  idleT := by rw [idleT_w1]; exact idT_mem
  ksOut t ht := by
    left; rcases memT1 ht with rfl | rfl <;> rw [ksb_w1, fkb_val] <;> decide

/-! ## The root SC -/

theorem rmax_rS : wL.rmax w1 rS = 2#u64 := by
  unfold LawfulStore.rmax maxA layout.sc.REFILL_MAX; rw [rsW_v _ (by decide) (by decide)]; decide

theorem rhead_rS : wL.rhead w1 rS = 0#u64 := by
  unfold LawfulStore.rhead headA layout.sc.REFILL_HEAD; rw [rsW_v _ (by decide) (by decide)]; decide

theorem rtail_rS : wL.rtail w1 rS = 1#u64 := by
  unfold LawfulStore.rtail tailA layout.sc.REFILL_TAIL; rw [rsW_v _ (by decide) (by decide)]; decide

theorem rperiod_rS : wL.rperiod w1 rS = 0#u64 := by
  unfold LawfulStore.rperiod periodA layout.sc.PERIOD; rw [rsW_v _ (by decide) (by decide)]; decide

theorem img1_rmp1 : img1 18446744071562104936 = mpW := by
  unfold img1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem img1_rmp2 : img1 18446744071562104944 = mpW := by
  unfold img1
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem refills_rS : wL.refills w1 rS = [⟨0#u64, mpW⟩, ⟨mpW, 0#u64⟩] := by
  unfold LawfulStore.refills LawfulStore.size
  rw [rmax_rS, rhead_rS, rtail_rS]
  have e : ringN (2#u64).val (0#u64).val (1#u64).val = 2 := by decide
  rw [e]
  have r0 : wL.rf w1 rS 0 = ⟨0#u64, mpW⟩ := by
    unfold LawfulStore.rf LawfulStore.refill LawfulStore.ix
    rw [rhead_rS, rmax_rS]
    have a1 : (rtA rS (u64 (((0#u64).val + 0) % (2#u64).val))).val = 18446744071562104832 + 96 := by
      unfold rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have a2 : (raA rS (u64 (((0#u64).val + 0) % (2#u64).val))).val = 18446744071562104832 + 104 := by
      unfold raA rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    rw [mem1_al a1 (by omega), mem1_al a2 (by omega), show 18446744071562104832 + 104 = 18446744071562104936 by rfl,
      img1_rmp1]
    rw [show img1 (18446744071562104832 + 96) = 0#u64 by decide]
  have r1 : wL.rf w1 rS 1 = ⟨mpW, 0#u64⟩ := by
    unfold LawfulStore.rf LawfulStore.refill LawfulStore.ix
    rw [rhead_rS, rmax_rS]
    have a1 : (rtA rS (u64 (((0#u64).val + 1) % (2#u64).val))).val = 18446744071562104832 + 112 := by
      unfold rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have a2 : (raA rS (u64 (((0#u64).val + 1) % (2#u64).val))).val = 18446744071562104832 + 120 := by
      unfold raA rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    rw [mem1_al a1 (by omega), mem1_al a2 (by omega), show 18446744071562104832 + 112 = 18446744071562104944 by rfl,
      img1_rmp2]
    rw [show img1 (18446744071562104832 + 120) = 0#u64 by decide]
  show List.map (wL.rf w1 rS) [0, 1] = _
  rw [List.map_cons, List.map_cons, List.map_nil, r0, r1]

theorem placed_rS : P1.Placed rS (0 + minSchedContextBits) := ⟨by decide, by decide, by decide⟩

theorem wf_rS : RefillsWF wst w1 rS (0 + minSchedContextBits) where
  placed := placed_rS
  min_le := by rw [rmax_rS]; unfold sporadic.MIN_REFILLS; decide
  le_abs := by rw [rmax_rS]; decide
  head_lt := by rw [rhead_rS, rmax_rS]; decide
  tail_lt := by rw [rtail_rS, rmax_rS]; decide

theorem rsw (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w1 (scW rS K) = img1 (18446744071562104832 + K.val) := rsW_v K hK h8

theorem optRef_rT : optRef rT = some rT.bv := by unfold optRef; rw [if_neg (by decide)]
theorem optRef_rS : optRef rS = some rS.bv := by unfold optRef; rw [if_neg (by decide)]

theorem w1_scRel1_rS : ScRel1 wst w1 rS rootScV 0 :=
  ScRel1.ofWF wf_rS
    (by rw [rperiod_rS]; rfl)
    (by rw [rsw _ (by decide) (by decide)]; decide)
    (by rw [rsw _ (by decide) (by decide), show img1 (18446744071562104832 + (24#u64).val) = rT by decide,
          optRef_rT]; rfl)
    (by rw [rsw _ (by decide) (by decide)]; decide)
    (by rw [rsw _ (by decide) (by decide)]; decide)
    (by rw [rsw _ (by decide) (by decide)]; decide)
    (by rw [rsw _ (by decide) (by decide)]; decide)
    (by rw [rmax_rS]; rfl)
    (by rw [refills_rS]; rfl)

theorem w1_scRelW_rS : ScRelW wst idleScPtr w1 rS rootScV 0 where
  pl := placed_rS
  period := w1_scRel1_rS.period
  consumed := w1_scRel1_rS.consumed
  tcb := w1_scRel1_rS.tcb
  ntfn := w1_scRel1_rS.ntfn
  badge := w1_scRel1_rS.badge
  yieldFrom := w1_scRel1_rS.yieldFrom
  sporadic := w1_scRel1_rS.sporadic
  spor _ := by rw [rmax_rS]; decide
  idle _ := by rw [rmax_rS]; decide
  max := w1_scRel1_rS.max
  act _ := w1_scRel1_rS

/-! ## The idle SC at `w1` -/

theorem scw1 (K : U64) (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w1 (scW idS K) = img1 (18446744071562096640 + K.val) := scW1_v K hK h8

theorem mem1_idS {K : U64} (hK : K.val < 128) (h8 : K.val % 8 = 0) :
    wL.mem w1 (core.num.U64.wrapping_add idS K) = wL.mem w0 (core.num.U64.wrapping_add idS K) := by
  rw [scW1_v K hK h8, scW_v K hK h8]; apply img1_old <;> omega

theorem rmax_idS1 : wL.rmax w1 idS = 2#u64 := by
  unfold LawfulStore.rmax maxA layout.sc.REFILL_MAX; rw [scW1_v _ (by decide) (by decide)]; decide

theorem rhead_idS1 : wL.rhead w1 idS = 0#u64 := by
  unfold LawfulStore.rhead headA layout.sc.REFILL_HEAD; rw [scW1_v _ (by decide) (by decide)]; decide

theorem rtail_idS1 : wL.rtail w1 idS = 1#u64 := by
  unfold LawfulStore.rtail tailA layout.sc.REFILL_TAIL; rw [scW1_v _ (by decide) (by decide)]; decide

theorem rperiod_idS1 : wL.rperiod w1 idS = 0#u64 := by
  unfold LawfulStore.rperiod periodA layout.sc.PERIOD; rw [scW1_v _ (by decide) (by decide)]; decide

theorem refills_idS1 : wL.refills w1 idS = [⟨0#u64, mpW⟩, ⟨mpW, 0#u64⟩] := by
  unfold LawfulStore.refills LawfulStore.size
  rw [rmax_idS1, rhead_idS1, rtail_idS1]
  have e : ringN (2#u64).val (0#u64).val (1#u64).val = 2 := by decide
  rw [e]
  have r0 : wL.rf w1 idS 0 = ⟨0#u64, mpW⟩ := by
    unfold LawfulStore.rf LawfulStore.refill LawfulStore.ix
    rw [rhead_idS1, rmax_idS1]
    have a1 : (rtA idS (u64 (((0#u64).val + 0) % (2#u64).val))).val = 18446744071562096640 + 96 := by
      unfold rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have a2 : (raA idS (u64 (((0#u64).val + 0) % (2#u64).val))).val = 18446744071562096640 + 104 := by
      unfold raA rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have e1 : img1 (18446744071562096640 + 96) = 0#u64 := by decide
    have e2 : img1 (18446744071562096640 + 104) = mpW := by
      rw [img1_old (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]; exact img_mp1
    rw [mem1_al a1 (by omega), mem1_al a2 (by omega), e1, e2]
  have r1 : wL.rf w1 idS 1 = ⟨mpW, 0#u64⟩ := by
    unfold LawfulStore.rf LawfulStore.refill LawfulStore.ix
    rw [rhead_idS1, rmax_idS1]
    have a1 : (rtA idS (u64 (((0#u64).val + 1) % (2#u64).val))).val = 18446744071562096640 + 112 := by
      unfold rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have a2 : (raA idS (u64 (((0#u64).val + 1) % (2#u64).val))).val = 18446744071562096640 + 120 := by
      unfold raA rtA layout.sc.REFILLS layout.sc.REFILL_SIZE; decide
    have e1 : img1 (18446744071562096640 + 120) = 0#u64 := by decide
    have e2 : img1 (18446744071562096640 + 112) = mpW := by
      rw [img1_old (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]; exact img_mp2
    rw [mem1_al a1 (by omega), mem1_al a2 (by omega), e2, e1]
  show List.map (wL.rf w1 idS) [0, 1] = _
  rw [List.map_cons, List.map_cons, List.map_nil, r0, r1]

theorem wf_idS1 : RefillsWF wst w1 idS (0 + minSchedContextBits) where
  placed := placed_idS
  min_le := by rw [rmax_idS1]; unfold sporadic.MIN_REFILLS; decide
  le_abs := by rw [rmax_idS1]; decide
  head_lt := by rw [rhead_idS1, rmax_idS1]; decide
  tail_lt := by rw [rtail_idS1, rmax_idS1]; decide

theorem w1_scRel1_idS : ScRel1 wst w1 idS idleScV 0 :=
  ScRel1.ofWF wf_idS1
    (by rw [rperiod_idS1]; rfl)
    (by rw [scw1 _ (by decide) (by decide)]; decide)
    (by rw [scw1 _ (by decide) (by decide), show img1 (18446744071562096640 + (24#u64).val) = idT by decide]
        show some idleThreadPtr = optRef idT
        unfold optRef; rw [if_neg (by decide), idT_bv])
    (by rw [scw1 _ (by decide) (by decide)]; decide)
    (by rw [scw1 _ (by decide) (by decide)]; decide)
    (by rw [scw1 _ (by decide) (by decide)]; decide)
    (by rw [scw1 _ (by decide) (by decide)]; decide)
    (by rw [rmax_idS1]; rfl)
    (by rw [refills_idS1]; rfl)

theorem w1_scRelW_idS : ScRelW wst idleScPtr w1 idS idleScV 0 where
  pl := placed_idS
  period := w1_scRel1_idS.period
  consumed := w1_scRel1_idS.consumed
  tcb := w1_scRel1_idS.tcb
  ntfn := w1_scRel1_idS.ntfn
  badge := w1_scRel1_idS.badge
  yieldFrom := w1_scRel1_idS.yieldFrom
  sporadic := w1_scRel1_idS.sporadic
  spor _ := by rw [rmax_idS1]; decide
  idle _ := by rw [rmax_idS1]; decide
  max := w1_scRel1_idS.max
  act _ := w1_scRel1_idS

/-! ## The spec side -/

theorem curDom_w1 : wL.mem w1 (curDomA wst w1) = 0#u64 := by
  unfold curDomA
  rw [mem1_al (n := 18446744071562133512) (by rw [wa_val (by rw [ksb_w1, fkb_val]; decide), ksb_w1, fkb_val]; rfl)
    (by norm_num)]
  decide

theorem dt_w1 : wL.mem w1 (dtA wst w1) = 15#u64 := by
  unfold dtA
  rw [mem1_al (n := 18446744071562133520) (by rw [wa_val (by rw [ksb_w1, fkb_val]; decide), ksb_w1, fkb_val]; rfl)
    (by norm_num)]
  decide

theorem σ1_idleTcb : σ1.kheap idT.bv = some (.tcb idleTcbV) := by rw [idT_bv]; exact kh1_idleT
theorem σ1_idleSc' : σ1.kheap idS.bv = some (.schedContext idleScV 0) := by rw [idS_bv]; exact kh1_idleS
theorem σ1_rootTcb : σ1.kheap rT.bv = some (.tcb rootTcbV) := kh1_rT
theorem σ1_rootSc : σ1.kheap rS.bv = some (.schedContext rootScV 0) := kh1_rS

/-- **`SchedSpec` at `w1`.** -/
theorem w1_schedSpec : SchedSpec wst T1 C1 0#u64 w1 (fun _ => []) [] σ1 where
  rq _ _ := rfl
  rqDom _ _ _ := rfl
  rel := rfl
  curThread := by rw [curT_w1]; rfl
  curSc := by rw [curSc_w1]; rfl
  curTime := by rw [time_w1]; rfl
  consumed := by rw [cons_w1]; rfl
  curDom := ⟨rfl, curDom_w1⟩
  tcb t ht := by
    rcases memT1 ht with rfl | rfl
    · exact ⟨idleTcbV, σ1_idleTcb, rfl, dom_w1 _ ht, by rw [sc_idT1, optRef_idS]; rfl,
        by rw [prio_w1 _ ht]; rfl⟩
    · exact ⟨rootTcbV, σ1_rootTcb, rfl, dom_w1 _ ht, by rw [sc_rT1, optRef_rS]; rfl, by rw [prio_w1 _ ht]; rfl⟩
  scMem t ht _ := by
    rcases memT1 ht with rfl | rfl
    · rw [sc_idT1]; exact idS_mem
    · rw [sc_rT1]; exact rS_mem
  scs sc hsc := by
    rcases memC1 hsc with rfl | rfl
    · exact ⟨idleScV, 0, σ1_idleSc', w1_scRelW_idS⟩
    · exact ⟨rootScV, 0, σ1_rootSc, w1_scRelW_rS⟩
  idleSc := by rw [idleSc_w1, idS_bv]; rfl
  domTime := by rw [dt_w1]; rfl
  idleTh := by rw [idleT_w1, idT_bv]; rfl

/-! ## The relation -/

theorem tSt_rT : (tStA rT).val = 18446744071562100736 + 3328 := by
  unfold tStA layout.tcb.STATE layout.tcb.F; decide
theorem tBlock_rT : (tBlockA rT).val = 18446744071562100736 + 3336 := by unfold tBlockA; decide
theorem badgeReg_rT : (badgeRegA rT).val = 18446744071562100736 + 256 := by
  unfold badgeRegA layout.tcb.REGS layout.reg.BADGE layout.reg.RDI; decide
theorem nextEp_rT : (Fl4Proofs.P1.nextA .Ep rT).val = 18446744071562100736 + 3496 := by
  unfold Fl4Proofs.P1.nextA nextOff; decide
theorem prevEp_rT : (Fl4Proofs.P1.prevA .Ep rT).val = 18446744071562100736 + 3504 := by
  unfold Fl4Proofs.P1.prevA prevOff; decide

/-- A word outside both TCBs is no notification write. -/
theorem nw1_far {a : U64}
    (h : (a.val < 18446744071562072064 ∨ 18446744071562072064 + 4096 ≤ a.val) ∧
      (a.val < 18446744071562100736 ∨ 18446744071562100736 + 4096 ≤ a.val)) :
    ¬ NWrite ∅ T1 a := by
  rintro (⟨n, hn, -⟩ | ⟨t, ht, e⟩)
  · exact hn
  · rcases memT1 ht with rfl | rfl <;>
    rcases e with e | e | e | e | e <;> have := congrArg UScalar.val e
    · rw [tSt_v] at this; omega
    · rw [tBlock_v] at this; omega
    · rw [badgeReg_v] at this; omega
    · rw [nextEp_v] at this; omega
    · rw [prevEp_v] at this; omega
    · rw [tSt_rT] at this; omega
    · rw [tBlock_rT] at this; omega
    · rw [badgeReg_rT] at this; omega
    · rw [nextEp_rT] at this; omega
    · rw [prevEp_rT] at this; omega

theorem scObj_val {sc : U64} {a : U64} (h : Sched.ScObj sc 0 a) : sc.val ≤ a.val ∧ a.val < sc.val + 128 := by
  have e : (2 : Nat) ^ (0 + Fl4Spec.minSchedContextBits) = 128 := by decide
  unfold Sched.ScObj at h; rw [e] at h; exact h

/-- **`SchedRel` at `w1`** (`N = ∅`, `T = T1`, `C = C1`, core 0). -/
theorem w1_schedRel : SchedRel wst ∅ T1 C1 0#u64 w1 σ1 where
  placed := ⟨tcbPlaced_T1, fun _ hn => hn.elim, fun _ hn => hn.elim⟩
  nodeNW o ho := nw1_far (by rw [nodeAt1_v o ho]; omega)
  domNW := nw1_far (by
    unfold curDomA; rw [wa_val (by rw [ksb_w1, fkb_val]; decide), ksb_w1, fkb_val]; decide)
  dtNW := nw1_far (by
    unfold dtA; rw [wa_val (by rw [ksb_w1, fkb_val]; decide), ksb_w1, fkb_val]; decide)
  scOut sc hsc x n hk a ha := by
    rcases memC1 hsc with rfl | rfl
    · rw [σ1_idleSc'] at hk; cases hk
      obtain ⟨h1, h2⟩ := scObj_val ha
      rw [idS_val] at h1 h2
      refine ⟨nw1_far (by omega), ?_, ?_, ?_⟩
      · rw [nodeBase_w1]; omega
      · intro t ht; rcases memT1 ht with rfl | rfl <;> simp only [idT_val, rT_val] <;> omega
      · rw [ksb_w1, fkb_val]; omega
    · rw [σ1_rootSc] at hk; cases hk
      obtain ⟨h1, h2⟩ := scObj_val ha
      rw [rS_val] at h1 h2
      refine ⟨nw1_far (by omega), ?_, ?_, ?_⟩
      · rw [nodeBase_w1]; omega
      · intro t ht; rcases memT1 ht with rfl | rfl <;> simp only [idT_val, rT_val] <;> omega
      · rw [ksb_w1, fkb_val]; omega
  scDisj sc hsc sc' hsc' hne x n x' n' hk hk' a ha ha' := by
    rcases memC1 hsc with rfl | rfl <;> rcases memC1 hsc' with rfl | rfl
    · exact hne rfl
    · rw [σ1_idleSc'] at hk; cases hk; rw [σ1_rootSc] at hk'; cases hk'
      obtain ⟨a1, a2⟩ := scObj_val ha; obtain ⟨b1, b2⟩ := scObj_val ha'
      rw [idS_val] at a1 a2; rw [rS_val] at b1 b2; omega
    · rw [σ1_rootSc] at hk; cases hk; rw [σ1_idleSc'] at hk'; cases hk'
      obtain ⟨a1, a2⟩ := scObj_val ha; obtain ⟨b1, b2⟩ := scObj_val ha'
      rw [rS_val] at a1 a2; rw [idS_val] at b1 b2; omega
    · exact hne rfl
  actW := Or.inl act_w1
  act := by rw [act_w1]; rfl
  repr := by rw [repr_w1]; rfl
  core sc hsc := by
    rcases memC1 hsc with rfl | rfl
    · rw [scw1 _ (by decide) (by decide)]; decide
    · rw [rsw _ (by decide) (by decide)]; decide
  lists := ⟨_, _, w1_schedCore, w1_schedSpec⟩

/-! ## The endpoint and notification relations' TCB part -/

theorem st_idT1 : wL.mem w1 (tStA idT) = 7#u64 := by
  unfold tStA layout.tcb.STATE layout.tcb.F; rw [tcbW1_v _ (by decide) (by decide)]; decide

theorem st_rT1 : wL.mem w1 (tStA rT) = 1#u64 := by
  unfold tStA layout.tcb.STATE layout.tcb.F; rw [rtW_v _ (by decide) (by decide)]; decide

theorem reg_w1 (t : U64) (ht : t ∈ T1) (i : U64) (hi : i.val < 32) : wL.mem w1 (Endp.regA t i) = 0#u64 := by
  rcases memT1 ht with rfl | rfl
  · have hv : (Endp.regA idT i).val = 18446744071562072064 + 256 + 8 * i.val := by
      unfold Endp.regA layout.tcb.REGS
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, idT_val]
      omega
    rw [mem1_al hv (by omega)]; img1z
  · have hv : (Endp.regA rT i).val = 18446744071562100736 + 256 + 8 * i.val := by
      unfold Endp.regA layout.tcb.REGS
      simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, rT_val]
      omega
    rw [mem1_al hv (by omega)]; img1z

theorem badge_w1 (t : U64) (ht : t ∈ T1) : wL.mem w1 (badgeRegA t) = 0#u64 := by
  rcases memT1 ht with rfl | rfl
  · rw [mem1_al badgeReg_v (by omega)]; decide
  · rw [mem1_al badgeReg_rT (by omega)]; decide

/-- A zero TCB word of either TCB (not `STATE`, `SC` or the CSpace-root slot's first word). -/
theorem tZ1 (t : U64) (ht : t ∈ T1) (K : U64) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hs : K.val ≠ 3328)
    (hc : K.val ≠ 3464) (h0 : K.val ≠ 0) : wL.mem w1 (core.num.U64.wrapping_add t K) = 0#u64 := by
  rcases memT1 ht with rfl | rfl
  · exact tcbZ1 K hK h8 hs hc
  · exact rtZ K hK h8 hs hc h0

/-- **The TCBs' endpoint relation** (`TcbRelE`). -/
theorem w1_tcbRelE (t : U64) (ht : t ∈ T1) (x : Tcb) (hx : x = idleTcbV ∨ x = rootTcbV)
    (hst : (wL.mem w1 (tStA t)).val = tsCode x.tcbState) : Endp.TcbRelE ∅ (wL.mem w1) t x where
  st := hst
  blk _ h := by rcases hx with rfl | rfl <;> cases h
  send _ _ h := by rcases hx with rfl | rfl <;> cases h
  recv _ _ _ h := by rcases hx with rfl | rfl <;> cases h
  reply _ h := by rcases hx with rfl | rfl <;> cases h
  regs r := by rw [reg_w1 t ht _ (by cases r <;> decide)]; rcases hx with rfl | rfl <;> rfl
  prio := by rw [prio_w1 t ht]; rcases hx with rfl | rfl <;> rfl
  fault0 := by
    unfold Endp.tFaultA; rw [tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rcases hx with rfl | rfl <;> simp [idleTcbV, rootTcbV]
  faultT := by
    unfold Endp.tFaultA; rw [tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rcases hx with rfl | rfl <;> simp [idleTcbV, rootTcbV]
  bound := by
    unfold Endp.tBoundA; rw [tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide), optRef_zero]
    rcases hx with rfl | rfl <;> rfl
  faultR := by
    unfold Endp.FaultRel Endp.FaultRel' Endp.tFaultA
    rw [tZ1 t ht _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    rcases hx with rfl | rfl <;> exact rfl

/-- **`EpStateRel` at `w1`.** -/
theorem w1_epStateRel : Endp.EpStateRel T1 ∅ ∅ ∅ (wL.mem w1) σ1 where
  ep _ h := h.elim
  reply _ h := h.elim
  tcb t ht := by
    rcases memT1 ht with rfl | rfl
    · exact ⟨idleTcbV, σ1_idleTcb, w1_tcbRelE _ ht _ (Or.inl rfl) (by rw [st_idT1]; rfl)⟩
    · exact ⟨rootTcbV, σ1_rootTcb, w1_tcbRelE _ ht _ (Or.inr rfl) (by rw [st_rT1]; rfl)⟩
  buf _ h := h.elim

/-- **`NtfnStateRel` at `w1`.** -/
theorem w1_ntfnStateRel : NtfnStateRel ∅ T1 (wL.mem w1) σ1 where
  ntfn _ h := h.elim
  tcb t ht := by
    rcases memT1 ht with rfl | rfl
    · exact ⟨idleTcbV, σ1_idleTcb, ⟨(by rw [st_idT1]; rfl), (fun _ h => by cases h),
        (by rw [badge_w1 _ ht]; rfl), (by rw [prio_w1 _ ht]; rfl)⟩⟩
    · exact ⟨rootTcbV, σ1_rootTcb, ⟨(by rw [st_rT1]; rfl), (fun _ h => by cases h),
        (by rw [badge_w1 _ ht]; rfl), (by rw [prio_w1 _ ht]; rfl)⟩⟩

theorem w1_tdx : TdxRel warI σ1 := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem w1_c0 : ∀ q ∈ C1, q ≠ 0#u64 := by
  intro q hq; rcases memC1 hq with rfl | rfl <;> decide

/-- **`OthersRel` at `w1`.** -/
theorem w1_othersRel (a : MachineState) :
    Vs.OthersRel wst ∅ T1 C1 ∅ ∅ ∅ 0#u64 wAR w1 a σ1 :=
  ⟨w1_schedRel, w1_epStateRel, w1_ntfnStateRel, w1_irqRel, w1_ioRel, w1_kRootRel, w1_ar a⟩

end

end Fl4Proofs.P3.JBoot
