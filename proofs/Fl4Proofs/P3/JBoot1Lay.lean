/-
P3 (line jboot, gen 4): **the placement and P1-heap conjuncts of `JAtZ` at the richer witness** (`w1`, `σ1`, the
ghosts of JBoot1Z: `thW1`, `G1`, `Hw1`, `Dw`, `Csw = {0}`, `T1`, `C1`, every other set empty).

* **`w1_topPlaced`**, **`w1_ipcApart`**, **`w1_scApart`**, **`w1_ks`**, **`w1_ip`**, **`w1_rp`**, **`w1_apart`**,
  **`w1_nk`**, **`w1_nodeB`**;
* **`heapOK_Hw1`**, **`w1_jplaced`** / **`w1_jpl`**, **`w1_cover`**, **`w1_zH`**, **`w1_hset`**, **`w1_hscC`**;
* **`w1_jcov`** (`JCovD`): the idle objects and the kernel-state block exempt as at `w0`, the IRQ CNodes
  128..255 and the global tables dead, and the three new objects **covered by their caps**: the root TCB by
  the thread cap in the root CNode (`[rT, rT + 4095]`), the root SC by the SC cap (`[rS, rS + 127]`), the root
  CNode by the CNode cap in the root TCB's CSpace slot (`[rC, rC + 63]`);
* **`w1_jkern`** (`JKern`: the root TCB current, the root SC current), **`w1_zD`**.

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBoot1Cs
import Fl4Proofs.P3.JBootLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical
open Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

set_option maxHeartbeats 1000000

/-- Case split on `Hw1`'s objects (`Hw1_pos`), the kind substituted. -/
macro "hwc1" h:term : tactic =>
  `(tactic| (rcases Hw1_pos $h with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ |
    ⟨e', e⟩ <;> cases e'))

theorem curW_w1 : wL.curW w1 = rT := curT_w1
theorem idleW_w1 : wL.idleW w1 = idT := idleT_w1
theorem cscW_w1 : wL.cscW w1 = rS := curSc_w1
theorem idleScW_w1 : idleScW (L := wL) w1 = idS := idleSc_w1

theorem dbgA_v1 : (wL.nodeAt w1 0#u64 layout.node.DEBUG_TCBS).val = 18446744071562147072 + 88 := by
  rw [nodeAt1_v _ (by rw [dbg_val]; omega), dbg_val]

theorem actA_v1 : (wL.nodeAt w1 (wL.cpu w1) layout.node.SCHED_ACTION).val = 18446744071562147072 + 16 := by
  rw [cpu_w1, nodeAt1_v _ (by rw [act_val]; omega), act_val]

theorem atA_v1 (hi : U64) (h : hi.val < 2048) :
    (atA (wL.ksb w1) hi).val = 18446744071562133504 + 288000 + 8 * hi.val := by
  unfold atA; rw [ksb_w1]
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
  omega

theorem stA_rT : (Fl4Proofs.P1.stA rT).val = 18446744071562100736 + 3328 := by
  rw [Fl4Proofs.P1.stA_eq]; exact (wa_val (a := rT) (b := 3328#u64) (by decide)).trans rfl

/-! ## `TopPlaced` -/

theorem oobj1_nat {a : U64} (h : Vs.OObj wst ∅ T1 C1 ∅ ∅ ∅ 0#u64 w1 σ1 a) :
    (18446744071562147072 ≤ a.val ∧ a.val < 18446744071562147072 + 4288) ∨
    (18446744071562133504 ≤ a.val ∧ a.val < 18446744071562133504 + 13568 ∧
      (a.val < 18446744071562133504 + 1248 ∨ 18446744071562133504 + 5344 ≤ a.val)) ∨
    (18446744071562072064 + 256 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562100736 + 256 ≤ a.val ∧ a.val < 18446744071562100736 + 4096) ∨
    (18446744071562096640 ≤ a.val ∧ a.val < 18446744071562096640 + 128) ∨
    (18446744071562104832 ≤ a.val ∧ a.val < 18446744071562104832 + 128) := by
  unfold Vs.OObj at h
  rw [nodeBase_w1, ksb_w1, fkb_val] at h
  rcases h with h | h | ⟨t, ht, h⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ | ⟨sc, hsc, x, n, hk, h⟩ | ⟨wp, hwp, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases memT1 ht with rfl | rfl
    · rw [idT_val] at h; exact Or.inr (Or.inr (Or.inl h))
    · rw [rT_val] at h; exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · simp at he
  · simp at hr
  · simp at hn
  · rcases memC1 hsc with rfl | rfl
    · rw [σ1_idleSc'] at hk; cases hk
      have := scObj_val h; rw [idS_val] at this; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl this))))
    · rw [σ1_rootSc] at hk; cases hk
      have := scObj_val h; rw [rS_val] at this; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr this))))
  · simp at hwp

theorem vobj1_nat {a : U64} (h : Vs.VObj thW1 ∅ ∅ ∅ ∅ ∅ (wL.ksb w1) a) :
    SlotNat1 a.val ∨ (18446744071562133504 + 288000 ≤ a.val ∧ a.val < 18446744071562133504 + 288000 + 16384) := by
  unfold Vs.VObj at h
  rw [ksb_w1, fkb_val] at h
  unfold SlotNat1 SlotNat
  rcases h with ⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, -⟩ | h
  · rcases thW1_pos hq with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e1, e⟩ | ⟨e, ⟨i, hi, e1⟩ | ⟨i, hi, hi2, e1⟩⟩
    · cases e
    · cases e
    · cases e; rw [Nat.pow_one] at h2; omega
    · cases e; rw [Nat.pow_zero] at h2; omega
    · cases e; rw [Nat.pow_zero] at h2; omega
  · rcases thW1_pos ht with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e⟩ | ⟨e, -⟩
    · omega
    · omega
    · cases e
    · cases e
  · simp at hq
  · exact Or.inr h

theorem slot_ends1 {x : U64} (h : IsSlot thW1 x) : SlotNat1 x.val ∧ SlotNat1 (x.val + 31) := by
  have h0 := (slot_nat1 h 0 (by omega)).1
  rw [Nat.add_zero] at h0
  exact ⟨h0, (slot_nat1 h 31 (by omega)).1⟩

theorem ePlaced1 : Endp.EPlaced T1 ∅ ∅ ∅ :=
  ⟨tcbPlaced_T1, fun e he => by simp at he, fun r hr => by simp at hr, fun e he => by simp at he,
    fun r hr => by simp at hr, fun e he => by simp at he, fun w hw => by simp at hw, fun w hw => by simp at hw,
    fun w hw => by simp at hw, fun w hw => by simp at hw, fun w hw => by simp at hw⟩

/-- **`TopPlaced` at `w1`.** -/
theorem w1_topPlaced : Vs.TopPlaced wst thW1 ∅ ∅ ∅ ∅ ∅ ∅ T1 C1 ∅ ∅ ∅ 0#u64 w1 σ1 where
  ep := ePlaced1
  vs := ⟨by rw [ksb_w1, fkb_val], by rw [ksb_w1, fkb_val]; omega, fun p hp => by simp at hp,
    fun p hp => by simp at hp⟩
  pt := fun p hp => by simp at hp
  pl := placed_thW1
  disj a hO hV := by
    have h1 := oobj1_nat hO
    have h2 := vobj1_nat hV
    unfold SlotNat1 SlotNat at h2
    omega
  nodeE a h1 h2 hE := by
    rw [nodeBase_w1] at h1 h2
    unfold Endp.EFoot at hE
    rcases hE with ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, h⟩ | ⟨wp, hwp, -⟩
    · simp at he
    · simp at hr
    · rcases memT1 ht with rfl | rfl
      · unfold Endp.TF Endp.TOffN Endp.TL at h; rw [idT_val] at h; omega
      · unfold Endp.TF Endp.TOffN Endp.TL at h; rw [rT_val] at h; omega
    · simp at hwp
  po b hb := by obtain ⟨p, hp, -⟩ := hb; simp at hp
  ps b hb := by obtain ⟨p, hp, -⟩ := hb; simp at hp
  pv b hb := by obtain ⟨p, hp, -⟩ := hb; simp at hp
  vo b hb := by
    rcases hb with ⟨hi, hhi, rfl⟩ | ⟨p, hp, -⟩
    · have hv := atA_v1 hi hhi
      refine ⟨by show (atA _ hi).val % 8 = 0; omega, fun p k hp hin => ?_⟩
      rw [hv] at hin
      thc1 hp <;> simp only [objSize, Nat.pow_zero, Nat.mul_one, Nat.pow_one] at hin <;> omega
    · simp at hp
  sd b hb hS := by
    obtain ⟨x, hx, hb'⟩ := hS
    have hx0 := (slot_nat1 hx 0 (by omega)).1
    have hx8 := (slot_nat1 hx 8 (by omega)).1
    unfold SlotNat1 SlotNat at hx0 hx8
    have hbv : b.val = x.val ∨ b.val = x.val + 8 := by
      rcases hb' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (wordOf_val (k := 8#u64) (by show x.val + 8 < 2 ^ 64; omega))
    rcases hb with ⟨hi, hhi, rfl⟩ | ⟨p, hp, -⟩
    · have hv := atA_v1 hi hhi
      omega
    · simp at hp
  tko t ht := by
    left; rw [ksb_w1, fkb_val]
    rcases thW1_pos ht with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e⟩ | ⟨e, -⟩
    · omega
    · omega
    · cases e
    · cases e

/-! ## The IPC and SC apartness -/

theorem w1_ipcApart : Ipc.IpcApart thW1 ∅ T1 ∅ ∅ ∅ (wL.ksb w1) 0#u64 where
  slot a ha x hx hin := by
    obtain ⟨h0, h31⟩ := slot_ends1 hx
    unfold SlotNat1 SlotNat at h0 h31
    unfold Ipc.IWords at ha
    rcases ha with ⟨t, ht, h⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ | ⟨wp, hwp, -⟩
    · rcases memT1 ht with rfl | rfl
      · rw [idT_val] at h; omega
      · rw [rT_val] at h; omega
    · simp at he
    · simp at hr
    · simp at hn
    · simp at hwp
  node a h1 h2 x hx hin := by
    obtain ⟨h0, h31⟩ := slot_ends1 hx
    unfold SlotNat1 SlotNat at h0 h31
    have z : (0#u64).val = 0 := rfl
    rw [ksb_w1, fkb_val, z] at h1 h2
    omega
  dom a ha := by
    rw [ksb_w1, fkb_val]
    unfold Ipc.IWords at ha
    rcases ha with ⟨t, ht, h⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ | ⟨wp, hwp, -⟩
    · rcases memT1 ht with rfl | rfl
      · rw [idT_val] at h; omega
      · rw [rT_val] at h; omega
    · simp at he
    · simp at hr
    · simp at hn
    · simp at hwp
  ks a h1 h2 h3 x hx hin := by
    obtain ⟨h0, h31⟩ := slot_ends1 hx
    unfold SlotNat1 SlotNat at h0 h31
    rw [ksb_w1, fkb_val] at h1 h2 h3
    omega
  kfit := fkb_lt
  kal := by rw [ksb_w1, fkb_val]

theorem w1_scApart : Ipc.ScApart thW1 C1 σ1 := by
  intro sc hsc x n hk a ha y hy hin
  obtain ⟨h0, h31⟩ := slot_ends1 hy
  unfold SlotNat1 SlotNat at h0 h31
  rcases memC1 hsc with rfl | rfl
  · rw [σ1_idleSc'] at hk; cases hk
    have := scObj_val ha; rw [idS_val] at this; omega
  · rw [σ1_rootSc] at hk; cases hk
    have := scObj_val ha; rw [rS_val] at this; omega

/-! ## The sets' placement -/

theorem w1_ks : KsApart ∅ T1 ∅ ∅ ∅ (wL.ksb w1) :=
  ⟨fun e he => by simp at he, fun r hr => by simp at hr, fun n hn => by simp at hn, fun w hw => by simp at hw⟩

theorem w1_ip : Ipc.IPlaced ∅ T1 ∅ ∅ ∅ :=
  ⟨⟨tcbPlaced_T1, fun n hn => by simp at hn, fun n hn => by simp at hn⟩, ePlaced1,
    fun n hn => by simp at hn, fun n hn => by simp at hn, fun n hn => by simp at hn⟩

theorem w1_rp : Sched.RPlaced wst ∅ T1 C1 ∅ 0#u64 w1 σ1 :=
  ⟨fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr,
    fun r hr => by simp at hr⟩

theorem w1_apart : Sched.SlotsApart (st := wst) thW1 T1 ∅ C1 ∅ 0#u64 w1 σ1 := by
  intro a ha
  obtain ⟨h0, h31⟩ := slot_ends1 ha
  unfold SlotNat1 SlotNat at h0 h31
  refine ⟨fun t ht => ?_, ?_, fun n hn => by simp at hn, fun sc hsc x n hk => ?_, fun r hr => by simp at hr⟩
  · rcases memT1 ht with rfl | rfl
    · rw [idT_val]; omega
    · rw [rT_val]; omega
  · rw [nodeBase_w1]; omega
  · rcases memC1 hsc with rfl | rfl
    · rw [σ1_idleSc'] at hk; cases hk; rw [e2sc, idS_val]; omega
    · rw [σ1_rootSc] at hk; cases hk; rw [e2sc, rS_val]; omega

theorem w1_nk : ∀ n ∈ (∅ : Set U64), n.val + 40 ≤ (wL.ksb w1).val ∨ (wL.ksb w1).val + 13568 ≤ n.val :=
  fun n hn => by simp at hn

theorem w1_nodeB : ∀ wp ∈ (∅ : Set (U64 × Fl4Spec.Word)), ∀ c : U64, c.val < 64 →
    wp.1.val + 8 ≤ wL.nodeBase w1 c ∨ wL.nodeBase w1 c + 4288 ≤ wp.1.val :=
  fun wp hw => by simp at hw

/-! ## P1's heap -/

theorem ne_rT_of {p : U64} (h : p.val ≠ 18446744071562100736) : p ≠ rT := ne_of_val (by rw [rT_val]; exact h)
theorem ne_rS_of {p : U64} (h : p.val ≠ 18446744071562104832) : p ≠ rS := ne_of_val (by rw [rS_val]; exact h)
theorem ne_rC_of {p : U64} (h : p.val ≠ 18446744071562108928) : p ≠ rC := ne_of_val (by rw [rC_val]; exact h)

theorem Hw1_zero : Hw1 0#u64 = none := by
  rw [Hw1_old (by decide) (by decide) (by decide)]; exact Hw_zero

/-- **`Hw1` is well formed.** -/
theorem heapOK_Hw1 : HeapOK Hw1 where
  align p k hp := by hwc1 hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  fits p k hp := by hwc1 hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  lt64 p k hp := by hwc1 hp <;> simp [HKind.bits]
  scmin p z hp := by hwc1 hp <;> omega
  disj p k q k' hp hq hne := by
    have hv : p.val ≠ q.val := fun e => hne (UScalar.eq_of_val_eq e)
    rcases Hw1_pos hp with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ |
      ⟨e', e⟩ <;> cases e' <;>
    rcases Hw1_pos hq with ⟨f, f'⟩ | ⟨f, f'⟩ | ⟨f, f'⟩ | ⟨f, f'⟩ | ⟨f, f'⟩ | ⟨f', f⟩ | ⟨f', f⟩ | ⟨f', f⟩ |
      ⟨f', f⟩ <;> cases f' <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega

theorem capTyped1 {x : U64} (h : IsSlot thW1 x) :
    CapTyped Hw1 (Heap.replies Hw1) (Heap.ntfns Hw1) (capV (wL.mem w1) x) := by
  unfold CapTyped
  rcases slot1_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] <;>
    exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩

theorem capV1_nodeA (i : U64) (hi : i.val < 128) : capV (wL.mem w1) (nodeA fkb i) = .Null := by
  have hv := nodeA_val (kb := fkb) fkb_lt hi
  rw [fkb_val] at hv
  have e8 : (8#u64).val = 8 := rfl
  exact capV_zero (by rw [mem1_al hv (by omega)]; img1z)
    (by rw [mem1_al (n := 18446744071562133504 + 1248 + 32 * i.val + 8) (by rw [wordOf_val (by omega), e8, hv])
      (by omega)]; img1z)

/-- **`JPlaced` at `w1`** (`Tr = T1`, `C = C1`). -/
theorem w1_jplaced : Sched.JPlaced (L := wL) thW1 Hw1 T1 C1 w1 σ1 where
  heap := heapOK_Hw1
  pl := placed_thW1
  tcb t := by
    constructor
    · intro h
      rcases thW1_some h with ⟨rfl, -⟩ | ⟨-, e⟩ | ⟨-, -, h'⟩
      · exact Hw1_rT
      · cases e
      · rcases thW_some h' with ⟨rfl, -⟩ | ⟨_, _, e⟩
        · exact Hw1_idT
        · cases e
    · intro h
      rcases Hw1_some h with ⟨rfl, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, h'⟩
      · exact thW1_rT
      · cases e
      · cases e
      · rcases Hw_pos h' with ⟨e, -⟩ | ⟨-, e'⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩
        · rw [show t = idT from UScalar.eq_of_val_eq (by rw [e, idT_val])]; exact thW1_idT
        all_goals cases e'
  cnode p r h := by
    rcases thW1_some h with ⟨-, e⟩ | ⟨rfl, e⟩ | ⟨n1, n2, h'⟩
    · cases e
    · cases e; exact Hw1_rC
    · have hs : p ≠ rS := by
        intro e; subst e; unfold thW at h'; rw [if_neg (by decide)] at h'
        split_ifs at h' with hx
        obtain ⟨irq, e⟩ := hx
        exact rS_irq irq e
      rw [Hw1_old n1 hs n2]; exact w0_jplaced.cnode p r h'
  tr := thT_thW1
  sc c y n hc hk := by
    rcases kh1_sc_of hk with ⟨e, -, rfl⟩ | ⟨e, -, rfl⟩
    · have : c = rS := Fl4Proofs.P1.eq_of_bv (by rw [e]); subst this; exact ⟨rS_mem, Hw1_rS⟩
    · have : c = idS := Fl4Proofs.P1.eq_of_bv (by rw [e, idS_bv]); subst this; exact ⟨idS_mem, Hw1_idS⟩
  ks p k hp hk := by
    rw [ksb_w1, fkb_val]
    rcases Hw1_pos hp with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ |
      ⟨e', e⟩ <;> cases e' <;>
      first
      | exact absurd rfl (hk _)
      | (simp only [HKind.bits, Nat.reducePow]; omega)
  ksIn p z hp := by
    rw [ksb_w1, fkb_val]
    hwc1 hp <;> simp only [Nat.reducePow] <;> omega
  typed a ha := capTyped1 ha
  irq i hi := by
    rw [ksb_w1, capV1_nodeA i hi]
    exact ⟨fun _ _ _ _ _ _ h => (by cases h), fun _ _ _ _ h => (by cases h), fun _ _ h => (by cases h)⟩
  fh t ht := by
    have h : AbsSlot thW1 (t.bv, Fl4Spec.tcbCnodeIndex 3) := by
      unfold AbsSlot; exact ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
    left
    have hs := AbsSlot.isSlot h
    rcases slot1_cases hs with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | e
    · exfalso
      have hv := congrArg UScalar.val e
      have hsv : (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)).val = t.val + 96 :=
        IsSlotAt.val placed_thW1 (i := 3) (Or.inr ⟨ht, by unfold tcbSlots; omega⟩)
      rcases thW1_pos ht with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e2⟩ | ⟨e2, -⟩ <;> try cases e2
      all_goals (rw [hsv] at hv; rw [rT_val] at hv; omega)
    · exfalso
      have hv := congrArg UScalar.val e
      have hsv : (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)).val = t.val + 96 :=
        IsSlotAt.val placed_thW1 (i := 3) (Or.inr ⟨ht, by unfold tcbSlots; omega⟩)
      rcases thW1_pos ht with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e2⟩ | ⟨e2, -⟩ <;> try cases e2
      all_goals (rw [hsv] at hv; rw [rC_val] at hv; omega)
    · exfalso
      have hv := congrArg UScalar.val e
      have hsv : (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 3)).val = t.val + 96 :=
        IsSlotAt.val placed_thW1 (i := 3) (Or.inr ⟨ht, by unfold tcbSlots; omega⟩)
      rcases thW1_pos ht with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e2⟩ | ⟨e2, -⟩ <;> try cases e2
      all_goals (rw [hsv] at hv; change _ = 18446744071562108960 at hv; omega)
    · exact e
  bfs t ht := by
    have h : AbsSlot thW1 (t.bv, Fl4Spec.tcbCnodeIndex 2) := by
      unfold AbsSlot; exact ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
    have hs := AbsSlot.isSlot h
    have hsv : (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)).val = t.val + 64 :=
      IsSlotAt.val placed_thW1 (i := 2) (Or.inr ⟨ht, by unfold tcbSlots; omega⟩)
    have ht' := thW1_pos ht
    rw [capV1_slot hs (ne_of_val (by rw [hsv, rT_val]; rcases ht' with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e2⟩ | ⟨e2, -⟩ <;>
        first | (cases e2; done) | omega))
      (ne_of_val (by rw [hsv, rC_val]; rcases ht' with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e2⟩ | ⟨e2, -⟩ <;>
        first | (cases e2; done) | omega))
      (ne_of_val (by rw [hsv]; change _ ≠ 18446744071562108960; rcases ht' with ⟨e1, -⟩ | ⟨e1, -⟩ | ⟨-, e2⟩ | ⟨e2, -⟩ <;>
        first | (cases e2; done) | omega))]
    exact Or.inl rfl
  cobj a ha := by
    rcases slot1_cases ha with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e]
    · trivial
    · trivial
    · exact ⟨Hw1_rS, by rw [idleScW_w1]; decide⟩
    · trivial

theorem w1_jpl : ∃ Tr Cq, Sched.JPlaced (L := wL) thW1 Hw1 Tr Cq w1 σ1 := ⟨T1, C1, w1_jplaced⟩

/-- **`SpecCover` at `w1`.** -/
theorem w1_cover : Sched.SpecCover Hw1 σ1 where
  ntfn o x h := (kh1_no_ntfn h).elim
  ep o x h := (kh1_no_ep h).elim
  reply o x h := (kh1_no_reply h).elim
  sc0 y k h := by
    have h' : kh1 (0#u64 : U64).bv = some (.schedContext y k) := h
    rcases kh1_sc_of h' with ⟨e, -⟩ | ⟨e, -⟩ <;> exact absurd e (by decide)
  arch o ao h := by
    rcases kh1_some h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨n1, n2, n3, h'⟩
    · cases e
    · cases e
    · cases e
    · obtain ⟨n, hn, hH⟩ := w0_cover.arch o ao h'
      refine ⟨n, hn, ?_⟩
      rw [Hw1_old (fun e => n1 (congrArg UScalar.bv e)) (fun e => n2 (congrArg UScalar.bv e))
        (fun e => n3 (congrArg UScalar.bv e))]
      exact hH

theorem w1_zH : (∀ t ∈ T1, Hw1 t = some .tcb) ∧ (∀ e ∈ (∅ : Set U64), Hw1 e = some .ep) ∧
    (∀ r ∈ (∅ : Set U64), Hw1 r = some .reply) ∧ (∀ n ∈ (∅ : Set U64), Hw1 n = some .ntfn) :=
  ⟨fun t ht => by rcases memT1 ht with rfl | rfl; exact Hw1_idT; exact Hw1_rT,
    fun e he => by simp at he, fun r hr => by simp at hr, fun n hn => by simp at hn⟩

theorem w1_hset : (∀ e, Hw1 e = some .ep → e ∈ (∅ : Set U64)) ∧ (∀ n, Hw1 n = some .ntfn → n ∈ (∅ : Set U64)) ∧
    (∀ r, Hw1 r = some .reply → r ∈ (∅ : Set U64)) :=
  ⟨fun e h => by hwc1 h, fun n h => by hwc1 h, fun r h => by hwc1 h⟩

theorem w1_hscC : ∀ c z, Hw1 c = some (.sc z) → c ∈ C1 := by
  intro c z h
  rcases Hw1_some h with ⟨-, e⟩ | ⟨rfl, -⟩ | ⟨-, e⟩ | ⟨-, -, -, h'⟩
  · cases e
  · exact rS_mem
  · cases e
  · have := w0_hscC c z h'; rw [Set.mem_singleton_iff.mp this]; exact idS_mem

/-! ## The cover and the dead set -/

theorem ksObj1_blk {q : U64} (h1 : 18446744071562133504 ≤ q.val) (h2 : q.val < 18446744071562133504 + 13568) :
    KsObj (L := wL) thW1 Hw1 w1 q := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> unfold KsIn <;> rw [ksb_w1, fkb_val]
  · thc1 hk <;>
      simp only [objSize, Nat.pow_zero, Nat.mul_one, Nat.pow_one, show max 32 1 = 32 by decide,
        show max 4096 1 = 4096 by decide, show max (32 * 2) 1 = 64 by decide] <;> omega
  · hwc1 hk <;> simp only [HKind.bits, Nat.reducePow] <;> omega

theorem Hw1_D {q : U64} (hq : q ∈ Dw) : Hw1 q = some (.other 12) ∨ Hw1 q = some (.other 5) := by
  have hq' := hq
  simp only [Dw, Set.mem_ofPred_eq] at hq'
  rw [Hw1_old (ne_rT_of (by omega)) (ne_rS_of (by omega)) (ne_rC_of (by omega))]
  exact Hw_D hq

theorem cov_rT : Covered (wL.mem w1) G1 rT.val (rT.val + 4096) :=
  ⟨rC, G1_flat.2 (Or.inr (Or.inl rfl)), by rw [capV_rC]; exact physF_thC, by rw [capV_rC]; rfl,
    by rw [capV_rC, base_thC]; rfl, by rw [capV_rC, top_thC]; rfl⟩

theorem cov_rS : Covered (wL.mem w1) G1 rS.val (rS.val + 128) :=
  ⟨rC1, G1_flat.2 (Or.inr (Or.inr rfl)), by rw [capV_rC1]; exact physF_scC, by rw [capV_rC1]; rfl,
    by rw [capV_rC1, base_scC]; rfl, by rw [capV_rC1, top_scC]; rfl⟩

theorem cov_rC : Covered (wL.mem w1) G1 rC.val (rC.val + 64) :=
  ⟨rT, G1_flat.2 (Or.inl rfl), by rw [capV_rT]; exact physF_cnC, by rw [capV_rT]; rfl,
    by rw [capV_rT, base_cnC]; rfl, by rw [capV_rT, top_cnC]; rfl⟩

/-- **`JCovD` at `w1`** (module docstring). -/
theorem w1_jcov : Sched.JCovD (L := wL) thW1 Hw1 G1 Dw Csw w1 where
  th q k hq := by
    rcases thW1_some hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨n1, n2, h'⟩
    · exact Or.inl cov_rT
    · exact Or.inl cov_rC
    · rcases thW_pos h' with ⟨e, -⟩ | ⟨-, ⟨i, hi, e⟩ | ⟨i, hi, hi2, e⟩⟩
      · have : q = idT := UScalar.eq_of_val_eq (by rw [e, idT_val])
        subst this
        exact Or.inr (Or.inr (Or.inl (Or.inl idleW_w1.symm)))
      · exact Or.inr (Or.inr (Or.inr (ksObj1_blk (by omega) (by omega))))
      · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
  h q k hq := by
    rcases Hw1_some hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨-, -, -, h'⟩
    · exact Or.inl cov_rT
    · exact Or.inl cov_rS
    · exact Or.inl cov_rC
    · rcases Hw_pos h' with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
      · have : q = idT := UScalar.eq_of_val_eq (by rw [e, idT_val])
        subst this
        exact Or.inr (Or.inr (Or.inl (Or.inl idleW_w1.symm)))
      · have : q = idS := UScalar.eq_of_val_eq (by rw [e, idS_val])
        subst this
        exact Or.inr (Or.inr (Or.inl (Or.inr idleScW_w1.symm)))
      · exact Or.inr (Or.inl (Or.inr e))
      · exact Or.inr (Or.inl (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr (ksObj1_blk (by omega) (by omega))))
      · exact Or.inr (Or.inr (Or.inr (ksObj1_blk (by omega) (by omega))))
  dead q hq := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun z h => ?_⟩ <;>
      rcases Hw1_D hq with e | e <;> rw [e] at h <;> cases h
  ks x hx _ _ _ h := (flat1_nut hx h).elim
  idleOut x hx _ _ _ h := (flat1_nut hx h).elim
  dx q hq h := by rcases Hw1_D hq with e | e <;> rw [e] at h <;> cases h

/-! ## `JKern` -/

/-- **`JKern` at `w1`.** -/
theorem w1_jkern : JKern (L := wL) warI Hw1 Csw Dw thW1 w1 σ1 where
  orig := w1_orig
  cur := by rw [curW_w1]; rfl
  curT := by rw [curW_w1]; exact thW1_rT
  act := by
    have hv := actA_v1
    refine ⟨by show (wL.nodeAt w1 (wL.cpu w1) layout.node.SCHED_ACTION).val % 8 = 0; omega,
      fun p k hp hin => ?_⟩
    rw [hv] at hin
    thc1 hp <;> simp only [objSize, Nat.pow_zero, Nat.mul_one, Nat.pow_one] at hin <;> omega
  dwAl := by have := dbgA_v1; show (wL.nodeAt w1 0#u64 layout.node.DEBUG_TCBS).val % 8 = 0; omega
  dwObj a ha hin := by
    have hv := dbgA_v1
    obtain ⟨h0, h31⟩ := slot_ends1 ha
    unfold SlotNat1 SlotNat at h0 h31
    omega
  dwNe := by
    rw [dbgA_v1, curW_w1, stA_rT, actA_v1]
    omega
  head := Or.inl (by rw [mem1_al dbgA_v1 (by omega)]; img1z)
  gpm := ⟨_, by rw [σ1_kheap, kh1_old (by decide) (by decide) (by decide)]; exact bootHeap_fInit.pml4⟩
  ga := fInit_gpm_al.1
  gf := fInit_gpm_al.2
  heap := heapOK_Hw1
  h0 := Hw1_zero
  hks := w1_jplaced.ks
  hksIn := w1_jplaced.ksIn
  hnd p k hp c hc := by
    rw [Csw, Set.mem_singleton_iff] at hc; subst hc
    rw [nodeBase_w1]
    hwc1 hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  ksbFit := w1_jkernNum.1
  ksbAl := w1_jkernNum.2.1
  nodeFit := w1_jkernNum.2.2.1
  cpuCs := w1_jkernNum.2.2.2.1
  curH := by rw [curW_w1]; exact Hw1_rT
  cscH := by rw [cscW_w1, Hw1_rS]; exact Option.some_ne_none _
  csLt := w1_jkernNum.2.2.2.2.1
  cs0 := w1_jkernNum.2.2.2.2.2.1
  csN := w1_jkernNum.2.2.2.2.2.2
  tdx := w1_tdx

/-- **`JAtZ.zD` at `w1`**: no slot holds a zombie. -/
theorem w1_zD : ∀ p ∈ ZTcb (L := wL) thW1 w1, p ∈ Dw := by
  intro p hp
  obtain ⟨y, hy, zt, n, hc, -⟩ := hp
  rcases slot1_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | e <;> rw [e] at hc <;> cases hc

end

end Fl4Proofs.P3.JBoot
