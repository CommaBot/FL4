/-
P3 (line jboot, gen 3): **the placement and P1-heap conjuncts of `JAtZ` at the witness** (`w0`, `fInitASt`, the
ghosts of JBootZ: `thW`, `Hw`, `Dw`, `Csw = {0}`, `T0`, `C0`, every other set empty).

* `XTopAt.fin`'s second half: **`w0_topPlaced`** (`Vs.TopPlaced`);
* `RelTopB`'s apartness: **`w0_ipcApart`**, **`w0_scApart`**;
* `JAtZ.ks` / `ip` / `rp` / `apart` / `nk` / `nodeB`: **`w0_ks`**, **`w0_ip`**, **`w0_rp`**, **`w0_apart`**,
  **`w0_nk`**, **`w0_nodeB`**;
* `JAtZ.jpl` / `cover` / `zH` / `hset` / `hscC` / `jcov` / `kern` / `zD`: **`heapOK_Hw`**, **`w0_jplaced`**,
  **`w0_jpl`**, **`w0_cover`**, **`w0_zH`**, **`w0_hset`**, **`w0_hscC`**, **`w0_jcov`**, **`w0_jkern`**,
  **`w0_zD`** (with **`lay_orig`**: no slot of `fInitASt` is original).

No sorry; no premises. New module; no existing statement changed.
-/
import Fl4Proofs.P3.JBootZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.JBoot
open fl4_core Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit Classical
open Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

set_option maxHeartbeats 1000000

/-- Case split on `Hw`'s objects (`Hw_pos`), the kind substituted. -/
macro "hwc" h:term : tactic =>
  `(tactic| (rcases Hw_pos $h with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ <;> cases e'))

/-- Case split on `thW`'s objects (`thW_pos`), the kind substituted. -/
macro "thc" h:term : tactic =>
  `(tactic| (rcases thW_pos $h with ⟨e, e'⟩ | ⟨e', ⟨i, hi, e⟩ | ⟨i, hi, hi2, e⟩⟩ <;> cases e'))

/-! ## The store's words -/

theorem curW_w0 : wL.curW w0 = idT := curT_w0
theorem idleW_w0 : wL.idleW w0 = idT := idleT_w0
theorem cscW_w0 : wL.cscW w0 = idS := curSc_w0
theorem idleScW_w0 : idleScW (L := wL) w0 = idS := idleSc_w0

theorem e2sc : (2 : Nat) ^ (0 + Fl4Spec.minSchedContextBits) = 128 := by decide

theorem dbg_val : layout.node.DEBUG_TCBS.val = 88 := by unfold layout.node.DEBUG_TCBS; rfl

theorem dbgA_v : (wL.nodeAt w0 0#u64 layout.node.DEBUG_TCBS).val = 18446744071562147072 + 88 := by
  rw [nodeAt_v _ (by rw [dbg_val]; omega), dbg_val]

theorem actA_v : (wL.nodeAt w0 (wL.cpu w0) layout.node.SCHED_ACTION).val = 18446744071562147072 + 16 := by
  rw [cpu_w0, nodeAt_v _ (by rw [act_val]; omega), act_val]

theorem atA_v (hi : U64) (h : hi.val < 2048) :
    (atA (wL.ksb w0) hi).val = 18446744071562133504 + 288000 + 8 * hi.val := by
  unfold atA; rw [ksb_w0]
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, fkb_val]
  omega

theorem stA_idT : (Fl4Proofs.P1.stA idT).val = 18446744071562072064 + 3328 := by
  rw [Fl4Proofs.P1.stA_eq]; exact (wa_val (a := idT) (b := 3328#u64) (by decide)).trans rfl

/-! ## `TopPlaced` -/

/-- The words of `OObj` at the witness. -/
theorem oobj_nat {a : U64} (h : Vs.OObj wst ∅ T0 C0 ∅ ∅ ∅ 0#u64 w0 fInitASt a) :
    (18446744071562147072 ≤ a.val ∧ a.val < 18446744071562147072 + 4288) ∨
    (18446744071562133504 ≤ a.val ∧ a.val < 18446744071562133504 + 13568 ∧
      (a.val < 18446744071562133504 + 1248 ∨ 18446744071562133504 + 5344 ≤ a.val)) ∨
    (18446744071562072064 + 256 ≤ a.val ∧ a.val < 18446744071562072064 + 4096) ∨
    (18446744071562096640 ≤ a.val ∧ a.val < 18446744071562096640 + 128) := by
  unfold Vs.OObj at h
  rw [nodeBase_w0, ksb_w0, fkb_val] at h
  rcases h with h | h | ⟨t, ht, h⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ | ⟨sc, hsc, x, n, hk, h⟩ | ⟨wp, hwp, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [T0, Set.mem_singleton_iff] at ht; subst ht; rw [idT_val] at h; exact Or.inr (Or.inr (Or.inl h))
  · simp at he
  · simp at hr
  · simp at hn
  · rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    rw [fInit_idleSc] at hk; cases hk
    unfold Sched.ScObj at h; rw [e2sc, idS_val] at h
    exact Or.inr (Or.inr (Or.inr h))
  · simp at hwp

/-- The words of `VObj` at the witness. -/
theorem vobj_nat {a : U64} (h : Vs.VObj thW ∅ ∅ ∅ ∅ ∅ (wL.ksb w0) a) :
    (18446744071562072064 ≤ a.val ∧ a.val < 18446744071562072064 + 192) ∨
    (18446744071562134752 ≤ a.val ∧ a.val < 18446744071562138848) ∨
    (18446744071562080256 ≤ a.val ∧ a.val < 18446744071562084352) ∨
    (18446744071562133504 + 288000 ≤ a.val ∧ a.val < 18446744071562133504 + 288000 + 16384) := by
  unfold Vs.VObj at h
  rw [ksb_w0, fkb_val] at h
  rcases h with ⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, -⟩ | h
  · rcases thW_pos hq with ⟨-, e⟩ | ⟨e, ⟨i, hi, e1⟩ | ⟨i, hi, hi2, e1⟩⟩
    · cases e
    · cases e; rw [Nat.pow_zero] at h2; omega
    · cases e; rw [Nat.pow_zero] at h2; omega
  · rcases thW_pos ht with ⟨e1, -⟩ | ⟨e, -⟩
    · omega
    · cases e
  · simp at hq
  · exact Or.inr (Or.inr (Or.inr h))

/-- A slot of `thW` lies in a slot range (its first and last byte). -/
theorem slot_ends {x : U64} (h : IsSlot thW x) : SlotNat x.val ∧ SlotNat (x.val + 31) := by
  have h0 := slot_nat h 0 (by omega)
  rw [Nat.add_zero] at h0
  exact ⟨h0, slot_nat h 31 (by omega)⟩

/-- **`TopPlaced` at the witness.** -/
theorem w0_topPlaced : Vs.TopPlaced wst thW ∅ ∅ ∅ ∅ ∅ ∅ T0 C0 ∅ ∅ ∅ 0#u64 w0 fInitASt where
  ep := ⟨tcbPlaced_T0, fun e he => by simp at he, fun r hr => by simp at hr, fun e he => by simp at he,
    fun r hr => by simp at hr, fun e he => by simp at he, fun w hw => by simp at hw, fun w hw => by simp at hw,
    fun w hw => by simp at hw, fun w hw => by simp at hw, fun w hw => by simp at hw⟩
  vs := ⟨by rw [ksb_w0, fkb_val], by rw [ksb_w0, fkb_val]; omega, fun p hp => by simp at hp,
    fun p hp => by simp at hp⟩
  pt := fun p hp => by simp at hp
  pl := placed_thW
  disj a hO hV := by
    have h1 := oobj_nat hO
    have h2 := vobj_nat hV
    omega
  nodeE a h1 h2 hE := by
    rw [nodeBase_w0] at h1 h2
    unfold Endp.EFoot at hE
    rcases hE with ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨t, ht, h⟩ | ⟨wp, hwp, -⟩
    · simp at he
    · simp at hr
    · rw [T0, Set.mem_singleton_iff] at ht; subst ht
      unfold Endp.TF Endp.TOffN Endp.TL at h; rw [idT_val] at h; omega
    · simp at hwp
  po b hb := by obtain ⟨p, hp, -⟩ := hb; simp at hp
  ps b hb := by obtain ⟨p, hp, -⟩ := hb; simp at hp
  pv b hb := by obtain ⟨p, hp, -⟩ := hb; simp at hp
  vo b hb := by
    rcases hb with ⟨hi, hhi, rfl⟩ | ⟨p, hp, -⟩
    · have hv := atA_v hi hhi
      refine ⟨by show (atA _ hi).val % 8 = 0; omega, fun p k hp hin => ?_⟩
      rw [hv] at hin
      thc hp <;> simp only [objSize, Nat.pow_zero, Nat.mul_one] at hin <;> omega
    · simp at hp
  sd b hb hS := by
    obtain ⟨x, hx, hb'⟩ := hS
    have hx0 := slot_nat hx 0 (by omega)
    have hx8 := slot_nat hx 8 (by omega)
    unfold SlotNat at hx0 hx8
    have hbv : b.val = x.val ∨ b.val = x.val + 8 := by
      rcases hb' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (wordOf_val (k := 8#u64) (by show x.val + 8 < 2 ^ 64; omega))
    rcases hb with ⟨hi, hhi, rfl⟩ | ⟨p, hp, -⟩
    · have hv := atA_v hi hhi
      omega
    · simp at hp
  tko t ht := by
    rcases thW_pos ht with ⟨e, -⟩ | ⟨e, -⟩
    · left; rw [ksb_w0, fkb_val]; omega
    · cases e

/-! ## The IPC and SC apartness -/

theorem w0_ipcApart : Ipc.IpcApart thW ∅ T0 ∅ ∅ ∅ (wL.ksb w0) 0#u64 where
  slot a ha x hx hin := by
    obtain ⟨h0, h31⟩ := slot_ends hx
    unfold SlotNat at h0 h31
    unfold Ipc.IWords at ha
    rcases ha with ⟨t, ht, h⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ | ⟨wp, hwp, -⟩
    · rw [T0, Set.mem_singleton_iff] at ht; subst ht; rw [idT_val] at h; omega
    · simp at he
    · simp at hr
    · simp at hn
    · simp at hwp
  node a h1 h2 x hx hin := by
    obtain ⟨h0, h31⟩ := slot_ends hx
    unfold SlotNat at h0 h31
    have z : (0#u64).val = 0 := rfl
    rw [ksb_w0, fkb_val, z] at h1 h2
    omega
  dom a ha := by
    rw [ksb_w0, fkb_val]
    unfold Ipc.IWords at ha
    rcases ha with ⟨t, ht, h⟩ | ⟨e, he, -⟩ | ⟨r, hr, -⟩ | ⟨n, hn, -⟩ | ⟨wp, hwp, -⟩
    · rw [T0, Set.mem_singleton_iff] at ht; subst ht; rw [idT_val] at h; omega
    · simp at he
    · simp at hr
    · simp at hn
    · simp at hwp
  ks a h1 h2 h3 x hx hin := by
    obtain ⟨h0, h31⟩ := slot_ends hx
    unfold SlotNat at h0 h31
    rw [ksb_w0, fkb_val] at h1 h2 h3
    omega
  kfit := fkb_lt
  kal := by rw [ksb_w0, fkb_val]

theorem w0_scApart : Ipc.ScApart thW C0 fInitASt := by
  intro sc hsc x n hk a ha y hy hin
  rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
  rw [fInit_idleSc] at hk; cases hk
  unfold Sched.ScObj at ha; rw [e2sc, idS_val] at ha
  obtain ⟨h0, h31⟩ := slot_ends hy
  unfold SlotNat at h0 h31
  omega

/-! ## The sets' placement -/

theorem w0_ks : KsApart ∅ T0 ∅ ∅ ∅ (wL.ksb w0) :=
  ⟨fun e he => by simp at he, fun r hr => by simp at hr, fun n hn => by simp at hn, fun w hw => by simp at hw⟩

theorem w0_ePlaced : Endp.EPlaced T0 ∅ ∅ ∅ :=
  ⟨tcbPlaced_T0, fun e he => by simp at he, fun r hr => by simp at hr, fun e he => by simp at he,
    fun r hr => by simp at hr, fun e he => by simp at he, fun w hw => by simp at hw, fun w hw => by simp at hw,
    fun w hw => by simp at hw, fun w hw => by simp at hw, fun w hw => by simp at hw⟩

theorem w0_ip : Ipc.IPlaced ∅ T0 ∅ ∅ ∅ :=
  ⟨⟨tcbPlaced_T0, fun n hn => by simp at hn, fun n hn => by simp at hn⟩, w0_ePlaced,
    fun n hn => by simp at hn, fun n hn => by simp at hn, fun n hn => by simp at hn⟩

theorem w0_rp : Sched.RPlaced wst ∅ T0 C0 ∅ 0#u64 w0 fInitASt :=
  ⟨fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr, fun r hr => by simp at hr,
    fun r hr => by simp at hr⟩

theorem w0_apart : Sched.SlotsApart (st := wst) thW T0 ∅ C0 ∅ 0#u64 w0 fInitASt := by
  intro a ha
  obtain ⟨h0, h31⟩ := slot_ends ha
  unfold SlotNat at h0 h31
  refine ⟨fun t ht => ?_, ?_, fun n hn => by simp at hn, fun sc hsc x n hk => ?_, fun r hr => by simp at hr⟩
  · rw [T0, Set.mem_singleton_iff] at ht; subst ht; rw [idT_val]; omega
  · rw [nodeBase_w0]; omega
  · rw [C0, Set.mem_singleton_iff] at hsc; subst hsc
    rw [fInit_idleSc] at hk; cases hk
    rw [e2sc, idS_val]; omega

theorem w0_nk : ∀ n ∈ (∅ : Set U64), n.val + 40 ≤ (wL.ksb w0).val ∨ (wL.ksb w0).val + 13568 ≤ n.val :=
  fun n hn => by simp at hn

theorem w0_nodeB : ∀ wp ∈ (∅ : Set (U64 × Fl4Spec.Word)), ∀ c : U64, c.val < 64 →
    wp.1.val + 8 ≤ wL.nodeBase w0 c ∨ wL.nodeBase w0 c + 4288 ≤ wp.1.val :=
  fun wp hw => by simp at hw

/-! ## P1's heap -/

theorem Hw_hi {p : U64} (h : 18446744071562080256 ≤ p.val ∧ p.val < 18446744071562084352 ∧ p.val % 32 = 0) :
    Hw p = some (.other 5) := by
  have n1 : p ≠ idT := fun e => by rw [e, idT_val] at h; omega
  have n2 : p ≠ idS := fun e => by rw [e, idS_val] at h; omega
  unfold Hw
  rw [if_neg n1, if_neg n2, if_neg (by omega), if_pos h]

theorem Hw_arch {p : U64}
    (h : p.val = 18446744071562084352 ∨ p.val = 18446744071562088448 ∨ p.val = 18446744071562092544) :
    Hw p = some (.other 12) := by
  have n1 : p ≠ idT := fun e => by rw [e, idT_val] at h; omega
  have n2 : p ≠ idS := fun e => by rw [e, idS_val] at h; omega
  unfold Hw
  rw [if_neg n1, if_neg n2, if_pos h]

theorem Hw_lo {p : U64} (h : fkb.val + 1248 ≤ p.val ∧ p.val < fkb.val + 5344 ∧ (p.val - fkb.val) % 32 = 0) :
    Hw p = some (.other 5) := by
  have hf := fkb_val
  have n1 : p ≠ idT := fun e => by rw [e, idT_val] at h; omega
  have n2 : p ≠ idS := fun e => by rw [e, idS_val] at h; omega
  unfold Hw
  rw [if_neg n1, if_neg n2, if_neg (by omega), if_neg (by omega)]
  unfold ksH; rw [if_pos h]

theorem Hw_zero : Hw 0#u64 = none := by
  have z : (0#u64).val = 0 := rfl
  cases h : Hw 0#u64 with
  | none => rfl
  | some k => exfalso; hwc h <;> omega

/-- **`Hw` is well formed.** -/
theorem heapOK_Hw : HeapOK Hw where
  align p k hp := by hwc hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  fits p k hp := by hwc hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  lt64 p k hp := by hwc hp <;> simp [HKind.bits]
  scmin p z hp := by hwc hp; omega
  disj p k q k' hp hq hne := by
    have hv : p.val ≠ q.val := fun e => hne (UScalar.eq_of_val_eq e)
    rcases Hw_pos hp with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ <;> cases e' <;>
    rcases Hw_pos hq with ⟨f, f'⟩ | ⟨f, f'⟩ | ⟨f', f⟩ | ⟨f', f⟩ | ⟨f', f⟩ | ⟨f', f⟩ <;> cases f' <;>
      simp only [HKind.bits, Nat.reducePow] <;> omega

theorem capTyped_null : CapTyped Hw (Heap.replies Hw) (Heap.ntfns Hw) .Null := by
  unfold CapTyped
  refine ⟨fun _ _ _ _ _ _ h => ?_, fun _ _ _ _ h => ?_, fun _ _ h => ?_⟩ <;> cases h

/-- **`JPlaced` at the witness** (`Tr = T0`, `C = C0`). -/
theorem w0_jplaced : Sched.JPlaced (L := wL) thW Hw T0 C0 w0 fInitASt where
  heap := heapOK_Hw
  pl := placed_thW
  tcb t := by
    constructor
    · intro h
      rcases thW_some h with ⟨rfl, -⟩ | ⟨_, _, e⟩
      · exact Hw_idT
      · cases e
    · intro h
      rcases Hw_pos h with ⟨e, -⟩ | ⟨-, e'⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩ | ⟨e', -⟩
      · rw [show t = idT from UScalar.eq_of_val_eq (by rw [e, idT_val])]; exact thW_idT
      all_goals cases e'
  cnode p r h := by
    rcases thW_pos h with ⟨-, e⟩ | ⟨e, ⟨i, hi, hv⟩ | ⟨i, hi, hi2, hv⟩⟩
    · cases e
    · cases e; exact Hw_lo (by rw [fkb_val]; omega)
    · cases e; exact Hw_hi (by omega)
  tr := thT_thW
  sc c y n _ hk := by
    obtain ⟨e, -, rfl⟩ := bootHeap_fInit.sc_of hk
    have : c = idS := Fl4Proofs.P1.eq_of_bv (by rw [e, idS_bv])
    subst this
    exact ⟨rfl, Hw_idS⟩
  ks p k hp hk := by
    rw [ksb_w0, fkb_val]
    rcases Hw_pos hp with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ <;> cases e' <;>
      first
      | exact absurd rfl (hk _)
      | (simp only [HKind.bits, Nat.reducePow]; omega)
  ksIn p z hp := by
    rw [ksb_w0, fkb_val]
    hwc hp <;> simp only [Nat.reducePow] <;> omega
  typed a ha := by rw [capV_slot ha]; exact capTyped_null
  irq i hi := by
    have hv := nodeA_val (kb := fkb) fkb_lt hi
    rw [fkb_val] at hv
    have e8 : (8#u64).val = 8 := rfl
    have c : capV (wL.mem w0) (nodeA fkb i) = .Null :=
      capV_zero (mem_slot (a := nodeA fkb i) (by unfold SlotNat; omega))
        (mem_slot (a := wordOf (nodeA fkb i) 8#u64) (by rw [wordOf_val (by omega), e8]; unfold SlotNat; omega))
    rw [ksb_w0, c]
    exact capTyped_null
  fh t ht := by
    have h : AbsSlot thW (t.bv, Fl4Spec.tcbCnodeIndex 3) := by
      unfold AbsSlot; exact ⟨t, rfl, Or.inr ⟨ht, 3, by decide, rfl⟩⟩
    exact Or.inl (capV_slot (AbsSlot.isSlot h))
  bfs t ht := by
    have h : AbsSlot thW (t.bv, Fl4Spec.tcbCnodeIndex 2) := by
      unfold AbsSlot; exact ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
    exact Or.inl (capV_slot (AbsSlot.isSlot h))
  cobj a ha := by rw [capV_slot ha]; trivial

theorem w0_jpl : ∃ Tr Cq, Sched.JPlaced (L := wL) thW Hw Tr Cq w0 fInitASt := ⟨T0, C0, w0_jplaced⟩

/-- The witness's spec arch objects are the three global tables. -/
theorem fInitKheap_arch {o : ObjRef} {ao} (h : fInitKheap o = some (.archObj ao)) :
    o = initGlobalPd ∨ o = initGlobalPdpt ∨ o = initGlobalPml4 := by
  unfold fInitKheap at h
  simp only [Function.update_apply] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h3)
  · rw [initKheap_idleS] at h; cases h
  · rw [initKheap_idleT] at h; cases h
  · cases h

/-- **`SpecCover` at the witness.** -/
theorem w0_cover : Sched.SpecCover Hw fInitASt where
  ntfn o x h := (bootHeap_fInit.no_ntfn h).elim
  ep o x h := (bootHeap_fInit.no_ep h).elim
  reply o x h := by
    change fInitKheap o = _ at h
    rcases bootHeap_fInit.obj _ _ h with rfl | rfl | e | e | e | e
    · rw [bootHeap_fInit.tcb] at h; cases h
    · rw [bootHeap_fInit.sc] at h; cases h
    all_goals cases e
  sc0 y k h := by
    have h' : fInitKheap (0#u64 : U64).bv = some (.schedContext y k) := h
    obtain ⟨e, -⟩ := bootHeap_fInit.sc_of h'
    exact absurd e (by decide)
  arch o ao h := by
    refine ⟨12, le_refl _, Hw_arch ?_⟩
    rcases fInitKheap_arch h with rfl | rfl | rfl
    · exact Or.inr (Or.inr (by decide))
    · exact Or.inr (Or.inl (by decide))
    · exact Or.inl (by decide)

theorem w0_zH : (∀ t ∈ T0, Hw t = some .tcb) ∧ (∀ e ∈ (∅ : Set U64), Hw e = some .ep) ∧
    (∀ r ∈ (∅ : Set U64), Hw r = some .reply) ∧ (∀ n ∈ (∅ : Set U64), Hw n = some .ntfn) :=
  ⟨fun t ht => by rw [T0, Set.mem_singleton_iff] at ht; subst ht; exact Hw_idT,
    fun e he => by simp at he, fun r hr => by simp at hr, fun n hn => by simp at hn⟩

theorem w0_hset : (∀ e, Hw e = some .ep → e ∈ (∅ : Set U64)) ∧ (∀ n, Hw n = some .ntfn → n ∈ (∅ : Set U64)) ∧
    (∀ r, Hw r = some .reply → r ∈ (∅ : Set U64)) :=
  ⟨fun e h => by hwc h, fun n h => by hwc h, fun r h => by hwc h⟩

theorem w0_hscC : ∀ c z, Hw c = some (.sc z) → c ∈ C0 := by
  intro c z h
  rcases Hw_pos h with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩ | ⟨e', e⟩
  · cases e'
  · rw [show c = idS from UScalar.eq_of_val_eq (by rw [e, idS_val])]; rfl
  all_goals cases e'

/-! ## The cover and the dead set -/

/-- An object at a word of the kernel-state block lies inside it (`KsObj`). -/
theorem ksObj_blk {q : U64} (h1 : 18446744071562133504 ≤ q.val) (h2 : q.val < 18446744071562133504 + 13568) :
    KsObj (L := wL) thW Hw w0 q := by
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩ <;> unfold KsIn <;> rw [ksb_w0, fkb_val]
  · thc hk <;>
      simp only [objSize, Nat.pow_zero, Nat.mul_one, show max 32 1 = 32 by decide,
        show max 4096 1 = 4096 by decide] <;> omega
  · hwc hk <;> simp only [HKind.bits, Nat.reducePow] <;> omega

theorem Hw_D {q : U64} (hq : q ∈ Dw) : Hw q = some (.other 12) ∨ Hw q = some (.other 5) := by
  simp only [Dw, Set.mem_ofPred_eq] at hq
  rcases hq with h | h
  · exact Or.inr (Hw_hi h)
  · exact Or.inl (Hw_arch h)

/-- **`JCovD` at the witness**: the idle objects exempt (`IdleAt`), the kernel-state block's objects exempt
(`KsObj`), the IRQ CNodes 128..255 and the global tables dead (`Dw`). -/
theorem w0_jcov : Sched.JCovD (L := wL) thW Hw Gw Dw Csw w0 where
  th q k hq := by
    rcases thW_pos hq with ⟨e, -⟩ | ⟨-, ⟨i, hi, e⟩ | ⟨i, hi, hi2, e⟩⟩
    · have : q = idT := UScalar.eq_of_val_eq (by rw [e, idT_val])
      subst this
      exact Or.inr (Or.inr (Or.inl (Or.inl idleW_w0.symm)))
    · exact Or.inr (Or.inr (Or.inr (ksObj_blk (by omega) (by omega))))
    · exact Or.inr (Or.inl (Or.inl ⟨by omega, by omega, by omega⟩))
  h q k hq := by
    rcases Hw_pos hq with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩
    · have : q = idT := UScalar.eq_of_val_eq (by rw [e, idT_val])
      subst this
      exact Or.inr (Or.inr (Or.inl (Or.inl idleW_w0.symm)))
    · have : q = idS := UScalar.eq_of_val_eq (by rw [e, idS_val])
      subst this
      exact Or.inr (Or.inr (Or.inl (Or.inr idleScW_w0.symm)))
    · exact Or.inr (Or.inl (Or.inr e))
    · exact Or.inr (Or.inl (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (ksObj_blk (by omega) (by omega))))
    · exact Or.inr (Or.inr (Or.inr (ksObj_blk (by omega) (by omega))))
  dead q hq := by
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun z h => ?_⟩ <;>
      rcases Hw_D hq with e | e <;> rw [e] at h <;> cases h
  ks x hx := by simp [Gw] at hx
  idleOut x hx := by simp [Gw] at hx
  dx q hq h := by rcases Hw_D hq with e | e <;> rw [e] at h <;> cases h

/-! ## `JKern` -/

/-- **No slot of the witness's spec state is original** (`initIoc`: `initKheap` holds only null caps). -/
theorem lay_orig (sl : CslotPtr) : fInitASt.isOriginalCap sl = false := by
  obtain ⟨a, b⟩ := sl
  show initIoc (a, b) = false
  unfold initIoc
  apply decide_eq_false
  rintro ⟨obj, hk, cap, hc, hne⟩
  apply hne
  rcases bootHeap_init.obj _ _ hk with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [initKheap_idleT] at hk; cases hk
    simp only [Fl4Spec.capOf, idleTcbV, tcbCnodeMap, Function.update_apply] at hc
    split_ifs at hc <;> (cases hc; rfl)
  · rw [initKheap_idleS] at hk; cases hk; simp [Fl4Spec.capOf] at hc
  · simp only [Fl4Spec.capOf, emptyCnode] at hc; split_ifs at hc; cases hc; rfl
  all_goals simp [Fl4Spec.capOf] at hc

/-- **`JKern` at the witness.** -/
theorem w0_jkern : JKern (L := wL) warI Hw Csw Dw thW w0 fInitASt where
  orig sl h := by rw [lay_orig] at h; cases h
  cur := by rw [curW_w0, idT_bv]; rfl
  curT := by rw [curW_w0]; exact thW_idT
  act := by
    have hv := actA_v
    refine ⟨by show (wL.nodeAt w0 (wL.cpu w0) layout.node.SCHED_ACTION).val % 8 = 0; omega,
      fun p k hp hin => ?_⟩
    rw [hv] at hin
    thc hp <;> simp only [objSize, Nat.pow_zero, Nat.mul_one] at hin <;> omega
  dwAl := by have := dbgA_v; show (wL.nodeAt w0 0#u64 layout.node.DEBUG_TCBS).val % 8 = 0; omega
  dwObj a ha hin := by
    have hv := dbgA_v
    obtain ⟨h0, h31⟩ := slot_ends ha
    unfold SlotNat at h0 h31
    omega
  dwNe := by
    rw [dbgA_v, curW_w0, stA_idT, actA_v]
    omega
  head := Or.inl (by rw [mem_al dbgA_v (by omega)]; img0)
  gpm := ⟨_, bootHeap_fInit.pml4⟩
  ga := fInit_gpm_al.1
  gf := fInit_gpm_al.2
  heap := heapOK_Hw
  h0 := Hw_zero
  hks := w0_jplaced.ks
  hksIn := w0_jplaced.ksIn
  hnd p k hp c hc := by
    rw [Csw, Set.mem_singleton_iff] at hc; subst hc
    rw [nodeBase_w0]
    hwc hp <;> simp only [HKind.bits, Nat.reducePow] <;> omega
  ksbFit := w0_jkernNum.1
  ksbAl := w0_jkernNum.2.1
  nodeFit := w0_jkernNum.2.2.1
  cpuCs := w0_jkernNum.2.2.2.1
  curH := by rw [curW_w0]; exact Hw_idT
  cscH := by rw [cscW_w0, Hw_idS]; exact Option.some_ne_none _
  csLt := w0_jkernNum.2.2.2.2.1
  cs0 := w0_jkernNum.2.2.2.2.2.1
  csN := w0_jkernNum.2.2.2.2.2.2
  tdx := w0_tdx

/-- **`JAtZ.zD` at the witness**: no slot holds a zombie. -/
theorem w0_zD : ∀ p ∈ ZTcb (L := wL) thW w0, p ∈ Dw := by
  intro p hp
  obtain ⟨y, hy, zt, n, hc, -⟩ := hp
  rw [capV_slot hy] at hc; cases hc

end

end Fl4Proofs.P3.JBoot
