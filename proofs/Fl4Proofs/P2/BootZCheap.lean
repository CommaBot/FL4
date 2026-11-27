/-
# P2 (line p3mc, gen 34): the cheap `JAtZ` fields at the boot state (handoff §38d, first group)

The ghost sets **`ZB G`** (`P2/BootMem`'s typed heap `thB`, the MDB ghost `G` left open, `T = {tiB}`,
`C = {sciB}`, every other set empty, core 0, `vx = ∅`) and the fields of P3's `JAtZ` that hold at
`(sB, σB)` for **every** MDB ghost `G` by placement / emptiness alone:

`thT`, `thk`, `ks`, `ip`, `nk`, `nodeB`, `cover`, `obj`, `zH`, `hset`, `hscC`, `nsc`, `c0`, `intL`, `ext`
(each `ZB_<field>`, stated with exactly `JAtZ`'s field type), plus `VxE (ZB G)` (instance) and the helpers
`kheapB_cases` (the five kinds of objects of `σB`), `wordB_zero` and `slot_null` (every slot of `thB` holds the null
cap in `memB`).

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootMem
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

/-- **The boot ghost sets** (module docstring), the MDB ghost `G` open. -/
def ZB (G : MdbGhost) : XSets :=
  ⟨thB, G, ∅, ∅, ∅, ∅, ∅, ∅, {tiB}, {sciB}, ∅, ∅, ∅, 0#u64, ∅⟩

instance (G : MdbGhost) : VxE (ZB G) := ⟨rfl⟩

theorem eq_of_val' {p q : U64} (h : p.val = q.val) : p = q := UScalar.eq_of_val_eq h

/-- The objects of `σB`: the idle TCB, the idle SC, the three paging structures, the IRQ CNodes (`irq < 128`). -/
theorem kheapB_cases {o : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject} (h : kheapB o = some ko) :
    (o = Fl4Spec.idleThreadPtr ∧ ∃ x, ko = .tcb x) ∨ (o = Fl4Spec.idleScPtr ∧ ∃ y n, ko = .schedContext y n) ∨
    ((o = Fl4Spec.initGlobalPml4 ∨ o = Fl4Spec.initGlobalPdpt ∨ o = Fl4Spec.initGlobalPd) ∧ ∃ a, ko = .archObj a) ∨
    ((∃ irq : Fl4Spec.Irq, irq.toNat < 128 ∧ irqNodeB + (Fl4Spec.ucast 64 irq <<< Fl4Spec.cteLevelBits) = o) ∧
      ko = .cnode 0 (Fl4Spec.emptyCnode 0)) := by
  unfold kheapB at h
  simp only [Function.update_apply] at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 <;> cases h
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inr h1), _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl h2), _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨Or.inl h3, _, rfl⟩))
  · exact Or.inr (Or.inl ⟨h4, _, _, rfl⟩)
  · exact Or.inl ⟨h5, _, rfl⟩
  · exact Or.inr (Or.inr (Or.inr ⟨h6, rfl⟩))

/-- `wordB` is 0 off its fifteen nonzero words. -/
theorem wordB_zero_of {n : Nat}
    (hs : n ≠ 18446744071562114304 ∧ n ≠ 18446744071562114312 ∧ n ≠ 18446744071562114328 ∧ n ≠ 18446744071562114336 ∧
    n ≠ 18446744071562100752 ∧ n ≠ 18446744071562100936 ∧ n ≠ 18446744071562100808 ∧ n ≠ 18446744071562100784 ∧
    n ≠ 18446744071562072064 + 3328 ∧ n ≠ 18446744071562072064 + 3464 ∧ n ≠ 18446744071562096640 + 24 ∧
    n ≠ 18446744071562096640 + 72 ∧ n ≠ 18446744071562096640 + 88 ∧ n ≠ 18446744071562096640 + 104 ∧
    n ≠ 18446744071562096640 + 112) :
    wordB n = 0#u64 := by
  unfold wordB
  rw [if_neg (show ¬ (n = 18446744071562114304 ∨ n = 18446744071562114312) by omega),
    if_neg (show ¬ (n = 18446744071562114328 ∨ n = 18446744071562114336) by omega),
    if_neg (show ¬ n = 18446744071562100752 by omega),
    if_neg (show ¬ n = 18446744071562100936 by omega),
    if_neg (show ¬ n = 18446744071562100808 by omega),
    if_neg (show ¬ n = 18446744071562100784 by omega),
    if_neg (show ¬ n = 18446744071562072064 + 3328 by omega),
    if_neg (show ¬ n = 18446744071562072064 + 3464 by omega),
    if_neg (show ¬ n = 18446744071562096640 + 24 by omega),
    if_neg (show ¬ n = 18446744071562096640 + 72 by omega),
    if_neg (show ¬ n = 18446744071562096640 + 88 by omega),
    if_neg (show ¬ (n = 18446744071562096640 + 104 ∨ n = 18446744071562096640 + 112) by omega)]

/-- `wordB` is 0 on the idle TCB's slots and the IRQ node. -/
theorem wordB_zero {n : Nat}
    (h : (18446744071562072064 ≤ n ∧ n < 18446744071562072064 + 200) ∨
      (18446744071562100736 + 1248 ≤ n ∧ n < 18446744071562100736 + 5344)) : wordB n = 0#u64 :=
  wordB_zero_of (by omega)

/-- **Every slot of `thB` holds the null cap in `sB`.** -/
theorem slot_null {y : U64} (hy : IsSlot thB y) : capV (bsL.mem sB) y = .Null := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  have hv : (slotOf p i).val = p.val + 32 * i ∧ p.val % 8 = 0 ∧
      ((18446744071562072064 ≤ p.val + 32 * i ∧ p.val + 32 * i + 16 ≤ 18446744071562072064 + 200) ∨
      (18446744071562100736 + 1248 ≤ p.val + 32 * i ∧ p.val + 32 * i + 16 ≤ 18446744071562100736 + 5344)) := by
    rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
    · rcases thB_cases hp with ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
      · cases e
      · cases e
        simp only [Nat.pow_zero] at hir
        exact ⟨slotOf_val (by omega), by omega, Or.inr ⟨by omega, by omega⟩⟩
    · rcases thB_cases hp with ⟨e, -⟩ | ⟨e, -⟩
      · simp only [tcbSlots] at hit
        exact ⟨slotOf_val (by omega), by omega, Or.inl ⟨by omega, by omega⟩⟩
      · cases e
  obtain ⟨hv, h8, hr⟩ := hv
  have hw : (wordOf (slotOf p i) 8#u64).val = p.val + 32 * i + 8 := by
    show (core.num.U64.wrapping_add (slotOf p i) 8#u64).val = _
    simp only [core.num.U64.wrapping_add_val_eq, hv]; simp [U64.size, U64.numBits]; omega
  have h0 : bsL.mem sB (slotOf p i) = 0#u64 := by
    rw [memB_mem (by show _ % 8 = 0; rw [hv]; omega), hv]; exact wordB_zero (by omega)
  have h1 : bsL.mem sB (wordOf (slotOf p i) 8#u64) = 0#u64 := by
    rw [memB_mem (by show _ % 8 = 0; rw [hw]; omega), hw]; exact wordB_zero (by omega)
  unfold capV; rw [h0, h1]; rfl

variable (G : MdbGhost)

theorem ZB_thT : ∀ t, (ZB G).th t = some .tcb → t ∈ (ZB G).T := by
  intro t ht
  rcases thB_cases ht with ⟨e, -⟩ | ⟨e, -⟩
  · show t = tiB; exact eq_of_val' (by rw [e, tiB_val])
  · cases e

theorem ZB_thk : ∀ q k, (ZB G).th q = some k → k = .tcb ∨ ∃ r, k = .cnode r := by
  intro q k hq
  rcases thB_cases hq with ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨0, rfl⟩

theorem ZB_ks : KsApart (ZB G).N (ZB G).T (ZB G).E (ZB G).R (ZB G).B (bsL.ksb sB) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem tiB_addr : TcbAddr tiB := ⟨by rw [tiB_val]; omega, by rw [tiB_val]; norm_num, by rw [tiB_val]; norm_num⟩

theorem tcbPlaced_B : TcbPlaced (ZB G).T := fun t ht => by
  have : t = tiB := ht
  subst this; exact tiB_addr

theorem ZB_ip : Ipc.IPlaced (ZB G).N (ZB G).T (ZB G).E (ZB G).R (ZB G).B :=
  ⟨⟨tcbPlaced_B G, fun _ h => h.elim, fun _ h => h.elim⟩,
    ⟨tcbPlaced_B G, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
      fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
      fun _ h => h.elim⟩,
    fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem ZB_nk : ∀ n ∈ (ZB G).N, n.val + 40 ≤ (bsL.ksb sB).val ∨ (bsL.ksb sB).val + 13568 ≤ n.val :=
  fun _ h => h.elim

theorem ZB_nodeB : ∀ wp ∈ (ZB G).B, ∀ c : U64, c.val < 64 →
    wp.1.val + 8 ≤ bsL.nodeBase sB c ∨ bsL.nodeBase sB c + 4288 ≤ wp.1.val := fun _ h => h.elim

theorem ZB_cover : Sched.SpecCover HB (σB (Z := Unit)) where
  ntfn o x h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  ep o x h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  reply o x h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  sc0 y k h := by
    rcases kheapB_cases (o := (0#u64 : U64).bv) h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨⟨irq, hi, e⟩, -⟩
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · rcases e with e | e | e <;> exact absurd e (by decide)
    · have := σB_node_val irq
      have h0 : ((0#u64 : U64).bv).toNat = 0 := rfl
      change (σB (Z := Unit)).interruptIrqNode irq = (0#u64 : U64).bv at e
      rw [e, h0, kbB_val] at this; omega
  arch o ao h := by
    refine ⟨12, le_refl _, ?_⟩
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨e, -⟩ | ⟨-, e⟩
    · cases e
    · cases e
    · have hv : (⟨o⟩ : U64).val = 18446744071562084352 ∨ (⟨o⟩ : U64).val = 18446744071562088448 ∨
          (⟨o⟩ : U64).val = 18446744071562092544 := by
        show o.toNat = _ ∨ o.toNat = _ ∨ o.toNat = _
        rcases e with rfl | rfl | rfl
        · left; decide
        · right; left; decide
        · right; right; decide
      unfold HB
      rw [if_neg (by omega), if_neg (by omega), if_pos hv]
    · cases e

theorem ZB_obj : Sched.ObjCover (ZB G).N (ZB G).T (ZB G).E (ZB G).R (ZB G).C (σB (Z := Unit)) where
  tcb o x h := by
    rcases kheapB_cases h with ⟨e, -⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
    · exact ⟨tiB, rfl, by rw [tiB_bv, e]⟩
    all_goals cases e
  ntfn o x h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  ep o x h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  reply o x h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  sc o y k h := by
    rcases kheapB_cases h with ⟨-, _, e⟩ | ⟨e, -⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
    · cases e
    · exact ⟨sciB, rfl, by rw [sciB_bv, e]⟩
    · cases e
    · cases e

theorem ZB_zH : (∀ t ∈ (ZB G).T, HB t = some .tcb) ∧ (∀ e ∈ (ZB G).E, HB e = some .ep) ∧
    (∀ r ∈ (ZB G).R, HB r = some .reply) ∧ (∀ n ∈ (ZB G).N, HB n = some .ntfn) :=
  ⟨fun t ht => by rw [show t = tiB from ht]; exact HB_ti, fun _ h => h.elim, fun _ h => h.elim,
    fun _ h => h.elim⟩

theorem ZB_hset : (∀ e, HB e = some .ep → e ∈ (ZB G).E) ∧ (∀ n, HB n = some .ntfn → n ∈ (ZB G).N) ∧
    (∀ r, HB r = some .reply → r ∈ (ZB G).R) := by
  refine ⟨fun e h => ?_, fun e h => ?_, fun e h => ?_⟩ <;>
    rcases HB_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k

theorem ZB_hscC : ∀ c z, HB c = some (.sc z) → c ∈ (ZB G).C := by
  intro c z h
  rcases HB_cases h with ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
  · cases k
  · show c = sciB; exact eq_of_val' (by rw [e, sciB_val])
  all_goals cases k

theorem ZB_nsc : Sched.NSC (ZB G).N (ZB G).C (σB (Z := Unit)) := fun _ h => h.elim

theorem ZB_c0 : ∀ q ∈ (ZB G).C, q ≠ 0#u64 := by
  intro q hq e
  have : q = sciB := hq
  rw [this] at e
  have := congrArg UScalar.val e
  rw [sciB_val] at this; exact absurd this (by decide)

theorem ZB_intL : IntLayout (ZB G).th (bsL.ksb sB) where
  fit := by rw [sB_ksb]; exact kbB_fit'
  align := by rw [sB_ksb]; exact kbB_al
  st_out i hi := by
    rw [sB_ksb]
    have hv := irqStA_val (kb := kbB) kbB_fit' hi
    rw [kbB_val] at hv
    refine ⟨by show _ % 8 = 0; rw [hv]; omega, fun p k hp ⟨h1, h2⟩ => ?_⟩
    rw [hv] at h1 h2
    rcases thB_in hp h1 h2 with h | h <;> omega
  node i hi := by
    rw [sB_ksb]
    have hv := nodeA_val (kb := kbB) kbB_fit' hi
    rw [kbB_val] at hv
    show thB (nodeA kbB i) = _
    unfold thB
    rw [if_neg (by omega), if_pos (by omega)]

theorem ZB_ext : JExt (L := bsL) (ZB G).th sB where
  nat y hy := by rw [slot_null hy]; trivial
  vw t ht := by
    have e : t = tiB := ZB_thT G t ht
    subst e
    have hv : (tVcpuA tiB).val = 18446744071562072064 + 3664 := by
      unfold tVcpuA; simp only [core.num.U64.wrapping_add_val_eq, tiB_val]; simp [U64.size, U64.numBits]
    rw [memB_mem (by show _ % 8 = 0; rw [hv]), hv]
    exact wordB_zero_of (by omega)

end

end Fl4Proofs.P2.BootSt
