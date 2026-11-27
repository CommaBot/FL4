/-
# P2 (line p3mc, gen 39): the ghosts at the second boot start and the cheap `JAtZ` fields there

The ghosts for `JAtZ … sR … σR` (P2/BootRSpec, P2/BootRMem):

* **`GR`**: the MDB ghost: two chains `[tRw]`, `[tmoW]` (the two non-null caps, both original), no parent;
* **`ZR`**: typed heap `thR`, MDB ghost `GR`, `T = {tiB, tRw}`, `C = {sciB, scRw}`, every other set empty, core 0,
  `vx = ∅`; **`AcR = {sciB, scRw}`** (the active SCs), `LstB` (no call stack), `DB`, `CsB` (gen 35 / 34, unchanged).

Proved (as gen 34's `P2/BootZCheap` at `σB`): the slot facts **`slotR_cases`** (every slot of `thR` is the root slot
`tRw`, holding `Thread tRw`, or holds four zero words: null cap, links 0, not revocable), `memR_at`, and the fields
`thT`, `thk`, `ks`, `ip`, `nk`, `nodeB`, `cover`, `obj`, `zH`, `hset`, `hscC`, `nsc`, `c0`, `intL`, `ext`
(`ZR_<field>`, each with exactly `JAtZ`'s field type), `VxE ZR`.

No premise. No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.BootRSpecS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

/-! ## The ghosts -/

/-- The MDB ghost at the second boot start: the root slot and the timeout-handler slot, two one-slot chains. -/
def GR : MdbGhost := ⟨[[tRw], [tmoW]], fun _ => none⟩

/-- **The ghost sets at the second boot start** (module docstring). -/
def ZR : XSets :=
  ⟨thR, GR, ∅, ∅, ∅, ∅, ∅, ∅, {tiB, tRw}, {sciB, scRw}, ∅, ∅, ∅, 0#u64, ∅⟩

instance : VxE ZR := ⟨rfl⟩

/-- The active SCs at the second boot start. -/
def AcR : Set U64 := {sciB, scRw}

/-! ## Words -/

/-- A word of `sR` by its address as a number. -/
theorem memR_at {a : U64} {n : Nat} (hv : a.val = n) (h8 : n % 8 = 0) : bsL.mem sR a = wordR n := by
  rw [memR_mem (by show a.val % 8 = 0; rw [hv]; exact h8), hv]

/-- `wordR` is 0 on the idle TCB's slots, the root TCB's slots but the root slot's two words, and the IRQ node. -/
theorem wordR_zero {n : Nat}
    (h : (18446744071562072064 ≤ n ∧ n < 18446744071562072064 + 200) ∨
      (18446744071562076160 + 8 ≤ n ∧ n < 18446744071562076160 + 200 ∧ n ≠ 18446744071562076160 + 24 ∧
        n ≠ 18446744071562076160 + 128 ∧ n ≠ 18446744071562076160 + 152) ∨
      (18446744071562100736 + 1248 ≤ n ∧ n < 18446744071562100736 + 5344)) : wordR n = 0#u64 :=
  wordR_zero_of (by omega)

theorem eq_of_val'' {p q : U64} (h : p.val = q.val) : p = q := UScalar.eq_of_val_eq h

/-- **The slots of `thR`**: the root slot `tRw` (cap `Thread tRw`, revocable, links 0), the timeout-handler slot
`tmoW` (cap `SchedContext scRw 7`, revocable, links 0), or four zero words (the null cap, links 0, not
revocable, not first-badged). -/
theorem slotR_cases {y : U64} (hy : IsSlot thR y) :
    y = tRw ∨ y = tmoW ∨ (capV (bsL.mem sR) y = .Null ∧ prevOf (bsL.mem sR) y = 0#u64 ∧ nextOf (bsL.mem sR) y = 0#u64 ∧
      revOf (bsL.mem sR) y = false ∧ fbOf (bsL.mem sR) y = false) := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  have hv : (slotOf p i).val = p.val + 32 * i ∧ p.val % 8 = 0 ∧
      ((18446744071562072064 ≤ p.val + 32 * i ∧ p.val + 32 * i + 32 ≤ 18446744071562072064 + 200) ∨
      (p.val = 18446744071562076160 ∧ i < 6) ∨
      (18446744071562100736 + 1248 ≤ p.val + 32 * i ∧ p.val + 32 * i + 32 ≤ 18446744071562100736 + 5344)) := by
    rcases hi with ⟨r, hp, hir⟩ | ⟨hp, hit⟩
    · rcases thR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨e, g1, g2, g3⟩
      · cases e
      · cases e
      · cases e
        simp only [Nat.pow_zero] at hir
        exact ⟨slotOf_val (by omega), by omega, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
    · rcases thR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
      · simp only [tcbSlots] at hit
        exact ⟨slotOf_val (by omega), by omega, Or.inr (Or.inl ⟨e, hit⟩)⟩
      · simp only [tcbSlots] at hit
        exact ⟨slotOf_val (by omega), by omega, Or.inl ⟨by omega, by omega⟩⟩
      · cases e
  obtain ⟨hv, h8, hr⟩ := hv
  by_cases h0 : (slotOf p i).val = 18446744071562076160
  · left; exact eq_of_val'' (by rw [h0, tRw_val])
  by_cases h4 : (slotOf p i).val = 18446744071562076288
  · right; left; exact eq_of_val'' (by rw [h4, tmoW_val])
  right; right
  have hw : ∀ k : U64, k.val < 32 → (wordOf (slotOf p i) k).val = p.val + 32 * i + k.val := fun k hk => by
    show (core.num.U64.wrapping_add (slotOf p i) k).val = _
    simp only [core.num.U64.wrapping_add_val_eq, hv]; simp [U64.size, U64.numBits]; omega
  have hz : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → bsL.mem sR (wordOf (slotOf p i) k) = 0#u64 := by
    intro k hk hk8
    rw [memR_at (hw k hk) (by omega)]
    exact wordR_zero (by omega)
  have e0 : wordOf (slotOf p i) 0#u64 = slotOf p i := by
    apply eq_of_val''; rw [hw 0#u64 (by decide)]; simp [hv]
  have z0 := hz 0#u64 (by decide) (by decide)
  rw [e0] at z0
  have z8 := hz 8#u64 (by decide) (by decide)
  have z16 := hz 16#u64 (by decide) (by decide)
  have z24 := hz 24#u64 (by decide) (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold capV; rw [z0, z8]; rfl
  · unfold prevOf; exact z16
  · unfold nextOf; rw [z24]; rfl
  · unfold revOf; rw [z24]; rfl
  · unfold fbOf; rw [z24]; rfl

/-- The root slot is a slot of `thR`. -/
theorem isSlot_R_root : IsSlot thR tRw :=
  ⟨tRw, 0, Or.inr ⟨thR_tR, by decide⟩, eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val])⟩

/-- The timeout-handler slot is a slot of `thR`. -/
theorem isSlot_R_tmo : IsSlot thR tmoW :=
  ⟨tRw, 4, Or.inr ⟨thR_tR, by decide⟩, eq_of_val'' (by rw [slotOf_val (by rw [tRw_val]; omega), tRw_val, tmoW_val])⟩

/-- A slot of `thR` holding a non-null cap is the root slot or the timeout-handler slot. -/
theorem slotR_nonnull {y : U64} (hy : IsSlot thR y) (hn : capV (bsL.mem sR) y ≠ .Null) : y = tRw ∨ y = tmoW := by
  rcases slotR_cases hy with e | e | h
  · exact Or.inl e
  · exact Or.inr e
  · exact absurd h.1 hn

/-! ## The cheap fields -/

theorem ZR_T {t : U64} : t ∈ ZR.T ↔ t = tiB ∨ t = tRw := Iff.rfl
theorem ZR_C {c : U64} : c ∈ ZR.C ↔ c = sciB ∨ c = scRw := Iff.rfl

theorem ZR_thT : ∀ t, ZR.th t = some .tcb → t ∈ ZR.T := by
  intro t ht
  rcases thR_cases ht with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · exact Or.inr (eq_of_val'' (by rw [e, tRw_val]))
  · exact Or.inl (eq_of_val'' (by rw [e, tiB_val]))
  · cases e

theorem ZR_thk : ∀ q k, ZR.th q = some k → k = .tcb ∨ ∃ r, k = .cnode r := by
  intro q k hq
  rcases thR_cases hq with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr ⟨0, rfl⟩

theorem ZR_ks : KsApart ZR.N ZR.T ZR.E ZR.R ZR.B (bsL.ksb sR) :=
  ⟨fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem tRw_addr : TcbAddr tRw := ⟨by rw [tRw_val]; omega, by rw [tRw_val]; norm_num, by rw [tRw_val]; norm_num⟩

theorem tcbPlaced_R : TcbPlaced ZR.T := fun t ht => by
  rcases ht with e | e
  · subst e; exact tiB_addr
  · subst e; exact tRw_addr

theorem ZR_ip : Ipc.IPlaced ZR.N ZR.T ZR.E ZR.R ZR.B :=
  ⟨⟨tcbPlaced_R, fun _ h => h.elim, fun _ h => h.elim⟩,
    ⟨tcbPlaced_R, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
      fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim,
      fun _ h => h.elim⟩,
    fun _ h => h.elim, fun _ h => h.elim, fun _ h => h.elim⟩

theorem ZR_nk : ∀ n ∈ ZR.N, n.val + 40 ≤ (bsL.ksb sR).val ∨ (bsL.ksb sR).val + 13568 ≤ n.val :=
  fun _ h => h.elim

theorem ZR_nodeB : ∀ wp ∈ ZR.B, ∀ c : U64, c.val < 64 →
    wp.1.val + 8 ≤ bsL.nodeBase sR c ∨ bsL.nodeBase sR c + 4288 ≤ wp.1.val := fun _ h => h.elim

theorem tRw_ne_tiB : tRw ≠ tiB := fun e => by
  have := congrArg UScalar.val e; rw [tRw_val, tiB_val] at this; omega

theorem scRw_ne_sciB : scRw ≠ sciB := fun e => by
  have := congrArg UScalar.val e; rw [scRw_val, sciB_val] at this; omega

/-- The objects of `σR`, `σB`'s cases spelt out. -/
theorem kheapR_cases' {o : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject} (h : kheapR o = some ko) :
    (o = tRp ∧ ko = .tcb tcbR) ∨ (o = scRp ∧ ko = .schedContext scR 0) ∨
    (o = Fl4Spec.idleThreadPtr ∧ ∃ x, ko = .tcb x) ∨ (o = Fl4Spec.idleScPtr ∧ ∃ y n, ko = .schedContext y n) ∨
    ((o = Fl4Spec.initGlobalPml4 ∨ o = Fl4Spec.initGlobalPdpt ∨ o = Fl4Spec.initGlobalPd) ∧ ∃ a, ko = .archObj a) ∨
    ((∃ irq : Fl4Spec.Irq, irq.toNat < 128 ∧ irqNodeB + (Fl4Spec.ucast 64 irq <<< Fl4Spec.cteLevelBits) = o) ∧
      ko = .cnode 0 (Fl4Spec.emptyCnode 0)) := by
  rcases kheapR_cases h with h1 | h1 | ⟨-, -, h1⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (kheapB_cases h1))

theorem ZR_cover : Sched.SpecCover HR (σR (Z := Unit)) where
  ntfn o x h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  ep o x h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  reply o x h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  sc0 y k h := by
    rcases kheapR_cases' (o := (0#u64 : U64).bv) h with ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ |
      ⟨⟨irq, hi, e⟩, -⟩
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · exact absurd e (by decide)
    · rcases e with e | e | e <;> exact absurd e (by decide)
    · have := σB_node_val irq
      have h0 : ((0#u64 : U64).bv).toNat = 0 := rfl
      change (σB (Z := Unit)).interruptIrqNode irq = (0#u64 : U64).bv at e
      rw [e, h0, kbB_val] at this; omega
  arch o ao h := by
    refine ⟨12, le_refl _, ?_⟩
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨e, -⟩ | ⟨-, e⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · have hv : (⟨o⟩ : U64).val = 18446744071562084352 ∨ (⟨o⟩ : U64).val = 18446744071562088448 ∨
          (⟨o⟩ : U64).val = 18446744071562092544 := by
        show o.toNat = _ ∨ o.toNat = _ ∨ o.toNat = _
        rcases e with rfl | rfl | rfl
        · left; decide
        · right; left; decide
        · right; right; decide
      unfold HR HB
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hv]
    · cases e

theorem ZR_obj : Sched.ObjCover ZR.N ZR.T ZR.E ZR.R ZR.C (σR (Z := Unit)) where
  tcb o x h := by
    rcases kheapR_cases' h with ⟨e, -⟩ | ⟨-, e⟩ | ⟨e, -⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
    · exact ⟨tRw, Or.inr rfl, by rw [tRw_bv, e]⟩
    · cases e
    · exact ⟨tiB, Or.inl rfl, by rw [tiB_bv, e]⟩
    all_goals cases e
  ntfn o x h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  ep o x h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  reply o x h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, _, e⟩ | ⟨-, _, _, e⟩ | ⟨-, _, e⟩ | ⟨-, e⟩ <;> cases e
  sc o y k h := by
    rcases kheapR_cases' h with ⟨-, e⟩ | ⟨e, -⟩ | ⟨-, _, e⟩ | ⟨e, -⟩ | ⟨-, _, e⟩ | ⟨-, e⟩
    · cases e
    · exact ⟨scRw, Or.inr rfl, by rw [scRw_bv, e]⟩
    · cases e
    · exact ⟨sciB, Or.inl rfl, by rw [sciB_bv, e]⟩
    · cases e
    · cases e

theorem ZR_zH : (∀ t ∈ ZR.T, HR t = some .tcb) ∧ (∀ e ∈ ZR.E, HR e = some .ep) ∧
    (∀ r ∈ ZR.R, HR r = some .reply) ∧ (∀ n ∈ ZR.N, HR n = some .ntfn) :=
  ⟨fun t ht => by rcases ht with e | e <;> subst e; exacts [HR_ti, HR_tR], fun _ h => h.elim,
    fun _ h => h.elim, fun _ h => h.elim⟩

theorem ZR_hset : (∀ e, HR e = some .ep → e ∈ ZR.E) ∧ (∀ n, HR n = some .ntfn → n ∈ ZR.N) ∧
    (∀ r, HR r = some .reply → r ∈ ZR.R) := by
  refine ⟨fun e h => ?_, fun e h => ?_, fun e h => ?_⟩ <;>
    rcases HR_cases h with ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩ <;> cases k

theorem ZR_hscC : ∀ c z, HR c = some (.sc z) → c ∈ ZR.C := by
  intro c z h
  rcases HR_cases h with ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨e, -⟩ | ⟨-, k⟩ | ⟨k, -⟩ | ⟨k, -⟩
  · cases k
  · exact Or.inr (eq_of_val'' (by rw [e, scRw_val]))
  · cases k
  · exact Or.inl (eq_of_val'' (by rw [e, sciB_val]))
  all_goals cases k

theorem ZR_nsc : Sched.NSC ZR.N ZR.C (σR (Z := Unit)) := fun _ h => h.elim

theorem ZR_c0 : ∀ q ∈ ZR.C, q ≠ 0#u64 := by
  intro q hq e
  rcases hq with h | h <;> subst h
  · have := congrArg UScalar.val e; rw [sciB_val] at this; exact absurd this (by decide)
  · have := congrArg UScalar.val e; rw [scRw_val] at this; exact absurd this (by decide)

theorem ZR_intL : IntLayout ZR.th (bsL.ksb sR) where
  fit := by rw [sR_ksb]; exact kbB_fit'
  align := by rw [sR_ksb]; exact kbB_al
  st_out i hi := by
    rw [sR_ksb]
    have hv := irqStA_val (kb := kbB) kbB_fit' hi
    rw [kbB_val] at hv
    refine ⟨by show _ % 8 = 0; rw [hv]; omega, fun p k hp ⟨h1, h2⟩ => ?_⟩
    rw [hv] at h1 h2
    rcases thR_in hp h1 h2 with h | h | h <;> omega
  node i hi := by
    rw [sR_ksb]
    have hv := nodeA_val (kb := kbB) kbB_fit' hi
    rw [kbB_val] at hv
    show thR (nodeA kbB i) = _
    unfold thR thB
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]

theorem ZR_ext : JExt (L := bsL) ZR.th sR where
  nat y hy := by
    rcases slotR_cases hy with e | e | ⟨hn, -⟩
    · subst e; rw [capV_R_root]; trivial
    · subst e; rw [capV_R_tmo]; trivial
    · rw [hn]; trivial
  vw t ht := by
    rcases ZR_thT t ht with e | e <;> subst e
    · have hv : (tVcpuA tiB).val = 18446744071562072064 + 3664 := by
        unfold tVcpuA; simp only [core.num.U64.wrapping_add_val_eq, tiB_val]; simp [U64.size, U64.numBits]
      rw [memR_at hv (by omega)]
      exact wordR_zero_of (by omega)
    · have hv : (tVcpuA tRw).val = 18446744071562076160 + 3664 := by
        unfold tVcpuA; simp only [core.num.U64.wrapping_add_val_eq, tRw_val]; simp [U64.size, U64.numBits]
      rw [memR_at hv (by omega)]
      exact wordR_zero_of (by omega)

end

end Fl4Proofs.P2.BootSt
