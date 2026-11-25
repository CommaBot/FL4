/-
P2: **`RegionOK` and `UserOK` from P1's placement facts** (the [J] premises of
`E2E.Fl4Step.ser`).

`LayP K` states, for a layout `K`, the placement P1 carries: the typed heap
(`HeapOK`), the nodes outside every object, the capability slots 32-byte
aligned inside TCBs (below offset 192) and `other` objects, and user memory off
the TCBs, notifications, SCs and slots. `regionOK_of` and `userOK_of` derive the
two premises; `P2/OwnJAtZ.lean` derives `LayP` from the joint invariant `JAtZ`.

`LayP` mentions no memory, only the ghosts that change under the gate
(`KLayout`): holding at the last serial entry's exit, it holds wherever a local
path starts (no serial entry in between, `Serial.no_overlap`).

No premises beyond the theorems' hypotheses.
-/
import Fl4Proofs.P1.QueueHeap
import Fl4Proofs.P2.E2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMap
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.E2E

noncomputable section
open Classical

/-- **Placement of a layout** [J] (P1's facts, module docstring). -/
structure LayP (K : KLayout) : Prop where
  heap : HeapOK K.heap
  node : ∀ c : U64, c.val < K.ncores → ∀ p k, K.heap p = some k →
    p.val + 2 ^ k.bits ≤ K.ksb.val + 13568 + c.val * 4288 ∨
      K.ksb.val + 13568 + c.val * 4288 + 4288 ≤ p.val
  slot : ∀ p ∈ K.slots, p.val % 32 = 0 ∧ ∃ q k, K.heap q = some k ∧ q.val ≤ p.val ∧
    p.val + 32 ≤ q.val + 2 ^ k.bits ∧ (k = .tcb → p.val + 32 ≤ q.val + 192) ∧
    (k = .tcb ∨ ∃ z, k = .other z)
  user : ∀ x ∈ K.user, ∀ p k, K.heap p = some k → (k = .tcb ∨ k = .ntfn ∨ ∃ z, k = .sc z) →
    ¬ InW p (2 ^ k.bits) x
  userSlot : ∀ x ∈ K.user, ∀ p ∈ K.slots, ¬ InW p 32 x

variable {K : KLayout}

/-- Two objects holding one word are one. -/
theorem LayP.uniq (h : LayP K) {p q : U64} {k k' : HKind} {b : U64} (hp : K.heap p = some k)
    (hq : K.heap q = some k') (hb : InW p (2 ^ k.bits) b) (hb' : InW q (2 ^ k'.bits) b) :
    p = q ∧ k = k' := by
  have e : p = q := by
    by_contra hne
    rcases h.heap.disj p k q k' hp hq hne with h1 | h1
    · have := hb.2; have := hb'.1; omega
    · have := hb.1; have := hb'.2; omega
  subst e
  rw [hp] at hq; exact ⟨rfl, Option.some.inj hq⟩

/-- A word of an object is in no node. -/
theorem LayP.no_node (h : LayP K) {p : U64} {k : HKind} {b : U64} (hp : K.heap p = some k)
    (hb : InW p (2 ^ k.bits) b) : ¬ ∃ c, InNode K c b := by
  rintro ⟨c, hc, h1, h2⟩
  rcases h.node c hc p k hp with h3 | h3
  · have := hb.2; omega
  · have := hb.1; omega

/-- A word of a slot lies in the slot's object. -/
theorem LayP.slot_obj (h : LayP K) {p b : U64} (hp : p ∈ K.slots) (hb : InW p 32 b) :
    ∃ q k, K.heap q = some k ∧ InW q (2 ^ k.bits) b ∧ (k = .tcb → b.val < q.val + 192) ∧
      (k = .tcb ∨ ∃ z, k = .other z) := by
  obtain ⟨-, q, k, hq, h1, h2, h3, h4⟩ := h.slot p hp
  obtain ⟨b1, b2⟩ := hb
  exact ⟨q, k, hq, ⟨by omega, by omega⟩, fun e => by have := h3 e; omega, h4⟩

/-- A word of an object that is neither a TCB (below 192) nor `other` is in no slot. -/
theorem LayP.no_slot (h : LayP K) {p : U64} {k : HKind} {b : U64} (hp : K.heap p = some k)
    (hb : InW p (2 ^ k.bits) b) (hk : ∀ z, k ≠ .other z) (ht : k = .tcb → p.val + 192 ≤ b.val) :
    ¬ ∃ q ∈ K.slots, InW q 32 b := by
  rintro ⟨q, hq, hqb⟩
  obtain ⟨q', k', hq', hb', h1, h2⟩ := h.slot_obj hq hqb
  obtain ⟨rfl, rfl⟩ := h.uniq hp hq' hb hb'
  rcases h2 with rfl | ⟨z, rfl⟩
  · have := h1 rfl; have := ht rfl; omega
  · exact hk z rfl

theorem fld_val {p off : U64} (h : p.val + off.val < 2 ^ 64) : (fld p off).val = p.val + off.val := by
  simp [fld, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-! ## What `region` says -/

theorem region_slot_inv {b p : U64} (h : region K b = .slot p) : p ∈ K.slots ∧ InW p 32 b := by
  unfold region at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  cases h; exact Classical.choose_spec h2

theorem region_tcb_inv {b t : U64} (h : region K b = .tcb t) :
    K.heap t = some .tcb ∧ InW t (2 ^ 12) b := by
  unfold region at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  cases h; exact Classical.choose_spec h3

theorem region_ntfn_inv {b p : U64} (h : region K b = .ntfn p) :
    K.heap p = some .ntfn ∧ InW p (2 ^ 6) b := by
  unfold region at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  cases h; exact Classical.choose_spec h4

theorem region_sc_inv {b p : U64} (h : region K b = .sc p) :
    ∃ z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b := by
  unfold region at h
  split_ifs at h with h1 h2 h3 h4 h5 h6
  cases h; exact Classical.choose_spec h6

theorem LayP.region_tcb (h : LayP K) {t b : U64} (ht : K.heap t = some .tcb)
    (hb : InW t (2 ^ 12) b) (h192 : t.val + 192 ≤ b.val) : region K b = .tcb t := by
  have hex : ∃ t, K.heap t = some .tcb ∧ InW t (2 ^ 12) b := ⟨t, ht, hb⟩
  unfold region
  rw [dif_neg (h.no_node ht hb), dif_neg (h.no_slot ht hb (by intro z e; cases e) fun _ => h192),
    dif_pos hex]
  have hc := Classical.choose_spec hex
  rw [(h.uniq hc.1 ht hc.2 hb).1]

theorem LayP.region_ntfn (h : LayP K) {p b : U64} (hp : K.heap p = some .ntfn)
    (hb : InW p (2 ^ 6) b) : region K b = .ntfn p := by
  have hex : ∃ p, K.heap p = some .ntfn ∧ InW p (2 ^ 6) b := ⟨p, hp, hb⟩
  unfold region
  rw [dif_neg (h.no_node hp hb),
    dif_neg (h.no_slot hp hb (by intro z e; cases e) (by intro e; cases e)), dif_neg, dif_pos hex]
  · have hc := Classical.choose_spec hex
    rw [(h.uniq hc.1 hp hc.2 hb).1]
  · rintro ⟨t, ht, htb⟩
    have := (h.uniq ht hp htb hb).2; cases this

theorem LayP.region_sc (h : LayP K) {p b : U64} {z : Nat} (hp : K.heap p = some (.sc z))
    (hb : InW p (2 ^ z) b) : region K b = .sc p := by
  have hex : ∃ p z, K.heap p = some (.sc z) ∧ InW p (2 ^ z) b := ⟨p, z, hp, hb⟩
  unfold region
  rw [dif_neg (h.no_node hp hb),
    dif_neg (h.no_slot hp hb (by intro z e; cases e) (by intro e; cases e)), dif_neg, dif_neg,
    dif_neg, dif_pos hex]
  · obtain ⟨z', hc1, hc2⟩ := Classical.choose_spec hex
    rw [(h.uniq hc1 hp hc2 hb).1]
  · rintro ⟨q, ⟨hq, hqb⟩ | ⟨hq, hqb⟩⟩
    · have := (h.uniq hq hp hqb hb).2; cases this
    · have := (h.uniq hq hp hqb hb).2; cases this
  · rintro ⟨q, hq, hqb⟩
    have := (h.uniq hq hp hqb hb).2; cases this
  · rintro ⟨t, ht, htb⟩
    have := (h.uniq ht hp htb hb).2; cases this

theorem LayP.region_slot (h : LayP K) {p : U64} (hp : p ∈ K.slots) : region K p = .slot p := by
  have hin : InW p 32 p := ⟨le_refl _, by omega⟩
  have hex : ∃ q ∈ K.slots, InW q 32 p := ⟨p, hp, hin⟩
  obtain ⟨q, k, hq, hb, -, -⟩ := h.slot_obj hp hin
  unfold region
  rw [dif_neg (h.no_node hq hb), dif_pos hex]
  have hc := Classical.choose_spec hex
  have e1 := (h.slot _ hc.1).1
  have e2 := (h.slot p hp).1
  have e3 := hc.2.1
  have e4 := hc.2.2
  congr 1
  exact UScalar.eq_of_val_eq (by omega)

theorem tcb_off {off : U64} (h : off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
    off = oREPLY_OBJ ∨ off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT) :
    192 ≤ off.val ∧ off.val < 4096 ∧ off.val % 8 = 0 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [oAFFINITY, oSTATE, oBLOCK_OBJ, oREPLY_OBJ, oTIMER_DEADLINE, oTIMER_HEIGHT]

theorem LayP.tcb_fld (h : LayP K) {t off : U64} (ht : K.heap t = some .tcb)
    (ho : off.val < 4096) : (fld t off).val = t.val + off.val := by
  have := h.heap.fits t _ ht
  simp only [HKind.bits] at this
  exact fld_val (by omega)

/-- **`RegionOK` from P1's placement.** -/
theorem regionOK_of (h : LayP K) : RegionOK K where
  tcb t ht off hoff := by
    obtain ⟨o1, o2, -⟩ := tcb_off hoff
    have hv := h.tcb_fld ht o2
    exact ⟨h.region_tcb ht ⟨by omega, by omega⟩ (by omega), by omega⟩
  slot p hp := h.region_slot hp
  ntfn p hp := by
    have hf := h.heap.fits p _ hp
    simp only [HKind.bits] at hf
    have hv : (fld p 24#u64).val = p.val + 24 := fld_val (by simp; omega)
    exact ⟨h.region_ntfn hp ⟨by omega, by omega⟩, by omega⟩
  scw p b hb := by
    obtain ⟨z, hp, -⟩ := region_sc_inv hb
    have hf := h.heap.fits p _ hp
    have hz := h.heap.scmin p z hp
    have h7 : (2 : Nat) ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by omega) hz
    simp only [HKind.bits] at hf
    have hv : (fld p 16#u64).val = p.val + 16 := fld_val (by simp; omega)
    exact ⟨h.region_sc hp ⟨by omega, by omega⟩, hv⟩
  tcbOf t b hb := (region_tcb_inv hb).1
  slotOf p b hb := (region_slot_inv hb).1
  ntfnOf p b hb := (region_ntfn_inv hb).1

theorem align8 {p k : Nat} (h : p % 2 ^ k = 0) (hk : 3 ≤ k) : p % 8 = 0 := by
  have hd : 8 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hk
  rw [← Nat.mod_mod_of_dvd p hd, h]

/-- **`UserOK` from P1's placement.** -/
theorem userOK_of (h : LayP K) : UserOK K where
  tcb t ht off hoff := by
    obtain ⟨o1, o2, o3⟩ := tcb_off (off := off) (by
      rcases hoff with e | e | e | e | e <;> simp [e])
    have hv := h.tcb_fld ht o2
    have ha := h.heap.align t _ ht
    simp only [HKind.bits] at ha
    refine ⟨?_, fun hu => h.user _ hu t _ ht (Or.inl rfl) ⟨by omega, ?_⟩⟩
    · unfold Aligned; omega
    · simp only [HKind.bits]; omega
  slot p hp := by
    refine ⟨?_, fun hu => h.userSlot p hu p hp ⟨le_refl _, by omega⟩⟩
    have := (h.slot p hp).1
    unfold Aligned; omega
  ntfn p hp := by
    have hf := h.heap.fits p _ hp
    have ha := h.heap.align p _ hp
    simp only [HKind.bits] at hf ha
    have hv : (fld p 24#u64).val = p.val + 24 := fld_val (by simp; omega)
    refine ⟨?_, fun hu => h.user _ hu p _ hp (Or.inr (Or.inl rfl)) ⟨by omega, ?_⟩⟩
    · unfold Aligned; omega
    · simp only [HKind.bits]; omega
  sc p b hb := by
    obtain ⟨z, hp, -⟩ := region_sc_inv hb
    have hf := h.heap.fits p _ hp
    have ha := h.heap.align p _ hp
    have hz := h.heap.scmin p z hp
    have h7 : (2 : Nat) ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by omega) hz
    simp only [HKind.bits] at hf ha
    have ha8 := align8 ha (by omega)
    have hv : (fld p 16#u64).val = p.val + 16 := fld_val (by simp; omega)
    refine ⟨?_, fun hu => h.user _ hu p _ hp (Or.inr (Or.inr ⟨z, rfl⟩)) ⟨by omega, ?_⟩⟩
    · unfold Aligned; omega
    · simp only [HKind.bits]; omega

end
end Fl4Proofs.P2.OwnMap
