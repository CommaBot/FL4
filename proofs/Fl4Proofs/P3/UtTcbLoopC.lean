/-
P3 (DESIGN.md §9), untyped: **the TCB creation loop's values** (handoff/utj.md
"uttypes", ut37; l4v `retype_region` of `TCBObject`s, each `default_tcb` with
`new_context`, seL4's `tcbDebugAppend` per new TCB).

`TcbC m A h0 d0 DW i`: after `i` rounds of the loop over the window at `A`
(the `j`-th TCB at `bT A j`), each created TCB has `init_context`'s registers
(`ctxW`) and the domain word `d0`, the TCBs form a list from the head word
`DW` (the last created) through `debug_next` back to the old head `h0`, whose
`debug_prev` is the first new TCB, the `debug_prev` of the last created is 0.

* `TcbC.keep`: a step writing none of those words keeps it;
* `TcbC.step`: `create_object` of TCB `i` (UtTcbInit's `create_tcb_content`
  values) extends it to `i + 1`.
-/
import Fl4Proofs.P3.UtTcbInit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp

noncomputable section

/-- The `j`-th TCB of a window of TCBs at `A`. -/
def bT (A j : Nat) : U64 := ⟨BitVec.ofNat 64 (A + j * 4096)⟩

theorem bT_v {A j win : Nat} (hj : j < win) (hfit : A + win * 4096 ≤ 2 ^ 64) : (bT A j).val = A + j * 4096 := by
  have : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
  show (BitVec.ofNat 64 (A + j * 4096)).toNat = _; simp; omega

theorem bT_ok {A j win : Nat} (hj : j < win) (hfit : A + win * 4096 ≤ 2 ^ 64) (hal : A % 32 = 0) : TcbOk (bT A j) := by
  have := bT_v hj hfit
  have : (j + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hj
  exact ⟨by omega, by omega⟩

/-- **The values the TCB loop has written after `i` rounds** (module docstring). -/
def TcbC (m : U64 → U64) (A : Nat) (h0 d0 DW : U64) (i : Nat) : Prop :=
  (∀ j, j < i → ∀ r : U64, r.val < 24 → m (regA (bT A j) r) = ctxW r.val) ∧
  (∀ j, j < i → m (P1.domA (bT A j)) = d0) ∧
  (∀ j, j < i → m (P1.dnA (bT A j)) = if j = 0 then h0 else bT A (j - 1)) ∧
  (∀ j, j + 1 < i → m (P1.dpA (bT A j)) = bT A (j + 1)) ∧
  (∀ j, j + 1 = i → m (P1.dpA (bT A j)) = 0#u64) ∧
  (0 < i → h0 ≠ 0#u64 → m (P1.dpA h0) = bT A 0) ∧
  m DW = (if i = 0 then h0 else bT A (i - 1))

theorem TcbC.zero {m : U64 → U64} {A : Nat} {h0 d0 DW : U64} (h : m DW = h0) : TcbC m A h0 d0 DW 0 :=
  ⟨fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), fun _ h => absurd h (by omega),
    fun _ h => absurd h (by omega), fun _ h => absurd h (by omega), fun h => absurd h (by omega), by simp [h]⟩

/-- The words `TcbC` reads. -/
def TcbCW (A : Nat) (h0 DW : U64) (i : Nat) (w : U64) : Prop :=
  (∃ j, j < i ∧ Rg (bT A j) 256 4096 w) ∨ (h0 ≠ 0#u64 ∧ w = P1.dpA h0) ∨ w = DW

theorem dA_al {t : U64} (ht : TcbOk t) : P1.Aligned (P1.domA t) ∧ P1.Aligned (P1.dnA t) ∧ P1.Aligned (P1.dpA t) := by
  have := domA_v ht; have := dnA_v ht; have := dpA_v ht; have := ht.1
  exact ⟨by show _ % 8 = 0; omega, by show _ % 8 = 0; omega, by show _ % 8 = 0; omega⟩

/-- **`TcbC` kept by a step writing none of its words.** -/
theorem TcbC.keep {m m' : U64 → U64} {A win i : Nat} {h0 d0 DW : U64} (h : TcbC m A h0 d0 DW i)
    (hi : i ≤ win) (hfit : A + win * 4096 ≤ 2 ^ 64) (hal : A % 32 = 0) (hh0 : h0 ≠ 0#u64 → TcbOk h0)
    (hDWal : P1.Aligned DW) (hk : ∀ w, P1.Aligned w → TcbCW A h0 DW i w → m' w = m w) :
    TcbC m' A h0 d0 DW i := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h
  have ok : ∀ j, j < i → TcbOk (bT A j) := fun j hj => bT_ok (by omega) hfit hal
  refine ⟨fun j hj r hr => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun hp hn => ?_, ?_⟩
  · rw [hk _ (regA_al (ok j hj) hr) (Or.inl ⟨j, hj, by unfold Rg; rw [regA_v (ok j hj) hr]; omega⟩)]
    exact c1 j hj r hr
  · rw [hk _ (dA_al (ok j hj)).1 (Or.inl ⟨j, hj, by unfold Rg; rw [domA_v (ok j hj)]; omega⟩)]
    exact c2 j hj
  · rw [hk _ (dA_al (ok j hj)).2.1 (Or.inl ⟨j, hj, by unfold Rg; rw [dnA_v (ok j hj)]; omega⟩)]
    exact c3 j hj
  · rw [hk _ (dA_al (ok j (by omega))).2.2 (Or.inl ⟨j, by omega, by unfold Rg; rw [dpA_v (ok j (by omega))]; omega⟩)]
    exact c4 j hj
  · rw [hk _ (dA_al (ok j (by omega))).2.2 (Or.inl ⟨j, by omega, by unfold Rg; rw [dpA_v (ok j (by omega))]; omega⟩)]
    exact c5 j hj
  · rw [hk _ (dA_al (hh0 hn)).2.2 (Or.inr (Or.inl ⟨hn, rfl⟩))]
    exact c6 hp hn
  · rw [hk _ hDWal (Or.inr (Or.inr rfl))]; exact c7

/-- **`TcbC` extended by the creation of TCB `i`** (module docstring): its
values (UtTcbInit's `create_tcb_content`, the old head being `m DW`), the
write frame the new TCB, the old head's `debug_prev` and the head word. -/
theorem TcbC.step {m m2 : U64 → U64} {A win zhi i : Nat} {h0 d0 DW : U64} (h : TcbC m A h0 d0 DW i)
    (hi : i < win) (hfit : A + win * 4096 ≤ 2 ^ 64) (hal : A % 32 = 0) (hA0 : 0 < A)
    (hzhi : A + win * 4096 ≤ zhi)
    (hh0 : h0 ≠ 0#u64 → TcbOk h0 ∧ (h0.val + 4096 ≤ A ∨ zhi ≤ h0.val))
    (hDWreg : ¬ (A ≤ DW.val ∧ DW.val < zhi)) (hDWh0 : h0 ≠ 0#u64 → ¬ Rg h0 0 4096 DW)
    (hfr : ∀ w, P1.Aligned w → ¬ (Rg (bT A i) 0 4096 w ∨ (m DW ≠ 0#u64 ∧ w = P1.dpA (m DW)) ∨ w = DW) → m2 w = m w)
    (hreg : ∀ r : U64, r.val < 24 → m2 (regA (bT A i) r) = ctxW r.val)
    (hdom : m2 (P1.domA (bT A i)) = d0) (hdn : m2 (P1.dnA (bT A i)) = m DW) (hdp : m2 (P1.dpA (bT A i)) = 0#u64)
    (hdph : m DW ≠ 0#u64 → m2 (P1.dpA (m DW)) = bT A i) (hDW2 : m2 DW = bT A i) :
    TcbC m2 A h0 d0 DW (i + 1) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := h
  have ok : ∀ j, j < win → TcbOk (bT A j) := fun j hj => bT_ok hj hfit hal
  have bv : ∀ j, j < win → (bT A j).val = A + j * 4096 := fun j hj => bT_v hj hfit
  have hik : (i + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hi
  have bne : ∀ j, j < win → bT A j ≠ 0#u64 := fun j hj e => by
    have := bv j hj; rw [e] at this; simp at this; omega
  -- the old head
  have hmDW : m DW = if i = 0 then h0 else bT A (i - 1) := c7
  -- earlier TCBs' words below `debug_prev` are kept
  have notW : ∀ j, j < i → ∀ w, P1.Aligned w → Rg (bT A j) 256 3584 w → m2 w = m w := by
    intro j hj w hw hr
    refine hfr w hw ?_
    have hbj := bv j (by omega)
    have hbi := bv i hi
    unfold Rg at hr
    rintro (h1 | ⟨hn, e⟩ | e)
    · unfold Rg at h1; rw [hbi] at h1; rw [hbj] at hr
      have : j * 4096 + 4096 ≤ i * 4096 := by have := Nat.mul_le_mul_right 4096 hj; omega
      omega
    · rw [hmDW] at hn e
      have hi0 : i ≠ 0 := by omega
      rw [if_neg hi0] at e
      rw [e, dpA_v (ok (i - 1) (by omega)), bv (i - 1) (by omega)] at hr
      rw [hbj] at hr
      have : (i - 1) * 4096 = i * 4096 - 4096 := by rw [Nat.sub_mul, Nat.one_mul]
      rcases Nat.lt_or_ge j (i - 1) with hl | hl
      · have : j * 4096 + 4096 ≤ (i - 1) * 4096 := by have := Nat.mul_le_mul_right 4096 hl; omega
        omega
      · have : j = i - 1 := by omega
        subst this; omega
    · rw [e] at hr; rw [hbj] at hr
      have : j * 4096 + 4096 ≤ i * 4096 := by have := Nat.mul_le_mul_right 4096 hj; omega
      exact hDWreg ⟨by omega, by omega⟩
  refine ⟨fun j hj r hr => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_, fun _ hn => ?_, ?_⟩
  · rcases Nat.lt_or_ge j i with hl | hl
    · rw [notW j hl _ (regA_al (ok j (by omega)) hr) (by unfold Rg; rw [regA_v (ok j (by omega)) hr]; omega)]
      exact c1 j hl r hr
    · have : j = i := by omega
      subst this; exact hreg r hr
  · rcases Nat.lt_or_ge j i with hl | hl
    · rw [notW j hl _ (dA_al (ok j (by omega))).1 (by unfold Rg; rw [domA_v (ok j (by omega))]; omega)]
      exact c2 j hl
    · have : j = i := by omega
      subst this; exact hdom
  · rcases Nat.lt_or_ge j i with hl | hl
    · rw [notW j hl _ (dA_al (ok j (by omega))).2.1 (by unfold Rg; rw [dnA_v (ok j (by omega))]; omega)]
      exact c3 j hl
    · have : j = i := by omega
      subst this; rw [hdn, hmDW]
  · rcases Nat.lt_or_ge (j + 1) i with hl | hl
    · -- an earlier `debug_prev`, not the old head's
      have hj' : j < win := by omega
      rw [hfr _ (dA_al (ok j hj')).2.2 ?_]
      · exact c4 j hl
      rintro (h1 | ⟨hn, e⟩ | e)
      · unfold Rg at h1; rw [dpA_v (ok j hj'), bv i hi, bv j hj'] at h1
        have : j * 4096 + 4096 ≤ i * 4096 := by have := Nat.mul_le_mul_right 4096 (show j < i by omega); omega
        omega
      · rw [hmDW, if_neg (by omega)] at e
        have := congrArg UScalar.val e
        rw [dpA_v (ok j hj'), dpA_v (ok (i - 1) (by omega)), bv j hj', bv (i - 1) (by omega)] at this
        have : j * 4096 + 4096 ≤ (i - 1) * 4096 := by
          have := Nat.mul_le_mul_right 4096 (show j < i - 1 by omega); omega
        omega
      · have hv := congrArg UScalar.val e
        rw [dpA_v (ok j hj'), bv j hj'] at hv
        have : j * 4096 + 4096 ≤ i * 4096 := by have := Nat.mul_le_mul_right 4096 (show j < i by omega); omega
        exact hDWreg ⟨by omega, by omega⟩
    · have : j + 1 = i := by omega
      subst this
      have e : m DW = bT A j := by rw [hmDW, if_neg (by omega)]; rfl
      have := hdph (by rw [e]; exact bne j (by omega))
      rw [e] at this; exact this
  · have : j = i := by omega
    subst this; exact hdp
  · by_cases hi0 : i = 0
    · subst hi0
      have e : m DW = h0 := by rw [hmDW]; rfl
      have := hdph (by rw [e]; exact hn)
      rw [e] at this; exact this
    · obtain ⟨hok, hout⟩ := hh0 hn
      rw [hfr _ (dA_al hok).2.2 ?_]
      · exact c6 (by omega) hn
      rintro (h1 | ⟨hn', e⟩ | e)
      · unfold Rg at h1; rw [dpA_v hok, bv i hi] at h1; omega
      · rw [hmDW, if_neg hi0] at e
        have := congrArg UScalar.val e
        rw [dpA_v hok, dpA_v (ok (i - 1) (by omega)), bv (i - 1) (by omega)] at this
        omega
      · exact hDWh0 hn (by rw [← e]; unfold Rg; rw [dpA_v hok]; omega)
  · rw [hDW2]; simp


/-- A TCB's words past its slots are in no slot. -/
theorem tcbw_not_slot {th : TypedHeap} (hP : Placed th) {q : U64} (hq : th q = some .tcb) {a w : U64}
    (ha : IsSlot th a) (h1 : q.val + 256 ≤ w.val) (h2 : w.val < q.val + 4096) :
    ¬ (a.val ≤ w.val ∧ w.val < a.val + 32) := by
  obtain ⟨p, kd, hp, g1, g2, g3⟩ := slot_in_object hP ha
  by_cases hpq : p = q
  · subst hpq; rw [hq] at hp; cases hp
    have := g3 rfl; simp [tcbSlots] at this; omega
  · have e4 : objSize ObjKind.tcb = 4096 := rfl
    rcases hP.disj p q kd .tcb hp hq hpq with h | h <;> omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxRecDepth 20000 in
/-- **`create_new_objects`' values for TCBs** (`create_loop_frame_tcb` with
`TcbC` after the loop: the new TCBs' registers, domain words, debug links; the
current-domain word `CD` kept). -/
theorem create_loop_content_tcb {A' : Type} (arI : machine.Arch A') (ar : A') (th th' : TypedHeap) (hP' : Placed th')
    (hext : ∀ a, IsSlot th a → IsSlot th' a)
    {pp : U64} {rs : Nat} (hpp : th' pp = some (.cnode rs))
    {idx : List Bool} (hidx : idx.length = rs) (hppo : IsSlot th (cslotAddr (pp.bv, idx))) {p sb fi : U64} {d : Bool}
    (hsb : sb.val < 64) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
    (σ1 : Fl4Spec.State Unit) {dest : U64} {r : Nat} (hdest : th' dest = some (.cnode r))
    (hdesto : th dest = some (.cnode r)) (hr : r ≤ 64)
    (nt us : U64) (dev : Bool) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 1) (hus : us.val < 64)
    (off win base : U64) (hwin : off.val + win.val ≤ 2 ^ r)
    (hfit : base.val + win.val * 4096 ≤ 2 ^ 64) (hhigh : 2 ^ 64 - 2 ^ 47 ≤ base.val) (hal : base.val % 32 = 0)
    (hpA : p.val ≤ base.val) (hAp : base.val + win.val * 4096 ≤ p.val + 2 ^ sb.val)
    (hnew : ∀ i, i < win.val → th' ⟨BitVec.ofNat 64 (base.val + i * 4096)⟩ = some .tcb)
    (zhi : Nat) (hzhi : base.val + win.val * 4096 ≤ zhi)
    (hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ base.val + win.val * 4096 ∨ zhi ≤ a.val)
    (hold : ∀ a, IsSlot th a → a.val + 32 ≤ base.val ∨ zhi ≤ a.val)
    (ksb0 DW : U64) (hDWal : P1.Aligned DW) (hDWout : ∀ a, IsSlot th' a → ¬ (a.val ≤ DW.val ∧ DW.val < a.val + 32))
    (hDWreg : ¬ (base.val ≤ DW.val ∧ DW.val < zhi))
    (hDW : ∀ s : S, L.ksb s = ksb0 → L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = DW)
    (G0 : MdbGhost) (m0 : U64 → U64)
    (hsrcd : ∀ j, j < win.val → cslotAddr (pp.bv, idx) ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
    (hG0 : ∀ x ∈ G0.chains.flatten, IsSlot th x)
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0)
    (hX : TcbX (L := L) th th' ksb0 DW base.val win.val zhi s 0)
    (hA0 : 0 < base.val)
    (hh0 : L.mem s DW ≠ 0#u64 → TcbOk (L.mem s DW) ∧ th' (L.mem s DW) = some .tcb ∧
      ((L.mem s DW).val + 4096 ≤ base.val ∨ zhi ≤ (L.mem s DW).val))
    (hDWh0 : L.mem s DW ≠ 0#u64 → ¬ Rg (L.mem s DW) 0 4096 DW)
    (CD : U64) (hCD : ∀ s1 : S, L.ksb s1 = ksb0 → Sched.curDomA st s1 = CD) (hCDal : P1.Aligned CD)
    (hCDreg : ¬ (base.val ≤ CD.val ∧ CD.val < zhi))
    (hCDh0 : L.mem s DW ≠ 0#u64 → ¬ Rg (L.mem s DW) 0 4096 CD) (hCDW : CD ≠ DW)
    (hCDs : ∀ a, IsSlot th' a → ¬ (a.val ≤ CD.val ∧ CD.val < a.val + 32)) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1 win.val ∧
      L.ksb res.1 = ksb0 ∧ WFrame (L := L) s res.1 (TcbLoopW th base.val win.val DW (L.mem s DW)) ∧
      TcbC (L.mem res.1) base.val (L.mem s DW) (L.mem s CD) DW win.val ∧ L.mem res.1 CD = L.mem s CD ⦄ := by
  have hz12 : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  have hk : 2 ^ zOf nt.val us.val = 4096 := by rw [hz12]; rfl
  have hn14 : nt.val < 14 := by omega
  unfold objects.create_new_objects
  rw [object_size_eq nt us hn14 hus]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have h63 : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val = zOf nt.val us.val := by
    have : ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64).val =
        (⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64).val % 64 := by
      simp only [UScalar.val_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 6
    rw [this]
    show (BitVec.ofNat 64 (zOf nt.val us.val)).toNat % 64 = _
    simp; omega
  have hdsl : ∀ j, j < win.val → IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
    fun j hj => ⟨dest, off.val + j, Or.inl ⟨r, hdesto, by omega⟩, rfl⟩
  have hnewcv : ∀ i, i < win.val →
      CapValid th' (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i * 2 ^ zOf nt.val us.val)⟩ us dev) := by
    intro i hi; rw [hk, hnt]; exact hnew i hi
  refine loop.spec_decr_nat (measure := fun x => win.val - x.2.2.val)
    (inv := fun x => x.2.1 = ar ∧ x.2.2.val ≤ win.val ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) x.1 x.2.2.val ∧
      TcbX (L := L) th th' ksb0 DW base.val win.val zhi x.1 x.2.2.val ∧
      WFrame (L := L) s x.1 (TcbLoopW th base.val win.val DW (L.mem s DW)) ∧
      (L.mem x.1 DW = L.mem s DW ∨ ∃ j, j < x.2.2.val ∧ L.mem x.1 DW = ⟨BitVec.ofNat 64 (base.val + j * 4096)⟩) ∧
      TcbC (L.mem x.1) base.val (L.mem s DW) (L.mem s CD) DW x.2.2.val ∧ L.mem x.1 CD = L.mem s CD) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hXi, hW1, hD1, hC1, hCD1⟩
    simp only at ha hiw hI hXi hW1 hD1 hC1 hCD1 ⊢
    subst ha
    unfold objects.create_new_objects_loop.body
    by_cases hit : i < win
    · rw [if_pos hit]
      have hit' : i.val < win.val := hit
      simp only [lift, bind_ok]
      have hik : (i.val + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hit'
      rw [Nat.add_mul, Nat.one_mul] at hik
      obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i
        ((⟨BitVec.ofNat 64 (zOf nt.val us.val)⟩ : U64) &&& 63#u64) _
        (by rw [h63]; simp [UScalarTy.U64_numBits_eq]; omega) rfl)
      rw [hi2]; simp only [bind_ok]
      have hi2v : i2.val = i.val * 4096 := by
        rw [hv2, h63, Nat.shiftLeft_eq, hk]
        simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      have hi3 : core.num.U64.wrapping_add base i2 = ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ := by
        apply u64_ofNat_eq
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]; omega
      rw [hi3]
      obtain ⟨⟨c, s2, a2⟩, hcr, hc, ha2, hI2, hk2, hz2, hX22, hm2⟩ := spec_exists (create_step (L := L) arI a1 th th'
        hP' ksb0 DW base.val win.val zhi hDWal hDWout hDWreg hDW rfl hzhi hfit hal hnew
        (fun j hj => hext _ (hdsl j hj)) (hext _ hppo) nt us dev hnt s1 i.val hit' hI hXi)
      simp only at hc ha2 hI2 hk2 hz2 hX22 hm2
      -- the frame of the creation
      have hW2 : WFrame (L := L) s s2 (TcbLoopW th base.val win.val DW (L.mem s DW)) := by
        set bi : U64 := ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ with hbi
        have hbiv : bi.val = base.val + i.val * 4096 := by
          show (BitVec.ofNat 64 (base.val + i.val * 4096)).toNat = _; simp; omega
        have htk : TcbOk bi := ⟨by rw [hbiv]; omega, by rw [hbiv]; omega⟩
        obtain ⟨hksb1, hz1, -, hX31⟩ := hXi
        have hcpu : tcbCpu (L := L) s1 bi = 0#u64 := by
          unfold tcbCpu
          have hv : (core.num.U64.wrapping_add bi 3520#u64).val = base.val + i.val * 4096 + 3520 := by
            obtain ⟨h1, h2⟩ := htk; rw [← hbiv]; addr_tac
          exact hz1 _ (by unfold P1.Aligned; omega) (by omega) (by omega)
        have hdw : dbgW (L := L) s1 bi = DW := by unfold dbgW; rw [hcpu]; exact hDW s1 hksb1
        have hnotInT : ∀ w : U64, InT bi w → base.val ≤ w.val ∧ w.val < base.val + (i.val + 1) * 4096 := by
          rintro w ⟨h1, h2, -⟩; rw [hbiv] at h1 h2; omega
        obtain ⟨r', hr', -, -, hf', -⟩ := spec_exists (create_tcb_frame (L := L) arI s1 a1 nt bi us dev hnt htk
          (by rw [hdw]; exact hDWal)
          (by rw [hdw]; intro h; rcases hX31 with h' | ⟨-, h', -⟩; exact absurd h' h; exact h')
          (by rw [hdw]; intro h; exact hDWreg (by have := hnotInT DW h; omega)))
        rw [hcr] at hr'; cases eq_of_ok_eq hr'
        refine hW1.trans (hf'.mono fun w hw => ?_)
        unfold TcbW at hw; rw [hdw] at hw
        rcases hw with h | ⟨hne, he⟩ | he
        · exact Or.inr (Or.inl ⟨i.val, hit', h⟩)
        · rcases hD1 with e | ⟨j, hj, e⟩
          · rw [e] at hne he; exact Or.inr (Or.inr (Or.inr ⟨hne, he⟩))
          · refine Or.inr (Or.inl ⟨j, by omega, ?_⟩)
            have hjv : (⟨BitVec.ofNat 64 (base.val + j * 4096)⟩ : U64).val = base.val + j * 4096 := by
              have : j * 4096 < win.val * 4096 := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
              show (BitVec.ofNat 64 (base.val + j * 4096)).toNat = _; simp; omega
            rw [e, hjv] at he
            unfold InT; rw [hjv]; omega
        · exact Or.inr (Or.inr (Or.inl (UScalar.eq_of_val_eq he)))
      -- the values of the creation
      have hC2 : TcbC (L.mem s2) base.val (L.mem s DW) (L.mem s CD) DW (i.val + 1) ∧ L.mem s2 CD = L.mem s CD := by
        set bi : U64 := ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ with hbi
        have hbiv : bi.val = base.val + i.val * 4096 := by
          show (BitVec.ofNat 64 (base.val + i.val * 4096)).toNat = _; simp; omega
        have htk : TcbOk bi := ⟨by rw [hbiv]; omega, by rw [hbiv]; omega⟩
        obtain ⟨hksb1, hz1, -, -⟩ := hXi
        have hcpu : tcbCpu (L := L) s1 bi = 0#u64 := by
          unfold tcbCpu
          have hv : (core.num.U64.wrapping_add bi 3520#u64).val = base.val + i.val * 4096 + 3520 := by
            obtain ⟨h1, h2⟩ := htk; rw [← hbiv]; addr_tac
          exact hz1 _ (by unfold P1.Aligned; omega) (by omega) (by omega)
        have hdw : dbgW (L := L) s1 bi = DW := by unfold dbgW; rw [hcpu]; exact hDW s1 hksb1
        have hcd1 : Sched.curDomA st s1 = CD := hCD s1 hksb1
        have hm1 : L.mem s1 DW = if i.val = 0 then L.mem s DW else bT base.val (i.val - 1) := hC1.2.2.2.2.2.2
        have hhd : L.mem s1 DW ≠ 0#u64 → TcbOk (L.mem s1 DW) ∧
            ((L.mem s1 DW).val + 4096 ≤ bi.val ∨ bi.val + 4096 ≤ (L.mem s1 DW).val) ∧ ¬ Rg (L.mem s1 DW) 0 4096 DW := by
          intro hn
          rw [hm1] at hn ⊢
          by_cases hi0 : i.val = 0
          · rw [if_pos hi0] at hn ⊢
            obtain ⟨g1, -, g3⟩ := hh0 hn
            refine ⟨g1, ?_, hDWh0 hn⟩
            rw [hbiv, hi0]; rcases g3 with g | g <;> omega
          · rw [if_neg hi0] at hn ⊢
            have hb := bT_v (A := base.val) (j := i.val - 1) (win := win.val) (by omega) hfit
            refine ⟨bT_ok (by omega) hfit hal, ?_, ?_⟩
            · rw [hb, hbiv]; left
              have : (i.val - 1) * 4096 + 4096 = i.val * 4096 := by
                rw [Nat.sub_mul, Nat.one_mul]; have : 4096 ≤ i.val * 4096 := by omega
                omega
              omega
            · unfold Rg; rw [hb]; intro hr
              have : (i.val - 1) * 4096 + 4096 = i.val * 4096 := by
                rw [Nat.sub_mul, Nat.one_mul]; have : 4096 ≤ i.val * 4096 := by omega
                omega
              exact hDWreg ⟨by omega, by omega⟩
        obtain ⟨r', hr', -, -, hf', hk1, hreg, hdom, hdn, hdp, hdph⟩ := spec_exists (create_tcb_content (L := L) arI s1
          a1 nt bi us dev hnt htk
          (by rw [hdw]; exact hDWal)
          (by rw [hdw]; intro h; exact (hhd h).1)
          (by rw [hdw]; intro h; exact (hhd h).2.1)
          (by rw [hdw]; intro hr; unfold Rg at hr; rw [hbiv] at hr; exact hDWreg ⟨by omega, by omega⟩)
          (by rw [hdw]; intro h; exact (hhd h).2.2)
          (by rw [hcd1]; intro hr; unfold Rg at hr; rw [hbiv] at hr; exact hCDreg ⟨by omega, by omega⟩)
          (by rw [hcd1]; exact hCDal))
        rw [hcr] at hr'; cases eq_of_ok_eq hr'
        simp only at hf' hk1 hreg hdom hdn hdp hdph
        rw [hdw] at hk1 hdn hdph
        rw [hcd1, hCD1] at hdom
        have hCD2 : L.mem s2 CD = L.mem s CD := by
          rw [← hCD1]; refine hf'.2.2 CD hCDal ?_
          unfold TcbWC; rw [hdw]
          rintro (hr | ⟨hn, e⟩ | e)
          · unfold Rg at hr; rw [hbiv] at hr; exact hCDreg ⟨by omega, by omega⟩
          · by_cases hi0 : i.val = 0
            · have e0 : L.mem s1 DW = L.mem s DW := by rw [hm1, if_pos hi0]
              rw [e0] at hn e
              exact hCDh0 hn (by unfold Rg; rw [e, dpA_v (hh0 hn).1]; omega)
            · have e0 : L.mem s1 DW = bT base.val (i.val - 1) := by rw [hm1, if_neg hi0]
              rw [e0] at e
              have hb := bT_v (A := base.val) (j := i.val - 1) (win := win.val) (by omega) hfit
              have := congrArg UScalar.val e
              rw [dpA_v (bT_ok (by omega) hfit hal), hb] at this
              have : (i.val - 1) * 4096 + 4096 = i.val * 4096 := by
                rw [Nat.sub_mul, Nat.one_mul]; have : 4096 ≤ i.val * 4096 := by omega
                omega
              exact hCDreg ⟨by omega, by omega⟩
          · exact hCDW e
        exact ⟨TcbC.step (zhi := zhi) hC1 hit' hfit hal hA0 hzhi (fun hn => ⟨(hh0 hn).1, (hh0 hn).2.2⟩) hDWreg hDWh0
          (fun w hw hn => hf'.2.2 w hw (by unfold TcbWC; rw [hdw]; exact hn)) hreg hdom hdn hdp hdph hk1, hCD2⟩
      subst hc ha2
      rw [hcr]; simp only [bind_ok, uncurry_apply_pair]
      have hi4 : (core.num.U64.wrapping_add off i).bv = BitVec.ofNat 64 (off.val + i.val) := by
        rw [bv_eq_ofNat]; congr 1
        have : off.val + i.val < 2 ^ 64 := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hr; omega
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
      rw [show obj.Slot.index dest (core.num.U64.wrapping_add off i) =
        ok (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val))) by
          rw [spec_eq_ok (slot_index_spec dest _), hi4]]
      simp only [bind_ok]
      have hcap : capability.Cap.Thread ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ =
          newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev := by
        rw [hk, hnt]; rfl
      rw [hcap]
      obtain ⟨σi, Gi, -, -, -, hM2, -, -, hsrc2, hnull2, -, -, -, hmemG, -⟩ := id hI2
      have hsm : cslotAddr (pp.bv, idx) ∈ Gi.chains.flatten := (hM2.members _).2 ⟨hext _ hppo, _, hsrc2, by simp⟩
      have hdn : slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)) ∉ Gi.chains.flatten := by
        intro h; obtain ⟨-, c0, h0, hn0⟩ := (hM2.members _).1 h
        rw [hnull2 i.val le_rfl hit'] at h0; exact hn0 (eq_of_ok_eq h0).symm
      have he : EncWf (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev) :=
        newCap_encWf (by omega) _ us dev hus (canonical_of_high (by
          show 2 ^ 64 - 2 ^ 47 ≤ (BitVec.ofNat 64 _).toNat; rw [hk]; simp; omega))
      obtain ⟨s3, hs3, hL3⟩ := spec_exists (loop_step th' hP' hpp hidx hsb hpfit σ1 hdest hr nt us dev t ht
        (by omega) hus (by omega) (fun h => by omega) off.val win.val base.val hwin (by rw [hk]; exact hfit) hhigh hpA
        (by rw [hk]; exact hAp) hnewcv (base.val + win.val * 4096) zhi hzs G0 m0 hsrcd s2 i.val hit' hI2)
      obtain ⟨s3', hs3', hX3⟩ := spec_exists (tcbx_insert (L := L) th th' hP' hext ksb0 DW base.val win.val zhi hDWal
        hDWout hold hzhi hnew hfit hal s2 Gi hM2 _ _ hsm hppo (hdsl i.val hit') hdn _ he i.val hit' hk2 hz2 hX22 hm2)
      rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
      have hnx : nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) = 0#u64 ∨
          IsSlot th' (nextOf (L.mem s2) (cslotAddr (pp.bv, idx))) := by
        rcases hM2.next_mem hsm with h | ⟨h1, -⟩
        · exact Or.inl h
        · exact Or.inr ((hM2.members _).1 h1).1
      obtain ⟨s3', hs3', hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s2
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev) _ _ (hext _ hppo)
        (hext _ (hdsl i.val hit')) hnx)
      rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
      obtain ⟨s3', hs3', hk3⟩ := spec_exists (insert_new_cap_kc (L := L) s2 (cslotAddr (pp.bv, idx))
        (slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)))
        (newCapOf nt.val ⟨BitVec.ofNat 64 (base.val + i.val * 2 ^ zOf nt.val us.val)⟩ us dev))
      rw [hs3] at hs3'; cases eq_of_ok_eq hs3'
      have hslw : ∀ a, (a = cslotAddr (pp.bv, idx) ∨ a = slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)) ∨
          (nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) ≠ 0#u64 ∧ a = nextOf (L.mem s2) (cslotAddr (pp.bv, idx)))) →
          IsSlot th' a := by
        rintro a (e | e | ⟨h0, e⟩)
        · rw [e]; exact hext _ hppo
        · rw [e]; exact hext _ (hdsl i.val hit')
        · rw [e]; exact hnx.resolve_left h0
      have hslw0 : ∀ a, (a = cslotAddr (pp.bv, idx) ∨ a = slotAddr dest.bv (BitVec.ofNat 64 (off.val + i.val)) ∨
          (nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) ≠ 0#u64 ∧ a = nextOf (L.mem s2) (cslotAddr (pp.bv, idx)))) →
          IsSlot th a := by
        rintro a (e | e | ⟨h0, e⟩)
        · rw [e]; exact hppo
        · rw [e]; exact hdsl i.val hit'
        · rw [e]
          rcases hM2.next_mem hsm with h | ⟨h1, -⟩
          · exact absurd h h0
          · rcases hmemG _ h1 with hg | ⟨j, hj, e'⟩
            · exact hG0 _ hg
            · rw [e']; exact hdsl j (by omega)
      have hW3 : WFrame (L := L) s s3 (TcbLoopW th base.val win.val DW (L.mem s DW)) :=
        hW2.trans ⟨hk3.1, hk3.2, fun w hw hnp => hfr w hw (fun a ha hin => hnp (Or.inl ⟨a, hslw0 a ha, hin.1, hin.2⟩))⟩
      have hD3 : L.mem s3 DW = ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ := by
        rw [hfr DW hDWal (fun a ha hin => hDWout a (hslw a ha) hin)]; exact hm2
      have hC3 : TcbC (L.mem s3) base.val (L.mem s DW) (L.mem s CD) DW (i.val + 1) ∧ L.mem s3 CD = L.mem s CD := by
        have kp : ∀ w : U64, P1.Aligned w → (TcbCW base.val (L.mem s DW) DW (i.val + 1) w ∨ w = CD) →
            L.mem s3 w = L.mem s2 w := by
          intro w hw hc
          refine hfr w hw (fun a ha hin => ?_)
          have hsa := hslw0 a ha
          rcases hc with (⟨j, hj, hr⟩ | ⟨hn, e⟩ | e) | e
          · unfold Rg at hr; rw [bT_v (win := win.val) (by omega) hfit] at hr
            have : (j + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ (by omega)
            have := hold a hsa; omega
          · exact tcbw_not_slot hP' (hh0 hn).2.1 (hext a hsa) (by rw [e, dpA_v (hh0 hn).1]; omega)
              (by rw [e, dpA_v (hh0 hn).1]; omega) hin
          · exact hDWout a (hext a hsa) (by rw [e] at hin; exact hin)
          · exact hCDs a (hext a hsa) (by rw [e] at hin; exact hin)
        exact ⟨hC2.1.keep (win := win.val) (by omega) hfit hal (fun hn => (hh0 hn).1) hDWal
          (fun w hw hc => kp w hw (Or.inl hc)), by rw [kp CD hCDal (Or.inr rfl)]; exact hC2.2⟩
      rw [hs3]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hL3, by rw [hi5]; exact hX3, hW3, Or.inr ⟨i.val, by omega, hD3⟩,
        by rw [hi5]; exact hC3.1, hC3.2, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI hC1
      exact ⟨rfl, hI, hXi.1, hW1, hC1, hCD1⟩
  · exact ⟨rfl, by simp, hinv, hX, WFrame.refl s _, Or.inl rfl, TcbC.zero rfl, rfl⟩


end

end

end Fl4Proofs.P3
