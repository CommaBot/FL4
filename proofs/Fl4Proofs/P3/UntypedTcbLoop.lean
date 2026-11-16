/-
P3 (DESIGN.md §9), untyped: **the object-creation loop for TCBs**.

Each round runs `create_object` for the next TCB (`create_tcb_frame`: it
writes only inside the new TCB past its slots, the old debug-list head's
`debug_prev` word and the core's list-head word) and then `insert_new_cap`
(`loop_step`). Besides `LoopInv`, the loop keeps `TcbX`: the TCBs not yet
created are still zero, every non-null slot is a slot of the old typed heap,
and the debug-list head word holds 0 or a TCB outside the region not yet
used.
-/
import Fl4Proofs.P3.UntypedTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A slot word is not inside a TCB's words past its slots. -/
theorem slot_word_not_tcb {th : TypedHeap} (hP : Placed th) {q : U64} (hq : th q = some .tcb) {a : U64}
    (ha : IsSlot th a) {k : U64} (hk : Off k) :
    ¬ (q.val + 256 ≤ (wordOf a k).val ∧ (wordOf a k).val < q.val + 4096) := by
  rw [slot_word_val hP ha hk]
  have := hk.lt
  obtain ⟨p, kd, hp, h1, h2, h3⟩ := slot_in_object hP ha
  by_cases hpq : p = q
  · subst hpq; rw [hq] at hp; cases hp
    have := h3 rfl; simp [tcbSlots] at this; omega
  · have e4 : objSize ObjKind.tcb = 4096 := rfl
    rcases hP.disj p q kd .tcb hp hq hpq with h | h <;> omega

theorem LoopInv.of_same {th' : TypedHeap} {srcSl : Fl4Spec.CslotPtr} {srcC : capability.Cap}
    {σ1 : Fl4Spec.State Unit} {f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit}
    {pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)} {A k win : Nat} {dslot : Nat → U64} {zlo zhi : Nat}
    {G0 : MdbGhost} {m0 : U64 → U64} {cj : Nat → capability.Cap}
    {s s' : S} {i : Nat}
    (hdsl : ∀ j, j < win → IsSlot th' (dslot j)) (hsrc : IsSlot th' (cslotAddr srcSl))
    (hiw : i ≤ win)
    (h : LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj s i)
    (hS : SlotsSame th' (L.mem s) (L.mem s'))
    (hz : ∀ w : U64, P1.Aligned w → zlo ≤ w.val → w.val < zhi → L.mem s' w = L.mem s w) :
    LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj s' i := by
  obtain ⟨σi, Gi, hchain, hR, hV, hM, hC, hI, hs, hnull, hno, hdd, hzr, hT1, hT1b, hT2a, hT2b, hT3, hFM, hCh, hRv⟩ := h
  have hcap : ∀ x, IsSlot th' x → capAt (L.mem s') x = capAt (L.mem s) x := fun x hx => hS.capAt hx
  have hsl : ∀ x, x ∈ Gi.chains.flatten → IsSlot th' x := fun x h => ((hM.members x).1 h).1
  refine ⟨σi, Gi, hchain, hR.of_caps hcap, hV.of_caps hcap, hM.of_same hS, hC.of_same hS rfl rfl,
    MdbInv.of_same hM hI hS, by rw [hcap _ hsrc]; exact hs,
    fun j h1 h2 => by rw [hcap _ (hdsl j h2)]; exact hnull j h1 h2, fun x hx hp => ?_, fun y hy => ?_,
    fun w hw h1 h2 => by rw [hz w hw h1 h2]; exact hzr w hw h1 h2, hT1, hT1b,
    fun j hj => by rw [hS.capV (hdsl j (by omega))]; exact hT2a j hj,
    fun x hx => by rw [hS.capV (hsl x (hT1b x hx))]; exact hT2b x hx, hT3,
    fun h0 => (hFM h0).of_caps hM.tree.nodup (fun x hx => hS.capV (hsl x hx)), hCh,
    fun x hx => by rw [hS.revOf (hsl x (hT1b x hx))]; exact hRv x hx⟩
  · rw [hS.capV (hsl x hx)] at hp ⊢; exact hno x hx hp
  · rw [hS.capV (hsl y (desc_mem hM hy).1)]; exact hdd y hy

/-- The loop's extra invariant for TCBs, after `i` of them. -/
def TcbX (th th' : TypedHeap) (ksb0 DW : U64) (A win zhi : Nat) (s : S) (i : Nat) : Prop :=
  L.ksb s = ksb0 ∧ ZeroRegion (L.mem s) (A + i * 4096) (A + win * 4096) ∧
  (∀ a, IsSlot th' a → (∃ c, capAt (L.mem s) a = ok c ∧ c ≠ .Null) → IsSlot th a) ∧
  (L.mem s DW = 0#u64 ∨ (th' (L.mem s DW) = some .tcb ∧ TcbOk (L.mem s DW) ∧
    ((L.mem s DW).val + 4096 ≤ A + i * 4096 ∨ zhi ≤ (L.mem s DW).val)))

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxRecDepth 20000 in
/-- **One TCB creation keeps the loop invariants**, with the new TCB now at the
head of the debug list. -/
theorem create_step {A' : Type} (arI : machine.Arch A') (ar : A') (th th' : TypedHeap) (hP' : Placed th')
    {srcSl : Fl4Spec.CslotPtr} {srcC : capability.Cap} {σ1 : Fl4Spec.State Unit}
    {f : Fl4Spec.CslotPtr × Fl4Spec.ObjRef → Fl4Spec.NonDet (Fl4Spec.State Unit) Unit}
    {pairs : List (Fl4Spec.CslotPtr × Fl4Spec.ObjRef)} {k : Nat} {dslot : Nat → U64} {zlo : Nat}
    {G0 : MdbGhost} {m0 : U64 → U64} {cj : Nat → capability.Cap}
    (ksb0 DW : U64) (A win zhi : Nat)
    (hDWal : P1.Aligned DW) (hDWout : ∀ a, IsSlot th' a → ¬ (a.val ≤ DW.val ∧ DW.val < a.val + 32))
    (hDWreg : ¬ (A ≤ DW.val ∧ DW.val < zhi))
    (hDW : ∀ s : S, L.ksb s = ksb0 → L.nodeAt s 0#u64 layout.node.DEBUG_TCBS = DW)
    (hzlo : zlo = A + win * 4096) (hzhi : A + win * 4096 ≤ zhi) (hfit : A + win * 4096 ≤ 2 ^ 64)
    (hal : A % 32 = 0) (hnew : ∀ i, i < win → th' ⟨BitVec.ofNat 64 (A + i * 4096)⟩ = some .tcb)
    (hdsl : ∀ j, j < win → IsSlot th' (dslot j)) (hsrc : IsSlot th' (cslotAddr srcSl))
    (nt us : U64) (dev : Bool) (hnt : nt.val = 1) (s : S) (i : Nat) (hi : i < win)
    (hL : LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj s i)
    (hX : TcbX (L := L) th th' ksb0 DW A win zhi s i) :
    objects.create_object st arI s ar nt ⟨BitVec.ofNat 64 (A + i * 4096)⟩ us dev ⦃ res =>
      res.1 = .Thread ⟨BitVec.ofNat 64 (A + i * 4096)⟩ ∧ res.2.2 = ar ∧
      LoopInv (L := L) th' srcSl srcC σ1 f pairs A k win dslot zlo zhi G0 m0 cj res.2.1 i ∧
      L.ksb res.2.1 = ksb0 ∧ ZeroRegion (L.mem res.2.1) (A + (i + 1) * 4096) (A + win * 4096) ∧
      (∀ a, IsSlot th' a → (∃ c, capAt (L.mem res.2.1) a = ok c ∧ c ≠ .Null) → IsSlot th a) ∧
      L.mem res.2.1 DW = ⟨BitVec.ofNat 64 (A + i * 4096)⟩ ⦄ := by
  obtain ⟨hksb, hz, hX2, hX3⟩ := hX
  set bi : U64 := ⟨BitVec.ofNat 64 (A + i * 4096)⟩ with hbi
  have hik : (i + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hi
  rw [Nat.add_mul, Nat.one_mul] at hik
  have hbiv : bi.val = A + i * 4096 := by show (BitVec.ofNat 64 (A + i * 4096)).toNat = _; simp; omega
  have htk : TcbOk bi := ⟨by rw [hbiv]; omega, by rw [hbiv]; omega⟩
  have hcpu : tcbCpu (L := L) s bi = 0#u64 := by
    unfold tcbCpu
    have hv : (core.num.U64.wrapping_add bi 3520#u64).val = A + i * 4096 + 3520 := by
      obtain ⟨h1, h2⟩ := htk; rw [← hbiv]; addr_tac
    exact hz _ (by unfold P1.Aligned; omega) (by omega) (by omega)
  have hdw : dbgW (L := L) s bi = DW := by unfold dbgW; rw [hcpu]; exact hDW s hksb
  have hnotInT : ∀ w : U64, InT bi w → A ≤ w.val ∧ w.val < A + (i + 1) * 4096 := by
    rintro w ⟨h1, h2, -⟩; rw [hbiv] at h1 h2; omega
  apply WP.spec_mono (create_tcb_frame (L := L) arI s ar nt bi us dev hnt htk (by rw [hdw]; exact hDWal)
    (by rw [hdw]; intro h; rcases hX3 with h' | ⟨-, h', -⟩; exact absurd h' h; exact h')
    (by rw [hdw]; intro h; exact hDWreg (by have := hnotInT DW h; omega)))
  rintro ⟨c, s', a'⟩ ⟨hc, ha, hf, hm⟩
  simp only at hc ha hf hm ⊢
  rw [hdw] at hm
  have hW : ∀ w, TcbW (L := L) s bi w →
      InT bi w ∨ (L.mem s DW ≠ 0#u64 ∧ w.val = (L.mem s DW).val + 3584) ∨ w.val = DW.val := by
    intro w h; unfold TcbW at h; rw [hdw] at h; exact h
  -- the head's word lies in an old TCB outside the region, or a new one already created
  have hhead : L.mem s DW ≠ 0#u64 → th' (L.mem s DW) = some .tcb ∧
      ((L.mem s DW).val + 4096 ≤ A + i * 4096 ∨ zhi ≤ (L.mem s DW).val) := by
    intro h; rcases hX3 with h' | ⟨h1, -, h2⟩
    · exact absurd h' h
    · exact ⟨h1, h2⟩
  have hSS : SlotsSame th' (L.mem s) (L.mem s') := by
    have key : ∀ a, IsSlot th' a → ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
      intro a ha k hk
      apply hf.2 _ (slot_word_aligned hP' ha hk)
      intro hw
      rcases hW _ hw with h | ⟨hne, he⟩ | he
      · exact slot_word_not_tcb hP' (hnew i hi) ha hk ⟨h.1, h.2.1⟩
      · obtain ⟨hq, -⟩ := hhead hne
        exact slot_word_not_tcb hP' hq ha hk (by rw [he]; omega)
      · have hv := slot_word_val hP' ha hk; have := hk.lt
        exact hDWout a ha (by rw [← he, hv]; omega)
    intro a ha
    refine ⟨?_, key a ha _ off8, key a ha _ off16, key a ha _ off24⟩
    have := key a ha _ off0; rwa [wordOf_zero] at this
  have hzf : ∀ lo, A + (i + 1) * 4096 ≤ lo → ∀ w : U64, P1.Aligned w → lo ≤ w.val → w.val < zhi →
      L.mem s' w = L.mem s w := by
    intro lo hlo w hw h1 h2
    apply hf.2 w hw
    intro hw'
    rcases hW _ hw' with h | ⟨hne, he⟩ | he
    · have := hnotInT w h; omega
    · rcases (hhead hne).2 with h' | h' <;> omega
    · exact hDWreg (by rw [← he]; omega)
  refine ⟨hc, ha, LoopInv.of_same hdsl hsrc (by omega) hL hSS
    (fun w hw h1 h2 => hzf zlo (by omega) w hw h1 h2), by rw [hf.1, hksb], fun w hw h1 h2 => ?_,
    fun a ha hc' => hX2 a ha (by rw [← hSS.capAt ha]; exact hc'), hm⟩
  rw [hzf (A + (i + 1) * 4096) le_rfl w hw h1 (by omega)]
  exact hz w hw (by omega) h2

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem insert_new_ksb (s : S) (src dest : U64) (c : capability.Cap) :
    cdt.insert_new_cap st s src dest c ⦃ s' => L.ksb s' = L.ksb s ⦄ := by
  unfold cdt.insert_new_cap
  have hsc : ∀ (s0 : S) sl c0, obj.Slot.set_cap st sl s0 c0 ⦃ s1 => L.ksb s1 = L.ksb s0 ⦄ := fun s0 sl c0 =>
    WP.spec_mono (set_cap_spec (L := L) sl s0 c0) (by rintro _ rfl; simp)
  step
  obtain ⟨s1, h1, k1⟩ := spec_exists (hsc s dest c)
  rw [h1]; simp only [bind_ok]
  step; step
  simp only [obj.Slot.is_null, bind_ok]
  by_cases hz0 : next = 0#u64
  · simp only [hz0, decide_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all
  · simp only [hz0, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    step*
    subst_vars; simp_all

set_option maxRecDepth 20000 in
/-- **An insertion keeps `TcbX`** (the inserted slot and its neighbours are
old slots, outside the region). -/
theorem tcbx_insert (th th' : TypedHeap) (hP' : Placed th') (hext : ∀ a, IsSlot th a → IsSlot th' a)
    (ksb0 DW : U64) (A win zhi : Nat) (hDWal : P1.Aligned DW)
    (hDWout : ∀ a, IsSlot th' a → ¬ (a.val ≤ DW.val ∧ DW.val < a.val + 32))
    (hold : ∀ a, IsSlot th a → a.val + 32 ≤ A ∨ zhi ≤ a.val) (hzhi : A + win * 4096 ≤ zhi)
    (hnew : ∀ i, i < win → th' ⟨BitVec.ofNat 64 (A + i * 4096)⟩ = some .tcb)
    (hfit : A + win * 4096 ≤ 2 ^ 64) (hal : A % 32 = 0)
    (s : S) (G : MdbGhost) (hM : MdbLinks th' (L.mem s) G) (src dest : U64)
    (hsrc : src ∈ G.chains.flatten) (hs : IsSlot th src) (hd : IsSlot th dest) (hdn : dest ∉ G.chains.flatten)
    (c : capability.Cap) (he : EncWf c) (i : Nat) (hi : i < win)
    (hksb : L.ksb s = ksb0) (hz : ZeroRegion (L.mem s) (A + (i + 1) * 4096) (A + win * 4096))
    (hX2 : ∀ a, IsSlot th' a → (∃ c, capAt (L.mem s) a = ok c ∧ c ≠ .Null) → IsSlot th a)
    (hm : L.mem s DW = ⟨BitVec.ofNat 64 (A + i * 4096)⟩) :
    cdt.insert_new_cap st s src dest c ⦃ s' => TcbX (L := L) th th' ksb0 DW A win zhi s' (i + 1) ⦄ := by
  have hs' := hext _ hs
  have hd' := hext _ hd
  have hne : src ≠ dest := fun e => hdn (e ▸ hsrc)
  have hnext : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th (nextOf (L.mem s) src) := by
    rcases hM.next_mem hsrc with h | ⟨h, -⟩
    · exact Or.inl h
    · obtain ⟨hsl, c0, hc0, hn0⟩ := (hM.members _).1 h
      exact Or.inr (hX2 _ hsl ⟨c0, hc0, hn0⟩)
  have hnx' : nextOf (L.mem s) src = 0#u64 ∨ IsSlot th' (nextOf (L.mem s) src) :=
    hnext.imp id (hext _)
  have hnx2 : nextOf (L.mem s) src = 0#u64 ∨
      (IsSlot th' (nextOf (L.mem s) src) ∧ nextOf (L.mem s) src ≠ dest ∧ nextOf (L.mem s) src ≠ src) := by
    rcases hM.next_mem hsrc with h | ⟨h, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨((hM.members _).1 h).1, fun e => hdn (e ▸ h), h2⟩
  obtain ⟨s1, h1, hfr⟩ := spec_exists (insert_new_frame (L := L) hP' s c src dest hs' hd' hnx')
  obtain ⟨s2, h2, hW⟩ := spec_exists (insert_new_mem (L := L) hP' s c src dest hs' hd' hne hnx2)
  obtain ⟨s3, h3, hk⟩ := spec_exists (insert_new_ksb (L := L) s src dest c)
  rw [h1] at h2 h3; cases eq_of_ok_eq h2; cases eq_of_ok_eq h3
  rw [h1, WP.spec_ok]
  have hout : ∀ w : U64, (A ≤ w.val ∧ w.val < zhi) ∨ w = DW →
      ∀ a, (a = src ∨ a = dest ∨ (nextOf (L.mem s) src ≠ 0#u64 ∧ a = nextOf (L.mem s) src)) →
        ¬ (a.val ≤ w.val ∧ w.val < a.val + 32) := by
    rintro w hw a ha
    have hoa : IsSlot th a := by
      rcases ha with rfl | rfl | ⟨hz0, rfl⟩
      · exact hs
      · exact hd
      · exact hnext.resolve_left hz0
    rcases hw with hw | rfl
    · have := hold a hoa; omega
    · exact hDWout a (hext a hoa)
  have hik : (i + 1) * 4096 ≤ win * 4096 := Nat.mul_le_mul_right _ hi
  refine ⟨by rw [hk, hksb], fun w hw h1 h2 => ?_, fun a ha hc => ?_, Or.inr ⟨?_, ?_, ?_⟩⟩
  · rw [hfr w hw (hout w (Or.inl ⟨by omega, by omega⟩))]; exact hz w hw (by omega) h2
  · rw [hW.capAt' ha he] at hc
    by_cases had : a = dest
    · rw [had]; exact hd
    · rw [if_neg had] at hc; exact hX2 a ha hc
  all_goals rw [hfr DW hDWal (hout DW (Or.inr rfl)), hm]
  · exact hnew i hi
  · have hbiv : (⟨BitVec.ofNat 64 (A + i * 4096)⟩ : U64).val = A + i * 4096 := by
      show (BitVec.ofNat 64 (A + i * 4096)).toNat = _; simp; omega
    exact ⟨by rw [hbiv]; omega, by rw [hbiv]; omega⟩
  · have hbiv : (⟨BitVec.ofNat 64 (A + i * 4096)⟩ : U64).val = A + i * 4096 := by
      show (BitVec.ofNat 64 (A + i * 4096)).toNat = _; simp; omega
    left; rw [hbiv]; omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxRecDepth 20000 in
/-- **`create_new_objects` for TCBs**: from the loop invariants at 0, the
invariant at `win`, the arch state unchanged. -/
theorem create_loop_rel_tcb {A' : Type} (arI : machine.Arch A') (ar : A') (th th' : TypedHeap) (hP' : Placed th')
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
    (s : S)
    (hinv : LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) s 0)
    (hX : TcbX (L := L) th th' ksb0 DW base.val win.val zhi s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1 win.val ∧
      L.ksb res.1 = ksb0 ⦄ := by
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
      TcbX (L := L) th th' ksb0 DW base.val win.val zhi x.1 x.2.2.val) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hXi⟩
    simp only at ha hiw hI hXi ⊢
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
      obtain ⟨σi, Gi, -, -, -, hM2, -, -, hsrc2, hnull2, -⟩ := id hI2
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
      rw [hs3]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hL3, by rw [hi5]; exact hX3, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hXi.1⟩
  · exact ⟨rfl, by simp, hinv, hX⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-! ## The TCB loop -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxRecDepth 20000 in
/-- **`create_new_objects`' write frame for TCBs** (`create_loop_rel_tcb`
with the frame `TcbLoopW`). -/
theorem create_loop_frame_tcb {A' : Type} (arI : machine.Arch A') (ar : A') (th th' : TypedHeap) (hP' : Placed th')
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
    (hX : TcbX (L := L) th th' ksb0 DW base.val win.val zhi s 0) :
    objects.create_new_objects st arI s ar nt (cslotAddr (pp.bv, idx)) dest off win base us dev ⦃ res =>
      res.2 = ar ∧ LoopInv (L := L) th' (pp.bv, idx) (.Untyped p sb fi d) σ1
      (Fl4Spec.createCap (Z := Unit) t us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 base.val) win.val (2 ^ zOf nt.val us.val)))
      base.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (base.val + win.val * 4096) zhi G0 m0 (cjOf nt.val us dev base.val (2 ^ zOf nt.val us.val)) res.1 win.val ∧
      L.ksb res.1 = ksb0 ∧ WFrame (L := L) s res.1 (TcbLoopW th base.val win.val DW (L.mem s DW)) ⦄ := by
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
      (L.mem x.1 DW = L.mem s DW ∨ ∃ j, j < x.2.2.val ∧ L.mem x.1 DW = ⟨BitVec.ofNat 64 (base.val + j * 4096)⟩)) _ _ _ ?_ ?_
  · rintro ⟨s1, a1, i⟩ ⟨ha, hiw, hI, hXi, hW1, hD1⟩
    simp only at ha hiw hI hXi hW1 hD1 ⊢
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
      obtain ⟨s3', hs3', hk3⟩ := spec_exists (insert_new_ksb (L := L) s2 (cslotAddr (pp.bv, idx))
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
        hW2.trans ⟨hk3, fun w hw hnp => hfr w hw (fun a ha hin => hnp (Or.inl ⟨a, hslw0 a ha, hin.1, hin.2⟩))⟩
      have hD3 : L.mem s3 DW = ⟨BitVec.ofNat 64 (base.val + i.val * 4096)⟩ := by
        rw [hfr DW hDWal (fun a ha hin => hDWout a (hslw a ha) hin)]; exact hm2
      rw [hs3]; simp only [bind_ok]
      step as ⟨i5, hi5⟩
      refine ⟨by omega, by rw [hi5]; exact hL3, by rw [hi5]; exact hX3, hW3, Or.inr ⟨i.val, by omega, hD3⟩, by omega⟩
    · rw [if_neg hit, WP.spec_ok]
      have : i.val = win.val := by have : ¬ i.val < win.val := hit; omega
      rw [this] at hI
      exact ⟨rfl, hI, hXi.1, hW1⟩
  · exact ⟨rfl, by simp, hinv, hX, WFrame.refl s _, Or.inl rfl⟩

end


/-- **`untyped::retype` (no reset) of TCBs refines FL4's `invoke_untyped`**
(4 KiB TCBs), as `retype_full` for the other types, with hypotheses on the
current core-0 debug list: its head word is aligned, outside the old slots and
the free region, and holds 0 or an old TCB. -/
theorem retype_full_tcb {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hnt : nt.val = 1) (hus : us.val < 64)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hDWal : P1.Aligned (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hDWobj : ∀ a, IsSlot th a → ¬ (a.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < a.val + 32))
    (hDWreg : ¬ (p.val + fi.val ≤ (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val ∧
      (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS).val < p.val + 2 ^ sb.val))
    (hhead : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨
      (th (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) = some .tcb ∧
        TcbOk (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G' th',
        (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev)).run σ = ({(.ok (), σ')}, False) ∧
        Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
        MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s) G (L.mem res.2.1) G') ∧ ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val)
          (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s) σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = L.ksb s ∧
        WFrame (L := L) s res.2.1 (TcbLoopW th (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat win.val
          (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))) ∧
        ∃ A k w dslot cj, RetExp th th' (L.mem s) (L.mem res.2.1) G G' A k w dslot cj ∧
          A = (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ∧ k = 2 ^ zOf nt.val us.val ∧ w = win.val ⦄ := by
  -- sizes and the region
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have htT : t = .tcbObject := by rw [hnt] at ht; simpa [objTypeOf] using ht.symm
  subst htT
  have hz12 : zOf nt.val us.val = 12 := by simp [zOf, hnt]
  set z := zOf nt.val us.val with hzdef
  have hz : z < 64 := by omega
  have hz47 : z ≤ 47 := by omega
  set k := 2 ^ z with hkdef
  have hk4 : k = 4096 := by rw [hkdef, hz12]; rfl
  have hk1 : 1 ≤ k := Nat.one_le_two_pow
  obtain ⟨hA1, hA2, hA3, hA4⟩ := retype_region p fi sb.val z win.val hsb hz hpal hpfit hfi hw1 hmem
  rw [← hkdef] at hA2 hA3 hA4
  set Ab := Fl4Spec.alignUp (p.bv + fi.bv) z with hAbdef
  set A := Ab.toNat with hAdef
  set aligned : U64 := ⟨Ab⟩ with halig
  have halv : aligned.val = A := rfl
  have hn14 : nt.val < 14 := by omega
  set src := cslotAddr (pp.bv, idx) with hsrcdef
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hs : IsSlot th src := hAs.isSlot
  have hsrcm : src ∈ G.chains.flatten := (hM.members src).2 ⟨hs, _, hcap, by simp⟩
  have hcv0 := capV_of_capAt hcap
  obtain ⟨hsb', hst'⟩ := topF_ut p sb fi dev hsb hpfit
  -- FL4: the cap update, then the loop
  obtain ⟨total, htot, hret⟩ := retype_noreset_eq (L := L) arI s ar src aligned nt us dest off win dev hn14 hus hz
    p sb fi dev hcap
  rw [hret]
  set nfi := core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p with hnfi
  set srcC' : capability.Cap := .Untyped p sb nfi dev with hsrcC'
  have he' : EncWf srcC' := by
    have : EncWf (capability.Cap.Untyped p sb fi dev) := by rw [capAt_words] at hcap; exact decode_encWf hcap
    exact ⟨this.1, this.2⟩
  obtain ⟨s1, hs1, hU1⟩ := spec_exists (set_cap_upd (L := L) hP s hs srcC' he')
  obtain ⟨s1', hs1', σa, hσa, hR1, hV1, hcdt1, hio1⟩ := spec_exists
    (retype_set_untyped_rel (L := L) th s σ hR hV hP hpp hidx hcap aligned total win z htot)
  rw [hs1] at hs1'; have e := eq_of_ok_eq hs1'; subst e
  rw [hs1]; simp only [bind_ok]
  obtain ⟨hcs1, hco1, hlk1, hfr1⟩ := hU1
  have hupd : CapShapeUpd th (L.mem s) (L.mem s1) src :=
    { links := hlk1, caps := hco1
      shp := by rw [hcs1, hcv0]; rfl
      bdg := by rw [hcs1, hcv0]; rfl
      nn := by rw [hcs1]; simp [srcC'] }
  have hM1 := hupd.mdbLinks hM hsrcm
  have hI1 := hupd.mdbInv hM hI
  have hC1 := hupd.cdtRel hC hcdt1 hio1
  -- the spec's pieces
  have hgs : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ = ({(.untypedCap dev p.bv sb.val fi.val, σ)}, False) := by
    obtain ⟨c, a, hc, hca, hg⟩ := hR.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
    rw [hg, hca.abs]; rfl
  have hwl : (windowSlots dest r off.val win.val).length = win.val := by simp [windowSlots]
  have hss : Fl4Spec.setCap (Z := Unit) (.untypedCap dev p.bv (Fl4Spec.bitsOf (.untypedCap dev p.bv sb.val fi.val))
      (Fl4Spec.unat (Ab + (BitVec.ofNat 64 (windowSlots dest r off.val win.val).length <<< bitsApi .tcbObject us.val) - p.bv)))
      (pp.bv, idx) σ = ({((), σa)}, False) := by
    rw [hwl, hb]; exact hσa
  have hrr := retypeRegionWith_eq bitsApi Ab win.val us.val .tcbObject dev σa
  rw [hb] at hrr
  rw [← hwl] at hrr
  -- the free region after the cap update
  have hzero1 : ZeroRegion (L.mem s1) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    have hne : w.val ≠ src.val ∧ w.val ≠ src.val + 8 := by
      rcases hfree q kq hq with h | h <;> constructor <;> omega
    rw [hfr1 w hw hne.1 hne.2]; exact hzero w hw h1 h2
  have hrf : RegionFree th A (A + win.val * k) := by
    intro q kd hq
    rcases hfree q kd hq with h | h
    · left; omega
    · right; omega
  have hnn : ∀ q kd, th q = some kd → 1 ≤ objSize kd → ¬ NewP A k win.val q :=
    fun q kd hq hs1 => not_newP hk1 hrf hq hs1
  -- the debug list
  set DW := L.nodeAt s 0#u64 layout.node.DEBUG_TCBS with hDWdef
  have hksb1 : L.ksb s1 = L.ksb s := by
    have : obj.Slot.set_cap st src s srcC' ⦃ s' => L.ksb s' = L.ksb s ⦄ :=
      WP.spec_mono (set_cap_spec (L := L) src s srcC') (by rintro _ rfl; simp)
    obtain ⟨s', h', h''⟩ := spec_exists this
    rw [hs1] at h'; cases eq_of_ok_eq h'; exact h''
  have hDW : ∀ s' : S, L.ksb s' = L.ksb s → L.nodeAt s' 0#u64 layout.node.DEBUG_TCBS = DW :=
    fun s' h => nodeAt_ksb h _ _
  have hDWm : L.mem s1 DW = L.mem s DW := by
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hs
    apply hfr1 DW hDWal
    · intro e; exact hDWobj src hs (by omega)
    · intro e; exact hDWobj src hs (by omega)
  have hfitA : A + win.val * 4096 ≤ 2 ^ 64 := by rw [← hk4]; omega
  have hA3' : A + win.val * 4096 ≤ p.val + 2 ^ sb.val := by rw [← hk4]; exact hA3
  have hal : A % 32 = 0 := by
    have h32 : 32 ∣ k := by rw [hk4]; decide
    exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h32 (Nat.dvd_of_mod_eq_zero hA2))
  have hrf4 : RegionFree th A (A + win.val * 4096) := by rw [← hk4]; exact hrf
  have hzero4 : ZeroRegion (L.mem s1) A (A + win.val * 4096) :=
    fun w hw h1 h2 => hzero1 w hw (by omega) (by rw [← hk4] at h2; omega)
  have hio1' : ∀ sl, σa.isOriginalCap sl = true → AbsSlot th sl := by rw [hio1]; exact horig
  obtain ⟨hP', hR', hV', hM', hC'⟩ := extend_tcb_rel th (L.mem s1) σa G hR1 hV1 hP hM1 hC1 hio1' Ab A win.val rfl
    σa.curDomain hfitA (by omega) hal hrf4 hzero4
  set th' := extendTh th A 4096 win.val .tcb with hth'
  have hext : ∀ a, IsSlot th a → IsSlot th' a := fun a ha => ha.extend (by omega) hrf4
  have hold : ∀ a, IsSlot th a → a.val + 32 ≤ A ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hnewP : ∀ i, i < win.val → NewP A 4096 win.val ⟨BitVec.ofNat 64 (A + i * 4096)⟩ := by
    intro i hi; refine ⟨i, hi, ?_⟩
    show (BitVec.ofNat 64 (A + i * 4096)).toNat = _
    have : i * 4096 < win.val * 4096 := Nat.mul_lt_mul_of_pos_right hi (by omega)
    simp; omega
  have hnew : ∀ i, i < win.val → th' ⟨BitVec.ofNat 64 (A + i * 4096)⟩ = some .tcb :=
    fun i hi => extendTh_new (hnewP i hi)
  have hnewslot : ∀ a, IsSlot th' a → ¬ IsSlot th a → ∃ q j, NewP A 4096 win.val q ∧ j < tcbSlots ∧ a = slotOf q j := by
    rintro a ⟨q, j, hj, rfl⟩ hn
    rcases hj.of_extend_tcb with hj | ⟨hq, hjl⟩
    · exact absurd ⟨q, j, hj, rfl⟩ hn
    · exact ⟨q, j, hq, hjl, rfl⟩
  have hnewv : ∀ q j, NewP A 4096 win.val q → j < tcbSlots →
      A ≤ (slotOf q j).val ∧ (slotOf q j).val + 32 ≤ A + win.val * 4096 ∧ (slotOf q j).val % 32 = 0 := by
    rintro q j ⟨i, hi, hqi⟩ hj
    have h1 : (i + 1) * 4096 ≤ win.val * 4096 := Nat.mul_le_mul_right _ hi
    rw [Nat.add_mul, Nat.one_mul] at h1
    simp [tcbSlots] at hj
    have hv : (slotOf q j).val = q.val + 32 * j := slotOf_val (by omega)
    rw [hv]; omega
  have hzs : ∀ a, IsSlot th' a → a.val + 32 ≤ A + win.val * 4096 ∨ p.val + 2 ^ sb.val ≤ a.val := by
    intro a ha
    by_cases ho : IsSlot th a
    · rcases hold a ho with h | h
      · left; omega
      · right; exact h
    · obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      left; exact (hnewv q j hq hj).2.1
  have hDWout : ∀ a, IsSlot th' a → ¬ (a.val ≤ DW.val ∧ DW.val < a.val + 32) := by
    intro a ha
    by_cases ho : IsSlot th a
    · exact hDWobj a ho
    · obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      have := hnewv q j hq hj
      intro h; exact hDWreg (by omega)
  have hsrc1 : capAt (L.mem s1) src = ok srcC' := by rw [capAt_capV, hcs1]
  have hsrcd : ∀ j, j < win.val → src ≠ slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) := by
    intro j hj e
    have := hempty (off.val + j) (by omega) (by omega)
    rw [← e, hcap] at this; cases eq_of_ok_eq this
  have hbA : (BitVec.ofNat 64 aligned.val : BitVec 64) = Ab := by rw [← bv_eq_ofNat]
  have hinv0 : LoopInv (L := L) th' (pp.bv, idx) srcC' (regionHeap σa (regionPtrs Ab win.val 4096)
        (.tcb (Fl4Spec.defaultTcb σa.curDomain)))
      (Fl4Spec.createCap (Z := Unit) .tcbObject us.val (pp.bv, idx) dev)
      ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val (2 ^ zOf nt.val us.val)))
      aligned.val (2 ^ zOf nt.val us.val) win.val (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)))
      (aligned.val + win.val * 4096) (p.val + 2 ^ sb.val) G (L.mem s1)
      (cjOf nt.val us dev aligned.val (2 ^ zOf nt.val us.val)) s1 0 := by
    refine ⟨_, G, fun σf h => h, hR', hV', hM', hC', hI1, hsrc1, ?_, ?_, ?_,
      fun w hw h1 h2 => hzero1 w hw (by omega) h2, fun x hx => Or.inl hx, fun x hx => hx,
      fun j hj => absurd hj (by omega), fun x _ => rfl, fun y x => ⟨Or.inl, by
        rintro (h | ⟨j, hj, -⟩)
        · exact h
        · omega⟩, fun h => h, fun ch hch => ⟨ch, hch, fun z hz => hz⟩, fun x _ => rfl⟩
    · intro j _ hj
      have hj' : off.val + j < 2 ^ r := by omega
      have hd : IsSlot th (slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) :=
        ⟨dest, off.val + j, Or.inl ⟨r, hdest, hj'⟩, rfl⟩
      have hnull := hempty (off.val + j) (by omega) (by omega)
      have hne : slotAddr dest.bv (BitVec.ofNat 64 (off.val + j)) ≠ src := by
        intro e; rw [e, hcap] at hnull; cases eq_of_ok_eq hnull
      rw [capAt_capV, hco1 _ hd hne, ← capAt_capV]; exact hnull
    · intro x hx hp
      have hxs : IsSlot th x := ((hM.members x).1 hx).1
      by_cases hxa : x = src
      · subst hxa
        rw [hcs1]
        refine ⟨?_, Or.inr ⟨rfl, ⟨le_refl _, le_refl _⟩⟩⟩
        obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
        rw [e1, e2, hsb', hst']; have := Nat.one_le_two_pow (n := sb.val); omega
      · rw [hco1 x hxs hxa] at hp ⊢
        refine ⟨hU.reg x hx hp, ?_⟩
        rcases hU.noov src hsrcm p sb fi dev hcv0 x hx hp with h | ⟨hu, hw⟩
        · left; unfold DisjR at h ⊢; simp only [Nat.zero_mul, Nat.add_zero, show 2 ^ zOf nt.val us.val = 4096 from hk4]
          omega
        · right; refine ⟨hu, ?_⟩
          obtain ⟨e1, e2, -⟩ := range_of_shape (show shape srcC' = shape (capability.Cap.Untyped p sb fi dev) from rfl)
          unfold Within at hw ⊢; rw [hcv0] at hw; rw [e1, e2]; exact hw
    · intro y hy
      obtain ⟨hp1, hp2, hp3⟩ := hU.inc src hsrcm p sb fi dev hcv0 y hy
      have hym := (desc_mem hM hy).1
      have hys : IsSlot th y := ((hM.members y).1 hym).1
      have hya : y ≠ src := by
        intro e; subst e
        rw [hcv0, hst'] at hp3
        have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
          rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
          simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
          have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
          rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
            rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
          omega
        rw [this, Nat.shiftRight_eq_div_pow, show 2 ^ sb.val - fi.val = 0 by omega] at hmem
        simp at hmem; omega
      rw [hco1 y hys hya]
      unfold DisjR; left; simp only [Nat.zero_mul, Nat.add_zero]; omega
  have hX0 : TcbX (L := L) th th' (L.ksb s) DW aligned.val win.val (p.val + 2 ^ sb.val) s1 0 := by
    refine ⟨hksb1, by rw [halv]; simpa using hzero4, ?_, ?_⟩
    · intro a ha ⟨c, hc, hcn⟩
      by_contra ho
      obtain ⟨q, j, hq, hj, rfl⟩ := hnewslot a ha ho
      obtain ⟨h1, h2, h3⟩ := hnewv q j hq hj
      have hz0 : ∀ w : U64, w.val = (slotOf q j).val ∨ w.val = (slotOf q j).val + 8 → L.mem s1 w = 0#u64 := by
        intro w hw
        have : w.val % 8 = 0 := by omega
        exact hzero4 w this (by omega) (by omega)
      rw [capAt_words, hz0 _ (Or.inl (by rw [wordOf_zero])), hz0 _ (Or.inr (by
        rw [wordOf_val (by have : (8#u64 : U64).val = 8 := rfl; omega)]; rfl))] at hc
      rw [decode_encode_null.2] at hc; exact hcn (eq_of_ok_eq hc).symm
    · rw [hDWm]
      rcases hhead with h | ⟨h1, h2⟩
      · exact Or.inl h
      · refine Or.inr ⟨(extendTh_of_old (by omega) hrf4 h1 objSize_pos_tcb).trans h1, h2, ?_⟩
        have e4 : objSize ObjKind.tcb = 4096 := rfl
        rcases hfree _ _ h1 with h | h
        · left; simp only [Nat.zero_mul, Nat.add_zero]; omega
        · right; exact h
  obtain ⟨⟨s2, a2⟩, hres, ha2, hfin, hks2, hW2⟩ := spec_exists (create_loop_frame_tcb (L := L) arI ar th th' hP' hext
    ((extendTh_of_old (by omega) hrf4 hpp (objSize_pos_cnode _)).trans hpp) hidx hs hsb hpfit _
    ((extendTh_of_old (by omega) hrf4 hdest (objSize_pos_cnode _)).trans hdest) hdest (by omega)
    nt us dev .tcbObject ht hnt hus off win aligned hwin (by rw [halv]; omega) (by rw [halv]; omega)
    (by rw [halv]; exact hal) (by rw [halv]; omega) (by rw [halv]; rw [← hk4]; omega)
    (by rw [halv]; exact hnew) (p.val + 2 ^ sb.val) (by rw [halv]; rw [← hk4]; omega)
    (by rw [halv]; exact hzs) (by rw [halv]; exact hold) (L.ksb s) DW hDWal hDWout
    (by rw [halv]; omega) hDW G (L.mem s1) hsrcd (fun x hx => ((hM.members x).1 hx).1) s1 hinv0 hX0)
  rw [hres]
  simp only [bind_ok, uncurry_apply_pair]
  rw [WP.spec_ok]
  simp only at ha2 hfin
  obtain ⟨σf, Gf, hchain, hRf, hVf, hMf, hCf, hIf, -, -, -, -, hZf, hT1, hT1b, hT2a, hT2b, hT3, hFf, hChf, hRvf⟩ := hfin
  have hdrop : ((windowSlots dest r off.val win.val).zip (regionPtrs (BitVec.ofNat 64 aligned.val) win.val
      (2 ^ zOf nt.val us.val))).drop win.val = [] := by
    apply List.drop_of_length_le; simp [windowSlots, regionPtrs]
  rw [hdrop] at hchain
  have hmx := hchain σf (mapMx_nil _ _)
  have hfiL : fi.val < 2 ^ sb.val := by
    have : (1#64 <<< sb.val - fi.bv : BitVec 64).toNat = 2 ^ sb.val - fi.val := by
      rw [BitVec.toNat_sub, BitVec.toNat_shiftLeft]
      simp only [BitVec.toNat_ofNat, Nat.shiftLeft_eq, show fi.bv.toNat = fi.val from rfl]
      have hM' : 2 ^ sb.val < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsb
      rw [show (1 % 2 ^ 64 * 2 ^ sb.val) % 2 ^ 64 = 2 ^ sb.val by
        rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, Nat.one_mul, Nat.mod_eq_of_lt hM']]
      omega
    rw [this, Nat.shiftRight_eq_div_pow] at hmem
    by_contra hc
    rw [show 2 ^ sb.val - fi.val = 0 by omega] at hmem; simp at hmem; omega
  have hnfiv : nfi.val = A + win.val * k - p.val := by
    rw [← hA4]
    show (core.num.U64.wrapping_sub (core.num.U64.wrapping_add aligned total) p).bv.toNat = _
    rw [core.num.U64.wrapping_sub_bv_eq, core.num.U64.wrapping_add_bv_eq, htot, ← bv_eq_ofNat]
  have hzv : zOf nt.val us.val < 64 := by omega
  have hkk : 2 ^ zOf nt.val us.val = k := rfl
  have hRD : RetypeDelta th (L.mem s) (L.mem s1) (L.mem s2) G Gf src p sb fi nfi dev A k win.val
        (fun j => slotAddr dest.bv (BitVec.ofNat 64 (off.val + j))) (cjOf nt.val us dev aligned.val k) := by
      refine ⟨hM, hsrcm, hcv0, hcs1, fun x hx hxs => hco1 x ((hM.members x).1 hx).1 hxs, hfiL, hA1,
        by omega, by omega, by omega, fun j _ => physF_newCap _ _ _ _, fun j hj => ?_, fun j hj => ?_,
        fun j hj hu => ?_, fun j hj hm => ?_, fun j l hj hl he => ?_, hT1, hT1b, hT2a, hT2b, hT3⟩
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨c1, -⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c1]; show (BitVec.ofNat 64 (A + j * k)).toNat = _; simp; omega
      · have h1 : (j + 1) * k ≤ win.val * k := Nat.mul_le_mul_right _ hj
        rw [Nat.add_mul, Nat.one_mul] at h1
        obtain ⟨-, c2⟩ := newCap_range (n := nt.val) (by omega) ⟨BitVec.ofNat 64 (A + j * k)⟩ us dev hus hzv
          (by show (BitVec.ofNat 64 (A + j * k)).toNat + _ ≤ _; rw [hkk]; simp; omega)
        unfold cjOf; rw [halv, c2]; show (BitVec.ofNat 64 (A + j * k)).toNat + _ - 1 = _; simp; omega
      · unfold cjOf at hu ⊢
        rw [halv] at hu ⊢
        obtain ⟨hn0, he⟩ := isUt_newCap hu
        refine ⟨us, dev, he, ?_⟩
        show 2 ^ us.val = 2 ^ zOf nt.val us.val
        simp [zOf, hn0]
      · obtain ⟨-, c0, h0, hn0⟩ := (hM.members _).1 hm
        rw [hempty (off.val + j) (by omega) (by omega)] at h0
        exact hn0 (eq_of_ok_eq h0).symm
      · have hj' : IsSlotAt th dest (off.val + j) := Or.inl ⟨r, hdest, by omega⟩
        have hl' : IsSlotAt th dest (off.val + l) := Or.inl ⟨r, hdest, by omega⟩
        by_contra hne
        rcases hj'.apart hP hl' (fun ⟨_, h2⟩ => hne (by omega)) with h | h <;>
          (change slotOf dest (off.val + j) = slotOf dest (off.val + l) at he; rw [he] at h; omega)
  have hth' : ∀ q kd, th' q = some kd → (th q = some kd ∧ (NewQ A k win.val (cjOf nt.val us dev aligned.val k) q →
      objSize kd = 0)) ∨ (NewQ A k win.val (cjOf nt.val us dev aligned.val k) q ∧ objSize kd ≤ k) := by
    rw [hk4]
    refine extendTh_shape (by omega) hrf4 (le_refl _) fun j _ => ?_
    cases hu : isUt (cjOf nt.val us dev aligned.val 4096 j)
    · rfl
    · exact absurd (isUt_newCap (by unfold cjOf at hu; exact hu)).1 (by omega)
  have hW : WFrame (L := L) s s2 (TcbLoopW th A win.val DW (L.mem s DW)) := by
    have hs' : IsSlot th src := hs
    obtain ⟨s1k, hs1k, k1⟩ := spec_exists (set_cap_ksb (L := L) src s srcC')
    rw [hs1] at hs1k; cases eq_of_ok_eq hs1k
    have hd1 : L.mem s1 DW = L.mem s DW := hfr1 DW hDWal (fun e => hDWobj src hs ⟨by omega, by omega⟩)
      (fun e => hDWobj src hs ⟨by omega, by omega⟩)
    rw [hd1] at hW2
    refine WFrame.trans (s2 := s1) ⟨k1, fun w hw hn => hfr1 w hw (fun e => hn (Or.inl ⟨src, hs', by omega, by omega⟩))
      (fun e => hn (Or.inl ⟨src, hs', by omega, by omega⟩))⟩ hW2
  refine ⟨rfl, ha2, σf, Gf, th', ?_, hP', hRf, hVf, hMf, hCf, hIf, ?_, ?_, fun hFI => ⟨?_, ?_⟩, by rw [hks2],
    hW, A, k, win.val, _, _, hRD.toExp hU hMf hth', rfl, rfl, rfl⟩
  rotate_right 2
  · exact (ktyped_region (hFI.kt.sub (ksub_of_eq (nks_setCap _ _) hσa)) Ab A win.val 4096 rfl (by omega) hfitA hrf4
      (fun q kd hq hs => extendTh_of_old (by omega) hrf4 hq hs) _
      (fun q hq => ⟨fun r cs he _ => (by cases he), fun t _ => extendTh_new hq⟩)).sub
      (ksub_of_eq (nks_mapMx (nks_createCap _ _ _ _) _) hmx)
  · exact hFf (hFI.fm.recap hM.tree.nodup src (by rw [hcs1, hcv0]; exact CapSim.of_shape rfl rfl)
      (fun z hz hzs => hco1 z ((hM.members z).1 hz).1 hzs))
  · rw [hbA] at hmx
    have hrb : Fl4Spec.retypeRegionWith (Z := Unit) bitsApi Ab (windowSlots dest r off.val win.val).length us.val
        .tcbObject dev σa = ({(regionPtrs Ab (windowSlots dest r off.val win.val).length 4096,
          regionHeap σa (regionPtrs Ab win.val 4096) (.tcb (Fl4Spec.defaultTcb σa.curDomain)))}, False) := by
      rw [hrr]; simp only [ne_eq, reduceCtorEq, not_false_eq_true, ↓reduceIte, hwl]
      rw [show 2 ^ z = 4096 from hk4]; rfl
    apply invokeUntyped_noreset_eq bitsApi (pp.bv, idx) p.bv Ab .tcbObject us.val _ dev σ σa _ σf _ _ hgs hss hrb
    · simp
    · rw [hwl]; rw [show 2 ^ zOf nt.val us.val = 4096 from hk4] at hmx; exact hmx
  · -- the untyped invariant
    exact ⟨hRD.utinv hU, MdbStep.retype hRD hI hChf
        (fun z hz => by rw [hRvf z hz, hupd.rv ((hM.members z).1 hz).1])
          (cjOf_vplaced rfl hA2 (by omega) (by omega))⟩
  · rw [← hk4] at hZf; exact hZf

end

end

end Fl4Proofs.P3
