/-
P3 (line mmuAD, gen 42b10): **the EPT table map's perform at `EptCore`** — FL4's `s.write(e, paddr(ptr) | 7)` and
`set_cap` of the mapped cap (crates/fl4-core/src/ept.rs l. 300-310) against the spec's `.tableMap` perform
(Fl4Spec/Ext/VirtEptInv l. 221-223: `storeGuestEntry tbl i (GuestPte.encode virtKind (.table (addrFromPPtr ptr)))`,
then `setCap (eptCap ptr level (some (asid, gpa)))`), the guest-table record after it.

* Address bits: `mask_toNat`, `gKey_getLsbD` (bit `i` of `gKey x l` is bit `i` of `x` when `l ≤ i`),
  `guestIndex_getLsbD`, **`gKey_step`** (the address bits above `l + 9` and the index at `l` give the address bits
  above `l`), `gKey_idem`, `gKey_hi` (an address below `2^47` has no bit at or above 47).
* Paths: `GPath.zero` (a level-0 path is a tagged root), **`GPath.store`** (a path after one entry write is a path
  before, or the path to the written table followed by the new entry, when the new entry names a zero table).
* **`EptNamed.tableMap`**: `EptNamed` across the table map (spec side the entry write, FL4 side the slot rewrite).
  The new table `ptr` was unreachable (`EptNamed.unmUnreach`; at level 0 `UnmappedEmpty`'s tag clause), so every new
  path ends at `ptr` through the written table `t`; every path to `t` has the decoded path's ASID and address bits
  above `t`'s level (`t`'s mapped cap matches both by `EptNamed.ex` / `all`; for the root `PoolInj.root`), so the
  rewritten cap `Ept ptr level true asid gpa` matches every path to `ptr` (`gKey_step`).
* `EptWalk.cnK`, `EptNamed.cnK`: the walk and named fields across the spec's slot write (`CnK`: arch objects and the
  ASID table kept).
* **`EptCore.tableMap`**: `EptCore X XL th s' σ'` after the table map, from `EptCore` before, the decoded path
  (`MapDecOut`'s `GPath` at the cap's ASID and masked guest address), the unmapped `Ept ptr level` cap at `dest`, the
  FL4 writes (the entry word related to the spec entry, `EptWord`; the rest off the tables of `X`; `dest` rewritten
  mapped, every other slot kept) and the spec's two steps (`storeGuestEntry` at `σ1`, then a `CnK` step to `σ'`).
  `UnmappedEmpty` after (the written table is reachable, so not an unmapped cap's table; `dest`'s table now mapped),
  `EptSlotOK` (`dest` held an unmapped cap, so it is no TCB's `SLOT_EPT`), `EptWalk` (P3/EptLookup's `EptWalk.store`:
  the new entry names the zero table `ptr` one level down) and `EptNamed` (above) are proved.

No named premise. New file only; root import after `P3.EptFrameEnc`.
-/
import Fl4Proofs.P3.EptFrameEnc
import Fl4Proofs.P3.EptDelRoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Address bits -/

theorem mask_toNat {l : Nat} (hl : l < 64) : (((1 : Fl4Spec.Word) <<< l) - 1).toNat = 2 ^ l - 1 := by
  obtain ⟨p1, p2⟩ := zv_pow64 hl
  have e1 : ((1 : Fl4Spec.Word) <<< l).toNat = 2 ^ l := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, show (1 : BitVec 64).toNat = 1 by decide, Nat.one_mul]
    exact Nat.mod_eq_of_lt p2
  rw [BitVec.toNat_sub, e1]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have h1 : (1 : BitVec 64).toNat = 1 := by decide
  rw [h1]
  rw [h64] at p2 ⊢
  generalize 2 ^ l = X at p1 p2 ⊢
  omega

theorem gKey_getLsbD (x : Fl4Spec.Word) {l i : Nat} (hl : l < 64) (hi : i < 64) :
    (gKey x l).getLsbD i = (x.getLsbD i && decide (l ≤ i)) := by
  have hm : (((1 : Fl4Spec.Word) <<< l) - 1).getLsbD i = decide (i < l) := by
    rw [← BitVec.testBit_toNat, mask_toNat hl, Nat.testBit_two_pow_sub_one]
  unfold gKey
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, hm]
  by_cases h : l ≤ i
  · have h' : ¬ i < l := by omega
    simp [hi, h, h']
  · have h' : i < l := by omega
    simp [hi, h, h']

theorem guestIndex_getLsbD (x : Fl4Spec.Word) (l : Nat) {j : Nat} (hj : j < 9) :
    (Fl4Spec.guestIndex x l).getLsbD j = x.getLsbD (l + j) := by
  unfold Fl4Spec.guestIndex
  rw [BitVec.getLsbD_ofNat, show (512 : Nat) = 2 ^ 9 by norm_num, Nat.testBit_mod_two_pow,
    BitVec.testBit_toNat, BitVec.getLsbD_ushiftRight]
  simp [hj]

/-- **The address bits above `l` from those above `l + 9` and the index at `l`.** -/
theorem gKey_step {x y : Fl4Spec.Word} {l : Nat} (hl : l + 9 < 64) (h1 : gKey x (l + 9) = gKey y (l + 9))
    (h2 : Fl4Spec.guestIndex x l = Fl4Spec.guestIndex y l) : gKey x l = gKey y l := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [gKey_getLsbD x (by omega) hi, gKey_getLsbD y (by omega) hi]
  by_cases hli : l ≤ i
  · by_cases h9 : l + 9 ≤ i
    · have : (gKey x (l + 9)).getLsbD i = (gKey y (l + 9)).getLsbD i := by rw [h1]
      rw [gKey_getLsbD x hl hi, gKey_getLsbD y hl hi] at this
      simpa [h9, hli] using this
    · have : (Fl4Spec.guestIndex x l).getLsbD (i - l) = (Fl4Spec.guestIndex y l).getLsbD (i - l) := by rw [h2]
      rw [guestIndex_getLsbD x l (by omega), guestIndex_getLsbD y l (by omega),
        show l + (i - l) = i by omega] at this
      simp [this]
  · simp [hli]

theorem gKey_idem (x : Fl4Spec.Word) {l l' : Nat} (hl : l' < 64) (hll : l ≤ l') :
    gKey (gKey x l) l' = gKey x l' := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [gKey_getLsbD _ hl hi, gKey_getLsbD _ (by omega) hi, gKey_getLsbD _ hl hi]
  by_cases h : l' ≤ i
  · have : l ≤ i := by omega
    simp [h, this]
  · simp [h]

/-- An address below `2^47` has no address bits at or above 48. -/
theorem gKey_hi {x y : Fl4Spec.Word} (hx : x.toNat < 2 ^ 47) (hy : y.toNat < 2 ^ 47) : gKey x 48 = gKey y 48 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [gKey_getLsbD x (by omega) hi, gKey_getLsbD y (by omega) hi]
  by_cases h : 48 ≤ i
  · have p : 2 ^ 47 ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, Nat.testBit_eq_false_of_lt (show x.toNat < 2 ^ i by omega),
      Nat.testBit_eq_false_of_lt (show y.toNat < 2 ^ i by omega)]
  · simp [h]

/-! ## Paths across one entry write -/

/-- A level-0 path is a tagged root of its ASID. -/
theorem GPath.zero {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {gpa : Fl4Spec.Word} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo gpa 0 u) :
    ∃ e, PoolAt σ hi lo e ∧ e &&& 1 = 1 ∧ u = Fl4Spec.asidEntryRoot e := by
  have key : ∀ l u, GPath σ hi lo gpa l u → l = 0 → ∃ e, PoolAt σ hi lo e ∧ e &&& 1 = 1 ∧
      u = Fl4Spec.asidEntryRoot e := by
    intro l u h
    induction h with
    | root hp h1 => exact fun _ => ⟨_, hp, h1, rfl⟩
    | step _ _ hc _ _ =>
      intro e0
      subst e0
      rcases eptChild_cases hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact absurd h (by decide)
  exact key 0 u h rfl

/-- **Paths after one entry write** (`storeGuestEntry tb i e`, the other objects and the ASID table kept) whose new
walked entry names a zero table: a path before, or the path to `tb` followed by the new entry. -/
theorem GPath.store {σ σ' : Fl4Spec.State Unit} {tb : Fl4Spec.ObjRef} {l0 : Nat} {es0 : BitVec 9 → Fl4Spec.Word}
    (hk : σ.kheap tb = some (.archObj (.ept l0 es0))) {i : BitVec 9} {e : Fl4Spec.Word}
    (hk' : σ'.kheap tb = some (.archObj (.ept l0 (Function.update es0 i e))))
    (hoth : ∀ r, r ≠ tb → σ'.kheap r = σ.kheap r)
    (hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable)
    (hz : ∀ c, eptChild l0 = some c →
      σ.kheap (Fl4Spec.ptrFromPAddr (e &&& Fl4Spec.guestPteAddress)) = some (.archObj (.ept c fun _ => 0)))
    {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex} {gpa : Fl4Spec.Word} {l : Nat}
    {u : Fl4Spec.ObjRef} (h : GPath σ' hi lo gpa l u) :
    GPath σ hi lo gpa l u ∨ (eptChild l0 = some l ∧ u = Fl4Spec.ptrFromPAddr (e &&& Fl4Spec.guestPteAddress) ∧
      GPath σ hi lo gpa l0 tb ∧ Fl4Spec.guestIndex gpa l = i) := by
  -- the new target is not `tb` (levels differ)
  have hne : ∀ c, eptChild l0 = some c → Fl4Spec.ptrFromPAddr (e &&& Fl4Spec.guestPteAddress) ≠ tb := by
    intro c hc e'
    have h1 := hz c hc
    rw [e', hk] at h1
    cases h1
    rcases eptChild_cases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  induction h with
  | root hp h1 =>
    obtain ⟨p, f, g1, g2, g3⟩ := hp
    have hpt : p ≠ tb := fun e' => by subst e'; rw [hk'] at g2; cases g2
    exact Or.inl (.root ⟨p, f, by rw [← hat]; exact g1, by rw [← hoth p hpt]; exact g2, g3⟩ h1)
  | @step l c t es _ hkt hc hw ih =>
    rcases ih with ih | ⟨hc0, rfl, -, -⟩
    · by_cases htb : t = tb
      · subst htb
        rw [hk'] at hkt
        injection hkt with hkt; injection hkt with hkt; injection hkt with hl hes; subst hl; subst hes
        by_cases hji : Fl4Spec.guestIndex gpa c = i
        · right
          refine ⟨hc, ?_, ih, hji⟩
          rw [hji, Function.update_self]
        · left
          have hw0 : GWalkE l0 es0 (Fl4Spec.guestIndex gpa c) := by
            obtain ⟨a1, a2, a3, a4⟩ := hw
            rw [Function.update_of_ne hji] at a3 a4
            exact ⟨a1, a2, a3, a4⟩
          rw [Function.update_of_ne hji]
          exact .step ih hk hc hw0
      · rw [hoth t htb] at hkt
        exact Or.inl (.step ih hkt hc hw)
    · have hz0 := hz l hc0
      rw [hoth _ (hne l hc0), hz0] at hkt
      cases hkt
      exact (gWalkE_zero hw).elim

/-! ## `EptNamed` across the table map -/

set_option maxHeartbeats 4000000 in
/-- **`EptNamed` across the table map** (module docstring): the spec's entry write at `σ1` (the new entry names the
zero table `ptr` one level below `t`), FL4's `dest` rewritten from the unmapped `Ept ptr lv` cap to the mapped cap at
the decoded path's ASID and masked address, every other slot kept. -/
theorem EptNamed.tableMap {th : TypedHeap} {m m' : U64 → U64} {σ σ1 : Fl4Spec.State Unit} (N : EptNamed th m σ)
    {t : Fl4Spec.ObjRef} {lk : Nat} {es0 : BitVec 9 → Fl4Spec.Word}
    (hk : σ.kheap t = some (.archObj (.ept lk es0))) {idx : BitVec 9} {e : Fl4Spec.Word}
    (hk1 : σ1.kheap t = some (.archObj (.ept lk (Function.update es0 idx e))))
    (hoth : ∀ r, r ≠ t → σ1.kheap r = σ.kheap r)
    (hat : σ1.archState.x64AsidTable = σ.archState.x64AsidTable)
    {ptr lv asid0 va0 asid1 g' : U64} (htg : Fl4Spec.ptrFromPAddr (e &&& Fl4Spec.guestPteAddress) = ptr.bv)
    (hch : eptChild lk = some lv.val) (hptrz : σ.kheap ptr.bv = some (.archObj (.ept lv.val fun _ => 0)))
    {dest : U64} (hd : IsSlot th dest) (hdc : capV m dest = .Ept ptr lv false asid0 va0)
    (huq : ∀ y, IsSlot th y → y ≠ dest → ∀ l (mm : Bool) a v, capV m y ≠ .Ept ptr l mm a v)
    (hroot : ∀ hi lo e, PoolAt σ hi lo e → e &&& 1 = 1 → Fl4Spec.asidEntryRoot e ≠ ptr.bv)
    {hi1 : Fl4Spec.AsidHighIndex} {lo1 : Fl4Spec.AsidLowIndex} {g : Fl4Spec.Word} (hg : g.toNat < 2 ^ 47)
    (hp1 : GPath σ hi1 lo1 g lk t) (hidx : Fl4Spec.guestIndex g lv.val = idx)
    (ha1 : Fl4Spec.asidHighBitsOf asid1.bv = hi1) (ha2 : Fl4Spec.asidLowBitsOf asid1.bv = lo1)
    (hgv : g'.bv = gKey g lv.val)
    (hcap' : capV m' dest = .Ept ptr lv true asid1 g')
    (hcp : ∀ y, IsSlot th y → y ≠ dest → capV m' y = capV m y) :
    EptNamed th m' σ1 := by
  have hcs := eptChild_cases hch
  have hl64 : lv.val + 9 < 64 := by omega
  -- the paths after
  have hdec : ∀ hi lo gpa l u, GPath σ1 hi lo gpa l u → GPath σ hi lo gpa l u ∨
      (eptChild lk = some l ∧ u = ptr.bv ∧ GPath σ hi lo gpa lk t ∧ Fl4Spec.guestIndex gpa l = idx) := by
    intro hi lo gpa l u h
    rcases GPath.store hk hk1 hoth hat (fun c hc => by
        rw [hch] at hc; cases hc; rw [htg]; exact hptrz) h with h | ⟨a, b, c, d⟩
    · exact Or.inl h
    · exact Or.inr ⟨a, b.trans htg, c, d⟩
  -- `ptr` was reached by no path
  have hun : ∀ hi lo gpa l, gpa.toNat < 2 ^ 47 → ¬ GPath σ hi lo gpa l ptr.bv := by
    intro hi lo gpa l hgp hp
    by_cases hl0 : l = 0
    · subst hl0
      obtain ⟨e0, he0, h0, hr⟩ := hp.zero
      exact hroot _ _ _ he0 h0 hr.symm
    · exact N.unmUnreach hd hdc hi lo gpa l hgp hl0 hp
  -- every path to `t` has the decoded path's ASID and address bits
  have hmatch : ∀ hi lo gpa, gpa.toNat < 2 ^ 47 → GPath σ hi lo gpa lk t →
      Fl4Spec.guestIndex gpa lv.val = idx → hi = hi1 ∧ lo = lo1 ∧ gKey gpa lv.val = g'.bv := by
    intro hi lo gpa hgp hp hix
    have hix' : Fl4Spec.guestIndex gpa lv.val = Fl4Spec.guestIndex g lv.val := hix.trans hidx.symm
    by_cases hk0 : lk = 0
    · subst hk0
      have hl39 : lv.val = 39 := by omega
      obtain ⟨e0, he0, h0, hr⟩ := hp.zero
      obtain ⟨e1, he1, h1', hr1⟩ := hp1.zero
      obtain ⟨a, b⟩ := N.inj.root hi lo hi1 lo1 e0 e1 he0 he1 h0 h1' (hr.symm.trans hr1)
      refine ⟨a, b, ?_⟩
      rw [hgv]
      have h48 : gKey gpa (lv.val + 9) = gKey g (lv.val + 9) := by rw [hl39]; exact gKey_hi hgp hg
      exact gKey_step hl64 h48 hix'
    · obtain ⟨y1, p1, lv1, a1, v1, hy1, hp1u, hlv1, b1, b2, b3, hc1⟩ := N.ex hi1 lo1 g lk t hg hp1 hk0
      obtain ⟨-, c1, c2, c3⟩ := N.all hi lo gpa lk t hgp hp hk0 y1 p1 lv1 true a1 v1 hy1 hp1u hc1
      refine ⟨c1.symm.trans b1, c2.symm.trans b2, ?_⟩
      have hlk : lk = lv.val + 9 := by omega
      have h9 : gKey gpa (lv.val + 9) = gKey g (lv.val + 9) := by rw [← hlk, ← c3, b3]
      rw [hgv]
      exact gKey_step hl64 h9 hix'
  refine ⟨fun hi lo gpa l u hgp hp hl => ?_, fun hi lo gpa l u hgp hp hl y p lv' mm a v hy hpu hc => ?_, ?_⟩
  · rcases hdec hi lo gpa l u hp with hp0 | ⟨hc, rfl, hpt, hix⟩
    · obtain ⟨y, p, lv', a, v, hy, hpu, hlv, b1, b2, b3, hc⟩ := N.ex hi lo gpa l u hgp hp0 hl
      have hyd : y ≠ dest := fun e' => by
        subst e'; rw [hdc] at hc; exact absurd (capability.Cap.Ept.inj hc).2.2.1 (by decide)
      exact ⟨y, p, lv', a, v, hy, hpu, hlv, b1, b2, b3, by rw [hcp y hy hyd]; exact hc⟩
    · rw [hch] at hc
      injection hc with hc
      subst hc
      obtain ⟨a, b, c⟩ := hmatch hi lo gpa hgp hpt hix
      exact ⟨dest, ptr, lv, asid1, g', hd, rfl, rfl, by rw [ha1, a], by rw [ha2, b], c.symm, hcap'⟩
  · rcases hdec hi lo gpa l u hp with hp0 | ⟨hc', rfl, hpt, hix⟩
    · by_cases hyd : y = dest
      · subst hyd
        rw [hcap'] at hc
        obtain ⟨rfl, -, -, -, -⟩ := capability.Cap.Ept.inj hc
        exact (hun hi lo gpa l hgp (hpu ▸ hp0)).elim
      · exact N.all hi lo gpa l u hgp hp0 hl y p lv' mm a v hy hpu (by rw [← hcp y hy hyd]; exact hc)
    · rw [hch] at hc'
      injection hc' with hc'
      subst hc'
      by_cases hyd : y = dest
      · subst hyd
        rw [hcap'] at hc
        obtain ⟨-, -, rfl, rfl, rfl⟩ := capability.Cap.Ept.inj hc
        obtain ⟨a', b', c'⟩ := hmatch hi lo gpa hgp hpt hix
        exact ⟨rfl, by rw [ha1, a'], by rw [ha2, b'], c'.symm⟩
      · have hpp : p = ptr := P1.eq_of_bv hpu
        subst hpp
        exact (huq y hy hyd lv' mm a v (by rw [← hcp y hy hyd]; exact hc)).elim
  · refine N.inj.mono hat fun hi lo e0 ⟨p, f, g1, g2, g3⟩ _ => ?_
    have hpt : p ≠ t := fun e' => by subst e'; rw [hk1] at g2; cases g2
    exact ⟨p, f, by rw [← hat]; exact g1, by rw [← hoth p hpt]; exact g2, g3⟩

/-! ## The spec's slot write -/

theorem EptWalk.cnK {σ σ' : Fl4Spec.State Unit} (hW : EptWalk σ) (hcn : Ipc.CnK σ σ') : EptWalk σ' :=
  EptWalk.keep hW (fun r l es hk => Or.inl ((cnK_arch hcn).1 hk)) (fun r l es hk => ⟨es, (cnK_arch hcn).2 hk⟩)
    (fun e he _ => Or.inl (cnK_entry hcn e he))

theorem EptNamed.cnK {th : TypedHeap} {m : U64 → U64} {σ σ' : Fl4Spec.State Unit} (N : EptNamed th m σ)
    (hcn : Ipc.CnK σ σ') : EptNamed th m σ' :=
  N.frameA (cnK_asid hcn)
    (fun _ _ _ ⟨q, f, h1, h2, h3⟩ _ => ⟨q, f, by rw [← cnK_asid hcn]; exact h1, (cnK_arch hcn).1 h2, h3⟩)
    (fun r l es hk => (cnK_arch hcn).1 hk) (fun y _ _ _ _ hy hc _ => ⟨y, hy, hc⟩) (fun y _ _ _ _ _ hy hc => ⟨y, hy, hc⟩)

/-! ## `EptCore` across the table map -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across the table map** (module docstring). -/
theorem EptCore.tableMap (C : EptCore (L := L) X XL th s σ) {s' : S} {σ1 σ' : Fl4Spec.State Unit}
    {t : U64} (ht : t ∈ X) {ptr lv asid0 va0 asid1 g : U64} {dest : U64} (hd : IsSlot th dest)
    (hdc : capV (L.mem s) dest = .Ept ptr lv false asid0 va0) (hXt : XL t = lkLvl lv.val)
    (hlv : lv.val = 39 ∨ lv.val = 30 ∨ lv.val = 21) (hg : g.val < 2 ^ 47) (ha1 : asid1 ≠ 0#u64)
    (hgk : gKey g.bv lv.val = g.bv)
    (hp1 : GPath σ (Fl4Spec.asidHighBitsOf asid1.bv) (Fl4Spec.asidLowBitsOf asid1.bv) g.bv (XL t) t.bv)
    {es0 : BitVec 9 → Fl4Spec.Word} (hk0 : σ.kheap t.bv = some (.archObj (.ept (XL t) es0)))
    {W : U64 → Prop} (hw : P1.WritesIn st s s' W)
    (hW : ∀ b, W b → b = eptA t (Fl4Spec.guestIndex g.bv lv.val) ∨ ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    (hwd : EptWord Fl4Spec.virtKind (L.mem s' (eptA t (Fl4Spec.guestIndex g.bv lv.val))).bv
      (Fl4Spec.GuestPte.encode Fl4Spec.virtKind (.table (Fl4Spec.addrFromPPtr ptr.bv))))
    (htg : Fl4Spec.ptrFromPAddr (Fl4Spec.GuestPte.encode Fl4Spec.virtKind (.table (Fl4Spec.addrFromPPtr ptr.bv)) &&&
      Fl4Spec.guestPteAddress) = ptr.bv)
    (hk1 : σ1.kheap t.bv = some (.archObj (.ept (XL t) (Function.update es0 (Fl4Spec.guestIndex g.bv lv.val)
      (Fl4Spec.GuestPte.encode Fl4Spec.virtKind (.table (Fl4Spec.addrFromPPtr ptr.bv)))))))
    (hoth : ∀ r, r ≠ t.bv → σ1.kheap r = σ.kheap r)
    (hat : σ1.archState.x64AsidTable = σ.archState.x64AsidTable) (hcn : Ipc.CnK σ1 σ')
    (hcap' : capV (L.mem s') dest = .Ept ptr lv true asid1 g)
    (hcp : ∀ y, IsSlot th y → y ≠ dest → capV (L.mem s') y = capV (L.mem s) y) :
    EptCore (L := L) X XL th s' σ' := by
  have hpX : ptr ∈ X := by have h := C.exte.cap dest hd; rw [hdc] at h; exact h
  have hXp : XL ptr = lv.val := by have h := C.capL dest hd ptr lv asid0 va0 false hdc; exact h.symm
  obtain ⟨u1, u2, u3, u4⟩ := C.ue dest hd ptr lv asid0 va0 hdc
  rw [hXp] at u2
  have hch : eptChild (XL t) = some lv.val := by rw [hXt]; rcases hlv with h | h | h <;> rw [h] <;> rfl
  have hge1 : ∀ x, GuestEntry σ1 x → GuestEntry σ x := by
    rintro x ⟨hi, q, f, lo, h1, h2, h3⟩
    have hq : q ≠ t.bv := fun e' => by subst e'; rw [hk1] at h2; cases h2
    exact ⟨hi, q, f, lo, by rw [← hat]; exact h1, by rw [← hoth q hq]; exact h2, h3⟩
  have hk' : σ'.kheap t.bv = _ := (cnK_arch hcn).2 hk1
  -- the written table is reachable, so `t ≠ p` for every unmapped cap's table `p`
  have hpt : ∀ y p l a v, IsSlot th y → capV (L.mem s) y = .Ept p l false a v → p.bv ≠ t.bv := by
    intro y p l a v hy hc e'
    by_cases h0 : XL t = 0
    · rw [h0] at hp1
      obtain ⟨e0, he0, h1, hr⟩ := hp1.zero
      exact (C.ue y hy p l a v hc).2.2.2 e0 he0.guest h1 (by rw [e', hr])
    · exact C.named.unmUnreach hy hc (Fl4Spec.asidHighBitsOf asid1.bv) (Fl4Spec.asidLowBitsOf asid1.bv) g.bv (XL t)
        hg h0 (by rw [e']; exact hp1)
  have hxk : ∀ u ∈ X, u ≠ t → σ'.kheap u.bv = σ.kheap u.bv := by
    intro u hu hne
    obtain ⟨es, hk, -⟩ := C.rel.obj u hu
    have hb : u.bv ≠ t.bv := fun h => hne (P1.eq_of_bv h)
    rw [hk]; exact (cnK_arch hcn).2 (by rw [hoth _ hb]; exact hk)
  refine C.entry ht hk0 hw hW hwd hk' hxk (fun y hy p l a v mm hc => ?_) ⟨fun y hy => ?_, ⟨fun y hy p l a v hc => ?_,
    fun y hy p sz r d a v hc => ?_⟩, fun y hy p l a v hc => ?_⟩ (fun r l es hk => ?_) (fun x hx => hge1 x (cnK_entry hcn x hx)) (fun o ko' ho => ?_) ?_ ?_ ?_ ?_
  · -- caps after: `dest`'s is the old one rewritten mapped
    by_cases e : y = dest
    · rw [e, hcap'] at hc
      obtain ⟨rfl, rfl, -, -, -⟩ := capability.Cap.Ept.inj hc
      exact ⟨dest, asid0, va0, false, hd, hdc⟩
    · exact ⟨y, a, v, mm, hy, by rw [← hcp y hy e]; exact hc⟩
  · by_cases e : y = dest
    · rw [e, hcap']; exact hpX
    · rw [hcp y hy e]; exact C.exte.cap y hy
  · by_cases e : y = dest
    · rw [e, hcap'] at hc
      obtain ⟨-, -, -, -, rfl⟩ := capability.Cap.Ept.inj hc
      exact hg
    · rw [hcp y hy e] at hc; exact C.exte.vtop.1 y hy p l a v hc
  · by_cases e : y = dest
    · rw [e, hcap'] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.vtop.2 y hy p sz r d a v hc
  · by_cases e : y = dest
    · rw [e, hcap'] at hc
      obtain ⟨-, -, -, rfl, -⟩ := capability.Cap.Ept.inj hc
      exact ha1
    · rw [hcp y hy e] at hc; exact C.exte.anz y hy p l a v hc
  · have h1 := (cnK_arch hcn).1 hk
    by_cases hr : r = t.bv
    · subst hr; exact ⟨_, _, hk0⟩
    · rw [hoth r hr] at h1; exact ⟨l, es, h1⟩
  · obtain ⟨ko1, hko1, hb1⟩ := cnK_size hcn o ko' ho
    by_cases hr : o = t.bv
    · subst hr
      rw [hk1] at hko1; cases hko1
      exact ⟨_, hk0, by rw [hb1, ept_bits, ept_bits]⟩
    · rw [hoth o hr] at hko1; exact ⟨ko1, hko1, hb1⟩
  · -- `UnmappedEmpty` after
    intro y hy p l a v hc
    have hyd : y ≠ dest := fun e => by
      rw [e, hcap'] at hc; exact absurd (capability.Cap.Ept.inj hc).2.2.1 (by decide)
    rw [hcp y hy hyd] at hc
    have hpX' : p ∈ X := by have h := C.exte.cap y hy; rw [hc] at h; exact h
    obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy p l a v hc
    have hpt' : p ≠ t := fun e => hpt y p l a v hy hc (by rw [e])
    refine ⟨fun i => ?_, ?_, fun y' hy' hne l' mm a' v' hc' => ?_, fun e he h1' => h4 e (hge1 e (cnK_entry hcn e he)) h1'⟩
    · have hp := C.rel.place p hpX'
      have e1 := eptA_val hp.2 i
      have hi9 := i.isLt
      rw [hw.mem_eq (b := eptA p i) (by unfold P1.Aligned; rw [e1]; omega) (fun hb => by
        rcases hW _ hb with h | h
        · exact hpt' (C.eptA_inj hpX' ht (congrArg UScalar.val h)).1
        · rcases h p hpX' with h | h <;> omega)]
      exact h1 i
    · rw [hxk p hpX' hpt']; exact h2
    · by_cases e : y' = dest
      · rw [e, hcap'] at hc'
        obtain ⟨rfl, -, -, -, -⟩ := capability.Cap.Ept.inj hc'
        exact h3 dest hd (fun e' => hyd e'.symm) lv false asid0 va0 hdc
      · exact h3 y' hy' hne l' mm a' v' (by rw [← hcp y' hy' e]; exact hc')
  · -- `EptSlotOK`: `dest` held an unmapped cap, so it is no TCB's `SLOT_EPT`
    intro t' ht'
    by_cases e : cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 5) = dest
    · exfalso
      rcases C.eslot t' ht' with h | ⟨p, a, v, h⟩ <;> rw [e, hdc] at h <;> cases h
    · exact Or.inr (Or.inr ⟨ht', hcp _ (isSlot_eptSlot ht') e⟩)
  · -- `EptWalk`: the new entry names the zero table `ptr` one level down
    refine EptWalk.cnK (EptWalk.store C.walk hk0 hk1 hoth hge1 fun _ c hc => ?_) hcn
    rw [hch] at hc; cases hc; rw [htg]; exact u2
  · -- `EptNamed`
    refine (C.named.tableMap hk0 hk1 hoth hat htg hch u2 hd hdc u3
      (fun hi lo e he h1 => u4 e he.guest h1) hg hp1 rfl rfl rfl hgk.symm hcap' hcp).cnK hcn

end

end

end Fl4Proofs.P3
