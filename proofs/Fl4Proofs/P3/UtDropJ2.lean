/-
P3 (DESIGN.md §9), Untyped's reset (the drop step), part 5: **the other
`JAtZ` fields across the drop** (handoff/utj.md "Round 9", item 2). At a
`JAtZ` state with a childless RAM untyped cap over `[p, p + 2^sb)`, the
drop goes, at the same FL4 state, to the spec state `σ'` detyped at the
region (`SDrop`), the sets `KeepS (KOff (RgOf p sb))` (`XSets.keep`), the typed
heap `restrictTh` and P1's heap `H.drop (RegionD H p (p + 2^sb))`. This
module proves the placement, cover and CSpace fields there:

* heap facts: `notRD_of` (an object of `H` off the region is kept),
  `JAtZ.specOff` (a spec object at an address off the region misses it:
  `SpecFree` at the source cap), `JAtZ.specKeep` (so `H`'s object there,
  no larger, is kept);
* `JAtZ.dropPlace`: `ks`, `ip`, `rp`, `apart`, `nk`, `nodeB`, `thT`, `thk`,
  `intL`, `zH`, `hset`, `hscC`, `sfree`, `obj`, `cover` (the last with
  `ArchFitHyp` [J], as `utEpJ`);
* `JAtZ.dropCov`: `jcov` (`JCovD` is antitone in the heaps; `D` kept);
* `JAtZ.dropDel`: `del` and `finM` (the typed heap's slots in the region
  are null: their caps would be in the MDB, whose slots are off the region,
  `UtCapP3.ns`).
-/
import Fl4Proofs.P3.UtDropJ
import Fl4Proofs.P3.UtEpSets
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## Heap facts -/

section Heap
variable {H : P1.Heap} {lo hi : Nat}

/-- An object of `H` missing `[lo, hi)` does not meet it. -/
theorem notRD_of {q : U64} {k : P1.HKind} (hq : H q = some k) (h : q.val + 2 ^ k.bits ≤ lo ∨ hi ≤ q.val) :
    ¬ P1.RegionD H lo hi q := by
  unfold P1.RegionD P1.MeetsR; rw [hq]; simp only [Option.elim]; omega

theorem drop_some {q : U64} {k : P1.HKind} (h : H.drop (P1.RegionD H lo hi) q = some k) : H q = some k :=
  (P1.Heap.drop_eq_some.1 h).2

theorem drop_keep {q : U64} {k : P1.HKind} (hq : H q = some k) (h : ¬ P1.RegionD H lo hi q) :
    H.drop (P1.RegionD H lo hi) q = some k := by
  rw [P1.Heap.drop_of_not h]; exact hq

end Heap

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- `DeadP` at a smaller heap. -/
theorem DeadP.drop {R : U64 → Prop} {q : U64} (h : DeadP (L := L) H s q) : DeadP (L := L) (H.drop R) s q := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨fun e => h1 (P1.Heap.drop_eq_some.1 e).2, fun e => h2 (P1.Heap.drop_eq_some.1 e).2,
    fun e => h3 (P1.Heap.drop_eq_some.1 e).2, fun e => h4 (P1.Heap.drop_eq_some.1 e).2,
    fun z e => h5 z (P1.Heap.drop_eq_some.1 e).2⟩

/-- `ExAt` at smaller heaps. -/
theorem ExAt.drop {th : TypedHeap} {R : U64 → Prop} {lo hi : Nat} {q : U64} (h : ExAt (L := L) th H s q) :
    ExAt (L := L) (restrictTh th lo hi) (H.drop R) s q := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨fun k e => h1 k (restrictTh_some e).1, fun k e => h2 k (P1.Heap.drop_eq_some.1 e).2⟩

/-- The range of a TCB zombie. -/
theorem range_zombieT (q n : U64) (hfit : q.val + 2 ^ 12 ≤ 2 ^ 64) :
    baseF (.Zombie q capability.ZOMBIE_TCB n) = q.val ∧ topF (.Zombie q capability.ZOMBIE_TCB n) = q.val + 2 ^ 12 - 1 :=
  Sched.capRange (b := 12#u64) (ok_inj (ptr_eq _).symm)
    (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits, fl4_abi.consts.bits.TCB])) (by decide) hfit

/-- The range of a CNode zombie of radix `zt`. -/
theorem range_zombieC (q zt n : U64) (hne : zt ≠ capability.ZOMBIE_TCB) (hr : zt.val + 5 < 64)
    (hfit : q.val + 2 ^ (zt.val + 5) ≤ 2 ^ 64) :
    baseF (.Zombie q zt n) = q.val ∧ topF (.Zombie q zt n) = q.val + 2 ^ (zt.val + 5) - 1 := by
  have hs : (core.num.U64.wrapping_add zt fl4_abi.consts.bits.SLOT).val = zt.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits,
      fl4_abi.consts.bits.SLOT]
    omega
  have h := Sched.capRange (c := .Zombie q zt n) (p := q) (b := core.num.U64.wrapping_add zt fl4_abi.consts.bits.SLOT)
    (ok_inj (ptr_eq _).symm) (ok_inj (by rw [← size_eq]; simp only [objects.cap_size_bits, hne, ↓reduceIte]))
    (by rw [hs]; exact hr) (by rw [hs]; exact hfit)
  rw [hs] at h
  exact h

/-- **`MdbLinks` at the restricted typed heap gives it at the whole one**
when the typed heap's slots in the region are null. -/
theorem MdbLinks.unrestrict {th : TypedHeap} {lo hi : Nat} {m : U64 → U64} {G : MdbGhost} (hP : Placed th)
    (hN : NoStraddle th lo hi) (hM : MdbLinks (restrictTh th lo hi) m G)
    (hnull : ∀ y, IsSlot th y → ¬ (y.val < lo ∨ hi ≤ y.val) → capV m y = .Null) : MdbLinks th m G := by
  refine ⟨hM.tree, hM.ne_nil, hM.chain, hM.head, hM.last, fun a => ⟨fun h => ?_, fun ⟨h1, c, hc, hn⟩ => ?_⟩⟩
  · obtain ⟨h1, h2⟩ := (hM.members a).1 h
    exact ⟨h1.of_restrict, h2⟩
  · have hout : a.val < lo ∨ hi ≤ a.val := by
      by_contra hin; exact hn (by rw [← capV_of_capAt hc]; exact hnull a h1 hin)
    exact (hM.members a).2 ⟨h1.restrict hP hN hout, c, hc, hn⟩

/-- An object of the restricted typed heap's slot named twice. -/
theorem AbsSlot.restrict2 {th : TypedHeap} {a1 b1 a2 b2 : Nat} {sl : Fl4Spec.CslotPtr}
    (h1 : AbsSlot (restrictTh th a1 b1) sl) (h2 : AbsSlot (restrictTh th a2 b2) sl) :
    AbsSlot (restrictTh (restrictTh th a1 b1) a2 b2) sl := by
  obtain ⟨q, e1, k1⟩ := h1
  obtain ⟨q', e2, k2⟩ := h2
  have : q' = q := P1.eq_of_bv (e2.symm.trans e1)
  subst this
  have ho : ¬ (a2 ≤ q'.val ∧ q'.val < b2) := by
    rcases k2 with k | ⟨k, -⟩
    · exact (restrictTh_some k).2
    · exact (restrictTh_some k).2
  exact ⟨q', e1, by rw [restrictTh_out ho]; exact k1⟩

section Rg
variable {p sb : U64} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
include hsb hfit

/-- An object of `H` not meeting the region has its address off it. -/
theorem off_of_notRD {q : U64} {k : P1.HKind} (hq : H q = some k)
    (h : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) q) : ¬ RgOf p sb q.bv :=
  fun hr => h (rgOf_regionD hsb hfit hq hr)

/-- An address off the region, as values. -/
theorem off_val {q : U64} (h : ¬ RgOf p sb q.bv) : ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) :=
  fun h' => h ((rgOf_iff hsb hfit q).2 h')

/-- **A spec object at an address off the region misses it** (`SpecFree` at
the source cap: a spec object meeting a RAM untyped cap's region lies in its
used part, at an address of the region). -/
theorem JAtZ.specOff (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hfi : fi.val ≤ 2 ^ sb.val)
    {o : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject} (hk : σ.kheap o = some ko) (ho : ¬ RgOf p sb o) :
    o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p.val ∨ p.val + 2 ^ sb.val ≤ o.toNat := by
  rcases J.sfree x hx p sb fi hcx o ko hk with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
    exact off_val hsb hfit (q := ⟨o⟩) ho ⟨h1, by show o.toNat < _; omega⟩

/-- **`H`'s object at a spec object's address off the region, no larger
than it, is kept.** -/
theorem JAtZ.specKeep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hfi : fi.val ≤ 2 ^ sb.val)
    {o : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject} (hk : σ.kheap o = some ko) (ho : ¬ RgOf p sb o)
    {k : P1.HKind} (hH : H ⟨o⟩ = some k) (hle : k.bits ≤ Fl4Spec.objBits ko) :
    H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)) ⟨o⟩ = some k := by
  refine drop_keep hH (notRD_of hH ?_)
  have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) hle
  rcases J.specOff hsb hfit hx hcx hfi hk ho with h | h
  · left; show o.toNat + _ ≤ _; omega
  · right; exact h

/-- **The placement, cover and set fields across the drop** (module
docstring; `ArchFitHyp` [J] for the arch objects, as `utEpJ`). -/
theorem JAtZ.dropPlace (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hfi : fi.val ≤ 2 ^ sb.val)
    (hAF : ArchFitHyp H σ) (hN : NoStraddle Z.th p.val (p.val + 2 ^ sb.val)) {σ' : Fl4Spec.State Unit}
    (hD : SDrop (RgOf p sb) σ σ') :
    let K := KOff (RgOf p sb)
    let H' := H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))
    let th' := restrictTh Z.th p.val (p.val + 2 ^ sb.val)
    KsApart (KeepS K Z.N) (KeepS K Z.T) (KeepS K Z.E) (KeepS K Z.R) (KeepB (KBOf p sb) Z.B) (L.ksb s) ∧
    (∀ t, th' t = some .tcb → t ∈ KeepS K Z.T) ∧
    (∀ q k, th' q = some k → k = .tcb ∨ ∃ r, k = .cnode r) ∧
    IPlaced (KeepS K Z.N) (KeepS K Z.T) (KeepS K Z.E) (KeepS K Z.R) (KeepB (KBOf p sb) Z.B) ∧
    Sched.RPlaced st (KeepS K Z.N) (KeepS K Z.T) (KeepS K Z.C) (KeepS K Z.R) Z.c s σ' ∧
    Sched.SlotsApart (st := st) th' (KeepS K Z.T) (KeepS K Z.N) (KeepS K Z.C) (KeepS K Z.R) Z.c s σ' ∧
    (∀ n ∈ KeepS K Z.N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val) ∧
    (∀ wp ∈ KeepB (KBOf p sb) Z.B, ∀ c : U64, c.val < 64 → wp.1.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ wp.1.val) ∧
    Sched.SpecCover H' σ' ∧
    Sched.ObjCover (KeepS K Z.N) (KeepS K Z.T) (KeepS K Z.E) (KeepS K Z.R) (KeepS K Z.C) σ' ∧
    ((∀ t ∈ KeepS K Z.T, H' t = some .tcb) ∧ (∀ e ∈ KeepS K Z.E, H' e = some .ep) ∧
      (∀ r ∈ KeepS K Z.R, H' r = some .reply) ∧ (∀ n ∈ KeepS K Z.N, H' n = some .ntfn)) ∧
    Sched.SpecFree (L.mem s) Z.G σ' ∧
    ((∀ e, H' e = some .ep → e ∈ KeepS K Z.E) ∧ (∀ n, H' n = some .ntfn → n ∈ KeepS K Z.N) ∧
      (∀ r, H' r = some .reply → r ∈ KeepS K Z.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ KeepS K Z.C) ∧
    IntLayout th' (L.ksb s) := by
  intro K H' th'
  have hoff : ∀ {q : U64} {k : P1.HKind}, H' q = some k → ¬ RgOf p sb q.bv := fun {q k} e =>
    off_of_notRD hsb hfit (drop_some e) (P1.Heap.drop_eq_some.1 e).1
  have hkeep := fun {o} {ko} (hk : σ.kheap o = some ko) (ho : ¬ RgOf p sb o) {k} (hH : H ⟨o⟩ = some k)
    (hle : k.bits ≤ Fl4Spec.objBits ko) => J.specKeep hsb hfit hx hcx hfi hk ho hH hle
  have hreg := (J.jcov.ks x hx p sb fi hcx).1
  refine ⟨⟨fun e he => J.ks.ep e he.1, fun r hr => J.ks.rep r hr.1, fun n hn => J.ks.ntfn n hn.1,
      fun wp hw => J.ks.buf wp hw.1⟩,
    fun t ht => ⟨J.thT t (restrictTh_some ht).1, fun hr => (restrictTh_some ht).2 ((rgOf_iff hsb hfit t).1 hr)⟩,
    fun q k hq => J.thk q k (restrictTh_some hq).1,
    ⟨J.ip.n.keepS, J.ip.e.keepS, fun n hn e he => J.ip.ne n hn.1 e he.1, fun n hn r hr => J.ip.nr n hn.1 r hr.1,
      fun n hn wp hw => J.ip.nb n hn.1 wp hw.1⟩,
    ⟨fun r hr => J.rp.align r hr.1, fun r hr => J.rp.ksb r hr.1, fun r hr t ht => J.rp.tcb r hr.1 t ht.1,
      fun r hr n hn => J.rp.ntfn r hr.1 n hn.1, fun r hr c hc y n hy => J.rp.sc r hr.1 c hc.1 y n (hD.back hy).2⟩,
    fun q hq => ?_, fun n hn => J.nk n hn.1, fun wp hw c hc => J.nodeB wp hw.1 c hc,
    ⟨fun o y hy => ?_, fun o y hy => ?_, fun o y hy => ?_, fun y k hy => J.cover.sc0 y k (hD.back hy).2,
      fun o ao hy => ?_⟩,
    J.obj.drop hD, ⟨fun t ht => ?_, fun e he => ?_, fun r hr => ?_, fun n hn => ?_⟩,
    fun x' hx' p' sb' fi' hc' o ko hk => J.sfree x' hx' p' sb' fi' hc' o ko (hD.back hk).2,
    ⟨fun e he => ⟨J.hset.1 e (drop_some he), hoff he⟩, fun n hn => ⟨J.hset.2.1 n (drop_some hn), hoff hn⟩,
      fun r hr => ⟨J.hset.2.2 r (drop_some hr), hoff hr⟩⟩,
    fun c z hc => ⟨J.hscC c z (drop_some hc), hoff hc⟩,
    ⟨J.intL.fit, J.intL.align, fun i hi => OutsideObjects.restrict (J.intL.st_out i hi), fun i hi => ?_⟩⟩
  · obtain ⟨g1, g2, g3, g4, g5⟩ := J.apart q (IsSlot.of_restrict hq)
    exact ⟨fun t ht => g1 t ht.1, g2, fun n hn => g3 n hn.1, fun c hc y n hy => g4 c hc.1 y n (hD.back hy).2,
      fun r hr => g5 r hr.1⟩
  · obtain ⟨ho, hk⟩ := hD.back hy
    exact hkeep hk ho (J.cover.ntfn o y hk) (Nat.le_of_eq rfl)
  · obtain ⟨ho, hk⟩ := hD.back hy
    exact hkeep hk ho (J.cover.ep o y hk) (Nat.le_of_eq rfl)
  · obtain ⟨ho, hk⟩ := hD.back hy
    exact hkeep hk ho (J.cover.reply o y hk) (Nat.le_of_eq rfl)
  · obtain ⟨ho, hk⟩ := hD.back hy
    obtain ⟨n, h12, hH⟩ := J.cover.arch o ao hk
    exact ⟨n, h12, hkeep hk ho hH (hAF o ao n hk hH)⟩
  · obtain ⟨Tr, Cq, hJP⟩ := J.jpl
    have hH := J.zH.1 t ht.1
    have hth : Z.th t = some .tcb := (hJP.tcb t).2 hH
    have ho := off_val hsb hfit ht.2
    refine drop_keep hH (notRD_of hH ?_)
    have := hN t .tcb hth
    simp only [objSize] at this
    show t.val + 4096 ≤ _ ∨ _
    omega
  · obtain ⟨y, hk, -⟩ := J.xtop.ipc.ep e he.1
    exact hkeep hk he.2 (J.zH.2.1 e he.1) (Nat.le_of_eq rfl)
  · obtain ⟨y, hk, -⟩ := J.xtop.ipc.reply r hr.1
    exact hkeep hk hr.2 (J.zH.2.2.1 r hr.1) (Nat.le_of_eq rfl)
  · obtain ⟨y, hk, -⟩ := J.xtop.ipc.ntfn n hn.1
    exact hkeep hk hn.2 (J.zH.2.2.2 n hn.1) (Nat.le_of_eq rfl)
  · have hv := nodeA_val J.intL.fit hi
    have hno : ¬ (p.val ≤ (nodeA (L.ksb s) i).val ∧ (nodeA (L.ksb s) i).val < p.val + 2 ^ sb.val) := by
      rw [hv]; rcases hreg with e | e <;> omega
    show restrictTh Z.th p.val (p.val + 2 ^ sb.val) (nodeA (L.ksb s) i) = some (.cnode 0)
    rw [restrictTh_out hno]; exact J.intL.node i hi

/-- **`JCovD` across the drop**: at the smaller heaps, with the same dead
set, ghost tree and FL4 state. -/
theorem JAtZ.dropCov (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Sched.JCovD (L := L) (restrictTh Z.th p.val (p.val + 2 ^ sb.val))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Z.G D Cs s := by
  have C := J.jcov
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun q hq => DeadP.drop (C.dead q hq), C.ks, ?_⟩
  · rcases C.th q k (restrictTh_some hq).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ExAt.drop h))
  · rcases C.h q k (drop_some hq) with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (ExAt.drop h))
  · intro x hx p' sb' fi' hc q hq
    obtain ⟨h1, h2, h3⟩ := C.idleOut x hx p' sb' fi' hc q hq
    exact ⟨h1, fun k e => h2 k (restrictTh_some e).1, fun k e => h3 k (drop_some e)⟩

/-- **The typed heap's slots in a region with no MDB slot are null.** -/
theorem JAtZ.nullIn (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hns : ∀ a ∈ Z.G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val) {y : U64} (hy : IsSlot Z.th y)
    (hin : ¬ (y.val < p.val ∨ p.val + 2 ^ sb.val ≤ y.val)) : capV (L.mem s) y = .Null := by
  obtain ⟨-, ⟨-, -, hML, -, -⟩, -⟩ := J.xtop.rel
  by_contra hn
  exact hin (hns y ((hML.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩))

/-- **`DelInv`, `FinM` and `DelBound` at the restricted typed heap** (the
CSpace fields of item 2): a zombie's object is covered by the zombie, so off
the childless region (`ut_free`); the typed heap's slots in the region are
null (`nullIn`), so a tree of the restricted heap is one of the whole heap;
for `DelBound`'s other memories, the region's slot words are cleared, which
keeps the tree and its measure. -/
theorem JAtZ.dropDel (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x)
    (hN : NoStraddle Z.th p.val (p.val + 2 ^ sb.val))
    (hns : ∀ a ∈ Z.G.chains.flatten, a.val < p.val ∨ p.val + 2 ^ sb.val ≤ a.val) :
    DelInv (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) (L.mem s) ∧
      (∀ G, MdbLinks (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) (L.mem s) G → FinM (L.mem s) G) ∧
      DelBound (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) := by
  obtain ⟨hPl, ⟨-, -, hML, -, hI⟩, -⟩ := J.xtop.rel
  set lo := p.val
  set hi := p.val + 2 ^ sb.val
  -- a zombie's object is off the region
  have hz : ∀ y, IsSlot Z.th y → ∀ q zt n, capV (L.mem s) y = .Zombie q zt n → ZOK Z.th q zt n →
      ZOK (restrictTh Z.th lo hi) q zt n := by
    intro y hy q zt n hc hZ
    have hyG : y ∈ Z.G.chains.flatten := (hML.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hc]; simp⟩
    have hph : physF (.Zombie q zt n) = true := ok_inj (by rw [← phys_eq]; rfl)
    have hut : isUt (.Zombie q zt n) = false := rfl
    have hout : ∀ b : Nat, baseF (.Zombie q zt n) = q.val ∧ topF (.Zombie q zt n) = q.val + 2 ^ b - 1 →
        ¬ (lo ≤ q.val ∧ q.val < hi) := fun b hr => by
      have := Nat.one_le_two_pow (n := b)
      rcases ut_free J.ut hI hx hcx hnd (by omega) (Sched.covered_of_cap hyG hc hph hut hr) with e | e <;> omega
    rcases hZ with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have e : zt = capability.ZOMBIE_TCB := UScalar.eq_of_val_eq (by rw [h1, zombie_tcb_val])
      have hf := hPl.fits q _ h2
      simp only [objSize] at hf
      subst e
      exact Or.inl ⟨h1, by rw [restrictTh_out (hout 12 (range_zombieT q n (by omega)))]; exact h2, h3⟩
    · have hne : zt ≠ capability.ZOMBIE_TCB := fun e => h1 (by rw [e, zombie_tcb_val])
      have hf := hPl.fits q _ h2
      simp only [objSize] at hf
      have hhi := hPl.high q _ h2
      have hr : zt.val + 5 < 64 := by
        by_contra hc'
        have : 2 ^ 64 ≤ 2 ^ (zt.val + 5) := Nat.pow_le_pow_right (by decide) (by omega)
        have : 32 * 2 ^ zt.val = 2 ^ (zt.val + 5) := by rw [Nat.pow_add]; omega
        omega
      have hf' : q.val + 2 ^ (zt.val + 5) ≤ 2 ^ 64 := by rw [Nat.pow_add]; omega
      exact Or.inr ⟨h1, by rw [restrictTh_out (hout _ (range_zombieC q zt n hne hr hf'))]; exact h2, h3⟩
  have hnull := fun y (hy : IsSlot Z.th y) hin => J.nullIn hsb hfit hns hy hin
  obtain ⟨Kb, hK1, hK6, hK3⟩ := J.bound
  refine ⟨⟨fun y hy q zt n hc => hz y hy.of_restrict q zt n hc (J.del.zwf y hy.of_restrict q zt n hc),
      fun y y' hy hy' hne => J.del.zu y y' hy.of_restrict hy'.of_restrict hne,
      fun y hy hc => J.del.nc y hy.of_restrict hc⟩,
    fun G hG => J.finM G (hG.unrestrict hPl hN hnull),
    ⟨Kb, fun q r hq => hK1 q r (restrictTh_some hq).1, hK6, fun m G hG => ?_⟩⟩
  -- clear the region's words: the tree and its measure are kept
  let m' : U64 → U64 := fun w => if lo ≤ w.val ∧ w.val < hi then 0#u64 else m w
  have hwo : ∀ y, IsSlot (restrictTh Z.th lo hi) y → ∀ k : U64, k.val < 32 → m' (wordOf y k) = m (wordOf y k) := by
    intro y hy k hk
    have hw := IsSlot.restrict_words hPl hN hy
    have hf : y.val + 32 ≤ 2 ^ 64 := by
      obtain ⟨q, i, hi', rfl⟩ := hy
      obtain ⟨kd, hkd, hs⟩ := hi'.size
      have := hPl.restrict.fits q kd hkd
      rw [hi'.val hPl.restrict]; omega
    have hv := wordOf_val (a := y) (k := k) (by omega)
    show (if _ then _ else _) = _
    rw [if_neg (by rw [hv]; omega)]
  have hSS : SlotsSame (restrictTh Z.th lo hi) m m' := fun y hy => by
    have h0 := hwo y hy 0#u64 (by decide)
    rw [wordOf_zero] at h0
    exact ⟨h0, hwo y hy 8#u64 (by decide), hwo y hy 16#u64 (by decide), hwo y hy 24#u64 (by decide)⟩
  have hG' : MdbLinks Z.th m' G := (hG.of_same hSS).unrestrict hPl hN (fun y hy hin => by
    obtain ⟨q, i, hi', rfl⟩ := hy
    obtain ⟨kd, hkd, hs⟩ := hi'.size
    have hv := hi'.val hPl
    have hf := hPl.fits q kd hkd
    have hq := hN q kd hkd
    rw [hv] at hin
    have hw : ∀ k : U64, k.val < 32 → m' (wordOf (slotOf q i) k) = 0#u64 := fun k hk => by
      have hw := wordOf_val (a := slotOf q i) (k := k) (by rw [hv]; omega)
      show (if _ then _ else _) = _
      rw [if_pos (by rw [hw, hv]; omega)]
    have h0 := hw 0#u64 (by decide)
    rw [wordOf_zero] at h0
    exact capV_zero h0 (hw 8#u64 (by decide)))
  have hmz : mzS m' G = mzS m G := by
    unfold mzS
    refine Finset.filter_congr fun y hy => ?_
    have hyS := ((hG.members y).1 (List.mem_toFinset.1 hy)).1
    unfold HomeZ
    rw [SlotsSame.capV hSS hyS]
  have := hK3 m' G hG'
  unfold psiD at this ⊢
  rwa [hmz] at this

/-- **`JPlaced` across the drop** (same thread and SC sets): `H`'s TCBs and
CNodes are the typed heap's, which straddle no region (`NoStraddle`); a spec
SC off the region misses it (`specKeep`); a cap in the MDB covers its
objects, which so miss the childless region (`ut_free`). -/
theorem JAtZ.dropJpl (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x)
    (hfi : fi.val ≤ 2 ^ sb.val) (hN : NoStraddle Z.th p.val (p.val + 2 ^ sb.val))
    {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ') :
    ∃ Tr Cq, Sched.JPlaced (L := L) (restrictTh Z.th p.val (p.val + 2 ^ sb.val))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Tr Cq s σ' := by
  obtain ⟨Tr, Cq, hJP⟩ := J.jpl
  obtain ⟨-, ⟨-, -, hML, -, hI⟩, -⟩ := J.xtop.rel
  have hkeepH : ∀ q kd, H q = some kd → Covered (L.mem s) Z.G q.val (q.val + 2 ^ kd.bits) →
      H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)) q = some kd := fun q kd hq hc => by
    have := Nat.one_le_two_pow (n := kd.bits)
    exact drop_keep hq (notRD_of hq (ut_free J.ut hI hx hcx hnd (by omega) hc))
  have htyp : ∀ a, IsSlot Z.th a → P1.CapTyped (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)))
      (P1.Heap.replies (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))))
      (P1.Heap.ntfns (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)))) (capV (L.mem s) a) := fun a ha => by
    by_cases hn : capV (L.mem s) a = .Null
    · rw [hn]; exact capTyped_null
    · exact capTyped_keep hJP.heap ((hML.members a).2 ⟨ha, _, capAt_capV _ _, hn⟩) rfl (hJP.typed a ha) hkeepH
  have hirqS : ∀ i : U64, i.val < 128 → IsSlot Z.th (nodeA (L.ksb s) i) := fun i hi => by
    have hA : AbsSlot Z.th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using J.intL.node i hi)⟩
    have := hA.isSlot; rwa [cslotAddr_nil] at this
  refine ⟨Tr, Cq, P1.HeapOK.drop hJP.heap, hJP.pl.restrict, fun t => ⟨fun h => ?_, fun h => ?_⟩, fun q r h => ?_,
    fun t h => hJP.tr t (restrictTh_some h).1, fun c y n hc hk => ?_, fun q k hq hk => hJP.ks q k (drop_some hq) hk,
    fun q z hq => hJP.ksIn q z (drop_some hq), fun a ha => htyp a ha.of_restrict, fun i hi => htyp _ (hirqS i hi),
    fun t h => hJP.fh t (restrictTh_some h).1, fun a ha => ?_⟩
  · obtain ⟨h1, -⟩ := restrictTh_some h
    have hH := (hJP.tcb t).1 h1
    refine drop_keep hH (notRD_of hH ?_)
    have := hN t _ h1
    have ho := (restrictTh_some h).2
    simp only [objSize] at this
    show t.val + 4096 ≤ _ ∨ _
    omega
  · have hH := drop_some h
    have ho := off_val hsb hfit (off_of_notRD hsb hfit hH (P1.Heap.drop_eq_some.1 h).1)
    rw [restrictTh_out ho]; exact (hJP.tcb t).2 hH
  · obtain ⟨h1, ho⟩ := restrictTh_some h
    have hH := hJP.cnode q r h1
    refine drop_keep hH (notRD_of hH ?_)
    have := hN q _ h1
    simp only [objSize] at this
    show q.val + 2 ^ (r + 5) ≤ _ ∨ _
    rw [Nat.pow_add]
    omega
  · obtain ⟨ho, hk0⟩ := hD.back hk
    obtain ⟨h1, h2⟩ := hJP.sc c y n hc hk0
    exact ⟨h1, J.specKeep hsb hfit hx hcx hfi (o := c.bv) hk0 ho h2
      (by show n + Fl4Spec.minSchedContextBits ≤ Fl4Spec.minSchedContextBits + n; omega)⟩
  · have hy := IsSlot.of_restrict ha
    have hC := hJP.cobj a hy
    have hmem : capV (L.mem s) a ≠ .Null → a ∈ Z.G.chains.flatten := fun hn =>
      (hML.members a).2 ⟨hy, _, capAt_capV _ _, hn⟩
    cases hc : capV (L.mem s) a with
    | Ept q lv m' a' va =>
      rw [hc] at hC
      obtain ⟨⟨n2, hH, hb, ht⟩, hA⟩ := hC
      have ha0 := hmem (by rw [hc]; simp)
      have hp : physF (.Ept q lv m' a' va) = true := ok_inj (phys_eq _).symm
      exact ⟨⟨n2, hkeepH q _ hH ⟨a, ha0, by rw [hc]; exact hp, by rw [hc]; rfl, by rw [hc]; exact hb,
        by rw [hc]; simp only [P1.HKind.bits]; exact ht⟩, hb, ht⟩, fun q' k hq hk => hA q' k (drop_some hq) hk⟩
    | Frame q sz r d m' ep a' va =>
      rw [hc] at hC
      exact fun q' k hq hk => hC q' k (drop_some hq) hk
    | SchedContext q sb' =>
      rw [hc] at hC
      obtain ⟨hH, hpi⟩ := hC
      have ha0 := hmem (by rw [hc]; simp)
      have hf := hJP.heap.fits q _ hH
      have hlt := hJP.heap.lt64 q _ hH
      simp only [P1.HKind.bits] at hf hlt
      exact ⟨hkeepH q _ hH (covered_of_cap ha0 hc (ok_inj (phys_eq _).symm) rfl
        (capRange (b := sb') (ok_inj (ptr_eq _).symm)
          (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits])) hlt hf)), hpi⟩
    | _ => trivial

/-- **The RAM untyped caps' facts across the drop** (`utc`): every field is
antitone in the typed heap or reads the FL4 state, the ghost tree, the
spec's `cdt` and arch state, all kept; the original caps' slots are off
this region too (`hrst`, the source cap's `UtCapP3.rst`). -/
theorem JAtZ.dropUtc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {σ' : Fl4Spec.State Unit}
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap) (harch : σ'.archState = σ.archState)
    (hrst : ∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) sl) :
    ∀ sl p' sb' fi' dev, AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) sl →
      capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p' sb' fi' dev) → dev = false →
      Sched.UtCapP3 (L := L) arI (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) s σ' Z.G sl p' sb' fi' := by
  intro sl p' sb' fi' dev hsl hc hd
  have U := J.utc sl p' sb' fi' dev hsl.of_restrict hc hd
  refine ⟨U.pal, U.pfit, U.fiLe, U.high, U.actZ, fun q kd h => U.free q kd (restrictTh_some h).1, U.zero, U.sb4,
    fun q k h => U.nostr q k (restrictTh_some h).1, U.nsFree, fun h => U.ns (by rw [← hcdt]; exact h),
    fun hn hnc hf0 => ⟨fun sl' ho => (hrst sl' (by rw [← horig]; exact ho)).restrict2
      ((U.rst hn (by rw [← hcdt]; exact hnc) hf0).1 sl' (by rw [← horig]; exact ho)),
      (U.rst hn (by rw [← hcdt]; exact hnc) hf0).2⟩, U.dwReg, fun hn => by rw [harch]; exact U.gReg hn⟩

/-- **The current thread and SC are live** (outside the region's dead
objects; no reschedule pending: `CurInv`), as in `dropBlk`. -/
theorem JAtZ.curLive (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread)
    (hRD : ∀ q, P1.RegionD H p.val (p.val + 2 ^ sb.val) q → DeadP (L := L) H s q) :
    ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) (L.curW s) ∧ ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) (L.cscW s) := by
  have hC := J.curInv hres
  obtain ⟨xt, hkt, hsc, -⟩ := hC.tcb
  obtain ⟨Q, R0, hcr, hs⟩ := J.xtop.fin.1.1.1.lists
  refine ⟨fun hd => ?_, fun hd => ?_⟩
  · have d2 := ((hRD _ hd).1 J.kern.curH).2.1
    have hT := J.thT _ J.kern.curT
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb _ hT
    rw [← J.kern.cur, hkt] at hk'; cases hk'
    rw [hR.sc, d2, optRef_zero] at hsc; cases hsc
  · obtain ⟨y, n, hy, hyt⟩ := J.inv.back _ xt _ hkt hsc
    have ecs : L.cscW s = Sched.nodeW st s Z.c layout.node.CUR_SC := by
      unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA Sched.nodeW; rw [hcr.cur]
    obtain ⟨q, hq, hqp⟩ := J.obj.sc _ y n hy
    have eq : q = L.cscW s := P1.eq_of_bv (by rw [hqp, hs.curSc, ecs])
    subst eq
    obtain ⟨y', n', hk', hx'⟩ := hs.scs _ hq
    have hk2 : σ.kheap σ.curSc = some (.schedContext y' n') := by rw [← hqp]; exact hk'
    rw [hy] at hk2; cases hk2
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc _ y n (J.c0 _ hq) hk').2
    have d := ((hRD _ hd).2.2.2.2 _ hH).1
    rw [hx'.tcb, scW_tcb, d, optRef_zero] at hyt; cases hyt

/-- **`JKern` across the drop**: the current thread and SC live (`curLive`),
the original caps' slots, the debug-list head and the global PML4 off the
region (the source cap's `UtCapP3.rst`/`gReg`), the rest antitone or kept. -/
theorem JAtZ.dropKern (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {σ' : Fl4Spec.State Unit}
    (hD : SDrop (RgOf p sb) σ σ') (horig : σ'.isOriginalCap = σ.isOriginalCap) (harch : σ'.archState = σ.archState)
    (hcur : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) (L.curW s))
    (hcsc : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) (L.cscW s))
    (hrst : ∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) sl)
    (hhd : ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val))
    (hg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val)) :
    JKern (L := L) (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs D
      (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) s σ' := by
  have K := J.kern
  have hcT : ¬ (p.val ≤ (L.curW s).val ∧ (L.curW s).val < p.val + 2 ^ sb.val) :=
    off_val hsb hfit (off_of_notRD hsb hfit K.curH hcur)
  refine ⟨fun sl h => hrst sl (by rw [← horig]; exact h), by rw [hD.ct]; exact K.cur,
    by rw [restrictTh_out hcT]; exact K.curT, OutsideObjects.restrict K.act, K.dwAl,
    fun a ha => K.dwObj a ha.of_restrict, K.dwNe, ?_, ?_, by rw [harch]; exact K.ga, by rw [harch]; exact K.gf,
    P1.HeapOK.drop K.heap, ?_, fun q k hq hk => K.hks q k (drop_some hq) hk,
    fun q z hq => K.hksIn q z (drop_some hq), fun q k hq c hc => K.hnd q k (drop_some hq) c hc, K.ksbFit,
    K.ksbAl, K.nodeFit, K.cpuCs, drop_keep K.curH hcur, by rw [P1.Heap.drop_of_not hcsc]; exact K.cscH,
    K.csLt, K.cs0⟩
  · rcases K.head with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨by rw [restrictTh_out hhd]; exact h1, h2⟩
  · rw [harch]
    obtain ⟨pt, hk⟩ := K.gpm
    refine ⟨pt, hD.fwd (fun hr => hg ?_) hk⟩
    exact (rgOf_iff hsb hfit ⟨σ.archState.x64GlobalPml4⟩).1 hr
  · cases e : H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val)) 0#u64 with
    | none => rfl
    | some k => have := drop_some e; rw [K.h0] at this; cases this

end Rg

/-- **`JAtZ` across the drop** (item 2 of handoff/utj.md "Round 9"): at a
childless RAM untyped cap with a used region (`fi ≠ 0`, the spec's
`resetUntypedCap` detypes then), from the same FL4 state, the spec state
`σ'` detyped at the region, the kept sets, the restricted typed heap and
P1's heap without the region's objects. Premises beyond `JAtZ`: no
reschedule pending, the spec detype's own facts (`SDrop` and the fields it
keeps), `KeptRefsP3`/`DbgTimerKept` at the region (`RegionUnrefJ` [J]'s two
parts, as `utEpJ`), `ArchFitHyp` [J] (as `utEpJ`), and `VsReachMiss` [J]
(VsDrop). -/
theorem JAtZ.drop (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread) {sl : Fl4Spec.CslotPtr} (hsl : AbsSlot Z.th sl)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hnc : ¬ ∃ y, σ.cdt y = some sl) (hfi0 : fi.val ≠ 0)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s)
    (hAF : ArchFitHyp H σ)
    {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ')
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hrepr : σ'.reprogramTimer = σ.reprogramTimer) (hcdom : σ'.curDomain = σ.curDomain)
    (hdtime : σ'.domainTime = σ.domainTime) (hist : σ'.interruptStates = σ.interruptStates)
    (hinode : σ'.interruptIrqNode = σ.interruptIrqNode) (harch : σ'.archState = σ.archState)
    (hdl : σ'.domainList = σ.domainList) (hdsi : σ'.domainStartIndex = σ.domainStartIndex)
    (hum : ∀ x, ¬ RgOf p sb x → σ'.machineState.underlyingMemory x = σ.machineState.underlyingMemory x)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1) :
    JAtZ (L := L) arI AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs Ac Lst D s a σ' := by
  have U := J.utc sl p sb fi false hsl hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfit := U.pfit
  obtain ⟨hPl, ⟨-, -, hML, hC, -⟩, -⟩ := J.xtop.rel
  have hx : cslotAddr sl ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hsl.isSlot, _, hcap, by simp⟩
  have hcx : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false := capV_of_capAt hcap
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl) := fun y =>
    Mdb.not_desc_of_no_child fun z hz => hnc ((hC.has_child_iff hPl hsl).2 ⟨z, hz⟩)
  have hRD := J.rgDeadD hx hcx hnd
  have hK := J.sKeep hsb hfit hRD hres hKR
  have hND : NotDev (L.mem s) (cslotAddr sl) p sb fi := by
    unfold NotDev; rw [hcx]; simp
  obtain ⟨hrst, hhd⟩ := U.rst hND hnc hfi0
  obtain ⟨hcur, hcsc⟩ := J.curLive hsb hfit hres hRD
  obtain ⟨hks, hthT, hthk, hip, hrp, hap, hnk, hnB, hcov, hobj, hzH, hsf, hhs, hscC, hiL⟩ :=
    J.dropPlace hsb hfit hx hcx U.fiLe hAF U.nostr hD
  obtain ⟨hnsc, hinv, hcu, hown, hoff, hact, hc0, hbsa, hsv, hiso, hsl', hcr⟩ := J.dropSpecInv hK hD
  obtain ⟨hcall, hrf, hrr, hyl, hmcp, hbuf⟩ := J.dropMixed hsb hfit hRD hK hD
  obtain ⟨hdel, hfin, hbd⟩ := J.dropDel hsb hfit hx hcx hnd U.nostr (U.ns hnc)
  have hX := J.dropX hres hsl hcap hnc hKR hD hcdt horig hrepr hcdom hdtime hist hinode harch hdl hdsi hum
    hXP hX4 hX3 hX2 hX1 hM
  have hjpl := J.dropJpl hsb hfit hx hcx hnd U.fiLe U.nostr hD
  have hjc := J.dropCov hsb hfit
  have hkn := J.dropKern hsb hfit hD horig harch hcur hcsc hrst hhd (U.gReg hND)
  have hutc := J.dropUtc hsb hfit hcdt horig harch hrst
  have hblk := J.dropBlk hres hx hcx hnd hKR hDT
  exact ⟨hX, hcall, hrf, hrr, hyl, hmcp, hbuf, hks, hthT, hthk, hip, hrp, hap, hnk, hnB, hjpl, hcov, hobj, hzH, hsf,
    hhs, hscC, hjc, hkn, hdel, J.ut, hbd, hfin, hutc, hnsc, hinv, hcu, hown, hoff, hact, hc0, hbsa, hsv, hiso, hsl',
    hcr, hblk, hiL⟩

end

end

end Fl4Proofs.P3
