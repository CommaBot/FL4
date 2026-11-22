/-
P3 (DESIGN.md §9), untyped: **`JAtZ`'s set and heap fields at the sets
enlarged by a retype's endpoints or notifications** (the nine inputs of
`JAtZ.add_frame` but `XTopAt`, handoff/utj.md "Exactly what remains" a).

The window `[A, A + w * k)` lies in a part `[lo, hi)` of RAM untyped
memory in which no object of the typed heap, no spec object and no IPC-buffer
word lies, and which misses the kernel-state block. P1's heap after is
`HOut` over the window (objects meeting it dropped, the new ones added):

* `hout_old`, `hout_new`, `hout_back`: lookups in an `HOut` heap.
* `ArchFitHyp` [J]: an `other` object of `H` at a spec arch object is no
  larger than it (the `H` object's range lies in the spec object's).
* `JAtZ.addSets`: from `JAtZ` at the old sets and heap, the window's new
  endpoints `En`, notifications `Nn` or replies `Rn` (of one kind: the new
  objects' P1 kind), the spec state
  after (its objects the old ones, CNodes changed, or the window's idle
  objects), `KsApart`, `IPlaced`, the notifications off the kernel-state
  block, `SpecCover`, `ObjCover`, `zH`, `hset` and `hscC` at the new sets
  and heap.
-/
import Fl4Proofs.P3.UtAddSpec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc Fl4Proofs.P1

noncomputable section

/-! ## Lookups in an `HOut` heap -/

section
variable {H H' : Heap} {lo hi A k w : Nat} {K : Option HKind}

theorem newAt_bd {A k w : Nat} {q : U64} (hk : 1 ≤ k) (h : NewAt A k w q) : A ≤ q.val ∧ q.val < A + w * k := by
  obtain ⟨j, hj, e⟩ := h
  have := Nat.mul_le_mul_right k (show j + 1 ≤ w by omega)
  rw [Nat.add_mul, Nat.one_mul] at this
  omega

theorem hout_old (h : HOut H H' lo hi A k w K) (hlo : lo = A) (hhi : hi = A + w * k) (hk : 1 ≤ k) {q : U64}
    {kd : HKind} (hq : H q = some kd) (hoff : q.val + 2 ^ kd.bits ≤ A ∨ A + w * k ≤ q.val) : H' q = some kd := by
  subst hlo hhi
  have h1 := Nat.one_le_two_pow (n := kd.bits)
  rw [h q, if_neg (fun ⟨hn, _⟩ => by have := newAt_bd hk hn; omega), if_neg, hq]
  rintro ⟨kd', hq', hm⟩
  rw [hq] at hq'; cases hq'
  exact hm (by omega)

theorem hout_new (h : HOut H H' lo hi A k w K) {q : U64} (hn : NewAt A k w q) {kd : HKind} (hK : K = some kd) :
    H' q = some kd := by
  rw [h q, if_pos ⟨hn, by rw [hK]; rfl⟩, hK]

theorem hout_back (h : HOut H H' lo hi A k w K) {q : U64} {kd : HKind} (hq : H' q = some kd) :
    (NewAt A k w q ∧ K = some kd) ∨ H q = some kd := by
  rw [h q] at hq
  split_ifs at hq with h1 h2
  · exact Or.inl ⟨h1.1, hq⟩
  · exact Or.inr hq

end

-- `ArchFitHyp` moved to JCarryDefs (jc1, unchanged statement).

/-- **`ArchFitHyp` across a retype** (jc1b; `JCarry.archFit` at the retype
sites): `H` grown by `HOut`, the spec's objects after old ones, CNodes, new
endpoints / notifications / replies, or new arch objects at the new `other`
objects, each at least as large as its P1 size (`hKa`). The old objects lie
off the region (`hspec`), so an old arch object is no new `other` object. -/
theorem ArchFitHyp.add {H H' : Heap} {σ σ' : Fl4Spec.State Unit} {lo hi A k w : Nat} {K : Option HKind}
    {En Nn Rn : Set U64} (h : ArchFitHyp H σ)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) (hout : HOut H H' A (A + w * k) A k w K)
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs', ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt A k w q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧ ∃ m, 12 ≤ m ∧ K = some (.other m)))
    (hKa : ∀ q m, NewAt A k w q → K = some (.other m) → ∀ ao, σ'.kheap q.bv = some (.archObj ao) →
      m ≤ Fl4Spec.objBits (.archObj ao)) : ArchFitHyp H' σ' := by
  intro o ao n ho hH
  rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨_, -, -, e⟩ | ⟨_, -, -, e⟩ | ⟨_, -, -, e⟩ | ⟨q, hq, rfl, -, m, -, hK⟩
  · rcases hout_back hout hH with ⟨hn, -⟩ | hH0
    · have h1 := newAt_bd hk1 hn
      have h2 := hspec _ _ e
      have h3 := Nat.one_le_two_pow (n := Fl4Spec.objBits (.archObj ao))
      have h4 : (⟨o⟩ : U64).val = o.toNat := rfl
      omega
    · exact h o ao n e hH0
  · cases e
  · cases e
  · cases e
  · cases e
  · have e := hout_new hout hq hK
    rw [show (⟨q.bv⟩ : U64) = q from rfl, e] at hH; cases hH
    exact hKa q n hq hK ao ho

/-- Every spec arch object is at least a 4 KiB page (`archKobjSize`). -/
theorem twelve_le_archObj (ao : Fl4Spec.ArchKernelObj) : 12 ≤ Fl4Spec.objBits (.archObj ao) := by
  cases ao with
  | dataPage _ sz =>
    cases sz <;> simp [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.pageBitsForSize, Fl4Spec.pageBits,
      Fl4Spec.ptTranslationBits]
  | _ => simp [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize, Fl4Spec.ptTranslationBits,
      Fl4Spec.wordSizeBits, Fl4Spec.pageBits]

/-- **A retype's new arch object is at least as large as its P1 `other` size**
(the `hKa` of `ArchFitHyp.add`: `newKind`'s sizes are the spec's
`archKobjSize` of the default arch objects). -/
theorem newKind_default_le {nt us m : Nat} {t : Fl4Spec.ApiObjectType} {dev : Bool} {cd : Fl4Spec.Domain}
    {ao : Fl4Spec.ArchKernelObj} (hty : objTypeOf nt = some t) (hK : newKind nt us = some (.other m))
    (he : Fl4Spec.defaultObject t dev us cd = .archObj ao) : m ≤ Fl4Spec.objBits (.archObj ao) := by
  have hn : nt < 19 := by
    by_contra h; rw [(objTypeOf_none nt).2 (by omega)] at hty; cases hty
  interval_cases nt <;> simp only [objTypeOf, Fl4Spec.archDataToObjType, newKind] at hty hK <;>
    simp at hty hK <;> subst hty <;> subst hK <;>
    simp [Fl4Spec.defaultObject, Fl4Spec.defaultArchObject] at he <;> subst he <;>
    first | decide | simp [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize, Fl4Spec.pageBitsForSize,
      Fl4Spec.pageBits, Fl4Spec.ptTranslationBits, Fl4Spec.wordSizeBits]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} {arI : machine.Arch A'}
variable {AR : A' → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The set and heap fields at the enlarged sets** (module docstring), the
spec's changed or new CNodes in one disjunct (any CNode after). -/
theorem JAtZ.addSetsG {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi) (hksr : hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ lo ∨ hi ≤ wp.1.val) (harch : ArchFitHyp H σ)
    {A k w : Nat} (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) {K : Option HKind} {H' : Heap}
    (hout : HOut H H' A (A + w * k) A k w K) {En Nn Rn : Set U64}
    (hEw : ∀ e ∈ En, e.val % 16 = 0 ∧ lo ≤ e.val ∧ e.val + 16 ≤ hi ∧ NewAt A k w e ∧ K = some .ep)
    (hNw : ∀ n ∈ Nn, n.val % 64 = 0 ∧ lo ≤ n.val ∧ n.val + 64 ≤ hi ∧ NewAt A k w n ∧ K = some .ntfn)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi ∧ NewAt A k w r ∧ K = some .reply)
    (hKn : ∀ q, NewAt A k w q → ∀ kd, K = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) ∨ (kd = .reply ∧ q ∈ Rn) ∨ ∃ m, kd = .other m)
    {σ' : Fl4Spec.State Unit}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs', ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt A k w q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧ ∃ m, 12 ≤ m ∧ K = some (.other m)))
    {Z' : XSets} (hT : Z'.T = Z.T) (hR : Z'.R = Z.R ∪ Rn) (hC : Z'.C = Z.C) (hBB : Z'.B = Z.B)
    (hE : Z'.E = Z.E ∪ En) (hN : Z'.N = Z.N ∪ Nn) :
    KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s') ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧
    (∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val) ∧
    Sched.SpecCover H' σ' ∧ Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ' ∧
    ((∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn)) ∧
    ((∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ Z'.C) := by
  rw [hT, hR, hC, hBB, hE, hN, hks]
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  -- the old objects off `[lo, hi)`
  have offT : ∀ t ∈ Z.T, t.val + 4096 ≤ lo ∨ hi ≤ t.val := by
    intro t ht
    have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
    have := hfree t .tcb hth
    simp only [objSize] at this; omega
  have offE : ∀ e ∈ Z.E, e.val + 16 ≤ lo ∨ hi ≤ e.val := by
    intro e he
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.ep e he
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, UScalar.bv_toNat] at this; omega
  have offR : ∀ r ∈ Z.R, r.val + 32 ≤ lo ∨ hi ≤ r.val := by
    intro r hr
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  have offN : ∀ n ∈ Z.N, n.val + 64 ≤ lo ∨ hi ≤ n.val := by
    intro n hn
    obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n hn
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this; omega
  -- two kinds of new objects never both occur
  have nEN : ∀ e ∈ En, ∀ n ∈ Nn, False := fun e he n hn => by
    have h1 := (hEw e he).2.2.2.2; have h2 := (hNw n hn).2.2.2.2; rw [h1] at h2; cases h2
  have nER : ∀ e ∈ En, ∀ r ∈ Rn, False := fun e he r hr => by
    have h1 := (hEw e he).2.2.2.2; have h2 := (hRw r hr).2.2.2.2; rw [h1] at h2; cases h2
  have nNR : ∀ n ∈ Nn, ∀ r ∈ Rn, False := fun n hn r hr => by
    have h1 := (hNw n hn).2.2.2.2; have h2 := (hRw r hr).2.2.2.2; rw [h1] at h2; cases h2
  have keep : ∀ {q : U64} {kd : HKind}, H q = some kd → (q.val + 2 ^ kd.bits ≤ lo ∨ hi ≤ q.val) → H' q = some kd :=
    fun hq hoff => hout_old hout rfl rfl hk1 hq (by omega)
  -- the spec's objects after, back
  have obk : ∀ o ko, σ'.kheap o = some ko → (∀ r cs, ko ≠ .cnode r cs) → (∀ x, ko ≠ .endpoint x) →
      (∀ x, ko ≠ .notification x) → (∀ x, ko ≠ .reply x) → (∀ x, ko ≠ .archObj x) → σ.kheap o = some ko := by
    intro o ko h h1 h2 h3 h4 h5
    rcases hback o ko h with e | ⟨r, cs', rfl⟩ | ⟨e, -, -, rfl⟩ | ⟨n, -, -, rfl⟩ | ⟨r, -, -, rfl⟩ |
      ⟨_, -, -, ⟨_, rfl⟩, -⟩
    · exact e
    · exact absurd rfl (h1 r cs')
    · exact absurd rfl (h2 _)
    · exact absurd rfl (h3 _)
    · exact absurd rfl (h4 _)
    · exact absurd rfl (h5 _)
  have hcov : Sched.SpecCover H' σ' := by
    refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun y z ho => ?_, fun o ao ho => ?_⟩
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, -, -, e'⟩ | ⟨n, hn, rfl, -⟩ | ⟨r, -, -, e'⟩ |
        ⟨_, -, -, ⟨_, e''⟩, -⟩
      · refine keep (J.cover.ntfn o x e) ?_
        have := hspec _ _ e
        simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, HKind.bits] at this ⊢; exact this
      · cases e
      · cases e'
      · obtain ⟨-, -, -, hna, hK⟩ := hNw n hn; exact hout_new hout hna hK
      · cases e'
      · cases e''
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, he, rfl, -⟩ | ⟨n, -, -, e'⟩ | ⟨r, -, -, e'⟩ |
        ⟨_, -, -, ⟨_, e''⟩, -⟩
      · refine keep (J.cover.ep o x e) ?_
        have := hspec _ _ e
        simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, HKind.bits] at this ⊢; exact this
      · cases e
      · obtain ⟨-, -, -, hna, hK⟩ := hEw e he; exact hout_new hout hna hK
      · cases e'
      · cases e'
      · cases e''
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, -, -, e'⟩ | ⟨n, -, -, e'⟩ | ⟨r, hr, rfl, -⟩ |
        ⟨_, -, -, ⟨_, e''⟩, -⟩
      · refine keep (J.cover.reply o x e) ?_
        have := hspec _ _ e
        simp only [Fl4Spec.objBits, Fl4Spec.replyBits, HKind.bits] at this ⊢; exact this
      · cases e
      · cases e'
      · cases e'
      · obtain ⟨-, -, -, hna, hK⟩ := hRw r hr; exact hout_new hout hna hK
      · cases e''
    · exact J.cover.sc0 y z (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h))
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, -, -, e'⟩ | ⟨n, -, -, e'⟩ | ⟨r, -, -, e'⟩ |
        ⟨q, hna, rfl, -, m, hm, hK⟩
      rotate_left
      · cases e
      · cases e'
      · cases e'
      · cases e'
      · exact ⟨m, hm, hout_new hout hna hK⟩
      obtain ⟨n, hn12, hHn⟩ := J.cover.arch o ao e
      refine ⟨n, hn12, keep hHn ?_⟩
      have h1 := hspec _ _ e
      have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) (harch o ao n e hHn)
      simp only [HKind.bits]
      show o.toNat + 2 ^ n ≤ lo ∨ hi ≤ o.toNat
      omega
  have hobj : Sched.ObjCover (Z.N ∪ Nn) Z.T (Z.E ∪ En) (Z.R ∪ Rn) Z.C σ' := by
    refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o y z ho => ?_⟩
    · exact J.obj.tcb o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h))
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, -, -, e'⟩ | ⟨n, hn, rfl, -⟩ | ⟨r, -, -, e'⟩ |
        ⟨_, -, -, ⟨_, e''⟩, -⟩
      · obtain ⟨n, hn, h⟩ := J.obj.ntfn o x e; exact ⟨n, Or.inl hn, h⟩
      · cases e
      · cases e'
      · exact ⟨n, Or.inr hn, rfl⟩
      · cases e'
      · cases e''
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, he, rfl, -⟩ | ⟨n, -, -, e'⟩ | ⟨r, -, -, e'⟩ |
        ⟨_, -, -, ⟨_, e''⟩, -⟩
      · obtain ⟨e, he, h⟩ := J.obj.ep o x e; exact ⟨e, Or.inl he, h⟩
      · cases e
      · exact ⟨e, Or.inr he, rfl⟩
      · cases e'
      · cases e'
      · cases e''
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨e, -, -, e'⟩ | ⟨n, -, -, e'⟩ | ⟨r, hr, rfl, -⟩ |
        ⟨_, -, -, ⟨_, e''⟩, -⟩
      · obtain ⟨r, hr, h⟩ := J.obj.reply o x e; exact ⟨r, Or.inl hr, h⟩
      · cases e
      · cases e'
      · cases e'
      · exact ⟨r, Or.inr hr, rfl⟩
      · cases e''
    · exact J.obj.sc o y z (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h))
  refine ⟨⟨fun e he => ?_, fun r hr => ?_, fun n hn => ?_, J.ks.buf⟩,
    ⟨⟨J.ip.n.tcb, fun n hn => ?_, fun n hn t ht => ?_⟩,
    ⟨J.ip.e.tcb, fun e he => ?_, fun r hr => ?_, fun e he t ht => ?_, fun r hr t ht => ?_, fun e he r hr => ?_,
      J.ip.e.balign, J.ip.e.bt, fun wp hw e he => ?_, fun wp hw r hr => ?_, J.ip.e.binj⟩,
      fun n hn e he => ?_, fun n hn r hr => ?_, fun n hn wp hw => ?_⟩, fun n hn => ?_, hcov, hobj,
      ⟨fun t ht => ?_, fun e he => ?_, fun r hr => ?_, fun n hn => ?_⟩,
      ⟨fun e he => ?_, fun n hn => ?_, fun r hr => ?_⟩, fun c z hc => ?_⟩
  -- KsApart
  · rcases he with he | he
    · exact J.ks.ep e he
    · obtain ⟨-, h1, h2, -⟩ := hEw e he; omega
  · rcases hr with hr | hr
    · exact J.ks.rep r hr
    · obtain ⟨-, h1, h2, -⟩ := hRw r hr; omega
  · rcases hn with hn | hn
    · exact J.ks.ntfn n hn
    · obtain ⟨-, h1, h2, -⟩ := hNw n hn; omega
  -- IPlaced
  · rcases hn with hn | hn
    · exact J.ip.n.ntfn n hn
    · obtain ⟨h0, h1, h2, -⟩ := hNw n hn; exact ⟨h0, by omega⟩
  · rcases hn with hn | hn
    · exact J.ip.n.disj n hn t ht
    · obtain ⟨-, h1, h2, -⟩ := hNw n hn; have := offT t ht; omega
  · rcases he with he | he
    · exact J.ip.e.ep e he
    · obtain ⟨h0, h1, h2, -⟩ := hEw e he; exact ⟨h0, by omega, by omega⟩
  · rcases hr with hr | hr
    · exact J.ip.e.rep r hr
    · obtain ⟨h0, h1, h2, -⟩ := hRw r hr; exact ⟨h0, by omega, by omega⟩
  · rcases he with he | he
    · exact J.ip.e.et e he t ht
    · obtain ⟨-, h1, h2, -⟩ := hEw e he; have := offT t ht; omega
  · rcases hr with hr | hr
    · exact J.ip.e.rt r hr t ht
    · obtain ⟨-, h1, h2, -⟩ := hRw r hr; have := offT t ht; omega
  · rcases he with he | he <;> rcases hr with hr | hr
    · exact J.ip.e.er e he r hr
    · obtain ⟨-, h1, h2, -⟩ := hRw r hr; have := offE e he; omega
    · obtain ⟨-, h1, h2, -⟩ := hEw e he; have := offR r hr; omega
    · exact (nER e he r hr).elim
  · rcases he with he | he
    · exact J.ip.e.be wp hw e he
    · obtain ⟨-, h1, h2, -⟩ := hEw e he; have := hB wp hw; omega
  · rcases hr with hr | hr
    · exact J.ip.e.br wp hw r hr
    · obtain ⟨-, h1, h2, -⟩ := hRw r hr; have := hB wp hw; omega
  · rcases hn with hn | hn <;> rcases he with he | he
    · exact J.ip.ne n hn e he
    · obtain ⟨-, h1, h2, -⟩ := hEw e he; have := offN n hn; omega
    · obtain ⟨-, h1, h2, -⟩ := hNw n hn; have := offE e he; omega
    · exact (nEN e he n hn).elim
  · rcases hn with hn | hn <;> rcases hr with hr | hr
    · exact J.ip.nr n hn r hr
    · obtain ⟨-, h1, h2, -⟩ := hRw r hr; have := offN n hn; omega
    · obtain ⟨-, h1, h2, -⟩ := hNw n hn; have := offR r hr; omega
    · exact (nNR n hn r hr).elim
  · rcases hn with hn | hn
    · exact J.ip.nb n hn wp hw
    · obtain ⟨-, h1, h2, -⟩ := hNw n hn; have := hB wp hw; omega
  -- nk
  · rcases hn with hn | hn
    · exact J.nk n hn
    · obtain ⟨-, h1, h2, -⟩ := hNw n hn; omega
  -- zH
  · exact keep (J.zH.1 t ht) (by simp only [HKind.bits]; have := offT t ht; omega)
  · rcases he with he | he
    · exact keep (J.zH.2.1 e he) (by simp only [HKind.bits]; have := offE e he; omega)
    · obtain ⟨-, -, -, hna, hK⟩ := hEw e he; exact hout_new hout hna hK
  · rcases hr with hr | hr
    · exact keep (J.zH.2.2.1 r hr) (by simp only [HKind.bits]; have := offR r hr; omega)
    · obtain ⟨-, -, -, hna, hK⟩ := hRw r hr; exact hout_new hout hna hK
  · rcases hn with hn | hn
    · exact keep (J.zH.2.2.2 n hn) (by simp only [HKind.bits]; have := offN n hn; omega)
    · obtain ⟨-, -, -, hna, hK⟩ := hNw n hn; exact hout_new hout hna hK
  -- hset
  · rcases hout_back hout he with ⟨hna, hK⟩ | h
    · rcases hKn e hna _ hK with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      · exact Or.inr h
      · cases h
      · cases h
      · obtain ⟨_, h⟩ := h; cases h
    · exact Or.inl (J.hset.1 e h)
  · rcases hout_back hout hn with ⟨hna, hK⟩ | h
    · rcases hKn n hna _ hK with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | h
      · cases h
      · exact Or.inr h
      · cases h
      · obtain ⟨_, h⟩ := h; cases h
    · exact Or.inl (J.hset.2.1 n h)
  · rcases hout_back hout hr with ⟨hna, hK⟩ | h
    · rcases hKn r hna _ hK with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | h
      · cases h
      · cases h
      · exact Or.inr h
      · obtain ⟨_, h⟩ := h; cases h
    · exact Or.inl (J.hset.2.2 r h)
  -- hscC
  · rcases hout_back hout hc with ⟨hna, hK⟩ | h
    · rcases hKn c hna _ hK with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨_, h⟩ <;> cases h
    · exact J.hscC c z h

/-- **The set and heap fields at the enlarged sets** (module docstring;
`JAtZ.addSetsG` with the changed CNodes old ones). -/
theorem JAtZ.addSets {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi) (hksr : hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ lo ∨ hi ≤ wp.1.val) (harch : ArchFitHyp H σ)
    {A k w : Nat} (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) {K : Option HKind} {H' : Heap}
    (hout : HOut H H' A (A + w * k) A k w K) {En Nn Rn : Set U64}
    (hEw : ∀ e ∈ En, e.val % 16 = 0 ∧ lo ≤ e.val ∧ e.val + 16 ≤ hi ∧ NewAt A k w e ∧ K = some .ep)
    (hNw : ∀ n ∈ Nn, n.val % 64 = 0 ∧ lo ≤ n.val ∧ n.val + 64 ≤ hi ∧ NewAt A k w n ∧ K = some .ntfn)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi ∧ NewAt A k w r ∧ K = some .reply)
    (hKn : ∀ q, NewAt A k w q → ∀ kd, K = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) ∨ (kd = .reply ∧ q ∈ Rn) ∨ ∃ m, kd = .other m)
    {σ' : Fl4Spec.State Unit}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt A k w q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧ ∃ m, 12 ≤ m ∧ K = some (.other m)))
    {Z' : XSets} (hT : Z'.T = Z.T) (hR : Z'.R = Z.R ∪ Rn) (hC : Z'.C = Z.C) (hBB : Z'.B = Z.B)
    (hE : Z'.E = Z.E ∪ En) (hN : Z'.N = Z.N ∪ Nn) :
    KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s') ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧
    (∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val) ∧
    Sched.SpecCover H' σ' ∧ Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ' ∧
    ((∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn)) ∧
    ((∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ Z'.C) :=
  J.addSetsG hks hlo0 hhi64 hfree hksr hspec hB harch hlo hhi hk1 hout hEw hNw hRw hKn
    (fun o ko h => (hback o ko h).imp_right (Or.imp_left fun ⟨r, _, cs', _, e⟩ => ⟨r, cs', e⟩)) hT hR hC hBB hE hN

/-- `JAtZ.addSetsG` with `ArchFitHyp` after (jc1b; `ArchFitHyp.add`). -/
theorem JAtZ.addSetsGA {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi) (hksr : hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ lo ∨ hi ≤ wp.1.val) (harch : ArchFitHyp H σ)
    {A k w : Nat} (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) {K : Option HKind} {H' : Heap}
    (hout : HOut H H' A (A + w * k) A k w K) {En Nn Rn : Set U64}
    (hEw : ∀ e ∈ En, e.val % 16 = 0 ∧ lo ≤ e.val ∧ e.val + 16 ≤ hi ∧ NewAt A k w e ∧ K = some .ep)
    (hNw : ∀ n ∈ Nn, n.val % 64 = 0 ∧ lo ≤ n.val ∧ n.val + 64 ≤ hi ∧ NewAt A k w n ∧ K = some .ntfn)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi ∧ NewAt A k w r ∧ K = some .reply)
    (hKn : ∀ q, NewAt A k w q → ∀ kd, K = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) ∨ (kd = .reply ∧ q ∈ Rn) ∨ ∃ m, kd = .other m)
    {σ' : Fl4Spec.State Unit}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs', ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt A k w q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧ ∃ m, 12 ≤ m ∧ K = some (.other m)))
    {Z' : XSets} (hT : Z'.T = Z.T) (hR : Z'.R = Z.R ∪ Rn) (hC : Z'.C = Z.C) (hBB : Z'.B = Z.B)
    (hE : Z'.E = Z.E ∪ En) (hN : Z'.N = Z.N ∪ Nn)
    (hKa : ∀ q m, NewAt A k w q → K = some (.other m) → ∀ ao, σ'.kheap q.bv = some (.archObj ao) →
      m ≤ Fl4Spec.objBits (.archObj ao)) :
    ArchFitHyp H' σ' ∧
        KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s') ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧
    (∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val) ∧
    Sched.SpecCover H' σ' ∧ Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ' ∧
    ((∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn)) ∧
    ((∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ Z'.C) :=
  ⟨ArchFitHyp.add harch hspec hlo hhi hk1 hout hback hKa,
    J.addSetsG hks hlo0 hhi64 hfree hksr hspec hB harch hlo hhi hk1 hout hEw hNw hRw hKn hback hT hR hC hBB hE hN⟩

/-- `JAtZ.addSets` with `ArchFitHyp` after (jc1b; `ArchFitHyp.add`). -/
theorem JAtZ.addSetsA {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi) (hksr : hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ lo ∨ hi ≤ wp.1.val) (harch : ArchFitHyp H σ)
    {A k w : Nat} (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) {K : Option HKind} {H' : Heap}
    (hout : HOut H H' A (A + w * k) A k w K) {En Nn Rn : Set U64}
    (hEw : ∀ e ∈ En, e.val % 16 = 0 ∧ lo ≤ e.val ∧ e.val + 16 ≤ hi ∧ NewAt A k w e ∧ K = some .ep)
    (hNw : ∀ n ∈ Nn, n.val % 64 = 0 ∧ lo ≤ n.val ∧ n.val + 64 ≤ hi ∧ NewAt A k w n ∧ K = some .ntfn)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi ∧ NewAt A k w r ∧ K = some .reply)
    (hKn : ∀ q, NewAt A k w q → ∀ kd, K = some kd →
      (kd = .ep ∧ q ∈ En) ∨ (kd = .ntfn ∧ q ∈ Nn) ∨ (kd = .reply ∧ q ∈ Rn) ∨ ∃ m, kd = .other m)
    {σ' : Fl4Spec.State Unit}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ ko = .cnode r cs') ∨
      (∃ e ∈ En, e.bv = o ∧ ko = .endpoint Fl4Spec.defaultEp) ∨
      (∃ n ∈ Nn, n.bv = o ∧ ko = .notification Fl4Spec.defaultNotification) ∨
      (∃ r ∈ Rn, r.bv = o ∧ ko = .reply Fl4Spec.defaultReply) ∨
      (∃ q, NewAt A k w q ∧ q.bv = o ∧ (∃ ao, ko = .archObj ao) ∧ ∃ m, 12 ≤ m ∧ K = some (.other m)))
    {Z' : XSets} (hT : Z'.T = Z.T) (hR : Z'.R = Z.R ∪ Rn) (hC : Z'.C = Z.C) (hBB : Z'.B = Z.B)
    (hE : Z'.E = Z.E ∪ En) (hN : Z'.N = Z.N ∪ Nn)
    (hKa : ∀ q m, NewAt A k w q → K = some (.other m) → ∀ ao, σ'.kheap q.bv = some (.archObj ao) →
      m ≤ Fl4Spec.objBits (.archObj ao)) :
    ArchFitHyp H' σ' ∧
        KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s') ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧
    (∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val) ∧
    Sched.SpecCover H' σ' ∧ Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ' ∧
    ((∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn)) ∧
    ((∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ Z'.C) :=
  ⟨ArchFitHyp.add harch hspec hlo hhi hk1 hout (fun o ko h => (hback o ko h).imp_right (Or.imp_left fun ⟨r, _, cs', _, e⟩ => ⟨r, cs', e⟩)) hKa,
    J.addSets hks hlo0 hhi64 hfree hksr hspec hB harch hlo hhi hk1 hout hEw hNw hRw hKn hback hT hR hC hBB hE hN⟩

set_option maxHeartbeats 2000000 in
/-- **`RPlaced` and `SlotsApart` at the notifications and replies grown by
the window** across the retype (`JAtZ.uaRest`'s `RPlaced` at the old sets,
`SlotsApart.sc_frame`): the new notifications and replies lie in `[lo, hi)`,
where no spec object (so no reply, notification or SC) and no object of the
typed heap (so no slot, no TCB) is; at most one of the two sets is new. -/
theorem JAtZ.addRP {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (InSlot Z.th)) {σB σ' : Fl4Spec.State Unit} {W : Fl4Spec.ObjRef → Prop}
    {o : Fl4Spec.ObjRef → Fl4Spec.KernelObject} (hA : SpecAdd σ σB W o) (hid : IdleNew W o) (hcn : CnK σB σ')
    {Nn Rn : Set U64} (hWn : ∀ n ∈ Nn, W n.bv) {lo hi : Nat} (hlo0 : 0 < lo) (hhi64 : hi ≤ 2 ^ 64)
    (hfree : RegionFree Z.th lo hi)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hNw : ∀ n ∈ Nn, lo ≤ n.val ∧ n.val + 64 ≤ hi)
    (hRw : ∀ r ∈ Rn, r.val % 32 = 0 ∧ lo ≤ r.val ∧ r.val + 32 ≤ hi)
    (hRks : ∀ r ∈ Rn, r.val + 32 ≤ (L.ksb s').val ∨ L.nodeBase s' Z.c + 4288 ≤ r.val)
    (hNR : Nn = ∅ ∨ Rn = ∅) :
    RPlaced st (Z.N ∪ Nn) Z.T Z.C (Z.R ∪ Rn) Z.c s' σ' ∧
      SlotsApart (st := st) Z.th Z.T (Z.N ∪ Nn) Z.C (Z.R ∪ Rn) Z.c s' σ' := by
  obtain ⟨-, hRP, -⟩ := J.uaRest hw hA hid hcn hWn
  have offR : ∀ r ∈ Z.R, r.val + 32 ≤ lo ∨ hi ≤ r.val := by
    intro r hr
    obtain ⟨x, hx, -⟩ := J.xtop.ipc.toE.reply r hr
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.replyBits, UScalar.bv_toNat] at this; omega
  have offN : ∀ n ∈ Z.N, n.val + 64 ≤ lo ∨ hi ≤ n.val := by
    intro n hn
    obtain ⟨x, hx, -⟩ := J.xtop.fin.1.1.2.2.1.ntfn n hn
    have := hspec _ _ hx
    simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this; omega
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have offT : ∀ t ∈ Z.T, t.val + 4096 ≤ lo ∨ hi ≤ t.val := by
    intro t ht
    have hth : Z.th t = some .tcb := (hJ.tcb t).2 (J.zH.1 t ht)
    have := hfree t .tcb hth
    simp only [objSize] at this; omega
  have hP := J.xtop.rel.1
  have slotOff : ∀ x, IsSlot Z.th x → x.val + 32 ≤ lo ∨ hi ≤ x.val := by
    rintro x ⟨p, i, hpi, rfl⟩
    obtain ⟨k, hk, hs⟩ := hpi.size
    rw [hpi.val hP]
    have := hfree p k hk; omega
  have hsz := uaSzKeep hA hid (CnStep.of_cnK hcn)
  have hAp := J.apart.sc_frame hw.1 hsz
  refine ⟨⟨fun r hr => ?_, fun r hr => ?_, fun r hr t ht => ?_, fun r hr n hn => ?_,
    fun r hr sc hsc x n hx => ?_⟩, fun x hx => ?_⟩
  · rcases hr with hr | hr
    · exact hRP.align r hr
    · obtain ⟨h0, h1, h2⟩ := hRw r hr
      refine ⟨h0, fun e => ?_, by omega⟩
      rw [e] at h1; simp at h1; omega
  · rcases hr with hr | hr
    · exact hRP.ksb r hr
    · exact hRks r hr
  · rcases hr with hr | hr
    · exact hRP.tcb r hr t ht
    · have := offT t ht; have := hRw r hr; omega
  · rcases hr with hr | hr <;> rcases hn with hn | hn
    · exact hRP.ntfn r hr n hn
    · have := offR r hr; have := hNw n hn; omega
    · have := offN n hn; have := hRw r hr; omega
    · rcases hNR with h | h
      · rw [h] at hn; exact hn.elim
      · rw [h] at hr; exact hr.elim
  · rcases hr with hr | hr
    · exact hRP.sc r hr sc hsc x n hx
    · obtain ⟨x0, hx0⟩ := hsz _ _ _ hx
      have := hspec _ _ hx0
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      have := hRw r hr
      rw [Nat.add_comm n]; omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hAp x hx
    refine ⟨h1, h2, fun n hn => ?_, h4, fun r hr => ?_⟩
    · rcases hn with hn | hn
      · exact h3 n hn
      · have := slotOff x hx; have := hNw n hn; omega
    · rcases hr with hr | hr
      · exact h5 r hr
      · have := slotOff x hx; have := hRw r hr; omega

end

end

end Fl4Proofs.P3
