/-
P3 (DESIGN.md §9), untyped: **`JAtZ`'s set and heap fields at `T` grown by a
retype's TCBs** (handoff/utj.md "uttypes", ut39; UtEpSets' `JAtZ.addSetsG`
for the TCB kind: the window's new objects are P1 TCBs, the spec's new
objects default TCBs, no endpoint, notification or reply is added).
-/
import Fl4Proofs.P3.UtEpSets
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P3.Ipc Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} {arI : machine.Arch A'}
variable {AR : A' → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 4000000 in
/-- `addSetsT` over `JAtZB` (mmuAD gen 42b25, in place; `JAtZ.addSetsT` is its corollary). -/
theorem JAtZB.addSetsT {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s) {lo hi : Nat}
    (hfree : RegionFree Z.th lo hi)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ lo ∨ hi ≤ wp.1.val) (harch : ArchFitHyp H σ)
    {A k w : Nat} (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) {H' : Heap}
    (hout : HOut H H' A (A + w * k) A k w (some .tcb)) {Tn : Set U64}
    (hTw : ∀ t ∈ Tn, P1.TcbAddr t ∧ lo ≤ t.val ∧ t.val + 4096 ≤ hi ∧ NewAt A k w t)
    {σ' : Fl4Spec.State Unit}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs', ko = .cnode r cs') ∨ (∃ t ∈ Tn, t.bv = o ∧ ∃ d, ko = .tcb (Fl4Spec.defaultTcb d)))
    {Z' : XSets} (hT : Z'.T = Z.T ∪ Tn) (hR : Z'.R = Z.R) (hC : Z'.C = Z.C) (hBB : Z'.B = Z.B)
    (hE : Z'.E = Z.E) (hN : Z'.N = Z.N) :
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
  have keep : ∀ {q : U64} {kd : HKind}, H q = some kd → (q.val + 2 ^ kd.bits ≤ lo ∨ hi ≤ q.val) → H' q = some kd :=
    fun hq hoff => hout_old hout rfl rfl hk1 hq (by omega)
  -- the spec's objects after, back
  have obk : ∀ o ko, σ'.kheap o = some ko → (∀ r cs, ko ≠ .cnode r cs) → (∀ x, ko ≠ .tcb x) →
      σ.kheap o = some ko := by
    intro o ko h h1 h2
    rcases hback o ko h with e | ⟨r, cs', rfl⟩ | ⟨t, -, -, d, rfl⟩
    · exact e
    · exact absurd rfl (h1 r cs')
    · exact absurd rfl (h2 _)
  have hcov : Sched.SpecCover H' σ' := by
    refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun y z ho => ?_, fun o ao ho => ?_⟩
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h)
      refine keep (J.cover.ntfn o x e) ?_
      have := hspec _ _ e
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, HKind.bits] at this ⊢; exact this
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h)
      refine keep (J.cover.ep o x e) ?_
      have := hspec _ _ e
      simp only [Fl4Spec.objBits, Fl4Spec.endpointBits, HKind.bits] at this ⊢; exact this
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h)
      refine keep (J.cover.reply o x e) ?_
      have := hspec _ _ e
      simp only [Fl4Spec.objBits, Fl4Spec.replyBits, HKind.bits] at this ⊢; exact this
    · exact J.cover.sc0 y z (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h))
    · have e := obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h)
      obtain ⟨n, hn12, hHn⟩ := J.cover.arch o ao e
      refine ⟨n, hn12, keep hHn ?_⟩
      have h1 := hspec _ _ e
      have h2 := Nat.pow_le_pow_right (show 0 < 2 by decide) (harch o ao n e hHn)
      simp only [HKind.bits]
      show o.toNat + 2 ^ n ≤ lo ∨ hi ≤ o.toNat
      omega
  have hobj : Sched.ObjCover Z.N (Z.T ∪ Tn) Z.E Z.R Z.C σ' := by
    refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o y z ho => ?_⟩
    · rcases hback o _ ho with e | ⟨r, cs', e⟩ | ⟨t, ht, rfl, -⟩
      · obtain ⟨t, ht, h⟩ := J.obj.tcb o x e; exact ⟨t, Or.inl ht, h⟩
      · cases e
      · exact ⟨t, Or.inr ht, rfl⟩
    · exact J.obj.ntfn o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h))
    · exact J.obj.ep o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h))
    · exact J.obj.reply o x (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h))
    · exact J.obj.sc o y z (obk _ _ ho (fun _ _ h => by cases h) (fun _ h => by cases h))
  refine ⟨⟨J.ks.ep, J.ks.rep, J.ks.ntfn, J.ks.buf⟩, ⟨⟨fun t ht => ?_, J.ip.n.ntfn, fun n hn t ht => ?_⟩,
    ⟨fun t ht => ?_, J.ip.e.ep, J.ip.e.rep, fun e he t ht => ?_, fun r hr t ht => ?_, J.ip.e.er,
      J.ip.e.balign, fun wp hw t ht => ?_, J.ip.e.be, J.ip.e.br, J.ip.e.binj⟩,
      J.ip.ne, J.ip.nr, J.ip.nb⟩, J.nk, hcov, hobj,
      ⟨fun t ht => ?_, fun e he => ?_, fun r hr => ?_, fun n hn => ?_⟩,
      ⟨fun e he => ?_, fun n hn => ?_, fun r hr => ?_⟩, fun c z hc => ?_⟩
  -- IPlaced
  · rcases ht with ht | ht
    · exact J.ip.n.tcb t ht
    · exact (hTw t ht).1
  · rcases ht with ht | ht
    · exact J.ip.n.disj n hn t ht
    · obtain ⟨-, h1, h2, -⟩ := hTw t ht; have := offN n hn; omega
  · rcases ht with ht | ht
    · exact J.ip.e.tcb t ht
    · exact (hTw t ht).1
  · rcases ht with ht | ht
    · exact J.ip.e.et e he t ht
    · obtain ⟨-, h1, h2, -⟩ := hTw t ht; have := offE e he; omega
  · rcases ht with ht | ht
    · exact J.ip.e.rt r hr t ht
    · obtain ⟨-, h1, h2, -⟩ := hTw t ht; have := offR r hr; omega
  · rcases ht with ht | ht
    · exact J.ip.e.bt wp hw t ht
    · obtain ⟨-, h1, h2, -⟩ := hTw t ht; have := hB wp hw; omega
  -- zH
  · rcases ht with ht | ht
    · exact keep (J.zH.1 t ht) (by simp only [HKind.bits]; have := offT t ht; omega)
    · exact hout_new hout (hTw t ht).2.2.2 rfl
  · exact keep (J.zH.2.1 e he) (by simp only [HKind.bits]; have := offE e he; omega)
  · exact keep (J.zH.2.2.1 r hr) (by simp only [HKind.bits]; have := offR r hr; omega)
  · exact keep (J.zH.2.2.2 n hn) (by simp only [HKind.bits]; have := offN n hn; omega)
  -- hset
  · rcases hout_back hout he with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hset.1 e h
  · rcases hout_back hout hn with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hset.2.1 n h
  · rcases hout_back hout hr with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hset.2.2 r h
  -- hscC
  · rcases hout_back hout hc with ⟨-, hK⟩ | h
    · cases hK
    · exact J.hscC c z h


/-- **The set and heap fields at `T ∪ Tn`** (module docstring). -/
theorem JAtZ.addSetsT {s : S} {a : A'} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s) {lo hi : Nat}
    (hfree : RegionFree Z.th lo hi)
    (hspec : ∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat)
    (hB : ∀ wp ∈ Z.B, wp.1.val + 8 ≤ lo ∨ hi ≤ wp.1.val) (harch : ArchFitHyp H σ)
    {A k w : Nat} (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) {H' : Heap}
    (hout : HOut H H' A (A + w * k) A k w (some .tcb)) {Tn : Set U64}
    (hTw : ∀ t ∈ Tn, P1.TcbAddr t ∧ lo ≤ t.val ∧ t.val + 4096 ≤ hi ∧ NewAt A k w t)
    {σ' : Fl4Spec.State Unit}
    (hback : ∀ o ko, σ'.kheap o = some ko → σ.kheap o = some ko ∨
      (∃ r cs', ko = .cnode r cs') ∨ (∃ t ∈ Tn, t.bv = o ∧ ∃ d, ko = .tcb (Fl4Spec.defaultTcb d)))
    {Z' : XSets} (hT : Z'.T = Z.T ∪ Tn) (hR : Z'.R = Z.R) (hC : Z'.C = Z.C) (hBB : Z'.B = Z.B)
    (hE : Z'.E = Z.E) (hN : Z'.N = Z.N) :
    KsApart Z'.N Z'.T Z'.E Z'.R Z'.B (L.ksb s') ∧ IPlaced Z'.N Z'.T Z'.E Z'.R Z'.B ∧
    (∀ n ∈ Z'.N, n.val + 40 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ n.val) ∧
    Sched.SpecCover H' σ' ∧ Sched.ObjCover Z'.N Z'.T Z'.E Z'.R Z'.C σ' ∧
    ((∀ t ∈ Z'.T, H' t = some .tcb) ∧ (∀ e ∈ Z'.E, H' e = some .ep) ∧ (∀ r ∈ Z'.R, H' r = some .reply) ∧
      (∀ n ∈ Z'.N, H' n = some .ntfn)) ∧
    ((∀ e, H' e = some .ep → e ∈ Z'.E) ∧ (∀ n, H' n = some .ntfn → n ∈ Z'.N) ∧
      (∀ r, H' r = some .reply → r ∈ Z'.R)) ∧
    (∀ c z, H' c = some (.sc z) → c ∈ Z'.C) :=
  JAtZB.addSetsT J.toB hks hfree hspec hB harch hlo hhi hk1 hout hTw hback hT hR hC hBB hE hN

end

end

end Fl4Proofs.P3
