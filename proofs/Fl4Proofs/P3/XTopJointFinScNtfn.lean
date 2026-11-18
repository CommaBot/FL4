/-
P3 (DESIGN.md §9), CSpace: **`unbind_ntfn` of an SC at `J`** (a step of a
final SC cap's finalisation, XTopJointFinSc's `JScFinSteps.unbindNtfn`):
`JAtZ.unbindNtfnJ`.

The spec's `sched_context_unbind_ntfn` clears the notification's `SC` link
and the SC's `NTFN` link: a frame `NFr true` of the notification
(`Sched.unbindScNtfn_nfr`; nothing when unbound). FL4's writes
(`unbind_ntfn_refines`: the notification's `SC` word and the SC's `NTFN`
word) are in `KFoot`, so in `FinW`; `IRel` after from `xtop_sc_step`; P1's
`unbind_ntfn.blk`; then XTopJointFinThread's `JAtZ.nfrStep`.
-/
import Fl4Proofs.P3.XTopJointFinScInact
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open Fl4Spec Classical Fl4Proofs.P3.Notif

noncomputable section

/-- **The spec's `sched_context_unbind_ntfn` of a bound SC**: its outcome and
the frame `NFr true` of the notification. -/
theorem unbindScNtfn_nfr {σ : State Unit} {p n : ObjRef} {y : SchedContext} {m : Nat} {xn : Notification}
    (hk : σ.kheap p = some (.schedContext y m)) (hy : y.scNtfn = some n)
    (hkn : σ.kheap n = some (.notification xn)) :
    schedContextUnbindNtfn (Z := Unit) p σ = ({((), updSc (updK σ n (.notification { xn with ntfnSc := none })) p
        { y with scNtfn := none } m)}, False) ∧
      NFr true n σ (updSc (updK σ n (.notification { xn with ntfnSc := none })) p { y with scNtfn := none } m) := by
  have hnp : n ≠ p := fun e => by rw [e, hk] at hkn; cases hkn
  have hk1 : (updK σ n (.notification { xn with ntfnSc := none })).kheap p = some (.schedContext y m) := by
    simp [updK, Ne.symm hnp, hk]
  have hg : getScObjRef (Z := Unit) SchedContext.scNtfn p σ = ({(y.scNtfn, σ)}, False) := by
    unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
  refine ⟨?_, ?_⟩
  · unfold schedContextUnbindNtfn
    rw [nd_bind_one hg, hy]
    show (setNtfnObjRef ntfnScUpdate n none >>= _) σ = _
    rw [nd_bind_one (setNtfnSc_eq _ hkn)]
    exact updateSchedContext_eq hk1 _
  · exact (NFr.upd (o' := .notification { xn with ntfnSc := none }) hkn (Or.inr (Or.inr ⟨xn, _, rfl, rfl, rfl, List.Sublist.refl _, fun _ => Or.inl rfl, Or.inr rfl,
      fun _ => Or.inl rfl, Or.inl rfl⟩))).trans
      (NFr.upd hk1 (Or.inr (Or.inl ⟨y, m, y.scRefills, none, rfl, rfl, fun _ => rfl, Or.inr rfl⟩)))

theorem unbindScNtfn_none {σ : State Unit} {p : ObjRef} {y : SchedContext} {m : Nat}
    (hk : σ.kheap p = some (.schedContext y m)) (hy : y.scNtfn = none) :
    schedContextUnbindNtfn (Z := Unit) p σ = ({((), σ)}, False) := by
  have hg : getScObjRef (Z := Unit) SchedContext.scNtfn p σ = ({(y.scNtfn, σ)}, False) := by
    unfold getScObjRef; rw [nd_bind_one (getSchedContext_eq hk)]; rfl
  unfold schedContextUnbindNtfn
  rw [nd_bind_one hg, hy]; rfl

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **`unbind_ntfn` of an SC at `J`** (module docstring): XTopJointFinSc's
`JScFinSteps.unbindNtfn`, proved (for any SC of the SCs, non-null). -/
theorem JAtZ.unbindNtfnJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64) :
    schedcontext.unbind_ntfn st s p ⦃ s' => ∃ σ',
      Fl4Spec.schedContextUnbindNtfn (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      JTP (L := L) arI AR Z H Cs s' a σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨y, m, hk, hx⟩ := hs.scs p hpC
  have hbn : ∀ n : U64, y.scNtfn = some n.bv → n ∈ Z.N := by
    intro n hn
    obtain ⟨xn, hxn⟩ := J.sv.scNtfn _ y m _ hk hn
    obtain ⟨m', hm', hmm⟩ := J.obj.ntfn _ xn hxn
    rw [← P1.eq_of_bv hmm]; exact hm'
  have hpS : p ∈ P1.Heap.scs H := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨_, (hJ.sc p y m hp0 hk).2⟩
  refine WP.spec_mono (WP.spec_and (unbind_ntfn_refines s σ hS hR J.nsc J.inv hpC hp0 hk hbn)
    (P1.schedcontext.unbind_ntfn.blk s p J.blk fun _ => hpS)) ?_
  rintro s' ⟨⟨σ', he, hS', hR', -, hI', -, hw, -⟩, hblk, hfoot, -⟩
  -- the spec frame
  obtain ⟨n, F⟩ : ∃ n, NFr true n σ σ' := by
    cases hy : y.scNtfn with
    | none =>
      have := the_result (unbindScNtfn_none hk hy) he
      subst this
      exact ⟨p.bv, NFr.refl _ _ _⟩
    | some n =>
      obtain ⟨xn, hkn⟩ := J.sv.scNtfn _ y m _ hk hy
      obtain ⟨e1, F⟩ := unbindScNtfn_nfr hk hy hkn
      have := the_result e1 he
      subst this
      exact ⟨n, F⟩
  -- FL4's writes
  have hWK : P1.WritesIn st s s' (KFoot st Z.T Z.N Z.C Z.c s σ) :=
    Sched.WritesIn.kfoot_of_nw_scw hS hpC (K := 40#u64) (by simp) (by simp) (by decide) hw
  have hW : P1.WritesIn st s s' (TFoot st Z.T Z.N Z.C Z.c s σ) := Sched.WritesIn.tfoot_of_kfoot hWK
  have hK : ScTKw (fun _ => False) σ σ' :=
    nkt_schedContextUnbindNtfn p.bv σ ((), σ') (by rw [he]; exact Set.mem_singleton _)
  have hX' := xtop_sc_step (ct := σ.curThread) J.xtop J.ip J.nk hW (hK.mono fun _ h => h.elim) hS' hR' id
  have hI3 := hX'.irelK (by rw [hW.1]; exact J.ks) (J.sc_buf hW hK)
  rw [hK.arch] at hI3
  have hFr : IFrame (L := L) Z.th s s' := ⟨J.xtop.slotsSame_of hW fun b h => Sched.tfoot_oobj hS h, hW.1⟩
  obtain ⟨V', J'⟩ := J.nfrStep hI3 hFr (hWK.mono fun b hb => Or.inl hb) F hI' hK.ckeep hblk hfoot
  exact ⟨σ', he, V', Ac, Lst, D, J'⟩

end

end

end Fl4Proofs.P3
