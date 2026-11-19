/-
P3 (DESIGN.md §9), IPC: **`XTopAt` at the same sets after IPC work**
(`XTopAt.irel_sameZ`), the variant of `XTopAt.irel_same` that keeps the
VSpace sets: from `XTopAt Z` before, `IRel` after, FL4 writing only words of
the other objects (`OObj`, the footprint the IPC sites give `IRel.iframe_of`)
and the spec keeping the arch state, the arch objects and the SC sizes,
`XTopAt` at `Z` itself.

`irel_same` takes the VSpace sets after from `IRel`'s `VsP.ex`, an
existential, so nothing ties them to `Z`'s; a fact about `Z`'s VSpace sets
carried at `J` (the planned weakened cap field `VsCapsW`, vsreach.md vs11)
needs the sets kept. The VSpace part at `Z`'s sets is carried across as in
`VsP.frame`: the VSpace words are no `OObj` word (`TopPlaced.disj`), the
arch objects are kept, and `OObj` after is `OObj` before (SC sizes kept).
-/
import Fl4Proofs.P3.IpcSlotsSame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P1 Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

/-- **`XTopAt` at the same sets after IPC work** (module docstring). -/
theorem XTopAt.irel_sameZ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {cr : Fl4Spec.Cr3}
    (hI : IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ') (hAR : AR a' cr)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hcdt : σ'.cdt = σ.cdt)
    (hio : σ'.isOriginalCap = σ.isOriginalCap) (hK : KSub σ σ') {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hWO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (har : σ'.archState = σ.archState)
    (harch : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = σ.kheap q) (hsz : Sched.SzKeep σ σ') :
    XTopAt (L := L) AR Z s' a' σ' := by
  have hks : L.ksb s' = L.ksb s := hW.1
  obtain ⟨V', hX3⟩ := XTopAt.irel_same hX hI hAR hSS hcdt hio hK hks
  obtain ⟨⟨⟨-, hP⟩, hR, hPt, hPI, -⟩, -, -, -⟩ := hX
  obtain ⟨⟨⟨hO3, -⟩, -, -, -, hCO3⟩, hB3, hIR3, hEA3⟩ := hX3
  obtain ⟨hksb, -, hmem⟩ := hW
  have hout : ∀ b, Aligned b → Vs.VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → L.mem s' b = L.mem s b :=
    fun b hb hv => hmem b hb fun hw => hP.disj b (hWO b hw) hv
  have hvw : ∀ b, Vs.VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hout b (hP.vo b hb).1 (Vs.vsWrite_vobj hP.vs hb)
  have hpw : ∀ b, Vs.PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b → L.mem s' b = L.mem s b := fun b hb => by
    refine hout b (hP.po b hb).1 ?_
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    exact Vs.table_vobj hP.pt hq hi _
  have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [LawfulStore.nodeBase, hksb]
  have hOO : ∀ x, Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' x → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ x := by
    intro x ha
    unfold Vs.OObj at ha ⊢
    rw [hnb, hksb] at ha
    rcases ha with h | h | h | h | h | h | ⟨sc, hsc, x0, n, hk, hob⟩ | h
    all_goals first
      | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr (Or.inl h))
      | exact Or.inr (Or.inr (Or.inr (Or.inl h))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      | (obtain ⟨x1, h1⟩ := hsz _ x0 n hk
         exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x1, n, h1, hob⟩)))))))
  refine ⟨⟨⟨hO3, ?_⟩, ?_, ?_, ?_, hCO3⟩, hB3, hIR3, hEA3⟩
  · exact ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun x hx => by rw [hksb]; exact hP.disj x (hOO x hx),
      fun x h1 h2 => by rw [hnb] at h1 h2; exact hP.nodeE x h1 h2,
      hP.po, hP.ps, by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd,
      by rw [hksb]; exact hP.tko⟩
  · rw [hksb]
    refine hR.frame hvw (by rw [har]) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact harch _ _ hf
  · refine hPt.frame hpw fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact harch _ _ hg
  · intro q hq lo hl
    have hw : Vs.VsWrite Z.P (L.ksb s) (Vs.peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hw]; exact hPI q hq lo hl


/-- **`irel_same` with the sets kept, in the shape of its uses**: the post's
sets `V'` are `Z`'s (`irel_sameZ`). -/
theorem XTopAt.irel_sameV {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {cr : Fl4Spec.Cr3}
    (hI : IRel st Z.th cr Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ') (hAR : AR a' cr)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hcdt : σ'.cdt = σ.cdt)
    (hio : σ'.isOriginalCap = σ.isOriginalCap) (hK : KSub σ σ') {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hWO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (har : σ'.archState = σ.archState)
    (hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao)) (hsz : Sched.SzKeep σ σ') :
    ∃ V' : XVs, XTopAt (L := L) AR (Z.mv Z.G V') s' a' σ' ∧ V' = Z.vs :=
  ⟨Z.vs, hX.irel_sameZ hI hAR hSS hcdt hio hK hW hWO har (fun q ao h => (hao q ao h).trans h.symm) hsz, rfl⟩

/-- **The VSpace sets put back** after a step whose post gave `XTopAt` at
some sets `V'`: FL4 writing no VSpace word of `Z`'s sets (`hWv`: a written
word outside the objects is no `VObj` word), the spec keeping the arch
state, the arch objects and the SC sizes; `XTopAt` at `Z`'s sets with the
post's ghost tree. -/
theorem XTopAt.vs_back {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {G' : MdbGhost} {V' : XVs}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hWv : ∀ b, W b → OutsideObjects Z.th b → Vs.VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b → False)
    (har : σ'.archState = σ.archState)
    (harch : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = σ.kheap q) (hsz : Sched.SzKeep σ σ') :
    XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ' := by
  obtain ⟨⟨⟨-, hP⟩, hR, hPt, hPI, -⟩, -, -, -⟩ := hX
  obtain ⟨⟨⟨hO3, -⟩, -, -, -, hCO3⟩, hB3, hIR3, hEA3⟩ := hX'
  obtain ⟨hksb, -, hmem⟩ := hW
  have hvw : ∀ b, Vs.VsWrite Z.P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hmem b (hP.vo b hb).1 fun hw => hWv b hw (hP.vo b hb) (Vs.vsWrite_vobj hP.vs hb)
  have hpw : ∀ b, Vs.PtWAll Z.L4 Z.L3 Z.L2 Z.L1 b → L.mem s' b = L.mem s b := fun b hb => by
    refine hmem b (hP.po b hb).1 fun hw => hWv b hw (hP.po b hb) ?_
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    exact Vs.table_vobj hP.pt hq hi _
  have hnb : L.nodeBase s' Z.c = L.nodeBase s Z.c := by simp [LawfulStore.nodeBase, hksb]
  have hOO : ∀ x, Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' x → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ x := by
    intro x ha
    unfold Vs.OObj at ha ⊢
    rw [hnb, hksb] at ha
    rcases ha with h | h | h | h | h | h | ⟨sc, hsc, x0, n, hk, hob⟩ | h
    all_goals first
      | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr (Or.inl h))
      | exact Or.inr (Or.inr (Or.inr (Or.inl h))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      | (obtain ⟨x1, h1⟩ := hsz _ x0 n hk
         exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x1, n, h1, hob⟩)))))))
  refine ⟨⟨⟨hO3, ?_⟩, ?_, ?_, ?_, hCO3⟩, hB3, hIR3, hEA3⟩
  · exact ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun x hx => by rw [hksb]; exact hP.disj x (hOO x hx),
      fun x h1 h2 => by rw [hnb] at h1 h2; exact hP.nodeE x h1 h2,
      hP.po, hP.ps, by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd,
      by rw [hksb]; exact hP.tko⟩
  · rw [hksb]
    refine hR.frame hvw (by rw [har]) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact harch _ _ hf
  · refine hPt.frame hpw fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact harch _ _ hg
  · intro q hq lo hl
    have hw : Vs.VsWrite Z.P (L.ksb s) (Vs.peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hw]; exact hPI q hq lo hl

/-- `vs_back` for FL4 writing words of the other objects only (`OObj`, the
footprint the IPC sites give `IRel.iframe_of`), the arch objects kept in the
`kern_keep` form. -/
theorem XTopAt.vs_backO {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {G' : MdbGhost} {V' : XVs}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b)
    (har : σ'.archState = σ.archState)
    (hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao)) (hsz : Sched.SzKeep σ σ') :
    XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ' :=
  hX.vs_back hX' hW (fun b hb _ hv => hX.fin.1.2.disj b (hWO b hb) hv) har
    (fun q ao h => (hao q ao h).trans h.symm) hsz

/-- `vs_back` for FL4 writing slot words only. -/
theorem XTopAt.vs_backS {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {G' : MdbGhost} {V' : XVs}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hW : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (har : σ'.archState = σ.archState)
    (harch : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = σ.kheap q) (hsz : Sched.SzKeep σ σ') :
    XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ' :=
  hX.vs_back hX' hW (fun _ hb ho _ => slotWd_inObj hX.rel.1 hb ho) har harch hsz

/-- `vs_backS` for a spec step changing CNodes and TCBs' caps only (`CnK`). -/
theorem XTopAt.vs_backC {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {G' : MdbGhost} {V' : XVs}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hW : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hcn : CnK σ σ') :
    XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ' :=
  hX.vs_backS hX' hW (by have e := congrArg Fl4Spec.AbstractState.archState hcn.1; exact e)
    (fun q ao hq => by
      rcases hcn.2 q with e | ⟨r, cs, cs', h1, -⟩ | ⟨x, y, h1, -⟩
      · exact e
      · rw [hq] at h1; cases h1
      · rw [hq] at h1; cases h1)
    (CnK.szKeep hcn)

/-- `vs_backS` for a CNode-only spec step (`CnK`, `KeepC`). -/
theorem XTopAt.vs_backK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s s' : S} {a a' : A}
    {σ σ' : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ) {G' : MdbGhost} {V' : XVs}
    (hX' : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') (hW : P1.WritesIn st s s' (Sched.SlotWd Z.th))
    (hcn : CnK σ σ') (hkc : KeepC σ σ') :
    XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ' :=
  hX.vs_backS hX' hW (ostep_of_cnk hcn hkc).2.2 (fun q ao hq => by
    rcases hkc q with e | ⟨r, cs, cs', h1, -⟩
    · exact e
    · rw [hq] at h1; cases h1) (SzKeep.of_keepC hkc)

end

end

end Fl4Proofs.P3
