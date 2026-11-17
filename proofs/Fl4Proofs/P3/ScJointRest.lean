/-
P3 (DESIGN.md §9), scheduling contexts: **the frame fields of `JAtZ` across
an SC step** (the fold's (c)): from FL4's writes in `TFoot` and the spec's
`ScTKw`, the IPC-buffer words (`BufWordRel`), the slots apart from the
scheduler's objects (`SlotsApart`), and the joint placement (`JPlaced`).

* `TFoot.ne_buf`: a `TFoot` word is no IPC-buffer word.
* `SlotsApart.sc_frame`, `JAtZ.sc_buf`, `JAtZ.sc_jpl`.
-/
import Fl4Proofs.P3.ScJointFrame
import Fl4Proofs.P3.ScPlaceSc
import Fl4Proofs.P3.ScFieldKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **A `TFoot` word is no IPC-buffer word.** -/
theorem Sched.TFoot.ne_buf {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {b : U64} (hb : TFoot st T N C c s σ b) {t : U64} (ht : t ∈ T) :
    b ≠ tIpcBufA t := by
  rcases hb with hb | ⟨y, hy, rfl⟩
  · exact hb.ne_tcbw hS ht (K := 3512#u64) (by simp) (fun h => h.2.2.2.2.1 rfl)
  · obtain ⟨Q, R, hc, -⟩ := hS.lists
    intro e
    unfold P1.yieldA tIpcBufA at e
    rw [tt_eq_iff (hc.tcbs y hy) (hc.tcbs t ht) (by simp) (by simp)] at e
    exact absurd e.2 (by decide)

/-- **`SlotsApart` across a step** keeping the kernel-state base and the SCs'
sizes. -/
theorem Sched.SlotsApart.sc_frame {th : TypedHeap} {T N C R : Set U64} {c : U64} {s s' : S}
    {σ σ' : Fl4Spec.State Unit} (h : SlotsApart (st := st) th T N C R c s σ) (hks : L.ksb s' = L.ksb s)
    (hsz : SzKeep σ σ') : SlotsApart (st := st) th T N C R c s' σ' := by
  intro a ha
  obtain ⟨h1, h2, h3, h4, h5⟩ := h a ha
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp only [P1.LawfulStore.nodeBase, hks]
  refine ⟨h1, by rw [hnb]; exact h2, h3, fun sc hsc x n hk => ?_, h5⟩
  obtain ⟨x0, hk0⟩ := hsz _ x n hk
  exact h4 sc hsc x0 n hk0

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **`BufWordRel` after an SC step.** -/
theorem JAtZ.sc_buf {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    BufWordRel Z.T (L.mem s') σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  exact J.buf.frame (fun t ht => hw.mem_eq (tIpcBufA_aligned (hc.tcbs t ht)) fun hb => hb.ne_buf hS ht rfl)
    hK.bufKeep

/-- **`SlotsApart` after an SC step.** -/
theorem JAtZ.sc_apart {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ' :=
  J.apart.sc_frame hw.1 hK.szKeep

/-- **`JPlaced` after an SC step.** -/
theorem JAtZ.sc_jpl {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') :
    ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ' := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hwU : P1.WritesIn st s s' (UFoot st Z.T Z.N Z.C Z.R Z.c s σ) := hw.mono fun b hb => Or.inl hb
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') := slotsSame_of_ufoot hJ.pl hS J.rp J.apart hwU
  have hIA := hJ.irqApart (c := Z.c) J.zH.1 J.zH.2.2.2 J.c0 J.zH.2.2.1 J.kern.ksbFit
  exact ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => hK.szKeep q.bv y n hq) hw.1 (irq_of_ufoot hS J.rp hIA hwU)⟩


/-- The arch objects are kept across an `ScTKw` step. -/
theorem Sched.ScTKw.archObj {P : Fl4Spec.ObjRef → Prop} {σ σ' : Fl4Spec.State Unit} (hK : ScTKw P σ σ')
    {p : Fl4Spec.ObjRef} {ao : Fl4Spec.ArchKernelObj} (hp : σ.kheap p = some (.archObj ao)) :
    σ'.kheap p = some (.archObj ao) := by
  have hk := hK.kh p
  rw [hp] at hk
  cases h' : σ'.kheap p with
  | none => rw [h'] at hk; exact hk.elim
  | some o =>
    rw [h'] at hk
    rcases hk with e | ⟨x, y, e1, -⟩ | ⟨x, y, n, e1, -⟩ | ⟨x, y, e1, -⟩ | ⟨x, y, e1, -⟩
    · rw [e]
    all_goals cases e1

/-- **`JKern` after an SC step**: the current thread and SC words are the
spec's, which the step keeps (`ScTKw`, `FK`); the node-0 `DEBUG_TCBS` word
kept (`hDbg`, P1-supplied); the dead set shrinking. -/
theorem JAtZ.sc_kern {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {P : Fl4Spec.ObjRef → Prop} {D' : Set U64}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ') (hF : FK σ σ')
    (hX' : XTopAt (L := L) AR Z s' a' σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS))
    (hD : D' ⊆ D) : JKern (L := L) H Cs D' Z.th s' σ' := by
  have K := J.kern
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hX'.fin.1.1.1.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hK.ct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hF.1]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => K.orig sl (by rw [← hK.orig]; exact h), by rw [ecw, hK.ct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hK.arch]; exact hK.archObj hpt⟩, by rw [hK.arch]; exact K.ga, by rw [hK.arch]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    fun h => K.cscLive (hD (by rw [ecs] at h; exact h)), K.csLt⟩
  rw [hna, hDbg]; exact K.head


/-- **`JCovD` after an SC step**, the dead set shrinking to `D'`: the dead
of `D'` dead after (`hdead`), the others of `D` covered after (`hcov`). -/
theorem JAtZ.sc_jcov {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {D' : Set U64}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ))
    (hdead : ∀ q ∈ D', Sched.DeadP (L := L) H s' q)
    (hcov : ∀ q ∈ D, q ∉ D' →
      (∀ k, Z.th q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + max (objSize k) 1)) ∧
      (∀ k, H q = some k → Sched.Covered (L.mem s') Z.G q.val (q.val + 2 ^ k.bits))) :
    Sched.JCovD (L := L) Z.th H Z.G D' Cs s' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  have hk : ∀ y ∈ Z.G.chains.flatten, physF (capV (L.mem s) y) = true → isUt (capV (L.mem s) y) = false →
      y ∈ Z.G.chains.flatten ∧ capV (L.mem s') y = capV (L.mem s) y :=
    fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩
  have JC := J.jcov
  refine ⟨fun q k hq => ?_, fun q k hq => ?_, hdead, fun x hx p sb fi d hc => ?_⟩
  · rcases JC.th q k hq with hc | hd
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr h
      · exact Or.inl ((hcov q hd h).1 k hq)
  · rcases JC.h q k hq with hc | hd
    · exact Or.inl (Sched.covered_keep hc hk)
    · by_cases h : q ∈ D'
      · exact Or.inr h
      · exact Or.inl ((hcov q hd h).2 k hq)
  · rw [hSS.capV (hsl x hx)] at hc
    have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
    obtain ⟨h1, h2⟩ := JC.ks x hx p sb fi d hc
    exact ⟨by rw [hks]; exact h1, fun c hc' => by rw [hnb]; exact h2 c hc'⟩

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after an SC step**: the caps kept (slots
apart), the free parts zero (no SC-step word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state and
the node-0 `DEBUG_TCBS` word (`hDbg`, P1-supplied). -/
theorem JAtZ.sc_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj hS h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  refine ⟨U.pal, U.pfit, U.fiLe, U.high, by rw [hcpu, hna]; exact U.actZ, U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hK.cdt] at h0; exact h0),
    fun k0 v0 => by simpa only [hna] using U.pp k0 v0, ?_, by rw [hna]; exact U.dwReg,
    by rw [hK.arch]; exact U.gReg⟩
  · intro w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero w hal h1 h2
    rcases tfoot_tcb hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi dev hcv).2 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi dev hcv n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi dev hcv sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro h0 hf0
    rw [hK.cdt] at h0
    obtain ⟨r1, r2, r3⟩ := U.rst h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← hK.orig]; exact h), r2, by rw [hna, hDbg]; exact r3⟩

end

end

end Fl4Proofs.P3
