/-
P3 (DESIGN.md §9), scheduling contexts: **`JAtZ` across an SC step**
(`JAtZ.sc_frame`): FL4's writes in the SC code's footprint (`TFoot`) and the
spec's `ScTKw` step keep the fields no SC step touches, given the ones it
re-establishes.

Kept by the frame: the kernel-global apartness (`ks`, `nk`: the base is
kept), the sets' fields (`thT`, `ip`, `zH`, `c0`, `bound`), the spec objects'
cover (`cover`, `obj`: `ScTKw` keeps every object's kind), `SpecFree` (the
caps and the objects' sizes kept), and the CSpace invariants (`del`, `ut`,
`finM`: no slot word is in `TFoot`, `SlotsSame`).

Re-established by the step (premises): `XTopAt`, the call stacks, yield,
MCP, buffer words, `RPlaced`, `SlotsApart`, `JPlaced`, the dead set, the
kernel-global words (`JKern`), the untyped caps' facts, the scheduler
invariants and P1's `BlkOK`.
-/
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

theorem Sched.ScTKw.ksz {P : ObjRef → Prop} {σ σ' : State Unit} (hK : Sched.ScTKw P σ σ') : KSz σ σ' := by
  intro o ko' ho
  have hk := hK.kh o
  rw [ho] at hk
  cases h0 : σ.kheap o with
  | none => rw [h0] at hk; exact hk.elim
  | some ko =>
    rw [h0] at hk
    refine ⟨ko, rfl, ?_⟩
    rcases hk with e | ⟨x, y, e1, e2, -⟩ | ⟨x, y, n, e1, e2⟩ | ⟨x, y, e1, e2, -⟩ | ⟨x, y, e1, e2, -⟩
    · rw [e]
    all_goals (subst e1; subst e2; rfl)

theorem Sched.ScTKw.kind_back {P : ObjRef → Prop} {σ σ' : State Unit} (hK : Sched.ScTKw P σ σ') {o : ObjRef}
    {ko' : KernelObject} (ho : σ'.kheap o = some ko') :
    ∃ ko, σ.kheap o = some ko ∧ ((∃ x, ko' = .notification x) → ∃ x, ko = .notification x) ∧
      ((∃ x, ko' = .endpoint x) → ∃ x, ko = .endpoint x) ∧ ((∃ x, ko' = .reply x) → ∃ x, ko = .reply x) ∧
      ((∃ x, ko' = .tcb x) → ∃ x, ko = .tcb x) ∧ ((∃ x n, ko' = .schedContext x n) → ∃ x n, ko = .schedContext x n) := by
  have hk := hK.kh o
  rw [ho] at hk
  cases h0 : σ.kheap o with
  | none => rw [h0] at hk; exact hk.elim
  | some ko =>
    rw [h0] at hk
    refine ⟨ko, rfl, ?_⟩
    rcases hk with e | ⟨x, y, e1, e2, -⟩ | ⟨x, y, n, e1, e2⟩ | ⟨x, y, e1, e2, -⟩ | ⟨x, y, e1, e2, -⟩
    · subst e; exact ⟨id, id, id, id, id⟩
    all_goals (subst e1; subst e2; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> simp_all)

theorem Sched.SpecCover.tkw {H : P1.Heap} {P : ObjRef → Prop} {σ σ' : State Unit} (h : Sched.SpecCover H σ)
    (hK : Sched.ScTKw P σ σ') : Sched.SpecCover H σ' := by
  refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun y k ho => ?_⟩
  · obtain ⟨ko, hk, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ntfn o x0 hk
  · obtain ⟨ko, hk, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ep o x0 hk
  · obtain ⟨ko, hk, -, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.reply o x0 hk
  · obtain ⟨ko, hk, -, -, -, -, h1⟩ := hK.kind_back ho
    obtain ⟨y0, k0, rfl⟩ := h1 ⟨y, k, rfl⟩; exact h.sc0 y0 k0 hk

theorem Sched.ObjCover.tkw {N T E R C : Set U64} {P : ObjRef → Prop} {σ σ' : State Unit}
    (h : Sched.ObjCover N T E R C σ) (hK : Sched.ScTKw P σ σ') : Sched.ObjCover N T E R C σ' := by
  refine ⟨fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o x ho => ?_, fun o y k ho => ?_⟩
  · obtain ⟨ko, hk, -, -, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.tcb o x0 hk
  · obtain ⟨ko, hk, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ntfn o x0 hk
  · obtain ⟨ko, hk, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.ep o x0 hk
  · obtain ⟨ko, hk, -, -, h1, -⟩ := hK.kind_back ho
    obtain ⟨x0, rfl⟩ := h1 ⟨x, rfl⟩; exact h.reply o x0 hk
  · obtain ⟨ko, hk, -, -, -, -, h1⟩ := hK.kind_back ho
    obtain ⟨y0, k0, rfl⟩ := h1 ⟨y, k, rfl⟩; exact h.sc o y0 k0 hk

end Spec

theorem FinM.of_capV {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G)
    (hc : ∀ x ∈ G.chains.flatten, capV mem' x = capV mem x) : FinM mem' G := by
  have hc' : ∀ ch ∈ G.chains, ∀ x ∈ ch, capV mem' x = capV mem x := fun ch hch x hx =>
    hc x (List.mem_flatten.2 ⟨ch, hch, hx⟩)
  refine ⟨fun ch1 h1 ch2 h2 x hx y hy ho => ?_, fun x hx y hy hne ho h1 h2 h3 => ?_,
    fun x hx y hy hne h1 h2 h3 => ?_, fun x hx y hy hne h1 => ?_⟩
  · rw [hc' ch1 h1 x hx, hc' ch2 h2 y hy] at ho; exact hF.conn ch1 h1 ch2 h2 x hx y hy ho
  · simp only [hc x hx, hc y hy] at ho h1 h2 h3 ⊢; exact hF.key x hx y hy hne ho h1 h2 h3
  · unfold srM at h3; simp only [hc x hx, hc y hy] at h1 h2 h3 ⊢; exact hF.fnest x hx y hy hne h1 h2 h3
  · simp only [hc x hx, hc y hy] at h1 ⊢; exact hF.zfin x hx y hy hne h1

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **`JAtZ` across an SC step** (module docstring). -/
theorem JAtZ.sc_frame {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} {P : Fl4Spec.ObjRef → Prop}
    (hw : P1.WritesIn st s s' (Sched.TFoot st Z.T Z.N Z.C Z.c s σ)) (hK : Sched.ScTKw P σ σ')
    (hX : XTopAt (L := L) AR Z s' a' σ')
    (hcall : Sched.CallRel (L.mem s') Z.R Z.C σ' Lst') (hrf : Sched.RFree (L.mem s') Z.R Z.C σ' Lst')
    (hyl : Sched.YieldRel Z.T Z.C (L.mem s') σ') (hmcp : Sched.McpRel Z.T (L.mem s') σ')
    (hbuf : BufWordRel Z.T (L.mem s') σ')
    (hrp : Sched.RPlaced st Z.N Z.T Z.C Z.R Z.c s' σ') (hap : Sched.SlotsApart (st := st) Z.th Z.T Z.N Z.C Z.R Z.c s' σ')
    (hjpl : ∃ Tr Cq, Sched.JPlaced (L := L) Z.th H Tr Cq s' σ') (hjc : Sched.JCovD (L := L) Z.th H Z.G D' Cs s')
    (hkern : JKern (L := L) H Cs D' Z.th s' σ')
    (hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi)
    (hnsc : Sched.NSC Z.N Z.C σ') (hinv : Sched.Inv σ') (hcur : σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ') (hoff : Sched.OffOK σ')
    (hact : Sched.ActIdle σ') (hbsa : Sched.BlockedScActive σ') (hsv : Sched.SchedValid σ') (hcr : CurRun σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s') :
    JAtZ (L := L) arI AR Z H Cs Ac' Lst' D' s' a' σ' := by
  have hks : L.ksb s' = L.ksb s := hw.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s') :=
    J.xtop.slotsSame_of hw fun b h => Sched.tfoot_oobj J.xtop.fin.1.1.1 h
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  refine ⟨hX, hcall, hrf, hyl, hmcp, hbuf, by rw [hks]; exact J.ks, J.thT, J.ip, hrp, hap,
    fun n hn => by rw [hks]; exact J.nk n hn, hjpl, J.cover.tkw hK, J.obj.tkw hK, J.zH, ?_, hjc, hkern,
    J.del.of_same hSS, UtInv.of_same hM J.ut hSS, J.bound, fun G hG => ?_, hutc, hnsc, hinv, hcur, hoff, hact,
    J.c0, hbsa, hsv, hcr, hblk⟩
  · refine SpecFree.frame J.sfree (fun x' hx' p sb fi' d hc => ⟨x', hx', fi', d, ?_, le_rfl⟩) hK.ksz
    rw [← hSS.capV (hsl x' hx')]; exact hc
  · have hG0 : MdbLinks Z.th (L.mem s) G := hG.of_same_symm hSS
    have hsl' : ∀ x ∈ G.chains.flatten, IsSlot Z.th x := fun x h => ((hG0.members x).1 h).1
    exact (J.finM G hG0).of_capV fun x hx => hSS.capV (hsl' x hx)

end

end

end Fl4Proofs.P3
