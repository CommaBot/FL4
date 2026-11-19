/-
P3 (DESIGN.md §9), untyped: **fresh replies into the relations** (the
reply half of the no-reset retype at `J`, handoff/utj.md "Round 5").

A no-reset retype of replies (type 6) adds the window's objects to `R`:
free in the spec (`defaultReply`: no TCB, no SC), their FL4 words zero.

* `rTcbA_eqW`, `rPrevA_eqW`, `rNextA_eqW`: the reply words as offsets.
* `Sched.CallRel.addR`, `Sched.RFree.addR`, `Sched.RRecv.addR`: the
  call-stack relation, the free replies' and the receive-bound replies'
  invariants at `R ∪ Rn` (a new reply is on no stack: the stacks hold
  replies of `R`, and the new ones are not in `R`; its link words are zero).
* `oobj_unionR`, `XTopAt.addR`: `XTopAt` with the new replies added to `R`
  (as UtEpXTop's `XTopAt.addE`).
-/
import Fl4Proofs.P3.UtEpJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

theorem rTcbA_eqW (r : U64) : Endp.rTcbA r = core.num.U64.wrapping_add r 0#u64 := by
  unfold Endp.rTcbA layout.reply.TCB; rfl
theorem rPrevA_eqW (r : U64) : P1.rPrevA r = core.num.U64.wrapping_add r 8#u64 := by
  unfold P1.rPrevA layout.reply.PREV; rfl
theorem rNextA_eqW (r : U64) : P1.rNextA r = core.num.U64.wrapping_add r 16#u64 := by
  unfold P1.rNextA layout.reply.NEXT; rfl

theorem objTypeOf_reply {n : Nat} (h : objTypeOf n = some .replyObject) : n = 6 := by
  unfold objTypeOf at h
  split_ifs at h <;> simp_all

section Calls
open Fl4Spec
variable {m : U64 → U64} {R Rn C : Set U64} {σ : State Unit} {Lst : U64 → List U64}

/-- **The call-stack relation over fresh free replies** with zero links. -/
theorem Sched.CallRel.addR (hC : Sched.CallRel m R C σ Lst)
    (hk : ∀ r ∈ Rn, σ.kheap r.bv = some (.reply defaultReply))
    (hm : ∀ r ∈ Rn, m (P1.rNextA r) = 0#u64 ∧ m (P1.rPrevA r) = 0#u64) (hd : ∀ r ∈ Rn, r ∉ R) :
    Sched.CallRel m (R ∪ Rn) C σ Lst := by
  refine ⟨fun sc hsc => ?_, hC.excl, fun r hr => ?_, fun d hd' hdet => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hC.stack sc hsc
    exact ⟨h1, fun r hr => Or.inl (h2 r hr), h3, h4⟩
  · rcases hr with hr | hr
    · exact hC.reply r hr
    · refine ⟨_, hk r hr, fun p => ⟨fun h => by simp [defaultReply] at h, ?_⟩⟩
      rintro ⟨sc, hsc, -, hh⟩
      exfalso
      obtain ⟨-, h2, -, -⟩ := hC.stack sc hsc
      exact hd r hr (h2 r (List.mem_of_mem_head? hh))
  · rcases hd' with hd' | hd'
    · obtain ⟨h1, h2, h3⟩ := hC.det d hd' hdet
      exact ⟨h1, fun h => let ⟨a, b, c⟩ := h2 h; ⟨Or.inl a, b, c⟩, fun h => let ⟨a, b, c⟩ := h3 h; ⟨Or.inl a, b, c⟩⟩
    · obtain ⟨e1, e2⟩ := hm d hd'
      rw [e1, e2]
      exact ⟨by decide, fun h => absurd rfl h, fun h => absurd rfl h⟩

/-- **`RFree` over fresh free replies** with zero links. -/
theorem Sched.RFree.addR (hF : Sched.RFree m R C σ Lst) (hC : Sched.CallRel m R C σ Lst)
    (hm : ∀ r ∈ Rn, m (P1.rNextA r) = 0#u64 ∧ m (P1.rPrevA r) = 0#u64) (hd : ∀ r ∈ Rn, r ∉ R) :
    Sched.RFree m (R ∪ Rn) C σ Lst := by
  intro d hd' hf
  rcases hd' with hd' | hd'
  · exact hF d hd' hf
  · refine ⟨fun sc hsc hm' => ?_, (hm d hd').1, (hm d hd').2⟩
    obtain ⟨-, h2, -, -⟩ := hC.stack sc hsc
    exact hd d hd' (h2 d hm')

/-- **`RRecv` over fresh replies** with zero links. -/
theorem Sched.RRecv.addR (hR : Sched.RRecv m R σ)
    (hm : ∀ r ∈ Rn, m (P1.rNextA r) = 0#u64 ∧ m (P1.rPrevA r) = 0#u64) : Sched.RRecv m (R ∪ Rn) σ := by
  intro d hd' hb
  rcases hd' with hd' | hd'
  · exact hR d hd' hb
  · exact hm d hd'

end Calls

section Add
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64} {σ : Fl4Spec.State Unit}

/-- An `OObj` word of the sets with `R ∪ Wn` is one of the old sets' or in
a new reply. -/
theorem oobj_unionR {s : S} {Wn : Set U64} {b : U64} (h : OObj st N T C E (R ∪ Wn) B c s σ b) :
    OObj st N T C E R B c s σ b ∨ ∃ r ∈ Wn, r.val ≤ b.val ∧ b.val < r.val + 32 := by
  unfold OObj at h
  rcases h with h | h | h | h | ⟨r, hr, h1, h2⟩ | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr (Or.inl h))
  · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · rcases hr with hr | hr
    · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, h1, h2⟩)))))
    · exact Or.inr ⟨r, hr, h1, h2⟩
  · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))

set_option maxHeartbeats 1000000 in
/-- **`XTopAt` with fresh replies added to `R`** (as `XTopAt.addE`): the
new replies free in the spec, their TCB word zero, aligned, apart from the
TCBs and the kernel-state block, and their words in no object of the
relation (`OObj`) and none the VSpace and CSpace code write (`VObj`). -/
theorem XTopAt.addR {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A}
    (hX : XTopAt (L := L) AR Z s a σ) {Wn : Set U64}
    (hkr : ∀ r ∈ Wn, σ.kheap r.bv = some (.reply Fl4Spec.defaultReply))
    (hmr : ∀ r ∈ Wn, L.mem s (Endp.rTcbA r) = 0#u64)
    (hal : ∀ r ∈ Wn, r.val % 32 = 0 ∧ r.val ≠ 0 ∧ r.val + 32 ≤ 2 ^ 64)
    (hT : ∀ r ∈ Wn, ∀ t ∈ Z.T, t.val + 4096 ≤ r.val ∨ r.val + 32 ≤ t.val)
    (hks : ∀ r ∈ Wn, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ r.val)
    (hfr : ∀ r ∈ Wn, ∀ b : U64, r.val ≤ b.val → b.val < r.val + 32 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b ∧ ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) b) :
    XTopAt (L := L) AR { Z with R := Z.R ∪ Wn } s a σ := by
  obtain ⟨⟨⟨⟨hSch, hEp, hNt, hIrq, hIo, hKr, hAr⟩, hP⟩, hV, hPt, hPI, hCO⟩, ⟨hPl, hCR, hFI, hD, hMO, hIA, hSA⟩,
    -, hE⟩ := hX
  have hO : ∀ r ∈ Wn, ∀ b : U64, r.val ≤ b.val → b.val < r.val + 32 →
      ¬ OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b := fun r hr b h1 h2 => (hfr r hr b h1 h2).1
  have hEp' : Endp.EpStateRel Z.T Z.E (Z.R ∪ Wn) Z.B (L.mem s) σ := by
    have h := Sched.EpStateRel.add (W := ∅) (En := ∅) (Rn := Wn) hEp (fun e h => h.elim) hkr (fun t h => h.elim)
      (fun e h => h.elim) hmr (fun t h => h.elim)
    simpa only [Set.union_empty] using h
  have hEP := hP.ep
  have hEP' : Endp.EPlaced Z.T Z.E (Z.R ∪ Wn) Z.B := by
    refine ⟨hEP.tcb, hEP.ep, fun r hr => ?_, hEP.et, fun r hr t ht => ?_, fun e he r hr => ?_, hEP.balign, hEP.bt,
      hEP.be, fun wp hw r hr => ?_, hEP.binj⟩
    · rcases hr with hr | hr
      · exact hEP.rep r hr
      · exact hal r hr
    · rcases hr with hr | hr
      · exact hEP.rt r hr t ht
      · exact hT r hr t ht
    · rcases hr with hr | hr
      · exact hEP.er e he r hr
      · have := range_apart (k := 16) (w := 32) (by omega) (by omega) (OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ)
          (fun b h1 h2 => Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, h1, h2⟩)))) (hO r hr)
        omega
    · rcases hr with hr | hr
      · exact hEP.br wp hw r hr
      · have := range_apart (k := 8) (w := 32) (by omega) (by omega) (OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ)
          (fun b h1 h2 => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, h1, h2⟩)))))))
          (hO r hr)
        omega
  have hfoot : ∀ b : U64, Endp.EFoot Z.T Z.E (Z.R ∪ Wn) Z.B b →
      Endp.EFoot Z.T Z.E Z.R Z.B b ∨ ∃ r ∈ Wn, r.val ≤ b.val ∧ b.val < r.val + 32 := by
    rintro b (h | ⟨r, hr, h⟩ | h)
    · exact Or.inl (Or.inl h)
    · rcases hr with hr | hr
      · exact Or.inl (Or.inr (Or.inl ⟨r, hr, h⟩))
      · exact Or.inr ⟨r, hr, by omega, by omega⟩
    · exact Or.inl (Or.inr (Or.inr h))
  have hwrite : ∀ b : U64, Endp.EWrite Z.T Z.E (Z.R ∪ Wn) Z.B b →
      Endp.EWrite Z.T Z.E Z.R Z.B b ∨ ∃ r ∈ Wn, b.val = r.val := by
    rintro b (h | ⟨r, hr, h⟩ | h)
    · exact Or.inl (Or.inl h)
    · rcases hr with hr | hr
      · exact Or.inl (Or.inr (Or.inl ⟨r, hr, h⟩))
      · exact Or.inr ⟨r, hr, h⟩
    · exact Or.inl (Or.inr (Or.inr h))
  have hnodeE : ∀ b : U64, L.nodeBase s Z.c ≤ b.val → b.val < L.nodeBase s Z.c + 4288 →
      ¬ Endp.EFoot Z.T Z.E (Z.R ∪ Wn) Z.B b := by
    intro b h1 h2 hf
    rcases hfoot b hf with hf | ⟨r, hr, g1, g2⟩
    · exact hP.nodeE b h1 h2 hf
    · exact hO r hr b g1 g2 (Or.inl ⟨h1, h2⟩)
  have hP' : TopPlaced st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E (Z.R ∪ Wn) Z.B Z.c s σ := by
    refine { hP with ep := hEP', disj := fun b hb => ?_, nodeE := hnodeE }
    rcases oobj_unionR hb with hb | ⟨r, hr, g1, g2⟩
    · exact hP.disj b hb
    · exact (hfr r hr b g1 g2).2
  have hIA' : IpcApart Z.th Z.N Z.T Z.E (Z.R ∪ Wn) Z.B (L.ksb s) Z.c := by
    have hiw : ∀ b, IWords Z.N Z.T Z.E (Z.R ∪ Wn) Z.B b →
        IWords Z.N Z.T Z.E Z.R Z.B b ∨ ∃ r ∈ Wn, r.val ≤ b.val ∧ b.val < r.val + 32 := by
      rintro b (h | h | ⟨r, hr, h1, h2⟩ | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases hr with hr | hr
        · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨r, hr, h1, h2⟩)))
        · exact Or.inr ⟨r, hr, h1, h2⟩
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
    refine { hIA with slot := fun b hb x hx hin => ?_, dom := fun b hb => ?_ }
    · rcases hiw b hb with hb | ⟨r, hr, g1, g2⟩
      · exact hIA.slot b hb x hx hin
      · exact (hfr r hr b g1 g2).2 (Vs.vobj_of_slot hPl _ _ _ _ _ _ hx hin.1 hin.2)
    · rcases hiw b hb with hb | ⟨r, hr, g1, g2⟩
      · exact hIA.dom b hb
      · have := hks r hr; omega
  obtain ⟨Q, R0, hc, -⟩ := hSch.lists
  have hE' : EpSchedApart st Z.T Z.C Z.E (Z.R ∪ Wn) Z.B Z.c s σ := by
    refine ⟨hnodeE, fun hw => ?_, fun hw => ?_, fun sc hsc x n hx b hb hw => ?_⟩
    · rcases hwrite _ hw with hw | ⟨r, hr, h⟩
      · exact hE.dom hw
      · rw [Sched.curDomA_val hc.node] at h; have := hks r hr; omega
    · rcases hwrite _ hw with hw | ⟨r, hr, h⟩
      · exact hE.dt hw
      · rw [Sched.dtA_val hc.node] at h; have := hks r hr; omega
    · rcases hwrite _ hw with hw | ⟨r, hr, h⟩
      · exact hE.sc sc hsc x n hx b hb hw
      · exact hO r hr b (by omega) (by omega)
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hx, hb⟩)))))))
  exact ⟨⟨⟨⟨hSch, hEp', hNt, hIrq, hIo, hKr, hAr⟩, hP'⟩, hV, hPt, hPI, hCO⟩,
    ⟨hPl, hCR, hFI, hD, hMO, hIA', hSA⟩, IpcRel.of hNt hEp' (sched_sc hSch), hE'⟩

end Add

end

end Fl4Proofs.P3
