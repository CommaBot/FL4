/-
P1: the debug-list head of every core's node (`DEBUG_TCBS`, node offset 88)
lies outside the kernel-word footprint `KW` and the object words `Ω`
(`node88_out`); so a step whose writes stay within `KW ∪ Ω` keeps it
(`KO.node88`).  The SchedContext decodes write only such words
(`schedcontext.decode.dec`'s frame), so they keep every core's debug head
(`schedcontext.decode.node88`).
-/
import Fl4Proofs.P1.QueueYield
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **No core's debug head is a `KW` or `Ω` word.** -/
theorem node88_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    {c : U64} (hc : c ∈ Cs) : ¬ KO st T Cs Ω H Sg Scs Z s (L.nodeAt s c layout.node.DEBUG_TCBS) := by
  have hN := h.nodes c hc
  have h88 : layout.node.DEBUG_TCBS.val < 4288 := by rw [debug_val]; omega
  have hal : Aligned (L.nodeAt s c layout.node.DEBUG_TCBS) :=
    nodeAt_aligned hN h88 (by rw [debug_val])
  have outΩ : L.nodeAt s c layout.node.DEBUG_TCBS ∉ Ω := fun hm =>
    out_ne_node (h.omega _ hm) hc hN h88 rfl
  rintro ((⟨y, hy, K, h1, h2, -, -, e⟩ | ⟨c', hc', o, ho, ho88, e⟩ | hm | ⟨c', hc', hin⟩ | ⟨e', he', hb⟩) | hm)
  · exact node_ne_field hN h88 hy (h.tcbs y hy) h2 e
  · by_cases ec : c' = c
    · subst ec
      exact nodeAt_ne hN h88 ho (by rw [debug_val]; omega) e
    · exact nodeAt_ne_cpu hN (h.nodes c' hc') h88 ho (Ne.symm ec) e
  · exact outΩ (hsub _ hm)
  · exact outΩ (hO.scW c' hc' _ hal hin)
  · obtain ⟨E, EQ, hEW⟩ := h.eps
    have heE : e' ∈ E := (hEW.2.2.2.2.2.2.2.1 e').2 he'
    obtain ⟨hE, hEN, -⟩ := hEW.1 e' heE
    have hv : (L.nodeAt s c layout.node.DEBUG_TCBS).val = e'.val ∨
        (L.nodeAt s c layout.node.DEBUG_TCBS).val = e'.val + 8 := by
      rcases hb with hb | hb
      · exact Or.inl (by rw [hb, epHeadA_val])
      · exact Or.inr (by rw [hb, epTSA_val hE])
    rw [nodeAt_val hN h88, debug_val] at hv
    have := hEN.1 c hc
    omega
  · exact outΩ hm

/-- **A `KO` frame keeps every core's debug head.** -/
theorem KO.node88 {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (w : WritesIn st s s' (KO st T Cs Ω H Sg Scs Z s)) {c : U64} (hc : c ∈ Cs) :
    L.mem s' (L.nodeAt s c layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) :=
  w.mem_eq (nodeAt_aligned (h.nodes c hc) (by rw [debug_val]; omega) (by rw [debug_val]))
    (node88_out h hO hsub hc)

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- **The SchedContext decodes keep every core's debug-list head**
(`DEBUG_TCBS`): they write only `KO` words (`schedcontext.decode.dec`). -/
theorem schedcontext.decode.node88 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U)
    (s : S) (a : A) (lbl sc : U64) (call : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (b : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.SchedContext sc b) extra) :
    schedcontext.decode st ar s a lbl sc call extra ⦃ r s' _ => ∀ c ∈ Cs,
      L.mem s' (L.nodeAt s c layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) ⦄ := by
  have hb := D.bxi
  refine WP.spec_mono (schedcontext.decode.dec hA E (scYieldGap_holds hA U) s a lbl sc call extra b D) ?_
  rintro ⟨r, s', a'⟩ ⟨-, w⟩
  exact fun c hc => KO.node88 hb.1.choose_spec.choose_spec hb.2.2.1.1 hb.2.2.2.1.sub w hc

/-- **`decode_invocation` on a SchedContext cap keeps every core's
debug-list head.** -/
theorem syscall.decode_invocation.sc_node88 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U) (s : S) (a : A) (lbl len : U64) (slot : obj.Slot) (sc b : U64)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.SchedContext sc b) extra) :
    syscall.decode_invocation st ar s a lbl len slot (.SchedContext sc b) blk call don fp buf extra ⦃ r s' _ =>
      ∀ c ∈ Cs, L.mem s' (L.nodeAt s c layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s c layout.node.DEBUG_TCBS) ⦄ := by
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 fun _ _ => rfl
  · exact schedcontext.decode.node88 hA E s a lbl sc call extra b D

end

end Fl4Proofs.P1
