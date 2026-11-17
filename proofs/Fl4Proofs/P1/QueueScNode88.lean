/-
P1: the debug-list head of every core's node (`DEBUG_TCBS`, node offset 88)
lies outside the kernel-word footprint `KW` and the object words `Ω`
(`node88_out`); so a step whose writes stay within `KW ∪ Ω` keeps it
(`KO.node88`).  The SchedContext decodes do not keep the debug heads in
general: binding a thread to an SC of another core moves the thread between
the cores' debug lists (`smp.migrate_tcb`), so `schedcontext.decode.dec`'s
frame is `KOD` (`KO` and the debug-list words).
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


end Fl4Proofs.P1
