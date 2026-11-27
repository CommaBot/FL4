/-
P3 (p3J gen 23): **the sharper kernel-word footprint already exists (P2's `KWN`), and it lies inside `ProjW`.**

Gen 22 planned a scripted copy of P1's footprint chain with a `KW` that excludes every core's node offsets 8 / 32
(`IDLE_THREAD` / `IDLE_SC`). Two findings change that plan (handoff gen 23):

1. **P2 has built it.** P2/FootN's **`KWN st Kp Nd …`** is `KW` minus the node identity words `IdW` (every core's
   `IDLE_THREAD` (8) and `IDLE_SC` (32), other cores' `CUR_THREAD` / `SCHED_ACTION` / `CUR_SC`, and the
   protected words `PrW`), with its footprint `FootN` and the `.kwN` / `FootN`-versions of the queue, schedule,
   budget, timer and stall paths (P2/FootN … FootN11, `SFootN`, `FFoot`). A second copy of P1's chain is not needed.
2. **P1's entry composites cannot be the source of the entry footprints.** `entryXG` / `kernel_entry.entryXG` ask
   `EntryHyps0` / `XferHyps`, which P1/EntryVacuous refutes at every entry state (`blkU`, `irqcap`,
   `XferHyps.buf_false`: the last is exactly the IPC-buffer frame-cap case of gen 22). So `…FootW` cannot be "P1's
   `entryXG` instantiated at `JAtZ`"; the footprint must be composed along P3's own joint chain (which carries the
   cap typing), from the per-operation footprints (P1 `Foot`, P2 `FootN`, P3 `KFoot` / `SFoot` / `KFootN`).

What this module proves is the end glue that any such composition needs: every word of
`KWN ∨ DbgW ∨ CapW` (over P1's sets of `H` at a `JAtZ` state, as `JAtZ.blk`: `T = H.tcbs`, `Sg = H.frame`,
`Ω = H.omega`, `Scs = H.scs`, `Z = H.scBits`, `Es = EH H`) is a `ProjW H Cs s` word (**`cur0wN_projW`**), and the
same for the transfer footprint at `U = ∅` (P3JMcFootC's `xferW_empty_projW`). So a `WritesIn` footprint of an
entry into `KWN ∨ DbgW ∨ CapW ∨ XferW … ∅` gives the `…FootWC` premise. Pieces: `obj_projW` (a word of an `H`
object), `node_projW` (a node word of a core of `Cs` at an offset `≠ 8, 32`), `kwN_projW`, `dbgW_projW`,
`capW_projW`.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMcFootC
import Fl4Proofs.P2.FootN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {H : P1.Heap} {Cs : Set U64} {s : S}

/-- A word at offset `K` of an `H` object is a `ProjW` word. -/
theorem obj_projW (hH : P1.HeapOK H) {p K : U64} {k : P1.HKind} (hp : H p = some k) (hK : K.val < 2 ^ k.bits) :
    ProjW (L := L) H Cs s (core.num.U64.wrapping_add p K) := by
  have hfit := hH.fits p _ hp
  have hv := wa_v (a := p) (b := K) (by omega)
  exact Or.inl ⟨p, k, hp, by rw [hv]; omega, by rw [hv]; omega⟩

/-- A node word of a core of `Cs`, at an offset other than `IDLE_THREAD` / `IDLE_SC`, is a `ProjW` word. -/
theorem node_projW {T : Set U64} {c o : U64} (hNP : NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val ≠ 8) (h32 : o.val ≠ 32) : ProjW (L := L) H Cs s (L.nodeAt s c o) := by
  have hv := nodeAt_val hNP ho
  exact Or.inr (Or.inr ⟨c, hc, by rw [hv]; omega, by rw [hv]; omega, fun _ => ⟨by rw [hv]; omega, by rw [hv]; omega⟩⟩)

/-- **`KWN` over `H`'s sets is inside `ProjW`** (module docstring). -/
theorem kwN_projW (hH : P1.HeapOK H) (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    {Kp : Set U64} {Nd : Prop} {b : U64}
    (hb : KWN st Kp Nd (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) s b) :
    ProjW (L := L) H Cs s b := by
  obtain ⟨hk, hn⟩ := hb
  rcases hk with ⟨y, hy, K, -, hK, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hg | ⟨c, ⟨z, hz⟩, hin⟩ |
    ⟨e, he, rfl | rfl⟩
  · exact obj_projW hH (k := .tcb) hy (by simp only [P1.HKind.bits]; omega)
  · refine node_projW (hNP c hc) hc ho (fun e => hn (Or.inl ⟨c, hc, o, Or.inl e, rfl⟩))
      (fun e => hn (Or.inl ⟨c, hc, o, Or.inr (Or.inl e), rfl⟩))
  · obtain ⟨-, p, k, hp, -, hin⟩ := hg
    exact Or.inl ⟨p, k, hp, hin.1, hin.2⟩
  · have e : P1.Heap.scBits H c = z := by simp only [P1.Heap.scBits, hz]
    rw [e] at hin
    exact Or.inl ⟨c, .sc z, hz, hin.1, hin.2⟩
  · unfold epHeadA
    rcases he with he | he
    · exact obj_projW hH he (by simp [P1.HKind.bits])
    · exact obj_projW hH he (by simp [P1.HKind.bits])
  · unfold epTSA
    rcases he with he | he
    · exact obj_projW hH he (by simp [P1.HKind.bits])
    · exact obj_projW hH he (by simp [P1.HKind.bits])

/-- The debug-list words over `H`'s TCBs and `Cs`'s nodes are `ProjW` words. -/
theorem dbgW_projW (hH : P1.HeapOK H) (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c) {b : U64}
    (hb : DbgW st (P1.Heap.tcbs H) Cs s b) : ProjW (L := L) H Cs s b := by
  rcases hb with ⟨y, hy, rfl | rfl⟩ | ⟨c, hc, rfl⟩
  · unfold dnA; exact obj_projW hH (k := .tcb) hy (by simp [P1.HKind.bits])
  · unfold dpA; exact obj_projW hH (k := .tcb) hy (by simp [P1.HKind.bits])
  · exact node_projW (hNP c hc) hc (by simp) (by simp) (by simp)

/-- The cap-slot words over `H`'s sets are `ProjW` words. -/
theorem capW_projW (hH : P1.HeapOK H) {Sg : Set U64} {b : U64}
    (hb : CapW (P1.Heap.tcbs H) (P1.Heap.omega H) Sg b) : ProjW (L := L) H Cs s b := by
  rcases hb with ⟨y, hy, K, hK, rfl⟩ | ⟨⟨-, p, k, hp, -, hin⟩, -⟩
  · exact obj_projW hH (k := .tcb) hy (by simp only [P1.HKind.bits]; omega)
  · exact Or.inl ⟨p, k, hp, hin.1, hin.2⟩

/-- **`KWN ∨ DbgW ∨ CapW` over `H`'s sets is inside `ProjW`** (module docstring). -/
theorem cur0wN_projW (hH : P1.HeapOK H) (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    {Kp : Set U64} {Nd : Prop} {b : U64}
    (hb : KWN st Kp Nd (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) s b ∨
      DbgW st (P1.Heap.tcbs H) Cs s b ∨ CapW (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) b) :
    ProjW (L := L) H Cs s b := by
  rcases hb with hb | hb | hb
  · exact kwN_projW hH hNP hb
  · exact dbgW_projW hH hNP hb
  · exact capW_projW hH hb

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **At a `JAtZ` state: a `WritesIn` footprint into `KWN ∨ DbgW ∨ CapW` over `H`'s sets is a `ProjW`
footprint** (module docstring). -/
theorem projW_of_cur0wN {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}
    {s s' : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {Kp : Set U64} {Nd : Prop}
    (hW : P1.WritesIn st s s' (fun b =>
      KWN st Kp Nd (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) s b ∨
      DbgW st (P1.Heap.tcbs H) Cs s b ∨ CapW (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) b)) :
    P1.WritesIn st s s' (ProjW (L := L) H Cs s) := by
  obtain ⟨Q, R, hq⟩ := J.blk.1
  exact hW.mono fun b hb => cur0wN_projW J.kern.heap (SchedQueuesInvX.nodes hq) hb

end

end Fl4Proofs.P3.Mc
