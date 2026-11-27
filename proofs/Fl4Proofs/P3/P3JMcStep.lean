/-
P3 (p3J gen 18): **`ForeignIdle` across a step with a projection footprint and stable ghosts** — what replaces
gen 17's `FIKeepIrq` [J] by premises that no longer mention the other cores.

* **`ProjW H Cs s b`** (the projection footprint): `b` inside an object of P1's heap `H`, inside the kernel-state
  block, or inside a node of a core of `Cs` but not another core's `IDLE_THREAD` / `IDLE_SC` word (FL4 writes those
  two words only in `create_idle_thread`, crates/fl4-core/src/boot.rs l.684-704).
* **`FIdleW s c`**: core `c`'s idle TCB 4096-aligned and its SC 128-aligned, both below `2 ^ 64` (FL4's
  `idle_base + c · idle_stride`, the SC at `+ 4096`).
* **`ForeignIdle.step`**: a step writing only `ProjW H Cs s` (P1 `WritesIn`), to ghosts with the same `H`, typed
  heap, TCB and SC sets, no new spec object where there was none (`KhNoneKeep`) and no new RAM untyped cap in the MDB
  (`UtKeep`), keeps `ForeignIdle ∧ FIdleW` of every core `c ∈ Cs`, `c ≠ cpu`. Proof: the five shape words and the
  node's two `IDLE_*` words are aligned and outside `ProjW` (apartness from `H`, the block and the nodes; another
  node's `IDLE_*` excluded by `ProjW` itself, other nodes disjoint), so `WritesIn` keeps them; everything else is
  ghost-level.
* **`JAtMcW`** (`JAtMc` with `FIdleW`), **`JAtMcW.jAtMc`**, **`jAtMcW_step`**: from `JAtMcW`'s ghosts and an outcome
  `JAtZ (Z.mv G' V') H Cs …` (U45nv's ghost shape: only the MDB and VSpace sets move), with the footprint and the two
  carry facts, `JAtMcW` at the outcome.

No sorry; no premises beyond the stated hypotheses. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The projection footprint** (module docstring). -/
def ProjW (H : P1.Heap) (Cs : Set U64) (s : S) (b : U64) : Prop :=
  (∃ p k, H p = some k ∧ p.val ≤ b.val ∧ b.val < p.val + 2 ^ k.bits) ∨
  ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568) ∨
  (∃ c ∈ Cs, L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288 ∧
    (c ≠ L.cpu s → b.val ≠ L.nodeBase s c + 8 ∧ b.val ≠ L.nodeBase s c + 32))

/-- **Core `c`'s idle objects aligned and fitting** (module docstring). -/
structure FIdleW (s : S) (c : U64) : Prop where
  tal : (idleOf (L := L) s c).val % 4096 = 0
  sal : (idleScOf (L := L) s c).val % 128 = 0
  tfit : (idleOf (L := L) s c).val + 4096 ≤ 2 ^ 64
  sfit : (idleScOf (L := L) s c).val + 128 ≤ 2 ^ 64

/-- No new spec object where there was none. -/
def KhNoneKeep (σ σ' : Fl4Spec.State Unit) : Prop := ∀ p, σ.kheap p = none → σ'.kheap p = none

/-- No new RAM untyped cap in the MDB: every one after was one before, at the same slot. -/
def UtKeep (G G' : MdbGhost) (s s' : S) : Prop :=
  ∀ x ∈ G'.chains.flatten, ∀ p sb fi, capV (L.mem s') x = .Untyped p sb fi false →
    x ∈ G.chains.flatten ∧ capV (L.mem s) x = .Untyped p sb fi false

variable {H : P1.Heap} {Cs : Set U64} {s s' : S}

theorem wa_v {a b : U64} (h : a.val + b.val < 2 ^ 64) : (core.num.U64.wrapping_add a b).val = a.val + b.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- A range apart from `H`'s objects, the block and every node holds no `ProjW` word. -/
theorem not_projW {lo n : Nat} {b : U64} (hb : lo ≤ b.val ∧ b.val < lo + n)
    (hH : ∀ p k, H p = some k → Apart p.val (2 ^ k.bits) lo n)
    (hK : Apart lo n (L.ksb s).val 13568)
    (hN : ∀ c ∈ Cs, Apart lo n (L.nodeBase s c) 4288) : ¬ ProjW (L := L) H Cs s b := by
  rintro (⟨p, k, hp, h1, h2⟩ | ⟨h1, h2⟩ | ⟨c, hc, h1, h2, -⟩)
  · have := hH p k hp; unfold Apart at this; omega
  · unfold Apart at hK; omega
  · have := hN c hc; unfold Apart at this; omega

/-- A word at offset `K` of an object at `x` kept by a `ProjW` step, when the object's range is apart. -/
theorem keep_off {x K : U64} {n : Nat} (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s))
    (hK : K.val < n) (hal : (x.val + K.val) % 8 = 0) (hfit : x.val + n ≤ 2 ^ 64)
    (hH : ∀ p k, H p = some k → Apart p.val (2 ^ k.bits) x.val n)
    (hB : Apart x.val n (L.ksb s).val 13568)
    (hN : ∀ c ∈ Cs, Apart x.val n (L.nodeBase s c) 4288) :
    L.mem s' (core.num.U64.wrapping_add x K) = L.mem s (core.num.U64.wrapping_add x K) := by
  have hv := wa_v (a := x) (b := K) (by omega)
  refine hW.2.2 _ (by show _ % 8 = 0; rw [hv]; exact hal) (not_projW ?_ hH hB hN)
  rw [hv]; omega

/-- Another core's node word at offset `o ∈ {8, 32}` (its `IDLE_THREAD` / `IDLE_SC`) is kept by a `ProjW` step. -/
theorem keep_idleWord {T : Set U64} {c o : U64} (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s))
    (hc : c ∈ Cs) (hne : c ≠ L.cpu s) (hNP : NodePlaced st T s c) (ho : o.val = 8 ∨ o.val = 32)
    (hnd : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val) :
    L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := by
  rw [nodeAt_of_ksb hW.1]
  have hv := nodeAt_val hNP (off := o) (by omega)
  have hal := hNP.align
  refine hW.2.2 _ (by show _ % 8 = 0; rw [hv]; omega) ?_
  rintro (⟨p, k, hp, h1, h2⟩ | ⟨h1, h2⟩ | ⟨c', hc', h1, h2, h3⟩)
  · have := hnd p k hp; rw [hv] at h1 h2; omega
  · rw [hv] at h1 h2; unfold LawfulStore.nodeBase at h1 h2; omega
  · rw [hv] at h1 h2 h3
    by_cases e : c' = c
    · subst e; have := h3 hne; omega
    · have hcv : c'.val ≠ c.val := fun h => e (UScalar.eq_of_val_eq h)
      unfold LawfulStore.nodeBase at h1 h2; omega

theorem nodeBase_of_ksb (h : L.ksb s' = L.ksb s) (c : U64) : L.nodeBase s' c = L.nodeBase s c := by
  unfold LawfulStore.nodeBase; rw [h]

/-- **`ForeignIdle ∧ FIdleW` across a `ProjW` step to stable ghosts** (module docstring). -/
theorem ForeignIdle.step {T : Set U64} {Z Z' : XSets} {σ σ' : Fl4Spec.State Unit} {c : U64}
    (hth : Z'.th = Z.th) (hT : Z'.T = Z.T) (hC : Z'.C = Z.C)
    (F : ForeignIdle (L := L) Z H Cs s σ c) (FW : FIdleW (L := L) s c) (hc : c ∈ Cs) (hne : c ≠ L.cpu s)
    (hNP : NodePlaced st T s c)
    (hnd : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val)
    (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s)) (hK : KhNoneKeep σ σ') (hU : UtKeep (L := L) Z.G Z'.G s s') :
    ForeignIdle (L := L) Z' H Cs s' σ' c ∧ FIdleW (L := L) s' c := by
  have e1 : idleOf (L := L) s' c = idleOf (L := L) s c :=
    keep_idleWord (o := layout.node.IDLE_THREAD) hW hc hne hNP (Or.inl (by unfold layout.node.IDLE_THREAD; rfl)) hnd
  have e2 : idleScOf (L := L) s' c = idleScOf (L := L) s c :=
    keep_idleWord (o := layout.node.IDLE_SC) hW hc hne hNP (Or.inr (by unfold layout.node.IDLE_SC; rfl)) hnd
  have hks := hW.1
  have kt : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (idleOf (L := L) s c) K) =
        L.mem s (core.num.U64.wrapping_add (idleOf (L := L) s c) K) := fun K hK h8 =>
    keep_off hW hK (by have := FW.tal; omega) FW.tfit F.tH F.tKs F.tN
  have ks : ∀ K : U64, K.val < 128 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (idleScOf (L := L) s c) K) =
        L.mem s (core.num.U64.wrapping_add (idleScOf (L := L) s c) K) := fun K hK h8 =>
    keep_off hW hK (by have := FW.sal; omega) FW.sfit F.sH F.sKs F.sN
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have h := F.tSt; rw [e1]; unfold P1.stA layout.tcb.STATE layout.tcb.F at h ⊢
    rw [kt _ (by decide) (by decide)]; exact h
  · have h := F.tAff; rw [e1]; unfold affA at h ⊢; rw [kt _ (by decide) (by decide)]; exact h
  · have h := F.tSc; rw [e1, e2]; unfold scA at h ⊢; rw [kt _ (by decide) (by decide)]; exact h
  · have h := F.sTcb; rw [e1, e2]; unfold scTcbA layout.sc.TCB at h ⊢; rw [ks _ (by decide) (by decide)]; exact h
  · have h := F.sCore; rw [e2]; unfold scCoreA layout.sc.CORE at h ⊢; rw [ks _ (by decide) (by decide)]; exact h
  · rw [e1]; exact F.tH
  · rw [e2]; exact F.sH
  · rw [e1, hth]; exact F.tTh
  · rw [e2, hth]; exact F.sTh
  · rw [e1, hT]; exact F.tT
  · rw [e2, hC]; exact F.sC
  · rw [e1]; exact hK _ F.tK
  · rw [e2]; exact hK _ F.sK
  · rw [e1, hks]; exact F.tKs
  · rw [e2, hks]; exact F.sKs
  · intro c' hc'; rw [e1, nodeBase_of_ksb hks]; exact F.tN c' hc'
  · intro c' hc'; rw [e2, nodeBase_of_ksb hks]; exact F.sN c' hc'
  · intro x hx p sb fi hcap
    obtain ⟨hx0, hc0⟩ := hU x hx p sb fi hcap
    rw [e1, e2]; exact F.ut x hx0 p sb fi hc0
  · exact ⟨by rw [e1]; exact FW.tal, by rw [e2]; exact FW.sal, by rw [e1]; exact FW.tfit, by rw [e2]; exact FW.sfit⟩

/-- **`JAtMc` with aligned, fitting foreign idle objects.** -/
def JAtMcW (AR : A → Fl4Spec.Cr3 → Prop) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
    JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VxE Z ∧
      ∀ c ∈ Cs, c ≠ L.cpu s → ForeignIdle (L := L) Z H Cs s σ c ∧ FIdleW (L := L) s c

variable {arI} {AR : A → Fl4Spec.Cr3 → Prop}

theorem JAtMcW.jAtMc {a : A} {σ : Fl4Spec.State Unit} (h : JAtMcW (L := L) arI AR s a σ) :
    JAtMc (L := L) arI AR s a σ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hV, hF⟩ := h
  exact ⟨Z, H, Cs, Ac, Lst, D, J, hV, fun c hc hne => (hF c hc hne).1⟩

/-- **One core: `JAtZ` gives `JAtMcW`.** -/
theorem jAtMcW_of_one {Z : XSets} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {a : A}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hV : VxE Z)
    (h1 : ∀ c ∈ Cs, c = L.cpu s) : JAtMcW (L := L) arI AR s a σ :=
  ⟨Z, H, Cs, Ac, Lst, D, J, hV, fun c hc hne => absurd (h1 c hc) hne⟩

/-- **`JAtMcW` across a step with the projection footprint and U45nv's ghost shape** (module docstring). -/
theorem jAtMcW_step {Z : XSets} {Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {a a' : A}
    {σ σ' : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hF : ∀ c ∈ Cs, c ≠ L.cpu s → ForeignIdle (L := L) Z H Cs s σ c ∧ FIdleW (L := L) s c)
    {G' : MdbGhost} {V' : Set U64 × Set U64 × Set U64 × Set U64 × Set U64} {Ac' : Set U64}
    {Lst' : U64 → List U64} {D' : Set U64}
    (J' : JAtZ (L := L) arI AR (Z.mv G' V') H Cs Ac' Lst' D' s' a' σ') (hV' : VxE (Z.mv G' V'))
    (hW : P1.WritesIn st s s' (ProjW (L := L) H Cs s)) (hK : KhNoneKeep σ σ') (hU : UtKeep (L := L) Z.G G' s s') :
    JAtMcW (L := L) arI AR s' a' σ' := by
  refine ⟨Z.mv G' V', H, Cs, Ac', Lst', D', J', hV', fun c hc hne => ?_⟩
  have hne0 : c ≠ L.cpu s := by rw [← hW.2.1]; exact hne
  obtain ⟨F, FW⟩ := hF c hc hne0
  obtain ⟨Q, R, hq⟩ := J.blk.1
  exact ForeignIdle.step (Z := Z) (Z' := Z.mv G' V') rfl rfl rfl F FW hc hne0 (SchedQueuesInvX.nodes hq c hc) (fun p k hp => J.kern.hnd p k hp c hc) hW hK hU

end

end Fl4Proofs.P3.Mc
