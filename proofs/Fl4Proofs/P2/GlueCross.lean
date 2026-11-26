/-
# P2 (line glue, gen 4): the **cross-core chain view is false**, and what that says of the start [P]

Gen 3 stopped on one missing fact, the *cross-core view* of the epoch's chain `Ch`:

  for `σ ∈ Ch` and a core `c` of the layout, some `σ' ∈ Ch` with `L.cpu σ' = c`, the same memory as `σ` on the
  aligned non-user words, and `c`'s Arch state (`CrossCoreView` below, without the Arch clause).

This module shows it is **false** as soon as the layout has two cores, at every chain state, and proves why from
P3's own invariant. No premise is introduced; nothing here is tagged.

## The counterexample (proved: `slJAt_aff`, `chain_cpu_eq`, `crossCoreView_false`)

P3's joint invariant is a single-core refinement parameterised by the current core, and it pins the core into
memory that every core shares:

* `JAtZ.xtop.fin…` contains `Sched.SchedRel … Z.c s σ`, whose `SchedCore` has `cur : L.cpu s = Z.c` and
  `aff : ∀ t ∈ Z.T, L.mem s (affA t) = Z.c` — **every TCB of `Z.T` has its `AFFINITY` word equal to the current
  core**;
* `JAtZ.tcbs_eq`: `Z.T = H.tcbs`, the TCBs of the typed heap `H`; `SlJAtZ.j` puts the layout's heap `K.heap` in
  `H`'s place, and `ChainLay.bun` (clause 7 of `loc_chain_all`, proved) gives `SlJAt K σ` at every `σ ∈ Ch`;
* the `AFFINITY` word `t + 3520` is aligned and lies inside the TCB's 4 KiB frame, which the IPC-buffer words
  (`K.user`, `SlJAtZ.user`) miss (`EPlaced.bt`).

So at every chain state `σ`, `L.mem σ (fld t oAFFINITY) = L.cpu σ` for **every** TCB `t` of `K.heap`, on a word
the cross-core view asks to be kept (`slJAt_aff`). The heap has a TCB (the current thread, `JKern.curH`). Two
chain states agreeing on aligned non-user words therefore have the same `cpu` (`chain_cpu_eq`), and the view is
refuted for any layout with `2 ≤ K.ncores` (`crossCoreView_false`). The Arch clause does not matter.

Concretely, at any reachable state with two cores: core `d` exits serially, `Ch` is chosen at that exit, every
TCB's `AFFINITY` word is `d` in its memory; a state of core `c ≠ d` in `Ch` needs every one of those words to be
`c`. No narrower *memory-equality* form survives: whatever set of words the view keeps, it may not contain a single
`AFFINITY` word of a TCB of the heap.

## Consequence for the start [P] of U2 / U4 / U5 (proved: `veq_aff`, `start_aff`, `start_two_cores`)

The same fact bites the existing start premise, which asks a `Ch` state of the **starting** core:

* `AFFINITY` words are gate-owned under `ownP` (`E2EP.ownP_aff_gate`), and `PO c hs .gate` holds, so `VEq`'s
  second clause makes every view-equal `ρ` agree with the physical memory there (`veq_aff`).
* Hence U5's start fact for core `c` (`∃ ρ, VEq … c hs ρ s.mem ∧` a `GlueAt` state `σ' ∈ Ch` of core `c` equal to
  `ρ` off user words) forces **every TCB of the layout to have `AFFINITY = c` in the physical memory**
  (`start_aff`). U2 (`ρ := s.mem`) and U4 (`ρ := H`) are instances.
* Two such starts by cores `c₁, c₂` in one epoch (same `K`, `Ch`) at physical memories that agree on the TCBs'
  `AFFINITY` words force `c₁ = c₂` (`start_two_cores`). `AFFINITY` words are gate words (`ownP_aff_gate`), so local
  paths do not write them; within an epoch they change only by the hardware steps' writes, which do not target
  kernel words.

So the start [P] of U2, U4 and U5 is satisfiable only on executions where, between two serial exits, every local
start is by one core whose number is every TCB's affinity: on a real SMP execution with threads homed on two cores
it is false at the first local start. The root cause is P3's scope (`SchedCore.aff`: the refinement covers states
in which every thread is homed on the current core), not the glue. This is a [J]-side gap: closing it needs P3's
joint invariant generalised to per-core scheduler relations (`aff` relaxed to the threads of `Z.c`'s queues, other
cores' threads related by their own core's relation), after which the chain could be indexed per core and the
cross-core view restated per core. That is P3 work, out of the glue's scope.

## What was not done (and why)

Task step 2 (`serializable_fl4_localU6`, `start`'s chain content replaced via `frame_acc` + `loc_chain_all` +
`veq_revert` + a `SerExitW` memory clause) is **not built**: it would rest on `CrossCoreView`, which is refuted
here for every multi-core layout. No `SerExitW` memory clause is added. Premise diff vs U5: none.

No premise, no `sorry`; no existing statement changed.
-/
import Fl4Proofs.P2.GlueFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.GlueCross
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMap (KLayout fld oAFFINITY oAFF_val)
open Fl4Proofs.P2.OwnMapP (KLayoutP RegionOKP ownP)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **At a bundle state every TCB of the layout's heap is homed on the current core** (module docstring): its
`AFFINITY` word is aligned, not a user word, and equals `L.cpu s` (P3's `SchedCore.aff` with `JAtZ.tcbs_eq`). -/
theorem slJAt_aff {K : KLayout} {s : S} (h : SlJAt (L := L) K s) {t : U64} (ht : K.heap t = some .tcb) :
    P1.Aligned (fld t oAFFINITY) ∧ fld t oAFFINITY ∉ K.user ∧ L.mem s (fld t oAFFINITY) = L.cpu s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have J := B.j
  have hT : t ∈ Zx.T := by rw [J.tcbs_eq.1]; exact ht
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hta : TcbAddr t := hcq.tcbs t hT
  have hv : (fld t oAFFINITY).val = t.val + 3520 := by
    have := Fl4Proofs.P3.Notif.tfield_val (K := oAFFINITY) hta (by rw [oAFF_val]; omega)
    rw [oAFF_val] at this; exact this
  refine ⟨?_, ?_, ?_⟩
  · unfold P1.Aligned; rw [hv]; have := hta.align; omega
  · rw [B.user]
    rintro ⟨wp, hwp, hw⟩
    have hb := J.ip.e.bt wp hwp t hT
    rw [hw, hv] at hb
    omega
  · exact (hcq.aff t hT).trans hcq.cur.symm

/-- The current thread of a bundle state is a TCB of the layout's heap. -/
theorem slJAt_cur {K : KLayout} {s : S} (h : SlJAt (L := L) K s) : K.heap (L.curW s) = some .tcb := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact B.j.kern.curH

/-- **Two bundle states of one layout that agree off user words run on the same core.** -/
theorem slJAt_cpu_eq {K : KLayout} {s s' : S} (h : SlJAt (L := L) K s) (h' : SlJAt (L := L) K s')
    (hm : ∀ x, P1.Aligned x → x ∉ K.user → L.mem s x = L.mem s' x) : L.cpu s = L.cpu s' := by
  have hcur := slJAt_cur h
  obtain ⟨ha, hu, e⟩ := slJAt_aff h hcur
  obtain ⟨-, -, e'⟩ := slJAt_aff h' hcur
  rw [← e, ← e', hm _ ha hu]

/-- **Two chain states agreeing off user words run on the same core** (`ChainLay.bun` + `slJAt_cpu_eq`). -/
theorem chain_cpu_eq {K : KLayout} {Ch : S → Prop} (hC : ChainLay (L := L) K Ch) {σ σ' : S} (h : Ch σ)
    (h' : Ch σ') (hm : ∀ x, P1.Aligned x → x ∉ K.user → L.mem σ x = L.mem σ' x) : L.cpu σ = L.cpu σ' :=
  slJAt_cpu_eq (hC.bun σ h) (hC.bun σ' h') hm

/-- **The cross-core view of a chain** (gen 3's missing fact, without its Arch clause; module docstring). -/
def CrossCoreView (K : KLayout) (Ch : S → Prop) : Prop :=
  ∀ σ, Ch σ → ∀ c : U64, c.val < K.ncores → ∃ σ', Ch σ' ∧ L.cpu σ' = c ∧
    ∀ x, P1.Aligned x → x ∉ K.user → L.mem σ' x = L.mem σ x

/-- **The cross-core view is false** for any nonempty chain of a layout with two cores (module docstring). -/
theorem crossCoreView_false {K : KLayout} {Ch : S → Prop} (hC : ChainLay (L := L) K Ch) {σ : S} (h : Ch σ)
    (hn : 2 ≤ K.ncores) : ¬ CrossCoreView (L := L) K Ch := by
  intro hX
  have h0 : (0#u64).val < K.ncores := by first | (simp <;> omega) | omega
  have h1 : (1#u64).val < K.ncores := by first | (simp <;> omega) | omega
  obtain ⟨σ0, hσ0, c0, m0⟩ := hX σ h 0#u64 h0
  obtain ⟨σ1, hσ1, c1, m1⟩ := hX σ h 1#u64 h1
  have e := chain_cpu_eq hC hσ0 hσ1 fun x ha hu => (m0 x ha hu).trans (m1 x ha hu).symm
  rw [c0, c1] at e
  exact absurd e (by decide)

/-- **A view-equal memory keeps every TCB's `AFFINITY` word** (gate-owned under `ownP`, `PO` of the gate). -/
theorem veq_aff {K : KLayoutP} (hK : RegionOKP K) {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (hV : Serial.VEq (ownP K) cls ko c hs ρ μ) {t : U64}
    (ht : K.heap t = some .tcb) : ρ (fld t oAFFINITY) = μ (fld t oAFFINITY) :=
  hV.2.1 _ (Or.inr (E2EP.ownP_aff_gate hK (hK.base.base.tcb t ht oAFFINITY (Or.inl rfl)).1 μ))

/-- **The start [P] homes every TCB on the starting core** (module docstring): a chain state `σ'` equal off user
words to a memory `ρ` view-equal (for core `L.cpu σ'`) to the physical memory `μ` gives `μ`'s `AFFINITY` word of
every TCB of the layout equal to `L.cpu σ'`. -/
theorem start_aff {K : KLayoutP} (hK : RegionOKP K) {Ch : S → Prop} (hC : ChainLay (L := L) K.toKLayout Ch)
    {σ' : S} (h' : Ch σ') {ρ μ : U64 → U64} (hρ : ∀ x, P1.Aligned x → x ∉ K.user → L.mem σ' x = ρ x)
    {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {hs : U64 → Prop}
    (hV : Serial.VEq (ownP K) cls ko (L.cpu σ') hs ρ μ) {t : U64} (ht : K.heap t = some .tcb) :
    μ (fld t oAFFINITY) = L.cpu σ' := by
  obtain ⟨ha, hu, e⟩ := slJAt_aff (hC.bun σ' h') ht
  rw [← veq_aff hK hV ht, ← hρ _ ha hu, e]

/-- **Two starts in one epoch are by one core** (module docstring): start data of `start_aff`'s shape for two
chain states at physical memories agreeing on the TCBs' `AFFINITY` words have the same `cpu`. -/
theorem start_two_cores {K : KLayoutP} (hK : RegionOKP K) {Ch : S → Prop} (hC : ChainLay (L := L) K.toKLayout Ch)
    {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}
    {σ₁ σ₂ : S} (h₁ : Ch σ₁) (h₂ : Ch σ₂) {ρ₁ ρ₂ μ₁ μ₂ : U64 → U64} {hs₁ hs₂ : U64 → Prop}
    (hρ₁ : ∀ x, P1.Aligned x → x ∉ K.user → L.mem σ₁ x = ρ₁ x)
    (hρ₂ : ∀ x, P1.Aligned x → x ∉ K.user → L.mem σ₂ x = ρ₂ x)
    (hV₁ : Serial.VEq (ownP K) cls ko (L.cpu σ₁) hs₁ ρ₁ μ₁) (hV₂ : Serial.VEq (ownP K) cls ko (L.cpu σ₂) hs₂ ρ₂ μ₂)
    (hμ : ∀ t, K.heap t = some .tcb → μ₁ (fld t oAFFINITY) = μ₂ (fld t oAFFINITY)) : L.cpu σ₁ = L.cpu σ₂ := by
  have ht := slJAt_cur (hC.bun σ₁ h₁)
  rw [← start_aff hK hC h₁ hρ₁ hV₁ ht, ← start_aff hK hC h₂ hρ₂ hV₂ ht, hμ _ ht]

end
end Fl4Proofs.P2.GlueCross
