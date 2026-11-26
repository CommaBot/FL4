/-
P3 (line mmuAD, gen 21): **the [J] placement bundles of P3/JExtVSteps(2) derived from layout facts** —
`JWPl` and `DetPl` from a pure layout record `JVLay`, and `JVLay` itself from the P3 joint invariant `JAtZ` plus
the VCPU placement `JVm` (P3/JVm.lean, the fact P2 asks at each VM bundle; `JVm.empty` natively).

## The layout record

`JVLay V th U` (memory-free; `U` the IPC-buffer words): the typed heap `Placed` (P3/Layout), its kinds TCB / CNode
only, every TCB a `P1.TcbAddr`, every VCPU of `V` 2^15-aligned and fitting, apart from every object of `th` and
from the other VCPUs, and every word of `U` aligned, in no slot, in no TCB and in no VCPU of `V`.

* **`JVLay.jwPl`**: `JWPl V th` (all six fields).
* **`JVLay.detPl`**: `DetPl V th (fun _ => U)` (all seven fields).
* `JVLay.nJS`: the generic "a word in no object of `th` but a TCB at an offset ≥ 192 other than 3328 / 3664, and
  no VCPU's `TCB` word, is none of `JW` / `SW`" — what each placement field reduces to.

## From the joint invariant

* **`JAtZ.jvLay`** `(J : JAtZ …) (Jv : JVm V H s σ) : JVLay V Z.th (BufU Z σ)`: `Placed` (`XTopAt.rel`), `thk`,
  `TcbPlaced` (`IPlaced`), the VCPUs' alignment / fit / mutual apartness and their apartness from the typed heap
  (`HeapOK` of `JKern.heap`, `JPlaced.tcb` / `cnode`, `JVm.heap`; a VCPU address is no typed-heap object by
  `JVm.spec` and `StateRel`), and the buffer words (`JAtZ.bufU_rbuf`, `JAtZ.bufU_noSlot`, and for the VCPUs
  `JCarry.bufPg` + `JVm.sep`: a buffer word lies in a data page, which `JVm.sep` keeps off every VCPU).
* **`JAtZ.jwPl`**, **`JAtZ.detPl`** (at `Ub := fun _ => BufU Z σ`), and the native forms **`JAtZ.jwPl0`**,
  **`JAtZ.detPl0`** (`V = ∅`, `JVm.empty`: no premise beyond `JAtZ`).

## Also derived (`JAtZ` + `JVm`)

* **`JAtZ.detAtB`** (`DetAtB`, P3/JExtVStepsB, at `Ub := fun _ => BufU Z σ`): node placed (`JAtZ.nodePl`, from
  `JKern.ksbAl` / `nodeFit` / `hnd`), IPI / action words outside the extension (`JAtZ.nodeW`), the buffer lookup kept
  along binding / `CW` writes (`JAtZ.tw_nBC` + `P1.lookup_ipc_buffer_same`) and in `BufU` (`JAtZ.bufOK`).
  `DetAt` itself is not derivable (P3/JExtVStepsB module docstring: its `buf` ranges over slot-word writes).
* **`JAtZ.hact`** (`sts_jv`'s `hact`), **`JAtZ.hct`** (`vcpu_decode_settcb_jv`'s `hct`, `JKern.curT`),
  **`JAtZ.thrCap`** (the `Thread` half of `hex`, `SlotsValid`), **`JVLay.hvi`** (`vcpu_enter_nosig`'s `hvi`, from
  the layout and `JExtV.bnd`).

## Step theorems without the derived premises

* **`sts_jv_of`** (no `JWPl`, `hact`), **`vcpu_enter_unbound_of`** (no `DetPl`), **`vcpu_detach_jv_of`** (no `DetPl`,
  `DetAt`), **`vcpu_decode_settcb_jv_of`** (no `DetPl`, `DetAt`, `hct`, `Thread` half of `hex`; `hexs` [J] stays:
  the extra cap slots are slots of the typed heap, a syscall front-end fact, P1's `DecPre.extra`),
  **`vcpu_finalise_jv_of`** (no `DetPl`, `DetAt`; `FinPl` [J] stays: the VCPU list's link words — no `JAtZ` / `JVm`
  field says the VCPU list's members are `V`'s VCPUs, P1's `VListed` / `VtIoPlace`), **`vcpu_enter_nosig_lay`** /
  **`vcpu_enter_bound_lay`** (no `hvi`; over `JVLay` + `DetAtB`, since at a `JAtZ` state every VCPU word is 0 and the
  bound-thread theorems are vacuous; `hns` / `hcs` [J] stay).

No premise is introduced here: every theorem's hypotheses are `JAtZ` (P3's proved joint invariant) and `JVm`
(the existing VCPU placement record; for `V = ∅` it is `JVm.empty`). In VM epochs `JAtZ` is not a proved
invariant (its `ext : JExt` fails, P3/JExtV.lean), so there these derivations need the `JVLay` record itself,
whose fields are all non-`ext` facts; no VM-epoch joint invariant exists yet. No existing statement changed.
-/
import Fl4Proofs.P3.JExtVStepsB
import Fl4Proofs.P3.JVm
import Fl4Proofs.P3.BufKeepJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Values of the extension's words -/

theorem lay_tw_val {t K : U64} (h : P1.TcbAddr t) (hK : K.val < 4096) :
    (core.num.U64.wrapping_add t K).val = t.val + K.val := by
  have := h.fits
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem lay_tVcpu_val {t : U64} (h : P1.TcbAddr t) : (tVcpuA t).val = t.val + 3664 := by
  have := h.fits
  unfold tVcpuA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem lay_stA_val {t : U64} (h : P1.TcbAddr t) : (P1.stA t).val = t.val + 3328 := by
  have := h.fits
  rw [P1.stA_eq]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem lay_vw_val {v o : U64} (h : v.val + 32768 ≤ 2 ^ 64) (ho : o.val < 32768) :
    (core.num.U64.wrapping_add v o).val = v.val + o.val := by
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem lay_vTcb_val {v : U64} (h : v.val + 32768 ≤ 2 ^ 64) : (vTcbA v).val = v.val + 20480 := by
  unfold vTcbA; rw [lay_vw_val h (by simp [vcpu.TCB])]; simp [vcpu.TCB]

theorem lay_pend_val {v : U64} (h : v.val + 32768 ≤ 2 ^ 64) : (pendA v).val = v.val + 20520 := by
  unfold pendA; rw [lay_vw_val h (by simp [vcpu.PENDING])]; simp [vcpu.PENDING]

theorem lay_svm_val {v : U64} (h : v.val + 32768 ≤ 2 ^ 64) : (svmA v).val = v.val + 20536 := by
  unfold svmA; rw [lay_vw_val h (by simp [vcpu.SVM_CPU])]; simp [vcpu.SVM_CPU]

/-! ## The layout record -/

/-- **The layout the extension's placement bundles need** (module docstring). -/
structure JVLay (V : Set U64) (th : TypedHeap) (U : Set U64) : Prop where
  pl : Placed th
  thk : ∀ q k, th q = some k → k = .tcb ∨ ∃ r, k = .cnode r
  tA : ∀ t, th t = some .tcb → P1.TcbAddr t
  vfit : ∀ v ∈ V, v.val % 32768 = 0 ∧ v.val + 32768 ≤ 2 ^ 64
  vap : ∀ v ∈ V, ∀ p k, th p = some k → p.val + objSize k ≤ v.val ∨ v.val + 32768 ≤ p.val
  vv : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → v.val + 32768 ≤ w.val ∨ w.val + 32768 ≤ v.val
  ua : ∀ b ∈ U, P1.Aligned b
  usl : ∀ b ∈ U, ∀ y, IsSlot th y → ¬ (y.val ≤ b.val ∧ b.val < y.val + 32)
  ut : ∀ b ∈ U, ∀ t, th t = some .tcb → b.val < t.val ∨ t.val + 4096 ≤ b.val
  uv : ∀ b ∈ U, ∀ v ∈ V, b.val < v.val ∨ v.val + 32768 ≤ b.val

variable {V : Set U64} {th : TypedHeap} {U : Set U64}

/-- A word inside a CNode lies in one of its slots. -/
theorem lay_cnode_slot (hP : Placed th) {p : U64} {r : Nat} (hp : th p = some (.cnode r)) {b : U64}
    (h1 : p.val ≤ b.val) (h2 : b.val < p.val + objSize (.cnode r)) :
    ∃ y, IsSlot th y ∧ y.val ≤ b.val ∧ b.val < y.val + 32 := by
  have h2' : b.val < p.val + 32 * 2 ^ r := by simpa [objSize] using h2
  have hi : IsSlotAt th p ((b.val - p.val) / 32) := Or.inl ⟨r, hp, by omega⟩
  refine ⟨slotOf p ((b.val - p.val) / 32), ⟨p, _, hi, rfl⟩, ?_⟩
  rw [hi.val hP]; omega

/-- A slot word's object: the slot `y` lies in the object at `p` (in its first 192 bytes for a TCB). -/
theorem lay_slot_in (hP : Placed th) {y : U64} (hy : IsSlot th y) :
    ∃ p k, th p = some k ∧ p.val ≤ y.val ∧ y.val + 32 ≤ p.val + objSize k ∧
      (k = .tcb → y.val + 32 ≤ p.val + 192) ∧ (wordOf y 8#u64).val = y.val + 8 := by
  obtain ⟨p, i, hi, rfl⟩ := hy
  obtain ⟨k, hk, hs⟩ := hi.size
  have hf := hP.fits p k hk
  have hyv := hi.val hP
  refine ⟨p, k, hk, by omega, by omega, fun ek => ?_, ?_⟩
  · subst ek
    rcases hi with ⟨r, hr, -⟩ | ⟨-, hi⟩
    · rw [hk] at hr; cases hr
    · simp [tcbSlots] at hi; omega
  · rw [wordOf_val (by simp; omega), hyv]; simp

/-- **The generic placement step, `JW` half**: a word that lies in no typed-heap object except a TCB at an
offset ≥ 192 other than the VCPU word's, and is no VCPU's `TCB` word, is no `JW` word. -/
theorem JVLay.nJ (Ly : JVLay V th U) {b : U64}
    (h1 : ∀ p k, th p = some k → p.val ≤ b.val → b.val < p.val + objSize k →
      k = .tcb ∧ p.val + 192 ≤ b.val ∧ b.val ≠ p.val + 3664)
    (h2 : ∀ v ∈ V, b.val ≠ v.val + 20480) : ¬ JW V th b := by
  rintro (⟨y, hy, e⟩ | ⟨t, ht, rfl⟩ | ⟨v, hv, rfl⟩)
  · obtain ⟨p, k, hk, g1, g2, g3, g4⟩ := lay_slot_in Ly.pl hy
    have hbv : b.val = y.val ∨ b.val = y.val + 8 := by
      rcases e with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr g4
    obtain ⟨ek, f1, -⟩ := h1 p k hk (by omega) (by omega)
    have := g3 ek; omega
  · have hv := lay_tVcpu_val (Ly.tA t ht)
    obtain ⟨-, -, g⟩ := h1 t .tcb ht (by omega) (by simp [objSize]; omega)
    exact g hv
  · exact h2 v hv (lay_vTcb_val (Ly.vfit v hv).2)

/-- **The generic placement step, `SW` half.** -/
theorem JVLay.nS (Ly : JVLay V th U) {b : U64}
    (h1 : ∀ t, th t = some .tcb → t.val ≤ b.val → b.val < t.val + 4096 → b.val ≠ t.val + 3328) :
    ¬ SW th b := by
  rintro ⟨t, ht, rfl⟩
  exact h1 t ht (by rw [lay_stA_val (Ly.tA t ht)]; omega) (by rw [lay_stA_val (Ly.tA t ht)]; omega)
    (lay_stA_val (Ly.tA t ht))

/-- **The generic placement step** (both halves). -/
theorem JVLay.nJS (Ly : JVLay V th U) {b : U64}
    (h1 : ∀ p k, th p = some k → p.val ≤ b.val → b.val < p.val + objSize k →
      k = .tcb ∧ p.val + 192 ≤ b.val ∧ b.val ≠ p.val + 3664 ∧ b.val ≠ p.val + 3328)
    (h2 : ∀ v ∈ V, b.val ≠ v.val + 20480) : ¬ JW V th b ∧ ¬ SW th b :=
  ⟨Ly.nJ (fun p k hp g1 g2 => let h := h1 p k hp g1 g2; ⟨h.1, h.2.1, h.2.2.1⟩) h2,
   Ly.nS fun t ht g1 g2 => (h1 t .tcb ht g1 (by simp [objSize]; exact g2)).2.2.2⟩

/-- A word inside a VCPU of `V` at an offset other than `TCB`'s is none of `JW` / `SW`. -/
theorem JVLay.nJS_v (Ly : JVLay V th U) {v : U64} (hv : v ∈ V) {b : U64} (h1 : v.val ≤ b.val)
    (h2 : b.val < v.val + 32768) (h3 : b.val ≠ v.val + 20480) : ¬ JW V th b ∧ ¬ SW th b := by
  refine Ly.nJS (fun p k hp g1 g2 => ?_) (fun w hw => ?_)
  · exfalso; rcases Ly.vap v hv p k hp with e | e <;> omega
  · by_cases e : v = w
    · subst e; exact h3
    · rcases Ly.vv v hv w hw e with e' | e' <;> omega

/-- A word at offset `K` of a TCB of `th`, `192 ≤ K < 4096`, `K ≠ 3664`, is no `JW` word (and no `SW` word when
`K ≠ 3328`). -/
theorem JVLay.nJS_t (Ly : JVLay V th U) {t : U64} (ht : th t = some .tcb) {b : U64} {K : Nat}
    (hb : b.val = t.val + K) (hK1 : 192 ≤ K) (hK2 : K < 4096) (hK3 : K ≠ 3664) :
    ¬ JW V th b ∧ (K ≠ 3328 → ¬ SW th b) := by
  have hta := (Ly.tA t ht).align
  have h1 : ∀ p k, th p = some k → p.val ≤ b.val → b.val < p.val + objSize k →
      k = .tcb ∧ p.val + 192 ≤ b.val ∧ b.val ≠ p.val + 3664 ∧ (K ≠ 3328 → b.val ≠ p.val + 3328) := by
    intro p k hp g1 g2
    by_cases e : p = t
    · subst e; rw [ht] at hp; cases hp
      exact ⟨rfl, by omega, by omega, fun h => by omega⟩
    · exfalso; rcases Ly.pl.disj p t k .tcb hp ht e with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega
  have h2 : ∀ v ∈ V, b.val ≠ v.val + 20480 := by
    intro v hv
    rcases Ly.vap v hv t .tcb ht with e | e <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e) <;> omega
  have hJ : ¬ JW V th b := Ly.nJ (fun p k hp g1 g2 => (h1 p k hp g1 g2).elim fun a h => ⟨a, h.1, h.2.1⟩) h2
  refine ⟨hJ, fun hK => ?_⟩
  exact Ly.nS fun t' ht' g1 g2 => (h1 t' .tcb ht' g1 (by simp only [objSize]; exact g2)).2.2.2 hK

/-- **`JWPl` from the layout.** -/
theorem JVLay.jwPl (Ly : JVLay V th U) : JWPl V th where
  jw b hb := by
    rcases hb with ⟨y, hy, rfl | rfl⟩ | ⟨t, ht, rfl⟩ | ⟨v, hv, rfl⟩
    · have := hy.align Ly.pl; unfold P1.Aligned; omega
    · have := hy.align Ly.pl
      obtain ⟨-, -, -, -, -, -, g⟩ := lay_slot_in Ly.pl hy
      unfold P1.Aligned; rw [g]; omega
    · have := lay_tVcpu_val (Ly.tA t ht); have := (Ly.tA t ht).align
      unfold P1.Aligned; omega
    · have := lay_vTcb_val (Ly.vfit v hv).2; have := (Ly.vfit v hv).1
      unfold P1.Aligned; omega
  sw b hb := by
    obtain ⟨t, ht, rfl⟩ := hb
    have := lay_stA_val (Ly.tA t ht); have := (Ly.tA t ht).align
    unfold P1.Aligned; omega
  swjw b hb := by
    obtain ⟨t, ht, rfl⟩ := hb
    exact (Ly.nJS_t ht (lay_stA_val (Ly.tA t ht)) (by omega) (by omega) (by omega)).1
  slv y hy t ht := by
    obtain ⟨p, k, hk, g1, g2, g3, g4⟩ := lay_slot_in Ly.pl hy
    have hv := lay_tVcpu_val (Ly.tA t ht)
    have hd : y.val + 32 ≤ t.val + 192 ∨ y.val + 32 ≤ t.val ∨ t.val + 4096 ≤ y.val := by
      by_cases e : p = t
      · subst e; rw [ht] at hk; cases hk; exact Or.inl (g3 rfl)
      · rcases Ly.pl.disj p t k .tcb hk ht e with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := congrArg UScalar.val e; rw [hv] at this; omega
    · have := congrArg UScalar.val e; rw [g4, hv] at this; omega
  slb y hy v hv := by
    obtain ⟨p, k, hk, g1, g2, g3, g4⟩ := lay_slot_in Ly.pl hy
    have hb := lay_vTcb_val (Ly.vfit v hv).2
    have hd := Ly.vap v hv p k hk
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have := congrArg UScalar.val e; rw [hb] at this; omega
    · have := congrArg UScalar.val e; rw [g4, hb] at this; omega
  vb t ht v hv e := by
    have := congrArg UScalar.val e
    rw [lay_tVcpu_val (Ly.tA t ht), lay_vTcb_val (Ly.vfit v hv).2] at this
    rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega

/-- A buffer word of `U` is none of `JW` / `SW`. -/
theorem JVLay.nJS_u (Ly : JVLay V th U) {b : U64} (hb : b ∈ U) : ¬ JW V th b ∧ ¬ SW th b := by
  refine Ly.nJS (fun p k hp g1 g2 => ?_) (fun v hv => ?_)
  · rcases Ly.thk p k hp with rfl | ⟨r, rfl⟩
    · exfalso; simp only [objSize] at g2; rcases Ly.ut b hb p hp with e | e <;> omega
    · obtain ⟨y, hy, f1, f2⟩ := lay_cnode_slot Ly.pl hp g1 g2
      exact absurd ⟨f1, f2⟩ (Ly.usl b hb y hy)
  · rcases Ly.uv b hb v hv with e | e <;> omega

/-- **`DetPl` from the layout**, at the buffer words `U` for every TCB. -/
theorem JVLay.detPl (Ly : JVLay V th U) : DetPl V th (fun _ => U) where
  pl := Ly.jwPl
  h0 h := (Ly.tA _ h).ne0 (by simp)
  ta := Ly.tA
  ua _ _ := Ly.ua
  rep t ht b hb := by
    rcases hb with ⟨K, h1, h2, h3, rfl⟩ | hb
    · have e := lay_tw_val (Ly.tA t ht) (K := K) (by omega)
      have := Ly.nJS_t ht e (by omega) (by omega) (by omega)
      exact ⟨this.1, this.2 (by omega)⟩
    · exact Ly.nJS_u hb
  vca v hv := by
    have f := Ly.vfit v hv
    exact ⟨by unfold P1.Aligned; rw [lay_pend_val f.2]; omega,
      by unfold P1.Aligned; rw [lay_svm_val f.2]; omega⟩
  vc v hv b hb := by
    have f := Ly.vfit v hv
    rcases hb with rfl | rfl
    · have := lay_pend_val f.2; exact Ly.nJS_v hv (by omega) (by omega) (by omega)
    · have := lay_svm_val f.2; exact Ly.nJS_v hv (by omega) (by omega) (by omega)

/-- **`vcpu_enter_nosig`'s `hvi` from the layout**: the bound VCPU's internal words are aligned and none of
`JW` / `SW` (its VCPU is in `V` by `JExtV.bnd`). -/
theorem JVLay.hvi {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {X : Set U64} {s : S}
    (Ly : JVLay V th U) (E : JExtV (L := L) V X th s) {t : U64} (ht : th t = some .tcb)
    (hv0 : L.mem s (tVcpuA t) ≠ 0#u64) :
    ∀ b, VW (L.mem s (tVcpuA t)) b → P1.Aligned b ∧ ¬ JW V th b ∧ ¬ SW th b := by
  obtain ⟨hv, -⟩ := (E.bnd t ht).resolve_left hv0
  rintro b ⟨o, h1, h2, h3, rfl⟩
  have f := Ly.vfit _ hv
  have e := lay_vw_val f.2 h1
  exact ⟨by unfold P1.Aligned; rw [e]; omega, Ly.nJS_v hv (by omega) (by omega) (by omega)⟩

end

/-! ## From the joint invariant -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V : Set U64}

/-- A typed-heap object is an `H` object of the same size. -/
theorem JAtZ.thH (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ p k, Z.th p = some k → ∃ hk, H p = some hk ∧ 2 ^ hk.bits = objSize k := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  intro p k hp
  rcases J.thk p k hp with rfl | ⟨r, rfl⟩
  · exact ⟨_, (hJ.tcb p).1 hp, by simp [P1.HKind.bits, objSize]⟩
  · exact ⟨_, hJ.cnode p r hp, by simp only [P1.HKind.bits, objSize]; rw [pow_add]; ring⟩

/-- **The layout record at a joint state** (module docstring). -/
theorem JAtZ.jvLay (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    JVLay V Z.th (BufU Z σ) := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  have hSR := J.xtop.rel.2.1.1
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hvn : ∀ v ∈ V, Z.th v = none := by
    intro v hv
    obtain ⟨x, hx⟩ := Jv.spec v hv
    cases h : Z.th v with
    | none => rfl
    | some k =>
      exfalso
      rcases J.thk v k h with rfl | ⟨r, rfl⟩
      · obtain ⟨c, hc, -⟩ := hSR.tcb v h
        rw [hc] at hx; cases hx
      · obtain ⟨c, hc, -⟩ := hSR.cnode v r h
        rw [hc] at hx; cases hx
  refine ⟨J.xtop.rel.1, J.thk, fun t ht => J.ip.e.tcb t (J.thT t ht), fun v hv => ?_, fun v hv p k hp => ?_,
    fun v hv w hw hne => ?_, fun b hb => (J.bufU_rbuf hb).1.1, fun b hb y hy => J.bufU_noSlot y hy b hb,
    fun b hb t ht => ?_, fun b hb v hv => ?_⟩
  · have h1 := hH.align v _ (Jv.heap v hv); have h2 := hH.fits v _ (Jv.heap v hv)
    simp only [P1.HKind.bits, h15] at h1 h2; exact ⟨h1, h2⟩
  · obtain ⟨hk, hpk, he⟩ := J.thH p k hp
    have hne : p ≠ v := fun e => by rw [e, hvn v hv] at hp; cases hp
    rcases hH.disj p hk v _ hpk (Jv.heap v hv) hne with e | e
    · left; rw [← he]; exact e
    · right; simpa [P1.HKind.bits, h15] using e
  · rcases hH.disj v _ w _ (Jv.heap v hv) (Jv.heap w hw) hne with e | e <;>
      simp only [P1.HKind.bits, h15] at e
    · exact Or.inl e
    · exact Or.inr e
  · have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    have := (J.bufU_rbuf hb).1.2.1 t ((hJ.tcb t).1 ht)
    rw [h12] at this; exact this
  · obtain ⟨wp, hwp, rfl⟩ := J.bufU_B hb
    obtain ⟨q, vms, hq, g1, g2⟩ := J.carry.bufPg wp hwp
    obtain ⟨x, hx⟩ := Jv.spec v hv
    have hne : q ≠ v.bv := fun e => by rw [e, hx] at hq; cases hq
    rcases Jv.sep v hv q _ hq hne with e | e
    · left
      have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
        simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
      rw [eb] at e; omega
    · right; omega

/-- **`JWPl` at a joint state.** -/
theorem JAtZ.jwPl (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    JWPl V Z.th := (J.jvLay Jv).jwPl

/-- **`DetPl` at a joint state**, at the IPC-buffer words `BufU Z σ`. -/
theorem JAtZ.detPl (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    DetPl V Z.th (fun _ => BufU Z σ) := (J.jvLay Jv).detPl

/-- Native `JWPl` (`V = ∅`). -/
theorem JAtZ.jwPl0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : JWPl ∅ Z.th :=
  J.jwPl (V := ∅) JVm.empty

/-- Native `DetPl` (`V = ∅`). -/
theorem JAtZ.detPl0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : DetPl ∅ Z.th (fun _ => BufU Z σ) :=
  J.detPl (V := ∅) JVm.empty

/-- The current core's node is placed (`JKern`'s `ksbAl` / `nodeFit` / `hnd`). -/
theorem JAtZ.nodePl (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.NodePlaced st (P1.Heap.tcbs H) s (L.cpu s) where
  align := by unfold P1.LawfulStore.nodeBase; have := J.kern.ksbAl; omega
  fits := by unfold P1.LawfulStore.nodeBase; have := J.kern.nodeFit; omega
  disj t ht := by
    have := J.kern.hnd t .tcb ht (L.cpu s) J.kern.cpuCs
    simpa [P1.HKind.bits] using this

/-- A word of the current core's node is none of `JW` / `SW`. -/
theorem JAtZ.nodeW (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {b : U64}
    (h1 : L.nodeBase s (L.cpu s) ≤ b.val) (h2 : b.val < L.nodeBase s (L.cpu s) + 4288) :
    ¬ JW V Z.th b ∧ ¬ SW Z.th b := by
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  refine (J.jvLay Jv).nJS (fun p k hp g1 g2 => ?_) (fun v hv => ?_)
  · exfalso
    obtain ⟨hk, hpk, he⟩ := J.thH p k hp
    rcases J.kern.hnd p hk hpk (L.cpu s) J.kern.cpuCs with e | e <;> (try rw [he] at e) <;> omega
  · have := ((J.jvLay Jv).vfit v hv).2
    rcases J.kern.hnd v _ (Jv.heap v hv) (L.cpu s) J.kern.cpuCs with e | e <;>
      (try simp only [P1.HKind.bits, h15] at e) <;> omega

/-- A TCB word at an offset outside the register range, other than the VCPU / state words, is no binding word
and no detach word `CW` (what the IPC-buffer lookup's three words need). -/
theorem JAtZ.tw_nBC (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {t : U64}
    (ht : Z.th t = some .tcb) {w : U64} {K : Nat} (hw : w.val = t.val + K) (hK : K < 4096)
    (hK2 : K < 256 ∨ 3328 < K) (hK3 : K ≠ 3664) (hK8 : K % 8 = 0) :
    P1.Aligned w ∧ ¬ (BW V Z.th w ∨ CW st V Z.th (fun _ => BufU Z σ) s w) := by
  have Ly := J.jvLay Jv
  have hta := Ly.tA t ht
  have ha := hta.align
  have dT : ∀ t', Z.th t' = some .tcb → t' ≠ t → t'.val + 4096 ≤ t.val ∨ t.val + 4096 ≤ t'.val := by
    intro t' ht' hne
    have h1 := (Ly.tA t' ht').align
    have : t'.val ≠ t.val := fun e => hne (UScalar.eq_of_val_eq e)
    omega
  have hN := J.nodePl
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have nodeT := hN.disj t ((hJ.tcb t).1 ht)
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  rw [h12] at nodeT
  refine ⟨by unfold P1.Aligned; rw [hw]; omega, ?_⟩
  rintro ((⟨t', ht', rfl⟩ | ⟨v, hv, rfl⟩) | (e | e | ⟨t', ht', h | e⟩ | ⟨v, hv, e | e⟩))
  · rw [lay_tVcpu_val (Ly.tA t' ht')] at hw
    by_cases e : t' = t
    · subst e; omega
    · rcases dT t' ht' e with e' | e' <;> omega
  · rw [lay_vTcb_val (Ly.vfit v hv).2] at hw
    rcases Ly.vap v hv t .tcb ht with e | e <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e) <;> omega
  · rw [e] at hw
    have := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
    have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
    unfold ipiA at hw; rw [this] at hw
    rcases nodeT with e' | e' <;> omega
  · rw [e] at hw
    have := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
    unfold actA at hw; rw [this] at hw
    rcases nodeT with e' | e' <;> omega
  · rcases h with ⟨K', g1, g2, g3, rfl⟩ | hb
    · rw [lay_tw_val (Ly.tA t' ht') (by omega)] at hw
      by_cases e : t' = t
      · subst e; omega
      · rcases dT t' ht' e with e' | e' <;> omega
    · rcases Ly.ut w hb t ht with e' | e' <;> omega
  · rw [e, lay_stA_val (Ly.tA t' ht')] at hw
    by_cases e' : t' = t
    · subst e'; omega
    · rcases dT t' ht' e' with e'' | e'' <;> omega
  · rw [e, lay_pend_val (Ly.vfit v hv).2] at hw
    rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega
  · rw [e, lay_svm_val (Ly.vfit v hv).2] at hw
    rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega

/-- **`DetAtB` at a joint state** (P3/JExtVStepsB): the node placed (`JAtZ.nodePl`), its IPI / action words
outside the extension (`JAtZ.nodeW`), and the buffer lookup kept along binding / `CW` writes (it reads only the
TCB's `IPC_BUFFER` word and buffer-slot words, `P1.lookup_ipc_buffer_same`), landing in `BufU` (`JAtZ.bufOK`). -/
theorem JAtZ.detAtB (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    DetAtB st V Z.th (fun _ => BufU Z σ) s where
  node := ⟨_, J.nodePl⟩
  nd b hb := by
    have hN := J.nodePl
    rcases hb with rfl | rfl
    · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
      have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
      unfold ipiA; exact J.nodeW Jv (by rw [e]; omega) (by rw [e]; omega)
    · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
      have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
      unfold actA; exact J.nodeW Jv (by rw [e]; omega) (by rw [e]; omega)
  buf s1 h t ht := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hta := (J.jvLay Jv).tA t ht
    have e1 : (P1.ibWordA t).val = t.val + 3512 := by
      unfold P1.ibWordA; rw [lay_tw_val hta (by simp)]; simp
    have e2 : (P1.sbWordA t).val = t.val + 64 := by
      rw [P1.sbWordA_eq, lay_tw_val hta (by simp)]; simp
    have e3 : (core.num.U64.wrapping_add (P1.sbWordA t) 8#u64).val = t.val + 72 := by
      rw [P1.sbWordA8_eq, lay_tw_val hta (by simp)]; simp
    have k1 := J.tw_nBC Jv ht e1 (by omega) (by omega) (by omega) (by omega)
    have k2 := J.tw_nBC Jv ht e2 (by omega) (by omega) (by omega) (by omega)
    have k3 := J.tw_nBC Jv ht e3 (by omega) (by omega) (by omega) (by omega)
    have hI : P1.IbSame (L := L) s s1 t := ⟨h.mem_eq k1.1 k1.2, h.mem_eq k2.1 k2.2, h.mem_eq k3.1 k3.2⟩
    rw [P1.lookup_ipc_buffer_same hI]
    exact J.bufOK ((hJ.tcb t).1 ht)

/-- `sts_jv`'s `hact` at a joint state. -/
theorem JAtZ.hact (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    P1.Aligned (actA st s) ∧ ¬ JW V Z.th (actA st s) ∧ ¬ SW Z.th (actA st s) :=
  ⟨(J.detAtB Jv).actA_al, ((J.detAtB Jv).nd _ (Or.inr rfl)).1, ((J.detAtB Jv).nd _ (Or.inr rfl)).2⟩

/-- `vcpu_decode_settcb_jv`'s `hct` at a joint state (`JKern.curT`). -/
theorem JAtZ.hct (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : Z.th (L.mem s (curA st s)) = some .tcb :=
  J.kern.curT

/-- The `Thread` half of `hex` at a joint state: a slot's `Thread` cap names a TCB (`SlotsValid`). -/
theorem JAtZ.thrCap (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) :
    ∀ p, capV (L.mem s) x = .Thread p → Z.th p = some .tcb := by
  intro p hp
  have hV := J.xtop.rel.2.1.2.1
  obtain ⟨q, i, hi, rfl⟩ := hx
  have hc : CapValid Z.th (capV (L.mem s) (slotOf q i)) := by
    rcases hi with ⟨r, hq, hi⟩ | ⟨hq, hi⟩
    · exact hV.cnode q r hq i hi _ (capAt_capV _ _)
    · exact hV.tcb q hq i hi _ (capAt_capV _ _)
  rw [hp] at hc; exact hc

end

/-! ## The step theorems without the derived premises -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}
  {ar : machine.Arch A}

/-- **`sts_jv` without `JWPl` / `hact`** (both from `JAtZ` + `JVm`). -/
theorem sts_jv_of (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) {t x : U64} (ht : Z.th t = some .tcb)
    (hx : x ≠ 8#u64 ∨ L.mem s (tVcpuA t) ≠ 0#u64) :
    sched.set_thread_state st s t x ⦃ s' => JExtV (L := L) V X Z.th s' ∧ RunVmB (L := L) Z.th s' ⦄ :=
  sts_jv (J.jwPl Jv) E R ht (J.hact Jv) hx

/-- **`vcpu_enter_unbound` without `DetPl`.** -/
theorem vcpu_enter_unbound_of (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) (a' : A) {t : U64}
    (ht : Z.th t = some .tcb) (h0 : L.mem s (tVcpuA t) = 0#u64) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ :=
  vcpu_enter_unbound hA (J.detPl Jv) E R a' ht h0

/-- **`vcpu_detach_jv` without `DetPl` / `DetAt`** (over `vcpu_detach_jvB`, `DetAtB` from `JAtZ` + `JVm`). -/
theorem vcpu_detach_jv_of (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) (a' : A) {t : U64}
    (ht : Z.th t = some .tcb) :
    vcpu.detach st ar s a' t ⦃ r => DetPost st V X Z.th (fun _ => BufU Z σ) t s r.1 ⦄ :=
  vcpu_detach_jvB hA (J.detPl Jv) (J.detAtB Jv) E R a' ht

/-- **`vcpu_decode_settcb_jv` without `DetPl` / `DetAt` / `hct` and the `Thread` half of `hex`**: what stays is
`hexs` [J], the extra cap slots being slots of the typed heap (the syscall front end's `lookup_extra_caps`
resolves them; P1's `DecPre.extra`). -/
theorem vcpu_decode_settcb_jv_of (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) (a' : A)
    {len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hvV : v ∈ V)
    (hexs : ∀ x ∈ extra.val, x ≠ 0#u64 → IsSlot Z.th x) :
    vcpu.decode st ar s a' fl4_abi.label.X86VCPUSetTCB len v call buf extra ⦃ r s' _ =>
      JExtV (L := L) V X Z.th s' ∧ RunVmB (L := L) Z.th s' ⦄ :=
  vcpu_decode_settcb_jvB hA (J.detPl Jv) (J.detAtB Jv) E R a' hvV
    (fun x hx h0 => ⟨hexs x hx h0, J.thrCap (hexs x hx h0)⟩) J.hct

/-- **`vcpu_finalise_jv` without `DetPl` / `DetAt`**; `F : FinPl` [J] stays (module docstring of
P3/JExtVSteps2: the VCPU list's link words, which no `JAtZ` / `JVm` field places). -/
theorem vcpu_finalise_jv_of (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) (a' : A) {v : U64}
    (hvV : v ∈ V) (F : FinPl st V Z.th (fun _ => BufU Z σ) s v) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ⦄ :=
  vcpu_finalise_jvB hA (J.detPl Jv) (J.detAtB Jv) E R a' hvV F

end

/-- **`vcpu_enter_nosig` without `hvi`**, from the layout record (`JVLay.hvi`). At a `JAtZ` state the theorem is
vacuous (`JExt.vw`: every VCPU word 0), so it is stated over `JVLay` and `DetAtB` directly. -/
theorem vcpu_enter_nosig_lay {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
    {ar : machine.Arch A} {V X U : Set U64} {th : TypedHeap} (hA : P0.ArchTotal ar) (Ly : JVLay V th U)
    {s : S} (Da : DetAtB st V th (fun _ => U) s) (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A)
    {t : U64} (ht : th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hns : ∀ s', P1.WritesIn st s s' (VW (L.mem s (tVcpuA t))) → obj.Tcb.bound_ntfn st t s' ⦃ n =>
      n ≠ 0#u64 → obj.Ntfn.state st n s' ⦃ x => x ≠ obj.NTFN_ACTIVE ⦄ ⦄) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ :=
  vcpu_enter_nosigB hA Ly.detPl Da E R a ht hv0 (Ly.hvi E ht hv0) hns

/-- **`vcpu_enter_boundB` without `hvi`** (every branch of `vcpu.enter` on a bound thread; `hcs` [J] stays:
`complete_signal`'s effect, P3/JExtVStepsB). -/
theorem vcpu_enter_bound_lay {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
    {ar : machine.Arch A} {V X U : Set U64} {th : TypedHeap} (hA : P0.ArchTotal ar) (Ly : JVLay V th U)
    {s : S} (Da : DetAtB st V th (fun _ => U) s) (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A)
    {t : U64} (ht : th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hcs : ∀ s3 (a1 : A) (n : U64), P1.WritesIn st s s3 (VW (L.mem s (tVcpuA t))) → n ≠ 0#u64 →
      notification.complete_signal st ar s3 a1 n t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
        DetAtB st V th (fun _ => U) r.1 ∧ L.mem r.1 (tVcpuA t) = L.mem s (tVcpuA t) ⦄) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ :=
  vcpu_enter_boundB hA Ly.detPl Da E R a ht hv0 (Ly.hvi E ht hv0) hcs

end Fl4Proofs.P3
