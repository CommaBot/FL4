/-
P3 (line mmuAD, gen 22): **`FinPl` (the VCPU list's placement at a finalise) from the layout and the list's
membership.**

`FinPl st V th Ub s v` [J] (P3/JExtVSteps2) asks the finalised VCPU's own `NEXT` / `PREV` words, the list head
word, the previous VCPU's `NEXT` word and the next VCPU's `PREV` word to be aligned and none of the extension
(`JW`), state (`SW`) or detach (`CW`) words.

* **`JVLay.finPl`**: from the layout record `JVLay` (P3/JExtVLay), `v ∈ V`, and
  - `hL` [J]: **the VCPU list's members are exactly `V`** (`P1.VListed st s w ↔ w ∈ V`). P1 proves the list's
    typing half (`VcpuPl.listed`: a listed VCPU is a heap `.other 15` object) but no equality with a set of
    VCPUs; through `VListed.next` it gives the `NEXT` neighbour (`fin_next_mem`);
  - `hP` [J]: **the `PREV` link stays in the list** (a nonzero `PREV` of a VCPU of `V` is in `V`). P1's `VListed`
    follows `NEXT` only: no P1 or P3 fact relates the `PREV` words to the list (the doubly-linked-list
    invariant), so this is the exact missing fact for the previous neighbour;
  - `hhd` [J]: the head word `VCPU_HEAD` (kernel-global area, offset 80) is aligned and none of `JW` / `SW` — the
    typed heap's CNodes (`.other` objects) may lie in the kernel-global area (`JKern.hksIn`), so this is not
    derivable from `JKern` alone;
  - `hnd` [J]: the current core's `IPI_PENDING` / `SCHED_ACTION` words lie outside every VCPU of `V`.
* **`JAtZ.finPl`**: the same at a joint state with `JVm`: `JVLay` from `JAtZ.jvLay`, and `hnd` derived
  (`JKern.hnd` for the VCPUs' heap objects, `JVm.heap`). Left: `hL`, `hP`, `hhd` (all [J]).
* **`vcpu_finalise_jv_lay`**: `vcpu_finalise_jv_of` (P3/JExtVLay) without `FinPl`.

## `vcpu_enter_boundK`'s placement premises from heap facts

* **`vcpuOm_of_heap`**: `VcpuOm V H.omega H.frame` (`vcpu_enter_boundK`'s `hVo`) from `HeapOK H` and "every VCPU of
  `V` is a heap `.other 15` object" (`JVm.heap`): the VCPU's words are `Heap.omega` words, and no reply / SC /
  notification object (the frame words) meets it (`HeapOK.disj`). **`JAtZ.vcpuOm`**: at a joint state + `JVm`.
* `JAtZ.hTt`: `hTt` from `JAtZ.thT` + `JAtZ.zH`. `hNt` holds by definition for `Nt := H.ntfns`.
* **`vcpu_enter_boundL`**: `vcpu_enter_boundK` over the layout record (`JVLay`, as gen 21's
  `vcpu_enter_bound_lay`) and P1's heap sets, with `DetPl`, `hvi`, `hVo`, `hNt` discharged. Remaining premises:
  `DetAtB`, `Bk` (= `JAtZ.blk`'s statement), `hHk` (= `JKern.heap`), `hVH` (= `JVm.heap`), `hTt`, `hSC`
  (= `JAtZ.slotCapW`'s statement), `hRt` — all [J], every one of them a VCPU-free statement that `JAtZ` already
  proves natively, so a VM-epoch joint invariant carrying `JAtZ`'s VCPU-free fields provides them.

No [P] / [W] / [S] premise; no existing statement changed.

(mmuAD gen 42b17) Stated over `JAtZ`'s `ext`-free part `JAtZB` (P3/JointAt), none reading `JAtZ.ext`: `finPl`, `hTt`;
each `JAtZ` name is a one-line corollary via `JAtZ.toB` with its statement unchanged (the `JAtZB` copies of gens 24-39
deleted).
-/
import Fl4Proofs.P3.JExtVInit
import Fl4Proofs.P3.JExtVLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V X U : Set U64} {th : TypedHeap}

theorem lay_next_val {v : U64} (h : v.val + 32768 ≤ 2 ^ 64) : (P1.vNextA v).val = v.val + 20488 := by
  unfold P1.vNextA; rw [lay_vw_val h (by simp [vcpu.NEXT])]; simp [vcpu.NEXT]

theorem lay_prev_val {v : U64} (h : v.val + 32768 ≤ 2 ^ 64) : (vPrevA v).val = v.val + 20496 := by
  unfold vPrevA; rw [lay_vw_val h (by simp [vcpu.PREV])]; simp [vcpu.PREV]

/-- The next VCPU of a listed VCPU is in `V` when the list's members are `V`. -/
theorem fin_next_mem {s : S} (hL : ∀ w, P1.VListed st s w ↔ w ∈ V) {v : U64} (hv : v ∈ V)
    (hn : L.mem s (P1.vNextA v) ≠ 0#u64) : L.mem s (P1.vNextA v) ∈ V :=
  (hL _).1 (P1.VListed.next ((hL v).2 hv) hn)

/-- A word of a VCPU of `V` at offset 20488 / 20496 (its `NEXT` / `PREV` words). -/
theorem JVLay.finOwn (Ly : JVLay V th U) {s : S} {v : U64} (hv : v ∈ V)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    {b : U64} (hb : b.val = v.val + 20488 ∨ b.val = v.val + 20496) :
    P1.Aligned b ∧ ¬ JW V th b ∧ ¬ CW st V th (fun _ => U) s b := by
  have f := Ly.vfit v hv
  have hb' : v.val + 20488 ≤ b.val ∧ b.val ≤ v.val + 20496 := by omega
  refine ⟨by unfold P1.Aligned; omega, (Ly.nJS_v hv (by omega) (by omega) (by omega)).1, ?_⟩
  rintro (e | e | ⟨t, ht, hr | e⟩ | ⟨w, hw, e | e⟩)
  · have := hnd b (Or.inl e) v hv; omega
  · have := hnd b (Or.inr e) v hv; omega
  · rcases hr with ⟨K, k1, k2, k3, e⟩ | hu
    · have e1 := congrArg UScalar.val e
      rw [lay_tw_val (Ly.tA t ht) (K := K) (by omega)] at e1
      rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega
    · rcases Ly.uv b hu v hv with e' | e' <;> omega
  · have e1 := congrArg UScalar.val e
    rw [lay_stA_val (Ly.tA t ht)] at e1
    rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega
  · have e1 := congrArg UScalar.val e
    rw [lay_pend_val (Ly.vfit w hw).2] at e1
    by_cases ew : v = w
    · subst ew; omega
    · rcases Ly.vv v hv w hw ew with e' | e' <;> omega
  · have e1 := congrArg UScalar.val e
    rw [lay_svm_val (Ly.vfit w hw).2] at e1
    by_cases ew : v = w
    · subst ew; omega
    · rcases Ly.vv v hv w hw ew with e' | e' <;> omega

/-- **`FinPl` from the layout and the list's membership** (module docstring; `hL`, `hP`, `hhd`, `hnd` [J]). -/
theorem JVLay.finPl (Ly : JVLay V th U) {s : S} {v : U64} (hv : v ∈ V)
    (hL : ∀ w, P1.VListed st s w ↔ w ∈ V)
    (hP : ∀ w ∈ V, L.mem s (vPrevA w) ≠ 0#u64 → L.mem s (vPrevA w) ∈ V)
    (hhd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V th (P1.vHeadA st s) ∧ ¬ SW th (P1.vHeadA st s))
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val) :
    FinPl st V th (fun _ => U) s v where
  own b hb := by
    rcases hb with rfl | rfl
    · exact Ly.finOwn hv hnd (Or.inl (lay_next_val (Ly.vfit v hv).2))
    · exact Ly.finOwn hv hnd (Or.inr (lay_prev_val (Ly.vfit v hv).2))
  nbr b hb := by
    rcases hb with rfl | ⟨hp, rfl⟩ | ⟨hn, rfl⟩
    · exact hhd
    · have hw := hP v hv hp
      have f := Ly.vfit _ hw
      have e := lay_next_val f.2
      exact ⟨by unfold P1.Aligned; omega, Ly.nJS_v hw (by omega) (by omega) (by omega)⟩
    · have hw := fin_next_mem hL hv hn
      have f := Ly.vfit _ hw
      have e := lay_prev_val f.2
      exact ⟨by unfold P1.Aligned; omega, Ly.nJS_v hw (by omega) (by omega) (by omega)⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {ar : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- **`FinPl` at a joint state** (module docstring): `hnd` from `JKern.hnd` + `JVm.heap`; `hL`, `hP`, `hhd` [J]. -/
theorem JAtZB.finPl (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {v : U64}
    (hv : v ∈ V) (hL : ∀ w, P1.VListed st s w ↔ w ∈ V)
    (hP : ∀ w ∈ V, L.mem s (vPrevA w) ≠ 0#u64 → L.mem s (vPrevA w) ∈ V)
    (hhd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s)) :
    FinPl st V Z.th (fun _ => BufU Z σ) s v := by
  refine (J.jvLay Jv).finPl hv hL hP hhd fun b hb w hw => ?_
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hN := J.nodePl
  have hb' : L.nodeBase s (L.cpu s) ≤ b.val ∧ b.val < L.nodeBase s (L.cpu s) + 4288 := by
    rcases hb with rfl | rfl
    · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
      have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
      unfold ipiA; rw [e]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
      have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
      unfold actA; rw [e]; omega
  rcases J.kern.hnd w _ (Jv.heap w hw) (L.cpu s) J.kern.cpuCs with e | e <;>
    (try simp only [P1.HKind.bits, h15] at e) <;> omega

/-- `JAtZB.finPl` at `JAtZ` (via `JAtZ.toB`). -/
theorem JAtZ.finPl (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {v : U64}
    (hv : v ∈ V) (hL : ∀ w, P1.VListed st s w ↔ w ∈ V)
    (hP : ∀ w ∈ V, L.mem s (vPrevA w) ≠ 0#u64 → L.mem s (vPrevA w) ∈ V)
    (hhd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s)) :
    FinPl st V Z.th (fun _ => BufU Z σ) s v :=
  Fl4Proofs.P3.JAtZB.finPl (J := J.toB) (Jv := Jv) (hv := hv) (hL := hL) (hP := hP) (hhd := hhd)

/-- **`vcpu_finalise_jv_of` without `FinPl`** (`JAtZ.finPl`; `hL`, `hP`, `hhd` [J]). At a native `JAtZ` state
`V` is empty and the theorem is vacuous; it is the form a VM-epoch joint invariant instantiates. -/
theorem vcpu_finalise_jv_lay (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s) (a' : A) {v : U64}
    (hvV : v ∈ V) (hL : ∀ w, P1.VListed st s w ↔ w ∈ V)
    (hP : ∀ w ∈ V, L.mem s (vPrevA w) ≠ 0#u64 → L.mem s (vPrevA w) ∈ V)
    (hhd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s)) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ⦄ :=
  vcpu_finalise_jv_of hA J Jv E R a' hvV (J.finPl Jv hvV hL hP hhd)

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {V X U : Set U64} {th : TypedHeap}

/-- **`vcpu_enter_boundK`'s `hVo` from the heap** (module docstring). -/
theorem vcpuOm_of_heap {H : P1.Heap} (hH : P1.HeapOK H) (hv : ∀ v ∈ V, H v = some (.other 15)) :
    VcpuOm V (P1.Heap.omega H) (P1.Heap.frame H) := by
  intro v hvV o h1 h2
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hal := hH.align v _ (hv v hvV)
  have hfit := hH.fits v _ (hv v hvV)
  simp only [P1.HKind.bits, h15] at hal hfit
  have e := lay_vw_val (v := v) (o := o) hfit h1
  refine ⟨?_, ?_⟩
  · simp only [P1.Heap.omega, Set.mem_setOf_eq]
    refine ⟨by unfold P1.Aligned; rw [e]; omega, v, _, hv v hvV, Or.inr (Or.inr (Or.inl ⟨15, rfl⟩)), ?_, ?_⟩
    · rw [e]; omega
    · show _ < v.val + 2 ^ 15
      rw [e, h15]; omega
  · intro hf
    simp only [P1.Heap.frame, Set.mem_setOf_eq] at hf
    obtain ⟨-, p, k, hp, hk, hin1, hin2⟩ := hf
    by_cases epv : p = v
    · subst epv
      rw [hv p hvV] at hp
      cases hp
      rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
    · have d := hH.disj p k v _ hp (hv v hvV) epv
      rw [show (2 : Nat) ^ (P1.HKind.other 15).bits = 32768 from by simp [P1.HKind.bits]] at d
      rw [e] at hin1 hin2
      generalize 2 ^ k.bits = m at hin2 d
      omega

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {ar : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem JAtZ.vcpuOm (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    VcpuOm V (P1.Heap.omega H) (P1.Heap.frame H) :=
  vcpuOm_of_heap J.kern.heap Jv.heap

theorem JAtZB.hTt (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ y, Z.th y = some .tcb → y ∈ P1.Heap.tcbs H := fun y hy => J.zH.1 y (J.thT y hy)

/-- `JAtZB.hTt` at `JAtZ` (via `JAtZ.toB`). -/
theorem JAtZ.hTt (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ y, Z.th y = some .tcb → y ∈ P1.Heap.tcbs H :=
  Fl4Proofs.P3.JAtZB.hTt (J := J.toB)

end

set_option maxHeartbeats 4000000 in
/-- **`vcpu_enter_boundK` over the layout record and P1's heap sets** (module docstring): `DetPl`, `hvi`, `hVo`,
`hNt` discharged; `Da`, `Bk`, `hHk`, `hVH`, `hTt`, `hSC`, `hRt` [J] (VCPU-free statements `JAtZ` proves natively). -/
theorem vcpu_enter_boundL {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
    {ar : machine.Arch A} {V X U : Set U64} {th : TypedHeap} {H : P1.Heap} {Cs Ac : Set U64}
    (hA : P0.ArchTotal ar) (Ly : JVLay V th U)
    {s : S} (Da : DetAtB st V th (fun _ => U) s) (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A)
    {t : U64} (ht : th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (Bk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s)
    (hHk : P1.HeapOK H) (hVH : ∀ v ∈ V, H v = some (.other 15))
    (hTt : ∀ y, th y = some .tcb → y ∈ P1.Heap.tcbs H)
    (hSC : Sched.SlotCapW th (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H))
    (hRt : ¬ P1.BlockedR (L.mem s (P1.stA t))) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ :=
  vcpu_enter_boundK hA Ly.detPl Da E R a ht hv0 (Ly.hvi E ht hv0) Bk hTt hSC (vcpuOm_of_heap hHk hVH)
    (fun _ hn => hn) hRt

end

end Fl4Proofs.P3
