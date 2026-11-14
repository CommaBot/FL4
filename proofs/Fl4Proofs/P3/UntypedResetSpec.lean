/-
P3 (DESIGN.md §9), untyped: the spec side of the reset. `reset_untyped_cap`
is nondeterministic (its preemption points, for `Z = Unit`, may or may not
preempt), so it is described by what holds of every outcome with no failure
(`NSat`) and by the existence of an outcome (`NHas`).

* the machine operations (`freeMemory`, `clearMemory`) on aligned ranges
  do not fail and change only the machine state;
* `delete_objects` empties the region of the heap (`detype`);
* `preemption_point` can always return without preempting, the state
  unchanged (`pp_ok`).
-/
import Fl4Proofs.P3.UntypedReset
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## Outcomes of nondeterministic computations -/

section
open Fl4Spec
variable {σ α β ε : Type}

/-- No failure from `s`, and every outcome satisfies `P`. -/
def NSat (m : NonDet σ α) (s : σ) (P : α × σ → Prop) : Prop := ¬ (m s).2 ∧ ∀ x ∈ (m s).1, P x
/-- Some outcome from `s` satisfies `P`. -/
def NHas (m : NonDet σ α) (s : σ) (P : α × σ → Prop) : Prop := ∃ x ∈ (m s).1, P x

theorem NSat.mono {m : NonDet σ α} {s : σ} {P Q : α × σ → Prop} (h : NSat m s P) (hq : ∀ x, P x → Q x) :
    NSat m s Q := ⟨h.1, fun x hx => hq x (h.2 x hx)⟩
theorem NHas.mono {m : NonDet σ α} {s : σ} {P Q : α × σ → Prop} (h : NHas m s P) (hq : ∀ x, P x → Q x) :
    NHas m s Q := by obtain ⟨x, hx, h⟩ := h; exact ⟨x, hx, hq x h⟩

theorem nsat_bind {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {P : β × σ → Prop}
    (h : NSat m s (fun x => NSat (f x.1) x.2 P)) : NSat (m >>= f) s P := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · show ¬ ((m s).2 ∨ ∃ x ∈ (m s).1, (f x.1 x.2).2)
    rintro (e | ⟨x, hx, e⟩)
    · exact h1 e
    · exact (h2 x hx).1 e
  · rintro r ⟨x, hx, hr⟩; exact (h2 x hx).2 r hr

theorem nhas_bind {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {P : β × σ → Prop}
    (h : NHas m s (fun x => NHas (f x.1) x.2 P)) : NHas (m >>= f) s P := by
  obtain ⟨x, hx, r, hr, hP⟩ := h; exact ⟨r, ⟨x, hx, hr⟩, hP⟩

theorem nsat_bind' {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {P : β × σ → Prop}
    (h : NSat m s (fun x => NSat (f x.1) x.2 P)) : NSat (NonDet.bind m f) s P := nsat_bind h
theorem nhas_bind' {m : NonDet σ α} {f : α → NonDet σ β} {s : σ} {P : β × σ → Prop}
    (h : NHas m s (fun x => NHas (f x.1) x.2 P)) : NHas (NonDet.bind m f) s P := nhas_bind h

theorem nsat_det {m : NonDet σ α} {s s' : σ} {a : α} {P : α × σ → Prop} (h : m s = ({(a, s')}, False))
    (hP : P (a, s')) : NSat m s P := by
  rw [NSat, h]; exact ⟨id, fun x hx => by rw [Set.mem_singleton_iff.1 hx]; exact hP⟩
theorem nhas_det {m : NonDet σ α} {s s' : σ} {a : α} {P : α × σ → Prop} (h : m s = ({(a, s')}, False))
    (hP : P (a, s')) : NHas m s P := by
  rw [NHas, h]; exact ⟨_, rfl, hP⟩

theorem nsat_pure {a : α} {s : σ} {P : α × σ → Prop} (hP : P (a, s)) : NSat (NonDet.pure a) s P :=
  nsat_det rfl hP
theorem nhas_pure {a : α} {s : σ} {P : α × σ → Prop} (hP : P (a, s)) : NHas (NonDet.pure a) s P :=
  nhas_det rfl hP

/-- The continuation of an exception-monad bind. -/
def ECont (f : α → NonDetE σ ε β) (Q : (α → NonDet σ (Except ε β)) → Prop) : Prop :=
  Q fun a => (f a).run

theorem nsatE_bind {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ} {P : Except ε β × σ → Prop}
    (h : NSat m.run s (fun x => match x.1 with
      | .ok a => NSat (f a).run x.2 P
      | .error e => P (.error e, x.2))) : NSat (m >>= f).run s P := by
  rw [ExceptT.run_bind]
  apply nsat_bind
  refine ⟨h.1, fun x hx => ?_⟩
  have := h.2 x hx
  rcases x with ⟨e | a, s1⟩
  · exact nsat_det rfl this
  · exact this

theorem nhasE_bind {m : NonDetE σ ε α} {f : α → NonDetE σ ε β} {s : σ} {P : Except ε β × σ → Prop}
    (h : NHas m.run s (fun x => match x.1 with
      | .ok a => NHas (f a).run x.2 P
      | .error e => P (.error e, x.2))) : NHas (m >>= f).run s P := by
  rw [ExceptT.run_bind]
  apply nhas_bind
  obtain ⟨x, hx, h⟩ := h
  refine ⟨x, hx, ?_⟩
  rcases x with ⟨e | a, s1⟩
  · exact nhas_det rfl h
  · exact h

theorem liftE_run (m : NonDet σ α) : (NonDetE.liftE (ε := ε) m).run = (m >>= fun a => NonDet.pure (.ok a)) := by
  unfold NonDetE.liftE; rw [ExceptT.run_lift]; rfl

theorem nsat_liftE {m : NonDet σ α} {s : σ} {P : Except ε α × σ → Prop} (h : NSat m s (fun x => P (.ok x.1, x.2))) :
    NSat (NonDetE.liftE (ε := ε) m).run s P := by
  rw [liftE_run]; exact nsat_bind (h.mono fun x hx => nsat_pure hx)
theorem nhas_liftE {m : NonDet σ α} {s : σ} {P : Except ε α × σ → Prop} (h : NHas m s (fun x => P (.ok x.1, x.2))) :
    NHas (NonDetE.liftE (ε := ε) m).run s P := by
  rw [liftE_run]; exact nhas_bind (h.mono fun x hx => nhas_pure hx)

theorem nsatE_pure {a : α} {s : σ} {P : Except ε α × σ → Prop} (hP : P (.ok a, s)) :
    NSat (pure a : NonDetE σ ε α).run s P := nsat_det rfl hP
theorem nhasE_pure {a : α} {s : σ} {P : Except ε α × σ → Prop} (hP : P (.ok a, s)) :
    NHas (pure a : NonDetE σ ε α).run s P := nhas_det rfl hP

end

/-! ## Machine operations -/

section
open Fl4Spec

theorem and7_iff (a : Word) : a &&& mask 3 = 0 ↔ a.toNat % 8 = 0 := by
  have hm : (mask 3 : BitVec 64) = 7#64 := rfl
  rw [hm]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and] at this
    have e : (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and]
    have e : (7#64 : BitVec 64).toNat = 2 ^ 3 - 1 := rfl
    rw [e, Nat.and_two_pow_sub_one_eq_mod]
    simpa using h

theorem storeWord_nsat {q : Word} (hq : q &&& mask 3 = 0) (w : Word) (ms : MachineState) :
    NSat (storeWord q w) ms (fun _ => True) ∧ NHas (storeWord q w) ms (fun _ => True) := by
  have ha : NonDet.assert (σ := MachineState) (q &&& mask 3 = 0) ms = ({((), ms)}, False) := by
    simp [NonDet.assert, hq]
  unfold storeWord
  exact ⟨nsat_bind (nsat_det ha (nsat_det rfl trivial)), nhas_bind (nhas_det ha (nhas_det rfl trivial))⟩

theorem mapMx_nsat {α β : Type} {S : Type} (f : α → NonDet S β) (L : List α)
    (hf : ∀ a ∈ L, ∀ s, NSat (f a) s (fun _ => True) ∧ NHas (f a) s (fun _ => True)) (s : S) :
    NSat (NonDet.mapMx f L) s (fun _ => True) ∧ NHas (NonDet.mapMx f L) s (fun _ => True) := by
  induction L generalizing s with
  | nil => exact ⟨nsat_pure trivial, nhas_pure trivial⟩
  | cons a tl ih =>
    have h1 := hf a (List.mem_cons_self ..) s
    have ih' := fun s => ih (fun b hb => hf b (List.mem_cons_of_mem _ hb)) s
    refine ⟨nsat_bind' (h1.1.mono fun x _ => (ih' x.2).1), ?_⟩
    obtain ⟨x, hx, -⟩ := h1.2
    exact nhas_bind' ⟨x, hx, (ih' x.2).2⟩

theorem uptoEnumStep8_al {a c : Word} (ha : a.toNat % 8 = 0) :
    ∀ q ∈ uptoEnumStep a (a + BitVec.ofNat 64 wordSize) c, q &&& mask 3 = 0 := by
  intro q hq
  unfold uptoEnumStep at hq
  split_ifs at hq
  · simp at hq
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hq
    rw [and7_iff]
    have e : a + BitVec.ofNat 64 wordSize - a = 8#64 := by
      rw [show wordSize = 8 from rfl]; bv_omega
    rw [e, BitVec.toNat_add, BitVec.toNat_mul]
    have : (8#64 : BitVec 64).toNat = 8 := rfl
    rw [this]; omega

/-- A machine operation over the words of an aligned range. -/
theorem clear_nsat {a c : Word} (ha : a.toNat % 8 = 0) (ms : MachineState) :
    NSat (NonDet.mapMx (fun p => storeWord p 0) (uptoEnumStep a (a + BitVec.ofNat 64 wordSize) c)) ms
      (fun _ => True) ∧
    NHas (NonDet.mapMx (fun p => storeWord p 0) (uptoEnumStep a (a + BitVec.ofNat 64 wordSize) c)) ms
      (fun _ => True) :=
  mapMx_nsat _ _ (fun q hq s => storeWord_nsat (uptoEnumStep8_al ha q hq) 0 s) ms

/-- The parts of the state the CSpace relations read. -/
def KSame {Z : Type} (σ σ' : State Z) : Prop :=
  σ'.kheap = σ.kheap ∧ σ'.cdt = σ.cdt ∧ σ'.isOriginalCap = σ.isOriginalCap

theorem KSame.refl {Z : Type} (σ : State Z) : KSame σ σ := ⟨rfl, rfl, rfl⟩
theorem KSame.trans {Z : Type} {σ1 σ2 σ3 : State Z} (h1 : KSame σ1 σ2) (h2 : KSame σ2 σ3) : KSame σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem doMachineOp_nsat {Z α : Type} {mop : NonDet MachineState α} (σ : State Z)
    (h : NSat mop σ.machineState (fun _ => True) ∧ NHas mop σ.machineState (fun _ => True)) :
    NSat (doMachineOp mop) σ (fun y => KSame σ y.2) ∧ NHas (doMachineOp mop) σ (fun y => KSame σ y.2) := by
  unfold doMachineOp
  refine ⟨nsat_bind (nsat_det rfl (nsat_bind ⟨h.1.1, ?_⟩)), nhas_bind (nhas_det rfl (nhas_bind ?_))⟩
  · rintro ⟨⟨r, ms'⟩, s1⟩ ⟨-, rfl⟩
    exact nsat_bind (nsat_det rfl (nsat_det rfl ⟨rfl, rfl, rfl⟩))
  · obtain ⟨⟨r, ms'⟩, hx, -⟩ := h.2
    exact ⟨((r, ms'), σ), ⟨hx, rfl⟩, nhas_bind (nhas_det rfl (nhas_det rfl ⟨rfl, rfl, rfl⟩))⟩

theorem clearMemory_nsat {Z : Type} {a : Word} (ha : a.toNat % 8 = 0) (n : Nat) (σ : State Z) :
    NSat (doMachineOp (clearMemory a n)) σ (fun y => KSame σ y.2) ∧
      NHas (doMachineOp (clearMemory a n)) σ (fun y => KSame σ y.2) :=
  doMachineOp_nsat σ (clear_nsat ha _)

theorem freeMemory_nsat {Z : Type} {a : Word} (ha : a.toNat % 8 = 0) (n : Nat) (σ : State Z) :
    NSat (doMachineOp (freeMemory a n)) σ (fun y => KSame σ y.2) ∧
      NHas (doMachineOp (freeMemory a n)) σ (fun y => KSame σ y.2) :=
  doMachineOp_nsat σ (clear_nsat ha _)

/-- `delete_objects`: the heap without the region, the CDT unchanged. -/
theorem deleteObjects_nsat {Z : Type} [StateExt Z] {a : Word} (ha : a.toNat % 8 = 0) (n : Nat) (σ : State Z) :
    let P := fun (y : Unit × State Z) => y.2.kheap = (detype {x | a ≤ x ∧ x ≤ a + 2 ^ n - 1} σ).kheap ∧
      y.2.cdt = σ.cdt ∧ y.2.isOriginalCap = σ.isOriginalCap
    NSat (deleteObjects (Z := Z) a n) σ P ∧ NHas (deleteObjects (Z := Z) a n) σ P := by
  intro P
  obtain ⟨h1, h2⟩ := freeMemory_nsat (Z := Z) ha n σ
  unfold deleteObjects
  refine ⟨nsat_bind (h1.mono fun x hx => nsat_det rfl ?_), nhas_bind (h2.mono fun x hx => nhas_det rfl ?_)⟩ <;>
  · obtain ⟨k1, k2, k3⟩ := hx
    refine ⟨?_, k2, k3⟩
    simp only [detype, k1]
    funext y; split <;> simp_all

end

/-! ## The preemption point, for `Z = Unit` -/

section
open Fl4Spec

/-- **The spec's preemption point can always return without preempting**,
the state unchanged (for `Z = Unit`, `work_units_limit_reached` is any
boolean and the extended operations do nothing). -/
theorem pp_ok (σ : State Unit) : NHas (preemptionPoint (Z := Unit)).run σ (fun y => y = (.ok (), σ)) := by
  unfold preemptionPoint
  apply nhasE_bind
  apply nhas_liftE
  unfold doExtendedOp
  refine nhas_bind (nhas_det rfl ?_)
  refine nhas_bind ⟨(((), σ), σ), ⟨rfl, rfl⟩, nhas_det rfl ?_⟩
  show NHas (orChoiceE _ _ _).run { σ with exst := σ.exst } _
  unfold orChoiceE
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det rfl ?_
  apply nhasE_bind
  apply nhas_liftE
  refine ⟨((false, σ), σ), ⟨⟨trivial, rfl⟩, rfl⟩, ?_⟩
  exact nhasE_pure rfl

end

/-! ## `reset_untyped_cap` -/

section
open Fl4Spec

theorem nhas_congr {σ α : Type} {m m' : NonDet σ α} {s : σ} {P : α × σ → Prop} (h : m s = m' s) :
    NHas m s P ↔ NHas m' s P := by unfold NHas; rw [h]
theorem nsat_congr {σ α : Type} {m m' : NonDet σ α} {s : σ} {P : α × σ → Prop} (h : m s = m' s) :
    NSat m s P ↔ NSat m' s P := by unfold NSat; rw [h]

theorem KSame.setCnodeSlot {Z : Type} {σ σ' : State Z} (h : KSame σ σ') (pb : ObjRef) (r : Nat) (cs : CnodeContents)
    (idx : List Bool) (a : Cap) : KSame (setCnodeSlot σ pb r cs idx a) (setCnodeSlot σ' pb r cs idx a) := by
  refine ⟨?_, h.2.1, h.2.2⟩
  show Function.update σ'.kheap pb _ = Function.update σ.kheap pb _
  rw [h.1]

/-- The chunks `k, k - 1, .., 0`. -/
def chunks (k : Nat) : List Nat := (List.range (k + 1)).reverse

theorem chunks_succ (k : Nat) : chunks (k + 1) = (k + 1) :: chunks k := by
  unfold chunks; rw [List.range_succ, List.reverse_append]; rfl

theorem filter_range_lt (c fi N : Nat) (hc : 0 < c) :
    (List.range N).filter (fun i => decide (i * c < fi)) = List.range (min N ((fi + c - 1) / c)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [List.range_succ, List.filter_append, ih]
    have key : N * c < fi ↔ N + 1 ≤ (fi + c - 1) / c := by
      rw [Nat.le_div_iff_mul_le hc, Nat.add_mul, Nat.one_mul]; omega
    by_cases h : N * c < fi
    · have h' := key.1 h
      rw [List.filter_cons_of_pos (by simpa using h), List.filter_nil,
        show min N ((fi + c - 1) / c) = N by omega, show min (N + 1) ((fi + c - 1) / c) = N + 1 by omega,
        ← List.range_succ]
    · have h' : ¬ N + 1 ≤ (fi + c - 1) / c := fun e => h (key.2 e)
      rw [List.filter_cons_of_neg (by simpa using h), List.filter_nil, List.append_nil]
      congr 1; omega

/-- The spec's chunk list, for a free index `0 < fi ≤ 2 ^ sz`. -/
theorem chunk_list (rcb sz fi : Nat) (hrs : rcb ≤ sz) (hfi0 : 0 < fi) (hfi : fi ≤ 2 ^ sz) :
    ((List.range (2 ^ (sz - rcb))).filter (fun i => decide (i * 2 ^ rcb < fi))).reverse =
      chunks ((fi - 1) / 2 ^ rcb) := by
  have hc : 0 < 2 ^ rcb := Nat.two_pow_pos _
  have hN : 2 ^ (sz - rcb) * 2 ^ rcb = 2 ^ sz := by rw [← Nat.pow_add]; congr 1; omega
  rw [filter_range_lt _ _ _ hc]
  unfold chunks
  congr 2
  have e1 : (fi - 1) / 2 ^ rcb + 1 = (fi + 2 ^ rcb - 1) / 2 ^ rcb := by
    rw [show fi + 2 ^ rcb - 1 = (fi - 1) + 1 * 2 ^ rcb by omega, Nat.add_mul_div_right _ _ hc]
  rw [e1]
  have : (fi + 2 ^ rcb - 1) / 2 ^ rcb ≤ 2 ^ (sz - rcb) := by
    rw [Nat.div_le_iff_le_mul_add_pred hc, Nat.mul_comm, hN]; omega
  omega

section Reset
variable (dev : Bool) (pu : ObjRef) (sz : Nat) (pb : ObjRef) (r : Nat) (idx : List Bool)

/-- One chunk of the reset (zero it, lower the free index, preemption point). -/
def chunkF (i : Nat) : PMonad Unit Unit := do
  NonDetE.liftE (doMachineOp (clearMemory (pu + (BitVec.ofNat 64 i <<< resetChunkBits)) (2 ^ resetChunkBits)))
  NonDetE.liftE (setCap (.untypedCap dev pu sz (i * 2 ^ resetChunkBits)) (pb, idx))
  preemptionPoint

/-- The slot's CNode is there. -/
def HasCN (σ : State Unit) : Prop := ∃ cs, σ.kheap pb = some (.cnode r cs) ∧ wellFormedCnodeN r cs

/-- Outcome `e`, the CSpace parts of the state those of `K`. -/
def TopP (e : Except Unit Unit) (K : State Unit) : Except Unit Unit × State Unit → Prop :=
  fun y => y.1 = e ∧ KSame K y.2

/-- The rest after the chunks. -/
def RestQ (e : Except Unit Unit) (K : State Unit) : Except Unit Unit × State Unit → Prop := fun y =>
  match y.1 with
  | .ok _ => NHas (NonDetE.liftE (archPostResetUntyped (Z := Unit) dev sz)).run y.2 (TopP e K)
  | .error e' => TopP e K (.error e', y.2)

/-- Running chunks `k, .., 0` from `σk` to an outcome is an outcome of the
whole reset from `σ`. -/
def RCont (σ : State Unit) (k : Nat) (σk : State Unit) : Prop :=
  ∀ e K, NHas (NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks k)).run σk (RestQ dev sz e K) →
    NHas (resetUntypedCap (Z := Unit) (pb, idx)).run σ (TopP e K)

variable {dev pu sz pb r idx}

theorem pu_al {pu : ObjRef} (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (i : Nat) :
    (pu + (BitVec.ofNat 64 i <<< resetChunkBits)).toNat % 8 = 0 := by
  rw [hrcb, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  omega

/-- The preemption point (opaque): it does not fail and keeps the CSpace
parts of the state. -/
def PPFrame : Prop := ∀ σ1 : State Unit, NSat (preemptionPoint (Z := Unit)).run σ1 (fun y => KSame σ1 y.2)

theorem chunk_nsat (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    (hpp : PPFrame) (i : Nat) (σ : State Unit) (hc : HasCN pb r σ) :
    NSat (chunkF dev pu sz pb idx i).run σ (fun y => HasCN pb r y.2) := by
  obtain ⟨cs, hk, hwf⟩ := hc
  unfold chunkF
  apply nsatE_bind
  apply nsat_liftE
  refine (clearMemory_nsat (pu_al hrcb hp8 i) _ σ).1.mono (fun y hy => ?_)
  show NSat (_ >>= fun _ => preemptionPoint).run y.2 _
  apply nsatE_bind
  apply nsat_liftE
  refine nsat_det (setCap_cnode _ (by rw [hy.1]; exact hk) hwf hidx) ?_
  show NSat (preemptionPoint (Z := Unit)).run _ _
  exact (hpp _).mono (fun z hz => ⟨Function.update cs idx (some (.untypedCap dev pu sz (i * 2 ^ resetChunkBits))),
    by rw [hz.1]; simp [setCnodeSlot], wf_update _ hwf hidx⟩)

theorem chunks_nsat (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    (hpp : PPFrame) (L : List Nat) (σ : State Unit) (hc : HasCN pb r σ) :
    NSat (NonDetE.mapMEx (chunkF dev pu sz pb idx) L).run σ (fun _ => True) := by
  induction L generalizing σ with
  | nil => exact nsatE_pure trivial
  | cons a L ih =>
    show NSat ((chunkF dev pu sz pb idx a) >>= fun _ => NonDetE.mapMEx (chunkF dev pu sz pb idx) L).run σ _
    apply nsatE_bind
    refine (chunk_nsat hrcb hp8 hidx hpp a σ hc).mono (fun y hy => ?_)
    rcases y with ⟨e | u, s1⟩
    · trivial
    · exact ih s1 hy

/-- An outcome `e` of a chunk, when the preemption point has one. -/
theorem chunk_has (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    {e : Except Unit Unit} (hpp : ∀ σ1 : State Unit, NHas (preemptionPoint (Z := Unit)).run σ1
      (fun y => y.1 = e ∧ KSame σ1 y.2))
    (i : Nat) (σ : State Unit) {cs : CnodeContents} (hk : σ.kheap pb = some (.cnode r cs))
    (hwf : wellFormedCnodeN r cs) :
    NHas (chunkF dev pu sz pb idx i).run σ (fun y => y.1 = e ∧
      KSame (setCnodeSlot σ pb r cs idx (.untypedCap dev pu sz (i * 2 ^ resetChunkBits))) y.2) := by
  unfold chunkF
  apply nhasE_bind
  apply nhas_liftE
  refine (clearMemory_nsat (pu_al hrcb hp8 i) _ σ).2.mono (fun y hy => ?_)
  show NHas (_ >>= fun _ => preemptionPoint).run y.2 _
  apply nhasE_bind
  apply nhas_liftE
  refine nhas_det (setCap_cnode _ (by rw [hy.1]; exact hk) hwf hidx) ?_
  show NHas (preemptionPoint (Z := Unit)).run _ _
  exact (hpp _).mono (fun z hz => ⟨hz.1, (KSame.setCnodeSlot hy _ _ _ _ _).trans hz.2⟩)

theorem pp_ok' : ∀ σ1 : State Unit, NHas (preemptionPoint (Z := Unit)).run σ1
    (fun y => y.1 = .ok () ∧ KSame σ1 y.2) :=
  fun σ1 => (pp_ok σ1).mono (fun y hy => by rw [hy]; exact ⟨rfl, KSame.refl _⟩)

theorem chunks_cons (k : Nat) : chunks k = k :: (List.range k).reverse := by
  unfold chunks; rw [List.range_succ, List.reverse_append]; rfl

/-- The chunk `k + 1` without preemption: the continuation from the state
after it. -/
theorem RCont.step (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    {σ σk : State Unit} {k : Nat} (hc : RCont dev pu sz pb idx σ (k + 1) σk) {cs : CnodeContents}
    (hk : σk.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) :
    ∃ σn, KSame (setCnodeSlot σk pb r cs idx (.untypedCap dev pu sz ((k + 1) * 2 ^ resetChunkBits))) σn ∧
      RCont dev pu sz pb idx σ k σn := by
  obtain ⟨y, hy, hy1, hy2⟩ := chunk_has (dev := dev) (sz := sz) hrcb hp8 hidx pp_ok' (k + 1) σk hk hwf
  refine ⟨y.2, hy2, fun e K h => hc e K ?_⟩
  rw [chunks_succ]
  show NHas ((chunkF dev pu sz pb idx (k + 1)) >>= fun _ =>
    NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks k)).run σk _
  apply nhasE_bind
  refine ⟨y, hy, ?_⟩
  rcases y with ⟨e1, s1⟩
  simp only at hy1; subst hy1; exact h

/-- The last chunk, without preemption: the reset's `Ok` outcome. -/
theorem RCont.done (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    {σ σk : State Unit} (hc : RCont dev pu sz pb idx σ 0 σk) {cs : CnodeContents}
    (hk : σk.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) :
    NHas (resetUntypedCap (Z := Unit) (pb, idx)).run σ
      (TopP (.ok ()) (setCnodeSlot σk pb r cs idx (.untypedCap dev pu sz (0 * 2 ^ resetChunkBits)))) := by
  obtain ⟨y, hy, hy1, hy2⟩ := chunk_has (dev := dev) (sz := sz) hrcb hp8 hidx pp_ok' 0 σk hk hwf
  apply hc
  show NHas ((chunkF dev pu sz pb idx 0) >>= fun _ => NonDetE.mapMEx (chunkF dev pu sz pb idx) []).run σk _
  apply nhasE_bind
  refine ⟨y, hy, ?_⟩
  rcases y with ⟨e1, s1⟩
  simp only at hy1; subst hy1
  apply nhasE_pure
  apply nhas_liftE
  exact nhas_det rfl ⟨rfl, hy2⟩

/-- A chunk whose preemption point preempts: the reset's error outcome. -/
theorem RCont.preempt (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    (hppE : ∀ σ1 : State Unit, NHas (preemptionPoint (Z := Unit)).run σ1 (fun y => y.1 = .error () ∧ KSame σ1 y.2))
    {σ σk : State Unit} {k : Nat} (hc : RCont dev pu sz pb idx σ k σk) {cs : CnodeContents}
    (hk : σk.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) :
    NHas (resetUntypedCap (Z := Unit) (pb, idx)).run σ
      (TopP (.error ()) (setCnodeSlot σk pb r cs idx (.untypedCap dev pu sz (k * 2 ^ resetChunkBits)))) := by
  obtain ⟨y, hy, hy1, hy2⟩ := chunk_has (dev := dev) (sz := sz) hrcb hp8 hidx hppE k σk hk hwf
  apply hc
  rw [chunks_cons]
  show NHas ((chunkF dev pu sz pb idx k) >>= fun _ =>
    NonDetE.mapMEx (chunkF dev pu sz pb idx) (List.range k).reverse).run σk _
  apply nhasE_bind
  refine ⟨y, hy, ?_⟩
  rcases y with ⟨e1, s1⟩
  simp only at hy1; subst hy1
  exact ⟨rfl, hy2⟩

/-- The region `delete_objects` empties. -/
abbrev regionSet (pu : ObjRef) (sz : Nat) : Set ObjRef := {x | pu ≤ x ∧ x ≤ pu + 2 ^ sz - 1}

theorem detype_hasCN {σ σD : State Unit} {cs : CnodeContents} (hk : σ.kheap pb = some (.cnode r cs))
    (hpb : pb ∉ regionSet pu sz) (hD : KSame (detype (regionSet pu sz) σ) σD) : σD.kheap pb = some (.cnode r cs) := by
  rw [hD.1]; simp only [detype]; rw [if_neg hpb]; exact hk

section Top
variable {σ : State Unit} {fi : Nat} {cs : CnodeContents}
  (hk : σ.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
  (hg : getCap (Z := Unit) (pb, idx) σ = ({(.untypedCap dev pu sz fi, σ)}, False)) (hfi : fi ≠ 0)
  (hp8 : pu.toNat % 8 = 0) (hpb : pb ∉ regionSet pu sz) (hrcb : resetChunkBits = 16)
include hk hwf hidx hg hfi hp8 hpb hrcb

theorem top_get :
    (NonDetE.liftE (ε := Unit) (getCap (Z := Unit) (pb, idx))).run σ =
      ({(.ok (.untypedCap dev pu sz fi), σ)}, False) := run_liftE hg

/-- **The spec's reset does not fail**, for an untyped cap with `fi ≠ 0`. -/
theorem reset_nsat (hpp : PPFrame) :
    NSat (resetUntypedCap (Z := Unit) (pb, idx)).run σ (fun _ => True) := by
  unfold resetUntypedCap
  apply nsatE_bind
  refine nsat_det (top_get hk hwf hidx hg hfi hp8 hpb hrcb) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nsatE_bind
  apply nsat_liftE
  refine (deleteObjects_nsat hp8 sz σ).1.mono (fun y hy => ?_)
  have hD : KSame (detype (regionSet pu sz) σ) y.2 := hy
  have hk' := detype_hasCN hk hpb hD
  dsimp only
  split_ifs with hs
  · apply nsatE_bind
    apply nsat_liftE
    unfold NonDet.unless
    split_ifs with hdv
    · apply nsat_bind
      refine nsat_pure (nsat_det (setCap_cnode _ hk' hwf hidx) ?_)
      exact nsat_liftE (nsat_det rfl trivial)
    · apply nsat_bind
      refine (clearMemory_nsat hp8 _ y.2).1.mono (fun z hz => nsat_det (setCap_cnode _ (by rw [hz.1]; exact hk') hwf hidx) ?_)
      exact nsat_liftE (nsat_det rfl trivial)
  · apply nsatE_bind
    refine (chunks_nsat hrcb hp8 hidx hpp _ y.2 ⟨cs, hk', hwf⟩).mono (fun z _ => ?_)
    rcases z with ⟨e | u, s1⟩
    · trivial
    · exact nsat_liftE (nsat_det rfl trivial)

/-- The small or device case: the outcome with the free index 0. -/
theorem reset_small (hs : dev = true ∨ sz < resetChunkBits) :
    ∃ σD, KSame (detype (regionSet pu sz) σ) σD ∧
      NHas (resetUntypedCap (Z := Unit) (pb, idx)).run σ (TopP (.ok ()) (setCnodeSlot σD pb r cs idx (.untypedCap dev pu sz 0))) := by
  obtain ⟨y, hy, hD⟩ := (deleteObjects_nsat (Z := Unit) hp8 sz σ).2
  have hD' : KSame (detype (regionSet pu sz) σ) y.2 := hD
  have hk' := detype_hasCN hk hpb hD'
  refine ⟨y.2, hD', ?_⟩
  unfold resetUntypedCap
  apply nhasE_bind
  refine nhas_det (top_get hk hwf hidx hg hfi hp8 hpb hrcb) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nhasE_bind
  apply nhas_liftE
  refine ⟨y, hy, ?_⟩
  dsimp only
  rw [if_pos (by simpa using hs)]
  apply nhasE_bind
  apply nhas_liftE
  unfold NonDet.unless
  split_ifs with hdv
  · apply nhas_bind
    refine nhas_pure (nhas_det (setCap_cnode _ hk' hwf hidx) ?_)
    exact nhas_liftE (nhas_det rfl ⟨rfl, KSame.refl _⟩)
  · apply nhas_bind
    obtain ⟨z, hz, hz1⟩ := (clearMemory_nsat hp8 (2 ^ sz) y.2).2
    refine ⟨z, hz, nhas_det (setCap_cnode _ (by rw [hz1.1]; exact hk') hwf hidx) ?_⟩
    exact nhas_liftE (nhas_det rfl ⟨rfl, KSame.setCnodeSlot hz1 _ _ _ _ _⟩)

/-- The chunked case: the continuation from the state after `delete_objects`. -/
theorem reset_init (hs : ¬ (dev = true ∨ sz < resetChunkBits)) (hfs : fi ≤ 2 ^ sz) :
    ∃ σD, KSame (detype (regionSet pu sz) σ) σD ∧
      RCont dev pu sz pb idx σ ((fi - 1) / 2 ^ resetChunkBits) σD := by
  obtain ⟨y, hy, hD⟩ := (deleteObjects_nsat (Z := Unit) hp8 sz σ).2
  refine ⟨y.2, hD, fun e K h => ?_⟩
  unfold resetUntypedCap
  apply nhasE_bind
  refine nhas_det (top_get hk hwf hidx hg hfi hp8 hpb hrcb) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nhasE_bind
  apply nhas_liftE
  refine ⟨y, hy, ?_⟩
  dsimp only
  rw [if_neg (by simpa using hs)]
  apply nhasE_bind
  have hl := chunk_list resetChunkBits sz fi (by omega) (by omega) hfs
  convert h using 4
  all_goals first
    | rfl
    | exact Iff.rfl
    | (rename_i x; unfold RestQ; rcases x with ⟨_ | _, _⟩ <;> exact Iff.rfl)
    | (rw [← hl]; congr 1; try (apply List.filter_congr; intro i _; simp [Fl4Spec.freeIndexOf]))

end Top

/-! ## Every `Ok` outcome of the reset has the same CSpace state -/

section Canon
variable {σ0 : State Unit} {cs : CnodeContents}

/-- The heap after the reset's `set_cap`s: the region removed, the slot
holding `a`. -/
def KHc (σ0 : State Unit) (pu : ObjRef) (sz : Nat) (pb : ObjRef) (r : Nat) (cs : CnodeContents) (idx : List Bool)
    (a : Cap) : ObjRef → Option KernelObject :=
  (setCnodeSlot (detype (regionSet pu sz) σ0) pb r cs idx a).kheap

/-- During the reset: the CDT and original bits of `σ0`, the heap after
`delete_objects`, possibly with the slot rewritten. -/
def RInv (σ0 : State Unit) (pu : ObjRef) (sz : Nat) (pb : ObjRef) (r : Nat) (cs : CnodeContents) (idx : List Bool)
    (σ1 : State Unit) : Prop :=
  σ1.cdt = σ0.cdt ∧ σ1.isOriginalCap = σ0.isOriginalCap ∧
    (σ1.kheap = (detype (regionSet pu sz) σ0).kheap ∨ ∃ a, σ1.kheap = KHc σ0 pu sz pb r cs idx a)

theorem RInv.cn (hk : σ0.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    (hpb : pb ∉ regionSet pu sz) {σ1 : State Unit} (h : RInv σ0 pu sz pb r cs idx σ1) :
    ∃ cs', σ1.kheap pb = some (.cnode r cs') ∧ wellFormedCnodeN r cs' ∧
      ∀ a, Function.update σ1.kheap pb (some (.cnode r (Function.update cs' idx (some a)))) = KHc σ0 pu sz pb r cs idx a := by
  have hD : (detype (regionSet pu sz) σ0).kheap pb = some (.cnode r cs) := by simp only [detype]; rw [if_neg hpb]; exact hk
  rcases h.2.2 with h1 | ⟨a0, h1⟩
  · refine ⟨cs, by rw [h1, hD], hwf, fun a => ?_⟩
    rw [h1]; rfl
  · refine ⟨Function.update cs idx (some a0), by rw [h1]; simp [KHc, setCnodeSlot], wf_update _ hwf hidx, fun a => ?_⟩
    rw [h1]
    unfold KHc setCnodeSlot
    simp only [Function.update_idem]

theorem chunk_nsat_canon (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    (hpp : PPFrame) (hk : σ0.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs)
    (hpb : pb ∉ regionSet pu sz) (i : Nat) (σ1 : State Unit) (h : RInv σ0 pu sz pb r cs idx σ1) :
    NSat (chunkF dev pu sz pb idx i).run σ1 (fun y => y.2.cdt = σ0.cdt ∧ y.2.isOriginalCap = σ0.isOriginalCap ∧
      y.2.kheap = KHc σ0 pu sz pb r cs idx (.untypedCap dev pu sz (i * 2 ^ resetChunkBits))) := by
  obtain ⟨cs', hk', hwf', hup⟩ := h.cn hk hwf hidx hpb
  unfold chunkF
  apply nsatE_bind
  apply nsat_liftE
  refine (clearMemory_nsat (pu_al hrcb hp8 i) _ σ1).1.mono (fun y hy => ?_)
  dsimp only
  apply nsatE_bind
  apply nsat_liftE
  refine nsat_det (setCap_cnode _ (by rw [hy.1]; exact hk') hwf' hidx) ?_
  show NSat (preemptionPoint (Z := Unit)).run _ _
  refine (hpp _).mono (fun z hz => ⟨?_, ?_, ?_⟩)
  · rw [hz.2.1]; show y.2.cdt = _; rw [hy.2.1, h.1]
  · rw [hz.2.2]; show y.2.isOriginalCap = _; rw [hy.2.2, h.2.1]
  · rw [hz.1, ← hup]; show Function.update y.2.kheap pb _ = _; rw [hy.1]

theorem chunks_nsat_canon (hrcb : resetChunkBits = 16) (hp8 : pu.toNat % 8 = 0) (hidx : idx.length = r)
    (hpp : PPFrame) (hk : σ0.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs)
    (hpb : pb ∉ regionSet pu sz) (k : Nat) (σ1 : State Unit) (h : RInv σ0 pu sz pb r cs idx σ1) :
    NSat (NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks k)).run σ1 (fun y => y.1 = .ok () →
      KSame (setCnodeSlot (detype (regionSet pu sz) σ0) pb r cs idx (.untypedCap dev pu sz 0)) y.2) := by
  induction k generalizing σ1 with
  | zero =>
    show NSat ((chunkF dev pu sz pb idx 0) >>= fun _ => NonDetE.mapMEx (chunkF dev pu sz pb idx) []).run σ1 _
    apply nsatE_bind
    refine (chunk_nsat_canon hrcb hp8 hidx hpp hk hwf hpb 0 σ1 h).mono (fun y hy => ?_)
    rcases y with ⟨e | u, s1⟩
    · intro h; cases h
    · refine nsatE_pure (fun _ => ⟨?_, hy.1, hy.2.1⟩)
      rw [hy.2.2]; simp [KHc]
  | succ k ih =>
    rw [chunks_succ]
    show NSat ((chunkF dev pu sz pb idx (k + 1)) >>= fun _ =>
      NonDetE.mapMEx (chunkF dev pu sz pb idx) (chunks k)).run σ1 _
    apply nsatE_bind
    refine (chunk_nsat_canon hrcb hp8 hidx hpp hk hwf hpb (k + 1) σ1 h).mono (fun y hy => ?_)
    rcases y with ⟨e | u, s1⟩
    · intro h; cases h
    · exact ih s1 ⟨hy.1, hy.2.1, Or.inr ⟨_, hy.2.2⟩⟩

/-- **Every `Ok` outcome of the spec's reset** has the CSpace state of the
canonical one: the region removed, the slot's free index 0. -/
theorem reset_nsat_ok (hk : σ0.kheap pb = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r)
    {fi : Nat} (hg : getCap (Z := Unit) (pb, idx) σ0 = ({(.untypedCap dev pu sz fi, σ0)}, False)) (hfi : fi ≠ 0)
    (hp8 : pu.toNat % 8 = 0) (hpb : pb ∉ regionSet pu sz) (hrcb : resetChunkBits = 16) (hpp : PPFrame)
    (hfs : fi ≤ 2 ^ sz) :
    NSat (resetUntypedCap (Z := Unit) (pb, idx)).run σ0 (fun y => y.1 = .ok () →
      KSame (setCnodeSlot (detype (regionSet pu sz) σ0) pb r cs idx (.untypedCap dev pu sz 0)) y.2) := by
  unfold resetUntypedCap
  apply nsatE_bind
  refine nsat_det (top_get hk hwf hidx hg hfi hp8 hpb hrcb) ?_
  dsimp only
  simp only [NonDetE.returnOk, ndE_pure_bind, Fl4Spec.bitsOf, Fl4Spec.objRefOf, Fl4Spec.freeIndexOf,
    Fl4Spec.isDeviceUntypedCap, hfi, ↓reduceIte]
  apply nsatE_bind
  apply nsat_liftE
  refine (deleteObjects_nsat hp8 sz σ0).1.mono (fun y hy => ?_)
  have hI0 : RInv σ0 pu sz pb r cs idx y.2 := ⟨hy.2.1, hy.2.2, Or.inl hy.1⟩
  obtain ⟨cs', hk', hwf', hup⟩ := hI0.cn hk hwf hidx hpb
  dsimp only
  split_ifs with hs
  · apply nsatE_bind
    apply nsat_liftE
    unfold NonDet.unless
    have fin : ∀ z : Unit × State Unit, KSame y.2 z.2 → NSat (setCap (Z := Unit) (.untypedCap dev pu sz 0) (pb, idx)) z.2
        (fun w => NSat (NonDetE.liftE (ε := Unit) (archPostResetUntyped (Z := Unit) dev sz)).run w.2
          (fun v => v.1 = .ok () → KSame (setCnodeSlot (detype (regionSet pu sz) σ0) pb r cs idx
            (.untypedCap dev pu sz 0)) v.2)) := by
      intro z hz
      refine nsat_det (setCap_cnode _ (by rw [hz.1]; exact hk') hwf' hidx) ?_
      refine nsat_liftE (nsat_det rfl (fun _ => ⟨?_, ?_, ?_⟩))
      · show Function.update z.2.kheap pb _ = _; rw [hz.1, hup]; rfl
      · show z.2.cdt = σ0.cdt; rw [hz.2.1, hy.2.1]
      · show z.2.isOriginalCap = σ0.isOriginalCap; rw [hz.2.2, hy.2.2]
    split_ifs with hdv
    · exact nsat_bind (nsat_pure (fin ((), y.2) (KSame.refl _)))
    · exact nsat_bind ((clearMemory_nsat hp8 _ y.2).1.mono (fun z hz => fin z hz))
  · apply nsatE_bind
    refine (chunks_nsat_canon hrcb hp8 hidx hpp hk hwf hpb ((fi - 1) / 2 ^ resetChunkBits) y.2 hI0).mono
      (fun z hz => ?_) |> (fun h => by
        have hl := chunk_list resetChunkBits sz fi (by omega) (by omega) hfs
        convert h using 4
        all_goals first
          | rfl
          | (rw [← hl]; congr 1; try (apply List.filter_congr; intro i _; simp [Fl4Spec.freeIndexOf])))
    rcases z with ⟨e | u, s1⟩
    · intro h; cases h
    · exact nsat_liftE (nsat_det rfl (fun _ => hz rfl))

end Canon

end Reset

end

end

end Fl4Proofs.P3
