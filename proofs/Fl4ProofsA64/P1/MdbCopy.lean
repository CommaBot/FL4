/-
P1 (aarch64, gen 50): **`AlikeA` for CNode Copy / Mint's new cap** — the hypothesis `AlikeA nc (capA src)` of gen 47 /
48 / 49's insertion lemmas (`cdt.insert_with_cap.mdbO`, `cdt.insert.mdbO`) discharged from `copied_cap`
(cnode.rs:77–102) for a non-null new cap.

* **`AlN d c`**: `d` is `Null`, or `d` is `AlikeA c` (same key, and for a key cap same class and kind, MdbIns) with
  `c` non-null; `AlN.trans` (a `Null` in the middle forces a `Null` at the end), `AlikeA.trans`,
  **`AlikeA.of_eq`** (same `cap_is_physical`, `ptr`, `cap_size_bits`, constructor: closed by `rfl` on concrete caps).
* **`capability.mask_cap_rights.al`** (capability.rs:360–386: rights bits only), **`objects.update_cap_data.al`**
  (objects.rs:156–183: badge / guard, or `Null`), **`objects.derive_cap.al`** (objects.rs:208–239: frames lose the
  mapping, `Zombie` / `IrqControl` become `Null`, others kept): each result `AlN` its argument.
* **`cnode.copied_cap.al`**: every `Ok (nc, false)` of `copied_cap` has `AlN nc src_cap`; **`AlN.ne`**: with
  `nc ≠ Null` (the decode refuses a `Null` new cap before inserting), `AlikeA nc src_cap`.
* The insertion's other hypothesis on the new cap, `EncWf`: **`capability.mask_cap_rights.wf`** (frame rights from
  `mask_vm_rights`, below 4), **`objects.update_cap_data.wf`** (a `CNode` guard size `data & 63`, guard
  `(data >> 6) & mask` below `2 ^ 58`), **`objects.derive_cap.wf`** (a frame loses asid / vaddr); **`cnode.copied_cap.wf`**:
  for Copy / Mint, every `Ok (nc, b)` has `b = false` (no move) and `EncWf nc` from `EncWf src_cap`.

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbMint
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

namespace W7
namespace R
namespace ST

theorem AlikeA.trans {a b c : capability.Cap} (h1 : AlikeA a b) (h2 : AlikeA b c) : AlikeA a c := by
  refine ⟨h1.1.trans h2.1, fun kc => ?_⟩
  have kb := h2.1.2 kc
  exact ⟨(h1.2 kb).1.trans (h2.2 kc).1, (h1.2 kb).2.trans (h2.2 kc).2⟩

/-- Two caps with the same physical bit, base, size bits and constructor are alike. -/
theorem AlikeA.of_eq {d c : capability.Cap} (h1 : objects.cap_is_physical d = objects.cap_is_physical c)
    (h2 : capability.Cap.ptr d = capability.Cap.ptr c) (h3 : objects.cap_size_bits d = objects.cap_size_bits c)
    (h4 : kindA d = kindA c) (h5 : isUtA d = isUtA c) (h6 : isFrA d = isFrA c) : AlikeA d c := by
  have e1 : physA d = physA c := okinj ((physA_eq d).symm.trans (h1.trans (physA_eq c)))
  have e2 : ptrA d = ptrA c := okinj ((ptrA_eq d).symm.trans (h2.trans (ptrA_eq c)))
  have e3 : sizeA d = sizeA c := okinj ((sizeA_eq d).symm.trans (h3.trans (sizeA_eq c)))
  refine ⟨?_, fun _ => ⟨by unfold clsA; rw [e2, e3], h4⟩⟩
  unfold RngKeyA; rw [e1, h5, h6]

/-- `d` is `Null`, or alike a non-null `c`. -/
def AlN (d c : capability.Cap) : Prop := d = .Null ∨ (AlikeA d c ∧ c ≠ .Null)

theorem AlN.trans {a b c : capability.Cap} (h1 : AlN a b) (h2 : AlN b c) : AlN a c := by
  rcases h1 with e | ⟨h1, hb⟩
  · exact Or.inl e
  · rcases h2 with e | ⟨h2, hc⟩
    · exact absurd e hb
    · exact Or.inr ⟨h1.trans h2, hc⟩

theorem AlN.ne {d c : capability.Cap} (h : AlN d c) (hd : d ≠ .Null) : AlikeA d c := by
  rcases h with e | ⟨h, -⟩
  · exact absurd e hd
  · exact h

set_option hygiene false in
/-- Closes `AlN` of a concrete result against a concrete argument. -/
local macro "aln" : tactic => `(tactic| (
  first
  | exact Or.inl rfl
  | exact Or.inr ⟨AlikeA.refl _, fun e => by cases e⟩
  | exact Or.inr ⟨AlikeA.of_eq rfl rfl rfl rfl rfl rfl, fun e => by cases e⟩))

/-- **`mask_cap_rights` keeps the cap alike.** -/
theorem capability.mask_cap_rights.al (r : capability.Rights) (c : capability.Cap) :
    capability.mask_cap_rights r c ⦃ m => AlN m c ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    cases sd <;> cases rc <;> cases g <;> cases gr <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 (by aln)
  case Notification p b sd rc =>
    cases sd <;> cases rc <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 (by aln)
  case Reply p g =>
    cases g <;> simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte] <;>
      exact (WP.spec_ok _).2 (by aln)
  case Frame p sz rt dv mp ep asd va =>
    simp only [capability.mask_cap_rights]
    exact WP.spec_bind (P0.capability.mask_vm_rights.p0 rt r) fun _ _ => (WP.spec_ok _).2 (by aln)
  all_goals (simp only [capability.mask_cap_rights]; exact (WP.spec_ok _).2 (by aln))

/-- **`update_cap_data` keeps the cap alike or returns `Null`.** -/
theorem objects.update_cap_data.al (pr : Bool) (data : U64) (c : capability.Cap) :
    objects.update_cap_data pr data c ⦃ m => AlN m c ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 (by aln)
    · split <;> exact (WP.spec_ok _).2 (by aln)
  case Notification p b sd rc =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 (by aln)
    · split <;> exact (WP.spec_ok _).2 (by aln)
  case CNode p rd gs g =>
    simp only [objects.update_cap_data]
    refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
    refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
    split
    · exact (WP.spec_ok _).2 (by aln)
    · refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun _ _ => ?_
      exact (WP.spec_ok _).2 (by aln)
  all_goals (simp only [objects.update_cap_data]; exact (WP.spec_ok _).2 (by aln))

set_option hygiene false in
/-- An `Ok` result of `derive_cap` (closes `AlN`). -/
local macro "al_ok" : tactic => `(tactic| (
  refine (WP.spec_ok _).2 fun nc h => ?_
  cases h
  aln))

set_option maxHeartbeats 1000000 in
/-- **`derive_cap` returns a cap alike its argument, or `Null`.** -/
theorem objects.derive_cap.al (s : S) (slot : U64) (c : capability.Cap) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → AlN nc c ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case Untyped p b i d =>
    simp only [objects.derive_cap]
    refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s slot hS) fun r _ => ?_
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      al_ok
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  case PageTable p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      al_ok
  case PageDirectory p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      al_ok
  case Pdpt p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      al_ok
  case Pml4 p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      al_ok
  case Ept p l m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      al_ok
  case HighVSpace p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      al_ok
  all_goals (simp only [objects.derive_cap]; al_ok)

set_option maxHeartbeats 1000000 in
/-- **CNode Copy / Mint's new cap is `AlN` the source cap** (module docstring). -/
theorem cnode.copied_cap.al (s : S) (lbl length buf src : U64) (src_cap : capability.Cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc, r = .Ok (nc, false) → AlN nc src_cap ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have fin : ∀ (m : capability.Cap), AlN m src_cap → ∀ x : core.result.Result capability.Cap error.Exc,
      (∀ nc, x = .Ok nc → AlN nc m) →
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch x
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual :
        Result (core.result.Result (capability.Cap × Bool) error.Exc)) ⦃ r =>
        ∀ nc, r = .Ok (nc, false) → AlN nc src_cap ⦄ := by
    intro m ht x hx
    rcases x with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      intro nc h; cases h; exact (hx v rfl).trans ht
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  split
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
      refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
      refine WP.spec_bind (capability.mask_cap_rights.al rr src_cap) fun c hc => ?_
      exact WP.spec_bind (objects.derive_cap.al s src c) fun r1 h1 => fin c hc r1 h1
  · split
    · split
      · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
      · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
        refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
        refine WP.spec_bind (capability.mask_cap_rights.al rr src_cap) fun c hc => ?_
        refine WP.spec_bind (objects.update_cap_data.al false data c) fun c1 hc1 => ?_
        exact WP.spec_bind (objects.derive_cap.al s src c1) fun r1 h1 => fin c1 (hc1.trans hc) r1 h1
    · split
      · exact (WP.spec_ok _).2 fun nc h => by cases h
      · split
        · simp only [error.truncated, WP.spec_ok]; intro nc h; cases h
        · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
          exact WP.spec_bind (P0.objects.update_cap_data.p0 true data src_cap) fun _ _ =>
            (WP.spec_ok _).2 fun nc h => by cases h

/-! ## The new cap encodable; Copy / Mint never move -/

theorem canon0 : CapRt.Canonical 0#u64 := Or.inl fun j hj _ => by simp

theorem capability.mask_vm_rights.lt4 (vm : U64) (r : capability.Rights) :
    capability.mask_vm_rights vm r ⦃ v => v.val < 4 ⦄ := by
  unfold capability.mask_vm_rights
  repeat' split
  all_goals
    rw [WP.spec_ok]
    simp [capability.VM_READ_ONLY, capability.VM_READ_WRITE, capability.VM_KERNEL_ONLY]

/-- **`mask_cap_rights` keeps the cap encodable.** -/
theorem capability.mask_cap_rights.wf (r : capability.Rights) (c : capability.Cap) (hc : CapRt.EncWf c) :
    capability.mask_cap_rights r c ⦃ m => CapRt.EncWf m ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    cases sd <;> cases rc <;> cases g <;> cases gr <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 hc
  case Notification p b sd rc =>
    cases sd <;> cases rc <;>
      simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte, bind_ok] <;>
      exact (WP.spec_ok _).2 hc
  case Reply p g =>
    cases g <;> simp only [capability.mask_cap_rights, Bool.false_eq_true, ↓reduceIte] <;>
      exact (WP.spec_ok _).2 hc
  case Frame p sz rt dv mp ep asd va =>
    simp only [capability.mask_cap_rights]
    refine WP.spec_bind (capability.mask_vm_rights.lt4 rt r) fun v hv => ?_
    cases ep
    · exact (WP.spec_ok _).2 ⟨hc.1, hv, hc.2.2.1, hc.2.2.2⟩
    · exact (WP.spec_ok _).2 ⟨hc.1, hv, hc.2.2.1, hc.2.2.2⟩
  all_goals (simp only [capability.mask_cap_rights]; exact (WP.spec_ok _).2 hc)

/-- **`update_cap_data` keeps the cap encodable** (a new `CNode` guard: `gs = data & 63`, guard below `2 ^ 58`). -/
theorem objects.update_cap_data.wf (pr : Bool) (data : U64) (c : capability.Cap) (hc : CapRt.EncWf c) :
    objects.update_cap_data pr data c ⦃ m => CapRt.EncWf m ⦄ := by
  cases c
  case Endpoint p b sd rc g gr =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 trivial
    · split
      · exact (WP.spec_ok _).2 hc
      · exact (WP.spec_ok _).2 trivial
  case Notification p b sd rc =>
    simp only [objects.update_cap_data]
    split
    · exact (WP.spec_ok _).2 trivial
    · split
      · exact (WP.spec_ok _).2 hc
      · exact (WP.spec_ok _).2 trivial
  case CNode p rd gs g =>
    simp only [objects.update_cap_data, lift, bind_ok]
    split
    · exact (WP.spec_ok _).2 trivial
    · rw [CapRt.shr_eq _ 6#i32 (by decide) (by decide), bind_ok]
      refine WP.spec_bind (Pₘ := fun _ => True) (by first | p0_auto | p0_split) fun m _ => ?_
      have h63 : (data &&& 63#u64).val < 64 := by
        have e : (data &&& 63#u64).val = data.val &&& 63 := by simp
        rw [e]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by norm_num)
      have hsh : ((⟨data.bv >>> (6#i32).toNat⟩ : U64)).val < 2 ^ 58 := by
        have := CapRt.lt_shr data.bv 6 (by norm_num); simpa using this
      have hg : ((⟨data.bv >>> (6#i32).toNat⟩ : U64) &&& m).val < 2 ^ 58 := by
        have e : ((⟨data.bv >>> (6#i32).toNat⟩ : U64) &&& m).val =
            ((⟨data.bv >>> (6#i32).toNat⟩ : U64)).val &&& m.val := by simp
        rw [e]; exact Nat.lt_of_le_of_lt Nat.and_le_left hsh
      exact (WP.spec_ok _).2 ⟨hc.1, hc.2.1, h63, hg⟩
  all_goals (simp only [objects.update_cap_data]; first | exact (WP.spec_ok _).2 hc | exact (WP.spec_ok _).2 trivial)

set_option hygiene false in
/-- An `Ok` result of `derive_cap` that is the argument or a cap without data (closes `EncWf`). -/
local macro "wf_ok" : tactic => `(tactic| (
  refine (WP.spec_ok _).2 fun nc h => ?_
  cases h
  first | exact hc | trivial))

set_option maxHeartbeats 1000000 in
/-- **`derive_cap` keeps the cap encodable** (a frame loses its mapping: `asid = 0`, `vaddr = 0`). -/
theorem objects.derive_cap.wf (s : S) (slot : U64) (c : capability.Cap) (hc : CapRt.EncWf c) :
    objects.derive_cap st s slot c ⦃ r => ∀ nc, r = .Ok nc → CapRt.EncWf nc ⦄ := by
  have hS : P0.StoreTotal st := L.total
  cases c
  case Untyped p b i d =>
    simp only [objects.derive_cap]
    refine WP.spec_bind (P0.cdt.ensure_no_children.p0 st s slot hS) fun r _ => ?_
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      wf_ok
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)
  case Frame p sz rt dv mp ep asd va =>
    simp only [objects.derive_cap]
    refine (WP.spec_ok _).2 fun nc h => ?_
    cases h
    have hp : CapRt.Canonical p ∧ rt.val < 4 := by cases ep <;> exact ⟨hc.1, hc.2.1⟩
    exact ⟨hp.1, hp.2, by simp, canon0⟩
  case PageTable p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      wf_ok
  case PageDirectory p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      wf_ok
  case Pdpt p m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      wf_ok
  case Pml4 p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      wf_ok
  case Ept p l m a v =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      wf_ok
  case HighVSpace p m a =>
    cases m
    · simp only [objects.derive_cap, Bool.false_eq_true, ↓reduceIte]
      exact (WP.spec_ok _).2 fun nc h => (by cases h)
    · simp only [objects.derive_cap, ↓reduceIte]
      wf_ok
  all_goals (simp only [objects.derive_cap]; wf_ok)

set_option maxHeartbeats 1000000 in
/-- **CNode Copy / Mint: no move, and the new cap encodable** when the source cap is (every decoded cap is,
`CapRt.decodeF_encWf`); only Move / Mutate return `true` (cnode.rs:77–102). -/
theorem cnode.copied_cap.wf (s : S) (lbl length buf src : U64) (src_cap : capability.Cap)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint) (hc : CapRt.EncWf src_cap) :
    cnode.copied_cap st s lbl length buf src src_cap ⦃ r => ∀ nc b, r = .Ok (nc, b) →
      b = false ∧ CapRt.EncWf nc ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have fin : ∀ x : core.result.Result capability.Cap error.Exc, (∀ nc, x = .Ok nc → CapRt.EncWf nc) →
      (do
        let cf ← core.result.Result.Insts.CoreOpsTry.branch x
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => ok (core.result.Result.Ok (val, false))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            (capability.Cap × Bool) (core.convert.FromSame error.Exc) residual :
        Result (core.result.Result (capability.Cap × Bool) error.Exc)) ⦃ r =>
        ∀ nc b, r = .Ok (nc, b) → b = false ∧ CapRt.EncWf nc ⦄ := by
    intro x hx
    rcases x with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok]
      intro nc b h; cases h; exact ⟨rfl, hx v rfl⟩
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc b h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc b h; cases h)
  unfold cnode.copied_cap
  refine WP.spec_bind (P0.sched.cur_thread.p0 st s hS) fun ct _ => ?_
  split
  · split
    · simp only [error.truncated, WP.spec_ok]; intro nc b h; cases h
    · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
      refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
      refine WP.spec_bind (capability.mask_cap_rights.wf rr src_cap hc) fun c hc' => ?_
      exact WP.spec_bind (objects.derive_cap.wf s src c hc') fun r1 h1 => fin r1 h1
  · split
    · split
      · simp only [error.truncated, WP.spec_ok]; intro nc b h; cases h
      · refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun i _ => ?_
        refine WP.spec_bind (P0.capability.Rights.from_word.p0 i) fun rr _ => ?_
        refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf _ hS) fun data _ => ?_
        refine WP.spec_bind (capability.mask_cap_rights.wf rr src_cap hc) fun c hc' => ?_
        refine WP.spec_bind (objects.update_cap_data.wf false data c hc') fun c1 hc1 => ?_
        exact WP.spec_bind (objects.derive_cap.wf s src c1 hc1) fun r1 h1 => fin r1 h1
    · rename_i h1 h2
      exfalso
      rcases hl with e | e
      · exact h1 e
      · exact h2 e

end ST
end R
end W7

end

end Fl4ProofsA64.P1
