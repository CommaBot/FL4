/-
# P2: `E2E.Once` of the CSpace walk's tree (line hpzg, gen 3)

The I/O port path's only racy reads are CSpace slots (`P2/AccessIoLP.lean`, `hro`): a slot holding a CNode cap
at an alternative is in `IoRS` (`slot_back`), and any other slot read ends the walk. Here the walk's tree
(`R.cspace.resolve_address_bits_loop`, from `P2/ProgGenIo0.lean`) is walked for `Once`:

* `rab_body_once`: one step on a CNode cap, from the empty touched set: the leaves (error, the found slot with
  `bits_left = 0`, a non-CNode slot read with `bits_left ≠ 0`, a CNode slot read) are the continuation's cases;
  a CNode-valued slot is non-racy (`hRc`), so the touched set stays empty before the next step; after any other
  slot read the walk ends (`bits_left ≠ 0`, the continuation's own concern).
* `rab_loop_once`: the whole walk (fuel induction) for a CNode set `C` closed under the CNode-valued slots.

No premises.
-/
import Fl4Proofs.P2.OnceWalk
import Fl4Proofs.P2.ProgGenIoTop
import Fl4Proofs.P2.AccessIoWalk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.E2E (Once)

/-- A step's outcome of the CSpace walk. -/
abbrev RabCF := ControlFlow (capability.Cap × U64 × U64) (core.result.Result cspace.Resolved error.LookupFault)

section
variable {S A Z : Type} {st : machine.Store S} {ar : machine.Arch A} {Rd User : U64 → Prop}

theorem tch_empty_of {Wd : Set U64} {q : U64} (h : Rd q ∧ ¬ User q) : E2E.tch Rd User Wd q ∅ = ∅ := by
  unfold E2E.tch
  rw [if_neg (fun hr => hr ⟨h.2, Or.inl h.1⟩)]

theorem q8_not_tch {Wd : Set U64} (q : U64) :
    core.num.U64.wrapping_add q 8#u64 ∉ E2E.tch Rd User Wd q ∅ := by
  unfold E2E.tch
  split_ifs
  · intro h
    rcases h with h | h
    · exact q8_ne q h
    · exact h
  · exact fun h => h

/-- `obj.Slot.index` is `cnSlot`. -/
theorem slot_index_eq {p o sl : U64} (h : obj.Slot.index p o = ok sl) : sl = cnSlot p o := by
  unfold obj.Slot.index at h
  simp only [lift, bind_ok] at h
  exact (ok_inj_ff h).symm

set_option maxHeartbeats 2000000 in
/-- **One step of the walk on a CNode cap** (module docstring). -/
theorem rab_body_once {cptr p r gs g n fuel m : U64} (hm : cspace.mask r = ok m)
    {Wd : Set U64} {s : S} {a : A} {kk : RabCF → SProg Z} {r' : Z × S × A}
    (h : interp st ar ((R.cspace.resolve_address_bits_loop.body cptr (.CNode p r gs g) n fuel).sbind kk) s a = ok r')
    (hRc : ∀ y p' r1 gs' g', obj.Slot.cap st (cnSlot p (y &&& m)) s = ok (.CNode p' r1 gs' g') →
      (Rd (cnSlot p (y &&& m)) ∧ ¬ User (cnSlot p (y &&& m))) ∧
      (Rd (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64) ∧
        ¬ User (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)))
    (hE : ∀ e, interp st ar (kk (.done (.Err e))) s a = ok r' → Once st ar Rd User Wd ∅ (kk (.done (.Err e))) s a)
    (hL0 : ∀ y, interp st ar (kk (.done (.Ok ⟨cnSlot p (y &&& m), 0#u64⟩))) s a = ok r' →
      Once st ar Rd User Wd ∅ (kk (.done (.Ok ⟨cnSlot p (y &&& m), 0#u64⟩))) s a)
    (hLR : ∀ y bl c, bl ≠ 0#u64 → obj.Slot.cap st (cnSlot p (y &&& m)) s = ok c →
      (∀ p' r1 gs' g', c ≠ .CNode p' r1 gs' g') →
      interp st ar (kk (.done (.Ok ⟨cnSlot p (y &&& m), bl⟩))) s a = ok r' →
      ∀ T', Once st ar Rd User Wd T' (kk (.done (.Ok ⟨cnSlot p (y &&& m), bl⟩))) s a)
    (hLC : ∀ y p' r1 gs' g' n' f', obj.Slot.cap st (cnSlot p (y &&& m)) s = ok (.CNode p' r1 gs' g') →
      f'.val < fuel.val →
      interp st ar (kk (.cont (.CNode p' r1 gs' g', n', f'))) s a = ok r' →
      Once st ar Rd User Wd ∅ (kk (.cont (.CNode p' r1 gs' g', n', f'))) s a) :
    Once st ar Rd User Wd ∅ ((R.cspace.resolve_address_bits_loop.body cptr (.CNode p r gs g) n fuel).sbind kk) s a := by
  unfold R.cspace.resolve_address_bits_loop.body at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun _ h => ?_)
  · simp only [SProg.sbind] at h ⊢; exact hE _ h
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun hf0 h => ?_)
  · simp only [SProg.sbind] at h ⊢; exact hE _ h
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun fuel1 hf1 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun i1 _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun i2 _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun _ h => ?_)
  · simp only [SProg.sbind] at h ⊢; exact hE _ h
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun _ h => ?_)
  · simp only [SProg.sbind] at h ⊢; exact hE _ h
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun hgt h => ?_)
  · simp only [SProg.sbind] at h ⊢; exact hE _ h
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun i3 hi3 h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun i5 _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun i6 hi6 h => ?_)
  rw [hm] at hi6
  cases ok_inj_ff hi6
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_liftR h (fun sl hsl h => ?_)
  have esl := slot_index_eq hsl
  subst esl
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun _ h => ?_) (fun hnl h => ?_)
  · simp only [SProg.sbind] at h ⊢; exact hL0 _ h
  -- the slot read
  have hf1' : fuel1.val < fuel.val := by
    obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := fuel) (y := 1#u64) (by
      have : fuel.val ≠ 0 := fun e => hf0 (UScalar.eq_of_val_eq (by rw [e]; rfl))
      scalar_tac))
    have ez : z = fuel1 := ok_inj_ff (hz.symm.trans hf1)
    rw [ez] at hv
    have : fuel.val ≠ 0 := fun e => hf0 (UScalar.eq_of_val_eq (by rw [e]; rfl))
    scalar_tac
  have hi3' : i3 ≠ 0#u64 := by
    have hle : (core.num.U64.wrapping_add r gs).val ≤ n.val := by
      have := hgt; simp only [gt_iff_lt, not_lt] at this; scalar_tac
    obtain ⟨z, hz, hv⟩ := spec_ex_fd (U64.sub_spec (x := n) (y := core.num.U64.wrapping_add r gs) (by scalar_tac))
    have ez : z = i3 := ok_inj_ff (hz.symm.trans hi3)
    rw [ez] at hv
    intro e
    rw [e] at hv
    exact hnl (UScalar.eq_of_val_eq (by scalar_tac))
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_slotcap h (fun _ => Set.notMem_empty _) (fun _ => q8_not_tch _) (fun c hc h => ?_)
  by_cases hcn : ∃ p' r1 gs' g', c = .CNode p' r1 gs' g'
  · obtain ⟨p', r1, gs', g', rfl⟩ := hcn
    try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
    obtain ⟨h0, h8⟩ := hRc _ _ _ _ _ hc
    rw [tch_empty_of h0, tch_empty_of h8]
    exact hLC _ _ _ _ _ _ _ hc hf1' h
  · cases c <;> (try exact absurd ⟨_, _, _, _, rfl⟩ hcn) <;> (simp only [SProg.sbind] at h ⊢) <;>
      exact hLR _ _ _ hi3' hc (fun _ _ _ _ e => hcn ⟨_, _, _, _, e⟩) h _

/-- **The walk** (fuel induction) over a CNode set `C` closed under its CNode-valued slots (module docstring). -/
theorem rab_loop_once (C : U64 → U64 → Prop) {cptr : U64} {Wd : Set U64} {s : S} {a : A}
    {g : core.result.Result cspace.Resolved error.LookupFault → SProg Z} {r' : Z × S × A}
    (hRc : ∀ p r m y p' r1 gs' g', C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (y &&& m)) s = ok (.CNode p' r1 gs' g') →
      (Rd (cnSlot p (y &&& m)) ∧ ¬ User (cnSlot p (y &&& m))) ∧
      (Rd (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64) ∧
        ¬ User (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)))
    (hcl : WalkCl (st := st) s C)
    (hE : ∀ e, interp st ar (g (.Err e)) s a = ok r' → Once st ar Rd User Wd ∅ (g (.Err e)) s a)
    (hL0 : ∀ p r m y, C p r → cspace.mask r = ok m →
      interp st ar (g (.Ok ⟨cnSlot p (y &&& m), 0#u64⟩)) s a = ok r' →
      Once st ar Rd User Wd ∅ (g (.Ok ⟨cnSlot p (y &&& m), 0#u64⟩)) s a)
    (hLR : ∀ q bl, bl ≠ 0#u64 → ∀ T', Once st ar Rd User Wd T' (g (.Ok ⟨q, bl⟩)) s a) :
    ∀ (N : Nat) (x : capability.Cap × U64 × U64), (∀ p r gs gg, x.1 = .CNode p r gs gg → C p r) →
      interp st ar ((SProg.iter (fun xL => R.cspace.resolve_address_bits_loop.body cptr xL.1 xL.2.1 xL.2.2) N x).sbind
        g) s a = ok r' →
      Once st ar Rd User Wd ∅ ((SProg.iter (fun xL => R.cspace.resolve_address_bits_loop.body cptr xL.1 xL.2.1 xL.2.2)
        N x).sbind g) s a := by
  intro N
  induction N with
  | zero => intro x _ _; simp only [SProg.iter, SProg.sbind, Once]
  | succ N ih =>
    intro x hx h
    rw [SProg.iter, SProg.sbind_assoc] at h ⊢
    obtain ⟨cap, n, fuel⟩ := x
    by_cases hcn : ∃ p r gs gg, cap = .CNode p r gs gg
    · obtain ⟨p, r, gs, gg, rfl⟩ := hcn
      obtain ⟨m, hm, -⟩ := spec_ex_fd (P0.cspace.mask.p0 r)
      have hC := hx p r gs gg rfl
      dsimp only at h ⊢
      refine rab_body_once hm h (fun y p' r1 gs' g' hc => hRc p r m y p' r1 gs' g' hC hm hc)
        (fun e h => ?_) (fun y h => ?_) (fun y bl c hbl _ _ _ T' => ?_) (fun y p' r1 gs' g' n' f' hc _ h => ?_)
      · simp only [SProg.sbind] at h ⊢; exact hE e h
      · simp only [SProg.sbind] at h ⊢; exact hL0 p r m y hC hm h
      · simp only [SProg.sbind]; exact hLR _ _ hbl T'
      · simp only [SProg.sbind] at h ⊢
        exact ih _ (fun p2 r2 gs2 g2 e => by
          cases e; exact hcl p r m y _ _ _ _ hC hm hc) h
    · dsimp only at h ⊢
      unfold R.cspace.resolve_address_bits_loop.body at h ⊢
      cases cap <;> (try exact absurd ⟨_, _, _, _, rfl⟩ hcn) <;>
        (simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind] at h ⊢) <;> exact hE _ h

end

end Fl4Proofs.P2.PathObl
