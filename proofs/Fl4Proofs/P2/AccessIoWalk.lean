/-
# P2: the CSpace walk over radix-masked slots (line p2io)

The I/O port path's walk interface (`P1`'s `CnOff` shape): a predicate `C` on CNode
pointer and radix, and only the radix-masked slots `cnSlot p (y &&& m)` of each CNode
in `C`. `P2/AccessCSpace.lean` (line p2sl) states the walk for a pointer predicate over
every offset; the lemmas here are the same walk with the masked shape, for any store
`gS` answering as `st` on `R` (`PathObl.GRd`):

* `WalkRc` (the masked CNode-valued slots are in `R`), `WalkCl` (`C` closed under them);
* `rab_body.guardM`, `rab_loop.guardM`, `rab.guardM`, `cspace.lookup_slot.guardM`.

Premises: none.
-/
import Fl4Proofs.P2.AccessIo
import Fl4Proofs.P1.FastRRLk
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R]

/-- The walk's read set: for each CNode `(p, r)` in `C` and each radix-masked
index, a slot holding a CNode cap has both cap words in `R`. -/
abbrev WalkRc (R : U64 → Prop) (s : S) (C : U64 → U64 → Prop) : Prop :=
  ∀ p r m y p' r' gs' g', C p r → cspace.mask r = ok m →
    obj.Slot.cap st (cnSlot p (y &&& m)) s = ok (.CNode p' r' gs' g') →
    R (cnSlot p (y &&& m)) ∧ R (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)

/-- `C` is closed under the CNode caps in its radix-masked slots. -/
abbrev WalkCl (s : S) (C : U64 → U64 → Prop) : Prop :=
  ∀ p r m y p' r' gs' g', C p r → cspace.mask r = ok m →
    obj.Slot.cap st (cnSlot p (y &&& m)) s = ok (.CNode p' r' gs' g') → C p' r'

/-- One step of the walk on a CNode cap. -/
theorem rab_body.guardM {s : S} {cptr n fuel p r gs g m : U64}
    {y : ControlFlow (capability.Cap × U64 × U64) (core.result.Result cspace.Resolved error.LookupFault)}
    (hm : cspace.mask r = ok m)
    (hR : ∀ z c, obj.Slot.cap st (cnSlot p (z &&& m)) s = ok c →
      ((∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨
        ∃ bl, y = ControlFlow.done (core.result.Result.Ok { slot := cnSlot p (z &&& m), bits_left := bl })) →
      R (cnSlot p (z &&& m)) ∧ R (core.num.U64.wrapping_add (cnSlot p (z &&& m)) 8#u64))
    (h : cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel = ok y) :
    cspace.resolve_address_bits_loop.body gS s cptr (.CNode p r gs g) n fuel = ok y := by
  unfold cspace.resolve_address_bits_loop.body at h ⊢
  simp only [obj.Slot.index, lift, bind_ok, hm] at h ⊢
  revert h
  repeat' (first
    | (exact fun h => h)
    | (with_reducible refine tr_ite (fun _ => ?_) (fun _ => ?_))
    | (with_reducible_and_instances refine tr_bind_same (fun _ _ => ?_)))
  all_goals
    with_reducible_and_instances refine tr_bind (fun c hc hk => ?_) (fun _ _ hk => hk)
    rw [← hc]
    obtain ⟨h0, h8⟩ := hR _ c hc (by
      cases c <;>
        first
        | exact Or.inl ⟨_, _, _, _, rfl⟩
        | exact Or.inr ⟨_, (ok_inj_ff hk).symm⟩)
    exact obj.Slot.cap.guard _ s h0 h8

/-- **The walk** (fuel induction): it reads the radix-masked slots of the
CNodes in `C` (`C`-closed) holding a CNode (`hRc`) and the slot it returns
(`hRf`). -/
theorem rab_loop.guardM {s : S} {cptr : U64} (C : U64 → U64 → Prop)
    (hRc : WalkRc (st := st) R s C) (hcl : WalkCl (st := st) s C) :
    ∀ (N : Nat) (cap : capability.Cap) (n fuel : U64) (res : core.result.Result cspace.Resolved error.LookupFault),
      fuel.val < N → (∀ p r gs g, cap = .CNode p r gs g → C p r) →
      (∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64)) →
      cspace.resolve_address_bits_loop st cap s cptr n fuel = ok res →
      cspace.resolve_address_bits_loop gS cap s cptr n fuel = ok res := by
  intro N
  induction N with
  | zero => intro _ _ _ _ hf; omega
  | succ N ih =>
    intro cap n fuel res hf hc hRf h
    rw [rabLoop_unfold] at h ⊢
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    by_cases hcn : ∃ p r gs g, cap = .CNode p r gs g
    · obtain ⟨p, r, gs, g, rfl⟩ := hcn
      obtain ⟨m, hm, -⟩ := spec_ex_fd (P0.cspace.mask.p0 r)
      have hy' : cspace.resolve_address_bits_loop.body gS s cptr (.CNode p r gs g) n fuel = ok y := by
        refine rab_body.guardM hm (fun z c hc' hb => ?_) hy
        rcases hb with ⟨p', r', gs', g', rfl⟩ | ⟨bl, rfl⟩
        · exact hRc p r m z p' r' gs' g' (hc _ _ _ _ rfl) hm hc'
        · exact hRf _ (ok_inj_ff hk).symm
      rw [hy']; simp only [bind_ok]
      cases y with
      | done z => exact hk
      | cont x =>
        obtain ⟨m', z, hm', hoff, hlt⟩ := rab_body_cont2 st hy
        rw [hm] at hm'; cases ok_inj_ff hm'
        exact ih x.1 x.2.1 x.2.2 res (by omega)
          (fun p' r' gs' g' e => hcl p r m z p' r' gs' g' (hc _ _ _ _ rfl) hm (e ▸ hoff)) hRf hk
    · rw [rab_body_nonCN st gS s cptr cap n fuel (fun p r gs g e => hcn ⟨p, r, gs, g, e⟩), hy]
      simp only [bind_ok]
      cases y with
      | done z => exact hk
      | cont x =>
        exfalso
        (cases cap <;> (try simp [cspace.resolve_address_bits_loop.body] at hy)) <;>
          exact hcn ⟨_, _, _, _, rfl⟩

/-- `resolve_address_bits` (the loop with fuel 65). -/
theorem rab.guardM {s : S} {root : capability.Cap} {cptr n : U64}
    {res : core.result.Result cspace.Resolved error.LookupFault} (C : U64 → U64 → Prop)
    (hRc : WalkRc (st := st) R s C) (hcl : WalkCl (st := st) s C)
    (hroot : ∀ p r gs g, root = .CNode p r gs g → C p r)
    (hRf : ∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
    (h : cspace.resolve_address_bits st s root cptr n = ok res) :
    cspace.resolve_address_bits gS s root cptr n = ok res :=
  rab_loop.guardM C hRc hcl 66 root n 65#u64 res (by simp) hroot hRf h

/-- **`lookup_slot`** (masked walk): the CTable root slot (`sl`, both words) and the walk. -/
theorem cspace.lookup_slot.guardM {s : S} {t cptr sl : U64}
    {res : core.result.Result cspace.Resolved error.LookupFault} (C : U64 → U64 → Prop)
    (hsl : obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl)
    (hR0 : R sl) (hR8 : R (core.num.U64.wrapping_add sl 8#u64))
    (hRc : WalkRc (st := st) R s C) (hcl : WalkCl (st := st) s C)
    (hroot : ∀ p r gs g, obj.Slot.cap st sl s = ok (.CNode p r gs g) → C p r)
    (hRf : ∀ x, res = .Ok x → R x.slot ∧ R (core.num.U64.wrapping_add x.slot 8#u64))
    (h : cspace.lookup_slot st s t cptr = ok res) :
    cspace.lookup_slot gS s t cptr = ok res := by
  unfold cspace.lookup_slot at h ⊢
  rw [hsl] at h ⊢; simp only [bind_ok] at h ⊢
  rw [obj.Slot.cap.guard sl s hR0 hR8]
  obtain ⟨root, er, h⟩ := bind_eq_ok h
  rw [er]; simp only [bind_ok]
  exact rab.guardM C hRc hcl (fun p r gs g e => hroot p r gs g (e ▸ er)) hRf h

end

end Fl4Proofs.P2.PathObl
