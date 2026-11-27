/-
P3x for virtualization (line virt, gen 24, item 1b): **FL4's `untyped::decode` against the gated spec decoder
`fl4DecodeUntypedInvocationV`, both gate outcomes** (FL4 untyped.rs l. 42-43; Fl4Spec/Ext/VirtFinalise
`untypedVtxGate` / `fl4DecodeUntypedInvocationV`).

* `fl4DecodeUntypedInvocationV_closed` / `_open`: the gated spec decoder on each side of `untypedVtxGate`.
* **`untyped_decode_refinesV`**: on `untypedVtxGate` (the backend `none`) FL4 returns `InvalidArgument 0` with
  nothing changed and the spec throws `invalidArgument 0` (VirtUtGate's `untyped_decode_vtx_gate`); otherwise every
  type number, the VT-x ones included, decodes as VirtUtDecV's `untyped_decode_refines_fl4V` (the gate is open: the
  backend is not `none`, so `virtualization()` reports its nonzero code; when the backend is `none` but the gate is
  shut by a short message or no extra cap, FL4 never reaches its gate either).

Named premises: `hag` [P] (the platform agreement `∀ r, Arch::virtualization() = ok r → r.val = virtKind.code`,
VIRT-PLAN §11.1, used unchanged: VirtWit9's `hvk_of_agree` / VirtWit10's `WitAgree`; FL4's `virtualization()`
returns the backend selected at boot (arch/x86_64 `Arch` impl), the spec's `virtKind` is that same constant).
`hA : P0.ArchTotal arI` (P0: every arch call returns). The rest as `untyped_decode_refines_fl4`. No [J]/[W].
New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtUtDecV
import Fl4Proofs.P3.VirtUtGate
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The gated spec decoder, gate closed. -/
theorem fl4DecodeUntypedInvocationV_closed {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {sl : Fl4Spec.CslotPtr}
    {c : Fl4Spec.Cap} {excaps : List Fl4Spec.Cap} (hg : Fl4Spec.untypedVtxGate slbl args excaps) (σ : Fl4Spec.State Unit) :
    (Fl4Spec.fl4DecodeUntypedInvocationV (Z := Unit) slbl args sl c excaps).run σ =
      ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold Fl4Spec.fl4DecodeUntypedInvocationV
  rw [if_pos hg]
  rfl

/-- The gated spec decoder, gate open. -/
theorem fl4DecodeUntypedInvocationV_open {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data} {sl : Fl4Spec.CslotPtr}
    {c : Fl4Spec.Cap} {excaps : List Fl4Spec.Cap} (hg : ¬ Fl4Spec.untypedVtxGate slbl args excaps) :
    Fl4Spec.fl4DecodeUntypedInvocationV (Z := Unit) slbl args sl c excaps =
      Fl4Spec.fl4DecodeUntypedInvocation slbl args sl c excaps := by
  unfold Fl4Spec.fl4DecodeUntypedInvocationV
  rw [if_neg hg]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **FL4's `untyped::decode` against the gated spec decoder, both gate outcomes** (module docstring). -/
theorem untyped_decode_refinesV [Fl4Proofs.P1.PlainStore st] {A : Type} (arI : machine.Arch A) (hA : P0.ArchTotal arI)
    (th : TypedHeap) (s : S) (ar : A)
    (hag : ∀ r, arI.virtualization ar = ok r → r.val = Fl4Spec.virtKind.code)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (slot : obj.Slot) (sl : Fl4Spec.CslotPtr) (hsl : slot = cslotAddr sl) (hAs : AbsSlot th sl)
    (p sb fi : U64) (dev : Bool) (hcap : capAt (L.mem s) slot = ok (.Untyped p sb fi dev))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    (Q : Fl4Spec.UntypedInvocation → core.result.Result Unit error.Exc × S × A → Prop)
    (hQ : ∀ (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64),
      args.head? = some nt → RetCtx (L := L) th s σ sl sb fi dev nt us dest off win t r reset fiv →
      (do
        let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
        untyped.retype st arI s2 ar slot reset ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win
          dev) ⦃ res =>
        Q (.retype sl reset p.bv (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val
          (windowSlots dest r off.val win.val) dev) res ⦄) :
    untyped.decode st arI s ar lbl length slot (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocationV slbl (args.map UScalar.bv) sl (absCap (.Untyped p sb fi dev)) excaps)
        s ar Q res ⦄ := by
  obtain ⟨v, hv, -⟩ := spec_exists (hA.virtualization ar)
  by_cases hg : Fl4Spec.untypedVtxGate slbl (args.map UScalar.bv) excaps
  · -- gate closed: the backend is `none`, FL4 refuses with `InvalidArgument 0`
    obtain ⟨hl, h6, hne, hvt, hvk⟩ := hg
    have hl' := hlbl.1 hl
    subst hl'
    have h6' : 6 ≤ args.length := by simpa using h6
    have hx0n : x0 ≠ 0#u64 := by
      rcases hex with ⟨-, rfl⟩ | ⟨h, -⟩
      · exact absurd rfl hne
      · exact h
    obtain ⟨nt, rest, rfl⟩ : ∃ nt rest, args = nt :: rest := by
      cases args with
      | nil => simp at h6'
      | cons a tl => exact ⟨a, tl, rfl⟩
    have hvt' : 14 ≤ nt.val ∧ nt.val ≤ 18 := by
      simpa [Fl4Spec.dataToNat, Fl4Spec.unat, Fl4Spec.isVtxObjectTypeNum, UScalar.bv_toNat] using hvt
    have hv0 : v = 0#u64 := by
      apply UScalar.eq_of_val_eq
      rw [hag v hv, hvk]; rfl
    subst hv0
    rw [untyped_decode_vtx_gate arI s ar length slot p sb fi dev buf extra ct hct (nt :: rest) hlen h6' hargs x0 hx0
      hx0n nt rfl hvt'.1 (by omega) hv]
    exact UPost.err (fl4DecodeUntypedInvocationV_closed ⟨hl, h6, hne, hvt, hvk⟩ σ)
      (show (0 : Nat) = (0#u64 : U64).val from rfl)
  · -- gate open
    rw [fl4DecodeUntypedInvocationV_open hg]
    refine untyped_decode_refines_fl4V arI th s ar σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen
      hargs slot sl hsl hAs p sb fi dev hcap extra x0 hx0 excaps hex ?_ hfan Q hQ
    intro hl h6 hx0n x hx hlo hhi
    refine ⟨v, hv, fun hv0 => hg ⟨hlbl.2 hl, by simpa using h6, ?_, ?_, ?_⟩⟩
    · rcases hex with ⟨h, -⟩ | ⟨-, -, -, -, -, -, -, -, rfl⟩
      · exact absurd h hx0n
      · simp
    · cases args with
      | nil => simp at hx
      | cons a tl =>
        simp only [List.head?_cons, Option.some.injEq] at hx
        subst hx
        show decide (14 ≤ a.val ∧ a.val ≤ 18) = true
        simp only [decide_eq_true_eq]
        omega
    · have h0 := hag v hv
      rw [hv0] at h0
      revert h0
      generalize Fl4Spec.virtKind = k
      cases k <;> intro h0 <;> first | rfl | (simp [Fl4Spec.VirtKind.code] at h0)
end

end
end Fl4Proofs.P3
