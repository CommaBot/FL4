/-
P3 (DESIGN.md §9), scheduling contexts: **SchedControl `ConfigureFlags`
end to end**: `decode_sched_control` (its decode, the caller's `Restart`
state, `configure_flags`) against l4v's decode, `set_thread_state ct
Restart` and `invoke_sched_control_configure_flags`.

The decoder's refill bound `max_num_refills sb` is the SC object's
`absMax n` for the object the cap names (`n = sb`, l4v `valid_cap`'s
object size; a hypothesis with the other facts of the target SC).
-/
import Fl4Proofs.P3.ScDecode
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

theorem absMax_eq {sb : Nat} (h : sb < 64) : absMax sb = Fl4Spec.maxNumRefills sb := by
  unfold absMax Fl4Spec.maxNumRefills Fl4Spec.sizeofSchedContextT Fl4Spec.wordSize Fl4Spec.refillSizeBytes
  rw [if_neg (by omega)]

/-- **`decode_sched_control` refines decode, `Restart`, and
`invoke_sched_control_configure_flags`.** -/
theorem decode_configure_refines (hT : TimeAgree ar) {N T C : Set U64} {c : U64} (th : TypedHeap) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ)
    (hN : NSC N C σ) (hI : Inv σ) (hC : CurInv σ) (hO : OffOK σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hsb : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x sb.val) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true) :
    schedcontext.decode_sched_control st ar s a lbl cpu length buf extra ⦃ res =>
      CPost σ (Fl4Spec.decodeSchedControlInvocationFlags (Z := Unit) slbl (args.map UScalar.bv) excaps) s a
        (fun inv res => ∃ σ1 σ', Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
          Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv σ1 = ({((), σ')}, False) ∧
          res.1 = .Ok () ∧ SchedRel st N T C c res.2.1 σ' ∧ NtfnStateRel N T (L.mem res.2.1) σ' ∧
          NSC N C σ' ∧ Inv σ') res ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ T := hct' ▸ hc.curT
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  refine decode_sched_control_refines hT th s a σ lbl slbl hlbl cpu length buf ct hct args hlen hargs extra x0 hx0
    excaps hex hsb _ ?_
  intro p sb bu pu er bd fl budget period hc0 _ _ _ _ _ hbud hper hmb hbp hle
  obtain ⟨hpC, hp0, x, hkp, hbnd⟩ := hsc p sb hc0
  have h64 := hsb p sb hc0
  have hpc : p.bv ≠ ct.bv := fun e => by rw [e, hkc] at hkp; cases hkp
  have hv : (sched.TS_RESTART).val = tsCode .restart := by rw [tsVals.2.1]; rfl
  refine WP.spec_bind (set_thread_state_refines s σ hR hS hctT hkc (not_in_ntfnQueue hR hctT hkc hrun) _ .restart hv
    (fun _ h => by cases h)) ?_
  rintro s1 ⟨σ1, h1, hR1, hS1⟩
  have h1' := h1
  rw [Fl4Proofs.P3.Notif.setThreadState_eq _ hkc] at h1'
  have e1 := pair_eq h1'
  subst e1
  set σ1 := stsAct (updK σ ct.bv (.tcb { xc with tcbState := .restart })) ct.bv with hσ1
  have hk1 : ∀ q, q ≠ ct.bv → σ1.kheap q = σ.kheap q := fun q hq => by
    rw [stsAct_kheap]; simp [updK, hq]
  have hkp1 : σ1.kheap p.bv = some (.schedContext x sb.val) := by rw [hk1 _ hpc]; exact hkp
  have hI1 : Inv σ1 := hI.restart hkc hrun
  have hC1 : CurInv σ1 := by
    have := hC.restart (xt := xc) (by rw [hcur]; exact hkc); rw [hcur] at this; exact this
  have hO1 : OffOK σ1 := hO.restart .restart
  have hN1 : NSC N C σ1 := fun m hm y q hy hq => by
    rw [stsAct_kheap] at hy
    by_cases e : m.bv = ct.bv
    · rw [e] at hy; simp [updK] at hy
    · simp only [updK_kheap, Function.update_of_ne e] at hy; exact hN m hm y q hy hq
  have hbnd1 : ∀ t : U64, x.scTcb = some t.bv →
      t ∈ T ∧ ∃ xt, σ1.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv := by
    intro t ht
    obtain ⟨htT, xt, hkt, hxt⟩ := hbnd t ht
    refine ⟨htT, ?_⟩
    by_cases e : t.bv = ct.bv
    · rw [e] at hkt; rw [hkt] at hkc; cases hkc
      exact ⟨{ xc with tcbState := .restart }, by rw [stsAct_kheap, e]; simp [updK], hxt⟩
    · exact ⟨xt, by rw [hk1 _ e]; exact hkt, hxt⟩
  have hNb : Fl4Spec.maxNumRefills sb.val < 2 ^ 60 := by rw [← absMax_eq h64]; exact absMax_lt _
  have hmr : (core.num.U64.wrapping_add er sporadic.MIN_REFILLS).val = er.val + 2 := by
    rw [core.num.U64.wrapping_add_val_eq, show (sporadic.MIN_REFILLS).val = 2 by unfold sporadic.MIN_REFILLS; rfl]
    have hsz : UScalar.size .U64 = 2 ^ 64 := by simp [UScalar.size_def, UScalarTy.numBits]
    exact Nat.mod_eq_of_lt (by rw [hsz]; omega)
  refine WP.spec_bind (configure_flags_refines s1 a σ1 hS1 hR1 hN1 hI1 hC1 hO1 hpC hp0 hkp1 hbnd1 cpu budget
    period (core.num.U64.wrapping_add er sporadic.MIN_REFILLS) bd fl hcpu (by rw [hmr]; omega) (by rw [hmr, absMax_eq h64]; exact hle) hmb hbp hT) ?_
  rintro ⟨s2, a2⟩ ⟨σ', hcfg, hS2, hR2, hN2, hI2, -⟩
  refine (WP.spec_ok _).mpr ⟨σ1, σ', h1, ?_, rfl, hS2, hR2, hN2, hI2⟩
  rw [← hbud, ← hper, ← hmr]
  exact hcfg

end

end

end Fl4Proofs.P3.Sched
