/-
P1 (aarch64): InvGaps' `ept` family — the AArch64 Stage-2 VSpace cap's decode (`ept.decode`,
crates/fl4-core/src/arch/aarch64/ept.rs:371–423: `ARMVSpaceClean_Data`, `ARMVSpaceInvalidate_Data`,
`ARMVSpaceCleanInvalidate_Data`, `ARMVSpaceUnify_Instruction`). New A64 proof, not a port: x86_64's
Fl4Proofs.P1.QueueDecEpt is the VT-x EPT table decode (Map / Unmap of EPT entries, over P3's `EptPlace`); on
AArch64 an `Ept` cap is a Stage-2 VSpace root and its invocations are cache maintenance only. The decode reads
(the arguments, the root's walk `ept.root` / `ept.lookup_slot`, the entry), then either fails with the state
unchanged or restarts the caller (`Cur0.restart`) and calls the arch's `cache_op` (an arch call, no store
write). So `decGap_ept` needs **no placement premise** (x86_64: `EptPlaceH`).

Named premises: none.
-/
import Fl4ProofsA64.P1.QueueDecUt
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {P3Ok : S → Prop}
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errE" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok,
      error.illegal, error.truncated, error.range, error.invalid_cap, error.invalid_arg]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

theorem ept_sub1 {e st : U64} (h : ¬ (e <= st)) : (e - 1#u64 : Result U64) ⦃ _ => True ⦄ := by
  have : st.val < e.val := by scalar_tac
  p0_auto

theorem ept_sub2 {e st : U64} (h : ¬ (e <= st)) : (e - st : Result U64) ⦃ _ => True ⦄ := by
  have : st.val < e.val := by scalar_tac
  p0_auto

theorem ept_branch_tot {α β : Type} (r : core.result.Result α β) :
    core.result.Result.Insts.CoreOpsTry.branch r ⦃ _ => True ⦄ := by
  cases r <;> exact (WP.spec_ok _).2 trivial

/-- The decode's total steps (reads, the root's walk, pure arithmetic, arch calls). -/
syntax "eptT" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| eptT) => `(tactic| first
      | exact (WP.spec_ok _).2 trivial
      | exact P0.msg.syscall_arg.p0 st s _ buf _ hS
      | exact P0.ept.lookup_slot.p0 st s _ _ _ hS
      | exact P0.ept.is_leaf.p0 _ _
      | exact P0.ept.leaf_base.p0 _ _
      | exact P0.ept.s2_rights_of.p0 _
      | exact P0.ept.ipa_limit.p0 _
      | exact hS.read s _
      | exact hA.s2_ipa_bits _
      | exact hA.cache_op _ _ _ _ _ _ _
      | exact shl_and63u _
      | exact ept_sub1 (by assumption)
      | exact ept_sub2 (by assumption))

/-- One step of the decode's walk (no backtracking past it). -/
syntax "eptOne" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| eptOne) => `(tactic| first
      | refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
      | refine spec_ite (fun _ => ?_) (fun _ => ?_)
      | (step with sched.cur_thread.spec as ⟨ct, ect⟩
         have e : ct = L.curW s := ect
         subst e)
      | refine WP.spec_bind (Pₘ := fun _ => True) (by eptT) fun _ _ => ?_
      | (refine WP.spec_bind (P0.ept.root.p0 st s _ _ hS) fun r _ => ?_
         rcases r with ⟨r1, asid⟩ | e <;> (try simp only [irq_branch_ok, bind_ok])))

/-- The decode's walk: error leaves (state unchanged), the restarted leaf, or one step and on. -/
syntax "eptR" : tactic
set_option hygiene false in
macro_rules
  | `(tactic| eptR) => `(tactic| first
      | exact (WP.spec_ok _).2 h1.post
      | errE
      | (eptOne <;> eptR))

set_option maxHeartbeats 8000000 in
/-- **`ept.decode`** (AArch64 Stage-2 cache maintenance) keeps the invariants: error leaves with the state
unchanged, or the caller's restart (`Cur0`) and the arch's `cache_op`. -/
theorem ept.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len : U64) (c : capability.Cap) (slot buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ept.decode st ar s a lbl len c slot buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.decode
  simp only [lift, bind_ok]
  eptR

/-- **InvGaps' `ept`, discharged** (AArch64: Stage-2 VSpace caps; no placement premise). -/
theorem decGap_ept {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ept := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot _hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact ept.decode.dec hA a lbl len _ slot buf D

end

end Fl4ProofsA64.P1
