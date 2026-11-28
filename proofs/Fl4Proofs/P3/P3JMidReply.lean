/-
P3 (p3J gen 33): **the mid invocation's Reply-cap decode leaf reduced to `do_reply_transfer`'s footprint**.

P3JMidDecK's `DispStabFootLk` asks, for a Reply cap `Reply p g` in the looked-up slot (`midDecReply`), the decode
leaf `XCapP (MidX …) (MidXP …)`: the stable post (`JStab Z H Cs`), `MR`, and the footprint `ProjW H Cs s'`. The
first two are StPostReply's `replyLeafJSt` (with `runTmoP_recvSt`) through IpcSendTop's `decode_replyDMX`, the
preempted outcome excluded by `specDec_noPreK`; `MR` as StPostInv's `handle_invocation_replyJSt` but from
`MachPlatT` (the tops' `MachPlatF` + `IpiF`, not `MachPlat`): **`TopPostDMXP.mrT`**, **`TopPostRMX.mrT`**,
**`XCapP.mrT`** (KEntry38's `….mr` with `msF_mrT`). The `set_thread_state … RESTART` before the transfer is in
`ProjW` (P3JMidInv's `stsProjW`). Left: the transfer's own footprint.

* **`ReplyXferFt Z H Cs` [J]** (FL4 only): at every state `JAtZ (Z.mv G V) H Cs` with current thread `ct`, every
  reply object `p ∈ Z.R`, the state `s1` after `set_thread_state ct RESTART`, `do_reply_transfer s1 ct p g` writes
  only `ProjW H Cs s1`.
* **`midDecReply_of`**: `SInvX σ`, `ct ≠ idle` at the entry and `ReplyXferFt` give `midDecReply`'s
  `MidDecStW (KW ∧ IsReplyCap)` (platform facts [P] `hA`, `hnd`, `hmax`, `htu`, `hT` (`TimeAgree.mb` for
  `min_budget`), `hMT`, `hKD`).
* **`DispStabFootLr` [J]** {inv, midReplyFt, midDecOther, midSpec, midRecvSw}: `DispStabFootLk` with
  `midDecReply` replaced by `midReplyFt` (`ReplyXferFt Z H Cs` under the same conditions); **`dispStabFootLk_of_Lr`**,
  top **`kernel_entry_runMcWKR_sysLr`** (globals as `_sysLk`).

Premise honesty: `midReplyFt` speaks of a sub-call of `midDecReply`'s (the transfer inside the Reply decode) and
of every reply object at every `JAtZ` state, not only the looked-up one; it implies `midDecReply` (`midDecReply_of`)
and is **not implied by it**. Not false on reachable states (argument, not proof): `ProjW` is every heap object
word, the kernel-global area and every node word except the other cores' offsets 8 / 32 (their idle thread and
idle SC words, written only at boot); `do_reply_transfer`'s writes are reply / TCB / SC words, the receiver's IPC
buffer frame (in `H`), the executing core's node and, through `possible_switch_to` / the stall of a remote SC,
other cores' scheduling words — none of the excluded ones (P1 `do_reply_transfer.foot` has it in `IpcFoot`; the
missing step is the node identity words, the `KWN ∅ False` walk of goal 2). Removed from the [J] content: the Reply
decode's stable post and `MR` (proved), the restart's footprint.

Named premises: `ReplyXferFt` [J], `DispStabFootLr` [J]. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JMidDecK
import Fl4Proofs.P3.StPostInv
import Fl4Proofs.P3.XTopJointKEntry41V
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {MR : A → Fl4Spec.MachineState → Prop}

/-- (p3J gen 33) **`TopPostDMXP.mr` from `MachPlatT`** (module docstring). -/
theorem TopPostDMXP.mrT (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostDMXP (L := L) X XP σ blk call don m s res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ inv, DecOut m σ inv → MachT.QInv inv) :
    TopPostDMXP (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) XP σ blk call don m s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩
  · refine Or.inl ⟨e, h1, h2, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢; exact ⟨h4, hR⟩
  · refine Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, ?_⟩
    dsimp only at h4 ⊢
    by_cases hp : res.1 = .Err .Preempted
    · rw [if_pos hp] at h4 ⊢; exact h4
    · rw [if_neg hp] at h4 ⊢
      exact ⟨h4, msF_mr hM hR ((msF_qperf (hq inv h1) hy).trans (msF_restart h2))⟩

/-- (p3J gen 33) **`TopPostRMX.mr` from `MachPlatT`**. -/
theorem TopPostRMX.mrT (hM : MachPlat arI MR) {X : S → A → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit}
    {blk call don : Bool} {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {ct : U64} {s : S}
    {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostRMX (L := L) X σ blk call don m ct s res) (hR : MR res.2.2 σ.machineState)
    (hq : ∀ inv, DecOut m σ inv → MachT.QInv inv) :
    TopPostRMX (L := L) (fun s a σ => X s a σ ∧ MR a σ.machineState) σ blk call don m ct s res := by
  rcases h with ⟨e, h1, h2, h3, h4⟩ | ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩
  · exact Or.inl ⟨e, h1, h2, h3, h4, hR⟩
  · refine Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, msF_mr hM hR ?_⟩
    exact ((congrArg Prod.fst (MachT.mtk_specTailG call ct.bv rr σy z hz)).trans
      (msF_qperf (hq inv h3) h5)).trans (msF_restart h4)

/-- (p3J gen 33) **`XCapP.mr` from `MachPlatT`** (module docstring). -/
theorem XCapP.mrT (hM : MachPlat arI MR) {X XP : S → A → Fl4Spec.State Unit → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCapP (L := L) arI X XP s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      MR r.2.2 σ.machineState ⦄)
    (hq : ∀ inv, DecOut (specDec fp slbl args ci sl c excaps buffer) σ inv → MachT.QInv inv) :
    XCapP (L := L) arI (fun s a σ => X s a σ ∧ MR a σ.machineState) XP s ar σ lbl length slot c blk call don fp buf
      extra slbl args ci sl excaps buffer ct := by
  rcases h with h | h
  · exact Or.inl (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrT hM h2 hq)
  · exact Or.inr (WP.spec_mono (WP.spec_and h hW) fun _ ⟨h1, h2⟩ => h1.mrT hM h2 hq)

end

end

end Fl4Proofs.P3

namespace Fl4Proofs.P3.Mc
open fl4_core Classical Fl4Spec Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P2.Wit
open Fl4Proofs.P3.JBoot Fl4Proofs.P3.SInvR.G5 Fl4Proofs.P3.Vs Fl4Proofs.P3.JBootQ
open Fl4Proofs.P3.SInvR.G4

end Fl4Proofs.P3.Mc
