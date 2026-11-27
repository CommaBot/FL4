/-
P3 (line mmuAD, gen 41): **a VCPU invocation's reply has at most 64 words** (spec only): the extended decoder
returns `.readVmcb v f x` only with `x ≤ 64` (Ext/VirtVcpu's `decodeVcpuInvocation`, FL4 vcpu.rs l. 952: `value > 64`
is `InvalidArgument`), `performVcpuInvocationF (.readVmcb v f x)` replies `x` words, every other VCPU invocation at
most one. What the spec's `replyFromKernel` (`msgMaxLength` = 120) and FL4's word loop need of `VDecTail`'s list.

* `zv_mem_run_throw` / `zv_mem_run_ret`: an outcome of `throwError` / `returnOk`.
* `zv_rvmcb_cond_le`, `zv_dec_rvmcb_le` (own `maxHeartbeats 4000000`, hand-written): an outcome `.ok (.readVmcb v f x)` of the decoder has `x.toNat ≤ 64`.
* `OutLen m n`: every outcome of `m` is a list of at most `n` words; `outLen_pure`, `outLen_bind`.
* **`zv_rep_len`**: a decoded invocation's single perform outcome has at most 64 words.

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3HiTail
open Classical

namespace Fl4Proofs.P3
open Fl4Spec

noncomputable section

theorem zv_mem_run_throw {α : Type} {e : SyscallError} {σ : State Unit} {q : Except SyscallError α × State Unit}
    (h : q ∈ (ExceptT.run (NonDetE.throwError (σ := State Unit) (α := α) e) σ).1) : q = (.error e, σ) := h

theorem zv_mem_run_ret {α : Type} {a : α} {σ : State Unit} {q : Except SyscallError α × State Unit}
    (h : q ∈ (ExceptT.run (NonDetE.returnOk (σ := State Unit) (ε := SyscallError) a) σ).1) : q = (.ok a, σ) := h

/-- The decoder's `readVmcb` test passed: the count is at most 64. -/
theorem zv_rvmcb_cond_le {x : Word} {P Q R T : Prop} (h : ¬(P ∨ Q ∨ R ∨ x > 64 ∨ T)) : x.toNat ≤ 64 := by
  have h1 : ¬ (64 : Word) < x := fun hx => h (Or.inr (Or.inr (Or.inr (Or.inl hx))))
  have h2 := BitVec.le_def.mp (BitVec.not_lt.mp h1)
  simpa using h2

set_option maxHeartbeats 4000000 in
/-- **The decoder's `readVmcb` has at most 64 words** (module docstring). -/
theorem zv_dec_rvmcb_le {lbl : Data} {args : List Data} {p : ObjRef} {ec : List (Cap × CslotPtr)}
    {σ σ1 : State Unit} {v : ObjRef} {f x : Word}
    (h : (.ok (.readVmcb v f x), σ1) ∈ (ExceptT.run (decodeVcpuInvocation (Z := Unit) lbl args p ec) σ).1) :
    x.toNat ≤ 64 := by
  unfold decodeVcpuInvocation at h
  dsimp only at h
  split at h
  all_goals
    repeat' (first
      | (have e := zv_mem_run_throw h; cases e; done)
      | (have e := zv_mem_run_ret h; cases e; done)
      | (split at h)
      | (rw [ExceptT.run_bind, nd_bind_apply] at h
         obtain ⟨⟨r, s1⟩, -, h⟩ := h
         cases r <;> dsimp only at h)
      | (have e : _ = _ := h; cases e; done)
      | (simp at h; done))
  all_goals try (have e := zv_mem_run_ret h; cases e)
  all_goals exact zv_rvmcb_cond_le ‹_›

/-- Every outcome of `m` is a list of at most `n` words. -/
def OutLen (m : NonDet (State Unit) (List Data)) (n : Nat) : Prop := ∀ σ, ∀ q ∈ (m σ).1, q.1.length ≤ n

theorem outLen_pure {r : List Data} {n : Nat} (h : r.length ≤ n) : OutLen (pure r) n := by
  intro σ q hq
  have e : q = (r, σ) := hq
  subst e; exact h

theorem outLen_bind {α : Type} {m : NonDet (State Unit) α} {f : α → NonDet (State Unit) (List Data)} {n : Nat}
    (hf : ∀ a, OutLen (f a) n) : OutLen (m >>= f) n := by
  intro σ q hq
  rw [nd_bind_apply] at hq
  obtain ⟨y, -, hy⟩ := hq
  exact hf y.1 y.2 q hy

theorem zv_perf_len1 (i : VcpuInvocation) (hi : ∀ v f x, i ≠ .readVmcb v f x) :
    OutLen (performVcpuInvocationF (Z := Unit) i) 1 := by
  cases i with
  | readVmcb v f x => exact absurd rfl (hi v f x)
  | _ =>
    unfold performVcpuInvocationF
    repeat (first | exact outLen_pure (by simp) | exact outLen_bind fun _ => outLen_pure (by simp) |
      exact outLen_bind fun _ => outLen_bind fun _ => outLen_pure (by simp))

theorem zv_perf_len_rvmcb (v : ObjRef) (f x : Word) :
    OutLen (performVcpuInvocationF (Z := Unit) (.readVmcb v f x)) x.toNat := by
  unfold performVcpuInvocationF
  exact outLen_bind fun _ => outLen_pure (by simp)

/-- **A decoded invocation's reply has at most 64 words** (module docstring). -/
theorem zv_rep_len {lbl : Data} {args : List Data} {p : ObjRef} {ec : List (Cap × CslotPtr)}
    {σ σ1 σ' : State Unit} {inv : VcpuInvocation} {rep : List Data}
    (hd : (.ok inv, σ1) ∈ (ExceptT.run (decodeVcpuInvocation (Z := Unit) lbl args p ec) σ).1)
    (hp : performVcpuInvocationF (Z := Unit) inv σ1 = ({(rep, σ')}, False)) : rep.length ≤ 64 := by
  have hm : (rep, σ') ∈ (performVcpuInvocationF (Z := Unit) inv σ1).1 := by rw [hp]; exact Set.mem_singleton _
  by_cases hr : ∃ v f x, inv = .readVmcb v f x
  · obtain ⟨v, f, x, rfl⟩ := hr
    have h1 := zv_perf_len_rvmcb v f x σ1 _ hm
    have h2 := zv_dec_rvmcb_le hd
    simp only at h1; omega
  · have h1 := zv_perf_len1 inv (fun v f x h => hr ⟨v, f, x, h⟩) σ1 _ hm
    simp only at h1; omega

/-- The extended decoder's outcome at a VCPU cap is the VCPU decoder's. -/
theorem zv_decV_mem {fp : Bool} {lbl : Data} {args : List Data} {cref : CapRef} {slot : CslotPtr} {v : ObjRef}
    {ec : List (Cap × CslotPtr)} {buffer : Option ObjRef} {σ : State Unit} {inv : VcpuInvocation}
    (h : ExceptT.run (fl4DecodeInvocationV (Z := Unit) fp lbl args cref slot (.archObjectCap (.vcpuCap v)) ec buffer)
      σ = ({(.ok (.vcpu inv), σ)}, False)) :
    (.ok inv, σ) ∈ (ExceptT.run (decodeVcpuInvocation (Z := Unit) lbl args v ec) σ).1 := by
  rw [zv_decV_vcpu] at h
  have hm : ((.ok (.vcpu inv) : Except SyscallError Fl4InvocationV), σ) ∈
      (ExceptT.run (NonDetE.liftME Fl4InvocationV.vcpu (decodeVcpuInvocation (Z := Unit) lbl args v ec)) σ).1 := by
    rw [h]; exact Set.mem_singleton _
  unfold NonDetE.liftME at hm
  rw [ExceptT.run_bind, nd_bind_apply] at hm
  obtain ⟨⟨r, s1⟩, hr, h2⟩ := hm
  cases r with
  | error e =>
    have e2 : ((.ok (.vcpu inv) : Except SyscallError Fl4InvocationV), σ) = (.error e, s1) := h2
    cases e2
  | ok a =>
    have e2 : ((.ok (.vcpu inv) : Except SyscallError Fl4InvocationV), σ) = (.ok (.vcpu a), s1) := h2
    simp only [Prod.mk.injEq, Except.ok.injEq, Fl4InvocationV.vcpu.injEq] at e2
    obtain ⟨rfl, rfl⟩ := e2
    exact hr

end

end Fl4Proofs.P3
