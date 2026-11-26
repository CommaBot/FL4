/-
# P2 (line p3mc, gen 10): U9's re-annotated VM-fault body at the view starts that decline on the view's words

At a vmF start at core `c`'s view whose run, from **every** state agreeing with the start on the words the view keeps
(`Rd := IoRS (userP K) ∧ VN`), declines and reads only `Rd`, the re-annotated body is `Safe` at the physical memory.
Unlike the foreign-handler case (`VmFhSafe`) no word outside `Rd` is read, so `Once` is free (`once_of_guardG`).

* `vm_acc_checks`: an accepted run passes `FaultChecks` at its prefix state;
* `vm_fault_act_guard`, `vm_local_act_guard`: with the action not `RESUME_CURRENT` the run stops at the action check
  and runs the same on any store answering the prefix words, `CUR_SC` / `CONSUMED` / `CUR_THREAD` / `SCHED_ACTION` and
  the current SC's refill head;
* **`vm_guard_cert`** (`PathObl`): `safe_tr_of_states` from such runs (as `vm_fh_safe`, with `Once` by
  `once_of_guardG` + `once_monoR`);
* **`vm_view_cert`** (`E2EP`): the view-level wrapper (`Rd`, `Ro := rsE ptes (IoRS (userV K)) ∧ VO`, the pins of
  `vmF_fh_annV`), then `safe_narrow_tr`;
* the two cases (handoff p3mc §12 items 2 and 1): **`vmF_act_annV`** (prefix action ≠ 0, current SC homed on `c` in
  `ρ`) and **`vmF_nogo_annV`** (prefix action 0, and wherever the handler slot holds an endpoint cap with the endpoint
  receiving, the cap grants nothing and the head is homed on `c`).

No premise: every fact is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.VmFhView
import Fl4Proofs.P2.OnceGuard
import Fl4Proofs.P2.SlOnceL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}

/-- **An accepted run passes `FaultChecks`** at its prefix state. -/
theorem vm_acc_checks {x : S} {a : A} {addr code : U64} {z : S} {b : A}
    (h' : syscall.handle_vm_fault_local st ar x a addr code = ok (true, z, b)) :
    ∃ x1 a1', sched.update_timestamp st ar x a = ok (x1, a1') ∧
      ∃ ptr badge dest rr, FaultChecks st x1 (L.curW x1) ptr badge dest rr := by
  unfold syscall.handle_vm_fault_local at h'
  rw [if_neg vm_nd_ne] at h'
  obtain ⟨⟨x1, a1'⟩, eu', h'⟩ := bind_eq_ok h'
  simp only [uncurry_apply_pair] at h'
  obtain ⟨csc', -, h'⟩ := bind_eq_ok h'
  obtain ⟨u', -, h'⟩ := bind_eq_ok h'
  obtain ⟨bb', -, h'⟩ := bind_eq_ok h'
  by_cases hb : bb' = true
  swap
  · rw [if_neg hb] at h'; exact absurd (congrArg Prod.fst (ok_inj_ff h')) Bool.false_ne_true
  rw [if_pos hb] at h'
  rw [cur_thread_ok] at h'
  simp only [bind_ok] at h'
  obtain ⟨j1, -, h'⟩ := bind_eq_ok h'
  obtain ⟨j2, -, h'⟩ := bind_eq_ok h'
  obtain ⟨f, -, h'⟩ := bind_eq_ok h'
  obtain ⟨ptr, badge, dest, rr, C', -⟩ := vm_fault_acc st ar h'
  exact ⟨x1, a1', eu', ptr, badge, dest, rr, C'⟩

section gen
variable {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

/-- **With the action not `RESUME_CURRENT`, the fast path stops at the action check**, on any store. -/
theorem vm_fault_act_guard {X : S} {a : A} {t : obj.Tcb} {f : error.Fault} {r : Bool × S × A}
    (hR : R (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION)) (hne : L.actionW X ≠ 0#u64)
    (h : fastpath_vm.vm_fault st ar X a t f = ok r) :
    fastpath_vm.vm_fault gS ar X a t f = ok r := by
  change fastFaultG st ar X a t f fl4_abi.consts.fault.VMFault = ok r at h
  show fastFaultG gS ar X a t f fl4_abi.consts.fault.VMFault = ok r
  unfold fastFaultG at h ⊢
  revert h
  rw [sched.action.guard (gS := gS) X hR]
  refine tr_bind_same (fun i hi => ?_)
  refine tr_ite (fun _ h' => h') (fun hc => ?_)
  exfalso
  rw [eq_of_spec_fd (sched.action.spec (L := L) X)] at hi
  have e := ok_inj_ff hi
  subst e
  apply hne
  have hc' : ¬ (L.actionW X != sched.ACTION_RESUME_CURRENT) = true := hc
  simp only [bne_iff_ne, ne_eq, not_not] at hc'
  rw [hc']; unfold sched.ACTION_RESUME_CURRENT; rfl

/-- **A VM-fault local path whose prefix state's action is not `RESUME_CURRENT`, on `gS`.** -/
theorem vm_local_act_guard {X : S} {a : A} {addr code : U64} {r : Bool × S × A}
    (hct : R (ctA (L := L) X)) (hwct : W (ctA (L := L) X)) (hcn : R (cnA (L := L) X)) (hwcn : W (cnA (L := L) X))
    (hmid : ∀ X1 a1, sched.update_timestamp st ar X a = ok (X1, a1) →
      R (L.nodeAt X1 (L.cpu X1) layout.node.CUR_SC) ∧ R (L.nodeAt X1 (L.cpu X1) layout.node.CONSUMED) ∧
      R (L.nodeAt X1 (L.cpu X1) layout.node.CUR_THREAD) ∧ RdHead (L := L) R X1 (L.cscW X1) ∧
      R (L.nodeAt X1 (L.cpu X1) layout.node.SCHED_ACTION) ∧ L.actionW X1 ≠ 0#u64)
    (h : syscall.handle_vm_fault_local st ar X a addr code = ok r) :
    syscall.handle_vm_fault_local gS ar X a addr code = ok r := by
  unfold syscall.handle_vm_fault_local at h ⊢
  revert h
  refine tr_ite (fun _ h' => h') (fun _ => ?_)
  rw [sched.update_timestamp.guard (gS := gS) ar X a hct hwct hcn hwcn]
  refine tr_bind_same (fun y eu => ?_)
  obtain ⟨X1, a1⟩ := y
  simp only [uncurry_apply_pair]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hmid X1 a1 eu
  rw [sched.cur_sc.guard (gS := gS) X1 h1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.consumed.guard (gS := gS) X1 h2]
  refine tr_bind_same (fun u _ => ?_)
  have ec : csc = L.cscW X1 := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc; exact (ok_inj_ff ecsc).symm
  rw [ec, sporadic.sufficient.guard (gS := gS) ar X1 a1 (L.cscW X1) u h4]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h' => h')
  rw [sched.cur_thread.guard (gS := gS) X1 h3, cur_thread_ok]
  simp only [bind_ok]
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun _ _ => ?_)
  refine tr_bind_same (fun f _ => ?_)
  exact fun h' => vm_fault_act_guard h5 h6 h'

end gen

set_option maxHeartbeats 1000000 in
/-- **The VM-fault body is `Safe` where every run agreeing on `Rd` declines on `Rd`** (module docstring). -/
theorem vm_guard_cert {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hA : P0.ArchTotal ar) (addr code : U64) {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64}
    {σ : S} {a : A} (hc : L.cpu σ = c)
    {Rd Ro : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hH : ∀ x, (x = ctA (L := L) σ ∨ x = cnA (L := L) σ) → HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v)))
    (rT : Rd (ctA (L := L) σ)) (rN : Rd (cnA (L := L) σ))
    (rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD))
    (HD : ∀ x : S, Ag st Rd σ x → ∀ r, syscall.handle_vm_fault_local st ar x a addr code = ok r →
      r.1 ≠ true ∧ syscall.handle_vm_fault_local
        (PathObl.guard st Rd (fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ)) ar x a addr code = ok r) :
    Safe own cls kt c hs μ
      (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_vm_fault_local addr code) ∅ a) := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local mm ar x a addr code = interp mm ar (R.syscall.handle_vm_fault_local addr code) x a :=
    fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a
  refine safe_tr_of_states hL hO hmk (Hp := fun x => x = ctA (L := L) σ ∨ x = cnA (L := L) σ) _ a hH hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_vm_fault_local addr code) ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu
    split_ifs
    · exact (hν.1 b (hRPO b hu hb)).trans (hρμ b (hRPO b hu hb)).symm
    · rfl
  have G : Ag st Rd σ s := ⟨sk, sc, fun b hb => by
    rw [hmem b (hRal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]; exact hRdρ b hb⟩
  have ecur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ rC
  obtain ⟨r, hr⟩ := vm_total (st := st) hA addr code s a
  obtain ⟨hn, hg⟩ := HD s G r hr
  rw [hp] at hg
  have hW := (interp_guard _ s a r hg).2
  have hRq : RdEq st (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hPO : PreOK st (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) s (L.curW s) := by
    intro z b v hb _ _
    rw [L.write_eq]
    refine mguard_write (L.write_eq z b v) (hSO z b v ?_)
    rw [ecur, G.node, G.node] at hb
    exact hb
  have hM := vm_dec_m hRq hPO hr hn
  rw [hp] at hM
  have hWM := (interp_mguard _ s a r hM).2
  have hO1 : Once st ar Rd User ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s a :=
    once_of_guardG (fun q hq => (hR0 q hq).2) _ (vm_noZero addr code) ∅ ∅ s a r hg
  have hOnce : Once st ar Ro User ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s a :=
    once_monoR (fun b hb => (hR0 b hb).1) _ ∅ ∅ ∅ s a hO1 subset_rfl
  refine ⟨s, fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hRal b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨by rcases hx with rfl | rfl; exacts [hRal _ rT, hRal _ rN], fun _ => hx⟩,
    fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
