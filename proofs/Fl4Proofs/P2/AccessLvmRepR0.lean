/-
# P2 (line lvm, gen 4): **`vcpu.report` on a guarded store** (no VCPU case; split for check time)

`vcpu.report.guardP`: for a predicate `P` the report's four write kinds keep (P1's `RepSteps`, the buffer the one
looked up) and at which the final `set_thread_state TS_RUNNING` is guarded (`hfin`), the report on any store
answering its reads / writes (`RepG`) as `st` is the real one. No named premises.
-/
import Fl4Proofs.P2.AccessLvmRep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section rep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

set_option maxHeartbeats 8000000 in
/-- **`vcpu.report` on a guarded store**, no VCPU bound: (module docstring): for a predicate `P` its four write kinds keep
(`RepSteps`, the buffer `b` the one looked up) and at which the final `set_thread_state` is guarded (`hfin`). -/
theorem vcpu.report.guardP0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge v b : U64) {P : S → Prop} {vOk : U64 → Prop} (Rs : RepSteps st t (· = b) P vOk)
    (hfin : ∀ s1, P s1 →
      sched.set_thread_state gS s1 t sched.TS_RUNNING = sched.set_thread_state st s1 t sched.TS_RUNNING)
    (hP : P s) (hvw : R (core.num.U64.wrapping_add t 3664#u64))
    (hv : L.mem s (core.num.U64.wrapping_add t 3664#u64) = v)
    (hlb : msg.lookup_ipc_buffer gS s true t = msg.lookup_ipc_buffer st s true t)
    (hb : msg.lookup_ipc_buffer st s true t = ok b)
    (hok : v ≠ 0#u64 → vOk v) (G : RepG R W t v b) (hv0 : v = 0#u64) :
    vcpu.report gS ar s a t badge = vcpu.report st ar s a t badge := by
  have hS : P0.StoreTotal st := L.total
  have hfin0 : ∀ s1, P s1 → sched.set_thread_state st s1 t sched.TS_RUNNING ⦃ fun _ => True ⦄ :=
    fun s1 _ => Fl4Proofs.P0.sched.set_thread_state.p0 st s1 t _ hS
  have gfr : vcpu.full_reply gS s t = vcpu.full_reply st s t := by
    unfold vcpu.full_reply; rw [obj.Tcb.reg.guard t s _ (G.regR _ (by scalar_tac))]
  have gmr : ∀ (s' : S) (i x : U64), i.val < 127 → msg.set_mr gS s' t b i x = msg.set_mr st s' t b i x :=
    fun s' i x hi => msg.set_mr.guard s' t b i x hi G.regW G.bufW
  have gsr : ∀ (s' : S) (r x : U64), r.val < 384 → obj.Tcb.set_reg gS t s' r x = obj.Tcb.set_reg st t s' r x :=
    fun s' r x hr => obj.Tcb.set_reg.guard t s' r x (G.regW r hr)
  have grg : ∀ (s' : S) (r : U64), r.val < 384 → obj.Tcb.reg gS t s' r = obj.Tcb.reg st t s' r :=
    fun s' r hr => obj.Tcb.reg.guard t s' r (G.regR r hr)
  have gsa : ∀ (s' : S), msg.syscall_arg gS s' t b 2#u64 = msg.syscall_arg st s' t b 2#u64 :=
    fun s' => msg.syscall_arg.guard_lt s' t b 2#u64 (by rw [n_msg_regs]; decide)
      (fun r hr => G.regR r (post_of_ok (msg.msg_register.lt _) hr))
  have e216 : (27#u64 * 8#u64 : Result U64) = ok 216#u64 := lv_mul_ok (by scalar_tac) (by scalar_tac)
  have e21208 : vcpu.EXIT + 216#u64 = ok 21208#u64 := lv_add_ok (by scalar_tac) (by scalar_tac)
  unfold vcpu.report
  rw [vcpu.bound.guardT s t hvw]
  have e : vcpu.bound st s t = ok v := by rw [← hv]; exact eq_of_spec_fd (vcpu.bound.spec (L := L) s t)
  rw [e]
  simp only [bind_ok]
  subst hv0
  have gl2 : ∀ (s' : S) (i : U64), vcpu.report_loop2 gS s' t 0#u64 false b false i =
      vcpu.report_loop2 st s' t 0#u64 false b false i :=
    lv_loop2 (fun h => by simp at h) G.regW G.bufW
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bind_ok, hlb, hb, gfr]
  simp only [gl2, vcpu.finish_notification]
  simp only [fun s' x => gmr s' 0#u64 x (by scalar_tac), fun s' x => gmr s' 1#u64 x (by scalar_tac), fun s' x => gmr s' 2#u64 x (by scalar_tac), fun s' x => gmr s' 3#u64 x (by scalar_tac), fun s' x => gmr s' 4#u64 x (by scalar_tac), fun s' x => gmr s' 5#u64 x (by scalar_tac), fun s' x => gmr s' 6#u64 x (by scalar_tac), fun s' x => gmr s' 7#u64 x (by scalar_tac), fun s' x => gmr s' 8#u64 x (by scalar_tac), fun s' x => gmr s' 9#u64 x (by scalar_tac), fun s' x => gmr s' 25#u64 x (by scalar_tac), fun s' x => gmr s' 26#u64 x (by scalar_tac), fun s' x => gmr s' 29#u64 x (by scalar_tac),
    fun s' x => gsr s' layout.reg.MSG_INFO x (by scalar_tac), fun s' x => gsr s' layout.reg.BADGE x (by scalar_tac), fun s' x => gsr s' layout.reg.FAULT_IP x (by simp [layout.reg.FAULT_IP]), fun s' => grg s' layout.reg.NEXT_IP (by simp [layout.reg.NEXT_IP])]
  repeat' (first
    | rfl
    | exact hfin _ (by assumption)
    | (refine ite_congr rfl (fun _ => ?_) (fun _ => ?_))
    | (refine bind_guard_congr (α := U64) rfl fun _ _ => ?_)
    | (refine bind_guard_congr (α := Bool) rfl fun _ _ => ?_)
    | (refine bind_guard_congr rfl ?_; rintro ⟨_, _⟩ h
       have := post_of_ok (Rs.mr _ _ _ _ rfl (by assumption) (by scalar_tac)) h
       try simp only [uncurry_apply_pair])
    | (refine bind_guard_congr rfl ?_; intro _ h
       have := post_of_ok (Rs.reg _ _ _ (by assumption) (by simp)) h)
    | (refine bind_guard_congr rfl ?_; intro _ h
       have := post_of_ok (vcpu.report_loop2.gen Rs rfl (by assumption)) h)
    | (refine bind_guard_congr rfl ?_; intro _ h
       have := post_of_ok (P := P) (by repeat' (rep_step Rs, rfl, hfin0, hS, hA, P)) h)
    | (refine bind_guard_congr rfl fun _ _ => ?_))
end rep

end Fl4Proofs.P2.PathObl
