/-
# P2: the accepted VM ReplyRecv local path on a store answering as `st` (line p2e, VM paths)

`syscall.handle_reply_recv_vm_local.guard_acc`: an accepted run (`true`) of the VM ReplyRecv local
path on any store `gS` answering as `st` on the words it reads (`GRd gS st R`) and writes
(`GWr gS st W`) ends exactly as the real run, given the fast path after the prefix agrees on `gS`
(`hmid`, for the real `FAULT_IP` value `NEXT_IP - 2`; `fastpath_vm.reply_recv_vm_found.guard` of `P2/AccessVmRR.lean` at the post-prefix state).
The prefix: the current thread, its `FLAGS` (`TRAP_SYSCALLS`) and `NEXT_IP`, the `FAULT_IP` write,
`update_timestamp` (the node's `CUR_TIME` / `CONSUMED`), the current SC's budget check
(`CUR_SC`, `CONSUMED`, its head refill).

Generic over the Arch instance. Premises: none (the hypotheses are the run-relative sets,
discharged in the path's obligations).
-/
import Fl4Proofs.P2.AccessVmRR
import Fl4Proofs.P2.AccessVmF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]

/-- **The accepted VM ReplyRecv local path on `gS`** ends exactly as the real run: the prefix's
words (`hct` … `hsuf`), then the fast path agreeing after it (`hmid`). -/
theorem syscall.handle_reply_recv_vm_local.guard_acc {A : Type} (ar : machine.Arch A) {s s' : S} {a a' : A}
    {rptr ep : U64}
    (hct : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hni : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    (hut : ∀ v s1, obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1 →
      R (ctA (L := L) s1) ∧ W (ctA (L := L) s1) ∧ R (cnA (L := L) s1) ∧ W (cnA (L := L) s1))
    (hcsc : ∀ v s1 s2 a1, obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_SC) ∧ R (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED))
    (hsuf : ∀ v s1 s2 a1 csc, obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → sched.cur_sc st s2 = ok csc →
      RdHead (L := L) R s2 csc)
    (hmid : ∀ nx s1 s2 a1, obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      fastpath_vm.reply_recv_vm_found st ar s2 a1 (L.curW s) rptr ep = ok (true, s', a') →
      fastpath_vm.reply_recv_vm_found gS ar s2 a1 (L.curW s) rptr ep =
        fastpath_vm.reply_recv_vm_found st ar s2 a1 (L.curW s) rptr ep)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (true, s', a')) :
    syscall.handle_reply_recv_vm_local gS ar s a (rptr, ep) = ok (true, s', a') := by
  unfold syscall.handle_reply_recv_vm_local at h ⊢
  revert h
  rw [sched.cur_thread.guard (gS := gS) s hct]
  refine tr_bind_same (fun t et => ?_)
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.flags.guard (gS := gS) (L.curW s) s hfl]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_bind_same (fun i1 _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [obj.Tcb.reg.guard (gS := gS) (L.curW s) s _ hni]
  refine tr_bind_same (fun nx enx => ?_)
  refine tr_bind_same (fun v ev => ?_)
  have ev' : core.num.U64.wrapping_sub nx 2#u64 = v := ok_inj_ff ev
  subst ev'
  rw [obj.Tcb.set_reg.guard (gS := gS) (L.curW s) s _ _ hfi]
  refine tr_bind_same (fun s1 e1 => ?_)
  obtain ⟨r1, w1, r2, w2⟩ := hut _ s1 e1
  refine tr_bind (fun x hx _ => by rw [sched.update_timestamp.guard (gS := gS) ar s1 a r1 w1 r2 w2]; exact hx)
    (fun x eu => ?_)
  obtain ⟨s2, a1⟩ := x
  simp only [uncurry_apply_pair]
  obtain ⟨h1, h2⟩ := hcsc _ s1 s2 a1 e1 eu
  rw [sched.cur_sc.guard (gS := gS) s2 h1]
  refine tr_bind_same (fun csc ecsc => ?_)
  rw [sched.consumed.guard (gS := gS) s2 h2]
  refine tr_bind_same (fun u _ => ?_)
  rw [sporadic.sufficient.guard (gS := gS) ar s2 a1 csc u (hsuf _ s1 s2 a1 csc e1 eu ecsc)]
  refine tr_bind_same (fun b _ => ?_)
  refine tr_ite (fun _ => ?_) (fun _ h => h)
  exact fun h' => (hmid nx s1 s2 a1 enx e1 eu h').trans h'

end

end Fl4Proofs.P2.PathObl
