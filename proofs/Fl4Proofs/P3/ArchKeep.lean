/-
P3 (DESIGN.md §9): **the arch relation through the kernel paths** (`ARKeep`).

`XTopAt`'s arch relation `AR a cr` is between FL4's abstract arch state `a`
and the spec's CR3. The kernel paths change `a` only by the arch operations
that return a new state; `ARKeep AR` says each of those used on the IPC and
SchedContext paths keeps `AR` at every CR3 (and succeeds):

* `now`, `set_deadline` (the timer), `send_reschedule`, `remote_stall` (the
  IPIs), `fpu_flush`, `fpu_release`, `fpu_sanitise`, `fpu_reload` (the lazy
  FPU), `vcpu_barrier`.

The queries (`ticks_to_us`, `us_to_ticks`, `kernel_wcet_ticks`, `max_us`,
...) return no new arch state, so need no field.

From `ARKeep` and P0's totality (`StoreTotal`, `ArchTotal`), each function on
the IPC tails that threads the arch state keeps `AR` (`AK.*`), so the three
tails of `IpcVsFrame` do (`AK.send_tail`, `AK.signal_tail`, `AK.reply_tail`).
-/
import Fl4Proofs.P0.Auto
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

section
variable {A C : Type} (arI : machine.Arch A)

/-- **The arch operations that return a new arch state keep `AR`** at every
CR3 (module docstring). -/
structure ARKeep (AR : A → C → Prop) : Prop where
  now : ∀ a c, AR a c → arI.now a ⦃ r => AR r.2 c ⦄
  set_deadline : ∀ a d c, AR a c → arI.set_deadline a d ⦃ a' => AR a' c ⦄
  send_reschedule : ∀ a m c, AR a c → arI.send_reschedule a m ⦃ a' => AR a' c ⦄
  remote_stall : ∀ a cpu c, AR a c → arI.remote_stall a cpu ⦃ a' => AR a' c ⦄
  fpu_flush : ∀ a t c, AR a c → arI.fpu_flush a t ⦃ a' => AR a' c ⦄
  fpu_release : ∀ a t c, AR a c → arI.fpu_release a t ⦃ a' => AR a' c ⦄
  fpu_sanitise : ∀ a t c, AR a c → arI.fpu_sanitise a t ⦃ a' => AR a' c ⦄
  fpu_reload : ∀ a t c, AR a c → arI.fpu_reload a t ⦃ a' => AR a' c ⦄
  vcpu_barrier : ∀ a c, AR a c → arI.vcpu_barrier a ⦃ a' => AR a' c ⦄

end

/-! ## The arch state through the IPC paths -/

open Lean Elab Tactic Meta in
/-- A call that threads the arch state, at the head of the program (bound or
in tail position): its `AK` lemma (`AK.<f>` for `f`), or `ARKeep`'s field for
an arch operation. -/
elab "ak_call" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Aeneas.Std.WP.spec do throwError "ak_call: not a spec"
  let args := target.getAppArgs
  let program := args[args.size - 2]!
  let program ← match ← Lean.Meta.reduceMatcher? program with
    | Lean.Meta.ReduceMatcherResult.reduced e => pure e.headBeta
    | _ => pure program
  let (m, bound) := match Aeneas.Step.getBindArgs? program with
    | some (m, _) => (m, true)
    | none => (program, false)
  let some n := m.getAppFn.constName? | throwError "ak_call: no constant head"
  let hS := mkIdent `hS
  let hA := mkIdent `hA
  let hK := mkIdent `hK
  if n.getPrefix == ``fl4_core.machine.Arch then
    let f := mkIdent (`ARKeep ++ Name.mkSimple n.getString!)
    let k := (m.getAppNumArgs) - 3
    let us : Array (TSyntax `term) := Array.replicate (k + 2) (← `(_))
    unless bound do throwError "ak_call: arch operation in tail position"
    evalTactic (← `(tactic| refine WP.spec_bind ($f $hK $us* (by assumption)) (fun _ _ => ?_)))
  else
    let ak := `Fl4Proofs.P3.AK ++ Name.mkSimple (((n.replacePrefix `fl4_core .anonymous).toString).replace "." "_")
    unless (← getEnv).contains ak do throwError "ak_call: not an arch-threading function"
    let f := mkIdent ak
    if bound then
      evalTactic (← `(tactic| refine WP.spec_bind ($f $hS $hA $hK (by assumption)) (fun _ _ => ?_)))
    else
      evalTactic (← `(tactic| exact $f $hS $hA $hK (by assumption)))

/-- Close the walk: `AR` at the returned arch state, or P0's side conditions. -/
macro "ak_close" : tactic => `(tactic| try (first | assumption | (simp only at *; assumption) | p0_close))

/-- Step through a body: the arch-threading calls by `ak_call`, the others by
P0's totality. -/
macro "ak_walk" : tactic => `(tactic|
  ((repeat' (first | ak_call | p0_ite_head | (simp only [bind_tc_ok, bind_ok, bind_assoc_eq, Aeneas.Std.bind_assoc, Aeneas.Std.uncurry]) | p0_cases_prod | (dsimp only) | step | split)) <;> ak_close))

section
variable {S A C : Type} {st : machine.Store S} {arI : machine.Arch A} {AR : A → C → Prop}
  (hS : P0.StoreTotal st) (hA : P0.ArchTotal arI) (hK : ARKeep arI AR) {c : C}
include hS hA hK
set_option linter.unusedSectionVars false

theorem AK.debug_configure_single_stepping {s : S} {a : A} {t : obj.Tcb} {bp : Std.U64} {n_instr : Std.U64} {is_reply : Bool} (h : AR a c) :
    debug.configure_single_stepping st arI s a t bp n_instr is_reply ⦃ r => AR r.2.2 c ⦄ := by
  unfold debug.configure_single_stepping; ak_walk

theorem AK.smp_migrate_tcb {s : S} {a : A} {t : obj.Tcb} {cpu : Std.U64} (h : AR a c) :
    smp.migrate_tcb st arI s a t cpu ⦃ r => AR r.2 c ⦄ := by
  unfold smp.migrate_tcb; ak_walk

theorem AK.smp_remote_reschedule {s : S} {a : A} {cpu : Std.U64} (h : AR a c) :
    smp.remote_reschedule st arI s a cpu ⦃ r => AR r.2 c ⦄ := by
  unfold smp.remote_reschedule; ak_walk

theorem AK.smp_remote_tcb_stall {s : S} {a : A} {t : obj.Tcb} (h : AR a c) :
    smp.remote_tcb_stall st arI s a t ⦃ r => AR r.2 c ⦄ := by
  unfold smp.remote_tcb_stall; ak_walk

theorem AK.schedcontext_donate {s : S} {a : A} {sc : obj.Sc} {«to» : obj.Tcb} (h : AR a c) :
    schedcontext.donate st arI s a sc «to» ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.donate; ak_walk

theorem AK.ipc_reply_push {s : S} {a : A} {caller : obj.Tcb} {callee : obj.Tcb} {r : obj.Reply} {can_donate : Bool} (h : AR a c) :
    ipc.reply_push st arI s a caller callee r can_donate ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.reply_push; ak_walk

theorem AK.endpoint_send_ipc {s : S} {a : A} {blocking : Bool} {do_call : Bool} {badge : Std.U64} {can_grant : Bool} {can_grant_reply : Bool} {can_donate : Bool} {thread : obj.Tcb} {ep_ptr : Std.U64} (h : AR a c) :
    endpoint.send_ipc st arI s a blocking do_call badge can_grant can_grant_reply can_donate thread ep_ptr ⦃ r => AR r.2 c ⦄ := by
  unfold endpoint.send_ipc; ak_walk

theorem AK.faults_handle_fault_reply {s : S} {a : A} {receiver : obj.Tcb} {sender : obj.Tcb} (h : AR a c) :
    faults.handle_fault_reply st arI s a receiver sender ⦃ r => AR r.2.2 c ⦄ := by
  unfold faults.handle_fault_reply; ak_walk

theorem AK.faults_send_fault_ipc {s : S} {a : A} {t : obj.Tcb} {handler : capability.Cap} {can_donate : Bool} {f : error.Fault} (h : AR a c) :
    faults.send_fault_ipc st arI s a t handler can_donate f ⦃ r => AR r.2.2 c ⦄ := by
  unfold faults.send_fault_ipc; ak_walk

theorem AK.faults_handle_timeout {s : S} {a : A} {t : obj.Tcb} {f : error.Fault} (h : AR a c) :
    faults.handle_timeout st arI s a t f ⦃ r => AR r.2 c ⦄ := by
  unfold faults.handle_timeout; ak_walk

theorem AK.ipc_cancel_ipc {s : S} {a : A} {t : obj.Tcb} (h : AR a c) :
    ipc.cancel_ipc st arI s a t ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.cancel_ipc; ak_walk

theorem AK.ipc_reply_pop {s : S} {a : A} {r : obj.Reply} {t : obj.Tcb} (h : AR a c) :
    ipc.reply_pop st arI s a r t ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.reply_pop; ak_walk

theorem AK.ipc_reply_remove {s : S} {a : A} {r : obj.Reply} {t : obj.Tcb} (h : AR a c) :
    ipc.reply_remove st arI s a r t ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.reply_remove; ak_walk

theorem AK.ipc_do_reply_transfer {s : S} {a : A} {sender : obj.Tcb} {r : obj.Reply} {grant : Bool} (h : AR a c) :
    ipc.do_reply_transfer st arI s a sender r grant ⦃ r => AR r.2 c ⦄ := by
  unfold ipc.do_reply_transfer; ak_walk

theorem AK.schedcontext_resume {s : S} {a : A} {sc : obj.Sc} (h : AR a c) :
    schedcontext.resume st arI s a sc ⦃ r => AR r.2 c ⦄ := by
  unfold schedcontext.resume; ak_walk

theorem AK.notification_maybe_donate_sched_context {s : S} {a : A} {t : obj.Tcb} {n : obj.Ntfn} (h : AR a c) :
    notification.maybe_donate_sched_context st arI s a t n ⦃ r => AR r.2 c ⦄ := by
  unfold notification.maybe_donate_sched_context; ak_walk

theorem AK.notification_send_signal {s : S} {a : A} {n_ptr : Std.U64} {badge : Std.U64} (h : AR a c) :
    notification.send_signal st arI s a n_ptr badge ⦃ r => AR r.2 c ⦄ := by
  unfold notification.send_signal; ak_walk


/-- **The IPC tails of `IpcVsFrame`** keep `AR`: the restart, then
`send_ipc`, `send_signal` or `do_reply_transfer`. -/
theorem AK.send_tail {s : S} {a : A} {ct : Std.U64} {blk call : Bool} {b : Std.U64} {g gr don : Bool} {p : Std.U64}
    (h : AR a c) : (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← endpoint.send_ipc st arI s1 a blk call b g gr don ct p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => AR r.2.2 c ⦄ := by
  ak_walk

theorem AK.signal_tail {s : S} {a : A} {ct p b : Std.U64} (h : AR a c) : (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← notification.send_signal st arI s1 a p b
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => AR r.2.2 c ⦄ := by
  ak_walk

theorem AK.reply_tail {s : S} {a : A} {ct p : Std.U64} {g : Bool} (h : AR a c) : (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s2, a1) ← ipc.do_reply_transfer st arI s1 a ct p g
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2, a1)) ⦃ r => AR r.2.2 c ⦄ := by
  ak_walk

end

/-- **The partial-correctness form** of a total triple (for callers that
combine `AK.*` with their own specs): every `ok` outcome satisfies the post. -/
theorem spec_ok_post {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) {v : α} (hv : m = ok v) : P v := by
  rw [hv, WP.spec_ok] at h; exact h

end Fl4Proofs.P3
