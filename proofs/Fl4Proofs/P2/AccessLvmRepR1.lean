/-
# P2 (line lvm, gen 4): **`vcpu.report` on a guarded store** (bound VCPU case; split for check time)

`vcpu.report.guardP`: for a predicate `P` the report's four write kinds keep (P1's `RepSteps`, the buffer the one
looked up) and at which the final `set_thread_state TS_RUNNING` is guarded (`hfin`), the report on any store
answering its reads / writes (`RepG`) as `st` is the real one. No named premises.
-/
import Fl4Proofs.P2.AccessLvmRepR1a
import Fl4Proofs.P2.AccessLvmRepR1b
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section rep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [GRd gS st R] [GWr gS st W]

/-- **`vcpu.report` on a guarded store**, a VCPU bound: (module docstring): for a predicate `P` its four write kinds keep
(`RepSteps`, the buffer `b` the one looked up) and at which the final `set_thread_state` is guarded (`hfin`). -/
theorem vcpu.report.guardP1 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge v b : U64) {P : S → Prop} {vOk : U64 → Prop} (Rs : RepSteps st t (· = b) P vOk)
    (hfin : ∀ s1, P s1 →
      sched.set_thread_state gS s1 t sched.TS_RUNNING = sched.set_thread_state st s1 t sched.TS_RUNNING)
    (hP : P s) (hvw : R (core.num.U64.wrapping_add t 3664#u64))
    (hv : L.mem s (core.num.U64.wrapping_add t 3664#u64) = v)
    (hlb : msg.lookup_ipc_buffer gS s true t = msg.lookup_ipc_buffer st s true t)
    (hb : msg.lookup_ipc_buffer st s true t = ok b)
    (hok : v ≠ 0#u64 → vOk v) (G : RepG R W t v b) (hv0 : v ≠ 0#u64) :
    vcpu.report gS ar s a t badge = vcpu.report st ar s a t badge := by
  by_cases hp : L.mem s (core.num.U64.wrapping_add v vcpu.PENDING) = 0#u64
  · exact vcpu.report.guardP1b hA s a t badge v b Rs hfin hP hvw hv hlb hb hok G hv0 rfl hp
  · exact vcpu.report.guardP1a hA s a t badge v b Rs hfin hP hvw hv hlb hb hok G hv0 rfl hp

end rep

end Fl4Proofs.P2.PathObl
