/-
P3 (DESIGN.md §9), invariant line G4 (g4i, KENTRY-PLAN g4i): **the
induction where every FL4 event entry is proved** (no `JEvRef`).

* `JReachE4`: `JReachE3`'s `start` / `step` / `irq` / `user` / `vmf`, and in
  place of the generic `event` step the two FaultIP entries: `trap`
  (`int $N`, a vector below 256 [P]) and `sysU` (the unknown syscall through
  `handle_syscall`, under the [S] scope `UnkSys` / `NoDbgSys`). `irq` was
  already free of `ct ≠ idle`. `JReachE4.toE3`, `jreach_invE4`.
* `kernel_entry_reachE4`: at every `JReachE4` state, the native syscall
  entry (J37N's per-state premises), the interrupt entry from any current
  thread (`jEvRef_irqA`: g4i's idle case, no `ct ≠ idle`), the user-exception
  and VM-fault entries (`UserHw` / `VmfHw`), `int $N` (`jEvRef_trap`) and the
  unknown syscall (`jEvRef_sysU`: `UnkSys`, `NoDbgSys` [S], `FastFaultOK` [J]
  at the entry state, `StoreExt` [P]), each with its finish bundle `KFinEv` /
  `hFin`, ending related with `SInvX`, `MR` and `JReachE4` again. No clause
  takes `JEvRef`.
-/
import Fl4Proofs.P3.XTopJointKEntryEv6
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **The reachable joint states, every event entry proved** (module docstring). -/
inductive JReachE4 : S → A → Fl4Spec.State Unit → Prop
  | start {s : S} {a : A} {σ : Fl4Spec.State Unit} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
      {Lst : U64 → List U64} {D : Set U64} :
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ → VxE Z → SInvX σ → MR a σ.machineState → JReachE4 s a σ
  | step {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (c : Fl4Spec.Syscall) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → NativeSys n c →
      syscall.handle_syscall st arI s a n = ok (s', a') →
      ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 →
      RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | irq {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (w : U64) :
      JReachE4 s a σ → IrqHw AR MR a a1 σ w → syscall.handle_interrupt_entry st arI s a1 w = ok (s', a') →
      EvOut false .interrupt σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | user {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n c : U64) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → UserHw n c →
      syscall.handle_user_exception st arI s a n c = ok (s', a') →
      EvOut false (.userLevelFault n.bv c.bv) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | vmf {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (ad c : U64)
      (ft : Fl4Spec.VMFaultType) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
      syscall.handle_vm_fault st arI s a ad c = ok (s', a') →
      EvOut false (.vmFaultEvent ft) σ σ' → RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | trap {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (v : U64)
      (ev : Fl4Spec.Event) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → v.val < 256 → KEvSpec (.trap v) true ev →
      syscall.handle_trap_syscall st arI s a v = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'
  | sysU {s : S} {a : A} {σ : Fl4Spec.State Unit} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (n : I64)
      (ev : Fl4Spec.Event) :
      JReachE4 s a σ → σ.curThread ≠ σ.idleThread → UnkSys (L := L) n s → NoDbgSys (L := L) arI n s a →
      KEvSpec (.sysU n) true ev → syscall.handle_syscall st arI s a n = ok (s', a') → EvOut true ev σ σ' →
      RJM (L := L) arI AR MR s' a' σ' → JReachE4 s' a' σ'

variable {arI AR MR}

/-- Every `JReachE4` state is a `JReachE3` state (`trap` / `sysU` are `JReachE3.event` steps). -/
theorem JReachE4.toE3 {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachE4 (L := L) arI AR MR s a σ) :
    JReachE3 (L := L) arI AR MR s a σ := by
  induction h with
  | @start s a σ Z H Cs Ac Lst D J hvx hX hR => exact JReachE3.start J hvx hX hR
  | @step s a σ s' a' σ' n c _ hct hn hv hy hRJ ih => exact JReachE3.step n c ih hct hn hv hy hRJ
  | @irq s a a1 σ s' a' σ' w _ hI hv hO hRJ ih => exact JReachE3.irq w ih hI hv hO hRJ
  | @user s a σ s' a' σ' n c _ hct hU hv hO hRJ ih => exact JReachE3.user n c ih hct hU hv hO hRJ
  | @vmf s a σ s' a' σ' ad c ft _ hct hV hv hO hRJ ih => exact JReachE3.vmf ad c ft ih hct hV hv hO hRJ
  | @trap s a σ s' a' σ' v ev _ hct _ hK hv hO hRJ ih =>
    exact JReachE3.event (.trap v) true ev ih hK (fun _ => hct) hv hO hRJ
  | @sysU s a σ s' a' σ' n ev _ hct _ _ hK hv hO hRJ ih =>
    exact JReachE3.event (.sysU n) true ev ih hK (fun _ => hct) hv hO hRJ

/-- **The invariant** of `JReachE4`: `JAtZ` at some ghosts, `SInvX`, `MR`. -/
theorem jreach_invE4 (hnd : Fl4Spec.numDomains = 1) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (h : JReachE4 (L := L) arI AR MR s a σ) :
    (∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ VxE Z) ∧ SInvX σ ∧ MR a σ.machineState :=
  jreach_invE3 hnd h.toE3

end

end

end Fl4Proofs.P3
