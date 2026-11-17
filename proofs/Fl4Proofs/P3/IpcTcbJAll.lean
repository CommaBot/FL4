/-
P3 (DESIGN.md §9), TCB invocations: **the IPC side's TCB leaves from
`JAtZ`, bundled** (`TcbXIpc`, CSpace's `decode_invocation_threadJAt`'s
`hI`): `tcbXIpc_ofJ`.
-/
import Fl4Proofs.P3.IpcSchedTailJ
import Fl4Proofs.P3.IpcReadRegsJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
open Fl4Proofs.P3.Notif (inClass released)

set_option maxHeartbeats 8000000 in
/-- **`TcbXIpc` from `JAtZ`** at the decode's state (module docstring).
Named, besides `JAtZ` and CSpace's `JStepHyps`: no reschedule pending
(P1's `DecPre.act`); the target among the TCBs; the decode's facts (the
target not the caller for ReadRegisters, the caller's buffer mapped and the
syscall arguments for WriteRegisters, a thread cap's object among the TCBs
for CopyRegisters, the notification to bind among the notifications and not
at 0); at every `XTopAt` of the typed heap the caller's IPC buffer valid
[global]; `SuspendKeeps` and `InstallJ` [J-step]; SetSchedParams' spec facts
after the install (`hSP`); the platform's facts [P]. -/
theorem tcbXIpc_ofJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit} {p ct buf : U64}
    {argsU : List U64} {blk call don : Bool}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hJS : JStepHyps (L := L) arI AR Z.th)
    (hres : σ.schedulerAction = .resumeCurThread) (hcur : σ.curThread = ct.bv) (hpT : p ∈ Z.T)
    (hpne : p ≠ ct)
    (hbuf : buf ≠ 0#u64 → ∃ sp, BufMap Z.B buf sp)
    (hargs : ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      ∀ (i : U64) x, argsU[i.val]? = some x → msg.syscall_arg st s1 ct buf i = ok x)
    (hsT : ∀ src : U64, (∃ x, IsSlot Z.th x ∧ capV (L.mem s) x = .Thread src) → src ∈ Z.T)
    (hqN : ∀ q, L.mem s (P1.boundA p) = 0#u64 → L.mem s (Notif.nBoundA q) = 0#u64 → q ∈ Z.N ∧ q ≠ 0#u64)
    (hZ : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Endp.IpcBufCapOK σ' ∧ Endp.BufCover Z'.T Z'.B σ' ∧ Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (hSK : SuspendKeeps st arI Z H Cs) (hJ2 : InstallJ (L := L) arI AR Z.th s σ ct)
    (hSP : ∀ (σ1 σ2 : Fl4Spec.State Unit) (p : U64) (sco : Option (Option Fl4Spec.ObjRef)) (ssl : Fl4Spec.CslotPtr)
      (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr), ScDec σ p.bv sco →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
      SpecPost σ2 p.bv sco ∧ ∀ v, sco = some (some v) → ∀ x y n, σ2.kheap p.bv = some (.tcb x) →
        σ2.kheap v = some (.schedContext y n) → Fl4Spec.runnable x.tcbState = false → inClass x.tcbState →
        Fl4Spec.scActive y = true → released σ2 y)
    (hStT : P0.StoreTotal st) (hArT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    (hmb : ∀ a, sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄) :
    TcbXIpc (L := L) arI AR Z.th s ar σ p ct buf argsU blk call don where
  readRegs := readRegsXHypJ J hJS hcur hpne hpT hZ
  writeRegs := writeRegsXHypJ J hJS hcur hpT (J.thT ct (J.xtop.curTcb hcur).1) hbuf hargs hmb
  copyRegs := copyRegsXHypJ J hJS hcur hpT hsT hSK hmb
  setPrio := fun _ _ hst hv => setPrioXLeafJ J hJS hst hv hpT hres
  schedTail := schedTailXHypJ arI hStT hArT hAK hTA hSP hJ2
  suspend := fun _ hst => suspendXLeafJ J hJS hst hpT
  resume := fun _ hst => resumeXLeafJD J hJS hst hpT (hmb ar)
  bind := fun q h0 h1 _ hst => bindXLeafJ J hJS hst hpT (hqN q h0 h1).1 (hqN q h0 h1).2
  unbind := fun h0 _ hst => unbindXLeafJ J hJS hst h0 hpT

end

end

end Fl4Proofs.P3
