# gen 9: writes Fl4Proofs/P3/XTopJointKEntryU42.lean from XTopJointKEntryU41.lean
src=open('Fl4Proofs/P3/XTopJointKEntryU41.lean').read()
i0=src.index('set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU41`**')
i1=src.index('set_option maxHeartbeats 8000000 in\n/-- **U41 gives U40**')
u41=src[i0:i1]
st0=u41.index('theorem kernel_entry_reachU41'); pr=u41.index('   := by\n')
stmt=u41[st0:pr]  # statement text of U41
assert stmt.count('KFinAtR41')==1 and stmt.count('KFinEv41')==5
s42=stmt.replace('theorem kernel_entry_reachU41','theorem kernel_entry_reachU42').replace('KFinAtR41','KFinAtR42').replace('KFinEv41','KFinEv42')
s41=stmt.replace('theorem kernel_entry_reachU41','theorem kernel_entry_reachU41_of42')
call_args='arI AR MR hARI hA hnd hM hIp hKD hIo hIoa hPAi hIA hT hmax htu hRef hPI hSX hDR hMap hFpu hJ'
def proof(fn,conv):
    return f'''   := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, hSys, hIrq, hUs, hVm, hTr, hSU⟩ :=
    {fn} {call_args}
  refine ⟨Z, H, Cs, Ac, Lst, D, J, hX, hCB, hW, hI, hN, hR, hFl, hPg, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n c hct hn hfl hK hDL hFin
    exact hSys n c hct hn hfl hK hDL
      (fun x hx Z' H' Cs' Ac' Lst' D' s' a' hF J' => (hFin x hx Z' H' Cs' Ac' Lst' D' s' a' hF J').{conv})
  · intro w a1 hIh hE; exact hIrq w a1 hIh (hE.{conv})
  · intro n c hct hU hE; exact hUs n c hct hU (hE.{conv})
  · intro ad c ft hct hVm' hE; exact hVm ad c ft hct hVm' (hE.{conv})
  · intro v hct hv hE; exact hTr v hct hv (fun ev hev w hw => (hE ev hev w hw).{conv})
  · intro n hct hU hD hE; exact hSU n hct hU hD (fun ev hev w hw => (hE ev hev w hw).{conv})
'''
head='''/-
P3 (line p3J, gen 10): **`kernel_entry_reachU42`** = `kernel_entry_reachU41` with the idle half of the
per-entry `ArchSwF` [P] removed (it is a theorem where it is used).

* P3KGen1 / P3KFin / P3KGen: U41's proof transported (P3KXport) with `ArchSwF` ↦ `ArchSwF'` (ArchSwIdle:
  the idle half asks `IdleVt σ`, and is a theorem there, `archSwFI_of`). The pre-g7e finish path
  (`KFinAtR5/31/27/KFinAtR` records, `jat_finishJRNM/JRN/JRP`, `jat_scheduleSR2ZRP/FR2ZR/WP0FZR`) is moved
  onto the g7e scheduler chain (`jat_scheduleWP0FZRI` on the transported `schedule_refinesWP0FRA`, `RootFr`
  from `IdleVt` carried in the records as `FinRootR`); ScNextDomCFR's `schedule_refinesWP0FR` and the
  `cn_*0F` / `scnt_refines0F` chain leave the cone. Every other constant of U41's cone using these ↦ its
  kernel-checked copy `Fl4ProofsK…`.
* `KFinAtR42` = `KFinAtR41` with `arch : ArchSwFT` (the thread half only); `KFinEv42`.
  `KFinAtR42.toK` / `KFinEv42.toK` (into the transported records, with `archSwFI_of` from `ArchTotal`),
  `KFinAtR41.to42` / `KFinEv41.to42` (`ArchSwF → ArchSwFT`, the first half).
* **Premise diff U41 → U42**: the syscall clause's `KFinAtR41 …` ↦ `KFinAtR42 …` and every event's
  `KFinEv41 …` ↦ `KFinEv42 …` (`ArchSwF` ↦ its thread half `ArchSwFT`: the idle half dropped). No new
  premise: the idle half follows from `ArchTotal` (already U41's `hA`), with no determinism premise since
  the spec's CR3 write `setCurrentCr3` is a plain state update. Start (`JReachU40`) and conclusion
  verbatim. [W] 0.
* **`kernel_entry_reachU41_of42`**: U41's statement verbatim, from U42.

Named premises: U41's (XTopJointKEntryU41) with `KFinAtR41.arch : ArchSwF` [P] narrowed to
`KFinAtR42.arch : ArchSwFT` [P] (set_vm_root against archSwitchToThread). No sorry.
-/
import Fl4Proofs.P3.XTopJointKEntryU41
import Fl4Proofs.P3.P3KGen
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.SInvR.G5
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`KFinAtR41` with the thread half of `ArchSwF` only.** -/
structure KFinAtR42 (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) : Prop where
  /-- [P] `ArchSwFT`: FL4's `set_vm_root` refines `archSwitchToThread` (ArchSwIdle). -/
  arch : ArchSwFT st arI Z.N Z.T Z.C Z.c

/-- `KFinEv41` with `KFinAtR42`. -/
def KFinEv42 (AR : A → Fl4Spec.Cr3 → Prop) (ev : Fl4Spec.Event) (Kf : S → A → Prop) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x ∈ ((Fl4Spec.NonDetE.handleE (Fl4Spec.fl4HandleEvent (Z := Unit) true ev)
      (fun _ => Fl4Spec.withoutPreemption Fl4Spec.preemptionPath)).run σ).1,
    ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A),
      Kf s' a' → JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 → KFinAtR42 (L := L) arI AR Z' H' Cs' s' a' x.2

variable {arI}

theorem KFinAtR42.toK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR42 (L := L) arI AR Z H Cs s a σ) (hA : P0.ArchTotal arI) :
    Fl4ProofsK.P3.SInvR.G5.KFinAtR41 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch.toN hA⟩

theorem KFinAtR41.to42 {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs : Set U64} {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : KFinAtR41 (L := L) arI AR Z H Cs s a σ) :
    KFinAtR42 (L := L) arI AR Z H Cs s a σ :=
  ⟨h.arch.1⟩

theorem KFinEv42.toK {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (h : KFinEv42 (L := L) arI AR ev Kf σ) (hA : P0.ArchTotal arI) :
    Fl4ProofsK.P3.SInvR.G5.KFinEv41 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ).toK hA

theorem KFinEv41.to42 {AR : A → Fl4Spec.Cr3 → Prop} {ev : Fl4Spec.Event} {Kf : S → A → Prop}
    {σ : Fl4Spec.State Unit} (h : KFinEv41 (L := L) arI AR ev Kf σ) :
    KFinEv42 (L := L) arI AR ev Kf σ :=
  fun x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ => (h x hx Z' H' Cs' Ac' Lst' D' s' a' hK hJ).to42

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

'''
out=head+'set_option maxHeartbeats 8000000 in\n/-- **`kernel_entry_reachU42`** (module docstring). -/\n'+s42+proof('Fl4ProofsK.P3.SInvR.G5.kernel_entry_reachU41','toK hA')
out+='\nset_option maxHeartbeats 8000000 in\n/-- **U42 gives U41** (module docstring). -/\n'+s41+proof('kernel_entry_reachU42','to42')
out+='\nend\n\nend\n\nend Fl4Proofs.P3.SInvR.G5\n'
open('Fl4Proofs/P3/XTopJointKEntryU42.lean','w').write(out)
