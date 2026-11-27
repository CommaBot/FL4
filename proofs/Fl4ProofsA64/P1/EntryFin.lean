-- AArch64 port of Fl4Proofs.P1.EntryFin (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (int6, FL4 #80 / #85): **the kernel-entry composites that end in `finish`**,
from par/a6x's `XG`-carrying composites (`EntryXGTop`) and `finish.entry`.

Since #80 / #85 a signal (`send_signal`, in `schedule`'s timers and on the IRQ
path) may complete a `TS_RUNNING_VM` thread's full-state VMEnter and write
its IPC buffer, so `finish` needs the buffer placement at its state
(`EntryHyps0.bufAt`, from `XG`), and the IRQ path needs `send_signal` to keep
`XG` (`SigXG`). Here:

* `sigXG_holds`: `SigXG` from `send_signal.tinvF`'s footprint (`FootDU`, with
  the user words `U`), `SigXG.of_ipcFoot`;
* `kernel_entry.entry` (QueueEntry's, which ended here before; one more
  hypothesis, the start tuple's `XferHyps`, and `IK : IbKeep`, like `TX`):
  `kernel_entry.entryXG` with `finish.entry`;
* `kernel_entry.entry_of` (moved from QueueInvAll) and `kernel_entry.entry_of2`
  (moved from QueueEntryGaps), `IK` added like `TX`.

a64 (AArch64 port): over the A forms (`TmoXGA`, `EHsA`, `EntryHypsA.of_gaps`, `finish.entryA`); the syscall
entry is `handle_syscall_general` (`fast := false`; A64 has no `SyscallGen`); `finish.entryA` needs no
`IbKeep`, so `IK` is dropped; `kernel_entry.entry_of2` uses `InvGaps2F` (QueueScBindVm: **[P] field
`scBindOwn`**) in place of `InvGaps2` (whose [J] `scBindRv` is false). `sigXG_holds` passes `SigXG`'s
`RunVcpuInv` hypothesis to `send_signal.tinvF`. Named premises: those of `EntryHypsA` / `P3Place` /
`InvGaps` / `InvGaps2F` / `CdtHyps` (as the originals; [J] `rvAt`, [P] `vmpl`, [P] `scBindOwn`); nothing new.
-/
import Fl4ProofsA64.P1.EntryXGTop
import Fl4ProofsA64.P1.QueueScBindVm  -- a64: `InvGaps2F`
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {P3Ok : S → Prop}
variable {A : Type _} {ar : machine.Arch A} {U : Set U64}

/-- **`send_signal` keeps `XG`** (`SigXG`): its footprint (`send_signal.tinvF`:
kernel words, debug-list words and the user words `U`) is an `IpcW`
footprint; the buffer placement from `XferHyps.buf` at the `XG` state. -/
theorem sigXG_holds (hA : P0.ArchTotal ar) : SigXG st ar :=
  SigXG.of_ipcFoot fun T Cs Ω H Sg Rp Scs Nt Z U P3Ok E Ac s a n badge hG h hU hn hH hRV => by
    obtain ⟨Q, R, x0⟩ := BXI.xs (sx := 0#u64) (BlkOK.bxi h) hU
    refine WP.spec_mono (notification.send_signal.tinvF hA s a n badge h.tinv hn hH (hU.usrW h)
      (fun y hy => E.buf _ _ _ _ s y hG x0.1 hy) hRV) fun r hr => ?_  -- a64: `hRV` (SigXG's A64 hypothesis)
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact WritesIn.mono hr.2.1 fun _ hb =>
      hb.elim (fun hb => hb.elim Or.inl fun hd => Or.inr (Or.inr (Or.inr hd))) fun hu => Or.inr (Or.inl (Or.inr hu))

/-- **Native kernel entries keep `EntryInv`** (`handle_syscall` excluding
VMEnter, `handle_interrupt_entry` for any IRQ), with the active set possibly
shrinking (SC deletion) and the heap possibly growing (retype): the entry
ends over some admissible set tuple.  The hypotheses not proved in P1 are
collected in `EntryHyps`, for every admissible tuple (`EH`), and the start
tuple's transfer placement facts `XH` (P3's); `hA` is P0's arch totality,
`TX` is a P1 lemma (`tmoXG_holds`; a64: no `IK`). (int6: moved from
QueueEntry; `kernel_entry.entryXG` with `finish.entry`.)
**Vacuous** (p1g): its premise bundles are contradictory with the `EntryInv` premise
(P1/EntryVacuous). Use P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29),
which has this conclusion from U29's premises. -/
theorem kernel_entry.entry (hA : P0.ArchTotal ar) (TX : TmoXGA st ar) {Adm : PSets → Prop}
    (EH : ∀ σ, Adm σ → EHsA st ar Adm Cs U P3Ok σ) (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩)
    (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entryXG hA TX (sigXG_holds hA) EH hσ XH s a hP h
    (fun σ hσ' Ac s a h g => WP.spec_mono (syscall.finish.entryA hA (EH σ hσ').2 (EH σ hσ').1.toEntryHyps0A s a h g)
      fun r hr => by obtain ⟨s', a'⟩ := r; obtain ⟨Ac', h'⟩ := hr; exact ⟨σ, hσ', Ac', h'⟩)
    fun σ hσ' Ac s h => ⟨σ, hσ', Ac, h⟩

/-- **Native kernel entries keep `EntryInv`, from the decode gaps `InvGaps`
and the P3 placement facts `P3Place`** of every admissible tuple; the entry
ends over some admissible tuple. (int6: moved from QueueInvAll.)
**Vacuous** (p1g): its premise bundles are contradictory with the `EntryInv` premise
(P1/EntryVacuous). Use P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29),
which has this conclusion from U29's premises. -/
theorem kernel_entry.entry_of {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧
      InvGaps st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry hA TX (fun σ h' => ⟨EntryHypsA.of_gaps hA h' (fun σ'' h'' => (GF σ'' h'').1) (GF σ h').1
    (GF σ h').2.1, (GF σ h').2.2⟩) hσ (GF _ hσ).1.xfer s a hP h

/-- **Native kernel entries keep `EntryInv`**, from `InvGaps2F` (a64), `CdtHyps`
and `P3Place` of every admissible tuple. (int6: moved from QueueEntryGaps.)
**Vacuous** (p1g): its premise bundles are contradictory with the `EntryInv` premise
(P1/EntryVacuous). Use P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29),
which has this conclusion from U29's premises. -/
theorem kernel_entry.entry_of2 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (TX : TmoXGA st ar)
    (GF : ∀ σ : PSets, Adm σ → P3Place st ar σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ CdtHyps st σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z P3Ok ∧
      InvGaps2F st ar Adm σ.T Cs σ.Ω σ.H σ.Sg σ.Rp σ.Scs σ.Nt σ.Z U P3Ok ∧ ∀ n ∈ σ.Nt, σ.H n = some .ntfn)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall_general st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) :=
  kernel_entry.entry_of hA TX (fun σ h' => ⟨(GF σ h').1, (GF σ h').2.2.1.gaps hA (GF σ h').1.xfer (GF σ h').2.1,
    (GF σ h').2.2.2⟩) hσ s a hP h

end

end Fl4ProofsA64.P1
