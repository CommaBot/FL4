/-
# P1: the serial VM exit `syscall.handle_vcpu_exit` keeps `EntryInv` (line vexit)

`handle_vcpu_exit s a irq stalled` (fl4-core `syscall.rs` 790–799) runs, unless a
remote stall already did it, `update_timestamp`, `vcpu.check` of the current
thread and `check_budget` (`vexit_pre`); then `handle_interrupt` when an IRQ came
(`vexit_irq`); then `finish` (`handle_vcpu_exit_split`). Each step has a P1
lemma:

* `update_timestamp`: `sched.update_timestamp.bxc` and `EntryInv.of_step` give
  `EntryInv` after it;
* `vcpu.check`: `vcpu.check.vck` on a `TS_RUNNING_VM` current thread,
  `check_of_ne` off it;
* `check_budget`: `sched.check_budget.allG`, with a guard `G` closed under
  `Foot` and a timeout hypothesis `TmoKG … G`;
* `handle_interrupt`: `interrupt.handle_interrupt.bxi`;
* `finish`: `sched.schedule.entry`, `sched.activate_thread.entry`, then
  `vcpu.check.entry` (as `syscall.finish.entry`, without `EntryHyps0`).

**`syscall.handle_vcpu_exit.entry`**: from `EntryInv` at the entry state, the
exit state satisfies `EntryInv` (same sets). It does **not** take the
`EntryHyps0` / `P3Place` bundles (contradictory, P1/EntryVacuous). The facts
those bundles supplied as fields over every state are premises here, each
pinned to the run's own intermediate states (Hoare triples over the prefix
programs `update_timestamp`, `vexit_pre`, `vexit_irq`, `finish_old`), so
EntryVacuous's refutations (which build an arbitrary `BXI` state) do not apply
to them:

* `hUt` [P] (the `vmpl` placement, at the state `update_timestamp` leaves):
  `VmPl` (the current thread's IPC buffer and its VCPU's `PENDING` word in the
  user words `U`, when it is `TS_RUNNING_VM`), and the guard `G` at the state
  `vcpu.check` leaves;
* `htmo` [P] (`TmoKG … G`: a timeout fault raised by `check_budget` from a
  `G`-state keeps the invariants and `G`; `EntryHyps0.tmoOK`'s content);
* `hI` [P] (at the state `vexit_pre` leaves, when an IRQ came): the IRQ slots'
  notification caps name heap notifications (`IrqNtAt`, `EntryHyps0.irqcap`'s
  content) and `BufAt` (`EntryHyps0.bufAt`'s);
* `hF` [P] (at the state `vexit_irq` leaves): `BufAt` for `schedule`, and
  `VmPl` at the state `finish_old` leaves (for `finish`'s `vcpu.check`).
* `IK : IbKeep` (arch, as every `finish` user takes it).

`vcpu_exit_local.entry` / `vm_timer_local.entry`: the same for the x86 local
VM-exit paths (`localvm.handle_vcpu_exit_local`, `handle_vm_timer_irq_local`),
from lvm's `vcpu_exit_local_triple` / `vm_timer_local_triple`.
-/
import Fl4Proofs.P1.QueueKeeps
import Fl4Proofs.P1.LocalVmExit
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- The first block of `handle_vcpu_exit` (the non-stalled prefix). -/
def vexit_pre (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (stalled : Bool) : Result (S × A) :=
  if stalled
  then ok (s, a)
  else
    do
    let (s2, a2) ← sched.update_timestamp st ar s a
    let ct ← sched.cur_thread st s2
    let (s3, a3) ← vcpu.check st ar s2 a2 ct
    let (_, s4, a4) ← sched.check_budget st ar s3 a3
    ok (s4, a4)

/-- `handle_vcpu_exit` up to `finish`. -/
def vexit_irq (st : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (irq : U64) (stalled : Bool) :
    Result (S × A) := do
  let (s1, a1) ← vexit_pre st ar s a stalled
  if irq != syscall.NO_IRQ
  then interrupt.handle_interrupt st ar s1 a1 irq
  else ok (s1, a1)

omit L in
theorem handle_vcpu_exit_split (s : S) (a : A) (irq : U64) (stalled : Bool) :
    syscall.handle_vcpu_exit st ar s a irq stalled = (do
      let (s2, a2) ← vexit_irq st ar s a irq stalled
      syscall.finish st ar s2 a2) := by
  unfold syscall.handle_vcpu_exit vexit_irq
  rw [Std.bind_assoc]
  exact congrArg (Std.bind (vexit_pre st ar s a stalled)) (funext fun x => by obtain ⟨s1, a1⟩ := x; rfl)

/-- The placement `vcpu.check` of the current thread needs when it is
`TS_RUNNING_VM` (`vcpu.check.vck`'s `hU`/`hbuf`/`hpw`; `EntryHyps0.vmpl`'s
content at one state). -/
def VmPl (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (U : Set U64) (s : S) : Prop :=
  L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM →
    BufAt st T Cs H Sg Scs Z U s ∧
    (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U)

/-- The IRQ slots' notification caps name heap notifications (at one state). -/
def IrqNtAt (st : machine.Store S) [L : LawfulStore st] (Nt : Set U64) (s : S) : Prop :=
  ∀ i : U64, i.val < 128 → obj.Slot.cap st (irqSlotA (L.ksb s) i) s ⦃ c => ∀ ptr b0 b1 b2,
    c = .Notification ptr b0 b1 b2 → ptr ∈ Nt ⦄

/-- `vcpu.check` of the current thread keeps `EntryInv` (and a guard it is
given at its result). -/
theorem vexit_check {Ac : Set U64} (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {G : S → Prop}
    (s : S) (a : A) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hV : VmPl st T Cs H Sg Scs Z U s)
    (hG : vcpu.check st ar s a (L.curW s) ⦃ s' _ => G s' ⦄) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ G s' ⦄ := by
  by_cases hv : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM
  · obtain ⟨hBA, hpw⟩ := hV hv
    have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
    refine WP.spec_mono (WP.spec_and (vcpu.check.vck hA hNt s a h hBA.1 (hBA.2 _ hcT) hpw) hG) ?_
    rintro ⟨s', a'⟩ ⟨h1, h2⟩
    simp only [WP.uncurry'_pair] at h1 h2 ⊢
    exact ⟨h1.1, h2⟩
  · rw [check_of_ne ar s a _ hv] at hG ⊢
    rw [WP.spec_ok] at hG ⊢
    exact ⟨h, hG⟩

/-- **The prefix of `handle_vcpu_exit` keeps the invariants** (`BXI`). -/
theorem vexit_pre.bxi {Ac : Set U64} (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {G : S → Prop}
    (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G)
    (hUt : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 => VmPl st T Cs H Sg Scs Z U s1 ∧
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => G s2 ⦄ ⦄) :
    vexit_pre st ar s a stalled ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold vexit_pre
  cases stalled with
  | true => exact (WP.spec_ok _).2 (EntryInv.bxi h)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (WP.spec_and (sched.update_timestamp.bxc hA s a (EntryInv.bxi h)) (hUt rfl)) ?_
    rintro ⟨s1, a1⟩ ⟨⟨⟨hb1, c1, -⟩, n1, f1⟩, hV1, hG1⟩
    have E1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := EntryInv.of_step h hb1.blk c1 n1.2.2 (Or.inl n1.1) f1
    show (do
      let ct ← sched.cur_thread st s1
      let (s3, a3) ← vcpu.check st ar s1 a1 ct
      let (_, s4, a4) ← sched.check_budget st ar s3 a3
      ok (s4, a4)) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄
    rw [cur_thread_ok]; simp only [bind_ok]
    refine WP.spec_bind (vexit_check hA hNt s1 a1 E1 hV1 hG1) ?_
    rintro ⟨s2, a2⟩ ⟨E2, g2⟩
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, -, hcA, hna, hcsc⟩ := E2
    refine WP.spec_bind (sched.check_budget.allG hA s2 a2 Q R h0 hB hX hS.sg hS hcsc hna hcA hGF g2 htmo) ?_
    rintro ⟨r, s3, a3⟩ ⟨⟨h3, -⟩, -⟩
    exact (WP.spec_ok _).2 h3

/-- **`handle_vcpu_exit` up to `finish` keeps the invariants.** -/
theorem vexit_irq.bxi {Ac : Set U64} (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {G : S → Prop}
    (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G)
    (hUt : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 => VmPl st T Cs H Sg Scs Z U s1 ∧
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => G s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true →
      IrqNtAt st Nt s1 ∧ BufAt st T Cs H Sg Scs Z U s1 ⦄) :
    vexit_irq st ar s a irq stalled ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold vexit_irq
  refine WP.spec_bind (WP.spec_and (vexit_pre.bxi hA hNt s a stalled h hGF htmo hUt) hI) ?_
  rintro ⟨s1, a1⟩ ⟨h1, i1⟩
  try simp only [WP.uncurry'_pair] at h1 i1 ⊢
  split
  · rename_i hirq
    obtain ⟨hc, hBA⟩ := i1 hirq
    exact interrupt.handle_interrupt.bxi hA hNt s1 a1 irq h1 hc hBA
  · exact (WP.spec_ok _).2 h1

/-- `finish` from a `BXI` state with `BufAt`, and the `vcpu.check` placement at
the state `finish_old` leaves, ends in `EntryInv` (`syscall.finish.entry`
without `EntryHyps0`). -/
theorem syscall.finish.entryV {Ac : Set U64} (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hV : syscall.finish_old st ar s a ⦃ s1 _ => VmPl st T Cs H Sg Scs Z U s1 ⦄) :
    syscall.finish st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  rw [finish_eq_old]
  refine WP.spec_bind (Pₘ := fun r : S × A => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      VmPl st T Cs H Sg Scs Z U r.1) (WP.spec_and ?_ hV) ?_
  · unfold syscall.finish_old
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
    refine WP.spec_bind (sched.schedule.entry hA IK hNt s a Q R h0 hB hS hX hSg hBA) ?_
    rintro ⟨s1, a1⟩ h1
    exact WP.spec_mono (sched.activate_thread.entry hA s1 a1 h1) fun r hr => by obtain ⟨s', a'⟩ := r; exact hr
  · rintro ⟨s2, a2⟩ ⟨h2, v2⟩
    show (do let t ← sched.cur_thread st s2; vcpu.check st ar s2 a2 t) ⦃ _ ⦄
    rw [cur_thread_ok]; simp only [bind_ok]
    refine WP.spec_mono (vexit_check (G := fun _ => True) hA hNt s2 a2 h2 v2
      (WP.spec_mono (P0.vcpu.check.p0 st ar s2 a2 (L.curW s2) L.total hA) fun _ _ => trivial)) ?_
    rintro ⟨s', a'⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    exact hh.1

/-- **(P1, vexit) The serial VM exit `handle_vcpu_exit` keeps `EntryInv`**
(module docstring; premises `htmo`, `hUt`, `hI`, `hF` [P], pinned to the run's
states, and `IK`). -/
theorem syscall.handle_vcpu_exit.entry {Ac : Set U64} (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (irq : U64) (stalled : Bool)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {G : S → Prop}
    (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G)
    (hUt : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 => VmPl st T Cs H Sg Scs Z U s1 ∧
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => G s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true →
      IrqNtAt st Nt s1 ∧ BufAt st T Cs H Sg Scs Z U s1 ⦄)
    (hF : vexit_irq st ar s a irq stalled ⦃ s2 a2 => BufAt st T Cs H Sg Scs Z U s2 ∧
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => VmPl st T Cs H Sg Scs Z U s3 ⦄ ⦄) :
    syscall.handle_vcpu_exit st ar s a irq stalled ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  rw [handle_vcpu_exit_split]
  refine WP.spec_bind (WP.spec_and (vexit_irq.bxi hA hNt s a irq stalled h hGF htmo hUt hI) hF) ?_
  rintro ⟨s2, a2⟩ ⟨h2, hBA, hV⟩
  try simp only [WP.uncurry'_pair] at h2 hBA hV ⊢
  exact syscall.finish.entryV hA IK hNt s2 a2 h2 hBA hV

/-- **The x86 local VM exit (no IRQ) keeps `EntryInv`** on its accepted runs:
`handle_vcpu_exit … NO_IRQ false`'s triple through lvm's
`vcpu_exit_local_triple`. Premises as `syscall.handle_vcpu_exit.entry`'s. -/
theorem vcpu_exit_local.entry {Ac : Set U64} (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (v n : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {G : S → Prop}
    (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G)
    (hUt : sched.update_timestamp st ar s a ⦃ s1 a1 => VmPl st T Cs H Sg Scs Z U s1 ∧
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => G s2 ⦄ ⦄)
    (hF : vexit_irq st ar s a syscall.NO_IRQ false ⦃ s2 a2 => BufAt st T Cs H Sg Scs Z U s2 ∧
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => VmPl st T Cs H Sg Scs Z U s3 ⦄ ⦄) :
    localvm.handle_vcpu_exit_local st ar s a v n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hI : vexit_pre st ar s a false ⦃ s1 _ => (syscall.NO_IRQ != syscall.NO_IRQ) = true →
      IrqNtAt st Nt s1 ∧ BufAt st T Cs H Sg Scs Z U s1 ⦄ :=
    WP.spec_mono (vexit_pre.bxi hA hNt s a false h hGF htmo fun _ => hUt) fun r _ => by
      obtain ⟨s', a'⟩ := r; simp
  refine vcpu_exit_local_triple ar hA (h0.nodes _ h0.cur) (P := fun r => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_
  exact WP.spec_mono (syscall.handle_vcpu_exit.entry hA IK hNt s a syscall.NO_IRQ false h hGF htmo
    (fun _ => hUt) hI hF) fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr

/-- **The x86 local VM timer exit keeps `EntryInv`** on its accepted runs
(`vm_timer_local_triple`). Premises as `syscall.handle_vcpu_exit.entry`'s. -/
theorem vm_timer_local.entry {Ac : Set U64} (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (irq n : U64) (p : localtimer.TimerIrqPlan)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) {G : S → Prop}
    (hGF : ∀ s1 s2 : S, G s1 → Foot st T Cs Sg Scs Z (EH H) s1 s2 → G s2)
    (htmo : TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac G)
    (hUt : sched.update_timestamp st ar s a ⦃ s1 a1 => VmPl st T Cs H Sg Scs Z U s1 ∧
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => G s2 ⦄ ⦄)
    (hI : vexit_pre st ar s a false ⦃ s1 _ => (irq != syscall.NO_IRQ) = true →
      IrqNtAt st Nt s1 ∧ BufAt st T Cs H Sg Scs Z U s1 ⦄)
    (hF : vexit_irq st ar s a irq false ⦃ s2 a2 => BufAt st T Cs H Sg Scs Z U s2 ∧
      syscall.finish_old st ar s2 a2 ⦃ s3 _ => VmPl st T Cs H Sg Scs Z U s3 ⦄ ⦄) :
    localvm.handle_vm_timer_irq_local st ar s a irq p n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  refine vm_timer_local_triple ar hA (h0.nodes _ h0.cur) (P := fun r => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_
  exact WP.spec_mono (syscall.handle_vcpu_exit.entry hA IK hNt s a irq false h hGF htmo
    (fun _ => hUt) hI hF) fun r hr => by obtain ⟨s', a'⟩ := r; simpa using hr

end

end Fl4Proofs.P1
