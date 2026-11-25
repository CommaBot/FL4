/-
P2 (actv): **the local entries that call `schedule` end in `AllCores` at the
entry's exit** (after `finish`'s `activate_thread` and `vcpu::check`).

`timer_irq_local.allCores` / `set_timer_local.allCores` (`P2/EntryIrq.lean`,
`P2/EntryTmr.lean`) end at `schedule`'s end; their `B` versions also name
`schedule`'s start (`BlkOK`, `BufAt`). Here:

* `AllCores.exit`: from `schedule`'s start (`BlkOK`, `BufAt`) and `AllCores` at
  its end, the tail (`AllCores.tail`, `P2/EntryTail.lean`) ends in
  `AllCores`; `EntryInv` at `schedule`'s end is P1's `sched.schedule.entry`,
  `BufAt` there from `SchIb`.
* **`timer_irq_local.allCoresExit`**, **`set_timer_local.allCoresExit`**: an
  accepted run of the local entry, from `AllCores` at the entry, ends in
  `AllCores`.

Named premises (beside the wrappers' `hR` [J], `hS0` [W], `hKS` [W]):

* `hSI` **[J]** (`SchIb`): `schedule` keeps every TCB's IPC-buffer lookup
  words (its `IPC_BUFFER` field, its buffer cap slot), from a `BlkOK`/`BufAt`
  state. P1 has this for `timer::fire`'s steps (`ibKeep_holds`), not for the
  rest of `schedule`, whose P1 footprint (`SchedW`, `KW`) admits every TCB
  field past the cap slots; no step of `schedule` writes these words.
* `hVW` **[P]** (`VcpuUsr`, `P2/EntryTail.lean`): a bound VCPU's `PENDING`
  word is a user-class word.
-/
import Fl4Proofs.P2.EntryIrq
import Fl4Proofs.P2.EntryTmr
import Fl4Proofs.P2.EntryTail
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- **[J] `schedule` keeps the IPC-buffer lookup words** (module docstring). -/
def SchIb (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac U : Set U64) : Prop :=
  ∀ (s : S) (a : A) (r : S × A), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s → BufAt st T Cs H Sg Scs Z U s →
    sched.schedule st ar s a = ok r → IbFr (L := L) T s r.1

/-- **From `schedule`'s start to the entry's exit.** -/
theorem AllCores.exit (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hS0 : (0#u64) ∉ Scs) (hSI : SchIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac U)
    (hVW : ∀ s : S, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s → VcpuUsr st T Cs H Sg Scs Z s)
    {s3 s4 s' : S} {a3 a4 a' : A}
    (hB3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (hBA3 : BufAt st T Cs H Sg Scs Z U s3)
    (esc : sched.schedule st ar s3 a3 = ok (s4, a4)) (h4 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4)
    (E : (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have hB3' := hB3
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := hB3'
  have hI := sched.schedule.entry hA IK hNt s3 a3 Q R hq hB hS hX hSg hBA3
  rw [esc, WP.spec_ok] at hI
  try simp only [WP.uncurry'_pair] at hI
  have hBA4 : BufAt st T Cs H Sg Scs Z U s4 := BufAt.of_fr hBA3 (hSI s3 a3 _ hB3 hBA3 esc)
  exact AllCores.tail hA hNt h4 hS0 hI hBA4 hVW E

set_option maxHeartbeats 4000000 in
/-- **The timer-interrupt local entry ends in `AllCores`** (module docstring).
Named premises: `hR` [J], `hS0` [W], `hKS` [W] (as `timer_irq_local.allCores`),
`hSI` [J], `hVW` [P]. -/
theorem timer_irq_local.allCoresExit (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hKS : ScKsOut st Scs Z s0)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (hSI : SchIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac U)
    (hVW : ∀ s : S, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s → VcpuUsr st T Cs H Sg Scs Z s)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, esc, W, E⟩ :=
    timer_irq_local.allCoresB hA IK hNt h0 hcpu hS0 hKS hI0 hBA0 hR e
  exact AllCores.exit hA IK hNt hS0 hSI hVW hB3 hBA3 esc W E

set_option maxHeartbeats 4000000 in
/-- **The `TCB_SetTimer` local entry ends in `AllCores`** (module docstring).
Named premises: `hR` [J], `hS0` [W] (as `set_timer_local.allCores`), `hSI` [J],
`hVW` [P]. -/
theorem set_timer_local.allCoresExit (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (hSI : SchIb st ar T Cs Ω H Sg Rp Scs Nt Z Ac U)
    (hVW : ∀ s : S, AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s → VcpuUsr st T Cs H Sg Scs Z s)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, esc, W, E⟩ :=
    set_timer_local.allCoresB hA IK hNt h0 hcpu hS0 hI0 hBA0 htg hR e
  exact AllCores.exit hA IK hNt hS0 hSI hVW hB3 hBA3 esc W E

end

end Fl4Proofs.P2.Stall
