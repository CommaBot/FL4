/-
P2: **`E2E.Fl4Step.ser` from P3's joint invariant at a serial entry's exit**.

Every exit of P3's `kernel_entry_reach*` tops (the general entries, and the local
ones' accepted runs, e.g. `kernel_entry_reachU29T`) ends in `JReachU17` at the exit
state `(s, a, σ)`. `kernel_entry_reachU17V` (used as is, its statement unchanged)
gives at such a state the joint invariant `JAtZ … Z H Cs … s a σ` for some ghosts.
The layout P2 reads off that state is `OwnMap.layoutJ Z H (L.ksb s) n` (typed heap,
kernel-state base, the slots of `Z.th`, the IPC/user frame words of `Z.B`, on `n`
cores), and `OwnMap.ok_of_JAtZ` gives `RegionOK` and `UserOK` for it.

* `ser_of_JAtZ`: at a `JAtZ` state, a configuration whose memory is the store's and
  whose ghost maps are that layout's (`ExitGhost`) satisfies `Fl4Step.ser`'s
  conclusion (`RegionOK ∧ UserOK ∧ Maps`).
* `ser_of_reach`: the same at every `JReachU17` state, i.e. at the exit of every
  serial entry P3 covers, with the ghosts `kernel_entry_reachU17V` provides.
* `ser_of_reachU29`: the same against the top of record, `kernel_entry_reachU29`
  (its premises verbatim; its exits, and `U29T`'s accepted local runs, end in
  `JReachU17`, so the bridge applies at each).
* `ser_step_of_JAtZ`: `Fl4Step.ser` for a serial step of `Serial` whose result is
  such a configuration.
* line lay: `ser_of_JAtZN`, `ser_of_reachN`, `ser_of_reachU29N`, `ser_step_of_JAtZN` —
  the same with `hn` discharged: P3's carried `JKern.csN` (line slj2) numbers `Cs` from 0,
  and the layout counts exactly those `n` cores. Premises: the platform ones and
  `ExitGhost` [P] only.

Premises:
* the platform premises of `kernel_entry_reachU17V` (P3's, verbatim: `ARIface`,
  `ArchTotal`, `numDomains = 1`, `MachPlat`, `MRKeepD`, `MRKeepIo`, `MRKeepIoapic`,
  `PPPlatA`, `IrqPlatA`, `TimeAgree`, `maxTicksToUs`, `ticks_to_us`, `ArchRefines`,
  `PortInValMR`, `StoreExt`, `SetDlDetR`), as tagged there;
* `hn` [J] (old statements only; discharged by the `…N` variants via `JKern.csN`):
  the `n` cores the layout counts are among the joint invariant's cores
  `Cs` (`JKern.cs0` gives it for `n = 1`; for more cores it is the boot fact that the
  running cores are `Cs`, `JKern.csLt` bounds them by 64). Not dischargeable from
  P3 as stated: `JAt` (and so `RJ`, `JReachU3.step`) re-quantifies `Cs` at every
  exit, and `JKern` pins it only by `cs0`, `cpuCs` (the entering core) and
  `csLt`; nothing ties it to the running cores or keeps it across entries.
  The fact that would discharge it is sound on the kernel side: the running
  count is the kernel-global word `ks::NUM_NODES` (offset 0, `layout.rs`), whose
  only writer is boot (`boot.rs` `init_core_state`, `ks_set(s, ks::NUM_NODES,
  num_nodes)`, the same `num_nodes` the boot loops and bootinfo use); every other
  `ks_set` with a computed offset lands at offset ≥ 192 (IRQ state, I/O-port
  bitmap, ASID table, domain schedule), and x86 never reads it. Tying `Cs` to
  that word in `JKern` (fixed across entries by that frame) is a P3 change
  through every `JKern` producer, scheduled separately;
* `ExitGhost` [P]: the model's link: `Serial`'s memory is the store's memory
  `L.mem s` at the exit on aligned kernel words, and the ghost maps a serial step
  installs are those of the layout read off the exit state (the ghost's
  definition; `Step.serial` lets the step choose them).
-/
import Fl4Proofs.P2.OwnJAtZ
import Fl4Proofs.P3.XTopJointKEntryU17
import Fl4Proofs.P3.XTopJointKEntryU29
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.SerExit
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3 Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

noncomputable section

variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}
  {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {MR : A → Fl4Spec.MachineState → Prop}

/-- **The ghost at a serial entry's exit** [P]: the configuration's memory is the
store's at the exit state `s` on aligned kernel words (as `E2E.StartAt` relates
them; user words are not modelled), and its ghost maps are `OwnMap`'s for the
layout `K` (`ko` read in the configuration's memory, as `E2E.Maps` has it). -/
structure ExitGhost (K : OwnMap.KLayout) (s : S) (c : Serial.Cfg U64 U64 U64 U64) : Prop where
  mem : ∀ x, P1.Aligned x → x ∉ K.user → c.mem x = L.mem s x
  own : c.own = OwnMap.own K
  cls : c.cls = OwnMap.cls K
  ko : c.ko = OwnMap.ko K c.mem

theorem maps_of_ghost {K : OwnMap.KLayout} {s : S} {c : Serial.Cfg U64 U64 U64 U64}
    (hG : ExitGhost (L := L) K s c) : E2E.Maps K c :=
  ⟨hG.own, hG.cls, hG.ko⟩

/-- **`Fl4Step.ser`'s conclusion at a `JAtZ` state.** -/
theorem ser_of_JAtZ {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat}
    (hn : ∀ c : U64, c.val < n → c ∈ Cs) {c : Serial.Cfg U64 U64 U64 U64}
    (hG : ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s c) :
    OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) c :=
  let h := OwnMap.ok_of_JAtZ J hn
  ⟨h.1, h.2, maps_of_ghost hG⟩

/-- **`Fl4Step.ser`'s conclusion at every `JReachU17` state** (where every serial
entry P3 covers exits), with the ghosts `kernel_entry_reachU17V` gives. -/
theorem ser_of_reach [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      ∀ n : Nat, (∀ c : U64, c.val < n → c ∈ Cs) → ∀ c : Serial.Cfg U64 U64 U64 U64,
        ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s c →
        OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
          E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
          E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) c := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, -, J, -⟩ :=
    kernel_entry_reachU17V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, J, fun n hn c hG => ser_of_JAtZ J hn hG⟩

/-- **`Fl4Step.ser`'s conclusion at every `JReachU17` state, by the top of record**
`kernel_entry_reachU29` (premises verbatim, statement unchanged): the `JAtZ` its
conclusion opens with gives the layout. Every exit of `U29` / `U29T` (accepted
local runs) / `U29TD` lands in `JReachU17`, so this applies at the exit of every
serial entry P3 covers. -/
theorem ser_of_reachU29 [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧
      ∀ n : Nat, (∀ c : U64, c.val < n → c ∈ Cs) → ∀ c : Serial.Cfg U64 U64 U64 U64,
        ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s c →
        OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
          E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
          E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) c := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, Ac, Lst, D, J, fun n hn c hG => ser_of_JAtZ J hn hG⟩

/-- With one core counted, `hn` is `JKern.cs0`. -/
theorem cores_one {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : ∀ c : U64, c.val < 1 → c ∈ Cs := by
  intro c hc
  have : c = 0#u64 := by
    have h0 : c.val = 0 := by omega
    exact UScalar.eq_of_val_eq (by simpa using h0)
  rw [this]; exact J.kern.cs0

/-- **`Fl4Step.ser` for a serial step** whose result is the exit configuration of an
entry ending at the `JAtZ` state `s` (`ExitGhost` [P]), on `n` cores of `Cs` [J]. -/
theorem ser_step_of_JAtZ {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {n : Nat}
    (hn : ∀ c : U64, c.val < n → c ∈ Cs) {x x' : Serial.Cfg U64 U64 U64 U64} {c : U64}
    (hG : E2E.SerStep x c → ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s x') :
    E2E.SerStep x c → OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) x' :=
  fun h => ser_of_JAtZ J hn (hG h)

/-! ## `hn` discharged (line lay): `JKern.csN` numbers `Cs` from 0 -/

/-- **`Fl4Step.ser`'s conclusion at a `JAtZ` state, `hn` discharged**: `JKern.csN`
(P3, line slj2: the cores numbered from 0) gives the core count `n` with `Cs` exactly
`0 .. n-1`, so `ser_of_JAtZ`'s `hn` holds for it. No premise beyond `JAtZ` and `ExitGhost`. -/
theorem ser_of_JAtZN {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∃ n : Nat, (∀ c : U64, c ∈ Cs ↔ c.val < n) ∧
      OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      ∀ c : Serial.Cfg U64 U64 U64 U64, ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s c →
        E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) c := by
  obtain ⟨n, hn⟩ := J.kern.csN
  have h := OwnMap.ok_of_JAtZ J (n := n) (fun c hc => (hn c).mpr hc)
  exact ⟨n, hn, h.1, h.2, fun _ hG => maps_of_ghost hG⟩

/-- **`ser_of_reach` with `hn` discharged**: at every `JReachU17` state, under
`kernel_entry_reachU17V`'s premises only, some ghosts and core count `n` (`Cs` = `0 .. n-1`)
give `Fl4Step.ser`'s conclusion for the layout read off the state, for every configuration
satisfying `ExitGhost` [P]. -/
theorem ser_of_reachN [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (n : Nat),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ (∀ c : U64, c ∈ Cs ↔ c.val < n) ∧
      OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      ∀ c : Serial.Cfg U64 U64 U64 U64, ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s c →
        E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) c := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, -, J, -⟩ :=
    kernel_entry_reachU17V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨n, hn, h⟩ := ser_of_JAtZN J
  exact ⟨Z, H, Cs, Ac, Lst, D, n, J, hn, h⟩

/-- **`ser_of_reachU29` with `hn` discharged** (the top of record, premises verbatim). -/
theorem ser_of_reachU29N [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR) (hA : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (n : Nat),
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ ∧ (∀ c : U64, c ∈ Cs ↔ c.val < n) ∧
      OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
      ∀ c : Serial.Cfg U64 U64 U64 U64, ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s c →
        E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) c := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨n, hn, h⟩ := ser_of_JAtZN J
  exact ⟨Z, H, Cs, Ac, Lst, D, n, J, hn, h⟩

/-- **`Fl4Step.ser` for a serial step, `hn` discharged**: the core count is `JKern.csN`'s. -/
theorem ser_step_of_JAtZN {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64}
    {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∃ n : Nat, (∀ c : U64, c ∈ Cs ↔ c.val < n) ∧
      ∀ {x x' : Serial.Cfg U64 U64 U64 U64} {c : U64},
        (E2E.SerStep x c → ExitGhost (L := L) (OwnMap.layoutJ Z H (L.ksb s) n) s x') →
        E2E.SerStep x c → OwnMap.RegionOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
          E2E.UserOK (OwnMap.layoutJ Z H (L.ksb s) n) ∧
          E2E.Maps (OwnMap.layoutJ Z H (L.ksb s) n) x' := by
  obtain ⟨n, hn⟩ := J.kern.csN
  exact ⟨n, hn, fun hG => ser_step_of_JAtZ J (fun c hc => (hn c).mpr hc) hG⟩

end
end Fl4Proofs.P2.SerExit
