/-
# P2 (line locmv): `LocRunMv` for the cheap local steps, and its ghost-relative form

Line lstab (P2/SlJStab.lean) reduced the syscall local path's layout gap to one [J] premise,
`LocRunMv Loc`: a local step `Loc` from `JAtZ Z H Cs …` ends in `JAtZ (Z.mv G' V') H Cs …`
with the kernel-state base kept, for every local step that can run between two serial
entries. This file discharges it for the steps P3 relates without its entry stack, and
states the premise in the form the `JReachSt` chain actually uses.

## The ghost-relative form
`JReachSt.atSt` only applies `LocRunMv` at `JAtSt th B H Cs k` states, i.e. at ghosts whose
`th`, `B`, `H`, `Cs` are the chain's. `LocKeepSt Loc th B H Cs` asks exactly that (`JAtSt`
kept by a `Loc` step, at those ghosts); `LocRunMv.keepSt` shows it is implied by `LocRunMv`,
`LocKeepSt.or` / `.mono` combine steps, and `JReachSt.atSt'`, `slJAt_layoutJ_of_jreachSt'`,
`sl_pathsK_startAt_stab'` are lstab's consumers under `LocKeepSt`. This lets a step's
relation mention the chain's `B` and `H` (the user-word step below), with the premise
restricted per entry: `LocKeepSt (Loc₁ ∨ Loc₂ ∨ …)` from one lemma per entry.

## Discharged steps
* **The clock reading of a declined local entry** (`LocTick`): P3 relates a decline that read
  the clock (`arI.now a = ok (n1, a')`; P1 FastLocalDecline's `LocalPre`, `ut_now`) to the
  joint state `(s, a', tick σ)` (`DeclAt`, XTopJointKEntryU29D: the general entry then runs
  from there). `locRunMv_tick`: the full `LocRunMv` (no restriction; ARKeep only), by
  `JAtZ.msArJ` at the same ghosts. `jreachSt_tick`: `JReachSt` is closed under it
  (`jreachU17_tick`). A decline before any write leaves `(s, a, σ)`: no step.
* **A user-word write** (`LocUser B H`): the word `wp ∈ B` (the chain's IPC-buffer words),
  apart from every non-`other` object of `H` and inside a spec object, written by the user
  (`Endp.setUm … storeMem`). `locKeepSt_user`: `LocKeepSt` by `JAtZ.userWrJ` (all ghosts
  kept, `BufPlaced` from `JAtZ.bufPlacedJ`). The step's `JReachU17` side (needed by
  `JReachSt.loc`) is not stated by P3: `JReachU3` has no user step.

## Not discharged (finding of this line; sizes in workspace/handoff/locmv.md)
Every *accepted* local entry is P3's general entry (P1 `syscall_local_same`,
`set_timer_local_same`, `irq_local_same`, …; `kernel_entry_reachU29S` / `U29T` / `U29Vm`).
Its stable-ghost post needs the general entry's own composition re-proved: in
`kernel_entryJ13PUG` the budget-stop outcome (`JAtZ.budgetOkB`: `∃ Z'`, `H`, `Cs` kept),
the dispatch outcome (`dispatch_all13PUN`'s `DispPostR` / `PPQJI`: `∃ Zm Hm Csm`) and the
preempted outcome lose the ghosts before `finish`, whose own post (`jat_finishJRN`) does keep
them (`∃ V', JAtZ (Z.mv Z.G V') H Cs`). The tops above (`KEntryU*`, 34 files) re-wrap
`KPost` / `RJ` at every level. So `LocRunMv` for accepted runs, the trap arm's
`fastpath.fault`, the ReplyRecv fast path, `TCB_SetTimer`, the timer interrupt, VM fault,
VM ReplyRecv, I/O port and invocation stays the named premise [J] (`LocKeepSt` restricted to
those runs).
-/
import Fl4Proofs.P2.SlJStab
import Fl4Proofs.P3.XTopJointKEntryU29D
import Fl4Proofs.P3.XTopJointData
import Fl4Proofs.P3.BufInv
import Fl4Proofs.P3.XTopJointPreemptZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop) (MR : A → Fl4Spec.MachineState → Prop)

/-- **[J] when not discharged: a local step keeps the chain's stable ghosts** (module
docstring): from `JAtSt th B H Cs k`, a `Loc` step ends in `JAtSt th B H Cs k`. The form
`JReachSt.atSt` uses; implied by lstab's `LocRunMv` (`LocRunMv.keepSt`). -/
def LocKeepSt (Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop)
    (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) : Prop :=
  ∀ (k : U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit),
    JAtSt (L := L) arI AR th B H Cs k s a σ → Loc s a σ s' a' σ' → JAtSt (L := L) arI AR th B H Cs k s' a' σ'

/-- **The clock reading of a declined local entry** (module docstring): the store state kept,
the Arch value a clock reading leaves, the spec state one oracle reading later (`tick σ`). -/
def LocTick (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  s' = s ∧ (∃ n1, arI.now a = ok (n1, a')) ∧ σ' = Fl4Spec.fl4ClockTick σ

/-- **A user-word write** (module docstring): a word of `B`, apart from every non-`other`
object of `H`, inside a spec object, written with any value; the spec stores the user word. -/
def LocUser (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A)
    (σ' : Fl4Spec.State Unit) : Prop :=
  ∃ wp ∈ B, ∃ v : U64,
    (∀ q k, H q = some k → (∀ z, k ≠ .other z) → wp.1.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ wp.1.val) ∧
    (∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ wp.1.val ∧ wp.1.val < o.toNat + 2 ^ Fl4Spec.objBits ko) ∧
    s' = L.wr s wp.1 v ∧ a' = a ∧
    σ' = Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory wp.2 v.bv)

variable {arI AR MR}

/-- `LocRunMv` gives the ghost-relative form at every chain. -/
theorem LocRunMv.keepSt {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hK : LocRunMv (L := L) arI AR Loc) (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap)
    (Cs : Set U64) : LocKeepSt (L := L) arI AR Loc th B H Cs := by
  intro k s a σ s' a' σ' ⟨Z, Ac, Lst, D, hth, hB, hk, J⟩ hL
  obtain ⟨hk', G, V, Ac', Lst', D', J'⟩ := hK _ _ _ _ _ _ _ _ _ _ _ _ J hL
  exact ⟨Z.mv G V, Ac', Lst', D', hth, hB, hk'.trans hk, J'⟩

/-- `LocKeepSt` of a union of steps. -/
theorem LocKeepSt.or {Loc₁ Loc₂ : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64}
    (h₁ : LocKeepSt (L := L) arI AR Loc₁ th B H Cs) (h₂ : LocKeepSt (L := L) arI AR Loc₂ th B H Cs) :
    LocKeepSt (L := L) arI AR (fun s a σ s' a' σ' => Loc₁ s a σ s' a' σ' ∨ Loc₂ s a σ s' a' σ') th B H Cs :=
  fun k s a σ s' a' σ' hS hL => hL.elim (h₁ k s a σ s' a' σ' hS) (h₂ k s a σ s' a' σ' hS)

/-- `LocKeepSt` of a sub-relation. -/
theorem LocKeepSt.mono {Loc₁ Loc₂ : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64}
    (h₂ : LocKeepSt (L := L) arI AR Loc₂ th B H Cs)
    (hsub : ∀ s a σ s' a' σ', Loc₁ s a σ s' a' σ' → Loc₂ s a σ s' a' σ') :
    LocKeepSt (L := L) arI AR Loc₁ th B H Cs :=
  fun k s a σ s' a' σ' hS hL => h₂ k s a σ s' a' σ' hS (hsub _ _ _ _ _ _ hL)

/-- **`JAtSt` at every `JReachSt` state** under the ghost-relative premise. -/
theorem JReachSt.atSt' {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64}
    (hK : LocKeepSt (L := L) arI AR Loc th B H Cs) {s : S} {a : A}
    {σ : Fl4Spec.State Unit} (h : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ) :
    JAtSt (L := L) arI AR th B H Cs k s a σ := by
  induction h with
  | exit _ hS => exact hS
  | loc _ hL _ ih => exact hK _ _ _ _ _ _ _ ih hL

/-- **`SlJAt` for the exit's layout** at every `JReachSt` state, under `LocKeepSt`. -/
theorem slJAt_layoutJ_of_jreachSt' {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hnd : Fl4Spec.numDomains = 1)
    {Z : XSets} {H : Heap} {Cs : Set U64} {k : U64} {n : Nat} (hn : ∀ c : U64, c ∈ Cs ↔ c.val < n)
    (hK : LocKeepSt (L := L) arI AR Loc Z.th Z.B H Cs)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (h : JReachSt (L := L) arI AR MR Loc Z.th Z.B H Cs k s a σ) :
    SlJAt (L := L) (layoutJ Z H k n) s := by
  obtain ⟨Z', Ac, Lst, D, hth, hB, hk', J⟩ := h.atSt' hK
  obtain ⟨-, -, -, -, -, -, -, hX, -⟩ := jreach_invU3 hnd h.reach.1
  exact slJAt_of_JAtZ_stable J hX.cr.2 (layoutJ Z H k n) rfl (by rw [hth]; rfl) (by rw [hB]; rfl)
    hk'.symm hn

/-! ## The clock reading of a declined entry -/

/-- **`LocRunMv` for the clock reading** (module docstring): unrestricted, by `JAtZ.msArJ`
at the same ghosts (`Z.mv Z.G Z.vs = Z`). -/
theorem locRunMv_tick (hAK : ARKeep arI AR) : LocRunMv (L := L) arI AR (LocTick arI) := by
  intro Z H Cs Ac Lst D s a σ s' a' σ' J ⟨hs, ⟨n1, hn⟩, hσ⟩
  subst hs hσ
  obtain ⟨Lst', J'⟩ := J.msArJ (gctState σ.machineState) a' rfl (fun hc => by
    have h := hAK.now a _ hc
    rw [hn, WP.spec_ok] at h
    exact h)
  exact ⟨rfl, Z.G, Z.vs, Ac, Lst', D, by rw [tick_eq]; exact J'⟩

/-- **`JReachSt` is closed under the clock reading** of a declined entry (`jreachU17_tick`). -/
theorem jreachSt_tick (hnd : Fl4Spec.numDomains = 1) (hARI : ARIface arI AR) (hM : MachPlat arI MR)
    {Loc : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop}
    (hsub : ∀ s a σ s' a' σ', LocTick arI s a σ s' a' σ' → Loc s a σ s' a' σ')
    {th : TypedHeap} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {Cs : Set U64} {k : U64}
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachSt (L := L) arI AR MR Loc th B H Cs k s a σ)
    {n1 : U64} {a1 : A} (hn : arI.now a = ok (n1, a1)) :
    JReachSt (L := L) arI AR MR Loc th B H Cs k s a1 (Fl4Spec.fl4ClockTick σ) :=
  .loc hJ (hsub _ _ _ _ _ _ ⟨rfl, ⟨n1, hn⟩, rfl⟩) (jreachU17_tick hnd hARI hM hJ.reach hn)

/-! ## A user-word write -/

/-- **`LocKeepSt` for a user-word write** (module docstring): `JAtZ.userWrJ` keeps every
ghost; `BufPlaced` by `JAtZ.bufPlacedJ`, the word aligned (`TopPlaced`'s `balign`). -/
theorem locKeepSt_user (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) :
    LocKeepSt (L := L) arI AR (LocUser (L := L) B H) th B H Cs := by
  intro k s a σ s' a' σ' ⟨Z, Ac, Lst, D, hth, hB, hk, J⟩ ⟨wp, hwB, v, hAp, hObj, hs, ha, hσ⟩
  subst hs ha hσ
  have hwZ : wp ∈ Z.B := hB ▸ hwB
  have hal : P1.Aligned wp.1 := (J.xtop.fin.1.2.ep.balign wp hwZ).1
  have hkb : L.ksb (L.wr s wp.1 v) = L.ksb s := (P1.writesIn_wr (st := st) (s := s) hal (v := v)).1
  exact ⟨Z, Ac, Lst, D, hth, hB, hkb.trans hk, J.userWrJ J.bufPlacedJ hwZ hAp hObj v⟩

end

/-! ## `StartAt` for the syscall local path under `LocKeepSt` -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`sl_pathsK_startAt_stab` under the ghost-relative premise** `LocKeepSt` (same
statement, `LocRunMv` replaced by `LocKeepSt Loc Z.th Z.B H Cx`). -/
theorem sl_pathsK_startAt_stab' {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop}
    {Loc : S → A3 → Fl4Spec.State Unit → S → A3 → Fl4Spec.State Unit → Prop}
    (hnd : Fl4Spec.numDomains = 1)
    (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlHereR (st := st) K found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks))
    {Z : XSets} {H : Heap} {Cx : Set U64} {k : U64} {nc : Nat} (hn : ∀ c : U64, c ∈ Cx ↔ c.val < nc)
    (hKL : LocKeepSt (L := L) arI AR Loc Z.th Z.B H Cx)
    (m : U64 → U64) (hK : RegionOK (layoutJ Z H k nc)) (hU : Fl4Proofs.P2.E2E.UserOK (layoutJ Z H k nc))
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit}
    (hR : JReachSt (L := L) arI AR MR Loc Z.th Z.B H Cx k σ a3 τ)
    (a : A) (hQ : Q (layoutJ Z H k nc) m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ (layoutJ Z H k nc).user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () (layoutJ Z H k nc) m hK hU) c hs μ
      ((sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () (layoutJ Z H k nc) m hK hU).body
        σ a) :=
  sl_pathsK_startAt ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz (layoutJ Z H k nc) m hK hU a
    (slJAt_layoutJ_of_jreachSt' hnd hn hKL hR) hQ hc hl hμ

end

end Fl4Proofs.P2.PathObl
