/-
# P2 (line lay): what the syscall local path's layout `K` is fixed over

`sl_localPathJ` (P2/SlJEnt.lean) asks `SlJAt K s` for one `K` at every state of its `Pre`,
and an anchor state `hKJ : ∃ s0, SlJAt K s0` for the global `RegionOK` / `RegionOKX` /
`UserOK` of `K`. P3 (`slJAt_of_reachU17`, P2/SlJReach.lean) gives a layout per state.

**Where `K` is used** (P2/E2E.lean). A `LocalPath` is indexed by `own K`, `cls K`, `ko K m`,
`K.user`, and `E2E.Paths` asks one for *every* layout `K` (with `RegionOK K`, `UserOK K`
supplied). In an execution (`Exec`) a started body is `LP i K s.mem hK hU` with `K` the
execution's ghost layout at the start step (`Fl4Step.start`), and `body_safe` uses the path's
obligations only at the start state `σ` (`Pre σ`, from `StartAt`) and at the states built from
it inside one body run (user writes, `PathSide.user_free`; `Alt` states in `dec_alt` /
`read_aligned` / `ReadOnce`, all quantified as `Pre s → Alt … s s' → …`). `PathSide.ko_aligned`
is the only field not under `Pre`; it follows from `RegionOK K` / `UserOK K` (`ko_aligned`,
P2/FootTimerSetLP.lean). So inside one `LocalPath` value, `K` is fixed over one body execution
(entry → exit) and `Pre` is needed only at its start state; no anchor is needed.

What the *execution* fixes: `Fl4Step.keep` (the model's ghost) keeps `K` across every step that
is not a serial entry, since the `Serial` model's ownership maps (`Maps K s`: `own`, `cls`, `ko`)
are `K`'s and change only at serial entries (`maps_step`). So the layout a started body sees is
the one installed by the last serial entry's `ser` (`SerExit.ser_of_reachN`), fixed over the
segment between two serial entries: not the whole run, not only the entry state.

## This file
* `sl_localPathK`: `sl_localPathJ` without the anchor: `RegionOK K` / `UserOK K` as `E2E.Paths`
  supplies them, `RegionOKX K` read per state from `SlJAt K s` (under `Pre`).
* `sl_pathsK`: the syscall local path as an `E2E.Paths` member, `Pre := SlJAt K ∧ Q K m`, so
  `sl_localPathJ`'s `hJ` holds by construction and the fixed-layout requirement becomes exactly
  `Fl4Step.start`'s `StartAt` [P] at each start: `SlJAt K σ` for the execution's `K`
  (`sl_pathsK_startAt`).
* `slJAt_of_JAtZ_stable`, `slJAt_of_reachU17_stable`: `SlJAt K s` holds for *every* `K` whose
  five fields match the stable ghost components at `s` — the typed heap `H`, the slots of
  `Zx.th`, the user words of `Zx.B`, `L.ksb s` and the core set `Cs` (numbered from 0). Every
  other ghost (`Zx.G`, the VSpace sets, `Zx.T/C/E/R/N/c/vx`, `Ac`, `Lst`, `D`, the Arch
  instance, `σ`) is free per state. `layoutJ_mv`: P3's step posts at `Z.mv G' V'` (the local
  paths' XTop posts) keep the layout.

## The remaining gap ([J], not stated by P3)
At a body's start state `σ`, P3 must give `JAtZ` with `H`, `Zx.th`, `Zx.B`, `Cs` equal to those
at the last serial exit (`ksb` is a store constant, `LawfulStore.ksb_wr`). Between two serial
entries only local paths, user steps and other cores' local paths run; none retypes or deletes
(they write no object or slot layout, P2/OwnLayout.lean), so the components are stable on the
kernel side, but P3's reachability (`JReachU3.step` … `RJM`/`RJ`) re-quantifies all ghosts at
each exit. What changes them: `H` grows on retype and shrinks on delete; `Zx.th` gains TCB/CNode
entries on retype and drops them on delete; `Zx.B` grows by a frame retype; `Cs` is constant
along every step (`JKern.csN`); all are serial entries. A P3 statement "an accepted local run
from `JAtZ Z H Cs` ends in `JAtZ (Z.mv G' V') H Cs`" (the posts already have that shape inside
`kernel_entry_reachU17V`'s premises) would close it.
-/
import Fl4Proofs.P2.SlJReach
import Fl4Proofs.P2.FootTimerSetLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

/-- The layout depends on the ghosts only through `Zx.th` and `Zx.B`: `Z.mv` (a step post that
changes the MDB ghost and VSpace sets) keeps it. -/
theorem layoutJ_mv (Z : XSets) (G : MdbGhost) (V : XVs) (H : Heap) (k : U64) (n : Nat) :
    layoutJ (Z.mv G V) H k n = layoutJ Z H k n := rfl

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`SlJAt K s` for every `K` matching the stable ghosts** of a `JAtZ` state with the action
resume: the typed heap, the slots of `Zx.th`, the user words of `Zx.B`, the kernel-state base
and the core set numbered from 0. -/
theorem slJAt_of_JAtZ_stable {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a' : A'}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ)
    (hres : σ.schedulerAction = .resumeCurThread) (K : KLayout) (hH : K.heap = H)
    (hS : K.slots = {a | IsSlot Zx.th a}) (hU : K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b})
    (hk : K.ksb = L.ksb s) (hn : ∀ c : U64, c ∈ Cx ↔ c.val < K.ncores) :
    SlJAt (L := L) K s := by
  have e : layoutJ Zx H (L.ksb s) K.ncores = K := by
    obtain ⟨heap, ksb, nc, slots, user⟩ := K
    simp only at hH hS hU hk
    subst hH hS hU hk
    rfl
  have h := SlJAt.of_JAtZ J hres hn
  rwa [e] at h

set_option maxHeartbeats 4000000 in
/-- **`SlJAt` at every reachable entry state, for every layout matching its stable ghosts**
(module docstring): `kernel_entry_reachU17V`'s premises only. -/
theorem slJAt_of_reachU17_stable {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (Zx : XSets) (H : Heap) (Cs : Set U64),
      ∀ K : KLayout, K.heap = H → K.slots = {a | IsSlot Zx.th a} →
        K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b} → K.ksb = L.ksb s →
        (∀ c : U64, c ∈ Cs ↔ c.val < K.ncores) → SlJAt (L := L) K s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, -, J, hX, -⟩ :=
    kernel_entry_reachU17V arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨Z, H, Cs, fun K hH hS hU hk hn => slJAt_of_JAtZ_stable J hX.cr.2 K hH hS hU hk hn⟩

end

/-! ## The local path without an anchor -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The syscall entry as a local path for the layout `K`, from the bundle at its start
states only** (module docstring): `sl_localPathJ` without the anchor `hKJ`. `RegionOK K` and
`UserOK K` are `E2E.Paths`'s arguments; `RegionOKX K` comes from `SlJAt K s` under `Pre`
(every obligation but `PathSide.ko_aligned` is under `Pre`; that one is `ko_aligned`). Other
premises as `sl_localPathJ`. -/
noncomputable def sl_localPathK (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlJAt (L := L) K s)
    (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ s, P s → SlEntR (st := st) K Locks found s)
    (hHr : ∀ s, P s → SlHereR (st := st) K found s)
    (hAr : ∀ s, P s → SlAccR (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  have hEj : ∀ s, P s → SlEntJ (st := st) K Locks found s :=
    fun s hP => (hJ s hP).entJ (hPE s hP).hN (hEr s hP)
  have hHj : ∀ s, P s → SlHereJ (st := st) K K.heap.scBits K.heap.scs found s :=
    fun s hP => (hJ s hP).hereJ (hHr s hP)
  have hAk : ∀ s, P s → SlAccK (st := st) ar K Locks found s :=
    fun s hP => (hJ s hP).accK (hAr s hP)
  have O : ∀ s, P s → PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (fun b => b = true) (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
    fun s hP => sl_pathObl_e ar hSt hA hK (hJ s hP).regionOKX hU hpz.choose_spec.1 hpz.choose_spec.2.1 hm
      (slSets_conv K) (fun _ h => h) a0 hPE hEj hHj hAk
  have Sd : ∀ s, P s → PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
    fun s hP => sl_pathSide_e ar hSt hA hK (hJ s hP).regionOKX hU hpz.choose_spec.1 hpz.choose_spec.2.1 hm
      (slSets_conv K) (fun _ h => h) a0 hPE hEj hHj hAk huf
  { S := S
    A := A
    X := Bool
    st := st
    L := L
    ar := ar
    F := slBody S n found
    p := hpz.choose
    Acc := fun b => b = true
    Locks := Locks
    Pre := P
    RS := SlRS (st := st) K Locks
    WS := SlWS (st := st) K Locks
    DS := SlDS (L := L)
    isProg := IsProg.on hpz.choose_spec.1 _ _ _
    obl :=
      { acc := fun s a r hP => (O s hP).acc s a r hP
        dec_alt := fun s a r hP => (O s hP).dec_alt s a r hP
        read_own := fun s x hP => (O s hP).read_own s x hP
        write_own := fun s x hP => (O s hP).write_own s x hP
        aligned := fun s x hP => (O s hP).aligned s x hP
        move := fun s a r hP => (O s hP).move s a r hP }
    side :=
      { read_aligned := fun s s' a r hP => (Sd s hP).read_aligned s s' a r hP
        rs_aligned := fun s x hP => (Sd s hP).rs_aligned s x hP
        ko_aligned := fun x hx => Fl4Proofs.P2.ko_aligned hK hU x hx
        user_free := fun s b v hP => (Sd s hP).user_free s b v hP }
    once := hpz.choose_spec.2.2
    total := fun s a => sl_total hSt hA n found s a
    masks := hm }

/-- **The syscall local path as an `E2E.Paths` member** (module docstring): for every layout
`K` and memory `m`, `sl_localPathK` with `Pre := SlJAt K ∧ Q K m`, so the bundle premise
holds by construction. The premises are `sl_localPathJ`'s, per layout, under that `Pre`. -/
noncomputable def sl_pathsK (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
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
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  fun _ K m hK hU =>
    sl_localPathK (K := K) (m0 := m) ar hSt hA hm a0 hK hU
      (P := fun s => SlJAt (L := L) K s ∧ Q K m s) (fun _ h => h.1)
      (fun s h => hPE K m s h.1 h.2) (fun s h => hEr K m s h.1 h.2) (fun s h => hHr K m s h.1 h.2)
      (fun s h => hAr K m s h.1 h.2) (fun s b v h => huf K m s b v h.1 h.2) (hpz K m)

/-- **`StartAt` for `sl_pathsK`** at the execution's layout `K`: what `Fl4Step.start` [P]
asks of the glue is the bundle `SlJAt K σ` for that `K` (the layout of the last serial exit,
kept by `Fl4Step.keep`) and `Q K m σ` at the start state, plus the glue's core / locks /
memory link. -/
theorem sl_pathsK_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
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
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hQ : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () K m hK hU) c hs μ
      ((sl_pathsK (Locks := Locks) ar hSt hA hm a0 Q hPE hEr hHr hAr huf hpz () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hQ⟩, hc, hl, hμ, rfl⟩

end

end Fl4Proofs.P2.PathObl
