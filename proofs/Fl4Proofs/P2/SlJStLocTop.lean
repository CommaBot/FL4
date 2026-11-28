/-
# P2 (line stpost, generations 6–9): the I/O port, `TCB_SetTimer` and timer-interrupt local paths' layout chain, closed

SlJStTop's `sl_pathsK_startAt_loc` for the syscall local path, extended to every local entry line
stpost proved stable: the chain's step relation is now the union `LocAll` of the accepted syscall
local runs (`LocSys`: trap arm and ReplyRecv fast path), the accepted I/O port runs (`LocIo`), the
accepted `TCB_SetTimer` runs (`LocTm`), the accepted timer interrupts (`LocIrq`, gen 7) and the accepted
frame-cap invocations (`LocInv`, gen 8; every label the plan accepts since gen 9, `CNodeDelete` included)
the accepted VM faults (`LocVmf`, gen 9) and the accepted VM ReplyRecv runs (`LocRrVm`, gen 9), each as a `LocSt` step (stable ghosts kept), so `LocKeepSt`
of it is `locKeepSt_st` (no premise).

Local entries left out of `LocAll`: the declined entries (U29D: a declining local entry falls back to the
general entry under the serial gate, whose ghosts grow by nature (new objects, caps, VSpaces), so no
stable-ghost step exists for them); `local_vm_exit` (the lvm line, P2 only, not on this branch).

* `lpRestrict`: a local path with its `Pre` narrowed to a `Pre'` that implies it and is closed under
  user-word writes (every obligation of `E2E.LocalPath` is stated under `Pre`, except `ko_aligned`).
* `io_localPathK`: AccessIoLP's `io_localPath` with the layout's alignment `IoLayA K` read per state
  under `Pre` (as SlJLay's `sl_localPathK` reads `RegionOKX`); `SlJAt.ioLayA`: `SlJAt K s` gives
  `IoLayA K` (`UserOK`'s alignment facts, and the TCBs' `TcbAddr` from P1's `BXI` at the state). So the
  [J] premise `hLA` of `io_localPath` is discharged on `io_pathsK`.
* `io_pathsK` / `tm_pathsK`: the I/O port and `TCB_SetTimer` local paths as `E2E.Paths` members,
  `Pre := SlJAt K ∧ Q K m` (as SlJLay's `sl_pathsK`); `tm_pathsK` is FootTimerSetMv's
  `set_timer_localPathM` narrowed by `lpRestrict` (its `Pre`, `StEntK`, from `hPE`).
  `io_pathsK_startAt` / `tm_pathsK_startAt`: `StartAt` from `SlJAt K σ ∧ Q K m σ`.
* **`loc_chain_all`** (the top): from a serial exit (`JReachU17`), ONE ghost choice `Z H Cx nc` gives
  SerExit's facts for `layoutJ Z H (L.ksb s0) nc` and the set `R` (`JReachSt` over `LocAllSt` at those
  ghosts) with: `R` at the exit; `R` closed under the accepted trap arm, the ReplyRecv fast path, the
  I/O port entry, the `TCB_SetTimer` entry and the timer interrupt (each under its U29 clause's inputs, a
  subset; the interrupt's are `IrqHw` [P] and `KFinEv13`); and `SlJAt (layoutJ Z H (L.ksb s0) nc)` at every
  `R` state (clause 7); clause 8 (gen 8): `R` closed under the accepted frame-cap invocation (U29V's
  inputs that the route reads, fl4-sync's plan; gen 8's temporary run restriction "label not `CNodeDelete`"
  was removed in gen 9); clause 9 (gen 9): `R` closed under the accepted VM fault (U29Vm's VM-fault clause
  inputs: `VmfHw` [P], `KFinEv13`); clause 10 (gen 9): `R` closed under the accepted VM ReplyRecv (U29Vm's
  ReplyRecv clause inputs that the route reads: the trap flag, `KFinAtR13`, fl4-sync's `found`). `StartAt` at an `R` state for each path: its `…_startAt` (`sl_pathsK_startAt_stab'`,
  `io_pathsK_startAt`, `tm_pathsK_startAt`) with clause 7 for `SlJAt K σ` and the path's `Q K m σ` plus the
  glue's core / locks / memory link. No `LocKeepSt` / `LocRunMv` premise.
* `IrqPreK`, **`irqPreK_of_chain`** (gen 7): the timer interrupt path's `Pre` (par/p2lt2's `IrqPreJ3`, body
  verbatim: `SlJAt K ∧` memory agreement) at every `R` state from clause 7 and the memory agreement; with
  `irq_pathsJ3_startAt` (par/p2lt2) this is the timer-interrupt path's `StartAt`: **`irq_pathsK_startAt`**
  (int13). `IrqPreK` is now an abbreviation of p2lt2's `IrqPreJ3` (same body).

Premises left: U29's platform inputs (`hARI hA hnd hM hKD hIo hPA hIA hT hmax htu hRef hPI hSX hDR`); each
path's own premises, unchanged in kind: `sl_pathsK`'s; `io_pathsK`'s `hPE` (`IoPre`), `hmA` [J]
(`ko`'s memory agrees on TCB affinity words), `huf` [J] (`PathSide.user_free`), `hpz` ([P] `IsProg` of the pruned body `ioBodyP`, as
AccessIoLP's `io_localPath` since hpzf; [W] `NoZero`, [W] declining `ReadOnce`) and `hm` [P] (`MasksWr`); `tm_pathsK`'s `hPE` (`StEntK`),
`hpz` ([P] `IsProg`, [W] `NoZero`, [W] `ReadOnce`), `hEU` / `hlk` / `hNU` (as `set_timer_localPathM`),
`huf` [J] (the `Pre` closed under user writes) and `hm` [P]. The glue identifying a body start with an
`R` state stays `Fl4Step.start` [P].
-/
import Fl4Proofs.P2.SlJStPostRR
import Fl4Proofs.P2.SlJStPostIrq
import Fl4Proofs.P2.SlJStPostInv
import Fl4Proofs.P2.SlJStPostVm
import Fl4Proofs.P2.SlJStPostRRVm
import Fl4Proofs.P2.AccessIoLP
import Fl4Proofs.P2.FootTimerSetMv
import Fl4Proofs.P2.FootTimerIrqJ3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

/-! ## Narrowing a local path's `Pre` -/

section restrict
variable {own : (U64 → U64) → U64 → Fl4Proofs.P2.Serial.Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → Fl4Proofs.P2.Serial.ClsOwner U64} {User : U64 → Prop}

/-- (stpost) **A local path with a narrower `Pre`** (module docstring). -/
noncomputable def lpRestrict (P : Fl4Proofs.P2.E2E.LocalPath own cls ko User) (Pre' : P.S → Prop)
    (hsub : ∀ s, Pre' s → P.Pre s)
    (huf : ∀ s b v, Pre' s → User b → Aligned b → Pre' (P.L.wr s b v)) :
    Fl4Proofs.P2.E2E.LocalPath own cls ko User where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := P.p
  Acc := P.Acc
  Locks := P.Locks
  Pre := Pre'
  RS := P.RS
  WS := P.WS
  DS := P.DS
  isProg := by
    letI := P.L
    exact fun st' N s ⟨s0, h0, hA⟩ a => P.isProg st' N s ⟨s0, hsub s0 h0, hA⟩ a
  obl :=
    letI := P.L
    { acc := fun s a r h => P.obl.acc s a r (hsub s h)
      dec_alt := fun s a r h => P.obl.dec_alt s a r (hsub s h)
      read_own := fun s x h => P.obl.read_own s x (hsub s h)
      write_own := fun s x h => P.obl.write_own s x (hsub s h)
      aligned := fun s x h => P.obl.aligned s x (hsub s h)
      move := fun s a r h => P.obl.move s a r (hsub s h) }
  side :=
    letI := P.L
    { read_aligned := fun s s' a r h => P.side.read_aligned s s' a r (hsub s h)
      rs_aligned := fun s x h => P.side.rs_aligned s x (hsub s h)
      ko_aligned := P.side.ko_aligned
      user_free := fun s b v h hb ha => ⟨huf s b v h hb ha, (P.side.user_free s b v (hsub s h) hb ha).2⟩ }
  once := letI := P.L; fun s s' a r h => P.once s s' a r (hsub s h)
  total := P.total
  masks := P.masks

/-- `StartAt` of a narrowed path from its `Pre'`. -/
theorem lpRestrict_startAt (P : Fl4Proofs.P2.E2E.LocalPath own cls ko User) (Pre' : P.S → Prop)
    (hsub : ∀ s, Pre' s → P.Pre s)
    (huf : ∀ s b v, Pre' s → User b → Aligned b → Pre' (P.L.wr s b v))
    {σ : P.S} (a : P.A) (hP : Pre' σ) {c : U64} {hs : U64 → Prop} (hc : P.L.cpu σ = c) (hl : P.Locks σ = hs)
    {μ : U64 → U64} (hμ : ∀ x, Aligned x → ¬ User x → P.L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt (lpRestrict P Pre' hsub huf) c hs μ ((lpRestrict P Pre' hsub huf).body σ a) :=
  ⟨σ, a, hP, hc, hl, hμ, rfl⟩

end restrict

/-! ## The I/O port path with its alignment per state -/

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type}

/-- (stpost) **`SlJAt K s` gives the layout's alignment `IoLayA K`** (module docstring). -/
theorem SlJAt.ioLayA {s : S} (B : SlJAt (L := L) K s) : IoLayA K := by
  have hU := B.userOK
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
  have h0 := B.j.bxi.1.choose_spec.choose_spec
  exact ⟨fun p hp => (hU.slot p hp).1, fun t ht => h0.tcbs t ht, fun p hp => (hU.ntfn p hp).1,
    fun p b hb => (hU.sc p b hb).1⟩

/-- (stpost) **The I/O port local path, `IoLayA` per state** (module docstring; AccessIoLP's
`io_localPath` with `hLA` under `Pre`). -/
noncomputable def io_localPathK (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : Fl4Proofs.P2.E2E.UserOK K) {number : I64} (hm : Fl4Proofs.P2.E2E.MasksWr st)
    {P : S → Prop} (hLA : ∀ s, P s → IoLayA K) (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r →
        Fl4Proofs.P2.E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    Fl4Proofs.P2.E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  have hp : IsProgOn (fun m s a => syscall.handle_ioport_local m ar s a number) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) hpz.choose :=
    io_isProgOn hA hPE hpz.choose_spec.1
  have O : ∀ s, P s → PathObl st (fun m s a => syscall.handle_ioport_local m ar s a number) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) :=
    fun s hP => io_pathObl_mv hA hK hU (hLA s hP) hPE hmA hp
  have Sd : ∀ s, P s → PathSide st (fun m s a => syscall.handle_ioport_local m ar s a number)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) :=
    fun s hP => io_pathSide hA hK (hLA s hP) hPE hp hpz.choose_spec.2.1 hm huf
  { S := S
    A := A
    X := Bool
    st := st
    L := L
    ar := ar
    F := ioBody S number
    p := hpz.choose
    Acc := fun b => b = true
    Locks := Locks
    Pre := P
    RS := IoRS (st := st) K Locks
    WS := IoWS (st := st) K Locks
    DS := IoDS (st := st)
    isProg := hp
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
    once := io_readOnce hA hPE hp hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
    total := fun s a => io_total hA number s a
    masks := hm }

/-- (stpost) **The I/O port local path as an `E2E.Paths` member** (module docstring): for every layout
`K` and memory `m`, `io_localPathK` with `Pre := SlJAt K ∧ Q K m` (`IoLayA K` by `SlJAt.ioLayA`). -/
noncomputable def io_pathsK (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K s ∧ Q K m s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r →
        Fl4Proofs.P2.E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  fun _ K m hK hU =>
    io_localPathK (K := K) (m0 := m) (Locks := Locks) ar hA hK hU hm (P := fun s => SlJAt (L := L) K s ∧ Q K m s)
      (fun _ h => h.1.ioLayA) (fun s h => hPE K m s h.1 h.2) (fun s h => hmA K m s h.1 h.2)
      (fun s b v h => huf K m s b v h.1 h.2) (hpz K m)

/-- (stpost) **`StartAt` for `io_pathsK`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem io_pathsK_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ K m s, SlJAt (L := L) K s → Q K m s → ∀ d, K.heap d = some .tcb →
      m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K s ∧ Q K m s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r →
        Fl4Proofs.P2.E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hQ : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (io_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf hpz
        () K m hK hU) c hs μ
      ((io_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf hpz
        () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hQ⟩, hc, hl, hμ, rfl⟩

end io

/-! ## The `TCB_SetTimer` path at `Pre := SlJAt K ∧ Q K m` -/

section tm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop}
variable {A : Type}

/-- `StEntK` at a layout `K` with the layout's typed heap as P1's ghosts. -/
abbrev StEntKK (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Cs Ω Sg Ac : Set U64) (target : U64)
    (m : U64 → U64) (s : S) : Prop :=
  Fl4Proofs.P2.StEntK K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac
    target m s

/-- (stpost) **The `TCB_SetTimer` local path as an `E2E.Paths` member** (module docstring):
`set_timer_localPathM` at each layout, narrowed to `Pre := SlJAt K ∧ Q K m` by `lpRestrict`. -/
noncomputable def tm_pathsK (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (Fl4Proofs.P2.stBody S n target) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (StEntKK K st Cs Ω Sg Ac target m) (Fl4Proofs.P2.MaxR K st lk))
    (hEU : ∀ K s b v, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ K.user → Aligned b →
      Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ K s, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  fun _ K m hK hU =>
    lpRestrict
      (Fl4Proofs.P2.set_timer_localPathM (lk := lk) ar n hA hK hU (hpz K m).choose_spec.1
        (hpz K m).choose_spec.2.1 hm (hpz K m).choose_spec.2.2 (hEU K) (hlk K)
        (hNU K))
      (fun s => SlJAt (L := L) K s ∧ Q K m s) (fun s h => hPE K m s h.1 h.2)
      (fun s b v h hb ha => huf K m s b v h.1 h.2 hb ha)

/-- (stpost) **`StartAt` for `tm_pathsK`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem tm_pathsK_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (Fl4Proofs.P2.stBody S n target) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (StEntKK K st Cs Ω Sg Ac target m) (Fl4Proofs.P2.MaxR K st lk))
    (hEU : ∀ K s b v, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ K.user → Aligned b →
      Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ K s, Fl4Proofs.P2.StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hQ : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (tm_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hpz hEU hlk hNU huf
        () K m hK hU) c hs μ
      ((tm_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hpz hEU hlk hNU huf
        () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hQ⟩, hc, hl, hμ, rfl⟩

end tm

/-! ## The chain over every stable local entry -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (arI : machine.Arch A)
variable (AR : A → Fl4Spec.Cr3 → Prop)

/-- (stpost) **The accepted local runs proved stable** (module docstring). -/
def LocAll (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) : Prop :=
  LocSys (st := st) arI s a σ s' a' σ' ∨ LocIo (st := st) arI s a σ s' a' σ' ∨ LocTm (st := st) arI s a σ s' a' σ' ∨
    LocIrq (st := st) arI s a σ s' a' σ' ∨ LocInv (st := st) arI s a σ s' a' σ' ∨
    LocVmf (st := st) arI s a σ s' a' σ' ∨ LocRrVm (st := st) arI s a σ s' a' σ'

/-- (stpost) **The chain's step relation** (module docstring). -/
abbrev LocAllSt (th : TypedHeap) (B : Set (U64 × Fl4Spec.Word)) (H : Heap) (Cs : Set U64) :
    S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop :=
  LocSt (L := L) arI AR (LocAll (st := st) arI) th B H Cs

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 8000000 in
/-- (stpost) **The layout chain over every stable local entry, closed** (module docstring). -/
theorem loc_chain_all [Fl4Proofs.P1.PlainStore st] {A3 : Type} {arI : machine.Arch A3}
    {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
    (hARI : ARIface arI AR) (hA3 : P0.ArchTotal arI)
    (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR) (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR) (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A3) MR)
    {s0 : S} {a3 : A3} {σ0 : Fl4Spec.State Unit} (h0 : JReachU17 (L := L) arI AR MR s0 a3 σ0) :
    ∃ (Z : XSets) (H : Heap) (Cx : Set U64) (nc : Nat), (∀ c : U64, c ∈ Cx ↔ c.val < nc) ∧
      ∃ (hK : OwnMap.RegionOK (layoutJ Z H (L.ksb s0) nc)) (hU : E2E.UserOK (layoutJ Z H (L.ksb s0) nc)),
      (∀ c : Serial.Cfg U64 U64 U64 U64, SerExit.ExitGhost (L := L) (layoutJ Z H (L.ksb s0) nc) s0 c →
        E2E.Maps (layoutJ Z H (L.ksb s0) nc) c) ∧
      -- 1. the exit
      JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s0 a3 σ0 ∧
      -- 2. the trap arm
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (n' : I64) (found' : U64 × U64), σ.curThread ≠ σ.idleThread → UnkSys (L := L) n' s →
          NoDbgSys (L := L) arI n' s a →
          (∀ ev, KEvSpec (.sysU n') true ev → ∀ w ∈ (Fl4Spec.fl4SyscallFaultIP (Z := Unit) σ.curThread σ).1,
            KFinEv13 (L := L) arI AR ev (KFrontSysU (st := st) arI n' s a) w.2) →
          ∀ s' a', syscall.handle_syscall_local st arI s a n' found' = ok (true, s', a') →
            ∃ ev σ', KEvSpec (.sysU n') true ev ∧ EvOut true ev σ σ' ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 3. the ReplyRecv fast path
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (found' : U64 × U64), σ.curThread ≠ σ.idleThread →
          (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
            ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
          (∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
            (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A3),
              KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
              JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
              KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
          (∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
            (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 →
            fl4_abi.syscall.SysReplyRecv = fl4_abi.syscall.SysReplyRecv →
            fastpath.reply_caps st s t = ok (some found')) →
          ∀ s' a', syscall.handle_syscall_local st arI s a fl4_abi.syscall.SysReplyRecv found' = ok (true, s', a') →
            ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 4. the I/O port entry
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (n : I64) (c : Fl4Spec.Syscall), σ.curThread ≠ σ.idleThread → NativeSys n c →
          (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
            ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
          (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
            (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A3),
              KFrontF (L := L) arI n s a s' a' →
              JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
              KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
          ∀ s' a', syscall.handle_ioport_local st arI s a n = ok (true, s', a') →
            ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 5. the `TCB_SetTimer` entry
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (n : I64) (c : Fl4Spec.Syscall) (target : U64), σ.curThread ≠ σ.idleThread → NativeSys n c →
          (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
            ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
          (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
            (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A3),
              KFrontF (L := L) arI n s a s' a' →
              JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
              KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
          SetTimerFound (L := L) s target →
          ∀ s' a', localtimer.handle_set_timer_local st arI s a n target = ok (true, s', a') →
            ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 6. the timer interrupt
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (w : U64) (a1 : A3) (p : localtimer.TimerIrqPlan), IrqHw AR MR a a1 σ w →
          KFinEv13 (L := L) arI AR .interrupt (KFrontI (st := st) arI s a1 w) σ →
          ∀ s' a', localtimer.handle_timer_irq_local st arI s a1 w p = ok (true, s', a') →
            ∃ σ', EvOut false .interrupt σ σ' ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 7. the layout bundle at every chain state
      (∀ (σ : S) (a3' : A3) (τ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) σ a3' τ →
        SlJAt (L := L) (layoutJ Z H (L.ksb s0) nc) σ) ∧
      -- 8. the frame-cap invocation (gen 8; every local label: Copy / Mint / Map, and Delete since gen 9)
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (n : I64) (c : Fl4Spec.Syscall) (p : localinv.Plan), σ.curThread ≠ σ.idleThread → NativeSys n c →
          (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
            ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
          (∀ x ∈ (specFront c σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
            (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A3),
              KFrontF (L := L) arI n s a s' a' →
              JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
              KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
          localinv.plan st s n = ok (some p) →
          ∀ s' a', syscall.handle_invocation_local st arI s a n p = ok (true, s', a') →
            ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true c σ).1 ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 9. the VM fault (gen 9)
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (ad c : U64) (ft : Fl4Spec.VMFaultType), σ.curThread ≠ σ.idleThread → VmfHw ad c ft σ →
          KFinEv13 (L := L) arI AR (.vmFaultEvent ft) (KFrontF2 (st := st) arI (brV (st := st) arI ad c) s a) σ →
          ∀ s' a', syscall.handle_vm_fault_local st arI s a ad c = ok (true, s', a') →
            ∃ σ', EvOut false (.vmFaultEvent ft) σ σ' ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') ∧
      -- 10. the VM ReplyRecv (gen 9)
      (∀ (s : S) (a : A3) (σ : Fl4Spec.State Unit),
        JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0) s a σ →
        ∀ (found : U64 × U64), σ.curThread ≠ σ.idleThread →
          (∀ ct v, sched.cur_thread st s = ok ct → obj.Tcb.flags st ct (L.wr s (regA ct layout.reg.FAULT_IP) v)
            ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄) →
          (∀ x ∈ (specFront .sysReplyRecv σ).1, ∀ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64)
            (Lst' : U64 → List U64) (D' : Set U64) (s' : S) (a' : A3),
              KFrontF (L := L) arI fl4_abi.syscall.SysReplyRecv s a s' a' →
              JAtZR (L := L) arI AR Z' H' Cs' Ac' Lst' D' s' a' x.2 →
              KFinAtR13 (L := L) arI AR Z' H' Cs' s' a' x.2) →
          (∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found)) →
          ∀ s' a', syscall.handle_reply_recv_vm_local st arI s a found = ok (true, s', a') →
            ∃ σ', ((), σ') ∈ (Fl4Spec.fl4KernelEntrySyscall (Z := Unit) true .sysReplyRecv σ).1 ∧
              JReachSt (L := L) arI AR MR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx (L.ksb s0)
                s' a' σ') := by
  obtain ⟨Z, H, Cx, Ac0, Lst0, D0, J, -, -, -, -, -, -, -, hvx⟩ := jreach_invU3 hnd h0.1
  obtain ⟨nc, hnc, hK, hU, hMaps⟩ := SerExit.ser_of_JAtZN J
  have hKS : LocKeepSt (L := L) arI AR (LocAllSt (L := L) arI AR Z.th Z.B H Cx) Z.th Z.B H Cx :=
    locKeepSt_st _ _ _ _ _
  have hsubS : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocSys (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' := fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inl h1, h2⟩
  have hsubI : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocIo (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' :=
    fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inr (Or.inl h1), h2⟩
  have hsubT : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocTm (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' :=
    fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inr (Or.inr (Or.inl h1)), h2⟩
  have hsubQ : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocIrq (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' :=
    fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inr (Or.inr (Or.inr (Or.inl h1))), h2⟩
  have hsubV : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocInv (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' :=
    fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))), h2⟩
  have hsubF : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocVmf (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' :=
    fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))), h2⟩
  have hsubR : ∀ s a σ s' a' σ', LocSt (L := L) arI AR (LocRrVm (st := st) arI) Z.th Z.B H Cx s a σ s' a' σ' →
      LocAllSt (L := L) arI AR Z.th Z.B H Cx s a σ s' a' σ' :=
    fun _ _ _ _ _ _ ⟨h1, h2⟩ => ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h1))))), h2⟩
  have hNS : NativeSys fl4_abi.syscall.SysReplyRecv .sysReplyRecv := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  refine ⟨Z, H, Cx, nc, hnc, hK, hU, hMaps, .exit h0 ⟨Z, Ac0, Lst0, D0, rfl, rfl, rfl, J, hvx⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s a σ hJ n' found' hct hUn hND hFin s' a' hrun
    exact jreachSt_sysUStK hARI hA3 hnd hM hKD hPA hT hmax htu hRef hSX hDR hKS hsubS hJ n' found' hct hUn hND
      hFin hrun
  · intro s a σ hJ found' hct hflag hFin hfd s' a' hrun
    exact jreachSt_rrSt hARI hA3 hnd hM hKD hPA hT hmax htu hRef hSX hDR hKS hsubS hJ found' hct hNS hflag hFin
      hfd hrun
  · intro s a σ hJ n c hct hn hflag hFin s' a' hrun
    exact jreachSt_ioSt hARI hA3 hnd hM hKD hIo hPA hT hmax htu hRef hPI hDR hKS hsubI hJ n c hct hn hflag hFin
      hrun
  · intro s a σ hJ n c target hct hn hflag hFin hTF s' a' hrun
    exact jreachSt_tmSt hARI hA3 hnd hM hKD hPA hT hmax htu hRef hDR hKS hsubT hJ n c target hct hn hflag hFin
      hTF hrun
  · intro s a σ hJ w a1 p hI hFin s' a' hrun
    exact jreachSt_irqSt hARI hA3 hnd hM hKD hPA hIA hT hmax htu hRef hDR hKS hsubQ hJ w a1 p hI hFin hrun
  · intro σ a3' τ hR
    exact slJAt_layoutJ_of_jreachSt' hnd hnc hKS hR
  · intro s a σ hJ n c p hct hn hflag hFin hp s' a' hrun
    exact jreachSt_invSt hARI hA3 hnd hM hKD hPA hT hmax htu hRef hDR hKS hsubV hJ n c p hct hn hflag hFin hp hrun
  · intro s a σ hJ ad c ft hct hV hFin s' a' hrun
    exact jreachSt_vmfSt hARI hA3 hnd hM hKD hPA hT hmax htu hRef hSX hDR hKS hsubF hJ ad c ft hct hV hFin hrun
  · intro s a σ hJ found hct hflag hFin hfd s' a' hrun
    exact jreachSt_rrVmSt hARI hA3 hnd hM hKD hPA hT hmax htu hRef hSX hDR hKS hsubR hJ found hct hNS hflag hFin
      hfd hrun

end

/-! ## The timer interrupt path's `Pre` at every chain state -/

section irq
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (stpost) **The timer interrupt path's `Pre`** (module docstring): line slj's bundle `SlJAt K` and the store
agreeing with the model memory `m` on aligned kernel words. Since int13 it is par/p2lt2's `IrqPreJ3`
(FootTimerIrqJ3) itself (stpost had written the same body out verbatim, `IrqPreJ3` not being on its branch),
i.e. `sl_pathsK`'s `SlJAt K ∧ Q K m` with `Q K m s := ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x`. -/
abbrev IrqPreK (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (m : U64 → U64) (s : S) : Prop :=
  Fl4Proofs.P2.IrqPreJ3 (L := L) K st m s

/-- (stpost) **`IrqPreK` at every state of a chain whose states carry `SlJAt K`** (module docstring): with
`loc_chain_all`'s clause 7 as `h7`, every chain state `σ` whose store agrees with `m` off the user words is a
start of the timer interrupt path at `(K, m)` (`irq_pathsJ3_startAt`'s `hJ` / `hM`, after integration). -/
theorem irqPreK_of_chain {A3 : Type} {R : S → A3 → Fl4Spec.State Unit → Prop} {K : KLayout}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), R σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a : A3} {τ : Fl4Spec.State Unit} (hR : R σ a τ) {m : U64 → U64}
    (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x) : IrqPreK K st m σ :=
  ⟨h7 σ a τ hR, hM⟩

/-- (int13) **`StartAt` of the timer interrupt path at every chain state** (stpost gen 7's integration note):
for a chain `R` whose states carry `SlJAt K` (`loc_chain_all`'s clause 7 as `h7`, `K = layoutJ Z H (L.ksb s0) nc`),
every `R` state `σ` whose store agrees with `m` off the user words, with the glue's core / locks / memory link,
is a start of par/p2lt2's `irq_pathsJ3` at `(K, m)`: `irq_pathsJ3_startAt` with `irqPreK_of_chain`. The premises
of `irq_pathsJ3` are passed through unchanged (`hA`, `hp` [P], `hz` [W], `hm` [P], `hro` [W], `hlk` [P], `hPL` [P]);
`Fl4Step.start` [P] stays the glue. -/
theorem irq_pathsK_startAt {A3 : Type} {R : S → A3 → Fl4Spec.State Unit → Prop} {A : Type}
    (ar : machine.Arch A) {irq : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop} {p : SProg Bool}
    (hA : P0.ArchTotal ar) (hp : IsProg (Fl4Proofs.P2.irqBody S irq pl) p) (hz : NoZero p)
    (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (Fl4Proofs.P2.IrqPreJ3 K st m) (Fl4Proofs.P2.MaxR K st lk))
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : Fl4Proofs.P2.PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), R σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : R σ a3 τ) (a : A)
    (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt (Fl4Proofs.P2.irq_pathsJ3 ar hA hp hz hm hro hlk hPL () K m hK hU) c hs μ
      ((Fl4Proofs.P2.irq_pathsJ3 ar hA hp hz hm hro hlk hPL () K m hK hU).body σ a) :=
  have h : IrqPreK K st m σ := irqPreK_of_chain h7 hR hM
  Fl4Proofs.P2.irq_pathsJ3_startAt ar hA hp hz hm hro hlk hPL K m hK hU a h.1 h.2 hc hl hμ

end irq

end Fl4Proofs.P2.PathObl
