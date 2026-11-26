/-
# P2: the top-level path members with `IsProg` / `NoZero` discharged by the generated trees (line hpzg, gen 3)

The `E2E.Paths` members on the integration branch (int/j13) take the program premise family as `hpz`
(`∃ p, IsProg … p ∧ NoZero p ∧ <read-once of p>`) or as `hp` / `hz` / `hro` of a free tree `p`. Here each
takes the generated tree (`P2/ProgGen*.lean`) for `p`: `IsProg` and `NoZero` are the `…_isProg` /
`…_noZero` theorems, and the one premise left is the read-once part, now stated of the concrete tree.

* `io_pathsKG` / `io_pathsKG_startAt`: SlJStLocTop's `io_pathsK` at `R.ioBodyG number` (`io_isProg`,
  `io_noZero`); premise `hro` [W]: declining-entry `Once` of `R.ioBodyG number` (as `io_localPathG`).
* `tm_pathsKG` / `tm_pathsKG_startAt`: `tm_pathsK` at `R.localtimer.handle_set_timer_local n target`
  (`st_isProg`, `st_noZero`); premise `hro` [W]: `ReadOnce` of that tree.
* `sl_pathsKCG` / `sl_pathsKCG_startAt`: SlJQ's `sl_pathsKC` at `R.syscall.handle_syscall_local n found`
  (`sl_isProg`, `sl_noZero`); premise `hro` [W]: `ReadOnce` of that tree.
* `irq_pathsJ3G` / `irq_pathsJ3G_startAt` / `irq_pathsKG_startAt`: p2lt2's `irq_pathsJ3` and int13's
  `irq_pathsK_startAt` at `R.localtimer.handle_timer_irq_local irq pl` (`irq_isProg`, `irq_noZero`): `hp` [P]
  and `hz` [W] gone; premise `hro` [W]: `ReadOnce` of that tree.

All other premises are passed through unchanged. No new premise.
-/
import Fl4Proofs.P2.SlJStLocTop
import Fl4Proofs.P2.SlJQ
import Fl4Proofs.P2.ProgGenIoLP
import Fl4Proofs.P2.ProgGenSyLP
import Fl4Proofs.P2.ProgGenStLP
import Fl4Proofs.P2.ProgGenTmLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

/-! ## The I/O port path -/

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- The read-once premise of the I/O port path at the generated tree, per layout. -/
abbrev IoHro (ar : machine.Arch A) (number : I64) (Q : KLayout → (U64 → U64) → S → Prop) : Prop :=
  ∀ K m, ∀ s s' a r, (SlJAt (L := L) K s ∧ Q K m s) →
    (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
    Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) s s' →
    interp st ar (R.ioBodyG number) s' a = ok r →
    Fl4Proofs.P2.E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.ioBodyG number) s' a

/-- **`io_pathsK` at the generated tree** (module docstring); `hro` [W]. -/
noncomputable def io_pathsKG (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
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
    (hro : IoHro (L := L) (Locks := Locks) ar number Q) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  io_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf
    (fun K m => ⟨R.ioBodyG number, io_isProg S number, io_noZero number, hro K m⟩)

/-- **`StartAt` for `io_pathsKG`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem io_pathsKG_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64)
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
    (hro : IoHro (L := L) (Locks := Locks) ar number Q)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hQ : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (io_pathsKG (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf hro
        () K m hK hU) c hs μ
      ((io_pathsKG (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number hm Q hPE hmA huf hro
        () K m hK hU).body σ a) :=
  io_pathsK_startAt ar hA number hm Q hPE hmA huf _ K m hK hU a hJ hQ hc hl hμ

end io

/-! ## The `TCB_SetTimer` path -/

section tm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop}
variable {A : Type}

/-- **`tm_pathsK` at the generated tree** (module docstring); `hro` [W]. -/
noncomputable def tm_pathsKG (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local n target) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (StEntKK K st Cs Ω Sg Ac target m) (Fl4Proofs.P2.MaxR K st lk))
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
  tm_pathsK (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE
    (fun K m => ⟨_, Fl4Proofs.P2.st_isProg S n target, Fl4Proofs.P2.st_noZero n target, hro K m⟩)
    hEU hlk hNU huf

/-- **`StartAt` for `tm_pathsKG`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem tm_pathsKG_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local n target) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (StEntKK K st Cs Ω Sg Ac target m) (Fl4Proofs.P2.MaxR K st lk))
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
      (tm_pathsKG (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hro hEU hlk hNU huf
        () K m hK hU) c hs μ
      ((tm_pathsKG (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hro hEU hlk hNU huf
        () K m hK hU).body σ a) :=
  tm_pathsK_startAt ar hA n target hm Q hPE _ hEU hlk hNU huf K m hK hU a hJ hQ hc hl hμ

end tm

/-! ## The syscall local path (canonical `Q`) -/

section sl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`sl_pathsKC` at the generated tree** (module docstring); `hro` [W]. -/
noncomputable def sl_pathsKCG (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hArw : ∀ K s b v, SlJAt (L := L) K s → SlAccR (st := st) ar K Locks found s → b ∈ K.user →
      Aligned b → SlAccR (st := st) ar K Locks found (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.syscall.handle_syscall_local n found) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
      (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKC (Locks := Locks) ar hSt hA hm a0 hPBw hArw hlk
    (fun K m => ⟨_, sl_isProg S n found, sl_noZero n found, hro K m⟩)

/-- **`StartAt` for `sl_pathsKCG`**. -/
theorem sl_pathsKCG_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hArw : ∀ K s b v, SlJAt (L := L) K s → SlAccR (st := st) ar K Locks found s → b ∈ K.user →
      Aligned b → SlAccR (st := st) ar K Locks found (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.syscall.handle_syscall_local n found) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
      (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKCG (Locks := Locks) ar hSt hA hm a0 hPBw hArw hlk hro () K m hK hU) c hs μ
      ((sl_pathsKCG (Locks := Locks) ar hSt hA hm a0 hPBw hArw hlk hro () K m hK hU).body σ a) :=
  sl_pathsKC_startAt ar hSt hA hm a0 hPBw hArw hlk _ K m hK hU a hJ hq hc hl hμ

end sl

/-! ## The timer interrupt path -/

section irq
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) {irq : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}

/-- **`irq_pathsJ3` at the generated tree** (module docstring): `hp` / `hz` discharged; `hro` [W]. -/
noncomputable def irq_pathsJ3G (hA : P0.ArchTotal ar) (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (Fl4Proofs.P2.IrqPreJ3 K st m) (Fl4Proofs.P2.MaxR K st lk))
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : Fl4Proofs.P2.PlanLk lk pl) : Fl4Proofs.P2.E2E.Paths Unit :=
  Fl4Proofs.P2.irq_pathsJ3 ar hA (Fl4Proofs.P2.irq_isProg S irq pl) (Fl4Proofs.P2.irq_noZero irq pl) hm hro hlk hPL

/-- **`StartAt` for `irq_pathsJ3G`** (`irq_pathsJ3_startAt` at the generated tree). -/
theorem irq_pathsJ3G_startAt (hA : P0.ArchTotal ar) (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (Fl4Proofs.P2.IrqPreJ3 K st m) (Fl4Proofs.P2.MaxR K st lk))
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : Fl4Proofs.P2.PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt (irq_pathsJ3G ar hA hm hro hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ3G ar hA hm hro hlk hPL () K m hK hU).body σ a) :=
  Fl4Proofs.P2.irq_pathsJ3_startAt ar hA _ _ hm hro hlk hPL K m hK hU a hJ hM hc hl hμ

/-- **int13's `irq_pathsK_startAt` at the generated tree**: every state of a chain carrying `SlJAt K`
(`loc_chain_all`'s clause 7 as `h7`) agreeing with `m` off the user words is a start of `irq_pathsJ3G`. -/
theorem irq_pathsKG_startAt {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (hA : P0.ArchTotal ar) (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hro : ∀ K m, Fl4Proofs.P2.E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) (Fl4Proofs.P2.IrqPreJ3 K st m) (Fl4Proofs.P2.MaxR K st lk))
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : Fl4Proofs.P2.PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A)
    (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt (irq_pathsJ3G ar hA hm hro hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ3G ar hA hm hro hlk hPL () K m hK hU).body σ a) :=
  irq_pathsK_startAt ar hA _ _ hm hro hlk hPL K m hK hU h7 hR a hM hc hl hμ

end irq

end Fl4Proofs.P2.PathObl
