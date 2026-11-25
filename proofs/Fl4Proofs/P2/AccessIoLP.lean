/-
# P2: the I/O port local path as an `E2E.LocalPath` value (line p2io)

`io_localPath` (`syscall.handle_ioport_local`, syscall number `number`), assembled as p2lt's
`irq_localPath` (`P2/FootTimerIrqObl.lean`) and p2e's `vm_localPath` (`P2/AccessVmLP.lean`, par/p2vm-m)
from the per-path obligations: `obl` = `io_pathObl_mv`, `side` = `io_pathSide`, `once` = `io_readOnce`,
`total` = `io_total`, with `Pre` any `P` giving `IoPre`, the maximal sets `IoRS` / `IoWS` and `DS = IoDS`.

* `io_total`: P0's totality of the body;
* `io_readOnce`: an accepting entry runs on `PathObl.guard st (IoRS s) (IoWS s)` (`io_acc`), so does every
  alternative (`interp_agree`), and a guarded run reads no racy word (`once_of_guardG`: `IoRS` holds no
  user word); a declining entry is the premise `hro` [W];
* `ioBody`: the extracted body is already generic in the Arch instance, so it is `F` as is.

**The program premise** (`hpz`, one [P]/[W] premise instead of `hp` / `hz` / `hro`): there is a tree `p` with
* `IsProg F p` [P]: the body is `p` on every store and Arch instance;
* `NoZero p` [W]: `p` has no `zero` / `clr` node; not provable for an arbitrary `p` with `IsProg`
  (`handoff/p2io-state.md`), hence stated of the same `p`, a pruned reification of the body;
* `hro` [W] (`ReadOnce` at a declining entry): at an alternative of an entry that does not accept, `p`'s run
  reads each racy word once. The declining run at an alternative may read words outside `IoRS s` (a CSpace
  slot whose `Null` / `Frame` cap changed, `P2/AccessIoRa.lean`), and no store instance counts reads
  (`P2/ReadGap.lean`), so it is a fact about `p`, of the same `p`. Checked true of the extracted body
  (`proofs/Fl4Core/Funs.lean`): the run reads no user word (`ioport.invocation_ok` l.32298 reads the port
  by `msg.syscall_arg … 0` l.3187, a register); its only reads outside `IoRS s` are CSpace slots of the
  walk (`cspace.resolve_address_bits_loop.body` l.3790). A slot holding a CNode cap at `s'` held it at `s`
  and is then in `IoRS s` (`WalkRc`, `slot_back`); any other slot read ends the walk with `bits_left ≠ 0`,
  and `invocation_ok` then declines without reading it again; the final slot (`n = level`) is not read by
  the walk and is read once by `invocation_ok`. So each word outside `IoRS s` is read at most once.
`p` is `hpz.choose`.

Premises (besides `hpz`): `hA` (Arch totality), `hK` [J] (`RegionOK`), `hU` [J] (`UserOK`), `hLA` [J]
(`IoLayA`), `hm` [P] (`MasksWr`), `hPE` (`Pre` gives `IoPre`, whose fields are the entry facts),
`hmA` [J] (`ko`'s memory `m0` agrees with the entry on every TCB's `AFFINITY`), `huf` [J]
(`PathSide.user_free`).
-/
import Fl4Proofs.P2.AccessIoMv
import Fl4Proofs.P2.OnceGuard
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-- The I/O port body as `E2E.LocalPath.F`. -/
abbrev ioBody (S : Type) (number : I64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => syscall.handle_ioport_local m ar s a number

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- P0's totality of the body. -/
theorem io_total (hA : P0.ArchTotal ar) (number : I64) (s : S) (a : A) :
    ∃ r, syscall.handle_ioport_local st ar s a number = ok r := by
  obtain ⟨r, e, -⟩ := spec_ex_fd (P0.syscall.handle_ioport_local.p0 st ar s a number L.total hA)
  exact ⟨r, e⟩

/-- **`ReadOnce` for the I/O port path** (module docstring), the declining entries a premise (`hro` [W]). -/
theorem io_readOnce (hA : P0.ArchTotal ar) {number : I64} {p : SProg Bool}
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_ioport_local m ar x a number = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hro : ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) P (IoRS (st := st) K Locks) := by
  intro s s' a r hE Al h
  by_cases hac : ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := io_acc (Locks := Locks) hA (hPE s hE) h0
    rw [hp] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true s1 a1
      Al.ksb Al.cpu Al.masks Al.read hg
    exact once_of_guardG (fun q hq => hq.2.1) p hz ∅ ∅ s' a _ hg'
  · exact hro s s' a r hE hac Al h

/-- **The I/O port local path** (module docstring); `hpz` is the program premise ([P] `IsProg`, [W] `NoZero`,
[W] `hro`). -/
noncomputable def io_localPath (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (hLA : IoLayA K) {number : I64} (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (ioBody S number) p ∧ NoZero p ∧
      ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
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
  isProg := hpz.choose_spec.1
  obl := io_pathObl_mv hA hK hU hLA hPE hmA
    (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
  side := io_pathSide hA hK hLA hPE (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm huf
  once := io_readOnce hA hPE (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
  total := fun s a => io_total hA number s a
  masks := hm

end

end Fl4Proofs.P2.PathObl
