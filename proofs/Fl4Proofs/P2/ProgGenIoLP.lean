/-
# P2: the I/O port local path with its program premise discharged (line hpzg)

`io_isProg`: the pruned I/O port body `ioBodyP S number` (`P2/IoPrune.lean`) is the generated tree
`R.ioBodyG number` (`P2/ProgGenIo*.lean` on top of `P2/ProgGenL*.lean`, from `xtask/scripts/gen_prog.py`
with `GEN_EXTRA` = `IoPrune` / `IoProgSrc`) on every store and Arch instance; `io_noZero`: that tree has no
`zero` / `clr` node. So `hpz` of `io_localPath` (`P2/AccessIoLP.lean`) holds with `p := R.ioBodyG number` up to
its third part.

`io_localPathG`: `io_localPath` with `hpz` replaced by that remaining part, now a statement about the concrete
tree:
* `hro` [W] (`ReadOnce` at a declining entry, `io_readOnce`): at an alternative of an entry that does not
  accept, the run of `R.ioBodyG number` reads each racy word once (`E2E.Once`).

The other premises are `io_localPath`'s, unchanged: `hA` (Arch totality), `hK` [J], `hU` [J], `hLA` [J],
`hm` [P], `hPE` (`Pre` gives `IoPre`), `hmA` [J], `huf` [J].
-/
import Fl4Proofs.P2.AccessIoLP
import Fl4Proofs.P2.ProgGenIoTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-- **`IsProg` for the pruned I/O port body**: it is the generated tree, on every store and Arch instance. -/
theorem io_isProg (S : Type) (number : I64) : IsProg (ioBodyP S number) (R.ioBodyG number) := by
  intro A ar st
  funext s a
  show ioBodyP S number ar st s a = _
  rw [ioBodyP_eq_G, R.ioBodyG_eq st ar, bind_proj3]

theorem io_noZero (number : I64) : NoZero (R.ioBodyG number) :=
  R.ioBodyG_nz number

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **The I/O port local path, `IsProg` / `NoZero` discharged** (module docstring): `io_localPath` with the
program `R.ioBodyG number`; `hro` [W] is the remaining read-once part. -/
noncomputable def io_localPathG (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hU : E2E.UserOK K) (hLA : IoLayA K) {number : I64} (hm : E2E.MasksWr st)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmA : ∀ s, P s → ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hro : ∀ s s' a r, P s → (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.ioBodyG number) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.ioBodyG number) s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  io_localPath (Locks := Locks) ar hA hK hU hLA hm hPE hmA huf
    ⟨R.ioBodyG number, io_isProg S number, io_noZero number, hro⟩

end

end Fl4Proofs.P2.PathObl
