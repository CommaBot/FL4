/-
# P2: the syscall local path with its program premise discharged (line hpzg)

`sl_isProg`: `syscall.handle_syscall_local` is the generated tree `R.syscall.handle_syscall_local n found`
(`P2/ProgGenL*.lean`, from `xtask/scripts/gen_prog.py`) on every store and
Arch instance; `sl_noZero`: the tree has no `zero` / `clr` node.

`sl_localPathG`: `sl_localPath` (`P2/SlLP.lean`) with `hpz` replaced by its remaining part, a statement about
the concrete tree:
* `hro` [W] (`E2E.ReadOnce` of `R.syscall.handle_syscall_local n found`).

The other premises are `sl_localPath`'s, unchanged.
-/
import Fl4Proofs.P2.SlLP
import Fl4Proofs.P2.ProgGenLTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

/-- **`IsProg` for the syscall body**: it is the generated tree, on every store and Arch instance. -/
theorem sl_isProg (S : Type) (n : I64) (found : U64 × U64) :
    IsProg (slBody S n found) (R.syscall.handle_syscall_local n found) := by
  intro A ar st
  funext s a
  rw [R.syscall.handle_syscall_local_eq st ar, bind_proj3]

theorem sl_noZero (n : I64) (found : U64 × U64) : NoZero (R.syscall.handle_syscall_local n found) :=
  R.syscall.handle_syscall_local_nz n found

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

/-- **The syscall entry beside the gate as a local path, `IsProg` / `NoZero` discharged** (module
docstring); `hro` [W] is the read-once part of the former `hpz`, now about the generated tree. -/
noncomputable def sl_localPathG (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hK : RegionOK K) (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K) (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hSe : SlSets K T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hEj : ∀ s, P s → SlEntJ (st := st) K Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hro : Fl4Proofs.P2.E2E.ReadOnce st ar (R.syscall.handle_syscall_local n found) (OwnMap.cls K)
      (OwnMap.ko K m0) (· ∈ K.user) P (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := slBody S n found
  p := R.syscall.handle_syscall_local n found
  Acc := fun b => b = true
  Locks := Locks
  Pre := P
  RS := SlRS (st := st) K Locks
  WS := SlWS (st := st) K Locks
  DS := SlDS (L := L)
  isProg := sl_isProg S n found
  obl := sl_pathObl_e ar hSt hA hK hX hU (sl_isProg S n found) (sl_noZero n found) hm hSe hUu a0 hPE hEj hHj
    hAk
  side := sl_pathSide_e ar hSt hA hK hX hU (sl_isProg S n found) (sl_noZero n found) hm hSe hUu a0 hPE hEj
    hHj hAk huf
  once := hro
  total := fun s a => sl_total hSt hA n found s a
  masks := hm

end

end Fl4Proofs.P2.PathObl
