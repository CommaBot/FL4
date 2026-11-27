/-
# P2: the VM-fault local path with its program premise discharged (line hpzg)

`vm_isProg`: `syscall.handle_vm_fault_local` is the generated tree `R.syscall.handle_vm_fault_local addr code`
(`P2/ProgGenL*.lean`, from `xtask/scripts/gen_prog.py`) on every store and
Arch instance, and `vm_noZero`: that tree has no `zero` / `clr` node. So `hpz` of `vm_localPath`
(`P2/AccessVmLP.lean`) holds with `p := R.syscall.handle_vm_fault_local addr code` up to its third part.

`vm_localPathG`: `vm_localPath` with `hpz` replaced by that remaining part, now a statement about the concrete
tree:
* `hro` [W] (the `hro` gap of `vm_readOnce`): at an entry whose handler is homed on another core, the runs of
  `R.syscall.handle_vm_fault_local addr code` from alternative states read each racy word once (`E2E.Once`).

The other premises are `vm_localPath`'s, unchanged: `hA` (Arch totality), `hK` [J], `hU` [J], `hLA` [J],
`hm` [P], `hmA` [J], `huf` [J], and `VmPre`'s fields.
-/
import Fl4Proofs.P2.AccessVmLP
import Fl4Proofs.P2.ProgGenLTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-- **`IsProg` for the VM-fault body**: it is the generated tree, on every store and Arch instance. -/
theorem vm_isProg (S : Type) (addr code : U64) :
    IsProg (vmBody S addr code) (R.syscall.handle_vm_fault_local addr code) := by
  intro A ar st
  funext s a
  rw [R.syscall.handle_vm_fault_local_eq st ar, bind_proj3]

theorem vm_noZero (addr code : U64) : NoZero (R.syscall.handle_vm_fault_local addr code) :=
  R.syscall.handle_vm_fault_local_nz addr code

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- `hpz` of `vm_localPath` from the generated tree and the read-once part `hro` [W]. -/
theorem vm_hpz {addr code : U64}
    (hro : ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.syscall.handle_vm_fault_local addr code) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s' a) :
    ∃ p : SProg Bool, IsProg (vmBody S addr code) p ∧ NoZero p ∧
      ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a :=
  ⟨_, vm_isProg S addr code, vm_noZero addr code, hro⟩

/-- **The VM-fault local path, `IsProg` / `NoZero` discharged** (module docstring): `vm_localPath` with the
program `R.syscall.handle_vm_fault_local addr code`; `hro` [W] is the remaining read-once part. -/
noncomputable def vm_localPathG (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {addr code : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hro : ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar (R.syscall.handle_vm_fault_local addr code) s' a = ok r →
      Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vmBody S addr code
  p := R.syscall.handle_vm_fault_local addr code
  Acc := fun b => b = true
  Locks := Locks
  Pre := VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := IsProg.on (vm_isProg S addr code) _ _ _
  obl := vm_pathObl_mv hA hK hU hLA hmA
    (fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a)
  side := vm_pathSide hA hK hLA (fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a)
    (vm_noZero addr code) hm huf
  once := vm_readOnce hA hK hLA (fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a)
    (vm_noZero addr code) hm hro
  total := fun s a => vm_total hA addr code s a
  masks := hm

end

end Fl4Proofs.P2.PathObl
