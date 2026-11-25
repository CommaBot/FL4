/-
# P2: the two VM local paths as `E2E.LocalPath` values (line p2e, VM paths)

`vm_localPath` (`syscall.handle_vm_fault_local`, fault address `addr`, code `code`) and `rr_localPath`
(`syscall.handle_reply_recv_vm_local`, `found = (rptr, ep)`), assembled as p2lt's `irq_localPath`
(`P2/FootTimerIrqObl.lean`) from the per-path obligations: `obl` = `vm_pathObl_mv` / `rr_pathObl`,
`side` = `vm_pathSide` / `rr_pathSide`, `once` = `vm_readOnce` / `rr_readOnce`, `total` = `vm_total` /
`rr_total`, with `Pre = VmPre` / `VmRRPre`, the maximal sets `IoRS` / `IoWS` and `DS = IoDS`.

`E2E.LocalPath.F` is generic in the Arch instance; the extracted bodies already are, so `vmBody` / `rrBody`
are the bodies as `F` (no restatement), and `IsProg F p` specialises to the per-`ar` form the obligations take.

**The program premise** (`hpz`, one [P]/[W] premise instead of `hp` / `hz` / `hro`): there is a tree `p` with
* `IsProg F p` [P]: the body is `p` on every store and Arch instance;
* `NoZero p` [W]: `p` has no `zero` / `clr` node. Not provable for an arbitrary `p` with `IsProg` (`p` may
  carry such nodes on branches no store reaches, `handoff/p2io-state.md`), hence stated of the same `p`: a
  pruned reification of the body; the bodies reach `zero` / `clear_free` only through `decode_invocation`,
  which neither VM path calls;
* the `hro` gap [W] of `vm_readOnce` / `rr_readOnce`: at an entry whose handler / receiver is homed on
  another core, `p`'s runs read each racy word once. It is a fact about `p` (no store counts reads,
  `P2/ReadGap.lean`), so it must be of the same `p`: two trees with `IsProg` may differ in how often they read.
`p` is `hpz.choose`.

Premises (besides `hpz`): `hA` (Arch totality), `hK` [J] (`RegionOK`), `hU` [J] (`UserOK`), `hLA` [J]
(`IoLayA`), `hm` [P] (`MasksWr`), `hmA` [J] (`ko`'s memory `m0` agrees with the entry on every TCB's
`AFFINITY`), `huf` [J] (`PathSide.user_free`), and `VmPre` / `VmRRPre`'s fields (`P2/AccessVmObl.lean`,
`P2/AccessVmRRD.lean`).
-/
import Fl4Proofs.P2.AccessVmMv
import Fl4Proofs.P2.AccessVmRRO
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-- The VM-fault body as `E2E.LocalPath.F`. -/
abbrev vmBody (S : Type) (addr code : U64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => syscall.handle_vm_fault_local m ar s a addr code

/-- The VM ReplyRecv body as `E2E.LocalPath.F`. -/
abbrev rrBody (S : Type) (rptr ep : U64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM-fault local path** (module docstring); `hpz` is the program premise ([P] `IsProg`, [W] `NoZero`,
[W] `hro`). -/
noncomputable def vm_localPath (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {addr code : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (vmBody S addr code) p ∧ NoZero p ∧
      ∀ s s' a r, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → (∃ b, VmRep st ar s a b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vmBody S addr code
  p := hpz.choose
  Acc := fun b => b = true
  Locks := Locks
  Pre := VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := hpz.choose_spec.1
  obl := vm_pathObl_mv hA hK hU hLA hmA
    (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
  side := vm_pathSide hA hK hLA (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm huf
  once := vm_readOnce hA hK hLA (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
  total := fun s a => vm_total hA addr code s a
  masks := hm

/-- **The VM ReplyRecv local path** (module docstring); `hpz` is the program premise ([P] `IsProg`,
[W] `NoZero`, [W] `hro`). -/
noncomputable def rr_localPath (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (rrBody S rptr ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := rrBody S rptr ep
  p := hpz.choose
  Acc := fun b => b = true
  Locks := Locks
  Pre := VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := hpz.choose_spec.1
  obl := rr_pathObl hA hK hU hLA hmA
    (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
  side := rr_pathSide hA hK hLA (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm huf
  once := rr_readOnce hA hK hLA (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
  total := fun s a => rr_total hA (rptr, ep) s a
  masks := hm

end

end Fl4Proofs.P2.PathObl
