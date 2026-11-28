/-
P1 (aarch64, gen 52): **`WinOK` carried with the MDB facts** — `MdbSW st T Ω OS s := MdbS st OS s ∧ WinOK T Ω`,
the bundle the MDB tops take and return (gen 51's `WinOK` was a separate hypothesis of the `copy_mdbS` tops beside
`OSOK`). `WinOK` mentions no state, so every step whose sets are fixed keeps it as it is; only a retype (new
`T` / `Ω` = the grown heap's, `PSets.ofHeap`) re-establishes it, by `HeapWin.retype` → `WinOK.ofHeap` (gen 53).

* **`MdbS.empty`** / **`MdbSW.boot`**: at a state whose `OS` slots are all null with zero link words (the boot
  zeroes the slots: `MdbLk.empty`, `RngOneA64.empty`, `KindA.empty`, `NullLk.zero`, `ClsA.empty`) over the sets of
  a window heap (`T ⊆ H.tcbs`, `Ω ⊆ H.omega`, `HeapWin H`; e.g. `HeapWin.empty`), `MdbSW` holds.
* **Where the entry gets it.** The kernel-entry composites (`kernel_entry.entry*`, EntryFin) run over an
  admissible tuple `σ` of an admissibility predicate `Adm` and end over some admissible `σ'`. `WinOK` lives in
  that predicate: **`AdmW Adm σ`** (`Adm σ`, `HeapWin σ.H`, `σ.T ⊆ σ.H.tcbs`, `σ.Ω ⊆ σ.H.omega`) gives
  **`AdmW.win`** (`WinOK σ.T σ.Ω`) at every entry, **`AdmW.ofHeap`** builds it for a heap's own tuple
  (`PSets.ofHeap`, the shape boot and retype produce: `UtRetypeP3.adm`). Using `AdmW Adm` as the composites' `Adm`
  needs the retype obligation to land in `AdmW` — `HeapWin` of the grown heap (`HeapWin.retype`, its window case
  hypothesis on the untyped region) — which is the retype work (gen 53); no existing statement is changed here and
  `WinOK` is in no [J].
* **`DCan.ofWin`**: the deletion tops' canonical-domain hypothesis `DCan D` follows from `D ⊆ OS`, `OSOK` and
  `WinOK` (`OSOK.canon`); so the `MdbSW` deletion tops below drop it.
* Tops over `MdbSW` (start → end): **`cdt.delete.zqETRMW`** / **`threadQETRMW`** (gen 50's `zqETRM` /
  `threadQETRM` without `hDC`), **`cnode.decode.cnode_mdbSW`** / **`syscall.decode_invocation.cnode_mdbSW`**
  (MdbRot's CNode family tops without a separate `WinOK`).

No named premise.
-/
import Fl4ProofsA64.P1.MdbRot
import Fl4ProofsA64.P1.MdbFinR
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

/-- **The admissible tuples with their heap in the kernel window** (module docstring). -/
def AdmW (Adm : PSets → Prop) (σ : PSets) : Prop :=
  Adm σ ∧ HeapWin σ.H ∧ σ.T ⊆ σ.H.tcbs ∧ σ.Ω ⊆ σ.H.omega

/-- **`WinOK` at every `AdmW` tuple.** -/
theorem AdmW.win {Adm : PSets → Prop} {σ : PSets} (h : AdmW Adm σ) : WinOK σ.T σ.Ω :=
  (WinOK.ofHeap h.2.1).mono h.2.2.1 h.2.2.2

/-- **A window heap's own tuple is `AdmW`.** -/
theorem AdmW.ofHeap {Adm : PSets → Prop} {H : Heap} (h : Adm (PSets.ofHeap H)) (hw : HeapWin H) :
    AdmW Adm (PSets.ofHeap H) :=
  ⟨h, hw, subset_rfl, subset_rfl⟩

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-- **The MDB facts with the static kernel window** (module docstring). -/
def MdbSW (st : machine.Store S) [L : LawfulStore st] (T Ω OS : Set U64) (s : S) : Prop :=
  MdbS st OS s ∧ WinOK T Ω

variable {OS : Set U64}

/-- **Boot**: null `OS` slots with zero link words. -/
theorem MdbS.empty {s : S} (h : ∀ x ∈ OS, capA st s x = .Null)
    (hz : ∀ x ∈ OS, L.mem s (wa x 16#u64) = 0#u64 ∧ L.mem s (wa x 24#u64) = 0#u64) : MdbS st OS s :=
  ⟨[], MdbLk.empty h, RngOneA64.empty, KindA.empty h, NullLk.zero fun x hx _ => hz x hx, ClsA.empty h⟩

/-- **Boot**: `MdbSW` over the sets of a window heap. -/
theorem MdbSW.boot {s : S} (h : ∀ x ∈ OS, capA st s x = .Null)
    (hz : ∀ x ∈ OS, L.mem s (wa x 16#u64) = 0#u64 ∧ L.mem s (wa x 24#u64) = 0#u64) {H0 : Heap} (hw : HeapWin H0)
    (hT : T ⊆ H0.tcbs) (hΩ : Ω ⊆ H0.omega) : MdbSW st T Ω OS s :=
  ⟨MdbS.empty h hz, (WinOK.ofHeap hw).mono hT hΩ⟩

/-- **The canonical domain from the window.** -/
theorem DCan.ofWin (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {D : Set U64} (hDO : D ⊆ OS) : DCan D :=
  fun _ hy => hO.canon hW (hDO hy)

section del
variable {Vc Ub D Fp : Set U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **`cdt.delete.zqETRM` over `MdbSW`**, no `DCan` hypothesis (module docstring). -/
theorem cdt.delete.zqETRMW (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hm : MdbSW st T Ω OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ MdbSW st T Ω OS r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.zqETRM hP hPl hO hA hV hDO (DCan.ofWin hO hm.2 hDO) hPp hTb hTe hR hH hS hW hIO hap h hx
    hxI hD hX hN hY h2 hm.1) fun _ ⟨j, y, z, m⟩ => ⟨j, y, z, m, hm.2⟩

/-- **`cdt.delete.threadQETRM` over `MdbSW`**, no `DCan` hypothesis (module docstring). -/
theorem cdt.delete.threadQETRMW (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) (hm : MdbSW st T Ω OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ∧ MdbSW st T Ω OS r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.threadQETRM hP hPl hO hA hV hDO (DCan.ofWin hO hm.2 hDO) hPp hTb hTe hR hH hS hW hIO hap
    h hx hxI hD hN hY h2 hc hid hpF hcov hm.1) fun _ ⟨j, y, z, m⟩ => ⟨j, y, z, m, hm.2⟩

end del

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `cnode.decode` over `MdbSW`** (module docstring). -/
theorem cnode.decode.cnode_mdbSW {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbSW st T Ω OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => MdbSW st T Ω OS s' ⦄ :=
  WP.spec_mono (cnode.decode.cnode_mdbS hO hm.2 q hT hm.1 a hl c hc hx) fun _ h => ⟨h, hm.2⟩

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation` over `MdbSW`** (module docstring). -/
theorem syscall.decode_invocation.cnode_mdbSW {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbSW st T Ω OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ =>
      MdbSW st T Ω OS s' ⦄ :=
  WP.spec_mono (syscall.decode_invocation.cnode_mdbS hO hm.2 q hT hm.1 a len slot cap blk call don fp buf extra hl hf
    hslot hcap hx) fun _ h => ⟨h, hm.2⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
