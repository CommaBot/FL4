/-
# P2 (line invj, generation 6): the PTE-arm Delete block under rule 8 (`IoRSP`, `IoWSP`, `delAccPP`)

The read / write sets of the Delete PTE arm's `ownP` path (pte's rule 8: a leaf `b ∈ K.ptes` is `lock b`'s) and the
decode block on them, under pte's reachability convention (`K.ptes = ptesR K m`, P2/PteReach.lean) at a bundle state
agreeing with `m` on the gate words (`GateAg`), with no VCPU:

* **`IoRSP K Locks s`**: `IoRS` minus every leaf entry not locked (`IoRS` itself unchanged); with the plan's single
  PTE lock `e` it **is** `IoRS` minus every leaf other than `e` (**`ioRSP_eq`**, = `IoRSX … e`);
  **`IoWSP`**: `IoWS` plus the locked leaves;
* the ownership obligations under `ownP`: **`ioRSP_rperm`** (`read_own`: off the leaves `ownP = own` at no VCPU;
  a locked leaf by `rpermP_pte`), **`ioWSP_wperm`** (`write_own`: `wpermP_of_V`, `wpermP_pte`), `ioWSP_aligned`;
* `SlJAtZ.vsJX`: `InvVsJ`'s facts with the sharpened walk read set (`SlJAtZ.vsRdX`);
* **`delAccPP`**: the PTE-arm decode block and reply on any store reading `IoRSP s` and writing `IoWSP s` run as
  on `st` (`delAccX` with `X = K.ptes`: the leaf `e` is in `K.ptes` by `ptesR_of_spe`; the leaves are `ptesR_sub`'s
  leaf entries, so the walk reads none of them).

No named premise. New module; no existing statement changes; no `kernel_entry_reach*` touched.
-/
import Fl4Proofs.P2.InvDelPteAccX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout)
open Fl4Proofs.P3.Vs (PtW)

section vsj
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit} {X : U64 → Prop}

/-- **`InvVsJ`'s facts at a bundle state with the walk read set off `X`** (`invVsJ_of` with `SlJAtZ.vsRdX`). -/
theorem SlJAtZ.vsJX (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) (hsub : ∀ b, X b → PtW Zx.L1 b) :
    ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRdG st (fun b => VsW K b ∧ ¬ X b) s asid va := by
  intro sl fp rt asid va hsl hc _
  have hsl' : Fl4Proofs.P3.IsSlot Zx.th sl := by rw [B.slots] at hsl; exact hsl
  have hcv := Fl4Proofs.P3.capV_of_capAt (mem := L.mem s) (a := sl)
    (by rw [← Fl4Proofs.P3.slot_cap_eq (st := st) sl s]; exact hc)
  have h := B.j.vsc _ hsl'
  rw [hcv] at h
  have h' : (true = true → asid ≠ 0#u64) ∧ Fl4Proofs.P3.Vs.PaM fp (Fl4Proofs.P3.Vs.frameMaskOf .Small) ∧
      (true = true → Fl4Proofs.P3.Vs.UserV va) := h
  have hu := h'.2.2 rfl
  refine ⟨?_, B.spe_ne0 asid va, B.vsRdX hsub asid va hu⟩
  have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
  show va.val ≤ fl4_abi.consts.USER_TOP.val
  rw [hU]
  exact hu

end vsj

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region)

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutP}

variable (st) in
/-- **The PTE arm's read set**: `IoRS` minus every leaf entry that is not locked. -/
def IoRSP (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  IoRS (st := st) K.toKLayout Locks s b ∧ (b ∈ K.ptes → Locks s b)

variable (st) in
/-- **The PTE arm's write set**: `IoWS` plus the locked leaf entries. -/
def IoWSP (K : KLayoutP) (Locks : S → U64 → Prop) (s : S) (b : U64) : Prop :=
  IoWS (st := st) K.toKLayout Locks s b ∨ (b ∈ K.ptes ∧ Locks s b)

/-- **With the plan's single PTE lock `e`, `IoRSP` is `IoRS` minus every leaf other than `e`.** -/
theorem ioRSP_eq {Locks : S → U64 → Prop} {s : S} {e : U64} (hl : Locks s e)
    (hone : ∀ b ∈ K.ptes, Locks s b → b = e) :
    IoRSP st K Locks s = IoRSX st K.toKLayout Locks (· ∈ K.ptes) e s := by
  funext b
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hb => hone b hb (h2 hb)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hb => by rw [h2 hb]; exact hl⟩

theorem ownP_eq_own (nv : K.vcpus = ∅) {m : U64 → U64} {b : U64} (hb : b ∉ K.ptes) :
    ownP K m b = own K.toKLayout m b := by
  rw [ownP_off hb, ownV_off (fun ⟨_, hv⟩ => not_inVcpu_empty nv hv)]

/-- **`read_own` for `IoRSP` under rule 8.** -/
theorem ioRSP_rperm (nv : K.vcpus = ∅) {Locks : S → U64 → Prop} {s : S} {b : U64}
    (h : IoRSP st K Locks s b) : PathObl.RPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) b := by
  by_cases hb : b ∈ K.ptes
  · exact rpermP_pte hb (h.2 hb)
  · have h3 := h.1.2.2
    unfold PathObl.RPerm PathObl.GateOnly at h3 ⊢
    rw [ownP_eq_own nv hb]
    exact h3

/-- **`write_own` for `IoWSP` under rule 8.** -/
theorem ioWSP_wperm (hK : RegionOKP K) (nv : K.vcpus = ∅) {Locks : S → U64 → Prop} {s : S} {b : U64}
    (h : IoWSP st K Locks s b) : PathObl.WPerm (ownP K) (L.cpu s) (Locks s) (L.mem s) b := by
  rcases h with h | ⟨hb, hl⟩
  · refine wpermP_of_V hK ?_
    have h2 := h.2
    unfold PathObl.WPerm at h2 ⊢
    rw [ownV_off (fun ⟨_, hv⟩ => not_inVcpu_empty nv hv)]
    exact h2
  · exact wpermP_pte hb hl

theorem ioWSP_aligned (hU : UserOKP K) {Locks : S → U64 → Prop} {s : S} {b : U64}
    (h : IoWSP st K Locks s b) : Aligned b := by
  rcases h with h | ⟨hb, -⟩
  · exact h.1
  · exact (hU.kern b hb).1

end sets

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (invj gen 6) **The PTE-arm Delete decode block and its reply on any store reading `IoRSP s` and writing
`IoWSP s`** run as on `st` (run-relative), at a bundle state agreeing with the epoch memory `m` on the gate words,
under pte's convention `K.ptes = ptesR K m`, with no VCPU (module docstring). No premise. -/
theorem delAccPP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {K : KLayoutP} {m : U64 → U64}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSP st K Locks s)] [GWr gS st W]
    {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'} {σ : Fl4Spec.State Unit}
    (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ) (hag : GateAg st K m s)
    (hconv : K.ptes = ptesR K m) (nv : K.vcpus = ∅) (hK : RegionOKP K) (hU : UserOKP K)
    (P : IoPre st K.toKLayout K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWSP st K Locks s b → W b)
    (E : DelEntP st K.toKLayout Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
    ptesR_sub B hag b (by rw [← hconv]; exact hb)
  have hpte : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → e ∈ K.ptes :=
    fun asid va e he => by rw [hconv]; exact ptesR_of_spe B hag nv he
  have hlf : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → VsW K.toKLayout e :=
    fun _ _ _ he => B.leafVsW he
  exact delAccX (X := (· ∈ K.ptes)) hA P hW (fun b hb => hWs b (Or.inl hb)) E hsl hlen (B.vsJX hsub)
    (fun b hb => ⟨(hU.kern b hb).1, hK.none b hb, (hU.kern b hb).2⟩)
    (fun b h hx => ⟨h, fun hb => absurd hb hx⟩)
    (fun asid va e he hl => ⟨VsW.ioRS (hlf asid va e he), fun _ => hl⟩) hlf
    (fun asid va e he hl => hWs e (Or.inr ⟨hpte asid va e he, hl⟩)) C hcap hy

end acc

end Fl4Proofs.P2.E2EP
