/-
P2 (line nscope, gen 2): **the PTE line's layout [J]s (`PteSl`, `VtmP`, `VxP`) from P3's typed-object placement**,
at a canonical choice of `K.ptes`.

`K.ptes` is a layout parameter that the glue picks in `Fl4StepP.ser` [P]; nothing tied it to P3's page tables.
This module fixes the choice and proves the three facts for it from what every P3 joint state (`JAtZ`) carries:
`TopPlaced` (P3/VsTop: `disj` — the kernel-state words outside the IRQ node are `OObj`, page-table words `VObj`,
the two apart; `po` — page-table words lie outside every typed-heap object, so outside the IRQ node's one-slot
CNodes `IntLayout.node`; `pv` — page-table words are no ASID-table / ASID-pool word, `VsWrite`), `VsRel.tmem`
(a nonzero ASID-table entry is a pool of `P`), `PtPlaced` (tables 4 KiB aligned) and `JKern.ksbFit`.

* **`ptesJ Zx`**: the words of P3's page-table objects of ghost `Zx` (`Vs.PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1`: the 512
  entries of every PML4 / PDPT / PD / PT of the ghost sets). The choice at the serial exit state is `ptesJ` of
  that state's bundle ghost.
* **`ptesJ_ks`** / **`ptesJ_tab`** (P3 side, at any `JAtZ` state): no `ptesJ` word in the kernel-state block, and
  `TabNoE (· ∈ ptesJ Zx) s`.
* **`ptesK st Kl`**: the words that are `ptesJ` words of the bundle ghost at *every* bundle state of layout `Kl`
  (and some bundle state exists). It is the canonical choice for which the existing all-states statement holds:
  **`pteSl_of_sub`**: `K.ptes ⊆ ptesK st K.toKLayout → PteSl st K` (the original `PteSl`, both halves).
  Bundle-relative, at one state: **`pteSlAt_of`** (`KsNoE` and `TabNoE` at a bundle state whose ghost's page-table
  words contain `K.ptes`; this is the choice `K.ptes := ptesJ Zx` at the serial exit state).
* `VtmP` / `VxP` quantify over the vt / vx entry states (`VtPre` / `VxPre`), which carry no bundle and do not pin
  `L.ksb s = K.ksb` or the ASID table's memory: **not derivable as stated** for any non-empty choice. Restated
  bundle-relative (new statements, the old ones untouched): **`vtmP_of_bundle`** / **`vxP_of_bundle`** (at a
  state that is also a bundle state of `K.toKLayout`, `K.ptes ⊆ ptesK`); the ingredients **`vtmP_of_ksb`** /
  **`vxP_of_ksb`** (from `KsNoE`, `L.ksb s = K.ksb` and, for `VtmP`, `TabNoE` at `s`).

No new [J]/[P]/[W] premise; the premises are the choice (`K.ptes ⊆ ptesK …` / `⊆ ptesJ Zx`) and the bundle at the
state. No existing statement or file of the pte line changed.
-/
import Fl4Proofs.P2.E2EPLvm
import Fl4Proofs.P2.E2EVTimerLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV

noncomputable section
open Classical

/-- **The PTE words of P3's page-table objects** of the ghost `Zx` (module docstring). -/
def ptesJ (Zx : Fl4Proofs.P3.XSets) : Set U64 := {b | Fl4Proofs.P3.Vs.PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 b}

section p3
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A' : Type} {arI : machine.Arch A'}
  {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64}
  {D : Set U64} {s : S} {a' : A'} {σ : Fl4Spec.State Unit}

/-- **No page-table word in the kernel-state block** at a joint state (`TopPlaced.disj` outside the IRQ node,
`TopPlaced.po` with `IntLayout.node` inside it). -/
theorem ptesJ_ks (J : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ) :
    ∀ o : U64, o.val < 13568 → core.num.U64.wrapping_add (L.ksb s) o ∉ ptesJ Zx := by
  intro o ho hb
  generalize hB : core.num.U64.wrapping_add (L.ksb s) o = b at hb
  obtain ⟨p, hp, i, hi, hbe⟩ := hb
  have hTP := J.xtop.fin.1.2
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  have hpa : p.val % 4096 = 0 := hTP.pt p hp
  have hpv : (Fl4Proofs.P3.Vs.peA p i).val = p.val + 8 * i.val :=
    Fl4Proofs.P3.Vs.peA_val (Fl4Proofs.P3.Vs.tbl_fit hpa) hi
  have hbv : b.val = (L.ksb s).val + o.val := by
    rw [← hB]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hbp : b.val = p.val + 8 * i.val := by rw [hbe]; exact hpv
  by_cases hin : 1248 ≤ o.val ∧ o.val < 5344
  · obtain ⟨j, hjv⟩ : ∃ j : U64, j.val = (o.val - 1248) / 32 := by
      refine ⟨⟨BitVec.ofNat 64 ((o.val - 1248) / 32)⟩, ?_⟩
      show (BitVec.ofNat 64 ((o.val - 1248) / 32)).toNat = _
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hj : j.val < 128 := by omega
    have hn := J.intL.node j hj
    have hnv := Fl4Proofs.P3.nodeA_val hkf hj
    have hout := (hTP.po b ⟨p, hp, i, hi, hbe⟩).2 _ _ hn
    apply hout
    show (Fl4Proofs.P3.nodeA (L.ksb s) j).val ≤ b.val ∧ b.val < (Fl4Proofs.P3.nodeA (L.ksb s) j).val + 32 * 2 ^ 0
    rw [hnv]; omega
  · have hO : (L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568 ∧
        (b.val < (L.ksb s).val + 1248 ∨ (L.ksb s).val + 5344 ≤ b.val) := by omega
    exact hTP.disj b (Or.inr (Or.inl hO)) (Or.inr (Or.inr (Or.inl ⟨p, Or.inr hp, by omega, by omega⟩)))

/-- **No page-table word is an ASID-table or ASID-pool word** at a joint state (`TopPlaced.pv`, `VsRel.tmem`). -/
theorem ptesJ_tab (J : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ) :
    TabNoE (L := L) (· ∈ ptesJ Zx) s := by
  have hTP := J.xtop.fin.1.2
  have hVR := J.xtop.fin.2.1
  intro hi hhi
  refine ⟨fun hb => hTP.pv _ hb (Or.inl ⟨hi, hhi, rfl⟩), fun lo hlo hne hb => ?_⟩
  exact hTP.pv _ hb (Or.inr ⟨_, hVR.tmem hi hhi hne, lo, hlo, rfl⟩)

end p3

section lay
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The canonical PTE set of a layout** (module docstring): the words that are page-table words of the bundle
ghost at every bundle state of `Kl`, at a layout with some bundle state. -/
def ptesK (Kl : OwnMap.KLayout) : Set U64 :=
  {b | (∃ s : S, SlJAt (L := L) Kl s) ∧
    ∀ (s : S) (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
      (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
      SlJAtZ (L := L) arI AR Zx Cx Ax Lst D Kl s a' σ → b ∈ ptesJ Zx}

variable {st}

/-- **`KsNoE` and `TabNoE` at one bundle state**, for any PTE set inside that state's page-table words (the
serial-exit choice `K.ptes := ptesJ Zx`). -/
theorem pteSlAt_of {K : KLayoutP} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
    {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (hsub : K.ptes ⊆ ptesJ Zx) :
    KsNoE (· ∈ K.ptes) K.toKLayoutV ∧ TabNoE (L := L) (· ∈ K.ptes) s := by
  have hk : L.ksb s = K.ksb := B.ksb
  refine ⟨fun o ho hb => ?_, fun hi hhi => ?_⟩
  · have : core.num.U64.wrapping_add (L.ksb s) o ∈ ptesJ Zx := by
      rw [hk]; exact hsub hb
    exact ptesJ_ks B.j o ho this
  · obtain ⟨h1, h2⟩ := ptesJ_tab B.j hi hhi
    exact ⟨fun hb => h1 (hsub hb), fun lo hlo hne hb => h2 lo hlo hne (hsub hb)⟩

/-- **`PteSl` at the canonical choice** (and any smaller PTE set). -/
theorem pteSl_of_sub {K : KLayoutP} (hsub : K.ptes ⊆ ptesK st K.toKLayout) : PteSl st K := by
  refine ⟨fun o ho hb => ?_, fun s hs => ?_⟩
  · obtain ⟨⟨s, A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩, -⟩ := hsub hb
    exact (pteSlAt_of B (fun b hb' => (hsub hb').2 s A' arI AR Zx Cx Ax Lst D a' σ B)).1 o ho hb
  · obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hs
    exact (pteSlAt_of B (fun b hb' => (hsub hb').2 s A' arI AR Zx Cx Ax Lst D a' σ B)).2

/-- **`VxP` from the kernel-state block** (`KsNoE`) at a state with `K`'s kernel base. -/
theorem vxP_of_ksb {K : KLayoutP} {s : S} (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) (hk : L.ksb s = K.ksb) :
    VxP (L := L) K s := by
  refine ⟨?_, ?_⟩
  · rw [hk]; exact hks _ (by simp [layout.ks.CUR_DOMAIN])
  · rw [hk]; exact hks _ (by simp [layout.ks.DOMAIN_TIME])

/-- **`VtmP` from the kernel-state block and the ASID words** at a state with `K`'s kernel base. -/
theorem vtmP_of_ksb {K : KLayoutP} {s : S} (irq : U64) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    (hk : L.ksb s = K.ksb) (htab : TabNoE (L := L) (· ∈ K.ptes) s) : VtmP K st irq s where
  domP := by rw [hk]; exact hks _ (by simp [layout.ks.CUR_DOMAIN])
  dtmP := by rw [hk]; exact hks _ (by simp [layout.ks.DOMAIN_TIME])
  iqP h128 i hi := by
    rw [Fl4Proofs.P3.state_off_eq] at hi
    have e := ok_inj_ff hi
    subst e
    rw [hk]; exact hks _ (by rw [irqOff_val h128]; omega)
  krP := by
    have e : krA (L := L) s = core.num.U64.wrapping_add K.ksb layout.ks.KERNEL_ROOT := by unfold krA; rw [hk]
    rw [e]; exact hks _ (by simp [layout.ks.KERNEL_ROOT])
  tabP := htab

/-- **`VxP` at a vx entry state that is a bundle state** of `K.toKLayout`, at the canonical choice
(bundle-relative variant of the `vxP` field; module docstring). -/
theorem vxP_of_bundle {K : KLayoutP} {s : S} (hsub : K.ptes ⊆ ptesK st K.toKLayout)
    (hs : SlJAt (L := L) K.toKLayout s) : VxP (L := L) K s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hs
  exact vxP_of_ksb (pteSl_of_sub hsub).1 B.ksb

/-- **`VtmP` at a vt entry state that is a bundle state** of `K.toKLayout`, at the canonical choice
(bundle-relative variant of the `vtP` field; module docstring). -/
theorem vtmP_of_bundle {K : KLayoutP} {s : S} (irq : U64) (hsub : K.ptes ⊆ ptesK st K.toKLayout)
    (hs : SlJAt (L := L) K.toKLayout s) : VtmP K st irq s := by
  have hP := pteSl_of_sub hsub
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hs
  exact vtmP_of_ksb irq hP.1 B.ksb (hP.2 s ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩)

end lay

end

end Fl4Proofs.P2.E2EP
