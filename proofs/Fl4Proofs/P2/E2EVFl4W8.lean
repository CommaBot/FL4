/-
P2 (line famw, gen 6): **`serializable_fl4_localW8` over W6's family, with the bundle at `OmegaU` for vt and a
layout finding for io / vmF / vmR** (new definitions only; no existing statement changes; no `kernel_entry_reach*`
touched; one new P3-side lemma in P3/JCurRunR.lean).

## 1. `IoLay`'s old kernel-block field is false at every P3 layout (`SlJAt.not_ioLayWide`)

`IoLay K` (P2/AccessIoOwn.lean) used to ask `region K b = .none` for **every** word of the 13568-byte kernel-state
block (`IoLayKsWide`). P3's layout `layoutJ` has slots there: the IRQ node's one-slot CNodes at `ksb + 1248 + 32 i`
(`IntLayout.node`, `JAtZ.intL`), and a slot's region is `.slot` (`RegionOK.slot`). So **`SlJAt.not_ioLayWide`**: at
any bundle state, `¬ IoLayKsWide K` — the same fact line slj met for `RegionOKX.ks`. This made io's `IoPre.lay` and
vmF / vmR's `VmLay` unsatisfiable at P3 scope. (Line iolay has since narrowed `IoLay.ks` in place to the aligned
words of the first 256 bytes, as `RegionOKX.ks`; `SlJAt.ioLay` in P2/E2EVFl4W9.lean proves the narrowed `IoLay` at
every bundle state. The former `SlJAt.not_ioLay`, `IoEntJ7.not`, `VmFEntJ7.not`, `VmREntJ7.not` were about the wide
field and are restated here as `not_ioLayWide`; the start facts are satisfiable now, see W9.)

## 2. vt at `OmegaU` (`BunIxU`, `VtEntJ8`)

`BunIx` (W4) fixes `Ω = H.omega`; P3 proves `AsidOff` only at `OmegaU` (the ASID table / pool words are `VsU`
words, `JAtZ.asidOffU`). **`BunIxU`**: the index's sets are the bundle's with `Ω` the bundle witness's `OmegaU`
(`BXI` by `JAtZ.bxiU`, `AsidOff` by `asidOffU`); **`bunIxU_of`**: satisfiable at every bundle state (a choice of
index, as `bunIx_of`). For vt this is a new convention variant beside lvm's (`hΩ : Ω = H.omega` is not used:
**`vexitEnt_P3U`** builds `VexitEnt` at P3 scope without it, every VCPU field vacuous since `vOf = 0`). Then
**`VtEntJ8`** = `nv` + `BunIxU` only: `inv` / `lay` / `ntw` / `aff` / `curAff` / `cscCore` / `cs` / `hAs` / `vf` /
`vlk` / `hvK` all derived (`cs` from line slj's `slJAt_slotJC`, `SlotJ.cs`). **`vtEntJ8_sat`**: at every bundle
state with no VCPU, the vt entry facts hold for an index with the bundle's sets — the vt start record is satisfiable.
vx (`VxEntJ8`): `VxEntJ4` minus `cs` / `curAff` / `cscCore` (derived).

## 3. `run` (P3/JCurRunR.lean)

`JAtZ.curRunR`: `Entered σ` and `NativeScope σ` ⇒ current state word `RESTART` or `RUNNING`. **Missing in P3:**
`NativeScope` (no TCB `runningVM`) at `JAtZ` states — a named premise of P3's native IPC lemmas, stated by no
invariant (`JExt.vw` only zeroes the VCPU words). Not wired into the io / vmF / vmR records here (those are vacuous by
§1 anyway).

## `serializable_fl4_localW8`

Over `fl4LocP3W6` with `StartP3W8`: sl as `StartP3W6`, vx `VxEntJ8`, vt record `VtPremP7` with entry facts
`VtEntJ8`, the rest as `StartP3W7`.

| slot | removed (vs W7 / W6 start facts) | added |
|---|---|---|
| vx | `cs`, `curAff`, `cscCore` [J] | — |
| vt | `VtEntJ4`: `BunIx` (`Ω = H.omega`), `cs`, `curAff`, `cscCore`, `hAs` [J] | `BunIxU` (index convention at `OmegaU`) |
-/
import Fl4Proofs.P2.E2EVFl4W7
import Fl4Proofs.P2.E2EVFl4W6
import Fl4Proofs.P3.JCurRunR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## 1. `IoLay` at a P3 layout -/

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The old (wide) kernel-block field of `IoLay`**: every word of `[ksb, ksb + 13568)` in no region (line iolay
narrowed `IoLay.ks` to the first 256 bytes; this is the former field, kept for the finding). -/
def IoLayKsWide (K : OwnMap.KLayout) : Prop :=
  ∀ b : U64, K.ksb.val ≤ b.val → b.val < K.ksb.val + 13568 → region K b = .none

/-- **The old wide kernel-block field is false at every bundle layout** (module docstring, item 1). -/
theorem SlJAt.not_ioLayWide {K : OwnMap.KLayout} {s : S} (h : SlJAt (L := L) K s) : ¬ IoLayKsWide K := by
  intro hL
  have hRK := h.regionOK
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hI := B.j.intL
  have hk := B.ksb
  have hf := hI.fit
  have hn := hI.node 0#u64 (by simp)
  have hv : (Fl4Proofs.P3.nodeA (L.ksb s) 0#u64).val = (L.ksb s).val + 1248 := by
    have := Fl4Proofs.P3.nodeA_val hf (i := 0#u64) (by simp)
    simpa using this
  have hv2 : (Fl4Proofs.P3.slotOf (Fl4Proofs.P3.nodeA (L.ksb s) 0#u64) 0).val = (L.ksb s).val + 1248 := by
    rw [Fl4Proofs.P3.slotOf_val (by rw [hv]; omega), hv]
  have hs : Fl4Proofs.P3.slotOf (Fl4Proofs.P3.nodeA (L.ksb s) 0#u64) 0 ∈ K.slots := by
    rw [B.slots]
    exact ⟨_, 0, Or.inl ⟨0, hn, by norm_num⟩, rfl⟩
  have hr := hL _ (by rw [hv2, hk]; omega) (by rw [hv2, hk]; omega)
  rw [hRK.slot _ hs] at hr
  cases hr

end lay

/-! ## 2. The bundle at `OmegaU` -/

section bunU
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : OwnMap.KLayout} {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
  {s : S}

/-- **The index's sets are the bundle's, `Ω` its witness's `OmegaU`** (module docstring, item 2; a choice of index:
`bunIxU_of`). -/
structure BunIxU (Kl : OwnMap.KLayout) (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat)
    (Ac : Set U64) (s : S) : Prop where
  hKH : Kl.heap = H
  hT : T = H.tcbs
  hSg : Sg = H.frame
  hRp : Rp = H.replies
  hScs : Scs = H.scs
  hNt : Nt = H.ntfns
  hZ : Z = H.scBits
  /-- Clause 7 at the state, with the index's `Cs` / `Ac` the bundle's ghosts and `Ω` the witness's `OmegaU`. -/
  ac : ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    SlJAtZ (L := L) arI AR Zx Cs Ac Lst D Kl s a' σ ∧ Ω = Fl4Proofs.P3.OmegaU Kl.heap Zx (L.ksb s) σ

/-- **Some index sets satisfy `BunIxU` at every bundle state.** -/
theorem bunIxU_of (h : SlJAt (L := L) Kl s) : ∃ Cs Ac Ω, BunIxU (L := L) Kl Kl.heap.tcbs Cs Ω Kl.heap Kl.heap.frame
    Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact ⟨Cx, Ax, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, rfl⟩⟩

variable (BU : BunIxU (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s)
include BU

theorem BunIxU.slJAtS : SlJAtS (L := L) Kl Cs Ac s := by
  obtain ⟨-, -, -, -, -, -, -, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, -⟩⟩ := BU
  exact ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩

theorem BunIxU.bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨hKH, hT, hSg, hRp, hScs, hNt, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, hΩ⟩⟩ := BU
  subst hKH hT hSg hRp hScs hNt hZ hΩ
  exact B.j.bxiU

theorem BunIxU.asidOff : AsidOff (L := L) Ω Sg s := by
  obtain ⟨hKH, -, hSg, -, -, -, -, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, hΩ⟩⟩ := BU
  subst hKH hSg hΩ
  exact B.j.asidOffU

theorem BunIxU.stLay : StLay Kl st T Scs Z s := by
  obtain ⟨hKH, hT, -, -, hScs, -, hZ, ⟨A', arI, AR, Zx, Lst, D, a', σ, B, -⟩⟩ := BU
  subst hKH hT hScs hZ
  exact B.stLay

theorem BunIxU.aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t) :=
  fun _ ht h0 => (XInv.core_eq BU.bxi.2.2.1 ht h0).symm

theorem BunIxU.ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region Kl (core.num.U64.wrapping_add p k) = .ntfn p := by
  have hL := irqLayK_of_slJAt BU.bxi BU.slJAtS.slJAt
  obtain ⟨hKH, -, -, -, -, hNt, -, -⟩ := BU
  subst hKH hNt
  exact hL.ntw

theorem BunIxU.scsT : ∀ c ∈ Scs, H c = some (.sc (Z c)) := by
  obtain ⟨-, -, -, -, hScs, -, hZ, -⟩ := BU
  subst hScs hZ
  rintro c ⟨z, hz⟩
  simp only [Heap.scBits, hz]

theorem BunIxU.ntT : ∀ q ∈ Nt, H q = some .ntfn := fun q hq => by
  rw [BU.hNt] at hq; exact hq

end bunU

section cur
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {Kl : OwnMap.KLayout} {Cs Ac : Set U64} {s : S}

theorem SlJAtS.curTcbH (h : SlJAtS (L := L) Kl Cs Ac s) : Kl.heap (L.curW s) = some .tcb := by
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := h
  exact B.curTcb.1

/-- The current thread's slot words lie in its TCB slots (line slj's `SlotJ.cs` at the bundle). -/
theorem SlJAtS.cs (h : SlJAtS (L := L) Kl Cs Ac s) :
    ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region Kl (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ OwnMap.TcbSlot Kl p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16 :=
  (slJAt_slotJC h.slJAt).slotJ.cs h.curTcbH

end cur

/-! ## 3. vx / vt entry facts -/

section vt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **lvm's `VexitEnt` at a P3 start without `hΩ`** (module docstring, item 2): every VCPU field vacuous (`vOf = 0`
at a bundle), the bound notification's tail by `vfar_ntfn`. -/
theorem vexitEnt_P3U {K : KLayoutV} {lk : S → U64 → Prop} {n : U64} {s : S} (nv : K.vcpus = ∅)
    (hJ : SlJAt (L := L) K.toKLayout s) (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (curAff : L.mem s (affA (L.curW s)) = L.cpu s) (cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s)
    (hNt : ∀ q ∈ Nt, H q = some .ntfn) :
    VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk (vOf st s) n s := by
  have hX := hI.2.2.1
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  exact ⟨hI, hL, ntw, cs, aff, curAff, cscCore,
    ⟨fun ⟨_, hw⟩ => not_inVcpu_empty nv hw, fun ⟨_, hw⟩ => not_inVcpu_empty nv hw⟩,
    bound_ne0 hJ rfl, bound_ne0 hJ rfl, bound_ne0 hJ rfl,
    fun n' hb hn => by
      rw [← hb] at hn ⊢
      have hNn := hX.2.2.bnd _ hcT hn
      exact vfar_ntfn hI hNn (hNt _ hNn)⟩

end vt

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vt's start entry facts at `OmegaU`** (module docstring, item 2): the layout choice and the index convention. -/
structure VtEntJ8 (i : VtArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention at `OmegaU` (a choice of index: `bunIxU_of`). -/
  ix : BunIxU (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s

theorem VtEntJ8.pre {i : VtArg S} {K : KLayoutV} {s : S} (E : VtEntJ8 st i K s) : VtPre st i K s := by
  have hS := E.ix.slJAtS
  have hJ := hS.slJAt
  have hac := hS.curAffCore
  exact vtmEnt_P3 E.nv hJ
    (vexitEnt_P3U E.nv hJ E.ix.bxi E.ix.stLay E.ix.ntw hS.cs E.ix.aff hac.1 hac.2 E.ix.ntT) E.ix.asidOff

/-- **The vt start entry facts are satisfiable at every bundle state with no VCPU** (module docstring, item 2). -/
theorem vtEntJ8_sat {K : KLayoutV} {s : S} (nv : K.vcpus = ∅) (h : SlJAt (L := L) K.toKLayout s) :
    ∃ Cs Ac Ω : Set U64, ∀ i : VtArg S, i.T = K.heap.tcbs → i.Cs = Cs → i.Ω = Ω → i.H = K.heap →
      i.Sg = K.heap.frame → i.Rp = K.heap.replies → i.Scs = K.heap.scs → i.Nt = K.heap.ntfns →
      i.Z = K.heap.scBits → i.Ac = Ac → VtEntJ8 st i K s := by
  obtain ⟨Cs, Ac, Ω, BU⟩ := bunIxU_of h
  refine ⟨Cs, Ac, Ω, fun i e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 => ⟨nv, ?_⟩⟩
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]
  exact BU

/-- **vx's start entry facts**: `VxEntJ4` minus `cs` / `curAff` / `cscCore` (derived from the bundle). -/
structure VxEntJ8 (i : VxArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] the glue's `v` is the current thread's bound VCPU (fl4-sync's `local_vm_exit`). -/
  hv : i.v = vOf st s
  /-- [J] -/
  usr : ∀ x, x ∈ K.user → Aligned x → UsrW st i.T i.Cs i.H i.Sg i.Scs i.Z s x
  /-- [P] -/
  buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄

theorem VxEntJ8.toJ4 {i : VxArg S} {K : KLayoutV} {s : S} (E : VxEntJ8 st i K s) : VxEntJ4 st i K s :=
  ⟨E.ix, E.hv, E.ix.ac.cs, E.ix.ac.curAffCore.1, E.ix.ac.curAffCore.2, E.usr, E.buf⟩

end ent

/-! ## 4. The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **The start fact of `fl4LocP3W6`, W7's entry facts with vx / vt at `VxEntJ8` / `VtEntJ8`.** -/
def StartP3W8 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .sl j => StartP3W6 st ar hA hm hSt a0 Ch K m hK hU c hs q (.sl j)
  | .vq (.inl j) => ∃ h : VxPremP3 st j K m, GlueAt ((vxSlotP3 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VxEntJ8 st j K σ) c hs m q
  | .vq (.inr j) => ∃ h : VtPremP7 st j K m, GlueAt ((vtSlotP3W5 st ar hA hm).path j K m hK hU h.toP5)
      (fun σ : S => Ch σ ∧ VtEntJ8 st j K σ) c hs m q
  | i => StartP3W7 st ar hA hm hSt a0 Ch K m hK hU c hs q i

/-- **`StartAt` of `fl4LocP3W6`'s family from `StartP3W8`**, given clause 7 on the chain. -/
theorem startAt_P3W8 {Ch : S → Prop} {K : KLayoutV} (hCh : ∀ σ, Ch σ → SlJAt (L := L) K.toKLayout σ)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W8 st ar hA hm hSt a0 Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | sl j => exact startAt_P3W6 st ar hA hm hSt a0 hCh (i := .sl j) h
  | vq j =>
    cases j with
    | inl j =>
      obtain ⟨h, hG⟩ := h
      exact startAt_P3W6 st ar hA hm hSt a0 hCh (i := .vq (.inl j))
        ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ4 st⟩⟩
    | inr j =>
      obtain ⟨h, hG⟩ := h
      show StartAt ((vtSlotP3W5 st ar hA hm).fam (fl4Dflt st ar hm) j K m hK hU) c hs m q
      rw [SlotN.fam_pos _ _ h.toP5]
      exact hG.startAt fun σ he _ => he.2.pre st
  | vmF j => exact startAt_P3W6 st ar hA hm hSt a0 hCh (startP3W5_of_W7 st ar hA hm hSt a0 (i := .vmF j) h)
  | vmR j => exact startAt_P3W6 st ar hA hm hSt a0 hCh (startP3W5_of_W7 st ar hA hm hSt a0 (i := .vmR j) h)
  | io j => exact startAt_P3W6 st ar hA hm hSt a0 hCh (startP3W5_of_W7 st ar hA hm hSt a0 (i := .io j) h)
  | st j => exact startAt_P3W6 st ar hA hm hSt a0 hCh (startP3W5_of_W7 st ar hA hm hSt a0 (i := .st j) h)
  | irq j => exact startAt_P3W6 st ar hA hm hSt a0 hCh (startP3W5_of_W7 st ar hA hm hSt a0 (i := .irq j) h)

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
