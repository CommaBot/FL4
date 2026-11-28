/-
# P2 (line vmscope, gen 2): one VT-x layout fact for the VM epochs — `serializable_fl4_localVX2S`

`serializable_fl4_localVX1` (P2/E2EPVX1.lean) runs the VM-exit slot in VM epochs under four [S] premises:
`VtxLayP K'` at a VM serial exit, the slot record's `vu : VcpuNU K` and `eu : VxEuX`, and the start state's
`VexitEnt ∧ VexitPEnt ∧ QPs`. This module replaces the first three by **one** layout fact, `VtxBundle`, stated once per
VM epoch (at the serial exit that opens it), and derives the rest:

* **`UserLayX L K`**: the store-free part of P3's bundle that the user-write frame lemmas read (`RegionOKX`, `LayP`,
  user words in no TCB / endpoint / notification / reply / SC, off the kernel-state block and every core's node,
  `ncores ≤ 64`). **`UserLayX.ofSlJAt`**: every P3 bundle state gives it (so it is exactly what the native epochs
  already have).
* **`bxi_userX`** (`bxi_userJ` from `UserLayX`), **`vexitEnt_wrV`** / **`vexitPEnt_wrV`**: `vexitEnt_wr` /
  `vexitPEnt_wr` with the VCPU clauses live (`vin`, `vfit` state-free; `vlk` by the lock map's `hlk`; `vfar`, `pusr`
  by `.ksb`), from `UserLayX` instead of a P3 bundle and without `nv`.
* **`VxIx`** (index convention, the store-free part of `BunIx`: a choice of index, untagged as `BunIx`'s fields) and
  **`vxEu_ofV`**: the slot's `eu` from `UserLayX`, `VxIx` and `kd` [P].
* **`VtxBundle L K`** [S] (module table): `RegionOK` / `E2E.UserOK` of the base layout, `UserLayX`, `VcpuHeap`
  (VCPUs are `other 15` heap objects), the slots apart from every VCPU, and `UserObj` (no user word in a VCPU).
  **`VtxBundle.okP`**: with the native PTE convention `K.ptes = ptesR K m` it gives `RegionOKP K ∧ UserOKP K`
  (`regionOKV_of`, `regionOKP_R`, `userOKP_R`), i.e. VX1's `VtxLayP`; **`VtxBundle.vu`**: `VcpuNU`.
  **`vtxBundle_of_vfacts`** / **`vtxBundle_of_jvm`**: at any P3 bundle state, the existing VT-x layout cluster
  (`VFacts` [J], or `JVmL` [J]) gives `VtxBundle` (consistency with the native facts; `vtxBundle_of_empty`: every
  native layout has it).
* **`VxPremV2`** (`hv0`, `ix`, `kd` [P]; no [S]) with **`VxPremV2.toV`** (`VxPremV` from it and `VtxBundle`).
* **`Fl4StepVX2`** / **`ExecVX2`**: `ExecVX` with the VM serial exit's layout fact `K'.vcpus ≠ ∅ ∧ K'.ptes =
  ptesR K' s'.mem ∧ VtxBundle L K'` (the PTE convention as at native exits); **`execVX_of_VX2`**: an `ExecVX2` is an
  `ExecVX` whose start facts also carry the epoch's bundle (`K.vcpus ≠ ∅ → VtxBundle L K`, the epoch invariant).
* **`VxStartV2`** [S] (the start entry only: `VxPre ∧ QPs` at the start state, `GlueAt`'s data [P]),
  **`vxStartV2_ne`**, **`vxStartV_of_V2`**; **`StartVX2`**, **`serializable_fl4_localVX2SG`**,
  **`serializable_fl4_localVX2S`** (U1's family ⊕ `vxSlotPV`, as VX1).

## Premises in VM epochs, VX1 → VX2S
| VX1 | VX2S |
|---|---|
| `VtxLayP K'` [S] at a VM serial exit | `VtxBundle L K'` [S] at a VM serial exit (+ PTE convention, as native exits) |
| `VxPremV.vu : VcpuNU K` [S] | derived: `VtxBundle.vu` (field `vu : UserObj`) |
| `VxPremV.eu : VxEuX` [S] | derived: `vxEu_ofV` (`UserLayX`, `VxIx` index convention, `kd` [P]) |
| start entry `VexitEnt ∧ VexitPEnt ∧ QPs` [S] | unchanged [S] (`VxStartV2`) |
| `kd`, `GlueAt`, `arm`, `serG`, `HwStepP` [P] | unchanged |

`VtxBundle`'s justification: native states have every field (`vtxBundle_of_jvm` from a P3 bundle and `JVmL`); at a
guest-running state FL4's layout is the same (VCPU objects are untyped-retyped `other 15` objects of 32 KiB, never
user frames, never covering a CNode slot; P3 does not reach such a state, `JExt.nat` / `.vw`), so it is [S] (scope),
not [J]. No new [J] / [W] / [P]. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW RegionOK LayP)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg xsafeRun_greach allowed_of_sinv)

noncomputable section
open Classical

/-! ## The store-free user-word layout facts -/

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The user-word layout facts** (module docstring): what the user-write frame lemmas read off P3's bundle. -/
structure UserLayX (L : LawfulStore st) (K : KLayout) : Prop where
  rx : RegionOKX K
  lp : LayP K
  uobj : ∀ x ∈ K.user, ∀ p k, K.heap p = some k → (∀ z, k ≠ .other z) → ¬ InW p (2 ^ k.bits) x
  uks : ∀ x ∈ K.user, ∀ o : U64, o.val < 13568 → x ≠ core.num.U64.wrapping_add K.ksb o
  unode : ∀ x ∈ K.user, ∀ c : U64, c.val < 64 → ∀ s : S, L.ksb s = K.ksb →
    x.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ x.val
  nc : K.ncores ≤ 64

variable {K : KLayout}

theorem UserLayX.userObj (U : UserLayX L K) {x : U64} (hx : x ∈ K.user) {p : U64} {k : HKind}
    (hp : K.heap p = some k) (hk : ∀ z, k ≠ .other z) : ¬ InW p (2 ^ k.bits) x :=
  U.uobj x hx p k hp hk

/-- **Every P3 bundle state gives `UserLayX`.** -/
theorem UserLayX.ofSlJAt {s : S} (B : SlJAt (L := L) K s) : UserLayX L K where
  rx := B.regionOKX
  lp := B.layP
  uobj := fun _ hx _ _ hp hk => B.userObj hx hp hk
  uks := fun _ hx _ ho => B.userKs hx ho
  unode := fun _ hx c hc s' hs' => by
    have h := B.userNode64 hx hc
    have e : L.nodeBase s' c = L.nodeBase s c := by
      simp only [LawfulStore.nodeBase, hs', B.kc.1]
    rw [e]; exact h
  nc := B.ncores_le

/-- **`BXI` across a write of user words** (`bxi_userJ` from `UserLayX`). -/
theorem bxi_userX {X X' : S} (B : UserLayX L K) (hkK : L.ksb X = K.ksb) {Cs Ω Sg Ac : Set U64}
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (h : BXI st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac X)
    (G : Ag st (NU K) X X') :
    BXI st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac X' := by
  have hX := B.rx
  have h1 := BXI.shrinkU (U := {b | b ∈ K.user ∧ Aligned b}) h
    (fun r hr b h1 h2 hu => B.userObj hu.1 (k := .reply) hr (fun z e => by cases e) ⟨h1, by
      show b.val < r.val + 2 ^ 5; omega⟩)
    (fun c hc b hin hu => B.userObj hu.1 (scs_heap hc) (fun z e => by cases e) hin)
    (fun c hc o h1 h2 hu => (nu_scw hX (scs_heap hc) h1 h2).2 hu.1)
    (fun n hn o h1 h2 hu => (nu_of_region hX (hX.ntW n hn o h1 h2).2.2
      (by rw [(hX.ntW n hn o h1 h2).1]; intro h; cases h)).2 hu.1)
    (fun o h1 h2 hu => B.uks _ hu.1 o h1 (by rw [← hkK]))
  have hUO : UserOK st K.heap.tcbs Cs {a | a ∈ Ω ∧ a ∉ {b | b ∈ K.user ∧ Aligned b}} K.heap
      {b | b ∈ K.user ∧ Aligned b} X := by
    intro b hb
    obtain ⟨hu, ha⟩ := hb
    refine ⟨⟨ha, fun t ht => ?_, fun c hc => ?_⟩, fun h => h.2 ⟨hu, ha⟩, fun e he => ?_⟩
    · have := B.userObj hu (k := .tcb) ht (fun z e => by cases e)
      simp only [InW, HKind.bits] at this
      omega
    · have h := B.unode b hu c (hCs c hc) X hkK
      omega
    · have hH := B.lp.heap
      rcases he with he | he
      · have := B.userObj hu he (fun z e => by cases e)
        have hal : e.val % 16 = 0 := by simpa [HKind.bits] using hH.align e _ he
        simp only [InW, HKind.bits] at this
        unfold Aligned at ha
        omega
      · have := B.userObj hu he (fun z e => by cases e)
        have hal : e.val % 64 = 0 := by simpa [HKind.bits] using hH.align e _ he
        simp only [InW, HKind.bits] at this
        unfold Aligned at ha
        omega
  obtain ⟨⟨Q, R, h0⟩, hB, hXi, hSg, hS⟩ := h1
  obtain ⟨h1', hB1, hX1, hS1, hSg1, -⟩ := xfer_all h0 hB hXi hS hSg hUO
    (G.writesIn.mono' fun b hb hu => Or.inr ⟨hu, hb⟩)
  exact BXI.growU h G.k ⟨⟨Q, R, h1'⟩, hB1, hX1, hSg1, hS1⟩

end lay

/-! ## The VM-exit entry facts across a user write, VCPU clauses live -/

section fr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop} {v n : U64}

/-- **`VexitEnt` across a user-word write** at any layout (`vexitEnt_wr` without `nv`: `vin` state-free, `vlk` by
`hlk`, `vfar` by `.ksb`). -/
theorem vexitEnt_wrV {X : S} (B : UserLayX L K.toKLayout) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b w, b ∈ K.user → Aligned b → lk (L.wr s b w) = lk s)
    (E : VexitEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk v n X)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (w : U64) :
    VexitEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk v n
      (L.wr X b w) := by
  have hX := B.rx
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hk : L.ksb X = K.ksb := ksb_of_stLay E.lay hN
  have G : Ag st (NU K.toKLayout) X (L.wr X b w) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb w hx⟩
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr X b w) (L.nodeAt (L.wr X b w) (L.cpu (L.wr X b w)) o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by
      rw [nodeAt_wr, L.cpu_wr]
      exact wr_nu hba hb w ⟨nodeAt_aligned hN ho h8, E.lay.nu_node ho⟩
  have ecur : L.curW (L.wr X b w) = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW (L.wr X b w) = L.cscW X :=
    eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := E.inv
  refine ⟨bxi_userX B hk hCs E.inv G, stLay_wrU E.lay b w, E.ntw, by rw [ecur]; exact E.cs, ?_, ?_, ?_,
    by rw [L.ksb_wr]; exact E.ksv, E.vin, fun h => by rw [hlk X b w hb hba]; exact E.vlk h,
    fun h => ⟨(E.vfar h).1.ksb (L.ksb_wr _ _ _), (E.vfar h).2⟩, ?_⟩
  · intro t ht h1
    have es : L.mem (L.wr X b w) (scA t) = L.mem X (scA t) :=
      wr_nu hba hb w (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h1 ⊢
    have hsc := (hXI.2.2.bound t ht h1).1
    have ec : L.mem (L.wr X b w) (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      wr_nu hba hb w (nu_scw hX (scs_heap hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr X b w) (affA t) = L.mem X (affA t) :=
      wr_nu hba hb w (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact E.aff t ht h1
  · have e : L.mem (L.wr X b w) (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
      wr_nu hba hb w (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, L.cpu_wr, e]; exact E.curAff
  · have e : L.mem (L.wr X b w) (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
      wr_nu hba hb w (nu_scw hX (scs_heap hXI.2.2.cur) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, L.cpu_wr, e]; exact E.cscCore
  · intro n' hn hn0
    have eb : L.mem (L.wr X b w) (boundA (L.curW X)) = L.mem X (boundA (L.curW X)) :=
      wr_nu hba hb w (nu_tcb hX hcH (o := 3368#u64) (by simp) (by simp) (by simp))
    rw [ecur, eb] at hn
    have hF := E.nfar n' hn hn0
    exact ⟨hF.1.ksb (L.ksb_wr _ _ _), hF.2⟩

variable {m : U64 → U64}

/-- **`VexitPEnt` across a user-word write** at any layout (`vexitPEnt_wr` without `nv`: `pusr` by `.ksb`, `vfit`
state-free). -/
theorem vexitPEnt_wrV {X : S} (B : UserLayX L K.toKLayout)
    (E : VexitEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk v n X)
    (P : VexitPEnt K st K.heap.tcbs Cs K.heap Sg K.heap.scs K.heap.scBits m v X)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (w : U64) :
    VexitPEnt K st K.heap.tcbs Cs K.heap Sg K.heap.scs K.heap.scBits m v (L.wr X b w) := by
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  have ht' : TcbAddr (L.curW X) := h0.tcbs _ h0.curT
  have ecur : L.curW (L.wr X b w) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact wr_nu hba hb w ⟨nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]),
      E.lay.nu_node (by rw [curth_val]; omega)⟩
  have tw : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      L.mem (L.wr X b w) (core.num.U64.wrapping_add (L.curW X) o) =
        L.mem X (core.num.U64.wrapping_add (L.curW X) o) := fun o h1 h2 =>
    wr_nu hba hb w ⟨field_aligned ht' h1 h2, fun hu => B.userObj hu hcH (fun z e => by cases e)
      (by unfold InW; rw [field_val ht' h1]; simp only [HKind.bits]; omega)⟩
  refine ⟨fun x hx hxa => (P.usr x hx hxa).ksb (L.ksb_wr _ _ _), fun h => (P.pusr h).ksb (L.ksb_wr _ _ _), ?_,
    P.vfit, ?_⟩
  · have e1 : L.mem (L.wr X b w) (ibA (L.curW X)) = L.mem X (ibA (L.curW X)) :=
      tw 3512#u64 (by simp) (by simp)
    have e2 : L.mem (L.wr X b w) (sbA (L.curW X)) = L.mem X (sbA (L.curW X)) := by
      rw [sbA_field ht']; exact tw 64#u64 (by simp) (by simp)
    have e3 : L.mem (L.wr X b w) (core.num.U64.wrapping_add (sbA (L.curW X)) 8#u64) =
        L.mem X (core.num.U64.wrapping_add (sbA (L.curW X)) 8#u64) := by
      rw [sbA8_field ht']; exact tw 72#u64 (by simp) (by simp)
    rw [ecur, lookup_buf_agree e1 e2 e3]
    exact P.buf
  · rw [ecur, P.aff0]
    exact (tw 3520#u64 (by simp) (by simp)).symm

end fr

/-! ## The VT-x bundle and the VM-exit record without [S] -/

section bun
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The VM-exit index's sets are the layout's** (index convention: `BunIx` without its P3 bundle field `ac`; a
choice of index, untagged as `BunIx`'s fields). -/
structure VxIx (i : VxArg S) (K : KLayoutV) : Prop where
  hKH : K.heap = i.H
  hT : i.T = i.H.tcbs
  hRp : i.Rp = i.H.replies
  hScs : i.Scs = i.H.scs
  hNt : i.Nt = i.H.ntfns
  hZ : i.Z = i.H.scBits
  hCs : i.Cs = {c : U64 | c.val < K.ncores}

variable {st} in
/-- **vx's `eu` at any layout** from `UserLayX`, the index convention and `kd` [P] (`vxEu_of` without `nv` and
without a P3 bundle). -/
theorem vxEu_ofV {i : VxArg S} {K : KLayoutV} {m : U64 → U64} (B : UserLayX L K.toKLayout) (ix : VxIx i K)
    (kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s) : VxEuX st i K m := by
  have hCs : ∀ c ∈ i.Cs, c.val < 64 := by
    intro c hc
    rw [ix.hCs] at hc
    exact Nat.lt_of_lt_of_le hc B.nc
  have hlk : ∀ s b w, b ∈ K.user → Aligned b → i.lk (L.wr s b w) = i.lk s :=
    fun s b w hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => kd s) s b w trivial
      (mem_userV.2 (Or.inl hb)) hba
  have hKH := ix.hKH
  have hT := ix.hT
  have hRp := ix.hRp
  have hScs := ix.hScs
  have hNt := ix.hNt
  have hZ := ix.hZ
  intro s b w hP hb hba
  have hE1 : VexitEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.v i.n s := hP.1
  have hP1 : VexitPEnt K st i.T i.Cs i.H i.Sg i.Scs i.Z m i.v s := hP.2
  show VexitEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.v i.n (L.wr s b w) ∧
    VexitPEnt K st i.T i.Cs i.H i.Sg i.Scs i.Z m i.v (L.wr s b w)
  rw [hT, hRp, hScs, hNt, hZ, ← hKH] at hE1
  rw [hT, hScs, hZ, ← hKH] at hP1
  rw [hT, hRp, hScs, hNt, hZ, ← hKH]
  exact ⟨vexitEnt_wrV B hCs hlk hE1 hb hba w, vexitPEnt_wrV B hE1 hP1 hb hba w⟩

/-- **The VT-x bundle** [S] (module docstring and table): the layout facts of a VM epoch. Every native layout has it
(`vtxBundle_of_jvm`); at a guest-running state it is scope (P3 reaches no such state). -/
structure VtxBundle (L : LawfulStore st) (K : KLayoutP) : Prop where
  /-- P3's region facts of the base layout (`SlJAtZ.okRU`). -/
  ok : RegionOK K.toKLayout
  /-- P3's user facts of the base layout (`SlJAtZ.okRU`). -/
  uok : E2E.UserOK K.toKLayout
  /-- The user-word layout facts (`UserLayX.ofSlJAt`). -/
  ul : UserLayX L K.toKLayout
  /-- `VcpuHeap`: the layout's VCPUs are `other 15` heap objects (`JVm.heap`; `VFacts.heap`). -/
  vh : VcpuHeap K.toKLayoutV
  /-- No VCPU word lies in a CNode slot (`slot_noVcpu`, from `VcpuSpec`). -/
  vsl : ∀ p ∈ K.slots, ∀ b, InW p 32 b → ¬ ∃ v, InVcpu K.toKLayoutV v b
  /-- `UserObj`: no user word lies in a VCPU (`VFacts.user`). -/
  vu : UserObj K.toKLayoutV

variable {st}
variable {K : KLayoutP}

/-- **`VtxBundle` with the PTE convention gives VX1's `VtxLayP`.** -/
theorem VtxBundle.okP (h : VtxBundle st L K) {m : U64 → U64} (he : K.ptes = ptesR K m) :
    RegionOKP K ∧ UserOKP K :=
  ⟨regionOKP_R (regionOKV_of h.ok h.ul.lp h.vh h.vsl) he, userOKP_R ⟨h.uok⟩ he⟩

theorem VtxBundle.vcpuNU (h : VtxBundle st L K) : VcpuNU K.toKLayoutV :=
  fun v b hv hu => h.vu b hu ⟨v, hv⟩

/-- **The existing VT-x layout cluster at a P3 bundle state gives `VtxBundle`.** -/
theorem vtxBundle_of_vfacts {s : S} (B : SlJAt (L := L) K.toKLayout s) (vf : VFacts L K.toKLayoutV) :
    VtxBundle st L K := by
  have hok : RegionOK K.toKLayout ∧ E2E.UserOK K.toKLayout := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B'⟩ := B
    exact B'.okRU
  exact ⟨hok.1, hok.2, UserLayX.ofSlJAt B, vf.heap,
    fun p hp b hb => slot_noVcpu B vf.spec vf.heap hp hb, vf.user⟩

/-- **`JVmL` [J] at a P3 bundle state gives `VtxBundle`.** -/
theorem vtxBundle_of_jvm {s : S} (B : SlJAt (L := L) K.toKLayout s) (hJ : JVmL L K.toKLayoutV) :
    VtxBundle st L K :=
  vtxBundle_of_vfacts B (VFacts.ofJVm hJ B)

/-- **Every native layout at a P3 bundle state has `VtxBundle`** (satisfiability at P3 scope). -/
theorem vtxBundle_of_empty {s : S} (B : SlJAt (L := L) K.toKLayout s) (nv : K.vcpus = ∅) : VtxBundle st L K :=
  vtxBundle_of_jvm B (jvmL_empty nv)

variable (st)

/-- **The VM-exit record without [S]**: `hv0`, the index convention, `kd` [P]. -/
structure VxPremV2 (i : VxArg S) (K : KLayoutV) : Prop where
  /-- The index is a real exit (fl4-sync's `vm_local` runs the body only for a bound VCPU, `l.vcpu ≠ 0`). -/
  hv0 : i.v ≠ 0#u64
  /-- Index convention. -/
  ix : VxIx i K
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

variable {st}

/-- **`VxPremV` from `VxPremV2` and the epoch's bundle.** -/
theorem VxPremV2.toV {i : VxArg S} {m : U64 → U64} (h : VxPremV2 st i K.toKLayoutV) (E : VtxBundle st L K) :
    VxPremV st i K.toKLayoutV m :=
  ⟨h.hv0, E.vcpuNU, vxEu_ofV E.ul h.ix h.kd, h.kd⟩

end bun

/-! ## Executions whose VM epochs carry the bundle -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **A step of FL4 with native and VM epochs, VM exits carrying `VtxBundle`**: `Fl4StepVX` with the VM case's
`VtxLayP` [S] replaced by the PTE convention and `VtxBundle` [S]. -/
structure Fl4StepVX2 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s : Cfg U64 U64 U64 U64) (K : KLayoutP) (Ch : S → Prop) (c : U64)
    (s' : Cfg U64 U64 U64 U64) (K' : KLayoutP) (Ch' : S → Prop) : Prop where
  /-- [P] an armed program is pure glue. -/
  arm : ∀ p, s'.ph c = .arm p → PureGlue p
  /-- [P] the glue's start fact. -/
  start : ∀ p0 k W, s.ph c = .loc p0 (.start k) W → ∀ (hK : RegionOKP K) (hU : UserOKP K),
    ∃ i, SF Ch K s.mem hK hU c (fun l => s.lk l = some c) k i
  /-- The serial exit: native ([P] `SerExitW`, convention) or VM (convention `vcpus ≠ ∅`, `ptes = ptesR`;
  [S] `VtxBundle`). -/
  ser : SerStep s c → (SerExitW P K'.toKLayoutV Ch' ∧ K'.vcpus = ∅ ∧ K'.ptes = ptesR K' s'.mem) ∨
    (K'.vcpus ≠ ∅ ∧ K'.ptes = ptesR K' s'.mem ∧ VtxBundle st L K')
  /-- [P] the exit ghost with rule 8. -/
  serG : SerStep s c → MapsP K' s'
  /-- Layout and chain change only at serial steps. -/
  keep : ¬ SerStep s c → K' = K ∧ Ch' = Ch

/-- **An execution of FL4 whose VM epochs carry `VtxBundle`.** -/
inductive ExecVX2 (LP : PathsP ι)
    (SF : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ι → Prop)
    (P : LocPlat st arI AR MR) (s0 : Cfg U64 U64 U64 U64) (K0 : KLayoutP) (Ch0 : S → Prop) :
    Cfg U64 U64 U64 U64 → KLayoutP → (S → Prop) → Prop
  | refl : ExecVX2 LP SF P s0 K0 Ch0 s0 K0 Ch0
  | step {s s' : Cfg U64 U64 U64 U64} {K K' : KLayoutP} {Ch Ch' : S → Prop} {c : U64} :
      ExecVX2 LP SF P s0 K0 Ch0 s K Ch → Step s c s' → Fl4StepVX2 LP SF P s K Ch c s' K' Ch' →
      ExecVX2 LP SF P s0 K0 Ch0 s' K' Ch'
  | hw {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {Ch : S → Prop} {v a x : U64} :
      ExecVX2 LP SF P s0 K0 Ch0 s K Ch → HwStepP K s v a x → ExecVX2 LP SF P s0 K0 Ch0 (hwCfg s a x) K Ch

end exec

/-! ## The VM-exit start fact and the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The VM-exit slot's start fact without the record's [S]** [S] (module docstring): `VxPremV2`, and the glue's
start state with the path's `Pre` and `QPs` (the [S] entry), its core, locks and memory link ([P], as `GlueAt`),
and the armed program the cut of the slot's body there, for the record the epoch's bundle gives. -/
def VxStartV2 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : VxArg S) : Prop :=
  ∃ q0, (∃ h : VxPremV2 st j K.toKLayoutV, ∃ (σ : S) (a : A),
      (VxPre st j K.toKLayoutV m σ ∧ QPs K st σ) ∧ L.cpu σ = c ∧ j.lk σ = hs ∧
      (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle st L K,
        q0 = ((vxSlotV st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toV (m := m) E)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **Every VM-exit start is in a VM epoch** (the exiting VCPU is the layout's). -/
theorem vxStartV2_ne {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VxArg S} (h : VxStartV2 st ar hA hm K μ hK hU c hs q j) :
    K.vcpus ≠ ∅ := fun e => by
  obtain ⟨q0, ⟨hp, σ, a, he, -⟩, -⟩ := h
  have hv := (he.1.1.vin hp.hv0).1
  rw [e] at hv
  exact hv

/-- **`VxStartV2` and the epoch's bundle give VX1's `VxStartV`.** -/
theorem vxStartV_of_V2 {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VxArg S} (E : VtxBundle st L K) (h : VxStartV2 st ar hA hm K μ hK hU c hs q j) :
    VxStartV st ar hA hm K μ hK hU c hs q j := by
  obtain ⟨q0, ⟨hp, σ, a, he, hc, hl, hμ, hq⟩, rfl⟩ := h
  exact ⟨q0, ⟨hp.toV E, σ, a, he, hc, hl, hμ, hq E⟩, rfl⟩

variable (st ar hA hm)

/-- **The start facts with the VM-exit slot at `VxStartV2`.** -/
def StartVX2 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : ιN ⊕ VxArg S → Prop
  | .inl i => K.vcpus = ∅ ∧ SFN Ch K m hK hU c hs q i
  | .inr j => VxStartV2 st ar hA hm K m hK hU c hs q j

end top

end
end Fl4Proofs.P2.E2EP
