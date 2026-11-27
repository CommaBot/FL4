/-
P2 (line iolay, gen 1): **`serializable_fl4_localW9`: the I/O port and VM-fault / VM-ReplyRecv starts at P3 scope
with their layout facts, CSpace walk, `run` and io's `iw` derived** (new definitions only, on top of famw's W8; the
one statement change is the in-place narrowing of `IoLay.ks`, below).

## 0. The statement change (line iolay)

`IoLay.ks` (P2/AccessIoOwn.lean) asked every word of the 13568-byte kernel-state block to lie in no region, which is
false at every P3 layout (famw's finding, now `SlJAt.not_ioLayWide` in W8: the IRQ node's one-slot CNodes sit at
`ksb + 1248 + 32 i`). It is narrowed in place, as line slj narrowed `RegionOKX.ks`, to the aligned words of the first
256 bytes (the paths read only `CUR_DOMAIN` 8, `DOMAIN_TIME` 16, `KERNEL_ROOT` 48 there). Forced follow-ons, each a
weakening: `IoPre.ksw` / `VmBase.ksw` take `o.val < 256` (was `< 13568`), `VmDF.ksw` (a structure field) likewise;
every user passes `CUR_DOMAIN` / `DOMAIN_TIME` / `KERNEL_ROOT`. W8's `SlJAt.not_ioLay`, `IoEntJ7.not`,
`VmFEntJ7.not`, `VmREntJ7.not` (false after the narrowing) are replaced there by `not_ioLayWide` about the old field.

## 1. Layout facts at bundle states

**`SlJAt.ioLay`**: the narrowed `IoLay K` at every bundle state (nodes `slj_region_node`; TCB / SC words
`LayP.region_tcb` / `region_sc`; slot words `LayP.slj_region_slot`; TCB slots `RegionOKX.tslot`; kernel globals
`RegionOKX.ks`; `ksb` alignment / fit from the node placement; user words in no region by `RegionOKX.kern` and off
the block by `SlJAtZ.ksU`). **`SlJAt.vmLay`**: `VmLay K` (endpoint / reply words `LayP.slj_region_obj`).

## 2. The CSpace walk at bundle states

**`SlJAtZ.ioWalk`**: `IoPre.walk` at every bundle state (P3's `JAtZ.cnOff` argument, with `C p r := th p = cnode r`,
plus the indexed slots are slots of `Zx.th`, i.e. of `K.slots`). **`SlJAtZ.ioFin`**: `IoPre.fin` (the slot a lookup
returns is an indexed slot of the closure, `lookup_slot_in` from m67's `rab_loop_slot`).

## 3. io's `iw` (`SlJAt.ioPre_wr`)

`IoPre` is kept by an aligned user-word write at a bundle state, for `Cs` below 64 cores: the `VmBase` part by
slhuf's `SlJAt.vmBase_wr` (with `VmLay` from §1), the walk / lookup by `lookup_slot_back` (slot words are `NU`,
`slot_nu`), `OutsideObjs` by `OutsideObjs.ksb`. **`ioPre_wr_hIw`** states it in the exact form of hpzg's
`hufQL_of` premise `hIw` (P2/InvHuf.lean on par/hpzg4; that lemma is not on this base). For io's record,
**`IoPremW9`** = `IoPremW3` minus `iw`, with `bun` sharpened to a bundle state whose core ghost is the index's `Cs`
(`bunS`, no premise: the start state, `BunIx.ac`), which gives `Cs` below 64 (`JKern.csLt`); `IoPremW9.toW3`.

## 4. `run` from the chain (line nscope's `kernel_entry_nativeScopeU29`)

Clause 7's bundle (`SlJAt`) does not carry `SInvX`, but the chain does: `ChainOf` fixes `Ch` to the `JReachSt` chain
from the exit, every `JReachSt` state is `JReachU17` (`JReachSt.reach`), and at every `JReachU17` state
`kernel_entry_nativeScopeU29` gives the current thread's state word `RESTART ∨ RUNNING` under `ct ≠ idle`.
**`chain_run`**: on the chain, `run` follows from **`hct`** [P] (every spec state related to the start state has a
non-idle current thread: the I/O port / VM-fault / ReplyRecv entries come from a user thread; the same input
`σ.curThread ≠ σ.idleThread` that `loc_chain_all` clauses 4 / 9 / 10 take) and P3's platform premise
`MRKeepIoapic` [P] (`kernel_entry_reachU29`'s, not in `LocPlat`). To see the chain at a start, **`execV_of_WC`**
is `execV_of_W` whose start callback gets `ChainOf` (from `SerExitW.chainOf`) instead of clause 7 alone.

## 5. Entry facts, satisfiability, the top

* io **`IoEntJ9`** = `BunIx` + `hct` [P] (`lay`, `walk`, `fin`, `run` derived; `IoEntJ9.toJ7`).
* vmF **`VmFEntJ9`** = `VmFEntJ7` − `br` (`VmLay` and `run`) + `hct` [P]; vmR **`VmREntJ9`** likewise.
  `BunIxU` (Ω := OmegaU) is not wired for them: their `BunIx`-derived `VmBase` fields (`entryInv`, `kb`, `nc`,
  heap typing) have no `BunIxU` counterparts yet, and the `AsidOff`-carrying fields (`hyp`, `mid`) stay [J] either way.
* Satisfiability: **`ioEntJ7_sat`** / **`ioEntJ9_sat`**: at every chain state with `hct`, some index meets io's
  W7 / W9 entry facts; **`vmBaseR7_sat`**: `VmBaseR7` (the part of vmF / vmR's entry facts that W8 showed false)
  holds at every chain state with `hct`, so `VmFEntJ7` / `VmREntJ7` reduce to their remaining [J] / [P] fields.
* **`StartP3W9`**: `StartP3W8` with io / vmF / vmR at `IoPremW9`+`IoEntJ9`, `VmFEntJ9`, `VmREntJ9`;
  **`startAt_P3W9`**; **`serializable_fl4_localW9`** (premises of W8 + `hIoa`).

| slot | removed (vs W8's start facts) | added |
|---|---|---|
| io | record `iw` [J]; entry `run` [J], `lay` [J] (false before), `walk` [J], `fin` [J] | record `bunS` (start state); entry `hct` [P] |
| vmF | entry `br.run` [J], `br.lay` [J] (false before) | entry `hct` [P] |
| vmR | entry `br.run` [J], `br.lay` [J] (false before) | entry `hct` [P] |
| top | — | `hIoa : MRKeepIoapic` [P] (P3 platform) |

Premises still open in these slots: io record `kd` [P], `hQ` / `nv` (conventions); vmF `hyp` [J], `lk` [P], `hyt` [J],
`gl` [P]; vmR `mid` [J], `lk` / `nb` [P], `hNt` / `nbt` [J], `fd` (clause-10 input); `hct` [P] for all three.
-/
import Fl4Proofs.P2.E2EVFl4W8
import Fl4Proofs.P3.JNativeScope
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **The narrowed `IoLay` at a bundle state** (module docstring, item 1). -/
theorem SlJAtZ.ioLay (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : IoLay K := by
  have hP := B.layP
  have X := B.regionOKX
  have hk : L.ksb s = K.ksb := B.ksb
  have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := TInv.nodes B.j.blk _ B.j.kern.cpuCs
  have na := hN.align
  have nf := hN.fits
  simp only [LawfulStore.nodeBase] at na nf
  refine
  { node := fun c b hb => slj_region_node hb
    tcbw := fun t ht off h1 h2 => ?_
    slotw := fun p hp b hb => hP.slj_region_slot hp hb
    slot8 := fun p hp => ?_
    tslot := fun t ht i sl h hi => ?_
    scw := fun p z hp b hb => hP.region_sc hp hb
    ks := X.ks
    ksf := ?_
    user := fun b hb => ⟨?_, ?_⟩ }
  · have hv := hP.tcb_fld ht h2
    unfold fld at hv ⊢
    exact hP.region_tcb ht ⟨by omega, by omega⟩ (by omega)
  · obtain ⟨h32, q, k, hq, h1, h2, -, -⟩ := hP.slot p hp
    have hf := hP.heap.fits q k hq
    exact ⟨by omega, by omega⟩
  · rw [Fl4Proofs.P1.tcb_slot_val] at h
    obtain rfl := ok_inj_ff h
    obtain ⟨hs, hts, -⟩ := X.tslot t ht i hi
    exact ⟨hs, hts⟩
  · rw [hk] at na nf
    exact ⟨by omega, by omega⟩
  · by_contra hne
    exact X.kern b hne hb
  · have := B.ksU hb
    rw [hk] at this
    omega

/-- **`VmLay` at a bundle state** (module docstring, item 1). -/
theorem SlJAtZ.vmLay (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) : VmLay K where
  io := B.ioLay
  epw p hp b hb := B.layP.slj_region_obj hp (Or.inl rfl) (by simpa [HKind.bits] using hb)
  rpw p hp b hb := B.layP.slj_region_obj hp (Or.inr rfl) (by simpa [HKind.bits] using hb)

theorem SlJAt.ioLay (B : SlJAt (L := L) K s) : IoLay K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.ioLay

theorem SlJAt.vmLay (B : SlJAt (L := L) K s) : VmLay K := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.vmLay

end lay

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **`IoPre.walk` at a bundle state** (module docstring, item 2: `JAtZ.cnOff`'s closure). -/
theorem SlJAtZ.ioWalk (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∃ C : U64 → U64 → Prop, (∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) ∧
      WalkCl (st := st) s C ∧
      ∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
        OutsideObjs st (Heap.tcbs K.heap) Cx s (cnSlot p (y &&& m)) ∧
        OutsideObjs st (Heap.tcbs K.heap) Cx s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64) := by
  have J := B.j
  have et : sched.cur_thread st s = ok (L.curW s) := cur_thread_ok (L := L) s
  have htcb := J.curW_tcb et
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  have hroot0 : ∀ sl root, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_CTABLE = ok sl → obj.Slot.cap st sl s = ok root →
      ∀ p r gs g, root = .CNode p r gs g → Zx.th p = some (.cnode r.val) := by
    intro sl root hsl hroot
    obtain ⟨tcb, c, -, hc, -, hval⟩ := hR.ctable hV htcb
    have hsl' := tcb_slot_spec (L.curW s) layout.tcb.SLOT_CTABLE
    rw [hsl, WP.spec_ok] at hsl'
    rw [hsl', show (layout.tcb.SLOT_CTABLE.bv : BitVec 64) = 0#64 by simp [layout.tcb.SLOT_CTABLE],
      slot_cap_eq, hc] at hroot
    obtain rfl := ok_inj_ff hroot
    intro p r gs g e
    subst e; exact hval.1
  refine ⟨fun p r => Zx.th p = some (.cnode r.val),
    fun p r gs g e => hroot0 _ _ (tcb_slot_ctable (L.curW s)) e p r gs g rfl,
    fun p r m x p' r' gs' g' hC hm e => ?_, fun p r m x hC hm => ?_⟩
  · rw [cnSlot_eq, slot_cap_eq] at e
    exact (hV.cnode p r.val hC _ (andMask_lt_pow hm x) _ e).1
  · have hi := andMask_lt_pow hm x
    have hsS : slotOf p (x &&& m).val ∈ K.slots := by
      rw [B.slots]; exact ⟨p, _, Or.inl ⟨_, hC, hi⟩, rfl⟩
    rw [cnSlot_eq]
    exact ⟨hsS, (J.capSW hC hi (Or.inl rfl)).1, (J.capSW hC hi (Or.inr rfl)).1⟩

/-- **The slot a lookup returns is an indexed slot of a closed CNode set** (`rab_loop_slot`). -/
theorem lookup_slot_in {t cptr : U64} {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, obj.Slot.cap st t s = ok (.CNode p r gs g) → C p r) (hcl : WalkCl (st := st) s C)
    {x : cspace.Resolved} (h : cspace.lookup_slot st s t cptr = ok (.Ok x)) :
    ∃ p r m y, C p r ∧ cspace.mask r = ok m ∧ x.slot = cnSlot p (y &&& m) := by
  unfold cspace.lookup_slot at h
  rw [tcb_slot_ctable] at h; simp only [bind_ok] at h
  obtain ⟨root, er, h⟩ := bind_eq_ok h
  exact rab_loop_slot st C hcl 66 root _ 65#u64 x (by simp) (fun p r gs g e => hroot p r gs g (e ▸ er)) h

/-- **`IoPre.fin` at a bundle state** (module docstring, item 2). -/
theorem SlJAtZ.ioFin (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    ∀ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) →
      x.slot ∈ K.slots ∧ OutsideObjs st (Heap.tcbs K.heap) Cx s x.slot ∧
        OutsideObjs st (Heap.tcbs K.heap) Cx s (core.num.U64.wrapping_add x.slot 8#u64) := by
  intro x hx
  obtain ⟨C, hroot, hcl, hsl⟩ := B.ioWalk
  obtain ⟨p, r, m, y, hC, hm, e⟩ := lookup_slot_in hroot hcl hx
  rw [e]
  exact hsl p r m y hC hm

end walk

section wr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Cs Ω Sg Ac : Set U64}

/-- A slot's two cap words are `NU`. -/
theorem slot_nu (hP : LayP K) {p : U64} (hp : p ∈ K.slots) :
    NU K p ∧ NU K (core.num.U64.wrapping_add p 8#u64) := by
  obtain ⟨h32, q, k, hq, h1, h2, -, -⟩ := hP.slot p hp
  have hf := hP.heap.fits q k hq
  have hv : (core.num.U64.wrapping_add p 8#u64).val = p.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine ⟨⟨by unfold Aligned; omega, fun hu => hP.userSlot p hu p hp ⟨le_refl _, by omega⟩⟩,
    ⟨by unfold Aligned; rw [hv]; omega, fun hu => hP.userSlot _ hu p hp ⟨by rw [hv]; omega, by rw [hv]; omega⟩⟩⟩

/-- A slot's cap is kept by a user-word write at a bundle state. -/
theorem SlJAt.cap_wr {s : S} (B : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    {x : U64} (hx : x ∈ K.slots) : obj.Slot.cap st x (L.wr s b v) = obj.Slot.cap st x s := by
  obtain ⟨n0, n8⟩ := slot_nu B.layP hx
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, wr_nu hba hb v n0, wr_nu hba hb v n8]

/-- **io's `iw`: `IoPre` is kept by an aligned user-word write at a bundle state** (module docstring, item 3;
canonical sets, `Cs` below 64 cores). -/
theorem SlJAt.ioPre_wr {s : S} (B : SlJAt (L := L) K s) (hCs : ∀ c ∈ Cs, c.val < 64)
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v) := by
  have VB : VmBase st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s :=
    { bxi := P.bxi, csc := P.csc, hcsc := P.hcsc, run := P.run, lay := B.vmLay, kb := P.kb, nc := P.nc, hT := P.hT,
      hSc := P.hSc, curAff := P.curAff, cscCore := P.cscCore, affSc := P.affSc, tmc := P.tmc }
  have W := B.vmBase_wr hCs VB hb hba v
  have ecur := B.curW_wr hb hba v
  have hX := B.regionOKX
  have ek : L.ksb (L.wr s b v) = L.ksb s := L.ksb_wr _ _ _
  have hcH : K.heap (L.curW s) = some .tcb := P.hT _ P.cT
  have hcS : L.curW s ∈ K.slots :=
    (P.lay.tslot _ hcH _ _ (tcb_slot_ctable (L.curW s)) (by simp [layout.tcb.SLOT_CTABLE])).1
  obtain ⟨C, hroot, hcl, hsl⟩ := P.walk
  have ecapR : L.mem (L.wr s b v) (regA (L.curW s) layout.reg.CAP) = L.mem s (regA (L.curW s) layout.reg.CAP) := by
    have hr := (P.reg (Locks := fun _ _ => True) (r := layout.reg.CAP) (by simp [layout.reg.CAP])).1
    exact wr_nu hba hb v ⟨hr.1, hr.2.1⟩
  exact
  { bxi := W.bxi, csc := W.csc, hcsc := W.hcsc, run := W.run, lay := P.lay, kb := W.kb, nc := W.nc, hT := W.hT,
    hSc := W.hSc, curAff := W.curAff, cscCore := W.cscCore, affSc := W.affSc, tmc := W.tmc
    walk := ⟨C, fun p r gs g h => hroot p r gs g (by rw [ecur, B.cap_wr hb hba v hcS] at h; exact h),
      fun p r m y p' r' gs' g' hC hm h =>
        hcl p r m y p' r' gs' g' hC hm (by rw [B.cap_wr hb hba v (hsl p r m y hC hm).1] at h; exact h),
      fun p r m y hC hm => ⟨(hsl p r m y hC hm).1, (hsl p r m y hC hm).2.1.ksb ek, (hsl p r m y hC hm).2.2.ksb ek⟩⟩
    fin := fun x hx => by
      rw [ecur, ecapR] at hx
      have hx' := lookup_slot_back (tcb_slot_ctable (L.curW s)) (B.cap_wr hb hba v hcS)
        (fun p r m y hC hm => B.cap_wr hb hba v (hsl p r m y hC hm).1) hcl hroot hx
      obtain ⟨h1, h2, h3⟩ := P.fin x hx'
      exact ⟨h1, h2.ksb ek, h3.ksb ek⟩ }

/-- **`SlJAt.ioPre_wr` in the form of hpzg's `hufQL_of` premise `hIw`** (P2/InvHuf.lean, par/hpzg4). -/
theorem ioPre_wr_hIw (hCs : ∀ c ∈ Cs, c.val < 64) :
    ∀ (K : KLayout) (s : S) (b v : U64), SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v) :=
  fun _ _ _ v hJ P hb hba => hJ.ioPre_wr hCs P hb hba v

end wr

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot InW InNode)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## `run` from the chain -/

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`run` at a chain state** (module docstring, item 4): from `hct` [P] and line nscope's
`kernel_entry_nativeScopeU29` at the chain state's `JReachU17`. -/
theorem chain_run (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {K : OwnMap.KLayout} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K Ch) {σ : S} (hσ : Ch σ)
    (hct : ∀ (a : A3) (τ : Fl4Spec.State Unit), Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR σ a τ →
      τ.curThread ≠ τ.idleThread) :
    L.mem σ (stA (L.curW σ)) = sched.TS_RESTART ∨ L.mem σ (stA (L.curW σ)) = sched.TS_RUNNING := by
  obtain ⟨Z, H, Cx, nc, -, -, hCh, -, -⟩ := hC
  subst hCh
  obtain ⟨a, τ, hR⟩ := hσ
  have hJ := hR.reach
  obtain ⟨-, -, -, -, -, -, -, -, -, hrun, -⟩ := Fl4Proofs.P3.SInvR.G5.kernel_entry_nativeScopeU29 arI AR MR P.ari
    P.tot P.nd P.mach P.kd P.io hIoa P.pa P.ia P.t P.max P.tu P.ref P.pi P.sx P.dr hJ
  exact hrun (hct a τ hJ)

theorem ChainOf.bun {σe : S} {K : OwnMap.KLayout} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K Ch) :
    ∀ σ, Ch σ → SlJAt (L := L) K σ := by
  obtain ⟨Z, H, Cx, nc, -, -, -, hCL, -⟩ := hC
  exact hCL.bun

end run

/-! ## Entry facts and records -/

section ent
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **The start's spec states have a non-idle current thread** [P] (module docstring, item 4: the I/O port /
VM-fault / ReplyRecv entries come from a user thread; `loc_chain_all` clauses 4 / 9 / 10 take the same input). -/
def NonIdle {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (s : S) : Prop :=
  ∀ (a : A3) (τ : Fl4Spec.State Unit), Fl4Proofs.P3.SInvR.G5.JReachU17 (L := L) arI AR MR s a τ →
    τ.curThread ≠ τ.idleThread

/-- **io's start entry facts** (module docstring, item 5): `lay`, `walk`, `fin`, `run` derived. -/
structure IoEntJ9 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : IoArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention (`BunIx`, a choice of index: `bunIx_of`). -/
  ix : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
    K.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s

/-- **W7's io entry facts from the bundle and `run`.** -/
theorem IoEntJ7.of_bun {i : IoArg S} {K : KLayoutV} {s : S}
    (ix : BunIx (L := L) K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    IoEntJ7 st i K s := by
  have hJ := ix.ac.slJAt
  obtain ⟨A', arI, AR, Zx, Lst, D, a', σ, B⟩ := ix.ac
  exact ⟨ix, hrun, PathObl.SlJAt.ioLay hJ, B.ioWalk, B.ioFin⟩

theorem IoEntJ9.toJ7 {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : IoArg S} {K : KLayoutV} {s : S} (E : IoEntJ9 st arI AR MR i K s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    IoEntJ7 st i K s :=
  IoEntJ7.of_bun st E.ix hrun

/-- **`VmBaseR7` from the bundle and `run`** (its `VmLay` was false before the narrowing). -/
theorem VmBaseR7.of_bun {Kl : OwnMap.KLayout} {s : S} (hJ : SlJAt (L := L) Kl s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    VmBaseR7 st Kl s :=
  ⟨hrun, PathObl.SlJAt.vmLay hJ⟩

/-- **vmF's start entry facts** (module docstring, item 5): `VmFEntJ7` minus `br`, plus `hct`. -/
structure VmFEntJ9 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmFArg S) (K : KLayoutV) (s : S) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] as `VmFPre.hyp`. -/
  hyp : ∀ a s1 a1, sched.update_timestamp st ar s a = ok (s1, a1) →
    VmFootHyps (L := L) i.T i.Cs i.Ω i.U i.Sg i.Rp i.Scs i.Nt i.Ac i.H i.Z s1
  /-- [P] as `VmFPre.lk`. -/
  lk : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → i.Locks s ptr ∧ i.Locks s r
  /-- [J] as `VmFPre.hyt`. -/
  hyt : ∀ a s1 a1 ptr badge dest r, sched.update_timestamp st ar s a = ok (s1, a1) →
    FaultChecks st s1 (L.curW s1) ptr badge dest r → L.mem s (yieldA dest) = 0#u64
  /-- [P] -/
  gl : VmGlue st ar i.Locks s

theorem VmFEntJ9.toJ7 {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmFArg S} {K : KLayoutV} {s : S}
    (E : VmFEntJ9 st ar arI AR MR i K s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    VmFEntJ7 st ar i K s :=
  ⟨E.nv, E.ix, VmBaseR7.of_bun st E.ix.ac.slJAt hrun, E.hyp, E.lk, E.hyt, E.gl⟩

/-- **vmR's start entry facts** (module docstring, item 5): `VmREntJ7` minus `br`, plus `hct`. -/
structure VmREntJ9 {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop)
    (MR : A3 → Fl4Spec.MachineState → Prop) (i : VmRArg S) (Kl : OwnMap.KLayout) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) Kl Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns
    Kl.heap.scBits i.Ac s
  /-- [P] (`NonIdle`). -/
  hct : NonIdle st arI AR MR s
  /-- [J] as `VmRPre.mid`. -/
  mid : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    BXI st Kl.heap.tcbs i.Cs i.Ω Kl.heap i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits i.Ac s2 ∧
      AsidOff (L := L) i.Ω i.Sg s2 ∧
      ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) i.rptr i.ep u usc →
        RRPl (L := L) Kl.heap.tcbs i.Cs i.Ω i.Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits s2
          (L.curW s) i.rptr i.ep u usc ∧ L.mem s2 (yieldA u) = 0#u64
  /-- [P] -/
  lk : i.Locks s i.rptr ∧ i.Locks s i.ep
  /-- [P] -/
  nb : L.mem s (rPrevA i.rptr) = 0#u64 ∧ L.mem s (rNextA i.rptr) = 0#u64
  /-- [J] -/
  hNt : ∀ p ∈ Kl.heap.ntfns, Kl.heap p = some .ntfn ∧ p.val % 64 = 0 ∧ p.val + 64 ≤ 2 ^ 64 ∧
    ∀ b, InW p 64 b → region Kl b = .ntfn p
  /-- [J] -/
  nbt : L.mem s (boundA (L.curW s)) ≠ 0#u64 → L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s
  /-- `loc_chain_all` clause 10's fl4-sync input `hfd`. -/
  fd : VmFoundC st i.rptr i.ep s

theorem VmREntJ9.toJ7 {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmRArg S} {Kl : OwnMap.KLayout} {s : S}
    (E : VmREntJ9 st ar arI AR MR i Kl s)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING) :
    VmREntJ7 st ar i Kl s :=
  ⟨E.ix, VmBaseR7.of_bun st E.ix.ac.slJAt hrun, E.mid, E.lk, E.nb, E.hNt, E.nbt, E.fd⟩

/-- **io's premises, `iw` derived** (module docstring, item 3): `IoPremW3` minus `iw`, `bun` at the index's
`Cs` / `Ac`. -/
structure IoPremW9 (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (as `ioSlotP3W`). -/
  nv : K.vcpus = ∅
  /-- Index convention: the index's `Q` is stpost's `IoQ`. -/
  hQ : i.Q = fun K' m' s => IoQ st i.Cs i.Ω i.Sg i.Ac K'.toKLayout m' s
  /-- [P] as `IoPremW2B.kd`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.Locks s
  /-- Some bundle state of the layout with the index's core / active-SC sets as its ghosts (no premise: the start
  state, `BunIx.ac`). -/
  bunS : ∃ σ : S, SlJAtS (L := L) K.toKLayout i.Cs i.Ac σ

theorem IoPremW9.hCs {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (h : IoPremW9 st i K m) :
    ∀ c ∈ i.Cs, c.val < 64 := by
  obtain ⟨σ, A', arI, AR, Zx, Lst, D, a', τ, B⟩ := h.bunS
  exact fun c hc => B.j.kern.csLt c hc

/-- **`IoPremW3` from `IoPremW9`**: `iw` by `SlJAt.ioPre_wr`. -/
theorem IoPremW9.toW3 {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (h : IoPremW9 st i K m) : IoPremW3 st i K m :=
  ⟨h.nv, h.hQ, fun _ _ v hJ P hb hba => PathObl.SlJAt.ioPre_wr hJ (h.hCs st) P hb hba v, h.kd,
    ⟨h.bunS.choose, h.bunS.choose_spec.slJAt⟩⟩

end ent

/-! ## Satisfiability -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **io's W9 entry facts are satisfiable at every bundle state with a non-idle current thread.** -/
theorem ioEntJ9_sat {K : KLayoutV} {s : S} (h : SlJAt (L := L) K.toKLayout s) (hct : NonIdle st arI AR MR s) :
    ∃ Ac : Set U64, ∀ i : IoArg S, i.Cs = {c : U64 | c.val < K.ncores} → i.Ω = K.heap.omega →
      i.Sg = K.heap.frame → i.Ac = Ac → IoEntJ9 st arI AR MR i K s := by
  obtain ⟨Ac, BI⟩ := bunIx_of h
  refine ⟨Ac, fun i e1 e2 e3 e4 => ⟨?_, hct⟩⟩
  rw [e1, e2, e3, e4]
  exact BI

/-- **W7's io entry facts (formerly unsatisfiable) hold at every chain state with a non-idle current thread.** -/
theorem ioEntJ7_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S} {K : KLayoutV}
    {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe K.toKLayout Ch) {s : S} (hs : Ch s)
    (hct : NonIdle st arI AR MR s) :
    ∃ Ac : Set U64, ∀ i : IoArg S, i.Cs = {c : U64 | c.val < K.ncores} → i.Ω = K.heap.omega →
      i.Sg = K.heap.frame → i.Ac = Ac → IoEntJ7 st i K s := by
  obtain ⟨Ac, hE⟩ := ioEntJ9_sat st (ChainOf.bun hC s hs) hct
  exact ⟨Ac, fun i e1 e2 e3 e4 => (hE i e1 e2 e3 e4).toJ7 st (chain_run P hIoa hC hs hct)⟩

/-- **`VmBaseR7` (vmF / vmR's formerly false entry part) holds at every chain state with a non-idle current
thread**, at the chain's layout. -/
theorem vmBaseR7_sat (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {σe : S}
    {Kl : OwnMap.KLayout} {Ch : S → Prop} (hC : ChainOf (L := L) arI AR MR σe Kl Ch) {s : S} (hs : Ch s)
    (hct : NonIdle st arI AR MR s) : VmBaseR7 st Kl s :=
  VmBaseR7.of_bun st (ChainOf.bun hC s hs) (chain_run P hIoa hC hs hct)

end sat

/-! ## Executions whose starts see the chain -/

section exec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {ι : Type}

/-- **`execV_of_W` with the start callback given the current chain** (`ChainOf`, module docstring item 4). -/
theorem execV_of_WC {LP : PathsV ι}
    {SF : (S → Prop) → ∀ K : KLayoutV, (U64 → U64) → RegionOKV K → UserOKV K → U64 → (U64 → Prop) → SP → ι → Prop}
    (hSF : ∀ (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) → SF Ch K m hK hU c hs q i →
        StartAt (LP i K m hK hU) c hs m q)
    {P : LocPlat st arI AR MR} {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} {Ch0 Ch : S → Prop}
    (hB : SerExitW P K0 Ch0) (h : ExecW LP SF P s0 K0 Ch0 s K Ch) :
    ExecV LP s0 K0 s K ∧ SerExitW P K Ch := by
  induction h with
  | refl => exact ⟨.refl, hB⟩
  | @step s1 s1' K1 K1' Ch1 Ch1' c1 _ hS g ih =>
    obtain ⟨hE, hX⟩ := ih
    refine ⟨.step hE hS ⟨g.arm, fun p0 k W hph hK hU => ?_, fun hs => ?_, fun hn => (g.keep hn).1⟩, ?_⟩
    · obtain ⟨i, hi⟩ := g.start p0 k W hph hK hU
      exact ⟨i, hSF _ _ _ _ _ _ _ _ i hX.chainOf hi⟩
    · have hok := serExitW_ok (g.serX hs) (g.serV hs)
      exact ⟨hok.1, hok.2, (g.serG hs).maps⟩
    · by_cases hs : SerStep s1 c1
      · exact g.serX hs
      · obtain ⟨e1, e2⟩ := g.keep hs
        rw [e1, e2]; exact hX
  | hw _ hH ih => exact ⟨.hw ih.1 hH, ih.2⟩

end exec

/-! ## The start fact and the top -/

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact of `fl4LocP3W6`, io / vmF / vmR at their W9 entry facts** (module docstring, item 5). -/
def StartP3W9 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ h : VmFPrem st ar j K m, GlueAt ((vmFSlot st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmFEntJ9 st ar arI AR MR j K σ) c hs m q
  | .vmR j => ∃ h : VmRPremP3 st ar j K m, GlueAt ((vmRSlotP3 st ar hA hm).liftAt j K m hK hU h)
      (fun σ : S => Ch σ ∧ VmREntJ9 st ar arI AR MR j (userV K) σ) c hs m q
  | .io j => ∃ h : IoPremW9 st j K m, GlueAt ((ioSlotP3W st ar hA hm).liftAt j K m hK hU (h.toW3 st).toP3)
      (fun σ : S => Ch σ ∧ IoEntJ9 st arI AR MR j K σ) c hs m q
  | i => StartP3W8 st ar hA hm hSt a0 Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartAt` of `fl4LocP3W6`'s family from `StartP3W9`**, given the current chain. -/
theorem startAt_P3W9 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {K : KLayoutV} (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W9 st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W6 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  obtain ⟨σe, hC⟩ := hC
  have hCh := ChainOf.bun hC
  cases i with
  | vmF j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .vmF j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ7 st ar (chain_run P hIoa hC he.1 he.2.hct)⟩⟩
  | vmR j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .vmR j)
      ⟨h, hG.mono fun σ he _ => ⟨he.1, he.2.toJ7 st ar (chain_run P hIoa hC he.1 he.2.hct)⟩⟩
  | io j =>
    obtain ⟨h, hG⟩ := h
    exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .io j)
      ⟨h.toW3 st, hG.mono fun σ he _ => ⟨he.1, he.2.toJ7 st (chain_run P hIoa hC he.1 he.2.hct)⟩⟩
  | st j => exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .st j) h
  | irq j => exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .irq j) h
  | sl j => exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .sl j) h
  | vq j => exact startAt_P3W8 st ar hA hm hSt a0 hCh (i := .vq j) h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EV
