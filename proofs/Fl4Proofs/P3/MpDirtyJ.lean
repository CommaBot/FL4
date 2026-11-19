/-
P3 (DESIGN.md §9), VSpace: **the ASID control cap's `MakePool` at `J` when
the region is dirty** (XTopJointVsCap's `JAsidCPath.dirty`; handoff/utj.md
Round 15): l4v's `delete_objects` of the pool's frame over dead objects, as
the untyped reset's drop (`JAtZ.drop`) at the restart's state, then the
clean case's step (`JAtZ.mpStepJ`) from the drop's state.

* The spec: `perform_asid_control_invocation` from a state detyped at the
  frame is the one from the state itself (`deleteObjects_detype`,
  `perform_mp_detype`: `delete_objects` detypes the frame again).
* `JAtZ.rstAll`, `JAtZ.dropA`: UtDropJ2's `JAtZ.drop` for any free index (an
  unused cap's region is its free part, holding no object of the typed heap).
* `MpEmptyAt` and `JAtZ.mpOObjAt`/`mpPlacedCAt`/`mpRegionCAt`/`mpAddOKAt`:
  XTopJointVsCap's clean-case placement lemmas from an empty region at one
  cap (there from `MpClean`, here from the drop).
-/
import Fl4Proofs.P3.XTopJointMakePool
import Fl4Proofs.P3.UtDropJ2
import Fl4Proofs.P3.VsMakePoolB
import Fl4Proofs.P3.VsDecFrameP
import Fl4Proofs.P3.UtResetSpecJ
import Fl4Proofs.P3.UtResetZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec: the perform after a detype of the frame -/

section Spec
open Fl4Spec

theorem detype_idemD (R : Set ObjRef) (t : State Unit) : detype R (detype R t) = detype R t := by
  simp only [detype]; congr 2; funext x; split <;> rfl

theorem detype_msD (R : Set ObjRef) (σ : State Unit) (ms : MachineState) :
    ({ detype R σ with machineState := ms } : State Unit) = detype R { σ with machineState := ms } := rfl

theorem doMachineOp_runD {α : Type} (mop : NonDet MachineState α) (σ : State Unit) :
    doMachineOp (Z := Unit) mop σ =
      ({y | ∃ x ∈ (mop σ.machineState).1, y = (x.1, { σ with machineState := x.2 })}, (mop σ.machineState).2) := by
  unfold doMachineOp
  simp only [Bind.bind, NonDet.bind, NonDet.gets, NonDet.selectF, NonDet.modify, Pure.pure, NonDet.pure]
  refine Prod.ext ?_ ?_
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl, x1, ⟨h1, h2⟩, x3, rfl, rfl⟩
      obtain ⟨⟨r, ms⟩, t⟩ := x1
      dsimp only at h1 h2 ⊢
      subst h2
      exact ⟨(r, ms), h1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, rfl, (x, σ), ⟨hx, rfl⟩, _, rfl, rfl⟩
  · simp

/-- `delete_objects` from a state detyped at its region: the same outcomes. -/
theorem deleteObjects_detype (a : Word) (n : Nat) (σ : State Unit) :
    deleteObjects (Z := Unit) a n (detype {x | a ≤ x ∧ x ≤ a + 2 ^ n - 1} σ) = deleteObjects (Z := Unit) a n σ := by
  unfold deleteObjects
  show NonDet.bind (doMachineOp _) _ (detype _ σ) = NonDet.bind (doMachineOp _) _ σ
  unfold NonDet.bind
  rw [doMachineOp_runD, doMachineOp_runD]
  simp only [NonDet.modify]
  congr 1
  · ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, by rw [detype_msD, detype_idemD]⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨_, ⟨z, hz, rfl⟩, by rw [detype_msD, detype_idemD]⟩
  · simp only [Set.mem_setOf_eq, and_false, exists_false, or_false]; rfl

/-- **`perform_asid_control_invocation` (`MakePool`) from a state detyped
at the frame** is the one from the state itself. -/
theorem perform_mp_detype (p : ObjRef) (dest ps : CslotPtr) (base : Asid) (σ : State Unit) :
    (performAsidControlInvocation (Z := Unit) (.makePool p dest ps base)) (detype (regionSet p 12) σ) =
      (performAsidControlInvocation (Z := Unit) (.makePool p dest ps base)) σ := by
  unfold performAsidControlInvocation
  show NonDet.bind (deleteObjects (Z := Unit) p page_bits) _ (detype _ σ) =
    NonDet.bind (deleteObjects (Z := Unit) p page_bits) _ σ
  unfold NonDet.bind
  rw [show regionSet p 12 = {x | p ≤ x ∧ x ≤ p + 2 ^ page_bits - 1} from rfl, deleteObjects_detype]

end Spec

/-! ## The drop for any free index -/

section Drop
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **The reset's facts of `UtCapP3.rst` for any free index**: at a
childless RAM untyped cap, the original caps' slots off the region and
core 0's debug-list head off it (`UtCapP3.rst` for a used region; for an
unused one, `fi = 0`, the region is the cap's free part, which holds no
object of the typed heap, `UtCapP3.free`). -/
theorem JAtZ.rstAll (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr} (hsl : AbsSlot Z.th sl)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hnc : ¬ ∃ y, σ.cdt y = some sl) :
    (∀ sl, σ.isOriginalCap sl = true → AbsSlot (restrictTh Z.th p.val (p.val + 2 ^ sb.val)) sl) ∧
    ¬ (p.val ≤ (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val ∧
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)).val < p.val + 2 ^ sb.val) := by
  have U := J.utc sl p sb fi false hsl hcap rfl
  have hND : NotDev (L.mem s) (cslotAddr sl) p sb fi := by
    unfold NotDev; rw [capV_of_capAt hcap]; simp
  by_cases hfi0 : fi.val = 0
  · have hfree := U.free
    rw [hfi0, Nat.add_zero] at hfree
    have hout : ∀ q k, Z.th q = some k → 0 < objSize k → ¬ (p.val ≤ q.val ∧ q.val < p.val + 2 ^ sb.val) := by
      intro q k hq hk hin
      rcases hfree q k hq with h | h <;> omega
    refine ⟨fun sl' h => ?_, ?_⟩
    · obtain ⟨q, h1, h2⟩ := J.kern.orig sl' h
      refine ⟨q, h1, ?_⟩
      rcases h2 with h2 | ⟨h2, h3⟩
      · rw [restrictTh_out (hout q _ h2 (by simp only [objSize]; positivity))]; exact Or.inl h2
      · rw [restrictTh_out (hout q _ h2 (by simp only [objSize]; omega))]; exact Or.inr ⟨h2, h3⟩
    · rcases J.kern.head with h | ⟨h1, -⟩
      · rw [h]
        have := U.high hND
        rintro ⟨g1, -⟩
        have h0 : (0#u64 : U64).val = 0 := rfl
        rw [h0] at g1
        omega
      · exact hout _ _ h1 (by simp only [objSize]; omega)
  · exact U.rst hND hnc hfi0

/-- **`JAtZ` across the drop** (item 2 of handoff/utj.md "Round 9"; any free
index, `JAtZ.rstAll`, handoff/utj.md Round 15): at a
childless RAM untyped cap, from the same FL4 state, the spec state
`σ'` detyped at the region, the kept sets, the restricted typed heap and
P1's heap without the region's objects. Premises beyond `JAtZ`: no
reschedule pending, the spec detype's own facts (`SDrop` and the fields it
keeps), `KeptRefsP3`/`DbgTimerKept` at the region (`RegionUnrefJ` [J]'s two
parts, as `utEpJ`), `ArchFitHyp` [J] (as `utEpJ`), and `VsReachMiss` [J]
(VsDrop). -/
theorem JAtZ.dropA (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread) {sl : Fl4Spec.CslotPtr} (hsl : AbsSlot Z.th sl)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hnc : ¬ ∃ y, σ.cdt y = some sl)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s)
    (hAF : ArchFitHyp H σ)
    {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ')
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hrepr : σ'.reprogramTimer = σ.reprogramTimer) (hcdom : σ'.curDomain = σ.curDomain)
    (hdtime : σ'.domainTime = σ.domainTime) (hist : σ'.interruptStates = σ.interruptStates)
    (hinode : σ'.interruptIrqNode = σ.interruptIrqNode) (harch : σ'.archState = σ.archState)
    (hdl : σ'.domainList = σ.domainList) (hdsi : σ'.domainStartIndex = σ.domainStartIndex)
    (hum : ∀ x, ¬ RgOf p sb x → σ'.machineState.underlyingMemory x = σ.machineState.underlyingMemory x)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1) :
    JAtZ (L := L) arI AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      (H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))) Cs Ac Lst D s a σ' := by
  have U := J.utc sl p sb fi false hsl hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfit := U.pfit
  obtain ⟨hPl, ⟨-, -, hML, hC, -⟩, -⟩ := J.xtop.rel
  have hx : cslotAddr sl ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hsl.isSlot, _, hcap, by simp⟩
  have hcx : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false := capV_of_capAt hcap
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl) := fun y =>
    Mdb.not_desc_of_no_child fun z hz => hnc ((hC.has_child_iff hPl hsl).2 ⟨z, hz⟩)
  have hRD := J.rgDeadD hx hcx hnd
  have hK := J.sKeep hsb hfit hRD hres hKR
  have hND : NotDev (L.mem s) (cslotAddr sl) p sb fi := by
    unfold NotDev; rw [hcx]; simp
  obtain ⟨hrst, hhd⟩ := J.rstAll hsl hcap hnc
  obtain ⟨hcur, hcsc⟩ := J.curLive hsb hfit hres hRD
  obtain ⟨hks, hthT, hthk, hip, hrp, hap, hnk, hnB, hcov, hobj, hzH, hsf, hhs, hscC, hiL⟩ :=
    J.dropPlace hsb hfit hx hcx U.fiLe hAF U.nostr hD
  obtain ⟨hnsc, hinv, hcu, hown, hoff, hact, hc0, hbsa, hsv, hiso, hsl', hcr⟩ := J.dropSpecInv hK hD
  obtain ⟨hcall, hrf, hrr, hyl, hmcp, hbuf⟩ := J.dropMixed hsb hfit hRD hK hD
  obtain ⟨hdel, hfin, hbd⟩ := J.dropDel hsb hfit hx hcx hnd U.nostr (U.ns hnc)
  have hX := J.dropX hres hsl hcap hnc hKR hD hcdt horig hrepr hcdom hdtime hist hinode harch hdl hdsi hum
    hXP hX4 hX3 hX2 hX1 hM
  have hjpl := J.dropJpl hsb hfit hx hcx hnd U.fiLe U.nostr hD
  have hjc := J.dropCov hsb hfit
  have hkn := J.dropKern hsb hfit hD horig harch hcur hcsc hrst hhd (U.gReg hND)
  have hutc := J.dropUtc hsb hfit hcdt horig harch hrst
  have hblk := J.dropBlk hres hx hcx hnd hKR hDT
  exact ⟨hX, hcall, hrf, hrr, hyl, hmcp, hbuf, hks, hthT, hthk, hip, hrp, hap, hnk, hnB, hjpl, hcov, hobj, hzH, hsf,
    hhs, hscC, hjc, hkn, hdel, J.ut, hbd, hfin, hutc, hnsc, hinv, hcu, hown, hoff, hact, hc0, hbsa, hsv, hiso, hsl',
    hcr, hblk, hiL⟩


end Drop

/-! ## The clean case's placement lemmas from an empty region -/

section Empty
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The region `[p, p + 4096)` holds no object and no IPC-buffer word**
(`JAtZ.mpEmpty` and `MpClean`'s word clause at one cap; also after the
detype of the region, XTopJointMakePoolD): what the clean case's placement
lemmas (`JAtZ.mpOObjAt`, `JAtZ.mpPlacedCAt`, `JAtZ.mpRegionCAt`,
`JAtZ.mpAddOKAt`) need. -/
def MpEmptyAt (Z : XSets) (H : P1.Heap) (p : U64) : Prop :=
  (∀ q k, Z.th q = some k → q.val + max (objSize k) 1 ≤ p.val ∨ p.val + 4096 ≤ q.val) ∧
  (∀ q k, H q = some k → q.val + 2 ^ k.bits ≤ p.val ∨ p.val + 4096 ≤ q.val) ∧
  ∀ wp ∈ Z.B, (wp.1.val + 8 ≤ p.val ∨ p.val + 4096 ≤ wp.1.val) ∧
    ∀ i ∈ Fl4Spec.intUpto 0 7, (wp.2 + (7 - BitVec.ofInt 64 i)).toNat < p.val ∨
      p.val + 4096 ≤ (wp.2 + (7 - BitVec.ofInt 64 i)).toNat

/-- `MpEmptyAt` of a clean region (`JAtZ.mpEmpty`, `MpClean`). -/
theorem JAtZ.mpEmptyAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hcl : MpClean (L := L) Z H D s) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64}
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) : MpEmptyAt Z H p :=
  ⟨(J.mpEmpty arI hcl hx hcx hnd).1, (J.mpEmpty arI hcl hx hcx hnd).2, (hcl x hx p fi hcx hnd).2⟩

/-- **No `OObj` word in an empty region** (`JAtZ.mpOObj` from `MpEmptyAt`). -/
theorem JAtZ.mpOObjAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64} (hE : MpEmptyAt Z H p)
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false) :
    ∀ b : U64, p.val ≤ b.val → b.val < p.val + 4096 → ¬ Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b := by
  intro b h1 h2 hO
  obtain ⟨-, hHo, hB⟩ := hE
  have hks := J.jcov.ks x hx p _ fi hcx
  rw [two_pow_asidPool] at hks
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := by have := J.kern.cpuCs; rw [hc.cur] at this; exact this
  have hobj : ∀ {q : U64} {k : P1.HKind}, H q = some k → q.val ≤ b.val → b.val < q.val + 2 ^ k.bits → False :=
    fun {q k} hq l1 l2 => by have := hHo q k hq; omega
  obtain ⟨Tr, Cq, hP⟩ := J.jpl
  rcases hO with ⟨o1, o2⟩ | ⟨o1, o2⟩ | ⟨t, ht, o1, o2⟩ | ⟨e, he, o1, o2⟩ | ⟨r, hr, o1, o2⟩ | ⟨n, hn, o1, o2⟩ |
      ⟨q, hq, y, n, hk, o1, o2⟩ | ⟨wp, hw, o1, o2⟩
  · have := hks.2.1 Z.c hcC; omega
  · have := hks.1; omega
  · exact hobj (J.zH.1 t ht) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (J.zH.2.1 e he) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (J.zH.2.2.1 r hr) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (J.zH.2.2.2 n hn) (by omega) (by simp only [P1.HKind.bits]; omega)
  · exact hobj (hP.sc q y n (J.c0 q hq) hk).2 o1 (by
      simp only [P1.HKind.bits]
      have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_add_right n Fl4Spec.minSchedContextBits)
      omega)
  · have := (hB wp hw).1; omega

set_option maxHeartbeats 1000000 in
/-- **`MpPlacedHyp` from `JAtZ` when the regions are clean** (as VsTopX's
`mpPlacedHyp_of`, from the dead-set cover `JCovD`: a clean region holds no
object, `JAtZ.mpEmpty`, so `restrictTh` keeps `th`, and no `OObj` word,
`JAtZ.mpOObj`). -/
theorem JAtZ.mpPlacedCAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {p : U64} (hE : MpEmptyAt Z H p) {x fi : U64} (hx : x ∈ Z.G.chains.flatten)
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (th' : TypedHeap) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit)
    (hth : th' = restrictTh Z.th p.val (p.val + 4096)) (hk : L.ksb s' = L.ksb s)
    (hsc : ∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n))
    (hRg : MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p) :
    (TopSR st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s' a' σ' →
      TopSR st th' (insert p Z.P) Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR s' a' σ') ∧
    ∀ t : U64, Z.th t = some .tcb → th' t = some .tcb := by
  have hTh := hE.1
  have hrt : restrictTh Z.th p.val (p.val + 4096) = Z.th := by
    funext q
    unfold restrictTh
    split
    · rename_i hq
      cases hk' : Z.th q with
      | none => rfl
      | some k => have := hTh q k hk'; omega
    · rfl
  rw [hrt] at hth
  subst th'
  refine ⟨fun hS => ?_, fun t ht => ht⟩
  obtain ⟨hO, hTP⟩ := hS
  obtain ⟨hpal, hpfit, hp0, -, -, -, hPo, hLo, hTo⟩ := hRg
  have hout := hTh
  have hoob : ∀ b : U64, p.val ≤ b.val → b.val < p.val + 4096 → ¬ Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ' b :=
    fun b h1 h2 hO' => J.mpOObjAt arI hx hE hcx b h1 h2 (Sched.OObj.mono hk hsc hO')
  have hpool : ∀ b, VsWrite (insert p Z.P) (L.ksb s') b → VsWrite Z.P (L.ksb s') b ∨
      (p.val ≤ b.val ∧ b.val < p.val + 4096 ∧ b.val % 8 = 0) := by
    rintro b (h | ⟨q, hq, lo, hl, rfl⟩)
    · exact Or.inl (Or.inl h)
    · rcases hq with rfl | hq
      · right; rw [peA_val hpfit hl]; refine ⟨by omega, by omega, by omega⟩
      · exact Or.inl (Or.inr ⟨q, hq, lo, hl, rfl⟩)
  refine ⟨hO, ⟨hTP.ep, ?_, hTP.pt, hTP.pl, fun b hb hv => ?_, hTP.nodeE, hTP.po, hTP.ps, fun b hb hw => ?_,
    fun b hw => ?_, fun b hw hsw => ?_, hTP.tko⟩⟩
  · -- `vs`
    refine ⟨hTP.vs.ksb_al, hTP.vs.ksb_fit, fun q hq => ?_, fun q hq => ?_⟩
    · rcases hq with rfl | hq
      · exact ⟨hpal, hpfit⟩
      · exact hTP.vs.pal q hq
    · rcases hq with rfl | hq
      · rw [hk]; exact hTo
      · exact hTP.vs.ptab q hq
  · -- `disj`
    rcases hv with h | h | ⟨q, hq, h1, h2'⟩ | h
    · exact hTP.disj b hb (Or.inl h)
    · exact hTP.disj b hb (Or.inr (Or.inl h))
    · rcases hq with (rfl | hq) | hq
      · exact hoob b h1 h2' hb
      · exact hTP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inl hq, h1, h2'⟩)))
      · exact hTP.disj b hb (Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, h1, h2'⟩)))
    · exact hTP.disj b hb (Or.inr (Or.inr (Or.inr h)))
  · -- `pv`
    rcases hpool b hw with h | ⟨h1, h2', -⟩
    · exact hTP.pv b hb h
    · obtain ⟨q, hq, i, hi, rfl⟩ := hb
      have hqa := hTP.pt q hq
      rw [peA_val (tbl_fit hqa) hi] at h1 h2'
      have := hLo q hq; omega
  · -- `vo`
    rcases hpool b hw with h | ⟨h1, h2', h8⟩
    · exact hTP.vo b h
    · refine ⟨h8, fun q k hq hin => ?_⟩
      have := hout q k hq; omega
  · -- `sd`
    rcases hpool b hw with h | ⟨h1, h2', -⟩
    · exact hTP.sd b h hsw
    · obtain ⟨y, hy, hb⟩ := hsw
      obtain ⟨q, i, hqi, rfl⟩ := hy
      have hv := hqi.val hTP.pl
      obtain ⟨k, hk', hs⟩ := hqi.size
      have := hout q k hk'
      have hf := hTP.pl.fits q k hk'
      rcases hb with rfl | rfl
      · rw [hv] at h1 h2'; omega
      · have : (core.num.U64.wrapping_add (slotOf q i) 8#u64).val = (slotOf q i).val + 8 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; rw [hv]; omega
        rw [this, hv] at h1 h2'; omega

/-- **The region facts of `MakePool`'s childless untyped from `JAtZ` when
the regions are clean** (what the old `JMpExtra` asked [J]): `MpRegion`
(alignment, fit and non-null pointer, no straddling object and no MDB slot
from `UtCapP3`; no CNode, pool or page table there: the region holds no
object of `th` or `H`, `JAtZ.mpEmpty`, and the spec's arch objects are `H`'s
`other` objects of at least a page, `SpecCover.arch`; the ASID table off it,
`UtKsApart`) and `RegOKTop` (`JAtZ.mpOObj`, the buffer bytes by
`MpClean`). -/
theorem JAtZ.mpRegionCAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs))
    (hidx : idx.length = rs) {p fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) (hE : MpEmptyAt Z H p) :
    MpRegion Z.th Z.G Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) p ∧ RegOKTop (L := L) Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ p := by
  obtain ⟨hPl, ⟨-, -, hM, hC, -⟩, -⟩ := J.xtop.rel
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hcx := capV_of_capAt hcap
  have hx : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hAs.isSlot, _, hcap, fun h => by cases h⟩
  have hnd := nodesc_of_cdt hPl hC hAs hnch
  have U := J.utc _ p _ fi false hAs hcap rfl
  have hTh := hE.1
  have hHo := hE.2.1
  have hks := J.jcov.ks _ hx p _ fi hcx
  rw [two_pow_asidPool] at hks
  have hpal : p.val % 4096 = 0 := by have := U.pal; rwa [two_pow_asidPool] at this
  have hpfit : p.val + 4096 ≤ 2 ^ 64 := by have := U.pfit; rwa [two_pow_asidPool] at this
  have hoff : ∀ q : U64, (∃ ao, σ.kheap q.bv = some (.archObj ao)) → q.val + 4096 ≤ p.val ∨ p.val + 4096 ≤ q.val := by
    rintro q ⟨ao, hq⟩
    obtain ⟨n, hn, hHq⟩ := J.cover.arch _ ao hq
    have h1 := hHo q _ hHq
    simp only [P1.HKind.bits] at h1
    have h2 : 4096 ≤ 2 ^ n := by
      calc 4096 = 2 ^ 12 := rfl
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
    omega
  have hR := J.xtop.fin.2.1
  have hPt := J.xtop.fin.2.2.1
  refine ⟨⟨hpal, hpfit, ?_, ?_, ?_, ?_, ?_, ?_, hks.2.2⟩, hpal, hpfit, J.mpOObjAt arI hx hE hcx,
    fun wp hw => (hE.2.2 wp hw).2⟩
  · intro e
    have hh := U.high (Sched.notDev_ram hcx)
    rw [e] at hh
    have h0 : (0#u64 : U64).val = 0 := rfl
    rw [h0] at hh
    norm_num at hh
  · have := U.nostr; rwa [two_pow_asidPool] at this
  · have := U.ns hnch; rwa [two_pow_asidPool] at this
  · rintro q r hq ⟨a1, a2⟩
    have := hTh q _ hq
    simp only [objSize] at this
    omega
  · intro q hq
    obtain ⟨f, hf, -⟩ := hR.pool q hq
    exact hoff q ⟨_, hf⟩
  · rintro q (hq | hq | hq | hq)
    · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact hoff q ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact hoff q ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact hoff q ⟨_, hf⟩
    · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact hoff q ⟨_, hf⟩

/-- **The new pool's page joins `H` as an `other` object** (P1's
`AddOKP`, for `BlkOK.addOther`): a clean region holds no object of `H`
(`JAtZ.mpEmpty`), and RAM untyped regions miss the nodes and the
kernel-state block (`UtKsApart`). -/
theorem JAtZ.mpAddOKAt {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {x : U64} (hx : x ∈ Z.G.chains.flatten) {p fi : U64} (hE : MpEmptyAt Z H p)
    (hcx : capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false)
    (hpal : p.val % 4096 = 0) (hpfit : p.val + 4096 ≤ 2 ^ 64)
    (hp0 : p ≠ 0#u64) :
    P1.AddOKP st H (· = p) (.other 12) Cs s := by
  obtain ⟨-, hHo, -⟩ := hE
  have hks := J.jcov.ks x hx p _ fi hcx
  rw [two_pow_asidPool] at hks
  have h12 : (P1.HKind.other 12).bits = 12 := rfl
  refine ⟨fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_, fun q hq p' kp hp' => ?_,
    fun q q' hq hq' hne => absurd (hq.trans hq'.symm) hne, fun q hq c hc => ?_, fun q hq => ?_⟩
  · subst hq
    cases hk : H q with
    | none => rfl
    | some k =>
      have := hHo q k hk
      have := Nat.one_le_two_pow (n := k.bits)
      omega
  · subst hq; rw [h12]; exact hpal
  · subst hq; rw [h12]; exact hpfit
  · subst hq; exact hp0
  · subst hq; rw [h12, show (2:Nat) ^ 12 = 4096 from rfl]; have := hHo p' kp hp'; omega
  · subst hq; rw [h12]; exact hks.2.1 c hc
  · subst hq; rw [h12]; exact hks.1


end Empty

/-! ## Region facts after the drop -/

section Off
variable {th : TypedHeap} {lo hi : Nat}

/-- An object holding a slot off a region, no object straddling it, is off it. -/
theorem obj_off_of_slot (hP : Placed th) (hN : NoStraddle th lo hi) {q : U64} {i : Nat} (hqi : IsSlotAt th q i)
    (hoff : (slotOf q i).val < lo ∨ hi ≤ (slotOf q i).val) : ¬ (lo ≤ q.val ∧ q.val < hi) := by
  intro hin
  have hv := hqi.val hP
  obtain ⟨k, hk, hs⟩ := hqi.size
  rcases hN q k hk with h | h | h <;> omega

/-- A slot off a region is a slot of the restricted typed heap. -/
theorem isSlot_restrict_off (hP : Placed th) (hN : NoStraddle th lo hi) {y : U64} (hy : IsSlot th y)
    (hoff : y.val < lo ∨ hi ≤ y.val) : IsSlot (restrictTh th lo hi) y := by
  obtain ⟨q, i, hqi, rfl⟩ := hy
  have hq := obj_off_of_slot hP hN hqi hoff
  refine ⟨q, i, ?_, rfl⟩
  unfold IsSlotAt
  rw [restrictTh_out hq]
  exact hqi

/-- A CNode slot off a region: its CNode is off it. -/
theorem cnode_off_of_slot (hP : Placed th) (hN : NoStraddle th lo hi) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : th pp = some (.cnode rs)) (hidx : idx.length = rs)
    (hoff : (cslotAddr (pp.bv, idx)).val < lo ∨ hi ≤ (cslotAddr (pp.bv, idx)).val) :
    ¬ (lo ≤ pp.val ∧ pp.val < hi) := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  obtain ⟨q, i, hqi, hq1, he⟩ := hAs.at
  have e : q = pp := P1.eq_of_bv hq1.symm
  subst e
  rw [he] at hoff
  exact obj_off_of_slot hP hN hqi hoff

end Off

/-! ## The dirty case at `J` -/

section Dirty
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- **The destination CNode misses a childless untyped cap's region**
(`DestLive`: a CNode cap of the MDB names it, `cnode_off_childless`, or it
lies in the kernel-state block, off every RAM untyped region). -/
theorem JAtZ.destOff {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {pd : U64} {rd : Nat} (hpd : Z.th pd = some (.cnode rd)) (hDL : DestLive Z.th (L.mem s) (L.ksb s) pd)
    {x : U64} (hx : x ∈ Z.G.chains.flatten) {p sb fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false)
    (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) : ¬ (p.val ≤ pd.val ∧ pd.val < p.val + 2 ^ sb.val) := by
  obtain ⟨-, ⟨-, -, hM, -, hI⟩, -⟩ := J.xtop.rel
  rcases hDL with ⟨y, r, gs, g, hy, hc⟩ | h
  · have hyG : y ∈ Z.G.chains.flatten := (hM.members y).2 ⟨hy, _, capAt_capV _ _, by rw [hc]; simp⟩
    exact cnode_off_childless J.ut hI hx hcx hnd hyG hc
  · obtain ⟨k1, -, -⟩ := J.jcov.ks x hx p sb fi hcx
    have := h _ hpd
    simp only [objSize] at this
    have := Nat.one_le_two_pow (n := rd)
    omega

set_option maxHeartbeats 16000000 in
/-- **The ASID control cap at `JAt`, any region** (the dirty case of
`JAsidCPath`; module docstring): VsDecFrameP's
`decode_invocation_asid_controlXP` with `MakePool`'s perform: FL4's restart
(`JAtZ.restartJ`), the drop of the pool's frame at the restart's state
(`JAtZ.dropA`, the spec's state detyped there), then `mp_perform_relB` and
`JAtZ.mpStepJ` from the drop's `JAtZ`, whose region is empty (`MpEmptyAt`); the
spec's perform from the detyped state is its perform from the restart's
(`perform_mp_detype`). The domain schedule from the footprint (`VsFootW`, as
VsThX's `domFrame_asid_control`). Premises: `ArchFitHyp` and
`RegionUnrefJ` [J] (as `JUtPath.heapH`), and `VsReachMiss` [J] at the
restart's state for a childless pool-sized RAM untyped's region, with no
extra roots (as `JUtPath.vsReach`). -/
theorem decode_invocation_asid_controlJD (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    (hAF : ArchFitHyp H σ) (hRU : RegionUnrefJ (L := L) arI H Cs)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlM : lbl = fl4_abi.label.X86ASIDControlMakePool ↔
      Fl4Spec.invocationType slbl = .archInvocationLabel .x64ASIDControlMakePool)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hVM : ∀ (x p fi : U64) (s1 : S), x ∈ Z.G.chains.flatten →
      capV (L.mem s) x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false → (∀ y, ¬ Mdb.Desc Z.G.par y x) →
      sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
      Vs.VsReachMiss p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1) (L.ksb s1) ∅ ∅ ∅ ∅ ∅)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hext : JMpExtra (L := L) Z s extra excaps)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  obtain ⟨hcur, htcb⟩ := J.ctTcb arI hct
  obtain ⟨hPl, hCR, hFI, hDR, hMO, hIA, -⟩ := hX.rel
  have hrun := J.curRun.run hni
  obtain ⟨xct, hkt0, -⟩ := hCR.1.tcb ct htcb
  have hkt : σ.kheap σ.curThread = some (.tcb xct) := by rw [hcur]; exact hkt0
  have hc2 : sched.cur_thread st s = ok (L.curW s) := cur_thread_eq s
  have hctE : ct = L.curW s := by rw [hct] at hc2; exact eq_of_ok_eq hc2
  -- the footprint (VsThX's `domFrame_asid_control`)
  let W : U64 → Prop := fun b => VsFootW st Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 s b ∨
    ¬ ((L.ksb s).val ≤ b.val ∧ b.val < (L.ksb s).val + 13568)
  have hext' : (∃ o0 o1, vspace.extra extra 0#usize = ok o0 ∧ vspace.extra extra 1#usize = ok o1 ∧
        (o0 = none ∨ o1 = none) ∧ excaps.length ≤ 1) ∨
      ∃ (pp : U64) (rs : Nat) (idx : List Bool) (y : obj.Slot) (uc : capability.Cap) (uc' : Fl4Spec.Cap)
        (rc : capability.Cap) (rc' : Fl4Spec.Cap) (ysl : Fl4Spec.CslotPtr)
        (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)),
        Z.th pp = some (.cnode rs) ∧ idx.length = rs ∧
        vspace.extra extra 0#usize = ok (some (cslotAddr (pp.bv, idx))) ∧ vspace.extra extra 1#usize = ok (some y) ∧
        capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok uc ∧ CapRel uc uc' ∧
        capAt (L.mem s) y = ok rc ∧ CapRel rc rc' ∧ CapValid Z.th rc ∧
        excaps = (uc', (pp.bv, idx)) :: (rc', ysl) :: rest ∧
        ∀ (p sb fi : U64), sb = fl4_abi.consts.bits.ASID_POOL →
      capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false) →
      (¬ ∃ sl, σ.cdt sl = some (pp.bv, idx)) →
      ∀ (pd : U64) (rd : Nat) (idxd : List Bool), Z.th pd = some (.cnode rd) → idxd.length = rd →
      capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null → CnRef Z.th (L.mem s) rc pd →
      ∀ (i base : U64), i.val < 2048 → base.val = i.val * 512 →
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let i1 ← lift (sb &&& 63#u64)
        let i2 ← 1#u64 <<< i1
        let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s1 (capability.Cap.Untyped p sb i2 false)
        let s3 ← st.clear_free s2 p 4096#u64
        let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
        let s5 ← vspace.set_asid_table st s4 i p
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, ar)) ⦃ res =>
        res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' th' G',
          ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).1 ∧
          ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
            Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).2 ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) σ' G' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
          MdbOKV (L.ksb s) (L.mem res.2.1) G' ∧ P1.WritesIn st s res.2.1 W ∧
          (DomRel (L.mem res.2.1) (L.ksb res.2.1) σ' → JAt (L := L) arI AR res.2.1 res.2.2 σ') ⦄ := by
    rcases hext.2 with h | ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    · exact Or.inl h
    refine Or.inr ⟨pp, rs, idx, y, uc, uc', rc, rc', ysl, rest, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
    intro p sb fi hsb hcap hnch pd rd idxd hpd hld hnull hCn i base hi hbase
    subst hsb
    have hpp := h1
    have hidx := h2
    have hsbv : (fl4_abi.consts.bits.ASID_POOL).val = 12 := by unfold fl4_abi.consts.bits.ASID_POOL; rfl
    have h2sb : 2 ^ (fl4_abi.consts.bits.ASID_POOL).val = 4096 := by rw [hsbv]; norm_num
    have hRg12 : ∀ o, RgOf p fl4_abi.consts.bits.ASID_POOL o ↔ o ∈ regionSet p.bv 12 := fun o => by
      show o ∈ regionSet p.bv (fl4_abi.consts.bits.ASID_POOL).val ↔ _; rw [hsbv]
    -- the source cap: in the MDB, childless, its region's facts
    have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
    have hxG : cslotAddr (pp.bv, idx) ∈ Z.G.chains.flatten :=
      (hCR.2.2.1.members _).2 ⟨hAs.isSlot, _, hcap, fun h => by cases h⟩
    have hnd := nodesc_of_cdt hPl hCR.2.2.2.1 hAs hnch
    have hcv := capV_of_capAt hcap
    have U := J.utc _ p _ fi false hAs hcap rfl
    have hfit := U.pfit
    rw [h2sb] at hfit
    have hns := U.ns hnch
    rw [h2sb] at hns
    have hN := U.nostr
    have hppOff : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) :=
      cnode_off_of_slot hPl hN hpp hidx (by rw [h2sb]; exact hns _ hxG)
    have hDL0 : DestLive Z.th (L.mem s) (L.ksb s) pd :=
      DestLive.of_cnRef (kb := L.ksb s) hCn ⟨y, hext.1 y h4, capV_of_capAt h7⟩
    have hpdOff := J.destOff arI hpd hDL0 hxG hcv hnd
    -- the restart
    obtain ⟨s1, σ1, x1, -, hst1, hkx, hcur1, he1, -, hid1, hct1, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
    obtain ⟨s1', σ1', -, hs1', -, hSS1, -, -, hk1, hcpu1⟩ :=
      restart_dstate Z.th hPl s σ Z.G J.dstate ct hct hcur htcb J.kern.act
    rw [hs1] at hs1'; cases eq_of_ok_eq hs1'
    have hσ1k : ∀ o, o ≠ ct.bv → σ1.kheap o = σ.kheap o := fun o ho => by
      rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; exact Function.update_of_ne ho _ _
    have hσ1c : σ1.kheap ct.bv = some (.tcb { x1 with tcbState := .restart }) := by
      rw [he1, Notif.stsAct_kheap, Notif.updK_kheap]; simp
    have hσ1cdt : σ1.cdt = σ.cdt := by rw [he1]; unfold Notif.stsAct; split_ifs <;> rfl
    have hres1 : σ1.schedulerAction ≠ .chooseNewThread := by
      rw [he1, J.restart_keeps_resume hni hkx hcur1]; simp
    have hAF1 : ArchFitHyp H σ1 := fun o ao n h hH => hAF o ao n (by
      by_cases ho : o = ct.bv
      · subst ho; rw [hσ1c] at h; cases h
      · rwa [hσ1k o ho] at h) hH
    have hcap1 : capAt (L.mem s1) (cslotAddr (pp.bv, idx)) =
        ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi false) := (hSS1.capAt hAs.isSlot).trans hcap
    have hnch1 : ¬ ∃ y, σ1.cdt y = some (pp.bv, idx) := by rw [hσ1cdt]; exact hnch
    -- the kept references at the restart's state (`RegionUnrefJ` [J])
    have hs1c : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s1 := by rw [← hctE]; exact hs1
    obtain ⟨hKR, hDT⟩ := hRU AR Z Ac Lst D s s1 ar σ J hs1c p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val)
      (fun q k hq hr => (region_deadP J.jcov J.ut hCR.2.2.2.2 hxG hcv (Or.inr ⟨hnd, le_rfl⟩) le_rfl q k hq hr).1)
    -- the drop at the restart's state
    set σd : Fl4Spec.State Unit := Fl4Spec.detype (regionSet p.bv 12) σ1 with hσd
    have hSD : SDrop (RgOf p fl4_abi.consts.bits.ASID_POOL) σ1 σd :=
      ⟨fun o ho => by have h := (hRg12 o).1 ho; rw [hσd]; simp only [Fl4Spec.detype]; exact if_pos h,
        fun o ho => by
          have h : o ∉ regionSet p.bv 12 := fun h => ho ((hRg12 o).2 h)
          rw [hσd]; simp only [Fl4Spec.detype]; exact if_neg h,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have Jd := J1.dropA hres1 hAs hcap1 hnch1 hKR hDT hAF1 hSD rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ => rfl) (Set.empty_subset _) (Set.empty_subset _) (Set.empty_subset _) (Set.empty_subset _)
      (Set.empty_subset _) (hVM _ p fi s1 hxG hcv hnd hs1)
    set Zd := ((Z.keep (KOff (RgOf p fl4_abi.consts.bits.ASID_POOL)) (KBOf p fl4_abi.consts.bits.ASID_POOL)).dropV
      p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val) (L.mem s1)) with hZd
    set Hd := H.drop (P1.RegionD H p.val (p.val + 2 ^ (fl4_abi.consts.bits.ASID_POOL).val)) with hHd
    obtain ⟨hPld, hCRd, hFId, hDRd, hMOd, hIAd, -⟩ := Jd.xtop.rel
    have hppd : Zd.th pp = some (.cnode rs) := by
      show restrictTh Z.th _ _ pp = _; rw [restrictTh_out hppOff]; exact hpp
    have hpdd : Zd.th pd = some (.cnode rd) := by
      show restrictTh Z.th _ _ pd = _; rw [restrictTh_out hpdOff]; exact hpd
    have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
    have hnull1 : capAt (L.mem s1) (cslotAddr (pd.bv, idxd)) = ok .Null := (hSS1.capAt hAd.isSlot).trans hnull
    have hnchd : ¬ ∃ y, σd.cdt y = some (pp.bv, idx) := hnch1
    obtain ⟨k1, -, -⟩ := J.jcov.ks _ hxG p _ fi hcv
    rw [h2sb] at k1
    have hN4 := hN
    rw [h2sb] at hN4
    -- the region is empty at the drop's state
    have hE : MpEmptyAt Zd Hd p := by
      refine ⟨fun q k hq => ?_, fun q k hq => ?_, fun wp hw => ?_⟩
      · obtain ⟨hq0, hqo⟩ := restrictTh_some hq
        rw [h2sb] at hqo
        have hm1 := le_max_left (objSize k) 1
        have hm2 := le_max_right (objSize k) 1
        have hm3 := max_choice (objSize k) 1
        rcases hN4 q k hq0 with h | h | h <;> rcases hm3 with e | e <;> rw [e] <;> omega
      · obtain ⟨hr, hq0⟩ := P1.Heap.drop_eq_some.1 hq
        unfold P1.RegionD P1.MeetsR at hr
        rw [hq0] at hr
        simp only [Option.elim, not_not] at hr
        rw [h2sb] at hr
        omega
      · obtain ⟨-, hb, hw1⟩ := hw
        rw [h2sb] at hw1
        refine ⟨hw1, fun i hi => ?_⟩
        have h0 : ¬ ((wp.2 + (7 - BitVec.ofInt 64 i)) ∈ regionSet p.bv 12) := fun h => hb i hi ((hRg12 _).2 h)
        rw [regionSet_iff' p _ 12 (by decide) hfit] at h0
        omega
    have hxGd : cslotAddr (pp.bv, idx) ∈ Zd.G.chains.flatten := hxG
    have hcvd := capV_of_capAt hcap1
    obtain ⟨hRg, hRO⟩ := Jd.mpRegionCAt arI hppd hidx hcap1 hnchd hE
    -- FL4's restart, then the perform from the drop's state
    rw [hs1]; simp only [bind_ok]
    refine WP.spec_mono (mp_perform_relB (L := L) vsMpHyps_top s1 ar σd Zd.G hPld hCRd.1 hCRd.2.1 hCRd.2.2.1
      hCRd.2.2.2.1 hCRd.2.2.2.2 Jd.ut Jd.xtop.fin.2.1 Jd.xtop.fin.2.2.1 Jd.xtop.fin.1 Jd.xtop.fin.1.2.vs
      Jd.xtop.fin.1.2.pt hppd hidx rfl hcap1 hnchd hpdd hld hnull1 hi hbase hRg hRO Jd.xtop.fin.1.2.vo
      Jd.xtop.fin.1.2.po Jd.xtop.fin.1.2.pv hFId hMOd.1.1 (rc := rc)) ?_
    rintro res ⟨hok, har, σ', th', G', hm, hnf, hP', hSt', hSV', hM', hC', hI', hU', hR', hPt', hSRq, hF', -, -, hMS, -,
      hcur', hth', hk', hsc, hRg', hxu, hPI', hMid⟩
    obtain ⟨hi', hh, hks1, hcpu1', hW, hzero, -, hMs, hkp, hkh, hcdt, horig, hsrc, hdst, hcap', hDI, -, -⟩ := hMid
    have hTh := hE.1
    have hrt := restrictTh_clean hTh
    rw [hrt] at hth'
    subst hth'
    -- the spec: the restart, then the perform from the restart's state
    have hpe := perform_mp_detype p.bv (pd.bv, idxd) (pp.bv, idx) base.bv σ1
    have hmem : ((), σ') ∈ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).1 := by
      rw [nd_bind_one hst1, ← hpe]; exact hm
    have hnf1 : ¬ ((Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
        Fl4Spec.performAsidControlInvocation (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ).2 := by
      rw [nd_bind_one hst1, ← hpe]; exact hnf
    have hMO' : MdbOKV (L.ksb s1) (L.mem res.2.1) G' := hMS.okv hMOd
    -- the footprint
    have hWr0 : P1.WritesIn st s s1 W := by
      have h := sts_foot (W := W) hPl (fun b h => Or.inl h.toW) (P1.WritesIn.refl s W) htcb J.kern.act
        (v := sched.TS_RESTART)
      rw [hs1, WP.spec_ok] at h; exact h
    have hWr1 : P1.WritesIn st s1 res.2.1 W := ⟨hks1, hcpu1', fun b hb hn => hW b hb (fun hw => hn (by
      rcases hw with ⟨x', k, hx', hk, rfl⟩ | hr | rfl
      · exact Or.inl (Or.inr (Or.inl ⟨x', k, hx'.of_restrict, hk, rfl⟩))
      · right; rintro ⟨g1, g2⟩; rcases k1 with e | e <;> omega
      · exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨hi', hh, by rw [hk1]⟩)))))))⟩
    refine ⟨hok, har, σ', Zd.th, G', hmem, hnf1, hP', ⟨hSt', hSV', hM', hC', hI'⟩, hF', by rw [← hk1]; exact hMO',
      hWr0.trans1 hWr1, fun hDR' => ?_⟩
    -- `XTopAt` after (as `decode_invocation_asid_controlJC`)
    have hTSR := Jd.mpPlacedCAt arI hE hxGd hcvd Zd.th res.2.1 res.2.2 σ' hrt.symm hk' hsc hRg'
    have hXd := Jd.xtop
    have hFx : FinX st Zd.th (insert p Zd.P) Zd.L4 Zd.L3 Zd.L2 Zd.L1
        (TopSR st Zd.th (insert p Zd.P) Zd.L4 Zd.L3 Zd.L2 Zd.L1 Zd.N Zd.T Zd.C Zd.E Zd.R Zd.B Zd.c AR)
        res.2.1 res.2.2 σ' := by
      refine ⟨hTSR.1 hSRq, hR', hPt', hPI' Zd.L4 hXd.fin.2.2.2.1, ?_⟩
      obtain ⟨t, h1, h2, -⟩ := hXd.fin.2.2.2.2
      obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hMO'.2.2
      have h2' := hTSR.2 t h2
      refine ⟨t, h1.trans hcur'.symm, h2', fun q asid h => ?_⟩
      have hv := hVC.at hM' ⟨t, 1, Or.inr ⟨h2', by decide⟩, rfl⟩ h (by simp)
      simp only [VCapOK] at hv
      exact (hv.2.2 trivial).1
    obtain ⟨⟨⟨hSch, hEp, hNt, -⟩, -⟩, -⟩ := id hFx
    have hX' : XTopAt (L := L) AR (Zd.mp G' p) res.2.1 res.2.2 σ' :=
      ⟨hFx, ⟨hFx.1.2.pl, ⟨hSt', hSV', hM', hC', hI'⟩, hF', hDR', by rw [hk']; exact hMO',
        IpcApart.of_topD hFx.1.2 (by rw [hk']; exact hIAd.dom), ScApart.of_top hFx.1.2⟩,
        IpcRel.of hNt hEp (sched_sc hSch), hXd.esa.mono hk' (fun q y n hq => hsc ⟨q⟩ y n hq)⟩
    -- `JAtZ` after, from the drop's `JAtZ` (`JAtZ.mpStepJ`)
    have Ad := Jd.mpAddOKAt arI hxGd hE hcvd hRg.pal hRg.pfit hRg.p0
    have hspecd : ∀ o ko, σd.kheap o = some ko → o.toNat < p.val ∨ p.val + 4096 ≤ o.toNat := by
      intro o ko ho
      have h0 : o ∉ regionSet p.bv 12 := fun hin => by
        have e : σd.kheap o = none := hSD.kin o ((hRg12 o).2 hin)
        rw [e] at ho; cases ho
      rw [regionSet_iff' p o 12 (by decide) hfit] at h0
      omega
    have hDLd : DestLive Zd.th (L.mem s1) (L.ksb s1) pd := by
      rcases hDL0 with ⟨y', r, gs, g, hy', hc⟩ | h
      · have hy'G : y' ∈ Z.G.chains.flatten := (hCR.2.2.1.members y').2 ⟨hy', _, capAt_capV _ _, by rw [hc]; simp⟩
        exact Or.inl ⟨y', r, gs, g, isSlot_restrict_off hPl hN hy' (by rw [h2sb]; exact hns y' hy'G),
          by rw [hSS1.capV hy']; exact hc⟩
      · exact Or.inr (fun k hk => by rw [hk1]; exact h k (restrictTh_some hk).1)
    exact ⟨_, _, Cs, Ac1, Lst1, D1, Jd.mpStepJ hh hTh hE.2.1 Ad hspecd hppd hidx hcap1 hnchd hpdd hld hnull1 hDLd hX'
      ⟨hks1, hcpu1', hW⟩ hzero hMs hkp hkh hcdt horig hsrc hdst hcap' (hDI Jd.del) hU'⟩
  have hD := decode_invocation_asid_controlXP arI Z.th hPl s ar σ Z.G hCR hFI J.ut hMO vsMpHyps_top hX.fin.1
    hX.fin.2.1 hX.fin.2.2.1 hX.fin.1.2.vs hX.fin.1.2.pt hX.fin.1.2.vo hX.fin.1.2.po hX.fin.1.2.pv lbl slbl hlM length
    buf ct hct hcur htcb J.kern.act hrun args hlen hargs extra excaps (Q := fun s' => P1.WritesIn st s s' W)
    (X := fun s' a' σ' => DomRel (L.mem s') (L.ksb s') σ' → JAt (L := L) arI AR s' a' σ') hext'
    (fun _ => ⟨Z, H, Cs, Ac, Lst, D, J⟩) slot blk call don fp ci sl buffer
  -- the domain schedule (VsThX's `domFrame_asid_control`)
  have hS := hX.fin.1
  have hF : DomFrame (L := L) arI s ar σ lbl length slot .AsidControl blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
    refine ⟨WP.spec_mono hD fun res hr => ?_, dk_spec_arch ⟨_, rfl⟩ hkt⟩
    rcases hr.2 with e | hw
    · rw [e]; exact ⟨rfl, fun _ _ => rfl⟩
    · refine ⟨hw.1, fun o ho => hw.2.2 _ ?_ ?_⟩
      · have := hS.2.vs.ksb_fit
        exact ksW_al (by omega) hS.2.vs.ksb_al (domOffs_lt' ho).1 (domOffs_lt' ho).2
      · rintro (h | h)
        · exact dom_not_foot hS ho h
        · apply h
          have := hS.2.vs.ksb_fit
          have hb : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by have := (domOffs_lt' ho).1; omega)
          have := (domOffs_lt' ho).1
          rw [hb]; omega
  exact Or.inl (DecOKMX.toXD arI (DecOKMQX.toX arI hD (fun _ _ _ h => h)) hF
    (okAll_specDec_asidControl fp slbl (args.map UScalar.bv) ci sl excaps buffer) hDR (fun _ _ _ hx hd => hx hd))

end Dirty

end

end Fl4Proofs.P3
