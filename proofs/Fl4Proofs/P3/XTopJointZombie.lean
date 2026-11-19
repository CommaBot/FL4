/-
P3 (DESIGN.md §9), CSpace: **the zombie steps of the deletion at `J`**
(XTopJointDelR's `JRdTrivHyp`, `JZombieHyp`, `JSwapHyp`).

* `JAtZ.obj_ready`: a slot whose cap's range is exactly one object of `H`,
  dead and not an SC, is ready to be emptied (`EmptyReady`; as
  `JAtZ.tcb_ready`).
* `JAtZ.zombie_ready`: a zombie's slot is ready: `DelInv`'s `ZOK` puts the
  zombie over a CNode of `Z.th` (`H`'s `other`, dead for `DeadP`) or a TCB;
  for a TCB the TCB's deadness is asked (`hd`).
* `JAtZ.zombieJCore`: a zombie written over a cap alike it (the deletion's
  `ZombieHypW` edit) keeps `JCs` and `JRest` at the same dead set, by
  `jowes_slotD`: the cover kept (the zombie covers what the cap it replaces
  covered, `CapAlike`), the untyped caps' facts kept (the slot's word is in
  no untyped cap's free part, the CDT, the original bits and the MDB's slots
  kept), the TCBs' fault-handler slots kept (`JPlaced.fh`: null or an
  endpoint cap, and no zombie is alike an endpoint cap: `ZOK`, `CapTyped`).
  No `DestLive` is read: the written slot was already linked.
* `JAtZ.swapJCore`: the zombie swapped with its first slot (the deletion's
  `SwapHypW` edit) keeps `JCs` and `JRest`, by `jowes_slotD`: the caps and
  the MDB renamed along the swap (the cover and the untyped regions kept,
  the TCBs' fault-handler slots neither of the two: `JPlaced.fh`, the
  objects apart), the CDT's children renamed (`CdtRel` before and after),
  the untyped caps' facts after from those before but for the first slot,
  linked after, which misses the region of an untyped cap without children
  (the zombie, a physical cap of the MDB covering it, by `ut_free`).
-/
import Fl4Proofs.P3.XTopJointEmpty
import Fl4Proofs.P3.ScDeadStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- **A slot is ready when its cap's range is one dead object of `H`** (not
an SC; as `JAtZ.tcb_ready`). -/
theorem JAtZ.obj_ready (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} {c : capability.Cap}
    (hcv : capV (L.mem s) x = c) {q : U64} {k : P1.HKind} (hHq : H q = some k)
    (e1 : baseF c = q.val) (e2 : topF c = q.val + 2 ^ k.bits - 1) (hd : DeadP (L := L) H s q)
    (hk : ∀ z, k ≠ .sc z) : EmptyReady (L := L) H Z.G s x := by
  unfold EmptyReady
  rw [hcv, e1, e2]
  intro _ _
  have hout : ∀ q' k', H q' = some k' → q' ≠ q → q'.val + 2 ^ k'.bits ≤ q.val ∨ q.val + 2 ^ k.bits ≤ q'.val :=
    fun q' k' hq' hne => J.kern.heap.disj q' k' q k hq' hHq hne
  have h1k : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
  intro lo hi hlh h1 h2
  · right
    intro q' hq'
    by_cases e : q' = q
    · subst e; exact hd
    · cases hk' : H q' with
      | none => exact deadP_none hk'
      | some k' =>
        exfalso
        have : 1 ≤ 2 ^ k'.bits := Nat.one_le_two_pow
        rcases hout q' k' hk' e with h | h <;> omega

/-- The range of a zombie over a CNode of radix `zt` (`zt + 5 < 64`). -/
theorem range_zombieCn (p zt n : U64) (hne : zt ≠ capability.ZOMBIE_TCB) (hr : zt.val + 5 < 64)
    (hfit : p.val + 2 ^ (zt.val + 5) ≤ 2 ^ 64) :
    baseF (.Zombie p zt n) = p.val ∧ topF (.Zombie p zt n) = p.val + 2 ^ (zt.val + 5) - 1 := by
  have hs : (core.num.U64.wrapping_add zt fl4_abi.consts.bits.SLOT).val = zt.val + 5 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits,
      fl4_abi.consts.bits.SLOT]
    omega
  have h := Sched.capRange (c := .Zombie p zt n) (p := p) (b := core.num.U64.wrapping_add zt fl4_abi.consts.bits.SLOT)
    (ok_inj (ptr_eq _).symm) (ok_inj (by rw [← size_eq]; simp only [objects.cap_size_bits, hne, ↓reduceIte]))
    (by rw [hs]; exact hr) (by rw [hs]; exact hfit)
  rw [hs] at h
  exact h

/-- **A zombie's slot is ready to be emptied** (module docstring): a CNode
zombie's CNode is `H`'s `other` object, dead for `DeadP`; a TCB zombie's
TCB is dead by `hd`. -/
theorem JAtZ.zombie_ready (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x)
    {p zt n : U64} (hcv : capV (L.mem s) x = .Zombie p zt n) (hd : zt.val = 65 → DeadP (L := L) H s p) :
    EmptyReady (L := L) H Z.G s x := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  rcases J.del.zwf x hx p zt n hcv with ⟨h65, hth, -⟩ | ⟨h65, hth, -⟩
  · have hz : zt = capability.ZOMBIE_TCB := UScalar.eq_of_val_eq (by rw [zombie_tcb_val]; exact h65)
    subst hz
    have hHp : H p = some .tcb := (hJ.tcb p).1 hth
    obtain ⟨r1, r2⟩ := range_thread p (J.kern.heap.fits p _ hHp)
    have al : CapAlike (.Zombie p capability.ZOMBIE_TCB n) (.Thread p) := capAlike_zombie_thread
    exact J.obj_ready hcv hHp (al.base.trans r1) (al.top.trans r2) (hd h65) (fun z e => by cases e)
  · have hne : zt ≠ capability.ZOMBIE_TCB := fun e => h65 (by rw [e, zombie_tcb_val])
    have hHp : H p = some (.other (zt.val + 5)) := hJ.cnode p zt.val hth
    have hlt : zt.val + 5 < 64 := J.kern.heap.lt64 p _ hHp
    obtain ⟨r1, r2⟩ := range_zombieCn p zt n hne hlt (J.kern.heap.fits p _ hHp)
    exact J.obj_ready hcv hHp r1 r2
      ⟨fun e => (by rw [hHp] at e; cases e), fun e => (by rw [hHp] at e; cases e),
        fun e => (by rw [hHp] at e; cases e), fun e => (by rw [hHp] at e; cases e),
        fun z e => (by rw [hHp] at e; cases e)⟩
      (fun z e => by cases e)

/-- **No zombie written over an endpoint cap**: the zombie's object is a TCB
or a CNode of `Z.th` (`ZOK`), the endpoint cap's an endpoint of `H`. -/
theorem zombie_not_ep {th : TypedHeap} {H : P1.Heap} {Tr Cq : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hJ : Sched.JPlaced (L := L) th H Tr Cq s σ) {p zt n : U64} (hz : ZOK th p zt n)
    {ep b0 : U64} {b1 b2 b3 b4 : Bool}
    (hal : CapAlike (.Zombie p zt n) (.Endpoint ep b0 b1 b2 b3 b4)) (hep : H ep = some .ep) : False := by
  have hr := hal.refs
  simp only [absCap, Fl4Spec.objRefs, Set.singleton_eq_singleton_iff] at hr
  have hpe : p = ep := by rw [UScalar.eq_equiv_bv_eq]; exact hr
  subst hpe
  rcases hz with ⟨-, hth, -⟩ | ⟨-, hth, -⟩
  · rw [(hJ.tcb p).1 hth] at hep; cases hep
  · rw [hJ.cnode p _ hth] at hep; cases hep

set_option maxHeartbeats 16000000 in
/-- **A zombie written over a cap alike it keeps `JAtZ`, relationally**
(module docstring): from the facts of the `set_cap` step (the spec's
outcome, `DState` after at the same ghost tree, the slot's zombie and the
others kept, `XTopAt` after, the slot words' frame, `CnK`), the
kernel-state base, `KBack`, `JCs` and `JRest` after. -/
theorem JAtZ.zombieJCoreD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p zt n : U64} (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hal : CapAlike (.Zombie p zt n) (capV (L.mem s) (cslotAddr sl)))
    {s2 : S} {σ2 : Fl4Spec.State Unit} {V2 : XVs}
    (hsc : Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ = ({((), σ2)}, False))
    (hDS2 : DState (L := L) Z.th s2 σ2 Z.G)
    (hz2 : capV (L.mem s2) (cslotAddr sl) = .Zombie p zt n)
    (hoth2 : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s2) y = capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv Z.G V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧ IpcFrKeep σ σ2 ∧ JCs (L := L) (Z.mv Z.G V2) s2 σ2 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JRest (L := L) arI (Z.mv Z.G V2) H Cs Ac' Lst' D s2 σ2 := by
  have hP := J.xtop.rel.1
  have hw : P1.WritesIn st s s2 (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  obtain ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hDl2, hFI2⟩ := hDS2
  have hMO := hX2.rel.2.2.2.2.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkc : KeepCT σ σ2 := KeepCT.of_cnK hcn2
  have hmem : ((), σ2) ∈ (Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ).1 := mem_of_single hsc
  have hkz : KSz σ σ2 := nkz_setCap _ _ σ ((), σ2) hmem
  have hcd : CdtKeepOff (fun _ => False) σ σ2 := ncd_setCap _ _ σ ((), σ2) hmem
  have hok : OKeep (fun _ => False) σ σ2 := no_setCap _ _ σ ((), σ2) hmem
  have hxs : IsSlot Z.th (cslotAddr sl) := hA.isSlot
  have hTK : TypedKept Z.th (L.mem s) (L.mem s2) := fun x hx => by
    by_cases e : x = cslotAddr sl
    · left; rw [e, hz2]; rfl
    · right; exact ⟨x, hx, by rw [hoth2 x hx e]⟩
  have hT3 : ∀ t, Z.th t = some .tcb → capAt (L.mem s2) (slotOf t 3) = capAt (L.mem s) (slotOf t 3) ∨
      capV (L.mem s2) (slotOf t 3) = .Null := by
    intro t ht
    have h1 : IsSlot Z.th (slotOf t 3) := ⟨t, 3, Or.inr ⟨ht, by decide⟩, rfl⟩
    by_cases hne : slotOf t 3 = cslotAddr sl
    · exfalso
      rcases hJ.fh t ht with e | ⟨ep, b0, b1, b2, b3, b4, e⟩
      · rw [cslot_tcb3, hne] at e; exact hxn e
      · rw [cslot_tcb3] at e
        have hep : H ep = some .ep := (hJ.typed _ h1).1 ep b0 b1 b2 b3 b4 e
        rw [hne] at e
        rw [e] at hal
        exact zombie_not_ep hJ (hDl2.zwf _ hxs p zt n hz2) hal hep
    · left; rw [capAt_capV, capAt_capV, hoth2 _ h1 hne]
  have hT2 : ∀ t, Z.th t = some .tcb → capAt (L.mem s2) (slotOf t 2) = capAt (L.mem s) (slotOf t 2) ∨
      capV (L.mem s2) (slotOf t 2) = .Null := by
    intro t ht
    have h1 : IsSlot Z.th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by decide⟩, rfl⟩
    by_cases hne : slotOf t 2 = cslotAddr sl
    · exfalso
      rcases hJ.bfs t ht with e | ⟨q0, sz0, r0, m0, e0, a0, v0, e⟩
      · rw [cslot_tcb2, hne] at e; exact hxn e
      · rw [cslot_tcb2, hne] at e
        rw [e] at hal
        have hfr := hal.frame
        simp [isFrame] at hfr
    · left; rw [capAt_capV, capAt_capV, hoth2 _ h1 hne]
  have hUK : UtKept Z.th (L.mem s) (L.mem s2) := fun x hx p' sb fi d h => by
    have e : x ≠ cslotAddr sl := fun e => by rw [e, hz2] at h; cases h
    exact ⟨x, hx, fi, by rw [← hoth2 x hx e]; exact h, Or.inl le_rfl⟩
  have hCK : CoverKept Z.th (L.mem s) (L.mem s2) := by
    intro y hy hp hu
    by_cases e : y = cslotAddr sl
    · subst e
      refine ⟨cslotAddr sl, hy, ?_, ?_, ?_, ?_⟩ <;> rw [hz2]
      · rw [hal.phys]; exact hp
      · rw [hal.isUt']; exact hu
      · exact hal.base
      · exact hal.top
    · exact ⟨y, hy, by rw [hoth2 y hy e]; exact hp, by rw [hoth2 y hy e]; exact hu, by rw [hoth2 y hy e],
        by rw [hoth2 y hy e]⟩
  have hjc : Sched.JCovD (L := L) Z.th H Z.G D Cs s2 :=
    J.jcov_cover hw.1 hM2 hCK hUK (fun q hq => J.deadP_slot hX2 hcn2 hkc hw (J.jcov.dead q hq))
      (J.idleW_keep hX2.fin.1.1.1 (CnStep.of_cnK hcn2).idle (CnStep.of_cnK hcn2).isc)
  -- the untyped caps' facts after: all kept
  have hks : L.ksb s2 = L.ksb s := hw.1
  have hcpu : L.cpu s2 = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s2 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hgp : σ2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn2.1; exact e
  have hDbg : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hutc : ∀ u p' sb fi dev, AbsSlot Z.th u → capAt (L.mem s2) (cslotAddr u) = ok (.Untyped p' sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s2 σ2 Z.G u p' sb fi := by
    intro u p' sb fi dev hu hcap' hdv
    have hne : cslotAddr u ≠ cslotAddr sl := fun e => by
      have := capV_of_capAt hcap'; rw [e, hz2] at this; cases this
    have hcv : capV (L.mem s) (cslotAddr u) = .Untyped p' sb fi dev := by
      rw [← hoth2 _ hu.isSlot hne]; exact capV_of_capAt hcap'
    have U := J.utc u p' sb fi dev hu (by rw [capAt_capV, hcv]) hdv
    have hfi := U.fiLe
    have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p'.val + fi.val ∨ p'.val + 2 ^ sb.val ≤ y.val := by
      intro y hy
      obtain ⟨q, i, hi, rfl⟩ := hy
      obtain ⟨k, hk, hs⟩ := hi.size
      have hv := hi.val hP
      rcases U.free q k hk with e | e <;> omega
    have hnc : (¬ ∃ x, σ2.cdt x = some u) → ¬ ∃ x, σ.cdt x = some u :=
      fun h0 ⟨x, hx⟩ => h0 ⟨x, by rw [hcd x id]; exact hx⟩
    have B := notDev_back (capV_of_capAt hcap') hcv
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free,
      fun g w hal' h1 h2 => ?_, U.sb4,
      U.nostr, U.nsFree, fun h0 => U.ns (hnc h0), 
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
    · rw [hw.mem_eq hal' fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
      exact U.zero (B g) w hal' h1 h2
    · obtain ⟨r1, r3⟩ := U.rst (B g) (hnc h0) hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← hok sl' id]; exact h), by rw [hna, hDbg]; exact r3⟩
  obtain ⟨hJC, R⟩ := jowes_slotD J hX2 hcn2 hkc hw hFI2 hMO hkz hTK hT3 hT2 hDl2 hUK hjc
    (fun sl' h => Or.inl (by rw [← hok sl' id]; exact h)) hutc
  exact ⟨hks, KBack.of_keepCT hkc, J.slot2Fr hkc hR2 hT2, hJC, Ac, Lst, R⟩

set_option maxHeartbeats 4000000 in
/-- `JAtZ.zombieJCoreD` with the dead set existential. -/
theorem JAtZ.zombieJCore (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p zt n : U64} (hxn : capV (L.mem s) (cslotAddr sl) ≠ .Null)
    (hal : CapAlike (.Zombie p zt n) (capV (L.mem s) (cslotAddr sl)))
    {s2 : S} {σ2 : Fl4Spec.State Unit} {V2 : XVs}
    (hsc : Fl4Spec.setCap (Z := Unit) (absCap (.Zombie p zt n)) sl σ = ({((), σ2)}, False))
    (hDS2 : DState (L := L) Z.th s2 σ2 Z.G)
    (hz2 : capV (L.mem s2) (cslotAddr sl) = .Zombie p zt n)
    (hoth2 : ∀ y, IsSlot Z.th y → y ≠ cslotAddr sl → capV (L.mem s2) y = capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv Z.G V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧ IpcFrKeep σ σ2 ∧ JCs (L := L) (Z.mv Z.G V2) s2 σ2 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JRest (L := L) arI (Z.mv Z.G V2) H Cs Ac' Lst' D' s2 σ2 := by
  obtain ⟨h1, h2, hf, h3, Ac', Lst', R⟩ := J.zombieJCoreD hA hxn hal hsc hDS2 hz2 hoth2 hX2 hwS hcn2
  exact ⟨h1, h2, hf, h3, Ac', Lst', D, R⟩

section Spec
open Fl4Spec

/-- **`cap_swap_for_delete` keeps the objects' kinds.** -/
theorem capSwapForDelete_nkz (s1 s2 : CslotPtr) : NKZ (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · exact nkz_bind (nkz_getCap _) (fun _ => nkz_bind (nkz_getCap _) (fun _ => capSwap_nkz _ _ _ _))
  · exact nkz_pure' _

/-- **`cap_swap_for_delete` sets the two slots' original bits only.** -/
theorem capSwapForDelete_orig (s1 s2 : CslotPtr) :
    NO (fun sl => sl = s1 ∨ sl = s2) (capSwapForDelete (Z := Unit) s1 s2) := by
  unfold capSwapForDelete NonDet.when
  split
  · exact no_bind (no_getCap _) (fun _ => no_bind (no_getCap _) (fun _ => capSwap_orig _ _ _ _))
  · exact no_pure' _

end Spec

set_option maxHeartbeats 16000000 in
/-- **The zombie at a slot swapped with its first slot keeps `JAtZ`,
relationally** (module docstring): from the facts of the swap (the spec's
`cap_swap_for_delete`, `DState` after at the ghost tree renamed, the two
slots' caps swapped and the others kept, `XTopAt` after, the slot words'
frame, `CnK`), the kernel-state base, `KBack`, `JCs` and `JRest` after.
The first slot, linked after, misses the regions of the untyped caps without
children: the zombie, a physical cap of the MDB based at it, does (`ut_free`). -/
theorem JAtZ.swapJCoreD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p zt n : U64} (hz : capV (L.mem s) (cslotAddr sl) = .Zombie p zt n)
    (hpx : p ≠ cslotAddr sl)
    {s2 : S} {σ2 : Fl4Spec.State Unit} {V2 : XVs}
    (hsw : Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ2)}, False))
    (hDS2 : DState (L := L) Z.th s2 σ2 (renG Z.G (Equiv.swap p (cslotAddr sl))))
    (hcap : ∀ y, IsSlot Z.th y → capV (L.mem s2) y = if y = cslotAddr sl then capV (L.mem s) p
      else if y = p then capV (L.mem s) (cslotAddr sl) else capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv (renG Z.G (Equiv.swap p (cslotAddr sl))) V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧ IpcFrKeep σ σ2 ∧ JCs (L := L) (Z.mv (renG Z.G (Equiv.swap p (cslotAddr sl))) V2) s2 σ2 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JRest (L := L) arI (Z.mv (renG Z.G (Equiv.swap p (cslotAddr sl))) V2) H Cs Ac' Lst' D s2 σ2 := by
  have hP := J.xtop.rel.1
  obtain ⟨-, ⟨-, -, hM, hC, -⟩, -⟩ := J.xtop.rel
  have hw : P1.WritesIn st s s2 (InSlot Z.th) := hwS.mono fun b hb => slotWd_range hP hb
  obtain ⟨⟨hR2, hV2, hM2, hC2, hI2⟩, hDl2, hFI2⟩ := hDS2
  have hMO := hX2.rel.2.2.2.2.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkc : KeepCT σ σ2 := KeepCT.of_cnK hcn2
  have hmem : ((), σ2) ∈ (Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ).1 := mem_of_single hsw
  have hkz : KSz σ σ2 := capSwapForDelete_nkz _ _ σ ((), σ2) hmem
  have hok : OKeep (fun sl' => sl' = homeSl p zt ∨ sl' = sl) σ σ2 := capSwapForDelete_orig _ _ σ ((), σ2) hmem
  have hxs : IsSlot Z.th (cslotAddr sl) := hA.isSlot
  have hZ : ZOK Z.th p zt n := J.del.zwf _ hxs p zt n hz
  have hHa : cslotAddr (homeSl p zt) = p := home_addr p _
  have hpS : IsSlot Z.th p := by have := (home_abs hZ).isSlot; rwa [hHa] at this
  have hxG : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hxs, _, capAt_capV _ _, by rw [hz]; nofun⟩
  -- the caps after: the swap's renaming
  have he : ∀ y, IsSlot Z.th y → IsSlot Z.th (Equiv.swap p (cslotAddr sl) y) := by
    intro y hy
    by_cases h1 : y = cslotAddr sl
    · rw [h1, Equiv.swap_apply_right]; exact hpS
    · by_cases h2 : y = p
      · rw [h2, Equiv.swap_apply_left]; exact hxs
      · rw [Equiv.swap_apply_of_ne_of_ne h2 h1]; exact hy
  have hcap' : ∀ y, IsSlot Z.th y → capV (L.mem s2) y = capV (L.mem s) (Equiv.swap p (cslotAddr sl) y) := by
    intro y hy
    rw [hcap y hy]
    by_cases h1 : y = cslotAddr sl
    · rw [if_pos h1, h1, Equiv.swap_apply_right]
    · by_cases h2 : y = p
      · rw [if_neg h1, if_pos h2, h2, Equiv.swap_apply_left]
      · rw [if_neg h1, if_neg h2, Equiv.swap_apply_of_ne_of_ne h2 h1]
  have hTK : TypedKept Z.th (L.mem s) (L.mem s2) := fun y hy =>
    Or.inr ⟨_, he y hy, by rw [hcap' y hy]⟩
  have hT3 : ∀ t, Z.th t = some .tcb → capAt (L.mem s2) (slotOf t 3) = capAt (L.mem s) (slotOf t 3) ∨
      capV (L.mem s2) (slotOf t 3) = .Null := by
    intro t ht
    have h1 : IsSlot Z.th (slotOf t 3) := ⟨t, 3, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hx3 : slotOf t 3 ≠ cslotAddr sl := by
      intro e
      rcases hJ.fh t ht with e' | ⟨ep, b0, b1, b2, b3, b4, e'⟩ <;> rw [cslot_tcb3, e, hz] at e' <;> cases e'
    have hp3 : slotOf t 3 ≠ p := by
      intro e
      have hv : (slotOf t 3).val = t.val + 32 * 3 :=
        (show IsSlotAt Z.th t 3 from Or.inr ⟨ht, by decide⟩).val hP
      rw [e] at hv
      obtain ⟨k, hHk⟩ : ∃ k, H p = some k := by
        rcases hZ with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · exact ⟨_, (hJ.tcb p).1 h⟩
        · exact ⟨_, hJ.cnode p _ h⟩
      have hHt : H t = some .tcb := (hJ.tcb t).1 ht
      have hpt : p ≠ t := fun e' => by rw [e'] at hv; omega
      have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
      have h12 : (P1.HKind.tcb).bits = 12 := rfl
      rcases J.kern.heap.disj p k t .tcb hHk hHt hpt with h | h
      · omega
      · rw [h12] at h; omega
    left
    rw [capAt_capV, capAt_capV, hcap' _ h1, Equiv.swap_apply_of_ne_of_ne hp3 hx3]
  have hT2 : ∀ t, Z.th t = some .tcb → capAt (L.mem s2) (slotOf t 2) = capAt (L.mem s) (slotOf t 2) ∨
      capV (L.mem s2) (slotOf t 2) = .Null := by
    intro t ht
    have h1 : IsSlot Z.th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hx2 : slotOf t 2 ≠ cslotAddr sl := by
      intro e
      rcases hJ.bfs t ht with e' | ⟨q0, sz0, r0, m0, e0, a0, v0, e'⟩ <;> rw [cslot_tcb2, e, hz] at e' <;> cases e'
    have hp2 : slotOf t 2 ≠ p := by
      intro e
      have hv : (slotOf t 2).val = t.val + 32 * 2 :=
        (show IsSlotAt Z.th t 2 from Or.inr ⟨ht, by decide⟩).val hP
      rw [e] at hv
      obtain ⟨k, hHk⟩ : ∃ k, H p = some k := by
        rcases hZ with ⟨-, h, -⟩ | ⟨-, h, -⟩
        · exact ⟨_, (hJ.tcb p).1 h⟩
        · exact ⟨_, hJ.cnode p _ h⟩
      have hHt : H t = some .tcb := (hJ.tcb t).1 ht
      have hpt : p ≠ t := fun e' => by rw [e'] at hv; omega
      have : 1 ≤ 2 ^ k.bits := Nat.one_le_two_pow
      have h12 : (P1.HKind.tcb).bits = 12 := rfl
      rcases J.kern.heap.disj p k t .tcb hHk hHt hpt with h | h
      · omega
      · rw [h12] at h; omega
    left
    rw [capAt_capV, capAt_capV, hcap' _ h1, Equiv.swap_apply_of_ne_of_ne hp2 hx2]
  have hUK : UtKept Z.th (L.mem s) (L.mem s2) := fun y hy p' sb fi d h =>
    ⟨_, he y hy, fi, by rw [← hcap' y hy]; exact h, Or.inl le_rfl⟩
  have hCK : CoverKept Z.th (L.mem s) (L.mem s2) := by
    intro y hy hp hu
    have e2 : capV (L.mem s2) (Equiv.swap p (cslotAddr sl) y) = capV (L.mem s) y := by
      rw [hcap' _ (he y hy), Equiv.swap_apply_self]
    exact ⟨_, he y hy, by rw [e2]; exact hp, by rw [e2]; exact hu, by rw [e2], by rw [e2]⟩
  have hjc : Sched.JCovD (L := L) Z.th H (renG Z.G (Equiv.swap p (cslotAddr sl))) D Cs s2 :=
    J.jcov_cover hw.1 hM2 hCK hUK (fun q hq => J.deadP_slot hX2 hcn2 hkc hw (J.jcov.dead q hq))
      (J.idleW_keep hX2.fin.1.1.1 (CnStep.of_cnK hcn2).idle (CnStep.of_cnK hcn2).isc)
  -- the untyped caps' facts after
  have hks : L.ksb s2 = L.ksb s := hw.1
  have hcpu : L.cpu s2 = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s2 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hgp : σ2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn2.1; exact e
  have hDbg : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hutc : ∀ u up sb fi dev, AbsSlot Z.th u → capAt (L.mem s2) (cslotAddr u) = ok (.Untyped up sb fi dev) → dev = false →
      UtCapP3 (L := L) arI Z.th s2 σ2 (renG Z.G (Equiv.swap p (cslotAddr sl))) u up sb fi := by
    intro u up sb fi dev hu hcap2 hdv
    have hcu := capV_of_capAt hcap2
    -- the slot the cap came from
    obtain ⟨u0, hu0, ha0⟩ : ∃ u0, AbsSlot Z.th u0 ∧ cslotAddr u0 = Equiv.swap p (cslotAddr sl) (cslotAddr u) := by
      by_cases h1 : cslotAddr u = cslotAddr sl
      · exact ⟨homeSl p zt, home_abs hZ, by rw [hHa, h1, Equiv.swap_apply_right]⟩
      · by_cases h2 : cslotAddr u = p
        · exact ⟨sl, hA, by rw [h2, Equiv.swap_apply_left]⟩
        · exact ⟨u, hu, by rw [Equiv.swap_apply_of_ne_of_ne h2 h1]⟩
    have hc0 : capV (L.mem s) (cslotAddr u0) = .Untyped up sb fi dev := by
      rw [ha0, ← hcap' _ hu.isSlot]; exact hcu
    have U := J.utc u0 up sb fi dev hu0 (by rw [capAt_capV, hc0]) hdv
    have hfi := U.fiLe
    have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ up.val + fi.val ∨ up.val + 2 ^ sb.val ≤ y.val := by
      intro y hy
      obtain ⟨q, i, hi, rfl⟩ := hy
      obtain ⟨k, hk, hs⟩ := hi.size
      have hv := hi.val hP
      rcases U.free q k hk with e | e <;> omega
    -- a child before is one after (the CDT renamed along the swap)
    have hnc : (¬ ∃ y, σ2.cdt y = some u) → ¬ ∃ y, σ.cdt y = some u0 := by
      rintro h0 ⟨y, hy⟩
      apply h0
      have hyA : AbsSlot Z.th y := (hC.cdt_slot y u0 hy).1
      have h1 : Z.G.par (cslotAddr y) = some (cslotAddr u0) := by rw [← hC.cdt y hyA, hy]; rfl
      have h2 : (renG Z.G (Equiv.swap p (cslotAddr sl))).par (Equiv.swap p (cslotAddr sl) (cslotAddr y)) =
          some (cslotAddr u) := by
        show (Z.G.par ((Equiv.swap p (cslotAddr sl)).symm (Equiv.swap p (cslotAddr sl) (cslotAddr y)))).map
          (Equiv.swap p (cslotAddr sl)) = _
        rw [Equiv.symm_apply_apply, h1, ha0]
        simp
      obtain ⟨y', hy'A, hy'a⟩ := hC2.par_slot _ _ h2
      have h3 := hC2.cdt y' hy'A
      rw [hy'a, h2] at h3
      cases hq : σ2.cdt y' with
      | none => rw [hq] at h3; cases h3
      | some q =>
        rw [hq] at h3
        have hqa : cslotAddr q = cslotAddr u := Option.some.inj h3
        have hqA := (hC2.cdt_slot y' q hq).2
        exact ⟨y', by rw [hq, cslotAddr_inj hP hqA hu hqa]⟩
    -- the first slot misses the region of a childless untyped cap
    have hpOut : (¬ ∃ y, σ.cdt y = some u0) → p.val < up.val ∨ up.val + 2 ^ sb.val ≤ p.val := by
      intro hn
      -- the zombie, a physical cap of the MDB based at `p`, misses the region
      have hu0m : cslotAddr u0 ∈ Z.G.chains.flatten :=
        (hM.members _).2 ⟨hu0.isSlot, _, capAt_capV _ _, by rw [hc0]; nofun⟩
      have hpz : physF (capV (L.mem s) (cslotAddr sl)) = true := by rw [hz]; exact ok_inj (phys_eq _).symm
      have hreg := J.ut.reg _ hxG hpz
      have hbz : baseF (capV (L.mem s) (cslotAddr sl)) = p.val := by
        rw [hz]; unfold baseF; rw [show ptrF (.Zombie p zt n) = p from ok_inj (ptr_eq _).symm]
      have hcov : Covered (L.mem s) Z.G p.val (p.val + 1) :=
        ⟨_, hxG, hpz, by rw [hz]; rfl, by rw [hbz], by omega⟩
      have := ut_free J.ut J.xtop.rel.2.1.2.2.2.2 hu0m hc0 (nodesc_of_cdt hP hC hu0 hn) (Nat.lt_succ_self _) hcov
      omega
    have B : NotDev (L.mem s2) (cslotAddr u) up sb fi → NotDev (L.mem s) (cslotAddr u0) up sb fi := fun g => by
      unfold NotDev at *; rw [hc0]; rw [hcu] at g; exact g
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free,
      fun g w hal' h1 h2 => ?_, U.sb4,
      U.nostr, fun y hy => ?_, fun h0 y hy => ?_, 
      fun g h0 hf0 => ?_, fun g => by rw [hna]; exact U.dwReg (B g), fun g => by rw [hgp]; exact U.gReg (B g)⟩
    · rw [hw.mem_eq hal' fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
      exact U.zero (B g) w hal' h1 h2
    · have := hobj y ((hM2.members y).1 hy).1
      omega
    · have hy0 : Equiv.swap p (cslotAddr sl) y ∈ Z.G.chains.flatten := by
        rw [mem_renG, Equiv.symm_swap] at hy; exact hy
      by_cases hyp : y = p
      · subst hyp; exact hpOut (hnc h0)
      · by_cases hyx : y = cslotAddr sl
        · subst hyx; exact U.ns (hnc h0) _ hxG
        · rw [Equiv.swap_apply_of_ne_of_ne hyp hyx] at hy0; exact U.ns (hnc h0) _ hy0
    · obtain ⟨r1, r3⟩ := U.rst (B g) (hnc h0) hf0
      refine ⟨fun sl' h => ?_, by rw [hna, hDbg]; exact r3⟩
      by_cases hd : sl' = homeSl p zt ∨ sl' = sl
      · rcases hd with rfl | rfl
        · exact AbsSlot.restrict hP U.nostr (home_abs hZ) (by rw [hHa]; exact hpOut (hnc h0))
        · exact AbsSlot.restrict hP U.nostr hA (U.ns (hnc h0) _ hxG)
      · exact r1 sl' (by rw [← hok sl' hd]; exact h)
  obtain ⟨hJC, R⟩ := jowes_slotD J hX2 hcn2 hkc hw hFI2 hMO hkz hTK hT3 hT2 hDl2 hUK hjc
    (fun sl' h => by
      by_cases hd : sl' = homeSl p zt ∨ sl' = sl
      · rcases hd with rfl | rfl
        · exact Or.inr (home_abs hZ)
        · exact Or.inr hA
      · exact Or.inl (by rw [← hok sl' hd]; exact h)) hutc
  exact ⟨hks, KBack.of_keepCT hkc, J.slot2Fr hkc hR2 hT2, hJC, Ac, Lst, R⟩

set_option maxHeartbeats 4000000 in
/-- `JAtZ.swapJCoreD` with the dead set existential. -/
theorem JAtZ.swapJCore (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {sl : Fl4Spec.CslotPtr}
    (hA : AbsSlot Z.th sl) {p zt n : U64} (hz : capV (L.mem s) (cslotAddr sl) = .Zombie p zt n)
    (hpx : p ≠ cslotAddr sl)
    {s2 : S} {σ2 : Fl4Spec.State Unit} {V2 : XVs}
    (hsw : Fl4Spec.capSwapForDelete (Z := Unit) (homeSl p zt) sl σ = ({((), σ2)}, False))
    (hDS2 : DState (L := L) Z.th s2 σ2 (renG Z.G (Equiv.swap p (cslotAddr sl))))
    (hcap : ∀ y, IsSlot Z.th y → capV (L.mem s2) y = if y = cslotAddr sl then capV (L.mem s) p
      else if y = p then capV (L.mem s) (cslotAddr sl) else capV (L.mem s) y)
    (hX2 : XTopAt (L := L) AR (Z.mv (renG Z.G (Equiv.swap p (cslotAddr sl))) V2) s2 a σ2)
    (hwS : P1.WritesIn st s s2 (Sched.SlotWd Z.th)) (hcn2 : Ipc.CnK σ σ2) :
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧ IpcFrKeep σ σ2 ∧ JCs (L := L) (Z.mv (renG Z.G (Equiv.swap p (cslotAddr sl))) V2) s2 σ2 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JRest (L := L) arI (Z.mv (renG Z.G (Equiv.swap p (cslotAddr sl))) V2) H Cs Ac' Lst' D' s2 σ2 := by
  obtain ⟨h1, h2, hf, h3, Ac', Lst', R⟩ := J.swapJCoreD hA hz hpx hsw hDS2 hcap hX2 hwS hcn2
  exact ⟨h1, h2, hf, h3, Ac', Lst', D, R⟩

end

end

end Fl4Proofs.P3
