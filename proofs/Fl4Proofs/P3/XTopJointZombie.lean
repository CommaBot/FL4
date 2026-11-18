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
  refine ⟨fun lo hi hlh h1 h2 => ?_, fun z hz h1 h2 => ?_⟩
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
  · exfalso
    have hne : L.cscW s ≠ q := fun e => by
      rw [e, hHq] at hz; exact hk z (Option.some.inj hz)
    have : 1 ≤ 2 ^ (P1.HKind.sc z).bits := Nat.one_le_two_pow
    rcases hout _ _ hz hne with h | h <;> omega

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
    L.ksb s2 = L.ksb s ∧ KBack σ σ2 ∧ JCs (L := L) (Z.mv Z.G V2) s2 σ2 ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JRest (L := L) arI (Z.mv Z.G V2) H Cs Ac' Lst' D' s2 σ2 := by
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
  have hUK : UtKept Z.th (L.mem s) (L.mem s2) := fun x hx p' sb fi d h => by
    have e : x ≠ cslotAddr sl := fun e => by rw [e, hz2] at h; cases h
    exact ⟨x, hx, fi, d, by rw [← hoth2 x hx e]; exact h, Or.inl le_rfl⟩
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
    J.jcov_cover hw.1 hM2 hCK hUK fun q hq => J.deadP_slot hX2 hcn2 hkc hw (J.jcov.dead q hq)
  -- the untyped caps' facts after: all kept
  have hks : L.ksb s2 = L.ksb s := hw.1
  have hcpu : L.cpu s2 = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s2 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  have hgp : σ2.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := by
    have e := congrArg (fun z => z.archState.x64GlobalPml4) hcn2.1; exact e
  have hDbg : L.mem s2 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun ⟨x, hx, h1, h2⟩ => J.kern.dwObj x hx ⟨h1, h2⟩
  have hutc : ∀ u p' sb fi dev, AbsSlot Z.th u → capAt (L.mem s2) (cslotAddr u) = ok (.Untyped p' sb fi dev) →
      UtCapP3 (L := L) arI Z.th s2 σ2 Z.G u p' sb fi := by
    intro u p' sb fi dev hu hcap'
    have hne : cslotAddr u ≠ cslotAddr sl := fun e => by
      have := capV_of_capAt hcap'; rw [e, hz2] at this; cases this
    have hcv : capV (L.mem s) (cslotAddr u) = .Untyped p' sb fi dev := by
      rw [← hoth2 _ hu.isSlot hne]; exact capV_of_capAt hcap'
    have U := J.utc u p' sb fi dev hu (by rw [capAt_capV, hcv])
    have hfi := U.fiLe
    have hobj : ∀ y, IsSlot Z.th y → y.val + 32 ≤ p'.val + fi.val ∨ p'.val + 2 ^ sb.val ≤ y.val := by
      intro y hy
      obtain ⟨q, i, hi, rfl⟩ := hy
      obtain ⟨k, hk, hs⟩ := hi.size
      have hv := hi.val hP
      rcases U.free q k hk with e | e <;> omega
    have hnc : (¬ ∃ x, σ2.cdt x = some u) → ¬ ∃ x, σ.cdt x = some u :=
      fun h0 ⟨x, hx⟩ => h0 ⟨x, by rw [hcd x id]; exact hx⟩
    refine ⟨U.pal, U.pfit, U.fiLe, U.high, by rw [hcpu, hna]; exact U.actZ, U.free, fun w hal' h1 h2 => ?_, U.sb4,
      U.nostr, U.nsFree, fun h0 => U.ns (hnc h0), fun k0 v0 => by simpa only [hna] using U.pp k0 v0,
      fun h0 hf0 => ?_, by rw [hna]; exact U.dwReg, by rw [hgp]; exact U.gReg⟩
    · rw [hw.mem_eq hal' fun ⟨y, hy, h1', h2'⟩ => by rcases hobj y hy with e | e <;> omega]
      exact U.zero w hal' h1 h2
    · obtain ⟨r1, r2, r3⟩ := U.rst (hnc h0) hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← hok sl' id]; exact h), r2, by rw [hna, hDbg]; exact r3⟩
  obtain ⟨hJC, R⟩ := jowes_slotD J hX2 hcn2 hkc hw hFI2 hMO hkz hTK hT3 hDl2 hUK hjc J.kern.cscLive
    (fun sl' h => Or.inl (by rw [← hok sl' id]; exact h)) hutc
  exact ⟨hks, KBack.of_keepCT hkc, hJC, Ac, Lst, D, R⟩

end

end

end Fl4Proofs.P3
