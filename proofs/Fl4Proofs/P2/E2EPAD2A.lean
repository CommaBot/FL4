/-
# P2 (line mmuAD, gen 17): **PageMap in VM epochs, part A** — the layout device, the VM entry fact, the declines

`pmPathsK`'s entry `PmPreG` holds P3's bundle `SlJAt` and the native epoch data `GateEp` (`K.vcpus = ∅`). In a VM
epoch neither is available. This module starts the VM copy of the PageMap path, as vmscope gens 8 / 10 did for
CNodeDelete / delPte:

* **`KLayoutP.uV K`**: `K` with the VCPU data words counted as user words (vlift's `userV`, at `KLayoutP`).
  `ownP`, `cls`, `ko`, `region` do not read `user`, so they are `K`'s. Its `ptU` (`K.uV.ptU`: user words, VCPU data
  words and PTE words as user) is the PageMap read-set layout of a VM epoch: `IoRS K.uV.ptU ⊆ PmRS K`
  (**`pmRS_of_ptUX`**, `rpermV_of_own_nd` off `VData`, `rpermP_of_V` off `K.ptes`), so an alternative over `PmRS K` is
  one over `IoRS K.uV.ptU` (**`alt_ptUX`**). `IoPre` carries over (**`IoPre.ptUX`**: the user clause of `IoLay` for
  VCPU data words by `RegionOKV.none` / `VcpuKsOff`, for PTE words by `RegionOKP.none` and `KsNoE`).
* **`PmGX`** (replaces `GateEp`): the walk fact `WalkP` (E2EPVX10A), `KsNoE (· ∈ K.ptes)`, `InvVF`, `RegionOKP`,
  `UserOKP`. **`PmPreFX`** = `InvLX ∧ PmQF ∧ PmGX` (replaces `PmPreF = SlJAt ∧ PmQF ∧ GateEp`), **`PmPreGX`** =
  `PmPreFX ∧ PmEx ∧ PmRoot` (replaces `PmPreG`). The shapes match the native ones, so the native proofs carry over
  with the device lemmas in place of `IoPre.ptU` / `alt_ptU` / `pmRS_of_ptU` and `InvLX.hz` in place of
  `slJAt_slot0`.
* `pm_slotRSX`, `pm_seenX`; **`pm_pruneX`**, **`pm_isProgOnX`**, **`pm_decX`**, **`pm_raX`**, **`pm_roX`**: the decline
  obligations of the PageMap path at `PmPreFX` (copies of InvPmDec's, no premise beyond `hA`).

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.E2EPAD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout InW region own GateField TimerField)
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)

noncomputable section

/-! ## The layout device -/

/-- `K` with the VCPU data words counted as user words (`userV` at `KLayoutP`). -/
def _root_.Fl4Proofs.P2.OwnMapP.KLayoutP.uV (K : KLayoutP) : KLayoutP :=
  { K with user := {x | x ∈ K.user ∨ VData K.toKLayoutV x} }

section dev
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The VM-epoch data at a PageMap entry** (replaces `GateEp`, module docstring). -/
structure PmGX (K : KLayoutP) (s : S) : Prop where
  /-- the walk fact (E2EPVX10A's `WalkP`, [S] at the start). -/
  walk : WalkP st K s
  ks : KsNoE (· ∈ K.ptes) K.toKLayoutV
  vf : InvVF K
  rk : RegionOKP K
  uk : UserOKP K

variable (st) in
/-- **The PageMap path's VM entry fact** (replaces `PmPreF`). -/
def PmPreFX (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  InvLX st (fun _ => True) K.toKLayout s ∧ PmQF st Cs Ω Sg Ac Locks p K m s ∧ PmGX st K s

variable (st) in
/-- **The PageMap path's VM entry fact with `PmEx` and `PmRoot`** (replaces `PmPreG`). -/
def PmPreGX (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  PmPreFX st Cs Ω Sg Ac Locks p K m s ∧ PmEx st p s ∧ PmRoot st p s

variable {K : KLayoutP} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {s s' : S}

theorem mem_uVptU {x : U64} : x ∈ K.uV.ptU.user ↔ (x ∈ K.user ∨ VData K.toKLayoutV x) ∨ x ∈ K.ptes := Iff.rfl
theorem own_uVptU : own K.uV.ptU = own K.toKLayout := rfl
theorem cls_uVptU : OwnMap.cls K.uV.ptU = OwnMap.cls K.toKLayout := rfl
theorem ko_uVptU : OwnMap.ko K.uV.ptU = OwnMap.ko K.toKLayout := rfl

/-- `IoLay` carries over to `K.uV.ptU`. -/
theorem ioLay_ptUX (hL : IoLay K.toKLayout) (h : PmGX st K s) : IoLay K.uV.ptU where
  node := hL.node
  tcbw := hL.tcbw
  slotw := hL.slotw
  slot8 := hL.slot8
  tslot := hL.tslot
  scw := hL.scw
  ks := hL.ks
  ksf := hL.ksf
  user := by
    intro b hb
    rcases hb with (hb | ⟨v, hv, _⟩) | hb
    · exact hL.user b hb
    · exact ⟨h.rk.base.none v b hv, vcpuKs_ofKo h.vf.ko v b hv⟩
    · refine ⟨h.rk.none b hb, ?_⟩
      rintro ⟨h1, h2⟩
      change K.ksb.val ≤ b.val at h1
      change b.val < K.ksb.val + 13568 at h2
      have kf := hL.ksf.2
      change K.ksb.val + 13568 ≤ 2 ^ 64 at kf
      have hbb : b.val < 2 ^ 64 := b.hBounds
      have hkb : K.ksb.val < 2 ^ 64 := K.ksb.hBounds
      have e1 : (core.num.U64.wrapping_sub b K.ksb).val = b.val - K.ksb.val := by
        rw [core.num.U64.wrapping_sub_val_eq]; simp [U64.size, U64.numBits] <;> omega
      refine h.ks _ (by rw [e1]; omega) ?_
      have : core.num.U64.wrapping_add K.ksb (core.num.U64.wrapping_sub b K.ksb) = b := by
        refine UScalar.eq_of_val_eq ?_
        rw [core.num.U64.wrapping_add_val_eq, e1]; simp [U64.size, U64.numBits] <;> omega
      rw [this]; exact hb

/-- **`IoPre` carries over to `K.uV.ptU`.** -/
theorem _root_.Fl4Proofs.P2.PathObl.IoPre.ptUX (P : IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (h : PmGX st K s) : IoPre st K.uV.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  ⟨P.bxi, P.csc, P.hcsc, P.run, ioLay_ptUX P.lay h, P.kb, P.nc, P.hT, P.hSc, P.curAff, P.cscCore, P.affSc,
    P.tmc, P.walk, P.fin⟩

/-- **`IoRS K.uV.ptU ⊆ PmRS K`** at a VM layout. -/
theorem pmRS_of_ptUX (h : PmGX st K s) {x : U64} (hx : IoRS (st := st) K.uV.ptU Locks s x) :
    PmRS st K Locks s x := by
  obtain ⟨ha, hu, hr⟩ := hx
  exact ⟨ha, fun h' => hu (Or.inl (Or.inl h')), rpermP_of_V (fun hp => hu (Or.inr hp))
    (rpermV_of_own_nd h.rk.base (fun hv => hu (Or.inl (Or.inr hv))) hr)⟩

/-- **An alternative over `PmRS K` is one over `IoRS K.uV.ptU`.** -/
theorem alt_ptUX (h : PmGX st K s)
    (Al : Alt st (PmRS st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) s s') :
    Alt st (IoRS (st := st) K.uV.ptU Locks s) (OwnMap.cls K.uV.ptU) (OwnMap.ko K.uV.ptU m0) (· ∈ K.uV.ptU.user)
      s s' := by
  refine ⟨Al.cpu, Al.ksb, Al.masks, fun x hx => Al.read x (pmRS_of_ptUX h hx), fun x _ hu hk => ?_⟩
  rw [cls_uVptU]
  by_cases hp : PmRS st K Locks s x
  · rw [Al.read x hp]
  · rw [ko_uVptU] at hk
    exact Al.clsEq x hp (fun h' => hu (Or.inl (Or.inl h'))) hk

end dev

/-! ## The arm's slot words at a VM entry -/

section core
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
  {s : S} {F : S → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **The plan's slot words are readable at `K.uV.ptU`** (`pm_slotRS` with `InvLX.hz`). -/
theorem pm_slotRSX (hJ : InvLX st F K.toKLayout s) (hq : PmQF st Cs Ω Sg Ac Locks p K μ s)
    (P : IoPre st K.uV.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) {o : U64} (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K.uV.ptU Locks s (core.num.U64.wrapping_add p.slot o) := by
  obtain ⟨-, -, -, -, -, -, hsl, -, hlk, -⟩ := pm_core hq
  have h0 : p.slot ≠ 0#u64 := fun e => hJ.hz (e ▸ hsl)
  exact (P.lockSlot (p := p.slot) hsl (hlk h0) ho h8).1

/-- **The plan's seen words are readable at `K.uV.ptU`.** -/
theorem pm_seenX (hJ : InvLX st F K.toKLayout s) (hq : PmQF st Cs Ω Sg Ac Locks p K μ s)
    (P : IoPre st K.uV.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ x, SeenW p x → IoRS (st := st) K.uV.ptU Locks s x := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, hSn⟩ := pm_core hq
  rcases hSn x hx with rfl | rfl
  · exact pm_slotRSX hJ hq P (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])
  · exact pm_slotRSX hJ hq P (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])

end core

/-! ## The declines at a VM entry (InvPmDec's, at `PmPreFX`) -/

section pruneX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`pr` of the PageMap slot**: on every store narrowing `st`, from every `PmPreF` state and every alternative of
one, the body is `invBodyPmG` (no premise beyond `hA`). -/
theorem pm_pruneX (hA : P0.ArchTotal ar) (number : I64) :
    PmPrune st ar number p K Locks μ (PmPreFX st Cs Ω Sg Ac Locks p K μ) := by
  intro m N s' hG a
  obtain ⟨s, ⟨hJ, hq, hE⟩, Al0⟩ := hG
  have P := hq.1.1.1.ptUX hE
  have Al := alt_ptUX hE Al0
  obtain ⟨x1, x2, x3, x4, x5, hcs, hsl, harm, -, -⟩ := pm_core hq
  have G : Ag st (IoRS (st := st) K.uV.ptU Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hN' : NodePlaced st K.toKLayout.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact P.np.ksb Al.ksb
  have hcT' : L.curW s' ∈ K.toKLayout.heap.tcbs := by rw [hcur]; exact P.cT
  -- the cap words at `p.slot` are readable, so the cap at the alternative is the entry's Frame cap
  obtain ⟨h8, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.uV.ptU Locks s p.slot := by
    have := pm_slotRSX hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRSX hJ hq P (o := 8#u64) (by simp) (by simp)
  have hcs' : obj.Slot.cap st p.slot s' = ok (.Frame x1 .Small x2 false x5 false x3 x4) := by
    rw [← hcs]
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, Al.read _ r0, Al.read _ r8]
  have hv : (core.num.U64.wrapping_add p.slot 8#u64).val = p.slot.val + 8 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have et : ∀ t, sched.cur_thread m s' = ok t → t = L.curW s' := fun t ht => by
    have := (cur_thread_nar N s').ok_eq ht
    rw [cur_thread_ok] at this
    exact (ok_inj_ff this).symm
  refine hil_eq_Pm m ar s' a number p (fun t info ht hi => ?_) fun t i2 s1 s2 a1 c ht hs1 hu hc => ?_
  · obtain rfl := et t ht
    have hi' := (msg_info_nar N s' _).ok_eq hi
    have emi : msg.msg_info st s (L.curW s) = ok info := by
      unfold msg.msg_info at hi' ⊢
      rw [reg_ok] at hi' ⊢
      rw [hcur, G.m _ (P.reg (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1] at hi'
      exact hi'
    exact (harm info emi).1
  obtain rfl := et t ht
  have es1 := (set_reg_nar N _ s' _ i2).ok_eq hs1
  have eu := (update_timestamp_nar N ar s1 a).ok_eq hu
  have ec := (slot_cap_nar N _ s2).ok_eq hc
  have w := prefix_writes ar hA P.tp hN' hcT' es1 eu
  have np : ∀ b, InW p.slot 32 b → Aligned b → L.mem s2 b = L.mem s' b := by
    intro b hb ha
    obtain ⟨p1, p2, p3⟩ := prefix_slot P hsl hb
    refine w.2.2 _ ha ?_
    rintro (⟨K', hK', e⟩ | e | e)
    · obtain ⟨k, hk, e2⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
      have ek : K' = k := UScalar.eq_of_val_eq (by rw [hK', hk]; simp [layout.reg.FAULT_IP])
      exact p1 (by rw [e2, e, hcur, ek])
    · exact p2 (e.trans (G.node _))
    · exact p3 (e.trans (G.node _))
  have sk : obj.Slot.cap st p.slot s2 = obj.Slot.cap st p.slot s' := by
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, np p.slot ⟨le_refl _, by omega⟩ h8,
      np _ ⟨by omega, by omega⟩ (by unfold Aligned; omega)]
  rw [sk, hcs'] at ec
  exact ⟨_, _, _, _, _, _, _, _, (ok_inj_ff ec).symm⟩

/-- **The relativised program premise of the PageMap path**: the tree `R.invBodyPmG` (no premise beyond `hA`). -/
theorem pm_isProgOnX (hA : P0.ArchTotal ar) (number : I64) :
    IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PmPreFX st Cs Ω Sg Ac Locks p K μ) (PmRS st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout μ) (· ∈ K.user)) (R.invBodyPmG number p) :=
  fun m N s' hG a => (pm_pruneX hA number m N s' hG a).trans
    (congrFun (congrFun (pm_isProg S number p A ar m) s') a)

/-! ## The declines (`dec`, `ra`, `ro`) -/

/-- **`dec` of the PageMap slot** (`PmDecW`; no premise beyond `hA`). -/
theorem pm_decX (hA : P0.ArchTotal ar) (number : I64) :
    PmDecW st ar number p K Locks μ (PmPreFX st Cs Ω Sg Ac Locks p K μ) := by
  intro s a r hE h hr s' r' Al0 h'
  obtain ⟨hJ, hq, hG⟩ := hE
  have P0' := hq.1.1.1
  have P := P0'.ptUX hG
  have Al := alt_ptUX hG Al0
  have hSeen := pm_seenX hJ hq P
  have G : Ag st (IoRS (st := st) K.uV.ptU Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hpre : ∀ b, (b = regA (L.curW s') layout.reg.FAULT_IP ∨
      b = L.nodeAt s' (L.cpu s') layout.node.CUR_TIME ∨ b = L.nodeAt s' (L.cpu s') layout.node.CONSUMED) →
      IoDS (st := st) s b := by
    intro b hb
    rw [hcur, G.node, G.node] at hb
    exact hb
  have hn : r'.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r'
    intro hb
    change b = true at hb
    subst hb
    exact inv_alt_not_acc hA P hSeen Al h hr h'
  refine ⟨hn, ?_, ?_⟩
  · exact handle_inv_dec_m ⟨fun _ _ => guard_read trivial, fun _ _ => guard_read_pair trivial trivial,
      fun _ => rfl, fun _ => rfl⟩ (fun y b v hb _ _ => guard_write (hpre b hb)) h' hn
  · have hR : RdEq st (mguard st (fun x y => StepOK (ownP K) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout μ) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
    have hKV := hG.rk.base
    have hW : PreOK st (mguard st (fun x y => StepOK (ownP K) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout μ) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) s' (L.curW s') := by
      intro y b v hb _ _
      obtain ⟨ha, hs⟩ := IoDS.safe P0' (hpre b hb)
      rw [L.write_eq]
      exact mguard_write (L.write_eq y b v)
        (stepOKP_of_stepOKV (stepOKV_of_stepOK hKV (stepOK_safe (m0 := μ) hJ.regionOK hJ.ioLayA ha hs)))
    exact handle_inv_dec_m hR hW h' hn

/-- **`ra` of the PageMap slot** (`PmRaW`; no premise beyond `hA`). -/
theorem pm_raX (hA : P0.ArchTotal ar) (number : I64) :
    PmRaW st ar number p K Locks μ (PmPreFX st Cs Ω Sg Ac Locks p K μ) := by
  intro s s' a r0 r hE Al0 h0 hr0 h
  obtain ⟨hJ, hq, hG⟩ := hE
  have P := hq.1.1.1.ptUX hG
  exact inv_ra_dec hA P (pm_seenX hJ hq P) (alt_ptUX hG Al0) h0 hr0 h

/-- **`ro` of the PageMap slot** (`PmRoW` of the tree `R.invBodyPmG`; no premise beyond `hA`). -/
theorem pm_roX (hA : P0.ArchTotal ar) (number : I64) :
    PmRoW st ar number p K Locks μ (R.invBodyPmG number p) (PmPreFX st Cs Ω Sg Ac Locks p K μ) := by
  intro s s' a r hE hac Al0 h
  have hp := pm_isProgOnX (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p)
    (K := K) (μ := μ) hA number
  obtain ⟨r0, h0⟩ := inv_total (st := st) hA number p s a
  have hr0 : r0.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r0
    intro e
    change b = true at e
    subst e
    exact hac ⟨z, c, h0⟩
  have h' : syscall.handle_invocation_local st ar s' a number p = ok r := by
    rw [inv_hp hp (Narrow.self st) ⟨s, hE, Al0⟩ a]; exact h
  obtain ⟨hJ, hq, hG⟩ := hE
  have P := hq.1.1.1.ptUX hG
  have hg := inv_dec_guardRS hA P (pm_seenX hJ hq P) (alt_ptUX hG Al0) h0 hr0 h'
  rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, ⟨hJ, hq, hG⟩, Al0⟩ a] at hg
  have hg2 := interp_mono (fun x hx => pmRS_of_ptUX hG hx) (fun _ _ => trivial) _ (pm_noZero number p) s' a _ hg
  exact once_of_guardG (fun w hw => hw.2.1) _ (pm_noZero number p) ∅ ∅ s' a _ hg2

end pruneX

end
end Fl4Proofs.P2.E2EP
