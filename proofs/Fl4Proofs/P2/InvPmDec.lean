/-
# P2 (line pte, generation 11): `pr`, `dec`, `ra`, `ro` of the PageMap slot, proved

The PageMap slot family (`P2/InvPmLP.lean`) took the pruning fact `pr` [J] and the decline obligations `dec`, `ra`,
`ro` [W] at `Pre := SlJAt ∧ PmQ ∧ GateEp`. Here they are theorems, at the start fact narrowed by the plan's lookup:

* **`PmQF`** `= PmQ ∧ InvLk` (the plan's slot is the slot the `CAP` register names, as invj's / stpost's
  `InvQF`): the glue's `localinv.plan` supplies it (`pmQF_of_plan`, from stpost's `planD_of_plan` /
  `invLk_of_plan`), so the narrowing is satisfiable at every planned entry; `PmPreF` = `SlJAt ∧ PmQF ∧ GateEp`.
  Without the lookup `p.slot ∈ K.slots` is not known, and the cap words at `p.slot` need not be readable.
* **The layout device `KLayoutP.ptU K`**: `K`'s base layout with the PTE words added to its user set (as gen 4's
  `KLayoutP.pteU`). `region` / `own` / `cls` / `ko` do not read `user`, so `IoPre` carries over (`IoPre.ptU`; the
  user clause of `IoLay` holds for the PTE words by the reachability convention's filters, `GateEp.pte`), and
  `IoRS (ptU K) s ⊆ PmRS K s` (`pmRS_of_ptU`, with `K.vcpus = ∅`). An alternative over `PmRS` is one over
  `IoRS (ptU K)` (`alt_ptU`). So the CNode-arm lemmas (stpost / hpzg: `inv_alt_not_acc`, `inv_ra_dec`,
  `inv_dec_guardRS`, `IoPre.lockSlot`, …) apply at `ptU K` unchanged: the words they read are no PTE words.
* `pm_core`: the arm's facts at the entry (the Frame cap at `p.slot`, `p.slot ∈ K.slots`, the label, the slot's
  lock, the seen words `MapW p.slot`); `pm_seen` (the seen words are in `IoRS (ptU K)`, the slot locked:
  `slJAt_slot0`, no premise);
* `invTailPm_eq`, `hil_eq_Pm`: the body is `invBodyPmG` when the label is `X86PageMap` and the cap read at
  `p.slot` after the prefix is a Frame cap;
* **`pm_prune`** (`PmPrune`, was [J] `pr`), **`pm_isProgOn`**, **`pm_dec`** (`PmDecW`, was [W] `dec`), **`pm_ra`**
  (`PmRaW`, was [W] `ra`), **`pm_ro`** (`PmRoW` of `R.invBodyPmG`, was [W] `ro`).

Premises: `hA` (P0 Arch totality) only. No existing statement changes.
-/
import Fl4Proofs.P2.InvPmLP
import Fl4Proofs.P2.InvHuf
import Fl4Proofs.P2.InvOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.OwnMap (KLayout InW region own GateField TimerField)
open Fl4Proofs.P2.E2E (Once ReadOnce StartAt SP)

noncomputable section

/-! ## The narrowed start fact -/

section q
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **The PageMap entry facts with the plan's lookup**: `PmQ ∧ InvLk` (module docstring). -/
def PmQF (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64)
    (s : S) : Prop :=
  PmQ st Cs Ω Sg Ac Locks p K m s ∧ InvLk st p s

/-- The PageMap path's narrowed `Pre`. -/
def PmPreF (st : machine.Store S) [L : LawfulStore st] (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop)
    (p : localinv.Plan) (K : KLayoutP) (m : U64 → U64) (s : S) : Prop :=
  SlJAt (L := L) K.toKLayout s ∧ PmQF st Cs Ω Sg Ac Locks p K m s ∧ GateEp st K s

/-- **`PmQF` from the glue's plan** (satisfiability of the narrowing): what `localinv.plan` returned at the entry
gives `InvPlanD` and `InvLk`. -/
theorem pmQF_of_plan {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP}
    {m : U64 → U64} {s : S} {n : I64} (hp : localinv.plan st s n = ok (some p))
    (hI : IoQ st Cs Ω Sg Ac K.toKLayout m s) (harm : PmArm st s)
    (hlk : ∀ (i : Nat) (x : U64), i < p.n.val → p.locks.val[i]? = some x → Locks s x) :
    PmQF st Cs Ω Sg Ac Locks p K m s :=
  ⟨⟨hI, planD_of_plan hp, harm, hlk⟩, invLk_of_plan hp⟩

end q

/-! ## The layout device: the PTE words as user words -/

/-- `K`'s base layout with the PTE words added to the user set (module docstring). -/
def _root_.Fl4Proofs.P2.OwnMapP.KLayoutP.ptU (K : KLayoutP) : KLayout :=
  { K.toKLayout with user := K.user ∪ K.ptes }

section dev
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {s s' : S}

theorem own_ptU : own K.ptU = own K.toKLayout := rfl
theorem cls_ptU : OwnMap.cls K.ptU = OwnMap.cls K.toKLayout := rfl
theorem ko_ptU : OwnMap.ko K.ptU = OwnMap.ko K.toKLayout := rfl

/-- What the reachability convention says of a PTE word. -/
theorem GateEp.pte (h : GateEp st K s) {e : U64} (he : e ∈ K.ptes) :
    region K.toKLayout e = .none ∧ Aligned e ∧ e ∉ K.user ∧
      ∀ o : U64, o.val < 13568 → e ≠ core.num.U64.wrapping_add K.ksb o := by
  obtain ⟨m1, ⟨-, hp⟩, -⟩ := h
  rw [hp] at he
  exact ⟨he.2.2.1, he.2.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.2⟩

theorem GateEp.nv (h : GateEp st K s) : K.vcpus = ∅ := h.choose_spec.1.1

/-- `IoLay` carries over to `ptU K`. -/
theorem ioLay_ptU (hL : IoLay K.toKLayout) (h : GateEp st K s) : IoLay K.ptU where
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
    rcases hb with hb | hb
    · exact hL.user b hb
    · obtain ⟨hr, -, -, hk⟩ := h.pte hb
      refine ⟨hr, ?_⟩
      rintro ⟨h1, h2⟩
      change K.ksb.val ≤ b.val at h1
      change b.val < K.ksb.val + 13568 at h2
      have kf := hL.ksf.2
      change K.ksb.val + 13568 ≤ 2 ^ 64 at kf
      have hbb : b.val < 2 ^ 64 := b.hBounds
      have hkb : K.ksb.val < 2 ^ 64 := K.ksb.hBounds
      have e1 : (core.num.U64.wrapping_sub b K.ksb).val = b.val - K.ksb.val := by
        rw [core.num.U64.wrapping_sub_val_eq]; simp [U64.size, U64.numBits] <;> omega
      refine hk _ (by rw [e1]; omega) (UScalar.eq_of_val_eq ?_)
      rw [core.num.U64.wrapping_add_val_eq, e1]; simp [U64.size, U64.numBits] <;> omega

/-- **`IoPre` carries over to `ptU K`.** -/
theorem _root_.Fl4Proofs.P2.PathObl.IoPre.ptU (P : IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s) (h : GateEp st K s) :
    IoPre st K.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  ⟨P.bxi, P.csc, P.hcsc, P.run, ioLay_ptU P.lay h, P.kb, P.nc, P.hT, P.hSc, P.curAff, P.cscCore, P.affSc,
    P.tmc, P.walk, P.fin⟩

/-- **`IoRS (ptU K) ⊆ PmRS K`** at a state with the epoch data. -/
theorem pmRS_of_ptU (h : GateEp st K s) {x : U64} (hx : IoRS (st := st) K.ptU Locks s x) :
    PmRS st K Locks s x := by
  have nv := h.nv
  obtain ⟨ha, hu, hr⟩ := hx
  rw [own_ptU] at hr
  exact ⟨ha, fun h' => hu (Or.inl h'), rpermP_of_V (fun hp => hu (Or.inr hp))
    (rpermV_of_own (fun ⟨_, hw⟩ => E2EV.not_inVcpu_empty nv hw) hr)⟩

/-- **An alternative over `PmRS K` is one over `IoRS (ptU K)`.** -/
theorem alt_ptU (h : GateEp st K s)
    (Al : Alt st (PmRS st K Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) s s') :
    Alt st (IoRS (st := st) K.ptU Locks s) (OwnMap.cls K.ptU) (OwnMap.ko K.ptU m0) (· ∈ K.ptU.user) s s' := by
  refine ⟨Al.cpu, Al.ksb, Al.masks, fun x hx => Al.read x (pmRS_of_ptU h hx), fun x _ hu hk => ?_⟩
  rw [cls_ptU]
  by_cases hp : PmRS st K Locks s x
  · rw [Al.read x hp]
  · rw [ko_ptU] at hk
    exact Al.clsEq x hp (fun h' => hu (Or.inl h')) hk

end dev

/-! ## The arm's facts at the entry -/

section core
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
  {s : S}

/-- **The PageMap arm's facts at the entry** from `PmQF`. -/
theorem pm_core (hq : PmQF st Cs Ω Sg Ac Locks p K μ s) :
    ∃ (fp rt asid va : U64) (mp : Bool),
      obj.Slot.cap st p.slot s = ok (.Frame fp .Small rt false mp false asid va) ∧ p.slot ∈ K.slots ∧
      (∀ info, msg.msg_info st s (L.curW s) = ok info →
        info.label = fl4_abi.label.X86PageMap ∧ ¬ info.length < 3#u64) ∧
      (p.slot ≠ 0#u64 → Locks s p.slot) ∧ (∀ x, SeenW p x → MapW p.slot x) := by
  obtain ⟨⟨⟨PE, -⟩, ⟨t, info, ex, et, ei, hpw⟩, harm, hlk⟩, ⟨x, hx, hxs⟩⟩ := hq
  have ht : t = L.curW s := ok_inj_ff (et.symm.trans (cur_thread_ok s))
  subst ht
  obtain ⟨hlbl, -⟩ := harm _ _ (cur_thread_ok s) ei
  rw [hlbl] at hpw
  obtain ⟨fp, rt, asid0, va, root, rasid, mp, x0, e, hcap, -, -, -, -, hHd, -, hSn⟩ := plan_with_mapF hpw
  obtain ⟨C, hroot, hcl, hC⟩ := PE.walk
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
  refine ⟨fp, rt, asid0, va, mp, hcap, ?_, fun info' hi => harm _ info' (cur_thread_ok s) hi,
    fun hd => (fun ⟨j, hj, hy⟩ => hlk j _ hj hy) (hHd hd), ?_⟩
  · rw [← hxs, hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1
  · intro w ⟨i, q, hi, hiM, hidx, hq⟩
    have hM : localinv.MAX_LOCKS.val = 4 := maxLocks_val
    have hiv : i.val < 4 := by have : i.val < localinv.MAX_LOCKS.val := hiM; omega
    have hlen : p.seen.val.length = 4 := by simp
    have hl : i.val < p.seen.length := by simp only [Aeneas.Std.Array.length]; omega
    rw [eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)] at hidx
    have e := ok_inj_ff hidx
    subst e hq
    exact hSn i.val (by omega) hi

variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **The plan's slot words are readable at `ptU K`**: the slot is a capability slot locked by the glue. -/
theorem pm_slotRS (hJ : SlJAt (L := L) K.toKLayout s) (hq : PmQF st Cs Ω Sg Ac Locks p K μ s)
    (P : IoPre st K.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) {o : U64} (ho : o.val < 32) (h8 : o.val % 8 = 0) :
    IoRS (st := st) K.ptU Locks s (core.num.U64.wrapping_add p.slot o) := by
  obtain ⟨-, -, -, -, -, -, hsl, -, hlk, -⟩ := pm_core hq
  have h0 : p.slot ≠ 0#u64 := fun e => slJAt_slot0 hJ (e ▸ hsl)
  exact (P.lockSlot (p := p.slot) hsl (hlk h0) ho h8).1

/-- **The plan's seen words are readable at `ptU K`** (no premise). -/
theorem pm_seen (hJ : SlJAt (L := L) K.toKLayout s) (hq : PmQF st Cs Ω Sg Ac Locks p K μ s)
    (P : IoPre st K.ptU T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ x, SeenW p x → IoRS (st := st) K.ptU Locks s x := by
  intro x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, hSn⟩ := pm_core hq
  rcases hSn x hx with rfl | rfl
  · exact pm_slotRS hJ hq P (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])
  · exact pm_slotRS hJ hq P (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])

end core

/-! ## The body is the pruned one (`pr`) -/

section eqs
variable {S : Type}

/-- **`invTail` is `invTailPmG`** when the label is `X86PageMap` and every cap read at the plan's slot after the
prefix is a Frame cap. -/
theorem invTailPm_eq {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (info : msginfo.MessageInfo) (p : localinv.Plan) (hlbl : info.label = fl4_abi.label.X86PageMap)
    (hcap : ∀ i2 s1 s2 a1 c, obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2 = ok s1 →
      sched.update_timestamp m ar s1 a = ok (s2, a1) → obj.Slot.cap m p.slot s2 = ok c →
      ∃ x1 x2 x3 x4 x5 x6 x7 x8, c = .Frame x1 x2 x3 x4 x5 x6 x7 x8) :
    invTail m ar s a t info p = invTailPmG m ar s a t info p := by
  unfold invTail invTailPmG
  refine bind_guard_congr rfl fun b _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun next _ => ?_
  refine bind_guard_congr rfl fun i2 _ => ?_
  refine bind_guard_congr rfl fun s1 hs1 => ?_
  refine bind_guard_congr rfl fun ⟨s2, a1⟩ hu => ?_
  refine bind_guard_congr rfl fun csc _ => ?_
  refine bind_guard_congr rfl fun i3 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i4 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i5 _ => ?_
  refine bind_guard_congr rfl fun b1 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun b2 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun b3 _ => ?_
  refine ite_congr rfl (fun _ => ?_) (fun _ => rfl)
  refine bind_guard_congr rfl fun buf _ => ?_
  refine bind_guard_congr rfl fun len _ => ?_
  refine bind_guard_congr rfl fun cap hc => ?_
  obtain ⟨x1, x2, x3, x4, x5, x6, x7, x8, rfl⟩ := hcap i2 s1 s2 a1 cap hs1 hu hc
  rw [hlbl, decInv_eq_Pm]
  rfl

/-- **The body is `invBodyPmG`** when the label read is `X86PageMap` and every cap read at the plan's slot after
the prefix is a Frame cap. -/
theorem hil_eq_Pm {A : Type} (m : machine.Store S) (ar : machine.Arch A) (s : S) (a : A) (number : I64)
    (p : localinv.Plan)
    (hlbl : ∀ t info, sched.cur_thread m s = ok t → msg.msg_info m s t = ok info →
      info.label = fl4_abi.label.X86PageMap)
    (hcap : ∀ t i2 s1 s2 a1 c, sched.cur_thread m s = ok t →
      obj.Tcb.set_reg m t s layout.reg.FAULT_IP i2 = ok s1 →
      sched.update_timestamp m ar s1 a = ok (s2, a1) → obj.Slot.cap m p.slot s2 = ok c →
      ∃ x1 x2 x3 x4 x5 x6 x7 x8, c = .Frame x1 x2 x3 x4 x5 x6 x7 x8) :
    syscall.handle_invocation_local m ar s a number p = invBodyPmG m ar s a number p := by
  rw [handle_invocation_local_eq]
  unfold invBodyPmG
  refine bind_guard_congr rfl fun t ht => ?_
  refine bind_guard_congr rfl fun info hi => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine bind_guard_congr rfl fun i _ => ?_
  refine bind_guard_congr rfl fun i1 _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  exact invTailPm_eq m ar s a t info p (hlbl t info ht hi) (hcap t · · · · · ht)

end eqs

section nar
variable {S : Type} {st m : machine.Store S}

/-- On a store narrowing `st`, the message info reads as on `st` or fails. -/
theorem msg_info_nar (N : Narrow st m) (s : S) (t : U64) :
    Nar (msg.msg_info m s t) (msg.msg_info st s t) := by
  unfold msg.msg_info obj.Tcb.reg
  nar_walk N

end nar

section prune
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`pr` of the PageMap slot**: on every store narrowing `st`, from every `PmPreF` state and every alternative of
one, the body is `invBodyPmG` (no premise beyond `hA`). -/
theorem pm_prune (hA : P0.ArchTotal ar) (number : I64) :
    PmPrune st ar number p K Locks μ (PmPreF st Cs Ω Sg Ac Locks p K μ) := by
  intro m N s' hG a
  obtain ⟨s, ⟨hJ, hq, hE⟩, Al0⟩ := hG
  have P := hq.1.1.1.ptU hE
  have Al := alt_ptU hE Al0
  obtain ⟨x1, x2, x3, x4, x5, hcs, hsl, harm, -, -⟩ := pm_core hq
  have G : Ag st (IoRS (st := st) K.ptU Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hN' : NodePlaced st K.toKLayout.heap.tcbs s' (L.cpu s') := by rw [Al.cpu]; exact P.np.ksb Al.ksb
  have hcT' : L.curW s' ∈ K.toKLayout.heap.tcbs := by rw [hcur]; exact P.cT
  -- the cap words at `p.slot` are readable, so the cap at the alternative is the entry's Frame cap
  obtain ⟨h8, hf⟩ := P.lay.slot8 _ hsl
  have r0 : IoRS (st := st) K.ptU Locks s p.slot := by
    have := pm_slotRS hJ hq P (o := 0#u64) (by simp) (by simp)
    rwa [wadd_zero hf] at this
  have r8 := pm_slotRS hJ hq P (o := 8#u64) (by simp) (by simp)
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
theorem pm_isProgOn (hA : P0.ArchTotal ar) (number : I64) :
    IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st (PmPreF st Cs Ω Sg Ac Locks p K μ) (PmRS st K Locks) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout μ) (· ∈ K.user)) (R.invBodyPmG number p) :=
  fun m N s' hG a => (pm_prune hA number m N s' hG a).trans
    (congrFun (congrFun (pm_isProg S number p A ar m) s') a)

/-! ## The declines (`dec`, `ra`, `ro`) -/

/-- **`dec` of the PageMap slot** (`PmDecW`; no premise beyond `hA`). -/
theorem pm_dec (hA : P0.ArchTotal ar) (number : I64) :
    PmDecW st ar number p K Locks μ (PmPreF st Cs Ω Sg Ac Locks p K μ) := by
  intro s a r hE h hr s' r' Al0 h'
  obtain ⟨hJ, hq, hG⟩ := hE
  have P0' := hq.1.1.1
  have P := P0'.ptU hG
  have Al := alt_ptU hG Al0
  have hSeen := pm_seen hJ hq P
  have G : Ag st (IoRS (st := st) K.ptU Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
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
    have hKV := E2EV.regionOKV_of_empty hJ.regionOK hG.nv (K := K.toKLayoutV)
    have hW : PreOK st (mguard st (fun x y => StepOK (ownP K) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout μ) (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) s' (L.curW s') := by
      intro y b v hb _ _
      obtain ⟨ha, hs⟩ := IoDS.safe P0' (hpre b hb)
      rw [L.write_eq]
      exact mguard_write (L.write_eq y b v)
        (stepOKP_of_stepOKV (stepOKV_of_stepOK hKV (stepOK_safe (m0 := μ) hJ.regionOK hJ.ioLayA ha hs)))
    exact handle_inv_dec_m hR hW h' hn

/-- **`ra` of the PageMap slot** (`PmRaW`; no premise beyond `hA`). -/
theorem pm_ra (hA : P0.ArchTotal ar) (number : I64) :
    PmRaW st ar number p K Locks μ (PmPreF st Cs Ω Sg Ac Locks p K μ) := by
  intro s s' a r0 r hE Al0 h0 hr0 h
  obtain ⟨hJ, hq, hG⟩ := hE
  have P := hq.1.1.1.ptU hG
  exact inv_ra_dec hA P (pm_seen hJ hq P) (alt_ptU hG Al0) h0 hr0 h

/-- **`ro` of the PageMap slot** (`PmRoW` of the tree `R.invBodyPmG`; no premise beyond `hA`). -/
theorem pm_ro (hA : P0.ArchTotal ar) (number : I64) :
    PmRoW st ar number p K Locks μ (R.invBodyPmG number p) (PmPreF st Cs Ω Sg Ac Locks p K μ) := by
  intro s s' a r hE hac Al0 h
  have hp := pm_isProgOn (st := st) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p)
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
  have P := hq.1.1.1.ptU hG
  have hg := inv_dec_guardRS hA P (pm_seen hJ hq P) (alt_ptU hG Al0) h0 hr0 h'
  rw [inv_hp hp (Narrow.guard _ _ _) ⟨s, ⟨hJ, hq, hG⟩, Al0⟩ a] at hg
  have hg2 := interp_mono (fun x hx => pmRS_of_ptU hG hx) (fun _ _ => trivial) _ (pm_noZero number p) s' a _ hg
  exact once_of_guardG (fun w hw => hw.2.1) _ (pm_noZero number p) ∅ ∅ s' a _ hg2

end prune

end
end Fl4Proofs.P2.E2EP
