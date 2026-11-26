/-
# P2 (line vmscope, gen 8): the invocation slots in VM epochs — `serializable_fl4_localVX8` (draft)
-/
import Fl4Proofs.P2.E2EPVX7
open Aeneas Aeneas.Std Result

/-! ## Part 1: the invocation paths' entry facts without a P3 bundle (`PathObl`) -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section lx
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **Reachability by aligned user-word writes**: `s'` is `s` after finitely many writes of aligned words of
`K.user`. -/
inductive UReach (K : KLayout) : S → S → Prop
  | refl (s : S) : UReach K s s
  | wr {s s' : S} {b : U64} (v : U64) : b ∈ K.user → Aligned b → UReach K (L.wr s b v) s' → UReach K s s'

variable (st) in
/-- **The kernel-word facts the invocation paths read from P3's bundle** (natively `slJAt_cdt`, `invBufJ8_of`,
`invBufSJ8_of`, `invVsJ_of`): the CDT neighbours of a capability slot are capability slots, the caller's receive /
send IPC-buffer words are aligned user words, a mapped small frame cap's walk is a kernel-word walk. -/
structure InvLXS (K : KLayout) (s : S) : Prop where
  /-- natively `slJAt_cdt` -/
  cdt : ∀ sl, sl ∈ K.slots →
    (L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add sl layout.cte.PREV) ∈ K.slots) ∧
    (∀ nx, obj.Slot.next st sl s = ok nx → nx ≠ 0#u64 → nx ∈ K.slots)
  /-- natively `invBufJ8_of` -/
  buf8 : InvBufJ8 st K s
  /-- natively `invBufSJ8_of` -/
  bufS8 : InvBufSJ8 st K s
  /-- natively `invVsJ_of` -/
  vs : ∀ sl fp rt asid va, sl ∈ K.slots →
    obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
    va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧ VsRd st K s asid va

variable (st) in
/-- **The invocation paths' bundle replacement** (module docstring): the layout facts P3's bundle gives
(`SlJAt.regionOK` / `userOK` / `ioLayA`, `UserLayX.ofSlJAt`, `slJAt_slot0`) and, at every state reached by aligned
user-word writes, `InvLXS` and the caller's entry fact `F`. -/
structure InvLX (F : S → Prop) (K : KLayout) (s : S) : Prop where
  regionOK : RegionOK K
  userOK : E2E.UserOK K
  ioLayA : IoLayA K
  ul : Fl4Proofs.P2.E2EP.UserLayX L K
  hz : (0#u64) ∉ K.slots
  cl : ∀ s', UReach (L := L) K s s' → InvLXS st K s' ∧ F s'

variable {F : S → Prop} {K : KLayout} {s : S}

theorem InvLX.here (h : InvLX st F K s) : InvLXS st K s ∧ F s := h.cl s (.refl s)

theorem InvLX.wr (h : InvLX st F K s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    InvLX st F K (L.wr s b v) :=
  ⟨h.regionOK, h.userOK, h.ioLayA, h.ul, h.hz, fun s' hr => h.cl s' (.wr v hb hba hr)⟩

theorem InvLX.mono {F' : S → Prop} (h : InvLX st F K s) (hF : ∀ s, F s → F' s) : InvLX st F' K s :=
  ⟨h.regionOK, h.userOK, h.ioLayA, h.ul, h.hz, fun s' hr => ⟨(h.cl s' hr).1, hF _ (h.cl s' hr).2⟩⟩

theorem InvLX.buf8 (h : InvLX st F K s) : InvBufJ8 st K s := h.here.1.buf8

theorem InvLX.bufS8 (h : InvLX st F K s) : InvBufSJ8 st K s := h.here.1.bufS8

/-- `hz_of` for `InvLX`. -/
theorem hzX_of : ∀ (K : KLayout) (s : S), InvLX st F K s → (0#u64) ∉ K.slots := fun _ _ h => h.hz

/-- `invCdtJ_of` for `InvLX`. -/
theorem invCdtJX_of {P : S → Prop} (hP : ∀ s, P s → InvLX st F K s) : InvCdtJ st K P :=
  fun s sl hs hsl => (hP s hs).here.1.cdt sl hsl

/-- `invVsJ_of` for `InvLX`. -/
theorem invVsJX_of {P : S → Prop} (hP : ∀ s, P s → InvLX st F K s) : InvVsJ st K P :=
  fun s sl fp rt asid va hs hsl hc ha => (hP s hs).here.1.vs sl fp rt asid va hsl hc ha

/-- `curW` survives an aligned user-word write (`curW_wrX` for `K.user`). -/
theorem curW_wrI (ul : Fl4Proofs.P2.E2EP.UserLayX L K) {T : Set U64} (hN : NodePlaced st T s (L.cpu s))
    (hk : L.ksb s = K.ksb) (hc : (L.cpu s).val < 64) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    L.curW (L.wr s b v) = L.curW s := by
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  have h0 := curth_val
  unfold LawfulStore.curW
  rw [nodeAt_wr, LawfulStore.cpu_wr]
  refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
  have h := ul.unode b hb (L.cpu s) hc s hk
  rw [e] at h
  omega

/-- **`IoRS` / `IoWS` / `IoDS` survive a user write** at an `InvLX ∧ IoPre` state (`SlJAt.ioRWDS_wrSt` without the
bundle). -/
theorem ioRWDS_wrI {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}
    (B : InvLX st F K s) (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64}
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) (hl : Locks (L.wr s b v) = Locks s) :
    IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
      IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
    E2E.ownDep B.regionOK B.userOK _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have h0 := P.bxi.1.choose_spec.choose_spec
  have hN := h0.nodes _ h0.cur
  have hc : (L.cpu s).val < 64 := Nat.lt_of_lt_of_le P.nc B.ul.nc
  have ecur : L.curW (L.wr s b v) = L.curW s := curW_wrI B.ul hN P.kb.symm hc hb hba v
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_wr]

/-- **`huf` of the invocation paths at `InvLX F ∧ Q`** (`F` gives `Q`, `Q` gives `IoPre`; the locks by `hlk` [P]). -/
theorem hufX {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}
    {Q : S → Prop} (hQP : ∀ s, Q s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hF : ∀ s, F s → Q s)
    (hlk : ∀ s b v, InvLX st F K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ s b v, (InvLX st F K s ∧ Q s) → b ∈ K.user → Aligned b →
      (InvLX st F K (L.wr s b v) ∧ Q (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v h hb hba
  have h' := h.1.wr hb hba v
  have el := hlk s b v h.1 hb hba
  exact ⟨⟨h', hF _ h'.here.2⟩, el, ioRWDS_wrI h.1 (hQP s h.2) hb hba v el⟩

end lx

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {F : S → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan}

/-- `invSeen_of` at `InvLX` states (`hz` from `InvLX.hz`). -/
theorem invSeenX_of :
    ∀ K μ s, InvLX st F K s → InvQF st Cs Ω Sg Ac Locks p K μ s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x := by
  intro K μ s hJ hq x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, -, -, -, -, -, -, -, hdK, -, hLd, -, -, hSn, -⟩ :=
    del_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hJ.hz (e ▸ hdK)
  obtain ⟨o, ho, rfl⟩ := hSn x hx
  have hov : o.val < 32 ∧ o.val % 8 = 0 := by
    rcases ho with rfl | rfl | rfl | rfl <;> simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
  exact (PE.lockSlot hdK (hLd hd0) hov.1 hov.2).1

/-- `invPs_of` at `InvLX` states. -/
theorem invPsX_of :
    ∀ K μ s, InvLX st F K s → InvQF st Cs Ω Sg Ac Locks p K μ s →
      IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  intro K μ s _ hq
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcap, hsK, -⟩ := del_core hq
  exact PE.slot hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

/-- `invSlotCNK_of` at `InvLX` states (`Q := InvQF`). -/
theorem invSlotCNX_of (K : KLayout) (m : U64 → U64) :
    InvSlotCN st K p (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) :=
  fun _ h => invQ_slotCN h.2.1 h.2.2

/-- `cmPs_ofW` at `InvLX` states. -/
theorem cmPsX_ofW :
    ∀ K μ s, InvLX st F K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s →
      IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  intro K μ s _ hq
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_coreW hq
  exact PE.slot hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

/-- `cmSeen_ofW` at `InvLX` states. -/
theorem cmSeenX_ofW :
    ∀ K μ s, InvLX st F K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → ∀ x, SeenW p x → IoRS (st := st) K Locks s x := by
  intro K μ s hJ hq x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hdK, -, hLd, hsK, -, hLs, -, hSn⟩ := cm_coreW hq
  have hd0 : dest ≠ 0#u64 := fun e => hJ.hz (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hJ.hz (e ▸ hsK)
  rcases hSn x hx with rfl | rfl | rfl | rfl
  · exact (PE.lockSlot hdK (hLd hd0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])).1

/-- `cmSC_ofZ` at `InvLX` states. -/
theorem cmSCX_ofZ : ∀ (K : KLayout) (μ : U64 → U64),
    InvSlotCN st K p (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) := by
  intro K μ s h
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_coreW h.2
  exact ⟨hsK, cp, cr, cg, cgb, hcap⟩

end ent

section arm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {F : S → Prop}

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (stpost gen 14) **`InvBlkUW2` for the uncut CNodeDelete arm** at `Pre := SlJAt K ∧ InvQF`: `length ≥ 2` by
`delAcc` / `delFin` (the `IoRS` / `IoWS` words are user-word-set words), `length < 2` by `truncAcc8` / `truncFin8`;
from [J] `hvs`, [J] `hcdt`, [J] `hz`, [J] `hbuf`. -/
theorem invBlkUW2_of8X {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, InvLX st F K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, InvLX st F K s → InvQF st Cs Ω Sg Ac Locks p K μ s → InvBufJ8 (st := st) K s) :
    InvBlkUW2 st ar p K Locks (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAcc8 (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) (PE.ioWr.mono (fun _ h => ioWS_cm h))
      (fun _ h => ⟨h.1, Or.inl h.2⟩) hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
        (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
    obtain ⟨h1, h2⟩ := truncFin8 (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (PE.ioWr.mono (fun _ h => ioWS_cm h)) (SWr.of_W (ioWS_cm PE.stw.2)) hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEnt_of (P := fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
      (hz s hE.1)
    haveI : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
        (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
    obtain ⟨hdec, hrep⟩ := delAcc (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (PE.ioWr.mono (fun _ h => ioWS_cm h)) (fun _ h => ioWS_cm h) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := delFin (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
      (PE.ioWr.mono (fun _ h => ioWS_cm h)) (ioWS_cm PE.stw.2) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (stpost gen 14) **`InvBlkGdUW2` for the uncut CNodeDelete arm** (as `invBlkUW2_of8X`, on
`gd st (InvCMRS s) (PWs …)`: `delAcc2` / `delFin2`, `truncAcc8` / `truncFin8`; a user word is an aligned word deciding
no owner, so `PW` allows its write). -/
theorem invBlkGdUW2_of8X {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, InvLX st F K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, InvLX st F K s → InvQF st Cs Ω Sg Ac Locks p K μ s → InvBufJ8 (st := st) K s) :
    InvBlkGdUW2 st ar p K Locks (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      SWr (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st (L.curW s) v :=
    fun v hv X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run hv))
  have hWu : ∀ b, UserW K b → WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) b :=
    fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAcc8 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE
      (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) hW hWu hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
    obtain ⟨h1, h2⟩ := truncFin8 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE
      hW (hst _ (Or.inr rfl)) hcs hsK (hbuf s hE.1 hqf) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have E := delEnt_of (P := fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
      (hz s hE.1)
    haveI : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
        (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
    have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
        (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) →
        WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
      intro q o hq _ ho h8 h8' _
      obtain ⟨q8, qf⟩ := PE.lay.slot8 q hq
      have hv := slot_word_val qf ho
      have hr := PE.lay.slotw q hq _ (slot_inW qf ho)
      have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
        have := congrArg UScalar.val e; rw [hv] at this; omega
      have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
      exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
    have hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K q → NullOrFrame (L.mem s q) →
        ∀ x, (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))).write x q 0#u64 = st.write x q 0#u64 :=
      fun q hq hl hT hn x => OwnMap.gds_write_cap0 hq hT hl hn OwnMap.nof_zero
    obtain ⟨hdec, hrep⟩ := delAcc2 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW hwS hw0 hst E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := delFin2 (gS := (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW (hst _ (Or.inr rfl)) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (stpost gen 13) **`InvBlkW2` for the CNodeDelete-no-PTE arm** at `Pre := SlJAt K ∧ InvQL`: `delAcc` (the decode
and the reply on the guarded store) and `delFin` (reply `Ok ()`, `FinOK`), from the entry facts `DelEnt`
(`delEnt_of`: [J] `hvs`, [J] `hcdt`, [J] `hz`). -/
theorem invBlkW2_ofX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hvs : InvVsJ st K (fun s => InvLX st F K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s))
    (hcdt : InvCdtJ st K (fun s => InvLX st F K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, InvLX st F K s → (0#u64) ∉ K.slots) :
    InvBlkW2 st ar p K Locks (fun s => InvLX st F K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hl hcap y hy
  have hqf := hE.2.1
  have PE := hqf.1.1.1
  have E := delEnt_of (P := fun s => InvLX st F K s ∧ InvQL st Cs Ω Sg Ac Locks p K μ s) hE hqf hvs hcdt
    (hz s hE.1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hsK, -⟩ := del_core hqf
  have hlbl := (hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  have hlen := len_ge2 (hE.2.2 (L.curW s) info (cur_thread_ok s) emi) hl
  rw [hlbl] at hy ⊢
  obtain ⟨hdec, hrep⟩ := delAcc (gS := guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hA PE
    PE.ioWr (fun _ h => h) E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  obtain ⟨h1, h2⟩ := delFin (gS := guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hA PE
    PE.ioWr PE.stw.2 E hsK hlen
    (fun sl fp rt asid va hsl hc hA => hvs s sl fp rt asid va hE hsl hc hA) C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (slhuf gen 14; gen 12's `invCMBlkUW3_of8` without `hnul`) **The Copy / Mint decode block on `guard st (InvCMRS s) (InvCMWS s)`** at `Pre := SlJAt K ∧
InvQCMW`, from [J] `hcdt`, `hz`, `hbuf`, `hbufS` (the target's zero word from the plan, `cmDestZ_of`). -/
theorem invCMBlkUW3_ofZX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hcdt : InvCdtJ st K (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, InvLX st F K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, InvLX st F K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufJ8 st K s)
    (hbufS : ∀ s, InvLX st F K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufSJ8 st K s)
:
    InvBlkUW3 st ar p K Locks (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hb hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_ofW (P := fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) hE hqf hcdt
    (hz s hE.1)
  have hsl := cmSl_ofW hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    hbufS s hE.1 hqf buf (by rw [← lib_prefix hA PE C false]; exact hb)
  obtain ⟨hdec, hrep⟩ := cmAccGZ hA PE E hsl (cmDestZ_of hqf) hbC (hbuf s hE.1 hqf) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  have : GRd (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) st
      (IoRS (st := st) K Locks s) := grd_sub (fun _ hy => ioRS_cm hy)
  obtain ⟨h1, h2⟩ := cmFin8 (gS := (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s))) hA PE
    (PE.ioWr.mono (fun _ h => ioWS_cm h)) (SWr.of_W (ioWS_cm PE.stw.2)) E hsl (hbuf s hE.1 hqf) hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (slhuf gen 14; as `invCMBlkGdUW3_of8`) **The Copy / Mint decode block on `gd st (InvCMRS s) (PWs …)`** (for `move`), as
`invCMBlkUW3_ofZX`. -/
theorem invCMBlkGdUW3_ofZX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
    (hcdt : InvCdtJ st K (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s))
    (hz : ∀ s, InvLX st F K s → (0#u64) ∉ K.slots)
    (hbuf : ∀ s, InvLX st F K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufJ8 st K s)
    (hbufS : ∀ s, InvLX st F K s → InvQCMW st Cs Ω Sg Ac Locks p K μ s → InvBufSJ8 st K s)
:
    InvBlkGdUW3 st ar p K Locks (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) := by
  intro s a info nx s1 s2 a1 buf length cap hE emi C hb hl hcap y hy
  have hqf := hE.2
  have PE := hqf.1.1.1
  have hK := hE.1.regionOK
  have hU := hE.1.userOK
  have hLA := hE.1.ioLayA
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_ofW (P := fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K μ s) hE hqf hcdt
    (hz s hE.1)
  have hsl := cmSl_ofW hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    hbufS s hE.1 hqf buf (by rw [← lib_prefix hA PE C false]; exact hb)
  obtain ⟨hdec, hrep⟩ := cmAccGdZ hA PE hK hU hLA E hsl (cmDestZ_of hqf) hbC (hbuf s hE.1 hqf) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  have hW := mvWrS PE hK hLA (c := L.cpu s) (lk := Locks s) (m := L.mem s)
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact PE.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run PE.run
  have hsw : SWr (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
      (L.curW s) sched.TS_RUNNING :=
    fun X => OwnMap.gds_write_state (PE.hT _ PE.cT) hS0 (fun hq => absurd hq (nq_run (Or.inr rfl)))
  have : GRd (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) st
      (IoRS (st := st) K Locks s) := gdr_sub (fun _ hy => ioRS_cm hy)
  obtain ⟨h1, h2⟩ := cmFin8 (gS := (gd st (InvCMRS (st := st) K Locks s)
    (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))) hA PE hW hsw E hsl (hbuf s hE.1 hqf) hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

end arm

section rest
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {F : S → Prop}
variable {K : KLayout} {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (invj gen 2) **The decode onward of an accepted truncated Delete reads once** (`InvUDecOnceW` at
`Pre ∧ ¬ InvLen`; module docstring). No premise. -/
theorem invU_decOnceX (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan} {m0 : U64 → U64} :
    InvUDecOnceW st ar number p K Locks
      (fun s => (InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m0 s) ∧ ¬ InvLen st s) := by
  intro s a info nx s1 s2 a1 buf length cap r' hE hac emi C ebuf ecap hlen h Wd
  obtain ⟨⟨hJ, hqf⟩, hnL⟩ := hE
  obtain ⟨sA, aA, h0⟩ := hac
  have P := hqf.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsl, -⟩ := del_core hqf
  have hlbl : info.label = fl4_abi.label.CNodeDelete := (hqf.1.2.2.1 _ info (cur_thread_ok s) emi).1
  have hil : info.length < 2#u64 := by
    by_contra hc
    apply hnL
    intro t info' ht hi'
    have et : t = L.curW s := ok_inj_ff (ht.symm.trans (cur_thread_ok s))
    subst et
    rw [emi] at hi'
    have ei : info = info' := ok_inj_ff hi'
    subst ei
    have : ¬ info.length.val < 2 := fun h' => hc (by scalar_tac)
    omega
  have hlen' := hlen hil
  have enx := C.1
  have es1 := C.2.1
  have eu := C.2.2.1
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  have ecap0 := ecap
  rw [cap_agree hL hsl ag, hcs] at ecap0
  have hcap' : cap = .CNode cp cr cg cgb := (ok_inj_ff ecap0).symm
  subst hcap'
  have M := invCM_hmid (Locks := Locks) hA P h0 info nx s1 s2 a1 emi enx es1 eu
  have hctR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [M.c, nodeAt_of_ksb M.k]
    exact (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])).1
  have edec : ∀ m : machine.Store S, sched.cur_thread m s2 = sched.cur_thread st s2 →
      decCNG m ar s2 a1 fl4_abi.label.CNodeDelete length p.slot (.CNode cp cr cg cgb) true true true false buf
        p.extra = ok (.Err (.Sys .TruncatedMessage), s2, a1) := by
    intro m hm
    unfold decCNG
    rw [hm, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact cnode_decode_trunc ar m hlen'
  unfold invCMRest at h ⊢
  rw [hlbl] at h ⊢
  refine once_gstep (R0 := IoRS (st := st) K Locks s) (W0 := IoWS (st := st) K Locks s)
    (fun q hq => ⟨ioRS_cm hq, hq.2.1⟩) (fun q hq => P.ioWS_nu hq) (R.decCNG_nz _ _ _ _ _ _ _ _ _ _) h
    (fun r h1 => ?_) (fun r h1 hk Wd1 _ => ?_)
  · rw [R.decCNG_eq] at h1 ⊢
    rw [edec _ (sched.cur_thread.guard (gS := PathObl.guard st (IoRS (st := st) K Locks s)
      (IoWS (st := st) K Locks s)) s2 hctR)]
    rw [edec st rfl] at h1
    exact h1
  rw [R.decCNG_eq] at h1
  obtain ⟨r0, er0, rfl⟩ := bind_shape h1
  rw [edec st rfl] at er0
  obtain rfl := ok_inj_ff er0
  dsimp only at hk ⊢
  unfold R.invPostG at hk ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.blk] at hk ⊢
  exact invU_replyOnce P M (fun x5 Wd' T' er hk' =>
    invU_tailOnce hA P hcs hsl ((InvLX.buf8 hJ)) C ecap hlen' er hk' Wd' T') hk Wd1

end rest

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {F : S → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (invj gen 2) **`InvURoTrW` discharged** for the tree `R.invBodyG number p` at `Pre := SlJAt K ∧ InvQF`: `Once` at
the entry (`invU_entOnce` + `invU_decOnceX`), carried to the alternatives by `once_agreeJ` over the accepted run on
`guard st (InvCMRS s) (InvCMWS s)` (`invUAccW_of2` + `invBlkUW2_of8X`). No premise beyond `hA`, [P] `hm`. -/
theorem invURoTrW_ofX {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) {number : I64}
    {p : localinv.Plan} (K : KLayout) (m : U64 → U64) :
    InvURoTrW st ar number p K Locks m (R.invBodyG number p)
      (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) := by
  intro s s' a r hE hL hac Al _
  have hacc : InvUAccW st ar number p K Locks (fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) :=
    invUAccW_of2 hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeenX_of K m s h.1 h.2)
      (fun s h => invPsX_of K m s h.1 h.2)
      (invBlkUW2_of8X hA (invVsJX_of (fun _ h => h.1)) (invCdtJX_of (fun _ h => h.1)) (hzX_of K)
        (fun s hJ _ => (InvLX.buf8 hJ)))
  have hSC := invSlotCNX_of (st := st) (F := F) (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) (p := p) K m
  have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA
    (P := fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1) hSC
    (inv_isProg S number p)
  obtain ⟨s1, a1, h0⟩ := hac
  have hg := hacc s a s1 a1 hE h0
  rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
  have h0' : interp st ar (R.invBodyG number p) s a = ok (true, s1, a1) := by
    rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE) a]; exact h0
  have hent := invU_entOnce (Locks := Locks) hA
    (P := fun s => (InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) ∧ ¬ InvLen st s)
    (fun _ h => h.1.2.1.1.1) (fun s h => invSeenX_of K m s h.1.1 h.1.2)
    (fun s h => invPsX_of K m s h.1.1 h.1.2) (invU_decOnceX (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) hA)
    s a _ ⟨hE, hL⟩ ⟨s1, a1, h0⟩ h0'
  exact once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) _ (inv_noZero number p) s s' a _ ∅ ∅ Al.ksb Al.cpu
    Al.masks Al.read hg hent

end ro

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {F : S → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (vmscope gen 8: copy at `InvLX st F K` in place of `SlJAt K`) (unify gen 2) **The CNodeDelete (no PTE lock) path with the explicit tree `R.invBodyG`**: `inv_pathsKFU4`'s
arguments (`inv_pathsKFU2` / `inv_pathsKFU8` / `inv_pathsKDelU`), `inv_localPathUq` in place of
`inv_localPathU`. Premises as `inv_pathsKFU4`: `hA`, [P] `hm`, `hCs`, [P] `hlk`. -/
noncomputable def inv_pathDelX (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hF : ∀ s, F s → InvQF st Cs Ω Sg Ac Locks p K m s)
    (hlk : ∀ s b v, InvLX st F K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA (P := fun s => InvLX st F K s ∧
      InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
      (invSlotCNX_of K m)
      (inv_isProg S number p)
  inv_localPathUq (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
    (P := fun s => InvLX st F K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
    (invUAccW_of2 hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeenX_of K m s h.1 h.2)
      (fun s h => invPsX_of K m s h.1 h.2)
      (invBlkUW2_of8X hA (invVsJX_of (fun _ h => h.1)) (invCdtJX_of (fun _ h => h.1)) (hzX_of K)
        (fun _ hJ _ => (InvLX.buf8 hJ))))
    (invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA) (fun _ h => h.2.1.1.1)
      (fun s h => invSeenX_of K m s h.1 h.2))
    (invMoveW_ofU hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1) (fun s h => invSeenX_of K m s h.1 h.2)
      (fun s h => invPsX_of K m s h.1 h.2) (fun _ h => h.2.1.1.2) hp
      (invBlkGdUW2_of8X hA (invVsJX_of (fun _ h => h.1)) (invCdtJX_of (fun _ h => h.1)) (hzX_of K)
        (fun _ hJ _ => (InvLX.buf8 hJ))))
    (invRaW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeenX_of K m s h.1 h.2))
    (hufX (fun _ h => h.1.1.1) hF hlk)
    (R.invBodyG number p) hp (inv_noZero number p)
    (invRoW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => invSeenX_of K m s h.1 h.2) hp (inv_noZero number p))
    (invURoAccW_of hm (PL := fun s => InvLX st F K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s)
      (fun _ h hL => ⟨h.1, h.2, hL⟩) hp (inv_noZero number p)
      (invAccW_of2 hA (fun _ h => h.2.1.1.1.1)
        (fun s h => invSeenX_of K m s h.1 h.2.1)
        (fun s h => invPsX_of K m s h.1 h.2.1)
        (invBlkW2_ofX hA (invVsJX_of (fun _ h => h.1)) (invCdtJX_of (fun _ h => h.1)) (hzX_of K)))
      (invURoTrW_ofX hA hm K m))

/-- (unify gen 2) **The Copy / Mint path with the explicit tree `R.invBodyG`**: `inv_pathsKCM7`'s arguments
(`inv_pathsKCM6` / `inv_pathsKCM2` / `inv_pathsKCM`, `inv_hpzCM`'s facts), `inv_localPathCMq` in place of
`inv_localPathCM`. Premises as `inv_pathsKCM7`: `hA`, [P] `hm`, `hCs`, [P] `hlk`. -/

noncomputable def inv_pathCMX (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hF : ∀ s, F s → InvQCMW st Cs Ω Sg Ac Locks p K m s)
    (hlk : ∀ s b v, InvLX st F K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA (P := fun s => InvLX st F K s ∧
      InvQCMW st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1) (cmSCX_ofZ K m) (inv_isProg S number p)
  have hacc : InvCMAccW st ar number p K Locks (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) :=
    invUAccW_of3 hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeenX_ofW K m s h.1 h.2)
      (fun s h => cmPsX_ofW K m s h.1 h.2)
      (invCMBlkUW3_ofZX hA (invCdtJX_of (fun _ h => h.1)) (hzX_of K) (fun _ h _ => (InvLX.buf8 h))
        (fun _ h _ => (InvLX.bufS8 h)))
  have hcdt : InvCdtJ st K (fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) :=
    invCdtJX_of (fun _ h => h.1)
  have hdo := invCMDecOnceW_of (number := number) hA
    (P := fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
    (fun _ h => h.2.1.2.2.1)
    (fun s h => cmEnt_ofW h h.2 hcdt (hzX_of K s h.1)) (fun _ h => cmSl_ofW h.2)
    (invCMTailW_of8 hA (fun _ h => h.2.1.1.1) (fun _ h => h.2.1.2.2.1)
      (fun s h => cmEnt_ofW h h.2 hcdt (hzX_of K s h.1)) (fun _ h => cmSl_ofW h.2)
      (fun s h => (InvLX.buf8 h.1)))
  inv_localPathCMq (K := K) (m0 := m) (Locks := Locks) ar hA hK hU number p hm
    (P := fun s => InvLX st F K s ∧ InvQCMW st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
    hacc
    (invDecW_of hA (fun _ h => h.1.regionOK) (fun _ h => h.1.ioLayA) (fun _ h => h.2.1.1.1)
      (fun s h => cmSeenX_ofW K m s h.1 h.2))
    (invMoveW_ofU3 hA (fun _ h => h.1.regionOK) (fun _ h => h.1.userOK) (fun _ h => h.1.ioLayA)
      (fun _ h => h.2.1.1.1) (fun s h => cmSeenX_ofW K m s h.1 h.2)
      (fun s h => cmPsX_ofW K m s h.1 h.2) (fun _ h => h.2.1.1.2) hp
      (invCMBlkGdUW3_ofZX hA (invCdtJX_of (fun _ h => h.1)) (hzX_of K) (fun _ h _ => (InvLX.buf8 h))
        (fun _ h _ => (InvLX.bufS8 h))))
    (invRaW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeenX_ofW K m s h.1 h.2))
    (hufX (fun _ h => h.1.1.1) hF hlk)
    (R.invBodyG number p) hp (inv_noZero number p)
    (invRoW_of hA (fun _ h => h.2.1.1.1)
      (fun s h => cmSeenX_ofW K m s h.1 h.2) hp (inv_noZero number p))
    (invCMRoAccW_of_ent hm hacc (hp.mono fun _ hy => altOf_cm_io hy) (inv_noZero number p)
      (invCM_entOnce hA (fun _ h => h.2.1.1.1)
        (fun s h => cmSeenX_ofW K m s h.1 h.2)
        (fun s h => cmPsX_ofW K m s h.1 h.2) hdo))

end paths

end Fl4Proofs.P2.PathObl

/-! ## Part 2: VCPU and PTE avoidance of the invocation paths (`E2EP`) -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame)

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The words a mapped frame cap's walk must not read in a VM epoch**: aligned VCPU data words and PTE words. -/
def XD (K : KLayoutP) (b : U64) : Prop := (Aligned b ∧ VData K.toKLayoutV b) ∨ b ∈ K.ptes

variable (st) in
/-- **A mapped small frame cap's walk reads no `XD` word** (natively `SlJAtZ.vsJX` with `ptesR_sub`, at `CvP`). -/
def VsXW (K : KLayoutP) (s : S) : Prop :=
  ∀ sl fp rt asid va, sl ∈ K.slots →
    obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
    va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
      VsRdG st (fun b => VsW K.toKLayout b ∧ ¬ XD K b) s asid va

/-- **The epoch's VCPU layout facts the avoidance reads** (from the epoch's `VtxBundle4`: `b.vu`, `ko`). -/
structure InvVF (K : KLayoutP) : Prop where
  vu : UserObj K.toKLayoutV
  ko : VcpuKsOff K.toKLayoutV

/-- **What an excluded set `Ex` must satisfy for the invocation paths' avoidance**: inside `XD` on aligned words,
off the regions, the kernel-global block and the user words; `XD` words are VSpace words. -/
structure ExOK (K : KLayoutP) (Ex : U64 → Prop) : Prop where
  ex : ∀ b, Aligned b → Ex b → XD K b
  reg : ∀ b, region K.toKLayout b ≠ .none → ¬ Ex b
  ks : KsNoE Ex K.toKLayoutV
  user : UserNoE Ex K.toKLayoutV
  xv : ∀ b, XD K b → VsW K.toKLayout b

theorem xd_vsW {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (vf : InvVF K) {b : U64} (h : XD K b) :
    VsW K.toKLayout b := by
  rcases h with ⟨ha, hv⟩ | hp
  · refine ⟨ha, ?_, fun hu => notVData_of_noVcpu (vf.vu b hu) hv⟩
    by_contra hr
    exact notVData_of_region' hK.base hr hv
  · exact ⟨(hU.kern b hp).1, hK.none b hp, (hU.kern b hp).2⟩

/-- `ExOK` for the VCPU data words (`AvoidV`). -/
theorem exOK_V {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (vf : InvVF K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) : ExOK K (VData K.toKLayoutV) where
  ex := fun _ ha hv => Or.inl ⟨ha, hv⟩
  reg := fun _ hb => notVData_of_region' hK.base hb
  ks := fun _ ho => notVData_of_noVcpu (noVcpu_ks (vcpuKs_ofKo vf.ko) hf ho)
  user := fun b hb => notVData_of_noVcpu (vf.vu b hb)
  xv := fun _ h => xd_vsW hK hU vf h

/-- `ExOK` for the VCPU data and PTE words (the route-C cut with VCPUs, `avoidE_cutLiftV_X`). -/
theorem exOK_VP {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (vf : InvVF K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hq : KsNoE (· ∈ K.ptes) K.toKLayoutV) :
    ExOK K (fun b => VData K.toKLayoutV b ∨ b ∈ K.ptes) where
  ex := fun _ ha hx => hx.elim (fun hv => Or.inl ⟨ha, hv⟩) Or.inr
  reg := fun b hb hx => hx.elim (notVData_of_region' hK.base hb) (fun hp => hb (hK.none b hp))
  ks := fun o ho hx => hx.elim (notVData_of_noVcpu (noVcpu_ks (vcpuKs_ofKo vf.ko) hf ho)) (hq o ho)
  user := userNoE_vpte hU vf.vu
  xv := fun _ h => xd_vsW hK hU vf h

variable {K : KLayoutP} {Locks : S → U64 → Prop} {s : S} {Ex : U64 → Prop}

/-- **An `IoRSR` word is an `InvCMRS` word off `Ex`** (`ioRSR_rsE` for any `ExOK` set). -/
theorem ioRSR_rsEX (E : ExOK K Ex) {x : U64} (h : IoRSR st K.toKLayout Locks s x) :
    rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s x := by
  refine ⟨ioRS_cm h.1, fun hx => ?_⟩
  rcases h.2 with hr | ⟨o, ho, rfl⟩
  · exact E.reg _ hr hx
  · exact E.ks o ho hx

/-- **An aligned user word is an `InvCMRS` word off `Ex`.** -/
theorem userW_rsEX (E : ExOK K Ex) {x : U64} (h : UserW K.toKLayout x) :
    rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s x :=
  ⟨⟨h.1, Or.inl h.2⟩, E.user x h.2⟩

end sets

section seenX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {F : S → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64} {s : S}

/-- `invSeenRN` at `InvLX` states. -/
theorem invSeenRNX (hJ : InvLX st F K s) (hq : InvQF st Cs Ω Sg Ac Locks p K μ s) :
    ∀ x, SeenW p x → IoRSR st K Locks s x := by
  intro x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, mp, C, -, -, -, -, -, -, -, hdK, -, hLd, -, -, hSn, -⟩ :=
    del_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hJ.hz (e ▸ hdK)
  obtain ⟨o, ho, rfl⟩ := hSn x hx
  have hov : o.val < 32 ∧ o.val % 8 = 0 := by
    rcases ho with rfl | rfl | rfl | rfl <;> simp [layout.cte.CAP0, layout.cte.CAP1, layout.cte.PREV, layout.cte.NEXT]
  exact PE.lockSlotR hdK (hLd hd0) hov.1 hov.2

/-- `cmSeenRN` at `InvLX` states. -/
theorem cmSeenRNX (hJ : InvLX st F K s) (hq : InvQCMW st Cs Ω Sg Ac Locks p K μ s) :
    ∀ x, SeenW p x → IoRSR st K Locks s x := by
  intro x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hdK, -, hLd, hsK, -, hLs, -, hSn⟩ := cm_coreW hq
  have hd0 : dest ≠ 0#u64 := fun e => hJ.hz (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hJ.hz (e ▸ hsK)
  rcases hSn x hx with rfl | rfl | rfl | rfl
  · exact (PE.lockSlotR hdK (hLd hd0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0]))
  · exact (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0]))
  · exact (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1]))
  · exact (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))

end seenX

section blk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (vmscope gen 8: copy for an `ExOK` set `Ex` and `InvLX`) (unify gen 2) **Both arms of the no-PTE Delete decode block on the store guarded to `InvCMRS` off the PTE set**
(module docstring). No premise. -/
theorem invBlkNX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    {F : S → Prop} {Ex : U64 → Prop} (hFv : ∀ s, F s → VsXW st K s) (E0 : ExOK K Ex) {s : S}
    (hE : InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s))
        (IoRSR st K.toKLayout Locks s) (InvCMWS (st := st) K.toKLayout Locks s) ar s z.1 z.2.1 := by
  obtain ⟨hJ, hq⟩ := hE
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
  have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
  rw [hlbl] at hy ⊢
  have hW : IoWr st (InvCMWS (st := st) K.toKLayout Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => ioWS_cm h)
  by_cases hlen : length < 2#u64
  · obtain ⟨hdec, hrep⟩ := truncAccR (R := rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (gS := guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE
      (fun _ h => ioRSR_rsEX E0 h) (fun _ h => userW_rsEX E0 h) hW
      (fun _ h => ⟨h.1, Or.inl h.2⟩) hcs hsK (InvLX.buf8 hJ) C hcap hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
          (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
      grd_sub (fun _ h => ioRSR_rsEX E0 h)
    obtain ⟨h1, h2⟩ :=
      truncFinR (gS := guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW
      (SWr.of_W (ioWS_cm PE.stw.2)) hcs hsK (InvLX.buf8 hJ) C hcap hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · have hvsP := invVsJX_of (st := st)
      (P := fun s => InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) (fun _ h => h.1)
    have E := delEnt_of (P := fun s => InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
      ⟨hJ, hq⟩ hq hvsP (invCdtJX_of (fun _ h => h.1)) (hzX_of _ s hJ)
    obtain ⟨hdec, hrep⟩ := delAccN (R := rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (X := XD K)
      (gS := guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW (fun _ h => ioWS_cm h) E hsK hlen (hFv s hJ.here.2) E0.xv
      (fun b h hx => ⟨ioRS_cm h, fun he => hx (E0.ex b h.1 he)⟩) C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
          (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
      grd_sub (fun _ h => ioRSR_rsEX E0 h)
    obtain ⟨h1, h2⟩ :=
      delFinN (gS := guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW (ioWS_cm PE.stw.2) E hsK hlen
      (fun sl fp rt asid va hsl hc hA => hvsP s sl fp rt asid va
        ⟨hJ, hq⟩ hsl hc hA)
      C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 8: copy for an `ExOK` set `Ex` and `InvLX`) (unify gen 2) **The accepted no-PTE Delete run reads no PTE word**: it runs on
`guard st (rsE ptes InvCMRS s) (InvCMWS s)` as on `st`. No premise. -/
theorem invAccNX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    {F : S → Prop} {Ex : U64 → Prop} (hFv : ∀ s, F s → VsXW st K s) (E0 : ExOK K Ex) {s s' : S} {a a' : A}
    (hE : InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s', a') := by
  have PE := hE.2.1.1.1
  haveI : GRd (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_rsEX E0 h)
  exact inv_acc_genR (W := InvCMWS (st := st) K.toKLayout Locks s) hA PE (PE.ioWr.mono (fun _ h => ioWS_cm h))
    (invSeenRNX hE.1 hE.2) (invPsRN hE.2)
    (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => invBlkNX hA hFv E0 hE emi hc hl hk y hy) h

/-- (vmscope gen 8: copy for an `ExOK` set `Ex` and `InvLX`) (unify gen 2) **The Copy / Mint decode block on the store guarded to `InvCMRS` off the PTE set** (module
docstring). No premise. -/
theorem invCMBlkNX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    {F : S → Prop} {Ex : U64 → Prop} (E0 : ExOK K Ex) {s : S}
    (hE : InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    {a : A} {info : msginfo.MessageInfo} {nx : U64} {s1 s2 : S} {a1 : A} {buf length : U64}
    {cap : capability.Cap} (emi : msg.msg_info st s (L.curW s) = ok info)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hb : msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (y : (core.result.Result Unit error.Exc) × S × A)
    (hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) ar s2 a1
        info.label length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧
      z.2.2 = core.result.Result.Ok () ∧
      FinOK (L := L) (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s))
        (IoRSR st K.toKLayout Locks s) (InvCMWS (st := st) K.toKLayout Locks s) ar s z.1 z.2.1 := by
  obtain ⟨hJ, hqf⟩ := hE
  have PE := hqf.1.1.1
  have hlb := hqf.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
  have E := cmEnt_ofW (P := fun s => InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    ⟨hJ, hqf⟩ hqf (invCdtJX_of (fun _ h => h.1)) (hzX_of _ s hJ)
  have hsl := cmSl_ofW hqf
  have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K.toKLayout (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
    (InvLX.bufS8 hJ) buf (by rw [← lib_prefix hA PE C false]; exact hb)
  have hW : IoWr st (InvCMWS (st := st) K.toKLayout Locks s) K.heap.scBits s := PE.ioWr.mono (fun _ h => ioWS_cm h)
  obtain ⟨hdec, hrep⟩ := cmAccZR (R := rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
    (gS := guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) hA PE
    (fun _ h => ioRSR_rsEX E0 h) (fun _ h => userW_rsEX E0 h) hW (fun _ h => ⟨h.1, Or.inl h.2⟩)
    (fun q o hq hlk ho h8 _ hw => ioWS_cm ((PE.lockSlot hq hlk ho h8).2 hw))
    (fun q hq hlk hT hn x v _ => by
      have h := (PE.lockSlot hq hlk (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT, hn⟩)
      rw [wadd_zero (PE.lay.slot8 q hq).2] at h
      exact gst_write (ioWS_cm h))
    (fun _ _ => SWr.of_W (ioWS_cm PE.stw.2)) E hsl (cmDestZ_of hqf) hbC (InvLX.buf8 hJ) hlb C hcap hy
  refine ⟨hdec, fun z hz' => ?_⟩
  haveI : GRd (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
        (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_rsEX E0 h)
  obtain ⟨h1, h2⟩ :=
    cmFin8R (gS := guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) hA PE hW (SWr.of_W (ioWS_cm PE.stw.2)) E hsl (InvLX.buf8 hJ)
      hlb C hcap hy hz'
  exact ⟨hrep z hz', h1, h2⟩

/-- (vmscope gen 8: copy for an `ExOK` set `Ex` and `InvLX`) (unify gen 2) **The accepted Copy / Mint run reads no PTE word**. No premise. -/
theorem invCMAccNX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {number : I64} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    {F : S → Prop} {Ex : U64 → Prop} (E0 : ExOK K Ex) {s s' : S} {a a' : A}
    (hE : InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s', a') := by
  have PE := hE.2.1.1.1
  haveI : GRd (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) st (IoRSR st K.toKLayout Locks s) :=
    grd_sub (fun _ h => ioRSR_rsEX E0 h)
  exact inv_acc_gen3R (W := InvCMWS (st := st) K.toKLayout Locks s) hA PE (PE.ioWr.mono (fun _ h => ioWS_cm h))
    (cmSeenRNX hE.1 hE.2) (cmPsRN hE.2)
    (fun info nx s1 s2 a1 buf length cap emi hc hb hl hk y hy => invCMBlkNX hA E0 hE emi hc hb hl hk y hy) h

end blk

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar)

/-- **The CNodeDelete (no PTE lock) path at `InvLX`, restricted to `QPs`, reads no `Ex` word** for every `ExOK` set
(`avoidE_delE` without the P3 bundle and `CvP`: the walk's facts from `VsXW` at the `Pre` state). -/
theorem avoidE_delX {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) {F : S → Prop}
    (hF : ∀ s, F s → InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hlk : ∀ s b v, InvLX st F K.toKLayout s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hFv : ∀ s, F s → VsXW st K s) {Ex : U64 → Prop} (hEx : ∀ s, F s → QPs K st s → ExOK K Ex) :
    AvoidE Ex ((inv_pathDelX (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p
      hm K.toKLayout m hK.base.base hU.base.base hF hlk).restrQ (fun s => QPs K st s)
      (fun _ _ _ _ h hb ha => h.wr (Or.inl hb) ha)) := by
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s) :=
    fun s h => invSlotCNX_of K.toKLayout m s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := m) hA
    (P := fun s => (InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s)
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hs' : (InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s := hs
    have hr' : syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) := hr
    show syscall.handle_invocation_local (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s1, a1)
    exact invAccNX hA hFv (hEx s hs'.1.1.here.2 hs'.2) hs'.1 hr'
  · intro s a r hs0 hr hn s' r' hA' h'
    have hs : (InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s := hs0
    have E0 := hEx s hs.1.1.here.2 hs.2
    have Al : Alt st (InvCMRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := hA'
    have AlR := Al.anti (R' := IoRSR st K.toKLayout Locks s) (fun x hx => ioRS_cm hx.1)
    have hr' : syscall.handle_invocation_local st ar s a number p = ok r := hr
    have h'' : syscall.handle_invocation_local st ar s' a number p = ok r' := h'
    have g := inv_dec_guardRSR hA hs.1.2.1.1.1 (invSeenRNX hs.1.1 hs.1.2) AlR hr' hn h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hpR st' N s' ⟨s, hs, AlR⟩ a
    show syscall.handle_invocation_local (guard st (fun b => ¬ Ex b) (fun _ => True)) ar s' a number p = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st)
      (fun q hq hp => (ioRSR_rsEX E0 hq).2 hp)
      (fun _ h => h) _ (inv_noZero number p) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs0, hAc⟩ := g
    have hs : (InvLX st F K.toKLayout s ∧ InvQF st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s := hs0
    have E0 := hEx s hs.1.1.here.2 hs.2
    have hAc' : Alt st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user) s σ := hAc
    exact hpR st' N σ ⟨s, hs, hAc'.anti (R' := IoRSR st K.toKLayout Locks s)
      (fun x hx => ioRSR_rsEX E0 hx)⟩ a

/-- **The Copy / Mint path at `InvLX`, restricted to `QPs`, reads no `Ex` word** for every `ExOK` set
(`avoidE_cmE` without the P3 bundle). -/
theorem avoidE_cmX {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) {F : S → Prop}
    (hF : ∀ s, F s → InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hlk : ∀ s b v, InvLX st F K.toKLayout s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    {Ex : U64 → Prop} (hEx : ∀ s, F s → QPs K st s → ExOK K Ex) :
    AvoidE Ex ((inv_pathCMX (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p
      hm K.toKLayout m hK.base.base hU.base.base hF hlk).restrQ (fun s => QPs K st s)
      (fun _ _ _ _ h hb ha => h.wr (Or.inl hb) ha)) := by
  have hSC : InvSlotCN st K.toKLayout p
      (fun s => (InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s) :=
    fun s h => cmSCX_ofZ K.toKLayout m s h.1
  have hpR := inv_isProgOnR (Locks := Locks) (m0 := m) hA
    (P := fun s => (InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s)
    (fun _ h => h.1.2.1.1.1) hSC (inv_isProg S number p)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hs' : (InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s := hs
    have hr' : syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1) := hr
    show syscall.handle_invocation_local (guard st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s)
      (InvCMWS (st := st) K.toKLayout Locks s)) ar s a number p = ok (true, s1, a1)
    exact invCMAccNX hA (hEx s hs'.1.1.here.2 hs'.2) hs'.1 hr'
  · intro s a r hs0 hr hn s' r' hA' h'
    have hs : (InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s := hs0
    have E0 := hEx s hs.1.1.here.2 hs.2
    have Al : Alt st (InvCMRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' := hA'
    have AlR := Al.anti (R' := IoRSR st K.toKLayout Locks s) (fun x hx => ioRS_cm hx.1)
    have hr' : syscall.handle_invocation_local st ar s a number p = ok r := hr
    have h'' : syscall.handle_invocation_local st ar s' a number p = ok r' := h'
    have g := inv_dec_guardRSR hA hs.1.2.1.1.1 (cmSeenRNX hs.1.1 hs.1.2) AlR hr' hn h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hpR st' N s' ⟨s, hs, AlR⟩ a
    show syscall.handle_invocation_local (guard st (fun b => ¬ Ex b) (fun _ => True)) ar s' a number p = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st)
      (fun q hq hp => (ioRSR_rsEX E0 hq).2 hp)
      (fun _ h => h) _ (inv_noZero number p) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs0, hAc⟩ := g
    have hs : (InvLX st F K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s) ∧ QPs K st s := hs0
    have E0 := hEx s hs.1.1.here.2 hs.2
    have hAc' : Alt st (rsE Ex (InvCMRS (st := st) K.toKLayout Locks) s) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout m) (· ∈ K.user) s σ := hAc
    exact hpR st' N σ ⟨s, hs, hAc'.anti (R' := IoRSR st K.toKLayout Locks s)
      (fun x hx => ioRSR_rsEX E0 hx)⟩ a

end av

end Fl4Proofs.P2.E2EP
