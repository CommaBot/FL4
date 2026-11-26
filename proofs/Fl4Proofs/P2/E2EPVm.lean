/-
P2 (line pte, gen 6): **the VM fault and VM ReplyRecv paths read no PTE word** (the `vmF` / `vmR` fields of
`P3AvP4`, discharged) and **`serializable_fl4_localP3P5`** (no [W] left).

Both read sets are `IoRS (userV K)` (user-free), so the `userP` trick applies (`P2/E2EPIrq.lean`, `P2/E2EPIo.lean`):
* `vmLay_userP` / `vmBase_userP` / `vmFPre_userP` / `vmRPre_userP` (fieldwise, through `ioLay_userP`), `rdTab_userP`
  (the ASID words are no PTE words: `TabNoE`), `ag_userP` (an alternative for `IoRS (userV K)` agrees on
  `IoRS (userP K)`);
* acc: `vm_acc` / `rr_vm_acc` at `userP K`; declines from every alternative: p2vm's **R''-generic** `vm_dec_tr` /
  `rr_dec_tr` at `userP K` with `R'' := IoRS (userP K) ∪ {the handler's / replied thread's words}` — those extra
  words are TCB fields (`VmRep.notPte`, `RrRep.notPte`: region `.tcb`, off the PTEs);
* vmR's `TabNoE` from `PteSl` at its bundle (`VmRRPreJ` carries `SlJAt (userV K)` = `SlJAt K` at `K.vcpus = ∅`);
  vmF's `Pre` (`VmPre`) carries no bundle: **`vmP` [J]** — the ASID table / pool words at a VM-fault entry state are
  no PTE words (P1 `HeapOK`, as `VtmP.tabP`).

`P3AvP5` (= `P3AvP4` − vmF − vmR − io + `vmP` [J]), **`serializable_fl4_localP3P5`**: every slot of `fl4LocP3W`
lifted to `ownP` with `K.ptes` arbitrary, **no [W]**; PTE-line [J]: `PteSl`, `VtmP`, `VxP`, `vmP` (all P1 `HeapOK`
distinctness).
-/
import Fl4Proofs.P2.E2EPIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}
variable {Locks : S → U64 → Prop}

theorem vmLay_userP (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    (hL : VmLay (userV K.toKLayoutV)) : VmLay (userP K) :=
  ⟨ioLay_userP hK hks hL.io, hL.epw, hL.rpw⟩

theorem vmBase_userP (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV) {s : S}
    (B : VmBase st (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  { B with lay := vmLay_userP hK hks B.lay }

theorem vmFPre_userP {A : Type} {ar : machine.Arch A} (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    {s : S} (P : VmFPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) :
    VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s :=
  { P with base := vmBase_userP hK hks P.base }

theorem vmRPre_userP {A : Type} {ar : machine.Arch A} (hK : RegionOKP K) (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    {s : S} {rptr ep : U64} (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep) :
    VmRPre st ar (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep :=
  { Q with base := vmBase_userP hK hks Q.base }

theorem ioRS_of_userP {s : S} {x : U64} (h : IoRS (st := st) (userP K) Locks s x) :
    IoRS (st := st) (userV K.toKLayoutV) Locks s x ∧ x ∉ K.ptes :=
  ⟨⟨h.1, fun hu => h.2.1 (Or.inl hu), h.2.2⟩, fun hp => h.2.1 (Or.inr hp)⟩

theorem ioRS_userP_of {s : S} {x : U64} (h : IoRS (st := st) (userV K.toKLayoutV) Locks s x) (hp : x ∉ K.ptes) :
    IoRS (st := st) (userP K) Locks s x :=
  ⟨h.1, fun hu => Or.elim hu h.2.1 hp, h.2.2⟩

theorem rdTab_userP {s : S} (h : RdTab (L := L) (IoRS (st := st) (userV K.toKLayoutV) Locks s) s)
    (ht : TabNoE (L := L) (· ∈ K.ptes) s) : RdTab (L := L) (IoRS (st := st) (userP K) Locks s) s :=
  fun hi hhi => ⟨ioRS_userP_of (h hi hhi).1 (ht hi hhi).1,
    fun lo hlo hne => ioRS_userP_of ((h hi hhi).2 lo hlo hne) ((ht hi hhi).2 lo hlo hne)⟩

theorem ag_userP {s s' : S} {m0 : U64 → U64}
    (Al : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) Locks s) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m0) (· ∈ (userV K.toKLayoutV).user) s s') :
    Ag st (IoRS (st := st) (userP K) Locks s) s s' :=
  ⟨Al.ksb, Al.cpu, fun b hb => Al.read b (ioRS_of_userP hb).1⟩

/-- A TCB field (offset 192 … 4096) of a thread of `T` is no PTE word. -/
theorem tcbw_notPte (hK : RegionOKP K) {s : S} (B : VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s) {t off : U64}
    (ht : t ∈ T) (h1 : 192 ≤ off.val) (h2 : off.val < 4096) : fld t off ∉ K.ptes := by
  intro hp
  have h3 : region K.toKLayout (fld t off) = .tcb t := B.lay.io.tcbw t (B.hT t ht) off h1 h2
  rw [hK.none _ hp] at h3
  cases h3

/-- The extra word `vm_dec_tr` reads (the handler's `REPLY_OBJ`) is no PTE word. -/
theorem VmRep.notPte {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hK : RegionOKP K) {s : S}
    (P : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hlkE : VmGlue st ar Locks s) {a : A} {b : U64}
    (h : VmRep st ar s a b) : b ∉ K.ptes := by
  obtain ⟨s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, -, rfl⟩ := h
  have D := vm_dfOf hA P hlkE eu
  have hdT := (D.ep sl ptr badge x y g gr hsl hcap).2.2 hst
  exact tcbw_notPte hK P.base hdT (off := 3360#u64) (by simp) (by simp)

/-- The extra words `rr_dec_tr` reads (the replied thread's `STATE` and word 3376) are no PTE words. -/
theorem RrRep.notPte (hK : RegionOKP K) {s : S} {rptr : U64} (P : VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hrR : rptr ∈ Rp) {b : U64} (h : RrRep st rptr s b) : b ∉ K.ptes := by
  obtain ⟨h0, -, hb⟩ := h
  have huT := (rr_uX P hrR 0#u64 0#u64).2 h0
  rcases hb with rfl | rfl
  · rw [stA_eq]; exact tcbw_notPte hK P huT (off := 3328#u64) (by simp) (by simp)
  · exact tcbw_notPte hK P huT (off := 3376#u64) (by simp) (by simp)

end lay

section vm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The VM-fault route-U path reads no PTE word**, from `PteSl` [J] and `vmP` [J]. -/
theorem vmF_avoidP_path (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (vmFSlot st ar hA hm).Prem i K.toKLayoutV m)
    (hvm : ∀ s, VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
      TabNoE (L := L) (· ∈ K.ptes) s) :
    AvoidE (· ∈ K.ptes) ((vmFSlot st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_vm_fault_local mm ar x a i.addr i.code =
      interp mm ar (R.syscall.handle_vm_fault_local i.addr i.code) x a :=
    fun a mm x => congrFun (congrFun (vm_isProg S i.addr i.code A ar mm) x) a
  refine ⟨?_, ?_, IsProg.on (vm_isProg S i.addr i.code) _ _ _⟩
  · intro s a r hs hr hb
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok (true, s1, a1) := hr
    have g1 := vm_acc (Locks := i.Locks) hA hs'.1 hs'.2.2 hr'
    have g2 := vm_acc (Locks := i.Locks) hA (vmFPre_userP hK hPS.1 hs'.1) (rdTab_userP hs'.2.2 (hvm s hs')) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_vm_fault_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.addr i.code = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok r := hr
    have h'' : syscall.handle_vm_fault_local st ar s' a i.addr i.code = ok r' := h'
    have hP := vmFPre_userP hK hPS.1 hs'.1
    have hn0 : r.1 ≠ true := hn
    have hn' : r'.1 ≠ true :=
      (vm_dec_alt (m0 := m) hA (regionOK_userV hK.base) h.lay hs'.1 hs'.2.1 hr' hn0 hAl h'').1
    have hg := vm_dec_tr hA hP hs'.2.1 (ag_userP hAl)
      (R'' := fun b => IoRS (st := st) (userP K) i.Locks s b ∨ VmRep st ar s a b) (fun b hb => Or.inl hb)
      (fun s1 a1 sl ptr badge x y g gr eu hsl hcap hst hne =>
        Or.inr ⟨s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, hne, rfl⟩) h'' hn'
    show syscall.handle_vm_fault_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.addr i.code
      = ok r'
    exact (eP a _ s').trans (interp_mono (st := st)
      (fun q hq => Or.elim hq (fun h1 => (ioRS_of_userP h1).2) (fun h2 => VmRep.notPte hA hK hP hs'.2.1 h2))
      (fun _ _ => trivial) _ (vm_noZero i.addr i.code) s' a r' ((eP a _ s').symm.trans hg))

/-- **The VM fault path reads no PTE word** (the `vmF` field of `P3AvP`). -/
theorem vmF_avoidP (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (vmFSlot st ar hA hm).Prem i K.toKLayoutV m)
    (hvm : ∀ s, VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
      TabNoE (L := L) (· ∈ K.ptes) s) :
    AvoidP K ((vmFSlot st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (vmFSlot st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)) := by
    rintro P W rfl
    exact avoidE_liftAtV hK.base _ W (vmF_avoidP_path st ar hA hm i K m hK hU hPS h hvm)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **The VM ReplyRecv route-U path reads no PTE word**, from `PteSl` [J]. -/
theorem vmR_avoidP_path (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (vmRSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) ((vmRSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_reply_recv_vm_local mm ar x a (i.rptr, i.ep) =
      interp mm ar (R.syscall.handle_reply_recv_vm_local (i.rptr, i.ep)) x a :=
    fun a mm x => congrFun (congrFun (rr_isProg S i.rptr i.ep A ar mm) x) a
  have hex : ∃ p : SProg Bool, IsProg (rrBody S i.rptr i.ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
          (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
          i.rptr i.ep s →
        (∃ b, RrRep st i.rptr s b) →
        PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' →
        interp st ar p s' a = ok r →
        E2E.Once st ar (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (· ∈ (userV K.toKLayoutV).user) ∅ ∅ p s' a :=
    ⟨_, rr_isProg S i.rptr i.ep, rr_noZero i.rptr i.ep, rr_hroJ hA⟩
  have bun : ∀ s, SlJAt (L := L) (userV K.toKLayoutV) s → SlJAt (L := L) K.toKLayout s := by
    intro s hJ; rw [← userV_empty h.nv]; exact hJ
  refine ⟨?_, ?_, IsProg.on (Classical.choose_spec hex).1 _ _ _⟩
  · intro s a r hs hr hb
    have hs' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok (true, s1, a1) := hr
    have hE := VmRRPreJ.pre hs'
    have g1 := rr_vm_acc (Locks := i.Locks) hA hE.1 hE.2.2.2 hr'
    have g2 := rr_vm_acc (Locks := i.Locks) hA (vmRPre_userP hK hPS.1 hE.1)
      (rdTab_userP hE.2.2.2 (hPS.2 s (bun s hs'.1))) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_reply_recv_vm_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a (i.rptr, i.ep) = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    have hs' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s := hs
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok r := hr
    have h'' : syscall.handle_reply_recv_vm_local st ar s' a (i.rptr, i.ep) = ok r' := h'
    have hE := VmRRPreJ.pre hs'
    have hEP : VmRRPre st ar (userP K) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω K.heap i.Sg (Heap.replies K.heap)
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s :=
      ⟨vmRPre_userP hK hPS.1 hE.1, hE.2.1, hE.2.2.1, rdTab_userP hE.2.2.2 (hPS.2 s (bun s hs'.1))⟩
    have hn0 : r.1 ≠ true := hn
    have hn' : r'.1 ≠ true :=
      (rr_dec_alt (m0 := m) hA (regionOK_userV hK.base) h.bun.choose_spec.ioLayA hE hr' hn0 hAl h'').1
    have hg := rr_dec_tr hA hEP (ag_userP hAl)
      (R'' := fun b => IoRS (st := st) (userP K) i.Locks s b ∨ RrRep st i.rptr s b) (fun b hb => Or.inl hb)
      (fun b hb => Or.inr hb) h'' hn'
    show syscall.handle_reply_recv_vm_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a
      (i.rptr, i.ep) = ok r'
    exact (eP a _ s').trans (interp_mono (st := st)
      (fun q hq => Or.elim hq (fun h1 => (ioRS_of_userP h1).2) (fun h2 => RrRep.notPte hK hEP.1.base hE.2.1 h2))
      (fun _ _ => trivial) _ (rr_noZero i.rptr i.ep) s' a r' ((eP a _ s').symm.trans hg))

/-- **The VM ReplyRecv path reads no PTE word** (the `vmR` field of `P3AvP`). -/
theorem vmR_avoidP (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (vmRSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K ((vmRSlotP3 st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (vmRSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)) := by
    rintro P W rfl
    exact avoidE_liftAtV hK.base _ W (vmR_avoidP_path st ar hA hm i K m hK hU hPS h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **The PTE-line premises of `fl4LocP3W`, no [W]** ([J] only, all P1 `HeapOK` distinctness). -/
structure P3AvP5 : Prop where
  pteSl : ∀ K : KLayoutP, RegionOKP K → K.ptes ≠ ∅ → PteSl st K
  vtP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m → ∀ s, VtPre st i K.toKLayoutV s → VtmP K st i.irq s
  vxP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m → ∀ s, VxPre st i K.toKLayoutV m s → VxP (L := L) K s
  /-- [J] at a VM-fault entry state the ASID table / pool words are no PTE words. -/
  vmP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vmFSlot st ar hA hm).Prem i K.toKLayoutV m →
    ∀ s, VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
      TabNoE (L := L) (· ∈ K.ptes) s

theorem P3AvP5.toP4 (h : P3AvP5 st ar hA hm) : P3AvP4 st ar hA hSt hm a0 where
  pteSl := h.pteSl
  vtP := h.vtP
  vxP := h.vxP
  vmF i K m hK hU he hp := vmF_avoidP st ar hA hm i K m hK hU (h.pteSl K hK he) hp (h.vmP i K m hK hU he hp)
  vmR i K m hK hU he hp := vmR_avoidP st ar hA hm i K m hK hU (h.pteSl K hK he) hp
  io i K m hK hU he hp := io_avoidP st ar hA hm i K m hK hU (h.pteSl K hK he) hp

/-- **FL4 end to end with rules 7 and 8, `K.ptes` arbitrary, no [W]**: `serializable_fl4_localP3P4` with all eight
slots' PTE avoidance discharged (`P3AvP5`: PTE-line [J] `PteSl`, `VtmP`, `VxP`, `vmP` only). -/
theorem serializable_fl4_localP3P5 (hAv : P3AvP5 st ar hA hm) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3P st ar hA hSt hm a0 (P3AvP2.toP3 st ar hA hSt hm a0 (P3AvP3.toP2 st ar hA hSt hm a0
      (P3AvP4.toP3 st ar hA hSt hm a0 (P3AvP5.toP4 st ar hA hSt hm a0 hAv))))) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localP3P4 st ar hA hSt hm a0 (P3AvP5.toP4 st ar hA hSt hm a0 hAv) h0 hA0 hK0 hU0 hM0 h hq

end vm

end
end Fl4Proofs.P2.E2EP
