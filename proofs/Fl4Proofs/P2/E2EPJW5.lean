/-
P2 (line nscope, gen 3b): **`serializable_fl4_localP3J5`: the PTE chain over `P3AvP5`'s slots with no premise
beyond the glue** — `E2EPJW`'s restriction (`QPs` in every path's `Pre`) extended to the three slots pte gen 6
discharged with `PteSl` / `vmP` [J] (`E2EPIo.io_avoidP_path`, `E2EPVm.vmF_avoidP_path` / `vmR_avoidP_path`).

* `io_avoidPJ` / `vmF_avoidPJ` / `vmR_avoidPJ`: the pte proofs, copied, under `Pre ∧ QPs` (`PteSl.1` → `QPs.ks`,
  `PteSl.2` / `vmP` → `QPs.tab`). **`vmP` [J] is gone**: vmF's `Pre` carries no bundle, but `QPs` is a start-state
  fact of every slot, so no bundle is needed.
* **`allJ5`**: every path of `fl4LocP3W`, restricted to `QPs` states, reads no PTE word, with no premise; the
  family **`fl4LocP3J5`** and **`serializable_fl4_localP3J5`**: no [W], no PTE-line [J] (`PteSl`, `VtmP`, `VxP`,
  `vmP` all replaced by the glue's start fact `QPs`, satisfiable by the choice `K.ptes ⊆ ptesJ Zx'` at the serial
  exit, `E2EPJW` module docstring). `P3AvJ` (gen 3a) is subsumed (`allJ5` proves its restricted `all` outright).

Kept as its own module so it can be re-targeted onto a later family (pte gen 7, W10). No existing statement changed.
-/
import Fl4Proofs.P2.E2EPVm
import Fl4Proofs.P2.E2EPJW
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

section vm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The I/O port's route-U path reads no PTE word**, from `PteSl` [J] (module docstring). -/
theorem io_avoidPJ_path (i : IoArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (ioSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((ioSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  have pre : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s →
      IoPre st (userV K.toKLayoutV) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac s :=
    fun s hs => ioPre_userV hK.base (vf.v hs.1).1 (h.2.pe s hs.1 hs.2)
  have preP : ∀ s, (SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) ∧ QPs K st s →
      IoPre st (userP K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac s :=
    fun s hs => ioPre_userP hK hs.2.ks (pre s hs.1)
  have hro := io_hro (K := userV K.toKLayoutV) (Locks := i.Locks) (m0 := m) hA (number := i.number)
    (P := fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) pre
  have hex : ∃ p : SProg Bool, IsProg (ioBodyP S i.number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1)) →
        PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' →
        interp st ar p s' a = ok r →
        E2E.Once st ar (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (· ∈ (userV K.toKLayoutV).user) ∅ ∅ p s' a :=
    ⟨_, io_isProg S i.number, io_noZero i.number, hro⟩
  have hIP := io_isProgOn (K := userV K.toKLayoutV) (Locks := i.Locks) (m0 := m) hA
    (P := fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) pre (io_isProg S i.number)
  refine ⟨?_, ?_, ?_⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_ioport_local st ar s a i.number = ok (true, s1, a1) := hr
    have g1 := io_acc hA (Locks := i.Locks) (pre s hs') hr'
    have g2 := io_acc hA (Locks := i.Locks) (preP s ⟨hs', hq⟩) hr'
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s (AltOf.pre hs') a
    have w1 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((e _ (Narrow.guard _ _ _)).symm.trans g2)).2
    show syscall.handle_ioport_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.number = ok (true, s1, a1)
    exact (e _ (Narrow.guard _ _ _)).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _
      ((e _ (Narrow.self _)).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_ioport_local st ar s a i.number = ok r := hr
    have h'' : syscall.handle_ioport_local st ar s' a i.number = ok r' := h'
    have hn' : r.1 ≠ true := hn
    have g := io_ra_decU hA (Locks := i.Locks) (m0 := m) (preP s ⟨hs', hq⟩) (alt_userP hAl) hr' hn' h''
    have e := fun (st' : machine.Store S) (N : Narrow st st') => hIP st' N s' ⟨s, hs', hAl⟩ a
    show syscall.handle_ioport_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.number = ok r'
    exact (e _ (Narrow.guard _ _ _)).trans (interp_mono (st := st) (fun q hq hp => hq.2 (Or.inr hp))
      (fun _ h => h) _ (io_noZero i.number) s' a r' ((e _ (Narrow.guard _ _ _)).symm.trans g))
  · intro st' N σ g a
    obtain ⟨s, hs, hAc⟩ := g
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    have hAc' : PathObl.Alt st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (OwnMap.cls (userV K.toKLayoutV)) (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s σ := hAc
    have g2 : AltOf st (fun s => (SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) ∧ QPs K st s)
        (IoRS (st := st) (userP K) i.Locks) (OwnMap.cls (userP K)) (OwnMap.ko (userP K) m) (· ∈ (userP K).user) σ :=
      ⟨s, ⟨hs', hq⟩, ⟨hAc'.cpu, hAc'.ksb, hAc'.masks,
        fun x hx => hAc'.read x ⟨⟨hx.1, fun hu => hx.2.1 (Or.inl hu), hx.2.2⟩, fun hp => hx.2.1 (Or.inr hp)⟩,
        fun x hx hu hk => hAc'.clsEq x (fun hr => hx ⟨hr.1.1, fun hu' => Or.elim hu' hr.1.2.1 hr.2, hr.1.2.2⟩)
          (fun h => hu (Or.inl h)) hk⟩⟩
    exact io_isProgOn (K := userP K) (Locks := i.Locks) (m0 := m) hA
      (P := fun s => (SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s) ∧ QPs K st s) preP
      (Classical.choose_spec hex).1 st' N σ g2 a


/-- **The VM-fault route-U path reads no PTE word**, from `PteSl` [J] and `vmP` [J]. -/
theorem vmF_avoidPJ_path (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmFSlot st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((vmFSlot st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_vm_fault_local mm ar x a i.addr i.code =
      interp mm ar (R.syscall.handle_vm_fault_local i.addr i.code) x a :=
    fun a mm x => congrFun (congrFun (vm_isProg S i.addr i.code A ar mm) x) a
  refine ⟨?_, ?_, IsProg.on (vm_isProg S i.addr i.code) _ _ _⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok (true, s1, a1) := hr
    have g1 := vm_acc (Locks := i.Locks) hA hs'.1 hs'.2.2 hr'
    have g2 := vm_acc (Locks := i.Locks) hA (vmFPre_userP hK hq.ks hs'.1) (rdTab_userP hs'.2.2 hq.tab) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_vm_fault_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.addr i.code = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok r := hr
    have h'' : syscall.handle_vm_fault_local st ar s' a i.addr i.code = ok r' := h'
    have hP := vmFPre_userP hK hq.ks hs'.1
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


/-- **The VM ReplyRecv route-U path reads no PTE word**, from `PteSl` [J]. -/
theorem vmR_avoidPJ_path (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmRSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((vmRSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
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
        i.rptr i.ep s := hs.1
    have hq : QPs K st s := hs.2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok (true, s1, a1) := hr
    have hE := VmRRPreJ.pre hs'
    have g1 := rr_vm_acc (Locks := i.Locks) hA hE.1 hE.2.2.2 hr'
    have g2 := rr_vm_acc (Locks := i.Locks) hA (vmRPre_userP hK hq.ks hE.1)
      (rdTab_userP hE.2.2.2 hq.tab) hr'
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
        i.rptr i.ep s := hs.1
    have hq : QPs K st s := hs.2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok r := hr
    have h'' : syscall.handle_reply_recv_vm_local st ar s' a (i.rptr, i.ep) = ok r' := h'
    have hE := VmRRPreJ.pre hs'
    have hEP : VmRRPre st ar (userP K) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω K.heap i.Sg (Heap.replies K.heap)
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s :=
      ⟨vmRPre_userP hK hq.ks hE.1, hE.2.1, hE.2.2.1, rdTab_userP hE.2.2.2 hq.tab⟩
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


/-- **`io_avoidP` under `QPs`** (slot lift). -/
theorem io_avoidPJ (i : IoArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (ioSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((ioSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (ioSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (io_avoidPJ_path st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **`vmF_avoidP` under `QPs`** (slot lift). -/
theorem vmF_avoidPJ (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmFSlot st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vmFSlot st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (vmFSlot st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (vmF_avoidPJ_path st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **`vmR_avoidP` under `QPs`** (slot lift). -/
theorem vmR_avoidPJ (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmRSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vmRSlotP3 st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (vmRSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (vmR_avoidPJ_path st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

end vm

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **Every path of `fl4LocP3W`, restricted to `QPs` states, reads no PTE word** (no premise). -/
theorem allJ5 :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      AvoidP K ((((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) i K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb)) := by
  intro i K m hK hU
  by_cases he : K.ptes = ∅
  · exact avoidP_empty he _
  cases i with
  | vmF i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m
    · exact vmF_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | vmR i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m
    · exact vmR_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | io i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m
    · exact io_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | st i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).st.Prem i K.toKLayoutV m
    · exact stm_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | irq i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).irq.Prem i K.toKLayoutV m
    · exact irq_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | sl i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).sl.Prem i K.toKLayoutV m
    · exact sl_avoidPJ st ar hA hSt hm a0 i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotC.noPre (fl4Dflt st ar hm) _ hp)
  | vq j =>
    cases j with
    | inl i =>
      by_cases hp : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · exact vx_avoidPJ st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)
    | inr i =>
      by_cases hp : (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · exact vt_avoidPJ st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)

/-- **FL4's eight local paths, each restricted to `QPs` states, PTE-cut and lifted to `ownP`** (no premise). -/
def fl4LocP3J5 : PathsP (E2EV.Fl4IxW (S := S)) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (allJ5 st ar hA hSt hm a0 i K m hK hU)

/-- **FL4 end to end with rules 7 and 8, `K.ptes` arbitrary, no [W] and no PTE-line [J]** (module docstring;
`E2EPJW`): every execution `ExecP` over `fl4LocP3J5` from a start with `Init`, `ArmInv`, `RegionOKP` / `UserOKP` [J]
and the maps, at a state with no local path in progress, ran exactly as some serial order of its completed entries.
Premises: only `ExecP`'s glue (`Fl4StepP`: `arm` [P]; `start` [P], each path's `Pre` including `QPs K st s`, true at
every start of the epoch for the glue's choice **`K.ptes ⊆ ptesJ Zx'`** of the serial-exit bundle ghost; `ser` with
the layout choice [P] / [J]; `HwStepP` [P]). -/
theorem serializable_fl4_localP3J5 {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3J5 st ar hA hSt hm a0) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eP _ h0 hA0 hK0 hU0 hM0 h hq

end top

end
end Fl4Proofs.P2.E2EP
