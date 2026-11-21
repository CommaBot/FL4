/-
P3 (DESIGN.md §9), invariant line G1 (g5c): **the cap half `HI S` across the
cap writers whose caps come from slots** (spec side only; outside the `JAtZ`
cone; vih3's SpecInvValidIrqHandlersY with `HI S` for `VH R`).

* `hi_setIrqState`, the ack's machine op, `deleted_irq_handler`: no cap write.
* `hi_okv_lookupCap` / `hi_okv_lookupExtraCaps`: a looked-up cap is `IoIn S`
  when `HI S` holds at the lookup (vih3's `OkV`); `ioIn_deriveCap`: `derive_cap`
  returns the cap itself or a cap that is no IO-port cap.
* IPC: `hi_transferCapsLoop` / `hi_transferCaps` (every transferred cap
  `IoIn S`), `hi_doNormalTransfer`.
* `hi_checkCapAt_ins` (the TCB installs re-read the source slot: an IO-port cap
  `same_object_as` the new cap is the new cap), `hi_setCap_bind_dead` + the page
  / page-table maps, `hi_performAsidControlInvocation` (the parent cap re-read),
  `hi_capDeleteOne`, `hi_deletingIrqHandler`, `hi_finaliseCap`.
-/
import Fl4Proofs.P3.SpecInvIoPortsW
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

variable {S : IoSet}

/-! ## Writers of no cap outside the frames -/

theorem hi_setIrqState (st : IrqState) (i : Irq) : IKH (HI S) (setIrqState (Z := Unit) st i) := by
  intro σ h x hx f l hh
  obtain ⟨hk, -⟩ := setIrqState_out hx
  obtain ⟨p, cref, hc⟩ := hh
  exact h f l ⟨p, cref, by rw [← hk]; exact hc⟩

theorem hi_dmo {α : Type} (mop : NonDet MachineState α) : IKH (HI S) (doMachineOp (Z := Unit) mop) :=
  ik_doMachineOp (fun _ _ h => h) mop

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_setIrqState _ _)
macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_dmo _)

theorem hi_capDeleteOne (sl : CslotPtr) : IKH (HI S) (capDeleteOne (Z := Unit) sl) := by
  unfold capDeleteOne emptySlot
  simp only [postCapDeletion]
  hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_capDeleteOne _)

theorem hi_deletingIrqHandler (irq : Irq) : IKH (HI S) (deletingIrqHandler (Z := Unit) irq) := by
  unfold deletingIrqHandler; hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_deletingIrqHandler _)

theorem hi_finaliseCap (c : Cap) (fin : Bool) : IKH (HI S) (finaliseCap (Z := Unit) c fin) := by
  cases c <;> unfold finaliseCap <;> hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_finaliseCap _ _)

/-! ## Looked-up caps -/

theorem hi_of_hV {σ σ' : State Unit} (e : hV σ' = hV σ) (h : HI S σ) : HI S σ' :=
  fun f l hh => h f l (by rw [has_of_hV e] at hh; exact hh)

theorem hi_okv_lookupCap {σ0 : State Unit} (hv : HI S σ0) (t : ObjRef) (c : CapRef) (cp : ObjRef) (rp : Bool) :
    OkV σ0 (fun r : Cap × CslotPtr => IoIn S r.1) (capFaultOnFailure (Z := Unit) cp rp (lookupCapAndSlot t c)) := by
  intro s hs a s' h
  have e : hV s' = hV s :=
    hv_capFaultOnFailure (P := fun x => hV x = hV s) cp rp _ (hv_lookupCapAndSlot t c) s rfl _ h
  have hc := okdAt_capFault cp rp (okCap_lookupCapAndSlot t c s) a s' h
  have e' := e.trans hs
  exact ⟨e', ioIn_of_slot (hi_of_hV e' hv) hc⟩

theorem hi_okv_lookupExtraCaps {σ0 : State Unit} (hv : HI S σ0) (t : ObjRef) (b : Option Data) (mi : MessageInfo) :
    OkV σ0 (fun caps : List (Cap × CslotPtr) => ∀ c ∈ caps, IoIn S c.1) (lookupExtraCaps (Z := Unit) t b mi) := by
  unfold lookupExtraCaps
  exact okv_bind (okv_frame fun v => ike_liftE (P := fun s => hV s = v) (hv_getExtraCptrs _ _)) fun cptrs _ =>
    okv_mapME (fun _ => hi_okv_lookupCap hv _ _ _ _) cptrs

theorem ioIn_deriveCap {sl : CslotPtr} {c c' : Cap} {σ s : State Unit} (hc : IoIn S c)
    (h : ((.ok c', s) : Except SyscallError Cap × State Unit) ∈ ((deriveCap (Z := Unit) sl c).run σ).1) :
    IoIn S c' := by
  have key : OkV σ (fun c' => IoIn S c') (deriveCap (Z := Unit) sl c) := by
    cases c with
    | archObjectCap a =>
      simp only [deriveCap]; unfold archDeriveCap
      split <;> first
        | exact okv_throw _
        | exact okv_returnOk hc
        | exact okv_returnOk (ioIn_noIo (fun _ _ h => by cases h) _)
        | exact okv_returnOk (ioIn_noIo (fun _ _ h => by simp_all) _)
    | untypedCap d b n f =>
      simp only [deriveCap]
      exact okv_bind (okv_frame fun v => hv_ensureNoChildren (P := fun s => hV s = v) _) fun _ _ => okv_returnOk hc
    | zombie => simp only [deriveCap]; exact okv_returnOk (ioIn_noIo (fun _ _ h => by cases h) _)
    | irqControlCap => simp only [deriveCap]; exact okv_returnOk (ioIn_noIo (fun _ _ h => by cases h) _)
    | _ => simp only [deriveCap]; exact okv_returnOk hc
  exact (key σ rfl c' s h).2

/-! ## IPC cap transfer -/

theorem hi_transferCapsLoop (ep : Option ObjRef) (rb : ObjRef) :
    ∀ (n : Nat) (caps : List (Cap × CslotPtr)) (sl : List CslotPtr) (mi : MessageInfo),
      (∀ c ∈ caps, IoIn S c.1) → IKH (HI S) (transferCapsLoop (Z := Unit) ep rb n caps sl mi)
  | n, [], sl, mi, _ => by unfold transferCapsLoop; exact ik_pure _
  | n, (c, s) :: cs, sl, mi, hR => by
    have ih := fun sl' mi' hR' => hi_transferCapsLoop ep rb (n + 1) cs sl' mi' hR'
    have hR1 : ∀ c' ∈ cs, IoIn S c'.1 := fun c' hc' => hR c' (List.mem_cons_of_mem _ hc')
    unfold transferCapsLoop constOnFailure
    refine ik_catch ?_ (fun _ => ik_pure' _)
    refine ike_returnOk_bind ?_
    split
    · exact ike_bind (ike_liftE (hv_setExtraBadge _ _ _)) fun _ => ike_liftE (ih _ _ hR1)
    · split
      · intro σ h x hx
        obtain ⟨z, hz, ⟨c', hc', hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
        · obtain ⟨r, s1⟩ := z
          simp only at hc'; subst hc'
          have hs1 : HI S s1 := hv_deriveCap (P := HI S) _ _ σ h _ hz
          have hca : IoIn S c' := ioIn_deriveCap (hR (c, s) (List.mem_cons_self ..)) hz
          exact (show IKHE (HI S) _ from by
            refine ike_bind (ike_whenE _ (ike_throw _)) fun _ =>
              ike_bind (ike_liftE (hi_capInsert _ _ _ hca)) fun _ =>
              ike_liftE (ih _ _ hR1)) s1 hs1 x hx
        · exact hv_deriveCap (P := HI S) _ _ σ h _ hz
      · exact ike_returnOk _

theorem hi_transferCaps (info : MessageInfo) (caps : List (Cap × CslotPtr)) (ep : Option ObjRef) (r : ObjRef)
    (rb : Option ObjRef) (hR : ∀ c ∈ caps, IoIn S c.1) :
    IKH (HI S) (transferCaps (Z := Unit) info caps ep r rb) := by
  unfold transferCaps
  refine ik_bind (hv_getReceiveSlots _ _) fun _ => ik_pure_bind ?_
  split
  · exact ik_pure _
  · exact hi_transferCapsLoop _ _ _ _ _ _ hR

theorem hi_doNormalTransfer (sender : ObjRef) (sbuf ep : Option ObjRef) (badge : Data) (grant : Bool)
    (receiver : ObjRef) (rbuf : Option ObjRef) :
    IKH (HI S) (doNormalTransfer (Z := Unit) sender sbuf ep badge grant receiver rbuf) := by
  unfold doNormalTransfer
  refine ik_bind (hv_getMessageInfo _) fun mi => ?_
  dsimp only
  have carry : ∀ {β : Type} {m : NonDet (State Unit) (List (Cap × CslotPtr))} {k : List (Cap × CslotPtr) → NonDet (State Unit) β},
      (∀ σ, HI S σ → ∀ y ∈ (m σ).1, HI S y.2 ∧ ∀ c ∈ y.1, IoIn S c.1) →
      (∀ caps, (∀ c ∈ caps, IoIn S c.1) → IKH (HI S) (k caps)) → IKH (HI S) (m >>= k) := by
    intro β m k hm hk σ h x ⟨y, hy, hx⟩
    exact hk y.1 (hm σ h y hy).2 y.2 (hm σ h y hy).1 x hx
  split
  all_goals refine carry ?_ (fun caps hc => ?_)
  · intro σ h y hy
    unfold NonDetE.catch at hy
    obtain ⟨z, hz, hy⟩ := hy
    obtain ⟨r, s⟩ := z
    have hs : HI S s := hv_lookupExtraCaps (P := HI S) _ _ _ σ h _ hz
    cases r with
    | ok a =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, (hi_okv_lookupExtraCaps h _ _ _ σ rfl a s hz).2⟩
    | error e =>
      obtain rfl := Set.mem_singleton_iff.1 hy
      exact ⟨hs, fun c hc => by cases hc⟩
  · exact ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (hi_transferCaps _ _ _ _ _ hc) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _
  · intro σ h y hy
    obtain rfl := Set.mem_singleton_iff.1 hy
    exact ⟨h, fun c hc => by cases hc⟩
  · exact ik_bind (hv_copyMrs _ _ _ _ _) fun _ => ik_bind (hi_transferCaps _ _ _ _ _ hc) fun _ =>
      ik_bind (hv_setMessageInfo _ _) fun _ => hv_asUser _ _

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_doNormalTransfer _ _ _ _ _ _ _)

/-! ## TCB installs, page maps, ASID control -/

theorem sameObjectAs_io {f l : IoPort} {c : Cap} (h : sameObjectAs (.archObjectCap (.ioPortCap f l)) c) :
    c = .archObjectCap (.ioPortCap f l) := by
  cases c <;> simp_all [sameObjectAs, sameRegionAs]
  all_goals first | done | (rename_i a; cases a <;> simp_all [sameAobjectAs, archSameRegionAs])

theorem hi_checkCapAt_ins (nc : Cap) (src : CslotPtr) (t : ObjRef) (sl dst : CslotPtr) :
    IKH (HI S) (checkCapAt (Z := Unit) nc src (checkCapAt (.threadCap t) sl (capInsert nc src dst))) := by
  unfold checkCapAt
  refine ik_getCap_bind fun c' σ hc' => ?_
  unfold NonDet.when
  split
  · rename_i hso
    intro h
    have hca : IoIn S nc := fun f l e => by
      subst e
      exact ioIn_of_slot h ((sameObjectAs_io hso) ▸ hc') f l rfl
    exact (ik_bind (hv_getCap _) fun _ => ik_ite _ (hi_capInsert _ _ _ hca) (ik_pure _)) σ h
  · exact ikp_of_ik (ik_pure _) σ

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_checkCapAt_ins _ _ _ _ _)

theorem hi_setCap_bind_dead {β : Type} (cap : Cap) (sl : CslotPtr) {k : Unit → NonDet (State Unit) β}
    (hk : ∀ a, IKH (HI S) (k a))
    (hd : ∀ f l, cap = .archObjectCap (.ioPortCap f l) → ∀ a σ x, x ∈ (k a σ).1 → False) :
    IKH (HI S) (setCap (Z := Unit) cap sl >>= k) := by
  intro σ h x ⟨y, hy, hx⟩
  by_cases hc : ∃ f l, cap = .archObjectCap (.ioPortCap f l)
  · obtain ⟨f, l, e⟩ := hc; exact (hd f l e _ _ x hx).elim
  · exact hk _ _ (hi_setCap cap sl (ioIn_noIo (fun f l e => hc ⟨f, l, e⟩) S) σ h y hy) x hx

/-- The dead continuation: the second bind's head fails. -/
macro "io_dead_k" : tactic => `(tactic| (intro _ _ e _ _ x hx; subst e; obtain ⟨_, _, _, hf, _⟩ := hx; first | exact hf | (simp [NonDet.fail] at hf) | cases hf))

/-- The same with the map entry matched first (the page map). -/
macro "io_dead_k2" : tactic => `(tactic| (intro _ _ e _ _ x hx; subst e; revert hx; split <;> (intro hx; obtain ⟨_, _, hx⟩ := hx; obtain ⟨_, hf, _⟩ := hx; first | exact hf | cases hf)))

/-- The slot holds the cap (the unmaps' decode fact: the invoked slot holds the invoked cap). -/
def AtSl (sl : CslotPtr) (c : Cap) (σ : State Unit) : Prop := capOpt (σ.kheap sl.1) sl.2 = some c

instance (sl : CslotPtr) (c : Cap) : WLH (AtSl sl c) :=
  wlh_of_hV fun _ _ e h => by unfold AtSl; rw [hV_cap e]; exact h

/-- The unmaps' tail: the slot's cap re-read and written back with its mapping cleared. When the
slot holds a page / table cap `pc`, the written cap is no IO-port cap. -/
theorem hi_unmapTail (pc : ArchCap) (hpc : ∀ m mt f l, updateMapData pc m mt ≠ .ioPortCap f l) (sl : CslotPtr)
    (m : Option (Asid × VSpaceRef)) (mt : Option VMMapType) (σ : State Unit) (h : HI S σ)
    (hat : AtSl sl (.archObjectCap pc) σ) :
    ∀ x ∈ ((NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
      setCap (Z := Unit) (.archObjectCap (updateMapData cap m mt)) sl) σ).1, HI S x.2 := by
  obtain ⟨o, r⟩ := sl
  intro x ⟨y, hy, hx⟩
  unfold NonDet.liftM at hy
  obtain ⟨z, hz, hy⟩ := hy
  obtain ⟨e1, e2⟩ := vih_mem_getCap hz
  have h2 : capOpt (σ.kheap o) r = some (.archObjectCap pc) := hat
  have ez : z.1 = .archObjectCap pc := by rw [h2] at e2; exact (Option.some.inj e2).symm
  obtain rfl := Set.mem_singleton_iff.1 hy
  have hs : HI S z.2 := by rw [e1]; exact h
  dsimp only at hx
  simp only [ez, Cap.theArchCap] at hx
  exact hi_setCap _ _ (ioIn_noIo (fun f l e => hpc m mt f l (Cap.archObjectCap.inj e)) S) z.2 hs x hx

/-- From a `Q` state every outcome has `HI S` (an unmap's pinned frame: `Q` holds the slot's cap). -/
def QH (Q : State Unit → Prop) {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ σ, Q σ → ∀ x ∈ (m σ).1, HI S x.2

theorem qh_bind {Q : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : IKH Q m) (hk : ∀ a, QH (S := S) Q (k a)) : QH (S := S) Q (m >>= k) := by
  intro σ h x hx
  obtain ⟨y, hy, hx⟩ := hx
  exact hk y.1 y.2 (hm σ h y hy) x hx

theorem qh_tail (pc : ArchCap) (hpc : ∀ m mt f l, updateMapData pc m mt ≠ .ioPortCap f l) (sl : CslotPtr)
    (m : Option (Asid × VSpaceRef)) (mt : Option VMMapType) :
    QH (S := S) (fun σ => HI S σ ∧ AtSl sl (.archObjectCap pc) σ)
      (NonDet.liftM Cap.theArchCap (getCap (Z := Unit) sl) >>= fun cap =>
        setCap (Z := Unit) (.archObjectCap (updateMapData cap m mt)) sl) :=
  fun σ h => hi_unmapTail pc hpc sl m mt σ h.1 h.2

theorem qh_bind' {Q : State Unit → Prop} {α β : Type} {m : NonDet (State Unit) α} {k : α → NonDet (State Unit) β}
    (hm : QH (S := S) Q m) (hk : ∀ a, IKH (HI S) (k a)) : QH (S := S) Q (m >>= k) := by
  intro σ h x hx
  obtain ⟨y, hy, hx⟩ := hx
  exact hk y.1 y.2 (hm σ h y hy) x hx

macro "qh_auto" : tactic => `(tactic| repeat' (first
  | exact qh_tail _ (by intro m mt f l e; simp [updateMapData] at e) _ _ _
  | (refine qh_bind (by hv_auto) fun _ => ?_)
  | split))

theorem hi_ppiu (dev : Bool) (b : ObjRef) (R : CapRights) (mt : VMMapType) (sz : VMPageSize)
    (mp : Option (Asid × VSpaceRef)) (sl : CslotPtr) (σ : State Unit)
    (hat : AtSl sl (.archObjectCap (.pageCap dev b R mt sz mp)) σ) :
    IKp (HI S) σ (performPageInvocationUnmap (Z := Unit) (.pageCap dev b R mt sz mp) sl) := by
  simp only [performPageInvocationUnmap]
  intro h
  exact (show QH (S := S) (fun σ => HI S σ ∧ AtSl sl (.archObjectCap (.pageCap dev b R mt sz mp)) σ) _ from by
    qh_auto) σ ⟨h, hat⟩

/-- The page perform; an unmap needs its slot to hold its cap. -/
theorem hi_performPageInvocation (iv : PageInvocation) (σ : State Unit)
    (hp : ∀ c sl, iv = .pageUnmap c sl → AtSl sl (.archObjectCap c) σ) :
    IKp (HI S) σ (performPageInvocation (Z := Unit) iv) := by
  cases iv with
  | pageMap cap sl ent vs =>
    simp only [performPageInvocation]
    exact ikp_of_ik (hi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by io_dead_k2)) σ
  | pageUnmap c sl =>
    have hat := hp c sl rfl
    by_cases hc : ∃ dev b R mt sz mp, c = .pageCap dev b R mt sz mp
    · obtain ⟨dev, b, R, mt, sz, mp, rfl⟩ := hc
      simp only [performPageInvocation]
      intro h
      refine (show QH (S := S) (fun σ => HI S σ ∧ AtSl sl (.archObjectCap (.pageCap dev b R mt sz mp)) σ) _
        from ?_) σ ⟨h, hat⟩
      repeat' (first
        | exact qh_bind' (fun σ h => hi_ppiu _ _ _ _ _ _ _ σ h.2 h.1) (fun _ => ik_pure _)
        | exact qh_bind' (fun _ _ x hx => hx.elim) (fun _ => ik_pure _)
        | exact qh_bind' (fun σ h x hx => by rw [Set.mem_singleton_iff.1 hx]; exact h.1) (fun _ => ik_pure _)
        | exact fun _ _ x hx => hx.elim
        | exact fun σ h x hx => by rw [Set.mem_singleton_iff.1 hx]; exact h.1
        | split)
    · simp only [performPageInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact fun _ x hx => hx.elim
  | pageGetAddr p => simp only [performPageInvocation]; exact ikp_of_ik (by hv_auto) σ

theorem hi_performPageTableInvocation (iv : PageTableInvocation) (σ : State Unit)
    (hp : ∀ c sl, iv = .pageTableUnmap c sl → AtSl sl c σ) :
    IKp (HI S) σ (performPageTableInvocation (Z := Unit) iv) := by
  cases iv with
  | pageTableMap cap sl pde pd vs =>
    simp only [performPageTableInvocation]
    exact ikp_of_ik (hi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by io_dead_k)) σ
  | pageTableUnmap c sl =>
    have hat := hp c sl rfl
    by_cases hc : ∃ p ma, c = .archObjectCap (.pageTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hc
      simp only [performPageTableInvocation]
      intro h
      exact (show QH (S := S) (fun σ => HI S σ ∧ AtSl sl (.archObjectCap (.pageTableCap p ma)) σ) _ from by
        qh_auto) σ ⟨h, hat⟩
    · simp only [performPageTableInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact fun _ x hx => hx.elim

theorem hi_performPageDirectoryInvocation (iv : PageDirectoryInvocation) (σ : State Unit)
    (hp : ∀ c sl, iv = .pageDirectoryUnmap c sl → AtSl sl c σ) :
    IKp (HI S) σ (performPageDirectoryInvocation (Z := Unit) iv) := by
  cases iv with
  | pageDirectoryMap cap sl pde pd vs =>
    simp only [performPageDirectoryInvocation]
    exact ikp_of_ik (hi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by io_dead_k)) σ
  | pageDirectoryUnmap c sl =>
    have hat := hp c sl rfl
    by_cases hc : ∃ p ma, c = .archObjectCap (.pageDirectoryCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hc
      simp only [performPageDirectoryInvocation]
      intro h
      exact (show QH (S := S) (fun σ => HI S σ ∧ AtSl sl (.archObjectCap (.pageDirectoryCap p ma)) σ) _ from by
        qh_auto) σ ⟨h, hat⟩
    · simp only [performPageDirectoryInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact fun _ x hx => hx.elim

theorem hi_performPdptInvocation (iv : PdptInvocation) (σ : State Unit)
    (hp : ∀ c sl, iv = .pdptUnmap c sl → AtSl sl c σ) :
    IKp (HI S) σ (performPdptInvocation (Z := Unit) iv) := by
  cases iv with
  | pdptMap cap sl pde pd vs =>
    simp only [performPdptInvocation]
    exact ikp_of_ik (hi_setCap_bind_dead _ _ (fun _ => by hv_auto) (by io_dead_k)) σ
  | pdptUnmap c sl =>
    have hat := hp c sl rfl
    by_cases hc : ∃ p ma, c = .archObjectCap (.pdPointerTableCap p ma)
    · obtain ⟨p, ma, rfl⟩ := hc
      simp only [performPdptInvocation]
      intro h
      exact (show QH (S := S) (fun σ => HI S σ ∧ AtSl sl (.archObjectCap (.pdPointerTableCap p ma)) σ) _ from by
        qh_auto) σ ⟨h, hat⟩
    · simp only [performPdptInvocation]
      split
      all_goals first | (exfalso; simp_all; done) | exact fun _ x hx => hx.elim

theorem ioIn_freeIndexUpdate {c : Cap} (h : IoIn S c) (g : Nat → Nat) : IoIn S (freeIndexUpdate g c) := by
  intro f l e; apply h f l; cases c <;> simp_all [freeIndexUpdate]

theorem hi_performAsidControlInvocation (iv : AsidControlInvocation) :
    IKH (HI S) (performAsidControlInvocation (Z := Unit) iv) := by
  cases iv with
  | makePool frame slot parent base =>
    simp only [performAsidControlInvocation]
    refine ik_bind (hi_deleteObjects _ _) fun _ => ik_getCap_bind fun pcap σ hp => ?_
    intro h
    refine ikp_bind (hi_setCap_p _ _ σ fun h' => ioIn_freeIndexUpdate (ioIn_of_slot h' hp) _) (fun _ => ?_) h
    hv_auto

macro_rules | `(tactic| hv_leaf) => `(tactic| with_reducible exact hi_performAsidControlInvocation _)

end

end Fl4Proofs.P3.SInvIo
