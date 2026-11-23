/-
P3 (issue #16, FL4 #71), VSpace FrameBatch: **the batch loop's state at `J`
and the per-entry interface** (KENTRY-PLAN fb3l).

* `FbKeep σ σ'`: what every batch entry keeps of the spec's state: every
  object but a CNode (same size), an arch object other than an ASID pool
  (same arch type) or a TCB's caps (`CapsOnly`); the scheduler's fields, the
  ASID table and the global PML4. Reflexive, transitive. `FbKeep.findVs`:
  the batch's `find_vspace_for_asid` outcome is kept.
* `FbFootK Z s s'`: FL4's words every batch entry keeps: the registers of
  the TCBs of `Z.T` and the mapped IPC-buffer words of `Z.B` (so the
  message's words stay readable, `syscall_arg_keep`).
* `FbMidJ`: the loop's invariant (XTopJointVsFb's `fb_loopI`): `JAtZ` at
  the decode's typed heap, the message's words, `FbKeep` from the decode's
  state.
* `FbErrOK`: an entry's error code as the loop computes it, against the
  spec's.
-/
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.XTopJointTcb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **What every batch entry keeps of the spec's state** (module docstring). -/
structure FbKeep (σ σ' : State Unit) : Prop where
  kh : ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ a a', σ.kheap p = some (.archObj a) ∧ σ'.kheap p = some (.archObj a') ∧ aaType a' = aaType a ∧
      aaType a ≠ .aASIDPool) ∨
    (∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∨
    (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ CapsOnly x y)
  ct : σ'.curThread = σ.curThread
  idle : σ'.idleThread = σ.idleThread
  cons : σ'.consumedTime = σ.consumedTime
  time : σ'.curTime = σ.curTime
  csc : σ'.curSc = σ.curSc
  isc : σ'.idleSc = σ.idleSc
  repr : σ'.reprogramTimer = σ.reprogramTimer
  act : σ'.schedulerAction = σ.schedulerAction
  dl : σ'.domainList = σ.domainList
  di : σ'.domainIndex = σ.domainIndex
  dsi : σ'.domainStartIndex = σ.domainStartIndex
  cdom : σ'.curDomain = σ.curDomain
  dt : σ'.domainTime = σ.domainTime
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  irqN : σ'.interruptIrqNode = σ.interruptIrqNode
  irqS : σ'.interruptStates = σ.interruptStates
  asidT : σ'.archState.x64AsidTable = σ.archState.x64AsidTable
  gpml4 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4

theorem FbKeep.refl (σ : State Unit) : FbKeep σ σ :=
  ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem FbKeep.trans {σ1 σ2 σ3 : State Unit} (h1 : FbKeep σ1 σ2) (h2 : FbKeep σ2 σ3) : FbKeep σ1 σ3 where
  kh p := by
    rcases h1.kh p with e1 | ⟨a, a', ha, ha', ht, hn⟩ | ⟨r, cs, cs', hc, hc'⟩ | ⟨x, y, hx, hy, hxy⟩
    · rw [← e1]; exact h2.kh p
    · rcases h2.kh p with e2 | ⟨b, b', hb, hb', ht2, -⟩ | ⟨r2, ds, ds', hd, -⟩ | ⟨x2, y2, hx2, -, -⟩
      · exact Or.inr (Or.inl ⟨a, a', ha, e2.trans ha', ht, hn⟩)
      · rw [ha'] at hb; cases hb
        exact Or.inr (Or.inl ⟨a, b', ha, hb', ht2.trans ht, hn⟩)
      · rw [ha'] at hd; cases hd
      · rw [ha'] at hx2; cases hx2
    · rcases h2.kh p with e2 | ⟨b, b', hb, -, -, -⟩ | ⟨r2, ds, ds', hd, hd'⟩ | ⟨x2, y2, hx2, -, -⟩
      · exact Or.inr (Or.inr (Or.inl ⟨r, cs, cs', hc, e2.trans hc'⟩))
      · rw [hc'] at hb; cases hb
      · rw [hc'] at hd; cases hd
        exact Or.inr (Or.inr (Or.inl ⟨r, cs, ds', hc, hd'⟩))
      · rw [hc'] at hx2; cases hx2
    · rcases h2.kh p with e2 | ⟨b, b', hb, -, -, -⟩ | ⟨r2, ds, ds', hd, -⟩ | ⟨x2, y2, hx2, hy2, hxy2⟩
      · exact Or.inr (Or.inr (Or.inr ⟨x, y, hx, e2.trans hy, hxy⟩))
      · rw [hy] at hb; cases hb
      · rw [hy] at hd; cases hd
      · rw [hy] at hx2; cases hx2
        exact Or.inr (Or.inr (Or.inr ⟨x, y2, hx, hy2, hxy.trans hxy2⟩))
  ct := h2.ct.trans h1.ct
  idle := h2.idle.trans h1.idle
  cons := h2.cons.trans h1.cons
  time := h2.time.trans h1.time
  csc := h2.csc.trans h1.csc
  isc := h2.isc.trans h1.isc
  repr := h2.repr.trans h1.repr
  act := h2.act.trans h1.act
  dl := h2.dl.trans h1.dl
  di := h2.di.trans h1.di
  dsi := h2.dsi.trans h1.dsi
  cdom := h2.cdom.trans h1.cdom
  dt := h2.dt.trans h1.dt
  rq := h2.rq.trans h1.rq
  rel := h2.rel.trans h1.rel
  irqN := h2.irqN.trans h1.irqN
  irqS := h2.irqS.trans h1.irqS
  asidT := h2.asidT.trans h1.asidT
  gpml4 := h2.gpml4.trans h1.gpml4

/-- A TCB is kept but for its caps. -/
theorem FbKeep.tcb {σ σ' : State Unit} (h : FbKeep σ σ') {t : ObjRef} {x : Tcb} (hx : σ.kheap t = some (.tcb x)) :
    ∃ y, σ'.kheap t = some (.tcb y) ∧ CapsOnly x y := by
  rcases h.kh t with e | ⟨a, a', ha, -⟩ | ⟨r, cs, cs', hc, -⟩ | ⟨x2, y, hx2, hy, hxy⟩
  · exact ⟨x, e.trans hx, CapsOnly.refl x⟩
  · rw [hx] at ha; cases ha
  · rw [hx] at hc; cases hc
  · rw [hx] at hx2; cases hx2; exact ⟨y, hy, hxy⟩

/-- A state whose object at `pp` is no ASID pool has no outcome of `getAsidPool pp`. -/
theorem getAsidPool_none {σ : State Unit} {pp : ObjRef} (hk : ∀ f, σ.kheap pp ≠ some (.archObj (.asidPool f))) :
    (getAsidPool (Z := Unit) pp σ).1 = ∅ := by
  unfold getAsidPool getObject NonDet.getsThe readObject
  show (NonDet.bind _ _ σ).1 = ∅
  unfold NonDet.bind
  cases hkp : σ.kheap pp with
  | none =>
    ext r
    simp only [hkp, NonDet.assertOpt, NonDet.fail, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, hx, -⟩; exact hx
  | some o =>
    ext r
    simp only [hkp, NonDet.assertOpt, NonDet.pure, Set.mem_singleton_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    rintro ⟨x, rfl, hr⟩
    dsimp only at hr
    cases o <;> (try simp [NonDet.fail] at hr)
    rename_i ao
    cases ao <;> (try simp [NonDet.fail] at hr)
    exact hk _ hkp

/-- **A successful `find_vspace_for_asid`'s table entry and pool.** -/
theorem findVs_pool {σ : State Unit} {a : Asid} {p : ObjRef} (h0 : a > 0)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) a) σ = ({(.ok p, σ)}, False)) :
    ∃ pp f, σ.archState.x64AsidTable (asidHighBitsOf a) = some pp ∧ σ.kheap pp = some (.archObj (.asidPool f)) ∧
      nativeAsidRoot (f (asidLowBitsOf a)) = some p := by
  cases ht : σ.archState.x64AsidTable (asidHighBitsOf a) with
  | none =>
    rw [findVspaceForAsid_none h0 ht] at hf
    have := congrArg Prod.fst hf
    simp at this
  | some pp =>
    by_cases hk : ∃ f, σ.kheap pp = some (.archObj (.asidPool f))
    · obtain ⟨f, hk⟩ := hk
      rw [findVspaceForAsid_some h0 ht hk] at hf
      refine ⟨pp, f, rfl, hk, ?_⟩
      cases hn : nativeAsidRoot (f (asidLowBitsOf a)) with
      | none => rw [hn] at hf; have := congrArg Prod.fst hf; simp at this
      | some r => rw [hn] at hf; have := congrArg Prod.fst hf; simp at this; rw [this]
    · exfalso
      have hg := getAsidPool_none (fun f e => hk ⟨f, e⟩)
      unfold findVspaceForAsid NonDetE.assertE at hf
      rw [runE_bind_ok (runE_liftE (assert_true' h0 σ)), runE_bind_ok (runE_liftE (show NonDet.gets _ σ = _ from rfl))]
        at hf
      simp only [ht] at hf
      rw [runE_bind_ok (show ExceptT.run (NonDetE.returnOk (some pp)) σ = _ from rfl)] at hf
      dsimp only at hf
      have hz : ∀ (k : (AsidLowIndex → Option ObjRef) → NonDetE (State Unit) LookupFailure ObjRef),
          (ExceptT.run (NonDetE.liftE (ε := LookupFailure) (getAsidPool (Z := Unit) pp) >>= k) σ).1 = ∅ := by
        intro k
        show (NonDet.bind (ExceptT.run (NonDetE.liftE (ε := LookupFailure) (getAsidPool (Z := Unit) pp)))
          (ExceptT.bindCont k) σ).1 = ∅
        have he : (ExceptT.run (NonDetE.liftE (ε := LookupFailure) (getAsidPool (Z := Unit) pp)) σ).1 = ∅ := by
          show (NonDet.bind _ _ σ).1 = ∅
          unfold NonDet.bind
          simp [hg]
        unfold NonDet.bind
        simp [he]
      have h1 := congrArg Prod.fst hf
      rw [hz] at h1
      exact Set.singleton_ne_empty _ h1.symm

/-- **`FbKeep` keeps the batch's `find_vspace_for_asid`.** -/
theorem FbKeep.findVs {σ σ' : State Unit} (h : FbKeep σ σ') {a : Asid} {p : ObjRef} (h0 : a > 0)
    (hf : ExceptT.run (findVspaceForAsid (Z := Unit) a) σ = ({(.ok p, σ)}, False)) :
    ExceptT.run (findVspaceForAsid (Z := Unit) a) σ' = ({(.ok p, σ')}, False) := by
  obtain ⟨pp, f, ht, hk, hr⟩ := findVs_pool h0 hf
  have hk' : σ'.kheap pp = some (.archObj (.asidPool f)) := by
    rcases h.kh pp with e | ⟨a1, a', ha, -, -, hn⟩ | ⟨r, cs, cs', hc, -⟩ | ⟨x, y, hx, -, -⟩
    · exact e.trans hk
    · rw [hk] at ha; cases ha; exact absurd rfl hn
    · rw [hk] at hc; cases hc
    · rw [hk] at hx; cases hx
  rw [findVspaceForAsid_some h0 ((congrFun h.asidT _).trans ht) hk', hr]

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop}

/-- **FL4's words every batch entry keeps** (module docstring). -/
def FbFootK (Z : XSets) (s s' : S) : Prop :=
  (∀ t ∈ Z.T, ∀ g : Fl4Spec.Register, L.mem s' (regA t (regIdx g)) = L.mem s (regA t (regIdx g))) ∧
    ∀ wp ∈ Z.B, L.mem s' wp.1 = L.mem s wp.1

/-- **The state the batch's loop carries** (KENTRY-PLAN fb3k, fb3l): `JAtZ` at the decode's typed
heap `th0`, the message words still readable (the batch writes no register or IPC-buffer word of
`ct`), and `FbKeep` from the decode's state `σ` (so the current thread, its thread state and the
batch's `find_vspace_for_asid` are kept). -/
def FbMidJ (σ : Fl4Spec.State Unit) (th0 : TypedHeap) (ct buf : U64) (args : List U64) (x : S) (a : A)
    (τ : Fl4Spec.State Unit) : Prop :=
  (∃ (Z1 : XSets) (H1 : P1.Heap) (Cs1 Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
    Z1.th = th0 ∧ ct ∈ Z1.T ∧ (buf ≠ 0#u64 → ∃ sp, BufMap Z1.B buf sp) ∧
    JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 x a τ) ∧
  (∀ (i : U64) v, args[i.val]? = some v → msg.syscall_arg st x ct buf i = ok v) ∧
  FbKeep σ τ

/-- **`FbMidJ` across one batch step** (the bridge for the per-entry lemmas): from `FbMidJ` at
`JAtZ`'s sets `Z1`, a step to `JAtZ` at sets `Z2` of the same typed heap, TCBs and buffer words,
FL4's step keeping `FbFootK` (at `Z1`) and the spec's `FbKeep`. -/
theorem FbMidJ.step {σ : Fl4Spec.State Unit} {th0 : TypedHeap} {ct buf : U64} {args : List U64}
    {x x' : S} {a a' : A} {τ τ' : Fl4Spec.State Unit} {Z1 Z2 : XSets} {H1 H2 : P1.Heap} {Cs1 Cs2 Ac1 Ac2 : Set U64}
    {Lst1 Lst2 : U64 → List U64} {D1 D2 : Set U64}
    (hal : args.length < 127)
    (hth : Z1.th = th0) (hct : ct ∈ Z1.T) (hbm : buf ≠ 0#u64 → ∃ sp, BufMap Z1.B buf sp)
    (hargs : ∀ (i : U64) v, args[i.val]? = some v → msg.syscall_arg st x ct buf i = ok v)
    (hK : FbKeep σ τ)
    (J2 : JAtZ (L := L) arI AR Z2 H2 Cs2 Ac2 Lst2 D2 x' a' τ')
    (hth2 : Z2.th = Z1.th) (hT2 : Z2.T = Z1.T) (hB2 : Z2.B = Z1.B)
    (hF : FbFootK (L := L) Z1 x x') (hK' : FbKeep τ τ') :
    FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args x' a' τ' := by
  refine ⟨⟨Z2, H2, Cs2, Ac2, Lst2, D2, hth2.trans hth, hT2 ▸ hct, fun h => hB2 ▸ hbm h, J2⟩, ?_, hK.trans hK'⟩
  intro i v hv
  rw [← hargs i v hv]
  apply syscall_arg_keep
  · exact hF.1 ct hct
  · intro hb0
    obtain ⟨sp, hsp⟩ := hbm hb0
    have hi : i.val < args.length := (List.getElem?_eq_some_iff.1 hv).1
    have hi1 : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
      have := i.hBounds
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this ⊢
      omega
    exact hF.2 _ (hsp _ (by rw [hi1]; omega))

/-- A failing entry's code as the loop computes it, against the spec's. -/
def FbErrOK (b : Fl4Spec.Fl4FrameBatchInvocation) (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data)
    (τ τ1 : Fl4Spec.State Unit) : error.Exc → Prop
  | .Sys e1 => error.SysError.code e1 ⦃ c => (.error c.bv, τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b w).run τ).1 ⦄
  | _ => (.error fl4_abi.consts.error.IllegalOperation.bv, τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b w).run τ).1

/-- **The decode's facts every entry uses** (proved at the decode, XTopJointVsFb's `fbCtx_of`):
FL4's batch record `bt` against the spec's `b`, the batch's `find_vspace_for_asid` at the decode's
state `σ`, the CNode caps valid at the decode's typed heap `th0`, the message short. -/
structure FbCtx (σ : Fl4Spec.State Unit) (th0 : TypedHeap) (args : List U64) (bt : vspace.Batch)
    (b : Fl4Spec.Fl4FrameBatchInvocation) : Prop where
  ni : Entered σ
  h0 : bt.asid ≠ 0#u64
  hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) bt.asid.bv) σ = ({(.ok bt.root.bv, σ)}, False)
  hbv : b.vspace = bt.root.bv
  hba : b.asid = bt.asid.bv
  hdep : b.depth = bt.depth.val
  hdep1 : 1 ≤ bt.depth.val ∧ bt.depth.val ≤ 64
  hmr : b.mapRights = bt.map_rights.bv
  hcr : b.capRights = bt.cap_rights.bv
  hat : b.attr = bt.attr.bv
  hdd : b.deferDelete = bt.defer_delete
  hopC : bt.op = vspace.frame_batch.COPY_MAP ↔ b.op = .copyMap
  hopR : bt.op = vspace.frame_batch.REMAP ↔ b.op = .remap
  hbc : b.cnode = absCap bt.cnode
  hbd : b.destCnode = absCap bt.dest_cnode
  hcnC : ∃ a b d e, bt.cnode = .CNode a b d e
  hdcC : ∃ a b d e, bt.dest_cnode = .CNode a b d e
  hcv : CapValid th0 bt.cnode
  hdcv : CapValid th0 bt.dest_cnode
  hcw : CapWf bt.cnode
  hdcw : CapWf bt.dest_cnode
  hal : args.length < 127
  /-- The batch's ASID is a 20-bit ASID (the PML4 cap's `VCapOK`; a mapped frame cap's `EncWf`). -/
  hasid : bt.asid.val < 2 ^ 20

/-- **What one entry leaves** (XTopJointVsFb's `fb_entryJ`): `FbMidJ` after at a spec state `τ1`, and
either an `Ok` with an `ok d'` outcome of the spec's `fbEntry` (the deferred flag `df || d'`) or an
error with an error outcome of the same code (`FbErrOK`), the flag kept. -/
def FbEntryPost (σ : Fl4Spec.State Unit) (th0 : TypedHeap) (ct buf : U64) (args : List U64)
    (b : Fl4Spec.Fl4FrameBatchInvocation) (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data) (τ : Fl4Spec.State Unit)
    (df : Bool) (r : core.result.Result Unit error.Exc × S × A × Bool) : Prop :=
  ∃ τ1, FbMidJ (L := L) (AR := AR) arI σ th0 ct buf args r.2.1 r.2.2.1 τ1 ∧
    ((r.1 = .Ok () ∧ ∃ d', (.ok d', τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b w).run τ).1 ∧ r.2.2.2 = (df || d')) ∨
      (∃ e, r.1 = .Err e ∧ r.2.2.2 = df ∧ FbErrOK b w τ τ1 e))

end

/-- Reduce a tuple-`let` continuation applied to a pair (MachKeepG4d's `fb_red`). -/
macro "fbj_red" : tactic =>
  `(tactic| ((try simp only [WP.uncurry'_pair]) <;> (try simp only [uncurry_apply_pair]) <;> (try simp only [Aeneas.Std.uncurry]) <;> (try dsimp only)))

end

end Fl4Proofs.P3
