/-
# P2 (line p3mc, gen 26): the timer interrupt's certificate at a view start whose notification wakes a thread of `c`

Handoff §30c (W-h): the irq starts whose earliest thread `tm` of `c`'s timer tree is, in `ρ`, on `c`, and whose
bound notification, in `ρ`, wakes somebody (`¬ NoWakeR`) with its head waiter, when it is waiting, on `c`
(`IrqWhR`). With U21–U23 these are all the irq starts (`irqWh_cover`, P2/E2EPU24).

The waking chain (P2/FootTimerFire*) asks its permissions over classes read at its entry state ("threads with
`AFFINITY` = the core", "SCs with `CORE` = the core", queued threads on a held object). At the view start `σ` the
view rewrites every `AFFINITY` / `CORE` to `c`, so these classes hold other cores' objects whose words the view does
not keep. P2/IrqWhW, IrqWhA, IrqWhS, IrqWhG are the chain with those classes cut by `Hm` / `Hs`; here `Hm y` is
"`y` is homed on `c` in `ρ`" and `Hs p` "`p` is homed on `c` in `ρ`", whose words are kept (`sr_tcb`, `srw_sc`).
The chain's `Hm` obligations hold at `σ`: a thread runnable at the view, or with an SC, is homed in `ρ`
(`view_hidden_home`, `view_tzero_home`), a bound SC is homed through its `TCB` word, the due thread and the waiting
head waiter by `IrqWhR`. The queue links of a queued thread on a held object (`LkW`), whoever's thread it is, keep
value and lock owner (`vn_linkQ`); the held endpoint / reply words and slot words are never rewritten (`nf_obj`,
`nf_slot`).

* `IrqWhRL` (the chain's reads of homed objects, slot words and held-lock words), `IrqWhWS` (its writes of them but
  the `STATE` words), `IrqWhPS` (a homed thread's `STATE` write with the old queue's lock held and a non-queued new
  state — what `stepOK_state` checks, decided by the thread's words of `IrqWhRL`).
* `ntfn_head_wait`: a nonzero notification head is a waiting notification's (P1 `EpsWit`).
* **`irq_wh_annV`**: `PathObl.safe_tr_wr` with `Rd := IrqHnRd ∪ IrqWhRL`, `Wd := IrqHnWd ∪ IrqWhWS ∪ STATE words`.
  At `σ` the run on `gd st Rd P` is the real one: an accepted fire case by `WH.irq_acc_fire_wkG` (P2/IrqWhG; its
  main-line facts: `PlanLk` given (`IrqPremK2B.pl`), `ObjLay` / `SlotLayV` / `BufAt` from `SlJAt` (`slJAt_slotJC`,
  `irq_bufAt_runB`)), every other run by `irq_pl_guard` + `irqTail_guardP` with `fire_ok` by `WH.fire_ok_guardWK`.
  Then as gen 24: `interp_agree_gd` σ → `s`, `interp_gd_guard`, `interp_gd` (`StepOK` per write: `stepOK_nondec`,
  `stepOK_state`, `stepOK_height`, `stepOK_deadline`).

Premises: `hPL : PlanLk lk pl` is a hypothesis, the [P] field `IrqPremK2B.pl` of the irq start fact (no new premise).
No existing statement changed.
Gen 49 (in place, statement of `irq_wh_annV` unchanged): its certificate data is split out as **`irq_wh_cert`**
(read set `IrqWhRd`, write set `IrqWhWd`, the guarded run, the writes' `WPerm` at the start, `tm ≠ 0`) for the
`InsA` twin (P2/InsV15Irq).
-/
import Fl4Proofs.P2.IrqWhG
import Fl4Proofs.P2.IrqHnAnn
import Fl4Proofs.P2.SlVAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oTIMER_HEIGHT oSTATE oBLOCK_OBJ InW GateField
  TimerField GField tcbOwner ntfnOwner QueuedState)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb
  TZero Hidden)

noncomputable section
open Classical

/-- **The earliest thread `tm` is on `c` and its bound notification wakes a thread, the head waiter of a waiting
one on `c`, in `ρ`** (module docstring). -/
def IrqWhR (ρ : U64 → U64) (c tm : U64) : Prop :=
  tm ≠ 0#u64 ∧ ρ (affA tm) = c ∧ ¬ NoWakeR ρ tm ∧
    ((ρ (epTSA (ρ (boundA tm))) &&& 3#u64) = obj.NTFN_WAITING → ρ (affA (ρ (epHeadA (ρ (boundA tm))))) = c)

section sets
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The waking chain's reads of homed objects, slot words and held-lock words** (module docstring). -/
def IrqWhRL (K : KLayout) (T Scs : Set U64) (Z : U64 → Nat) (lk : U64 → Prop) (ρ : U64 → U64) (c : U64) (σ : S)
    (b : U64) : Prop :=
  (∃ y, LocT st T σ y ∧ ρ (fld y oAFFINITY) = c ∧ ∃ k : U64, 256 ≤ k.val ∧ k.val < 4096 ∧ k.val % 8 = 0 ∧
    ¬ TimerField k.val ∧ ¬ GField k.val ∧ b = core.num.U64.wrapping_add y k) ∨
  (∃ p ∈ Scs, L.mem σ (scCoreA p) = L.cpu σ ∧ ρ (fld p 16#u64) = c ∧ Aligned b ∧ InSC p (Z p) b) ∨
  (∃ y, LocT st T σ y ∧ ρ (fld y oAFFINITY) = c ∧ (b = vtA y ∨ b = core.num.U64.wrapping_add (vtA y) 8#u64)) ∨
  (Aligned b ∧ LkW st K T lk σ b)

/-- **The waking chain's writes of homed objects and held-lock words, but `STATE`** (module docstring). -/
def IrqWhWS (K : KLayout) (T Scs : Set U64) (Z : U64 → Nat) (lk : U64 → Prop) (ρ : U64 → U64) (c : U64) (σ : S)
    (b : U64) : Prop :=
  (∃ y, LocT st T σ y ∧ ρ (fld y oAFFINITY) = c ∧ ∃ k : U64, 256 ≤ k.val ∧ k.val < 4096 ∧ k.val % 8 = 0 ∧
    ¬ GateField k.val ∧ ¬ TimerField k.val ∧ ¬ GField k.val ∧ k.val ≠ 3328 ∧ k.val ≠ 3336 ∧
    b = core.num.U64.wrapping_add y k) ∨
  (∃ p ∈ Scs, L.mem σ (scCoreA p) = L.cpu σ ∧ ρ (fld p 16#u64) = c ∧ Aligned b ∧ InSC p (Z p) b ∧
    b.val ≠ p.val + 16) ∨
  (Aligned b ∧ LkW st K T lk σ b)

/-- **The `STATE` words of homed threads** (module docstring). -/
def IrqWhWSt (T : Set U64) (ρ : U64 → U64) (c : U64) (σ : S) (b : U64) : Prop :=
  ∃ y, LocT st T σ y ∧ ρ (fld y oAFFINITY) = c ∧ b = stA y

/-- **A homed thread's checked `STATE` write** (module docstring). -/
def IrqWhPS (T : Set U64) (lk : U64 → Prop) (ρ : U64 → U64) (c : U64) (σ : S) (x : S) (q v : U64) : Prop :=
  ∃ y, LocT st T σ y ∧ ρ (fld y oAFFINITY) = c ∧ q = stA y ∧ L.mem x (affA y) = c ∧
    (QueuedState (L.mem x (stA y)) → lk (L.mem x (blockA y))) ∧ ¬ QueuedState v

/-- **The read set of `irq_wh_annV`'s certificate** (gen 49, split out of `irq_wh_annV`): `IrqHnRd ∪ IrqWhRL`. -/
def IrqWhRd (K : KLayout) (T Scs : Set U64) (Z : U64 → Nat) (lk : U64 → Prop) (ρ : U64 → U64) (c irq : U64) (σ : S)
    (b : U64) : Prop :=
  IrqHnRd st T Z irq σ b ∨ IrqWhRL st K T Scs Z lk ρ c σ b

/-- **The write set of `irq_wh_annV`'s certificate** (gen 49): `IrqHnWd ∪ IrqWhWS ∪ IrqWhWSt`. -/
def IrqWhWd (K : KLayout) (T Scs : Set U64) (Z : U64 → Nat) (lk : U64 → Prop) (ρ : U64 → U64) (c : U64) (σ : S)
    (b : U64) : Prop :=
  IrqHnWd st T Z σ b ∨ IrqWhWS st K T Scs Z lk ρ c σ b ∨ IrqWhWSt st T ρ c σ b

end sets

section head
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap}

/-- **A nonzero notification head is a waiting notification's** (module docstring). -/
theorem ntfn_head_wait {s : S} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {N : U64}
    (h0 : SchedQueuesInv st T Cs Ω H s Q Rq) (hHN : H N = some .ntfn)
    (hne : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) ≠ 0#u64) :
    L.epState s N = obj.NTFN_WAITING := by
  obtain ⟨E, EQ, hEW⟩ := h0.eps
  have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN)
  obtain ⟨-, -, hq⟩ := hEW.1 N he
  have e : L.mem s (core.num.U64.wrapping_add N layout.ntfn.HEAD) = (EQ N).headD 0#u64 := by
    rw [← hq.head, ntfn_head_eq]
    rfl
  obtain ⟨k1, -, k0, -, k4, -⟩ := hEW.2.2.2.2.2
  cases hl : EQ N with
  | nil => rw [hl] at e; exact absurd e hne
  | cons y ys =>
    have hy : y ∈ EQ N := by rw [hl]; exact List.mem_cons_self
    have yT : y ∈ T := hq.mem y hy
    obtain ⟨hyX, hb, hbl⟩ := hEW.2.2.2.1 N he y hy
    rcases hbl with h | h | h
    · have := k1 y yT hyX (Or.inl h)
      rw [hb, hHN] at this; cases this
    · have := k1 y yT hyX (Or.inr h)
      rw [hb, hHN] at this; cases this
    · rw [(k4 N he y hy).2.2 h]; simp [obj.NTFN_WAITING]

end head

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The data of `irq_wh_annV`'s certificate** (gen 49, split out of `irq_wh_annV` in place): the read set
`IrqWhRd`, aligned and readable, the write set `IrqWhWd`, held at the start, the guarded run with `StepOK` at every
state carrying `ρ` on the read set, and `tm ≠ 0`. -/
theorem irq_wh_cert (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hPL : PlanLk lk pl) (hH : IrqWhR ρ c (ρ (tmA (L := L) σ))) :
    (∀ b, IrqWhRd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c irq σ b → Aligned b) ∧
    (∀ q, IrqWhRd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c irq σ q → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) ∧ ¬ q ∈ K.user) ∧
    (∀ x, IrqWhWd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x))) ∧
    (∀ q, ¬ q ∈ K.user → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) → PO c hs (ownP K μ q)) ∧
    (∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, IrqWhRd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c irq σ b → L.mem s b = ρ b) →
      ∃ r, interp (guard st (IrqWhRd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c irq σ) (IrqWhWd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ)) ar
          (R.localtimer.handle_timer_irq_local irq pl) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.localtimer.handle_timer_irq_local irq pl) s a) ∧
    (∀ x, IrqWhWd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ x → PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) x) ∧
    L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) ≠ 0#u64 := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  have hUO := hJ.userOK
  obtain ⟨hk, hcp⟩ := hJ.kc
  obtain ⟨Ω, Ac, EM⟩ := IrqPreJ3.entM (st := st) (K := K.toKLayout) (m := L.mem σ) (s := σ) (irq := irq)
    ⟨hJ, fun _ _ _ => rfl⟩
  have E0 := EM.ent
  have hI := E0.inv
  have hL := E0.lay
  have hY := E0.ly
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced (Heap.tcbs K.toKLayout.heap) := h0.tcbs
  have hN : NodePlaced st (Heap.tcbs K.toKLayout.heap) σ (L.cpu σ) := h0.nodes _ h0.cur
  have hcT : L.curW σ ∈ Heap.tcbs K.toKLayout.heap := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := vx_cur_home hJ hmm
  have hcs : L.cscW σ ∈ Heap.scs K.toKLayout.heap := hI.2.2.1.2.2.cur
  have hO := hI.2.2.1.1
  have hSs := hI.2.2.2.2
  have ct0 : L.curW σ ≠ 0#u64 := fun e => (hT _ hcT).ne0 (by rw [e]; rfl)
  have csc0 : L.cscW σ ≠ 0#u64 := fun e => by
    have h1 := st_scH (K := K) hcs
    rw [e, slJAt_heap0 hJ] at h1
    cases h1
  -- a thread's `AFFINITY` at the view is the core
  have affC : ∀ t, t ∈ Heap.tcbs K.toKLayout.heap → L.mem σ (affA t) = L.cpu σ := fun t ht => by
    have hu : affA t ∉ K.user := hL.nu_tcb ht (k := 3520#u64) (by simp) (by simp)
    have ha : Aligned (affA t) := field_aligned (hT _ ht) (by simp) (by simp)
    rw [hmm _ ha hu, hc]
    exact CoreView.view_aff hK0 ht c ρ
  have ownT : ∀ t k, t ∈ Heap.tcbs K.toKLayout.heap → 256 ≤ k.val → k.val < 4096 →
      OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add t k) = tcbOwner (L.mem σ) t k.val :=
    fun t k ht h1 h2 => by
      have e := hL.own_tcb hT (L.mem σ) ht (k := k) h1 h2
      unfold fld at e
      exact e
  -- homes
  have scHome : ∀ p, p ∈ Heap.scs K.toKLayout.heap → L.mem σ (scTcbA p) ≠ 0#u64 → ρ (fld p 16#u64) = c := by
    intro p hp hp0
    obtain ⟨hP, hz⟩ := hO.sc _ hp
    obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
    have hv : (scTcbA p).val = p.val + 24 := by
      unfold scTcbA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hr : region K.toKLayout (scTcbA p) = .sc p :=
      hX.scW p _ (st_scH (K := K) hp) _ ⟨by omega, by omega⟩
    have ha : Aligned (scTcbA p) := by unfold Aligned; rw [hv]; omega
    have hku : scTcbA p ∉ K.user := hL.nu_sc hp ⟨by omega, by omega⟩
    exact CoreView.view_sctcb_home (K := K.toKLayout) hr (by omega) (by rw [← hmm _ ha hku]; exact hp0)
  have cscHome : IrqOk st σ → ρ (fld (L.cscW σ) 16#u64) = c := by
    intro hok
    have hne : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := by rw [hok.sc]; exact csc0
    obtain ⟨hcs', htcb, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
    rw [← hok.sc]
    exact scHome _ hcs' (fun e => ct0 (htcb.symm.trans e))
  have rhHome : ∀ (h00 : L.mem σ (rhA (L := L) σ) ≠ 0#u64),
      ρ (fld (L.mem σ (rhA (L := L) σ)) oAFFINITY) = c ∧
        ρ (fld (L.mem σ (scA (L.mem σ (rhA (L := L) σ)))) 16#u64) = c := by
    intro h00
    obtain ⟨⟨Q, Rq, hq'⟩, hb, ⟨-, -, hX'⟩, -, -⟩ := id hI
    obtain ⟨hTr, -, -⟩ := bxi_rh hI h00
    have hne : L.mem σ (scA (L.mem σ (rhA (L := L) σ))) ≠ 0#u64 := by
      intro e0
      have hfl := hb.r _ hTr
      have hrel := hq'.release _ hq'.cur
      have hd : L.mem σ (rhA (L := L) σ) = (Rq (L.cpu σ)).headD 0#u64 := hrel.head
      have hmR : L.mem σ (rhA (L := L) σ) ∈ Rq (L.cpu σ) := by
        cases hl' : Rq (L.cpu σ) with
        | nil => rw [hl'] at hd; exact absurd hd h00
        | cons r rs => rw [hl'] at hd; rw [hd]; simp
      exact hfl ((hq'.released _ hTr).2 (by rw [hq'.inR _ hq'.cur _ hmR]; exact hmR)) e0
    obtain ⟨hcs', htcb, -⟩ := hX'.bound _ hTr hne
    refine ⟨?_, scHome _ hcs' (fun e => h00 (htcb.symm.trans e))⟩
    have hrH : K.toKLayout.heap (L.mem σ (rhA (L := L) σ)) = some .tcb := hTr
    obtain ⟨hr, hv, ha⟩ := hX.tcbW _ hrH 3464#u64 (by simp) (by simp) (by simp)
    have hu : scA (L.mem σ (rhA (L := L) σ)) ∉ K.user := hL.nu_tcb hTr (k := 3464#u64) (by simp) (by simp)
    refine CoreView.view_tzero_home hr (by rw [hv]; simp [TZero]) ?_
    rw [← hmm _ ha hu]; exact hne
  set tm := L.mem σ (L.nodeAt σ (L.cpu σ) layout.node.TIMER_MIN) with htm
  have armρ : tm ≠ 0#u64 → ρ (fld tm oTIMER_DEADLINE) ≠ 0#u64 := by
    intro hne
    obtain ⟨tmT, arm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    have tH : K.toKLayout.heap tm = some .tcb := tmT
    obtain ⟨hr0, hv0, hal⟩ := hX.tcbW tm tH 3528#u64 (by simp) (by simp) (by simp)
    have hr : region K.toKLayout (tdA tm) = .tcb tm := hr0
    have hv : (tdA tm).val - tm.val = (3528#u64).val := hv0
    have hu : tdA tm ∉ K.user := hL.nu_tcb tmT (k := 3528#u64) (by simp) (by simp)
    have e1 := hmm (tdA tm) hal hu
    have e2 : view K.toKLayout c ρ (tdA tm) = ρ (tdA tm) :=
      CoreView.view_timer_keep hr (by rw [hv]; simp) (by rw [hv]; simp)
    intro e
    exact arm.1 (by rw [e1, e2]; exact e)
  -- the good read words
  let G : U64 → Prop := fun b => Aligned b ∧ RPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧
    b ∉ K.user ∧ SR K c ρ b
  have gN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → G (L.nodeAt σ (L.cpu σ) o) := by
    intro o ho h8
    have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := hL.nd o ho
    have hr' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := by rw [hr, hc]
    exact ⟨nodeAt_aligned hN ho h8, Or.inl (held_core (hL.own_node _ ho)), hL.nu_node ho,
      sr_nf hK (by rw [hr']; intro h; cases h) (nf_node hr')⟩
  have gC : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → G (core.num.U64.wrapping_add (L.curW σ) k) := by
    intro k h1 h2 h3 h4 h5 h6
    refine ⟨field_aligned ht' h2 h3, ?_, hL.nu_tcb hcT h1 h2, sr_tcb hK hX htH hcur (by omega) h2 h3⟩
    by_cases hg : GateField k.val
    · exact Or.inr (by unfold GateOnly; rw [ownT _ k hcT h1 h2, tcbOwner, if_pos hg])
    · refine Or.inl (held_core ?_)
      rw [ownT _ k hcT h1 h2, tcbOwner, if_neg hg, if_neg (by unfold TimerField; omega),
        if_neg (by unfold GField; omega)]
      exact congrArg Owner.core (affC _ hcT)
  have gT : IrqOk st σ → ∀ b, Aligned b → IrqRdT st (Heap.scBits K.toKLayout.heap) σ b → G b := by
    intro hok b ha hb
    have hrp := irq_rd_own hK0 hI hL hY E0.aff hok (lk := lk σ) (irqRdT_sub hb)
    have hnu := irq_rd_nu hI hL hY (irqRdT_sub hb)
    refine ⟨ha, hrp, hnu, ?_⟩
    rcases hb with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩ | hb | ⟨hne, rfl | hb⟩ | ⟨hne, rfl⟩ |
        ⟨k, hk', hk32, h8, rfl⟩
    · exact (gN o ho h8).2.2.2
    · exact (gC k h1 h2 h3 h4 h5 h6).2.2.2
    · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) hb).1
    · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
      exact sr_tcb hK hX (show K.toKLayout.heap _ = some .tcb from r1) (rhHome hne).1 (o := 3464#u64)
        (by simp) (by simp) (by simp)
    · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne
      exact (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne).2 hb).1
    · obtain ⟨tmT, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
      exact sr_timer hK hX (show K.toKLayout.heap _ = some .tcb from tmT) (o := 3528#u64) (by simp) (by simp)
        (by simp) (armρ hne)
    · obtain ⟨p, hr, -, -⟩ := hY.cs k hk' hk32
      exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_slot hr)
  have gSc : L.mem σ (scA (L.curW σ)) ≠ 0#u64 → G (scCoreA (L.mem σ (scA (L.curW σ)))) := by
    intro hne
    obtain ⟨hcs0, htcb0, -⟩ := hI.2.2.1.2.2.bound _ h0.curT hne
    have hcs' : L.mem σ (scA (L.curW σ)) ∈ Heap.scs K.toKLayout.heap := hcs0
    have htcb : L.mem σ (scTcbA (L.mem σ (scA (L.curW σ)))) = L.curW σ := htcb0
    have hcore : L.mem σ (scCoreA (L.mem σ (scA (L.curW σ)))) = L.cpu σ := (E0.aff _ hcT hne).trans (affC _ hcT)
    clear hcs0 htcb0
    generalize hpq : L.mem σ (scA (L.curW σ)) = p at hcs' htcb hne hcore ⊢
    have hz := st_scH (K := K) hcs'
    obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
      (by simp [layout.sc.CORE])
    have e := sc_own hL hcs' hin hcore
    refine ⟨am, ?_, hL.nu_sc hcs' hin, (srw_sc hK hX hz (scHome _ hcs' (fun e => ct0 (htcb.symm.trans e))) hin).1⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have gK : ∀ o : U64, (o = layout.ks.CUR_DOMAIN ∨ o = layout.ks.DOMAIN_TIME ∨ o = layout.ks.KERNEL_ROOT) →
      G (core.num.U64.wrapping_add (L.ksb σ) o) := by
    rintro o (rfl | rfl | rfl)
    · exact ⟨hL.domA, rperm_none hL.dom _, hL.domU,
        ⟨vn_of_nf hK (nf_none hL.dom), hq.ksw (by simp [layout.ks.CUR_DOMAIN])⟩⟩
    · exact ⟨hL.dtmA, rperm_none hL.dtm _, hL.dtmU,
        ⟨vn_of_nf hK (nf_none hL.dtm), hq.ksw (by simp [layout.ks.DOMAIN_TIME])⟩⟩
    · exact ⟨hY.kr.1, rperm_none hY.kr.2 _, hY.krU,
        ⟨vn_of_nf hK (nf_none hY.kr.2), hq.ksw (by simp [layout.ks.KERNEL_ROOT])⟩⟩
  have gI : ∀ i, interrupt.state_off irq = ok i → G (core.num.U64.wrapping_add (L.ksb σ) i) := fun i hi => by
    obtain ⟨ha, hr⟩ := hY.iq hirq i hi
    exact ⟨ha, rperm_none hr _, hY.iqU hirq i hi, ⟨vn_of_nf hK (nf_none hr), hq.ksw (state_off_lt hirq hi)⟩⟩
  have gTab : IrqOk st σ → ∀ hi : U64, hi.val < 2048 → G (atAF (L.ksb σ) hi) ∧
      ∀ lo : U64, lo.val < 512 → L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → G (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) := by
    intro _ hi hhi
    obtain ⟨⟨a0, r0⟩, hlo'⟩ := hY.tab hi hhi
    refine ⟨⟨a0, rperm_none r0 _, (hY.tabU hi hhi).1, ⟨vn_of_nf hK (nf_none r0), (hq.tab hi hhi).1⟩⟩,
      fun lo hlo hne => ?_⟩
    obtain ⟨a1, r1⟩ := hlo' lo hlo hne
    exact ⟨a1, rperm_none r1 _, (hY.tabU hi hhi).2 lo hlo hne,
      ⟨vn_of_nf hK (nf_none r1), (hq.tab hi hhi).2 lo hlo hne⟩⟩
  have gR : ∀ b, IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ b → G b := by
    intro b hb
    rcases hb with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩ | ⟨hok, ha, hb⟩ | ⟨hne, rfl⟩ |
        ⟨o, ho, rfl⟩ | ⟨-, i, hi, rfl⟩ | ⟨hok, hi, hhi, rfl | ⟨lo, hlo, hne, rfl⟩⟩
    · exact gN o ho h8
    · exact gC k h1 h2 h3 h4 h5 h6
    · exact gT hok b ha hb
    · exact gSc hne
    · exact gK o ho
    · exact gI i hi
    · exact (gTab hok hi hhi).1
    · exact (gTab hok hi hhi).2 lo hlo hne
  -- membership helpers
  have rN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (L.nodeAt σ (L.cpu σ) o) :=
    fun o h1 h2 => Or.inl ⟨o, h1, h2, rfl⟩
  have rC : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (core.num.U64.wrapping_add (L.curW σ) k) :=
    fun k h1 h2 h3 h4 h5 h6 => Or.inr (Or.inl ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩)
  have rK : ∀ o : U64, (o = layout.ks.CUR_DOMAIN ∨ o = layout.ks.DOMAIN_TIME ∨ o = layout.ks.KERNEL_ROOT) →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (core.num.U64.wrapping_add (L.ksb σ) o) :=
    fun o ho => Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨o, ho, rfl⟩))))
  have rI : ∀ i, interrupt.state_off irq = ok i →
      IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (core.num.U64.wrapping_add (L.ksb σ) i) :=
    fun i hi => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hirq, i, hi, rfl⟩)))))
  have rSt : IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (stA (L.curW σ)) := by
    rw [Fl4Proofs.P1.stA_eq]
    exact rC 3328#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
  have rAf : IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ (affA (L.curW σ)) :=
    rC 3520#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
  -- (gen 24) values the view keeps
  have kvR : ∀ b, G b → L.mem σ b = ρ b := fun b g => by
    rw [hmm b g.1 g.2.2.1]; exact g.2.2.2.1.1
  have hY := E0.ly
  have eTm : L.mem σ (tmA (L := L) σ) = ρ (tmA (L := L) σ) :=
    kvR _ (gN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  obtain ⟨hH0, hH1, hH2, hH3⟩ := hH
  have hne : tm ≠ 0#u64 := fun e => hH0 (by rw [← eTm]; exact e)
  obtain ⟨tmT, tmArm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  have tH : K.toKLayout.heap tm = some .tcb := tmT
  have hHome : ρ (fld tm oAFFINITY) = c := by
    have h' : ρ (affA (L.mem σ (tmA (L := L) σ))) = c := by rw [eTm]; exact hH1
    exact h'
  have hW2 : ¬ NoWakeR ρ tm := by
    have h' : ¬ NoWakeR ρ (L.mem σ (tmA (L := L) σ)) := by rw [eTm]; exact hH2
    exact h'
  have hW3 : (ρ (epTSA (ρ (boundA tm))) &&& 3#u64) = obj.NTFN_WAITING → ρ (affA (ρ (epHeadA (ρ (boundA tm))))) = c := by
    have h' : (ρ (epTSA (ρ (boundA (L.mem σ (tmA (L := L) σ))))) &&& 3#u64) = obj.NTFN_WAITING →
        ρ (affA (ρ (epHeadA (ρ (boundA (L.mem σ (tmA (L := L) σ))))))) = c := by rw [eTm]; exact hH3
    exact h'
  -- armed in the view ⇒ armed in `ρ`
  have armY : ∀ y, y ∈ Heap.tcbs K.toKLayout.heap → L.mem σ (tdA y) ≠ 0#u64 → ρ (fld y oTIMER_DEADLINE) ≠ 0#u64 := by
    intro y yT hy
    have yH : K.toKLayout.heap y = some .tcb := yT
    obtain ⟨hr0, hv0, hal⟩ := hX.tcbW y yH 3528#u64 (by simp) (by simp) (by simp)
    have hr : region K.toKLayout (tdA y) = .tcb y := hr0
    have hv : (tdA y).val - y.val = (3528#u64).val := hv0
    have hu : tdA y ∉ K.user := hL.nu_tcb yT (k := 3528#u64) (by simp) (by simp)
    have e1 := hmm (tdA y) hal hu
    have e2 : view K.toKLayout c ρ (tdA y) = ρ (tdA y) :=
      CoreView.view_timer_keep hr (by rw [hv]; simp) (by rw [hv]; simp)
    intro e
    exact hy (by rw [e1, e2]; exact e)
  -- the timer words of the keys armed in `c`'s tree
  have gKey : ∀ y k, y ∈ Heap.tcbs K.toKLayout.heap → FootLtArmed st σ (L.cpu σ) y → 3528 ≤ k.val → k.val < 3576 →
      k.val % 8 = 0 → G (core.num.U64.wrapping_add y k) := by
    intro y k yT ya h1 h2 h3
    have yH : K.toKLayout.heap y = some .tcb := yT
    have hs' : SR K c ρ (fld y k) := sr_timer hK hX yH h1 (by omega) h3 (armY y yT ya.1)
    exact ⟨field_aligned (hT _ yT) (by omega) h3, Or.inl (held_core (ftree_own hL hT yT ya h1 h2 h3)),
      hL.nu_tcb yT (by omega) (by omega), hs'⟩
  -- `tm`'s words off its timer fields
  have gTm : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      k.val ≠ 3496 → k.val ≠ 3504 → G (core.num.U64.wrapping_add tm k) := by
    intro k h1 h2 h3 h4 h5 h6
    refine ⟨field_aligned (hT _ tmT) h2 h3, ?_, hL.nu_tcb tmT h1 h2, sr_tcb hK hX tH hHome (by omega) h2 h3⟩
    by_cases hg : GateField k.val
    · exact Or.inr (by unfold GateOnly; rw [ownT _ k tmT h1 h2, tcbOwner, if_pos hg])
    · refine Or.inl (held_core ?_)
      rw [ownT _ k tmT h1 h2, tcbOwner, if_neg hg, if_neg (by unfold TimerField; omega),
        if_neg (by unfold GField; omega)]
      exact congrArg Owner.core (affC _ tmT)
  -- `tm`'s bound notification
  set N := L.mem σ (boundA tm) with hNdef
  have ntAll : N ≠ 0#u64 → L.mem σ (ntfnBtA N) = tm ∧ ∀ k : U64, k.val < 64 → k.val % 8 = 0 →
      G (core.num.U64.wrapping_add N k) ∧
        (k.val ≠ 24 → OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add N k) = .core (L.cpu σ)) := by
    intro hb
    have hNt : N ∈ K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ tmT hb
    have hbt : L.mem σ (ntfnBtA N) = tm := hI.2.2.1.2.2.bs.tb _ tmT hb
    refine ⟨hbt, fun k h1 h2 => ?_⟩
    have hpH : K.toKLayout.heap N = some .ntfn := hNt
    obtain ⟨r24, -, a24⟩ := hX.ntW _ hpH 24#u64 (by simp) (by simp)
    have r24' : region K.toKLayout (fld N 24#u64) = .ntfn N := r24
    have eA : fld N 24#u64 = ntfnBtA N := by
      unfold fld ntfnBtA layout.ntfn.BOUND_TCB
      rfl
    have hbσ : L.mem σ (fld N 24#u64) = tm := by rw [eA]; exact hbt
    have hbρ : ρ (fld N 24#u64) = tm := by
      have e1 : view K.toKLayout c ρ (fld N 24#u64) = ρ (fld N 24#u64) := view_ntfn r24'
      have e2 : L.mem σ (fld N 24#u64) = view K.toKLayout c ρ (fld N 24#u64) :=
        hmm (fld N 24#u64) a24 (hL.nu (by rw [r24']; intro h; cases h))
      rw [← e1, ← e2]; exact hbσ
    obtain ⟨r, v, ha⟩ := hX.ntW _ hpH k h1 h2
    have own_e : OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add N k) =
        ntfnOwner K.toKLayout (L.mem σ) N k.val := by
      simp only [OwnMap.own, r, v]
    have hcore : k.val ≠ 24 → OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add N k) = .core (L.cpu σ) :=
      fun h24 => by
        rw [own_e, ntfnOwner, if_neg h24, hbσ, if_pos tH]
        exact congrArg Owner.core (affC tm tmT)
    refine ⟨⟨ha, ?_, hL.nu (by rw [r]; intro h; cases h),
      sr_nf hK (by rw [r]; intro h; cases h) (nf_ntfn r (fun _ => by rw [hbρ]; exact hHome))⟩, hcore⟩
    by_cases h24 : k.val = 24
    · exact Or.inr (by unfold GateOnly; rw [own_e, ntfnOwner, if_pos h24])
    · exact Or.inl (held_core (hcore h24))
  -- every word of `IrqRd`, once `current_ok` passed
  have gIrq : IrqOk st σ → ∀ b, Aligned b → IrqRd st (Heap.scBits K.toKLayout.heap) σ b → G b := by
    intro hok b ha hb
    have hrp := irq_rd_own hK0 hI hL hY E0.aff hok (lk := lk σ) hb
    have hnu := irq_rd_nu hI hL hY hb
    refine ⟨ha, hrp, hnu, ?_⟩
    rcases hb with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, h4, h5, h6, rfl⟩ | hb | ⟨hne', rfl | hb⟩ | ⟨-, hb⟩ |
        ⟨k, hk', hk32, h8, rfl⟩
    · exact (gN o ho h8).2.2.2
    · exact (gC k h1 h2 h3 h4 h5 h6).2.2.2
    · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) hb).1
    · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne'
      exact sr_tcb hK hX (show K.toKLayout.heap _ = some .tcb from r1) (rhHome hne').1 (o := 3464#u64)
        (by simp) (by simp) (by simp)
    · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne'
      exact (srw_sc hK hX (st_scH (K := K) r4) (rhHome hne').2 hb).1
    · rcases hb with ⟨k, hk, rfl⟩ | ⟨-, ⟨k, hk, rfl⟩ | ⟨hb0, rfl | rfl⟩⟩
      · rcases hk with e | e | e | e
        · exact sr_tcb hK hX tH hHome (o := k) (by omega) (by omega) (by omega)
        · exact (gKey tm k tmT tmArm (by omega) (by omega) (by omega)).2.2.2
        · exact (gKey tm k tmT tmArm (by omega) (by omega) (by omega)).2.2.2
        · exact sr_tcb hK hX tH hHome (o := k) (by omega) (by omega) (by omega)
      · exact sr_tcb hK hX tH hHome (o := k) (by rcases hk with e | e | e <;> omega)
          (by rcases hk with e | e | e <;> omega) (by rcases hk with e | e | e <;> omega)
      · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])).1.2.2.2
      · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1.2.2.2
    · obtain ⟨p, hr, -, -⟩ := hY.cs k hk' hk32
      exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_slot hr)
  have gFire : IrqOk st σ → ∀ b, Aligned b →
      FireRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) σ b → G b := by
    intro hok b ha hb
    rcases hb with hb | ⟨y, hy, ya, k, h1, h2, h8, rfl⟩ | ⟨-, hb0, k, hk, h8, rfl⟩
    · exact gIrq hok b ha hb
    · exact gKey y k hy ya h1 h2 h8
    · exact ((ntAll hb0).2 k hk h8).1
  have gPl : ∀ b, IrqHnPl st σ b → G b := by
    rintro b (⟨k, hk, rfl⟩ | ⟨hb0, rfl | rfl⟩)
    · by_cases e : k.val = 3568
      · exact gKey tm k tmT tmArm (by omega) (by omega) (by omega)
      · exact gTm k (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
          (by rcases hk with e' | e' | e' | e' | e' | e' <;> omega)
    · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])).1
    · exact ((ntAll hb0).2 _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1
  -- (gen 26) the waking chain's objects: homes, slot words, held-lock words
  have heapT : ∀ y, y ∈ Heap.tcbs K.toKLayout.heap → K.toKLayout.heap y = some .tcb := fun y hy => hy
  have es : ∀ y, stA y = fld y oSTATE := fun y => by rw [Fl4Proofs.P1.stA_eq]; rfl
  have eB : ∀ y, blockA y = fld y oBLOCK_OBJ := fun y => by rw [blockA_eq]; rfl
  have hQJ := slJAt_slotJC (st := st) hJ
  have hSL : SlotLayV K.toKLayout st (Heap.tcbs K.toKLayout.heap) σ := hQJ.slotJ.slotLayV (fun y hy => hy)
  have hOL : ObjLay K.toKLayout K.toKLayout.heap (Heap.replies K.toKLayout.heap) :=
    hQJ.slotJ.objLay (fun r hr => hr)
  have sH : ∀ y k, y ∈ Heap.tcbs K.toKLayout.heap → ρ (fld y oAFFINITY) = c → 256 ≤ k.val → k.val < 4096 →
      k.val % 8 = 0 → Aligned (core.num.U64.wrapping_add y k) ∧ core.num.U64.wrapping_add y k ∉ K.user ∧
        SR K c ρ (core.num.U64.wrapping_add y k) :=
    fun y k hy hm h1 h2 h3 => ⟨field_aligned (hT _ hy) h2 h3, hL.nu_tcb hy h1 h2,
      sr_tcb hK hX (heapT y hy) hm (by omega) h2 h3⟩
  have hμY : ∀ y, y ∈ Heap.tcbs K.toKLayout.heap → ρ (fld y oAFFINITY) = c → μ (fld y oAFFINITY) = c := by
    intro y hy hm
    have hp : fld y oAFFINITY ∉ K.ptes := (sH y 3520#u64 hy hm (by simp) (by simp) (by simp)).2.2.2
    have hpo : PO c hs (ownP K μ (fld y oAFFINITY)) := by
      right; rw [ownP_eq_own nv hp]; exact OwnMap.own_aff_gate hK0 (heapT y hy) μ
    rw [← hV.2.1 _ hpo]; exact hm
  -- a thread runnable at the view, or with an SC, is homed in `ρ`; so is a bound SC
  have hHr : ∀ y ∈ Heap.tcbs K.toKLayout.heap, Runnable (L.mem σ (stA y)) → ρ (fld y oAFFINITY) = c := by
    intro y hy hr
    have hu : stA y ∉ K.user := by
      rw [Fl4Proofs.P1.stA_eq]; exact hL.nu_tcb hy (k := 3328#u64) (by simp) (by simp)
    have ha : Aligned (stA y) := by
      rw [Fl4Proofs.P1.stA_eq]; exact field_aligned (hT _ hy) (by simp) (by simp)
    have e : L.mem σ (stA y) = view K.toKLayout c ρ (fld y oSTATE) := by rw [hmm _ ha hu, es]
    refine CoreView.view_hidden_home hK0 (heapT y hy) ?_
    rw [← e]
    unfold Runnable at hr
    unfold Hidden
    rcases hr with h | h | h <;> rw [h] <;> simp [sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM]
  have hHsc : ∀ y ∈ Heap.tcbs K.toKLayout.heap, L.mem σ (scA y) ≠ 0#u64 → ρ (fld y oAFFINITY) = c := by
    intro y hy hne'
    obtain ⟨hr, hv, ha⟩ := hX.tcbW _ (heapT y hy) 3464#u64 (by simp) (by simp) (by simp)
    have hu : scA y ∉ K.user := hL.nu_tcb hy (k := 3464#u64) (by simp) (by simp)
    refine CoreView.view_tzero_home hr (by rw [hv]; simp [TZero]) ?_
    rw [← hmm _ ha hu]; exact hne'
  have hHs : ∀ y ∈ Heap.tcbs K.toKLayout.heap, L.mem σ (scA y) ≠ 0#u64 →
      ρ (fld (L.mem σ (scA y)) 16#u64) = c := by
    intro y hy hne'
    obtain ⟨hcs0, htcb0, -⟩ := hI.2.2.1.2.2.bound _ hy hne'
    have y0 : y ≠ 0#u64 := fun e => (hT _ hy).ne0 (by rw [e]; rfl)
    exact scHome _ hcs0 (fun e => y0 (htcb0.symm.trans e))
  have scC : ∀ x ∈ Heap.tcbs K.toKLayout.heap, L.mem σ (scA x) ≠ 0#u64 →
      L.mem σ (scA x) ∈ Heap.scs K.toKLayout.heap ∧ L.mem σ (scCoreA (L.mem σ (scA x))) = L.cpu σ ∧
        Aligned (scCoreA (L.mem σ (scA x))) ∧
        InSC (L.mem σ (scA x)) (Heap.scBits K.toKLayout.heap (L.mem σ (scA x))) (scCoreA (L.mem σ (scA x))) := by
    intro x hx hne'
    obtain ⟨hcs0, -, -⟩ := hI.2.2.1.2.2.bound _ hx hne'
    have hcs' : L.mem σ (scA x) ∈ Heap.scs K.toKLayout.heap := hcs0
    have hcore := (E0.aff _ hx hne').trans (affC _ hx)
    obtain ⟨-, am, hin, -⟩ := sc_off hX (st_scH (K := K) hcs') (o := layout.sc.CORE) (by simp [layout.sc.CORE])
      (by simp [layout.sc.CORE])
    exact ⟨hcs', hcore, am, hin⟩
  -- slot words and held-lock words
  have slotV_sr : ∀ {y}, LocT st (Heap.tcbs K.toKLayout.heap) σ y → SR K c ρ (vtA y) ∧
      SR K c ρ (core.num.U64.wrapping_add (vtA y) 8#u64) := by
    intro y hy
    have hy' := hT y hy.1
    have one : ∀ k : U64, (k.val = 32 ∨ k.val = 40) → SR K c ρ (core.num.U64.wrapping_add y k) := fun k hk => by
      obtain ⟨p, hr, -, -⟩ := hSL y hy k hk
      exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_slot hr)
    have e1 : vtA y = core.num.U64.wrapping_add y 32#u64 := by
      apply UScalar.eq_of_val_eq
      rw [vtA_val hy', tcb_wadd_val hy' (by simp)]; simp
    have e2 : core.num.U64.wrapping_add (vtA y) 8#u64 = core.num.U64.wrapping_add y 40#u64 := by
      apply UScalar.eq_of_val_eq
      have := hy'.fits
      rw [tcb_wadd_val hy' (by simp)]
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vtA_val hy']
      omega
    rw [e2, e1]
    exact ⟨one _ (Or.inl (by simp)), one _ (Or.inr (by simp))⟩
  have srLk : ∀ b, LkW st K.toKLayout (Heap.tcbs K.toKLayout.heap) (lk σ) σ b → SR K c ρ b := by
    rintro b (⟨y, hy, hqs, -, k, hk, rfl⟩ | ⟨p, -, hr⟩)
    · obtain ⟨r, v, -⟩ := hX.tcbW y (heapT y hy) k (by omega) (by omega) (by omega)
      have hst : QueuedState (view K.toKLayout c ρ (fld y oSTATE)) := by
        have hu : stA y ∉ K.user := by
          rw [Fl4Proofs.P1.stA_eq]; exact hL.nu_tcb hy (k := 3328#u64) (by simp) (by simp)
        have ha' : Aligned (stA y) := by
          rw [Fl4Proofs.P1.stA_eq]; exact field_aligned (hT _ hy) (by simp) (by simp)
        rw [← es, ← hmm _ ha' hu]; exact hqs
      have hv := vn_linkQ hK (y := y) (off := k) (heapT y hy) r v hk hst
      exact ⟨hv.1, fun hp => by rw [hK.none _ hp] at r; cases r⟩
    · exact sr_nf hK (by rw [hr]; intro h; cases h) (nf_obj hr)
  have gRL : ∀ b, IrqWhRL st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap)
      (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ b → G b := by
    rintro b (⟨y, hy, hm, k, h1, h2, h3, ht, hg, rfl⟩ | ⟨p, hp, hcp', hm, ha, hb⟩ | ⟨y, hy, hm, hb⟩ | ⟨ha, hb⟩)
    · obtain ⟨a1, u1, s1⟩ := sH y k hy.1 hm h1 h2 h3
      exact ⟨a1, loc_rd_own hI hL (Or.inr (Or.inl ⟨y, hy, k, h1, h2, h3, ht, hg, rfl⟩)), u1, s1⟩
    · exact ⟨ha, loc_rd_own hI hL (Or.inr (Or.inr ⟨p, hp, hcp', hb⟩)), hL.nu_sc hp hb,
        (srw_sc hK hX (st_scH (K := K) hp) hm hb).1⟩
    · obtain ⟨m1, m2⟩ := slot_maxRV (lk := lk) hT hSL hL.user hy
      obtain ⟨s1, s2⟩ := slotV_sr hy
      rcases hb with rfl | rfl
      · exact ⟨m1.2.1, m1.1, m1.2.2, s1⟩
      · exact ⟨m2.2.1, m2.1, m2.2.2, s2⟩
    · have o := lkw_own hI hL (lk := lk σ) (Lk := lk σ) (fun _ h => h) hb
      exact ⟨ha, o.2, hL.nu_held o.1, srLk b hb⟩
  -- the read set
  let RL : U64 → Prop := IrqWhRL st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap)
    (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ
  let Rd : U64 → Prop := fun b =>
    IrqHnRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) irq σ b ∨ RL b
  have gRd : ∀ b, Rd b → G b := by
    rintro b ((hb | ⟨hok, ha, hb⟩ | hb) | hb)
    · exact gR b hb
    · exact gFire hok b ha hb
    · exact gPl b hb
    · exact gRL b hb
  have rn : ∀ b, IrqFhRn st (Heap.scBits K.toKLayout.heap) irq σ b → Rd b := fun b h => Or.inl (Or.inl h)
  have rPl : ∀ k : U64, (k.val = 3520 ∨ k.val = 3568 ∨ k.val = 3368 ∨ k.val = 3328 ∨ k.val = 3336 ∨
      k.val = 3360) → Rd (core.num.U64.wrapping_add tm k) := fun k hk =>
    Or.inl (Or.inr (Or.inr (Or.inl ⟨k, hk, rfl⟩)))
  have rF : IrqOk st σ → ∀ b, Aligned b →
      FireRd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) σ b → Rd b :=
    fun hok b ha hb => Or.inl (Or.inr (Or.inl ⟨hok, ha, hb⟩))
  have rL : ∀ b, RL b → Rd b := fun b h => Or.inr h
  have rHx : ∀ x ∈ Heap.tcbs K.toKLayout.heap, ρ (fld x oAFFINITY) = c → ∀ k : U64, 256 ≤ k.val → k.val < 4096 →
      k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) → k.val ≠ 3496 → k.val ≠ 3504 →
      Rd (core.num.U64.wrapping_add x k) :=
    fun x hx hm k h1 h2 h3 h4 h5 h6 => rL _ (Or.inl ⟨x, ⟨hx, affC x hx⟩, hm, k, h1, h2, h3,
      by unfold TimerField; omega, by unfold GField; omega, rfl⟩)
  have rCx : ∀ x ∈ Heap.tcbs K.toKLayout.heap, ρ (fld x oAFFINITY) = c → L.mem σ (scA x) ≠ 0#u64 →
      Rd (scCoreA (L.mem σ (scA x))) := fun x hx _ hne' => by
    obtain ⟨p1, p2, p3, p4⟩ := scC x hx hne'
    exact rL _ (Or.inr (Or.inl ⟨_, p1, p2, hHs x hx hne', p3, p4⟩))
  let Ro : U64 → Prop := fun q => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q
  have nuV : ∀ b, b ∉ K.user → b ∉ (userV K.toKLayoutV).user := fun b hb hu =>
    (mem_userV.1 hu).elim hb (not_vData_empty nv)
  have gRo : ∀ b, G b → Ro b ∧ b ∉ K.user := fun b g =>
    ⟨⟨⟨⟨g.2.1, g.1, nuV b g.2.2.1⟩, g.2.2.2.2⟩, g.2.2.2.1.2⟩, g.2.2.1⟩
  have hR0 : ∀ q, Rd q → Ro q ∧ ¬ q ∈ K.user := fun q hq => gRo q (gRd q hq)
  have hal : ∀ b, Rd b → Aligned b := fun b hb => (gRd b hb).1
  -- the write sets
  let WS : U64 → Prop := IrqWhWS st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap)
    (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ
  let WSt : U64 → Prop := IrqWhWSt st (Heap.tcbs K.toKLayout.heap) ρ c σ
  let PS : S → U64 → U64 → Prop := IrqWhPS st (Heap.tcbs K.toKLayout.heap) (lk σ) ρ c σ
  let Wd : U64 → Prop := fun b =>
    IrqHnWd st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) σ b ∨ WS b ∨ WSt b
  let P : S → U64 → U64 → Prop := fun x q v =>
    IrqHnP st (Heap.tcbs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) c σ x q v ∨ WS q ∨ PS x q v
  have hPW : ∀ x q v, P x q v → Wd q := by
    rintro x q v (((h | ⟨rfl, -⟩) | h | ⟨hok, y, hy, ya, rfl, -⟩ | ⟨hok, rfl, -⟩) | h | ⟨y, hy, hm, rfl, -⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr rfl))
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨hok, y, hy, ya, rfl⟩)))
    · exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hok, rfl⟩)))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨y, hy, hm, rfl⟩)
  have wSR : ∀ b, Aligned b → PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b → SR K c ρ b →
      Aligned b ∧ PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧ b ∉ K.ptes ∧
        VO K c ρ b := fun b ha hw hs => ⟨ha, hw, hs.2, hs.1.2⟩
  have gW : ∀ b, Wd b → Aligned b ∧ PathObl.WPerm (OwnMap.own K.toKLayout) (L.cpu σ) (lk σ) (L.mem σ) b ∧
      b ∉ K.ptes ∧ VO K c ρ b := by
    rintro b ((((⟨hok, ha, hw, -⟩ | rfl | rfl) | rfl) | ⟨hok, ha, hw | hw⟩ | ⟨hok, y, hy, ya, rfl⟩ | ⟨hok, rfl⟩) |
      (⟨y, hy, hm, k, h1, h2, h3, hga, ht, hg, n1, n2, rfl⟩ | ⟨p, hp, hcp', hm, ha, hb, h16⟩ | ⟨ha, hb⟩) |
      ⟨y, hy, hm, rfl⟩)
    · have hwp := irq_wr_own hI hL hok (lk := lk σ) hw
      refine wSR b ha hwp ?_
      rcases hw with ⟨o, ho, h8, rfl⟩ | ⟨k, h1, h2, h3, rfl⟩ | h | rfl | rfl | rfl | rfl
      · exact (gN o ho h8).2.2.2
      · exact sr_tcb hK hX htH hcur (o := k) (by omega) (by omega) h3
      · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) h.inSC).1
      · exact (srw_sc hK hX (st_scH (K := K) hcs) (cscHome hok) (scq_of hO hSs hcs).2.2.1.1).1
      · exact sr_tcb hK hX htH hcur (o := 3480#u64) (by simp) (by simp) (by simp)
      · exact sr_tcb hK hX htH hcur (o := 3488#u64) (by simp) (by simp) (by simp)
      · exact sr_tcb hK hX htH hcur (o := 3592#u64) (by simp) (by simp) (by simp)
    · have g := gN layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      exact wSR _ g.1 (held_core (hL.own_node _ (by simp [layout.node.CUR_TIME]))) g.2.2.2
    · have g := gN layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
      exact wSR _ g.1 (held_core (hL.own_node _ (by simp [layout.node.CONSUMED]))) g.2.2.2
    · have g := gC 3328#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
      rw [Fl4Proofs.P1.stA_eq]
      refine wSR _ g.1 (held_core ?_) g.2.2.2
      rw [ownT _ 3328#u64 hcT (by simp) (by simp), tcbOwner, if_neg (by simp [GateField]),
        if_neg (by simp [TimerField]), if_neg (by simp [GField])]
      exact congrArg Owner.core (affC _ hcT)
    · obtain ⟨y, hy, ya, k, h1, h2, h8, rfl⟩ := hw
      exact wSR _ ha (held_core (ftree_own hL hT hy ya (by omega) (by omega) h8))
        (gKey y k hy ya (by omega) (by omega) h8).2.2.2
    · obtain ⟨-, hb0, k, hk, h8, h24, rfl⟩ := hw
      exact wSR _ ha (held_core (((ntAll hb0).2 k hk h8).2 h24)) ((ntAll hb0).2 k hk h8).1.2.2.2
    · have g := gKey y 3568#u64 hy ya (by simp) (by simp) (by simp)
      exact wSR _ g.1 (held_core (ftree_own hL hT hy ya (k := 3568#u64) (by simp) (by simp) (by simp))) g.2.2.2
    · have g := gKey tm 3528#u64 tmT tmArm (by simp) (by simp) (by simp)
      exact wSR _ g.1 (held_core (ftree_own hL hT tmT tmArm (k := 3528#u64) (by simp) (by simp) (by simp))) g.2.2.2
    · obtain ⟨a1, -, s1⟩ := sH y k hy.1 hm h1 h2 h3
      exact wSR _ a1 (loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, k, h1, h2, h3, hga, ht, hg, rfl⟩))) s1
    · exact wSR _ ha (loc_wr_own hI hL (Or.inr (Or.inr ⟨p, hp, hcp', hb, h16⟩)))
        (srw_sc hK hX (st_scH (K := K) hp) hm hb).1
    · exact wSR _ ha (lkw_own hI hL (lk := lk σ) (Lk := lk σ) (fun _ h => h) hb).1 (srLk b hb)
    · obtain ⟨a1, -, s1⟩ := sH y 3328#u64 hy.1 hm (by simp) (by simp) (by simp)
      rw [Fl4Proofs.P1.stA_eq]
      exact wSR _ a1 (loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, 3328#u64, by simp, by simp, by simp,
        by unfold GateField; simp, by unfold TimerField; simp, by unfold GField; simp, rfl⟩))) s1
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hWd : ∀ x, Wd x → Aligned x ∧ (¬ x ∈ K.user → HeldV c hs (ownP K μ x)) := by
    intro x hx
    obtain ⟨ha, hw, hp, hvo⟩ := gW x hx
    refine ⟨ha, fun _ => ?_⟩
    have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hp, ← hc, ← hl]
      exact heldV_of_heldBy hw
    rw [eown, hvo] at h1
    rw [hV.1 x (Or.inl h1)]
    exact h1
  have hRPO : ∀ x, ¬ x ∈ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm hx.1.1.1
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  -- the checked writes
  have hpA : fld (L.curW σ) oAFFINITY ∉ K.ptes := (gC 3520#u64 (by simp) (by simp) (by simp) (Or.inl (by simp))
    (by simp) (by simp)).2.2.2.2
  have hμc : μ (fld (L.curW σ) oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld (L.curW σ) oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpA]; exact OwnMap.own_aff_gate hK0 htH μ
    rw [← hV.2.1 _ hpo]; exact hcur
  have hpT : fld tm oAFFINITY ∉ K.ptes := (gTm 3520#u64 (by simp) (by simp) (by simp) (Or.inl (by simp))
    (by simp) (by simp)).2.2.2.2
  have hμT : μ (fld tm oAFFINITY) = c := by
    have hpo : PO c hs (ownP K μ (fld tm oAFFINITY)) := by
      right; rw [ownP_eq_own nv hpT]; exact OwnMap.own_aff_gate hK0 tH μ
    rw [← hV.2.1 _ hpo]; exact hHome
  have hPal : ∀ x q v, P x q v → Aligned q := fun x q v h => (gW q (hPW x q v h)).1
  have heapT : ∀ y, y ∈ Heap.tcbs K.toKLayout.heap → K.toKLayout.heap y = some .tcb := fun y hy => hy
  have hStep : ∀ (x : S) (q v : U64) (x' : S), (fun _ : S => True) x → P x q v → st.write x q v = ok x' →
      PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem x)
        (L.mem x') ∧ (fun _ : S => True) x' := by
    intro x q v x' _ hP hw
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    refine ⟨?_, trivial⟩
    have ha := hPal x q v hP
    rcases hP with ((hW | ⟨rfl, rfl, e3, e4⟩) | ⟨-, -, hw' | hw'⟩ | ⟨-, y, hy, -, rfl, hcnd⟩ | ⟨-, rfl, e3, hcnd⟩) |
      (⟨y, hy, hm, k, h1, h2, h3, hga, ht, hg, n1, n2, rfl⟩ | ⟨p, hp, -, -, -, hb, h16⟩ | ⟨-, hb⟩) |
      ⟨y, hy, hm, rfl, hx, hq0, hv⟩
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := by
        rcases hW with ⟨-, -, hw', hn⟩ | rfl | rfl
        · exact irq_wr_nondec hK0 hI hL hw' hn
        · exact OwnMap.nondec_of_region hK0 (Or.inr (Or.inl ⟨_, hL.nd _ (by simp [layout.node.CUR_TIME])⟩))
        · exact OwnMap.nondec_of_region hK0 (Or.inr (Or.inl ⟨_, hL.nd _ (by simp [layout.node.CONSUMED])⟩))
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd))
    · have es : stA (L.curW σ) = fld (L.curW σ) oSTATE := by rw [Fl4Proofs.P1.stA_eq]; rfl
      rw [es]
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_state hK0 hUO (m0 := μ) htH e4 hμc
        (fun hq' => absurd hq' (by rw [← es, e3]; simp [OwnMap.QueuedState, sched.TS_RESTART]))
        (fun hq' => absurd hq' (by simp [OwnMap.QueuedState, sched.TS_RUNNING]))))
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := by
        obtain ⟨y, hy, -, k, h1, h2, -, rfl⟩ := hw'
        apply OwnMap.nondec_of_region hK0
        have e : (core.num.U64.wrapping_add y k).val - y.val = k.val := by
          rw [field_val (hT y hy) (by omega)]; omega
        exact Or.inl ⟨y, hL.tcb y hy k (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd))
    · have hnd : ¬ OwnMap.DecW K.toKLayout q := by
        obtain ⟨hne', hb, k, hk, -, h24, rfl⟩ := hw'
        apply OwnMap.nondec_of_region hK0
        obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne'
        have hNt := hI.2.2.1.2.2.bnd _ q1 hb
        obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hY.ntw _ hNt k hk, ?_⟩))))
        rw [ntfn_word_val p1 p2 hk]
        omega
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha hnd))
    · have eh : thA y = fld y oTIMER_HEIGHT := rfl
      rw [eh]
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (stepOK_height hK0 hUO (m0 := μ) (heapT y hy) hcnd))
    · exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (stepOK_deadline hK0 hUO (m0 := μ) tH e3 hμT hcnd))
    · exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha
        (locw_nondec hK0 hT hL hy.1 h1 h2 hga ht n1 n2)))
    · exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha
        (scw_nondec hK0 hL hp hb h16)))
    · exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_nondec hK0 hUO (m0 := μ) ha
        (lkw_nondec hK0 hI hL hb)))
    · rw [es]
      exact stepOKP_of_stepOKV (stepOKV_of_stepOK hK.base (OwnMap.stepOK_state hK0 hUO (m0 := μ) (heapT y hy.1)
        hx (hμY y hy.1 hm) (fun hq' => by rw [← hl, ← eB]; exact hq0 (by rw [es]; exact hq'))
        (fun hq' => absurd hq' hv)))
  have hPd : ∀ x x' q v, (∀ w, Rd w → L.mem x' w = L.mem x w) → P x q v → P x' q v := by
    rintro x x' q v hag' (((h | ⟨e1, e2, e3, e4⟩) | h | ⟨hok, y, hy, ya, e1, hcnd⟩ | ⟨hok, e1, e3, hcnd⟩) | h |
      ⟨y, hy, hm, e1, hx, hq0, hv⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr ⟨e1, e2, by rw [hag' _ (rn _ rSt)]; exact e3, by rw [hag' _ (rn _ rAf)]; exact e4⟩))
    · exact Or.inl (Or.inr (Or.inl h))
    · have yT := hT _ hy
      have d1 : Rd (tdA y) := rF hok _ (field_aligned yT (by simp) (by simp))
        (Or.inr (Or.inl ⟨y, hy, ya, 3528#u64, by simp, by simp, by simp, rfl⟩))
      have d2 : Rd (thA y) := rF hok _ (field_aligned yT (by simp) (by simp))
        (Or.inr (Or.inl ⟨y, hy, ya, 3568#u64, by simp, by simp, by simp, rfl⟩))
      refine Or.inl (Or.inr (Or.inr (Or.inl ⟨hok, y, hy, ya, e1, ?_⟩)))
      rw [hag' _ d1, hag' _ d2]
      exact hcnd
    · have d0 : Rd (affA tm) := rPl 3520#u64 (Or.inl (by simp))
      have d1 : Rd (tdA tm) := rF hok _ (field_aligned (hT _ tmT) (by simp) (by simp))
        (Or.inr (Or.inl ⟨tm, tmT, tmArm, 3528#u64, by simp, by simp, by simp, rfl⟩))
      have d2 : Rd (thA tm) := rPl 3568#u64 (Or.inr (Or.inl (by simp)))
      have e3' : L.mem x (affA tm) = c := e3
      have hc' : L.mem x (tdA tm) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem x (thA tm)).val >>> 8 = c.val := hcnd
      have d0' : L.mem x' (affA tm) = L.mem x (affA tm) := hag' _ d0
      have d1' : L.mem x' (tdA tm) = L.mem x (tdA tm) := hag' _ d1
      have d2' : L.mem x' (thA tm) = L.mem x (thA tm) := hag' _ d2
      have hc'' : L.mem x' (tdA tm) ≠ 0#u64 ∨ v ≠ 0#u64 → (L.mem x' (thA tm)).val >>> 8 = c.val := by
        rw [d1', d2']; exact hc'
      exact Or.inl (Or.inr (Or.inr (Or.inr ⟨hok, e1, d0'.trans e3', hc''⟩)))
    · exact Or.inr (Or.inl h)
    · have dA : Rd (affA y) := rL _ (Or.inl ⟨y, hy, hm, 3520#u64, by simp, by simp, by simp,
        by unfold TimerField; simp, by unfold GField; simp, rfl⟩)
      have dS : Rd (stA y) := by
        rw [Fl4Proofs.P1.stA_eq]
        exact rL _ (Or.inl ⟨y, hy, hm, 3328#u64, by simp, by simp, by simp,
          by unfold TimerField; simp, by unfold GField; simp, rfl⟩)
      have dB : Rd (blockA y) := by
        rw [blockA_eq]
        exact rL _ (Or.inl ⟨y, hy, hm, 3336#u64, by simp, by simp, by simp,
          by unfold TimerField; simp, by unfold GField; simp, rfl⟩)
      have dA' : L.mem x' (affA y) = L.mem x (affA y) := hag' _ dA
      have dS' : L.mem x' (stA y) = L.mem x (stA y) := hag' _ dS
      have dB' : L.mem x' (blockA y) = L.mem x (blockA y) := hag' _ dB
      refine Or.inr (Or.inr ⟨y, hy, hm, e1, by rw [dA']; exact hx, fun hq' => ?_, hv⟩)
      rw [dB']; exact hq0 (by rw [← dS']; exact hq')
  -- (gen 26) the notification wakes somebody at the view start; its waiting head is homed
  have e1N : ρ (boundA tm) = N := by
    have g := gTm 3368#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)
    exact (kvR _ g).symm
  have eSt : L.mem σ (stA tm) = ρ (stA tm) := by
    rw [Fl4Proofs.P1.stA_eq]
    exact kvR _ (gTm 3328#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp))
  have hWkσ : ¬ NoWake st σ := by
    intro hNW
    apply hW2
    unfold NoWakeR
    rw [e1N]
    by_cases hb0 : N = 0#u64
    · exact Or.inl hb0
    obtain ⟨hbt, gA⟩ := ntAll hb0
    have eT : L.mem σ (epTSA N) = ρ (epTSA N) :=
      kvR _ (gA layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])).1
    have eS : L.epState σ N = ρ (epTSA N) &&& 3#u64 := by
      unfold LawfulStore.epState
      rw [eT]
    have eBt : L.mem σ (ntfnBtA N) = ρ (ntfnBtA N) :=
      kvR _ (gA layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB])).1
    have hNW' : N = 0#u64 ∨ (L.epState σ N ≠ obj.NTFN_IDLE ∧ L.epState σ N ≠ obj.NTFN_WAITING) ∨
        (L.epState σ N = obj.NTFN_IDLE ∧
          (L.mem σ (ntfnBtA N) = 0#u64 ∨ L.mem σ (stA (L.mem σ (ntfnBtA N))) ≠ sched.TS_BLOCKED_ON_RECV)) := hNW
    rcases hNW' with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h hb0
    · exact Or.inr (Or.inl ⟨by rw [← eS]; exact h1, by rw [← eS]; exact h2⟩)
    · refine Or.inr (Or.inr ⟨by rw [← eS]; exact h1, ?_⟩)
      rw [hbt] at h2
      rw [← eBt, hbt, ← eSt]
      exact h2
  have hb0 : N ≠ 0#u64 := fun e => hWkσ (Or.inl e)
  obtain ⟨hbt, gA⟩ := ntAll hb0
  have eT : L.mem σ (epTSA N) = ρ (epTSA N) :=
    kvR _ (gA layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])).1
  have eHd : L.mem σ (epHeadA N) = ρ (epHeadA N) :=
    kvR _ (gA layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])).1
  have hHw : L.epState σ N = obj.NTFN_WAITING → ρ (fld (L.epQ σ N).head oAFFINITY) = c := by
    intro hw
    have hw' : (ρ (epTSA (ρ (boundA tm))) &&& 3#u64) = obj.NTFN_WAITING := by
      rw [e1N, ← eT]; exact hw
    have h := hW3 hw'
    rw [e1N, ← eHd] at h
    exact h
  have hNtN : N ∈ K.toKLayout.heap.ntfns := hI.2.2.1.2.2.bnd _ tmT hb0
  have hHw0 : L.mem σ (core.num.U64.wrapping_add N layout.ntfn.HEAD) ≠ 0#u64 →
      ρ (fld (L.mem σ (core.num.U64.wrapping_add N layout.ntfn.HEAD)) oAFFINITY) = c := by
    intro hne'
    have h := hHw (ntfn_head_wait h0 hNtN hne')
    have e : core.num.U64.wrapping_add N layout.ntfn.HEAD = epHeadA N := by
      unfold epHeadA; rw [ntfn_head_eq]
    rw [e]; exact h
  -- the run at the view start, on the checked store
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localtimer.handle_timer_irq_local mm ar x a irq pl =
        interp mm ar (R.localtimer.handle_timer_irq_local irq pl) x a :=
    fun mm x a => congrFun (congrFun (irq_isProg S irq pl A ar mm) x) a
  obtain ⟨r, hr, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar σ a irq pl LawfulStore.total hA)
  have hgσ : localtimer.handle_timer_irq_local (gd st Rd P) ar σ a irq pl = ok r := by
    by_cases hfa : r.1 = true ∧ IrqFire st ar σ a
    · obtain ⟨b, s', a'⟩ := r
      obtain ⟨hb, hq'⟩ := hfa
      simp only at hb
      subst hb
      obtain ⟨-, -, -, tip, -, -, -, -, -, -, -, -, -, -, etip, eb, eok, -⟩ := fire_eqs ar hA hq' hr
      obtain ⟨hmr, hsct, hcore⟩ := current_ok_true eok
      obtain ⟨-, haff, -, -⟩ := may_run_here_true hmr
      have hok : IrqOk st σ := ⟨haff, hsct, hcore⟩
      obtain ⟨hPE, hPR⟩ := plan_pe_pr hI etip eb
      obtain ⟨U, hB⟩ := hQJ.bufAt
      exact WH.irq_acc_fire_wkG (gS := gd st Rd P) (R := Rd) (W := WAll P)
        (Hm := fun y => ρ (fld y oAFFINITY) = c) (Hs := fun p => ρ (fld p 16#u64) = c) (Lk := lk σ) (U := U)
        ar hA hI hL hY.ntw E0.nth hq' hWkσ
        (fun hok' w ha hw => rF hok' w ha hw)
        (fun hok' w ha hw hn => fun _ _ => by
          rcases hw with hw | hw | hw
          · exact Or.inl (Or.inl (Or.inl (Or.inl ⟨hok', ha, hw, hn⟩)))
          · exact Or.inl (Or.inr (Or.inl ⟨hok', ha, Or.inl hw⟩))
          · exact Or.inl (Or.inr (Or.inl ⟨hok', ha, Or.inr hw⟩)))
        (fun _ i hi => rn _ (rI i hi)) (fun _ => rn _ (rK _ (Or.inl rfl)))
        (fun _ => rn _ (rK _ (Or.inr (Or.inl rfl))))
        (fun _ X hX haff => gd_write (Or.inl (Or.inl (Or.inr ⟨rfl, rfl, hX, haff.trans hc⟩))))
        (fun X y v hy ya hcnd => gd_write (Or.inl (Or.inr (Or.inr (Or.inl ⟨hok, y, hy, ya, rfl, fun h => by
          rw [← hc]; exact hcnd h⟩)))))
        (fun X y v hy ya hyt ha1 _ hcnd => by
          subst hyt
          exact gd_write (Or.inl (Or.inr (Or.inr (Or.inr ⟨hok, rfl, ha1.trans hc, fun h => by
            rw [← hc]; exact hcnd h⟩)))))
        E0.aff rHx rCx
        (fun y hy hm k h1 h2 h3 ht hg => rL _ (Or.inl ⟨y, hy, hm, k, h1, h2, h3, ht, hg, rfl⟩))
        (fun y hy hm k h1 h2 h3 hga ht hg n1 n2 => fun _ _ =>
          Or.inr (Or.inl (Or.inl ⟨y, hy, hm, k, h1, h2, h3, hga, ht, hg, n1, n2, rfl⟩)))
        (fun p hp hcp' hm b ha hb => rL _ (Or.inr (Or.inl ⟨p, hp, hcp', hm, ha, hb⟩)))
        (fun p hp hcp' hm b ha hb h16 => fun _ _ =>
          Or.inr (Or.inl (Or.inr (Or.inl ⟨p, hp, hcp', hm, ha, hb, h16⟩))))
        (fun y hy hqs hlk k hk => by
          have ha := field_aligned (hT y hy) (K := k) (by omega) (by omega)
          have hw : LkW st K.toKLayout (Heap.tcbs K.toKLayout.heap) (lk σ) σ (core.num.U64.wrapping_add y k) :=
            Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩
          exact ⟨rL _ (Or.inr (Or.inr (Or.inr ⟨ha, hw⟩))), fun _ _ => Or.inr (Or.inl (Or.inr (Or.inr ⟨ha, hw⟩)))⟩)
        (fun X y v hy hm haff hq0 hv => gd_write (Or.inr (Or.inr ⟨y, hy, hm, rfl, haff.trans hc, hq0, hv⟩)))
        (hPL σ).1 (hPL σ).2.1
        (fun k h1 h2 h3 => fun _ _ => by
          obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNtN
          have ha : Aligned (core.num.U64.wrapping_add N k) := by
            unfold Aligned; rw [ntfn_word_val p1 p2 h1]; omega
          exact Or.inl (Or.inr (Or.inl ⟨hok, ha, Or.inr ⟨hne, hb0, k, h1, h2, h3, rfl⟩⟩)))
        (fun hep k h1 h2 => by
          obtain ⟨hH', hal'⟩ := hPE hep
          have hw : LkW st K.toKLayout (Heap.tcbs K.toKLayout.heap) (lk σ) σ (core.num.U64.wrapping_add pl.ep k) :=
            Or.inr ⟨pl.ep, (hPL σ).2.1 hep, hOL.1 _ hH' k h1⟩
          exact ⟨rL _ (Or.inr (Or.inr (Or.inr ⟨hal' k h1 h2, hw⟩))),
            fun _ _ => Or.inr (Or.inl (Or.inr (Or.inr ⟨hal' k h1 h2, hw⟩)))⟩)
        (fun hr' => by
          obtain ⟨hR, hal'⟩ := hPR hr'
          have hw : LkW st K.toKLayout (Heap.tcbs K.toKLayout.heap) (lk σ) σ (rTcbA pl.reply) :=
            Or.inr ⟨pl.reply, (hPL σ).2.2 hr', by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩
          exact fun _ _ => Or.inr (Or.inl (Or.inr (Or.inr ⟨hal', hw⟩))))
        (irq_bufAt_runB ar hA hI hB hq' hr) E0.asid
        (fun y hy hm => ⟨rL _ (Or.inr (Or.inr (Or.inl ⟨y, hy, hm, Or.inl rfl⟩))),
          rL _ (Or.inr (Or.inr (Or.inl ⟨y, hy, hm, Or.inr rfl⟩)))⟩)
        (rn _ (rK _ (Or.inr (Or.inr rfl))))
        (fun hi hhi => ⟨rn _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hok, hi, hhi, Or.inl rfl⟩)))))),
          fun lo hlo hne' => rn _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            ⟨hok, hi, hhi, Or.inr ⟨lo, hlo, hne', rfl⟩⟩))))))⟩)
        hHr hHsc hHs hHw hHw0 hHome hr
    · refine irq_pl_guard ar (gS := gd st Rd P) (R := Rd)
        (fun _ i hi => rn _ (rI i hi))
        (rn _ (rN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun _ => ⟨rPl 3520#u64 (Or.inl (by simp)), rPl 3568#u64 (Or.inr (Or.inl (by simp))),
          rPl 3368#u64 (Or.inr (Or.inr (Or.inl (by simp)))), fun _ => ⟨?_, rPl 3336#u64 (by simp),
          rPl 3360#u64 (by simp), fun n en hn0 => ?_⟩⟩) ?_ hr
      · show Rd (stA tm)
        rw [Fl4Proofs.P1.stA_eq]
        exact rPl 3328#u64 (by simp)
      · rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) σ _)] at en
        have en' : L.mem σ (boundA tm) = n := ok_inj_ff en
        subst en'
        exact ⟨Or.inl (Or.inr (Or.inr (Or.inr ⟨hn0, Or.inl rfl⟩))), Or.inl (Or.inr (Or.inr (Or.inr ⟨hn0, Or.inr rfl⟩)))⟩
      · intro mx emx hle ei1 tip etip eb hrt
        exact irqTail_guardP (gS := gd st Rd P) (R := Rd) (W := WAll P) ar hA hI
          (fun o h1 h2 => rn _ (rN o h1 h2))
          (current_ok.guardC2 (gS := gd st Rd P) σ _ _ _ csc0 (rn _ rAf) (fun _ =>
            ⟨rn _ rSt, rn _ (rC 3472#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)),
              rn _ (rC 3664#u64 (by simp) (by simp) (by simp) (Or.inr (by simp)) (by simp) (by simp)),
              rn _ (rC 3464#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)),
              fun hne' => rn _ (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne', rfl⟩)))),
              rn _ (rN _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])),
              rn _ (rC 3432#u64 (by simp) (by simp) (by simp) (Or.inl (by simp)) (by simp) (by simp)),
              rn _ (rK _ (Or.inl rfl))⟩))
          (fun hok w ha hw => rn _ (Or.inr (Or.inr (Or.inl ⟨hok, ha, hw⟩))))
          (fun hok w ha hw hn => fun _ _ => Or.inl (Or.inl (Or.inl (Or.inl ⟨hok, ha, hw, hn⟩))))
          (fun _ i hi => rn _ (rI i hi))
          (fun _ => rn _ (rK _ (Or.inl rfl))) (fun _ => rn _ (rK _ (Or.inr (Or.inl rfl))))
          (fun _ _ X hX haff => gd_write (Or.inl (Or.inl (Or.inr ⟨rfl, rfl, hX, haff.trans hc⟩))))
          (fun _ => rn _ (rK _ (Or.inr (Or.inr rfl))))
          (fun hok hi hhi => ⟨rn _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hok, hi, hhi, Or.inl rfl⟩)))))),
            fun lo hlo hne' => rn _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hok, hi, hhi, Or.inr ⟨lo, hlo, hne', rfl⟩⟩))))))⟩)
          E0.asid (fun _ _ => Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl)))))
          (fun _ _ => Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl)))))
          emx hle ei1
          (fun hok s1 a1 now eu _ => by
            obtain ⟨n1, -, er⟩ := ut_now ar hA hN eu
            simp only at er
            exact WH.fire_ok_guardWK (Hm := fun y => ρ (fld y oAFFINITY) = c) hI hL hY.ntw
              (fun w ha hw => rF hok w ha hw) rHx rCx hHr hHome hHw0 (rn _ (rK _ (Or.inl rfl))) E0.nth
              (by rw [er, utW_ksb]) (by rw [er, utW_cpu]) (fun b hb h1 h2 => by rw [er]; exact utW_mem hN n1 hb h1 h2)
              etip eb _ _)
          (fun h1 h2 => hfa ⟨h1, h2⟩) hrt
  rw [hp] at hgσ
  -- every state carrying `ρ` on the reads runs as the view start
  have hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → (∀ b, Rd b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rd Wd) ar (R.localtimer.handle_timer_irq_local irq pl) s a = ok r ∧
        WithinM st ar (fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ)
          (· ∈ K.user) c hs (L.mem x) (L.mem y)) (R.localtimer.handle_timer_irq_local irq pl) s a := by
    intro s hcs' hks hag
    have hagR : ∀ b, Rd b → L.mem s b = L.mem σ b := fun b hb => (hag b hb).trans (kvR b (gRd b hb)).symm
    obtain ⟨x0, s0', a0'⟩ := r
    obtain ⟨s1', hs1⟩ := interp_agree_gd (st := st) (masksWr_plain st) hal hPal hPd
      (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) σ s a x0 s0' a0' hks hcs'
      (by rw [PlainStore.frame_masks_eq, PlainStore.frame_masks_eq]) hagR hgσ
    refine ⟨_, interp_gd_guard (R' := Rd) (W := Wd) (fun q h => h) hPW _ s a _ hs1, ?_⟩
    have hm := interp_gd (R := Rd) (P := P)
      (Q := fun x y => PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs
        (L.mem x) (L.mem y)) (I := fun _ => True) hStep _ s a _ trivial hs1
    exact (interp_mguard _ s a _ hm).2
  exact ⟨hal, hR0, hWd, hRPO, hgo, fun x hx => (gW x hx).2.1, hne⟩

set_option maxHeartbeats 32000000 in
/-- **U9's armed timer-interrupt program is `Safe` at a view start whose earliest thread is homed and whose
notification wakes a thread of `c`** (module docstring). -/
theorem irq_wh_annV (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅)
    {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {irq : U64} {pl : localtimer.TimerIrqPlan} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hirq : irq.val < 128)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hPL : PlanLk lk pl) (hH : IrqWhR ρ c (ρ (tmA (L := L) σ))) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_timer_irq_local irq pl) ∅ a)) := by
  obtain ⟨hal, hR0, hWd, hRPO, hgo, -, -⟩ := irq_wh_cert ar hA hK hU nv hV hJ hq hirq hc hl hmm hPL hH
  have h := PathObl.safe_tr_wr (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) (masksWr_plain st) (a := a)
    (R.localtimer.handle_timer_irq_local irq pl) (irq_noZero irq pl) hc
    (Ro := fun q => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q)
    (Rd := IrqWhRd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c irq σ) (Wd := IrqWhWd st K.toKLayout (Heap.tcbs K.toKLayout.heap) (Heap.scs K.toKLayout.heap) (Heap.scBits K.toKLayout.heap) (lk σ) ρ c σ)
    hal hR0 hWd hRPO (fun x hx => hV.2.1 x hx) hgo
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
