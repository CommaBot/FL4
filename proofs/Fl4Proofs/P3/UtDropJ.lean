/-
P3 (DESIGN.md §9), Untyped's reset (the drop step), part 4: **the drop's
closure premises at `J`** (handoff/utj.md "Round 8", item 1). At a `JAtZ`
state with a childless RAM untyped cap `x` over `[p, p + 2^sb)`:

* `JAtZ.rgDeadD`: every object of `H` meeting the region is dead
  (`region_deadP`: uncovered, so in `JCovD`'s dead set);
* `JAtZ.rgTcb`/`rgEp`/`rgNtfn`/`rgReply`/`rgSc`: a spec object at an
  address of the region has the spec links of a dead object (inactive with
  no SC, bound notification or yield SC; an idle endpoint; a notification
  with no queue, bound thread or SC; a reply with no TCB; an SC with no
  TCB, notification, yielder or reply), through the relations (`TcbRel`,
  `YieldRel`, `EpObjRel`, `NtfnRel1`, `IpcRel.reply`, `ScRelW`,
  `CallRel.stack` with `scReply_ne`);
* `JAtZ.sKeep`: `SKeep` of the region (UtDropSpec), every link's both ends
  off the region: the dead object's link is null, and a live object's link
  into the region contradicts a back-link — `SchedValid` (queues, replies,
  yield), `Inv.back`/`rq`/`rel`, `ActIdle`, `CurInv` (no reschedule pending:
  the untyped invocation runs), `ntfn_link`, P1's `TSc` (an SC's thread
  names it back), `RFree` (a free reply is on no call stack), and for the
  three links with no back-link in the invariants (a TCB's and an SC's bound
  notification, a notification's bound TCB) `KeptRefsP3` (the existing [J]
  `RegionUnrefJ`'s first part, instantiated at this region);
* `JAtZ.xKeep`: `XKeep` (UtDropSets' stage-A premises) from `SKeep` and the
  relations;
* `JAtZ.dropX`: `XTopAt.drop` at `J`, its non-[J] inputs discharged here
  (UtInv, the cap, NoStraddle and the MDB slots off the region from
  `UtCapP3`); left as premises: the spec's detype (`SDrop` and the kept
  spec fields: the spec step's own facts) and `VsReachMiss` [J] (VsDrop).
-/
import Fl4Proofs.P3.UtDropX
import Fl4Proofs.P3.XTopJointFin
import Fl4Proofs.P3.XTopJointRemove
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- An object of `H` at an address of the region meets it. -/
theorem rgOf_regionD {p sb : U64} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) {q : U64}
    {k : P1.HKind} (hq : H q = some k) (hr : RgOf p sb q.bv) :
    P1.RegionD H p.val (p.val + 2 ^ sb.val) q := by
  obtain ⟨h1, h2⟩ := (rgOf_iff hsb hfit q).1 hr
  unfold P1.RegionD P1.MeetsR
  rw [hq]
  simp only [Option.elim]
  have := Nat.one_le_two_pow (n := k.bits)
  omega

/-- **The objects meeting a childless RAM untyped region are dead.** -/
theorem JAtZ.rgDeadD (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : x ∈ Z.G.chains.flatten)
    {p sb fi : U64} (hcx : capV (L.mem s) x = .Untyped p sb fi false) (hnd : ∀ y, ¬ Mdb.Desc Z.G.par y x) :
    ∀ q, P1.RegionD H p.val (p.val + 2 ^ sb.val) q → DeadP (L := L) H s q := by
  intro q hq
  obtain ⟨-, ⟨-, -, -, -, hI⟩, -⟩ := J.xtop.rel
  cases e : H q with
  | none => exact DeadP.none e
  | some k => exact (region_deadP J.jcov J.ut hI hx hcx (Or.inr ⟨hnd, le_rfl⟩) le_rfl q k e hq).2

section Rg
variable {p sb : U64} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
  (hRD : ∀ q, P1.RegionD H p.val (p.val + 2 ^ sb.val) q → DeadP (L := L) H s q)
include hsb hfit hRD

/-- A spec TCB in the region is a dead thread's. -/
theorem JAtZ.rgTcb (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap o = some (.tcb x)) (hr : RgOf p sb o) :
    tsCode x.tcbState = 0 ∧ x.tcbSchedContext = none ∧ x.tcbBoundNotification = none ∧ x.tcbYieldTo = none := by
  obtain ⟨t, ht, rfl⟩ := J.obj.tcb o x hk
  have hH := J.zH.1 t ht
  obtain ⟨d1, d2, d3, -, -, d6⟩ := (hRD t (rgOf_regionD hsb hfit hH hr)).1 hH
  obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb t ht
  rw [hk] at hk'; cases hk'
  obtain ⟨y, hy, ey⟩ := J.yld.tcb t ht
  rw [hk] at hy; cases hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := hR.st; rw [← stA_tStA, d1] at this; unfold sched.TS_INACTIVE at this; simpa using this.symm
  · rw [hR.sc, d2, optRef_zero]
  · rw [hR.bound, show tBoundA t = P1.boundA t from rfl, d3, optRef_zero]
  · rw [ey, d6, optRef_zero]

/-- A spec endpoint in the region is idle. -/
theorem JAtZ.rgEp (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : Fl4Spec.ObjRef} {x : Fl4Spec.Endpoint}
    (hk : σ.kheap o = some (.endpoint x)) (hr : RgOf p sb o) : x.epQueue = [] := by
  obtain ⟨e, he, rfl⟩ := J.obj.ep o x hk
  have hH := J.zH.2.1 e he
  have d := (hRD e (rgOf_regionD hsb hfit hH hr)).2.1 hH
  rw [epState_eq] at d
  obtain ⟨x', hk', hR⟩ := J.xtop.ipc.ep e he
  rw [hk] at hk'; cases hk'
  cases x with
  | idleEP => rfl
  | sendEP q => obtain ⟨h1, -⟩ := hR; rw [d] at h1; exact absurd h1 (by decide)
  | recvEP q => obtain ⟨h1, -⟩ := hR; rw [d] at h1; exact absurd h1 (by decide)

/-- A spec notification in the region has no queue, bound thread or SC. -/
theorem JAtZ.rgNtfn (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : Fl4Spec.ObjRef}
    {x : Fl4Spec.Notification} (hk : σ.kheap o = some (.notification x)) (hr : RgOf p sb o) :
    Fl4Spec.ntfnQueueOf x = [] ∧ x.ntfnBoundTcb = none ∧ x.ntfnSc = none := by
  obtain ⟨n, hn, rfl⟩ := J.obj.ntfn o x hk
  have hH := J.zH.2.2.2 n hn
  obtain ⟨d1, d2, d3⟩ := (hRD n (rgOf_regionD hsb hfit hH hr)).2.2.1 hH
  rw [epState_eq] at d1
  obtain ⟨x', hk', hR⟩ := J.xtop.ipc.ntfn n hn
  rw [hk] at hk'; cases hk'
  refine ⟨?_, ?_, ?_⟩
  · have hO := hR.obj
    cases h : x.ntfnObj with
    | idleNtfn => simp [Fl4Spec.ntfnQueueOf, h, Fl4Spec.Ntfn.ntfnQueue]
    | activeNtfn b => simp [Fl4Spec.ntfnQueueOf, h, Fl4Spec.Ntfn.ntfnQueue]
    | waitingNtfn l => rw [h] at hO; exact absurd hO.1 d1
  · rw [hR.bound, show nBoundA n = P1.ntfnBtA n from rfl, d2, optRef_zero]
  · rw [hR.sc, show nScA n = P1.ntfnScA n from rfl, d3, optRef_zero]

/-- A spec reply in the region has no TCB. -/
theorem JAtZ.rgReply (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : Fl4Spec.ObjRef} {x : Fl4Spec.Reply}
    (hk : σ.kheap o = some (.reply x)) (hr : RgOf p sb o) : x.replyTcb = none := by
  obtain ⟨r, hrR, rfl⟩ := J.obj.reply o x hk
  have hH := J.zH.2.2.1 r hrR
  have d := (hRD r (rgOf_regionD hsb hfit hH hr)).2.2.2.1 hH
  obtain ⟨x', hk', hR⟩ := J.xtop.ipc.reply r hrR
  rw [hk] at hk'; cases hk'
  rw [hR, show Endp.rTcbA r = P1.rTcbA r from rfl, d, optRef_zero]

/-- A spec SC in the region has no TCB, notification, yielder or reply. -/
theorem JAtZ.rgSc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {o : Fl4Spec.ObjRef}
    {y : Fl4Spec.SchedContext} {k : Nat} (hk : σ.kheap o = some (.schedContext y k)) (hr : RgOf p sb o) :
    y.scTcb = none ∧ y.scNtfn = none ∧ y.scYieldFrom = none ∧ y.scReplies = [] := by
  obtain ⟨c, hc, rfl⟩ := J.obj.sc o y k hk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := (hJ.sc c y k (J.c0 c hc) hk).2
  obtain ⟨d1, d2, d3, d4⟩ := (hRD c (rgOf_regionD hsb hfit hH hr)).2.2.2.2 _ hH
  obtain ⟨Q, R0, hcr, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨y', n', hk', hR⟩ := hs.scs c hc
  rw [hk] at hk'; cases hk'
  have hL : Lst c = [] := by
    by_contra hne; exact J.scReply_ne hc hne d2
  obtain ⟨⟨y1, n1, hk1, hyL⟩, -⟩ := J.call.stack c hc
  rw [hk] at hk1; cases hk1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hR.tcb, scW_tcb, d1, optRef_zero]
  · rw [hR.ntfn, scW_ntfn, d3, optRef_zero]
  · rw [hR.yieldFrom, ← scYieldFromA_eq, d4, optRef_zero]
  · rw [hyL, hL]; rfl

theorem tsCode_zero {st : Fl4Spec.ThreadState} (h : tsCode st = 0) : st = .inactive := by
  cases st <;> simp_all [tsCode]

set_option maxHeartbeats 4000000 in
/-- **No spec link names an object of the region** (`SKeep`; module
docstring). -/
theorem JAtZ.sKeep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s) :
    SKeep (RgOf p sb) σ := by
  have tT := fun {o} {x} hk hr => J.rgTcb hsb hfit hRD (o := o) (x := x) hk hr
  have tE := fun {o} {x} hk hr => J.rgEp hsb hfit hRD (o := o) (x := x) hk hr
  have tN := fun {o} {x} hk hr => J.rgNtfn hsb hfit hRD (o := o) (x := x) hk hr
  have tR := fun {o} {x} hk hr => J.rgReply hsb hfit hRD (o := o) (x := x) hk hr
  have tC := fun {o} {y} {k} hk hr => J.rgSc hsb hfit hRD (o := o) (y := y) (k := k) hk hr
  have hV := J.sv
  have hIv := J.inv
  have hI := J.xtop.ipc
  obtain ⟨Q, R0, hcr, hs⟩ := J.xtop.fin.1.1.1.lists
  have hX := J.blk.2.2.1.2.2
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8⟩ := hKR
  -- a live thread (state not inactive) is off the region
  have live : ∀ {t x}, σ.kheap t = some (.tcb x) → tsCode x.tcbState ≠ 0 → ¬ RgOf p sb t :=
    fun hk h0 hr => h0 (tT hk hr).1
  have liveSc : ∀ {t x c}, σ.kheap t = some (.tcb x) → x.tcbSchedContext = some c → ¬ RgOf p sb t :=
    fun hk hc hr => by rw [(tT hk hr).2.1] at hc; cases hc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t x e pl hk hs
    refine ⟨live hk (by rw [hs]; simp [tsCode]), fun hr => ?_⟩
    · -- send: the endpoint
      obtain ⟨xe, hxe, hm⟩ := hV.sendQ t x e pl hk hs
      rw [tE hxe hr] at hm; cases hm
  · intro t x e r d hk hs
    refine ⟨live hk (by rw [hs]; simp [tsCode]), fun hr => ?_, fun r' er hr => ?_⟩
    · -- receive: the endpoint
      obtain ⟨xe, hxe, hm⟩ := hV.recvQ t x e r d hk hs
      rw [tE hxe hr] at hm; cases hm
    · -- receive: the reply
      subst er
      obtain ⟨xr, hxr, hm⟩ := hV.recvReply t x e r' d hk hs
      rw [tR hxr hr] at hm; cases hm
  · intro t x n hk hs
    refine ⟨live hk (by rw [hs]; simp [tsCode]), fun hr => ?_⟩
    · -- notification wait: the notification
      obtain ⟨xn, hxn, hm⟩ := hV.ntfnW t x n hk hs
      rw [(tN hxn hr).1] at hm; cases hm
  · intro t x r hk hs
    refine ⟨live hk (by rw [hs]; simp [tsCode]), fun hr => ?_⟩
    · -- on reply: the reply
      obtain ⟨xr, hxr, hm⟩ := hV.onReply t x r hk hs
      rw [tR hxr hr] at hm; cases hm
  · intro t x c hk hc
    refine ⟨liveSc hk hc, fun hr => ?_⟩
    · -- a thread's SC
      obtain ⟨y, n, hy, hyt⟩ := hIv.back t x c hk hc
      rw [(tC hy hr).1] at hyt; cases hyt
  · intro t x n hk hn
    refine ⟨(fun hr => by rw [(tT hk hr).2.2.1] at hn; cases hn), fun hr => ?_⟩
    · -- a thread's bound notification (KeptRefsP3)
      obtain ⟨t', ht', rfl⟩ := J.obj.tcb t x hk
      obtain ⟨x', hk', hR⟩ := hI.tcb t' ht'
      rw [hk] at hk'; cases hk'
      have hb := hR.bound
      rw [hn, show tBoundA t' = P1.boundA t' from rfl] at hb
      have h0 : L.mem s (P1.boundA t') ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb; cases hb
      have en : n = (L.mem s (P1.boundA t')).bv := by
        rw [Notif.optRef_ne h0] at hb; exact (Option.some.inj hb)
      have hH := J.zH.1 t' ht'
      have hnD : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) t' := fun hd => h0 ((hRD t' hd).1 hH).2.2.1
      have hNt := hX.bnd t' hH h0
      exact k4 t' hH hnD (by rw [hNt]; simp) (rgOf_regionD hsb hfit hNt (by rw [← en]; exact hr))
  · intro t x c hk hc
    refine ⟨(fun hr => by rw [(tT hk hr).2.2.2] at hc; cases hc), fun hr => ?_⟩
    · -- a thread's yield SC
      obtain ⟨t', ht', rfl⟩ := J.obj.tcb t x hk
      obtain ⟨y0, hy0, ey⟩ := J.yld.tcb t' ht'
      rw [hk] at hy0; cases hy0
      rw [ey] at hc
      have h0 : L.mem s (P1.yieldA t') ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hc; cases hc
      obtain ⟨-, y, n, hy, hyf⟩ := J.yld.toSc t' ht' h0
      rw [Notif.optRef_ne h0] at hc
      rw [← (Option.some.inj hc)] at hr
      rw [(tC hy hr).2.2.1] at hyf; cases hyf
  · intro e x hk u hu
    refine ⟨(fun hr => by rw [tE hk hr] at hu; cases hu), fun hr => ?_⟩
    · -- an endpoint's queued thread
      obtain ⟨e', he', rfl⟩ := J.obj.ep e x hk
      obtain ⟨x', hk', hR⟩ := hI.ep e' he'
      rw [hk] at hk'; cases hk'
      have key : ∀ (xs : List U64) (k : Nat), k ≠ 0 → x.epQueue = xs.map UScalar.bv →
          P1.QueueRel (L.mem s) Z.T .Ep (qOf (L.mem s) e') xs → (∀ y ∈ xs, QueuedOn (L.mem s) e' k y) → False := by
        intro xs k hk0 hq hQ hy
        rw [hq] at hu
        obtain ⟨y, hyx, rfl⟩ := List.mem_map.1 hu
        have hyT := hQ.mem y hyx
        have hH := J.zH.1 y hyT
        have d1 := ((hRD y (rgOf_regionD hsb hfit hH hr)).1 hH).1
        have h3 := (hy y hyx).1
        rw [← stA_tStA, d1] at h3; unfold sched.TS_INACTIVE at h3
        exact hk0 (by rw [← h3]; rfl)
      cases x with
      | idleEP => cases hu
      | sendEP q => obtain ⟨-, xs, -, hq, hQ, hy⟩ := hR; exact key xs 4 (by decide) hq hQ hy
      | recvEP q => obtain ⟨-, xs, -, hq, hQ, hy⟩ := hR; exact key xs 3 (by decide) hq hQ hy
  · intro n x hk u hu
    refine ⟨(fun hr => by rw [(tN hk hr).1] at hu; cases hu), fun hr => ?_⟩
    · -- a notification's queued thread
      obtain ⟨-, hm⟩ := hV.ntfnQ n x hk
      obtain ⟨xu, hxu, hst⟩ := hm u hu
      exact live hxu (by rw [hst]; simp [tsCode]) hr
  · intro n x t hk ht
    refine ⟨(fun hr => by rw [(tN hk hr).2.1] at ht; cases ht), fun hr => ?_⟩
    · -- a notification's bound thread (KeptRefsP3)
      obtain ⟨n', hn', rfl⟩ := J.obj.ntfn n x hk
      obtain ⟨x', hk', hR⟩ := hI.ntfn n' hn'
      rw [hk] at hk'; cases hk'
      have hb := hR.bound
      rw [ht, show nBoundA n' = P1.ntfnBtA n' from rfl] at hb
      have h0 : L.mem s (P1.ntfnBtA n') ≠ 0#u64 := fun e => by rw [e, optRef_zero] at hb; cases hb
      have et : t = (L.mem s (P1.ntfnBtA n')).bv := by
        rw [Notif.optRef_ne h0] at hb; exact (Option.some.inj hb)
      have hH := J.zH.2.2.2 n' hn'
      have hnD : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) n' := fun hd => h0 ((hRD n' hd).2.2.1 hH).2.1
      have hTm : L.mem s (P1.ntfnBtA n') ∈ Z.T := hR.bound_mem h0
      have hHt := J.zH.1 _ hTm
      exact k6 n' hH hnD (by rw [hHt]; simp) (rgOf_regionD hsb hfit hHt (by rw [← et]; exact hr))
  · intro n x c hk hc
    refine ⟨(fun hr => by rw [(tN hk hr).2.2] at hc; cases hc), fun hr => ?_⟩
    · -- a notification's SC
      obtain ⟨n', hn', rfl⟩ := J.obj.ntfn n x hk
      obtain ⟨y, m, hy, hyn⟩ := J.ntfn_link hn' x c hk hc
      rw [(tC hy hr).2.1] at hyn; cases hyn
  · intro r x t hk ht
    refine ⟨(fun hr => by rw [tR hk hr] at ht; cases ht), fun hr => ?_⟩
    · -- a reply's thread
      obtain ⟨x', hx', hst⟩ := hV.replyTcb r x t hk ht
      refine live hx' ?_ hr
      rcases hst with e | ⟨ep, d, e⟩ <;> rw [e] <;> simp [tsCode]
  · intro c y k t hk ht
    refine ⟨(fun hr => by rw [(tC hk hr).1] at ht; cases ht), fun hr => ?_⟩
    · -- an SC's thread (P1's `TSc`)
      obtain ⟨c', hc', rfl⟩ := J.obj.sc c y k hk
      obtain ⟨y', n', hk', hR⟩ := hs.scs c' hc'
      rw [hk] at hk'; cases hk'
      have h1 := hR.tcb
      rw [ht, scW_tcb] at h1
      have h0 : L.mem s (P1.scTcbA c') ≠ 0#u64 := fun e => by rw [e, optRef_zero] at h1; cases h1
      have et : t = (L.mem s (P1.scTcbA c')).bv := by
        rw [Notif.optRef_ne h0] at h1; exact (Option.some.inj h1)
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hHc := (hJ.sc c' y k (J.c0 c' hc') hk).2
      have hScs : c' ∈ P1.Heap.scs H := ⟨_, hHc⟩
      have hTt : L.mem s (P1.scTcbA c') ∈ P1.Heap.tcbs H := hX.yt.1 c' hScs h0
      have hback := hX.tsc c' hScs (J.c0 c' hc') h0
      have hTZ : L.mem s (P1.scTcbA c') ∈ Z.T := by rw [J.tcbs_eq.1]; exact hTt
      obtain ⟨xt, hkt, hRt⟩ := hI.tcb _ hTZ
      rw [← et] at hkt
      have hsc := hRt.sc
      rw [hback, Notif.optRef_ne (J.c0 c' hc'), (tT hkt hr).2.1] at hsc
      cases hsc
  · intro c y k n hk hn
    refine ⟨(fun hr => by rw [(tC hk hr).2.1] at hn; cases hn), fun hr => ?_⟩
    · -- an SC's notification (KeptRefsP3)
      obtain ⟨c', hc', rfl⟩ := J.obj.sc c y k hk
      obtain ⟨y', n', hk', hR⟩ := hs.scs c' hc'
      rw [hk] at hk'; cases hk'
      have h1 := hR.ntfn
      rw [hn, scW_ntfn] at h1
      have h0 : L.mem s (P1.scNtfnA c') ≠ 0#u64 := fun e => by rw [e, optRef_zero] at h1; cases h1
      have en : n = (L.mem s (P1.scNtfnA c')).bv := by
        rw [Notif.optRef_ne h0] at h1; exact (Option.some.inj h1)
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hHc := (hJ.sc c' y k (J.c0 c' hc') hk).2
      have hScs : c' ∈ P1.Heap.scs H := ⟨_, hHc⟩
      have hnD : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) c' := fun hd =>
        h0 ((hRD c' hd).2.2.2.2 _ hHc).2.2.1
      have hNt : L.mem s (P1.scNtfnA c') ∈ P1.Heap.ntfns H := hX.scn c' hScs h0
      exact k5 c' hScs hnD (by rw [show H _ = some .ntfn from hNt]; simp)
        (rgOf_regionD hsb hfit hNt (by rw [← en]; exact hr))
  · intro c y k t hk ht
    refine ⟨(fun hr => by rw [(tC hk hr).2.2.1] at ht; cases ht), fun hr => ?_⟩
    · -- an SC's yielder
      obtain ⟨x, hx, hyt⟩ := hV.scYieldFrom c y k t hk ht
      rw [(tT hx hr).2.2.2] at hyt; cases hyt
  · intro c y k r hk hrm
    refine ⟨(fun hr => by rw [(tC hk hr).2.2.2] at hrm; cases hrm), fun hr => ?_⟩
    · -- an SC's reply (`RFree`)
      obtain ⟨c', hc', rfl⟩ := J.obj.sc c y k hk
      obtain ⟨⟨y1, n1, hk1, hyL⟩, hLR, -⟩ := J.call.stack c' hc'
      rw [hk] at hk1; cases hk1
      rw [hyL] at hrm
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hrm
      have hrR := hLR r' hr'
      obtain ⟨xr, hxr, -⟩ := hI.reply r' hrR
      have hfree : Free σ r' := ⟨xr, hxr, tR hxr hr⟩
      exact (J.rfree r' hrR hfree).1 c' hc' hr'
  · intro d p' u hu hr
    obtain ⟨x, scp, y, n, h1, h2, -⟩ := hIv.rq d p' u hu
    exact liveSc h1 h2 hr
  · intro u hu hr
    obtain ⟨x, scp, y, n, h1, h2, -⟩ := hIv.rel u hu
    exact liveSc h1 h2 hr
  · intro t ht hr
    obtain ⟨x, scp, -, -, h1, h2, -⟩ := schedulable_inv (J.act.1 t ht)
    exact liveSc h1 h2 hr
  · refine ⟨fun hr => ?_, fun hr => ?_⟩
    · -- the idle thread
      obtain ⟨x, hx, h1, -⟩ := J.act.2
      exact liveSc hx h1 hr
    · -- the idle SC
      obtain ⟨x, hx, h1, -⟩ := J.act.2
      obtain ⟨y, n, hy, hyt⟩ := hIv.back _ x _ hx h1
      rw [(tC hy hr).1] at hyt; cases hyt
  · refine ⟨fun hr => ?_, fun hr => ?_⟩
    · -- the current thread
      obtain ⟨xt, hkt, hsc, -⟩ := (J.curInv hres).tcb
      exact liveSc hkt hsc hr
    · -- the current SC
      obtain ⟨xt, hkt, hsc, -⟩ := (J.curInv hres).tcb
      obtain ⟨y, n, hy, hyt⟩ := hIv.back _ xt _ hkt hsc
      rw [(tC hy hr).1] at hyt; cases hyt

/-- **Stage A's premises at `J`** (`XKeep`, from `SKeep` and the relations). -/
theorem JAtZ.xKeep (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hK : SKeep (RgOf p sb) σ) :
    XKeep st (KOff (RgOf p sb)) Z s σ := by
  have hI := J.xtop.ipc
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hcr, hs⟩ := hS.lists
  refine ⟨fun t ht h0 hr => ?_, fun t ht _ x hk e r d hst => ?_, fun n hn _ h0 => ?_, ⟨fun t ht hq => ?_,
    fun t ht e => ?_, ?_, ?_, fun t ht _ h0 => ?_⟩⟩
  · obtain ⟨x, hk, hR⟩ := hI.tcb t ht
    have h1 := (J.rgTcb hsb hfit hRD hk hr).1
    have h2 := hR.st
    rw [h1] at h2
    exact h0 (UScalar.eq_of_val_eq (by rw [h2]; rfl))
  · obtain ⟨x', hk', hR⟩ := hI.tcb t ht
    rw [hk] at hk'; cases hk'
    have h1 := (hR.recv e (some r) d hst).1
    have h0 : L.mem s (tReplyA t) ≠ 0#u64 := fun e0 => by rw [e0, optRef_zero] at h1; cases h1
    rw [Notif.optRef_ne h0] at h1
    show ¬ RgOf p sb (L.mem s (tReplyA t)).bv
    rw [Option.some.inj h1]
    exact (hK.recv t.bv x e (some r) d hk hst).2.2 r rfl
  · obtain ⟨x, hk, hR⟩ := hI.ntfn n hn
    have hb := hR.bound
    rw [Notif.optRef_ne h0] at hb
    exact (hK.ntfnB n.bv x _ hk hb).2
  · rcases hq with ⟨d, p', hm⟩ | hm
    · exact hK.rq d p' _ hm
    · exact hK.rel _ hm
  · intro hr
    have hH := J.zH.1 t ht
    have d := ((hRD t (rgOf_regionD hsb hfit hH hr)).1 hH).2.2.2.1
    apply d
    rw [← e]
    unfold P1.LawfulStore.actionW Sched.nodeW; rw [hcr.cur]
  · show ¬ RgOf p sb (Sched.nodeW st s Z.c layout.node.CUR_THREAD).bv
    rw [← hs.curThread]; exact hK.cur.1
  · show ¬ RgOf p sb (Sched.nodeW st s Z.c layout.node.IDLE_THREAD).bv
    rw [← hs.idleTh]; exact hK.idle.1
  · obtain ⟨x, hk, hR⟩ := hI.tcb t ht
    have hsc := hR.sc
    rw [Notif.optRef_ne h0] at hsc
    exact (hK.tcbSc t.bv x _ hk hsc).2

end Rg

/-- **`XTopAt` across the drop at `J`** (`XTopAt.drop` with its closure
premises `XKeep`/`SKeep` and its CSpace inputs discharged from `JAtZ` at a
childless RAM untyped cap in a slot of the typed heap; module docstring).
Premises left: the spec's detype (`SDrop` and the spec fields it keeps, the
spec step's facts), `KeptRefsP3` at the region (`RegionUnrefJ` [J], as
`utEpJ`), and `VsReachMiss` [J] (VsDrop). -/
theorem JAtZ.dropX (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread) {sl : Fl4Spec.CslotPtr} (hsl : AbsSlot Z.th sl)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi false))
    (hnc : ¬ ∃ y, σ.cdt y = some sl)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ')
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hrepr : σ'.reprogramTimer = σ.reprogramTimer) (hcdom : σ'.curDomain = σ.curDomain)
    (hdtime : σ'.domainTime = σ.domainTime) (hist : σ'.interruptStates = σ.interruptStates)
    (hinode : σ'.interruptIrqNode = σ.interruptIrqNode) (harch : σ'.archState = σ.archState)
    (hdl : σ'.domainList = σ.domainList) (hdsi : σ'.domainStartIndex = σ.domainStartIndex)
    (hum : ∀ x, ¬ RgOf p sb x → σ'.machineState.underlyingMemory x = σ.machineState.underlyingMemory x)
    {XP X4 X3 X2 X1 : Set U64} (hXP : XP ⊆ Z.P) (hX4 : X4 ⊆ Z.L4) (hX3 : X3 ⊆ Z.L3) (hX2 : X2 ⊆ Z.L2)
    (hX1 : X1 ⊆ Z.L1) (hM : Vs.VsReachMiss p.val (p.val + 2 ^ sb.val) (L.mem s) (L.ksb s) XP X4 X3 X2 X1) :
    XTopAt (L := L) AR ((Z.keep (KOff (RgOf p sb)) (KBOf p sb)).dropV p.val (p.val + 2 ^ sb.val) (L.mem s))
      s a σ' := by
  have U := J.utc sl p sb fi false hsl hcap rfl
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  obtain ⟨hPl, ⟨-, -, hML, hC, -⟩, -⟩ := J.xtop.rel
  have hx : cslotAddr sl ∈ Z.G.chains.flatten := (hML.members _).2 ⟨hsl.isSlot, _, hcap, by simp⟩
  have hcx : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi false := capV_of_capAt hcap
  have hnd : ∀ y, ¬ Mdb.Desc Z.G.par y (cslotAddr sl) := fun y =>
    Mdb.not_desc_of_no_child fun z hz => hnc ((hC.has_child_iff hPl hsl).2 ⟨z, hz⟩)
  have hRD := J.rgDeadD hx hcx hnd
  have hK := J.sKeep hsb U.pfit hRD hres hKR
  exact XTopAt.drop J.xtop (J.xKeep hsb U.pfit hRD hK) hsb U.pfit hD hK hcdt horig hrepr hcdom hdtime hist
    hinode harch hdl hdsi hum J.ut hx hcx hnd U.nostr (U.ns hnc) hXP hX4 hX3 hX2 hX1 hM

/-- **The scheduler's spec invariants across the drop at `J`** (item 2, the
spec-only `JAtZ` fields at the kept sets): `nsc`, `inv`, `cur`, `own`, `off`,
`act`, `c0`, `bsa`, `sv`, `isorted`, `slink`, `curRun` (UtDropSpec's `.drop`
lemmas with `SKeep`). -/
theorem JAtZ.dropSpecInv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p sb : U64}
    (hK : SKeep (RgOf p sb) σ) {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ') :
    Sched.NSC (KeepS (KOff (RgOf p sb)) Z.N) (KeepS (KOff (RgOf p sb)) Z.C) σ' ∧ Sched.Inv σ' ∧
      (σ'.schedulerAction = .chooseNewThread ∨ Sched.CurInv σ') ∧
      Sched.CurOwnW (KeepS (KOff (RgOf p sb)) Z.T) (KeepS (KOff (RgOf p sb)) Z.C) σ' ∧ Sched.OffOK σ' ∧
      Sched.ActIdle σ' ∧ (∀ q ∈ KeepS (KOff (RgOf p sb)) Z.C, q ≠ 0#u64) ∧ Sched.BlockedScActive σ' ∧
      Sched.SchedValid σ' ∧ Sched.IpcSorted σ' ∧ Sched.ScLinkHyp σ' ∧ CurRunM σ' :=
  ⟨J.nsc.drop hK hD, J.inv.drop hK hD, CurInvW.drop J.cur hK hD, J.own.drop hK hD, J.off.drop hD,
    J.act.drop hK hD, fun q hq => J.c0 q hq.1, J.bsa.drop hD, J.sv.drop hK hD, J.isorted.drop hK hD,
    J.slink.drop hK hD, J.curRun.drop hD⟩

section Mixed
variable {p sb : U64} (hsb : sb.val < 64) (hfit : p.val + 2 ^ sb.val ≤ 2 ^ 64)
  (hRD : ∀ q, P1.RegionD H p.val (p.val + 2 ^ sb.val) q → DeadP (L := L) H s q)
include hsb hfit hRD

/-- A reply of `Z.R` is not null. -/
theorem JAtZ.r_ne0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {r : U64} (hr : r ∈ Z.R) : r ≠ 0#u64 :=
  fun e => by have := J.zH.2.2.1 r hr; rw [e, J.kern.h0] at this; cases this

/-- A reply linked from a reply of `Z.R` (its back link naming that reply)
is off the region: a reply in the region is free (`rgReply`), so unlinked
(`RFree`). -/
theorem JAtZ.link_off (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {d n : U64} (hd : d ∈ Z.R)
    (hn : n ∈ Z.R) (hb : L.mem s (P1.rPrevA n) = d ∨ L.mem s (P1.rNextA n) = d) : ¬ RgOf p sb n.bv := by
  intro hr
  obtain ⟨xr, hxr, -⟩ := J.xtop.ipc.reply n hn
  have hfree : Free σ n := ⟨xr, hxr, J.rgReply hsb hfit hRD hxr hr⟩
  obtain ⟨-, h1, h2⟩ := J.rfree n hn hfree
  rcases hb with e | e
  · rw [h2] at e; exact J.r_ne0 hsb hfit hRD hd e.symm
  · rw [h1] at e; exact J.r_ne0 hsb hfit hRD hd e.symm

/-- **The mixed relations across the drop at `J`** (item 2: `call`, `rfree`,
`rrecv`, `yld`, `mcp`, `buf` at the kept sets, the same FL4 memory and the
detyped spec state). -/
theorem JAtZ.dropMixed (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hK : SKeep (RgOf p sb) σ)
    {σ' : Fl4Spec.State Unit} (hD : SDrop (RgOf p sb) σ σ') :
    Sched.CallRel (L.mem s) (KeepS (KOff (RgOf p sb)) Z.R) (KeepS (KOff (RgOf p sb)) Z.C) σ' Lst ∧
      Sched.RFree (L.mem s) (KeepS (KOff (RgOf p sb)) Z.R) (KeepS (KOff (RgOf p sb)) Z.C) σ' Lst ∧
      Sched.RRecv (L.mem s) (KeepS (KOff (RgOf p sb)) Z.R) σ' ∧
      Sched.YieldRel (KeepS (KOff (RgOf p sb)) Z.T) (KeepS (KOff (RgOf p sb)) Z.C) (L.mem s) σ' ∧
      Sched.McpRel (KeepS (KOff (RgOf p sb)) Z.T) (L.mem s) σ' ∧
      BufWordRel (KeepS (KOff (RgOf p sb)) Z.T) (L.mem s) σ' := by
  have C := J.call
  -- a reply on a kept stack's SC: both kept
  have onStack : ∀ sc ∈ Z.C, ∀ r ∈ Lst sc, ¬ RgOf p sb sc.bv ∧ ¬ RgOf p sb r.bv := by
    intro sc hsc r hr
    obtain ⟨⟨y, n, hk, hyL⟩, -⟩ := C.stack sc hsc
    exact hK.scR sc.bv y n r.bv hk (by rw [hyL]; exact List.mem_map_of_mem hr)
  have detC : ∀ d, Detached (KeepS (KOff (RgOf p sb)) Z.C) Lst d → Detached Z.C Lst d :=
    fun d h sc hsc hm => h sc ⟨hsc, (onStack sc hsc d hm).1⟩ hm
  have detC' : ∀ d, Detached Z.C Lst d → Detached (KeepS (KOff (RgOf p sb)) Z.C) Lst d :=
    fun d h sc hsc => h sc hsc.1
  refine ⟨⟨fun sc hsc => ?_, fun sc hsc sc' hsc' r h1 h2 => C.excl sc hsc.1 sc' hsc'.1 r h1 h2,
    fun r hr => ?_, fun d hd hdet => ?_⟩, fun d hd hfr => ?_, fun d hd hrb => ?_, ⟨fun t ht => ?_,
    fun t ht h0 => ?_, fun sc hsc y n hy q hq => ?_⟩, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨⟨y, n, hk, hyL⟩, hLR, hnd, hSW⟩ := C.stack sc hsc.1
    exact ⟨⟨y, n, hD.fwd hsc.2 hk, hyL⟩, fun r hr => ⟨hLR r hr, (onStack sc hsc.1 r hr).2⟩, hnd, hSW⟩
  · obtain ⟨x, hk, hiff⟩ := C.reply r hr.1
    refine ⟨x, hD.fwd hr.2 hk, fun q => ⟨fun h => ?_, fun ⟨sc, hsc, e, hh⟩ => (hiff q).2 ⟨sc, hsc.1, e, hh⟩⟩⟩
    obtain ⟨sc, hsc, e, hh⟩ := (hiff q).1 h
    exact ⟨sc, ⟨hsc, (onStack sc hsc r (List.mem_of_mem_head? hh)).1⟩, e, hh⟩
  · obtain ⟨h1, h2, h3⟩ := C.det d hd.1 (detC d hdet)
    refine ⟨h1, fun h0 => ?_, fun h0 => ?_⟩
    · obtain ⟨a1, a2, a3⟩ := h2 h0
      exact ⟨⟨a1, J.link_off hsb hfit hRD hd.1 a1 (Or.inl a3)⟩, detC' _ a2, a3⟩
    · obtain ⟨a1, a2, a3⟩ := h3 h0
      exact ⟨⟨a1, J.link_off hsb hfit hRD hd.1 a1 (Or.inr a3)⟩, detC' _ a2, a3⟩
  · obtain ⟨x, hx, hn⟩ := hfr
    obtain ⟨h1, h2, h3⟩ := J.rfree d hd.1 ⟨x, (hD.back hx).2, hn⟩
    exact ⟨detC' d h1, h2, h3⟩
  · obtain ⟨x, t, xt, h1, h2, h3, h4⟩ := hrb
    exact J.rrecv d hd.1 ⟨x, t, xt, (hD.back h1).2, h2, (hD.back h3).2, h4⟩
  · obtain ⟨x, hk, e⟩ := J.yld.tcb t ht.1
    exact ⟨x, hD.fwd ht.2 hk, e⟩
  · obtain ⟨h1, y, n, hy, e⟩ := J.yld.toSc t ht.1 h0
    obtain ⟨x, hk, ex⟩ := J.yld.tcb t ht.1
    have k2 := (hK.tcbYield t.bv x _ hk (by rw [ex, Notif.optRef_ne h0])).2
    exact ⟨⟨h1, k2⟩, y, n, hD.fwd k2 hy, e⟩
  · obtain ⟨t, ht, e1, e2⟩ := J.yld.frm sc hsc.1 y n (hD.back hy).2 q hq
    have k := (hK.scY sc.bv y n q (hD.back hy).2 hq).2
    exact ⟨t, ⟨ht, by show ¬ RgOf p sb t.bv; rw [e1]; exact k⟩, e1, e2⟩
  · obtain ⟨x, hk, e⟩ := J.mcp t ht.1
    exact ⟨x, hD.fwd ht.2 hk, e⟩
  · obtain ⟨x, hk, e⟩ := J.buf t ht.1
    exact ⟨x, hD.fwd ht.2 hk, e⟩

end Mixed

/-- **P1's `BlkOK` across the drop at `J`** (item 2, `blk`: P1's
`BlkOK.drop` with `dropOK_of`): `H` loses the objects meeting the region,
all dead (`rgDeadD`); the current thread and SC are live (no reschedule
pending: `CurInv`, their SC/TCB links are not null); the region is off the
kernel-state block (`UtKsApart`). The kept links are `RegionUnrefJ` [J]'s two
parts at this region. -/
theorem JAtZ.dropBlk (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hres : σ.schedulerAction ≠ .chooseNewThread) {p sb : U64}
    (hRD : ∀ q, P1.RegionD H p.val (p.val + 2 ^ sb.val) q → DeadP (L := L) H s q)
    (hreg : p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val)
    (hKR : KeptRefsP3 (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) s)
    (hDT : DbgTimerKept (L := L) H (P1.RegionD H p.val (p.val + 2 ^ sb.val)) Cs s) :
    let H' := H.drop (P1.RegionD H p.val (p.val + 2 ^ sb.val))
    P1.BlkOK st (P1.Heap.tcbs H') Cs (P1.Heap.omega H') H' (P1.Heap.frame H') (P1.Heap.replies H')
      (P1.Heap.scs H') (P1.Heap.ntfns H') (P1.Heap.scBits H') Ac s := by
  intro H'
  have hC := J.curInv hres
  obtain ⟨xt, hkt, hsc, -⟩ := hC.tcb
  obtain ⟨Q, R0, hcr, hs⟩ := J.xtop.fin.1.1.1.lists
  -- the current thread is live
  have hcur : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) (L.curW s) := by
    intro hd
    have d2 := ((hRD _ hd).1 J.kern.curH).2.1
    have hT := J.thT _ J.kern.curT
    obtain ⟨x', hk', hR⟩ := J.xtop.ipc.tcb _ hT
    rw [← J.kern.cur, hkt] at hk'; cases hk'
    rw [hR.sc, d2, optRef_zero] at hsc; cases hsc
  -- the current SC is live
  have hcsc : ¬ P1.RegionD H p.val (p.val + 2 ^ sb.val) (L.cscW s) := by
    intro hd
    obtain ⟨y, n, hy, hyt⟩ := J.inv.back _ xt _ hkt hsc
    have ecs : L.cscW s = Sched.nodeW st s Z.c layout.node.CUR_SC := by
      unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA Sched.nodeW; rw [hcr.cur]
    obtain ⟨q, hq, hqp⟩ := J.obj.sc _ y n hy
    have eq : q = L.cscW s := P1.eq_of_bv (by rw [hqp, hs.curSc, ecs])
    subst eq
    obtain ⟨y', n', hk', hx'⟩ := hs.scs _ hq
    have hk2 : σ.kheap σ.curSc = some (.schedContext y' n') := by rw [← hqp]; exact hk'
    rw [hy] at hk2; cases hk2
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hH := (hJ.sc _ y n (J.c0 _ hq) hk').2
    have d := ((hRD _ hd).2.2.2.2 _ hH).1
    rw [hx'.tcb, scW_tcb, d, optRef_zero] at hyt; cases hyt
  refine P1.BlkOK.drop (dropOK_of J.kern.heap J.kern.h0 (fun q k _ hq => hRD q hq) hcur hcsc J.kern.hks
    J.kern.hksIn hreg J.kern.hnd hKR hDT J.kern.ksbFit) J.blk

end

end

end Fl4Proofs.P3
