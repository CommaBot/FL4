/-
P3 (p3J gen 38): **the SchedContext cap's decode at stable ghosts, and its `ProjW` footprint for every label**.

* **`uFoot_projW`**: ScDecodeAll's `UFoot` (every word a SchedContext invocation may write: `TFoot` = `KFoot`
  — TCB words at the scheduler offsets, the current core's node, notification words, SC words — or `YIELD_TO`
  words; the reply words `RW`; the register words `RegW`) at `Z`'s sets is inside `Mc.ProjW H Cs s` at a `JAtZ`
  state (TCBs / replies / notifications by `JAtZ.zH`, SCs by `JPlaced.sc`, the node at `Z.c = cpu s`). So the
  SchedContext code never writes another core's `IDLE_THREAD` / `IDLE_SC` word.
* **`scDecFootJ`**: FL4's `decode_invocation` of a SchedContext cap, **any label**, writes only `ProjW`: the
  fast-path flag's error and the decode's errors leave the state (CPost), every other outcome ends in ScAll, whose
  last conjunct is the `UFoot` footprint (ScDecodeAll's `sc_decode_refines`, entered as ScJointStep's
  `sched_contextJ_step` enters it; its hypotheses the same).
* `XCap.andW`: a post on FL4's decode run conjoined into `XCap`'s `X` (every `X` there is at the run's state).
* `ScReplyJSt`, **`sc_consumedReplyJSt`**: ScJointStep's `ScReplyJ` / ScJointConsumed's `sc_consumedReplyJ` with
  `JStab Z H Cs` for `JAt` (the same proof: the reply ends at `Z.mv Z.G V`).
* **`decScJ3St`**: ScJointStep's `decode_invocation_sched_contextJ` (Consumed, Bind, UnbindObject) with
  `JStab Z H Cs` for `JAt` (the same proof: `sched_contextJ_step`'s outcomes are at `Z`).

No premise beyond the copied lemmas' own (theirs verbatim); no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JIrqB
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 38) **A SchedContext invocation's word is a `ProjW` word** at a `JAtZ` state (module docstring). -/
theorem uFoot_projW {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : Sched.UFoot st Z.T Z.N Z.C Z.R Z.c s σ b) : Mc.ProjW (L := L) H Cs s b := by
  obtain ⟨Q, R0, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have hcpu : L.cpu s = Z.c := hc.cur
  have hH := J.kern.heap
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hscH : ∀ q ∈ Z.C, ∀ y n, σ.kheap q.bv = some (.schedContext y n) →
      H q = some (.sc (n + Fl4Spec.minSchedContextBits)) :=
    fun q hq y n hk => (hJ.sc q y n (J.c0 q hq) hk).2
  rcases hb with (((⟨y, hy, K, hK, rfl⟩ | ⟨h1, h2⟩) | ⟨n, hn, h1, h2⟩ | ⟨q, hq, y, n, hk, ⟨h1, h2⟩, -⟩) |
      ⟨y, hy, rfl⟩) | (⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, K, k1, k2, rfl⟩
  · exact Mc.obj_projW hH (k := .tcb) (J.zH.1 y hy) (by simp only [P1.HKind.bits]; have := hK.2.1; omega)
  · exact Or.inr (Or.inr ⟨Z.c, hcpu ▸ J.kern.cpuCs, h1, h2, fun h => absurd hcpu.symm h⟩)
  · exact Or.inl ⟨n, .ntfn, J.zH.2.2.2 n hn, h1, by simp only [P1.HKind.bits]; omega⟩
  · exact Or.inl ⟨q, .sc _, hscH q hq y n hk, h1, by simpa only [P1.HKind.bits] using h2⟩
  · exact Mc.obj_projW hH (k := .tcb) (J.zH.1 y hy) (K := 3472#u64) (by simp [P1.HKind.bits])
  · rw [rNextA_eqW]
    exact Mc.obj_projW hH (k := .reply) (J.zH.2.2.1 r hr) (by simp [P1.HKind.bits])
  · obtain ⟨y, n, hk, -⟩ := hs.scs q hq
    rw [scReplyA_eq]
    have h32 : (32#u64 : U64).val < 2 ^ (P1.HKind.sc (n + Fl4Spec.minSchedContextBits)).bits := by
      simp only [P1.HKind.bits, Fl4Spec.minSchedContextBits]
      have : 2 ^ 7 ≤ 2 ^ (n + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have e : (32#u64 : U64).val = 32 := rfl
      omega
    exact Mc.obj_projW hH (hscH q hq y n hk) h32
  · exact Mc.obj_projW hH (k := .tcb) (J.zH.1 y hy) (by simp only [P1.HKind.bits]; omega)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 38) **FL4's SchedContext decode writes only `ProjW`, every label** (module docstring; hypotheses
ScJointStep's `sched_contextJ_step`'s, the ones `sc_decode_refines` reads). -/
theorem scDecFootJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (length slot buf : U64) (blk call don fp : Bool) :
    syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ Z.T := by
    intro hx p hc
    rcases hex with ⟨h0, -⟩ | ⟨-, -, c, a', rest, hc', -, hv, -⟩
    · exact absurd h0 hx
    · rw [hc] at hc'; cases eq_of_ok_eq hc'
      exact J.thT p hv
  have hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ Z.N ∧ p ≠ 0#u64 := by
    intro hx p b w r hc
    rcases hex with ⟨h0, -⟩ | ⟨-, hS, -⟩
    · exact absurd h0 hx
    · obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hH : H p = some .ntfn := ((hJ.typed x0 hS).2.1 p b w r (capV_of_capAt hc)).2
      refine ⟨J.hset.2.1 p hH, fun e => ?_⟩
      rw [e, J.kern.h0] at hH; cases hH
  have hX := J.xtop
  have hS := hX.fin.1.1.1
  have hR := hX.fin.1.1.2.2.1
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (sc_decode_refines htm Z.th s a σ hS hR J.nsc J.inv J.yld J.act J.mcp J.c0 J.call J.rp
      J.rfree lbl slbl hlbl hsc hpi hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu
      Ipc.msgOK_holds) ?_
    rintro ⟨r0, s', a'⟩ hq
    rcases hq with ⟨e, e', he, -, -⟩ | ⟨inv, -, -, σ0, data, σ1, σ2, -, -, -, hall, -⟩
    · cases he; exact P1.WritesIn.refl _ _
    · exact hall.2.2.2.2.2.mono fun b hb => uFoot_projW J hb
  · simp only [↓reduceIte, WP.spec_ok]
    exact P1.WritesIn.refl _ _

/-- (p3J gen 38) **A post on FL4's decode run, conjoined into `XCap`'s `X`** (module docstring). -/
theorem XCap.andW {X : S → A → Fl4Spec.State Unit → Prop} {Q : S → Prop} {s : S} {ar : A}
    {σ : Fl4Spec.State Unit} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool} {buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {slbl : Fl4Spec.Data} {args : List Fl4Spec.Data}
    {ci : Fl4Spec.CapRef} {sl : Fl4Spec.CslotPtr} {excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)}
    {buffer : Option Fl4Spec.ObjRef} {ct : U64}
    (h : XCap (L := L) arI X s ar σ lbl length slot c blk call don fp buf extra slbl args ci sl excaps buffer ct)
    (hW : syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r => Q r.2.1 ⦄) :
    XCap (L := L) arI (fun s1 a1 σ1 => X s1 a1 σ1 ∧ Q s1) s ar σ lbl length slot c blk call don fp buf extra slbl
      args ci sl excaps buffer ct := by
  rcases h with h | h
  · refine Or.inl (WP.spec_mono (WP.spec_and h hW) fun res ⟨hr, hq⟩ => ?_)
    exact match hr with
    | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, h4, hq⟩
    | Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4⟩ => Or.inr ⟨inv, h1, σ1, h2, y, hy, h3, h4, hq⟩
  · refine Or.inr (WP.spec_mono (WP.spec_and h hW) fun res ⟨hr, hq⟩ => ?_)
    exact match hr with
    | Or.inl ⟨e, h1, h2, h3, h4⟩ => Or.inl ⟨e, h1, h2, h3, h4, hq⟩
    | Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7⟩ =>
      Or.inr ⟨h1, h2, inv, h3, σ1, h4, rr, σy, h5, z, hz, h6, h7, hq⟩

/-- (p3J gen 38) ScJointStep's `ScReplyJ` with `JStab Z H Cs` for `JAt` (module docstring). -/
def ScReplyJSt (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (lbl length slot : U64)
    (sc sb : U64) (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (slbl : Fl4Spec.Data) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (ct : U64) : Prop :=
  syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
    ⦃ r => r.1 = .Ok () → L.mem r.2.1 (stA ct) ≠ sched.TS_RESTART → ∀ inv σ0 data σ1 σ2,
      (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
        ({(.ok inv, σ)}, False) →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) →
      Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({(data, σ1)}, False) →
      ((), σ2) ∈ (Fl4Proofs.P3.specTail call ct.bv data σ1).1 →
      JStab (L := L) arI AR Z H Cs r.2.1 r.2.2 σ2 ⦄

set_option maxHeartbeats 16000000 in
/-- (p3J gen 38) **Consumed's reply at `J`, at stable ghosts** (ScJointConsumed's `sc_consumedReplyJ`, the
same proof; module docstring). -/
theorem sc_consumedReplyJSt (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hni : Entered σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    (l44 : lbl = fl4_abi.label.SchedContextConsumed)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    {ct : U64} (hct : sched.cur_thread st s = ok ct)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (length slot buf : U64) (blk call don fp : Bool) :
    ScReplyJSt (L := L) (arI := arI) AR Z H Cs s a σ lbl length slot sc sb blk call don fp buf extra slbl excaps ct := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s Z.c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ Z.T := hct' ▸ hc.curT
  have hg : Fl4Spec.genInvocationType slbl = .schedContextConsumed := by
    rw [hlbl, l44]; unfold scLabelOf; simp
  have hinv : ∀ inv, (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ =
      ({(.ok inv, σ)}, False) → inv = .invokeSchedContextConsumed sc.bv := by
    intro inv hrun
    simp only [Fl4Spec.decodeSchedContextInvocation, hg] at hrun
    exact (retP_pure (P := fun v => v = Fl4Spec.SchedContextInvocation.invokeSchedContextConsumed sc.bv) rfl :
      RetP _ (Fl4Spec.NonDetE.returnOk (Fl4Spec.SchedContextInvocation.invokeSchedContextConsumed sc.bv))).of_run hrun
  -- the caller's restart
  obtain ⟨s1, σ1, x, -, he0, -, hcur, eσ1, -, -, -, hs1, Ac1, Lst1, D1, J1⟩ := J.restartJ hni hct
  rw [hcur] at he0
  have hk1 : σ1.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    rw [eσ1, stsAct_kheap]; simp [updK]
  -- the spec's update of the SC's consumed time
  obtain ⟨Q1, R1, hc1, hs1'⟩ := J1.xtop.fin.1.1.1.lists
  obtain ⟨z, n, hkz, -⟩ := hs1'.scs sc hsc
  obtain ⟨c, v, hv⟩ := updConsumed_one hkz
  set σu := updSc σ1 sc.bv (Fl4Spec.scConsumedUpdate (fun _ => v) z) n with hσu
  have hsct : ct.bv ≠ sc.bv := fun e => by rw [e, hkz] at hk1; cases hk1
  have hku : σu.kheap ct.bv = some (.tcb { x with tcbState := .restart }) := by
    simp only [hσu, updSc, updK, Function.update_of_ne hsct]; exact hk1
  have hrc : Fl4Spec.returnConsumed (Z := Unit) sc.bv σ1 = ({(Fl4Spec.wordsFromTime c, σu)}, False) := by
    unfold Fl4Spec.returnConsumed; rw [nd_bind_one hv]; rfl
  have hsetc : Fl4Spec.setConsumed (Z := Unit) sc.bv ct.bv σ1 =
      Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, Fl4Spec.wordsFromTime c) σu := by
    unfold Fl4Spec.setConsumed; rw [nd_bind_one hv]
  -- FL4's `set_consumed`, with the spec's reply when a call
  have hSC : schedcontext.set_consumed st arI s1 a sc ct call ⦃ s3 => ∃ σ2,
      Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) ct.bv (0, Fl4Spec.wordsFromTime c)) σu =
        ({((), σ2)}, False) ∧ ∃ y, σ2.kheap ct.bv = some (.tcb y) ∧ y.tcbState = .restart ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' s3 a σ2 ⦄ := by
    cases call
    · unfold schedcontext.set_consumed
      refine WP.spec_bind (J1.updConsumedJ hAT hmax htu hsc hctT) ?_
      rintro ⟨cv, s3⟩ ⟨σ2, c', he2, V, J2⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [hv] at he2
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he2))
      refine (WP.spec_ok _).2 ⟨σu, ?_, _, hku, rfl, V, Ac1, Lst1, D1, J2⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_right (by simp)]; rfl
    · refine WP.spec_mono (J1.setConsumedJ hAT hmax htu hsc hctT) ?_
      rintro s3 ⟨σ2, he2, -, V, J2⟩
      obtain ⟨v', w', he2'⟩ := Sched.setConsumed_shape hkz hk1
      have eσ2 := the_result he2' he2
      refine ⟨σ2, ?_, Endp.replyTcb { x with tcbState := .restart } w', by rw [eσ2]; simp [updK], rfl,
        V, Ac1, Lst1, D1, J2⟩
      unfold Fl4Spec.NonDet.when; rw [ite_eq_left rfl, ← hsetc]; exact he2
  -- the decode
  unfold ScReplyJSt syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  swap
  · simp only [↓reduceIte, WP.spec_ok]
    intro h; cases h
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold schedcontext.decode
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id (ar := arI) a hS (hback h0).1
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok, ite_eq_left l44, hs1]
  simp only [bind_ok]
  refine WP.spec_bind hSC ?_
  rintro s3 ⟨σ2, hrf, y, hk2, hrs2, V, Ac2, Lst2, D2, J2⟩
  refine WP.spec_bind (J2.runJ hctT hk2 hrs2) ?_
  rintro s4 ⟨Lst4, D4, J4⟩
  rw [WP.spec_ok]
  intro _ _ inv σ0 data σa σb hrun he0' he1 htail
  have e := hinv inv hrun
  subst e
  rw [he0] at he0'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he0'))
  have he1' : Fl4Spec.returnConsumed (Z := Unit) sc.bv σ1 = ({(data, σa)}, False) := he1
  rw [hrc] at he1'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst he1'))
  rw [specTail_of_restart hku rfl, nd_bind_one hrf, Notif.setThreadState_eq .running hk2] at htail
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 htail)
  exact ⟨_, _, _, _, _, J4⟩



set_option maxHeartbeats 2000000 in
/-- (p3J gen 38) **The SchedContext cap for Consumed, Bind and UnbindObject, `XCap` at stable ghosts**
(ScJointStep's `decode_invocation_sched_contextJ`, the same proof with `JStab Z H Cs` for `JAt`: every
outcome of `sched_contextJ_step` is at `Z` itself, Consumed's reply at `Z.mv Z.G V`). -/
theorem decScJ3St {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) [VxE Z] (hres : σ.schedulerAction = .resumeCurThread)
    (htm : TimeAgree arI) (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st Z.N Z.T Z.C Z.c)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ Z.C) (hpi : sc.bv ≠ σ.idleSc)
    (hl : lbl = fl4_abi.label.SchedContextConsumed ∨ lbl = fl4_abi.label.SchedContextBind ∨
      lbl = fl4_abi.label.SchedContextUnbindObject)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ Z.T ∧ L.mem s (P1.scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ Z.N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel Z.th (L.mem s) x0 (excaps.map Prod.fst))
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef)
    (hslot : capAt (L.mem s) slot = ok (.SchedContext sc sb)) (hslotS : IsSlot Z.th slot) (hsb : sb.val < 64)
    (hssz : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → n + Fl4Spec.minSchedContextBits = sb.val)
    (hx0S : x0 ≠ 0#u64 → IsSlot Z.th x0)
    (hArch : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => ∀ c, AR a c → AR r.2.2 c ⦄)
    (hRest : syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ r => r.1 = .Ok () → ∀ σ1, (∃ inv σ0,
        (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)).run σ = ({(.ok inv, σ)}, False) ∧
        Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ0)}, False) ∧
        Fl4Spec.invokeSchedContext (Z := Unit) inv σ0 = ({([], σ1)}, False)) →
        ScStepP1 (L := L) Z H Cs s r.2.1 ⦄)
    (hRep : lbl = fl4_abi.label.SchedContextConsumed →
      ScReplyJSt (L := L) (arI := arI) AR Z H Cs s a σ lbl length slot sc sb blk call don fp buf extra slbl excaps ct) :
    XCap (L := L) arI (JStab (L := L) arI AR Z H Cs) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  have hJ := sched_contextJ_step s a σ J hres htm hmb hmax htu hmsg lbl slbl hlbl sb hsc hpi
    hl hback hbn hct hcs extra
    x0 hx0 excaps hex length slot buf blk call don fp args ci sl buffer hslot hslotS hsb hssz hx0S hArch hRest
  obtain ⟨r, hr, hp⟩ := spec_exists hJ
  have tr : ∀ P : core.result.Result Unit error.Exc × S × A → Prop, P r →
      syscall.decode_invocation st arI s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra ⦃ P ⦄ :=
    fun P hP => by rw [hr]; exact (WP.spec_ok _).2 hP
  obtain ⟨hcur, -⟩ := J.curEq hct
  rcases hp with ⟨σ', Ac', Lst', D', J', ⟨e, h1, rfl, h2, h3, e', h4, h5⟩ | ⟨h1, rfl, inv, σ0, h2, h3, h4⟩⟩ |
    ⟨h1, hne, rfl, inv, σ0, data, σ1, h2, h3, h4, hdn, σ2, h5⟩
  · left
    refine tr _ (Or.inl ⟨e, h1, h2, ⟨e', h4, h5⟩, ?_⟩)
    exact J'.stab
  · left
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J'.xtop.rel
    refine tr _ (Or.inr ⟨.invokeSchedContext inv, DecOut.of_eq (run_liftME_ok h2), σ0, by rw [hcur]; exact h3, (.ok [], σ'),
      mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := ([], σ'))
        (by rw [h4]; exact Set.mem_singleton _),
      ⟨Z.th, Z.G, Or.inl ⟨h1, rfl⟩, hPl, hCR, hFI, hD, hMO⟩, J'.stab⟩)
  · right
    by_cases l44 : lbl = fl4_abi.label.SchedContextConsumed
    swap
    · exfalso
      refine hdn (invokeSc_data_nil ?_ h4)
      rcases hl.resolve_left l44 with l | l
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at h2
        obtain ⟨cap, rfl⟩ := (retP_bindDec _ _).of_run h2
        exact Or.inl ⟨_, _, rfl⟩
      · have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
          rw [hlbl, l]; unfold scLabelOf; simp
        simp only [Fl4Spec.decodeSchedContextInvocation, hg] at h2
        obtain ⟨cap, rfl⟩ := (retP_unbindObjDec _ _).of_run h2
        exact Or.inr ⟨_, _, rfl⟩
    have hR := hRep l44
    unfold ScReplyJSt at hR
    rw [hr, WP.spec_ok] at hR
    have hX := hR h1 hne inv σ0 data σ1 σ2 h2 h3 h4 h5
    obtain ⟨G2, V2, Ac2, Lst2, D2, J2⟩ := hX
    obtain ⟨hPl, hCR, hFI, hD, hMO, -, -⟩ := J2.xtop.rel
    exact tr _ (Or.inr ⟨h1, hne, .invokeSchedContext inv, DecOut.of_eq (run_liftME_ok h2), σ0, by rw [hcur]; exact h3, data, σ1,
      mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
        (by rw [h4]; exact Set.mem_singleton _),
      ((), σ2), h5, ⟨(Z.mv G2 V2).th, (Z.mv G2 V2).G, hPl, hCR, hFI, hD, hMO⟩, ⟨G2, V2, Ac2, Lst2, D2, J2⟩⟩)

end

end

end Fl4Proofs.P3
