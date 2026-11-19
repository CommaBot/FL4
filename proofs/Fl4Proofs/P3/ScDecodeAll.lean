/-
P3 (DESIGN.md §9), scheduling contexts: **the SchedContext decode with every
relation** (`sc_decode_refines`).

* `UFoot`: every word a SchedContext invocation may write (`TFoot` and the
  reply words);
* `ScAll`: after the invocation, the scheduler relations (`SRels`), the
  yield-to, MCP and call-stack relations (with a new ghost stack), the
  replies' placement, and the writes in `UFoot`;
* `ScAll.of_k`, `.of_t`, `.of_u`: from the branches' footprints (`KFoot` for
  Bind, UnbindObject and Consumed, `TFoot` for YieldTo, `RFoot` for Unbind)
  and the spec's `SOK` (ScPres.lean);
* `sc_decode_refines`: over every label, ending in `ScAll`.
-/
import Fl4Proofs.P3.ScKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **Every word a SchedContext invocation may write.** -/
def UFoot (st : machine.Store S) [L : LawfulStore st] (T N C R : Set U64) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  TFoot st T N C c s σ b ∨ RW R C b ∨ RegW T b

/-- **The relations after a SchedContext invocation** from `(s0, σ0)`. -/
def ScAll (N T C R : Set U64) (c : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S) (σ : Fl4Spec.State Unit) :
    Prop :=
  SRels (st := st) N T C c s σ ∧ YieldRel T C (L.mem s) σ ∧ McpRel T (L.mem s) σ ∧
    (∃ Lst' : U64 → List U64, CallRel (L.mem s) R C σ Lst' ∧ RFree (L.mem s) R C σ Lst') ∧
    RPlaced st N T C R c s σ ∧ WritesIn st s0 s (UFoot st T N C R c s0 σ0)

/-- `ScAll` from a `KFoot` branch (Bind, UnbindObject, Consumed). -/
theorem ScAll.of_k {N T C R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) (hY : YieldRel T C (L.mem s) σ)
    (hM : McpRel T (L.mem s) σ) {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst)
    (hRF : RFree (L.mem s) R C σ Lst) (h : KRels (st := st) N T C c s σ s' σ') :
    ScAll (st := st) N T C R c s σ s' σ' := by
  obtain ⟨hSR, hw, hsok⟩ := h
  obtain ⟨k1, k2, k3, k4⟩ := KFoot.keep hS hRP hw
  have hck := hsok.ckeep rfl
  obtain ⟨hCR', hRP'⟩ := CallRel.carry hCR hRP ⟨k3, k4⟩ hw.1 hck
  exact ⟨hSR, hY.frame k2 (hsok.ykeep rfl), hM.frame k1 hsok.mcpKeep, ⟨Lst, hCR', RFree.carry hRF hCR k4 hck⟩,
    hRP', hw.mono fun b hb => Or.inl (Or.inl hb)⟩

/-- `ScAll` from a `TFootR` branch (YieldTo, Consumed: the yield-to relation
carried, the caller's registers written by the reply). -/
theorem ScAll.of_tr {N T C R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit} {f : Bool × Bool}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hM : McpRel T (L.mem s) σ) {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst)
    (hRF : RFree (L.mem s) R C σ Lst) (hSR : SRels (st := st) N T C c s' σ') (hY' : YieldRel T C (L.mem s') σ')
    (hw : WritesIn st s s' (TFootR st T N C c s σ)) (hsok : SOK f σ σ') (hf : f.2 = true) :
    ScAll (st := st) N T C R c s σ s' σ' := by
  obtain ⟨k1, k3, k4⟩ := TFootR.keep hS hRP hw
  have hck := hsok.ckeep hf
  obtain ⟨hCR', hRP'⟩ := CallRel.carry hCR hRP ⟨k3, k4⟩ hw.1 hck
  exact ⟨hSR, hY', hM.frame k1 hsok.mcpKeep, ⟨Lst, hCR', RFree.carry hRF hCR k4 hck⟩, hRP',
    hw.mono fun b hb => by rcases hb with hb | hb; exact Or.inl hb; exact Or.inr (Or.inr hb)⟩

/-- `ScAll` from the YieldTo branch (`TFootR`; it carries the yield-to relation). -/
theorem ScAll.of_t {N T C R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hM : McpRel T (L.mem s) σ) {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst)
    (hRF : RFree (L.mem s) R C σ Lst)
    (h : YRels (st := st) N T C c s' σ' ∧ WritesIn st s s' (TFootR st T N C c s σ) ∧ SOK (false, true) σ σ') :
    ScAll (st := st) N T C R c s σ s' σ' := by
  obtain ⟨⟨hS', hR', hN', hI', hY', -⟩, hw, hsok⟩ := h
  exact ScAll.of_tr hS hRP hM hCR hRF ⟨hS', hR', hN', hI'⟩ hY' hw hsok rfl

/-- `ScAll` from the Unbind branch (`RFoot`; it carries the call-stack relation). -/
theorem ScAll.of_u {N T C R : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) (hY : YieldRel T C (L.mem s) σ)
    (hM : McpRel T (L.mem s) σ) {Lst' : U64 → List U64}
    (h : SRels (st := st) N T C c s' σ' ∧ CallRel (L.mem s') R C σ' Lst' ∧ RPlaced st N T C R c s' σ' ∧
      RFree (L.mem s') R C σ' Lst' ∧ WritesIn st s s' (RFoot st T N C R c s σ))
    (hsok : SOK (true, false) σ σ') :
    ScAll (st := st) N T C R c s σ s' σ' := by
  obtain ⟨hSR, hCR', hRP', hRF', hw⟩ := h
  obtain ⟨k1, k2⟩ := RFoot.keep hS hRP hw
  exact ⟨hSR, hY.frame k2 (hsok.ykeep rfl), hM.frame k1 hsok.mcpKeep, ⟨Lst', hCR', hRF'⟩, hRP',
    hw.mono fun b hb => by rcases hb with hb | hb; exact Or.inl (Or.inl hb); exact Or.inr (Or.inl hb)⟩

/-- **The finer footprint** of a SchedContext invocation by label: Bind and
UnbindObject write only `TFoot` words, and so does a YieldTo from an SC
yielded to by none that leaves the caller restarting (it switched; a YieldTo
returning at once has replied and set the caller running). -/
def ScFine (N T C : Set U64) (c lbl sc ct : U64) (s0 : S) (σ0 : Fl4Spec.State Unit) (s : S)
    (σ : Fl4Spec.State Unit) : Prop :=
  ((lbl = fl4_abi.label.SchedContextBind ∨ lbl = fl4_abi.label.SchedContextUnbindObject) →
    WritesIn st s0 s (TFoot st T N C c s0 σ0)) ∧
  (lbl = fl4_abi.label.SchedContextYieldTo → L.mem s0 (scYieldFromA sc) = 0#u64 →
    ∀ x', σ.kheap ct.bv = some (.tcb x') → x'.tcbState = .restart → WritesIn st s0 s (TFoot st T N C c s0 σ0))

theorem lbl_ne {lbl x y : U64} (h : lbl = x) (hv : x.val ≠ y.val) : lbl ≠ y :=
  fun e => hv (by rw [← h, e])

/-- **SchedContext invocation decode refines l4v
`decode_sched_context_invocation`**, then `set_thread_state Restart` and
`invoke_sched_context` (with `handle_invocation`'s reply and `Running` when
the invocation returns data), over every label (Consumed, Bind, UnbindObject,
Unbind, YieldTo, anything else illegal).

The hypotheses are the labels': the relations (with the yield-to, MCP and
call-stack relations, `ActIdle`), the SC's back-pointer (`hback`: a bound
thread of `T`, not the idle thread, whose SC word is `sc`; P1's coming
sc.tcb↔tcb.sc invariant) and notification (`hbn`), the SC not the idle SC
(`hpi`), the extra cap (`ExtraRel`, its thread or notification in `T` or
`N`), the caller schedulable (`hcs`), and the platform facts (`hT`, `hmb`,
`hmax`, `htu`) and the Ep side's message hypothesis (`hmsg`). -/
theorem sc_decode_refines {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (hsc : sc ∈ C) (hpi : sc.bv ≠ σ.idleSc)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (call : Bool)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c) :
    schedcontext.decode st ar s a lbl sc call extra ⦃ res =>
      CPost σ (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv excaps) s a
        (ScQ (fun s' σ' => ScAll (st := st) N T C R c s σ s' σ' ∧ ScFine (st := st) N T C c lbl sc ct s σ s' σ')
          σ ct call) res ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hsc0 := hC0 sc hsc
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hctT : ct ∈ T := hct' ▸ hc.curT
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  obtain ⟨xc, scq, yq, nq, hkc, -, hrun, -⟩ := schedulable_inv hcs
  obtain ⟨y, n, hk, hx⟩ := hs.scs sc hsc
  have hdec : ∀ g, Fl4Spec.genInvocationType slbl = g →
      (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv excaps).run σ =
        (match g with
          | .schedContextConsumed => Fl4Spec.NonDetE.returnOk <| .invokeSchedContextConsumed sc.bv
          | .schedContextBind => Fl4Spec.decodeSchedContextBind sc.bv excaps
          | .schedContextUnbindObject => Fl4Spec.decodeSchedContextUnbindObject sc.bv excaps
          | .schedContextUnbind => do
            let scx ← Fl4Spec.NonDetE.liftE <| Fl4Spec.getSchedContext sc.bv
            let ctPtr ← Fl4Spec.NonDetE.liftE <| Fl4Spec.NonDet.gets fun s : Fl4Spec.State Unit => s.curThread
            Fl4Spec.NonDetE.whenE (scx.scTcb = some ctPtr) <| Fl4Spec.NonDetE.throwError .illegalOperation
            Fl4Spec.NonDetE.returnOk <| .invokeSchedContextUnbind sc.bv
          | .schedContextYieldTo => Fl4Spec.decodeSchedContextYieldTo sc.bv
          | _ => Fl4Spec.NonDetE.throwError <| .illegalOperation : Fl4Spec.SEMonad Unit Fl4Spec.SchedContextInvocation).run σ := by
    intro g hg; unfold Fl4Spec.decodeSchedContextInvocation; rw [hg]; rfl
  unfold schedcontext.decode
  step with obj.Sc.tcb.spec as ⟨i, hi⟩
  rw [scTcbA_eq] at hi
  subst hi
  refine WP.spec_bind (show _ ⦃ r => r = (s, a) ⦄ from ?_) ?_
  · by_cases h0 : L.mem s (scW sc 24#u64) = 0#u64
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = false := by simp [h0]
      simp only [this, Bool.false_eq_true, ↓reduceIte]; exact (WP.spec_ok _).mpr rfl
    · have : (L.mem s (scW sc 24#u64) != 0#u64) = true := by simp [h0]
      simp only [this, ↓reduceIte]; exact remote_tcb_stall_id a hS (hback h0).1
  intro r hr
  subst hr
  show (sched.cur_thread st s >>= _) ⦃ _ ⦄
  rw [hct, bind_tc_ok]
  by_cases l44 : lbl = fl4_abi.label.SchedContextConsumed
  · rw [ite_eq_left l44]
    have hg : Fl4Spec.genInvocationType slbl = .schedContextConsumed := by
      rw [hlbl, l44]; unfold scLabelOf; simp
    refine WP.spec_mono (sc_consumed_refines s a σ hS hR hN hI hY hsc hctT hkc hrun hAI call hmax htu hmsg) ?_
    rintro r ⟨h1, -, σ1, data, σ2, σ3, he1, he2, hst2, he3, hS3, hR3, hN3, hI3, hY3, -, hw3⟩
    have hsok : SOK (true, true) σ σ3 := ((pres_setThreadState _ _ _).of_eq he1).trans
      (((pres_returnConsumed _ _).of_eq he2).trans
        ((pres_bind (pres_when _ (pres_replyFromKernel _ _ _)) fun _ => pres_setThreadState _ _ _).of_eq he3))
    exact Or.inr ⟨.invokeSchedContextConsumed sc.bv, by rw [hdec _ hg]; rfl, h1, σ1, data, σ2, σ3, he1, he2,
      Or.inr ⟨retConsumed_ne he2, hst2, he3⟩, ScAll.of_tr hS hRP hM hCR hRF ⟨hS3, hR3, hN3, hI3⟩ hY3 hw3 hsok rfl,
      fun h => by rcases h with h | h <;> exact absurd h (lbl_ne l44 (by simp)),
      fun h => absurd h (lbl_ne l44 (by simp))⟩
  rw [ite_eq_right l44]
  have h44 : lbl.val ≠ 44 := fun h => l44 (UScalar.eq_of_val_eq (by simp [h]))
  by_cases l41 : lbl = fl4_abi.label.SchedContextBind
  · rw [ite_eq_left l41]
    have hg : Fl4Spec.genInvocationType slbl = .schedContextBind := by
      rw [hlbl, l41]; unfold scLabelOf; simp
    exact WP.spec_mono (bind_branch_refines hT th s a σ hS hR hN hI hsc hsc0 extra x0 hx0 excaps hex hcapT hcapN
      hctT hkc hrun call) fun r h => CPost.congr (by rw [hdec _ hg])
        (h.mono fun _ _ hq => hq.mono fun _ _ hk => ⟨ScAll.of_k hS hRP hY hM hCR hRF hk,
          fun _ => WritesIn.tfoot_of_kfoot hk.2.1, fun h => absurd h (lbl_ne l41 (by simp))⟩)
  rw [ite_eq_right l41]
  have h41 : lbl.val ≠ 41 := fun h => l41 (UScalar.eq_of_val_eq (by simp [h]))
  by_cases l43 : lbl = fl4_abi.label.SchedContextUnbindObject
  · rw [ite_eq_left l43]
    have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbindObject := by
      rw [hlbl, l43]; unfold scLabelOf; simp
    exact WP.spec_mono (unbindobj_branch_refines th s a σ hS hR hN hI hsc hsc0 extra x0 hx0 excaps hex hcapT hcapN
      hctT hcur hkc hrun call) fun r h => CPost.congr (by rw [hdec _ hg])
        (h.mono fun _ _ hq => hq.mono fun _ _ hk => ⟨ScAll.of_k hS hRP hY hM hCR hRF hk,
          fun _ => WritesIn.tfoot_of_kfoot hk.2.1, fun h => absurd h (lbl_ne l43 (by simp))⟩)
  rw [ite_eq_right l43]
  have h43 : lbl.val ≠ 43 := fun h => l43 (UScalar.eq_of_val_eq (by simp [h]))
  by_cases l42 : lbl = fl4_abi.label.SchedContextUnbind
  · rw [ite_eq_left l42]
    have hg : Fl4Spec.genInvocationType slbl = .schedContextUnbind := by
      rw [hlbl, l42]; unfold scLabelOf; simp
    have hpre := hdec _ hg
    dsimp only at hpre
    rw [lE_bind (getSchedContext_eq hk), lE_bind (show Fl4Spec.NonDet.gets (fun s : Fl4Spec.State Unit => s.curThread) σ =
      ({(σ.curThread, σ)}, False) from rfl), hcur] at hpre
    have hct0 : ct ≠ 0#u64 := fun e => (hc.tcbs ct hctT).ne0 (by rw [e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i1, hi1⟩
    rw [scTcbA_eq] at hi1
    subst hi1
    by_cases he : L.mem s (scW sc 24#u64) = ct
    · rw [ite_eq_left he]
      refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
      rw [hpre]
      exact wE_pos (by rw [hx.tcb]; exact (bv_optRef_some hct0).2 he) _ _ σ
    rw [ite_eq_right he]
    refine WP.spec_mono (unbind_invoke_refines s a σ hS hR hN hI hCR hRP hsc hsc0 hpi hk
      (fun t ht => by
        have h0 : L.mem s (scW sc 24#u64) ≠ 0#u64 := by intro h; rw [hx.tcb, h, optRef_zero] at ht; cases ht
        obtain ⟨g1, -, g3⟩ := hback h0
        have : L.mem s (scW sc 24#u64) = t := (bv_optRef_some (fun e => by
          rw [e] at ht; exact absurd (by rw [hx.tcb, optRef_ne h0] at ht; exact Option.some.inj ht) (by
            intro h'; exact h0 (eq_of_bv (h'.trans (by rfl)))))).1 (by rw [← hx.tcb]; exact ht)
        rw [← this]; exact ⟨g1, g3⟩)
      (hbn y n hk) hctT hkc hrun hRF) ?_
    rintro r ⟨h1, σ0, σ3, Lst', he0, he3, hR3, hCR3, hRP3, hRF3, hw3⟩
    have hsok : SOK (true, false) σ σ3 := ((pres_setThreadState _ _ _).of_eq he0).trans
      (((pres_invokeSchedContext _).of_eq he3).weaken (fun _ => by simp)
        (fun h => by cases h))
    refine Or.inr ⟨.invokeSchedContextUnbind sc.bv, ?_, h1, σ0, [], σ3, σ3, he0, he3, Or.inl ⟨rfl, rfl⟩,
      ⟨ScAll.of_u hS hRP hY hM ⟨hR3, hCR3, hRP3, hRF3, hw3⟩ hsok,
        fun h => by rcases h with h | h <;> exact absurd h (lbl_ne l42 (by simp)),
        fun h => absurd h (lbl_ne l42 (by simp))⟩⟩
    rw [hpre, wE_neg (fun h => he ((bv_optRef_some hct0).1 (hx.tcb ▸ h)))]; rfl
  rw [ite_eq_right l42]
  have h42 : lbl.val ≠ 42 := fun h => l42 (UScalar.eq_of_val_eq (by simp [h]))
  by_cases l45 : lbl = fl4_abi.label.SchedContextYieldTo
  · rw [ite_eq_left l45]
    have hg : Fl4Spec.genInvocationType slbl = .schedContextYieldTo := by
      rw [hlbl, l45]; unfold scLabelOf; simp
    refine WP.spec_mono (yieldto_branch_refines s a σ hS hR hN hI hY hAI hM hC0 hsc
      (fun h0 => ⟨(hback h0).1, (hback h0).2.1⟩) hctT hcur hcs call hmb hmax htu hmsg) ?_
    intro r h
    exact CPost.congr (by rw [hdec _ hg]) (h.mono fun inv r' hq => hq.mono fun _ _ hr =>
      ⟨ScAll.of_t hS hRP hM hCR hRF ⟨hr.1, hr.2.1, hr.2.2.1⟩,
        fun h => by rcases h with h | h <;> exact absurd h (lbl_ne l45 (by simp)), fun _ h0 x' hk hst => hr.2.2.2 h0 ⟨x', hk, hst⟩⟩)
  rw [ite_eq_right l45]
  have h45 : lbl.val ≠ 45 := fun h => l45 (UScalar.eq_of_val_eq (by simp [h]))
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by
    rw [hlbl]; unfold scLabelOf; simp [h41, h42, h43, h44, h45]
  refine illegal_ok s a _ (Or.inl ⟨_, .illegalOperation, rfl, ?_, Or.inl trivial⟩)
  rw [hdec _ hg]; rfl

end

end

end Fl4Proofs.P3.Sched
