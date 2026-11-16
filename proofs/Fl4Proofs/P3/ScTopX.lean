/-
P3 (DESIGN.md §9), scheduling contexts: **the SchedContext cap for
`handle_invocation_refinesMX`** (HandleTopX): `DecOKDMX ∨ DecOKRMX` with
`X` true (`decode_invocation_sched_contextX`).

FL4's decode is deterministic, so the arm is picked from its one result
(`sc_decode_refines`' `ScQ`):

* the invocation returned no data (Bind, UnbindObject, Unbind, and a
  YieldTo that switches): `DecOKDMX`, the spec's result `[]`, FL4's empty
  success tail still to run;
* it returned data (Consumed, and a YieldTo returning at once): FL4 has
  already replied (`set_consumed(…, call)`, then `Running`), so
  `DecOKRMX`: the spec's `specTail` (`reply_from_kernel (0, data)` when
  called, then `Running`, `specTail_of_restart`) relates to FL4's state,
  which is no longer `Restart`.

In both arms the CSpace relation, `FinInv`, the domain schedule and
`MdbOKV` are kept: FL4 writes only `UFoot` words (no slot word, no domain
word), and the spec's invocation, reply and `set_thread_state` keep `SOK`.
-/
import Fl4Proofs.P3.ScTop
import Fl4Proofs.P3.ScTopCfg
import Fl4Proofs.P3.HandleTopX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

/-- **`specTail` of a `Restart` thread**: the reply when called, then
`Running`. -/
theorem specTail_of_restart {σ : Fl4Spec.State Unit} {t : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap t = some (.tcb x)) (hrs : x.tcbState = .restart) (call : Bool) (rr : List Fl4Spec.Data) :
    Fl4Proofs.P3.specTail call t rr σ = (do
      Fl4Spec.NonDet.when (call = true) (Fl4Spec.replyFromKernel (Z := Unit) t (0, rr))
      Fl4Spec.setThreadState (Z := Unit) t .running : Fl4Spec.SMonad Unit Unit) σ := by
  unfold Fl4Proofs.P3.specTail
  rw [nd_bind_one (Notif.getThreadState_eq hk)]
  simp only [hrs]

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **The SchedContext cap for `handle_invocation_refinesMX`** (module
docstring). -/
theorem decode_invocation_sched_contextX {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst) (hA : SlotsApart (st := st) th T N C R c s σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ C) (hpi : sc.bv ≠ Fl4Spec.idleScPtr)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hcapT : ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKDMX (L := L) ar (fun _ _ _ => True) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ∨
    DecOKRMX (L := L) ar (fun _ _ _ => True) s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      slbl args ci sl excaps buffer ct := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  have hctT : ct ∈ T := hct' ▸ hc.curT
  have hf := hc.node.fits
  have hal := hc.node.align
  simp only [LawfulStore.nodeBase] at hf hal
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  -- the decode's one result
  have key : syscall.decode_invocation st ar s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra
      ⦃ res => (fp = true ∧ res = (.Err (.Sys (.InvalidCapability 0#u64)), s, a)) ∨
        (fp = false ∧ CPost σ (Fl4Spec.decodeSchedContextInvocation (Z := Unit) slbl sc.bv (excaps.map Prod.fst)) s a
          (ScQ (fun s' σ' => ScAll (st := st) N T C R c s σ s' σ' ∧ ScFine (st := st) N T C c lbl sc ct s σ s' σ')
            σ ct call) res) ⦄ := by
    unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact WP.spec_mono (sc_decode_refines hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF lbl slbl hlbl hsc hpi
        hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg) fun r h => Or.inr ⟨by trivial, h⟩
    · simp only [↓reduceIte, WP.spec_ok]
      exact Or.inl ⟨by trivial, by trivial⟩
  obtain ⟨r, hr, hq⟩ := spec_exists key
  have tr : ∀ P : core.result.Result Unit error.Exc × S × A → Prop, P r →
      syscall.decode_invocation st ar s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra ⦃ P ⦄ :=
    fun P hP => by rw [hr]; exact (WP.spec_ok _).2 hP
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, hq⟩
  · -- the first phase of a call: `InvalidCapability 0`
    left
    refine tr _ (Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, trivial⟩)
  rcases hq with ⟨e, e', he, hrun, herr⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, hcase, ⟨hall, -⟩⟩
  · left
    subst he
    exact tr _ (Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err hrun, herr⟩, trivial⟩)
  -- what both arms keep
  have hw := hall.2.2.2.2.2
  have hSS := slotsSame_of_ufoot hP hS hRP hA hw
  have hdw : ∀ o ∈ domOffs, L.mem r.2.1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := fun o ho =>
    hw.mem_eq (ksW_al hkf hka (domOffs_lt ho).1 (domOffs_lt ho).2) fun hb => UFoot.ne_ks hS hRP hNk hb (domOffs_lt ho).1 rfl
  have fin : ∀ σ' : Fl4Spec.State Unit, SOK (false, false) σ σ' →
      CRel th (L.mem r.2.1) σ' G ∧ FinInv th (L.mem r.2.1) σ' G ∧ DomRel (L.mem r.2.1) (L.ksb r.2.1) σ' ∧
        MdbOKV (L.ksb r.2.1) (L.mem r.2.1) G := by
    intro σ' hk
    obtain ⟨h1, h2⟩ := crel_of_sok hCRel hFI hSS hk
    exact ⟨h1, h2, by rw [hw.1]; exact hDR.frame hdw hk.dl hk.dsi, by rw [hw.1]; exact MdbOKV.of_same hCRel.2.2.1 hSS hFR⟩
  have hsok1 : SOK (false, false) σ σ1 := ((pres_setThreadState _ _ _).of_eq he0).trans
    (((pres_invokeSchedContext inv).of_eq he1).weaken (fun h => by cases h) (fun h => by cases h))
  have hdec : DecOut (specDec false slbl args ci sl (.SchedContext sc sb) excaps buffer) σ
      (.invokeSchedContext inv) := DecOut.of_eq (run_liftME_ok hrun)
  have hmem : ((.ok data, σ1) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
      ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedContext inv)).run σ0).1 :=
    mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
      (by rw [he1]; exact Set.mem_singleton _)
  rcases hcase with ⟨hd, -⟩ | ⟨⟨xr, hkr, hrs⟩, hdo⟩
  · -- no data: the empty success tail
    left
    obtain ⟨c1, c2, c3, c4⟩ := fin σ1 hsok1
    exact tr _ (Or.inr ⟨_, hdec, σ0, by rw [hcur]; exact he0, _, hmem,
      ⟨th, G, Or.inl ⟨hr1, by rw [hd]⟩, hP, c1, c2, c3, c4⟩, trivial⟩)
  · -- data: FL4 has replied
    right
    have hsok2 : SOK (false, false) σ σ2 := hsok1.trans
      ((pres_bind (pres_when _ (pres_replyFromKernel _ _ _)) fun _ => pres_setThreadState _ _ _).of_eq hdo)
    obtain ⟨c1, c2, c3, c4⟩ := fin σ2 hsok2
    obtain ⟨y2, hky2, hrun2⟩ := running_after hkr hdo
    obtain ⟨x2, hkx2, hrel2⟩ := hall.1.2.1.tcb ct hctT
    rw [hky2] at hkx2; cases hkx2
    have hne : L.mem r.2.1 (stA ct) ≠ sched.TS_RESTART := by
      intro e
      have h1 := hrel2.st
      rw [hrun2] at h1
      rw [show tStA ct = stA ct by rw [tStA_eq, stA_eq], e, tsVals.2.1] at h1
      simp [tsCode] at h1
    have hz : ((), σ2) ∈ (Fl4Proofs.P3.specTail call ct.bv data σ1).1 := by
      rw [specTail_of_restart hkr hrs, hdo]; exact Set.mem_singleton _
    exact tr _ (Or.inr ⟨hr1, hne, _, hdec, σ0, by rw [hcur]; exact he0, data, σ1, hmem, ((), σ2), hz,
      ⟨th, G, hP, c1, c2, c3, c4⟩, trivial⟩)


/-- **The SchedControl cap for `handle_invocation_refinesMX`**: its one
invocation (`ConfigureFlags`) returns no data, so `DecOKDMX` with `X` true. -/
theorem decode_invocation_sched_controlX {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (hFR : MdbOKV (L.ksb s) (L.mem s) G)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) (hRP : RPlaced st N T C R c s σ) (hA : SlotsApart (st := st) th T N C R c s σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOKDMX (L := L) ar (fun _ _ _ => True) s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra
      slbl (args.map UScalar.bv) ci sl excaps buffer := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  have hf := hc.node.fits
  have hal := hc.node.align
  simp only [LawfulStore.nodeBase] at hf hal
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  unfold DecOKDMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (decode_configure_refines hT th s a σ hS hR hN hI hC hO lbl slbl hlbl cpu length buf ct
      hcpu hct args hlen hargs extra x0 hx0 _ hex hsb hsc hkc hrun) ?_
    rintro ⟨r0, s', a'⟩ hq
    rcases hq with ⟨e, e', he, hrun', herr⟩ | ⟨inv, hrun', σ1, σ', he1, he2, hr1, -, -, -, -, hw⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, ⟨e', run_liftME_err hrun', herr⟩, trivial⟩
    · have hwU : WritesIn st s s' (UFoot st T N C R c s σ) := hw.mono fun b hb => Or.inl (Or.inl hb)
      have hSS := slotsSame_of_ufoot hP hS hRP hA hwU
      have hsok : SOK (false, false) σ σ' := ((pres_setThreadState _ _ _).of_eq he1).trans
        ((pres_invokeSchedControlConfigureFlags _ inv).of_eq he2)
      obtain ⟨c1, c2⟩ := crel_of_sok hCRel hFI hSS hsok
      have hdw : ∀ o ∈ domOffs, L.mem s' (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := fun o ho =>
        hw.mem_eq (ksW_al hkf hka (domOffs_lt ho).1 (domOffs_lt ho).2) fun hb =>
          UFoot.ne_ks hS hRP hNk (Or.inl (Or.inl hb)) (domOffs_lt ho).1 rfl
      refine Or.inr ⟨_, DecOut.of_eq (run_liftME_ok hrun'), σ1, by rw [hcur]; exact he1, (.ok [], σ'), ?_,
        ⟨th, G, Or.inl ⟨hr1, rfl⟩, hP, c1, c2, by rw [hw.1]; exact hDR.frame hdw hsok.dl hsok.dsi,
          by rw [hw.1]; exact MdbOKV.of_same hCRel.2.2.1 hSS hFR⟩, trivial⟩
      exact mem_bindE_ok (mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv)
        (s := σ1) (x := ((), σ')) (by rw [he2]; exact Set.mem_singleton _)) (Set.mem_singleton _)
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, ⟨_, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩, trivial⟩

end

end

end Fl4Proofs.P3.Sched
