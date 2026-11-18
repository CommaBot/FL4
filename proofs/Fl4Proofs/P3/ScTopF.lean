/-
P3 (DESIGN.md §9), scheduling contexts: **the SchedContext and SchedControl
caps with the frame invariant** (`DecOKF`, `DecOKDF`; TopF.lean).

Both caps' invocations keep every slot word (`slotsSame_of_ufoot`), so
`Vs.FrameInv` carries over by `FrameInv.of_same`, the ghost unchanged:

* `decode_invocation_sched_contextF`, `decode_invocation_sched_controlF`:
  `DecOKF`;
* `decode_invocation_sched_contextPF`, `decode_invocation_sched_controlPF`:
  `DecOKDF`, the placement from `ScPlaced`.
-/
import Fl4Proofs.P3.ScTopCfg
import Fl4Proofs.P3.TopF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- `top_of_lift` with the frame invariant. -/
theorem top_of_liftF {α : Type} {f : α → Fl4Spec.Fl4Invocation} {m : Fl4Spec.SEMonad Unit α}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f inv)).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
          Vs.FrameInv (L.mem res.2.1) G')) :
    TopPostF (L := L) σ blk call don (Fl4Spec.NonDetE.liftME f m) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err hr, he⟩
  · exact Or.inr ⟨f inv, DecOut.of_eq (run_liftME_ok hr), rest⟩

/-- **The SchedContext cap** with the frame invariant (`DecOKF`). -/
theorem decode_invocation_sched_contextF {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : Vs.FrameInv (L.mem s) G)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst) (hA : SlotsApart (st := st) th T N C R c s σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ C) (hpi : sc.bv ≠ σ.idleSc)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKF (L := L) ar s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra slbl args ci sl
      excaps buffer := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  unfold DecOKF syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (sc_decode_refines hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF lbl slbl hlbl hsc hpi
      hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_liftF (f := Fl4Spec.Fl4Invocation.invokeSchedContext)
    rcases hq with ⟨e, e', he, hrun, herr⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, -, ⟨hall, -⟩⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, e', hrun, herr⟩
    · have hSS := slotsSame_of_ufoot hP hS hRP hA hall.2.2.2.2.2
      refine Or.inr ⟨inv, hrun, σ0, by rw [hcur]; exact he0, (.ok data, σ1), ?_, th, G, Or.inl ⟨hr1, data, rfl⟩,
        hP, ?_⟩
      · exact mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
          (by rw [he1]; exact Set.mem_singleton _)
      · have hsok : SOK (false, false) σ σ1 := ((pres_setThreadState _ _ _).of_eq he0).trans
          (((pres_invokeSchedContext inv).of_eq he1).weaken (fun h => by cases h) (fun h => by cases h))
        obtain ⟨h1, h2⟩ := crel_of_sok hCRel hFI hSS hsok
        exact ⟨h1, h2, FrameInv.of_same hCRel.2.2.1 hFR hSS⟩
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The SchedControl cap** with the frame invariant (`DecOKF`). -/
theorem decode_invocation_sched_controlF {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : Vs.FrameInv (L.mem s) G)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) (hRP : RPlaced st N T C R c s σ) (hA : SlotsApart (st := st) th T N C R c s σ)
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
    DecOKF (L := L) ar s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  unfold DecOKF syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (decode_configure_refines hT th s a σ hS hR hN hI hC hO lbl slbl hlbl cpu length buf ct
      hcpu hct args hlen hargs extra x0 hx0 _ hex (fun _ => hsb) (fun _ => hsc) hkc hrun) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_liftF (f := Fl4Spec.Fl4Invocation.invokeSchedControl)
    rcases hq with ⟨e, e', he, hrun', herr⟩ | ⟨inv, hrun', σ1, σ', he1, he2, hr1, -, -, -, -, hw⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, e', hrun', herr⟩
    · have hSS := slotsSame_of_ufoot hP hS hRP hA (hw.mono fun b hb => Or.inl (Or.inl hb))
      refine Or.inr ⟨inv, hrun', σ1, by rw [hcur]; exact he1, (.ok [], σ'), ?_, th, G, Or.inl ⟨hr1, [], rfl⟩,
        hP, ?_⟩
      · exact mem_bindE_ok (mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv)
          (s := σ1) (x := ((), σ')) (by rw [he2]; exact Set.mem_singleton _)) (Set.mem_singleton _)
      · have hsok : SOK (false, false) σ σ' := ((pres_setThreadState _ _ _).of_eq he1).trans
          ((pres_invokeSchedControlConfigureFlags _ inv).of_eq he2)
        obtain ⟨h1, h2⟩ := crel_of_sok hCRel hFI hSS hsok
        exact ⟨h1, h2, FrameInv.of_same hCRel.2.2.1 hFR hSS⟩
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The SchedControl cap with the domain schedule and the frame invariant**
(`DecOKDF`), the placement from `ScPlaced`. -/
theorem decode_invocation_sched_controlPF {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : Vs.FrameInv (L.mem s) G)
    (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) (hRP : RPlaced st N T C R c s σ) (hPl : ScPlaced (st := st) th T N C R c s σ)
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
    DecOKDF (L := L) ar s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer :=
  DecOKF.withDom ar hDR
    (decode_invocation_sched_controlF hT th hP s a σ G hCRel hFI hFR hS hR hN hI hC hO hRP hPl.slots lbl slbl hlbl
      cpu length buf ct hcpu hct args hlen hargs extra x0 hx0 excaps hex hsb hsc hkc hrun slot blk call don fp ci sl
      buffer)
    (domFrame_sched_control hT th s a σ hS hR hN hI hC hO hRP hPl.ntfnKs lbl slbl hlbl cpu length buf ct hcpu hct
      args hlen hargs extra x0 hx0 excaps hex hsb hsc hkc hrun slot blk call don fp ci sl buffer)

/-- **The SchedContext cap with the domain schedule and the frame invariant**
(`DecOKDF`), the placement from `ScPlaced`. -/
theorem decode_invocation_sched_contextPF {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : Vs.FrameInv (L.mem s) G)
    (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst) (hPl : ScPlaced (st := st) th T N C R c s σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ C) (hpi : sc.bv ≠ σ.idleSc)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hcapT : x0 ≠ 0#u64 → ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : x0 ≠ 0#u64 → ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    DecOKDF (L := L) ar s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra slbl args ci sl
      excaps buffer :=
  DecOKF.withDom ar hDR
    (decode_invocation_sched_contextF hT th hP s a σ G hCRel hFI hFR hS hR hN hI hY hAI hM hC0 hCR hRP hRF hPl.slots
      lbl slbl hlbl sb hsc hpi hback hbn hct hcs extra x0 hx0 excaps hex hcapT hcapN hmb hmax htu hmsg length slot buf
      blk call don fp args ci sl buffer)
    (domFrame_sched_context hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF hPl.ntfnKs lbl slbl hlbl sb hsc hpi
      hback hbn hct hcs extra x0 hx0 excaps hex hcapT hcapN hmb hmax htu hmsg length slot buf blk call don fp args ci
      sl buffer)

end

end

end Fl4Proofs.P3.Sched
