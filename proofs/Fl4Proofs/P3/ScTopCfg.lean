/-
P3 (DESIGN.md §9), scheduling contexts: **the SchedControl cap at the top
level** and the placement record.

* `ScPlaced`: the placement hypotheses of the scheduling-context caps
  (`SlotsApart`, the notifications apart from the kernel-global area), to
  be supplied once at the top level;
* `decode_invocation_sched_control`: `DecOK` for the SchedControl cap
  (`decode_configure_refines` with its `KFoot` footprint, the spec's `SOK`
  from `pres_invokeSchedControlConfigureFlags`), `domFrame_sched_control`,
  `decode_invocation_sched_controlD`;
* `decode_invocation_sched_contextP`, `…_controlP`: the `DecOKD` statements
  from `ScPlaced`.
-/
import Fl4Proofs.P3.ScTop
import Fl4Proofs.P3.ScDecodeCfg
import Fl4Proofs.P3.ScPresCfg
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **The placement of the scheduling-context objects** against the typed
heap and the kernel-global area. -/
structure ScPlaced (th : TypedHeap) (T N C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  slots : SlotsApart (st := st) th T N C R c s σ
  ntfnKs : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val

/-- The outcomes of `liftE m` then `returnOk`: the states of `m`'s. -/
theorem mem_liftE_ret_inv {σ ε α β : Type} {m : Fl4Spec.NonDet σ α} {b : β} {s : σ} {y : Except ε β × σ}
    (h : y ∈ ((Fl4Spec.NonDetE.liftE (ε := ε) m >>= fun _ => Fl4Spec.NonDetE.returnOk b).run s).1) :
    ∃ z ∈ (m s).1, y.2 = z.2 := by
  rw [ExceptT.run_bind] at h
  obtain ⟨⟨r, σx⟩, hx, hy⟩ := h
  obtain ⟨z, hz, hxz⟩ := mem_liftE_inv hx
  refine ⟨z, hz, ?_⟩
  simp only at hxz
  cases r <;> simp only [ExceptT.bindCont] at hy <;> rw [Set.mem_singleton_iff.1 hy] <;> exact hxz

/-- **The SchedControl cap** (`decode_configure_refines`): `DecOK`. -/
theorem decode_invocation_sched_control {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
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
    DecOK (L := L) ar s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (decode_configure_refines hT th s a σ hS hR hN hI hC hO lbl slbl hlbl cpu length buf ct
      hcpu hct args hlen hargs extra x0 hx0 _ hex (fun _ => hsb) (fun _ => hsc) hkc hrun) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_lift (f := Fl4Spec.Fl4Invocation.invokeSchedControl)
    rcases hq with ⟨e, e', he, hrun', herr⟩ | ⟨inv, hrun', σ1, σ', he1, he2, hr1, -, -, -, -, hw⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, e', hrun', herr⟩
    · refine Or.inr ⟨inv, hrun', σ1, by rw [hcur]; exact he1, (.ok [], σ'), ?_, th, G, Or.inl ⟨hr1, [], rfl⟩,
        hP, ?_⟩
      · exact mem_bindE_ok (mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv)
          (s := σ1) (x := ((), σ')) (by rw [he2]; exact Set.mem_singleton _)) (Set.mem_singleton _)
      · have hsok : SOK (false, false) σ σ' := ((pres_setThreadState _ _ _).of_eq he1).trans
          ((pres_invokeSchedControlConfigureFlags _ inv).of_eq he2)
        exact crel_of_sok hCRel hFI (slotsSame_of_ufoot hP hS hRP hA (hw.mono fun b hb => Or.inl (Or.inl hb))) hsok
  · exact top_invalid rfl

/-- **The SchedControl cap's domain-schedule frame.** -/
theorem domFrame_sched_control {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) (hRP : RPlaced st N T C R c s σ)
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
    DomFrame (L := L) ar s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hf := hc.node.fits
  have hal := hc.node.align
  simp only [LawfulStore.nodeBase] at hf hal
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hka : (L.ksb s).val % 8 = 0 := by omega
  refine ⟨?_, fun inv σ1 hd he y hy => ?_⟩
  · unfold syscall.decode_invocation
    rw [hct]; simp only [bind_ok]
    cases fp
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine WP.spec_mono (decode_configure_refines hT th s a σ hS hR hN hI hC hO lbl slbl hlbl cpu length buf ct
        hcpu hct args hlen hargs extra x0 hx0 _ hex (fun _ => hsb) (fun _ => hsc) hkc hrun) ?_
      rintro ⟨r0, s', a'⟩ hq
      rcases hq with ⟨e, e', he, -, -⟩ | ⟨inv, -, σ1, σ', -, -, -, -, -, -, -, hw⟩
      · cases he; exact ⟨rfl, fun _ _ => rfl⟩
      · refine ⟨hw.1, fun o ho => hw.mem_eq (ksW_al hkf hka (domOffs_lt ho).1 (domOffs_lt ho).2) fun hb =>
          UFoot.ne_ks hS hRP hNk (Or.inl (Or.inl hb)) (domOffs_lt ho).1 rfl⟩
    · simp [WP.spec_ok]
  · cases fp
    · obtain ⟨i, rfl⟩ := DecOut.liftME_inv (f := Fl4Spec.Fl4Invocation.invokeSchedControl) hd
      obtain ⟨x, hx, hyx⟩ := mem_liftE_ret_inv
        (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) i) hy
      have h1 := (pres_setThreadState (false, false) _ _).of_eq he
      have h2 := pres_invokeSchedControlConfigureFlags (false, false) i σ1 x hx
      rw [hyx]
      exact ⟨h2.dl.trans h1.dl, h2.dsi.trans h1.dsi⟩
    · exfalso
      obtain ⟨hm, -⟩ := hd
      have e : (specDec true slbl (args.map UScalar.bv) ci sl (.SchedControl cpu) excaps buffer).run σ =
          ({(.error (.invalidCapability 0), σ)}, False) := rfl
      rw [e] at hm
      simp at hm

/-- **The SchedControl cap with the domain schedule**, the placement from
`ScPlaced`. -/
theorem decode_invocation_sched_controlP {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
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
    DecOKD (L := L) ar s a σ lbl length slot (.SchedControl cpu) blk call don fp buf extra slbl
      (args.map UScalar.bv) ci sl excaps buffer :=
  DecOK.withDom ar hDR
    (decode_invocation_sched_control hT th hP s a σ G hCRel hFI hS hR hN hI hC hO hRP hPl.slots lbl slbl hlbl cpu
      length buf ct hcpu hct args hlen hargs extra x0 hx0 excaps hex hsb hsc hkc hrun slot blk call don fp ci sl buffer)
    (domFrame_sched_control hT th s a σ hS hR hN hI hC hO hRP hPl.ntfnKs lbl slbl hlbl cpu length buf ct hcpu hct
      args hlen hargs extra x0 hx0 excaps hex hsb hsc hkc hrun slot blk call don fp ci sl buffer)

/-- **The SchedContext cap with the domain schedule**, the placement from
`ScPlaced`. -/
theorem decode_invocation_sched_contextP {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
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
    DecOKD (L := L) ar s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra slbl args ci sl
      excaps buffer :=
  decode_invocation_sched_contextD hT th hP s a σ G hCRel hFI hDR hS hR hN hI hY hAI hM hC0 hCR hRP hRF hPl.slots
    hPl.ntfnKs lbl slbl hlbl sb hsc hpi hback hbn hct hcs extra x0 hx0 excaps hex hcapT hcapN hmb hmax htu hmsg
    length slot buf blk call don fp args ci sl buffer

end

end

end Fl4Proofs.P3.Sched
