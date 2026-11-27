/-
P3 (DESIGN.md §9), scheduling contexts: **the SchedContext cap at the top
level** (`DecOK`, DecodeTop.lean): `decode_invocation_sched_context`
discharges `decode_invocation_refines`' `hSchedContext`.

The CSpace relation (`CRel`) and `FinInv` are kept: FL4 writes only `UFoot`
words, which are no cap slot words when the typed heap's slots lie apart from
the scheduler's objects (`SlotsApart`: a placement hypothesis, the TCBs' slots
being below offset 256), so the slots are the same (`SlotsSame`); and the spec
keeps the CNodes, the TCBs' caps, the CDT and the object kinds (`SOK`, from
`pres_setThreadState` and `pres_invokeSchedContext`).
-/
import Fl4Proofs.P3.ScDecodeAll
import Fl4Proofs.P3.DecodeTopD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- **Hypothesis: the typed heap's cap slots lie apart from the scheduler's
objects** (the TCBs of `T` past offset 256, core `c`'s node, the
notifications of `N`, the SCs of `C`, the replies of `R`). -/
def SlotsApart (th : TypedHeap) (T N C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ a, IsSlot th a →
    (∀ t ∈ T, a.val + 32 ≤ t.val + 256 ∨ t.val + 4096 ≤ a.val) ∧
    (a.val + 32 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧
    (∀ n ∈ N, a.val + 32 ≤ n.val ∨ n.val + 40 ≤ a.val) ∧
    (∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → a.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ a.val) ∧
    (∀ r ∈ R, a.val + 32 ≤ r.val ∨ r.val + 32 ≤ a.val)

/-- A `UFoot` word is no slot word. -/
theorem UFoot.not_slot {th : TypedHeap} (hP : Placed th) {N T C R : Set U64} {c : U64} {s : S}
    {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hA : SlotsApart (st := st) th T N C R c s σ) {a k : U64} (ha : IsSlot th a) (hk : Off k)
    (hb : UFoot st T N C R c s σ (wordOf a k)) : False := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hv := slot_word_val hP ha hk
  have hkl := hk.lt
  obtain ⟨g1, g2, g3, g4, g5⟩ := hA a ha
  rcases hb with (((⟨y, hy, K, hK, e⟩ | ⟨b1, b2⟩) | ⟨n, hn, b1, b2⟩ | ⟨sc, hsc, x, n, hkx, ⟨b1, b2⟩, -⟩) |
      ⟨y, hy, e⟩) | ((⟨r, hr, e⟩ | ⟨q, hq, e⟩) | hreg)
  · have := congrArg UScalar.val e
    rw [hv, tfield_val (hT y hy) hK.2.1] at this
    have := g1 y hy; have := hK.1; have := hK.2.1; omega
  · rw [hv] at b1 b2; omega
  · have := g3 n hn; rw [hv] at b1 b2; omega
  · have := g4 sc hsc x n hkx; rw [hv] at b1 b2; omega
  · have := congrArg UScalar.val e
    rw [hv, yieldA_val hT hy] at this
    have := g1 y hy; omega
  · have := congrArg UScalar.val e
    rw [hv, rNextA_val (hRP.align r hr)] at this
    have := g5 r hr; omega
  · obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hq
    obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    have := congrArg UScalar.val e
    rw [hv, hvq] at this
    have := g4 q hq xq nq hkq; have := hsz xq nq hkq; omega
  · obtain ⟨y, hy, r1, r2⟩ := hreg.range hT
    rw [hv] at r1 r2
    have := g1 y hy; omega

/-- **The slots are kept** by a `UFoot` step. -/
theorem slotsSame_of_ufoot {th : TypedHeap} (hP : Placed th) {N T C R : Set U64} {c : U64} {s s' : S}
    {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hA : SlotsApart (st := st) th T N C R c s σ) (hw : WritesIn st s s' (UFoot st T N C R c s σ)) :
    SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have w : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
    hw.mem_eq (slot_word_aligned hP ha hk) fun hb => UFoot.not_slot hP hS hRP hA ha hk hb
  refine ⟨?_, w _ (Or.inr (Or.inl rfl)), w _ (Or.inr (Or.inr (Or.inl rfl))), w _ (Or.inr (Or.inr (Or.inr rfl)))⟩
  have := w _ (Or.inl rfl)
  rwa [wordOf_zero] at this

/-- **`CRel` and `FinInv` across a step** keeping the slots and `SOK`. -/
theorem crel_of_sok {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    {f : Bool × Bool} (hC : CRel th m σ G) (hFI : FinInv th m σ G) (hS : SlotsSame th m m') (hk : SOK f σ σ') :
    CRel th m' σ' G ∧ FinInv th m' σ' G := by
  obtain ⟨hR, hV, hM, hCd, hI⟩ := hC
  have hcap : ∀ x, IsSlot th x → capAt m' x = capAt m x := fun x hx => hS.capAt hx
  exact ⟨⟨((hk.stateRel hR).of_caps hcap), hV.of_caps hcap, hM.of_same hS, hCd.of_same hS hk.cdt hk.orig,
    hI.of_same hM hS⟩, hFI.of_same hM hS hk.ksub⟩

/-- **The SchedContext cap** (`sc_decode_refines`): `DecOK`, the CSpace
relation kept by `crel_of_sok`. -/
theorem decode_invocation_sched_context {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G)
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
    DecOK (L := L) ar s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra slbl args ci sl
      excaps buffer := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (sc_decode_refines hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF lbl slbl hlbl hsc hpi
      hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_lift (f := Fl4Spec.Fl4Invocation.invokeSchedContext)
    rcases hq with ⟨e, e', he, hrun, herr⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, -, ⟨hall, -⟩⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, e', hrun, herr⟩
    · refine Or.inr ⟨inv, hrun, σ0, by rw [hcur]; exact he0, (.ok data, σ1), ?_, th, G, Or.inl ⟨hr1, data, rfl⟩,
        hP, ?_⟩
      · exact mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
          (by rw [he1]; exact Set.mem_singleton _)
      · have hsok : SOK (false, false) σ σ1 := ((pres_setThreadState _ _ _).of_eq he0).trans
          (((pres_invokeSchedContext inv).of_eq he1).weaken (fun h => by cases h) (fun h => by cases h))
        exact crel_of_sok hCRel hFI (slotsSame_of_ufoot hP hS hRP hA hall.2.2.2.2.2) hsok
  · exact top_invalid rfl

/-! ## The domain schedule (`DomFrame`) -/

/-- A `UFoot` word is no word of the kernel-global area's first 256 bytes
(the domain schedule's words among them), when the notifications lie apart
from the kernel-global area (`hNk`). -/
theorem UFoot.ne_ks {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
    {b : U64} (hb : UFoot st T N C R c s σ b) {o : U64} (ho : o.val < 256) : b ≠ ksW (L.ksb s) o := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hf := hc.node.fits
  simp only [LawfulStore.nodeBase] at hf
  have hv : (ksW (L.ksb s) o).val = (L.ksb s).val + o.val := ksW_val (by omega)
  intro e
  have ev := congrArg UScalar.val e
  rw [hv] at ev
  rcases hb with (((⟨y, hy, K, hK, rfl⟩ | ⟨b1, b2⟩) | ⟨n, hn, b1, b2⟩ | ⟨sc, hsc, x, n, hkx, ho', -⟩) |
      ⟨y, hy, rfl⟩) | ((⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩) | hreg)
  · rw [tfield_val (hT y hy) hK.2.1] at ev
    have := hc.ksOut y hy; have := hK.1; have := hK.2.1; omega
  · simp only [LawfulStore.nodeBase] at b1; omega
  · have := hNk n hn; omega
  · have := (hS.scOut sc hsc x n hkx _ ho').2.2.2; omega
  · rw [yieldA_val hT hy] at ev
    have := hc.ksOut y hy; omega
  · rw [rNextA_val (hRP.align r hr)] at ev
    have := hRP.ksb r hr; simp only [LawfulStore.nodeBase] at this; omega
  · obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hq
    obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    have hin : ScObj q nq (scReplyA q) := by have := hsz xq nq hkq; unfold ScObj; rw [hvq]; omega
    have := (hS.scOut q hq xq nq hkq _ hin).2.2.2
    rw [hvq] at ev this; omega
  · obtain ⟨y, hy, r1, r2⟩ := hreg.range hT
    have := hc.ksOut y hy; omega

theorem domOffs_lt {o : U64} (ho : o ∈ domOffs) : o.val < 256 ∧ o.val % 8 = 0 := by
  simp only [domOffs, List.mem_cons, List.mem_nil_iff, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- The outcome of a `liftME` is one of the inner decode's. -/
theorem DecOut.liftME_inv {α β : Type} {f : α → β} {m : Fl4Spec.SEMonad Unit α} {σ : Fl4Spec.State Unit} {inv : β}
    (h : DecOut (Fl4Spec.NonDetE.liftME f m) σ inv) : ∃ i, inv = f i := by
  unfold DecOut Fl4Spec.NonDetE.liftME at h
  rw [ExceptT.run_bind] at h
  obtain ⟨⟨⟨r, σ'⟩, -, hm⟩, -⟩ := h
  cases r with
  | error e => exact absurd (Set.mem_singleton_iff.1 hm) (by simp)
  | ok i =>
    refine ⟨i, ?_⟩
    have := Set.mem_singleton_iff.1 hm
    simp only [Prod.mk.injEq, Except.ok.injEq] at this
    exact this.1

theorem mem_liftE_inv {σ ε α : Type} {m : Fl4Spec.NonDet σ α} {s : σ} {y : Except ε α × σ}
    (h : y ∈ ((Fl4Spec.NonDetE.liftE (ε := ε) m).run s).1) : ∃ x ∈ (m s).1, y.2 = x.2 := by
  unfold Fl4Spec.NonDetE.liftE at h
  rw [ExceptT.run_lift] at h
  obtain ⟨x, hx, hy⟩ := h
  rw [Set.mem_singleton_iff.1 hy]
  exact ⟨x, hx, rfl⟩

/-- **The SchedContext cap's domain-schedule frame**: FL4 writes only
`UFoot` words, none of the domain schedule's (the notifications lying apart
from the kernel-global area, `hNk`), and the spec keeps `domain_list` and
`domain_start_index` (`SOK`). -/
theorem domFrame_sched_context {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
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
    DomFrame (L := L) ar s a σ lbl length slot (.SchedContext sc sb) blk call don fp buf extra slbl args ci sl
      excaps buffer := by
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
      refine WP.spec_mono (sc_decode_refines hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF lbl slbl hlbl hsc hpi
        hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg) ?_
      rintro ⟨r0, s', a'⟩ hq
      rcases hq with ⟨e, e', he, -, -⟩ | ⟨inv, -, -, σ0, data, σ1, σ2, -, -, -, ⟨hall, -⟩⟩
      · cases he; exact ⟨rfl, fun _ _ => rfl⟩
      · have hw := hall.2.2.2.2.2
        refine ⟨hw.1, fun o ho => hw.mem_eq (ksW_al hkf hka (domOffs_lt ho).1 (domOffs_lt ho).2) fun hb =>
          UFoot.ne_ks hS hRP hNk hb (domOffs_lt ho).1 rfl⟩
    · simp [WP.spec_ok]
  · cases fp
    · obtain ⟨i, rfl⟩ := DecOut.liftME_inv (f := Fl4Spec.Fl4Invocation.invokeSchedContext) hd
      obtain ⟨x, hx, hyx⟩ := mem_liftE_inv (m := Fl4Spec.invokeSchedContext (Z := Unit) i) hy
      have h1 := (pres_setThreadState (false, false) _ _).of_eq he
      have h2 := (pres_invokeSchedContext i).weaken (f' := (false, false)) (fun h => by cases h) (fun h => by cases h)
        σ1 x hx
      rw [hyx]
      exact ⟨h2.dl.trans h1.dl, h2.dsi.trans h1.dsi⟩
    · exfalso
      obtain ⟨hm, -⟩ := hd
      have e : (specDec true slbl args ci sl (.SchedContext sc sb) excaps buffer).run σ =
          ({(.error (.invalidCapability 0), σ)}, False) := rfl
      rw [e] at hm
      simp at hm

/-- **The SchedContext cap with the domain schedule** (`DecOKD`). -/
theorem decode_invocation_sched_contextD {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst) (hA : SlotsApart (st := st) th T N C R c s σ)
    (hNk : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val)
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
  DecOK.withDom ar hDR
    (decode_invocation_sched_context hT th hP s a σ G hCRel hFI hS hR hN hI hY hAI hM hC0 hCR hRP hRF hA lbl slbl
      hlbl sb hsc hpi hback hbn hct hcs extra x0 hx0 excaps hex hcapT hcapN hmb hmax htu hmsg length slot buf blk
      call don fp args ci sl buffer)
    (domFrame_sched_context hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF hNk lbl slbl hlbl sb hsc hpi hback
      hbn hct hcs extra x0 hx0 excaps hex hcapT hcapN hmb hmax htu hmsg length slot buf blk call don fp args ci sl
      buffer)

end

end

end Fl4Proofs.P3.Sched
