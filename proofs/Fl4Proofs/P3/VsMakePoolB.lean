/-
P3 (DESIGN.md §9), VSpace: **ASIDControl `MakePool`'s perform without the
restart** (handoff/utj.md Round 15): VsMakePoolRel's `mp_perform_rel` from
the restart's state itself (`mp_perform_relB`, post `MpPostB` / `MpMidB`:
the spec's `perform_asid_control_invocation` from that state). For the
dirty case of the ASID control path at `J` (XTopJointMakePoolD), where the
state the perform starts from is the restart's, detyped at the region
(`JAtZ.drop`). The proof is `mp_perform_rel`'s after its restart step.
-/
import Fl4Proofs.P3.VsMakePoolRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`MpMid` without the restart**: the words written since `s0` (`MpW`),
the spec's step from `σ` (`MpStep`), the source's and destination's caps
after, the other slots' caps kept, `DelInv` kept, the decode's facts at
`s0`. -/
def MpMidB {A : Type} (th0 : TypedHeap) (s0 : S) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (p : U64)
    (dest ps : Fl4Spec.CslotPtr) (σ' : Fl4Spec.State Unit) (th' : TypedHeap)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ (hi : U64), hi.val < 2048 ∧ L.ksb res.2.1 = L.ksb s0 ∧ L.cpu res.2.1 = L.cpu s0 ∧
    (∀ b, Aligned b → ¬ MpW th0 p (L.ksb s0) hi b → L.mem res.2.1 b = L.mem s0 b) ∧
    (∀ w : U64, Aligned w → p.val ≤ w.val → w.val < p.val + 4096 → L.mem res.2.1 w = 0#u64) ∧
    (L.mem res.2.1 (atA (L.ksb s0) hi) = p) ∧
    MpStep p σ σ' ∧
    σ'.kheap p.bv = some (.archObj (.asidPool fun _ => none)) ∧
    (∀ o, o ≠ p.bv → σ'.kheap o = σ.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ σ'.kheap o = none) ∨
      ∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ σ'.kheap o = some (.cnode r cs')) ∧
    σ'.cdt = Function.update σ.cdt dest (some ps) ∧
    (∀ sl, sl ≠ dest → σ'.isOriginalCap sl = σ.isOriginalCap sl) ∧
    capV (L.mem res.2.1) (cslotAddr ps) = .Untyped p fl4_abi.consts.bits.ASID_POOL 4096#u64 false ∧
    (∃ b, capV (L.mem res.2.1) (cslotAddr dest) = .AsidPool p b) ∧
    (∀ y, IsSlot th' y → y ≠ cslotAddr ps → y ≠ cslotAddr dest → capV (L.mem res.2.1) y = capV (L.mem s0) y) ∧
    (DelInv th' (L.mem s0) → DelInv th' (L.mem res.2.1)) ∧
    (∃ (pp : U64) (rs : Nat) (idx : List Bool) (fi0 : U64), ps = (pp.bv, idx) ∧ th0 pp = some (.cnode rs) ∧
      idx.length = rs ∧ capAt (L.mem s0) (cslotAddr ps) = ok (.Untyped p fl4_abi.consts.bits.ASID_POOL fi0 false) ∧
      ¬ ∃ sl, σ.cdt sl = some ps) ∧
    ∃ (pd : U64) (rd : Nat) (idxd : List Bool), dest = (pd.bv, idxd) ∧ th0 pd = some (.cnode rd) ∧
      idxd.length = rd ∧ capAt (L.mem s0) (cslotAddr dest) = ok .Null

/-- The post of `MakePool`'s perform without the restart (`mp_perform_relB`). -/
def MpPostB {A : Type} (P L4 L3 L2 L1 : Set U64) (SR : S → A → Fl4Spec.State Unit → Prop)
    (th0 : TypedHeap) (k0 : U64)
    (m0 : U64 → U64) (G0 : MdbGhost) (s0 : S) (rc : capability.Cap) (σ : Fl4Spec.State Unit) (p : U64)
    (dest ps : Fl4Spec.CslotPtr) (base : Fl4Spec.Asid)
    (res : core.result.Result Unit error.Exc × S × A) : Prop :=
  ∃ σ' th' G', ((), σ') ∈ ((Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv dest ps base)) σ).1 ∧
    ¬ ((Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv dest ps base)) σ).2 ∧
    Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
    MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
    UtInv (L.mem res.2.1) G' ∧ VsRel (insert p P) (L.mem res.2.1) (L.ksb res.2.1) σ' ∧
    PtRel L4 L3 L2 L1 (L.mem res.2.1) σ' ∧ SR res.2.1 res.2.2 σ' ∧ FinInv th' (L.mem res.2.1) σ' G' ∧
    Vs.FrameInv (L.mem res.2.1) G' ∧
    (∀ P' L4' L3' L2' L1' : Set U64, Vs.VsCapsIn P' L4' L3' L2' L1' m0 G0 →
      Vs.VsCapsIn (insert p P') L4' L3' L2' L1' (L.mem res.2.1) G') ∧
    MdbStep m0 G0 (L.mem res.2.1) G' ∧
    (∀ ksb : U64, Vs.VsMdbInv ksb m0 G0 → Vs.VsMdbInv ksb (L.mem res.2.1) G') ∧
    σ'.curThread = σ.curThread ∧
    /- what the joint placement invariant needs of the step (`MpPlacedHyp`) -/
    th' = restrictTh th0 p.val (p.val + 4096) ∧ L.ksb res.2.1 = k0 ∧
    (∀ (q : U64) y n, σ'.kheap q.bv = some (.schedContext y n) → ∃ y0, σ.kheap q.bv = some (.schedContext y0 n)) ∧
    MpRegion th0 G0 P L4 L3 L2 L1 k0 p ∧
    (∃ x fi, x ∈ G0.chains.flatten ∧ capV m0 x = .Untyped p fl4_abi.consts.bits.ASID_POOL fi false ∧
      ∀ y, ¬ Mdb.Desc G0.par y x) ∧
    (∀ L4' : Set U64, Vs.PoolsIn P L4' m0 → Vs.PoolsIn (insert p P) L4' (L.mem res.2.1)) ∧
    MpMidB (L := L) th0 s0 rc σ p dest ps σ' th' res

set_option maxHeartbeats 4000000 in
/-- **`MakePool`'s perform without the restart refines l4v**: `mp_perform_rel`
from the state itself (after the restart), against the spec's
`perform_asid_control_invocation` from `σ` (`MpPostB`). -/
theorem mp_perform_relB {A : Type} {th : TypedHeap} {P L4 L3 L2 L1 : Set U64}
    {SR : S → A → Fl4Spec.State Unit → Prop} {RegOK : S → Fl4Spec.State Unit → U64 → Prop}
    (hH : VsMpHyps st A th P L4 L3 L2 L1 SR RegOK)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hPl : Placed th) (hSt : StateRel th (L.mem s) σ) (hSV : SlotsValid th (L.mem s))
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (hR : VsRel P (L.mem s) (L.ksb s) σ) (hPt : PtRel L4 L3 L2 L1 (L.mem s) σ)
    (hS : SR s a σ) (hVP : VsPlaced P (L.ksb s)) (hPP : PtPlaced L4 L3 L2 L1)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} (hsb : sb = fl4_abi.consts.bits.ASID_POOL)
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hnch : ¬ ∃ sl, σ.cdt sl = some (pp.bv, idx))
    {pd : U64} {rd : Nat} (hpd : th pd = some (.cnode rd)) {idxd : List Bool} (hidxd : idxd.length = rd)
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null)
    {i base : U64} (hi : i.val < 2048) (hbase : base.val = i.val * 512)
    (hRg : MpRegion th G P L4 L3 L2 L1 (L.ksb s) p) (hRO : RegOK s σ p)
    (hVO : ∀ b, VsWrite P (L.ksb s) b → OutsideObjects th b)
    (hPO : ∀ b, PtWAll L4 L3 L2 L1 b → OutsideObjects th b)
    (hPV : ∀ b, PtWAll L4 L3 L2 L1 b → ¬ VsWrite P (L.ksb s) b) (hFI : FinInv th (L.mem s) σ G)
    (hFR : Vs.FrameInv (L.mem s) G) {rc : capability.Cap} :
    (do
      let i1 ← lift (sb &&& 63#u64)
      let i2 ← 1#u64 <<< i1
      let s2 ← obj.Slot.set_cap st (cslotAddr (pp.bv, idx)) s (capability.Cap.Untyped p sb i2 false)
      let s3 ← st.clear_free s2 p 4096#u64
      let s4 ← cdt.insert st s3 (capability.Cap.AsidPool p base) (cslotAddr (pp.bv, idx)) (cslotAddr (pd.bv, idxd))
      let s5 ← vspace.set_asid_table st s4 i p
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a)) ⦃ res =>
      res.1 = .Ok () ∧ res.2.2 = a ∧ MpPostB (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G s rc σ p (pd.bv, idxd) (pp.bv, idx) base.bv res ⦄ := by
  obtain ⟨hpal, hpfit, hp0, hN, hns, hcn, hPo, hLo, hTo⟩ := hRg
  set x := cslotAddr (pp.bv, idx) with hxdef
  set val := cslotAddr (pd.bv, idxd) with hvaldef
  have hsbv : sb.val = 12 := by rw [hsb]; unfold fl4_abi.consts.bits.ASID_POOL; rfl
  have h2sb : 2 ^ sb.val = 4096 := by rw [hsbv]; rfl
  set th' := restrictTh th p.val (p.val + 2 ^ sb.val) with hth'
  have hP' : Placed th' := hPl.restrict
  have hN' : NoStraddle th p.val (p.val + 2 ^ sb.val) := by rw [h2sb]; exact hN
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hAd : AbsSlot th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hidxd] using hpd)⟩
  have hxs : IsSlot th x := hAs.isSlot
  have hvs : IsSlot th val := hAd.isSlot
  have hpp' : th' pp = some (.cnode rs) := by
    rw [hth', restrictTh_out (by rw [h2sb]; exact hcn pp rs hpp)]; exact hpp
  have hpd' : th' pd = some (.cnode rd) := by
    rw [hth', restrictTh_out (by rw [h2sb]; exact hcn pd rd hpd)]; exact hpd
  have hAs' : AbsSlot th' (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp')⟩
  have hAd' : AbsSlot th' (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hidxd] using hpd')⟩
  have hxs' : IsSlot th' x := hAs'.isSlot
  have hvs' : IsSlot th' val := hAd'.isSlot
  have hxv : x ≠ val := by
    intro e; rw [e, hdst] at hcap; cases eq_of_ok_eq hcap
  -- no restart: the body starts at the state itself
  have hKT1 : KTyped th σ := hFI.kt
  have hSS : SlotsSame th (L.mem s) (L.mem s) := SlotsSame.refl _ _
  -- the free index
  have hl : (lift (sb &&& 63#u64) : Result U64) = ok sb := by subst hsb; unfold fl4_abi.consts.bits.ASID_POOL; rfl
  have hsh : (1#u64 <<< sb : Result U64) = ok 4096#u64 := by subst hsb; unfold fl4_abi.consts.bits.ASID_POOL; rfl
  rw [hl]; simp only [bind_ok]; rw [hsh]; simp only [bind_ok]
  -- the region and the spec's state without it
  have hpfit' : p.val + 2 ^ sb.val ≤ 2 ^ 64 := by rw [h2sb]; exact hpfit
  have hreg : ∀ q : U64, q.bv ∈ Fl4Proofs.P3.regionSet p.bv 12 ↔ p.val ≤ q.val ∧ q.val < p.val + 4096 :=
    fun q => regionSet_iff p q 12 (by decide) hpfit
  have hxm : x ∈ G.chains.flatten := (hM.members x).2 ⟨hxs, _, hcap, by simp⟩
  have hnd : ∀ y, ¬ Mdb.Desc G.par y x := nodesc_of_cdt hPl hC hAs hnch
  have hcx1 : capV (L.mem s) x = .Untyped p sb fi false := capV_of_capAt hcap
  have hdel_rel : ∀ τd : Fl4Spec.State Unit, KSame (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ) τd →
      ResetRel th' G x p sb false (L.mem s) τd fi := by
    intro τd hD
    obtain ⟨r1, r2, r3, r4⟩ := detype_rel (σ := σ) (σd := τd) hSt hSV hPl hM hC hI hU hxm hcx1 hnd hN'
      (by rw [h2sb]; exact hns) (fun q hq => by
        rw [hD.1]; simp only [Fl4Spec.detype]
        split_ifs with h
        · exact absurd ((hreg q).1 h) (by rw [← h2sb]; exact hq)
        · rfl)
      (by rw [hD.2.1]; rfl) (by rw [hD.2.2.1]; rfl)
    exact ⟨r1, r2, r3, r4, hI, hU, hcx1⟩
  have hf' : (4096#u64 : U64).val ≤ 2 ^ sb.val := by rw [h2sb]; decide
  have hset := fun τd hD => reset_set_step (L := L) hPl hpp' hidx (hdel_rel τd hD) hnd 4096#u64 hf'
  obtain ⟨s2, hs2, -⟩ := spec_exists (hset _ (KSame.refl _))
  rw [hs2]; simp only [bind_ok]
  have hset2 : ∀ τd, KSame (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ) τd → ∃ cs,
      τd.kheap pp.bv = some (.cnode rs cs) ∧ Fl4Spec.wellFormedCnodeN rs cs ∧
      ResetRel th' G x p sb false (L.mem s2)
        (setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv sb.val (4096#u64 : U64).val)) 4096#u64 ∧
      (∀ w : U64, P1.Aligned w → w.val ≠ x.val → w.val ≠ x.val + 8 → L.mem s2 w = L.mem s w) ∧
      (∀ y, IsSlot th' y → y ≠ x → capV (L.mem s2) y = capV (L.mem s) y) ∧
      LinksKeep th' (L.mem s) (L.mem s2) := by
    intro τd hD
    have := hset τd hD
    rw [hs2, WP.spec_ok] at this
    obtain ⟨cs, h1, h2, h3, h4, h5, h6⟩ := this
    exact ⟨cs, h1, h2, h3, h4, h5, h6⟩
  obtain ⟨cs0, -, -, RR2, hfr2, hco2, hLK2⟩ := hset2 _ (KSame.refl _)
  -- the zeroing
  rw [L.clear_free_eq]; simp only [bind_ok]
  set s3 := L.zr s2 p 4096#u64 with hs3
  have hpA : P1.Aligned p := by unfold P1.Aligned; omega
  have hzero : ∀ τ f, ResetRel th' G x p sb false (L.mem s2) τ f → ResetRel th' G x p sb false (L.mem s3) τ f ∧
      ∀ w : U64, P1.Aligned w → L.mem s3 w = if p.val ≤ w.val ∧ w.val < p.val + 4096 then 0#u64 else L.mem s2 w :=
    fun τ f h => reset_zero_step (L := L) hPl hN' h hxs' p 4096#u64 hpA (by decide) le_rfl
      (by rw [h2sb]; rfl) hpfit'
  obtain ⟨RR3, hz3⟩ := hzero _ _ RR2
  have hSS3 : SlotsSame th' (L.mem s2) (L.mem s3) :=
    slotsSame_out hP' (fun b hb => hb.restrict_words hPl hN') (fun w hw ho => by
      rw [hz3 w hw, if_neg (by rw [h2sb] at ho; omega)])
  -- the insertion
  have he0 : EncWf (capability.Cap.Untyped p sb fi false) := by rw [capAt_words] at hcap; exact decode_encWf hcap
  have heA : EncWf (capability.Cap.AsidPool p base) := he0.1
  have hsrc3 : capAt (L.mem s3) x = ok (.Untyped p sb 4096#u64 false) := by rw [capAt_capV, RR3.cap]
  have hdst3 : capAt (L.mem s3) val = ok .Null := by
    rw [capAt_capV, hSS3.capV hvs', hco2 val hvs' (Ne.symm hxv), ← capAt_capV, hdst]
  have hnx : nextOf (L.mem s3) x = 0#u64 ∨
      (IsSlot th' (nextOf (L.mem s3) x) ∧ nextOf (L.mem s3) x ≠ val ∧ nextOf (L.mem s3) x ≠ x) := by
    have hvm : val ∉ G.chains.flatten := by
      intro h; obtain ⟨-, c0, h0, hn⟩ := (RR3.M.members val).1 h
      rw [hdst3] at h0; exact hn (eq_of_ok_eq h0).symm
    rcases RR3.M.next_mem hxm with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨((RR3.M.members _).1 h1).1, fun e => hvm (e ▸ h1), h2⟩
  have hnx' : nextOf (L.mem s3) x = 0#u64 ∨ IsSlot th' (nextOf (L.mem s3) x) := by
    rcases hnx with h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hvm0 : val ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (RR3.M.members val).1 h
    rw [hdst3] at h0; exact hn (eq_of_ok_eq h0).symm
  obtain ⟨s4, hs4, hdi4, hW4, hF4, hF2⟩ := spec_exists (WP.spec_and
    (insert_delinv_imp (L := L) hP' s3 G RR3.M hxm hvs' hvm0 hsrc3 (.AsidPool p base) heA (by simp) rfl) <| WP.spec_and
    (insert_mem (L := L) hP' s3 (.AsidPool p base) x val hxs' hvs' hxv _ hsrc3 hnx)
    (WP.spec_and (insert_frame (L := L) hP' s3 (.AsidPool p base) x val hxs' hvs' _ hsrc3 hnx')
      (insert_frame2 (L := L) hP' s3 (.AsidPool p base) x val hxs' hvs' _ hsrc3 hnx')))
  rw [hs4]; simp only [bind_ok]
  refine WP.spec_bind (set_asid_table_spec s4 i p) ?_
  rintro s5 rfl
  refine (WP.spec_ok _).2 ⟨rfl, rfl, ?_⟩
  show MpPostB (L := L) P L4 L3 L2 L1 SR th (L.ksb s) (L.mem s) G s rc σ p (pd.bv, idxd) (pp.bv, idx) base.bv
    (.Ok (), L.wr s4 (atA (L.ksb s4) (i &&& 2047#u64)) p, a)
  -- FL4: the kernel-state base and the words
  have hksb2 : L.ksb s2 = L.ksb s := by
    have := set_cap_spec (L := L) x s (.Untyped p sb 4096#u64 false)
    rw [hs2, WP.spec_ok] at this; rw [this]; simp
  have hksb4 : L.ksb s4 = L.ksb s := by rw [hF4.1, hs3, L.ksb_zr, hksb2]
  set K := L.ksb s with hK
  rw [hksb4, and2047_of_lt hi]
  set s5 := L.wr s4 (atA K i) p with hs5
  have hksb5 : L.ksb s5 = K := by rw [hs5, L.ksb_wr, hksb4]
  have hAt : P1.Aligned (atA K i) := by
    show _ % 8 = 0; rw [atA_val hVP.ksb_fit hi]; have := hVP.ksb_al; omega
  have hAtv := atA_val hVP.ksb_fit hi
  have hAtO : OutsideObjects th (atA K i) := hVO _ (Or.inl ⟨i, hi, rfl⟩)
  have hslo : ∀ b, OutsideObjects th b → ∀ y, IsSlot th y → ¬ (y.val ≤ b.val ∧ b.val < y.val + 32) := by
    intro b hb y hy hin
    obtain ⟨q, k, hq, h1, h2, -⟩ := slot_in_object hPl hy
    exact hb.2 q k hq ⟨by omega, by omega⟩
  have hO' : ∀ b, OutsideObjects th b → OutsideObjects th' b :=
    fun b hb => ⟨hb.1, fun q k h => hb.2 q k (restrictTh_some h).1⟩
  have hmem41 : ∀ b, P1.Aligned b → OutsideObjects th b → ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) →
      L.mem s4 b = L.mem s b := by
    intro b hb ho hr
    have h1 := hslo b ho x hxs
    rw [hF4.2 b (hO' b ho), hz3 b hb, if_neg hr, hfr2 b hb (by omega) (by omega)]
  have hmemR : ∀ b, P1.Aligned b → p.val ≤ b.val → b.val < p.val + 4096 → L.mem s4 b = 0#u64 := by
    intro b hb h1 h2
    have hob : OutsideObjects th' b := ⟨hb, fun q k hq hin => by
      have := RegionFree.restrict hN' q k hq
      rw [h2sb] at this; omega⟩
    rw [hF4.2 b hob, hz3 b hb, if_pos ⟨h1, h2⟩]
  have hm54 : ∀ b, P1.Aligned b → b.val ≠ (atA K i).val → L.mem s5 b = L.mem s4 b :=
    fun b hb hne => L.mem_wr_ne hAt hb (Ne.symm hne)
  have hSS5 : SlotsSame th' (L.mem s4) (L.mem s5) :=
    slotsSame_wr hP' s4 p hAt (fun y hy => hslo _ hAtO y hy.of_restrict)
  have hvm : val ∉ G.chains.flatten := by
    intro h; obtain ⟨-, c0, h0, hn⟩ := (RR3.M.members val).1 h
    rw [hdst3] at h0; exact hn (eq_of_ok_eq h0).symm
  have hbv : base.bv.toNat = i.bv.toNat * 512 := hbase
  have hlow : Fl4Spec.asidLowBitsOf base.bv = 0 := base_low hbv
  have hhigh : Fl4Spec.asidHighBitsOf base.bv = Fl4Spec.ucast 11 i.bv := base_high hi hbv
  have hpq : ∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096) → q.bv ≠ p.bv := by
    intro q hq e
    have : q.val = p.val := congrArg BitVec.toNat e
    omega
  have hp0bv : Fl4Spec.ptrAdd p.bv (0 * 2 ^ 12) = p.bv := by simp [Fl4Spec.ptrAdd]
  set A : Fl4Spec.Cap := .archObjectCap (.asidPoolCap p.bv base.bv) with hA
  set G' := insG G x val true with hG'
  -- the spec, after `delete_objects`
  have key : ∀ τd : Fl4Spec.State Unit, KSame (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ) τd →
      ∃ τf, mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv τd = ({((), τf)}, False) ∧
        StateRel th' (L.mem s5) τf ∧ SlotsValid th' (L.mem s5) ∧ MdbLinks th' (L.mem s4) G' ∧
        MdbLinks th' (L.mem s5) G' ∧ CdtRel th' (L.mem s5) τf G' ∧ (∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096) →
          ∀ ao, σ.kheap q.bv = some (.archObj ao) → τf.kheap q.bv = σ.kheap q.bv) ∧
        τf.kheap p.bv = some (.archObj (.asidPool fun _ => none)) ∧
        τf.archState.x64AsidTable =
          Function.update σ.archState.x64AsidTable (Fl4Spec.ucast 11 i.bv) (some p.bv) ∧
        OStep (fun _ => False) τd τf ∧ τf.machineState = τd.machineState ∧
        τf.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3 ∧ KTyped th' τf ∧
        (∀ o, o ≠ p.bv → τf.kheap o = σ.kheap o ∨ (o ∈ Fl4Proofs.P3.regionSet p.bv 12 ∧ τf.kheap o = none) ∨
          ∃ r cs cs', σ.kheap o = some (.cnode r cs) ∧ τf.kheap o = some (.cnode r cs')) ∧
        τf.cdt = Function.update σ.cdt (pd.bv, idxd) (some (pp.bv, idx)) ∧
        (∀ sl, sl ≠ (pd.bv, idxd) → τf.isOriginalCap sl = σ.isOriginalCap sl) := by
    intro τd hD
    obtain ⟨cs, hkpp, hwf, RR2τ, -, -, -⟩ := hset2 τd hD
    have hτs : setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv sb.val (4096#u64 : U64).val) =
        setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv 12 4096) := by rw [hsbv]; rfl
    rw [hτs] at RR2τ
    have RR3τ := (hzero _ _ RR2τ).1
    set τs := setCnodeSlot τd pp.bv rs cs idx (.untypedCap false p.bv 12 4096) with hτsdef
    set τr := mpRegion τd pp.bv rs cs idx p.bv with hτr
    have hgc : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) τd = ({(.untypedCap false p.bv 12 fi.val, τd)}, False) := by
      obtain ⟨c, a', hc, hca, hg⟩ := (hdel_rel τd hD).R.slot_cap (s := s) (sl := (pp.bv, idx)) (p := pp) rfl
        (by simpa [hidx] using hpp')
      rw [hcap] at hc; have := eq_of_ok_eq hc; subst this
      rw [hg, hca.abs]; simp [absCap, hsbv]
    have hkr : ∀ q : U64, ¬ (p.val ≤ q.val ∧ q.val < p.val + 4096) → τr.kheap q.bv = τs.kheap q.bv := by
      intro q hq
      simp only [hτr, mpRegion, regionHeap]
      rw [foldr_update_apply, if_neg]
      simp only [regionPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton]
      rw [hp0bv]; exact hpq q hq
    have hR3r : StateRel th' (L.mem s3) τr := StateRel.of_agree RR3τ.R (fun q kd hq _ => hkr q (by
      have := (restrictTh_some hq).2; rw [h2sb] at this; exact this))
    have hC3r : CdtRel th' (L.mem s3) τr G := CdtRel.of_cdt RR3τ.C rfl rfl
    -- `cap_insert`
    obtain ⟨cS, aS, hcS, hcaS, hgs⟩ := hR3r.slot_cap (s := s3) (sl := (pp.bv, idx)) (p := pp) rfl
      (by simpa [hidx] using hpp')
    rw [hsrc3] at hcS; have := eq_of_ok_eq hcS; subst this
    obtain ⟨cD, aD, hcD, hcaD, hgd⟩ := hR3r.slot_cap (s := s3) (sl := (pd.bv, idxd)) (p := pd) rfl
      (by simpa [hidxd] using hpd')
    rw [hdst3] at hcD; have := eq_of_ok_eq hcD; subst this
    rw [hcaS.abs] at hgs; rw [hcaD.abs] at hgd
    obtain ⟨csd, hkpd, hwfd, -⟩ := hR3r.cnode pd rd hpd'
    have hsetd := setCap_cnode (Z := Unit) A hkpd hwfd hidxd
    have hci := capInsert_eq hgs hgd (setUntyped_skip (by simp [Fl4Spec.isUntypedCap, hA])) hsetd rfl rfl
    set τi := capInsertState τr (setCnodeSlot τr pd.bv rd csd idxd A) A
      (absCap (.Untyped p sb 4096#u64 false)) (pp.bv, idx) (pd.bv, idxd) with hτi
    have hperf := mpPerf_eq hkpp hwf hidx hgc hci hlow
    have hins := insert_refines' (L := L) th' s3 τr G hR3r RR3τ.V hP' RR3τ.M hC3r hpp' hpd' hidx hidxd hsrc3
      (by simp) hdst3 (.AsidPool p base) A ⟨trivial, rfl⟩ trivial heA (by simp) trivial
    rw [hs4, WP.spec_ok] at hins
    obtain ⟨τi', G'', hci', hR4, hV4, hM4, hC4, hG''⟩ := hins (fun _ => hnd)
    have e1 : τi' = τi := by
      rw [hci] at hci'
      have := congrArg Prod.fst hci'
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    rw [e1] at hR4 hC4
    have hio : τr.isOriginalCap (pp.bv, idx) = true := by
      rw [hC3r.orig (pp.bv, idx) hAs']; exact RR3.I.utrev x hxm (by rw [RR3.cap]; rfl)
    have hb : decide (Fl4Spec.shouldBeParentOf (absCap (.Untyped p sb 4096#u64 false))
        (τr.isOriginalCap (pp.bv, idx)) A
        (decide (Fl4Spec.isCapRevocable A (absCap (.Untyped p sb 4096#u64 false))))) = true := by
      rw [hio]; simp only [absCap, hsbv]
      exact decide_eq_true (sbp_pool hpfit base.bv _ _)
    rw [hb] at hG''
    subst hG''
    have hpdq : ∀ q : U64, ∀ ao, σ.kheap q.bv = some (.archObj ao) → q.bv ≠ pd.bv ∧ q.bv ≠ pp.bv := by
      intro q ao hq
      obtain ⟨c1, hk1, -⟩ := hSt.cnode pd rd hpd
      obtain ⟨c2, hk2, -⟩ := hSt.cnode pp rs hpp
      exact ⟨fun e => (by rw [e, hk1] at hq; cases hq), fun e => (by rw [e, hk2] at hq; cases hq)⟩
    have hpd_out : ¬ (p.val ≤ pd.val ∧ pd.val < p.val + 4096) := hcn pd rd hpd
    have hpp_out : ¬ (p.val ≤ pp.val ∧ pp.val < p.val + 4096) := hcn pp rs hpp
    have hpdp : p.bv ≠ pd.bv := fun e => hpq pd hpd_out e.symm
    have hppp : p.bv ≠ pp.bv := fun e => hpq pp hpp_out e.symm
    refine ⟨mpTable τi p.bv base.bv, hperf, (hR4.of_kheap (σ' := mpTable τi p.bv base.bv) rfl).of_caps (fun y hy => hSS5.capAt hy),
      Fl4Proofs.P3.SlotsValid.of_caps hV4 (fun y hy => hSS5.capAt hy), hM4, hM4.of_same hSS5,
      hC4.of_same hSS5 rfl rfl, fun q hq ao hqa => ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hpdq q ao hqa
      show (Function.update τr.kheap pd.bv _) q.bv = _
      rw [Function.update_of_ne h1, hkr q hq]
      show (Function.update τd.kheap pp.bv _) q.bv = _
      rw [Function.update_of_ne h2, hD.1]
      simp only [Fl4Spec.detype]
      split_ifs with h
      · exact absurd ((hreg q).1 h) hq
      · rfl
    · show (Function.update τr.kheap pd.bv _) p.bv = _
      rw [Function.update_of_ne hpdp]
      simp only [hτr, mpRegion, regionHeap]
      rw [foldr_update_apply, if_pos]
      simp only [regionPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton]
      exact hp0bv.symm
    · show Function.update τi.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv) (some p.bv) = _
      rw [hhigh]
      have : τi.archState = σ.archState := hD.2.2.2
      rw [this]
    · -- the other subsystems' state: only CNodes, the pool's cell, the CDT and the table change
      have hpd0 : τd.kheap p.bv = none := by
        rw [hD.1]; simp only [Fl4Spec.detype]
        rw [if_pos ((hreg p).2 ⟨le_refl _, by omega⟩)]
      have h1 := OStep.cnode hkpp idx (.untypedCap false p.bv 12 4096)
      have hτr' : τr = updK τs p.bv (.archObj (.asidPool fun _ => none)) := by
        simp only [hτr, mpRegion, regionHeap, regionPtrs, List.range_one, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, hp0bv]; rfl
      have h2 : OStep (fun _ => False) τs τr := by
        rw [hτr']
        refine OStep.arch (Or.inl ?_) _
        show (Function.update τd.kheap pp.bv _) p.bv = none
        rw [Function.update_of_ne hppp, hpd0]
      have h3 := OStep.cnode hkpd idxd A
      have h4 : OStep (fun _ => False) (setCnodeSlot τr pd.bv rd csd idxd A) τi :=
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ hq => absurd rfl hq⟩
      have h5 := OStep.table (σ := τi) (Function.update τi.archState.x64AsidTable (Fl4Spec.asidHighBitsOf base.bv)
        (some p.bv))
      exact ((((h1.trans h2).trans h3).trans h4).trans h5).mono (fun q h => by simp at h)
    · show τi.archState.x64CurrentCr3 = _
      rw [show τi.archState = σ.archState from hD.2.2.2]
    · -- the spec's CNodes and TCBs are the restricted heap's
      have hτr' : τr = updK τs p.bv (.archObj (.asidPool fun _ => none)) := by
        simp only [hτr, mpRegion, regionHeap, regionPtrs, List.range_one, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, hp0bv]; rfl
      have hkh : ∀ o, (mpTable τi p.bv base.bv).kheap o = Function.update (Function.update
          (Function.update τd.kheap pp.bv (some (.cnode rs (Function.update cs idx
            (some (.untypedCap false p.bv 12 4096)))))) p.bv (some (.archObj (.asidPool fun _ => none)))) pd.bv
          (some (.cnode rd (Function.update csd idxd (some A)))) o := by
        intro o; show (Function.update τr.kheap pd.bv _) o = _; rw [hτr']; rfl
      have hout : ∀ o : Fl4Spec.ObjRef, o ∉ Fl4Proofs.P3.regionSet p.bv 12 → th' ⟨o⟩ = th ⟨o⟩ := by
        intro o ho
        rw [hth', restrictTh_out]
        intro hin; apply ho; rw [show o = (⟨o⟩ : U64).bv from rfl, hreg]; rw [h2sb] at hin; exact hin
      have hd0 : ∀ o, τd.kheap o = (Fl4Spec.detype (Fl4Proofs.P3.regionSet p.bv 12) σ).kheap o := by
        intro o; rw [hD.1]
      intro o
      refine ⟨fun r' cs' hc hw => ?_, fun t ht => ?_⟩ <;> rw [hkh] at *
      · by_cases e1 : o = pd.bv
        · subst e1; rw [Function.update_self] at hc; cases hc; exact hpd'
        rw [Function.update_of_ne e1] at hc
        by_cases e2 : o = p.bv
        · subst e2; rw [Function.update_self] at hc; cases hc
        rw [Function.update_of_ne e2] at hc
        by_cases e3 : o = pp.bv
        · subst e3; rw [Function.update_self] at hc; cases hc; exact hpp'
        rw [Function.update_of_ne e3, hd0] at hc
        simp only [Fl4Spec.detype] at hc
        split_ifs at hc with h4
        rw [hout o h4]; exact (hKT1 o).1 r' cs' hc hw
      · by_cases e1 : o = pd.bv
        · subst e1; rw [Function.update_self] at ht; cases ht
        rw [Function.update_of_ne e1] at ht
        by_cases e2 : o = p.bv
        · subst e2; rw [Function.update_self] at ht; cases ht
        rw [Function.update_of_ne e2] at ht
        by_cases e3 : o = pp.bv
        · subst e3; rw [Function.update_self] at ht; cases ht
        rw [Function.update_of_ne e3, hd0] at ht
        simp only [Fl4Spec.detype] at ht
        split_ifs at ht with h4
        rw [hout o h4]; exact (hKT1 o).2 t ht
    · -- the heap: the pool's cell, the region's cells and two CNodes change
      have hτr' : τr = updK τs p.bv (.archObj (.asidPool fun _ => none)) := by
        simp only [hτr, mpRegion, regionHeap, regionPtrs, List.range_one, List.map_cons, List.map_nil,
          List.foldr_cons, List.foldr_nil, hp0bv]; rfl
      have hkh : ∀ o, (mpTable τi p.bv base.bv).kheap o = Function.update (Function.update
          (Function.update τd.kheap pp.bv (some (.cnode rs (Function.update cs idx
            (some (.untypedCap false p.bv 12 4096)))))) p.bv (some (.archObj (.asidPool fun _ => none)))) pd.bv
          (some (.cnode rd (Function.update csd idxd (some A)))) o := by
        intro o; show (Function.update τr.kheap pd.bv _) o = _; rw [hτr']; rfl
      intro o hop
      rw [hkh]
      obtain ⟨c1, hk1, -⟩ := hSt.cnode pd rd hpd
      obtain ⟨c2, hk2, -⟩ := hSt.cnode pp rs hpp
      by_cases e1 : o = pd.bv
      · subst e1; rw [Function.update_self]
        exact Or.inr (Or.inr ⟨rd, c1, _, hk1, rfl⟩)
      rw [Function.update_of_ne e1, Function.update_of_ne hop]
      by_cases e3 : o = pp.bv
      · subst e3; rw [Function.update_self]
        exact Or.inr (Or.inr ⟨rs, c2, _, hk2, rfl⟩)
      rw [Function.update_of_ne e3, hD.1]
      simp only [Fl4Spec.detype]
      split_ifs with h4
      · exact Or.inr (Or.inl ⟨h4, rfl⟩)
      · exact Or.inl rfl
    · -- the CDT
      show Function.update τr.cdt (pd.bv, idxd) (if _ = true then _ else _) = _
      rw [if_pos hb]
      have : τr.cdt = σ.cdt := hD.2.1
      rw [this]
    · -- the original bits
      intro sl hsl
      show Function.update τr.isOriginalCap (pd.bv, idxd) _ sl = _
      rw [Function.update_of_ne hsl]
      exact congrFun hD.2.2.1 sl
  -- the MDB invariants after the insertion
  have heU : EncWf (capability.Cap.Untyped p sb 4096#u64 false) := ⟨he0.1, he0.2⟩
  have hNc : Canonical (nextOf (L.mem s3) x) := by
    rcases hnx with h | ⟨h, -, -⟩
    · rw [h]; exact canonical_zero
    · exact h.canonical hP'
  have hbA : baseF (.AsidPool p base) = baseF (capV (L.mem s3) x) := by
    rw [RR3.cap]; unfold baseF; rw [ptrF_ap, ptrF_ut]
  have htA : topF (.AsidPool p base) = topF (capV (L.mem s3) x) := by
    rw [RR3.cap]; unfold topF; rw [ptrF_ap, ptrF_ut, sizeF_ap, sizeF_ut, hsb]
  obtain ⟨tx1, tx2⟩ := topF_ut p sb 4096#u64 false (by omega) hpfit'
  have hctx : InsACtx th' (L.mem s3) (L.mem s4) G x val p base :=
    { hM := RR3.M, hI := RR3.I, hsrc := hxm, hd := hvs', hdest := hvm
      hnext := fun y hy => hW4.nextOf' hP' hy hvs' hxv hNc
      hcap := fun y hy => by
        have h := hW4.capAt' hy heA heU hsrc3
        rw [capAt_capV] at h
        by_cases h1 : y = val
        · rw [if_pos h1] at h ⊢; exact eq_of_ok_eq h
        · rw [if_neg h1] at h ⊢
          by_cases h2 : y = x
          · rw [if_pos h2] at h; subst h2; rw [RR3.cap]; exact eq_of_ok_eq h
          · rw [if_neg h2, capAt_capV] at h; exact eq_of_ok_eq h
      hrev := fun y hy => by rw [hW4.revOf' hy hxv]; rfl
      hfb := fun y hy => by rw [InsWords.fbOf' hW4 hy hxv]; rfl
      hut := by rw [RR3.cap]; rfl
      hcr := by rw [hbA, htA, RR3.cap, tx1, tx2]; have := Nat.one_le_two_pow (n := sb.val); omega
      hcin := by unfold Within; rw [hbA, htA]; exact ⟨le_refl _, le_refl _⟩
      hreg := RR3.U.reg
      hno := fun y hy hp => by
        by_cases hyx : y = x
        · right; rw [hyx, RR3.cap]; exact ⟨rfl, le_refl _, le_refl _⟩
        · by_cases hdj : Disj (capV (L.mem s3) y) (capV (L.mem s3) x)
          · left; unfold Disj at hdj ⊢; rw [hbA, htA]; exact hdj
          · rcases RR3.U.drange x hxm p sb 4096#u64 false RR3.cap y hy hyx hp hdj with h | h
            · exact absurd h (hnd y)
            · right
              have h0 := RR3.I.desc y x h
              unfold isPM isPF at h0
              simp only [Bool.and_eq_true] at h0
              obtain ⟨⟨-, h2⟩, -⟩ := h0
              rw [RR3.cap] at h2
              have hU' := srB_to_ut h2
              rw [← RR3.cap] at h2
              exact ⟨hU', ((srB_ut_iff hU' _).1 h2).2.1⟩
      hdd := fun y hy => absurd hy (hnd y) }
  have hI4 : MdbInv (L.mem s4) G' := hctx.inv
  have hU4 : UtInv (L.mem s4) G' := utinv_pool RR3.M RR3.U hxm RR3.cap (by rw [h2sb]; rfl) hnd hvm hctx.cd
    hbA htA (fun y hy => hctx.cz hy)
  -- the spec run
  have hDel := deleteObjects_nsat (Z := Unit) (a := p.bv) (show p.val % 8 = 0 by omega) 12 σ
  have hrun : (Fl4Spec.performAsidControlInvocation (Z := Unit) (.makePool p.bv (pd.bv, idxd) (pp.bv, idx) base.bv)) σ =
      (Fl4Spec.deleteObjects p.bv 12 >>= fun _ => mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) σ := rfl
  have hall : NSat (Fl4Spec.deleteObjects p.bv 12 >>= fun _ => mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) σ
      (fun _ => True) :=
    nsat_bind (hDel.1.mono fun y hy => by
      obtain ⟨τf, he, -⟩ := key y.2 ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2⟩
      exact nsat_det he trivial)
  obtain ⟨y, hy, hPy⟩ := hDel.2
  obtain ⟨τf, he, hR5, hV5, hM4, hM5, hC5, hkq, hkp, htab, hOf, hmsf, hcrf, hKTf, hkhf, hcdtf, horf⟩ := key y.2 ⟨hPy.1, hPy.2.1, hPy.2.2.1, hPy.2.2.2⟩
  have hmem : ((), τf) ∈ ((Fl4Spec.deleteObjects p.bv 12 >>= fun _ =>
      mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) σ).1 := by
    obtain ⟨r, hr, hre⟩ := nhas_bind (m := Fl4Spec.deleteObjects (Z := Unit) p.bv 12)
      (f := fun _ => mpPerf p.bv (pd.bv, idxd) (pp.bv, idx) base.bv) (s := σ) (P := fun r => r = ((), τf))
      ⟨y, hy, nhas_det he rfl⟩
    rw [← hre]; exact hr
  -- the ASID and page-table relations
  have hVout : ∀ b, VsWrite P K b → ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) := by
    rintro b (⟨hi', hh, rfl⟩ | ⟨q, hq, lo, hl, rfl⟩) hin
    · rw [atA_val hVP.ksb_fit hh] at hin; omega
    · obtain ⟨-, qf⟩ := hVP.pal q hq
      rw [peA_val qf hl] at hin; have := hPo q hq; omega
  have hR1' : VsRel P (L.mem s) K σ := hR
  have hVs4 : VsRel P (L.mem s4) K σ := VsRel.frame hR1'
    (fun b hb => hmem41 b (VsWrite.aligned hVP hb) (hVO b hb) (hVout b hb)) rfl (fun _ _ => rfl)
  have hpP : p ∉ P := fun h => by have := hPo p h; omega
  have hVP' : VsPlaced (insert p P) K := by
    refine ⟨hVP.ksb_al, hVP.ksb_fit, fun q hq => ?_, fun q hq => ?_⟩
    · rcases hq with rfl | hq
      · exact ⟨hpal, hpfit⟩
      · exact hVP.pal q hq
    · rcases hq with rfl | hq
      · exact hTo
      · exact hVP.ptab q hq
  have hpne : ∀ b : U64, b ≠ atA K i → b.val ≠ (atA K i).val := fun b h e => h (UScalar.eq_of_val_eq e)
  have hz5 : ∀ lo : U64, lo.val < 512 → L.mem s5 (peA p lo) = 0#u64 := fun lo hl => by
      have hv := peA_val hpfit hl
      have hal : P1.Aligned (peA p lo) := by show _ % 8 = 0; rw [hv]; omega
      rw [hm54 _ hal (by rw [hv, hAtv]; omega), hmemR _ hal (by omega) (by omega)]
  have hVs5 : VsRel (insert p P) (L.mem s5) K τf := VsRel.add_pool hVP' hVs4 hpP hi hp0
    (fun b hb hne _ => hm54 b hb (hpne b hne))
    hz5
    (L.mem_wr_same hAt) hkp (fun q hq => by
      obtain ⟨f, hf, -⟩ := hVs4.pool q hq
      have := hPo q hq
      rw [hkq q (by omega) _ hf]) htab
  have hPt5 : PtRel L4 L3 L2 L1 (L.mem s5) τf := PtRel.frame hPt
    (fun b hb => by
      have hal := PtWAll.aligned hPP hb
      have hnv : b ≠ atA K i := fun e => hPV b hb (e ▸ Or.inl ⟨i, hi, rfl⟩)
      rw [hm54 b hal (hpne b hnv)]
      refine hmem41 b hal (hPO b hb) ?_
      obtain ⟨q, hq, j, hj, rfl⟩ := hb
      have hqa := hPP q hq
      rw [peA_val (tbl_fit hqa) hj]; have := hLo q hq; omega)
    (fun q hq => by
      obtain ⟨ao, hao⟩ := hPt.arch hq
      have hqa := hPP q hq
      have := hLo q hq
      exact hkq q (by omega) ao hao)
  -- the rest of the state relation
  have hcpu5 : L.cpu s5 = L.cpu s := by
    have h2 : L.cpu s2 = L.cpu s := by
      have := set_cap_spec (L := L) x s (.Untyped p sb 4096#u64 false)
      rw [hs2, WP.spec_ok] at this; rw [this]; simp
    rw [hs5, L.cpu_wr, hF2.2.1, hs3, L.cpu_zr, h2]
  have hMp : MpStep p σ τf := by
    obtain ⟨ms, hy2, hum⟩ := deleteObjects_mem (by decide) (by decide) (show p.bv.toNat % 8 = 0 by
      show p.val % 8 = 0; omega) (show p.bv.toNat + 2 ^ 12 ≤ 2 ^ 64 from hpfit) hy
    have hO1 : OStep (fun q => q ∈ Fl4Proofs.P3.regionSet p.bv 12) σ y.2 := by
      rw [hy2]
      refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun q hq => ?_⟩
      simp only [Fl4Spec.detype] at hq ⊢
      split_ifs at hq ⊢ with h
      · exact ⟨Or.inl h, Or.inl rfl⟩
      · exact absurd rfl hq
    refine ⟨(hO1.trans hOf).mono (fun q h => h.elim id False.elim), fun x hx => ?_, hcrf⟩
    rw [hmsf, hy2]
    exact hum x hx
  have hW5 : ∀ b, P1.Aligned b → ¬ MpW th p (L.ksb s) i b → L.mem s5 b = L.mem s b := (fun b hb hn => by
      have hr : ¬ (p.val ≤ b.val ∧ b.val < p.val + 4096) := fun h => hn (Or.inr (Or.inl h))
      have hnv : b ≠ atA K i := fun e => hn (Or.inr (Or.inr (by rw [e])))
      have hns : ¬ ∃ x' k, IsSlot th' x' ∧ Off k ∧ b = wordOf x' k :=
        fun ⟨x', k, hx', hk, e⟩ => hn (Or.inl ⟨x', k, hx'.of_restrict, hk, e⟩)
      rw [hm54 b hb (hpne b hnv), hF2.2.2 b hb hns, hz3 b hb, if_neg hr]
      refine hfr2 b hb (fun e => hn (Or.inl ⟨x, 0#u64, hxs, off0, ?_⟩)) (fun e => hn (Or.inl ⟨x, 8#u64, hxs, off8, ?_⟩))
      · rw [wordOf_zero]; exact UScalar.eq_of_val_eq e
      · apply UScalar.eq_of_val_eq; rw [e, wordOf_val (show x.val + (8#u64).val < 2 ^ 64 by
        have := hxs.fit hPl; simp; omega)]; rfl)
  have hSR5 : SR s5 a τf := hH.mpSR s s5 a σ τf p i hi hS hRO
    (by rw [hksb5]) hcpu5 hW5 hMp
  -- `DelInv`
  have hDI : DelInv th' (L.mem s) → DelInv th' (L.mem s5) := by
    intro D0
    have D1 := delInv_same_mp D0 (fun a ha => hSS a ha.of_restrict)
    have D2 : DelInv th' (L.mem s2) := DelInv.of_kept D1 id (fun y hy p0 zt n h => ⟨hy, by
        show capV _ y = _
        by_cases e : y = x
        · rw [e, RR2.cap] at h; cases h
        · rw [← hco2 y hy e]; exact h⟩) (fun _ _ _ _ hne _ _ _ _ _ _ _ _ => hne)
      (fun y hy h => by
        by_cases e : y = x
        · rw [e, RR2.cap] at h; cases h
        · obtain ⟨l1, l2⟩ := hLK2 y hy
          have := D1.nc y hy (by rw [← hco2 y hy e]; exact h)
          unfold prevOf nextOf at this ⊢; rw [l1, l2]; exact this)
    exact delInv_same_mp (hdi4 (delInv_same_mp D2 hSS3)) hSS5
  have hMid : MpMidB (L := L) th s rc σ p (pd.bv, idxd) (pp.bv, idx) τf th' ((.Ok () : core.result.Result Unit error.Exc), s5, a) := by
    refine ⟨i, hi, by show L.ksb s5 = L.ksb s; rw [hksb5],
      hcpu5, hW5, fun w hw h1 h2 => by
        rw [hm54 w hw (by rw [hAtv]; rcases hTo with e | e <;> omega), hmemR w hw h1 h2],
      L.mem_wr_same hAt, hMp, hkp, hkhf, hcdtf, horf, ?_, ⟨base, ?_⟩, ?_, hDI, ⟨pp, rs, idx, fi, rfl, hpp, hidx, by rw [← hsb]; exact hcap, hnch⟩,
      pd, rd, idxd, rfl, hpd, hidxd, hdst⟩
    · show capV (L.mem s5) x = _
      rw [hSS5.capV hxs', hctx.cz hxm, RR3.cap, hsb]
    · show capV (L.mem s5) val = _
      rw [hSS5.capV hvs', hctx.cd]
    · intro y hy h1 h2
      show capV (L.mem s5) y = _
      rw [hSS5.capV hy, hctx.hcap y hy, if_neg h2, hSS3.capV hy, hco2 y hy h1, hSS.capV hy.of_restrict]
  -- `FinInv`
  have hnd0 := hM.tree.nodup
  have F1 : FinM (L.mem s) G := hFI.fm.of_caps hnd0 (fun z hz => hSS.capV ((hM.members z).1 hz).1)
  have F2 : FinM (L.mem s2) G := F1.recap hnd0 x (by rw [RR2.cap, hcx1]; exact MdbLike.capSim ⟨rfl, rfl, rfl⟩)
    (fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne)
  have F3 : FinM (L.mem s3) G := F2.of_caps hnd0 (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
  have hfr4 : ∀ w ∈ G.chains.flatten,
      ¬ Ovl (absCap (capV (L.mem s4) val)) (absCap (capV (L.mem s4) w)) ∧
      (isFrame (capV (L.mem s4) val) = true → srB (capV (L.mem s4) val) (capV (L.mem s4) w) = false) ∧
      (isFrame (capV (L.mem s4) w) = true → srB (capV (L.mem s4) w) (capV (L.mem s4) val) = false) := by
    intro w hw
    have hov := not_ovl_pool (q := p) (b := base) (hctx.hreg w hw)
      (fun h => (hctx.hno w hw h).imp id And.left) hctx.hcr
    refine ⟨?_, ?_, ?_⟩
    · rw [hctx.cd, hctx.cz hw]; exact hov
    · intro h; rw [hctx.cd] at h; cases h
    · intro hf
      rw [hctx.cd]
      cases hs : srB (capV (L.mem s4) w) (.AsidPool p base)
      · rfl
      · exact absurd (srB_frame_frame hf hs) (by simp [isFrame])
  have F4 : FinM (L.mem s4) G' := F3.fresh_ins hxm hvm true hM4.tree.nodup (fun z hz => hctx.cz hz) hfr4
  have F5 : FinM (L.mem s5) G' := F4.of_caps hM4.tree.nodup (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  -- `FrameInv`
  have FR1 : Vs.FrameInv (L.mem s) G := hFR.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1)
  have FR2 : Vs.FrameInv (L.mem s2) G := FR1.recap x (by rw [RR2.cap, hcx1]; exact ⟨rfl, rfl, rfl⟩)
    (fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne)
  have FR3 : Vs.FrameInv (L.mem s3) G := FR2.of_caps (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
  have FR4 : Vs.FrameInv (L.mem s4) G' := FR3.insert_fresh hxm hvm true hctx.cd
    (by rw [hctx.cz hxm]; exact MdbLike.refl _) (fun z hz _ => hctx.cz hz) (fun _ _ _ _ _ _ h => by cases h)
    (fun y hy _ _ _ _ _ _ hc q h1 h2 => Vs.pool_out hc (hctx.hreg y hy)
      (fun h => (hctx.hno y hy h).imp id And.left) hctx.hcr q h1 h2)
  have FR5 : Vs.FrameInv (L.mem s5) G' := FR4.of_caps (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  have VC : ∀ P' L4' L3' L2' L1' : Set U64, Vs.VsCapsIn P' L4' L3' L2' L1' (L.mem s) G →
      Vs.VsCapsIn (insert p P') L4' L3' L2' L1' (L.mem s5) G' := fun P' L4' L3' L2' L1' hVC => by
    have V1 := hVC.of_caps (fun z hz => hSS.capV ((hM.members z).1 hz).1)
    have V2 := V1.recap x (by rw [RR2.cap]; trivial) (fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne)
    have V3 := V2.of_caps (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
    have V4 := V3.insert_fresh (P' := insert p P') (L4' := L4') (L3' := L3') (L2' := L2') (L1' := L1')
      (Set.subset_insert _ _) subset_rfl subset_rfl subset_rfl subset_rfl hxm true
      (by rw [hctx.cd]; exact Vs.vcap_pool hbase hi hp0) (by rw [hctx.cz hxm]; exact id) (fun z hz _ _ => hctx.cz hz)
    exact V4.of_caps (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  -- the MDB step and the VSpace MDB invariant
  have hrv2 : ∀ z ∈ G.chains.flatten, revOf (L.mem s2) z = revOf (L.mem s) z := fun z hz => by
    have hzs := ((hM.members z).1 hz).1
    have a1 := hzs.align hPl; have f1 := hzs.fit hPl; have a2 := hxs.align hPl; have f2 := hxs.fit hPl
    have hv : (wordOf z 24#u64).val = z.val + 24 := wordOf_val (by simp; omega)
    unfold revOf
    rw [hfr2 (wordOf z 24#u64) (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega)]
  have hco2' : ∀ z ∈ G.chains.flatten, z ≠ x → capV (L.mem s2) z = capV (L.mem s) z :=
    fun z hz hne => hco2 z ((RR2.M.members z).1 hz).1 hne
  have hrv4 : ∀ z ∈ G.chains.flatten, revOf (L.mem s4) z = revOf (L.mem s3) z := fun z hz => by
    rw [hctx.hrev z ((RR3.M.members z).1 hz).1, if_neg (fun e : z = val => hvm (e ▸ hz))]
  have hf4 : (4096#u64 : U64).val = 2 ^ sb.val := by rw [h2sb]; rfl
  have MS : MdbStep (L.mem s) G (L.mem s5) G' :=
    (MdbStep.of_same hM hSS).trans <|
    (MdbStep.setFi hM hI hxm hcx1 RR2.cap hf' (Or.inr hnd) hco2' hrv2).trans <|
    (MdbStep.of_same RR2.M hSS3).trans <|
    (MdbStep.pool RR3.M RR3.I hxm RR3.cap hf4 hnd hvm hctx.cd hbA htA (fun z hz => hctx.cz hz) hrv4
      ⟨by rw [hbase]; omega, by rw [hbase]; omega, hp0⟩).trans <|
    MdbStep.of_same hM4 hSS5
  have VM : ∀ ksb : U64, Vs.VsMdbInv ksb (L.mem s) G → Vs.VsMdbInv ksb (L.mem s5) G' := fun ksb h0 => by
    have W1 := h0.keep (fun z hz => hSS.capV ((hM.members z).1 hz).1)
    have W2 := W1.setFi hcx1 RR2.cap hco2'
    have W3 := W2.keep (fun z hz => hSS3.capV ((RR2.M.members z).1 hz).1)
    have W4 := W3.pool hxm hctx.cd ⟨by rw [hbase]; omega, by rw [hbase]; omega, hp0⟩ (fun z hz => hctx.cz hz)
    exact W4.keep (fun z hz => hSS5.capV ((hM4.members z).1 hz).1)
  refine ⟨τf, th', G', by rw [hrun]; exact hmem, by rw [hrun]; exact hall.1, hP', hR5, hV5, hM5, hC5,
    MdbInv.of_same hM4 hI4 hSS5, UtInv.of_same hM4 hU4 hSS5, by rw [hksb5]; exact hVs5, hPt5, hSR5, ⟨hKTf, F5⟩, FR5, VC,
    MS, VM, hMp.1.ct, by rw [hth', h2sb],
    by rw [hksb5], ?_, ⟨hpal, hpfit, hp0, hN, hns, hcn, hPo, hLo, hTo⟩,
    ⟨x, fi, hxm, by rw [← hsb]; exact capV_of_capAt hcap, hnd⟩, ?_, hMid⟩
  · -- no new SC
    intro q y n hk
    have e := hMp.1.keep' (q := q.bv) (by
      rw [hk]; rintro (h | ⟨r, cs, h⟩ | ⟨ao, h⟩) <;> cases h)
    rw [e] at hk
    exact ⟨y, hk⟩
  -- the pools' entries: the new pool's zero, the others' kept
  intro L4' hPI q hq lo hl hne
  rcases hq with rfl | hq
  · exact absurd (hz5 lo hl) hne
  have hw : VsWrite P K (peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
  have hal := VsWrite.aligned hVP hw
  obtain ⟨-, qf⟩ := hVP.pal q hq
  have hnv : peA q lo ≠ atA K i := fun e => by
    have := congrArg UScalar.val e
    rw [peA_val qf hl, atA_val hVP.ksb_fit hi] at this
    have := hVP.ptab q hq; omega
  have e : L.mem s5 (peA q lo) = L.mem s (peA q lo) := by
    rw [hm54 _ hal (hpne _ hnv), hmem41 _ hal (hVO _ hw) (hVout _ hw)]
  rw [e] at hne ⊢
  exact hPI q hq lo hl hne


end

end

end Fl4Proofs.P3.Vs
