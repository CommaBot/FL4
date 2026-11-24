/-
P3 (issue #16, FL4 #71), VSpace FrameBatch (KENTRY-PLAN fb3l): **the
COPY_MAP entry's insert at `J`** with the batch loop's facts.

* `fbc_ppk`: `FbKeep` is a `PPK` step (`PPR0` kept).
* `fbc_foot_trans`: `FbFootK` across two steps at sets of the same TCBs and
  buffer words.
* `fbc_destCap`: a CNode a lookup reaches (`CnRef`) from a root held in a
  slot is named by a CNode cap in a slot (`DestCap`).
* `fbc_mask_frame`, `fbc_notPage`: the masked frame cap is a frame cap of
  the same frame; a cap that is no frame abstracts to no page cap.
* `JAtZ.fbInsJ`: `cdt::insert` of the derived (unmapped) frame copy into an
  empty CNode slot at `J` (XTopJointGrant's `JAtZ.insDJ`), with `LiveDN`
  (XTopJointLiveIns' `LiveDN.insC`), `NoSwitch`, `SpecGlob`
  (XTopJointTcbInstall's `SpecGlob.ins`), `PPR0`, `FbKeep` and `FbFootK`
  after.
-/
import Fl4Proofs.P3.XTopJointFbDelFrameN
import Fl4Proofs.P3.XTopJointLiveIns
import Fl4Proofs.P3.XTopJointTcbInstall
import Fl4Proofs.P3.SpecFbKeepDel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section Spec
open Fl4Spec

/-- **`FbKeep` keeps what `PPR0` reads.** -/
theorem fbc_ppk {σ σ' : State Unit} (h : FbKeep σ σ') : PPK σ σ' where
  cons := h.cons
  time := h.time
  csc := h.csc
  rel u hu := by rw [h.rel] at hu; exact hu
  sc p y n hy := by
    rcases h.kh p with e | ⟨a, a', ha, ha', -⟩ | ⟨r, cs, cs', hc, hc'⟩ | ⟨x, y', hx, hy', -⟩
    · rw [← e]; exact hy
    · rw [ha'] at hy; cases hy
    · rw [hc'] at hy; cases hy
    · rw [hy'] at hy; cases hy
  tcb p y hy := by
    rcases h.kh p with e | ⟨a, a', ha, ha', -⟩ | ⟨r, cs, cs', hc, hc'⟩ | ⟨x, y', hx, hy', hxy⟩
    · exact ⟨y, by rw [← e]; exact hy, rfl, id⟩
    · rw [ha'] at hy; cases hy
    · rw [hc'] at hy; cases hy
    · rw [hy'] at hy; cases hy
      exact ⟨x, hx, hxy.2.2.2.2.2.1.symm, fun hb => by rw [hxy.1]; exact hb⟩
  ct := h.ct
  idle := h.idle
  ns hn u := by rw [h.act]; exact hn u
  ina p x y hx hy hi := by
    left
    rcases h.kh p with e | ⟨a, a', ha, ha', -⟩ | ⟨r, cs, cs', hc, hc'⟩ | ⟨x', y', hx', hy', hxy⟩
    · rw [e, hx] at hy; cases hy; exact hi
    · rw [hx] at ha; cases ha
    · rw [hx] at hc; cases hc
    · rw [hx] at hx'; cases hx'; rw [hy] at hy'; cases hy'; rw [hxy.1]; exact hi
  nq hq d q := by rw [h.ct, h.rq]; exact hq d q

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop}

theorem fbc_foot_trans {Z Z' : XSets} {s s1 s2 : S} (hT : Z'.T = Z.T) (hB : Z'.B = Z.B)
    (h1 : FbFootK (L := L) Z s s1) (h2 : FbFootK (L := L) Z' s1 s2) : FbFootK (L := L) Z s s2 :=
  ⟨fun t ht g => (h2.1 t (hT ▸ ht) g).trans (h1.1 t ht g), fun wp hw => (h2.2 wp (hB ▸ hw)).trans (h1.2 wp hw)⟩

theorem fbc_destCap {th : TypedHeap} {mem : U64 → U64} {root : capability.Cap} {p : U64} (h : CnRef th mem root p)
    (hr : ∃ y, IsSlot th y ∧ capV mem y = root) : DestCap th mem p := by
  obtain ⟨r, gs, g, hr'⟩ := h
  rcases hr' with ⟨q, r', idx, hq, hl, hc⟩ | e
  · exact ⟨cslotAddr (q.bv, idx), r, gs, g, AbsSlot.isSlot ⟨q, rfl, Or.inl (by rw [hl]; exact hq)⟩,
      capV_of_capAt hc⟩
  · obtain ⟨y, hy, hyc⟩ := hr
    exact ⟨y, r, gs, g, hy, by rw [hyc, e]⟩

theorem fbc_mask_frame {r : capability.Rights} {p : U64} {sz : capability.FrameSize} {rt : U64} {d m e : Bool}
    {a v : U64} {c1 : capability.Cap}
    (h : capability.mask_cap_rights r (.Frame p sz rt d m e a v) = ok c1) :
    ∃ rt', c1 = .Frame p sz rt' d m e a v := by
  simp only [capability.mask_cap_rights] at h
  obtain ⟨i, hi, -⟩ := spec_exists (P0.capability.mask_vm_rights.p0 rt r)
  rw [hi, bind_ok] at h
  exact ⟨i, (eq_of_ok_eq h).symm⟩

theorem fbc_notPage {c : capability.Cap} (h : vspace.as_frame c = ok none) :
    ¬ Fl4Spec.isPageCap (absCap c) = true := by
  cases c <;> simp_all [vspace.as_frame, absCap, Fl4Spec.isPageCap]

variable (arI)
variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The COPY_MAP insert at `J`** (module docstring). -/
theorem JAtZ.fbInsJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ) (hns : Vs.NoSwitch σ) (hsg : SpecGlob σ) (hp0 : PPR0 σ)
    {ps pd : U64} {rs rd : Nat} (hps : Z.th ps = some (.cnode rs)) (hpd : Z.th pd = some (.cnode rd))
    {idxs idxd : List Bool} (hls : idxs.length = rs) (hld : idxd.length = rd)
    {p : U64} {sz : capability.FrameSize} {rt : U64} {d m e : Bool} {asid va : U64}
    (hsrcC : capAt (L.mem s) (cslotAddr (ps.bv, idxs)) = ok (.Frame p sz rt d m e asid va))
    (hdst : capAt (L.mem s) (cslotAddr (pd.bv, idxd)) = ok .Null) {rt' : U64}
    (hw : CapWf (.Frame p sz rt' d false false 0#u64 0#u64))
    (hcv : CapValid Z.th (.Frame p sz rt' d false false 0#u64 0#u64))
    (he : EncWf (.Frame p sz rt' d false false 0#u64 0#u64))
    (hDs : DestCap Z.th (L.mem s) ps) (hDd : DestCap Z.th (L.mem s) pd) :
    cdt.insert st s (.Frame p sz rt' d false false 0#u64 0#u64) (cslotAddr (ps.bv, idxs))
      (cslotAddr (pd.bv, idxd)) ⦃ s' => ∃ (σ' : Fl4Spec.State Unit) (G' : MdbGhost),
      Fl4Spec.capInsert (Z := Unit) (absCap (.Frame p sz rt' d false false 0#u64 0#u64)) (ps.bv, idxs) (pd.bv, idxd) σ =
        ({((), σ')}, False) ∧
      JAtZ (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac Lst D s' a σ' ∧ LiveDN (L := L) Z.th H Cs G' s' σ' ∧
      Vs.NoSwitch σ' ∧ SpecGlob σ' ∧ PPR0 σ' ∧ FbKeep σ σ' ∧ FbFootK (L := L) Z s s' ∧
      capV (L.mem s') (cslotAddr (pd.bv, idxd)) = .Frame p sz rt' d false false 0#u64 0#u64 ∧
      CnSlotsKept (L := L) Z.th s s' ⦄ := by
  set cc : capability.Cap := .Frame p sz rt' d false false 0#u64 0#u64 with hcc
  have hX := J.xtop
  have hPl : Placed Z.th := hX.rel.1
  have hM : MdbLinks Z.th (L.mem s) Z.G := hX.rel.2.1.2.2.1
  have hR : StateRel Z.th (L.mem s) σ := hX.rel.2.1.1
  have hAs : AbsSlot Z.th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hAd : AbsSlot Z.th (pd.bv, idxd) := ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
  have hsnn : (capability.Cap.Frame p sz rt d m e asid va) ≠ .Null := by simp
  have hsm : cslotAddr (ps.bv, idxs) ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hsrcC, hsnn⟩
  have hdnm : cslotAddr (pd.bv, idxd) ∉ Z.G.chains.flatten := fun h => by
    obtain ⟨-, c0, h0, hn⟩ := (hM.members _).1 h; rw [hdst] at h0; exact hn (eq_of_ok_eq h0).symm
  have hnv : ∀ P L4 L3 L2 L1 : Set U64, Vs.VCapOK P L4 L3 L2 L1 (.Frame p sz rt d m e asid va) →
      Vs.VCapOK P L4 L3 L2 L1 cc := by
    intro P L4 L3 L2 L1 h
    exact ⟨fun h' => absurd h' (by simp), h.2.1, fun h' => absurd h' (by simp)⟩
  refine WP.spec_mono (WP.spec_and (J.insDJ hps hpd hls hld hsrcC hsnn hdst cc (absCap cc) ⟨hw, rfl⟩ hcv he
    (by simp [hcc]) (by simp [hcc, shape]) (Or.inr rfl) (fun h => by simp [isUt] at h) rfl
    (by simp [hcc, okey]) hnv (fun h => by simp [hcc, Vs.TabUn] at h)
    (fun h => by rcases h with h | h <;> exact (h rfl).elim) (fun h => by simp [hcc, Vs.TabUn] at h)
    (fun h => by simp [isUt] at h)
    (fun _ => by simp [hcc, Vs.NativeCap]) hDs hDd)
    (Vs.insert_trace hPl s Z.G hM hsm hAd.isSlot hdnm hsrcC cc he)) ?_
  rintro s' ⟨⟨σ', hci, -, hcn, -, hoth, hdc, hsc, G', J'⟩, hF, -⟩
  have hwS := SlotFrame2.writesIn hF
  have hmem : ((), σ') ∈ (Fl4Spec.capInsert (Z := Unit) (absCap cc) (ps.bv, idxs) (pd.bv, idxd) σ).1 := by
    rw [hci]; rfl
  have hK : FbKeep σ σ' := FbKeep.of_cnK hcn
  have hum : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory := by
    have e := congrArg (fun z => z.machineState.underlyingMemory) hcn.1; exact e
  have hLv' := LiveDN.insC J J.dstate hLv J' J'.dstate hpd hld hci hwS hsrcC hdst hoth hdc hsc (by simp [hcc])
    (by simp [hcc, isZb]) hDd
  -- `SpecGlob` after: the new cap is a page cap, the destination no IRQ node slot
  have hnu : ¬ Fl4Spec.isUntypedCap (absCap cc) = true := by simp [hcc, absCap, Fl4Spec.isUntypedCap]
  have hk := nik_capInsert hnu (ps.bv, idxs) (pd.bv, idxd) σ _ hmem
  have hgk := gk_capInsert (absCap cc) (ps.bv, idxs) (pd.bv, idxd) σ _ hmem
  have hd : ∀ irq, (pd.bv, idxd) ≠ (σ.interruptIrqNode irq, []) := by
    intro irq e
    obtain ⟨y, r, gs, g, hy, hyc⟩ := hDd
    obtain ⟨sl, hAy, rfl⟩ := IsSlot.abs hy
    obtain ⟨c0, a0, hc0, hca0, hg0⟩ := hR.abs_cap hAy
    rw [capV_of_capAt hc0] at hyc
    subst hyc
    obtain ⟨o, cr⟩ := sl
    have ha0 := (getCap_set_iff σ o cr a0).1 (congrArg Prod.fst hg0)
    rw [hca0.abs] at ha0
    have hpe : pd.bv = σ.interruptIrqNode irq := congrArg Prod.fst e
    exact hsg.ref o cr _ ha0 (by simp [absCap, IsPageCap]) irq (by rw [← hpe]; simp [absCap, Fl4Spec.objRefs])
  have hsg' : SpecGlob σ' := hsg.ins hk (congrArg Prod.fst hgk) (congrArg Prod.snd hgk) hd
    (fun hp => absurd (by simp [hcc, absCap, IsPageCap]) hp)
  refine ⟨σ', G', hci, J', hLv', fun u => by rw [hK.act]; exact hns u, hsg', PPR0.of_ppk hp0 (fbc_ppk hK), hK,
    FbFootK.of_rel arI J J' rfl rfl hK hum, hdc, fun y hy p0 r0 gs0 g0 h => ?_⟩
  by_cases ey : y = cslotAddr (pd.bv, idxd)
  · rw [ey, capV_of_capAt hdst] at h; cases h
  by_cases es : y = cslotAddr (ps.bv, idxs)
  · rw [es, capV_of_capAt hsrcC] at h; cases h
  rw [hoth y hy es ey]; exact h

end

end

end Fl4Proofs.P3
