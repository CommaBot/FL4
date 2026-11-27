/-
P3 (line mmuAD, gen 39): **the EnableIOPort `set_cap` at `JAtZV3`** — rewriting one CNode slot's I/O-port cap
`IoPort f l 0` (no owner) to `IoPort f l p` (owner `p ∈ V`, FL4 vcpu.rs l. 1046 `ex[0].set_cap(s, Cap::IoPort
{first, last, vcpu: v})`) keeps the VM-epoch invariant with the spec state unchanged (the spec's
`ioPortCap first last` has no owner field: decision Q2, `Ext/VirtVcpu` `performVcpuInvocation`'s comment).

* `Vs.IoLike c' c`: `Vs.MdbLike` without its VT-x flag (`vtF`, which does change here: `vtF (IoPort f l p) =
  (p ≠ 0)`); `Vs.IoLike.srl` / `srr` / `capSim` / `isPF` and **`Vs.Recap.carryIo`** (P3/VsMdb's `Recap.carry`
  over `IoLike`, proof verbatim: it never reads the VT-x flag) — MDB links, CDT relation, `MdbInv`, `FinInv` after.
* `StateRel.of_absV`, `SlotsValid.of_cvV`: the CSpace state relation and slot validity across a step keeping every
  slot's abstraction (`absCap`, `CapWf`) and validity; `Vs.VsKeep.of_vk`: `VsKeep` when every slot keeps its
  VSpace key and ref.
* **`JAtZV3.ioOwnJ`**: from `JAtZV3` with the CNode slot `x = cslotAddr (pc, idx)` holding `IoPort f l 0`,
  `p ∈ V` canonical: `set_cap x (IoPort f l p)` ends in `JAtZV3` at the same σ, with the new cap at `x` and FL4's
  writes the two cap words of `x`. Proof: `XTopAt.slotStep` (CSpace relations by `Recap.carryIo`, `StateRel.of_absV`,
  `MdbStep.recap`), `JAtZB.vsStepJXB` (P3/JAtZBRecap; σ' = σ), the extension (`JExtV.cap`: `VtxCap (IoPort f l p)`
  is `p ∈ V`; the TCB/VCPU/list words and every VCPU image miss `x`'s words: `JWPl`, `JVLay.vap`).

No named premise (`Canonical p`, the CNode slot and the cap `IoPort f l 0` are the statement's scope; the
EnableIOPort decoder supplies them, P3/JAtZV3VEio). No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBRecap
import Fl4Proofs.P3.JAtZV3VDisp4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Vs
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3

noncomputable section

/-- `MdbLike` without the VT-x flag (module docstring; `True` keeps `MdbLike`'s field positions). -/
def IoLike (c' c : capability.Cap) : Prop :=
  shape c' = shape c ∧ okey c' = okey c ∧ badgeF c' = badgeF c ∧ True

theorem IoLike.refl (c : capability.Cap) : IoLike c c := ⟨rfl, rfl, rfl, trivial⟩

theorem IoLike.srl {c' c : capability.Cap} (h : IoLike c' c) (b : capability.Cap) : srB c' b = srB c b := by
  rw [srB_shape, h.1, ← srB_shape]

theorem IoLike.srr {c' c : capability.Cap} (h : IoLike c' c) (b : capability.Cap) : srB b c' = srB b c := by
  rw [srB_shape, h.1, ← srB_shape]

theorem IoLike.capSim {c' c : capability.Cap} (h : IoLike c' c) : CapSim c' c :=
  ⟨h.2.1, refs_of_shape h.1, (shape_kind h.1).2.2.1, (shape_kind h.1).2.2.2.1, h.srl, h.srr⟩

theorem IoLike.isPF {a' a b' b : capability.Cap} (ha : IoLike a' a) (hb : IoLike b' b) (r f : Bool) :
    isPF r a' b' f = isPF r a b f := by
  unfold Fl4Proofs.P3.isPF
  rw [ha.srl, hb.srr, (shape_kind ha.1).1, ha.2.2.1, hb.2.2.1]

/-- An I/O-port cap with another owner is `IoLike`. -/
theorem ioLike_io (f l q q' : U64) : IoLike (.IoPort f l q') (.IoPort f l q) := ⟨rfl, rfl, rfl, trivial⟩

/-- **`VsKeep` when every slot keeps its VSpace key and ref.** -/
theorem VsKeep.of_vk {th : TypedHeap} {m m' : U64 → U64}
    (hc : ∀ y, IsSlot th y → VKey (capV m' y) = VKey (capV m y) ∧ VRefOf (capV m' y) = VRefOf (capV m y)) :
    VsKeep th th m m' where
  fwd y hy _ := ⟨y, hy, (hc y hy).1, (hc y hy).2⟩
  back y hy _ := ⟨y, hy, (hc y hy).1.symm, (hc y hy).2.symm⟩
  inj y1 y2 hy1 hy2 hne hk _ := ⟨y1, y2, hy1, hy2, hne, (hc y1 hy1).1.symm, (hc y1 hy1).2.symm,
    by rw [← (hc y2 hy2).1]; exact hk.symm⟩

section
variable {th : TypedHeap}

set_option maxHeartbeats 1000000 in
/-- **`Recap.carry` (P3/VsMdb) for an `IoLike` recap** (proof verbatim; `IoLike` is `MdbLike` without the VT-x flag, which the proof never reads). -/
theorem Recap.carryIo {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost} {x : U64}
    (hM : MdbLinks th m G) (hC : CdtRel th m σ G) (hI : MdbInv m G) (hFI : FinInv th m σ G)
    (hF : SlotFoot th m m' x) (hx : IoLike (capV m' x) (capV m x)) (hK : KFoot σ σ') :
    MdbLinks th m' G ∧ CdtRel th m' σ' G ∧ MdbInv m' G ∧ FinInv th m' σ' G := by
  have hpv : ∀ y, IsSlot th y → prevOf m' y = prevOf m y := fun y hy => (hF y hy).1
  have hnx : ∀ y, IsSlot th y → nextOf m' y = nextOf m y := fun y hy => by
    unfold nextOf; rw [(hF y hy).2.1]
  have hrv : ∀ y, IsSlot th y → revOf m' y = revOf m y := fun y hy => by
    unfold revOf; rw [(hF y hy).2.1]
  have hfb : ∀ y, IsSlot th y → fbOf m' y = fbOf m y := fun y hy => by
    unfold fbOf; rw [(hF y hy).2.1]
  have hcv : ∀ y, IsSlot th y → y ≠ x → capV m' y = capV m y := fun y hy hne => by
    unfold capV; rw [((hF y hy).2.2 hne).1, ((hF y hy).2.2 hne).2]
  have hlk : ∀ y, IsSlot th y → IoLike (capV m' y) (capV m y) := fun y hy => by
    by_cases e : y = x
    · subst e; exact hx
    · rw [hcv y hy e]; exact IoLike.refl _
  have hsl : ∀ y, y ∈ G.chains.flatten → IsSlot th y := fun y h => ((hM.members y).1 h).1
  have hM' : MdbLinks th m' G := hM.recap (fun y hy => ⟨hpv y hy, hnx y hy⟩)
    (fun y hy => (shape_kind (hlk y hy).1).2.2.2.2)
  refine ⟨hM', ⟨fun sl hs => by rw [hK.1]; exact hC.cdt sl hs,
    fun sl q hq => hC.cdt_slot sl q (by rw [← hK.1]; exact hq),
    fun sl hs => by rw [hK.2.1, hC.orig sl hs, hrv _ hs.isSlot], hC.par_slot⟩, ?_, ?_⟩
  · have hnx' : ∀ y ∈ G.chains.flatten, nextOf m y ≠ 0#u64 → nextOf m y ∈ G.chains.flatten := by
      intro y hy hn
      rcases hM.next_mem hy with h | ⟨h, -⟩
      · exact absurd h hn
      · exact h
    have hpm : ∀ a b, a ∈ G.chains.flatten → b ∈ G.chains.flatten → isPM m' a b = isPM m a b := by
      intro a b ha hb
      unfold isPM
      rw [hrv a (hsl a ha), hfb b (hsl b hb)]
      exact (hlk a (hsl a ha)).isPF (hlk b (hsl b hb)) _ _
    have hsr : ∀ a b, a ∈ G.chains.flatten → b ∈ G.chains.flatten → srM m' a b = srM m a b := by
      intro a b ha hb
      unfold srM; rw [(hlk a (hsl a ha)).srl, (hlk b (hsl b hb)).srr]
    refine ⟨fun c p h => ?_, fun a b h => ?_, fun y hy hn a ha hd => ?_, fun ch hch => ?_,
      fun y hy hn hb hs hbd hb0 => ?_, fun a ha hu => ?_, fun a ha hz => ?_⟩
    · rw [hrv p (hsl p (hM.tree.par_mem _ _ h).2)]; exact hI.orig c p h
    · obtain ⟨h1, h2⟩ := desc_mem hM h
      rw [hpm a b h2 h1]; exact hI.desc a b h
    · have hy' := hsl y hy
      rw [hnx y hy'] at hn hd ⊢
      have ha' : a ∈ G.chains.flatten := by rcases ha with rfl | ha; exact hy; exact (desc_mem hM ha).2
      rw [hpm a _ ha' (hnx' y hy hn)]; exact hI.after y hy hn a ha hd
    · refine Mdb.chunkL_congr (hI.chunk ch hch) (fun u hu v hv => srF_congr ?_ ?_ ?_)
      · exact hsr u v (List.mem_flatten.2 ⟨_, hch, hu⟩) (List.mem_flatten.2 ⟨_, hch, hv⟩)
      · exact (shape_kind (hlk u (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))).1).2.2.2.1
      · exact hrv u (hsl u (List.mem_flatten.2 ⟨_, hch, hu⟩))
    · have hy' := hsl y hy
      rw [hnx y hy'] at hn hs hbd hb0 ⊢
      have hn' := hnx' y hy hn
      rw [(shape_kind (hlk y hy').1).1] at hb
      rw [(hlk y hy').2.2.1, (hlk _ (hsl _ hn')).2.2.1] at hbd
      rw [(hlk _ (hsl _ hn')).2.2.1] at hb0
      rw [hsr y _ hy hn'] at hs
      rw [hfb _ (hsl _ hn')]; exact hI.badges y hy hn hb hs hbd hb0
    · rw [(shape_kind (hlk a (hsl a ha)).1).2.1] at hu; rw [hrv a (hsl a ha)]; exact hI.utrev a ha hu
    · rw [(shape_kind (hlk a (hsl a ha)).1).2.2.1] at hz; rw [hsr a a ha ha]; exact hI.self a ha hz
  · exact ⟨hFI.kt.sub hK.ksub, hFI.fm.recap hM.tree.nodup x hx.capSim
      (fun z hz hne => hcv z (hsl z hz) hne)⟩


end

end

end Fl4Proofs.P3.Vs

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {th : TypedHeap} {m m' : U64 → U64}

/-- **The CSpace state relation across a step keeping every slot's abstraction.** -/
theorem StateRel.of_absV {Z : Type} {σ : Fl4Spec.State Z} (hR : StateRel th m σ)
    (h : ∀ y, IsSlot th y → CapWf (capV m y) → CapWf (capV m' y) ∧ absCap (capV m' y) = absCap (capV m y)) :
    StateRel th m' σ := by
  have hS : ∀ y oc, IsSlot th y → SlotRel m y oc → SlotRel m' y oc := by
    rintro y oc hy ⟨c, ac, hc, ho, hw, ha⟩
    have e := capV_of_capAt hc
    subst e
    obtain ⟨hw', ha'⟩ := h y hy hw
    exact ⟨capV m' y, ac, capAt_capV _ _, ho, hw', ha'.trans ha⟩
  refine ⟨fun p r hp => ?_, fun t ht => ?_⟩
  · obtain ⟨cs, hk, hwf, hs⟩ := hR.cnode p r hp
    refine ⟨cs, hk, hwf, fun idx hl => hS _ _ ?_ (hs idx hl)⟩
    rw [slotAddr_ofBl]
    exact ⟨p, _, Or.inl ⟨r, hp, hl ▸ blVal_lt idx⟩, rfl⟩
  · obtain ⟨tcb, hk, hs⟩ := hR.tcb t ht
    exact ⟨tcb, hk, fun i hi => hS _ _ ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩ (hs i hi)⟩

/-- **Slot validity across a step keeping every slot's validity.** -/
theorem SlotsValid.of_cvV (hV : SlotsValid th m)
    (h : ∀ y, IsSlot th y → CapValid th (capV m y) → CapValid th (capV m' y)) : SlotsValid th m' := by
  refine ⟨fun p r hp i hi c hc => ?_, fun t ht i hi c hc => ?_⟩
  · have e := capV_of_capAt hc
    subst e
    exact h _ ⟨p, i, Or.inl ⟨r, hp, hi⟩, rfl⟩ (hV.cnode p r hp i hi _ (capAt_capV _ _))
  · have e := capV_of_capAt hc
    subst e
    exact h _ ⟨t, i, Or.inr ⟨ht, hi⟩, rfl⟩ (hV.tcb t ht i hi _ (capAt_capV _ _))

end

section
open Classical Fl4Proofs.P3.Vs
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The EnableIOPort `set_cap` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.ioOwnJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {pc : U64} {r : Nat}
    {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r) {f l : U64}
    (hcx : capV (L.mem s) (cslotAddr (pc.bv, idx)) = .IoPort f l 0#u64) {p : U64} (hp : p ∈ V)
    (hcan : Canonical p) :
    obj.Slot.set_cap st (cslotAddr (pc.bv, idx)) s (.IoPort f l p) ⦃ s' =>
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s' a σ ∧
      capV (L.mem s') (cslotAddr (pc.bv, idx)) = .IoPort f l p ∧
      P1.WritesIn st s s' (fun b => b = cslotAddr (pc.bv, idx) ∨ b = wordOf (cslotAddr (pc.bv, idx)) 8#u64) ⦄ := by
  have B := J.z2.zv.base
  have hP : Placed Z.th := B.xtop.rel.1
  have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
  have hx : IsSlot Z.th (cslotAddr (pc.bv, idx)) := hA.isSlot
  obtain ⟨hSR, hSV, hM, hCd, hI⟩ := B.xtop.rel.2.1
  have hwf : f.val < 2 ^ 16 ∧ l.val < 2 ^ 16 ∧ f.val ≤ l.val := by
    obtain ⟨c0, a0, hc0, hr0, -⟩ := hSR.abs_cap hA
    have e := capV_of_capAt hc0
    rw [hcx] at e
    subst e
    exact hr0.1
  have hEnc : EncWf (.IoPort f l p) := ⟨hwf.1, hwf.2.1, hcan⟩
  have hfx := hx.fit hP
  have hal32 := hx.align hP
  refine WP.spec_mono (WP.spec_and (Vs.set_cap_foot hP hx s _ hEnc)
    (set_cap_frame s (cslotAddr (pc.bv, idx)) (.IoPort f l p) (by omega) (by omega))) ?_
  rintro s' ⟨⟨hF, hcv'⟩, hWF⟩
  set x := cslotAddr (pc.bv, idx) with hxdef
  have h8 : (wordOf x 8#u64).val = x.val + 8 := wa8_val (by omega)
  have hW : P1.WritesIn st s s' (fun b => b = x ∨ b = wordOf x 8#u64) := by
    refine ⟨hWF.1, hWF.2.1, fun b hb hn => hWF.2.2 b hb fun hr => hn (by
      obtain ⟨g1, g2⟩ := hr
      have hb8 : b.val % 8 = 0 := hb
      by_cases e : b.val = x.val
      · exact Or.inl (UScalar.eq_of_val_eq e)
      · exact Or.inr (UScalar.eq_of_val_eq (by rw [h8]; omega)))⟩
  have hks : L.ksb s' = L.ksb s := hW.1
  -- the caps after
  have hcap : ∀ y, IsSlot Z.th y → y ≠ x → capV (L.mem s') y = capV (L.mem s) y := fun y hy hne => by
    unfold capV; rw [((hF y hy).2.2 hne).1, ((hF y hy).2.2 hne).2]
  have hlk : IoLike (capV (L.mem s') x) (capV (L.mem s) x) := by rw [hcv', hcx]; exact ioLike_io f l _ _
  have hsh : shape (capV (L.mem s') x) = shape (capV (L.mem s) x) := hlk.1
  have hok : okey (capV (L.mem s') x) = okey (capV (L.mem s) x) := hlk.2.1
  have hnu : isUt (capV (L.mem s) x) = false := by rw [hcx]; rfl
  have hl : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s (wordOf y 24#u64) := fun y hy => ⟨(hF y hy).1, (hF y hy).2.1⟩
  -- the CSpace relations after
  obtain ⟨hM', hCd', hI', hFI'⟩ := Recap.carryIo hM hCd hI B.xtop.rel.2.2.1 hF hlk (KFoot.refl σ)
  have hSR' : StateRel Z.th (L.mem s') σ := hSR.of_absV fun y hy hw => by
    by_cases e : y = x
    · rw [e, hcv', hcx]; exact ⟨hwf, rfl⟩
    · rw [hcap y hy e]; exact ⟨hw, rfl⟩
  have hSV' : SlotsValid Z.th (L.mem s') := hSV.of_cvV fun y hy hv => by
    by_cases e : y = x
    · rw [e, hcv']; trivial
    · rw [hcap y hy e]; exact hv
  have hMO' : MdbOKV (L.ksb s) (L.mem s') Z.G :=
    (MdbStep.recap hM x (CapAlike.of_shape hsh hok fun h => by rw [hnu] at h; cases h)
      (fun P L4 L3 L2 L1 _ => by rw [hcv']; trivial)
      (fun z hz hne => hcap z ((hM.members z).1 hz).1 hne)
      (fun z hz => by unfold revOf; rw [(hF z ((hM.members z).1 hz).1).2.1])).okv B.xtop.rel.2.2.2.2.1
  have hTS : ∀ t, Z.th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1) := by
    intro t ht
    have hs : IsSlot Z.th (slotOf t 1) := ⟨t, 1, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩
    have he : cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 1) = slotOf t 1 := by
      show slotAddr t.bv (Fl4Spec.ofBl _) = _
      rw [slotAddr_ofBl, tcbCnodeIndex_blVal 1 (by decide)]
    have hne : slotOf t 1 ≠ x := fun e => cnode_slot_ne_tcb hP hpc hidx ht 1 (by decide) (by rw [he, e])
    rw [capAt_capV, capAt_capV, hcap _ hs hne]
  have hX1 : XTopAt (L := L) AR { Z with G := Z.G } s' a σ :=
    XTopAt.slotStep B.xtop (hW.mono fun b hb => by
        rcases hb with rfl | rfl
        · exact ⟨x, hx, 0#u64, Or.inl rfl, (wordOf_zero x).symm⟩
        · exact ⟨x, hx, 8#u64, Or.inr (Or.inl rfl), rfl⟩)
      (Ipc.CnK.refl σ) (Ipc.KeepC.refl σ) ⟨hSR', hSV', hM', hCd', hI'⟩ hFI' hMO' hTS
  -- `JAtZB` after (`vsStepJXB`, σ unchanged)
  have hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s') := fun y hy => by
    by_cases e : y = x
    · rw [e, hcv']; trivial
    · rw [hcap y hy e]; exact B.vsc y hy
  have hvn : Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s') :=
    B.vsShr (G' := Z.G) hX1 hks (VsKeep.of_vk fun y hy => by
      by_cases e : y = x
      · rw [e, hcv', hcx]; exact ⟨rfl, rfl⟩
      · rw [hcap y hy e]; exact ⟨rfl, rfl⟩) (ArchShr.refl σ)
  have B' : JAtZB (L := L) arI AR Z H Cs Ac Lst D s' a σ :=
    B.vsStepJXB ⟨B.scOut⟩ hpc hidx (TabsArch.empty σ) (L3' := Z.L3) (L2' := Z.L2) (L1' := Z.L1) hX1
      (VsSFr.of_eq rfl) (hW.mono fun b hb => Or.inl (Or.inr hb)) hcap hsh hok hnu hl hvc
      ⟨subset_rfl, subset_rfl, subset_rfl⟩ hvn
  -- the extension: `x`'s words miss every VCPU and every extension word
  have Ly := B.jvLay J.z2.zv.vm
  have Pw := B.jwPl J.z2.zv.vm
  have hxv : ∀ u ∈ V, ∀ b, (b = x ∨ b = wordOf x 8#u64) → b.val < u.val ∨ u.val + 32768 ≤ b.val := by
    intro u hu b hb
    obtain ⟨g1, g2, -, -⟩ := B.cslotW_val hpc hidx hb
    have hap := Ly.vap u hu pc _ hpc
    simp only [objSize] at hap
    have e5 : (2 : Nat) ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
    omega
  have hjw : ∀ b, (b = x ∨ b = wordOf x 8#u64) → JW V Z.th b := fun b hb => Or.inl ⟨x, hx, hb⟩
  have kTV : ∀ t, Z.th t = some .tcb → L.mem s' (tVcpuA t) = L.mem s (tVcpuA t) := fun t ht =>
    hW.mem_eq (Pw.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))) fun hb => by
      rcases hb with e | e
      · exact (Pw.slv x hx t ht).1 e.symm
      · exact (Pw.slv x hx t ht).2 e.symm
  have kVT : ∀ v ∈ V, L.mem s' (vTcbA v) = L.mem s (vTcbA v) := fun v hv =>
    hW.mem_eq (Pw.jw _ (Or.inr (Or.inr ⟨v, hv, rfl⟩))) fun hb => by
      rcases hb with e | e
      · exact (Pw.slb x hx v hv).1 e.symm
      · exact (Pw.slb x hx v hv).2 e.symm
  have kSt : ∀ t, Z.th t = some .tcb → L.mem s' (P1.stA t) = L.mem s (P1.stA t) := fun t ht =>
    hW.mem_eq (Pw.sw _ ⟨t, ht, rfl⟩) fun hb => Pw.swjw _ ⟨t, ht, rfl⟩ (hjw _ hb)
  have E0 := J.z2.zv.extv
  have E' : JExtV (L := L) V X Z.th s' :=
    { cap := fun y hy => by
        by_cases e : y = x
        · rw [e, hcv']; exact fun _ => hp
        · rw [hcap y hy e]; exact E0.cap y hy
      bnd := fun t ht => by
        rcases E0.bnd t ht with h | ⟨h1, h2⟩
        · left; rw [kTV t ht]; exact h
        · right; rw [kTV t ht]; exact ⟨h1, by rw [kVT _ h1]; exact h2⟩
      back := fun v hv => by
        rcases E0.back v hv with h | ⟨h1, h2⟩
        · left; rw [kVT v hv]; exact h
        · right; rw [kVT v hv]; exact ⟨h1, by rw [kTV _ h1]; exact h2⟩
      nz := E0.nz }
  have R' : RunVmB (L := L) Z.th s' := fun t ht h8' => by
    rw [kTV t ht]; exact J.z2.zv.rvm t ht (by rw [← kSt t ht]; exact h8')
  have Jv' : JVm (L := L) V H s' σ :=
    ⟨J.z2.zv.vm.spec, J.z2.zv.vm.heap, fun u hu => by rw [hks]; exact J.z2.zv.vm.ks u hu, J.z2.zv.vm.sep⟩
  have Vl' : VList st V Z.th s' := J.z2.zv.vl.writes hW fun b hb => by
    refine ⟨J.z2.zv.vl.lw_al Ly.vfit hb, fun hWb => ?_⟩
    rcases hb with rfl | ⟨u, hu, rfl | rfl⟩
    · exact J.z2.zv.vl.hd.2.1 (hjw _ hWb)
    · have := lay_next_val (Ly.vfit u hu).2
      rcases hxv u hu _ hWb with h | h <;> omega
    · have := lay_prev_val (Ly.vfit u hu).2
      rcases hxv u hu _ hWb with h | h <;> omega
  have vb' : VBind V σ (L.mem s') := J.z2.vb.ofKheap rfl kVT
  have vr' : VRel V σ (L.mem s') :=
    J.vr.frame (fun u _ vs hu => hu) (v3_agreeW hW (fun u hu => (Ly.vfit u hu).2) hxv)
  exact ⟨⟨⟨⟨B', E', R', Jv', Vl'⟩, vb'⟩, J.vo, vr'⟩, hcv', hW⟩

end

end

end Fl4Proofs.P3
