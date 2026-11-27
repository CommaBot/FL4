/-
P3x for virtualization (line virt, gen 27, item 1): **the untyped `Retype` step with VCPUs at `JExtV2`** —
VirtUtInvV's `retype_cont_vcpu` / `untyped_retype_vcpu` restated with `JExtV2` (P3/JExtV2) for `JExtV` (entry and
post), over P3/VirtRetFullV2's `retype_full_vcpu2`. Same proofs.

* `RetPostV2`: `RetPostV` with `JExtV2` and, in addition, `ChSub G G'` (each old chain inside one new chain),
  **`NoIoTcb th m → NoIoTcb th m'`** (P3/VirtRetFullV2's `noIoTcb_retExp`: the new caps are VCPU caps) and
  **`VcpuOneChain G m → VcpuOneChain G' m'`** (P3/VirtVChunkIns' `vcpuOneChain_retExp`; freshness by
  `fresh_of_jextV2`: no VCPU of `V` lies in the new window, from `hVreg` and `retype_region`). With `MdbInv` after
  (in the post), `VcpuChunked` after is `vcpuChunked_of`.
* **`retype_cont_vcpu2`**, **`untyped_retype_vcpu2`** — the step theorem at `JExtV2`.

Named premises (all used unchanged, as VirtUtInvV): `CapAgree arI ar` [P], `VirtCodeAgree arI ar` [P], `hag` [P],
`JWPl V th` [J], `hactJ` [J], `hnd` [J]. No new premise (`NoIoTcb` / `VcpuOneChain` appear only as implications in
the post). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtUtInvV
import Fl4Proofs.P3.VirtVChunkIns
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtUtInvV2
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame
open Fl4Proofs.P3.VirtLoopInv0 Fl4Proofs.P3.VirtLoopSharp Fl4Proofs.P3.VirtRetVcpuPre Fl4Proofs.P3.VirtRetFullV Classical
open Fl4Proofs.P3.VirtUtInvV Fl4Proofs.P3.VirtRetFullV2 Fl4Proofs.P3.VirtVChunkIns

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The post of the VCPU retype step at `JExtV2`** (module docstring). -/
def RetPostV2 {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ar : A')
    (V X : Set U64) (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ σ' G', (Fl4Spec.fl4InvokeUntypedV (Z := Unit) inv).run σ1 = ({(.ok (), σ')}, False) ∧
      StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
      MdbLinks th (L.mem res.2.1) G' ∧ CdtRel th (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
      UtInv (L.mem res.2.1) G' ∧ MdbStep m G (L.mem res.2.1) G' ∧
      (FinInv th m σ G → FinInv th (L.mem res.2.1) σ' G') ∧
      match inv with
      | .retype src _ _ rb _ _ slots _ =>
        VList st (VsI V rb.toNat slots.length) th res.2.1 ∧
        JExtV2 (L := L) (VsI V rb.toNat slots.length) X th res.2.1 ∧
        (∀ j, j < slots.length → VRelAt (memW st res.2.1) σ' (vI rb.toNat j).bv) ∧
        ∃ dslot, RetExp th th m (L.mem res.2.1) G G' rb.toNat 32768 slots.length dslot (vcj rb.toNat)
          (cslotAddr src) ∧ DslotC th dslot slots.length ∧ ChSub G G' ∧
          (NoIoTcb th m → NoIoTcb th (L.mem res.2.1)) ∧
          (VcpuOneChain G m → VcpuOneChain G' (L.mem res.2.1))

set_option maxHeartbeats 4000000 in
/-- **decode's success continuation for type 14, at `JExtV2`** (module docstring). -/
theorem retype_cont_vcpu2 {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
    (hcA : CapAgree arI ar) (hkA : VirtCodeAgree arI ar)
    (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    (ct : U64) (hcur : σ.curThread = ct.bv) (hct : sched.cur_thread st s = ok ct) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val) (htop : p.val + 2 ^ sb.val < 2 ^ 64)
    (hactZ : ¬ (p.val + fi.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0)
    {V X : Set U64} (Vl : VList st V th s) (E : JExtV2 (L := L) V X th s)
    (hVf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hVV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    (hVreg : ∀ w ∈ V, w.val + 32768 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.val)
    (hhdV : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhdreg : (P1.vHeadA st s).val + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (P1.vHeadA st s).val)
    (hSV : ∀ y, IsSlot th y → ((P1.vHeadA st s).val + 8 ≤ y.val ∨ y.val + 32 ≤ (P1.vHeadA st s).val) ∧
      ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (hTV : ∀ t, th t = some .tcb → P1.TcbAddr t ∧ tVcpuA t ≠ P1.vHeadA st s ∧
      (∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
      ∀ y, IsSlot th y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32))
    (P : JWPl V th)
    (hactJ : P1.Aligned (actA st s) ∧ ¬ JW V th (actA st s) ∧ ¬ SW th (actA st s))
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hna : P1.vHeadA st s ≠ actA st s)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat) (reset : Bool) (fiv : U64)
    (hnt : nt.val = 14)
    (hctx : RetCtx (L := L) th s σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev) ⦃ res =>
      RetPostV2 (L := L) th (L.mem s) G σ ar V X (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
  obtain ⟨ht, -, ⟨hdest, hr64, -⟩, ⟨hw1, -, hwin⟩, hempty, hreset, hfiv, -, hmem, -⟩ := hctx
  have htv : t = .archObject .vcpuObj := by
    rw [hnt, objTypeOf_14] at ht; exact (Option.some.inj ht).symm
  subst htv
  -- the restart
  have hTa := (hTV ct htcb).1
  have hstv : (P1.stA ct).val = ct.val + 3328 := lay_stA_val hTa
  have hSct : SW th (P1.stA ct) := ⟨ct, htcb, rfl⟩
  have hne : actA st s ≠ P1.stA ct := fun e => hactJ.2.2 ⟨ct, htcb, e⟩
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th hP s ct sched.TS_RESTART htcb hact)
  obtain ⟨s2', hs2', hW, -⟩ := spec_exists (sts_w (L := L) s ct sched.TS_RESTART (P.sw _ hSct) hactJ.1 hne)
  rw [hs2] at hs2'; have := eq_of_ok_eq hs2'; subst this
  rw [hs2]; simp only [bind_ok]
  have hk2 : L.ksb s2 = L.ksb s := hW.1
  have hhd2 : P1.vHeadA st s2 = P1.vHeadA st s := by unfold P1.vHeadA; rw [hk2]
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hSS (t := ct.bv) hkt .restart
  have hI1 := MdbInv.of_same hM hI hSS
  have hU1 := UtInv.of_same hM hU hSS
  have hcap1 : capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev) := by
    rw [hSS.capAt (AbsSlot.isSlot ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩)]; exact hcap
  have hempty1 : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s2) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null := by
    intro i h1 h2
    rw [hSS.capAt ⟨dest, i, Or.inl ⟨r, hdest, by omega⟩, rfl⟩]; exact hempty i h1 h2
  have hzero1 : ZeroRegion (L.mem s2) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hW.mem_eq hw (by
      rintro (e | e)
      · subst e
        have e4 : objSize ObjKind.tcb = 4096 := rfl
        rcases hfree ct _ htcb with h | h <;> omega
      · subst e; exact hactZ ⟨h1, h2⟩)]
    exact hzero w hw h1 h2
  -- the list and the extension across the restart
  have Vl2 : VList st V th s2 := Vl.writes hW (fun b hb => ⟨Vl.lw_al hVf hb, by
    rcases hb with rfl | ⟨w, hw, rfl | rfl⟩
    · rintro (e | e)
      · exact Vl.hd.2.2 ⟨ct, htcb, e⟩
      · exact hna e
    · have hn := lay_next_val (hVf w hw).2
      have hT := (hTV ct htcb).2.2.1 w hw
      rintro (e | e)
      · have := congrArg UScalar.val e; omega
      · have := congrArg UScalar.val e; have := hnd _ (Or.inr rfl) w hw; omega
    · have hn := lay_prev_val (hVf w hw).2
      have hT := (hTV ct htcb).2.2.1 w hw
      rintro (e | e)
      · have := congrArg UScalar.val e; omega
      · have := congrArg UScalar.val e; have := hnd _ (Or.inr rfl) w hw; omega⟩)
  have E2 : JExtV2 (L := L) V X th s2 := E.of_writes P hW (by
    rintro b (rfl | rfl)
    · exact P.swjw _ hSct
    · exact hactJ.2.1)
  have hhdV2 : ∀ w ∈ V, (P1.vHeadA st s2).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s2).val := by
    rw [hhd2]; exact hhdV
  have hhdreg2 : (P1.vHeadA st s2).val + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (P1.vHeadA st s2).val := by
    rw [hhd2]; exact hhdreg
  have hSV2 : ∀ y, IsSlot th y → ((P1.vHeadA st s2).val + 8 ≤ y.val ∨ y.val + 32 ≤ (P1.vHeadA st s2).val) ∧
      ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val := by
    rw [hhd2]; exact hSV
  have hTV2 : ∀ t, th t = some .tcb → P1.TcbAddr t ∧ tVcpuA t ≠ P1.vHeadA st s2 ∧
      (∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
      ∀ y, IsSlot th y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32) := by
    rw [hhd2]; exact hTV
  -- reset = true only on an unused untyped
  have hfiv' : fiv = fi := by
    rw [hfiv]
    cases hrs : reset
    · rfl
    · rw [hrs] at hreset
      have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
      exact (UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl))
  subst hfiv'
  -- the new objects are fresh: no VCPU of `V` among them
  have hz15 : zOf nt.val us.val = 15 := by rw [hnt]; simp [zOf]
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hmem15 := hmem
  rw [hz15] at hmem15
  obtain ⟨hA1, -, hA3, -⟩ := retype_region p fiv sb.val 15 win.val hsb (by norm_num) hpal hpfit hfi hw1 hmem15
  rw [show (2 : Nat) ^ 15 = 32768 by norm_num] at hA3
  have hfit : (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 32768 ≤ 2 ^ 64 := by
    rw [hz15]; omega
  have hVfr : ∀ v ∈ V, ∀ j, j < win.val → v ≠ vI (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat j := by
    rw [hz15]
    intro v hv j hj e
    have e1 := vI_val (B := (Fl4Spec.alignUp (p.bv + fiv.bv) 15).toNat) (j := j) (by omega)
    rw [← e] at e1
    rcases hVreg v hv with c | c <;> omega
  have hfull := retype_full_vcpu2 (L := L) arI ar hA hcA hkA th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 hpp hidx hcap1
    hpal hpfit hfi hhigh htop nt us hnt hdest hr64 off win hwin hw1 hmem hempty1 hfree hzero1 Vl2 E2 hVf hVV hVreg
    hhdV2 hhdreg2 hSV2 hTV2
  have hpost : ∀ res, (res.1 = .Ok () ∧ res.2.2 = ar ∧ ∃ σ' G',
        (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (.archObject .vcpuObj) us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 = ({(.ok (), σ')}, False) ∧
        StateRel th (L.mem res.2.1) σ' ∧ SlotsValid th (L.mem res.2.1) ∧
        MdbLinks th (L.mem res.2.1) G' ∧ CdtRel th (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
        (UtInv (L.mem res.2.1) G' ∧ MdbStep (L.mem s2) G (L.mem res.2.1) G') ∧
        ZeroRegion (L.mem res.2.1)
          ((Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat + win.val * 32768) (p.val + 2 ^ sb.val) ∧
        (FinInv th (L.mem s2) σ1 G → FinInv th (L.mem res.2.1) σ' G') ∧
        VList st (VsI V (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat win.val) th res.2.1 ∧
        JExtV2 (L := L) (VsI V (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat win.val) X th res.2.1 ∧
        ChSub G G' ∧
        (∀ j, j < win.val →
          VRelAt (memW st res.2.1) σ' (vI (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat j).bv) ∧
        ∃ dslot, RetExp th th (L.mem s2) (L.mem res.2.1) G G'
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat 32768 win.val dslot
          (vcj (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat) (cslotAddr (pp.bv, idx)) ∧
          ThX th th (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat 32768 win.val nt.val us.val ∧
          DslotC th dslot win.val) →
      (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype (pp.bv, idx) reset p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (.archObject .vcpuObj) us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 =
        (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (.archObject .vcpuObj) us.val
          (windowSlots dest r off.val win.val) dev)).run σ1 →
      RetPostV2 (L := L) th (L.mem s) G σ ar V X (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (.archObject .vcpuObj) us.val
        (windowSlots dest r off.val win.val) dev) res := by
    rintro res ⟨h1, h2, σ', G', hrun, hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hVl', hE', hCS, hVR', dslot, hEx,
      -, hdsC⟩ he
    refine ⟨h1, h2, σ1, by rw [hcur]; exact hst1, σ', G', he.trans hrun, hR', hV', hM', hC', hI', hU',
      MdbStep.same_left hM hSS hSt', fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)),
      ?_⟩
    show VList st (VsI V _ (windowSlots dest r off.val win.val).length) th res.2.1 ∧ _
    rw [windowSlots_length]
    have hEx0 := hEx.same_left hM hSS
    exact ⟨hVl', hE', hVR', dslot, hEx0, hdsC, hCS,
      fun hT => noIoTcb_retExp hEx0 hM' (fun j _ f l o h => by simp [vcj] at h) hT,
      fun hO => vcpuOneChain_retExp hEx0 hCS hM'.tree.nodup (by first | exact hfit | (rw [windowSlots_length]; exact hfit))
        (fresh_of_jextV2 E hM (by first | exact hVfr | (rw [windowSlots_length]; exact hVfr))) hO⟩
  rcases Bool.eq_false_or_eq_true reset with hrs | hrs <;> subst hrs
  · have hnc : ¬ ∃ x, σ.cdt x = some (pp.bv, idx) := by simpa using hreset.symm
    have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hunused hnc]; rfl)
    have hcap0 := hcap1; rw [hf0] at hcap0
    rw [retype_reset_unused (L := L) arI s2 ar _ _ nt us dest off win dev hcap0]
    have hg : Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 = ({(.untypedCap dev p.bv sb.val 0, σ1)}, False) := by
      obtain ⟨c, a, hc, hca, hg⟩ := hR1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
      rw [hcap0] at hc; have := eq_of_ok_eq hc; subst this
      rw [hg, hca.abs]; rfl
    exact WP.spec_mono hfull (fun res h => hpost res h (fl4InvokeUntypedV_reset_unused _ _ _ _ _ _ dev σ1 hg))
  · exact WP.spec_mono hfull (fun res h => hpost res h rfl)

/-- **The untyped `Retype` step with VCPUs at `JExtV2`, both gate outcomes** (module docstring). -/
theorem untyped_retype_vcpu2 [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (ar : A')
    (hA : P0.ArchTotal arI) (hcA : CapAgree arI ar) (hkA : VirtCodeAgree arI ar)
    (hag : ∀ r, arI.virtualization ar = ok r → r.val = Fl4Spec.virtKind.code)
    (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .untypedRetype ↔ lbl = fl4_abi.label.UntypedRetype)
    (length buf ct : U64) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (h14 : ∀ x, args.head? = some x → x.val = 14)
    (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val) (htop : p.val + 2 ^ sb.val < 2 ^ 64)
    (hactZ : ¬ (p.val + fi.val ≤ (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ∧
      (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val < p.val + 2 ^ sb.val))
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hunused : (¬ ∃ x, σ.cdt x = some (pp.bv, idx)) → fi.val = 0)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List Fl4Spec.Cap) (hex : ExtraRel th (L.mem s) x0 excaps)
    (hfan : Fl4Spec.retypeFanOutLimit = 256#64)
    {V X : Set U64} (Vl : VList st V th s) (E : JExtV2 (L := L) V X th s)
    (hVf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hVV : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    (hVreg : ∀ w ∈ V, w.val + 32768 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ w.val)
    (hhdV : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhdreg : (P1.vHeadA st s).val + 8 ≤ p.val + fi.val ∨ p.val + 2 ^ sb.val ≤ (P1.vHeadA st s).val)
    (hSV : ∀ y, IsSlot th y → ((P1.vHeadA st s).val + 8 ≤ y.val ∨ y.val + 32 ≤ (P1.vHeadA st s).val) ∧
      ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val)
    (hTV : ∀ t, th t = some .tcb → P1.TcbAddr t ∧ tVcpuA t ≠ P1.vHeadA st s ∧
      (∀ w ∈ V, t.val + 4096 ≤ w.val ∨ w.val + 32768 ≤ t.val) ∧
      ∀ y, IsSlot th y → ¬ (y.val ≤ (tVcpuA t).val ∧ (tVcpuA t).val < y.val + 32))
    (P : JWPl V th)
    (hactJ : P1.Aligned (actA st s) ∧ ¬ JW V th (actA st s) ∧ ¬ SW th (actA st s))
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hna : P1.vHeadA st s ≠ actA st s) :
    untyped.decode st arI s ar lbl length (cslotAddr (pp.bv, idx)) (.Untyped p sb fi dev) buf extra ⦃ res =>
      UPost σ (Fl4Spec.fl4DecodeUntypedInvocationV slbl (args.map UScalar.bv) (pp.bv, idx)
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPostV2 (L := L) th (L.mem s) G σ ar V X) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refinesV arI hA th s ar hag σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen
    hargs _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  exact retype_cont_vcpu2 arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU ct hcur hct htcb hact hpp hidx hcap hpal
    hpfit hfi hhigh htop hactZ hfree hzero hunused Vl E hVf hVV hVreg hhdV hhdreg hSV hTV P hactJ hnd hna
    nt us dest off win t r reset fiv (h14 nt hnt0) hctx

end

end
end Fl4Proofs.P3.VirtUtInvV2
