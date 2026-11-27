/-
P3x for virtualization (line virt, gen 24, item 1c): **the untyped `Retype` invocation step with VCPUs** — FL4's
`untyped::decode` (with its tail `set_thread_state Restart`, `retype`) for type 14 = `X86Vcpu` against the gated spec
decoder `fl4DecodeUntypedInvocationV`, the spec's `setThreadState Restart` and `fl4InvokeUntypedV`, for both gate
outcomes.

FL4 source: `crates/fl4-core/src/untyped.rs` l. 25-72 (`decode`: gate l. 42-43, `set_thread_state(s, ct,
TS_RESTART)` l. 70, `retype` l. 71), l. 57-60 (`ensure_no_children` Ok ⇒ `free_index = 0`, `reset = true`),
`retype` with `reset = true` on an unused untyped (free index 0) runs a no-op `reset_untyped`
(UntypedSuccess's `retype_reset_unused`), so it is the `reset = false` retype (VirtRetFullV's `retype_full_vcpu`).

* `objTypeOf_14`: type number 14 is `.archObject .vcpuObj` (`archDataToObjType 7`).
* `fl4InvokeUntypedV_reset_unused`: the spec's `fl4InvokeUntypedV` with `reset = true` on an unused untyped cap is
  the `reset = false` one (UntypedSuccess's `invokeUntyped_reset_unused`, the VCPU hook does not read `reset`).
* `RetPostV`: the post of a VCPU retype step — FL4 `Ok`, arch state kept; the spec's `setThreadState Restart` then
  `fl4InvokeUntypedV inv` have single outcomes `σ1`, `σ'`; StateRel / SlotsValid / MdbLinks / CdtRel / MdbInv / UtInv
  at the (unchanged) typed heap, MdbStep from the entry, FinInv kept; and with `rb` the invocation's retype base and
  `n` its window length: `VList` and **`JExtV` over `VsI V rb n`**, **`VRelAt` at `σ'` for every new VCPU**, and
  RetExp with the caps `vcj rb`.
* **`retype_cont_vcpu`**: decode's success continuation for type 14 (`set_thread_state Restart`, `retype`, either
  `reset`) satisfies `RetPostV`. The restart's footprint (JExtVSteps' `sts_w`: the thread's state word and the
  current core's `SCHED_ACTION` word) misses the slots (`set_thread_state_slots`), the free region, the list words
  of `VList` and the words `JExtV` reads, so `retype_full_vcpu`'s entry facts hold after it.
* **`untyped_retype_vcpu`**: **the step theorem**: for a message whose type word is 14, FL4's `untyped::decode`
  ⦃ `UPost σ (fl4DecodeUntypedInvocationV …) s ar (RetPostV …)` ⦄ — either both refuse with related errors and
  nothing changes (the VT-x gate closed, `virtKind = none`: `InvalidArgument 0`; or any earlier/later check), or the
  spec decodes the `Retype` of `.archObject .vcpuObj` and `RetPostV` holds (VirtUtGateV's `untyped_decode_refinesV`
  with this file's continuation).

State hypotheses (no premise): `retype_full_vcpu`'s (placement of `V`, the head word, the slots and TCBs; `htop`;
`hfree`/`hzero`; `VList V`, `JExtV V X`), `retype_cont`'s for the restart (`hcur`, `hct`, `htcb`, `hact`,
`hactZ`, `hunused`: an untyped cap without children is unused, as UntypedInvoke), and for the restart's words:
`hna` (the `SCHED_ACTION` word is not the list head word: the head is the kernel-state block's word 80, node words
lie at `ksb + 13568 + cpu * 4288 + off`, fl4-core layout.rs `ks` / `node`; at a joint state VirtHns'
`JAtZ.head_ne_act`). At a joint state the restart premises below are `JAtZ.jwPl`, `JAtZ.hact`, `JAtZ.hnd` (with
`JVm`).

Named premises (all used unchanged): `CapAgree arI ar` [P], `VirtCodeAgree arI ar` [P] (`retype_full_vcpu`);
`hag` [P] (platform agreement, VirtUtGateV); `JWPl V th` [J] (JExtVSteps: placement of the words `JExtV` reads;
`JAtZ.jwPl` at a joint state); `hactJ` [J] (sts_jv's `hact`: the `SCHED_ACTION` word aligned, none of `JW`/`SW`;
`JAtZ.hact` at a joint state); `hnd` [J] (VirtVCappedDel / vcpu_finalise_vl's: the current core's node words apart
from `V`'s VCPUs; `JAtZ.hnd` at a joint state). No new premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtUtGateV
import Fl4Proofs.P3.VirtRetFullV
import Fl4Proofs.P3.UntypedInvoke
import Fl4Proofs.P3.JExtVLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtUtInvV
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame
open Fl4Proofs.P3.VirtLoopInv0 Fl4Proofs.P3.VirtLoopSharp Fl4Proofs.P3.VirtRetVcpuPre Fl4Proofs.P3.VirtRetFullV Classical

noncomputable section
set_option linter.unusedSimpArgs false

theorem objTypeOf_14 : objTypeOf 14 = some (.archObject .vcpuObj) := by
  unfold objTypeOf Fl4Spec.archDataToObjType; simp

theorem windowSlots_length (dest : U64) (r off win : Nat) : (windowSlots dest r off win).length = win := by
  simp [windowSlots]

theorem run_bind_congr' {σ ε α β : Type} {m m' : Fl4Spec.NonDetE σ ε α} {s : σ} (h : m.run s = m'.run s)
    (k : α → Fl4Spec.NonDetE σ ε β) : (m >>= k).run s = (m' >>= k).run s := by
  simp only [ExceptT.run_bind]
  show (ExceptT.run m >>= _) s = (ExceptT.run m' >>= _) s
  simp only [nd_bind_apply, h]

/-- The spec's VCPU-extended untyped invocation with `reset = true` on an unused untyped cap. -/
theorem fl4InvokeUntypedV_reset_unused (srcSl : Fl4Spec.CslotPtr) (base rb : Fl4Spec.ObjRef)
    (t : Fl4Spec.ApiObjectType) (us : Nat) (slots : List Fl4Spec.CslotPtr) (dev : Bool) (σ : Fl4Spec.State Unit)
    {d : Bool} {p : Fl4Spec.ObjRef} {sb : Nat}
    (hg : Fl4Spec.getCap (Z := Unit) srcSl σ = ({(.untypedCap d p sb 0, σ)}, False)) :
    (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype srcSl true base rb t us slots dev)).run σ =
      (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype srcSl false base rb t us slots dev)).run σ := by
  have h := invokeUntyped_reset_unused Fl4Spec.fl4ObjBitsApi srcSl base rb t us slots dev σ hg
  unfold Fl4Spec.fl4InvokeUntypedV
  dsimp only
  exact run_bind_congr' h _

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **The post of the VCPU retype step** (module docstring). -/
def RetPostV {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ar : A')
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
        JExtV (L := L) (VsI V rb.toNat slots.length) X th res.2.1 ∧
        (∀ j, j < slots.length → VRelAt (memW st res.2.1) σ' (vI rb.toNat j).bv) ∧
        ∃ dslot, RetExp th th m (L.mem res.2.1) G G' rb.toNat 32768 slots.length dslot (vcj rb.toNat)
          (cslotAddr src) ∧ DslotC th dslot slots.length

set_option maxHeartbeats 4000000 in
/-- **decode's success continuation for type 14** (module docstring). -/
theorem retype_cont_vcpu {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
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
    {V X : Set U64} (Vl : VList st V th s) (E : JExtV (L := L) V X th s)
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
      RetPostV (L := L) th (L.mem s) G σ ar V X (.retype (pp.bv, idx) reset p.bv
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
  have E2 : JExtV (L := L) V X th s2 := E.of_writes P hW (by
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
  have hfull := retype_full_vcpu (L := L) arI ar hA hcA hkA th s2 σ1 G hR1 hV1 hP hM1 hC1 hI1 hU1 hpp hidx hcap1
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
        JExtV (L := L) (VsI V (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)).toNat win.val) X th res.2.1 ∧
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
      RetPostV (L := L) th (L.mem s) G σ ar V X (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) (.archObject .vcpuObj) us.val
        (windowSlots dest r off.val win.val) dev) res := by
    rintro res ⟨h1, h2, σ', G', hrun, hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hVl', hE', hVR', dslot, hEx,
      -, hdsC⟩ he
    refine ⟨h1, h2, σ1, by rw [hcur]; exact hst1, σ', G', he.trans hrun, hR', hV', hM', hC', hI', hU',
      MdbStep.same_left hM hSS hSt', fun hFI => hFin (hFI.of_same hM hSS (ksub_of_eq (setThreadState_nks _ _) hst1)),
      ?_⟩
    show VList st (VsI V _ (windowSlots dest r off.val win.val).length) th res.2.1 ∧ _
    rw [windowSlots_length]
    exact ⟨hVl', hE', hVR', dslot, hEx.same_left hM hSS, hdsC⟩
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

/-- **The untyped `Retype` step with VCPUs, both gate outcomes** (module docstring). -/
theorem untyped_retype_vcpu [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (ar : A')
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
    {V X : Set U64} (Vl : VList st V th s) (E : JExtV (L := L) V X th s)
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
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPostV (L := L) th (L.mem s) G σ ar V X) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refinesV arI hA th s ar hag σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen
    hargs _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  exact retype_cont_vcpu arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU ct hcur hct htcb hact hpp hidx hcap hpal
    hpfit hfi hhigh htop hactZ hfree hzero hunused Vl E hVf hVV hVreg hhdV hhdreg hSV hTV P hactJ hnd hna
    nt us dest off win t r reset fiv (h14 nt hnt0) hctx

end

end
end Fl4Proofs.P3.VirtUtInvV
