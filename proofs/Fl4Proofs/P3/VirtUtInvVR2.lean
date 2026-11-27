/-
P3x for virtualization (line virt, gen 27, item 1): **the untyped `Retype` step with VCPUs at `JExtV2`, with the
relation for every old VCPU** — VirtUtInvVR's `RetPostVR` / `retype_cont_vcpuR` / `untyped_retype_vcpuR` /
`RetPostVR.vrelAll` restated over P3/VirtUtInvV2 (`RetPostV2`, `retype_cont_vcpu2`). Same proofs (gen 25's
`cont_vcpu_frame` and `vcpuAt_retStep` are reused unchanged; they never read `JExtV`).

* `RetPostVR2`, **`retype_cont_vcpuR2`**, **`untyped_retype_vcpuR2`** (the step theorem: `untyped_retype_vcpu2`'s
  statement + `hVR`, post `RetPostVR2`), **`RetPostVR2.vrelAll`** (`VRelAll (VsI V rb n)` at the step's single spec
  outcome).

Named premises: as P3/VirtUtInvV2 (`CapAgree` [P], `VirtCodeAgree` [P], `hag` [P], `JWPl` [J], `hactJ` [J], `hnd`
[J]). No new premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtUtInvVR
import Fl4Proofs.P3.VirtUtInvV2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtUtInvVR2
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame
open Fl4Proofs.P3.VirtLoopInv0 Fl4Proofs.P3.VirtLoopSharp Fl4Proofs.P3.VirtRetVcpuPre Fl4Proofs.P3.VirtRetFullV
open Fl4Proofs.P3.VirtUtInvV Fl4Proofs.P3.VirtRetFrameV Fl4Proofs.P3.VirtRetSpecV Fl4Proofs.P3.VirtVKeep Classical

open Fl4Proofs.P3.VirtUtInvVR Fl4Proofs.P3.VirtUtInvV2

noncomputable section
set_option linter.unusedSimpArgs false

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`RetPostVR` at `JExtV2`**: `RetPostV2` and the relation for every old VCPU. -/
def RetPostVR2 {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ar : A')
    (V X : Set U64) (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  RetPostV2 (L := L) th m G σ ar V X inv res ∧
    ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((Fl4Spec.fl4InvokeUntypedV (Z := Unit) inv).run σ1).1, VRelAll V (memW st res.2.1) y.2

set_option maxHeartbeats 4000000 in
/-- **`retype_cont_vcpuR` at `JExtV2`** (same proof, over `retype_cont_vcpu2`). -/
theorem retype_cont_vcpuR2 {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
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
    (hVR : VRelAll V (memW st s) σ)
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
      RetPostVR2 (L := L) th (L.mem s) G σ ar V X (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
  have hmain := retype_cont_vcpu2 arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU ct hcur hct htcb hact hpp hidx hcap
    hpal hpfit hfi hhigh htop hactZ hfree hzero hunused Vl E hVf hVV hVreg hhdV hhdreg hSV hTV P hactJ hnd hna
    nt us dest off win t r reset fiv hnt hctx
  obtain ⟨ht, -, ⟨hdest, hr64, -⟩, ⟨hw1, -, hwin⟩, -, hreset, hfiv, -, hmem, -⟩ := hctx
  have htv : t = .archObject .vcpuObj := by
    rw [hnt, objTypeOf_14] at ht; exact (Option.some.inj ht).symm
  subst htv
  have hres0 : reset = true → fi.val = 0 := fun h => hunused (by rw [h] at hreset; simpa using hreset.symm)
  have hfiv' : fiv = fi := by
    rw [hfiv]
    cases hrs : reset
    · rfl
    · exact UScalar.eq_of_val_eq (by rw [hres0 hrs]; rfl)
  subst hfiv'
  have hframe := cont_vcpu_frame arI ar hA hcA hkA th s G hP hM ct htcb hact hpp hidx hcap hpal hpfit hfi hhigh htop
    hactZ hfree hzero Vl hVf hVV hVreg hhdV hhdreg hSV hTV P hactJ hnd hna nt us dest off win hdest hr64 hw1 hwin hnt
    reset hres0 hmem
  -- the spec's restart, and the untyped cap after it
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, -⟩ := restart_rel hR hV hM hC (SlotsSame.refl th (L.mem s)) (t := ct.bv) hkt .restart
  have hres : reset = true → ∃ d pu sz, Fl4Spec.getCap (Z := Unit) (pp.bv, idx) σ1 =
      ({(.untypedCap d pu sz 0, σ1)}, False) := by
    intro hrs
    have hf0 : fiv = 0#u64 := UScalar.eq_of_val_eq (by rw [hres0 hrs]; rfl)
    have hcap0 := hcap; rw [hf0] at hcap0
    obtain ⟨c, a, hc, hca, hg⟩ := hR1.slot_cap (sl := (pp.bv, idx)) (p := pp) rfl (by simpa [hidx] using hpp)
    rw [hcap0] at hc; have := eq_of_ok_eq hc; subst this
    exact ⟨dev, p.bv, sb.val, by rw [hg, hca.abs]; rfl⟩
  -- old VCPUs are off the new objects
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hz15 : zOf nt.val us.val = 15 := by rw [hnt]; simp [zOf]
  rw [hz15] at hmem
  obtain ⟨hA1, -, hA3, -⟩ := retype_region p fiv sb.val 15 win.val hsb (by norm_num) hpal hpfit hfi hw1 hmem
  rw [show (2 : Nat) ^ 15 = 32768 by norm_num] at hA3
  have hout : ∀ v ∈ V, v.bv ∉ regionPtrs (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
      (windowSlots dest r off.val win.val).length 32768 := by
    intro v hv hm
    rw [windowSlots_length, hz15] at hm
    obtain ⟨j, hj, e⟩ := (mem_regionPtrs _ _ 32768 win.val rfl (by norm_num) (by omega) v).1 hm
    have h1 : j * 32768 + 32768 ≤ win.val * 32768 := by omega
    rcases hVreg v hv with c | c <;> omega
  refine WP.spec_mono (WP.spec_and hmain hframe) ?_
  rintro res ⟨hpost, hag⟩
  refine ⟨hpost, fun σ1' h1 y hy v hv => vrelAt_frameAL (hag v hv) ?_ (hVR v hv)⟩
  have e : σ1' = σ1 := by
    rw [hcur] at h1
    have := congrArg Prod.fst (h1.symm.trans hst1)
    exact congrArg Prod.snd (Set.singleton_eq_singleton_iff.1 this)
  subst e
  exact vcpuAt_retStep hst1 hres hy (hout v hv)

/-- **`untyped_retype_vcpuR` at `JExtV2`**: the step theorem, the relation kept for every VCPU. -/
theorem untyped_retype_vcpuR2 [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (ar : A')
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
    (hVR : VRelAll V (memW st s) σ)
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
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPostVR2 (L := L) th (L.mem s) G σ ar V X) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refinesV arI hA th s ar hag σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen
    hargs _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  exact retype_cont_vcpuR2 arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU ct hcur hct htcb hact hpp hidx hcap hpal
    hpfit hfi hhigh htop hactZ hfree hzero hunused Vl E hVR hVf hVV hVreg hhdV hhdreg hSV hTV P hactJ hnd hna
    nt us dest off win t r reset fiv (h14 nt hnt0) hctx

/-- **The relation for every VCPU after a successful step** (module docstring): `RetPostVR` of a retype gives the
single spec outcome `σ'` and `VRelAll (VsI V rb n)` there. -/
theorem RetPostVR2.vrelAll {A' : Type} {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit}
    {ar : A'} {V X : Set U64} {src : Fl4Spec.CslotPtr} {reset : Bool} {base rb : Fl4Spec.ObjRef}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A'}
    (h : RetPostVR2 (L := L) th m G σ ar V X (.retype src reset base rb t us slots dev) res) :
    res.1 = .Ok () ∧ ∃ σ1 σ', Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
      (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype src reset base rb t us slots dev)).run σ1 =
        ({(.ok (), σ')}, False) ∧
      VRelAll (VsI V rb.toNat slots.length) (memW st res.2.1) σ' := by
  obtain ⟨⟨h1, -, σ1, hs1, σ', -, hrun, -, -, -, -, -, -, -, -, -, -, hnew, -⟩, hold⟩ := h
  refine ⟨h1, σ1, σ', hs1, hrun, fun v hv => ?_⟩
  rcases hv with hv | ⟨j, hj, rfl⟩
  · exact hold σ1 hs1 (.ok (), σ') (by rw [hrun]; exact Set.mem_singleton _) v hv
  · exact hnew j hj

end

end
end Fl4Proofs.P3.VirtUtInvVR2
