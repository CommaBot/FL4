/-
P3x for virtualization (line virt, gen 25, item 1): **the untyped `Retype` step with VCPUs keeps the VCPU relation
for every VCPU** — gen 24's `untyped_retype_vcpu` (P3/VirtUtInvV) related only the new VCPUs (`RetPostV`'s
`VRelAt` at `σ'` for `vI rb j`); here, from `VRelAll V` at the entry, also every VCPU of `V` (the ones listed
before the step) after it, so `VRelAll (VsI V rb n)` holds after the step.

FL4 source: `crates/fl4-core/src/untyped.rs` l. 70-71 (`set_thread_state(s, ct, TS_RESTART)`, `retype`); the restart
writes the thread's state word and the current core's `SCHED_ACTION` (JExtVSteps' `sts_w`), the retype only
`vcpu::init`'s words and slot words (P3/VirtRetFrameV); neither touches an old VCPU's words other than its `PREV`
link, which the relation does not read. Spec: `setThreadState` keeps every VCPU, the VCPU invocation every VCPU off
its new objects (P3/VirtRetSpecV); with `reset = true` (only on an unused untyped) it is the `reset = false` one
(VirtUtInvV's `fl4InvokeUntypedV_reset_unused`).

* `vcpuAt_retStep`: the spec side of the step for every outcome.
* **`cont_vcpu_frame`**: decode's continuation for type 14 (either `reset`) keeps `AgreeAtAL` at every VCPU of `V`.
* `RetPostVR` = `RetPostV` and `VRelAll V` at every outcome of the spec's invocation after the restart;
  **`retype_cont_vcpuR`**, **`untyped_retype_vcpuR`** (the step theorem, both gate outcomes: `untyped_retype_vcpu`'s
  statement with `hVR : VRelAll V (memW st s) σ` added and `RetPostVR` for `RetPostV`).
* **`RetPostVR.vrelAll`**: on success, `VRelAll (VsI V rb n)` at the step's single spec outcome — the relation for
  every VCPU after the step.

State hypotheses (no premise): `untyped_retype_vcpu`'s, and `hVR` (the relation at the entry). Named premises (all
used unchanged): `CapAgree arI ar` [P], `VirtCodeAgree arI ar` [P] (`retype_full_vcpu`, `retype_vcpu_frame`);
`hag` [P] (VirtUtGateV); `JWPl V th` [J], `hactJ` [J], `hnd` [J] (as `untyped_retype_vcpu`). No new premise. New file
only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtUtInvV
import Fl4Proofs.P3.VirtRetFrameV
import Fl4Proofs.P3.VirtRetSpecV
import Fl4Proofs.P3.VirtVKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtUtInvVR
open fl4_core Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame
open Fl4Proofs.P3.VirtLoopInv0 Fl4Proofs.P3.VirtLoopSharp Fl4Proofs.P3.VirtRetVcpuPre Fl4Proofs.P3.VirtRetFullV
open Fl4Proofs.P3.VirtUtInvV Fl4Proofs.P3.VirtRetFrameV Fl4Proofs.P3.VirtRetSpecV Fl4Proofs.P3.VirtVKeep Classical

noncomputable section
set_option linter.unusedSimpArgs false

/-- **The spec side of the step, every outcome**: the restart keeps every VCPU, the invocation every VCPU off its
new objects. -/
theorem vcpuAt_retStep {t : Fl4Spec.ObjRef} {ts : Fl4Spec.ThreadState} {σ σ1 : Fl4Spec.State Unit}
    (h1 : Fl4Spec.setThreadState (Z := Unit) t ts σ = ({((), σ1)}, False))
    {src : Fl4Spec.CslotPtr} {reset : Bool} {base rb : Fl4Spec.ObjRef} {us : Nat} {slots : List Fl4Spec.CslotPtr}
    {dev : Bool}
    (hres : reset = true → ∃ d pu sz, Fl4Spec.getCap (Z := Unit) src σ1 = ({(.untypedCap d pu sz 0, σ1)}, False))
    {y : Except Unit Unit × Fl4Spec.State Unit}
    (hy : y ∈ ((Fl4Spec.fl4InvokeUntypedV (Z := Unit)
      (.retype src reset base rb (.archObject .vcpuObj) us slots dev)).run σ1).1)
    {o : Fl4Spec.ObjRef} (ho : o ∉ regionPtrs rb slots.length 32768) :
    Fl4Spec.vcpuAt y.2 o = Fl4Spec.vcpuAt σ o := by
  have e1 : Fl4Spec.vcpuAt σ1 o = Fl4Spec.vcpuAt σ o :=
    congrFun (vc_setThreadState t ts σ ((), σ1) (by rw [h1]; exact Set.mem_singleton _)) o
  rw [← e1]
  cases reset
  · exact vcpuAt_invokeV src base rb us slots dev hy ho
  · obtain ⟨d, pu, sz, hg⟩ := hres rfl
    rw [fl4InvokeUntypedV_reset_unused src base rb (.archObject .vcpuObj) us slots dev σ1 hg] at hy
    exact vcpuAt_invokeV src base rb us slots dev hy ho

theorem agAL_trans {m1 m2 m3 : Fl4Spec.Word → Fl4Spec.Word} {v : Fl4Spec.Word} (h1 : AgreeAtAL m1 m2 v)
    (h2 : AgreeAtAL m2 m3 v) : AgreeAtAL m1 m3 v :=
  fun o a b c d => (h2 o a b c d).trans (h1 o a b c d)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **decode's continuation for type 14 keeps every old VCPU's words but its links** (module docstring). -/
theorem cont_vcpu_frame {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
    (hcA : CapAgree arI ar) (hkA : VirtCodeAgree arI ar)
    (th : TypedHeap) (s : S) (G : MdbGhost) (hP : Placed th) (hM : MdbLinks th (L.mem s) G)
    (ct : U64) (htcb : th ct = some .tcb)
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
    {V : Set U64} (Vl : VList st V th s)
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
    (nt us dest off win : U64) {r : Nat} (hdest : th dest = some (.cnode r)) (hr64 : r < 64)
    (hw1 : 1 ≤ win.val) (hwin : off.val + win.val ≤ 2 ^ r) (hnt : nt.val = 14) (reset : Bool)
    (hreset : reset = true → fi.val = 0)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) reset
        ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev) ⦃ res =>
      ∀ v ∈ V, AgreeAtAL (memW st s) (memW st res.2.1) v.bv ⦄ := by
  -- the restart
  have hTa := (hTV ct htcb).1
  have hSct : SW th (P1.stA ct) := ⟨ct, htcb, rfl⟩
  have hne : actA st s ≠ P1.stA ct := fun e => hactJ.2.2 ⟨ct, htcb, e⟩
  obtain ⟨s2, hs2, hSS⟩ := spec_exists (set_thread_state_slots (L := L) th hP s ct sched.TS_RESTART htcb hact)
  obtain ⟨s2', hs2', hW, -⟩ := spec_exists (sts_w (L := L) s ct sched.TS_RESTART (P.sw _ hSct) hactJ.1 hne)
  rw [hs2] at hs2'; have := eq_of_ok_eq hs2'; subst this
  rw [hs2]; simp only [bind_ok]
  have hk2 : L.ksb s2 = L.ksb s := hW.1
  have hhd2 : P1.vHeadA st s2 = P1.vHeadA st s := by unfold P1.vHeadA; rw [hk2]
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hsl : IsSlot th (cslotAddr (pp.bv, idx)) := hAs.isSlot
  have hcap1 : capAt (L.mem s2) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev) := by
    rw [hSS.capAt hsl]; exact hcap
  have hzero1 : ZeroRegion (L.mem s2) (p.val + fi.val) (p.val + 2 ^ sb.val) := by
    intro w hw h1 h2
    rw [hW.mem_eq hw (by
      rintro (e | e)
      · subst e
        have e4 : objSize ObjKind.tcb = 4096 := rfl
        have := lay_stA_val hTa
        rcases hfree ct _ htcb with h | h <;> omega
      · subst e; exact hactZ ⟨h1, h2⟩)]
    exact hzero w hw h1 h2
  have Vl2 : VList st V th s2 := Vl.writes hW (fun b hb => ⟨Vl.lw_al hVf hb, by
    rcases hb with rfl | ⟨w, hw, rfl | rfl⟩
    · rintro (e | e)
      · exact Vl.hd.2.2 ⟨ct, htcb, e⟩
      · exact hna e
    · have hn := lay_next_val (hVf w hw).2
      have hT := (hTV ct htcb).2.2.1 w hw
      rintro (e | e)
      · have := congrArg UScalar.val e; have := lay_stA_val hTa; omega
      · have := congrArg UScalar.val e; have := hnd _ (Or.inr rfl) w hw; omega
    · have hn := lay_prev_val (hVf w hw).2
      have hT := (hTV ct htcb).2.2.1 w hw
      rintro (e | e)
      · have := congrArg UScalar.val e; have := lay_stA_val hTa; omega
      · have := congrArg UScalar.val e; have := hnd _ (Or.inr rfl) w hw; omega⟩)
  have hnx2 : nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) = 0#u64 ∨
      IsSlot th (nextOf (L.mem s2) (cslotAddr (pp.bv, idx))) := by
    have hxm : cslotAddr (pp.bv, idx) ∈ G.chains.flatten := (hM.members _).2 ⟨hsl, _, hcap, by simp⟩
    have e : nextOf (L.mem s2) (cslotAddr (pp.bv, idx)) = nextOf (L.mem s) (cslotAddr (pp.bv, idx)) := by
      unfold nextOf; rw [(hSS _ hsl).2.2.2]
    rw [e]
    rcases hM.next_mem hxm with h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr ((hM.members _).1 h1).1
  -- the restart's words are off `V`
  have hS : ∀ v ∈ V, AgreeAtAL (memW st s) (memW st s2) v.bv := fun v hv =>
    agreeAL_of_off (hVf v hv) hW (by
      rintro b (rfl | rfl) hal
      · have e := lay_stA_val hTa; have := (hTV ct htcb).2.2.1 v hv; unfold P1.Aligned at hal
        have := (hVf v hv).1; omega
      · have := hnd _ (Or.inr rfl) v hv; unfold P1.Aligned at hal; have := (hVf v hv).1; omega)
  -- the region
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hz15 : zOf nt.val us.val = 15 := by rw [hnt]; simp [zOf]
  rw [hz15] at hmem
  rw [hz15]
  obtain ⟨hA1, hA2, hA3, -⟩ := retype_region p fi sb.val 15 win.val hsb (by norm_num) hpal hpfit hfi hw1 hmem
  rw [show (2 : Nat) ^ 15 = 32768 by norm_num] at hA2 hA3
  set Ab := Fl4Spec.alignUp (p.bv + fi.bv) 15 with hAbdef
  set A := Ab.toNat with hAdef
  have RP : RPl st V A win.val (P1.vHeadA st s2) :=
    { bal := hA2, b0 := by omega, bfit := by omega, vf := hVf, vv := hVV
      vw := fun w hw => by rcases hVreg w hw with h | h <;> [left; right] <;> omega
      hv := by rw [hhd2]; exact hhdV
      hw := by rw [hhd2]; rcases hhdreg with h | h <;> [left; right] <;> omega }
  have hSW : ∀ y, IsSlot th y → (y.val + 32 ≤ A ∨ A + win.val * 32768 ≤ y.val) ∧
      ((P1.vHeadA st s2).val + 8 ≤ y.val ∨ y.val + 32 ≤ (P1.vHeadA st s2).val) ∧
      ∀ w ∈ V, y.val + 32 ≤ w.val ∨ w.val + 32768 ≤ y.val := by
    intro y hy
    rw [hhd2]
    refine ⟨?_, (hSV y hy).1, (hSV y hy).2⟩
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP hy
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hwz : WinZero (L.mem s2) A 32768 win.val False := fun w hw h1 h2 =>
    Or.inl (hzero1 w hw (by omega) (by omega))
  have hF : untyped.retype st arI s2 ar (cslotAddr (pp.bv, idx)) false ⟨Ab⟩ nt us dest off win dev ⦃ res =>
      ∀ v ∈ V, AgreeAtAL (memW st s) (memW st res.2.1) v.bv ⦄ :=
    WP.spec_mono (retype_vcpu_frame (ar := arI) (a := ar) hA hcA hkA RP rfl hP hSW hsl hcap1 hnx2 hdest
      (by omega) off win rfl hwin Vl2 hwz nt us hnt ⟨Ab⟩ rfl dev)
      fun res h v hv => agAL_trans (hS v hv) (agreeAL_of_retW RP (fun y hy => (hSV y hy).2) h.2 hv)
  cases reset
  · exact hF
  · have hf0 : fi = 0#u64 := UScalar.eq_of_val_eq (by rw [hreset rfl]; rfl)
    have hcap0 := hcap1; rw [hf0] at hcap0
    rw [retype_reset_unused (L := L) arI s2 ar _ _ nt us dest off win dev hcap0]
    exact hF

/-- **The post of the VCPU retype step with the relation for every old VCPU** (module docstring). -/
def RetPostVR {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ : Fl4Spec.State Unit) (ar : A')
    (V X : Set U64) (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  RetPostV (L := L) th m G σ ar V X inv res ∧
    ∀ σ1, Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) →
      ∀ y ∈ ((Fl4Spec.fl4InvokeUntypedV (Z := Unit) inv).run σ1).1, VRelAll V (memW st res.2.1) y.2

set_option maxHeartbeats 4000000 in
/-- **decode's success continuation for type 14, with the relation for every old VCPU** (module docstring). -/
theorem retype_cont_vcpuR {A' : Type} (arI : machine.Arch A') (ar : A') (hA : P0.ArchTotal arI)
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
      RetPostVR (L := L) th (L.mem s) G σ ar V X (.retype (pp.bv, idx) reset p.bv
        (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
  have hmain := retype_cont_vcpu arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU ct hcur hct htcb hact hpp hidx hcap
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

/-- **The untyped `Retype` step with VCPUs, the relation kept for every VCPU** (module docstring). -/
theorem untyped_retype_vcpuR [Fl4Proofs.P1.PlainStore st] {A' : Type} (arI : machine.Arch A') (ar : A')
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
        (absCap (.Untyped p sb fi dev)) excaps) s ar (RetPostVR (L := L) th (L.mem s) G σ ar V X) res ⦄ := by
  have hAs : AbsSlot th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  refine untyped_decode_refinesV arI hA th s ar hag σ G hR hV hP hM hC hI lbl slbl hlbl length buf ct hct args hlen
    hargs _ (pp.bv, idx) rfl hAs p sb fi dev hcap extra x0 hx0 excaps hex hfan _ ?_
  intro nt us dest off win t r reset fiv hnt0 hctx
  exact retype_cont_vcpuR arI ar hA hcA hkA th s σ G hR hV hP hM hC hI hU ct hcur hct htcb hact hpp hidx hcap hpal
    hpfit hfi hhigh htop hactZ hfree hzero hunused Vl E hVR hVf hVV hVreg hhdV hhdreg hSV hTV P hactJ hnd hna
    nt us dest off win t r reset fiv (h14 nt hnt0) hctx

/-- **The relation for every VCPU after a successful step** (module docstring): `RetPostVR` of a retype gives the
single spec outcome `σ'` and `VRelAll (VsI V rb n)` there. -/
theorem RetPostVR.vrelAll {A' : Type} {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} {σ : Fl4Spec.State Unit}
    {ar : A'} {V X : Set U64} {src : Fl4Spec.CslotPtr} {reset : Bool} {base rb : Fl4Spec.ObjRef}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A'}
    (h : RetPostVR (L := L) th m G σ ar V X (.retype src reset base rb t us slots dev) res) :
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
end Fl4Proofs.P3.VirtUtInvVR
