/-
P3 (DESIGN.md §9), TCB invocations: **SetSchedParams' scheduler step from
`JAtZ`** (the fold's re-scoping of `schedTailXHyp_of`): `JAtZ` after the
fault-handler install (`InstallJ`, the CSpace side's install step, with the
current thread in no release queue), the facts after `set_mcp` carried from
it (a `TView` step), and the spec's facts after `set_priority`
(`SetPrioSpecOK`).
-/
import Fl4Proofs.P3.IpcSchedTail
import Fl4Proofs.P3.IpcCopyRegsJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-- **The spec facts after `set_priority`** [J-step, spec only]: `Inv`,
`ObjCover` and `NSC` at its outcome (l4v `valid_sched`, `valid_objs`). -/
def SetPrioSpecOK (Z : XSets) (p : Fl4Spec.ObjRef) (pr : Fl4Spec.Priority) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ σ', Fl4Spec.setPriority (Z := Unit) p pr σ = ({((), σ')}, False) →
    Inv σ' ∧ ObjCover Z.N Z.T Z.E Z.R Z.C σ' ∧ NSC Z.N Z.C σ'

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
open Fl4Proofs.P3.Notif (inClass released)

/-- **`JAtZ` after SetSchedParams' fault-handler install** [J-step, the
CSpace side's install], with the current thread in no release queue
(l4v `ct_not_in_release_q`), and `SetPrioSpecOK` after the `MCP` write
[J-step, spec only]: at `SchedTailXHyp`'s hypotheses. -/
def InstallJ (AR : A → Fl4Spec.Cr3 → Prop) (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ (s1 : S) (σ1 : Fl4Spec.State Unit) (a : A) (p mcp prio scv x2 : U64) (scf : Bool) (ssl : Fl4Spec.CslotPtr)
    (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr) (q : Fl4Spec.ObjRef) (sco : Option (Option Fl4Spec.ObjRef))
    (s2 : S) (a1 : A) (σ2 : Fl4Spec.State Unit) (G2 : MdbGhost),
    sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    th p = some .tcb → mcp.val < 256 → prio.val < 256 →
    (sco = none ↔ scf = false) → (sco = some none → scv = 0#u64) →
    (∀ v, sco = some (some v) → v = scv.bv ∧ scv ≠ 0#u64) →
    ScDec σ p.bv sco → p ≠ L.idleW s → IsSlot th x2 →
    tcb.install_tcb_cap st arI s1 a p (cslotAddr ssl) layout.tcb.SLOT_FAULT_HANDLER (capV (L.mem s) x2) x2 =
      ok (.Ok (), s2, a1) →
    (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
    DState (L := L) th s2 σ2 G2 → WX (L := L) AR th s2 a1 σ2 G2 →
    ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) (Lst : U64 → List U64) (D : Set U64), Z.th = th ∧
      JAtZ (L := L) arI AR Z H Cs Ac Lst D s2 a1 σ2 ∧ σ2.curThread ∉ σ2.releaseQueue ∧
      ∀ x, σ2.kheap p.bv = some (.tcb x) → SetPrioSpecOK Z p.bv (Fl4Spec.ucast 8 prio.bv)
        (Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }))

set_option maxHeartbeats 32000000 in
/-- **`SchedTailXHyp` from `JAtZ`** (module docstring). Named: the spec's
facts after the install (`hSP`, as `schedTailXHyp_of`); `InstallJ`
[J-step]; the platform's `TimeAgree`, totality and `ARKeep` [P]. -/
theorem schedTailXHypJ {AR : A → Fl4Spec.Cr3 → Prop} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {ct : U64}
    (hStT : P0.StoreTotal st) (hArT : P0.ArchTotal arI) (hAK : ARKeep arI AR) (hTA : TimeAgree arI)
    (hSP : ∀ (σ1 σ2 : Fl4Spec.State Unit) (p : U64) (sco : Option (Option Fl4Spec.ObjRef)) (ssl : Fl4Spec.CslotPtr)
      (fh : Fl4Spec.Cap × Fl4Spec.CslotPtr), ScDec σ p.bv sco →
      Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
      (.ok (), σ2) ∈ ((Fl4Spec.installTcbCap (Z := Unit) p.bv ssl 3 (some fh)).run σ1).1 →
      SpecPost σ2 p.bv sco ∧ ∀ v, sco = some (some v) → ∀ x y n, σ2.kheap p.bv = some (.tcb x) →
        σ2.kheap v = some (.schedContext y n) → Fl4Spec.runnable x.tcbState = false → inClass x.tcbState →
        Fl4Spec.scActive y = true → released σ2 y)
    (hJ2 : InstallJ (L := L) arI AR th s σ ct) :
    SchedTailXHyp (L := L) arI AR th s σ ct := by
  intro s1 σ1 a p mcp prio scv x2 scf ssl fh q sco s2 a1 σ2 G2 hs1 hst1 hp hm hpr h1 h2 h3 hD hpI hx2 hinsI hins hDS
    hWX
  obtain ⟨Z, H, Cs, Ac, Lst, D, hth, J2, hNR2, hPS⟩ :=
    hJ2 s1 σ1 a p mcp prio scv x2 scf ssl fh q sco s2 a1 σ2 G2 hs1 hst1 hp hm hpr h1 h2 h3 hD hpI hx2 hinsI hins hDS hWX
  have hX := J2.xtop
  have hKA := J2.ks
  have hP0 := J2.ip
  have hpT : p ∈ Z.T := J2.thT p (by rw [hth]; exact hp)
  have hAR : AR a1 σ2.archState.x64CurrentCr3 := hX.fin.1.1.2.2.2.2.2.2
  obtain ⟨⟨x, hk2, hA2, hQ2, -, hU2, hB2⟩, hrl⟩ := hSP σ1 σ2 p sco ssl fh hD hst1 hins
  unfold schedTail
  -- `set_mcp`
  rw [set_mcp_eq, bind_ok]
  set σa := Notif.updK σ2 p.bv (.tcb { x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }) with hσa
  have ha : ((), σa) ∈ (Fl4Spec.setMcpriority (Z := Unit) p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 := by
    show _ ∈ (Fl4Spec.threadSet (Z := Unit) _ p.bv σ2).1
    rw [Notif.threadSet_eq _ hk2]; exact Set.mem_singleton _
  have hXa := (hX.tcbWr hpT 3440#u64 (Or.inl rfl) mcp).bufSpec (tcbMcpStep_upd hk2 (Fl4Spec.ucast 8 mcp.bv))
  have hcra : σa.archState.x64CurrentCr3 = σ2.archState.x64CurrentCr3 := rfl
  have hT : P1.TcbPlaced Z.T := hP0.e.tcb
  have hBWa : BufWordRel Z.T (L.mem (L.wr s2 (mcpA p) mcp)) σa := by
    refine J2.buf.frame (fun t ht => ?_) (fun q y hq => ?_)
    · refine Notif.rd_wr_ne (P1.field_aligned (hT p hpT) (by decide) (by decide))
        (P1.field_aligned (hT t ht) (by decide) (by decide)) ?_
      exact Notif.tfield_ne (hT p hpT) (hT t ht) (by decide) (by decide) (fun _ => by decide)
    · by_cases e : q = p.bv
      · subst e; rw [hk2] at hq; cases hq
        exact ⟨{ x with tcbMcpriority := Fl4Spec.ucast 8 mcp.bv }, by simp [hσa, Notif.updK], rfl⟩
      · exact ⟨y, by simp [hσa, Notif.updK, Function.update_of_ne e, hq], rfl⟩
  have hIa := hXa.irelK (by rw [L.ksb_wr]; exact hKA) hBWa
  rw [hcra] at hIa
  -- the facts after `set_mcp`, from `JAtZ` after the install
  have hTVa : TView σ2 σa := TView.upd hk2 rfl rfl rfl rfl
  have hSVa : SchedValid σa := J2.sv.tcbView hTVa rfl
  have hInva : Inv σa := inv_updView J2.inv hk2 ⟨rfl, rfl, rfl, rfl⟩
  have hOCa : ObjCover Z.N Z.T Z.E Z.R Z.C σa := J2.obj.tcbView hTVa
  have hSorta : IpcSorted σa := by
    refine J2.isorted.frame (fun q x' hq => ⟨x', (hTVa.ntcb (fun _ e => by cases e)).1 hq, rfl⟩)
      (fun q x' hq => ⟨x', (hTVa.ntcb (fun _ e => by cases e)).1 hq, rfl⟩) (fun u => ?_)
    unfold prioOf
    rw [tcbsOf_eq, tcbsOf_eq]
    by_cases e : u = p.bv
    · subst e; simp [hσa, Notif.updK, hk2]
    · simp [hσa, Notif.updK, Function.update_of_ne e]
  have hQa := qSorted_of_spec (L := L) hIa.1.toE hIa.1.toN hT hSorta
  have hrela : σa.curThread = p.bv → p.bv ∉ σa.releaseQueue := fun h => by
    have : σ2.curThread = p.bv := h
    rw [← this]; exact hNR2
  -- `set_priority`
  refine WP.spec_bind (set_priority_irel hP0 hIa hpT prio hpr hInva.actReady
    hrela hSVa hInva hOCa (fun e he => hQa e (Or.inl he)) (fun e he => hQa e (Or.inr he))) ?_
  rintro s4 ⟨σb, hsb, hIb⟩
  have hb : ((), σb) ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 prio.bv) σa).1 := by
    rw [hsb]; exact Set.mem_singleton _
  have hv : VK σ2 σb := (presV_setMcpriority _ _ σ2 _ ha).trans (presV_setPriority _ _ σa _ hb)
  obtain ⟨xb, hkb, hstb, hscb⟩ := hv.tcb _ x hk2
  have fin : ∀ (s5 : S) (a5 : A) (σc : Fl4Spec.State Unit), ((), σc) ∈ (scStep p.bv sco σb).1 →
      IRel st Z.th σ2.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s5 σc → AR a5 σ2.archState.x64CurrentCr3 →
      ((core.result.Result.Ok () : core.result.Result Unit error.Exc) = core.result.Result.Ok () ∧ ∃ σa' σb' σc', ((), σa') ∈ (Fl4Spec.setMcpriority (Z := Unit)
        p.bv (Fl4Spec.ucast 8 mcp.bv) σ2).1 ∧ ((), σb') ∈ (Fl4Spec.setPriority (Z := Unit) p.bv (Fl4Spec.ucast 8 prio.bv) σa').1 ∧
        ((), σc') ∈ (scStep p.bv sco σb').1 ∧ RelTopM (L := L) s5 σc' ∧ XTop (L := L) AR s5 a5 σc') := by
    intro s5 a5 σc hc hI5 hAR5
    obtain ⟨⟨Z', -, -, -, -, -, -, -, -, hZ'⟩, -⟩ := IRel.xtop (L := L) (AR := AR) (a := a5) hI5 hAR5
    exact ⟨rfl, σa, σb, σc, ha, hb, hc, (SRT.relTop hI5).1, Z', hZ'⟩
  obtain ⟨hInvb, hOCb, hNb⟩ := hPS x hk2 σb hsb
  cases scf
  · -- no SC step
    have hsco : sco = none := h1.2 rfl
    subst hsco
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨trivial, (fin s4 a1 σb (Set.mem_singleton _) hIb hAR).2⟩
  simp only [↓reduceIte]
  step with Sched.obj.Sc.is_null.spec' as ⟨bz, hbz⟩
  by_cases hs0 : scv = 0#u64
  · -- the unbind
    have hsco : sco = some none := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp)
      | some o =>
        cases o with
        | none => rfl
        | some v => exact absurd hs0 (h3 v rfl).2
    subst hsco
    rw [hbz, decide_eq_true hs0]
    simp only [↓reduceIte]
    obtain ⟨cc, y, n, hcx, hks, hy⟩ := hU2 rfl
    have hksb : σb.kheap cc = some (.schedContext y n) := (hv.sc cc y n).2 hks
    have hxbsc : xb.tcbSchedContext = some cc := by rw [hscb, hcx]
    obtain ⟨Qb, Rb, hcb, hsbl⟩ := hIb.2.2.1.lists
    obtain ⟨xb', hkb', -, -, hscw, -⟩ := hsbl.tcb p hpT
    rw [hkb] at hkb'; cases hkb'
    step with P1.obj.Tcb.sc.spec as ⟨i4, hi4⟩
    have hi40 : i4 ≠ 0#u64 := fun e => by rw [hscw, ← hi4, e, Notif.optRef_zero] at hxbsc; cases hxbsc
    have hi4c : i4.bv = cc := by rw [hscw, ← hi4, Notif.optRef_ne hi40] at hxbsc; exact Option.some.inj hxbsc
    have hi4C : i4 ∈ Z.C := by rw [hi4]; exact hsbl.scMem p hpT (by rw [← hi4]; exact hi40)
    step with Sched.obj.Sc.is_null.spec' as ⟨b1, hb1⟩
    rw [hb1, decide_eq_false hi40]
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (unbind_irel hP0 hIb hNb hInvb hi4C (by rw [hi4c]; exact hksb) hpT hy) ?_
    rintro s5 ⟨σc, hsc, hIc⟩
    rw [WP.spec_ok]
    refine fin s5 a1 σc ?_ hIc hAR
    show _ ∈ ((Fl4Spec.getTcbObjRef (Z := Unit) Fl4Spec.Tcb.tcbSchedContext p.bv >>= fun o =>
      Fl4Spec.NonDet.assertOpt o >>= fun c => Fl4Spec.schedContextUnbindTcb c) σb).1
    rw [nd_bind_one (Endp.getTcbObjRef_eq _ hkb), hxbsc]
    rw [nd_bind_one (show (Fl4Spec.NonDet.assertOpt (some cc) : Fl4Spec.SMonad Unit Fl4Spec.ObjRef) σb =
      ({(cc, σb)}, False) from rfl), ← hi4c, hsc]
    exact Set.mem_singleton _
  · -- the bind
    have hsco : sco = some (some scv.bv) := by
      cases sco with
      | none => exact absurd (h1.1 rfl) (by simp)
      | some o =>
        cases o with
        | none => exact absurd (h2 rfl) hs0
        | some v => rw [(h3 v rfl).1]
    subst hsco
    rw [hbz, decide_eq_false hs0]
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨x0, y, n, hkt0, hxs0, hkc0, hyt0, -, -, -, -, -, -⟩ := hB2 _ rfl
    rw [hk2] at hkt0; cases hkt0
    have hkcb : σb.kheap scv.bv = some (.schedContext y n) := (hv.sc _ y n).2 hkc0
    obtain ⟨c', hc'C, hc'e⟩ := hOCb.sc _ y n hkcb
    have hc' : scv = c' := (P1.eq_of_bv hc'e).symm
    subst hc'
    have hblk : Fl4Spec.runnable xb.tcbState = false → inClass xb.tcbState → Fl4Spec.scActive y = true →
        released σb y := by
      intro hr hc ha'
      rw [hstb] at hr hc
      have := hrl _ rfl x y n hk2 hkc0 hr hc ha'
      unfold released at this ⊢; rw [hv.tm]; exact this
    refine WP.spec_bind (WP.spec_and (bind_irel hP0 s4 a1 hIb hNb hInvb hc'C hs0 hkcb hyt0 hpT hkb
      (by rw [hscb]; exact hxs0) hblk hTA) (AK.schedcontext_bind_tcb hStT hArT hAK hAR)) ?_
    rintro ⟨s5, a5⟩ ⟨⟨σc, hsc, hIc⟩, hAR5⟩
    try simp only [uncurry_apply_pair]
    rw [WP.spec_ok]
    refine fin s5 a5 σc ?_ hIc hAR5
    show _ ∈ (Fl4Spec.schedContextBindTcb (Z := Unit) scv.bv p.bv σb).1
    rw [hsc]; exact Set.mem_singleton _


end

end

end Fl4Proofs.P3
