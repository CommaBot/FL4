/-
# P2 (line p3mc, gen 18): st's decline certificate at a view start whose target is another core's

At an st entry `σ` at core `c`'s view of `ρ` (a bundle state `SlJAt`, the st entry facts `StEnt` at `userV K`, the
aligned kernel words the view's, core `c`, locks `hs`) whose target's `AFFINITY` is, in `ρ`, not `c`, U9's
re-annotated armed program (the extracted tree, P2/StFamC) is `Safe` at the physical memory `μ`:

* **`st_cur_home`**: the current thread is homed on `c` in `ρ`. Its `SC` word is the current SC (`StPre.sct`), which is
  no zero word since the layout's heap has no object at 0 (`JKern.h0`) and the current SC is a typed SC
  (`StPre.csc`); a nonzero `SC` word at the view is a homed thread's (`view_tzero_home`).
* **`st_fh_annV`**: the five words the declining run reads — `CUR_THREAD`, `CUR_SC` (core `c`'s node), the caller's
  `MSG_INFO` and `FLAGS` (a homed thread's) and the target's `AFFINITY` (gate-owned at every memory) — are in the
  path's read set `MaxR` at `σ` (as `StOnce.st_hro`'s walk), are no PTE word and keep their owner under the view;
  the first four keep their value (`SR`). `PathObl.st_fh_safe` then gives `Safe`.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.StFhCert
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW GateField tcbOwner)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb TZero decOff_list)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **No object at address 0** in a bundle state's layout (`JKern.h0`). -/
theorem slJAt_heap0 {Kl : KLayout} {s : S} (h : SlJAt (L := L) Kl s) : Kl.heap 0#u64 = none := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact B.j.kern.h0

/-- **The current thread at an st entry of `c`'s view is homed on `c`** (module docstring). -/
theorem st_cur_home {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Cs Ω Sg Ac : Set U64} {target : U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (E : StEnt (userV K.toKLayoutV) st K.toKLayoutV.heap.tcbs Cs Ω K.toKLayoutV.heap Sg K.toKLayoutV.heap.replies
      K.toKLayoutV.heap.scs K.toKLayoutV.heap.ntfns K.toKLayoutV.heap.scBits Ac target σ)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ρ (fld (L.curW σ) oAFFINITY) = c := by
  have hX := hJ.regionOKX
  have h0 := E.inv.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayoutV.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayoutV.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hz := slJAt_heap0 hJ
  have hcsc : L.cscW σ ≠ 0#u64 := by
    intro e
    obtain ⟨z, hz'⟩ := E.pre.csc
    rw [e] at hz'
    have hz2 : K.toKLayout.heap 0#u64 = some (.sc z) := hz'
    rw [hz] at hz2
    cases hz2
  have ha : Aligned (scA (L.curW σ)) := field_aligned ht' (by simp) (by simp)
  have hu : scA (L.curW σ) ∉ K.user := fun hu =>
    E.lay.nu_tcb hcT (k := 3464#u64) (by simp) (by simp) (mem_userV.2 (Or.inl hu))
  have hv : view K.toKLayout c ρ (scA (L.curW σ)) ≠ 0#u64 := by
    rw [← hmm _ ha hu, E.pre.sct]; exact hcsc
  obtain ⟨r, v, -⟩ := hX.tcbW _ htH 3464#u64 (by simp) (by simp) (by simp)
  exact CoreView.view_tzero_home r (by rw [v]; simp [TZero]) hv

set_option maxHeartbeats 8000000 in
/-- **U9's armed st program is `Safe` at a view start whose target is another core's** (module docstring). -/
theorem st_fh_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {Cs Ω Sg Ac : Set U64} {n : I64} {target : U64} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (E : StEnt (userV K.toKLayoutV) st K.toKLayoutV.heap.tcbs Cs Ω K.toKLayoutV.heap Sg K.toKLayoutV.heap.replies
      K.toKLayoutV.heap.scs K.toKLayoutV.heap.ntfns K.toKLayoutV.heap.scBits Ac target σ)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hρ : ρ (affA target) ≠ c) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_set_timer_local n target) ∅ a)) := by
  have hX := hJ.regionOKX
  have hK0 := hJ.regionOK
  obtain ⟨hk, hcp⟩ := hJ.kc
  have hI := E.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayoutV.heap.tcbs := h0.tcbs
  have hN : NodePlaced st K.toKLayoutV.heap.tcbs σ (L.cpu σ) := h0.nodes _ h0.cur
  have hcT : L.curW σ ∈ K.toKLayoutV.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hL := E.lay
  have hcur := st_cur_home hJ E hmm
  -- the path's read set at `σ` (`StOnce.st_hro`'s walk)
  set R' : U64 → Prop := MaxR (userV K.toKLayoutV) st lk σ with eR'
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R' (L.nodeAt σ (L.cpu σ) o) := fun o h1 h2 =>
    ⟨Or.inl (held_core (hL.own_node _ h1)), nodeAt_aligned hN h1 h2, hL.nu_node h1⟩
  have cR : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      R' (core.num.U64.wrapping_add (L.curW σ) k) := fun k h1 h2 h3 h4 => by
    have e := caller_own' hL hT hcT E.pre.aff E.pre.nq h1 h2 h4
    refine ⟨?_, field_aligned ht' h2 h3, hL.nu_tcb hcT h1 h2⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have rR : ∀ r : U64, r.val < 384 → R' (regA (L.curW σ) r) := fun r hr => by
    obtain ⟨k, hk, e⟩ := regA_eq ht' hr
    rw [e]; exact cR k (by omega) (by omega) (by omega) (by omega)
  have htg : target ∈ K.toKLayoutV.heap.tcbs := E.tg
  have htgH : K.toKLayout.heap target = some .tcb := htg
  have rAt : R' (affA target) := ⟨Or.inr (by
      have e := hL.own_tcb hT (L.mem σ) htg (k := 3520#u64) (by simp) (by simp)
      unfold fld at e
      unfold GateOnly affA; rw [e, tcbOwner, if_pos (show GateField (3520#u64).val from Or.inl (by simp))]),
    field_aligned (hT _ htg) (by simp) (by simp), hL.nu_tcb htg (by simp) (by simp)⟩
  -- what the view keeps
  have ndS : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → SR K c ρ (L.nodeAt σ (L.cpu σ) o) := by
    intro o ho h8
    have v := nodeAt_val hN ho
    have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) :=
      hX.node _ _ ⟨hcp, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
        by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
    have hr' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := by rw [hr, hc]
    exact sr_nf hK (by rw [hr']; intro h; cases h) (nf_node hr')
  have W : ∀ b, StFhRd (L := L) σ b → R' b ∧ SR K c ρ b := by
    rintro b (rfl | rfl | rfl | rfl)
    · exact ⟨nR _ (by rw [curth_val]; omega) (by rw [curth_val]),
        ndS _ (by rw [curth_val]; omega) (by rw [curth_val])⟩
    · exact ⟨rR _ (by simp [layout.reg.MSG_INFO]),
        sr_reg hK hX htH hcur (by simp [layout.reg.MSG_INFO])⟩
    · exact ⟨cR _ (by simp) (by simp) (by simp) (by simp),
        sr_tcb hK hX htH hcur (o := 3456#u64) (by simp) (by simp) (by simp)⟩
    · exact ⟨nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
        ndS _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])⟩
  -- the read sets
  let Ro : U64 → Prop := fun q =>
    rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q
  have hR0 : ∀ q, StFhRd (L := L) σ q → Ro q ∧ q ∉ K.user := fun q hq =>
    ⟨⟨⟨(W q hq).1, (W q hq).2.2⟩, (W q hq).2.1.2⟩, fun hu => (W q hq).1.2.2 (mem_userV.2 (Or.inl hu))⟩
  -- the target's `AFFINITY`
  obtain ⟨rA, -, -⟩ := hX.tcbW _ htgH 3520#u64 (by simp) (by simp) (by simp)
  have rA' : region K.toKLayout (affA target) = .tcb target := rA
  have hpA : affA target ∉ K.ptes := fun hp => by
    have h := hK.none _ hp
    rw [rA'] at h
    cases h
  have hgo : Ro (affA target) ∧ affA target ∉ K.user := by
    refine ⟨⟨⟨rAt, hpA⟩, ?_⟩, hX.kern _ (by rw [rA']; intro h; cases h)⟩
    show ownP K (view K.toKLayout c ρ) (affA target) = ownP K ρ (affA target)
    rw [ownP_eq_own nv hpA, ownP_eq_own nv hpA]
    exact (OwnMap.own_aff_gate hK0 htgH _).trans (OwnMap.own_aff_gate hK0 htgH _).symm
  -- the memories
  have hRdρ : ∀ b, StFhRd (L := L) σ b → ρ b = L.mem σ b := fun b hb =>
    (W b hb).2.1.1.symm.trans
      (hmm b (W b hb).1.2.1 (fun hu => (W b hb).1.2.2 (mem_userV.2 (Or.inl hu)))).symm
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm hx.1.1.1
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have h := PathObl.st_fh_safe (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) hmk hA (n := n) (a := a) hc (Ro := Ro)
    (fun b hb => (W b hb).1.2.1) rAt.2.1 hR0 hgo hρ hRdρ hRPO (fun x hx => hV.2.1 x hx)
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
