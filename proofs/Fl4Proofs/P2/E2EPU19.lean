/-
# P2 (line p3mc, gen 20): U19, vx's `VSafe9` discharged at every vx start

## The vx starts
The vx slot (`vq`'s left summand, `vxSlotP3`) arms `localvm.handle_vcpu_exit_local v n` (the extracted tree,
`vexit_localPathPG2`: no `Classical.choose`'d program). At every vx start the glue's index has `v` the current
thread's bound VCPU (`VxEntJ8N.hv`, part of the start fact), and at a P3 bundle state no thread is bound to a VCPU
(`vOf_zero`), so `v = 0`. The body then reads `CUR_THREAD`, the core, `CUR_SC` and the current thread's `STATE`,
and declines **writing nothing** whatever the state is (`if state ≠ RUNNING_VM then false else if v = 0 then
false`: localvm.rs `handle_vcpu_exit_local`). So the run is a decline at every memory, and U9's re-annotated body is
`Safe` by the real-valued certificate (`ViewSafeReal.safe_tr_of_states`), as for st's foreign target (U17):

* `PathObl.VxRd`, **`PathObl.vx_dec_run`** (the run with `v = 0` on any store answering the three words: declined, no
  write), **`PathObl.vx_fh_safe`** (the function-level certificate, `Hp := ∅`);
* **`vx_fh_annV`**: at a vx entry `σ` of `c`'s view (a P3 bundle state `SlJAt`, core `c`, locks `hs`, the view's
  kernel words) the three words are in the path's read set `VexitRS` (node words of `c`, held; the current thread's
  `STATE`, held: the current thread's `AFFINITY` is the core, `StPre.aff`), no PTE word, no user word, and the view
  keeps their value and owner (`SR`): the current thread is homed on `c` in `ρ` (`vx_cur_home`: its `SC` word is the
  current SC, `StPre.sct`, a typed SC and so not 0, and a nonzero `SC` word at the view is a homed thread's,
  `view_tzero_home`);
* **`vx_annV`**: the start fact `StartV2C` at a vx index gives the glue's state (`Ch σ ∧ VxEntJ8N σ`, so `SlJAt` and
  `v = 0`) and the armed program (`cutP` of the path's body = `tr` on `VexitRS ∖ PTE`, `tr_cut`).

`VxAt` (the vx indices), `U19At := U18At ∨ VxAt`.

## U19
**`serializable_fl4_localU19`** (`ExecWPRV10 (fl4LocW11JC ⊕ invocations) (¬IoIx) U19At StartV2C`);
**`serializable_fl4_localU18of19`**: U18's statement follows from U19.

## Premises of `serializable_fl4_localU19` vs `serializable_fl4_localU18`
* **Removed: `VSafe9` [J] at every vx start** (`vq`'s left summand). Nothing added; family and start facts unchanged
  (`fl4LocW11JC` / `StartV2C` [P]; vx's start clause already names the extracted tree and carries `VxEntJ8N.hv` [P],
  the glue's `v`).
* Open: `VSafe9` [J] at irq (route (a)), vt (`vq`'s right summand) and invocation starts; `VSafe` [J] unchanged.

No existing statement changed except the root import list.

Gen 47 (line p3mc): `vx_fh_annV`'s read-set block split out as `vx_rd_node`, `vx_rd_st`, `vx_fh_rd` (with the words'
region tag) and `vx_annV`'s glue as `vx_start_data`, both shared with P2/InsV15Vx's `InsA` proofs; statements unchanged.
-/
import Fl4Proofs.P2.E2EPU18
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- The three words a vx body with `v = 0` reads (module docstring). -/
def VxRd (σ : S) (b : U64) : Prop :=
  b = L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD ∨ b = L.nodeAt σ (L.cpu σ) layout.node.CUR_SC ∨
    b = core.num.U64.wrapping_add (L.curW σ) 3328#u64

set_option maxHeartbeats 4000000 in
/-- **A vx run with `v = 0` declines writing nothing, on any store answering its three reads** (module
docstring). -/
theorem vx_dec_run {gS : machine.Store S} {R : U64 → Prop} [GRd gS st R] {s : S} {a : A} {n : U64}
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) (h2 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC))
    (h3 : R (core.num.U64.wrapping_add (L.curW s) 3328#u64)) :
    localvm.handle_vcpu_exit_local gS ar s a 0#u64 n = ok (false, s, a) := by
  have h3' : R (stA (L.curW s)) := by rw [Fl4Proofs.P1.stA_eq]; exact h3
  have esc : sched.cur_sc st s = ok (L.cscW s) := eq_of_spec_fd (sched.cur_sc.spec (L := L) s)
  unfold localvm.handle_vcpu_exit_local
  rw [PathObl.sched.cur_thread.guard (gS := gS) s h1, cur_thread_ok, gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok]
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h2, esc]
  simp only [bind_ok, num_domains_ne_one_false, Bool.false_eq_true, ↓reduceIte]
  rw [PathObl.obj.Tcb.state.guard (gS := gS) _ s h3', state_ok']
  simp only [bind_ok]
  by_cases hb : (L.mem s (stA (L.curW s)) != sched.TS_RUNNING_VM) = true
  · rw [if_pos hb]
  · rw [if_neg hb]

set_option maxHeartbeats 4000000 in
/-- **The vx body with `v = 0` is `Safe`** (module docstring; the certificate writes nothing). -/
theorem vx_fh_safe {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} {n : U64} (hc : L.cpu σ = c)
    {Ro : U64 → Prop}
    (hal : ∀ b, VxRd (L := L) σ b → Aligned b)
    (hR0 : ∀ q, VxRd (L := L) σ q → Ro q ∧ ¬ User q)
    (hRdρ : ∀ b, VxRd (L := L) σ b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x) :
    Safe own cls kt c hs μ
      (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.localvm.handle_vcpu_exit_local 0#u64 n) ∅ a) := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vcpu_exit_local mm ar x a 0#u64 n =
        interp mm ar (R.localvm.handle_vcpu_exit_local 0#u64 n) x a :=
    fun mm x a => congrFun (congrFun (vexit_isProg S 0#u64 n A ar mm) x) a
  refine safe_tr_of_states hL hO hmk (Hp := fun _ => False) _ a (fun x hx => hx.elim) hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar
    (R.localvm.handle_vcpu_exit_local 0#u64 n) ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, VxRd (L := L) σ b → L.mem s b = L.mem σ b := fun b hb => by
    rw [hmem b (hal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]; exact hRdρ b hb
  have eN : ∀ o, L.nodeAt s (L.cpu s) o = L.nodeAt σ (L.cpu σ) o := fun o => by
    rw [sc]; exact nodeAt_of_ksb sk _ o
  have hcur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW
    rw [eN]
    exact hag _ (Or.inl rfl)
  have r1 : VxRd (L := L) σ (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := Or.inl (eN _)
  have r2 : VxRd (L := L) σ (L.nodeAt s (L.cpu s) layout.node.CUR_SC) := Or.inr (Or.inl (eN _))
  have r3 : VxRd (L := L) σ (core.num.U64.wrapping_add (L.curW s) 3328#u64) :=
    Or.inr (Or.inr (by rw [hcur]))
  have hg := vx_dec_run ar (gS := PathObl.guard st (VxRd (L := L) σ) (fun _ => False)) (a := a) (n := n) r1 r2 r3
  rw [hp] at hg
  have hW := (interp_guard _ s a _ hg).2
  have hM : localvm.handle_vcpu_exit_local
      (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) ar s a 0#u64 n =
        ok (false, s, a) := by
    haveI iR : GRd (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) st (fun _ => True) :=
      { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    exact vx_dec_run ar (R := fun _ => True) trivial trivial trivial
  rw [hp] at hM
  have hWM := (interp_mguard _ s a _ hM).2
  have hO1 := once_of_guardG (R := VxRd (L := L) σ) (W := fun _ => False) (User := User)
    (fun q hq => (hR0 q hq).2) _ (vexit_noZero 0#u64 n) ∅ ∅ s a _ hg
  have hOnce := once_monoR (R := VxRd (L := L) σ) (R' := Ro) (User := User)
    (fun b hb => (hR0 b hb).1) _ ∅ ∅ ∅ s a hO1 (fun _ h => h)
  refine ⟨s, fun _ => False, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hal b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => hx.elim, fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW GateField TimerField GField tcbOwner)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec nf_node)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- **The current thread at a P3 bundle state of `c`'s view is homed on `c`** (module docstring). -/
theorem vx_cur_home {K : KLayoutP} {c : U64} {ρ : U64 → U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ρ (fld (L.curW σ) oAFFINITY) = c := by
  have hX := hJ.regionOKX
  obtain ⟨Ac, B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have hP := stPre_ofS B.ac
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hz := slJAt_heap0 hJ
  have hcsc : L.cscW σ ≠ 0#u64 := by
    intro e
    obtain ⟨z, hz'⟩ := hP.csc
    rw [e] at hz'
    have hz2 : K.toKLayout.heap 0#u64 = some (.sc z) := hz'
    rw [hz] at hz2
    cases hz2
  have ha : Aligned (scA (L.curW σ)) := field_aligned ht' (by simp) (by simp)
  have hu : scA (L.curW σ) ∉ K.user := hL.nu_tcb hcT (k := 3464#u64) (by simp) (by simp)
  have hv : view K.toKLayout c ρ (scA (L.curW σ)) ≠ 0#u64 := by
    rw [← hmm _ ha hu, hP.sct]; exact hcsc
  obtain ⟨r, v, -⟩ := hX.tcbW _ htH 3464#u64 (by simp) (by simp) (by simp)
  exact CoreView.view_tzero_home r (by rw [v]; simp [CoreView.TZero]) hv

set_option maxHeartbeats 4000000 in
/-- A node word of the core at a P3 bundle state of `c`'s view: in the path's read set, kept by the view, no user
word, region-tagged (`vx_fh_annV`'s read set; gen 47 split). -/
theorem vx_rd_node {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {lk : S → U64 → Prop} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hc : L.cpu σ = c) (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    (VexitRS K.toKLayoutV st lk σ (L.nodeAt σ (L.cpu σ) o) ∧ ¬ L.nodeAt σ (L.cpu σ) o ∈ K.ptes) ∧
      SR K c ρ (L.nodeAt σ (L.cpu σ) o) ∧ L.nodeAt σ (L.cpu σ) o ∉ K.user ∧
      region K.toKLayout (L.nodeAt σ (L.cpu σ) o) ≠ .none := by
  obtain ⟨_, B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st K.toKLayout.heap.tcbs σ (L.cpu σ) := h0.nodes _ h0.cur
  have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := hL.nd o ho
  have hr' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := by rw [hr, hc]
  refine ⟨⟨⟨nodeAt_aligned hN ho h8, Or.inr (rpermV_of_own (fun ⟨w, hw⟩ => by
      have h := hK.base.none w _ hw
      rw [hr] at h
      cases h) (Or.inl (held_core (hL.own_node _ ho))))⟩, fun hp => by
      have h := hK.none _ hp
      rw [hr] at h
      cases h⟩,
    sr_nf hK (by rw [hr']; intro h; cases h) (nf_node hr'), hL.nu_node ho, by rw [hr]; intro h; cases h⟩

set_option maxHeartbeats 4000000 in
/-- The current thread's `STATE` word at a P3 bundle state of `c`'s view: as `vx_rd_node` (gen 47 split). -/
theorem vx_rd_st {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {lk : S → U64 → Prop} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    (VexitRS K.toKLayoutV st lk σ (core.num.U64.wrapping_add (L.curW σ) 3328#u64) ∧
        ¬ core.num.U64.wrapping_add (L.curW σ) 3328#u64 ∈ K.ptes) ∧
      SR K c ρ (core.num.U64.wrapping_add (L.curW σ) 3328#u64) ∧
      core.num.U64.wrapping_add (L.curW σ) 3328#u64 ∉ K.user ∧
      region K.toKLayout (core.num.U64.wrapping_add (L.curW σ) 3328#u64) ≠ .none := by
  have hX := hJ.regionOKX
  obtain ⟨_, B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have hP := stPre_ofS B.ac
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have ht' := hT _ hcT
  have hcur := vx_cur_home hJ hmm
  obtain ⟨r, -, -⟩ := hX.tcbW _ htH 3328#u64 (by simp) (by simp) (by simp)
  have r' : region K.toKLayout (core.num.U64.wrapping_add (L.curW σ) 3328#u64) = .tcb (L.curW σ) := r
  have e := hL.own_tcb hT (L.mem σ) hcT (k := 3328#u64) (by simp) (by simp)
  unfold fld at e
  have g1 : ¬ GateField (3328#u64).val := by simp [GateField]
  have g2 : ¬ TimerField (3328#u64).val := by simp [TimerField]
  have g3 : ¬ GField (3328#u64).val := by simp [GField]
  have eo : OwnMap.own K.toKLayout (L.mem σ) (core.num.U64.wrapping_add (L.curW σ) 3328#u64) =
      .core (L.cpu σ) := by
    rw [e, tcbOwner, if_neg g1, if_neg g2, if_neg g3]
    exact congrArg Owner.core hP.aff
  refine ⟨⟨⟨field_aligned ht' (by simp) (by simp), Or.inr (rpermV_of_own (fun ⟨w, hw⟩ => by
      have h := hK.base.none w _ hw
      rw [r'] at h
      cases h) (Or.inl (held_core eo)))⟩, fun hp => by
      have h := hK.none _ hp
      rw [r'] at h
      cases h⟩,
    sr_tcb hK hX htH hcur (o := 3328#u64) (by simp) (by simp) (by simp),
    hL.nu_tcb hcT (k := 3328#u64) (by simp) (by simp), by rw [r']; intro h; cases h⟩

/-- **The three words a vx body with `v = 0` reads, at a P3 bundle state of `c`'s view** (`vx_fh_annV`'s read set,
gen 47 split; also used by `vx_fh_insA`, P2/InsV15Vx): in the path's read set off the PTE words, kept by the view,
no user word, region-tagged. -/
theorem vx_fh_rd {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {lk : S → U64 → Prop} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    ∀ b, VxRd (L := L) σ b → (VexitRS K.toKLayoutV st lk σ b ∧ ¬ b ∈ K.ptes) ∧ SR K c ρ b ∧ b ∉ K.user ∧
      region K.toKLayout b ≠ .none := by
  rintro b (rfl | rfl | rfl)
  · exact vx_rd_node hK hJ hc _ (by rw [curth_val]; omega) (by rw [curth_val])
  · exact vx_rd_node hK hJ hc _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  · exact vx_rd_st hK hJ hc hmm

set_option maxHeartbeats 8000000 in
/-- **U9's armed vx program with `v = 0` is `Safe` at a view start** (module docstring). -/
theorem vx_fh_annV (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {v n : U64} {σ : S} {a : A} (hv : v = 0#u64)
    (hJ : SlJAt (L := L) K.toKLayout σ) (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (fun x => VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localvm.handle_vcpu_exit_local v n) ∅ a)) := by
  subst hv
  -- the read set
  let Rs : U64 → Prop := fun x => VexitRS K.toKLayoutV st lk σ x ∧ ¬ x ∈ K.ptes
  have W : ∀ b, VxRd (L := L) σ b → Rs b ∧ SR K c ρ b ∧ b ∉ K.user := fun b hb =>
    have h := vx_fh_rd (lk := lk) hK hJ hc hmm b hb
    ⟨h.1, h.2.1, h.2.2.1⟩
  -- the narrowed read set
  let Ro : U64 → Prop := fun q => Rs q ∧ VO K c ρ q
  have hR0 : ∀ q, VxRd (L := L) σ q → Ro q ∧ q ∉ K.user := fun q hq =>
    ⟨⟨(W q hq).1, (W q hq).2.1.1.2⟩, (W q hq).2.2⟩
  have hal : ∀ b, VxRd (L := L) σ b → Aligned b := fun b hb => (W b hb).1.1.1
  -- the memories
  have hRdρ : ∀ b, VxRd (L := L) σ b → ρ b = L.mem σ b := fun b hb =>
    (W b hb).2.1.1.1.symm.trans (hmm b (hal b hb) (W b hb).2.2).symm
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_off hx.1.2, ← hc, ← hl]
      exact po_of_rperm (hx.1.1.2.resolve_left hu)
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have h := PathObl.vx_fh_safe (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar (moveHeldP hK) (ownDepP hK hU) hmk (n := n) (a := a) hc (Ro := Ro)
    hal hR0 hRdρ hRPO (fun x hx => hV.2.1 x hx)
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The vx starts** (`vq`'s left summand). -/
def VxAt (_K : KLayoutP) (_c : U64) (_hs : U64 → Prop) (_ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.vq (.inl _)) => True
  | _ => False

/-- **The exempt starts of U19**: U18's and the vx starts. -/
def U19At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U18At (S := S) K c hs ρ k0 i ∨ VxAt (S := S) K c hs ρ k0 i

set_option maxHeartbeats 4000000 in
/-- **What a vx start gives** (`vx_annV`'s glue, gen 47 split; also used by P2/InsV15Vx's `vx_insA_annV`): the glue
state `σ'` (a P3 bundle state of `c`'s view, core `c`, locks `hs`) with `v = 0`, and the armed body, the cut of the
translated vx tree. -/
theorem vx_start_data {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hf : VxAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    ∃ (σ' : S) (a : A) (lk : S → U64 → Prop) (v n : U64), v = 0#u64 ∧ SlJAt (L := L) K.toKLayout σ' ∧
      L.cpu σ' = c ∧ lk σ' = (fun l => s.lk l = some c) ∧
      (∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x) ∧
      k = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c
        (tr (VexitRS K.toKLayoutV st lk σ') (· ∈ K.user) (OwnMap.cls K.toKLayout)
          (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
          (R.localvm.handle_vcpu_exit_local v n) ∅ a) ∅ := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · rcases j with j | j
    · obtain ⟨hLk, hG0⟩ := hsf
      obtain ⟨q0, ⟨h1, σ, ⟨-, hEn⟩, hG⟩, e⟩ := hG0 (fun s => hLk.kernDetS _ s)
      obtain ⟨σ', a, hσ, hc, hl, hμ, rfl⟩ := hG (vxEu_of (m := view K.toKLayout c ρ) h1.nv hEn)
      subst e
      have hEn' : VxEntJ8N st j K.toKLayoutV σ' := by rw [hσ]; exact hEn
      have hJ : SlJAt (L := L) K.toKLayout σ' := hEn'.ix.ac.slJAt
      have hc' : L.cpu σ' = c := hc
      have hl' : j.lk σ' = (fun l => s.lk l = some c) := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x := hμ
      refine ⟨σ', a, j.lk, j.v, j.n, hEn'.hv.trans (vOf_zero hJ), hJ, hc', hl', hmm, ?_⟩
      unfold LocalPath.body
      rw [hc]
      all_goals rfl
    · exact False.elim hf
  · exact False.elim hf

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every vx start** (module docstring). -/
theorem vx_annV {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : VxAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  obtain ⟨σ', a, lk, v, n, hv0, hJ, hc', hl', hmm, rfl⟩ := vx_start_data st ar hA a0 hsf hf
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  have h := vx_fh_annV ar (masksWr_plain st) hK hU hV (lk := lk) (n := n) (a := a) hv0 hJ hc' hl' hmm
  rw [tr_cut (VexitRS K.toKLayoutV st lk σ') (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
    (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ') (masksOf st σ') ar
    (R.localvm.handle_vcpu_exit_local v n) ∅ a] at h
  exact h

end all

end
end Fl4Proofs.P2.E2EP
