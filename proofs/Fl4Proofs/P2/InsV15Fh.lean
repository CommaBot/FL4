/-
# P2 (line p3mc, gen 49): the foreign-handler pattern — `InsA` of a declining body from its run at one store state;
`InsV15V` at every vmF start

## 1. The pattern (shared by the vmF, sl and vmR foreign-handler certificates)
The `VSafe9` certificates of the foreign-handler branches (`vm_fh_safe`, P2/VmFhSafe; `sl_fh_safe`, P2/SlFhCert;
`rr_fh_safe`, P2/RrFhSafe) are `safe_tr_of_states` with, for each admissible `ν`, the store state of
`exists_mem_state` (`ν` on the words read, `ρ` elsewhere), on which the run declines on a guard `guard st Rg Wd`
with `StepOK` per write and `Once`. What that run needs of the state is only that it carries `ρ` on a carried set
`Rc` (the words `σ` and `ρ` agree on, plus the decisive `AFFINITY`), all readable at `μ`.

* **`PathObl.insA_narrow_tr_gd`**: from such a run oracle (`hgo`: at every state with `σ`'s constants carrying `ρ` on
  `Rc`, the run on `guard st Rg Wd` is ok, `StepOK` per write, `Once` for `R0 ∧ Qv`) whose guard read set `Rg` and
  write set `Wd` avoid `G`, the re-annotated body `narrowSP cls kt c Qv ∅ (tr R0 … kv p ∅ a)` is `InsA G …` at `μ`
  (`insA_narrow_tr_of_states`, P2/InsV15Cert; `InsT` by `insT_of_within`). Unlike `insA_narrow_tr_wrU`, the guard read
  set need not be carried (vmF's guard reads the handler's `REPLY` word, which is not known readable at `μ`).

## 2. vmF
* **`PathObl.vm_fh_insA`**: the `InsA` twin of `vm_fh_safe`, by the pattern and `vm_fh_run` (split out of
  `vm_fh_safe`'s proof in place this generation, P2/VmFhSafe, statement of `vm_fh_safe` unchanged).
* `RTW K b` (region-tagged or kernel-static word), **`vmFhR_rt`** (every word `VmFhR` names is one: node, kernel
  static, slot, endpoint, TCB and SC words), `rt_notPWE` (with `IoRS (userP K)`: no paging word of the epoch).
  So the read set of `vmF_fh_annV`, cut by `RTW`, avoids `PWE K E'`.
* **`vmF_fh_insA_annV`**: the `InsA` counterpart of `vmF_fh_annV` (P2/VmFhView), read set
  `(IoRS (userP K) ∧ VN) ∧ RTW`.
* **`vmF_k0_insA`**: the vmF body's re-annotation is `InsA` at every view start with action 0 (homed branch:
  `vmF_k0_nar` + `w11A_noGS` + `LocalPath.insAVQ`; foreign branch: `vmF_fh_insA_annV`), as `vmF_k0_safe` (P2/E2EPU12).
* **`vmF_insA_annV`**, `VmFPm`, **`insAP_vmF_view`**: `InsV15V`'s obligation of `nativePmKAD B` at every vmF start
  without a VCPU.

No named premise. Existing file touched: P2/VmFhSafe (`vm_fh_run` split out of `vm_fh_safe`); every existing
statement byte-identical.
-/
import Fl4Proofs.P2.InsV15SlR
import Fl4Proofs.P2.VmFhView
import Fl4Proofs.P2.E2EPU12
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq InsT insT_of_within
  insA_narrow_tr_of_states)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsA narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The foreign-handler pattern: `InsA` of the re-annotated body from its guarded run at every state carrying `ρ`
on `Rc`** (module docstring §1). -/
theorem insA_narrow_tr_gd {X : Type} {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (p : SProg X)
    (hc : L.cpu σ = c) {R0 Qv Rc Rg Wd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hcal : ∀ b, Rc b → Aligned b) (hR0 : ∀ q, Rc q → (R0 q ∧ Qv q) ∧ ¬ User q)
    (hgal : ∀ b, Rg b → Aligned b) (hRgG : ∀ b, Rg b → ¬ G b) (hWdG : ∀ b, Wd b → User b ∨ ¬ G b)
    (hWd : ∀ x, Wd x → Aligned x ∧ (¬ User x → HeldV c hs (own μ x)))
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hgo : ∀ s : S, L.cpu s = L.cpu σ → L.ksb s = L.ksb σ → st.frame_masks s = st.frame_masks σ →
      (∀ b, Rc b → L.mem s b = ρ b) →
      ∃ r, interp (guard st Rg Wd) ar p s a = ok r ∧
        WithinM st ar (fun x y => StepOK own cls kt User c hs (L.mem x) (L.mem y)) p s a ∧
        Once st ar (fun x => R0 x ∧ Qv x) User ∅ ∅ p s a) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅ (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar p ∅ a)) := by
  refine insA_narrow_tr_of_states hQ hL hO hmk hGo hGko hGQ (Hp := fun x => Wd x ∧ ¬ User x) p a
    (fun x hx => (hWd x hx.1).2 hx.2) hRPO ?_
  intro ν hν
  generalize hq : tr (fun x => R0 x ∧ Qv x) User cls kt c (L.ksb σ) (masksOf st σ) ar p ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, (R0 b ∧ Qv b) → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, Rc b → L.mem s b = ρ b := fun b hb => by
    rw [hmem b (hcal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]
  obtain ⟨r, hg, hWM, hOnce⟩ := hgo s sc sk sm hag
  have hW := (interp_guard _ s a r hg).2
  refine ⟨s, Wd, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hgal b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨(hWd x hx).1, fun hu => ⟨hx, hu⟩⟩, fun x hx hxa => by rw [hmem x hxa, if_pos hx],
    fun x hxa hu' hne hpo => hne ?_, insT_of_within p s a (Within.mono hRgG hWdG p s a hW),
    Within.mono (fun b hb hg => absurd hg (hRgG b hb)) (fun _ _ => trivial) _ s a hW⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

set_option maxHeartbeats 4000000 in
/-- **The VM-fault body at an entry whose fault handler is another core's is `InsA` in its re-annotated form** (the
`InsA` twin of `vm_fh_safe`; module docstring §2). -/
theorem vm_fh_insA {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b) (hA : P0.ArchTotal ar) (addr code : U64)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (hc : L.cpu σ = c)
    {R0 Qv Rd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q)
    (rT : Rd (ctA (L := L) σ)) (rN : Rd (cnA (L := L) σ))
    (rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD))
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1)) (F : VmFhR st Rd σ s1)
    {sl ptr badge : U64} {x' y g gr : Bool}
    (hsl : obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr))
    (hst : L.epState s1 ptr = obj.EP_RECV)
    (hAo : (R0 (affA (L.mem s1 (epHeadA ptr))) ∧ Qv (affA (L.mem s1 (epHeadA ptr)))) ∧
      ¬ User (affA (L.mem s1 (epHeadA ptr))))
    (hdA : Aligned (affA (L.mem s1 (epHeadA ptr)))) (hdR : Aligned (replyA (L.mem s1 (epHeadA ptr))))
    (hdT : affA (L.mem s1 (epHeadA ptr)) ≠ ctA (L := L) σ ∧ affA (L.mem s1 (epHeadA ptr)) ≠ cnA (L := L) σ)
    (hρd : ρ (affA (L.mem s1 (epHeadA ptr))) ≠ c)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hH : ∀ x, (x = ctA (L := L) σ ∨ x = cnA (L := L) σ) → HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v)))
    (hRdG : ∀ b, Rd b → ¬ G b) (hRG : ¬ G (replyA (L.mem s1 (epHeadA ptr))))
    (hAG : ¬ G (affA (L.mem s1 (epHeadA ptr)))) (hTG : ¬ G (ctA (L := L) σ)) (hNG : ¬ G (cnA (L := L) σ)) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅
        (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_vm_fault_local addr code) ∅ a)) := by
  refine insA_narrow_tr_gd ar hQ hL hO hmk hGo hGko hGU _ hc hGQ
    (Rc := fun b => Rd b ∨ b = affA (L.mem s1 (epHeadA ptr)))
    (Rg := fun b => Rd b ∨ b = replyA (L.mem s1 (epHeadA ptr)) ∨ b = affA (L.mem s1 (epHeadA ptr)))
    (Wd := fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ)
    (by rintro b (hb | rfl); exacts [hRal b hb, hdA])
    (by rintro q (hq | rfl); exacts [hR0 q hq, hAo])
    (by rintro b (hb | rfl | rfl); exacts [hRal b hb, hdR, hdA])
    (by rintro b (hb | rfl | rfl); exacts [hRdG b hb, hRG, hAG])
    (by rintro b (rfl | rfl); exacts [Or.inr hTG, Or.inr hNG])
    (fun x hx => ⟨by rcases hx with rfl | rfl; exacts [hRal _ rT, hRal _ rN], fun _ => hH x hx⟩)
    hRPO hρμ ?_
  intro s sc sk _ hag
  have G0 : Ag st Rd σ s := ⟨sk, sc, fun b hb => (hag b (Or.inl hb)).trans (hRdρ b hb)⟩
  have hoff : L.mem s (affA (L.mem s1 (epHeadA ptr))) ≠ c := by rw [hag _ (Or.inr rfl)]; exact hρd
  exact vm_fh_run hA addr code hc (Ro := fun x => R0 x ∧ Qv x) hRal hR0 rT rN rC eu F hsl hcap hst hAo hdA hdT
    hSO G0 hoff

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg VEq Safe narrowSP PO HeldV InsA InsAP insAP_of_insA insA_narrow)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD vn_of_nf nf_node)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-- A region-tagged or kernel-static word (module docstring §2). -/
def RTW (K : KLayoutP) (b : U64) : Prop :=
  region K.toKLayout b ≠ .none ∨ ∃ o : U64, o.val < 13568 ∧ b = core.num.U64.wrapping_add K.ksb o

/-- **A readable kernel word under `userP K` that is region-tagged or kernel-static is no paging word of the
epoch.** -/
theorem rt_notPWE {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutP} (hK : RegionOKP K)
    {E : U64 → U64} {Locks : S → U64 → Prop} {s : S} {b : U64}
    (hio : IoRS (st := st) (userP K) Locks s b) (hr : RTW K b) : ¬ PWE K E b := by
  intro hp
  rcases hr with hr | ⟨o, ho, rfl⟩
  · exact hr (pwe_region hK hp)
  · rcases hp with hp | hp
    · exact (ioRS_of_userP hio).2 hp
    · exact hp.2.2.2.2 o ho rfl

section rt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A} {U : Set U64} {Locks : S → U64 → Prop}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 1000000 in
/-- **Every word the declining VM-fault run reads up to the handler's `AFFINITY` is region-tagged or kernel-static**
(module docstring §2; the region facts of `vmFhR_vnH`). -/
theorem vmFhR_rt (hA : P0.ArchTotal ar) {K : KLayoutP}
    (P : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s)
    {a : A} {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar s a = ok (s1, a1)) :
    VmFhR st (RTW K) s s1 := by
  have B := P.base
  have hN := B.np
  have hT := B.tp
  have HY := P.hyp a s1 a1 eu
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have ndV : ∀ o : U64, o.val < 4288 → RTW K (L.nodeAt s (L.cpu s) o) := fun o ho =>
    Or.inl (by
      have h : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := B.lay.io.node _ _ (B.inNode o ho)
      rw [h]; simp)
  have scV : ∀ p ∈ Scs, RefillsWF st s p (Z p) → RdHead (L := L) (RTW K) s p := fun p hp hw =>
    ScAcc.head (W := fun _ => True)
      ⟨fun b _ hb => Or.inl (by
        have h : region K.toKLayout b = .sc p := B.lay.io.scw p (Z p) (B.hSc p hp) b hb
        rw [h]; simp), fun _ _ _ => trivial, trivial⟩ hw
  have ksV : ∀ o : U64, o.val < 256 → RTW K (core.num.U64.wrapping_add (L.ksb s) o) := fun o h1 =>
    Or.inr ⟨o, by omega, by rw [← B.kb] <;> rfl⟩
  have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  refine
    { k := utW_ksb s n
      c := utW_cpu s n
      nd := fun o ho _ => by rw [ut_nodeAt]; exact ndV o ho
      dt := by rw [utW_ksb]; exact ksV _ (by simp [layout.ks.DOMAIN_TIME])
      cd := by rw [utW_ksb]; exact ksV _ (by simp [layout.ks.CUR_DOMAIN])
      cur := ut_cur hN n
      sl := ?_
      ep := ?_
      td := ?_
      rs := ?_
      suf := ?_ }
  · intro sl hsl
    obtain ⟨hsl1, -⟩ := B.lay.io.tslot _ (B.hT _ B.cT) _ sl hsl (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    obtain ⟨h8, hf⟩ := B.lay.io.slot8 sl hsl1
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have r1 : region K.toKLayout sl = .slot sl := B.lay.io.slotw sl hsl1 sl ⟨le_refl _, by omega⟩
    have r2 : region K.toKLayout (core.num.U64.wrapping_add sl 8#u64) = .slot sl :=
      B.lay.io.slotw sl hsl1 _ ⟨by omega, by omega⟩
    exact ⟨Or.inl (by rw [r1]; simp), Or.inl (by rw [r2]; simp)⟩
  · intro sl ptr badge x y g gr hsl hcap
    have hsl' : obj.Tcb.slot (L.curW (utW (L := L) s n)) layout.tcb.SLOT_FAULT_HANDLER = ok sl := by
      rw [ut_cur hN n]; exact hsl
    have hpH : H ptr = some .ep := by
      have h1 := HY.cap
      rw [hsl', WP.spec_ok, hcap, WP.spec_ok] at h1
      exact h1.1 ptr badge x y g gr rfl
    have hKp := P.hEp ptr hpH
    have hEP := vm_epP HY.bxi hpH
    have h1 := epTSA_val hEP
    have h2 := epHeadA_val (ep := ptr)
    have := hEP.fits
    have r1 : region K.toKLayout (epTSA ptr) = .obj ptr := B.lay.epw ptr hKp _ ⟨by omega, by omega⟩
    have r2 : region K.toKLayout (epHeadA ptr) = .obj ptr := B.lay.epw ptr hKp _ ⟨by omega, by omega⟩
    exact ⟨Or.inl (by rw [r1]; simp), Or.inl (by rw [r2]; simp)⟩
  · intro h0
    rw [etm] at h0 ⊢
    obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B.bxi
    have hTm := (hX.tm.min _ hq.cur).resolve_left h0
    have hr : region K.toKLayout (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
        .tcb (L.mem s (tmA (L := L) s)) :=
      B.lay.io.tcbw _ (B.hT _ hTm) 3528#u64 (by simp) (by simp)
    exact Or.inl (by
      show region K.toKLayout (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) ≠ .none
      rw [hr]; simp)
  · intro h0
    rw [erh] at h0 ⊢
    obtain ⟨hrT, hscS, hmx⟩ := bxi_rh B.bxi h0
    have esc : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) =
        L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
    rw [esc]
    have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
      B.lay.io.tcbw _ (B.hT _ hrT) 3464#u64 (by simp) (by simp)
    exact ⟨Or.inl (by rw [hr]; simp), rdHead_ut B.bxi n hscS (scV _ hscS (bxi_scin B.bxi hscS hmx).1)⟩
  · rw [ut_csc hN n]
    exact rdHead_ut B.bxi n B.cscS (scV _ B.cscS B.cscwf)

end rt

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's armed VM-fault program is `InsA` at a view start whose fault handler is another core's** (the `InsA`
counterpart of `vmF_fh_annV`; module docstring §2). -/
theorem vmF_fh_insA_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64} (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {addr code : U64} {σ : S} {a : A}
    (hP : VmPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1))
    {sl ptr badge : U64} {x' y g gr : Bool}
    (hsl : obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr))
    (hst : L.epState s1 ptr = obj.EP_RECV)
    (hρd : ρ (affA (L.mem s1 (epHeadA ptr))) ≠ c) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_vm_fault_local addr code) ∅ a)) := by
  have P' : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ := vmFPre_userP hK hq.ks hP.1
  have B := hP.1.base
  have B' := P'.base
  have D' := vm_dfOf hA P' hP.2.1 eu
  have hsc0 : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := B.bxi.2.1.resume hact
  -- the read set, cut to the region-tagged and kernel-static words
  let Rd : U64 → Prop := fun b => (IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) ∧ RTW K b
  have F : VmFhR st Rd σ s1 :=
    VmFhR.and (VmFhR.and (VmFhR.ofDF D') (vmFhR_vn hA hK P' hc hmm hsc0 eu)) (vmFhR_rt hA P' eu)
  have hR0 : ∀ q, Rd q → (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ q ∧ VO K c ρ q) ∧
      q ∉ K.user := fun q hq' =>
    ⟨⟨⟨(ioRS_of_userP hq'.1.1).1, (ioRS_of_userP hq'.1.1).2⟩, hq'.1.2.2⟩,
      fun hu => hq'.1.1.2.1 (Or.inl (Or.inl hu))⟩
  have ndRg : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) :=
    fun o ho => B.lay.io.node _ _ (B.inNode o ho)
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact ndRg o ho))⟩,
      Or.inl (by rw [ndRg o ho]; simp)⟩
  have rT : Rd (ctA (L := L) σ) := ndR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN : Rd (cnA (L := L) σ) := ndR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
    ndR _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  -- the handler
  have hd : L.mem s1 (epHeadA ptr) ∈ T := (D'.ep sl ptr badge x' y g gr hsl hcap).2.2 hst
  have hdA' := B.tp _ hd
  have hdK : K.heap (L.mem s1 (epHeadA ptr)) = some .tcb := B.hT _ hd
  have hAff : IoRS (st := st) (userP K) Locks σ (affA (L.mem s1 (epHeadA ptr))) :=
    D'.gate _ hd 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
  have hAffP : affA (L.mem s1 (epHeadA ptr)) ∉ K.ptes := (ioRS_of_userP hAff).2
  have hgate : ∀ m, ownP K m (affA (L.mem s1 (epHeadA ptr))) = .gate := fun m => by
    rw [ownP_eq_own nv hAffP]
    exact own_tcb_gate (K := userV K.toKLayoutV) B.lay.io hdK hdA' (off := 3520#u64) (by simp) (by simp)
      (by simp [Fl4Proofs.P2.OwnMap.GateField])
  have hAo : (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ (affA (L.mem s1 (epHeadA ptr))) ∧
      VO K c ρ (affA (L.mem s1 (epHeadA ptr)))) ∧ affA (L.mem s1 (epHeadA ptr)) ∉ K.user :=
    ⟨⟨⟨(ioRS_of_userP hAff).1, hAffP⟩, by unfold VO; rw [hgate, hgate]⟩, fun hu => hAff.2.1 (Or.inl (Or.inl hu))⟩
  have hdA : Aligned (affA (L.mem s1 (epHeadA ptr))) := field_aligned hdA' (by simp) (by simp)
  have hdR : Aligned (replyA (L.mem s1 (epHeadA ptr))) := field_aligned hdA' (by simp) (by simp)
  have hrA : region K.toKLayout (affA (L.mem s1 (epHeadA ptr))) = .tcb (L.mem s1 (epHeadA ptr)) :=
    B.lay.io.tcbw _ hdK 3520#u64 (by simp) (by simp)
  have hrR : region K.toKLayout (replyA (L.mem s1 (epHeadA ptr))) = .tcb (L.mem s1 (epHeadA ptr)) :=
    B.lay.io.tcbw _ hdK 3360#u64 (by simp) (by simp)
  have hnd : ∀ o : U64, o.val < 4288 → affA (L.mem s1 (epHeadA ptr)) ≠ L.nodeAt σ (L.cpu σ) o := by
    intro o ho e
    have h2 := ndRg o ho
    rw [← e, hrA] at h2
    cases h2
  have hdT : affA (L.mem s1 (epHeadA ptr)) ≠ ctA (L := L) σ ∧ affA (L.mem s1 (epHeadA ptr)) ≠ cnA (L := L) σ :=
    ⟨hnd _ (by simp [layout.node.CUR_TIME]), hnd _ (by simp [layout.node.CONSUMED])⟩
  -- the paging words of the epoch
  have hnG : ∀ b, region K.toKLayout b ≠ .none → ¬ PWE K E' b := fun b hb hp => hb (pwe_region hK hp)
  have hRdG : ∀ b, Rd b → ¬ PWE K E' b := fun b hb => rt_notPWE hK hb.1.1 hb.2
  have hRG : ¬ PWE K E' (replyA (L.mem s1 (epHeadA ptr))) := hnG _ (by rw [hrR]; simp)
  have hAG : ¬ PWE K E' (affA (L.mem s1 (epHeadA ptr))) := hnG _ (by rw [hrA]; simp)
  have hTG : ¬ PWE K E' (ctA (L := L) σ) :=
    hnG _ (by rw [show ctA (L := L) σ = L.nodeAt σ (L.cpu σ) layout.node.CUR_TIME from rfl,
      ndRg _ (by simp [layout.node.CUR_TIME])]; simp)
  have hNG : ¬ PWE K E' (cnA (L := L) σ) :=
    hnG _ (by rw [show cnA (L := L) σ = L.nodeAt σ (L.cpu σ) layout.node.CONSUMED from rfl,
      ndRg _ (by simp [layout.node.CONSUMED])]; simp)
  -- the memories
  have hRdρ : ∀ b, Rd b → ρ b = L.mem σ b := fun b hb =>
    (hb.1.2.1.symm.trans (hmm b hb.1.1.1 (fun hu => hb.1.1.2.1 (Or.inl (Or.inl hu)))).symm)
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user →
      (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ x ∧ VO K c ρ x) →
      PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm hx.1.1.2.2
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have hH : ∀ x, (x = ctA (L := L) σ ∨ x = cnA (L := L) σ) → HeldV c hs (ownP K μ x) := by
    intro x hx
    have hnd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → x = L.nodeAt σ (L.cpu σ) o →
        HeldV c hs (ownP K μ x) := by
      rintro o ho h8 rfl
      have hp : L.nodeAt σ (L.cpu σ) o ∉ K.ptes := fun hp =>
        (B'.nd (Locks := Locks) o ho h8).1.2.1 (Or.inr hp)
      rw [ownP_eq_own nv hp]
      have e := own_node (m := μ) (K := userV K.toKLayoutV) B.lay.io (B.inNode o ho)
      show HeldV c hs (OwnMap.own (userV K.toKLayoutV) μ _)
      rw [e]
      exact hc
    rcases hx with rfl | rfl
    · exact hnd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) rfl
    · exact hnd' _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) rfl
  have hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem z)
        (L.mem (L.wr z b v)) := by
    intro z b v hb
    obtain ⟨ha, hsw⟩ := B.dsSafe (st := st) (b := b) hb
    exact stepOK_safeP hK nv hLA ha hsw
  exact PathObl.vm_fh_insA (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) hmk (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) hA addr code (hs := hs) (μ := μ) (ρ := ρ) (a := a)
    hc (fun b hb => vo_of_pwe hK hb) (fun b hb => hb.1.1.1) hR0 rT rN rC eu F hsl hcap hst hAo hdA hdR hdT hρd hRdρ
    hRPO (fun x hx => hV.2.1 x hx) hH hSO hRdG hRG hAG hTG hNG

end main

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 4000000 in
/-- **The vmF body's re-annotation is `InsA` at every view start with action 0** (module docstring §2; the `InsA`
counterpart of `vmF_k0_safe`). -/
theorem vmF_k0_insA (j : VmFArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hLk : LkC j.Locks) (h0 : Act0V st K c ρ) (hTR : TabRV st K c ρ)
    (nv : K.vcpus = ∅) (hcv : K.ptes = ptesR K E')
    (hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E' (atAF K.ksb hi))
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.vmF j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  have hG := w11A_noGS st ar hA (masksWr_plain st) L.total a0 (.vmF j) hK hU nv hcv hT
  by_cases hp : (vmFSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (vmFSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).NoGStarts (PWE K E')
          (view K.toKLayout c ρ) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hG' hS'
      have hpr : VmFPremA st ar j K.toKLayoutV := hp
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨⟨hP, -⟩, hq⟩ := id hpre
      have hP' : VmPre st ar (userV K.toKLayoutV) j.T j.Cs j.Ω j.U j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.Locks σ := hP
      have hq' : QPs K st σ := hq
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      have B := hP'.1.base
      have hact : L.actionW σ = 0#u64 := act_of_view B hq'.ksb hc' hmm h0
      obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
      have eu : sched.update_timestamp st ar σ a = ok (utW (L := L) σ n, a2) := update_timestamp_ok ar B.np hn
      by_cases hB : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
          obj.Slot.cap st sl (utW (L := L) σ n) = ok (capability.Cap.Endpoint ptr badge x' y g gr) →
          L.epState (utW (L := L) σ n) ptr = obj.EP_RECV →
          ρ (affA (L.mem (utW (L := L) σ n) (epHeadA ptr))) = c
      · -- the handler homed wherever it is reached: one run for every agreeing state
        refine insA_narrow _ ?_ ∅
        obtain ⟨hNA, hND⟩ := vmF_k0_nar st ar hA j K hK hU c ρ hLk h0 hTR hp W hAv σ a hpre hc' hmm eu hB
        have := E2E.LocalPath.insAVQ
          (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
          (NP := NotPresent) adEq_equiv (pwe_own hK) (fun x hx => pwe_ko hK μ hx)
          (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
          hpre hμ (by rw [hc, hl]; exact hV)
          (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := VNW K c ρ) (DD := VDD K.toKLayout c ρ)
          (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
          (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
          (fun q hq m v y hy => Fl4Proofs.P2.CoreView.vown_upd hK hq.2.2 m v y hy)
          (NR := fun s0 b => VN K c ρ b ∧
            (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) j.Locks) s0 b ∨ VKc K.toKLayout c ρ b))
          (NWs := fun _ => VNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
          (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
            ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x)
          ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
          (fun s b v _ hQ hu hb => by
            refine ⟨(L.cpu_wr s b v).trans hQ.1, (L.ksb_wr s b v).trans hQ.2.1,
              (masksWr_plain st s b v).trans hQ.2.2.1, fun x hx hu' => ?_⟩
            exact (mem_wr_ne' (L := L) hb hx (fun e => hu' (e ▸ hu))).trans (hQ.2.2.2 x hx hu'))
          hNA hND (fun s0 s h1 _ _ h2 h3 => hG' s0 s a h1 h2 h3)
        rw [hc, hl] at this; exact this
      · -- a receiving fault endpoint's head is another core's: the foreign-handler pattern
        push_neg at hB
        obtain ⟨sl, ptr, badge, x', y, g, gr, hsl, hcap, hst, hρd⟩ := hB
        have h := vmF_fh_insA_annV (addr := j.addr) (code := j.code) hA (masksWr_plain st) hK hU hpr.nv
          ⟨hpr.lay.slot8, hpr.lay.tcb, hpr.lay.ntfn8, hpr.lay.sc8⟩ E' hV hP' hq' hc' hl' hmm hact eu hsl hcap hst hρd
        convert h using 2
        unfold LocalPath.body
        rw [hc]
        all_goals rfl
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmF j) K (view K.toKLayout c ρ) hK hU)
      (SlotU.fam_pos _ _ hp) hG hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st))
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmF j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`vmF_insA_annV` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmF_insA_annV_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : VmFArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.vmF j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.vmF j) := hsf
  have hE := epochPteN_view_of J nv hM hV
  have hS := startAt_UN_C st ar hA (masksWr_plain st) L.total a0 P.run
    (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE (startU_of_U2 st ar hA a0 hC nv h')
  have h0 := vmF_act0_SF_C st ar hA a0 P (hK := hK) (hU := hU) hC nv hsf
  have hTR := vmF_bun_SF_C st ar hA a0 P.run (hK := hK) (hU := hU) hC nv hsf
  have hLk : LkC j.Locks := h'.1
  have hT : ∀ hi : U64, hi.val < 2048 → view K.toKLayout c ρ (atAF K.ksb hi) = E (atAF K.ksb hi) :=
    fun hi hhi => atAF_view L J nv hM hV (bun_of_chain st (arI := arI) (AR := AR) (MR := MR) hC) hhi
  unfold annV
  rw [hM.own, hM.cls, hM.ko] at hV ⊢
  exact vmF_k0_insA st ar hA a0 j K hK hU c _ ρ s.mem k E hV hLk h0 hTR nv J.conv hT hS

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every vmF start without a VCPU** (module docstring §2). -/
theorem vmF_insA_annV (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : VmFArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.vmF j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) :=
  vmF_insA_annV_C st ar hA a0 (locPlatCR_of P hIoa) E nv hC J hsf hM hV

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The vmF indices of the PageMap index type. -/
def VmFPm : IxV13Pm S → Prop
  | .inl (.inl (.vmF _)) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`insAP_vmF_view` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insAP_vmF_view_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : VmFPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.vmF j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.vmF j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (vmF_insA_annV_C st ar hA a0 P E nv hC J hsf' hM hV)

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every vmF start** (module docstring §2). -/
theorem insAP_vmF_view (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : VmFPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) :=
  insAP_vmF_view_C st ar hA a0 (locPlatCR_of P hIoa) B E nv hx hC J hM hV hsf

end pm

end
end Fl4Proofs.P2.E2EP
