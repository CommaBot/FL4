/-
# P2 (line p3mc, gen 19): U18, st's `VSafe9` discharged at the st starts whose target is homed

## The st starts discharged
**`st_k0_safeC`**: at a view start of an st index `j` whose target is, in `ρ`, homed on `c`
(`ρ (fld j.target oAFFINITY) = c`), the armed body is `Safe` at the physical memory, by `LocalPath.safeVQW`
(P2/SafeVQW) with
* `N := VN`, `Kc := VKc`, `DD := VDD`, `hO1 := vown_off`;
* the write set `NW := StNW` (`VN ∧ VKc ∧ (¬ VDec ∨ another core's thread's TIMER_HEIGHT)`), the step check
  `VW := StVW` and `hO2W := stVW_own` (P2/StAccVW): the accepted run may recolour nodes of `c`'s tree that are other
  cores' threads armed in it, keeping the tree they name;
* `Q` = agreement with the start state on the aligned kernel words, the core, the kernel base and the frame masks;
* at every start state `s0` of `Q` (`stVC_ent`: sl's view context, P2/StHView):
  - **accepted** runs: on `guard (StNR s0) StNW` (`st_acc_v`) and on `mguard StVW` (`st_acc_vw`);
  - **declined** runs whose target is disarmed or armed in `c`'s tree: on `guard (MaxR ∖ PTE ∩ SR) StDec`
    (`st_dec_v`), moved to every alternative by `run_transfer`, then widened (`run_mono`; `StDec` words are `VNW`) and
    checked (`withinM_of_within`: they are no other core's deadline or height);
  - **declined** runs whose target is armed in another core's tree: at every alternative, on any store answering
    `StNR s0`, declined and writing nothing (`st_walk_v`).

`StHAt` (these starts), `U18At := U17At ∨ StHAt`, **`st_annV_h`**.

## U18
**`serializable_fl4_localU18`** (`ExecWPRV10 (fl4LocW11JC ⊕ invocations) (¬IoIx) U18At StartV2C`);
**`serializable_fl4_localU17of18`**: U17's statement follows from U18.

## Premises of `serializable_fl4_localU18` vs `serializable_fl4_localU17`
* **Removed: `VSafe9` [J] at the st starts whose target is homed on `c` in `ρ`.** With U17 (target another core's),
  st's `VSafe9` is discharged at every st start. Nothing added; family and start facts unchanged
  (`fl4LocW11JC` / `StartV2C` [P]).
* Open: `VSafe9` [J] at irq (route (a)), vq and invocation starts; `VSafe` [J] unchanged.

No existing statement changed except the root import list.

Gen 48 (in place, statements unchanged): `st_k0_nar` (the four run facts) split out of `st_k0_safeC`, shared with
`st_k0_insAH` (P2/InsV15StH).
-/
import Fl4Proofs.P2.StHView
import Fl4Proofs.P2.E2EPU17
import Fl4Proofs.P2.SafeVQW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oTIMER_HEIGHT InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec)

noncomputable section
open Classical

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

/-- A word a declined run writes is one the view keeps and that decides no owner. -/
theorem stDec_vnw {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Cs Ω Sg Ac : Set U64} {target : U64} {s : S}
    (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s) {q : U64}
    (hq : StDec st s q) : VNW K c ρ q := by
  have hX := hJ.regionOKX
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.toKLayoutV.heap.tcbs s (L.cpu s) := h0.nodes _ h0.cur
  have hcH : K.toKLayout.heap (L.curW s) = some .tcb := h0.curT
  rcases hq with rfl | rfl | rfl
  · exact vnw_reg V.hK hX hcH V.cur (by simp [layout.reg.FAULT_IP])
  · exact (srw_node V hJ hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2
  · exact (srw_node V hJ hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2

/-- A write of a word that decides no owner passes st's check. -/
theorem stVW_of_nd {K : KLayoutP} (hU : UserOKP K) {c : U64} {ρ : U64 → U64} {X : S} {q v : U64}
    (ha : Aligned q) (hn : ¬ VDec K.toKLayout c ρ q) : StVW st K.toKLayout c ρ X (L.wr X q v) := by
  refine stPW_vw hU.base.base ⟨ha, fun t ht hta => ⟨fun e => hn ?_, fun e _ => (hn ?_).elim⟩⟩
  · exact Or.inl ⟨t, oTIMER_DEADLINE, ht, hta, decOff_DL, e⟩
  · exact Or.inl ⟨t, oTIMER_HEIGHT, ht, hta, decOff_HT, e⟩

/-- The target's `AFFINITY` at an st view start whose target is homed is the core. -/
theorem st_aff_home {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Cs Ω Sg Ac : Set U64} {target : U64} {s : S}
    (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (htH : ρ (fld target oAFFINITY) = c) : L.mem s (affA target) = L.cpu s := by
  have hg : K.toKLayout.heap target = some .tcb := E.tg
  have aA : Aligned (affA target) :=
    field_aligned (E.inv.1.choose_spec.choose_spec.tcbs _ E.tg) (by simp) (by simp)
  have uA : affA target ∉ K.user := fun hu =>
    E.lay.nu_tcb E.tg (k := 3520#u64) (by simp) (by simp) (mem_userV.2 (Or.inl hu))
  have e1 := V.hm _ aA uA
  have e2 : view K.toKLayout c ρ (affA target) = ρ (affA target) :=
    (sr_tcb V.hK hJ.regionOKX hg htH (o := 3520#u64) (by simp) (by simp) (by simp)).1.1
  rw [e1, e2, V.cpu]; exact htH

theorem stVW_userV {K : KLayoutP} {c : U64} {ρ : U64 → U64} :
    StVW st (userV K.toKLayoutV) c ρ = StVW st K.toKLayout c ρ := rfl

set_option maxHeartbeats 8000000 in
/-- **A declined st run, moved to an alternative**: on st's narrowed store and under st's check. -/
theorem st_dec_alt (hA : P0.ArchTotal ar) {K : KLayoutP} (hU : UserOKP K) {c : U64} {ρ : U64 → U64}
    {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop} {n : I64} {target : U64} {s0 s' s1 : S} {a a1 : A}
    {r' : Bool × S × A}
    (V : SlVC (L := L) K c ρ s0) (hJ : SlJAt (L := L) K.toKLayout s0) (E : StEV st K Cs Ω Sg Ac target s0)
    (htH : ρ (fld target oAFFINITY) = c)
    (hr0 : localtimer.handle_set_timer_local st ar s0 a n target = ok (false, s1, a1))
    (hAlt : Alt st (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) s0) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user) s0 s')
    (hr' : localtimer.handle_set_timer_local st ar s' a n target = ok r') :
    localtimer.handle_set_timer_local (guard st (StNR st K c ρ lk s0) (StNW K c ρ)) ar s' a n target = ok r' ∧
      localtimer.handle_set_timer_local (mguard st (StVW st K.toKLayout c ρ)) ar s' a n target = ok r' := by
  have hz := st_noZero n target
  have hPg := IsProg.on (st_isProg S n target) ar st (fun _ => True)
  have hat0 := st_aff_home st V hJ E htH
  have hp' : ∀ (mm : machine.Store S) (x : S),
      localtimer.handle_set_timer_local mm ar x a n target =
        interp mm ar (R.localtimer.handle_set_timer_local n target) x a :=
    fun mm x => congrFun (congrFun (st_isProg S n target A ar mm) x) a
  by_cases hto : L.mem s0 (tdA target) = 0#u64 ∨ (L.mem s0 (thA target)).val >>> 8 = (L.cpu s0).val
  · have g0 := st_dec_v ar hA (lk := lk) V hJ E htH hto hr0
    have g := E2E.run_transfer (st := st) (masksWr_plain st) hz hPg
      (fun w hw => hw.1.1.2.1) (fun w hw => (E.dec hw).1) trivial trivial hAlt.ksb hAlt.cpu
      hAlt.masks (fun w hw => hAlt.read w hw.1) g0 hr'
    refine ⟨run_mono (st := st) hz hPg trivial (fun q hq => ⟨hq.2.1, Or.inl hq.1⟩)
      (fun q hq => stNW_of_vnw (stDec_vnw st V hJ E hq)) g, ?_⟩
    have g' : localtimer.handle_set_timer_local
        (guard st (fun w => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) s0 w ∧ SR K c ρ w) (StDec st s0))
        ar s' a n target = ok r' := g
    rw [hp'] at g' ⊢
    obtain ⟨g1, g2⟩ := interp_guard _ s' a _ g'
    refine mguard_of_withinM _ s' a _ g1 (withinM_of_within (fun x q v x' hq hw => ?_) _ hz s' a g2)
    rw [L.write_eq] at hw
    have e := ok_inj_ff hw
    subst e
    exact stVW_of_nd st hU (E.dec hq).1 (stDec_vnw st V hJ E hq).2.2
  · rw [not_or] at hto
    haveI : GRd (mguard st (StVW st K.toKLayout c ρ)) st (StNR st K c ρ lk s0) :=
      { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl,
        frame_masks := rfl }
    exact ⟨(st_walk_v ar V hJ E htH hat0 hto.1 hto.2 hAlt
        (gS := guard st (StNR st K c ρ lk s0) (StNW K c ρ)) hr').1,
      (st_walk_v ar V hJ E htH hat0 hto.1 hto.2 hAlt (gS := mguard st (StVW st K.toKLayout c ρ)) hr').1⟩

set_option maxHeartbeats 4000000 in
/-- **st's narrowed and checked runs at a homed view start** (split out of `st_k0_safeC`'s proof in place, gen 48):
the four run facts `LocalPath.safeVQW` asks (`VQNarW`), for the st path at the view, the start states agreeing with
`σ` on the core, the kernel base, the frame masks and the aligned kernel words. -/
theorem st_k0_nar (j : StArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (ρ : U64 → U64)
    (hH : ρ (fld j.target oAFFINITY) = c)
    (hp : (stSlotC st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ))
    (W : NoVcpuRW K.toKLayoutV
      ((stSlotC st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp))
    (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base
      ((stSlotC st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp) W)
        (noVcpuRd_atV hK.base _ W)).rJ K (fun b hb => Or.inl hb)))
    (σ : S) (a : A) (hc' : L.cpu σ = c) :
    (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).VQNarW σ a
      (view K.toKLayout c ρ) (@StNR S st L K c ρ j.lk) (fun _ => StNW K c ρ) (@StVW S st L K.toKLayout c ρ)
      (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
        ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x) := by
  have hpr : K.toKLayoutV.vcpus = ∅ ∧ StPremK2B st j K.toKLayoutV (view K.toKLayout c ρ) := hp
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty hpr.1 hpr.2.bun.choose_spec
  -- the facts at a start state
  have At : ∀ s0 : S, (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv).Pre s0 →
      L.cpu s0 = c → (∀ x, Aligned x → x ∉ K.user → L.mem s0 x = view K.toKLayout c ρ x) →
      ∃ Cs Ω Sg Ac, ∃ E0 : StEV st K Cs Ω Sg Ac j.target s0, SlJAt (L := L) K.toKLayout s0 ∧
        SlVC (L := L) K c ρ s0 := by
    intro s0 hpre0 hc0 hm0
    obtain ⟨⟨hJ0, hQ0⟩, hQP0⟩ := id hpre0
    have hJ0' : SlJAt (L := L) K.toKLayout s0 := hJ0
    have hQ0' : j.Q K.toKLayoutV (view K.toKLayout c ρ) s0 := hQ0
    have hQP0' : QPs K st s0 := hQP0
    have E0 := (stEntK_userV hK.base (vf.v hJ0').1 (vf.v hJ0').2.1 (slJAt_ksb hJ0') (hpr.2.pe s0 hJ0' hQ0')).ent
    exact ⟨_, _, _, _, E0, hJ0', stVC_ent hK hU hJ0' E0 hQP0' hc0 hm0⟩
  unfold Fl4Proofs.P2.E2E.LocalPath.VQNarW Fl4Proofs.P2.E2E.LocalPath.VQNar
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · -- accepted runs, narrowed
    intro s0 r hpre0 _ hc0 hρ0 hrun0 hacc0
    obtain ⟨Cs, Ω, Sg, Ac, E0, hJ0, V0⟩ := At s0 hpre0 (hc0.trans hc') hρ0
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc0
    subst hb
    have hr0 : localtimer.handle_set_timer_local st ar s0 a j.n j.target = ok (true, s1, a1) := hrun0
    exact st_acc_v (st := st) (L := L) ar hA (lk := j.lk) V0 hJ0 E0 hH hr0
  · -- declined runs, narrowed, at every alternative
    intro s0 r hpre0 _ hc0 hρ0 hrun0 hdec0 s' r' hAlt0 hrun'
    obtain ⟨Cs, Ω, Sg, Ac, E0, hJ0, V0⟩ := At s0 hpre0 (hc0.trans hc') hρ0
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = false := Bool.eq_false_iff.2 hdec0
    subst hb
    exact (st_dec_alt st ar hA hU V0 hJ0 E0 hH hrun0 hAlt0 hrun').1
  · -- accepted runs, checked
    intro s0 r hpre0 _ hc0 hρ0 hrun0 hacc0
    obtain ⟨Cs, Ω, Sg, Ac, E0, hJ0, V0⟩ := At s0 hpre0 (hc0.trans hc') hρ0
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc0
    subst hb
    have hr0 : localtimer.handle_set_timer_local st ar s0 a j.n j.target = ok (true, s1, a1) := hrun0
    have g := st_acc_vw (st := st) (L := L) ar hA (regionOK_userV hK.base) (userOK_userV hK.base hU.base)
      (st_isProg S j.n j.target) E0.inv E0.tg E0.lay hH hr0
    rw [stVW_userV] at g
    exact g
  · -- declined runs, checked, at every alternative
    intro s0 r hpre0 _ hc0 hρ0 hrun0 hdec0 s' r' hAlt0 hrun'
    obtain ⟨Cs, Ω, Sg, Ac, E0, hJ0, V0⟩ := At s0 hpre0 (hc0.trans hc') hρ0
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = false := Bool.eq_false_iff.2 hdec0
    subst hb
    exact (st_dec_alt st ar hA hU V0 hJ0 E0 hH hrun0 hAlt0 hrun').2

set_option maxHeartbeats 8000000 in
/-- **The st body is `Safe` at every view start whose target is homed** (module docstring). -/
theorem st_k0_safeC (j : StArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hH : ρ (fld j.target oAFFINITY) = c)
    (hS : StartAt (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  have hko := Fl4Proofs.P2.CoreView.ko_of_veq hK hV
  by_cases hp : (stSlotC st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (stSlotC st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      have hc' : L.cpu σ = c := hc
      refine Fl4Proofs.P2.Serial.safe_narrow _ ?_ ∅
      obtain ⟨⟨hNA, hND⟩, hVA, hVD⟩ := st_k0_nar st ar hA j K hK hU c ρ hH hp W hAv σ a hc'
      have := E2E.LocalPath.safeVQW
        (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv)
        (moveHeldP hK) (ownDepP hK hU) (ρv := view K.toKLayout c ρ) (ρ := ρ) (μ := μ) (σ := σ) (a := a)
        hpre hμ (by rw [hc, hl]; exact hV)
        (N := VN K c ρ) (Kc := VKc K.toKLayout c ρ) (NW := StNW K c ρ) (DD := VDD K.toKLayout c ρ)
        (fun x h => h.1) (fun x h => h.2) (fun x h => by rw [hko]; exact h) (fun x h => ⟨h.1, h.2.1⟩)
        (fun m m' h y hy => Fl4Proofs.P2.CoreView.vown_off hK hU m m' h y hy)
        (VW := @StVW S st L K.toKLayout c ρ)
        (fun q hq s v m hW hm y hy => stVW_own (L := L) hK hU hq.2.2 s v m hW hm y hy)
        (NR := @StNR S st L K c ρ j.lk) (NWs := fun _ => StNW K c ρ) (fun _ _ h => h) (fun _ _ h => h)
        (fun s0 => L.cpu s0 = L.cpu σ ∧ L.ksb s0 = L.ksb σ ∧ st.frame_masks s0 = st.frame_masks σ ∧
          ∀ x, Aligned x → x ∉ K.user → L.mem s0 x = L.mem σ x)
        ⟨rfl, rfl, rfl, fun _ _ _ => rfl⟩
        (fun s b v _ hQ hu hb => by
          refine ⟨(L.cpu_wr s b v).trans hQ.1, (L.ksb_wr s b v).trans hQ.2.1,
            (masksWr_plain st s b v).trans hQ.2.2.1, fun x hx hu' => ?_⟩
          exact (mem_wr_ne' (L := L) hb hx (fun e => hu' (e ▸ hu))).trans (hQ.2.2.2 x hx hu'))
        hNA hND hVA hVD
      rw [hc, hl] at this; exact this
    exact key _ _ (allC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      (SlotU.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st))
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The st starts whose target is homed on `c` in `ρ`.** -/
def StHAt (_K : KLayoutP) (c : U64) (_hs : U64 → Prop) (ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inl (.st j) => ρ (fld j.target oAFFINITY) = c
  | _ => False

/-- **The exempt starts of U18**: U17's and the st starts whose target is homed. -/
def U18At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U17At (S := S) K c hs ρ k0 i ∨ StHAt (S := S) K c hs ρ k0 i

/-- **U9's re-annotated body is `Safe` at every st start of a chain whose target is homed** (module docstring). -/
theorem st_annV_h {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : StHAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · have h' : StartU2C st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.st j) := hsf
    have hS := startAt_stC st ar hA a0 (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact st_k0_safeC st ar hA a0 j K hK hU c _ ρ s.mem k hV hf hS
  all_goals exact False.elim hf

end all

end
end Fl4Proofs.P2.E2EP
