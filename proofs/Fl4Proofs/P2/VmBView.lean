/-
# P2 (line p3mc, gen 12): the accepted VM-fault run's words at a view start, kept by the view (`vm_narA_view`)

At a VM-fault start state `σ` whose memory is core `c`'s view `view K c ρ` on aligned kernel words, with the
entry facts `VmFPre` at `userP K`, every word the accepted fast path touches (`VmNarA`, P2/VmAccN) is kept by the
view (value and owner, `VN`), and either readable by the path or of an unchanged class owner (`VKc`); every word it
writes is `VNW` (`VN`, `VKc`, deciding no foreign owner). The objects:
* the core's node, the kernel words below 256, every TCB slot, the held endpoints and reply objects: never
  rewritten by the view (`nf_node`, `nf_none`, `nf_slot`, `nf_obj`);
* the current thread: running or restarting at the view, so homed on `c` (`view_hidden_home`); the handler: homed
  by the record's `DQ` (`ρ (AFFINITY d) = c`, which the caller supplies); their SCs and the current SC, homed through
  the SC's `TCB` back-pointer (`vm_sc_home_of_tcb`), the current SC given (`hcsc`);
* a thread blocked on receive on a held endpoint, the handler's queue successor, possibly another core's: its
  `EP_NEXT`/`EP_PREV` words are kept with their owner, the endpoint lock (**`vn_link`**: the view hides no
  blocked state, and the link owner of a queued thread does not depend on its home);
* the earliest timer's deadline (`vn_td`, readable: `VmBase.td`), the release head and its SC (`vm_homes`);
* the ASID words: readable (`RdTab`, from `VmPre`) and in no region (`hTabR`, from a bundle state at the view).

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.VmAccN
import Fl4Proofs.P2.VmFhView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb decOff_list view_hidden_home Hidden TZero)

noncomputable section
open Classical

/-! ## Words of a queued thread and of objects -/

theorem not_vdec_obj {K : KLayout} (hK : OwnMap.RegionOK K) {c : U64} {ρ : U64 → U64} {q p : U64}
    (hr : region K q = .obj p) : ¬ VDec K c ρ q := by
  rintro (⟨t, off, ht, -, ho, rfl⟩ | ⟨p', hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨p', b, hb, -, rfl⟩)
  · rw [(hK.tcb t ht off (decOff_list ho)).1] at hr; cases hr
  · rw [(hK.ntfn p' hp).1] at hr; cases hr
  · rw [(hK.tcb t ht _ (Or.inl rfl)).1] at hr; cases hr
  · rw [(hK.scw p' b hb).1] at hr; cases hr

/-- Another core's thread's `STATE` that the view shows nonzero is the real one. -/
theorem view_state_keep {K : KLayout} {c : U64} {m : U64 → U64} {b t : U64} (hb : region K b = .tcb t)
    (ha : m (fld t oAFFINITY) ≠ c) (ho : b.val - t.val = 3328) (hn : view K c m b ≠ 0#u64) :
    view K c m b = m b := by
  have h1 : b.val - t.val ≠ 3520 := by omega
  have h2 : ¬ TZero (b.val - t.val) := by unfold TZero; omega
  by_cases hh : Hidden (m b)
  · exfalso; apply hn
    have : CoreView.repl K c m b = some 0#u64 := by
      simp only [CoreView.repl, CoreView.repl2, hb, CoreView.tcbRepl, if_neg ha, if_neg h1, if_neg h2]
      rw [if_pos ⟨ho, hh⟩]
    exact CoreView.view_some this
  · have : CoreView.repl K c m b = none := by
      simp only [CoreView.repl, CoreView.repl2, hb, CoreView.tcbRepl, if_neg ha, if_neg h1, if_neg h2]
      rw [if_neg (fun h => hh h.2)]
    exact CoreView.view_none this

/-- **The queue links of a thread blocked on receive are kept by the view, whoever's thread it is** (module
docstring). -/
theorem vn_link {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {y off : U64}
    (hy : K.heap y = some .tcb) (hA : TcbAddr y) (hr : region K.toKLayout (fld y off) = .tcb y)
    (hoff : off.val = 3496 ∨ off.val = 3504)
    (hst : view K.toKLayout c ρ (fld y OwnMap.oSTATE) = sched.TS_BLOCKED_ON_RECV) :
    VN K c ρ (fld y off) ∧ VKc K.toKLayout c ρ (fld y off) ∧ ¬ VDec K.toKLayout c ρ (fld y off) := by
  have hK0 := hK.base.base
  have ho : (fld y off).val - y.val = off.val := by
    unfold fld; rw [tcb_wadd_val hA (by omega)]; omega
  have hkc : VKc K.toKLayout c ρ (fld y off) := by
    unfold VKc
    have hne : ¬ ((fld y off).val - y.val = 3328 ∨ (fld y off).val - y.val = 3528) := by omega
    simp only [OwnMap.ko, hr, if_neg hne]
  have hnd : ¬ VDec K.toKLayout c ρ (fld y off) := by
    rintro (⟨t', off', ht', -, ho', e⟩ | ⟨p, hp, e⟩ | ⟨t', ht', e⟩ | ⟨p, b', hb', -, e⟩)
    · obtain ⟨h1, h2⟩ := hK0.tcb t' ht' off' (decOff_list ho')
      rw [← e, hr] at h1
      cases h1
      rw [← e, ho] at h2
      rcases decOff_list ho' with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [OwnMap.oAFF_val, OwnMap.oSTATE_val, OwnMap.oBOBJ_val, OwnMap.oROBJ_val, OwnMap.oDL_val,
          OwnMap.oHT_val] at h2 <;> omega
    · have h1 := (hK0.ntfn p hp).1
      rw [← e, hr] at h1; cases h1
    · obtain ⟨h1, h2⟩ := hK0.tcb t' ht' _ (Or.inl rfl)
      rw [← e, hr] at h1
      cases h1
      rw [← e, ho, OwnMap.oAFF_val] at h2; omega
    · have h1 := (hK0.scw p b' hb').1
      rw [← e, hr] at h1; cases h1
  by_cases ha : ρ (fld y oAFFINITY) = c
  · exact ⟨vn_of_nf hK (nf_tcb hr ha), hkc, hnd⟩
  refine ⟨⟨view_keep_tcb hr (by omega) (by unfold TZero; omega) (by omega), ?_⟩, hkc, hnd⟩
  obtain ⟨hrS, hoS⟩ := hK0.tcb y hy OwnMap.oSTATE (Or.inr (Or.inl rfl))
  obtain ⟨hrB, hoB⟩ := hK0.tcb y hy OwnMap.oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl)))
  rw [OwnMap.oSTATE_val] at hoS; rw [OwnMap.oBOBJ_val] at hoB
  have hne : view K.toKLayout c ρ (fld y OwnMap.oSTATE) ≠ 0#u64 := by
    rw [hst]; intro h; have := congrArg UScalar.val h; unfold sched.TS_BLOCKED_ON_RECV at this; simp at this
  have eS := view_state_keep hrS ha hoS hne
  have eB : view K.toKLayout c ρ (fld y OwnMap.oBLOCK_OBJ) = ρ (fld y OwnMap.oBLOCK_OBJ) :=
    view_keep_tcb hrB (by omega) (by unfold TZero; omega) (by omega)
  have hq : OwnMap.QueuedState (ρ (fld y OwnMap.oSTATE)) := by rw [← eS, hst]; exact recv_queued
  have hp : fld y off ∉ K.ptes := fun h => by rw [hK.none _ h] at hr; cases hr
  have hv : ¬ ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v (fld y off) := by
    rintro ⟨v, hv⟩; rw [hK.base.none v _ hv] at hr; cases hr
  have g1 : ¬ OwnMap.GateField ((fld y off).val - y.val) := by rw [ho]; unfold OwnMap.GateField; omega
  have g2 : ¬ OwnMap.TimerField ((fld y off).val - y.val) := by rw [ho]; unfold OwnMap.TimerField; omega
  have g3 : OwnMap.GField ((fld y off).val - y.val) := by rw [ho]; unfold OwnMap.GField; omega
  rw [ownP_off hp, ownP_off hp, ownV_off hv, ownV_off hv]
  simp only [OwnMap.own, hr, OwnMap.tcbOwner, if_neg g1, if_neg g2, if_pos g3, OwnMap.gOwner, eS, eB, if_pos hq]

/-! ## The record at a view start -/

section pins
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

/-- The read set of the narrowed accepted run: aligned kernel words the view keeps, readable or of an unchanged
class owner. -/
def NNv (K : KLayoutP) (c : U64) (ρ : U64 → U64) (Locks : S → U64 → Prop) (σ : S) (b : U64) : Prop :=
  Aligned b ∧ b ∉ K.user ∧ VN K c ρ b ∧ (IoRS (st := st) (userP K) Locks σ b ∨ VKc K.toKLayout c ρ b)

/-- The write set of the narrowed accepted run. -/
def NWv (K : KLayoutP) (c : U64) (ρ : U64 → U64) (b : U64) : Prop := Aligned b ∧ VNW K c ρ b

set_option maxHeartbeats 4000000 in
/-- **`VmNarA` for the view's words at a view start** (module docstring). -/
theorem vm_narA_view {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {σ : S}
    (P : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hc : L.cpu σ = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hcsc : ρ (fld (L.cscW σ) 16#u64) = c)
    (hTab : RdTab (L := L) (IoRS (st := st) (userV K.toKLayoutV) Locks σ) σ)
    (hTabR : ∀ hi : U64, hi.val < 2048 → region K.toKLayout (atAF (L.ksb σ) hi) = .none ∧
      (L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
        region K.toKLayout (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) = .none)) :
    VmNarA st (userP K) T Z Locks (fun d => ρ (fld d oAFFINITY) = c) (NNv (st := st) K c ρ Locks σ) (NWv K c ρ) σ := by
  have B := P.base
  have hK0 := hK.base.base
  have hN := B.np
  have hT := B.tp
  have ku : ∀ b, b ∉ (userP K).user → b ∉ K.user := fun b h hu => h (Or.inl (Or.inl hu))
  have nnOf : ∀ b, Aligned b → b ∉ K.user → NotForeign K.toKLayout c ρ b → NNv (st := st) K c ρ Locks σ b :=
    fun b ha hu hnf => ⟨ha, hu, vn_of_nf hK hnf, Or.inr (vkc_of hK0 hnf.1)⟩
  have nwOf : ∀ b, Aligned b → NotForeign K.toKLayout c ρ b → ¬ VDec K.toKLayout c ρ b → NWv K c ρ b :=
    fun b ha hnf hnd => ⟨ha, vn_of_nf hK hnf, vkc_of hK0 hnf.1, hnd⟩
  -- the words of a thread homed on `c`
  have tw : ∀ y ∈ T, ρ (fld y oAFFINITY) = c → ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
      NNv (st := st) K c ρ Locks σ (fld y off) ∧ (off.val ≠ 3520 → NWv K c ρ (fld y off)) := by
    intro y hy hya off h1 h2 h3
    have hr : region K.toKLayout (fld y off) = .tcb y := B.lay.io.tcbw y (B.hT y hy) off h1 h2
    have ha : Aligned (fld y off) := field_aligned (hT y hy) h2 h3
    have hu : fld y off ∉ K.user := ku _ (B.region_kernel (Or.inl (by
      rw [show region (userP K) (fld y off) = .tcb y from hr]; simp)))
    have hnf := nf_tcb hr hya
    refine ⟨nnOf _ ha hu hnf, fun h0 => nwOf _ ha hnf (not_vdec_tcb hK0 hr hya ?_)⟩
    unfold fld; rw [tcb_wadd_val (hT y hy) h2]; omega
  have regw : ∀ y ∈ T, ρ (fld y oAFFINITY) = c → ∀ r : U64, r.val < 384 →
      NNv (st := st) K c ρ Locks σ (regA y r) ∧ NWv K c ρ (regA y r) := by
    intro y hy hya r hr
    obtain ⟨k, hk, e⟩ := regA_eq (hT y hy) hr
    rw [e]
    exact ⟨(tw y hy hya k (by omega) (by omega) (by omega)).1,
      (tw y hy hya k (by omega) (by omega) (by omega)).2 (by omega)⟩
  -- the current thread is homed
  have hcur : ρ (fld (L.curW σ) oAFFINITY) = c := by
    have e : fld (L.curW σ) OwnMap.oSTATE = stA (L.curW σ) := fld_state _
    have hr : region K.toKLayout (fld (L.curW σ) OwnMap.oSTATE) = .tcb (L.curW σ) :=
      B.lay.io.tcbw _ (B.hT _ B.cT) OwnMap.oSTATE (by rw [OwnMap.oSTATE_val]; omega) (by rw [OwnMap.oSTATE_val]; omega)
    have hst : L.mem σ (fld (L.curW σ) OwnMap.oSTATE) = view K.toKLayout c ρ (fld (L.curW σ) OwnMap.oSTATE) :=
      hm _ (field_aligned B.tA (by rw [OwnMap.oSTATE_val]; omega) (by rw [OwnMap.oSTATE_val]))
        (ku _ (B.region_kernel (Or.inl (by rw [show region (userP K) _ = _ from hr]; simp))))
    refine view_hidden_home hK0 (B.hT _ B.cT) ?_
    rw [← hst, e]
    rcases B.run with h | h <;> rw [h] <;> simp [Hidden, sched.TS_RESTART, sched.TS_RUNNING]
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B.bxi
  -- an SC homed on `c`
  have scN : ∀ p ∈ Scs, ρ (fld p 16#u64) = c → ScAcc (NNv (st := st) K c ρ Locks σ) (NWv K c ρ) p (Z p) := by
    intro p hp hpc
    have hr : ∀ b, InSC p (Z p) b → region K.toKLayout b = .sc p := fun b hb' =>
      B.lay.io.scw p (Z p) (B.hSc p hp) b hb'
    have hu : ∀ b, InSC p (Z p) b → b ∉ K.user := fun b hb' => ku _ (B.region_kernel (Or.inl (by
      rw [show region (userP K) b = .sc p from hr b hb']; simp)))
    obtain ⟨hP, hz⟩ := hO.sc _ hp
    obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    have hin : InSC p (Z p) (core.num.U64.wrapping_add p layout.sc.CONSUMED) :=
      ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩
    refine ⟨fun b ha hb' => nnOf b ha (hu b hb') (nf_sc (hr b hb') hpc),
      fun b ha hb' => nwOf b ha (nf_sc (hr b hb'.inSC) hpc) (not_vdec_sc hK0 (hr b hb'.inSC) hpc), ?_⟩
    exact nwOf _ (by unfold Aligned; rw [hv, hcv]; omega) (nf_sc (hr _ hin) hpc) (not_vdec_sc hK0 (hr _ hin) hpc)
  have ndR : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := fun o ho => by
    rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)
  refine
  { nd := fun o ho h8 => ?_
    ks := fun o h1 h2 => ?_
    tab := ?_
    home := fun off h1 h2 h3 hg _ => ?_
    reg := fun r hr => regw _ B.cT hcur r hr
    tslot := fun y hy i sl hsl hi => ?_
    dhome := fun d hd hdq _ off h1 h2 h3 hg _ _ => ?_
    dgate := fun d hd hdq off h1 h2 h3 _ => (tw d hd hdq off h1 h2 h3).1
    dreg := fun d hd hdq _ r hr => regw d hd hdq r hr
    link := fun y hy p hst _ _ off hoff => ?_
    ep := fun p b hp hb' ha _ => ?_
    rp := fun p b hp hb' ha _ => ?_
    csc := scN _ B.cscS hcsc
    dsc := fun d hd _ _ hne => ?_
    td := fun h0 => ?_
    rs := fun h0 => ?_ }
  · have ha := nodeAt_aligned hN ho h8
    have hu := ku _ (B.region_kernel (Or.inl (by rw [show region (userP K) _ = _ from ndR o ho]; simp)))
    exact ⟨nnOf _ ha hu (nf_node (ndR o ho)), nwOf _ ha (nf_node (ndR o ho)) (not_vdec_node hK0 (ndR o ho))⟩
  · obtain ⟨k8, kf⟩ := B.lay.io.ksf
    have hv : (core.num.U64.wrapping_add (L.ksb σ) o).val = (L.ksb σ).val + o.val := by
      rw [← B.kb]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have ha : Aligned (core.num.U64.wrapping_add (L.ksb σ) o) := by unfold Aligned; rw [hv, ← B.kb]; omega
    have hr : region K.toKLayout (core.num.U64.wrapping_add (L.ksb σ) o) = .none :=
      B.lay.io.ks _ ha (by rw [hv, ← B.kb]; omega) (by rw [hv, ← B.kb]; omega)
    have hu : core.num.U64.wrapping_add (L.ksb σ) o ∉ K.user := ku _ (B.region_kernel (Or.inr (by
      rw [hv, ← B.kb]; constructor <;> omega)))
    exact nnOf _ ha hu (nf_none hr)
  · intro hi hhi
    obtain ⟨⟨a1, u1, -⟩, hp⟩ := hTab hi hhi
    obtain ⟨r1, rp⟩ := hTabR hi hhi
    refine ⟨nnOf _ a1 (fun h => u1 (mem_userV.2 (Or.inl h))) (nf_none r1), fun lo hlo h0 => ?_⟩
    obtain ⟨a2, u2, -⟩ := hp lo hlo h0
    exact nnOf _ a2 (fun h => u2 (mem_userV.2 (Or.inl h))) (nf_none (rp h0 lo hlo))
  · have h := tw _ B.cT hcur off h1 h2 h3
    exact ⟨h.1, h.2 (fun e => hg (by unfold OwnMap.GateField; omega))⟩
  · obtain ⟨hsl1, -⟩ := B.lay.io.tslot _ (B.hT _ hy) _ sl hsl hi
    obtain ⟨h8, hf⟩ := B.lay.io.slot8 sl hsl1
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have r0 : region K.toKLayout sl = .slot sl := B.lay.io.slotw sl hsl1 sl ⟨le_refl _, by omega⟩
    have r8 : region K.toKLayout (core.num.U64.wrapping_add sl 8#u64) = .slot sl :=
      B.lay.io.slotw sl hsl1 _ ⟨by omega, by omega⟩
    refine ⟨nnOf _ (by unfold Aligned; omega) (ku _ (B.region_kernel (Or.inl (by
        rw [show region (userP K) sl = .slot sl from r0]; simp)))) (nf_slot r0),
      nnOf _ (by unfold Aligned; rw [hv]; omega) (ku _ (B.region_kernel (Or.inl (by
        rw [show region (userP K) _ = .slot sl from r8]; simp)))) (nf_slot r8)⟩
  · have h := tw d hd hdq off h1 h2 h3
    exact ⟨h.1, h.2 (fun e => hg (by unfold OwnMap.GateField; omega))⟩
  · have hA := hT y hy
    have h1 : 192 ≤ off.val := by omega
    have h2 : off.val < 4096 := by omega
    have hr : region K.toKLayout (fld y off) = .tcb y := B.lay.io.tcbw y (B.hT y hy) off h1 h2
    have ha : Aligned (fld y off) := field_aligned hA h2 (by omega)
    have hu : fld y off ∉ K.user := ku _ (B.region_kernel (Or.inl (by
      rw [show region (userP K) (fld y off) = .tcb y from hr]; simp)))
    have hrS : region K.toKLayout (fld y OwnMap.oSTATE) = .tcb y :=
      B.lay.io.tcbw y (B.hT y hy) OwnMap.oSTATE (by rw [OwnMap.oSTATE_val]; omega) (by rw [OwnMap.oSTATE_val]; omega)
    have hu1 : fld y OwnMap.oSTATE ∉ K.user := ku _ (B.region_kernel (Or.inl (by
      rw [show region (userP K) (fld y OwnMap.oSTATE) = .tcb y from hrS]; simp)))
    have hm1 : L.mem σ (fld y OwnMap.oSTATE) = view K.toKLayout c ρ (fld y OwnMap.oSTATE) :=
      hm (fld y OwnMap.oSTATE) (field_aligned hA (by rw [OwnMap.oSTATE_val]; omega) (by rw [OwnMap.oSTATE_val])) hu1
    have hs' : view K.toKLayout c ρ (fld y OwnMap.oSTATE) = sched.TS_BLOCKED_ON_RECV := by
      rw [← hm1, fld_state]; exact hst
    obtain ⟨v1, v2, v3⟩ := vn_link hK (B.hT y hy) hA hr hoff hs'
    exact ⟨⟨ha, hu, v1, Or.inr v2⟩, ha, v1, v2, v3⟩
  · have hr : region K.toKLayout b = .obj p := B.lay.epw p hp b hb'
    have hu : b ∉ K.user := ku _ (B.region_kernel (Or.inl (by rw [show region (userP K) b = .obj p from hr]; simp)))
    exact ⟨nnOf _ ha hu (nf_obj hr), nwOf _ ha (nf_obj hr) (not_vdec_obj hK0 hr)⟩
  · have hr : region K.toKLayout b = .obj p := B.lay.rpw p hp b hb'
    have hu : b ∉ K.user := ku _ (B.region_kernel (Or.inl (by rw [show region (userP K) b = .obj p from hr]; simp)))
    exact ⟨nnOf _ ha hu (nf_obj hr), nwOf _ ha (nf_obj hr) (not_vdec_obj hK0 hr)⟩
  · obtain ⟨hcs, htcb, -⟩ := hX.bound d hd hne
    exact scN _ hcs (vm_sc_home_of_tcb B hm hcs (by rw [htcb]; intro e; exact (hT d hd).ne0 (by rw [e]; rfl)))
  · have hTm := (hX.tm.min _ hq.cur).resolve_left h0
    obtain ⟨hd, -⟩ := B.tmc h0
    have hr : region K.toKLayout (fld (L.mem σ (tmA (L := L) σ)) OwnMap.oTIMER_DEADLINE) =
        .tcb (L.mem σ (tmA (L := L) σ)) :=
      B.lay.io.tcbw _ (B.hT _ hTm) 3528#u64 (by simp) (by simp)
    have ho : (fld (L.mem σ (tmA (L := L) σ)) OwnMap.oTIMER_DEADLINE).val -
        (L.mem σ (tmA (L := L) σ)).val = 3528 := by
      unfold fld; rw [tcb_wadd_val (hT _ hTm) (by simp [OwnMap.oTIMER_DEADLINE])]
      simp [OwnMap.oTIMER_DEADLINE]
    have e1 := view_keep_tcb (c := c) (m := ρ) hr (by omega) (by unfold TZero; omega) (by omega)
    have ha : Aligned (fld (L.mem σ (tmA (L := L) σ)) OwnMap.oTIMER_DEADLINE) :=
      field_aligned (hT _ hTm) (by simp [OwnMap.oTIMER_DEADLINE]) (by simp [OwnMap.oTIMER_DEADLINE])
    have hu : fld (L.mem σ (tmA (L := L) σ)) OwnMap.oTIMER_DEADLINE ∉ K.user := ku _ (B.region_kernel (Or.inl (by
      rw [show region (userP K) _ = _ from hr]; simp)))
    have hm' := hm _ ha hu
    exact ⟨ha, hu, vn_td hK (B.hT _ hTm) (by rw [← e1, ← hm']; exact hd), Or.inl (B.td (Locks := Locks) h0)⟩
  · obtain ⟨hrT, hscS, hmx⟩ := bxi_rh B.bxi h0
    obtain ⟨ha, hsa⟩ := (vm_homes B hm).2 h0
    have hacc := scN _ hscS hsa
    exact ⟨(tw _ hrT ha 3464#u64 (by simp) (by simp) (by simp)).1, hacc.rd,
      hacc.head (bxi_scin B.bxi hscS hmx).1⟩

end pins

end
end Fl4Proofs.P2.E2EP
