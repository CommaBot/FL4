/-
P3 (DESIGN.md §9), TCB invocations: **TcbDataX's and TcbReadRegs's
hypotheses discharged**.

* `SuspendWFrHyp` from P1's `sched.suspend.kw` (its `Foot` in `KW`), given P1's
  invariant at the restart's state in P1's shape (`SuspendP1Hyp`: `BlkOK`,
  the source a TCB of `T`) and the placement of `KW` apart from the slots
  (`KWOut`) and the domain schedule (`KWDom`): `wfr_of_foot`,
  `suspendWFrHyp_of`.
-/
import Fl4Proofs.P3.TcbReadRegs
import Fl4Proofs.P3.ScTcbHyp
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.ScTop
import Fl4Proofs.P3.ScSpecStep
import Fl4Proofs.P3.SpecFinOutTcb
import Fl4Proofs.P3.ScPlace
import Fl4Proofs.P1.QueueSuspendP1
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`KW`'s aligned words apart from the domain schedule** (the first 256
bytes of the kernel-global block; P1's `KWLow`). -/
def KWDom (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64) (s : S) : Prop :=
  ∀ b, P1.Aligned b → P1.KW st T Cs Sg Scs Z Es s b → b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val

/-- **A P1 `Foot` step is a `WFr` step**, its words apart from the slots and
the domain schedule. -/
theorem wfr_of_foot {th : TypedHeap} (hP : Placed th) {T Cs Sg Scs Es : Set U64} {Z : U64 → Nat} {s s' : S}
    (hKs : KsbPlaced th (L.ksb s)) (hK : Sched.KWOut (st := st) th T Cs Sg Scs Z Es s)
    (hD : KWDom (L := L) T Cs Sg Scs Z Es s) (hw : P1.Foot st T Cs Sg Scs Z Es s s') :
    WFr (L := L) th s s' := by
  refine ⟨Sched.slotsSame_of_foot hP hK hw, hw.1, hw.2.1,
    Vs.domSame_low hKs.fits hKs.align fun b hb h1 h2 => hw.mem_eq hb fun hkw => ?_⟩
  rcases hD b hb hkw with h | h
  · unfold P1.Aligned at hb; omega
  · omega

/-- **P1's invariant at the restart's state** (in P1's shape, for the P1
side): `BlkOK` over some sets, the source a TCB of them, and `KW` of those
sets apart from the slots and the domain schedule. -/
def SuspendP1Hyp (th : TypedHeap) (s : S) (ct p : U64) : Prop :=
  ∀ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    ∃ (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64),
      P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧ p ∈ T ∧
      Sched.KWOut (st := st) th T Cs Sg Scs Z (P1.EH H) s1 ∧ KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s1

/-- **`SuspendWFrHyp` from P1's footprint of `suspend`.** -/
theorem suspendWFrHyp_of {A : Type} (arI : machine.Arch A) {th : TypedHeap} (hP : Placed th) {s : S}
    {ct p : U64} (hC : TCtx (L := L) th s ct) (hS : SuspendP1Hyp (L := L) th s ct p) :
    SuspendWFrHyp (L := L) arI th s ct p := by
  intro s1 a hs1
  obtain ⟨T, Cs, Ω, H, Sg, Rp, Scs, Nt, Z, Ac, hB, hpT, hK, hD⟩ := hS s1 hs1
  have hW : WFr (L := L) th s s1 := by
    have h := sts_t hP hC sched.TS_RESTART
    rw [hs1] at h
    exact ((WP.spec_ok _).1 h).1
  have hKs : KsbPlaced th (L.ksb s1) := (hC.wfr hW).ksb
  obtain ⟨⟨Q, R, hSQ⟩, hBd, hX, -, hSg⟩ := hB
  exact WP.spec_mono (P1.sched.suspend.kw s1 a p hSQ hpT hBd hX hSg.sub) fun r hr =>
    wfr_of_foot hP hKs hK hD hr

/-- **`SuspendP1Hyp` from P1's `suspendP1`** over the joint invariant's sets:
P1 gives `BlkOK`, the target in `T` and `KWLow` (this file's `KWDom`) after
the restart; `KWOut` is the typed heap's (`JPlaced.kwOutBlk`), kept with the
base. -/
theorem suspendP1Hyp_of_joint {th : TypedHeap} {H : P1.Heap} {Tr C Cs Ac : Set U64} {s : S}
    {σ : Fl4Spec.State Unit} (hJ : Sched.JPlaced (L := L) th H Tr C s σ)
    (hb : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s)
    {ct p : U64} (hct : ct = L.curW s) (hnb : ¬ P1.Blocked (L.mem s (P1.stA ct)))
    (hnr : L.mem s (P1.stA ct) ≠ sched.TS_BLOCKED_ON_REPLY) (hp : p ∈ P1.Heap.tcbs H)
    (hSc : ∀ c ∈ P1.Heap.scs H, c.val + 2 ^ P1.Heap.scBits H c ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ c.val) :
    SuspendP1Hyp (L := L) th s ct p := by
  intro s1 hs1
  obtain ⟨h1, h2, h3⟩ := P1.suspendP1 hb hct hnb hnr hp hSc s1 hs1
  have hk : L.ksb s1 = L.ksb s := by
    have h := set_thread_state_ksb (st := st) s ct sched.TS_RESTART
    rw [hs1] at h; exact (WP.spec_ok (p := fun s' => L.ksb s' = L.ksb s) s1).1 h
  exact ⟨_, Cs, _, H, _, _, _, _, _, Ac, h1, h2, (hJ.kwOutBlk hb).ksb hk, h3⟩

/-! ## `GetBpHyp`: `get_breakpoint` is total -/

theorem shr63_ok (x y : U64) : ∃ z, (x >>> (y &&& 63#u64) : Result U64) = ok z := by
  have h : (y &&& 63#u64).val < 64 := by rw [and63_val]; omega
  obtain ⟨z, hz, -⟩ := spec_exists (U64.ShiftRight_spec (x := x) (y := y &&& 63#u64) h)
  exact ⟨z, hz⟩

theorem shl63_ok (x y : U64) : ∃ z, (x <<< (y &&& 63#u64) : Result U64) = ok z := by
  have h : (y &&& 63#u64).val < 64 := by rw [and63_val]; omega
  obtain ⟨z, hz, -⟩ := spec_exists (U64.ShiftLeft_spec (x := x) (y := y &&& 63#u64) h)
  exact ⟨z, hz⟩

theorem shr63_eq (x y : U64) : (x >>> (y &&& 63#u64) : Result U64) = ok (shr63_ok x y).choose :=
  (shr63_ok x y).choose_spec

theorem shl63_eq (x y : U64) : (x <<< (y &&& 63#u64) : Result U64) = ok (shl63_ok x y).choose :=
  (shl63_ok x y).choose_spec

/-- **`get_breakpoint` never fails**: its shifts are masked to `0..63` and its
reads are store reads. -/
theorem get_breakpoint_total (s : S) (t bp : U64) : ∃ r, debug.get_breakpoint st s t bp = ok r := by
  unfold debug.get_breakpoint debug.dr7 obj.Tcb.debug_reg debug.type_and_access debug.type_shift
    debug.size_shift debug.enable_bit
  simp only [lift, bind_ok, L.read_eq]
  generalize L.mem s _ = v
  obtain ⟨z1, h1⟩ := shr63_ok v (core.num.U64.wrapping_add 16#u64 (core.num.U64.wrapping_mul bp 4#u64))
  obtain ⟨z2, h2⟩ := shr63_ok v (core.num.U64.wrapping_add 18#u64 (core.num.U64.wrapping_mul bp 4#u64))
  obtain ⟨z3, h3⟩ := shl63_ok 1#u64 (core.num.U64.wrapping_add (core.num.U64.wrapping_mul bp 2#u64) 1#u64)
  rw [h1, h2, h3]; simp only [bind_ok]
  repeat' split
  all_goals (simp only [bind_ok]; try exact ⟨_, rfl⟩)

theorem getBpHyp_of (s : S) (ct p : U64) : GetBpHyp (st := st) s ct p :=
  fun s1 bp _ => get_breakpoint_total s1 p bp

/-! ## `SingleStepHypW`: `configure_single_stepping` writes the target's
debug and flags words -/

theorem set_debug_reg_eq (s : S) (t i v : U64) :
    obj.Tcb.set_debug_reg st t s i v = ok (L.wr s (core.num.U64.wrapping_add
      (core.num.U64.wrapping_add t layout.tcb.DEBUG) (core.num.U64.wrapping_mul i 8#u64)) v) := by
  unfold obj.Tcb.set_debug_reg
  simp only [lift, bind_ok]
  exact L.write_eq _ _ _

theorem wfr_dbg {th : TypedHeap} (hP : Placed th) {s : S} (hK : KsbPlaced th (L.ksb s)) {t : U64}
    (ht : th t = some .tcb) {i : U64} (hi : i.val < 8) (v : U64) :
    WFr (L := L) th s (L.wr s (core.num.U64.wrapping_add
      (core.num.U64.wrapping_add t layout.tcb.DEBUG) (core.num.U64.wrapping_mul i 8#u64)) v) := by
  have hf := hP.fits t _ ht
  have ha := hP.align t _ ht
  have e4 : objSize ObjKind.tcb = 4096 := rfl
  rw [e4] at hf
  have hD : layout.tcb.DEBUG = 448#u64 := by unfold layout.tcb.DEBUG; rfl
  have hv : (core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.DEBUG)
      (core.num.U64.wrapping_mul i 8#u64)).val = t.val + 448 + i.val * 8 := by
    rw [hD]
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    omega
  exact wfr_tcbw hP hK ht (by rw [hv]; omega) (by rw [hv]; omega) (by unfold P1.Aligned; rw [hv]; omega) v

/-- **`SingleStepHypW`**: `configure_single_stepping` (no reply) on a TCB
target writes its `SS_ENABLED`/`SS_COUNT` debug words and, when disabling, its
`FLAGS` register. -/
theorem singleStepHypW_of {A : Type} (arI : machine.Arch A) {th : TypedHeap} (hP : Placed th) {s : S}
    {ct p : U64} (hC : TCtx (L := L) th s ct) (hpt : th p = some .tcb) :
    SingleStepHypW (L := L) arI th s ct p := by
  intro s1 bp n a hs1
  have hW : WFr (L := L) th s s1 := by
    have h := sts_t hP hC sched.TS_RESTART
    rw [hs1] at h
    exact ((WP.spec_ok _).1 h).1
  have hK : KsbPlaced th (L.ksb s1) := (hC.wfr hW).ksb
  have e6 : debug.SS_ENABLED = 6#u64 := by unfold debug.SS_ENABLED; rfl
  have e7 : debug.SS_COUNT = 7#u64 := by unfold debug.SS_COUNT; rfl
  have eF : layout.reg.FLAGS = 13#u64 := by unfold layout.reg.FLAGS; rfl
  unfold debug.configure_single_stepping
  refine WP.spec_bind (Pₘ := fun s3 => WFr (L := L) th s1 s3) ?_ ?_
  · split
    · rw [set_debug_reg_eq]; simp only [bind_ok]
      have W2 := wfr_dbg hP hK hpt (i := debug.SS_ENABLED) (by rw [e6]; decide) 0#u64
      have hK2 : KsbPlaced th (L.ksb (L.wr s1 (core.num.U64.wrapping_add (core.num.U64.wrapping_add p
          layout.tcb.DEBUG) (core.num.U64.wrapping_mul debug.SS_ENABLED 8#u64)) 0#u64)) := by
        rw [L.ksb_wr]; exact hK
      refine WP.spec_bind (Endp.obj.Tcb.reg.spec _ p _) ?_
      rintro _ -
      refine WP.spec_bind P0.Consts.debug.EFLAGS_TF.spec ?_
      rintro _ rfl
      simp only [lift, bind_ok]
      exact WP.spec_mono (set_reg_wfr hP hK2 hpt (i := layout.reg.FLAGS) (by rw [eF]; decide) _)
        fun s3 W3 => W2.trans W3
    · rw [set_debug_reg_eq]; simp only [WP.spec_ok]
      exact wfr_dbg hP hK hpt (i := debug.SS_ENABLED) (by rw [e6]; decide) 1#u64
  · intro s3 W3
    rw [set_debug_reg_eq]; simp only [bind_ok, WP.spec_ok]
    have hK3 : KsbPlaced th (L.ksb s3) := by rw [W3.2.1]; exact hK
    exact W3.trans (wfr_dbg hP hK3 hpt (i := debug.SS_COUNT) (by rw [e7]; decide) n)

end


/-! ## `SetFlagsSpecHyp`: the spec's `set_flags` -/

namespace Sched
open Fl4Spec

section
variable {f : Bool × Bool}

theorem pres_setX64CurrentFpuOwner (o : Option ObjRef) : Pres f (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner
  exact pres_bind (pres_gets _) (fun _ => pres_bind (pres_maybeM (fun _ => pres_archThreadSet _ _) _) (fun _ =>
    pres_bind (pres_modify (fun σ => ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)) (fun _ =>
      pres_maybeM (fun _ => pres_archThreadSet _ _) _)))

/-- **`fpu_release`** keeps what the CSpace relation and the domain schedule read. -/
theorem pres_fpuRelease (t : ObjRef) : Pres f (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease switchLocalFpuOwner saveFpuState loadFpuState
  refine pres_bind (pres_gets _) (fun _ => pres_when _ ?_)
  refine pres_bind (pres_gets _) (fun _ => pres_bind (pres_doMachineOp _) (fun _ =>
    pres_bind (pres_maybeM (fun _ => pres_bind (pres_doMachineOp _) (fun _ => pres_asUser _ _)) _) (fun _ =>
      pres_bind ?_ (fun _ => pres_setX64CurrentFpuOwner _))))
  exact pres_doMachineOp _

end

theorem presV_selectF {α : Type} (S : Set α × Prop) : PresV (NonDet.selectF S : NonDet (State Unit) α) := by
  intro σ x hx; obtain ⟨-, h⟩ := hx; rw [h]; exact VK.refl σ

theorem presV_doMachineOp {α : Type} (mop : NonDet MachineState α) : PresV (doMachineOp (Z := Unit) mop) := by
  unfold doMachineOp
  refine presV_bind (presV_gets _) (fun _ => presV_bind (presV_selectF _) (fun x => ?_))
  obtain ⟨r, ms⟩ := x
  exact presV_bind (presV_modify (fun σ => ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩)) (fun _ => presV_pure _)

theorem presV_archThreadSet (g : ArchTcb → ArchTcb) (t : ObjRef) : PresV (archThreadSet (Z := Unit) g t) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨k, hk', -, e⟩ := setObject_mem hx
  rw [hk] at hk'; cases hk'
  rw [e]; exact VK.updTcb hk rfl rfl

theorem presV_asUser {α : Type} (p : ObjRef) (u : UserMonad α) : PresV (asUser (Z := Unit) p u) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨hk, hs⟩ := getsThe_getTcb_mem hy
  rw [hs] at hx
  obtain ⟨y2, hy2, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy2] at hx
  obtain ⟨y3, hy3, hx⟩ := hx
  obtain ⟨-, e3⟩ := hy3
  obtain ⟨y4, hy4, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy4] at hx
  obtain ⟨y5, hy5, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hx]
  simp only at e3 hy5
  rw [e3] at hy5
  obtain ⟨k, hk', -, e⟩ := setObject_mem hy5
  rw [hk] at hk'; cases hk'
  rw [e]; exact VK.updTcb hk rfl rfl

theorem presV_setX64CurrentFpuOwner (o : Option ObjRef) : PresV (setX64CurrentFpuOwner (Z := Unit) o) := by
  unfold setX64CurrentFpuOwner
  exact presV_bind (presV_gets _) (fun _ => presV_bind (presV_maybeM (fun _ => presV_archThreadSet _ _) _) (fun _ =>
    presV_bind (presV_modify (fun σ => ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩)) (fun _ =>
      presV_maybeM (fun _ => presV_archThreadSet _ _) _)))

/-- **`fpu_release`** keeps every thread's state. -/
theorem presV_fpuRelease (t : ObjRef) : PresV (fpuRelease (Z := Unit) t) := by
  unfold fpuRelease switchLocalFpuOwner saveFpuState loadFpuState
  refine presV_bind (presV_gets _) (fun _ => presV_when _ ?_)
  refine presV_bind (presV_gets _) (fun _ => presV_bind (presV_doMachineOp _) (fun _ =>
    presV_bind (presV_maybeM (fun _ => presV_bind (presV_doMachineOp _) (fun _ => presV_asUser _ _)) _) (fun _ =>
      presV_bind ?_ (fun _ => presV_setX64CurrentFpuOwner _))))
  exact presV_doMachineOp _

/-- Every set of TCB flags is a word's (one flag, in the mask). -/
theorem tcbFlags_rep (F : TcbFlags) : ∃ w, wordToTcbFlags w = F := by
  by_cases h : TcbFlag.fpuDisabled ∈ F
  · refine ⟨1, Set.ext fun g => ?_⟩
    cases g
    simp only [wordToTcbFlags, Set.mem_setOf_eq, h, iff_true]
    decide
  · refine ⟨0, Set.ext fun g => ?_⟩
    cases g
    simp only [wordToTcbFlags, Set.mem_setOf_eq, h, iff_false]
    decide

end Sched

open Sched in
/-- **`SetFlagsSpecHyp`**: the spec's `set_flags` on a TCB target (its flags,
`fpu_release` when the FPU is disabled) keeps the CSpace relation and the
domain schedule (`SOK`) and the caller's `Restart` (`VK`); its result word
exists since every flag set is a word's. -/
theorem setFlagsSpecHyp_of {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {th : TypedHeap}
    {G : MdbGhost} {σ : Fl4Spec.State Unit} {ct p : U64} (hpt : th p = some .tcb)
    (hcur : σ.curThread = ct.bv) (hkt : ∃ x, σ.kheap ct.bv = some (.tcb x)) :
    SetFlagsSpecHyp (L := L) th G σ ct p := by
  intro s1 σ1 clear set blk call don hst hRL
  obtain ⟨x0, hk0⟩ := hkt
  have hk0' : σ.kheap σ.curThread = some (.tcb x0) := by rw [hcur]; exact hk0
  have e1 := Notif.setThreadState_eq (Z := Unit) .restart hk0'
  rw [hst] at e1
  have hσ1 : σ1 = Notif.stsAct (Notif.updK σ σ.curThread (.tcb { x0 with tcbState := .restart })) σ.curThread := by
    have := congrArg (fun y => y.1) e1; simpa using this
  have hk1 : σ1.kheap ct.bv = some (.tcb { x0 with tcbState := .restart }) := by
    rw [hσ1, Notif.stsAct_kheap, ← hcur]; simp [Notif.updK]
  obtain ⟨xp, hkp, -⟩ := hRL.1.1.tcb p hpt
  set nf : Fl4Spec.TcbFlags := xp.tcbFlags \ Fl4Spec.wordToTcbFlags clear.bv ∪ Fl4Spec.wordToTcbFlags set.bv
    with hnf
  have hts : Fl4Spec.setFlags (Z := Unit) p.bv nf σ1 =
      ({((), Notif.updK σ1 p.bv (.tcb { xp with tcbFlags := nf }))}, False) := Notif.threadSet_eq _ hkp
  set σ2 := Notif.updK σ1 p.bv (.tcb { xp with tcbFlags := nf }) with hσ2
  have hkp2 : σ2.kheap p.bv = some (.tcb { xp with tcbFlags := nf }) := by simp [hσ2, Notif.updK]
  have sok2 : SOK (false, false) σ1 σ2 := (pres_threadSet (fun x => by simp [PK]) p.bv).of_eq hts
  have hts' : Fl4Spec.threadSet (Z := Unit) (fun tcb => { tcb with tcbFlags := nf }) p.bv σ1 =
      ({((), σ2)}, False) := hts
  have vk2 : VK σ1 σ2 := presV_threadSet (g := fun tcb => { tcb with tcbFlags := nf }) (fun _ => rfl) (fun _ => rfl)
    p.bv σ1 _ (by rw [hts']; exact Set.mem_singleton _)
  obtain ⟨σ3, h3⟩ : ∃ σ3, ((), σ3) ∈ (Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ nf)
      (Fl4Spec.fpuRelease (Z := Unit) p.bv) σ2).1 := by
    unfold Fl4Spec.NonDet.when
    split_ifs
    · exact prepareThreadDelete_out hkp2
    · exact ⟨σ2, Set.mem_singleton _⟩
  have sok3 : SOK (false, false) σ2 σ3 := pres_when _ (pres_fpuRelease p.bv) σ2 _ h3
  have vk3 : VK σ2 σ3 := presV_when _ (presV_fpuRelease p.bv) σ2 _ h3
  obtain ⟨w, hw⟩ := tcbFlags_rep nf
  have sok := sok2.trans sok3
  obtain ⟨y, hy, est, -⟩ := (vk2.trans vk3).tcb ct.bv _ hk1
  obtain ⟨hC', hFI'⟩ := crel_of_sok hRL.1 hRL.2.1 (SlotsSame.refl _ _) sok
  refine ⟨w, σ3, y, mem_liftE (x := ([w], σ3)) ?_, ⟨hC', hFI', hRL.2.2.1,
    hRL.2.2.2.of_same (DomSame.refl _ _) sok.dl sok.dsi⟩, hy, est⟩
  show ([w], σ3) ∈ ((do
    let flags ← Fl4Spec.threadGet (Z := Unit) Fl4Spec.Tcb.tcbFlags p.bv
    let newFlags ← pure (flags \ Fl4Spec.wordToTcbFlags clear.bv ∪ Fl4Spec.wordToTcbFlags set.bv)
    Fl4Spec.setFlags p.bv newFlags
    Fl4Spec.NonDet.when (Fl4Spec.TcbFlag.fpuDisabled ∈ newFlags) (Fl4Spec.fpuRelease p.bv)
    let w ← Fl4Spec.NonDet.select {w | Fl4Spec.wordToTcbFlags w = newFlags}
    return [w]) σ1).1
  rw [Notif.nd_bind_one (Notif.threadGet_eq _ hkp), Notif.nd_pure_bind', Notif.nd_bind_one hts]
  exact mem_bind_nd (x := ((), σ3)) (by convert h3) (mem_bind_nd (x := (w, σ3)) (y := ([w], σ3)) ⟨hw, rfl⟩ (Set.mem_singleton _))

end

end Fl4Proofs.P3
