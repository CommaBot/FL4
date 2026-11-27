/-
# P2 (line p3mc, gen 39, unit A): P3's spec invariant `SInvX` at the second boot start `σR`

Gen 34's `boot_sinvX_B` (P2/BootSpecInv, `SInvX σB`) re-proved at `σR` (P2/BootRSpec, round 2: `σB` with the
running root thread `tRp` current, bound to the root SC `scRp`, and two non-null caps, `threadCap tRp` in the root
thread's CSpace-root slot and `schedContextCap scRp 0` in its timeout-handler slot): **`sinvX_R`**. Each field is
split by `kheapR_cases` (the root TCB, the root SC, or one of `σB`'s objects, where gen 34's lemma applies) and by
`capAt_R` / `capOpt_R` (the two non-null caps). `ScLiveT` (`uA_scLiveT_R`) holds by the two caps: the root thread is
named by its thread cap, the root SC by its SC cap.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.BootRZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.BootSt
open Fl4Spec Fl4Proofs.P3 Classical

noncomputable section

/-! ## Objects -/

theorem uA_ofB {p : ObjRef} {o : KernelObject} (h : kheapB p = some o) : kheapR p = some o := by
  have h1 : p ≠ tRp := by rintro rfl; rw [kheapB_tRp] at h; cases h
  have h2 : p ≠ scRp := by rintro rfl; rw [kheapB_scRp] at h; cases h
  rw [kheapR_of_ne h1 h2]; exact h

theorem uA_idleT : kheapR idleThreadPtr = kheapB idleThreadPtr := kheapR_of_ne (by decide) (by decide)
theorem uA_idleS : kheapR idleScPtr = kheapB idleScPtr := kheapR_of_ne (by decide) (by decide)

/-- A `TI` predicate at `σR` from the root TCB's and `σB`'s. -/
theorem uA_TI {Q : Tcb → Prop} (hR : Q tcbR) (hB : SInv.TI Q (σB (Z := Unit))) : SInv.TI Q (σR (Z := Unit)) := by
  intro p x hp
  rcases kheapR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
  · cases e; exact hR
  · cases e
  · exact hB p x h

/-- A non-TCB, non-SC object of `σR` is `σB`'s. -/
theorem uA_toB {p : ObjRef} {o : KernelObject} (h : kheapR p = some o) (ht : ∀ x, o ≠ .tcb x)
    (hs : ∀ y n, o ≠ .schedContext y n) : kheapB p = some o := by
  rcases kheapR_cases h with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
  · exact absurd e (ht _)
  · exact absurd e (hs _ _)
  · exact h

theorem uA_irqNode_ne (irq : Irq) : (σR (Z := Unit)).interruptIrqNode irq ≠ tRp := by
  intro e
  have h := σB_node_val irq
  change (σB (Z := Unit)).interruptIrqNode irq = tRp at e
  rw [e, tRp_toNat, kbB_val] at h; omega

theorem uA_scActive_R : scActive scR = true := by decide

theorem uA_irqNode_ne' (irq : Irq) : (σR (Z := Unit)).interruptIrqNode irq ≠ scRp := by
  intro e
  have h := σB_node_val irq
  change (σB (Z := Unit)).interruptIrqNode irq = scRp at e
  rw [e, scRp_toNat, kbB_val] at h; omega

/-! ## `SInvA`'s fields -/

theorem uA_vfh_R : SInv.VfhAll (σR (Z := Unit)) :=
  uA_TI (by unfold SInv.vfhQ validFaultHandler; exact Or.inr rfl) SInv.boot_vfhAll_B

theorem uA_cnDom_R : SInv.CnDom (σR (Z := Unit)) := by
  intro sl c hc p r g e
  subst e
  rcases capOpt_R hc with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> cases e

theorem uA_fts_R : SInv.FaultTcbsS (σR (Z := Unit)) :=
  uA_TI (fun hf => absurd rfl hf) SInv.boot_faultTcbsS_B

theorem uA_noNtfn {n : ObjRef} {x : Notification} : kheapB n ≠ some (.notification x) := by
  intro hn
  simp only [kheapB, Function.update_apply] at hn
  split_ifs at hn <;> (try cases hn)
  all_goals (split_ifs at hn <;> cases hn)

theorem uA_nqb_R : SInv.NQB (σR (Z := Unit)) := by
  rintro t ⟨n, x, hn, -⟩
  exact absurd (uA_toB hn (fun _ => by simp) (fun _ _ => by simp)) uA_noNtfn

theorem uA_ns_R : SInv.NativeScopeS (σR (Z := Unit)) :=
  uA_TI (fun h => by cases h) SInv.boot_nativeScope_B

theorem uA_sg_R : SInvG.SpecGlobS (σR (Z := Unit)) where
  irq irq a ha := by
    rcases capAt_R ha with e | ⟨e, -⟩ | ⟨e, -⟩
    · exact Or.inl e
    · have e2 : ([] : CnodeIndex) = tcbCnodeIndex 0 := congrArg Prod.snd e
      exact absurd e2 (by decide)
    · have e2 : ([] : CnodeIndex) = tcbCnodeIndex 4 := congrArg Prod.snd e
      exact absurd e2 (by decide)
  ref p cref a ha _ irq := by
    rcases capAt_R ha with e | ⟨-, e⟩ | ⟨-, e⟩
    · subst e; simp [objRefs]
    · subst e; simp only [objRefs, Set.mem_singleton_iff]; exact uA_irqNode_ne irq
    · subst e; simp only [objRefs, Set.mem_singleton_iff]; exact uA_irqNode_ne' irq
  idle p cref a ha _ := by
    rcases capAt_R ha with e | ⟨-, e⟩ | ⟨-, e⟩
    · subst e; simp [objRefs]
    · subst e; simp only [objRefs, Set.mem_singleton_iff]; exact fun e => tRp_ne_idle e.symm
    · subst e; simp only [objRefs, Set.mem_singleton_iff]; exact fun e => absurd e (by decide)

theorem uA_vih_R : SInvV.ValidIrqHandlers (σR (Z := Unit)) := by
  intro p cref irq hc
  rcases capOpt_R hc with e | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;> cases e

theorem uA_utInv_R : SInvU.UtInv (σR (Z := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro sl _ _ _ _ hc; rcases capAt_R hc with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro sl _ _ _ _ hc; rcases capAt_R hc with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro s1 _ _ _ _ _ _ _ _ _ _ hc; rcases capAt_R hc with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro s1 _ _ _ _ _ _ _ _ _ _ hc; rcases capAt_R hc with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro sl _ _ _ _ hc; rcases capAt_R hc with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e

theorem uA_utInv'_R : SInvU.UtInv' (σR (Z := Unit)) := by
  refine ⟨uA_utInv_R, fun c p h => ?_, fun x hx => ?_⟩
  · exact absurd h (by simp [SInvU.uV, σR, σB, initCdt])
  · obtain ⟨c, hc⟩ := SInvU.tg_first hx
    exact absurd hc (by simp [SInvU.uV, σR, σB, initCdt])

theorem uA_utNV_R : SInvU.UtNV (SInvU.uV (σR (Z := Unit))) := by
  have h0 : ∀ sl c, (SInvU.uV (σR (Z := Unit))).2.1 sl = some c →
      c = .nullCap ∨ (sl = (tRp, tcbCnodeIndex 0) ∧ c = .threadCap tRp) ∨
        (sl = (tRp, tcbCnodeIndex 4) ∧ c = .schedContextCap scRp 0) := fun _ _ h => capAt_R h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u dev b n fi hu; rcases h0 _ _ hu with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · rintro p c hp hne ⟨u, dev, b, n, fi, hu, -⟩; rcases h0 _ _ hu with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro u dev b n fi hu; rcases h0 _ _ hu with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro s c s' c' r hs hs' hr hr'
    rcases h0 _ _ hs' with e' | ⟨-, e'⟩ | ⟨-, e'⟩ <;> subst e'
    · simp [SInvU.sRefs] at hr'
    · simp only [SInvU.sRefs, Set.mem_singleton_iff] at hr'
      subst hr'
      rcases h0 _ _ hs with e | ⟨-, e⟩ | ⟨-, e⟩ <;> subst e
      · simp [SInvU.capRng, objRefs] at hr
      · rfl
      · simp only [SInvU.capRng, objRefs, Set.mem_singleton_iff] at hr
        exact absurd hr tRp_ne_scRp
    · simp [SInvU.sRefs] at hr'
  · intro s c r hs hr i c' hc' hn
    rcases h0 _ _ hc' with e | ⟨e1, -⟩ | ⟨e1, -⟩
    · exact absurd e hn
    · rcases h0 _ _ hs with e | ⟨-, e⟩ | ⟨-, e⟩ <;> subst e
      · simp [SInvU.sRefs] at hr
      · cases e1; exact ⟨0, by decide, rfl⟩
      · simp [SInvU.sRefs] at hr
    · rcases h0 _ _ hs with e | ⟨-, e⟩ | ⟨-, e⟩ <;> subst e
      · simp [SInvU.sRefs] at hr
      · cases e1; exact ⟨4, by decide, rfl⟩
      · simp [SInvU.sRefs] at hr
  · intro s r b n hs; rcases h0 _ _ hs with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  · intro s c hs b hb
    rcases h0 _ _ hs with e | ⟨-, e⟩ | ⟨-, e⟩ <;> subst e <;> simp [SInvU.shp] at hb

theorem uA_ut_R : SInvU.UtInv3 (σR (Z := Unit)) :=
  ⟨⟨uA_utInv'_R, uA_utNV_R⟩, irqOut_R _ uA_irqNode_ne uA_irqNode_ne'⟩

theorem uA_nq_R : SInv.NtfnQB (σR (Z := Unit)) := by
  intro n x t hn ht
  have hn' := uA_toB hn (fun _ => by simp) (fun _ _ => by simp)
  obtain ⟨y, hy, hs⟩ := SInv.boot_ntfnQB_B n x t hn' ht
  exact ⟨y, uA_ofB hy, hs⟩

theorem uA_epq_R : SInv.EpQB (σR (Z := Unit)) := by
  intro n x t hn ht
  have hn' := uA_toB hn (fun _ => by simp) (fun _ _ => by simp)
  obtain ⟨y, hy, hs⟩ := SInv.boot_epQB_B n x t hn' ht
  exact ⟨y, uA_ofB hy, hs⟩

theorem uA_live_R : SInv.IfLiveT (σR (Z := Unit)) := by
  intro t y ht hl
  rcases kheapR_cases ht with ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
  · subst e; exact ⟨_, capAt_R_root⟩
  · cases e
  · exact absurd (SInvAll.boot_ifLiveT_B t y h hl) (by
      rintro ⟨s, hs⟩; cases SInvU.init_capAt_B hs)

theorem uA_vi_R : SInvI.ValidIdle (σR (Z := Unit)) := by
  obtain ⟨-, -, -, ⟨x0, h0⟩, ⟨sc0, n0, hs0⟩, hB⟩ := SInvAll.boot_validIdle_B
  refine ⟨rfl, rfl, fun e => absurd e Bool.false_ne_true, ⟨x0, uA_ofB (p := idleThreadPtr) h0⟩, ⟨sc0, n0, uA_ofB (p := idleScPtr) hs0⟩, ?_⟩
  intro p o hp
  change kheapR p = some o at hp
  change SInvI.ObjOK idleThreadPtr idleScPtr idleThreadPtr p o
  rcases kheapR_cases hp with ⟨e, e'⟩ | ⟨e, e'⟩ | ⟨-, -, h⟩
  · subst e e'
    exact ⟨fun e => absurd e tRp_ne_idle, fun _ e => scRp_ne_idle (Option.some.inj e),
      fun e => absurd e tRp_ne_idle⟩
  · subst e e'
    exact ⟨fun e => absurd e scRp_ne_idle, fun _ e => tRp_ne_idle (Option.some.inj e)⟩
  · exact hB p o h

theorem uA_ft_R : SInvF.FT (σR (Z := Unit)) := fun t ht => by
  simp [σR, σB, initArchState] at ht

theorem uA_idleScOut_R : SInvL.IdleScOutV (σR (Z := Unit)) := irqOut_R _ (fun _ => by decide) (fun _ => by decide)

theorem uA_ntfnScB_R : SInvL.NtfnScB (σR (Z := Unit)) := by
  intro n ntf c hn hc
  have hn' := uA_toB hn (fun _ => by simp) (fun _ _ => by simp)
  obtain ⟨y, k, hy, hs⟩ := SInvAll.boot_ntfnScB_B n ntf c hn' hc
  exact ⟨y, k, uA_ofB hy, hs⟩

theorem uA_scInv_R : SInvB.ScInv (σR (Z := Unit)) := by
  obtain ⟨⟨hBk, hFw⟩, hRn⟩ := SInvB.boot_scInv_B
  refine ⟨⟨fun u xu c hu hc => ?_, fun p y n u hp hu => ?_⟩, fun p y n hp => ?_⟩
  · rcases kheapR_cases hu with ⟨e, e'⟩ | ⟨-, e'⟩ | ⟨-, -, h⟩
    · subst e; cases e'; cases hc
      exact ⟨scR, 0, kheapR_scR, rfl, fun _ => List.cons_ne_nil _ _⟩
    · cases e'
    · obtain ⟨y, k, hy, h1, h2⟩ := hBk u xu c h hc
      exact ⟨y, k, uA_ofB hy, h1, h2⟩
  · rcases kheapR_cases hp with ⟨-, e'⟩ | ⟨e, e'⟩ | ⟨-, -, h⟩
    · cases e'
    · subst e; cases e'; cases hu
      exact ⟨tcbR, kheapR_tR, rfl⟩
    · obtain ⟨x, hx, h1⟩ := hFw p y n u h hu
      exact ⟨x, uA_ofB hx, h1⟩
  · rcases kheapR_cases hp with ⟨-, e'⟩ | ⟨-, e'⟩ | ⟨-, -, h⟩
    · cases e'
    · cases e'; exact fun _ => List.cons_ne_nil _ _
    · exact hRn p y n h

theorem uA_scKindR_R : SInvL.ScKindR (σR (Z := Unit)) := by
  intro s r b s' c' h1 h2 h3
  rcases capAt_R h1 with e | ⟨-, e⟩ | ⟨-, e⟩ <;> cases e
  rcases capAt_R h2 with e | ⟨-, e⟩ | ⟨-, e⟩ <;> subst e
  · simp [SInvU.capRng, objRefs] at h3
  · simp only [SInvU.capRng, objRefs, Set.mem_singleton_iff] at h3
    exact absurd h3.symm tRp_ne_scRp
  · exact ⟨0, rfl⟩

theorem uA_dom_R : DomListOK (σR (Z := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [σR, σB]
  · intro e he _; simp only [σR, σB, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl
  · simp [σR, σB]
  · simp only [σR, σB, domainEndMarker]; decide
  · simp only [σR, σB, domainEndMarker]; decide
  · simp [σR, σB]
  · intro e he; simp only [σR, σB, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> rfl

theorem uA_cs_R : SInvQ.CurScT (σR (Z := Unit)) := by
  intro x hx
  change kheapR tRp = some (.tcb x) at hx
  rw [kheapR_tR] at hx; cases hx; rfl

/-- **`ScLiveT` at `σR`**: the root thread is named by its thread cap, the root SC by its SC cap; `σB`'s live
objects are the idle pair. -/
theorem uA_scLiveT_R : SInvL.ScLiveT (SInvL.idleP (σR (Z := Unit))) (σR (Z := Unit)) := by
  intro p o hp hl h1 h2
  rcases kheapR_cases hp with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, -, h⟩
  · subst e; exact ⟨_, _, capAt_R_root, rfl⟩
  · subst e; exact ⟨_, _, capAt_R_tmo, rfl⟩
  · obtain ⟨s, c, hs, hn⟩ := SInvL.boot_scLiveT_B p o h hl h1 h2
    rw [SInvU.init_capAt_B hs] at hn
    simp [SInvL.NCap] at hn

/-- **`SInvA σR` from `ScLiveT`** (every other field proved). -/
theorem uA_sinvA_R_of (hT : SInvL.ScLiveT (SInvL.idleP (σR (Z := Unit))) (σR (Z := Unit))) :
    SInvAll.SInvA (σR (Z := Unit)) where
  vfh := uA_vfh_R
  cnDom := uA_cnDom_R
  fts := uA_fts_R
  nqb := uA_nqb_R
  ns := uA_ns_R
  sg := uA_sg_R
  idleOut := idleOut_R
  dom := uA_dom_R
  vim := fun _ _ => rfl
  vih := uA_vih_R
  vmt := ⟨BitVec.le_refl _, by show (0 : Nat) ≤ _; exact Nat.zero_le _⟩
  ut := uA_ut_R
  nq := uA_nq_R
  epq := uA_epq_R
  live := uA_live_R
  vi := uA_vi_R
  ft := uA_ft_R
  sl := ⟨⟨hT, uA_idleScOut_R, uA_ntfnScB_R, uA_scInv_R⟩, uA_scKindR_R⟩
  cs := uA_cs_R

theorem uA_sinvA_R : SInvAll.SInvA (σR (Z := Unit)) := uA_sinvA_R_of uA_scLiveT_R

/-! ## The rest of `SInvX` -/

theorem uA_ctExit_R : SInvAll.CtExit (σR (Z := Unit)) := ⟨tcbR, kheapR_tR, Or.inl rfl⟩

theorem uA_onlyIdle_R : SInvAll.OnlyIdle (σR (Z := Unit)) := by
  intro t x ht hs
  rcases kheapR_cases ht with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
  · cases e; cases hs
  · cases e
  · exact SInvAll.boot_onlyIdle_B t x h hs

theorem uA_t4_R : SInvQ.T4 (σR (Z := Unit)) :=
  ⟨SInvQ.dlok_of uA_dom_R, rfl, uA_TI (by simp [SInvQ.dom0, tcbR, defaultDomain])
    SInvQ.boot_t4_B.2.2⟩

theorem uA_ex_R : SInvQ.EX (σR (Z := Unit)) :=
  ⟨⟨⟨fun _ _ _ h => (List.not_mem_nil h).elim, trivial⟩,
    ⟨fun _ h => by simp [σR, σB] at h, fun _ h => by simp [σR, σB] at h, fun _ _ _ h => List.not_mem_nil h⟩⟩,
    fun _ _ h => List.not_mem_nil h, fun _ h => by simp [σR, σB] at h, uA_cs_R⟩

theorem uA_rb_R : SInvQ.RB (σR (Z := Unit)) := by
  refine ⟨⟨⟨fun _ _ _ h => by simp [σR, σB] at h, fun _ h => by simp [σR, σB] at h⟩,
    fun _ => ⟨fun _ _ h => by simp [σR, σB] at h, ⟨fun h => by simp [σR, σB] at h,
      fun h => by simp [σR, σB] at h⟩⟩, fun _ h => by simp [σR, σB] at h⟩, fun _ => Or.inl ?_⟩
  exact ⟨tcbR, kheapR_tR, rfl⟩

theorem uA_rpos_R : SInvE.RPos (σR (Z := Unit)) := by
  intro p y n hy
  rcases kheapR_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
  · cases e
  · cases e; intro _ hp; exact absurd rfl hp
  · exact SInvE.boot_rpos_B p y n h

theorem uA_bsa_R : Sched.BlockedScActive (σR (Z := Unit)) := by
  refine ⟨fun p y n t x hp hyt hx hq => ?_, fun p y n hp hr => ?_⟩
  · rcases kheapR_cases hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
    · cases e; simp [tcbR, ipcQueuedThreadState] at hq
    · cases e
    · rw [SInvR.init_tcbSt_B h] at hq; cases hq
  · rcases kheapR_cases hp with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
    · cases e
    · cases e; exact absurd rfl hr
    · exact SInvR.B8e.boot_bsa_B.replies p y n h hr

theorem uA_vb_R : SInvR.B8n.VB (σR (Z := Unit)) := by
  intro t hs hne _
  obtain ⟨x, -, -, -, hx, -, hr, -, -, -⟩ := Sched.schedulable_inv hs
  rcases kheapR_cases hx with ⟨e, -⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
  · exact absurd e hne
  · cases e
  · have e := SInvR.init_tcbSt_B h
    rw [e] at hr; simp [runnable] at hr

theorem uA_rdy_R : SInvR.Rdy (σR (Z := Unit)) := by
  refine ⟨fun d p t h => by simp [σR, σB] at h, fun t h => by simp [σR, σB] at h, fun t x c hx hb _ => ?_,
    fun p y n hy ha => ?_, fun t h => by simp [σR, σB] at h, fun y n hy => ?_⟩
  · exfalso
    rcases kheapR_cases hx with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
    · cases e
      rcases hb with ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ <;> cases h
    · cases e
    · have e := SInvR.init_tcbSt_B h
      rcases hb with ⟨_, h⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h⟩ <;> rw [e] at h <;> cases h
  · rcases kheapR_cases hy with ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, h⟩
    · cases e
    · cases e
      refine ⟨le_refl _, SInvR.minBudget_le_maxPeriod, ?_, fun _ => by simp [scR]⟩
      have := MAX_PERIOD.isLt
      simp [SInvR.rsum, scR]; omega
    · exact SInvR.boot_rdy_B.2.2.2.1 p y n h ha
  · change kheapR idleScPtr = some (.schedContext y n) at hy
    rw [uA_idleS] at hy
    exact SInvR.boot_idleHd_B y n hy

theorem uA_offReady_R : Sched.OffReady (σR (Z := Unit)) := by
  intro y n hy
  change kheapR scRp = some (.schedContext y n) at hy
  rw [kheapR_scR] at hy
  cases hy
  show (0 : Nat) + 0 ≤ 0
  rfl

theorem uA_cAx_R : SInvR.CAx (σR (Z := Unit)) :=
  fun _ => ⟨tcbR, scRp, scR, 0, kheapR_tR, rfl, kheapR_scR, uA_scActive_R⟩

/-- `SInvX σR` from `ScLiveT`. -/
theorem uA_sinvX_R_of (hT : SInvL.ScLiveT (SInvL.idleP (σR (Z := Unit))) (σR (Z := Unit))) :
    SInvR.G4.SInvX (σR (Z := Unit)) :=
  ⟨⟨⟨⟨⟨⟨⟨⟨uA_sinvA_R_of hT, uA_ctExit_R⟩, uA_onlyIdle_R⟩, uA_ex_R, uA_rb_R, uA_t4_R⟩, rfl⟩, uA_bsa_R⟩,
    uA_vb_R⟩, uA_rdy_R, uA_offReady_R, uA_cAx_R⟩, uA_rpos_R⟩

/-- **`SInvX` at the second boot start `σR`.** -/
theorem sinvX_R : SInvR.G4.SInvX (σR (Z := Unit)) := uA_sinvX_R_of uA_scLiveT_R

end

end Fl4Proofs.P2.BootSt
