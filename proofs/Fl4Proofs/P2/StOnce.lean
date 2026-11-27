/-
# P2: `ReadOnce` of the `TCB_SetTimer` tree (line hpzg, gen 3; gen 4 on `MaxR` without user words)

`set_timer_localPathG` (`P2/ProgGenStLP.lean`) left `hro` [W]: `E2E.ReadOnce` of
`R.localtimer.handle_set_timer_local n target` with `RS = MaxR`. Since vlift's gen 3, `MaxR` excludes the user
words (`w ∉ K.user`), so a run guarded on `MaxR` reads no racy user word:

* an entry that accepts, or declines with the target's deadline readable (`hfar`): the entry's run is guarded on
  `MaxR` (`set_timer_acc_own`; `set_timer_dec_guard`), so is every alternative's (`interp_agree`), and a run
  guarded on a read set without user words is `Once` (`once_of_guardG`);
* otherwise (the target is of this core and armed in another core's tree): at an alternative the run reads `MaxR`
  words up to the target check, then the target's `TIMER_DEADLINE` (the one racy read, nothing touched before
  it), then this core's tree (`MaxR`, `in_core_timer_tree_access`), which does not hold the target
  (`in_core_found`), and declines.

* `st_hro`: **`hro` of `set_timer_localPathG` holds**;
* `set_timer_localPathG2`: the `TCB_SetTimer` local path with `IsProg`, `NoZero` and `ReadOnce` discharged;
* `tm_pathsKG2` / `tm_pathsKG2_startAt`: SlJStLocTop's `tm_pathsK` with its program premise family `hpz` fully
  discharged.

No new premise: the user-word facts come from the entry's `StLay` (`user` / `domU` / `dtmU`, derived from P3 by
`SlJAtZ.stLay`). Premises otherwise `set_timer_localPathG`'s minus `hro`.
-/
import Fl4Proofs.P2.FootTimerSetDec
import Fl4Proofs.P2.ProgGenStLP
import Fl4Proofs.P2.OnceWalk
import Fl4Proofs.P2.FootTimerSetObl
import Fl4Proofs.P2.FootTimerSetLP
import Fl4Proofs.P2.ProgGenWire
import Fl4Proofs.P2.IoOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.E2E (Once ReadOnce)


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

variable {target : U64} {m : U64 → U64} {lk : S → U64 → Prop}
variable {A : Type} (ar : machine.Arch A) (n : I64)

set_option maxHeartbeats 8000000 in
/-- **`hro` of `set_timer_localPathG` holds** (module docstring). -/
theorem st_hro (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K) (hm : E2E.MasksWr st) :
    E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local n target) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m) (MaxR K st lk) := by
  intro s s' a r' hEK Al h
  have hE := hEK.ent
  have eP : ∀ (mm : machine.Store S) (x : S),
      localtimer.handle_set_timer_local mm ar x a n target = interp mm ar (R.localtimer.handle_set_timer_local n target) x a :=
    fun mm x => congrFun (congrFun (st_isProg S n target A ar mm) x) a
  have hz := st_noZero n target
  have hRU : ∀ q, MaxR K st lk s q → q ∉ K.user := fun q hq => hq.2.2
  -- a guarded run at the entry gives a guarded run at the alternative
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localtimer.handle_set_timer_local (guard st (MaxR K st lk s) W') ar s a n target =
        ok (x, s1, a1) →
      Once st ar (MaxR K st lk s) (· ∈ K.user) ∅ ∅ (R.localtimer.handle_set_timer_local n target) s' a := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.2.1) hWa _ hz s s' a x s1 a1 Al.ksb Al.cpu Al.masks
      (fun w hw => Al.read w hw) hg
    exact PathObl.once_of_guardG (User := (· ∈ K.user)) hRU _ hz ∅ ∅ s' a _ hg'
  obtain ⟨r0, hr0⟩ : ∃ r, localtimer.handle_set_timer_local st ar s a n target = ok r := by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st ar s a n target LawfulStore.total hA)
    exact ⟨r, e⟩
  obtain ⟨b0, s1, a1⟩ := r0
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  cases b0
  swap
  · -- accepted at the entry
    exact tr (W' := MaxW K st lk s) (fun _ hw => hw.2) (set_timer_acc_own ar hA hE.inv hE.tg hE.lay hE.aff hr0)
  by_cases hfar : L.mem s (affA target) ≠ L.cpu s ∨ L.mem s (tdA target) = 0#u64 ∨
      (L.mem s (thA target)).val >>> 8 = (L.cpu s).val
  · exact tr (W' := StDec st s) (fun _ hw => (hE.dec hw).1)
      (set_timer_dec_guard ar hA (lk := lk) hE.inv hE.tg hE.lay hE.pre hE.aff hfar hr0)
  -- the target is of this core and armed in another core's tree: walk the tree
  rw [not_or, not_or, not_not] at hfar
  obtain ⟨hat, hd, hh⟩ := hfar
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk hE.inv)).tree _ h0.cur
  have hL := hE.lay
  set R' : U64 → Prop := MaxR K st lk s with eR'
  have nuT : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → core.num.U64.wrapping_add x k ∉ K.user :=
    fun hx h1 h2 => hL.nu_tcb hx h1 h2
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R' (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    ⟨Or.inl (held_core (hL.own_node _ h1)), nodeAt_aligned hN h1 h2, hL.nu_node h1⟩
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have cR : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      R' (core.num.U64.wrapping_add (L.curW s) k) := fun k h1 h2 h3 h4 => by
    have e := caller_own' hL hT hcT hE.pre.aff hE.pre.nq h1 h2 h4
    refine ⟨?_, field_aligned ht' h2 h3, nuT hcT h1 h2⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have rR : ∀ r : U64, r.val < 384 → R' (regA (L.curW s) r) := fun r hr => by
    obtain ⟨k, hk, e⟩ := regA_eq ht' hr
    rw [e]; exact cR k (by omega) (by omega) (by omega) (by omega)
  have rAt : R' (affA target) := ⟨Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hE.tg (k := 3520#u64) (by simp) (by simp)
      unfold fld at e
      unfold GateOnly affA; rw [e, tcbOwner, if_pos (show GateField (3520#u64).val from Or.inl (by simp))]),
    field_aligned (hT _ hE.tg) (by simp) (by simp), nuT hE.tg (by simp) (by simp)⟩
  have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R' (core.num.U64.wrapping_add y k) := by
    intro y hy k h1 h2 h3
    refine ⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3,
      nuT (ct.inT y hy) (by omega) (by omega)⟩
    have e := hL.own_tcb hT (L.mem s) (ct.inT y hy) (k := k) (by omega) (by omega)
    unfold fld at e
    rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
      if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
      if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from
        fun h => ct.armed y hy (UScalar.eq_of_val_eq h))]
    have e2 := ct.core y hy
    rw [Nat.shiftRight_eq_div_pow] at e2
    exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)
  have eN : ∀ o, L.nodeAt s' (L.cpu s) o = L.nodeAt s (L.cpu s) o := fun o => nodeAt_of_ksb Al.ksb _ o
  have ct' : CoreTree st T s' (L.cpu s) W0 := CoreTree.agree ct eN
    (Al.read _ (nR _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])))
    (Al.read _ (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
    (fun y hy => ⟨Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)),
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)),
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)),
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)),
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp))⟩)
  have hk : target ∉ W0.keys := fun h => hh (ct.core target h)
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW
    rw [Al.cpu, eN]
    exact Al.read _ (nR _ (by rw [curth_val]; omega) (by rw [curth_val]))
  have nR' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R' (L.nodeAt s' (L.cpu s') o) := fun o h1 h2 => by
    rw [Al.cpu, eN]; exact nR o h1 h2
  have hR0 : ∀ q, R' q → R' q ∧ q ∉ K.user := fun q hq => ⟨hq, hq.2.2⟩
  have hW0 : ∀ q, R' q → q ∉ K.user := fun q hq => hq.2.2
  -- the walk, on `R' = MaxR s` (no user words)
  unfold R.localtimer.handle_set_timer_local at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sched.cur_thread_nz) h (fun r h1 => ?_) (fun r h1 hk1 Wd1 _ => ?_)
  · rw [R.sched.cur_thread_eq] at h1 ⊢
    rw [PathObl.sched.cur_thread.guard (gS := guard st R' R') s' (nR' _ (by rw [curth_val]; omega) (by rw [curth_val]))]
    exact h1
  replace h := hk1
  rw [R.sched.cur_thread_eq] at h1
  obtain ⟨t, et, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  rw [cur_thread_ok, hcur] at et
  have et' : t = L.curW s := (ok_inj_ff et).symm
  subst et'
  -- the core
  simp only [SProg.curCpu, SProg.sbind, Once] at h ⊢
  intro cpu hcpu
  simp only [interp] at h
  obtain ⟨cpu', hcpu', h⟩ := bok.mp h
  rw [hcpu] at hcpu'
  have ecpu : cpu = L.cpu s := by
    rw [L.cur_cpu_eq, Al.cpu] at hcpu; exact (ok_inj_ff hcpu).symm
  cases ok_inj_ff hcpu'
  subst ecpu
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.msg.msg_info_nz _) h (fun r h1 => ?_) (fun r h1 hk1 Wd2 _ => ?_)
  · rw [R.msg.msg_info_eq] at h1 ⊢
    rw [PathObl.msg.msg_info.guard (gS := guard st R' R') s' _ (rR _ (by simp [layout.reg.MSG_INFO]))]
    exact h1
  replace h := hk1
  rw [R.msg.msg_info_eq] at h1
  obtain ⟨info, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.obj.Tcb.flags_nz _) h (fun r h1 => ?_) (fun r h1 hk1 Wd3 _ => ?_)
  · rw [R.obj.Tcb.flags_eq] at h1 ⊢
    rw [PathObl.obj.Tcb.flags.guard (gS := guard st R' R') _ s' (cR _ (by simp) (by simp) (by simp) (by simp))]
    exact h1
  replace h := hk1
  rw [R.obj.Tcb.flags_eq] at h1
  obtain ⟨i, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  refine once_ite0 h (fun _ _ => by simp only [Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.sched.cur_sc_nz) h (fun r h1 => ?_) (fun r h1 hk1 Wd4 _ => ?_)
  · rw [R.sched.cur_sc_eq] at h1 ⊢
    rw [PathObl.sched.cur_sc.guard (gS := guard st R' R') s' (nR' _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
    exact h1
  replace h := hk1
  rw [R.sched.cur_sc_eq] at h1
  obtain ⟨csc, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  -- the target check
  unfold R.localtimer.set_timer_target_ok at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.obj.Tcb.affinity_nz _) h (fun r h1 => ?_) (fun r h1 hk1 Wd5 _ => ?_)
  · rw [R.obj.Tcb.affinity_eq] at h1 ⊢
    rw [PathObl.obj.Tcb.affinity.guard (gS := guard st R' R') target s' rAt]
    exact h1
  replace h := hk1
  rw [R.obj.Tcb.affinity_eq] at h1
  obtain ⟨i1, -, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  refine once_ite h (fun _ _ => by simp only [SProg.sbind, Bool.false_eq_true, ↓reduceIte, Once]) (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  -- the deadline: the one racy read
  unfold R.obj.Tcb.timer_deadline at h ⊢
  simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret, SProg.sbind_assoc, SProg.sbind, SProg.read] at h ⊢
  refine once_liftR h (fun i0 hi0 h => ?_)
  simp only [SProg.sbind, Once] at h ⊢
  refine ⟨fun _ => Set.notMem_empty _, fun v hv => ?_⟩
  simp only [interp] at h
  obtain ⟨v', hv', h⟩ := bok.mp h
  rw [hv] at hv'
  cases ok_inj_ff hv'
  have hdv : L.mem s' (tdA target) = v := by
    have e : obj.Tcb.timer_deadline st target s' = ok v := by
      unfold obj.Tcb.timer_deadline
      rw [hi0]
      simp only [lift, bind_ok]
      exact hv
    rw [td_ok] at e; exact ok_inj_ff e
  have hd' : L.mem s' (tdA target) ≠ 0#u64 := by
    by_cases hin : MaxR K st lk s (tdA target)
    · rw [Al.read _ hin]; exact hd
    · have e := Al.clsEq _ hin (set_timer_user hK hUO hE) (Or.inr (set_timer_ko hK hUO hEK hat))
      exact fun h0 => hd ((set_timer_cls hE _ _ e).1 h0)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_ite h (fun hv0 _ => absurd (hdv.trans hv0) hd') (fun _ h => ?_)
  try simp only [SProg.sbind_assoc, SProg.sbind] at h ⊢
  refine once_gstep hR0 hW0 (R.localtimer.in_core_timer_tree_nz _ _ _) h (fun r h1 => ?_) (fun r h1 hk1 Wd6 _ => ?_)
  · rw [R.localtimer.in_core_timer_tree_eq] at h1 ⊢
    obtain ⟨b, eb, rfl⟩ := bind_shape h1
    rw [in_core_timer_tree_access (gS := guard st R' R') ct' (fun w hw => by
      rcases hw with rfl | rfl | ⟨y, hy, rfl | rfl | rfl⟩
      · rw [eN]; exact nR _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])
      · rw [eN]; exact nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      · exact keyR y hy _ (by simp) (by simp) (by simp)
      · exact keyR y hy _ (by simp) (by simp) (by simp)
      · exact keyR y hy _ (by simp) (by simp) (by simp)) eb]
    exact bok.mpr ⟨b, rfl, rfl⟩
  replace h := hk1
  rw [R.localtimer.in_core_timer_tree_eq] at h1
  obtain ⟨b, eb, rfl⟩ := bind_shape h1
  dsimp only at h ⊢
  have hb : b = false := by
    cases b
    · rfl
    · exact absurd (in_core_found ct' eb) hk
  subst hb
  simp only [Bool.false_eq_true, ↓reduceIte, SProg.sbind, Once]

/-- **`TCB_SetTimer` with `IsProg`, `NoZero`, `move` and `ReadOnce` discharged** (module docstring):
`set_timer_localPathM` (FootTimerSetMv, `move` proved) at the generated tree with `hro := st_hro`. -/
noncomputable def set_timer_localPathG2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hm : E2E.MasksWr st)
    (hEU : ∀ s b v, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → b ∈ K.user → Aligned b →
      StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → ∀ o : U64, o.val < 4288 →
      L.nodeAt s (L.cpu s) o ∉ K.user) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  set_timer_localPathM (lk := lk) ar n hA hK hUO (st_isProg S n target) (st_noZero n target) hm
    (st_hro ar n hA hK hUO hm) hEU hlk hNU

end

/-! ## The top-level `TCB_SetTimer` path member, program premise family discharged -/

section tm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop}
variable {A : Type}
open Fl4Proofs.P2.PathObl (StEntKK lpRestrict SlJAt tm_pathsK)

/-- **`tm_pathsK` with `hpz` fully discharged** (module docstring): at each layout, `set_timer_localPathG2`
narrowed to `Pre := SlJAt K ∧ Q K m` by `lpRestrict`. -/
noncomputable def tm_pathsKG2 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hEU : ∀ K s b v, StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ K.user → Aligned b →
      StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac target (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ K s, StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v)) :
    E2E.Paths Unit :=
  fun _ K m hK hU =>
    lpRestrict
      (set_timer_localPathG2 (lk := lk) ar n hA hK hU hm (hEU K) (hlk K) (hNU K))
      (fun s => SlJAt (L := L) K s ∧ Q K m s) (fun s h => hPE K m s h.1 h.2)
      (fun s b v h hb ha => huf K m s b v h.1 h.2 hb ha)

/-- **`StartAt` for `tm_pathsKG2`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem tm_pathsKG2_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hEU : ∀ K s b v, StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ K.user → Aligned b →
      StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac target (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ K s, StEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ K.user)
    (huf : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b →
      SlJAt (L := L) K (L.wr s b v) ∧ Q K m (L.wr s b v))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hQ : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt
      (tm_pathsKG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hEU hlk hNU
        huf () K m hK hU) c hs μ
      ((tm_pathsKG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hEU hlk hNU
        huf () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hQ⟩, hc, hl, hμ, rfl⟩

end tm

end Fl4Proofs.P2
