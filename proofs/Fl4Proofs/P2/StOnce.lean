/-
# P2: `ReadOnce` of the `TCB_SetTimer` tree (line hpzg, gen 3)

`set_timer_localPathG` (`P2/ProgGenStLP.lean`) left `hro` [W]: `E2E.ReadOnce` of
`R.localtimer.handle_set_timer_local n target` with `RS = MaxR`. `MaxR` holds the user words (the gate's by
`own`), which are racy for `Once` whatever the read set, so the runs are put on the guard of `MaxR` without the
user words (`R'`):

* an entry that accepts, or declines with the target's deadline readable (`hfar`): the entry's run is guarded on
  `R'` (`set_timer_acc` with `st_rd_nouser`; `set_timer_dec_guardU`, `P2/StOnceA.lean`), so is every
  alternative's (`interp_agree`), and a run guarded on a read set without user words is `Once`
  (`once_of_guardG`);
* otherwise (the target is of this core and armed in another core's tree): at an alternative the run reads `R'`
  words up to the target check, then the target's `TIMER_DEADLINE` (the one racy read, nothing touched before
  it), then this core's tree (`R'`, `in_core_timer_tree_access`), which does not hold the target
  (`in_core_found`), and declines.

* `st_rd_nouser`: the accepted run's reads (`StRd`) are no user words;
* `st_hro`: **`hro` of `set_timer_localPathG` holds**;
* `set_timer_localPathG2`: the `TCB_SetTimer` local path with `IsProg`, `NoZero` and `ReadOnce` discharged;
* `tm_pathsKG2` / `tm_pathsKG2_startAt`: SlJStLocTop's `tm_pathsK` with its program premise family `hpz` fully
  discharged.

New premises (layout facts, [J]): `hUK` (user words lie in no region of the layout) and `hUD` (at an entry, the
kernel-state words `CUR_DOMAIN` / `DOMAIN_TIME` are no user words). Otherwise `set_timer_localPathG`'s minus `hro`.
-/
import Fl4Proofs.P2.StOnceA
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

section mono
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} {User : U64 → Prop}

theorem PathObl.racy_mono_R {R R' : U64 → Prop} (hRR : ∀ q, R' q → R q) {Wd : Set U64} {q : U64}
    (h : E2E.Racy R User Wd q) : E2E.Racy R' User Wd q := by
  unfold E2E.Racy at *
  rintro ⟨h1, h2⟩
  exact h ⟨h1, h2.imp_left (hRR q)⟩

theorem PathObl.tch_mono_R {R R' : U64 → Prop} (hRR : ∀ q, R' q → R q) {Wd T T' : Set U64} {q : U64}
    (hT : T ⊆ T') : E2E.tch R User Wd q T ⊆ E2E.tch R' User Wd q T' := by
  by_cases hr : E2E.Racy R User Wd q
  · have e1 : E2E.tch R User Wd q T = insert q T := by unfold E2E.tch; exact if_pos hr
    have e2 : E2E.tch R' User Wd q T' = insert q T' := by
      unfold E2E.tch; exact if_pos (PathObl.racy_mono_R hRR hr)
    rw [e1, e2]; exact Set.insert_subset_insert hT
  · have e1 : E2E.tch R User Wd q T = T := by unfold E2E.tch; exact if_neg hr
    rw [e1]; exact hT.trans E2E.tch_sub

/-- **`Once` for a smaller read set**: the racy words of `R` are racy for `R' ⊆ R`. -/
theorem PathObl.once_mono_R {X : Type} {R R' : U64 → Prop} (hRR : ∀ q, R' q → R q) (p : SProg X) :
    ∀ (Wd T T' : Set U64) (s : S) (a : A), Once st ar R' User Wd T' p s a → T ⊆ T' →
      Once st ar R User Wd T p s a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (PathObl.racy_mono_R hRR hr) (hT hq),
      fun v hv => ih v _ _ _ s a (h.2 v hv) (PathObl.tch_mono_R hRR hT)⟩
  | rdp q k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact ⟨fun hr hq => h.1 (PathObl.racy_mono_R hRR hr) (hT hq),
      fun hr hq => h.2.1 (PathObl.racy_mono_R hRR hr) (PathObl.tch_mono_R hRR hT hq),
      fun v hv => ih v _ _ _ s a (h.2.2 v hv) (PathObl.tch_mono_R hRR (PathObl.tch_mono_R hRR hT))⟩
  | wr q v k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    intro s' hs'
    have h1 := h s' hs'
    by_cases hu : User q
    · simp only [if_pos hu] at h1 ⊢
      exact ih _ _ _ s' a h1 (Set.insert_subset_insert hT)
    · simp only [if_neg hu] at h1 ⊢
      exact ih _ _ _ s' a h1 hT
  | zero q n k ih => intro Wd T T' s a h; simp only [Once] at h
  | clr q n k ih => intro Wd T T' s a h; simp only [Once] at h
  | ksb k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | cpu k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | masks k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v hv => ih v _ _ _ s a (h v hv) hT
  | arch op k ih =>
    intro Wd T T' s a h hT
    simp only [Once] at h ⊢
    exact fun v a' hv => ih v _ _ _ s a' (h v a' hv) hT

end mono

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **The accepted run's reads are no user words** (module docstring). -/
theorem st_rd_nouser {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hL : StLay K st T Scs Z s)
    (hUK : ∀ b ∈ K.user, region K b = .none)
    (hUD : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.user ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.user)
    {target w : U64} (htg : target ∈ T) (ho : StOk st Scs s target)
    (h : StRd st T Z s target w) : w ∉ K.user := by
  have h0 := hI.1.choose_spec.choose_spec
  have nuT : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → core.num.U64.wrapping_add x k ∉ K.user :=
    fun hx h1 h2 hu => by
      have e := hL.tcb _ hx _ h1 h2
      unfold fld at e
      rw [hUK _ hu] at e; cases e
  have nuS : ∀ {p b : U64}, p ∈ Scs → InSC p (Z p) b → b ∉ K.user := fun hp hb hu => by
    have e := hL.sc _ hp _ hb
    rw [hUK _ hu] at e; cases e
  rcases h with h | ⟨k, h1, h2, -, h4, rfl⟩ | rfl | rfl | rfl | h | ⟨hne, rfl | h⟩
  · rcases h with ⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho', h8, rfl⟩
    · exact nuT hz.1 (by omega) (by omega)
    · intro hu
      have e := hL.nd o ho'
      rw [hUK _ hu] at e; cases e
  · exact nuT h0.curT h1 h2
  · exact nuT htg (by simp) (by simp)
  · exact hUD.1
  · exact hUD.2
  · exact nuS ho.csc h
  · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
    exact nuT r1 (by simp) (by simp)
  · obtain ⟨-, -, -, r4, -⟩ := rel_facts hI hne
    exact nuS r4 h

variable {target : U64} {m : U64 → U64} {lk : S → U64 → Prop}
variable {A : Type} (ar : machine.Arch A) (n : I64)

set_option maxHeartbeats 8000000 in
/-- **`hro` of `set_timer_localPathG` holds** (module docstring). -/
theorem st_hro (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K) (hm : E2E.MasksWr st)
    (hUK : ∀ s, StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s → ∀ b ∈ K.user, region K b = .none)
    (hUD : ∀ s, StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s →
      core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.user ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.user) :
    E2E.ReadOnce st ar (R.localtimer.handle_set_timer_local n target) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m) (MaxR K st lk) := by
  intro s s' a r' hEK Al h
  have hE := hEK.ent
  have hUK := hUK s hEK
  have eP : ∀ (mm : machine.Store S) (x : S),
      localtimer.handle_set_timer_local mm ar x a n target = interp mm ar (R.localtimer.handle_set_timer_local n target) x a :=
    fun mm x => congrFun (congrFun (st_isProg S n target A ar mm) x) a
  have hz := st_noZero n target
  have hRU : ∀ q, (fun w => MaxR K st lk s w ∧ w ∉ K.user) q → q ∉ K.user := fun q hq => hq.2
  -- a guarded run at the entry gives a guarded run at the alternative
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localtimer.handle_set_timer_local (guard st (fun w => MaxR K st lk s w ∧ w ∉ K.user) W') ar s a n target =
        ok (x, s1, a1) →
      Once st ar (MaxR K st lk s) (· ∈ K.user) ∅ ∅ (R.localtimer.handle_set_timer_local n target) s' a := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1.2) hWa _ hz s s' a x s1 a1 Al.ksb Al.cpu Al.masks
      (fun w hw => Al.read w hw.1) hg
    have := PathObl.once_of_guardG (User := (· ∈ K.user)) hRU _ hz ∅ ∅ s' a _ hg'
    exact PathObl.once_mono_R (fun q hq => hq.1) _ ∅ ∅ ∅ s' a this subset_rfl
  obtain ⟨r0, hr0⟩ : ∃ r, localtimer.handle_set_timer_local st ar s a n target = ok r := by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st ar s a n target LawfulStore.total hA)
    exact ⟨r, e⟩
  obtain ⟨b0, s1, a1⟩ := r0
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  cases b0
  swap
  · -- accepted at the entry
    refine tr (W' := MaxW K st lk s) (fun _ hw => hw.2) (set_timer_acc ar hA hE.inv hE.tg
      (fun ho w ha hw => ⟨⟨st_rd_own hE.inv hE.lay hE.aff hE.tg ho hw, ha⟩,
        st_rd_nouser hE.inv hE.lay hUK (hUD s hEK) hE.tg ho hw⟩)
      (fun ho w ha hw => ⟨st_wr_own hE.inv hE.lay ho hw, ha⟩)
      (fun ho => ⟨⟨st_rd_own hE.inv hE.lay hE.aff hE.tg ho (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hE.lay.domA⟩,
        (hUD s hEK).1⟩)
      (fun ho => ⟨⟨st_rd_own hE.inv hE.lay hE.aff hE.tg ho (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
        hE.lay.dtmA⟩, (hUD s hEK).2⟩) hr0)
  by_cases hfar : L.mem s (affA target) ≠ L.cpu s ∨ L.mem s (tdA target) = 0#u64 ∨
      (L.mem s (thA target)).val >>> 8 = (L.cpu s).val
  · exact tr (W' := StDec st s) (fun _ hw => (hE.dec hw).1)
      (set_timer_dec_guardU ar hA (lk := lk) hE.inv hE.tg hE.lay hE.pre hE.aff hfar hUK (hUD s hEK) hr0)
  -- the target is of this core and armed in another core's tree: walk the tree
  rw [not_or, not_or, not_not] at hfar
  obtain ⟨hat, hd, hh⟩ := hfar
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk hE.inv)).tree _ h0.cur
  have hL := hE.lay
  set R' : U64 → Prop := fun w => MaxR K st lk s w ∧ w ∉ K.user with eR'
  have nuT : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → core.num.U64.wrapping_add x k ∉ K.user :=
    fun hx h1 h2 hu => by
      have e := hL.tcb _ hx _ h1 h2
      unfold fld at e
      rw [hUK _ hu] at e; cases e
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R' (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    ⟨⟨Or.inl (held_core (hL.own_node _ h1)), nodeAt_aligned hN h1 h2⟩, fun hu => by
      have e := hL.nd o h1
      rw [hUK _ hu] at e; cases e⟩
  have hcT : L.curW s ∈ T := h0.curT
  have ht' := hT _ hcT
  have cR : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      R' (core.num.U64.wrapping_add (L.curW s) k) := fun k h1 h2 h3 h4 => by
    have e := caller_own' hL hT hcT hE.pre.aff hE.pre.nq h1 h2 h4
    refine ⟨⟨?_, field_aligned ht' h2 h3⟩, nuT hcT h1 h2⟩
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have rR : ∀ r : U64, r.val < 384 → R' (regA (L.curW s) r) := fun r hr => by
    obtain ⟨k, hk, e⟩ := regA_eq ht' hr
    rw [e]; exact cR k (by omega) (by omega) (by omega) (by omega)
  have rAt : R' (affA target) := ⟨⟨Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hE.tg (k := 3520#u64) (by simp) (by simp)
      unfold fld at e
      unfold GateOnly affA; rw [e, tcbOwner, if_pos (show GateField (3520#u64).val from Or.inl (by simp))]),
    field_aligned (hT _ hE.tg) (by simp) (by simp)⟩, nuT hE.tg (by simp) (by simp)⟩
  have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      R' (core.num.U64.wrapping_add y k) := by
    intro y hy k h1 h2 h3
    refine ⟨⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3⟩,
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
    (Al.read _ (nR _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])).1)
    (Al.read _ (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1)
    (fun y hy => ⟨Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)).1,
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)).1,
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)).1,
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)).1,
      Al.read _ (keyR y hy _ (by simp) (by simp) (by simp)).1⟩)
  have hk : target ∉ W0.keys := fun h => hh (ct.core target h)
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW
    rw [Al.cpu, eN]
    exact Al.read _ (nR _ (by rw [curth_val]; omega) (by rw [curth_val])).1
  have nR' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R' (L.nodeAt s' (L.cpu s') o) := fun o h1 h2 => by
    rw [Al.cpu, eN]; exact nR o h1 h2
  have hR0 : ∀ q, R' q → R' q ∧ q ∉ K.user := fun q hq => ⟨hq, hq.2⟩
  have hW0 : ∀ q, R' q → q ∉ K.user := fun q hq => hq.2
  -- the walk, on `R'`, then weakened to `MaxR s`
  suffices hO : Once st ar R' (· ∈ K.user) ∅ ∅ (R.localtimer.handle_set_timer_local n target) s' a from
    PathObl.once_mono_R (fun q hq => hq.1) _ ∅ ∅ ∅ s' a hO subset_rfl
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
    (hUK : ∀ s, StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s → ∀ b ∈ K.user, region K b = .none)
    (hUD : ∀ s, StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s →
      core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.user ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.user)
    (hEU : ∀ s b v, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → b ∈ K.user → Aligned b →
      StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → ∀ o : U64, o.val < 4288 →
      L.nodeAt s (L.cpu s) o ∉ K.user) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  set_timer_localPathM (lk := lk) ar n hA hK hUO (st_isProg S n target) (st_noZero n target) hm
    (st_hro ar n hA hK hUO hm hUK hUD) hEU hlk hNU

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
    (hUK : ∀ K m s, StEntKK K st Cs Ω Sg Ac target m s → ∀ b ∈ K.user, region K b = .none)
    (hUD : ∀ K m s, StEntKK K st Cs Ω Sg Ac target m s →
      core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.user ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.user)
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
      (set_timer_localPathG2 (lk := lk) ar n hA hK hU hm (hUK K m) (hUD K m) (hEU K) (hlk K) (hNU K))
      (fun s => SlJAt (L := L) K s ∧ Q K m s) (fun s h => hPE K m s h.1 h.2)
      (fun s b v h hb ha => huf K m s b v h.1 h.2 hb ha)

/-- **`StartAt` for `tm_pathsKG2`** at a layout `K` from `SlJAt K σ ∧ Q K m σ`. -/
theorem tm_pathsKG2_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hm : E2E.MasksWr st) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s → StEntKK K st Cs Ω Sg Ac target m s)
    (hUK : ∀ K m s, StEntKK K st Cs Ω Sg Ac target m s → ∀ b ∈ K.user, region K b = .none)
    (hUD : ∀ K m s, StEntKK K st Cs Ω Sg Ac target m s →
      core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.user ∧
      core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.user)
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
      (tm_pathsKG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hUK hUD hEU hlk hNU
        huf () K m hK hU) c hs μ
      ((tm_pathsKG2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) ar hA n target hm Q hPE hUK hUD hEU hlk hNU
        huf () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hQ⟩, hc, hl, hμ, rfl⟩

end tm

end Fl4Proofs.P2
