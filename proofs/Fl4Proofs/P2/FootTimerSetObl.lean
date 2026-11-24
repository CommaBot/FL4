/-
# P2: `PathObl` and `PathSide` for the `TCB_SetTimer` local path

`set_timer_pathObl` / `set_timer_pathSide`: the per-path obligation of `localtimer.handle_set_timer_local` with the
maximal sets `MaxR` / `MaxW` (the aligned words the path may read / write at the entry state) and
`DecSet = StDec` (`FAULT_IP`, the timestamp words), for the ownership map `OwnMap.own K`.

`dec_alt`: if the declined run may read the target's deadline (`set_timer_dec_guard`), its reads are all in `MaxR`, so
it is the same run at every alternative (`interp_agree`). Otherwise the target is of this core and armed in another
core's tree: an alternative keeps the target's affinity (the gate's), this core's tree (its own) and, by the class
of the deadline word, that the target is armed, so it declines at `set_timer_target_ok` (`set_timer_far`). No local
path changes whether such a target is armed: `timer::fire` beside the gate fires only the plan's thread, of the
firing core (`plan_objects`), so the class owner of `TIMER_DEADLINE` (zero / nonzero) is the thread's home core.

Premises:
* `hp` [P] (`IsProg`), `hz` [W] (`NoZero`), `hm` [P] (writes leave `frame_masks`), as in `P2/PathBridge` / E2E;
* `hK` [J] (`RegionOK`), `hUO` [J] (`E2E.UserOK`, the deciding words are aligned), `StLay` [J], and in `StEnt` the
  core-placement facts of p2j's `P2/InvAff` [J];
* `hcls` / `hko` [P] on the class map: the target's `TIMER_DEADLINE` has the class zero / nonzero, owned by the
  thread's home core (a change to `OwnMap.cls` / `OwnMap.ko`, p2c's line); `hkoF`, `hkoA`, `hU`: the prefix's words
  are untracked, tracked words aligned, the deadline no user word;
* `hmv` [W]: `move` of accepted runs (pending the kernel's write reorder, `P2/MoveTimer`);
* `huf` [J] (`PathSide.user_free`).
-/
import Fl4Proofs.P2.FootTimerSetFar
import Fl4Proofs.P2.E2E
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)
open Fl4Proofs.P2.OwnMap
open Classical
open Fl4Proofs.P2.PathObl (guard mguard RPerm WPerm HeldBy GateOnly SProg IsProg NoZero interp interp_agree interp_mono
  interp_guard interp_to_mguard StepOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **A write of a word that decides no owner** (a node word, or a TCB word below `STATE`) moves no owner. -/
theorem own_keep (hK : RegionOK K) (hUO : E2E.UserOK K) {q : U64} (hq : Aligned q)
    (hr : (∃ c, region K q = .node c) ∨ (∃ t, region K q = .tcb t ∧ q.val - t.val < 3328)) (s : S) (v x : U64) :
    own K (L.mem (L.wr s q v)) x = own K (L.mem s) x := by
  have ne : ∀ y, Aligned y → q ≠ y → L.mem (L.wr s q v) y = L.mem s y := fun y hy hn => mem_wr_ne' hq hy hn
  have tw : ∀ t, K.heap t = some .tcb → ∀ off, (off = oAFFINITY ∨ off = oSTATE ∨ off = oBLOCK_OBJ ∨
      off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT) →
      L.mem (L.wr s q v) (fld t off) = L.mem s (fld t off) := by
    intro t ht off ho
    obtain ⟨r1, r2⟩ := hK.tcb t ht off (by rcases ho with h | h | h | h | h <;> simp only [h, true_or, or_true])
    have hv : 3328 ≤ off.val := by
      rcases ho with rfl | rfl | rfl | rfl | rfl <;>
        simp [oAFFINITY, oSTATE, oBLOCK_OBJ, oTIMER_DEADLINE, oTIMER_HEIGHT]
    refine ne _ (hUO.tcb t ht off ho).1 fun e => ?_
    subst e
    rcases hr with ⟨c, hc⟩ | ⟨t', hc, hlt⟩
    · rw [r1] at hc; cases hc
    · rw [r1] at hc; cases hc; omega
  have nr : ∀ y, Aligned y → (∀ c, region K y ≠ .node c) → (∀ t, region K y ≠ .tcb t) →
      L.mem (L.wr s q v) y = L.mem s y := fun y hy h1 h2 => ne y hy fun e => by
    subst e
    rcases hr with ⟨c, hc⟩ | ⟨t', hc, -⟩
    · exact h1 c hc
    · exact h2 t' hc
  cases hR : region K x with
  | node c => simp only [own, hR]
  | obj p => simp only [own, hR]
  | none => simp only [own, hR]
  | slot p =>
    have hps := hK.slotOf p x hR
    have e := nr p (hUO.slot p hps).1 (fun c h => by rw [hK.slot p hps] at h; cases h)
      (fun c h => by rw [hK.slot p hps] at h; cases h)
    simp only [own, hR, slotOwner, e]
  | sc p =>
    obtain ⟨h16, -⟩ := hK.scw p x hR
    have e := nr (fld p 16#u64) (hUO.sc p x hR).1 (fun c h => by rw [h16] at h; cases h)
      (fun c h => by rw [h16] at h; cases h)
    simp only [own, hR, e]
  | ntfn p =>
    have hpn := hK.ntfnOf p x hR
    obtain ⟨h24, -⟩ := hK.ntfn p hpn
    have e := nr (fld p 24#u64) (hUO.ntfn p hpn).1 (fun c h => by rw [h24] at h; cases h)
      (fun c h => by rw [h24] at h; cases h)
    simp only [own, hR, ntfnOwner, e]
    by_cases hb : K.heap (L.mem s (fld p 24#u64)) = some .tcb
    · simp only [if_pos hb, tw _ hb oAFFINITY (Or.inl rfl)]
    · simp only [if_neg hb]
  | tcb t =>
    have ht := hK.tcbOf t x hR
    simp only [own, hR, tcbOwner, tw t ht oAFFINITY (Or.inl rfl), tw t ht oSTATE (Or.inr (Or.inl rfl)),
      tw t ht oBLOCK_OBJ (Or.inr (Or.inr (Or.inl rfl))),
      tw t ht oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      tw t ht oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]

/-- **The entry facts** (`PathObl`'s `Pre`): P1's invariant, the layout [J] and the core-placement facts [J]. -/
structure StEnt (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (target : U64) (s : S) : Prop where
  inv : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  lay : StLay K st T Scs Z s
  pre : StPre st Scs s
  aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  tg : target ∈ T

variable {target : U64} {lk : S → U64 → Prop}

theorem StEnt.dec {s : S} (h : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s) {q : U64} (hq : StDec st s q) :
    Aligned q ∧ own K (L.mem s) q = .core (L.cpu s) ∧
      ((∃ c, region K q = .node c) ∨ (∃ t, region K q = .tcb t ∧ q.val - t.val < 3328)) := by
  have h0 := h.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  have ht' : TcbAddr (L.curW s) := h0.tcbs _ h0.curT
  rcases hq with rfl | rfl | rfl
  · obtain ⟨k, hk, e⟩ := regA_eq (t := L.curW s) ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    have hk' : k.val = 392 := by rw [hk]; simp [layout.reg.FAULT_IP]
    rw [e]
    have eo := caller_own' h.lay h0.tcbs h0.curT h.pre.aff h.pre.nq (k := k) (by omega) (by omega) (by omega)
    rw [if_neg (show ¬ GateField k.val by unfold GateField; omega)] at eo
    refine ⟨field_aligned ht' (by omega) (by omega), eo, Or.inr ⟨L.curW s, ?_, ?_⟩⟩
    · exact h.lay.tcb _ h0.curT k (by omega) (by omega)
    · rw [field_val ht' (by omega)]; omega
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
      h.lay.own_node _ (by simp [layout.node.CUR_TIME]), Or.inl ⟨_, h.lay.nd _ (by simp [layout.node.CUR_TIME])⟩⟩
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      h.lay.own_node _ (by simp [layout.node.CONSUMED]), Or.inl ⟨_, h.lay.nd _ (by simp [layout.node.CONSUMED])⟩⟩

theorem nodeR {s : S} (h : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s) {o : U64} (h1 : o.val < 4288)
    (h2 : o.val % 8 = 0) : MaxR K st lk s (L.nodeAt s (L.cpu s) o) := by
  have h0 := h.inv.1.choose_spec.choose_spec
  exact ⟨Or.inl (held_core (h.lay.own_node _ h1)), nodeAt_aligned (h0.nodes _ h0.cur) h1 h2⟩

variable {A : Type} (ar : machine.Arch A) (n : I64)
variable {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop} {p : SProg Bool}

/-- The family the schema premise is about. -/
abbrev stF (S : Type) (n : I64) (target : U64) {A : Type} (ar : machine.Arch A) (m : machine.Store S) (s : S) (a : A) :
    Result (Bool × S × A) :=
  localtimer.handle_set_timer_local m ar s a n target

/-- Every run at an alternative is one that the guard at the alternative follows: accepted as the entry's, or declined
writing only `StDec`. -/
theorem set_timer_alt (hA : P0.ArchTotal ar)
    (hp : ∀ m : machine.Store S, stF S n target ar m = interp m ar p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    {s s' : S} {a : A} {r' : Bool × S × A}
    (hcls : ∀ v w, cls (tdA target) v = cls (tdA target) w → (v = 0#u64 ↔ w = 0#u64))
    (hko : L.mem s (affA target) = L.cpu s → ko (tdA target) = .core (L.cpu s))
    (hU : ¬ User (tdA target))
    (hE : StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s)
    (hAlt : PathObl.Alt st (MaxR K st lk s) cls ko User s s')
    (h' : localtimer.handle_set_timer_local st ar s' a n target = ok r') :
    (∃ s1 a1, localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1) ∧ r'.1 = true ∧
      localtimer.handle_set_timer_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s' a n target = ok r') ∨
    (∃ s1 a1, localtimer.handle_set_timer_local st ar s a n target = ok (false, s1, a1) ∧ r'.1 = false ∧
      localtimer.handle_set_timer_local (guard st Aligned (StDec st s)) ar s' a n target = ok r') := by
  have hR1 : ∀ w, MaxR K st lk s w → Aligned w := fun _ hw => hw.2
  have hW1 : ∀ w, MaxW K st lk s w → Aligned w := fun _ hw => hw.2
  have hW2 : ∀ w, StDec st s w → Aligned w := fun _ hw => (hE.dec hw).1
  have eP : ∀ (m : machine.Store S) (x : S), localtimer.handle_set_timer_local m ar x a n target = interp m ar p x a :=
    fun m x => congrFun (congrFun (hp m) x) a
  -- transfer of a guarded run
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localtimer.handle_set_timer_local (guard st (MaxR K st lk s) W') ar s a n target = ok (x, s1, a1) →
      r'.1 = x ∧ localtimer.handle_set_timer_local (guard st (MaxR K st lk s) W') ar s' a n target = ok r' := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa p hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks hAlt.read hg
    have hst := (interp_guard p s' a _ hg').1
    rw [← eP, h'] at hst
    have e := Result.ok_injective hst
    subst e
    exact ⟨rfl, by rw [eP]; exact hg'⟩
  obtain ⟨r, hr⟩ : ∃ r, localtimer.handle_set_timer_local st ar s a n target = ok r := by
    have := P0.localtimer.handle_set_timer_local.p0 st ar s a n target LawfulStore.total hA
    obtain ⟨r, e, -⟩ := spec_ex_fd this
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  swap
  · left
    obtain ⟨h1, h2⟩ := tr hW1 (set_timer_acc_own ar hA hE.inv hE.tg hE.lay hE.aff hr)
    exact ⟨s1, a1, hr, h1, h2⟩
  right
  by_cases hfar : L.mem s (affA target) ≠ L.cpu s ∨ L.mem s (tdA target) = 0#u64 ∨
      (L.mem s (thA target)).val >>> 8 = (L.cpu s).val
  · obtain ⟨h1, h2⟩ := tr hW2 (set_timer_dec_guard ar hA (lk := lk) hE.inv hE.tg hE.lay hE.pre hE.aff hfar hr)
    refine ⟨s1, a1, hr, h1, ?_⟩
    rw [eP] at h2 ⊢
    exact interp_mono hR1 (fun _ h => h) p hz s' a r' h2
  · rw [not_or, not_or, not_not] at hfar
    obtain ⟨hat, hd, hh⟩ := hfar
    have h0 := hE.inv.1.choose_spec.choose_spec
    have hT : TcbPlaced T := h0.tcbs
    have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
    obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk hE.inv)).tree _ h0.cur
    have eN : ∀ o, L.nodeAt s' (L.cpu s) o = L.nodeAt s (L.cpu s) o := fun o => nodeAt_of_ksb hAlt.ksb _ o
    have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) := by
      intro y hy k h1 h2 h3
      refine hAlt.read _ ⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3⟩
      have e := hE.lay.own_tcb hT (L.mem s) (ct.inT y hy) (k := k) (by omega) (by omega)
      unfold fld at e
      rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
        if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
        if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from
          fun h => ct.armed y hy (UScalar.eq_of_val_eq h))]
      have e2 := ct.core y hy
      rw [Nat.shiftRight_eq_div_pow] at e2
      exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)
    have ct' : CoreTree st T s' (L.cpu s) W0 := CoreTree.agree ct eN
      (hAlt.read _ (nodeR hE (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])))
      (hAlt.read _ (nodeR hE (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
      (fun y hy => ⟨keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
        keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
        keyR y hy _ (by simp) (by simp) (by simp)⟩)
    have hd' : L.mem s' (tdA target) ≠ 0#u64 := by
      by_cases hin : MaxR K st lk s (tdA target)
      · rw [hAlt.read _ hin]; exact hd
      · have e := hAlt.clsEq _ hin hU (Or.inr (hko hat))
        exact fun h => hd ((hcls _ _ e).1 h)
    have hcur : L.curW s' = L.curW s := by
      unfold LawfulStore.curW
      rw [hAlt.cpu, eN]
      exact hAlt.read _ (nodeR hE (by rw [curth_val]; omega) (by rw [curth_val]))
    have hk : target ∉ W0.keys := fun h => hh (ct.core target h)
    rw [← hAlt.cpu] at ct'
    obtain ⟨h1, h2⟩ := set_timer_far ar hT (by rw [hAlt.cpu]; exact hN.ksb hAlt.ksb) (by rw [hcur]; exact h0.curT) hE.tg
      ct' hk hd' h'
    refine ⟨s1, a1, hr, h1, ?_⟩
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ h => h) (fun _ h => h.elim) p hz s' a r' h2

/-- **`PathObl` for `TCB_SetTimer`** (module docstring), `move` of accepted runs a premise. -/
theorem set_timer_pathObl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    {P : S → Prop} (hPE : ∀ s, P s → StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s)
    (hp : ∀ m : machine.Store S, stF S n target ar m = interp m ar p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hcls : ∀ s, P s → ∀ v w, cls (tdA target) v = cls (tdA target) w → (v = 0#u64 ↔ w = 0#u64))
    (hko : ∀ s, P s → L.mem s (affA target) = L.cpu s → ko (tdA target) = .core (L.cpu s))
    (hU : ∀ s, P s → ¬ User (tdA target))
    (hkoF : ∀ s, P s → ∀ q, StDec st s q → ko q = .free)
    (hkoA : ∀ x, ko x ≠ .free → Aligned x)
    (hmv : ∀ s a s1 a1, P s →
      localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1) →
      localtimer.handle_set_timer_local (mguard st
        (fun x y => StepOK (own K) cls ko User (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s a n target =
          ok (true, s1, a1)) :
    PathObl.PathObl st (fun m s a => localtimer.handle_set_timer_local m ar s a n target) (fun b => b = true)
      (own K) cls ko User lk P (MaxR K st lk) (MaxW K st lk) (StDec st) := by
  have eP : ∀ (m : machine.Store S) (x : S) (a : A),
      localtimer.handle_set_timer_local m ar x a n target = interp m ar p x a :=
    fun m x a => congrFun (congrFun (hp m) x) a
  -- the per-write check of the prefix's words
  have hQ : ∀ s, P s → ∀ (x : S) (q v : U64), StDec st s q →
      StepOK (own K) cls ko User (L.cpu s) (lk s) (L.mem x) (L.mem (L.wr x q v)) := by
    intro s hE x q v hq
    obtain ⟨a1, -, a3⟩ := (hPE s hE).dec hq
    refine ⟨fun w hw => absurd (own_keep hK hUO a1 a3 x v w) hw, fun w hw _ => ?_⟩
    by_cases hwq : w = q
    · subst hwq; exact Or.inr (Or.inr (hkoF s hE w hq))
    · by_cases hf : ko w = .free
      · exact Or.inr (Or.inr hf)
      · exact absurd (mem_wr_ne' a1 (hkoA w hf) (fun e => hwq e.symm)) hw
  have dec : ∀ s a r, P s →
      localtimer.handle_set_timer_local st ar s a n target = ok r → r.1 ≠ true →
      ∀ s' r', PathObl.Alt st (MaxR K st lk s) cls ko User s s' →
      localtimer.handle_set_timer_local st ar s' a n target = ok r' →
      r'.1 ≠ true ∧
      localtimer.handle_set_timer_local (guard st (fun _ => True) (StDec st s)) ar s' a n target = ok r' ∧
      localtimer.handle_set_timer_local (mguard st
        (fun x y => StepOK (own K) cls ko User (L.cpu s) (lk s) (L.mem x) (L.mem y))) ar s' a n target = ok r' := by
    intro s a r hE hr hn s' r' hAlt h'
    rcases set_timer_alt (lk := lk) ar n hA hp hz hm (hcls s hE) (hko s hE) (hU s hE) (hPE s hE) hAlt h' with ⟨s1, a1, e, -, -⟩ | ⟨s1, a1, -, h1, h2⟩
    · rw [hr] at e
      exact absurd (by rw [Result.ok_injective e]) hn
    · rw [eP] at h2
      refine ⟨by rw [h1]; exact Bool.false_ne_true, ?_, ?_⟩
      · rw [eP]; exact interp_mono (fun _ _ => trivial) (fun _ h => h) p hz s' a r' h2
      · rw [eP]; exact interp_to_mguard (fun x q v hq => hQ s hE x q v hq) p hz s' a r' h2
  refine ⟨?_, dec, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    replace hE := hPE s hE
    exact set_timer_acc_own ar hA hE.inv hE.tg hE.lay hE.aff h
  · intro s x _ hx _; exact hx.1
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.1
    · exact held_core ((hPE s hE).dec hx).2.1
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.2
    · exact ((hPE s hE).dec hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (dec s a _ hE h Bool.false_ne_true s _ (PathObl.Alt.refl s) h).2.2
    · exact hmv s a s1 a1 hE h

/-- **`PathSide` for `TCB_SetTimer`** (module docstring). -/
theorem set_timer_pathSide (hA : P0.ArchTotal ar)
    {P : S → Prop} (hPE : ∀ s, P s → StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s)
    (hp : ∀ m : machine.Store S, stF S n target ar m = interp m ar p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hcls : ∀ s, P s → ∀ v w, cls (tdA target) v = cls (tdA target) w → (v = 0#u64 ↔ w = 0#u64))
    (hko : ∀ s, P s → L.mem s (affA target) = L.cpu s → ko (tdA target) = .core (L.cpu s))
    (hU : ∀ s, P s → ¬ User (tdA target)) (hkoA : ∀ x, ko x ≠ .free → Aligned x)
    (huf : ∀ s b v, P s → User b → Aligned b →
      P (L.wr s b v) ∧ lk (L.wr s b v) = lk s ∧
        MaxR K st lk (L.wr s b v) = MaxR K st lk s ∧ MaxW K st lk (L.wr s b v) = MaxW K st lk s ∧
        StDec st (L.wr s b v) = StDec st s) :
    PathObl.PathSide st (fun m s a => localtimer.handle_set_timer_local m ar s a n target) cls ko User lk
      P (MaxR K st lk) (MaxW K st lk) (StDec st) := by
  refine ⟨?_, fun s x _ hx => hx.2, hkoA, huf⟩
  intro s s' a r hE hAlt h
  have eP : ∀ (m : machine.Store S) (x : S), localtimer.handle_set_timer_local m ar x a n target = interp m ar p x a :=
    fun m x => congrFun (congrFun (hp m) x) a
  rcases set_timer_alt (lk := lk) ar n hA hp hz hm (hcls s hE) (hko s hE) (hU s hE) (hPE s hE) hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
  · show localtimer.handle_set_timer_local _ ar s' a n target = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw.2) (fun _ _ => trivial) p hz s' a r h2
  · show localtimer.handle_set_timer_local _ ar s' a n target = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2

end

end Fl4Proofs.P2
