/-
# P2: `PathObl.move` for `TCB_SetTimer` (the re-extracted write order)

With `timer::remove` writing `TIMER_DEADLINE` before `TIMER_HEIGHT` and `timer::insert` `TIMER_HEIGHT` before
`TIMER_DEADLINE` (par/rr, aca1aef4), every write of an accepted `localtimer.handle_set_timer_local` run passes
`PathObl.StepOK` for `OwnMap.own K` / `cls K` / `ko K m`:

* the words of `StWr` outside `StDecW` decide nothing (`st_wr_nondec`, then `OwnMap.stepOK_nondec`);
* the caller's `STATE` (`RESTART`, then `RUNNING`; neither queued), the caller homed here (`stepOK_state`);
* a key's `TIMER_HEIGHT` / `TIMER_DEADLINE` (`stepOK_height`, `stepOK_deadline`): the timer group's owner stays
  `core c` (`own_upd_timer`), under the per-write conditions `set_timer_accG` hands over; a deadline's class owner is
  the target's home core, this one.

`set_timer_move` runs the accepted path on the checked store `PathObl.gd st ⊤ (StWrOK …)` (`set_timer_accG`) and
moves it to `mguard` (`PathObl.interp_gd`, through `IsProg`). `set_timer_localPathM` is `set_timer_localPath`
without its `hmv` premise.

Premises (of `set_timer_localPathM`, all from `set_timer_localPath` except `hmv`, now proved): `hp` [P], `hm` [P],
`hro` [W] (`ReadOnce`), `hEU` / `hNU` [J], `hlk` [P]; the layout's `RegionOK` / `UserOK` are its arguments.
-/
import Fl4Proofs.P2.FootTimerSetLP
import Fl4Proofs.P2.MoveOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section
variable {K : KLayout}

theorem decOff_dh {off : U64} (ho : off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT) : DecOff off := by
  rcases ho with rfl | rfl
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- **Writing a thread's `TIMER_DEADLINE` or `TIMER_HEIGHT` moves no owner** when its timer group's owner
(`tOwner`) stays. -/
theorem own_upd_timer (hK : RegionOK K) {t off v : U64} {m : U64 → U64} (ht : K.heap t = some .tcb)
    (ho : off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT)
    (htO : tOwner (Function.update m (fld t off) v (fld t oTIMER_DEADLINE))
        (Function.update m (fld t off) v (fld t oTIMER_HEIGHT)) (.core (m (fld t oAFFINITY))) =
      tOwner (m (fld t oTIMER_DEADLINE)) (m (fld t oTIMER_HEIGHT)) (.core (m (fld t oAFFINITY)))) :
    own K (Function.update m (fld t off) v) = own K m := by
  have hoD := decOff_dh ho
  have hr0 := (hK.tcb t ht off hoD.reg).1
  have ne_reg : ∀ y, region K y ≠ .tcb t → y ≠ fld t off := fun y hy e => hy (e ▸ hr0)
  have ne_t : ∀ t' off', K.heap t' = some .tcb → DecOff off' → t' ≠ t → fld t' off' ≠ fld t off :=
    fun t' off' ht' ho' hn e => hn (fld_inj hK ht' ht ho' hoD e).1
  have hA : fld t oAFFINITY ≠ fld t off := fld_ne_off hK ht (Or.inl rfl) hoD
    (by rcases ho with rfl | rfl <;> simp only [oAFF_val, oDL_val, oHT_val] <;> omega)
  have hS : fld t oSTATE ≠ fld t off := fld_ne_off hK ht (Or.inr (Or.inl rfl)) hoD
    (by rcases ho with rfl | rfl <;> simp only [oSTATE_val, oDL_val, oHT_val] <;> omega)
  have hB : fld t oBLOCK_OBJ ≠ fld t off := fld_ne_off hK ht (Or.inr (Or.inr (Or.inl rfl))) hoD
    (by rcases ho with rfl | rfl <;> simp only [oBOBJ_val, oDL_val, oHT_val] <;> omega)
  funext x
  cases hr : region K x with
  | node c => simp only [own, hr]
  | obj p => simp only [own, hr]
  | none => simp only [own, hr]
  | slot p =>
    have hp := hK.slot p (hK.slotOf p x hr)
    simp only [own, hr, slotOwner, Function.update_of_ne (ne_reg p (by rw [hp]; intro h; cases h))]
  | sc p =>
    have hp := (hK.scw p x hr).1
    simp only [own, hr, Function.update_of_ne (ne_reg _ (by rw [hp]; intro h; cases h))]
  | ntfn p =>
    have hp := hK.ntfnOf p x hr
    have h24 := (hK.ntfn p hp).1
    simp only [own, hr, ntfnOwner, Function.update_of_ne (ne_reg _ (by rw [h24]; intro h; cases h))]
    by_cases hq : K.heap (m (fld p 24#u64)) = some .tcb
    · by_cases eb : m (fld p 24#u64) = t
      · have hA' : fld (m (fld p 24#u64)) oAFFINITY ≠ fld t off := by rw [eb]; exact hA
        simp only [hq, Function.update_of_ne hA']
      · simp only [hq, Function.update_of_ne (ne_t _ _ hq (Or.inl rfl) eb)]
    · simp only [hq, ↓reduceIte]
  | tcb t' =>
    have ht' := hK.tcbOf t' x hr
    simp only [own, hr]
    by_cases e : t' = t
    · rw [e]
      unfold tcbOwner
      rw [Function.update_of_ne hA, Function.update_of_ne hS, Function.update_of_ne hB, htO]
    · exact tcbOwner_upd_other (fun off' ho' => ne_t t' off' ht' ho' e) _

section st
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A timer-field write passes the check when the timer group's owner stays; a `TIMER_DEADLINE` write needs
the thread homed on core `c` (in the model memory `m0` `ko` reads). -/
theorem stepOK_timer (hK : RegionOK K) (hU : E2E.UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {t off v : U64} (ht : K.heap t = some .tcb) (ho : off = oTIMER_DEADLINE ∨ off = oTIMER_HEIGHT)
    (htO : tOwner (Function.update (L.mem s) (fld t off) v (fld t oTIMER_DEADLINE))
        (Function.update (L.mem s) (fld t off) v (fld t oTIMER_HEIGHT)) (.core (L.mem s (fld t oAFFINITY))) =
      tOwner (L.mem s (fld t oTIMER_DEADLINE)) (L.mem s (fld t oTIMER_HEIGHT)) (.core (L.mem s (fld t oAFFINITY))))
    (hc0 : off = oTIMER_DEADLINE → m0 (fld t oAFFINITY) = c) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s) (L.mem (L.wr s (fld t off) v)) := by
  have hoD := decOff_dh ho
  have ha : Aligned (fld t off) := (hU.tcb t ht off hoD).1
  have e : own K (L.mem (L.wr s (fld t off) v)) = own K (L.mem s) := by
    rw [own_wr hK hU ha, own_upd_timer hK ht ho htO]
  refine ⟨fun x hx => absurd (congrFun e x) hx, fun x hx _ => ?_⟩
  by_cases hf : ko K m0 x = .free
  · exact Or.inr (Or.inr hf)
  have hdx := ko_dec hK hf
  have hxa : x = fld t off := Classical.byContradiction fun hn =>
    hx (by rw [mem_wr_upd ha (decW_ok hU hdx).1, Function.update_of_ne hn])
  subst hxa
  obtain ⟨hr, hv⟩ := hK.tcb t ht off hoD.reg
  rcases ho with rfl | rfl
  · refine Or.inr (Or.inl ?_)
    simp only [ko, hr]
    rw [if_pos (Or.inr (by rw [hv, oDL_val])), hc0 rfl]
  · exfalso; apply hf; simp only [ko, hr]; rw [if_neg (by rw [hv, oHT_val]; omega)]

theorem oHT_ne_oDL : oTIMER_HEIGHT ≠ oTIMER_DEADLINE := fun e => by
  have := congrArg UScalar.val e
  rw [oHT_val, oDL_val] at this
  omega

/-- **A `TIMER_HEIGHT` write passes the check** when, the thread armed, the old and the new height both name
core `c` (`set_red` / `set_black` / `set_height`; with the thread disarmed its height decides nothing). -/
theorem stepOK_height (hK : RegionOK K) (hU : E2E.UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {t v : U64} (ht : K.heap t = some .tcb)
    (hcond : L.mem s (fld t oTIMER_DEADLINE) ≠ 0#u64 →
      (L.mem s (fld t oTIMER_HEIGHT)).val >>> 8 = c.val ∧ v.val >>> 8 = c.val) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s)
      (L.mem (L.wr s (fld t oTIMER_HEIGHT) v)) := by
  have hDH : fld t oTIMER_DEADLINE ≠ fld t oTIMER_HEIGHT :=
    fld_ne_off hK ht (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (by simp only [oDL_val, oHT_val]; omega)
  refine stepOK_timer hK hU ht (Or.inr rfl) ?_ (fun h => absurd h oHT_ne_oDL)
  rw [Function.update_of_ne hDH, Function.update_self]
  unfold tOwner
  by_cases hd : (L.mem s (fld t oTIMER_DEADLINE)).val = 0
  · rw [if_neg (not_not.mpr hd), if_neg (not_not.mpr hd)]
  · rw [if_pos hd, if_pos hd]
    obtain ⟨h1, h2⟩ := hcond (fun e => hd (by rw [e]; rfl))
    rw [Nat.shiftRight_eq_div_pow] at h1 h2
    rw [MoveTimer.treeCore_of h1, MoveTimer.treeCore_of h2]

/-- **A `TIMER_DEADLINE` write passes the check** for a thread homed on core `c` whose height names `c`
whenever the old or the new deadline is set. -/
theorem stepOK_deadline (hK : RegionOK K) (hU : E2E.UserOK K) {m0 : U64 → U64} {c : U64} {lk : U64 → Prop}
    {s : S} {t v : U64} (ht : K.heap t = some .tcb) (ha : L.mem s (fld t oAFFINITY) = c)
    (hc0 : m0 (fld t oAFFINITY) = c)
    (hcond : L.mem s (fld t oTIMER_DEADLINE) ≠ 0#u64 ∨ v ≠ 0#u64 →
      (L.mem s (fld t oTIMER_HEIGHT)).val >>> 8 = c.val) :
    PathObl.StepOK (own K) (cls K) (ko K m0) (· ∈ K.user) c lk (L.mem s)
      (L.mem (L.wr s (fld t oTIMER_DEADLINE) v)) := by
  have hHD : fld t oTIMER_HEIGHT ≠ fld t oTIMER_DEADLINE :=
    fld_ne_off hK ht (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (by simp only [oDL_val, oHT_val]; omega)
  refine stepOK_timer hK hU ht (Or.inl rfl) ?_ (fun _ => hc0)
  rw [Function.update_self, Function.update_of_ne hHD]
  have side : ∀ d : U64, (d ≠ 0#u64 → L.mem s (fld t oTIMER_DEADLINE) ≠ 0#u64 ∨ v ≠ 0#u64) →
      tOwner d (L.mem s (fld t oTIMER_HEIGHT)) (.core (L.mem s (fld t oAFFINITY))) = .core c := by
    intro d hd'
    unfold tOwner
    by_cases hd : d.val = 0
    · rw [if_neg (not_not.mpr hd), ha]
    · rw [if_pos hd]
      have h1 := hcond (hd' (fun e => hd (by rw [e]; rfl)))
      rw [Nat.shiftRight_eq_div_pow] at h1
      rw [MoveTimer.treeCore_of h1]
  rw [side v Or.inr, side _ Or.inl]

end st

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- **The words of `StWr` outside `StDecW` decide nothing** (`OwnMap.DecW`): this core's node words, a key's
links and colour-free tree words, the caller's registers, the current SC's ring and `CONSUMED`. -/
theorem st_wr_nondec (hK : RegionOK K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K st T Scs Z s) {target w : U64} (ho : StOk st Scs s target) (h : StWr st T Z s target w)
    (hn : ¬ StDecW st T s target w) : ¬ DecW K w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hq := scq_of hI.2.2.1.1 hI.2.2.2.2 ho.csc
  apply nondec_of_region hK
  rcases h with h | ⟨k, h1, h2, -, rfl⟩ | h | rfl
  · rcases h with ⟨z, hz, k, h1, h2, -, rfl⟩ | ⟨o, ho', -, rfl⟩
    · have e : (core.num.U64.wrapping_add z k).val - z.val = k.val := by
        rw [field_val (hT z hz.1) (by omega)]; omega
      have k1 : k.val ≠ 3528 := fun e' => hn (Or.inr ⟨z, hz, Or.inl (by
        unfold tdA; rw [show k = 3528#u64 from UScalar.eq_of_val_eq (by simp [e'])])⟩)
      have k2 : k.val ≠ 3568 := fun e' => hn (Or.inr ⟨z, hz, Or.inr (by
        unfold thA; rw [show k = 3568#u64 from UScalar.eq_of_val_eq (by simp [e'])])⟩)
      exact Or.inl ⟨z, hL.tcb z hz.1 k (by omega) (by omega), by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨_, hL.nd o ho'⟩)
  · have e : (core.num.U64.wrapping_add (L.curW s) k).val - (L.curW s).val = k.val := by
      rw [field_val (hT _ h0.curT) (by omega)]; omega
    have k1 : k.val ≠ 3328 := fun e' => hn (Or.inl (by
      rw [stA_eq, show k = 3328#u64 from UScalar.eq_of_val_eq (by simp [e'])]))
    exact Or.inl ⟨_, hL.tcb _ h0.curT k h1 (by omega), by omega, by omega, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hL.sc _ ho.csc w h.inSC, by unfold InRing at h; omega⟩))))
  · obtain ⟨hP, hz⟩ := hI.2.2.1.1.sc _ ho.csc
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hL.sc _ ho.csc _ hq.2.2.1.1, by rw [hv, hcv]; omega⟩))))

/-- The per-write check of `PathObl.move` at state `x` (core `c`, locks `lk`, class owners read in `m`). -/
def StWrOK (st : machine.Store S) [L : LawfulStore st] (K : KLayout) (m : U64 → U64) (c : U64)
    (lk : U64 → Prop) (x : S) (q v : U64) : Prop :=
  PathObl.StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) c lk (L.mem x) (L.mem (L.wr x q v))

variable {target : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) (n : I64) {lk : S → U64 → Prop} {p : SProg Bool}

/-- **`PathObl.move` for an accepted `TCB_SetTimer` local path** (module docstring). -/
theorem set_timer_move (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (stBody S n target) p) {s s1 : S} {a a1 : A}
    (hE : StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m s)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1)) :
    localtimer.handle_set_timer_local (mguard st
      (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
        (L.mem y))) ar s a n target = ok (true, s1, a1) := by
  have hI := hE.ent.inv
  have h0 := hI.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := h0.curT
  have hL := hE.ent.lay
  have heap : ∀ y ∈ T, K.heap y = some .tcb := fun y hy =>
    hK.tcbOf y _ (hL.tcb y hy 3328#u64 (by simp) (by simp))
  have m_aff : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y) := fun y hy =>
    (hE.mem _ (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).1 (hUO.tcb y (heap y hy) oAFFINITY (Or.inl rfl)).2).symm
  have es : stA (L.curW s) = fld (L.curW s) oSTATE := by rw [stA_eq]; rfl
  have nq : ∀ v : U64, (v = sched.TS_RUNNING ∨ v = sched.TS_RESTART) → ¬ QueuedState v := by
    rintro v (rfl | rfl) <;> simp [QueuedState, sched.TS_RUNNING, sched.TS_RESTART]
  have hg : localtimer.handle_set_timer_local (gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) ar s a n
      target = ok (true, s1, a1) :=
    set_timer_accG (gS := gd st (fun _ => True) (StWrOK st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (W := WAll (StWrOK st K m (L.cpu s) (lk s))) ar hA hI hE.ent.tg
      (fun _ _ _ _ => trivial)
      (fun ho w ha hw hn x v => stepOK_nondec hK hUO ha (st_wr_nondec hK hI hL ho hw hn))
      (fun _ => trivial) (fun _ => trivial)
      (fun ho X v hv hX haff => gd_write (by
        show StWrOK st K m (L.cpu s) (lk s) X (stA (L.curW s)) v
        unfold StWrOK
        rw [es]
        exact stepOK_state hK hUO (heap _ hcT) haff (by rw [m_aff _ hcT]; exact ho.aff)
          (fun hq => absurd hq (by rw [← es]; exact nq _ hX))
          (fun hq => absurd hq (nq v hv.symm))))
      (fun ho X y v hy hc => gd_write (stepOK_height hK hUO (heap y hy.1) hc))
      (fun ho X y v hy hX hs hc => gd_write
        (stepOK_deadline hK hUO (heap y hy.1) hX (by rw [m_aff y hy.1]; exact hs) hc))
      h
  have eP : ∀ mm : machine.Store S,
      localtimer.handle_set_timer_local mm ar s a n target = interp mm ar p s a :=
    fun mm => congrFun (congrFun (hp A ar mm) s) a
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOK st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
      (L.mem y)) (I := fun _ => True)
    (fun x q v x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := Result.ok.inj hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

/-- **`TCB_SetTimer` is a local path**, `move` proved (`set_timer_localPath` with `set_timer_move`). -/
noncomputable def set_timer_localPathM (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (stBody S n target) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (StEntK K st T Cs Ω H Sg Rp Scs Nt Z Ac target m) (MaxR K st lk))
    (hEU : ∀ s b v, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → b ∈ K.user → Aligned b →
      StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac target s → ∀ o : U64, o.val < 4288 →
      L.nodeAt s (L.cpu s) o ∉ K.user) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  set_timer_localPath ar n hA hK hUO hp hz hm
    (fun _ _ _ _ hE h => set_timer_move ar n hA hK hUO hp hE h) hro hEU hlk hNU

end

end Fl4Proofs.P2
