/-
# P2 (line p3mc, gen 19): st at a view start whose target is homed: the narrowed runs

At an st entry `s` at core `c`'s view of `ρ` (a bundle state `SlJAt`, the st entry facts `StEnt` at `userV K`, `QPs`, the
aligned kernel words the view's, core `c`) whose target is homed on `c` in `ρ`:

* **`stVC_ent`**: sl's view context `SlVC` (P2/SlVPin) holds at `s`, with no fact about the current thread's state
  (P2/StVPin's `stVC_of` asked for a running one): the current thread is homed (`st_cur_home`), the current SC, the
  release head and its SC, and every SC with a nonzero `TCB` word are homed (`st_sc_home`, `st_csc_home`,
  `st_rh_home`: P1's back-pointers at `s` with `view_sctcb_home` / `view_tzero_home`, as `vm_homes` without
  `VmBase`);
* **`stRd_sr`**: every word of the accepted run's read set `StRd` is `SR` (kept by the view, value and owner, no PTE
  word): node words, the caller's words, the target's `AFFINITY`, `CUR_DOMAIN` / `DOMAIN_TIME`, the current SC, the
  release head's SC word and SC; a key's timer words if the key is homed (`sr_tcb`), or, if it is another core's
  thread, since it is armed in `c`'s tree (`sr_timer`);
* **`st_acc_v`**: an accepted run is the same run on `guard st (StNR s) StNW`, with `StNR s := VN ∧ (MaxR ∖ PTE ∨
  VKc)` and `StNW := VN ∧ VKc ∧ (¬ VDec ∨ another core's thread's TIMER_HEIGHT)` (`GED.set_timer_accGD`; the
  reads by `st_rd_own` / `st_rd_nu` / `stRd_sr`, the writes by `st_wr_nondec`, `vnw_tcb`, `vkc_timer`, `srw_sc`,
  `vn_timer`);
* **`st_dec_v`**: a declined run whose target is disarmed or armed in `c`'s tree is the same run on
  `guard st (MaxR ∖ PTE ∩ SR) StDec` (`set_timer_dec_guardS` + `stRd_sr`);
* **`st_walk_v`**: where the target is armed in another core's tree, the run at any alternative `s'` of `s` (agreeing
  on `MaxR ∖ PTE`, class-equal on the other non-user words `s`'s core or the gate owns) declines writing nothing, on
  every store answering `StNR s` (`st_tok_run`): its reads up to the target check agree, the target's deadline stays
  nonzero (class equality), and `c`'s tree agrees and holds no target (`in_core_found`), as `StOnce.st_hro`'s walk.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.StVPin
import Fl4Proofs.P2.StDecG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oTIMER_HEIGHT InW DecW ko GateField
  TimerField tcbOwner tOwner)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec TZero)
open Fl4Proofs.P2.Serial (Owner)

noncomputable section
open Classical

section ctx
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]

/-- st's entry facts at the layout `userV K`, the sets of the heap. -/
abbrev StEV (st : machine.Store S) [L : LawfulStore st] (K : KLayoutP) (Cs Ω Sg Ac : Set U64) (target : U64)
    (s : S) : Prop :=
  StEnt (userV K.toKLayoutV) st K.toKLayoutV.heap.tcbs Cs Ω K.toKLayoutV.heap Sg K.toKLayoutV.heap.replies
    K.toKLayoutV.heap.scs K.toKLayoutV.heap.ntfns K.toKLayoutV.heap.scBits Ac target s

theorem st_scH {K : KLayoutP} {p : U64} (hp : p ∈ K.toKLayoutV.heap.scs) :
    K.toKLayout.heap p = some (.sc (K.toKLayoutV.heap.scBits p)) := by
  obtain ⟨z, hz⟩ := hp
  rw [Heap.scBits_eq hz]; exact hz

variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Cs Ω Sg Ac : Set U64} {target : U64} {s : S}

/-- An SC whose `TCB` word is nonzero at an st entry of the view is homed on `c`. -/
theorem st_sc_home (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    {p : U64} (hp : p ∈ K.toKLayoutV.heap.scs) (h0 : L.mem s (scTcbA p) ≠ 0#u64) : ρ (fld p 16#u64) = c := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := E.inv
  obtain ⟨hP, hz⟩ := hO.sc _ hp
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hv : (scTcbA p).val = p.val + 24 := by
    unfold scTcbA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hr : region K.toKLayout (scTcbA p) = .sc p :=
    hJ.regionOKX.scW p _ (st_scH hp) _ ⟨by omega, by omega⟩
  have ha : Aligned (scTcbA p) := by unfold Aligned; rw [hv]; omega
  have hk : scTcbA p ∉ K.user := fun hu =>
    E.lay.nu_sc hp ⟨by omega, by omega⟩ (mem_userV.2 (Or.inl hu))
  exact CoreView.view_sctcb_home (K := K.toKLayout) hr (by omega) (by rw [← hm _ ha hk]; exact h0)

/-- The current SC at an st entry of the view is homed on `c`. -/
theorem st_csc_home (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) :
    ρ (fld (L.cscW s) 16#u64) = c := by
  have h0 := E.inv.1.choose_spec.choose_spec
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := E.inv
  have hne := st_scn hJ E
  obtain ⟨hcs, htcb, -⟩ := hX.bound _ h0.curT hne
  rw [← E.pre.sct]
  exact st_sc_home hJ E hm hcs (fun e => by
    have e2 : L.curW s = 0#u64 := htcb.symm.trans e
    exact (h0.tcbs _ h0.curT).ne0 (by
      have e3 : (L.curW s).val = 0 := by rw [e2]; rfl
      exact e3))

/-- The release head at an st entry of the view, and its SC, are homed on `c`. -/
theorem st_rh_home (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    ρ (fld (L.mem s (rhA (L := L) s)) oAFFINITY) = c ∧
      ρ (fld (L.mem s (scA (L.mem s (rhA (L := L) s)))) 16#u64) = c := by
  have hX0 := hJ.regionOKX
  have hBX := E.inv
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := E.inv
  obtain ⟨hT, -, -⟩ := bxi_rh hBX h0
  have hne : L.mem s (scA (L.mem s (rhA (L := L) s))) ≠ 0#u64 := by
    intro e0
    have hfl := hb.r _ hT
    have hrel := hq.release _ hq.cur
    have hd : L.mem s (rhA (L := L) s) = (Rq (L.cpu s)).headD 0#u64 := hrel.head
    have hmR : L.mem s (rhA (L := L) s) ∈ Rq (L.cpu s) := by
      cases hl : Rq (L.cpu s) with
      | nil => rw [hl] at hd; exact absurd hd h0
      | cons r rs => rw [hl] at hd; rw [hd]; simp
    exact hfl ((hq.released _ hT).2 (by rw [hq.inR _ hq.cur _ hmR]; exact hmR)) e0
  obtain ⟨hcs, htcb, -⟩ := hX.bound _ hT hne
  refine ⟨?_, st_sc_home hJ E hm hcs (by rw [htcb]; exact h0)⟩
  have htH : K.toKLayout.heap (L.mem s (rhA (L := L) s)) = some .tcb := hT
  obtain ⟨hr, hv, ha⟩ := hX0.tcbW _ htH 3464#u64 (by simp) (by simp) (by simp)
  have hu : scA (L.mem s (rhA (L := L) s)) ∉ K.user := fun hu =>
    E.lay.nu_tcb hT (k := 3464#u64) (by simp) (by simp) (mem_userV.2 (Or.inl hu))
  refine CoreView.view_tzero_home hr (by rw [hv]; simp [TZero]) ?_
  rw [← hm _ ha hu]; exact hne

/-- **sl's view context at an st entry** (module docstring), with no fact about the current thread's state. -/
theorem stVC_ent (hK : RegionOKP K) (hU : UserOKP K) (hJ : SlJAt (L := L) K.toKLayout s)
    (E : StEV st K Cs Ω Sg Ac target s) (hq : QPs K st s) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) :
    SlVC (L := L) K c ρ s :=
  { hK := hK
    cpu := hc
    hm := hm
    cur := st_cur_home hJ E hm
    csc := st_csc_home hJ E hm
    rh := st_rh_home hJ E hm
    scb := fun p hp h0 => st_sc_home hJ E hm hp h0
    ks := hq.ks
    ksb := hq.ksb
    tab := hq.tab
    upte := userNoE_pte hU
    scn := st_scn hJ E }

/-- A thread armed at the view start is armed in `ρ`. -/
theorem st_armρ (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    {y : U64} (hy : K.toKLayout.heap y = some .tcb) (hd : L.mem s (tdA y) ≠ 0#u64) :
    ρ (fld y oTIMER_DEADLINE) ≠ 0#u64 := by
  obtain ⟨hr0, hv0, hal⟩ := hJ.regionOKX.tcbW y hy 3528#u64 (by simp) (by simp) (by simp)
  have hr : region K.toKLayout (tdA y) = .tcb y := hr0
  have hv : (tdA y).val - y.val = (3528#u64).val := hv0
  have hu : tdA y ∉ K.user := fun hu =>
    E.lay.nu_tcb (show y ∈ K.toKLayoutV.heap.tcbs from hy) (k := 3528#u64) (by simp) (by simp)
      (mem_userV.2 (Or.inl hu))
  have e1 := V.hm (tdA y) hal hu
  have e2 : view K.toKLayout c ρ (tdA y) = ρ (tdA y) :=
    CoreView.view_timer_keep hr (by rw [hv]; simp) (by rw [hv]; simp)
  intro e
  exact hd (by rw [e1, e2]; exact e)

/-- **The accepted run's read words are `SR`** (module docstring). -/
theorem stRd_sr (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (htH : ρ (fld target oAFFINITY) = c) {w : U64}
    (hw : StRd st K.toKLayoutV.heap.tcbs K.toKLayoutV.heap.scBits s target w) : SR K c ρ w := by
  have hX := hJ.regionOKX
  have hK := V.hK
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.toKLayoutV.heap.tcbs s (L.cpu s) := h0.nodes _ h0.cur
  have hcH : K.toKLayout.heap (L.curW s) = some .tcb := h0.curT
  have htgH : K.toKLayout.heap target = some .tcb := E.tg
  unfold StRd TW at hw
  rcases hw with ((⟨z, ⟨hz, hy⟩, k, h1, h2, h3, rfl⟩ | ⟨o, ho, h8, rfl⟩) | ⟨k, h1, h2, h3, h4, rfl⟩ | rfl | rfl | rfl |
    hb | ⟨hne, rfl | hb⟩)
  · have hzH : K.toKLayout.heap z = some .tcb := hz
    by_cases ha : ρ (fld z oAFFINITY) = c
    · exact sr_tcb hK hX hzH ha (by omega) (by omega) h3
    · rcases hy with rfl | hy
      · exact absurd htH ha
      · exact sr_timer hK hX hzH (o := k) (by omega) (by omega) h3 (st_armρ V hJ E hzH hy.1)
  · exact (srw_node V hJ hN ho h8).1
  · exact sr_tcb hK hX hcH V.cur (by omega) h2 h3
  · exact sr_tcb hK hX htgH htH (o := 3520#u64) (by simp) (by simp) (by simp)
  · exact sr_ks V hJ hN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · exact sr_ks V hJ hN (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · exact (srw_sc hK hX (st_scH E.pre.csc) V.csc hb).1
  · obtain ⟨hT, -, -⟩ := bxi_rh E.inv hne
    exact sr_tcb hK hX (show K.toKLayout.heap _ = some .tcb from hT) (V.rh hne).1 (o := 3464#u64)
      (by simp) (by simp) (by simp)
  · obtain ⟨-, hcs, -⟩ := bxi_rh E.inv hne
    exact (srw_sc hK hX (st_scH hcs) (V.rh hne).2 hb).1

end ctx

/-! ## The narrowed runs -/

section runs
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Cs Ω Sg Ac : Set U64} {target : U64} {s : S}

/-- **st's narrowed write set** (module docstring). -/
def StNW (K : KLayoutP) (c : U64) (ρ : U64 → U64) (q : U64) : Prop :=
  VN K c ρ q ∧ VKc K.toKLayout c ρ q ∧ (¬ VDec K.toKLayout c ρ q ∨
    ∃ t, K.toKLayout.heap t = some .tcb ∧ ρ (fld t oAFFINITY) ≠ c ∧ q = fld t oTIMER_HEIGHT)

/-- **st's narrowed read set at `s0`** (module docstring). -/
def StNR (st : machine.Store S) [L : LawfulStore st] (K : KLayoutP) (c : U64) (ρ : U64 → U64)
    (lk : S → U64 → Prop) (s0 : S) (b : U64) : Prop :=
  VN K c ρ b ∧ (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) s0 b ∨ VKc K.toKLayout c ρ b)

theorem stNW_of_vnw {q : U64} (h : VNW K c ρ q) : StNW K c ρ q := ⟨h.1, h.2.1, Or.inl h.2.2⟩

set_option maxHeartbeats 8000000 in
/-- **The accepted run on st's narrowed store** (module docstring). -/
theorem st_acc_v (hA : P0.ArchTotal ar) {lk : S → U64 → Prop} {n : I64} {s1 : S} {a a1 : A}
    (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (htH : ρ (fld target oAFFINITY) = c)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (true, s1, a1)) :
    localtimer.handle_set_timer_local (guard st (StNR st K c ρ lk s) (StNW K c ρ)) ar s a n target =
      ok (true, s1, a1) := by
  have hX := hJ.regionOKX
  have hK := V.hK
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.toKLayoutV.heap.tcbs s (L.cpu s) := h0.nodes _ h0.cur
  have hcH : K.toKLayout.heap (L.curW s) = some .tcb := h0.curT
  have htgH : K.toKLayout.heap target = some .tcb := E.tg
  have hKu : OwnMap.RegionOK (userV K.toKLayoutV) := regionOK_userV hK.base
  have hcq := scq_of E.inv.2.2.1.1 E.inv.2.2.2.2 E.pre.csc
  have gRd : StOk st K.toKLayoutV.heap.scs s target → ∀ w, Aligned w →
      StRd st K.toKLayoutV.heap.tcbs K.toKLayoutV.heap.scBits s target w → StNR st K c ρ lk s w :=
    fun ho w ha hw =>
      ⟨(stRd_sr V hJ E htH hw).1, Or.inl ⟨⟨st_rd_own E.inv E.lay E.aff E.tg ho hw, ha, st_rd_nu E.inv E.lay E.tg ho hw⟩,
        (stRd_sr V hJ E htH hw).2⟩⟩
  refine GED.set_timer_accGD (gS := guard st (StNR st K c ρ lk s) (StNW K c ρ)) (R := StNR st K c ρ lk s)
    (W := StNW K c ρ) ar hA E.inv E.tg gRd ?_
    (fun ho => gRd ho _ E.lay.domA (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    (fun ho => gRd ho _ E.lay.dtmA (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
    (fun _ X v _ _ _ => guard_write (by
      rw [stA_eq]
      exact stNW_of_vnw (vnw_tcb hK hX hcH V.cur (o := 3328#u64) (by simp) (by simp) (by simp) (by simp))))
    (fun _ X y v hy _ => guard_write (by
      have hyH : K.toKLayout.heap y = some .tcb := hy.1
      by_cases ha : ρ (fld y oAFFINITY) = c
      · exact stNW_of_vnw (vnw_tcb hK hX hyH ha (o := 3568#u64) (by simp) (by simp) (by simp) (by simp))
      · rcases hy.2 with rfl | hy2
        · exact absurd htH ha
        · obtain ⟨hr0, hv0, -⟩ := hX.tcbW y hyH 3568#u64 (by simp) (by simp) (by simp)
          have hr : region K.toKLayout (thA y) = .tcb y := hr0
          have hv : (thA y).val - y.val = (3568#u64).val := hv0
          exact ⟨CoreView.vn_timer hK hX hyH (o := 3568#u64) (by simp) (by simp) (by simp) (st_armρ V hJ E hyH hy2.1),
            vkc_timer hr (by rw [hv]; simp) (by rw [hv]; simp), Or.inr ⟨y, hyH, ha, rfl⟩⟩))
    (fun _ X v _ _ _ => guard_write
      (stNW_of_vnw (vnw_tcb hK hX htgH htH (o := 3528#u64) (by simp) (by simp) (by simp) (by simp)))) h
  intro ho w ha hw hn
  have nd : ¬ VDec K.toKLayout c ρ w := fun hv => st_wr_nondec hKu E.inv E.lay ho hw hn (vdec_decW hv)
  unfold StWr TW at hw
  rcases hw with ((⟨z, hz, k, h1, h2, h3, rfl⟩ | ⟨o, ho', h8, rfl⟩) | ⟨k, h1, h2, h3, rfl⟩ | hb | rfl)
  · have hzH : K.toKLayout.heap z = some .tcb := hz.1
    obtain ⟨hr, hv, -⟩ := hX.tcbW z hzH k (by omega) (by omega) h3
    refine ⟨(stRd_sr V hJ E htH (Or.inl (Or.inl ⟨z, hz, k, h1, h2, h3, rfl⟩))).1,
      vkc_timer hr (by rw [hv]; omega) (by
        rw [hv]; intro e
        have ek : k = 3528#u64 := UScalar.eq_of_val_eq (by rw [e]; rfl)
        exact hn (Or.inr ⟨z, hz, Or.inl (by rw [ek]; rfl)⟩)), Or.inl nd⟩
  · exact stNW_of_vnw (srw_node V hJ hN ho' h8).2
  · exact stNW_of_vnw (vnw_tcb hK hX hcH V.cur (o := k) (by omega) (by omega) h3 (by omega))
  · exact stNW_of_vnw (srw_sc hK hX (st_scH E.pre.csc) V.csc hb.inSC).2
  · exact stNW_of_vnw (srw_sc hK hX (st_scH E.pre.csc) V.csc hcq.2.2.1.1).2

/-- **A declined run whose target is disarmed or armed in `c`'s tree, on st's narrowed store** (module docstring). -/
theorem st_dec_v (hA : P0.ArchTotal ar) {lk : S → U64 → Prop} {n : I64} {s1 : S} {a a1 : A}
    (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (htH : ρ (fld target oAFFINITY) = c)
    (hto : L.mem s (tdA target) = 0#u64 ∨ (L.mem s (thA target)).val >>> 8 = (L.cpu s).val)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok (false, s1, a1)) :
    localtimer.handle_set_timer_local
      (guard st (fun w => rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) s w ∧ SR K c ρ w) (StDec st s))
      ar s a n target = ok (false, s1, a1) := by
  have g := set_timer_dec_guardS ar hA (lk := lk) E.inv E.tg E.lay E.pre E.aff (Or.inr hto) h
  have hp : ∀ mm : machine.Store S,
      localtimer.handle_set_timer_local mm ar s a n target =
        interp mm ar (R.localtimer.handle_set_timer_local n target) s a :=
    fun mm => congrFun (congrFun (st_isProg S n target A ar mm) s) a
  rw [hp] at g ⊢
  exact interp_mono (fun q hq => ⟨⟨hq.1, (stRd_sr V hJ E htH hq.2).2⟩, stRd_sr V hJ E htH hq.2⟩) (fun q hq => hq)
    _ (st_noZero n target) s a _ g

set_option maxHeartbeats 8000000 in
/-- **A run at an alternative of a start whose target is armed in another core's tree declines** (module
docstring), on every store answering st's narrowed read set. -/
theorem st_walk_v {lk : S → U64 → Prop} {n : I64} {s' : S} {a : A} {r : Bool × S × A}
    (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) (E : StEV st K Cs Ω Sg Ac target s)
    (htH : ρ (fld target oAFFINITY) = c) (hat : L.mem s (affA target) = L.cpu s)
    (hd : L.mem s (tdA target) ≠ 0#u64) (hh : ¬ (L.mem s (thA target)).val >>> 8 = (L.cpu s).val)
    (Al : Alt st (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) s) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user) s s')
    {gS : machine.Store S} [GRd gS st (StNR st K c ρ lk s)]
    (h : localtimer.handle_set_timer_local st ar s' a n target = ok r) :
    localtimer.handle_set_timer_local gS ar s' a n target = ok r ∧ r.1 = false := by
  have hX := hJ.regionOKX
  have hK := V.hK
  have h0 := E.inv.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayoutV.heap.tcbs := h0.tcbs
  have hN : NodePlaced st K.toKLayoutV.heap.tcbs s (L.cpu s) := h0.nodes _ h0.cur
  have hcT : L.curW s ∈ K.toKLayoutV.heap.tcbs := h0.curT
  have hcH : K.toKLayout.heap (L.curW s) = some .tcb := hcT
  have ht' := hT _ hcT
  have htgH : K.toKLayout.heap target = some .tcb := E.tg
  have hL := E.lay
  set RS : U64 → Prop := rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) s with eRS
  have mk : ∀ {w : U64}, MaxR (userV K.toKLayoutV) st lk s w → SR K c ρ w → RS w ∧ StNR st K c ρ lk s w :=
    fun h1 h2 => ⟨⟨h1, h2.2⟩, h2.1, Or.inl ⟨h1, h2.2⟩⟩
  have nR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → RS (L.nodeAt s (L.cpu s) o) ∧
      StNR st K c ρ lk s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    mk ⟨Or.inl (held_core (hL.own_node _ h1)), nodeAt_aligned hN h1 h2, hL.nu_node h1⟩ (srw_node V hJ hN h1 h2).1
  have cR : ∀ k : U64, 256 ≤ k.val → k.val < 4096 → k.val % 8 = 0 → (k.val < 3528 ∨ 3576 ≤ k.val) →
      RS (core.num.U64.wrapping_add (L.curW s) k) ∧ StNR st K c ρ lk s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 h4 => by
    have e := caller_own' hL hT hcT E.pre.aff E.pre.nq h1 h2 h4
    refine mk ⟨?_, field_aligned ht' h2 h3, hL.nu_tcb hcT h1 h2⟩ (sr_tcb hK hX hcH V.cur (by omega) h2 h3)
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have rR : ∀ r : U64, r.val < 384 → RS (regA (L.curW s) r) ∧ StNR st K c ρ lk s (regA (L.curW s) r) :=
    fun r hr => by
    obtain ⟨k, hk, e⟩ := regA_eq ht' hr
    rw [e]; exact cR k (by omega) (by omega) (by omega) (by omega)
  have rAt : RS (affA target) ∧ StNR st K c ρ lk s (affA target) := mk ⟨Or.inr (by
      have e := hL.own_tcb hT (L.mem s) E.tg (k := 3520#u64) (by simp) (by simp)
      unfold fld at e
      unfold GateOnly affA; rw [e, tcbOwner, if_pos (show GateField (3520#u64).val from Or.inl (by simp))]),
    field_aligned (hT _ E.tg) (by simp) (by simp), hL.nu_tcb E.tg (by simp) (by simp)⟩
    (sr_tcb hK hX htgH htH (o := 3520#u64) (by simp) (by simp) (by simp))
  obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk E.inv)).tree _ h0.cur
  have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
      RS (core.num.U64.wrapping_add y k) ∧ StNR st K c ρ lk s (core.num.U64.wrapping_add y k) := by
    intro y hy k h1 h2 h3
    refine mk ⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3,
      hL.nu_tcb (ct.inT y hy) (by omega) (by omega)⟩
      (stRd_sr V hJ E htH (Or.inl (Or.inl ⟨y, ⟨ct.inT y hy, Or.inr ⟨ct.armed y hy, ct.core y hy⟩⟩, k, h1, h2, h3,
        rfl⟩)))
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
  have ct' : CoreTree st K.toKLayoutV.heap.tcbs s' (L.cpu s) W0 := CoreTree.agree ct eN
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
  have eN' : ∀ o, L.nodeAt s' (L.cpu s') o = L.nodeAt s (L.cpu s) o := fun o => by rw [Al.cpu, eN]
  -- the target's words at `s'`
  obtain ⟨hrD0, hvD0, haD⟩ := hX.tcbW target htgH 3528#u64 (by simp) (by simp) (by simp)
  have hrD : region K.toKLayout (tdA target) = .tcb target := hrD0
  have hvD : (tdA target).val - target.val = (3528#u64).val := hvD0
  have huD : tdA target ∉ K.user := fun hu =>
    hL.nu_tcb E.tg (k := 3528#u64) (by simp) (by simp) (mem_userV.2 (Or.inl hu))
  have hat' : L.mem s' (affA target) = L.cpu s' := by rw [Al.read _ rAt.1, Al.cpu]; exact hat
  have hd' : L.mem s' (tdA target) ≠ 0#u64 := by
    by_cases hin : RS (tdA target)
    · rw [Al.read _ hin]; exact hd
    · have hko : OwnMap.ko K.toKLayout (view K.toKLayout c ρ) (tdA target) = .core (L.cpu s) := by
        have aA : Aligned (affA target) := field_aligned (hT _ E.tg) (by simp) (by simp)
        have uA : affA target ∉ K.user := fun hu =>
          hL.nu_tcb E.tg (k := 3520#u64) (by simp) (by simp) (mem_userV.2 (Or.inl hu))
        have e := V.hm (affA target) aA uA
        simp only [OwnMap.ko, hrD]
        rw [if_pos (Or.inr (by rw [hvD]; simp))]
        show Fl4Proofs.P2.Serial.ClsOwner.core (view K.toKLayout c ρ (affA target)) = _
        rw [← e, hat]
      have e := Al.clsEq _ hin huD (Or.inr hko)
      have e' : L.mem s' (tdA target) = L.mem s (tdA target) := by simpa only [OwnMap.cls, hrD] using e
      rw [e']; exact hd
  have hNRD : StNR st K c ρ lk s (tdA target) :=
    ⟨CoreView.vn_timer hK hX htgH (o := 3528#u64) (by simp) (by simp) (by simp) (st_armρ V hJ E htgH hd),
      Or.inr (CoreView.vkc_of hK.base.base (fun t hr => by rw [hrD] at hr; cases hr; exact htH))⟩
  have hNRH : StNR st K c ρ lk s (thA target) :=
    ⟨CoreView.vn_timer hK hX htgH (o := 3568#u64) (by simp) (by simp) (by simp) (st_armρ V hJ E htgH hd),
      Or.inr (CoreView.vkc_of hK.base.base (fun t hr => by
        have hrH : region K.toKLayout (thA target) = .tcb target :=
          (hX.tcbW target htgH 3568#u64 (by simp) (by simp) (by simp)).1
        rw [hrH] at hr; cases hr; exact htH))⟩
  have tR : ∀ w, TreeReads st s' (L.cpu s) W0.keys w → StNR st K c ρ lk s w := by
    intro w hw
    rcases hw with rfl | rfl | ⟨y, hy, rfl | rfl | rfl⟩
    · rw [eN]; exact (nR _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])).2
    · rw [eN]; exact (nR _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).2
    · exact (keyR y hy _ (by simp) (by simp) (by simp)).2
    · exact (keyR y hy _ (by simp) (by simp) (by simp)).2
    · exact (keyR y hy _ (by simp) (by simp) (by simp)).2
  -- the target check at `s'`
  have ht : localtimer.set_timer_target_ok st s' (L.cpu s') target = ok false := by
    unfold localtimer.set_timer_target_ok
    rw [aff_ok, hat']
    simp only [bind_ok, bind_tc_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [td_ok]
    simp only [bind_ok, bind_tc_ok]
    rw [if_neg hd']
    obtain ⟨b, eb, -⟩ := spec_ex_fd (P0.localtimer.in_core_timer_tree.p0 st s' (L.cpu s') target
      (L.mem s' (tdA target)) LawfulStore.total)
    rw [eb]
    simp only [bind_ok, bind_tc_ok]
    cases b
    · rfl
    · rw [Al.cpu] at eb; exact absurd (in_core_found ct' eb) hk
  have ht' : localtimer.set_timer_target_ok gS s' (L.cpu s') target = ok false := by
    rw [Al.cpu] at ht ⊢
    exact set_timer_target_ok.guard (gS := gS) ct' tR rAt.2 hNRD hNRH ht
  exact st_tok_run ar (by rw [eN']; exact (nR _ (by rw [curth_val]; omega) (by rw [curth_val])).2)
    (by rw [hcur]; exact (rR _ (by simp [layout.reg.MSG_INFO])).2)
    (by rw [hcur]; exact (cR _ (by simp) (by simp) (by simp) (by simp)).2)
    (by rw [eN']; exact (nR _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).2) ht ht' h

end runs

end
end Fl4Proofs.P2.E2EP
