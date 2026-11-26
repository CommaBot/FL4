/-
# P2 (line p3mc, gen 4): pinning the I/O port path's objects at a view start state (`io_narA_view`, `io_narD_view`)

At a start state `s` of the I/O port path whose memory is core `c`'s view `view K c ρ` (on aligned kernel words), the
entry facts `IoPre` (P1's invariants, at the view) say where each object the path touches really lives in `ρ`:
* the current thread is homed on `c` (`IoPre.run`: running or restarting at the view, so not hidden,
  `view_hidden_home`);
* where it has an SC, that SC is on `c` (`ScExtra.bound`: the SC's `TCB` word names the thread, nonzero at the view,
  `view_sctcb_home`);
* the release head is homed on `c` (it has an SC, `BoundInv.r`; a nonzero `SC` word at the view, `view_tzero_home`)
  and so is its SC (`view_sctcb_home`);
* the earliest timer's `TIMER_DEADLINE` is kept by the view (offset 3528 is never rewritten), with its owner (the
  timer is armed, `IoPre.tmc`, so the owner is the tree's core, not the thread's home).
Hence `IoNar` (`ViewSafeIoAcc`) with `NN := VN`, `NW := VNW`, and `IoNarD` (`ViewSafeIoDec`) with
`R := VN ∧ (RS ∨ VKc)` for any read set `RS` that holds the timer word.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.ViewSafeOwn
import Fl4Proofs.P2.ViewSafeIoAcc
import Fl4Proofs.P2.ViewSafeIoDec
import Fl4Proofs.P2.E2EPIrq
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP UserOKP ownP_pte ownP_off)
open Fl4Proofs.P2.OwnMapV (ownV_off ownV_on_mem)

noncomputable section
open Classical

/-! ## Not-foreign words by region -/

theorem nf_tcb {K : KLayout} {c : U64} {ρ : U64 → U64} {b t : U64} (hr : region K b = .tcb t)
    (ha : ρ (fld t oAFFINITY) = c) : NotForeign K c ρ b := by
  unfold NotForeign
  refine ⟨fun t' h => ?_, fun p h => ?_, fun d h => ?_, fun p h => ?_⟩ <;> rw [hr] at h <;> cases h
  exact ha

theorem nf_sc {K : KLayout} {c : U64} {ρ : U64 → U64} {b p : U64} (hr : region K b = .sc p)
    (ha : ρ (fld p 16#u64) = c) : NotForeign K c ρ b := by
  unfold NotForeign
  refine ⟨fun t h => ?_, fun p' h => ?_, fun d h => ?_, fun p' h => ?_⟩ <;> rw [hr] at h <;> cases h
  exact ha

theorem nf_node {K : KLayout} {c : U64} {ρ : U64 → U64} {b : U64} (hr : region K b = .node c) :
    NotForeign K c ρ b := by
  unfold NotForeign
  refine ⟨fun t h => ?_, fun p h => ?_, fun d h => ?_, fun p h => ?_⟩ <;> rw [hr] at h <;> cases h
  exact Or.inl rfl

theorem nf_slot {K : KLayout} {c : U64} {ρ : U64 → U64} {b p : U64} (hr : region K b = .slot p) :
    NotForeign K c ρ b := by
  unfold NotForeign
  refine ⟨fun t h => ?_, fun p' h => ?_, fun d h => ?_, fun p' h => ?_⟩ <;> rw [hr] at h <;> cases h

theorem nf_none {K : KLayout} {c : U64} {ρ : U64 → U64} {b : U64} (hr : region K b = .none) :
    NotForeign K c ρ b := by
  unfold NotForeign
  refine ⟨fun t h => ?_, fun p h => ?_, fun d h => ?_, fun p h => ?_⟩ <;> rw [hr] at h <;> cases h

theorem vn_of_nf {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {b : U64}
    (h : NotForeign K.toKLayout c ρ b) : VN K c ρ b :=
  ⟨view_eq_nf h, ownP_view_nf hK h⟩

/-- The class owner is kept on every word but a `STATE`/`TIMER_DEADLINE` word of a thread homed off `c`. -/
theorem vkc_of {K : KLayout} (hK : RegionOK K) {c : U64} {ρ : U64 → U64} {x : U64}
    (h : ∀ t, region K x = .tcb t → ρ (fld t oAFFINITY) = c) : VKc K c ρ x := by
  unfold VKc
  cases hr : region K x with
  | tcb t => simp only [ko, hr, view_tcb_fld hK (hK.tcbOf t x hr) (h t hr) (Or.inl rfl)]
  | sc p => simp only [ko, hr]
  | node d => simp only [ko, hr]
  | slot p => simp only [ko, hr]
  | ntfn p => simp only [ko, hr]
  | obj p => simp only [ko, hr]
  | none => simp only [ko, hr]

/-- A word of `c`'s node decides no `VDD` owner. -/
theorem not_vdec_node {K : KLayout} (hK : RegionOK K) {c : U64} {ρ : U64 → U64} {q d : U64}
    (hr : region K q = .node d) : ¬ VDec K c ρ q := by
  rintro (⟨t, off, ht, -, ho, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨p, b, hb, -, rfl⟩)
  · rw [(hK.tcb t ht off (decOff_list ho)).1] at hr; cases hr
  · rw [(hK.ntfn p hp).1] at hr; cases hr
  · rw [(hK.tcb t ht _ (Or.inl rfl)).1] at hr; cases hr
  · rw [(hK.scw p b hb).1] at hr; cases hr

/-- A word of an SC on `c` decides no `VDD` owner. -/
theorem not_vdec_sc {K : KLayout} (hK : RegionOK K) {c : U64} {ρ : U64 → U64} {q p : U64}
    (hr : region K q = .sc p) (ha : ρ (fld p 16#u64) = c) : ¬ VDec K c ρ q := by
  rintro (⟨t, off, ht, -, ho, rfl⟩ | ⟨p', hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨p', b, hb, ha', rfl⟩)
  · rw [(hK.tcb t ht off (decOff_list ho)).1] at hr; cases hr
  · rw [(hK.ntfn p' hp).1] at hr; cases hr
  · rw [(hK.tcb t ht _ (Or.inl rfl)).1] at hr; cases hr
  · rw [(hK.scw p' b hb).1] at hr; cases hr; exact ha' ha

/-- A word of a thread homed on `c`, not its `AFFINITY`, decides no `VDD` owner. -/
theorem not_vdec_tcb {K : KLayout} (hK : RegionOK K) {c : U64} {ρ : U64 → U64} {q t : U64}
    (hr : region K q = .tcb t) (ha : ρ (fld t oAFFINITY) = c) (ho : q.val - t.val ≠ 3520) : ¬ VDec K c ρ q := by
  rintro (⟨t', off, ht, ha', ho', rfl⟩ | ⟨p, hp, rfl⟩ | ⟨t', ht, rfl⟩ | ⟨p, b, hb, -, rfl⟩)
  · rw [(hK.tcb t' ht off (decOff_list ho')).1] at hr; cases hr; exact ha' ha
  · rw [(hK.ntfn p hp).1] at hr; cases hr
  · obtain ⟨h1, h2⟩ := hK.tcb t' ht _ (Or.inl rfl)
    rw [h1] at hr; cases hr; rw [h2, oAFF_val] at ho; exact ho rfl
  · rw [(hK.scw p b hb).1] at hr; cases hr

/-- The view keeps a TCB word off `AFFINITY`, the zeroed words and `STATE`, whoever's thread it is. -/
theorem view_keep_tcb {K : KLayout} {c : U64} {m : U64 → U64} {b t : U64} (hb : region K b = .tcb t)
    (h1 : b.val - t.val ≠ 3520) (h2 : ¬ TZero (b.val - t.val)) (h3 : b.val - t.val ≠ 3328) :
    view K c m b = m b := by
  by_cases ha : m (fld t oAFFINITY) = c
  · exact view_home hb ha
  · exact view_none (by simp only [repl, repl2, hb, tcbRepl, if_neg ha, if_neg h1, if_neg h2,
      if_neg (fun h : b.val - t.val = 3328 ∧ Hidden (m b) => h3 h.1)])

/-- **An armed timer's `TIMER_DEADLINE` is kept by the view, value and owner, whoever's thread it is.** -/
theorem vn_td {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {t : U64}
    (ht : K.heap t = some .tcb) (h0 : ρ (fld t oTIMER_DEADLINE) ≠ 0#u64) : VN K c ρ (fld t oTIMER_DEADLINE) := by
  have hK0 := hK.base.base
  obtain ⟨hr, ho⟩ := hK0.tcb t ht oTIMER_DEADLINE (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  obtain ⟨hr', ho'⟩ := hK0.tcb t ht oTIMER_HEIGHT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  rw [oDL_val] at ho; rw [oHT_val] at ho'
  have e1 : view K.toKLayout c ρ (fld t oTIMER_DEADLINE) = ρ (fld t oTIMER_DEADLINE) :=
    view_keep_tcb hr (by omega) (by unfold TZero; omega) (by omega)
  have e2 : view K.toKLayout c ρ (fld t oTIMER_HEIGHT) = ρ (fld t oTIMER_HEIGHT) :=
    view_keep_tcb hr' (by omega) (by unfold TZero; omega) (by omega)
  refine ⟨e1, ?_⟩
  have hp : fld t oTIMER_DEADLINE ∉ K.ptes := fun h => by rw [hK.none _ h] at hr; cases hr
  have hv : ¬ ∃ v, Fl4Proofs.P2.OwnMapV.InVcpu K.toKLayoutV v (fld t oTIMER_DEADLINE) := by
    rintro ⟨v, hv⟩; rw [hK.base.none v _ hv] at hr; cases hr
  have hv0 : (ρ (fld t oTIMER_DEADLINE)).val ≠ 0 := fun h => h0 (by
    apply UScalar.eq_of_val_eq; rw [h]; rfl)
  rw [ownP_off hp, ownP_off hp, ownV_off hv, ownV_off hv]
  simp only [own, hr, ho, tcbOwner, GateField, TimerField, tOwner, e1, e2]
  simp only [hv0, ne_eq, not_false_eq_true, if_true]
  norm_num

/-! ## The pins at a view start state -/

section pins
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- An SC whose `TCB` word is a nonzero value at the view is really on `c`. -/
theorem sc_home_of_tcb {K : KLayoutP} {c : U64} {ρ : U64 → U64}
    (P : IoPre st (Fl4Proofs.P2.E2EP.userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    {p : U64} (hp : p ∈ Scs) (h0 : L.mem s (scTcbA p) ≠ 0#u64) : ρ (fld p 16#u64) = c := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  obtain ⟨hP, hz⟩ := hO.sc _ hp
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hv : (scTcbA p).val = p.val + 24 := by
    unfold scTcbA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hr : region (Fl4Proofs.P2.E2EP.userP K) (scTcbA p) = .sc p :=
    P.lay.scw p (Z p) (P.hSc p hp) _ ⟨by omega, by omega⟩
  have ha : Aligned (scTcbA p) := by unfold Aligned; rw [hv]; omega
  have hk : scTcbA p ∉ K.user := fun hu =>
    P.region_kernel (Or.inl (by rw [hr]; simp)) (Or.inl (Or.inl hu))
  exact view_sctcb_home (K := K.toKLayout) hr (by omega) (by rw [← hm _ ha hk]; exact h0)

/-- **Where each object the I/O port path touches lives**, from the entry facts at the view (module docstring). -/
theorem io_homes {K : KLayoutP} {c : U64} {ρ : U64 → U64}
    (P : IoPre st (Fl4Proofs.P2.E2EP.userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hK : RegionOKP K) (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) :
    ρ (fld (L.curW s) oAFFINITY) = c ∧
      (L.mem s (scA (L.curW s)) ≠ 0#u64 → ρ (fld (L.cscW s) 16#u64) = c) ∧
      (L.mem s (rhA (L := L) s) ≠ 0#u64 → ρ (fld (L.mem s (rhA (L := L) s)) oAFFINITY) = c ∧
        ρ (fld (L.mem s (scA (L.mem s (rhA (L := L) s)))) 16#u64) = c) := by
  have hK0 := hK.base.base
  have tw : ∀ t ∈ T, ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
      L.mem s (core.num.U64.wrapping_add t off) = view K.toKLayout c ρ (core.num.U64.wrapping_add t off) :=
    fun t ht off h1 h2 h3 => hm _ (field_aligned (P.tp t ht) h2 h3) (fun hu =>
      P.region_kernel (Or.inl (by have e := P.lay.tcbw t (P.hT t ht) off h1 h2; unfold fld at e; rw [e]; simp))
        (Or.inl (Or.inl hu)))
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  refine ⟨?_, fun hne => ?_, fun h0 => ?_⟩
  · have e : fld (L.curW s) oSTATE = stA (L.curW s) := UScalar.eq_of_val_eq (by
      unfold fld stA
      rw [tcb_wadd_val P.tA (by rw [oSTATE_val]; omega), tcb_wadd_val P.tA (by rw [st_val]; omega), oSTATE_val,
        st_val])
    have hst := tw _ P.cT layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega) (by rw [st_val])
    refine view_hidden_home hK0 (P.hT _ P.cT) ?_
    rw [e]; unfold stA; rw [← hst]
    rcases P.run with h | h <;> rw [show core.num.U64.wrapping_add (L.curW s) layout.tcb.STATE = stA (L.curW s) from rfl,
      h] <;> simp [Hidden, sched.TS_RESTART, sched.TS_RUNNING]
  · obtain ⟨hcs, htcb, -⟩ := hX.bound _ P.cT hne
    rw [P.hcsc hne]
    exact sc_home_of_tcb P hm hcs (by rw [htcb]; intro e; exact P.tA.ne0 (by rw [e]; rfl))
  · obtain ⟨hT, -, -⟩ := bxi_rh P.bxi h0
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
    refine ⟨?_, sc_home_of_tcb P hm hcs (by rw [htcb]; exact h0)⟩
    have hA := P.tp _ hT
    have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
      P.lay.tcbw _ (P.hT _ hT) 3464#u64 (by simp) (by simp)
    refine view_tzero_home hr ?_ (by unfold scA; rw [← tw _ hT 3464#u64 (by simp) (by simp) (by simp)]; exact hne)
    unfold scA; rw [tcb_wadd_val hA (by simp)]; unfold TZero; simp

/-- **`IoNar` at a view start state** (module docstring): `NN := VN`, `NW := VNW`. -/
theorem io_narA_view {K : KLayoutP} {c : U64} {ρ : U64 → U64}
    (P : IoPre st (Fl4Proofs.P2.E2EP.userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hK : RegionOKP K) (hc : L.cpu s = c) (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) :
    IoNar (L := L) (Fl4Proofs.P2.E2EP.userP K) Z (VN K c ρ) (VNW K c ρ) s := by
  have hK0 := hK.base.base
  obtain ⟨hcur, hcsc, hrh⟩ := io_homes P hK hm
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have curT : ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) off) = .tcb (L.curW s) :=
    fun off h1 h2 => P.lay.tcbw _ (P.hT _ P.cT) off h1 h2
  have scR : ∀ p ∈ Scs, ∀ b, InSC p (Z p) b → region K.toKLayout b = .sc p := fun p hp b hb =>
    P.lay.scw p (Z p) (P.hSc p hp) b hb
  have vnwS : ∀ p ∈ Scs, ρ (fld p 16#u64) = c → ∀ b, InSC p (Z p) b → VNW K c ρ b := fun p hp ha b hb =>
    ⟨vn_of_nf hK (nf_sc (scR p hp b hb) ha), vkc_of hK0 (fun t h => by rw [scR p hp b hb] at h; cases h),
      not_vdec_sc hK0 (scR p hp b hb) ha⟩
  refine ⟨fun o h1 h2 => ?_, fun off h1 h2 => ?_, fun off h1 h2 h3 => ?_, fun sl hsl => ?_, fun o h1 h2 => ?_,
    fun hne => ?_, fun h0 => ?_, fun h0 => ?_⟩
  · have hr : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node c := by
      rw [← hc]; exact P.lay.node _ _ (P.inNode o h1)
    have hv := vn_of_nf hK (nf_node (ρ := ρ) hr)
    exact ⟨hv, hv, vkc_of hK0 (fun t h => by rw [hr] at h; cases h), not_vdec_node hK0 hr⟩
  · exact vn_of_nf hK (nf_tcb (curT off h1 h2) hcur)
  · have hr := curT off h1 h2
    refine ⟨vn_of_nf hK (nf_tcb hr hcur), vkc_of hK0 (fun t h => by rw [hr] at h; cases h; exact hcur),
      not_vdec_tcb hK0 hr hcur ?_⟩
    rw [tcb_wadd_val P.tA h2]; omega
  · obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact ⟨vn_of_nf hK (nf_slot (P.lay.slotw sl hsl sl ⟨le_refl _, by omega⟩)),
      vn_of_nf hK (nf_slot (P.lay.slotw sl hsl _ ⟨by omega, by omega⟩))⟩
  · obtain ⟨k8, kf⟩ := P.lay.ksf
    have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      rw [← P.kb]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine vn_of_nf hK (nf_none (P.lay.ks _ ?_ ?_ ?_))
    · unfold Aligned; rw [hv, ← P.kb]; omega
    · rw [hv, ← P.kb]; omega
    · rw [hv, ← P.kb]; omega
  · have ha := hcsc hne
    exact ⟨fun b _ hb => vn_of_nf hK (nf_sc (scR _ P.cscS b hb) ha),
      fun b _ hb => vnwS _ P.cscS ha b hb.inSC,
      vnwS _ P.cscS ha _ (by
        obtain ⟨hP, hz⟩ := hO.sc _ P.cscS
        obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
        have hv : (core.num.U64.wrapping_add (L.cscW s) layout.sc.CONSUMED).val = (L.cscW s).val + 8 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, layout.sc.CONSUMED]; omega
        exact ⟨by omega, by omega⟩)⟩
  · have hT := (hX.tm.min _ hq.cur).resolve_left h0
    obtain ⟨hd, -⟩ := P.tmc h0
    have hr : region K.toKLayout (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE) = .tcb (L.mem s (tmA (L := L) s)) :=
      P.lay.tcbw _ (P.hT _ hT) 3528#u64 (by simp) (by simp)
    have ho : (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE).val - (L.mem s (tmA (L := L) s)).val = 3528 := by
      unfold fld; rw [tcb_wadd_val (P.tp _ hT) (by simp [oTIMER_DEADLINE])]; simp [oTIMER_DEADLINE]
    have e1 := view_keep_tcb (c := c) (m := ρ) hr (by omega) (by unfold TZero; omega) (by omega)
    have hm' : L.mem s (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE) =
        view K.toKLayout c ρ (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE) :=
      hm _ (field_aligned (P.tp _ hT) (by simp [oTIMER_DEADLINE]) (by simp [oTIMER_DEADLINE])) (fun hu =>
        P.region_kernel (Or.inl (fun h => by
          have h' : region K.toKLayout (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE) = .none := h
          rw [hr] at h'; cases h')) (Or.inl (Or.inl hu)))
    exact vn_td hK (P.hT _ hT) (by rw [← e1, ← hm']; exact hd)
  · obtain ⟨ha, hsa⟩ := hrh h0
    obtain ⟨hT, hsc, -⟩ := bxi_rh P.bxi h0
    have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
      P.lay.tcbw _ (P.hT _ hT) 3464#u64 (by simp) (by simp)
    exact ⟨vn_of_nf hK (nf_tcb hr ha), fun b _ hb => vn_of_nf hK (nf_sc (scR _ hsc b hb) hsa)⟩

/-- **`IoNarD` at a view start state**, the reads in `VN ∧ (RS ∨ VKc)` for a read set `RS` holding the timer word. -/
theorem io_narD_view {K : KLayoutP} {c : U64} {ρ : U64 → U64} {RS : U64 → Prop}
    (P : IoPre st (Fl4Proofs.P2.E2EP.userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hK : RegionOKP K) (hc : L.cpu s = c) (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    (hRS : L.mem s (tmA (L := L) s) ≠ 0#u64 → RS (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)) :
    IoNarD (L := L) (Fl4Proofs.P2.E2EP.userP K) (fun b => VN K c ρ b ∧ (RS b ∨ VKc K.toKLayout c ρ b))
      (VNW K c ρ) s := by
  have hK0 := hK.base.base
  have N := io_narA_view P hK hc hm
  obtain ⟨hcur, hcsc, hrh⟩ := io_homes P hK hm
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have curT : ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) off) = .tcb (L.curW s) :=
    fun off h1 h2 => P.lay.tcbw _ (P.hT _ P.cT) off h1 h2
  have scR : ∀ p ∈ Scs, ∀ b, InSC p (Z p) b → region K.toKLayout b = .sc p := fun p hp b hb =>
    P.lay.scw p (Z p) (P.hSc p hp) b hb
  have hdS : ∀ p ∈ Scs, ρ (fld p 16#u64) = c → RefillsWF st s p (Z p) →
      RdHead (L := L) (fun b => VN K c ρ b ∧ (RS b ∨ VKc K.toKLayout c ρ b)) s p := fun p hp ha hw =>
    ScAcc.head (W := fun _ => True) ⟨fun b _ hb => ⟨vn_of_nf hK (nf_sc (scR p hp b hb) ha),
      Or.inr (vkc_of hK0 (fun t h => by rw [scR p hp b hb] at h; cases h))⟩, fun _ _ _ => trivial, trivial⟩ hw
  refine ⟨fun o h1 h2 => ⟨⟨(N.nd o h1 h2).1, Or.inr (N.nd o h1 h2).2.2.1⟩, (N.nd o h1 h2).2⟩,
    fun off h1 h2 => ⟨N.cur off h1 h2, Or.inr (vkc_of hK0 (fun t h => by
      rw [curT off h1 h2] at h; cases h; exact hcur))⟩, ?_, fun sl hsl => ?_, fun o h1 h2 => ?_,
    fun hne => hdS _ P.cscS (hcsc hne) P.cscwf, fun h0 => ⟨N.td h0, Or.inl (hRS h0)⟩, fun h0 => ?_⟩
  · exact (N.reg P.tA (by simp [layout.reg.FAULT_IP])).2
  · obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have r1 : region K.toKLayout sl = .slot sl := P.lay.slotw sl hsl sl ⟨le_refl _, by omega⟩
    have r2 : region K.toKLayout (core.num.U64.wrapping_add sl 8#u64) = .slot sl :=
      P.lay.slotw sl hsl (core.num.U64.wrapping_add sl 8#u64) ⟨by omega, by omega⟩
    exact ⟨⟨(N.slot sl hsl).1, Or.inr (vkc_of hK0 (fun t h => by rw [r1] at h; cases h))⟩,
      ⟨(N.slot sl hsl).2, Or.inr (vkc_of hK0 (fun t h => by rw [r2] at h; cases h))⟩⟩
  · obtain ⟨k8, kf⟩ := P.lay.ksf
    have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      rw [← P.kb]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have hr : region K.toKLayout (core.num.U64.wrapping_add (L.ksb s) o) = .none := by
      refine P.lay.ks _ ?_ ?_ ?_
      · unfold Aligned; rw [hv, ← P.kb]; omega
      · rw [hv, ← P.kb]; omega
      · rw [hv, ← P.kb]; omega
    exact ⟨N.ks o h1 h2, Or.inr (vkc_of hK0 (fun t h => by rw [hr] at h; cases h))⟩
  · obtain ⟨ha, hsa⟩ := hrh h0
    obtain ⟨hT, hsc, hmx⟩ := bxi_rh P.bxi h0
    have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
      P.lay.tcbw _ (P.hT _ hT) 3464#u64 (by simp) (by simp)
    exact ⟨⟨(N.rs h0).1, Or.inr (vkc_of hK0 (fun t h => by rw [hr] at h; cases h; exact ha))⟩,
      hdS _ hsc hsa (bxi_scin P.bxi hsc hmx).1⟩

end pins

end
end Fl4Proofs.P2.CoreView
