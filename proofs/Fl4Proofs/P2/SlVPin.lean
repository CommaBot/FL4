/-
# P2 (line p3mc, gen 15): the words of the sl path at a view start that the view keeps

At an sl entry state `s` at core `c`'s view of `ρ` (`SlVC`: the aligned kernel words are the view's, the current
thread, the current SC, the release head and its SC homed on `c` in `ρ`, an SC with a nonzero `TCB` back-pointer
homed on `c`, no kernel global / ASID / user word a PTE), the words the sl path touches are, word by word:

* **`SR`** (reads): kept by the view in value and owner (`VN`) and no PTE word;
* **`VNW`** (writes): `VN`, class owner kept (`VKc`), deciding no foreign owner (`¬ VDec`).

The generic lemmas: `sr_nf`, `vnw_nf` (from `NotForeign`), `sr_tcb` / `vnw_tcb` / `sr_reg` / `vnw_reg` (a homed
thread's words), `sr_tslot`, `srw_ep`, `srw_rp`, `srw_sc` / `scAcc_v` (a homed SC), `srw_node`, `sr_ks`, `srw_user`
(user words: region `.none`); then the records shared by both arms at a prefix state: **`slCom_v`** (`SlCom SR`),
**`preAcc_v`**, **`preDec_v`**, **`rdHead_v`**.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.SlVBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb TZero)

noncomputable section
open Classical

/-! ## The sets -/

/-- **A read the view keeps**: `VN` and no PTE word. -/
abbrev SR (K : KLayoutP) (c : U64) (ρ : U64 → U64) (b : U64) : Prop := VN K c ρ b ∧ b ∉ K.ptes

section gen
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64}

theorem sr_nf (hK : RegionOKP K) {b : U64} (hr : region K.toKLayout b ≠ .none)
    (h : NotForeign K.toKLayout c ρ b) : SR K c ρ b :=
  ⟨vn_of_nf hK h, fun hp => hr (hK.none b hp)⟩

theorem vnw_nf (hK : RegionOKP K) {b : U64} (h : NotForeign K.toKLayout c ρ b)
    (hd : ¬ VDec K.toKLayout c ρ b) : VNW K c ρ b :=
  ⟨vn_of_nf hK h, vkc_of hK.base.base h.1, hd⟩

theorem not_vdec_none {Kl : KLayout} (hK : OwnMap.RegionOK Kl) {q : U64} (hr : region Kl q = .none) :
    ¬ VDec Kl c ρ q := by
  rintro (⟨t, off, ht, -, ho, rfl⟩ | ⟨p', hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨p', b, hb, -, rfl⟩)
  · rw [(hK.tcb t ht off (CoreView.decOff_list ho)).1] at hr; cases hr
  · rw [(hK.ntfn p' hp).1] at hr; cases hr
  · rw [(hK.tcb t ht _ (Or.inl rfl)).1] at hr; cases hr
  · rw [(hK.scw p' b hb).1] at hr; cases hr

variable (hK : RegionOKP K) (hX : RegionOKX K.toKLayout)
include hK hX

theorem sr_tcb {t o : U64} (ht : K.toKLayout.heap t = some .tcb) (ha : ρ (fld t oAFFINITY) = c)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) :
    SR K c ρ (core.num.U64.wrapping_add t o) := by
  obtain ⟨r, -, -⟩ := hX.tcbW t ht o h1 h2 h3
  exact sr_nf hK (by rw [r]; intro h; cases h) (nf_tcb r ha)

theorem vnw_tcb {t o : U64} (ht : K.toKLayout.heap t = some .tcb) (ha : ρ (fld t oAFFINITY) = c)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (h4 : o.val ≠ 3520) :
    VNW K c ρ (core.num.U64.wrapping_add t o) := by
  obtain ⟨r, v, -⟩ := hX.tcbW t ht o h1 h2 h3
  exact vnw_nf hK (nf_tcb r ha) (not_vdec_tcb hK.base.base r ha (by rw [v]; exact h4))

theorem sr_reg {t r : U64} (ht : K.toKLayout.heap t = some .tcb) (ha : ρ (fld t oAFFINITY) = c)
    (hr : r.val < 384) : SR K c ρ (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact sr_tcb hK hX ht ha (by omega) (by omega) (by omega)

theorem vnw_reg {t r : U64} (ht : K.toKLayout.heap t = some .tcb) (ha : ρ (fld t oAFFINITY) = c)
    (hr : r.val < 384) : VNW K c ρ (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact vnw_tcb hK hX ht ha (by omega) (by omega) (by omega) (by omega)

theorem sr_tslot {t i : U64} (ht : K.toKLayout.heap t = some .tcb) (hi : i.val < 6) :
    SR K c ρ (slotIdx t i) ∧ SR K c ρ (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨hs, -, r8, -, -, -⟩ := hX.tslot t ht i hi
  have r0 := hK.base.base.slot _ hs
  exact ⟨sr_nf hK (by rw [r0]; intro h; cases h) (nf_slot r0), sr_nf hK (by rw [r8]; intro h; cases h) (nf_slot r8)⟩

theorem srw_ep {p o : U64} (hp : K.toKLayout.heap p = some .ep) (h1 : o.val < 16) (h2 : o.val % 8 = 0) :
    SR K c ρ (core.num.U64.wrapping_add p o) ∧ VNW K c ρ (core.num.U64.wrapping_add p o) := by
  obtain ⟨r, -⟩ := hX.epW p hp o h1 h2
  exact ⟨sr_nf hK (by rw [r]; intro h; cases h) (nf_obj r), vnw_nf hK (nf_obj r) (not_vdec_obj hK.base.base r)⟩

theorem srw_rp {p o : U64} (hp : K.toKLayout.heap p = some .reply) (h1 : o.val < 32) (h2 : o.val % 8 = 0) :
    SR K c ρ (core.num.U64.wrapping_add p o) ∧ VNW K c ρ (core.num.U64.wrapping_add p o) := by
  obtain ⟨r, -⟩ := hX.rpW p hp o h1 h2
  exact ⟨sr_nf hK (by rw [r]; intro h; cases h) (nf_obj r), vnw_nf hK (nf_obj r) (not_vdec_obj hK.base.base r)⟩

theorem srw_sc {p : U64} {z : Nat} (hz : K.toKLayout.heap p = some (.sc z)) (hc : ρ (fld p 16#u64) = c)
    {b : U64} (hb : InSC p z b) : SR K c ρ b ∧ VNW K c ρ b := by
  have r := hX.scW p z hz b hb
  exact ⟨sr_nf hK (by rw [r]; intro h; cases h) (nf_sc r hc), vnw_nf hK (nf_sc r hc) (not_vdec_sc hK.base.base r hc)⟩

theorem scAcc_v {p : U64} {z : Nat} (hz : K.toKLayout.heap p = some (.sc z)) (hc : ρ (fld p 16#u64) = c) :
    ScAcc (SR K c ρ) (VNW K c ρ) p z := by
  obtain ⟨-, -, hin, -⟩ := sc_off hX hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    (by simp [layout.sc.CONSUMED])
  exact ⟨fun b _ hb => (srw_sc hK hX hz hc hb).1, fun b _ hb => (srw_sc hK hX hz hc hb.inSC).2,
    (srw_sc hK hX hz hc hin).2⟩

theorem srw_user {b : U64} (hu : b ∈ K.user) (hup : ∀ b ∈ K.user, b ∉ K.ptes) : SR K c ρ b ∧ VNW K c ρ b := by
  have hr : region K.toKLayout b = .none := by
    by_contra h; exact hX.kern b h hu
  exact ⟨⟨vn_of_nf hK (nf_none hr), hup b hu⟩, vnw_nf hK (nf_none hr) (not_vdec_none hK.base.base hr)⟩

end gen

/-! ## The view context at an entry state -/

section ctx
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The view context of an sl entry state `s`** (module docstring). -/
structure SlVC (K : KLayoutP) (c : U64) (ρ : U64 → U64) (s : S) : Prop where
  hK : RegionOKP K
  cpu : L.cpu s = c
  hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x
  cur : ρ (fld (L.curW s) oAFFINITY) = c
  csc : ρ (fld (L.cscW s) 16#u64) = c
  rh : L.mem s (rhA (L := L) s) ≠ 0#u64 → ρ (fld (L.mem s (rhA (L := L) s)) oAFFINITY) = c ∧
    ρ (fld (L.mem s (scA (L.mem s (rhA (L := L) s)))) 16#u64) = c
  scb : ∀ p ∈ K.toKLayout.heap.scs, L.mem s (scTcbA p) ≠ 0#u64 → ρ (fld p 16#u64) = c
  ks : KsNoE (· ∈ K.ptes) K.toKLayoutV
  ksb : L.ksb s = K.ksb
  tab : TabNoE (L := L) (· ∈ K.ptes) s
  upte : ∀ b ∈ K.user, b ∉ K.ptes
  scn : L.mem s (scA (L.curW s)) ≠ 0#u64

variable {K : KLayoutP} {c : U64} {ρ : U64 → U64}

theorem srw_node {s : S} (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    SR K c ρ (L.nodeAt s (L.cpu s) o) ∧ VNW K c ρ (L.nodeAt s (L.cpu s) o) := by
  obtain ⟨hk, hc⟩ := hJ.kc
  have v := nodeAt_val hN ho
  have hr : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    hJ.regionOKX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  have hr' : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node c := by rw [hr, V.cpu]
  exact ⟨sr_nf V.hK (by rw [hr']; intro h; cases h) (nf_node hr'),
    vnw_nf V.hK (nf_node hr') (not_vdec_node V.hK.base.base hr')⟩

theorem sr_ks {s : S} (V : SlVC (L := L) K c ρ s) (hJ : SlJAt (L := L) K.toKLayout s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 256) (h8 : o.val % 8 = 0) :
    SR K c ρ (core.num.U64.wrapping_add (L.ksb s) o) := by
  have hX := hJ.regionOKX
  have hk := V.ksb
  have hf := hN.fits
  have ha := hN.align
  simp only [LawfulStore.nodeBase] at hf ha
  have e : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hal : Aligned (core.num.U64.wrapping_add (L.ksb s) o) := by unfold Aligned; rw [e]; omega
  have hr : region K.toKLayout (core.num.U64.wrapping_add (L.ksb s) o) = .none :=
    hX.ks _ hal (by rw [e, ← hk]; omega) (by rw [e, ← hk]; omega)
  refine ⟨vn_of_nf V.hK (nf_none hr), ?_⟩
  rw [hk]; exact V.ks o (by omega)

end ctx

/-! ## The records shared by both arms -/

section com
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The prefix words** (`PreAcc` for `SR` / `VNW`). -/
theorem preAcc_v {s : S} (V : SlVC (L := L) K c ρ s) (B : SlJAt (L := L) K.toKLayout s)
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found K.toKLayout.heap.tcbs Cs Ω K.user Sg
      K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns Ac K.toKLayout.heap
      K.toKLayout.heap.scBits s) :
    PreAcc (L := L) (SR K c ρ) (VNW K c ρ) s := by
  have hX := B.regionOKX
  exact ⟨fun o h1 h2 => srw_node V B E.hN h1 h2,
    sr_tcb V.hK hX E.hSt.1 V.cur (o := 3456#u64) (by simp) (by simp) (by simp),
    sr_reg V.hK hX E.hSt.1 V.cur (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP]),
    vnw_reg V.hK hX E.hSt.1 V.cur (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])⟩

/-- **The prefix words of a declined run** (`PreDec` for `SR`, writes unconstrained). -/
theorem preDec_v {s : S} (V : SlVC (L := L) K c ρ s) (B : SlJAt (L := L) K.toKLayout s)
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found K.toKLayout.heap.tcbs Cs Ω K.user Sg
      K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns Ac K.toKLayout.heap
      K.toKLayout.heap.scBits s) :
    PreDec (L := L) (SR K c ρ) (fun _ => True) s := by
  have P := preAcc_v ar V B E
  exact ⟨fun o h1 h2 => (P.nd o h1 h2).1, trivial, trivial, P.fl, P.nx, trivial⟩

/-- **The head refill of an SC homed on `c` is `SR` at the prefix state.** -/
theorem rdHead_v (hA : P0.ArchTotal ar) {s : S} (V : SlVC (L := L) K c ρ s) (B : SlJAt (L := L) K.toKLayout s)
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found K.toKLayout.heap.tcbs Cs Ω K.user Sg
      K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns Ac K.toKLayout.heap
      K.toKLayout.heap.scBits s)
    (Hh : SlHere (st := st) K.toKLayout K.toKLayout.heap.scBits K.toKLayout.heap.scs found s) {a X a1}
    (LP : LocalPre (st := st) ar s a (X, a1))
    {sc : U64} (hs : ScHere (st := st) K.toKLayout K.toKLayout.heap.scBits K.toKLayout.heap.scs s sc)
    (hc : ρ (fld sc 16#u64) = c) : RdHead (L := L) (SR K c ρ) X sc := by
  have hX := B.regionOKX
  obtain ⟨hz, hin, hmx, -⟩ := hs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  have hW : RefillsWF st X sc (K.toKLayout.heap.scBits sc) :=
    ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
  exact ScAcc.head (scAcc_v V.hK hX hz hc) hW

set_option maxHeartbeats 4000000 in
/-- **The common words at a prefix state are `SR`** (`slCom_nu` for `SR`). -/
theorem slCom_v (hA : P0.ArchTotal ar) {s : S} (V : SlVC (L := L) K c ρ s) (B : SlJAt (L := L) K.toKLayout s)
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found K.toKLayout.heap.tcbs Cs Ω K.user Sg
      K.toKLayout.heap.replies K.toKLayout.heap.scs K.toKLayout.heap.ntfns Ac K.toKLayout.heap
      K.toKLayout.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : SlCom (L := L) (SR K c ρ) X := by
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → SR K c ρ (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 => by rw [nX]; exact (srw_node V B E.hN h1 h2).1
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem X (L.nodeAt X (L.cpu X) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 h3 h4 => by
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN h1 h2) (not_slDS_node E.hN E.hT E.hcT h1 h3 h4)
  have eTm : L.mem X (tmA (L := L) X) = L.mem s (tmA (L := L) s) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) :=
    eN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  refine ⟨nd, ?_, ?_, ⟨nd _ (by simp [l1Off]) (by simp [l1Off]), fun inv hinv => nd _ (by simp; omega)
    (by simp <;> omega)⟩, fun h => ?_, fun h => ?_⟩
  · rw [kX]; exact sr_ks V B E.hN (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact sr_ks V B E.hN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, hd0, -⟩ := tm_of ar hA hX (slSets_conv K.toKLayout) E hk hcp LP h
    generalize L.mem s (tmA (L := L) s) = t at ht hd0
    obtain ⟨r, v, al⟩ := hX.tcbW t ht 3528#u64 (by simp) (by simp) (by simp)
    have e : core.num.U64.wrapping_add t 3528#u64 = fld t oTIMER_DEADLINE := rfl
    have hu : fld t oTIMER_DEADLINE ∉ K.user := by rw [← e]; exact hX.kern _ (by rw [r]; intro h; cases h)
    have hv : view K.toKLayout c ρ (fld t oTIMER_DEADLINE) = ρ (fld t oTIMER_DEADLINE) :=
      view_keep_tcb (by rw [← e]; exact r) (by rw [← e, v]; simp) (by rw [← e, v]; unfold TZero; simp)
        (by rw [← e, v]; simp)
    have h0 : ρ (fld t oTIMER_DEADLINE) ≠ 0#u64 := by
      rw [← hv, ← V.hm _ (by rw [← e]; exact al) hu]
      intro h0; apply hd0; rw [h0]; rfl
    rw [e]
    exact ⟨vn_td V.hK ht h0, fun hp => by rw [← e] at hp; have := V.hK.none _ hp; rw [r] at this; cases this⟩
  · rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := rh_of ar hA hX (slSets_conv K.toKLayout) E hk hcp LP h
    obtain ⟨hrA, hrS⟩ := V.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    refine ⟨sr_tcb V.hK hX ht hrA (o := 3464#u64) (by simp) (by simp) (by simp), ?_⟩
    generalize L.mem s (scA (L.mem s (rhA (L := L) s))) = sc at hs hrS
    obtain ⟨hz, hin, hmx, -⟩ := hs
    obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
    have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
      lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 hk hcp
        (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
    have hW : RefillsWF st X sc (K.toKLayout.heap.scBits sc) :=
      ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
    exact ScAcc.head (scAcc_v V.hK hX hz hrS) hW

end com

end
end Fl4Proofs.P2.E2EP
