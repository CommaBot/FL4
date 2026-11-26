/-
# P2 (line p3mc, gen 9): U9's re-annotated VM-fault body is `Safe` at a view start whose fault handler is another core's

The decline split for vmF (handoff p3mc §11, step 1) at core `c`'s view `view K c ρ`: at a start state `σ` of the
VM-fault path (`VmPre (userV K)`, `QPs`, memory the view on aligned kernel words, core `c`) whose prefix state finds
the fault endpoint in the receive state with head `d`, the action `RESUME_CURRENT` (0), and `ρ (AFFINITY d) ≠ c`,
U9's armed program `narrowSP cls (ko K μ) c (VO K c ρ) ∅ (body σ a)` is `Safe` at the physical memory `μ`
(`VEq ρ μ`):

* **pins** (`vm_sc_home_of_tcb`, `vm_homes`): `CoreView.sc_home_of_tcb` / `io_homes` for `VmBase`: the release head
  and its SC are homed on `c` in `ρ`, and so is the current SC where the current thread has one (back-pointer);
* `VmFhR.and`, `VmFhR.ofDF` (the IoRS half from `vm_dfOf`), **`vmFhR_vn`** (the `VN` half: the words the
  declining run reads up to the handler's `AFFINITY` are kept by the view, value and owner; the current thread has
  an SC since the action is 0, `BoundInv.resume`);
* `ownP_of_own`, `stepOK_safeP` (the prefix writes pass `StepOK` under `ownP` at any state),
  `po_of_rperm`;
* **`vmF_fh_annV`**: `PathObl.vm_fh_safe` with `Rd := IoRS (userP K) ∧ VN`, `Ro := rsE ptes (IoRS (userV K)) ∧ VO`,
  then `E2E.safe_narrow_tr`.

No premise: every fact is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU9
import Fl4Proofs.P2.VmFhSafe
import Fl4Proofs.P2.NarrowTr
import Fl4Proofs.P2.E2EPVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td view_keep_tcb
  view_sctcb_home view_tzero_home)

noncomputable section
open Classical

/-! ## Owners under `ownP` at a layout without VCPUs -/

theorem ownP_of_own {K : KLayoutP} (nv : K.vcpus = ∅) {m m' : U64 → U64}
    (h : OwnMap.own K.toKLayout m = OwnMap.own K.toKLayout m') : ownP K m = ownP K m' := by
  funext x
  by_cases hp : x ∈ K.ptes
  · rw [ownP_pte hp, ownP_pte hp]
  · rw [ownP_eq_own nv hp, ownP_eq_own nv hp, h]

theorem nf_obj {K : KLayout} {c : U64} {ρ : U64 → U64} {b p : U64} (hr : region K b = .obj p) :
    NotForeign K c ρ b := by
  unfold NotForeign
  refine ⟨fun t h => ?_, fun p' h => ?_, fun d h => ?_, fun p' h => ?_⟩ <;> rw [hr] at h <;> cases h

theorem po_of_rperm {own : (U64 → U64) → U64 → Owner U64 U64} {c : U64} {lk : U64 → Prop} {m : U64 → U64}
    {x : U64} (h : RPerm own c lk m x) : PO c lk (own m x) := by
  rcases h with h | h
  · left
    revert h
    cases own m x <;> exact id
  · right; exact h

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The prefix writes pass `StepOK` under `ownP`**, at any state. -/
theorem stepOK_safeP {K : KLayoutP} (hK : RegionOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout)
    {m0 : U64 → U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop} {x : S} {b v : U64} (hb : Aligned b)
    (h : SafeW K.toKLayout b) :
    StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) User c lk (L.mem x)
      (L.mem (L.wr x b v)) := by
  have e := ownP_of_own nv (own_wr_safe (st := st) (x := x) (v := v) hK.base.base hLA hb h)
  exact ⟨fun z hz => absurd (congrFun e z) hz,
    (stepOK_safe (st := st) (m0 := m0) (User := User) (c := c) (lk := lk) (x := x) (v := v) hK.base.base hLA hb h).2⟩

/-! ## `VmFhR` by halves -/

theorem VmFhR.and {R1 R2 : U64 → Prop} {s s1 : S} (F1 : VmFhR st R1 s s1) (F2 : VmFhR st R2 s s1) :
    VmFhR st (fun b => R1 b ∧ R2 b) s s1 where
  k := F1.k
  c := F1.c
  nd o h1 h2 := ⟨F1.nd o h1 h2, F2.nd o h1 h2⟩
  dt := ⟨F1.dt, F2.dt⟩
  cd := ⟨F1.cd, F2.cd⟩
  cur := F1.cur
  sl sl h := ⟨⟨(F1.sl sl h).1, (F2.sl sl h).1⟩, ⟨(F1.sl sl h).2, (F2.sl sl h).2⟩⟩
  ep sl ptr badge x y g gr h1 h2 := ⟨⟨(F1.ep sl ptr badge x y g gr h1 h2).1, (F2.ep sl ptr badge x y g gr h1 h2).1⟩,
    ⟨(F1.ep sl ptr badge x y g gr h1 h2).2, (F2.ep sl ptr badge x y g gr h1 h2).2⟩⟩
  td h := ⟨F1.td h, F2.td h⟩
  rs h := ⟨⟨(F1.rs h).1, (F2.rs h).1⟩, ⟨(F1.rs h).2.1, (F2.rs h).2.1⟩, ⟨(F1.rs h).2.2.1, (F2.rs h).2.2.1⟩,
    ⟨(F1.rs h).2.2.2, (F2.rs h).2.2.2⟩⟩
  suf := ⟨⟨F1.suf.1, F2.suf.1⟩, ⟨F1.suf.2.1, F2.suf.2.1⟩, ⟨F1.suf.2.2, F2.suf.2.2⟩⟩

theorem VmFhR.ofDF {K : KLayout} {T : Set U64} {Locks : S → U64 → Prop} {s s1 : S} (D : VmDF st K T Locks s s1) :
    VmFhR st (IoRS (st := st) K Locks s) s s1 where
  k := D.k
  c := D.c
  nd := D.nd
  dt := D.ksw _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  cd := D.ksw _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  cur := D.cur
  sl := D.sl
  ep sl ptr badge x y g gr h1 h2 := ⟨(D.ep sl ptr badge x y g gr h1 h2).1, (D.ep sl ptr badge x y g gr h1 h2).2.1⟩
  td := D.td
  rs := D.rs
  suf := D.suf

/-! ## The pins at a view start state of the VM-fault path -/

variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- An SC whose `TCB` word is a nonzero value at the view is really on `c` (`CoreView.sc_home_of_tcb`). -/
theorem vm_sc_home_of_tcb {K : KLayoutP} {c : U64} {ρ : U64 → U64}
    (P : VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    {p : U64} (hp : p ∈ Scs) (h0 : L.mem s (scTcbA p) ≠ 0#u64) : ρ (fld p 16#u64) = c := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  obtain ⟨hP, hz⟩ := hO.sc _ hp
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hv : (scTcbA p).val = p.val + 24 := by
    unfold scTcbA; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hr : region (userP K) (scTcbA p) = .sc p :=
    P.lay.io.scw p (Z p) (P.hSc p hp) _ ⟨by omega, by omega⟩
  have ha : Aligned (scTcbA p) := by unfold Aligned; rw [hv]; omega
  have hk : scTcbA p ∉ K.user := fun hu =>
    P.region_kernel (Or.inl (by rw [hr]; simp)) (Or.inl (Or.inl hu))
  exact view_sctcb_home (K := K.toKLayout) hr (by omega) (by rw [← hm _ ha hk]; exact h0)

/-- **The current SC (where the current thread has one), the release head and its SC are homed on `c`.** -/
theorem vm_homes {K : KLayoutP} {c : U64} {ρ : U64 → U64}
    (P : VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) :
    (L.mem s (scA (L.curW s)) ≠ 0#u64 → ρ (fld (L.cscW s) 16#u64) = c) ∧
      (L.mem s (rhA (L := L) s) ≠ 0#u64 → ρ (fld (L.mem s (rhA (L := L) s)) oAFFINITY) = c ∧
        ρ (fld (L.mem s (scA (L.mem s (rhA (L := L) s)))) 16#u64) = c) := by
  have tw : ∀ t ∈ T, ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
      L.mem s (core.num.U64.wrapping_add t off) = view K.toKLayout c ρ (core.num.U64.wrapping_add t off) :=
    fun t ht off h1 h2 h3 => hm _ (field_aligned (P.tp t ht) h2 h3) (fun hu =>
      P.region_kernel (Or.inl (by have e := P.lay.io.tcbw t (P.hT t ht) off h1 h2; unfold fld at e; rw [e]; simp))
        (Or.inl (Or.inl hu)))
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  refine ⟨fun hne => ?_, fun h0 => ?_⟩
  · obtain ⟨hcs, htcb, -⟩ := hX.bound _ P.cT hne
    rw [P.hcsc hne]
    exact vm_sc_home_of_tcb P hm hcs (by rw [htcb]; intro e; exact P.tA.ne0 (by rw [e]; rfl))
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
    refine ⟨?_, vm_sc_home_of_tcb P hm hcs (by rw [htcb]; exact h0)⟩
    have hA := P.tp _ hT
    have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
      P.lay.io.tcbw _ (P.hT _ hT) 3464#u64 (by simp) (by simp)
    refine view_tzero_home hr ?_ (by unfold scA; rw [← tw _ hT 3464#u64 (by simp) (by simp) (by simp)]; exact hne)
    unfold scA; rw [tcb_wadd_val hA (by simp)]; unfold Fl4Proofs.P2.CoreView.TZero; simp

variable {A : Type} {ar : machine.Arch A} {U : Set U64} {Locks : S → U64 → Prop}

set_option maxHeartbeats 1000000 in
/-- **The words the declining run reads up to the handler's `AFFINITY` are kept by the view** (module
docstring), where the current SC is homed on `c`. -/
theorem vmFhR_vnH (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64}
    (P : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    (hcH : ρ (fld (L.cscW s) 16#u64) = c)
    {a : A} {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar s a = ok (s1, a1)) :
    VmFhR st (VN K c ρ) s s1 := by
  have B := P.base
  have hK0 := hK.base.base
  have hN := B.np
  have hT := B.tp
  have HY := P.hyp a s1 a1 eu
  obtain ⟨-, hrh⟩ := vm_homes B hm
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  rw [update_timestamp_ok ar hN hn] at eu
  have eS := (Prod.mk.inj (ok_inj_ff eu)).1
  subst eS
  have ndR : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node c := fun o ho => by
    rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)
  have ndV : ∀ o : U64, o.val < 4288 → VN K c ρ (L.nodeAt s (L.cpu s) o) := fun o ho =>
    vn_of_nf hK (nf_node (ndR o ho))
  have scR : ∀ p ∈ Scs, ∀ b, Fl4Proofs.P1.InSC p (Z p) b → region K.toKLayout b = .sc p := fun p hp b hb =>
    B.lay.io.scw p (Z p) (B.hSc p hp) b hb
  have scV : ∀ p ∈ Scs, ρ (fld p 16#u64) = c → RefillsWF st s p (Z p) → RdHead (L := L) (VN K c ρ) s p :=
    fun p hp ha hw => ScAcc.head (W := fun _ => True)
      ⟨fun b _ hb => vn_of_nf hK (nf_sc (scR p hp b hb) ha), fun _ _ _ => trivial, trivial⟩ hw
  have ksV : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → VN K c ρ (core.num.U64.wrapping_add (L.ksb s) o) := by
    intro o h1 h2
    obtain ⟨k8, kf⟩ := B.lay.io.ksf
    have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      rw [← B.kb]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine vn_of_nf hK (nf_none (B.lay.io.ks _ ?_ ?_ ?_))
    · unfold Aligned; rw [hv, ← B.kb]; omega
    · rw [hv, ← B.kb]; omega
    · rw [hv, ← B.kb]; omega
  have etm : L.mem (utW (L := L) s n) (tmA (L := L) (utW (L := L) s n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.TIMER_MIN) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (utW (L := L) s n) (rhA (L := L) (utW (L := L) s n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (utW (L := L) s n) (L.nodeAt (utW (L := L) s n) (L.cpu (utW (L := L) s n)) layout.node.RELEASE_HEAD) = _
    rw [ut_nodeAt]
    exact ut_node hN n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  refine
    { k := utW_ksb s n
      c := utW_cpu s n
      nd := fun o ho _ => by rw [ut_nodeAt]; exact ndV o ho
      dt := by rw [utW_ksb]; exact ksV _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
      cd := by rw [utW_ksb]; exact ksV _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
      cur := ut_cur hN n
      sl := ?_
      ep := ?_
      td := ?_
      rs := ?_
      suf := ?_ }
  · intro sl hsl
    obtain ⟨hsl1, -⟩ := B.lay.io.tslot _ (B.hT _ B.cT) _ sl hsl (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    obtain ⟨h8, hf⟩ := B.lay.io.slot8 sl hsl1
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact ⟨vn_of_nf hK (nf_slot (B.lay.io.slotw sl hsl1 sl ⟨le_refl _, by omega⟩)),
      vn_of_nf hK (nf_slot (B.lay.io.slotw sl hsl1 _ ⟨by omega, by omega⟩))⟩
  · intro sl ptr badge x y g gr hsl hcap
    have hsl' : obj.Tcb.slot (L.curW (utW (L := L) s n)) layout.tcb.SLOT_FAULT_HANDLER = ok sl := by
      rw [ut_cur hN n]; exact hsl
    have hpH : H ptr = some .ep := by
      have h1 := HY.cap
      rw [hsl', WP.spec_ok, hcap, WP.spec_ok] at h1
      exact h1.1 ptr badge x y g gr rfl
    have hKp := P.hEp ptr hpH
    have hEP := vm_epP HY.bxi hpH
    have h1 := epTSA_val hEP
    have h2 := epHeadA_val (ep := ptr)
    have := hEP.fits
    exact ⟨vn_of_nf hK (nf_obj (B.lay.epw ptr hKp _ ⟨by omega, by omega⟩)),
      vn_of_nf hK (nf_obj (B.lay.epw ptr hKp _ ⟨by omega, by omega⟩))⟩
  · intro h0
    rw [etm] at h0 ⊢
    obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B.bxi
    have hTm := (hX.tm.min _ hq.cur).resolve_left h0
    obtain ⟨hd, -⟩ := B.tmc h0
    have hr : region K.toKLayout (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
        .tcb (L.mem s (tmA (L := L) s)) :=
      B.lay.io.tcbw _ (B.hT _ hTm) 3528#u64 (by simp) (by simp)
    have ho : (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE).val -
        (L.mem s (tmA (L := L) s)).val = 3528 := by
      unfold fld; rw [tcb_wadd_val (B.tp _ hTm) (by simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE])]
      simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE]
    have e1 := view_keep_tcb (c := c) (m := ρ) hr (by omega) (by unfold Fl4Proofs.P2.CoreView.TZero; omega)
      (by omega)
    have hm' : L.mem s (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
        view K.toKLayout c ρ (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) :=
      hm _ (field_aligned (B.tp _ hTm) (by simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE])
        (by simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE])) (fun hu =>
        B.region_kernel (Or.inl (fun h => by
          have h' : region (userP K) (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) = .none := h
          have hr' : region (userP K) (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
            .tcb (L.mem s (tmA (L := L) s)) := hr
          rw [hr'] at h'; cases h')) (Or.inl (Or.inl hu)))
    exact vn_td hK (B.hT _ hTm) (by rw [← e1, ← hm']; exact hd)
  · intro h0
    rw [erh] at h0 ⊢
    obtain ⟨hrT, hscS, hmx⟩ := bxi_rh B.bxi h0
    have esc : L.mem (utW (L := L) s n) (scA (L.mem s (rhA (L := L) s))) =
        L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      ut_tcb hN hT n hrT (Kx := 3464#u64) (by simp) (by simp)
    rw [esc]
    obtain ⟨ha, hsa⟩ := hrh h0
    have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
      B.lay.io.tcbw _ (B.hT _ hrT) 3464#u64 (by simp) (by simp)
    exact ⟨vn_of_nf hK (nf_tcb hr ha),
      rdHead_ut B.bxi n hscS (scV _ hscS hsa (bxi_scin B.bxi hscS hmx).1)⟩
  · rw [ut_csc hN n]
    exact rdHead_ut B.bxi n B.cscS (scV _ B.cscS hcH B.cscwf)

/-- **`vmFhR_vnH` where the current thread has an SC** (the current SC is then homed, `vm_homes`). -/
theorem vmFhR_vn (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64}
    (P : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    (hsc0 : L.mem s (scA (L.curW s)) ≠ 0#u64)
    {a : A} {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar s a = ok (s1, a1)) :
    VmFhR st (VN K c ρ) s s1 :=
  vmFhR_vnH hA hK P hc hm ((vm_homes P.base hm).1 hsc0) eu

end

/-! ## The re-annotated body at a view start whose fault handler is another core's -/

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 2000000 in
/-- **U9's armed VM-fault program is `Safe` at a view start whose fault handler is another core's** (module
docstring). -/
theorem vmF_fh_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {addr code : U64} {σ : S} {a : A}
    (hP : VmPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1))
    {sl ptr badge : U64} {x' y g gr : Bool}
    (hsl : obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr))
    (hst : L.epState s1 ptr = obj.EP_RECV)
    (hρd : ρ (affA (L.mem s1 (epHeadA ptr))) ≠ c) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_vm_fault_local addr code) ∅ a)) := by
  have hK0 := hK.base.base
  have P' : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ := vmFPre_userP hK hq.ks hP.1
  have B := hP.1.base
  have B' := P'.base
  have D' := vm_dfOf hA P' hP.2.1 eu
  have hsc0 : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := B.bxi.2.1.resume hact
  -- the read sets
  let Rd : U64 → Prop := fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b
  let Ro : U64 → Prop := fun b => rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ b ∧ VO K c ρ b
  have F : VmFhR st Rd σ s1 := VmFhR.and (VmFhR.ofDF D') (vmFhR_vn hA hK P' hc hmm hsc0 eu)
  have hR0 : ∀ q, Rd q → Ro q ∧ q ∉ K.user := fun q hq' =>
    ⟨⟨⟨(ioRS_of_userP hq'.1).1, (ioRS_of_userP hq'.1).2⟩, hq'.2.2⟩, fun hu => hq'.1.2.1 (Or.inl (Or.inl hu))⟩
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)))⟩
  have rT : Rd (ctA (L := L) σ) := ndR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN : Rd (cnA (L := L) σ) := ndR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
    ndR _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  -- the handler
  have hd : L.mem s1 (epHeadA ptr) ∈ T := (D'.ep sl ptr badge x' y g gr hsl hcap).2.2 hst
  have hdA' := B.tp _ hd
  have hdK : K.heap (L.mem s1 (epHeadA ptr)) = some .tcb := B.hT _ hd
  have hAff : IoRS (st := st) (userP K) Locks σ (affA (L.mem s1 (epHeadA ptr))) :=
    D'.gate _ hd 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
  have hAffP : affA (L.mem s1 (epHeadA ptr)) ∉ K.ptes := (ioRS_of_userP hAff).2
  have hgate : ∀ m, ownP K m (affA (L.mem s1 (epHeadA ptr))) = .gate := fun m => by
    rw [ownP_eq_own nv hAffP]
    exact own_tcb_gate (K := userV K.toKLayoutV) B.lay.io hdK hdA' (off := 3520#u64) (by simp) (by simp)
      (by simp [Fl4Proofs.P2.OwnMap.GateField])
  have hAo : Ro (affA (L.mem s1 (epHeadA ptr))) ∧ affA (L.mem s1 (epHeadA ptr)) ∉ K.user :=
    ⟨⟨⟨(ioRS_of_userP hAff).1, hAffP⟩, by unfold VO; rw [hgate, hgate]⟩, fun hu => hAff.2.1 (Or.inl (Or.inl hu))⟩
  have hdA : Aligned (affA (L.mem s1 (epHeadA ptr))) := field_aligned hdA' (by simp) (by simp)
  have hdR : Aligned (replyA (L.mem s1 (epHeadA ptr))) := field_aligned hdA' (by simp) (by simp)
  have hrA : region K.toKLayout (affA (L.mem s1 (epHeadA ptr))) = .tcb (L.mem s1 (epHeadA ptr)) :=
    B.lay.io.tcbw _ hdK 3520#u64 (by simp) (by simp)
  have hnd : ∀ o : U64, o.val < 4288 → affA (L.mem s1 (epHeadA ptr)) ≠ L.nodeAt σ (L.cpu σ) o := by
    intro o ho e
    have h2 : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := B.lay.io.node _ _ (B.inNode o ho)
    rw [← e, hrA] at h2
    cases h2
  have hdT : affA (L.mem s1 (epHeadA ptr)) ≠ ctA (L := L) σ ∧ affA (L.mem s1 (epHeadA ptr)) ≠ cnA (L := L) σ :=
    ⟨hnd _ (by simp [layout.node.CUR_TIME]), hnd _ (by simp [layout.node.CONSUMED])⟩
  -- the memories
  have hRdρ : ∀ b, Rd b → ρ b = L.mem σ b := fun b hb =>
    (hb.2.1.symm.trans (hmm b hb.1.1 (fun hu => hb.1.2.1 (Or.inl (Or.inl hu)))).symm)
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm hx.1.1.2.2
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have hH : ∀ x, (x = ctA (L := L) σ ∨ x = cnA (L := L) σ) → HeldV c hs (ownP K μ x) := by
    intro x hx
    have hnd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → x = L.nodeAt σ (L.cpu σ) o →
        HeldV c hs (ownP K μ x) := by
      rintro o ho h8 rfl
      have hp : L.nodeAt σ (L.cpu σ) o ∉ K.ptes := fun hp =>
        (B'.nd (Locks := Locks) o ho h8).1.2.1 (Or.inr hp)
      rw [ownP_eq_own nv hp]
      have e := own_node (m := μ) (K := userV K.toKLayoutV) B.lay.io (B.inNode o ho)
      show HeldV c hs (OwnMap.own (userV K.toKLayoutV) μ _)
      rw [e]
      exact hc
    rcases hx with rfl | rfl
    · exact hnd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) rfl
    · exact hnd' _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) rfl
  have hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem z)
        (L.mem (L.wr z b v)) := by
    intro z b v hb
    obtain ⟨ha, hsw⟩ := B.dsSafe (st := st) (b := b) hb
    exact stepOK_safeP hK nv hLA ha hsw
  have h := vm_fh_safe (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) (moveHeldP hK) (ownDepP hK hU) hmk hA addr code (hs := hs) (μ := μ) (ρ := ρ) (a := a) hc
    (Rd := Rd) (Ro := Ro) (fun b hb => hb.1.1) hR0 rT rN rC eu F hsl hcap hst hAo hdA hdR hdT hρd hRdρ hRPO
    (Or.inr (hgate μ)) (fun x hx => hV.2.1 x hx) hH hSO
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
