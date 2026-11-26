/-
# P2 (line p3mc, gen 13): U9's re-annotated VM ReplyRecv body is `Safe` at a view start whose receiver is another core's

The decline split for vmR at core `c`'s view `view K c ρ` (the counterpart of `VmFhView.vmF_fh_annV`): at a start
state `σ` of the VM ReplyRecv path (`VmRPre (userV K)`, the reply and endpoint typed, `QPs`, memory the view on
aligned kernel words, core `c`) with action `RESUME_CURRENT` (0) whose reply object names a receiver `u ≠ 0` with
`ρ (AFFINITY u) ≠ c`, U9's armed program `narrowSP cls (ko K μ) c (VO K c ρ) ∅ (body σ a)` is `Safe` at the
physical memory `μ` (`VEq ρ μ`):

* pins: `vm_cur_home` (the current thread is homed on `c` in `ρ`: its state at the view is running or restart,
  `view_hidden_home`), `view_ntfn` (the view keeps notification words), `nf_ntfn_cur` (a word of the current thread's
  bound notification is not foreign), **`rrDR0_vn`** (the `VN` half of `RrDR0` at the dispatch state);
* **`vmR_fh_annV`**: `PathObl.rr_fh_safe` with `Rd := IoRS (userP K) ∧ VN`, `Ro := rsE ptes (IoRS (userV K)) ∧ VO`,
  then `E2E.safe_narrow_tr`. The prefix's `FAULT_IP` write is held at `μ`: writable at the view, its owner kept by
  the view (`VN`) and by `VEq`.

No premise: every fact is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.RrFhSafe
import Fl4Proofs.P2.VmFhView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td view_keep_tcb
  view_sctcb_home view_tzero_home view_hidden_home Hidden)

noncomputable section
open Classical

/-- The view keeps every notification word. -/
theorem view_ntfn {K : KLayout} {c : U64} {m : U64 → U64} {b p : U64} (hr : region K b = .ntfn p) :
    view K c m b = m b :=
  CoreView.view_none (by simp [CoreView.repl, CoreView.repl2, hr])

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

/-- **The current thread is homed on `c`** (`io_homes`' first clause for `VmBase`). -/
theorem vm_cur_home {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64}
    (P : VmBase st (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) :
    ρ (fld (L.curW s) oAFFINITY) = c := by
  have hK0 := hK.base.base
  have e : fld (L.curW s) OwnMap.oSTATE = stA (L.curW s) := UScalar.eq_of_val_eq (by
    unfold fld stA
    rw [tcb_wadd_val P.tA (by rw [OwnMap.oSTATE_val]; omega), tcb_wadd_val P.tA (by rw [st_val]; omega),
      OwnMap.oSTATE_val, st_val])
  have ha : Aligned (stA (L.curW s)) := field_aligned P.tA (by rw [st_val]; omega) (by rw [st_val])
  have hu : stA (L.curW s) ∉ K.user := fun hu =>
    P.region_kernel (Or.inl (by
      have e2 := P.lay.io.tcbw _ (P.hT _ P.cT) layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
      unfold fld at e2; unfold stA; rw [e2]; simp)) (mem_userV.2 (Or.inl hu))
  refine view_hidden_home hK0 (P.hT _ P.cT) ?_
  rw [e, ← hm _ ha hu]
  rcases P.run with h | h <;> rw [h] <;> simp [Hidden, sched.TS_RESTART, sched.TS_RUNNING]

variable {A : Type} {ar : machine.Arch A} {Locks : S → U64 → Prop}

set_option maxHeartbeats 2000000 in
/-- **The `VN` half of `RrDR0` at the dispatch state** (module docstring), the current SC homed on `c`. -/
theorem rrDR0_vn {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {rptr ep : U64}
    (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hrR : rptr ∈ Rp) (hpE : H ep = some .ep) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    (hP' : VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcH : ρ (fld (L.cscW s) 16#u64) = c) (v n : U64) :
    RrDR0 (L := L) (VN K c ρ) (rrX (L := L) s v n) (L.curW s) rptr ep := by
  have B := Q.base
  have hK0 := hK.base.base
  have hN := B.np
  have hT := B.tp
  have hcT := B.cT
  have hcA := B.tA
  obtain ⟨⟨Qs, Rq, hq⟩, hb, hX, hSg, hS⟩ := B.bxi
  have hO := hX.1
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hcC : L.cpu s ∈ Cs := hq.cur
  have hcur := vm_cur_home hK B hm
  obtain ⟨-, hrh⟩ := vm_homes hP' hm
  have curV : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → VN K c ρ (fld (L.curW s) off) := fun off h1 h2 =>
    vn_of_nf hK (nf_tcb (B.lay.io.tcbw _ (B.hT _ hcT) off h1 h2) hcur)
  have ndR : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node c := fun o ho => by
    rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)
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
  have esct : L.mem (rrX (L := L) s v n) (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    rrX_tcb hN hT hcT v n hcT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
  have etm : L.mem (rrX (L := L) s v n) (tmA (L := L) (rrX (L := L) s v n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (rrX (L := L) s v n) (L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n))
      layout.node.TIMER_MIN) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hcA hcT v n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (rrX (L := L) s v n) (rhA (L := L) (rrX (L := L) s v n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (rrX (L := L) s v n) (L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n))
      layout.node.RELEASE_HEAD) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hcA hcT v n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  have rp := hO.rp rptr hrR
  have hrK := Q.hRp rptr hrR
  have hE := vm_epP B.bxi hpE
  refine
  { nd := fun o ho _ => by rw [rrX_nodeAt]; exact vn_of_nf hK (nf_node (ndR o ho))
    dt := by rw [rrX_ksb]; exact ksV _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    cd := by rw [rrX_ksb]; exact ksV _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
    tm := fun h0 => by
      rw [etm] at h0 ⊢
      have hTm := (hX.2.2.tm.min _ hq.cur).resolve_left h0
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
            have h' : region (userV K.toKLayoutV)
              (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) = .none := h
            have hr' : region (userV K.toKLayoutV)
              (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
              .tcb (L.mem s (tmA (L := L) s)) := hr
            rw [hr'] at h'; cases h')) (mem_userV.2 (Or.inl hu)))
      exact vn_td hK (B.hT _ hTm) (by rw [← e1, ← hm']; exact hd)
    rh := fun h0 => by
      rw [erh] at h0 ⊢
      obtain ⟨hrT, hscS, hmx⟩ := bxi_rh B.bxi h0
      have e1 : L.mem (rrX (L := L) s v n) (scA (L.mem s (rhA (L := L) s))) =
          L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        rrX_tcb hN hT hcT v n hrT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [e1]
      obtain ⟨ha, hsa⟩ := hrh h0
      have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
        B.lay.io.tcbw _ (B.hT _ hrT) 3464#u64 (by simp) (by simp)
      exact ⟨vn_of_nf hK (nf_tcb hr ha),
        rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B.bxi hscS) (scV _ hscS hsa (bxi_scin B.bxi hscS hmx).1)⟩
    tSt := curV layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
    tSc := curV 3464#u64 (by simp) (by simp)
    tMx := fun h0 => by
      rw [esct] at h0 ⊢
      rw [← B.hcsc h0]
      have hw := sc_word_in hO B.cscS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact vn_of_nf hK (nf_sc (scR _ B.cscS _ hw.2) hcH)
    tIq := curV 3592#u64 (by simp) (by simp)
    tMi := by
      obtain ⟨k, hk, e⟩ := regA_eq hcA (r := layout.reg.MSG_INFO) (lt384 (Or.inr (Or.inr (Or.inr rfl))))
      rw [e]
      have hk' : k.val = 256 + 8 * layout.reg.MSG_INFO.val := hk
      have h1 : layout.reg.MSG_INFO.val < 384 := lt384 (Or.inr (Or.inr (Or.inr rfl)))
      exact curV k (by omega) (by omega)
    tBn := curV 3368#u64 (by simp) (by simp)
    tPr := curV 3448#u64 (by simp) (by simp)
    ntf := fun h0 => by
      have eb : L.mem (rrX (L := L) s v n) (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
        rrX_tcb hN hT hcT v n hcT (Kx := 3368#u64) (by simp) (by simp) (fun _ => by simp)
      rw [eb] at h0 ⊢
      have hnN := hX0.bnd (L.curW s) hcT h0
      obtain ⟨-, h64, hfit, hreg⟩ := Q.hNt _ hnN
      have hbt := Q.nbt h0
      have nfo : ∀ o : U64, o.val < 64 → o.val % 8 = 0 →
          VN K c ρ (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) o) := by
        intro o ho h8
        have hv : (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) o).val =
            (L.mem s (boundA (L.curW s))).val + o.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        have hr : region K.toKLayout (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) o) =
            .ntfn (L.mem s (boundA (L.curW s))) := hreg _ ⟨by rw [hv]; omega, by rw [hv]; omega⟩
        have hv24 : (fld (L.mem s (boundA (L.curW s))) 24#u64).val = (L.mem s (boundA (L.curW s))).val + 24 := by
          unfold fld; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        have hr24 : region K.toKLayout (fld (L.mem s (boundA (L.curW s))) 24#u64) =
            .ntfn (L.mem s (boundA (L.curW s))) := hreg _ ⟨by rw [hv24]; omega, by rw [hv24]; omega⟩
        have ha24 : Aligned (fld (L.mem s (boundA (L.curW s))) 24#u64) := by unfold Aligned; rw [hv24]; omega
        have hu24 : fld (L.mem s (boundA (L.curW s))) 24#u64 ∉ K.user := fun hu =>
          B.region_kernel (Or.inl (by
            have hr' : region (userV K.toKLayoutV) (fld (L.mem s (boundA (L.curW s))) 24#u64) =
              .ntfn (L.mem s (boundA (L.curW s))) := hr24
            rw [hr']; simp)) (mem_userV.2 (Or.inl hu))
        have e24 : ρ (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s := by
          rw [← view_ntfn (K := K.toKLayout) (c := c) (m := ρ) hr24, ← hm _ ha24 hu24]; exact hbt
        refine vn_of_nf hK ⟨fun t h => ?_, fun p h => ?_, fun d h => ?_, fun p h _ => ?_⟩ <;> rw [hr] at h <;>
          cases h
        rw [e24]; exact hcur
      exact ⟨nfo _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
        nfo _ (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])⟩
    rRt := by
      have h := rTcbA_val0 rptr; have := rp.1; have := rp.2
      exact vn_of_nf hK (nf_obj (B.lay.rpw rptr hrK _ ⟨by omega, by omega⟩))
    rNx := by
      have h := rNextA_val rp; have := rp.1; have := rp.2
      exact vn_of_nf hK (nf_obj (B.lay.rpw rptr hrK _ ⟨by omega, by omega⟩))
    eTS := by
      have h := epTSA_val hE; have := hE.fits; have := hE.align
      exact vn_of_nf hK (nf_obj (B.lay.epw ep Q.hEp _ ⟨by omega, by omega⟩)) }

end

/-! ## The re-annotated body at a view start whose receiver is another core's -/

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's armed VM ReplyRecv program is `Safe` at a view start whose receiver is another core's** (module
docstring). -/
theorem vmR_fh_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {rptr ep : U64} {σ : S} {a : A}
    (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks σ rptr ep)
    (hrR : rptr ∈ Rp) (hpE : H ep = some .ep) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    (hu0 : L.mem σ (rTcbA rptr) ≠ 0#u64) (hρu : ρ (affA (L.mem σ (rTcbA rptr))) ≠ c) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_reply_recv_vm_local (rptr, ep)) ∅ a)) := by
  have hK0 := hK.base.base
  have Q' : VmRPre st ar (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks σ rptr ep := vmRPre_userP hK hq.ks Q
  have B := Q.base
  have B' := Q'.base
  have hN := B.np
  have hcT := B.cT
  have hcA := B.tA
  have hcC : L.cpu σ ∈ Cs := by obtain ⟨⟨Qs, Rq, hq'⟩, -, -, -, -⟩ := B.bxi; exact hq'.cur
  have hsc0 : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := B.bxi.2.1.resume hact
  have hcH : ρ (fld (L.cscW σ) 16#u64) = c := (vm_homes B' hmm).1 hsc0
  have hcur := vm_cur_home hK B hmm
  -- the read sets
  let Rd : U64 → Prop := fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b
  let Ro : U64 → Prop := fun b => rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ b ∧ VO K c ρ b
  have hR0 : ∀ q, Rd q → Ro q ∧ q ∉ K.user := fun q hq' =>
    ⟨⟨⟨(ioRS_of_userP hq'.1).1, (ioRS_of_userP hq'.1).2⟩, hq'.2.2⟩, fun hu => hq'.1.2.1 (Or.inl (Or.inl hu))⟩
  have ndσ : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)))⟩
  have curV : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → VN K c ρ (fld (L.curW σ) off) := fun off h1 h2 =>
    vn_of_nf hK (nf_tcb (B.lay.io.tcbw _ (B.hT _ hcT) off h1 h2) hcur)
  have regV : ∀ r : U64, r.val < 384 → VN K c ρ (regA (L.curW σ) r) := by
    intro r hr
    obtain ⟨k, hk, e⟩ := regA_eq hcA hr
    rw [e]
    have hk' : k.val = 256 + 8 * r.val := hk
    exact curV k (by omega) (by omega)
  have hFr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
  have hNr : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
  have rF : Rd (regA (L.curW σ) layout.reg.FAULT_IP) := ⟨(B'.reg (Locks := Locks) hFr).1, regV _ hFr⟩
  have rNI : Rd (regA (L.curW σ) layout.reg.NEXT_IP) := ⟨(B'.reg (Locks := Locks) hNr).1, regV _ hNr⟩
  have rFl : Rd (core.num.U64.wrapping_add (L.curW σ) 3456#u64) :=
    ⟨(B'.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp)
      (by simp [Fl4Proofs.P2.OwnMap.GateField]) (by simp [Fl4Proofs.P2.OwnMap.TimerField])).1,
      curV 3456#u64 (by simp) (by simp)⟩
  -- the dispatch states
  have hpre : ∀ v X a2,
      sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2) →
      ∃ n, X = rrX (L := L) σ v n := by
    intro v X a2 eu
    have hN1 : NodePlaced st T (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v)
        (L.cpu (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v)) := by
      rw [LawfulStore.cpu_wr]; exact hN.wr
    obtain ⟨⟨n, a3⟩, hn, -⟩ := spec_ex_fd (hA.now a)
    rw [update_timestamp_ok ar hN1 hn] at eu
    exact ⟨n, (Prod.mk.inj (ok_inj_ff eu)).1.symm⟩
  have hex : ∀ v, ∃ X a2,
      sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2) := by
    intro v
    have hN1 : NodePlaced st T (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v)
        (L.cpu (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v)) := by
      rw [LawfulStore.cpu_wr]; exact hN.wr
    obtain ⟨⟨n, a3⟩, hn, -⟩ := spec_ex_fd (hA.now a)
    exact ⟨_, _, update_timestamp_ok ar hN1 hn⟩
  have hmidσ : ∀ v X a2,
      sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2) →
      RdHead (L := L) Rd X (L.cscW X) ∧ RrDR0 (L := L) Rd X (L.curW σ) rptr ep ∧
        L.mem X (rTcbA rptr) = L.mem σ (rTcbA rptr) := by
    intro v X a2 eu
    obtain ⟨n, rfl⟩ := hpre v X a2 eu
    refine ⟨?_, (rr_dr Q' hrR hpE v n).to0.and (rrDR0_vn hK Q hrR hpE hc hmm B' hcH v n), (rr_uX B hrR v n).1⟩
    rw [rrX_csc hN hcA hcT v n]
    have h1 := rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B'.bxi B'.cscS)
      ((B'.cscacc (Locks := Locks)).head B'.cscwf)
    have h2 := rdHead_rrX (R := VN K c ρ) hN hcA hcT hcC v n (bxi_headOut B.bxi B.cscS)
      (ScAcc.head (W := fun _ => True)
        ⟨fun b _ hb => vn_of_nf hK (nf_sc (B.lay.io.scw _ (Z _) (B.hSc _ B.cscS) b hb) hcH),
          fun _ _ _ => trivial, trivial⟩ B.cscwf)
    unfold RdHead at h1 h2 ⊢
    exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
  -- the receiver
  have huT : L.mem σ (rTcbA rptr) ∈ T := (rr_uX B hrR 0#u64 0#u64).2 hu0
  have huA := B.tp _ huT
  have huK : K.heap (L.mem σ (rTcbA rptr)) = some .tcb := B.hT _ huT
  have hgate : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
      Fl4Proofs.P2.OwnMap.GateField off.val → Ro (fld (L.mem σ (rTcbA rptr)) off) ∧
        fld (L.mem σ (rTcbA rptr)) off ∉ K.user ∧ Aligned (fld (L.mem σ (rTcbA rptr)) off) := by
    intro off h1 h2 h8 hg
    have hI := B'.gate (Locks := Locks) huT h1 h2 h8 hg
    have hP := (ioRS_of_userP hI).2
    have hgm : ∀ m, ownP K m (fld (L.mem σ (rTcbA rptr)) off) = .gate := fun m => by
      rw [ownP_eq_own nv hP]
      exact own_tcb_gate (K := userV K.toKLayoutV) B.lay.io huK huA h1 h2 hg
    exact ⟨⟨⟨(ioRS_of_userP hI).1, hP⟩, by unfold VO; rw [hgm, hgm]⟩, fun hu => hI.2.1 (Or.inl (Or.inl hu)), hI.1⟩
  have hgo : ∀ b, (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
      b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr))) →
      Ro b ∧ b ∉ K.user ∧ Aligned b := by
    rintro b (rfl | rfl | rfl | rfl)
    · exact hgate 3464#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    · exact hgate 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    · exact hgate 3432#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    · exact hgate 3448#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
  have haS : Aligned (stA (L.mem σ (rTcbA rptr))) := field_aligned huA (by rw [st_val]; omega) (by rw [st_val])
  have haF : Aligned (core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64) :=
    field_aligned huA (by simp) (by simp)
  have hrA : region K.toKLayout (affA (L.mem σ (rTcbA rptr))) = .tcb (L.mem σ (rTcbA rptr)) :=
    B.lay.io.tcbw _ huK 3520#u64 (by simp) (by simp)
  have hnd : ∀ o : U64, o.val < 4288 → affA (L.mem σ (rTcbA rptr)) ≠ L.nodeAt σ (L.cpu σ) o := by
    intro o ho e
    have h2 : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := B.lay.io.node _ _ (B.inNode o ho)
    rw [← e, hrA] at h2
    cases h2
  have huW : affA (L.mem σ (rTcbA rptr)) ≠ regA (L.curW σ) layout.reg.FAULT_IP ∧
      affA (L.mem σ (rTcbA rptr)) ≠ ctA (L := L) σ ∧ affA (L.mem σ (rTcbA rptr)) ≠ cnA (L := L) σ := by
    refine ⟨fun e => ?_, hnd _ (by simp [layout.node.CUR_TIME]), hnd _ (by simp [layout.node.CONSUMED])⟩
    obtain ⟨k, hk, ek⟩ := regA_eq hcA hFr
    have hk' : k.val = 256 + 8 * layout.reg.FAULT_IP.val := hk
    have h2 : region K.toKLayout (regA (L.curW σ) layout.reg.FAULT_IP) = .tcb (L.curW σ) := by
      rw [ek]; exact B.lay.io.tcbw _ (B.hT _ hcT) k (by omega) (by omega)
    rw [← e, hrA] at h2
    have h3 : L.mem σ (rTcbA rptr) = L.curW σ := by injection h2
    rw [h3] at hρu
    exact hρu hcur
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
  have hH : ∀ x, (x = regA (L.curW σ) layout.reg.FAULT_IP ∨ x = ctA (L := L) σ ∨ x = cnA (L := L) σ) →
      HeldV c hs (ownP K μ x) := by
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
    rcases hx with rfl | rfl | rfl
    · have hI := (B'.reg (Locks := Locks) hFr).1
      have hW := (B.reg (Locks := Locks) hFr).2.2
      have hp := (ioRS_of_userP hI).2
      have h1 : HeldV c hs (ownP K (L.mem σ) (regA (L.curW σ) layout.reg.FAULT_IP)) := by
        rw [ownP_eq_own nv hp, ← hc, ← hl]
        unfold WPerm at hW
        show HeldV (L.cpu σ) (Locks σ)
          (OwnMap.own (userV K.toKLayoutV) (L.mem σ) (regA (L.curW σ) layout.reg.FAULT_IP))
        revert hW
        cases OwnMap.own (userV K.toKLayoutV) (L.mem σ) (regA (L.curW σ) layout.reg.FAULT_IP) <;> exact id
      rw [eown, (regV _ hFr).2] at h1
      rw [hV.1 _ (Or.inl h1)]
      exact h1
    · exact hnd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) rfl
    · exact hnd' _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) rfl
  have hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem z)
        (L.mem (L.wr z b v)) := by
    intro z b v hb
    obtain ⟨ha, hsw⟩ := B.dsSafe (st := st) (b := b) hb
    exact stepOK_safeP hK nv hLA ha hsw
  have h := rr_fh_safe (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) (moveHeldP hK) (ownDepP hK hU) hmk hA (rptr := rptr) (ep := ep) (hs := hs) (μ := μ)
    (ρ := ρ) (σ := σ) (a := a) hc (Rd := Rd) (Ro := Ro) (fun b hb => hb.1.1) hR0 ndσ rF rNI rFl hmidσ hex hu0
    hgo haS haF huW hρu hRdρ hRPO (fun x hx => hV.2.1 x hx) hH hSO
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

end main

end
end Fl4Proofs.P2.E2EP
