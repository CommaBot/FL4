/-
# P2 (line p3mc, gen 14): the accepted VM ReplyRecv run's words at a view start, kept by the view (`rr_narA_view`)

At a VM ReplyRecv start state `σ` whose memory is core `c`'s view `view K c ρ` on aligned kernel words (`VmRPre` at
`userV K`), with the receiver `u` homed on `c` in `ρ`, every word of the dispatch-state record `RrAccV`
(P2/AccessVmRR) is, besides readable (`IoRS (userV K)`, `VmRPre.rrAccV`), **not foreign** (`NotForeign`, so kept by
the view with its owner and class owner) or, for the earliest timer's deadline, kept by the view and readable at
`userP K`; every word it writes is moreover writable (`IoWS`), not foreign and deciding no foreign owner (`¬ VDec`):

* `RrNF` / `RrNW`, `RrRv` / `RrWv`: the narrowed read / write sets; `rrRv_nn`, `rrWv_nw`: they lie in U12's
  `NNv`-shape (aligned kernel words, `VN`, readable at `userP` or `VKc`) and in `Aligned ∧ VNW`;
* the objects: the core's node, the kernel words below 256, the ASID words (`hTabR`, in no region), the reply object
  and the endpoint (`nf_obj`), the receiver's `VTABLE` slot (`nf_slot`); the current thread (running at the view,
  `vm_cur_home`) and the receiver (`hρu`) homed; the receiver's SC (homed through its `TCB` back-pointer,
  `vm_sc_home_of_tcb`), the current SC (`hcH`), the release head and its SC (`vm_homes`); the current thread's bound
  notification (its `BOUND_TCB` the current thread, `VmRPre.nbt`); the earliest timer's deadline (`vn_td`);
* **`rr_narA_view`**: `RrAccV Z (RrRv …) (RrWv …)` at every dispatch state `rrX σ v n` under the checks.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.RrAccN
import Fl4Proofs.P2.RrFhView
import Fl4Proofs.P2.VmBView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW GateField TimerField GField)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb TZero)

noncomputable section
open Classical

section sets
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A read of the narrowed run: not foreign, or kept by the view and readable at `userP`. -/
abbrev RrNF (K : KLayoutP) (c : U64) (ρ : U64 → U64) (Locks : S → U64 → Prop) (σ : S) (b : U64) : Prop :=
  NotForeign K.toKLayout c ρ b ∨ (VN K c ρ b ∧ IoRS (st := st) (userP K) Locks σ b)

/-- A write of the narrowed run: not foreign and deciding no foreign owner. -/
abbrev RrNW (K : KLayoutP) (c : U64) (ρ : U64 → U64) (b : U64) : Prop :=
  NotForeign K.toKLayout c ρ b ∧ ¬ VDec K.toKLayout c ρ b

/-- **The narrowed read set.** -/
abbrev RrRv (K : KLayoutP) (c : U64) (ρ : U64 → U64) (Locks : S → U64 → Prop) (σ : S) (b : U64) : Prop :=
  IoRS (st := st) (userV K.toKLayoutV) Locks σ b ∧ RrNF (st := st) K c ρ Locks σ b

/-- **The narrowed write set.** -/
abbrev RrWv (K : KLayoutP) (c : U64) (ρ : U64 → U64) (Locks : S → U64 → Prop) (σ : S) (b : U64) : Prop :=
  IoWS (st := st) (userV K.toKLayoutV) Locks σ b ∧ RrNW K c ρ b

theorem rrRv_nn {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {σ : S}
    {b : U64} (h : RrRv (st := st) K c ρ Locks σ b) :
    Aligned b ∧ b ∉ K.user ∧ VN K c ρ b ∧ (IoRS (st := st) (userP K) Locks σ b ∨ VKc K.toKLayout c ρ b) := by
  refine ⟨h.1.1, fun hu => h.1.2.1 (mem_userV.2 (Or.inl hu)), ?_⟩
  rcases h.2 with h2 | h2
  · exact ⟨vn_of_nf hK h2, Or.inr (vkc_of hK.base.base h2.1)⟩
  · exact ⟨h2.1, Or.inl h2.2⟩

theorem rrWv_nw {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {σ : S}
    {b : U64} (h : RrWv (st := st) K c ρ Locks σ b) : Aligned b ∧ VNW K c ρ b :=
  ⟨h.1.1, vn_of_nf hK h.2.1, vkc_of hK.base.base h.2.1.1, h.2.2⟩

end sets

section pins
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 8000000 in
/-- **`RrAccV` for the narrowed sets at a view start with a homed receiver** (module docstring). -/
theorem rr_narA_view {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {σ : S} {rptr ep : U64}
    (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks σ rptr ep)
    (hP' : VmBase st (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac σ) (hcc : L.cpu σ = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hcH : ρ (fld (L.cscW σ) 16#u64) = c)
    (hTab : RdTab (L := L) (IoRS (st := st) (userV K.toKLayoutV) Locks σ) σ)
    (hTabR : ∀ hi : U64, hi.val < 2048 → region K.toKLayout (atAF (L.ksb σ) hi) = .none ∧
      (L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
        region K.toKLayout (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) = .none))
    {a2 : A} {v n u usc : U64}
    (Pl : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z (rrX (L := L) σ v n) (L.curW σ) rptr ep u usc)
    (C : RRChecksG st ar fl4_abi.consts.fault.VMFault (rrX (L := L) σ v n) a2 (L.curW σ) rptr ep u usc)
    (hAs : AsidOff (L := L) Ω Sg (rrX (L := L) σ v n)) (hρu : ρ (fld u oAFFINITY) = c) :
    RrAccV (L := L) Z (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ) (rrX (L := L) σ v n)
      (L.curW σ) rptr ep u usc := by
  have A1 := Q.rrAccV Pl C hAs hTab (W := IoWS (st := st) (userV K.toKLayoutV) Locks σ) (fun _ _ h => h)
  have B := Q.base
  have hK0 := hK.base.base
  have hN := B.np
  have hT := B.tp
  have hcT := B.cT
  have hcA := B.tA
  obtain ⟨⟨Qs, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B.bxi
  have hX0 : ScExtra0 st T Cs Scs Nt σ := hX.toScExtra0
  have hcC : L.cpu σ ∈ Cs := hq.cur
  have hcur := vm_cur_home hK B hm
  have hu := Pl.hu
  have hut : u ≠ L.curW σ := Pl.hut
  obtain ⟨haff, -⟩ := rr_u_home B Pl C
  -- words of a homed thread
  have tN : ∀ y ∈ T, ρ (fld y oAFFINITY) = c → ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
      NotForeign K.toKLayout c ρ (fld y off) := fun y hy hya off h1 h2 =>
    nf_tcb (B.lay.io.tcbw y (B.hT y hy) off h1 h2) hya
  have tW : ∀ y ∈ T, ρ (fld y oAFFINITY) = c → ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val ≠ 3520 →
      RrNW K c ρ (fld y off) := fun y hy hya off h1 h2 h3 =>
    ⟨tN y hy hya off h1 h2, not_vdec_tcb hK0 (B.lay.io.tcbw y (B.hT y hy) off h1 h2) hya
      (by unfold fld; rw [tcb_wadd_val (hT y hy) h2]; omega)⟩
  have rgW : ∀ y ∈ T, ρ (fld y oAFFINITY) = c → ∀ r : U64, r.val < 384 → RrNW K c ρ (regA y r) := by
    intro y hy hya r hr
    obtain ⟨k, hk, e⟩ := regA_eq (hT y hy) hr
    rw [e]
    have hk' : k.val = 256 + 8 * r.val := hk
    exact tW y hy hya k (by omega) (by omega) (by omega)
  -- an SC homed on `c`
  have scN : ∀ p ∈ Scs, ρ (fld p 16#u64) = c →
      ScAcc (RrNF (st := st) K c ρ Locks σ) (RrNW K c ρ) p (Z p) := by
    intro p hp hpc
    have hr : ∀ b, InSC p (Z p) b → region K.toKLayout b = .sc p := fun b hb' =>
      B.lay.io.scw p (Z p) (B.hSc p hp) b hb'
    obtain ⟨hP, hz⟩ := hO.sc _ hp
    obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    have hin : InSC p (Z p) (core.num.U64.wrapping_add p layout.sc.CONSUMED) :=
      ⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩
    exact ⟨fun b _ hb' => Or.inl (nf_sc (hr b hb') hpc),
      fun b _ hb' => ⟨nf_sc (hr b hb'.inSC) hpc, not_vdec_sc hK0 (hr b hb'.inSC) hpc⟩,
      ⟨nf_sc (hr _ hin) hpc, not_vdec_sc hK0 (hr _ hin) hpc⟩⟩
  have ndR : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := fun o ho => by
    rw [← hcc]; exact B.lay.io.node _ _ (B.inNode o ho)
  have ksN : ∀ o : U64, o.val < 256 → o.val % 8 = 0 →
      NotForeign K.toKLayout c ρ (core.num.U64.wrapping_add (L.ksb σ) o) := by
    intro o h1 h2
    obtain ⟨k8, kf⟩ := B.lay.io.ksf
    have hv : (core.num.U64.wrapping_add (L.ksb σ) o).val = (L.ksb σ).val + o.val := by
      rw [← B.kb]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    refine nf_none (B.lay.io.ks _ ?_ ?_ ?_)
    · unfold Aligned; rw [hv, ← B.kb]; omega
    · rw [hv, ← B.kb]; omega
    · rw [hv, ← B.kb]; omega
  -- `u`'s SC
  have escu : L.mem (rrX (L := L) σ v n) (scA u) = L.mem σ (scA u) :=
    rrX_tcb hN hT hcT v n hu (Kx := 3464#u64) (by simp) (by simp) (fun h => absurd h hut)
  have husc : L.mem σ (scA u) = usc := by rw [← escu]; exact Pl.husc
  have hcore : L.mem σ (scCoreA usc) = L.cpu σ := by
    rw [← husc, B.affSc u hu (by rw [husc]; exact Pl.hsc0), haff]
  have huscH : ρ (fld usc 16#u64) = c := by
    obtain ⟨hcs, htcb, -⟩ := hX.bound u hu (by rw [husc]; exact Pl.hsc0)
    rw [← husc]
    exact vm_sc_home_of_tcb hP' hm hcs (by rw [htcb]; intro e; exact (hT u hu).ne0 (by rw [e]; rfl))
  have hacc := scN usc Pl.hcS huscH
  -- the caller's SC is the current SC
  obtain ⟨b0, hsch0, hb0⟩ := C.sch
  subst hb0
  have hsp := sched.is_schedulable.spec' (L := L) (rrX (L := L) σ v n) (L.curW σ)
  rw [hsch0, WP.spec_ok] at hsp
  obtain ⟨-, hts0, -, -⟩ := hsp rfl
  have esct : L.mem (rrX (L := L) σ v n) (scA (L.curW σ)) = L.mem σ (scA (L.curW σ)) :=
    rrX_tcb hN hT hcT v n hcT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
  have ecsc : L.cscW σ = L.mem σ (scA (L.curW σ)) := B.hcsc (by rw [← esct]; exact hts0)
  -- the reply object and the endpoint
  have rp := Pl.hO.rp rptr Pl.hrR
  have hrK := Q.hRp rptr Pl.hrR
  have rpW : ∀ b, InW rptr 32 b → RrNW K c ρ b := fun b hb' =>
    ⟨nf_obj (B.lay.rpw rptr hrK b hb'), not_vdec_obj hK0 (B.lay.rpw rptr hrK b hb')⟩
  have epW : ∀ b, InW ep 16 b → RrNW K c ρ b := fun b hb' =>
    ⟨nf_obj (B.lay.epw ep Q.hEp b hb'), not_vdec_obj hK0 (B.lay.epw ep Q.hEp b hb')⟩
  have vRt := rTcbA_val0 rptr
  have vNx := rNextA_val rp
  have vPv := rPrevA_val rp
  have vEh := epHeadA_val (ep := ep)
  have vTS := epTSA_val Pl.hE
  have rp1 := rp.1
  have rp2 := rp.2
  have ef := Pl.hE.fits
  have ea := Pl.hE.align
  -- node words
  have etm : L.mem (rrX (L := L) σ v n) (tmA (L := L) (rrX (L := L) σ v n)) = L.mem σ (tmA (L := L) σ) := by
    show L.mem (rrX (L := L) σ v n) (L.nodeAt (rrX (L := L) σ v n) (L.cpu (rrX (L := L) σ v n))
      layout.node.TIMER_MIN) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hcA hcT v n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (rrX (L := L) σ v n) (rhA (L := L) (rrX (L := L) σ v n)) = L.mem σ (rhA (L := L) σ) := by
    show L.mem (rrX (L := L) σ v n) (L.nodeAt (rrX (L := L) σ v n) (L.cpu (rrX (L := L) σ v n))
      layout.node.RELEASE_HEAD) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hcA hcT v n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  have A2 : RrAccV (L := L) Z (RrNF (st := st) K c ρ Locks σ) (RrNW K c ρ) (rrX (L := L) σ v n)
      (L.curW σ) rptr ep u usc := by
    refine
    { nd := fun o ho h8 => by
        rw [rrX_nodeAt]; exact ⟨Or.inl (nf_node (ndR o ho)), nf_node (ndR o ho), not_vdec_node hK0 (ndR o ho)⟩
      dt := by rw [rrX_ksb]; exact Or.inl (ksN _ (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME]))
      cd := by rw [rrX_ksb]; exact Or.inl (ksN _ (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN]))
      kr := by
        unfold krA; rw [rrX_ksb]
        exact Or.inl (ksN _ (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT]))
      tab := ?_
      tSt := Or.inl (tN _ hcT hcur layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega))
      tSc := Or.inl (tN _ hcT hcur 3464#u64 (by simp) (by simp))
      tMx := by
        rw [esct, ← ecsc]
        have hw := sc_word_in hO B.cscS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
          (by simp [layout.sc.REFILL_MAX])
        exact (scN _ B.cscS hcH).rd _ hw.1 hw.2
      tIq := Or.inl (tN _ hcT hcur 3592#u64 (by simp) (by simp))
      tMi := by
        obtain ⟨k, hk, e⟩ := regA_eq hcA (r := layout.reg.MSG_INFO) (lt384 (Or.inr (Or.inr (Or.inr rfl))))
        rw [e]
        have hk' : k.val = 256 + 8 * layout.reg.MSG_INFO.val := hk
        have h1 : layout.reg.MSG_INFO.val < 384 := lt384 (Or.inr (Or.inr (Or.inr rfl)))
        exact Or.inl (tN _ hcT hcur k (by omega) (by omega))
      tBn := Or.inl (tN _ hcT hcur 3368#u64 (by simp) (by simp))
      tPr := Or.inl (tN _ hcT hcur 3448#u64 (by simp) (by simp))
      ntf := ?_
      wRp := tW _ hcT hcur 3360#u64 (by simp) (by simp) (by simp)
      wEn := tW _ hcT hcur 3496#u64 (by simp) (by simp) (by simp)
      wEp := tW _ hcT hcur 3504#u64 (by simp) (by simp) (by simp)
      rRt := Or.inl (rpW _ ⟨by omega, by omega⟩).1
      rNx := Or.inl (rpW _ ⟨by omega, by omega⟩).1
      rPv := Or.inl (rpW _ ⟨by omega, by omega⟩).1
      wNx := rpW _ ⟨by omega, by omega⟩
      wPv := rpW _ ⟨by omega, by omega⟩
      wRt := rpW _ ⟨by omega, by omega⟩
      uSt := Or.inl (tN _ hu hρu layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega))
      uFt := ⟨Or.inl (tN _ hu hρu 3376#u64 (by simp) (by simp)), tW _ hu hρu 3376#u64 (by simp) (by simp) (by simp)⟩
      uSc := Or.inl (tN _ hu hρu 3464#u64 (by simp) (by simp))
      uPr := Or.inl (tN _ hu hρu 3448#u64 (by simp) (by simp))
      uAf := Or.inl (tN _ hu hρu 3520#u64 (by simp) (by simp))
      uDo := Or.inl (tN _ hu hρu 3432#u64 (by simp) (by simp))
      uIq := Or.inl (tN _ hu hρu 3592#u64 (by simp) (by simp))
      uMx := by
        have hw := sc_word_in hO Pl.hcS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
          (by simp [layout.sc.REFILL_MAX])
        exact hacc.rd _ hw.1 hw.2
      uNi := rgW _ hu hρu layout.reg.NEXT_IP (by simp [layout.reg.NEXT_IP])
      uYt := Or.inl (tN _ hu hρu 3472#u64 (by simp) (by simp))
      uFi := Or.inl (rgW _ hu hρu layout.reg.FAULT_IP (by simp [layout.reg.FAULT_IP])).1
      uVt := ?_
      eTS := Or.inl (epW _ ⟨by omega, by omega⟩).1
      wEh := epW _ ⟨by omega, by omega⟩
      wEt := epW _ ⟨by omega, by omega⟩
      spo := by
        have hw := sc_word_in hO Pl.hcS (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
          (by simp [layout.sc.SPORADIC])
        exact hacc.rd _ hw.1 hw.2
      cor := by
        have hw := sc_word_in hO Pl.hcS (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
        exact hacc.rd _ hw.1 hw.2
      ccs := ?_
      uHd := hacc.head Pl.hWF
      uscA := hacc
      csc := by rw [rrX_csc hN hcA hcT v n]; exact scN _ B.cscS hcH
      tm := ?_
      rh := ?_ }
    · -- the ASID words
      intro hi hhi
      have hA1 := hAs hi hhi
      rw [rrX_ksb] at hA1 ⊢
      have e : L.mem (rrX (L := L) σ v n) (atAF (L.ksb σ) hi) = L.mem σ (atAF (L.ksb σ) hi) :=
        rrX_out hN hcA hcT hcC v n (hq.omega _ hA1.1)
      rw [e]
      obtain ⟨r1, rp'⟩ := hTabR hi hhi
      exact ⟨Or.inl (nf_none r1), fun lo hlo h0 => Or.inl (nf_none (rp' h0 lo hlo))⟩
    · -- the bound notification
      intro nn hnn hne
      have hv := obj.Tcb.bound_ntfn.val (L := L) (rrX (L := L) σ v n) (L.curW σ)
      rw [hnn, WP.spec_ok] at hv
      subst hv
      have eb : L.mem (rrX (L := L) σ v n) (boundA (L.curW σ)) = L.mem σ (boundA (L.curW σ)) :=
        rrX_tcb hN hT hcT v n hcT (Kx := 3368#u64) (by simp) (by simp) (fun _ => by simp)
      have h0 : L.mem σ (boundA (L.curW σ)) ≠ 0#u64 := by rw [← eb]; exact bne_iff_ne.mp hne
      rw [eb]
      have hnN := hX0.bnd (L.curW σ) hcT h0
      obtain ⟨-, h64, hfit, hreg⟩ := Q.hNt _ hnN
      have hbt := Q.nbt h0
      have nfo : ∀ o : U64, o.val < 64 → o.val % 8 = 0 →
          NotForeign K.toKLayout c ρ (core.num.U64.wrapping_add (L.mem σ (boundA (L.curW σ))) o) := by
        intro o ho h8
        have hv : (core.num.U64.wrapping_add (L.mem σ (boundA (L.curW σ))) o).val =
            (L.mem σ (boundA (L.curW σ))).val + o.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        have hr : region K.toKLayout (core.num.U64.wrapping_add (L.mem σ (boundA (L.curW σ))) o) =
            .ntfn (L.mem σ (boundA (L.curW σ))) := hreg _ ⟨by rw [hv]; omega, by rw [hv]; omega⟩
        have hv24 : (fld (L.mem σ (boundA (L.curW σ))) 24#u64).val = (L.mem σ (boundA (L.curW σ))).val + 24 := by
          unfold fld; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        have hr24 : region K.toKLayout (fld (L.mem σ (boundA (L.curW σ))) 24#u64) =
            .ntfn (L.mem σ (boundA (L.curW σ))) := hreg _ ⟨by rw [hv24]; omega, by rw [hv24]; omega⟩
        have ha24 : Aligned (fld (L.mem σ (boundA (L.curW σ))) 24#u64) := by unfold Aligned; rw [hv24]; omega
        have hu24 : fld (L.mem σ (boundA (L.curW σ))) 24#u64 ∉ K.user := fun hu' =>
          B.region_kernel (Or.inl (by
            have hr' : region (userV K.toKLayoutV) (fld (L.mem σ (boundA (L.curW σ))) 24#u64) =
              .ntfn (L.mem σ (boundA (L.curW σ))) := hr24
            rw [hr']; simp)) (mem_userV.2 (Or.inl hu'))
        have e24 : ρ (fld (L.mem σ (boundA (L.curW σ))) 24#u64) = L.curW σ := by
          rw [← view_ntfn (K := K.toKLayout) (c := c) (m := ρ) hr24, ← hm _ ha24 hu24]; exact hbt
        refine ⟨fun t h => ?_, fun p h => ?_, fun d h => ?_, fun p h _ => ?_⟩ <;> rw [hr] at h <;> cases h
        rw [e24]; exact hcur
      exact ⟨Or.inl (nfo _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])),
        Or.inl (nfo _ (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]))⟩
    · -- the receiver's `VTABLE` slot
      obtain ⟨hsl1, -⟩ := B.lay.io.tslot _ (B.hT _ hu) layout.tcb.SLOT_VTABLE (vtA u)
        (tcb_slot_eq u layout.tcb.SLOT_VTABLE) (by simp [layout.tcb.SLOT_VTABLE])
      obtain ⟨h8, hf⟩ := B.lay.io.slot8 (vtA u) hsl1
      have hv : (core.num.U64.wrapping_add (vtA u) 8#u64).val = (vtA u).val + 8 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      exact ⟨Or.inl (nf_slot (B.lay.io.slotw (vtA u) hsl1 (vtA u) ⟨le_refl _, by omega⟩)),
        Or.inl (nf_slot (B.lay.io.slotw (vtA u) hsl1 _ ⟨by omega, by omega⟩))⟩
    · -- the current SC word of `usc`'s core: this node's
      have hw := sc_word_in hO Pl.hcS (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
      have eo : OutsideObjs st T Cs σ (scCoreA usc) :=
        (Pl.hΩ _ (Pl.hSg.sub _ (Pl.scSg _ hw.1 hw.2))).ksb (rrX_ksb σ v n).symm
      have e1 : L.mem (rrX (L := L) σ v n) (core.num.U64.wrapping_add usc layout.sc.CORE) =
          L.cpu (rrX (L := L) σ v n) := by
        rw [rrX_cpu]; exact (rrX_out hN hcA hcT hcC v n eo).trans hcore
      rw [e1, rrX_nodeAt]
      exact Or.inl (nf_node (ndR _ (by simp [layout.node.CUR_SC])))
    · -- the earliest timer's deadline
      intro h0
      rw [etm] at h0 ⊢
      have hTm := (hX.tm.min _ hq.cur).resolve_left h0
      obtain ⟨hd, -⟩ := B.tmc h0
      have hr : region K.toKLayout (fld (L.mem σ (tmA (L := L) σ)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
          .tcb (L.mem σ (tmA (L := L) σ)) :=
        B.lay.io.tcbw _ (B.hT _ hTm) 3528#u64 (by simp) (by simp)
      have ho : (fld (L.mem σ (tmA (L := L) σ)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE).val -
          (L.mem σ (tmA (L := L) σ)).val = 3528 := by
        unfold fld; rw [tcb_wadd_val (B.tp _ hTm) (by simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE])]
        simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE]
      have e1 := view_keep_tcb (c := c) (m := ρ) hr (by omega) (by unfold TZero; omega) (by omega)
      have hm' : L.mem σ (fld (L.mem σ (tmA (L := L) σ)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
          view K.toKLayout c ρ (fld (L.mem σ (tmA (L := L) σ)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) :=
        hm _ (field_aligned (B.tp _ hTm) (by simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE])
          (by simp [Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE])) (fun hu' =>
          B.region_kernel (Or.inl (fun h => by
            have h' : region (userV K.toKLayoutV)
              (fld (L.mem σ (tmA (L := L) σ)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) = .none := h
            have hr' : region (userV K.toKLayoutV)
              (fld (L.mem σ (tmA (L := L) σ)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
              .tcb (L.mem σ (tmA (L := L) σ)) := hr
            rw [hr'] at h'; cases h')) (mem_userV.2 (Or.inl hu')))
      exact Or.inr ⟨vn_td hK (B.hT _ hTm) (by rw [← e1, ← hm']; exact hd), hP'.td (Locks := Locks) h0⟩
    · -- the release head and its SC
      intro h0
      rw [erh] at h0 ⊢
      obtain ⟨hrT, hscS, hmx⟩ := bxi_rh B.bxi h0
      have e1 : L.mem (rrX (L := L) σ v n) (scA (L.mem σ (rhA (L := L) σ))) =
          L.mem σ (scA (L.mem σ (rhA (L := L) σ))) :=
        rrX_tcb hN hT hcT v n hrT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [e1]
      obtain ⟨ha, hsa⟩ := (vm_homes hP' hm).2 h0
      have hacc' := scN _ hscS hsa
      exact ⟨Or.inl (tN _ hrT ha 3464#u64 (by simp) (by simp)), hacc'.rd,
        rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B.bxi hscS) (hacc'.head (bxi_scin B.bxi hscS hmx).1)⟩
  exact RrAccV.and A1 A2

end pins

end
end Fl4Proofs.P2.E2EP
