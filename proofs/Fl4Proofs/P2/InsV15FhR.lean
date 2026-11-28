/-
# P2 (line p3mc, gen 49): `InsV15V` at every vmR start — the foreign-receiver branch by the foreign-handler pattern

The vmR starts whose reply names a receiver homed off the core (`RFH`, U13) were left open in gen 48. Their `VSafe9`
certificate (`rr_fh_safe`, P2/RrFhSafe) is `safe_tr_of_states` with the run built inline; its run from one store
state is split out in place this generation (`rr_fh_run`, statement of `rr_fh_safe` unchanged), and the pattern of
P2/InsV15Fh (`insA_narrow_tr_gd`) gives its `InsA` twin.

* **`PathObl.rr_fh_insA`**: the `InsA` twin of `rr_fh_safe` (guard read set: `Rd`, the receiver's `SC`, `AFFINITY`,
  `3432`, `PRIO`, `STATE`, `3376` words; write set: `FAULT_IP`, `CUR_TIME`, `CONSUMED`; all off `G`).
* **`rrDR0_rt`**: every word `RrDR0` names at the dispatch state is region-tagged or kernel-static (`RTW`, the region
  facts of `rrDR0_vn`).
* **`vmR_fh_insA_annV`**: the `InsA` counterpart of `vmR_fh_annV` (P2/RrFhView), read set
  `(IoRS (userP K) ∧ VN) ∧ RTW`, off `PWE K E'` by `rt_notPWE`.
* **`vmR_k0_insAF`**: the vmR body's re-annotation is `InsA` at every view start with action 0 and `RFH` (as
  `vmR_k0_fh`, P2/E2EPU13); **`vmR_insA_annV_all`**: at every vmR start without a VCPU (`vmR_k0_insAH` of gen 48 where
  `¬ RFH`); `VmRPm`, **`insAP_vmR_view`**.

No named premise. Existing file touched: P2/RrFhSafe (`rr_fh_run` split out of `rr_fh_safe`); every existing
statement byte-identical.
-/
import Fl4Proofs.P2.InsV15Fh
import Fl4Proofs.P2.RrFhView
import Fl4Proofs.P2.E2EPU14
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsA narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The VM ReplyRecv body at an entry whose receiver is another core's is `InsA` in its re-annotated form** (the
`InsA` twin of `rr_fh_safe`; module docstring). -/
theorem rr_fh_insA {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b) (hA : P0.ArchTotal ar) {rptr ep : U64}
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} (hc : L.cpu σ = c)
    {R0 Qv Rd : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q)
    (ndσ : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o))
    (rF : Rd (regA (L.curW σ) layout.reg.FAULT_IP)) (rNI : Rd (regA (L.curW σ) layout.reg.NEXT_IP))
    (rFl : Rd (core.num.U64.wrapping_add (L.curW σ) 3456#u64))
    (hmidσ : ∀ v X a2,
      sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2) →
      RdHead (L := L) Rd X (L.cscW X) ∧ RrDR0 (L := L) Rd X (L.curW σ) rptr ep ∧
        L.mem X (rTcbA rptr) = L.mem σ (rTcbA rptr))
    (hex : ∀ v, ∃ X a2, sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2))
    (hu0 : L.mem σ (rTcbA rptr) ≠ 0#u64)
    (hgo : ∀ b, (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
        b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr))) →
      (R0 b ∧ Qv b) ∧ ¬ User b ∧ Aligned b)
    (haS : Aligned (stA (L.mem σ (rTcbA rptr))))
    (haF : Aligned (core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64))
    (huW : affA (L.mem σ (rTcbA rptr)) ≠ regA (L.curW σ) layout.reg.FAULT_IP ∧
      affA (L.mem σ (rTcbA rptr)) ≠ ctA (L := L) σ ∧ affA (L.mem σ (rTcbA rptr)) ≠ cnA (L := L) σ)
    (hρu : ρ (affA (L.mem σ (rTcbA rptr))) ≠ c)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hH : ∀ x, (x = regA (L.curW σ) layout.reg.FAULT_IP ∨ x = ctA (L := L) σ ∨ x = cnA (L := L) σ) →
      HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v)))
    (hRdG : ∀ b, Rd b → ¬ G b)
    (hgoG : ∀ b, (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
        b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr))) → ¬ G b)
    (hSG : ¬ G (stA (L.mem σ (rTcbA rptr))))
    (hFG : ¬ G (core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64))
    (hWG : ∀ b, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) → ¬ G b) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅
        (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) ∅ a)) := by
  have rT : Rd (ctA (L := L) σ) := ndσ _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN : Rd (cnA (L := L) σ) := ndσ _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hAff := hgo _ (Or.inr (Or.inl rfl))
  refine insA_narrow_tr_gd ar hQ hL hO hmk hGo hGko hGU _ hc hGQ
    (Rc := fun b => Rd b ∨ b = affA (L.mem σ (rTcbA rptr)))
    (Rg := fun b => (Rd b ∨ (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
          b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr)))) ∨
          b = stA (L.mem σ (rTcbA rptr)) ∨ b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64)
    (Wd := fun b => b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ)
    (by rintro b (hb | rfl); exacts [hRal b hb, hAff.2.2])
    (by rintro q (hq | rfl); exacts [hR0 q hq, ⟨hAff.1, hAff.2.1⟩])
    (by rintro b ((hb | hb) | rfl | rfl); exacts [hRal b hb, (hgo b hb).2.2, haS, haF])
    (by rintro b ((hb | hb) | rfl | rfl); exacts [hRdG b hb, hgoG b hb, hSG, hFG])
    (fun b hb => Or.inr (hWG b hb))
    (fun x hx => ⟨by rcases hx with rfl | rfl | rfl; exacts [hRal _ rF, hRal _ rT, hRal _ rN], fun _ => hH x hx⟩)
    hRPO hρμ ?_
  intro s sc sk _ hag
  have G0 : Ag st Rd σ s := ⟨sk, sc, fun b hb => (hag b (Or.inl hb)).trans (hRdρ b hb)⟩
  have hoff : L.mem s (affA (L.mem σ (rTcbA rptr))) ≠ c := by rw [hag _ (Or.inr rfl)]; exact hρu
  exact rr_fh_run hA hc (Ro := fun x => R0 x ∧ Qv x) hRal hR0 ndσ rF rNI rFl hmidσ hex hu0
    (fun b hb => ⟨(hgo b hb).1, (hgo b hb).2.1, (hgo b hb).2.2⟩) huW hSO G0 hoff

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg VEq Safe narrowSP PO HeldV InsA InsAP insAP_of_insA insA_narrow)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD vn_of_nf nf_node nf_sc nf_tcb)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section rt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}
variable {A : Type} {ar : machine.Arch A} {Locks : S → U64 → Prop}

theorem rtw_of {K : KLayoutP} {b : U64} {r : OwnMap.Region} (h : region K.toKLayout b = r) (hr : r ≠ .none) :
    RTW K b := Or.inl (by rw [h]; exact hr)

set_option maxHeartbeats 2000000 in
/-- **Every word `RrDR0` names at the dispatch state is region-tagged or kernel-static** (module docstring; the
region facts of `rrDR0_vn`). -/
theorem rrDR0_rt {K : KLayoutP} {rptr ep : U64}
    (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hrR : rptr ∈ Rp) (hpE : H ep = some .ep) (v n : U64) :
    RrDR0 (L := L) (RTW K) (rrX (L := L) s v n) (L.curW s) rptr ep := by
  have B := Q.base
  have hN := B.np
  have hT := B.tp
  have hcT := B.cT
  have hcA := B.tA
  obtain ⟨⟨Qs, Rq, hq⟩, hb, hX, hSg, hS⟩ := B.bxi
  have hO := hX.1
  have hX0 : ScExtra0 st T Cs Scs Nt s := hX.2.2.toScExtra0
  have hcC : L.cpu s ∈ Cs := hq.cur
  have curV : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → RTW K (fld (L.curW s) off) := fun off h1 h2 =>
    rtw_of (B.lay.io.tcbw _ (B.hT _ hcT) off h1 h2) (by simp)
  have scR : ∀ p ∈ Scs, ∀ b, Fl4Proofs.P1.InSC p (Z p) b → region K.toKLayout b = .sc p := fun p hp b hb =>
    B.lay.io.scw p (Z p) (B.hSc p hp) b hb
  have scV : ∀ p ∈ Scs, RefillsWF st s p (Z p) → RdHead (L := L) (RTW K) s p :=
    fun p hp hw => ScAcc.head (W := fun _ => True)
      ⟨fun b _ hb => rtw_of (scR p hp b hb) (by simp), fun _ _ _ => trivial, trivial⟩ hw
  have ksV : ∀ o : U64, o.val < 256 → RTW K (core.num.U64.wrapping_add (L.ksb s) o) := fun o h1 =>
    Or.inr ⟨o, by omega, by rw [← B.kb] <;> rfl⟩
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
  { nd := fun o ho _ => by rw [rrX_nodeAt]; exact rtw_of (B.lay.io.node _ _ (B.inNode o ho)) (by simp)
    dt := by rw [rrX_ksb]; exact ksV _ (by simp [layout.ks.DOMAIN_TIME])
    cd := by rw [rrX_ksb]; exact ksV _ (by simp [layout.ks.CUR_DOMAIN])
    tm := fun h0 => by
      rw [etm] at h0 ⊢
      have hTm := (hX.2.2.tm.min _ hq.cur).resolve_left h0
      have hr : region K.toKLayout (fld (L.mem s (tmA (L := L) s)) Fl4Proofs.P2.OwnMap.oTIMER_DEADLINE) =
          .tcb (L.mem s (tmA (L := L) s)) :=
        B.lay.io.tcbw _ (B.hT _ hTm) 3528#u64 (by simp) (by simp)
      exact rtw_of hr (by simp)
    rh := fun h0 => by
      rw [erh] at h0 ⊢
      obtain ⟨hrT, hscS, hmx⟩ := bxi_rh B.bxi h0
      have e1 : L.mem (rrX (L := L) s v n) (scA (L.mem s (rhA (L := L) s))) =
          L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        rrX_tcb hN hT hcT v n hrT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [e1]
      have hr : region K.toKLayout (scA (L.mem s (rhA (L := L) s))) = .tcb (L.mem s (rhA (L := L) s)) :=
        B.lay.io.tcbw _ (B.hT _ hrT) 3464#u64 (by simp) (by simp)
      exact ⟨rtw_of hr (by simp),
        rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B.bxi hscS) (scV _ hscS (bxi_scin B.bxi hscS hmx).1)⟩
    tSt := curV layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
    tSc := curV 3464#u64 (by simp) (by simp)
    tMx := fun h0 => by
      rw [esct] at h0 ⊢
      rw [← B.hcsc h0]
      have hw := sc_word_in hO B.cscS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact rtw_of (scR _ B.cscS _ hw.2) (by simp)
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
      have nfo : ∀ o : U64, o.val < 64 → o.val % 8 = 0 →
          RTW K (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) o) := by
        intro o ho h8
        have hv : (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) o).val =
            (L.mem s (boundA (L.curW s))).val + o.val := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        have hr : region K.toKLayout (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) o) =
            .ntfn (L.mem s (boundA (L.curW s))) := hreg _ ⟨by rw [hv]; omega, by rw [hv]; omega⟩
        exact rtw_of hr (by simp)
      exact ⟨nfo _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
        nfo _ (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])⟩
    rRt := by
      have h := rTcbA_val0 rptr; have := rp.1; have := rp.2
      exact rtw_of (B.lay.rpw rptr hrK _ ⟨by omega, by omega⟩) (by simp)
    rNx := by
      have h := rNextA_val rp; have := rp.1; have := rp.2
      exact rtw_of (B.lay.rpw rptr hrK _ ⟨by omega, by omega⟩) (by simp)
    eTS := by
      have h := epTSA_val hE; have := hE.fits; have := hE.align
      exact rtw_of (B.lay.epw ep Q.hEp _ ⟨by omega, by omega⟩) (by simp) }

end rt

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's armed VM ReplyRecv program is `InsA` at a view start whose receiver is another core's** (the `InsA`
counterpart of `vmR_fh_annV`; module docstring). -/
theorem vmR_fh_insA_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64} (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {rptr ep : U64} {σ : S} {a : A}
    (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks σ rptr ep)
    (hrR : rptr ∈ Rp) (hpE : H ep = some .ep) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    (hu0 : L.mem σ (rTcbA rptr) ≠ 0#u64) (hρu : ρ (affA (L.mem σ (rTcbA rptr))) ≠ c) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_reply_recv_vm_local (rptr, ep)) ∅ a)) := by
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
  -- the read sets, cut to the region-tagged and kernel-static words
  let Rd : U64 → Prop := fun b => (IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) ∧ RTW K b
  have hR0 : ∀ q, Rd q → (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ q ∧ VO K c ρ q) ∧
      q ∉ K.user := fun q hq' =>
    ⟨⟨⟨(ioRS_of_userP hq'.1.1).1, (ioRS_of_userP hq'.1.1).2⟩, hq'.1.2.2⟩,
      fun hu => hq'.1.1.2.1 (Or.inl (Or.inl hu))⟩
  have ndRg : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) :=
    fun o ho => B.lay.io.node _ _ (B.inNode o ho)
  have ndσ : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact ndRg o ho))⟩,
      rtw_of (ndRg o ho) (by simp)⟩
  have curR : ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
      region K.toKLayout (fld (L.curW σ) off) = .tcb (L.curW σ) := fun off h1 h2 =>
    B.lay.io.tcbw _ (B.hT _ hcT) off h1 h2
  have curV : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → VN K c ρ (fld (L.curW σ) off) ∧
      RTW K (fld (L.curW σ) off) := fun off h1 h2 =>
    ⟨vn_of_nf hK (nf_tcb (curR off h1 h2) hcur), rtw_of (curR off h1 h2) (by simp)⟩
  have regV : ∀ r : U64, r.val < 384 → (VN K c ρ (regA (L.curW σ) r) ∧ RTW K (regA (L.curW σ) r)) ∧
      region K.toKLayout (regA (L.curW σ) r) = .tcb (L.curW σ) := by
    intro r hr
    obtain ⟨k, hk, e⟩ := regA_eq hcA hr
    rw [e]
    have hk' : k.val = 256 + 8 * r.val := hk
    exact ⟨curV k (by omega) (by omega), curR k (by omega) (by omega)⟩
  have hFr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
  have hNr : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
  have rF : Rd (regA (L.curW σ) layout.reg.FAULT_IP) :=
    ⟨⟨(B'.reg (Locks := Locks) hFr).1, (regV _ hFr).1.1⟩, (regV _ hFr).1.2⟩
  have rNI : Rd (regA (L.curW σ) layout.reg.NEXT_IP) :=
    ⟨⟨(B'.reg (Locks := Locks) hNr).1, (regV _ hNr).1.1⟩, (regV _ hNr).1.2⟩
  have rFl : Rd (core.num.U64.wrapping_add (L.curW σ) 3456#u64) :=
    ⟨⟨(B'.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp)
      (by simp [Fl4Proofs.P2.OwnMap.GateField]) (by simp [Fl4Proofs.P2.OwnMap.TimerField])).1,
      (curV 3456#u64 (by simp) (by simp)).1⟩, (curV 3456#u64 (by simp) (by simp)).2⟩
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
    refine ⟨?_, ((rr_dr Q' hrR hpE v n).to0.and (rrDR0_vn hK Q hrR hpE hc hmm B' hcH v n)).and
      (rrDR0_rt Q hrR hpE v n), (rr_uX B hrR v n).1⟩
    rw [rrX_csc hN hcA hcT v n]
    have h1 := rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B'.bxi B'.cscS)
      ((B'.cscacc (Locks := Locks)).head B'.cscwf)
    have h2 := rdHead_rrX (R := VN K c ρ) hN hcA hcT hcC v n (bxi_headOut B.bxi B.cscS)
      (ScAcc.head (W := fun _ => True)
        ⟨fun b _ hb => vn_of_nf hK (nf_sc (B.lay.io.scw _ (Z _) (B.hSc _ B.cscS) b hb) hcH),
          fun _ _ _ => trivial, trivial⟩ B.cscwf)
    have h3 := rdHead_rrX (R := RTW K) hN hcA hcT hcC v n (bxi_headOut B.bxi B.cscS)
      (ScAcc.head (W := fun _ => True)
        ⟨fun b _ hb => rtw_of (B.lay.io.scw _ (Z _) (B.hSc _ B.cscS) b hb) (by simp),
          fun _ _ _ => trivial, trivial⟩ B.cscwf)
    unfold RdHead at h1 h2 h3 ⊢
    exact ⟨⟨⟨h1.1, h2.1⟩, h3.1⟩, ⟨⟨h1.2.1, h2.2.1⟩, h3.2.1⟩, ⟨⟨h1.2.2, h2.2.2⟩, h3.2.2⟩⟩
  -- the receiver
  have huT : L.mem σ (rTcbA rptr) ∈ T := (rr_uX B hrR 0#u64 0#u64).2 hu0
  have huA := B.tp _ huT
  have huK : K.heap (L.mem σ (rTcbA rptr)) = some .tcb := B.hT _ huT
  have uR : ∀ off : U64, 192 ≤ off.val → off.val < 4096 →
      region K.toKLayout (fld (L.mem σ (rTcbA rptr)) off) = .tcb (L.mem σ (rTcbA rptr)) := fun off h1 h2 =>
    B.lay.io.tcbw _ huK off h1 h2
  have hgate : ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
      Fl4Proofs.P2.OwnMap.GateField off.val →
        (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ (fld (L.mem σ (rTcbA rptr)) off) ∧
          VO K c ρ (fld (L.mem σ (rTcbA rptr)) off)) ∧
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
      (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ b ∧ VO K c ρ b) ∧ b ∉ K.user ∧
        Aligned b := by
    rintro b (rfl | rfl | rfl | rfl)
    · exact hgate 3464#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    · exact hgate 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    · exact hgate 3432#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    · exact hgate 3448#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
  have haS : Aligned (stA (L.mem σ (rTcbA rptr))) := field_aligned huA (by rw [st_val]; omega) (by rw [st_val])
  have haF : Aligned (core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64) :=
    field_aligned huA (by simp) (by simp)
  have hrA : region K.toKLayout (affA (L.mem σ (rTcbA rptr))) = .tcb (L.mem σ (rTcbA rptr)) :=
    uR 3520#u64 (by simp) (by simp)
  have hnd : ∀ o : U64, o.val < 4288 → affA (L.mem σ (rTcbA rptr)) ≠ L.nodeAt σ (L.cpu σ) o := by
    intro o ho e
    have h2 := ndRg o ho
    rw [← e, hrA] at h2
    cases h2
  have huW : affA (L.mem σ (rTcbA rptr)) ≠ regA (L.curW σ) layout.reg.FAULT_IP ∧
      affA (L.mem σ (rTcbA rptr)) ≠ ctA (L := L) σ ∧ affA (L.mem σ (rTcbA rptr)) ≠ cnA (L := L) σ := by
    refine ⟨fun e => ?_, hnd _ (by simp [layout.node.CUR_TIME]), hnd _ (by simp [layout.node.CONSUMED])⟩
    have h2 := (regV _ hFr).2
    rw [← e, hrA] at h2
    have h3 : L.mem σ (rTcbA rptr) = L.curW σ := by injection h2
    rw [h3] at hρu
    exact hρu hcur
  -- the paging words of the epoch
  have hnG : ∀ b, region K.toKLayout b ≠ .none → ¬ PWE K E' b := fun b hb hp => hb (pwe_region hK hp)
  have hRdG : ∀ b, Rd b → ¬ PWE K E' b := fun b hb => rt_notPWE hK hb.1.1 hb.2
  have hgoG : ∀ b, (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
      b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr))) →
      ¬ PWE K E' b := by
    rintro b (rfl | rfl | rfl | rfl)
    · exact hnG _ (by rw [show scA (L.mem σ (rTcbA rptr)) = fld (L.mem σ (rTcbA rptr)) 3464#u64 from rfl,
        uR 3464#u64 (by simp) (by simp)]; simp)
    · exact hnG _ (by rw [hrA]; simp)
    · exact hnG _ (by rw [show core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 =
        fld (L.mem σ (rTcbA rptr)) 3432#u64 from rfl, uR 3432#u64 (by simp) (by simp)]; simp)
    · exact hnG _ (by rw [show prioA (L.mem σ (rTcbA rptr)) = fld (L.mem σ (rTcbA rptr)) 3448#u64 from rfl,
        uR 3448#u64 (by simp) (by simp)]; simp)
  have hSG : ¬ PWE K E' (stA (L.mem σ (rTcbA rptr))) :=
    hnG _ (by rw [show stA (L.mem σ (rTcbA rptr)) = fld (L.mem σ (rTcbA rptr)) layout.tcb.STATE from rfl,
      uR layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)]; simp)
  have hFG : ¬ PWE K E' (core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64) :=
    hnG _ (by rw [show core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64 =
      fld (L.mem σ (rTcbA rptr)) 3376#u64 from rfl, uR 3376#u64 (by simp) (by simp)]; simp)
  have hWG : ∀ b, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      ¬ PWE K E' b := by
    rintro b (rfl | rfl | rfl)
    · exact hnG _ (by rw [(regV _ hFr).2]; simp)
    · exact hnG _ (by rw [show ctA (L := L) σ = L.nodeAt σ (L.cpu σ) layout.node.CUR_TIME from rfl,
        ndRg _ (by simp [layout.node.CUR_TIME])]; simp)
    · exact hnG _ (by rw [show cnA (L := L) σ = L.nodeAt σ (L.cpu σ) layout.node.CONSUMED from rfl,
        ndRg _ (by simp [layout.node.CONSUMED])]; simp)
  -- the memories
  have hRdρ : ∀ b, Rd b → ρ b = L.mem σ b := fun b hb =>
    (hb.1.2.1.symm.trans (hmm b hb.1.1.1 (fun hu => hb.1.1.2.1 (Or.inl (Or.inl hu)))).symm)
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user →
      (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ x ∧ VO K c ρ x) →
      PO c hs (ownP K μ x) := by
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
      rw [eown, (regV _ hFr).1.1.2] at h1
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
  exact PathObl.rr_fh_insA (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) hmk (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) hA (rptr := rptr) (ep := ep) (hs := hs) (μ := μ)
    (ρ := ρ) (σ := σ) (a := a) hc (fun b hb => vo_of_pwe hK hb) (fun b hb => hb.1.1.1) hR0 ndσ rF rNI rFl hmidσ hex
    hu0 hgo haS haF huW hρu hRdρ hRPO (fun x hx => hV.2.1 x hx) hH hSO hRdG hgoG hSG hFG hWG

end main

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 4000000 in
/-- **The vmR body's re-annotation is `InsA` at every view start with action 0 whose reply names a receiver homed
off the core** (module docstring; the `InsA` counterpart of `vmR_k0_fh`). -/
theorem vmR_k0_insAF (j : VmRArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : Act0V st K c ρ) (hF : RFH K c ρ j)
    (hS : StartAt (fl4LocW11JA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  by_cases hp : (vmRSlotA st ar hA (masksWr_plain st)).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = (vmRSlotA st ar hA (masksWr_plain st)).path j K.toKLayoutV (view K.toKLayout c ρ) hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      have hpr : VmRPremA st j K.toKLayoutV := hp
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      obtain ⟨⟨hP, -⟩, hq⟩ := id hpre
      have hP' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs j.Cs j.Ω j.Sg
          (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits j.Ac
          j.Locks j.rptr j.ep σ := hP
      have hq' : QPs K st σ := hq
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      obtain ⟨Q, hrR, hpE, -⟩ := VmRRPreJ.pre hP'
      have B := Q.base
      have hact : L.actionW σ = 0#u64 := act_of_view B hq'.ksb hc' hmm h0
      have rp := B.bxi.2.2.1.1.rp j.rptr hrR
      have hrK := Q.hRp j.rptr hrR
      have hrt : IoRS (st := st) (userV K.toKLayoutV) j.Locks σ (rTcbA j.rptr) := by
        have h := rTcbA_val0 j.rptr; have := rp.1; have := rp.2
        exact (B.reply (Locks := j.Locks) hrK (b := rTcbA j.rptr) ⟨by omega, by omega⟩
          (by unfold Aligned; omega) Q.lk.1).1
      have eu : L.mem σ (rTcbA j.rptr) = view K.toKLayout c ρ (rTcbA j.rptr) :=
        hmm _ hrt.1 (fun hu => hrt.2.1 (mem_userV.2 (Or.inl hu)))
      have hLA0 := hpr.bun.choose_spec.ioLayA
      have h := vmR_fh_insA_annV hA (masksWr_plain st) hK hU hpr.nv ⟨hLA0.slot8, hLA0.tcb, hLA0.ntfn8, hLA0.sc8⟩ E'
        hV Q hrR hpE hq' hc' hl' hmm hact (a := a) (by rw [eu]; exact hF.1) (by rw [eu]; exact hF.2)
      convert h using 2
      unfold LocalPath.body
      rw [hc]
      all_goals rfl
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      (SlotU.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) (view K.toKLayout c ρ)) (· ∈ (userV K.toKLayoutV).user))
        (W : NoVcpuRW K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
          (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st))
          (OwnMap.ko_aligned (regionOK_userV hK.base) (userOK_userV hK.base hU.base) (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allA st ar hA (masksWr_plain st) L.total a0 (.vmR j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`vmR_insA_annV_all` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem vmR_insA_annV_all_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : VmRArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.vmR j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  by_cases hF : RFH (S := S) K c ρ j
  · have h' : StartU2 st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.vmR j) := hsf
    have hE := epochPteN_view_of J nv hM hV
    have hS := startAt_UN_C st ar hA (masksWr_plain st) L.total a0 P.run
      (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE (startU_of_U2 st ar hA a0 hC nv h')
    have h0 := vmR_act0_SF_C st ar hA a0 P (hK := hK) (hU := hU) hC nv hsf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact vmR_k0_insAF st ar hA a0 j K hK hU c _ ρ s.mem k E hV h0 hF hS
  · exact vmR_insA_annV_h_C st ar hA a0 P E nv hC J hsf hM hV hF

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every vmR start without a VCPU** (module docstring; gen 48's
`vmR_insA_annV_h` where the reply names no receiver homed off the core). -/
theorem vmR_insA_annV_all (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : VmRArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.vmR j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) :=
  vmR_insA_annV_all_C st ar hA a0 (locPlatCR_of P hIoa) E nv hC J hsf hM hV

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The vmR indices of the PageMap index type. -/
def VmRPm : IxV13Pm S → Prop
  | .inl (.inl (.vmR _)) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`insAP_vmR_view` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insAP_vmR_view_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : VmRPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.vmR j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.vmR j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (vmR_insA_annV_all_C st ar hA a0 P E nv hC J hsf' hM hV)

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every vmR start** (module docstring). -/
theorem insAP_vmR_view (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : VmRPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) :=
  insAP_vmR_view_C st ar hA a0 (locPlatCR_of P hIoa) B E nv hx hC J hM hV hsf

end pm

end
end Fl4Proofs.P2.E2EP
