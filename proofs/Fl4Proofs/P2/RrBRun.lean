/-
# P2 (line p3mc, gen 14): the VM ReplyRecv run at a view start with a homed receiver, on the view's words (`rrB_run`)

At a VM ReplyRecv start state `σ` at core `c`'s view (`VmRPre (userV K)`, the reply and endpoint typed, `RdTab`,
`QPs`, the view's kernel words, action `RESUME_CURRENT`) whose reply object names no receiver or one homed on `c`
in `ρ` (`hH`), the run from `σ` is the run on a guarded store `guard st Rd Wr` whose reads are aligned kernel words
the view keeps (`VN`), readable at `σ` (`userP`) or of an unchanged class owner (`VKc`), and whose writes are `VNW`
(the counterpart of `vmB_run`, P2/VmBRun):
* accepted: `rr_accR` (P2/RrAccN) with `Rd := RrRv`, `Wr := RrWv` and the record `rr_narA_view` (P2/RrBView); the
  checks' receiver is the reply's `TCB` word, nonzero, so homed by `hH`; its and the current thread's `STATE` /
  `BLOCK_OBJ` writes are in `RrWv`;
* declined: `rr_local_guard_dec` on `IoRS (userP K) ∧ VN`: `RrDR` is `rr_dr` (readable) met with `RrDR0`'s `VN`
  half (`rrDR0_vn`) and the receiver clauses for a homed receiver (`RrDR.of0`); the off-core clause is void, as at
  the view every heap thread's `AFFINITY` is `c` (`view_aff`).

Also `RrDR.andV` (`RrDR` for two sets gives `RrDR` for their meet). No premise. No existing statement changed.
-/
import Fl4Proofs.P2.RrBView
import Fl4Proofs.P2.AccessVmRRM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`RrDR` for two sets gives `RrDR` for their meet.** -/
theorem RrDR.andV {R1 R2 : U64 → Prop} {X : S} {t rptr ep : U64} (D1 : RrDR (L := L) R1 X t rptr ep)
    (D2 : RrDR (L := L) R2 X t rptr ep) : RrDR (L := L) (fun b => R1 b ∧ R2 b) X t rptr ep where
  nd o h1 h2 := ⟨D1.nd o h1 h2, D2.nd o h1 h2⟩
  dt := ⟨D1.dt, D2.dt⟩
  cd := ⟨D1.cd, D2.cd⟩
  tm h := ⟨D1.tm h, D2.tm h⟩
  rh h := ⟨⟨(D1.rh h).1, (D2.rh h).1⟩, ⟨(D1.rh h).2.1, (D2.rh h).2.1⟩, ⟨(D1.rh h).2.2.1, (D2.rh h).2.2.1⟩,
    ⟨(D1.rh h).2.2.2, (D2.rh h).2.2.2⟩⟩
  tSt := ⟨D1.tSt, D2.tSt⟩
  tSc := ⟨D1.tSc, D2.tSc⟩
  tMx h := ⟨D1.tMx h, D2.tMx h⟩
  tIq := ⟨D1.tIq, D2.tIq⟩
  tMi := ⟨D1.tMi, D2.tMi⟩
  tBn := ⟨D1.tBn, D2.tBn⟩
  tPr := ⟨D1.tPr, D2.tPr⟩
  ntf h := ⟨⟨(D1.ntf h).1, (D2.ntf h).1⟩, ⟨(D1.ntf h).2, (D2.ntf h).2⟩⟩
  rRt := ⟨D1.rRt, D2.rRt⟩
  rNx := ⟨D1.rNx, D2.rNx⟩
  eTS := ⟨D1.eTS, D2.eTS⟩
  uG u hu hu0 := ⟨⟨(D1.uG u hu hu0).1, (D2.uG u hu hu0).1⟩, ⟨(D1.uG u hu hu0).2.1, (D2.uG u hu hu0).2.1⟩,
    ⟨(D1.uG u hu hu0).2.2.1, (D2.uG u hu hu0).2.2.1⟩, ⟨(D1.uG u hu hu0).2.2.2, (D2.uG u hu hu0).2.2.2⟩⟩
  uH u hu hu0 ha := ⟨⟨(D1.uH u hu hu0 ha).1, (D2.uH u hu hu0 ha).1⟩,
    ⟨(D1.uH u hu hu0 ha).2.1, (D2.uH u hu hu0 ha).2.1⟩, ⟨(D1.uH u hu hu0 ha).2.2, (D2.uH u hu hu0 ha).2.2⟩⟩
  uS u hu hu0 ha hs hc := ⟨⟨(D1.uS u hu hu0 ha hs hc).1, (D2.uS u hu hu0 ha hs hc).1⟩,
    ⟨(D1.uS u hu hu0 ha hs hc).2.1, (D2.uS u hu hu0 ha hs hc).2.1⟩,
    ⟨(D1.uS u hu hu0 ha hs hc).2.2, (D2.uS u hu hu0 ha hs hc).2.2⟩⟩

/-- `RrDR` from `RrDR0` and the receiver clauses. -/
theorem RrDR.of0 {R : U64 → Prop} {X : S} {t rptr ep : U64} (D : RrDR0 (L := L) R X t rptr ep)
    (hG : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 →
      R (scA u) ∧ R (affA u) ∧ R (core.num.U64.wrapping_add u 3432#u64) ∧ R (prioA u))
    (hH : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X (affA u) = L.cpu X →
      R (stA u) ∧ R (core.num.U64.wrapping_add u 3376#u64) ∧ R (inqA u))
    (hS : ∀ u, L.mem X (rTcbA rptr) = u → u ≠ 0#u64 → L.mem X (affA u) = L.cpu X →
      L.mem X (stA u) = sched.TS_BLOCKED_ON_REPLY → L.mem X (scA u) ≠ 0#u64 →
      RdHead (L := L) R X (L.mem X (scA u))) :
    RrDR (L := L) R X t rptr ep :=
  ⟨D.nd, D.dt, D.cd, D.tm, D.rh, D.tSt, D.tSc, D.tMx, D.tIq, D.tMi, D.tBn, D.tPr, D.ntf, D.rRt, D.rNx, D.eTS, hG,
    hH, hS⟩

end

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW GateField TimerField GField)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_tcb vkc_of not_vdec_node
  not_vdec_tcb)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 8000000 in
/-- **The run from a view start with a homed (or no) receiver is a run on the view's words** (module docstring). -/
theorem rrB_run (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64}
    {rptr ep : U64} {σ : S} {a : A}
    (Q : VmRPre st ar (userV K.toKLayoutV) T Cs Ω H Sg Rp Scs Nt Z Ac Locks σ rptr ep)
    (hrR : rptr ∈ Rp) (hpE : H ep = some .ep)
    (hTab : RdTab (L := L) (IoRS (st := st) (userV K.toKLayoutV) Locks σ) σ)
    (hq : QPs K st σ) (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    (hH : L.mem σ (rTcbA rptr) ≠ 0#u64 → ρ (affA (L.mem σ (rTcbA rptr))) = c)
    (hTabR : ∀ hi : U64, hi.val < 2048 → region K.toKLayout (atAF (L.ksb σ) hi) = .none ∧
      (L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
        region K.toKLayout (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) = .none)) :
    ∃ (Rd Wr : U64 → Prop) (r : Bool × S × A),
      (∀ b, Rd b → Aligned b ∧ b ∉ K.user ∧ VN K c ρ b ∧
        (IoRS (st := st) (userP K) Locks σ b ∨ VKc K.toKLayout c ρ b)) ∧
      (∀ b, Wr b → Aligned b ∧ VNW K c ρ b) ∧
      (r.1 ≠ true → ∀ b, Rd b → IoRS (st := st) (userP K) Locks σ b) ∧
      syscall.handle_reply_recv_vm_local st ar σ a (rptr, ep) = ok r ∧
      syscall.handle_reply_recv_vm_local (PathObl.guard st Rd Wr) ar σ a (rptr, ep) = ok r := by
  have Q' : VmRPre st ar (userP K) T Cs Ω H Sg Rp Scs Nt Z Ac Locks σ rptr ep := vmRPre_userP hK hq.ks Q
  have B := Q.base
  have B' := Q'.base
  have hK0 := hK.base.base
  have hN := B.np
  have hT := B.tp
  have hcT := B.cT
  have hcA := B.tA
  obtain ⟨⟨Qs, Rq, hq0⟩, hB0, hX, hSg, hS⟩ := B.bxi
  have hX0 : ScExtra0 st T Cs Scs Nt σ := hX.2.2.toScExtra0
  have hcC : L.cpu σ ∈ Cs := hq0.cur
  have hsc0 : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := B.bxi.2.1.resume hact
  have hcH : ρ (fld (L.cscW σ) 16#u64) = c := (vm_homes B' hmm).1 hsc0
  have hcur := vm_cur_home hK B hmm
  obtain ⟨r, hr⟩ := rr_total (st := st) hA (rptr, ep) σ a
  have hFr : layout.reg.FAULT_IP.val < 384 := by simp [layout.reg.FAULT_IP]
  have hNr : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
  have ndR : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := fun o ho => by
    rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)
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
  have huX : ∀ v n, L.mem (rrX (L := L) σ v n) (rTcbA rptr) = L.mem σ (rTcbA rptr) := fun v n =>
    (rr_uX B hrR v n).1
  -- a receiver named by the reply at a dispatch state is a homed thread
  have hU : ∀ v n u, L.mem (rrX (L := L) σ v n) (rTcbA rptr) = u → u ≠ 0#u64 →
      u ∈ T ∧ ρ (fld u oAFFINITY) = c := by
    intro v n u hu hu0
    have hu' : L.mem σ (rTcbA rptr) = u := by rw [← huX v n]; exact hu
    refine ⟨by rw [← hu']; exact (rr_uX B hrR v n).2 (by rw [hu']; exact hu0), ?_⟩
    rw [← hu']; exact hH (by rw [hu']; exact hu0)
  by_cases hacc : r.1 = true
  · -- accepted
    obtain ⟨b0, s', a'⟩ := r
    change b0 = true at hacc
    subst hacc
    refine ⟨RrRv (st := st) K c ρ Locks σ, RrWv (st := st) K c ρ Locks σ, _, fun b hb => rrRv_nn hK hb,
      fun b hb => rrWv_nw hK hb, fun h => absurd rfl h, hr, ?_⟩
    have hρC : ∀ (a2 : A) (v n u usc : U64),
        RRChecksG st ar fl4_abi.consts.fault.VMFault (rrX (L := L) σ v n) a2 (L.curW σ) rptr ep u usc →
        RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z (rrX (L := L) σ v n) (L.curW σ) rptr ep u usc →
        ρ (fld u oAFFINITY) = c := by
      intro a2 v n u usc C Pl
      have e := C.tcb
      rw [eq_of_spec_fd (obj.Reply.tcb.blk (L := L) _ rptr)] at e
      have eu : L.mem (rrX (L := L) σ v n) (rTcbA rptr) = u := ok_inj_ff e
      exact (hU v n u eu (fun h0 => (hT _ Pl.hu).ne0 (by rw [h0]; rfl))).2
    refine rr_accR (gS := PathObl.guard st (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ)) hA Q
      (fun o ho h8 => ⟨⟨(B.nd (Locks := Locks) o ho h8).1, Or.inl (nf_node (ndR o ho))⟩,
        ⟨(B.nd (Locks := Locks) o ho h8).2, nf_node (ndR o ho), not_vdec_node hK0 (ndR o ho)⟩⟩)
      ⟨(B.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1, Or.inl (tN _ hcT hcur 3456#u64 (by simp) (by simp))⟩
      ⟨(B.reg (Locks := Locks) hNr).1, Or.inl (rgW _ hcT hcur _ hNr).1⟩
      ⟨(B.reg (Locks := Locks) hFr).2, rgW _ hcT hcur _ hFr⟩ ?_ ?_ ?_ hr
    · -- the current SC's head
      have h1 := (B.cscacc (Locks := Locks)).head B.cscwf
      have h2 := ScAcc.head (R := RrNF (st := st) K c ρ Locks σ) (W := fun _ => True)
        ⟨fun b _ hb => Or.inl (nf_sc (B.lay.io.scw _ (Z _) (B.hSc _ B.cscS) b hb) hcH), fun _ _ _ => trivial,
          trivial⟩ B.cscwf
      unfold RdHead at h1 h2 ⊢
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
    · intro a2 v n u usc Pl C hAs
      exact rr_narA_view hK Q B' hc hmm hcH hTab hTabR Pl C hAs (hρC a2 v n u usc C Pl)
    · intro a2 v n u usc Pl C
      have hρ := hρC a2 v n u usc C Pl
      obtain ⟨haff, -⟩ := rr_u_home B Pl C
      have hu := Pl.hu
      have hst : RrWv (st := st) K c ρ Locks σ (stA (L.curW σ)) :=
        ⟨(B.stw (Locks := Locks)).2, tW _ hcT hcur layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
          (by rw [st_val]; omega)⟩
      have hbo : RrWv (st := st) K c ρ Locks σ (core.num.U64.wrapping_add (L.curW σ) 3336#u64) :=
        ⟨(B.home (Locks := Locks) (off := 3336#u64) (by simp) (by simp) (by simp) (by simp [GateField])
          (by simp [TimerField])).2, tW _ hcT hcur 3336#u64 (by simp) (by simp) (by simp)⟩
      have hsu : RrWv (st := st) K c ρ Locks σ (core.num.U64.wrapping_add u layout.tcb.STATE) := by
        rw [show core.num.U64.wrapping_add u layout.tcb.STATE = core.num.U64.wrapping_add u 3328#u64 from stA_eq u]
        exact ⟨(B.homeOf (Locks := Locks) (off := 3328#u64) hu haff (by simp) (by simp) (by simp)
          (by simp [GateField]) (by simp [TimerField]) (by simp [GField])).2,
          tW _ hu hρ 3328#u64 (by simp) (by simp) (by simp)⟩
      exact ⟨SWr.of_W (gS := PathObl.guard st (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ)) hst,
        SWr.of_W (gS := PathObl.guard st (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ)) hst,
        fun _ _ => gst_write hst, fun _ => gst_write hbo,
        SWr.of_W (gS := PathObl.guard st (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ)) hsu,
        SWr.of_W (gS := PathObl.guard st (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ)) hsu,
        SWr.of_W (gS := PathObl.guard st (RrRv (st := st) K c ρ Locks σ) (RrWv (st := st) K c ρ Locks σ)) hsu⟩
  · -- declined
    let Rd : U64 → Prop := fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b
    let Wr : U64 → Prop := fun b =>
      b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ
    have hn : r.1 ≠ true := hacc
    have ndRd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
      ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (ndR o ho))⟩
    have hnd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Aligned (L.nodeAt σ (L.cpu σ) o) ∧
        VNW K c ρ (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
      ⟨nodeAt_aligned B.np ho h8, vn_of_nf hK (nf_node (ndR o ho)), vkc_of hK0 (nf_node (ndR o ho)).1,
        not_vdec_node hK0 (ndR o ho)⟩
    have hFW : Aligned (regA (L.curW σ) layout.reg.FAULT_IP) ∧ VNW K c ρ (regA (L.curW σ) layout.reg.FAULT_IP) :=
      rrWv_nw (st := st) (Locks := Locks) (σ := σ) hK ⟨(B.reg (Locks := Locks) hFr).2, rgW _ hcT hcur _ hFr⟩
    refine ⟨Rd, Wr, r, fun b hb => ⟨hb.1.1, fun hu => hb.1.2.1 (Or.inl (Or.inl hu)), hb.2, Or.inl hb.1⟩,
      fun b hb => ?_, fun _ b hb => hb.1, hr, ?_⟩
    · rcases hb with rfl | rfl | rfl
      · exact hFW
      · exact hnd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      · exact hnd' _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    refine rr_local_guard_dec (R := Rd) (W := Wr)
      (ndRd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))
      ⟨(B'.home (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField])).1, vn_of_nf hK (tN _ hcT hcur 3456#u64 (by simp) (by simp))⟩
      ⟨(B'.reg (Locks := Locks) hNr).1, vn_of_nf hK (rgW _ hcT hcur _ hNr).1⟩ (Or.inl rfl)
      ⟨ndRd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]), Or.inr (Or.inl rfl),
        ndRd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]), Or.inr (Or.inr rfl)⟩ ?_ hr hn
    intro v X2 a2 eu
    obtain ⟨n, rfl⟩ := hpre v X2 a2 eu
    have D0 := rrDR0_vn hK Q hrR hpE hc hmm B' hcH v n
    have D1 := rr_dr Q' hrR hpE v n
    refine ⟨by rw [rrX_nodeAt]; exact ndRd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
      by rw [rrX_nodeAt]; exact ndRd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]), ?_,
      RrDR.andV D1 (RrDR.of0 D0 ?_ ?_ ?_), ?_⟩
    · -- the current SC's head
      rw [rrX_csc hN hcA hcT v n]
      have h1 := rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B'.bxi B'.cscS)
        ((B'.cscacc (Locks := Locks)).head B'.cscwf)
      have h2 := rdHead_rrX (R := VN K c ρ) hN hcA hcT hcC v n (bxi_headOut B.bxi B.cscS)
        (ScAcc.head (W := fun _ => True)
          ⟨fun b _ hb => vn_of_nf hK (nf_sc (B.lay.io.scw _ (Z _) (B.hSc _ B.cscS) b hb) hcH),
            fun _ _ _ => trivial, trivial⟩ B.cscwf)
      unfold RdHead at h1 h2 ⊢
      exact ⟨⟨h1.1, h2.1⟩, ⟨h1.2.1, h2.2.1⟩, ⟨h1.2.2, h2.2.2⟩⟩
    · -- the receiver's gate words
      intro u hu hu0
      obtain ⟨huT, hρ⟩ := hU v n u hu hu0
      exact ⟨vn_of_nf hK (tN _ huT hρ 3464#u64 (by simp) (by simp)),
        vn_of_nf hK (tN _ huT hρ 3520#u64 (by simp) (by simp)),
        vn_of_nf hK (tN _ huT hρ 3432#u64 (by simp) (by simp)),
        vn_of_nf hK (tN _ huT hρ 3448#u64 (by simp) (by simp))⟩
    · -- the receiver's home words
      intro u hu hu0 _
      obtain ⟨huT, hρ⟩ := hU v n u hu hu0
      exact ⟨vn_of_nf hK (tN _ huT hρ layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)),
        vn_of_nf hK (tN _ huT hρ 3376#u64 (by simp) (by simp)),
        vn_of_nf hK (tN _ huT hρ 3592#u64 (by simp) (by simp))⟩
    · -- the receiver's SC head
      intro u hu hu0 _ hst hsc
      obtain ⟨huT, hρ⟩ := hU v n u hu hu0
      have est : L.mem (rrX (L := L) σ v n) (stA u) = L.mem σ (stA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val])
          (fun _ => by rw [st_val]; omega)
      have esc : L.mem (rrX (L := L) σ v n) (scA u) = L.mem σ (scA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [est] at hst
      rw [esc] at hsc ⊢
      obtain ⟨hcS, htcb, -⟩ := hX0.bound u huT hsc
      have hρs : ρ (fld (L.mem σ (scA u)) 16#u64) = c :=
        vm_sc_home_of_tcb B' hmm hcS (by rw [htcb]; intro e; exact (hT u huT).ne0 (by rw [e]; rfl))
      have hact' : L.mem σ (scA u) ∈ Ac :=
        hB0.sact u huT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) hsc
      have hWF := (hS.all _ hcS).1 ((hS.act _ hcS).1 hact')
      exact rdHead_rrX hN hcA hcT hcC v n (bxi_headOut B.bxi hcS)
        (ScAcc.head (W := fun _ => True)
          ⟨fun b _ hb => vn_of_nf hK (nf_sc (B.lay.io.scw _ (Z _) (B.hSc _ hcS) b hb) hρs),
            fun _ _ _ => trivial, trivial⟩ hWF)
    · -- a receiver off the core: none at the view
      intro u hu hu0 hoff
      exfalso
      apply hoff
      obtain ⟨huT, -⟩ := hU v n u hu hu0
      have ea : L.mem (rrX (L := L) σ v n) (affA u) = L.mem σ (affA u) :=
        rrX_tcb hN hT hcT v n huT (Kx := 3520#u64) (by simp) (by simp) (fun _ => by simp)
      have hAff : IoRS (st := st) (userP K) Locks σ (affA u) :=
        B'.gate (Locks := Locks) (off := 3520#u64) huT (by simp) (by simp) (by simp) (by simp [GateField])
      rw [ea, rrX_cpu, hmm _ hAff.1 (fun hu' => hAff.2.1 (Or.inl (Or.inl hu'))), hc]
      exact Fl4Proofs.P2.CoreView.view_aff hK0 (B.hT _ huT) c ρ

end main

end
end Fl4Proofs.P2.E2EP
