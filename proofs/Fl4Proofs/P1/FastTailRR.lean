/-
# m67's `RRReads5.nvm` derived (FL4 #16, m70)

At the ReplyRecv dispatch state `X0` (`BXI` there and m68's `RRPl`), the
receiver `u` an accepted `fastpath.reply_recv` switches to is current and
`Running` at the run's end (`rrPre5_of`): `u` is `Restart` at `X15` (`X6`),
its SC `usc` is well formed at `X3` (m68's `rr_x3`) and kept to `X15` (the
writes `X3 → X15` miss `Ω`: `rr_om38`, `rr_m15`), the current SC is kept from
`X0` (m68's `FinKeep` at `X8`), and the tail is `switch_to_nvm`. Then
`RRPreAt5` holds at every entry state with `EntryInv` (`RRPreAt5.of_inv`), and
the P1 top `kernel_entry.entry_of10` takes neither `FaultNvmPre` nor
`RRPreAt5`.
-/
import Fl4Proofs.P1.FastTailFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The writes `X8 → X15` (t blocked on the endpoint) miss every word outside
`t`'s TCB, the endpoint and the reply's `TCB` word. -/
theorem rr_m15 {X0 X8 X9 X10 X11 X12 X13 X14 X15 : S} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (e9 : obj.Tcb.set_state st t X8 sched.TS_BLOCKED_ON_RECV = ok X9)
    (e10 : obj.Tcb.set_block_obj st t X9 ep = ok X10)
    (e11 : obj.Tcb.set_reply_obj st t X10 rptr = ok X11)
    (e12 : obj.Reply.set_tcb st rptr X11 t = ok X12)
    (e13 : obj.Tcb.set_ep_next st t X12 0#u64 = ok X13)
    (e14 : obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14)
    (e15 : obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15) :
    L.ksb X15 = L.ksb X8 ∧ L.cpu X15 = L.cpu X8 ∧
    ∀ b, Aligned b → (b.val < t.val ∨ t.val + 2 ^ 12 ≤ b.val) → (b.val + 8 ≤ ep.val ∨ ep.val + 16 ≤ b.val) →
      b.val ≠ (rTcbA rptr).val → L.mem X15 b = L.mem X8 b := by
  have hT := P.hT
  have ht' := hT t P.ht
  have aSt := P.aS P.ht
  have hrΩ := P.hSg.sub _ P.rtS
  have aR : Aligned (rTcbA rptr) := (P.hΩ _ hrΩ).1
  have w9 : X9 = L.wr X8 (stA t) sched.TS_BLOCKED_ON_RECV := by
    have := obj.Tcb.set_state.spec (L := L) X8 t sched.TS_BLOCKED_ON_RECV; rw [e9, WP.spec_ok] at this; exact this
  have w10 : X10 = L.wr X9 (blockA t) ep := by
    have := obj.Tcb.set_block_obj.wr (L := L) X9 t ep; rw [e10, WP.spec_ok] at this; exact this
  have w11 : X11 = L.wr X10 (replyA t) rptr := by
    have := obj.Tcb.set_reply_obj.wr (L := L) X10 t rptr; rw [e11, WP.spec_ok] at this; exact this
  have w12 : X12 = L.wr X11 (rTcbA rptr) t := by
    have := obj.Reply.set_tcb.spec (L := L) X11 rptr t; rw [e12, WP.spec_ok] at this; exact this
  have w13 : X13 = L.wr X12 (nextA .Ep t) 0#u64 := by
    rw [obj.Tcb.set_ep_next.ok] at e13; exact (ok_inj_ff e13).symm
  have w14 : X14 = L.wr X13 (prevA .Ep t) 0#u64 := by
    rw [obj.Tcb.set_ep_prev.ok] at e14; exact (ok_inj_ff e14).symm
  have w15 : X15 = epW (L := L) X14 ep t t obj.EP_RECV := by
    rw [obj.Ep.set_queue.ok] at e15; exact (ok_inj_ff e15).symm
  have vB : (blockA t).val = t.val + 3336 := tcbw_val hT P.ht (by decide)
  have vRp : (replyA t).val = t.val + 3360 := tcbw_val hT P.ht (by decide)
  have vN : (nextA .Ep t).val = t.val + 3496 := by rw [nextA_val ht']; rfl
  have vP : (prevA .Ep t).val = t.val + 3504 := by rw [prevA_val ht']; rfl
  have vS := P.vS P.ht
  have vH : (epHeadA ep).val = ep.val := epHeadA_val
  have vTS : (epTSA ep).val = ep.val + 8 := epTSA_val P.hE
  have ea := P.hE.align
  have ta := ht'.align
  have aB : Aligned (blockA t) := by show _ % 8 = 0; omega
  have aRp : Aligned (replyA t) := by show _ % 8 = 0; omega
  have aN : Aligned (nextA .Ep t) := by show _ % 8 = 0; omega
  have aP : Aligned (prevA .Ep t) := by show _ % 8 = 0; omega
  have aH : Aligned (epHeadA ep) := by show _ % 8 = 0; omega
  have aTS : Aligned (epTSA ep) := by show _ % 8 = 0; omega
  refine ⟨?_, ?_, fun b hb h1 h2 h3 => ?_⟩
  · rw [w15]; unfold epW; simp only [L.ksb_wr]; rw [w14, w13, w12, w11, w10, w9]; simp only [L.ksb_wr]
  · rw [w15]; unfold epW; simp only [LawfulStore.cpu_wr]; rw [w14, w13, w12, w11, w10, w9]
    simp only [LawfulStore.cpu_wr]
  rw [w15]; unfold epW
  rw [L.mem_wr_ne aTS hb (by rw [vTS]; omega), L.mem_wr_ne aH hb (by rw [vH]; omega),
    w14, L.mem_wr_ne aP hb (by rw [vP]; omega), w13, L.mem_wr_ne aN hb (by rw [vN]; omega),
    w12, L.mem_wr_ne aR hb (Ne.symm h3), w11, L.mem_wr_ne aRp hb (by rw [vRp]; omega),
    w10, L.mem_wr_ne aB hb (by rw [vB]; omega), w9, L.mem_wr_ne aSt hb (by rw [vS]; omega)]

/-- The writes `X3 → X8` (the reply transfer's end) miss `Ω`, and `u` is
`Restart` at `X8`. -/
theorem rr_om38 {X0 X3 X4 X5 X6 X7 X8 : S} {a a2 : A} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (k8 : L.ksb X8 = L.ksb X0) (c8 : L.cpu X8 = L.cpu X0)
    (e4 : faults.handle_fault_reply st ar X3 a u t = ok (true, X4, a2))
    (e5 : faults.clear_fault st X4 u = ok X5)
    (e6 : obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6)
    (e7 : sched.set_action st X6 u = ok X7)
    (e8 : obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8) :
    (∀ b ∈ Ω, L.mem X8 b = L.mem X3 b) ∧ L.mem X8 (stA u) = sched.TS_RESTART := by
  have hT := P.hT
  have hu' := hT u P.hu
  have ht' := hT t P.ht
  have aSt := P.aS P.ht
  have aSu := P.aS P.hu
  have vSt := P.vS P.ht
  have vSu := P.vS P.hu
  have vF : (faultA u).val = u.val + 3376 := tcbw_val hT P.hu (by decide)
  have aF : Aligned (faultA u) := by show _ % 8 = 0; rw [vF]; have := hu'.align; omega
  have w34u := faults.handle_fault_reply.rg (L := L) (ar := ar) (T := {u}) (s := X3) (a := a) (snd := t)
    (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hu') (Set.mem_singleton u)
  rw [e4, WP.spec_ok] at w34u
  have x5 : X5 = L.wr X4 (faultA u) fl4_abi.consts.fault.NullFault := by
    unfold faults.clear_fault at e5
    have := obj.Tcb.set_fault_type.spec (L := L) X4 u fl4_abi.consts.fault.NullFault
    rw [e5, WP.spec_ok] at this; exact this
  have x6 : X6 = L.wr X5 (stA u) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X5 u sched.TS_RESTART; rw [e6, WP.spec_ok] at this; exact this
  have x7 : X7 = L.wr X6 (L.nodeAt X6 (L.cpu X6) layout.node.SCHED_ACTION) u := by
    rw [set_action_ok] at e7; exact (ok_inj_ff e7).symm
  have x8 : X8 = L.wr X7 (stA t) sched.TS_RUNNING := by
    have := obj.Tcb.set_state.spec (L := L) X7 t sched.TS_RUNNING; rw [e8, WP.spec_ok] at this; exact this
  have k6 : L.ksb X6 = L.ksb X0 := by rw [← k8, x8, x7, L.ksb_wr, L.ksb_wr]
  have c6 : L.cpu X6 = L.cpu X0 := by rw [← c8, x8, x7, LawfulStore.cpu_wr, LawfulStore.cpu_wr]
  have hN6 : NodePlaced st T X6 (L.cpu X6) := by rw [c6]; exact P.hN.ksb k6
  have vA := nodeAt_val hN6 (off := layout.node.SCHED_ACTION) (by rw [act_val]; omega)
  have aA : Aligned (L.nodeAt X6 (L.cpu X6) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN6 (by rw [act_val]; omega) (by rw [act_val])
  have nb : L.nodeBase X6 (L.cpu X6) = L.nodeBase X0 (L.cpu X0) := by
    rw [c6]; simp [LawfulStore.nodeBase, k6]
  have ndu := P.hN.disj u P.hu
  have hut : u.val ≠ t.val := fun e => P.hut (UScalar.eq_of_val_eq e)
  have ua := hu'.align; have ta := ht'.align
  refine ⟨fun b hb => ?_, ?_⟩
  · have hO := P.hΩ b hb
    have hba := hO.1
    have hbu := hO.2.1 u P.hu
    have hbt := hO.2.1 t P.ht
    have hbn := hO.2.2 _ P.hcC
    rw [x8, L.mem_wr_ne aSt hba (by rw [vSt]; omega), x7, L.mem_wr_ne aA hba (by rw [vA, act_val, nb]; omega),
      x6, L.mem_wr_ne aSu hba (by rw [vSu]; omega), x5, L.mem_wr_ne aF hba (by rw [vF]; omega)]
    refine w34u.2.2 b hba ?_
    rintro (⟨y, hy, K, -, h2, -, e⟩ | h)
    · rw [Set.mem_singleton_iff.1 hy] at e
      have := congrArg UScalar.val e; rw [tcbw_val hT P.hu (by omega)] at this; omega
    · exact absurd h (Set.notMem_empty _)
  · rw [x8, L.mem_wr_ne aSt aSu (by rw [vSt, vSu]; omega), x7,
      L.mem_wr_ne aA aSu (by rw [vA, act_val, nb, vSu]; omega), x6, L.mem_wr_same aSu]

set_option maxHeartbeats 1600000 in
/-- **m67's `nvm` from the dispatch state's invariants** (module docstring). -/
theorem rrPre5_of {H : Heap} {Ac : Set U64} {X0 : S} {a : A}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X0)
    (hP : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecks st ar X0 a t rptr ep u usc → RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : RRSum (L := L) Scs X0) (hA : P0.ArchTotal ar) : RRPre5 (L := L) ar X0 a := by
  intro t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3 X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15
    e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  have P := hP t rptr ep u usc hct hrc hC
  obtain ⟨-, -, K8, -⟩ := rr_x8 ar P hC (hS usc P.hcS) e1 e2 e3s e3 e4 e5 e6 e7 e8
  obtain ⟨-, -, -, -, -, hW3, -⟩ := rr_x3 ar P hC (hS usc P.hcS) e1 e2 e3s e3
  obtain ⟨om38, su8⟩ := rr_om38 ar P K8.ksb K8.cpu e4 e5 e6 e7 e8
  obtain ⟨k15, c15, m15⟩ := rr_m15 P e9 e10 e11 e12 e13 e14 e15
  obtain ⟨-, -, hX, -, hS0⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt X0 := hX.2.2.toScExtra0
  have hO := P.hO
  have hT := P.hT
  have hu' := hT u P.hu
  have ht' := hT t P.ht
  have ua := hu'.align; have ta := ht'.align
  have hut : u.val ≠ t.val := fun e => P.hut (UScalar.eq_of_val_eq e)
  have hrΩ := P.hSg.sub _ P.rtS
  -- Ω words pass `m15`'s side conditions
  have m15Ω : ∀ b ∈ Ω, b ≠ rTcbA rptr → L.mem X15 b = L.mem X8 b := fun b hb hne =>
    m15 b (P.hΩ b hb).1 ((P.hΩ b hb).2.1 t P.ht) (P.hEΩ b hb) (fun e => hne (UScalar.eq_of_val_eq e))
  -- u's words too
  have m15u : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X15 (core.num.U64.wrapping_add u K) = L.mem X8 (core.num.U64.wrapping_add u K) := by
    intro K hK h8
    have v := tcbw_val hT P.hu hK
    have hed := P.hE.disj u P.hu
    have hro := (P.hΩ _ hrΩ).2.1 u P.hu
    exact m15 _ (field_aligned hu' hK h8) (by rw [v]; omega) (by rw [v]; omega) (by rw [v]; omega)
  have kX : L.ksb X15 = L.ksb X0 := k15.trans K8.ksb
  have cX : L.cpu X15 = L.cpu X0 := c15.trans K8.cpu
  -- SC facts
  have nrp : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → ¬ RpLW Rp b ∧ b ≠ rTcbA rptr := by
    intro c hc b hin
    unfold InSC at hin
    refine ⟨?_, fun e => ?_⟩
    · rintro ⟨r', hr', rfl | rfl⟩
      · have := hO.rpSc r' hr' _ hc; rw [rPrevA_val (hO.rp r' hr')] at hin; omega
      · have := hO.rpSc r' hr' _ hc; rw [rNextA_val (hO.rp r' hr')] at hin; omega
    · have := hO.rpSc rptr P.hrR _ hc; rw [e, rTcbA_val0] at hin; omega
  have scWu : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb h => P.hSg.sub _ (P.scSg b hb h)
  have hWX : RefillsWF st X15 usc (Z usc) := hW3.agree fun b hb hin => by
    rw [m15Ω b (scWu b hb hin) (nrp _ P.hcS b hin).2, om38 b (scWu b hb hin)]
  have hcs : L.cscW X0 ∈ Scs := hX0.cur
  have hcq0 : SCq st X0 Ω (L.cscW X0) (Z (L.cscW X0)) := by
    obtain ⟨hP', hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP' hz
    have hv := sc_word_val hP' hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
    exact ⟨(hS0.all _ hcs).1, fun b hb hi => hS0.sub _ ((hS0.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have csA : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecX : L.cscW X15 = L.cscW X0 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    have v := nodeAt_val P.hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have hnt := P.hN.disj t P.ht
    have hne := P.hEN.1 _ P.hcC
    have hro := (P.hΩ _ hrΩ).2.2 _ P.hcC
    have c24 : layout.node.CUR_SC.val = 24 := by simp [layout.node.CUR_SC]
    rw [m15 _ csA (by rw [v]; omega) (by rw [v]; omega) (by rw [v]; omega)]
    exact K8.node _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC])
  have escX : L.mem X15 (scA u) = usc := by
    rw [scA_eq, m15u _ (by simp) (by simp)]
    rw [K8.tcb u P.hu 3464#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide), ← scA_eq]
    exact P.husc
  have stX : L.mem X15 (stA u) = sched.TS_RESTART := by
    rw [stA_eq, m15u _ (by simp) (by simp), ← stA_eq]; exact su8
  have eyX : L.mem X15 (yieldA u) = L.mem X0 (yieldA u) := by
    rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl, m15u _ (by simp) (by simp)]
    exact K8.tcb u P.hu 3472#u64 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
  have hcX : SCq st X15 Ω (L.cscW X15) (Z (L.cscW X15)) := by
    rw [ecX]
    refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
    by_cases hcd : L.cscW X0 = usc
    · rw [hcd]; exact hWX
    · have agC : ∀ b, Aligned b → InSC (L.cscW X0) (Z (L.cscW X0)) b → L.mem X15 b = L.mem X0 b := by
        intro b hb hin
        have hbΩ := hcq0.2.1 b hb hin
        obtain ⟨n1, n2⟩ := nrp _ hcs b hin
        rw [m15Ω b hbΩ n2]
        refine K8.omg b ⟨hbΩ, n1⟩ n2 fun hR => ?_
        have := hO.scDisj _ hcs _ P.hcS hcd
        unfold InSC at hin; unfold InRing at hR; omega
      have em : L.rmax X15 (L.cscW X0) = L.rmax X0 (L.cscW X0) := by
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact agC _ a1 ⟨a2, a3⟩
      exact (hcq0.1 (em ▸ hm)).agree agC
  have htX : L.mem X15 (scA u) ≠ L.cscW X15 → SCin st X15 Ω (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) ∧
      ∀ b, InSC (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) b → Outside b (L.cscW X15) (Z (L.cscW X15)) := by
    rw [escX, ecX]
    intro hne
    refine ⟨⟨hWX, scWu⟩, fun b hin => ?_⟩
    have := hO.scDisj _ P.hcS _ hcs hne
    unfold InSC at hin; unfold Outside; omega
  have hyX : L.mem X15 (yieldA u) ≠ 0#u64 → L.mem X15 (yieldA u) ∈ Scs := by
    rw [eyX]; exact hX0.yt.2.1 u P.hu
  have PX : TailPld (L := L) T Cs Ω X15 u :=
    (⟨hT, P.hu, P.hN, P.hcC, P.hΩ⟩ : TailPld (L := L) T Cs Ω X0 u).ksb kX cX
  refine ⟨fun s' a' hsw => ?_⟩
  have hend := switch_to_nvm hA X15 a2 PX (ObjsOK.any hO) P.hSg.sub hcX htX (Or.inr stX) hyX
  rw [hsw, WP.spec_ok] at hend
  obtain ⟨h1, h2⟩ := hend
  rw [h1, h2]
  simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]

/-- **`RRPreAt5` (m67's `nvm`) at an entry state** with `EntryInv`, under
m68's ring-sum bound `RRSumAt` [J] (the dispatch states' invariants from
`budget_ok.bxc`, the placement from `rrPl_of`, as `RRPreAt2.of5`). -/
theorem RRPreAt5.of_inv {U Ac : Set U64} {H : Heap} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSum : RRSumAt (L := L) ar Scs s a) : RRPreAt5 (L := L) ar s a := by
  intro t nx s1 s2 a2 et enx es1 hb
  have h0 := h.1.choose_spec.choose_spec
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  have htT : t ∈ T := by rw [et']; exact h0.curT
  have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := reg_entry (r := layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) h htT
      (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at this; exact this
  have hW := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (h0.tcbs t htT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW
  obtain ⟨K, hK, e1⟩ := hW
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h0.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have e1' : s1 = L.wr s (core.num.U64.wrapping_add (L.curW s) K) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [e1, et']
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal e1' (WritesIn.refl _ _)⟩
  have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
  rw [hb, WP.spec_ok] at hx
  have hPl := fun t' rptr ep u usc (et2 : sched.cur_thread st s2 = ok t') hrc
    (hC : RRChecks st ar s2 a2 t' rptr ep u usc) => rrPl_of ar E0 hNt hx.1 (hx.2.2 rfl) et2 hrc hC
  exact rrPre5_of ar hx.1 hPl (hSum t nx s1 s2 a2 et enx es1 hb) hA

end

section top
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`, the fast paths' end-state reads
derived** (m70): `entry_of9` without m67's `hNv : FaultNvmPre` [J] and
`hRP : RRPreAt5` [J] (`FaultNvmPre.of_asid`, `RRPreAt5.of_inv`). Left:
`StoreExt` [P], `AsidOff` [J], `RRSumAt` [J], `CnOffAt` [J]. -/
theorem kernel_entry.entry_of10 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hSum : RRSumAt (L := L) ar Scs s a)
    (hCn : CnOffAt (L := L) ar T Cs Sg s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  have hNt : ∀ n ∈ Nt, H n = some .ntfn := (GF _ hσ).2.2.2.2.2
  exact kernel_entry.entry_of9 hA GF hσ s a hP h hX hAs
    (fun _ _ => FaultNvmPre.of_asid ar hA E0 (GF _ hσ).1.xfer hP h hAs) hSum hCn
    (RRPreAt5.of_inv ar hA E0 hNt hP h hSum)

end top

end Fl4Proofs.P1
