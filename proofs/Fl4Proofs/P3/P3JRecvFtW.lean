/-
P3 (p3J gen 31): **the endpoint receive writes only `ProjW`** — FL4's `endpoint.receive_ipc` under P1's invariants
over the sets of `H` (P1 EntryXG's `receive_ipc.xg` hypotheses, its walk re-run with `ProjW` for `XG`), from a
`BufK` state (no frame cap in any TCB's IPC-buffer slot at the base state `sE`):

* **`completeSignalProjW`**: `notification.complete_signal` (the active bound notification): the `BADGE` register,
  the notification's state word, P2's `maybe_donate_sched_context.ff` (`ffoot_projW`) and `unblock_check`
  (`unblock_projW`) — gen 28's `recvSignalProjW` active branch on `complete_signal`'s code.
* **`recvIpcProjW`**: `take_reply` (P3JRecvFtN's `take_reply.kwN0`), the complete-signal branch, the bound
  notification's SC return (P3JRecvN's `maybe_return_sched_context.kwN0`), `wait_for_sender.footN0` and
  `receive_from_sender.footNB` (P3JRecvFtN), each mapped into `ProjW` (`kwN_projW`, `ipcWN_projW`) and composed by
  `WritesIn.projW_trans`; `BufK` carried to the transfer by `bufK_kw` along the `KW` steps.

No premise beyond the stated hypotheses; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRecvFtN
import Fl4Proofs.P3.P3JSysRecv
import Fl4Proofs.P3.P3JMcFlt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {H : P1.Heap} {Cs Ac : Set U64}

set_option maxHeartbeats 8000000 in
/-- **`complete_signal` writes only `ProjW`** under P1's invariants over `H`'s sets (module docstring). -/
theorem completeSignalProjW (hA : P0.ArchTotal ar) (hH : P1.HeapOK H)
    (s : S) (a : A) (n t : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H s Q R)
    (hB : BoundInv st (P1.Heap.tcbs H) Ac s)
    (hX : XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) s)
    (hS : SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s)
    (hSg : SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s) (ht : t ∈ P1.Heap.tcbs H)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t) (hn : H n = some .ntfn) (hnΩ : ntfnScA n ∈ P1.Heap.omega H)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ P1.Heap.scs H ∧
      L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs)
    (hdA : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scA t) = 0#u64 → Sch st s t → L.mem s (ntfnScA n) ∈ Ac) :
    notification.complete_signal st ar s a n t ⦃ s' _ => P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ := by
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ :=
    (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  unfold notification.complete_signal
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact ok0
  step with obj.Ntfn.state.spec as ⟨i, ei⟩
  split
  · exact ok0
  rename_i hia
  have hact : L.epState s n = 2#u64 := by rw [← ei]; exact ntfn_active_ne hia
  step with obj.Ntfn.badge.any as ⟨b1, _⟩
  refine WP.spec_bind (obj.Tcb.set_reg.badge s t b1 hta) fun s1 e1 => ?_
  subst e1
  have g1 : P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (ProjW (L := L) H Cs s) :=
    (writesIn_wr (field_aligned hta (by simp) (by simp))).mono fun b hb => by
      subst hb; exact tcbF_projW hH ht (by simp)
  obtain ⟨h1, hB1, hX1, hS1, hSg1⟩ := badge_all (v := b1) h hB hX hS hSg ht
  have ha1 : Aligned (core.num.U64.wrapping_add t 256#u64) := field_aligned hta (by simp) (by simp)
  have f1 : ∀ y ∈ P1.Heap.tcbs H, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 256) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 hne =>
    L.mem_wr_ne ha1 (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h' => hne rfl h'.symm)
        (UScalar.eq_of_val_eq e))
  have o1 : ∀ x ∈ P1.Heap.omega H, L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) x = L.mem s x :=
    fun x hx => L.mem_wr_ne ha1 (h.omega x hx).1 (fun e => out_ne_field (h.omega x hx) ht hta (by simp) e)
  have ts1 : L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (epTSA n) = L.mem s (epTSA n) :=
    L.mem_wr_ne ha1 (ep_aligned hE).2 (by
      rw [field_val hta (by simp), epTSA_val hE]; have := hE.disj t ht; simp; omega)
  have hact1 : L.epState (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) n = 2#u64 := by
    simp only [LawfulStore.epState]; rw [ts1]; exact hact
  have ei1 : L.idleW (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) = L.idleW s := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ha1 (nodeAt_aligned hN (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) hN (by rw [idle8]; omega) ht hta (by simp) (UScalar.eq_of_val_eq e).symm)
  set s1 := L.wr s (core.num.U64.wrapping_add t 256#u64) b1 with hs1
  refine WP.spec_bind (obj.Ntfn.set_state.val s1 n _) fun s2 e2 => ?_
  subst e2
  have g2 : P1.WritesIn st s
      (L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)))
      (ProjW (L := L) H Cs s) :=
    g1.projW_trans ((writesIn_wr (ep_aligned hE).2).mono fun b hb => by
      subst hb; unfold epTSA
      exact obj_projW hH (k := .ntfn) hn (by simp [layout.ep.TAIL_STATE, P1.HKind.bits]))
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hn hact1
  set s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have F : ∀ y ∈ P1.Heap.tcbs H, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = t → K.val ≠ 256) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 h1' h2' h3' => (f2 y hy K hK hK8 h1' h2').trans (f1 y hy K hK hK8 h3')
  have O : ∀ x ∈ P1.Heap.omega H, L.mem s2 x = L.mem s x := fun x hx => (o2 x hx).trans (o1 x hx)
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have ea2' : L.actionW s2 = L.actionW s := by
    rw [ea2, hs1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hc2 : L.mem s2 (ntfnScA n) = L.mem s (ntfnScA n) := O _ hnΩ
  refine WP.spec_bind (Fl4Proofs.P2.Stall.notification.maybe_donate_sched_context.ff (Kp := ∅) (Il := ∅)
    (Ks := ∅) (Es := EH H) (U := ∅) hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht
    (by rw [iq2]; exact htq) (by rw [iq2]; exact htr) (by rw [ea2']; exact hta') (by rw [ei2, ei1]; exact hti)
    (fun h0 _ _ => ?_) (Set.notMem_empty _) (Set.notMem_empty _) (fun k hk => absurd hk (Set.notMem_empty _))) ?_
  · rw [hc2] at h0 ⊢
    obtain ⟨c1, c3⟩ := hns h0
    obtain ⟨-, hcΩ⟩ := objs_omega hX.1 hSg.sub
    refine ⟨c1, by rw [O _ (hcΩ _ c1).2.1]; exact c3, fun hS2t => hdA h0 (by rw [← sc2]; assumption) ?_⟩
    have f21 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s1 (core.num.U64.wrapping_add t K) :=
      fun K a1 a2 a3 a4 => f2 t ht K a1 a2 a3 a4
    have hS1t : Sch st s1 t := Sch.of_eq
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      (fun hf => by rwa [inqA_eq, f21 _ (by simp) (by simp) (by simp) (by simp)] at hf)
      ea2 ei2 ec2 (by rw [Fl4Proofs.P1.stA_eq]; exact f21 _ (by simp) (by simp) (by simp) (by simp)) hS2t
    exact Sch.wr_field h ht (by simp) (by simp) (by simp) ht hS1t
  rintro ⟨s3, a1⟩ ⟨⟨⟨Q3, R3, h3'⟩, hB3, hX3, hS3, hSg3⟩, F3⟩
  try simp only [WP.uncurry'_pair]
  have g3 : P1.WritesIn st s s3 (ProjW (L := L) H Cs s) :=
    g2.projW_trans ((WritesA.w F3).mono fun _ hb => ffoot_projW hH h2.nodes hX2.1 hb)
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ :=
    (WP.spec_ok _).2 g3
  step with obj.Tcb.sc.spec as ⟨i1, ei1'⟩
  step with sporadic.sc_sporadic.spec as ⟨b2, eb2⟩
  split
  · rename_i hb2
    step with obj.Ntfn.sc.val as ⟨i2, _⟩
    split
    · step with sched.cur_sc.spec as ⟨c4, _⟩
      step with sc_ne.spec as ⟨b3⟩
      split
      · have hi1S : i1 ∈ P1.Heap.scs H := (hX3.2.2.bound t ht (by rw [← ei1']; exact (eb2 hb2).1)).1 |> fun h => by
          rw [← ei1'] at h; exact h
        refine WP.spec_bind (unblock_projW hH s3 t i1 h3' hX3 hS3 ht ei1' (eb2 hb2).1
          (hS3.spor i1 hi1S (eb2 hb2).2)) fun s5 F5 => ?_
        exact (WP.spec_ok _).2 (g3.projW_trans F5)
      · exact ok3
    · exact ok3
  · exact ok3

set_option maxHeartbeats 8000000 in
/-- **`receive_ipc` writes only `ProjW`** under P1's invariants over `H`'s sets, from a `BufK` state (module
docstring). -/
theorem recvIpcProjW (hA : P0.ArchTotal ar) (hH : P1.HeapOK H) {sE : S}
    (hNB : NoBufCap (L := L) (P1.Heap.tcbs H) sE)
    (hP : BufApart (L := L) (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (EH H) sE)
    (s : S) (a : A) (t : U64) (cap : capability.Cap) (blocking : Bool) (reply_cap : capability.Cap) (e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H s Q R)
    (hB : BoundInv st (P1.Heap.tcbs H) Ac s)
    (hX : XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) s)
    (hS : SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s)
    (hSg : SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s) (hc : CanBlock st (P1.Heap.tcbs H) Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hHe : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ P1.Heap.replies H)
    (hNt : ∀ n ∈ P1.Heap.ntfns H, H n = some .ntfn) (hK0 : BufK (L := L) (P1.Heap.tcbs H) sE s) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ =>
      P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ := by
  unfold endpoint.receive_ipc
  rw [hptr]
  simp only [Aeneas.Std.bind_ok]
  refine WP.spec_bind (WP.spec_and (endpoint.take_reply.inv ar s a t reply_cap Q R h hB hX hS hSg hc hcap)
    (endpoint.take_reply.kwN0 (Sg := P1.Heap.frame H) (Scs := P1.Heap.scs H) (Z := P1.Heap.scBits H) s a t
      reply_cap h hX hSg hcap)) ?_
  rintro ⟨reply, s1, a1⟩ ⟨⟨h1, hB1, hX1, hS1, hSg1, hc1, hi1, hr1, kb1, -⟩, F1⟩
  have g1 : P1.WritesIn st s s1 (ProjW (L := L) H Cs s) := (WritesA.w F1).mono fun _ hb => kwN_projW hH h.nodes hb
  have K1 : BufK (L := L) (P1.Heap.tcbs H) sE s1 := bufK_kw hP hK0 F1.foot
  have hidle := hc.ni
  try simp only [WP.uncurry'_pair]
  have ht := hc.mem
  -- the end on the endpoint
  have tail : ∀ (s2 : S) (a2 : A) (Q2 : U64 → U64 → List U64) (R2 : U64 → List U64),
      SchedQueuesInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H s2 Q2 R2 → BoundInv st (P1.Heap.tcbs H) Ac s2 →
      XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
        (P1.Heap.ntfns H) (P1.Heap.scBits H) s2 →
      SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s2 →
      SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s2 → CanBlock st (P1.Heap.tcbs H) Ac s2 t →
      (reply ≠ 0#u64 → reply ∈ P1.Heap.replies H ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) →
      BufK (L := L) (P1.Heap.tcbs H) sE s2 → P1.WritesIn st s s2 (ProjW (L := L) H Cs s) →
      (do
        let st0 ← obj.Ep.state st e s2
        if st0 = obj.EP_IDLE then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else if st0 = obj.EP_RECV then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else endpoint.receive_from_sender st ar s2 a2 t e reply) ⦃ s' _ =>
          P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ := by
    intro s2 a2 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 K2 g2
    have W : (do
        let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
        ok (s3, a2)) ⦃ s' _ => P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ :=
      WP.spec_bind (endpoint.wait_for_sender.footN0 (Ac := Ac) s2 t e blocking reply Q2 R2 h2 hX2 hSg2 ht
        (fun _ => hc2) hHe (fun hn => (hr2 hn).1)) fun s3 f3 =>
        (WP.spec_ok _).2 (g2.projW_trans ((WritesA.w f3).mono fun _ hb => kwN_projW hH h2.nodes hb))
    step with obj.Ep.state.spec as ⟨v, hv⟩
    split
    · exact W
    · split
      · exact W
      · rename_i h01 h02
        exact WP.spec_mono (endpoint.receive_from_sender.footNB hA hNB hP s2 a2 t e reply Q2 R2 h2 hB2 hX2 hS2 hSg2
          hc2 hHe ⟨fun e0 => h01 (by rw [hv, e0, ep_idle_val]), fun e0 => h02 (by rw [hv, e0, ep_recv_val'])⟩
          hr2 K2) fun r f => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at f ⊢
            exact g2.projW_trans ((WritesA.w f).mono fun _ hb => ipcWN_projW hH h2.nodes hb)
  -- the bound notification's SC
  have mid : ∀ (i : U64), (if blocking then notification.maybe_return_sched_context st s1 i t else ok s1)
      ⦃ s2 => ∃ Q2 R2, SchedQueuesInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H s2 Q2 R2 ∧
        BoundInv st (P1.Heap.tcbs H) Ac s2 ∧
        XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
          (P1.Heap.ntfns H) (P1.Heap.scBits H) s2 ∧
        SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s2 ∧
        SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s2 ∧ CanBlock st (P1.Heap.tcbs H) Ac s2 t ∧
        (reply ≠ 0#u64 → reply ∈ P1.Heap.replies H ∧
          (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) ∧
        BufK (L := L) (P1.Heap.tcbs H) sE s2 ∧ P1.WritesIn st s s2 (ProjW (L := L) H Cs s) ⦄ := by
    intro i
    split
    · refine WP.spec_mono (WP.spec_and (notification.maybe_return_sched_context.inv s1 i t Q R h1 hB1 hX1 hS1 hSg1 ht
        ⟨hc1.nq, hc1.nr, hc1.na⟩ (by rw [hi1]; exact hidle))
        (notification.maybe_return_sched_context.kwN0 (Es := EH H) s1 i t Q R h1 hB1 hX1 hS1 hSg1 ht
        ⟨hc1.nq, hc1.nr, hc1.na⟩ (by rw [hi1]; exact hidle))) fun s2 hh' => ?_
      obtain ⟨hh, F2⟩ := hh'
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2, q2, st2, na2, ii2, rt2, sa2, ks2, sc2⟩ := hh
      refine ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc1.mrsc q2 st2 na2 ii2 sc2, fun hn => ?_, bufK_kw hP K1 F2.foot,
        g1.projW_trans ((WritesA.w F2).mono fun _ hb => kwN_projW hH h1.nodes hb)⟩
      obtain ⟨r1, r2⟩ := hr1 hn
      rw [rt2 _ r1]; exact ⟨r1, r2⟩
    · exact (WP.spec_ok _).2 ⟨Q, R, h1, hB1, hX1, hS1, hSg1, hc1, hr1, K1, g1⟩
  step with obj.Tcb.bound_ntfn.val as ⟨i, ei⟩
  split
  · rename_i hi0
    step with obj.Ntfn.state.spec as ⟨v1, hv1⟩
    split
    · have hn0 : L.mem s1 (boundA t) ≠ 0#u64 := by rw [← ei]; simpa using hi0
      obtain ⟨hn1, hn2, hn3⟩ := BoundNtfnOK.of_inv hNt ht hX1 hS1 hSg1 hn0
      subst ei
      refine WP.spec_mono (completeSignalProjW hA hH s1 a1 _ t Q R h1 hB1 hX1 hS1 hSg1 ht hc1.nq hc1.nr hc1.na
        hc1.ni hn1 hn2 hn3 (fun _ h0 hS' => ?_)) fun r f => ?_
      · exfalso
        rcases hS' with e | e | e | e | ⟨e1, e2⟩ | e
        · exact e hc1.nq
        · exact e hc1.nr
        · exact hc1.na e
        · exact hc1.ni e
        · exact hB1.resume e1 (by rw [e2]; exact h0)
        · rcases e with e | e
          · exact hc1.nb e
          · exact hc1.nrp e
      · obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at f ⊢
        exact g1.projW_trans f
    · refine WP.spec_bind (mid i) ?_
      rintro s2 ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc2, hr2, K2, g2⟩
      exact tail s2 a1 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 K2 g2
  · try simp only [Aeneas.Std.bind_ok]
    exact tail s1 a1 Q R h1 hB1 hX1 hS1 hSg1 hc1 hr1 K1 g1

end

end Fl4Proofs.P3.Mc
