/-
P1: `receive_signal` in full (the active notification case besides the
blocking ones), and the kernel-entry receive and timeout paths
(`handle_recv`, `handle_timeout`) from explicit cap-validity, transfer and
blocking hypotheses.
-/
import Fl4Proofs.P1.QueueReplyPop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

theorem BXI.blk {Ac : Set U64} {s : S} (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

theorem BlkOK.bxi {Ac : Set U64} {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩

/-- seL4 `receiveSignal`: blocking or polling on an idle or waiting
notification, or taking the badge of an active one (with its SC, if
unbound, and the sporadic unblock).  The receiver can block; the
notification's state word is one of the three states. -/
theorem notification.receive_signal.ipc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (blocking : Bool) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hnN : n ∈ Nt) (hn : H n = some .ntfn) (h3 : L.epState s n ≠ 3#u64) :
    notification.receive_signal st ar s a t n blocking ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have ht := hc.mem
  by_cases e01 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64
  · exact WP.spec_mono (notification.receive_signal.block ar s a t n blocking Q R h hB hX hS hSg ht (fun _ => hc)
      hc.ni hn e01) fun r hr => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr
  have hact : L.epState s n = 2#u64 := by
    have := (L.mem s (epTSA n)).val
    push_neg at e01
    simp only [LawfulStore.epState] at e01 h3 ⊢
    apply UScalar.eq_of_val_eq
    have hb : (L.mem s (epTSA n) &&& 3#u64).val < 4 := by
      rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
    have e0 : (L.mem s (epTSA n) &&& 3#u64).val ≠ 0 := fun e => e01.1 (UScalar.eq_of_val_eq e)
    have e1 : (L.mem s (epTSA n) &&& 3#u64).val ≠ 1 := fun e => e01.2 (UScalar.eq_of_val_eq e)
    have e3 : (L.mem s (epTSA n) &&& 3#u64).val ≠ 3 := fun e => h3 (UScalar.eq_of_val_eq e)
    show (L.mem s (epTSA n) &&& 3#u64).val = 2
    omega
  have hta' := hc.na
  have hti := hc.ni
  have htq := hc.nq
  have htr := hc.nr
  have hnΩ : ntfnScA n ∈ Ω := hSg.sub _ (hX.1.ntW n hnN)
  have hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧
      L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs := fun h0 => by
    obtain ⟨hc', -⟩ := hX.2.2.nsc n hnN h0
    exact ⟨hc', hX.2.2.core _ hc'⟩
  have hdA : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scA t) = 0#u64 → Sch st s t → L.mem s (ntfnScA n) ∈ Ac := by
    intro _ h0 hS'
    exfalso
    rcases hS' with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e hc.nq
    · exact e hc.nr
    · exact hc.na e
    · exact hc.ni e
    · exact hB.resume e1 (by rw [e2]; exact h0)
    · rcases e with e | e
      · exact hc.nb e
      · exact hc.nrp e
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hn)
  obtain ⟨hE, -, -⟩ := hEW.1 n he
  unfold notification.receive_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  rw [if_neg (by rw [hv, hact, ntfn_idle_val]; decide), if_neg (by rw [hv, hact, ntfn_wait_val']; decide)]
  step with obj.Ntfn.badge.any as ⟨b1, _⟩
  refine WP.spec_bind (obj.Tcb.set_reg.badge s t b1 hta) fun s1 e1 => ?_
  subst e1
  obtain ⟨h1, hB1, hX1, hS1, hSg1⟩ := badge_all (v := b1) h hB hX hS hSg ht
  have ha1 : Aligned (core.num.U64.wrapping_add t 256#u64) := field_aligned hta (by simp) (by simp)
  have f1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 256) →
      L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 hne =>
    L.mem_wr_ne ha1 (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' => by subst e'; exact fun h' => hne rfl h'.symm)
        (UScalar.eq_of_val_eq e))
  have o1 : ∀ x ∈ Ω, L.mem (L.wr s (core.num.U64.wrapping_add t 256#u64) b1) x = L.mem s x := fun x hx =>
    L.mem_wr_ne ha1 (h.omega x hx).1 (fun e => out_ne_field (h.omega x hx) ht hta (by simp) e)
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
  obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, o2, ea2, ei2, ec2⟩ := ntfn_idle_all h1 hB1 hX1 hS1 hSg1 hn hact1
  set s2 := L.wr s1 (epTSA n) ((L.mem s1 (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs2
  have F : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 → (y = t → K.val ≠ 256) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 h1' h2' h3' => (f2 y hy K hK hK8 h1' h2').trans (f1 y hy K hK hK8 h3')
  have O : ∀ x ∈ Ω, L.mem s2 x = L.mem s x := fun x hx => (o2 x hx).trans (o1 x hx)
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact F t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have ea2' : L.actionW s2 = L.actionW s := by
    rw [ea2, hs1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hc2 : L.mem s2 (ntfnScA n) = L.mem s (ntfnScA n) := O _ hnΩ
  refine WP.spec_bind (notification.maybe_donate_sched_context.ipc hA s2 a t n Q R h2 hB2 hX2 hS2 hSg2 ht
    (by rw [iq2]; exact htq) (by rw [iq2]; exact htr) (by rw [ea2']; exact hta') (by rw [ei2, ei1]; exact hti)
    fun h0 _ _ => ?_) ?_
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
      ea2 ei2 ec2 (by rw [stA_eq]; exact f21 _ (by simp) (by simp) (by simp) (by simp)) hS2t
    exact Sch.wr_field h ht (by simp) (by simp) (by simp) ht hS1t
  rintro ⟨s3, a1⟩ ⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩
  try simp only [WP.uncurry'_pair]
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b3⟩
  split
  · step with sporadic.sc_sporadic.spec as ⟨b2, eb2⟩
    split
    · rename_i hb2
      have hi1S : i1 ∈ Scs := (hX3.2.2.bound t ht (by rw [← ei1]; exact (eb2 hb2).1)).1 |> fun h => by
        rw [← ei1] at h; exact h
      refine WP.spec_bind (sporadic.unblock_check.all s3 t i1 h3 hB3 hX3 hS3 hSg3 ht ei1 (eb2 hb2).1
        (hS3.spor i1 hi1S (eb2 hb2).2)) fun s5 hh => ?_
      obtain ⟨h5, hB5, hX5, hS5, hSg5, -⟩ := hh
      exact (WP.spec_ok _).2 ⟨⟨Q3, R3, h5⟩, hB5, hX5, hS5, hSg5⟩
    · exact ok3
  · exact ok3

/-- The cap-validity facts the receive and timeout paths read (P3's
`CapValid`): an endpoint cap names a heap endpoint, a notification cap a
notification object of `Nt`, a reply cap a reply object. -/
def CapTyped (H : Heap) (Rp Nt : Set U64) (c : capability.Cap) : Prop :=
  (∀ p b x y z w, c = .Endpoint p b x y z w → H p = some .ep) ∧
  (∀ p b x y, c = .Notification p b x y → p ∈ Nt ∧ H p = some .ntfn) ∧
  (∀ p g, c = .Reply p g → p ∈ Rp)

/-- seL4 `handleRecv`: the endpoint (or notification) cap and, with a reply
right, the reply cap are looked up; `receive_ipc` / `receive_signal`, or a
cap fault.  From the hypotheses at the call: the looked-up caps are typed
(`CapTyped`), the notification states are the three states, the current
thread can block, the user words are outside the kernel objects (`UserOK`)
and the message transfer writes there (`XferOK`); cap faults are the fault
family `hfault`. -/
theorem syscall.handle_recv.bxi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) {U : Set U64} (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U)
    {Ac : Set U64} (s : S) (a : A) (blk rep : Bool) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s (L.curW s))
    (hlk : ∀ cptr, cspace.lookup_cap st s (L.curW s) cptr ⦃ r => ∀ c, r = .Ok c → CapTyped H Rp Nt c ⦄)
    (h3 : ∀ n ∈ Nt, L.epState s n ≠ 3#u64)
    (hfault : ∀ (f : error.Fault),
      faults.handle_fault st ar s a (L.curW s) f ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄) :
    syscall.handle_recv st ar s a blk rep ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  have CF : ∀ cptr lf, syscall.cap_fault_recv st ar s a cptr lf ⦃ s' _ =>
      ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := fun cptr lf => by
    unfold syscall.cap_fault_recv
    step with sched.cur_thread.spec as ⟨t1, e1⟩
    have e1' : t1 = L.curW s := e1
    subst e1'
    exact hfault _
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ :=
    (WP.spec_ok _).2 ⟨Ac, ⟨Q, R, h0⟩, hB, hX, hSg, hS⟩
  have RI : ∀ (c rc : capability.Cap) (e : U64), capability.Cap.ptr c = ok e → H e = some .ep →
      (∀ p g, rc = .Reply p g → p ∈ Rp) →
      endpoint.receive_ipc st ar s a (L.curW s) c blk rc ⦃ s' _ =>
        ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := fun c rc e hp hH hr =>
    WP.spec_mono (endpoint.receive_ipc.ipc hA hxf s a _ c blk rc e Q R h0 hB hX hS hSg hU hc hp hH hr hNt)
      fun r hh => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hh)⟩
  have RS : ∀ n, n ∈ Nt → H n = some .ntfn → notification.receive_signal st ar s a (L.curW s) n blk ⦃ s' _ =>
      ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := fun n hn hH =>
    WP.spec_mono (notification.receive_signal.ipc hA s a _ n blk Q R h0 hB hX hS hSg hc hn hH (h3 n hn))
      fun r hh => by obtain ⟨s', a'⟩ := r; exact ⟨Ac, BlkOK.bxi (by simpa using hh)⟩
  unfold syscall.handle_recv
  step with sched.cur_thread.spec as ⟨t, et⟩
  have et' : t = L.curW s := et
  subst et'
  step with obj.Tcb.reg.spec as ⟨cptr⟩
  refine WP.spec_bind (hlk cptr) fun r hr => ?_
  split
  · rename_i c
    have hct := hr c rfl
    split
    all_goals first | exact CF _ _ | skip
    · -- an endpoint cap
      rename_i p b x rcv z w
      have hpH := hct.1 p b x rcv z w rfl
      split
      · split
        · step with obj.Tcb.reg.spec as ⟨rptr⟩
          refine WP.spec_bind (hlk rptr) fun r1 hr1 => ?_
          split
          · rename_i c1
            have hct1 := hr1 c1 rfl
            split
            all_goals first | exact CF _ _ | skip
            exact RI _ _ p rfl hpH (fun q g e => hct1.2.2 q g e)
          · split
            all_goals first | exact ok0 | exact CF _ _
        · exact RI _ _ p rfl hpH (fun q g e => by cases e)
      · exact CF _ _
    · -- a notification cap
      rename_i p b x rcv
      obtain ⟨hpN, hpH⟩ := hct.2.1 p b x rcv rfl
      refine WP.spec_bind (obj.Ntfn.bound_tcb.val s p) fun bd _ => ?_
      split
      · split
        · split
          · exact CF _ _
          · exact RS p hpN hpH
        · exact RS p hpN hpH
      · exact CF _ _
  · split
    all_goals first | exact ok0 | exact CF _ _

theorem obj.Tcb.set_fault_w0.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_w0 st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3384#u64) v ⦄ := by
  unfold obj.Tcb.set_fault_w0; step*; simp_all

theorem obj.Tcb.set_fault_w1.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_w1 st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3392#u64) v ⦄ := by
  unfold obj.Tcb.set_fault_w1; step*; simp_all

theorem obj.Tcb.set_fault_w2.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_fault_w2 st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3400#u64) v ⦄ := by
  unfold obj.Tcb.set_fault_w2; step*; simp_all

theorem obj.Tcb.set_lf_type.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_lf_type st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3408#u64) v ⦄ := by
  unfold obj.Tcb.set_lf_type; step*; simp_all

theorem obj.Tcb.set_lf_w0.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_lf_w0 st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3416#u64) v ⦄ := by
  unfold obj.Tcb.set_lf_w0; step*; simp_all

theorem obj.Tcb.set_lf_w1.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_lf_w1 st t s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 3424#u64) v ⦄ := by
  unfold obj.Tcb.set_lf_w1; step*; simp_all

/-- A write of a fault word of a TCB keeps the invariants, a thread's ability
to block and `UserOK`. -/
theorem faultW_step {U : Set U64} {s : S} {t t0 K v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t0) (ht : t ∈ T)
    (hK : 3376 ≤ K.val) (hK' : K.val < 3432) (hK8 : K.val % 8 = 0) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      UserOK st T Cs Ω H U (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      CanBlock st T Ac (L.wr s (core.num.U64.wrapping_add t K) v) t0 := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hN := h0.nodes _ h0.cur
  obtain ⟨b1, b2⟩ := bx_field (K := K) (v := v) h0 hB hX hSg.sub ht (by omega) hK8 (by omega) (by omega)
  have ha := field_aligned hta (by omega : K.val < 4096) hK8
  have fk : ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → K'.val ≠ K.val →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add t0 K') =
        L.mem s (core.num.U64.wrapping_add t0 K') := fun K' h1 h2 hne =>
    L.mem_wr_ne ha (field_aligned (hT t0 hc.mem) h1 h2) (fun e => field_ne hta (hT t0 hc.mem) (by omega) h1
      (fun _ => fun e' => hne e'.symm) (UScalar.eq_of_val_eq e))
  have ani := ani_field (v := v) hT hN ht (by omega : K.val < 4096) hK8
  refine ⟨⟨⟨Q, R, inv_wr_field h0 ht (by omega) hK8 (by omega)⟩, b1, b2,
    SCsOK.field h0 hS hX ht (by omega) hK8 (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩,
    hU.ksb (L.ksb_wr _ _ _), ⟨hc.mem, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [stA_eq, fk _ (by simp) (by simp) (by simp; omega), ← stA_eq]; exact hc.nb
  · rw [stA_eq, fk _ (by simp) (by simp) (by simp; omega), ← stA_eq]; exact hc.nrp
  · rw [inqA_eq, fk _ (by simp) (by simp) (by simp; omega), ← inqA_eq]; exact hc.nq
  · rw [inqA_eq, fk _ (by simp) (by simp) (by simp; omega), ← inqA_eq]; exact hc.nr
  · rw [ani.1]; exact hc.na
  · rw [ani.2.1]; exact hc.ni
  · rw [scA_eq, fk _ (by simp) (by simp) (by simp; omega), ← scA_eq]; exact hc.ac

/-- seL4 `setFault`: the fault (and lookup-failure) words of `t`. -/
theorem faults.set_fault.blk {U : Set U64} (s : S) (t : obj.Tcb) (f : error.Fault) {t0 : U64}
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t0) :
    faults.set_fault st s t f ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      UserOK st T Cs Ω H U s' ∧ CanBlock st T Ac s' t0 ⦄ := by
  have W : ∀ {s₁ : S} (K v : U64), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ ∧ UserOK st T Cs Ω H U s₁ ∧
      CanBlock st T Ac s₁ t0 → 3376 ≤ K.val → K.val < 3432 → K.val % 8 = 0 →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s₁ (core.num.U64.wrapping_add t K) v) ∧
        UserOK st T Cs Ω H U (L.wr s₁ (core.num.U64.wrapping_add t K) v) ∧
        CanBlock st T Ac (L.wr s₁ (core.num.U64.wrapping_add t K) v) t0 :=
    fun K v hh h1 h2 h3 => faultW_step hh.1 hh.2.1 hh.2.2 ht h1 h2 h3
  have tail : ∀ (s₁ : S) (ty w0 w1 w2 : U64), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s₁ ∧ UserOK st T Cs Ω H U s₁ ∧
      CanBlock st T Ac s₁ t0 → (do
        let s2 ← obj.Tcb.set_fault_type st t s₁ ty
        let s3 ← obj.Tcb.set_fault_w0 st t s2 w0
        let s4 ← obj.Tcb.set_fault_w1 st t s3 w1
        obj.Tcb.set_fault_w2 st t s4 w2) ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          UserOK st T Cs Ω H U s' ∧ CanBlock st T Ac s' t0 ⦄ := by
    intro s₁ ty w0 w1 w2 hh
    refine WP.spec_bind (obj.Tcb.set_fault_type.spec s₁ t ty) fun s2 e2 => ?_
    subst e2
    have h2 := W (s₁ := s₁) 3376#u64 ty hh (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w0.wr _ t w0) fun s3 e3 => ?_
    subst e3
    have h3 := W 3384#u64 w0 h2 (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w1.wr _ t w1) fun s4 e4 => ?_
    subst e4
    have h4 := W 3392#u64 w1 h3 (by simp) (by simp) (by simp)
    exact WP.spec_mono (obj.Tcb.set_fault_w2.wr _ t w2) fun s5 e5 => by
      subst e5; exact W 3400#u64 w2 h4 (by simp) (by simp) (by simp)
  unfold faults.set_fault
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 × U64 =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ UserOK st T Cs Ω H U r.1 ∧ CanBlock st T Ac r.1 t0) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨h, hU, hc⟩ | skip
    · refine WP.spec_bind (P0.error.LookupFault.encode.p0 _) ?_
      rintro ⟨lt, l0, l1⟩ -
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (obj.Tcb.set_lf_type.wr s t lt) fun s2 e2 => ?_
      subst e2
      have h2 := W (s₁ := s) 3408#u64 lt ⟨h, hU, hc⟩ (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w0.wr _ t l0) fun s3 e3 => ?_
      subst e3
      have h3 := W 3416#u64 l0 h2 (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w1.wr _ t l1) fun s4 e4 => ?_
      subst e4
      have h4 := W 3424#u64 l1 h3 (by simp) (by simp) (by simp)
      refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ => (WP.spec_ok _).2 h4
      split <;> exact (WP.spec_ok _).2 trivial
    · refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ => (WP.spec_ok _).2 ⟨h, hU, hc⟩
      split <;> exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, ty, w0, w1, w2⟩ hh
    try simp only [uncurry_apply_pair]
    exact tail s1 ty w0 w1 w2 hh

/-- seL4 `handleTimeout`: the fault goes to the thread's timeout handler as a
fault IPC (`send_fault_ipc`, no donation), if the handler cap is an
endpoint.  From the hypotheses at the call: the handler cap is typed, the
thread can block, `UserOK` and `XferOK`. -/
theorem faults.handle_timeout.bxi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U) {Ac : Set U64} (s : S) (a : A) (t : obj.Tcb) (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) :
    faults.handle_timeout st ar s a t f ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have ht := hc.mem
  unfold faults.handle_timeout
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 h | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (faults.set_fault.blk s t f h ht hU hc) ?_
    rintro s1 ⟨h1, hU1, hc1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.ipc hA hxf s1 a true false b g gr false t p Q1 R1 q1 hB1 hX1 hS1 hSg1
      hU1 hc1 (fun e => by cases e) hpH) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 (by simpa using h2)
  · rintro ⟨x, s2, a2⟩ h2
    exact (WP.spec_ok _).2 h2


/-- `set_fault` writes only `t`'s fault and lookup-failure fields, so every
thread's `SC` field is kept. -/
theorem faults.set_fault.sc (s : S) (t : obj.Tcb) (f : error.Fault) (hT : TcbPlaced T) (ht : t ∈ T) :
    faults.set_fault st s t f ⦃ s' => L.mem s' (scA t) = L.mem s (scA t) ⦄ := by
  have W : ∀ {s₁ : S} (K v : U64), L.mem s₁ (scA t) = L.mem s (scA t) → 3376 ≤ K.val → K.val < 3432 →
      K.val % 8 = 0 → L.mem (L.wr s₁ (core.num.U64.wrapping_add t K) v) (scA t) = L.mem s (scA t) :=
    fun K v e h1 h2 h3 => by
      rw [← e, scA_eq]
      exact L.mem_wr_ne (field_aligned (hT t ht) (by omega) h3) (field_aligned (hT t ht) (by simp) (by simp))
        (fun e' => field_ne (hT t ht) (hT t ht) (by omega) (by simp) (fun _ => by simp; omega)
          (UScalar.eq_of_val_eq e'))
  unfold faults.set_fault
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 × U64 => L.mem r.1 (scA t) = L.mem s (scA t)) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 (rfl : L.mem s (scA t) = L.mem s (scA t)) | skip
    · refine WP.spec_bind (P0.error.LookupFault.encode.p0 _) ?_
      rintro ⟨lt, l0, l1⟩ -
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (obj.Tcb.set_lf_type.wr s t lt) fun s2 e2 => ?_
      subst e2
      have h2 := W (s₁ := s) 3408#u64 lt rfl (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w0.wr _ t l0) fun s3 e3 => ?_
      subst e3
      have h3 := W 3416#u64 l0 h2 (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w1.wr _ t l1) fun s4 e4 => ?_
      subst e4
      have h4 := W 3424#u64 l1 h3 (by simp) (by simp) (by simp)
      refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ => (WP.spec_ok _).2 h4
      split <;> exact (WP.spec_ok _).2 trivial
    · refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ =>
        (WP.spec_ok _).2 (rfl : L.mem s (scA t) = L.mem s (scA t))
      split <;> exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, ty, w0, w1, w2⟩ hh
    try simp only [uncurry_apply_pair]
    simp only at hh
    refine WP.spec_bind (obj.Tcb.set_fault_type.spec s1 t ty) fun s2 e2 => ?_
    subst e2
    have h2 := W (s₁ := s1) 3376#u64 ty hh (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w0.wr _ t w0) fun s3 e3 => ?_
    subst e3
    have h3 := W 3384#u64 w0 h2 (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w1.wr _ t w1) fun s4 e4 => ?_
    subst e4
    have h4 := W 3392#u64 w1 h3 (by simp) (by simp) (by simp)
    exact WP.spec_mono (obj.Tcb.set_fault_w2.wr _ t w2) fun s5 e5 => by
      subst e5; exact W 3400#u64 w2 h4 (by simp) (by simp) (by simp)

/-- seL4 `handleFault`: a fault IPC to the thread's fault handler when it is
an endpoint cap (donating the thread's SC if it has one), else the fault is
recorded and the thread made inactive.  From the hypotheses at the call:
the handler cap is typed, the thread can block, `UserOK` and `XferOK`. -/
theorem faults.handle_fault.bxi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U) {Ac : Set U64} (s : S) (a : A) (t : obj.Tcb) (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) :
    faults.handle_fault st ar s a t f ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  have ht := hc.mem
  unfold faults.handle_fault
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧
      (r.1 = false → r.2.1 = s)) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨h, fun _ => rfl⟩ | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.sc s t f h.1.choose_spec.choose_spec.tcbs ht)) ?_
    rintro s1 ⟨⟨h1, hU1, hc1⟩, sc1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.ipc hA hxf s1 a true false b g gr (i != 0#u64) t p Q1 R1 q1 hB1 hX1
      hS1 hSg1 hU1 hc1 (fun e => ?_) hpH) ?_
    · have hi : i ≠ 0#u64 := by simpa using e
      rw [sc1, ← ei]; exact hi
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 ⟨by simpa using h2, fun e => by cases e⟩
  · rintro ⟨b, s2, a2⟩ ⟨h2, e2⟩
    try simp only [WP.uncurry'_pair] at e2
    simp only [uncurry_apply_pair]
    split
    · exact (WP.spec_ok _).2 h2
    · rename_i hb
      have e2' : s2 = s := e2 (by simpa using hb)
      subst e2'
      refine WP.spec_bind (faults.set_fault.blk s2 t f h2 ht hU hc) ?_
      rintro s3 ⟨h3, -, hc3⟩
      obtain ⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩ := h3
      refine WP.spec_bind (sts_all s3 t _ Q3 R3 q3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne
        (Or.inr hc3.nb) (hX3.noref (q3.tcbs t ht) hc3.nrp (fun e => hc3.nb (Or.inr (Or.inl e))))
        ⟨fun c hc' p hp hm => absurd hm (q3.notQ ht hc3.nq hc' hp), fun c hc' hm => absurd hm (q3.notR ht hc3.nr hc'),
          fun e => absurd e hc3.na⟩) ?_
      rintro s4 ⟨h4, hB4, hX4, hS4, hSg4, -, -⟩
      exact (WP.spec_ok _).2 ⟨⟨Q3, R3, h4.congrX empty_congr⟩, hB4, hX4, hS4, hSg4⟩

end

end Fl4Proofs.P1
