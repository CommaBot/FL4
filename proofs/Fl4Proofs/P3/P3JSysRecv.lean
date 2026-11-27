/-
P3 (p3J gen 28): **the notification receive (`SysRecv` / `SysWait` / `SysNBRecv` / `SysNBWait` on a notification
cap) with a projection footprint** — FL4's `notification.receive_signal` writes only `ProjW H Cs s`, under P1's
invariants over the sets of `H` (P1 EntryXG's `receive_signal.xg` hypotheses, its walk re-run with `ProjW` for
`XG`):

* idle / waiting, polling: the `BADGE` register (a TCB word of `H`);
* idle / waiting, blocking: P3JRecvN's `ntfn_block.footN0` (`KWN ∅ False`, inside `ProjW` by `kwN_projW`);
* active: the `BADGE` register, the notification's state word (an `H` notification), P2's
  `maybe_donate_sched_context.ff` at `Kp = Il = Ks = ∅`, `U = ∅` (`ffoot_projW`: `FireW`'s `KW`/`DbgW` words
  without the node identity words, or a donation word — a TCB's `SC`/`AFFINITY` word or an SC's `TCB` word), and
  `unblock_check` (P1 `unblock_check.fr`: the SC's refill ring and the current node's `REPROGRAM` word,
  `unblock_projW`).

Glue: `ffoot_projW`, `tcbF_projW`. Top: **`recvSignalProjW`**. No premise; no sorry. New module; no existing
statement changed.
-/
import Fl4Proofs.P3.P3JRecvN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Mc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {H : P1.Heap} {Cs : Set U64}

/-- A word at offset `K < 4096` of a TCB of `H` is a `ProjW` word. -/
theorem tcbF_projW (hH : P1.HeapOK H) {s : S} {y K : U64} (hy : y ∈ P1.Heap.tcbs H) (hK : K.val < 4096) :
    ProjW (L := L) H Cs s (core.num.U64.wrapping_add y K) :=
  obj_projW hH (k := .tcb) hy (by simp only [P1.HKind.bits]; omega)

/-- **P2's `FireW` at `Kp = Il = Ks = ∅`, `U = ∅`, over `H`'s sets, is inside `ProjW`** (module docstring). -/
theorem ffoot_projW (hH : P1.HeapOK H) {s : S} (hNP : ∀ c ∈ Cs, NodePlaced st (P1.Heap.tcbs H) s c)
    (hO : ObjsOK st (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H) (P1.Heap.ntfns H)
      (P1.Heap.scBits H) s) {b : U64}
    (hb : Fl4Proofs.P2.Stall.FireW st ∅ ∅ ∅ (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (EH H) ∅ s b) :
    ProjW (L := L) H Cs s b := by
  rcases hb with ⟨hw, hn⟩ | hd
  · have hi : ¬ Fl4Proofs.P1.IdN st False Cs s b := by
      rintro ⟨c, hc, o, ho, e⟩
      refine hn (Or.inl ⟨c, hc, o, ?_, e⟩)
      rcases ho with e1 | e1 | e1 | ⟨h, -⟩
      · exact Or.inl e1
      · exact Or.inr (Or.inl e1)
      · exact Or.inr (Or.inr (Or.inl e1))
      · exact h.elim
    rcases hw with hk | hd | hu
    · exact kw_projW hH hNP hk hi
    · exact dbgW_projW hH hNP hd
    · exact absurd hu (Set.notMem_empty _)
  · rcases hd with ⟨y, hy, -, -, rfl | rfl⟩ | ⟨k, hk, -, rfl⟩
    · rw [scA_eq]; exact tcbF_projW hH hy (by simp)
    · rw [affA_eq]; exact tcbF_projW hH hy (by simp)
    · obtain ⟨hP, hz⟩ := hO.sc k hk
      have hv := scTcbA_val (c := k) hP hz
      have h7 : 2 ^ 7 ≤ 2 ^ P1.Heap.scBits H k := Nat.pow_le_pow_right (by norm_num) hz
      have hfit := hP.2
      exact sc_projW hk ⟨by rw [hv]; omega, by rw [hv]; omega⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {H : P1.Heap} {Cs Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- `unblock_check` of a bound SC writes only `ProjW` (P1 `unblock_check.kw`'s words, module docstring). -/
theorem unblock_projW (hH : P1.HeapOK H) {X : Set U64} (s : S) (t i : U64) {Q : U64 → U64 → List U64}
    {R : U64 → List U64}
    (h : SchedQueuesInvX st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H X s Q R)
    (hX : XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) s)
    (hS : SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s)
    (ht : t ∈ P1.Heap.tcbs H) (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64) (hiA : i ∈ Ac) :
    sporadic.unblock_check st s i ⦃ s' => P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ := by
  have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
  rw [← i_post] at hiS
  have hW : RefillsWF st s i (P1.Heap.scBits H i) := hS.wf hiS hiA
  have hSCin : SCin st s (P1.Heap.omega H) i (P1.Heap.scBits H i) := ⟨hW, hX.1.scW i hiS⟩
  have hN' := h.nodes _ h.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (P1.Heap.scBits H i) :=
    hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
  exact WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w => w.mono fun b hb => by
    rcases hb with hb | rfl
    · exact sc_projW hiS hb.inSC
    · unfold LawfulStore.nodeA
      exact node_projW hN' h.cur (by rw [rp]; omega) (by rw [rp]; omega) (by rw [rp]; omega)

set_option maxHeartbeats 8000000 in
/-- **`receive_signal` writes only `ProjW`** under P1's invariants over `H`'s sets (module docstring). -/
theorem recvSignalProjW (hA : P0.ArchTotal ar) (hH : P1.HeapOK H)
    (s : S) (a : A) (t n : U64) (blocking : Bool) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H s Q R)
    (hB : BoundInv st (P1.Heap.tcbs H) Ac s)
    (hX : XInv st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.replies H) (P1.Heap.scs H)
      (P1.Heap.ntfns H) (P1.Heap.scBits H) s)
    (hS : SCsOK st (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) Ac s)
    (hSg : SgOK st (P1.Heap.omega H) (P1.Heap.frame H) s) (hc : CanBlock st (P1.Heap.tcbs H) Ac s t)
    (hnN : n ∈ P1.Heap.ntfns H) (hn : H n = some .ntfn) (h3 : L.epState s n ≠ 3#u64) :
    notification.receive_signal st ar s a t n blocking ⦃ s' _ =>
      P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ := by
  have ht := hc.mem
  have hT := h.tcbs
  have hta := hT t ht
  have hNP := h.nodes
  have FB : ∀ v : U64, P1.WritesIn st s (L.wr s (core.num.U64.wrapping_add t 256#u64) v) (ProjW (L := L) H Cs s) :=
    fun v => (writesIn_wr (field_aligned hta (by simp) (by simp))).mono fun b hb => by
      subst hb; exact tcbF_projW hH ht (by simp)
  by_cases e01 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64
  · have nb : (do let s1 ← obj.Tcb.set_reg st t s layout.reg.BADGE 0#u64; ok (s1, a)) ⦃ s' _ =>
        P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ := by
      refine WP.spec_bind (obj.Tcb.set_reg.badge s t 0#u64 hta) ?_
      rintro s1 rfl
      simp only [WP.spec_ok, WP.uncurry'_pair]
      exact FB _
    have blk' : (do
        let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
        let s2 ← obj.Tcb.set_block_obj st t s1 n
        let s3 ← sched.schedule_tcb st s2 t
        let s4 ← notification.ntfn_append st s3 n t
        let s5 ← notification.maybe_return_sched_context st s4 n t
        ok (s5, a)) ⦃ s' _ => P1.WritesIn st s s' (ProjW (L := L) H Cs s) ⦄ :=
      WP.spec_mono (ntfn_block.footN0 s a t n Q R h hB hX hS hSg hc hc.ni hn e01) fun r f => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at f ⊢
        exact (WritesA.w f).mono fun _ hb => kwN_projW hH hNP hb
    unfold notification.receive_signal
    step with obj.Ntfn.state.spec as ⟨v, hv⟩
    split
    · split
      · exact blk'
      · exact nb
    · split
      · split
        · exact blk'
        · exact nb
      · exfalso
        rename_i h1 h2
        rw [ntfn_idle_val] at h1; rw [ntfn_wait_val'] at h2
        rcases e01 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction
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
  have hnΩ : ntfnScA n ∈ P1.Heap.omega H := hSg.sub _ (hX.1.ntW n hnN)
  have hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (ntfnScA n) ∈ P1.Heap.scs H ∧
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
  have g1 := FB b1
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
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b3⟩
  split
  · step with sporadic.sc_sporadic.spec as ⟨b2, eb2⟩
    split
    · rename_i hb2
      have hi1S : i1 ∈ P1.Heap.scs H := (hX3.2.2.bound t ht (by rw [← ei1']; exact (eb2 hb2).1)).1 |> fun h => by
        rw [← ei1'] at h; exact h
      refine WP.spec_bind (unblock_projW hH s3 t i1 h3' hX3 hS3 ht ei1' (eb2 hb2).1
        (hS3.spor i1 hi1S (eb2 hb2).2)) fun s5 F5 => ?_
      exact (WP.spec_ok _).2 (g3.projW_trans F5)
    · exact ok3
  · exact ok3

end

end Fl4Proofs.P3.Mc
