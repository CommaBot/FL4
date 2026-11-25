/-
# P2 (line p2sl): the accepted ReplyRecv arm of `handle_syscall_local` at its entry

`sl_rr_entry_foot`: an accepted `handle_syscall_local` of a thread that does
not trap its syscalls (the ReplyRecv arm, fl4-sync's `found = (r, ep)`,
`SlLocks`) writes only `FootSl` words of the entry state `s`: the prefix
(`sl_pre_foot`), then `fastpath.reply_recv_found` from the prefix's state `X`
(`sl_rr_foot`), whose footprint at `X` is one at `s` (`FootSl.pre_mono`, with
the prefix's agreement facts `sl_pre_agree`).

Hypotheses at `s`: the TCBs and the node placed, the current thread a TCB;
at the state `X` the prefix reaches: P1's `BXI`, the placement bundle `RRPl`
of an accepted run, fl4-sync's check that the reply object has no neighbours,
and

* `hy0` [J]: the reply's thread yields to no SC (`FootSlRR`'s module docstring).
-/
import Fl4Proofs.P2.FootSlRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st] (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The prefix's state agrees with the entry state** on everything
`FootSl` reads: the kernel base, the core, the TCB words other than
`FAULT_IP`, the current thread and SC, and a placed endpoint's head. -/
theorem sl_pre_agree {T Cs : Set U64} (hA : P0.ArchTotal ar) {s X : S} {a a1 : A}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hP : LocalPre (st := st) ar s a (X, a1)) :
    L.ksb X = L.ksb s ∧ L.cpu X = L.cpu s ∧
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    L.curW X = L.curW s ∧ L.cscW X = L.cscW s ∧
    (∀ ep, EpPlaced T ep → EpOutNodes st Cs X ep → L.cpu X ∈ Cs →
      L.mem X (epHeadA ep) = L.mem s (epHeadA ep)) := by
  obtain ⟨t, nx, s1, et, -, es1, eu⟩ := hP
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  have ht' := hT _ hcT
  have e1 := set_fip_wr ht' es1
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  obtain ⟨n1, -, e2⟩ := ut_now ar hA hN1 eu
  try simp only at e2
  obtain ⟨KF, hKF, eKF⟩ := regA_eq ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by rw [eKF]; exact field_aligned ht' (by omega) (by omega)
  have ag : ∀ b, Aligned b → b ≠ regA (L.curW s) layout.reg.FAULT_IP → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s →
      L.mem X b = L.mem s b := by
    intro b hb h1 h2 h3
    rw [e2, utW_mem hN1 n1 hb (by rw [e1, ctA_wr]; exact h2) (by rw [e1, cnA_wr]; exact h3), e1,
      mem_wr_ne' aF hb (Ne.symm h1)]
  have hk2 : L.ksb X = L.ksb s := by rw [e2, utW_ksb, e1, L.ksb_wr]
  have hc2 : L.cpu X = L.cpu s := by rw [e2, utW_cpu, e1, LawfulStore.cpu_wr]
  have vct : (ctA (L := L) s).val = L.nodeBase s (L.cpu s) + 48 := by
    unfold ctA; rw [nodeAt_val hN (by simp [layout.node.CUR_TIME])]; simp [layout.node.CUR_TIME]
  have vcn : (cnA (L := L) s).val = L.nodeBase s (L.cpu s) + 40 := by
    unfold cnA; rw [nodeAt_val hN (by simp [layout.node.CONSUMED])]; simp [layout.node.CONSUMED]
  have agT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK h8 h392
    have hy' := hT y hy
    have vb := field_val hy' hK
    have nd := hN.disj y hy
    refine ag _ (field_aligned hy' hK h8) ?_ ?_ ?_
    · rw [eKF]; exact field_ne hy' ht' hK (by omega) (fun _ => by omega)
    · intro e; have e' := congrArg UScalar.val e; omega
    · intro e; have e' := congrArg UScalar.val e; omega
  have agN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem X (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h48 h40
    have vo := nodeAt_val hN ho
    refine ag _ (nodeAt_aligned hN ho h8) ?_ ?_ ?_
    · rw [eKF]; exact node_ne_field hN ho hcT ht' (by omega)
    · intro e; have e' := congrArg UScalar.val e; omega
    · intro e; have e' := congrArg UScalar.val e; omega
  refine ⟨hk2, hc2, agT, ?_, ?_, ?_⟩
  · show L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) = _
    rw [hc2, nodeAt_of_ksb hk2]; exact agN _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  · unfold LawfulStore.cscW LawfulStore.nodeA
    rw [hc2, nodeAt_of_ksb hk2]; exact agN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  · intro ep hE hEN hcC
    obtain ⟨vh, -⟩ := sl_ep_vals hE
    have hEN1 := hEN.1 _ hcC
    have nb : L.nodeBase X (L.cpu X) = L.nodeBase s (L.cpu s) := by
      simp only [LawfulStore.nodeBase, hk2, hc2]
    rw [nb] at hEN1
    refine ag _ (ep_aligned hE).1 ?_ ?_ ?_
    · rw [eKF]; exact (sl_ep_ne_field hE hcT ht' (by omega)).1
    · intro e; have e' := congrArg UScalar.val e; rw [vh, vct] at e'; omega
    · intro e; have e' := congrArg UScalar.val e; rw [vh, vcn] at e'; omega

set_option maxHeartbeats 4000000 in
/-- **An accepted ReplyRecv beside the gate writes only its footprint at the
entry state** (module docstring). -/
theorem sl_rr_entry_foot {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {found : U64 × U64} {ep r : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hI : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hPl : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) r ep u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X (L.curW s) r ep u usc)
    (hrz : ∀ X a1, LocalPre (st := st) ar s a (X, a1) →
      L.mem X (rNextA r) &&& ~~~1#u64 = 0#u64 ∧ L.mem X (rPrevA r) &&& ~~~1#u64 = 0#u64)
    (hy0 : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ u usc,
      RRChecks st ar X a1 (L.curW s) r ep u usc → L.mem X (yieldA u) = 0#u64)
    (hnt : ∃ f, obj.Tcb.flags st (L.curW s) s = ok f ∧
      ¬ (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (hL : SlLocks st s n found ep r)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    WritesIn st s s' (FootSl st T Z s ep r) := by
  obtain ⟨f0, ef0, hf0⟩ := hnt
  rcases hL with ⟨f1, ef1, hf1, -⟩ | ⟨f1, -, -, hn, hfd⟩
  · rw [ok_inj_ff (ef1.symm.trans ef0)] at hf1; exact absurd hf1 hf0
  subst hn hfd
  unfold syscall.handle_syscall_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  have hi : i = f0 := ok_inj_ff (ei.symm.trans ef0)
  subst hi
  try simp only [lift, bind_ok] at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [if_neg hf0] at h
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte, if_neg hf0] at h
  have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
  have wpre := sl_pre_foot hA hT hN hcT hP
  obtain ⟨hk2, hc2, agT, hcur2, hcsc2, aep⟩ := sl_pre_agree (Cs := Cs) ar hA hT hN hcT hP
  obtain ⟨u, usc, C, -⟩ := reply_recv_found_acc st ar h
  have P := hPl _ _ hP u usc C
  have heph := aep ep P.hE P.hEN P.hcC
  have w := sl_rr_foot (Z := Z) ar hA (hI _ _ hP) (hPl _ _ hP) (hrz _ _ hP) (hy0 _ _ hP) h
  refine (wpre.trans (w.mono fun b hb => FootSl.pre_mono hT hk2 hc2 agT hcur2 hcsc2 heph hb)).mono ?_
  intro b hb
  rcases hb with hb | hb
  · exact sl_pre_sub hT hcT hb
  · exact hb

end

end Fl4Proofs.P2
