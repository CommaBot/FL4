/-
# P2 (line p2sl): `handle_syscall_local` writes only its footprint

The write-footprint lemmas of the syscall entry beside the serial gate, at
its entry state `s` (where fl4-sync's `local_syscall` holds its locks), with
the footprint `FootSl` of `P2/FootSlDefs.lean`:

* `sl_decline_foot` (FootSlDefs): a declined run wrote at most the
  current thread's `FAULT_IP` and the node's two timestamp words;
* **`sl_trap_foot`**: an accepted run of a thread that traps its syscalls
  (the fault fast path) writes only `FootSl` words of `s`, with the
  endpoint `ep` and reply object `r` fl4-sync locked (`SlLocks`): the prefix
  (`sl_pre_foot`), then `fastpath.fault` from the prefix's state `X`
  (`sl_fault_foot`), whose footprint at `X` is one at `s`
  (`FootSl.pre_mono`: the prefix writes no TCB word but `FAULT_IP` and no
  node word but `CUR_TIME` / `CONSUMED`, which `FootSl` does not read);
* the ReplyRecv arm (`fastpath.reply_recv_found`) is not covered here yet.

Hypotheses of `sl_trap_foot` at `s`: the TCBs and the node placed, the
current thread a TCB; at the state `X` the prefix reaches (as P1 states its
fast-path facts, `FastFaultPre`, at the state `fastpath.fault` is entered):
P1's `BXI`, the handler blocked on receive, `FaultEntAt`, and

* `hy0` [J]: the handler yields to no SC (`FootSlFault`'s module docstring).
-/
import Fl4Proofs.P2.FootSlFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st] (ar : machine.Arch A)

theorem SlReach.mem {m : U64 → U64} {T : Set U64} {ep y : U64} (h : SlReach m T ep y) : y ∈ T := by
  cases h <;> assumption

/-- Reachability along `EP_NEXT` carries over between memories agreeing on
the head word and the queue links of `T`. -/
theorem SlReach.congr {m m' : U64 → U64} {T : Set U64} {ep y : U64}
    (hh : m (epHeadA ep) = m' (epHeadA ep)) (hn : ∀ y ∈ T, m (nextA .Ep y) = m' (nextA .Ep y))
    (h : SlReach m T ep y) : SlReach m' T ep y := by
  induction h with
  | head h1 => rw [hh] at h1 ⊢; exact SlReach.head h1
  | @next y hr h1 ih => rw [hn y hr.mem] at h1 ⊢; exact SlReach.next ih h1

theorem sbA8 {y : U64} (h : TcbAddr y) :
    core.num.U64.wrapping_add (sbA y) 8#u64 = core.num.U64.wrapping_add y 72#u64 := by
  apply UScalar.eq_of_val_eq
  rw [field_val h (by simp), core.num.U64.wrapping_add_val_eq, sbA_val h]
  have := h.fits
  simp [U64.size_def, U64.numBits]
  omega

/-- **The footprint is read through TCB words other than `FAULT_IP`, the
current thread and SC, and the locked endpoint's head**: a state agreeing
with `s` on those has its footprint inside `s`'s. -/
theorem FootSl.pre_mono {T : Set U64} {Z : U64 → Nat} {s X : S} {ep r b : U64} (hT : TcbPlaced T)
    (hk : L.ksb X = L.ksb s) (hc : L.cpu X = L.cpu s)
    (htcb : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hcur : L.curW X = L.curW s) (hcsc : L.cscW X = L.cscW s)
    (heph : L.mem X (epHeadA ep) = L.mem s (epHeadA ep))
    (h : FootSl st T Z X ep r b) : FootSl st T Z s ep r b := by
  have on : ∀ y, SlOn st T X y → SlOn st T s y := by
    rintro y ⟨hy, ha | hcu⟩
    · refine ⟨hy, Or.inl ?_⟩
      have e := htcb y hy 3520#u64 (by simp) (by simp) (by simp)
      rw [← hc]; exact e.symm.trans ha
    · exact ⟨hy, Or.inr (hcu.trans hcur)⟩
  have blk : ∀ y ∈ T, SlBlk st s y → SlBlk st X y := by
    intro y hy hb
    have e : L.mem X (stA y) = L.mem s (stA y) := by rw [stA_eq]; exact htcb y hy _ (by simp) (by simp) (by simp)
    unfold SlBlk at hb ⊢; rw [e]; exact hb
  rcases h with ⟨o, ho, h8, rfl⟩ | ⟨y, hy, K, hK, e, hT', hb⟩ | ⟨y, hy, w, buf, hl, h0, i, hi, e⟩ |
    ⟨c, hcs, hin⟩ | hlk | ⟨y, hr, e⟩
  · exact FootSl.node ⟨o, ho, h8, by rw [hc, nodeAt_of_ksb hk]⟩
  · exact FootSl.tcb ⟨y, on y hy, K, hK, e, hT', fun h => hb (blk y hy.1 h)⟩
  · have hy' := hT y hy.1
    have el : msg.lookup_ipc_buffer st X w y = msg.lookup_ipc_buffer st s w y := by
      refine lookup_buf_agreeB w (htcb y hy.1 3512#u64 (by simp) (by simp) (by simp)) ?_ ?_
      · rw [sbA_field hy']; exact htcb y hy.1 64#u64 (by simp) (by simp) (by simp)
      · rw [sbA8 hy']; exact htcb y hy.1 72#u64 (by simp) (by simp) (by simp)
    exact FootSl.buf ⟨y, on y hy, w, buf, el ▸ hl, h0, i, hi, e⟩
  · refine FootSl.sc ⟨c, ?_, hin⟩
    rcases hcs with rfl | ⟨y, hy, hsc, h0⟩
    · exact Or.inl hcsc
    · refine Or.inr ⟨y, on y hy, ?_, h0⟩
      rw [← hsc, scA_eq]; exact (htcb y hy.1 _ (by simp) (by simp) (by simp)).symm
  · exact FootSl.lk hlk
  · refine FootSl.q ⟨y, SlReach.congr heph (fun y hy => ?_) hr, e⟩
    show L.mem X (core.num.U64.wrapping_add y 3496#u64) = L.mem s (core.num.U64.wrapping_add y 3496#u64)
    exact htcb y hy _ (by simp) (by simp) (by simp)

set_option maxHeartbeats 4000000 in
/-- **An accepted trapped syscall beside the gate writes only its footprint**
(module docstring). -/
theorem sl_trap_foot {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {n : I64} {found : U64 × U64} {ep r : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hI : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X)
    (hrecv : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (stA dest) = sched.TS_BLOCKED_ON_RECV)
    (hF : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → FaultEntAt (L := L) T Cs Ω U Sg Rp X (L.curW s))
    (hy0 : ∀ X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
      FaultChecks st X (L.curW s) ptr badge dest r → L.mem X (yieldA dest) = 0#u64)
    (htrap : ∃ f, obj.Tcb.flags st (L.curW s) s = ok f ∧
      (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (hL : SlLocks st s n found ep r)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    WritesIn st s s' (FootSl st T Z s ep r) := by
  obtain ⟨f0, ef0, hf0⟩ := htrap
  have ht' := hT _ hcT
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
  rw [if_pos hf0] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte, if_pos hf0] at h
  try simp only [lift, bind_ok] at h
  have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
  have wpre := sl_pre_foot hA hT hN hcT hP
  obtain ⟨ptr, badge, dest, r0, hc, w⟩ :=
    sl_fault_foot (Z := Z) ar hA (hI _ _ hP) (hrecv _ _ hP) (hF _ _ hP) (hy0 _ _ hP) h
  obtain ⟨-, rest, E⟩ := (hF _ _ hP).2 ptr badge dest r0 hc
  -- the prefix's state agrees with `s` but on `FAULT_IP` and the two timestamp words
  have e1 := set_fip_wr ht' es1
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  obtain ⟨n1, -, e2⟩ := ut_now ar hA hN1 eu
  try simp only at e2
  obtain ⟨hct, hcn, -⟩ := ct_cn hN
  obtain ⟨KF, hKF, eKF⟩ := regA_eq ht' (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by rw [eKF]; exact field_aligned ht' (by omega) (by omega)
  have ag : ∀ b, Aligned b → b ≠ regA (L.curW s) layout.reg.FAULT_IP → b ≠ ctA (L := L) s → b ≠ cnA (L := L) s →
      L.mem s2 b = L.mem s b := by
    intro b hb h1 h2 h3
    rw [e2, utW_mem hN1 n1 hb (by rw [e1, ctA_wr]; exact h2) (by rw [e1, cnA_wr]; exact h3), e1,
      mem_wr_ne' aF hb (Ne.symm h1)]
  have hk2 : L.ksb s2 = L.ksb s := by rw [e2, utW_ksb, e1, L.ksb_wr]
  have hc2 : L.cpu s2 = L.cpu s := by rw [e2, utW_cpu, e1, LawfulStore.cpu_wr]
  have vct : (ctA (L := L) s).val = L.nodeBase s (L.cpu s) + 48 := by
    unfold ctA; rw [nodeAt_val hN (by simp [layout.node.CUR_TIME])]; simp [layout.node.CUR_TIME]
  have vcn : (cnA (L := L) s).val = L.nodeBase s (L.cpu s) + 40 := by
    unfold cnA; rw [nodeAt_val hN (by simp [layout.node.CONSUMED])]; simp [layout.node.CONSUMED]
  have agT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK h8 h392
    have hy' := hT y hy
    have vb := field_val hy' hK
    have nd := hN.disj y hy
    refine ag _ (field_aligned hy' hK h8) ?_ ?_ ?_
    · rw [eKF]; exact field_ne hy' ht' hK (by omega) (fun _ => by omega)
    · intro e; have e' := congrArg UScalar.val e; omega
    · intro e; have e' := congrArg UScalar.val e; omega
  have agN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem s2 (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8 h48 h40
    have vo := nodeAt_val hN ho
    refine ag _ (nodeAt_aligned hN ho h8) ?_ ?_ ?_
    · rw [eKF]; exact node_ne_field hN ho hcT ht' (by omega)
    · intro e; have e' := congrArg UScalar.val e; omega
    · intro e; have e' := congrArg UScalar.val e; omega
  have hcur2 : L.curW s2 = L.curW s := by
    show L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) = _
    rw [hc2, nodeAt_of_ksb hk2]; exact agN _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hcsc2 : L.cscW s2 = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [hc2, nodeAt_of_ksb hk2]; exact agN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
      (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  -- the endpoint: its words are no TCB or node words
  have hE := E.hE
  have ea := hE.align
  obtain ⟨vh, -⟩ := sl_ep_vals hE
  have heph : L.mem s2 (epHeadA ptr) = L.mem s (epHeadA ptr) := by
    have hEN := E.hEN.1 _ E.hcC
    have nb : L.nodeBase s2 (L.cpu s2) = L.nodeBase s (L.cpu s) := by
      simp only [LawfulStore.nodeBase, hk2, hc2]
    rw [nb] at hEN
    refine ag _ (ep_aligned hE).1 ?_ ?_ ?_
    · rw [eKF]; exact (sl_ep_ne_field hE hcT ht' (by omega)).1
    · intro e; have e' := congrArg UScalar.val e; rw [vh, vct] at e'; omega
    · intro e; have e' := congrArg UScalar.val e; rw [vh, vcn] at e'; omega
  -- the locked objects are `ptr` and `r0`
  rcases hL with ⟨f1, ef1, hf1, sl, badge', x', y', g', gr', esl, ecap, hr⟩ | ⟨f1, ef1, hf1, -⟩
  swap
  · rw [ok_inj_ff (ef1.symm.trans ef0)] at hf1; exact absurd hf0 hf1
  obtain ⟨sl2, x2, y2, g2, gr2, esl2, ecap2, -⟩ := hc.cap
  have esl' : sl2 = sl := ok_inj_ff (esl2.symm.trans esl)
  subst esl'
  have hs : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER =
      ok (core.num.U64.wrapping_add (L.curW s)
        (core.num.U64.wrapping_mul layout.tcb.SLOT_FAULT_HANDLER layout.cte.SIZE)) := by
    simp [obj.Tcb.slot, lift]
  have vsl : (core.num.U64.wrapping_add (L.curW s)
      (core.num.U64.wrapping_mul layout.tcb.SLOT_FAULT_HANDLER layout.cte.SIZE)).val = (L.curW s).val + 96 := by
    have := ht'.fits
    unfold layout.tcb.SLOT_FAULT_HANDLER layout.cte.SIZE
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    all_goals omega
  have hsl : sl2 = core.num.U64.wrapping_add (L.curW s) 96#u64 := by
    rw [hs] at esl
    rw [← ok_inj_ff esl]
    apply UScalar.eq_of_val_eq
    rw [vsl, field_val ht' (by simp)]
    simp
  have hsl8 : core.num.U64.wrapping_add sl2 8#u64 = core.num.U64.wrapping_add (L.curW s) 104#u64 := by
    rw [hsl]; apply UScalar.eq_of_val_eq
    rw [core.num.U64.wrapping_add_val_eq, field_val ht' (by simp), field_val ht' (by simp)]
    have := ht'.fits
    simp [U64.size_def, U64.numBits]; omega
  have ecs : obj.Slot.cap st sl2 s2 = obj.Slot.cap st sl2 s := by
    unfold obj.Slot.cap
    rw [L.read_pair_eq, L.read_pair_eq, hsl8]
    rw [hsl, agT _ hcT 96#u64 (by simp) (by simp) (by simp), agT _ hcT 104#u64 (by simp) (by simp) (by simp)]
  rw [ecs, ecap] at ecap2
  have hpe : ptr = ep := by
    have := ok_inj_ff ecap2
    simp only [capability.Cap.Endpoint.injEq] at this
    exact this.1.symm
  subst hpe
  have hhd : L.mem s (epHeadA ptr) = dest := by
    have h1 := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s2 ptr)] at h1; rw [← heph]; exact ok_inj_ff h1
  have hdT : dest ∈ T := E.hq.mem dest (by simp)
  have hr0 : r0 = r := by
    have h1 := hc.reply
    rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) s2 dest)] at h1
    rw [hr, hhd, ← ok_inj_ff h1]
    exact (agT dest hdT 3360#u64 (by simp) (by simp) (by simp))
  subst hr0
  -- assemble
  refine (wpre.trans (w.mono fun b hb => FootSl.pre_mono hT hk2 hc2 agT hcur2 hcsc2 heph hb)).mono ?_
  intro b hb
  rcases hb with hb | hb
  · exact sl_pre_sub hT hcT hb
  · exact hb

end

end Fl4Proofs.P2
