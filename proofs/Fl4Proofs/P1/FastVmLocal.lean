/-
# The page-fault entries beside the serial gate, accepted (FL4 #71, pf1 step 2)

`syscall.handle_vm_fault_local` and `syscall.handle_reply_recv_vm_local`
(fl4-sync's `local_vm_fault` / `local_syscall`) where they return `true`:

* `vm_local_triple`: every postcondition the general entry
  `syscall.handle_vm_fault` has, the local entry has on its `true` results
  (`vm_local_same`, given `VmFaultOK`);
* `rr_found_decline_of_vm`: where `reply_recv_vm_found` accepts, the #56
  `reply_recv_found` declines at the same state (its receiver's fault is a VM
  fault, not an UnknownSyscall one), so the general entry
  `syscall.handle_syscall … SysReplyRecv`, whose own fast path is
  `fastpath.reply_recv`, runs its general path (`syscall_rr_true`);
* `check_budget_restart_true` / `budget_ok_true` (a passing `budget_ok` is
  its timestamp update), `reply_caps_keep` (`reply_caps` past writes it does
  not read), `rr_prefix_keep` (the local entry's prefix keeps the current
  thread and fl4-sync's `found`);
* `rr_vm_local_same` / `rr_vm_local_triple`: an accepted
  `handle_reply_recv_vm_local` ends where `syscall.handle_syscall … SysReplyRecv`
  ends, given `RRPreAtG … VMFault`, placement facts at the entry state, the
  top's flag fact, and `found` = `reply_caps` at the entry state (fl4-sync's
  contract);
* `RRPreAtG.of_inv`: the bundle from `EntryInv` (any fault type).
-/
import Fl4Proofs.P1.FastVmDecline
import Fl4Proofs.P1.FastTailRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The VM-fault local entry where it ran: the general entry's
postconditions** (on the `true` results). -/
theorem vm_local_triple (hX : StoreExt st) (hA : P0.ArchTotal ar) {s : S} {a : A} {addr code : U64}
    {P : S × A → Prop} (hF : VmFaultOK (L := L) ar s a)
    (hG : syscall.handle_vm_fault st ar s a addr code ⦃ P ⦄) :
    syscall.handle_vm_fault_local st ar s a addr code ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.syscall.handle_vm_fault_local.p0 st ar s a addr code L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := vm_local_same ar hX hF e
  rw [hs, WP.spec_ok] at hG
  exact hG

/-- **Where `reply_recv_vm_found` accepts, `reply_recv_found` declines** at
the same state and with the same reply and endpoint: the reply's thread is the
same (`Reply.tcb`), and its fault type is `VMFault`, not `UnknownSyscall`. -/
theorem rr_found_decline_of_vm (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {t : obj.Tcb} {rptr ep : U64}
    (hv : fastpath_vm.reply_recv_vm_found st ar s a t rptr ep = ok (true, s', a')) :
    fastpath.reply_recv_found st ar s a t rptr ep = ok (false, s, a) := by
  obtain ⟨u, usc, CV, -⟩ := reply_recv_vm_found_acc st ar hv
  obtain ⟨⟨b, x, y⟩, e, -⟩ := spec_ex_fd (P0.fastpath.reply_recv_found.p0 st ar s a t rptr ep L.total hA)
  cases b
  · obtain ⟨rfl, rfl⟩ := reply_recv_found_decline st ar e
    exact e
  · obtain ⟨u', usc', C, -⟩ := reply_recv_found_acc st ar e
    have hu : u' = u := by
      have h1 := C.tcb
      rw [CV.tcb] at h1
      exact (ok_inj_ff h1).symm
    subst hu
    obtain ⟨i, hi, hc⟩ := C.uft
    obtain ⟨i', hi', hc'⟩ := CV.uft
    rw [hi] at hi'
    have hii := ok_inj_ff hi'
    subst hii
    simp only [bne_iff_ne, ne_eq, not_not] at hc hc'
    exact absurd (hc'.symm.trans hc) vm_ne_us

/-- **The general `syscall … SysReplyRecv` with its fast paths enabled, where
`fastpath.reply_recv` declines at the dispatch state, is its general path**
(the converse direction of `syscall_rr_general`, for `fast = true`). -/
theorem syscall_rr_true {s s1 s2 s' X : S} {a a2 a' a'' : A} {t nx i1 : U64}
    (et : sched.cur_thread st s = ok t) (enx : obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1)
    (ef : obj.Tcb.flags st t s1 = ok i1)
    (c1 : ¬ (i1 &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true)
    (eb : syscall.budget_ok st ar s1 a = ok (true, s2, a2))
    (hdec : fastpath.reply_recv st ar s2 a2 = ok (false, s2, a2))
    (hd : syscall.dispatch_syscall st ar s2 a2 fl4_abi.syscall.SysReplyRecv = ok (X, a''))
    (hf : syscall.finish st ar X a'' = ok (s', a')) :
    syscall.syscall st ar s a fl4_abi.syscall.SysReplyRecv true = ok (false, s', a') := by
  have c2 : ¬ fl4_abi.syscall.SysReplyRecv < fl4_abi.syscall.SYSCALL_MIN := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MIN
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  have c3 : ¬ fl4_abi.syscall.SysReplyRecv > fl4_abi.syscall.SYSCALL_MAX := by
    unfold fl4_abi.syscall.SysReplyRecv fl4_abi.syscall.SYSCALL_MAX
    first | decide | simp | (simp [IScalar.lt_equiv]) | (simp [IScalar.lt_equiv]; omega)
  unfold syscall.syscall
  rw [et]; simp only [bind_ok]
  rw [enx]; simp only [lift, bind_ok]
  rw [es1]; simp only [bind_ok]
  rw [ef]; simp only [lift, bind_ok, if_neg c1, if_neg c2, if_neg c3]
  rw [eb]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, if_true, eq_self_iff_true]
  rw [hdec]; simp only [bind_ok, uncurry_apply_pair, ↓reduceIte, Bool.false_eq_true]
  rw [hd]; simp only [bind_ok, uncurry_apply_pair]
  rw [hf]; simp only [bind_ok, uncurry_apply_pair]

/-- **A passing `budget_ok` is its timestamp update**: `check_budget_restart`
returns `true` only from the `sufficient` branch, which writes nothing. -/
theorem check_budget_restart_true {s s' : S} {a a' : A}
    (h : sched.check_budget_restart st ar s a = ok (true, s', a')) : s' = s ∧ a' = a := by
  unfold sched.check_budget_restart at h
  obtain ⟨⟨r, s1, a1⟩, e, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨ct, -, h⟩ := bind_eq_ok h
  have hr : r = true → s1 = s ∧ a1 = a := by
    intro hr0
    unfold sched.check_budget at e
    obtain ⟨sc, -, e⟩ := bind_eq_ok e
    obtain ⟨c, -, e⟩ := bind_eq_ok e
    obtain ⟨b, -, e⟩ := bind_eq_ok e
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at e
      obtain ⟨⟨s3, a3⟩, -, e⟩ := bind_eq_ok e
      try simp only [uncurry_apply_pair] at e
      have e' := ok_inj_ff e
      simp only [Prod.mk.injEq] at e'
      rw [hr0] at e'; exact absurd e'.1 (by decide)
    · simp only [↓reduceIte] at e
      obtain ⟨b1, -, e⟩ := bind_eq_ok e
      have e' := ok_inj_ff e
      simp only [Prod.mk.injEq] at e'
      exact ⟨e'.2.1.symm, e'.2.2.symm⟩
  cases r
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨b2, -, h⟩ := bind_eq_ok h
    cases b2
    · simp at h
    · simp only [↓reduceIte] at h
      obtain ⟨s4, -, h⟩ := bind_eq_ok h
      simp at h
  · simp only [↓reduceIte] at h
    have e' := ok_inj_ff h
    simp only [Prod.mk.injEq, true_and] at e'
    obtain ⟨rfl, rfl⟩ := e'
    exact hr rfl

theorem budget_ok_true {s s' : S} {a a' : A} (h : syscall.budget_ok st ar s a = ok (true, s', a')) :
    sched.update_timestamp st ar s a = ok (s', a') := by
  unfold syscall.budget_ok at h
  obtain ⟨⟨x, y⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨rfl, rfl⟩ := check_budget_restart_true ar h
  exact eu

/-- **`reply_caps` past writes it does not read**: `t`'s CSpace root slot
(words 0, 8), its `REPLY` / `CAP` registers and the cap-slot words its walks
reach (`CnOff`). -/
theorem reply_caps_keep {T Cs Sg : Set U64} {s s' : S} {t rptr ep : U64} {W : U64 → Prop}
    (ht' : TcbAddr t) (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep)))
    (hW : WritesIn st s s' W)
    (hwT : ∀ K : U64, (K.val = 0 ∨ K.val = 8 ∨ K.val = 256 + 8 * layout.reg.REPLY.val ∨
      K.val = 256 + 8 * layout.reg.CAP.val) → ¬ W (core.num.U64.wrapping_add t K))
    (hwc : ∀ b, CapSW (L := L) T Cs Sg s b → ¬ W b)
    (hCn : CnOff (L := L) T Cs Sg s t) :
    fastpath.reply_caps st s' t = ok (some (rptr, ep)) := by
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, ⟨i1, found1, b0, b1, b3, b4, hi1, hr1, hc1⟩⟩⟩ :=
    reply_caps_some st hrc
  obtain ⟨C, hC0, hcl, hWc⟩ := hCn sl root hsl hroot
  have capK : ∀ b, CapSW (L := L) T Cs Sg s b → L.mem s' b = L.mem s b := fun b hb =>
    hW.mem_eq hb.1.1 (hwc b hb)
  have slotK : ∀ p r, C p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s' = obj.Slot.cap st (cnSlot p (x &&& m)) s := by
    intro p r hp m hm x
    obtain ⟨h1, h2⟩ := hWc p r m x hp hm
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, capK _ h1, capK _ h2]
  have tK : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val = 0 ∨ K.val = 8 ∨
      K.val = 256 + 8 * layout.reg.REPLY.val ∨ K.val = 256 + 8 * layout.reg.CAP.val) →
      L.mem s' (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) :=
    fun K hK h8 hk => hW.mem_eq (field_aligned ht' hK h8) (hwT K hk)
  have esl : sl = core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) := by
    simp only [obj.Tcb.slot, lift, bind_ok] at hsl; exact (ok_inj_ff hsl).symm
  have tf := ht'.fits
  have vsl : sl.val = t.val := by
    rw [esl]; simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    all_goals omega
  have e0 : sl = core.num.U64.wrapping_add t 0#u64 := by
    apply UScalar.eq_of_val_eq; rw [vsl, tcb_wadd_val ht' (by decide)]; simp
  have e8 : core.num.U64.wrapping_add sl 8#u64 = core.num.U64.wrapping_add t 8#u64 := by
    apply UScalar.eq_of_val_eq; rw [tcb_wadd_val ht' (by decide)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vsl]; omega
  have hroot' : obj.Slot.cap st sl s' = ok root := by
    rw [← hroot]; unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, e8, e0,
      tK 0#u64 (by decide) (by decide) (Or.inl (by decide)), tK 8#u64 (by decide) (by decide) (Or.inr (Or.inl (by decide)))]
  have hCAP : (layout.reg.CAP).val < 384 := by simp
  have hREP : (layout.reg.REPLY).val < 384 := by simp
  have hregR : obj.Tcb.reg st t s' layout.reg.REPLY = obj.Tcb.reg st t s layout.reg.REPLY := by
    obtain ⟨K, hK, eK⟩ := regA_eq ht' hREP
    rw [reg_ok, reg_ok, eK, tK K (by simp [layout.reg.REPLY, layout.reg.R12] at hK; omega)
      (by simp [layout.reg.REPLY, layout.reg.R12] at hK; omega) (Or.inr (Or.inr (Or.inl hK)))]
  have hregC : obj.Tcb.reg st t s' layout.reg.CAP = obj.Tcb.reg st t s layout.reg.CAP := by
    obtain ⟨K, hK, eK⟩ := regA_eq ht' hCAP
    rw [reg_ok, reg_ok, eK, tK K (by simp [layout.reg.CAP, layout.reg.RDI] at hK; omega)
      (by simp [layout.reg.CAP, layout.reg.RDI] at hK; omega) (Or.inr (Or.inr (Or.inr hK)))]
  have hr' : cspace.resolve_address_bits st s' root i cspace.WORD_BITS = ok (core.result.Result.Ok found) :=
    rab_loop_congr2 st C slotK hcl 66 root _ 65#u64 _ (by simp) hC0 hr
  have hr1' : cspace.resolve_address_bits st s' root i1 cspace.WORD_BITS = ok (core.result.Result.Ok found1) :=
    rab_loop_congr2 st C slotK hcl 66 root _ 65#u64 _ (by simp) hC0 hr1
  have hc' : obj.Slot.cap st found.slot s' = ok (capability.Cap.Reply rptr g) := by
    obtain ⟨p, r, m, y, hp, hm, hs⟩ := rab_loop_slot st C hcl 66 root _ 65#u64 found (by simp) hC0 hr
    rw [hs, slotK p r hp m hm y, ← hs]; exact hc
  have hc1' : obj.Slot.cap st found1.slot s' = ok (capability.Cap.Endpoint ep b0 b1 true b3 b4) := by
    obtain ⟨p, r, m, y, hp, hm, hs⟩ := rab_loop_slot st C hcl 66 root _ 65#u64 found1 (by simp) hC0 hr1
    rw [hs, slotK p r hp m hm y, ← hs]; exact hc1
  unfold fastpath.reply_caps
  rw [hsl]; simp only [bind_ok]
  rw [hroot']; simp only [bind_ok]
  rw [hregR, hi]; simp only [bind_ok]
  rw [hr']; simp only [bind_ok]
  rw [hc']; simp only [bind_ok]
  rw [hregC, hi1]; simp only [bind_ok]
  rw [hr1']; simp only [bind_ok]
  rw [hc1']; simp only [bind_ok, ↓reduceIte]

/-- **The local ReplyRecv entry's prefix keeps what its fast path reads of
`found`** (KENTRY-PLAN pf1's former `RRVmFound` [W], derived): the `FAULT_IP` write
and a passing `budget_ok` (`update_timestamp`: the core's `CUR_TIME` and
`CONSUMED`) write neither the current-thread word, nor `t`'s root slot or
`REPLY` / `CAP` registers, nor a cap-slot word; so at the dispatch state the
current thread is `t` and `reply_caps` returns what it returned at entry. -/
theorem local_prefix_keep {T Cs Sg : Set U64} {s s1 s2 : S} {a a2 : A} {t v : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (et : sched.cur_thread st s = ok t) (htT : t ∈ T) (hCn : CnOff (L := L) T Cs Sg s t)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1)
    (hb : syscall.budget_ok st ar s1 a = ok (true, s2, a2)) (hA : P0.ArchTotal ar) :
    sched.cur_thread st s2 = ok t ∧ ∀ rptr ep, fastpath.reply_caps st s t = ok (some (rptr, ep)) →
      fastpath.reply_caps st s2 t = ok (some (rptr, ep)) := by
  have ht' := hT t htT
  obtain ⟨hct, hcn, hne⟩ := ct_cn hN
  have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP v ht' (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW1
  obtain ⟨KF, hKF, e1⟩ := hW1
  have hKF' : KF.val = 392 := by rw [hKF]; simp [layout.reg.FAULT_IP]
  have aF : Aligned (core.num.U64.wrapping_add t KF) := field_aligned ht' (by omega) (by omega)
  have hu := budget_ok_true ar hb
  obtain ⟨⟨n, b2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have hN1 : NodePlaced st T s1 (L.cpu s1) := by rw [e1, LawfulStore.cpu_wr]; exact hN.wr
  rw [update_timestamp_ok ar hN1 hn] at hu
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (ok_inj_ff hu)
  have ec : ctA (L := L) s1 = ctA (L := L) s := by rw [e1, ctA_wr]
  have en : cnA (L := L) s1 = cnA (L := L) s := by rw [e1, cnA_wr]
  -- the footprint from `s`
  have hW : WritesIn st s (utW (L := L) s1 n)
      (fun b => b = core.num.U64.wrapping_add t KF ∨ b = ctA (L := L) s ∨ b = cnA (L := L) s) := by
    refine ⟨?_, ?_, fun b hb hn' => ?_⟩
    · unfold utW; rw [e1]; simp only [L.ksb_wr]
    · unfold utW; rw [e1]; simp only [LawfulStore.cpu_wr]
    · unfold utW
      rw [ec, en, mem_wr_ne' hcn hb (fun e => hn' (Or.inr (Or.inr e.symm))),
        mem_wr_ne' hct hb (fun e => hn' (Or.inr (Or.inl e.symm))), e1,
        mem_wr_ne' aF hb (fun e => hn' (Or.inl e.symm))]
  have vb := nodeAt_val hN (off := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME])
  have vn := nodeAt_val hN (off := layout.node.CONSUMED) (by simp [layout.node.CONSUMED])
  have nd := hN.disj t htT
  have na := hN.align
  have tvF := tcb_wadd_val ht' (o := KF) (by omega)
  refine ⟨?_, ?_⟩
  · -- the current-thread word
    have vC := nodeAt_val hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
    have aC : Aligned (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    have eC : L.nodeAt (utW (L := L) s1 n) (L.cpu (utW (L := L) s1 n)) layout.node.CUR_THREAD =
        L.nodeAt s (L.cpu s) layout.node.CUR_THREAD := by
      rw [hW.2.1, nodeAt_of_ksb hW.1]
    have hm : L.mem (utW (L := L) s1 n) (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) =
        L.mem s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := by
      refine hW.mem_eq aC ?_
      rintro (e | e | e) <;> (have e' := congrArg UScalar.val e)
      · rw [vC, tvF] at e'; simp [layout.node.CUR_THREAD] at e'; omega
      · unfold ctA at e'; rw [vC, vb] at e'; simp [layout.node.CUR_THREAD, layout.node.CUR_TIME] at e'
      · unfold cnA at e'; rw [vC, vn] at e'; simp [layout.node.CUR_THREAD, layout.node.CONSUMED] at e'
    rw [cur_thread_ok] at et ⊢
    rw [← ok_inj_ff et]
    unfold LawfulStore.curW; rw [eC, hm]
  · intro rptr ep hrc
    refine reply_caps_keep (T := T) (Cs := Cs) (Sg := Sg) ht' hrc hW ?_ ?_ hCn
    · intro K hK e
      have hK2 : K.val < 4096 ∧ K.val ≠ 392 := by
        simp [layout.reg.REPLY, layout.reg.CAP, layout.reg.R12, layout.reg.RDI] at hK; omega
      have tvK := tcb_wadd_val ht' (o := K) hK2.1
      rcases e with e | e | e <;> (have e' := congrArg UScalar.val e)
      · rw [tvK, tvF] at e'; omega
      · unfold ctA at e'; rw [vb, tvK] at e'; simp [layout.node.CUR_TIME] at e'; omega
      · unfold cnA at e'; rw [vn, tvK] at e'; simp [layout.node.CONSUMED] at e'; omega
    · rintro b ⟨⟨-, oT, oN⟩, -⟩ e
      have bt := oT t htT
      have bn := oN _ hcC
      rcases e with e | e | e <;> (have e' := congrArg UScalar.val e)
      · rw [tvF] at e'; omega
      · unfold ctA at e'; rw [vb] at e'; simp [layout.node.CUR_TIME] at e'; omega
      · unfold cnA at e'; rw [vn] at e'; simp [layout.node.CONSUMED] at e'; omega

/-- `local_prefix_keep` with `found` (the ReplyRecv entries' form). -/
theorem rr_prefix_keep {T Cs Sg : Set U64} {s s1 s2 : S} {a a2 : A} {t v rptr ep : U64}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcC : L.cpu s ∈ Cs)
    (et : sched.cur_thread st s = ok t) (htT : t ∈ T) (hCn : CnOff (L := L) T Cs Sg s t)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1)
    (hb : syscall.budget_ok st ar s1 a = ok (true, s2, a2))
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) (hA : P0.ArchTotal ar) :
    sched.cur_thread st s2 = ok t ∧ fastpath.reply_caps st s2 t = ok (some (rptr, ep)) :=
  let h := local_prefix_keep ar hT hN hcC et htT hCn es1 hb hA
  ⟨h.1, h.2 _ _ hrc⟩

/-- **`rr_vm_local_same`: the VM-fault ReplyRecv entry beside the serial
gate, where its fast path ran, is the general entry**
`syscall.handle_syscall … SysReplyRecv` (whose own fast path declines there,
`rr_found_decline_of_vm`), given `StoreExt` [P], `RRPreAtG … VMFault`, the placement facts at
the entry state that `rr_prefix_keep` reads, the top's flag fact, and that
`found` is what `reply_caps` returns at the entry state (fl4-sync's
`local_syscall` computes it there). -/
theorem rr_vm_local_same (hX : StoreExt st) (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s' : S} {a a' : A} {found : U64 × U64}
    (hP : RRPreAtG (L := L) ar fl4_abi.consts.fault.VMFault s a)
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hfd : ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found))
    (h : syscall.handle_reply_recv_vm_local st ar s a found = ok (true, s', a')) :
    syscall.handle_syscall st ar s a fl4_abi.syscall.SysReplyRecv = ok (s', a') := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  obtain ⟨rptr, ep⟩ := found
  unfold syscall.handle_reply_recv_vm_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨i, -, h⟩ := bind_eq_ok h
  by_cases c1 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · rw [if_pos c1] at h; simp at h
  rw [if_neg c1] at h
  obtain ⟨nx, enx, h⟩ := bind_eq_ok h
  obtain ⟨s1, es1, h⟩ := bind_eq_ok h
  obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  simp only [↓reduceIte] at h
  try dsimp only at h
  have hb : syscall.budget_ok st ar s1 a = ok (true, s2, a1) := by
    unfold syscall.budget_ok
    rw [eu]; simp only [bind_ok, uncurry_apply_pair]
    exact check_budget_restart_suf ar ecsc ec eb
  have htT : t ∈ T := by
    rw [cur_thread_ok] at et; rw [← ok_inj_ff et]; exact hcT
  obtain ⟨et2, hrc⟩ := rr_prefix_keep ar hT hN hcC et htT (hCn t et) es1 hb (hfd t et) hA
  obtain ⟨X, a'', hd, hf⟩ := rr_vm_same ar hX et2 hrc h (hP t nx s1 s2 a1 et enx es1 hb)
  have hdec : fastpath.reply_recv st ar s2 a1 = ok (false, s2, a1) := by
    unfold fastpath.reply_recv
    rw [et2]; simp only [bind_ok]
    rw [hrc]; simp only [bind_ok]
    exact rr_found_decline_of_vm ar hA h
  -- the flags word at the `FAULT_IP`-written state: trap clear (the top's fact)
  have hs1 : s1 = L.wr s (regA t layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64) := by
    have hW1 := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
      (hT t htT) (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at hW1
    obtain ⟨K, hK, e1⟩ := hW1
    obtain ⟨K', hK', eK'⟩ := regA_eq (hT t htT) (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    rw [e1, eK']; congr 2; apply UScalar.eq_of_val_eq; rw [hK, hK']
  have hfl := hflag t (core.num.U64.wrapping_sub nx 2#u64) et
  rw [← hs1] at hfl
  obtain ⟨fl, efl, hfl0⟩ := spec_ex_fd hfl
  have c1' : ¬ (fl &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true := by
    rw [hfl0]; simp
  have hs := syscall_rr_true ar et enx es1 efl c1' hb hdec hd hf
  unfold syscall.handle_syscall
  rw [hs]; simp only [bind_ok, uncurry_apply_pair]

/-- **The VM-fault ReplyRecv local entry where it ran: the general entry's
postconditions** (on the `true` results).
`hX : StoreExt` [P] as in `rr_vm_local_same`. -/
theorem rr_vm_local_triple (hX : StoreExt st) (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s : S} {a : A} {found : U64 × U64}
    {P : S × A → Prop} (hP : RRPreAtG (L := L) ar fl4_abi.consts.fault.VMFault s a)
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t)
    (hflag : ∀ t v, sched.cur_thread st s = ok t → obj.Tcb.flags st t (L.wr s (regA t layout.reg.FAULT_IP) v)
      ⦃ f => (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 ⦄)
    (hfd : ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found))
    (hG : syscall.handle_syscall st ar s a fl4_abi.syscall.SysReplyRecv ⦃ P ⦄) :
    syscall.handle_reply_recv_vm_local st ar s a found ⦃ r => r.1 = true → P (r.2.1, r.2.2) ⦄ := by
  obtain ⟨⟨b, s', a'⟩, e, -⟩ := spec_ex_fd (P0.syscall.handle_reply_recv_vm_local.p0 st ar s a found L.total hA)
  rw [e, WP.spec_ok]
  intro hb
  simp only at hb
  subst hb
  have hs := rr_vm_local_same ar hX hA hP hI hCn hflag hfd e
  rw [hs, WP.spec_ok] at hG
  exact hG

/-- **`RRPreAtG` at an entry state** with `EntryInv` (m70's `RRPreAt5.of_inv`,
m68's `RRPreAt2.of5`, m67's `RRPreAt.of2`, over the fault type), under
`RRSumAt` / `CnOffAt` [J]. -/
theorem RRPreAtG.of_inv {ty : U64} [HfrRestart st ar ty] {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {U Ac : Set U64} {H : Heap} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSum : RRSumAt (L := L) ar Scs s a) (hCn : CnOffAt (L := L) ar T Cs Sg s a) :
    RRPreAtG (L := L) ar ty s a :=
  RRPreAt.of2G ar hA E0 hP h (RRPreAt2.of5G ar hA E0 hNt hP h hSum hCn (RRPreAt5.of_invG ar hA E0 hNt hP h hSum))

end

end Fl4Proofs.P1
