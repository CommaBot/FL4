/-
# P2 (line p2sl): the accepted ReplyRecv fast path writes only its footprint

`sl_rr_foot`: an accepted `fastpath.reply_recv_found X0 a t rptr ep` (the
ReplyRecv arm of `handle_syscall_local`, entered after the prefix, with
fl4-sync's `found = (rptr, ep)`) writes only `FootSl` words of `X0`, with
`ep` and `rptr` locked. The run is P1's `rrTail` (`reply_recv_found_acc`);
its words (`RrW`):

* `t`'s state, `BLOCK_OBJ`, `REPLY_OBJ` and queue links (`t` is the current
  thread, runnable, so its queue links are its own);
* the faulting thread `u`'s registers (`handle_fault_reply`), fault word and
  state (`u` is on this core: `schedulable_here` checked its affinity);
* the reply object's `PREV` / `NEXT` / `TCB` words (`reply_remove` with no
  neighbours: fl4-sync's check that both links are 0) and the endpoint's
  two words (locked);
* `u`'s SC ring and the node's `REPROGRAM` (`unblock_check`), the node's
  action word, and the tail `switch_to u` (`sl_switch_to_foot`).

Hypotheses at `X0`: P1's `BXI` and `RRPl` (P1's placement bundle for an
accepted run, `rrPl_lk`), fl4-sync's check that the reply object has no
neighbours (`hrz`), and

* `hy0` [J]: `u` yields to no SC (as `FootSlFault`'s `hy0`, for a thread
  blocked on a reply).
-/
import Fl4Proofs.P2.FootSyscall
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st] (ar : machine.Arch A)

/-- The words `X3 → X15` of the run (no SC word). -/
def RrN (X0 : S) (t u rptr ep : U64) (b : U64) : Prop :=
  (∃ K : U64, (K.val = 3328 ∨ K.val = 3336 ∨ K.val = 3360 ∨ K.val = 3496 ∨ K.val = 3504) ∧
    b = core.num.U64.wrapping_add t K) ∨
  (∃ K : U64, 256 ≤ K.val ∧ K.val ≤ 3376 ∧ b = core.num.U64.wrapping_add u K) ∨
  b = rPrevA rptr ∨ b = rNextA rptr ∨ b = rTcbA rptr ∨
  b = L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION ∨ b = epHeadA ep ∨ b = epTSA ep

/-- The run's words. -/
def RrW (Z : U64 → Nat) (X0 : S) (t u rptr ep usc : U64) (b : U64) : Prop :=
  RrN (L := L) X0 t u rptr ep b ∨ InRing usc (Z usc) b ∨ b = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM

theorem sl_wr1 {X Y : S} {B : U64 → Prop} {ad v : U64} (e : Y = L.wr X ad v) (ha : Aligned ad) (hb : B ad) :
    WritesIn st X Y B := by
  subst e; exact (writesIn_wr ha).mono fun b h => h ▸ hb

set_option maxHeartbeats 16000000 in
/-- **An accepted ReplyRecv fast path writes only `FootSl`** (module docstring). -/
theorem sl_rr_foot {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {X0 : S} {a : A} {t : obj.Tcb} {rptr ep : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X0)
    (hP : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hrz : L.mem X0 (rNextA rptr) &&& ~~~1#u64 = 0#u64 ∧ L.mem X0 (rPrevA rptr) &&& ~~~1#u64 = 0#u64)
    (hy0 : ∀ u usc, RRChecks st ar X0 a t rptr ep u usc → L.mem X0 (yieldA u) = 0#u64)
    {sF : S} {aF : A} (h : fastpath.reply_recv_found st ar X0 a t rptr ep = ok (true, sF, aF)) :
    WritesIn st X0 sF (FootSl st T Z X0 ep rptr) := by
  obtain ⟨u, usc, C, hrt⟩ := reply_recv_found_acc st ar h
  have P := hP u usc C
  have hyu := hy0 u usc C
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  have hX0 : ScExtra0 st T Cs Scs Nt X0 := hX.2.2.toScExtra0
  have hO := hX.1
  have hT := P.hT
  have ht' := hT t P.ht
  have hu' := hT u P.hu
  have hN := P.hN
  have hcC := P.hcC
  have hΩ := P.hΩ
  obtain ⟨bh, hbh, hbt⟩ := C.here
  subst hbt
  have HF := here_facts (L := L) hbh
  -- `t` runnable
  obtain ⟨b0, hsch0, hb0⟩ := C.sch
  subst hb0
  have hsp := sched.is_schedulable.spec' (L := L) X0 t
  rw [hsch0, WP.spec_ok] at hsp
  obtain ⟨hrun0, -, -, -⟩ := hsp rfl
  have tnb : ¬ SlBlk st X0 t := by
    intro hb; unfold SlBlk at hb; unfold Runnable at hrun0
    rcases hb with e | e | e <;> rw [e] at hrun0 <;> revert hrun0 <;>
      simp [sched.TS_BLOCKED_ON_RECV, sched.TS_BLOCKED_ON_SEND, sched.TS_BLOCKED_ON_NTFN, sched.TS_RUNNING,
        sched.TS_RESTART, sched.TS_RUNNING_VM]
  have tOn : SlOn st T X0 t := ⟨P.ht, Or.inr P.hcur.symm⟩
  have uOn : SlOn st T X0 u := slOn_aff P.hu HF.aff
  have rp := hO.rp rptr P.hrR
  have vPv := rPrevA_val rp
  have vNx := rNextA_val rp
  have vRt := rTcbA_val0 rptr
  obtain ⟨vEh, vEt⟩ := sl_ep_vals P.hE
  -- `RrW` words are footprint words
  have sub : ∀ b, RrW (L := L) Z X0 t u rptr ep usc b → FootSl st T Z X0 ep rptr b := by
    rintro b ((⟨K, hK, rfl⟩ | ⟨K, h1, h2, rfl⟩ | rfl | rfl | rfl | rfl | rfl | rfl) | hb | rfl)
    · exact FootSl.tcb (slTcb_at' tOn (by omega) (by omega) tnb)
    · exact FootSl.tcb (slTcb_at uOn (by omega) (by omega) (by omega))
    · exact FootSl.lk (Or.inr ⟨by omega, by omega⟩)
    · exact FootSl.lk (Or.inr ⟨by omega, by omega⟩)
    · exact FootSl.lk slLk_rtcb
    · exact FootSl.node (slNode_at (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
    · exact FootSl.lk (slLk_ep P.hE).1
    · exact FootSl.lk (slLk_ep P.hE).2
    · exact FootSl.sc (slSc_ring (Or.inr ⟨u, uOn, P.husc, P.hsc0⟩) hb)
    · exact FootSl.node (slNode_at (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
  -- the run's words, one by one
  let RW := RrW (L := L) Z X0 t u rptr ep usc
  let N := RrN (L := L) X0 t u rptr ep
  have rT : ∀ K : U64, (K.val = 3328 ∨ K.val = 3336 ∨ K.val = 3360 ∨ K.val = 3496 ∨ K.val = 3504) →
      N (core.num.U64.wrapping_add t K) := fun K hK => Or.inl ⟨K, hK, rfl⟩
  have rU : ∀ K : U64, 256 ≤ K.val → K.val ≤ 3376 → N (core.num.U64.wrapping_add u K) := fun K h1 h2 =>
    Or.inr (Or.inl ⟨K, h1, h2, rfl⟩)
  have rPv : N (rPrevA rptr) := Or.inr (Or.inr (Or.inl rfl))
  have rNx : N (rNextA rptr) := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have rRt : N (rTcbA rptr) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have rAc : N (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have rEh : N (epHeadA ep) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have rEt : N (epTSA ep) := Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  have scΩ : ∀ b, Aligned b → InSC usc (Z usc) b → b ∈ Ω := fun b hb hin => P.hSg.sub _ (P.scSg b hb hin)
  have rpΩ : ∀ b, (b = rPrevA rptr ∨ b = rNextA rptr ∨ b = rTcbA rptr) → b ∈ Ω := by
    rintro b (rfl | rfl | rfl)
    · exact P.hSg.sub _ (P.rpS _ ⟨rptr, P.hrR, Or.inl rfl⟩)
    · exact P.hSg.sub _ (P.rpS _ ⟨rptr, P.hrR, Or.inr rfl⟩)
    · exact P.hSg.sub _ P.rtS
  -- what `N` / `RW` miss: TCB words, node words, `Ω` words
  have tN : ∀ y K : U64, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3336 ∧ K.val ≠ 3360 ∧ K.val ≠ 3496 ∧ K.val ≠ 3504) →
      (y = u → 3376 < K.val) → ¬ RW (core.num.U64.wrapping_add y K) := by
    intro y K hy hK h8 ht hu hw
    have hy' := hT y hy
    have vb := field_val hy' hK
    have om : ∀ b ∈ Ω, b ≠ core.num.U64.wrapping_add y K := fun b hb => P.omg_tcb hb hy hK
    rcases hw with (⟨K', hK', e⟩ | ⟨K', h1, h2, e⟩ | e | e | e | e | e | e) | hb | e
    · by_cases hyt : y = t
      · subst hyt; have := ht rfl; have e' := congrArg UScalar.val e
        rw [vb, field_val ht' (by omega)] at e'; omega
      · exact field_ne hy' ht' hK (by omega) (fun h => absurd h hyt) e
    · by_cases hyu : y = u
      · subst hyu; have := hu rfl; have e' := congrArg UScalar.val e
        rw [vb, field_val hu' (by omega)] at e'; omega
      · exact field_ne hy' hu' hK (by omega) (fun h => absurd h hyu) e
    · exact om _ (rpΩ _ (Or.inl rfl)) e.symm
    · exact om _ (rpΩ _ (Or.inr (Or.inl rfl))) e.symm
    · exact om _ (rpΩ _ (Or.inr (Or.inr rfl))) e.symm
    · exact P.tcb_node hy hK (by simp [layout.node.SCHED_ACTION]) e
    · have := P.hE.disj y hy; have e' := congrArg UScalar.val e; rw [vb, vEh] at e'; omega
    · have := P.hE.disj y hy; have e' := congrArg UScalar.val e; rw [vb, vEt] at e'; omega
    · exact om _ (scΩ _ (field_aligned hy' hK h8) hb.inSC) rfl
    · exact P.tcb_node hy hK (by simp [layout.node.REPROGRAM]) e
  have nN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
      ¬ RW (L.nodeAt X0 (L.cpu X0) o) := by
    intro o ho h8 h16 h56 hw
    have vo := nodeAt_val hN ho
    have aO := nodeAt_aligned hN ho h8
    have hEN := P.hEN.1 _ hcC
    rcases hw with (⟨K', hK', e⟩ | ⟨K', h1, h2, e⟩ | e | e | e | e | e | e) | hb | e
    · exact P.tcb_node P.ht (by omega) ho e.symm
    · exact P.tcb_node P.hu (by omega) ho e.symm
    · exact P.omg_node (rpΩ _ (Or.inl rfl)) ho e.symm
    · exact P.omg_node (rpΩ _ (Or.inr (Or.inl rfl))) ho e.symm
    · exact P.omg_node (rpΩ _ (Or.inr (Or.inr rfl))) ho e.symm
    · exact nodeAt_ne hN ho (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]; omega) e
    · have e' := congrArg UScalar.val e; rw [vo, vEh] at e'; omega
    · have e' := congrArg UScalar.val e; rw [vo, vEt] at e'; omega
    · exact P.omg_node (scΩ _ aO hb.inSC) ho rfl
    · exact nodeAt_ne hN ho (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]; omega) e
  have oN : ∀ b ∈ Ω, b ≠ rPrevA rptr → b ≠ rNextA rptr → b ≠ rTcbA rptr → ¬ N b := by
    intro b hb n1 n2 n3 hw
    rcases hw with ⟨K', hK', e⟩ | ⟨K', h1, h2, e⟩ | e | e | e | e | e | e
    · exact P.omg_tcb hb P.ht (by omega) e
    · exact P.omg_tcb hb P.hu (by omega) e
    · exact n1 e
    · exact n2 e
    · exact n3 e
    · exact P.omg_node hb (by simp [layout.node.SCHED_ACTION]) e
    · have := P.hEΩ b hb; have e' := congrArg UScalar.val e; rw [vEh] at e'; omega
    · have := P.hEΩ b hb; have e' := congrArg UScalar.val e; rw [vEt] at e'; omega
  have oW : ∀ b ∈ Ω, b ≠ rPrevA rptr → b ≠ rNextA rptr → b ≠ rTcbA rptr → ¬ InRing usc (Z usc) b →
      ¬ RW b := by
    intro b hb n1 n2 n3 n4 hw
    rcases hw with hw | hw | e
    · exact oN b hb n1 n2 n3 hw
    · exact n4 hw
    · exact P.omg_node hb (by simp [layout.node.REPROGRAM]) e
  -- an SC word is no reply word
  have scRp : ∀ c ∈ Scs, ∀ b, InSC c (Z c) b → b ≠ rPrevA rptr ∧ b ≠ rNextA rptr ∧ b ≠ rTcbA rptr := by
    intro c hc b hin
    have := hO.rpSc rptr P.hrR c hc
    unfold InSC at hin
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩ <;> have e' := congrArg UScalar.val e <;> omega
  /- The run. -/
  unfold rrTail at hrt
  obtain ⟨X1, e1, h⟩ := bind_eq_ok hrt
  obtain ⟨⟨X2, a1⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨b9, -, h⟩ := bind_eq_ok h
  obtain ⟨X3, e3, h⟩ := bind_eq_ok h
  obtain ⟨⟨restart, X4, a2⟩, e4, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  obtain ⟨X5, e5, h⟩ := bind_eq_ok h
  have hX1 : X1 = L.wr X0 (stA t) sched.TS_RESTART := by
    have := obj.Tcb.set_state.spec (L := L) X0 t sched.TS_RESTART; rw [e1, WP.spec_ok] at this; exact this
  have aSt := P.aS P.ht
  have aSu := P.aS P.hu
  obtain ⟨aPv, aNx⟩ := P.rpA rptr P.hrR
  have aRt : Aligned (rTcbA rptr) := (hΩ _ (rpΩ _ (Or.inr (Or.inr rfl)))).1
  have nSt : ∀ b ∈ Ω, stA t ≠ b := fun b hb e => P.omg_tcb hb P.ht (K := 3328#u64) (by simp) (by rw [← e, stA_eq])
  have ernx : L.mem X1 (rNextA rptr) &&& ~~~1#u64 = 0#u64 := by
    rw [hX1, mem_wr_ne' aSt aNx (nSt _ (rpΩ _ (Or.inr (Or.inl rfl))))]; exact hrz.1
  have erpv : L.mem X1 (rPrevA rptr) &&& ~~~1#u64 = 0#u64 := by
    rw [hX1, mem_wr_ne' aSt aPv (nSt _ (rpΩ _ (Or.inl rfl)))]; exact hrz.2
  have hn1 : obj.Reply.next st rptr X1 = ok 0#u64 := by
    rw [eq_of_spec_fd (obj.Reply.next.spec (L := L) X1 rptr), ernx]
  have k1 : L.ksb X1 = L.ksb X0 := by rw [hX1]; simp
  have c1 : L.cpu X1 = L.cpu X0 := by rw [hX1]; simp
  have cA : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) :=
    nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hTS : rTcbA rptr ≠ stA u := by
    rw [stA_eq]; exact P.omg_tcb (rpΩ _ (Or.inr (Or.inr rfl))) P.hu (by decide)
  obtain ⟨-, w12, -⟩ := rr_remove_foot ar (Rp := ({rptr} : Set U64)) (s := X1) (Or.inl ⟨0#u64, hn1, by simp⟩)
    (fun h' _ => absurd ernx h') (fun h' => absurd erpv h')
    (fun r' hr' => by rw [Set.mem_singleton_iff] at hr'; rw [hr']; exact ⟨aPv, aNx⟩)
    (Set.mem_singleton _) aRt aSu hTS (fun X w => by
      show L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD) ≠ u
      have ho : layout.node.CUR_THREAD.val < 4288 := by simp [layout.node.CUR_THREAD]
      rw [w.2.1, nodeAt_of_ksb w.1, c1, nodeAt_of_ksb k1, w.mem_eq cA ?_, hX1, mem_wr_ne' aSt cA ?_]
      · rw [show L.mem X0 (L.nodeAt X0 (L.cpu X0) layout.node.CUR_THREAD) = t from P.hcur]
        exact fun e => P.hut e.symm
      · rw [stA_eq]; exact P.tcb_node P.ht (K := 3328#u64) (by decide) ho
      · intro hF
        rcases hF with hR | e | e
        · obtain ⟨r', hr', e⟩ := hR
          have hr'' : r' = rptr := hr'
          rw [hr''] at e
          rcases e with e | e
          · exact P.omg_node (rpΩ _ (Or.inl rfl)) ho e.symm
          · exact P.omg_node (rpΩ _ (Or.inr (Or.inl rfl))) ho e.symm
        · exact P.omg_node (rpΩ _ (Or.inr (Or.inr rfl))) ho e.symm
        · rw [stA_eq] at e; exact P.tcb_node P.hu (K := 3328#u64) (by decide) ho e.symm) e2
  have w01 : WritesIn st X0 X1 N := sl_wr1 hX1 aSt (by rw [stA_eq]; exact rT _ (by simp))
  have w12' : WritesIn st X1 X2 N := w12.mono fun b hb => by
    rcases hb with hR | e | e
    · obtain ⟨r', hr', e⟩ := hR
      have hr'' : r' = rptr := hr'
      rw [hr''] at e
      rcases e with e | e
      · rw [e]; exact rPv
      · rw [e]; exact rNx
    · rw [e]; exact rRt
    · rw [e, stA_eq]; exact rU _ (by simp) (by simp)
  have w02 : WritesIn st X0 X2 N := w01.trans1 w12'
  -- `unblock_check` on `u`'s SC
  have hW2 : RefillsWF st X2 usc (Z usc) := P.hWF.agree fun b hb hin => by
    obtain ⟨n1, n2, n3⟩ := scRp usc P.hcS b hin
    exact w02.mem_eq hb (oN b (scΩ b hb hin) n1 n2 n3)
  have eN2 : L.nodeA X2 layout.node.REPROGRAM = L.nodeAt X0 (L.cpu X0) layout.node.REPROGRAM := by
    unfold LawfulStore.nodeA; rw [w02.2.1, nodeAt_of_ksb w02.1]
  have hrep : Aligned (L.nodeA X2 layout.node.REPROGRAM) ∧
      Outside (L.nodeA X2 layout.node.REPROGRAM) usc (Z usc) := by
    rw [eN2]
    exact ⟨nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]),
      node_out_place scΩ hΩ hcC hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])⟩
  have key : X3 = X2 ∨ sporadic.unblock_check st X2 usc = ok X3 := by
    split at e3
    · obtain ⟨i13, -, e3⟩ := bind_eq_ok e3
      obtain ⟨i14, -, e3⟩ := bind_eq_ok e3
      split at e3
      · exact Or.inr e3
      · exact Or.inl (ok_inj_ff e3).symm
    · exact Or.inl (ok_inj_ff e3).symm
  have w23 : WritesIn st X2 X3 RW ∧ RefillsWF st X3 usc (Z usc) := by
    rcases key with rfl | e3'
    · exact ⟨WritesIn.refl _ _, hW2⟩
    · have hf := sporadic.unblock_check.fr hW2 hrep
      have hw := sporadic.unblock_check.wf hW2 hrep
      rw [e3', WP.spec_ok] at hf hw
      refine ⟨hf.mono fun b hb => ?_, hw⟩
      rcases hb with hb | rfl
      · exact Or.inr (Or.inl hb)
      · rw [eN2]; exact Or.inr (Or.inr rfl)
  obtain ⟨w23, hW3⟩ := w23
  have w03 : WritesIn st X0 X3 RW := ((w02.mono fun _ h => Or.inl h).trans w23).mono fun _ hb => hb.elim id id
  -- the fault reply, `clear_fault`
  have hTu : TcbPlaced ({u} : Set U64) := fun y hy => by rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hu'
  have w34 : WritesIn st X3 X4 N := by
    have := faults.handle_fault_reply.rg (st := st) (L := L) (ar := ar) (s := X3) (a := a1) (snd := t) hTu (Set.mem_singleton u)
    rw [e4, WP.spec_ok] at this
    refine this.mono fun b hb => ?_
    rcases hb with ⟨y, hy, K, h1, h2, -, rfl⟩ | hb
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact rU K h1 (by omega)
    · simp at hb
  have hX5 : X5 = L.wr X4 (faultA u) fl4_abi.consts.fault.NullFault := by
    unfold faults.clear_fault at e5
    have := obj.Tcb.set_fault_type.spec (L := L) X4 u fl4_abi.consts.fault.NullFault
    rw [e5, WP.spec_ok] at this; exact this
  have w45 : WritesIn st X4 X5 N :=
    sl_wr1 hX5 (field_aligned (K := 3376#u64) hu' (by simp) (by simp)) (rU 3376#u64 (by simp) (by simp))
  have w05 : WritesIn st X0 X5 RW := (w03.trans ((w34.trans1 w45).mono fun _ h => Or.inl h)).mono
    fun _ hb => hb.elim id id
  have eNA5 : ∀ Y : S, L.ksb Y = L.ksb X5 → L.cpu Y = L.cpu X5 →
      L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION = L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION := by
    intro Y hk hc; rw [hc, nodeAt_of_ksb hk, w05.2.1, nodeAt_of_ksb w05.1]
  have aAc : Aligned (L.nodeAt X0 (L.cpu X0) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
  have aBl : Aligned (blockA t) := field_aligned (K := 3336#u64) ht' (by simp) (by simp)
  have aRp : Aligned (replyA t) := field_aligned (K := 3360#u64) ht' (by simp) (by simp)
  have aEn : Aligned (nextA .Ep t) := nextA_aligned ht' .Ep
  have aEp : Aligned (prevA .Ep t) := prevA_aligned ht' .Ep
  obtain ⟨aEh, aEt⟩ := ep_aligned P.hE
  -- the rest of the run, either restart flag
  have hrest : ∃ X15 : S, WritesIn st X5 X15 N ∧ fastpath.switch_to st ar X15 a2 u = ok (sF, aF) := by
    split at h
    all_goals
      obtain ⟨X6, e6, h⟩ := bind_eq_ok h
      obtain ⟨X7, e7, h⟩ := bind_eq_ok h
      obtain ⟨X8, e8, h⟩ := bind_eq_ok h
      obtain ⟨X9, e9, h⟩ := bind_eq_ok h
      obtain ⟨X10, e10, h⟩ := bind_eq_ok h
      obtain ⟨X11, e11, h⟩ := bind_eq_ok h
      obtain ⟨X12, e12, h⟩ := bind_eq_ok h
      obtain ⟨X13, e13, h⟩ := bind_eq_ok h
      obtain ⟨X14, e14, h⟩ := bind_eq_ok h
      obtain ⟨X15, e15, h⟩ := bind_eq_ok h
      obtain ⟨⟨X16, a3⟩, hsw, h⟩ := bind_eq_ok h
      have hx := ok_inj_ff h
      simp only [Prod.mk.injEq, true_and] at hx
      obtain ⟨rfl, rfl⟩ := hx
      refine ⟨X15, ?_, hsw⟩
      obtain ⟨v6, e6'⟩ : ∃ v, obj.Tcb.set_state st u X5 v = ok X6 := ⟨_, e6⟩
      have h6 := obj.Tcb.set_state.spec (L := L) X5 u v6
      rw [e6', WP.spec_ok] at h6
      have h7 := sched.set_action.spec (L := L) X6 u
      rw [e7, WP.spec_ok] at h7
      have h8 := obj.Tcb.set_state.spec (L := L) X7 t sched.TS_RUNNING
      rw [e8, WP.spec_ok] at h8
      have h9 := obj.Tcb.set_state.spec (L := L) X8 t sched.TS_BLOCKED_ON_RECV
      rw [e9, WP.spec_ok] at h9
      have h10 := obj.Tcb.set_block_obj.wr (L := L) X9 t ep
      rw [e10, WP.spec_ok] at h10
      have h11 := obj.Tcb.set_reply_obj.wr (L := L) X10 t rptr
      rw [e11, WP.spec_ok] at h11
      have h12 := obj.Reply.set_tcb.spec (L := L) X11 rptr t
      rw [e12, WP.spec_ok] at h12
      rw [obj.Tcb.set_ep_next.ok] at e13
      rw [obj.Tcb.set_ep_prev.ok] at e14
      rw [obj.Ep.set_queue.ok] at e15
      have h13 := (ok_inj_ff e13).symm
      have h14 := (ok_inj_ff e14).symm
      have h15 := (ok_inj_ff e15).symm
      unfold epW at h15
      have w6 : WritesIn st X5 X6 N := sl_wr1 h6 aSu (by rw [stA_eq]; exact rU _ (by simp) (by simp))
      have w7 : WritesIn st X6 X7 N := by
        rw [eNA5 X6 w6.1 w6.2.1] at h7; exact sl_wr1 h7 aAc rAc
      have w8 : WritesIn st X7 X8 N := sl_wr1 h8 aSt (by rw [stA_eq]; exact rT _ (by simp))
      have w9 : WritesIn st X8 X9 N := sl_wr1 h9 aSt (by rw [stA_eq]; exact rT _ (by simp))
      have w10 : WritesIn st X9 X10 N := sl_wr1 h10 aBl (rT 3336#u64 (by simp))
      have w11 : WritesIn st X10 X11 N := sl_wr1 h11 aRp (rT 3360#u64 (by simp))
      have w12 : WritesIn st X11 X12 N := sl_wr1 h12 aRt rRt
      have w13 : WritesIn st X12 X13 N := sl_wr1 h13 aEn (rT 3496#u64 (by simp))
      have w14 : WritesIn st X13 X14 N := sl_wr1 h14 aEp (rT 3504#u64 (by simp))
      have w15 : WritesIn st X14 X15 N := by
        rw [h15]
        exact ((writesIn_wr aEh).trans (writesIn_wr aEt)).mono fun b hb => by
          rcases hb with rfl | rfl
          · exact rEh
          · exact rEt
      exact (((((((((w6.trans1 w7).trans1 w8).trans1 w9).trans1 w10).trans1 w11).trans1 w12).trans1 w13).trans1
        w14).trans1 w15)
  obtain ⟨X15, w515, hsw⟩ := hrest
  have w015 : WritesIn st X0 X15 RW := (w05.trans (w515.mono fun _ h => Or.inl h)).mono fun _ hb => hb.elim id id
  have w315 : WritesIn st X3 X15 N := (w34.trans1 w45).trans1 w515
  have k15 := w015.1
  have c15 := w015.2.1
  -- facts at `X15` for the switch
  have escY : L.mem X15 (scA u) = usc := by
    rw [scA_eq, w015.mem_eq (field_aligned hu' (by simp) (by simp))
      (tN u 3464#u64 P.hu (by simp) (by simp) (fun e => absurd e P.hut) (fun _ => by simp))]
    exact P.husc
  have eyY : L.mem X15 (yieldA u) = 0#u64 := by
    rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl,
      w015.mem_eq (field_aligned hu' (by simp) (by simp))
      (tN u 3472#u64 P.hu (by simp) (by simp) (fun e => absurd e P.hut) (fun _ => by simp))]
    exact hyu
  have ecY : L.cscW X15 = L.cscW X0 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [c15, nodeAt_of_ksb k15]
    exact w015.mem_eq (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (nN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
        (by simp [layout.node.CUR_SC]))
  have hW15 : RefillsWF st X15 usc (Z usc) := hW3.agree fun b hb hin => by
    obtain ⟨n1, n2, n3⟩ := scRp usc P.hcS b hin
    exact w315.mem_eq hb (oN b (scΩ b hb hin) n1 n2 n3)
  have hcs : L.cscW X0 ∈ Scs := hX0.cur
  have hcq0 : SCq st X0 Ω (L.cscW X0) (Z (L.cscW X0)) := by
    obtain ⟨hP, hz⟩ := hO.sc _ hcs
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
    exact ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have hcY : SCq st X15 Ω (L.cscW X15) (Z (L.cscW X15)) := by
    rw [ecY]
    refine ⟨fun hm => ?_, hcq0.2.1, hcq0.2.2⟩
    by_cases hcd : L.cscW X0 = usc
    · rw [hcd]; exact hW15
    · have agC : ∀ b, Aligned b → InSC (L.cscW X0) (Z (L.cscW X0)) b → L.mem X15 b = L.mem X0 b := by
        intro b hb hin
        obtain ⟨n1, n2, n3⟩ := scRp _ hcs b hin
        refine w015.mem_eq hb (oW b (hcq0.2.1 b hb hin) n1 n2 n3 fun hR => ?_)
        have := hO.scDisj _ hcs _ P.hcS hcd
        unfold InSC at hin; unfold InRing at hR; omega
      have em : L.rmax X15 (L.cscW X0) = L.rmax X0 (L.cscW X0) := by
        obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
        exact agC _ a1 ⟨a2, a3⟩
      exact (hcq0.1 (em ▸ hm)).agree agC
  have htY : L.mem X15 (scA u) ≠ L.cscW X15 → SCin st X15 Ω (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) ∧
      ∀ b, InSC (L.mem X15 (scA u)) (Z (L.mem X15 (scA u))) b → Outside b (L.cscW X15) (Z (L.cscW X15)) := by
    rw [escY, ecY]
    intro hne
    refine ⟨⟨hW15, scΩ⟩, fun b hin => ?_⟩
    have := hO.scDisj _ P.hcS _ hcs hne
    unfold InSC at hin; unfold Outside; omega
  have P15 : TailPld (L := L) T Cs Ω X15 u :=
    (⟨hT, P.hu, hN, hcC, hΩ⟩ : TailPld (L := L) T Cs Ω X0 u).ksb k15 c15
  have wsw := sl_switch_to_foot (ar := ar) hA X15 a2 P15 hcY htY eyY (B := FootSl st T Z X0 ep rptr)
    (fun o h1 h2 => by rw [c15, nodeAt_of_ksb k15]; exact FootSl.node (slNode_at h1 h2))
    (fun b hb h => by
      rw [ecY] at h
      rcases h with h | rfl
      · exact FootSl.sc (slSc_ring (Or.inl rfl) h)
      · exact FootSl.sc ⟨_, Or.inl rfl, hcq0.2.2.1.1⟩)
    (fun _ b hb h => by
      rw [escY] at h
      exact FootSl.sc (slSc_ring (Or.inr ⟨u, uOn, P.husc, P.hsc0⟩) h))
    (fun K h1 h2 => FootSl.tcb (slTcb_at uOn (by omega) (by omega) (by omega)))
  rw [hsw, WP.spec_ok] at wsw
  exact ((w015.mono sub).trans wsw).mono fun _ hb => hb.elim id id

end

end Fl4Proofs.P2
