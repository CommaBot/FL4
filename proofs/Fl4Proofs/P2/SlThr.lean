/-
# P2 (line p2sl): the decided thread of the syscall entry beside the gate

`slThr st rp s`: the thread on whose home core an accepted run of
`syscall.handle_syscall_local` depends, read at the entry state `s`: in the trap arm
(`SlTrap`) the head of the endpoint named by the current thread's fault-handler cap
(`fhA`, `resPtr`, `capPtr`), in the ReplyRecv arm the reply object's thread (`Reply.tcb rp`, fl4-sync's
`found.1`). The `SlThr` fields proved here:

* `slThr_alt` (`SlThr.alt`): `slThr` is the same at every alternative of `s`;
* `slThr_acc` (`SlThr.acc`): an accepting run at an alternative passed `schedulable_here` on
  `slThr` (`AFFINITY = cur_cpu`; the thread is then live, `SlLive`), read through the prefix (`lp_mem`: the prefix keeps every
  aligned word other than its own three, `SlDS`).

Premises: `SlThrIn` [W] at the entry state (each field tagged there): the words the decided
thread is read from, and its `AFFINITY`, are in the read set `SlRS s` and are not prefix
words; plus `SlPre`'s placement and `PreAcc` facts.
-/
import Fl4Proofs.P2.SlObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The current thread's fault-handler slot. -/
abbrev fhA (s : S) : U64 := slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER

/-- The endpoint a cap names (`0` for any other cap). -/
def capPtr : capability.Cap → U64
  | .Endpoint ptr _ _ _ _ _ => ptr
  | _ => 0#u64

open Classical in
/-- The endpoint a decoded cap names (`0` for a failed decode). -/
noncomputable def resPtr (c : Result capability.Cap) : U64 :=
  if h : ∃ k, c = ok k then capPtr (Classical.choose h) else 0#u64

theorem resPtr_ok {c : Result capability.Cap} {k : capability.Cap} (h : c = ok k) : resPtr c = capPtr k := by
  have he : ∃ k, c = ok k := ⟨k, h⟩
  unfold resPtr
  rw [dif_pos he]
  exact congrArg capPtr (ok_inj_ff ((Classical.choose_spec he).symm.trans h))

/-- A decoded cap is an endpoint cap. -/
def IsEp (c : Result capability.Cap) : Prop :=
  ∃ ptr b x y g gr, c = ok (capability.Cap.Endpoint ptr b x y g gr)

variable (st) in
open Classical in
/-- **The decided thread** at the entry state (module docstring; `0` when the fault-handler cap
is not an endpoint, where the trap arm declines without reading a thread). -/
noncomputable def slThr (rp : U64) (s : S) : U64 :=
  if SlTrap st s then
    (if IsEp (obj.Slot.cap st (fhA (L := L) s) s) then
      L.mem s (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) else 0#u64)
  else L.mem s (rTcbA rp)

variable (st) in
open Classical in
/-- **The decided thread is live**: the trap arm's handler endpoint is in `RECV` (so its head is
a thread, P1), the ReplyRecv arm's reply object names a thread (`≠ 0`). Only then does a run
read the decided thread's words. -/
def SlLive (rp : U64) (s : S) : Prop :=
  if SlTrap st s then IsEp (obj.Slot.cap st (fhA (L := L) s) s) ∧
    obj.Ep.state st (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) s = ok obj.EP_RECV
  else L.mem s (rTcbA rp) ≠ 0#u64

/-- `Ep.state` reads the endpoint's tail-state word. -/
theorem ep_state_congr {s s' : S} {p : U64} (h : L.mem s' (epTSA p) = L.mem s (epTSA p)) :
    obj.Ep.state st p s' = obj.Ep.state st p s := by
  rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s' p), eq_of_spec_fd (obj.Ep.state.spec (L := L) s p)]
  unfold LawfulStore.epState
  rw [h]

theorem u_ne0 {u : U64} (h : ∃ b, obj.Tcb.is_null u = ok b ∧ ¬ b = true) : u ≠ 0#u64 := by
  obtain ⟨b, hb, hn⟩ := h
  rw [is_null_ok] at hb
  rw [← ok_inj_ff hb] at hn
  simpa using hn

/-- **Where the decided thread is read from** [W] (per-word layout at the entry state `s`,
fl4-sync's locks): the words `slThr` reads and its `AFFINITY` are in `SlRS s` and are not
prefix words. -/
structure SlThrIn (K : KLayout) (Locks : S → U64 → Prop) (rp : U64) (s : S) : Prop where
  /-- [W] the current thread's fault-handler slot (its own TCB). -/
  fh : SlTrap st s → SlRS (st := st) K Locks s (fhA (L := L) s) ∧
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add (fhA (L := L) s) 8#u64) ∧
    ¬ SlDS (L := L) s (fhA (L := L) s) ∧ ¬ SlDS (L := L) s (core.num.U64.wrapping_add (fhA (L := L) s) 8#u64)
  /-- [W] the handler endpoint's head and tail-state words (fl4-sync locks that endpoint). -/
  eh : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) → SlRS (st := st) K Locks s (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) ∧
    ¬ SlDS (L := L) s (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) ∧
    SlRS (st := st) K Locks s (epTSA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) ∧
    ¬ SlDS (L := L) s (epTSA (resPtr (obj.Slot.cap st (fhA (L := L) s) s)))
  /-- [W] the reply object's thread (fl4-sync locks the reply object). -/
  rt : ¬ SlTrap st s → SlRS (st := st) K Locks s (rTcbA rp) ∧ ¬ SlDS (L := L) s (rTcbA rp)
  /-- [W] the decided thread's `AFFINITY` when it is live (a placed TCB's, gate-owned: `af_of_tcb`). -/
  af : SlLive st rp s → SlRS (st := st) K Locks s (affA (slThr st rp s)) ∧ ¬ SlDS (L := L) s (affA (slThr st rp s))

theorem NodePlaced.of_ksb {T : Set U64} {s s' : S} {c : U64} (hk : L.ksb s' = L.ksb s)
    (h : NodePlaced st T s c) : NodePlaced st T s' c := by
  have e : L.nodeBase s' c = L.nodeBase s c := by simp only [LawfulStore.nodeBase, hk]
  exact ⟨by rw [e]; exact h.align, by rw [e]; exact h.fits, by rw [e]; exact h.disj⟩

theorem slDS_of {s s' : S} {b : U64} (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s)
    (hcur : L.curW s' = L.curW s) : SlDS (L := L) s' b ↔ SlDS (L := L) s b := by
  unfold SlDS
  rw [hcur, slDS_node (o := layout.node.CUR_TIME) hk hc, slDS_node (o := layout.node.CONSUMED) hk hc]

theorem cap_congr {s s' : S} {sl : U64} (h1 : L.mem s' sl = L.mem s sl)
    (h2 : L.mem s' (core.num.U64.wrapping_add sl 8#u64) = L.mem s (core.num.U64.wrapping_add sl 8#u64)) :
    obj.Slot.cap st sl s' = obj.Slot.cap st sl s := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, h1, h2]

theorem slTrap_alt {R : U64 → Prop} {cl : U64 → U64 → U64} {ko' : U64 → Fl4Proofs.P2.Serial.ClsOwner U64}
    {Us : U64 → Prop} {s s' : S} (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (Al : Alt st R cl ko' Us s s') (hcur : L.curW s' = L.curW s) : SlTrap st s' ↔ SlTrap st s := by
  unfold SlTrap
  rw [hcur, flags_ok, flags_ok, Al.read _ hfl]

variable {A : Type} (ar : machine.Arch A)

/-- The prefix keeps every aligned word other than its own three (`SlDS`). -/
theorem lp_mem {T : Set U64} (hA : P0.ArchTotal ar) {s X : S} {a a1 : A}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hP : LocalPre (st := st) ar s a (X, a1)) {b : U64} (hb : Aligned b) (hd : ¬ SlDS (L := L) s b) :
    L.mem X b = L.mem s b := by
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
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by
    rw [eKF]; exact field_aligned ht' (by omega) (by omega)
  rw [e2, utW_mem hN1 n1 hb (by rw [e1, ctA_wr]; exact fun e => hd (Or.inr (Or.inl e)))
    (by rw [e1, cnA_wr]; exact fun e => hd (Or.inr (Or.inr e))), e1,
    mem_wr_ne' aF hb (fun e => hd (Or.inl e.symm))]

set_option maxHeartbeats 4000000 in
/-- **Inversion of an accepted syscall entry**: the prefix to `X`, then the accepted arm. -/
theorem sl_acc_inv {s s' : S} {a a' : A} {n : I64} {found : U64 × U64}
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s', a')) :
    ∃ X a1, LocalPre (st := st) ar s a (X, a1) ∧
      ((SlTrap st s ∧ ∃ n', fastpath.fault st ar X a1 (L.curW s) n' = ok (true, s', a')) ∨
       (¬ SlTrap st s ∧ fastpath.reply_recv_found st ar X a1 (L.curW s) found.1 found.2 = ok (true, s', a'))) := by
  obtain ⟨rp, ep⟩ := found
  unfold syscall.handle_syscall_local at h
  try simp only [lift, bind_ok] at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  try simp only [lift, bind_ok] at h
  rw [num_domains_ne_one_false] at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  by_cases hf : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
  · have hS : SlTrap st s := ⟨i, ei, hf⟩
    rw [if_pos hf] at h
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
    cases b
    · simp at h
    simp only [↓reduceIte, if_pos hf] at h
    try simp only [lift, bind_ok] at h
    exact ⟨s2, a1, hP, Or.inl ⟨hS, _, h⟩⟩
  · have hS : ¬ SlTrap st s := fun ⟨f, ef, hf'⟩ => hf (by rw [ok_inj_ff (ei.symm.trans ef)]; exact hf')
    rw [if_neg hf] at h
    by_cases hn : (n != fl4_abi.syscall.SysReplyRecv) = true
    · rw [if_pos hn] at h; simp at h
    rw [if_neg hn] at h
    obtain ⟨nx, enx, h⟩ := bind_eq_ok h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨⟨s2, a1⟩, eu, h⟩ := bind_eq_ok h
    try simp only [uncurry_apply_pair] at h
    obtain ⟨csc, ecsc, h⟩ := bind_eq_ok h
    obtain ⟨c, ec, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    have hP : LocalPre (st := st) ar s a (s2, a1) := ⟨_, nx, s1, cur_thread_ok s, enx, es1, eu⟩
    cases b
    · simp at h
    simp only [↓reduceIte, if_neg hf] at h
    exact ⟨s2, a1, hP, Or.inr ⟨hS, h⟩⟩

variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`SlThr.alt`**: the decided thread is read from the read set. -/
theorem slThr_alt {rp : U64} {cl : U64 → U64 → U64} {ko' : U64 → Fl4Proofs.P2.Serial.ClsOwner U64} {s s' : S}
    (hp : PreAcc (L := L) (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) s)
    (I : SlThrIn (st := st) K Locks rp s)
    (Al : Alt st (SlRS (st := st) K Locks s) cl ko' (· ∈ K.user) s s') : slThr st rp s' = slThr st rp s := by
  have hcur := sl_alt_cur hp Al
  have hT := slTrap_alt hp.fl Al hcur
  have hf : fhA (L := L) s' = fhA (L := L) s := congrArg (fun t => slotIdx t layout.tcb.SLOT_FAULT_HANDLER) hcur
  unfold slThr
  by_cases hS : SlTrap st s
  · rw [if_pos (hT.2 hS), if_pos hS]
    obtain ⟨f1, f2, -, -⟩ := I.fh hS
    rw [hf, cap_congr (Al.read _ f1) (Al.read _ f2)]
    by_cases hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s)
    · rw [if_pos hE, if_pos hE, Al.read _ (I.eh hS hE).1]
    · rw [if_neg hE, if_neg hE]
  · rw [if_neg (fun h => hS (hT.1 h)), if_neg hS, Al.read _ (I.rt hS).1]

set_option maxHeartbeats 4000000 in
/-- **`SlThr.acc`**: an accepting run at an alternative passed `schedulable_here` on the
decided thread. -/
theorem slThr_acc (hA : P0.ArchTotal ar) {cl : U64 → U64 → U64} {ko' : U64 → Fl4Proofs.P2.Serial.ClsOwner U64}
    {s s' : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (I : SlThrIn (st := st) K Locks found.1 s)
    (Al : Alt st (SlRS (st := st) K Locks s) cl ko' (· ∈ K.user) s s')
    (h : syscall.handle_syscall_local st ar s' a n found = ok r) (hr : r.1 = true) :
    L.mem s (affA (slThr st found.1 s)) = L.cpu s := by
  obtain ⟨b, s1, a1⟩ := r
  dsimp only at hr
  subst hr
  have hcur := sl_alt_cur E.preG Al
  have hTr := slTrap_alt E.preG.fl Al hcur
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ T := by rw [hcur]; exact E.hcT
  have hD : ∀ b, ¬ SlDS (L := L) s b → ¬ SlDS (L := L) s' b :=
    fun b hb h => hb ((slDS_of Al.ksb Al.cpu hcur).1 h)
  obtain ⟨X, a2, LP, hX⟩ := sl_acc_inv ar h
  have lm : ∀ b, SlRS (st := st) K Locks s b → ¬ SlDS (L := L) s b → L.mem X b = L.mem s b :=
    fun b h1 h2 => by rw [lp_mem ar hA E.hT hN' hc' LP h1.1 (hD b h2), Al.read _ h1]
  have hcX : L.cpu X = L.cpu s' := (sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP).2.1
  rcases hX with ⟨hS', n', hf⟩ | ⟨hS', hf⟩
  · have hS := hTr.1 hS'
    obtain ⟨ptr, badge, dest, rr, hc, -⟩ := fault_acc st ar hf
    have HF := here_facts (L := L) hc.here
    obtain ⟨sl, x, y, g, gr, hsl, hcap, -⟩ := hc.cap
    have esl : sl = fhA (L := L) s := by rw [tcb_slot_val, hcur] at hsl; exact (ok_inj_ff hsl).symm
    subst esl
    obtain ⟨f1, f2, f3, f4⟩ := I.fh hS
    rw [cap_congr (lm _ f1 f3) (lm _ f2 f4)] at hcap
    have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := resPtr_ok hcap
    have hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s) := ⟨_, _, _, _, _, _, hcap⟩
    have e2 := I.eh hS hE
    rw [hp] at e2
    have h1 := obj.Ep.head.spec' (st := st) X ptr
    rw [hc.head, WP.spec_ok] at h1
    have hd : slThr st found.1 s = dest := by
      unfold slThr
      rw [if_pos hS, if_pos hE, hp, h1, lm _ e2.1 e2.2.1]
    have lv : SlLive st found.1 s := by
      unfold SlLive
      rw [if_pos hS]
      refine ⟨hE, ?_⟩
      rw [hp, ← ep_state_congr (lm _ e2.2.2.1 e2.2.2.2)]
      exact hc.ep
    have af := I.af lv
    rw [hd] at af ⊢
    rw [← Al.read _ af.1, ← Al.cpu]
    rw [← lp_mem ar hA E.hT hN' hc' LP af.1.1 (hD _ af.2), HF.aff, hcX]
  · have hS : ¬ SlTrap st s := fun h' => hS' (hTr.2 h')
    obtain ⟨u, usc, C, -⟩ := reply_recv_found_acc st ar hf
    obtain ⟨bb, hb, hbt⟩ := C.here
    subst hbt
    have HF := here_facts (L := L) hb
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [C.tcb, WP.spec_ok] at h1
    have hd : slThr st found.1 s = u := by
      unfold slThr
      rw [if_neg hS, h1, lm _ (I.rt hS).1 (I.rt hS).2]
    have lv : SlLive st found.1 s := by
      unfold SlLive
      rw [if_neg hS, ← lm _ (I.rt hS).1 (I.rt hS).2, ← h1]
      exact u_ne0 C.u0
    have af := I.af lv
    rw [hd] at af ⊢
    rw [← Al.read _ af.1, ← Al.cpu]
    rw [← lp_mem ar hA E.hT hN' hc' LP af.1.1 (hD _ af.2), HF.aff, hcX]

end

end Fl4Proofs.P2.PathObl
