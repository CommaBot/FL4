/-
# P2 (line pte, generation 14): the PageMap decode's first reads at the decode state (third `blk` piece)

`blk`'s decode (`decode_page_map`, P2/InvPmDecG.lean) needs, at the decode state `s2` (after the prefix and the checks,
`InvChk`), that a store reading `IoRS (ptU K) s` as `st` (the guarded store of `blk`: `IoRS (ptU K) ⊆ PmRSU`,
`pmRSU_ioRS`) answer the current thread, the message registers and `extra[0]`'s cap as `st`. Here, at a `PmPreG`
state:

* `msgReg_lt`: every message register index is below 384 (a TCB register word);
* `decode_nof`, **`cap_pml4_nof`**: a slot holding a PML4 cap has a first word that is neither Null nor Frame, so its
  two words are gate-owned (`IoPre.slot`);
* **`pm_decRd`**: `cur_thread` and `syscall_arg` (any index below `N_MSG_REGISTERS`) at `s2` on such a store are
  `st`'s; `extra[0]` is a slot `x0` (`vspace.extra … = some x0`) whose cap at `s2` reads alike on that store and is,
  as at the entry, the plan's mapped PML4 cap `Pml4 root true rasid`, whose ASID finds `root` at the entry
  (`PmRoot`, from the plan by `pmRoot_of_qf`);
* **`pm_decWalk`**: `check_vspace` of that cap and the small-page `page_entry_slot` (user `va`) at `s2` on such a
  store are `st`'s at `s2` (`pm_vsRd`, `vsRdG_tr` for both stores; the prefix writes no `VsW` word).
* **`pm_decRdC`**, **`pm_decWalkC`** (gen-45 p3mc, moved here from P2/InvPmGdV): the same with the read hypothesis
  cut by a word class `G` (`∀ b, IoRS (ptU K) s b → G b → R b`), the class asked only at the words read (the
  caller's node words, its registers, the slots, the walk words off the leaves). `pm_decRd` / `pm_decWalk` are their
  one-line instances at `G := fun _ => True` (statements unchanged).

No named premise. New module; gen 45 re-proves `pm_decRd` / `pm_decWalk` as corollaries (statements unchanged).
-/
import Fl4Proofs.P2.InvPmDecG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP

noncomputable section

section aux
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem msgReg_lt {i r : U64} (h : msg.msg_register i = ok r) : r.val < 384 := by
  unfold msg.msg_register at h
  by_cases h0 : i = 0#u64
  · rw [if_pos h0] at h; cases ok_inj_ff h; simp [layout.reg.R10]
  rw [if_neg h0] at h
  by_cases h1 : i = 1#u64
  · rw [if_pos h1] at h; cases ok_inj_ff h; simp [layout.reg.R8]
  rw [if_neg h1] at h
  by_cases h2 : i = 2#u64
  · rw [if_pos h2] at h; cases ok_inj_ff h; simp [layout.reg.R9]
  rw [if_neg h2] at h; cases ok_inj_ff h; simp [layout.reg.R15]

/-- A first word that is Null or Frame decodes to Null or a Frame cap. -/
theorem decode_nof {w0 w1 : U64} {c : capability.Cap} (h : capability.Cap.decode w0 w1 = ok c)
    (hn : OwnMap.NullOrFrame w0) : ∀ r b a, c ≠ .Pml4 r b a := by
  unfold capability.Cap.decode at h
  obtain ⟨t, ht, h⟩ := bind_eq_ok h
  obtain ⟨p, -, h⟩ := bind_eq_ok h
  have tv : t.val = w0.val / 2 ^ 59 := by
    have hs : (w0 >>> 59#i32) ⦃ t => t.val = w0.val >>> 59 ⦄ := by
      step as ⟨t', h1, h2⟩
      simpa using h1
    rw [post_of_ok hs ht, Nat.shiftRight_eq_div_pow]
  unfold OwnMap.NullOrFrame at hn
  rw [← tv] at hn
  rcases hn with h0 | h0
  · have e : t = 0#u64 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst e
    have h' : (ok capability.Cap.Null : Result capability.Cap) = ok c := h
    cases ok_inj_ff h'
    exact fun _ _ _ e => by simp at e
  · have e : t = 13#u64 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
    subst e
    have h' : (do
      let i ← w0 >>> 48#i32
      let i1 ← lift (i &&& 3#u64)
      let fs ← capability.FrameSize.from_code i1
      let i2 ← w0 >>> 50#i32
      let i3 ← lift (i2 &&& 3#u64)
      let b ← capability.bit w0 52#u64
      let b1 ← capability.bit w0 53#u64
      let b2 ← capability.bit w0 58#u64
      let i4 ← capability.unpack_asid w0 54#u64 w1
      let i5 ← lift (w1 &&& capability.PTR_MASK)
      ok (capability.Cap.Frame p fs i3 b b1 b2 i4 i5)) = ok c := h
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    obtain ⟨_, -, h'⟩ := bind_eq_ok h'
    cases ok_inj_ff h'
    exact fun _ _ _ e => by simp at e

/-- **A slot holding a PML4 cap: its first word is neither Null nor Frame.** -/
theorem cap_pml4_nof {s : S} {sl r a : U64} {b : Bool} (h : obj.Slot.cap st sl s = ok (.Pml4 r b a)) :
    ¬ OwnMap.NullOrFrame (L.mem s sl) := by
  intro hn
  unfold obj.Slot.cap at h
  rw [L.read_pair_eq] at h
  simp only [bind_ok] at h
  exact decode_nof h hn r b a rfl

end aux

section rd
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {μ : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **The PageMap decode's first reads, the read hypothesis cut by a word class `G`** (module docstring; `pm_decRd`
is its instance at `G := True`). -/
theorem pm_decRdC (hA : P0.ArchTotal ar) {s : S} {R G : U64 → Prop} {gS : machine.Store S} [GRd gS st R]
    {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hR : ∀ b, IoRS (st := st) K.ptU Locks s b → G b → R b)
    (hGn : ∀ o : U64, o.val < 4288 → G (L.nodeAt s (L.cpu s) o))
    (hGr : ∀ r : U64, r.val < 384 → G (regA (L.curW s) r))
    (hGs : ∀ q ∈ K.slots, G q ∧ G (core.num.U64.wrapping_add q 8#u64)) :
    L.curW s2 = L.curW s ∧
    sched.cur_thread gS s2 = sched.cur_thread st s2 ∧
    (∀ i, i < msg.N_MSG_REGISTERS → ∀ buf,
      msg.syscall_arg gS s2 (L.curW s2) buf i = msg.syscall_arg st s2 (L.curW s2) buf i) ∧
    ∃ x0 root rasid, vspace.extra p.extra 0#usize = ok (some x0) ∧
      obj.Slot.cap gS x0 s2 = obj.Slot.cap st x0 s2 ∧
      obj.Slot.cap st x0 s2 = ok (.Pml4 root true rasid) ∧
      vspace.find_vspace_for_asid st s rasid = ok (.Ok root) := by
  obtain ⟨⟨hJ, hq, hG⟩, hEx, hRt⟩ := hE
  have Pb := hq.1.1.1
  have P := Pb.ptU hG
  obtain ⟨-, es1, eu, -, -, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) (P.ioWr (Locks := Locks))
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have hL : Slot8 K.toKLayout := fun q hq => Pb.lay.slot8 q hq
  have ag : ∀ b, SlotW K.toKLayout b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact Pb.slot_keep w0 hq hbq hb
  refine ⟨hct, ?_, ?_, ?_⟩
  · have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
      rw [I.cp, nodeAt_of_ksb I.k]
      exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD])).1 (hGn _ (by simp [layout.node.CUR_THREAD]))
    exact sched.cur_thread.guard (gS := gS) s2 hctR
  · intro i hi buf
    refine msg.syscall_arg.guard_lt (gS := gS) s2 (L.curW s2) buf i hi (fun r hr => ?_)
    rw [hct]
    exact hR _ (P.reg (msgReg_lt hr)).1 (hGr _ (msgReg_lt hr))
  · obtain ⟨⟨-, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hq
    have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
    subst et
    rw [(harm _ info (cur_thread_ok s) hi).1] at hpw
    obtain ⟨-, -, -, -, root, rasid, -, x0, -, -, hx0, hx00, hcx, -⟩ := plan_with_mapF hpw
    have hkp := (plan_with_kp hpw).2
    rw [← hkp] at hx0
    obtain ⟨x0', hx0', hxK⟩ := pmEx_slots Pb hEx
    rw [hx0] at hx0'
    obtain rfl := ok_inj_ff hx0'
    have hc2 : obj.Slot.cap st x0 s2 = obj.Slot.cap st x0 s := cap_agree hL hxK ag
    have hRx := P.slot (Locks := Locks) (sl := x0) hxK (Or.inr (cap_pml4_nof hcx))
    refine ⟨x0, root, rasid, ?_, obj.Slot.cap.guard (gS := gS) x0 s2 (hR _ hRx.1 (hGs x0 hxK).1)
      (hR _ hRx.2 (hGs x0 hxK).2), hc2.trans hcx, hRt x0 root rasid hx0 hcx⟩
    unfold vspace.extra obj.Slot.is_null
    simp only [show ¬ (0#usize ≥ 3#usize) by decide, ↓reduceIte, hx0, bind_ok, decide_eq_true_eq, hx00]

set_option maxHeartbeats 1000000 in
/-- **The PageMap decode's walk, the read hypothesis cut by a word class `G`** (module docstring; `pm_decWalk` is
its instance at `G := True`). -/
theorem pm_decWalkC (hA : P0.ArchTotal ar) {s : S} {R G : U64 → Prop} {gS : machine.Store S} [GRd gS st R]
    {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hR : ∀ b, IoRS (st := st) K.ptU Locks s b → G b → R b)
    (hGv : ∀ b, VsW K.toKLayout b → b ∉ K.ptes → G b)
    {root rasid va : U64} (hva : ¬ va > fl4_abi.consts.USER_TOP) :
    vspace.check_vspace gS s2 (.Pml4 root true rasid) = vspace.check_vspace st s2 (.Pml4 root true rasid) ∧
    (vspace.find_vspace_for_asid st s rasid = ok (.Ok root) →
      vspace.page_entry_slot gS s2 root va .Small = vspace.page_entry_slot st s2 root va .Small) := by
  have hV := pm_vsRd hE.1 rasid va (userV_of_not_gt hva)
  obtain ⟨⟨-, hq, -⟩, -, -⟩ := hE
  have Pb := hq.1.1.1
  obtain ⟨-, es1, eu, -, -, -, -⟩ := C
  have w0 := prefix_writes ar hA Pb.tp Pb.np Pb.cT es1 eu
  have hrs : ∀ b, (VsW K.toKLayout b ∧ ¬ b ∈ K.ptes) → st.read s2 b = st.read s b := fun b hb => by
    rw [L.read_eq, L.read_eq, w0.2.2 b hb.1.1 (Pb.vs_notPreW hb.1)]
  have hrg : ∀ b, (VsW K.toKLayout b ∧ ¬ b ∈ K.ptes) → gS.read s2 b = st.read s b := fun b hb =>
    (gst_read (hR _ (pm_vsW_ioRS (Locks := Locks) (s := s) hb.1 hb.2) (hGv _ hb.1 hb.2))).trans (hrs b hb)
  have hks : st.ks_base s2 = st.ks_base s := by rw [L.ks_base_eq, L.ks_base_eq, w0.1]
  have hkg : gS.ks_base s2 = st.ks_base s := by rw [gst_ks_base]; exact hks
  have T1 := vsRdG_tr hV hrg hkg
  have T2 := vsRdG_tr hV hrs hks
  refine ⟨(check_vspace_tr (m' := gS) (x' := s2) (s := s) (root := root) T1.1).trans
    (check_vspace_tr (m' := st) (x' := s2) (s := s) (root := root) T2.1).symm, fun hf => ?_⟩
  exact (page_entry_slot_small_tr (m' := gS) (x' := s2) (s := s) ((T1.2 root hf))).trans
    (page_entry_slot_small_tr (m' := st) (x' := s2) (s := s) ((T2.2 root hf))).symm

/-- **The PageMap decode's first reads at the decode state** (module docstring): `pm_decRdC` at `G := True`. -/
theorem pm_decRd (hA : P0.ArchTotal ar) {s : S} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K.ptU Locks s)]
    {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1) :
    L.curW s2 = L.curW s ∧
    sched.cur_thread gS s2 = sched.cur_thread st s2 ∧
    (∀ i, i < msg.N_MSG_REGISTERS → ∀ buf,
      msg.syscall_arg gS s2 (L.curW s2) buf i = msg.syscall_arg st s2 (L.curW s2) buf i) ∧
    ∃ x0 root rasid, vspace.extra p.extra 0#usize = ok (some x0) ∧
      obj.Slot.cap gS x0 s2 = obj.Slot.cap st x0 s2 ∧
      obj.Slot.cap st x0 s2 = ok (.Pml4 root true rasid) ∧
      vspace.find_vspace_for_asid st s rasid = ok (.Ok root) :=
  pm_decRdC (R := IoRS (st := st) K.ptU Locks s) (G := fun _ => True) hA hE C (fun _ h _ => h) (fun _ _ => trivial)
    (fun _ _ => trivial) (fun _ _ => ⟨trivial, trivial⟩)

/-- **The PageMap decode's walk at the decode state** on a store reading `IoRS (ptU K) s` as `st`: `check_vspace`
and the small-page `page_entry_slot` give `st`'s answers at `s2` (`pm_decWalkC` at `G := True`). -/
theorem pm_decWalk (hA : P0.ArchTotal ar) {s : S} {gS : machine.Store S}
    [GRd gS st (IoRS (st := st) K.ptU Locks s)] {a : A} {nx : U64} {s1 s2 : S} {a1 : A}
    (hE : PmPreG st Cs Ω Sg Ac Locks p K μ s) (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    {root rasid va : U64} (hva : ¬ va > fl4_abi.consts.USER_TOP) :
    vspace.check_vspace gS s2 (.Pml4 root true rasid) = vspace.check_vspace st s2 (.Pml4 root true rasid) ∧
    (vspace.find_vspace_for_asid st s rasid = ok (.Ok root) →
      vspace.page_entry_slot gS s2 root va .Small = vspace.page_entry_slot st s2 root va .Small) :=
  pm_decWalkC (R := IoRS (st := st) K.ptU Locks s) (G := fun _ => True) hA hE C (fun _ h _ => h)
    (fun _ _ _ => trivial) hva

end rd

end
end Fl4Proofs.P2.E2EP
