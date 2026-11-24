/-
# P2: `PathObl.dec_alt` of the I/O port path (line p2io)

* `io_alt_not_acc`: a run that declines at the entry `s` is not accepted at any
  alternative state;
* `ioTail_dec`, `handle_dec`: a declined run on another store instance with the same reads
  and prefix writes;
* `io_dec_guard` (writes `IoDS` only), `io_dec_mguard` (every write `StepOK`);
* `io_dec_alt`: **`PathObl.dec_alt`**.

Premises: those of `IoPre`; `RegionOK`, `IoLayA` [J].
-/
import Fl4Proofs.P2.AccessIoAlt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region tcbOwner TcbSlot NullOrFrame slotOwner RegionOK
  GateField TimerField)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

/-- At an alternative state, a slot's CNode or I/O port cap was there at `s`. -/
theorem slot_back (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {sl : U64} (hsl : sl ∈ K.slots) {c : capability.Cap} (hc : obj.Slot.cap st sl s' = ok c)
    (h : (∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨ ∃ f l z, c = .IoPort f l z) :
    obj.Slot.cap st sl s = ok c := by
  have hn' := cap_not_nof hc h
  obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
  have hr : region K sl = .slot sl := P.lay.slotw sl hsl sl ⟨le_refl _, by omega⟩
  have hg : TcbSlot K sl ∨ ¬ NullOrFrame (L.mem s sl) := by
    by_cases hT : TcbSlot K sl
    · exact Or.inl hT
    refine Or.inr fun hn => ?_
    by_cases hR : IoRS (st := st) K Locks s sl
    · rw [Al.read sl hR] at hn'; exact hn' hn
    · have hk : OwnMap.ko K m0 sl = .gate := by
        unfold OwnMap.ko; simp only [hr]; rw [if_pos ⟨rfl, hT⟩]
      have hu : sl ∉ K.user := P.region_kernel (Or.inl (by rw [hr]; simp))
      have e := Al.clsEq sl hR hu (Or.inl hk)
      unfold OwnMap.cls at e
      simp only [hr] at e
      rw [if_neg (fun h => hn' h.2.2), if_pos ⟨rfl, hT, hn⟩] at e
      exact hn' (by rw [e]; left; rfl)
  obtain ⟨r0, r8⟩ := P.slot (Locks := Locks) hsl hg
  unfold obj.Slot.cap at hc ⊢
  rw [L.read_pair_eq] at hc ⊢
  rw [Al.read _ r0, Al.read _ r8] at hc
  exact hc

/-- The three prefix words are no slot words. -/
theorem prefix_slot (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {sl b : U64} (hsl : sl ∈ K.slots) (hb : InW sl 32 b) :
    b ≠ regA (L.curW s) layout.reg.FAULT_IP ∧ b ≠ ctA (L := L) s ∧ b ≠ cnA (L := L) s := by
  have hr := P.lay.slotw sl hsl b hb
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    obtain ⟨k, hk, e⟩ := regA_eq P.tA (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    have hf : layout.reg.FAULT_IP.val = 17 := by simp [layout.reg.FAULT_IP]
    have h2 := P.lay.tcbw _ (P.hT _ P.cT) k (by omega) (by omega)
    unfold fld at h2
    rw [← e, hr] at h2; cases h2
  · rintro rfl
    rw [P.lay.node _ _ (P.inNode _ (by simp [layout.node.CUR_TIME]))] at hr; cases hr
  · rintro rfl
    rw [P.lay.node _ _ (P.inNode _ (by simp [layout.node.CONSUMED]))] at hr; cases hr

theorem cap_wr {x : S} {a v sl : U64} (ha : Aligned a) (h0 : Aligned sl)
    (h8 : Aligned (core.num.U64.wrapping_add sl 8#u64)) (n0 : sl ≠ a) (n8 : core.num.U64.wrapping_add sl 8#u64 ≠ a) :
    obj.Slot.cap st sl (L.wr x a v) = obj.Slot.cap st sl x := by
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq, mem_wr_ne' ha h0 (Ne.symm n0), mem_wr_ne' ha h8 (Ne.symm n8)]

set_option maxHeartbeats 1000000 in
/-- **A run that declines at `s` is accepted at no alternative state.** -/
theorem io_alt_not_acc {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (Al : Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r : Bool × S × A} {z : S} {b : A} (h : syscall.handle_ioport_local st ar s a number = ok r)
    (hr : r.1 ≠ true) (h' : syscall.handle_ioport_local st ar s' a number = ok (true, z, b)) : False := by
  have hRa : ∀ b, IoRS (st := st) K Locks s b → Aligned b := fun _ h => h.1
  have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.nd (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  obtain ⟨info, emi', hfl', hnum, ht'⟩ := handle_ioport_inv h'
  rw [hcur] at emi' hfl' ht'
  have eflg : L.mem s' (core.num.U64.wrapping_add (L.curW s) 3456#u64) =
      L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    G.m _ (P.home (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  rw [eflg] at hfl'
  have rg : ∀ q : U64, q.val < 384 → L.mem s' (regA (L.curW s) q) = L.mem s (regA (L.curW s) q) := fun q hq =>
    G.m _ (P.reg hq).1
  have emi : msg.msg_info st s (L.curW s) = ok info := by
    unfold msg.msg_info at emi' ⊢
    rw [reg_ok] at emi' ⊢
    rw [rg _ (by simp [layout.reg.MSG_INFO])] at emi'
    exact emi'
  -- the run at `s` reaches the tail
  have ht : ioTail st ar s a (L.curW s) info number = ok r := by
    rw [handle_ioport_local_eq, cur_thread_ok] at h
    simp only [bind_ok] at h
    rw [emi] at h; simp only [bind_ok] at h
    rw [if_neg (by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]), flags_ok] at h
    simp only [bind_ok, lift] at h
    rw [hfl', if_neg (by simp)] at h
    by_cases c2 : (number != fl4_abi.syscall.SysCall) = true
    · rw [if_pos c2] at h
      rw [if_neg (by rw [hnum (by simpa using c2)]; simp)] at h
      exact h
    · rw [if_neg c2] at h; exact h
  obtain ⟨nx, s1', s2', a1, hb, hnx', hs1', hu', hact', hy', hx, hinv', hsuf', hh'⟩ := ioTail_inv ht'
  -- the prefix at `s`
  have ev : nx = L.mem s (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [reg_ok] at hnx'; rw [← ok_inj_ff hnx']; exact rg _ (by simp [layout.reg.NEXT_IP])
  have hnx : obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx := by rw [reg_ok, ev]
  have hfr : (layout.reg.FAULT_IP).val < 384 := by simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := hRa _ (P.reg (Locks := Locks) hfr).1
  have aT : Aligned (ctA (L := L) s) := nodeAt_aligned P.np (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have aN : Aligned (cnA (L := L) s) := nodeAt_aligned P.np (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have hs1 : obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) =
      ok (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) := set_reg_ok' _ _ _ _
  rw [set_reg_ok'] at hs1'
  have es1' := (ok_inj_ff hs1').symm
  have G1 := G.wr hRa (a := regA (L.curW s) layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) aF
  rw [← es1'] at G1
  obtain ⟨now, hnow, es2'⟩ := upd_eq hu'
  have hu := upd_fwd (st := st) (s := L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) hnow
  have eT : ctA (L := L) s1' = ctA (L := L) s := by
    show L.nodeAt _ _ _ = L.nodeAt _ _ _
    rw [es1', nd_wr, G.node]
  have eN : cnA (L := L) s1' = cnA (L := L) s := by
    show L.nodeAt _ _ _ = L.nodeAt _ _ _
    rw [es1', nd_wr, G.node]
  have eT1 : ctA (L := L) (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) =
      ctA (L := L) s := nd_wr _ _ _ _
  have eN1 : cnA (L := L) (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) =
      cnA (L := L) s := nd_wr _ _ _ _
  rw [eT, eN] at es2'
  rw [eT1, eN1] at hu
  have rT := (P.nd (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have rN := (P.nd (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  have G2 := (G1.wr hRa (a := ctA (L := L) s) (v := now) aT)
  have e1 : L.mem s1' (ctA (L := L) s) = L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) := G1.m _ rT
  have e2 := G2.m _ rN
  rw [e1, e2] at es2'
  have G3 := G2.wr hRa (a := cnA (L := L) s) (v := core.num.U64.wrapping_add (L.mem (L.wr (L.wr s
    (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) now) (cnA (L := L) s))
    (core.num.U64.wrapping_sub now (L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s)))) aN
  rw [← es2'] at G3
  -- slots through the prefix
  have capS : ∀ sl ∈ K.slots, ∀ (x : S) (v1 v2 v3 : U64), obj.Slot.cap st sl (L.wr (L.wr (L.wr x
      (regA (L.curW s) layout.reg.FAULT_IP) v1) (ctA (L := L) s) v2) (cnA (L := L) s) v3) = obj.Slot.cap st sl x := by
    intro sl hsl x v1 v2 v3
    obtain ⟨h8, hf⟩ := P.lay.slot8 sl hsl
    have hv : (core.num.U64.wrapping_add sl 8#u64).val = sl.val + 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    obtain ⟨p1, p2, p3⟩ := prefix_slot P hsl (b := sl) ⟨le_refl _, by omega⟩
    obtain ⟨q1, q2, q3⟩ := prefix_slot P hsl (b := core.num.U64.wrapping_add sl 8#u64) ⟨by omega, by omega⟩
    have a8 : Aligned (core.num.U64.wrapping_add sl 8#u64) := by unfold Aligned; omega
    rw [cap_wr aN h8 a8 p3 q3, cap_wr aT h8 a8 p2 q2, cap_wr aF h8 a8 p1 q1]
  rw [es1'] at es2'
  obtain ⟨s2, hs2⟩ : ∃ s2, L.wr (L.wr (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))
    (ctA (L := L) s) now) (cnA (L := L) s) (core.num.U64.wrapping_add (L.mem (L.wr (L.wr s
    (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) now) (cnA (L := L) s))
    (core.num.U64.wrapping_sub now (L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s)))) = s2 := ⟨_, rfl⟩
  rw [hs2] at hu G3
  have w := prefix_writes ar hA P.tp P.np P.cT hs1 hu
  have Hf := here_facts hh'
  have rsc : IoRS (st := st) K Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have e3 : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (hRa _ rsc) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s :=
    (P.hcsc (by rw [← e3, ← G3.m _ rsc]; exact Hf.sc)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.mid (Locks := Locks) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi hnx hs1 hu
  -- the checks at `s2`
  have nA := (P.nd (Locks := Locks) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
  have nS := (P.nd (Locks := Locks) layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
  have nM := (P.nd (Locks := Locks) layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
  have nR := (P.nd (Locks := Locks) layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
  have nd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by rw [w.2.1, nodeAt_of_ksb w.1]
  have hact : sched.action st s2 = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) _)] at hact' ⊢
    rw [← ok_inj_ff hact']
    unfold LawfulStore.actionW
    rw [G3.node, G3.m _ (by rw [nd2]; exact nA)]
  have hy : obj.Tcb.yield_to st (L.curW s) s2 = ok 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) _ _)] at hy' ⊢
    rw [← ok_inj_ff hy']; exact congrArg ok (G3.m _ M2.yld).symm
  have hh : fastpath.schedulable_here st s2 (L.curW s) = ok true := by
    rw [← hh']
    exact (here_congr G3 (by show IoRS _ _ _ (L.nodeAt _ _ _); rw [nd2]; exact rT)
      (by show IoRS _ _ _ (L.nodeAt _ _ _); rw [nd2]; exact nM)
      (by show IoRS _ _ _ (L.nodeAt _ _ _); rw [nd2]; exact nR) M2.td M2.rs M2.dt M2.cd M2.af M2.dom M2.iok.1.sc
      M2.iok.1.inq).symm
  have hsf : sporadic.sufficient st ar s2 a1 (L.cscW s2) (L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED)) = ok true := by
    have ec : L.cscW s2' = L.cscW s2 := by
      unfold LawfulStore.cscW LawfulStore.nodeA
      rw [G3.node]; exact G3.m _ (by rw [nd2]; exact nS)
    have en : L.mem s2' (L.nodeAt s2' (L.cpu s2') layout.node.CONSUMED) =
        L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.CONSUMED) := by
      rw [G3.node]; exact G3.m _ (by rw [nd2]; exact rN)
    rw [ec, en] at hsuf'
    rw [← hsuf']
    exact (suff_congr G3 a1 M2.rh).symm
  have ecap : L.mem s2' (regA (L.curW s) layout.reg.CAP) = L.mem s2 (regA (L.curW s) layout.reg.CAP) := G3.m _ M2.cap
  rw [ecap] at hinv'
  have c2 : ∀ sl ∈ K.slots, obj.Slot.cap st sl s2 = obj.Slot.cap st sl s := fun sl hsl => by
    rw [← hs2]; exact capS sl hsl s _ _ _
  have c2' : ∀ sl ∈ K.slots, obj.Slot.cap st sl s2' = obj.Slot.cap st sl s' := fun sl hsl => by
    rw [es2']; exact capS sl hsl s' _ _ _
  have hback : ∀ sl ∈ K.slots, ∀ c, obj.Slot.cap st sl s2' = ok c →
      ((∃ p' r' gs' g', c = .CNode p' r' gs' g') ∨ ∃ f l z, c = .IoPort f l z) → obj.Slot.cap st sl s2 = ok c := by
    intro sl hsl c hc hk
    rw [c2 sl hsl]
    rw [c2' sl hsl] at hc
    exact slot_back P Al hsl hc hk
  obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
  have hinv : ioport.invocation_ok st s2 (L.curW s) (L.mem s2 (regA (L.curW s) layout.reg.CAP)) info = ok true := by
    refine inv_back (C := C) (tcb_slot_ctable _) (cap_congr G3 M2.hR0 M2.hR8) (fun p r m y c hp hm hc hk =>
      hback _ (hC p r m y hp hm).1 c hc hk) (fun x f l z hl hc => hback _ ?_ _ hc (Or.inr ⟨_, _, _, rfl⟩)) M2.hcl M2.hroot
      (lib_congr G3 hbsl M2.iok.1.ib (M2.iok.1.bs bsl hbsl).1 (M2.iok.1.bs bsl hbsl).2) (G3.m _ M2.r10) hinv'
    -- the looked-up slot is a capability slot
    have hl0 : cspace.lookup_slot st s (L.curW s) (L.mem s2 (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) := by
      have hts := P.lay.tslot _ (P.hT _ P.cT) layout.tcb.SLOT_CTABLE _ (tcb_slot_ctable _) (by simp [layout.tcb.SLOT_CTABLE])
      exact lookup_slot_back (tcb_slot_ctable _) (c2 _ hts.1) (fun p r m y hp hm => c2 _ (hC p r m y hp hm).1) hcl hroot hl
    have ecp : L.mem s2 (regA (L.curW s) layout.reg.CAP) = L.mem s (regA (L.curW s) layout.reg.CAP) := by
      obtain ⟨k, hk, e⟩ := regA_eq P.tA (r := layout.reg.CAP) (by simp [layout.reg.CAP])
      have hc9 : layout.reg.CAP.val ≠ 17 ∧ layout.reg.CAP.val < 384 := by simp [layout.reg.CAP]
      rw [e]
      exact w.2.2 _ (field_aligned P.tA (by omega) (by omega)) (preW_tcb P.tA P.np P.cT (by omega) (by omega))
    rw [ecp] at hl0
    exact (P.fin x hl0).1
  exact hr (ioTail_true hb hnx hs1 hu hact hy hx hinv hsf hh ht)

end

end Fl4Proofs.P2.PathObl
