/-
# P2 (line invj, generation 7): declines of the frame-cap invocation path at the alternatives of `IoRSR`

stpost's `inv_alt_not_acc` / `inv_dec_alt` (P2/InvDec.lean) for the region-tagged read set `IoRSR` (scripted copy,
the `IoPre` lemmas over `IoRS` replaced by P2/InvDelPteIoR.lean's): **`inv_alt_not_accR`**, **`inv_dec_altR`** — a
run declining at `s` declines at every state agreeing with `s` on the `IoRSR s` words (in particular at every
alternative of `InvRSP s`, by `Alt.anti`), on the decline guard and on the `mguard` store for `StepOK (own K)`. The
declining run reads no leaf entry. `maxHeartbeats 1000000` as the source's.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteIoR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section altR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s' : S} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}

set_option maxHeartbeats 1000000 in
/-- **A frame-cap invocation run that declines at `s` is accepted at no alternative state** (`hSeen` [J]: the
words `still_holds` reads are in the read set). -/
theorem inv_alt_not_accR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    {p : localinv.Plan} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRSR st K Locks s x)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    {a : A} {r : Bool × S × A} {z : S} {b : A} (h : syscall.handle_invocation_local st ar s a number p = ok r)
    (hr : r.1 ≠ true) (h' : syscall.handle_invocation_local st ar s' a number p = ok (true, z, b)) : False := by
  have hRa : ∀ b, IoRSR st K Locks s b → Aligned b := fun _ h => h.1.1
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  obtain ⟨info, emi', hfl', hnum, ht'⟩ := handle_inv_inv h'
  rw [hcur] at emi' hfl' ht'
  have eflg : L.mem s' (core.num.U64.wrapping_add (L.curW s) 3456#u64) =
      L.mem s (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    G.m _ (P.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  rw [eflg] at hfl'
  have rg : ∀ q : U64, q.val < 384 → L.mem s' (regA (L.curW s) q) = L.mem s (regA (L.curW s) q) := fun q hq =>
    G.m _ (P.regR (Locks := Locks) hq).1
  have emi : msg.msg_info st s (L.curW s) = ok info := by
    unfold msg.msg_info at emi' ⊢
    rw [reg_ok] at emi' ⊢
    rw [rg _ (by simp [layout.reg.MSG_INFO])] at emi'
    exact emi'
  -- the run at `s` reaches the tail
  have ht : invTail st ar s a (L.curW s) info p = ok r := by
    rw [handle_invocation_local_eq, cur_thread_ok] at h
    simp only [bind_ok] at h
    rw [emi] at h; simp only [bind_ok] at h
    rw [if_neg (by simp [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]), flags_ok] at h
    simp only [bind_ok, lift] at h
    rw [hfl', if_neg (by simp)] at h
    rw [if_neg (by rw [hnum]; simp)] at h
    exact h
  obtain ⟨nx, s1', s2', a1, hb, hnx', hs1', hu', hact', hy', hsuf', hh', hsh'⟩ := invTail_inv ht'
  -- the prefix at `s`
  have ev : nx = L.mem s (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [reg_ok] at hnx'; rw [← ok_inj_ff hnx']; exact rg _ (by simp [layout.reg.NEXT_IP])
  have hnx : obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx := by rw [reg_ok, ev]
  have hfr : (layout.reg.FAULT_IP).val < 384 := by simp [layout.reg.FAULT_IP]
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := hRa _ (P.regR (Locks := Locks) hfr).1
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
  have rT := (P.ndR (Locks := Locks) layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have rN := (P.ndR (Locks := Locks) layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
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
  rw [es1'] at es2'
  obtain ⟨s2, hs2⟩ : ∃ s2, L.wr (L.wr (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))
    (ctA (L := L) s) now) (cnA (L := L) s) (core.num.U64.wrapping_add (L.mem (L.wr (L.wr s
    (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s) now) (cnA (L := L) s))
    (core.num.U64.wrapping_sub now (L.mem (L.wr s (regA (L.curW s) layout.reg.FAULT_IP)
      (core.num.U64.wrapping_sub nx 2#u64)) (ctA (L := L) s)))) = s2 := ⟨_, rfl⟩
  rw [hs2] at hu G3
  have w := prefix_writes ar hA P.tp P.np P.cT hs1 hu
  have Hf := here_facts hh'
  have rsc : IoRSR st K Locks s (scA (L.curW s)) :=
    P.gateR (Locks := Locks) (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
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
    (P.midR (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi hnx hs1 hu
  -- the checks at `s2`
  have nA := (P.ndR (Locks := Locks) layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
  have nS := (P.ndR (Locks := Locks) layout.node.CUR_SC (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
  have nM := (P.ndR (Locks := Locks) layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])).1
  have nR := (P.ndR (Locks := Locks) layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])).1
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
    exact (here_congr G3 (by show IoRSR st K Locks s (L.nodeAt _ _ _); rw [nd2]; exact rT)
      (by show IoRSR st K Locks s (L.nodeAt _ _ _); rw [nd2]; exact nM)
      (by show IoRSR st K Locks s (L.nodeAt _ _ _); rw [nd2]; exact nR) M2.td M2.rs M2.dt M2.cd M2.af M2.dom M2.iok.1.sc
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
  -- the plan re-check: its words are in the read set
  have hsh : localinv.Plan.still_holds st p s2 = ok true := by
    rw [← hsh']
    exact still_holds_st p (fun w hw => (G3.m w (hSeen w hw)).symm)
  exact hr (invTail_true hb hnx hs1 hu hact hy hsf hh hsh ht)

/-- **`PathObl.dec_alt`** for the frame-cap invocation path at one entry. -/
theorem inv_dec_altR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K)
    {number : I64} {p : localinv.Plan} (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSeen : ∀ x, SeenW p x → IoRSR st K Locks s x) {a : A} {r r' : Bool × S × A}
    (h : syscall.handle_invocation_local st ar s a number p = ok r) (hr : r.1 ≠ true)
    (Al : Alt st (IoRSR st K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s')
    (h' : syscall.handle_invocation_local st ar s' a number p = ok r') :
    r'.1 ≠ true ∧
      syscall.handle_invocation_local (guard st (fun _ => True) (IoDS (st := st) s)) ar s' a number p = ok r' ∧
      syscall.handle_invocation_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s' a number p = ok r' := by
  have G : Ag st (IoRSR st K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
  have nC := (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD])).1
  have hcur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ nC
  have hpre : ∀ b, (b = regA (L.curW s') layout.reg.FAULT_IP ∨
      b = L.nodeAt s' (L.cpu s') layout.node.CUR_TIME ∨ b = L.nodeAt s' (L.cpu s') layout.node.CONSUMED) →
      IoDS (st := st) s b := by
    intro b hb
    rw [hcur, G.node, G.node] at hb
    exact hb
  have hn : r'.1 ≠ true := by
    obtain ⟨b, z, c⟩ := r'
    intro hb
    change b = true at hb
    subst hb
    exact inv_alt_not_accR hA P hSeen Al h hr h'
  refine ⟨hn, ?_, ?_⟩
  · refine handle_inv_dec_m ⟨fun _ _ => guard_read trivial, fun _ _ => guard_read_pair trivial trivial,
      fun _ => rfl, fun _ => rfl⟩ (fun y b v hb _ _ => guard_write (hpre b hb)) h' hn
  · have hR : RdEq st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) :=
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
    have hW : PreOK st (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) s' (L.curW s') := by
      intro y b v hb _ _
      obtain ⟨ha, hs⟩ := IoDS.safe P (hpre b hb)
      rw [L.write_eq]
      exact mguard_write (L.write_eq y b v) (stepOK_safe (m0 := m0) hK hLA ha hs)
    exact handle_inv_dec_m hR hW h' hn

end altR

end Fl4Proofs.P2.PathObl
