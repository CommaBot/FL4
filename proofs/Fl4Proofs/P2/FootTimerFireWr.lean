/-
# P2 (p2lf): a fired timer's idle-bound `Recv` wake on the guarded store, from the entry state's word sets

The `Recv` half of `P2/FootTimerFireWf`: `wake_recv_guard` (`P2/FootTimerFireWk`) with its word premises taken from
the broad per-class premises at the entry state `s` (as `wake_wait_fire`), plus the endpoint's words (`rwE`) and the
reply's `TCB` word (`wRt`), which the caller gets from `ObjLay` [J] and the held locks of the endpoint / reply.

* `scSb`: the SC size used for a woken thread (`0` when it has no SC: then no word is in its SC).
* `recv_rt`: a receiver's reply object: its `TCB` word is aligned and none of the words `wake_recv_guard` keeps.
* `wake_recv_fire`: the idle-bound `Recv` branch of `send_signal` on `gS` is its real run.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (NodeSt ScAcc)

/-- The SC size of a woken thread's SC `c` (`0` for no SC). -/
def scSb (Z : U64 → Nat) (c : U64) : Nat := if c = 0#u64 then 0 else Z c

theorem scSb_ne {Z : U64 → Nat} {c : U64} (h : c ≠ 0#u64) : scSb Z c = Z c := by
  unfold scSb; rw [if_neg h]

section rt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxHeartbeats 4000000 in
/-- **A receiver's reply object** at a state with `TInv`: its `TCB` word is aligned and none of the words that
`wake_recv_guard`'s `hRt` lists. -/
theorem recv_rt {X : S} {N t r : U64} (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hNN : N ∈ Nt) (ht : t ∈ T)
    (hrecv : L.mem X (stA t) = sched.TS_BLOCKED_ON_RECV) (hr : L.mem X (replyA t) = r) (hr0 : r ≠ 0#u64) :
    Aligned (rTcbA r) ∧ ∀ b, (b = ntfnScA N ∨
      (Aligned b ∧ InSC (L.mem X (scA t)) (scSb Z (L.mem X (scA t))) b) ∨
      b = core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN ∨
      (∃ o : U64, o.val < 4288 ∧ b = L.nodeAt X (L.cpu X) o) ∨
      (∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add t K)) → b ≠ rTcbA r := by
  obtain ⟨⟨Q, Rq, hq⟩, -, hXX, -, hSgX⟩ := hTX
  have hrp : r ∈ Rp := by
    have := (hXX.2.1.recv t ht hrecv (by rw [hr]; exact hr0)).1; rwa [hr] at this
  obtain ⟨r32, rv, -, -⟩ := rp_facts hXX.1 hrp
  have hSg : rTcbA r ∈ Sg := hXX.1.tcbW hrp
  have hO := hq.omega _ (hSgX.sub _ hSg)
  refine ⟨by unfold Aligned; rw [rv]; omega, ?_⟩
  rintro b (rfl | ⟨-, hin⟩ | rfl | ⟨o, ho, rfl⟩ | ⟨K, hK, rfl⟩) e
  · have e' := congrArg UScalar.val e
    rw [rv] at e'
    have := hXX.1.ntRp N hNN r hrp; omega
  · have e' := congrArg UScalar.val e
    rw [rv] at e'
    by_cases h0 : L.mem X (scA t) = 0#u64
    · rw [h0] at hin
      unfold scSb at hin; rw [if_pos rfl] at hin
      have := hXX.1.rp0 r hrp
      have hz : r.val ≠ 0 := fun h => this (UScalar.eq_of_val_eq (by rw [h]; rfl))
      have := hin.2; simp at this; omega
    · rw [scSb_ne h0] at hin
      have hc := (hXX.2.2.toScExtra0.bound t ht h0).1
      have := hXX.1.rpSc r hrp _ hc
      have := hin.1; have := hin.2; omega
  · have e' := congrArg UScalar.val e
    rw [ks_val hq (by simp [layout.ks.CUR_DOMAIN])] at e'
    have := hSgX.ks _ hSg
    simp [layout.ks.CUR_DOMAIN] at e'; omega
  · exact out_ne_node hO hq.cur (hq.nodes _ hq.cur) ho (congrArg UScalar.val e)
  · exact out_ne_field hO ht (hq.tcbs t ht) hK (congrArg UScalar.val e)

end rt

section recv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **The idle-bound `Recv` branch of a fired timer's signal on the guarded store, from the entry state's sets**
(module docstring). `t` is the notification's bound thread, in `Recv` on `ep` with reply `r`. -/
theorem wake_recv_fire {A : Type} (ar : machine.Arch A) {s X : S} (a : A) {N badge t ep r : U64}
    {Lk : U64 → Prop}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hNN : N ∈ Nt) (hHN : H N = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hidle : L.epState X N = obj.NTFN_IDLE) (hbt : L.mem X (ntfnBtA N) = t) (ht0 : t ≠ 0#u64)
    (hrecv : L.mem X (stA t) = sched.TS_BLOCKED_ON_RECV)
    (heq : L.mem X (blockA t) = ep) (hr : L.mem X (replyA t) = r)
    (hcur : t ≠ L.curW X) (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (haf : L.mem X (affA t) = L.cpu s)
    (hdom : L.mem X (domA t) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN))
    (hnd : L.mem X (scA t) = 0#u64 → L.mem X (ntfnScA N) = 0#u64)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLkE : Lk ep)
    (rwE : ∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add ep k) ∧ W (core.num.U64.wrapping_add ep k))
    (wRt : r ≠ 0#u64 → W (rTcbA r))
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s) :
    notification.send_signal gS ar X a N badge = notification.send_signal st ar X a N badge := by
  have hTX' := hTX
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXX, hSS, hSgX⟩ := hTX
  obtain ⟨E, EQ, hEW⟩ := hq.eps
  have hT := hq.tcbs
  have htT : t ∈ T := by
    rcases TInv.ntb hTX' N hNN with h | h
    · rw [hbt] at h; exact absurd h ht0
    · rwa [hbt] at h
  have hblk : Blocked (L.mem X (stA t)) := Or.inr (Or.inl hrecv)
  obtain ⟨hep, hmem⟩ := hEW.2.2.2.2.1 t htT (by simp) hblk
  rw [heq] at hep hmem
  obtain ⟨hE, -, hqr⟩ := hEW.1 ep hep
  obtain ⟨-, -, -, k3, -, -⟩ := hEW.2.2.2.2.2
  have ht' := hT t htT
  -- `t` at `s`
  have k3328 : L.mem X (stA t) = L.mem s (stA t) := by
    rw [stA_eq]; exact kT t htT 3328#u64 (by simp) (by simp) (Or.inl (by simp))
  have k3336 : L.mem X (blockA t) = L.mem s (blockA t) := by
    rw [blockA_eq]; exact kT t htT 3336#u64 (by simp) (by simp) (Or.inl (by simp))
  have k3464 : L.mem X (scA t) = L.mem s (scA t) := by
    rw [scA_eq]; exact kT t htT 3464#u64 (by simp) (by simp) (Or.inl (by simp))
  have hloc : LocT st T s t := by
    refine ⟨htT, ?_⟩
    rw [← haf]; unfold affA; exact (kT t htT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).symm
  -- the endpoint queue's members: receivers blocked on `ep`, queued at `s`
  have qS : ∀ z ∈ EQ ep, QueuedState (L.mem s (stA z)) ∧ Lk (L.mem s (blockA z)) := by
    intro z hz
    obtain ⟨-, hb, -⟩ := hEW.2.2.2.1 ep hep z hz
    have hzT := hqr.mem z hz
    have hs : L.mem X (stA z) = sched.TS_BLOCKED_ON_RECV := by rw [k3 ep hep z hz t hmem, hrecv]
    rw [stA_eq, ← kT z hzT 3328#u64 (by simp) (by simp) (Or.inl (by simp)), ← stA_eq, hs,
      blockA_eq, ← kT z hzT 3336#u64 (by simp) (by simp) (Or.inl (by simp)), ← blockA_eq, hb]
    exact ⟨Or.inl (by simp [sched.TS_BLOCKED_ON_RECV]), hLkE⟩
  have lnk : ∀ z ∈ EQ ep, R (prevA .Ep z) ∧ R (nextA .Ep z) ∧ W (prevA .Ep z) ∧ W (nextA .Ep z) := by
    intro z hz
    obtain ⟨q1, q2⟩ := qS z hz
    have hzT := hqr.mem z hz
    obtain ⟨p1, p2⟩ := lkL z hzT q1 q2 3504#u64 (Or.inr (by simp))
    obtain ⟨n1, n2⟩ := lkL z hzT q1 q2 3496#u64 (Or.inl (by simp))
    exact ⟨p1, n1, p2, n2⟩
  have rw' : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val → ¬ GField K.val →
      R (core.num.U64.wrapping_add t K) := rL t hloc
  -- the node
  have eN : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by rw [cX, nodeAt_of_ksb kX]
  have hn : NodeSt (L := L) R W X := by
    unfold PathObl.NodeSt
    rw [eN, eN]
    exact ⟨(nRW _ (by rw [curth_val]; omega) (by rw [curth_val])).1,
      (nRW _ (by rw [act_val]; omega) (by rw [act_val])).1, (nRW _ (by rw [act_val]; omega) (by rw [act_val])).2⟩
  -- the badge register
  have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
  obtain ⟨KB, hKB, eKB⟩ := regA_eq ht' (r := layout.reg.BADGE) (by rw [hbv]; omega)
  have hKB' : KB.val = 256 := by rw [hKB, hbv]
  have gB1 : ¬ GateField KB.val := by unfold GateField; omega
  have gB2 : ¬ TimerField KB.val := by unfold TimerField; omega
  have gB3 : ¬ GField KB.val := by unfold GField; omega
  -- the woken thread's SC
  have scF : L.mem X (scA t) ≠ 0#u64 → L.mem X (scA t) ∈ Scs ∧ L.mem s (scCoreA (L.mem X (scA t))) = L.cpu s ∧
      L.mem X (scA t) ∈ Ac := by
    intro h0
    have hs0 : L.mem s (scA t) ≠ 0#u64 := by rw [← k3464]; exact h0
    refine ⟨(hXX.2.2.toScExtra0.bound t htT h0).1, by rw [k3464, hAffSc t htT hs0]; exact hloc.2, ?_⟩
    exact hBd.sact t htT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hrecv)))))))) h0
  let sb : Nat := scSb Z (L.mem X (scA t))
  have esb : L.mem X (scA t) ≠ 0#u64 → sb = Z (L.mem X (scA t)) := fun h0 => scSb_ne h0
  have P : WkPre st R W X t N sb := by
    refine ⟨fun h0 => ?_, fun _ => ?_, hnd, hdom, by rw [haf, cX], fun h0 => ?_, fun h0 => ?_, fun h0 => ?_,
      fun h0 => ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact rS _ c1 c2 _ hcq.2.2.2.2 hcq.2.2.2.1
    · exact rN layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    · obtain ⟨c1, c2, -⟩ := scF h0
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      obtain ⟨h8, h128, -⟩ := sc_lo hP hz
      have hv := sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
      have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
      exact rS _ c1 c2 _ (by unfold Aligned; unfold sporA; rw [hv, hsv]; omega)
        ⟨by unfold sporA; rw [hv]; omega, by unfold sporA; rw [hv, hsv]; omega⟩
    · rw [esb h0]
      obtain ⟨c1, c2, -⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      refine ⟨fun b ha hb => rS _ c1 c2 b ha hb, fun b ha hb => wS _ c1 c2 b ha hb.inSC (by
        have := hb.1; omega), ?_⟩
      obtain ⟨⟨q1, q2⟩, q3⟩ := hcq.2.2.1
      have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
      obtain ⟨hP, hz⟩ := hXX.1.sc _ c1
      have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
      exact wS _ c1 c2 _ q3 ⟨q1, q2⟩ (by rw [hv, hcv]; omega)
    · rw [esb h0]
      obtain ⟨c1, -, c3⟩ := scF h0
      have hcq := scq_of hXX.1 hSS c1
      exact hcq.1 ((hSS.act _ c1).1 c3)
    · rw [esb h0]
      obtain ⟨c1, -, -⟩ := scF h0
      have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
      have aR : Aligned (L.nodeA X layout.node.REPROGRAM) :=
        nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
      refine ⟨aR, ?_⟩
      unfold Outside
      by_contra hc
      push_neg at hc
      have hΩ := hXX.1.scW _ c1 _ aR ⟨hc.1, hc.2⟩
      exact out_ne_node (hq.omega _ hΩ) hq.cur hN (o := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM]) rfl
    · show R (L.nodeAt X (L.cpu X) layout.node.CUR_TIME)
      rw [eN]; exact (nRW _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
    · show W (L.nodeAt X (L.cpu X) layout.node.REPROGRAM)
      rw [eN]; exact (nRW _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2
    · rw [eN]; exact (nRW _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    · rw [kX]; exact rCD
  -- the reply
  have hRt := fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).2
  have aRt := fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).1
  -- `t`'s words outside the ones `cancel_ipc` writes keep their values along `CnD`
  have epT : ∀ (K : U64), K.val < 4096 → ∀ b, (b = epHeadA ep ∨ b = epTSA ep) →
      core.num.U64.wrapping_add t K ≠ b := by
    intro K hK b hb e
    have e' := congrArg UScalar.val e
    rw [field_val ht' hK] at e'
    rcases hb with rfl | rfl
    · rw [epHeadA_val] at e'; rcases hE.disj t htT with h' | h' <;> omega
    · rw [epTSA_val hE] at e'; rcases hE.disj t htT with h' | h' <;> omega
  have lnkT : ∀ (K : U64), K.val < 4096 → K.val ≠ 3496 → K.val ≠ 3504 → ∀ b, LinkOf .Ep (EQ ep) b →
      core.num.U64.wrapping_add t K ≠ b := by
    rintro K hK h1 h2 b ⟨y, hy, rfl | rfl⟩ <;>
      exact tcb_word_ne ht' (hT y (hqr.mem y hy)) hK (by simp [nextOff, prevOff])
        (fun e => by subst e; simp [nextOff, prevOff]; omega)
  have cK : ∀ (Y : S), WritesIn st X Y (CnD (EQ ep) ep t r) → ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      K.val ≠ 3376 → K.val ≠ 3496 → K.val ≠ 3504 → K.val ≠ 3328 →
      L.mem Y (core.num.U64.wrapping_add t K) = L.mem X (core.num.U64.wrapping_add t K) := by
    intro Y wY K hK h8 n1 n2 n3 n4
    refine wY.mem_eq (field_aligned ht' hK h8) ?_
    rintro (e | e | ⟨hr0, e⟩ | e)
    · exact tcb_word_ne ht' ht' (K2 := 3376#u64) hK (by simp) (fun _ => by simp; omega) e
    · rcases e with e | e | e
      · exact lnkT K hK n2 n3 _ e rfl
      · exact epT K hK _ (Or.inl e) rfl
      · exact epT K hK _ (Or.inr e) rfl
    · exact hRt hr0 _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨K, hK, rfl⟩)))) e
    · rw [stA_eq] at e; exact tcb_word_ne ht' ht' (K2 := 3328#u64) hK (by simp) (fun _ => by simp; omega) e
  have sW : ∀ v : U64, ¬ QueuedState v → ∀ Y, WritesIn st X Y (CnD (EQ ep) ep t r) →
      gS.write Y (stA t) v = st.write Y (stA t) v := by
    intro v hv Y wY
    refine hSW Y t v hloc ?_ (fun _ => ?_) hv
    · unfold affA
      rw [cK Y wY 3520#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]
      exact (kT t htT 3520#u64 (by simp) (by simp) (Or.inl (by simp))).trans hloc.2
    · rw [blockA_eq, cK Y wY 3336#u64 (by simp) (by simp) (by simp) (by simp) (by simp) (by simp), ← blockA_eq,
        heq]; exact hLkE
  have hE0 := rwE layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  have hE8 := rwE layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])
  have rT : ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val → ¬ GField K.val →
      R (core.num.U64.wrapping_add t K) := rw'
  refine wake_recv_guard ar X a N badge t ep r (sb := sb) hq hEW hidle hbt ht0 hrecv heq hep hmem hr
    (rN _ (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]))
    (ep_aligned (hEW.1 N ((hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN))).1).2
    (hq.omega _ (hSgX.sub _ (hXX.1.ntB N hNN).1)).1
    (rN _ (by simp [layout.ntfn.BOUND_TCB]) (by simp [layout.ntfn.BOUND_TCB]))
    (wL t hloc 3376#u64 (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])
      (by simp [GField]) (by simp))
    (by rw [stA_eq]; exact rT 3328#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [blockA_eq]; exact rT 3336#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rT 3360#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    hE0.1 hE8.1 hE0.2 hE8.2
    (lnk t hmem).1 (lnk t hmem).2.1 (lnk t hmem).2.2.1 (lnk t hmem).2.2.2
    (fun hE' => (lnk _ ((qmem_nbrs hqr hmem).1 hE')).2.2.1)
    (fun hH' => (lnk _ ((qmem_nbrs hqr hmem).2 hH')).2.2.2)
    (fun hr0 => ⟨wRt hr0, aRt hr0⟩) P.mx hcur hn
    (by rw [scA_eq]; exact rT 3464#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [inqA_eq]; exact rT 3592#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rT 3432#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (rT 3520#u64 (by simp) (by simp) (by simp) (by simp [TimerField]) (by simp [GField]))
    (by rw [eKB]; exact wL t hloc KB (by omega) (by omega) (by omega) gB1 gB2 gB3 (by omega)) hac
    (sW _ (by simp [QueuedState, sched.TS_INACTIVE])) (sW _ (by simp [QueuedState, sched.TS_RUNNING])) P
    (hSgX.sub _ (hXX.1.ntW N hNN)) (fun h0 b hb hin => hXX.1.scW _ (scF h0).1 b hb (by rw [← esb h0]; exact hin))
    hRt

end recv

end Fl4Proofs.P2
