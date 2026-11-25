/-
# P2: the round-robin case's choice: after `append`, the current thread is the highest and alone in its queue

`highest_prio_app`: `round_robin_ok` accepted with the L1 bitmap empty or the highest marked priority below the
current thread's, so the thread's ready queue was empty (a non-empty queue sets its bitmap bits, P1
`BitmapOK`, and `highest_prio` finds the highest marked priority, P1 `sched.highest_prio.spec`). After `append`
(P1 `sched.append.ready`) the queue is `[d]` (head = tail = `d`), the L1 word is set, and `highest_prio` is `d`'s
priority (any other marked priority was marked before, hence below it). This is the shape of P1
`highest_prio_enq` (FastFin) for `append` and `round_robin_ok`'s test.

No named premises.
-/
import Fl4Proofs.P2.FootTimerIrqRF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section law
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64}

/-- **After `append` of an unqueued thread whose priority beats every marked one** (module docstring). -/
theorem highest_prio_app {X Y : S} {d dom : U64} {Q : U64 → List U64} (hT : TcbPlaced T) (hd : d ∈ T)
    (hp : (L.mem X (prioA d)).val < 256) (hN : NodePlaced st T X (L.cpu X))
    (haff : L.mem X (affA d) = L.cpu X) (hRQ : ReadyQueues st T X (L.cpu X) Q)
    (hnq : (L.mem X (inqA d) &&& sched.Q_QUEUED) = 0#u64) (hdq : ∀ p' : U64, p'.val < 256 → d ∉ Q p')
    (hhi : L.l1W X (L.cpu X) = 0#u64 ∨ ∃ h, sched.highest_prio st X dom = ok h ∧ h < L.mem X (prioA d))
    (hY : sched.append st X d = ok Y) (hNY : NodePlaced st T Y (L.cpu X)) (hcY : L.cpu Y = L.cpu X) :
    sched.highest_prio st Y 0#u64 = ok (L.mem X (prioA d)) ∧ L.l1W Y (L.cpu Y) ≠ 0#u64 ∧
      L.mem Y (L.nodeAt Y (L.cpu X) (rqOff (L.mem X (prioA d)))) = d ∧
      L.mem Y (L.nodeAt Y (L.cpu X) (rqTailOff (L.mem X (prioA d)))) = d ∧
      ReadyQueues st T Y (L.cpu X) (Function.update Q (L.mem X (prioA d)) [d]) := by
  have E := sched.append.ready (L := L) X d Q hT hd hp (by rw [haff]; exact hN) hN (by rw [haff]; exact hRQ)
    (fun _ => hdq)
  rw [hY, WP.spec_ok, haff] at E
  simp only [hnq, ne_eq, not_true_eq_false, ↓reduceIte] at E
  obtain ⟨-, hBX⟩ := hRQ
  have mk : ∀ q : U64, q.val < 256 → Q q ≠ [] → L.l1W X (L.cpu X) ≠ 0#u64 := fun q hq hne => by
    have hb := (hBX.l2 q hq).2 hne
    have hw : L.l2W X (L.cpu X) (q.val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hb⟩
    have hl := (hBX.l1 (q.val / 64) (by omega)).2 ⟨by omega, hw⟩
    exact (ne_zero_iff_bit _).2 ⟨_, by omega, hl⟩
  have below : ∀ q : U64, q.val < 256 → Q q ≠ [] → q.val < (L.mem X (prioA d)).val := fun q hq hne => by
    have hlX := mk q hq hne
    rcases hhi with h0 | ⟨h, hh, hlt⟩
    · exact absurd h0 hlX
    · obtain ⟨h', hh', -, -, hh3⟩ := spec_ex_fd (sched.highest_prio.spec (L := L) X dom _ hN hBX hlX)
      rw [hh] at hh'
      have e := ok_inj_ff hh'
      subst e
      have h1 := hh3 q hq hne
      have h2 : h.val < (L.mem X (prioA d)).val := hlt
      omega
  have hQp : Q (L.mem X (prioA d)) = [] := by
    by_contra hne
    have := below _ hp hne
    omega
  rw [hQp, List.nil_append] at E
  have hNE : (Function.update Q (L.mem X (prioA d)) [d]) (L.mem X (prioA d)) ≠ [] := by simp
  have hB := E.2
  have hl1 : L.l1W Y (L.cpu X) ≠ 0#u64 := by
    have hb := (hB.l2 _ hp).2 hNE
    have hw : L.l2W Y (L.cpu X) ((L.mem X (prioA d)).val / 64) ≠ 0#u64 := (ne_zero_iff_bit _).2 ⟨_, by omega, hb⟩
    have hl := (hB.l1 ((L.mem X (prioA d)).val / 64) (by omega)).2 ⟨by omega, hw⟩
    exact (ne_zero_iff_bit _).2 ⟨_, by omega, hl⟩
  have hr := E.1.rel _ hp
  have e1 := hr.head
  have e2 := hr.last
  simp only [Function.update_self] at e1 e2
  refine ⟨?_, by rw [hcY]; exact hl1, e1, e2, E⟩
  have hNY' : NodePlaced st T Y (L.cpu Y) := by rw [hcY]; exact hNY
  have hB' : BitmapOK st Y (L.cpu Y) (fun p' => Function.update Q (L.mem X (prioA d)) [d] p' ≠ []) := by
    rw [hcY]; exact hB
  obtain ⟨q, hq, hq1, hq2, hq3⟩ :=
    spec_ex_fd (sched.highest_prio.spec (L := L) Y 0#u64 _ hNY' hB' (by rw [hcY]; exact hl1))
  rw [hq]
  have hpq : (L.mem X (prioA d)).val ≤ q.val := hq3 _ hp hNE
  have hqp : q.val ≤ (L.mem X (prioA d)).val := by
    by_cases e : q = L.mem X (prioA d)
    · rw [e]
    · rw [Function.update_of_ne e] at hq2
      have := below q hq1 hq2
      omega
  exact congrArg ok (UScalar.eq_of_val_eq (by omega))

end law

end Fl4Proofs.P2
