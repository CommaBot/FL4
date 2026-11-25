/-
# P2 (p2lf): a fired timer's waking signal, both branches, on `gS` and on `st`

At the state `X` after `remove` (a state with `TInv`), the bound notification `N` wakes a thread: its `WAITING`
queue's head, or its bound thread `t` in `Recv` (`WkCase`). `wk_sig` gives both halves the fire step needs:
`send_signal gS = send_signal st` (`wake_wait_fire` / `wake_recv_fire`), and for the `st` run: `TInv` and
`TAgree` after it (P1 `send_signal.tagree`, from `BufAt`), `ksb` / `cpu` kept, and the action `RESUME_CURRENT` or
the woken thread (`wake_wait_st` / `wake_recv_st`, with `WkPre` from `wkpre_true`).

* `WkCase`: the two waking cases at `X`, with what each branch's guard needs.
* `wk_sig`: the waking signal on both stores.

No named premises.
-/
import Fl4Proofs.P2.FootTimerFireWp
import Fl4Proofs.P2.FootTimerFireWs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (NodeSt ScAcc)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The two waking cases of a fired timer's signal** at the state `X` after `remove` (module docstring): the
notification `N` is `WAITING` and its head may run here, or it is `IDLE` with its bound thread `t` in `Recv` that
may run here, blocked on an endpoint whose lock is held (`Lk`), with the endpoint's words and the reply's `TCB`
word accessible (`R` / `W`). -/
def WkCase (st : machine.Store S) [L : LawfulStore st] (R W : U64 → Prop) (Lk : U64 → Prop) (cpu : U64) (X : S)
    (N t : U64) : Prop :=
  (L.epState X N = obj.NTFN_WAITING ∧ (L.epQ X N).head ≠ L.curW X ∧
    L.mem X (affA (L.epQ X N).head) = cpu ∧
    L.mem X (domA (L.epQ X N).head) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) ∧
    (L.mem X (scA (L.epQ X N).head) = 0#u64 → L.mem X (ntfnScA N) = 0#u64)) ∨
  (L.epState X N = obj.NTFN_IDLE ∧ L.mem X (ntfnBtA N) = t ∧ t ≠ 0#u64 ∧
    L.mem X (stA t) = sched.TS_BLOCKED_ON_RECV ∧ t ≠ L.curW X ∧ L.mem X (affA t) = cpu ∧
    L.mem X (domA t) = L.mem X (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN) ∧
    (L.mem X (scA t) = 0#u64 → L.mem X (ntfnScA N) = 0#u64) ∧ Lk (L.mem X (blockA t)) ∧
    (∀ k : U64, k.val < 16 → k.val % 8 = 0 →
      R (core.num.U64.wrapping_add (L.mem X (blockA t)) k) ∧ W (core.num.U64.wrapping_add (L.mem X (blockA t)) k)) ∧
    (L.mem X (replyA t) ≠ 0#u64 → W (rTcbA (L.mem X (replyA t)))))

end

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxRecDepth 4000 in
set_option maxHeartbeats 16000000 in
/-- **The waking signal on both stores** (module docstring). -/
theorem wk_sig {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {s X : S} (a : A) {N badge t : U64}
    {Lk : U64 → Prop} {U : Set U64}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hBA : BufAt st T Cs H Sg Scs Z U X)
    (hNN : N ∈ Nt) (hHN : H N = some .ntfn)
    (hAffSc : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (kX : L.ksb X = L.ksb s) (cX : L.cpu X = L.cpu s)
    (kT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (K.val < 3528 ∨ 3576 ≤ K.val) →
      L.mem X (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (hac : L.actionW X = sched.ACTION_RESUME_CURRENT)
    (hwk : WkCase st R W Lk (L.cpu s) X N t)
    (rN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → R (core.num.U64.wrapping_add N k))
    (wN : ∀ k : U64, k.val < 64 → k.val % 8 = 0 → k.val ≠ 24 → W (core.num.U64.wrapping_add N k))
    (rL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ TimerField K.val →
      ¬ GField K.val → R (core.num.U64.wrapping_add y K))
    (wL : ∀ y, LocT st T s y → ∀ K : U64, 256 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → ¬ GateField K.val →
      ¬ TimerField K.val → ¬ GField K.val → K.val ≠ 3328 → W (core.num.U64.wrapping_add y K))
    (rS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → R b)
    (wS : ∀ p ∈ Scs, L.mem s (scCoreA p) = L.cpu s → ∀ b, Aligned b → InSC p (Z p) b → b.val ≠ p.val + 16 → W b)
    (lkL : ∀ y ∈ T, QueuedState (L.mem s (stA y)) → Lk (L.mem s (blockA y)) → ∀ k : U64,
      (k.val = 3496 ∨ k.val = 3504) → R (core.num.U64.wrapping_add y k) ∧ W (core.num.U64.wrapping_add y k))
    (hLk : Lk N)
    (nRW : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o))
    (rCD : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN))
    (hSW : StW st gS T Lk s) :
    notification.send_signal gS ar X a N badge = notification.send_signal st ar X a N badge ∧
    ∀ X2 a2, notification.send_signal st ar X a N badge = ok (X2, a2) →
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X2 ∧ TAgree st T Cs X X2 ∧ L.ksb X2 = L.ksb X ∧ L.cpu X2 = L.cpu X ∧
      ∃ w ∈ T, (L.actionW X2 = sched.ACTION_RESUME_CURRENT ∨ L.actionW X2 = w) := by
  have hTX' := hTX
  obtain ⟨⟨Q, Rq, hq⟩, hBd, hXX, hSS, hSgX⟩ := hTX
  obtain ⟨E, EQ, hEW⟩ := hq.eps
  have hT := hq.tcbs
  have he : N ∈ E := (hEW.2.2.2.2.2.2.2.1 N).2 (Or.inr hHN)
  have hnsΩ : ntfnScA N ∈ Ω := hSgX.sub _ (hXX.1.ntW N hNN)
  -- `TInv`, `TAgree`, `ksb` after the signal on `st`
  have post : ∀ X2 a2, notification.send_signal st ar X a N badge = ok (X2, a2) →
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X2 ∧ TAgree st T Cs X X2 ∧ L.ksb X2 = L.ksb X := by
    intro X2 a2 hr
    have tg := notification.send_signal.tagree hA X a N badge hTX' hNN hHN hBA.1 hBA.2
    rw [hr, WP.spec_ok] at tg
    try simp only [WP.uncurry'_pair] at tg
    exact tg
  rcases hwk with ⟨hwt, hcur, haf, hdom, hnd⟩ | ⟨hidle, hbt, ht0, hrecv, hcur, haf, hdom, hnd, hLkE, rwE, wRt⟩
  · -- `WAITING`
    refine ⟨wake_wait_fire ar a hTX' hNN hHN hAffSc kX cX kT hcur hac hwt haf hdom hnd rN wN rL wL rS wS lkL hLk
      nRW rCD hSW, fun X2 a2 hr => ?_⟩
    obtain ⟨p1, p2, p3⟩ := post X2 a2 hr
    obtain ⟨hE, -, hqr⟩ := hEW.1 N he
    obtain ⟨-, -, -, -, -, k5⟩ := hEW.2.2.2.2.2
    have hwt1 : L.epState X N = 1#u64 := by rw [hwt]; simp [obj.NTFN_WAITING]
    have hne : EQ N ≠ [] := fun h0 => (k5 N he h0).2 hHN hwt1
    obtain ⟨y0, ys, hys⟩ := List.exists_cons_of_ne_nil hne
    obtain ⟨w, ew⟩ : ∃ w, (L.epQ X N).head = w := ⟨_, rfl⟩
    rw [ew] at hcur haf hdom hnd
    have hmem : w ∈ EQ N := by
      have : w = y0 := by rw [← ew, hqr.head, hys]; rfl
      rw [this, hys]; exact List.mem_cons_self
    obtain ⟨-, -, hbl⟩ := hEW.2.2.2.1 N he w hmem
    have hwT : w ∈ T := hqr.mem w hmem
    obtain ⟨P, hscΩ, hAo⟩ := wkpre_true (N := N) hTX' hAffSc kX cX kT hwT hbl haf hdom hnd
    obtain ⟨-, wi, act⟩ := wake_wait_st ar X a N badge w hq hEW he hwt ew hmem hcur hac P hnsΩ hscΩ hAo hr
    exact ⟨p1, p2, p3, wi.2.1, w, hwT, act⟩
  · -- idle-bound `Recv`
    obtain ⟨ep, heq⟩ : ∃ ep, L.mem X (blockA t) = ep := ⟨_, rfl⟩
    obtain ⟨r, hr⟩ : ∃ r, L.mem X (replyA t) = r := ⟨_, rfl⟩
    rw [heq] at hLkE rwE
    rw [hr] at wRt
    refine ⟨wake_recv_fire ar a hTX' hNN hHN hAffSc kX cX kT hidle hbt ht0 hrecv heq hr hcur hac haf hdom hnd rN
      rL wL rS wS lkL hLkE rwE wRt nRW rCD hSW, fun X2 a2 hrun => ?_⟩
    obtain ⟨p1, p2, p3⟩ := post X2 a2 hrun
    have htT : t ∈ T := by
      rcases TInv.ntb hTX' N hNN with h | h
      · rw [hbt] at h; exact absurd h ht0
      · rwa [hbt] at h
    have hblk : Blocked (L.mem X (stA t)) := Or.inr (Or.inl hrecv)
    obtain ⟨hep, hmem⟩ := hEW.2.2.2.2.1 t htT (by simp) hblk
    rw [heq] at hep hmem
    obtain ⟨P, hscΩ, hAo⟩ := wkpre_true (N := N) hTX' hAffSc kX cX kT htT hblk haf hdom hnd
    obtain ⟨-, wi, act⟩ := wake_recv_st ar X a N badge t ep r hq hEW hidle hbt ht0 hrecv heq hep hmem hr
      (fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).1) hcur hac P hnsΩ hscΩ
      (fun hr0 => (recv_rt (Z := Z) hTX' hNN htT hrecv hr hr0).2) hAo hrun
    exact ⟨p1, p2, p3, wi.2.1, t, htT, act⟩

end main

end Fl4Proofs.P2
