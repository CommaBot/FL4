/-
# P2 (p2lf): a fired timer's waking signal, both branches, on `gS` and on `st`

At the state `X` after `remove` (a state with `TInv`), the bound notification `N` wakes a thread: its `WAITING`
queue's head, or its bound thread `t` in `Recv` (`WkCase`). `wk_sig` gives both halves the fire step needs:
`send_signal gS = send_signal st` (`wake_wait_fire` / `wake_recv_fire`), and for the `st` run: `TInv` and
`TAgree` after it (P1 `send_signal.tagree`, from `BufAt`), `ksb` / `cpu` kept, and the action `RESUME_CURRENT` or
the woken thread (`wake_wait_st` / `wake_recv_st`, with `WkPre` from `wkpre_true`).

* `WkCase`: the two waking cases at `X`, with what each branch's guard needs.
* `probe_nd`, `epfoot_nd`: a word every `D`-run keeps is not in `D`; `EpFoot` holds no `Ω` / node / non-link word.
* `WkKeep`, `wk_keep`: what the waking signal keeps (node words but `SCHED_ACTION` / `REPROGRAM`, thread words but
  `EP` links and the woken thread's `STATE` / badge / fault word, SCs other than the woken thread's).
* `wk_sig`: the waking signal on both stores, with `WkKeep` for the `st` run.

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

section keep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- A word that every run writing only `D` keeps is not in `D` (probe it with one write). -/
theorem probe_nd {X : S} {D : U64 → Prop} {b : U64} (hb : Aligned b)
    (keep : ∀ X', WritesIn st X X' D → L.mem X' b = L.mem X b) : ¬ D b := by
  intro hD
  have w : WritesIn st X (L.wr X b (if L.mem X b = 0#u64 then 1#u64 else 0#u64)) D :=
    (writesIn_wr (st := st) hb).mono (fun b' e => by subst e; exact hD)
  have k := keep _ w
  rw [L.mem_wr _ _ _ _ hb hb, if_pos rfl] at k
  by_cases h : L.mem X b = 0#u64
  · rw [if_pos h, h] at k; simp at k
  · rw [if_neg h] at k; exact h k.symm

/-- **What a waking signal keeps**, from its start `X` to its end `X2`: this core's node words other than
`SCHED_ACTION` (16) and `REPROGRAM` (56); every thread's words other than its `EP` links, and for the woken thread
`w` also other than its `STATE`, badge register and fault word; the words of every SC other than `w`'s. -/
def WkKeep (st : machine.Store S) [L : LawfulStore st] (T Scs : Set U64) (Z : U64 → Nat) (X X2 : S) (w : U64) :
    Prop :=
  (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 →
    L.mem X2 (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o)) ∧
  (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
    (y = w → K.val ≠ 3328 ∧ K.val ≠ 256 ∧ K.val ≠ 3376) →
    L.mem X2 (core.num.U64.wrapping_add y K) = L.mem X (core.num.U64.wrapping_add y K)) ∧
  (∀ c ∈ Scs, c ≠ L.mem X (scA w) → ∀ b, Aligned b → InSC c (Z c) b → L.mem X2 b = L.mem X b)

/-- `EpFoot` of a queue of `E` holds no word of `Ω`, no node word of this core and no thread word other than an `EP`
link (`epfoot_keep`, probed). -/
theorem epfoot_nd {X : S} {Xs E : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {EQ : U64 → List U64}
    {n : U64} (hq : SchedQueuesInvX st T Cs Ω H Xs X Q Rq) (hEW : EpsWit st T Cs Ω H Xs X E EQ) (he : n ∈ E)
    (hWT : ∀ y ∈ EQ n, y ∈ T) :
    (∀ b, Aligned b → b ∈ Ω → ¬ EpFoot (EQ n) n b) ∧
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ EpFoot (EQ n) n (L.nodeAt X (L.cpu X) o)) ∧
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      ¬ EpFoot (EQ n) n (core.num.U64.wrapping_add y K)) := by
  have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
  refine ⟨fun b hb hΩ => probe_nd (st := st) (X := X) hb fun X' hw => (epfoot_keep hq hEW he hWT hw).2.1 b hΩ,
    fun o ho h8 => probe_nd (st := st) (X := X) (nodeAt_aligned hN ho h8) fun X' hw => ?_,
    fun y hy K hK h8 h1 h2 => probe_nd (st := st) (X := X) (field_aligned (hq.tcbs y hy) hK h8) fun X' hw =>
      (epfoot_keep hq hEW he hWT hw).1 y hy K hK h8 h1 h2⟩
  have := (epfoot_keep hq hEW he hWT hw).2.2 o ho h8
  rwa [hw.2.1, nodeAt_of_ksb hw.1] at this

set_option maxHeartbeats 4000000 in
/-- **`WkKeep` from the waking signal's writes** (`wake_wait_st` / `wake_recv_st`), given that their queue part
`D` holds no node word, no thread word other than an `EP` link (and `w`'s `STATE` / fault word) and no SC word. -/
theorem wk_keep {X X2 : S} {D : U64 → Prop} {w : U64}
    (hTX : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac X) (hw : w ∈ T)
    (hW : WritesIn st X X2 (fun b => D b ∨ WkD st X w b ∨
      InRing (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) b ∨ b = L.nodeA X layout.node.REPROGRAM))
    (dN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ D (L.nodeAt X (L.cpu X) o))
    (dT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = w → K.val ≠ 3328 ∧ K.val ≠ 3376) → ¬ D (core.num.U64.wrapping_add y K))
    (dS : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → ¬ D b) :
    WkKeep st T Scs Z X X2 w := by
  obtain ⟨⟨Q, Rq, hq⟩, -, hXX, -, -⟩ := hTX
  have hO := hXX.1
  have hT := hq.tcbs
  have hcC := hq.cur
  have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hcC
  have hw' := hT w hw
  have eR : L.nodeA X layout.node.REPROGRAM = L.nodeAt X (L.cpu X) layout.node.REPROGRAM := rfl
  have hbv : layout.reg.BADGE.val = 0 := by unfold layout.reg.BADGE layout.reg.RDI; rfl
  obtain ⟨KB, hKB, eB⟩ := regA_eq hw' (r := layout.reg.BADGE) (by rw [hbv]; omega)
  have hKB' : KB.val = 256 := by rw [hKB, hbv]
  -- the ring of `w`'s SC
  have hRing : ∀ b, Aligned b → InRing (L.mem X (scA w)) (scSb Z (L.mem X (scA w))) b →
      L.mem X (scA w) ∈ Scs ∧ InSC (L.mem X (scA w)) (Z (L.mem X (scA w))) b ∧ b ∈ Ω := by
    intro b hb hr
    by_cases h0 : L.mem X (scA w) = 0#u64
    · exfalso
      rw [h0] at hr; unfold scSb at hr; rw [if_pos rfl] at hr
      have := hr.1; have := hr.2; simp at *; omega
    · rw [scSb_ne h0] at hr
      have hc := (hXX.2.2.bound w hw h0).1
      have hin : InSC (L.mem X (scA w)) (Z (L.mem X (scA w))) b := ⟨by have := hr.1; omega, hr.2⟩
      exact ⟨hc, hin, hO.scW _ hc b hb hin⟩
  refine ⟨fun o ho h8 h16 h56 => ?_, fun y hy K hK h8 h1 h2 hyw => ?_, fun c hc hne b hb hin => ?_⟩
  · refine hW.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (hd | (e | e | e) | hr | e)
    · exact dN o ho h8 hd
    · rw [stA_eq] at e; exact node_ne_field hN ho hw hw' (by simp) e
    · rw [eB] at e; exact node_ne_field hN ho hw hw' (by omega) e
    · exact nodeAt_ne hN ho (by rw [act_val]; omega) (by rw [act_val]; omega) e
    · obtain ⟨-, -, hΩ⟩ := hRing _ (nodeAt_aligned hN ho h8) hr
      exact out_ne_node (hq.omega _ hΩ) hcC hN ho rfl
    · rw [eR] at e
      exact nodeAt_ne hN ho (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]; omega) e
  · have hy' := hT y hy
    refine hW.mem_eq (field_aligned hy' hK h8) ?_
    rintro (hd | (e | e | e) | hr | e)
    · exact dT y hy K hK h8 h1 h2 (fun h => ⟨(hyw h).1, (hyw h).2.2⟩) hd
    · rw [stA_eq] at e
      exact field_ne hy' hw' hK (by simp) (fun h => by simp; exact (hyw h).1) e
    · rw [eB] at e
      exact field_ne hy' hw' hK (by omega) (fun h => by rw [hKB']; exact (hyw h).2.1) e
    · exact node_ne_field hN (by rw [act_val]; omega) hy hy' hK e.symm
    · obtain ⟨-, -, hΩ⟩ := hRing _ (field_aligned hy' hK h8) hr
      exact out_ne_field (hq.omega _ hΩ) hy hy' hK rfl
    · rw [eR] at e
      exact node_ne_field hN (by simp [layout.node.REPROGRAM]) hy hy' hK e.symm
  · have ho := hq.omega b (hO.scW c hc b hb hin)
    refine hW.mem_eq hb ?_
    rintro (hd | (e | e | e) | hr | e)
    · exact dS c hc b hb hin hd
    · subst e; rw [stA_eq] at ho; exact out_ne_field ho hw hw' (by simp) rfl
    · subst e; rw [eB] at ho; exact out_ne_field ho hw hw' (by omega) rfl
    · subst e; exact out_ne_node ho hcC hN (by rw [act_val]; omega) rfl
    · obtain ⟨hc', hin', -⟩ := hRing b hb hr
      have := hO.scDisj c hc _ hc' hne
      have := hin.1; have := hin.2; have := hin'.1; have := hin'.2
      omega
    · subst e; rw [eR] at ho; exact out_ne_node ho hcC hN (by simp [layout.node.REPROGRAM]) rfl

end keep

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
      ∃ w ∈ T, (L.actionW X2 = sched.ACTION_RESUME_CURRENT ∨ L.actionW X2 = w) ∧ WkKeep st T Scs Z X X2 w ∧
        Blocked (L.mem X (stA w)) ∧ L.mem X (affA w) = L.cpu s ∧ w ≠ L.curW X := by
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
    obtain ⟨dΩ, dN, dT⟩ := epfoot_nd (n := N) hq hEW he (fun y hy => hqr.mem y hy)
    exact ⟨p1, p2, p3, wi.2.1, w, hwT, act, wk_keep hTX' hwT wi (fun o ho h8 => dN o ho h8)
      (fun y hy K hK h8 h1 h2 _ => dT y hy K hK h8 h1 h2) (fun c hc b hb hin => dΩ b hb (hXX.1.scW c hc b hb hin)),
      hbl, haf, hcur⟩
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
    have hN : NodePlaced st T X (L.cpu X) := hq.nodes _ hq.cur
    have hcC := hq.cur
    have ht' := hT t htT
    obtain ⟨dΩ, dN, dT⟩ := epfoot_nd (n := ep) hq hEW hep (fun y hy => (hEW.1 ep hep).2.2.mem y hy)
    have hrO : r ≠ 0#u64 → OutsideObjs st T Cs X (rTcbA r) ∧ (rTcbA r).val = r.val ∧
        ∀ c ∈ Scs, r.val + 32 ≤ c.val ∨ c.val + 2 ^ Z c ≤ r.val := by
      intro hr0
      have hrp : r ∈ Rp := by
        have := (hXX.2.1.recv t htT hrecv (by rw [hr]; exact hr0)).1; rwa [hr] at this
      obtain ⟨-, rv, -, -⟩ := rp_facts hXX.1 hrp
      exact ⟨hq.omega _ (hSgX.sub _ (hXX.1.tcbW hrp)), rv, hXX.1.rpSc r hrp⟩
    refine ⟨p1, p2, p3, wi.2.1, t, htT, act, wk_keep hTX' htT wi ?_ ?_ ?_, hblk, haf, hcur⟩
    · intro o ho h8
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · unfold faultA at e; exact node_ne_field hN ho htT ht' (by simp) e
      · exact dN o ho h8 hf
      · exact out_ne_node (hrO hr0).1 hcC hN ho (congrArg UScalar.val e)
      · rw [stA_eq] at e; exact node_ne_field hN ho htT ht' (by simp) e
    · intro y hy K hK h8 h1 h2 hyw
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · unfold faultA at e; exact field_ne (hT y hy) ht' hK (by simp) (fun h => by simp; exact (hyw h).2) e
      · exact dT y hy K hK h8 h1 h2 hf
      · exact out_ne_field (hrO hr0).1 hy (hT y hy) hK (congrArg UScalar.val e)
      · rw [stA_eq] at e; exact field_ne (hT y hy) ht' hK (by simp) (fun h => by simp; exact (hyw h).1) e
    · intro c hc b hb hin
      have ho := hq.omega b (hXX.1.scW c hc b hb hin)
      rintro (e | hf | ⟨hr0, e⟩ | e)
      · subst e; unfold faultA at ho; exact out_ne_field ho htT ht' (by simp) rfl
      · exact dΩ b hb (hXX.1.scW c hc b hb hin) hf
      · obtain ⟨-, rv, rs⟩ := hrO hr0
        have ev := congrArg UScalar.val e
        rw [rv] at ev
        have := rs c hc; have := hin.1; have := hin.2
        omega
      · subst e; rw [stA_eq] at ho; exact out_ne_field ho htT ht' (by simp) rfl

end main

end Fl4Proofs.P2
