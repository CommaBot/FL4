/-
P2 (p2j4): **a remote stall of core `d` keeps P1's invariants at every core's
view.**

* `CoreInv c`: `EntryInv`'s core-specific clauses for core `c` (`PerCore` and
  the current-SC clauses) and `IdleSc c`; `CoreInv.entry`: with `BlkOK` at
  any view they give `EntryInv` at core `c`'s view.
* `stallAt.views`: from `EntryInv` at the view of `d` and the other cores'
  `CoreInv`, `stallAt d` gives `EntryInv` at the view of `d`, and keeps every
  other core's `CoreInv`, hence `EntryInv` at every view; a core's
  `SCHED_ACTION` is kept, or `RESUME` for `d`.

Premises of `stallAt.views`:
* the transfer at the view of `d` (`hRSK`; `RS`, `XG`, `UserOK` at the
  stall's start, as in P1), `XferOKRS` [J] (`P2/FootN5.lean`), `XferFootOKC`
  [J] (`P2/XferN.lean`), `TmoCap` [P];
* `hown` [J]: `d`'s current thread is none of the other cores' idle,
  current or action threads (`OtherK`); from `OwnJ.curAff` (a current
  thread's `AFFINITY` is its core) and the idle threads' placement;
* `hactK` [J]: `d`'s action, if a thread, is not in `OtherK` (an action
  thread is on `d`'s ready queues, affinity `d`);
* `hcurNB` [J]: another core's current thread is not blocked on an
  endpoint or notification (it runs: only its own core blocks it);
* `hnq` [J]: `d`'s current thread, unless idle, is in no ready queue (seL4
  `ct_not_in_q`).

**(p2j5)** The protected set is now `OtherK` (was: the other cores' idle
threads), and the exclusion layer (`FootN`'s `PrW`) also protects their
`IN_QUEUES` and every thread's `AFFINITY`. So the old premise `hact` (another
core's action is no thread) is gone: an action thread's state, queue flags
and SC are kept (`CoreInv.keep`). The conclusion `OKeep` now also keeps the
`IN_QUEUES` of `OtherK` (so another core's `hnq`, `ct_not_in_q`, survives
the stall: `OKeep.nq`) and every thread's `AFFINITY` (`OwnJ`'s (1)/(2) for
the other cores).
-/
import Fl4Proofs.P2.StallView
import Fl4Proofs.P1.QueueIpcFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {P3Ok : S → Prop} {A : Type _} {ar : machine.Arch A}

/-- Core `c`'s clauses of `EntryInv`, and `IdleSc`. -/
structure CoreInv (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (c : U64) (s : S) : Prop where
  per : PerCore st T Cs Scs Z Ac c s
  ac : cscAt st c s ∈ Ac
  ne : actAt st c s ≠ curAt st c s
  csc : L.mem s (scA (curAt st c s)) ≠ 0#u64 → cscAt st c s = L.mem s (scA (curAt st c s))
  isc : IdleSc st c s

/-- `EntryInv` at core `c`'s view, from `BlkOK` at any view. -/
theorem CoreInv.entry {d c : U64} {s : S} (p : CoreInv st T Cs Scs Z Ac c s)
    (h : @BlkOK S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    @EntryInv S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  have h' := BlkOK.view h p.per
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.1.2.2.tm, p.ac, p.ne, p.csc⟩

/-- `EntryInv` at core `c`'s view gives `CoreInv c`. -/
theorem CoreInv.of {c : U64} {s : S} (h : @EntryInv S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st c s) : CoreInv st T Cs Scs Z Ac c s :=
  ⟨PerCore.of (@EntryInv.blkOK S (atCpu st c) (L.atCpu c) _ _ _ _ _ _ _ _ _ _ _ h), h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, hI⟩

/-- `StKeep` without the (view-dependent) current core. -/
structure OKeep (st : machine.Store S) [L : LawfulStore st] (T Cs Scs Kp : Set U64) (d : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  nd : ∀ c ∈ Cs, ∀ o : U64, (o.val = 8 ∨ o.val = 32 ∨ (c ≠ d ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) →
    L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  kp : ∀ y ∈ Kp, L.mem s' (stA y) = L.mem s (stA y)
  iq : ∀ y ∈ Kp, L.mem s' (inqA y) = L.mem s (inqA y)
  af : ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y)
  sc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y)
  lk : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) ∧ L.mem s' (scTcbA c) = L.mem s (scTcbA c)

theorem OKeep.idle {Kp : Set U64} {d c : U64} {s s' : S} (k : OKeep st T Cs Scs Kp d s s') (hc : c ∈ Cs)
    (hiT : L.mem s (L.nodeAt s c layout.node.IDLE_THREAD) ∈ T) (h : IdleSc st c s) : IdleSc st c s' := by
  unfold IdleSc at h ⊢
  rw [nodeAt_of_ksb k.ksb, nodeAt_of_ksb k.ksb, k.nd c hc _ (Or.inr (Or.inl (by simp [layout.node.IDLE_SC]))),
    k.nd c hc _ (Or.inl idle8), k.sc _ hiT]
  exact h

/-- The node words of a core other than `d`. -/
theorem keep_words {Kp : Set U64} {d c : U64} {s s' : S} (k : OKeep st T Cs Scs Kp d s s') (hc : c ∈ Cs) (hne : c ≠ d) :
    actAt st c s' = actAt st c s ∧ curAt st c s' = curAt st c s ∧ idleAt st c s' = idleAt st c s ∧
      cscAt st c s' = cscAt st c s := by
  have w : ∀ o : U64, (o.val = 8 ∨ o.val = 32 ∨ (c ≠ d ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) →
      L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := fun o ho => by
    rw [nodeAt_of_ksb k.ksb]; exact k.nd c hc o ho
  exact ⟨w layout.node.SCHED_ACTION (Or.inr (Or.inr ⟨hne, Or.inr (Or.inl act_val)⟩)),
    w layout.node.CUR_THREAD (Or.inr (Or.inr ⟨hne, Or.inl curth0⟩)), w layout.node.IDLE_THREAD (Or.inl idle8),
    w layout.node.CUR_SC (Or.inr (Or.inr ⟨hne, Or.inr (Or.inr (by simp [layout.node.CUR_SC]))⟩))⟩

/-- **A stall of `d` keeps the other cores' clauses.** -/
theorem CoreInv.keep {Kp : Set U64} {d c : U64} {s s' : S} (p : CoreInv st T Cs Scs Z Ac c s)
    (k : OKeep st T Cs Scs Kp d s s') (hc : c ∈ Cs) (hne : c ≠ d) (hKp : idleAt st c s ∈ Kp)
    (ha : actAt st c s ∈ T → actAt st c s ∈ Kp) :
    CoreInv st T Cs Scs Z Ac c s' := by
  obtain ⟨ea, ec, ei, es⟩ := keep_words k hc hne
  obtain ⟨p, ac, ne, csc, isc⟩ := p
  have ksc := k.sc
  refine ⟨⟨hc, by rw [ea]; exact p.action, fun h => by
      rw [ea] at h ⊢; rw [k.kp _ (ha h)]; exact p.run h,
    fun h => by rw [ea] at h ⊢; rw [k.iq _ (ha h)]; exact p.rel h,
    by rw [ec]; exact p.curT, by rw [ei]; exact p.idleT,
    fun h => by rw [ea] at h ⊢; rw [ksc _ h]; exact p.act h,
    by rw [ei, ksc _ p.idleT]; exact p.idle, fun h => by rw [ec, ksc _ p.curT]; exact p.resume (ea ▸ h),
    by rw [ei, k.kp _ hKp]; exact p.idleNB, fun t ht ho hb => ?_, fun j hj hb => ?_, by rw [es]; exact p.csc,
    fun t ht hb hn => ?_⟩, by rw [es]; exact ac, by rw [ea, ec]; exact ne, fun hb => ?_,
    k.idle hc p.idleT isc⟩
  · rw [ea, ei, ec] at ho
    rw [ksc t ht] at hb ⊢
    exact p.sact t ht ho hb
  · rw [(k.lk j hj).2, ei] at hb
    rw [(k.lk j hj).1]; exact p.idleR j hj hb
  · rw [ksc t ht] at hb hn ⊢
    rw [es] at hn ⊢
    exact p.disj t ht hb hn
  · rw [ec, ksc _ p.curT] at hb ⊢
    rw [es]; exact csc hb

/-- The other cores' idle, current and action threads: the threads a stall
of `d` must not touch. -/
def OtherK (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (d : U64) (s : S) : Set U64 :=
  {y | ∃ c ∈ Cs, c ≠ d ∧ (y = idleAt st c s ∨ y = curAt st c s ∨ (y = actAt st c s ∧ y ∈ T))}

/-- Another core's `ct_not_in_q` survives the stall. -/
theorem OKeep.nq {Kp : Set U64} {d c : U64} {s s' : S} (k : OKeep st T Cs Scs Kp d s s') (hc : c ∈ Cs)
    (hne : c ≠ d) (hK : curAt st c s ∈ Kp)
    (h : (L.mem s (inqA (curAt st c s)) &&& sched.Q_QUEUED) = 0#u64) :
    (L.mem s' (inqA (curAt st c s')) &&& sched.Q_QUEUED) = 0#u64 := by
  rw [(keep_words k hc hne).2.1, k.iq _ hK]; exact h

/-- **A remote stall keeps the invariants at every core's view.**
Named premises: `hxf` [J] (`XferOKRS`, `P2/FootN5.lean`), `hxw` [J] (`XferFootOKC`,
`P2/XferN.lean`). -/
theorem stallAt.views (hA : P0.ArchTotal ar) (d : U64)
    {RS : S → S → Prop}
    (hxf : @XferOKRS S (atCpu st d) (L.atCpu d) A ar T Cs Ω H Sg Rp Scs Nt Z U RS
      (@XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok))
    (hxw : @XferFootOKC S (atCpu st d) (L.atCpu d) A ar T Cs Ω H Sg Rp Scs Nt Z U RS
      (@XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → @WritesIn S (atCpu st d) (L.atCpu d) s1 s2
      (@KW S (atCpu st d) (L.atCpu d) T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (s : S) (a : A) (h : @EntryInv S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st d s) (hG : @XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok s)
    (hRS0 : RS s s) (hU : @UserOK S (atCpu st d) (L.atCpu d) T Cs Ω H U s)
    (hcap : @TmoCap S (atCpu st d) (L.atCpu d) Scs Z H Rp Nt s)
    (hC : ∀ c ∈ Cs, c ≠ d → CoreInv st T Cs Scs Z Ac c s)
    (hown : curAt st d s ∉ OtherK st T Cs d s)
    (hactK : actAt st d s ∈ T → actAt st d s ∉ OtherK st T Cs d s)
    (hcurNB : ∀ c ∈ Cs, c ≠ d → ¬ Blocked (L.mem s (stA (curAt st c s))))
    (hnq : curAt st d s ≠ idleAt st d s → (L.mem s (inqA (curAt st d s)) &&& sched.Q_QUEUED) = 0#u64) :
    stallAt st ar d s a ⦃ s' _ =>
      (∀ c ∈ Cs, @EntryInv S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IdleSc st c s') ∧
      OKeep st T Cs Scs (OtherK st T Cs d s) d s s' ∧ curAt st d s' = idleAt st d s' ∧
      (actAt st d s' = actAt st d s ∨ actAt st d s' = 0#u64) ∧ (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ⦄ := by
  have hKT : ∀ y ∈ OtherK st T Cs d s, y ∈ T := by
    rintro y ⟨c, hc, hne, rfl | rfl | ⟨rfl, hy⟩⟩
    · exact (hC c hc hne).per.idleT
    · exact (hC c hc hne).per.curT
    · exact hy
  have hKB : ∀ y ∈ OtherK st T Cs d s, ¬ Blocked (L.mem s (stA y)) := by
    rintro y ⟨c, hc, hne, rfl | rfl | ⟨rfl, hy⟩⟩ hb
    · exact (hC c hc hne).per.idleNB (Or.inl hb)
    · exact hcurNB c hc hne hb
    · exact blocked_not_runnable hb ((hC c hc hne).per.run hy)
  unfold stallAt
  refine WP.spec_mono (@stallSeq.entryN S (atCpu st d) (L.atCpu d) T Ω H Cs Sg Rp Scs Nt Z Ac U
    (OtherK st T Cs d s) P3Ok A ar hA RS hxf hxw hRSK hKT s a h hI hG hown hactK hKB hRS0 hU hnq hcap) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨e', hI', k, hcur, hac⟩ := hh
  have k' : OKeep st T Cs Scs (OtherK st T Cs d s) d s s' := ⟨k.ksb, k.nd, k.kp, k.iq, k.af, k.sc, k.lk⟩
  refine ⟨fun c hc => ?_, k', hcur, hac, fun c hc hne => (keep_words k' hc hne).1⟩
  by_cases e : c = d
  · subst e; exact ⟨e', hI'⟩
  · have p := (hC c hc e).keep k' hc e ⟨c, hc, e, Or.inl rfl⟩ fun h => ⟨c, hc, e, Or.inr (Or.inr ⟨rfl, h⟩)⟩
    exact ⟨p.entry (@EntryInv.blkOK S (atCpu st d) (L.atCpu d) _ _ _ _ _ _ _ _ _ _ _ e'), p.isc⟩

end

end Fl4Proofs.P2.Stall
