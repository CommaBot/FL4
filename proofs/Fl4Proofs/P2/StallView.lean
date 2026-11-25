/-
P2 (p2j4): **from one core's view to another's**.

* `PerCore st … c s`: P1's current-core clauses, for core `c`
  (`SchedQueuesInvX.cur/action/actOK/curT/idleT`, `BoundInv.act/idle/resume/
  idleNB/sact`, `ReplyInv0.idle`, `ScExtra0.cur`, `SCsOK.disj`).
* `BlkOK.view`: `BlkOK` at the view of core `d` and `PerCore c` give `BlkOK`
  at the view of core `c`.

No premise.
-/
import Fl4Proofs.P2.StallAt
import Fl4Proofs.P2.StallFull
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

/-- The view's `LawfulStore`, for instance resolution in this file. -/
local instance atCpuI {S : Type _} {st : machine.Store S} [L : LawfulStore st] (d : U64) : LawfulStore (atCpu st d) :=
  L.atCpu d

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- Core `c`'s `SCHED_ACTION`, `CUR_THREAD`, `IDLE_THREAD`, `CUR_SC` words. -/
def actAt (st : machine.Store S) [L : LawfulStore st] (c : U64) (s : S) : U64 := (L.atCpu c).actionW s
def curAt (st : machine.Store S) [L : LawfulStore st] (c : U64) (s : S) : U64 := (L.atCpu c).curW s
def idleAt (st : machine.Store S) [L : LawfulStore st] (c : U64) (s : S) : U64 := (L.atCpu c).idleW s
def cscAt (st : machine.Store S) [L : LawfulStore st] (c : U64) (s : S) : U64 := (L.atCpu c).cscW s

/-- **P1's current-core clauses for core `c`.** -/
structure PerCore (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (c : U64) (s : S) : Prop where
  mem : c ∈ Cs
  action : actAt st c s = 0#u64 ∨ actAt st c s = 1#u64 ∨ actAt st c s ∈ T
  run : actAt st c s ∈ T → Runnable (L.mem s (stA (actAt st c s)))
  rel : actAt st c s ∈ T → (L.mem s (inqA (actAt st c s)) &&& sched.Q_RELEASE) = 0#u64
  curT : curAt st c s ∈ T
  idleT : idleAt st c s ∈ T
  act : actAt st c s ∈ T → L.mem s (scA (actAt st c s)) ≠ 0#u64
  idle : L.mem s (scA (idleAt st c s)) ≠ 0#u64
  resume : actAt st c s = 0#u64 → L.mem s (scA (curAt st c s)) ≠ 0#u64
  idleNB : ¬ BlockedR (L.mem s (stA (idleAt st c s)))
  sact : ∀ t ∈ T, (actAt st c s = t ∨ idleAt st c s = t ∨ (actAt st c s = 0#u64 ∧ curAt st c s = t)) →
    L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac
  idleR : ∀ k ∈ Scs, L.mem s (scTcbA k) = idleAt st c s → L.mem s (scReplyA k) = 0#u64
  csc : cscAt st c s ∈ Scs
  disj : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ≠ cscAt st c s →
    ∀ b, InSC (L.mem s (scA t)) (Z (L.mem s (scA t))) b → Outside b (cscAt st c s) (Z (cscAt st c s))

theorem node_view {d c : U64} {s : S} {k : U64} (h : @NodePlaced S (atCpu st d) (L.atCpu d) T s k) :
    @NodePlaced S (atCpu st c) (L.atCpu c) T s k := by
  obtain ⟨a, b, e⟩ := h; exact ⟨a, b, e⟩

theorem rwf_view {d c : U64} {s : S} {k : U64} {z : Nat} (h : @RefillsWF S (atCpu st d) (L.atCpu d) s k z) :
    @RefillsWF S (atCpu st c) (L.atCpu c) s k z := by
  cases h; constructor <;> assumption

theorem coreTree_view {d c : U64} {s : S} {k : U64} {t : TRB.RBT} (h : @CoreTree S (atCpu st d) (L.atCpu d) T s k t) :
    @CoreTree S (atCpu st c) (L.atCpu c) T s k t := by
  cases h; constructor <;> assumption

theorem timerRB_view {d c : U64} {s : S} (h : @TimerRB S (atCpu st d) (L.atCpu d) T Cs s) :
    @TimerRB S (atCpu st c) (L.atCpu c) T Cs s :=
  ⟨fun k hk => (h.tree k hk).imp fun _ => coreTree_view,
    fun y hy hd => by
      obtain ⟨k, hk, t, ht, hm⟩ := h.armed y hy hd
      exact ⟨k, hk, t, coreTree_view ht, hm⟩, h.idle⟩

theorem timerOK_view {d c : U64} {s : S} (h : @TimerOK S (atCpu st d) (L.atCpu d) T Cs s) :
    @TimerOK S (atCpu st c) (L.atCpu c) T Cs s :=
  ⟨fun k hk => node_view (h.npl k hk), h.lt, h.rt, h.pt, h.root, h.min, h.core, h.dn, h.dp, h.dh⟩

theorem objsOK_view {d c : U64} {s : S} (h : @ObjsOK S (atCpu st d) (L.atCpu d) Ω Sg Rp Scs Nt Z s) :
    @ObjsOK S (atCpu st c) (L.atCpu c) Ω Sg Rp Scs Nt Z s := by
  cases h; constructor <;> assumption

theorem bndS_view {d c : U64} {s : S} (h : @BndS S (atCpu st d) (L.atCpu d) T Scs Nt s) :
    @BndS S (atCpu st c) (L.atCpu c) T Scs Nt s := by
  cases h; constructor <;> assumption

theorem sca_view {d c : U64} {s : S} {k : U64} {z : Nat} (h : @SCA S (atCpu st d) (L.atCpu d) s Sg k z) :
    @SCA S (atCpu st c) (L.atCpu c) s Sg k z := ⟨fun hm => rwf_view (h.1 hm), h.2.1, h.2.2⟩

theorem reply_view {d c : U64} {s : S} (h : @ReplyInv S (atCpu st d) (L.atCpu d) T Rp Scs s)
    (hi : ∀ k ∈ Scs, L.mem s (scTcbA k) = idleAt st c s → L.mem s (scReplyA k) = 0#u64) :
    @ReplyInv S (atCpu st c) (L.atCpu c) T Rp Scs s := by
  obtain ⟨h0, hh⟩ := h
  refine @ReplyInv.mk S (atCpu st c) (L.atCpu c) T Rp Scs s ?_ hh
  cases h0
  constructor <;> first | exact hi | assumption

theorem scExtra_view {d c : U64} {s : S} (h : @ScExtra S (atCpu st d) (L.atCpu d) T Cs Scs Nt s)
    (hcs : cscAt st c s ∈ Scs) : @ScExtra S (atCpu st c) (L.atCpu c) T Cs Scs Nt s := by
  obtain ⟨h0, hh⟩ := h
  refine @ScExtra.mk S (atCpu st c) (L.atCpu c) T Cs Scs Nt s ?_ hh
  exact ⟨h0.bound, hcs, h0.core, h0.bnd, h0.nsc, timerOK_view h0.tm, h0.ntb, timerRB_view h0.rb, h0.scn, h0.yt,
    bndS_view h0.bs⟩

theorem scsOK_view {d c : U64} {s : S} (h : @SCsOK S (atCpu st d) (L.atCpu d) T Ω Sg Scs Z Ac s)
    (hd : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ≠ cscAt st c s →
      ∀ b, InSC (L.mem s (scA t)) (Z (L.mem s (scA t))) b → Outside b (cscAt st c s) (Z (cscAt st c s))) :
    @SCsOK S (atCpu st c) (L.atCpu c) T Ω Sg Scs Z Ac s :=
  ⟨h.sub, h.ks, h.ksΩ, hd, fun k hk => sca_view (h.all k hk), h.act, h.spor, h.spSg, h.rep, h.repSg, h.scKs⟩

theorem sgOK_view {d c : U64} {s : S} (h : @SgOK S (atCpu st d) (L.atCpu d) Ω Sg s) :
    @SgOK S (atCpu st c) (L.atCpu c) Ω Sg s := ⟨h.sub, h.ks, h.ksΩ⟩

/-- The released flag names the release queue, at any view. -/
theorem notR_of_flag {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {X : Set U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) {y : U64} (hy : y ∈ T)
    (h0 : (L.mem s (inqA y) &&& sched.Q_RELEASE) = 0#u64) : ∀ k ∈ Cs, y ∉ R k := fun k hk hm => by
  have e := h.inR k hk y hm
  exact (h.released y hy).2 (by rw [e]; exact hm) h0

theorem ready_view {d c : U64} {s : S} {k : U64} {Q : U64 → List U64}
    (h : @ReadyQueues S (atCpu st d) (L.atCpu d) T s k Q) : @ReadyQueues S (atCpu st c) (L.atCpu c) T s k Q := by
  obtain ⟨a, b⟩ := h
  refine ⟨?_, ?_⟩
  · first | exact a | (cases a; constructor <;> assumption)
  · first | exact b | (cases b; constructor <;> assumption)

theorem eps_view {d c : U64} {s : S} {X : Set U64} (h : @EpsOK S (atCpu st d) (L.atCpu d) T Cs Ω H X s) :
    @EpsOK S (atCpu st c) (L.atCpu c) T Cs Ω H X s := by
  obtain ⟨E, EQ, w⟩ := h
  refine ⟨E, EQ, ?_⟩
  first | exact w | (cases w; constructor <;> assumption)

theorem queues_view {d c : U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {X : Set U64}
    (h : @SchedQueuesInvX S (atCpu st d) (L.atCpu d) T Cs Ω H X s Q R) (p : PerCore st T Cs Scs Z Ac c s) :
    @SchedQueuesInvX S (atCpu st c) (L.atCpu c) T Cs Ω H X s Q R :=
  ⟨h.tcbs, fun k hk => node_view (h.nodes k hk), p.mem, h.aff, h.prio, fun k hk => ready_view (h.ready k hk), h.release, h.inQ, h.inR, h.queued,
    h.released, h.excl, p.action, h.runQ, h.runR,
    fun hT => ⟨p.run hT, notR_of_flag (st := atCpu st d) (L := L.atCpu d) h hT (p.rel hT)⟩,
    eps_view h.eps, p.curT, p.idleT, h.ksOut, h.omega⟩

theorem bound_view {d c : U64} {s : S} (h : @BoundInv S (atCpu st d) (L.atCpu d) T Ac s)
    (p : PerCore st T Cs Scs Z Ac c s) : @BoundInv S (atCpu st c) (L.atCpu c) T Ac s :=
  ⟨h.q, h.r, p.act, p.idle, p.resume, p.idleNB, fun t ht hs hb => by
    rcases hs with e | e | e | e | e | e
    · exact h.sact t ht (Or.inl e) hb
    · exact h.sact t ht (Or.inr (Or.inl e)) hb
    · exact p.sact t ht (Or.inl e) hb
    · exact p.sact t ht (Or.inr (Or.inl e)) hb
    · exact p.sact t ht (Or.inr (Or.inr e)) hb
    · exact h.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))) hb⟩

/-- **`BlkOK` at core `d`'s view and core `c`'s clauses give `BlkOK` at core
`c`'s view.** -/
theorem BlkOK.view {d c : U64} {s : S} (h : @BlkOK S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (p : PerCore st T Cs Scs Z Ac c s) : @BlkOK S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, q⟩, hB, ⟨hO, hR, hE⟩, hS, hSg⟩ := h
  exact ⟨⟨Q, R, queues_view q p⟩, bound_view hB p, ⟨objsOK_view hO, reply_view hR p.idleR, scExtra_view hE p.csc⟩,
    scsOK_view hS p.disj, sgOK_view hSg⟩

/-- Conversely, `BlkOK` at core `c`'s view gives its clauses. -/
theorem PerCore.of {c : U64} {s : S} (h : @BlkOK S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    PerCore st T Cs Scs Z Ac c s := by
  obtain ⟨⟨Q, R, q⟩, hB, ⟨hO, hR, hE⟩, hS, hSg⟩ := h
  refine ⟨q.cur, q.action, fun hT => (q.actOK hT).1, fun hT => ?_, q.curT, q.idleT, hB.act, hB.idle, hB.resume,
    hB.idleNB, fun t ht ho hb => ?_, hR.idle, hE.cur, hS.disj⟩
  · by_contra hn
    exact (q.actOK hT).2 _ (q.aff _ hT) ((q.released _ hT).1 hn)
  · refine hB.sact t ht ?_ hb
    rcases ho with e | e | e
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inr (Or.inr (Or.inl e)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl e))))

end

end Fl4Proofs.P2.Stall
