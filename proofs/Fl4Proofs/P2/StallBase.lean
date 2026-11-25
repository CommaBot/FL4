/-
P2 (p2j5): **the executing core's base store and the per-core views**.

`StallView` moves P1's invariants between two views `atCpu st d`,
`atCpu st c`. The issuing core runs on the base store `st` itself, whose
`cur_cpu` returns `L.cpu s` (constant along an entry: `WritesIn.2.1`). Here:

* `BlkOK.viewB`: `BlkOK` at `st` and core `c`'s clauses give it at core
  `c`'s view;
* `BlkOK.viewR`: `BlkOK` at any view and the executing core's clauses give it
  at `st`;
* `PerCore.ofB`: `BlkOK` at `st` gives the executing core's clauses;
* `EntryInv.toView` / `EntryInv.ofView`: `EntryInv` at `st` and at the view of
  the executing core are the same.

No premise. (The `*_viewB` / `*_viewR` lemmas are `StallView`'s `*_view`
with the base store as source / target.)
-/
import Fl4Proofs.P2.StallView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-! ## From the base store -/

theorem node_viewB {c : U64} {s : S} {k : U64} (h : @NodePlaced S st L T s k) :
    @NodePlaced S (atCpu st c) (L.atCpu c) T s k := by
  obtain ⟨a, b, e⟩ := h; exact ⟨a, b, e⟩

theorem rwf_viewB {c : U64} {s : S} {k : U64} {z : Nat} (h : @RefillsWF S st L s k z) :
    @RefillsWF S (atCpu st c) (L.atCpu c) s k z := by
  cases h; constructor <;> assumption

theorem coreTree_viewB {c : U64} {s : S} {k : U64} {t : TRB.RBT} (h : @CoreTree S st L T s k t) :
    @CoreTree S (atCpu st c) (L.atCpu c) T s k t := by
  cases h; constructor <;> assumption

theorem timerRB_viewB {c : U64} {s : S} (h : @TimerRB S st L T Cs s) :
    @TimerRB S (atCpu st c) (L.atCpu c) T Cs s :=
  ⟨fun k hk => (h.tree k hk).imp fun _ => coreTree_viewB,
    fun y hy hd => by
      obtain ⟨k, hk, t, ht, hm⟩ := h.armed y hy hd
      exact ⟨k, hk, t, coreTree_viewB ht, hm⟩, h.idle⟩

theorem timerOK_viewB {c : U64} {s : S} (h : @TimerOK S st L T Cs s) :
    @TimerOK S (atCpu st c) (L.atCpu c) T Cs s :=
  ⟨fun k hk => node_viewB (h.npl k hk), h.lt, h.rt, h.pt, h.root, h.min, h.core, h.dn, h.dp, h.dh⟩

theorem objsOK_viewB {c : U64} {s : S} (h : @ObjsOK S st L Ω Sg Rp Scs Nt Z s) :
    @ObjsOK S (atCpu st c) (L.atCpu c) Ω Sg Rp Scs Nt Z s := by
  cases h; constructor <;> assumption

theorem bndS_viewB {c : U64} {s : S} (h : @BndS S st L T Scs Nt s) :
    @BndS S (atCpu st c) (L.atCpu c) T Scs Nt s := by
  cases h; constructor <;> assumption

theorem sca_viewB {c : U64} {s : S} {k : U64} {z : Nat} (h : @SCA S st L s Sg k z) :
    @SCA S (atCpu st c) (L.atCpu c) s Sg k z := ⟨fun hm => rwf_viewB (h.1 hm), h.2.1, h.2.2⟩

theorem reply_viewB {c : U64} {s : S} (h : @ReplyInv S st L T Rp Scs s)
    (hi : ∀ k ∈ Scs, L.mem s (scTcbA k) = idleAt st c s → L.mem s (scReplyA k) = 0#u64) :
    @ReplyInv S (atCpu st c) (L.atCpu c) T Rp Scs s := by
  obtain ⟨h0, hh⟩ := h
  refine @ReplyInv.mk S (atCpu st c) (L.atCpu c) T Rp Scs s ?_ hh
  cases h0
  constructor <;> first | exact hi | assumption

theorem scExtra_viewB {c : U64} {s : S} (h : @ScExtra S st L T Cs Scs Nt s)
    (hcs : cscAt st c s ∈ Scs) : @ScExtra S (atCpu st c) (L.atCpu c) T Cs Scs Nt s := by
  obtain ⟨h0, hh, ha⟩ := h
  refine @ScExtra.mk S (atCpu st c) (L.atCpu c) T Cs Scs Nt s ?_ hh ha
  exact ⟨h0.bound, hcs, h0.core, h0.bnd, h0.nsc, timerOK_viewB h0.tm, h0.ntb, timerRB_viewB h0.rb, h0.scn, h0.yt,
    bndS_viewB h0.bs⟩

theorem scsOK_viewB {c : U64} {s : S} (h : @SCsOK S st L T Ω Sg Scs Z Ac s)
    (hd : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ≠ cscAt st c s →
      ∀ b, InSC (L.mem s (scA t)) (Z (L.mem s (scA t))) b → Outside b (cscAt st c s) (Z (cscAt st c s))) :
    @SCsOK S (atCpu st c) (L.atCpu c) T Ω Sg Scs Z Ac s :=
  ⟨h.sub, h.ks, h.ksΩ, hd, fun k hk => sca_viewB (h.all k hk), h.act, h.spor, h.spSg, h.rep, h.repSg⟩

theorem sgOK_viewB {c : U64} {s : S} (h : @SgOK S st L Ω Sg s) :
    @SgOK S (atCpu st c) (L.atCpu c) Ω Sg s := ⟨h.sub, h.ks, h.ksΩ⟩

theorem ready_viewB {c : U64} {s : S} {k : U64} {Q : U64 → List U64}
    (h : @ReadyQueues S st L T s k Q) : @ReadyQueues S (atCpu st c) (L.atCpu c) T s k Q := by
  obtain ⟨a, b⟩ := h
  refine ⟨?_, ?_⟩
  · first | exact a | (cases a; constructor <;> assumption)
  · first | exact b | (cases b; constructor <;> assumption)

theorem eps_viewB {c : U64} {s : S} {X : Set U64} (h : @EpsOK S st L T Cs Ω H X s) :
    @EpsOK S (atCpu st c) (L.atCpu c) T Cs Ω H X s := by
  obtain ⟨E, EQ, w⟩ := h
  refine ⟨E, EQ, ?_⟩
  first | exact w | (cases w; constructor <;> assumption)

theorem queues_viewB {c : U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {X : Set U64}
    (h : @SchedQueuesInvX S st L T Cs Ω H X s Q R) (p : PerCore st T Cs Scs Z Ac c s) :
    @SchedQueuesInvX S (atCpu st c) (L.atCpu c) T Cs Ω H X s Q R :=
  ⟨h.tcbs, fun k hk => node_viewB (h.nodes k hk), p.mem, h.aff, h.prio, fun k hk => ready_viewB (h.ready k hk), h.release, h.inQ, h.inR, h.queued,
    h.released, h.excl, p.action, h.runQ, h.runR,
    fun hT => ⟨p.run hT, notR_of_flag (st := st) (L := L) h hT (p.rel hT)⟩,
    eps_viewB h.eps, p.curT, p.idleT, h.ksOut, h.omega⟩

theorem bound_viewB {c : U64} {s : S} (h : @BoundInv S st L T Ac s)
    (p : PerCore st T Cs Scs Z Ac c s) : @BoundInv S (atCpu st c) (L.atCpu c) T Ac s :=
  ⟨h.q, h.r, p.act, p.idle, p.resume, p.idleNB, fun t ht hs hb => by
    rcases hs with e | e | e | e | e | e
    · exact h.sact t ht (Or.inl e) hb
    · exact h.sact t ht (Or.inr (Or.inl e)) hb
    · exact p.sact t ht (Or.inl e) hb
    · exact p.sact t ht (Or.inr (Or.inl e)) hb
    · exact p.sact t ht (Or.inr (Or.inr e)) hb
    · exact h.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))) hb⟩

/-- **`BlkOK` and core `c`'s clauses give `BlkOK` at core `c`'s view.** -/
theorem BlkOK.viewB {c : U64} {s : S} (h : @BlkOK S st L T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (p : PerCore st T Cs Scs Z Ac c s) : @BlkOK S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, q⟩, hB, ⟨hO, hR, hE⟩, hS, hSg⟩ := h
  exact ⟨⟨Q, R, queues_viewB q p⟩, bound_viewB hB p, ⟨objsOK_viewB hO, reply_viewB hR p.idleR, scExtra_viewB hE p.csc⟩,
    scsOK_viewB hS p.disj, sgOK_viewB hSg⟩

/-- `BlkOK` at the base store gives the executing core's clauses. -/
theorem PerCore.ofB {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    PerCore st T Cs Scs Z Ac (L.cpu s) s := by
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

/-! ## To the base store -/

theorem node_viewR {d : U64} {s : S} {k : U64} (h : @NodePlaced S (atCpu st d) (L.atCpu d) T s k) :
    @NodePlaced S st L T s k := by
  obtain ⟨a, b, e⟩ := h; exact ⟨a, b, e⟩

theorem rwf_viewR {d : U64} {s : S} {k : U64} {z : Nat} (h : @RefillsWF S (atCpu st d) (L.atCpu d) s k z) :
    @RefillsWF S st L s k z := by
  cases h; constructor <;> assumption

theorem coreTree_viewR {d : U64} {s : S} {k : U64} {t : TRB.RBT} (h : @CoreTree S (atCpu st d) (L.atCpu d) T s k t) :
    @CoreTree S st L T s k t := by
  cases h; constructor <;> assumption

theorem timerRB_viewR {d : U64} {s : S} (h : @TimerRB S (atCpu st d) (L.atCpu d) T Cs s) :
    @TimerRB S st L T Cs s :=
  ⟨fun k hk => (h.tree k hk).imp fun _ => coreTree_viewR,
    fun y hy hd => by
      obtain ⟨k, hk, t, ht, hm⟩ := h.armed y hy hd
      exact ⟨k, hk, t, coreTree_viewR ht, hm⟩, h.idle⟩

theorem timerOK_viewR {d : U64} {s : S} (h : @TimerOK S (atCpu st d) (L.atCpu d) T Cs s) :
    @TimerOK S st L T Cs s :=
  ⟨fun k hk => node_viewR (h.npl k hk), h.lt, h.rt, h.pt, h.root, h.min, h.core, h.dn, h.dp, h.dh⟩

theorem objsOK_viewR {d : U64} {s : S} (h : @ObjsOK S (atCpu st d) (L.atCpu d) Ω Sg Rp Scs Nt Z s) :
    @ObjsOK S st L Ω Sg Rp Scs Nt Z s := by
  cases h; constructor <;> assumption

theorem bndS_viewR {d : U64} {s : S} (h : @BndS S (atCpu st d) (L.atCpu d) T Scs Nt s) :
    @BndS S st L T Scs Nt s := by
  cases h; constructor <;> assumption

theorem sca_viewR {d : U64} {s : S} {k : U64} {z : Nat} (h : @SCA S (atCpu st d) (L.atCpu d) s Sg k z) :
    @SCA S st L s Sg k z := ⟨fun hm => rwf_viewR (h.1 hm), h.2.1, h.2.2⟩

theorem reply_viewR {d : U64} {s : S} (h : @ReplyInv S (atCpu st d) (L.atCpu d) T Rp Scs s)
    (hi : ∀ k ∈ Scs, L.mem s (scTcbA k) = idleAt st (L.cpu s) s → L.mem s (scReplyA k) = 0#u64) :
    @ReplyInv S st L T Rp Scs s := by
  obtain ⟨h0, hh⟩ := h
  refine @ReplyInv.mk S st L T Rp Scs s ?_ hh
  cases h0
  constructor <;> first | exact hi | assumption

theorem scExtra_viewR {d : U64} {s : S} (h : @ScExtra S (atCpu st d) (L.atCpu d) T Cs Scs Nt s)
    (hcs : cscAt st (L.cpu s) s ∈ Scs) : @ScExtra S st L T Cs Scs Nt s := by
  obtain ⟨h0, hh, ha⟩ := h
  refine @ScExtra.mk S st L T Cs Scs Nt s ?_ hh ha
  exact ⟨h0.bound, hcs, h0.core, h0.bnd, h0.nsc, timerOK_viewR h0.tm, h0.ntb, timerRB_viewR h0.rb, h0.scn, h0.yt,
    bndS_viewR h0.bs⟩

theorem scsOK_viewR {d : U64} {s : S} (h : @SCsOK S (atCpu st d) (L.atCpu d) T Ω Sg Scs Z Ac s)
    (hd : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ≠ cscAt st (L.cpu s) s →
      ∀ b, InSC (L.mem s (scA t)) (Z (L.mem s (scA t))) b → Outside b (cscAt st (L.cpu s) s) (Z (cscAt st (L.cpu s) s))) :
    @SCsOK S st L T Ω Sg Scs Z Ac s :=
  ⟨h.sub, h.ks, h.ksΩ, hd, fun k hk => sca_viewR (h.all k hk), h.act, h.spor, h.spSg, h.rep, h.repSg⟩

theorem sgOK_viewR {d : U64} {s : S} (h : @SgOK S (atCpu st d) (L.atCpu d) Ω Sg s) :
    @SgOK S st L Ω Sg s := ⟨h.sub, h.ks, h.ksΩ⟩

theorem ready_viewR {d : U64} {s : S} {k : U64} {Q : U64 → List U64}
    (h : @ReadyQueues S (atCpu st d) (L.atCpu d) T s k Q) : @ReadyQueues S st L T s k Q := by
  obtain ⟨a, b⟩ := h
  refine ⟨?_, ?_⟩
  · first | exact a | (cases a; constructor <;> assumption)
  · first | exact b | (cases b; constructor <;> assumption)

theorem eps_viewR {d : U64} {s : S} {X : Set U64} (h : @EpsOK S (atCpu st d) (L.atCpu d) T Cs Ω H X s) :
    @EpsOK S st L T Cs Ω H X s := by
  obtain ⟨E, EQ, w⟩ := h
  refine ⟨E, EQ, ?_⟩
  first | exact w | (cases w; constructor <;> assumption)

theorem queues_viewR {d : U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {X : Set U64}
    (h : @SchedQueuesInvX S (atCpu st d) (L.atCpu d) T Cs Ω H X s Q R) (p : PerCore st T Cs Scs Z Ac (L.cpu s) s) :
    @SchedQueuesInvX S st L T Cs Ω H X s Q R :=
  ⟨h.tcbs, fun k hk => node_viewR (h.nodes k hk), p.mem, h.aff, h.prio, fun k hk => ready_viewR (h.ready k hk), h.release, h.inQ, h.inR, h.queued,
    h.released, h.excl, p.action, h.runQ, h.runR,
    fun hT => ⟨p.run hT, notR_of_flag (st := atCpu st d) (L := L.atCpu d) h hT (p.rel hT)⟩,
    eps_viewR h.eps, p.curT, p.idleT, h.ksOut, h.omega⟩

theorem bound_viewR {d : U64} {s : S} (h : @BoundInv S (atCpu st d) (L.atCpu d) T Ac s)
    (p : PerCore st T Cs Scs Z Ac (L.cpu s) s) : @BoundInv S st L T Ac s :=
  ⟨h.q, h.r, p.act, p.idle, p.resume, p.idleNB, fun t ht hs hb => by
    rcases hs with e | e | e | e | e | e
    · exact h.sact t ht (Or.inl e) hb
    · exact h.sact t ht (Or.inr (Or.inl e)) hb
    · exact p.sact t ht (Or.inl e) hb
    · exact p.sact t ht (Or.inr (Or.inl e)) hb
    · exact p.sact t ht (Or.inr (Or.inr e)) hb
    · exact h.sact t ht (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr e))))) hb⟩

/-- **`BlkOK` at core `d`'s view and the executing core's clauses give `BlkOK`.** -/
theorem BlkOK.viewR {d : U64} {s : S} (h : @BlkOK S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (p : PerCore st T Cs Scs Z Ac (L.cpu s) s) : @BlkOK S st L T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, q⟩, hB, ⟨hO, hR, hE⟩, hS, hSg⟩ := h
  exact ⟨⟨Q, R, queues_viewR q p⟩, bound_viewR hB p, ⟨objsOK_viewR hO, reply_viewR hR p.idleR, scExtra_viewR hE p.csc⟩,
    scsOK_viewR hS p.disj, sgOK_viewR hSg⟩

/-- `EntryInv` at the base store is `EntryInv` at the executing core's view. -/
theorem EntryInv.toView {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    @EntryInv S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  have h' := BlkOK.viewB h.blkOK (PerCore.ofB h.blkOK)
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.1.2.2.tm, h.2.2.2.2.2⟩

theorem EntryInv.ofView {s : S} (h : @EntryInv S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s := by
  have hb := @EntryInv.blkOK S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) _ _ _ _ _ _ _ _ _ _ _ h
  have h' := BlkOK.viewR hb (PerCore.of hb)
  exact ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2.1, h'.2.2.1.2.2.tm, h.2.2.2.2.2⟩

end

end Fl4Proofs.P2.Stall
