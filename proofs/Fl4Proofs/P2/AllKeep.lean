/-
P2 (p2j8): **the refined frame of a step on one core** (`OKeep2`) and
`AllCores.step2`.

`AllStep`'s `LocW` protects every thread's `SC`/`AFFINITY` and every SC's
`REPLY`/`TCB` words, which a donation (`send_ipc` to a passive server, a
notification's SC to its waiter) or `reply_push` writes. What the other cores'
clauses of `AllCores` read is narrower:

* `LocW2 e s`: every core's `IDLE_THREAD`/`IDLE_SC` node words, the other
  cores' `CUR_THREAD`/`SCHED_ACTION`/`CUR_SC`; the `STATE`, `IN_QUEUES`,
  `AFFINITY` and `SC` words of the other cores' idle, current and action
  threads (`OtherK e`); every idle thread's `AFFINITY` and `SC`; the `REPLY`
  and `TCB` words of every idle thread's SC.
* (p2j15) the `STATE` of `OtherK` is kept only up to `StK` (unchanged, or
  runnable before and after): `send_signal` may complete a remote, descheduled
  `RUNNING_VM` thread (`RUNNING_VM` to `RUNNING`), possibly another core's
  action thread; every reader needs only `Runnable` / not `Blocked(R)`.
* `OKeep2 e s s'`: those words kept (`OKeep2.trans`, `OKeep2.ofW` from a
  footprint missing `LocW2`).
* `CoreInv.keep2`: `OKeep2` keeps another core's `CoreInv`, given at the end
  P1's SC facts (`ObjsOK`, `bound`, `TSc`): the SC-disjointness clause `disj`
  follows from `scDisj` at the end, and `idleR` (an SC bound to the idle
  thread has no reply) from `TSc` (such an SC is the idle thread's own, whose
  links are kept).
* **`AllCores.step2`**: `AllCores.step` with `OKeep2` in place of the
  footprint obligation.

Named premise: `hS0` [W] (`0 ∉ Scs`: no SC object at the null address; P1's
`TSc` asks `c ≠ 0`).
-/
import Fl4Proofs.P2.AllStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The words a step on core `e` must not write (module docstring). -/
def LocW2 (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (e : U64) (s : S) (b : U64) : Prop :=
  (∃ c ∈ Cs, ∃ o : U64, (o.val = 8 ∨ o.val = 32 ∨ (c ≠ e ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) ∧
      b = L.nodeAt s c o) ∨
  (∃ y ∈ OtherK st T Cs e s, b = stA y ∨ b = inqA y ∨ b = affA y ∨ b = scA y) ∨
  (∃ c ∈ Cs, b = affA (idleAt st c s) ∨ b = scA (idleAt st c s)) ∨
  (∃ c ∈ Cs, b = scReplyA (L.mem s (scA (idleAt st c s))) ∨ b = scTcbA (L.mem s (scA (idleAt st c s))))

/-- A thread state kept, or runnable before and after (p2j15: a signal may
complete a remote descheduled VCPU thread, `RUNNING_VM` to `RUNNING`, which
can be another core's action thread). -/
def StK (v v' : U64) : Prop := v' = v ∨ (Runnable v ∧ Runnable v')

theorem StK.trans {v1 v2 v3 : U64} (h1 : StK v1 v2) (h2 : StK v2 v3) : StK v1 v3 := by
  rcases h1 with e1 | ⟨r1, r2⟩ <;> rcases h2 with e2 | ⟨r2', r3⟩
  · exact Or.inl (e2.trans e1)
  · subst e1; exact Or.inr ⟨r2', r3⟩
  · subst e2; exact Or.inr ⟨r1, r2⟩
  · exact Or.inr ⟨r1, r3⟩

theorem StK.run {v v' : U64} (h : StK v v') (hr : Runnable v) : Runnable v' := by
  rcases h with e | ⟨-, r⟩
  · rw [e]; exact hr
  · exact r

theorem StK.nb {v v' : U64} (h : StK v v') (hn : ¬ Blocked v) : ¬ Blocked v' := by
  rcases h with e | ⟨-, r⟩
  · rw [e]; exact hn
  · exact fun hb => not_runnable_of_blocked hb r

theorem StK.nbr {v v' : U64} (h : StK v v') (hn : ¬ BlockedR v) : ¬ BlockedR v' := by
  rcases h with e | ⟨-, r⟩
  · rw [e]; exact hn
  · rintro (hb | hb)
    · exact not_runnable_of_blocked hb r
    · rcases r with e | e | e <;> rw [hb] at e <;>
        simp_all [sched.TS_RUNNING, sched.TS_RESTART, sched.TS_RUNNING_VM, sched.TS_BLOCKED_ON_REPLY]

theorem StK.idle {v v' : U64} (h : StK v v') (hv : v = sched.TS_IDLE) : v' = sched.TS_IDLE := by
  rcases h with e | ⟨r, -⟩
  · rw [e]; exact hv
  · subst hv
    exact absurd r (by unfold Runnable sched.TS_IDLE sched.TS_RUNNING sched.TS_RESTART sched.TS_RUNNING_VM; decide)

/-- The words `LocW2` names, kept (a protected thread's `STATE` up to `StK`). -/
structure OKeep2 (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (e : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  nd : ∀ c ∈ Cs, ∀ o : U64, (o.val = 8 ∨ o.val = 32 ∨ (c ≠ e ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) →
    L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  kp : ∀ y ∈ OtherK st T Cs e s, StK (L.mem s (stA y)) (L.mem s' (stA y))
  iq : ∀ y ∈ OtherK st T Cs e s, L.mem s' (inqA y) = L.mem s (inqA y)
  af : ∀ y ∈ OtherK st T Cs e s, L.mem s' (affA y) = L.mem s (affA y)
  sc : ∀ y ∈ OtherK st T Cs e s, L.mem s' (scA y) = L.mem s (scA y)
  iaf : ∀ c ∈ Cs, L.mem s' (affA (idleAt st c s)) = L.mem s (affA (idleAt st c s))
  isc : ∀ c ∈ Cs, L.mem s' (scA (idleAt st c s)) = L.mem s (scA (idleAt st c s))
  ilk : ∀ c ∈ Cs, L.mem s' (scReplyA (L.mem s (scA (idleAt st c s)))) =
      L.mem s (scReplyA (L.mem s (scA (idleAt st c s)))) ∧
    L.mem s' (scTcbA (L.mem s (scA (idleAt st c s)))) = L.mem s (scTcbA (L.mem s (scA (idleAt st c s))))

theorem OKeep2.refl (e : U64) (s : S) : OKeep2 st T Cs e s s :=
  ⟨rfl, fun _ _ _ _ => rfl, fun _ _ => Or.inl rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem OKeep2.word {e c o : U64} {s s' : S} (k : OKeep2 st T Cs e s s') (hc : c ∈ Cs)
    (ho : o.val = 8 ∨ o.val = 32 ∨ (c ≠ e ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) :
    L.mem s' (L.nodeAt s' c o) = L.mem s (L.nodeAt s c o) := by
  rw [nodeAt_of_ksb k.ksb]; exact k.nd c hc o ho

/-- The node words of a core other than `e`, and every core's idle thread. -/
theorem OKeep2.words {e c : U64} {s s' : S} (k : OKeep2 st T Cs e s s') (hc : c ∈ Cs) (hne : c ≠ e) :
    actAt st c s' = actAt st c s ∧ curAt st c s' = curAt st c s ∧ idleAt st c s' = idleAt st c s ∧
      cscAt st c s' = cscAt st c s :=
  ⟨k.word hc (Or.inr (Or.inr ⟨hne, Or.inr (Or.inl act_val)⟩)), k.word hc (Or.inr (Or.inr ⟨hne, Or.inl curth0⟩)),
    k.word hc (Or.inl idle8), k.word hc (Or.inr (Or.inr ⟨hne, Or.inr (Or.inr (by simp [layout.node.CUR_SC]))⟩))⟩

theorem OKeep2.idle_eq {e c : U64} {s s' : S} (k : OKeep2 st T Cs e s s') (hc : c ∈ Cs) :
    idleAt st c s' = idleAt st c s := k.word hc (Or.inl idle8)

theorem OKeep2.otherK {e : U64} {s s' : S} (k : OKeep2 st T Cs e s s') :
    OtherK st T Cs e s' = OtherK st T Cs e s := by
  ext y
  constructor
  · rintro ⟨c, hc, hne, h⟩
    obtain ⟨ea, ec, ei, -⟩ := k.words hc hne
    rw [ea, ec, ei] at h
    exact ⟨c, hc, hne, h⟩
  · rintro ⟨c, hc, hne, h⟩
    obtain ⟨ea, ec, ei, -⟩ := k.words hc hne
    rw [← ea, ← ec, ← ei] at h
    exact ⟨c, hc, hne, h⟩

theorem OKeep2.trans {e : U64} {s s1 s2 : S} (k1 : OKeep2 st T Cs e s s1) (k2 : OKeep2 st T Cs e s1 s2) :
    OKeep2 st T Cs e s s2 := by
  have hK : ∀ {y}, y ∈ OtherK st T Cs e s → y ∈ OtherK st T Cs e s1 := fun hy => by rw [k1.otherK]; exact hy
  refine ⟨k2.ksb.trans k1.ksb, fun c hc o ho => ?_, fun y hy => (k1.kp y hy).trans (k2.kp y (hK hy)),
    fun y hy => (k2.iq y (hK hy)).trans (k1.iq y hy), fun y hy => (k2.af y (hK hy)).trans (k1.af y hy),
    fun y hy => (k2.sc y (hK hy)).trans (k1.sc y hy), fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · have e2 := k2.nd c hc o ho
    rw [nodeAt_of_ksb k1.ksb] at e2
    exact e2.trans (k1.nd c hc o ho)
  · have e2 := k2.iaf c hc
    rw [k1.idle_eq hc] at e2
    exact e2.trans (k1.iaf c hc)
  · have e2 := k2.isc c hc
    rw [k1.idle_eq hc] at e2
    exact e2.trans (k1.isc c hc)
  · have e2 := k2.ilk c hc
    rw [k1.idle_eq hc, k1.isc c hc] at e2
    exact ⟨e2.1.trans (k1.ilk c hc).1, e2.2.trans (k1.ilk c hc).2⟩

/-- **Writes that miss `LocW2 e s` keep its words**, from the placement at `s`. -/
theorem OKeep2.ofW {s s' : S} {F : U64 → Prop} {e : U64} {X : Set U64} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs e s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs)
    (w : WritesIn st s s' F) (hF : ∀ b, F b → ¬ LocW2 st T Cs e s b) : OKeep2 st T Cs e s s' := by
  have keep : ∀ b, LocW2 st T Cs e s b → Aligned b → L.mem s' b = L.mem s b :=
    fun b hb al => w.2.2 b al fun hf => hF b hf hb
  refine ⟨w.1, fun c hc o ho => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · exact keep _ (Or.inl ⟨c, hc, o, ho, rfl⟩) (nodeAt_aligned (hq.nodes c hc) (by omega) (by omega))
  · exact Or.inl (keep _ (Or.inr (Or.inl ⟨y, hy, Or.inl rfl⟩))
      (by rw [stA_eq]; exact field_aligned (hq.tcbs y (hKT y hy)) (by simp) (by simp)))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr (Or.inl rfl)⟩)) (inqA_aligned (hq.tcbs y (hKT y hy)))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr (Or.inr (Or.inl rfl))⟩))
      (by rw [affA_eq]; exact field_aligned (hq.tcbs y (hKT y hy)) (by simp) (by simp))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr (Or.inr (Or.inr rfl))⟩)) (scA_aligned (hq.tcbs y (hKT y hy)))
  · exact keep _ (Or.inr (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩)))
      (by rw [affA_eq]; exact field_aligned (hq.tcbs _ (hiT c hc)) (by simp) (by simp))
  · exact keep _ (Or.inr (Or.inr (Or.inl ⟨c, hc, Or.inr rfl⟩))) (scA_aligned (hq.tcbs _ (hiT c hc)))
  · obtain ⟨⟨a1, -⟩, ⟨a2, -⟩⟩ := sclink_in hO (hiS c hc)
    exact ⟨keep _ (Or.inr (Or.inr (Or.inr ⟨c, hc, Or.inl rfl⟩))) a1,
      keep _ (Or.inr (Or.inr (Or.inr ⟨c, hc, Or.inr rfl⟩))) a2⟩

/-- A core's `IdleSc` across `OKeep2`. -/
theorem OKeep2.idleSc {e c : U64} {s s' : S} (k : OKeep2 st T Cs e s s') (hc : c ∈ Cs) (h : IdleSc st c s) :
    IdleSc st c s' := by
  unfold IdleSc at h ⊢
  rw [k.word (o := layout.node.IDLE_SC) hc (Or.inr (Or.inl (by simp [layout.node.IDLE_SC]))),
    k.word (o := layout.node.IDLE_THREAD) hc (Or.inl idle8)]
  show L.mem s (L.nodeAt s c layout.node.IDLE_SC) = L.mem s' (scA (idleAt st c s))
  rw [k.isc c hc]; exact h

/-- **`OKeep2` keeps another core's clauses**, given P1's SC facts at the end. -/
theorem CoreInv.keep2 {e c : U64} {s s' : S} (p : CoreInv st T Cs Scs Z Ac c s)
    (k : OKeep2 st T Cs e s s') (hc : c ∈ Cs) (hne : c ≠ e) (hS0 : (0#u64) ∉ Scs)
    (hO' : ObjsOK st Ω Sg Rp Scs Nt Z s')
    (hbd' : ∀ t ∈ T, L.mem s' (scA t) ≠ 0#u64 → L.mem s' (scA t) ∈ Scs) (hts' : TSc st Scs s')
    (hT : TcbPlaced T) :
    CoreInv st T Cs Scs Z Ac c s' := by
  obtain ⟨ea, ec, ei, es⟩ := k.words hc hne
  have kI : idleAt st c s ∈ OtherK st T Cs e s := ⟨c, hc, hne, Or.inl rfl⟩
  have kC : curAt st c s ∈ OtherK st T Cs e s := ⟨c, hc, hne, Or.inr (Or.inl rfl)⟩
  have kA : actAt st c s ∈ T → actAt st c s ∈ OtherK st T Cs e s := fun h => ⟨c, hc, hne, Or.inr (Or.inr ⟨rfl, h⟩)⟩
  obtain ⟨p, ac, ne, csc, isc⟩ := p
  refine ⟨⟨hc, by rw [ea]; exact p.action, fun h => by
      rw [ea] at h ⊢; exact (k.kp _ (kA h)).run (p.run h),
    fun h => by rw [ea] at h ⊢; rw [k.iq _ (kA h)]; exact p.rel h,
    by rw [ec]; exact p.curT, by rw [ei]; exact p.idleT,
    fun h => by rw [ea] at h ⊢; rw [k.sc _ (kA h)]; exact p.act h,
    by rw [ei, k.sc _ kI]; exact p.idle, fun h => by rw [ec, k.sc _ kC]; exact p.resume (ea ▸ h),
    by rw [ei]; exact (k.kp _ kI).nbr p.idleNB, fun t ht ho hb => ?_, fun j hj hb => ?_, by rw [es]; exact p.csc,
    fun t ht hb hn b hb' => ?_⟩, by rw [es]; exact ac, by rw [ea, ec]; exact ne, fun hb => ?_, ?_⟩
  · rw [ea, ei, ec] at ho
    have hK : t ∈ OtherK st T Cs e s := by
      rcases ho with rfl | rfl | ⟨-, rfl⟩
      · exact kA ht
      · exact kI
      · exact kC
    rw [k.sc t hK] at hb ⊢
    exact p.sact t ht ho hb
  · rw [ei] at hb
    have hi0 : idleAt st c s ≠ 0#u64 := fun h0 => (hT _ p.idleT).ne0 (by rw [h0]; rfl)
    have hj0 : j ≠ 0#u64 := fun h0 => hS0 (h0 ▸ hj)
    have e1 : L.mem s' (scA (idleAt st c s)) = j := by
      have := hts' j hj hj0 (by rw [hb]; exact hi0)
      rwa [hb] at this
    rw [k.sc _ kI] at e1
    subst e1
    obtain ⟨l1, l2⟩ := k.ilk c hc
    rw [l1]; rw [l2] at hb; exact p.idleR _ hj hb
  · rw [es] at hn ⊢
    have := hO'.scDisj _ (hbd' t ht hb) _ p.csc hn
    unfold Outside; unfold InSC at hb'; omega
  · rw [ec, k.sc _ kC] at hb ⊢
    rw [es]; exact csc hb
  · exact k.idleSc hc isc

/-- **A step on the executing core keeps `AllCores`**, from `OKeep2` and its
end facts at that core. -/
theorem AllCores.step2 {s s' : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcpu : L.cpu s ∈ Cs)
    (k : OKeep2 st T Cs (L.cpu s) s s') (hS0 : (0#u64) ∉ Scs)
    (he : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s') (hc' : L.cpu s' = L.cpu s)
    (ha : L.mem s' (affA (curAt st (L.cpu s) s')) = L.cpu s)
    (hac : actAt st (L.cpu s) s' ∈ T → L.mem s' (affA (actAt st (L.cpu s) s')) = L.cpu s)
    (hnb : ¬ Blocked (L.mem s' (stA (curAt st (L.cpu s) s'))))
    (hnq : curAt st (L.cpu s) s' ≠ idleAt st (L.cpu s) s' →
      (L.mem s' (inqA (curAt st (L.cpu s) s')) &&& sched.Q_QUEUED) = 0#u64)
    (hacNT : actAt st (L.cpu s) s' ∉ T) (hidl : L.mem s' (stA (idleAt st (L.cpu s) s')) = sched.TS_IDLE) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have hv : @EntryInv S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
    have := EntryInv.toView he
    rw [hc'] at this
    exact this
  have hb := @EntryInv.blkOK S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) _ _ _ _ _ _ _ _ _ _ _ hv
  obtain ⟨⟨Q', R', hq'⟩, -, hX', -⟩ := he
  have hbd' : ∀ t ∈ T, L.mem s' (scA t) ≠ 0#u64 → L.mem s' (scA t) ∈ Scs :=
    fun t ht h0 => (hX'.2.2.bound t ht h0).1
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc hT => ?_, fun c hc => ?_, fun c hc hn => ?_,
    fun c hc => ?_, fun c hc => ?_⟩
  · by_cases e : c = L.cpu s
    · rw [e]; exact ⟨hv, k.idleSc hcpu (h.inv _ hcpu).2⟩
    · have p := (h.core hc).keep2 k hc e hS0 hX'.1 hbd' hX'.2.2.tsc hq'.tcbs
      exact ⟨p.entry hb, p.isc⟩
  · by_cases e : c = L.cpu s
    · rw [e]; exact ha
    · rw [(k.words hc e).2.1, k.af _ ⟨c, hc, e, Or.inr (Or.inl rfl)⟩]; exact h.curAff c hc
  · rw [k.idle_eq hc, k.iaf c hc]; exact h.idleAff c hc
  · by_cases e : c = L.cpu s
    · rw [e] at hT ⊢; exact hac hT
    · rw [(k.words hc e).1] at hT ⊢; rw [k.af _ ⟨c, hc, e, Or.inr (Or.inr ⟨rfl, hT⟩)⟩]; exact h.actAff c hc hT
  · by_cases e : c = L.cpu s
    · rw [e]; exact hnb
    · rw [(k.words hc e).2.1]; exact (k.kp _ ⟨c, hc, e, Or.inr (Or.inl rfl)⟩).nb (h.curNB c hc)
  · by_cases e : c = L.cpu s
    · rw [e] at hn ⊢; exact hnq hn
    · obtain ⟨-, ec, ei, -⟩ := k.words hc e
      rw [ec, k.iq _ ⟨c, hc, e, Or.inr (Or.inl rfl)⟩]
      exact h.nq c hc (by rw [← ec, ← ei]; exact hn)
  · by_cases e : c = L.cpu s
    · rw [e]; exact hacNT
    · rw [(k.words hc e).1]; exact h.actNT c hc
  · by_cases e : c = L.cpu s
    · rw [e]; exact hidl
    · rw [k.idle_eq hc]; exact (k.kp _ ⟨c, hc, e, Or.inl rfl⟩).idle (h.idleSt c hc)

end

end Fl4Proofs.P2.Stall
