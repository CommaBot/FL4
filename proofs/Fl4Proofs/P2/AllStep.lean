/-
P2 (p2j7): **a step on one core keeps `AllCores`**, from its footprint and its
end state at the executing core (the `AllCores` analogue of `OwnJ.accept`).

* `LocW e s`: the words a step on core `e` must not write: every core's
  `IDLE_THREAD` and `IDLE_SC` node words, the other cores' `CUR_THREAD`,
  `SCHED_ACTION` and `CUR_SC`, the `STATE` and `IN_QUEUES` words of the other
  cores' idle, current and action threads (`OtherK e`), every TCB's
  `AFFINITY` and `SC`, and every SC's `REPLY` and `TCB` link.
* `OKeep.ofW`: a step whose writes (`WritesIn … F`) miss `LocW e s` keeps them
  (`OKeep`, as the stall's), from P1's `EntryInv` at the start.
* **`AllCores.step`**: from `AllCores s`, a step on the executing core
  `e = L.cpu s` whose writes miss `LocW e s`, and its end facts at `e` (P1's
  `EntryInv` at the end; `e`'s current and action threads of affinity `e`; the
  current thread not blocked and, unless idle, in no ready queue) gives
  `AllCores s'`. The other cores' clauses and `e`'s `IdleSc` follow from the
  frame alone.

Premises of `AllCores.step` (each step instance discharges them): the
footprint obligation `hF` and the end facts `he`, `ha`, `hac`, `hnb`, `hnq`.
For the stall the same frame is `stallAt.all`. P1 proves each accepted local
path ends where the serial entry ends (`inv_local_same`, `usf_same`,
`hus_same`, …), so a local path's instance is its serial entry's.
-/
import Fl4Proofs.P2.AllCores
import Fl4Proofs.P2.StallBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The words a step on core `e` must not write (module docstring). -/
def LocW (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (e : U64) (s : S) (b : U64) : Prop :=
  (∃ c ∈ Cs, ∃ o : U64, (o.val = 8 ∨ o.val = 32 ∨ (c ≠ e ∧ (o.val = 0 ∨ o.val = 16 ∨ o.val = 24))) ∧
      b = L.nodeAt s c o) ∨
  (∃ y ∈ OtherK st T Cs e s, b = stA y ∨ b = inqA y) ∨
  (∃ y ∈ T, b = affA y ∨ b = scA y) ∨
  (∃ c ∈ Scs, b = scReplyA c ∨ b = scTcbA c)

/-- The other cores' idle, current and action threads are TCBs. -/
theorem AllCores.KT {s : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s) {e : U64} :
    ∀ y ∈ OtherK st T Cs e s, y ∈ T := by
  rintro y ⟨c, hc, -, rfl | rfl | ⟨rfl, hy⟩⟩
  · exact (h.core hc).per.idleT
  · exact (h.core hc).per.curT
  · exact hy

/-- **Writes that miss `LocW e s` keep the words `OKeep` reads.** -/
theorem OKeep.ofW {s s' : S} {F : U64 → Prop} {e : U64}
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hKT : ∀ y ∈ OtherK st T Cs e s, y ∈ T)
    (w : WritesIn st s s' F) (hF : ∀ b, F b → ¬ LocW st T Cs Scs e s b) :
    OKeep st T Cs Scs (OtherK st T Cs e s) e s s' := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -⟩ := h
  have keep : ∀ b, LocW st T Cs Scs e s b → Aligned b → L.mem s' b = L.mem s b :=
    fun b hb al => w.2.2 b al fun hf => hF b hf hb
  refine ⟨w.1, fun c hc o ho => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_⟩
  · exact keep _ (Or.inl ⟨c, hc, o, ho, rfl⟩) (nodeAt_aligned (hq.nodes c hc) (by omega) (by omega))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inl rfl⟩))
      (by rw [stA_eq]; exact field_aligned (hq.tcbs y (hKT y hy)) (by simp) (by simp))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr rfl⟩)) (inqA_aligned (hq.tcbs y (hKT y hy)))
  · exact keep _ (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl rfl⟩)))
      (by rw [affA_eq]; exact field_aligned (hq.tcbs y hy) (by simp) (by simp))
  · exact keep _ (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr rfl⟩))) (scA_aligned (hq.tcbs y hy))
  · obtain ⟨⟨a1, -⟩, ⟨a2, -⟩⟩ := sclink_in hX.1 hc
    exact ⟨keep _ (Or.inr (Or.inr (Or.inr ⟨c, hc, Or.inl rfl⟩))) a1,
      keep _ (Or.inr (Or.inr (Or.inr ⟨c, hc, Or.inr rfl⟩))) a2⟩

/-- **A step on the executing core keeps `AllCores`**, from its footprint
obligation `hF` and its end facts at that core. -/
theorem AllCores.step {s s' : S} {F : U64 → Prop} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcpu : L.cpu s ∈ Cs) (w : WritesIn st s s' F) (hF : ∀ b, F b → ¬ LocW st T Cs Scs (L.cpu s) s b)
    (he : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s')
    (ha : L.mem s' (affA (curAt st (L.cpu s) s')) = L.cpu s)
    (hac : actAt st (L.cpu s) s' ∈ T → L.mem s' (affA (actAt st (L.cpu s) s')) = L.cpu s)
    (hnb : ¬ Blocked (L.mem s' (stA (curAt st (L.cpu s) s'))))
    (hnq : curAt st (L.cpu s) s' ≠ idleAt st (L.cpu s) s' →
      (L.mem s' (inqA (curAt st (L.cpu s) s')) &&& sched.Q_QUEUED) = 0#u64) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have k := OKeep.ofW (EntryInv.ofView (h.inv _ hcpu).1) h.KT w hF
  have hv : @EntryInv S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
    have := EntryInv.toView he
    rw [w.2.1] at this
    exact this
  have hb := @EntryInv.blkOK S (atCpu st (L.cpu s)) (L.atCpu (L.cpu s)) _ _ _ _ _ _ _ _ _ _ _ hv
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc hT => ?_, fun c hc => ?_, fun c hc hn => ?_⟩
  · by_cases e : c = L.cpu s
    · rw [e]; exact ⟨hv, k.idle hcpu (h.core hcpu).per.idleT (h.inv _ hcpu).2⟩
    · have p := (h.core hc).keep k hc e ⟨c, hc, e, Or.inl rfl⟩ fun h' => ⟨c, hc, e, Or.inr (Or.inr ⟨rfl, h'⟩)⟩
      exact ⟨p.entry hb, p.isc⟩
  · by_cases e : c = L.cpu s
    · rw [e]; exact ha
    · rw [(keep_words k hc e).2.1, k.af _ (h.core hc).per.curT]; exact h.curAff c hc
  · rw [k.idleAt hc, k.af _ (h.core hc).per.idleT]; exact h.idleAff c hc
  · by_cases e : c = L.cpu s
    · rw [e] at hT ⊢; exact hac hT
    · rw [(keep_words k hc e).1] at hT ⊢; rw [k.af _ hT]; exact h.actAff c hc hT
  · by_cases e : c = L.cpu s
    · rw [e]; exact hnb
    · rw [(keep_words k hc e).2.1, k.kp _ ⟨c, hc, e, Or.inr (Or.inl rfl)⟩]; exact h.curNB c hc
  · by_cases e : c = L.cpu s
    · rw [e] at hn ⊢; exact hnq hn
    · obtain ⟨-, ec, ei, -⟩ := keep_words k hc e
      refine k.nq hc e ⟨c, hc, e, Or.inr (Or.inl rfl)⟩ (h.nq c hc ?_)
      rw [← ec, ← ei]; exact hn

end

end Fl4Proofs.P2.Stall
