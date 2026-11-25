/-
P2 (p2j7): **the all-cores per-core invariant `AllCores`**, and the remote
stall as an `AllCores → AllCores` step.

`AllCores s`: at every core `c ∈ Cs`,

* `inv`: P1's `EntryInv` at core `c`'s view and `IdleSc c`;
* `curAff`, `idleAff`, `actAff`: `c`'s current thread, idle thread and action
  thread (when the action is a thread) have `AFFINITY` `c` (`OwnJ`'s (1);
  `create_idle_thread`; `possible_switch_to` sets the action only to a thread
  whose affinity is the executing core, sched.rs:369–375);
* `curNB`: `c`'s current thread is not blocked on an endpoint or
  notification;
* `nq`: `c`'s current thread, unless idle, is in no ready queue (seL4
  `ct_not_in_q`);
* (p2j16) `actNT`: `c`'s action is no thread (serialized entries, each ending
  in `schedule`, DESIGN §7 (3)); `idleSt`: `c`'s idle thread is `TS_IDLE`.

Open internal obligation of `stallAt.all` (p2j16, until the stall's frame
protects the stalled core's idle thread): `hidl`, the stalled core's idle
thread still `TS_IDLE` at the stall's end.

`AllCores.notK`: a thread of affinity `d` is none of the other cores' idle,
current or action threads (`OtherK d`), since those have the other cores as
affinity. So `AllCores` gives every [J] premise of `stallAt.views` (`hown`,
`hactK`, `hcurNB`, `hnq`, and the other cores' `CoreInv`), and
**`stallAt.all`**: from `AllCores` (and the transfer premises of
`stallAt.views`: `hRSK`, `XG`, `RS`, `UserOK` at the view of `d`,
`XferOKRS` [J], `XferFootOKC` [J], `TmoCap` [P]) a stall of `d` ends in `AllCores`, with `d` on
its idle thread and the other cores' actions kept. The per-core [J] premises
of `stallAt.views` (`hown`, `hactK`, `hcurNB`, `hnq`) are gone; `XferFootOKC`
stays [J] (its discharge from P1's `XferHyps` was vacuous, p2j8), and
`XferOKRS` [J] replaces P1's unguarded `XferOK` (p2j13).

Not in `AllCores`: `OwnJ`'s (2) `AffSc` (a bound SC's `CORE` is its thread's
affinity). Keeping it across the stall needs the SCs' `CORE` words among the
protected words of the core-separated footprint (`FootN`'s `PrW`); the stall
writes the current SC's refills and `CONSUMED`, not its `CORE`.
-/
import Fl4Proofs.P2.StallAll
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {P3Ok : S → Prop} {A : Type _} {ar : machine.Arch A}

/-- **The all-cores per-core invariant** (module docstring). -/
structure AllCores (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop where
  inv : ∀ c ∈ Cs, @EntryInv S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s ∧ IdleSc st c s
  curAff : ∀ c ∈ Cs, L.mem s (affA (curAt st c s)) = c
  idleAff : ∀ c ∈ Cs, L.mem s (affA (idleAt st c s)) = c
  actAff : ∀ c ∈ Cs, actAt st c s ∈ T → L.mem s (affA (actAt st c s)) = c
  curNB : ∀ c ∈ Cs, ¬ Blocked (L.mem s (stA (curAt st c s)))
  nq : ∀ c ∈ Cs, curAt st c s ≠ idleAt st c s → (L.mem s (inqA (curAt st c s)) &&& sched.Q_QUEUED) = 0#u64
  /-- (p2j16) No core's action is a thread: entries are serialized (DESIGN §7 (3)) and each ends in
  `schedule`, which leaves `RESUME_CURRENT`. -/
  actNT : ∀ c ∈ Cs, actAt st c s ∉ T
  /-- (p2j16) Every idle thread's `STATE` is `TS_IDLE` (boot.rs:690; nothing writes it). -/
  idleSt : ∀ c ∈ Cs, L.mem s (stA (idleAt st c s)) = sched.TS_IDLE

/-- Core `c`'s `CoreInv`. -/
theorem AllCores.core {s : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s) {c : U64} (hc : c ∈ Cs) :
    CoreInv st T Cs Scs Z Ac c s :=
  CoreInv.of (h.inv c hc).1 (h.inv c hc).2

/-- A thread of affinity `d` is none of the other cores' idle, current or
action threads. -/
theorem AllCores.notK {s : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s) {d y : U64}
    (hy : L.mem s (affA y) = d) : y ∉ OtherK st T Cs d s := by
  rintro ⟨c, hc, hne, rfl | rfl | ⟨rfl, hy'⟩⟩
  · exact hne ((h.idleAff c hc).symm.trans hy)
  · exact hne ((h.curAff c hc).symm.trans hy)
  · exact hne ((h.actAff c hc hy').symm.trans hy)

/-- A core's `IDLE_THREAD` across `OKeep`. -/
theorem OKeep.idleAt {Kp : Set U64} {d c : U64} {s s' : S} (k : OKeep st T Cs Scs Kp d s s') (hc : c ∈ Cs) :
    idleAt st c s' = idleAt st c s := by
  show L.mem s' (L.nodeAt s' c layout.node.IDLE_THREAD) = L.mem s (L.nodeAt s c layout.node.IDLE_THREAD)
  rw [nodeAt_of_ksb k.ksb]; exact k.nd c hc _ (Or.inl idle8)

/-- **A remote stall of `d` from `AllCores` ends in `AllCores`.**
Named premises: `hxf` [J] (`XferOKRS`, `P2/FootN5.lean`), `hxw` [J] (`XferFootOKC`,
`P2/XferN.lean`). -/
theorem stallAt.all (hA : P0.ArchTotal ar) (d : U64) (hd : d ∈ Cs)
    {RS : S → S → Prop}
    (hxf : @XferOKRS S (atCpu st d) (L.atCpu d) A ar T Cs Ω H Sg Rp Scs Nt Z U RS
      (@XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok))
    (hxw : @XferFootOKC S (atCpu st d) (L.atCpu d) A ar T Cs Ω H Sg Rp Scs Nt Z U RS
      (@XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → @WritesIn S (atCpu st d) (L.atCpu d) s1 s2
      (@KW S (atCpu st d) (L.atCpu d) T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (s : S) (a : A) (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : @XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok s)
    (hRS0 : RS s s) (hU : @UserOK S (atCpu st d) (L.atCpu d) T Cs Ω H U s)
    (hcap : @TmoCap S (atCpu st d) (L.atCpu d) Scs Z H Rp Nt s)
    (hidl : stallAt st ar d s a ⦃ s' _ => L.mem s' (stA (idleAt st d s')) = sched.TS_IDLE ⦄) :
    stallAt st ar d s a ⦃ s' _ =>
      AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ curAt st d s' = idleAt st d s' ∧
      (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ⦄ := by
  refine WP.spec_mono (WP.spec_and (stallAt.views (Ac := Ac) (P3Ok := P3Ok) hA d hxf hxw hRSK s a (h.inv d hd).1
    (h.inv d hd).2 hG hRS0 hU hcap (fun c hc _ => h.core hc) (h.notK (h.curAff d hd))
    (fun ha => h.notK (h.actAff d hd ha)) (fun c hc _ => h.curNB c hc) (h.nq d hd)) hidl) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨hinv, k, hcur, hac, hoth⟩, hid⟩ := hh
  refine ⟨⟨hinv, fun c hc => ?_, fun c hc => ?_, fun c hc ha => ?_, fun c hc => ?_, fun c hc hn => ?_,
    fun c hc => ?_, fun c hc => ?_⟩, hcur, hoth⟩
  · by_cases e : c = d
    · rw [e, hcur, k.idleAt hd, k.af _ (h.core hd).per.idleT]; exact h.idleAff d hd
    · rw [(keep_words k hc e).2.1, k.af _ (h.core hc).per.curT]; exact h.curAff c hc
  · rw [k.idleAt hc, k.af _ (h.core hc).per.idleT]; exact h.idleAff c hc
  · by_cases e : c = d
    · rw [e] at ha ⊢
      rcases hac with hac | hac
      · rw [hac] at ha ⊢; rw [k.af _ ha]; exact h.actAff d hd ha
      · obtain ⟨⟨Q, R, hq⟩, -⟩ := (h.inv d hd).1
        rw [hac] at ha
        exact absurd (by simp) (hq.tcbs _ ha).ne0
    · rw [(keep_words k hc e).1] at ha ⊢; rw [k.af _ ha]; exact h.actAff c hc ha
  · by_cases e : c = d
    · rw [e, hcur]
      exact fun hb => (CoreInv.of (hinv d hd).1 (hinv d hd).2).per.idleNB (Or.inl hb)
    · rw [(keep_words k hc e).2.1, k.kp _ ⟨c, hc, e, Or.inr (Or.inl rfl)⟩]; exact h.curNB c hc
  · by_cases e : c = d
    · rw [e] at hn; exact absurd hcur hn
    · obtain ⟨-, ec, ei, -⟩ := keep_words k hc e
      refine k.nq hc e ⟨c, hc, e, Or.inr (Or.inl rfl)⟩ (h.nq c hc ?_)
      rw [← ec, ← ei]; exact hn
  · by_cases e : c = d
    · rw [e]
      rcases hac with hac | hac
      · rw [hac]; exact h.actNT d hd
      · obtain ⟨⟨Q, R, hq⟩, -⟩ := (h.inv d hd).1
        rw [hac]
        exact fun ha => absurd (by simp) (hq.tcbs _ ha).ne0
    · rw [(keep_words k hc e).1]; exact h.actNT c hc
  · by_cases e : c = d
    · rw [e]; exact hid
    · rw [k.idleAt hc, k.kp _ ⟨c, hc, e, Or.inl rfl⟩]; exact h.idleSt c hc

end

end Fl4Proofs.P2.Stall
