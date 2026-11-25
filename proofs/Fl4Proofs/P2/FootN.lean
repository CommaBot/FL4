/-
P2 (p2j, KWN step 1): **`KWN`, the core-separated footprint** (built beside
P1's `KW` the way KENTRY-PLAN a6f built `KWB`; `KW`, `Foot` and every P1
lemma are untouched).

`KW` (P1 `QueueFoot`) admits a write to any node word of any core but the
debug-list head. `KWN` is `KW` without the **node identity words** `IdW`:
every core's `IDLE_THREAD` (offset 8) and `IDLE_SC` (32), and, of every core
other than the executing one, `CUR_THREAD` (0), `SCHED_ACTION` (16) and
`CUR_SC` (24). No kernel operation writes them (the idle words are written
once, at boot, `create_idle_thread`; a core's current thread, action and SC
only by that core, `smp::stall` included, which runs at the stalled core's
view). A `KWN` footprint (`FootN`) therefore keeps every core's idle thread
and idle SC, and every other core's current thread, action and current SC
(`FootN.idKeep`): the frame the stall (`P2/StallAt.lean`) and the all-cores
invariant need.

Here: the definitions and their API (`FootN.refl`/`trans`/`foot`, `FootN.of'`,
`footN_wr`/`footN_field`/`footN_node`, `notIdW_field`/`notIdW_node`/
`notIdW_out`), and the `.kwN` versions of P1's scheduler-queue footprints:
`QFoot.kwN`, `enqueue`, `dequeue`, `release_remove`, `set_action`,
`schedule_tcb`, `set_thread_state`, `reschedule_required`,
`possible_switch_to`, the two `unblock_sporadic`, `reply_unlink`. No premise.

**Exclusion layer (p2j3).** `KWN`/`FootN` take two more parameters, `Kp`
(threads whose `STATE` word is protected) and `Nd` (no-donation mode):
`IdW` is now `IdN` (the node identity words, plus, under `Nd`, the
executing core's own `CUR_THREAD`) or `PrW` (the `STATE` of `Kp`; under
`Nd` every thread's `SC` word and every SC's `REPLY`/`TCB` words). With
`Kp = ∅`, `Nd = False` this is the old `KWN`. A stall's budget path runs
with `Kp` = the other cores' idle threads and `Nd` true, so its footprint
keeps their states, every thread's SC binding, every SC's reply stack and
thread, and the stalled core's current thread. The lemmas writing a `STATE`
take `t ∉ Kp`; those writing an SC link (`donate`) take `¬ Nd`.

**(p2j5)** `PrW` also protects the `IN_QUEUES` words of `Kp` and, under `Nd`,
every thread's `AFFINITY`: `Kp` now is the other cores' idle, current and
action threads, which a stall keeps unqueued (seL4 `ct_not_in_q`). The
queue operations take `t ∉ Kp`. `reschedule_required` queues the executing
core's action thread, so the footprint also carries `AcK` (a new
`SCHED_ACTION` is no thread of `Kp`; `WritesA`), and it and
`possible_switch_to` take `ActOut` (the action is no thread of `Kp`).
-/
import Fl4Proofs.P1.QueueFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- The node offsets no kernel operation writes: the idle thread (8) and
idle SC (32) of every core; `CUR_THREAD` (0), `SCHED_ACTION` (16) and
`CUR_SC` (24) of a core other than the executing one (`cur` false); and,
in no-donation mode `nd` (a stall's budget path), the executing core's own
`CUR_THREAD` (0). -/
def IdOff (cur nd : Prop) (o : Nat) : Prop :=
  o = 8 ∨ o = 32 ∨ (¬ cur ∧ (o = 0 ∨ o = 16 ∨ o = 24)) ∨ (nd ∧ cur ∧ o = 0)

theorem idOff_cur {c : U64} {nd : Prop} {o : Nat} (h8 : o ≠ 8) (h32 : o ≠ 32) (h0 : nd → o ≠ 0) :
    ¬ IdOff (c = c) nd o := by
  rintro (e | e | ⟨hne, -⟩ | ⟨hn, -, e⟩)
  · exact h8 e
  · exact h32 e
  · exact hne rfl
  · exact h0 hn e

theorem idOff_ge {p q : Prop} {o : Nat} (h : 40 ≤ o) : ¬ IdOff p q o := by
  rintro (e | e | ⟨-, e | e | e⟩ | ⟨-, -, e⟩) <;> omega

theorem IdOff.lt {p q : Prop} {o : Nat} (h : IdOff p q o) : o < 40 := by
  rcases h with e | e | ⟨-, e | e | e⟩ | ⟨-, -, e⟩ <;> omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Es : Set U64} {Ac : Set U64}

/-- The node identity words at `s0` (`IdOff`). -/
def IdN (st : machine.Store S) [L : LawfulStore st] (Nd : Prop) (Cs : Set U64) (s0 : S) (b : U64) : Prop :=
  ∃ c ∈ Cs, ∃ o : U64, IdOff (c = L.cpu s0) Nd o.val ∧ b = L.nodeAt s0 c o

/-- **The protected thread and SC words** (P2 p2j3, the stall's exclusion
layer): the `STATE` and `IN_QUEUES` words of the threads `Kp` (the other
cores' threads, during a stall), and, when `Nd` (no
donation), every thread's `SC` and `AFFINITY` words and every SC's `REPLY` and `TCB` words.
The witnesses carry their placement (`TcbAddr`, `OutsideObjs`), so a node or
TCB-field write is seen to miss them without further hypotheses. -/
def PrW (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Scs : Set U64) (s0 : S)
    (b : U64) : Prop :=
  (∃ y ∈ T, TcbAddr y ∧ y ∈ Kp ∧ (b = stA y ∨ b = inqA y)) ∨
  (Nd ∧ ((∃ y ∈ T, TcbAddr y ∧ (b = scA y ∨ b = affA y)) ∨
    (∃ c ∈ Scs, (b = scReplyA c ∨ b = scTcbA c) ∧ OutsideObjs st T Cs s0 b)))

/-- The words no `KWN` step writes: the node identity words (`IdN`) and the
protected words (`PrW`). With `Kp = ∅` and `Nd = False` these are exactly the
node identity words. -/
def IdW (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Scs : Set U64) (s0 : S)
    (b : U64) : Prop :=
  IdN st Nd Cs s0 b ∨ PrW st Kp Nd T Cs Scs s0 b

/-- `KW` without the node identity and protected words. -/
def KWN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es : Set U64) (s0 : S) (b : U64) : Prop :=
  KW st T Cs Sg Scs Z Es s0 b ∧ ¬ IdW st Kp Nd T Cs Scs s0 b

/-- The executing core's action is no protected thread. -/
def ActOut (st : machine.Store S) [L : LawfulStore st] (T Kp : Set U64) (s : S) : Prop :=
  L.actionW s ∈ T → L.actionW s ∉ Kp

/-- A step makes no protected thread the executing core's action. -/
def AcK (st : machine.Store S) [L : LawfulStore st] (T Kp : Set U64) (s s' : S) : Prop :=
  L.actionW s' ∈ T → L.actionW s' ∈ Kp → L.actionW s' = L.actionW s

theorem AcK.of_eq {Kp : Set U64} {s s' : S} (h : L.actionW s' = L.actionW s) : AcK st T Kp s s' := fun _ _ => h

theorem AcK.of_nT {Kp : Set U64} {s s' : S} (h : L.actionW s' ∉ T) : AcK st T Kp s s' := fun h' => absurd h' h

theorem AcK.trans {Kp : Set U64} {s₁ s₂ s₃ : S} (h₁ : AcK st T Kp s₁ s₂) (h₂ : AcK st T Kp s₂ s₃) :
    AcK st T Kp s₁ s₃ := fun hT hK => by
  have e := h₂ hT hK
  exact e.trans (h₁ (e ▸ hT) (e ▸ hK))

theorem ActOut.step {Kp : Set U64} {s s' : S} (h : ActOut st T Kp s) (k : AcK st T Kp s s') : ActOut st T Kp s' :=
  fun hT hK => by
    have e := k hT hK
    exact h (e ▸ hT) (e ▸ hK)

/-- `WritesIn` with `AcK`. -/
def WritesA (st : machine.Store S) [L : LawfulStore st] (T Kp : Set U64) (s s' : S) (B : U64 → Prop) : Prop :=
  L.ksb s' = L.ksb s ∧ L.cpu s' = L.cpu s ∧ (∀ b, Aligned b → ¬ B b → L.mem s' b = L.mem s b) ∧ AcK st T Kp s s'

theorem WritesA.refl {Kp : Set U64} (s : S) (B : U64 → Prop) : WritesA st T Kp s s B :=
  ⟨rfl, rfl, fun _ _ _ => rfl, AcK.of_eq rfl⟩

theorem WritesA.w {Kp : Set U64} {s s' : S} {B : U64 → Prop} (h : WritesA st T Kp s s' B) : WritesIn st s s' B :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem WritesA.ac {Kp : Set U64} {s s' : S} {B : U64 → Prop} (h : WritesA st T Kp s s' B) : AcK st T Kp s s' :=
  h.2.2.2

theorem WritesA.out {Kp : Set U64} {s s' : S} {B : U64 → Prop} (h : WritesA st T Kp s s' B)
    (ha : ActOut st T Kp s) : ActOut st T Kp s' := ha.step h.ac

theorem WritesIn.a {Kp : Set U64} {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) (k : AcK st T Kp s s') :
    WritesA st T Kp s s' B := ⟨h.1, h.2.1, h.2.2, k⟩

theorem WritesA.mono {Kp : Set U64} {s s' : S} {A B : U64 → Prop} (h : WritesA st T Kp s s' A) (hAB : ∀ b, A b → B b) :
    WritesA st T Kp s s' B := (WritesIn.mono h.w hAB).a h.ac

theorem WritesA.trans {Kp : Set U64} {s₁ s₂ s₃ : S} {A B : U64 → Prop} (h₁ : WritesA st T Kp s₁ s₂ A)
    (h₂ : WritesA st T Kp s₂ s₃ B) : WritesA st T Kp s₁ s₃ (fun b => A b ∨ B b) :=
  (WritesIn.trans h₁.w h₂.w).a (h₁.ac.trans h₂.ac)

theorem WritesA.mem_eq {Kp : Set U64} {s s' : S} {B : U64 → Prop} (h : WritesA st T Kp s s' B) {b : U64}
    (hb : Aligned b) (hn : ¬ B b) : L.mem s' b = L.mem s b := h.2.2.1 b hb hn

/-- A step whose writes miss the action word keeps the action. -/
theorem actionW_of {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) (hN : NodePlaced st T s (L.cpu s))
    (hn : ¬ B (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) : L.actionW s' = L.actionW s := by
  unfold LawfulStore.actionW
  rw [h.2.1, nodeAt_of_ksb h.1]
  exact h.mem_eq (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])) hn

theorem actionW_out {s : S} {a v : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (ha : OutsideObjs st T Cs s a) : L.actionW (L.wr s a v) = L.actionW s :=
  actionW_of (writesIn_wr ha.1) (NP _ hc) fun e =>
    out_ne_node ha hc (NP _ hc) (by rw [act_val]; omega) (congrArg UScalar.val e)

theorem actionW_field {s : S} {y K v : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (hc : L.cpu s ∈ Cs) (hy : y ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) :
    L.actionW (L.wr s (core.num.U64.wrapping_add y K) v) = L.actionW s :=
  act_wr_field (NP _ hc) hy (hT y hy) rfl hK hK8

theorem act_aligned {s : S} (hN : NodePlaced st T s (L.cpu s)) :
    Aligned (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
  nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])

theorem notAct_omega {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) : L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ∉ Ω := fun hm =>
  out_ne_node (h.omega _ hm) h.cur (h.nodes _ h.cur) (by rw [act_val]; omega) rfl

theorem notAct_node {s : S} {c o : U64} (hN : NodePlaced st T s (L.cpu s)) (hN' : NodePlaced st T s c)
    (ho : o.val < 4288) (h16 : o.val ≠ 16) : L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ L.nodeAt s c o := fun e =>
  node_ne_node hN hN' (by rw [act_val]; omega) ho (fun _ => by rw [act_val]; exact fun h => h16 h.symm)
    (congrArg UScalar.val e)

/-- A footprint inside `KWN`. -/
abbrev FootN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es : Set U64) (s s' : S) : Prop :=
  WritesA st T Kp s s' (KWN st Kp Nd T Cs Sg Scs Z Es s)

variable {Kp : Set U64} {Nd : Prop}

theorem IdN.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : IdN st Nd Cs s0 b) : IdN st Nd Cs s1 b := by
  obtain ⟨c, hcs, o, ho, e⟩ := h
  exact ⟨c, hcs, o, by rw [hc]; exact ho, by rw [e, nodeAt_of_ksb hk]⟩

theorem PrW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : PrW st Kp Nd T Cs Scs s0 b) :
    PrW st Kp Nd T Cs Scs s1 b := by
  rcases h with h | ⟨hn, h | ⟨c, hc, e, ho⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨hn, Or.inl h⟩
  · exact Or.inr ⟨hn, Or.inr ⟨c, hc, e, ho.ksb hk⟩⟩

theorem IdW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : IdW st Kp Nd T Cs Scs s0 b) : IdW st Kp Nd T Cs Scs s1 b :=
  h.imp (IdN.ksb hk hc) (PrW.ksb hk)

theorem FootN.foot {s s' : S} (h : FootN st Kp Nd T Cs Sg Scs Z Es s s') : Foot st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono (WritesA.w h) fun _ hb => hb.1

theorem FootN.refl (s : S) : FootN st Kp Nd T Cs Sg Scs Z Es s s := WritesA.refl _ _

theorem FootN.trans {s₁ s₂ s₃ : S} (h₁ : FootN st Kp Nd T Cs Sg Scs Z Es s₁ s₂)
    (h₂ : FootN st Kp Nd T Cs Sg Scs Z Es s₂ s₃) : FootN st Kp Nd T Cs Sg Scs Z Es s₁ s₃ :=
  WritesA.mono (WritesA.trans h₁ h₂) fun b hb =>
    Or.elim hb id fun hb => ⟨KW.ksb h₁.1 hb.1, fun hi => hb.2 (hi.ksb h₁.1 h₁.2.1)⟩

theorem FootN.of' {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → KWN st Kp Nd T Cs Sg Scs Z Es s b) (hk : AcK st T Kp s s') :
    FootN st Kp Nd T Cs Sg Scs Z Es s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh), hk⟩

/-- **A `KWN` footprint keeps the node identity and protected words.** -/
theorem FootN.idKeep {s s' : S} (f : FootN st Kp Nd T Cs Sg Scs Z Es s s') {b : U64} (hb : Aligned b)
    (hi : IdW st Kp Nd T Cs Scs s b) : L.mem s' b = L.mem s b :=
  f.mem_eq hb fun hk => hk.2 hi

/-! ## Words outside `IdW` -/

theorem IdN.lt {s : S} {b : U64} (h : IdN st Nd Cs s b) :
    ∃ c ∈ Cs, ∃ o : U64, IdOff (c = L.cpu s) Nd o.val ∧ o.val < 40 ∧ b = L.nodeAt s c o := by
  obtain ⟨c, hc, o, ho, e⟩ := h
  exact ⟨c, hc, o, ho, ho.lt, e⟩

/-- What a write to field `K` of `y` must avoid: `STATE` and `IN_QUEUES` of a
protected thread, `SC` and `AFFINITY` under `Nd`. -/
def PrF (Kp : Set U64) (Nd : Prop) (y K : U64) : Prop :=
  (y ∈ Kp → K.val ≠ 3328 ∧ K.val ≠ 3592) ∧ (Nd → K.val ≠ 3464 ∧ K.val ≠ 3520)

theorem PrF.of_ne {y K : U64} (h1 : K.val ≠ 3328) (h2 : K.val ≠ 3592) (h3 : K.val ≠ 3464) (h4 : K.val ≠ 3520) :
    PrF Kp Nd y K := ⟨fun _ => ⟨h1, h2⟩, fun _ => ⟨h3, h4⟩⟩

theorem PrF.of_nk {y K : U64} (hy : y ∉ Kp) (h3 : K.val ≠ 3464) (h4 : K.val ≠ 3520) : PrF Kp Nd y K :=
  ⟨fun h => absurd h hy, fun _ => ⟨h3, h4⟩⟩

/-- Discharges a literal offset inequality. -/
macro "xf_ne" : tactic =>
  `(tactic| first | decide | omega | (simp; done) | (simp only [nextOff, prevOff]; decide) | (cases ‹tcbqueue.Link› <;> simp [nextOff, prevOff]; done))

/-- Tries `PrF.of_ne` on literal offsets. -/
macro "xf_auto" : tactic => `(tactic| exact PrF.of_ne (by xf_ne) (by xf_ne) (by xf_ne) (by xf_ne))

theorem notPrW_field {s : S} {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : K.val < 4096)
    (hx : PrF Kp Nd y K) : ¬ PrW st Kp Nd T Cs Scs s (core.num.U64.wrapping_add y K) := by
  rintro (⟨y', hy', hya', hk, e | e⟩ | ⟨hn, ⟨y', hy', hya', e | e⟩ | ⟨c, hc, -, ho⟩⟩)
  · rw [stA_eq] at e
    exact field_ne (hT y hy) hya' hK (by decide) (fun h => by subst h; exact (hx.1 hk).1) e
  · rw [inqA_eq] at e
    exact field_ne (hT y hy) hya' hK (by decide) (fun h => by subst h; exact (hx.1 hk).2) e
  · rw [scA_eq] at e
    exact field_ne (hT y hy) hya' hK (by decide) (fun h => by subst h; exact (hx.2 hn).1) e
  · rw [affA_eq] at e
    exact field_ne (hT y hy) hya' hK (by decide) (fun h => by subst h; exact (hx.2 hn).2) e
  · exact out_ne_field ho hy (hT y hy) hK rfl

theorem notIdW_field {s : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) {y K : U64} (hy : y ∈ T)
    (hK : K.val < 4096) (hx : PrF Kp Nd y K := by xf_auto) :
    ¬ IdW st Kp Nd T Cs Scs s (core.num.U64.wrapping_add y K) := by
  rintro (h | h)
  · obtain ⟨c, hc, o, -, ho, e⟩ := h.lt
    exact node_ne_field (NP c hc) (by omega) hy (hT y hy) hK e.symm
  · exact notPrW_field hT hy hK hx h

theorem notPrW_node {s : S} (NP : ∀ c ∈ Cs, NodePlaced st T s c) {c o : U64} (hc : c ∈ Cs)
    (ho : o.val < 4288) : ¬ PrW st Kp Nd T Cs Scs s (L.nodeAt s c o) := by
  rintro (⟨y', hy', hya', -, e | e⟩ | ⟨-, ⟨y', hy', hya', e | e⟩ | ⟨c', -, -, hout⟩⟩)
  · rw [stA_eq] at e; exact node_ne_field (NP c hc) ho hy' hya' (by decide) e
  · rw [inqA_eq] at e; exact node_ne_field (NP c hc) ho hy' hya' (by decide) e
  · rw [scA_eq] at e; exact node_ne_field (NP c hc) ho hy' hya' (by decide) e
  · rw [affA_eq] at e; exact node_ne_field (NP c hc) ho hy' hya' (by decide) e
  · exact out_ne_node hout hc (NP c hc) ho rfl

theorem notIdW_node {s : S} (NP : ∀ c ∈ Cs, NodePlaced st T s c) {c o : U64} (hc : c ∈ Cs)
    (ho : o.val < 4288) (hn : ¬ IdOff (c = L.cpu s) Nd o.val) : ¬ IdW st Kp Nd T Cs Scs s (L.nodeAt s c o) := by
  rintro (h | h)
  · obtain ⟨c', hc', o', ho', hlt, e⟩ := h.lt
    by_cases hcc : c = c'
    · subst hcc
      by_cases hoo : o.val = o'.val
      · rw [hoo] at hn; exact hn ho'
      · exact node_ne_node (NP c hc) (NP c hc') ho (by omega) (fun _ => hoo) (congrArg UScalar.val e)
    · exact node_ne_node (NP c hc) (NP c' hc') ho (by omega) (fun h => absurd h hcc) (congrArg UScalar.val e)
  · exact notPrW_node NP hc ho h

/-- An SC header word the write must avoid under `Nd`. -/
def NoHdr (Nd : Prop) (Scs : Set U64) (a : U64) : Prop := Nd → ∀ c ∈ Scs, a ≠ scReplyA c ∧ a ≠ scTcbA c

theorem notIdW_out {s : S} (NP : ∀ c ∈ Cs, NodePlaced st T s c) {a : U64} (ha : OutsideObjs st T Cs s a)
    (hh : NoHdr Nd Scs a) : ¬ IdW st Kp Nd T Cs Scs s a := by
  rintro (h | h)
  · obtain ⟨c, hc, o, -, ho, e⟩ := h.lt
    exact out_ne_node ha hc (NP c hc) (by omega) (congrArg UScalar.val e).symm
  · rcases h with ⟨y', hy', hya', -, e | e⟩ | ⟨hn, ⟨y', hy', hya', e | e⟩ | ⟨c, hc, e | e, -⟩⟩
    · rw [stA_eq] at e; exact out_ne_field ha hy' hya' (by decide) (congrArg UScalar.val e).symm
    · rw [inqA_eq] at e; exact out_ne_field ha hy' hya' (by decide) (congrArg UScalar.val e).symm
    · rw [scA_eq] at e; exact out_ne_field ha hy' hya' (by decide) (congrArg UScalar.val e).symm
    · rw [affA_eq] at e; exact out_ne_field ha hy' hya' (by decide) (congrArg UScalar.val e).symm
    · exact (hh hn c hc).1 e
    · exact (hh hn c hc).2 e

theorem NoHdr.of_not {a : U64} (h : ¬ Nd) : NoHdr Nd Scs a := fun hn => absurd hn h

/-- A word outside every SC object is no SC header word. -/
theorem noHdr_outSc {Ω Sg Rp Nt : Set U64} {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {b : U64}
    (hb : ∀ c ∈ Scs, b.val + 8 ≤ c.val ∨ c.val + 2 ^ Z c ≤ b.val) : NoHdr Nd Scs b := by
  intro _ c hc
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have v1 := sc_word_val hP hz (o := layout.sc.REPLY) (by simp [layout.sc.REPLY])
  have v2 := sc_word_val hP hz (o := layout.sc.TCB) (by simp [layout.sc.TCB])
  have r32 : layout.sc.REPLY.val = 32 := by simp [layout.sc.REPLY]
  have t24 : layout.sc.TCB.val = 24 := by simp [layout.sc.TCB]
  have := hb c hc
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have e' := congrArg UScalar.val e; unfold scReplyA at e'; rw [v1, r32] at e'; omega
  · have e' := congrArg UScalar.val e; unfold scTcbA at e'; rw [v2, t24] at e'; omega

/-- A word of SC `i` other than its `TCB` (24) and `REPLY` (32) words is no
SC header word. -/
theorem noHdr_sc {Ω Sg Rp Nt : Set U64} {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {i b : U64} (hi : i ∈ Scs)
    (hb : InSC i (Z i) b) (h24 : b.val ≠ i.val + 24) (h32 : b.val ≠ i.val + 32) : NoHdr Nd Scs b := by
  intro _ c hc
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have v1 := sc_word_val hP hz (o := layout.sc.REPLY) (by simp [layout.sc.REPLY])
  have v2 := sc_word_val hP hz (o := layout.sc.TCB) (by simp [layout.sc.TCB])
  have r32 : layout.sc.REPLY.val = 32 := by simp [layout.sc.REPLY]
  have t24 : layout.sc.TCB.val = 24 := by simp [layout.sc.TCB]
  obtain ⟨hb1, hb2⟩ := hb
  by_cases e : c = i
  · subst e
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have e' := congrArg UScalar.val e; unfold scReplyA at e'; rw [v1, r32] at e'; exact h32 e'
    · have e' := congrArg UScalar.val e; unfold scTcbA at e'; rw [v2, t24] at e'; exact h24 e'
  · have hd := hO.scDisj c hc i hi e
    refine ⟨fun e => ?_, fun e => ?_⟩
    · have e' := congrArg UScalar.val e; unfold scReplyA at e'; rw [v1, r32] at e'; omega
    · have e' := congrArg UScalar.val e; unfold scTcbA at e'; rw [v2, t24] at e'; omega

/-- A reply-object word is no SC header word. -/
theorem noHdr_rp {Ω Sg Rp Nt : Set U64} {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {r b : U64} (hr : r ∈ Rp)
    (h1 : r.val ≤ b.val) (h2 : b.val + 8 ≤ r.val + 32) : NoHdr Nd Scs b :=
  noHdr_outSc hO fun c hc => by have := hO.rpSc r hr c hc; omega

/-- An SC ring word is no SC header word. -/
theorem noHdr_ring {Ω Sg Rp Nt : Set U64} {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {i b : U64} (hi : i ∈ Scs)
    (hb : InRing i (Z i) b) : NoHdr Nd Scs b :=
  noHdr_sc hO hi hb.inSC (by have := hb.1; omega) (by have := hb.1; omega)

theorem footN_wr {s : S} {a v : U64} (ha : Aligned a) (hk : KWN st Kp Nd T Cs Sg Scs Z Es s a)
    (he : L.actionW (L.wr s a v) = L.actionW s) : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s a v) :=
  ((writesIn_wr ha).mono fun b hb => hb ▸ hk).a (AcK.of_eq he)

theorem footN_field {s : S} {y K v : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) (hy : y ∈ T)
    (hK : 192 ≤ K.val) (hK' : K.val < 4096) (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584)
    (hx : PrF Kp Nd y K := by xf_auto) :
    FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  footN_wr (field_aligned (hT y hy) hK' hK8) ⟨kw_field hy hK hK' hKd, notIdW_field hT NP hy hK' hx⟩
    (actionW_field hT NP hc hy hK' hK8)

theorem footN_node {s : S} {c o v : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) (hn : ¬ IdOff (c = L.cpu s) Nd o.val) (hcpu : L.cpu s ∈ Cs)
    (h16 : o.val ≠ 16 := by first | (simp; done) | omega) :
    FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s c o) v) :=
  footN_wr (nodeAt_aligned (NP c hc) ho h8) ⟨kw_node hc ho h88, notIdW_node NP hc ho hn⟩
    (actionW_of (writesIn_wr (nodeAt_aligned (NP c hc) ho h8)) (NP _ hcpu) fun e =>
      node_ne_node (NP _ hcpu) (NP c hc) (by rw [act_val]; omega) ho
        (fun _ => by rw [act_val]; exact fun h => h16 h.symm) (congrArg UScalar.val e))

theorem LawfulStore.QFoot.kwN {s : S} {W : List U64} {c : U64} {P : Nat → Prop} {t b : U64}
    (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hW : ∀ w ∈ W, w ∈ T)
    (hc : c ∈ Cs) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (hP : ∀ o, P o → o ≠ 88)
    (hPi : ∀ o, P o → ¬ IdOff (c = L.cpu s) Nd o) (htK : t ∉ Kp) (h : L.QFoot s W c P t b) :
    KWN st Kp Nd T Cs Sg Scs Z Es s b := by
  refine ⟨h.kw hW hc hcpu ht hP, ?_⟩
  rcases h with ⟨w, hw, e | e⟩ | ⟨o, hPo, ho, -, e⟩ | e | ⟨o, hPo, ho, -, e⟩ <;> subst e
  · rw [nextA_eq']; exact notIdW_field hT NP (hW w hw) (by simp [nextOff])
  · rw [prevA_eq']; exact notIdW_field hT NP (hW w hw) (by simp [prevOff])
  · exact notIdW_node NP hc ho (hPi _ hPo)
  · rw [inqA_eq]; exact notIdW_field hT NP ht (by simp) (PrF.of_nk htK (by simp) (by simp))
  · have h120 : o.val = 120 := hPo
    exact notIdW_node NP hcpu ho (idOff_ge (by omega))

/-- A queue operation keeps the action. -/
theorem LawfulStore.QFoot.act {s s' : S} {W : List U64} {c : U64} {P : Nat → Prop} {t : U64}
    (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hW : ∀ w ∈ W, w ∈ T)
    (hc : c ∈ Cs) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (hP : ∀ o, P o → o ≠ 16)
    (h : WritesIn st s s' (L.QFoot s W c P t)) : L.actionW s' = L.actionW s := by
  refine actionW_of h (NP _ hcpu) ?_
  have hN := NP _ hcpu
  have e16 : layout.node.SCHED_ACTION.val = 16 := act_val
  rintro (⟨w, hw, e | e⟩ | ⟨o, hPo, ho, -, e⟩ | e | ⟨o, hPo, ho, -, e⟩)
  · rw [nextA_eq'] at e
    exact node_ne_field hN (by omega) (hW w hw) (hT w (hW w hw)) (by simp [nextOff]) e
  · rw [prevA_eq'] at e
    exact node_ne_field hN (by omega) (hW w hw) (hT w (hW w hw)) (by simp [prevOff]) e
  · exact node_ne_node hN (NP c hc) (by omega) ho (fun _ => by rw [e16]; exact fun h => hP _ hPo h.symm)
      (congrArg UScalar.val e)
  · rw [inqA_eq] at e; exact node_ne_field hN (by omega) ht (hT t ht) (by simp) e
  · have h120 : o.val = 120 := hPo
    exact node_ne_node hN hN (by omega) ho (fun _ => by omega) (congrArg UScalar.val e)

/-! ## The scheduler-queue operations -/

theorem rTcbA_v (r : U64) : (rTcbA r).val = r.val := by
  unfold rTcbA layout.reply.TCB
  have := r.hBounds
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at this ⊢

section queues
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.enqueue.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (htK : t ∉ Kp) :
    sched.enqueue st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  have hW : ∀ w ∈ t :: Q (L.mem s (affA t)) (L.mem s (prioA t)), w ∈ T := by
    intro w hw
    rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact (hR1.1.rel _ hp).mem w hw
  exact WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => WritesIn.a (hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes hW hc h.cur ht (fun o ho => by omega) (fun o ho => idOff_ge (by omega)) htK hb)
      (AcK.of_eq (LawfulStore.QFoot.act h.tcbs h.nodes hW hc h.cur ht (fun o ho => by omega) hh.1))

theorem sched.dequeue.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (htK : t ∉ Kp) :
    sched.dequeue st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  exact WP.spec_mono (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (h.queued t ht).1) fun s' hh => WritesIn.a (hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes (hR1.1.rel _ hp).mem hc h.cur ht (fun o ho => by omega)
        (fun o ho => idOff_ge (by omega)) htK hb)
      (AcK.of_eq (LawfulStore.QFoot.act h.tcbs h.nodes (hR1.1.rel _ hp).mem hc h.cur ht (fun o ho => by omega) hh.1))

theorem sched.release_remove.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (htK : t ∉ Kp) :
    sched.release_remove st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  exact WP.spec_mono (sched.release_remove.foot s t _ h.tcbs ht (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc)
    (h.released t ht).1) fun s' hh => WritesIn.a (hh.1.mono fun b hb =>
      LawfulStore.QFoot.kwN h.tcbs h.nodes (h.release _ hc).mem hc h.cur ht
        (fun o ho => by unfold RelOffs at ho; omega)
        (fun o ho => idOff_ge (by unfold RelOffs at ho; omega)) htK hb)
      (AcK.of_eq (LawfulStore.QFoot.act h.tcbs h.nodes (h.release _ hc).mem hc h.cur ht
        (fun o ho => by unfold RelOffs at ho; omega) hh.1))

theorem sched.set_action.kwN (s : S) (v : U64) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (hv : v ∈ T → v ∉ Kp) :
    sched.set_action st s v ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e
    have ha := act_aligned (NP _ hc)
    refine WritesIn.a ((writesIn_wr ha).mono fun b hb => hb ▸ ⟨kw_node hc (by rw [act_val]; omega) (by rw [act_val]; omega),
      notIdW_node NP hc (by rw [act_val]; omega)
        (idOff_cur (by rw [act_val]; omega) (by rw [act_val]; omega) (fun _ => by rw [act_val]; omega))⟩) ?_
    have hv' : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) v) = v := by
      unfold LawfulStore.actionW
      rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]
      exact L.mem_wr_same ha
    intro h1 h2
    rw [hv'] at h1 h2
    exact absurd h2 (hv h1)

theorem small_out {v : U64} (hT : TcbPlaced T) (hv : v.val < 4096) : v ∈ T → v ∉ Kp :=
  fun h => absurd h (notT_small hT hv)

theorem sched.schedule_tcb.kwN (s : S) (t : obj.Tcb) (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (hc : L.cpu s ∈ Cs) :
    sched.schedule_tcb st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, e1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 (FootN.refl _)
      · exact sched.set_action.kwN s _ NP hc (small_out hT (by rw [choose_val]; simp))
    · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact (WP.spec_ok _).2 (FootN.refl _)

theorem sched.set_thread_state.kwN (s : S) (t : obj.Tcb) (v : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) (hKt : t ∉ Kp) : sched.set_thread_state st s t v ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) _ t h.tcbs
    (fun c hc => (h.nodes c hc).ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact h.cur)) fun s2 f2 => ?_
  have f1 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact footN_field h.tcbs h.nodes h.cur ht (by simp) (by simp) (by simp) (by simp) (PrF.of_nk hKt (by simp) (by simp))
  exact f1.trans f2

theorem sched.reschedule_required.kwN (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hKa : ActOut st T Kp s) :
    sched.reschedule_required st s ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => FootN st Kp Nd T Cs Sg Scs Z Es s s1 ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact sched.enqueue.kwN s act h hT (by rw [act_post] at hT ⊢; exact hKa hT)
        · exact (WP.spec_ok _).2 (FootN.refl _)
      · exact (WP.spec_ok _).2 (FootN.refl _)
    · exact (WP.spec_ok _).2 (FootN.refl _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  exact WP.spec_mono (sched.set_action.kwN s1 _ (fun c hc => (h.nodes c hc).ksb f1.1)
    (by rw [f1.2.1]; exact h.cur) (small_out h.tcbs (by rw [choose_val]; simp))) fun s2 f2 => f1.trans f2

theorem sched.possible_switch_to.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (htK : t ∉ Kp) (hKa : ActOut st T Kp s) :
    sched.possible_switch_to st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.kwN s t h ht htK
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.kwN s t h ht htK
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h)
      (sched.reschedule_required.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s h hKa)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, f1⟩
    exact WP.spec_mono (sched.enqueue.kwN s1 t h1 ht htK) fun s2 f2 => f1.trans f2
  · exact sched.set_action.kwN s _ h.nodes h.cur (fun _ => htK)

/-- An SC ring word is no node identity word. -/
theorem notIdW_ring {s : S} {i b : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hiS : i ∈ Scs) (hb : Aligned b) (hr : InRing i (Z i) b) :
    ¬ IdW st Kp Nd T Cs Scs s b :=
  notIdW_out h.nodes (h.omega _ (hX.1.scW i hiS b hb hr.inSC)) (noHdr_ring hX.1 hiS hr)

theorem endpoint.unblock_sporadic.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootN.of' w3 (fun b hb hh => ?_) (AcK.of_eq (actionW_of w3 hN' (by
        rintro (hh | e)
        · exact notAct_omega h (hX.1.scW i hiS _ (act_aligned hN') hh.inSC)
        · exact notAct_node hN' hN' (by rw [rp]; omega) (by rw [rp]; omega) e)))
      rcases hh with hh | rfl
      · exact ⟨hh.kw hiS, notIdW_ring h hX hiS hb hh⟩
      · exact ⟨kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega),
          notIdW_node h.nodes h.cur (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))⟩
    · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact (WP.spec_ok _).2 (FootN.refl _)

theorem notification.unblock_sporadic.kwN (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootN.of' w3 (fun b hb hh => ?_) (AcK.of_eq (actionW_of w3 hN' (by
        rintro (hh | e)
        · exact notAct_omega h (hX.1.scW i hiS _ (act_aligned hN') hh.inSC)
        · exact notAct_node hN' hN' (by rw [rp]; omega) (by rw [rp]; omega) e)))
      rcases hh with hh | rfl
      · exact ⟨hh.kw hiS, notIdW_ring h hX hiS hb hh⟩
      · exact ⟨kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega),
          notIdW_node h.nodes h.cur (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))⟩
    · exact (WP.spec_ok _).2 (FootN.refl _)
  · exact (WP.spec_ok _).2 (FootN.refl _)

theorem ipc.reply_unlink.kwN (s : S) (r t : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht : t ∈ T) (hKt : t ∉ Kp) :
    ipc.reply_unlink st s r t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have hm : rTcbA r ∈ Ω := hsub _ (hX.1.tcbW hr)
  have ha := (h.omega _ hm).1
  have h1 := inv_of_free h ((writesIn_wr (v := 0#u64) ha).mono fun b hb => hb ▸ Or.inl hm)
  exact WP.spec_mono (sched.set_thread_state.kwN _ t _ h1 ht hKt) fun s2 f2 =>
    (footN_wr ha ⟨kw_sg (hX.1.tcbW hr), notIdW_out h.nodes (h.omega _ hm)
      (noHdr_rp hX.1 hr (by rw [rTcbA_v]) (by rw [rTcbA_v]; omega))⟩ (actionW_out h.nodes h.cur (h.omega _ hm))).trans f2

end queues

end

end Fl4Proofs.P1
