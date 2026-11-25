/-
P2 (p2j15, KWN step 8): **`timer::fire`'s core-separated footprint** (`FFoot`),
the frame `FireKeep` (premise `hfk` of `AllCores.sched`) asks for.

`fire` signals bound notifications. A signal may donate the notification's SC
to the woken thread (`maybe_donate_sched_context`), which writes that
thread's `SC` (and, through `migrate_tcb`, `AFFINITY`) word and the SC's `TCB`
word: words `KWN Kp True` protects. So the footprint is

* `FireW Kp Il Ks U s`: `KW` (with the debug-list words `DbgW` and the user
  words `U`) without the node identity and protected words `IdW Kp True`
  (`P2/FootN.lean`: every core's idle words, the other cores' current,
  action and SC words, the executing core's `CUR_THREAD`; the `STATE` and
  `IN_QUEUES` of `Kp`, every thread's `SC`/`AFFINITY`, every SC's
  `REPLY`/`TCB`), **or** a donation word `DonW`: the `SC`/`AFFINITY` of a
  thread outside `Kp` and `Il`, the `TCB` word of an SC outside `Ks`.
* `FFoot` = `WritesA` in `FireW` (so with `AcK`); `refl`/`trans`,
  `FootN.ff`, `FootDN.ff` (every `KWN Kp True` / `FootDN Kp True` lemma of
  `P2/FootN*.lean` is an `FFoot` one).
* With `Kp` the other cores' idle/current/action threads (`OtherK`), `Il`
  every core's idle thread and `Ks` every idle thread's SC (`IlAt`, `KsAt`):
  `locW2_idW` (the words of `LocW2` are `IdW` words), `donW_not` (no donation
  word is a `LocW2` word), **`FFoot.okeep`** (`OKeep2`), `FFoot.cur` (the
  executing core's current thread kept) and **`FireKeep.ofFF`**: an `FFoot`
  footprint of `fire` gives `FireKeep` from `ActOut` and `curW ∉ OtherK` at
  `fire`'s start.
* `schedcontext.donate.ff`: a donation of an unbound SC (`maybe_donate`'s
  case) to a thread outside `Kp`/`Il`, of an SC outside `Ks`, is an `FFoot`.

No premise.
-/
import Fl4Proofs.P2.AllSched
import Fl4Proofs.P2.FootN4
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}
variable {Kp Il Ks : Set U64}

/-- The donation words: the `SC` and `AFFINITY` words of a thread outside
`Kp` and `Il`, the `TCB` word of an SC outside `Ks`. -/
def DonW (T Kp Il Scs Ks : Set U64) (b : U64) : Prop :=
  (∃ y ∈ T, y ∉ Kp ∧ y ∉ Il ∧ (b = scA y ∨ b = affA y)) ∨ (∃ k ∈ Scs, k ∉ Ks ∧ b = scTcbA k)

/-- `timer::fire`'s words (module docstring). -/
def FireW (st : machine.Store S) [L : LawfulStore st] (Kp Il Ks : Set U64) (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es U : Set U64) (s0 : S) (b : U64) : Prop :=
  ((KW st T Cs Sg Scs Z Es s0 b ∨ DbgW st T Cs s0 b ∨ b ∈ U) ∧ ¬ IdW st Kp True T Cs Scs s0 b) ∨
    DonW T Kp Il Scs Ks b

/-- A footprint inside `FireW`, with `AcK`. -/
abbrev FFoot (st : machine.Store S) [L : LawfulStore st] (Kp Il Ks : Set U64) (T Cs Sg Scs : Set U64)
    (Z : U64 → Nat) (Es U : Set U64) (s s' : S) : Prop :=
  WritesA st T Kp s s' (FireW st Kp Il Ks T Cs Sg Scs Z Es U s)

theorem FireW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : FireW st Kp Il Ks T Cs Sg Scs Z Es U s1 b) : FireW st Kp Il Ks T Cs Sg Scs Z Es U s0 b := by
  rcases h with ⟨hw, hn⟩ | hd
  · refine Or.inl ⟨?_, fun hi => hn (hi.ksb hk hc)⟩
    rcases hw with h | h | h
    · exact Or.inl (KW.ksb hk h)
    · exact Or.inr (Or.inl (DbgW.ksb hk h))
    · exact Or.inr (Or.inr h)
  · exact Or.inr hd

theorem FFoot.refl (s : S) : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s := WritesA.refl _ _

theorem FFoot.trans {s₁ s₂ s₃ : S} (h₁ : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s₁ s₂)
    (h₂ : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s₂ s₃) : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s₁ s₃ :=
  WritesA.mono (WritesA.trans h₁ h₂) fun _ hb => Or.elim hb id fun hb => FireW.ksb h₁.1 h₁.2.1 hb

/-- A `KWN Kp True` footprint is an `FFoot` one. -/
theorem FootN.ff {s s' : S} (f : FootN st Kp True T Cs Sg Scs Z Es s s') :
    FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s' :=
  WritesA.mono f fun _ hb => Or.inl ⟨Or.inl hb.1, hb.2⟩

/-- A `FootDN Kp True` footprint is an `FFoot` one. -/
theorem FootDN.ff {s s' : S} (f : FootDN st Kp True T Cs Sg Scs Z Es s s') :
    FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s' :=
  WritesA.mono f fun _ hb => Or.inl ⟨hb.1.elim Or.inl fun h => Or.inr (Or.inl h), hb.2⟩

/-- Every core's idle thread. -/
def IlAt (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) : Set U64 :=
  {y | ∃ c ∈ Cs, y = idleAt st c s}

/-- Every core's idle thread's SC. -/
def KsAt (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (s : S) : Set U64 :=
  {k | ∃ c ∈ Cs, k = L.mem s (scA (idleAt st c s))}

/-- Two SCs' `TCB` and `REPLY` header words differ. -/
theorem tcb_ne_hdr {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c c' : U64} (hc : c ∈ Scs) (hc' : c' ∈ Scs)
    (hne : c ≠ c') : scTcbA c ≠ scReplyA c' ∧ scTcbA c ≠ scTcbA c' := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨hP', hz'⟩ := hO.sc c' hc'
  have ht := scTcbA_val hP hz
  have hr' := scReplyA_val hP' hz'
  have ht' := scTcbA_val hP' hz'
  have h7 : 128 ≤ 2 ^ Z c := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hz)
  have h7' : 128 ≤ 2 ^ Z c' := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hz')
  refine ⟨fun e2 => ?_, fun e2 => ?_⟩
  · have := congrArg UScalar.val e2
    rw [ht, hr'] at this
    rcases hO.scDisj c hc c' hc' hne with d | d <;> omega
  · have := congrArg UScalar.val e2
    rw [ht, ht'] at this
    rcases hO.scDisj c hc c' hc' hne with d | d <;> omega

/-- The four protected TCB words of `LocW2` as fields. -/
theorem locFld {y b : U64} (h : b = stA y ∨ b = inqA y ∨ b = affA y ∨ b = scA y) :
    ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add y K := by
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨3328#u64, by simp, stA_eq y⟩
  · exact ⟨3592#u64, by simp, inqA_eq y⟩
  · exact ⟨3520#u64, by simp, affA_eq y⟩
  · exact ⟨3464#u64, by simp, scA_eq y⟩

/-- **The words of `LocW2` are `IdW (OtherK) True` words.** -/
theorem locW2_idW {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs) {b : U64}
    (hl : LocW2 st T Cs (L.cpu s) s b) : IdW st (OtherK st T Cs (L.cpu s) s) True T Cs Scs s b := by
  have hT := hq.tcbs
  rcases hl with ⟨c, hc, o, ho, e⟩ | ⟨y, hy, e⟩ | ⟨c, hc, e⟩ | ⟨c, hc, e⟩
  · refine Or.inl ⟨c, hc, o, ?_, e⟩
    rcases ho with h8 | h32 | ⟨hne, hh⟩
    · exact Or.inl h8
    · exact Or.inr (Or.inl h32)
    · exact Or.inr (Or.inr (Or.inl ⟨hne, hh⟩))
  · have hyT := hKT y hy
    rcases e with e | e | e | e
    · exact Or.inr (Or.inl ⟨y, hyT, hT y hyT, hy, Or.inl e⟩)
    · exact Or.inr (Or.inl ⟨y, hyT, hT y hyT, hy, Or.inr e⟩)
    · exact Or.inr (Or.inr ⟨trivial, Or.inl ⟨y, hyT, hT y hyT, Or.inr e⟩⟩)
    · exact Or.inr (Or.inr ⟨trivial, Or.inl ⟨y, hyT, hT y hyT, Or.inl e⟩⟩)
  · have hyT := hiT c hc
    rcases e with e | e
    · exact Or.inr (Or.inr ⟨trivial, Or.inl ⟨_, hyT, hT _ hyT, Or.inr e⟩⟩)
    · exact Or.inr (Or.inr ⟨trivial, Or.inl ⟨_, hyT, hT _ hyT, Or.inl e⟩⟩)
  · have hsc := hiS c hc
    obtain ⟨⟨a1, i1⟩, ⟨a2, i2⟩⟩ := sclink_in hO hsc
    rcases e with e | e
    · subst e
      exact Or.inr (Or.inr ⟨trivial, Or.inr ⟨_, hsc, Or.inl rfl, hq.omega _ (hO.scW _ hsc _ a1 i1)⟩⟩)
    · subst e
      exact Or.inr (Or.inr ⟨trivial, Or.inr ⟨_, hsc, Or.inr rfl, hq.omega _ (hO.scW _ hsc _ a2 i2)⟩⟩)

/-- **No donation word is a `LocW2` word.** -/
theorem donW_not {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs) {b : U64}
    (hd : DonW T (OtherK st T Cs (L.cpu s) s) (IlAt st Cs s) Scs (KsAt st Cs s) b)
    (hl : LocW2 st T Cs (L.cpu s) s b) : False := by
  have hT := hq.tcbs
  -- the idle SCs' header words lie outside the objects
  have hidl : ∀ c ∈ Cs, OutsideObjs st T Cs s (scReplyA (L.mem s (scA (idleAt st c s)))) ∧
      OutsideObjs st T Cs s (scTcbA (L.mem s (scA (idleAt st c s)))) := fun c hc => by
    have hsc := hiS c hc
    obtain ⟨⟨a1, i1⟩, ⟨a2, i2⟩⟩ := sclink_in hO hsc
    exact ⟨hq.omega _ (hO.scW _ hsc _ a1 i1), hq.omega _ (hO.scW _ hsc _ a2 i2)⟩
  rcases hd with ⟨y, hyT, hyK, hyI, hby⟩ | ⟨k, hk, hkK, hbk⟩
  · obtain ⟨K, hK, hbK⟩ : ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add y K := by
      rcases hby with rfl | rfl
      · exact ⟨3464#u64, by simp, scA_eq y⟩
      · exact ⟨3520#u64, by simp, affA_eq y⟩
    rcases hl with ⟨c, hc, o, ho, e⟩ | ⟨y', hy', e⟩ | ⟨c, hc, e⟩ | ⟨c, hc, e⟩
    · exact node_ne_field (hq.nodes c hc) (by omega) hyT (hT y hyT) hK (e.symm.trans hbK)
    · obtain ⟨K', hK', e'⟩ := locFld e
      exact field_ne (hT y hyT) (hT y' (hKT y' hy')) hK hK' (fun h => by subst h; exact absurd hy' hyK)
        (hbK.symm.trans e')
    · obtain ⟨K', hK', e'⟩ : ∃ K' : U64, K'.val < 4096 ∧ b = core.num.U64.wrapping_add (idleAt st c s) K' := by
        rcases e with rfl | rfl
        · exact ⟨3520#u64, by simp, affA_eq _⟩
        · exact ⟨3464#u64, by simp, scA_eq _⟩
      exact field_ne (hT y hyT) (hT _ (hiT c hc)) hK hK' (fun h => absurd ⟨c, hc, h⟩ hyI) (hbK.symm.trans e')
    · rcases e with e | e
      · exact out_ne_field (hidl c hc).1 hyT (hT y hyT) hK (congrArg UScalar.val (hbK.symm.trans e))
      · exact out_ne_field (hidl c hc).2 hyT (hT y hyT) hK (congrArg UScalar.val (hbK.symm.trans e))
  · subst hbk
    obtain ⟨-, ⟨a2, i2⟩⟩ := sclink_in hO hk
    have hout : OutsideObjs st T Cs s (scTcbA k) := hq.omega _ (hO.scW _ hk _ a2 i2)
    rcases hl with ⟨c, hc, o, ho, e⟩ | ⟨y', hy', e⟩ | ⟨c, hc, e⟩ | ⟨c, hc, e⟩
    · exact out_ne_node hout hc (hq.nodes c hc) (by omega) (congrArg UScalar.val e.symm)
    · obtain ⟨K', hK', e'⟩ := locFld e
      exact out_ne_field hout (hKT y' hy') (hT y' (hKT y' hy')) hK' (congrArg UScalar.val e'.symm)
    · obtain ⟨K', hK', e'⟩ : ∃ K' : U64, K'.val < 4096 ∧
          scTcbA k = core.num.U64.wrapping_add (idleAt st c s) K' := by
        rcases e with e | e
        · exact ⟨3520#u64, by simp, e.trans (affA_eq _)⟩
        · exact ⟨3464#u64, by simp, e.trans (scA_eq _)⟩
      exact out_ne_field hout (hiT c hc) (hT _ (hiT c hc)) hK' (congrArg UScalar.val e'.symm)
    · have hne : k ≠ L.mem s (scA (idleAt st c s)) := fun h => hkK ⟨c, hc, h⟩
      rcases e with e | e
      · exact (tcb_ne_hdr hO hk (hiS c hc) hne).1 e
      · exact (tcb_ne_hdr hO hk (hiS c hc) hne).2 e

/-- **An `FFoot` footprint over the other cores' threads keeps `LocW2`.** -/
theorem FFoot.okeep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs)
    (f : FFoot st (OtherK st T Cs (L.cpu s) s) (IlAt st Cs s) (KsAt st Cs s) T Cs Sg Scs Z Es U s s') :
    OKeep2 st T Cs (L.cpu s) s s' := by
  refine OKeep2.ofW hq hO hKT hiT hiS f.w fun b hb hl => ?_
  rcases hb with ⟨-, hn⟩ | hd
  · exact hn (locW2_idW hq hO hKT hiT hiS hl)
  · exact donW_not hq hO hKT hiT hiS hd hl

/-- An `FFoot` footprint keeps the executing core's current thread. -/
theorem FFoot.cur {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (f : FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s') :
    L.curW s' = L.curW s := by
  have hN := hq.nodes _ hq.cur
  unfold LawfulStore.curW
  rw [nodeAt_of_ksb f.1, f.2.1]
  refine f.mem_eq (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0])) fun hb => ?_
  rcases hb with ⟨-, hn⟩ | ⟨y, hyT, -, -, hby⟩ | ⟨k, hk, -, hbk⟩
  · exact hn (Or.inl ⟨_, hq.cur, _, Or.inr (Or.inr (Or.inr ⟨trivial, rfl, by rw [curth0]⟩)), rfl⟩)
  · rcases hby with e | e
    · rw [scA_eq] at e
      exact node_ne_field hN (by rw [curth0]; omega) hyT (hq.tcbs y hyT) (by simp) e
    · rw [affA_eq] at e
      exact node_ne_field hN (by rw [curth0]; omega) hyT (hq.tcbs y hyT) (by simp) e
  · obtain ⟨-, ⟨a2, i2⟩⟩ := sclink_in hO hk
    exact out_ne_node (hq.omega _ (hO.scW _ hk _ a2 i2)) hq.cur hN (by rw [curth0]; omega)
      (congrArg UScalar.val hbk)

/-- **An `FFoot` footprint of `fire` gives `FireKeep`**, from `ActOut` and the
current thread outside `OtherK` at `fire`'s start. -/
theorem FireKeep.ofFF {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs)
    (ha : ActOut st T (OtherK st T Cs (L.cpu s) s) s) (hc : L.curW s ∉ OtherK st T Cs (L.cpu s) s)
    (f : FFoot st (OtherK st T Cs (L.cpu s) s) (IlAt st Cs s) (KsAt st Cs s) T Cs Sg Scs Z Es U s s') :
    FireKeep st T Cs (L.cpu s) s s' :=
  ⟨FFoot.okeep hq hO hKT hiT hiS f, f.out ha, by rw [FFoot.cur hq hO f]; exact hc⟩

/-- **A donation of an unbound SC** (`maybe_donate_sched_context`'s case) to a
thread outside `Kp` and `Il`, of an SC outside `Ks`, is an `FFoot`. -/
theorem schedcontext.donate.ff {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S) (a : A) (sc dst : U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (D : DbgTz st T Cs s) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hsc : sc ∈ Scs) (hdst : dst ∈ T) (hcore : L.mem s (scCoreA sc) ∈ Cs)
    (htc0 : L.mem s (scTcbA sc) = 0#u64) (hdK : dst ∉ Kp) (hdI : dst ∉ Il) (hsK : sc ∉ Ks) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s' ⦄ := by
  have hT := h.tcbs
  have hN1 := h.nodes _ h.cur
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = s) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 rfl
    · rename_i hb
      exact absurd (by rw [eb, ei, htc0]; rfl) hb
  rintro ⟨s1, a1⟩ e1
  simp only at e1
  subst e1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (donate_tail.frame hA _ a1 sc dst h D hO hsub hsc hdst hcore) ?_
  rintro ⟨s', a'⟩ ⟨w, -⟩
  try simp only [WP.uncurry'_pair] at w ⊢
  refine (w.mono fun b hb => ?_).a (AcK.of_eq (actionW_of w hN1 ?_))
  · rcases hb with rfl | rfl | rfl | hb
    · exact Or.inr (Or.inr ⟨sc, hsc, hsK, rfl⟩)
    · exact Or.inr (Or.inl ⟨dst, hdst, hdK, hdI, Or.inl rfl⟩)
    · exact Or.inr (Or.inl ⟨dst, hdst, hdK, hdI, Or.inr rfl⟩)
    · exact Or.inl ⟨Or.inr (Or.inl hb), notIdW_dbg h.tcbs h.nodes hb⟩
  · rintro (e | e | e | e)
    · exact notAct_omega h (by rw [e]; exact hsub _ (hO.fixW sc hsc).1)
    · rw [scA_eq] at e; exact node_ne_field hN1 (by rw [act_val]; omega) hdst (hT _ hdst) (by simp) e
    · rw [affA_eq] at e; exact node_ne_field hN1 (by rw [act_val]; omega) hdst (hT _ hdst) (by simp) e
    · exact notDbgW_node h.tcbs h.nodes h.cur (by rw [act_val]; omega) (by rw [act_val]; omega) e

/-- `resume` in `KWN`: a `postpone` of the SC's thread, which is not protected. -/
theorem schedcontext.resume.kwN {Nd : Prop} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (sc : obj.Sc) (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R)
    (hsc : sc ≠ 0#u64 → L.mem s (scTcbA sc) ≠ 0#u64 →
      L.mem s (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s (scCoreA sc) ∧ L.mem s (scCoreA sc) ∈ Cs ∧
        L.mem s (scTcbA sc) ∉ Kp) :
    schedcontext.resume st ar s a sc ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold schedcontext.resume
  step with obj.Sc.is_null.spec as ⟨b, b_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootN.refl _
  rename_i hb
  have hsc0 : sc ≠ 0#u64 := by simpa [b_post] using hb
  step with obj.Sc.tcb.spec as ⟨i, i_post⟩
  step with obj.Tcb.is_null.spec as ⟨b1, b1_post⟩
  split
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootN.refl _
  rename_i hb1
  have hi0 : L.mem s (scTcbA sc) ≠ 0#u64 := by rw [← i_post]; simpa [b1_post] using hb1
  obtain ⟨hiT, hcore, hcs, hK⟩ := hsc hsc0 hi0
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨-, -, hr0, -⟩ := b2_post hb2
    rw [i_post] at hr0
    have post := sched.postpone.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s sc Q R h
      hiT hr0 hcore hcs hK
    step with sporadic.ready.spec as ⟨b3⟩
    split
    · step with sporadic.sufficient.ok (st := st) hA as ⟨b4⟩
      split
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootN.refl _
      · exact WP.spec_bind post fun s1 h1 => by simpa using h1
    · exact WP.spec_bind post fun s1 h1 => by simpa using h1
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootN.refl _

/-- **`maybe_donate_sched_context` in `FFoot`** (P1 `tinvFK`): the donation
of the notification's unbound SC to `t` (outside `Kp`, `Il`; the SC, whose
`TCB` word is null, is outside `Ks` when `Ks`'s SCs are bound), then
`resume`. -/
theorem notification.maybe_donate_sched_context.ff {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64)
    (hta' : L.actionW s ≠ t) (hti : L.idleW s ≠ t)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (htK : t ∉ Kp) (htI : t ∉ Il) (hKs : ∀ k ∈ Ks, L.mem s (scTcbA k) ≠ 0#u64) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s' ⦄ := by
  have ok0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, FFoot.refl _⟩
  unfold notification.maybe_donate_sched_context
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  split
  · rename_i hi
    step with obj.Ntfn.sc.val as ⟨i1, ei1⟩
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · exact ok0
    rename_i hb
    have hi10 : i1 ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with obj.Sc.tcb.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      have htc0 : L.mem s (scTcbA i1) = 0#u64 := by rw [← ei2, hi2]
      obtain ⟨hS1, hcore1, hin1⟩ := hns (by rw [← ei1]; exact hi10) (by rw [← ei1]; exact htc0) (by rw [← ei, hi])
      rw [← ei1] at hS1 hin1 hcore1
      refine WP.spec_bind (WP.spec_and (schedcontext.donate.unbound hA s a i1 t Q R h hB hX hS hSg ht htq htr hS1
        hi10 htc0 hcore1 hin1 (by rw [← ei, hi]) hti)
        (schedcontext.donate.ff (Kp := Kp) (Il := Il) (Ks := Ks) (Es := Es) (U := U) hA s a i1 t h hX.dbg hX.1
          hSg.sub hS1 ht hcore1 htc0 htK htI (fun hk => hKs _ hk htc0))) ?_
      rintro ⟨s4, a4⟩ ⟨⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, -, -, -, sc4, tc4, ea4⟩, f4⟩
      try simp only [WP.uncurry'_pair]
      have hsc : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.mem s4 (scTcbA i1) ∉ Kp := fun _ _ => by
        obtain ⟨-, -, hc4⟩ := hX4.2.2.bound t ht (by rw [sc4]; exact hi10)
        rw [sc4] at hc4
        rw [tc4]
        exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 i1 hS1).2.1, hc4, htK⟩
      have hsc' : i1 ≠ 0#u64 → L.mem s4 (scTcbA i1) ≠ 0#u64 →
          L.mem s4 (scTcbA i1) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA i1) ∧ L.mem s4 (scCoreA i1) ∈ Cs ∧
            L.actionW s4 ≠ L.mem s4 (scTcbA i1) := fun a b => by
        obtain ⟨x1, x2, x3, -⟩ := hsc a b
        exact ⟨x1, x2, x3, by rw [ea4, tc4]; exact hta'⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_mono (WP.spec_and (schedcontext.resume.all hA s4 a4 i1 Q4 R4 h4 hB4 hX4 hSg4 hS4 hsc')
        (schedcontext.resume.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := Es) hA s4 a4 i1 Q4
          R4 h4 hsc)) ?_
      rintro ⟨s5, a5⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩, k5⟩
      exact ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS4.fr f5, hSg5⟩, f4.trans (FootN.ff k5)⟩
    · exact ok0
  · exact ok0

/-- **`signal_tail` in `FFoot`** (P1 `signal_tail.FK`): the woken thread's
badge, the donation, the switch-to and the sporadic unblock. -/
theorem signal_tail.ff {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s2 : S) (a1 : A)
    (dst n badge : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h2 : SchedQueuesInv st T Cs Ω H s2 Q R) (hB2 : BoundInv st T Ac s2) (hX2 : XInv st T Cs Ω Sg Rp Scs Nt Z s2)
    (hS2 : SCsOK st T Ω Sg Scs Z Ac s2) (hSg2 : SgOK st Ω Sg s2) (hd : dst ∈ T) (hn : n ∈ Nt)
    (dq : (L.mem s2 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (dr : (L.mem s2 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (da : L.actionW s2 ≠ dst) (di : L.idleW s2 ≠ dst) (dR : ¬ BlockedR (L.mem s2 (stA dst)))
    (hdK : dst ∉ Kp) (hdI : dst ∉ Il) (hKsS : ∀ k ∈ Ks, k ∈ Scs) (hKs : ∀ k ∈ Ks, L.mem s2 (scTcbA k) ≠ 0#u64)
    (hKa : ActOut st T Kp s2) :
    (do
      let s3 ← obj.Tcb.set_reg st dst s2 layout.reg.BADGE badge
      let (s4, a2) ← notification.maybe_donate_sched_context st ar s3 a1 dst n
      let b1 ← sched.is_schedulable st s4 dst
      let s5 ← if b1 then sched.possible_switch_to st s4 dst else ok s4
      let s6 ← notification.unblock_sporadic st s5 dst
      ok (s6, a2)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
        FFoot st Kp Il Ks T Cs Sg Scs Z Es U s2 s' ⦄ := by
  have hT := h2.tcbs
  have hta := hT dst hd
  have hfa : Aligned (core.num.U64.wrapping_add dst 256#u64) := field_aligned hta (by simp) (by simp)
  have sg3 : ∀ b ∈ Sg, L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) b = L.mem s2 b := fun b hb =>
    L.mem_wr_ne hfa (h2.omega _ (hSg2.sub _ hb)).1 (out_ne_field (h2.omega _ (hSg2.sub _ hb)) hd hta (by simp))
  refine WP.spec_bind (obj.Tcb.set_reg.badge s2 dst badge hta) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, hB3, hX3, hS3, hSg3⟩ := badge_all (v := badge) h2 hB2 hX2 hS2 hSg2 hd
  have F3 : FootN st Kp True T Cs Sg Scs Z Es s2 (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) :=
    footN_field hT h2.nodes h2.cur hd (by simp) (by simp) (by simp) (by simp)
  have iq3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (inqA dst) = L.mem s2 (inqA dst) := by
    rw [inqA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have ea3 : L.actionW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.actionW s2 :=
    act_wr_field (h2.nodes _ h2.cur) hd hta rfl (by simp) (by simp)
  have ei3 : L.idleW (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) = L.idleW s2 := by
    unfold LawfulStore.idleW; rw [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp))
      (nodeAt_aligned (h2.nodes _ h2.cur) (by rw [idle8]; omega) (by rw [idle8]))
      (fun e => node_ne_field (K := 256#u64) (h2.nodes _ h2.cur) (by rw [idle8]; omega) hd hta (by simp)
        (UScalar.eq_of_val_eq e).symm)
  have sc3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = L.mem s2 (scA dst) := by
    rw [scA_eq]
    exact L.mem_wr_ne (field_aligned hta (by simp) (by simp)) (field_aligned hta (by simp) (by simp))
      (fun e => field_ne (K1 := 256#u64) (K2 := 3464#u64) hta hta (by simp) (by simp) (fun _ => by simp)
        (UScalar.eq_of_val_eq e))
  have hsA3 : L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scA dst) = 0#u64 →
      ¬ Sch st (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) dst := fun h0 hS => by
    rw [sc3] at h0
    rcases Sch.wr_field h2 hd (by simp) (by simp) (by simp) hd hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact e dq
    · exact e dr
    · exact da e
    · exact di e
    · exact hB2.resume e1 (by rw [e2]; exact h0)
    · exact dR e
  have hKs3 : ∀ k ∈ Ks, L.mem (L.wr s2 (core.num.U64.wrapping_add dst 256#u64) badge) (scTcbA k) ≠ 0#u64 :=
    fun k hk => by rw [sg3 _ (scSg hX2.1 k (hKsS k hk)).2]; exact hKs k hk
  refine WP.spec_bind (notification.maybe_donate_sched_context.ff (Kp := Kp) (Il := Il) (Ks := Ks) (Es := Es)
    (U := U) hA _ a1 dst n Q R h3 hB3 hX3 hS3 hSg3 hd
    (by rw [iq3]; exact dq) (by rw [iq3]; exact dr) (by rw [ea3]; exact da) (by rw [ei3]; exact di)
    (ntfn_sc_ok hX3 hn hsA3) hdK hdI hKs3) ?_
  rintro ⟨s4, a2⟩ ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, F4⟩
  try simp only [WP.uncurry'_pair]
  have hKa4 : ActOut st T Kp s4 := F4.out (hKa.step (AcK.of_eq ea3))
  step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s5 ∧
      FootN st Kp True T Cs Sg Scs Z Es s4 s5) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s4 dst Q4 R4 h4 hB4 hSg4 hd (hb1 hb).1
        (fun _ => (hS4.act _ (hX4.2.2.bound dst hd (hb1 hb).2.1).1).2 (hb1 hb).2.2.2))
        (sched.possible_switch_to.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := Es) s4 dst h4
          hd hdK hKa4)) fun s5 hh => ?_
      obtain ⟨⟨p5, -, -⟩, k5⟩ := hh
      exact ⟨⟨p5.inv, p5.bnd, hX4.fr p5.fr, hS4.fr p5.fr, hSg4.fr p5.fr⟩, k5⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, FootN.refl _⟩
  rintro s5 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, F5⟩
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s5 dst h5 hB5 hX5 hS5 hSg5 hd)
    (endpoint.unblock_sporadic.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := Es) s5 dst h5
      hX5 hS5 hd)) ?_
  rintro s6 ⟨⟨h6, hB6, hX6, hS6, hSg6, -⟩, F6⟩
  exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h6⟩, hB6, hX6, hS6, hSg6⟩,
    (FootN.ff F3).trans (F4.trans (FootN.ff (F5.trans F6)))⟩

/-- `maybe_donate_sched_context.ff` without the queue/action/idle facts
(P1 `tinvFBK`): with a bound SC nothing is donated. -/
theorem notification.maybe_donate_sched_context.ffB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hns : L.mem s (ntfnScA n) ≠ 0#u64 → L.mem s (scTcbA (L.mem s (ntfnScA n))) = 0#u64 →
      L.mem s (scA t) = 0#u64 → L.mem s (ntfnScA n) ∈ Scs ∧ L.mem s (scCoreA (L.mem s (ntfnScA n))) ∈ Cs ∧
        (Sch st s t → L.mem s (ntfnScA n) ∈ Ac))
    (htK : t ∉ Kp) (htI : t ∉ Il) (hKs : ∀ k ∈ Ks, L.mem s (scTcbA k) ≠ 0#u64) :
    notification.maybe_donate_sched_context st ar s a t n ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s' ⦄ := by
  by_cases h0 : L.mem s (scA t) = 0#u64
  · refine notification.maybe_donate_sched_context.ff hA s a t n Q R h hB hX hS hSg ht ?_ ?_ ?_ ?_ hns htK htI hKs
    · by_contra hq; exact hB.q t ht hq h0
    · by_contra hq; exact hB.r t ht hq h0
    · intro e; exact hB.act (by rw [e]; exact ht) (by rw [e]; exact h0)
    · intro e; exact hB.idle (by rw [e]; exact h0)
  · unfold notification.maybe_donate_sched_context
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    rw [if_neg (by rw [ei]; exact h0)]
    exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩, FFoot.refl _⟩

/-- **`signal_vm` in `FFoot`** (P1 `signal_vmFK`): after the VMEnter
completion, the donation, the switch-to and the sporadic SC's
`unblock_check` (its refill ring and the executing core's `REPROGRAM`). -/
theorem signal_vm.ff {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a : A) (i n : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hiT : i ∈ T) (hn : n ∈ Nt)
    (st1 : L.mem s1 (stA i) = sched.TS_RUNNING)
    (hiK : i ∉ Kp) (hiI : i ∉ Il) (hKsS : ∀ k ∈ Ks, k ∈ Scs) (hKs : ∀ k ∈ Ks, L.mem s1 (scTcbA k) ≠ 0#u64)
    (hKa : ActOut st T Kp s1) :
    (do
      let (s2, a1) ← notification.maybe_donate_sched_context st ar s1 a i n
      let b2 ← sched.is_schedulable st s2 i
      let s3 ← if b2 = true then sched.possible_switch_to st s2 i else ok s2
      let i4 ← obj.Tcb.sc st i s3
      let b3 ← obj.Sc.is_null i4
      if b3 = true then ok (s3, a1)
      else do
        let b4 ← sporadic.sc_active st s3 i4
        if b4 = true then do
          let i5 ← obj.Ntfn.sc st n s3
          if i4 = i5 then do
            let b5 ← sporadic.sc_sporadic st s3 i4
            if b5 = true then do
              let s4 ← sched.cur_sc st s3
              let b6 ← core.cmp.PartialEq.ne.trait_default obj.Sc.Insts.CoreCmpPartialEqSc i4 s4
              if b6 = true then do
                let s5 ← sporadic.unblock_check st s3 i4
                ok (s5, a1)
              else ok (s3, a1)
            else ok (s3, a1)
          else ok (s3, a1)
        else ok (s3, a1)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          FFoot st Kp Il Ks T Cs Sg Scs Z Es U s1 s' ⦄ := by
  obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
  have hsA1 : L.mem s1 (scA i) = 0#u64 → ¬ Sch st s1 i := fun h0 hS => by
    rcases hS with e | e | e | e | ⟨e1, e2⟩ | e
    · exact hB1.q i hiT e h0
    · exact hB1.r i hiT e h0
    · exact hB1.act (by rw [e]; exact hiT) (by rw [e]; exact h0)
    · exact hB1.idle (by rw [e]; exact h0)
    · exact hB1.resume e1 (by rw [e2]; exact h0)
    · rw [st1] at e
      rcases e with e | e
      · exact not_blocked_running e
      · exact running_ne.1 e
  refine WP.spec_bind (notification.maybe_donate_sched_context.ffB (Kp := Kp) (Il := Il) (Ks := Ks) (Es := Es)
    (U := U) hA s1 a i n Q1 R1 q1 hB1 hX1 hS1 hSg1 hiT (ntfn_sc_ok hX1 hn hsA1) hiK hiI hKs) ?_
  rintro ⟨s2, a1⟩ ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, F2⟩
  try simp only [WP.uncurry'_pair]
  have hKa2 : ActOut st T Kp s2 := F2.out hKa
  step with sched.is_schedulable.spec' as ⟨b2, hb2⟩
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧
      FootN st Kp True T Cs Sg Scs Z Es s2 s3) ?_ ?_
  · split
    · rename_i hb
      refine WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s2 i Q2 R2 q2 hB2 hSg2 hiT (hb2 hb).1
        (fun _ => (hS2.act _ (hX2.2.2.bound i hiT (hb2 hb).2.1).1).2 (hb2 hb).2.2.2))
        (sched.possible_switch_to.kwN (Sg := Sg) (Kp := Kp) (Nd := True) (Scs := Scs) (Z := Z) (Es := Es) s2 i q2
          hiT hiK hKa2)) fun s3 hh => ?_
      obtain ⟨⟨p3, -, -⟩, k3⟩ := hh
      exact ⟨⟨p3.inv, p3.bnd, hX2.fr p3.fr, hS2.fr p3.fr, hSg2.fr p3.fr⟩, k3⟩
    · exact (WP.spec_ok _).2 ⟨⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩, FootN.refl _⟩
  rintro s3 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, F3⟩
  have ok3 : (ok (s3, a1) : Result (S × A)) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FFoot st Kp Il Ks T Cs Sg Scs Z Es U s1 s' ⦄ :=
    (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, q3⟩, hB3, hX3, hS3, hSg3⟩, F2.trans (FootN.ff F3)⟩
  step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
  step with obj.Sc.is_null.spec as ⟨b3, _hb3⟩
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
  refine WP.spec_bind (sporadic.sc_active.spec s3 i4) fun b4 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (obj.Ntfn.sc.any s3 n) fun i5 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  step with sporadic.sc_sporadic.spec as ⟨b5, eb5⟩
  refine sig_if _ _ _ _ (fun hb5 => ?_) (fun _ => ok3)
  step with sched.cur_sc.spec as ⟨c4, _⟩
  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  have hi4S : i4 ∈ Scs := (hX3.2.2.bound i hiT (by rw [← ei4]; exact (eb5 hb5).1)).1 |> fun h => by
    rw [← ei4] at h; exact h
  have hiA : i4 ∈ Ac := hS3.spor i4 hi4S (eb5 hb5).2
  have hW : RefillsWF st s3 i4 (Z i4) := hS3.wf hi4S hiA
  have hSCin : SCin st s3 Ω i4 (Z i4) := ⟨hW, hX3.1.scW i4 hi4S⟩
  have hN' := q3.nodes _ q3.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) i4 (Z i4) :=
    hSCin.node_out q3.omega q3.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine WP.spec_bind (WP.spec_and (sporadic.unblock_check.all s3 i i4 q3 hB3 hX3 hS3 hSg3 hiT ei4 (eb5 hb5).1 hiA)
    (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s5 ⟨hh, w5⟩ => ?_
  have hact : L.actionW s5 = L.actionW s3 := by
    refine actionW_of w5 hN' ?_
    rintro (hr | e)
    · exact notAct_omega q3 (hX3.1.scW i4 hi4S _ (act_aligned hN') hr.inSC)
    · exact notAct_node hN' hN' (by rw [rp]; omega) (by rw [rp]; omega) e
  have F5 : FootN st Kp True T Cs Sg Scs Z Es s3 s5 := by
    refine FootN.of' w5 (fun b hb hh => ?_) (AcK.of_eq hact)
    rcases hh with hr | rfl
    · exact ⟨InRing.kw hi4S hr, notIdW_ring q3 hX3 hi4S hb hr⟩
    · exact ⟨kw_node q3.cur (by rw [rp]; omega) (by rw [rp]; omega),
        notIdW_node q3.nodes q3.cur (by rw [rp]; omega)
          (idOff_cur (by rw [rp]; omega) (by rw [rp]; omega) (fun _ => by rw [rp]; omega))⟩
  obtain ⟨q5, hB5, hX5, hS5, hSg5, -⟩ := hh
  exact (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, q5⟩, hB5, hX5, hS5, hSg5⟩, F2.trans (FootN.ff (F3.trans F5))⟩

/-- **The composable frame of `fire`'s pieces** on core `e` from `s0`:
`OKeep2`, no other core's thread made the action, the current thread kept.
Unlike `FFoot` it admits the `StK` step of a remote VMEnter completion
(`RUNNING_VM` to `RUNNING`). -/
structure FK (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (e : U64) (s0 s : S) : Prop where
  keep : OKeep2 st T Cs e s0 s
  ac : AcK st T (OtherK st T Cs e s0) s0 s
  cur : L.curW s = L.curW s0

theorem FK.refl (e : U64) (s : S) : FK st T Cs e s s := ⟨OKeep2.refl e s, AcK.of_eq rfl, rfl⟩

theorem FK.trans {e : U64} {s0 s1 s2 : S} (k1 : FK st T Cs e s0 s1) (k2 : FK st T Cs e s1 s2) :
    FK st T Cs e s0 s2 := by
  have hK := k1.keep.otherK
  have a2 := k2.ac
  rw [hK] at a2
  exact ⟨k1.keep.trans k2.keep, k1.ac.trans a2, k2.cur.trans k1.cur⟩

/-- An `FFoot` footprint over the other cores' threads is an `FK` step. -/
theorem FFoot.fk {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs)
    (f : FFoot st (OtherK st T Cs (L.cpu s) s) (IlAt st Cs s) (KsAt st Cs s) T Cs Sg Scs Z Es U s s') :
    FK st T Cs (L.cpu s) s s' :=
  ⟨FFoot.okeep hq hO hKT hiT hiS f, f.ac, FFoot.cur hq hO f⟩

/-- **`FireKeep` from an `FK` frame of `fire`.** -/
theorem FireKeep.ofFK {e : U64} {s s' : S} (k : FK st T Cs e s s') (ha : ActOut st T (OtherK st T Cs e s) s)
    (hc : L.curW s ∉ OtherK st T Cs e s) : FireKeep st T Cs e s s' :=
  ⟨k.keep, ha.step k.ac, by rw [k.cur]; exact hc⟩

/-! ## The VMEnter completion (`vcpu.report`) as an `FK` step -/

/-- The report's `RepW` words (the thread's registers, the user words) are
`FireW` words. -/
theorem RepW.fireW {s : S} {t b : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (ht : t ∈ T)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (h : RepW t U b) :
    FireW st Kp Il Ks T Cs Sg Scs Z Es U s b := by
  rcases h with ⟨K, h1, h2, -, rfl⟩ | hu
  · exact Or.inl ⟨Or.inl (kw_field ht (by omega) (by omega) ⟨by omega, by omega⟩),
      notIdW_field hT NP ht (by omega) (PrF.of_ne (by omega) (by omega) (by omega) (by omega))⟩
  · refine Or.inl ⟨Or.inr (Or.inr hu), notIdW_out NP (hU b hu).out fun _ c hc => ?_⟩
    obtain ⟨⟨-, i1⟩, ⟨-, i2⟩⟩ := sclink_in hO hc
    exact ⟨fun e => (hU b hu).sc c hc (by rw [e]; exact i1), fun e => (hU b hu).sc c hc (by rw [e]; exact i2)⟩

/-- The report's `RepW` writes are an `FFoot`. -/
theorem RepW.ff {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s1 : S} {t : U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (ht : t ∈ T)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (w : WritesIn st s s1 (RepW t U)) :
    FFoot st Kp Il Ks T Cs Sg Scs Z Es U s s1 := by
  have hN := hq.nodes _ hq.cur
  refine (w.mono fun b hb => RepW.fireW hq.tcbs hq.nodes ht hU hO hb).a (AcK.of_eq (actionW_of w hN ?_))
  rintro (⟨K, h1, h2, -, e⟩ | hu)
  · exact node_ne_field hN (by rw [act_val]; omega) ht (hq.tcbs t ht) (by omega) e
  · exact out_ne_node (hU _ hu).out hq.cur hN (by rw [act_val]; omega) rfl

/-- `set_thread_state` writes the thread's `STATE` word and possibly the
executing core's `SCHED_ACTION` (to `CHOOSE_NEW`). -/
theorem sched.set_thread_state.w2 (s : S) (t : obj.Tcb) (v : U64) (hT : TcbPlaced T)
    (hN : NodePlaced st T s (L.cpu s)) (ht : t ∈ T) :
    sched.set_thread_state st s t v ⦃ s' => WritesIn st s s'
        (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧ L.mem s' (stA t) = v ⦄ := by
  have hta := hT t ht
  have a1 : Aligned (stA t) := by rw [stA_eq]; exact field_aligned hta (by simp) (by simp)
  have w1 : WritesIn st s (L.wr s (stA t) v)
      (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
    (writesIn_wr a1).mono fun b hb => Or.inl hb
  have e1 : L.actionW (L.wr s (stA t) v) = L.actionW s := act_wr_field hN ht hta (stA_eq t) (by simp) (by simp)
  have ok1 : (ok (L.wr s (stA t) v) : Result S) ⦃ s' => WritesIn st s s'
        (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = sched.ACTION_CHOOSE_NEW) ∧ L.mem s' (stA t) = v ⦄ :=
    (WP.spec_ok _).2 ⟨w1, Or.inl e1, L.mem_wr_same a1⟩
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 es1 => ?_
  subst es1
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact ok1
      · refine WP.spec_mono (sched.set_action.spec _ _) fun s' e' => ?_
        subst e'
        have hk1 : L.ksb (L.wr s (stA t) v) = L.ksb s := L.ksb_wr _ _ _
        have hc1 : L.cpu (L.wr s (stA t) v) = L.cpu s := L.cpu_wr _ _ _
        rw [hc1, nodeAt_of_ksb hk1]
        have ha := act_aligned hN
        refine ⟨(w1.trans (writesIn_wr ha)).mono fun b hb => hb.elim id Or.inr, Or.inr ?_, ?_⟩
        · unfold LawfulStore.actionW
          rw [L.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _), hc1, nodeAt_of_ksb hk1]
          exact L.mem_wr_same ha
        · rw [L.mem_wr_ne ha a1 (fun e => node_ne_field (K := 3328#u64) hN (by rw [act_val]; omega) ht hta
            (by simp) (by rw [← stA_eq]; exact UScalar.eq_of_val_eq e))]
          exact L.mem_wr_same a1
    · exact ok1
  · exact ok1

/-- **Writes that miss `LocW2 e s` except one thread's `STATE` word**, runnable
before and after, keep `OKeep2` (its `kp` up to `StK`). -/
theorem OKeep2.ofWst {s s' : S} {F : U64 → Prop} {e t : U64} {X : Set U64} {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs e s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs) (ht : t ∈ T)
    (w : WritesIn st s s' F) (hF : ∀ b, F b → b ≠ stA t → ¬ LocW2 st T Cs e s b)
    (hr : Runnable (L.mem s (stA t))) (hr' : Runnable (L.mem s' (stA t))) : OKeep2 st T Cs e s s' := by
  have hT := hq.tcbs
  have hta := hT t ht
  have keep : ∀ b, LocW2 st T Cs e s b → b ≠ stA t → Aligned b → L.mem s' b = L.mem s b :=
    fun b hb hne al => w.2.2 b al fun hf => hF b hf hne hb
  have fne : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val ≠ 3328 → core.num.U64.wrapping_add y K ≠ stA t :=
    fun y hy K hK hK3 e' => field_ne (hT y hy) hta hK (by simp) (fun _ => by simpa using hK3) (e'.trans (stA_eq t))
  refine ⟨w.1, fun c hc o ho => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun c hc => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · exact keep _ (Or.inl ⟨c, hc, o, ho, rfl⟩)
      (fun e' => node_ne_field (K := 3328#u64) (hq.nodes c hc) (by omega) ht hta (by simp) (e'.trans (stA_eq t)))
      (nodeAt_aligned (hq.nodes c hc) (by omega) (by omega))
  · by_cases hyt : y = t
    · subst hyt; exact Or.inr ⟨hr, hr'⟩
    · refine Or.inl (keep _ (Or.inr (Or.inl ⟨y, hy, Or.inl rfl⟩)) ?_
        (by rw [stA_eq]; exact field_aligned (hT y (hKT y hy)) (by simp) (by simp)))
      intro e'
      rw [stA_eq, stA_eq] at e'
      exact field_ne (hT y (hKT y hy)) hta (by simp) (by simp) (fun h => absurd h hyt) e'
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr (Or.inl rfl)⟩))
      (by rw [inqA_eq]; exact fne y (hKT y hy) _ (by simp) (by simp)) (inqA_aligned (hT y (hKT y hy)))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr (Or.inr (Or.inl rfl))⟩))
      (by rw [affA_eq]; exact fne y (hKT y hy) _ (by simp) (by simp))
      (by rw [affA_eq]; exact field_aligned (hT y (hKT y hy)) (by simp) (by simp))
  · exact keep _ (Or.inr (Or.inl ⟨y, hy, Or.inr (Or.inr (Or.inr rfl))⟩))
      (by rw [scA_eq]; exact fne y (hKT y hy) _ (by simp) (by simp)) (scA_aligned (hT y (hKT y hy)))
  · exact keep _ (Or.inr (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩)))
      (by rw [affA_eq]; exact fne _ (hiT c hc) _ (by simp) (by simp))
      (by rw [affA_eq]; exact field_aligned (hT _ (hiT c hc)) (by simp) (by simp))
  · exact keep _ (Or.inr (Or.inr (Or.inl ⟨c, hc, Or.inr rfl⟩)))
      (by rw [scA_eq]; exact fne _ (hiT c hc) _ (by simp) (by simp)) (scA_aligned (hT _ (hiT c hc)))
  · have hsc := hiS c hc
    obtain ⟨⟨a1, i1⟩, ⟨a2, i2⟩⟩ := sclink_in hO hsc
    have o1 := hq.omega _ (hO.scW _ hsc _ a1 i1)
    have o2 := hq.omega _ (hO.scW _ hsc _ a2 i2)
    exact ⟨keep _ (Or.inr (Or.inr (Or.inr ⟨c, hc, Or.inl rfl⟩)))
        (fun e' => out_ne_field (K := 3328#u64) o1 ht hta (by simp) (by rw [← stA_eq, e'])) a1,
      keep _ (Or.inr (Or.inr (Or.inr ⟨c, hc, Or.inr rfl⟩)))
        (fun e' => out_ne_field (K := 3328#u64) o2 ht hta (by simp) (by rw [← stA_eq, e'])) a2⟩

/-- **`set_thread_state` between runnable states is an `FK` step**, also for
another core's thread (its `STATE` up to `StK`). -/
theorem sched.set_thread_state.fk {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t v : U64) (hq : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs) (ht : t ∈ T)
    (hr : Runnable (L.mem s (stA t))) (hv : Runnable v) :
    sched.set_thread_state st s t v ⦃ s' => FK st T Cs (L.cpu s) s s' ⦄ := by
  have hN := hq.nodes _ hq.cur
  have hT := hq.tcbs
  refine WP.spec_mono (sched.set_thread_state.w2 s t v hT hN ht) fun s' ⟨w, ha, hst⟩ => ?_
  have hna : ¬ LocW2 st T Cs (L.cpu s) s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := fun hl =>
    notIdW_node hq.nodes hq.cur (by rw [act_val]; omega)
      (idOff_cur (by rw [act_val]; omega) (by rw [act_val]; omega) (fun _ => by rw [act_val]; omega))
      (locW2_idW hq hO hKT hiT hiS hl)
  refine ⟨OKeep2.ofWst hq hO hKT hiT hiS ht w
    (fun b hb hne => hb.elim (fun e => absurd e hne) (fun e => by rw [e]; exact hna)) hr (by rw [hst]; exact hv),
    ?_, ?_⟩
  · rcases ha with e | e
    · exact AcK.of_eq e
    · exact AcK.of_nT (by rw [e, choose_val]; exact notT_small hT (by simp))
  · have hc0 : (layout.node.CUR_THREAD).val < 4288 := by rw [curth0]; omega
    unfold LawfulStore.curW
    rw [nodeAt_of_ksb w.1, w.2.1]
    refine w.mem_eq (nodeAt_aligned hN hc0 (by rw [curth0])) ?_
    rintro (e | e)
    · exact node_ne_field (K := 3328#u64) hN hc0 ht (hT t ht) (by simp) (e.trans (stA_eq t))
    · exact nodeAt_ne hN hc0 (by rw [act_val]; omega) (by rw [curth0, act_val]; omega) e

/-- **`vcpu.report` of a `TS_RUNNING_VM` thread (`signal_completes`) is an
`FK` step**, also when the thread is another core's (P1 `vcpu.report.xf`: its
`RepW` writes are an `FFoot`, then `set_thread_state TS_RUNNING`, both states
runnable). -/
theorem vcpu.report.fk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t badge : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hvm : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (hc : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add t 3664#u64)) vcpu.PENDING) = 0#u64)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true t ⦃ b => BufOK U b ⦄)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs) :
    vcpu.report st ar s a t badge ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      L.mem s' (stA t) = sched.TS_RUNNING ∧ FK st T Cs (L.cpu s) s s' ⦄ := by
  have h0 := h
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := h0
  refine WP.spec_mono (WP.spec_and (vcpu.report.xf hA s a t badge h ht hvm hc hU hbuf)
    (vcpu.report.blk hA s a t badge h ht hvm hc hU hbuf)) ?_
  rintro s' ⟨⟨s1, h1, st1, w1, e⟩, hb', st'⟩
  have K1 : FK st T Cs (L.cpu s) s s1 :=
    FFoot.fk hq hX.1 hKT hiT hiS (RepW.ff (Es := ∅) (U := U) hq hX.1 ht hU w1)
  obtain ⟨⟨Q1, R1, hq1⟩, -, hX1, -, -⟩ := h1
  have hcpu : L.cpu s1 = L.cpu s := w1.2.1
  have hK1 : OtherK st T Cs (L.cpu s1) s1 = OtherK st T Cs (L.cpu s) s := by rw [hcpu]; exact K1.keep.otherK
  have K2 := sched.set_thread_state.fk s1 t sched.TS_RUNNING hq1 hX1.1
    (fun y hy => by rw [hK1] at hy; exact hKT y hy) (fun c hc => by rw [K1.keep.idle_eq hc]; exact hiT c hc)
    (fun c hc => by rw [K1.keep.idle_eq hc, K1.keep.isc c hc]; exact hiS c hc) ht
    (by rw [st1]; exact Or.inr (Or.inr rfl)) (Or.inl rfl)
  rw [e, WP.spec_ok, hcpu] at K2
  exact ⟨hb', st', K1.trans K2⟩

/-! ## `cancel_ipc` of a receive-blocked thread, in `KWN` -/

/-- `set_thread_state.kwN` from the placement only. -/
theorem sched.set_thread_state.kwNP {Nd : Prop} (s : S) (t : obj.Tcb) (v : U64) (hT : TcbPlaced T)
    (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs) (ht : t ∈ T) (hKt : t ∉ Kp) :
    sched.set_thread_state st s t v ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) _ t hT
    (fun c hc => (NP c hc).ksb (L.ksb_wr _ _ _)) (by rw [LawfulStore.cpu_wr]; exact hc)) fun s2 f2 => ?_
  have f1 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact footN_field hT NP hc ht (by simp) (by simp) (by simp) (by simp) (PrF.of_nk hKt (by simp) (by simp))
  exact f1.trans f2

/-- `reply_unlink.kwN` from `ObjsOK` (no `XInv`). -/
theorem ipc.reply_unlink.kwNO {Nd : Prop} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (r t : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht : t ∈ T) (hKt : t ∉ Kp) :
    ipc.reply_unlink st s r t ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have hm : rTcbA r ∈ Ω := hsub _ (hO.tcbW hr)
  have ha := (h.omega _ hm).1
  have h1 := inv_of_free h ((writesIn_wr (v := 0#u64) ha).mono fun b hb => hb ▸ Or.inl hm)
  exact WP.spec_mono (sched.set_thread_state.kwN _ t _ h1 ht hKt) fun s2 f2 =>
    (footN_wr ha ⟨kw_sg (hO.tcbW hr), notIdW_out h.nodes (h.omega _ hm)
      (noHdr_rp hO hr (by rw [rTcbA_v]) (by rw [rTcbA_v]; omega))⟩ (actionW_out h.nodes h.cur (h.omega _ hm))).trans f2

/-- **`cancel_ipc` of a receive-blocked thread outside `Kp`, in `KWN`**
(`clear_fault`, the endpoint dequeue, `reply_unlink`, `TS_INACTIVE`). -/
theorem ipc.cancel_ipc.kwNR {Nd : Prop} {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    {Q : U64 → U64 → List U64} {R : U64 → List U64} (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hst : L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV)
    (hrecv : L.mem s (replyA t) ≠ 0#u64 → L.mem s (replyA t) ∈ Rp) (hKt : t ∉ Kp) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  unfold ipc.cancel_ipc
  refine WP.spec_bind (WP.spec_and (faults.clear_fault.inv s t Q R h ht hO hsub)
    (WP.spec_mono (obj.Tcb.set_fault_type.spec s t _) fun s' e => e)) ?_
  rintro s1 ⟨⟨h1, f1, -, -, -⟩, e1⟩
  have F1 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s s1 := by
    rw [e1]; exact footN_field (K := 3376#u64) hT h.nodes h.cur ht (by simp) (by simp) (by simp) (by simp)
  have st1 : L.mem s1 (stA t) = sched.TS_BLOCKED_ON_RECV := by
    rw [stA_eq, f1 t ht _ (by simp) (by simp) (fun _ => by simp), ← stA_eq]; exact hst
  have rp1 : L.mem s1 (replyA t) = L.mem s (replyA t) := f1 t ht _ (by simp) (by simp) (fun _ => by simp)
  have hb : Blocked (L.mem s1 (stA t)) := by rw [st1]; exact Or.inr (Or.inl rfl)
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · rename_i hsd
    rw [ev, st1] at hsd
    exact absurd hsd (by unfold sched.TS_BLOCKED_ON_RECV sched.TS_BLOCKED_ON_SEND; decide)
  split
  · rename_i _ hrv
    step with obj.Tcb.block_obj.spec as ⟨ep, ep_post⟩
    subst ep_post
    obtain ⟨E, EQ, hEW⟩ := h1.eps
    obtain ⟨he, hmem⟩ := hEW.2.2.2.2.1 t ht (by simp) hb
    obtain ⟨hE, hEN, hq⟩ := hEW.1 _ he
    have hH : L.mem s1 (blockA t) ∈ EH H := (hEW.2.2.2.2.2.2.2.1 _).1 he
    refine WP.spec_bind (WP.spec_and (endpoint.ep_dequeue.inv s1 t Q R h1 ht (by simp) hb)
      (endpoint.ep_dequeue.foot s1 _ t _ hT hE hq hmem)) ?_
    rintro s2 ⟨⟨h2, f2, -⟩, w2⟩
    have F2 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 :=
      FootN.of' w2 (fun b _ hb => EpFoot.kwN hT h1.nodes hq.mem hH hE hEN (hEW.2.2.1 _ he) (hdrΩ_of hX hsub) hb)
        (AcK.of_eq (EpFoot.act hT h1.nodes h1.cur hq.mem hE hEN w2))
    step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
    refine WP.spec_bind (Pₘ := fun s3 => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s3) ?_ ?_
    · split
      · rename_i hi
        have hi0 : i ≠ 0#u64 := by simpa using hi
        have rp2 : L.mem s2 (replyA t) = L.mem s (replyA t) :=
          (f2 t ht _ (by simp) (by simp) (by simp) (by simp)).trans rp1
        have hiR : i ∈ Rp := by rw [ei, rp2]; exact hrecv (by rw [← rp2, ← ei]; exact hi0)
        exact WP.spec_mono (ipc.reply_unlink.kwNO (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s2 i t h2 hO.ksb hsub hiR ht hKt) fun s3 f3 => F1.trans (F2.trans f3)
      · exact (WP.spec_ok _).2 (F1.trans F2)
    intro s3 f3
    refine WP.spec_bind (sched.set_thread_state.kwNP (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ hT (fun c hc => (h.nodes c hc).ksb f3.1)
      (by rw [f3.2.1]; exact h.cur) ht hKt) fun s4 f4 => ?_
    exact (WP.spec_ok _).2 (f3.trans f4)
  · rename_i _ hnr
    exact absurd (ev.trans st1) hnr

end

end Fl4Proofs.P2.Stall
