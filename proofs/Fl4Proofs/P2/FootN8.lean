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

end

end Fl4Proofs.P2.Stall
