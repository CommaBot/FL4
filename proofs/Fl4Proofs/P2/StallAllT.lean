/-
P2 (tmofr gen 2): **the P2 stall tops without the transfer premises.**

* **`stallAt.viewsT`**: `stallAt.views` (P2/StallAll) with `stallSeq.entryNT`
  (P2/TmoFrD) in place of `stallSeq.entryN`: the [J] premises `XferOKRS` and
  `XferFootOKC` are gone, with them `RS`, `hRSK`, `hRS0` and `UserOK`. Left:
  `XG`, `TmoCap` [P] (`hcap`) and `stallAt.views`' per-core premises
  (`hown`, `hactK`, `hcurNB`, `hnq` [J], the other cores' `CoreInv`, `hidS`).
* **`stallAt.allT`**: `stallAt.all` (P2/AllCores) with `stallAt.viewsT`:
  from `AllCores`, `XG` and `TmoCap` [P] at the view of `d`.

`stallAt.views` / `stallAt.all` are left as they were (their statements would
change).
-/
import Fl4Proofs.P2.AllCores
import Fl4Proofs.P2.TmoFrD
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {P3Ok : S → Prop} {A : Type _} {ar : machine.Arch A}

/-- **(tmofr gen 2) A remote stall keeps the invariants at every core's view,
no transfer premise** (`stallAt.views` with `stallSeq.entryNT`). Named premise:
`hcap` (`TmoCap` [P]); `hown`, `hactK`, `hcurNB`, `hnq` [J] as in `stallAt.views`. -/
theorem stallAt.viewsT (hA : P0.ArchTotal ar) (d : U64)
    (s : S) (a : A) (h : @EntryInv S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hI : IdleSc st d s) (hG : @XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok s)
    (hcap : @TmoCap S (atCpu st d) (L.atCpu d) Scs Z H Rp Nt s)
    (hC : ∀ c ∈ Cs, c ≠ d → CoreInv st T Cs Scs Z Ac c s)
    (hown : curAt st d s ∉ OtherK st T Cs d s)
    (hactK : actAt st d s ∈ T → actAt st d s ∉ OtherK st T Cs d s)
    (hcurNB : ∀ c ∈ Cs, c ≠ d → ¬ Blocked (L.mem s (stA (curAt st c s))))
    (hnq : curAt st d s ≠ idleAt st d s → (L.mem s (inqA (curAt st d s)) &&& sched.Q_QUEUED) = 0#u64)
    (hidS : L.mem s (stA (idleAt st d s)) = sched.TS_IDLE) :
    stallAt st ar d s a ⦃ s' _ =>
      (∀ c ∈ Cs, @EntryInv S (atCpu st c) (L.atCpu c) T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IdleSc st c s') ∧
      OKeep st T Cs Scs (OtherK st T Cs d s) d s s' ∧ curAt st d s' = idleAt st d s' ∧
      (actAt st d s' = actAt st d s ∨ actAt st d s' = 0#u64) ∧ (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ∧
      L.mem s' (stA (idleAt st d s)) = sched.TS_IDLE ⦄ := by
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
  -- (p2j17) the protected set: the other cores' threads and `d`'s idle thread
  have q0 := h.1.choose_spec.choose_spec
  have hiT : idleAt st d s ∈ T := q0.idleT
  have hKT' : ∀ y ∈ {y | y ∈ OtherK st T Cs d s ∨ y = idleAt st d s}, y ∈ T := by
    rintro y (hy | rfl)
    · exact hKT y hy
    · exact hiT
  have hKB' : ∀ y ∈ {y | y ∈ OtherK st T Cs d s ∨ y = idleAt st d s}, ¬ Blocked (L.mem s (stA y)) := by
    rintro y (hy | rfl) hb
    · exact hKB y hy hb
    · rw [hidS] at hb; exact tsIdle_nb hb
  have hown' : curAt st d s ≠ idleAt st d s →
      curAt st d s ∉ {y | y ∈ OtherK st T Cs d s ∨ y = idleAt st d s} := fun hne hk => hk.elim hown hne
  have hactK' : actAt st d s ∈ T → actAt st d s ∉ {y | y ∈ OtherK st T Cs d s ∨ y = idleAt st d s} :=
    fun hT hk => hk.elim (hactK hT) fun e => by
      have r : Runnable (L.mem s (stA (actAt st d s))) := (q0.actOK hT).1
      rw [e, hidS] at r
      exact tsIdle_nr r
  unfold stallAt
  refine WP.spec_mono (stallSeq.entryNT (st := atCpu st d) (L := L.atCpu d) (T := T) (Ω := Ω) (H := H)
    (Cs := Cs) (Sg := Sg) (Rp := Rp) (Scs := Scs) (Nt := Nt) (Z := Z) (Ac := Ac)
    (Kp := {y | y ∈ OtherK st T Cs d s ∨ y = idleAt st d s}) (P3Ok := P3Ok) hA hKT' s a h hI hG hown' hactK'
    hKB' hnq hcap) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨e', hI', k, hcur, hac⟩ := hh
  have k' : OKeep st T Cs Scs (OtherK st T Cs d s) d s s' :=
    ⟨k.ksb, k.nd, fun y hy => k.kp y (Or.inl hy), fun y hy => k.iq y (Or.inl hy), k.af, k.sc, k.lk⟩
  refine ⟨fun c hc => ?_, k', hcur, hac, fun c hc hne => (keep_words k' hc hne).1,
    (atCpu_mem d s' _).symm.trans ((k.kp (idleAt st d s) (Or.inr rfl)).trans hidS)⟩
  by_cases e : c = d
  · subst e; exact ⟨e', hI'⟩
  · have p := (hC c hc e).keep k' hc e ⟨c, hc, e, Or.inl rfl⟩ fun h => ⟨c, hc, e, Or.inr (Or.inr ⟨rfl, h⟩)⟩
    exact ⟨p.entry (@EntryInv.blkOK S (atCpu st d) (L.atCpu d) _ _ _ _ _ _ _ _ _ _ _ e'), p.isc⟩

/-- **(tmofr gen 2) A remote stall of `d` from `AllCores` ends in `AllCores`,
no transfer premise** (`stallAt.all` with `stallAt.viewsT`). Named premise:
`hcap` (`TmoCap` [P]). -/
theorem stallAt.allT (hA : P0.ArchTotal ar) (d : U64) (hd : d ∈ Cs)
    (s : S) (a : A) (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hG : @XG S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Scs Z P3Ok s)
    (hcap : @TmoCap S (atCpu st d) (L.atCpu d) Scs Z H Rp Nt s) :
    stallAt st ar d s a ⦃ s' _ =>
      AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ curAt st d s' = idleAt st d s' ∧
      (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ⦄ := by
  refine WP.spec_mono (stallAt.viewsT (Ac := Ac) (P3Ok := P3Ok) hA d s a (h.inv d hd).1
    (h.inv d hd).2 hG hcap (fun c hc _ => h.core hc) (h.notK (h.curAff d hd))
    (fun ha => h.notK (h.actAff d hd ha)) (fun c hc _ => h.curNB c hc) (h.nq d hd) (h.idleSt d hd)) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨hinv, k, hcur, hac, hoth, hid⟩ := hh
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
    · rw [e, k.idleAt hd]; exact hid
    · rw [k.idleAt hc, k.kp _ ⟨c, hc, e, Or.inl rfl⟩]; exact h.idleSt c hc

end

end Fl4Proofs.P2.Stall
