/-
P2 (p2j14): **`schedule` closes an entry on the executing core:
`AllCores → AllCores`** (an `AllCores.step2` instance for every entry, since
every entry ends in `schedule`).

* `OKeep2.ofSN`: an `SFootN` footprint protecting the other cores' idle,
  current and action threads (`Kp = OtherK e s`) keeps the words of `LocW2`.
* `KpAff.ofKeep`: from `AllCores` at the entry's start and `OKeep2` up to a
  state on the same core, the other cores' threads have other affinities.
* **`AllCores.sched`**: from `AllCores s0`, an entry body `s0 → s` on core
  `e = L.cpu s0` that keeps `LocW2` (`kb`, `OKeep2 e s0 s`) and ends in P1's
  `BlkOK`, `schedule` from `s` ends in `AllCores`.

Named premises of `AllCores.sched` (the parts of `schedule` this module does
not lift to the core-separated footprint, `timer::fire` and the release loop
of `awaken`):
* `hfk` [J] (`FireKeep`): `timer::fire` keeps `LocW2`, and at its end the
  executing core's action thread and current thread are none of the other
  cores' threads (`ActOut`, `curW ∉ OtherK`). `fire` signals bound
  notifications; P1 proves only its `KW` footprint (`FootDU`), and a signal
  may donate an SC (`maybe_donate_sched_context`) or migrate a waiter, so
  its lift is the notification analogue of `FootN5`'s `send_ipc.footN`.
* `hE` [J] (`SchPre` at the end of `awaken`): with action `RESUME` the current
  thread is `SchCur`; an action thread and the idle thread have affinity the
  executing core.
* `hS0` [W] (as `AllCores.step2`).

Open internal obligations (p2j16, not premises: discharged later in this
development):
* `hidl`: the entry body ends with the executing core's idle thread still
  `TS_IDLE` (an end fact each entry supplies, as `kb`);
* `hsI`: `schedule` keeps the executing core's idle thread `TS_IDLE` (to be
  proved from `hidl`: `fire` over `OtherK ∪ {idle}`, then the rest of
  `schedule` with `KpAff` widened to non-runnable protected threads).
-/
import Fl4Proofs.P2.AllKeep
import Fl4Proofs.P2.FootN7
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **An `SFootN` footprint over the other cores' threads keeps `LocW2`.** -/
theorem OKeep2.ofSN {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hKT : ∀ y ∈ OtherK st T Cs (L.cpu s) s, y ∈ T) (hiT : ∀ c ∈ Cs, idleAt st c s ∈ T)
    (hiS : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ∈ Scs)
    (f : SFootN st (OtherK st T Cs (L.cpu s) s) T Cs Sg Scs Z H s s') : OKeep2 st T Cs (L.cpu s) s s' := by
  refine OKeep2.ofW hq hO hKT hiT hiS f.w fun b hb hl => ?_
  have hT := hq.tcbs
  rcases hl with ⟨c, hc, o, ho, e⟩ | ⟨y, hy, e⟩ | ⟨c, hc, e⟩ | ⟨c, hc, e⟩
  · refine hb.2.1 ⟨c, hc, o, ?_, e⟩
    rcases ho with h8 | h32 | ⟨hne, hh⟩
    · exact Or.inl h8
    · exact Or.inr (Or.inl h32)
    · exact Or.inr (Or.inr (Or.inl ⟨hne, hh⟩))
  · have hyT := hKT y hy
    rcases e with e | e | e | e
    · exact hb.2.2 (Or.inl ⟨y, hyT, hT y hyT, hy, Or.inl e⟩)
    · exact hb.2.2 (Or.inl ⟨y, hyT, hT y hyT, hy, Or.inr e⟩)
    · exact hb.2.2 (Or.inr ⟨trivial, Or.inl ⟨y, hyT, hT y hyT, Or.inr e⟩⟩)
    · exact hb.2.2 (Or.inr ⟨trivial, Or.inl ⟨y, hyT, hT y hyT, Or.inl e⟩⟩)
  · have hyT := hiT c hc
    rcases e with e | e
    · exact hb.2.2 (Or.inr ⟨trivial, Or.inl ⟨_, hyT, hT _ hyT, Or.inr e⟩⟩)
    · exact hb.2.2 (Or.inr ⟨trivial, Or.inl ⟨_, hyT, hT _ hyT, Or.inl e⟩⟩)
  · have hsc := hiS c hc
    obtain ⟨⟨a1, i1⟩, ⟨a2, i2⟩⟩ := sclink_in hO hsc
    rcases e with e | e
    · subst e
      exact hb.2.2 (Or.inr ⟨trivial, Or.inr ⟨_, hsc, Or.inl rfl, hq.omega _ (hO.scW _ hsc _ a1 i1)⟩⟩)
    · subst e
      exact hb.2.2 (Or.inr ⟨trivial, Or.inr ⟨_, hsc, Or.inr rfl, hq.omega _ (hO.scW _ hsc _ a2 i2)⟩⟩)

/-- The other cores' threads have other affinities, along `OKeep2`. -/
theorem KpAff.ofKeep {s0 s : S} (h : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (k : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0) :
    KpAff st T (OtherK st T Cs (L.cpu s0) s0) s := fun y hy => by
  refine ⟨h.KT y hy, ?_⟩
  rw [k.af y hy, hc]
  obtain ⟨c, hc', hne, hh⟩ := hy
  rcases hh with rfl | rfl | ⟨rfl, hT⟩
  · rw [h.idleAff c hc']; exact hne
  · rw [h.curAff c hc']; exact hne
  · rw [h.actAff c hc' hT]; exact hne

/-- What `timer::fire` must keep on core `e` (premise `hfk` of `AllCores.sched`). -/
def FireKeep (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (e : U64) (s s1 : S) : Prop :=
  OKeep2 st T Cs e s s1 ∧ ActOut st T (OtherK st T Cs e s) s1 ∧ L.curW s1 ∉ OtherK st T Cs e s

/-- **`schedule` closes an entry: `AllCores → AllCores`.** Named premises:
`hfk` [J] (`FireKeep` at the end of `timer::fire`), `hE` [J] (`SchPre` at
the end of `awaken`), `hS0` [W]. -/
theorem AllCores.sched {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (kb : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hfk : ∀ rf : S × A, timer.fire st ar s a = ok rf → FireKeep st T Cs (L.cpu s0) s rf.1)
    (hE : ∀ r : S × A, sched.awaken st ar s a = ok r → SchPre st T r.1)
    (hidl : L.mem s (stA (L.idleW s)) = sched.TS_IDLE)
    (hsI : sched.schedule st ar s a ⦃ s' _ => L.mem s' (stA (L.idleW s')) = sched.TS_IDLE ⦄) :
    sched.schedule st ar s a ⦃ s' _ => AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := h
  set e := L.cpu s0 with he
  have hF : ∀ rf : S × A, timer.fire st ar s a = ok rf →
      KpAff st T (OtherK st T Cs e s0) rf.1 ∧ ActOut st T (OtherK st T Cs e s0) rf.1 ∧
        L.curW rf.1 ∉ OtherK st T Cs e s0 := fun rf hrf => by
    obtain ⟨k1, hac, hcu⟩ := hfk rf hrf
    have hKs : OtherK st T Cs e s = OtherK st T Cs e s0 := kb.otherK
    rw [hKs] at hac hcu
    have w := (WP.spec_ok _).1 (hrf ▸ timer.fire.tinvF hA IK hNt s a ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA)
    exact ⟨KpAff.ofKeep h0 hcpu (kb.trans k1) (w.2.2.1.trans hc), hac, hcu⟩
  refine WP.spec_mono (WP.spec_and (WP.spec_and (sched.schedule.sN (Kp := OtherK st T Cs e s0) hA IK hNt s a
      ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA hF)
    (WP.spec_and (sched.schedule.cur hA IK hNt s a ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA hE)
      (WP.spec_and (sched.schedule.entry hA IK hNt s a Q R hq hB hS hX hSg hBA)
        (sched.schedule.tinv hA IK hNt s a Q R hq hB hS hX hSg hBA)))) hsI) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨⟨rf, hrf, Fd, F⟩, C, hen, -, -, -, -, -, -, ha0, -⟩, hsi⟩ := hh
  have w := (WP.spec_ok _).1 (hrf ▸ timer.fire.tinvF hA IK hNt s a ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA)
  obtain ⟨⟨⟨Q1, R1, h1⟩, -, hX1, -, -⟩, Fd'⟩ := w
  obtain ⟨k1, -, -⟩ := hfk rf hrf
  have k01 := kb.trans k1
  have hc1 : L.cpu rf.1 = e := Fd'.2.1.trans hc
  -- the footprint after `fire`, over the other cores' threads at `rf.1`
  have hK : OtherK st T Cs e s0 = OtherK st T Cs (L.cpu rf.1) rf.1 := by rw [hc1, k01.otherK]
  rw [hK] at F
  have k2 : OKeep2 st T Cs (L.cpu rf.1) rf.1 s' := by
    refine OKeep2.ofSN h1 hX1.1 (fun y hy => ?_) (fun c hc' => ?_) (fun c hc' => ?_) F
    · rw [← hK] at hy; exact h0.KT y hy
    · rw [k01.idle_eq hc']; exact (h0.core hc').per.idleT
    · rw [k01.idle_eq hc']
      exact (hX1.2.2.bound (idleAt st c s0) (h0.core hc').per.idleT
        (by rw [k01.isc c hc']; exact (h0.core hc').per.idle)).1
  rw [hc1] at k2
  have hc' : L.cpu s' = L.cpu s0 := F.2.1.trans hc1
  have ec : curAt st (L.cpu s0) s' = L.curW s' := by rw [← hc']; rfl
  have ea : actAt st (L.cpu s0) s' = L.actionW s' := by rw [← hc']; rfl
  have ei : idleAt st (L.cpu s0) s' = L.idleW s' := by rw [← hc']; rfl
  refine AllCores.step2 h0 hcpu (k01.trans k2) hS0 hen hc' ?_ ?_ ?_ ?_ ?_ ?_
  · rw [ec, C.aff, hc']
  · intro hT; rw [ea, ha0] at hT
    obtain ⟨⟨Q', R', hq'⟩, -⟩ := hen
    exact absurd hT (notT_small hq'.tcbs (by simp))
  · rw [ec]; exact C.nb
  · rw [ec, ei]; exact C.nq
  · rw [ea, ha0]
    obtain ⟨⟨Q', R', hq'⟩, -⟩ := hen
    exact notT_small hq'.tcbs (by simp)
  · rw [ei]; exact hsi

end

end Fl4Proofs.P2.Stall
