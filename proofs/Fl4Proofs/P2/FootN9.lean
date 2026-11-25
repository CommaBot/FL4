/-
P2 (p2j17, KWN step 9): **`timer::fire` as an `FKI` step, and `hfk`
discharged.**

* `TW.kwN` / `TW.fn`: the timer words (`TW`: a TCB's timer fields
  3528..3575, a node's offsets 104/112) are `KWN` words, so `timer.remove`'s
  footprint is a `FootN` one for any protected set.
* `timer.fire_loop.fki`, `timer.fire.fki`: with P1's loop invariant (`TInv`,
  `FootDU`, `IbFr`) the loop carries `FKI` (the other cores' threads and the
  executing core's idle thread kept, `P2/FootN8.lean`) and `FCtx`: each
  iteration is `timer.remove` (`TW.fn`), `send_signal` (`send_signal.fk`) and
  the `REPROGRAM` node write (`footN_node`).
* `AllCores.notKs`: a thread of affinity `e` after an `OKeep2` frame from an
  `AllCores` state is none of the other cores' threads.
* `FCtx.ofAll`: `FCtx` at an entry body's end from `AllCores` at its start,
  `OKeep2`, `BlkOK`, the executing core's idle thread `TS_IDLE` (`hidl`) and
  `ActOut`.
* **`AllCores.schedF`**: `AllCores.sched` with `hfk` discharged
  (`FireKeep.ofFK`). Its entry end facts (supplied by each entry, as `kb` and
  `hidl`; not premises of the development): `hao` (`ActOut`: the executing
  core's action is none of the other cores' threads) and `hcK` (the current
  thread is none of them; `AllCores.notKs` gives it from the current thread's
  affinity being the executing core), and `hidl`. `hsI` is discharged by
  `sched.schedule.idl` (`schedule.sN` over `KI`, with `KpAff` widened in
  `P2/FootN6.lean` to non-runnable protected threads). Remaining hypotheses:
  `hE` [J], `hS0` [W].
-/
import Fl4Proofs.P2.FootN8
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}
variable {Kp : Set U64} {Nd : Prop}

/-- The timer words are `KWN` words. -/
theorem TW.kwN {s : S} {b : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (h : TW st T Cs s b) : KWN st Kp Nd T Cs Sg Scs Z Es s b := by
  rcases h with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩
  · exact ⟨kw_field hy (by omega) (by omega) ⟨by omega, by omega⟩,
      notIdW_field hT NP hy (by omega) (PrF.of_ne (by omega) (by omega) (by omega) (by omega))⟩
  · exact ⟨kw_node hc (by omega) (by omega), notIdW_node NP hc (by omega) (idOff_ge (by omega))⟩

/-- **A footprint in the timer words is a `FootN` one.** -/
theorem TW.fn {s s' : S} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hc : L.cpu s ∈ Cs)
    (w : WritesIn st s s' (TW st T Cs s)) : FootN st Kp Nd T Cs Sg Scs Z Es s s' := by
  refine FootN.of' w (fun b _ hb => TW.kwN hT NP hb) (AcK.of_eq (actionW_of w (NP _ hc) ?_))
  rintro (⟨y, hy, K, h1, h2, e⟩ | ⟨c, hc', o, ho, e⟩)
  · exact node_ne_field (NP _ hc) (by rw [act_val]; omega) hy (hT y hy) (by omega) e
  · exact node_ne_node (NP _ hc) (NP c hc') (by rw [act_val]; omega) (by omega)
      (fun _ => by rw [act_val]; omega) (congrArg UScalar.val e)

/-- **`timer::fire`'s loop is an `FKI` step** (P1 `timer.fire_loop.tinvF`). -/
theorem timer.fire_loop.fki {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (c0 : FCtx st T Cs Scs (L.cpu s) s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => FKI st T Cs (L.cpu s) s s' ⦄ := by
  obtain ⟨IKr, IKs, IKp⟩ := IK T Cs Ω H Sg Rp Scs Nt Z Ac U
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ FKI st T Cs (L.cpu s) s r.1 ∧
      FCtx st T Cs Scs (L.cpu s) r.1) ?_ fun r hr => by obtain ⟨s', a'⟩ := r; exact hr.2.2.2.1
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootDU st T Cs Sg Scs Z (EH H) U s x.1 ∧
      IbFr (L := L) T s x.1 ∧ FKI st T Cs (L.cpu s) s x.1 ∧ FCtx st T Cs Scs (L.cpu s) x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, F1, f1, K1, c1⟩
    simp only at h1 F1 f1 K1 c1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1, c1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hI1, F1, f1, K1, c1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (timer.remove.tf (s0 := s1) s1 t (TF.start hI1) htT) (IKr s1 t hI1 htT)) ?_
      rintro s2 ⟨⟨h2, f2, -, -, w2⟩, g2⟩
      have F2 : FootDU st T Cs Sg Scs Z (EH H) U s s2 := F1.trans (FootD.u (Foot.d (f2.mono (Set.empty_subset _))))
      have f12 := f1.trans g2
      have N2 : FootN st (KI st T Cs (L.cpu s) s1) True T Cs Sg Scs Z ∅ s1 s2 :=
        TW.fn h1q.tcbs h1q.nodes h1q.cur w2
      have K12 : FKI st T Cs (L.cpu s) s1 s2 := c1.fkiN h1q hX1.1 N2
      have c2 := c1.step K12 N2.2.1
      have K2 := K1.trans c1.he K12
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ FKI st T Cs (L.cpu s) s r.1 ∧
          FCtx st T Cs Scs (L.cpu s) r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          have c2' : FCtx st T Cs Scs (L.cpu s2) s2 := by rw [c2.cpu]; exact c2
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2)
            (IKs s2 a1 n bd h2 hn (hNt n hn) hb2))
            (notification.send_signal.fk hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2 c2')) fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr
            have K3 := hr.2
            rw [c2.cpu] at K3
            exact ⟨hr.1.1.1, F2.trans hr.1.1.2.1, f12.trans hr.1.2, K2.trans c1.he K3,
              c2.step K3 hr.1.1.2.1.2.1⟩
        · exact (WP.spec_ok _).2 ⟨h2, F2, f12, K2, c2⟩
      rintro ⟨s3, a3⟩ ⟨h3, F3, f3, K3, c3⟩
      simp only at h3 F3 f3 K3 c3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3', ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have hc3 := h3.1.choose_spec.choose_spec.cur
      have h3' := h3
      obtain ⟨⟨Q3, R3, q3⟩, -, hX3, -, -⟩ := h3'
      have N4 : FootN st (KI st T Cs (L.cpu s) s3) True T Cs Sg Scs Z ∅ s3
          (L.wr s3 (L.nodeAt s3 (L.cpu s3) layout.node.REPROGRAM) 1#u64) :=
        footN_node q3.nodes q3.cur (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)
          (idOff_ge (by rw [rp]; omega)) q3.cur (by rw [rp]; omega)
      have K34 : FKI st T Cs (L.cpu s) s3 _ := c3.fkiN q3 hX3.1 N4
      exact ⟨reprogram.tinv h3, F3.trans (FootD.u (Foot.d (foot_node (h3.1.choose_spec.choose_spec.nodes _ hc3) hc3
        (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)))), f3.trans (IKp s3 1#u64 h3),
        K3.trans c3.he K34, c3.step K34 N4.2.1, by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, f1, K1, c1⟩
  · exact ⟨h, FootD.u (Foot.d (Foot.refl _)), IbFr.refl s, FKI.refl _ s, c0⟩

/-- **`timer::fire` is an `FKI` step.** -/
theorem timer.fire.fki {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (c0 : FCtx st T Cs Scs (L.cpu s) s) :
    timer.fire st ar s a ⦃ s' _ => FKI st T Cs (L.cpu s) s s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.fki hA IK hNt s a now 0#u64 h hBA c0

/-- A thread of affinity `e` after an `OKeep2` frame from an `AllCores` state
is none of the other cores' threads. -/
theorem AllCores.notKs {s0 s : S} (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) {e y : U64}
    (kb : OKeep2 st T Cs e s0 s) (hy : L.mem s (affA y) = e) : y ∉ OtherK st T Cs e s0 := fun hk =>
  h0.notK (by rw [← kb.af y hk]; exact hy) hk

/-- **`FCtx` at an entry body's end.** -/
theorem FCtx.ofAll {s0 s : S} (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (kb : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hidl : L.mem s (stA (L.idleW s)) = sched.TS_IDLE)
    (hao : ActOut st T (OtherK st T Cs (L.cpu s0) s0) s) : FCtx st T Cs Scs (L.cpu s0) s := by
  obtain ⟨-, -, hX, -, -⟩ := h
  have iT : ∀ c ∈ Cs, idleAt st c s ∈ T := fun c hc' => by
    rw [kb.idle_eq hc']; exact (h0.core hc').per.idleT
  have iS0 : ∀ c ∈ Cs, L.mem s (scA (idleAt st c s)) ≠ 0#u64 := fun c hc' => by
    rw [kb.idle_eq hc', kb.isc c hc']; exact (h0.core hc').per.idle
  refine ⟨hc, hcpu, fun y hy => ?_, iT, fun c hc' => (hX.2.2.bound _ (iT c hc') (iS0 c hc')).1, iS0,
    fun c hc' => ?_, fun c hc' hne => ?_, fun c hc' hne => ?_, fun c hc' hne => ?_, ?_⟩
  · rw [kb.otherK] at hy; exact h0.KT y hy
  · by_cases e' : c = L.cpu s0
    · rw [e', ← hc]; exact hidl
    · rw [kb.idle_eq hc']; exact (kb.kp _ ⟨c, hc', e', Or.inl rfl⟩).idle (h0.idleSt c hc')
  · rw [(kb.words hc' hne).2.1]; exact (kb.kp _ ⟨c, hc', hne, Or.inr (Or.inl rfl)⟩).nb (h0.curNB c hc')
  · rw [(kb.words hc' hne).2.1, kb.af _ ⟨c, hc', hne, Or.inr (Or.inl rfl)⟩]; exact h0.curAff c hc'
  · rw [(kb.words hc' hne).1]; exact h0.actNT c hc'
  · rw [kb.otherK]; exact hao

/-- **`schedule` keeps the executing core's idle thread `TS_IDLE`** (`hsI` of
`AllCores.sched`): `fire` is an `FKI` step (`timer.fire.fki`), and the rest of
`schedule` an `SFootN` over `KI` (`schedule.sN` with `KpAff` widened: the
other cores' threads have other affinities, the idle thread is not runnable;
the current thread, none of the other cores' threads, is runnable only if it
is not the idle thread). -/
theorem sched.schedule.idl {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (kb : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hao : ActOut st T (OtherK st T Cs (L.cpu s0) s0) s) (hcK : L.curW s ∉ OtherK st T Cs (L.cpu s0) s0)
    (hidl : L.mem s (stA (L.idleW s)) = sched.TS_IDLE) :
    sched.schedule st ar s a ⦃ s' _ => L.mem s' (stA (L.idleW s')) = sched.TS_IDLE ⦄ := by
  have c : FCtx st T Cs Scs (L.cpu s0) s := FCtx.ofAll h0 hcpu kb hc h hidl hao
  have c' : FCtx st T Cs Scs (L.cpu s) s := by rw [hc]; exact c
  have he := c.he
  have h' := h
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := h'
  have hT := hq.tcbs
  have hiT : idleAt st (L.cpu s0) s ∈ T := c.iT _ he
  have hiS : L.mem s (stA (idleAt st (L.cpu s0) s)) = sched.TS_IDLE := c.iSt _ he
  have FK : ∀ rf : S × A, timer.fire st ar s a = ok rf → FKI st T Cs (L.cpu s0) s rf.1 ∧
      TInv st T Cs Ω H Sg Rp Scs Nt Z Ac rf.1 ∧ L.cpu rf.1 = L.cpu s0 := fun rf hrf => by
    have k0 := timer.fire.fki hA IK hNt s a ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA c'
    rw [hrf] at k0
    have k1 := (WP.spec_ok rf).1 k0
    have k : FKI st T Cs (L.cpu s) s rf.1 := k1
    have w := (WP.spec_ok _).1 (hrf ▸ timer.fire.tinvF hA IK hNt s a ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA)
    rw [hc] at k
    exact ⟨k, w.1, w.2.2.1.trans hc⟩
  have hF : ∀ rf : S × A, timer.fire st ar s a = ok rf →
      KpAff st T (KI st T Cs (L.cpu s0) s) rf.1 ∧ ActOut st T (KI st T Cs (L.cpu s0) s) rf.1 ∧
        (L.curW rf.1 ∈ KI st T Cs (L.cpu s0) s → ¬ Runnable (L.mem rf.1 (stA (L.curW rf.1)))) := fun rf hrf => by
    obtain ⟨k, w, hc1⟩ := FK rf hrf
    have hKA := KpAff.ofKeep h0 hcpu (kb.trans k.fk.keep) hc1
    have c1 := c.step k (hc1.trans hc.symm)
    obtain ⟨⟨Q1, R1, q1⟩, -, -, -, -⟩ := w
    have hI : L.mem rf.1 (stA (idleAt st (L.cpu s0) s)) = sched.TS_IDLE := k.idl.trans hiS
    refine ⟨fun y hy => ?_, ?_, fun hk => ?_⟩
    · rcases hy with hy | rfl
      · rw [kb.otherK] at hy; exact hKA y hy
      · exact ⟨hiT, Or.inr (by rw [hI]; exact tsIdle_nr)⟩
    · have ao := c1.aoK q1
      rw [k.kiEq he] at ao
      exact ao
    · rw [k.fk.cur] at hk ⊢
      rcases hk with hk | hk
      · rw [kb.otherK] at hk; exact absurd hk hcK
      · rw [hk, hI]; exact tsIdle_nr
  refine WP.spec_mono (sched.schedule.sN (Kp := KI st T Cs (L.cpu s0) s) hA IK hNt s a h hBA hF) ?_
  rintro ⟨s', a'⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨rf, hrf, -, F⟩ := hh
  obtain ⟨k, w, hc1⟩ := FK rf hrf
  obtain ⟨⟨Q1, R1, q1⟩, -, -, -, -⟩ := w
  have hcs : L.cpu s' = L.cpu s0 := F.2.1.trans hc1
  have hi' : idleAt st (L.cpu s0) s' = idleAt st (L.cpu s0) rf.1 := by
    show L.mem s' (L.nodeAt s' (L.cpu s0) layout.node.IDLE_THREAD) =
      L.mem rf.1 (L.nodeAt rf.1 (L.cpu s0) layout.node.IDLE_THREAD)
    rw [nodeAt_of_ksb F.1]
    exact F.mem_eq (nodeAt_aligned (q1.nodes _ he) (by rw [idle8]; omega) (by rw [idle8]))
      (fun hb => hb.2.1 ⟨_, he, _, Or.inl idle8, rfl⟩)
  have hs' : L.mem s' (stA (idleAt st (L.cpu s0) s)) = L.mem rf.1 (stA (idleAt st (L.cpu s0) s)) :=
    F.mem_eq (by rw [stA_eq]; exact field_aligned (hT _ hiT) (by simp) (by simp))
      (fun hb => hb.2.2 (Or.inl ⟨_, hiT, hT _ hiT, Or.inr rfl, Or.inl rfl⟩))
  show L.mem s' (stA (idleAt st (L.cpu s') s')) = sched.TS_IDLE
  rw [hcs, hi', k.fk.keep.idle_eq he, hs', k.idl]
  exact hiS

/-- **`schedule` closes an entry, `hfk` discharged** (`AllCores.sched` with
`FireKeep` from `timer.fire.fki`, `hsI` from `schedule.idl`). Entry end
facts `hao`, `hcK`, `hidl` (module docstring); hypotheses `hE` [J],
`hS0` [W]. -/
theorem AllCores.schedF {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (kb : OKeep2 st T Cs (L.cpu s0) s0 s) (hc : L.cpu s = L.cpu s0)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hao : ActOut st T (OtherK st T Cs (L.cpu s0) s0) s) (hcK : L.curW s ∉ OtherK st T Cs (L.cpu s0) s0)
    (hE : ∀ r : S × A, sched.awaken st ar s a = ok r → SchPre st T r.1)
    (hidl : L.mem s (stA (L.idleW s)) = sched.TS_IDLE) :
    sched.schedule st ar s a ⦃ s' _ => AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have c : FCtx st T Cs Scs (L.cpu s0) s := FCtx.ofAll h0 hcpu kb hc h hidl hao
  have c' : FCtx st T Cs Scs (L.cpu s) s := by rw [hc]; exact c
  have h' := h
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := h'
  refine AllCores.sched hA IK hNt a h0 hcpu hS0 kb hc h hBA (fun rf hrf => ?_) hE hidl
    (sched.schedule.idl hA IK hNt a h0 hcpu kb hc h hBA hao hcK hidl)
  have k0 := timer.fire.fki hA IK hNt s a ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ hBA c'
  rw [hrf] at k0
  have k1 := (WP.spec_ok rf).1 k0
  have k : FKI st T Cs (L.cpu s) s rf.1 := k1
  rw [hc] at k
  exact FireKeep.ofFK k.fk c.ao (by rw [kb.otherK]; exact hcK)

end

end Fl4Proofs.P2.Stall
