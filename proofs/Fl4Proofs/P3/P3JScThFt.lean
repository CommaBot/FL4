/-
P3 (p3J gen 43): **bucket 3, the SchedContext and Thread finaliser footprints inside `ProjW`**. P1 QueueFinSc's
`fin_sc.blk` and QueueFinal's `fin_thread.blk` walks mirrored at `Kp = ∅`, `Nd = False` (as gen 39 / 40 / 42 mirrored
the notification / endpoint / reply finalisers): every step is a `KWN ∅ False` step (no other core's idle words),
the debug-list removal a `DbgW` step (`FootDN`).

FL4 `objects.rs` `finalise_cap_object`: the `SchedContext` arm (l.369–381: `unbind_all_tcbs`, `unbind_ntfn`,
`unbind_reply`, `complete_yield_to` of the yield-from thread, `set_refill_max 0`, `set_sporadic 0`) and the `Thread`
arm (l.349–368: `remote_tcb_stall`, `vcpu::detach`, `unbind_notification`, `timer::remove`, the SC's `unbind_tcb`
and `complete_yield_to`, `suspend`, `debug_remove`, `fpu_release`); `schedcontext.rs` l.41–62 (`unbind_tcb`:
`reschedule_required` if current, `dequeue`, `release_remove`, the two links cleared; `unbind_all_tcbs`), l.100–106
(`unbind_reply`).

* `footN0_omega` (a write of an `Ω` word that is a `KW` word), `tws_footN0` (P3JFinW's `TWS` words — SC words,
  register / `YIELD_TO` / `STATE` words of one thread, the executing core's `SCHED_ACTION` — are `KWN ∅ False`
  words), `tw_footN0` (P1's timer words `TW`: TCB offsets 3528–3576, every core's 104 / 112).
* **`smp.remote_tcb_stall.kwN0`** (the IPI word 120 of the executing core), **`schedcontext.unbind_tcb.kwN0`**
  (`reschedule_required.kwN`, `dequeue.kwN`, `release_remove.kwN`, `footN_field` at 3464, `footN0_sgw`),
  **`schedcontext.unbind_all_tcbs.kwN0`**, **`schedcontext.unbind_reply.kwN0`**,
  **`schedcontext.complete_yield_to.kwN0`** (P3JFinW's `complete_yield_to.tws`).
* **`fin_sc.kwN0`** / `fin_cap_sc.kwN0` (hypotheses those of P1 `fin_sc.blk`), **`fin_thread.kwDN0`** /
  `fin_cap_thread.kwDN0` (hypotheses those of P1 `fin_thread.blk`; `unbind_notification.kwN0` of gen 40,
  `sched.suspend.kwN0` of gen 41, `timer.remove` by `TF`'s `TW` words, `debug_remove` by `notIdW_dbg`).
* P3: **`JAtZ.finScProjW`**, **`JAtZ.finThreadProjW`**: at a `JAtZ` state these write only `ProjW H Cs s`.

The hypotheses of the two P1 lemmas (the SC's thread / the thread is neither the scheduler action nor the idle
thread; the thread's VCPU word is 0) are lemma hypotheses here, as there; no named premise. `AcK` is vacuous at
`Kp = ∅`. No sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JFinFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64} {Es : Set U64}

/-- (p3J gen 43) A write of an `Ω` word that is a `KW` word is a `KWN ∅ False` step. -/
theorem footN0_omega {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 s : S}
    (h : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hk : L.ksb s = L.ksb s0) (hcp : L.cpu s = L.cpu s0)
    {a v : U64} (hm : a ∈ Ω) (hkw : KW st T Cs Sg Scs Z Es s a) :
    FootN st ∅ False T Cs Sg Scs Z Es s (L.wr s a v) := by
  have NP : ∀ c ∈ Cs, NodePlaced st T s c := fun c hc => (h.nodes c hc).ksb hk
  have ho : OutsideObjs st T Cs s a := (h.omega a hm).ksb hk
  exact footN_wr ho.1 ⟨hkw, notIdW_out NP ho (fun h => h.elim)⟩
    (actionW_out NP (by rw [hcp]; exact h.cur) ho)

/-- (p3J gen 43) **`TWS` words are `KWN ∅ False` words** (module docstring). -/
theorem tws_footN0 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S} {y : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hy : y ∈ T)
    (w : WritesIn st s s' (TWS st Scs Z y s)) : FootN st ∅ False T Cs Sg Scs Z Es s s' := by
  refine FootN.of' w (fun b hb hw => ?_) (fun _ h => absurd h (Set.notMem_empty _))
  rcases hw with (⟨c, hc, hin⟩ | ⟨K, h1, h2, h3, rfl⟩) | rfl | rfl | rfl
  · exact ⟨kw_sc hc hin, notIdW_out h.nodes (h.omega _ (hO.scW c hc b hb hin)) (fun h => h.elim)⟩
  · exact ⟨kw_field hy (by omega) (by omega) ⟨by omega, by omega⟩,
      notIdW_field h.tcbs h.nodes hy (by omega) (PrF.of_ne (by omega) (by omega) (by omega) (by omega) (by omega))⟩
  · rw [show yieldA y = core.num.U64.wrapping_add y 3472#u64 from rfl]
    exact ⟨kw_field hy (by simp) (by simp) (by simp), notIdW_field h.tcbs h.nodes hy (by simp)⟩
  · rw [stA_eq]
    exact ⟨kw_field hy (by simp) (by simp) (by simp), notIdW_field h.tcbs h.nodes hy (by simp)
      ⟨fun h => absurd h (Set.notMem_empty _), fun h => h.elim⟩⟩
  · exact ⟨kw_node h.cur (by rw [act_val]; omega) (by rw [act_val]; omega),
      notIdW_node h.nodes h.cur (by rw [act_val]; omega)
        (idOff_cur (by rw [act_val]; omega) (by rw [act_val]; omega) (fun h => h.elim))⟩

/-- (p3J gen 43) **The timer words `TW` are `KWN ∅ False` words** (module docstring). -/
theorem tw_footN0 {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (w : WritesIn st s s' (TW st T Cs s)) :
    FootN st ∅ False T Cs Sg Scs Z Es s s' := by
  refine FootN.of' w (fun b _ hb => ?_) (fun _ h => absurd h (Set.notMem_empty _))
  rcases hb with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨c, hc, o, ho, rfl⟩
  · exact ⟨kw_field hy (by omega) (by omega) ⟨by omega, by omega⟩,
      notIdW_field h.tcbs h.nodes hy (by omega) (PrF.of_ne (by omega) (by omega) (by omega) (by omega) (by omega))⟩
  · exact ⟨kw_node hc (by omega) (by omega), notIdW_node h.nodes hc (by omega) (idOff_ge (by omega))⟩

/-- (p3J gen 43) **`remote_tcb_stall` in `KWN ∅ False`**: it writes at most the executing core's IPI word. -/
theorem smp.remote_tcb_stall.kwN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  refine WP.spec_mono (smp.remote_tcb_stall.spec hA s a t) ?_
  rintro ⟨s', a'⟩ e
  simp only [WP.uncurry'_pair] at e ⊢
  rcases e with rfl | ⟨v, rfl⟩
  · exact FootN.refl _
  · have ip : layout.node.IPI_PENDING.val = 120 := by simp [layout.node.IPI_PENDING]
    exact footN_node h0.nodes h0.cur (by have := ip; omega) (by have := ip; omega) (by have := ip; omega)
      (idOff_ge (by have := ip; omega)) h0.cur (by have := ip; omega)

set_option maxHeartbeats 4000000 in
/-- (p3J gen 43) **`unbind_tcb` in `KWN ∅ False`** (P1 `schedcontext.unbind_tcb.blk`; module docstring). -/
theorem schedcontext.unbind_tcb.kwN0 (s : S) (sc : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hsc : sc ∈ Scs) :
    schedcontext.unbind_tcb st s sc ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  unfold schedcontext.unbind_tcb
  step with obj.Sc.tcb.spec as ⟨t, et⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  rename_i hb
  have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have htT : t ∈ T := by rw [et]; exact hX.2.2.yt.1 sc hsc (by rw [← et]; exact ht0)
  step with sched.cur_thread.spec as ⟨t1, et1⟩
  step with tcb_eq.blk as ⟨b1, eb1⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s1 Q1 R1) ∧
      FootN st ∅ False T Cs Sg Scs Z Es s s1) ?_ ?_
  · split
    · refine WP.spec_mono (WP.spec_and (sched.reschedule_required.inv s Q R h0)
        (sched.reschedule_required.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s h0
          (fun _ h => absurd h (Set.notMem_empty _)))) ?_
      rintro s1 ⟨⟨⟨Q1, h1⟩, -⟩, fw1⟩
      exact ⟨⟨Q1, R, h1⟩, fw1⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h0⟩, FootN.refl _⟩
  rintro s1 ⟨⟨Q1, R1, h1⟩, fw1⟩
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s1 t Q1 R1 h1 htT)
    (sched.dequeue.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s1 t h1 htT
      (Set.notMem_empty t))) ?_
  rintro s2 ⟨h2, fw2⟩
  refine WP.spec_bind (sched.release_remove.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es)
    s2 t h2 htT (Set.notMem_empty t)) fun s3 fw3 => ?_
  have f03 := fw1.trans (fw2.trans fw3)
  refine WP.spec_bind (obj.Tcb.set_sc.wr s3 t 0#u64) fun s4 e4 => ?_
  subst e4
  have NP3 : ∀ c ∈ Cs, NodePlaced st T s3 c := fun c hc => (h0.nodes c hc).ksb f03.1
  have hc3 : L.cpu s3 ∈ Cs := by rw [f03.2.1]; exact h0.cur
  have f4 : FootN st ∅ False T Cs Sg Scs Z Es s3 (L.wr s3 (scA t) 0#u64) := by
    rw [scA_eq]
    exact footN_field h0.tcbs NP3 hc3 htT (by simp) (by simp) (by simp) (by simp)
      ⟨fun h => absurd h (Set.notMem_empty _), fun h => h.elim⟩
  refine WP.spec_mono (obj.Sc.set_tcb.wr _ sc 0#u64) fun s5 e5 => ?_
  subst e5
  have f04 := f03.trans f4
  have hm := (hX.1.fixW sc hsc).1
  exact f04.trans (footN0_sgw h0 hSg.sub f04.1 f04.2.1 (h0.omega _ (hSg.sub _ hm)).1 hm)

/-- (p3J gen 43) **`unbind_all_tcbs` in `KWN ∅ False`** (module docstring). -/
theorem schedcontext.unbind_all_tcbs.kwN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) :
    schedcontext.unbind_all_tcbs st ar s a p ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  unfold schedcontext.unbind_all_tcbs
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  split
  · refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a i h)
      (smp.remote_tcb_stall.kwN0 (Es := Es) hA s a i h)) ?_
    rintro ⟨s1, a1⟩ hh
    simp only [WP.uncurry'_pair] at hh
    obtain ⟨⟨h1, -⟩, f1⟩ := hh
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (schedcontext.unbind_tcb.kwN0 (Es := Es) s1 p h1 hp) fun s2 f2 => ?_
    exact (WP.spec_ok _).2 (f1.trans f2)
  · exact (WP.spec_ok _).2 (FootN.refl _)

/-- (p3J gen 43) **`unbind_reply` in `KWN ∅ False`** (P1 `schedcontext.unbind_reply.blk`). -/
theorem schedcontext.unbind_reply.kwN0 (s : S) (c : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) :
    schedcontext.unbind_reply st s c ⦃ s' => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.2.sub
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootN.refl _)
  rename_i hb
  have hcS : c ∈ Scs := hc (fun e => hb (by rw [eb, e]; rfl))
  refine WP.spec_bind (obj.Sc.reply.val s c) fun i ei => ?_
  split
  · rename_i hi
    have hiR : i ∈ Rp := by rw [ei]; exact h.2.2.1.2.1.screp c hcS (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (obj.Reply.set_next.val0 s i 0#u64) fun s1 e1 => ?_
    rw [zero_link] at e1
    subst e1
    have m1 := hO.nextW hiR
    have m2 := hO.repW c hcS
    refine WP.spec_mono (obj.Sc.set_reply.spec _ c 0#u64) fun s2 e2 => ?_
    subst e2
    exact (footN0_sgw h0 hsub rfl rfl (h0.omega _ (hsub _ m1)).1 m1).trans
      (footN0_sgw h0 hsub (by rw [L.ksb_wr]) (by rw [L.cpu_wr]) (h0.omega _ (hsub _ m2)).1 m2)
  · exact (WP.spec_ok _).2 (FootN.refl _)

/-- (p3J gen 43) **`complete_yield_to` in `KWN ∅ False`** (P3JFinW's `TWS` walk; module docstring). -/
theorem schedcontext.complete_yield_to.kwN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (y : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T) :
    schedcontext.complete_yield_to st ar s a y ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z Es s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, -⟩ := h
  refine WP.spec_mono (schedcontext.complete_yield_to.tws hA s a y (fun b hb => h0.omega b hb) hX.1 hy h0.tcbs
    (fun h1 => hX.2.2.yt.2.1 y hy h1)) ?_
  rintro ⟨s', a'⟩ w
  simp only [WP.uncurry'_pair]
  exact tws_footN0 h0 hX.1 hy w

set_option maxHeartbeats 4000000 in
/-- (p3J gen 43) **A SchedContext cap's object finalisation in `KWN ∅ False`** (P1 `fin_sc.blk`, its
hypotheses; module docstring). -/
theorem fin_sc.kwN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) fin ⦃ r =>
      FootN st ∅ False T Cs Sg Scs Z Es s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (FootN.refl _)
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_all_tcbs.blk hA s a p h hp hp0 hna hidle)
    (schedcontext.unbind_all_tcbs.kwN0 (Es := Es) hA s a p h hp)) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh
  obtain ⟨⟨h1, -⟩, g1⟩ := hh
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_ntfn.blk s1 p h1 fun _ => hp)
    (schedcontext.unbind_ntfn.kwN0 (Es := Es) s1 p h1 fun _ => hp)) fun s2 hh2 => ?_
  obtain ⟨⟨h2, -⟩, g2⟩ := hh2
  refine WP.spec_bind (WP.spec_and (schedcontext.unbind_reply.blk s2 p p h2 (fun _ => hp) hp)
    (schedcontext.unbind_reply.kwN0 (Es := Es) s2 p h2 (fun _ => hp))) fun s3 hh3 => ?_
  obtain ⟨⟨h3, -⟩, g3⟩ := hh3
  refine WP.spec_bind (obj.Sc.yield_from.val s3 p) fun yf eyf => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      FootN st ∅ False T Cs Sg Scs Z Es s3 r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, FootN.refl _⟩
    · rename_i hb
      have hy0 : yf ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hyT : yf ∈ T := by rw [eyf]; exact h3.2.2.1.2.2.yt.2.2 p hp (by rw [← eyf]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s3 a1 yf h3 (fun _ => hyT))
        (schedcontext.complete_yield_to.kwN0 (Es := Es) hA s3 a1 yf h3 hyT)) ?_
      rintro ⟨s4, a4⟩ hh4
      simp only [WP.uncurry'_pair] at hh4
      exact ⟨hh4.1.1, hh4.2⟩
  rintro ⟨s4, a2⟩ ⟨h4, g4⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (obj.Sc.set_refill_max.spec s4 p 0#u64) fun s5 e5 => ?_
  subst e5
  refine WP.spec_bind (obj.Sc.set_sporadic.wr _ p 0#u64) fun s6 e6 => ?_
  subst e6
  have h04 := h4.1.choose_spec.choose_spec
  have hO := h4.2.2.1.1
  have hsub := h4.2.2.2.2.sub
  obtain ⟨hPp, hzp⟩ := hO.sc p hp
  obtain ⟨h8, h128, -⟩ := sc_lo hPp hzp
  have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
  have av : (core.num.U64.wrapping_add p layout.sc.SPORADIC).val = p.val + 64 := by
    rw [sc_word_val hPp hzp (by rw [hsv]; omega), hsv]
  have hal : Aligned (core.num.U64.wrapping_add p layout.sc.SPORADIC) := by unfold Aligned; rw [av]; omega
  have hin : InSC p (Z p) (core.num.U64.wrapping_add p layout.sc.SPORADIC) :=
    ⟨by rw [av]; omega, by rw [av]; omega⟩
  have hms := hO.scW p hp _ hal hin
  have hmx := hO.mxW p hp
  have g5 : FootN st ∅ False T Cs Sg Scs Z Es s4 (L.wr s4 (maxA p) 0#u64) :=
    footN0_sgw h04 hsub rfl rfl (h04.omega _ (hsub _ hmx)).1 hmx
  have g6 : FootN st ∅ False T Cs Sg Scs Z Es (L.wr s4 (maxA p) 0#u64)
      (L.wr (L.wr s4 (maxA p) 0#u64) (core.num.U64.wrapping_add p layout.sc.SPORADIC) 0#u64) :=
    footN0_omega h04 (by rw [L.ksb_wr]) (by rw [L.cpu_wr]) hms (kw_sc hp hin)
  exact (WP.spec_ok _).2 (g1.trans (g2.trans (g3.trans (g4.trans (g5.trans g6)))))

/-- (p3J gen 43) **`finalise_cap` of a SchedContext cap in `KWN ∅ False`** (module docstring). -/
theorem fin_cap_sc.kwN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap st ar s a (.SchedContext p x) fin ex ⦃ r =>
      FootN st ∅ False T Cs Sg Scs Z Es s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_sc.kwN0 hA s a p x fin h hp hp0 hna hidle

set_option maxHeartbeats 4000000 in
/-- (p3J gen 43) **A thread cap's object finalisation in `FootDN ∅ False`** (P1 `fin_thread.blk`, its
hypotheses; module docstring). -/
theorem fin_thread.kwDN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r =>
      FootDN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (FootDN.refl _)
  have hStart := h
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hStart
  refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.blk hA s a p h)
    (smp.remote_tcb_stall.all hA s a p hq0 hb0 hx0 hs0 hg0))
    (smp.remote_tcb_stall.kwN0 (Es := EH H) hA s a p h)) ?_
  rintro ⟨s1, a1⟩ hh
  simp only [WP.uncurry'_pair] at hh
  obtain ⟨⟨⟨h1, -, ea1, -, ei1⟩, _, _, _, _, _, _, _, _, _, keep, _⟩, g1⟩ := hh
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (vcpu.detach_none ar s1 a1 p (by
    rw [keep p hp 3664#u64 (by simp) (by simp)]; exact hv0)) ?_
  intro r hr
  subst r
  try dsimp only
  refine WP.spec_bind (WP.spec_and (notification.unbind_notification.blkF s1 p h1 hp)
    (notification.unbind_notification.kwN0 (Es := EH H) s1 p h1 hp)) fun s2 hh2 => ?_
  obtain ⟨⟨h2, -, n2⟩, g2⟩ := hh2
  refine WP.spec_bind (timer.remove.tf (s0 := s2) s2 p (TF.start h2) hp) fun s3 hh3 => ?_
  obtain ⟨h3, -, n3, -, w3⟩ := hh3
  have ea3 : L.actionW s3 = L.actionW s := by rw [n3.1, n2.1, ea1]
  have ei3 : L.idleW s3 = L.idleW s := by rw [n3.2.1, n2.2.1, ei1]
  have g3 : FootN st ∅ False T Cs Sg Scs Z (EH H) s2 s3 := tw_footN0 h2.1.choose_spec.choose_spec w3
  have g03 := g1.trans (g2.trans g3)
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      FootN st ∅ False T Cs Sg Scs Z (EH H) s r.1 ∧ L.actionW r.1 ≠ p) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, g03, by rw [ea3]; exact hna⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiS, hit, -⟩ := h3.2.2.1.2.2.bound p hp (by rw [← ei]; exact hi0)
    rw [← ei] at hiS hit
    refine WP.spec_bind (WP.spec_and (schedcontext.unbind_tcb.blk s3 i h3 hiS hi0
      (fun _ => by rw [hit, ea3]; exact hna) (fun _ => by rw [hit, ei3]; exact hidle))
      (schedcontext.unbind_tcb.kwN0 (Es := EH H) s3 i h3 hiS)) fun s5 hh5 => ?_
    obtain ⟨⟨h5, -, ea5, _⟩, g5⟩ := hh5
    have na5 : L.actionW s5 ≠ p := by
      rcases ea5 with e | e
      · rw [e, ea3]; exact hna
      · rw [e]; exact fun e' => notT_small h5.1.choose_spec.choose_spec.tcbs (by simp) (e' ▸ hp)
    step with obj.Sc.yield_from.val as ⟨y, ey⟩
    step with obj.Tcb.is_null.spec as ⟨b1, eb1⟩
    split
    · exact (WP.spec_ok _).2 ⟨h5, g03.trans g5, na5⟩
    · rename_i hb1
      have hy0 : y ≠ 0#u64 := fun e => hb1 (by rw [eb1, e]; rfl)
      have hyT : y ∈ T := by rw [ey]; exact h5.2.2.1.2.2.yt.2.2 i hiS (by rw [← ey]; exact hy0)
      refine WP.spec_mono (WP.spec_and (schedcontext.complete_yield_to.blk hA s5 a1 y h5 (fun _ => hyT))
        (schedcontext.complete_yield_to.kwN0 (Es := EH H) hA s5 a1 y h5 hyT)) ?_
      rintro ⟨s6, a6⟩ hh6
      simp only [WP.uncurry'_pair] at hh6
      obtain ⟨⟨h6, -, n6⟩, g6⟩ := hh6
      exact ⟨h6, (g03.trans g5).trans g6, by rw [n6.1]; exact na5⟩
  rintro ⟨s4, a2⟩ ⟨h4, g4, na4⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (WP.spec_and (sched.suspend.blk s4 a2 p h4 hp na4) (sched.suspend.kwN0 s4 a2 p h4 hp)) ?_
  rintro ⟨s5, a3⟩ hh5
  simp only [WP.uncurry'_pair] at hh5
  obtain ⟨⟨h5, -⟩, g5⟩ := hh5
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (objects.debug_remove.x (X := ∅) s5 p h5 hp) fun s6 hh6 => ?_
  obtain ⟨-, -, w6⟩ := hh6
  refine WP.spec_bind (hA.fpu_release a3 p) fun a4 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.slot.p0 p _) fun s7 _ => ?_
  have h05 := h5.1.choose_spec.choose_spec
  have g6 : FootDN st ∅ False T Cs Sg Scs Z (EH H) s5 s6 :=
    FootDN.of' w6 (fun b _ hb => ⟨Or.inr hb, notIdW_dbg h05.tcbs h05.nodes hb⟩)
      (fun _ h => absurd h (Set.notMem_empty _))
  exact (WP.spec_ok _).2 ((g4.trans g5).d.trans g6)

/-- (p3J gen 43) **`finalise_cap` of a thread cap in `FootDN ∅ False`** (module docstring). -/
theorem fin_cap_thread.kwDN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p)
    (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) :
    objects.finalise_cap st ar s a (.Thread p) fin ex ⦃ r =>
      FootDN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_thread.kwDN0 hA s a p fin h hp hna hidle hv0

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 43) **`finalise_cap` of a SchedContext cap at a `JAtZ` state writes only `ProjW`** (module
docstring; hypotheses those of P1 `fin_sc.blk`). -/
theorem JAtZ.finScProjW (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ P1.Heap.scs H) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p))
    (hidle : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) (x : U64) (fin ex : Bool) :
    objects.finalise_cap st arI s a (.SchedContext p x) fin ex ⦃ r =>
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.fin_cap_sc.kwN0 (Es := P1.EH H) hA s a p x fin ex J.blk hp hp0 hna hidle) fun _ F =>
    (P1.WritesA.w F).mono fun _ hb => Mc.kwN_projW J.kern.heap h0.nodes hb

/-- (p3J gen 43) **`finalise_cap` of a thread cap of `Z.T` at a `JAtZ` state writes only `ProjW`** (module
docstring; hypotheses those of P1 `fin_thread.blk`). -/
theorem JAtZ.finThreadProjW (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ Z.T) (hna : L.actionW s ≠ p)
    (hidle : L.idleW s ≠ p) (hv0 : L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) (fin ex : Bool) :
    objects.finalise_cap st arI s a (.Thread p) fin ex ⦃ r =>
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.fin_cap_thread.kwDN0 hA s a p fin ex J.blk (J.zH.1 p hp) hna hidle hv0) fun _ F =>
    footDN_projW J.kern.heap h0.nodes F

end

end Fl4Proofs.P3
