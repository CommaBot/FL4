/-
P2-level (p3J gen 33): **`reply_pop` and `reply_remove` in `KWN ∅ False`** (P1's `reply_pop.blk` /
`reply_remove.blk` give `FootD` only; P3JRecvFtN has `reply_remove_tcb.kwN0`). Namespace `Fl4Proofs.P1`, FL4 only.

* **`schedcontext.donate.kwDN`**: P2's `donate.kwIN` (an SC whose thread is in no queue) for an SC whose thread may
  be queued: the `dequeue` / `release_remove` no-ops replaced by P2's `dequeue.kwN` / `release_remove.kwN` and P1's
  `dequeue.inv` / `release_remove.inv` (text copy otherwise). `FootDN Kp Nd` (the debug-list words of the
  migration allowed).
* `keep_wrO`: a word other than the written one is kept.
* **`ipc.reply_pop.kwDN0`**: the head's SC takes the head's `prev` (`Sc.set_reply`, an `Sg` word), the new head the
  head's `NEXT` word, the head's links cleared (all `Sg` words: P3JRecvFtN's `footN0_sgw`), the SC donated back to
  the caller if it has none (`donate.kwDN` at the intermediate state: `SchedQueuesInvX` by `inv_of_free`, `DbgTz`
  by `DbgTz.wr_out`, the SC's `CORE` / `TCB` words kept), `reply_unlink` (`Sg` word, P2's
  `set_thread_state.kwNP`). From `XInv` (`ReplyInv.next` / `.prev`, `ScExtra.yt` / `.core`), `SchedQueuesInvX`,
  `DbgTz` at the entry.
* **`ipc.reply_remove.kwDN0`**: the head case by `reply_pop.kwDN0`, the others as `reply_remove_tcb.kwN0`.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JRecvFtN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64} {Kp : Set U64} {Nd : Prop}
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

set_option maxHeartbeats 2000000 in
/-- (p3J gen 33) **`donate`'s footprint in `KWN`, the SC's thread possibly queued** (P2 `donate.kwIN` with
`dequeue.kwN` / `release_remove.kwN` for its `noop`s). -/
theorem schedcontext.donate.kwDN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) {s0 : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s0)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hD : DbgTz st T Cs s) (hcore : L.mem s (scCoreA sc) ∈ Cs)
    (hsc : sc ∈ Scs) (hdst : dst ∈ T) (hNd : ¬ Nd) (hKa : ActOut st T Kp s)
    (hi : L.mem s (scTcbA sc) ≠ 0#u64 → L.mem s (scTcbA sc) ∈ T ∧ L.mem s (scTcbA sc) ∉ Kp) :
    schedcontext.donate st ar s a sc dst ⦃ s' _ => FootDN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hN' := h.nodes _ h.cur
  have hcO : scCoreA sc ∈ Ω := ((objs_omega hO hsub).2 sc hsc).2.1
  unfold schedcontext.donate
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => FootN st Kp Nd T Cs ∅ ∅ Z ∅ s r.1 ∧
      ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X r.1 Q1 R1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨FootN.refl _, Q, R, h⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    obtain ⟨hiT, hiK⟩ := hi (by rw [← ei]; exact hi0)
    rw [← ei] at hiT hiK
    refine WP.spec_bind (smp.remote_tcb_stall.spec hA s a i) ?_
    rintro ⟨s2, a2⟩ hs2
    try simp only [WP.uncurry'_pair] at hs2 ⊢
    have hst : SchedQueuesInvX st T Cs Ω H X s2 Q R ∧ FootN st Kp Nd T Cs ∅ ∅ Z ∅ s s2 := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · exact ⟨h, FootN.refl _⟩
      · exact ⟨inv_of_free h (free_node_write rfl h.cur hN' (by rw [ipi_val]; unfold LowFree; omega)),
          footN_node h.nodes h.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) (by rw [ipi_val]; omega)
            (idOff_ge (by rw [ipi_val]; omega)) h.cur (by rw [ipi_val]; omega)⟩
    obtain ⟨q2, f2⟩ := hst
    refine WP.spec_bind (WP.spec_and (sched.dequeue.kwN (Sg := ∅) (Scs := ∅) (Es := ∅) (Nd := Nd) (Z := Z) s2 i q2 hiT hiK)
      (sched.dequeue.inv s2 i Q R q2 hiT)) ?_
    rintro s3 ⟨f3, q3⟩
    refine WP.spec_bind (WP.spec_and (sched.release_remove.kwN (Sg := ∅) (Scs := ∅) (Es := ∅) (Nd := Nd) (Z := Z) s3 i q3
      hiT hiK) (sched.release_remove.inv s3 i _ R q3 hiT)) ?_
    rintro s4 ⟨f4, q4⟩
    have f24 : FootN st Kp Nd T Cs ∅ ∅ Z ∅ s s4 := (f2.trans f3).trans f4
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q4 hiT (by simp) (by simp) (by simp)
    have f05 : FootN st Kp Nd T Cs ∅ ∅ Z ∅ s (L.wr s4 (scA i) 0#u64) := by
      rw [scA_eq]; exact FootN.field hT h.nodes h.cur f24 hiT (by simp) (by simp) (by simp) (by simp)
        ⟨fun _ => by simp, fun h => absurd h hNd⟩
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => FootN st Kp Nd T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧
        ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s6 Q1 R1) ?_
      fun s6 ⟨f6, q6⟩ => (WP.spec_ok _).2 ⟨f05.trans f6, q6⟩
    have RR : sched.reschedule_required st (L.wr s4 (scA i) 0#u64) ⦃ s6 =>
        FootN st Kp Nd T Cs ∅ ∅ Z ∅ (L.wr s4 (scA i) 0#u64) s6 ∧ ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s6 Q1 R1 ⦄ :=
      WP.spec_mono (WP.spec_and (sched.reschedule_required.kwN _ q5 (f05.out hKa)) (sched.reschedule_required.inv _ _ _ q5))
        fun s6 ⟨f6, ⟨Q6, h6⟩, _, _⟩ => ⟨f6, _, _, h6⟩
    split
    · exact RR
    · step with sched.action.spec as ⟨i1, ei1⟩
      split
      · exact RR
      · exact (WP.spec_ok _).2 ⟨FootN.refl _, _, _, q5⟩
  rintro ⟨s1, a1⟩ ⟨f1, Q1, R1, h1⟩
  try simp only [WP.uncurry'_pair]
  have D1 : DbgTz st T Cs s1 := Foot0.dbg hT h.nodes f1.foot hD
  have c1 : L.mem s1 (scCoreA sc) = L.mem s (scCoreA sc) := Foot0.out hT h.nodes f1.foot (h.omega _ hcO)
  refine WP.spec_mono (donate_tail.frame hA s1 a1 sc dst h1 D1 hO.ksb hsub hsc hdst (by rw [c1]; exact hcore)) ?_
  rintro ⟨s', a'⟩ ⟨w, -⟩
  try simp only [WP.uncurry'_pair] at w ⊢
  have hact : L.actionW s' = L.actionW s1 := by
    refine actionW_of w (h1.nodes _ h1.cur) ?_
    have hN1 := h1.nodes _ h1.cur
    rintro (e | e | e | e)
    · exact notAct_omega h1 (by rw [e]; exact hsub _ (hO.fixW sc hsc).1)
    · rw [scA_eq] at e; exact node_ne_field hN1 (by rw [act_val]; omega) hdst (hT _ hdst) (by simp) e
    · rw [affA_eq] at e; exact node_ne_field hN1 (by rw [act_val]; omega) hdst (hT _ hdst) (by simp) e
    · exact notDbgW_node h1.tcbs h1.nodes h1.cur (by rw [act_val]; omega) (by rw [act_val]; omega) e
  refine (FootN.of0 (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Es := Es) f1 hNd).d.trans (FootDN.of' w (hk := AcK.of_eq hact) fun b hb' hb => ?_)
  rcases hb with rfl | rfl | rfl | hb
  · exact ⟨Or.inl (kw_sg (hO.fixW sc hsc).1), notIdW_out h1.nodes (h1.omega _ (hsub _ (hO.fixW sc hsc).1))
      (NoHdr.of_not hNd)⟩
  · exact ⟨Or.inl (by rw [scA_eq]; exact kw_field hdst (by simp) (by simp) (by simp)),
      by rw [scA_eq]; exact notIdW_field h1.tcbs h1.nodes hdst (by simp) ⟨fun _ => by simp, fun h => absurd h hNd⟩⟩
  · exact ⟨Or.inl (by rw [affA_eq]; exact kw_field hdst (by simp) (by simp) (by simp)),
      by rw [affA_eq]; exact notIdW_field h1.tcbs h1.nodes hdst (by simp) ⟨fun _ => by simp, fun h => absurd h hNd⟩⟩
  · exact ⟨Or.inr hb, notIdW_dbg h1.tcbs h1.nodes hb⟩

theorem keep_wrO {s : S} {a b v : U64} (ha : Aligned a) (hb : Aligned b) (hne : b.val ≠ a.val) :
    L.mem (L.wr s a v) b = L.mem s b :=
  (writesIn_wr (v := v) ha).2.2 b hb (fun e => hne (congrArg UScalar.val e))

set_option maxHeartbeats 4000000 in
/-- (p3J gen 33) **`reply_pop` in `KWN ∅ False`** (module docstring). -/
theorem ipc.reply_pop.kwDN0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hD : DbgTz st T Cs s) (hr : r ∈ Rp) (ht : t ∈ T)
    (hb : headBit (L.mem s (rNextA r)) = true) (hn0 : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64) :
    ipc.reply_pop st ar s a r t ⦃ res => FootDN st ∅ False T Cs Sg Scs Z Es s res.1 ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hal : ∀ b ∈ Ω, Aligned b := fun b hb => (h.omega b hb).1
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  obtain ⟨c, hc⟩ : ∃ c, L.mem s (rNextA r) &&& ~~~1#u64 = c := ⟨_, rfl⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (rPrevA r) &&& ~~~1#u64 = p := ⟨_, rfl⟩
  have hcS : c ∈ Scs := by rw [← hc]; exact (hX.2.1.next r hr hn0).1 hb
  have hpR : p ≠ 0#u64 → p ∈ Rp := fun h0' => by rw [← hp]; exact hX.2.1.prev r hr (by rw [hp]; exact h0')
  have hscF := sc_facts hO hcS
  have hTc : scTcbA c ∈ Ω ∧ scCoreA c ∈ Ω := ⟨(hcΩ c hcS).1, (hcΩ c hcS).2.1⟩
  have hm1 : scReplyA c ∈ Ω := hsub _ (hO.repW c hcS)
  unfold ipc.reply_pop
  step with obj.Reply.next.spec as ⟨nx, enx⟩
  step with obj.Reply.prev.spec as ⟨pv, epv⟩
  refine WP.spec_bind (obj.Reply.next_raw.val s r) fun raw eraw => ?_
  rw [hc] at enx; rw [hp] at epv
  subst nx pv raw
  step with obj.Sc.set_reply.spec as ⟨s1, e1⟩
  subst e1
  have F1 : FootN st ∅ False T Cs Sg Scs Z Es s (L.wr s (scReplyA c) p) :=
    footN0_sgw h hsub rfl rfl (hal _ hm1) (hO.repW c hcS)
  have h1 := inv_of_free h ((writesIn_wr (v := p) (hal _ hm1)).mono fun b hb => hb ▸ Or.inl hm1)
  have D1 : DbgTz st T Cs (L.wr s (scReplyA c) p) :=
    DbgTz.wr_out hT h.nodes (hal _ hm1) (notDbgW_out hT h.nodes (h.omega _ hm1)) hD
  have k1 : ∀ b, b = scTcbA c ∨ b = scCoreA c → L.mem (L.wr s (scReplyA c) p) b = L.mem s b := by
    rintro b (rfl | rfl)
    · exact keep_wrO (hal _ hm1) (hal _ hTc.1) (by rw [hscF.2.2.2.2.2.2.1, hscF.2.1]; omega)
    · exact keep_wrO (hal _ hm1) (hal _ hTc.2) (by rw [hscF.2.2.2.2.2.2.1, hscF.2.2.1]; omega)
  refine WP.spec_bind (Pₘ := fun s2 => FootN st ∅ False T Cs Sg Scs Z Es s s2 ∧
      (∃ Q2 R2, SchedQueuesInvX st T Cs Ω H X s2 Q2 R2) ∧ DbgTz st T Cs s2 ∧
      (∀ b, b = scTcbA c ∨ b = scCoreA c → L.mem s2 b = L.mem s b)) ?_ ?_
  · split
    · rename_i hp0
      have hpR' := hpR (by simpa using hp0)
      have hm2 : rNextA p ∈ Ω := (hrΩ p hpR').2.2
      have hal2 := hal _ hm2
      refine WP.spec_mono (obj.Reply.set_next_raw.val _ p _) fun s2 e2 => ?_
      subst e2
      obtain ⟨-, -, pp8, pn16⟩ := rp_facts hO hpR'
      have hne := rword_ne_sc hO hpR' (a := rNextA p) (by omega) c hcS
      refine ⟨F1.trans (footN0_sgw h hsub F1.1 F1.2.1 hal2 (hO.nextW hpR')),
        ⟨Q, R, inv_of_free h1 ((writesIn_wr hal2).mono fun b hb => hb ▸ Or.inl hm2)⟩,
        DbgTz.wr_out hT h1.nodes hal2 (notDbgW_out hT h1.nodes (h1.omega _ hm2)) D1, ?_⟩
      intro b hb
      rw [← k1 b hb]
      rcases hb with rfl | rfl
      · exact keep_wrO hal2 (hal _ hTc.1) (Ne.symm hne.1)
      · exact keep_wrO hal2 (hal _ hTc.2) (Ne.symm hne.2.1)
    · exact (WP.spec_ok _).2 ⟨F1, ⟨Q, R, h1⟩, D1, k1⟩
  rintro s2 ⟨F2, ⟨Q2, R2, h2⟩, D2, k2⟩
  have hm3 : rNextA r ∈ Ω := (hrΩ r hr).2.2
  have hal3 := hal _ hm3
  obtain ⟨-, -, rp8, rn16⟩ := rp_facts hO hr
  have hne3 := rword_ne_sc hO hr (a := rNextA r) (by omega) c hcS
  refine WP.spec_bind (obj.Reply.set_next.spec s2 r 0#u64) fun s3 hs3 => ?_
  obtain ⟨w3, e3, -⟩ := hs3
  subst e3
  have F3 := F2.trans (footN0_sgw (v := w3) h hsub F2.1 F2.2.1 hal3 (hO.nextW hr))
  have h3 := inv_of_free h2 ((writesIn_wr (v := w3) hal3).mono fun b hb => hb ▸ Or.inl hm3)
  have D3 : DbgTz st T Cs (L.wr s2 (rNextA r) w3) :=
    DbgTz.wr_out hT h2.nodes hal3 (notDbgW_out hT h2.nodes (h2.omega _ hm3)) D2
  have k3 : ∀ b, b = scTcbA c ∨ b = scCoreA c → L.mem (L.wr s2 (rNextA r) w3) b = L.mem s b := by
    intro b hb
    rw [← k2 b hb]
    rcases hb with rfl | rfl
    · exact keep_wrO hal3 (hal _ hTc.1) (Ne.symm hne3.1)
    · exact keep_wrO hal3 (hal _ hTc.2) (Ne.symm hne3.2.1)
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun res : S × A => FootDN st ∅ False T Cs Sg Scs Z Es s res.1) ?_ ?_
  · split
    · exact WP.spec_mono (schedcontext.donate.kwDN (Kp := ∅) (Nd := False) (Es := Es) hA _ a c t h3 hO hsub D3
        (by rw [k3 _ (Or.inr rfl)]; exact hX.2.2.core c hcS) hcS ht not_false (fun _ => Set.notMem_empty _)
        (fun h0' => ⟨by rw [k3 _ (Or.inl rfl)] at h0' ⊢; exact hX.2.2.yt.1 c hcS h0', Set.notMem_empty _⟩))
        fun res f => F3.d.trans f
    · exact (WP.spec_ok _).2 F3.d
  rintro ⟨s4, a4⟩ f4
  try simp only [WP.uncurry'_pair]
  dsimp only at f4 ⊢
  have hm5 : rPrevA r ∈ Ω := (hrΩ r hr).2.1
  refine WP.spec_bind (obj.Reply.set_prev.spec s4 r 0#u64) fun s5 hs5 => ?_
  obtain ⟨w5, e5, -⟩ := hs5
  subst e5
  have f5 := f4.trans (footN0_sgw (v := w5) h hsub f4.1 f4.2.1 (hal _ hm5) (hO.prevW hr)).d
  refine WP.spec_bind (Pₘ := fun s6 => FootDN st ∅ False T Cs Sg Scs Z Es s s6) ?_
    fun s6 f6 => (WP.spec_ok _).2 f6
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec _ r 0#u64) fun s6 e6 => ?_
  subst e6
  have hm6 : rTcbA r ∈ Ω := (hrΩ r hr).1
  have f6 := f5.trans (footN0_sgw (v := 0#u64) h hsub f5.1 f5.2.1 (hal _ hm6) (hO.tcbW hr)).d
  exact WP.spec_mono (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
    (Es := Es) _ t _ hT (fun c hc => (h.nodes c hc).ksb f6.1) (by rw [f6.2.1]; exact h.cur) ht
    (Set.notMem_empty t)) fun s7 f7 => f6.trans f7.d

set_option maxHeartbeats 4000000 in
/-- (p3J gen 33) **`reply_remove` in `KWN ∅ False`** (module docstring). -/
theorem ipc.reply_remove.kwDN0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (r t : U64)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hD : DbgTz st T Cs s) (hr : r ∈ Rp) (ht : t ∈ T) :
    ipc.reply_remove st ar s a r t ⦃ res => FootDN st ∅ False T Cs Sg Scs Z Es s res.1 ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  unfold ipc.reply_remove
  step with obj.Reply.next.spec as ⟨next, enext⟩
  step with obj.Reply.prev.spec as ⟨prev, eprev⟩
  have hpR : prev ≠ 0#u64 → prev ∈ Rp := fun h0' => by
    rw [eprev] at h0' ⊢; exact hX.2.1.prev r hr h0'
  split
  · rename_i hn
    have hn0 : L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 := by rw [← enext]; simpa using hn
    step with obj.Reply.next_is_head.spec as ⟨b, eb⟩
    split
    · rename_i hb
      exact ipc.reply_pop.kwDN0 hA s a r t h hX hsub hD hr ht (by rw [← eb]; exact hb) hn0
    · rename_i hb
      have hnR : (next != 0#u64) = true → next ∈ Rp := fun _ => by
        rw [enext]; exact (hX.2.1.next r hr hn0).2 (by rw [← eb]; simpa using hb)
      have hRp := hnR (by simpa using hn)
      refine WP.spec_bind (Pₘ := fun s1 => FootN st ∅ False T Cs Sg Scs Z Es s s1)
        (WP.spec_mono (obj.Reply.set_prev.spec s next 0#u64) fun s1 hs1 => by
          obtain ⟨w, e1, -⟩ := hs1; subst e1
          exact footN0_sgw h hsub rfl rfl (rp_aligned hO hRp).2.1 (hO.prevW hRp)) ?_
      intro s1 f1
      refine WP.spec_bind (Pₘ := fun s2 => FootN st ∅ False T Cs Sg Scs Z Es s s2) ?_ ?_
      · split
        · rename_i hne
          have hRp := hpR (by simpa using hne)
          exact WP.spec_mono (obj.Reply.set_next.spec s1 prev 0#u64) fun s2 hs2 => by
            obtain ⟨w, e2, -⟩ := hs2; subst e2
            exact f1.trans (footN0_sgw h hsub f1.1 f1.2.1 (rp_aligned hO hRp).2.2 (hO.nextW hRp))
        · exact (WP.spec_ok _).2 f1
      intro s2 f2
      refine WP.spec_bind (obj.Reply.set_prev.spec s2 r 0#u64) fun s3 hs3 => ?_
      obtain ⟨w3, e3, -⟩ := hs3
      subst e3
      have f3 := f2.trans (footN0_sgw (v := w3) h hsub f2.1 f2.2.1 (rp_aligned hO hr).2.1 (hO.prevW hr))
      refine WP.spec_bind (obj.Reply.set_next.spec _ r 0#u64) fun s4 hs4 => ?_
      obtain ⟨w4, e4, -⟩ := hs4
      subst e4
      have f4 := f3.trans (footN0_sgw (v := w4) h hsub f3.1 f3.2.1 (rp_aligned hO hr).2.2 (hO.nextW hr))
      refine WP.spec_bind (Pₘ := fun s5 => FootN st ∅ False T Cs Sg Scs Z Es s s5) ?_
        fun s5 f5 => (WP.spec_ok _).2 f5.d
      unfold ipc.reply_unlink
      refine WP.spec_bind (obj.Reply.set_tcb.spec _ r 0#u64) fun s5 e5 => ?_
      subst e5
      have f5 := f4.trans (footN0_sgw (v := 0#u64) h hsub f4.1 f4.2.1 (rp_aligned hO hr).1 (hO.tcbW hr))
      exact WP.spec_mono (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
        (Es := Es) _ t _ hT (fun c hc => (h.nodes c hc).ksb f5.1) (by rw [f5.2.1]; exact h.cur) ht
        (Set.notMem_empty t)) fun s6 f6 => f5.trans f6
  · rename_i hn
    have hnR : (next != 0#u64) = true → next ∈ Rp := fun hne => absurd hne hn
    refine WP.spec_bind (Pₘ := fun s1 => FootN st ∅ False T Cs Sg Scs Z Es s s1)
      ((WP.spec_ok _).2 (FootN.refl _)) ?_
    intro s1 f1
    refine WP.spec_bind (Pₘ := fun s2 => FootN st ∅ False T Cs Sg Scs Z Es s s2) ?_ ?_
    · split
      · rename_i hne
        have hRp := hpR (by simpa using hne)
        exact WP.spec_mono (obj.Reply.set_next.spec s1 prev 0#u64) fun s2 hs2 => by
          obtain ⟨w, e2, -⟩ := hs2; subst e2
          exact f1.trans (footN0_sgw h hsub f1.1 f1.2.1 (rp_aligned hO hRp).2.2 (hO.nextW hRp))
      · exact (WP.spec_ok _).2 f1
    intro s2 f2
    refine WP.spec_bind (obj.Reply.set_prev.spec s2 r 0#u64) fun s3 hs3 => ?_
    obtain ⟨w3, e3, -⟩ := hs3
    subst e3
    have f3 := f2.trans (footN0_sgw (v := w3) h hsub f2.1 f2.2.1 (rp_aligned hO hr).2.1 (hO.prevW hr))
    refine WP.spec_bind (obj.Reply.set_next.spec _ r 0#u64) fun s4 hs4 => ?_
    obtain ⟨w4, e4, -⟩ := hs4
    subst e4
    have f4 := f3.trans (footN0_sgw (v := w4) h hsub f3.1 f3.2.1 (rp_aligned hO hr).2.2 (hO.nextW hr))
    refine WP.spec_bind (Pₘ := fun s5 => FootN st ∅ False T Cs Sg Scs Z Es s s5) ?_
      fun s5 f5 => (WP.spec_ok _).2 f5.d
    unfold ipc.reply_unlink
    refine WP.spec_bind (obj.Reply.set_tcb.spec _ r 0#u64) fun s5 e5 => ?_
    subst e5
    have f5 := f4.trans (footN0_sgw (v := 0#u64) h hsub f4.1 f4.2.1 (rp_aligned hO hr).1 (hO.tcbW hr))
    exact WP.spec_mono (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
      (Es := Es) _ t _ hT (fun c hc => (h.nodes c hc).ksb f5.1) (by rw [f5.2.1]; exact h.cur) ht
      (Set.notMem_empty t)) fun s6 f6 => f5.trans f6

end

end Fl4Proofs.P1
