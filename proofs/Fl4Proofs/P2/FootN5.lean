/-
P2 (p2j, KWN step 5): **`send_ipc` and the timeout fault in `KWN`**.

* `IpcFootN`: P1's `IpcFoot` (`IpcW`: `KW`, the receiver's user context and
  IPC buffer, cap-slot words, debug-list words) without node identity
  words; `refl`/`trans`, `FootDN.ipc`, `FootN.ipc`, `XferW.ipcN` (the
  transfer's words are no node identity words, from the invariants at the
  transfer's start and `UserOK`).
* `send_ipc.footPN` (P1 `send_ipc.footP` over `KWN` steps), `send_ipc.footN`,
  `handle_timeout.footN`: a timeout fault writes only `IpcW` words and no
  node identity word.
* `tmoKG_N`: P1's `TmoKG` for `GN s0` (`XG` and an `IpcFootN` footprint from
  `s0`), from `EntryHyps0`, `TmoXG` and the transfer footprint `XferFootOK`
  at a relation `RS` — **named premise `hRSX` [P]**: `RS s s` at every `XG`
  state where `BXI` holds (P3's `RSI`, its CSpace relation at P3's placed
  states; P1's own users pass it per call as `hRS0`). `GN s0` is kept by
  `KWN` steps (`GN.foot`), so with `check_budget.allGN` (`P2/FootN3.lean`)
  the budget path from `s0` writes no node identity word of `s0`.
* (p2j3) the exclusion layer: `send_ipc.footPN`/`footN` and
  `handle_timeout.footN` take the sender `t ∉ Kp`, the protected threads
  not blocked (so the woken receiver is none of them) and, for a
  donation, `¬ Nd`; `tmoKG_N` runs in `Nd` mode and derives these from
  `s0` (the current thread and the `Kp` states are protected words).
  **Named premise `XferHdr` [P]**: the message transfer writes no SC
  `REPLY`/`TCB` word (P1's `XferW` admits any SC word).
-/
import Fl4Proofs.P2.FootN3
import Fl4Proofs.P2.FootN4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- `IpcW` without the node identity words. -/
def IpcWN {S : Type _} (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat)
    (Es U : Set U64) (s0 : S) (b : U64) : Prop :=
  IpcW st T Cs Ω Sg Scs Z Es U s0 b ∧ ¬ IdW st Kp Nd T Cs Scs s0 b

/-- A footprint inside `IpcWN`. -/
abbrev IpcFootN {S : Type _} (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat)
    (Es U : Set U64) (s s' : S) : Prop :=
  WritesIn st s s' (IpcWN st Kp Nd T Cs Ω Sg Scs Z Es U s)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64} {Kp : Set U64} {Nd : Prop}

theorem IpcFootN.refl (s : S) : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s := WritesIn.refl _ _

theorem IpcFootN.trans {s₁ s₂ s₃ : S} (h₁ : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s₁ s₂)
    (h₂ : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s₂ s₃) : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb =>
    Or.elim hb id fun hb => ⟨IpcW.ksb h₁.1 hb.1, notIdW_ksb h₁.1.symm h₁.2.1.symm hb.2⟩

theorem IpcFootN.ipc {s s' : S} (h : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') : IpcFoot st T Cs Ω Sg Scs Z Es U s s' :=
  WritesIn.mono h fun _ hb => hb.1

/-- An `IpcFootN` footprint keeps the node identity words. -/
theorem IpcFootN.idKeep {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') {b : U64} (hb : Aligned b)
    (hi : IdW st Kp Nd T Cs Scs s b) : L.mem s' b = L.mem s b :=
  f.mem_eq hb fun hk => hk.2 hi

theorem FootDN.ipc {s s' : S} (h : FootDN st Kp Nd T Cs Sg Scs Z Es s s') : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s' :=
  WritesIn.mono h fun _ hb => ⟨hb.1.elim Or.inl fun hd => Or.inr (Or.inr (Or.inr hd)), hb.2⟩

theorem FootN.ipc {s s' : S} (h : FootN st Kp Nd T Cs Sg Scs Z Es s s') : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s' :=
  FootDN.ipc h.d

/-- The transfer's words are no node identity words. -/
theorem XferW.ipcN {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hU : UserOK st T Cs Ω H U s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (w : WritesIn st s s' (XferW T U Ω Sg Scs Z (L.ksb s)))
    (hh : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) ∧ L.mem s' (scTcbA c) = L.mem s (scTcbA c)) :
    IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s' := by
  refine ⟨w.1, w.2.1, fun b hb hn => ?_⟩
  by_cases hhd : ∃ c ∈ Scs, b = scReplyA c ∨ b = scTcbA c
  · obtain ⟨c, hc, e | e⟩ := hhd <;> subst e
    · exact (hh c hc).1
    · exact (hh c hc).2
  have nh : NoHdr Nd Scs b := fun _ c hc => ⟨fun e => hhd ⟨c, hc, Or.inl e⟩, fun e => hhd ⟨c, hc, Or.inr e⟩⟩
  refine w.2.2 b hb fun hx => hn ⟨?_, ?_⟩
  · rcases hx with hx | hx | ⟨c, hc, hin⟩
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inl (kw_sc hc hin)
  · rcases hx with (⟨y, hy, K, hK, -, e⟩ | hu) | ⟨⟨y, hy, K, hK, e⟩ | ⟨hm, -⟩, -⟩ | ⟨c, hc, hin⟩
    · subst e; exact notIdW_field h.tcbs h.nodes hy (by omega)
    · exact notIdW_out h.nodes (hU b hu).1 nh
    · subst e; exact notIdW_field h.tcbs h.nodes hy (by omega)
    · exact notIdW_out h.nodes (h.omega _ hm) nh
    · exact notIdW_out h.nodes (h.omega _ (hX.1.scW c hc b hb hin)) nh

/-- **A property `send_ipc` keeps**, `KWN` steps (P1 `send_ipc.footP` with `KW`
replaced by `KWN` and the transfer's start a `FootN` step): under `send_ipc.ipc`'s hypotheses, a
property `Pst` of the states that holds at the start, is kept by `KW` steps
(`hPK`) and holds after the message transfer from a state the receiver's
dequeue (a `KW` step from `s`) reached (`hxP`), holds at the end
(`send_ipc.foot`: `IpcFoot` from `s`; `send_ipc.xg`: `XG`). -/
theorem endpoint.send_ipc.footPN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKt : t ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) (hdK : can_donate = true → ¬ Nd) (Pst : S → Prop)
    (hPK : ∀ s1 s2 : S, Pst s1 → FootDN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → Pst s2) (hP0 : Pst s)
    (hxP : ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s1 : S) (a : A) (snd ep badge : U64)
      (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
      SchedQueuesInvX st T Cs Ω H X s1 Q R → BoundInv st T Ac s1 → XInv st T Cs Ω Sg Rp Scs Nt Z s1 →
      SCsOK st T Ω Sg Scs Z Ac s1 → SgOK st Ω Sg s1 → UserOK st T Cs Ω H U s1 →
      FootN st Kp Nd T Cs Sg Scs Z (EH H) s s1 → XG st T Cs Ω H Sg Scs Z P3Ok s1 →
      ipc.do_ipc_transfer st ar s1 a snd ep badge grant rcv ⦃ s2 => Pst s2 ⦄) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => Pst s' ⦄ := by
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (endpoint.send_ipc.blockFootN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply can_donate t e h (fun _ => hc) hH (Or.inl e0) hKt (hdrΩ_of hX hSg.sub)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hPK _ _ hP0 hh.d
  · exact WP.spec_mono (endpoint.send_ipc.blockFootN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply can_donate t e h (fun _ => hc) hH (Or.inr e0) hKt (hdrΩ_of hX hSg.sub)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hPK _ _ hP0 hh.d
  -- a receiving endpoint
  obtain ⟨hdT, hbe, -, hds⟩ := ep_head h hH (Or.inr rfl) e0
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ t := fun e' => hc.nb (by rw [← e', hds]; exact Or.inr (Or.inl rfl))
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inr (Or.inl rfl)))
  have hKd : hd ∉ Kp := fun hk => hKB hd hk (by rw [hds]; exact Or.inr (Or.inl rfl))
  have hdta := hT hd hdT
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  have hv2 : v = 2#u64 := hv.trans e0
  rw [hv2]
  simp only [ep_idle_val, ep_send_val', show ¬ ((2#u64) = 0#u64) from by decide,
    show ¬ ((2#u64) = 1#u64) from by decide, ↓reduceIte]
  have hsub := hSg.sub
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE0, hEN0, hq0⟩ := hEW0.1 e heE0
  have hdm : hd ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 hd hdT (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s e hd (EQ0 e) hT hE0 hq0 hdm)) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  have F1 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s s1 :=
    FootN.of' w1 fun b _ hb => EpFoot.kwN hT h.nodes hq0.mem (Or.inl hH) hE0 hEN0 (hEW0.2.2.1 e heE0) (hdrΩ_of hX hSg.sub) hb
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  refine WP.spec_bind (WP.spec_and (hxf _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1)
      (hG.foot F1.foot))
    (hxP _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) F1 (hG.foot F1.foot))) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩, F2⟩
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1' h2' => (f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1' h2')
  have Fst : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Frp : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fiq : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fsc : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea2' : L.actionW s2 = L.actionW s := ea2.trans ea1
  have ei2' : L.idleW s2 = L.idleW s := ei2.trans ei1
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  have hds2 : L.mem s2 (stA hd) = sched.TS_BLOCKED_ON_RECV := (Fst hd hdT).trans hds
  -- the reply object leaves the receiver
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3 : Set U64, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SCsOK st T Ω Sg Scs Z Ac s3 ∧ SgOK st Ω Sg s3 ∧ ExcT X3 hd ∧
      (hd ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA hd))) ∧ ¬ Runnable (L.mem s3 (stA hd)) ∧
      (hd ∈ X3 → L.mem s3 (replyA hd) = 0#u64) ∧ (hd ∉ X3 → L.mem s3 (stA hd) = sched.TS_INACTIVE) ∧
      ((i != 0#u64) = true → hd ∉ X3 ∧ i ∈ Rp ∧ L.mem s3 (rTcbA i) = 0#u64) ∧
      L.mem s3 (stA t) = L.mem s (stA t) ∧ L.mem s3 (inqA t) = L.mem s (inqA t) ∧
      L.mem s3 (scA t) = L.mem s (scA t) ∧ L.actionW s3 ≠ t ∧ L.idleW s3 = L.idleW s ∧
      L.mem s3 (scA hd) = L.mem s (scA hd) ∧ Pst s3) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (WP.spec_and (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s2 i hd h2 hX2 hsub hiR hdT hKd)) fun s3 hh' => ?_
      obtain ⟨hh, fu⟩ := hh'
      obtain ⟨h3, e3, k3, z3⟩ := hh
      have hclr : ∀ r ∈ Rp, L.mem s2 (rTcbA r) = hd → L.mem s3 (rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, ← ei] at b2; rw [← b2]; exact z3
      refine ⟨_, h3, hB2.keepT h2 k3 (by rw [e3]; exact not_blocked_inactive) (by rw [e3]; exact inactive_ne.1),
        hX2.keepT k3 (by rw [e3]; exact inactive_ne) hclr, hS2.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3]; exact not_blocked_inactive), by rw [e3]; exact not_runnable_inactive,
        fun hm => absurd rfl hm.2, fun _ => e3, fun _ => ⟨fun hm => hm.2 rfl, hiR, z3⟩,
        (k3.stf ht (Ne.symm hdt)).trans (Fst t ht), (k3.inqf ht).trans (Fiq t ht), (k3.scf ht).trans (Fsc t ht),
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT), hPK _ _ F2 fu.d⟩
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · rcases k3.act with e' | e'
        · rw [e', ea2']; exact hc.na
        · rw [e']; exact fun e2 => notT_small hT (by simp) (e2 ▸ ht)
    · rename_i hi
      have hi0 : i = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi; exact hi
      refine (WP.spec_ok _).2 ⟨_, h2, hB2, hX2, hS2, hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl),
        by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl)), fun _ => by rw [← ei, hi0],
        fun hm => absurd (Or.inr rfl) hm, fun hi' => absurd hi0 (by simpa using hi'),
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT, F2⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3, F3⟩
  have hdA3 : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [shd3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inr (Or.inl rfl))))))))
      h0
  have htA3 : L.mem s3 (scA t) ≠ 0#u64 → L.mem s3 (scA t) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢; exact hc.ac h0
  have htq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by rw [iq3]; exact hc.nq
  have htr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by rw [iq3]; exact hc.nr
  have hnb3 : ¬ Blocked (L.mem s3 (stA t)) := by rw [st3]; exact hc.nb
  have hnrp3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st3]; exact hc.nrp
  have hcold3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨hnrp3, fun e' => hnb3 (Or.inr (Or.inl e'))⟩
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT hnr3
  have hidle3 : L.idleW s3 ≠ t := by rw [ei3]; exact hidle
  have hnt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ t := hX3.noref hta hcold3.1 hcold3.2
  have hnd3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ hd := by
    by_cases hm : hd ∈ X3
    · exact hX3.noref0 hdta (hz3 hm)
    · have e' := hin3 hm
      exact hX3.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4, f4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_mono (send_tail.footN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s4 a1 hd Q4 R4 h4 hB4 hX4 hS4
      hSg4 hdT hXc4 hx4 hnr4 hdA4 hKd) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact hPK _ _ F3 (f4.trans hr.d)
  have Ppush : (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i can_donate ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (WP.spec_and (ipc.reply_push.ipc hA s3 a t hd i can_donate Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3)
      (ipc.reply_push.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a t hd i can_donate h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT htA3 hKt hdK)) fun r hh' => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh'
    obtain ⟨hh, fk⟩ := hh'
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0, fk⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    refine WP.spec_bind (WP.spec_and (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩)
      (sched.set_thread_state.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ h3 ht hKt)) fun s4 hh' => ?_
    obtain ⟨hh, fk⟩ := hh'
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0, fk.d⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3, WritesIn.refl _ _⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      have hsc0 : L.mem s3 (scA t) ≠ 0#u64 := by rw [sc3]; exact hdon hcd
      obtain ⟨hiS, hitc, -⟩ := hX3.2.2.bound t ht hsc0
      rw [← ei3'] at hiS hitc
      refine WP.spec_mono (WP.spec_and (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt
        (by rw [ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)) (by rw [ei3]; exact hdi))
        (schedcontext.donate.kwIN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a i3 hd h3 hX3.1 hSg3.sub
          hX3.dbg (hX3.2.2.core i3 hiS) hiS hdT (hdK hcd) fun _ => by rw [hitc]; exact ⟨ht, htq3, htr3⟩))
        fun r hh' => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh'
      obtain ⟨hh, fk⟩ := hh'
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4, sd4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_,
        fun _ => by rw [sd4, ei3']; exact htA3 (by rw [sc3]; exact hdon hcd), fk⟩
      · rcases hx3 with hm | hnb
        · exact Or.inl hm
        · exact Or.inr (by rw [st4 hd hdT]; exact hnb)
      · by_cases hm : hd ∈ X3
        · exact hX4.noref0 hdta (by rw [rp4 hd hdT]; exact hz3 hm)
        · have e' : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT).trans (hin3 hm)
          exact hX4.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
    · exact Pok
  split
  · repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush (by assumption)
  · step with obj.Tcb.fault_type.any as ⟨i1, _⟩
    repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush (by assumption)
      | exact Pdon (by assumption)
      | exact Pok



/-- **[P] The message transfer writes no SC `REPLY` or `TCB` word.** P1's
transfer footprint `XferW` (premise `XferFootOK`) admits any SC word
(`InSC`): a timeout-fault message resets the faulting SC's `CONSUMED`.
The real transfer (`ipc::do_ipc_transfer`: registers, IPC buffer, cap
transfer, fault message) never writes an SC's reply-stack head or bound
thread; P1 does not separate these words, so the stall's exclusion layer
(`PrW`: the SC links are protected in no-donation mode) takes it as a
premise. -/
def XferHdr {S : Type _} (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Scs : Set U64) : Prop :=
  ∀ (s : S) (a : A) (snd ep badge : U64) (grant : Bool) (rcv : U64),
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) ∧ L.mem s' (scTcbA c) = L.mem s (scTcbA c) ⦄

/-- A `KWN`/`IpcWN` footprint keeps the `STATE` of the protected threads. -/
theorem IpcFootN.stK {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') (hT : TcbPlaced T) {y : U64}
    (hyT : y ∈ T) (hy : y ∈ Kp) : L.mem s' (stA y) = L.mem s (stA y) :=
  f.idKeep (by rw [stA_eq]; exact field_aligned (hT y hyT) (by simp) (by simp))
    (Or.inr (Or.inl ⟨y, hyT, hT y hyT, hy, rfl⟩))

/-- In no-donation mode an `IpcWN` footprint keeps the current thread. -/
theorem IpcFootN.curK {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') (hNd : Nd)
    (NP : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) : L.curW s' = L.curW s := by
  unfold LawfulStore.curW
  rw [nodeAt_of_ksb f.1, f.2.1]
  exact f.idKeep (nodeAt_aligned NP (by rw [curth0]; omega) (by rw [curth0]))
    (Or.inl ⟨_, hc, _, Or.inr (Or.inr (Or.inr ⟨hNd, rfl, by rw [curth0]⟩)), rfl⟩)

/-- **`send_ipc`'s footprint in `IpcWN`** (P1 `send_ipc.foot`). -/
theorem endpoint.send_ipc.footN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)) {RS : S → S → Prop}
    (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok)) (s : S) (a : A)
    (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (hxh : XferHdr st ar Scs)
    (hKt : t ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) (hdK : can_donate = true → ¬ Nd) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s' ⦄ :=
  endpoint.send_ipc.footPN hA hxf s a blocking do_call badge can_grant can_grant_reply can_donate t e Q R h hB hX hS
    hSg hU hc hdon hH hG hKt hKB hdK (fun s' => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s')
    (fun _ _ p f => IpcFootN.trans p (FootDN.ipc f)) (IpcFootN.refl s)
    fun Ac' X Q' R' s1 a' snd ep badge' grant rcv hs hr h1 hB1 hX1 hS1 hSg1 hU1 F1 hG1 =>
      WP.spec_mono (WP.spec_and (hxw Ac' X Q' R' s1 a' snd ep badge' grant rcv hs hr h1 hB1 hX1 hS1 hSg1 hU1
        (hRSK s s s1 hRS0 F1.foot) hG1) (hxh s1 a' snd ep badge' grant rcv))
        fun s2 hh => (FootN.ipc F1).trans (XferW.ipcN h1 hX1 hU1 hSg1.sub hh.1.1 hh.2)

/-- **A timeout fault's footprint in `IpcWN`** (P1 `handle_timeout.foot`). -/
theorem faults.handle_timeout.footN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (hxf : XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok)) {RS : S → S → Prop}
    (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok)) {Ac : Set U64} (s : S) (a : A)
    (t : obj.Tcb) (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (hxh : XferHdr st ar Scs)
    (hKt : t ∉ Kp) (hKT : ∀ y ∈ Kp, y ∈ T) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) :
    faults.handle_timeout st ar s a t f ⦃ s' _ => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s' ⦄ := by
  have ht := hc.mem
  unfold faults.handle_timeout
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s r.2.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 (IpcFootN.refl s) | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    have q0 := h.1.choose_spec.choose_spec
    refine WP.spec_bind (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.kwN (Cs := Cs) (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s t f q0.tcbs q0.nodes ht)) ?_
    rintro s1 ⟨⟨h1, hU1, hc1⟩, F1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.footN (Nd := Nd) hA hxf hxw s1 a true false b g gr false t p Q1 R1 q1 hB1 hX1 hS1
      hSg1 hU1 hc1 (fun e => by cases e) hpH hRSK (hRSK s s s1 hRS0 F1.foot) (hG.foot F1.foot) hxh hKt
      (fun y hy => by
        rw [IpcFootN.stK (Ω := Ω) (U := U) (Es := EH H) (FootN.ipc F1) q0.tcbs (hKT y hy) hy]; exact hKB y hy)
      (fun e => by cases e)) ?_
    rintro ⟨s2, a1⟩ h2
    exact (WP.spec_ok _).2 ((FootN.ipc F1).trans (by simpa using h2))
  · rintro ⟨x, s2, a2⟩ h2
    exact (WP.spec_ok _).2 h2

/-- The states a budget check from `s0` passes: `XG` states reached by an
`IpcWN` footprint. -/
def GN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) (s0 s : S) : Prop :=
  XG st T Cs Ω H Sg Scs Z P3Ok s ∧ IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s0 s

/-- `GN s0` is kept by `KWN` steps. -/
theorem GN.foot {s0 s1 s2 : S} (g : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s1)
    (f : FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2) : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s2 :=
  ⟨g.1.foot f.foot, g.2.trans (FootN.ipc f)⟩

theorem GN.refl {s0 : S} (g : XG st T Cs Ω H Sg Scs Z P3Ok s0) : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s0 :=
  ⟨g, IpcFootN.refl s0⟩

/-- **Timeout faults keep `GN s0`** (P1's `TmoKG` at `GN s0`), with the named
premise `hRSX` [P]: the transfer relation `RS` holds at the `XG` / `BXI`
states (P1's `hRS0`, per state). -/
theorem tmoKG_N {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (TX : TmoXG st ar) {RS : S → S → Prop}
    (hxw : XferFootOK st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRSX : ∀ (Ac : Set U64) (s : S), XG st T Cs Ω H Sg Scs Z P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → RS s s)
    (hxh : XferHdr st ar Scs) (hNd : Nd) (hKT : ∀ y ∈ Kp, y ∈ T)
    (Ac : Set U64) (s0 : S) (hKc : L.curW s0 ∉ Kp) (hKB0 : ∀ y ∈ Kp, ¬ Blocked (L.mem s0 (stA y)))
    (NP0 : NodePlaced st T s0 (L.cpu s0)) (hc0 : L.cpu s0 ∈ Cs) :
    TmoKG st ar T Cs Ω H Sg Rp Scs Nt Z Ac (GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0) :=
  fun s a f Q R h hB hX hSg hS hG => by
    have hKt : L.curW s ∉ Kp := by rw [hG.2.curK hNd NP0 hc0]; exact hKc
    have hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)) := fun y hy => by
      rw [hG.2.stK h.tcbs (hKT y hy) hy]; exact hKB0 y hy
    have hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h⟩, hB, hX, hSg, hS⟩
    obtain ⟨hc, hU, hcap⟩ := E.tmoOK Ac s hG.1 hb
    have hk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩
    refine WP.spec_mono (WP.spec_and (WP.spec_and (faults.handle_timeout.bxi hA E.xfer s a _ f
      (XG.faultG hG.1 hk hU hc) hk hU hc (hcap _ (Or.inl rfl)))
      (TX T Cs Ω H Sg Rp Scs Nt Z U P3Ok E.xfer Ac s a _ f hG.1 hk hU hc (hcap _ (Or.inl rfl))))
      (faults.handle_timeout.footN (Nd := Nd) hA E.xfer hxw s a _ f hk hU hc (hcap _ (Or.inl rfl)) hRSK
        (hRSX Ac s hG.1 hb) hG.1 hxh hKt hKT hKB)) ?_
    rintro ⟨s', a'⟩ hr
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨BlkOK.bxi hr.1.1, hr.1.2, hG.2.trans hr.2⟩

end

end Fl4Proofs.P1
