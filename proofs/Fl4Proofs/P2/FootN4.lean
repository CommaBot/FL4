/-
P2 (p2j, KWN step 4): **`send_ipc`'s step lemmas in `KWN`** (P1
`QueueIpcFoot`'s, mirrored; P1 untouched): `FootDN` (`FootD` without node
identity words) and its API, `notIdW_dbg`, `EpFoot.kwN`,
`set_blocked_on_reply.kwN`, `set_fault.kwN`, `blkfoot_footN`,
`send_block.footN`, `send_ipc.blockFootN`, `send_tail.footN`,
`donate.kwIN`, `reply_push.kwN`. No premise.
-/
import Fl4Proofs.P2.FootN2
import Fl4Proofs.P1.QueueIpcFoot
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64} {Kp : Set U64} {Nd : Prop}

/-- A footprint inside `KW` and the debug-list words, without node identity
words. -/
abbrev FootDN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesA st T Kp s s' (fun b => (KW st T Cs Sg Scs Z Es s b ∨ DbgW st T Cs s b) ∧ ¬ IdW st Kp Nd T Cs Scs s b)

theorem notIdW_ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : ¬ IdW st Kp Nd T Cs Scs s0 b) : ¬ IdW st Kp Nd T Cs Scs s1 b :=
  fun hi => h (hi.ksb hk.symm hc.symm)

theorem FootDN.refl (s : S) : FootDN st Kp Nd T Cs Sg Scs Z Es s s := WritesA.refl _ _

theorem FootDN.footD {s s' : S} (h : FootDN st Kp Nd T Cs Sg Scs Z Es s s') : FootD st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono (WritesA.w h) fun _ hb => hb.1

theorem FootDN.trans {s₁ s₂ s₃ : S} (h₁ : FootDN st Kp Nd T Cs Sg Scs Z Es s₁ s₂)
    (h₂ : FootDN st Kp Nd T Cs Sg Scs Z Es s₂ s₃) : FootDN st Kp Nd T Cs Sg Scs Z Es s₁ s₃ :=
  WritesA.mono (WritesA.trans h₁ h₂) fun b hb => by
    rcases hb with hb | ⟨hb, hn⟩
    · exact hb
    · refine ⟨?_, notIdW_ksb h₁.1.symm h₁.2.1.symm hn⟩
      rcases hb with hb | hb
      · exact Or.inl (KW.ksb h₁.1 hb)
      · exact Or.inr (DbgW.ksb h₁.1 hb)

theorem FootDN.of' {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → (KW st T Cs Sg Scs Z Es s b ∨ DbgW st T Cs s b) ∧ ¬ IdW st Kp Nd T Cs Scs s b)
    (hk : AcK st T Kp s s') : FootDN st Kp Nd T Cs Sg Scs Z Es s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh), hk⟩

theorem FootN.d {s s' : S} (f : FootN st Kp Nd T Cs Sg Scs Z Es s s') : FootDN st Kp Nd T Cs Sg Scs Z Es s s' :=
  WritesA.mono f fun _ hb => ⟨Or.inl hb.1, hb.2⟩

theorem FootN.of0 {s s' : S} (f : FootN st Kp Nd T Cs ∅ ∅ Z ∅ s s') (hNd : ¬ Nd) :
    FootN st Kp Nd T Cs Sg Scs Z Es s s' :=
  WritesA.mono f fun b hb => by
    refine ⟨?_, fun h => hb.2 ?_⟩
    swap
    · rcases h with h | h
      · exact Or.inl h
      · rcases h with h | ⟨hn, -⟩
        · exact Or.inr (Or.inl h)
        · exact absurd hn hNd
    rcases hb.1 with h | h | hm | ⟨c, hc, -⟩ | ⟨e, he, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd hm (Set.notMem_empty _)
    · exact absurd hc (Set.notMem_empty _)
    · exact absurd he (Set.notMem_empty _)

/-- A `FootN` write of a TCB field after a `FootN` step. -/
theorem FootN.field {s s₁ : S} {y K v : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (hcpu : L.cpu s ∈ Cs) (f : FootN st Kp Nd T Cs Sg Scs Z Es s s₁) (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) (hx : PrF Kp Nd y K := by xf_auto) :
    FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s₁ (core.num.U64.wrapping_add y K) v) :=
  f.trans (footN_field hT (fun c hc => (NP c hc).ksb f.1) (by rw [f.2.1]; exact hcpu) hy hK hK' hK8 hKd hx)

/-- The debug-list words are no node identity words. -/
theorem notIdW_dbg {s : S} {b : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (h : DbgW st T Cs s b) : ¬ IdW st Kp Nd T Cs Scs s b := by
  rcases h with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩ <;> subst e
  · exact notIdW_field hT NP hy (by simp)
  · exact notIdW_field hT NP hy (by simp)
  · exact notIdW_node NP hc (by simp [debug_val]) (idOff_ge (by simp [debug_val]))

/-- The SC header words are in `Ω` (under `Nd`). -/
def HdrΩ (Nd : Prop) (Ω Scs : Set U64) : Prop := Nd → ∀ c ∈ Scs, scReplyA c ∈ Ω ∧ scTcbA c ∈ Ω

theorem hdrΩ_of {s : S} (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) : HdrΩ Nd Ω Scs :=
  fun _ c hc => ⟨hsub _ (hX.1.repW c hc), hsub _ (hX.1.fixW c hc).1⟩

/-- An endpoint's words are no node identity or protected words. -/
theorem notIdW_ep {s : S} {e b : U64} (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hE : EpPlaced T e)
    (hEN : EpOutNodes st Cs s e) (hEΩ : ∀ a ∈ Ω, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val) (hHΩ : HdrΩ Nd Ω Scs)
    (hb : b = epHeadA e ∨ b = epTSA e) : ¬ IdW st Kp Nd T Cs Scs s b := by
  have hv : b.val = e.val ∨ b.val = e.val + 8 := by
    rcases hb with rfl | rfl
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE)
  rintro (h | h)
  · obtain ⟨c, hc, o, -, ho, e'⟩ := h.lt
    rw [e', nodeAt_val (NP c hc) (by omega)] at hv
    have := hEN.1 c hc
    omega
  · rcases h with ⟨y', hy', hya', -, e' | e'⟩ | ⟨hn, ⟨y', hy', hya', e' | e'⟩ | ⟨c, hc, e' | e', -⟩ | ⟨y', hy', hya', e'⟩⟩
    · rw [e', stA_eq, field_val hya' (by decide)] at hv; have := hE.disj y' hy'; simp at hv; omega
    · rw [e', inqA_eq, field_val hya' (by decide)] at hv; have := hE.disj y' hy'; simp at hv; omega
    · rw [e', scA_eq, field_val hya' (by decide)] at hv; have := hE.disj y' hy'; simp at hv; omega
    · rw [e', affA_eq, field_val hya' (by decide)] at hv; have := hE.disj y' hy'; simp at hv; omega
    · have := hEΩ _ (hHΩ hn c hc).1; rw [← e'] at this; omega
    · have := hEΩ _ (hHΩ hn c hc).2; rw [← e'] at this; omega
    · rw [e', field_val hya' (by decide)] at hv; have := hE.disj y' hy'; simp at hv; omega

theorem EpFoot.kwN {s : S} {W : List U64} {e b : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (hW : ∀ w ∈ W, w ∈ T) (he : e ∈ Es) (hE : EpPlaced T e) (hEN : EpOutNodes st Cs s e)
    (hEΩ : ∀ a ∈ Ω, a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val) (hHΩ : HdrΩ Nd Ω Scs) (h : EpFoot W e b) :
    KWN st Kp Nd T Cs Sg Scs Z Es s b := by
  refine ⟨h.kw hW he, ?_⟩
  rcases h with ⟨w, hw, e' | e'⟩ | e' | e' <;> subst e'
  · rw [nextA_eq']; exact notIdW_field hT NP (hW w hw) (by cases tcbqueue.Link.Ep <;> simp [nextOff])
  · rw [prevA_eq']; exact notIdW_field hT NP (hW w hw) (by cases tcbqueue.Link.Ep <;> simp [prevOff])
  · exact notIdW_ep NP hE hEN hEΩ hHΩ (Or.inl rfl)
  · exact notIdW_ep NP hE hEN hEΩ hHΩ (Or.inr rfl)

/-- An endpoint operation keeps the action. -/
theorem EpFoot.act {s s' : S} {W : List U64} {e : U64} (hT : TcbPlaced T) (NP : ∀ c ∈ Cs, NodePlaced st T s c)
    (hcpu : L.cpu s ∈ Cs) (hW : ∀ w ∈ W, w ∈ T) (hE : EpPlaced T e) (hEN : EpOutNodes st Cs s e)
    (h : WritesIn st s s' (EpFoot W e)) : L.actionW s' = L.actionW s := by
  have hN := NP _ hcpu
  have e16 : layout.node.SCHED_ACTION.val = 16 := act_val
  refine actionW_of h hN ?_
  have ev : ∀ b : U64, b.val = e.val ∨ b.val = e.val + 8 →
      L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ≠ b := fun b hb e' => by
    have := hEN.1 _ hcpu
    rw [← e', nodeAt_val hN (by omega)] at hb
    omega
  rintro (⟨w, hw, e' | e'⟩ | e' | e')
  · rw [nextA_eq'] at e'
    exact node_ne_field hN (by omega) (hW w hw) (hT w (hW w hw)) (by simp [nextOff]) e'
  · rw [prevA_eq'] at e'
    exact node_ne_field hN (by omega) (hW w hw) (hT w (hW w hw)) (by simp [prevOff]) e'
  · exact ev _ (Or.inl epHeadA_val) e'
  · exact ev _ (Or.inr (epTSA_val hE)) e'

section kw
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.set_blocked_on_reply.kwN (s : S) (t r : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T)
    (hKt : t ∉ Kp) :
    sched.set_blocked_on_reply st s t r ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  unfold sched.set_blocked_on_reply
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_reply_obj.wr as ⟨s2, e2⟩
  subst e1 e2
  have f1 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) := by
    rw [stA_eq]; exact footN_field hT h.nodes h.cur ht (by simp) (by simp) (by simp) (by simp) (PrF.of_nk hKt (by simp) (by simp))
  have f2 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr (L.wr s (stA t) sched.TS_BLOCKED_ON_REPLY) (replyA t) r) :=
    FootN.field (K := 3360#u64) hT h.nodes h.cur f1 ht (by simp) (by simp) (by simp) (by simp)
  exact WP.spec_mono (sched.schedule_tcb.kwN _ t hT (fun c hc => (h.nodes c hc).ksb f2.1)
    (by rw [f2.2.1]; exact h.cur)) fun s3 f3 => f2.trans f3

theorem faults.set_fault.kwN (s : S) (t : obj.Tcb) (f : error.Fault) (hT : TcbPlaced T)
    (NP : ∀ c ∈ Cs, NodePlaced st T s c) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) :
    faults.set_fault st s t f ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have W : ∀ {s₁ : S} (K v : U64), FootN st Kp Nd T Cs Sg Scs Z Es s s₁ → 3376 ≤ K.val → K.val < 3432 →
      K.val % 8 = 0 → FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s₁ (core.num.U64.wrapping_add t K) v) :=
    fun K v e h1 h2 h3 => FootN.field hT NP hcpu e ht (by omega) (by omega) h3 (by omega)
  unfold faults.set_fault
  refine WP.spec_bind (Pₘ := fun r : S × U64 × U64 × U64 × U64 => FootN st Kp Nd T Cs Sg Scs Z Es s r.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 (FootN.refl s) | skip
    · refine WP.spec_bind (P0.error.LookupFault.encode.p0 _) ?_
      rintro ⟨lt, l0, l1⟩ -
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (obj.Tcb.set_lf_type.wr s t lt) fun s2 e2 => ?_
      subst e2
      have h2 := W (s₁ := s) 3408#u64 lt (FootN.refl s) (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w0.wr _ t l0) fun s3 e3 => ?_
      subst e3
      have h3 := W 3416#u64 l0 h2 (by simp) (by simp) (by simp)
      refine WP.spec_bind (obj.Tcb.set_lf_w1.wr _ t l1) fun s4 e4 => ?_
      subst e4
      have h4 := W 3424#u64 l1 h3 (by simp) (by simp) (by simp)
      refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ => (WP.spec_ok _).2 h4
      split <;> exact (WP.spec_ok _).2 trivial
    · refine WP.spec_bind (Pₘ := fun _ : U64 => True) ?_ fun i _ =>
        (WP.spec_ok _).2 (FootN.refl s)
      split <;> exact (WP.spec_ok _).2 trivial
  · rintro ⟨s1, ty, w0, w1, w2⟩ hh
    try simp only [uncurry_apply_pair]
    simp only at hh
    refine WP.spec_bind (obj.Tcb.set_fault_type.spec s1 t ty) fun s2 e2 => ?_
    subst e2
    have h2 := W (s₁ := s1) 3376#u64 ty hh (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w0.wr _ t w0) fun s3 e3 => ?_
    subst e3
    have h3 := W 3384#u64 w0 h2 (by simp) (by simp) (by simp)
    refine WP.spec_bind (obj.Tcb.set_fault_w1.wr _ t w1) fun s4 e4 => ?_
    subst e4
    have h4 := W 3392#u64 w1 h3 (by simp) (by simp) (by simp)
    exact WP.spec_mono (obj.Tcb.set_fault_w2.wr _ t w2) fun s5 e5 => by
      subst e5; exact W 3400#u64 w2 h4 (by simp) (by simp) (by simp)

/-- A `BlkFoot` step from `s` (no reply object) inside `KWN`. -/
theorem blkfoot_footN {s s' : S} {t : U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hKt : t ∉ Kp)
    (w : WritesIn st s s' (BlkFoot st s t 0#u64)) (hk : AcK st T Kp s s') : FootN st Kp Nd T Cs Sg Scs Z Es s s' :=
  FootN.of' w (hk := hk) fun b _ hb => by
    rcases hb with ⟨K, hK, rfl⟩ | rfl | ⟨h0, -⟩
    · exact ⟨kw_field ht (by omega) (by omega) (by omega), notIdW_field h.tcbs h.nodes ht (by omega)
        (PrF.of_nk hKt (by omega) (by omega))⟩
    · exact ⟨kw_node h.cur (by rw [act_val]; omega) (by rw [act_val]; omega),
        notIdW_node h.nodes h.cur (by rw [act_val]; omega)
          (idOff_cur (by rw [act_val]; omega) (by rw [act_val]; omega) (fun _ => by rw [act_val]; omega))⟩
    · exact absurd rfl h0

set_option maxHeartbeats 4000000 in
/-- **The blocking send's footprint** in `KWN`. -/
theorem send_block.footN {A : Type _} (s : S) (a : A) (t e badge : U64) (can_grant can_grant_reply do_call : Bool)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : CanBlock st T Ac s t) (hH : H e = some .ep) (hKt : t ∉ Kp) (hHΩ : HdrΩ Nd Ω Scs) :
    (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_SEND
      let s2 ← obj.Tcb.set_block_obj st t s1 e
      let s3 ← obj.Tcb.set_block_badge st t s2 badge
      let i ← if can_grant then ok endpoint.FLAG_GRANT else ok 0#u64
      let i1 ← if can_grant_reply then ok endpoint.FLAG_GRANT_REPLY else ok 0#u64
      let i2 ← lift (i ||| i1)
      let i3 ← if do_call then ok endpoint.FLAG_CALL else ok 0#u64
      let f ← lift (i2 ||| i3)
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  step with obj.Tcb.set_block_badge.wr as ⟨s3, e3⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  have h3 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s3 Q R := by
    rw [e3]; exact inv_wr_fieldX (K := 3344#u64) h2 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w1 : WritesIn st s s1 (BlkFoot st s t 0#u64) := by
    rw [e1]; exact blk_wr_field (K := 3328#u64) hta (WritesIn.refl _ _) (by simp)
  have w3 : WritesIn st s s3 (BlkFoot st s t 0#u64) := by
    rw [e3, e2]; exact blk_wr_field hta (blk_wr_field hta w1 (by simp)) (by simp)
  have key : ∀ f : U64, (do
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ := by
    intro f
    step with obj.Tcb.set_block_flags.wr as ⟨s4, e4⟩
    have h4 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s4 Q R := by
      rw [e4]; exact inv_wr_fieldX (K := 3352#u64) h3 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    have w4 : WritesIn st s s4 (BlkFoot st s t 0#u64) := by rw [e4]; exact blk_wr_field hta w3 (by simp)
    have v4 : L.mem s4 (stA t) = sched.TS_BLOCKED_ON_SEND := by
      rw [e4, fld_wr_ne' hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e3, fld_wr_ne' hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have a4 : L.actionW s4 = L.actionW s := by
      rw [e4, act_wr_field (h3.nodes _ h3.cur) ht hta rfl (by simp) (by simp),
        e3, act_wr_field (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
        e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
        e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
    refine WP.spec_bind (sched.schedule_tcb.blk s4 t h4 (by rw [v4]; exact blocked_not_runnable (Or.inl rfl))) ?_
    rintro s5 ⟨h5, e5, -⟩
    obtain ⟨w5, ha5, -, -, -, -⟩ := blk_sched h4 ht w4 a4 e5
    have k5 : AcK st T Kp s s5 := by
      rcases ha5 with e | e
      · exact AcK.of_eq e
      · exact AcK.of_nT (by rw [e]; exact notT_small h.tcbs (by simp))
    obtain ⟨E, EQ, hEW⟩ := h.eps
    have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
    obtain ⟨hE, hEN, hq⟩ := hEW.1 e heE
    obtain ⟨kf, -, -, ke⟩ := blkfoot_keep h hEW ht (fun h0 => absurd rfl h0) w5
    have hqe : L.epQ s5 e = L.epQ s e := by simp only [LawfulStore.epQ, (ke e heE).1, (ke e heE).2]
    have hq5 : QueueRel (L.mem s5) T .Ep (L.epQ s5 e) (EQ e) :=
      ⟨hq.nodup, hq.mem, by rw [hqe]; exact hq.head, by rw [hqe]; exact hq.last, hq.seg.congr fun y hy =>
        ⟨kf y (hq.mem y hy) (prevOff .Ep) (by simp [prevOff]) (by simp [prevOff]) (fun _ => by simp [prevOff]),
         kf y (hq.mem y hy) (nextOff .Ep) (by simp [nextOff]) (by simp [nextOff]) (fun _ => by simp [nextOff])⟩⟩
    have hn : t ∉ EQ e := fun hm => hc.nb (hEW.2.2.2.1 e heE t hm).2.2
    refine WP.spec_bind (endpoint.ep_append.foot s5 e t obj.EP_SEND (EQ e) h.tcbs hE hq5 ht hn) fun s6 w6 => ?_
    have F5 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s s5 := blkfoot_footN h ht hKt w5 k5
    have hW : ∀ w ∈ t :: EQ e, w ∈ T := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ht
      · exact hq.mem w hw
    have A6 : L.actionW s6 = L.actionW s5 := EpFoot.act h5.tcbs h5.nodes h5.cur hW hE
      (by obtain ⟨a, b⟩ := hEN; exact ⟨fun c hc => by
            have e' : L.nodeBase s5 c = L.nodeBase s c := by simp [LawfulStore.nodeBase, F5.1]
            rw [e']; exact a c hc, by first | exact b | (rw [F5.1]; exact b)⟩) w6
    refine (WP.spec_ok _).2 (F5.trans (FootN.of' w6 (hk := AcK.of_eq A6) fun b _ hb => ?_))
    have k := EpFoot.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) h.tcbs h.nodes hW (Or.inl hH) hE hEN (hEW.2.2.1 e heE) hHΩ hb
    exact ⟨KW.ksb F5.1.symm k.1, notIdW_ksb F5.1 F5.2.1 k.2⟩
  cases can_grant <;> cases can_grant_reply <;> cases do_call <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok, lift] <;> exact key _

/-- **`send_ipc`'s footprint on an idle or sending endpoint** in `KWN`. -/
theorem endpoint.send_ipc.blockFootN {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : blocking = true → CanBlock st T Ac s t)
    (hH : H e = some .ep) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 1#u64) (hKt : t ∉ Kp) (hHΩ : HdrΩ Nd Ω Scs) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z (EH H) s s' ⦄ := by
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · split
    · exact send_block.footN s a t e badge can_grant can_grant_reply do_call h (hc ‹_›) hH hKt hHΩ
    · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootN.refl _
  · split
    · split
      · exact send_block.footN s a t e badge can_grant can_grant_reply do_call h (hc ‹_›) hH hKt hHΩ
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact FootN.refl _
    · exfalso
      rename_i h1 h2
      rw [ep_idle_val] at h1; rw [ep_send_val'] at h2
      rcases hst0 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction

set_option maxHeartbeats 1000000 in
/-- **`donate`'s footprint** in `KWN` (P1 `donate.kwI`). -/
theorem schedcontext.donate.kwIN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc dst : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) {s0 : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s0)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hD : DbgTz st T Cs s) (hcore : L.mem s (scCoreA sc) ∈ Cs)
    (hsc : sc ∈ Scs) (hdst : dst ∈ T) (hNd : ¬ Nd) (hKa : ActOut st T Kp s)
    (hi : L.mem s (scTcbA sc) ≠ 0#u64 → L.mem s (scTcbA sc) ∈ T ∧
      (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_QUEUED) = 0#u64 ∧
      (L.mem s (inqA (L.mem s (scTcbA sc))) &&& sched.Q_RELEASE) = 0#u64) :
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
    obtain ⟨hiT, hiq, hir⟩ := hi (by rw [← ei]; exact hi0)
    rw [← ei] at hiT hiq hir
    refine WP.spec_bind (smp.remote_tcb_stall.spec hA s a i) ?_
    rintro ⟨s2, a2⟩ hs2
    try simp only [WP.uncurry'_pair] at hs2 ⊢
    have hst : SchedQueuesInvX st T Cs Ω H X s2 Q R ∧ FootN st Kp Nd T Cs ∅ ∅ Z ∅ s s2 ∧
        L.mem s2 (inqA i) = L.mem s (inqA i) := by
      rcases hs2 with rfl | ⟨v, rfl⟩
      · exact ⟨h, FootN.refl _, rfl⟩
      · refine ⟨inv_of_free h (free_node_write rfl h.cur hN' (by rw [ipi_val]; unfold LowFree; omega)),
          footN_node h.nodes h.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) (by rw [ipi_val]; omega)
            (idOff_ge (by rw [ipi_val]; omega)) h.cur (by rw [ipi_val]; omega), ?_⟩
        rw [inqA_eq]; exact field_wr_node h h.cur (by rw [ipi_val]; omega) (by rw [ipi_val]) hiT (by simp) (by simp)
    obtain ⟨q2, f2, iq2⟩ := hst
    refine WP.spec_bind (sched.dequeue.noop s2 i (by rw [iq2]; exact hiq)) fun s3 e3 => ?_
    subst s3
    refine WP.spec_bind (sched.release_remove.noop s2 i (by rw [iq2]; exact hir)) fun s4 e4 => ?_
    subst s4
    step with obj.Tcb.set_sc.wr as ⟨s5, e5⟩
    subst e5
    have q5 := inv_wr_field (K := 3464#u64) (v := 0#u64) q2 hiT (by simp) (by simp) (by simp)
    have f05 : FootN st Kp Nd T Cs ∅ ∅ Z ∅ s (L.wr s2 (scA i) 0#u64) := by
      rw [scA_eq]; exact FootN.field hT h.nodes h.cur f2 hiT (by simp) (by simp) (by simp) (by simp)
        ⟨fun _ => by simp, fun h => absurd h hNd⟩
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    refine WP.spec_bind (Pₘ := fun s6 => FootN st Kp Nd T Cs ∅ ∅ Z ∅ (L.wr s2 (scA i) 0#u64) s6 ∧
        ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s6 Q1 R1) ?_
      fun s6 ⟨f6, q6⟩ => (WP.spec_ok _).2 ⟨f05.trans f6, q6⟩
    have RR : sched.reschedule_required st (L.wr s2 (scA i) 0#u64) ⦃ s6 =>
        FootN st Kp Nd T Cs ∅ ∅ Z ∅ (L.wr s2 (scA i) 0#u64) s6 ∧ ∃ Q1 R1, SchedQueuesInvX st T Cs Ω H X s6 Q1 R1 ⦄ :=
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


set_option maxHeartbeats 4000000 in
/-- **`reply_push`'s footprint** in `KWN` (P1 `reply_push.kw`). -/
theorem ipc.reply_push.kwN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (caller callee r : U64) (can_donate : Bool)
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hXc : ExcT X caller)
    (hx : caller ∈ X ∨ ¬ Blocked (L.mem s (stA caller)))
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hcl : caller ∈ T) (hcq : (L.mem s (inqA caller) &&& sched.Q_QUEUED) = 0#u64)
    (hcr : (L.mem s (inqA caller) &&& sched.Q_RELEASE) = 0#u64) (hca : L.actionW s ≠ caller)
    (hci : L.idleW s ≠ caller)
    (hcold : L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA caller) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr : r ∈ Rp) (hr00 : r ≠ 0#u64) (hr0 : L.mem s (rTcbA r) = 0#u64) (hce : callee ∈ T)
    (hcA : L.mem s (scA caller) ≠ 0#u64 → L.mem s (scA caller) ∈ Ac) (hKc : caller ∉ Kp)
    (hdK : can_donate = true → ¬ Nd) (hKa : ActOut st T Kp s) :
    ipc.reply_push st ar s a caller callee r can_donate ⦃ s' _ => FootDN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hT := h.tcbs
  have hO := hX.1
  have hsub := hSg.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  obtain ⟨r32, rt0, rp8, rn16⟩ := rp_facts hO hr
  unfold ipc.reply_push
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  step with obj.Reply.set_tcb.spec as ⟨s1, e1⟩
  subst e1
  have f1 : FootN st Kp Nd T Cs Sg Scs Z Es s (L.wr s (rTcbA r) caller) :=
    footN_wr (h.omega _ (hrΩ r hr).1).1 ⟨kw_sg (hO.tcbW hr), notIdW_out h.nodes (h.omega _ (hrΩ r hr).1)
      (noHdr_rp hO hr (by rw [rt0]) (by rw [rt0]; omega))⟩ (actionW_out h.nodes h.cur (h.omega _ (hrΩ r hr).1))
  have q1 := (omega_wr (v := caller) h (hrΩ r hr).1).1
  refine WP.spec_bind (WP.spec_and (sched.set_blocked_on_reply.ipc s caller r Q R h hXc hx hB hX hS hSg hcl hcq hcr
    hca hci hcold hr hr00 hr0 hcA)
    (sched.set_blocked_on_reply.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) _ caller r q1 hcl hKc)) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, f2', o2, -, -, -, -⟩, f2⟩
  have f02 := f1.trans f2
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 f02.d
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hci0 : L.mem s (scA caller) ≠ 0#u64 := by rw [← ei]; exact hi0
  obtain ⟨hiS, hitc, -⟩ := hX.2.2.bound caller hcl hci0
  rw [← ei] at hiS hitc
  obtain ⟨h128, tv, cv, -, -, -, rv, -⟩ := sc_facts hO hiS
  have hti : (scTcbA i).val ≠ (rTcbA r).val := by
    rw [tv, rt0]; have := hO.rpSc r hr i hiS; omega
  have hci : (scCoreA i).val ≠ (rTcbA r).val := by
    rw [cv, rt0]; have := hO.rpSc r hr i hiS; omega
  have hal : Aligned (scTcbA i) := (h.omega _ (hcΩ i hiS).1).1
  have hcal : Aligned (scCoreA i) := (h.omega _ (hcΩ i hiS).2.1).1
  have tc2 : L.mem s2 (scTcbA i) = caller := by
    rw [o2 _ (hcΩ i hiS).1 (fun e => hti (congrArg UScalar.val e))]
    exact hitc
  have cc2 : L.mem s2 (scCoreA i) = L.mem s (scCoreA i) :=
    o2 _ (hcΩ i hiS).2.1 (fun e => hci (congrArg UScalar.val e))
  -- what the reply and SC writes keep
  let P : S → Prop := fun s' => SchedQueuesInvX st T Cs Ω H ∅ s' Q R ∧ FootN st Kp Nd T Cs Sg Scs Z Es s s' ∧
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K)) ∧
    L.mem s' (scTcbA i) = caller ∧ DbgTz st T Cs s' ∧ L.mem s' (scCoreA i) = L.mem s (scCoreA i)
  have W : ¬ Nd → ∀ (s' : S) (b v : U64), P s' → b ∈ Sg → (scTcbA i).val ≠ b.val → (scCoreA i).val ≠ b.val →
      P (L.wr s' b v) := by
    intro hnd s' b v ⟨q, f, k, c, D, cc⟩ hb hne hne'
    obtain ⟨q', -, k'⟩ := omega_wr (v := v) q (hsub b hb)
    have hbo := q.omega _ (hsub b hb)
    have hba := hbo.1
    exact ⟨q', f.trans (footN_wr hba ⟨kw_sg hb, notIdW_out q.nodes hbo (NoHdr.of_not hnd)⟩ (actionW_out q.nodes q.cur hbo)), fun y hy K h1 h2 => (k' y hy K h1 h2).trans (k y hy K h1 h2),
      by rw [L.mem_wr_ne hba hal (Ne.symm hne)]; exact c,
      DbgTz.wr_out q.tcbs q.nodes hba (notDbgW_out q.tcbs q.nodes hbo) D,
      by rw [L.mem_wr_ne hba hcal (Ne.symm hne')]; exact cc⟩
  have P2 : P s2 := ⟨h2, f02, fun _ _ _ _ _ => rfl, tc2, hX2.dbg, cc2⟩
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · split
    · step with obj.Sc.reply.val as ⟨i2, ei2⟩
      have hnd : ¬ Nd := hdK (by assumption)
      have hi2 : i2 ≠ 0#u64 → i2 ∈ Rp := fun h0 => by rw [ei2] at h0 ⊢; exact hX2.2.1.screp i hiS h0
      refine WP.spec_bind (Pₘ := P) ?_ fun s3 p3 => ?_
      · split
        · rename_i hne
          have h0 : i2 ≠ 0#u64 := by simpa using hne
          have hp := hi2 h0
          refine WP.spec_mono (obj.Reply.set_next.val0 s2 i2 r) fun s3 e3 => ?_
          subst e3
          obtain ⟨-, -, -, n16⟩ := rp_facts hO hp
          exact W hnd _ _ _ P2 (hO.nextW hp) (by rw [tv, n16]; have := hO.rpSc i2 hp i hiS; omega)
            (by rw [cv, n16]; have := hO.rpSc i2 hp i hiS; omega)
        · exact (WP.spec_ok _).2 P2
      refine WP.spec_bind (obj.Reply.set_prev.val s3 r i2) fun s4 e4 => ?_
      subst e4
      have p4 := W hnd _ _ (i2 &&& ~~~1#u64) p3 (hO.prevW hr) (by rw [tv, rp8]; have := hO.rpSc r hr i hiS; omega)
        (by rw [cv, rp8]; have := hO.rpSc r hr i hiS; omega)
      refine WP.spec_bind (obj.Sc.set_reply.spec _ i r) fun s5 e5 => ?_
      subst e5
      have p5 := W hnd _ _ r p4 (hO.repW i hiS) (by rw [tv, rv]; omega) (by rw [cv, rv]; omega)
      refine WP.spec_bind (obj.Reply.set_next.val1 _ r i) fun s6 e6 => ?_
      subst e6
      have p6 := W hnd _ _ ((i &&& ~~~1#u64) ||| 1#u64) p5 (hO.nextW hr)
        (by rw [tv, rn16]; have := hO.rpSc r hr i hiS; omega)
        (by rw [cv, rn16]; have := hO.rpSc r hr i hiS; omega)
      obtain ⟨q6, f6, k6, c6, D6, cc6⟩ := p6
      have iq : ∀ s', (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add y K) = L.mem s2 (core.num.U64.wrapping_add y K)) →
          L.mem s' (inqA caller) = L.mem s (inqA caller) := fun s' k => by
        rw [inqA_eq, k caller hcl _ (by simp) (by simp)]
        exact f2' caller hcl _ (by simp) (by simp) (fun _ => ⟨by simp, by simp, by simp, by simp, by simp⟩)
      refine WP.spec_mono (schedcontext.donate.kwIN (Es := Es) hA _ a i callee q6 hO hsub D6
        (by rw [cc6]; exact hX.2.2.core i hiS) hiS hce hnd (f6.out hKa) fun _ => ?_)
        fun r' f' => f6.d.trans f'
      rw [c6]
      exact ⟨hcl, by rw [iq _ k6]; exact hcq, by rw [iq _ k6]; exact hcr⟩
    · exact (WP.spec_ok _).2 f02.d
  · exact (WP.spec_ok _).2 f02.d

end kw

/-- `send_tail`'s footprint in `KWN`. -/
theorem send_tail.footN {X : Set U64} (s4 : S) {A : Type _} (a1 : A) (hd : U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (h4 : SchedQueuesInvX st T Cs Ω H X s4 Q R) (hB4 : BoundInv st T Ac s4)
    (hX4 : XInv st T Cs Ω Sg Rp Scs Nt Z s4) (hS4 : SCsOK st T Ω Sg Scs Z Ac s4) (hSg4 : SgOK st Ω Sg s4) (hdT : hd ∈ T)
    (hXc : ExcT X hd) (hx : hd ∈ X ∨ ¬ Blocked (L.mem s4 (stA hd))) (hnr : ∀ r ∈ Rp, L.mem s4 (rTcbA r) ≠ hd)
    (hdA : L.mem s4 (scA hd) ≠ 0#u64 → L.mem s4 (scA hd) ∈ Ac) (hKd : hd ∉ Kp) (hKa : ActOut st T Kp s4) :
    (do
      let s5 ← sched.set_thread_state st s4 hd sched.TS_RUNNING
      let s6 ← endpoint.unblock_sporadic st s5 hd
      let s7 ← sched.possible_switch_to st s6 hd
      ok (s7, a1)) ⦃ s' _ => FootN st Kp Nd T Cs Sg Scs Z Es s4 s' ⦄ := by
  refine WP.spec_bind (WP.spec_and (sts_all s4 hd _ Q R h4 hB4 hX4 hS4 hSg4 hdT not_blocked_running running_ne hx hnr
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s4 hd _ h4 hdT hKd)) fun s5 hh' => ?_
  obtain ⟨hh, f5⟩ := hh'
  obtain ⟨h5, hB5, hX5, hS5, hSg5, e5, k5⟩ := hh
  have h5' := h5.congrX (excT_congr hXc)
  refine WP.spec_bind (WP.spec_and (endpoint.unblock_sporadic.all s5 hd h5' hB5 hX5 hS5 hSg5 hdT)
    (endpoint.unblock_sporadic.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s5 hd h5' hX5 hS5 hdT)) fun s6 hh' => ?_
  obtain ⟨hh, f6⟩ := hh'
  obtain ⟨h6, -⟩ := hh
  refine WP.spec_bind (sched.possible_switch_to.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := Es) s6 hd h6 hdT hKd (f6.out (f5.out hKa)))
    fun s7 f7 => (WP.spec_ok _).2 (f5.trans (f6.trans f7))


end

end Fl4Proofs.P1
