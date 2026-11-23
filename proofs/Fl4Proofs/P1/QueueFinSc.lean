/-
P1: the SchedContext branch of `finalise_cap` (unbind the thread, the
notification and the reply, complete a pending yield, deactivate) keeps the
invariants and has a `KW` footprint.
-/
import Fl4Proofs.P1.QueueFinal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- Two words at offsets `o1 ≠ o2` below 128 of SC objects differ. -/
theorem scw_ne {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c p a b : U64} (hc : c ∈ Scs) (hp : p ∈ Scs)
    {o1 o2 : Nat} (ha : a.val = c.val + o1) (hb : b.val = p.val + o2) (h1 : o1 < 128) (h2 : o2 < 128)
    (hne : o1 ≠ o2) : a.val ≠ b.val := by
  have := (sc_facts hO hc).1; have := (sc_facts hO hp).1
  by_cases e : c = p
  · subst e; omega
  · have := hO.scDisj c hc p hp e; omega

/-! ## The SC words the tail of the SC finalisation relies on -/

/-- The `TCB` and `NTFN` words of the SC `p` and the current SC word are kept,
and a null `REPLY` word of `p` stays null. -/
def SKeep (st : machine.Store S) [L : LawfulStore st] (p : U64) (s s' : S) : Prop :=
  L.mem s' (scTcbA p) = L.mem s (scTcbA p) ∧ L.mem s' (scNtfnA p) = L.mem s (scNtfnA p) ∧ L.cscW s' = L.cscW s ∧
    (L.mem s (scReplyA p) = 0#u64 → L.mem s' (scReplyA p) = 0#u64)

theorem SKeep.refl (p : U64) (s : S) : SKeep st p s s := ⟨rfl, rfl, rfl, id⟩
theorem SKeep.trans {p : U64} {s₁ s₂ s₃ : S} (h₁ : SKeep st p s₁ s₂) (h₂ : SKeep st p s₂ s₃) : SKeep st p s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, fun h => h₂.2.2.2 (h₁.2.2.2 h)⟩

/-- A write of a word of `Ω` other than `p`'s `TCB` and `NTFN` words. -/
theorem SKeep.wr_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {p a v : U64}
    (h0 : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hp : p ∈ Scs) (ha : a ∈ Ω) (h1 : a.val ≠ (scTcbA p).val) (h2 : a.val ≠ (scNtfnA p).val)
    (h3 : a.val ≠ (scReplyA p).val) :
    SKeep st p s (L.wr s a v) :=
  ⟨L.mem_wr_ne (h0.omega a ha).1 (h0.omega _ (hsub _ (hO.fixW p hp).1)).1 h1,
    L.mem_wr_ne (h0.omega a ha).1 (h0.omega _ (hsub _ (hO.snW p hp))).1 h2, cscW_wr_out h0 ha,
    fun h0' => by rw [L.mem_wr_ne (h0.omega a ha).1 (h0.omega _ (hsub _ (hO.repW p hp))).1 h3]; exact h0'⟩

/-- A TCB field write, given where `p`'s words lie (in some state `s0`). -/
theorem SKeep.wr_field {s s0 : S} {p y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s))
    (o1 : OutsideObjs st T Cs s0 (scTcbA p)) (o2 : OutsideObjs st T Cs s0 (scNtfnA p))
    (o3 : OutsideObjs st T Cs s0 (scReplyA p)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) : SKeep st p s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  ⟨L.mem_wr_ne (field_aligned (hT y hy) hK hK8) o1.1 (out_ne_field o1 hy (hT y hy) hK),
    L.mem_wr_ne (field_aligned (hT y hy) hK hK8) o2.1 (out_ne_field o2 hy (hT y hy) hK),
    cscW_wr_field hT hN hy hK hK8,
    fun h0 => by rw [L.mem_wr_ne (field_aligned (hT y hy) hK hK8) o3.1 (out_ne_field o3 hy (hT y hy) hK)]; exact h0⟩

/-! ## `unbind_reply` -/

theorem zero_link : ((0#u64 &&& ~~~1#u64) ||| 0#u64) = 0#u64 := by decide

/-- Clearing a reply's `NEXT` word. -/
theorem rnext_zero_all {s : S} {r : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (rNextA r) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (rNextA r) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨r32, -, -, av⟩ := rp_facts hO hr
  have hm : rNextA r ∈ Ω := hSg.sub _ (hO.nextW hr)
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := 0#u64) h0 hB hX hS hSg hm
    (fun r' hr' => by
      obtain ⟨r32', e1, -, -⟩ := rp_facts hO hr'
      rw [av, e1]; omega)
    (fun c hc => by
      obtain ⟨h128, e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc
      rw [av, e1, e2, e3, e4, e5]; have := hO.rpSc r hr c hc; omega)
    (fun _ _ _ h0 => absurd (by decide) h0) (fun _ _ _ h0 => absurd (by decide) h0)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (fun c hc e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      rw [av, scNtfnA_val hPc hzc]; have := hO.rpSc r hr c hc; have := (sc_facts hO hc).1; omega))
    (fun _ _ _ => Tz.zero) (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (rword_ne_spor hO hr (by rw [av]; omega))
    (fun _ _ _ _ h => absurd (by simp) h)
    (fun c hc e => absurd e (rword_ne_screp hO hr (by rw [av]; omega) c hc))
    (BndS.wr_rpw hX.2.2.toScExtra0 h0 hO hSg.sub hm hr ⟨by rw [av]; omega, by rw [av]; omega⟩)
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, foot_wr (h0.omega _ hm).1 (kw_sg (hO.nextW hr))⟩

/-- Clearing an SC's `REPLY` word. -/
theorem screp_zero_all {s : S} {c : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs)
    (hnoh : ∀ r ∈ Rp, headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
      L.mem s (rNextA r) &&& ~~~1#u64 ≠ c) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (scReplyA c) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s (L.wr s (scReplyA c) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  have av := scReplyA_val hP hz
  obtain ⟨h128, -⟩ := sc_facts hO hc
  have hm : scReplyA c ∈ Ω := hSg.sub _ (hO.repW c hc)
  obtain ⟨h1, hB1, hX1, hS1, hSg1, -⟩ := link_allT (w := 0#u64) h0 hB hX hS hSg hm
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' => by
      obtain ⟨h128', e1, e2, e3, e4, e5, -⟩ := sc_facts hO hc'
      rw [av, e1, e2, e3, e4, e5]
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.rpSc r hr c hc; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.rpSc r hr c hc; omega)
    (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (fun c' hc' e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c' hc'
      exact scw_ne hO hc hc' av (scNtfnA_val hPc hzc) (by omega) (by omega) (by omega)))
    (fun _ _ _ => Tz.zero) (fun _ _ _ h0 => absurd rfl h0) (fun _ _ _ h0 => absurd rfl h0)
    (scw_ne_spor hO hc av (by omega) (by omega))
    (fun _ _ _ _ h => absurd (by simp) h)
    (fun c' hc' e r hr hb hz ec => by
      have : c' = c := by
        by_contra hne
        obtain ⟨-, -, -, -, -, -, e7, -⟩ := sc_facts hO hc'
        rw [av, e7] at e
        have := hO.scDisj c hc c' hc' (Ne.symm hne); have := (sc_facts hO hc').1; omega
      exact absurd (ec.trans this) (hnoh r hr hb hz))
    (BndS.wr_scw (o := 32) hX.2.2.toScExtra0 h0 hO hSg.sub hm hc av (by omega) (by omega))
  exact ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩, foot_wr (h0.omega _ hm).1 (kw_sg (hO.repW c hc))⟩

/-- `unbind_reply` (seL4 `schedContext_unbindReply`, the reply-stack head
side): the head reply's `NEXT` link and the SC's `REPLY` word are cleared. -/
theorem schedcontext.unbind_reply.blk (s : S) (c p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ≠ 0#u64 → c ∈ Scs) (hp : p ∈ Scs) :
    schedcontext.unbind_reply st s c ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ SKeep st p s s' ∧
      (c ≠ 0#u64 → L.mem s' (scReplyA c) = 0#u64) ⦄ := by
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · rename_i hb
    exact (WP.spec_ok _).2 ⟨h, Foot.refl _, SKeep.refl _ _, fun h0 => absurd (by simpa [eb] using hb) h0⟩
  rename_i hb
  have hcS : c ∈ Scs := hc (fun e => hb (by rw [eb, e]; rfl))
  refine WP.spec_bind (obj.Sc.reply.val s c) fun i ei => ?_
  split
  · rename_i hi
    have hiR : i ∈ Rp := by rw [ei]; exact h.2.2.1.2.1.screp c hcS (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (obj.Reply.set_next.val0 s i 0#u64) fun s1 e1 => ?_
    rw [zero_link] at e1
    subst e1
    obtain ⟨h1, f1⟩ := rnext_zero_all h hiR
    refine WP.spec_mono (obj.Sc.set_reply.spec _ c 0#u64) fun s2 e2 => ?_
    subst e2
    have hO := h.2.2.1.1
    have hsub := h.2.2.2.2.sub
    have h0 := h.1.choose_spec.choose_spec
    obtain ⟨h2, f2⟩ := screp_zero_all h1 hcS (fun r hr hb hz ec => by
      by_cases hri : r = i
      · subst hri
        rw [L.mem_wr_same (h0.omega _ (hsub _ (hO.nextW hiR))).1] at hz; exact hz (by simp)
      · have hne : L.mem (L.wr s (rNextA i) 0#u64) (rNextA r) = L.mem s (rNextA r) := by
          refine L.mem_wr_ne (h0.omega _ (hsub _ (hO.nextW hiR))).1 (h0.omega _ (hsub _ (hO.nextW hr))).1 ?_
          rw [(rp_facts hO hiR).2.2.2, (rp_facts hO hr).2.2.2]
          have := (hO.rp r hr).1; have := (hO.rp i hiR).1
          have : r.val ≠ i.val := fun e => hri (UScalar.eq_of_val_eq e)
          omega
        rw [hne] at hb hz ec
        have := h.2.2.1.2.1.head r hr hb hz
        rw [ec, ← ei] at this
        exact hri this.symm)
    have h0' := h1.1.choose_spec.choose_spec
    obtain ⟨hPc, hzc⟩ := hO.sc c hcS
    obtain ⟨hPp, hzp⟩ := hO.sc p hp
    obtain ⟨-, -, -, av⟩ := rp_facts hO hiR
    have hm2 : scReplyA c ∈ Ω := hsub _ (hO.repW c hcS)
    have k2 : SKeep st p (L.wr s (rNextA i) 0#u64) (L.wr (L.wr s (rNextA i) 0#u64) (scReplyA c) 0#u64) :=
      ⟨L.mem_wr_ne (h0'.omega _ hm2).1 (h0'.omega _ (hsub _ (hO.fixW p hp).1)).1
          (scw_ne hO hcS hp (scReplyA_val hPc hzc) (scTcbA_val hPp hzp) (by omega) (by omega) (by omega)),
        L.mem_wr_ne (h0'.omega _ hm2).1 (h0'.omega _ (hsub _ (hO.snW p hp))).1
          (scw_ne hO hcS hp (scReplyA_val hPc hzc) (scNtfnA_val hPp hzp) (by omega) (by omega) (by omega)),
        cscW_wr_out h0' hm2, fun hz => by
          rw [L.mem_wr_val (h0'.omega _ hm2).1 (h0'.omega _ (hsub _ (hO.repW p hp))).1]
          split
          · rfl
          · exact hz⟩
    refine ⟨h2, f1.trans f2, (SKeep.wr_out h0 hO hsub hp (hsub _ (hO.nextW hiR)) ?_ ?_ ?_).trans k2,
      fun _ => L.mem_wr_same (h0'.omega _ hm2).1⟩
    · rw [av, scTcbA_val hPp hzp]; have := hO.rpSc i hiR p hp; have := (sc_facts hO hp).1; omega
    · rw [av, scNtfnA_val hPp hzp]; have := hO.rpSc i hiR p hp; have := (sc_facts hO hp).1; omega
    · rw [av, scReplyA_val hPp hzp]; have := hO.rpSc i hiR p hp; have := (sc_facts hO hp).1; omega
  · rename_i hi
    refine (WP.spec_ok _).2 ⟨h, Foot.refl _, SKeep.refl _ _, fun _ => ?_⟩
    rw [← ei]; apply UScalar.eq_of_val_eq; simpa using hi

/-! ## `complete_yield_to` keeps `SKeep` -/

theorem regSK {s : S} {t r v p : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hr : r.val < 384) (hp : p ∈ Scs) :
    obj.Tcb.set_reg st t s r v ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧
      ANI st s s' ∧ SKeep st p s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.2.sub
  refine WP.spec_mono (WP.spec_and (regW_spec h ht hr) (obj.Tcb.set_reg.wrK s t r v (h0.tcbs t ht) hr)) ?_
  rintro s' ⟨⟨hb, f, n⟩, K, hK, e⟩
  refine ⟨hb, f, n, ?_⟩
  subst e
  exact SKeep.wr_field h0.tcbs (h0.nodes _ h0.cur) (h0.omega _ (hsub _ (hO.fixW p hp).1))
    (h0.omega _ (hsub _ (hO.snW p hp))) (h0.omega _ (hsub _ (hO.repW p hp))) ht (by omega) (by omega)

theorem schedcontext.update_consumed.blkS {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (c p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (hp : p ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧ Foot st T Cs Sg Scs Z ∅ s r.2 ∧ ANI st s r.2 ∧ SKeep st p s r.2 ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.2.sub
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨hPp, hzp⟩ := hO.sc p hp
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add c layout.sc.CONSUMED) := by unfold Aligned; rw [hv, hcv]; omega
  have hin : InSC c (Z c) (core.num.U64.wrapping_add c layout.sc.CONSUMED) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  have hm := hO.scW c hc _ hal hin
  have sk : ∀ v, SKeep st p s (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) := fun v =>
    SKeep.wr_out h0 hO hsub hp hm
      (scw_ne hO hc hp (by rw [hv, hcv]) (scTcbA_val hPp hzp) (by omega) (by omega) (by omega))
      (scw_ne hO hc hp (by rw [hv, hcv]) (scNtfnA_val hPp hzp) (by omega) (by omega) (by omega))
      (scw_ne hO hc hp (by rw [hv, hcv]) (scReplyA_val hPp hzp) (by omega) (by omega) (by omega))
  refine WP.spec_mono (WP.spec_and (schedcontext.update_consumed.blk hA s a c h hc) ?_) fun r hr =>
    ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2⟩
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    refine WP.spec_bind (hA.ticks_to_us a _) fun i _ => ?_
    exact (WP.spec_ok _).2 (sk y)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_bind (hA.ticks_to_us a _) fun i _ => ?_
    exact (WP.spec_ok _).2 (sk 0#u64)

theorem schedcontext.set_consumed.blkS {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (c t p : U64) (wm : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs) (ht : t ∈ T) (hp : p ∈ Scs) :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ∧ SKeep st p s s' ⦄ := by
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.blkS hA s a c p h hc hp) ?_
  rintro ⟨x, s1⟩ ⟨h1, f1, n1, k1⟩
  simp only at h1 f1 n1 k1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s1 true t L.total) fun buf _ => ?_
    refine WP.spec_bind (regSK h1 ht (r := layout.reg.BADGE) (by simp [layout.reg.BADGE, layout.reg.RDI]) hp)
      fun s2 ⟨h2, f2, n2, k2⟩ => ?_
    unfold msg.set_mr
    simp only [show (0#u64 < msg.N_MSG_REGISTERS) = True from by simp [msg.N_MSG_REGISTERS], if_true]
    simp only [msg.msg_register, if_true, Aeneas.Std.bind_ok]
    refine WP.spec_bind (Pₘ := fun r : U64 × S => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2 ∧
        Foot st T Cs Sg Scs Z ∅ s2 r.2 ∧ ANI st s2 r.2 ∧ SKeep st p s2 r.2) ?_ ?_
    · refine WP.spec_bind (regSK h2 ht (r := layout.reg.R10) (by simp [layout.reg.R10]) hp) fun s3 hh => ?_
      simp only [lift, Aeneas.Std.bind_ok, WP.spec_ok]; exact hh
    rintro ⟨len, s3⟩ ⟨h3, f3, n3, k3⟩
    simp only at h3 f3 n3 k3
    try simp only [WP.uncurry'_pair]
    unfold msginfo.MessageInfo.new msg.set_msg_info
    simp only [Aeneas.Std.bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ => ?_
    refine WP.spec_mono (regSK h3 ht (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO, layout.reg.RSI]) hp)
      fun s4 ⟨h4, f4, n4, k4⟩ => ⟨h4, f1.trans (f2.trans (f3.trans f4)), n1.trans (n2.trans (n3.trans n4)),
        k1.trans (k2.trans (k3.trans k4))⟩
  · exact (WP.spec_ok _).2 ⟨h1, f1, n1, k1⟩

theorem schedcontext.cancel_yield_to.blkS (s : S) (t p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (ht : t ∈ T) (hp : p ∈ Scs) :
    schedcontext.cancel_yield_to st s t ⦃ s' =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ∧ SKeep st p s s' ⦄ := by
  refine WP.spec_mono (WP.spec_and (schedcontext.cancel_yield_to.blk s t h ht) ?_) fun r hr =>
    ⟨hr.1.1, hr.1.2.1, hr.1.2.2, hr.2⟩
  unfold schedcontext.cancel_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 (SKeep.refl _ _)
  step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
  split
  · rename_i _ hy
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
    have hT := h0.tcbs
    have hO := hX.1
    have hsub := hSg.sub
    have hyS : yt ∈ Scs := by
      rw [yt_post]; exact hX.2.2.yt.2.1 t ht (by rw [← yt_post]; simpa using hy)
    have hm : scYieldFromA yt ∈ Ω := hsub _ (hO.syW yt hyS)
    have ho := h0.omega _ hm
    obtain ⟨hPp, hzp⟩ := hO.sc p hp
    obtain ⟨-, -, -, -, -, -, -, e56⟩ := sc_facts hO hyS
    have av : (scYieldFromA yt).val = yt.val + 56 := e56
    step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
    subst s5_post
    have k5 := SKeep.wr_out (v := 0#u64) h0 hO hsub hp hm
      (scw_ne hO hyS hp av (scTcbA_val hPp hzp) (by omega) (by omega) (by omega))
      (scw_ne hO hyS hp av (scNtfnA_val hPp hzp) (by omega) (by omega) (by omega))
      (scw_ne hO hyS hp av (scReplyA_val hPp hzp) (by omega) (by omega) (by omega))
    have h5 : SchedQueuesInv st T Cs Ω H (L.wr s (scYieldFromA yt) 0#u64) Q R :=
      inv_of_free h0 ((writesIn_wr (v := 0#u64) ho.1).mono fun b hb => hb ▸ Or.inl hm)
    refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
    subst e
    rw [show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl]
    exact k5.trans (SKeep.wr_field hT (h5.nodes _ h5.cur) (h0.omega _ (hsub _ (hO.fixW p hp).1))
      (h0.omega _ (hsub _ (hO.snW p hp))) (h0.omega _ (hsub _ (hO.repW p hp))) ht (by simp) (by simp))
  · exact (WP.spec_ok _).2 (SKeep.refl _ _)

theorem schedcontext.complete_yield_to.blkS {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (y p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ≠ 0#u64 → y ∈ T) (hp : p ∈ Scs) :
    schedcontext.complete_yield_to st ar s a y ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧ ANI st s s' ∧ SKeep st p s s' ⦄ := by
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
  split
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _, SKeep.refl _ _⟩
  rename_i hb
  have hyT : y ∈ T := hy (fun e => hb (by rw [b_post, e]; rfl))
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  split
  · rename_i hi
    have hiS : i ∈ Scs := by rw [ei]; exact h.2.2.1.2.2.yt.2.1 y hyT (by rw [← ei]; simpa using hi)
    refine WP.spec_bind (schedcontext.set_consumed.blkS hA s a i y p true h hiS hyT hp)
      fun s1 ⟨h1, f1, n1, k1⟩ => ?_
    refine WP.spec_bind (schedcontext.cancel_yield_to.blkS s1 y p h1 hyT hp) fun s2 ⟨h2, f2, n2, k2⟩ => ?_
    exact (WP.spec_ok _).2 ⟨h2, f1.trans f2, n1.trans n2, k1.trans k2⟩
  · exact (WP.spec_ok _).2 ⟨h, Foot.refl _, ANI.refl _, SKeep.refl _ _⟩

/-! ## `unbind_all_tcbs` -/

/-- `remote_tcb_stall` keeps `SKeep`. -/
theorem smp.remote_tcb_stall.blkS {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) :
    smp.remote_tcb_stall st ar s a t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      Foot st T Cs Sg Scs Z ∅ s s' ∧ L.actionW s' = L.actionW s ∧ L.idleW s' = L.idleW s ∧ SKeep st p s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.2.sub
  refine WP.spec_mono (WP.spec_and (smp.remote_tcb_stall.blk hA s a t h) (smp.remote_tcb_stall.spec hA s a t)) ?_
  rintro ⟨s', a'⟩ hr
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨⟨h1, f1, ea, -, ei⟩, e⟩ := hr
  refine ⟨h1, f1, ea, ei, ?_⟩
  rcases e with rfl | ⟨v, rfl⟩
  · exact SKeep.refl _ _
  have hN := h0.nodes _ h0.cur
  have ip : layout.node.IPI_PENDING.val = 120 := by simp [layout.node.IPI_PENDING]
  have hal := nodeAt_aligned hN (off := layout.node.IPI_PENDING) (by rw [ip]; omega) (by rw [ip])
  have o1 := h0.omega _ (hsub _ (hO.fixW p hp).1)
  have o2 := h0.omega _ (hsub _ (hO.snW p hp))
  have o3 := h0.omega _ (hsub _ (hO.repW p hp))
  refine ⟨L.mem_wr_ne hal o1.1 (out_ne_node o1 h0.cur hN (by rw [ip]; omega)),
    L.mem_wr_ne hal o2.1 (out_ne_node o2 h0.cur hN (by rw [ip]; omega)), ?_,
    fun h0' => by rw [L.mem_wr_ne hal o3.1 (out_ne_node o3 h0.cur hN (by rw [ip]; omega))]; exact h0'⟩
  unfold LawfulStore.cscW; rw [nodeA_wr]
  unfold LawfulStore.nodeA
  exact L.mem_wr_ne hal (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
    (by rw [nodeAt_val hN (by rw [ip]; omega), nodeAt_val hN (by simp [layout.node.CUR_SC]), ip]
        simp [layout.node.CUR_SC])

/-- `unbind_all_tcbs`: the SC ends with no thread, the current SC word is
kept, and the scheduler action is kept or becomes `CHOOSE_NEW`. -/
theorem schedcontext.unbind_all_tcbs.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (p : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    schedcontext.unbind_all_tcbs st ar s a p ⦃ s' _ =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ∧
      (L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64) ∧ L.idleW s' = L.idleW s ∧
      L.mem s' (scTcbA p) = 0#u64 ∧ L.cscW s' = L.cscW s ⦄ := by
  unfold schedcontext.unbind_all_tcbs
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  split
  · rename_i hi
    refine WP.spec_bind (smp.remote_tcb_stall.blkS hA s a i p h hp) ?_
    rintro ⟨s1, a1⟩ ⟨h1, f1, ea1, ei1, k1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (schedcontext.unbind_tcb.blk s1 p h1 hp hp0 (fun h0 => by
        rw [k1.1] at h0 ⊢; rw [ea1]; exact hna h0)
      (fun h0 => by rw [k1.1] at h0 ⊢; rw [ei1]; exact hidle h0)) fun s2 ⟨h2, f2, ea2, ei2, t2, c2⟩ => ?_
    refine (WP.spec_ok _).2 ⟨h2, f1.trans f2, ?_, by rw [ei2, ei1], t2, by rw [c2, k1.2.2.1]⟩
    rcases ea2 with e | e
    · exact Or.inl (by rw [e, ea1])
    · exact Or.inr e
  · rename_i hi
    refine (WP.spec_ok _).2 ⟨h, Foot.refl _, Or.inl rfl, rfl, ?_, rfl⟩
    rw [← ei]; apply UScalar.eq_of_val_eq; simpa using hi

/-! ## Deactivating the SC: `REFILL_MAX` and `SPORADIC` cleared -/

/-- `XInv` after clearing `REFILL_MAX` of an SC no notification names. -/
theorem XInv.wr_max {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {p v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hp : p ∈ Scs) (hnn : ∀ n ∈ Nt, L.mem s (ntfnScA n) ≠ p) :
    XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (maxA p) v) := by
  have hO := hX.1
  have hT := h.tcbs
  obtain ⟨ha, -, -⟩ := maxA_facts hO hp
  obtain ⟨hPp, hzp⟩ := hO.sc p hp
  have mxv := maxA_val hPp hzp
  have hm : maxA p ∈ Ω := hsub _ (hO.mxW p hp)
  have ho := h.omega _ hm
  have k : ∀ b, Aligned b → (maxA p).val ≠ b.val → L.mem (L.wr s (maxA p) v) b = L.mem s b :=
    fun b hb hne => L.mem_wr_ne ha hb hne
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (maxA p) v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 => k _ (field_aligned (hT y hy) hK hK8) (out_ne_field ho hy (hT y hy) hK).symm
  have al : ∀ b ∈ Ω, Aligned b := fun b hb => (h.omega b hb).1
  have scw : ∀ c ∈ Scs, ∀ b ∈ Sg, ∀ o : Nat, b.val = c.val + o → o < 128 → o ≠ 72 →
      L.mem (L.wr s (maxA p) v) b = L.mem s b := fun c hc b hb o hv ho1 ho2 =>
    k _ (al _ (hsub _ hb)) (scw_ne hO hp hc mxv hv (by omega) ho1 (Ne.symm ho2))
  have rw' : ∀ r ∈ Rp, ∀ b ∈ Sg, (b.val = r.val ∨ b.val = r.val + 8 ∨ b.val = r.val + 16) →
      L.mem (L.wr s (maxA p) v) b = L.mem s b := fun r hr b hb hv =>
    k _ (al _ (hsub _ hb)) (by have := hO.rpSc r hr p hp; have := (sc_facts hO hp).1; omega)
  refine hX.keepN
    (fun r hr => ⟨rw' r hr _ (hO.tcbW hr) (Or.inl (rp_facts hO hr).2.1),
      rw' r hr _ (hO.prevW hr) (Or.inr (Or.inl (rp_facts hO hr).2.2.1)),
      rw' r hr _ (hO.nextW hr) (Or.inr (Or.inr (rp_facts hO hr).2.2.2))⟩)
    (fun c hc => ⟨scw c hc _ (hO.fixW c hc).1 24 (sc_facts hO hc).2.1 (by omega) (by omega),
      scw c hc _ (hO.fixW c hc).2 16 (sc_facts hO hc).2.2.1 (by omega) (by omega)⟩)
    (fun y hy => by rw [scA_eq]; exact fk y hy _ (by simp) (by simp))
    (fun y hy => fk y hy _ (by simp) (by simp))
    (fun y hy => by rw [stA_eq]; exact fk y hy _ (by simp) (by simp))
    (by rw [cscW_wr_out h hm]; exact hX.2.2.cur)
    (fun c hc => scw c hc _ (hO.repW c hc) 32 (sc_facts hO hc).2.2.2.2.2.2.1 (by omega) (by omega))
    (fun y hy => by
      rw [show boundA y = core.num.U64.wrapping_add y 3368#u64 from rfl]; exact fk y hy _ (by simp) (by simp))
    (fun n hn => k _ (hO.ntAl n hn) (by
      rw [mxv]; have := hO.ntSc n hn p hp; have := (sc_facts hO hp).1; omega))
    (hX.tn (TmFr.wr hT h.nodes hO ha (notTmW_omega hT h.nodes ho (fun n hn e => by
      rw [mxv, ntfnBtA_val (hO.ntP n hn)] at e
      have := hO.ntOSc n hn p hp; have := (sc_facts hO hp).1; omega))))
    (fun c hc => by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      exact scw c hc _ (hO.snW c hc) 40 (scNtfnA_val hPc hzc) (by omega) (by omega))
    (hX.2.2.yt.keep (fun c hc => scw c hc _ (hO.fixW c hc).1 24 (sc_facts hO hc).2.1 (by omega) (by omega))
      (fun y hy => fk y hy _ (by simp) (by simp))
      (fun c hc => scw c hc _ (hO.syW c hc) 56 (sc_facts hO hc).2.2.2.2.2.2.2 (by omega) (by omega)))
    (fun c hc ⟨n, hn, e⟩ => by
      have hne : c ≠ p := fun e' => hnn n hn (e.trans e')
      obtain ⟨a1, -, -⟩ := maxA_facts hO hc
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      refine k _ a1 ?_
      rw [mxv, maxA_val hPc hzc]
      have := hO.scDisj c hc p hp hne; have := (sc_facts hO hp).1; have := (sc_facts hO hc).1; omega) (idleW_wr_out h hm)

theorem obj.Sc.set_sporadic.wr (s : S) (c : obj.Sc) (v : U64) :
    obj.Sc.set_sporadic st c s v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add c layout.sc.SPORADIC) v ⦄ := by
  unfold obj.Sc.set_sporadic; step*; simp_all

/-- `BoundInv` for the active SCs other than `p`, when no thread names `p`. -/
theorem BoundInv.restrict {s : S} {p : U64} (hB : BoundInv st T Ac s) (hnb : ∀ y ∈ T, L.mem s (scA y) ≠ p) :
    BoundInv st T (Ac \ {p}) s :=
  { hB with sact := fun y hy hS h0 => ⟨hB.sact y hy hS h0, hnb y hy⟩ }

/-- Deactivating an SC that no thread or notification names: `REFILL_MAX`
and then `SPORADIC` cleared.  The invariants hold again after both writes,
with `p` no longer active (in between, `SCsOK.spor` fails for `p`). -/
theorem deact_all {s : S} {p : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs)
    (hnb : ∀ y ∈ T, L.mem s (scA y) ≠ p) (hnn : ∀ n ∈ Nt, L.mem s (ntfnScA n) ≠ p)
    (hr0 : L.mem s (scReplyA p) = 0#u64) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z (Ac \ {p})
        (L.wr (L.wr s (maxA p) 0#u64) (core.num.U64.wrapping_add p layout.sc.SPORADIC) 0#u64) ∧
      Foot st T Cs Sg Scs Z ∅ s
        (L.wr (L.wr s (maxA p) 0#u64) (core.num.U64.wrapping_add p layout.sc.SPORADIC) 0#u64) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hm : maxA p ∈ Ω := hSg.sub _ (hO.mxW p hp)
  have ho := h0.omega _ hm
  obtain ⟨hPp, hzp⟩ := hO.sc p hp
  obtain ⟨h8, h128, -⟩ := sc_lo hPp hzp
  have mxv := maxA_val hPp hzp
  have hsv : layout.sc.SPORADIC.val = 64 := by simp [layout.sc.SPORADIC]
  have av : (core.num.U64.wrapping_add p layout.sc.SPORADIC).val = p.val + 64 := by
    rw [sc_word_val hPp hzp (by rw [hsv]; omega), hsv]
  have hal : Aligned (core.num.U64.wrapping_add p layout.sc.SPORADIC) := by unfold Aligned; rw [av]; omega
  have hin : InSC p (Z p) (core.num.U64.wrapping_add p layout.sc.SPORADIC) :=
    ⟨by rw [av]; omega, by rw [av]; omega⟩
  have hms := hO.scW p hp _ hal hin
  set s5 := L.wr s (maxA p) 0#u64 with hs5
  set s6 := L.wr s5 (core.num.U64.wrapping_add p layout.sc.SPORADIC) 0#u64 with hs6
  -- the `REFILL_MAX` write
  have h5 : SchedQueuesInv st T Cs Ω H s5 Q R :=
    inv_of_free h0 ((writesIn_wr (v := 0#u64) ho.1).mono fun b hb => hb ▸ Or.inl hm)
  have hB5 := BoundInv.owr (v := 0#u64) h0 hB hm
  have hX5 := XInv.wr_max (v := 0#u64) h0 hX hSg.sub hp hnn
  -- the `SPORADIC` write
  have ne : ∀ c ∈ Scs, ∀ b : U64, ∀ o : Nat, b.val = c.val + o → o < 128 → o ≠ 64 →
      (core.num.U64.wrapping_add p layout.sc.SPORADIC).val ≠ b.val := fun c hc b o hv h1 h2 =>
    scw_ne hO hp hc av hv (by omega) h1 (Ne.symm h2)
  have h6 : SchedQueuesInv st T Cs Ω H s6 Q R :=
    inv_of_free h5 ((writesIn_wr (v := 0#u64) hal).mono fun b hb => hb ▸ Or.inl hms)
  have hB6 := (BoundInv.owr (v := 0#u64) h5 hB5 hms)
  have hX6 : XInv st T Cs Ω Sg Rp Scs Nt Z s6 := XInv.wr_linkT h5 hX5 hSg.sub hms
    (fun r hr => by rw [av, (rp_facts hO hr).2.1]; have := hO.rpSc r hr p hp; omega)
    (fun c hc => by
      obtain ⟨-, e1, e2, e3, -⟩ := sc_facts hO hc
      exact ⟨ne c hc _ 24 e1 (by omega) (by omega), ne c hc _ 16 e2 (by omega) (by omega),
        ne c hc _ 72 e3 (by omega) (by omega)⟩)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.2] at e; have := hO.rpSc r hr p hp; omega)
    (fun r hr e => by rw [av, (rp_facts hO hr).2.2.1] at e; have := hO.rpSc r hr p hp; omega)
    (fun c hc e => absurd e (ne c hc _ 32 (sc_facts hO hc).2.2.2.2.2.2.1 (by omega) (by omega)))
    (fun n hn e => absurd e (by rw [av, ntfnScA_val (hO.ntP n hn)]; have := hO.ntOSc n hn p hp; omega))
    (fun c hc e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      exact ne c hc _ 40 (scNtfnA_val hPc hzc) (by omega) (by omega)))
    (fun n hn e => absurd e (by rw [av, ntfnBtA_val (hO.ntP n hn)]; have := hO.ntOSc n hn p hp; omega))
    (fun c hc e => absurd e (by
      obtain ⟨hPc, hzc⟩ := hO.sc c hc
      exact ne c hc _ 40 (scNtfnA_val hPc hzc) (by omega) (by omega)))
    (fun c hc e => absurd e (ne c hc _ 56 (sc_facts hO hc).2.2.2.2.2.2.2 (by omega) (by omega)))
    (fun r hr e => absurd e (by rw [av, (rp_facts hO hr).2.2.2]; have := hO.rpSc r hr p hp; omega))
    (fun c hc e => absurd e (ne c hc _ 32 (sc_facts hO hc).2.2.2.2.2.2.1 (by omega) (by omega)))
    (BndS.wr_scw (o := 64) hX5.2.2.toScExtra0 h5 hX5.1 hSg.sub hms hp av (by omega) (by omega))
  -- `SCsOK` for `Ac \ {p}` after both writes
  have hms' : core.num.U64.wrapping_add p layout.sc.SPORADIC ∈ Ω := hms
  have hos := h0.omega _ hms'
  have w : WritesIn st s s6 (fun b => b = maxA p ∨ b = core.num.U64.wrapping_add p layout.sc.SPORADIC) :=
    (writesIn_wr ho.1).trans (writesIn_wr hal)
  have out : ∀ c ∈ Scs, c ≠ p → ∀ b, Aligned b →
      (b = maxA p ∨ b = core.num.U64.wrapping_add p layout.sc.SPORADIC) → Outside b c (Z c) := by
    rintro c hc hne b - (rfl | rfl)
    · have := hO.scDisj c hc p hp hne; have := (sc_facts hO hp).1
      unfold Outside; rw [mxv]; omega
    · have := hO.scDisj c hc p hp hne
      unfold Outside; rw [av]; omega
  have fld : ∀ y ∈ T, L.mem s6 (scA y) = L.mem s (scA y) := fun y hy =>
    w.mem_eq (scA_aligned (h0.tcbs y hy)) (by
      rintro (e | e)
      · rw [scA_eq] at e; exact out_ne_field (K := 3464#u64) ho hy (h0.tcbs y hy) (by simp) (congrArg UScalar.val e)
      · rw [scA_eq] at e; exact out_ne_field (K := 3464#u64) hos hy (h0.tcbs y hy) (by simp) (congrArg UScalar.val e))
  have csc : L.cscW s6 = L.cscW s := by rw [hs6, cscW_wr_out h5 hms', hs5, cscW_wr_out h0 hm]
  have mx6 : L.rmax s6 p = 0#u64 := by
    show L.mem s6 (maxA p) = 0#u64
    rw [hs6, L.mem_wr_ne hal ho.1 (by rw [av, mxv]; omega), hs5, L.mem_wr_same ho.1]
  have sp6 : L.mem s6 (sporA p) = 0#u64 := L.mem_wr_same hal
  have kmx : ∀ c ∈ Scs, c ≠ p → L.rmax s6 c = L.rmax s c := fun c hc hne => by
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc
    exact w.mem_eq a1 fun hh => by have := out c hc hne _ a1 hh; unfold Outside at this; omega
  have ksp : ∀ c ∈ Scs, c ≠ p → L.mem s6 (sporA c) = L.mem s (sporA c) := fun c hc hne => by
    obtain ⟨hPc, hzc⟩ := hO.sc c hc
    obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
    have spv := sporA_val hPc hzc
    have al : Aligned (sporA c) := by unfold Aligned; omega
    exact w.mem_eq al fun hh => by
      have := out c hc hne _ al hh; unfold Outside at this; omega
  have hS6 : SCsOK st T Ω Sg Scs Z (Ac \ {p}) s6 := by
    refine ⟨hS.sub, fun b hb => by rw [w.1]; exact hS.ks b hb, fun o h1 h2 => by rw [w.1]; exact hS.ksΩ o h1 h2,
      fun y hy hb hne => ?_, fun c hc => ?_, fun c hc => ?_, fun c hc h0' => ?_, ?_, ?_, ?_⟩
    · rw [fld y hy] at hb hne ⊢; rw [csc] at hne ⊢; exact hS.disj y hy hb hne
    · by_cases e : c = p
      · subst e; exact (hS.all c hc).mk' fun hne => absurd mx6 hne
      obtain ⟨a1, a2, a3⟩ := maxA_facts hO hc
      exact (hS.all c hc).writesIn a1 ⟨a2, a3⟩ w (out c hc e)
    · by_cases e : c = p
      · subst e
        exact ⟨fun hh => absurd rfl hh.2, fun hh => absurd mx6 hh⟩
      · rw [kmx c hc e]
        exact ⟨fun hh => (hS.act c hc).1 hh.1, fun hh => ⟨(hS.act c hc).2 hh, e⟩⟩
    · by_cases e : c = p
      · subst e; exact absurd sp6 h0'
      · exact ⟨hS.spor c hc (by rw [← ksp c hc e]; exact h0'), e⟩
    · exact hS.spSg
    · intro c hc h0'
      have krp : L.mem s6 (scReplyA c) = L.mem s (scReplyA c) := by
        obtain ⟨hPc, hzc⟩ := hO.sc c hc
        obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
        have rpv := scReplyA_val hPc hzc
        have al : Aligned (scReplyA c) := by unfold Aligned; omega
        refine w.mem_eq al fun hh => ?_
        rcases hh with e | e <;> have := congrArg UScalar.val e
        · rw [rpv, mxv] at this
          by_cases e' : c = p
          · subst e'; omega
          · have := hO.scDisj c hc p hp e'; omega
        · rw [rpv, av] at this
          by_cases e' : c = p
          · subst e'; omega
          · have := hO.scDisj c hc p hp e'; omega
      rw [krp] at h0'
      by_cases e : c = p
      · subst e; exact absurd hr0 h0'
      · exact ⟨hS.rep c hc h0', e⟩
    · exact hS.repSg
  refine ⟨⟨⟨Q, R, h6⟩, hB6.restrict fun y hy => by rw [fld y hy]; exact hnb y hy, hX6, hS6,
    ⟨hSg.sub, fun b hb => by rw [w.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [w.1]; exact hSg.ksΩ o h1 h2⟩⟩,
    (foot_wr ho.1 (kw_sg (hO.mxW p hp))).trans (foot_wr hal (kw_sc hp hin))⟩

/-! ## The SchedContext branch -/

/-- `finalise_cap` of a final SC cap: the thread, the notification and the
reply are unbound, a pending yield is completed, and the SC is deactivated
(`REFILL_MAX` and `SPORADIC` cleared), so it leaves the active SCs `Ac`.
The scheduler action and the idle thread must not be the SC's thread.  The
SC may be the current SC (`SCsOK` allows an inactive current SC; charging
it needs a current SC in `Ac`). -/
theorem fin_sc.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p x : U64)
    (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Scs) (hp0 : p ≠ 0#u64)
    (hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p))
    (hidle : L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)) :
    objects.finalise_cap_object st ar s a (.SchedContext p x) fin ⦃ r =>
      ∃ Ac', (Ac' = Ac ∨ Ac' = Ac \ {p}) ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' r.2.1 ∧
        Foot st T Cs Sg Scs Z ∅ s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 ⟨Ac, Or.inl rfl, h, Foot.refl _⟩
  refine WP.spec_bind (schedcontext.unbind_all_tcbs.blk hA s a p h hp hp0 hna hidle) ?_
  rintro ⟨s1, a1⟩ ⟨h1, f1, -, -, t1, c1⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (schedcontext.unbind_ntfn.blk s1 p h1 fun _ => hp) fun s2 ⟨h2, f2, t2, c2, n2⟩ => ?_
  refine WP.spec_bind (schedcontext.unbind_reply.blk s2 p p h2 (fun _ => hp) hp) fun s3 ⟨h3, f3, k3, r3⟩ => ?_
  refine WP.spec_bind (obj.Sc.yield_from.val s3 p) fun yf eyf => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      Foot st T Cs Sg Scs Z ∅ s3 r.1 ∧ SKeep st p s3 r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, Foot.refl _, SKeep.refl _ _⟩
    · refine WP.spec_mono (schedcontext.complete_yield_to.blkS hA s3 a1 yf p h3 (fun hy0 => by
        rw [eyf]; exact h3.2.2.1.2.2.yt.2.2 p hp (by rw [← eyf]; exact hy0)) hp) ?_
      rintro ⟨s4, a4⟩ ⟨h4, f4, -, k4⟩
      exact ⟨h4, f4, k4⟩
  rintro ⟨s4, a2⟩ ⟨h4, f4, k4⟩
  try simp only [WP.uncurry'_pair]
  have t4 : L.mem s4 (scTcbA p) = 0#u64 := by rw [k4.1, k3.1, t2, t1]
  have n4 : L.mem s4 (scNtfnA p) = 0#u64 := by rw [k4.2.1, k3.2.1, n2 hp0]
  have r4 : L.mem s4 (scReplyA p) = 0#u64 := k4.2.2.2 (r3 hp0)
  have hX4 := h4.2.2.1
  have hT4 := h4.1.choose_spec.choose_spec.tcbs
  have hnb : ∀ y ∈ T, L.mem s4 (scA y) ≠ p := fun y hy e => by
    obtain ⟨-, e2, -⟩ := hX4.2.2.bound y hy (by rw [e]; exact hp0)
    rw [e, t4] at e2
    exact (hT4 y hy).ne0 (by rw [← e2]; rfl)
  have hnn : ∀ n ∈ Nt, L.mem s4 (ntfnScA n) ≠ p := fun n hn e => by
    obtain ⟨-, e2⟩ := hX4.2.2.nsc n hn (by rw [e]; exact hp0)
    rw [e, n4] at e2
    exact hX4.1.nt0 n hn e2.symm
  refine WP.spec_bind (obj.Sc.set_refill_max.spec s4 p 0#u64) fun s5 e5 => ?_
  subst e5
  refine WP.spec_bind (obj.Sc.set_sporadic.wr _ p 0#u64) fun s6 e6 => ?_
  subst e6
  obtain ⟨h6, f6⟩ := deact_all h4 hp hnb hnn r4
  exact (WP.spec_ok _).2 ⟨_, Or.inr rfl, h6, f1.trans (f2.trans (f3.trans (f4.trans f6)))⟩

end

end Fl4Proofs.P1
