/-
P1: InvGaps' `schedContext` family: `schedcontext.decode` (the SchedContext
invocations: Consumed, Bind, UnbindObject, Unbind, YieldTo) keeps the
invariants, from `DecPre`; YieldTo is named (`ScYieldGap`).
-/
import Fl4Proofs.P1.QueueInvAll
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U X : Set U64}

/-! ## Two writes in either order -/

/-- Kernel words and object words: what the SchedContext decodes write. -/
def KO (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64) (Z : U64 → Nat)
    (s0 : S) (b : U64) : Prop :=
  KW st T Cs Sg Scs Z (EH H) s0 b ∨ b ∈ Ω

theorem KO.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : KO st T Cs Ω H Sg Scs Z s1 b) :
    KO st T Cs Ω H Sg Scs Z s0 b :=
  h.elim (fun h => Or.inl (KW.ksb hk h)) Or.inr

theorem KO.trans {s0 s s' : S} (h : WritesIn st s0 s (KO st T Cs Ω H Sg Scs Z s0))
    (hw : WritesIn st s s' (KO st T Cs Ω H Sg Scs Z s)) : WritesIn st s0 s' (KO st T Cs Ω H Sg Scs Z s0) :=
  (h.trans hw).mono fun _ hb => hb.elim id (KO.ksb h.1)

theorem Foot.ko {s s' : S} {Es : Set U64} (f : Foot st T Cs Sg Scs Z Es s s') (hE : Es ⊆ EH H) :
    WritesIn st s s' (KO st T Cs Ω H Sg Scs Z s) :=
  WritesIn.mono f fun _ hb => Or.inl (KW.mono hb hE)

/-- `KO` with the debug-list words (`bind_tcb` moves a thread between cores'
debug lists). -/
def KOD (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64) (Z : U64 → Nat)
    (s0 : S) (b : U64) : Prop :=
  KO st T Cs Ω H Sg Scs Z s0 b ∨ DbgW st T Cs s0 b

theorem KOD.trans {s0 s s' : S} (h : WritesIn st s0 s (KO st T Cs Ω H Sg Scs Z s0))
    (hw : WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s)) : WritesIn st s0 s' (KOD st T Cs Ω H Sg Scs Z s0) :=
  (h.trans hw).mono fun _ hb => by
    rcases hb with hb | hb | ⟨y, hy, e⟩ | ⟨c, hc, e⟩
    · exact Or.inl hb
    · exact Or.inl (KO.ksb h.1 hb)
    · exact Or.inr (Or.inl ⟨y, hy, e⟩)
    · exact Or.inr (Or.inr ⟨c, hc, by rw [e, nodeAt_of_ksb h.1]⟩)

theorem FootD.kod {s s' : S} {Es : Set U64} (f : FootD st T Cs Sg Scs Z Es s s') (hE : Es ⊆ EH H) :
    WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s) :=
  WritesIn.mono f fun _ hb => hb.elim (fun hb => Or.inl (Or.inl (KW.mono hb hE))) Or.inr

/-- Two writes to distinct aligned words commute (as far as the invariants
see: `WritesIn` with no footprint). -/
theorem wr_swap {s : S} {a b v w : U64} (ha : Aligned a) (hb : Aligned b) (hne : a.val ≠ b.val) :
    WritesIn st (L.wr (L.wr s b w) a v) (L.wr (L.wr s a v) b w) (fun _ => False) := by
  refine ⟨by simp [L.ksb_wr], by simp [L.cpu_wr], fun x hx _ => ?_⟩
  rw [L.mem_wr_val hb hx, L.mem_wr_val ha hx, L.mem_wr_val ha hx, L.mem_wr_val hb hx]
  by_cases e1 : b.val = x.val <;> by_cases e2 : a.val = x.val <;> simp [e1, e2] <;> omega

/-- `BlkOK` across a no-footprint `WritesIn`. -/
theorem BlkOK.same {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hw : WritesIn st s s' (fun _ => False)) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' :=
  (blk_of_capw h hw fun _ hb => hb.elim).1

/-! ## `bind_ntfn` -/

/-- **`bind_ntfn`** writes two object words. -/
theorem schedcontext.bind_ntfn.ko (s : S) (c n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ∈ Scs) (hn : n ∈ Nt) :
    schedcontext.bind_ntfn st s c n ⦃ s' => WritesIn st s s' (KO st T Cs Ω H Sg Scs Z s) ⦄ := by
  unfold schedcontext.bind_ntfn
  refine WP.spec_bind (obj.Ntfn.set_sc.wr s n c) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c n) fun s2 e2 => ?_
  subst e2
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hmB : scNtfnA c ∈ Ω := hSg.sub _ (hO.snW c hc)
  have hmA : ntfnScA n ∈ Ω := hSg.sub _ (hO.ntW n hn)
  have alA : Aligned (ntfnScA n) := hO.ntAl n hn
  have alB : Aligned (scNtfnA c) := (h0.omega _ hmB).1
  refine ((writesIn_wr alA).trans (writesIn_wr alB)).mono fun b hb => ?_
  rcases hb with rfl | rfl
  · exact Or.inr hmA
  · exact Or.inr hmB

/-- The current node's words (but its debug head) are `KO` words. -/
theorem NodeW.ko {s : S} {b : U64} (hc : L.cpu s ∈ Cs) (h : NodeW st s b) : KO st T Cs Ω H Sg Scs Z s b := by
  obtain ⟨o, ho, h88, rfl⟩ := h
  exact Or.inl (kw_node hc ho h88)

/-- **`bind_ntfn`** of an SC and a notification bound to nothing. -/
theorem schedcontext.bind_ntfn.blk (s : S) (c n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ∈ Scs) (hc0 : c ≠ 0#u64) (hn : n ∈ Nt) (h1 : L.mem s (ntfnScA n) = 0#u64) (h2 : L.mem s (scNtfnA c) = 0#u64) :
    schedcontext.bind_ntfn st s c n ⦃ s' => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold schedcontext.bind_ntfn
  refine WP.spec_bind (obj.Ntfn.set_sc.wr s n c) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c n) fun s2 e2 => ?_
  subst e2
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h128, e1, e2, e3, e4, e5, e6, e7⟩ := sc_facts hO hc
  have avB := scNtfnA_val hP hz
  have hnP := hO.ntP n hn
  have avA := ntfnScA_val hnP
  have hmB : scNtfnA c ∈ Ω := hSg.sub _ (hO.snW c hc)
  have hmA : ntfnScA n ∈ Ω := hSg.sub _ (hO.ntW n hn)
  have alA : Aligned (ntfnScA n) := hO.ntAl n hn
  have alB : Aligned (scNtfnA c) := (h0.omega _ hmB).1
  have dnc := hO.ntOSc n hn c hc
  have hneAB : (ntfnScA n).val ≠ (scNtfnA c).val := by rw [avA, avB]; omega
  -- the swapped order: the SC's word first
  have scw : ∀ c' ∈ Scs, ∀ o : U64, o.val < 128 → c' ≠ c →
      (core.num.U64.wrapping_add c' o).val ≠ (scNtfnA c).val := fun c' hc' o ho hne => by
    obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    rw [sc_word_val hP' hz' ho, avB]
    have := hO.scDisj c hc c' hc' (Ne.symm hne); have := (sc_facts hO hc').1; omega
  -- an SC word of `c'` at offset `o` is not `scNtfnA c` unless `c' = c` and `o = 40`
  have scw' : ∀ c' ∈ Scs, ∀ o : U64, o.val < 128 → o.val ≠ 40 →
      (core.num.U64.wrapping_add c' o).val ≠ (scNtfnA c).val := fun c' hc' o ho h40 => by
    by_cases e : c' = c
    · subst e; rw [sc_word_val hP hz ho, avB]; omega
    · exact scw c' hc' o ho e
  have nnz : ∀ n' ∈ Nt, L.mem s (ntfnScA n') ≠ c := fun n' hn' e => by
    obtain ⟨-, e'⟩ := hX.2.2.nsc n' hn' (by rw [e]; exact hc0)
    rw [e, h2] at e'
    exact hO.nt0 n' hn' e'.symm
  have rpc : ∀ r ∈ Rp, ∀ o : U64, o.val < 32 → (core.num.U64.wrapping_add r o).val ≠ (scNtfnA c).val :=
    fun r hr o ho => by
      rw [rp_val (hO.rp r hr) ho, avB]; have := hO.rpSc r hr c hc; omega
  obtain ⟨g0, gB, gX, gS, gSg, -⟩ := link_allTM (w := n) h0 hB hX.m hS hSg hmB
    (fun r hr => by rw [avB, (rp_facts hO hr).2.1]; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' => by
      obtain ⟨h128', f1, f2, f3, f4, f5, -⟩ := sc_facts hO hc'
      rw [avB, f1, f2, f3, f4, f5]
      by_cases e : c = c'
      · subst e; omega
      · have := hO.scDisj c hc c' hc' e; omega)
    (fun r hr e => by rw [avB, (rp_facts hO hr).2.2.2] at e; have := hO.rpSc r hr c hc; omega)
    (fun r hr e => by rw [avB, (rp_facts hO hr).2.2.1] at e; have := hO.rpSc r hr c hc; omega)
    (fun c' hc' e => absurd e.symm (scw' c' hc' layout.sc.REPLY (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY])))
    (fun n' hn' e => absurd e (by rw [avB, ntfnScA_val (hO.ntP n' hn')]; have := hO.ntSc n' hn' c hc; omega))
    (fun c' hc' e n' hn' ee => by
      have hcc : c' = c := by
        by_contra hne
        exact scw c' hc' layout.sc.NTFN (by simp [layout.sc.NTFN]) hne e.symm
      exact absurd (hcc ▸ ee) (nnz n' hn'))
    (fun n' hn' e => absurd e (by rw [avB, ntfnBtA_val (hO.ntP n' hn')]; have := hO.ntOSc n' hn' c hc; omega))
    (fun _ _ _ _ => hn)
    (fun c' hc' e => absurd e.symm (scw' c' hc' layout.sc.YIELD_FROM (by simp [layout.sc.YIELD_FROM])
      (by simp [layout.sc.YIELD_FROM])))
    (fun c' hc' => fun e => scw' c' hc' layout.sc.SPORADIC (by simp [layout.sc.SPORADIC])
      (by simp [layout.sc.SPORADIC]) e.symm)
    (fun r hr e => absurd e (by rw [avB, (rp_facts hO hr).2.2.2]; have := hO.rpSc r hr c hc; omega))
    (fun c' hc' e => absurd e.symm (scw' c' hc' layout.sc.REPLY (by simp [layout.sc.REPLY]) (by simp [layout.sc.REPLY])))
  -- the notification's word second
  have scA' : ∀ c' ∈ Scs, ∀ o : U64, o.val < 128 → (core.num.U64.wrapping_add c' o).val ≠ (ntfnScA n).val :=
    fun c' hc' o ho => by
      obtain ⟨hP', hz'⟩ := hO.sc c' hc'
      rw [sc_word_val hP' hz' ho, avA]; have := hO.ntOSc n hn c' hc'; have := (sc_facts hO hc').1; omega
  have ntw : ∀ n' ∈ Nt, ∀ o : U64, o.val < 64 → (core.num.U64.wrapping_add n' o).val = (ntfnScA n).val →
      n' = n ∧ o.val = 32 := fun n' hn' o ho e => by
    have hp' := hO.ntP n' hn'
    have : (core.num.U64.wrapping_add n' o).val = n'.val + o.val := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [this, avA] at e
    have hnn : n'.val = n.val := by omega
    exact ⟨UScalar.eq_of_val_eq hnn, by omega⟩
  have mB : L.mem (L.wr s (scNtfnA c) n) (scNtfnA c) = n := L.mem_wr_same alB
  obtain ⟨k0, kB, kX, kS, kSg, -⟩ := link_allTM (w := c) g0 gB gX gS gSg hmA
    (fun r hr => by rw [avA, (rp_facts hO hr).2.1]; have := hO.ntORp n hn r hr; omega)
    (fun c' hc' => by
      obtain ⟨h128', f1, f2, f3, f4, f5, -⟩ := sc_facts hO hc'
      rw [avA, f1, f2, f3, f4, f5]; have := hO.ntOSc n hn c' hc'; omega)
    (fun r hr e => by rw [avA, (rp_facts hO hr).2.2.2] at e; have := hO.ntORp n hn r hr; omega)
    (fun r hr e => by rw [avA, (rp_facts hO hr).2.2.1] at e; have := hO.ntORp n hn r hr; omega)
    (fun c' hc' e => absurd e.symm (scA' c' hc' layout.sc.REPLY (by simp [layout.sc.REPLY])))
    (fun n' hn' e _ => by
      have hnn : n' = n := (ntw n' hn' layout.ntfn.SC (by simp [layout.ntfn.SC]) e.symm).1
      subst hnn; exact ⟨hc, mB⟩)
    (fun c' hc' e => absurd e.symm (scA' c' hc' layout.sc.NTFN (by simp [layout.sc.NTFN])))
    (fun n' hn' e => absurd e (by
      intro e'
      obtain ⟨-, h32⟩ := ntw n' hn' layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB]) e'.symm
      simp [layout.ntfn.BOUND_TCB] at h32))
    (fun c' hc' e => absurd e.symm (scA' c' hc' layout.sc.NTFN (by simp [layout.sc.NTFN])))
    (fun c' hc' e => absurd e.symm (scA' c' hc' layout.sc.YIELD_FROM (by simp [layout.sc.YIELD_FROM])))
    (fun c' hc' => fun e => scA' c' hc' layout.sc.SPORADIC (by simp [layout.sc.SPORADIC]) e.symm)
    (fun r hr e => absurd e (by rw [avA, (rp_facts hO hr).2.2.2]; have := hO.ntORp n hn r hr; omega))
    (fun c' hc' e => absurd e.symm (scA' c' hc' layout.sc.REPLY (by simp [layout.sc.REPLY])))
  have hM : BlkOKM st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr (L.wr s (scNtfnA c) n) (ntfnScA n) c) :=
    ⟨⟨Q, R, k0⟩, kB, kX, kS, kSg⟩
  exact BlkOK.same (hM.x (BndS.pairSN hX.2.2.toScExtra0 h0 hO hSg.sub hc hn (Or.inr rfl)
    (Or.inl ⟨rfl, rfl, h1, h2⟩))) (wr_swap alA alB hneAB)

/-! ## `set_consumed` within `XS` -/

theorem schedcontext.set_consumed.xs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {s0 s : S} {a : A} {c t : U64} {wm : Bool}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hc : c ∈ Scs) (ht : t ∈ T)
    (hG : ∀ s', XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s') :
    schedcontext.set_consumed st ar s a c t wm ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  unfold schedcontext.set_consumed
  refine WP.spec_bind (schedcontext.update_consumed.xs hA h hc) ?_
  rintro ⟨x, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · refine WP.spec_bind (E.buf _ _ _ _ s1 t (hG s1 h1) h1.1 ht) fun buf hb => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) h1 ht (by simp [layout.reg.BADGE, layout.reg.RDI]))
      fun s2 h2 => ?_
    refine WP.spec_bind (msg.set_mr.xs h2 ht hb (by simp)) ?_
    rintro ⟨len, s3⟩ ⟨h3, -⟩
    simp only at h3
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
    unfold msg.set_msg_info
    exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
      obj.Tcb.set_reg.xs (v := w) h3 ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
  · exact (WP.spec_ok _).2 h1

/-! ## The decoder's reads -/

theorem sched.is_blocked.br (s : S) (t : obj.Tcb) :
    sched.is_blocked st s t ⦃ b => b = false → ¬ BlockedR (L.mem s (stA t)) ⦄ := by
  unfold sched.is_blocked
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  subst ev
  split
  · simp
  split
  · simp
  split
  · simp
  · rename_i h1 h2 h3
    simp only [WP.spec_ok, decide_eq_false_iff_not]
    intro h4 hb
    rcases hb with (e | e | e) | e
    · exact h2 e
    · exact h1 e
    · exact h3 e
    · exact h4 e

theorem schedcontext.extra_cap.ok {s : S} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hx : ∀ sl ∈ extra.val, sl ≠ 0#u64 → obj.Slot.cap st sl s ⦃ c => CapOK st T Rp Scs Nt H s c ⦄) :
    schedcontext.extra_cap st s extra 0#usize ⦃ o => ∀ c, o = some c → CapOK st T Rp Scs Nt H s c ⦄ := by
  unfold schedcontext.extra_cap
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  split
  · simp_all
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp
  rename_i h0
  refine WP.spec_bind (hx sl (hsl ▸ List.getElem_mem hl0) (by simpa using h0)) fun c hc => ?_
  exact (WP.spec_ok _).2 fun c' e => by cases e; exact hc

theorem sporadic.sc_released.act (s : S) (sc : obj.Sc) :
    sporadic.sc_released st s sc ⦃ b => b = true → L.rmax s sc ≠ 0#u64 ⦄ := by
  unfold sporadic.sc_released
  refine WP.spec_bind (sporadic.sc_active.val s sc) fun b1 hb1 => ?_
  split
  · rename_i hb
    exact WP.spec_mono (sporadic.ready.spec s sc) fun _ _ _ => hb1 hb
  · simp

/-- `remote_tcb_stall` from `BXI`. -/
theorem smp.remote_tcb_stall.bxi {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    smp.remote_tcb_stall st ar s a t ⦃ s1 _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 ∧
      L.actionW s1 = L.actionW s ∧ L.curW s1 = L.curW s ∧ L.idleW s1 = L.idleW s ∧ L.cscW s1 = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem s1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ x ∈ Ω, L.mem s1 x = L.mem s x) ∧ WritesIn st s s1 (NodeW st s) ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩ := h
  refine WP.spec_mono (WP.spec_and (smp.remote_tcb_stall.all hA s a t h0 hB hX hS hSg)
    (smp.remote_tcb_stall.spec hA s a t)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  obtain ⟨⟨h1, hB1, hX1, hS1, hSg1, ea, ec, ei, ecs, f, o⟩, e⟩ := hr
  refine ⟨⟨⟨Q, R, h1⟩, hB1, hX1, hSg1, hS1⟩, ea, ec, ei, ecs, f, o, ?_⟩
  rcases e with rfl | ⟨v, rfl⟩
  · exact WritesIn.refl _ _
  · exact (writesIn_wr (nodeAt_aligned (h0.nodes _ h0.cur) (by simp [layout.node.IPI_PENDING])
      (by simp [layout.node.IPI_PENDING]))).mono fun b e =>
        ⟨_, by simp [layout.node.IPI_PENDING], by simp [layout.node.IPI_PENDING], e⟩

/-! ## The decoder -/

/-- The named YieldTo gap: `yield_to` (`complete_yield_to`, `resume`,
`yield_switches`, the consumed-time reply) after the caller's restart, with
the decoder's checks and the caller's entry facts (`DecPre`: the action
resume, or choose-new after the restart; the caller's SC bound and active,
`CanBlock.ac`; the caller in no release queue, `CanBlock.nr`).  Discharged
in QueueYield (`scYieldGap_holds`). -/
def ScYieldGap (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop :=
  ∀ (Ac : Set U64) (s : S) (a : A) (sc : U64) (call : Bool), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    UserOK st T Cs Ω H U s → sc ∈ Scs → sc ≠ 0#u64 → L.mem s (stA (L.curW s)) = sched.TS_RESTART →
    L.mem s (scTcbA sc) ≠ 0#u64 → L.mem s (scTcbA sc) ≠ L.curW s → L.mem s (yieldA (L.curW s)) = 0#u64 →
    (L.actionW s = 0#u64 ∨ L.actionW s = 1#u64) → L.mem s (scA (L.curW s)) ≠ 0#u64 →
    L.mem s (scA (L.curW s)) ∈ Ac → (L.mem s (inqA (L.curW s)) &&& sched.Q_RELEASE) = 0#u64 →
    schedcontext.yield_to st ar s a sc call ⦃ s' _ => (∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s') ∧
      WritesIn st s s' (KO st T Cs Ω H Sg Scs Z s) ⦄

theorem DecPost.of_bxi {s s' : S} {r : core.result.Result Unit error.Exc} {Ac' : Set U64}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s') (hr : r ≠ .Err .Preempted) :
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' :=
  ⟨Ac', h, fun e => absurd e hr⟩

/-- `KO` words are `Cur0W` words. -/
theorem KO.cur0w {s : S} {b : U64} (h : KO st T Cs Ω H Sg Scs Z s b) : Cur0W st T Cs Ω H Sg Scs Z s b := by
  rcases h with h | h
  · exact Or.inl h
  · by_cases hs : b ∈ Sg
    · exact Or.inl (kw_sg hs)
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨h, hs⟩)))

/-- **`schedcontext.decode`** keeps the invariants. -/
theorem schedcontext.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (s : S) (a : A) (lbl sc : U64) (call : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (b : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.SchedContext sc b) extra) (he : EntAt st P3Ok s) :
    schedcontext.decode st ar s a lbl sc call extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧
      WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h := D.bxi
  obtain ⟨hsc, hsc0, hidle⟩ := D.cap.2.2 sc b rfl
  unfold schedcontext.decode
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  -- the stall
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 = L.actionW s ∧ L.curW r.1 = L.curW s ∧ L.idleW r.1 = L.idleW s ∧ L.cscW r.1 = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem r.1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ x ∈ Ω, L.mem r.1 x = L.mem s x) ∧ WritesIn st s r.1 (NodeW st s)) ?_ ?_
  · split
    · exact WP.spec_mono (smp.remote_tcb_stall.bxi hA s a i h) fun r hr => by
        obtain ⟨s', a'⟩ := r; simpa using hr
    · exact (WP.spec_ok _).2 ⟨h, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl, WritesIn.refl _ _⟩
  rintro ⟨s1, a1⟩ ⟨h1, ea1, ec1, ei1, ecs1, f1, o1, w1⟩
  try simp only [WP.uncurry'_pair]
  have W1 : WritesIn st s s1 (KO st T Cs Ω H Sg Scs Z s) :=
    WritesIn.mono w1 fun _ hb => NodeW.ko h.1.choose_spec.choose_spec.cur hb
  have KT : ∀ {s' : S}, WritesIn st s1 s' (KO st T Cs Ω H Sg Scs Z s1) → WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s) :=
    fun w => (KO.trans W1 w).mono fun _ hb => Or.inl hb
  have KTD : ∀ {s' : S}, WritesIn st s1 s' (KOD st T Cs Ω H Sg Scs Z s1) →
      WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s) :=
    fun w => KOD.trans W1 w
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.1.sub
  have run1 : Runnable (L.mem s1 (stA (L.curW s))) := by
    rw [stA_eq, f1 _ hct _ (by simp) (by simp), ← stA_eq]; exact D.run
  have act1 : L.actionW s1 = 0#u64 := ea1.trans D.act
  have idle1 : L.mem s1 (scTcbA sc) ≠ L.idleW s1 := by
    rw [o1 _ (hsub _ (hO.fixW sc hsc).1), ei1]; exact hidle
  have hU1 : UserOK st T Cs Ω H U s1 := D.user.ksb w1.1
  have hx1 := D.extra s1 w1
  have Er : ∀ e : error.SysError, (ok ((core.result.Result.Err (error.Exc.Sys e) : core.result.Result Unit error.Exc),
      s1, a1) : Result _) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧
        WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s) ⦄ := fun e =>
    (WP.spec_ok _).2 ⟨DecPost.of_bxi h1 (by simp), W1.mono fun _ hb => Or.inl hb⟩
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = L.curW s := ect.trans ec1
  subst ect'
  simp only [error.illegal, error.truncated, error.invalid_cap, bind_ok]
  split
  · -- Consumed
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
      (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
    obtain ⟨Q2, R2, x2⟩ := BXI.xs (BlkOK.bxi h2) (hU1.ksb k2.ksb)
    have hG2 : XG st T Cs Ω H Sg Scs Z P3Ok s2 :=
      ⟨s, he, Cur0W.trans (W1.mono fun _ hb => KO.cur0w hb) (Foot.cur0w f2 (Set.empty_subset _))⟩
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.xs hA E x2 hsc hct
        fun s' h' => XG.xs hG2 h' (hU1.ksb k2.ksb))
      (schedcontext.set_consumed.blk hA s2 a1 sc (L.curW s) call h2 hsc hct)) fun s3 ⟨x3, _, f3, _⟩ => ?_
    have hst : L.mem s3 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, x3.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp), ← stA_eq, e2]
    refine WP.spec_bind (WP.spec_and (sched.set_thread_state.running_bxi x3.bxi hct hst)
      (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 _ _ x3.1.1 hct)) fun s4 ⟨h4, f4⟩ => ?_
    exact (WP.spec_ok _).2 ⟨DecPost.of_bxi h4 (by simp), KT (KO.trans (Foot.ko f2 (Set.empty_subset _))
      (KO.trans (Foot.ko f3 (Set.empty_subset _)) (Foot.ko f4 (Set.empty_subset _))))⟩
  split
  · -- Bind
    refine WP.spec_bind (schedcontext.extra_cap.ok (fun sl hsl h0 => hx1 sl hsl h0)) fun o ho => ?_
    rcases o with _ | c
    · exact Er _
    have hcO := ho c rfl
    cases c
    all_goals first | exact Er _ | skip
    · -- a notification
      rename_i ptr _ _ _
      obtain ⟨hpN, -⟩ := hcO.1.2.1 ptr _ _ _ rfl
      dsimp only
      refine WP.spec_bind (obj.Sc.ntfn.val s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      rename_i hi1
      refine WP.spec_bind (obj.Ntfn.sc.val s1 ptr) fun i2 ei2 => ?_
      split
      · exact Er _
      rename_i hi2
      refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
        (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
      have z1 : L.mem s2 (ntfnScA ptr) = 0#u64 := by
        rw [k2.nsc ptr hpN, ← ei2]; exact UScalar.eq_of_val_eq (by simpa using hi2)
      have z2 : L.mem s2 (scNtfnA sc) = 0#u64 := by
        rw [k2.snt sc hsc, ← ei1]; exact UScalar.eq_of_val_eq (by simpa using hi1)
      refine WP.spec_bind (WP.spec_and (schedcontext.bind_ntfn.blk s2 sc ptr h2 hsc hsc0 hpN z1 z2)
        (schedcontext.bind_ntfn.ko s2 sc ptr h2 hsc hpN)) fun s3 ⟨h3, f3⟩ => ?_
      exact (WP.spec_ok _).2 ⟨DecPost.of_bxi (BlkOK.bxi h3) (by simp), KT (KO.trans (Foot.ko f2 (Set.empty_subset _)) f3)⟩
    · -- a thread
      rename_i ptr
      have hpT : ptr ∈ T := hcO.2.1 ptr rfl
      dsimp only
      refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      rename_i hi1
      refine WP.spec_bind (obj.Tcb.sc.spec s1 ptr) fun i2 ei2 => ?_
      split
      · exact Er _
      rename_i hi2
      have z1 : L.mem s1 (scTcbA sc) = 0#u64 := by rw [← ei1]; exact UScalar.eq_of_val_eq (by simpa using hi1)
      have z2 : L.mem s1 (scA ptr) = 0#u64 := by rw [← ei2]; exact UScalar.eq_of_val_eq (by simpa using hi2)
      refine WP.spec_bind (sched.is_blocked.br s1 ptr) fun bb hbb => ?_
      have fin : (BlockedR (L.mem s1 (stA ptr)) → sc ∈ Ac) →
          (do
            let s2 ← sched.set_thread_state st s1 (L.curW s) sched.TS_RESTART
            let (s3, a2) ← schedcontext.bind_tcb st ar s2 a1 sc ptr
            ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r s' _ =>
              DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ WritesIn st s s' (KOD st T Cs Ω H Sg Scs Z s) ⦄ := fun hbA =>
        WP.spec_mono (sc_bind_tcb.blkF hA s1 a1 _ sc ptr h1.blk hct run1 hpT hsc hsc0 z2 z1 hbA) fun r hr => by
          obtain ⟨r', s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KTD (FootD.kod hr.2.2 (Set.empty_subset _))⟩
      split
      · refine WP.spec_bind (sporadic.sc_released.act s1 sc) fun b1 hb1 => ?_
        split
        · rename_i hb1t
          exact fin fun _ => (h1.2.2.2.2.act sc hsc).2 (hb1 hb1t)
        · exact Er _
      · rename_i hbf
        exact fin fun hb => absurd hb (hbb (by simpa using hbf))
  split
  · -- UnbindObject
    refine WP.spec_bind (schedcontext.extra_cap.ok (fun sl hsl h0 => hx1 sl hsl h0)) fun o ho => ?_
    rcases o with _ | c
    · exact Er _
    have hcO := ho c rfl
    cases c
    all_goals first | exact Er _ | skip
    · rename_i ptr _ _ _
      dsimp only
      refine WP.spec_bind (obj.Sc.ntfn.val s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      exact WP.spec_mono (sc_unbind_ntfn.blkF s1 a1 _ sc h1.blk hct run1 hsc) fun r hr => by
        obtain ⟨r', s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KT (Foot.ko hr.2.2.1 (Set.empty_subset _))⟩
    · rename_i ptr
      dsimp only
      refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      split
      · exact Er _
      exact WP.spec_mono (sc_unbind_tcb.blkF s1 a1 _ sc h1.blk hct run1 hsc hsc0
        (fun hz e => hz (by rw [← e, act1])) (fun _ => Ne.symm idle1)) fun r hr => by
        obtain ⟨r', s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KT (Foot.ko hr.2.2.1 (Set.empty_subset _))⟩
  split
  · -- Unbind
    refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
    split
    · exact Er _
    exact WP.spec_mono (sc_unbind.blkF hA s1 a1 _ sc h1.blk hct run1 hsc hsc0
      (fun hz e => hz (by rw [← e, act1])) (fun _ => Ne.symm idle1)) fun r hr => by
      obtain ⟨r', s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KT (Foot.ko hr.2.2.1 (Set.empty_subset _))⟩
  split
  · -- YieldTo
    refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
    refine WP.spec_bind (obj.Tcb.is_null.spec i1) fun bn ebn => ?_
    split
    · exact Er _
    rename_i hbn
    refine WP.spec_bind (tcb_eq.blk i1 (L.curW s)) fun be ebe => ?_
    split
    · exact Er _
    rename_i hbe
    refine WP.spec_bind (obj.Tcb.prio.spec s1 i1) fun i2 _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.mcp.p0 st (L.curW s) s1 hS) fun i3 _ => ?_
    split
    · exact Er _
    refine WP.spec_bind (obj.Tcb.yield_to.spec s1 (L.curW s)) fun i4 ei4 => ?_
    split
    · exact Er _
    rename_i hi4
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
      (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
    have hc2 : L.curW s2 = L.curW s := k2.curW.trans ec1
    have t2 : L.mem s2 (scTcbA sc) = i1 := (k2.fix sc hsc).1.trans ei1.symm
    have y2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
      unfold yieldA
      rw [k2.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)]
      rw [← yieldA, ← ei4]; exact UScalar.eq_of_val_eq (by simpa using hi4)
    refine WP.spec_bind (Y Ac s2 a1 sc call (BlkOK.bxi h2) (hU1.ksb k2.ksb) hsc hsc0 (by rw [hc2]; exact e2)
      (by rw [t2]; intro e; exact hbn (by rw [ebn, e]; rfl))
      (by rw [t2, hc2]; intro e; exact hbe (by rw [ebe, e]; simp))
      (by rw [hc2]; exact y2)
      (by rcases k2.act with e | e
          · left; rw [e, act1]
          · right; exact e)
      (by rw [hc2, k2.scf hct, scA_eq, f1 _ hct _ (by simp) (by simp), ← scA_eq]; exact h.2.1.resume D.act)
      (by rw [hc2, k2.scf hct, scA_eq, f1 _ hct _ (by simp) (by simp), ← scA_eq]
          exact D.cb.ac (h.2.1.resume D.act))
      (by rw [hc2, inqA_eq, k2.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩),
            f1 _ hct _ (by simp) (by simp), ← inqA_eq]; exact D.cb.nr)) ?_
    rintro ⟨s3, a2⟩ ⟨⟨Ac3, h3⟩, f3⟩
    try simp only [WP.uncurry'_pair]
    exact (WP.spec_ok _).2 ⟨DecPost.of_bxi h3 (by simp), KT (KO.trans (Foot.ko f2 (Set.empty_subset _)) f3)⟩
  · exact Er _

/-- **InvGaps' `schedContext`, discharged** but for the named `ScYieldGap`. -/
theorem decGap_sc {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedContext := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i sc b
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact WP.spec_mono (schedcontext.decode.dec hA E Y s a lbl sc call extra b D hE) fun _ hr => hr.1

end

end Fl4Proofs.P1
