/-
P1: EntryHyps' `xfer` discharged: the message transfer (`do_ipc_transfer`)
keeps the invariants within `XferFr` (`XferOK`), from the placement facts:
the receiver's IPC buffer words are user words (`BufU`), a granted cap's
slots are cap-slot words (`XferSlots`) and the CDT insert writes cap-slot
words only (`InsCapW`).
-/
import Fl4Proofs.P1.QueueDebug
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `blk_of_capw` for the queue invariant with an excluded set. -/
theorem capw_bx {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S} {B : U64 → Prop}
    (h0 : SchedQueuesInvX st T Cs Ω H X s Q R) (hBd : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) :
    SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.curW s' = L.curW s ∧ L.cscW s' = L.cscW s ∧ L.actionW s' = L.actionW s ∧ L.idleW s' = L.idleW s ∧
      (∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ b ∈ Sg, L.mem s' b = L.mem s b) := by
  have hT := h0.tcbs
  have hO := hX.1
  have hBw : ∀ b, B b → L.Free s Ω Cs b ∨ TLow T b := fun b hb =>
    (hB b hb).elim Or.inr fun h' => Or.inl (Or.inl h'.1)
  have fld : ∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK0 hK hK8
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) fun hb => ?_
    rcases hB _ hb with hl | ⟨hm, -⟩
    · exact tlow_ne_field hT hy hK0 hK hl rfl
    · exact out_ne_field (h0.omega _ hm) hy (hT y hy) hK rfl
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    refine hw.mem_eq (nodeAt_aligned (h0.nodes c hc) ho h8) fun hb => ?_
    rcases hB _ hb with hl | ⟨hm, -⟩
    · exact tlow_ne_node hT (h0.nodes c hc) ho hl rfl
    · exact out_ne_node (h0.omega _ hm) hc (h0.nodes c hc) ho rfl
  have sig : ∀ b ∈ Sg, L.mem s' b = L.mem s b := by
    intro b hb
    have ho := h0.omega _ (hSg.sub b hb)
    refine hw.mem_eq ho.1 fun hb' => ?_
    rcases hB _ hb' with hl | ⟨-, hn⟩
    · exact tlow_ne_out hT ho hl
    · exact hn hb
  have cur : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho h8 => by
    rw [hw.2.1, nodeAt_of_ksb hw.1]; exact nod _ h0.cur o ho h8
  have hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp)
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    exact cur _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact cur _ (by rw [idle8]; omega) (by rw [idle8])
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact cur _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; exact cur _ (by rw [curth0]; omega) (by rw [curth0])
  have htm : TmFr st T Cs Nt s s' := TmFr.of_writes hT h0.nodes hO hw fun b hb => by
    rcases hB b hb with hl | ⟨hm, hn⟩
    · rintro (⟨y, hy, K, h1, h2, h3, e⟩ | ⟨c, hc, o, ho, e⟩ | ⟨n, hn', e⟩)
      · exact tlow_ne_field hT hy (by omega) (by omega) hl e
      · exact tlow_ne_node hT (h0.nodes c hc) (by omega) hl e.symm
      · exact tlow_ne_out hT (h0.omega _ (hSg.sub _ (hO.ntB n hn').2)) (by rw [← e]; exact hl)
    · rintro (⟨y, hy, K, h1, h2, h3, e⟩ | ⟨c, hc, o, ho, e⟩ | ⟨n, hn', e⟩)
      · exact out_ne_field (h0.omega _ hm) hy (hT y hy) (by omega) (congrArg UScalar.val e).symm
      · exact out_ne_node (h0.omega _ hm) hc (h0.nodes c hc) (by omega) (congrArg UScalar.val e).symm
      · exact hn (by rw [e]; exact (hO.ntB n hn').2)
  have hX' : XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
    hX.keep (fun r hr => ⟨sig _ (hX.1.tcbW hr), sig _ (hX.1.prevW hr), sig _ (hX.1.nextW hr)⟩)
      (fun c hc => ⟨sig _ (hX.1.fixW c hc).1, sig _ (hX.1.fixW c hc).2⟩) hsc
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp)) hst
      (by rw [ecs]; exact hX.2.2.cur) (fun c hc => sig _ (hX.1.repW c hc))
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
      (fun n hn => sig _ (hX.1.ntW n hn)) (hX.tn htm)
      (fun c hc => sig _ (hX.1.snW c hc)) (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
      (fun c hc => sig _ (hX.1.syW c hc))
      (fun c hc => sig _ (hX.1.mxW c hc)) ei
      (fun y hy => fld y hy _ (by simp) (by simp) (by simp))
  have hS' : SCsOK st T Ω Sg Scs Z Ac s' := by
    refine ⟨hS.sub, fun b hb => by rw [hw.1]; exact hS.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hS.ksΩ o h1 h2,
      fun t ht hb hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax s' c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h1 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h1), hS.spSg,
      fun c hc h1 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h1), hS.repSg, fun c hc => by rw [hw.1]; exact hS.scKs c hc⟩
    rw [hsc t ht] at hb hne ⊢; rw [ecs] at hne ⊢; exact hS.disj t ht hb hne
  exact ⟨inv_of_capw h0 hw hBw, BoundInv.capw h0 hBd hw hBw, hX', hS',
      ⟨hSg.sub, fun b hb => by rw [hw.1]; exact hSg.ks b hb, fun o h1 h2 => by rw [hw.1]; exact hSg.ksΩ o h1 h2⟩,
    ec, ecs, ea, ei, fld, sig⟩

/-! ## The transfer invariant and its steps -/

/-- The invariants a message transfer keeps. -/
def XI (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s : S) : Prop :=
  SchedQueuesInvX st T Cs Ω H X s Q R ∧ BoundInv st T Ac s ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s ∧
    SCsOK st T Ω Sg Scs Z Ac s ∧ SgOK st Ω Sg s ∧ UserOK st T Cs Ω H U s

/-- `XI` at `s`, and `XferFr` and the `XW` frame from `s0`. -/
def XS (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s0 s : S) : Prop :=
  XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s ∧ XferFr st T Rp s0 s ∧ WritesIn st s0 s (XW T U Ω Sg Scs Z)

variable {U X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {P3Ok : S → Prop}

theorem XferFr.refl (s : S) : XferFr st T Rp s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ _ _ _ => rfl, fun _ _ => rfl, rfl⟩

theorem XferFr.trans {s1 s2 s3 : S} (h1 : XferFr st T Rp s1 s2) (h2 : XferFr st T Rp s2 s3) :
    XferFr st T Rp s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    fun y hy K a b c => (h2.2.2.2.2.1 y hy K a b c).trans (h1.2.2.2.2.1 y hy K a b c),
    fun r hr => (h2.2.2.2.2.2.1 r hr).trans (h1.2.2.2.2.2.1 r hr), h2.2.2.2.2.2.2.trans h1.2.2.2.2.2.2⟩

theorem XS.start {s : S} (h : XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s) :
    XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s := ⟨h, XferFr.refl s, WritesIn.refl _ _⟩

theorem XS.fr {s0 s : S} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) : XferFr st T Rp s0 s := h.2.1

theorem XS.w {s0 s : S} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) :
    WritesIn st s0 s (XW T U Ω Sg Scs Z) := h.2.2

theorem XS.mk {s0 s : S} (h : XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s) (fr : XferFr st T Rp s0 s)
    (w : WritesIn st s0 s (XW T U Ω Sg Scs Z)) : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s := ⟨h, fr, w⟩

/-- An `XferFoot` write. -/
theorem XS.foot {s0 s s' : S} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hw : WritesIn st s s' (XferFoot T U)) : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' := by
  obtain ⟨⟨h1, hB, hX, hS, hSg, hU⟩, fr, w⟩ := h
  obtain ⟨h2, hB2, hX2, hS2, hSg2, ea, ec, ei, ecs, f, o⟩ := xfer_all h1 hB hX hS hSg hU hw
  exact ⟨⟨h2, hB2, hX2, hS2, hSg2, hU.ksb hw.1⟩,
    fr.trans ⟨ea, ec, ei, ecs, f, fun r hr => o _ (hSg.sub _ (hX.1.tcbW hr)), hw.1⟩,
    (w.trans hw).mono fun _ hb => hb.elim id Or.inl⟩

/-- A write of cap-slot words. -/
theorem XS.capw {s0 s s' : S} {B : U64 → Prop} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' := by
  obtain ⟨⟨h1, hB1, hX, hS, hSg, hU⟩, fr, w⟩ := h
  obtain ⟨h2, hB2, hX2, hS2, hSg2, ec, ecs, ea, ei, f, o⟩ := capw_bx h1 hB1 hX hS hSg hw hB
  exact ⟨⟨h2, hB2, hX2, hS2, hSg2, hU.ksb hw.1⟩,
    fr.trans ⟨ea, ec, ei, ecs, fun y hy K a b c => f y hy K (by omega) b c, fun r hr => o _ (hX.1.tcbW hr), hw.1⟩,
    (w.trans hw).mono fun b hb => hb.elim id fun hb => Or.inr (Or.inl (hB b hb))⟩

/-- A write of an SC's `CONSUMED` word. -/
theorem XS.consumed {s0 s : S} {c v : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hc : c ∈ Scs) :
    XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) := by
  obtain ⟨⟨h0, hB, hX, hS, hSg, hU⟩, fr, w⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add c layout.sc.CONSUMED) := by unfold Aligned; rw [hv, hcv]; omega
  have hin : InSC c (Z c) (core.num.U64.wrapping_add c layout.sc.CONSUMED) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  have hm := hO.scW c hc _ hal hin
  have ho := h0.omega _ hm
  have hw := writesIn_wr (st := st) (s := s) (v := v) hal
  obtain ⟨h1, hB1, hX1, hSg1, ea, ec, ecs, -⟩ := ring_bx h0 hB hX hSg hc (hw.mono fun b hb => Or.inr hb)
  have hS1 : SCsOK st T Ω Sg Scs Z Ac (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) := by
    refine SCsOK.wr h0 hS hX hal
      (fun y hy => (out_ne_field (K := 3464#u64) ho hy (h0.tcbs y hy) (by simp)).symm)
      (out_ne_node ho h0.cur (h0.nodes _ h0.cur) (by simp [layout.node.CUR_SC])).symm (fun c' hc' => ?_)
      (scw_ne_spor hO hc (o := 8) (by rw [hv, hcv]) (by omega) (by omega))
      (fun c' hc' e => absurd e (scw_ne_screp hO hc (o := 8) (by rw [hv, hcv]) (by omega) (by omega) c' hc'))
    obtain ⟨h128', -, -, f3, f4, f5, -⟩ := sc_facts hO hc'
    rw [hv, f3, f4, f5, hcv]
    by_cases e : c = c'
    · subst e; omega
    · have := hO.scDisj c hc c' hc' e; omega
  have ani := ani_out (v := v) (h0.nodes _ h0.cur) h0.cur ho
  refine ⟨⟨h1, hB1, hX1, hS1, hSg1, hU.ksb hw.1⟩, fr.trans ⟨ea, ec, ani.2.1, ecs, fun y hy K a b k8 => ?_,
    fun r hr => ?_, hw.1⟩, (w.trans hw).mono fun b hb => hb.elim id fun e => Or.inr (Or.inr ⟨c, hc, e ▸ hin⟩)⟩
  · exact L.mem_wr_ne hal (field_aligned (h0.tcbs y hy) b k8)
      (fun e => out_ne_field ho hy (h0.tcbs y hy) b e.symm)
  · have hp := hO.rp r hr
    refine L.mem_wr_ne hal (h0.omega _ (hSg.sub _ (hO.tcbW hr))).1 ?_
    rw [hv, hcv, rTcbA_val hp]
    have := hO.rpSc r hr c hc
    omega

/-- `XG` is kept along a transfer (its `XW` frame). -/
theorem XG.xs {P3Ok : S → Prop} {s0 s : S} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s0)
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hU : UserOK st T Cs Ω H U s0) :
    XG st T Cs Ω H Sg Scs Z P3Ok s :=
  hG.of_fr (h.w.mono fun _ hb => XW.cur0w hU hb)

/-! ## The transfer's writes -/

-- `BufOK` (the IPC buffer's words are user words) moved to QueueSignal (int6).
theorem obj.Tcb.set_reg.xs {s0 s : S} {y r v : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hy : y ∈ T)
    (hr : r.val < 384) :
    obj.Tcb.set_reg st y s r v ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  have hT := h.1.1.tcbs
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s y r v (hT y hy) hr) fun s' ⟨K, hK, e⟩ => ?_
  subst e
  exact h.foot ((writesIn_wr (field_aligned (hT y hy) (by omega) (by omega))).mono fun b e =>
    Or.inl ⟨y, hy, K, by omega, by omega, e⟩)

theorem msg.buf_set.xs {s0 s : S} {buf i v : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hb : BufOK U buf) (h0 : buf ≠ 0#u64) (hi : i.val < 128) :
    msg.buf_set st s buf i v ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact h.foot ((writesIn_wr (h.1.2.2.2.2.2 _ hu).1.1).mono fun b e => Or.inr (e ▸ hu))

theorem msg.set_mr.xs {s0 s : S} {y buf i v : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ∧ r.1.val ≤ i.val + 4 ⦄ := by
  unfold msg.set_mr
  split
  · have hreg : ∀ j, msg.msg_register j ⦃ r => r.val < 384 ⦄ := fun j => by
      unfold msg.msg_register
      split; · simp [layout.reg.R10]
      split; · simp [layout.reg.R8]
      split; · simp [layout.reg.R9]
      simp [layout.reg.R15]
    refine WP.spec_bind (hreg i) fun r hr => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h hy hr) fun s1 h1 => ?_
    try simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 ⟨h1, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (msg.buf_set.xs (v := v) h hb h0 hi1) fun s1 h1 => ?_
      refine (WP.spec_ok _).2 ⟨h1, ?_⟩
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · exact (WP.spec_ok _).2 ⟨h, by simp [msg.N_MSG_REGISTERS]⟩

theorem msg.msg_register.lt (j : U64) : msg.msg_register j ⦃ r => r.val < 384 ⦄ := by
  unfold msg.msg_register
  split; · simp [layout.reg.R10]
  split; · simp [layout.reg.R8]
  split; · simp [layout.reg.R9]
  simp [layout.reg.R15]

theorem msg.copy_mrs_loop0.xs {s0 s : S} {snd rcv n i : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hr : rcv ∈ T) :
    msg.copy_mrs_loop0 st s snd rcv n i ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun y => 4 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 y.1)
  · rintro ⟨s1, i1⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop0.body
    split
    · split
      · rename_i _ hi
        have hi' : i1.val < 4 := by simpa [msg.N_MSG_REGISTERS] using hi
        refine WP.spec_bind (msg.msg_register.lt i1) fun rg hrg => ?_
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hr hrg) fun s2 h2 => ?_
        step as ⟨i2, hi2⟩
        exact ⟨h2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem msg.copy_mrs_loop1.xs {s0 s : S} {sb rb n i : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hb : BufOK U rb) (h0 : rb ≠ 0#u64) :
    msg.copy_mrs_loop1 st s sb rb n i ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun y => 120 - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop1.body
    split
    · split
      · rename_i _ hi
        have hi' : j.val < 120 := by simpa [msg.MSG_MAX_LENGTH] using hi
        step
        have hi2 := i1_post
        refine WP.spec_bind (P0.msg.buf_get.p0 st s1 sb i1 hS) fun v _ => ?_
        refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 (by omega)) fun s2 h2 => ?_
        exact (WP.spec_ok _).2 ⟨h2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem msg.copy_mrs.xs {s0 s : S} {snd sb rcv rb n : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hr : rcv ∈ T) (hb : BufOK U rb) :
    msg.copy_mrs st s snd sb rcv rb n ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (msg.copy_mrs_loop0.xs (snd := snd) (n := n) (i := 0#u64) h hr) ?_
  rintro ⟨s1, i⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  split
  · exact (WP.spec_ok _).2 h1
  rename_i h0 _
  exact msg.copy_mrs_loop1.xs h1 hb h0

/-- The placement facts of a message transfer (P3's): the receiver's IPC
buffer words are user words; the sender's extra caps and the receiver's
receive slot are cap-slot words; the CDT insert of a granted cap into the
receive slot writes cap-slot words only (the slots and their CDT neighbours
are cap slots). -/
structure XferHyps (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  buf : ∀ Ac X Q R (s : S) (y : U64), XG st T Cs Ω H Sg Scs Z P3Ok s → XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s → y ∈ T →
    msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  extra : ∀ Ac X Q R (s : S) (y b : U64) (tag : msginfo.MessageInfo), XG st T Cs Ω H Sg Scs Z P3Ok s → XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s →
    y ∈ T → ipc.lookup_extra_caps st s y b tag ⦃ r => ∀ e, r = .Ok e → ∀ sl ∈ e.val, sl = 0#u64 ∨ CapW T Ω Sg sl ⦄
  slot : ∀ Ac X Q R (s : S) (y b : U64), XG st T Cs Ω H Sg Scs Z P3Ok s → XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s → y ∈ T →
    ipc.get_receive_slot st s y b ⦃ d => d = 0#u64 ∨ CapW T Ω Sg d ⦄
  ins : ∀ Ac X Q R (s : S) (c : capability.Cap) (src dest : U64), XG st T Cs Ω H Sg Scs Z P3Ok s → XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s →
    CapW T Ω Sg src → CapW T Ω Sg dest → cdt.insert st s c src dest ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄

theorem idx_mem {α : Type} {n : Usize} (v : Aeneas.Std.Array α n) (i : Usize) (hi : i.val < n.val) :
    Aeneas.Std.Array.index_usize v i ⦃ x => x ∈ v.val ⦄ := by
  have hl : i.val < v.val.length := by rw [v.property]; exact hi
  exact WP.spec_mono (Aeneas.Std.Array.index_usize_spec v i hl) fun x e => e ▸ List.getElem_mem hl

theorem ipc.transfer_caps_loop.xs (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s0 s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rb : U64} {out : msginfo.MessageInfo} {dest i : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hG : ∀ s', XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s')
    (hx : ∀ sl ∈ extra.val, sl = 0#u64 ∨ CapW T Ω Sg sl) (hd : dest = 0#u64 ∨ CapW T Ω Sg dest)
    (hb : BufOK U rb) (h0 : rb ≠ 0#u64) :
    ipc.transfer_caps_loop st s extra ep rb out dest i ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.transfer_caps_loop
  apply loop.spec_decr_nat (measure := fun y => 3 - y.2.2.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 y.1 ∧ (y.2.2.1 = 0#u64 ∨ CapW T Ω Sg y.2.2.1))
  · rintro ⟨s1, o1, d1, j⟩ ⟨h1, hd1⟩
    simp only at h1 hd1
    dsimp only
    unfold ipc.transfer_caps_loop.body
    split
    · rename_i hj
      have hj' : j.val < 3 := by simpa using hj
      have hc : (UScalar.cast .Usize j).val = j.val := by
        have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        simp only [UScalar.cast_val_eq, UScalar.size, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by omega)
      have hl : (UScalar.cast .Usize j).val < extra.val.length := by
        rw [hc, extra.property]; simp; omega
      simp only [lift, bind_ok]
      refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra _ hl) fun sl hsl => ?_
      simp only [obj.Slot.is_null, bind_ok]
      split
      · exact (WP.spec_ok _).2 h1
      rename_i hsl0
      refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra _ hl) fun slot hslot => ?_
      have hsw : CapW T Ω Sg slot := by
        rcases hx slot (hslot ▸ List.getElem_mem hl) with e | e
        · have e' : sl = 0#u64 := by rw [hsl, ← hslot]; exact e
          exact absurd (by simp [e']) hsl0
        · exact e
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st slot s1 hS) fun cap _ => ?_
      refine WP.spec_bind (P0.ipc.unwrapped_badge.p0 cap ep) fun o _ => ?_
      rcases o with _ | badge
      · simp only [obj.Slot.is_null, bind_ok]
        split
        · exact (WP.spec_ok _).2 h1
        rename_i hd0
        have hdw : CapW T Ω Sg d1 := hd1.resolve_left fun e => hd0 (by simp [e])
        refine WP.spec_bind (P0.objects.derive_cap.p0 st s1 slot cap hS) fun r _ => ?_
        rcases r with c | _
        · simp only
          refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun b2 _ => ?_
          split
          · exact (WP.spec_ok _).2 h1
          refine WP.spec_bind (E.ins _ _ _ _ s1 c slot d1 (hG s1 h1) h1.1 hsw hdw) fun s2 hw2 => ?_
          step
          exact ⟨h1.capw hw2 fun b hb => hb, Or.inl trivial, by omega⟩
        · exact (WP.spec_ok _).2 h1
      · simp only [msg.BUF_CAPS, msg.BUF_USER_DATA, msg.MSG_MAX_LENGTH]
        step
        step
        try simp only [lift, bind_ok]
        have hix : (core.num.U64.wrapping_add i3 j).val < 128 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        refine WP.spec_bind (msg.buf_set.xs (v := badge) h1 hb h0 hix) fun s2 h2 => ?_
        step*
        exact ⟨h2, hd1, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact ⟨h, hd⟩

theorem ipc.transfer_caps.xs (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s0 s : S}
    {info : msginfo.MessageInfo} {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rcv rb : U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hr : rcv ∈ T)
    (hG : ∀ s', XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s')
    (hx : ∀ sl ∈ extra.val, sl = 0#u64 ∨ CapW T Ω Sg sl) (hb : BufOK U rb) :
    ipc.transfer_caps st s info extra ep rcv rb ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ := by
  unfold ipc.transfer_caps
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun out _ => ?_
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun s1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  split
  · exact (WP.spec_ok _).2 h
  rename_i h0
  refine WP.spec_bind (E.slot _ _ _ _ s rcv rb (hG s h) h.1 hr) fun dest hd => ?_
  refine WP.spec_bind (ipc.transfer_caps_loop.xs (out := out) (i := 0#u64) E h hG hx hd hb h0) ?_
  rintro ⟨s2, o2, i⟩ h2
  exact (WP.spec_ok _).2 h2

theorem ipc.no_extra : ∀ sl ∈ ipc.NO_EXTRA_CAPS.val, sl = 0#u64 ∨ CapW T Ω Sg sl := by
  intro sl hsl
  left
  simp [ipc.NO_EXTRA_CAPS, Aeneas.Std.Array.make] at hsl
  exact hsl

theorem ipc.do_normal_transfer.xs (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s0 : S}
    {snd sb ep badge rcv rb : U64} {grant : Bool}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s0) (hs : snd ∈ T) (hr : rcv ∈ T) (hb : BufOK U rb)
    (hG : ∀ s', XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s') :
    ipc.do_normal_transfer st s0 snd sb ep badge grant rcv rb ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (P0.msg.msg_info.p0 st s0 snd hS) fun tag _ => ?_
  refine WP.spec_bind (Pₘ := fun e : Aeneas.Std.Array obj.Slot 3#usize => ∀ sl ∈ e.val, sl = 0#u64 ∨ CapW T Ω Sg sl)
    ?_ fun extra hx => ?_
  · split
    · refine WP.spec_bind (E.extra _ _ _ _ s0 snd sb tag (hG s0 h) h.1 hs) fun r hr' => ?_
      rcases r with e | _
      · exact (WP.spec_ok _).2 (hr' e rfl)
      · exact (WP.spec_ok _).2 ipc.no_extra
    · exact (WP.spec_ok _).2 ipc.no_extra
  refine WP.spec_bind (msg.copy_mrs.xs (snd := snd) (sb := sb) (n := tag.length) h hr hb) ?_
  rintro ⟨n, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (ipc.transfer_caps.xs (info := tag) (ep := ep) E h1 hr (fun s' h' => hG s' h') hx hb) ?_
  rintro ⟨out, s2⟩ h2
  simp only at h2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s3 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xs h3 hr (by simp [layout.reg.BADGE, layout.reg.RDI])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xs (v := w) h2 hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

theorem faults.copy_mrs_fault_loop0.xs {s0 s : S} {snd rcv : U64} {regs : Slice U64} {i : Usize}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hr : rcv ∈ T) (hi : i.val ≤ (Slice.len regs).val) :
    faults.copy_mrs_fault_loop0 st s snd rcv regs i ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.1 ∧
      r.2.val ≤ (Slice.len regs).val ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 y.1 ∧ y.2.val ≤ (Slice.len regs).val)
  · rintro ⟨s1, j⟩ ⟨h1, hj1⟩
    simp only at h1 hj1
    dsimp only
    unfold faults.copy_mrs_fault_loop0.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      simp only [lift, bind_ok]
      split
      · step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
        refine WP.spec_bind (msg.msg_register.lt _) fun rg hrg => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xs (v := v) h1 hr hrg) fun s2 h2 => ?_
        step as ⟨j2, hj2⟩
        exact ⟨h2, by omega, by omega⟩
      · exact (WP.spec_ok _).2 ⟨h1, hj1⟩
    · rename_i hj
      exact (WP.spec_ok _).2 ⟨h1, hj1⟩
  · exact ⟨h, hi⟩

theorem faults.copy_mrs_fault_loop1.xs {s0 s : S} {snd buf : U64} {regs : Slice U64} {i : Usize}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64)
    (hl : (Slice.len regs).val < 127) :
    faults.copy_mrs_fault_loop1 st s snd regs buf i ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_loop1.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .U64 j).val = j.val := by
        have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        have := j.hBounds
        simp only [UScalar.cast_val_eq, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)
      have hix : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hc]; omega
      refine WP.spec_bind (msg.buf_set.xs (v := v) h1 hb h0 hix) fun s2 h2 => ?_
      step as ⟨j2, hj2⟩
      exact ⟨h2, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault.xs {s0 s : S} {snd rcv buf : U64} {regs : Slice U64}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hr : rcv ∈ T) (hb : BufOK U buf)
    (hl : (Slice.len regs).val < 127) :
    faults.copy_mrs_fault st s snd rcv regs buf ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (faults.copy_mrs_fault_loop0.xs (snd := snd) (regs := regs) (i := 0#usize) h hr (by simp)) ?_
  rintro ⟨s1, i⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · rename_i hne
    exact faults.copy_mrs_fault_loop1.xs h1 hb (by simpa using hne) hl
  · exact (WP.spec_ok _).2 h1

theorem faults.set_mrs_lookup_failure.xs {s0 s : S} {rcv buf off : U64} {lf : error.LookupFault}
    (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hr : rcv ∈ T) (hb : BufOK U buf) (ho : off.val < 124) :
    faults.set_mrs_lookup_failure st s rcv buf lf off ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ := by
  unfold faults.set_mrs_lookup_failure
  have hk : ∀ k : U64, k.val < 4 → (core.num.U64.wrapping_add off k).val < 127 := fun k hk => by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.error.LookupFault.type_code.p0 lf) fun i _ => ?_
  refine WP.spec_bind (msg.set_mr.xs (v := i) h hr hb (by omega)) ?_
  rintro ⟨i1, s1⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  · try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xs h1 hr hb (hk 1#u64 (by simp))) fun r hr' => hr'.1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xs h1 hr hb (hk 1#u64 (by simp))) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xs h2 hr hb (hk 2#u64 (by simp))) fun r hr' => hr'.1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xs h1 hr hb (hk 1#u64 (by simp))) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xs h2 hr hb (hk 2#u64 (by simp))) ?_
    rintro ⟨_, s3⟩ ⟨h3, -⟩
    simp only at h3
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xs h3 hr hb (hk 3#u64 (by simp))) fun r hr' => hr'.1

theorem schedcontext.update_consumed.xs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    {c : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ := by
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ => (WP.spec_ok _).2 (h.consumed hc)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ => (WP.spec_ok _).2 (h.consumed hc)

/-- Some `set_mr`s in a row, ending the computation. -/
theorem set_mr_last {s0 s : S} {y buf i v : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ⦄ :=
  WP.spec_mono (msg.set_mr.xs h hy hb hi) fun _ h' => h'.1

set_option hygiene false in
/-- One `set_mr` of the receiver, from the state of `hcur`. -/
local macro "smr" : tactic => `(tactic| (
  refine WP.spec_bind (msg.set_mr.xs hcur hr hb (by simp)) ?_
  rintro ⟨_, s'⟩ ⟨hcur, -⟩
  try simp only at hcur
  try simp only [WP.uncurry'_pair]))

theorem faults.set_mrs_fault.xs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {snd rcv buf : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hb : BufOK U buf) :
    faults.set_mrs_fault st ar s a snd rcv buf ⦃ r => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.set_mrs_fault
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hS) fun ty _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  have hcur := h
  split
  · smr; smr; smr
    refine WP.spec_bind (P0.faults.lookup_failure.p0 st s' snd hS) fun lf _ => ?_
    exact faults.set_mrs_lookup_failure.xs hcur hr hb (by simp)
  split
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (faults.copy_mrs_fault.xs (snd := snd) h hr hb (by simp [faults.SYSCALL_MESSAGE])) fun s2 h2 => ?_
    exact set_mr_last h2 hr hb (by simp)
  split
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (faults.copy_mrs_fault.xs (snd := snd) h hr hb (by simp [faults.EXCEPTION_MESSAGE]))
      fun s2 hcur => ?_
    smr
    exact set_mr_last hcur hr hb (by simp)
  split
  · step with obj.Tcb.sc.spec as ⟨c, hc⟩
    simp only [obj.Sc.is_null, bind_ok]
    split
    · exact set_mr_last h hr hb (by simp)
    rename_i hne
    have hc0 : L.mem s (scA snd) ≠ 0#u64 := by rw [← hc]; simpa using hne
    have hcS : c ∈ Scs := hc ▸ (h.1.2.2.1.2.2.bound snd hs hc0).1
    refine WP.spec_bind (schedcontext.update_consumed.xs hA h hcS) ?_
    rintro ⟨cons, s1⟩ h1
    simp only at h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (msg.set_mr.xs h1 hr hb (by simp)) ?_
    rintro ⟨len, s2⟩ ⟨h2, hl2⟩
    simp only at h2 hl2
    try simp only [WP.uncurry'_pair]
    exact set_mr_last h2 hr hb (by simp at hl2; omega)
  split
  · smr
    refine WP.spec_bind (msg.set_mr.xs hcur hr hb (by simp)) ?_
    rintro ⟨ret, s2⟩ ⟨hcur, -⟩
    simp only at hcur
    try simp only [WP.uncurry'_pair]
    split
    · split
      · smr
        exact set_mr_last hcur hr hb (by simp)
      · exact (WP.spec_ok _).2 hcur
    · exact (WP.spec_ok _).2 hcur
  split
  · smr; smr; smr
    exact set_mr_last hcur hr hb (by simp)
  · exact (WP.spec_ok _).2 h

theorem ipc.do_fault_transfer.xs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {badge snd rcv rb : U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hb : BufOK U rb) :
    ipc.do_fault_transfer st ar s a badge snd rcv rb ⦃ s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (faults.set_mrs_fault.xs hA h hs hr hb) ?_
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xs h3 hr (by simp [layout.reg.BADGE, layout.reg.RDI])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xs (v := w) h1 hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

/-- **EntryHyps' `xfer`: the message transfer keeps the invariants within
`XferFr`**, from the placement facts `XferHyps`. -/
theorem xferOK_of {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XG st T Cs Ω H Sg Scs Z P3Ok) := by
  intro Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hG0
  have hP : P0.StoreTotal st := L.total
  have h0 : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s := XS.start ⟨h, hB, hX, hS, hSg, hU⟩
  have hG : ∀ s', XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s' → XG st T Cs Ω H Sg Scs Z P3Ok s' :=
    fun s' h' => XG.xs hG0 h' hU
  refine WP.spec_mono (P₀ := fun s' => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s') ?_
    fun s' h'' => ⟨h''.1.1, h''.1.2.1, h''.1.2.2.1, h''.1.2.2.2.1, h''.1.2.2.2.2.1, h''.fr, hG s' h''⟩
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (E.buf _ _ _ _ s rcv hG0 h0.1 hr) fun rb hb => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hP) fun ft _ => ?_
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false snd hP) fun sb _ => ?_
    exact ipc.do_normal_transfer.xs E h0 hs hr hb hG
  · exact ipc.do_fault_transfer.xs hA h0 hs hr hb

end

end Fl4Proofs.P1
