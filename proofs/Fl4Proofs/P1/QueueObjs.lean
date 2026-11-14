/-
P1: reply objects and scheduling contexts as placed, disjoint objects, and
the invariants about them that `schedule`, `cancel_ipc`, `suspend` and
`restart` rely on:

* `ObjsOK`: reply objects (32 bytes, aligned) and SCs (`2 ^ Z c` bytes,
  `Placed`) are pairwise disjoint and lie among the other objects' words
  `Ω`; the reply words and the SCs' `CORE`/`TCB` words are frame words `Sg`.
* `ReplyInv` (l4v reply invariants): a thread blocked on reply has a reply
  object whose `TCB` word names it; so has a receiver with a reply object;
  the `next` link of a reply is an SC (head bit set) or a reply, its `prev`
  link a reply.
* `ScExtra` (l4v `sc_tcb_sc_at`, `valid_objs`): a bound TCB's SC is an SC
  object whose `TCB` word names it back and whose `CORE` word is a core; the
  current SC is an SC object.
-/
import Fl4Proofs.P1.QueueCancel
import Fl4Proofs.P1.QueueSchedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64}
variable {Cs Sg Rp Scs : Set U64} {Z : U64 → Nat}


/-- The reply invariants. -/
structure ReplyInv (st : machine.Store S) [L : LawfulStore st] (T Rp Scs : Set U64) (s : S) : Prop where
  reply : ∀ t ∈ T, L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY →
    L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t
  recv : ∀ t ∈ T, L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s (replyA t) ≠ 0#u64 →
    L.mem s (replyA t) ∈ Rp ∧ L.mem s (rTcbA (L.mem s (replyA t))) = t
  next : ∀ r ∈ Rp, L.mem s (rNextA r) &&& ~~~1#u64 ≠ 0#u64 →
    (headBit (L.mem s (rNextA r)) = true → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Scs) ∧
    (headBit (L.mem s (rNextA r)) = false → L.mem s (rNextA r) &&& ~~~1#u64 ∈ Rp)
  prev : ∀ r ∈ Rp, L.mem s (rPrevA r) &&& ~~~1#u64 ≠ 0#u64 → L.mem s (rPrevA r) &&& ~~~1#u64 ∈ Rp

/-- Bound SCs are SC objects naming their thread and a core. -/
structure ScExtra (st : machine.Store S) [L : LawfulStore st] (T Cs Scs : Set U64) (s : S) : Prop where
  bound : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 →
    L.mem s (scA t) ∈ Scs ∧ L.mem s (scTcbA (L.mem s (scA t))) = t ∧ L.mem s (scCoreA (L.mem s (scA t))) ∈ Cs
  cur : L.cscW s ∈ Scs

/-- The object invariants together. -/
def XInv (st : machine.Store S) [L : LawfulStore st] (T Cs Ω Sg Rp Scs : Set U64) (Z : U64 → Nat) (s : S) : Prop :=
  ObjsOK st Ω Sg Rp Scs Z s ∧ ReplyInv st T Rp Scs s ∧ ScExtra st T Cs Scs s

/-! ## Under a frame -/

/-- `XInv` only reads the reply words, the SCs' `TCB`/`CORE` words, the TCBs'
reply, state and SC fields, and the current SC. -/
theorem XInv.keep {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Z s)
    (hrw : ∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r) ∧ L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧
      L.mem s' (rNextA r) = L.mem s (rNextA r))
    (hfx : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c))
    (hsc : ∀ t ∈ T, L.mem s' (scA t) = L.mem s (scA t))
    (hrep : ∀ t ∈ T, L.mem s' (replyA t) = L.mem s (replyA t))
    (hst : ∀ t ∈ T, L.mem s' (stA t) = L.mem s (stA t))
    (hcs : L.cscW s' ∈ Scs) : XInv st T Cs Ω Sg Rp Scs Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  refine ⟨hO.ksb, ⟨fun t ht hs => ?_, fun t ht hs hn => ?_, fun r hr => ?_, fun r hr => ?_⟩,
    ⟨fun t ht hb => ?_, hcs⟩⟩
  · rw [hst t ht] at hs
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    rw [hrep t ht, (hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [hst t ht] at hs; rw [hrep t ht] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv t ht hs hn
    rw [(hrw _ h1).1]; exact ⟨h1, h2⟩
  · rw [(hrw r hr).2.2]; exact hR.next r hr
  · rw [(hrw r hr).2.1]; exact hR.prev r hr
  · rw [hsc t ht] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound t ht hb
    rw [(hfx _ h1).1, (hfx _ h1).2]; exact ⟨h1, h2, h3⟩

theorem XInv.fr {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Z s) (f : Fr st T Sg s s') :
    XInv st T Cs Ω Sg Rp Scs Z s' :=
  hX.keep (fun r hr => ⟨f.sig _ (hX.1.tcbW hr), f.sig _ (hX.1.prevW hr), f.sig _ (hX.1.nextW hr)⟩)
    (fun c hc => ⟨f.sig _ (hX.1.fixW c hc).1, f.sig _ (hX.1.fixW c hc).2⟩) f.sc f.rep f.st
    (by rw [f.csc]; exact hX.2.2.cur)

/-! ## Writes that avoid the protected words -/

/-- The words `XInv` reads (besides the current SC). -/
def Prot (T Rp Scs : Set U64) (b : U64) : Prop :=
  (∃ r ∈ Rp, b = rTcbA r ∨ b = rPrevA r ∨ b = rNextA r) ∨ (∃ c ∈ Scs, b = scTcbA c ∨ b = scCoreA c) ∨
  (∃ t ∈ T, b = scA t ∨ b = replyA t ∨ b = stA t)

theorem ObjsOK.aligned (h : ObjsOK st Ω Sg Rp Scs Z s) (hT : TcbPlaced T) {b : U64} (hb : Prot T Rp Scs b) :
    Aligned b := by
  rcases hb with ⟨r, hr, e⟩ | ⟨c, hc, e⟩ | ⟨t, ht, e⟩
  · have hp := h.rp r hr
    rcases e with rfl | rfl | rfl <;> unfold Aligned
    · rw [rTcbA_val hp]; omega
    · rw [rPrevA_val hp]; omega
    · rw [rNextA_val hp]; omega
  · obtain ⟨hP, hz⟩ := h.sc c hc
    have := (sc_lo hP hz).1
    rcases e with rfl | rfl <;> unfold Aligned
    · rw [scTcbA_val hP hz]; omega
    · rw [scCoreA_val hP hz]; omega
  · rcases e with rfl | rfl | rfl
    · exact scA_aligned (hT t ht)
    · exact field_aligned (hT t ht) (by simp) (by simp)
    · rw [stA_eq]; exact field_aligned (hT t ht) (by simp) (by simp)

/-- `XInv` after writes that avoid the protected words, given the new
current SC is an SC object. -/
theorem XInv.writes {s s' : S} {B : U64 → Prop} (hX : XInv st T Cs Ω Sg Rp Scs Z s) (hT : TcbPlaced T)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → ¬ Prot T Rp Scs b) (hcs : L.cscW s' ∈ Scs) :
    XInv st T Cs Ω Sg Rp Scs Z s' := by
  have k : ∀ b, Prot T Rp Scs b → L.mem s' b = L.mem s b := fun b hb =>
    hw.mem_eq (hX.1.aligned hT hb) (fun h => hB b h hb)
  exact hX.keep (fun r hr => ⟨k _ (Or.inl ⟨r, hr, Or.inl rfl⟩), k _ (Or.inl ⟨r, hr, Or.inr (Or.inl rfl)⟩),
      k _ (Or.inl ⟨r, hr, Or.inr (Or.inr rfl)⟩)⟩)
    (fun c hc => ⟨k _ (Or.inr (Or.inl ⟨c, hc, Or.inl rfl⟩)), k _ (Or.inr (Or.inl ⟨c, hc, Or.inr rfl⟩))⟩)
    (fun t ht => k _ (Or.inr (Or.inr ⟨t, ht, Or.inl rfl⟩)))
    (fun t ht => k _ (Or.inr (Or.inr ⟨t, ht, Or.inr (Or.inl rfl)⟩)))
    (fun t ht => k _ (Or.inr (Or.inr ⟨t, ht, Or.inr (Or.inr rfl)⟩))) hcs

/-- Protected words are words of `Ω` or TCB fields. -/
theorem ObjsOK.prot_cases (h : ObjsOK st Ω Sg Rp Scs Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) {b : U64}
    (hb : Prot T Rp Scs b) : b ∈ Ω ∨ ∃ t ∈ T, ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add t K := by
  rcases hb with ⟨r, hr, e⟩ | ⟨c, hc, e⟩ | ⟨t, ht, e⟩
  · left; rcases e with rfl | rfl | rfl
    · exact hsub _ (h.tcbW hr)
    · exact hsub _ (h.prevW hr)
    · exact hsub _ (h.nextW hr)
  · left; rcases e with rfl | rfl
    · exact hsub _ (h.fixW c hc).1
    · exact hsub _ (h.fixW c hc).2
  · right; refine ⟨t, ht, ?_⟩
    rcases e with rfl | rfl | rfl
    · exact ⟨3464#u64, by simp, rfl⟩
    · exact ⟨3360#u64, by simp, rfl⟩
    · exact ⟨3328#u64, by simp, stA_eq t⟩

/-- Node words are not protected. -/
theorem not_prot_node {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    {c o : U64} (hc : c ∈ Cs) (ho : o.val < 4288) : ¬ Prot T Rp Scs (L.nodeAt s c o) := by
  intro hp
  rcases hO.prot_cases hsub hp with hm | ⟨t, ht, K, hK, e⟩
  · exact out_ne_node (h.omega _ hm) hc (h.nodes c hc) ho rfl
  · exact node_ne_field (h.nodes c hc) ho ht (h.tcbs t ht) hK e

/-- The ring and `CONSUMED` word of an SC object are not protected. -/
theorem not_prot_ring {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Z s) {c b : U64} (hc : c ∈ Scs)
    (hb : Aligned b) (hr : InRing c (Z c) b ∨ b = core.num.U64.wrapping_add c layout.sc.CONSUMED) :
    ¬ Prot T Rp Scs b := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨-, h128, -⟩ := sc_lo hP hz
  have hbv : (c.val + 72 ≤ b.val ∨ b.val = c.val + 8) ∧ b.val < c.val + 2 ^ Z c := by
    rcases hr with ⟨h1, h2⟩ | rfl
    · exact ⟨Or.inl h1, h2⟩
    · rw [sc_word_val hP hz (by simp [layout.sc.CONSUMED])]; simp [layout.sc.CONSUMED]; omega
  have hin : InSC c (Z c) b := ⟨by omega, hbv.2⟩
  rintro (⟨r, hr', e⟩ | ⟨c', hc', e⟩ | ⟨t, ht, e⟩)
  · have hp := hO.rp r hr'
    have hrv : b.val = r.val ∨ b.val = r.val + 8 ∨ b.val = r.val + 16 := by
      rcases e with rfl | rfl | rfl
      · exact Or.inl (rTcbA_val hp)
      · exact Or.inr (Or.inl (rPrevA_val hp))
      · exact Or.inr (Or.inr (rNextA_val hp))
    have := hO.rpSc r hr' c hc
    omega
  · obtain ⟨hP', hz'⟩ := hO.sc c' hc'
    obtain ⟨-, h128', -⟩ := sc_lo hP' hz'
    have hcv : b.val = c'.val + 24 ∨ b.val = c'.val + 16 := by
      rcases e with rfl | rfl
      · exact Or.inl (scTcbA_val hP' hz')
      · exact Or.inr (scCoreA_val hP' hz')
    by_cases e' : c = c'
    · subst e'; omega
    · have := hO.scDisj c hc c' hc' e'; omega
  · have hm := hO.scW c hc b hb hin
    have hout := (h.omega _ hm).2.1 t ht
    have hv : b.val = t.val + 3464 ∨ b.val = t.val + 3360 ∨ b.val = t.val + 3328 := by
      rcases e with rfl | rfl | rfl
      · left; rw [scA_eq, field_val (h.tcbs t ht) (by simp)]; simp
      · right; left; unfold replyA; rw [field_val (h.tcbs t ht) (by simp)]; simp
      · right; right; rw [stA_eq, field_val (h.tcbs t ht) (by simp)]; simp
    omega

/-! ## Under `KeepT` (what `cancel_ipc` keeps) -/

theorem KeepT.curW {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') : L.curW s' = L.curW s :=
  k.nd _ (by rw [curth0]; omega)
theorem KeepT.idleW {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') : L.idleW s' = L.idleW s :=
  k.nd _ (by rw [idle8]; omega)
theorem KeepT.cscW {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') : L.cscW s' = L.cscW s :=
  k.nd _ (by simp [layout.node.CUR_SC])
theorem KeepT.scf {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (scA y) = L.mem s (scA y) := by
  rw [scA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
theorem KeepT.inqf {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (inqA y) = L.mem s (inqA y) := by
  rw [inqA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
theorem KeepT.repf {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (replyA y) = L.mem s (replyA y) :=
  k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
theorem KeepT.stf {t : U64} {s s' : S} (k : KeepT st T Rp Scs t s s') {y : U64} (hy : y ∈ T) (hyt : y ≠ t) :
    L.mem s' (stA y) = L.mem s (stA y) := by
  rw [stA_eq]; exact k.fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e hyt)

/-- `BoundInv` under `KeepT`. -/
theorem BoundInv.keepT {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64} {s s' : S}
    (h : SchedQueuesInvX st T Cs Ω X s Q R) (hB : BoundInv st T s) (k : KeepT st T Rp Scs t s s') :
    BoundInv st T s' := by
  refine hB.mk' (fun y hy => k.scf hy) (fun y hy hf => Or.inl (by rw [← k.inqf hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← k.inqf hy]; exact hf))) (fun haT => ?_)
    (by rw [k.idleW]; exact ⟨h.idleT, hB.idle⟩) (fun h0 => ?_)
  · rcases k.act with e | e
    · rw [e] at haT ⊢; exact ⟨haT, hB.act haT⟩
    · rw [e] at haT; exact absurd haT (notT_small h.tcbs (by simp))
  · rcases k.act with e | e
    · rw [e] at h0; rw [k.curW]; exact ⟨h.curT, hB.resume h0⟩
    · rw [e] at h0; simp at h0

/-- `XInv` under `KeepT`, when `t` ends neither blocked on reply nor on
receive. -/
theorem XInv.keepT {t : U64} {s s' : S} (hX : XInv st T Cs Ω Sg Rp Scs Z s) (k : KeepT st T Rp Scs t s s')
    (hst : L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s' (stA t) ≠ sched.TS_BLOCKED_ON_RECV) :
    XInv st T Cs Ω Sg Rp Scs Z s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  have rt : ∀ u ∈ T, u ≠ t → ∀ r ∈ Rp, L.mem s (rTcbA r) = u → L.mem s' (rTcbA r) = u := by
    intro u hu hut r hr e
    rcases k.rtcb r hr with e' | e'
    · rw [e']; exact e
    · exact absurd (e.symm.trans e') hut
  refine ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr hn => ?_, fun r hr hp => ?_⟩,
    ⟨fun u hu hb => ?_, by rw [k.cscW]; exact hE.cur⟩⟩
  · by_cases e : u = t
    · subst e; exact absurd hs hst.1
    rw [k.stf hu e] at hs
    obtain ⟨h1, h2⟩ := hR.reply u hu hs
    rw [k.repf hu]; exact ⟨h1, rt u hu e _ h1 h2⟩
  · by_cases e : u = t
    · subst e; exact absurd hs hst.2
    rw [k.stf hu e] at hs; rw [k.repf hu] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv u hu hs hn
    exact ⟨h1, rt u hu e _ h1 h2⟩
  · rcases (k.rlink r hr).2 with e | e
    · rw [e] at hn ⊢; exact hR.next r hr hn
    · exact absurd e hn
  · rcases (k.rlink r hr).1 with e | e
    · rw [e] at hp ⊢; exact hR.prev r hr hp
    · exact absurd e hp
  · rw [k.scf hu] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
    obtain ⟨f1, f2, -⟩ := k.fix _ h1
    rw [f1, f2]; exact ⟨h1, h2, h3⟩

/-- `cancel_ipc` keeps the queue invariant, `BoundInv` and `XInv`; the reply
facts it needs come from `XInv`. -/
theorem ipc.cancel_ipc.all {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω s Q R) (ht : t ∈ T)
    (hB : BoundInv st T s) (hX : XInv st T Cs Ω Sg Rp Scs Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) :
    ipc.cancel_ipc st ar s a t ⦃ s' _ => SchedQueuesInv st T Cs Ω s' Q R ∧ BoundInv st T s' ∧
      XInv st T Cs Ω Sg Rp Scs Z s' ∧ ¬ Blocked (L.mem s' (stA t)) ∧
      (L.mem s' (stA t) = sched.TS_INACTIVE ∨
        (L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' = L.actionW s)) ∧ KeepT st T Rp Scs t s s' ⦄ := by
  obtain ⟨hO, hR, hE⟩ := hX
  have hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  refine WP.spec_mono (ipc.cancel_ipc.inv s a t Q R h ht hO hsub (hR.recv t ht) hreply) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  obtain ⟨h', nb, nr, hst, k⟩ := hr
  exact ⟨h', hB.keepT h k, XInv.keepT (Z := Z) (Ω := Ω) (Sg := Sg) ⟨hO, hR, hE⟩ k
    ⟨nr, fun e => nb (Or.inr (Or.inl e))⟩, nb, hst, k⟩

end

end Fl4Proofs.P1
