/-
P1: the blocking side of IPC: a thread blocks on an endpoint or notification
(`ep_append` / `ntfn_append`, from `send_ipc`, `receive_ipc`'s
`wait_for_sender` and `receive_signal`), keeping `SchedQueuesInv` (with
`EpTy`), `BoundInv`, `XInv` and `SCsOK`.
-/
import Fl4Proofs.P1.QueueSuspend
import Fl4Proofs.P1.QueueAppend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- A thread in the exception set, blocked on `e`, joins `e`'s queue: it
leaves the exception set. The queue's members share its state and the
object's state word is the code of that state. -/
theorem inv_ep_ins {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {e t : U64} {xs' : List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E)
    (ht : t ∈ T) (htX : t ∈ X) (hbt : L.mem s (blockA t) = e) (hbs : Blocked (L.mem s (stA t)))
    (hkE : (L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND ∨ L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV) →
      H e = some .ep)
    (hkN : L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN → H e = some .ntfn)
    (hsame : ∀ y ∈ EQ e, L.mem s (stA y) = L.mem s (stA t))
    (hcode : (L.mem s (stA t) = sched.TS_BLOCKED_ON_SEND → L.epState s' e = 1#u64) ∧
      (L.mem s (stA t) = sched.TS_BLOCKED_ON_RECV → L.epState s' e = 2#u64) ∧
      (L.mem s (stA t) = sched.TS_BLOCKED_ON_NTFN → L.epState s' e = 1#u64))
    (hw : WritesIn st s s' (EpFoot (t :: EQ e) e))
    (hq' : QueueRel (L.mem s') T .Ep (L.epQ s' e) xs') (hmem' : ∀ y, y ∈ xs' ↔ y = t ∨ y ∈ EQ e) :
    SchedQueuesInvX st T Cs Ω H {y | y ∈ X ∧ y ≠ t} s' Q R := by
  have hT := h.tcbs
  obtain ⟨w1, w2, w5, w3, w4, w6⟩ := hEW
  obtain ⟨hE, hEN, hq⟩ := w1 e he
  have hWT : ∀ w ∈ t :: EQ e, w ∈ T := by
    intro w hw; rcases List.mem_cons.1 hw with rfl | hw
    · exact ht
    · exact hq.mem w hw
  have htm : t ∉ EQ e := fun hm => (w3 e he t hm).1 htX
  have epv : ∀ (e' a : U64), EpPlaced T e' → (a = epHeadA e' ∨ a = epTSA e') →
      a.val = e'.val ∨ a.val = e'.val + 8 := by
    rintro e' a hE' (rfl | rfl)
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE')
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 h1 h2
    refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · rw [nextA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [nextOff]) (fun _ => by simp [nextOff]; exact h1) e'
    · rw [prevA_eq'] at e'
      exact field_ne (hT y hy) (hT w (hWT w hw')) hK (by simp [prevOff]) (fun _ => by simp [prevOff]; exact h2) e'
    · have hv := epv e _ hE e'
      rw [field_val (hT y hy) hK] at hv
      have := hE.disj y hy
      omega
  have nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) := by
    intro c hc o ho h8
    have hN := h.nodes c hc
    refine hw.mem_eq (nodeAt_aligned hN ho h8) ?_
    rintro (⟨w, hw', e' | e'⟩ | e')
    · exact nodeAt_ne_nextA hN ho (hWT w hw') (hT w (hWT w hw')) _ e'
    · exact nodeAt_ne_prevA hN ho (hWT w hw') (hT w (hWT w hw')) _ e'
    · have hv := epv e _ hE e'
      rw [nodeAt_val hN ho] at hv
      have := hEN.1 c hc
      omega
  have oth : ∀ e' ∈ E, e' ≠ e → ∀ a, (a = epHeadA e' ∨ a = epTSA e') → L.mem s' a = L.mem s a := by
    intro e' he' hne a ha
    have hE' := (w1 e' he').1
    have hal : Aligned a := by
      rcases ha with rfl | rfl
      · exact (ep_aligned hE').1
      · exact (ep_aligned hE').2
    have hav := epv e' a hE' ha
    refine hw.mem_eq hal ?_
    rintro (⟨w, hw', e2 | e2⟩ | e2)
    · have := nextA_inside (hT w (hWT w hw')) .Ep; rw [← e2] at this
      have := hE'.disj w (hWT w hw'); omega
    · have := prevA_inside (hT w (hWT w hw')) .Ep; rw [← e2] at this
      have := hE'.disj w (hWT w hw'); omega
    · have hv := epv e a hE e2
      have := w2 e' he' e he hne; omega
  have hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y) :=
    fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp)⟩
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    exact nod _ h.cur _ (by rw [act_val]; omega) (by rw [act_val])
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, hw.1]
  have hmemE : ∀ y, y ∈ Function.update EQ e xs' e ↔ y = t ∨ y ∈ EQ e := fun y => by
    rw [Function.update_self]; exact hmem' y
  refine inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩) (fun c hc o h1 h2 _ => nod c hc o h1 h2)
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp))
    (fun y hy => Or.inl (fld y hy _ (by simp) (by simp) (by simp) (by simp))) (by rw [hact]; exact h.action) hsb
    (by rw [hact]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT) ?_
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [curth0]; omega) (by rw [curth0])]; exact h.curT)
    (by rw [hw.2.1, nodeAt_of_ksb hw.1, nod _ h.cur _ (by rw [idle8]; omega) (by rw [idle8])]; exact h.idleT)
  · rw [nextA_eq']; exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']; exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  obtain ⟨k1, k2, k0, k3, k4, k5⟩ := w6
  refine ⟨E, Function.update EQ e xs', fun e' he' => ?_, w2, w5, fun e' he' y hy => ?_, fun y hy hyX hb => ?_,
    ⟨fun y hy hyX hs => ?_, fun y hy hyX hs => ?_, k0, fun e' he' y hy z hz => ?_, fun e' he' y hy => ?_,
      fun e' he' h0 => ?_⟩⟩
  · refine ⟨(w1 e' he').1, ⟨fun c hc => by rw [hnb]; exact (w1 e' he').2.1.1 c hc, by rw [hw.1]; exact (w1 e' he').2.1.2⟩, ?_⟩
    by_cases hee : e' = e
    · subst hee; rw [Function.update_self]; exact hq'
    · rw [Function.update_of_ne hee]
      have hq2 := (w1 e' he').2.2
      have eq : L.epQ s' e' = L.epQ s e' := by
        simp only [LawfulStore.epQ, oth e' he' hee _ (Or.inl rfl), oth e' he' hee _ (Or.inr rfl)]
      rw [eq]
      refine ⟨hq2.nodup, hq2.mem, hq2.head, hq2.last, hq2.seg.congr fun y hy => ?_⟩
      have hyT := hq2.mem y hy
      have hyE : y ∉ t :: EQ e := by
        intro hm; rcases List.mem_cons.1 hm with rfl | hm
        · exact (w3 e' he' y hy).1 htX
        · exact hee ((w3 e' he' y hy).2.1.symm.trans (w3 e he y hm).2.1)
      have hk := fun (K : U64) (hK : K.val < 4096) (hK8 : K.val % 8 = 0) (hKl : K.val = 3496 ∨ K.val = 3504) =>
        hw.mem_eq (field_aligned (hT y hyT) hK hK8) (by
          rintro (⟨w, hw', e2 | e2⟩ | e2)
          · have hwy : w ≠ y := fun h' => hyE (h' ▸ hw')
            rw [nextA_eq'] at e2
            exact field_ne (hT y hyT) (hT w (hWT w hw')) hK (by simp [nextOff])
              (fun h' => absurd h'.symm hwy) e2
          · have hwy : w ≠ y := fun h' => hyE (h' ▸ hw')
            rw [prevA_eq'] at e2
            exact field_ne (hT y hyT) (hT w (hWT w hw')) hK (by simp [prevOff])
              (fun h' => absurd h'.symm hwy) e2
          · have hv := epv e _ hE e2
            rw [field_val (hT y hyT) hK] at hv
            have := hE.disj y hyT; omega)
      exact ⟨by rw [prevA_eq']; exact hk _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]),
        by rw [nextA_eq']; exact hk _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])⟩
  · by_cases hee : e' = e
    · subst hee
      rcases (hmemE y).1 hy with rfl | hy'
      · exact ⟨fun hX => hX.2 rfl, by rw [(hsb _ ht).2]; exact hbt, by rw [(hsb _ ht).1]; exact hbs⟩
      · have := w3 e' he y hy'
        have hyT := hq.mem y hy'
        exact ⟨fun hX => this.1 hX.1, by rw [(hsb y hyT).2]; exact this.2.1, by rw [(hsb y hyT).1]; exact this.2.2⟩
    · rw [Function.update_of_ne hee] at hy
      have := w3 e' he' y hy
      have hyT := (w1 e' he').2.2.mem y hy
      exact ⟨fun hX => this.1 hX.1, by rw [(hsb y hyT).2]; exact this.2.1, by rw [(hsb y hyT).1]; exact this.2.2⟩
  · rw [(hsb y hy).1] at hb
    rw [(hsb y hy).2]
    by_cases hyt : y = t
    · subst hyt
      rw [hbt]; exact ⟨he, (hmemE y).2 (Or.inl rfl)⟩
    · have hyX0 : y ∉ X := fun hX => hyX ⟨hX, hyt⟩
      obtain ⟨hbE, hmem⟩ := w4 y hy hyX0 hb
      refine ⟨hbE, ?_⟩
      by_cases hee : L.mem s (blockA y) = e
      · rw [hee, Function.update_self]; rw [hee] at hmem; exact (hmem' y).2 (Or.inr hmem)
      · rw [Function.update_of_ne hee]; exact hmem
  -- `EpTy`
  · rw [(hsb y hy).1] at hs; rw [(hsb y hy).2]
    by_cases hyt : y = t
    · subst hyt; rw [hbt]; exact hkE hs
    · exact k1 y hy (fun hX => hyX ⟨hX, hyt⟩) hs
  · rw [(hsb y hy).1] at hs; rw [(hsb y hy).2]
    by_cases hyt : y = t
    · subst hyt; rw [hbt]; exact hkN hs
    · exact k2 y hy (fun hX => hyX ⟨hX, hyt⟩) hs
  · have st' : ∀ w, w ∈ Function.update EQ e' xs' e' → e' = e → L.mem s' (stA w) = L.mem s (stA t) := by
      intro w hwm ee; subst ee
      rcases (hmemE w).1 hwm with rfl | hw'
      · exact (hsb _ ht).1
      · rw [(hsb w (hq.mem w hw')).1]; exact hsame w hw'
    by_cases hee : e' = e
    · rw [st' y (hee ▸ hy) hee, st' z (hee ▸ hz) hee]
    · rw [Function.update_of_ne hee] at hy hz
      rw [(hsb y ((w1 e' he').2.2.mem y hy)).1, (hsb z ((w1 e' he').2.2.mem z hz)).1]
      exact k3 e' he' y hy z hz
  · by_cases hee : e' = e
    · subst hee
      have hs : L.mem s' (stA y) = L.mem s (stA t) := by
        rcases (hmemE y).1 hy with rfl | hy'
        · exact (hsb _ ht).1
        · rw [(hsb y (hq.mem y hy')).1]; exact hsame y hy'
      rw [hs]; exact hcode
    · rw [Function.update_of_ne hee] at hy
      rw [(hsb y ((w1 e' he').2.2.mem y hy)).1]
      simp only [LawfulStore.epState, oth e' he' hee _ (Or.inr rfl)]
      exact k4 e' he' y hy
  · by_cases hee : e' = e
    · subst hee; rw [Function.update_self] at h0
      exact absurd ((hmemE t).2 (Or.inl rfl)) (by rw [h0]; simp)
    · rw [Function.update_of_ne hee] at h0
      simp only [LawfulStore.epState, oth e' he' hee _ (Or.inr rfl)]
      exact k5 e' he' h0

/-- The blocked states and the object codes they go with. -/
def BlockCase (H : Heap) (e v w : U64) : Prop :=
  (v = sched.TS_BLOCKED_ON_SEND ∧ H e = some .ep ∧ w = 1#u64) ∨
  (v = sched.TS_BLOCKED_ON_RECV ∧ H e = some .ep ∧ w = 2#u64) ∨
  (v = sched.TS_BLOCKED_ON_NTFN ∧ H e = some .ntfn ∧ w = 1#u64)

/-- When `e`'s state word is idle or the code of `v` (and `e`'s kind fits
`v`), every member of `e`'s queue is in state `v`. -/
theorem members_same {X : Set U64} {s : S}
    {E : Set U64} {EQ : U64 → List U64} {e v w : U64}
    (hEW : EpsWit st T Cs Ω H X s E EQ) (he : e ∈ E) (hc : BlockCase H e v w)
    (hst : L.epState s e = 0#u64 ∨ L.epState s e = w) : ∀ y ∈ EQ e, L.mem s (stA y) = v := by
  intro y hy
  obtain ⟨w1, -, -, w3, -, k1, k2, -, -, k4, -⟩ := hEW
  obtain ⟨hyX, hbe, hb⟩ := w3 e he y hy
  have hyT := (w1 e he).2.2.mem y hy
  obtain ⟨c1, c2, c3⟩ := k4 e he y hy
  obtain ⟨r1, r2, r3, r4, r6⟩ := ts_vals
  rcases hb with hs | hs | hs
  · have hk := k1 y hyT hyX (Or.inl hs); rw [hbe] at hk
    have := c1 hs
    rcases hc with ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩
    · exact hs
    · rcases hst with e0 | e0 <;> rw [this] at e0 <;> exact absurd e0 (by decide)
    · rw [hh] at hk; cases hk
  · have hk := k1 y hyT hyX (Or.inr hs); rw [hbe] at hk
    have := c2 hs
    rcases hc with ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩
    · rcases hst with e0 | e0 <;> rw [this] at e0 <;> exact absurd e0 (by decide)
    · exact hs
    · rw [hh] at hk; cases hk
  · have hk := k2 y hyT hyX hs; rw [hbe] at hk
    have := c3 hs
    rcases hc with ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩
    · rw [hh] at hk; cases hk
    · rw [hh] at hk; cases hk
    · exact hs

/-! ## The other invariants after a blocking path -/

theorem blocked_ne_reply {v : U64} (h : Blocked v) : v ≠ sched.TS_BLOCKED_ON_REPLY := by
  have e : sched.TS_BLOCKED_ON_REPLY = 5#u64 := by unfold sched.TS_BLOCKED_ON_REPLY; rfl
  obtain ⟨-, -, r3, r4, r6⟩ := ts_vals
  rw [e]; rcases h with h | h | h <;> rw [h] <;> simp [r3, r4, r6]

/-- `BoundInv`, `XInv` and `SCsOK` after a blocking path of `t`: the words
that changed are `t`'s state, block and reply fields, the `Ep` links, the
action (which is kept or becomes choose-new) and the `TCB` word of the reply
object `r0` (unused or naming `t` before, naming `t` after); `t` ends blocked
and, if blocked on receive with a reply object, that object names it. -/
theorem blk_keep {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t r0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) (hk : L.ksb s' = L.ksb s) (hc : L.cpu s' = L.cpu s)
    (fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3336 ∧ K.val ≠ 3344 ∧ K.val ≠ 3352 ∧ K.val ≠ 3360) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K))
    (om : ∀ a ∈ Ω, (r0 ≠ 0#u64 → a ≠ rTcbA r0) → L.mem s' a = L.mem s a)
    (nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o))
    (hact : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64)
    (hbl : L.mem s' (stA t) = sched.TS_BLOCKED_ON_REPLY →
      L.mem s' (replyA t) ∈ Rp ∧ L.mem s' (rTcbA (L.mem s' (replyA t))) = t)
    (hr0 : r0 ≠ 0#u64 → r0 ∈ Rp ∧ (L.mem s (rTcbA r0) = 0#u64 ∨ L.mem s (rTcbA r0) = t))
    (hidl : L.idleW s = t → ¬ Blocked (L.mem s' (stA t))) (htm : TmFr st T Cs Nt s s')
    (hrecv : L.mem s' (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s' (replyA t) ≠ 0#u64 →
      L.mem s' (replyA t) ∈ Rp ∧ L.mem s' (rTcbA (L.mem s' (replyA t))) = t)
    (hold : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr0' : r0 ≠ 0#u64 → L.mem s' (rTcbA r0) = t ∧ L.mem s' (replyA t) = r0 ∧
      (L.mem s' (stA t) = sched.TS_BLOCKED_ON_REPLY ∨ L.mem s' (stA t) = sched.TS_BLOCKED_ON_RECV))
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac) :
    BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' := by
  obtain ⟨hO, hR, hE⟩ := hX
  have hsub := hS.sub
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hsub
  have hT := h.tcbs
  have scf : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have inqf : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)
  have repf : ∀ y ∈ T, y ≠ t → L.mem s' (replyA y) = L.mem s (replyA y) := fun y hy hyt =>
    fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e hyt)
  have stf : ∀ y ∈ T, y ≠ t → L.mem s' (stA y) = L.mem s (stA y) := fun y hy hyt => by
    rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun e => absurd e hyt)
  have ec : L.curW s' = L.curW s := nd _ (by rw [curth0]; omega)
  have ei : L.idleW s' = L.idleW s := nd _ (by rw [idle8]; omega)
  have ecs : L.cscW s' = L.cscW s := nd _ (by simp [layout.node.CUR_SC])
  -- the reply words
  have r0p : r0 ≠ 0#u64 → r0.val % 32 = 0 ∧ r0.val + 32 ≤ 2 ^ 64 := fun h0 => hO.rp r0 (hr0 h0).1
  have rt : ∀ r ∈ Rp, r ≠ r0 ∨ r0 = 0#u64 → L.mem s' (rTcbA r) = L.mem s (rTcbA r) := by
    intro r hr hne
    refine om _ (hrΩ r hr).1 (fun h0 e => ?_)
    rcases hne with hne | hne
    · have := congrArg UScalar.val e
      rw [rTcbA_val (hO.rp r hr), rTcbA_val (r0p h0)] at this
      exact hne (UScalar.eq_of_val_eq this)
    · exact h0 hne
  have rpv : ∀ r ∈ Rp, L.mem s' (rPrevA r) = L.mem s (rPrevA r) := fun r hr =>
    om _ (hrΩ r hr).2.1 (fun h0 e => by
      have := congrArg UScalar.val e
      rw [rPrevA_val (hO.rp r hr), rTcbA_val (r0p h0)] at this
      have := (hO.rp r hr).1; have := (r0p h0).1; omega)
  have rnx : ∀ r ∈ Rp, L.mem s' (rNextA r) = L.mem s (rNextA r) := fun r hr =>
    om _ (hrΩ r hr).2.2 (fun h0 e => by
      have := congrArg UScalar.val e
      rw [rNextA_val (hO.rp r hr), rTcbA_val (r0p h0)] at this
      have := (hO.rp r hr).1; have := (r0p h0).1; omega)
  have scw : ∀ c ∈ Scs, ∀ a, a ∈ Ω → (a.val = c.val + 24 ∨ a.val = c.val + 16 ∨ a.val = c.val + 72 ∨
      a.val = c.val + 80 ∨ a.val = c.val + 88) → L.mem s' a = L.mem s a := by
    intro c hc a ha hv
    refine om a ha (fun h0 e => ?_)
    have := congrArg UScalar.val e
    rw [rTcbA_val (r0p h0)] at this
    have := hO.rpSc r0 (hr0 h0).1 c hc
    have := (sc_facts hO hc).1
    omega
  have fix : ∀ c ∈ Scs, L.mem s' (scTcbA c) = L.mem s (scTcbA c) ∧ L.mem s' (scCoreA c) = L.mem s (scCoreA c) ∧
      L.mem s' (maxA c) = L.mem s (maxA c) ∧ L.mem s' (headA c) = L.mem s (headA c) ∧
      L.mem s' (tailA c) = L.mem s (tailA c) := fun c hc => by
    obtain ⟨-, e1, e2, e3, e4, e5, -, -⟩ := sc_facts hO hc
    obtain ⟨c1, c2, c3, c4, c5⟩ := hcΩ c hc
    exact ⟨scw c hc _ c1 (Or.inl e1), scw c hc _ c2 (Or.inr (Or.inl e2)), scw c hc _ c3 (Or.inr (Or.inr (Or.inl e3))),
      scw c hc _ c4 (Or.inr (Or.inr (Or.inr (Or.inl e4)))), scw c hc _ c5 (Or.inr (Or.inr (Or.inr (Or.inr e5))))⟩
  have srp : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c) := fun c hc =>
    om _ (hS.sub _ (hO.repW c hc)) (fun h0 e => by
      have := congrArg UScalar.val e
      rw [rTcbA_val (r0p h0), (sc_facts hO hc).2.2.2.2.2.2.1] at this
      have := hO.rpSc r0 (hr0 h0).1 c hc
      have := (sc_facts hO hc).1
      omega)
  have rtu : ∀ u ∈ T, u ≠ t → ∀ r ∈ Rp, L.mem s (rTcbA r) = u → L.mem s' (rTcbA r) = u := by
    intro u hu hut r hr e
    refine (rt r hr ?_).trans e
    by_cases h0 : r0 = 0#u64
    · exact Or.inr h0
    left; rintro rfl
    rcases (hr0 h0).2 with e' | e'
    · rw [e] at e'; exact (hT _ hu).ne0 (by rw [e']; rfl)
    · exact hut (e.symm.trans e')
  refine ⟨hB.mk' scf (fun y hy hf => Or.inl (by rw [← inqf y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← inqf y hy]; exact hf))) (fun haT => ?_)
    (by rw [ei]; exact ⟨h.idleT, hB.idle⟩) (fun h0 => ?_) (by
      rw [ei]
      by_cases e : L.idleW s = t
      · rw [e]; exact hidl e
      · rw [stf (L.idleW s) h.idleT e]; exact hB.idleNB) (fun y hy hS h0 => by
        by_cases e : y = t
        · subst e; exact Or.inr (htA h0)
        · refine Or.inl (Sch.of_le (fun hf => by rwa [inqf y hy] at hf) (fun hf => by rwa [inqf y hy] at hf)
            (fun e' => ?_) (fun e' => by rwa [ei] at e') (fun ⟨e1, e2⟩ => ⟨?_, by rwa [ec] at e2⟩)
            (fun hb => by rwa [stf y hy e] at hb) hS)
          · rcases hact with e'' | e''
            · rwa [e''] at e'
            · rw [e''] at e'; exact absurd (e' ▸ hy) (notT_small hT (by simp))
          · rcases hact with e'' | e''
            · rwa [e''] at e1
            · rw [e''] at e1; exact absurd e1 (by decide)),
    ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
        fun c hc => by rw [srp c hc]; exact hR.screp c hc⟩,
      ⟨⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [(fix c hc).2.1]; exact hE.core c hc,
        fun u hu => by
          rw [show L.mem s' (boundA u) = L.mem s (boundA u) from
            fld u hu _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp)]
          exact hE.bnd u hu,
        ScExtra.nsc_keep hE.nsc (fun n hn => om _ (hS.sub _ (hO.ntW n hn)) (fun h0 e => by
            have := congrArg UScalar.val e
            rw [rTcbA_val (r0p h0)] at this
            have := hO.ntRp n hn r0 (hr0 h0).1; omega))
          (fun c hc => om _ (hS.sub _ (hO.snW c hc)) (fun h0 e => by
            have := congrArg UScalar.val e
            obtain ⟨hPc, hzc⟩ := hO.sc c hc
            rw [rTcbA_val (r0p h0), scNtfnA_val hPc hzc] at this
            have := hO.rpSc r0 (hr0 h0).1 c hc
            have := (sc_facts hO hc).1
            omega)) (fun c hc => (fix c hc).2.2.1), hE.tm.tmfr htm, hE.ntb.tmfr htm,
        fun c hc => by
          rw [om _ (hS.sub _ (hO.snW c hc)) (fun h0 e => by
            have := congrArg UScalar.val e
            obtain ⟨hPc, hzc⟩ := hO.sc c hc
            rw [rTcbA_val (r0p h0), scNtfnA_val hPc hzc] at this
            have := hO.rpSc r0 (hr0 h0).1 c hc
            have := (sc_facts hO hc).1
            omega)]
          exact hE.scn c hc,
        hE.yt.keep (fun c hc => (fix c hc).1)
          (fun y hy => fld y hy _ (by simp) (by simp) (by simp) (by simp) (fun _ => by simp))
          (fun c hc => om _ (hS.sub _ (hO.syW c hc)) (fun h0 e => by
            have := congrArg UScalar.val e
            rw [rTcbA_val (r0p h0), show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
              (sc_facts hO hc).2.2.2.2.2.2.2] at this
            have := hO.rpSc r0 (hr0 h0).1 c hc
            have := (sc_facts hO hc).1
            omega))⟩, hE.tsc.keep hE.yt.1 (fun c hc => (fix c hc).1) scf⟩⟩,
    SCsOK.keep hS ⟨hO, hR, hE⟩ hk scf ecs (fun c hc => (fix c hc).2.2) (fun c hc =>
      om _ (spor_omega hO hc) (fun h0 e => by
        have := congrArg UScalar.val e
        obtain ⟨hPc, hzc⟩ := hO.sc c hc
        rw [rTcbA_val (r0p h0), sporA_val hPc hzc] at this
        have := hO.rpSc r0 (hr0 h0).1 c hc; have := (sc_facts hO hc).1; omega)) srp⟩
  · rcases hact with e | e
    · rw [e] at haT ⊢; exact ⟨haT, hB.act haT⟩
    · rw [e] at haT; exact absurd haT (notT_small hT (by simp))
  · rcases hact with e | e
    · rw [e] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩
    · rw [e] at h0; simp at h0
  · by_cases e : u = t
    · subst e; exact hbl hs
    rw [stf u hu e] at hs
    obtain ⟨h1, h2⟩ := hR.reply u hu hs
    rw [repf u hu e]; exact ⟨h1, rtu u hu e _ h1 h2⟩
  · by_cases e : u = t
    · subst e; exact hrecv hs hn
    rw [stf u hu e] at hs; rw [repf u hu e] at hn ⊢
    obtain ⟨h1, h2⟩ := hR.recv u hu hs hn
    exact ⟨h1, rtu u hu e _ h1 h2⟩
  · rw [rnx r hr]; exact hR.next r hr
  · rw [rpv r hr]; exact hR.prev r hr
  · by_cases hr' : r0 ≠ 0#u64 ∧ r = r0
    · obtain ⟨h0, rfl⟩ := hr'
      obtain ⟨e1, e2, e3⟩ := hr0' h0
      rw [e1, e2]; exact ⟨h0, ht, rfl, e3⟩
    have e : L.mem s' (rTcbA r) = L.mem s (rTcbA r) := rt r hr (by
      by_cases h0 : r0 = 0#u64
      · exact Or.inr h0
      · exact Or.inl fun e => hr' ⟨h0, e⟩)
    rw [e] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    have hut : L.mem s (rTcbA r) ≠ t := fun e' => by
      rw [e'] at b3; rcases b3 with b3 | b3
      · exact hold.1 b3
      · exact hold.2 b3
    rw [repf _ b1 hut, stf _ b1 hut]; exact ⟨b0, b1, b2, b3⟩
  · rw [scf u hu] at hb ⊢
    obtain ⟨h1, h2, h3⟩ := hE.bound u hu hb
    rw [(fix _ h1).1, (fix _ h1).2.1]; exact ⟨h1, h2, h3⟩

/-! ## The blocking writes -/

/-- The words a blocking path writes before the append: `t`'s state,
block-object, badge, flags and reply fields, the current node's action and
the `TCB` word of the reply object `r0` (if any). -/
def BlkFoot (st : machine.Store S) [L : LawfulStore st] (s : S) (t r0 : U64) (b : U64) : Prop :=
  (∃ K : U64, (K.val = 3328 ∨ K.val = 3336 ∨ K.val = 3344 ∨ K.val = 3352 ∨ K.val = 3360) ∧
    b = core.num.U64.wrapping_add t K) ∨
  b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION ∨ (r0 ≠ 0#u64 ∧ b = rTcbA r0)

/-- What `BlkFoot` leaves alone. -/
theorem blkfoot_keep {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {E : Set U64} {EQ : U64 → List U64} {t r0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hEW : EpsWit st T Cs Ω H X s E EQ) (ht : t ∈ T)
    (hr0 : r0 ≠ 0#u64 → rTcbA r0 ∈ Ω) (hw : WritesIn st s s' (BlkFoot st s t r0)) :
    (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      (y = t → K.val ≠ 3328 ∧ K.val ≠ 3336 ∧ K.val ≠ 3344 ∧ K.val ≠ 3352 ∧ K.val ≠ 3360) →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
    (∀ a ∈ Ω, (r0 ≠ 0#u64 → a ≠ rTcbA r0) → L.mem s' a = L.mem s a) ∧
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o)) ∧
    (∀ e ∈ E, L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e)) := by
  have hT := h.tcbs
  have hN' := h.nodes _ h.cur
  have hta := hT t ht
  refine ⟨fun y hy K hK hK8 hne => ?_, fun a ha hne => ?_, fun o ho h8 h16 => ?_, fun e he => ?_⟩
  · refine hw.mem_eq (field_aligned (hT y hy) hK hK8) ?_
    rintro (⟨K', hK', e⟩ | e | ⟨h0, e⟩)
    · refine field_ne (hT y hy) hta hK (by omega) (fun e' => ?_) e
      have := hne e'; omega
    · exact node_ne_field hN' (by rw [act_val]; omega) hy (hT y hy) hK e.symm
    · have ho := h.omega _ (hr0 h0)
      exact out_ne_field ho hy (hT y hy) hK (congrArg UScalar.val e)
  · have ho := h.omega a ha
    refine hw.mem_eq ho.1 ?_
    rintro (⟨K', hK', e⟩ | e | ⟨h0, e⟩)
    · exact out_ne_field ho ht hta (by omega) (congrArg UScalar.val e).symm
    · exact out_ne_node ho h.cur hN' (by rw [act_val]; omega) (congrArg UScalar.val e).symm
    · exact hne h0 e
  · rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned hN' ho h8) ?_
    rintro (⟨K', hK', e⟩ | e | ⟨h0, e⟩)
    · exact node_ne_field hN' ho ht hta (by omega) e
    · have := congrArg UScalar.val e
      rw [nodeAt_val hN' ho, nodeAt_val hN' (by rw [act_val]; omega), act_val] at this
      exact h16 (by simpa using this)
    · have ho' := h.omega _ (hr0 h0)
      exact out_ne_node ho' h.cur hN' ho (congrArg UScalar.val e)
  · obtain ⟨hE, hEN, -⟩ := hEW.1 e he
    obtain ⟨o1, o2⟩ := ep_out hE hEN
    have k : ∀ a, OutsideObjs st T Cs s a → (a.val = e.val ∨ a.val = e.val + 8) → L.mem s' a = L.mem s a := by
      intro a ha hv
      refine hw.mem_eq ha.1 ?_
      rintro (⟨K', hK', e'⟩ | e' | ⟨h0, e'⟩)
      · exact out_ne_field ha ht hta (by omega) (congrArg UScalar.val e').symm
      · exact out_ne_node ha h.cur hN' (by rw [act_val]; omega) (congrArg UScalar.val e').symm
      · have := hEW.2.2.1 e he _ (hr0 h0)
        have := congrArg UScalar.val e'
        omega
    exact ⟨k _ o1 (Or.inl epHeadA_val), k _ o2 (Or.inr (epTSA_val hE))⟩

theorem BlockCase.facts {H : Heap} {e v w : U64} (hc : BlockCase H e v w) :
    ((v = sched.TS_BLOCKED_ON_SEND ∨ v = sched.TS_BLOCKED_ON_RECV) → H e = some .ep) ∧
    (v = sched.TS_BLOCKED_ON_NTFN → H e = some .ntfn) ∧
    (v = sched.TS_BLOCKED_ON_SEND → w = 1#u64) ∧ (v = sched.TS_BLOCKED_ON_RECV → w = 2#u64) ∧
    (v = sched.TS_BLOCKED_ON_NTFN → w = 1#u64) ∧ Blocked v ∧ (H e = some .ep ∨ H e = some .ntfn) := by
  obtain ⟨-, -, r3, r4, r6⟩ := ts_vals
  rcases hc with ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩ | ⟨rfl, hh, rfl⟩ <;> rw [r3, r4, r6] <;>
    refine ⟨fun _ => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, ?_, ?_⟩ <;>
    (try simp only [Blocked, r3, r4, r6]) <;> first
    | exact hh
    | (exfalso; revert h; decide)
    | (left; exact hh)
    | (right; exact hh)
    | decide
    | (rename_i h'; exfalso; revert h'; decide)

/-- A `BlkFoot` write leaves the timer-tree words alone. -/
theorem TmFr.of_blkfoot {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t r0 : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (ht : t ∈ T) (hr0 : r0 ≠ 0#u64 → r0 ∈ Rp) (hw : WritesIn st s s' (BlkFoot st s t r0)) :
    TmFr st T Cs Nt s s' := by
  have hΩ : ∀ n ∈ Nt, OutsideObjs st T Cs s (ntfnBtA n) := fun n hn => h.omega _ (hsub _ (hO.ntB n hn).2)
  refine TmFr.of_writes h.tcbs h.nodes hO hw ?_
  rintro b (⟨K, hK, rfl⟩ | rfl | ⟨h0, rfl⟩)
  · exact notTmW_field h.tcbs h.nodes hΩ ht (by omega) (by omega)
  · exact notTmW_node h.tcbs h.nodes hΩ h.cur (by rw [act_val]; omega) (by rw [act_val]; omega)
  · have hp := hr0 h0
    refine notTmW_omega h.tcbs h.nodes (h.omega _ (hsub _ (hO.tcbW hp))) (fun n hn e => ?_)
    rw [rTcbA_val (hO.rp _ hp), ntfnBtA_val (hO.ntP n hn)] at e
    have := hO.ntORp n hn _ hp; omega

/-- The append that ends a blocking path, and the invariants after it: the
thread was blocked and its block object set on a state `s5` reached from
`s` by `BlkFoot` writes, with `t` in the exception set. -/
theorem blk_tail {f : Result S} {s s5 : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t e v w r0 : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s)
    (ht : t ∈ T) (hc : BlockCase H e v w) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = w)
    (h5 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s5 Q R)
    (hw5 : WritesIn st s s5 (BlkFoot st s t r0))
    (hact : L.actionW s5 = L.actionW s ∨ L.actionW s5 = 1#u64)
    (hv : L.mem s5 (stA t) = v) (hb : L.mem s5 (blockA t) = e)
    (hr0 : r0 ≠ 0#u64 → r0 ∈ Rp ∧ (L.mem s (rTcbA r0) = 0#u64 ∨ L.mem s (rTcbA r0) = t))
    (hidl : L.idleW s ≠ t)
    (hrecv : L.mem s5 (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s5 (replyA t) ≠ 0#u64 →
      L.mem s5 (replyA t) ∈ Rp ∧ L.mem s5 (rTcbA (L.mem s5 (replyA t))) = t)
    (hold : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV)
    (hr05 : r0 ≠ 0#u64 → L.mem s5 (rTcbA r0) = t ∧ L.mem s5 (replyA t) = r0 ∧
      L.mem s5 (stA t) = sched.TS_BLOCKED_ON_RECV)
    (htA : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac)
    (happ : ∀ xs, EpPlaced T e → QueueRel (L.mem s5) T .Ep (L.epQ s5 e) xs → t ∉ xs →
      f ⦃ s6 => QueueRel (L.mem s6) T .Ep (L.epQ s6 e)
          (insPrio (fun y => L.mem s5 (prioA y)) (L.mem s5 (prioA t)) t xs) ∧
        L.epState s6 e = w ∧ WritesIn st s5 s6 (EpFoot (t :: xs) e) ⦄) :
    f ⦃ s6 => SchedQueuesInv st T Cs Ω H s6 Q R ∧ BoundInv st T Ac s6 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s6 ∧
      SCsOK st T Ω Sg Scs Z Ac s6 ∧ SgOK st Ω Sg s6 ∧ L.actionW s6 = L.actionW s5 ∧ L.curW s6 = L.curW s5 ∧
      L.mem s6 (stA t) = v ∧ L.idleW s6 = L.idleW s ⦄ := by
  obtain ⟨fE, fN, f1, f2, f3, fB, fH⟩ := hc.facts
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have he : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 fH
  obtain ⟨E5, EQ5, hEW5⟩ := h5.eps
  have he5 : e ∈ E5 := (hEW5.2.2.2.2.2.2.2.1 e).2 fH
  have hO := hX.1
  have hsub := hSg.sub
  have hr0Ω : r0 ≠ 0#u64 → rTcbA r0 ∈ Ω := fun h0 => hsub _ (hO.tcbW (hr0 h0).1)
  obtain ⟨k1, k2, k3, k4⟩ := blkfoot_keep h hEW ht hr0Ω hw5
  have hst5 : L.epState s5 e = L.epState s e := by unfold LawfulStore.epState; rw [(k4 e he).2]
  have hq5 := (hEW5.1 e he5).2.2
  have htn : t ∉ EQ5 e := fun hm => (hEW5.2.2.2.1 e he5 t hm).1 (Or.inr rfl)
  have hsame := members_same hEW5 he5 hc (by rw [hst5]; exact hst0)
  have hWT : ∀ y ∈ t :: EQ5 e, y ∈ T := by
    intro y hy; rcases List.mem_cons.1 hy with rfl | hy
    · exact ht
    · exact hq5.mem y hy
  refine WP.spec_mono (happ _ (hEW5.1 e he5).1 hq5 htn) fun s6 hh => ?_
  obtain ⟨hq6, hcode, hw6⟩ := hh
  have hinv := inv_ep_ins h5 hEW5 he5 ht (Or.inr rfl) hb (hv ▸ fB) (by rw [hv]; exact fE) (by rw [hv]; exact fN)
    (fun y hy => (hsame y hy).trans hv.symm)
    (by rw [hv, hcode]; exact ⟨f1, f2, f3⟩) hw6 hq6 (fun y => mem_insPrio)
  have eX : {y | y ∈ {y | y ∈ (∅ : Set U64) ∨ y = t} ∧ y ≠ t} = (∅ : Set U64) := by
    ext y; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, false_or, iff_false, not_and]; exact fun a b => b a
  rw [eX] at hinv
  obtain ⟨j1, j2, j3⟩ := epfoot_keep h5 hEW5 he5 hWT hw6
  have hk6 : L.ksb s6 = L.ksb s := hw6.1.trans hw5.1
  have hc6 : L.cpu s6 = L.cpu s := hw6.2.1.trans hw5.2.1
  have st6 : L.mem s6 (stA t) = L.mem s5 (stA t) := by
    rw [stA_eq]; exact j1 t ht _ (by simp) (by simp) (by simp) (by simp)
  have rp6 : L.mem s6 (replyA t) = L.mem s5 (replyA t) := j1 t ht _ (by simp) (by simp) (by simp) (by simp)
  have ea6 : L.actionW s6 = L.actionW s5 := by
    unfold LawfulStore.actionW; exact j3 _ (by rw [act_val]; omega) (by rw [act_val])
  have nd6 : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 24) →
      L.mem s6 (L.nodeAt s6 (L.cpu s6) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho =>
    (j3 o (by omega) (by omega)).trans (k3 o (by omega) (by omega) (by omega))
  have rc6 : L.mem s6 (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s6 (replyA t) ≠ 0#u64 →
      L.mem s6 (replyA t) ∈ Rp ∧ L.mem s6 (rTcbA (L.mem s6 (replyA t))) = t := by
    rw [st6, rp6]; intro h1 h2
    obtain ⟨r1, r2⟩ := hrecv h1 h2
    exact ⟨r1, (j2 _ (hsub _ (hO.tcbW r1))).trans r2⟩
  obtain ⟨b1, b2, b3⟩ := blk_keep (hidl := fun e => absurd e hidl)
    (htm := (TmFr.of_blkfoot h hO hsub ht (fun h0 => (hr0 h0).1) hw5).trans
      (TmFr.of_epfoot h5 hEW5 he5 hWT hw6 hO.ksb hsub)) h hB hX hS ht hk6 hc6
    (fun y hy K hK hK8 h1 h2 hy' => (j1 y hy K hK hK8 h1 h2).trans (k1 y hy K hK hK8 hy'))
    (fun a ha hne => (j2 a ha).trans (k2 a ha hne)) nd6 (by rw [ea6]; exact hact)
    (fun e => absurd (show v = sched.TS_BLOCKED_ON_REPLY by rw [← hv, ← st6]; exact e) (blocked_ne_reply fB))
    hr0 rc6 hold (fun h0 => by
      obtain ⟨e1, e2, e3⟩ := hr05 h0
      exact ⟨(j2 _ (hsub _ (hO.tcbW (hr0 h0).1))).trans e1, rp6.trans e2, Or.inr (st6.trans e3)⟩) htA
  exact ⟨hinv, b1, b2, b3, ⟨hSg.sub, fun b hb => by rw [hk6]; exact hSg.ks b hb,
    fun o h1 h2 => by rw [hk6]; exact hSg.ksΩ o h1 h2⟩, ea6,
    j3 _ (by rw [curth0]; omega) (by rw [curth0]), st6.trans hv, nd6 _ (by rw [idle8]; omega)⟩

/-! ## The steps before the append -/

theorem blocked_not_runnable {v : U64} (h : Blocked v) : ¬ Runnable v := by
  obtain ⟨r1, r2, r3, r4, r6⟩ := ts_vals
  rintro (e | e) <;> rcases h with h | h | h <;> rw [h] at e <;> simp [r1, r2, r3, r4, r6] at e

theorem tcb_eq.blk (a b : obj.Tcb) : obj.Tcb.Insts.CoreCmpPartialEqTcb.eq a b ⦃ r => r = decide (a = b) ⦄ := by
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq; simp

/-- seL4 `scheduleTCB` on a thread that is not runnable: the action stays or
becomes choose-new. -/
theorem sched.schedule_tcb.blk {X : Set U64} (s : S) (t : obj.Tcb) {Q : U64 → U64 → List U64}
    {R : U64 → List U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hnr : ¬ Runnable (L.mem s (stA t))) :
    sched.schedule_tcb st s t ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧
      (s' = s ∨ s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) ∧
      (L.curW s' = t → L.actionW s' ≠ 0#u64) ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, e1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  have hset : (sched.set_action st s sched.ACTION_CHOOSE_NEW) ⦃ s' => SchedQueuesInvX st T Cs Ω H X s' Q R ∧
      (s' = s ∨ s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) ∧
      (L.curW s' = t → L.actionW s' ≠ 0#u64) ⦄ := by
    refine WP.spec_mono (sched.set_action.spec s _) fun s' e => ?_
    subst e
    rw [choose_val]
    obtain ⟨h1, e1⟩ := inv_set_action h (Or.inr (Or.inl rfl)) (fun h1T => absurd h1T (notT_small h.tcbs (by simp)))
    exact ⟨h1, Or.inr rfl, fun _ => by rw [e1]; simp⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec' as ⟨b1, hb1⟩
      split
      · exact absurd (hb1 ‹_›).1 hnr
      · exact hset
    · refine (WP.spec_ok _).2 ⟨h, Or.inl rfl, fun _ => ?_⟩
      rw [← ei]; rw [resume_val] at *; assumption
  · refine (WP.spec_ok _).2 ⟨h, Or.inl rfl, fun hc => ?_⟩
    rename_i hb
    exact absurd (by rw [eb, decide_eq_true_eq, e1]; exact hc.symm) hb

theorem fld_wr_ne {s : S} {t K K' v : U64} (ht : TcbAddr t) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hK' : K'.val < 4096) (hK8' : K'.val % 8 = 0) (hne : K.val ≠ K'.val) :
    L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add t K') =
      L.mem s (core.num.U64.wrapping_add t K') :=
  L.mem_wr_ne (field_aligned ht hK hK8) (field_aligned ht hK' hK8')
    (fun e => field_ne ht ht hK hK' (fun _ => hne) (UScalar.eq_of_val_eq e))

theorem fld_wr_ne' {s : S} {t K K' v a b : U64} (ht : TcbAddr t) (ha : a = core.num.U64.wrapping_add t K)
    (hb : b = core.num.U64.wrapping_add t K') (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (hK' : K'.val < 4096) (hK8' : K'.val % 8 = 0) (hne : K.val ≠ K'.val) :
    L.mem (L.wr s a v) b = L.mem s b := by
  subst ha hb; exact fld_wr_ne ht hK hK8 hK' hK8' hne


/-- A field write of `t` as a `BlkFoot` step. -/
theorem blk_wr_field {s s1 : S} {t r0 K v : U64} (ht : TcbAddr t) (hw : WritesIn st s s1 (BlkFoot st s t r0))
    (hK : K.val = 3328 ∨ K.val = 3336 ∨ K.val = 3344 ∨ K.val = 3352 ∨ K.val = 3360) :
    WritesIn st s (L.wr s1 (core.num.U64.wrapping_add t K) v) (BlkFoot st s t r0) :=
  (hw.trans (writesIn_wr (field_aligned ht (by omega) (by omega)))).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact Or.inl ⟨K, hK, hb⟩

/-- The action write of `schedule_tcb` as a `BlkFoot` step. -/
theorem blk_wr_act {s s1 : S} {t r0 v : U64} (hN : NodePlaced st T s (L.cpu s))
    (hw : WritesIn st s s1 (BlkFoot st s t r0)) :
    WritesIn st s (L.wr s1 (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION) v) (BlkFoot st s t r0) := by
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  exact (hw.trans (writesIn_wr (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])))).mono
    fun b hb => by
      rcases hb with hb | hb
      · exact hb
      · exact Or.inr (Or.inl hb)

/-- After `schedule_tcb.blk`: the footprint, the action, and `t`'s fields. -/
theorem blk_sched {X : Set U64} {s s4 s5 : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t r0 : U64}
    (h4 : SchedQueuesInvX st T Cs Ω H X s4 Q R) (ht : t ∈ T) (w4 : WritesIn st s s4 (BlkFoot st s t r0))
    (a4 : L.actionW s4 = L.actionW s)
    (e5 : s5 = s4 ∨ s5 = L.wr s4 (L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION) 1#u64) :
    WritesIn st s s5 (BlkFoot st s t r0) ∧ (L.actionW s5 = L.actionW s ∨ L.actionW s5 = 1#u64) ∧
      L.mem s5 (stA t) = L.mem s4 (stA t) ∧ L.mem s5 (blockA t) = L.mem s4 (blockA t) ∧
      L.mem s5 (replyA t) = L.mem s4 (replyA t) ∧ (∀ a ∈ Ω, L.mem s5 a = L.mem s4 a) := by
  have hN4 := h4.nodes _ h4.cur
  have hta := h4.tcbs t ht
  rcases e5 with rfl | rfl
  · exact ⟨w4, Or.inl a4, rfl, rfl, rfl, fun _ _ => rfl⟩
  have hN : NodePlaced st T s (L.cpu s) := by rw [← w4.2.1]; exact hN4.ksb w4.1.symm
  have na : Aligned (L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION) :=
    nodeAt_aligned hN4 (by rw [act_val]; omega) (by rw [act_val])
  have fk : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s4 (L.nodeAt s4 (L.cpu s4) layout.node.SCHED_ACTION) 1#u64) (core.num.U64.wrapping_add t K) =
        L.mem s4 (core.num.U64.wrapping_add t K) := fun K hK hK8 =>
    L.mem_wr_ne na (field_aligned hta hK hK8)
      (fun e => node_ne_field hN4 (by rw [act_val]; omega) ht hta hK (UScalar.eq_of_val_eq e))
  refine ⟨blk_wr_act hN w4, Or.inr ?_, by rw [stA_eq]; exact fk _ (by simp) (by simp),
    fk _ (by simp) (by simp), fk _ (by simp) (by simp), fun a ha => ?_⟩
  · unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_same na
  · have ho := h4.omega a ha
    exact L.mem_wr_ne na ho.1 (out_ne_node ho h4.cur hN4 (by rw [act_val]; omega))

theorem ep_send_val : obj.EP_SEND &&& 3#u64 = 1#u64 := by unfold obj.EP_SEND; decide
theorem ep_recv_val : obj.EP_RECV &&& 3#u64 = 2#u64 := by unfold obj.EP_RECV; decide
theorem ntfn_wait_val : obj.NTFN_WAITING &&& 3#u64 = 1#u64 := by unfold obj.NTFN_WAITING; decide

/-! ## `send_ipc` blocking -/

/-- What a thread that blocks must satisfy: a TCB, not blocked, in no ready
or release queue, not the switch-to candidate. -/
structure CanBlock (st : machine.Store S) [L : LawfulStore st] (T Ac : Set U64) (s : S) (t : U64) : Prop where
  mem : t ∈ T
  nb : ¬ Blocked (L.mem s (stA t))
  nrp : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY
  nq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64
  nr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64
  na : L.actionW s ≠ t
  /-- The idle thread does not block. -/
  ni : L.idleW s ≠ t
  /-- Its SC, if any, is active (it runs on it). -/
  ac : L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ Ac

theorem CanBlock.old {s : S} {t : U64} (hc : CanBlock st T Ac s t) :
    L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV :=
  ⟨hc.nrp, fun e => hc.nb (Or.inr (Or.inl e))⟩

/-- The state, block-object and further field writes of a blocking path (up to `schedule_tcb`),
as seen by the queue invariant. -/
theorem blk_set_state {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t v : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hc : CanBlock st T Ac s t) :
    SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} (L.wr s (stA t) v) Q R :=
  inv_set_state_blk h hc.mem (Or.inr hc.nb)
    ⟨fun c hc' p hp hm => absurd hm (h.notQ hc.mem hc.nq hc' hp), fun c hc' hm => absurd hm (h.notR hc.mem hc.nr hc'),
     fun e => absurd e hc.na⟩

/-- The blocking branch of `send_ipc` (seL4 `sendIPC`, blocking on an idle or
sending endpoint) keeps the invariants. -/
theorem send_block {A : Type _} (s : S) (a : A) (t e badge : U64) (can_grant can_grant_reply do_call : Bool)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hH : H e = some .ep) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 1#u64) :
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
      ok (s6, a)) ⦃ s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧ BoundInv st T Ac s' ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
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
      ok (s6, a)) ⦃ s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧ BoundInv st T Ac s' ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
    intro f
    step with obj.Tcb.set_block_flags.wr as ⟨s4, e4⟩
    have h4 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s4 Q R := by
      rw [e4]; exact inv_wr_fieldX (K := 3352#u64) h3 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    have w4 : WritesIn st s s4 (BlkFoot st s t 0#u64) := by rw [e4]; exact blk_wr_field hta w3 (by simp)
    -- the state and block object of `t` in `s4`
    have v4 : L.mem s4 (stA t) = sched.TS_BLOCKED_ON_SEND := by
      rw [e4, fld_wr_ne' hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e3, fld_wr_ne' hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have b4 : L.mem s4 (blockA t) = e := by
      rw [e4, fld_wr_ne' hta rfl (blockA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e3, fld_wr_ne' hta rfl (blockA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e2]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have a4 : L.actionW s4 = L.actionW s := by
      rw [e4, act_wr_field (h3.nodes _ h3.cur) ht hta rfl (by simp) (by simp),
        e3, act_wr_field (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
        e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
        e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
    refine WP.spec_bind (sched.schedule_tcb.blk s4 t h4 (by rw [v4]; exact blocked_not_runnable (Or.inl rfl))) ?_
    rintro s5 ⟨h5, e5, -⟩
    obtain ⟨w5, a5, v5, b5, -, -⟩ := blk_sched h4 ht w4 a4 e5
    rw [v4] at v5; rw [b4] at b5
    obtain ⟨-, -, r3, r4, -⟩ := ts_vals
    refine WP.spec_bind (blk_tail (f := endpoint.ep_append st s5 e t obj.EP_SEND) (r0 := 0#u64) (hidl := hc.ni)
      h hB hX hS hSg ht
      (Or.inl ⟨rfl, hH, rfl⟩) hst0 h5 w5 a5 v5 b5 (fun h0 => absurd rfl h0)
      (fun h1 => absurd (v5.symm.trans h1) (by rw [r3, r4]; decide)) hc.old (fun h0 => absurd rfl h0) hc.ac
      (fun xs hE hq hn => WP.spec_mono (WP.spec_and
        (endpoint.ep_append.rel s5 e t obj.EP_SEND xs h5.tcbs hE hq ht hn)
        (endpoint.ep_append.foot s5 e t obj.EP_SEND xs h5.tcbs hE hq ht hn))
        fun s6 hh => ⟨hh.1.1, by rw [hh.1.2, ep_send_val], hh.2⟩)) ?_
    rintro s6 hh
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩
  cases can_grant <;> cases can_grant_reply <;> cases do_call <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Aeneas.Std.bind_ok, lift] <;> exact key _

theorem ep_idle_val : obj.EP_IDLE = 0#u64 := by unfold obj.EP_IDLE; rfl
theorem ep_send_val' : obj.EP_SEND = 1#u64 := by unfold obj.EP_SEND; rfl

/-- seL4 `sendIPC` on an idle or sending endpoint (where the sender blocks,
or returns if non-blocking) keeps the invariants. -/
theorem endpoint.send_ipc.block {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : blocking = true → CanBlock st T Ac s t)
    (hH : H e = some .ep) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 1#u64) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧ BoundInv st T Ac s' ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  split
  · split
    · exact send_block s a t e badge can_grant can_grant_reply do_call Q R h hB hX hS hSg (hc ‹_›) hH hst0
    · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨h, hB, hX, hS, hSg⟩
  · split
    · split
      · exact send_block s a t e badge can_grant can_grant_reply do_call Q R h hB hX hS hSg (hc ‹_›) hH hst0
      · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨h, hB, hX, hS, hSg⟩
    · exfalso
      rename_i h1 h2
      rw [ep_idle_val] at h1; rw [ep_send_val'] at h2
      rcases hst0 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction

/-! ## `wait_for_sender` (the blocking end of `receive_ipc`) -/

theorem obj.Tcb.set_reg.badge (s : S) (t : obj.Tcb) (v : U64) (ht : TcbAddr t) :
    obj.Tcb.set_reg st t s layout.reg.BADGE v ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add t 256#u64) v ⦄ := by
  unfold obj.Tcb.set_reg
  step*
  subst_vars
  congr 1
  have := ht.fits
  apply UScalar.eq_of_val_eq
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
    layout.tcb.REGS, layout.reg.BADGE, layout.reg.RDI]
  try omega

/-- The reply object's `TCB` write as a `BlkFoot` step. -/
theorem blk_wr_reply {s s1 : S} {t r0 v : U64} (ha : Aligned (rTcbA r0)) (h0 : r0 ≠ 0#u64)
    (hw : WritesIn st s s1 (BlkFoot st s t r0)) : WritesIn st s (L.wr s1 (rTcbA r0) v) (BlkFoot st s t r0) :=
  (hw.trans (writesIn_wr ha)).mono fun b hb => by
    rcases hb with hb | hb
    · exact hb
    · exact Or.inr (Or.inr ⟨h0, hb⟩)

/-- A write to a word of `Ω`: the queue invariant, the action and the TCB
fields are kept. -/
theorem omega_wr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ha : a ∈ Ω) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s a v) Q R ∧ L.actionW (L.wr s a v) = L.actionW s ∧
      ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s a v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  refine ⟨inv_of_free h ((writesIn_wr ho.1).mono fun b hb => Or.inl (hb ▸ ha)), ?_, fun y hy K hK hK8 => ?_⟩
  · unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_ne ho.1 (nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val]))
      (fun e => out_ne_node ho h.cur hN (by rw [act_val]; omega) e.symm)
  · exact L.mem_wr_ne ho.1 (field_aligned (h.tcbs y hy) hK hK8) (fun e => out_ne_field ho hy (h.tcbs y hy) hK e.symm)

/-- `wait_for_sender` (seL4 `receiveIPC`'s blocking branch, on an idle or
receiving endpoint, with the reply object bookkeeping; or the non-blocking
return) keeps the invariants. The reply object, if any, names no other
thread. -/
theorem endpoint.wait_for_sender.inv (s : S) (t e : U64) (blocking : Bool) (reply : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hc : blocking = true → CanBlock st T Ac s t)
    (hH : H e = some .ep) (hst0 : L.epState s e = 0#u64 ∨ L.epState s e = 2#u64)
    (hr : reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s (rTcbA reply) = 0#u64 ∨ L.mem s (rTcbA reply) = t)) :
    endpoint.wait_for_sender st s t e blocking reply ⦃ s' => SchedQueuesInv st T Cs Ω H s' Q R ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  unfold endpoint.wait_for_sender
  split
  · have hc := hc ‹_›
    step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
    step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
    step with obj.Tcb.set_reply_obj.wr as ⟨s3, e3⟩
    have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
      rw [e1]; exact blk_set_state h hc
    have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
      rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    have h3 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s3 Q R := by
      rw [e3]; exact inv_wr_fieldX (K := 3360#u64) h2 ht (Or.inr rfl) (by simp) (by simp) (by simp)
    rw [stA_eq] at e1
    have w3 : WritesIn st s s3 (BlkFoot st s t reply) := by
      rw [e3, e2, e1]
      exact blk_wr_field (K := 3360#u64) hta (blk_wr_field hta (blk_wr_field hta (WritesIn.refl _ _) (by simp))
        (by simp)) (by simp)
    have v3 : L.mem s3 (stA t) = sched.TS_BLOCKED_ON_RECV := by
      rw [e3, fld_wr_ne' (K := 3360#u64) (a := replyA t) hta rfl (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp),
        e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have b3 : L.mem s3 (blockA t) = e := by
      rw [e3, fld_wr_ne' (K := 3360#u64) (a := replyA t) hta rfl (blockA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e2]
      exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have rp3 : L.mem s3 (replyA t) = reply := by
      rw [e3]; exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
    have a3 : L.actionW s3 = L.actionW s := by
      rw [e3, act_wr_field (K := 3360#u64) (a := replyA t) (h2.nodes _ h2.cur) ht hta rfl (by simp) (by simp),
        e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
        e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
    refine WP.spec_bind (sched.schedule_tcb.blk s3 t h3 (by rw [v3]; exact blocked_not_runnable (Or.inr (Or.inl rfl)))) ?_
    rintro s4 ⟨h4, e4, -⟩
    obtain ⟨w4, a4, v4, b4, rp4, -⟩ := blk_sched h3 ht w3 a3 e4
    rw [v3] at v4; rw [b3] at b4; rw [rp3] at rp4
    obtain ⟨-, -, r3, -, -⟩ := ts_vals
    have tail : ∀ s5 : S, SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s5 Q R →
        WritesIn st s s5 (BlkFoot st s t reply) → (L.actionW s5 = L.actionW s ∨ L.actionW s5 = 1#u64) →
        L.mem s5 (stA t) = sched.TS_BLOCKED_ON_RECV → L.mem s5 (blockA t) = e →
        L.mem s5 (replyA t) = reply → (reply ≠ 0#u64 → L.mem s5 (rTcbA reply) = t) →
        endpoint.ep_append st s5 e t obj.EP_RECV ⦃ s' => SchedQueuesInv st T Cs Ω H s' Q R ∧
          BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
      intro s5 h5 w5 a5 v5 b5 rp5 rt5
      refine WP.spec_mono ?_ fun s6 (hh : _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ L.actionW s6 = L.actionW s5 ∧
        L.curW s6 = L.curW s5 ∧ L.mem s6 (stA t) = sched.TS_BLOCKED_ON_RECV ∧ L.idleW s6 = L.idleW s) =>
          ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩
      exact blk_tail (r0 := reply) (hidl := hc.ni) h hB hX hS hSg ht (Or.inr (Or.inl ⟨rfl, hH, rfl⟩)) hst0 h5 w5 a5 v5 b5 hr
        (fun _ hn => by rw [rp5] at hn ⊢; exact ⟨(hr hn).1, rt5 hn⟩) hc.old (fun h0 => ⟨rt5 h0, rp5, v5⟩) hc.ac
        (fun xs hE hq hn => WP.spec_mono (WP.spec_and
          (endpoint.ep_append.rel s5 e t obj.EP_RECV xs h5.tcbs hE hq ht hn)
          (endpoint.ep_append.foot s5 e t obj.EP_RECV xs h5.tcbs hE hq ht hn))
          fun s6 hh => ⟨hh.1.1, by rw [hh.1.2, ep_recv_val], hh.2⟩)
    split
    · rename_i hne
      have h0 : reply ≠ 0#u64 := by simpa using hne
      obtain ⟨hrp, -⟩ := hr h0
      have hm : rTcbA reply ∈ Ω := hSg.sub _ (hX.1.tcbW hrp)
      step with obj.Reply.set_tcb.spec as ⟨s6, e6⟩
      try simp only [Aeneas.Std.bind_ok]
      obtain ⟨h6, a6, f6⟩ := omega_wr (v := t) h4 hm
      rw [← e6] at h6 a6 f6
      apply tail s6 h6 (by rw [e6]; exact blk_wr_reply (h4.omega _ hm).1 h0 w4) (by rw [a6]; exact a4)
      · rw [stA_eq, f6 t ht _ (by simp) (by simp), ← stA_eq]; exact v4
      · rw [blockA_eq, f6 t ht _ (by simp) (by simp), ← blockA_eq]; exact b4
      · exact (f6 t ht _ (by simp) (by simp)).trans rp4
      · intro _; rw [e6]; exact L.mem_wr_same (h4.omega _ hm).1
    · rename_i hne
      have h0 : reply = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne; exact hne
      try simp only [Aeneas.Std.bind_ok]
      exact tail s4 h4 w4 a4 v4 b4 rp4 (fun hn => absurd h0 hn)
  · refine WP.spec_mono (obj.Tcb.set_reg.badge s t 0#u64 hta) fun s' e' => ?_
    subst e'
    obtain ⟨b1, b2⟩ := bx_field (K := 256#u64) (v := 0#u64) h hB hX hSg.sub ht (by simp) (by simp) (by simp) (by simp)
    exact ⟨inv_wr_field h ht (by simp) (by simp) (by simp), b1, b2,
      SCsOK.field h hS hX ht (by simp) (by simp) (by simp),
      ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩

/-! ## `maybe_return_sched_context` -/

theorem obj.Tcb.set_sc.wr (s : S) (t : obj.Tcb) (v : U64) :
    obj.Tcb.set_sc st t s v ⦃ s' => s' = L.wr s (scA t) v ⦄ := by
  unfold obj.Tcb.set_sc; step*; simp_all [scA]
theorem obj.Sc.set_tcb.wr (s : S) (c : obj.Sc) (v : U64) :
    obj.Sc.set_tcb st c s v ⦃ s' => s' = L.wr s (scTcbA c) v ⦄ := by
  unfold obj.Sc.set_tcb; step*; simp_all [scTcbA]
theorem obj.Ntfn.sc.any (s : S) (n : obj.Ntfn) : obj.Ntfn.sc st n s ⦃ _ => True ⦄ := by
  unfold obj.Ntfn.sc; step*

/-- `SCsOK` when the SC fields are kept or cleared. -/
theorem SCsOK.keep' {s s' : S} (hS : SCsOK st T Ω Sg Scs Z Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hk : L.ksb s' = L.ksb s) (hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∨ L.mem s' (scA y) = 0#u64)
    (hcs : L.cscW s' = L.cscW s)
    (hfix : ∀ c ∈ Scs, L.mem s' (maxA c) = L.mem s (maxA c) ∧ L.mem s' (headA c) = L.mem s (headA c) ∧
      L.mem s' (tailA c) = L.mem s (tailA c))
    (hsp : ∀ c ∈ Scs, L.mem s' (sporA c) = L.mem s (sporA c))
    (hrp : ∀ c ∈ Scs, L.mem s' (scReplyA c) = L.mem s (scReplyA c)) : SCsOK st T Ω Sg Scs Z Ac s' := by
  have wf : ∀ c ∈ Scs, RefillsWF st s c (Z c) → RefillsWF st s' c (Z c) := fun c hc hW => by
    obtain ⟨f3, f4, f5⟩ := hfix c hc
    exact hW.of_hdr f3 (by rw [show L.rhead s' c = L.mem s' (headA c) from rfl, f4]; exact hW.head_lt)
      (by rw [show L.rtail s' c = L.mem s' (tailA c) from rfl, f5]; exact hW.tail_lt)
  refine ⟨hS.sub, fun b hb => by rw [hk]; exact hS.ks b hb, fun o h1 h2 => by rw [hk]; exact hS.ksΩ o h1 h2,
    fun y hy hb hne => ?_, fun c hc => (hS.all c hc).of_wf (hfix c hc).1 (wf c hc),
    fun c hc => by rw [show L.rmax s' c = L.rmax s c from (hfix c hc).1]; exact hS.act c hc,
    fun c hc h0 => hS.spor c hc (by rw [← hsp c hc]; exact h0), hS.spSg,
    fun c hc h0 => hS.rep c hc (by rwa [hrp c hc] at h0), hS.repSg⟩
  · rcases hsc y hy with e | e
    · rw [e] at hb hne ⊢; rw [hcs] at hne ⊢; exact hS.disj y hy hb hne
    · exact absurd e hb

/-- `BoundInv` after a write to a word of `Ω`. -/
theorem BoundInv.owr {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {a v : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (ha : a ∈ Ω) :
    BoundInv st T Ac (L.wr s a v) := by
  have ho := h.omega a ha
  have hN := h.nodes _ h.cur
  obtain ⟨-, ea, f⟩ := omega_wr (v := v) h ha
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s a v) (L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o h1 h2 => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ho.1 (nodeAt_aligned hN h1 h2) (fun e => out_ne_node ho h.cur hN h1 e.symm)
  have hsc : ∀ y ∈ T, L.mem (L.wr s a v) (scA y) = L.mem s (scA y) := fun y hy => f y hy _ (by simp) (by simp)
  have hiq : ∀ y ∈ T, L.mem (L.wr s a v) (inqA y) = L.mem s (inqA y) := fun y hy => f y hy _ (by simp) (by simp)
  have ec : L.curW (L.wr s a v) = L.curW s := nd _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW (L.wr s a v) = L.idleW s := nd _ (by rw [idle8]; omega) (by rw [idle8])
  refine hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hiq y hy]; exact hf))
    (fun y hy hf => Or.inr (Or.inl (by rw [← hiq y hy]; exact hf))) (fun haT => ?_)
    (by rw [ei]; exact ⟨h.idleT, hB.idle⟩) (fun h0 => ?_)
    (hB.nb ei (by rw [stA_eq]; exact f _ h.idleT _ (by simp) (by simp)))
    (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hiq y hy] at hf) (fun hf => by rwa [hiq y hy] at hf)
      ea ei ec (by rw [stA_eq]; exact f _ hy _ (by simp) (by simp)) hS))
  · rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩
  · rw [ea] at h0; rw [ec]; exact ⟨h.curT, hB.resume h0⟩

/-- A blocked thread is in no ready or release queue and is not the
switch-to candidate. -/
theorem blocked_out {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) (hnr : ¬ Runnable (L.mem s (stA t))) :
    (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t := by
  refine ⟨?_, ?_, fun e => hnr (by have := (h.actOK (by rw [e]; exact ht)).1; rw [e] at this; exact this)⟩
  · by_contra hne
    exact hnr (h.runQ _ (h.aff t ht) _ (h.prio t ht) t ((h.queued t ht).1 hne))
  · by_contra hne
    exact hnr (h.runR _ (h.aff t ht) t ((h.released t ht).1 hne))

/-- `BoundInv` after the action becomes choose-new, from its queue and idle
parts. -/
theorem BoundInv.choose {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hq : ∀ y ∈ T, (L.mem s (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 → L.mem s (scA y) ≠ 0#u64)
    (hr : ∀ y ∈ T, (L.mem s (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 → L.mem s (scA y) ≠ 0#u64)
    (hidle : L.mem s (scA (L.idleW s)) ≠ 0#u64) (hnb : ¬ Blocked (L.mem s (stA (L.idleW s))))
    (hsa : ∀ y ∈ T, Sch st s y → L.mem s (scA y) ≠ 0#u64 → L.mem s (scA y) ∈ Ac) :
    BoundInv st T Ac (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) := by
  have fk : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    field_wr_node h h.cur (by rw [act_val]; omega) (by rw [act_val]) hy hK hK8
  have sc : ∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) (scA y) =
      L.mem s (scA y) := fun y hy => fk y hy _ (by simp) (by simp)
  have iq : ∀ y ∈ T, L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) (inqA y) =
      L.mem s (inqA y) := fun y hy => fk y hy _ (by simp) (by simp)
  have ei : L.idleW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) = L.idleW s :=
    rd_cur_node h (by rw [act_val]; omega) (by rw [act_val]) (by rw [idle8]; omega) (by rw [idle8])
      (by rw [act_val, idle8]; omega)
  have ea : L.actionW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) = 1#u64 := by
    unfold LawfulStore.actionW
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    exact L.mem_wr_same (nodeAt_aligned (h.nodes _ h.cur) (by rw [act_val]; omega) (by rw [act_val]))
  have ec : L.curW (L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64) = L.curW s :=
    rd_cur_node h (by rw [act_val]; omega) (by rw [act_val]) (by rw [curth0]; omega) (by rw [curth0])
      (by rw [act_val, curth0]; omega)
  refine ⟨fun y hy hf => ?_, fun y hy hf => ?_, fun haT => ?_, ?_, fun h0 => ?_, ?_, fun y hy hS h0 => ?_⟩
  rotate_right
  · rw [sc y hy] at h0 ⊢
    refine hsa y hy (Sch.of_le (fun hf => by rwa [iq y hy] at hf) (fun hf => by rwa [iq y hy] at hf)
      (fun e => ?_) (fun e => by rwa [ei] at e) (fun ⟨e1, _⟩ => by rw [ea] at e1; exact absurd e1 (by decide))
      (fun hb => by rwa [stA_eq, fk y hy _ (by simp) (by simp), ← stA_eq] at hb) hS) h0
    rw [ea] at e; exact absurd (e ▸ hy) (notT_small h.tcbs (by simp))
  rotate_right
  · rw [ei, stA_eq, fk (L.idleW s) h.idleT _ (by simp) (by simp), ← stA_eq]; exact hnb
  · rw [iq y hy] at hf; rw [sc y hy]; exact hq y hy hf
  · rw [iq y hy] at hf; rw [sc y hy]; exact hr y hy hf
  · rw [ea] at haT; exact absurd haT (notT_small h.tcbs (by simp))
  · rw [ei, sc (L.idleW s) h.idleT]; exact hidle
  · rw [ea] at h0; simp at h0

/-- Unbinding the SC `i` of a blocked thread `t` (not the idle thread, and
not current under a resume action): `t`'s SC field and `i`'s `TCB` word are
cleared. -/
theorem unbind_state {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t i : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hidle : L.idleW s ≠ t) (hsc : L.mem s (scA t) = i) (hi0 : i ≠ 0#u64) :
    SchedQueuesInv st T Cs Ω H (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) Q R ∧
      ((L.curW (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) = t →
        L.actionW (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) ≠ 0#u64) →
        BoundInv st T Ac (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64)) ∧
      BoundInv st T Ac (L.wr (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64)
        (L.nodeAt (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64)
          (L.cpu (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64)) layout.node.SCHED_ACTION) 1#u64) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) ∧
      SgOK st Ω Sg (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) ∧
      L.mem (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) (inqA t) = L.mem s (inqA t) ∧
      L.mem (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) (stA t) = L.mem s (stA t) ∧
      L.actionW (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) = L.actionW s ∧
      L.idleW (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) = L.idleW s ∧
      (∀ r ∈ Rp, L.mem (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) (rTcbA r) = L.mem s (rTcbA r)) ∧
      (∀ y ∈ T, L.mem (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) (stA y) = L.mem s (stA y)) ∧
      L.ksb (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) = L.ksb s := by
  obtain ⟨hO, hR, hE⟩ := hX
  have hT := h.tcbs
  have hta := hT t ht
  have hN := h.nodes _ h.cur
  obtain ⟨hq0, hr0, hna⟩ := hout
  obtain ⟨hiS, hit, -⟩ := hE.bound t ht (by rw [hsc]; exact hi0)
  rw [hsc] at hiS hit
  have hm : scTcbA i ∈ Ω := hSg.sub _ (hO.fixW i hiS).1
  have hmo := h.omega _ hm
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hO hSg.sub
  have h1 : SchedQueuesInv st T Cs Ω H (L.wr s (scA t) 0#u64) Q R :=
    inv_wr_field (K := 3464#u64) h ht (by simp) (by simp) (by simp)
  obtain ⟨h2, a2, f2⟩ := omega_wr (v := 0#u64) h1 hm
  have tmU : TmFr st T Cs Nt s (L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64) :=
    (TmFr.wr hT h.nodes hO (scA_aligned hta) (notTmW_field (K := 3464#u64) hT h.nodes
      (fun n hn => h.omega _ (hSg.sub _ (hO.ntB n hn).2)) ht (by simp) (by simp))).trans
      (TmFr.wr hT h1.nodes hO.ksb hmo.1 (notTmW_insc h1 hO.ksb hSg.sub hiS hmo.1
        (by have := (sc_facts hO hiS); obtain ⟨hP, hz⟩ := hO.sc i hiS; exact ⟨by omega, by omega⟩)))
  set s2 := L.wr (L.wr s (scA t) 0#u64) (scTcbA i) 0#u64 with hs2
  have hsa : Aligned (scA t) := scA_aligned hta
  -- the frame from `s` to `s2`
  have F1 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K hK hK8 hne
    rw [f2 y hy K hK hK8]
    exact L.mem_wr_ne hsa (field_aligned (hT y hy) hK hK8)
      (fun e => field_ne hta (hT y hy) (by simp) hK (fun e' h' => hne e'.symm (by rw [← h']; rfl))
        (UScalar.eq_of_val_eq e))
  have F2 : ∀ a ∈ Ω, a.val ≠ (scTcbA i).val → L.mem s2 a = L.mem s a := by
    intro a ha hne
    have ho := h.omega a ha
    rw [hs2, L.mem_wr_ne hmo.1 ho.1 (fun e => hne e.symm)]
    exact L.mem_wr_ne hsa ho.1 (fun e => out_ne_field (K := 3464#u64) ho ht hta (by simp) (by rw [← scA_eq]; exact e))
  have F3 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s2 (L.nodeAt s2 (L.cpu s2) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o h1' h2'
    rw [hs2]
    simp only [LawfulStore.cpu_wr, nodeAt_wr]
    rw [L.mem_wr_ne hmo.1 (nodeAt_aligned hN h1' h2') (fun e => out_ne_node hmo h.cur hN h1' e.symm)]
    exact L.mem_wr_ne hsa (nodeAt_aligned hN h1' h2')
      (fun e => node_ne_field (K := 3464#u64) hN h1' ht hta (by simp) (by rw [← scA_eq]; exact (UScalar.eq_of_val_eq e).symm))
  have sct : L.mem s2 (scA t) = 0#u64 := by
    rw [hs2, L.mem_wr_ne hmo.1 hsa (fun e => out_ne_field (K := 3464#u64) hmo ht hta (by simp) (by rw [← scA_eq]; exact e.symm))]
    exact L.mem_wr_same hsa
  have scy : ∀ y ∈ T, y ≠ t → L.mem s2 (scA y) = L.mem s (scA y) := fun y hy hyt => by
    rw [scA_eq]; exact F1 y hy _ (by simp) (by simp) (fun e => absurd e hyt)
  have iqy : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)
  have ea : L.actionW s2 = L.actionW s := F3 _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW s2 = L.curW s := F3 _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW s2 = L.idleW s := F3 _ (by rw [idle8]; omega) (by rw [idle8])
  have ecs : L.cscW s2 = L.cscW s := F3 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hiv := sc_facts hO hiS
  -- SC words other than `i`'s `TCB` word
  have scw : ∀ c ∈ Scs, ∀ a ∈ Ω, (a.val = c.val + 16 ∨ a.val = c.val + 72 ∨ a.val = c.val + 80 ∨
      a.val = c.val + 88 ∨ (c ≠ i ∧ a.val = c.val + 24)) → L.mem s2 a = L.mem s a := by
    intro c hc a ha hv
    refine F2 a ha (fun e => ?_)
    rw [hiv.2.1] at e
    have := (sc_facts hO hc).1
    have := hiv.1
    by_cases hci : c = i
    · subst hci
      rcases hv with hv | hv | hv | hv | ⟨hv0, -⟩
      all_goals first | omega | exact hv0 rfl
    · have := hO.scDisj c hc i hiS hci
      rcases hv with hv | hv | hv | hv | ⟨-, hv⟩ <;> omega
  have bq : ∀ y ∈ T, (L.mem s2 (inqA y) &&& sched.Q_QUEUED) ≠ 0#u64 → L.mem s2 (scA y) ≠ 0#u64 := by
    intro y hy hf
    rw [iqy y hy] at hf
    by_cases e : y = t
    · subst e; exact absurd hq0 hf
    · rw [scy y hy e]; exact hB.q y hy hf
  have br : ∀ y ∈ T, (L.mem s2 (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 → L.mem s2 (scA y) ≠ 0#u64 := by
    intro y hy hf
    rw [iqy y hy] at hf
    by_cases e : y = t
    · subst e; exact absurd hr0 hf
    · rw [scy y hy e]; exact hB.r y hy hf
  have bidle : L.mem s2 (scA (L.idleW s2)) ≠ 0#u64 := by
    rw [ei, scy (L.idleW s) h.idleT hidle]; exact hB.idle
  have bnb : ¬ Blocked (L.mem s2 (stA (L.idleW s2))) := by
    rw [ei, stA_eq, F1 (L.idleW s) h.idleT _ (by simp) (by simp) (fun _ => by simp), ← stA_eq]; exact hB.idleNB
  have bsa : ∀ y ∈ T, Sch st s2 y → L.mem s2 (scA y) ≠ 0#u64 → L.mem s2 (scA y) ∈ Ac := by
    intro y hy hS h0
    have hyt : y ≠ t := fun e => by subst e; exact h0 sct
    rw [scy y hy hyt] at h0 ⊢
    exact hB.sact y hy (Sch.of_eq (fun hf => by rwa [iqy y hy] at hf) (fun hf => by rwa [iqy y hy] at hf)
      ea ei ec (by rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)) hS) h0
  refine ⟨h2, fun hcur => ⟨bq, br, fun haT => ?_, bidle, fun h0 => ?_, bnb, bsa⟩, BoundInv.choose h2 bq br bidle bnb bsa,
    ⟨hO.ksb, ⟨fun u hu hs => ?_, fun u hu hs hn => ?_, fun r hr => ?_, fun r hr => ?_, fun r hr hn => ?_,
        fun c hc => by
          rw [F2 _ (hSg.sub _ (hO.repW c hc)) (fun e => by
            rw [(sc_facts hO hc).2.2.2.2.2.2.1, hiv.2.1] at e
            have := (sc_facts hO hc).1; have := hiv.1
            by_cases hci : c = i
            · subst hci; omega
            · have := hO.scDisj c hc i hiS hci; omega)]
          exact hR.screp c hc⟩,
      ⟨⟨fun u hu hb => ?_, by rw [ecs]; exact hE.cur, fun c hc => by rw [scw c hc _ (hcΩ _ hc).2.1 (Or.inl (sc_facts hO hc).2.2.1)]; exact hE.core c hc,
        fun u hu => by
          rw [show L.mem s2 (boundA u) = L.mem s (boundA u) from F1 u hu _ (by simp) (by simp) (fun _ => by simp)]
          exact hE.bnd u hu,
        ScExtra.nsc_keep hE.nsc (fun n hn => F2 _ (hSg.sub _ (hO.ntW n hn)) (fun e => by
            rw [hiv.2.1] at e
            have := hO.ntSc n hn i hiS; have := hiv.1; omega))
          (fun c hc => F2 _ (hSg.sub _ (hO.snW c hc)) (fun e => by
            obtain ⟨hPc, hzc⟩ := hO.sc c hc
            rw [scNtfnA_val hPc hzc, hiv.2.1] at e
            have := (sc_facts hO hc).1; have := hiv.1
            by_cases hci : c = i
            · subst hci; omega
            · have := hO.scDisj c hc i hiS hci; omega))
          (fun c hc => scw c hc _ (hcΩ _ hc).2.2.1 (Or.inr (Or.inl (sc_facts hO hc).2.2.2.1))), hE.tm.tmfr tmU, hE.ntb.tmfr tmU,
        fun c hc => by
          rw [F2 _ (hSg.sub _ (hO.snW c hc)) (fun e => by
            obtain ⟨hPc, hzc⟩ := hO.sc c hc
            rw [scNtfnA_val hPc hzc, hiv.2.1] at e
            have := (sc_facts hO hc).1; have := hiv.1
            by_cases hci : c = i
            · subst hci; omega
            · have := hO.scDisj c hc i hiS hci; omega)]
          exact hE.scn c hc,
        ⟨fun c hc h0 => by
          by_cases hci : c = i
          · subst hci
            rw [hs2, L.mem_wr_same hmo.1] at h0; exact absurd rfl h0
          · have e1 : L.mem s2 (scTcbA c) = L.mem s (scTcbA c) := F2 _ (hcΩ c hc).1 (fun e => by
              rw [(sc_facts hO hc).2.1, hiv.2.1] at e
              have := (sc_facts hO hc).1; have := hiv.1
              have := hO.scDisj c hc i hiS hci; omega)
            rw [e1] at h0 ⊢; exact hE.yt.1 c hc h0,
         fun u hu => by
          rw [show yieldA u = core.num.U64.wrapping_add u 3472#u64 from rfl,
            F1 u hu _ (by simp) (by simp) (fun _ => by simp)]
          exact hE.yt.2.1 u hu,
         fun c hc => by
          rw [F2 _ (hSg.sub _ (hO.syW c hc)) (fun e => by
            rw [show scYieldFromA c = core.num.U64.wrapping_add c layout.sc.YIELD_FROM from rfl,
              (sc_facts hO hc).2.2.2.2.2.2.2, hiv.2.1] at e
            have := (sc_facts hO hc).1; have := hiv.1
            by_cases hci : c = i
            · subst hci; omega
            · have := hO.scDisj c hc i hiS hci; omega)]
          exact hE.yt.2.2 c hc⟩⟩, fun c hc hc0 h0 => by
        by_cases hci : c = i
        · subst hci
          rw [hs2, L.mem_wr_same hmo.1] at h0; exact absurd rfl h0
        · have e1 : L.mem s2 (scTcbA c) = L.mem s (scTcbA c) := F2 _ (hcΩ c hc).1 (fun e => by
            rw [(sc_facts hO hc).2.1, hiv.2.1] at e
            have := (sc_facts hO hc).1; have := hiv.1
            have := hO.scDisj c hc i hiS hci; omega)
          rw [e1] at h0 ⊢
          have hyT := hE.yt.1 c hc h0
          have hb := hE.tsc c hc hc0 h0
          by_cases hyt : L.mem s (scTcbA c) = t
          · rw [hyt, hsc] at hb; exact absurd hb.symm hci
          · rw [scA_eq, F1 _ hyT _ (by simp) (by simp) (fun e => absurd e hyt), ← scA_eq]; exact hb⟩⟩,
    SCsOK.keep' hS ⟨hO, hR, hE⟩ (by simp [hs2]) (fun y hy => ?_) ecs (fun c hc => ?_) (fun c hc =>
      F2 _ (spor_omega hO hc) (fun e => by
        obtain ⟨hPc, hzc⟩ := hO.sc c hc
        rw [sporA_val hPc hzc, hiv.2.1] at e
        have := (sc_facts hO hc).1; have := hiv.1
        by_cases hci : c = i
        · subst hci; omega
        · have := hO.scDisj c hc i hiS hci; omega))
      (fun c hc => F2 _ (hSg.sub _ (hO.repW c hc)) (fun e => by
        rw [(sc_facts hO hc).2.2.2.2.2.2.1, hiv.2.1] at e
        have := (sc_facts hO hc).1; have := hiv.1
        by_cases hci : c = i
        · subst hci; omega
        · have := hO.scDisj c hc i hiS hci; omega)),
    ⟨hSg.sub, fun b hb => by simp only [hs2, LawfulStore.ksb_wr]; exact hSg.ks b hb,
      fun o h1 h2 => by simp only [hs2, LawfulStore.ksb_wr]; exact hSg.ksΩ o h1 h2⟩, iqy t ht,
    by rw [stA_eq]; exact F1 t ht _ (by simp) (by simp) (fun _ => by simp), ea, ei, fun r hr =>
      F2 _ (hrΩ _ hr).1 (fun e => by
        rw [rTcbA_val (hO.rp _ hr), hiv.2.1] at e
        have := hO.rpSc _ hr i hiS; have := hiv.1; omega),
    fun y hy => by rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp), by simp [hs2]⟩
  · rw [ea] at haT ⊢; rw [scy _ haT hna]; exact hB.act haT
  · rw [ea] at h0; rw [ec]
    have hct : L.curW s ≠ t := fun e => hcur (by rw [ec]; exact e) (by rw [ea]; exact h0)
    rw [scy (L.curW s) h.curT hct]; exact hB.resume h0
  · have st2 : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
      rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)
    have rp2 : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
      F1 y hy _ (by simp) (by simp) (fun _ => by simp)
    rw [st2 u hu] at hs; rw [rp2 u hu]
    obtain ⟨h1', h2'⟩ := hR.reply u hu hs
    refine ⟨h1', ?_⟩
    rw [F2 _ (hrΩ _ h1').1 (fun e => ?_)]; exact h2'
    rw [rTcbA_val (hO.rp _ h1'), hiv.2.1] at e
    have := hO.rpSc _ h1' i hiS; have := hiv.1; omega
  · have st2 : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
      rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)
    have rp2 : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
      F1 y hy _ (by simp) (by simp) (fun _ => by simp)
    rw [st2 u hu] at hs; rw [rp2 u hu] at hn ⊢
    obtain ⟨h1', h2'⟩ := hR.recv u hu hs hn
    refine ⟨h1', ?_⟩
    rw [F2 _ (hrΩ _ h1').1 (fun e => ?_)]; exact h2'
    rw [rTcbA_val (hO.rp _ h1'), hiv.2.1] at e
    have := hO.rpSc _ h1' i hiS; have := hiv.1; omega
  · rw [F2 _ (hrΩ _ hr).2.2 (fun e => ?_)]
    · exact hR.next r hr
    rw [rNextA_val (hO.rp _ hr), hiv.2.1] at e
    have := hO.rpSc _ hr i hiS; have := hiv.1; omega
  · rw [F2 _ (hrΩ _ hr).2.1 (fun e => ?_)]
    · exact hR.prev r hr
    rw [rPrevA_val (hO.rp _ hr), hiv.2.1] at e
    have := hO.rpSc _ hr i hiS; have := hiv.1; omega
  · have st2 : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
      rw [stA_eq]; exact F1 y hy _ (by simp) (by simp) (fun _ => by simp)
    have rp2 : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
      F1 y hy _ (by simp) (by simp) (fun _ => by simp)
    have rtq : L.mem s2 (rTcbA r) = L.mem s (rTcbA r) := F2 _ (hrΩ _ hr).1 (fun e => by
      rw [rTcbA_val (hO.rp _ hr), hiv.2.1] at e
      have := hO.rpSc _ hr i hiS; have := hiv.1; omega)
    rw [rtq] at hn ⊢
    obtain ⟨b0, b1, b2, b3⟩ := hR.back r hr hn
    rw [rp2 _ b1, st2 _ b1]; exact ⟨b0, b1, b2, b3⟩
  · have hut : u ≠ t := fun e => by subst e; exact hb sct
    rw [scy u hu hut] at hb ⊢
    obtain ⟨c1, c2, c3⟩ := hE.bound u hu hb
    have hci : L.mem s (scA u) ≠ i := fun e => by rw [e, hit] at c2; exact hut c2.symm
    obtain ⟨-, e1, e2, -⟩ := sc_facts hO c1
    rw [scw _ c1 _ (hcΩ _ c1).1 (Or.inr (Or.inr (Or.inr (Or.inr ⟨hci, e1⟩)))),
      scw _ c1 _ (hcΩ _ c1).2.1 (Or.inl e2)]
    exact ⟨c1, c2, c3⟩
  · by_cases e : y = t
    · subst e; exact Or.inr sct
    · exact Or.inl (scy y hy e)
  · obtain ⟨-, -, -, e3, e4, e5, -, -⟩ := sc_facts hO hc
    obtain ⟨-, -, c3, c4, c5⟩ := hcΩ c hc
    exact ⟨scw c hc _ c3 (Or.inr (Or.inl e3)), scw c hc _ c4 (Or.inr (Or.inr (Or.inl e4))),
      scw c hc _ c5 (Or.inr (Or.inr (Or.inr (Or.inl e5))))⟩

/-- `reschedule_required` keeps the `IN_QUEUES` word of a thread other than
the switch-to candidate, and the idle thread. -/
theorem sched.reschedule_required.frame (s : S) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SgOK st Ω Sg s) {y : U64} (hy : y ∈ T)
    (hya : L.actionW s ≠ y) :
    sched.reschedule_required st s ⦃ s' => L.mem s' (inqA y) = L.mem s (inqA y) ∧ L.idleW s' = L.idleW s ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  refine WP.spec_bind (Pₘ := fun s1 => (∃ Q1 R1, SchedQueuesInv st T Cs Ω H s1 Q1 R1) ∧
    L.mem s1 (inqA y) = L.mem s (inqA y) ∧ L.idleW s1 = L.idleW s) ?_ ?_
  · split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        have hrun : Runnable (L.mem s (stA act)) := by
          have := (h.actOK (act_post ▸ hT)).1; rw [← act_post] at this; exact this
        have hbd : L.mem s (scA act) ≠ 0#u64 := by
          have := hB.act (act_post ▸ hT); rw [← act_post] at this; exact this
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · have hc := h.aff act hT
          have hp := h.prio act hT
          refine WP.spec_mono (WP.spec_and (sched.enqueue.sch (Sg := Sg) s act Q R h hB hS hT (fun _ => hb ‹_›)
            (fun _ => hrun) (fun _ => hbd) (fun _ => hB.sact act hT (Or.inr (Or.inr (Or.inl act_post.symm))) hbd))
            (sched.enqueue.foot s act _ h.tcbs hT hp (h.nodes _ hc) (h.nodes _ h.cur) ((h.ready _ hc).1.rel _ hp)
              (fun h0 => h.notQ hT h0 hc hp))) fun s1 hh => ?_
          obtain ⟨⟨p1, -, -, -⟩, hw, -⟩ := hh
          have hW : ∀ w ∈ act :: Q (L.mem s (affA act)) (L.mem s (prioA act)), w ∈ T := by
            intro w hw; rcases List.mem_cons.1 hw with rfl | hw
            · exact hT
            · exact h.memT hc hp hw
          obtain ⟨-, hi, -, -, ei⟩ := qfoot_keep h hS hW hc hT p128 hw
          exact ⟨p1.inv, hi y hy (fun e => hya (by rw [← act_post, e])), ei⟩
        · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl, rfl⟩
      · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl, rfl⟩
    · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, rfl, rfl⟩
  · rintro s1 ⟨⟨Q1, R1, h1⟩, e1, i1⟩
    refine WP.spec_mono (sched.set_action.spec s1 _) fun s2 e => ?_
    subst e
    refine ⟨?_, ?_⟩
    · rw [inqA_eq, field_wr_node h1 h1.cur (by rw [act_val]; omega) (by rw [act_val]) hy (by simp) (by simp),
        ← inqA_eq]; exact e1
    · rw [← i1]
      exact rd_cur_node h1 (by rw [act_val]; omega) (by rw [act_val]) (by rw [idle8]; omega) (by rw [idle8])
        (by rw [act_val, idle8]; omega)

theorem sched.reschedule_required.resume (s : S) (h0 : L.actionW s = 0#u64) :
    sched.reschedule_required st s ⦃ s' => s' = L.wr s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) 1#u64 ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, ea⟩
  split
  · rename_i hne; exfalso; rw [ea, h0, resume_val] at hne; simp at hne
  · try simp only [Aeneas.Std.bind_ok]
    rw [choose_val]; exact sched.set_action.spec s _

/-- `maybe_return_sched_context` (seL4 `maybeReturnSchedContext`) on a thread
in no ready or release queue and not the switch-to candidate: if the
notification's SC is the thread's, it is unbound (and the scheduler asked to
choose if the thread is current). The thread's state and `IN_QUEUES` word
and the idle thread are kept, and the thread is not the candidate after. -/
theorem notification.maybe_return_sched_context.inv (s : S) (n t : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T)
    (hout : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 ∧
      L.actionW s ≠ t)
    (hidle : L.idleW s ≠ t) :
    notification.maybe_return_sched_context st s n t ⦃ s' => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      L.mem s' (inqA t) = L.mem s (inqA t) ∧ L.mem s' (stA t) = L.mem s (stA t) ∧ L.actionW s' ≠ t ∧
      L.idleW s' = L.idleW s ∧ (∀ r ∈ Rp, L.mem s' (rTcbA r) = L.mem s (rTcbA r)) ∧
      (∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y)) ∧ L.ksb s' = L.ksb s ∧
      (L.mem s' (scA t) = L.mem s (scA t) ∨ L.mem s' (scA t) = 0#u64) ⦄ := by
  have hta := h.tcbs t ht
  unfold notification.maybe_return_sched_context
  step with obj.Ntfn.sc.any as ⟨i, _⟩
  step with obj.Sc.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, hX, hS, hSg, rfl, rfl, hout.2.2, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl,
      Or.inl rfl⟩
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  step with obj.Tcb.sc.spec as ⟨i1, ei1⟩
  split
  · rename_i hii
    have hsc : L.mem s (scA t) = i := by rw [← ei1, hii]
    step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
    step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
    have key := unbind_state h hB hX hS hSg ht hout hidle hsc hi0
    rw [← e1, ← e2] at key
    obtain ⟨k1, kB, kB3, k3, k4, k5, q2, st2, a2, i2, r2, sa2, ks2⟩ := key
    have na2 : L.actionW s2 ≠ t := by rw [a2]; exact hout.2.2
    have sct2 : L.mem s2 (scA t) = 0#u64 := by
      obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht (by rw [hsc]; exact hi0)
      rw [hsc] at hiS
      have hm := h.omega _ (hSg.sub _ (hX.1.fixW i hiS).1)
      rw [e2, e1, L.mem_wr_ne hm.1 (scA_aligned hta)
        (fun e => out_ne_field (K := 3464#u64) hm ht hta (by simp) (by rw [← scA_eq]; exact e.symm))]
      exact L.mem_wr_same (scA_aligned hta)
    step with sched.cur_thread.spec as ⟨t1, et1⟩
    step with tcb_eq.blk as ⟨b1, eb1⟩
    split
    · by_cases ha0 : L.actionW s2 = 0#u64
      · refine WP.spec_mono (sched.reschedule_required.resume s2 ha0) fun s3 e3 => ?_
        subst e3
        have f := fr_node (Sg := Sg) (hi8 := fun _ => by simp [layout.node.SCHED_ACTION, layout.node.REPROGRAM, layout.node.CUR_THREAD]) (v := 1#u64) k1 k5 k1.cur (by rw [act_val]; omega) (by rw [act_val])
          (hto := ⟨by rw [act_val]; omega, by rw [act_val]; omega⟩)
          (fun _ => by rw [act_val]; omega)
        obtain ⟨j1, ea3⟩ := inv_set_action k1 (Or.inr (Or.inl rfl)) (fun h1T => absurd h1T (notT_small k1.tcbs (by simp)))
        refine ⟨⟨Q, R, j1⟩, kB3, k3.fr f, k4.fr f, k5.fr f, ?_, ?_, ?_, ?_,
          fun r hr => (f.sig _ (k3.1.tcbW hr)).trans (r2 r hr), fun y hy => ?_, by rw [L.ksb_wr]; exact ks2,
          Or.inr (by rw [scA_eq, field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) ht (by simp) (by simp),
            ← scA_eq]; exact sct2)⟩
        rotate_right
        · rw [stA_eq, field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) hy (by simp) (by simp),
            ← stA_eq]; exact sa2 y hy
        · rw [inqA_eq, field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) ht (by simp) (by simp),
            ← inqA_eq]; exact q2
        · rw [stA_eq, field_wr_node k1 k1.cur (by rw [act_val]; omega) (by rw [act_val]) ht (by simp) (by simp),
            ← stA_eq]; exact st2
        · rw [ea3]; exact fun e => notT_small k1.tcbs (by simp) (e ▸ ht)
        · rw [← i2]
          exact rd_cur_node k1 (by rw [act_val]; omega) (by rw [act_val]) (by rw [idle8]; omega) (by rw [idle8])
            (by rw [act_val, idle8]; omega)
      · have kB2 := kB (fun _ => ha0)
        exact WP.spec_mono (WP.spec_and (sched.reschedule_required.sch s2 Q R k1 kB2 k5)
          (sched.reschedule_required.frame s2 Q R k1 kB2 k5 ht na2)) fun s3 hh =>
          ⟨hh.1.1.inv, hh.1.1.bnd, k3.fr hh.1.1.fr, k4.fr hh.1.1.fr, k5.fr hh.1.1.fr, hh.2.1.trans q2,
            (hh.1.2.2.2.1 t ht).trans st2, by rw [hh.1.2.1]; exact fun e => notT_small k1.tcbs (by simp) (e ▸ ht),
            hh.2.2.trans i2, fun r hr => (hh.1.1.fr.sig _ (k3.1.tcbW hr)).trans (r2 r hr),
            fun y hy => (hh.1.2.2.2.1 y hy).trans (sa2 y hy), hh.1.1.fr.ksb.trans ks2,
            Or.inr (by rw [hh.1.1.fr.sc t ht]; exact sct2)⟩
    · rename_i hb1
      have hne : t ≠ t1 := fun e => hb1 (by rw [eb1, decide_eq_true_eq]; exact e)
      exact (WP.spec_ok _).2 ⟨⟨Q, R, k1⟩, kB (fun e => absurd (by rw [et1]; exact e.symm) hne), k3, k4, k5,
        q2, st2, na2, i2, r2, sa2, ks2, Or.inr sct2⟩
  · exact (WP.spec_ok _).2 ⟨⟨Q, R, h⟩, hB, hX, hS, hSg, rfl, rfl, hout.2.2, rfl, fun _ _ => rfl, fun _ _ => rfl, rfl,
      Or.inl rfl⟩

/-! ## `receive_signal` blocking -/

/-- The blocking branch of `receive_signal` (seL4 `receiveSignal` on an idle
or waiting notification): `t` blocks, joins the queue, and the notification's
SC returns to it if it had it. -/
theorem ntfn_block {A : Type _} (s : S) (a : A) (t n : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t) (hidle : L.idleW s ≠ t)
    (hH : H n = some .ntfn) (hst0 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64) :
    (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_NTFN
      let s2 ← obj.Tcb.set_block_obj st t s1 n
      let s3 ← sched.schedule_tcb st s2 t
      let s4 ← notification.ntfn_append st s3 n t
      let s5 ← notification.maybe_return_sched_context st s4 n t
      ok (s5, a)) ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
  have ht := hc.mem
  have hta := h.tcbs t ht
  have hN := h.nodes _ h.cur
  step with obj.Tcb.set_state.spec as ⟨s1, e1⟩
  step with obj.Tcb.set_block_obj.wr as ⟨s2, e2⟩
  have h1 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s1 Q R := by
    rw [e1]; exact blk_set_state h hc
  have h2 : SchedQueuesInvX st T Cs Ω H {y | y ∈ (∅ : Set U64) ∨ y = t} s2 Q R := by
    rw [e2]; exact inv_wr_fieldX (K := 3336#u64) h1 ht (Or.inr rfl) (by simp) (by simp) (by simp)
  rw [stA_eq] at e1
  have w2 : WritesIn st s s2 (BlkFoot st s t 0#u64) := by
    rw [e2, e1]; exact blk_wr_field hta (blk_wr_field (K := 3328#u64) hta (WritesIn.refl _ _) (by simp)) (by simp)
  have v2 : L.mem s2 (stA t) = sched.TS_BLOCKED_ON_NTFN := by
    rw [e2, fld_wr_ne' hta (blockA_eq t) (stA_eq t) (by simp) (by simp) (by simp) (by simp) (by simp), e1, stA_eq]
    exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have b2 : L.mem s2 (blockA t) = n := by
    rw [e2]; exact L.mem_wr_same (field_aligned hta (by simp) (by simp))
  have a2 : L.actionW s2 = L.actionW s := by
    rw [e2, act_wr_field (h1.nodes _ h1.cur) ht hta (blockA_eq t) (by simp) (by simp),
      e1, act_wr_field hN ht hta rfl (by simp) (by simp)]
  have hbl : Blocked sched.TS_BLOCKED_ON_NTFN := Or.inr (Or.inr rfl)
  refine WP.spec_bind (sched.schedule_tcb.blk s2 t h2 (by rw [v2]; exact blocked_not_runnable hbl)) ?_
  rintro s3 ⟨h3, e3, hc3⟩
  obtain ⟨w3, a3, v3, b3, -, -⟩ := blk_sched h2 ht w2 a2 e3
  rw [v2] at v3; rw [b2] at b3
  obtain ⟨-, -, r3, -, r6⟩ := ts_vals
  refine WP.spec_bind (blk_tail (f := notification.ntfn_append st s3 n t) (r0 := 0#u64) (hidl := hidle)
    h hB hX hS hSg ht
    (Or.inr (Or.inr ⟨rfl, hH, rfl⟩)) hst0 h3 w3 a3 v3 b3 (fun h0 => absurd rfl h0)
    (fun h1 => absurd (v3.symm.trans h1) (by rw [r3, r6]; decide)) hc.old (fun h0 => absurd rfl h0) hc.ac
    (fun xs hE hq hn => WP.spec_mono (WP.spec_and
      (notification.ntfn_append.rel s3 n t xs h3.tcbs hE hq ht hn)
      (notification.ntfn_append.foot s3 n t xs h3.tcbs hE hq ht hn))
      fun s4 hh => ⟨hh.1.1, by rw [hh.1.2, ntfn_wait_val], hh.2⟩)) ?_
  rintro s4 ⟨h4, hB4, hX4, hS4, hSg4, ea4, ec4, v4, ei4⟩
  refine WP.spec_bind (notification.maybe_return_sched_context.inv s4 n t Q R h4 hB4 hX4 hS4 hSg4 ht
    (blocked_out h4 ht (by rw [v4]; exact blocked_not_runnable hbl)) (by rw [ei4]; exact hidle)) ?_
  rintro s5 hh
  simp only [WP.spec_ok, WP.uncurry'_pair]
  exact ⟨hh.1, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2.1⟩

theorem ntfn_idle_val : obj.NTFN_IDLE = 0#u64 := by unfold obj.NTFN_IDLE; rfl
theorem ntfn_wait_val' : obj.NTFN_WAITING = 1#u64 := by unfold obj.NTFN_WAITING; rfl

/-- Clearing the badge register keeps the invariants. -/
theorem badge0_all {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {t : U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) :
    SchedQueuesInv st T Cs Ω H (L.wr s (core.num.U64.wrapping_add t 256#u64) 0#u64) Q R ∧
      BoundInv st T Ac (L.wr s (core.num.U64.wrapping_add t 256#u64) 0#u64) ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z (L.wr s (core.num.U64.wrapping_add t 256#u64) 0#u64) ∧
      SCsOK st T Ω Sg Scs Z Ac (L.wr s (core.num.U64.wrapping_add t 256#u64) 0#u64) ∧
      SgOK st Ω Sg (L.wr s (core.num.U64.wrapping_add t 256#u64) 0#u64) := by
  obtain ⟨b1, b2⟩ := bx_field (K := 256#u64) (v := 0#u64) h hB hX hSg.sub ht (by simp) (by simp) (by simp) (by simp)
  exact ⟨inv_wr_field h ht (by simp) (by simp) (by simp), b1, b2,
    SCsOK.field h hS hX ht (by simp) (by simp) (by simp),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩

/-- seL4 `receiveSignal` on an idle or waiting notification (the receiver
blocks, or gets badge 0 if non-blocking) keeps the invariants. -/
theorem notification.receive_signal.block {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t n : U64)
    (blocking : Bool) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ht : t ∈ T) (hc : blocking = true → CanBlock st T Ac s t)
    (hidle : L.idleW s ≠ t) (hH : H n = some .ntfn) (hst0 : L.epState s n = 0#u64 ∨ L.epState s n = 1#u64) :
    notification.receive_signal st ar s a t n blocking ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
  have hta := h.tcbs t ht
  have nb : (do let s1 ← obj.Tcb.set_reg st t s layout.reg.BADGE 0#u64; ok (s1, a)) ⦃ s' _ =>
      (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
        SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ⦄ := by
    refine WP.spec_bind (obj.Tcb.set_reg.badge s t 0#u64 hta) ?_
    rintro s1 rfl
    simp only [WP.spec_ok, WP.uncurry'_pair]
    obtain ⟨k1, k2, k3, k4, k5⟩ := badge0_all h hB hX hS hSg ht
    exact ⟨⟨Q, R, k1⟩, k2, k3, k4, k5⟩
  unfold notification.receive_signal
  step with obj.Ntfn.state.spec as ⟨v, hv⟩
  split
  · split
    · exact ntfn_block s a t n Q R h hB hX hS hSg (hc ‹_›) hidle hH hst0
    · exact nb
  · split
    · split
      · exact ntfn_block s a t n Q R h hB hX hS hSg (hc ‹_›) hidle hH hst0
      · exact nb
    · exfalso
      rename_i h1 h2
      rw [ntfn_idle_val] at h1; rw [ntfn_wait_val'] at h2
      rcases hst0 with e0 | e0 <;> rw [← hv] at e0 <;> contradiction

/-! ## `take_reply` (the reply bookkeeping of `receive_ipc`) -/

theorem obj.Reply.tcb.blk (s : S) (r : obj.Reply) : obj.Reply.tcb st r s ⦃ v => v = L.mem s (rTcbA r) ⦄ := by
  unfold obj.Reply.tcb; step*; simp_all [rTcbA]

theorem tcb_ne.blk (a b : obj.Tcb) :
    core.cmp.PartialEq.ne.trait_default obj.Tcb.Insts.CoreCmpPartialEqTcb a b ⦃ r => r = true ↔ a ≠ b ⦄ := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq]

/-- `CanBlock` across `cancel_ipc` of another thread. -/
theorem CanBlock.keepT {s s' : S} {t u : U64} (hc : CanBlock st T Ac s t) (hut : t ≠ u) (hT : TcbPlaced T)
    (k : KeepT st T Cs Rp Scs Nt u s s') : CanBlock st T Ac s' t := by
  refine ⟨hc.mem, by rw [k.stf hc.mem hut]; exact hc.nb, by rw [k.stf hc.mem hut]; exact hc.nrp,
    by rw [k.inqf hc.mem]; exact hc.nq, by rw [k.inqf hc.mem]; exact hc.nr, ?_, by rw [k.idleW]; exact hc.ni,
    by rw [k.scf hc.mem]; exact hc.ac⟩
  rcases k.act with e | e
  · rw [e]; exact hc.na
  · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hc.mem)

/-- seL4 `receiveIPC`'s reply bookkeeping (`take_reply`): a reply object
that names another thread is taken from it (`cancel_ipc`), so the returned
reply object is unused or names the receiver. -/
theorem endpoint.take_reply.inv {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hcap : ∀ p g, cap = .Reply p g → p ∈ Rp) :
    endpoint.take_reply st ar s a t cap ⦃ reply s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧
      BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
      CanBlock st T Ac s' t ∧ L.idleW s' = L.idleW s ∧
      (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s' (rTcbA reply) = 0#u64 ∨ L.mem s' (rTcbA reply) = t)) ∧
      L.ksb s' = L.ksb s ∧ (¬ Blocked (L.mem s (stA (L.idleW s))) → ¬ Blocked (L.mem s' (stA (L.idleW s')))) ⦄ := by
  have base : ∀ p, (p ≠ 0#u64 → p ∈ Rp ∧ (L.mem s (rTcbA p) = 0#u64 ∨ L.mem s (rTcbA p) = t)) →
      (ok (p, s, a) : Result (obj.Reply × S × A)) ⦃ reply s' _ => SchedQueuesInv st T Cs Ω H s' Q R ∧
        BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧
        CanBlock st T Ac s' t ∧ L.idleW s' = L.idleW s ∧
        (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s' (rTcbA reply) = 0#u64 ∨ L.mem s' (rTcbA reply) = t)) ∧
        L.ksb s' = L.ksb s ∧ (¬ Blocked (L.mem s (stA (L.idleW s))) → ¬ Blocked (L.mem s' (stA (L.idleW s')))) ⦄ :=
    fun p hp => (WP.spec_ok _).2 ⟨h, hB, hX, hS, hSg, hc, rfl, hp, rfl, id⟩
  unfold endpoint.take_reply
  split
  case h_5 p g =>
    have hp := hcap p g rfl
    step with obj.Reply.tcb.blk as ⟨i, ei⟩
    step with obj.Tcb.is_null.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hi0 : i = 0#u64 := by simpa [eb] using hb
      exact base p fun _ => ⟨hp, Or.inl (by rw [← ei, hi0])⟩
    rename_i hb
    have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
    step with tcb_ne.blk as ⟨b1, eb1⟩
    split
    · rename_i hb1
      have hit : i ≠ t := fun e => (eb1.1 hb1) e
      obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
      rw [← ei] at hiT
      refine WP.spec_bind (ipc.cancel_ipc.all s a i Q R h hiT hB hX hSg.sub) ?_
      rintro ⟨s1, a1⟩ ⟨h1, hB1, hX1, nb1, -, -, k1, clr1⟩
      try simp only [WP.uncurry'_pair]
      refine (WP.spec_ok _).2 ⟨h1, hB1, hX1, hS.keepT hX k1, ⟨hSg.sub, fun b hb => by rw [k1.ksb]; exact hSg.ks b hb,
        fun o h1' h2' => by rw [k1.ksb]; exact hSg.ksΩ o h1' h2'⟩, hc.keepT (Ne.symm hit) h.tcbs k1, k1.idleW,
        fun _ => ⟨hp, Or.inl (clr1 p hp ei.symm)⟩, k1.ksb, fun hnb => ?_⟩
      rw [k1.idleW]
      by_cases hii : L.idleW s = i
      · rw [hii]; exact nb1
      · rw [k1.stf (y := L.idleW s) h.idleT hii]; exact hnb
    · rename_i hb1
      have hit : i = t := by by_contra e; exact hb1 (eb1.2 e)
      exact base p fun _ => ⟨hp, Or.inr (by rw [← ei, hit])⟩
  all_goals exact base _ fun h0 => absurd rfl h0

/-! ## `receive_ipc` -/

/-- The invariants the IPC paths keep. -/
def BlkOK (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s : S) : Prop :=
  (∃ Q R, SchedQueuesInv st T Cs Ω H s Q R) ∧ BoundInv st T Ac s ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s ∧
    SCsOK st T Ω Sg Scs Z Ac s ∧ SgOK st Ω Sg s

theorem obj.Tcb.bound_ntfn.any (s : S) (t : obj.Tcb) : obj.Tcb.bound_ntfn st t s ⦃ _ => True ⦄ := by
  unfold obj.Tcb.bound_ntfn; step*

/-- `CanBlock` after `maybe_return_sched_context`. -/
theorem CanBlock.mrsc {s s' : S} {t : U64} (hc : CanBlock st T Ac s t) (hq : L.mem s' (inqA t) = L.mem s (inqA t))
    (hs : L.mem s' (stA t) = L.mem s (stA t)) (ha : L.actionW s' ≠ t) (hi : L.idleW s' = L.idleW s)
    (hsc : L.mem s' (scA t) = L.mem s (scA t) ∨ L.mem s' (scA t) = 0#u64) :
    CanBlock st T Ac s' t :=
  ⟨hc.mem, by rw [hs]; exact hc.nb, by rw [hs]; exact hc.nrp, by rw [hq]; exact hc.nq, by rw [hq]; exact hc.nr, ha,
    by rw [hi]; exact hc.ni, fun h0 => by
      rcases hsc with e | e
      · rw [e] at h0 ⊢; exact hc.ac h0
      · exact absurd e h0⟩

theorem ntfn_active_val : obj.NTFN_ACTIVE = 2#u64 := by unfold obj.NTFN_ACTIVE; rfl
theorem ep_recv_val' : obj.EP_RECV = 2#u64 := by unfold obj.EP_RECV; rfl

/-- seL4 `receiveIPC`: the reply bookkeeping (`take_reply`), the bound
notification's SC going back to it (`maybe_return_sched_context`), and the
blocking (or polling) end on an idle or receiving endpoint keep the
invariants; given that the two other ends, `complete_signal` (an active
bound notification) and `receive_from_sender` (a sending endpoint), do. -/
theorem endpoint.receive_ipc.inv {A : Type _} (ar : machine.Arch A) (s : S) (a : A) (t : U64)
    (cap : capability.Cap) (blocking : Bool) (reply_cap : capability.Cap) (e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hc : CanBlock st T Ac s t)
    (hptr : capability.Cap.ptr cap = ok e) (hH : H e = some .ep)
    (hcap : ∀ p g, reply_cap = .Reply p g → p ∈ Rp)
    (hcs : ∀ (s1 : S) (a1 : A) (n : U64), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → CanBlock st T Ac s1 t →
      n = L.mem s1 (boundA t) → n ≠ 0#u64 → L.epState s1 n = 2#u64 →
      notification.complete_signal st ar s1 a1 n t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄)
    (hrfs : ∀ (s2 : S) (a2 : A) (r : U64), BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s2 → CanBlock st T Ac s2 t →
      (r ≠ 0#u64 → r ∈ Rp ∧ (L.mem s2 (rTcbA r) = 0#u64 ∨ L.mem s2 (rTcbA r) = t)) →
      L.ksb s2 = L.ksb s → ¬ Blocked (L.mem s2 (stA (L.idleW s2))) →
      L.epState s2 e ≠ 0#u64 → L.epState s2 e ≠ 2#u64 →
      endpoint.receive_from_sender st ar s2 a2 t e r ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄) :
    endpoint.receive_ipc st ar s a t cap blocking reply_cap ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold endpoint.receive_ipc
  rw [hptr]
  simp only [Aeneas.Std.bind_ok]
  refine WP.spec_bind (endpoint.take_reply.inv ar s a t reply_cap Q R h hB hX hS hSg hc hcap) ?_
  rintro ⟨reply, s1, a1⟩ ⟨h1, hB1, hX1, hS1, hSg1, hc1, hi1, hr1, kb1, ib1⟩
  have hidle := hc.ni
  have ib1 := ib1 hB.idleNB
  try simp only [WP.uncurry'_pair]
  have ht := hc.mem
  -- the end on the endpoint
  have tail : ∀ (s2 : S) (a2 : A) (Q2 : U64 → U64 → List U64) (R2 : U64 → List U64),
      SchedQueuesInv st T Cs Ω H s2 Q2 R2 → BoundInv st T Ac s2 → XInv st T Cs Ω Sg Rp Scs Nt Z s2 →
      SCsOK st T Ω Sg Scs Z Ac s2 → SgOK st Ω Sg s2 → CanBlock st T Ac s2 t →
      (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) →
      L.ksb s2 = L.ksb s → ¬ Blocked (L.mem s2 (stA (L.idleW s2))) →
      (do
        let st0 ← obj.Ep.state st e s2
        if st0 = obj.EP_IDLE then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else if st0 = obj.EP_RECV then do
          let s3 ← endpoint.wait_for_sender st s2 t e blocking reply
          ok (s3, a2)
        else endpoint.receive_from_sender st ar s2 a2 t e reply) ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
    intro s2 a2 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 kb2 ib2
    step with obj.Ep.state.spec as ⟨v, hv⟩
    split
    · rename_i h0
      refine WP.spec_bind (endpoint.wait_for_sender.inv s2 t e blocking reply Q2 R2 h2 hB2 hX2 hS2 hSg2 ht
        (fun _ => hc2) hH (Or.inl (by rw [← hv, h0, ep_idle_val])) hr2) fun s3 hh => ?_
      exact (WP.spec_ok _).2 ⟨⟨Q2, R2, hh.1⟩, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩
    · split
      · rename_i _ h0
        refine WP.spec_bind (endpoint.wait_for_sender.inv s2 t e blocking reply Q2 R2 h2 hB2 hX2 hS2 hSg2 ht
          (fun _ => hc2) hH (Or.inr (by rw [← hv, h0, ep_recv_val'])) hr2) fun s3 hh => ?_
        exact (WP.spec_ok _).2 ⟨⟨Q2, R2, hh.1⟩, hh.2.1, hh.2.2.1, hh.2.2.2.1, hh.2.2.2.2⟩
      · rename_i h01 h02
        exact hrfs s2 a2 reply ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2⟩ hc2 hr2 kb2 ib2
          (fun e0 => h01 (by rw [hv, e0, ep_idle_val])) (fun e0 => h02 (by rw [hv, e0, ep_recv_val']))
  -- the bound notification's SC
  have mid : ∀ (i : U64), (if blocking then notification.maybe_return_sched_context st s1 i t else ok s1)
      ⦃ s2 => ∃ Q2 R2, SchedQueuesInv st T Cs Ω H s2 Q2 R2 ∧ BoundInv st T Ac s2 ∧
        XInv st T Cs Ω Sg Rp Scs Nt Z s2 ∧ SCsOK st T Ω Sg Scs Z Ac s2 ∧ SgOK st Ω Sg s2 ∧ CanBlock st T Ac s2 t ∧
        (reply ≠ 0#u64 → reply ∈ Rp ∧ (L.mem s2 (rTcbA reply) = 0#u64 ∨ L.mem s2 (rTcbA reply) = t)) ∧
        L.ksb s2 = L.ksb s ∧ ¬ Blocked (L.mem s2 (stA (L.idleW s2))) ⦄ := by
    intro i
    split
    · refine WP.spec_mono (notification.maybe_return_sched_context.inv s1 i t Q R h1 hB1 hX1 hS1 hSg1 ht
        ⟨hc1.nq, hc1.nr, hc1.na⟩ (by rw [hi1]; exact hidle)) fun s2 hh => ?_
      obtain ⟨⟨Q2, R2, h2⟩, hB2, hX2, hS2, hSg2, q2, st2, na2, ii2, rt2, sa2, ks2, sc2⟩ := hh
      refine ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc1.mrsc q2 st2 na2 ii2 sc2, fun hn => ?_, ks2.trans kb1, ?_⟩
      · obtain ⟨r1, r2⟩ := hr1 hn
        rw [rt2 _ r1]; exact ⟨r1, r2⟩
      · rw [ii2, sa2 (L.idleW s1) h1.idleT]; exact ib1
    · exact (WP.spec_ok _).2 ⟨Q, R, h1, hB1, hX1, hS1, hSg1, hc1, hr1, kb1, ib1⟩
  step with obj.Tcb.bound_ntfn.val as ⟨i, ei⟩
  split
  · rename_i hi0
    step with obj.Ntfn.state.spec as ⟨v1, hv1⟩
    split
    · rename_i hva
      exact hcs s1 a1 i ⟨⟨Q, R, h1⟩, hB1, hX1, hS1, hSg1⟩ hc1 ei (by simpa using hi0)
        (by rw [← hv1, hva]; unfold obj.NTFN_ACTIVE; rfl)
    · refine WP.spec_bind (mid i) ?_
      rintro s2 ⟨Q2, R2, h2, hB2, hX2, hS2, hSg2, hc2, hr2, kb2, ib2⟩
      exact tail s2 a1 Q2 R2 h2 hB2 hX2 hS2 hSg2 hc2 hr2 kb2 ib2
  · try simp only [Aeneas.Std.bind_ok]
    exact tail s1 a1 Q R h1 hB1 hX1 hS1 hSg1 hc1 hr1 kb1 ib1

end

end Fl4Proofs.P1
