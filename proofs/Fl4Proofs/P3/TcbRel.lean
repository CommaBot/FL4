/-
P3 (DESIGN.md §9): **one TCB relation for the notification and endpoint
subsystems**, and two theorems against the combined relation.

`TcbRel R m t x` relates the TCB at `t` once for both subsystems: it is
`TcbRelE` (state code, IPC payloads, all registers, priority, fault, bound
notification) together with the block object of `BlockedOnNotification`;
`TcbRel1` (notifications) and `TcbRelE` (endpoints) are its projections
(`TcbRel.to1`, `TcbRel.toE`), and it is built from them (`TcbRel.mk'`).

`CombRel N T E R B m σ := NtfnStateRel N T m σ ∧ EpStateRel T E R B m σ`,
which is the per-subsystem object relations over the shared `TcbRel`
(`CombRel.tcbRel`). The other subsystems are `SR`, now with a stability
hypothesis that covers both write sets (`CombHyps`); `SR` no longer holds
either IPC relation, so the shared TCB words (state, block object, the
badge register RDI, priority) need no stability assumption.

Re-derived against `CombRel`:
* `receive_ipc_poll_comb` (endpoint; writes the shared badge register),
* `receive_signal_poll_comb` (notification; the same register),
* `send_ipc_block_comb` (endpoint; writes the shared state and block words
  and the `Ep` links the notification queues also use).
-/
import Fl4Proofs.P3.Ep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

/-! ## The shared TCB relation -/

section
open Fl4Spec

/-- The TCB at `t` and the spec's TCB `x`, for both IPC subsystems. -/
def TcbRel (R : Set U64) (m : U64 → U64) (t : U64) (x : Tcb) : Prop :=
  TcbRelE R m t x ∧ ∀ n, x.tcbState = .blockedOnNotification n → (m (tBlockA t)).bv = n

theorem TcbRel.toE {R : Set U64} {m : U64 → U64} {t : U64} {x : Tcb} (h : TcbRel R m t x) : TcbRelE R m t x := h.1

theorem TcbRel.to1 {R : Set U64} {m : U64 → U64} {t : U64} {x : Tcb} (h : TcbRel R m t x) : TcbRel1 m t x :=
  ⟨h.1.st, h.2, by rw [badgeRegA_eq_regA]; exact h.1.regs _, h.1.prio⟩

theorem TcbRel.mk' {R : Set U64} {m : U64 → U64} {t : U64} {x : Tcb} (h1 : TcbRel1 m t x) (hE : TcbRelE R m t x) :
    TcbRel R m t x := ⟨hE, h1.blk⟩

end

/-- The combined relation of the two IPC subsystems. -/
def CombRel {Z : Type} (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (m : U64 → U64) (σ : Fl4Spec.State Z) :
    Prop :=
  NtfnStateRel N T m σ ∧ EpStateRel T E R B m σ

theorem CombRel.tcbRel {Z : Type} {N T E R : Set U64} {B} {m : U64 → U64} {σ : Fl4Spec.State Z}
    (h : CombRel N T E R B m σ) : ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ TcbRel R m t x := by
  intro t ht
  obtain ⟨x, hk, hx⟩ := h.2.tcb t ht
  obtain ⟨y, hk', hy⟩ := h.1.tcb t ht
  rw [hk] at hk'; cases hk'
  exact ⟨x, hk, TcbRel.mk' hy hx⟩

/-- `CombRel` is the object relations over the shared `TcbRel`. -/
theorem CombRel.iff {Z : Type} {N T E R : Set U64} {B} {m : U64 → U64} {σ : Fl4Spec.State Z} :
    CombRel N T E R B m σ ↔
      (∀ n ∈ N, ∃ x, σ.kheap n.bv = some (.notification x) ∧ NtfnRel1 m T n x) ∧
      (∀ e ∈ E, ∃ x, σ.kheap e.bv = some (.endpoint x) ∧ EpObjRel m T e x) ∧
      (∀ r ∈ R, ∃ x, σ.kheap r.bv = some (.reply x) ∧ x.replyTcb = optRef (m (rTcbA r))) ∧
      (∀ wp ∈ B, (m wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2) ∧
      (∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ TcbRel R m t x) := by
  constructor
  · intro h
    exact ⟨h.1.ntfn, h.2.ep, h.2.reply, h.2.buf, h.tcbRel⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨h1, fun t ht => ?_⟩, ⟨h2, h3, fun t ht => ?_, h4⟩⟩
    · obtain ⟨x, hk, hx⟩ := h5 t ht; exact ⟨x, hk, hx.to1⟩
    · obtain ⟨x, hk, hx⟩ := h5 t ht; exact ⟨x, hk, hx.toE⟩

/-- Placement for both subsystems: notifications do not overlap endpoints,
replies or mapped buffer words either. -/
structure CPlaced (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) : Prop where
  n : NPlaced T N
  e : EPlaced T E R B
  ne : ∀ n ∈ N, ∀ e ∈ E, n.val + 64 ≤ e.val ∨ e.val + 16 ≤ n.val
  nr : ∀ n ∈ N, ∀ r ∈ R, n.val + 64 ≤ r.val ∨ r.val + 32 ≤ n.val
  nb : ∀ n ∈ N, ∀ wp ∈ B, wp.1.val < n.val ∨ n.val + 64 ≤ wp.1.val

section Hyps
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- What the combined proofs assume of the other subsystems' relation `SR`:
stability under both IPC subsystems' writes and spec steps, and
`schedule_tcb` ↔ `set_thread_state_act` keeping both footprints. -/
structure CombHyps (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  stable : ∀ s s' σ σ', SR s σ → WritesIn st s s' (fun a => NWrite N T a ∨ EWrite T E R B a) →
    (NtfnStep σ σ' ∨ EpStep σ σ') → SR s' σ'
  scheduleTcb : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => FootEq T E R B (L.mem s) (L.mem s') ∧
      Notif.FootEq N T (L.mem s) (L.mem s') ∧ SR s' (stsAct σ t.bv) ⦄

theorem CombHyps.epHyps {N T E R : Set U64} {B} {SR : S → Fl4Spec.State Unit → Prop} (h : CombHyps st N T E R B SR) :
    EpHyps st T E R B SR :=
  ⟨fun s s' σ σ' h1 h2 h3 => h.stable s s' σ σ' h1 (h2.mono fun _ h => Or.inr h) (Or.inr h3),
   fun s σ t h1 h2 h3 => WP.spec_mono (h.scheduleTcb s σ t h1 h2 h3) fun _ h => ⟨h.1, h.2.2⟩⟩

end Hyps

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

theorem receive_ipc_poll_comb (hC : CombHyps st N T E R B SR) (hP : CPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hbn : xt.tcbBoundNotification = none)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x) (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) false rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hR := hRC.2
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [CanBlock] at hc
  have hspec0 := receiveIpc_noSend b rights false (replyArg_spec hP.e hR hrc) hkt hbn hk hns
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hP.e s σ hR ht hkt Fl4Spec.badge_register 0#u64
  obtain ⟨hN1, -, -⟩ := set_badge_reg_rel (L := L) hP.n hRC.1 ht hkt 0#u64
  rw [badgeRegA_eq_regA] at hN1
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register (0#u64 : U64).bv)))}, False) := by
    rw [hspec0]
    unfold Fl4Spec.receiveIpcBlocked Fl4Spec.doNbrecvFailedTransfer
    rw [if_neg (by simp), nd_bind_one (asUser_setRegister_eq _ _ hkt)]
    rfl
  have key : (do
      let s3 ← endpoint.wait_for_sender st s t e false rv
      ok (s3, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) false rc' σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← regIdx_badge]
    step as ⟨s1', h1⟩
    subst h1
    exact ⟨_, hspec, ⟨hN1, hR1⟩, hC.stable _ _ _ _ hSR (hW1.mono fun _ h => Or.inr h) (Or.inr hS1)⟩
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 false rc rc' rv hrc hbound
  step as ⟨st1, hst1⟩
  rw [hst1, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    exact key
  | recvEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact key
  | sendEP q => exact absurd rfl (hns q)


theorem receive_signal_poll_comb (hC : CombHyps st N T E R B SR) (hP : CPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SR s σ) {t : U64} (ht : t ∈ T) {n : U64} (hn : n ∈ N)
    {x : Fl4Spec.Notification} (hk : σ.kheap n.bv = some (.notification x))
    (hna : ∀ b, x.ntfnObj ≠ .activeNtfn b) (cb : Fl4Spec.Badge) (cr : Fl4Spec.CapRights) :
    notification.receive_signal st ar s a t n false ⦃ r =>
      r.2 = a ∧ ∃ σ', Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) false σ =
        ({((), σ')}, False) ∧ CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hR := hRC.1
  have hx := hR.at_ntfn hn hk
  obtain ⟨xt, hkt, -⟩ := hR.tcb t ht
  have hspec : Fl4Spec.receiveSignal (Z := Unit) t.bv (.notificationCap n.bv cb cr) false σ =
      ({((), updK σ t.bv (.tcb (setReg xt Fl4Spec.badge_register 0)))}, False) := by
    rw [receiveSignal_cap hk]
    cases h : x.ntfnObj
    all_goals first | exact absurd h (hna _) | skip
    all_goals
      dsimp only
      unfold Fl4Spec.receiveSignalBlocked Fl4Spec.doNbrecvFailedTransfer
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [nd_bind_one (asUser_setRegister_eq _ _ hkt)]
      rfl
  have hst : stOf (L.mem s) n = obj.NTFN_IDLE ∨ stOf (L.mem s) n = obj.NTFN_WAITING := by
    have := hx.obj
    cases h : x.ntfnObj with
    | idleNtfn => exact Or.inl (stOf_idle (T := T) (h ▸ this) rfl)
    | waitingNtfn q => exact Or.inr (stOf_waiting (T := T) (h ▸ this) rfl)
    | activeNtfn b => exact absurd h (hna b)
  obtain ⟨hR', hW, hS⟩ := set_badge_reg_rel hP.n hR ht hkt 0#u64
  obtain ⟨hE', -, -⟩ := write_reg_rel hP.e s σ hRC.2 ht hkt Fl4Spec.badge_register 0#u64
  rw [← badgeRegA_eq_regA] at hE'
  have hS' := hC.stable _ _ _ _ hSR (hW.mono fun _ h => Or.inl h) (Or.inl hS)
  unfold notification.receive_signal
  step
  rw [st_post, epState_eq] at *
  rcases hst with hst | hst
  · simp only [hst, ↓reduceIte, Bool.false_eq_true]
    step
    subst s1_post
    exact ⟨_, hspec, ⟨hR', hE'⟩, hS'⟩
  · simp only [hst, ntfn_consts.1, ntfn_consts.2.1, show (1#u64 : U64) ≠ 0#u64 by decide, ↓reduceIte,
      Bool.false_eq_true]
    step
    subst s1_post
    exact ⟨_, hspec, ⟨hR', hE'⟩, hS'⟩



/-! ## Notification relation under endpoint writes -/

theorem nwords_val {n : U64} (hn : NAddr n) :
    (epHeadA n).val = n.val ∧ (epTSA n).val = n.val + 8 ∧ (nBadgeA n).val = n.val + 16 ∧
      (nBoundA n).val = n.val + 24 ∧ (nScA n).val = n.val + 32 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [epHeadA_eq, nfield_val hn (by simp)]; rfl
  · rw [epTSA_eq, nfield_val hn (by simp)]; rfl
  · rw [nBadgeA_eq, nfield_val hn (by simp)]; rfl
  · rw [nBoundA_eq, nfield_val hn (by simp)]; rfl
  · rw [nScA_eq, nfield_val hn (by simp)]; rfl

/-- Words of the notifications agree when memory agrees on every aligned
word with value `P`, and `P` holds for every notification word. -/
theorem nwordsEq_of {m m' : U64 → U64} {n : U64} (hn : NAddr n) (P : Nat → Prop)
    (hA : ∀ a, Aligned a → P a.val → m' a = m a) (hPn : ∀ k, k < 40 → P (n.val + k)) : NWordsEq m m' n := by
  obtain ⟨v1, v2, v3, v4, v5⟩ := nwords_val hn
  have al : ∀ K : U64, K.val < 40 → K.val % 8 = 0 → Aligned (core.num.U64.wrapping_add n K) :=
    fun K h1 h2 => nfield_aligned hn (by omega) h2
  refine ⟨hA _ ?_ (by rw [v1]; simpa using hPn 0 (by omega)), hA _ ?_ (by rw [v2]; exact hPn 8 (by omega)),
    hA _ ?_ (by rw [v3]; exact hPn 16 (by omega)), hA _ ?_ (by rw [v4]; exact hPn 24 (by omega)),
    hA _ ?_ (by rw [v5]; exact hPn 32 (by omega))⟩
  · rw [epHeadA_eq]; exact al _ (by simp) (by simp)
  · rw [epTSA_eq]; exact al _ (by simp) (by simp)
  · rw [nBadgeA_eq]; exact al _ (by simp) (by simp)
  · rw [nBoundA_eq]; exact al _ (by simp) (by simp)
  · rw [nScA_eq]; exact al _ (by simp) (by simp)

theorem tfieldsEq_of {m m' : U64 → U64} {y : U64} (hy : TcbAddr y) (P : Nat → Prop)
    (hA : ∀ a, Aligned a → P a.val → m' a = m a)
    (h1 : P (y.val + 3328)) (h2 : P (y.val + 3336)) (h3 : P (y.val + 256)) (h4 : P (y.val + 3448)) :
    TFieldsEq m m' y := by
  refine ⟨hA _ (a_st hy).1 (by rw [val_st hy]; exact h1), hA _ (a_blk hy).1 (by rw [val_blk hy]; exact h2),
    hA _ ?_ ?_, hA _ (a_prio hy).1 (by rw [val_prio hy]; exact h4)⟩
  · rw [badgeRegA_eq_regA]; exact (a_reg hy _).1
  · rw [badgeRegA_eq, tw_val hy (by simp)]; exact h3

theorem tlinksEq_of {m m' : U64 → U64} {y : U64} (hy : TcbAddr y) (P : Nat → Prop)
    (hA : ∀ a, Aligned a → P a.val → m' a = m a) (h1 : P (y.val + 3496)) (h2 : P (y.val + 3504)) :
    TLinksEq m m' y :=
  ⟨hA _ (a_prev hy).1 (by rw [val_prev hy]; exact h2), hA _ (a_next hy).1 (by rw [val_next hy]; exact h1)⟩

/-- Writing fields `[3328, 3360)` of the TCB `t` (state, block object,
block badge, block flags, reply object): the notification relation, for a
`t` in no notification queue. -/
theorem ntfn_upd_fields {Z : Type} (hP : CPlaced N T E R B) {m m' : U64 → U64} {σ : Fl4Spec.State Z}
    (hR : NtfnStateRel N T m σ) {t : U64} (ht : t ∈ T) (x' : Fl4Spec.Tcb)
    (hA : ∀ a, Aligned a → (a.val < t.val + 3328 ∨ t.val + 3368 ≤ a.val) → m' a = m a)
    (hq : ∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue)
    (hx : TcbRel1 m' t x') : NtfnStateRel N T m' (updK σ t.bv (.tcb x')) := by
  have hta := hP.n.tcb t ht
  let P : Nat → Prop := fun v => v < t.val + 3328 ∨ t.val + 3368 ≤ v
  refine hR.upd_tcb ht x' (fun n hn => nwordsEq_of (hP.n.ntfn n hn) P hA fun k hk => ?_)
    (fun y hy hne => tfieldsEq_of (hP.n.tcb y hy) P hA ?_ ?_ ?_ ?_)
    (fun y hy => tlinksEq_of (hP.n.tcb y hy) P hA ?_ ?_) (Or.inl hq) hx
  · have := hP.n.disj n hn t ht; show _ ∨ _; omega
  all_goals
    show _ ∨ _
    first
    | (have := tcb_disj hP.e ht hy hne; omega)
    | (by_cases e : y = t
       · subst e; omega
       · have := tcb_disj hP.e ht hy e; omega)

/-- The queue operations on the endpoint `e` keep the notification relation
when none of the TCBs `W` whose links they write is blocked on a
notification. -/
theorem ntfn_frame_ep {Z : Type} (hP : CPlaced N T E R B) {m m' : U64 → U64} {σ σ' : Fl4Spec.State Z}
    (hR : NtfnStateRel N T m σ) {e : U64} (he : e ∈ E) {W : List U64}
    (hW : ∀ w ∈ W, w ∈ T ∧ (m (tStA w)).val ≠ 6) (hA : QAgree T e W m m') (hk : Notif.KView σ σ') :
    NtfnStateRel N T m' σ' := by
  let P : Nat → Prop := fun v => ¬ (v = e.val ∨ v = e.val + 8) ∧ ¬ ∃ w ∈ W, (v = w.val + 3496 ∨ v = w.val + 3504)
  have hA' : ∀ a, Aligned a → P a.val → m' a = m a := fun a ha h => hA a ha h
  have hfield : ∀ y ∈ T, ∀ k, 256 ≤ k → k < 3456 → P (y.val + k) := by
    intro y hy k h1 h2
    refine ⟨?_, ?_⟩
    · have := hP.e.et e he y hy; omega
    · rintro ⟨w, hw, hv⟩
      by_cases ew : w = y
      · subst ew; omega
      · have := tcb_disj hP.e (hW w hw).1 hy (Ne.symm ew); omega
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hkx, hx⟩ := hR.ntfn n hn
    refine ⟨x, hk.1 _ _ hkx, hx.frame (nwordsEq_of (hP.n.ntfn n hn) P hA' fun k hk' => ?_) fun y hy hq => ?_⟩
    · refine ⟨?_, ?_⟩
      · have := hP.ne n hn e he; omega
      · rintro ⟨w, hw, hv⟩; have := hP.n.disj n hn w (hW w hw).1; omega
    · obtain ⟨-, h6, hb⟩ := hx.obj.blocked hq
      have hya := hP.n.tcb y hy
      refine ⟨hA' _ (a_st hya).1 (by rw [val_st hya]; exact hfield y hy _ (by omega) (by omega)),
        hA' _ (a_blk hya).1 (by rw [val_blk hya]; exact hfield y hy _ (by omega) (by omega)),
        tlinksEq_of hya P hA' ?_ ?_⟩ <;>
      · refine ⟨?_, ?_⟩
        · have := hP.e.et e he y hy; omega
        · rintro ⟨w, hw, hv⟩
          by_cases ew : w = y
          · subst ew; exact (hW w hw).2 h6
          · have := tcb_disj hP.e (hW w hw).1 hy (Ne.symm ew); omega
  · obtain ⟨x, hkx, hx⟩ := hR.tcb t ht
    obtain ⟨y, hky, e1, e2, e3⟩ := hk.2 _ _ hkx
    have hta := hP.n.tcb t ht
    have hx' := hx.frame (tfieldsEq_of hta P hA' (hfield t ht _ (by omega) (by omega))
      (hfield t ht _ (by omega) (by omega)) (hfield t ht _ (by omega) (by omega))
      (hfield t ht _ (by omega) (by omega)))
    exact ⟨y, hky, ⟨e1 ▸ hx'.st, fun n hn => hx'.blk n (e1 ▸ hn), e2 ▸ hx'.badge, e3 ▸ hx'.prio⟩⟩

/-- **Blocking send**, against the combined relation: the notification
relation is kept too (the thread's state and block words are shared, and the
`Ep` links written belong to TCBs that are on no notification queue). -/
theorem send_ipc_block_comb (hC : CombHyps st N T E R B SR) (hP' : CPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (call : Bool) (badge : U64) (g gr d : Bool) :
    endpoint.send_ipc st ar s a true call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hH := hC.epHyps
  have hP := hP'.e
  have hR := hRC.2
  have hN := hRC.1
  have hqn := not_member hN ht hkt hnn
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hq := not_queued hR ht hkt hnb
  have htq : t.bv ∉ x.epQueue := hq e he x hk
  set d' : Fl4Spec.SenderPayload :=
    { senderBadge := badge.bv, senderCanGrant := g, senderCanGrantReply := gr, senderIsCall := call }
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnSend e.bv d' }
  set σ1 := updK σ t.bv (.tcb x1)
  set f := ((if g then endpoint.FLAG_GRANT else 0#u64) ||| (if gr then endpoint.FLAG_GRANT_REPLY else 0#u64)) |||
      (if call then endpoint.FLAG_CALL else 0#u64) with hf
  set s4 := L.wr (L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_SEND) (tBlockA t) e) (tBadgeA t) badge)
      (tFlagsA t) f
  obtain ⟨hA4, r1, r2, r3, r4, hW4⟩ := block_send_writes (L := L) hP s ht e badge f
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_badge hta; have v4 := val_flags hta
  have hR1 : EpStateRel T E R B (L.mem s4) σ1 := by
    refine hR.upd_tcb hP ht x1 (hA4.mono fun b hb => ?_) (Or.inl hq) ?_
    · have n1 : b.val ≠ (tStA t).val := fun h => hb.2 (TF.of_val (a_st hta).2 h)
      have n2 : b.val ≠ (tBlockA t).val := fun h => hb.2 (TF.of_val (a_blk hta).2 h)
      have n3 : b.val ≠ (tBadgeA t).val := fun h => hb.2 (TF.of_val (a_badge hta).2 h)
      have n4 : b.val ≠ (tFlagsA t).val := fun h => hb.2 (TF.of_val (a_flags hta).2 h)
      omega
    refine hxt.restate hta (hA4.mono fun b hb => ?_) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · have := hb.2; omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_SEND; rfl
    · intro e' h; simp only [x1, Fl4Spec.epBlocked, Option.some.injEq] at h; subst h; rw [r2]
    · intro e' d'' h
      simp only [x1, Fl4Spec.ThreadState.blockedOnSend.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨by rw [r3], by rw [r4, hf, flags_eq]; rfl⟩
    · intro e' r d'' h; simp [x1] at h
    · intro r h; simp [x1] at h
  have hN1 : NtfnStateRel N T (L.mem s4) σ1 := by
    have hxt1 := hN.at_tcb ht hkt
    have g4 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3360 ≤ b.val) → L.mem s4 b = L.mem s b :=
      fun b hb hv => hA4 b hb (by omega)
    refine ntfn_upd_fields hP' hN ht x1 (fun b hb hv => hA4 b hb ?_) hqn ⟨?_, ?_, ?_, ?_⟩
    · omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_SEND; rfl
    · intro n h; simp [x1] at h
    · show (L.mem s4 (badgeRegA t)).bv = badgeOf xt
      rw [g4 _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hxt1.badge
    · show (L.mem s4 (prioA t)).val = xt.tcbPriority.toNat
      rw [g4 _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hxt1.prio
  have hS1 : EpStep σ σ1 := EpStep.tcb hkt _ xt.tcbArch
  have hSR1 := hH.stable _ _ _ _ hSR hW4 hS1
  set σ2 := stsAct σ1 t.bv
  have hnt : e.bv ≠ t.bv := kheap_ne hk hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  have hspec : Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ =
      Fl4Spec.tcbEpAppend t.bv e.bv false σ2 := by
    rw [sendIpc_block hk hc]
    unfold Fl4Spec.sendIpcBlocked
    rw [nd_bind_one (setThreadState_eq _ hkt)]
  have key : (do
      let s1 ← obj.Tcb.set_state st t s sched.TS_BLOCKED_ON_SEND
      let s2 ← obj.Tcb.set_block_obj st t s1 e
      let s3 ← obj.Tcb.set_block_badge st t s2 badge
      let i ← ok (if g = true then endpoint.FLAG_GRANT else 0#u64)
      let i1 ← ok (if gr = true then endpoint.FLAG_GRANT_REPLY else 0#u64)
      let i2 ← lift (i ||| i1)
      let i3 ← ok (if call = true then endpoint.FLAG_CALL else 0#u64)
      let f ← lift (i2 ||| i3)
      let s4 ← obj.Tcb.set_block_flags st t s3 f
      let s5 ← sched.schedule_tcb st s4 t
      let s6 ← endpoint.ep_append st s5 e t obj.EP_SEND
      ok (s6, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) true call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    step; step; step
    simp only [lift]
    step
    subst s1_post s2_post s3_post i2_post
    refine WP.spec_bind (hC.scheduleTcb _ σ1 t hR1 hSR1 ht) ?_
    rintro s5 ⟨hf5, hfN5, hS5⟩
    have hN2 : NtfnStateRel N T (L.mem s5) σ2 := hN1.frame hP'.n hfN5 (Notif.KView.stsAct _ _)
    have hR2 : EpStateRel T E R B (L.mem s5) σ2 := hR1.frame hP hf5 (KView.stsAct' _ _)
    have hpr : ∀ y ∈ T, L.mem s5 (prioA y) = L.mem s (prioA y) := by
      intro y hy
      have hya := hP.tcb y hy
      rw [hf5 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩)))]
      refine hA4 _ (a_prio hya).1 ?_
      have := val_prio hya
      by_cases eyt : y = t
      · subst eyt; omega
      · have := tcb_disj hP ht hy eyt; omega
    have hsort5 := sorted_transfer hP.tcb hx (hR2.at_ep he hk2) hpr hsort
    have htst : (L.mem s5 (tStA t)).val = if false = true then 3 else 4 := by
      rw [hf5 _ (a_st hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_st hta).2⟩))), r1]
      unfold sched.TS_BLOCKED_ON_SEND; rfl
    have htb : L.mem s5 (tBlockA t) = e := by
      rw [hf5 _ (a_blk hta).1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_blk hta).2⟩))), r2]
    have happ := ep_append_rel hH hP s5 σ2 hR2 hS5 ht hkt2 he hk2 false hc htq htst htb hsort5
    simp only [Bool.false_eq_true, ↓reduceIte] at happ
    obtain ⟨xs, hQ, hxs, hB⟩ := (hR2.at_ep he hk2).queue
    have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
    have hqa := WP.spec_mono (ep_append_full hP s5 he t obj.EP_SEND xs hQ ht htxs) fun _ h => h.2.2.1
    refine WP.spec_bind (WP.spec_and happ hqa) ?_
    rintro s6 ⟨⟨σ', hσ', hR', hS'⟩, hQA⟩
    -- the spec's append only changes the endpoint
    have hq2 : ∀ y ∈ x.epQueue, ∃ z, σ2.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ2 y := by
      intro y hy
      rw [hxs] at hy
      obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
      obtain ⟨z, hz, -⟩ := hR2.tcb y' (hQ.mem y' hy'x)
      exact ⟨z, hz, by simp [prioOf, hz]⟩
    rw [tcbEpAppend_eq hk2 hkt2 (prioOf σ2) hq2] at hσ'
    have hσe : σ' = updK σ2 e.bv (.endpoint (Fl4Spec.updateEpQueue x
        (specIns x.epQueue (prioOf σ2) x1.tcbPriority t.bv) false)) := by
      have := congrArg Prod.fst hσ'
      simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
      exact this.symm
    have hkv : Notif.KView σ2 σ' := by
      rw [hσe]
      refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
      · have : p ≠ e.bv := by intro h'; rw [h', hk2] at h; cases h
        simp [this, h]
      · have : p ≠ e.bv := by intro h'; rw [h', hk2] at h; cases h
        simp [this, h]
    have hW : ∀ w ∈ t :: xs, w ∈ T ∧ (L.mem s5 (tStA w)).val ≠ 6 := by
      intro w hw
      rcases List.mem_cons.1 hw with rfl | hw
      · exact ⟨ht, by rw [htst]; simp⟩
      · exact ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
    have hN3 := ntfn_frame_ep hP' hN2 he hW hQA hkv
    simp only [WP.spec_ok]
    exact ⟨by simp, σ', by rw [hspec, tcbEpAppend_eq hk2 hkt2 (prioOf σ2) hq2, hσe], ⟨hN3, hR'⟩, hS'⟩
  unfold endpoint.send_ipc
  step
  rw [st_post, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    simp only [↓reduceIte, flag_ite]
    exact key
  | sendEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.1.symm]
    simp only [↓reduceIte, flag_ite]
    exact key
  | recvEP q => simp [CanBlock] at hc


end

end

end Fl4Proofs.P3.Endp
