/-
P3 (DESIGN.md §9), IPC: **the merged notification and endpoint relation**
(the plan of Ep.lean's note "Merging the subsystem relations").

`NtfnStateRel` (`TcbRel1`) and `EpStateRel` (`TcbRelE`) both relate the TCB
state word, the block-object word, the badge register and the priority. Here
the TCB part is one relation owned by neither subsystem:

* `TcbRel R m t x`: the state code `tsCode`, the block object for every
  blocked state (endpoint and notification), the IPC payloads, all
  registers, priority, fault, bound notification, and the SC word
  (`tcbSchedContext ↔ scA`). `TcbRel.toN` / `TcbRel.toE` give `TcbRel1` /
  `TcbRelE`, so the existing proofs keep their statements.
* The object parts stay per subsystem: `NtfnRel1` (notifications),
  `EpObjRel` (endpoints), replies' TCB word, the mapped IPC-buffer words.
* `IpcRel N T E R B m σ`: all of them (`IpcRel.toN` / `IpcRel.toE`, and
  `IpcRel.of` back), with one placement `IPlaced`, one footprint `IFoot`
  (the notification words, `EFoot`, the SC words) and one `IKView`
  (`IpcRel.frame`).
* The updates: `IpcRel.upd_tcb` on the shared part, `upd_ntfn`, `upd_ep`,
  `upd_reply` per object; each keeps both subsystems' parts.
-/
import Fl4Proofs.P3.EpWrite
import Fl4Proofs.P1.QueueSchedStep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

/-! ## The TCB relation -/

section Rel
open Fl4Spec

/-- **The TCB at `t` and the spec's TCB `x`**, for both IPC subsystems. -/
structure TcbRel (R : Set U64) (m : U64 → U64) (t : U64) (x : Tcb) : Prop where
  st : (m (tStA t)).val = tsCode x.tcbState
  blkE : ∀ e, epBlocked x.tcbState = some e → (m (tBlockA t)).bv = e
  blkN : ∀ n, x.tcbState = .blockedOnNotification n → (m (tBlockA t)).bv = n
  send : ∀ e d, x.tcbState = .blockedOnSend e d → (m (tBadgeA t)).bv = d.senderBadge ∧ m (tFlagsA t) = flagsOf d
  recv : ∀ e r d, x.tcbState = .blockedOnReceive e r d → optRef (m (tReplyA t)) = r ∧
    (r ≠ none → m (tReplyA t) ∈ R)
  reply : ∀ r, x.tcbState = .blockedOnReply r → (m (tReplyA t)).bv = r
  regs : ∀ r, (m (regA t (regIdx r))).bv = x.tcbArch.tcbContext.userRegs r
  prio : (m (prioA t)).val = x.tcbPriority.toNat
  fault0 : m (tFaultA t) = 0#u64 ↔ x.tcbFault = none
  faultT : m (tFaultA t) = 5#u64 ↔ ∃ b, x.tcbFault = some (.timeout b)
  bound : x.tcbBoundNotification = optRef (m (tBoundA t))
  faultR : FaultRel m t x.tcbFault
  sc : x.tcbSchedContext = optRef (m (scA t))

variable {R : Set U64} {m : U64 → U64} {t : U64} {x : Tcb}

/-- The endpoint subsystem's view. -/
theorem TcbRel.toE (h : TcbRel R m t x) : TcbRelE R m t x :=
  ⟨h.st, h.blkE, h.send, h.recv, h.reply, h.regs, h.prio, h.fault0, h.faultT, h.bound, h.faultR⟩

/-- The notification subsystem's view. -/
theorem TcbRel.toN (h : TcbRel R m t x) : TcbRel1 m t x :=
  ⟨h.st, h.blkN, by rw [badgeRegA_eq_regA]; exact h.regs _, h.prio⟩

/-- Both views and the SC word give the relation. -/
theorem TcbRel.of (hE : TcbRelE R m t x) (hN : TcbRel1 m t x) (hsc : x.tcbSchedContext = optRef (m (scA t))) :
    TcbRel R m t x :=
  ⟨hE.st, hE.blk, hN.blk, hE.send, hE.recv, hE.reply, hE.regs, hE.prio, hE.fault0, hE.faultT, hE.bound,
    hE.faultR, hsc⟩

end Rel

/-- The words of the TCB at `t` the relation reads (not the `Ep` links): the
endpoint fields and the SC word. -/
def TFI (t a : U64) : Prop := TF t a ∨ a = scA t

theorem TcbRel.frame {R : Set U64} {m m' : U64 → U64} {t : U64} {x : Fl4Spec.Tcb} (ht : TcbAddr t)
    (h : TcbRel R m t x) (he : Agree m m' (TFI t)) : TcbRel R m' t x := by
  have hE := h.toE.frame ht (fun a ha hf => he a ha (Or.inl hf))
  have hN := h.toN.frame ⟨he _ (a_st ht).1 (Or.inl (a_st ht).2), he _ (a_blk ht).1 (Or.inl (a_blk ht).2),
    by rw [badgeRegA_eq_regA]; exact he _ (a_reg ht _).1 (Or.inl (a_reg ht _).2),
    he _ (a_prio ht).1 (Or.inl (a_prio ht).2)⟩
  exact TcbRel.of hE hN (by rw [he _ (scA_aligned ht) (Or.inr rfl)]; exact h.sc)

/-! ## Placement, the relation, footprint and view -/

/-- **The ghost sets of both subsystems**: their own placements and the
notifications apart from the endpoints, replies and buffer words. -/
structure IPlaced (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) : Prop where
  n : NPlaced T N
  e : EPlaced T E R B
  ne : ∀ n ∈ N, ∀ e ∈ E, n.val + 64 ≤ e.val ∨ e.val + 16 ≤ n.val
  nr : ∀ n ∈ N, ∀ r ∈ R, n.val + 64 ≤ r.val ∨ r.val + 32 ≤ n.val
  nb : ∀ n ∈ N, ∀ wp ∈ B, wp.1.val < n.val ∨ n.val + 64 ≤ wp.1.val

section Rel2
open Fl4Spec

/-- **The IPC state relation**: TCBs (`TcbRel`), notifications, endpoints,
replies and the mapped IPC-buffer words. -/
structure IpcRel {Z : Type} (N T E R : Set U64) (B : Set (U64 × Word)) (m : U64 → U64) (σ : State Z) :
    Prop where
  tcb : ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ TcbRel R m t x
  ntfn : ∀ n ∈ N, ∃ x, σ.kheap n.bv = some (.notification x) ∧ NtfnRel1 m T n x
  ep : ∀ e ∈ E, ∃ x, σ.kheap e.bv = some (.endpoint x) ∧ EpObjRel m T e x
  reply : ∀ r ∈ R, ∃ x, σ.kheap r.bv = some (.reply x) ∧ x.replyTcb = optRef (m (rTcbA r))
  buf : ∀ wp ∈ B, (m wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2

variable {Z : Type} {N T E R : Set U64} {B : Set (U64 × Word)} {m : U64 → U64} {σ : State Z}

theorem IpcRel.toN (h : IpcRel N T E R B m σ) : NtfnStateRel N T m σ :=
  ⟨h.ntfn, fun t ht => let ⟨x, hk, hx⟩ := h.tcb t ht; ⟨x, hk, hx.toN⟩⟩

theorem IpcRel.toE (h : IpcRel N T E R B m σ) : EpStateRel T E R B m σ :=
  ⟨h.ep, h.reply, fun t ht => let ⟨x, hk, hx⟩ := h.tcb t ht; ⟨x, hk, hx.toE⟩, h.buf⟩

/-- Both subsystems' relations and the SC words give the merged one. -/
theorem IpcRel.of (hN : NtfnStateRel N T m σ) (hE : EpStateRel T E R B m σ)
    (hsc : ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbSchedContext = optRef (m (scA t))) :
    IpcRel N T E R B m σ := by
  refine ⟨fun t ht => ?_, hN.ntfn, hE.ep, hE.reply, hE.buf⟩
  obtain ⟨x, hk, hx⟩ := hE.tcb t ht
  obtain ⟨y, hky, hy⟩ := hN.tcb t ht
  rw [hk] at hky; injection hky with hky; injection hky with hky; subst hky
  exact ⟨x, hk, TcbRel.of hx hy (hsc t ht x hk)⟩

theorem IpcRel.sc (h : IpcRel N T E R B m σ) :
    ∀ t ∈ T, ∀ x, σ.kheap t.bv = some (.tcb x) → x.tcbSchedContext = optRef (m (scA t)) := by
  intro t ht x hk
  obtain ⟨y, hky, hy⟩ := h.tcb t ht
  rw [hk] at hky; injection hky with hky; injection hky with hky; subst hky
  exact hy.sc

/-- **The words the relation reads**: the notification words, the endpoint
subsystem's footprint, the TCBs' SC words. -/
def IFoot (N T E R : Set U64) (B : Set (U64 × Word)) (a : U64) : Prop :=
  EFoot T E R B a ∨ (∃ n ∈ N, n.val ≤ a.val ∧ a.val < n.val + 40) ∨ (∃ t ∈ T, a = scA t)

theorem EFoot.ifoot {a : U64} (h : EFoot T E R B a) : IFoot N T E R B a := Or.inl h

theorem NFoot.ifoot (hP : IPlaced N T E R B) {a : U64} (h : NFoot N T a) : IFoot N T E R B a := by
  rcases h with h | ⟨t, ht, h | h | h | h | h | h⟩
  · exact Or.inr (Or.inl h)
  all_goals subst h; have hta := hP.e.tcb t ht
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_st hta).2⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_blk hta).2⟩)))
  · rw [badgeRegA_eq_regA]; exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_reg hta _).2⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl (a_prio hta).2⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (a_next hta).2⟩)))
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr (a_prev hta).2⟩)))

/-- **What the relation reads of the spec's state**: both subsystems' views
and the TCBs' SC. -/
def IKView (σ σ' : State Z) : Prop :=
  Notif.KView σ σ' ∧ Endp.KView σ σ' ∧
    ∀ p x, σ.kheap p = some (.tcb x) → ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbSchedContext = x.tcbSchedContext

theorem IKView.refl (σ : State Z) : IKView σ σ :=
  ⟨Notif.KView.refl σ, Endp.KView.refl σ, fun _ x h => ⟨x, h, rfl⟩⟩

theorem IKView.trans {σ₁ σ₂ σ₃ : State Z} (h₁ : IKView σ₁ σ₂) (h₂ : IKView σ₂ σ₃) : IKView σ₁ σ₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, fun p x h => by
    obtain ⟨y, hy, e⟩ := h₁.2.2 p x h
    obtain ⟨z, hz, f⟩ := h₂.2.2 p y hy
    exact ⟨z, hz, f.trans e⟩⟩

/-- **The relation only reads `IFoot` and `IKView`.** -/
theorem IpcRel.frame {m' : U64 → U64} {σ' : State Z} (hR : IpcRel N T E R B m σ) (hP : IPlaced N T E R B)
    (hm : Agree m m' (IFoot N T E R B)) (hk : IKView σ σ') : IpcRel N T E R B m' σ' := by
  refine IpcRel.of (hR.toN.frame hP.n (fun a ha hf => hm a ha (NFoot.ifoot hP hf)) hk.1)
    (hR.toE.frame hP.e (fun a ha hf => hm a ha (Or.inl hf)) hk.2.1) fun t ht y hky => ?_
  obtain ⟨x, hkx, hx⟩ := hR.tcb t ht
  obtain ⟨y', hky', e⟩ := hk.2.2 _ _ hkx
  rw [hky] at hky'; injection hky' with hky'; injection hky' with hky'; subst hky'
  rw [e, hm _ (scA_aligned (hP.e.tcb t ht)) (Or.inr (Or.inr ⟨t, ht, rfl⟩))]
  exact hx.sc

end Rel2


/-! ## Disjointness -/

section Disj
open Fl4Spec
variable {N T E R : Set U64} {B : Set (U64 × Word)}

/-- The words of the notification at `n`. -/
def NW (n a : U64) : Prop := n.val ≤ a.val ∧ a.val < n.val + 40

theorem scA_val {t : U64} (ht : TcbAddr t) : (scA t).val = t.val + 3464 := by
  unfold scA; rw [tw_val ht (by simp)]; rfl

theorem TFI.range {t a : U64} (ht : TcbAddr t) (h : TFI t a) : t.val + 256 ≤ a.val ∧ a.val ≤ t.val + 3464 := by
  rcases h with h | rfl
  · have := h.range; omega
  · rw [scA_val ht]; omega

theorem TL.range {t a : U64} (h : TL t a) : t.val + 3496 ≤ a.val ∧ a.val ≤ t.val + 3504 := by
  unfold TL at h; omega

theorem nw_words (hP : IPlaced N T E R B) {n : U64} (hn : n ∈ N) :
    NW n (epHeadA n) ∧ NW n (epTSA n) ∧ NW n (nBadgeA n) ∧ NW n (nBoundA n) ∧ NW n (nScA n) := by
  have ha := hP.n.ntfn n hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [epHeadA_eq, NW, nfield_val ha (by simp)]; simp
  · rw [epTSA_eq, NW, nfield_val ha (by simp)]; simp
  · rw [nBadgeA_eq, NW, nfield_val ha (by simp)]; simp
  · rw [nBoundA_eq, NW, nfield_val ha (by simp)]; simp
  · rw [nScA_eq, NW, nfield_val ha (by simp)]; simp

theorem NW.ifoot {n a : U64} (hn : n ∈ N) (h : NW n a) : IFoot N T E R B a := Or.inr (Or.inl ⟨n, hn, h⟩)

/-- A notification word is no field or link of a TCB. -/
theorem NW.not_tcb (hP : IPlaced N T E R B) {n t a : U64} (hn : n ∈ N) (ht : t ∈ T) (h : NW n a) :
    ¬ TFI t a ∧ ¬ TL t a := by
  have := hP.n.disj n hn t ht
  have hta := hP.e.tcb t ht
  refine ⟨fun hf => ?_, fun hl => ?_⟩
  · have := TFI.range hta hf; unfold NW at h; omega
  · have := TL.range hl; unfold NW at h; omega

theorem NW.disj (hP : IPlaced N T E R B) {n n' a : U64} (hn : n ∈ N) (hn' : n' ∈ N) (hne : n' ≠ n)
    (h : NW n' a) : ¬ NW n a := by
  have h1 := (hP.n.ntfn n hn).align
  have h2 := (hP.n.ntfn n' hn').align
  have := val_ne_of_ne hne
  unfold NW at *; omega

/-- A TCB word (field or link) is no field of another TCB. -/
theorem tcb_not_tfi (hP : IPlaced N T E R B) {t y a : U64} (ht : t ∈ T) (hy : y ∈ T) (hne : y ≠ t)
    (ha : TFI y a ∨ TL y a) : ¬ TFI t a ∧ ¬ TL t a := by
  have := tcb_disj hP.e ht hy hne
  have hta := hP.e.tcb t ht
  have hya := hP.e.tcb y hy
  have hr : y.val + 256 ≤ a.val ∧ a.val ≤ y.val + 3504 := by
    rcases ha with ha | ha
    · have := TFI.range hya ha; omega
    · have := TL.range ha; omega
  refine ⟨fun hf => ?_, fun hl => ?_⟩
  · have := TFI.range hta hf; omega
  · have := TL.range hl; omega

theorem TL.not_tfi {t a : U64} (ht : TcbAddr t) (h : TL t a) : ¬ TFI t a := by
  intro hf; have := TFI.range ht hf; have := TL.range h; omega

/-- The SC word of a TCB is in no endpoint-subsystem word. -/
theorem scA_not_efoot (hP : IPlaced N T E R B) {t : U64} (ht : t ∈ T) : ¬ EFoot T E R B (scA t) := by
  have hta := hP.e.tcb t ht
  have hv := scA_val hta
  rintro (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨y, hy, h | h⟩ | ⟨wp, hw, h⟩)
  · have := hP.e.et e he t ht; omega
  · have := hP.e.rt r hr t ht; omega
  · by_cases e : y = t
    · subst e; obtain ⟨-, h2⟩ := h; unfold TOffN at h2; omega
    · exact (tcb_not_tfi hP ht hy e (Or.inl (Or.inl h))).1 (Or.inr rfl)
  · by_cases e : y = t
    · subst e; have := TL.range h; omega
    · exact (tcb_not_tfi hP ht hy e (Or.inr h)).1 (Or.inr rfl)
  · have := hP.e.bt wp hw t ht; rw [← h] at this; omega

/-- An endpoint-subsystem word outside `t`'s fields is not `t`'s SC word. -/
theorem efoot_not_tfi (hP : IPlaced N T E R B) {t a : U64} (ht : t ∈ T) (h : EFoot T E R B a)
    (hnt : ¬ TF t a) : ¬ TFI t a := by
  rintro (hf | rfl)
  · exact hnt hf
  · exact scA_not_efoot hP ht h

theorem ntfn_ne_ep (hP : IPlaced N T E R B) {n e : U64} (hn : n ∈ N) (he : e ∈ E) : n ≠ e := by
  rintro rfl; have := hP.ne n hn n he; omega

end Disj

/-! ## Updates -/

section Upd
open Fl4Spec
variable {Z : Type} {N T E R : Set U64} {B : Set (U64 × Word)} {m m' : U64 → U64} {σ : State Z}

/-- **Membership from the state word**: a TCB whose state word is not a
blocked-on-IPC code is in no endpoint or notification queue. -/
theorem IpcRel.not_queued (hR : IpcRel N T E R B m σ) {t : U64}
    (hs : (m (tStA t)).val ≠ 3 ∧ (m (tStA t)).val ≠ 4 ∧ (m (tStA t)).val ≠ 6) :
    (∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue) ∧
    (∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue) := by
  refine ⟨fun n hn z hz hq => ?_, fun e he z hz hq => ?_⟩
  · obtain ⟨z', hz', hr⟩ := hR.ntfn n hn
    rw [hz] at hz'; injection hz' with hz'; injection hz' with hz'; subst hz'
    exact hs.2.2 (hr.obj.blocked hq).2.1
  · obtain ⟨z', hz', hr⟩ := hR.ep e he
    rw [hz] at hz'; injection hz' with hz'; injection hz' with hz'; subst hz'
    obtain ⟨xs, -, hq', hm⟩ := hr.queue
    rw [hq', List.mem_map] at hq
    obtain ⟨y, hy, ey⟩ := hq
    have : y = t := eq_of_bv ey
    subst this
    rcases (hm y hy).2 with h | h
    · exact hs.1 h
    · exact hs.2.1 h

/-- **Replacing the TCB at `t`**: the other objects keep their relation when
memory agrees outside `t`'s fields; `t`'s state and block object may only
change if `t` is in no queue of either kind. -/
theorem IpcRel.upd_tcb (hR : IpcRel N T E R B m σ) (hP : IPlaced N T E R B) {t : U64} (ht : t ∈ T) (x' : Tcb)
    (hA : Agree m m' (fun b => IFoot N T E R B b ∧ ¬ TFI t b))
    (hq : ((∀ n ∈ N, ∀ z, σ.kheap n.bv = some (.notification z) → t.bv ∉ z.ntfnObj.ntfnQueue) ∧
        (∀ e ∈ E, ∀ z, σ.kheap e.bv = some (.endpoint z) → t.bv ∉ z.epQueue)) ∨
      (m' (tStA t) = m (tStA t) ∧ m' (tBlockA t) = m (tBlockA t)))
    (hx : TcbRel R m' t x') : IpcRel N T E R B m' (updK σ t.bv (.tcb x')) := by
  have hta := hP.e.tcb t ht
  -- words of another TCB `y`
  have hy : ∀ y ∈ T, ∀ a, Aligned a → (TFI y a ∨ TL y a) → (y ≠ t ∨ TL y a) → m' a = m a := by
    intro y hy a ha h hne
    have hI : IFoot N T E R B a := by
      rcases h with (h | rfl) | h
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl h⟩)))
      · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr h⟩)))
    refine hA a ha ⟨hI, ?_⟩
    by_cases e : y = t
    · subst e
      rcases hne with hne | hl
      · exact absurd rfl hne
      · exact TL.not_tfi hta hl
    · exact (tcb_not_tfi hP ht hy e h).1
  have hN : NtfnStateRel N T m' (updK σ t.bv (.tcb x')) := by
    refine hR.toN.upd_tcb ht x' (fun n hn => ?_) (fun y hy' hne => ?_) (fun y hy' => ?_)
      (hq.imp (fun h => h.1) id) hx.toN
    · obtain ⟨w1, w2, w3, w4, w5⟩ := nw_words hP hn
      have f : ∀ a, Aligned a → NW n a → m' a = m a := fun a ha h =>
        hA a ha ⟨h.ifoot hn, (h.not_tcb hP hn ht).1⟩
      exact ⟨f _ (foot_head hP.n hn).1 w1, f _ (foot_ts hP.n hn).1 w2, f _ (foot_badge hP.n hn).1 w3,
        f _ (foot_bound hP.n hn).1 w4, f _ (foot_sc hP.n hn).1 w5⟩
    · have hya := hP.e.tcb y hy'
      exact ⟨hy y hy' _ (a_st hya).1 (Or.inl (Or.inl (a_st hya).2)) (Or.inl hne),
        hy y hy' _ (a_blk hya).1 (Or.inl (Or.inl (a_blk hya).2)) (Or.inl hne),
        by rw [badgeRegA_eq_regA]; exact hy y hy' _ (a_reg hya _).1 (Or.inl (Or.inl (a_reg hya _).2)) (Or.inl hne),
        hy y hy' _ (a_prio hya).1 (Or.inl (Or.inl (a_prio hya).2)) (Or.inl hne)⟩
    · have hya := hP.e.tcb y hy'
      exact ⟨hy y hy' _ (a_prev hya).1 (Or.inr (a_prev hya).2) (Or.inr (a_prev hya).2),
        hy y hy' _ (a_next hya).1 (Or.inr (a_next hya).2) (Or.inr (a_next hya).2)⟩
  have hE : EpStateRel T E R B m' (updK σ t.bv (.tcb x')) :=
    hR.toE.upd_tcb hP.e ht x' (fun b hb ⟨hf, hnt⟩ => hA b hb ⟨Or.inl hf, efoot_not_tfi hP ht hf hnt⟩)
      (hq.imp (fun h => h.2) id) hx.toE
  refine IpcRel.of hN hE fun y hy' z hkz => ?_
  by_cases e : y = t
  · subst e
    simp only [updK, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hkz
    subst hkz; exact hx.sc
  · have hk' : σ.kheap y.bv = some (.tcb z) := by simpa [updK, bv_inj e] using hkz
    rw [hR.sc y hy' z hk', hy y hy' _ (scA_aligned (hP.e.tcb y hy')) (Or.inl (Or.inr rfl)) (Or.inl e)]

/-- The `Ep` links of TCBs blocked on `n` (in memory `m`), as `LinkOn`. -/
theorem linkOn_tcb {m : U64 → U64} {o a : U64} (h : LinkOn T m o a) : ∃ y ∈ T, m (tBlockA y) = o ∧ TL y a := h

/-- **Replacing the notification at `n`**: the other objects keep their
relation when memory agrees outside `n`'s words and the links of the TCBs
blocked on `n`. -/
theorem IpcRel.upd_ntfn (hR : IpcRel N T E R B m σ) (hP : IPlaced N T E R B) {n : U64} (hn : n ∈ N)
    (x' : Notification)
    (hA : Agree m m' (fun b => IFoot N T E R B b ∧ ¬ NW n b ∧ ¬ LinkOn T m n b))
    (hx : NtfnRel1 m' T n x') : IpcRel N T E R B m' (updK σ n.bv (.notification x')) := by
  obtain ⟨x0, hk0, -⟩ := hR.ntfn n hn
  -- TCB words (fields and links of TCBs not blocked on `n`)
  have hf : ∀ y ∈ T, ∀ a, Aligned a → TFI y a → m' a = m a := by
    intro y hy a ha h
    refine hA a ha ⟨?_, fun hw => (hw.not_tcb hP hn hy).1 h, ?_⟩
    · rcases h with h | rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl h⟩)))
      · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
    · rintro ⟨y', hy', -, hl⟩
      by_cases e : y' = y
      · subst e; exact TL.not_tfi (hP.e.tcb y' hy') hl h
      · exact (tcb_not_tfi hP hy hy' e (Or.inr hl)).1 h
  have hl : ∀ y ∈ T, m (tBlockA y) ≠ n → ∀ a, Aligned a → TL y a → m' a = m a := by
    intro y hy hb a ha h
    refine hA a ha ⟨Or.inl (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr h⟩))), fun hw => (hw.not_tcb hP hn hy).2 h, ?_⟩
    rintro ⟨y', hy', hb', hl'⟩
    by_cases e : y' = y
    · subst e; exact hb hb'
    · exact (tcb_not_tfi hP hy hy' e (Or.inr hl')).2 h
  have hT : ∀ y ∈ T, TFieldsEq m m' y := fun y hy =>
    have hya := hP.e.tcb y hy
    ⟨hf y hy _ (a_st hya).1 (Or.inl (a_st hya).2), hf y hy _ (a_blk hya).1 (Or.inl (a_blk hya).2),
      by rw [badgeRegA_eq_regA]; exact hf y hy _ (a_reg hya _).1 (Or.inl (a_reg hya _).2),
      hf y hy _ (a_prio hya).1 (Or.inl (a_prio hya).2)⟩
  have hNs : NtfnStateRel N T m' (updK σ n.bv (.notification x')) := by
    refine hR.toN.upd_ntfn hn x' (fun n' hn' hne => ?_) hT (fun y hy hb => ?_) hx
    · obtain ⟨w1, w2, w3, w4, w5⟩ := nw_words hP hn'
      have g : ∀ a, Aligned a → NW n' a → m' a = m a := fun a ha h => by
        refine hA a ha ⟨h.ifoot hn', h.disj hP hn hn' hne, ?_⟩
        rintro ⟨y, hy, -, hl'⟩; exact (h.not_tcb hP hn' hy).2 hl'
      exact ⟨g _ (foot_head hP.n hn').1 w1, g _ (foot_ts hP.n hn').1 w2, g _ (foot_badge hP.n hn').1 w3,
        g _ (foot_bound hP.n hn').1 w4, g _ (foot_sc hP.n hn').1 w5⟩
    · have hya := hP.e.tcb y hy
      exact ⟨hl y hy hb _ (a_prev hya).1 (a_prev hya).2, hl y hy hb _ (a_next hya).1 (a_next hya).2⟩
  have hEs : EpStateRel T E R B m' (updK σ n.bv (.notification x')) := by
    have hR' := hR.toE
    refine ⟨fun e he => ?_, fun r hr => ?_, fun y hy => ?_, fun wp hw => ?_⟩
    · obtain ⟨z, hkz, hz⟩ := hR'.ep e he
      have hne : e.bv ≠ n.bv := kheap_ne hkz hk0 (fun _ h1 h2 => by subst h1; cases h2)
      have hwe : ∀ a, (a.val = e.val ∨ a.val = e.val + 8) → ¬ NW n a ∧ ¬ LinkOn T m n a := by
        intro a ha
        refine ⟨fun hw => ?_, fun ⟨y, hy, _, hl'⟩ => ?_⟩
        · have := hP.ne n hn e he; unfold NW at hw; omega
        · have := hP.e.et e he y hy; have := TL.range hl'; omega
      refine ⟨z, by simp [updK, hne, hkz], hz.frame
        (hA _ (a_head hP.e he).1 ⟨Or.inl (a_head hP.e he).2, hwe _ (Or.inl (val_head e))⟩)
        (hA _ (a_ts hP.e he).1 ⟨Or.inl (a_ts hP.e he).2, hwe _ (Or.inr (val_ts hP.e he))⟩) fun y hy hq => ?_⟩
      have hya := hP.e.tcb y hy
      have hb : m (tBlockA y) ≠ n := by
        rw [(hz.blocked hq).2]; exact (ntfn_ne_ep hP hn he).symm
      exact ⟨(hT y hy).st, (hT y hy).blk, hl y hy hb _ (a_prev hya).1 (a_prev hya).2,
        hl y hy hb _ (a_next hya).1 (a_next hya).2⟩
    · obtain ⟨z, hkz, hz⟩ := hR'.reply r hr
      have hne : r.bv ≠ n.bv := kheap_ne hkz hk0 (fun _ h1 h2 => by subst h1; cases h2)
      refine ⟨z, by simp [updK, hne, hkz], ?_⟩
      rw [hz, hA _ (a_rtcb hP.e hr).1 ⟨Or.inl (a_rtcb hP.e hr).2, fun hw => ?_, fun ⟨y, hy, _, hl'⟩ => ?_⟩]
      · have := hP.nr n hn r hr; unfold NW at hw; rw [rTcbA_val] at hw; omega
      · have := hP.e.rt r hr y hy; have := TL.range hl'; rw [rTcbA_val] at this; omega
    · obtain ⟨z, hkz, hz⟩ := hR'.tcb y hy
      have hne : y.bv ≠ n.bv := kheap_ne hkz hk0 (fun _ h1 h2 => by subst h1; cases h2)
      exact ⟨z, by simp [updK, hne, hkz], hz.frame (hP.e.tcb y hy) fun a ha h => hf y hy a ha (Or.inl h)⟩
    · have hal : Aligned wp.1 := (hP.e.balign wp hw).1
      show (m' wp.1).bv = loadWordAt σ.machineState.underlyingMemory wp.2
      rw [hA _ hal ⟨Or.inl (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩))), fun hw' => ?_, fun ⟨y, hy, _, hl'⟩ => ?_⟩]
      · exact hR'.buf wp hw
      · have := hP.nb n hn wp hw; unfold NW at hw'; omega
      · have := hP.e.bt wp hw y hy; have := TL.range hl'; omega
  refine IpcRel.of hNs hEs fun y hy z hkz => ?_
  have hne : y.bv ≠ n.bv := by
    intro e; obtain ⟨z', hz', -⟩ := hR.tcb y hy; rw [e, hk0] at hz'; cases hz'
  have hk' : σ.kheap y.bv = some (.tcb z) := by simpa [updK, hne] using hkz
  rw [hR.sc y hy z hk', hf y hy _ (scA_aligned (hP.e.tcb y hy)) (Or.inr rfl)]

/-- **Replacing the endpoint at `e`**: the other objects keep their relation
when memory agrees outside `e`'s words and the links of the TCBs blocked on
`e`. -/
theorem IpcRel.upd_ep (hR : IpcRel N T E R B m σ) (hP : IPlaced N T E R B) {e : U64} (he : e ∈ E)
    (x' : Endpoint)
    (hA : Agree m m' (fun b => IFoot N T E R B b ∧ ¬ EW e b ∧ ¬ LinkOn T m e b))
    (hx : EpObjRel m' T e x') : IpcRel N T E R B m' (updK σ e.bv (.endpoint x')) := by
  obtain ⟨x0, hk0, -⟩ := hR.ep e he
  have hf : ∀ y ∈ T, ∀ a, Aligned a → TFI y a → m' a = m a := by
    intro y hy a ha h
    have hya := hP.e.tcb y hy
    refine hA a ha ⟨?_, fun hw => ?_, ?_⟩
    · rcases h with h | rfl
      · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl h⟩)))
      · exact Or.inr (Or.inr ⟨y, hy, rfl⟩)
    · have := TFI.range hya h; have := hP.e.et e he y hy; unfold EW at hw; omega
    · rintro ⟨y', hy', -, hl⟩
      by_cases e' : y' = y
      · subst e'; exact TL.not_tfi hya hl h
      · exact (tcb_not_tfi hP hy hy' e' (Or.inr hl)).1 h
  have hEs : EpStateRel T E R B m' (updK σ e.bv (.endpoint x')) :=
    hR.toE.upd_ep hP.e he x' (fun b hb ⟨hb1, hb2, hb3⟩ => hA b hb ⟨Or.inl hb1, hb2, hb3⟩) hx
  have hNs : NtfnStateRel N T m' (updK σ e.bv (.endpoint x')) := by
    have hR' := hR.toN
    refine ⟨fun n hn => ?_, fun y hy => ?_⟩
    · obtain ⟨z, hkz, hz⟩ := hR'.ntfn n hn
      have hne : n.bv ≠ e.bv := kheap_ne hkz hk0 (fun _ h1 h2 => by subst h1; cases h2)
      obtain ⟨w1, w2, w3, w4, w5⟩ := nw_words hP hn
      have g : ∀ a, Aligned a → NW n a → m' a = m a := fun a ha h => by
        refine hA a ha ⟨h.ifoot hn, fun hw => ?_, fun ⟨y, hy, _, hl'⟩ => (h.not_tcb hP hn hy).2 hl'⟩
        have := hP.ne n hn e he; unfold NW at h; unfold EW at hw; omega
      refine ⟨z, by simp [updK, hne, hkz], hz.frame ⟨g _ (foot_head hP.n hn).1 w1, g _ (foot_ts hP.n hn).1 w2,
        g _ (foot_badge hP.n hn).1 w3, g _ (foot_bound hP.n hn).1 w4, g _ (foot_sc hP.n hn).1 w5⟩
        fun y hy hq => ?_⟩
      have hya := hP.e.tcb y hy
      have hb : m (tBlockA y) = n := (hz.obj.blocked hq).2.2
      have hlk : ∀ a, Aligned a → TL y a → m' a = m a := by
        intro a ha hl
        refine hA a ha ⟨Or.inl (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inr hl⟩))), fun hw => ?_, ?_⟩
        · have := hP.e.et e he y hy; have := TL.range hl; unfold EW at hw; omega
        · rintro ⟨y', hy', hb', hl'⟩
          by_cases e' : y' = y
          · subst e'; rw [hb] at hb'; exact ntfn_ne_ep hP hn he hb'
          · exact (tcb_not_tfi hP hy hy' e' (Or.inr hl')).2 hl
      exact ⟨hf y hy _ (a_st hya).1 (Or.inl (a_st hya).2), hf y hy _ (a_blk hya).1 (Or.inl (a_blk hya).2),
        hlk _ (a_prev hya).1 (a_prev hya).2, hlk _ (a_next hya).1 (a_next hya).2⟩
    · obtain ⟨z, hkz, hz⟩ := hR'.tcb y hy
      have hne : y.bv ≠ e.bv := kheap_ne hkz hk0 (fun _ h1 h2 => by subst h1; cases h2)
      have hya := hP.e.tcb y hy
      exact ⟨z, by simp [updK, hne, hkz], hz.frame ⟨hf y hy _ (a_st hya).1 (Or.inl (a_st hya).2),
        hf y hy _ (a_blk hya).1 (Or.inl (a_blk hya).2),
        by rw [badgeRegA_eq_regA]; exact hf y hy _ (a_reg hya _).1 (Or.inl (a_reg hya _).2),
        hf y hy _ (a_prio hya).1 (Or.inl (a_prio hya).2)⟩⟩
  refine IpcRel.of hNs hEs fun y hy z hkz => ?_
  have hne : y.bv ≠ e.bv := by
    intro h; obtain ⟨z', hz', -⟩ := hR.tcb y hy; rw [h, hk0] at hz'; cases hz'
  have hk' : σ.kheap y.bv = some (.tcb z) := by simpa [updK, hne] using hkz
  rw [hR.sc y hy z hk', hf y hy _ (scA_aligned (hP.e.tcb y hy)) (Or.inr rfl)]

/-- **Replacing the reply object at `r`.** -/
theorem IpcRel.upd_reply (hR : IpcRel N T E R B m σ) (hP : IPlaced N T E R B) {r : U64} (hr : r ∈ R)
    (x' : Reply) (hA : Agree m m' (fun b => IFoot N T E R B b ∧ b.val ≠ r.val))
    (hx : x'.replyTcb = optRef (m' (rTcbA r))) : IpcRel N T E R B m' (updK σ r.bv (.reply x')) := by
  obtain ⟨x0, hk0, -⟩ := hR.reply r hr
  have hEs := hR.toE.upd_reply hP.e hr x' (fun b hb ⟨hb1, hb2⟩ => hA b hb ⟨Or.inl hb1, hb2⟩) hx
  have hkv : Notif.KView σ (updK σ r.bv (.reply x')) := by
    refine ⟨fun p z h => ?_, fun p z h => ⟨z, ?_, rfl, rfl, rfl⟩⟩
    · have : p ≠ r.bv := by rintro rfl; rw [hk0] at h; cases h
      simpa [updK, this] using h
    · have : p ≠ r.bv := by rintro rfl; rw [hk0] at h; cases h
      simpa [updK, this] using h
  have hNs := hR.toN.frame hP.n (fun a ha hfa => hA a ha ⟨NFoot.ifoot hP hfa, by
    rcases hfa with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
    · have := hP.nr n hn r hr; omega
    · have hta := hP.e.tcb t ht
      have := hP.e.rt r hr t ht
      have hv : a.val = (tStA t).val ∨ a.val = (tBlockA t).val ∨ a.val = (badgeRegA t).val ∨
          a.val = (prioA t).val ∨ a.val = (nextA .Ep t).val ∨ a.val = (prevA .Ep t).val := by
        rcases h with h | h | h | h | h | h <;> simp [h]
      rw [val_st hta, val_blk hta, val_prio hta, val_next hta, val_prev hta, badgeRegA_eq_regA,
        regA_val hta (regIdx_lt _)] at hv
      have := regIdx_lt Fl4Spec.badge_register
      omega⟩) hkv
  refine IpcRel.of hNs hEs fun y hy z hkz => ?_
  have hne : y.bv ≠ r.bv := by
    intro h; obtain ⟨z', hz', -⟩ := hR.tcb y hy; rw [h, hk0] at hz'; cases hz'
  have hk' : σ.kheap y.bv = some (.tcb z) := by simpa [updK, hne] using hkz
  have hya := hP.e.tcb y hy
  rw [hR.sc y hy z hk', hA _ (scA_aligned hya) ⟨Or.inr (Or.inr ⟨y, hy, rfl⟩), by
    rw [scA_val hya]; have := hP.e.rt r hr y hy; omega⟩]

end Upd

end

end Fl4Proofs.P3.Ipc
