/-
P3 (DESIGN.md §9), scheduling contexts: **a reply bound to a thread blocked
receiving has null `PREV`/`NEXT` words** (`RRecv`, carried in `JAtZ`).

FL4 (as seL4's C kernel) binds a reply to a receiver only in
`receive_ipc`'s `wait_for_sender`, after `take_reply` freed it (`cancel_ipc`
of its previous thread: `reply_remove_tcb` clears both links, a receiver's
reply already has none) or found it free (`RFree`: no links). Every other
write of a reply's `TCB` word (`reply_push`) binds a caller blocked on
reply. A reply cut off a call stack (`reply_remove` of a non-head,
`unbind_reply`) keeps links among the cut-off replies, but its thread is
the caller still blocked on reply. So the fact is not "detached replies have
null links" (false in reachable states) but this one; l4v: `valid_replies`
(a receiver's reply has `reply_sc = None` and is in no `sc_replies`), with
C `receiveIPC`/`reply_remove_tcb` clearing the links.

* `RecvB σ d`: the spec's reply `d` names a thread blocked receiving.
* `RRecv m R σ`: every such reply of `R` has null `PREV`/`NEXT` words (on no
  call stack then, `detached_of_next0`).
* `RRecv.frame`: across a step keeping the replies' link words and adding no
  `RecvB` (`KhRB`: each changed object `ObjRB`-steps: a TCB blocked
  receiving after was one before, a reply naming a thread after named it
  before); `KhRB.of_kh` for the frames of the shape
  `σ'.kheap p = σ.kheap p ∨ Chg p o o'`, `KhRB.of_sctkw` for SC steps.
* `RRecv.step`: across a call-stack step (`CallStep`) on `r`.
* `unbind_reply_rwords`: `unbind_reply` keeps every reply's `PREV` word and
  keeps or nulls its `NEXT` word.
-/
import Fl4Proofs.P3.ScCallOps
import Fl4Proofs.P3.ScTK
import Fl4Proofs.P3.ScCallCut
import Fl4Proofs.P3.ScCallUnbind
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Spec
open Fl4Spec

/-- The spec's reply `d` names a thread blocked receiving. -/
def RecvB (σ : State Unit) (d : U64) : Prop :=
  ∃ x t xt, σ.kheap d.bv = some (.reply x) ∧ x.replyTcb = some t ∧ σ.kheap t = some (.tcb xt) ∧
    receiveBlocked xt.tcbState = true

/-- An object step adding no receive-blocked TCB and no reply's thread. -/
def ObjRB (o o' : KernelObject) : Prop :=
  (∀ y, o' = .tcb y → receiveBlocked y.tcbState = true → ∃ x, o = .tcb x ∧ receiveBlocked x.tcbState = true) ∧
  (∀ y t, o' = .reply y → y.replyTcb = some t → ∃ x, o = .reply x ∧ x.replyTcb = some t)

theorem ObjRB.refl (o : KernelObject) : ObjRB o o :=
  ⟨fun y h hb => ⟨y, h, hb⟩, fun y t h ht => ⟨y, h, ht⟩⟩

/-- A TCB step whose state after is not receive-blocked, or kept. -/
theorem ObjRB.tcb {x y : Tcb} (h : y.tcbState = x.tcbState ∨ receiveBlocked y.tcbState = false) :
    ObjRB (.tcb x) (.tcb y) := by
  refine ⟨fun y' e hb => ?_, fun y' t e _ => (by cases e)⟩
  cases e
  rcases h with h | h
  · exact ⟨x, rfl, h ▸ hb⟩
  · rw [h] at hb; cases hb

/-- A reply step keeping its thread or dropping it. -/
theorem ObjRB.reply {x y : Reply} (h : y.replyTcb = x.replyTcb ∨ y.replyTcb = none) :
    ObjRB (.reply x) (.reply y) := by
  refine ⟨fun y' e _ => (by cases e), fun y' t e ht => ?_⟩
  cases e
  rcases h with h | h
  · exact ⟨x, rfl, h ▸ ht⟩
  · rw [h] at ht; cases ht

/-- An object step between kinds other than TCBs and replies. -/
theorem ObjRB.other {o o' : KernelObject} (h1 : ∀ y, o' ≠ .tcb y) (h2 : ∀ y, o' ≠ .reply y) : ObjRB o o' :=
  ⟨fun y e => absurd e (h1 y), fun y _ e => absurd e (h2 y)⟩

/-- Every object after `ObjRB`-steps from the one before (or is kept). -/
def KhRB (σ σ' : State Unit) : Prop :=
  ∀ p o', σ'.kheap p = some o' → ∃ o, σ.kheap p = some o ∧ ObjRB o o'

theorem KhRB.refl (σ : State Unit) : KhRB σ σ := fun _ o' h => ⟨o', h, ObjRB.refl o'⟩

theorem KhRB.of_kheap {σ σ' : State Unit} (h : σ'.kheap = σ.kheap) : KhRB σ σ' :=
  fun _ o' hp => ⟨o', by rw [← h]; exact hp, ObjRB.refl o'⟩

theorem KhRB.trans {σ1 σ2 σ3 : State Unit} (h1 : KhRB σ1 σ2) (h2 : KhRB σ2 σ3) : KhRB σ1 σ3 := by
  intro p o3 hp
  obtain ⟨o2, hp2, r2⟩ := h2 p o3 hp
  obtain ⟨o1, hp1, r1⟩ := h1 p o2 hp2
  refine ⟨o1, hp1, fun y e hb => ?_, fun y t e ht => ?_⟩
  · obtain ⟨x2, e2, hb2⟩ := r2.1 y e hb; exact r1.1 x2 e2 hb2
  · obtain ⟨x2, e2, ht2⟩ := r2.2 y t e ht; exact r1.2 x2 t e2 ht2

/-- **`KhRB` of a frame of the usual shape** (each object kept or
`Q`-changed, every `Q`-change `ObjRB`). -/
theorem KhRB.of_kh {σ σ' : State Unit} {Q : ObjRef → KernelObject → KernelObject → Prop}
    (kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ Q p o o')
    (hQ : ∀ p o o', Q p o o' → ObjRB o o') : KhRB σ σ' := by
  intro p o' hp
  rcases kh p with e | ⟨o, o2, h1, h2, hq⟩
  · exact ⟨o', by rw [← e]; exact hp, ObjRB.refl o'⟩
  · rw [hp] at h2; cases h2; exact ⟨o, h1, hQ p o o' hq⟩

/-- An update of one object, `ObjRB`-stepping. -/
theorem KhRB.upd {σ : State Unit} {p : ObjRef} {o o' : KernelObject} (hk : σ.kheap p = some o)
    (h : ObjRB o o') : KhRB σ (updK σ p o') := by
  intro q o2 hq
  by_cases e : q = p
  · subst e; simp [updK] at hq; subst hq; exact ⟨o, hk, h⟩
  · simp [updK, e] at hq; exact ⟨o2, hq, ObjRB.refl o2⟩

/-- `TKObj` steps add no `RecvB` (a TCB's state changes only between
IPC-free states; a reply changes only its SC). -/
theorem TKObj.rb {P : Prop} {o o' : KernelObject} (h : TKObj P o o') : ObjRB o o' := by
  rcases h with rfl | ⟨x, y, rfl, rfl, -, hs⟩ | ⟨x, y, n, rfl, rfl⟩ | ⟨x, y, rfl, rfl, -⟩ | ⟨x, y, rfl, rfl, e⟩
  · exact ObjRB.refl _
  · refine ObjRB.tcb (hs.imp_right fun hh => ?_)
    obtain ⟨-, -, hy⟩ := hh
    obtain ⟨hep, -, -⟩ := hy
    generalize y.tcbState = ts at hep ⊢
    cases ts <;> simp_all [Fl4Spec.epBlocked, receiveBlocked]
  · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)
  · exact ObjRB.other (fun _ e => by cases e) (fun _ e => by cases e)
  · exact ObjRB.reply (Or.inl (by rw [e]))

theorem KhRB.of_otk {P : ObjRef → Prop} {σ σ' : State Unit} (h : ∀ p, OTK (P p) (σ.kheap p) (σ'.kheap p)) :
    KhRB σ σ' := by
  intro p o' hp
  have hk := h p
  rw [hp] at hk
  cases e : σ.kheap p with
  | none => rw [e] at hk; exact absurd hk (by simp [OTK])
  | some o => rw [e] at hk; exact ⟨o, rfl, TKObj.rb hk⟩

theorem KhRB.of_sctkw {P : ObjRef → Prop} {σ σ' : State Unit} (h : ScTKw P σ σ') : KhRB σ σ' :=
  KhRB.of_otk h.kh

/-- The unlink of a reply from its thread (`reply_unlink`: the thread
`Inactive`, the reply's thread dropped). -/
theorem KhRB.unlink {σ5 σ' : State Unit} {t r : ObjRef} {x5 : Tcb} {xr5 : Reply}
    (hkt : σ5.kheap t = some (.tcb x5)) (hkr : σ5.kheap r = some (.reply xr5))
    (kt' : σ'.kheap t = some (.tcb { x5 with tcbState := .inactive }))
    (kr' : σ'.kheap r = some (.reply { xr5 with replyTcb := none }))
    (ko' : ∀ p, p ≠ t → p ≠ r → σ'.kheap p = σ5.kheap p) : KhRB σ5 σ' := by
  intro p o' hp
  by_cases e1 : p = t
  · subst e1; rw [kt'] at hp; obtain rfl := Option.some.inj hp; exact ⟨_, hkt, ObjRB.tcb (Or.inr rfl)⟩
  by_cases e2 : p = r
  · subst e2; rw [kr'] at hp; obtain rfl := Option.some.inj hp; exact ⟨_, hkr, ObjRB.reply (Or.inr rfl)⟩
  rw [ko' p e1 e2] at hp; exact ⟨o', hp, ObjRB.refl o'⟩

/-- `RecvB` back across a `KhRB` step. -/
theorem KhRB.recvB {σ σ' : State Unit} (h : KhRB σ σ') {d : U64} (hd : RecvB σ' d) : RecvB σ d := by
  obtain ⟨x', t, xt', hx', ht', hxt', hb'⟩ := hd
  obtain ⟨o, ho, r⟩ := h _ _ hx'
  obtain ⟨x, rfl, ht⟩ := r.2 x' t rfl ht'
  obtain ⟨o2, ho2, r2⟩ := h _ _ hxt'
  obtain ⟨xt, rfl, hb⟩ := r2.1 xt' rfl hb'
  exact ⟨x, t, xt, ho, ht, ho2, hb⟩

end Spec

/-- **A reply bound to a thread blocked receiving has null links** (module
docstring). -/
def RRecv (m : U64 → U64) (R : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ d ∈ R, RecvB σ d → m (rNextA d) = 0#u64 ∧ m (rPrevA d) = 0#u64

/-- **A reply with a null `NEXT` word is on no call stack**: a stack's
newest reply's `NEXT` word is its SC tagged with bit 0, an older one's the
next newer reply (`StackW`), never null (`RPlaced.align`). -/
theorem detached_of_next0 {m : U64 → U64} {R C : Set U64} {σ : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (hC : CallRel m R C σ Lst) (hR0 : ∀ r ∈ R, r ≠ 0#u64) {d : U64} (hn : m (rNextA d) = 0#u64) :
    Detached C Lst d := by
  intro sc hsc hd
  obtain ⟨-, hLR, -, hW⟩ := hC.stack sc hsc
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hd
  have hw := (hW.2 i hi).2
  rw [e, hn] at hw
  cases i with
  | zero => exact odd_ne_even (q := sc) (r := 0#u64) (by first | decide | rfl | simp) hw.symm
  | succ j =>
    have hj : j < (Lst sc).length := by omega
    have hw' : (Lst sc).getD j 0#u64 = 0#u64 := hw.symm
    first
      | simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some] at hw'
      | rw [List.getD_eq_getElem _ _ hj] at hw'
    exact hR0 _ (hLR _ (List.getElem_mem hj)) hw'

/-- **`RRecv` across a step keeping the replies' link words and adding no
`RecvB`.** -/
theorem RRecv.frame {R : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : RRecv m R σ)
    (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d)) (hb : KhRB σ σ') :
    RRecv m' R σ' := fun d hd hr => by
  obtain ⟨h1, h2⟩ := h d hd (hb.recvB hr)
  exact ⟨(hm d hd).2.trans h1, (hm d hd).1.trans h2⟩

/-- `RRecv` with the link words kept and the spec's objects kept. -/
theorem RRecv.same {R : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} (h : RRecv m R σ)
    (hm : ∀ d ∈ R, m' (rPrevA d) = m (rPrevA d) ∧ m' (rNextA d) = m (rNextA d)) (hk : σ'.kheap = σ.kheap) :
    RRecv m' R σ' := h.frame hm (KhRB.of_kheap hk)

/-- **`RRecv` across a call-stack step on `r`** (`CallStep`: the other
detached unlinked replies keep their words): `r` unlinked after, or not
bound to a receiver after; every other `RecvB` after was one before. -/
theorem RRecv.step {R C : Set U64} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {Lst Lst' : U64 → List U64}
    {r : U64} (h : RRecv m R σ) (hCR : CallRel m R C σ Lst) (hR0 : ∀ d ∈ R, d ≠ 0#u64)
    (hcs : CallStep m m' R C Lst Lst' r) (hb : ∀ d ∈ R, RecvB σ' d → d ≠ r → RecvB σ d)
    (hr : RecvB σ' r → m' (rNextA r) = 0#u64 ∧ m' (rPrevA r) = 0#u64) : RRecv m' R σ' := by
  intro d hd hrd
  by_cases e : d = r
  · subst e; exact hr hrd
  · obtain ⟨h0n, h0p⟩ := h d hd (hb d hd hrd e)
    obtain ⟨e1, e2⟩ := hcs.1 d hd (detached_of_next0 hCR hR0 h0n) h0n h0p e
    exact ⟨e1.trans h0n, e2.trans h0p⟩


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`unbind_reply`'s reply words** (module docstring): it writes only the
head reply's `NEXT` word, with null. -/
theorem unbind_reply_rwords {N T C R : Set U64} {c : U64} (s : S) (σ : Fl4Spec.State Unit)
    (hS : SchedRel st N T C c s σ) {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst)
    (hRP : RPlaced st N T C R c s σ) {p : U64} (hp : p ∈ C) (hp0 : p ≠ 0#u64) {y : Fl4Spec.SchedContext} {n : Nat}
    (hk : σ.kheap p.bv = some (.schedContext y n)) :
    schedcontext.unbind_reply st s p ⦃ s' => ∀ r ∈ R,
      (L.mem s' (rNextA r) = L.mem s (rNextA r) ∨ L.mem s' (rNextA r) = 0#u64) ∧
      L.mem s' (rPrevA r) = L.mem s (rPrevA r) ⦄ := by
  obtain ⟨⟨y', n', hk', hyL⟩, hLR, hLnd, hLw⟩ := hCR.stack p hp
  rw [hk] at hk'; cases hk'
  obtain ⟨haP, hvP, hszP⟩ := sc_reply_word hS hp
  unfold schedcontext.unbind_reply
  step with obj.Sc.is_null.spec' as ⟨b, hb⟩
  simp only [hb, hp0, decide_false, Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (obj.Sc.reply.val s p) ?_
  intro i hi
  rw [hLw.1] at hi
  subst hi
  cases hL : Lst p with
  | nil =>
    simp only [List.headD_nil, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    first | trivial | (intro r _; simp) | simp
  | cons r0 rest =>
    have hr0R : r0 ∈ R := hLR r0 (by rw [hL]; simp)
    have hA0 := hRP.align r0 hr0R
    have hne0 : (r0 != 0#u64) = true := by simpa using hA0.2.1
    simp only [List.headD_cons, hne0, ↓reduceIte]
    refine WP.spec_bind (obj.Reply.set_next.val0 s r0 0#u64) ?_
    rintro s1 rfl
    rw [rz_next]
    have hn0 : Aligned (rNextA r0) := hRP.aligned hr0R (Or.inr (rNextA_val hA0))
    refine WP.spec_mono (obj.Sc.set_reply.spec _ p 0#u64) ?_
    rintro s2 rfl
    intro r hr
    have hA := hRP.align r hr
    have h1 := hRP.sc r hr p hp y n hk
    have h2 := hszP y n hk
    have hpv : (scReplyA p).val ≠ (rPrevA r).val := by rw [hvP, rPrevA_val hA]; omega
    have hnv : (scReplyA p).val ≠ (rNextA r).val := by rw [hvP, rNextA_val hA]; omega
    have alP := hRP.aligned hr (Or.inl (rPrevA_val hA))
    have alN := hRP.aligned hr (Or.inr (rNextA_val hA))
    refine ⟨?_, ?_⟩
    · rw [L.mem_wr_ne haP alN hnv]
      by_cases e : r = r0
      · subst e; exact Or.inr (L.mem_wr_same hn0)
      · exact Or.inl (L.mem_wr_ne hn0 alN (Ne.symm ((rwords_ne hA hA0).2 e).2))
    · rw [L.mem_wr_ne haP alP hpv, L.mem_wr_ne hn0 alP (Ne.symm (rwords_ne hA hA0).1)]

end

end

end Fl4Proofs.P3.Sched
