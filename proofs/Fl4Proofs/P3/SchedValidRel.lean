/-
P3 (DESIGN.md §9): **`SchedValid` at related states**, from the IPC relation
(`IpcRel`: TCBs, notifications, endpoints, replies), P1's endpoint and
notification queues (`EpsWit`, outside entries: no exception set) and reply
links (`ReplyInv0`), the call-stack relation (`CallRel`) and the yield-to
relation (`YieldRel`), with the spec's objects those of the relations' sets
(`ObjCover`): `schedValid_of`.

Not from these, and named:
* `EpRdyHyp`: an endpoint's queued threads have their SCs released when
  active (l4v `released_ipc_queues` for endpoints; `Inv.rd` covers the
  notification-blocked ones);
* `ScLinkHyp`: an SC's thread and notification exist and a TCB's bound
  notification exists (the scheduler relation's SC words and P1's
  `BoundInv`).
-/
import Fl4Proofs.P3.SchedValid
import Fl4Proofs.P3.IpcRel
import Fl4Proofs.P3.ScCall
import Fl4Proofs.P3.ScYield
import Fl4Proofs.P1.QueueHeap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section Spec
open Fl4Spec

/-- **The spec's objects are the relations' objects.** -/
structure ObjCover (N T E R C : Set U64) (σ : State Unit) : Prop where
  tcb : ∀ o x, σ.kheap o = some (.tcb x) → ∃ t ∈ T, t.bv = o
  ntfn : ∀ o x, σ.kheap o = some (.notification x) → ∃ n ∈ N, n.bv = o
  ep : ∀ o x, σ.kheap o = some (.endpoint x) → ∃ e ∈ E, e.bv = o
  reply : ∀ o x, σ.kheap o = some (.reply x) → ∃ r ∈ R, r.bv = o
  sc : ∀ o y k, σ.kheap o = some (.schedContext y k) → ∃ c ∈ C, c.bv = o

/-- l4v `released_ipc_queues` for the endpoints. -/
def EpRdyHyp (σ : State Unit) : Prop := ∀ e x, σ.kheap e = some (.endpoint x) → ∀ u ∈ x.epQueue, QRdy σ u

/-- The SC links and bound notifications (see the module docstring). -/
structure ScLinkHyp (σ : State Unit) : Prop where
  scTcb : ∀ sc y k f, σ.kheap sc = some (.schedContext y k) → y.scTcb = some f → ∃ x, σ.kheap f = some (.tcb x)
  scNtfn : ∀ sc y k n, σ.kheap sc = some (.schedContext y k) → y.scNtfn = some n →
    ∃ xn, σ.kheap n = some (.notification xn)
  tcbNtfn : ∀ t x n, σ.kheap t = some (.tcb x) → x.tcbBoundNotification = some n →
    ∃ xn, σ.kheap n = some (.notification xn)
  /-- A sporadic SC is active (Configure sets sporadic only with a budget of
  at least `MIN_BUDGET`; FL4's `ScRelW.spor`). -/
  scSpor : ∀ sc y k, σ.kheap sc = some (.schedContext y k) → y.scSporadic = true → scActive y = true

theorem optRef_some {w : U64} {p : ObjRef} (h : optRef w = some p) : w ≠ 0#u64 ∧ w.bv = p := by
  unfold optRef at h
  split_ifs at h with h0
  cases h; exact ⟨h0, rfl⟩

theorem optRef_ne {w : U64} (h : w ≠ 0#u64) : optRef w = some w.bv := by
  unfold optRef; rw [if_neg h]

theorem bv_inj {a b : U64} (h : a.bv = b.bv) : a = b :=
  UScalar.eq_of_val_eq (by have := congrArg BitVec.toNat h; simpa using this)

theorem nodup_map_bv {xs : List U64} (h : xs.Nodup) : (xs.map UScalar.bv).Nodup :=
  h.map (fun _ _ e => bv_inj e)

theorem mem_map_bv' {xs : List U64} {u : ObjRef} (h : u ∈ xs.map UScalar.bv) : ∃ y ∈ xs, y.bv = u := by
  simpa using h

theorem stA_tStA (t : U64) : P1.stA t = tStA t := by rw [P1.stA_eq, tStA_eq]
theorem blockA_tBlockA (t : U64) : P1.blockA t = tBlockA t := rfl
theorem replyA_tReplyA (t : U64) : P1.replyA t = tReplyA t := rfl

end Spec

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- An object's queue in `EpsWit`, at a queue relation's header: the same
list. -/
theorem eqs_unique {T Cs Ω : Set U64} {H : Heap} {s : S} {E' : Set U64} {EQ : U64 → List U64}
    (hW : EpsWit st T Cs Ω H ∅ s E' EQ) (hTP : TcbPlaced T) {e : U64} (he : e ∈ E') {xs : List U64}
    (hq : QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs) : xs = EQ e :=
  QueueRel.unique hTP hq (hW.1 e he).2.2


/-- The spec's endpoint at an object of `EpsWit` holding a queued thread. -/
theorem ep_member {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {Cs Ω : Set U64} {H : Heap} {s : S}
    {σ : Fl4Spec.State Unit} {E' : Set U64} {EQ : U64 → List U64}
    (hI : Ipc.IpcRel N T E R B (L.mem s) σ) (hW : EpsWit st T Cs Ω H ∅ s E' EQ) (hTP : TcbPlaced T)
    {e : U64} (he : e ∈ E) (he' : e ∈ E') {u : U64} (hu : u ∈ EQ e) :
    ∃ xe, σ.kheap e.bv = some (.endpoint xe) ∧ u.bv ∈ xe.epQueue := by
  obtain ⟨xe, hk, hr⟩ := hI.ep e he
  refine ⟨xe, hk, ?_⟩
  cases xe with
  | idleEP =>
    have := eqs_unique hW hTP he' hr.2
    rw [← this] at hu; cases hu
  | sendEP q =>
    obtain ⟨-, xs, -, rfl, hq, -⟩ := hr
    have := eqs_unique hW hTP he' hq
    rw [← this] at hu
    exact List.mem_map_of_mem hu
  | recvEP q =>
    obtain ⟨-, xs, -, rfl, hq, -⟩ := hr
    have := eqs_unique hW hTP he' hq
    rw [← this] at hu
    exact List.mem_map_of_mem hu

/-- The spec's notification at an object of `EpsWit` holding a queued thread. -/
theorem ntfn_member {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {Cs Ω : Set U64} {H : Heap} {s : S}
    {σ : Fl4Spec.State Unit} {E' : Set U64} {EQ : U64 → List U64}
    (hI : Ipc.IpcRel N T E R B (L.mem s) σ) (hW : EpsWit st T Cs Ω H ∅ s E' EQ) (hTP : TcbPlaced T)
    {n : U64} (hn : n ∈ N) (hn' : n ∈ E') {u : U64} (hu : u ∈ EQ n) :
    ∃ xn, σ.kheap n.bv = some (.notification xn) ∧ u.bv ∈ Fl4Spec.ntfnQueueOf xn := by
  obtain ⟨xn, hk, hr⟩ := hI.ntfn n hn
  refine ⟨xn, hk, ?_⟩
  have ho := hr.obj
  cases hx : xn.ntfnObj with
  | idleNtfn =>
    rw [hx] at ho
    have := eqs_unique hW hTP hn' ho.2
    rw [← this] at hu; cases hu
  | activeNtfn b =>
    rw [hx] at ho
    have := eqs_unique hW hTP hn' ho.2.1
    rw [← this] at hu; cases hu
  | waitingNtfn q =>
    rw [hx] at ho
    obtain ⟨-, xs, -, rfl, hq, -⟩ := ho
    have := eqs_unique hW hTP hn' hq
    rw [← this] at hu
    show u.bv ∈ xn.ntfnObj.ntfnQueue
    rw [hx]
    exact List.mem_map_of_mem hu

theorem st_of_code {w k : U64} (h : w.val = k.val) : w = k := UScalar.eq_of_val_eq h

/-- **`SchedValid` from the relations** (see the module docstring). -/
theorem schedValid_of {N T E R C Cs Ω Scs : Set U64} {B : Set (U64 × Fl4Spec.Word)} {H : Heap} {s : S}
    {σ : Fl4Spec.State Unit} {E' : Set U64} {EQ : U64 → List U64} {Lst : U64 → List U64}
    (hI : Ipc.IpcRel N T E R B (L.mem s) σ) (hTP : TcbPlaced T) (hCv : ObjCover N T E R C σ)
    (hW : EpsWit st T Cs Ω H ∅ s E' EQ) (hHE : ∀ e, H e = some .ep → e ∈ E)
    (hHN : ∀ n, H n = some .ntfn → n ∈ N)
    (hRI : ReplyInv0 st T R Scs s) (hCR : CallRel (L.mem s) R C σ Lst) (hY : YieldRel T C (L.mem s) σ)
    (hC0 : ∀ c ∈ C, c ≠ 0#u64) (hRdy : EpRdyHyp σ) (hSL : ScLinkHyp σ) :
    SchedValid σ := by
  have hvals := tsVals
  -- a spec TCB, its FL4 TCB and relation
  have tcbOf : ∀ o x, σ.kheap o = some (.tcb x) → ∃ t ∈ T, t.bv = o ∧ Ipc.TcbRel R (L.mem s) t x := by
    intro o x hk
    obtain ⟨t, ht, rfl⟩ := hCv.tcb o x hk
    obtain ⟨x', hk', hR⟩ := hI.tcb t ht
    rw [hk] at hk'; cases hk'
    exact ⟨t, ht, rfl, hR⟩
  have hblk := hW.2.2.2.2.1
  have hk1 := hW.2.2.2.2.2.1
  have hk2 := hW.2.2.2.2.2.2.1
  refine ⟨fun e x hk => ?_, fun n x hk => ?_, fun t x ep ro d hk hs => ?_, fun t x ep pl hk hs => ?_,
    fun t x n hk hs => ?_, fun t x ep r d hk hs => ?_, fun t x r hk hs => ?_, fun r xr t hk ht => ?_,
    fun sc y k r hk hm => ?_, hSL.scTcb, hSL.scNtfn, fun sc y k t hk hyf => ?_, fun t x p hk hyt => ?_,
    hSL.tcbNtfn, fun n xn t hk ht => ?_, hSL.scSpor⟩
  · -- epQ
    obtain ⟨e', he', rfl⟩ := hCv.ep e x hk
    obtain ⟨x', hk', hr⟩ := hI.ep e' he'
    rw [hk] at hk'; cases hk'
    refine ⟨?_, hRdy _ x hk⟩
    cases x with
    | idleEP => exact List.nodup_nil
    | sendEP q => obtain ⟨-, xs, -, rfl, hq, -⟩ := hr; exact nodup_map_bv hq.nodup
    | recvEP q => obtain ⟨-, xs, -, rfl, hq, -⟩ := hr; exact nodup_map_bv hq.nodup
  · -- ntfnQ
    obtain ⟨n', hn', rfl⟩ := hCv.ntfn n x hk
    obtain ⟨x', hk', hr⟩ := hI.ntfn n' hn'
    rw [hk] at hk'; cases hk'
    have ho := hr.obj
    show (x.ntfnObj.ntfnQueue).Nodup ∧ ∀ u ∈ x.ntfnObj.ntfnQueue, _
    cases hx : x.ntfnObj with
    | idleNtfn => exact ⟨List.nodup_nil, fun u hu => by cases hu⟩
    | activeNtfn b => exact ⟨List.nodup_nil, fun u hu => by cases hu⟩
    | waitingNtfn q =>
      rw [hx] at ho
      obtain ⟨-, xs, -, rfl, hq, hbl⟩ := ho
      refine ⟨nodup_map_bv hq.nodup, fun u hu => ?_⟩
      obtain ⟨y, hy, rfl⟩ := mem_map_bv' hu
      obtain ⟨xy, hky, hR⟩ := hI.tcb y (hq.mem y hy)
      refine ⟨xy, hky, ?_⟩
      obtain ⟨h1, h2⟩ := hbl y hy
      have hc : Notif.tsCode xy.tcbState = 6 := by rw [← hR.st]; exact h1
      cases hs : xy.tcbState <;> rw [hs] at hc <;> simp [Notif.tsCode] at hc
      rename_i n''
      have := hR.blkN n'' hs
      rw [h2] at this
      rw [this]
  · -- recvQ
    obtain ⟨t', ht', rfl, hR⟩ := tcbOf t x hk
    have hc : (L.mem s (P1.stA t')).val = 3 := by rw [stA_tStA, hR.st, hs]; rfl
    have hs3 : L.mem s (P1.stA t') = sched.TS_BLOCKED_ON_RECV := st_of_code (by rw [hc, hvals.2.2.1]; rfl)
    obtain ⟨hbe, hbq⟩ := hblk t' ht' (fun h => h) (Or.inr (Or.inl hs3))
    have hH := hk1 t' ht' (fun h => h) (Or.inr hs3)
    obtain ⟨xe, hke, hq⟩ := ep_member hI hW hTP (hHE _ hH) hbe hbq
    have he : (L.mem s (P1.blockA t')).bv = ep := by rw [blockA_tBlockA]; exact hR.blkE ep (by rw [hs]; rfl)
    rw [he] at hke
    exact ⟨xe, hke, hq⟩
  · -- sendQ
    obtain ⟨t', ht', rfl, hR⟩ := tcbOf t x hk
    have hc : (L.mem s (P1.stA t')).val = 4 := by rw [stA_tStA, hR.st, hs]; rfl
    have hs4 : L.mem s (P1.stA t') = sched.TS_BLOCKED_ON_SEND := st_of_code (by rw [hc, hvals.2.2.2.1]; rfl)
    obtain ⟨hbe, hbq⟩ := hblk t' ht' (fun h => h) (Or.inl hs4)
    have hH := hk1 t' ht' (fun h => h) (Or.inl hs4)
    obtain ⟨xe, hke, hq⟩ := ep_member hI hW hTP (hHE _ hH) hbe hbq
    have he : (L.mem s (P1.blockA t')).bv = ep := by rw [blockA_tBlockA]; exact hR.blkE ep (by rw [hs]; rfl)
    rw [he] at hke
    exact ⟨xe, hke, hq⟩
  · -- ntfnW
    obtain ⟨t', ht', rfl, hR⟩ := tcbOf t x hk
    have hc : (L.mem s (P1.stA t')).val = 6 := by rw [stA_tStA, hR.st, hs]; rfl
    have hs6 : L.mem s (P1.stA t') = sched.TS_BLOCKED_ON_NTFN := st_of_code (by rw [hc, hvals.2.2.2.2]; rfl)
    obtain ⟨hbe, hbq⟩ := hblk t' ht' (fun h => h) (Or.inr (Or.inr hs6))
    have hH := hk2 t' ht' (fun h => h) hs6
    obtain ⟨xn, hkn, hq⟩ := ntfn_member hI hW hTP (hHN _ hH) hbe hbq
    have he : (L.mem s (P1.blockA t')).bv = n := by rw [blockA_tBlockA]; exact hR.blkN n hs
    rw [he] at hkn
    exact ⟨xn, hkn, hq⟩
  · -- recvReply
    obtain ⟨t', ht', rfl, hR⟩ := tcbOf t x hk
    obtain ⟨hro, hrR⟩ := hR.recv ep (some r) d hs
    obtain ⟨h0, hrb⟩ := optRef_some hro
    have hc : (L.mem s (P1.stA t')).val = 3 := by rw [stA_tStA, hR.st, hs]; rfl
    have hs3 : L.mem s (P1.stA t') = sched.TS_BLOCKED_ON_RECV := st_of_code (by rw [hc, hvals.2.2.1]; rfl)
    obtain ⟨-, hback⟩ := hRI.recv t' ht' hs3 h0
    obtain ⟨xr, hkr, hrt⟩ := hI.reply _ (hrR (by simp))
    rw [hrb] at hkr
    refine ⟨xr, hkr, ?_⟩
    rw [hrt]
    have : Endp.rTcbA (L.mem s (tReplyA t')) = P1.rTcbA (L.mem s (P1.replyA t')) := rfl
    rw [this, hback]
    exact optRef_ne (fun h => (hTP t' ht').ne0 (by rw [h]; rfl))
  · -- onReply
    obtain ⟨t', ht', rfl, hR⟩ := tcbOf t x hk
    have hrb := hR.reply r hs
    have hc : (L.mem s (P1.stA t')).val = 5 := by rw [stA_tStA, hR.st, hs]; rfl
    have hs5 : L.mem s (P1.stA t') = sched.TS_BLOCKED_ON_REPLY :=
      st_of_code (by rw [hc]; unfold sched.TS_BLOCKED_ON_REPLY; rfl)
    obtain ⟨hmR, hback⟩ := hRI.reply t' ht' hs5
    obtain ⟨xr, hkr, hrt⟩ := hI.reply _ hmR
    rw [replyA_tReplyA, hrb] at hkr
    refine ⟨xr, hkr, ?_⟩
    rw [hrt]
    have : Endp.rTcbA (L.mem s (P1.replyA t')) = P1.rTcbA (L.mem s (P1.replyA t')) := rfl
    rw [this, hback]
    exact optRef_ne (fun h => (hTP t' ht').ne0 (by rw [h]; rfl))
  · -- replyTcb
    obtain ⟨r', hr', rfl⟩ := hCv.reply r xr hk
    obtain ⟨xr', hk', hrt⟩ := hI.reply r' hr'
    rw [hk] at hk'; cases hk'
    rw [hrt] at ht
    obtain ⟨h0, hbt⟩ := optRef_some ht
    obtain ⟨hr0, hT, hra, hst⟩ := hRI.back r' hr' h0
    obtain ⟨x, hkx, hR⟩ := hI.tcb _ hT
    rw [show P1.rTcbA r' = Endp.rTcbA r' from rfl, hbt] at hkx
    refine ⟨x, hkx, ?_⟩
    have hcode := hR.st
    rw [← stA_tStA] at hcode
    rcases hst with e | e
    · rw [e] at hcode
      have h5 : Notif.tsCode x.tcbState = 5 := by rw [← hcode]; unfold sched.TS_BLOCKED_ON_REPLY; rfl
      cases hs : x.tcbState <;> rw [hs] at h5 <;> simp [Notif.tsCode] at h5
      rename_i r''
      have := hR.reply r'' hs
      rw [← replyA_tReplyA, hra] at this
      exact Or.inl (by rw [this])
    · rw [e, hvals.2.2.1] at hcode
      have h3 : Notif.tsCode x.tcbState = 3 := by rw [← hcode]; rfl
      obtain ⟨ep, ro, d, hs⟩ := Endp.tsCode_three h3
      obtain ⟨hro, -⟩ := hR.recv ep ro d hs
      rw [← replyA_tReplyA, hra, optRef_ne hr0] at hro
      exact Or.inr ⟨ep, d, by rw [hs, ← hro]⟩
  · -- replies
    obtain ⟨c, hc, rfl⟩ := hCv.sc sc y k hk
    obtain ⟨⟨y', k', hk', hl⟩, hLR, -, -⟩ := hCR.stack c hc
    rw [hk] at hk'; cases hk'
    rw [hl] at hm
    obtain ⟨r', hr', rfl⟩ := mem_map_bv' hm
    obtain ⟨xr, hkr, hsc⟩ := hCR.reply r' (hLR r' hr')
    refine ⟨xr, hkr, fun hh => ?_, fun hh => ?_⟩
    · rw [hl] at hh
      have hh' : (Lst c).head? = some r' := by
        cases e : Lst c with
        | nil => rw [e] at hh; cases hh
        | cons a l => rw [e] at hh; simp at hh; rw [bv_inj hh]; rfl
      exact (hsc c.bv).2 ⟨c, hc, rfl, hh'⟩
    · cases e : xr.replySc with
      | none => rfl
      | some p =>
        obtain ⟨c', hc', hp, hhd⟩ := (hsc p).1 e
        have hr1 : r' ∈ Lst c' := List.mem_of_mem_head? hhd
        have := hCR.excl c hc c' hc' r' hr' hr1
        subst this
        exact absurd (by rw [hl]; cases e2 : Lst c with
          | nil => rw [e2] at hhd; cases hhd
          | cons a l => rw [e2] at hhd; simp at hhd; subst hhd; rfl) hh
  · -- scYieldFrom
    obtain ⟨c, hc, rfl⟩ := hCv.sc sc y k hk
    obtain ⟨t', ht', rfl, hyw⟩ := hY.frm c hc y k hk t hyf
    obtain ⟨x, hkx, hyt⟩ := hY.tcb t' ht'
    refine ⟨x, hkx, ?_⟩
    rw [hyt, hyw]
    exact optRef_ne (hC0 c hc)
  · -- tcbYieldTo
    obtain ⟨t', ht', rfl, -⟩ := tcbOf t x hk
    obtain ⟨x', hk', hyt'⟩ := hY.tcb t' ht'
    rw [hk] at hk'; cases hk'
    rw [hyt'] at hyt
    obtain ⟨h0, hp⟩ := optRef_some hyt
    obtain ⟨-, y, k, hks, -⟩ := hY.toSc t' ht' h0
    rw [hp] at hks
    exact ⟨y, k, hks⟩
  · -- ntfnTcb
    obtain ⟨n', hn', rfl⟩ := hCv.ntfn n xn hk
    obtain ⟨xn', hk', hr⟩ := hI.ntfn n' hn'
    rw [hk] at hk'; cases hk'
    rw [hr.bound] at ht
    obtain ⟨h0, hb⟩ := optRef_some ht
    obtain ⟨x, hkx, -⟩ := hI.tcb _ (hr.bound_mem h0)
    rw [hb] at hkx
    exact ⟨x, hkx⟩


/-- **`SchedValid` from P1's invariant `BlkOK`** (its queues `EpsOK` and
reply links `ReplyInv`, over the heap's sets) with the IPC relation over the
same sets, the call-stack and yield-to relations, the spec's objects those of
the sets, the endpoint readiness and the SC links. -/
theorem schedValid_of_blk {N E C Cs Ω Sg Scs Ac : Set U64} {Z : U64 → Nat} {B : Set (U64 × Fl4Spec.Word)}
    {H : Heap} {s : S} {σ : Fl4Spec.State Unit} {Lst : U64 → List U64}
    (hB : BlkOK st (Heap.tcbs H) Cs Ω H Sg (Heap.replies H) Scs (Heap.ntfns H) Z Ac s)
    (hI : Ipc.IpcRel N (Heap.tcbs H) E (Heap.replies H) B (L.mem s) σ)
    (hCv : ObjCover N (Heap.tcbs H) E (Heap.replies H) C σ)
    (hHE : ∀ e, H e = some .ep → e ∈ E) (hHN : ∀ n, H n = some .ntfn → n ∈ N)
    (hCR : CallRel (L.mem s) (Heap.replies H) C σ Lst) (hY : YieldRel (Heap.tcbs H) C (L.mem s) σ)
    (hC0 : ∀ c ∈ C, c ≠ 0#u64) (hRdy : EpRdyHyp σ) (hSL : ScLinkHyp σ) : SchedValid σ := by
  obtain ⟨⟨Q, R0, hSQ⟩, -, hX, -, -⟩ := hB
  obtain ⟨E', EQ, hW⟩ := hSQ.eps
  exact schedValid_of hI hSQ.tcbs hCv hW hHE hHN hX.2.1.toReplyInv0 hCR hY hC0 hRdy hSL

end

end

end Fl4Proofs.P3.Sched
