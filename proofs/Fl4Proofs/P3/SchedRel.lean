/-
P3 (DESIGN.md §9), scheduler: the state relation `SchedRel`.

**Single core.** The spec is single-core; FL4 has per-core state. The
relation fixes one core `c` (the current core, `L.cpu s = c`, its node
`NodePlaced`) and requires every TCB of `T` to have affinity `c`: then all
ready and release queues that hold a thread of `T` are core `c`'s, and the
other cores' nodes are not read. (Core `c` need not be 0; FL4's boot core is
0.) Domains: FL4 is built with one domain (`fl4_abi::config::NUM_DOMAINS =
1`), so the relation has the spec's `cur_domain` and every `tcb_domain` be
0, FL4's `CUR_DOMAIN` word and every TCB's domain word 0, and the spec's
ready queues of other domains empty.

`SchedCore st T c s Q R` is the part of P1's `SchedQueuesInv` that is about
the scheduler's own words (ghost lists `Q p` of the ready queue of priority
`p`, `R` of the release queue): queue relations, bitmap, `IN_QUEUES` flags,
affinities, priorities, the action word, the current and idle threads. It
leaves out what P1 also states about thread states (`runQ`, `runR`,
`actOK`) and endpoint/notification queues (`eps`): those are invariants, not
part of the relation, and the notification code changes them.

`SchedSpec` relates `SchedCore`'s lists and the node words to the spec:
* `ready_queues 0 p` is `Q p` (as `obj_ref`s); other domains are empty;
* `release_queue` is `R`;
* `cur_thread`, `cur_sc`, `cur_time`, `consumed_time`: the node's
  `CUR_THREAD`, `CUR_SC`, `CUR_TIME`, `CONSUMED` words; `reprogram_timer`:
  the `REPROGRAM` word is nonzero; `domain_time`: the kernel-global
  `DOMAIN_TIME` word; `idle_thread`: the node's `IDLE_THREAD` word;
* `scheduler_action`: the action word is 0 (resume), 1 (choose new) or the
  TCB to switch to (`ActRel`);
* each TCB's `tcb_sched_context` is its SC word (0 ↔ none), a nonzero SC
  word is in the ghost set `C` of scheduling contexts, and its priority word
  is `tcb_priority`;
* each SC of `C` is a scheduling context in the spec's heap whose
  `sc_refill_max` is the `REFILL_MAX` word (so `sc_active` agrees).

`SchedRel N T C c s σ` adds the placement facts the relation needs to be
stable under the notification code (`NtfnStep` / `NWrite`): `NPlaced T N`,
and the node, `CUR_DOMAIN`, `DOMAIN_TIME` and `REFILL_MAX` words are not
notification code writes. `SchedRel.stable` discharges `SchedHyps.stable` (NtfnSched.lean).
-/
import Fl4Proofs.P3.ScRel
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section Defs
variable {S : Type _} (st : machine.Store S) [L : LawfulStore st]

/-- The `CUR_DOMAIN` word (layout.rs `ks::CUR_DOMAIN`). -/
def curDomA (s : S) : U64 := core.num.U64.wrapping_add (L.ksb s) 8#u64
/-- The `DOMAIN_TIME` word (layout.rs `ks::DOMAIN_TIME`). -/
def dtA (s : S) : U64 := core.num.U64.wrapping_add (L.ksb s) 16#u64
/-- Word `o` of core `c`'s node. -/
def nodeW (s : S) (c o : U64) : U64 := L.mem s (L.nodeAt s c o)

/-- FL4's action word and the spec's scheduler action. -/
def ActRel (w : U64) : Fl4Spec.SchedulerAction → Prop
  | .resumeCurThread => w = 0#u64
  | .chooseNewThread => w = 1#u64
  | .switchThread t => w ≠ 0#u64 ∧ w ≠ 1#u64 ∧ w.bv = t

/-- The scheduler's own words on core `c`, with ghost lists `Q` (ready queue
per priority) and `R` (release queue); see the module docstring. -/
structure SchedCore (T : Set U64) (c : U64) (s : S) (Q : U64 → List U64) (R : List U64) : Prop where
  tcbs : TcbPlaced T
  node : NodePlaced st T s c
  cur : L.cpu s = c
  aff : ∀ t ∈ T, L.mem s (affA t) = c
  prio : ∀ t ∈ T, (L.mem s (prioA t)).val < 256
  ready : ReadyQueues st T s c Q
  release : QueueRel (L.mem s) T .Sched (L.relQ s c) R
  inQ : ∀ p : U64, p.val < 256 → ∀ t ∈ Q p, L.mem s (prioA t) = p
  queued : ∀ t ∈ T, ((L.mem s (inqA t) &&& sched.Q_QUEUED) ≠ 0#u64 ↔ t ∈ Q (L.mem s (prioA t)))
  released : ∀ t ∈ T, ((L.mem s (inqA t) &&& sched.Q_RELEASE) ≠ 0#u64 ↔ t ∈ R)
  excl : ∀ t ∈ T, t ∈ Q (L.mem s (prioA t)) → t ∉ R
  curT : nodeW st s c layout.node.CUR_THREAD ∈ T
  idleT : nodeW st s c layout.node.IDLE_THREAD ∈ T
  ksOut : ∀ t ∈ T, t.val + 2 ^ 12 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val

/-- The spec's priority of FL4 priority `p`. -/
def specPrio (p : U64) : Fl4Spec.Priority := BitVec.ofNat 8 p.val

/-- The scheduler state of the spec and FL4's (see the module docstring). -/
structure SchedSpec (T C : Set U64) (c : U64) (s : S) (Q : U64 → List U64) (R : List U64)
    (σ : Fl4Spec.State Unit) : Prop where
  rq : ∀ p : U64, p.val < 256 → σ.readyQueues 0 (specPrio p) = (Q p).map UScalar.bv
  rqDom : ∀ d p, d ≠ 0 → σ.readyQueues d p = []
  rel : σ.releaseQueue = R.map UScalar.bv
  curThread : σ.curThread = (nodeW st s c layout.node.CUR_THREAD).bv
  curSc : σ.curSc = (nodeW st s c layout.node.CUR_SC).bv
  curTime : σ.curTime = (nodeW st s c layout.node.CUR_TIME).bv
  consumed : σ.consumedTime = (nodeW st s c layout.node.CONSUMED).bv
  curDom : σ.curDomain = 0 ∧ L.mem s (curDomA st s) = 0#u64
  tcb : ∀ t ∈ T, ∃ x, σ.kheap t.bv = some (.tcb x) ∧ x.tcbDomain = 0 ∧ L.mem s (domA t) = 0#u64 ∧
    x.tcbSchedContext = optRef (L.mem s (scA t)) ∧ (L.mem s (prioA t)).val = x.tcbPriority.toNat
  scMem : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scA t) ∈ C
  scs : ∀ sc ∈ C, ∃ x n, σ.kheap sc.bv = some (.schedContext x n) ∧ ScRelW st s sc x n
  /-- The idle SC word is the spec's `idle_sc_ptr` (fixed at boot). -/
  idleSc : (nodeW st s c layout.node.IDLE_SC).bv = Fl4Spec.idleScPtr
  /-- `domain_time` is the `DOMAIN_TIME` word. -/
  domTime : σ.domainTime = (L.mem s (dtA st s)).bv
  /-- `idle_thread` is the node's `IDLE_THREAD` word. -/
  idleTh : σ.idleThread = (nodeW st s c layout.node.IDLE_THREAD).bv

/-- The scheduler relation for the notification proofs' `SR`. -/
structure SchedRel (N T C : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  placed : NPlaced T N
  nodeNW : ∀ o : U64, o.val < 4288 → ¬ NWrite N T (L.nodeAt s c o)
  domNW : ¬ NWrite N T (curDomA st s)
  dtNW : ¬ NWrite N T (dtA st s)
  /-- The SC words lie outside what the notification code writes, core
  `c`'s node, the TCBs and the kernel-global area. -/
  scOut : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, ScObj sc n a →
    ¬ NWrite N T a ∧
    (a.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧ (∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
    (a.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val)
  /-- Distinct SC objects do not overlap. -/
  scDisj : ∀ sc ∈ C, ∀ sc' ∈ C, sc ≠ sc' → ∀ x n x' n', σ.kheap sc.bv = some (.schedContext x n) →
    σ.kheap sc'.bv = some (.schedContext x' n') → ∀ a : U64, ScObj sc n a → ¬ ScObj sc' n' a
  /-- The action word is resume, choose-new, or a TCB (P1 `action`), and
  related to the spec's scheduler action. -/
  actW : nodeW st s c layout.node.SCHED_ACTION = 0#u64 ∨ nodeW st s c layout.node.SCHED_ACTION = 1#u64 ∨
    nodeW st s c layout.node.SCHED_ACTION ∈ T
  act : ActRel (nodeW st s c layout.node.SCHED_ACTION) σ.schedulerAction
  /-- `reprogram_timer` ↔ the `REPROGRAM` word is nonzero. -/
  repr : σ.reprogramTimer = decide (nodeW st s c layout.node.REPROGRAM ≠ 0#u64)
  /-- Every SC of `C` is on core `c` (its `CORE` word). -/
  core : ∀ sc ∈ C, L.mem s (scW sc 16#u64) = c
  lists : ∃ Q R, SchedCore st T c s Q R ∧ SchedSpec st T C c s Q R σ

end Defs

/-! ## If-then-else (non-deprecated forms) -/

theorem ite_t {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) : (if c then a else b) = a := by simp [h]
theorem ite_f {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : ¬ c) : (if c then a else b) = b := by simp [h]
theorem dite_t {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬ c → α} (h : c) :
    dite c a b = a h := by simp [h]

/-! ## Agreement: what the relation reads -/

section Agree
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- The TCB fields the scheduler relation reads: affinity, priority,
domain, SC, `IN_QUEUES`, `Sched` links. -/
def SchedField (K : U64) : Prop :=
  K = 3520#u64 ∨ K = 3448#u64 ∨ K = 3432#u64 ∨ K = 3464#u64 ∨ K = 3592#u64 ∨ K = 3480#u64 ∨ K = 3488#u64

/-- `s'` agrees with `s` on what `SchedRel` reads of FL4's memory. -/
structure SAgree (st : machine.Store S) [L : LawfulStore st] (T C : Set U64) (c : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  /-- Node words other than the action and reprogram words and the timer
  tree's root and min words (104, 112: read by no relation). -/
  node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 → o.val ≠ 104 → o.val ≠ 112 →
    o.val ≠ 88 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  tcb : ∀ y ∈ T, ∀ K, SchedField K → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  dom : L.mem s' (curDomA st s) = L.mem s (curDomA st s)
  dt : L.mem s' (dtA st s) = L.mem s (dtA st s)
  sc : ∀ sc ∈ C, ScAgree st s s' sc

theorem nodeAt_ksb {s s' : S} (h : L.ksb s' = L.ksb s) (c o : U64) : L.nodeAt s' c o = L.nodeAt s c o := by
  simp [LawfulStore.nodeAt, h]

theorem SAgree.nodeW {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {o : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h16 : o.val ≠ 16) (h56 : o.val ≠ 56) (h104 : o.val ≠ 104)
    (h112 : o.val ≠ 112) (h88 : o.val ≠ 88) : nodeW st s' c o = nodeW st s c o := by
  unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb h.ksb]; exact h.node o ho h8 h16 h56 h104 h112 h88

theorem SAgree.aff {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (affA y) = L.mem s (affA y) := h.tcb y hy _ (by simp [SchedField])
theorem SAgree.prio {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (prioA y) = L.mem s (prioA y) := h.tcb y hy _ (by simp [SchedField])
theorem SAgree.dom' {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (domA y) = L.mem s (domA y) := h.tcb y hy _ (by simp [SchedField])
theorem SAgree.scw {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (scA y) = L.mem s (scA y) := h.tcb y hy _ (by simp [SchedField])
theorem SAgree.inq {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (inqA y) = L.mem s (inqA y) := h.tcb y hy _ (by simp [SchedField])
theorem SAgree.next {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) := h.tcb y hy _ (by simp [SchedField, nextOff])
theorem SAgree.prev {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y) := h.tcb y hy _ (by simp [SchedField, prevOff])

theorem nodePlaced_ksb {T : Set U64} {s s' : S} {c : U64} (hN : NodePlaced st T s c) (hk : L.ksb s' = L.ksb s) :
    NodePlaced st T s' c := by
  have e : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  exact ⟨by rw [e]; exact hN.align, by rw [e]; exact hN.fits, by rw [e]; exact hN.disj⟩

theorem SAgree.views {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') : ViewsEq st s s' c := by
  refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
  · simp only [LawfulStore.rqQ, nodeAt_ksb h.ksb]
    rw [h.node _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
        (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
      h.node _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
        (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
        (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)]
  · simp only [LawfulStore.l1W, nodeAt_ksb h.ksb]
    exact h.node _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
      (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
  · simp only [LawfulStore.l2W, nodeAt_ksb h.ksb]
    exact h.node _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)

theorem SAgree.links {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') {q xs}
    (hq : QueueRel (L.mem s) T .Sched q xs) : QueueRel (L.mem s') T .Sched q xs :=
  ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
    ⟨h.prev (hq.mem y hy), h.next (hq.mem y hy)⟩⟩


/-- The TCB fields `SchedCore` reads: affinity, priority, `IN_QUEUES`,
`Sched` links. -/
def CoreField (K : U64) : Prop :=
  K = 3520#u64 ∨ K = 3448#u64 ∨ K = 3592#u64 ∨ K = 3480#u64 ∨ K = 3488#u64

/-- `s'` agrees with `s` on what `SchedCore` reads. -/
structure CAgree (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (c : U64) (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  node : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 → o.val ≠ 40 → o.val ≠ 48 → o.val ≠ 24 →
    o.val ≠ 104 → o.val ≠ 112 → o.val ≠ 88 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  tcb : ∀ y ∈ T, ∀ K, CoreField K → L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)

theorem SAgree.toC {T C : Set U64} {c : U64} {s s' : S} (h : SAgree st T C c s s') : CAgree st T c s s' :=
  ⟨h.ksb, h.cpu, fun o h1 h2 h3 h4 _ _ _ h5 h6 h7 => h.node o h1 h2 h3 h4 h5 h6 h7, fun y hy K hK => h.tcb y hy K (by
    rcases hK with h | h | h | h | h <;> simp [SchedField, h])⟩

theorem CAgree.aff {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (affA y) = L.mem s (affA y) := h.tcb y hy _ (by simp [CoreField])
theorem CAgree.prio {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (prioA y) = L.mem s (prioA y) := h.tcb y hy _ (by simp [CoreField])
theorem CAgree.inq {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (inqA y) = L.mem s (inqA y) := h.tcb y hy _ (by simp [CoreField])
theorem CAgree.next {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (nextA .Sched y) = L.mem s (nextA .Sched y) := h.tcb y hy _ (by simp [CoreField, nextOff])
theorem CAgree.prev {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {y : U64} (hy : y ∈ T) :
    L.mem s' (prevA .Sched y) = L.mem s (prevA .Sched y) := h.tcb y hy _ (by simp [CoreField, prevOff])

theorem CAgree.nodeW {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {o : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h16 : o.val ≠ 16) (h56 : o.val ≠ 56) (h40 : o.val ≠ 40)
    (h48 : o.val ≠ 48) (h24 : o.val ≠ 24) (h104 : o.val ≠ 104) (h112 : o.val ≠ 112) (h88 : o.val ≠ 88) :
    nodeW st s' c o = nodeW st s c o := by
  unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb h.ksb]; exact h.node o ho h8 h16 h56 h40 h48 h24 h104 h112 h88

theorem CAgree.views {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') : ViewsEq st s s' c := by
  refine ⟨fun p hp => ?_, ?_, fun g hg => ?_⟩
  · simp only [LawfulStore.rqQ, nodeAt_ksb h.ksb]
    rw [h.node _ (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
        (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega)
        (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega) (by rw [rqOff_val hp]; omega),
      h.node _ (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
        (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)
        (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega) (by rw [rqTailOff_val hp]; omega)]
  · simp only [LawfulStore.l1W, nodeAt_ksb h.ksb]
    exact h.node _ (by rw [l1Off_val]; omega) (by rw [l1Off_val]) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
      (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
      (by rw [l1Off_val]; omega) (by rw [l1Off_val]; omega)
  · simp only [LawfulStore.l2W, nodeAt_ksb h.ksb]
    exact h.node _ (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)
      (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega) (by rw [l2Off_val hg]; omega)

theorem CAgree.links {T : Set U64} {c : U64} {s s' : S} (h : CAgree st T c s s') {q xs}
    (hq : QueueRel (L.mem s) T .Sched q xs) : QueueRel (L.mem s') T .Sched q xs :=
  ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy =>
    ⟨h.prev (hq.mem y hy), h.next (hq.mem y hy)⟩⟩

theorem SchedCore.agree {T : Set U64} {c : U64} {s s' : S} {Q : U64 → List U64} {R : List U64}
    (h : SchedCore st T c s Q R) (ha : CAgree st T c s s') : SchedCore st T c s' Q R := by
  have hv := ha.views
  have hrel : L.relQ s' c = L.relQ s c := by
    simp only [LawfulStore.relQ, nodeAt_ksb ha.ksb]
    rw [ha.node _ (by rw [relh_val]; omega) (by rw [relh_val]) (by rw [relh_val]; omega) (by rw [relh_val]; omega)
        (by rw [relh_val]; omega) (by rw [relh_val]; omega) (by rw [relh_val]; omega) (by rw [relh_val]; omega)
        (by rw [relh_val]; omega) (by rw [relh_val]; omega),
      ha.node _ (by rw [relt_val]; omega) (by rw [relt_val]) (by rw [relt_val]; omega) (by rw [relt_val]; omega)
        (by rw [relt_val]; omega) (by rw [relt_val]; omega) (by rw [relt_val]; omega) (by rw [relt_val]; omega)
        (by rw [relt_val]; omega) (by rw [relt_val]; omega)]
  refine ⟨h.tcbs, nodePlaced_ksb h.node ha.ksb, ha.cpu.trans h.cur, fun t ht => (ha.aff ht).trans (h.aff t ht),
    fun t ht => (ha.prio ht) ▸ h.prio t ht,
    ⟨h.ready.1.agree hv.1 fun p hp y hy =>
      ⟨ha.next ((h.ready.1.rel p hp).mem y hy), ha.prev ((h.ready.1.rel p hp).mem y hy)⟩, h.ready.2.views hv⟩,
    hrel ▸ ha.links h.release,
    fun p hp t ht => (ha.prio ((h.ready.1.rel p hp).mem t ht)).trans (h.inQ p hp t ht),
    fun t ht => by rw [ha.inq ht, ha.prio ht]; exact h.queued t ht,
    fun t ht => by rw [ha.inq ht]; exact h.released t ht,
    fun t ht => by rw [ha.prio ht]; exact h.excl t ht, ?_, ?_, by rw [ha.ksb]; exact h.ksOut⟩
  · rw [ha.nodeW (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]
    exact h.curT
  · rw [ha.nodeW (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
      (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])
        (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]
    exact h.idleT

theorem curDomA_ksb {s s' : S} (h : L.ksb s' = L.ksb s) : curDomA st s' = curDomA st s := by
  simp [curDomA, h]

theorem dtA_ksb {s s' : S} (h : L.ksb s' = L.ksb s) : dtA st s' = dtA st s := by
  simp [dtA, h]

theorem dtA_aligned {T : Set U64} {s : S} {c : U64} (hN : NodePlaced st T s c) : Aligned (dtA st s) := by
  have h1 := hN.align; have h2 := hN.fits
  unfold Aligned dtA
  simp only [LawfulStore.nodeBase] at h1 h2
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

theorem dtA_val {T : Set U64} {s : S} {c : U64} (hN : NodePlaced st T s c) :
    (dtA st s).val = (L.ksb s).val + 16 := by
  have h2 := hN.fits
  simp only [LawfulStore.nodeBase] at h2
  simp [dtA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega

/-- The FL4 side of `SchedSpec` under agreement. -/
theorem SchedSpec.agree {T C : Set U64} {c : U64} {s s' : S} {Q : U64 → List U64} {R : List U64}
    {σ : Fl4Spec.State Unit} (h : SchedSpec st T C c s Q R σ) (ha : SAgree st T C c s s') :
    SchedSpec st T C c s' Q R σ := by
  have w : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 16 → o.val ≠ 56 → o.val ≠ 104 → o.val ≠ 112 →
      o.val ≠ 88 → nodeW st s' c o = nodeW st s c o :=
    fun o h1 h2 h3 h4 h5 h6 h7 => ha.nodeW h1 h2 h3 h4 h5 h6 h7
  refine ⟨h.rq, h.rqDom, h.rel, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_, fun t ht => ?_, fun sc hsc => ?_,
    by rw [w _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact h.idleSc, by rw [dtA_ksb ha.ksb, ha.dt]; exact h.domTime,
    by rw [w layout.node.IDLE_THREAD (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact h.idleTh⟩
  · rw [w _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact h.curThread
  · rw [w _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]
    exact h.curSc
  · rw [w _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]
    exact h.curTime
  · rw [w _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]
    exact h.consumed
  · rw [curDomA_ksb ha.ksb, ha.dom]; exact h.curDom
  · obtain ⟨x, hk, h1, h2, h3, h4⟩ := h.tcb t ht
    exact ⟨x, hk, h1, by rw [ha.dom' ht]; exact h2, by rw [ha.scw ht]; exact h3, by rw [ha.prio ht]; exact h4⟩
  · rw [ha.scw ht]; exact h.scMem t ht
  · obtain ⟨x, n, hk, e⟩ := h.scs sc hsc
    exact ⟨x, n, hk, e.agree (ha.sc sc hsc)⟩

/-- The SC words of `C` under agreement: the same words. -/
theorem SchedSpec.rmax_eq {T C : Set U64} {c : U64} {s s' : S} {Q : U64 → List U64} {R : List U64}
    {σ : Fl4Spec.State Unit} (h : SchedSpec st T C c s Q R σ) (ha : ∀ sc ∈ C, ScAgree st s s' sc) :
    ∀ sc ∈ C, L.rmax s' sc = L.rmax s sc := by
  intro sc hsc
  obtain ⟨x, n, -, e⟩ := h.scs sc hsc
  simp only [LawfulStore.rmax, maxA_eq]
  exact ha sc hsc _ (e.hdr (by simp) (by simp)).1 (e.hdr (by simp) (by simp)).2

/-- The `CORE` words of the SCs of `C` under agreement. -/
theorem SchedSpec.core_eq {T C : Set U64} {c : U64} {s s' : S} {Q : U64 → List U64} {R : List U64}
    {σ : Fl4Spec.State Unit} (h : SchedSpec st T C c s Q R σ) (ha : ∀ sc ∈ C, ScAgree st s s' sc)
    (hc : ∀ sc ∈ C, L.mem s (scW sc 16#u64) = c) : ∀ sc ∈ C, L.mem s' (scW sc 16#u64) = c := by
  intro sc hsc
  obtain ⟨x, n, -, e⟩ := h.scs sc hsc
  rw [ha sc hsc _ (e.hdr (by simp) (by simp)).1 (e.hdr (by simp) (by simp)).2]; exact hc sc hsc

/-- The spec's SC objects in `σ'` were SC objects of the same size in `σ`. -/
def SzKeep (σ σ' : Fl4Spec.State Unit) : Prop :=
  ∀ p x n, σ'.kheap p = some (.schedContext x n) → ∃ x0, σ.kheap p = some (.schedContext x0 n)

theorem SzKeep.of_kheap {σ σ' : Fl4Spec.State Unit} (h : σ'.kheap = σ.kheap) : SzKeep σ σ' :=
  fun p x n hp => ⟨x, by rw [← h]; exact hp⟩

theorem SzKeep.updK {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {o o' : Fl4Spec.KernelObject}
    (hk : σ.kheap p = some o) (ho : ∀ x n, o' = .schedContext x n → ∃ x0, o = .schedContext x0 n) :
    SzKeep σ (updK σ p o') := by
  intro q x n hq
  by_cases e : q = p
  · subst e; simp only [updK_kheap, Function.update_self, Option.some.injEq] at hq
    obtain ⟨x0, h0⟩ := ho x n hq; exact ⟨x0, by rw [hk, h0]⟩
  · simp only [updK_kheap, ne_eq, e, not_false_eq_true, Function.update_of_ne] at hq; exact ⟨x, hq⟩

theorem scOut_transfer {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit} (hk : L.ksb s' = L.ksb s)
    (hz : SzKeep σ σ')
    (h : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, ScObj sc n a → ¬ NWrite N T a ∧
      (a.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧ (∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
      (a.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val)) :
    ∀ sc ∈ C, ∀ x n, σ'.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, ScObj sc n a → ¬ NWrite N T a ∧
      (a.val < L.nodeBase s' c ∨ L.nodeBase s' c + 4288 ≤ a.val) ∧ (∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
      (a.val + 8 ≤ (L.ksb s').val ∨ (L.ksb s').val + 13568 ≤ a.val) := by
  intro sc hsc x n hx a ha
  obtain ⟨x0, hx0⟩ := hz _ x n hx
  have := h sc hsc x0 n hx0 a ha
  simp only [LawfulStore.nodeBase, hk] at this ⊢; exact this

theorem scDisj_transfer {C : Set U64} {σ σ' : Fl4Spec.State Unit} (hz : SzKeep σ σ')
    (h : ∀ sc ∈ C, ∀ sc' ∈ C, sc ≠ sc' → ∀ x n x' n', σ.kheap sc.bv = some (.schedContext x n) →
      σ.kheap sc'.bv = some (.schedContext x' n') → ∀ a : U64, ScObj sc n a → ¬ ScObj sc' n' a) :
    ∀ sc ∈ C, ∀ sc' ∈ C, sc ≠ sc' → ∀ x n x' n', σ'.kheap sc.bv = some (.schedContext x n) →
      σ'.kheap sc'.bv = some (.schedContext x' n') → ∀ a : U64, ScObj sc n a → ¬ ScObj sc' n' a := by
  intro sc hsc sc' hsc' hne x n x' n' hx hx' a
  obtain ⟨x0, hx0⟩ := hz _ x n hx
  obtain ⟨x0', hx0'⟩ := hz _ x' n' hx'
  exact h sc hsc sc' hsc' hne x0 n x0' n' hx0 hx0' a

/-- `scOut` for a word the relation reads. -/
theorem SchedRel.scOutIn {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc a : U64} (hsc : sc ∈ C) (hin : ScIn st s sc a) : ¬ NWrite N T a ∧
      (a.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧ (∀ t ∈ T, a.val < t.val ∨ t.val + 4096 ≤ a.val) ∧
      (a.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val) := by
  obtain ⟨Q, R, -, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  exact hS.scOut sc hsc x n hk a (hx.in_obj hin)

/-- A word the relation reads of one SC is outside the object of another. -/
theorem SchedRel.scDisjIn {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) {sc sc' a : U64} (hsc : sc ∈ C) (hsc' : sc' ∈ C) (hne : sc ≠ sc')
    {x' : Fl4Spec.SchedContext} {n' : Nat} (hk' : σ.kheap sc'.bv = some (.schedContext x' n'))
    (hin : ScIn st s sc a) : ¬ ScObj sc' n' a := by
  obtain ⟨Q, R, -, hs⟩ := hS.lists
  obtain ⟨x, n, hk, hx⟩ := hs.scs sc hsc
  exact hS.scDisj sc hsc sc' hsc' hne x n x' n' hk hk' a (hx.in_obj hin)

end Agree

/-! ## Stability under the notification code -/

section Stable
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- A TCB field the notification code does not write. -/
theorem tfield_not_nwrite {N T : Set U64} (hP : NPlaced T N) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096)
    (hKw : K ≠ 3328#u64 ∧ K ≠ 3336#u64 ∧ K ≠ 256#u64 ∧ K ≠ 3496#u64 ∧ K ≠ 3504#u64) :
    ¬ NWrite N T (core.num.U64.wrapping_add y K) := by
  have hya := hP.tcb y hy
  rintro (⟨n, hn, h1, h2⟩ | ⟨t, ht, e | e | e | e | e⟩)
  · rw [tfield_val hya hK] at h1 h2
    have := hP.disj n hn y hy; omega
  · rw [tStA_eq, tt_eq_iff hya (hP.tcb t ht) hK (by simp)] at e; exact hKw.1 e.2
  · rw [tBlockA_eq, tt_eq_iff hya (hP.tcb t ht) hK (by simp)] at e; exact hKw.2.1 e.2
  · rw [badgeRegA_eq, tt_eq_iff hya (hP.tcb t ht) hK (by simp)] at e; exact hKw.2.2.1 e.2
  · rw [nextEp_eq, tt_eq_iff hya (hP.tcb t ht) hK (by simp)] at e; exact hKw.2.2.2.1 e.2
  · rw [prevEp_eq, tt_eq_iff hya (hP.tcb t ht) hK (by simp)] at e; exact hKw.2.2.2.2 e.2

theorem schedField_ok {K : U64} (h : SchedField K) :
    K.val < 4096 ∧ K.val % 8 = 0 ∧ (K ≠ 3328#u64 ∧ K ≠ 3336#u64 ∧ K ≠ 256#u64 ∧ K ≠ 3496#u64 ∧ K ≠ 3504#u64) := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

/-- Writes of the notification code keep what `SchedRel` reads. -/
theorem sagree_of_nwrite {N T C : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hw : WritesIn st s s' (NWrite N T)) : SAgree st T C c s s' := by
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ _ => hw.mem_eq (nodeAt_aligned hc.node ho h8) (hS.nodeNW o ho),
    fun y hy K hK => ?_, hw.mem_eq ?_ hS.domNW, hw.mem_eq ?_ hS.dtNW,
    fun sc hsc a ha hin => hw.mem_eq ha (hS.scOutIn hsc hin).1⟩
  · obtain ⟨h1, h2, h3⟩ := schedField_ok hK
    exact hw.mem_eq (field_aligned (hc.tcbs y hy) h1 h2) (tfield_not_nwrite hS.placed hy h1 h3)
  · have h1 := hc.node.align
    have h2 := hc.node.fits
    unfold Aligned curDomA
    simp only [LawfulStore.nodeBase] at h1 h2
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    omega
  · have h1 := hc.node.align
    have h2 := hc.node.fits
    unfold Aligned dtA
    simp only [LawfulStore.nodeBase] at h1 h2
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
    omega

/-! The spec side of a notification step. -/

theorem NtfnStep.abs {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') :
    σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
    σ'.schedulerAction = σ.schedulerAction ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.reprogramTimer = σ.reprogramTimer ∧ σ'.curDomain = σ.curDomain := by
  have e := h.2.1
  exact ⟨(by have := congrArg Fl4Spec.AbstractState.readyQueues e; exact this), (by have := congrArg Fl4Spec.AbstractState.releaseQueue e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curThread e; exact this), (by have := congrArg Fl4Spec.AbstractState.schedulerAction e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curSc e; exact this), (by have := congrArg Fl4Spec.AbstractState.curTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.consumedTime e; exact this), (by have := congrArg Fl4Spec.AbstractState.reprogramTimer e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curDomain e; exact this)⟩

theorem NtfnStep.domainTime {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') : σ'.domainTime = σ.domainTime := by
  have := congrArg Fl4Spec.AbstractState.domainTime h.2.1; exact this

theorem NtfnStep.idleThread {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') : σ'.idleThread = σ.idleThread := by
  have := congrArg Fl4Spec.AbstractState.idleThread h.2.1; exact this

theorem NtfnStep.tcbSched {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) : ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbDomain = x.tcbDomain ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbPriority = x.tcbPriority := by
  rcases h.2.2 p with e | ⟨a, b, ha, -, -, -⟩ | ⟨a, b, ha, hb, e⟩
  · exact ⟨x, e.trans hk, rfl, rfl, rfl⟩
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha
    refine ⟨b, hb, ?_, ?_, ?_⟩ <;> rw [e]

theorem NtfnStep.sc {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') {p : Fl4Spec.ObjRef}
    {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext x n)) :
    σ'.kheap p = some (.schedContext x n) := by
  rcases h.2.2 p with e | ⟨a, b, ha, -, -, -⟩ | ⟨a, b, ha, -, -⟩
  · exact e.trans hk
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha

theorem SzKeep.ntfnStep {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') : SzKeep σ σ' := by
  intro p x n hp
  rcases h.2.2 p with e | ⟨a, b, -, hb, -, -⟩ | ⟨a, b, -, hb, -⟩
  · exact ⟨x, e ▸ hp⟩
  · rw [hp] at hb; cases hb
  · rw [hp] at hb; cases hb

/-- A notification step that may also change notifications' bound TCB and
SC, reply objects, and TCBs' `tcb_yield_to`: the scheduler relation does not
read them. -/
def NtfnStepW (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ'.exst = σ.exst ∧ { σ'.toAbstractState with kheap := σ.kheap } = σ.toAbstractState ∧
  ∀ p, σ'.kheap p = σ.kheap p ∨
    (∃ x y, σ.kheap p = some (.notification x) ∧ σ'.kheap p = some (.notification y)) ∨
    (∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧
      y = { x with tcbState := y.tcbState, tcbArch := y.tcbArch, tcbYieldTo := y.tcbYieldTo }) ∨
    (∃ x y, σ.kheap p = some (.reply x) ∧ σ'.kheap p = some (.reply y))

theorem NtfnStep.weak {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') : NtfnStepW σ σ' := by
  refine ⟨h.1, h.2.1, fun p => ?_⟩
  rcases h.2.2 p with e | ⟨x, y, h1, h2, -⟩ | e
  · exact Or.inl e
  · exact Or.inr (Or.inl ⟨x, y, h1, h2⟩)
  · obtain ⟨x, y, h1, h2, e⟩ := e
    exact Or.inr (Or.inr (Or.inl ⟨x, y, h1, h2, by rw [e]⟩))

theorem NtfnStepW.abs {σ σ' : Fl4Spec.State Unit} (h : NtfnStepW σ σ') :
    σ'.readyQueues = σ.readyQueues ∧ σ'.releaseQueue = σ.releaseQueue ∧ σ'.curThread = σ.curThread ∧
    σ'.schedulerAction = σ.schedulerAction ∧ σ'.curSc = σ.curSc ∧ σ'.curTime = σ.curTime ∧
    σ'.consumedTime = σ.consumedTime ∧ σ'.reprogramTimer = σ.reprogramTimer ∧ σ'.curDomain = σ.curDomain := by
  have e := h.2.1
  exact ⟨(by have := congrArg Fl4Spec.AbstractState.readyQueues e; exact this), (by have := congrArg Fl4Spec.AbstractState.releaseQueue e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curThread e; exact this), (by have := congrArg Fl4Spec.AbstractState.schedulerAction e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curSc e; exact this), (by have := congrArg Fl4Spec.AbstractState.curTime e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.consumedTime e; exact this), (by have := congrArg Fl4Spec.AbstractState.reprogramTimer e; exact this),
    (by have := congrArg Fl4Spec.AbstractState.curDomain e; exact this)⟩

theorem NtfnStepW.domainTime {σ σ' : Fl4Spec.State Unit} (h : NtfnStepW σ σ') : σ'.domainTime = σ.domainTime := by
  have := congrArg Fl4Spec.AbstractState.domainTime h.2.1; exact this

theorem NtfnStepW.idleThread {σ σ' : Fl4Spec.State Unit} (h : NtfnStepW σ σ') : σ'.idleThread = σ.idleThread := by
  have := congrArg Fl4Spec.AbstractState.idleThread h.2.1; exact this

theorem NtfnStepW.tcbSched {σ σ' : Fl4Spec.State Unit} (h : NtfnStepW σ σ') {p : Fl4Spec.ObjRef} {x : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) : ∃ y, σ'.kheap p = some (.tcb y) ∧ y.tcbDomain = x.tcbDomain ∧
      y.tcbSchedContext = x.tcbSchedContext ∧ y.tcbPriority = x.tcbPriority := by
  rcases h.2.2 p with e | ⟨a, b, ha, -⟩ | ⟨a, b, ha, hb, e⟩ | ⟨a, b, ha, -⟩
  · exact ⟨x, e.trans hk, rfl, rfl, rfl⟩
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha
    refine ⟨b, hb, ?_, ?_, ?_⟩ <;> rw [e]
  · rw [hk] at ha; cases ha

theorem NtfnStepW.sc {σ σ' : Fl4Spec.State Unit} (h : NtfnStepW σ σ') {p : Fl4Spec.ObjRef}
    {x : Fl4Spec.SchedContext} {n : Nat} (hk : σ.kheap p = some (.schedContext x n)) :
    σ'.kheap p = some (.schedContext x n) := by
  rcases h.2.2 p with e | ⟨a, b, ha, -⟩ | ⟨a, b, ha, -, -⟩ | ⟨a, b, ha, -⟩
  · exact e.trans hk
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha
  · rw [hk] at ha; cases ha

theorem SzKeep.ntfnStepW {σ σ' : Fl4Spec.State Unit} (h : NtfnStepW σ σ') : SzKeep σ σ' := by
  intro p x n hp
  rcases h.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb⟩
  · exact ⟨x, e ▸ hp⟩
  · rw [hp] at hb; cases hb
  · rw [hp] at hb; cases hb
  · rw [hp] at hb; cases hb

/-- **The scheduler relation from agreeing memory** (`SAgree`, and the action
and reprogram words unchanged) and a spec step that keeps what it reads
(`NtfnStepW`). -/
theorem SchedRel.of_sagree {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (ha : SAgree st T C c s s')
    (hact : nodeW st s' c layout.node.SCHED_ACTION = nodeW st s c layout.node.SCHED_ACTION)
    (hrp : nodeW st s' c layout.node.REPROGRAM = nodeW st s c layout.node.REPROGRAM)
    (hn : NtfnStepW σ σ') : SchedRel st N T C c s' σ' := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hs' := hs.agree ha
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := NtfnStepW.abs hn
  refine ⟨hS.placed, fun o ho => by rw [nodeAt_ksb ha.ksb]; exact hS.nodeNW o ho,
    by rw [curDomA_ksb ha.ksb]; exact hS.domNW, by rw [dtA_ksb ha.ksb]; exact hS.dtNW,
    scOut_transfer ha.ksb (SzKeep.ntfnStepW hn) hS.scOut,
    scDisj_transfer (SzKeep.ntfnStepW hn) hS.scDisj, by rw [hact]; exact hS.actW,
    by rw [hact, e4]; exact hS.act, by rw [hrp, e8]; exact hS.repr, hs.core_eq ha.sc hS.core, Q, R,
    hc.agree ha.toC, ?_⟩
  refine ⟨fun p hp => by rw [e1]; exact hs'.rq p hp, fun d p hd => by rw [e1]; exact hs'.rqDom d p hd,
    by rw [e2]; exact hs'.rel, by rw [e3]; exact hs'.curThread,
    by rw [e5]; exact hs'.curSc, by rw [e6]; exact hs'.curTime, by rw [e7]; exact hs'.consumed,
    by rw [e9]; exact hs'.curDom, fun t ht => ?_, hs'.scMem,
    fun sc hsc => ?_, hs'.idleSc, by rw [NtfnStepW.domainTime hn]; exact hs'.domTime,
    by rw [NtfnStepW.idleThread hn]; exact hs'.idleTh⟩
  · obtain ⟨x, hk, h1, h2, h3, h4⟩ := hs'.tcb t ht
    obtain ⟨y, hky, f1, f2, f3⟩ := NtfnStepW.tcbSched hn hk
    exact ⟨y, hky, f1.trans h1, h2, f2.trans h3, f3 ▸ h4⟩
  · obtain ⟨x, n, hk, e⟩ := hs'.scs sc hsc
    exact ⟨x, n, NtfnStepW.sc hn hk, e⟩

/-- **The scheduler relation is kept by a notification step** that may also
change notifications' bound TCB and SC (`NtfnStepW`). -/
theorem SchedRel.stableW {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hw : WritesIn st s s' (NWrite N T)) (hn : NtfnStepW σ σ') :
    SchedRel st N T C c s' σ' := by
  have ha := sagree_of_nwrite hS hw
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  refine hS.of_sagree ha ?_ ?_ hn
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hw.1]
    exact hw.mem_eq (nodeAt_aligned hc.node (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
      (hS.nodeNW _ (by simp [layout.node.SCHED_ACTION]))
  · unfold Fl4Proofs.P3.Sched.nodeW; rw [nodeAt_ksb hw.1]
    exact hw.mem_eq (nodeAt_aligned hc.node (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
      (hS.nodeNW _ (by simp [layout.node.REPROGRAM]))

/-- **`SchedHyps.stable`**: the scheduler relation is kept by the notification
code's own steps. -/
theorem SchedRel.stable {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hw : WritesIn st s s' (NWrite N T)) (hn : NtfnStep σ σ') :
    SchedRel st N T C c s' σ' :=
  hS.stableW hw (NtfnStep.weak hn)

end Stable

end

end Fl4Proofs.P3.Sched
