/-
P3 (DESIGN.md §9): **the primitive steps of the decodes, for the composite
relation** (TopXAll's `XTop`). A decode's post records that its run is a
composition of primitive steps by `StepClosed`: every relation `Q` closed
under the current thread's restart (`restart`), a kernel-state step (`ks`:
`KsW` words, the spec's `KsStep`, the domain words kept, the IRQ and IO-port
relations kept, an arch operation of the interrupt or IO port decodes, `ArchIrqStep`) and a capability
insert into a CNode (`slot`, with the CSpace relation after), a CNode-only
step (`cslot`: the spec's `CnK` changing CNodes only, FL4's slot words, the
CSpace relation after: a move, a swap), a scheduler
step (`sched`: `SchedStep`, the queue, action and domain-schedule words and
the scheduler relation after at every family of sets) and the deletion of a
notification cap (`del`, `delete_one`) relates its start and end. XTopStep
proves `XTop`'s instance; the decodes stay free of the composite relation's
definitions.
-/
import Fl4Proofs.P3.DomKeep
import Fl4Proofs.P3.IoBitmap
import Fl4Proofs.P3.MdbStepVs
import Fl4Proofs.P3.CnodeRevoke
import Fl4Proofs.P3.VsInsFrame
import Fl4Proofs.P3.SchedRel
import Fl4Proofs.P3.SpecCnK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The kernel-global words a kernel-state step may write: past the current
domain and domain time words, not the kernel root, not the IRQ node's CTEs
(`ksb + 1248 .. ksb + 5344`, written by slot steps only). -/
def KsW (kb b : U64) : Prop := ∃ K : U64, 24 ≤ K.val ∧ K.val < 13568 ∧ K.val ≠ 48 ∧ b.val = kb.val + K.val ∧
  (K.val < 1248 ∨ 5344 ≤ K.val)

/-- The spec's kernel-state steps: only the interrupt states, the IRQ masks,
the IO ports, the arch IRQ states and the domain schedule change. -/
structure KsStep (σ σ' : Fl4Spec.State Unit) : Prop where
  kh : σ'.kheap = σ.kheap
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  rq : σ'.readyQueues = σ.readyQueues
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  act : σ'.schedulerAction = σ.schedulerAction
  csc : σ'.curSc = σ.curSc
  ctime : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  repr : σ'.reprogramTimer = σ.reprogramTimer
  cdom : σ'.curDomain = σ.curDomain
  dtime : σ'.domainTime = σ.domainTime
  idle : σ'.idleThread = σ.idleThread
  inode : σ'.interruptIrqNode = σ.interruptIrqNode
  um : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory
  asidT : σ'.archState.x64AsidTable = σ.archState.x64AsidTable
  gpml4 : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4
  cr3 : σ'.archState.x64CurrentCr3 = σ.archState.x64CurrentCr3

theorem KsStep.refl (σ : Fl4Spec.State Unit) : KsStep σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A word of a slot of the typed heap. -/
def InSlot (th : TypedHeap) (b : U64) : Prop := ∃ a, IsSlot th a ∧ a.val ≤ b.val ∧ b.val < a.val + 32

/-- The spec's scheduler steps: only the ready queues, the scheduler
action, the domain time and index and the domain schedule's start change. -/
structure SchedK (σ σ' : Fl4Spec.State Unit) : Prop where
  kh : σ'.kheap = σ.kheap
  cdt : σ'.cdt = σ.cdt
  orig : σ'.isOriginalCap = σ.isOriginalCap
  rel : σ'.releaseQueue = σ.releaseQueue
  ct : σ'.curThread = σ.curThread
  csc : σ'.curSc = σ.curSc
  ctime : σ'.curTime = σ.curTime
  cons : σ'.consumedTime = σ.consumedTime
  repr : σ'.reprogramTimer = σ.reprogramTimer
  cdom : σ'.curDomain = σ.curDomain
  idle : σ'.idleThread = σ.idleThread
  inode : σ'.interruptIrqNode = σ.interruptIrqNode
  ist : σ'.interruptStates = σ.interruptStates
  ms : σ'.machineState = σ.machineState
  arch : σ'.archState = σ.archState

theorem SchedK.refl (σ : Fl4Spec.State Unit) : SchedK σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SchedK.trans {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : SchedK σ1 σ2) (h2 : SchedK σ2 σ3) : SchedK σ1 σ3 :=
  ⟨h2.kh.trans h1.kh, h2.cdt.trans h1.cdt, h2.orig.trans h1.orig, h2.rel.trans h1.rel, h2.ct.trans h1.ct,
    h2.csc.trans h1.csc, h2.ctime.trans h1.ctime, h2.cons.trans h1.cons, h2.repr.trans h1.repr,
    h2.cdom.trans h1.cdom, h2.idle.trans h1.idle, h2.inode.trans h1.inode, h2.ist.trans h1.ist,
    h2.ms.trans h1.ms, h2.arch.trans h1.arch⟩

/-- **The domain schedule relation** as DomDecode states it (`DomRel`,
`domRel_iff`), for the steps' statements: the table's domain and duration
words are the spec's `domain_list` (2 entries), and the start word its
`domain_start_index`. -/
def DomRelW (m : U64 → U64) (kb : U64) (σ : Fl4Spec.State Unit) : Prop :=
  σ.domainList.length = 2 ∧
  (∀ i : U64, i.val < 2 →
    σ.domainList[i.val]? = some
      (BitVec.ofNat 8 (m (core.num.U64.wrapping_add kb
        (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)))).val,
       BitVec.ofNat 56 (m (core.num.U64.wrapping_add kb (core.num.U64.wrapping_add
        (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)) 8#u64))).val) ∧
    (m (core.num.U64.wrapping_add kb
      (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)))).val < 2 ^ 8 ∧
    (m (core.num.U64.wrapping_add kb (core.num.U64.wrapping_add
      (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)) 8#u64))).val < 2 ^ 56 ∧
    (m (core.num.U64.wrapping_add kb (core.num.U64.wrapping_add
      (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)) 8#u64)) = 0#u64 →
      m (core.num.U64.wrapping_add kb
        (core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64))) = 0#u64)) ∧
  σ.domainStartIndex = (m (core.num.U64.wrapping_add kb 32#u64)).val

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- The arch operations of the interrupt and IO port decodes: none, an
IRQ's mask, an IOAPIC pin's (remapped) programming, a port access. -/
def ArchIrqStep (a a' : A) : Prop :=
  a' = a ∨ (∃ irq b, arI.mask_irq a irq b = ok a') ∨
    (∃ i p l po v b, arI.ioapic_map a i p l po v = ok (b, a')) ∨
    (∃ i p l po v h b, arI.ioapic_map_remapped a i p l po v h = ok (b, a')) ∨
    (∃ p z v, arI.port_in a p z = ok (v, a')) ∨ (∃ p z d, arI.port_out a p z d = ok a')

/-- The kernel-global words of the domain schedule a scheduler step may
write: the domain time and index, the start and the table. -/
def DomKW (kb b : U64) : Prop := ∃ K ∈ ([16, 24, 32, 192, 200, 208, 216] : List Nat), b.val = kb.val + K

theorem domKW_val {kb b : U64} (h : DomKW kb b) :
    kb.val + 16 ≤ b.val ∧ b.val ≤ kb.val + 216 ∧ b.val ≠ kb.val + 8 ∧ b.val ≠ kb.val + 48 := by
  obtain ⟨K, hK, e⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
  omega

/-- The words a scheduler step writes: the `Sched` links and `IN_QUEUES`
word of the TCBs of `T`, core `c`'s node, and the domain time, domain index
and domain-schedule words (start, table). -/
def SchW (T : Set U64) (c : U64) (s : S) (b : U64) : Prop :=
  (∃ y ∈ T, b = core.num.U64.wrapping_add y 3480#u64 ∨ b = core.num.U64.wrapping_add y 3488#u64 ∨
    b = core.num.U64.wrapping_add y 3592#u64) ∨
  (L.nodeBase s c ≤ b.val ∧ b.val < L.nodeBase s c + 4288) ∨ DomKW (L.ksb s) b

/-- **A scheduler step** (`set_domain`, `reschedule_required`, the domain
schedule's start and configuration): the spec changes only the scheduler's
fields (`SchedK`); at every family of sets whose TCBs include the typed
heap's, from the scheduler and notification relations, FL4 writes only
`SchW` words and the scheduler relation holds after; the domain relation is
kept. -/
def SchedStep (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (s' : S) (σ' : Fl4Spec.State Unit) : Prop :=
  SchedK σ σ' ∧ ∀ (N T C : Set U64) (c : U64), (∀ t, th t = some .tcb → t ∈ T) →
    Sched.SchedRel st N T C c s σ → Notif.NtfnStateRel N T (L.mem s) σ →
    Sched.SchedRel st N T C c s' σ' ∧ P1.WritesIn st s s' (SchW (L := L) T c s) ∧
    (DomRelW (L.mem s) (L.ksb s) σ → DomRelW (L.mem s') (L.ksb s) σ')

/-- The current thread runnable (what the restart needs). -/
def CurRun (σ : Fl4Spec.State Unit) : Prop :=
  ∀ x, σ.kheap σ.curThread = some (.tcb x) → Fl4Spec.runnable x.tcbState = true

/-- **Closure under the primitive steps** (module docstring). -/
structure StepClosed (th : TypedHeap) (Q : S → A → Fl4Spec.State Unit → S → A → Fl4Spec.State Unit → Prop) :
    Prop where
  trans : ∀ s1 a1 σ1 s2 a2 σ2 s3 a3 σ3, Q s1 a1 σ1 s2 a2 σ2 → Q s2 a2 σ2 s3 a3 σ3 → Q s1 a1 σ1 s3 a3 σ3
  restart : ∀ (s : S) (a : A) (σ : Fl4Spec.State Unit) (ct : U64) (x : Fl4Spec.Tcb) (s1 : S),
    σ.curThread = ct.bv → σ.kheap ct.bv = some (.tcb x) → th ct = some .tcb →
    Fl4Spec.runnable x.tcbState = true → sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Q s a σ s1 a (Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv)
  ks : ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit), P1.WritesIn st s s' (KsW (L.ksb s)) → KsStep σ σ' →
    DK4 (L := L) s s' → σ'.domainList = σ.domainList → σ'.domainStartIndex = σ.domainStartIndex →
    (IrqRel (L.mem s) (L.ksb s) σ → IrqRel (L.mem s') (L.ksb s) σ') →
    (IoRel (L.mem s) (L.ksb s) σ → IoRel (L.mem s') (L.ksb s) σ') →
    ArchIrqStep arI a a' → Q s a σ s' a' σ'
  slot : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G' : MdbGhost) (c : Fl4Spec.Cap) (ps pd : U64)
    (rs rd : Nat) (idxs idxd : List Bool), th ps = some (.cnode rs) → th pd = some (.cnode rd) →
    Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False) →
    P1.WritesIn st s s' (InSlot th) → CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' →
    MdbOKV (L.ksb s) (L.mem s') G' →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) →
    Q s a σ s' a σ'
  sched : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit), SchedStep (L := L) th s σ s' σ' → Q s a σ s' a σ'
  cslot : ∀ (s s' : S) (a : A) (σ σ' : Fl4Spec.State Unit) (G' : MdbGhost), Ipc.CnK σ σ' →
    (∀ p, σ'.kheap p = σ.kheap p ∨
      ∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) →
    P1.WritesIn st s s' (InSlot th) → CRel th (L.mem s') σ' G' → FinInv th (L.mem s') σ' G' →
    MdbOKV (L.ksb s) (L.mem s') G' →
    (∀ t, th t = some .tcb → capAt (L.mem s') (slotOf t 1) = capAt (L.mem s) (slotOf t 1)) →
    Q s a σ s' a σ'
  del : ∀ (s s' : S) (a a' : A) (σ σ' : Fl4Spec.State Unit) (sl : Fl4Spec.CslotPtr) (p b : U64) (w r : Bool),
    AbsSlot th sl → capV (L.mem s) (cslotAddr sl) = .Notification p b w r →
    cdt.delete_one st arI s a (cslotAddr sl) = ok (s', a') → ((), σ') ∈ (Fl4Spec.capDeleteOne (Z := Unit) sl σ).1 →
    Q s a σ s' a' σ'

/-- **A run made of primitive steps** (module docstring). -/
def Steps (th : TypedHeap) (s : S) (a : A) (σ : Fl4Spec.State Unit) (s' : S) (a' : A) (σ' : Fl4Spec.State Unit) :
    Prop :=
  ∀ Q, StepClosed (L := L) arI th Q → Q s a σ s' a' σ'

theorem Steps.trans {th : TypedHeap} {s1 s2 s3 : S} {a1 a2 a3 : A} {σ1 σ2 σ3 : Fl4Spec.State Unit}
    (h1 : Steps (L := L) arI th s1 a1 σ1 s2 a2 σ2) (h2 : Steps (L := L) arI th s2 a2 σ2 s3 a3 σ3) :
    Steps (L := L) arI th s1 a1 σ1 s3 a3 σ3 :=
  fun Q hQ => hQ.trans _ _ _ _ _ _ _ _ _ (h1 Q hQ) (h2 Q hQ)

/-- **A scheduler step** (`StepClosed.sched`). -/
theorem Steps.sched {th : TypedHeap} {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit}
    (h : SchedStep (L := L) th s σ s' σ') : Steps (L := L) arI th s a σ s' a σ' :=
  fun _ hQ => hQ.sched s s' a σ σ' h

end


/-! ## The steps of the decodes -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

theorem spec_self {α : Type} {p : Result α} {P : α → Prop} (h : p ⦃ P ⦄) : p ⦃ fun x => p = ok x ⦄ := by
  obtain ⟨x, hx, -⟩ := spec_exists h
  rw [hx]; exact (WP.spec_ok _).2 rfl

/-- The current thread's restart (`StepClosed.restart`), from the spec's
single outcome. -/
theorem Steps.restart {th : TypedHeap} {s s1 : S} {a : A} {σ σ1 : Fl4Spec.State Unit} {ct : U64}
    {x : Fl4Spec.Tcb} (hcur : σ.curThread = ct.bv) (hk : σ.kheap ct.bv = some (.tcb x)) (htcb : th ct = some .tcb)
    (hs1 : sched.set_thread_state st s ct sched.TS_RESTART = ok s1)
    (hst : Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False)) (hC : CurRun σ) :
    Steps (L := L) arI th s a σ s1 a σ1 := by
  intro Q hQ
  have hrun : Fl4Spec.runnable x.tcbState = true := hC x (by rw [hcur]; exact hk)
  have e : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { x with tcbState := .restart })) ct.bv := by
    rw [hcur, Notif.setThreadState_eq .restart hk] at hst
    have := congrArg (fun q => ((), σ1) ∈ q.1) hst
    simp only [Set.mem_singleton_iff, Prod.mk.injEq, true_and] at this
    exact of_eq_true this
  subst e
  exact hQ.restart s a σ ct x s1 hcur hk htcb hrun hs1

theorem IoRel.irqWr {th : TypedHeap} {kb : U64} (hL : IntLayout th kb) {s : S} {σ : Fl4Spec.State Unit}
    (hR : IoRel (L.mem s) kb σ) {i : U64} (hi : i.val < 128) (v : U64) (σ' : Fl4Spec.State Unit)
    (hio : σ'.archState.x64AllocatedIoPorts = σ.archState.x64AllocatedIoPorts) :
    IoRel (L.mem (L.wr s (irqStA kb i) v)) kb σ' := by
  intro p hp
  have hw : (wI p).val < 1024 := by rw [wI_val hp]; omega
  have hv := ioA_val hL.fit hw
  have hv2 := irqStA_val hL.fit hi
  have ha := hL.align
  unfold bitOf
  rw [hio, L.mem_wr_ne (by unfold P1.Aligned; rw [hv2]; omega) (by unfold P1.Aligned; rw [hv]; omega)
    (by rw [hv, hv2]; omega)]
  exact hR p hp

/-- **An IRQ state word's write** (`StepClosed.ks`), with the arch state's
mask. -/
theorem Steps.irqWr {th : TypedHeap} {s : S} {a a1 : A} {σ : Fl4Spec.State Unit} (hL : IntLayout th (L.ksb s))
    {irq : U64} (hirq : irq.val < 128) (v : U64) {b : Bool} (hm : arI.mask_irq a irq b = ok a1)
    (sti : Fl4Spec.IrqState) (hsti : irqSt v = sti) :
    Steps (L := L) arI th s a σ (L.wr s (irqStA (L.ksb s) irq) v) a1 (setIrqSt sti (BitVec.ofNat 8 irq.val) σ) := by
  intro Q hQ
  have hv := irqStA_val hL.fit hirq
  have ha8 : (L.ksb s).val % 8 = 0 := by have := hL.align; omega
  refine hQ.ks _ _ _ _ _ _ ((P1.writesIn_wr (by unfold P1.Aligned; rw [hv]; omega)).mono fun b e => ?_)
    (by constructor <;> rfl) (DK4.irqSt hL.fit ha8 hirq v) rfl rfl
    (fun h => IrqRel.wr hL h hirq v _ (by rw [← hsti]; rfl) rfl) (fun h => IoRel.irqWr hL h hirq v _ rfl)
    (Or.inr (Or.inl ⟨irq, b, hm⟩))
  subst e
  have hK : (⟨BitVec.ofNat 64 (224 + 8 * irq.val)⟩ : U64).val = 224 + 8 * irq.val := by
    show (BitVec.ofNat 64 _).toNat = _; simp; omega
  exact ⟨⟨BitVec.ofNat 64 (224 + 8 * irq.val)⟩, by rw [hK]; omega, by rw [hK]; omega, by rw [hK]; omega,
    by rw [hK, hv]; omega, by rw [hK]; omega⟩

/-- **A spec-only kernel-state step** (an arch IRQ state, say). -/
theorem Steps.ksSpec {th : TypedHeap} {s : S} {a : A} {σ σ' : Fl4Spec.State Unit} (hO : KsStep σ σ')
    (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (hirq : IrqRel (L.mem s) (L.ksb s) σ → IrqRel (L.mem s) (L.ksb s) σ')
    (hio : IoRel (L.mem s) (L.ksb s) σ → IoRel (L.mem s) (L.ksb s) σ') :
    Steps (L := L) arI th s a σ s a σ' := fun Q hQ =>
  hQ.ks s s a a σ σ' (P1.WritesIn.refl _ _) hO (DK4.refl s) hdl hds hirq hio (Or.inl rfl)

/-- **An arch operation of an interrupt decode.** -/
theorem Steps.arch {th : TypedHeap} {s : S} {a a' : A} {σ : Fl4Spec.State Unit} (h : ArchIrqStep arI a a') :
    Steps (L := L) arI th s a σ s a' σ := fun Q hQ =>
  hQ.ks s s a a' σ σ (P1.WritesIn.refl _ _) (KsStep.refl σ) (DK4.refl s) rfl rfl id id h

/-- **A capability insert into a CNode slot** (`StepClosed.slot`), from the
insert's frame (`insert_frame2`) and the CSpace relation after. -/
theorem Steps.insert {th : TypedHeap} (hP : Placed th) {s s' : S} {a : A} {σ σ' : Fl4Spec.State Unit} {G' : MdbGhost}
    {c : Fl4Spec.Cap} {ps pd : U64} {rs rd : Nat} {idxs idxd : List Bool} (hps : th ps = some (.cnode rs))
    (hpd : th pd = some (.cnode rd)) (hld : idxd.length = rd)
    (hci : Fl4Spec.capInsert (Z := Unit) c (ps.bv, idxs) (pd.bv, idxd) σ = ({((), σ')}, False))
    (hF : Vs.SlotFrame2 (L := L) th s s') (hCR : CRel th (L.mem s') σ' G') (hFI : FinInv th (L.mem s') σ' G')
    (hMO : MdbOKV (L.ksb s) (L.mem s') G')
    (hcap : ∀ y, IsSlot th y → y ≠ cslotAddr (pd.bv, idxd) → capV (L.mem s') y = capV (L.mem s) y) :
    Steps (L := L) arI th s a σ s' a σ' := by
  intro Q hQ
  refine hQ.slot s s' a σ σ' G' c ps pd rs rd idxs idxd hps hpd hci
    ⟨hF.1, hF.2.1, fun b hb hn => hF.2.2 b hb fun ⟨x, k, hx, hk, e⟩ => hn ⟨x, hx, ?_⟩⟩ hCR hFI hMO fun t ht => ?_
  · have hf := hx.fit hP
    have := hk.lt
    have hv := wordOf_val (a := x) (k := k) (by omega)
    rw [e, hv]; omega
  · have h1 : IsSlot th (slotOf t 1) := ⟨t, 1, Or.inr ⟨ht, by decide⟩, rfl⟩
    have hne : slotOf t 1 ≠ cslotAddr (pd.bv, idxd) := by
      intro e
      obtain ⟨p, i, hi, hp1, hp2⟩ := AbsSlot.at (th := th) (sl := (pd.bv, idxd)) ⟨pd, rfl, Or.inl (by simpa [hld] using hpd)⟩
      have hpp : p = pd := P1.eq_of_bv hp1.symm
      subst hpp
      have := IsSlotAt.apart hP (Or.inr ⟨ht, by decide⟩ : IsSlotAt th t 1) hi (fun hh => by
        obtain ⟨h, -⟩ := hh; subst h; rw [hpd] at ht; cases ht)
      rw [e, hp2] at this; omega
    rw [capAt_capV, capAt_capV, hcap _ h1 hne]

end

end

end Fl4Proofs.P3
