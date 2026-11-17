/-
P1: CNode `Delete` and `Revoke` (`cdt.delete` exposed, `cdt.revoke`), after
the caller's restart, keep the invariants and the preemption-point facts
(`Cur0`), from the finalisation steps named in `DelGaps` (one shape:
`Cur0` in, `Cur0` out).  The loops (`finalise_slot_immediate`,
`revoke_loop`) with their preemption points (`preemption_point.pp`) are
proved here.
-/
import Fl4Proofs.P1.QueueReplyX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- The four words of a cap slot are cap-slot words. -/
def SlotW (T Ω Sg : Set U64) (x : U64) : Prop :=
  Aligned x ∧ ∀ o : U64, o.val < 32 → o.val % 8 = 0 → CapW T Ω Sg (core.num.U64.wrapping_add x o)

/-- The state inside a deletion, from the decode's start `s0`: the
invariants (for some active set), the current thread and SC kept, the
current thread's `SC` field kept or cleared, the switch-to candidate no
thread, the current thread not blocked (on IPC or a reply); and `s0`'s
current-SC fact. -/
def Cur0 (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s : S) : Prop :=
  (L.mem s0 (scA (L.curW s0)) ≠ 0#u64 → L.cscW s0 = L.mem s0 (scA (L.curW s0))) ∧
  ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s ∧ L.curW s = L.curW s0 ∧ L.cscW s = L.cscW s0 ∧
    (L.mem s (scA (L.curW s0)) = L.mem s0 (scA (L.curW s0)) ∨ L.mem s (scA (L.curW s0)) = 0#u64) ∧
    (∀ y ∈ T, L.actionW s ≠ y) ∧ ¬ BlockedR (L.mem s (stA (L.curW s0))) ∧
    WritesIn st s0 s (Cur0W st T Cs Ω H Sg Scs Z s0)

/-- `DecPost` from `Cur0`'s parts (the frame is not needed). -/
theorem Cur0.postOf {s0 s : S} {r : core.result.Result Unit error.Exc} {Ac' : Set U64}
    (hc0 : L.mem s0 (scA (L.curW s0)) ≠ 0#u64 → L.cscW s0 = L.mem s0 (scA (L.curW s0)))
    (h1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s) (ec : L.curW s = L.curW s0) (ecs : L.cscW s = L.cscW s0)
    (esc : L.mem s (scA (L.curW s0)) = L.mem s0 (scA (L.curW s0)) ∨ L.mem s (scA (L.curW s0)) = 0#u64)
    (na : ∀ y ∈ T, L.actionW s ≠ y) : DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r s := by
  refine ⟨Ac', h1, fun _ => ⟨⟨ecs, ec, fun _ _ => ?_, ?_⟩, na _ h1.1.choose_spec.choose_spec.curT, fun hne => ?_⟩⟩
  · rcases esc with e | e
    · rw [e]
      by_cases z : L.mem s0 (scA (L.curW s0)) = 0#u64
      · exact Or.inl z
      · exact Or.inr (hc0 z).symm
    · exact Or.inl e
  · rcases esc with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · rw [ec] at hne ⊢
    rcases esc with e | e
    · rw [e] at hne ⊢; rw [ecs]; exact hc0 hne
    · exact absurd e hne

theorem Cur0.post {s0 s : S} {r : core.result.Result Unit error.Exc}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r s := by
  obtain ⟨hc0, Ac', h1, ec, ecs, esc, na, -⟩ := h
  exact Cur0.postOf hc0 h1 ec ecs esc na

theorem nbr_restart : ¬ BlockedR sched.TS_RESTART := fun h => h.elim not_blocked_restart restart_ne.1

theorem nbr_runnable {v : U64} (h : Runnable v) : ¬ BlockedR v := fun h' =>
  h'.elim (runnable_ok h).1 (runnable_ok h).2

/-- `Cur0` across a step: the invariants for some active set, the current
thread and SC kept, the current thread's `SC` kept or cleared, the
candidate kept or `CHOOSE_NEW`, and the current thread's state kept or not
blocked. -/
theorem Cur0.mk {s0 s s' : S} {Ac' : Set U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hb : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s') (ec : L.curW s' = L.curW s) (ecs : L.cscW s' = L.cscW s)
    (esc : L.mem s' (scA (L.curW s)) = L.mem s (scA (L.curW s)) ∨ L.mem s' (scA (L.curW s)) = 0#u64)
    (ea : L.actionW s' = L.actionW s ∨ L.actionW s' = 1#u64)
    (est : L.mem s' (stA (L.curW s)) = L.mem s (stA (L.curW s)) ∨ ¬ BlockedR (L.mem s' (stA (L.curW s))))
    (hw : WritesIn st s s' (Cur0W st T Cs Ω H Sg Scs Z s)) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  obtain ⟨hc0, Ac1, hb1, ec1, ecs1, esc1, na1, nb1, w1⟩ := h
  have hT := hb1.1.choose_spec.choose_spec.tcbs
  refine ⟨hc0, Ac', hb, ec.trans ec1, ecs.trans ecs1, ?_, fun y hy => ?_, ?_, Cur0W.trans w1 hw⟩
  · rw [ec1] at esc
    rcases esc with e | e
    · rw [e]; exact esc1
    · exact Or.inr e
  · rcases ea with e | e
    · rw [e]; exact na1 y hy
    · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)
  · rw [ec1] at est
    rcases est with e | e
    · rw [e]; exact nb1
    · exact e

/-- `Cur0`'s frame. -/
theorem Cur0.fr {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : Fr0 st T Cs Ω H Sg Scs Z s0 s :=
  h.2.choose_spec.2.2.2.2.2.2

/-- `Cur0`'s invariants. -/
theorem Cur0.bxi {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    ∃ Ac', BXI st T Cs Ω H Sg Rp Scs Nt Z Ac' s := ⟨_, h.2.choose_spec.1⟩

/-- Cap-slot writes. -/
theorem Cur0.capw {s0 s s' : S} {B : U64 → Prop} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  have h0 := h
  obtain ⟨-, Ac', h1, -, -, -, -, -⟩ := h0
  have hct : L.curW s ∈ T := h1.1.choose_spec.choose_spec.curT
  obtain ⟨b, -, ec, ecs, ea, fld, -, -⟩ := blk_of_capw h1.blk hw hB
  refine Cur0.mk h (BlkOK.bxi b) ec ecs (Or.inl ?_) (Or.inl ea) (Or.inl ?_)
    (hw.mono fun b hb => Or.inr (Or.inr (Or.inl (hB b hb))))
  · rw [scA_eq]; exact fld _ hct _ (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact fld _ hct _ (by simp) (by simp) (by simp)

/-- `set_cap` of a cap slot. -/
theorem obj.Slot.set_cap.capw {s : S} {x : U64} {c : capability.Cap} (hx' : SlotW T Ω Sg x) :
    obj.Slot.set_cap st x s c ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨ha, hx⟩ := hx'
  unfold obj.Slot.set_cap
  refine WP.spec_bind (P0.capability.Cap.encode.p0 c) ?_
  rintro ⟨w0, w1⟩ -
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (LawfulStore.write_spec s x w0) fun s1 e1 => ?_
  subst e1
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec _ _ w1) fun s2 e2 => ?_
  subst e2
  have h0 : core.num.U64.wrapping_add x 0#u64 = x := by
    apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
  have c0 : CapW T Ω Sg x := h0 ▸ hx 0#u64 (by simp) (by simp)
  have c8 := hx 8#u64 (by simp) (by simp)
  have a8 : Aligned (core.num.U64.wrapping_add x 8#u64) := by
    unfold Aligned at ha ⊢; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  exact ((writesIn_wr ha).trans (writesIn_wr a8)).mono fun b hb => by
    rcases hb with e | e
    · exact e ▸ c0
    · exact e ▸ c8

/-- A preemption point. -/
theorem sched.preemption_point.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    sched.preemption_point st ar s a ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hh := h
  obtain ⟨-, Ac', h1, -, -, -, -, -⟩ := hh
  have q := h1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  obtain ⟨-, hΩ, hSgw⟩ := ks_work_units h1.blk
  have ho := q.omega _ hΩ
  refine WP.spec_mono (sched.preemption_point.pp (Ac := Ac') hA s a h1.blk) fun r ⟨b, w⟩ => ?_
  -- the preemption point's words are not the scheduler words nor any TCB field
  have nn : ∀ o : U64, (o.val = 0 ∨ o.val = 16 ∨ o.val = 24) → ¬ PPW st s (L.nodeAt s (L.cpu s) o) := by
    intro o ho' hp
    rcases hp with e | e | e
    · exact out_ne_node (o := o) ho q.cur hN (by omega) (congrArg UScalar.val e)
    · have := congrArg UScalar.val e
      unfold LawfulStore.nodeA at this
      rw [nodeAt_val hN (by omega), nodeAt_val hN (by simp [layout.node.CUR_TIME])] at this
      simp [layout.node.CUR_TIME] at this; omega
    · have := congrArg UScalar.val e
      unfold LawfulStore.nodeA at this
      rw [nodeAt_val hN (by omega), nodeAt_val hN (by simp [layout.node.CONSUMED])] at this
      simp [layout.node.CONSUMED] at this; omega
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 16 ∨ o.val = 24) →
      L.mem r.2.1 (L.nodeAt r.2.1 (L.cpu r.2.1) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o ho' => by
    rw [w.2.1, nodeAt_of_ksb w.1]
    exact w.mem_eq (nodeAt_aligned hN (by omega) (by omega)) (nn o ho')
  have hct : L.curW s ∈ T := q.curT
  have ffld : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem r.2.1 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK hK8 => by
    refine w.mem_eq (field_aligned (hT _ hct) hK hK8) fun hp => ?_
    rcases hp with e | e | e
    · exact out_ne_field (K := K) ho hct (hT _ hct) hK (congrArg UScalar.val e)
    · exact node_ne_field (K := K) (o := layout.node.CUR_TIME) hN (by simp [layout.node.CUR_TIME]) hct
        (hT _ hct) hK (by unfold LawfulStore.nodeA at e; exact e.symm)
    · exact node_ne_field (K := K) (o := layout.node.CONSUMED) hN (by simp [layout.node.CONSUMED]) hct
        (hT _ hct) hK (by unfold LawfulStore.nodeA at e; exact e.symm)
  have ec := nd _ (by rw [curth0]; simp)
  have ea := nd _ (by rw [act_val]; simp)
  refine Cur0.mk h (BlkOK.bxi b) ec ?_ (Or.inl (by rw [scA_eq]; exact ffld _ (by simp) (by simp))) (Or.inl ea)
    (Or.inl (by rw [stA_eq]; exact ffld _ (by simp) (by simp))) (w.mono fun b hb => ?_)
  · unfold LawfulStore.cscW LawfulStore.nodeA; exact nd _ (by simp [layout.node.CUR_SC])
  · rcases hb with e | e | e
    · exact Or.inr (Or.inr (Or.inl (Or.inr (e ▸ ⟨hΩ, hSgw⟩))))
    · exact Or.inl (e ▸ kw_node q.cur (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    · exact Or.inl (e ▸ kw_node q.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]))

/-- The slot at index `i` of a slot array at `p`. -/
def slotIdx (p i : U64) : U64 := core.num.U64.wrapping_add p (core.num.U64.wrapping_mul i 32#u64)

/-- A cap's typing for its deletion (P3's `valid_cap`): `CapTyped`; IRQ
handler caps name IRQs below 128; I/O-port caps name ranges of 16-bit ports;
CNode and zombie caps name arrays of cap slots; thread caps name TCBs. -/
def DelCapOK (T Ω Sg : Set U64) (H : Heap) (Rp Nt : Set U64) (c : capability.Cap) : Prop :=
  CapTyped H Rp Nt c ∧ (∀ i, c = .IrqHandler i → i.val < 128) ∧
  (∀ f l o, c = .IoPort f l o → f.val ≤ l.val ∧ l.val < 65536) ∧
  (∀ p r g b, c = .CNode p r g b → SlotW T Ω Sg p ∧ ∀ i : U64, i.val < 2 ^ (r.val % 64) → SlotW T Ω Sg (slotIdx p i)) ∧
  (∀ p t n, c = .Zombie p t n → SlotW T Ω Sg p ∧ ∀ i : U64, i.val < n.val → SlotW T Ω Sg (slotIdx p i)) ∧
  (∀ p, c = .Thread p → p ∈ T)

/-- The placement facts of a cap's finalisation that depend on the state
(P3's: no cap names the idle thread or its SC; native TCBs have no bound
VCPU; SC caps name SCs). -/
def FinPl (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (s : S) (c : capability.Cap) : Prop :=
  (∀ p, c = .Thread p → p ≠ L.idleW s ∧ L.mem s (core.num.U64.wrapping_add p 3664#u64) = 0#u64) ∧
  (∀ p b, c = .SchedContext p b → p ∈ Scs ∧ p ≠ 0#u64 ∧
    (L.mem s (scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (scTcbA p)))

theorem DelCapOK.null : DelCapOK T Ω Sg H Rp Nt .Null := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- The finalisation steps (P3's), each `Cur0` in and `Cur0` out: the caps
in cap slots are typed for deletion (`DelCapOK`); each typed cap's
finalisation, with typed remainder and cleanup caps; the deferred delete of
a cap slot; emptying a cap slot with its CDT unlinking and the typed cleanup
cap's `post_cap_deletion`; and the CDT's `NEXT` links of cap slots name cap
slots.  QueueDelFin proves this from placement (`DelPlace`) and the named
per-kind finalisations (`FinGaps`). -/
structure DelGapsAt (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  cap : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.cap st x s ⦃ c => DelCapOK T Ω Sg H Rp Nt c ∧ FinPl st Scs s c ⦄
  fin : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (fin : Bool),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → DelCapOK T Ω Sg H Rp Nt c → FinPl st Scs s c →
    objects.finalise_cap st ar s a c fin false ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      DelCapOK T Ω Sg H Rp Nt r.1.1 ∧ DelCapOK T Ω Sg H Rp Nt r.1.2 ⦄
  deferred : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64), Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
    SlotW T Ω Sg x → cdt.delete_deferred st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄
  empty : ∀ (Ac : Set U64) (s : S) (a : A) (x : U64) (c : capability.Cap),
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s → SlotW T Ω Sg x → DelCapOK T Ω Sg H Rp Nt c →
    cdt.empty_slot st ar s a x c ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄
  next : ∀ (Ac : Set U64) (s : S) (x : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    SlotW T Ω Sg x → obj.Slot.next st x s ⦃ n => n = 0#u64 ∨ SlotW T Ω Sg n ⦄

/-- The deletion gaps at every decode start reached from a `P3Ok` entry. -/
def DelGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop :=
  ∀ s0, EntAt st P3Ok s0 → DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0

theorem cte_size : layout.cte.SIZE = 32#u64 := by unfold layout.cte.SIZE; rfl

/-- A non-removable zombie has a nonzero count. -/
theorem cdt.cap_removable.zombie (c : capability.Cap) (x : U64) :
    cdt.cap_removable c x ⦃ b => b = false → ∀ p t n, c = .Zombie p t n → n ≠ 0#u64 ⦄ := by
  cases c <;> simp [cdt.cap_removable]
  split <;> simp_all
  split <;> simp_all

theorem zombie_last {T Ω Sg : Set U64} {H : Heap} {Rp Nt : Set U64} {p t n : U64}
    (hc : DelCapOK T Ω Sg H Rp Nt (.Zombie p t n)) (hn : n ≠ 0#u64) :
    SlotW T Ω Sg (slotIdx p (core.num.U64.wrapping_sub n 1#u64)) := by
  refine (hc.2.2.2.2.1 p t n rfl).2 _ ?_
  have : n.val ≠ 0 := fun e => hn (UScalar.eq_of_val_eq (by simpa using e))
  simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega

set_option hygiene false in
/-- The preemption-point tail of a loop round (`Cur0` at `s2`). -/
local macro "pptail" : tactic => `(tactic| (
  refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
  rintro ⟨rr, s3, a3⟩ h3
  try simp only [WP.uncurry'_pair] at h3 ⊢
  try simp only [uncurry_apply_pair] at h3 ⊢
  rcases rr with _ | ee
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
    refine (WP.spec_ok _).2 ⟨h3, ?_⟩
    show fuel1.val < fuel.val
    omega
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    first | exact (WP.spec_ok _).2 h3 | exact h3 | exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩ |
      exact ⟨h3, by intro v hv; simp_all⟩))

set_option maxHeartbeats 4000000 in
theorem cdt.finalise_slot_immediate.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.finalise_slot_immediate st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      ∀ v, r.1 = .Ok v → DelCapOK T Ω Sg H Rp Nt v.cleanup ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, by intro v hv; simp_all⟩
    rename_i hf
    step as ⟨fuel1, hf1⟩
    obtain ⟨Acx, hbx⟩ := h1.bxi
    refine WP.spec_bind (G.cap Acx s1 x h1.fr hbx hx) fun c ⟨hc, hpl⟩ => ?_
    refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h1, fun v hv => by cases hv; exact DelCapOK.null⟩
    refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_
    refine WP.spec_bind (G.fin Ac s1 a1 c fin h1 hc hpl) ?_
    rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨h2', hrem, hcl⟩
    try simp only [uncurry_apply_pair, WP.uncurry'_pair]
    refine WP.spec_bind (cdt.cap_removable.zombie rem x) fun br hbr => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2', fun v hv => by cases hv; exact hcl⟩
    rename_i hbr0
    have hbr' := hbr (by simpa using hbr0)
    refine WP.spec_bind (obj.Slot.set_cap.capw (c := rem) (s := s2) hx) fun s2' w2 => ?_
    have h2 := h2'.capw w2 fun _ hb => hb
    have hf' : 0 < fuel.val := by simpa using hf
    split
    all_goals try pptail
    -- the zombie: the deferred delete of its last slot, then the count
    simp only [lift, bind_ok]
    rename_i zp zt zn
    have hen := zombie_last hrem (hbr' zp zt zn rfl)
    unfold obj.Slot.index
    simp only [lift, bind_ok, cte_size]
    refine WP.spec_bind (G.deferred Ac s2' a2 _ h2 hen) ?_
    rintro ⟨r, s3, a3⟩ h3
    try simp only [uncurry_apply_pair] at h3 ⊢
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s3 hS) fun c _ => ?_
      have SC : ∀ c', obj.Slot.set_cap st x s3 c' ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := fun c' =>
        WP.spec_mono (obj.Slot.set_cap.capw hx) fun s' w => h3.capw w fun _ hb => hb
      refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1) ?_ ?_
      · split
        all_goals try exact (WP.spec_ok _).2 h3
        split
        · split
          · refine WP.spec_bind (Pₘ := fun s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s') ?_
              fun s' h' => (WP.spec_ok _).2 h'
            split
            · try simp only [lift, bind_ok]
              exact SC _
            · exact (WP.spec_ok _).2 h3
          · exact (WP.spec_ok _).2 h3
        · exact (WP.spec_ok _).2 h3
      · rintro ⟨s4, a4⟩ h2
        try simp only [uncurry_apply_pair] at h2 ⊢
        pptail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 ⟨h3, by intro v hv; simp_all⟩
  · exact h

/-- `cdt.delete` (exposed) of a cap slot. -/
theorem cdt.delete.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.delete st ar s a x true ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  unfold cdt.delete
  simp only [↓reduceIte]
  refine WP.spec_bind (cdt.finalise_slot_immediate.cur0 hA G h hx) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, hv1⟩
  try simp only [uncurry_apply_pair] at h1 hv1 ⊢
  rcases r with v | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (G.empty Ac s1 a1 x _ h1 hx (hv1 v rfl)) ?_
    rintro ⟨s2, a2⟩ h2
    try simp only [uncurry_apply_pair] at h2 ⊢
    exact (WP.spec_ok _).2 h2
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 2000000 in
/-- `cdt.revoke` of a cap slot. -/
theorem cdt.revoke.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s0 s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s0) {a : A} {x : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hx : SlotW T Ω Sg x) :
    cdt.revoke st ar s a x ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.revoke cdt.revoke_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1)
  · rintro ⟨s1, a1, fuel⟩ h1
    simp only at h1
    dsimp only
    unfold cdt.revoke_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    have hf' : 0 < fuel.val := by simpa using hf
    step as ⟨fuel1, hf1⟩
    have h1' := h1
    obtain ⟨-, Acx, hbx, -, -, -, -, -⟩ := h1'
    refine WP.spec_bind (G.next Acx s1 x h1.fr hbx hx) fun nx hnx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 h1
    rename_i hn0
    have hnW : SlotW T Ω Sg nx := hnx.resolve_left (by simpa using hn0)
    refine WP.spec_bind (P0.cdt.is_mdb_parent_of.p0 st s1 x nx hS) fun bp _ => ?_
    split
    · refine WP.spec_bind (cdt.delete.cur0 hA G h1 hnW) ?_
      rintro ⟨r, s2', a2⟩ h2
      try simp only [uncurry_apply_pair] at h2 ⊢
      rcases r with _ | e
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        refine WP.spec_bind (sched.preemption_point.cur0 hA h2) ?_
        rintro ⟨rr, s3, a3⟩ h3
        try simp only [uncurry_apply_pair] at h3 ⊢
        rcases rr with _ | ee
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, bind_tc_ok]
          refine (WP.spec_ok _).2 ⟨h3, ?_⟩
          show fuel1.val < fuel.val
          omega
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 h3
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
          core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
          bind_tc_ok]
        exact (WP.spec_ok _).2 h2
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- The caller's restart from `DecPre` starts `Cur0`. -/
theorem Cur0.restart {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 ⦄ := by
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 ⟨h1, f1, est, k⟩ => ?_
  have ec := k.curW
  have ecs := k.cscW
  have esc := k.scf hct
  refine ⟨D.hcsc, Ac, BlkOK.bxi h1, ec, ecs, Or.inl esc, fun y hy => ?_, by rw [est]; exact nbr_restart,
    WritesIn.mono f1 fun _ hb => Or.inl (KW.mono hb (Set.empty_subset _))⟩
  rcases k.act with e | e
  · rw [e, D.act]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)
  · rw [e]; exact fun e' => notT_small hT (by simp) (e' ▸ hy)

/-- **CNode `Delete`** from `DelGaps`. -/
theorem cnode_del {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0.restart D) fun s1 h1 => WP.spec_mono (cdt.delete.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- **CNode `Revoke`** from `DelGaps`. -/
theorem cnode_rev {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s) {a : A} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hx : SlotW T Ω Sg x) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind (Cur0.restart D) fun s1 h1 => WP.spec_mono (cdt.revoke.cur0 hA G h1 hx) fun r hr => by
    obtain ⟨r', s', a'⟩ := r; exact hr.post

/-- `CdtHyps` with the target slot of a CNode operation a whole cap slot
(its four words cap-slot words). -/
structure CdtHyps2 (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop extends CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok where
  tgtW : ∀ (Ac : Set U64) (s : S) (c : capability.Cap) (i d : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → SlotW T Ω Sg x ⦄

set_option hygiene false in
local macro "errleaf2" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode`**, Delete and Revoke included. -/
theorem cnode.decode.dec2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} (G : DelGapsAt st ar T Cs Ω H Sg Rp Scs Nt Z s)
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (c : capability.Cap) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf2
  split
  · errleaf2
  split
  · errleaf2
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (WP.spec_and (C.tgt Ac s c idx dep hE D.bxi) (C.tgtW Ac s c idx dep hE D.bxi)) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf2
  have hv := hr.1 v rfl
  have hvW := hr.2 v rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (D.err _)
    | exact lift2 (cnode.decode_copy.dec C.toCdtHyps lbl len buf v D hE hv)
    | exact lift2 (cnode.decode_cancel_badged_sends.dec C.toCdtHyps v D hE hv)
    | exact lift2 (cnode.decode_rotate.dec C.toCdtHyps len buf v D hE hv)
    | exact cnode_del hA G D hvW
    | exact cnode_rev hA G D hvW
    | split)

/-- **InvGaps' `cnode`, discharged** from `CdtHyps2` and `DelGaps`. -/
theorem decGap_cnode2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (C : CdtHyps2 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) (G : DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact cnode.decode.dec2 hA C (G s hE) a lbl len buf D hE _

end

end Fl4Proofs.P1
