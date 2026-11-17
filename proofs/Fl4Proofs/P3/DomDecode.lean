/-
P3 (DESIGN.md §9), domains: **`domain::decode`** against l4v's
`decode_domain_invocation`, then `set_thread_state Restart` and
`invoke_domain` (`domain_decode_refines`), and its branch of the dispatcher
(`decode_invocation_domain`).

`DomRel` relates FL4's domain schedule (the kernel-global table of
`NUM_DOMAIN_SCHEDULES` = 2 entries, a domain word and a duration word each,
and the `DOM_SCHED_START` word) to the spec's `domain_list` and
`domain_start_index`. FL4 is built with one domain: `DomConfig` is the
platform constant `numDomains = 1` (PORTING.md, "Platform constants");
`timeArgLen = 1` and `maxDomainDuration = 2^56 - 1` hold by definition.

The scheduler steps are hypotheses for the scheduler's proofs: `DomSetHyp`
(DomainSetSet's `set_domain` against `invoke_set_domain`) and `DomResHyp`
(ScheduleSetStart's `reschedule_required` against `reschedule_required`),
each about the states the decode reaches.
-/
import Fl4Proofs.P3.DecodeTop
import Fl4Proofs.P3.NtfnSched
import Fl4Proofs.P1.QueueSlots
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-! ## The spec's decode -/

section
open Fl4Spec

theorem dec_dom_other {σ : State Unit} {slbl : Data} (args : List Data) (excs : List (Cap × CslotPtr))
    (h1 : genInvocationType slbl ≠ .domainSetSet) (h2 : genInvocationType slbl ≠ .domainScheduleConfigure)
    (h3 : genInvocationType slbl ≠ .domainScheduleSetStart) :
    (decodeDomainInvocation (Z := Unit) slbl args excs).run σ = ({(.error .illegalOperation, σ)}, False) := by
  unfold decodeDomainInvocation
  split
  · exact absurd ‹_› h1
  · exact absurd ‹_› h2
  · exact absurd ‹_› h3
  · rfl

theorem dec_start_nil {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainScheduleSetStart)
    (excs : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl [] excs).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainScheduleSetStart
  rw [whenE_pos (by simp)]
  exact run_bind_error (s := σ) rfl _

theorem dec_start {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainScheduleSetStart)
    (y0 : Data) (rest : List Data) (excs : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl (y0 :: rest) excs).run σ =
      if unat y0 ≥ σ.domainList.length then
        ({(.error (.rangeError 0 (BitVec.ofNat 64 (σ.domainList.length - 1))), σ)}, False)
      else if the σ.domainList[unat y0]? = domainEndMarker then ({(.error (.invalidArgument 0), σ)}, False)
      else ({(.ok (.invokeDomainScheduleSetStart (unat y0)), σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainScheduleSetStart
  rw [whenE_neg (by simp)]
  simp only [ndE_pure_bind, Fl4Spec.NonDetE.returnOk, List.getElem?_cons_zero, the_some]
  rw [run_bind_ok (s := σ) (run_liftE (m := NonDet.gets fun s : State Unit => s.domainList) rfl)]
  by_cases h1 : unat y0 ≥ σ.domainList.length
  · rw [if_pos h1, whenE_pos h1]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h1, whenE_neg h1, retOk_bind]
  by_cases h2 : the σ.domainList[unat y0]? = domainEndMarker
  · rw [if_pos h2, whenE_pos h2]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h2, whenE_neg h2, retOk_bind]; rfl

theorem dec_conf_short {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainScheduleConfigure)
    (args : List Data) (hl : args.length < 3) (excs : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl args excs).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainScheduleConfigure
  rw [whenE_pos (show args.length < 2 + timeArgLen by unfold timeArgLen; omega)]
  exact run_bind_error (s := σ) rfl _

theorem dec_conf {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainScheduleConfigure)
    (y0 y1 y2 : Data) (rest : List Data) (excs : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl (y0 :: y1 :: y2 :: rest) excs).run σ =
      if unat y0 ≥ σ.domainList.length - 1 then
        ({(.error (.rangeError 0 (BitVec.ofNat 64 (σ.domainList.length - 2))), σ)}, False)
      else if unat y1 ≥ numDomains then
        ({(.error (.rangeError 0 (BitVec.ofNat 64 (numDomains - 1))), σ)}, False)
      else if y2 > maxDomainDuration then ({(.error (.invalidArgument 2), σ)}, False)
      else if y2 = 0 ∧ y1 ≠ 0 then ({(.error (.invalidArgument 1), σ)}, False)
      else if unat y0 = σ.domainStartIndex ∧ y2 = 0 then ({(.error (.invalidArgument 2), σ)}, False)
      else ({(.ok (.invokeDomainScheduleConfigure (unat y0) (ucast domainLen y1) (ucast domainDurationLen y2)),
        σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainScheduleConfigure
  rw [whenE_neg (show ¬ (y0 :: y1 :: y2 :: rest).length < 2 + timeArgLen by unfold timeArgLen; simp)]
  simp only [retOk_bind, List.getElem?_cons_zero, List.getElem?_cons_succ, the_some, parseTimeArg]
  rw [run_bind_ok (s := σ) (run_liftE (m := NonDet.gets fun s : State Unit => s.domainList) rfl)]
  by_cases h1 : unat y0 ≥ σ.domainList.length - 1
  · rw [if_pos h1, whenE_pos h1]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h1, whenE_neg h1, retOk_bind]
  by_cases h2 : unat y1 ≥ numDomains
  · rw [if_pos h2, whenE_pos h2]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h2, whenE_neg h2, retOk_bind]
  by_cases h3 : y2 > maxDomainDuration
  · rw [if_pos h3, whenE_pos h3]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h3, whenE_neg h3, retOk_bind]
  by_cases h4 : y2 = 0 ∧ y1 ≠ 0
  · rw [if_pos h4, whenE_pos h4]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h4, whenE_neg h4, retOk_bind]
  rw [run_bind_ok (s := σ) (run_liftE (m := NonDet.gets fun s : State Unit => s.domainStartIndex) rfl)]
  by_cases h5 : unat y0 = σ.domainStartIndex ∧ y2 = 0
  · rw [if_pos h5, whenE_pos h5]; exact run_bind_error (s := σ) rfl _
  rw [if_neg h5, whenE_neg h5, retOk_bind]; rfl

theorem dec_set_nil {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainSetSet)
    (excs : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl [] excs).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainSet
  exact run_bind_error (s := σ) rfl _

theorem dec_set_big {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainSetSet)
    (x : Data) (xs : List Data) (hx : unat x ≥ numDomains) (excs : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl (x :: xs) excs).run σ =
      ({(.error (.invalidArgument 0), σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainSet
  dsimp only
  rw [whenE_pos hx]
  exact run_bind_error (s := σ) (run_bind_error (s := σ) rfl _) _

theorem dec_set_noex {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainSetSet)
    (x : Data) (xs : List Data) (hx : ¬ unat x ≥ numDomains) :
    (decodeDomainInvocation (Z := Unit) slbl (x :: xs) []).run σ = ({(.error .truncatedMessage, σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainSet
  dsimp only
  rw [whenE_neg hx, retOk_bind, run_bind_ok (s := σ) rfl, whenE_pos (by simp)]
  exact run_bind_error (s := σ) rfl _

theorem dec_set_thread {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainSetSet)
    (x : Data) (xs : List Data) (hx : ¬ unat x ≥ numDomains) (p : ObjRef) (sl : CslotPtr)
    (rest : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl (x :: xs) ((.threadCap p, sl) :: rest)).run σ =
      ({(.ok (.invokeDomainSet p (ucast domainLen x)), σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainSet
  dsimp only
  rw [whenE_neg hx, retOk_bind, run_bind_ok (s := σ) rfl, whenE_neg (by simp), retOk_bind]
  rfl

theorem dec_set_other {σ : State Unit} {slbl : Data} (hg : genInvocationType slbl = .domainSetSet)
    (x : Data) (xs : List Data) (hx : ¬ unat x ≥ numDomains) (c : Cap) (hc : ∀ p, c ≠ .threadCap p)
    (sl : CslotPtr) (rest : List (Cap × CslotPtr)) :
    (decodeDomainInvocation (Z := Unit) slbl (x :: xs) ((c, sl) :: rest)).run σ =
      ({(.error (.invalidArgument 1), σ)}, False) := by
  unfold decodeDomainInvocation; rw [hg]
  dsimp only
  unfold decodeDomainSet
  dsimp only
  rw [whenE_neg hx, retOk_bind, run_bind_ok (s := σ) rfl, whenE_neg (by simp), retOk_bind]
  simp only [List.head?_cons, the_some]
  rfl

end

/-! ## The relation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]


/-- The offset of entry `i`'s domain word in the kernel-global area
(layout.rs `ks::DOM_SCHEDULE`, two words per entry). -/
def entOff (i : U64) : U64 := core.num.U64.wrapping_add 192#u64 (core.num.U64.wrapping_mul i 16#u64)
/-- The offset of entry `i`'s duration word. -/
def durOff (i : U64) : U64 := core.num.U64.wrapping_add (entOff i) 8#u64
/-- The kernel-global word at offset `o`. -/
def ksW (kb o : U64) : U64 := core.num.U64.wrapping_add kb o

theorem ksW_val {kb o : U64} (h : kb.val + o.val < 2 ^ 64) : (ksW kb o).val = kb.val + o.val := by
  unfold ksW; simp only [core.num.U64.wrapping_add_val_eq]; simp [U64.size, U64.numBits]; omega

theorem entOff_val {i : U64} (h : i.val < 2) : (entOff i).val = 192 + 16 * i.val := by
  unfold entOff; simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
  simp [U64.size, U64.numBits]; omega

theorem durOff_val {i : U64} (h : i.val < 2) : (durOff i).val = 200 + 16 * i.val := by
  unfold durOff; simp only [core.num.U64.wrapping_add_val_eq, entOff_val h]
  simp [U64.size, U64.numBits]; omega

/-- **The domain schedule relation**: FL4's table (domain and duration
words, a zero duration only with domain 0) is the spec's `domain_list`, of
`NUM_DOMAIN_SCHEDULES` = 2 entries, and the `DOM_SCHED_START` word its
`domain_start_index`. -/
def DomRel (m : U64 → U64) (kb : U64) (σ : Fl4Spec.State Unit) : Prop :=
  σ.domainList.length = 2 ∧
  (∀ i : U64, i.val < 2 →
    σ.domainList[i.val]? = some (BitVec.ofNat 8 (m (ksW kb (entOff i))).val,
      BitVec.ofNat 56 (m (ksW kb (durOff i))).val) ∧
    (m (ksW kb (entOff i))).val < 2 ^ 8 ∧ (m (ksW kb (durOff i))).val < 2 ^ 56 ∧
    (m (ksW kb (durOff i)) = 0#u64 → m (ksW kb (entOff i)) = 0#u64)) ∧
  σ.domainStartIndex = (m (ksW kb 32#u64)).val

/-- `DomRel` is StepSem's `DomRelW`. -/
theorem domRel_iff {m : U64 → U64} {kb : U64} {σ : Fl4Spec.State Unit} : DomRel m kb σ ↔ DomRelW m kb σ :=
  Iff.rfl

/-- The words of the domain schedule are the same. -/
def DomSame (m m' : U64 → U64) (kb : U64) : Prop :=
  m' (ksW kb 32#u64) = m (ksW kb 32#u64) ∧
  ∀ i : U64, i.val < 2 → m' (ksW kb (entOff i)) = m (ksW kb (entOff i)) ∧
    m' (ksW kb (durOff i)) = m (ksW kb (durOff i))

theorem DomSame.refl (m : U64 → U64) (kb : U64) : DomSame m m kb := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem DomSame.trans {m1 m2 m3 : U64 → U64} {kb : U64} (h1 : DomSame m1 m2 kb) (h2 : DomSame m2 m3 kb) :
    DomSame m1 m3 kb :=
  ⟨h2.1.trans h1.1, fun i hi => ⟨(h2.2 i hi).1.trans (h1.2 i hi).1, (h2.2 i hi).2.trans (h1.2 i hi).2⟩⟩

theorem DomRel.of_same {m m' : U64 → U64} {kb : U64} {σ σ' : Fl4Spec.State Unit} (h : DomRel m kb σ)
    (hs : DomSame m m' kb) (hl : σ'.domainList = σ.domainList) (hst : σ'.domainStartIndex = σ.domainStartIndex) :
    DomRel m' kb σ' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [hl]; exact h1, fun i hi => ?_, by rw [hst, hs.1]; exact h3⟩
  rw [(hs.2 i hi).1, (hs.2 i hi).2, hl]; exact h2 i hi

/-- A write to an aligned word outside the domain schedule keeps it. -/
theorem domSame_wr {kb a v : U64} (hf : kb.val + 13568 ≤ 2 ^ 64) (hkb : kb.val % 8 = 0) (ha : P1.Aligned a)
    (hout : ∀ o : U64, o.val < 256 → (ksW kb o).val ≠ a.val ∨ o.val ∉ ({32, 192, 200, 208, 216} : Finset Nat))
    (s : S) : DomSame (L.mem s) (L.mem (L.wr s a v)) kb := by
  have hw : ∀ o : U64, o.val ∈ ({32, 192, 200, 208, 216} : Finset Nat) →
      L.mem (L.wr s a v) (ksW kb o) = L.mem s (ksW kb o) := by
    intro o ho
    have ho' : o.val < 256 := by simp at ho; omega
    have hv := ksW_val (kb := kb) (o := o) (by omega)
    rcases hout o ho' with h | h
    · exact L.mem_wr_ne ha (by unfold P1.Aligned; rw [hv]; simp at ho; omega) (Ne.symm h)
    · exact absurd ho h
  refine ⟨hw _ (by simp), fun i hi => ⟨hw _ ?_, hw _ ?_⟩⟩
  · rw [entOff_val hi]; simp; omega
  · rw [durOff_val hi]; simp; omega

/-- **The platform constant**: FL4 is built with one domain. -/
structure DomConfig : Prop where
  numDomains : Fl4Spec.numDomains = 1

/-- The spec's state after `domain_set_start`'s updates, before
`reschedule_required`. -/
def startSt (σ : Fl4Spec.State Unit) (n : Nat) : Fl4Spec.State Unit :=
  { { { σ with domainStartIndex := n } with domainTime := 0 } with domainIndex := σ.domainList.length - 2 }

/-- FL4's state after ScheduleSetStart's writes, before
`reschedule_required`. -/
def startS (s1 : S) (kb index : U64) : S :=
  L.wr (L.wr (L.wr s1 (ksW kb 32#u64) index) (ksW kb 16#u64) 0#u64) (ksW kb 24#u64) 0#u64

/-- **The scheduler step of DomainSetSet** (for the scheduler's proofs):
from the state after `set_thread_state Restart`, FL4's `set_domain` of a TCB
to a domain below `NUM_DOMAINS` keeps the slots and the domain schedule, and
the spec's `invoke_set_domain` has an outcome that keeps the CNodes and
TCBs, the CSpace relation, the CDT and the domain schedule; the run made of
primitive steps (`Steps`). -/
def DomSetHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ s1 σ1 (t d : U64), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) →
    th t = some .tcb → d.val < 1 →
    sched.set_domain st s1 t d ⦃ s2 => SlotsSame th (L.mem s1) (L.mem s2) ∧ L.ksb s2 = L.ksb s1 ∧
      DomSame (L.mem s1) (L.mem s2) (L.ksb s1) ∧
      ∃ y ∈ (Fl4Spec.invokeSetDomain (Z := Unit) t.bv (Fl4Spec.ucast Fl4Spec.domainLen d.bv) σ1).1,
        KSub σ1 y.2 ∧ (∀ m, StateRel th m σ1 → StateRel th m y.2) ∧ y.2.cdt = σ1.cdt ∧
        y.2.isOriginalCap = σ1.isOriginalCap ∧ y.2.domainList = σ1.domainList ∧
        y.2.domainStartIndex = σ1.domainStartIndex ∧
        ∀ (A : Type) (arI : machine.Arch A) (a : A), Steps (L := L) arI th s1 a σ1 s2 a y.2 ⦄

/-- **The scheduler step of ScheduleSetStart** (for the scheduler's
proofs): FL4's `reschedule_required` after the decode's writes, and the
spec's `reschedule_required` after `domain_set_start`'s updates; the run
made of primitive steps (`Steps`). -/
def DomResHyp (th : TypedHeap) (s : S) (σ : Fl4Spec.State Unit) (ct : U64) : Prop :=
  ∀ s1 σ1 (index : U64), sched.set_thread_state st s ct sched.TS_RESTART = ok s1 →
    Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) → index.val < 2 →
    sched.reschedule_required st (startS (L := L) s1 (L.ksb s) index) ⦃ s5 =>
      SlotsSame th (L.mem (startS (L := L) s1 (L.ksb s) index)) (L.mem s5) ∧ L.ksb s5 = L.ksb s ∧
      DomSame (L.mem (startS (L := L) s1 (L.ksb s) index)) (L.mem s5) (L.ksb s) ∧
      ∃ y ∈ (Fl4Spec.rescheduleRequired (Z := Unit) (startSt σ1 index.val)).1,
        KSub (startSt σ1 index.val) y.2 ∧ (∀ m, StateRel th m (startSt σ1 index.val) → StateRel th m y.2) ∧
        y.2.cdt = σ1.cdt ∧ y.2.isOriginalCap = σ1.isOriginalCap ∧ y.2.domainList = σ1.domainList ∧
        y.2.domainStartIndex = index.val ∧
        ∀ (A : Type) (arI : machine.Arch A) (a : A),
          Steps (L := L) arI th (startS (L := L) s1 (L.ksb s) index) a (startSt σ1 index.val) s5 a y.2 ⦄

/-- **The result of `domain::decode`**: the spec's error with the state
unchanged, or the spec's decode, `set_thread_state Restart` and an outcome
of `invoke_domain`, with the CSpace relation, `FinInv` and `DomRel`; the run
made of primitive steps (`Steps`, at every arch state). -/
def DomPost (th : TypedHeap) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.DomainInvocation) (s : S) (res : core.result.Result Unit error.Exc × S) :
    Prop :=
  (∃ e, res.1 = .Err e ∧ res.2 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ SysErrRel e e') ∨
  (res.1 = .Ok () ∧ ∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ (Fl4Spec.invokeDomain (Z := Unit) inv σ1).1, SlotsSame th (L.mem s) (L.mem res.2) ∧
      CRel th (L.mem res.2) y.2 G ∧ FinInv th (L.mem res.2) y.2 G ∧ L.ksb res.2 = L.ksb s ∧
      DomRel (L.mem res.2) (L.ksb res.2) y.2 ∧
      (CurRun σ → ∀ (A : Type) (arI : machine.Arch A) (a : A), Steps (L := L) arI th s a σ res.2 a y.2))

theorem dom_err {th : TypedHeap} {σ : Fl4Spec.State Unit} {G : MdbGhost}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.DomainInvocation} {s : S} {e : error.Exc} {e' : Fl4Spec.SyscallError}
    (h : m.run σ = ({(.error e', σ)}, False)) (he : SysErrRel e e') :
    (ok ((.Err e, s) : core.result.Result Unit error.Exc × S)) ⦃ res => DomPost (L := L) th σ G m s res ⦄ := by
  rw [WP.spec_ok]; exact Or.inl ⟨e, rfl, rfl, e', h, he⟩

/-- The CSpace parts and `FinInv` carried by a step that keeps the slots. -/
theorem crel_step {th : TypedHeap} {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit} {G : MdbGhost}
    (hCR : CRel th m σ G) (hFI : FinInv th m σ G) (hS : SlotsSame th m m') (hK : KSub σ σ')
    (hR' : StateRel th m' σ') (hcdt : σ'.cdt = σ.cdt) (hio : σ'.isOriginalCap = σ.isOriginalCap) :
    CRel th m' σ' G ∧ FinInv th m' σ' G := by
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  exact ⟨⟨hR', hV.of_caps (fun x hx => hS.capAt hx), hM.of_same hS, hC.of_same hS hcdt hio, MdbInv.of_same hM hI hS⟩,
    hFI.of_same hM hS hK⟩

/-- A word of the kernel-global area below 256, aligned. -/
theorem ksW_al {kb o : U64} (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) (ho : o.val < 256)
    (h8 : o.val % 8 = 0) : P1.Aligned (ksW kb o) := by
  unfold P1.Aligned; rw [ksW_val (by omega)]; omega

/-- **`set_thread_state Restart`**, with the CSpace parts, `FinInv` and the
domain schedule. -/
theorem dom_restart (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (_hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val) :
    ∃ s1, sched.set_thread_state st s ct sched.TS_RESTART = ok s1 ∧ SlotsSame th (L.mem s) (L.mem s1) ∧
      L.ksb s1 = L.ksb s ∧ ∃ σ1, Fl4Spec.setThreadState (Z := Unit) ct.bv .restart σ = ({((), σ1)}, False) ∧
      CRel th (L.mem s1) σ1 G ∧ FinInv th (L.mem s1) σ1 G ∧ DomRel (L.mem s1) (L.ksb s) σ1 ∧
      σ1.domainList = σ.domainList ∧
      (CurRun σ → ∀ (A : Type) (arI : machine.Arch A) (a : A), Steps (L := L) arI th s a σ s1 a σ1) := by
  have htf := hP.fits ct _ htcb
  have hta := hP.align ct _ htcb
  have hstv : (stA ct).val = ct.val + 3328 := by
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  obtain ⟨s1, hs1, hS, hkb, hF⟩ := spec_exists (WP.spec_and (set_thread_state_slots (L := L) th hP s ct
    sched.TS_RESTART htcb hact) (WP.spec_and (set_thread_state_ksb (L := L) s ct sched.TS_RESTART)
    (set_thread_state_frame (L := L) s ct sched.TS_RESTART (by unfold P1.Aligned; rw [hstv]; omega) hact.1)))
  obtain ⟨hR, hV, hM, hC, hI⟩ := hCR
  obtain ⟨tcb, hkt, -⟩ := hR.tcb ct htcb
  obtain ⟨σ1, hst1, hR1, hV1, hM1, hC1, hcdt1, hio1⟩ := restart_rel hR hV hM hC hS (t := ct.bv) hkt .restart
  have hdl : σ1.domainList = σ.domainList ∧ σ1.domainStartIndex = σ.domainStartIndex := by
    have e := Notif.setThreadState_eq (Z := Unit) .restart hkt
    rw [hst1] at e
    have e' : σ1 = Notif.stsAct (Notif.updK σ ct.bv (.tcb { tcb with tcbState := .restart })) ct.bv := by
      have := congrArg (fun x => x.1) e; simpa using this
    subst e'
    unfold Notif.stsAct; split <;> exact ⟨rfl, rfl⟩
  have hw : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → L.mem s1 (ksW (L.ksb s) o) = L.mem s (ksW (L.ksb s) o) := by
    intro o ho h8
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    apply hF _ (ksW_al hkf hka ho h8)
    · rw [hstv]; intro e
      have := (hksO o ho h8).2 ct .tcb htcb
      have e4 : objSize ObjKind.tcb = 4096 := rfl
      rw [e4] at this; exact this ⟨by omega, by omega⟩
    · exact fun e => hactK o ho e.symm
  have hDS : DomSame (L.mem s) (L.mem s1) (L.ksb s) := by
    refine ⟨hw _ (by decide) (by decide), fun i hi => ⟨hw _ ?_ ?_, hw _ ?_ ?_⟩⟩ <;>
      first | (rw [entOff_val hi]; omega) | (rw [durOff_val hi]; omega)
  refine ⟨s1, hs1, hS, hkb, σ1, hst1, ?_⟩
  have hK := ksub_of_eq (setThreadState_nks _ _) hst1
  obtain ⟨hCR1, hFI1⟩ := crel_step ⟨hR, hV, hM, hC, hI⟩ hFI hS hK hR1 hcdt1 hio1
  exact ⟨hCR1, hFI1, hDR.of_same hDS hdl.1 hdl.2, hdl.1, fun hC A arI a =>
    Steps.restart arI _hcur hkt htcb hs1 (by rw [_hcur]; exact hst1) hC⟩

/-! ## FL4's steps -/

theorem nds_eq : layout.NUM_DOMAIN_SCHEDULES = 2#u64 := by
  unfold layout.NUM_DOMAIN_SCHEDULES fl4_abi.config.NUM_DOMAIN_SCHEDULES; rfl

theorem nd_eq : layout.NUM_DOMAINS = 1#u64 := by
  unfold layout.NUM_DOMAINS fl4_abi.config.NUM_DOMAINS; rfl

theorem ks_set_eq (s : S) (off v : U64) : obj.ks_set st s off v = ok (L.wr s (ksW (L.ksb s) off) v) := by
  unfold obj.ks_set; simp [L.ks_base_eq, L.write_eq, lift, ksW]

theorem ks_get_eq (s : S) (off : U64) : obj.ks_get st s off = ok (L.mem s (ksW (L.ksb s) off)) := by
  unfold obj.ks_get; simp [L.ks_base_eq, L.read_eq, lift, ksW]

theorem dur_eq (s : S) (i : U64) :
    sched.dom_sched_duration st s i = ok (L.mem s (ksW (L.ksb s) (durOff i))) := by
  unfold sched.dom_sched_duration
  rw [show layout.ks.DOM_SCHEDULE = ok 192#u64 by unfold layout.ks.DOM_SCHEDULE layout.WORD; rfl]
  simp only [lift, bind_ok, ks_get_eq]; rfl

theorem set_dom_sched_eq (s : S) (i d du : U64) :
    sched.set_dom_sched st s i d du =
      ok (L.wr (L.wr s (ksW (L.ksb s) (entOff i)) d) (ksW (L.ksb s) (durOff i)) du) := by
  unfold sched.set_dom_sched
  rw [show layout.ks.DOM_SCHEDULE = ok 192#u64 by unfold layout.ks.DOM_SCHEDULE layout.WORD; rfl]
  simp only [lift, bind_ok, ks_set_eq, L.ksb_wr]; rfl

theorem outside_slot {th : TypedHeap} (hP : Placed th) {A : U64} (hO : OutsideObjects th A) :
    ∀ a, IsSlot th a → ¬ (a.val ≤ A.val ∧ A.val < a.val + 32) := by
  intro a ha h
  obtain ⟨p, k, hp, h1, h2, -⟩ := slot_in_object hP ha
  exact hO.2 p k hp ⟨by omega, by omega⟩

/-- The writes of a kernel-global word below 256 keep the slots. -/
theorem slotsSame_ks {th : TypedHeap} (hP : Placed th) (s : S) {kb o : U64} (v : U64)
    (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) (ho : o.val < 256) (h8 : o.val % 8 = 0)
    (hO : OutsideObjects th (ksW kb o)) : SlotsSame th (L.mem s) (L.mem (L.wr s (ksW kb o) v)) :=
  slotsSame_wr hP s v (ksW_al hkf hka ho h8) (outside_slot hP hO)

theorem mem_ks_ne (s : S) {kb o o' : U64} (v : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (ho : o.val < 256) (h8 : o.val % 8 = 0) (ho' : o'.val < 256) (h8' : o'.val % 8 = 0) (hne : o.val ≠ o'.val) :
    L.mem (L.wr s (ksW kb o) v) (ksW kb o') = L.mem s (ksW kb o') :=
  L.mem_wr_ne (ksW_al hkf hka ho h8) (ksW_al hkf hka ho' h8')
    (by rw [ksW_val (by omega), ksW_val (by omega)]; omega)

theorem mem_ks_same (s : S) {kb o : U64} (v : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (ho : o.val < 256) (h8 : o.val % 8 = 0) : L.mem (L.wr s (ksW kb o) v) (ksW kb o) = v :=
  L.mem_wr_same (ksW_al hkf hka ho h8)

theorem mem_setStart {σ1 : Fl4Spec.State Unit} {n : Nat} {y : Unit × Fl4Spec.State Unit}
    (h : y ∈ (Fl4Spec.rescheduleRequired (Z := Unit) (startSt σ1 n)).1) :
    y ∈ (Fl4Spec.domainSetStart (Z := Unit) n σ1).1 := by
  unfold Fl4Spec.domainSetStart
  exact mem_bind_nd rfl (mem_bind_nd rfl (mem_bind_nd rfl (mem_bind_nd rfl h)))

theorem dur_off_bounds {i : U64} (hi : i.val < 2) :
    (entOff i).val < 256 ∧ (entOff i).val % 8 = 0 ∧ (durOff i).val < 256 ∧ (durOff i).val % 8 = 0 ∧
    (entOff i).val ≠ 32 ∧ (entOff i).val ≠ 16 ∧ (entOff i).val ≠ 24 ∧
    (durOff i).val ≠ 32 ∧ (durOff i).val ≠ 16 ∧ (durOff i).val ≠ 24 := by
  rw [entOff_val hi, durOff_val hi]; omega

theorem wtrans {s₁ s₂ s₃ : S} {A : U64 → Prop} (h₁ : P1.WritesIn st s₁ s₂ A) (h₂ : P1.WritesIn st s₂ s₃ A) :
    P1.WritesIn st s₁ s₃ A := (h₁.trans h₂).mono fun _ hb => by rcases hb with hb | hb <;> exact hb

/-- A write of a domain-schedule word (`DomKW`). -/
theorem writesIn_ksW (s : S) {kb o : U64} (v : U64) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (ho : o.val ∈ ([16, 24, 32, 192, 200, 208, 216] : List Nat)) :
    P1.WritesIn st s (L.wr s (ksW kb o) v) (DomKW kb) := by
  have ho' : o.val < 256 ∧ o.val % 8 = 0 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; omega
  exact (P1.writesIn_wr (ksW_al hkf hka ho'.1 ho'.2)).mono fun b hb => ⟨o.val, ho, by rw [hb, ksW_val (by omega)]⟩

/-- **The scheduler relation across writes of the domain schedule's words**
(`DomKW`), the spec changing only the domain fields, with the domain time
the `DOMAIN_TIME` word after. -/
theorem Sched.SchedRel.domW {N T C : Set U64} {c : U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (hS : Sched.SchedRel st N T C c s σ) (hw : P1.WritesIn st s s' (DomKW (L.ksb s)))
    (hK : SchedK σ σ') (hrq : σ'.readyQueues = σ.readyQueues) (hact : σ'.schedulerAction = σ.schedulerAction)
    (hdt : σ'.domainTime = (L.mem s' (Sched.dtA st s)).bv) : Sched.SchedRel st N T C c s' σ' := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hN := hc.node
  have hk : L.ksb s' = L.ksb s := hw.1
  have hf := hN.fits; have hal := hN.align
  simp only [P1.LawfulStore.nodeBase] at hf hal
  have hm : ∀ b : U64, P1.Aligned b → (b.val < (L.ksb s).val + 16 ∨ (L.ksb s).val + 216 < b.val) →
      L.mem s' b = L.mem s b :=
    fun b hb h => hw.mem_eq hb fun hd => by have := domKW_val hd; omega
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun o ho h8 => hm _ (P1.nodeAt_aligned hN ho h8) (Or.inr (by
      rw [P1.nodeAt_val hN ho]; simp only [P1.LawfulStore.nodeBase]; omega))
  have nwo : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Sched.nodeW st s' c o = Sched.nodeW st s c o := by
    intro o ho h8; unfold Sched.nodeW; rw [Sched.nodeAt_ksb hk]; exact hnode o ho h8
  have htf : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) := by
    intro y hy K h1 h2
    have hya := hc.tcbs y hy
    refine hm _ (P1.field_aligned hya h1 h2) ?_
    rw [Notif.tfield_val hya h1]; rcases hc.ksOut y hy with h | h <;> omega
  have hsc : ∀ sc ∈ C, Sched.ScAgree st s s' sc := fun sc hsc' b hb hin =>
    hm b hb (by rcases (hS.scOutIn hsc' hin).2.2.2 with h | h <;> omega)
  have hcd : L.mem s' (Sched.curDomA st s) = L.mem s (Sched.curDomA st s) := by
    have hv : (Sched.curDomA st s).val = (L.ksb s).val + 8 := by
      simp [Sched.curDomA, core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    exact hm _ (by unfold P1.Aligned; rw [hv]; omega) (Or.inl (by omega))
  have hca : Sched.CAgree st T c s s' :=
    ⟨hk, hw.2.1, fun o ho h8 _ _ _ _ _ _ _ => hnode o ho h8, fun y hy K hK => htf y hy K (by
      rcases hK with rfl | rfl | rfl | rfl | rfl <;> simp) (by rcases hK with rfl | rfl | rfl | rfl | rfl <;> simp)⟩
  have hz : Sched.SzKeep σ σ' := Sched.SzKeep.of_kheap hK.kh
  refine ⟨hS.placed, fun o ho => by rw [Sched.nodeAt_ksb hk]; exact hS.nodeNW o ho,
    by rw [Sched.curDomA_ksb hk]; exact hS.domNW, by rw [Sched.dtA_ksb hk]; exact hS.dtNW,
    Sched.scOut_transfer hk hz hS.scOut, Sched.scDisj_transfer hz hS.scDisj,
    by rw [nwo _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])]; exact hS.actW,
    by rw [nwo _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]), hact]; exact hS.act,
    by rw [nwo _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]), hK.repr]; exact hS.repr,
    hs.core_eq hsc hS.core, Q, R0, hc.agree hca, ?_⟩
  refine ⟨fun p hp => by rw [hrq]; exact hs.rq p hp, fun d p hd => by rw [hrq]; exact hs.rqDom d p hd,
    by rw [hK.rel]; exact hs.rel, ?_, ?_, ?_, ?_, ?_, fun t ht => ?_, fun t ht h0 => ?_, fun sc hsc' => ?_, ?_,
    by rw [hdt, Sched.dtA_ksb hk], ?_⟩
  · rw [hK.ct, nwo _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])]; exact hs.curThread
  · rw [hK.csc, nwo _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hs.curSc
  · rw [hK.ctime, nwo _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])]; exact hs.curTime
  · rw [hK.cons, nwo _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])]; exact hs.consumed
  · rw [hK.cdom, Sched.curDomA_ksb hk, hcd]; exact hs.curDom
  · obtain ⟨x, hkx, h1, h2, h3, h4⟩ := hs.tcb t ht
    refine ⟨x, by rw [hK.kh]; exact hkx, h1, ?_, ?_, ?_⟩
    · rw [P1.domA, htf t ht _ (by decide) (by decide)]; exact h2
    · rw [P1.scA, htf t ht _ (by decide) (by decide)]; exact h3
    · rw [P1.prioA, htf t ht _ (by decide) (by decide)]; exact h4
  · have e : L.mem s' (P1.scA t) = L.mem s (P1.scA t) := by rw [P1.scA, htf t ht _ (by decide) (by decide)]
    rw [e] at h0 ⊢; exact hs.scMem t ht h0
  · obtain ⟨x, n, hkx, e⟩ := hs.scs sc hsc'
    exact ⟨x, n, by rw [hK.kh]; exact hkx, e.agree (hsc sc hsc')⟩
  · rw [nwo _ (by simp [layout.node.IDLE_SC]) (by simp [layout.node.IDLE_SC])]; exact hs.idleSc
  · rw [hK.idle, nwo _ (by simp [layout.node.IDLE_THREAD]) (by simp [layout.node.IDLE_THREAD])]; exact hs.idleTh

/-- **Writes of the domain schedule's words keep P1's `BlkOK`**: they are
kernel-state words, in `Ω` and no SC's (`SgOK`). -/
theorem blkKeep_domKW {th : TypedHeap} {s s' : S} (hw : P1.WritesIn st s s' (DomKW (L.ksb s)))
    (hka : (L.ksb s).val % 8 = 0) : BlkKeep (L := L) th s s' := by
  intro T Cs Ω H Sg Rp Scs Nt Z Ac _ h
  have hw' : P1.WritesIn st s s' (fun b => DomKW (L.ksb s) b ∧ P1.Aligned b) :=
    ⟨hw.1, hw.2.1, fun b hb hn => hw.2.2 b hb fun h => hn ⟨h, hb⟩⟩
  have hSg := h.2.2.2.2
  have h0 := h.1.choose_spec.choose_spec
  refine (P1.blk_of_capw h hw' fun b hb => ?_).1
  obtain ⟨⟨K, hK, e⟩, hal⟩ := hb
  have hb8 : b.val % 8 = 0 := hal
  refine Or.inr ⟨?_, fun hm => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 16#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 24#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 32#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 192#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 200#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 208#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
      | (have eb : b = core.num.U64.wrapping_add (L.ksb s) 216#u64 :=
            UScalar.eq_of_val_eq (by rw [P1.ks_val h0 (by decide)]; simpa using e)
         rw [eb]; exact hSg.ksΩ _ (by decide) (by decide))
  · have := hSg.ks b hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    omega

/-- **ScheduleSetStart's writes as a scheduler step** (`SchedStep`): the
start, the domain time and index words, against `domain_set_start`'s
updates. -/
theorem schedStep_start (th : TypedHeap) (s1 : S) (σ1 : Fl4Spec.State Unit) {kb : U64} (y0 : U64)
    (hk1 : L.ksb s1 = kb) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) :
    SchedStep (L := L) th s1 σ1 (startS (L := L) s1 kb y0) (startSt σ1 y0.val) := by
  subst hk1
  set kb := L.ksb s1
  have hw : P1.WritesIn st s1 (startS (L := L) s1 kb y0) (DomKW kb) :=
    wtrans (wtrans (writesIn_ksW s1 y0 hkf hka (o := 32#u64) (by simp))
      (writesIn_ksW _ 0#u64 hkf hka (o := 16#u64) (by simp))) (writesIn_ksW _ 0#u64 hkf hka (o := 24#u64) (by simp))
  have hw4 : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → o.val ≠ 32 → o.val ≠ 16 → o.val ≠ 24 →
      L.mem (startS (L := L) s1 kb y0) (ksW kb o) = L.mem s1 (ksW kb o) := by
    intro o ho h8 n32 n16 n24
    rw [startS, mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n24.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n16.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n32.symm)]
  have h32 : L.mem (startS (L := L) s1 kb y0) (ksW kb 32#u64) = y0 := by
    rw [startS, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_same _ _ hkf hka (by decide) (by decide)]
  have h16 : L.mem (startS (L := L) s1 kb y0) (ksW kb 16#u64) = 0#u64 := by
    rw [startS, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_same _ _ hkf hka (by decide) (by decide)]
  refine ⟨by constructor <;> rfl, fun N T C c _ hS _ => ⟨hS.domW hw (by constructor <;> rfl) rfl rfl ?_,
    hw.mono fun b hb => Or.inr (Or.inr hb), fun hD => ?_⟩, ⟨fun d p _ hu => Or.inl ⟨d, p, hu⟩, Or.inr rfl⟩, blkKeep_domKW hw hka⟩
  · show (0 : BitVec 64) = (L.mem (startS (L := L) s1 kb y0) (ksW kb 16#u64)).bv
    rw [h16]; rfl
  · obtain ⟨hl1, hent1, -⟩ := domRel_iff.2 hD
    refine domRel_iff.1 ⟨hl1, fun i hi => ?_, by rw [h32]; rfl⟩
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := dur_off_bounds hi
    rw [hw4 _ b1 b2 b5 b6 b7, hw4 _ b3 b4 b8 b9 b10]
    exact hent1 i hi

/-- **DomainScheduleSetStart.** -/
theorem dom_start_refines (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (slbl : Fl4Spec.Data) (hg : Fl4Spec.genInvocationType slbl = .domainScheduleSetStart)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hRes : DomResHyp (L := L) th s σ ct) :
    domain.decode st s fl4_abi.label.DomainScheduleSetStart length buf extra ⦃ res =>
      DomPost (L := L) th σ G (Fl4Spec.decodeDomainInvocation slbl (args.map UScalar.bv) excs) s res ⦄ := by
  set kb := L.ksb s with hkbdef
  unfold domain.decode
  have n1 : ¬ fl4_abi.label.DomainScheduleSetStart = fl4_abi.label.DomainSetSet := by
    rw [u64_eq_iff]; simp [fl4_abi.label.DomainScheduleSetStart, fl4_abi.label.DomainSetSet]
  have n2 : ¬ fl4_abi.label.DomainScheduleSetStart = fl4_abi.label.DomainScheduleConfigure := by
    rw [u64_eq_iff]; simp [fl4_abi.label.DomainScheduleSetStart, fl4_abi.label.DomainScheduleConfigure]
  rw [hct]; simp only [bind_ok, n1, n2, ↓reduceIte]
  by_cases h1 : length < 1#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    have : args = [] := List.eq_nil_of_length_eq_zero (by rw [← hlen]; scalar_tac)
    subst this
    exact dom_err (dec_start_nil hg _) trivial
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), bind_ok, nds_eq]
  have hspec := dec_start (σ := σ) hg y0.bv (rest.map UScalar.bv) excs
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  obtain ⟨hl, hent, hstart⟩ := hDR
  have hun : Fl4Spec.unat y0.bv = y0.val := rfl
  rw [hl, hun] at hspec
  by_cases h2 : y0 ≥ 2#u64
  · rw [if_pos h2]
    simp only [show (2#u64 - 1#u64 : Result U64) = ok 1#u64 from rfl, error.range, bind_ok]
    refine dom_err (e' := .rangeError 0 (BitVec.ofNat 64 (2 - 1))) ?_ ⟨rfl, rfl⟩
    rw [hmap, hspec, if_pos (by scalar_tac)]
  rw [if_neg h2]
  have hy : y0.val < 2 := by scalar_tac
  rw [dur_eq]; simp only [bind_ok]
  obtain ⟨hlist, hdlt, hult, hz⟩ := hent y0 hy
  by_cases h3 : L.mem s (ksW kb (durOff y0)) = 0#u64
  · rw [if_pos h3]; simp only [error.invalid_arg, bind_ok]
    refine dom_err (e' := .invalidArgument 0) ?_ rfl
    rw [hmap, hspec, if_neg (by omega), if_pos ?_]
    rw [hlist, hz h3, h3]; rfl
  rw [if_neg h3]
  have hne : ¬ Fl4Spec.the σ.domainList[y0.val]? = Fl4Spec.domainEndMarker := by
    intro e; rw [hlist] at e
    change (BitVec.ofNat 8 _, BitVec.ofNat 56 _) = Fl4Spec.domainEndMarker at e
    have e2 := congrArg (fun x => x.2.toNat) e
    simp only [Fl4Spec.domainEndMarker, BitVec.toNat_ofNat] at e2
    rw [Nat.mod_eq_of_lt hult] at e2
    exact h3 (UScalar.eq_of_val_eq (e2.trans rfl))
  -- `set_thread_state Restart`
  obtain ⟨s1, hs1, hS1, hkb1, σ1, hst1, hCR1, hFI1, hDR1, hdl1, hstR⟩ :=
    dom_restart th hP s σ G hCR hFI ⟨hl, hent, hstart⟩ ct hcur htcb hact hkf hka hksO hactK
  rw [hs1]
  simp only [bind_ok, ks_set_eq, hkb1, L.ksb_wr, show (2#u64 - 2#u64 : Result U64) = ok 0#u64 from rfl,
    show layout.ks.DOM_SCHED_START = 32#u64 by unfold layout.ks.DOM_SCHED_START; rfl,
    show layout.ks.DOMAIN_TIME = 16#u64 by unfold layout.ks.DOMAIN_TIME; rfl,
    show layout.ks.DOM_SCHED_IDX = 24#u64 by unfold layout.ks.DOM_SCHED_IDX; rfl]
  refine WP.spec_bind (hRes s1 σ1 y0 hs1 hst1 hy) ?_
  rintro s5 ⟨hS5, hkb5, hDS5, y, hy5, hK, hSR, hcdt, hio, hdl, hst5, hss⟩
  rw [WP.spec_ok]
  -- the slots and the domain words of the writes
  set s4 := startS (L := L) s1 kb y0 with hs4
  have hS4 : SlotsSame th (L.mem s1) (L.mem s4) := by
    refine (slotsSame_ks (o := 32#u64) hP s1 y0 hkf hka (by decide) (by decide)
      (hksO _ (by decide) (by decide))).trans ?_
    refine (slotsSame_ks (o := 16#u64) hP (L.wr s1 (ksW kb 32#u64) y0) 0#u64 hkf hka (by decide) (by decide)
      (hksO _ (by decide) (by decide))).trans ?_
    exact slotsSame_ks (o := 24#u64) hP (L.wr (L.wr s1 (ksW kb 32#u64) y0) (ksW kb 16#u64) 0#u64) 0#u64 hkf hka
      (by decide) (by decide) (hksO _ (by decide) (by decide))
  have hw4 : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → o.val ≠ 32 → o.val ≠ 16 → o.val ≠ 24 →
      L.mem s4 (ksW kb o) = L.mem s1 (ksW kb o) := by
    intro o ho h8 n32 n16 n24
    rw [hs4, startS, mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n24.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n16.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n32.symm)]
  have h32 : L.mem s4 (ksW kb 32#u64) = y0 := by
    rw [hs4, startS, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_same _ _ hkf hka (by decide) (by decide)]
  obtain ⟨hl1, hent1, hst1'⟩ := hDR1
  have hDR4 : DomRel (L.mem s4) kb (startSt σ1 y0.val) := by
    refine ⟨hl1, fun i hi => ?_, by rw [h32]; rfl⟩
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ := dur_off_bounds hi
    rw [hw4 _ b1 b2 b5 b6 b7, hw4 _ b3 b4 b8 b9 b10]
    exact hent1 i hi
  have hR4 : StateRel th (L.mem s4) (startSt σ1 y0.val) :=
    (hCR1.1.of_caps (fun x hx => hS4.capAt hx)).of_kheap rfl
  have hR5 : StateRel th (L.mem s5) y.2 := (hSR _ hR4).of_caps (fun x hx => hS5.capAt hx)
  obtain ⟨hCR5, hFI5⟩ := crel_step hCR1 hFI1 (hS4.trans hS5) ((KSub.of_kheap rfl).trans hK) hR5 hcdt hio
  refine Or.inr ⟨rfl, .invokeDomainScheduleSetStart y0.val, by rw [hmap, hspec, if_neg (by omega), if_neg hne], σ1, by rw [hcur]; exact hst1,
    y, mem_setStart hy5, hS1.trans (hS4.trans hS5), hCR5, hFI5, hkb5, ?_, fun hC A arI a =>
      ((hstR hC A arI a).trans arI (Steps.sched arI (schedStep_start th s1 σ1 y0 hkb1 hkf hka))).trans arI
        (hss A arI a)⟩
  rw [hkb5]
  exact hDR4.of_same hDS5 hdl hst5

theorem ucast_ofNat (w : Nat) (x : U64) : Fl4Spec.ucast w x.bv = BitVec.ofNat w x.val := by
  apply BitVec.eq_of_toNat_eq; simp [Fl4Spec.ucast, BitVec.toNat_setWidth]

/-- ScheduleConfigure's entry 0 written: the domain relation. -/
theorem domRel_conf (s1 : S) {kb : U64} (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0)
    (σ1 : Fl4Spec.State Unit) (y1 y2 : U64) (h1 : y1.val = 0) (h2 : y2.val < 2 ^ 56)
    (hD : DomRel (L.mem s1) kb σ1) :
    DomRel (L.mem (L.wr (L.wr s1 (ksW kb 192#u64) y1) (ksW kb 200#u64) y2)) kb
      { σ1 with domainList := (σ1.domainList.set (Fl4Spec.unat (0#u64 : U64).bv)
        (Fl4Spec.ucast Fl4Spec.domainLen y1.bv, Fl4Spec.ucast Fl4Spec.domainDurationLen y2.bv)) } := by
  have e0 : entOff 0#u64 = 192#u64 := rfl
  have d0 : durOff 0#u64 = 200#u64 := rfl
  set s2 := L.wr (L.wr s1 (ksW kb 192#u64) y1) (ksW kb 200#u64) y2 with hs2
  have hw : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → o.val ≠ 192 → o.val ≠ 200 →
      L.mem s2 (ksW kb o) = L.mem s1 (ksW kb o) := by
    intro o ho h8 n1 n2
    rw [hs2, mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n2.symm),
      mem_ks_ne _ _ hkf hka (by decide) (by decide) ho h8 (by simpa using n1.symm)]
  have w192 : L.mem s2 (ksW kb 192#u64) = y1 := by
    rw [hs2, mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
      mem_ks_same _ _ hkf hka (by decide) (by decide)]
  have w200 : L.mem s2 (ksW kb 200#u64) = y2 := by
    rw [hs2, mem_ks_same _ _ hkf hka (by decide) (by decide)]
  obtain ⟨hl1, hent1, hst1'⟩ := hD
  set ent : Fl4Spec.Domain × Fl4Spec.DomainDuration :=
    (Fl4Spec.ucast Fl4Spec.domainLen y1.bv, Fl4Spec.ucast Fl4Spec.domainDurationLen y2.bv) with hent
  refine ⟨by simp [hl1], fun i hi => ?_, by
    rw [hw _ (by decide) (by decide) (by decide) (by decide)]; exact hst1'⟩
  rcases (show i.val = 0 ∨ i.val = 1 by omega) with hi0 | hi1
  · have : i = 0#u64 := UScalar.eq_of_val_eq (by rw [hi0]; rfl)
    subst this
    rw [e0, d0, w192, w200]
    refine ⟨?_, by rw [h1]; decide, h2, fun _ => UScalar.eq_of_val_eq (by rw [h1]; rfl)⟩
    rw [hi0, show Fl4Spec.unat (0#u64 : U64).bv = 0 from rfl, List.getElem?_set_self (by rw [hl1]; decide),
      hent, ucast_ofNat, ucast_ofNat]; rfl
  · have : i = 1#u64 := UScalar.eq_of_val_eq (by rw [hi1]; rfl)
    subst this
    have e1 : entOff 1#u64 = 208#u64 := rfl
    have d1 : durOff 1#u64 = 216#u64 := rfl
    have := hent1 1#u64 hi
    rw [e1, d1] at this ⊢
    rw [hw _ (by decide) (by decide) (by decide) (by decide), hw _ (by decide) (by decide) (by decide) (by decide)]
    refine ⟨?_, this.2⟩
    rw [show Fl4Spec.unat (0#u64 : U64).bv = 0 from rfl, List.getElem?_set_ne (by decide)]
    exact this.1

/-- **ScheduleConfigure's writes as a scheduler step** (`SchedStep`): entry
0's words, against the spec's `domain_list` update. -/
theorem schedStep_conf (th : TypedHeap) (s1 : S) (σ1 : Fl4Spec.State Unit) {kb : U64} (y1 y2 : U64)
    (hk1 : L.ksb s1 = kb) (hkf : kb.val + 13568 ≤ 2 ^ 64) (hka : kb.val % 8 = 0) (h1 : y1.val = 0)
    (h2 : y2.val < 2 ^ 56) :
    SchedStep (L := L) th s1 σ1 (L.wr (L.wr s1 (ksW kb 192#u64) y1) (ksW kb 200#u64) y2)
      { σ1 with domainList := (σ1.domainList.set (Fl4Spec.unat (0#u64 : U64).bv)
        (Fl4Spec.ucast Fl4Spec.domainLen y1.bv, Fl4Spec.ucast Fl4Spec.domainDurationLen y2.bv)) } := by
  subst hk1
  have hw := wtrans (writesIn_ksW s1 y1 hkf hka (o := 192#u64) (by simp))
    (writesIn_ksW (L.wr s1 (ksW (L.ksb s1) 192#u64) y1) y2 hkf hka (o := 200#u64) (by simp))
  refine ⟨by constructor <;> rfl, fun N T C c _ hS _ => ⟨hS.domW hw (by constructor <;> rfl) rfl rfl ?_,
    hw.mono fun b hb => Or.inr (Or.inr hb), fun hD => domRel_iff.1
      (domRel_conf s1 hkf hka σ1 y1 y2 h1 h2 (domRel_iff.2 hD))⟩, ⟨fun d p _ hu => Or.inl ⟨d, p, hu⟩, Or.inr rfl⟩, blkKeep_domKW hw hka⟩
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  show σ1.domainTime = (L.mem _ (ksW (L.ksb s1) 16#u64)).bv
  rw [mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide),
    mem_ks_ne _ _ hkf hka (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact hs.domTime

/-- ScheduleConfigure's invocation: the entry written, with the CSpace parts,
`FinInv` and `DomRel`. -/
theorem dom_conf_ok (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.DomainInvocation) (y0 y1 y2 : U64) (h0 : y0.val = 0) (h1 : y1.val = 0)
    (h2 : y2.val < 2 ^ 56)
    (hm : m.run σ = ({(.ok (.invokeDomainScheduleConfigure (Fl4Spec.unat y0.bv)
      (Fl4Spec.ucast Fl4Spec.domainLen y1.bv) (Fl4Spec.ucast Fl4Spec.domainDurationLen y2.bv)), σ)}, False)) :
    (do
      let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
      let s2 ← sched.set_dom_sched st s1 y0 y1 y2
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ res =>
      DomPost (L := L) th σ G m s res ⦄ := by
  set kb := L.ksb s with hkbdef
  obtain ⟨s1, hs1, hS1, hkb1, σ1, hst1, hCR1, hFI1, hDR1, -, hstR⟩ :=
    dom_restart th hP s σ G hCR hFI hDR ct hcur htcb hact hkf hka hksO hactK
  rw [hs1]; simp only [bind_ok, set_dom_sched_eq, hkb1]
  rw [WP.spec_ok]
  have hy0 : y0 = 0#u64 := UScalar.eq_of_val_eq (by rw [h0]; rfl)
  subst hy0
  have e0 : entOff 0#u64 = 192#u64 := rfl
  have d0 : durOff 0#u64 = 200#u64 := rfl
  rw [e0, d0]
  set s2 := L.wr (L.wr s1 (ksW kb 192#u64) y1) (ksW kb 200#u64) y2 with hs2
  have hS2 : SlotsSame th (L.mem s1) (L.mem s2) :=
    (slotsSame_ks (o := 192#u64) hP s1 y1 hkf hka (by decide) (by decide) (hksO _ (by decide) (by decide))).trans
      (slotsSame_ks (o := 200#u64) hP _ y2 hkf hka (by decide) (by decide) (hksO _ (by decide) (by decide)))
  set σ2 : Fl4Spec.State Unit := { σ1 with domainList := (σ1.domainList.set (Fl4Spec.unat (0#u64 : U64).bv)
    (Fl4Spec.ucast Fl4Spec.domainLen y1.bv, Fl4Spec.ucast Fl4Spec.domainDurationLen y2.bv)) } with hσ2
  have hDR2 : DomRel (L.mem s2) kb σ2 := domRel_conf s1 hkf hka σ1 y1 y2 h1 h2 hDR1
  have hR2 : StateRel th (L.mem s2) σ2 := (hCR1.1.of_caps (fun x hx => hS2.capAt hx)).of_kheap rfl
  obtain ⟨hCR2, hFI2⟩ := crel_step (σ' := σ2) hCR1 hFI1 hS2 (KSub.of_kheap rfl) hR2 rfl rfl
  exact Or.inr ⟨rfl, _, hm, σ1, by rw [hcur]; exact hst1, ((), σ2), rfl, hS1.trans hS2, hCR2, hFI2,
    by rw [hs2, L.ksb_wr, L.ksb_wr, hkb1], by
    show DomRel (L.mem s2) (L.ksb s2) σ2
    rw [hs2, L.ksb_wr, L.ksb_wr, hkb1]; exact hDR2,
    fun hC A arI a => (hstR hC A arI a).trans arI (Steps.sched arI (schedStep_conf th s1 σ1 y1 y2 hkb1 hkf hka h1 h2))⟩

theorem maxdur_eq : domain.MAX_DURATION = ok ⟨BitVec.ofNat 64 (2 ^ 56 - 1)⟩ := by
  unfold domain.MAX_DURATION
  rw [shl_eq _ _ (by decide) (by decide)]
  simp only [bind_ok]
  have : (⟨U64.bv 1#u64 <<< I32.toNat 56#i32⟩ : U64) = 72057594037927936#u64 := by decide
  rw [this]
  rfl

/-- **DomainScheduleConfigure.** -/
theorem dom_conf_refines (hcfg : DomConfig) (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit)
    (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (slbl : Fl4Spec.Data) (hg : Fl4Spec.genInvocationType slbl = .domainScheduleConfigure)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    domain.decode st s fl4_abi.label.DomainScheduleConfigure length buf extra ⦃ res =>
      DomPost (L := L) th σ G (Fl4Spec.decodeDomainInvocation slbl (args.map UScalar.bv) excs) s res ⦄ := by
  set kb := L.ksb s with hkbdef
  unfold domain.decode
  have n1 : ¬ fl4_abi.label.DomainScheduleConfigure = fl4_abi.label.DomainSetSet := by
    rw [u64_eq_iff]; simp [fl4_abi.label.DomainScheduleConfigure, fl4_abi.label.DomainSetSet]
  rw [hct]; simp only [bind_ok, n1, ↓reduceIte]
  by_cases h1 : length < 3#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    exact dom_err (dec_conf_short hg _ (by rw [List.length_map, ← hlen]; scalar_tac) _) trivial
  rw [if_neg h1]
  obtain ⟨y0, y1, y2, rest, rfl⟩ : ∃ y0 y1 y2 rest, args = y0 :: y1 :: y2 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; scalar_tac
    | [_] => exfalso; simp at hlen; scalar_tac
    | [_, _] => exfalso; simp at hlen; scalar_tac
    | y0 :: y1 :: y2 :: rest => exact ⟨y0, y1, y2, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), hargs 1#u64 y1 (by simp), hargs 2#u64 y2 (by simp), bind_ok, nds_eq, nd_eq,
    show (2#u64 - 1#u64 : Result U64) = ok 1#u64 from rfl]
  have hspec := dec_conf (σ := σ) hg y0.bv y1.bv y2.bv (rest.map UScalar.bv) excs
  have hmap : List.map UScalar.bv (y0 :: y1 :: y2 :: rest) = y0.bv :: y1.bv :: y2.bv :: rest.map UScalar.bv := rfl
  obtain ⟨hl, hent, hstart⟩ := hDR
  have hu0 : Fl4Spec.unat y0.bv = y0.val := rfl
  have hu1 : Fl4Spec.unat y1.bv = y1.val := rfl
  rw [hl, hu0, hu1, hcfg.numDomains] at hspec
  by_cases c1 : y0 ≥ 1#u64
  · rw [if_pos c1]
    simp only [show (2#u64 - 2#u64 : Result U64) = ok 0#u64 from rfl, error.range, bind_ok]
    refine dom_err (e' := .rangeError 0 (BitVec.ofNat 64 (2 - 2))) ?_ ⟨rfl, rfl⟩
    rw [hmap, hspec, if_pos (by scalar_tac)]
  rw [if_neg c1]
  have hy0 : y0.val = 0 := by scalar_tac
  by_cases c2 : y1 ≥ 1#u64
  · rw [if_pos c2]
    simp only [show (1#u64 - 1#u64 : Result U64) = ok 0#u64 from rfl, error.range, bind_ok]
    refine dom_err (e' := .rangeError 0 (BitVec.ofNat 64 (1 - 1))) ?_ ⟨rfl, rfl⟩
    rw [hmap, hspec, if_neg (by omega), if_pos (by scalar_tac)]
  rw [if_neg c2]
  have hy1 : y1.val = 0 := by scalar_tac
  have hy1' : y1 = 0#u64 := UScalar.eq_of_val_eq (by rw [hy1]; rfl)
  rw [maxdur_eq]; simp only [bind_ok]
  have hmx : (y2.bv > Fl4Spec.maxDomainDuration) ↔ 2 ^ 56 - 1 < y2.val := by
    rw [show Fl4Spec.maxDomainDuration = BitVec.ofNat 64 (2 ^ 56 - 1) from rfl]
    exact bv_gt_iff y2 _ (by decide)
  by_cases c3 : y2 > (⟨BitVec.ofNat 64 (2 ^ 56 - 1)⟩ : U64)
  · rw [if_pos c3]; simp only [error.invalid_arg, bind_ok]
    refine dom_err (e' := .invalidArgument 2) ?_ rfl
    have : 2 ^ 56 - 1 < y2.val := by
      have : (⟨BitVec.ofNat 64 (2 ^ 56 - 1)⟩ : U64).val = 2 ^ 56 - 1 := by
        show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = _; simp
      scalar_tac
    rw [hmap, hspec, if_neg (by omega), if_neg (by omega), if_pos (hmx.2 this)]
  rw [if_neg c3]
  have hy2 : y2.val < 2 ^ 56 := by
    have : (⟨BitVec.ofNat 64 (2 ^ 56 - 1)⟩ : U64).val = 2 ^ 56 - 1 := by
      show (BitVec.ofNat 64 (2 ^ 56 - 1)).toNat = _; simp
    scalar_tac
  have nc3 : ¬ y2.bv > Fl4Spec.maxDomainDuration := fun h => by have := hmx.1 h; omega
  have nc4 : ¬ (y2.bv = 0 ∧ y1.bv ≠ 0) := by rw [hy1']; simp
  have hok : ∀ (hc5 : ¬ (y0.val = σ.domainStartIndex ∧ y2.bv = 0)),
      (do
        let s1 ← sched.set_thread_state st s ct sched.TS_RESTART
        let s2 ← sched.set_dom_sched st s1 y0 y1 y2
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ res =>
        DomPost (L := L) th σ G (Fl4Spec.decodeDomainInvocation slbl (List.map UScalar.bv (y0 :: y1 :: y2 :: rest))
          excs) s res ⦄ := fun hc5 =>
    dom_conf_ok th hP s σ G hCR hFI ⟨hl, hent, hstart⟩ ct hcur htcb hact hkf hka hksO hactK _ y0 y1 y2 hy0 hy1 hy2
      (by rw [hmap, hspec, if_neg (by omega), if_neg (by omega), if_neg nc3, if_neg nc4, if_neg hc5]; rfl)
  have hk2 : obj.ks_get st s layout.ks.DOM_SCHED_START = ok (L.mem s (ksW kb 32#u64)) := by
    rw [ks_get_eq, show layout.ks.DOM_SCHED_START = 32#u64 by unfold layout.ks.DOM_SCHED_START; rfl]
  have hst : (y0 = L.mem s (ksW kb 32#u64)) ↔ y0.val = σ.domainStartIndex := by
    rw [hstart]; exact ⟨fun h => by rw [h], fun h => UScalar.eq_of_val_eq h⟩
  by_cases c4 : y2 = 0#u64
  · rw [if_pos c4]
    have hb : (y1 != 0#u64) = false := by rw [hy1']; rfl
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hk2, bind_ok]
    have hz : y2.bv = 0 := by rw [c4]; rfl
    by_cases c5 : y0 = L.mem s (ksW kb 32#u64)
    · rw [if_pos c5, if_pos c4]; simp only [error.invalid_arg, bind_ok]
      refine dom_err (e' := .invalidArgument 2) ?_ rfl
      rw [hmap, hspec, if_neg (by omega), if_neg (by omega), if_neg nc3, if_neg nc4, if_pos ⟨hst.1 c5, hz⟩]
    · rw [if_neg c5]; exact hok (fun h => c5 (hst.2 h.1))
  · rw [if_neg c4]; simp only [hk2, bind_ok]
    have hz : ¬ y2.bv = 0 := fun h => c4 (UScalar.eq_of_val_eq (by
      have := congrArg BitVec.toNat h; simpa using this))
    by_cases c5 : y0 = L.mem s (ksW kb 32#u64)
    · rw [if_pos c5, if_neg c4]; exact hok (fun h => hz h.2)
    · rw [if_neg c5]; exact hok (fun h => c5 (hst.2 h.1))

/-- **DomainSetSet.** -/
theorem dom_set_refines (hcfg : DomConfig) (th : TypedHeap) (hP : Placed th) (s : S) (σ : Fl4Spec.State Unit)
    (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (slbl : Fl4Spec.Data) (hg : Fl4Spec.genInvocationType slbl = .domainSetSet)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) :
    domain.decode st s fl4_abi.label.DomainSetSet length buf extra ⦃ res =>
      DomPost (L := L) th σ G (Fl4Spec.decodeDomainInvocation slbl (args.map UScalar.bv) excs) s res ⦄ := by
  set kb := L.ksb s with hkbdef
  unfold domain.decode
  rw [hct]; simp only [bind_ok, ↓reduceIte]
  by_cases h1 : length = 0#u64
  · rw [if_pos h1]; simp only [error.truncated, bind_ok]
    have : args = [] := List.eq_nil_of_length_eq_zero (by rw [← hlen, h1]; rfl)
    subst this
    exact dom_err (dec_set_nil hg _) trivial
  rw [if_neg h1]
  obtain ⟨y0, rest, rfl⟩ : ∃ y0 rest, args = y0 :: rest := by
    match args with
    | [] => exfalso; simp at hlen; exact h1 (UScalar.eq_of_val_eq (by rw [hlen]; rfl))
    | y0 :: rest => exact ⟨y0, rest, rfl⟩
  simp only [hargs 0#u64 y0 (by simp), bind_ok, nd_eq]
  have hmap : List.map UScalar.bv (y0 :: rest) = y0.bv :: rest.map UScalar.bv := rfl
  have hu0 : Fl4Spec.unat y0.bv = y0.val := rfl
  rw [hmap]
  by_cases c1 : y0 ≥ 1#u64
  · rw [if_pos c1]; simp only [error.invalid_arg, bind_ok]
    exact dom_err (e' := .invalidArgument 0) (dec_set_big hg _ _ (by rw [hu0, hcfg.numDomains]; scalar_tac) _) rfl
  rw [if_neg c1]
  have nc1 : ¬ Fl4Spec.unat y0.bv ≥ Fl4Spec.numDomains := by rw [hu0, hcfg.numDomains]; scalar_tac
  have hy0 : y0.val < 1 := by scalar_tac
  rw [hx0]; simp only [bind_ok, is_null_eq]
  rcases hex with ⟨rfl, rfl⟩ | ⟨hx0n, ps, rs, idxs, rest', hps, hls, hxe, rfl⟩
  · simp only [decide_true, ↓reduceIte, error.truncated, bind_ok]
    exact dom_err (dec_set_noex hg _ _ nc1) trivial
  simp only [hx0n, decide_false, Bool.false_eq_true, ↓reduceIte, slot_cap_eq, capAt_capV, bind_ok]
  have hAs : AbsSlot th (ps.bv, idxs) := ⟨ps, rfl, Or.inl (by simpa [hls] using hps)⟩
  have hcv : CapValid th (capV (L.mem s) x0) := hCR.2.1.abs hAs (by rw [← hxe]; exact capAt_capV _ _)
  generalize hcx : capV (L.mem s) x0 = c at hcv ⊢
  have hother : (∀ p, c ≠ .Thread p) →
      (ok ((core.result.Result.Err (error.Exc.Sys (error.SysError.InvalidArgument 1#u64))), s) :
        Result (core.result.Result Unit error.Exc × S)) ⦃ res =>
      DomPost (L := L) th σ G (Fl4Spec.decodeDomainInvocation slbl (y0.bv :: rest.map UScalar.bv)
        ((absCap c, (ps.bv, idxs)) :: rest')) s res ⦄ := by
    intro hc
    refine dom_err (dec_set_other hg _ _ nc1 _ (fun p e => ?_) _ _) rfl
    cases c <;> simp [absCap] at e
    exact hc _ rfl
  cases c with
  | Thread ptr =>
    simp only
    obtain ⟨s1, hs1, hS1, hkb1, σ1, hst1, hCR1, hFI1, hDR1, -, hstR⟩ :=
      dom_restart th hP s σ G hCR hFI hDR ct hcur htcb hact hkf hka hksO hactK
    rw [hs1]; simp only [bind_ok]
    refine WP.spec_bind (hSet s1 σ1 ptr y0 hs1 hst1 hcv hy0) ?_
    rintro s2 ⟨hS2, hkb2, hDS, y, hy, hK, hSR, hcdt, hio, hdl, hst, hss⟩
    rw [WP.spec_ok]
    have hR2 : StateRel th (L.mem s2) y.2 := (hSR _ hCR1.1).of_caps (fun x hx => hS2.capAt hx)
    obtain ⟨hCR2, hFI2⟩ := crel_step hCR1 hFI1 hS2 hK hR2 hcdt hio
    refine Or.inr ⟨rfl, .invokeDomainSet ptr.bv (Fl4Spec.ucast Fl4Spec.domainLen y0.bv),
      dec_set_thread hg _ _ nc1 _ _ _, σ1, by rw [hcur]; exact hst1, y, hy, hS1.trans hS2, hCR2, hFI2, hkb2.trans hkb1, ?_,
      fun hC A arI a => (hstR hC A arI a).trans arI (hss A arI a)⟩
    show DomRel (L.mem s2) (L.ksb s2) y.2
    rw [hkb2, hkb1]
    rw [hkb1] at hDS
    exact hDR1.of_same hDS hdl hst
  | _ => simp only [error.invalid_arg, bind_ok]; exact hother (by simp)

/-- The spec's domain label of an FL4 label. -/
def domLabelOf (lbl : U64) : Fl4Spec.GenInvocationLabels :=
  if lbl.val = 37 then .domainSetSet else if lbl.val = 38 then .domainScheduleConfigure
  else if lbl.val = 39 then .domainScheduleSetStart else .invalidInvocation

/-- **FL4's `domain::decode` refines l4v's domain invocations, every
label**: `decode_domain_invocation`, `set_thread_state Restart` and
`invoke_domain`, with the CSpace relation, `FinInv` and `DomRel` after them.
The scheduler steps are `DomSetHyp` and `DomResHyp`. -/
theorem domain_decode_refines (hcfg : DomConfig) (th : TypedHeap) (hP : Placed th) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) (hRes : DomResHyp (L := L) th s σ ct) :
    domain.decode st s lbl length buf extra ⦃ res =>
      DomPost (L := L) th σ G (Fl4Spec.decodeDomainInvocation slbl (args.map UScalar.bv) excs) s res ⦄ := by
  by_cases h37 : lbl.val = 37
  · have e : lbl = fl4_abi.label.DomainSetSet := UScalar.eq_of_val_eq (by rw [h37]; simp [fl4_abi.label.DomainSetSet])
    subst e
    exact dom_set_refines hcfg th hP s σ G hCR hFI hDR ct hct hcur htcb hact hkf hka hksO hactK slbl
      (by rw [hlbl]; simp [domLabelOf, h37]) length buf args hlen hargs extra x0 hx0 excs hex hSet
  by_cases h38 : lbl.val = 38
  · have e : lbl = fl4_abi.label.DomainScheduleConfigure :=
      UScalar.eq_of_val_eq (by rw [h38]; simp [fl4_abi.label.DomainScheduleConfigure])
    subst e
    exact dom_conf_refines hcfg th hP s σ G hCR hFI hDR ct hct hcur htcb hact hkf hka hksO hactK slbl
      (by rw [hlbl]; simp [domLabelOf, h38]) length buf args hlen hargs extra excs
  by_cases h39 : lbl.val = 39
  · have e : lbl = fl4_abi.label.DomainScheduleSetStart :=
      UScalar.eq_of_val_eq (by rw [h39]; simp [fl4_abi.label.DomainScheduleSetStart])
    subst e
    exact dom_start_refines th hP s σ G hCR hFI hDR ct hct hcur htcb hact hkf hka hksO hactK slbl
      (by rw [hlbl]; simp [domLabelOf, h39]) length buf args hlen hargs extra excs hRes
  have hg : Fl4Spec.genInvocationType slbl = .invalidInvocation := by rw [hlbl]; simp [domLabelOf, h37, h38, h39]
  unfold domain.decode
  have n1 : ¬ lbl = fl4_abi.label.DomainSetSet := by rw [u64_eq_iff]; simpa [fl4_abi.label.DomainSetSet] using h37
  have n2 : ¬ lbl = fl4_abi.label.DomainScheduleConfigure := by
    rw [u64_eq_iff]; simpa [fl4_abi.label.DomainScheduleConfigure] using h38
  have n3 : ¬ lbl = fl4_abi.label.DomainScheduleSetStart := by
    rw [u64_eq_iff]; simpa [fl4_abi.label.DomainScheduleSetStart] using h39
  rw [hct]; simp only [bind_ok, n1, n2, n3, ↓reduceIte, error.illegal]
  exact dom_err (dec_dom_other _ _ (by rw [hg]; decide) (by rw [hg]; decide) (by rw [hg]; decide)) trivial

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **The domain cap** of the dispatcher (`domain_decode_refines`). -/
theorem decode_invocation_domain (hcfg : DomConfig) (th : TypedHeap) (hP : Placed th) (s : S) (ar : A)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCR : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hDR : DomRel (L.mem s) (L.ksb s) σ)
    (ct : U64) (hct : sched.cur_thread st s = ok ct) (hcur : σ.curThread = ct.bv) (htcb : th ct = some .tcb)
    (hact : OutsideObjects th (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION))
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (hksO : ∀ o : U64, o.val < 256 → o.val % 8 = 0 → OutsideObjects th (ksW (L.ksb s) o))
    (hactK : ∀ o : U64, o.val < 256 → (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION).val ≠ (ksW (L.ksb s) o).val)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = domLabelOf lbl)
    (length buf : U64) (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraSRel th (L.mem s) x0 excs)
    (hSet : DomSetHyp (L := L) th s σ ct) (hRes : DomResHyp (L := L) th s σ ct)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    DecOK (L := L) arI s ar σ lbl length slot .Domain blk call don fp buf extra slbl (args.map UScalar.bv) ci sl
      excs buffer := by
  unfold DecOK syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (domain_decode_refines hcfg th hP s σ G hCR hFI hDR ct hct hcur htcb hact hkf hka hksO hactK
      lbl slbl hlbl length buf args hlen hargs extra x0 hx0 excs hex hSet hRes) ?_
    rintro ⟨r0, s'⟩ hq
    simp only [uncurry_apply_pair]
    rw [WP.spec_ok]
    apply top_of_lift (f := Fl4Spec.Fl4Invocation.invokeDomain)
    rcases hq with ⟨e, he, hs', e', h1, h2⟩ | ⟨he, inv, hrun, σ1, hst, y, hy, -, hCR', hFI', -, -, -⟩
    · exact Or.inl ⟨e, he, hs', e', h1, Or.inl h2⟩
    · have hm : ((.ok [], y.2) : Except Unit (List Fl4Spec.Data) × Fl4Spec.State Unit) ∈
          ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain inv)).run σ1).1 := by
        show _ ∈ ((Fl4Spec.NonDetE.liftE (do Fl4Spec.invokeDomain (Z := Unit) inv; return ([] : List Fl4Spec.Data))).run
          σ1).1
        exact mem_liftE (x := ([], y.2)) (mem_bind_nd hy rfl)
      exact Or.inr ⟨inv, hrun, σ1, hst, (.ok [], y.2), hm, th, G, Or.inl ⟨he, [], rfl⟩, hP, hCR', hFI'⟩
  · exact top_invalid rfl

end

end

end Fl4Proofs.P3
