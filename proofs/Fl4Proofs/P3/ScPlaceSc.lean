/-
P3 (DESIGN.md §9), scheduling contexts: **the SchedContext and SchedControl
invocations keep the joint placement invariant `JPlaced`**.

* `AddrApart`, `UFoot.not_at`: a 32-byte block apart from the TCBs' low
  256 bytes, the core's node, the notifications, the SCs and the replies
  holds no `UFoot` word (`UFoot.not_slot` for any address).
* `IrqApart`: the IRQ handler slots are such blocks; `JPlaced.irqApart` and
  `JPlaced.slotsApart` derive it and the `SlotsApart` placement hypothesis
  from `JPlaced`.
* `JPlaced.ufoot`: a `UFoot` step with the spec's objects kept as `SOK`
  keeps `JPlaced`.
* `TopPostFJ`: `TopPostF` with a predicate at the post states;
  `decode_invocation_sched_contextJ`, `decode_invocation_sched_controlJ`:
  the two caps' `DecOKF` with `JPlaced` after.
-/
import Fl4Proofs.P3.ScPlace
import Fl4Proofs.P3.ScTopF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]

/-- The block `[a, a + 32)` apart from what `UFoot` covers. -/
def AddrApart (T N C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) (a : U64) : Prop :=
  a.val + 32 ≤ 2 ^ 64 ∧
    (∀ t ∈ T, a.val + 32 ≤ t.val + 256 ∨ t.val + 4096 ≤ a.val) ∧
    (a.val + 32 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ a.val) ∧
    (∀ n ∈ N, a.val + 32 ≤ n.val ∨ n.val + 40 ≤ a.val) ∧
    (∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → a.val + 32 ≤ sc.val ∨ sc.val + 2 ^ (n + Fl4Spec.minSchedContextBits) ≤ a.val) ∧
    (∀ r ∈ R, a.val + 32 ≤ r.val ∨ r.val + 32 ≤ a.val)

/-- A `UFoot` word is in no apart block (`UFoot.not_slot`'s proof). -/
theorem UFoot.not_at {N T C R : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) {a k : U64}
    (hA : AddrApart (st := st) T N C R c s σ a) (hk : Off k)
    (hb : UFoot st T N C R c s σ (wordOf a k)) : False := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hT := hc.tcbs
  have hkl := hk.lt
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := hA
  have hv : (wordOf a k).val = a.val + k.val := wordOf_val (by omega)
  rcases hb with (((⟨y, hy, K, hK, e⟩ | ⟨b1, b2⟩) | ⟨n, hn, b1, b2⟩ | ⟨sc, hsc, x, n, hkx, ⟨b1, b2⟩, -⟩) |
      ⟨y, hy, e⟩) | (⟨r, hr, e⟩ | ⟨q, hq, e⟩)
  · have := congrArg UScalar.val e
    rw [hv, tfield_val (hT y hy) hK.2.1] at this
    have := g1 y hy; have := hK.1; have := hK.2.1; omega
  · rw [hv] at b1 b2; omega
  · have := g3 n hn; rw [hv] at b1 b2; omega
  · have := g4 sc hsc x n hkx; rw [hv] at b1 b2; omega
  · have := congrArg UScalar.val e
    rw [hv, yieldA_val hT hy] at this
    have := g1 y hy; omega
  · have := congrArg UScalar.val e
    rw [hv, rNextA_val (hRP.align r hr)] at this
    have := g5 r hr; omega
  · obtain ⟨-, hvq, hsz⟩ := sc_reply_word hS hq
    obtain ⟨xq, nq, hkq, -⟩ := hs.scs q hq
    have := congrArg UScalar.val e
    rw [hv, hvq] at this
    have := g4 q hq xq nq hkq; have := hsz xq nq hkq; omega

/-- The IRQ handler slots are apart blocks. -/
def IrqApart (T N C R : Set U64) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ i : U64, i.val < 128 → AddrApart (st := st) T N C R c s σ (nodeA (L.ksb s) i)

/-- **A `UFoot` step keeps the IRQ handler slots' caps.** -/
theorem irq_of_ufoot {N T C R : Set U64} {c : U64} {s s' : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) (hA : IrqApart (st := st) T N C R c s σ)
    (hw : WritesIn st s s' (UFoot st T N C R c s σ)) :
    ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  intro i hi
  have hAi := hA i hi
  obtain ⟨Q, R', hc, -⟩ := hS.lists
  have hNa := hc.node.align
  have hNf := hc.node.fits
  simp only [LawfulStore.nodeBase] at hNa hNf
  have hf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by omega
  have hnv := nodeA_val hf hi
  have w : ∀ k, Off k → L.mem s' (wordOf (nodeA (L.ksb s) i) k) = L.mem s (wordOf (nodeA (L.ksb s) i) k) := by
    intro k hk
    have hkl := hk.lt
    refine hw.mem_eq ?_ fun hb => UFoot.not_at hS hRP hAi hk hb
    unfold Aligned
    rw [wordOf_val (by rw [hnv]; omega)]
    rw [hnv]; omega
  unfold capV
  have h0 := w _ off0
  rw [wordOf_zero] at h0
  rw [h0, w _ off8]

/-- **`IrqApart` from `JPlaced`**: `H`'s objects are outside the kernel-global
area, where the IRQ handler slots are. -/
theorem JPlaced.irqApart {th : TypedHeap} {H : Heap} {Tr C0 : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C0 s σ) {T N C R : Set U64} {c : U64}
    (hT : ∀ t ∈ T, H t = some .tcb) (hN : ∀ n ∈ N, H n = some .ntfn) (hC : ∀ q ∈ C, q ≠ 0#u64)
    (hR : ∀ r ∈ R, H r = some .reply) (hf : (L.ksb s).val + 13568 ≤ 2 ^ 64) :
    IrqApart (st := st) T N C R c s σ := by
  intro i hi
  have hv := nodeA_val hf hi
  refine ⟨by rw [hv]; omega, fun t ht => ?_, ?_, fun n hn => ?_, fun q hq x n hk => ?_, fun r hr => ?_⟩
  · have := h.ks t _ (hT t ht); simp only [HKind.bits] at this; rw [hv]; omega
  · rw [hv]; left; simp only [LawfulStore.nodeBase]; omega
  · have := h.ks n _ (hN n hn); simp only [HKind.bits] at this; rw [hv]; omega
  · have := h.ks q _ (h.sc q x n (hC q hq) hk).2; simp only [HKind.bits] at this; rw [hv]; have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_add_right n Fl4Spec.minSchedContextBits); omega
  · have := h.ks r _ (hR r hr); simp only [HKind.bits] at this; rw [hv]; omega

/-- **`SlotsApart` from `JPlaced`**: the slots lie in CNodes and in the TCBs'
first 192 bytes; the objects of `H` are disjoint, and the core's node is
outside the CNodes (P1's `Ω`) and the TCBs. -/
theorem JPlaced.slotsApart {th : TypedHeap} {H : Heap} {Tr C0 : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C0 s σ) {T N C R Cs : Set U64} {c : U64}
    (hT : T = Heap.tcbs H) (hN : ∀ n ∈ N, H n = some .ntfn) (hC : ∀ q ∈ C, q ≠ 0#u64)
    (hR : ∀ r ∈ R, H r = some .reply) (hc : c ∈ Cs) (hNd : NodePlaced st T s c)
    (hΩ : ∀ a ∈ Heap.omega H, OutsideObjs st T Cs s a) :
    SlotsApart (st := st) th T N C R c s σ := by
  intro a ha
  obtain ⟨q, kq, hq, e1, e2, e3, hkq⟩ := h.slot_in ha
  have disj : ∀ p k, H p = some k → p ≠ q → p.val + 2 ^ k.bits ≤ q.val ∨ q.val + 2 ^ kq.bits ≤ p.val :=
    fun p k hp hpq => h.heap.disj p k q kq hp hq hpq
  have ne_of : ∀ p k, H p = some k → (k ≠ .tcb ∧ ∀ z, k ≠ .other z) → p ≠ q := by
    rintro p k hp ⟨h1, h2⟩ rfl; rw [hp] at hq; cases hq
    rcases hkq with e | ⟨z, e⟩
    · exact h1 e
    · exact h2 z e
  refine ⟨fun t ht => ?_, ?_, fun n hn => ?_, fun sc hsc x n hk => ?_, fun r hr => ?_⟩
  · rw [hT] at ht
    by_cases e : t = q
    · subst e; rw [ht] at hq; cases hq; have := e3 rfl; omega
    · have := disj t _ ht e; rw [show (2 : ℕ) ^ HKind.tcb.bits = 4096 from rfl] at this; omega
  · -- the node
    rcases hkq with rfl | ⟨z, rfl⟩
    · have hqT : q ∈ T := by rw [hT]; exact hq
      have := hNd.disj q hqT; simp only [HKind.bits] at e2; omega
    · have hal : a.val % 32 = 0 := by
        obtain ⟨q', i, hqi, rfl⟩ := ha
        exact hqi.aligned h.pl
      have hbase := hNd.align
      have hfit := hNd.fits
      have hw : ∀ w : U64, w.val % 8 = 0 → q.val ≤ w.val → w.val < a.val + 32 →
          w.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ w.val := fun w h8 hq1 hq2 =>
        (hΩ w ⟨h8, q, _, hq, Or.inr (Or.inr (Or.inl ⟨z, rfl⟩)), hq1, by omega⟩).2.2 c hc
      by_cases hab : L.nodeBase s c ≤ a.val
      · rcases hw a (by omega) e1 (by omega) with e | e
        · omega
        · right; omega
      · left
        by_contra hlt'
        have hlt : L.nodeBase s c < 2 ^ 64 := by omega
        obtain ⟨w, hwv⟩ : ∃ w : U64, w.val = L.nodeBase s c :=
          ⟨⟨BitVec.ofNat 64 (L.nodeBase s c)⟩, by
            show (BitVec.ofNat 64 (L.nodeBase s c)).toNat = _; simp; omega⟩
        rcases hw w (by rw [hwv]; exact hbase) (by rw [hwv]; omega) (by rw [hwv]; omega) with e | e <;>
          rw [hwv] at e <;> omega
  · have hp := hN n hn
    have := disj n _ hp (ne_of n _ hp ⟨fun e => (by cases e), fun _ e => (by cases e)⟩)
    rw [show (2 : ℕ) ^ HKind.ntfn.bits = 64 from rfl] at this; omega
  · have hp := (h.sc sc x n (hC sc hsc) hk).2
    have := disj sc _ hp (ne_of sc _ hp ⟨fun e => (by cases e), fun _ e => (by cases e)⟩)
    rw [show (2 : ℕ) ^ (HKind.sc (n + Fl4Spec.minSchedContextBits)).bits = 2 ^ (n + Fl4Spec.minSchedContextBits) from rfl] at this; have := Nat.pow_le_pow_right (show 0 < 2 by decide) (Nat.le_add_right n Fl4Spec.minSchedContextBits); omega
  · have hp := hR r hr
    have := disj r _ hp (ne_of r _ hp ⟨fun e => (by cases e), fun _ e => (by cases e)⟩)
    rw [show (2 : ℕ) ^ HKind.reply.bits = 32 from rfl] at this; omega

/-- The spec's SC objects after a `SOK` step were SCs of the same size. -/
theorem sok_sc {f : Bool × Bool} {σ σ' : Fl4Spec.State Unit} (h : SOK f σ σ') :
    ∀ (c : U64) y n, c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n) →
      ∃ y0, σ.kheap c.bv = some (.schedContext y0 n) := by
  intro c y n _ hk
  have := h.kh c.bv
  rw [hk] at this
  revert this
  cases hk0 : σ.kheap c.bv with
  | none => simp [ORel]
  | some o =>
    cases o with
    | schedContext x m =>
      simp only [ORel, PK]
      rintro ⟨e, -, -⟩
      exact ⟨x, by rw [e]⟩
    | _ => simp [ORel, PK]

/-- **A `UFoot` step with the spec's objects kept (`SOK`) keeps `JPlaced`.** -/
theorem JPlaced.ufoot {th : TypedHeap} {H : Heap} {Tr C0 : Set U64} {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : JPlaced (L := L) th H Tr C0 s σ) {N T C R : Set U64} {c : U64} {f : Bool × Bool}
    (hS : SchedRel st N T C c s σ) (hRP : RPlaced st N T C R c s σ) (hIA : IrqApart (st := st) T N C R c s σ)
    (hSS : SlotsSame th (L.mem s) (L.mem s')) (hw : WritesIn st s s' (UFoot st T N C R c s σ))
    (hsok : SOK f σ σ') : JPlaced (L := L) th H Tr C0 s' σ' :=
  h.same hSS (sok_sc hsok) hw.1 (irq_of_ufoot hS hRP hIA hw)

/-- `TopPostF` with `J` at the post states. -/
def TopPostFJ (J : S → Fl4Spec.State Unit → Prop) (σ : Fl4Spec.State Unit) (blk call don : Bool)
    (m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation) (s : S) (res : core.result.Result Unit error.Exc × S × A) :
    Prop :=
  (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
  (∃ inv, DecOut m σ inv ∧ ∃ σ1,
    Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
    ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don inv).run σ1).1, ∃ th' G',
      ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
      Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
      Vs.FrameInv (L.mem res.2.1) G' ∧ J res.2.1 y.2)

theorem TopPostFJ.toF {J : S → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostFJ (L := L) J σ blk call don m s res) : TopPostF (L := L) σ blk call don m s res := by
  rcases h with h | ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨inv, h1, σ1, h2, y, hy, th', G', h3, h4, h5, h6, h7⟩

/-- `J` holds after: in the error branch the state is unchanged. -/
theorem TopPostFJ.post {J : S → Fl4Spec.State Unit → Prop} {σ : Fl4Spec.State Unit} {blk call don : Bool}
    {m : Fl4Spec.SEMonad Unit Fl4Spec.Fl4Invocation} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : TopPostFJ (L := L) J σ blk call don m s res) (hJ : J s σ) : ∃ σ', J res.2.1 σ' := by
  rcases h with ⟨-, -, e, -⟩ | ⟨-, -, -, -, y, -, -, -, -, -, -, -, -, h⟩
  · exact ⟨σ, by rw [e]; exact hJ⟩
  · exact ⟨y.2, h⟩

theorem top_of_liftFJ {J : S → Fl4Spec.State Unit → Prop} {α : Type} {f : α → Fl4Spec.Fl4Invocation}
    {m : Fl4Spec.SEMonad Unit α}
    {σ : Fl4Spec.State Unit} {blk call don : Bool} {s : S} {res : core.result.Result Unit error.Exc × S × A}
    (h : (∃ e, res.1 = .Err e ∧ res.2.1 = s ∧ ∃ e', m.run σ = ({(.error e', σ)}, False) ∧ ErrRel e e') ∨
      (∃ inv, m.run σ = ({(.ok inv, σ)}, False) ∧ ∃ σ1,
        Fl4Spec.setThreadState (Z := Unit) σ.curThread .restart σ = ({((), σ1)}, False) ∧
        ∃ y ∈ ((Fl4Spec.fl4PerformInvocation (Z := Unit) blk call don (f inv)).run σ1).1, ∃ th' G',
          ((res.1 = .Ok () ∧ ∃ rr, y.1 = .ok rr) ∨ (res.1 = .Err .Preempted ∧ y.1 = .error ())) ∧
          Placed th' ∧ CRel th' (L.mem res.2.1) y.2 G' ∧ FinInv th' (L.mem res.2.1) y.2 G' ∧
          Vs.FrameInv (L.mem res.2.1) G' ∧ J res.2.1 y.2)) :
    TopPostFJ (L := L) J σ blk call don (Fl4Spec.NonDetE.liftME f m) s res := by
  rcases h with ⟨e, h1, h2, e', hr, he⟩ | ⟨inv, hr, rest⟩
  · exact Or.inl ⟨e, h1, h2, e', run_liftME_err hr, he⟩
  · exact Or.inr ⟨f inv, DecOut.of_eq (run_liftME_ok hr), rest⟩

/-- **The SchedContext cap** with the frame invariant and `JPlaced` after. -/
theorem decode_invocation_sched_contextJ {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : Vs.FrameInv (L.mem s) G)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hY : YieldRel T C (L.mem s) σ) (hAI : ActIdle σ) (hM : McpRel T (L.mem s) σ) (hC0 : ∀ q ∈ C, q ≠ 0#u64)
    {Lst : U64 → List U64} (hCR : CallRel (L.mem s) R C σ Lst) (hRP : RPlaced st N T C R c s σ)
    (hRF : RFree (L.mem s) R C σ Lst) (hA : SlotsApart (st := st) th T N C R c s σ)
    {H : Heap} {Tr C0 : Set U64} (hJ : JPlaced (L := L) th H Tr C0 s σ) (hIA : IrqApart (st := st) T N C R c s σ)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlbl : Fl4Spec.genInvocationType slbl = scLabelOf lbl)
    {sc : U64} (sb : U64) (hsc : sc ∈ C) (hpi : sc.bv ≠ Fl4Spec.idleScPtr)
    (hback : L.mem s (scW sc 24#u64) ≠ 0#u64 →
      L.mem s (scW sc 24#u64) ∈ T ∧ L.mem s (scA (L.mem s (scW sc 24#u64))) = sc ∧
      (L.mem s (scW sc 24#u64)).bv ≠ σ.idleThread)
    (hbn : ∀ y n, σ.kheap sc.bv = some (.schedContext y n) → ∀ m : U64, y.scNtfn = some m.bv → m ∈ N)
    {ct : U64} (hct : sched.cur_thread st s = ok ct) (hcs : Fl4Spec.schedulable ct.bv σ = true)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hcapT : ∀ p, capAt (L.mem s) x0 = ok (.Thread p) → p ∈ T)
    (hcapN : ∀ p b w r, capAt (L.mem s) x0 = ok (.Notification p b w r) → p ∈ N ∧ p ≠ 0#u64)
    (hmb : sporadic.min_budget ar a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, ar.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) (hmsg : MsgOK st N T C c)
    (length slot buf : U64) (blk call don fp : Bool) (args : List Fl4Spec.Data) (ci : Fl4Spec.CapRef)
    (sl : Fl4Spec.CslotPtr) (buffer : Option Fl4Spec.ObjRef) :
    syscall.decode_invocation st ar s a lbl length slot (.SchedContext sc sb) blk call don fp buf extra ⦃ res =>
      TopPostFJ (L := L) (JPlaced (L := L) th H Tr C0) σ blk call don
        (specDec fp slbl args ci sl (.SchedContext sc sb) excaps buffer) s res ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (sc_decode_refines hT th s a σ hS hR hN hI hY hAI hM hC0 hCR hRP hRF lbl slbl hlbl hsc hpi
      hback hbn hct hcs call extra x0 hx0 _ hex hcapT hcapN hmb hmax htu hmsg) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_liftFJ (f := Fl4Spec.Fl4Invocation.invokeSchedContext)
    rcases hq with ⟨e, e', he, hrun, herr⟩ | ⟨inv, hrun, hr1, σ0, data, σ1, σ2, he0, he1, -, hall⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, e', hrun, herr⟩
    · have hSS := slotsSame_of_ufoot hP hS hRP hA hall.2.2.2.2.2
      refine Or.inr ⟨inv, hrun, σ0, by rw [hcur]; exact he0, (.ok data, σ1), ?_, th, G, Or.inl ⟨hr1, data, rfl⟩,
        hP, ?_⟩
      · exact mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedContext (Z := Unit) inv) (s := σ0) (x := (data, σ1))
          (by rw [he1]; exact Set.mem_singleton _)
      · have hsok : SOK (false, false) σ σ1 := ((pres_setThreadState _ _ _).of_eq he0).trans
          (((pres_invokeSchedContext inv).of_eq he1).weaken (fun h => by cases h) (fun h => by cases h))
        obtain ⟨h1, h2⟩ := crel_of_sok hCRel hFI hSS hsok
        exact ⟨h1, h2, FrameInv.of_same hCRel.2.2.1 hFR hSS,
          hJ.ufoot hS hRP hIA hSS hall.2.2.2.2.2 hsok⟩
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩

/-- **The SchedControl cap** with the frame invariant and `JPlaced` after. -/
theorem decode_invocation_sched_controlJ {N T C R : Set U64} {c : U64} (hT : TimeAgree ar) (th : TypedHeap)
    (hP : Placed th) (s : S) (a : A) (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hCRel : CRel th (L.mem s) σ G) (hFI : FinInv th (L.mem s) σ G) (hFR : Vs.FrameInv (L.mem s) G)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hC : CurInv σ) (hO : OffOK σ) (hRP : RPlaced st N T C R c s σ) (hA : SlotsApart (st := st) th T N C R c s σ)
    {H : Heap} {Tr C0 : Set U64} (hJ : JPlaced (L := L) th H Tr C0 s σ) (hIA : IrqApart (st := st) T N C R c s σ)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.genInvocationType slbl = .schedControlConfigureFlags ↔
      lbl = fl4_abi.label.SchedControlConfigureFlags)
    (cpu length buf ct : U64) (hcpu : cpu = c) (hct : sched.cur_thread st s = ok ct) (args : List U64)
    (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (x0 : U64) (hx0 : Aeneas.Std.Array.index_usize extra 0#usize = ok x0)
    (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (hex : ExtraRel th (L.mem s) x0 (excaps.map Prod.fst))
    (hsb : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → sb.val < 64)
    (hsc : ∀ p sb, capAt (L.mem s) x0 = ok (.SchedContext p sb) → p ∈ C ∧ p ≠ 0#u64 ∧
      ∃ x, σ.kheap p.bv = some (.schedContext x (sb.val - Fl4Spec.minSchedContextBits)) ∧
        ∀ t : U64, x.scTcb = some t.bv →
          t ∈ T ∧ ∃ xt, σ.kheap t.bv = some (.tcb xt) ∧ xt.tcbSchedContext = some p.bv)
    {xc : Fl4Spec.Tcb} (hkc : σ.kheap ct.bv = some (.tcb xc)) (hrun : Fl4Spec.runnable xc.tcbState = true)
    (slot : U64) (blk call don fp : Bool) (ci : Fl4Spec.CapRef) (sl : Fl4Spec.CslotPtr)
    (buffer : Option Fl4Spec.ObjRef) :
    syscall.decode_invocation st ar s a lbl length slot (.SchedControl cpu) blk call don fp buf extra ⦃ res =>
      TopPostFJ (L := L) (JPlaced (L := L) th H Tr C0) σ blk call don
        (specDec fp slbl (args.map UScalar.bv) ci sl (.SchedControl cpu) excaps buffer) s res ⦄ := by
  obtain ⟨Q, R', hc, hs⟩ := hS.lists
  have hct' : ct = nodeW st s c layout.node.CUR_THREAD := by
    have h := sched.cur_thread.spec' (L := L) s
    rw [hct, WP.spec_ok, hc.cur] at h; exact h
  have hcur : σ.curThread = ct.bv := by rw [hs.curThread, hct']
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases fp
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_mono (decode_configure_refines hT th s a σ hS hR hN hI hC hO lbl slbl hlbl cpu length buf ct
      hcpu hct args hlen hargs extra x0 hx0 _ hex hsb hsc hkc hrun) ?_
    rintro ⟨r0, s', a'⟩ hq
    apply top_of_liftFJ (f := Fl4Spec.Fl4Invocation.invokeSchedControl)
    rcases hq with ⟨e, e', he, hrun', herr⟩ | ⟨inv, hrun', σ1, σ', he1, he2, hr1, -, -, -, -, hw⟩
    · cases he
      exact Or.inl ⟨e, rfl, rfl, e', hrun', herr⟩
    · have hwU : WritesIn st s s' (UFoot st T N C R c s σ) := hw.mono fun b hb => Or.inl (Or.inl hb)
      have hSS := slotsSame_of_ufoot hP hS hRP hA hwU
      refine Or.inr ⟨inv, hrun', σ1, by rw [hcur]; exact he1, (.ok [], σ'), ?_, th, G, Or.inl ⟨hr1, [], rfl⟩,
        hP, ?_⟩
      · exact mem_bindE_ok (mem_liftE (ε := Unit) (m := Fl4Spec.invokeSchedControlConfigureFlags (Z := Unit) inv)
          (s := σ1) (x := ((), σ')) (by rw [he2]; exact Set.mem_singleton _)) (Set.mem_singleton _)
      · have hsok : SOK (false, false) σ σ' := ((pres_setThreadState _ _ _).of_eq he1).trans
          ((pres_invokeSchedControlConfigureFlags _ inv).of_eq he2)
        obtain ⟨h1, h2⟩ := crel_of_sok hCRel hFI hSS hsok
        exact ⟨h1, h2, FrameInv.of_same hCRel.2.2.1 hFR hSS, hJ.ufoot hS hRP hIA hSS hwU hsok⟩
  · simp only [↓reduceIte, WP.spec_ok]
    exact Or.inl ⟨_, rfl, rfl, _, rfl, Or.inr ⟨0#u64, rfl, rfl⟩⟩


end

end

end Fl4Proofs.P3.Sched
