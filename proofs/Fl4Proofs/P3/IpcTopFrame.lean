/-
P3 (DESIGN.md §9), IPC: **the CSpace relation across the IPC operations**,
from a frame. The IPC theorems (IpcEp*, IpcNtfn*) prove `IpcRel ∧ SR` after
each operation for any `SR` with `IpcSchedHyps`; their posts say nothing of
the CSpace relation, so `RelTopM` reaches the syscall handlers by being part
of `SR`:

* `IWords N T E R B`: the words of the IPC objects (`OObj`'s IPC
  disjuncts: the TCBs past their slots, the endpoints, replies,
  notifications and the mapped IPC-buffer words); `NWrite` and `EWrite`
  (the words the notification and endpoint code write) are in it
  (`NWrite.iwords`, `EWrite.iwords`).
* `IpcApart th N T E R B kb`: every such word is in no slot of the typed
  heap and not a word of the domain schedule; `IpcApart.of_top` from
  `TopPlaced` (whose `disj` keeps `OObj` apart from the slots) and the
  objects' distance from the kernel-global block.
* `RelTopI`: `RelTopM` with `IpcApart` for its typed heap; `RelTopI.frame`:
  it holds across FL4 writes in `IWords` and a spec step keeping the caps
  (`CKeep`) and the domain schedule. `NtfnStep` and `EpStep` are such steps
  (`NtfnStep.ckeep`, `EpStep.ckeep`): they change only notifications,
  endpoints, replies and the state and user context of TCBs.
* `IpcSchedHyps.withTop`: `IpcSchedHyps` for `RelTopI ∧ SR` from
  `IpcSchedHyps` for `SR` (its stabilities and `block` lifted by the frame)
  and the three scheduler-side fields for `RelTopI ∧ SR`
  (`IpcTopTails`: `schedule_tcb`, the wake tail and `cancel_ipc`, which
  write scheduler words); `EpBufHyps` and `EpBufMapHyps` lift directly.

The cap transfer (`transfer_caps` with a grant and extra caps) is outside
the IPC theorems (their `hcaps`), so it is not covered here.
-/
import Fl4Proofs.P3.IpcSendTop
import Fl4Proofs.P3.IpcEpIpc
import Fl4Proofs.P3.IpcEpBlock
import Fl4Proofs.P3.IpcNtfnWake
import Fl4Proofs.P3.IpcNtfnRecv
import Fl4Proofs.P3.IpcNtfnBlock
import Fl4Proofs.P3.IpcNtfnSend
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-! ## The words -/

/-- **The words of the IPC objects**: the TCBs past their slots, the
endpoints, replies, notifications, the mapped IPC-buffer words. -/
def IWords (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (a : U64) : Prop :=
  (∃ t ∈ T, t.val + 256 ≤ a.val ∧ a.val < t.val + 4096) ∨
  (∃ e ∈ E, e.val ≤ a.val ∧ a.val < e.val + 16) ∨
  (∃ r ∈ R, r.val ≤ a.val ∧ a.val < r.val + 32) ∨
  (∃ n ∈ N, n.val ≤ a.val ∧ a.val < n.val + 40) ∨
  (∃ wp ∈ B, wp.1.val ≤ a.val ∧ a.val < wp.1.val + 8)

/-- The notification code writes IPC words. -/
theorem NWrite.iwords (hT : TcbPlaced T) {a : U64} (h : NWrite N T a) : IWords N T E R B a := by
  rcases h with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, h2⟩)))
  · have hta := hT t ht
    have hv : a.val = (tStA t).val ∨ a.val = (tBlockA t).val ∨ a.val = (badgeRegA t).val ∨
        a.val = (nextA .Ep t).val ∨ a.val = (prevA .Ep t).val := by
      rcases h with h | h | h | h | h <;> simp [h]
    rw [val_st hta, val_blk hta, val_next hta, val_prev hta, badgeRegA_eq_regA,
      regA_val hta (regIdx_lt _)] at hv
    have := regIdx_lt Fl4Spec.badge_register
    exact Or.inl ⟨t, ht, by omega, by omega⟩

/-- The endpoint code writes IPC words. -/
theorem EWrite.iwords {a : U64} (h : EWrite T E R B a) : IWords N T E R B a := by
  rcases h with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hw, rfl⟩
  · exact Or.inr (Or.inl ⟨e, he, by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨r, hr, by omega, by omega⟩))
  · have := h.tf.range; exact Or.inl ⟨t, ht, by omega, by omega⟩
  · unfold TL at h; exact Or.inl ⟨t, ht, by omega, by omega⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, le_refl _, by omega⟩)))

/-! ## The placement -/

/-- **The IPC words apart from the CSpace relation**: in no slot of the
typed heap, and not a word of the domain schedule (the first 256 bytes of
the kernel-global block at `kb`). -/
structure IpcApart (th : TypedHeap) (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (kb c : U64) : Prop where
  slot : ∀ a, IWords N T E R B a → ∀ x, IsSlot th x → ¬ (x.val ≤ a.val ∧ a.val < x.val + 32)
  /-- Core `c`'s node (whose action word `schedule_tcb` writes) holds no slot. -/
  node : ∀ a : U64, kb.val + 13568 + c.val * 4288 ≤ a.val → a.val < kb.val + 13568 + c.val * 4288 + 4288 →
    ∀ x, IsSlot th x → ¬ (x.val ≤ a.val ∧ a.val < x.val + 32)
  dom : ∀ a, IWords N T E R B a → a.val < kb.val ∨ kb.val + 256 ≤ a.val
  /-- The kernel-global block holds no slot. -/
  ks : ∀ a : U64, kb.val ≤ a.val → a.val < kb.val + 13568 → ∀ x, IsSlot th x → ¬ (x.val ≤ a.val ∧ a.val < x.val + 32)
  kfit : kb.val + 13568 ≤ 2 ^ 64
  kal : kb.val % 8 = 0

/-- **`IpcApart` from `TopPlaced`** and the IPC objects' distance from the
kernel-global block (for the TCBs, `SchedRel`'s `ksOut`; for the buffer
words, `BufPlaced.dom`). -/
theorem IpcApart.of_top {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hP : Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ)
    (hkT : ∀ t ∈ T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ t.val)
    (hkE : ∀ e ∈ E, e.val + 16 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ e.val)
    (hkR : ∀ r ∈ R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ r.val)
    (hkN : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ n.val)
    (hkB : ∀ wp ∈ B, wp.1.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ wp.1.val) :
    IpcApart th N T E R B (L.ksb s) c := by
  refine ⟨fun a ha x hx ⟨h1, h2⟩ => ?_, fun a h1 h2 x hx ⟨h3, h4⟩ =>
    hP.disj a (Or.inl ⟨h1, h2⟩) (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h3 h4), fun a ha => ?_,
    fun a h1 h2 x hx ⟨h3, h4⟩ =>
    hP.disj a (Or.inr (Or.inl ⟨h1, h2⟩)) (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h3 h4),
    by have := hP.vs.ksb_fit; omega, hP.vs.ksb_al⟩
  · refine hP.disj a ?_ (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h1 h2)
    rcases ha with h | h | h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · obtain ⟨n, hn, h1, h2⟩ := h; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  · rcases ha with ⟨t, ht, h1, h2⟩ | ⟨e, he, h1, h2⟩ | ⟨r, hr, h1, h2⟩ | ⟨n, hn, h1, h2⟩ | ⟨wp, hw, h1, h2⟩
    · have := hkT t ht; omega
    · have := hkE e he; omega
    · have := hkR r hr; omega
    · have := hkN n hn; omega
    · have := hkB wp hw; omega

/-- **The SC objects hold no slot.** -/
def ScApart (th : TypedHeap) (C : Set U64) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, Sched.ScObj sc n a →
    ∀ y, IsSlot th y → ¬ (y.val ≤ a.val ∧ a.val < y.val + 32)

theorem ScApart.of_top {th : TypedHeap} {P L4 L3 L2 L1 : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hP : Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ) : ScApart th C σ :=
  fun sc hsc x n hk a ha y hy ⟨h1, h2⟩ =>
    hP.disj a (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hk, ha⟩)))))))
      (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hy h1 h2)

theorem ScApart.mono {th : TypedHeap} {σ σ' : Fl4Spec.State Unit} (h : ScApart th C σ)
    (hz : Sched.SzKeep σ σ') : ScApart th C σ' := fun sc hsc x n hk a ha y hy => by
  obtain ⟨x0, h0⟩ := hz _ x n hk
  exact h sc hsc x0 n h0 a ha y hy

/-! ## The relation and its frame -/

/-- **The body of `RelTopI`** for a typed heap and a ghost tree. -/
def RelTopB (th : TypedHeap) (G : MdbGhost) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  Placed th ∧ CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ DomRel (L.mem s) (L.ksb s) σ ∧
    MdbOKV (L.ksb s) (L.mem s) G ∧ IpcApart th N T E R B (L.ksb s) c ∧ ScApart th C σ

/-- The words of core `c`'s node. -/
def NodeW (kb c a : U64) : Prop :=
  kb.val + 13568 + c.val * 4288 ≤ a.val ∧ a.val < kb.val + 13568 + c.val * 4288 + 4288

/-! ## The VSpace and kernel-state parts -/

/-- **The VSpace and kernel-state relations** at the typed heap `th`, for
some VSpace sets (the parts of VSpace's `FinX`/`TopSR` the IPC code does not
change), with the IPC objects and SCs apart from the kernel-global block. -/
structure VsP (th : TypedHeap) (cr : Fl4Spec.Cr3) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop where
  ex : ∃ P L4 L3 L2 L1, Vs.VsRel P (L.mem s) (L.ksb s) σ ∧ Vs.PtRel L4 L3 L2 L1 (L.mem s) σ ∧
    Vs.PoolsIn P L4 (L.mem s) ∧ Vs.CurOK st th s σ ∧ Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ
  irq : IrqRel (L.mem s) (L.ksb s) σ
  io : IoRel (L.mem s) (L.ksb s) σ
  kr : Vs.KRootRel (L.mem s) (L.ksb s) σ
  ksT : ∀ t ∈ T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ t.val
  ksE : ∀ e ∈ E, e.val + 16 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ e.val
  ksR : ∀ r ∈ R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ r.val
  ksN : ∀ n ∈ N, n.val + 64 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ n.val
  ksB : ∀ wp ∈ B, wp.1.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ wp.1.val
  ksC : ∀ sc ∈ C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → ∀ a : U64, Sched.ScObj sc n a →
    a.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ a.val
  /-- The spec's CR3 (for the arch relation, outside the IPC code). -/
  cr3 : σ.archState.x64CurrentCr3 = cr

/-- **The spec step of IPC code** for `VsP`: the arch state, the IRQ state
and node, the current thread, the arch objects and the SC sizes kept. -/
def VsKeep (σ σ' : Fl4Spec.State Unit) : Prop :=
  σ'.archState = σ.archState ∧ σ'.interruptStates = σ.interruptStates ∧
    σ'.interruptIrqNode = σ.interruptIrqNode ∧ σ'.curThread = σ.curThread ∧
    (∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = σ.kheap q) ∧ Sched.SzKeep σ σ'

theorem VsKeep.refl (σ : Fl4Spec.State Unit) : VsKeep σ σ :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ _ => rfl, Sched.SzKeep.of_kheap rfl⟩

theorem VsKeep.trans {σ1 σ2 σ3 : Fl4Spec.State Unit} (h1 : VsKeep σ1 σ2) (h2 : VsKeep σ2 σ3) : VsKeep σ1 σ3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1,
    fun q ao hq => (h2.2.2.2.2.1 q ao (by rw [h1.2.2.2.2.1 q ao hq]; exact hq)).trans (h1.2.2.2.2.1 q ao hq),
    fun p x n hp => by
      obtain ⟨x2, h⟩ := h2.2.2.2.2.2 p x n hp
      exact h1.2.2.2.2.2 p x2 n h⟩

/-- **The words IPC code writes**: IPC words, core `c`'s node, SC words, slot
words. -/
def IpcVW (th : TypedHeap) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) (b : U64) : Prop :=
  IWords N T E R B b ∨ NodeW (L.ksb s) c b ∨
    (∃ sc ∈ C, ∃ x n, σ.kheap sc.bv = some (.schedContext x n) ∧ Sched.ScObj sc n b) ∨ Sched.SlotWd th b

theorem slotWd_range' {th : TypedHeap} (hP : Placed th) {b : U64} (h : Sched.SlotWd th b) :
    ∃ y, IsSlot th y ∧ y.val ≤ b.val ∧ b.val < y.val + 32 := by
  obtain ⟨y, hy, k, hk, rfl⟩ := h
  have := hy.fit hP; have := hk.lt
  exact ⟨y, hy, by rw [wordOf_val (by omega)]; omega, by rw [wordOf_val (by omega)]; omega⟩

/-- An IPC write word is either one the other relations read (`OObj`) or a
slot word, never in the kernel-global block. -/
theorem IpcVW.cases {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit} {P L4 L3 L2 L1 : Set U64}
    (h : VsP (L := L) th cr N T C E R B c s σ) (hIA : IpcApart th N T E R B (L.ksb s) c) (hPl : Placed th) {b : U64}
    (hb : IpcVW (L := L) th N T C E R B c s σ b) :
    (Vs.OObj st N T C E R B c s σ b ∨ ∃ y, IsSlot th y ∧ y.val ≤ b.val ∧ b.val < y.val + 32) ∧
      (b.val < (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ b.val) := by
  have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
  rcases hb with (⟨t, ht, h1, h2⟩ | ⟨e, he, h1, h2⟩ | ⟨r, hr, h1, h2⟩ | ⟨n, hn, h1, h2⟩ | ⟨wp, hw, h1, h2⟩) |
    ⟨h1, h2⟩ | ⟨sc, hsc, x, n, hk, hobj⟩ | hsw
  · exact ⟨Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, h1, h2⟩))), by have := h.ksT t ht; omega⟩
  · exact ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, he, h1, h2⟩)))), by have := h.ksE e he; omega⟩
  · exact ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨r, hr, h1, h2⟩))))), by have := h.ksR r hr; omega⟩
  · exact ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, hn, h1, by omega⟩)))))),
      by have := h.ksN n hn; omega⟩
  · exact ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hw, h1, h2⟩))))))),
      by have := h.ksB wp hw; omega⟩
  · exact ⟨Or.inl (Or.inl ⟨by rw [hnb]; exact h1, by rw [hnb]; exact h2⟩), by omega⟩
  · refine ⟨Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x, n, hk, hobj⟩))))))), ?_⟩
    have := h.ksC sc hsc x n hk b hobj; omega
  · obtain ⟨y, hy, g1, g2⟩ := slotWd_range' hPl hsw
    refine ⟨Or.inr ⟨y, hy, g1, g2⟩, ?_⟩
    by_contra hc
    exact hIA.ks b (by omega) (by omega) y hy ⟨g1, g2⟩

/-- **`VsP` across an IPC step**: FL4 writes IPC words, node words, SC words
and slot words (`IpcVW`), the spec keeps what `VsKeep` says, and the MDB
gives the current thread's root after (`MdbLinks`, `VsMdbInv`). -/
theorem VsP.frame {th : TypedHeap} {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop} {G' : MdbGhost}
    (h : VsP (L := L) th cr N T C E R B c s σ) (hIA : IpcApart th N T E R B (L.ksb s) c) (hPl : Placed th)
    (hW : WritesIn st s s' W) (hWI : ∀ b, W b → IpcVW (L := L) th N T C E R B c s σ b) (hK : VsKeep σ σ')
    (hM' : MdbLinks th (L.mem s') G') (hV' : Vs.VsMdbInv (L.ksb s') (L.mem s') G') :
    VsP (L := L) th cr N T C E R B c s' σ' := by
  obtain ⟨hksb, -, hmem⟩ := hW
  obtain ⟨har, hist, hinode, hcur, harch, hsz⟩ := hK
  obtain ⟨P, L4, L3, L2, L1, hR, hPt, hPI, hCO, hP⟩ := h.ex
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  -- a word the VSpace relations read, outside the objects and not an `OObj` word
  have hout : ∀ b, Aligned b → OutsideObjects th b → Vs.VObj th P L4 L3 L2 L1 (L.ksb s) b → L.mem s' b = L.mem s b := by
    intro b hb ho hv
    refine hmem b hb fun hw => ?_
    rcases (IpcVW.cases (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) h hIA hPl (hWI b hw)).1 with
      hO | ⟨y, hy, g1, g2⟩
    · exact hP.disj b hO hv
    · obtain ⟨q, k, hq, h3, h4, -⟩ := slot_in_object hPl hy
      exact ho.2 q k hq ⟨by omega, by omega⟩
  have hvw : ∀ b, Vs.VsWrite P (L.ksb s) b → L.mem s' b = L.mem s b := fun b hb =>
    hout b (hP.vo b hb).1 (hP.vo b hb) (Vs.vsWrite_vobj hP.vs hb)
  have hpw : ∀ b, Vs.PtWAll L4 L3 L2 L1 b → L.mem s' b = L.mem s b := fun b hb => by
    refine hout b (hP.po b hb).1 (hP.po b hb) ?_
    obtain ⟨q, hq, i, hi, rfl⟩ := hb
    exact Vs.table_vobj hP.pt hq hi _
  have hks : ∀ b : U64, Aligned b → (L.ksb s).val ≤ b.val → b.val < (L.ksb s).val + 13568 →
      L.mem s' b = L.mem s b := fun b hb h1 h2 => hmem b hb fun hw => by
    have := (IpcVW.cases (P := P) (L4 := L4) (L3 := L3) (L2 := L2) (L1 := L1) h hIA hPl (hWI b hw)).2; omega
  have hsz' : ∀ (sc : U64) x n, σ'.kheap sc.bv = some (.schedContext x n) → ∃ x0, σ.kheap sc.bv = some (.schedContext x0 n) :=
    fun sc x n hx => hsz _ x n hx
  have hnb : L.nodeBase s' c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hksb]
  have hOO : ∀ a, Vs.OObj st N T C E R B c s' σ' a → Vs.OObj st N T C E R B c s σ a := by
    intro a ha
    unfold Vs.OObj at ha ⊢
    rw [hnb, hksb] at ha
    rcases ha with h | h | h | h | h | h | ⟨sc, hsc, x, n, hk, hob⟩ | h
    all_goals first
      | exact Or.inl h | exact Or.inr (Or.inl h) | exact Or.inr (Or.inr (Or.inl h))
      | exact Or.inr (Or.inr (Or.inr (Or.inl h))) | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
      | (obtain ⟨x0, h0⟩ := hsz' sc x n hk
         exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨sc, hsc, x0, n, h0, hob⟩)))))))
  refine ⟨⟨P, L4, L3, L2, L1, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by rw [har]; exact h.cr3⟩
  · rw [hksb]
    refine hR.frame hvw (by rw [har]) fun p hp => ?_
    obtain ⟨f, hf, -⟩ := hR.pool p hp
    exact harch _ _ hf
  · refine hPt.frame hpw fun q hq => ?_
    rcases hq with hq | hq | hq | hq
    · obtain ⟨g, hg, -⟩ := hPt.l4 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l3 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l2 q hq; exact harch _ _ hg
    · obtain ⟨g, hg, -⟩ := hPt.l1 q hq; exact harch _ _ hg
  · intro q hq lo hl
    have hw : Vs.VsWrite P (L.ksb s) (Vs.peA q lo) := Or.inr ⟨q, hq, lo, hl, rfl⟩
    rw [hvw _ hw]; exact hPI q hq lo hl
  · obtain ⟨t, h1, h2, -⟩ := hCO
    obtain ⟨⟨P', L4', L3', L2', L1', hVC⟩, -⟩ := hV'
    refine ⟨t, h1.trans hcur.symm, h2, fun p asid hc => ?_⟩
    have hv := hVC.at hM' ⟨t, 1, Or.inr ⟨h2, by decide⟩, rfl⟩ hc (by simp)
    simp only [Vs.VCapOK] at hv
    exact (hv.2.2 trivial).1
  · exact ⟨hP.ep, by rw [hksb]; exact hP.vs, hP.pt, hP.pl, fun x hx => by rw [hksb]; exact hP.disj x (hOO x hx),
      fun x h1 h2 => by rw [hnb] at h1 h2; exact hP.nodeE x h1 h2,
      hP.po, hP.ps, by rw [hksb]; exact hP.pv, by rw [hksb]; exact hP.vo, by rw [hksb]; exact hP.sd,
      by rw [hksb]; exact hP.tko⟩
  · rw [hksb]; exact Vs.IrqRel.ksFrame h.irq hkf hka hks hist hinode
  · rw [hksb]; exact Vs.IoRel.ksFrame h.io hkf hka hks (by rw [har])
  · have hkr := h.kr
    unfold Vs.KRootRel Vs.globCr3 at hkr ⊢
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [hksb, hks _ (by unfold Aligned; rw [hkv]; omega) (by rw [hkv]; omega) (by rw [hkv]; omega), har]
    exact hkr
  · rw [hksb]; exact h.ksT
  · rw [hksb]; exact h.ksE
  · rw [hksb]; exact h.ksR
  · rw [hksb]; exact h.ksN
  · rw [hksb]; exact h.ksB
  · intro sc hsc x n hk a ha
    obtain ⟨x0, h0⟩ := hsz' sc x n hk
    rw [hksb]; exact h.ksC sc hsc x0 n h0 a ha

/-- **`RelTopM` for the IPC proofs** at the typed heap `th`: with its typed
heap apart from the IPC words and the SC objects apart from the slots, and the
VSpace and kernel-state parts (`VsP`). -/
def RelTopI (th : TypedHeap) (cr : Fl4Spec.Cr3) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S)
    (σ : Fl4Spec.State Unit) : Prop :=
  (∃ G, RelTopB (L := L) th G N T C E R B c s σ) ∧ VsP (L := L) th cr N T C E R B c s σ

theorem RelTopI.relTop {s : S} {σ : Fl4Spec.State Unit} (h : RelTopI (L := L) th cr N T C E R B c s σ) :
    RelTopM (L := L) s σ :=
  let ⟨⟨G, hPl, hCR, hFI, hD, hMO, _, _⟩, _⟩ := h
  ⟨th, G, hPl, hCR, hFI, hD, hMO⟩

/-- **The frame**: FL4 writing only IPC words and words of core `c`'s node,
the spec keeping the caps and the domain schedule. -/
theorem RelTopB.frameN {th : TypedHeap} {G : MdbGhost} {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (h : RelTopB (L := L) th G N T C E R B c s σ) (hW : WritesIn st s s' W)
    (hWI : ∀ a, W a → IWords N T E R B a ∨ NodeW (L.ksb s) c a)
    (hK : CKeep σ σ') (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (hz : Sched.SzKeep σ σ') :
    RelTopB (L := L) th G N T C E R B c s' σ' := by
  obtain ⟨hPl, hCR, hFI, hD, hMO, hA, hSA⟩ := h
  obtain ⟨hksb, -, hmem⟩ := hW
  have hSS : SlotsSame th (L.mem s) (L.mem s') := by
    intro a ha
    have hf := ha.fit hPl
    have hal := ha.align hPl
    have w : ∀ k : U64, k.val < 32 → k.val % 8 = 0 → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := by
      intro k hk hk8
      have hv := wordOf_val (a := a) (k := k) (by omega)
      refine hmem _ (by unfold P1.Aligned; rw [hv]; omega) fun hw => ?_
      rcases hWI _ hw with hi | ⟨h1, h2⟩
      · exact hA.slot _ hi a ha (by rw [hv]; omega)
      · exact hA.node _ h1 h2 a ha (by rw [hv]; omega)
    refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
    have := w 0#u64 (by decide) (by decide)
    rwa [wordOf_zero] at this
  have hDS : DomSame (L.mem s) (L.mem s') (L.ksb s) :=
    Vs.domSame_low hA.kfit hA.kal fun b hb h1 h2 => hmem b hb fun hw => by
      rcases hWI _ hw with hi | ⟨h3, -⟩
      · have := hA.dom _ hi; omega
      · omega
  refine ⟨hPl, ⟨(hCR.1.of_ckeep hK).of_caps (fun x hx => hSS.capAt hx),
      SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy), hCR.2.2.1.of_same hSS,
      hCR.2.2.2.1.of_same hSS hK.cdt hK.orig, MdbInv.of_same hCR.2.2.1 hCR.2.2.2.2 hSS⟩,
    hFI.of_same hCR.2.2.1 hSS hK.ks, ?_, ?_, ?_, hSA.mono hz⟩
  · rw [hksb]; exact hD.of_same hDS hdl hds
  · rw [hksb]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO
  · rw [hksb]; exact hA

theorem RelTopI.frameN {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (h : RelTopI (L := L) th cr N T C E R B c s σ) (hW : WritesIn st s s' W)
    (hWI : ∀ a, W a → IWords N T E R B a ∨ NodeW (L.ksb s) c a)
    (hK : CKeep σ σ') (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (hKV : VsKeep σ σ') :
    RelTopI (L := L) th cr N T C E R B c s' σ' :=
  let ⟨⟨G, hB⟩, hV⟩ := h
  have hB' := hB.frameN hW hWI hK hdl hds hKV.2.2.2.2.2
  ⟨⟨G, hB'⟩, hV.frame hB.2.2.2.2.2.1 hB.1 hW (fun b hb => (hWI b hb).elim Or.inl (fun h => Or.inr (Or.inl h))) hKV
    hB'.2.1.2.2.1 hB'.2.2.2.2.1.2.2⟩

/-- **`RelTopI` from the post's `RelTopB`** over IPC writes and a `VsKeep` step. -/
theorem RelTopI.of_B {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop} {G' : MdbGhost}
    (h : RelTopI (L := L) th cr N T C E R B c s σ) (hB' : RelTopB (L := L) th G' N T C E R B c s' σ')
    (hW : WritesIn st s s' W) (hWI : ∀ b, W b → IpcVW (L := L) th N T C E R B c s σ b) (hKV : VsKeep σ σ') :
    RelTopI (L := L) th cr N T C E R B c s' σ' :=
  let ⟨⟨_, hB⟩, hV⟩ := h
  ⟨⟨G', hB'⟩, hV.frame hB.2.2.2.2.2.1 hB.1 hW hWI hKV hB'.2.1.2.2.1 hB'.2.2.2.2.1.2.2⟩

/-- **The frame** for FL4 writing only IPC words. -/
theorem RelTopI.frame {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (h : RelTopI (L := L) th cr N T C E R B c s σ) (hW : WritesIn st s s' W) (hWI : ∀ a, W a → IWords N T E R B a)
    (hK : CKeep σ σ') (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex)
    (hKV : VsKeep σ σ') :
    RelTopI (L := L) th cr N T C E R B c s' σ' :=
  h.frameN hW (fun a ha => Or.inl (hWI a ha)) hK hdl hds hKV

/-! ## The spec's IPC steps keep the caps -/

/-- A notification step keeps the caps and the domain schedule. -/
theorem _root_.Fl4Proofs.P3.Notif.NtfnStep.ckeep {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') :
    CKeep σ σ' ∧ σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex := by
  obtain ⟨-, hab, hk⟩ := h
  have h1 := congrArg Fl4Spec.AbstractState.cdt hab
  have h2 := congrArg Fl4Spec.AbstractState.isOriginalCap hab
  have h3 := congrArg Fl4Spec.AbstractState.domainList hab
  have h4 := congrArg Fl4Spec.AbstractState.domainStartIndex hab
  refine ⟨⟨fun o => ?_, fun o r cs hc _ => ?_, fun o t ht => ?_, h1, h2⟩, h3, h4⟩
  · rcases hk o with e | ⟨x, y, h1, h2, -⟩ | ⟨x, y, h1, h2, -⟩
    · exact ⟨fun r cs hc hw => ⟨cs, e ▸ hc, hw⟩, fun t ht => ⟨t, e ▸ ht⟩, fun hn => e ▸ hn⟩
    · refine ⟨fun r cs hc _ => ?_, fun t ht => ?_, fun hn => ?_⟩ <;> simp_all
    · refine ⟨fun r cs hc _ => ?_, fun t ht => ⟨x, h1⟩, fun hn => ?_⟩ <;> simp_all
  · rcases hk o with e | ⟨x, y, h1, h2, -⟩ | ⟨x, y, h1, h2, -⟩
    · rw [e]; exact hc
    · rw [hc] at h1; cases h1
    · rw [hc] at h1; cases h1
  · rcases hk o with e | ⟨x, y, h1, h2, -⟩ | ⟨x, y, h1, h2, hy⟩
    · exact ⟨t, by rw [e]; exact ht, rfl⟩
    · rw [ht] at h1; cases h1
    · rw [ht] at h1; injection h1 with h1; injection h1 with h1; subst h1
      exact ⟨y, h2, by rw [hy]; rfl⟩

/-- An endpoint step keeps the caps and the domain schedule. -/
theorem _root_.Fl4Proofs.P3.Endp.EpStep.ckeep {σ σ' : Fl4Spec.State Unit} (h : EpStep σ σ') :
    CKeep σ σ' ∧ σ'.domainList = σ.domainList ∧ σ'.domainStartIndex = σ.domainStartIndex := by
  obtain ⟨-, hab, hk⟩ := h
  have h1 := congrArg Fl4Spec.AbstractState.cdt hab
  have h2 := congrArg Fl4Spec.AbstractState.isOriginalCap hab
  have h3 := congrArg Fl4Spec.AbstractState.domainList hab
  have h4 := congrArg Fl4Spec.AbstractState.domainStartIndex hab
  refine ⟨⟨fun o => ?_, fun o r cs hc _ => ?_, fun o t ht => ?_, h1, h2⟩, h3, h4⟩
  · rcases hk o with e | ⟨x, y, h1, h2⟩ | ⟨x, y, h1, h2, -⟩ | ⟨x, y, h1, h2, -⟩
    · exact ⟨fun r cs hc hw => ⟨cs, e ▸ hc, hw⟩, fun t ht => ⟨t, e ▸ ht⟩, fun hn => e ▸ hn⟩
    · exact ⟨fun r cs hc _ => (by rw [h2] at hc; cases hc), fun t ht => (by rw [h2] at ht; cases ht),
        fun hn => (by rw [h1] at hn; cases hn)⟩
    · exact ⟨fun r cs hc _ => (by rw [h2] at hc; cases hc), fun t ht => (by rw [h2] at ht; cases ht),
        fun hn => (by rw [h1] at hn; cases hn)⟩
    · exact ⟨fun r cs hc _ => (by rw [h2] at hc; cases hc), fun t ht => ⟨x, h1⟩,
        fun hn => (by rw [h1] at hn; cases hn)⟩
  · rcases hk o with e | ⟨x, y, h1, h2⟩ | ⟨x, y, h1, h2, -⟩ | ⟨x, y, h1, h2, -⟩
    · rw [e]; exact hc
    all_goals (rw [hc] at h1; cases h1)
  · rcases hk o with e | ⟨x, y, h1, h2⟩ | ⟨x, y, h1, h2, -⟩ | ⟨x, y, h1, h2, hy⟩
    · exact ⟨t, by rw [e]; exact ht, rfl⟩
    · rw [ht] at h1; cases h1
    · rw [ht] at h1; cases h1
    · rw [ht] at h1; injection h1 with h1; injection h1 with h1; subst h1
      exact ⟨y, h2, by rw [hy]; rfl⟩

theorem SzKeep.epStep {σ σ' : Fl4Spec.State Unit} (h : EpStep σ σ') : Sched.SzKeep σ σ' := by
  intro p x n hp
  rcases h.2.2 p with e | ⟨a, b, -, hb⟩ | ⟨a, b, -, hb, -⟩ | ⟨a, b, -, hb, -⟩
  · exact ⟨x, e ▸ hp⟩
  all_goals (rw [hp] at hb; cases hb)

theorem VsKeep.of_kheap {σ σ' : Fl4Spec.State Unit} (hk : σ'.kheap = σ.kheap) (ha : σ'.archState = σ.archState)
    (hi : σ'.interruptStates = σ.interruptStates) (hn : σ'.interruptIrqNode = σ.interruptIrqNode)
    (hc : σ'.curThread = σ.curThread) : VsKeep σ σ' :=
  ⟨ha, hi, hn, hc, fun q _ _ => by rw [hk], Sched.SzKeep.of_kheap hk⟩

theorem VsKeep.stsAct (σ : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) : VsKeep σ (Notif.stsAct σ t) :=
  VsKeep.of_kheap (stsAct_kheap σ t) (by unfold Notif.stsAct; split <;> rfl) (by unfold Notif.stsAct; split <;> rfl)
    (by unfold Notif.stsAct; split <;> rfl) (by unfold Notif.stsAct; split <;> rfl)

/-- A TCB update keeps `VsKeep`. -/
theorem VsKeep.updK_tcb {σ : Fl4Spec.State Unit} {p : Fl4Spec.ObjRef} {x y : Fl4Spec.Tcb}
    (hk : σ.kheap p = some (.tcb x)) : VsKeep σ (updK σ p (.tcb y)) := by
  refine ⟨rfl, rfl, rfl, rfl, fun q ao hq => ?_, fun q z n hq => ?_⟩
  · have e : q ≠ p := by rintro rfl; rw [hk] at hq; cases hq
    simp [updK, Function.update_of_ne e]
  · have e : q ≠ p := by rintro rfl; simp [updK] at hq
    exact ⟨z, by simpa [updK, Function.update_of_ne e] using hq⟩

theorem VsKeep.epStep {σ σ' : Fl4Spec.State Unit} (h : EpStep σ σ') : VsKeep σ σ' := by
  obtain ⟨-, hab, hk⟩ := h
  refine ⟨(by have e := congrArg Fl4Spec.AbstractState.archState hab; exact e), (by have e := congrArg Fl4Spec.AbstractState.interruptStates hab; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.interruptIrqNode hab; exact e), (by have e := congrArg Fl4Spec.AbstractState.curThread hab; exact e),
    fun q ao hq => ?_, SzKeep.epStep ⟨rfl, hab, hk⟩⟩
  · rcases hk q with e | ⟨x, y, h1, -⟩ | ⟨x, y, h1, -, -⟩ | ⟨x, y, h1, -, -⟩
    · exact e
    all_goals (rw [hq] at h1; cases h1)

theorem VsKeep.ntfnStep {σ σ' : Fl4Spec.State Unit} (h : NtfnStep σ σ') : VsKeep σ σ' := by
  obtain ⟨-, hab, hk⟩ := h
  refine ⟨(by have e := congrArg Fl4Spec.AbstractState.archState hab; exact e), (by have e := congrArg Fl4Spec.AbstractState.interruptStates hab; exact e),
    (by have e := congrArg Fl4Spec.AbstractState.interruptIrqNode hab; exact e), (by have e := congrArg Fl4Spec.AbstractState.curThread hab; exact e),
    fun q ao hq => ?_, Sched.SzKeep.ntfnStep ⟨rfl, hab, hk⟩⟩
  · rcases hk q with e | ⟨x, y, h1, -⟩ | ⟨x, y, h1, -, -⟩
    · exact e
    all_goals (rw [hq] at h1; cases h1)

theorem RelTopI.stableN (hT : TcbPlaced T) {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : RelTopI (L := L) th cr N T C E R B c s σ) (hW : WritesIn st s s' (NWrite N T)) (hK : NtfnStep σ σ') :
    RelTopI (L := L) th cr N T C E R B c s' σ' :=
  let ⟨hc, hl, hs⟩ := hK.ckeep
  h.frame hW (fun _ ha => NWrite.iwords hT ha) hc hl hs (VsKeep.ntfnStep hK)

theorem RelTopI.stableE {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : RelTopI (L := L) th cr N T C E R B c s σ) (hW : WritesIn st s s' (EWrite T E R B)) (hK : EpStep σ σ') :
    RelTopI (L := L) th cr N T C E R B c s' σ' :=
  let ⟨hc, hl, hs⟩ := hK.ckeep
  h.frame hW (fun _ ha => EWrite.iwords ha) hc hl hs (VsKeep.epStep hK)

end

/-! ## The hypotheses for `RelTopI ∧ SR` -/

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `RelTopI` with the other subsystems' relation. -/
def SRT (th : TypedHeap) (cr : Fl4Spec.Cr3) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64)
    (SR : S → Fl4Spec.State Unit → Prop) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  RelTopI (L := L) th cr N T C E R B c s σ ∧ SR s σ

/-- **The scheduler-side fields of `IpcSchedHyps` for `RelTopI ∧ SR`**: the
operations that write scheduler words (`schedule_tcb`, the wake tail,
`cancel_ipc`), outside the IPC frame. -/
structure IpcTopTails (th : TypedHeap) (cr : Fl4Spec.Cr3) (N T C E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  scheduleTcb : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → ScRelM T (L.mem s) σ →
    SRT st th cr N T C E R B c SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧
      SRT st th cr N T C E R B c SR s' (stsAct σ t.bv) ⦄
  wakeTail : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
    SRT st th cr N T C E R B c SR s σ → t ∈ T →
    n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running → NotQueued σ t.bv →
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st th cr N T C E R B c SR r.1 σ' ⦄
  cancelIpc : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
    SRT st th cr N T C E R B c SR s σ → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
    ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st th cr N T C E R B c SR r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧
      x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ⦄

variable {st ar}

/-- **`IpcSchedHyps` for `RelTopI ∧ SR`**: the stabilities and `block` by the
frame, `notQueued` from `SR`, the scheduler-side fields given. -/
theorem IpcSchedHyps.withTop {SR : S → Fl4Spec.State Unit → Prop} (hH : IpcSchedHyps st ar N T E R B SR)
    (hT : TcbPlaced T) (hX : IpcTopTails st ar th cr N T C E R B c SR) :
    IpcSchedHyps st ar N T E R B (SRT st th cr N T C E R B c SR) where
  stableN s s' σ σ' h hW hK hNB := ⟨h.1.stableN hT hW hK, hH.stableN s s' σ σ' h.2 hW hK hNB⟩
  stableE s s' σ σ' h hW hK := ⟨h.1.stableE hW hK, hH.stableE s s' σ σ' h.2 hW hK⟩
  notQueued s σ t x hR h hk hr := hH.notQueued s σ t x hR h.2 hk hr
  block s s' σ σ' t h hq hb hsa hid hW hK hst :=
    ⟨h.1.stableN hT hW hK, hH.block s s' σ σ' t h.2 hq hb hsa hid hW hK hst⟩
  scheduleTcb := hX.scheduleTcb
  wakeTail := hX.wakeTail
  cancelIpc := hX.cancelIpc

theorem EpBufHyps.withTop {SR : S → Fl4Spec.State Unit → Prop} (h : EpBufHyps st T E R B SR) :
    EpBufHyps st T E R B (SRT st th cr N T C E R B c SR) :=
  ⟨fun s σ t x b hR hS => h.lookup s σ t x b hR hS.2⟩

theorem EpBufMapHyps.withTop {SR : S → Fl4Spec.State Unit → Prop} (h : EpBufMapHyps st T E R B SR) :
    EpBufMapHyps st T E R B (SRT st th cr N T C E R B c SR) :=
  ⟨fun s σ t x b p hR hS => h.lookupMap s σ t x b p hR hS.2, fun s σ t x p hR hS => h.frame s σ t x p hR hS.2,
    fun s σ t x p hR hS => h.recvSlots s σ t x p hR hS.2⟩

/-- The composite relation after an IPC theorem with `SRT`. -/
theorem SRT.relTop {SR : S → Fl4Spec.State Unit → Prop} {s : S} {σ : Fl4Spec.State Unit}
    (h : IpcRel N T E R B (L.mem s) σ ∧ SRT st th cr N T C E R B c SR s σ) :
    RelTopM (L := L) s σ ∧ IpcRel N T E R B (L.mem s) σ ∧ SR s σ :=
  ⟨h.2.1.relTop, h.1, h.2.2⟩

end Hyps

end

end Fl4Proofs.P3.Ipc
