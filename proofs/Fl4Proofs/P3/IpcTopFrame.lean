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
variable {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

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
  kfit : kb.val + 13568 ≤ 2 ^ 64
  kal : kb.val % 8 = 0

/-- **`IpcApart` from `TopPlaced`** and the IPC objects' distance from the
kernel-global block (for the TCBs, `SchedRel`'s `ksOut`; for the buffer
words, `BufPlaced.dom`). -/
theorem IpcApart.of_top {th : TypedHeap} {P L4 L3 L2 L1 C : Set U64} {s : S} {σ : Fl4Spec.State Unit}
    (hP : Vs.TopPlaced st th P L4 L3 L2 L1 N T C E R B c s σ)
    (hkT : ∀ t ∈ T, t.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ t.val)
    (hkE : ∀ e ∈ E, e.val + 16 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ e.val)
    (hkR : ∀ r ∈ R, r.val + 32 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ r.val)
    (hkN : ∀ n ∈ N, n.val + 40 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ n.val)
    (hkB : ∀ wp ∈ B, wp.1.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ wp.1.val) :
    IpcApart th N T E R B (L.ksb s) c := by
  refine ⟨fun a ha x hx ⟨h1, h2⟩ => ?_, fun a h1 h2 x hx ⟨h3, h4⟩ =>
    hP.disj a (Or.inl ⟨h1, h2⟩) (Vs.vobj_of_slot hP.pl P L4 L3 L2 L1 (L.ksb s) hx h3 h4), fun a ha => ?_, by have := hP.vs.ksb_fit; omega, hP.vs.ksb_al⟩
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

/-! ## The relation and its frame -/

/-- **`RelTopM` for the IPC proofs**: with its typed heap apart from the
IPC words. -/
def RelTopI (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∃ th G, Placed th ∧ CRel th (L.mem s) σ G ∧ FinInv th (L.mem s) σ G ∧ DomRel (L.mem s) (L.ksb s) σ ∧
    MdbOKV (L.ksb s) (L.mem s) G ∧ IpcApart th N T E R B (L.ksb s) c

theorem RelTopI.relTop {s : S} {σ : Fl4Spec.State Unit} (h : RelTopI (L := L) N T E R B c s σ) :
    RelTopM (L := L) s σ :=
  let ⟨th, G, hPl, hCR, hFI, hD, hMO, _⟩ := h
  ⟨th, G, hPl, hCR, hFI, hD, hMO⟩

/-- The words of core `c`'s node. -/
def NodeW (kb c a : U64) : Prop :=
  kb.val + 13568 + c.val * 4288 ≤ a.val ∧ a.val < kb.val + 13568 + c.val * 4288 + 4288

/-- **The frame**: FL4 writing only IPC words and words of core `c`'s node,
the spec keeping the caps and the domain schedule. -/
theorem RelTopI.frameN {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (h : RelTopI (L := L) N T E R B c s σ) (hW : WritesIn st s s' W)
    (hWI : ∀ a, W a → IWords N T E R B a ∨ NodeW (L.ksb s) c a)
    (hK : CKeep σ σ') (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex) :
    RelTopI (L := L) N T E R B c s' σ' := by
  obtain ⟨th, G, hPl, hCR, hFI, hD, hMO, hA⟩ := h
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
  refine ⟨th, G, hPl, ⟨(hCR.1.of_ckeep hK).of_caps (fun x hx => hSS.capAt hx),
      SlotsValid.of_caps hCR.2.1 (fun y hy => hSS.capAt hy), hCR.2.2.1.of_same hSS,
      hCR.2.2.2.1.of_same hSS hK.cdt hK.orig, MdbInv.of_same hCR.2.2.1 hCR.2.2.2.2 hSS⟩,
    hFI.of_same hCR.2.2.1 hSS hK.ks, ?_, ?_, ?_⟩
  · rw [hksb]; exact hD.of_same hDS hdl hds
  · rw [hksb]; exact MdbOKV.of_same hCR.2.2.1 hSS hMO
  · rw [hksb]; exact hA

/-- **The frame** for FL4 writing only IPC words. -/
theorem RelTopI.frame {s s' : S} {σ σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (h : RelTopI (L := L) N T E R B c s σ) (hW : WritesIn st s s' W) (hWI : ∀ a, W a → IWords N T E R B a)
    (hK : CKeep σ σ') (hdl : σ'.domainList = σ.domainList) (hds : σ'.domainStartIndex = σ.domainStartIndex) :
    RelTopI (L := L) N T E R B c s' σ' :=
  h.frameN hW (fun a ha => Or.inl (hWI a ha)) hK hdl hds

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

theorem RelTopI.stableN (hT : TcbPlaced T) {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : RelTopI (L := L) N T E R B c s σ) (hW : WritesIn st s s' (NWrite N T)) (hK : NtfnStep σ σ') :
    RelTopI (L := L) N T E R B c s' σ' :=
  let ⟨hc, hl, hs⟩ := hK.ckeep
  h.frame hW (fun _ ha => NWrite.iwords hT ha) hc hl hs

theorem RelTopI.stableE {s s' : S} {σ σ' : Fl4Spec.State Unit}
    (h : RelTopI (L := L) N T E R B c s σ) (hW : WritesIn st s s' (EWrite T E R B)) (hK : EpStep σ σ') :
    RelTopI (L := L) N T E R B c s' σ' :=
  let ⟨hc, hl, hs⟩ := hK.ckeep
  h.frame hW (fun _ ha => EWrite.iwords ha) hc hl hs

end

/-! ## The hypotheses for `RelTopI ∧ SR` -/

section Hyps
variable {S A : Type} (st : machine.Store S) (ar : machine.Arch A) [L : LawfulStore st]
variable {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- `RelTopI` with the other subsystems' relation. -/
def SRT (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (SR : S → Fl4Spec.State Unit → Prop)
    (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  RelTopI (L := L) N T E R B c s σ ∧ SR s σ

/-- **The scheduler-side fields of `IpcSchedHyps` for `RelTopI ∧ SR`**: the
operations that write scheduler words (`schedule_tcb`, the wake tail,
`cancel_ipc`), outside the IPC frame. -/
structure IpcTopTails (N T E R : Set U64) (B : Set (U64 × Fl4Spec.Word)) (c : U64) (SR : S → Fl4Spec.State Unit → Prop) :
    Prop where
  scheduleTcb : ∀ s σ (t : U64), EpStateRel T E R B (L.mem s) σ → ScRelM T (L.mem s) σ →
    SRT st N T E R B c SR s σ → t ∈ T →
    sched.schedule_tcb st s t ⦃ s' => Agree (L.mem s) (L.mem s') (IFoot N T E R B) ∧
      SRT st N T E R B c SR s' (stsAct σ t.bv) ⦄
  wakeTail : ∀ s (a : A) σ (t n : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
    SRT st N T E R B c SR s σ → t ∈ T →
    n ∈ N → σ.kheap t.bv = some (.tcb x) → x.tcbState = .running → NotQueued σ t.bv →
    rustWakeTail st ar s a t n ⦃ r => ¬ (specWakeTail t.bv n.bv σ).2 ∧ ∃ σ', ((), σ') ∈ (specWakeTail t.bv n.bv σ).1 ∧
      Agree (L.mem s) (L.mem r.1) (IFoot N T E R B) ∧ IKView σ σ' ∧ SRT st N T E R B c SR r.1 σ' ⦄
  cancelIpc : ∀ s (a : A) σ (t : U64) (x : Fl4Spec.Tcb), IpcRel N T E R B (L.mem s) σ →
    SRT st N T E R B c SR s σ → t ∈ T →
    σ.kheap t.bv = some (.tcb x) → Fl4Spec.receiveBlocked x.tcbState = true →
    ipc.cancel_ipc st ar s a t ⦃ r => ∃ σ' x', Fl4Spec.cancelIpc (Z := Unit) t.bv σ = ({((), σ')}, False) ∧
      IpcRel N T E R B (L.mem r.1) σ' ∧ SRT st N T E R B c SR r.1 σ' ∧ σ'.kheap t.bv = some (.tcb x') ∧
      x'.tcbState = .inactive ∧ RelIfBound σ' t.bv ⦄

variable {st ar}

/-- **`IpcSchedHyps` for `RelTopI ∧ SR`**: the stabilities and `block` by the
frame, `notQueued` from `SR`, the scheduler-side fields given. -/
theorem IpcSchedHyps.withTop {SR : S → Fl4Spec.State Unit → Prop} (hH : IpcSchedHyps st ar N T E R B SR)
    (hT : TcbPlaced T) (hX : IpcTopTails st ar N T E R B c SR) :
    IpcSchedHyps st ar N T E R B (SRT st N T E R B c SR) where
  stableN s s' σ σ' h hW hK hNB := ⟨h.1.stableN hT hW hK, hH.stableN s s' σ σ' h.2 hW hK hNB⟩
  stableE s s' σ σ' h hW hK := ⟨h.1.stableE hW hK, hH.stableE s s' σ σ' h.2 hW hK⟩
  notQueued s σ t x h hk hr := hH.notQueued s σ t x h.2 hk hr
  block s s' σ σ' t h hq hb hsa hid hW hK hst :=
    ⟨h.1.stableN hT hW hK, hH.block s s' σ σ' t h.2 hq hb hsa hid hW hK hst⟩
  scheduleTcb := hX.scheduleTcb
  wakeTail := hX.wakeTail
  cancelIpc := hX.cancelIpc

theorem EpBufHyps.withTop {SR : S → Fl4Spec.State Unit → Prop} (h : EpBufHyps st T E R B SR) :
    EpBufHyps st T E R B (SRT st N T E R B c SR) :=
  ⟨fun s σ t x b hR hS => h.lookup s σ t x b hR hS.2⟩

theorem EpBufMapHyps.withTop {SR : S → Fl4Spec.State Unit → Prop} (h : EpBufMapHyps st T E R B SR) :
    EpBufMapHyps st T E R B (SRT st N T E R B c SR) :=
  ⟨fun s σ t x b p hR hS => h.lookupMap s σ t x b p hR hS.2, fun s σ t x p hR hS => h.frame s σ t x p hR hS.2,
    fun s σ t x p hR hS => h.recvSlots s σ t x p hR hS.2⟩

/-- The composite relation after an IPC theorem with `SRT`. -/
theorem SRT.relTop {SR : S → Fl4Spec.State Unit → Prop} {s : S} {σ : Fl4Spec.State Unit}
    (h : IpcRel N T E R B (L.mem s) σ ∧ SRT st N T E R B c SR s σ) :
    RelTopM (L := L) s σ ∧ IpcRel N T E R B (L.mem s) σ ∧ SR s σ :=
  ⟨h.2.1.relTop, h.1, h.2.2⟩

end Hyps

end

end Fl4Proofs.P3.Ipc
