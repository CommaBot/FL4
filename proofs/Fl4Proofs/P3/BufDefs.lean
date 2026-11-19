/-
P3 (DESIGN.md §9), IPC: **the IPC-buffer invariants' definitions**, upstream
of `JAtZ` (handoff/glob.md decisions 2-4): what `JAtZ.bok`/`JAtZ.fcov` and
`JCs.urz` state, and the spec-step frame `IpcFrKeep` most steps keep them by.

* `IpcFrKeep σ σ'`: every TCB after has a null IPC-frame cap or was a TCB
  with the same `tcb_ipcframe` and `tcb_ipc_buffer`; every non-device data
  page is kept (`page`), and none is new (`pback`). `refl`, `trans`,
  `of_kheap`, `of_epStep`, `of_updTcb`, `of_updObj`, `of_fresh`,
  `of_nullFrame`, `of_otk` (the SC/scheduler code's `OTK`), `of_slot2` (a
  CSpace step: objects kept, CNodes' slots or TCBs' caps changed, each TCB's
  FL4 buffer slot kept or emptied, the spec's frame cap read through
  `StateRel`).
* `Endp.IpcBufCapOK.keep`, `FrameCover.ipcFr` (both across `IpcFrKeep`).
* `FrameCover B σ` (decision 3): every 8-aligned word of every non-device
  data page is a pair `(a, a)` of `B`; `step`, `keep`, `of_kheap`.
* `UtZero mem G σ` (l4v `untyped_ranges_zero`): the spec's memory is zero in
  the free part of every RAM untyped cap of the MDB slots; `step`, `same`.
* `UmIn σ σ'`: every byte of the spec's memory changed lies in a non-device
  data page of `σ` (`of_eq`, `refl`, `trans`, `store`: one word stored in a
  user frame); `UtZero.umIn`/`UtZero.sameU` keep `UtZero` across it (with
  `SpecFree`: no object in a free part).
-/
import Fl4Proofs.P3.XTopCnodeAll
import Fl4Proofs.P3.XTopTcbAll
import Fl4Proofs.P3.IpcSendDon
import Fl4Proofs.P3.ScXProd
import Fl4Proofs.P3.ScUtRetype
import Fl4Proofs.P3.ScIpcSorted
import Fl4Proofs.P3.ScRecvLinks
import Fl4Proofs.P3.VsCapW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

section Spec
open Fl4Spec

/-- **A step keeping what `IpcBufCapOK` and `FrameCover` read** (module
docstring). -/
structure IpcFrKeep (σ σ' : State Unit) : Prop where
  tcb : ∀ t x', σ'.kheap t = some (.tcb x') → x'.tcbIpcframe = .nullCap ∨
    ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbIpcframe = x'.tcbIpcframe ∧ x.tcbIpcBuffer = x'.tcbIpcBuffer
  page : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
    σ'.kheap p = some (.archObj (.dataPage false vms))
  pback : ∀ p vms, σ'.kheap p = some (.archObj (.dataPage false vms)) →
    σ.kheap p = some (.archObj (.dataPage false vms))

namespace IpcFrKeep
variable {σ σ' σ'' : State Unit}

theorem refl (σ : State Unit) : IpcFrKeep σ σ :=
  ⟨fun _ x h => Or.inr ⟨x, h, rfl, rfl⟩, fun _ _ h => h, fun _ _ h => h⟩

theorem trans (h1 : IpcFrKeep σ σ') (h2 : IpcFrKeep σ' σ'') : IpcFrKeep σ σ'' := by
  refine ⟨fun t x3 h3 => ?_, fun p vms h => h2.page p vms (h1.page p vms h),
    fun p vms h => h1.pback p vms (h2.pback p vms h)⟩
  rcases h2.tcb t x3 h3 with e | ⟨x2, h2', e1, e2⟩
  · exact Or.inl e
  · rcases h1.tcb t x2 h2' with e | ⟨x1, h1', f1, f2⟩
    · exact Or.inl (by rw [← e1]; exact e)
    · exact Or.inr ⟨x1, h1', f1.trans e1, f2.trans e2⟩

theorem of_kheap (hk : σ'.kheap = σ.kheap) : IpcFrKeep σ σ' :=
  ⟨fun _ x h => Or.inr ⟨x, by rw [← hk]; exact h, rfl, rfl⟩, fun _ _ h => by rw [hk]; exact h,
    fun _ _ h => by rw [← hk]; exact h⟩

/-- An `EpStep` (the endpoint, reply and TCB-state code). -/
theorem of_epStep (hs : Endp.EpStep σ σ') : IpcFrKeep σ σ' := by
  obtain ⟨-, -, hk⟩ := hs
  refine ⟨fun t x' hx' => Or.inr ?_, fun p vms h => ?_, fun p vms h => ?_⟩
  · rcases hk t with e | ⟨a, b, h1, h2⟩ | ⟨a, b, h1, h2, -⟩ | ⟨a, b, h1, h2, e⟩
    · exact ⟨x', by rw [← e]; exact hx', rfl, rfl⟩
    · rw [hx'] at h2; cases h2
    · rw [hx'] at h2; cases h2
    · have hb : x' = b := by rw [hx'] at h2; exact KernelObject.tcb.inj (Option.some.inj h2)
      subst hb
      exact ⟨a, h1, by rw [e], by rw [e]⟩
  · rcases hk p with e | ⟨a, b, h1', -⟩ | ⟨a, b, h1', -, -⟩ | ⟨a, b, h1', -, -⟩
    · rw [e]; exact h
    · rw [h] at h1'; cases h1'
    · rw [h] at h1'; cases h1'
    · rw [h] at h1'; cases h1'
  · rcases hk p with e | ⟨a, b, -, h1'⟩ | ⟨a, b, -, h1', -⟩ | ⟨a, b, -, h1', -⟩
    · rw [← e]; exact h
    · rw [h] at h1'; cases h1'
    · rw [h] at h1'; cases h1'
    · rw [h] at h1'; cases h1'

/-- A TCB written keeping its IPC frame and buffer address. -/
theorem of_updTcb {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x)) (h1 : y.tcbIpcframe = x.tcbIpcframe)
    (h2 : y.tcbIpcBuffer = x.tcbIpcBuffer) : IpcFrKeep σ (Notif.updK σ t (.tcb y)) := by
  refine ⟨fun q x' hq => Or.inr ?_, fun p vms h => ?_, fun p vms h => ?_⟩
  · by_cases e : q = t
    · subst e
      simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hq
      subst hq
      exact ⟨x, hk, h1.symm, h2.symm⟩
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at hq
      exact ⟨x', hq, rfl, rfl⟩
  · by_cases e : p = t
    · subst e; rw [hk] at h; cases h
    · simp only [Notif.updK_kheap, Function.update_of_ne e]; exact h
  · by_cases e : p = t
    · subst e; simp only [Notif.updK_kheap, Function.update_self] at h; cases h
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at h; exact h

/-- An object that is no non-device data page written over no such page, a
TCB only with a null IPC frame (a new TCB: the retype's `default_tcb`). -/
theorem of_updObj {p : ObjRef} {o : KernelObject}
    (hp : ∀ vms, σ.kheap p ≠ some (.archObj (.dataPage false vms)))
    (hpo : ∀ vms, o ≠ .archObj (.dataPage false vms))
    (ho : ∀ x, o = .tcb x → x.tcbIpcframe = .nullCap) : IpcFrKeep σ (Notif.updK σ p o) := by
  refine ⟨fun q x' hq => ?_, fun q vms h => ?_, fun q vms h => ?_⟩
  · by_cases e : q = p
    · subst e
      simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq] at hq
      exact Or.inl (ho x' hq)
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at hq
      exact Or.inr ⟨x', hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; exact absurd h (hp vms)
    · simp only [Notif.updK_kheap, Function.update_of_ne e]; exact h
  · by_cases e : q = p
    · subst e; simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq] at h
      exact absurd h (hpo vms)
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at h; exact h

/-- **Objects added at free addresses**, the new TCBs with null IPC frames
and no new data page (the non-frame retypes). -/
theorem of_fresh (h : ∀ p, σ'.kheap p = σ.kheap p ∨
    (σ.kheap p = none ∧ (∀ x, σ'.kheap p = some (.tcb x) → x.tcbIpcframe = .nullCap) ∧
      ∀ vms, σ'.kheap p ≠ some (.archObj (.dataPage false vms)))) : IpcFrKeep σ σ' := by
  refine ⟨fun q x' hq => ?_, fun q vms hq => ?_, fun q vms hq => ?_⟩
  · rcases h q with e | ⟨-, hn, -⟩
    · exact Or.inr ⟨x', by rw [← e]; exact hq, rfl, rfl⟩
    · exact Or.inl (hn x' hq)
  · rcases h q with e | ⟨e, -⟩
    · rw [e]; exact hq
    · rw [hq] at e; cases e
  · rcases h q with e | ⟨-, -, hn⟩
    · rw [← e]; exact hq
    · exact absurd hq (hn vms)

/-- A TCB's IPC-frame slot emptied (a deletion of that slot's cap). -/
theorem of_nullFrame {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x)) (h1 : y.tcbIpcframe = .nullCap) :
    IpcFrKeep σ (Notif.updK σ t (.tcb y)) :=
  of_updObj (fun vms e => by rw [hk] at e; cases e) (fun _ e => by cases e) (fun x' e => by cases e; exact h1)

/-- **The SC and scheduler code's object steps** (`OTK`: a TCB changed in its
scheduling fields only, the other objects in kind kept). -/
theorem of_otk {P : ObjRef → Prop} (h : ∀ p, Sched.OTK (P p) (σ.kheap p) (σ'.kheap p)) : IpcFrKeep σ σ' := by
  refine ⟨fun q x' hq => Or.inr ?_, fun q vms hq => ?_, fun q vms hq => ?_⟩
  · have hq' := h q
    rw [hq] at hq'
    revert hq'
    cases e : σ.kheap q with
    | none => intro hq'; simp [Sched.OTK] at hq'
    | some o =>
      intro hq'
      simp only [Sched.OTK] at hq'
      rcases hq' with rfl | ⟨x, y, h1, h2, h3, -⟩ | ⟨_, _, _, _, h2⟩ | ⟨_, _, _, h2, -⟩ | ⟨_, _, _, h2, -⟩
      · exact ⟨x', rfl, rfl, rfl⟩
      · cases h2; subst h1; rw [h3]; exact ⟨x, rfl, rfl, rfl⟩
      all_goals cases h2
  · have hq' := h q
    rw [hq] at hq'
    revert hq'
    cases e : σ'.kheap q with
    | none => intro hq'; simp [Sched.OTK] at hq'
    | some o =>
      intro hq'
      simp only [Sched.OTK] at hq'
      rcases hq' with e' | ⟨_, _, h1, -⟩ | ⟨_, _, _, h1, -⟩ | ⟨_, _, h1, -⟩ | ⟨_, _, h1, -⟩
      · subst e'; rfl
      all_goals cases h1
  · have hq' := h q
    rw [hq] at hq'
    revert hq'
    cases e : σ.kheap q with
    | none => intro hq'; simp [Sched.OTK] at hq'
    | some o =>
      intro hq'
      simp only [Sched.OTK] at hq'
      rcases hq' with e' | ⟨_, _, -, h1, -⟩ | ⟨_, _, _, -, h1⟩ | ⟨_, _, -, h1, -⟩ | ⟨_, _, -, h1, -⟩
      · subst e'; rfl
      all_goals cases h1

/-- **A CSpace step** (module docstring): every object kept, a CNode's slots
or a TCB's caps changed (its buffer address kept), every TCB of the spec one
of the typed heap's, whose FL4 buffer slot (`slotOf t 2`) is kept or emptied;
the spec's IPC frame is FL4's (`StateRel.bufCap`, `CapRel` functional). -/
theorem of_slot2 {th : TypedHeap} {mem mem' : U64 → U64}
    (hkc : ∀ p, σ'.kheap p = σ.kheap p ∨ (∃ r cs cs', σ.kheap p = some (.cnode r cs) ∧ σ'.kheap p = some (.cnode r cs')) ∨
      ∃ x y, σ.kheap p = some (.tcb x) ∧ σ'.kheap p = some (.tcb y) ∧ y.tcbIpcBuffer = x.tcbIpcBuffer)
    (hR : StateRel th mem σ) (hR' : StateRel th mem' σ')
    (hT : ∀ t x, σ'.kheap t = some (.tcb x) → ∃ q : U64, q.bv = t ∧ th q = some .tcb)
    (h2 : ∀ q, th q = some .tcb → capAt mem' (slotOf q 2) = capAt mem (slotOf q 2) ∨ capV mem' (slotOf q 2) = .Null) :
    IpcFrKeep σ σ' := by
  refine ⟨fun t x' hx' => ?_, fun p vms h => ?_, fun p vms h => ?_⟩
  · obtain ⟨q, rfl, hq⟩ := hT t x' hx'
    obtain ⟨y', hky', hsl'⟩ := hR'.tcb q hq
    have e1 : y' = x' := by rw [hx'] at hky'; exact (KernelObject.tcb.inj (Option.some.inj hky')).symm
    subst e1
    obtain ⟨c', ac', hc', hac', hca'⟩ := hsl' 2 (by decide)
    rw [tcbCnodeMap_two] at hac'
    cases hac'
    rcases hkc q.bv with e | ⟨r, cs, cs', -, h1'⟩ | ⟨x, y, h1, h1', hb⟩
    · exact Or.inr ⟨y', by rw [← e]; exact hx', rfl, rfl⟩
    · rw [hx'] at h1'; cases h1'
    · have e2 : y = y' := by rw [hx'] at h1'; exact (KernelObject.tcb.inj (Option.some.inj h1')).symm
      subst e2
      obtain ⟨x0, hkx0, hsl⟩ := hR.tcb q hq
      have e3 : x0 = x := by rw [h1] at hkx0; exact (KernelObject.tcb.inj (Option.some.inj hkx0)).symm
      subst e3
      obtain ⟨c, ac, hc, hac, hca⟩ := hsl 2 (by decide)
      rw [tcbCnodeMap_two] at hac
      cases hac
      rcases h2 q hq with e | e
      · have hcc : c' = c := by
          have h3 : capAt mem' (slotOf q 2) = ok c' := hc'
          have h4 : capAt mem (slotOf q 2) = ok c := hc
          rw [e, h4] at h3; exact (ok_inj h3).symm
        subst hcc
        exact Or.inr ⟨x0, h1, by rw [hca.abs, hca'.abs], hb.symm⟩
      · left
        have h3 : capV mem' (slotOf q 2) = c' := capV_of_capAt hc'
        rw [hca'.abs, ← h3, e, absCap_null]
  · rcases hkc p with e | ⟨r, cs, cs', h1, -⟩ | ⟨x, y, h1, -⟩
    · rw [e]; exact h
    · rw [h] at h1; cases h1
    · rw [h] at h1; cases h1
  · rcases hkc p with e | ⟨r, cs, cs', -, h1⟩ | ⟨x, y, -, h1, -⟩
    · rw [← e]; exact h
    · rw [h] at h1; cases h1
    · rw [h] at h1; cases h1

/-- **The IPC frames' facts of one object step**: a TCB after was a TCB with
the same IPC frame and buffer address, and neither object is a non-device
data page (the IPC, scheduler and TCB code's per-object change relations,
`KChg`, `EChg`, `BChg`, …). -/
def ObjFrK (o o' : KernelObject) : Prop :=
  (∀ y, o' = .tcb y → ∃ x, o = .tcb x ∧ x.tcbIpcframe = y.tcbIpcframe ∧ x.tcbIpcBuffer = y.tcbIpcBuffer) ∧
    (∀ vms, o ≠ .archObj (.dataPage false vms)) ∧ (∀ vms, o' ≠ .archObj (.dataPage false vms))

/-- A TCB replaced by one with the same IPC frame and buffer address. -/
theorem objFrK_tcb {x y : Tcb} (h1 : y.tcbIpcframe = x.tcbIpcframe) (h2 : y.tcbIpcBuffer = x.tcbIpcBuffer) :
    ObjFrK (.tcb x) (.tcb y) := by
  unfold ObjFrK
  refine ⟨?_, ?_, ?_⟩
  · intro y' e; cases e; exact ⟨x, rfl, h1.symm, h2.symm⟩
  · intro vms e; cases e
  · intro vms e; cases e

/-- An object that is neither a TCB nor a data page replaced by another. -/
theorem objFrK_other {o o' : KernelObject} (h1 : ∀ y, o' ≠ .tcb y) (h2 : ∀ vms, o ≠ .archObj (.dataPage false vms))
    (h3 : ∀ vms, o' ≠ .archObj (.dataPage false vms)) : ObjFrK o o' := by
  unfold ObjFrK
  exact ⟨fun y e => absurd e (h1 y), h2, h3⟩

/-- **A step whose changed objects are `ObjFrK`** (the frame records'
`kh` shape: each object kept or changed by the record's relation `C`). -/
theorem of_chg {C : ObjRef → KernelObject → KernelObject → Prop}
    (kh : ∀ p, σ'.kheap p = σ.kheap p ∨ ∃ o o', σ.kheap p = some o ∧ σ'.kheap p = some o' ∧ C p o o')
    (hC : ∀ p o o', C p o o' → ObjFrK o o') : IpcFrKeep σ σ' := by
  refine ⟨fun t x' hx' => Or.inr ?_, fun p vms h => ?_, fun p vms h => ?_⟩
  · rcases kh t with e | ⟨o, o', h1, h2, hc⟩
    · exact ⟨x', by rw [← e]; exact hx', rfl, rfl⟩
    · rw [hx'] at h2; cases h2
      exact (hC t o _ hc).1 x' rfl |>.imp fun x ⟨a, b, c⟩ => ⟨by rw [h1, a], b, c⟩
  · rcases kh p with e | ⟨o, o', h1, h2, hc⟩
    · rw [e]; exact h
    · rw [h] at h1; cases h1; exact absurd rfl ((hC p _ o' hc).2.1 vms)
  · rcases kh p with e | ⟨o, o', h1, h2, hc⟩
    · rw [← e]; exact h
    · rw [h] at h2; cases h2; exact absurd rfl ((hC p o _ hc).2.2 vms)

end IpcFrKeep

variable {σ σ' : State Unit}

theorem _root_.Fl4Proofs.P3.Endp.ipcBufOf_null {b : Bool} {x : Tcb} (h : x.tcbIpcframe = .nullCap) :
    Endp.ipcBufOf b x = none := by
  unfold Endp.ipcBufOf; rw [h]

/-- A user frame across a step keeping the data pages. -/
theorem inUserFrame_keep (hpg : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
    σ'.kheap p = some (.archObj (.dataPage false vms))) {a : Word} (h : inUserFrame a σ) : inUserFrame a σ' :=
  let ⟨sz, hsz⟩ := h; ⟨sz, hpg _ _ hsz⟩

/-- **`IpcBufCapOK` across an `IpcFrKeep` step.** -/
theorem _root_.Fl4Proofs.P3.Endp.IpcBufCapOK.keep (h : Endp.IpcBufCapOK σ) (hK : IpcFrKeep σ σ') :
    Endp.IpcBufCapOK σ' := by
  intro t x' hx' dev p R mt vms md hf hR
  rcases hK.tcb t x' hx' with e | ⟨x, hx, e1, e2⟩
  · rw [e] at hf; cases hf
  · obtain ⟨h1, h2, h3, h4, h5⟩ := h t x hx dev p R mt vms md (by rw [e1]; exact hf) hR
    exact ⟨h1, h2, fun k hk => by rw [← e2]; exact inUserFrame_keep hK.page (h3 k hk), by rw [← e2]; exact h4, h5⟩

/-- **`B` covers the user frames** (module docstring). -/
def FrameCover (B : Set (U64 × Word)) (σ : State Unit) : Prop :=
  ∀ q vms, σ.kheap q = some (.archObj (.dataPage false vms)) → ∀ a : U64, q.toNat ≤ a.val →
    a.val < q.toNat + 2 ^ pageBitsForSize vms → a.val % 8 = 0 → (a, a.bv) ∈ B

variable {B B' : Set (U64 × Word)}

/-- **`FrameCover` across a step** (the data pages after are the ones
before, or new ones whose words are in the new `B`). -/
theorem FrameCover.step (h : FrameCover B σ) (hB : B ⊆ B')
    (hnew : ∀ q vms, σ'.kheap q = some (.archObj (.dataPage false vms)) →
      σ.kheap q = some (.archObj (.dataPage false vms)) ∨
      ∀ a : U64, q.toNat ≤ a.val → a.val < q.toNat + 2 ^ pageBitsForSize vms → a.val % 8 = 0 → (a, a.bv) ∈ B') :
    FrameCover B' σ' := by
  intro q vms hq a h1 h2 h3
  rcases hnew q vms hq with e | e
  · exact hB (h q vms e a h1 h2 h3)
  · exact e a h1 h2 h3

/-- `FrameCover` across a step adding no data page. -/
theorem FrameCover.keep (h : FrameCover B σ) (hB : B ⊆ B')
    (hpg : ∀ q vms, σ'.kheap q = some (.archObj (.dataPage false vms)) →
      σ.kheap q = some (.archObj (.dataPage false vms))) : FrameCover B' σ' :=
  h.step hB fun q vms hq => Or.inl (hpg q vms hq)

/-- `FrameCover` at the same objects. -/
theorem FrameCover.of_kheap (h : FrameCover B σ) (hk : σ'.kheap = σ.kheap) : FrameCover B σ' :=
  h.keep (fun _ h => h) fun q vms hq => by rw [← hk]; exact hq

/-- `FrameCover` across an `IpcFrKeep` step, at the same `B`. -/
theorem FrameCover.ipcFr (h : FrameCover B σ) (hK : IpcFrKeep σ σ') : FrameCover B σ' :=
  h.keep (fun _ h => h) hK.pback

end Spec

/-! ## `UtZero` (l4v `untyped_ranges_zero`) -/

section Zero
open Fl4Spec

/-- **The free parts of the RAM untyped caps are zero in the spec's memory**
(module docstring). -/
def UtZero (mem : U64 → U64) (G : MdbGhost) (σ : State Unit) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV mem x = .Untyped p sb fi false →
    ∀ a : Word, p.val + fi.val ≤ a.toNat → a.toNat < p.val + 2 ^ sb.val → σ.machineState.underlyingMemory a = 0

variable {mem mem' : U64 → U64} {G G' : MdbGhost} {σ σ' : State Unit}

/-- **`UtZero` across a step**: each RAM untyped cap after is one before with
a free index at most its own (the memory changing in its free part only to
zero), or its free part is zero after. -/
theorem UtZero.step (h : UtZero mem G σ)
    (hc : ∀ x ∈ G'.chains.flatten, ∀ p sb fi, capV mem' x = .Untyped p sb fi false →
      (∃ y ∈ G.chains.flatten, ∃ fi0 : U64, capV mem y = .Untyped p sb fi0 false ∧ fi0.val ≤ fi.val ∧
        ∀ a : Word, p.val + fi.val ≤ a.toNat → a.toNat < p.val + 2 ^ sb.val →
          σ'.machineState.underlyingMemory a = σ.machineState.underlyingMemory a ∨
          σ'.machineState.underlyingMemory a = 0) ∨
      ∀ a : Word, p.val + fi.val ≤ a.toNat → a.toNat < p.val + 2 ^ sb.val → σ'.machineState.underlyingMemory a = 0) :
    UtZero mem' G' σ' := by
  intro x hx p sb fi hcx a h1 h2
  rcases hc x hx p sb fi hcx with ⟨y, hy, fi0, hcy, hle, hum⟩ | hz
  · rcases hum a h1 h2 with e | e
    · rw [e]; exact h y hy p sb fi0 hcy a (by omega) h2
    · exact e
  · exact hz a h1 h2

/-- `UtZero` at the same caps and memory. -/
theorem UtZero.same (h : UtZero mem G σ) (hG : ∀ x ∈ G'.chains.flatten, x ∈ G.chains.flatten)
    (hcap : ∀ x ∈ G'.chains.flatten, capV mem' x = capV mem x)
    (hum : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory) : UtZero mem' G' σ' :=
  h.step fun x hx p sb fi hcx => Or.inl ⟨x, hG x hx, fi, by rw [← hcap x hx]; exact hcx, le_rfl,
    fun a _ _ => Or.inl (by rw [hum])⟩

/-- **The spec's memory changed only inside user frames** (each byte changed
lies in a non-device data page of the state before): what a step writing
only IPC-buffer and FPU-frame words keeps `UtZero` by (`UtZero.umIn`, with
`SpecFree`: a free part holds no object). -/
def UmIn (σ σ' : State Unit) : Prop :=
  ∀ a : Word, σ'.machineState.underlyingMemory a = σ.machineState.underlyingMemory a ∨ inUserFrame a σ

theorem UmIn.of_eq (h : σ'.machineState.underlyingMemory = σ.machineState.underlyingMemory) : UmIn σ σ' :=
  fun a => Or.inl (by rw [h])

theorem UmIn.refl (σ : State Unit) : UmIn σ σ := fun _ => Or.inl rfl

/-- `UmIn` across two steps, the middle state's data pages the first's. -/
theorem UmIn.trans {σ'' : State Unit} (h1 : UmIn σ σ') (h2 : UmIn σ' σ'')
    (hpb : ∀ p vms, σ'.kheap p = some (.archObj (.dataPage false vms)) →
      σ.kheap p = some (.archObj (.dataPage false vms))) : UmIn σ σ'' := by
  intro a
  rcases h2 a with e | ⟨sz, hz⟩
  · rw [e]; exact h1 a
  · exact Or.inr ⟨sz, hpb _ _ hz⟩

/-- **One word stored in a user frame** (each of its 8 bytes `inUserFrame`). -/
theorem UmIn.store {w v : Word} (hw : ∀ y : Word, y.toNat < 8 → inUserFrame (w + y) σ) :
    UmIn σ (Endp.setUm σ (Endp.storeMem σ.machineState.underlyingMemory w v)) := by
  intro a
  by_cases h : ∃ y : Word, y.toNat < 8 ∧ a = w + y
  · obtain ⟨y, hy, rfl⟩ := h; exact Or.inr (hw y hy)
  · refine Or.inl (Endp.storeMem_other _ w v a fun y hy e => h ⟨y, hy, e⟩)

/-- `UmIn` of a step whose memory is the state before's (`setUm` of the same
memory, or any step keeping it). -/
theorem UmIn.setUm_self (um : Word → Word8) (h : ∀ a, um a = σ.machineState.underlyingMemory a ∨ inUserFrame a σ) :
    UmIn σ (Endp.setUm σ um) := h

theorem umIn_bounds (a : Word) (sz : VMPageSize) :
    (a &&& ~~~(mask (pageBitsForSize sz) : BitVec 64)).toNat ≤ a.toNat ∧
      a.toNat < (a &&& ~~~(mask (pageBitsForSize sz) : BitVec 64)).toNat + 2 ^ pageBitsForSize sz := by
  have hn := Endp.and_not_mask_toNat a _ (Endp.pageBits_mem sz)
  have hpos : 0 < 2 ^ pageBitsForSize sz := by positivity
  rw [hn]
  exact ⟨Nat.div_mul_le_self _ _, Nat.lt_div_mul_add hpos⟩

/-- **`UtZero` across a step writing only user frames** (`UmIn`; the caps
and the free parts kept). -/
theorem UtZero.umIn (h : UtZero mem G σ) (hF : Sched.SpecFree mem G σ) (hu : UmIn σ σ') :
    UtZero mem G σ' := by
  intro x hx p sb fi hcx a h1 h2
  rcases hu a with e | ⟨sz, hz⟩
  · rw [e]; exact h x hx p sb fi hcx a h1 h2
  · obtain ⟨g1, g2⟩ := umIn_bounds a sz
    have hb : objBits (.archObj (.dataPage false sz)) = pageBitsForSize sz := rfl
    rcases hF x hx p sb fi hcx _ _ hz with (g | g) | ⟨g3, g4⟩ <;> rw [hb] at * <;> omega

/-- **`UtZero` across a step keeping the slots' caps, writing only user
frames** (`UtZero.same` and `UtZero.umIn`). -/
theorem UtZero.sameU (h : UtZero mem G σ) (hF : Sched.SpecFree mem G σ)
    (hG : ∀ x ∈ G'.chains.flatten, x ∈ G.chains.flatten)
    (hcap : ∀ x ∈ G'.chains.flatten, capV mem' x = capV mem x) (hu : UmIn σ σ') : UtZero mem' G' σ' :=
  (h.umIn hF hu).same hG hcap rfl

end Zero

end

end Fl4Proofs.P3
