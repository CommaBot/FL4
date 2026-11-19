/-
P3 (DESIGN.md §9), IPC: **the IPC-buffer facts as carried invariants**,
phase 1 (handoff/glob.md): the frame lemmas toward removing JEntryGlob's
∀-state premises `ipcBufOK`, `bufCover`, `bufPlaced` [J] (each quantifies
over every `XTopAt` state of the typed heap, false in general).

* `bufPlaced_of`: `Vs.BufPlaced` from `XTopAt` with `KsApart`, `IPlaced`,
  the SCs 8-aligned and the buffer words off the nodes below core `Z.c`
  (`hlow`): `ntfn` by `IPlaced.nb`, `far` by `KsApart.buf`, `hlow` and
  `EpSchedApart.node` (a buffer word is an `EFoot` word), `sc` by
  `EpSchedApart.sc` (a buffer word is an `EWrite` word). So `BufPlaced`
  needs no field of its own: `JAtZ.bufPlacedLow` at any `JAtZ` (given
  `hlow`), `JAtZ.bufPlaced0` on core 0 (`hlow` vacuous).
* `IpcFrKeep σ σ'`: a spec step keeping what `IpcBufCapOK` and `BufCover`
  read: every TCB after has a null IPC-frame cap or was a TCB with the same
  `tcb_ipcframe` and `tcb_ipc_buffer`, and every non-device data page is
  kept. `refl`, `trans`, `of_kheap`, `of_epStep`, `of_updTcb` (a TCB update
  keeping both fields), `of_updObj` (an object written over no data page,
  a TCB written only with a null frame), `of_fresh` (objects added at free
  addresses, the TCBs with null frames: the retypes), `of_nullFrame` (a
  TCB's frame slot emptied: the deletions).
* `Endp.IpcBufCapOK.keep`, `Endp.BufCover.keep` (with the sets: `T'`'s
  TCBs in `T` or with a null frame, `B ⊆ B'`), `Endp.BufMap.mono`.
* `Endp.IpcBufCapOK.setFrame`, `Endp.BufCover.setFrame`: a TCB's IPC frame
  and buffer address replaced, given the new pair's facts: the obligations
  of the IPC-buffer install (SetIPCBuffer, Configure).
-/
import Fl4Proofs.P3.JointAt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

noncomputable section

/-! ## `BufPlaced` from the joint invariant -/

section Placed
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

theorem nodeBase_val (s : S) (c : U64) : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl

/-- **`BufPlaced` from `XTopAt`** (module docstring). -/
theorem bufPlaced_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) (hks : KsApart Z.N Z.T Z.E Z.R Z.B (L.ksb s))
    (hip : IPlaced Z.N Z.T Z.E Z.R Z.B)
    (hsc : ∀ sc ∈ Z.C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → sc.val % 8 = 0)
    (hlow : ∀ wp ∈ Z.B, wp.1.val < L.nodeBase s 0#u64 ∨ L.nodeBase s Z.c ≤ wp.1.val) :
    Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ := by
  have hn0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by
    rw [nodeBase_val]; simp
  refine ⟨fun wp hw n hn => ?_, fun wp hw => ?_, fun wp hw sc hsc' x n hk => ?_⟩
  · have h1 := hip.nb n hn wp hw
    have h2 := (hip.e.balign wp hw).1
    have h3 := (hip.n.ntfn n hn).align
    omega
  · rcases hks.buf wp hw with h | h
    · exact Or.inl h
    · right
      rcases hlow wp hw with h' | h'
      · rw [hn0] at h'; omega
      · by_contra hc
        exact hX.esa.node wp.1 h' (by omega) (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)))
  · have h2 := (hip.e.balign wp hw).1
    have h3 := hsc sc hsc' x n hk
    by_contra hc
    exact hX.esa.sc sc hsc' x n hk wp.1 ⟨by omega, by omega⟩ (Or.inr (Or.inr (Or.inr ⟨wp, hw, rfl⟩)))

variable {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- The SCs of `Z.C` are 8-aligned (`H`'s SC objects, `JPlaced.sc`, `HeapOK.align`). -/
theorem JAtZ.scAlign8 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ sc ∈ Z.C, ∀ x n, σ.kheap sc.bv = some (.schedContext x n) → sc.val % 8 = 0 := by
  intro sc hsc x n hk
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hq := (hJ.sc sc x n (J.c0 sc hsc) hk).2
  have hal := J.kern.heap.align sc _ hq
  simp only [P1.HKind.bits] at hal
  have hd : 8 ∣ 2 ^ (n + Fl4Spec.minSchedContextBits) :=
    Nat.pow_dvd_pow 2 (by simp only [Fl4Spec.minSchedContextBits]; omega : 3 ≤ n + Fl4Spec.minSchedContextBits)
  rw [← Nat.mod_mod_of_dvd sc.val hd, hal]

/-- **`BufPlaced` at a `JAtZ`**, the buffer words off the nodes below core
`Z.c`. -/
theorem JAtZ.bufPlacedLow (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hlow : ∀ wp ∈ Z.B, wp.1.val < L.nodeBase s 0#u64 ∨ L.nodeBase s Z.c ≤ wp.1.val) :
    Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ :=
  bufPlaced_of J.xtop J.ks J.ip J.scAlign8 hlow

/-- **`BufPlaced` at a `JAtZ` on core 0.** -/
theorem JAtZ.bufPlaced0 (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hc0 : Z.c = 0#u64) :
    Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ :=
  J.bufPlacedLow fun _ _ => by rw [hc0]; omega

end Placed

/-! ## The spec steps keeping the IPC-buffer facts -/

section Spec
open Fl4Spec

/-- **A step keeping what `IpcBufCapOK` and `BufCover` read** (module
docstring). -/
structure IpcFrKeep (σ σ' : State Unit) : Prop where
  tcb : ∀ t x', σ'.kheap t = some (.tcb x') → x'.tcbIpcframe = .nullCap ∨
    ∃ x, σ.kheap t = some (.tcb x) ∧ x.tcbIpcframe = x'.tcbIpcframe ∧ x.tcbIpcBuffer = x'.tcbIpcBuffer
  page : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
    σ'.kheap p = some (.archObj (.dataPage false vms))

namespace IpcFrKeep
variable {σ σ' σ'' : State Unit}

theorem refl (σ : State Unit) : IpcFrKeep σ σ := ⟨fun _ x h => Or.inr ⟨x, h, rfl, rfl⟩, fun _ _ h => h⟩

theorem trans (h1 : IpcFrKeep σ σ') (h2 : IpcFrKeep σ' σ'') : IpcFrKeep σ σ'' := by
  refine ⟨fun t x3 h3 => ?_, fun p vms h => h2.page p vms (h1.page p vms h)⟩
  rcases h2.tcb t x3 h3 with e | ⟨x2, h2', e1, e2⟩
  · exact Or.inl e
  · rcases h1.tcb t x2 h2' with e | ⟨x1, h1', f1, f2⟩
    · exact Or.inl (by rw [← e1]; exact e)
    · exact Or.inr ⟨x1, h1', f1.trans e1, f2.trans e2⟩

theorem of_kheap (hk : σ'.kheap = σ.kheap) : IpcFrKeep σ σ' :=
  ⟨fun _ x h => Or.inr ⟨x, by rw [← hk]; exact h, rfl, rfl⟩, fun _ _ h => by rw [hk]; exact h⟩

/-- An `EpStep` (the endpoint, reply and TCB-state code; as XTopJointXferB's
`ipcBufCapOK_epStep`). -/
theorem of_epStep (hs : Endp.EpStep σ σ') : IpcFrKeep σ σ' := by
  obtain ⟨-, -, hk⟩ := hs
  refine ⟨fun t x' hx' => Or.inr ?_, fun p vms h => ?_⟩
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

/-- A TCB written keeping its IPC frame and buffer address. -/
theorem of_updTcb {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x)) (h1 : y.tcbIpcframe = x.tcbIpcframe)
    (h2 : y.tcbIpcBuffer = x.tcbIpcBuffer) : IpcFrKeep σ (Notif.updK σ t (.tcb y)) := by
  refine ⟨fun q x' hq => Or.inr ?_, fun p vms h => ?_⟩
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

/-- An object written over no non-device data page, a TCB only with a null
IPC frame (a new TCB: the retype's `default_tcb`). -/
theorem of_updObj {p : ObjRef} {o : KernelObject}
    (hp : ∀ vms, σ.kheap p ≠ some (.archObj (.dataPage false vms)))
    (ho : ∀ x, o = .tcb x → x.tcbIpcframe = .nullCap) : IpcFrKeep σ (Notif.updK σ p o) := by
  refine ⟨fun q x' hq => ?_, fun q vms h => ?_⟩
  · by_cases e : q = p
    · subst e
      simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq] at hq
      exact Or.inl (ho x' hq)
    · simp only [Notif.updK_kheap, Function.update_of_ne e] at hq
      exact Or.inr ⟨x', hq, rfl, rfl⟩
  · by_cases e : q = p
    · subst e; exact absurd h (hp vms)
    · simp only [Notif.updK_kheap, Function.update_of_ne e]; exact h

/-- **Objects added at free addresses**, the new TCBs with null IPC frames
(the retypes: every object kept or new where there was none). -/
theorem of_fresh (h : ∀ p, σ'.kheap p = σ.kheap p ∨
    (σ.kheap p = none ∧ ∀ x, σ'.kheap p = some (.tcb x) → x.tcbIpcframe = .nullCap)) : IpcFrKeep σ σ' := by
  refine ⟨fun q x' hq => ?_, fun q vms hq => ?_⟩
  · rcases h q with e | ⟨-, hn⟩
    · exact Or.inr ⟨x', by rw [← e]; exact hq, rfl, rfl⟩
    · exact Or.inl (hn x' hq)
  · rcases h q with e | ⟨e, -⟩
    · rw [e]; exact hq
    · rw [hq] at e; cases e

/-- A TCB's IPC-frame slot emptied (a deletion of that slot's cap). -/
theorem of_nullFrame {t : ObjRef} {x y : Tcb} (hk : σ.kheap t = some (.tcb x)) (h1 : y.tcbIpcframe = .nullCap) :
    IpcFrKeep σ (Notif.updK σ t (.tcb y)) :=
  of_updObj (fun vms e => by rw [hk] at e; cases e) (fun x' e => by cases e; exact h1)

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

theorem _root_.Fl4Proofs.P3.Endp.BufMap.mono {B B' : Set (U64 × Word)} {w : U64} {p : Word}
    (h : Endp.BufMap B w p) (hB : B ⊆ B') : Endp.BufMap B' w p :=
  fun i hi => hB (h i hi)

/-- **`BufCover` across an `IpcFrKeep` step**, the TCB set's new members
with null frames, the buffer words growing. -/
theorem _root_.Fl4Proofs.P3.Endp.BufCover.keep {T T' : Set U64} {B B' : Set (U64 × Word)}
    (h : Endp.BufCover T B σ) (hK : IpcFrKeep σ σ')
    (hT : ∀ t ∈ T', t ∈ T ∨ ∀ x, σ'.kheap t.bv = some (.tcb x) → x.tcbIpcframe = .nullCap) (hB : B ⊆ B') :
    Endp.BufCover T' B' σ' := by
  intro t ht x' b p hx' hp w hw
  have hnn : x'.tcbIpcframe ≠ .nullCap := fun e => by rw [Endp.ipcBufOf_null e] at hp; cases hp
  rcases hK.tcb t.bv x' hx' with e | ⟨x, hx, e1, e2⟩
  · exact absurd e hnn
  · have hp' : Endp.ipcBufOf b x = some p := by
      unfold Endp.ipcBufOf at hp ⊢; rw [e1, e2]; exact hp
    rcases hT t ht with ht0 | hn
    · exact (h t ht0 x b p hx hp' w hw).mono hB
    · exact absurd (hn x' hx') hnn

/-- **`IpcBufCapOK` with a TCB's IPC frame and buffer address replaced**,
given the new pair's facts (the install's obligation: l4v
`check_valid_ipc_buffer` and `valid_cap` of the new cap). -/
theorem _root_.Fl4Proofs.P3.Endp.IpcBufCapOK.setFrame (h : Endp.IpcBufCapOK σ) {t : ObjRef} {x y : Tcb}
    (hk : σ.kheap t = some (.tcb x))
    (hy : ∀ dev p R mt vms md, y.tcbIpcframe = .archObjectCap (.pageCap dev p R mt vms md) → vmReadOnly ⊆ R →
      dev = false ∧ p ≠ 0 ∧
        (∀ k, k < 128 → inUserFrame (Endp.bufAddr (p + (y.tcbIpcBuffer &&& mask (pageBitsForSize vms))) k) σ) ∧
        y.tcbIpcBuffer.toNat % 1024 = 0 ∧
        p.toNat % 2 ^ pageBitsForSize vms = 0) :
    Endp.IpcBufCapOK (Notif.updK σ t (.tcb y)) := by
  have hpg : ∀ p vms, σ.kheap p = some (.archObj (.dataPage false vms)) →
      (Notif.updK σ t (.tcb y)).kheap p = some (.archObj (.dataPage false vms)) := fun p vms hp => by
    by_cases e : p = t
    · subst e; rw [hk] at hp; cases hp
    · simp only [Notif.updK_kheap, Function.update_of_ne e]; exact hp
  intro q x' hq dev p R mt vms md hf hR
  by_cases e : q = t
  · subst e
    simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hq
    subst hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := hy dev p R mt vms md hf hR
    exact ⟨h1, h2, fun k hk => inUserFrame_keep hpg (h3 k hk), h4, h5⟩
  · simp only [Notif.updK_kheap, Function.update_of_ne e] at hq
    obtain ⟨h1, h2, h3, h4, h5⟩ := h q x' hq dev p R mt vms md hf hR
    exact ⟨h1, h2, fun k hk => inUserFrame_keep hpg (h3 k hk), h4, h5⟩

/-- **`BufCover` with a TCB's IPC frame and buffer address replaced**, given
the new buffer mapped in `B` (the install's obligation: the new buffer's
words related, so in `B`). -/
theorem _root_.Fl4Proofs.P3.Endp.BufCover.setFrame {T : Set U64} {B : Set (U64 × Word)}
    (h : Endp.BufCover T B σ) {t : ObjRef} {y : Tcb}
    (hy : ∀ b p, Endp.ipcBufOf b y = some p → ∀ w : U64, w.bv = p → Endp.BufMap B w p) :
    Endp.BufCover T B (Notif.updK σ t (.tcb y)) := by
  intro q hq x' b p hx' hp w hw
  by_cases e : q.bv = t
  · rw [e] at hx'
    simp only [Notif.updK_kheap, Function.update_self, Option.some.injEq, KernelObject.tcb.injEq] at hx'
    subst hx'
    exact hy b p hp w hw
  · simp only [Notif.updK_kheap, Function.update_of_ne e] at hx'
    exact h q hq x' b p hx' hp w hw

end Spec

end

end Fl4Proofs.P3
