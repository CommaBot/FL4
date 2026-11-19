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
* `IpcFrKeep` and `Endp.IpcBufCapOK.keep` now live upstream of `JAtZ`, in
  BufDefs.
* `Endp.BufCover.keep` (with the sets: `T'`'s
  TCBs in `T` or with a null frame, `B ⊆ B'`), `Endp.BufMap.mono`.
* `Endp.IpcBufCapOK.setFrame`, `Endp.BufCover.setFrame`: a TCB's IPC frame
  and buffer address replaced, given the new pair's facts: the obligations
  of the IPC-buffer install (SetIPCBuffer, Configure).
-/
import Fl4Proofs.P3.JointAt
import Fl4Proofs.P3.BufDefs
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

/-- **`BufPlaced` at every `JAtZ`** (no premise): `hlow` from `JAtZ.nodeB`
at the node slots below core `Z.c` (`Z.c ∈ Cs`, `JKern.csLt`). -/
theorem JAtZ.bufPlacedJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    Vs.BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ := by
  refine J.bufPlacedLow fun wp hw => ?_
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hc64 := J.kern.csLt Z.c hcC
  have hn0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by rw [nodeBase_val]; simp
  rw [hn0, nodeBase_val]
  by_contra hne
  have h1 : (L.ksb s).val + 13568 ≤ wp.1.val := by omega
  have h2 : wp.1.val < (L.ksb s).val + 13568 + Z.c.val * 4288 := by omega
  set k := (wp.1.val - ((L.ksb s).val + 13568)) / 4288 with hk
  have hkc : k < Z.c.val := by
    rw [hk, Nat.div_lt_iff_lt_mul (by norm_num)]; rw [Nat.mul_comm] at h2; omega
  obtain ⟨c', hc'⟩ : ∃ c' : U64, c'.val = k := ⟨⟨BitVec.ofNat 64 k⟩, by
    show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)⟩
  have e := J.nodeB wp hw c' (by omega)
  rw [nodeBase_val, hc'] at e
  have hlo : k * 4288 ≤ wp.1.val - ((L.ksb s).val + 13568) := Nat.div_mul_le_self _ _
  have hhi : wp.1.val - ((L.ksb s).val + 13568) < k * 4288 + 4288 := by
    rw [hk]; exact Nat.lt_div_mul_add (by norm_num)
  omega

end Placed

/-! ## The spec steps keeping the IPC-buffer facts -/

section Spec
open Fl4Spec

variable {σ σ' : State Unit}

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
