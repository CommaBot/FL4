/-
# P2 (line p2sl): `SlEnt.hthr` from the entry's P1 invariants

`hthr_of`: the live decided thread is a heap TCB, at the prefix state of a prefix run (`lp_ex`),
from `SlSets` [J] and `SlEnt`'s other fields:

* trap arm: the handler endpoint (a heap endpoint, `SlEnt.hep`) is in `RECV`; it is one of
  `EpsOK`'s objects, whose empty queue would have state `0` (`EpTy`), so its queue's head (the
  decided thread) is a member, a TCB of `T`;
* ReplyRecv arm: fl4-sync's reply object (a heap reply, `SlEnt.hrp`) names a thread, which is in
  `T` (`ReplyInv.back`).

`SlEntJ` is `SlEnt` without `hthr`; `slEnt_of`; `sl_pathObl_e` / `sl_pathSide_e` are
`sl_pathObl_h` / `sl_pathSide_h` with `SlEnt` so replaced.

Premises: as `sl_pathObl_h` / `sl_pathSide_h`, with `SlEntJ` (`dsR`, `hep`, `hrp` [J], `lep`,
`lrp` [P]) for `SlEnt`.
-/
import Fl4Proofs.P2.SlHereJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **`SlEnt` without `hthr`** (each field as in `SlEnt`). -/
structure SlEntJ (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] as `SlEnt.dsR`. -/
  dsR : ∀ x, SlDS (L := L) s x → (∃ c, region K x = .node c) ∨ region K x = .tcb (L.curW s)
  /-- [J] as `SlEnt.hep`. -/
  hep : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    K.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep
  /-- [J] as `SlEnt.hrp`. -/
  hrp : ¬ SlTrap st s → K.heap found.1 = some .reply
  /-- [P] as `SlEnt.lep`. -/
  lep : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    Locks s (resPtr (obj.Slot.cap st (fhA (L := L) s) s))
  /-- [P] as `SlEnt.lrp`. -/
  lrp : ¬ SlTrap st s → Locks s found.1

theorem SlEntJ.ent {found : U64 × U64} {s : S} (N : SlEntJ (st := st) K Locks found s)
    (hthr : SlLive st found.1 s → K.heap (slThr st found.1 s) = some .tcb) : SlEnt (st := st) K Locks found s :=
  ⟨N.dsR, N.hep, N.hrp, hthr, N.lep, N.lrp⟩

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

theorem ep_recv_ne0 : obj.EP_RECV ≠ 0#u64 := fun h => by
  have h' := congrArg (fun x : U64 => x.val) h
  simp at h'

/-- A word in an object region is not a prefix word (`not_slDS_of_obj` from `dsR` alone). -/
theorem SlEntJ.nobj {s : S} (N : SlEntJ (st := st) K Locks found s) {x p : U64}
    (h : region K x = .obj p) : ¬ SlDS (L := L) s x := fun hx => by
  rcases N.dsR x hx with ⟨c, e⟩ | e <;> rw [h] at e <;> cases e

/-- **`SlEnt.hthr` from P1's endpoint queues and reply invariant.** -/
theorem hthr_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEntJ (st := st) K Locks found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (lv : SlLive st found.1 s) : K.heap (slThr st found.1 s) = some .tcb := by
  obtain ⟨⟨Q, R, hSQ⟩, -, hXI, -, -⟩ := E.hI a X a1 LP
  by_cases hS : SlTrap st s
  · unfold SlLive at lv
    rw [if_pos hS] at lv
    obtain ⟨hE, hst⟩ := lv
    have he := N.hep hS hE
    have et : slThr st found.1 s = L.mem s (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) := by
      unfold slThr
      rw [if_pos hS, if_pos hE]
    rw [et]
    obtain ⟨ptr, hp⟩ : ∃ p, resPtr (obj.Slot.cap st (fhA (L := L) s) s) = p := ⟨_, rfl⟩
    rw [hp] at he hst ⊢
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s ptr)] at hst
    have hs2 : L.epState s ptr = obj.EP_RECV := ok_inj_ff hst
    obtain ⟨r1, a1h⟩ := hX.epW _ he layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
    obtain ⟨r2, a2h⟩ := hX.epW _ he layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])
    have eH : L.mem X (epHeadA ptr) = L.mem s (epHeadA ptr) := lp_mem ar hA E.hT E.hN E.hcT LP a1h (N.nobj r1)
    have eTS : L.mem X (epTSA ptr) = L.mem s (epTSA ptr) := lp_mem ar hA E.hT E.hN E.hcT LP a2h (N.nobj r2)
    have hsX : L.epState X ptr = obj.EP_RECV := by
      unfold LawfulStore.epState
      rw [eTS]
      exact hs2
    obtain ⟨Ee, EQ, w1, -, -, -, -, -, -, k0, -, -, k5⟩ := hSQ.eps
    have hpE : ptr ∈ Ee := (k0 ptr).2 (Or.inl (by rw [← hSe.heap]; exact he))
    have hq := (w1 ptr hpE).2.2
    have hhd : (L.epQ X ptr).head = (EQ ptr).headD 0#u64 := hq.head
    rw [← eH]
    cases hl : EQ ptr with
    | nil =>
      have h0 := (k5 ptr hpE hl).1 (by rw [← hSe.heap]; exact he)
      exact absurd (hsX.symm.trans h0) ep_recv_ne0
    | cons y ys =>
      rw [hl] at hhd
      have e : L.mem X (epHeadA ptr) = y := hhd
      rw [e]
      exact hSe.tcb (hq.mem y (by rw [hl]; simp))
  · have et : slThr st found.1 s = L.mem s (rTcbA found.1) := by unfold slThr; rw [if_neg hS]
    have lv' : L.mem s (rTcbA found.1) ≠ 0#u64 := by unfold SlLive at lv; rw [if_neg hS] at lv; exact lv
    rw [et]
    have hrp := N.hrp hS
    have hRp : found.1 ∈ Rp := by
      rw [hSe.replies]
      show H found.1 = some .reply
      rw [← hSe.heap]
      exact hrp
    obtain ⟨r1, a1h⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
    have eT : L.mem X (rTcbA found.1) = L.mem s (rTcbA found.1) :=
      lp_mem ar hA E.hT E.hN E.hcT LP a1h (N.nobj r1)
    have h0X : L.mem X (rTcbA found.1) ≠ 0#u64 := by rw [eT]; exact lv'
    obtain ⟨-, hT', -, -⟩ := hXI.2.1.back _ hRp h0X
    rw [eT] at hT'
    exact hSe.tcb hT'

/-- **`SlEnt` from `SlEntJ` and the entry's P1 invariants** (the prefix run from `a0`). -/
theorem slEnt_of (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hX : RegionOKX K)
    (hSe : SlSets K T Rp Scs Nt H Z) (a0 : A) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEntJ (st := st) K Locks found s) : SlEnt (st := st) K Locks found s := by
  obtain ⟨X, a1, LP⟩ := lp_ex ar hSt hA E.hT E.hcT a0
  exact N.ent (hthr_of ar hA hX hSe E N LP)

variable {p : SProg Bool}

/-- **`PathObl` of the syscall entry**: `sl_pathObl_h` with `SlEnt` from `slEnt_of` (`SlEntJ`). -/
theorem sl_pathObl_e (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hSe : SlSets K T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hEj : ∀ s, P s → SlEntJ (st := st) K Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K Locks found s) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl_h ar hSt hA hK hX hU hFp hz hm hSe hUu a0 hPE
    (fun s hP => slEnt_of ar hSt hA hX hSe a0 (hPE s hP) (hEj s hP)) hHj hAk

/-- **`PathSide` of the syscall entry**: `sl_pathSide_h` with `SlEnt` from `slEnt_of`. -/
theorem sl_pathSide_e (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hSe : SlSets K T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hEj : ∀ s, P s → SlEntJ (st := st) K Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathSide_h ar hSt hA hK hX hU hFp hz hm hSe hUu a0 hPE
    (fun s hP => slEnt_of ar hSt hA hX hSe a0 (hPE s hP) (hEj s hP)) hHj hAk huf

end

end Fl4Proofs.P2.PathObl
