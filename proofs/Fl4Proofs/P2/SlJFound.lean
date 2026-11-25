/-
# P2 (line slhuf, gen 2): the syscall local path's `ep` / `hrp` from fl4-sync's `found` contract

`sl_pathsK` / `sl_pathsKU` take, per layout, `SlHereR` (its one field `ep` [J]:
`¬ SlTrap → K.heap found.2 = some .ep`) and `SlEntR` (`hrp` [J]:
`¬ SlTrap → K.heap found.1 = some .reply`, plus the lock facts `lep`, `lrp` [P]). Both are facts
about fl4-sync's `found`: in `local_syscall` (crates/fl4-sync/src/lib.rs l.710-760) a thread
whose `TRAP_SYSCALLS` flag is clear reaches `handle_syscall_local` only for `SysReplyRecv` and
only with `found = (r, ep)` returned by `fastpath::reply_caps(s, t)` at the entry state.

## The guard (checked)
`ep` / `hrp` are guarded by `¬ SlTrap` only. Their readers (`slThrIn_of` P2/SlLay, `slDecIn_of`
P2/SlDecL, the ReplyRecv arm of P2/SlAccL, `hthr_of` P2/SlEntJ, `usc_of` P2/SlHereJ) read them
on the `¬ SlTrap` arm only, but they build `SlThrIn` / `SlDecIn` / `SlHere` / `SlEnt` facts whose
`¬ SlTrap` fields carry no `n` guard: `n` is split only in the run inversion (`sl_acc_inv`,
P2/SlThr.lean). So restating `ep` / `hrp` with `n = SysReplyRecv` alone would need that guard
threaded through `SlEnt`, `SlHere`, `SlThrIn`, `SlDecIn` and their users (they take no `n`).
Instead the contract below carries fl4-sync's arm fact too (`SlSyncC.arm`), from which the
unguarded forms follow; `SlJAt.rrG` gives the guarded restatement itself.

## This file
* `jAtZ_lookupTyped`: at a `JAtZ` state, a cap the current thread's `lookup_slot` finds is typed
  (`lookup_slot_refines`: the slot is a CNode slot of `Z.th`; `JPlaced.typed`).
* `SlJAt.foundTyped`: at a bundle state, `reply_caps (cur) = ok (some found)` gives
  `K.heap found.1 = some .reply` and `K.heap found.2 = some .ep` (`reply_caps_some`,
  `RCaps.replyLookup` / `RCaps.capLookup`). This is also the form the VM ReplyRecv path's
  contract (`P1.rr_vm_local_same`'s `hfd`, no guard) has: `SlJAt.vmFound` gives `VmRRPre`'s
  `rptr ∈ Rp`, `H ep = some .ep` (and `VmRPre.hEp`) from it, at `H = K.heap`, `Rp = K.heap.replies`.
* `SlFoundRC n found s`: `P1.syscall_local_same`'s `hfd`, verbatim. `SlSyncC n found s`: the
  fl4-sync contract premise [P] (`fd` = `SlFoundRC`, `arm`: an untrapped thread runs the syscall
  local path only for `SysReplyRecv`).
* `SlJAt.rrG`: `ep` / `hrp` with the `n = SysReplyRecv` guard, from `SlFoundRC` alone.
  `SlJAt.hereR`, `SlJAt.entR`: `SlHereR`, `SlEntR` from `SlSyncC` (+ the lock facts `SlEntL`).
* `sl_pathsKF`, `sl_pathsKF_startAt`: `sl_pathsKU` / `sl_pathsKU_startAt` with `hHr`, `hEr`
  replaced by `hEl` (`SlEntL`: `lep`, `lrp` [P], unchanged) and `hC` (`SlSyncC` [P]).

## Premises
* `hC` [P] (`SlSyncC`): fl4-sync's call-site contract at every `Pre` state; `fd` is exactly
  `syscall_local_same`'s `hfd`.
* `hEl` [P]: the lock facts `lep`, `lrp`, as before. Others as `sl_pathsKU`.
-/
import Fl4Proofs.P2.SlJHuf
import Fl4Proofs.P3.StPostRRLink
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A cap the current thread's lookup finds is typed** at a joint-invariant state: the walk's
slot is a CNode slot of `Z.th` (`lookup_slot_refines`, `SlotOk`), whose cap is typed
(`JPlaced.typed`). -/
theorem jAtZ_lookupTyped {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop} {Z : XSets}
    {H : Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A'}
    {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {t c : U64} {r : cspace.Resolved} (et : sched.cur_thread st s = ok t)
    (h : cspace.lookup_slot st s t c = ok (core.result.Result.Ok r)) {cap : capability.Cap}
    (hc : obj.Slot.cap st r.slot s = ok cap) : CapTyped H (Heap.replies H) (Heap.ntfns H) cap := by
  have htcb := J.curW_tcb et
  have hR := J.xtop.rel.2.1.1
  have hV := J.xtop.rel.2.1.2.1
  have HL := lookup_slot_refines Z.th s σ hR hV t htcb c
  rw [h, WP.spec_ok] at HL
  obtain ⟨e, -, hrel, hok⟩ := HL
  cases e with
  | ok v =>
    obtain ⟨sl, rest⟩ := v
    obtain ⟨hsl, -⟩ := hrel
    obtain ⟨pp, hp, hth, -⟩ := hok
    have hca : capAt (L.mem s) (cslotAddr sl) = ok cap := by
      rw [← hsl, ← slot_cap_eq]; exact hc
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hT := hJ.typed _ (AbsSlot.isSlot ⟨pp, hp, Or.inl hth⟩)
    rwa [capV_of_capAt hca] at hT
  | error _ => exact hrel.elim

/-- **fl4-sync's `found` is a heap reply and a heap endpoint** at a bundle state, given that it
is what `reply_caps` returns for the current thread (module docstring). -/
theorem SlJAt.foundTyped {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {found : U64 × U64}
    (h : ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found)) :
    K.heap found.1 = some .reply ∧ K.heap found.2 = some .ep := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := B
  obtain ⟨rp, ep⟩ := found
  have et := cur_thread_ok (L := L) s
  have hR := reply_caps_some st (h _ et)
  obtain ⟨i, f1, g, -, hl, hc⟩ := hR.replyLookup
  obtain ⟨i1, f2, b0, b1, b3, b4, -, hl2, hc2⟩ := hR.capLookup
  exact ⟨(jAtZ_lookupTyped B.j et hl hc).2.2 _ g rfl,
    (jAtZ_lookupTyped B.j et hl2 hc2).1 _ _ _ _ _ _ rfl⟩

/-- **The VM ReplyRecv path's found-object facts from its contract**: `P1.rr_vm_local_same`'s
`hfd` (unguarded) gives `VmRRPre`'s `rptr ∈ Rp` and `H ep = some .ep` (P2/AccessVmRRD.lean) and
`VmRPre.hEp` (P2/AccessVmRRA.lean) at a bundle state, with `H = K.heap`, `Rp = K.heap.replies`. -/
theorem SlJAt.vmFound {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {rptr ep : U64}
    (hfd : ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some (rptr, ep))) :
    rptr ∈ Heap.replies K.heap ∧ K.heap ep = some .ep :=
  B.foundTyped hfd

variable (st) in
/-- **`P1.syscall_local_same`'s `hfd`**, verbatim: for an untrapped ReplyRecv, `found` is what
`reply_caps` returns for the current thread at the entry state. -/
def SlFoundRC (n : I64) (found : U64 × U64) (s : S) : Prop :=
  ∀ t f, sched.cur_thread st s = ok t → obj.Tcb.flags st t s = ok f →
    (f &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS) = 0#u64 → n = fl4_abi.syscall.SysReplyRecv →
    fastpath.reply_caps st s t = ok (some found)

variable (st) in
/-- **The fl4-sync contract of the syscall local path** [P] (`local_syscall`,
crates/fl4-sync/src/lib.rs l.696-760, before `handle_syscall_local`). -/
structure SlSyncC (n : I64) (found : U64 × U64) (s : S) : Prop where
  /-- [P] `found` is `reply_caps` of the current thread (an untrapped ReplyRecv; l.710-713). -/
  fd : SlFoundRC st n found s
  /-- [P] an untrapped thread reaches `handle_syscall_local` only for `SysReplyRecv`
  (l.709; other numbers take the invocation / timer / VM / I/O-port local paths). -/
  arm : ¬ SlTrap st s → n = fl4_abi.syscall.SysReplyRecv

/-- `SlFoundRC` on the untrapped ReplyRecv arm, in `SlTrap` terms: the unguarded contract
(`P1.rr_vm_local_same`'s `hfd` form). -/
theorem SlFoundRC.rc {n : I64} {found : U64 × U64} {s : S} (h : SlFoundRC st n found s)
    (hS : ¬ SlTrap st s) (hn : n = fl4_abi.syscall.SysReplyRecv) :
    ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found) := by
  intro t et
  have et' : t = L.curW s := by rw [cur_thread_ok] at et; exact (ok_inj_ff et).symm
  subst et'
  refine h _ _ et (flags_mem (L := L) s _) ?_ hn
  by_contra hne
  exact hS ⟨_, flags_mem (L := L) s _, by simp [bne_iff_ne, hne]⟩

/-- **`ep` / `hrp` with the `n = SysReplyRecv` guard** (the restatement), from `SlFoundRC`. -/
theorem SlJAt.rrG {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {n : I64} {found : U64 × U64}
    (h : SlFoundRC st n found s) :
    ¬ SlTrap st s → n = fl4_abi.syscall.SysReplyRecv →
      K.heap found.1 = some .reply ∧ K.heap found.2 = some .ep :=
  fun hS hn => B.foundTyped (h.rc hS hn)

/-- **`SlHereR` from the contract.** -/
theorem SlJAt.hereR {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {n : I64} {found : U64 × U64}
    (C : SlSyncC st n found s) : SlHereR (st := st) K found s :=
  ⟨fun hS => (B.rrG C.fd hS (C.arm hS)).2⟩

/-- **The lock facts of `SlEntR`** [P] (`lep`, `lrp` as there). -/
structure SlEntL (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [P] as `SlEnt.lep`. -/
  lep : SlTrap st s → IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    Locks s (resPtr (obj.Slot.cap st (fhA (L := L) s) s))
  /-- [P] as `SlEnt.lrp`. -/
  lrp : ¬ SlTrap st s → Locks s found.1

/-- **`SlEntR` from the contract and the lock facts.** -/
theorem SlJAt.entR {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {Locks : S → U64 → Prop} {n : I64}
    {found : U64 × U64} (C : SlSyncC st n found s) (E : SlEntL (st := st) K Locks found s) :
    SlEntR (st := st) K Locks found s :=
  ⟨fun hS => (B.rrG C.fd hS (C.arm hS)).1, E.lep, E.lrp⟩

end

/-! ## The local path with `ep` / `hrp` replaced by the contract -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`sl_pathsKU` with `hHr` / `hEr` replaced** by the fl4-sync contract `hC` [P] (`SlSyncC`)
and the lock facts `hEl` [P] (`SlEntL`). Other premises as `sl_pathsKU`. -/
noncomputable def sl_pathsKF (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEl : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntL (st := st) K Locks found s)
    (hC : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlSyncC st n found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKU (Locks := Locks) ar hSt hA hm a0 Q hPE
    (fun K m s hJ hq => hJ.entR (hC K m s hJ hq) (hEl K m s hJ hq))
    (fun K m s hJ hq => hJ.hereR (hC K m s hJ hq)) hAr hQ hlk hpz

/-- **`StartAt` for `sl_pathsKF`** (`sl_pathsKU_startAt` with `hHr` / `hEr` replaced). -/
theorem sl_pathsKF_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (Q : KLayout → (U64 → U64) → S → Prop)
    (hPE : ∀ K m s, SlJAt (L := L) K s → Q K m s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEl : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlEntL (st := st) K Locks found s)
    (hC : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlSyncC st n found s)
    (hAr : ∀ K m s, SlJAt (L := L) K s → Q K m s → SlAccR (st := st) ar K Locks found s)
    (hQ : ∀ K m s b v, SlJAt (L := L) K s → Q K m s → b ∈ K.user → Aligned b → Q K m (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ Q K m s) (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : Q K m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKF (Locks := Locks) ar hSt hA hm a0 Q hPE hEl hC hAr hQ hlk hpz () K m hK hU) c hs μ
      ((sl_pathsKF (Locks := Locks) ar hSt hA hm a0 Q hPE hEl hC hAr hQ hlk hpz () K m hK hU).body σ a) :=
  sl_pathsKU_startAt ar hSt hA hm a0 Q hPE _ _ hAr hQ hlk hpz K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl
