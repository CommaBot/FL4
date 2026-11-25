/-
# P2 (line p2sl): `SlAccIn`'s P1 parts from the entry's P1 invariants

`SlPreB` already carries P1's invariants at the prefix state `X` (`hI`: `BXI`, with the endpoint
queues `EpsOK`, `BoundInv`, `XInv`, `SCsOK`; `hF`: m61's `FaultEntAt` under the trap arm's checks;
`hrecv`: the receiver is blocked on receive). With the entry's P1 sets being the typed heap's
(`SlSets` [J]: `K.heap = H`, `T = H.tcbs`, …, the convention of P1's own `sets` fields, e.g.
`UtRetypeP.sets`, P1/QueueUtRetype.lean; `layoutJ`'s `heap := H`, P2/OwnJAtZ.lean), they give:

* `nq_of`: `SlAccIn.nq`. The handler endpoint is a heap endpoint (`trap_ep`), so one of `EpsOK`'s
  objects; its ghost queue is `FaultEnt.hq`'s `dest :: rest` (`QueueRel.unique`); the next member
  `y` is a TCB of `T`, blocked on `ptr`, with `dest`'s state (`EpTy`), i.e. blocked on receive.
* `frp_of`: the heap part of `SlAccIn.frp` (`FaultEntAt`: `r ∈ Rp`).
* `dsc_of`: `SlAccIn.dsc` except the SC's `CORE` word: the receiver's SC is nonzero
  (`FaultEnt.hsc`), one of `Scs` (`ScExtra0.bound`), active (`BoundInv.sact`: a thread blocked on
  receive is `Sch`; `SCsOK.act`), and a heap SC of size `Z sc` (`SlSets`).
* `core_of` (line slco): the `CORE` word of the nonzero SC of a thread of `T` whose `AFFINITY` is
  this core is this core: P1's `ScAff` (`XInv.core_eq`, P1/ScAffInv.lean) at the prefix state,
  carried back to the entry by `lp_mem` (the thread's `SC` word, the SC's `CORE` word are not
  prefix words). `dco_of`: the trap arm's receiver (`schedulable_here`: `AFFINITY` is this core,
  `SC` nonzero, `here_facts`), formerly the premise `SlAccJ.dco`.

`slAccIn_of` assembles `SlAccIn` from `SlSets` and the remaining `SlAccJ`; `sl_pathObl_j` /
`sl_pathSide_j` are `sl_pathObl_lay` / `sl_pathSide_lay` with `SlAccIn` so replaced.

Premises: `SlSets` [J]; `SlAccJ` (`pool` [J], `frl` [P] fl4-sync's reply lock, `fbuf` /
`rbuf` [J]); the rest as `sl_pathObl_lay` / `sl_pathSide_lay`.
-/
import Fl4Proofs.P2.SlAccL
import Fl4Proofs.P1.ScAffInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-- **[J] The entry's P1 sets are the typed heap's**: the layout's heap is P1's typed heap `H`
(`layoutJ`, P2/OwnJAtZ.lean: `heap := H`) and the TCBs, replies, SCs (with their size
exponents) and notifications P1's invariants range over are `H`'s (P1's own `sets` convention,
`UtRetypeP.sets`, P1/QueueUtRetype.lean). -/
structure SlSets (K : KLayout) (T Rp Scs Nt : Set U64) (H : Heap) (Z : U64 → Nat) : Prop where
  heap : K.heap = H
  tcbs : T = H.tcbs
  replies : Rp = H.replies
  scs : Scs = H.scs
  bits : Z = H.scBits
  ntfns : Nt = H.ntfns

variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}

theorem SlSets.tcb (h : SlSets K T Rp Scs Nt H Z) {t : U64} (ht : t ∈ T) : K.heap t = some .tcb := by
  have h' : t ∈ H.tcbs := by rw [← h.tcbs]; exact ht
  rw [h.heap]
  exact h'

theorem SlSets.reply (h : SlSets K T Rp Scs Nt H Z) {r : U64} (hr : r ∈ Rp) : K.heap r = some .reply := by
  have h' : r ∈ H.replies := by rw [← h.replies]; exact hr
  rw [h.heap]
  exact h'

theorem SlSets.ntfn (h : SlSets K T Rp Scs Nt H Z) {x : U64} (hx : x ∈ Nt) : K.heap x = some .ntfn := by
  have h' : x ∈ H.ntfns := by rw [← h.ntfns]; exact hx
  rw [h.heap]
  exact h'

theorem SlSets.sc (h : SlSets K T Rp Scs Nt H Z) {c : U64} (hc : c ∈ Scs) : K.heap c = some (.sc (Z c)) := by
  have h' : c ∈ H.scs := by rw [← h.scs]; exact hc
  obtain ⟨z, hz⟩ := h'
  have e : Z c = z := by rw [h.bits]; simp only [Heap.scBits, hz]
  rw [h.heap, e]
  exact hz

theorem queued_recv {v : U64} (h : v = sched.TS_BLOCKED_ON_RECV) : QueuedState v := by
  unfold QueuedState
  rw [h, sched.TS_BLOCKED_ON_RECV.val_eq]
  exact Or.inl rfl

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

/-- **`SlAccIn.nq` from P1's endpoint queues** (`EpsOK`, `FaultEnt.hq`, `hrecv`). -/
theorem nq_of (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) (he : K.heap ptr = some .ep)
    (hne : (L.epQ X ptr).end ≠ dest) :
    K.heap (L.mem X (nextA .Ep dest)) = some .tcb ∧ QueuedState (L.mem X (stA (L.mem X (nextA .Ep dest)))) ∧
      L.mem X (blockA (L.mem X (nextA .Ep dest))) = ptr := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := E.hI a X a1 LP
  obtain ⟨Ee, EQ, w1, -, -, w4, -, -, -, k0, k3, -, -⟩ := hSQ.eps
  obtain ⟨-, rest, FE⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r hc
  have hpE : ptr ∈ Ee := (k0 ptr).2 (Or.inl (by rw [← hSe.heap]; exact he))
  have hEQ : EQ ptr = dest :: rest := (w1 ptr hpE).2.2.unique E.hT FE.hq
  cases rest with
  | nil => exact (hne (by simpa using FE.hq.last)).elim
  | cons y ys =>
    have hn : L.mem X (nextA .Ep dest) = y := ((Seg_cons _ _ _ _ _ _).1 FE.hq.seg).2.1
    have hyq : y ∈ EQ ptr := by rw [hEQ]; simp
    obtain ⟨-, hb, -⟩ := w4 ptr hpE y hyq
    have hst : L.mem X (stA y) = L.mem X (stA dest) := k3 ptr hpE y hyq dest (by rw [hEQ]; simp)
    rw [hn]
    exact ⟨hSe.tcb (FE.hq.mem y (by simp)), queued_recv (hst.trans (E.hrecv hS a X a1 LP hc)), hb⟩

/-- **The heap part of `SlAccIn.frp`** (`FaultEntAt`: the receiver's reply object is in `Rp`). -/
theorem frp_of (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) : K.heap r = some .reply :=
  hSe.reply ((E.hF hS a X a1 LP).2 ptr badge dest r hc).1

/-- **`SlAccIn.dsc` from P1's SC invariants**, given the SC's `CORE` word: the receiver's SC is
nonzero, one of `Scs`, active (the receiver is blocked on receive, so `Sch`), a heap SC. -/
theorem dsc_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r)
    (hco : L.mem s (fld (L.mem s (scA dest)) 16#u64) = L.cpu s) :
    ScHere (st := st) K Z Scs s (L.mem s (scA dest)) := by
  obtain ⟨-, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  obtain ⟨-, rest, FE⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r hc
  have hdT : dest ∈ T := FE.hq.mem dest (by simp)
  have hdt : K.heap dest = some .tcb := hSe.tcb hdT
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu hdt (by simp) (by simp) (by simp) (by simp))
  have hsc0 : L.mem X (scA dest) ≠ 0#u64 := FE.hsc
  have hScs : L.mem X (scA dest) ∈ Scs := (hXI.2.2.bound dest hdT hsc0).1
  have hBR : BlockedR (L.mem X (stA dest)) := Or.inl (Or.inr (Or.inl (E.hrecv hS a X a1 LP hc)))
  have hAc : L.mem X (scA dest) ∈ Ac :=
    hB.sact dest hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hBR))))) hsc0
  have hmx := (hSC.act _ hScs).1 hAc
  rw [eSc] at hScs hmx
  have hz := hSe.sc hScs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA (L.mem s (scA dest))) = L.mem s (maxA (L.mem s (scA dest))) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  refine ⟨hz, hScs, ?_, hco⟩
  show L.mem s (maxA (L.mem s (scA dest))) ≠ 0#u64
  rw [← em]
  exact hmx

/-- **An SC bound to a thread running here has this core in its `CORE` word** (line slco): P1's
`ScAff` at the prefix state (`XInv.core_eq`), carried back to the entry state (`lp_mem`). -/
theorem core_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    {t : U64} (htT : t ∈ T) (hs0 : L.mem X (scA t) ≠ 0#u64) (haf : L.mem X (affA t) = L.cpu s) :
    L.mem s (fld (L.mem s (scA t)) 16#u64) = L.cpu s := by
  obtain ⟨-, -, hXI, -, -⟩ := E.hI a X a1 LP
  have ht := hSe.tcb htT
  have eSc : L.mem X (scA t) = L.mem s (scA t) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
  have hce := hXI.core_eq htT hs0
  have hScs : L.mem X (scA t) ∈ Scs := (hXI.2.2.bound t htT hs0).1
  rw [eSc] at hce hScs
  have hz := hSe.sc hScs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE])
    (by simp [layout.sc.CORE])
  have ec : L.mem X (scCoreA (L.mem s (scA t))) = L.mem s (scCoreA (L.mem s (scA t))) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 hk hcp
      (by unfold scCoreA; rw [rm]; intro c h; cases h) (by unfold scCoreA; rw [rm]; intro h; cases h))
  have e16 : fld (L.mem s (scA t)) 16#u64 = scCoreA (L.mem s (scA t)) := by
    unfold fld scCoreA
    congr 1
    simp [layout.sc.CORE]
  rw [e16, ← ec, ← hce, haf]

/-- **`SlAccIn.dsc`'s `CORE` word** (formerly the premise `SlAccJ.dco`): the trap arm's receiver
passed `schedulable_here` at the prefix state (`AFFINITY` is this core, `SC` nonzero), so
`core_of`. -/
theorem dco_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    L.mem s (fld (L.mem s (scA dest)) 16#u64) = L.cpu s := by
  obtain ⟨-, rest, FE⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r hc
  have hdT : dest ∈ T := FE.hq.mem dest (by simp)
  have HF := here_facts (L := L) hc.here
  obtain ⟨-, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  exact core_of ar hA hX hSe E hk hcp LP hdT HF.sc (HF.aff.trans cX)

/-- **What stays of `SlAccIn`** once its P1 parts come from the entry's invariants (`slAccIn_of`). -/
structure SlAccJ (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] as `SlAccIn.pool`. -/
  pool : ∀ hi : U64, hi.val < 2048 → L.mem s (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
    Aligned (peAF (L.mem s (atAF K.ksb hi)) lo) ∧ region K (peAF (L.mem s (atAF K.ksb hi)) lo) = .none
  /-- [P] trap arm: fl4-sync holds the receiver's reply object's lock (`lock_object(m, r, ..)`,
  crates/fl4-sync/src/lib.rs l.695). -/
  frl : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → Locks s r
  /-- [J] as `SlAccIn.fbuf`. -/
  fbuf : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → ∀ rb, msg.lookup_ipc_buffer st X true dest = ok rb →
    BufW (fun b => Aligned b ∧ b ∈ K.user) rb
  /-- [J] as `SlAccIn.rbuf`. -/
  rbuf : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ buf,
    msg.lookup_ipc_buffer st X false (L.curW s) = ok buf → BufW (fun b => Aligned b ∧ b ∈ K.user) buf

/-- **`SlAccIn` from the entry's P1 invariants**, `SlSets` and `SlAccJ`. -/
theorem slAccIn_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K)
    (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Aj : SlAccJ (st := st) ar K Locks found s) : SlAccIn (st := st) ar K Locks Z Scs found s :=
  { pool := Aj.pool
    frp := fun hS a X a1 LP {_p _b _d _r} hc => ⟨frp_of ar hSe E hS LP hc, Aj.frl hS a X a1 LP hc⟩
    dsc := fun hS a X a1 LP {_p _b _d _r} hc => dsc_of ar hA hX hSe E Hh hS LP hc (dco_of ar hA hX hSe E Hh.ksb Hh.cpu hS LP hc)
    nq := fun hS a X a1 LP {_p _b _d _r} hc hne => nq_of ar hSe E hS LP hc
      (trap_ep ar hA E N (slThrIn_of hK hX (preAcc_of ar hX E Hh) E.hSt.1 N) hS LP hc).1 hne
    fbuf := Aj.fbuf
    rbuf := Aj.rbuf }

variable {p : SProg Bool}

/-- **`PathObl` of the syscall entry**: `sl_pathObl_lay` with `SlAccIn` from `slAccIn_of`
(`SlSets`, `SlAccJ`). -/
theorem sl_pathObl_j (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hSe : SlSets K T Rp Scs Nt H Z)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hH : ∀ s, P s → SlHere (st := st) K Z Scs found s)
    (hAj : ∀ s, P s → SlAccJ (st := st) ar K Locks found s) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl_lay ar hA hK hX hU hFp hz hm hPE hE hH
    (fun s hP => slAccIn_of ar hA hK hX hSe (hPE s hP) (hE s hP) (hH s hP) (hAj s hP))

/-- **`PathSide` of the syscall entry**: `sl_pathSide_lay` with `SlAccIn` from `slAccIn_of`. -/
theorem sl_pathSide_j (hS : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hSe : SlSets K T Rp Scs Nt H Z)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hH : ∀ s, P s → SlHere (st := st) K Z Scs found s)
    (hAj : ∀ s, P s → SlAccJ (st := st) ar K Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s) :
    PathSide st (fun m s a => syscall.handle_syscall_local m ar s a n found)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathSide_lay ar hS hA hK hX hU hFp hz hm hPE hE hH
    (fun s hP => slAccIn_of ar hA hK hX hSe (hPE s hP) (hE s hP) (hH s hP) (hAj s hP)) huf

end

end Fl4Proofs.P2.PathObl
