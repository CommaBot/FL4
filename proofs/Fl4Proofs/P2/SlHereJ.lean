/-
# P2 (line p2sl): `SlHere`'s P1 parts from the entry's P1 invariants

`SlHere` is stated at the entry state `s`; `SlPreB.hI` gives P1's invariants (`BXI`) at the
prefix state `X` of any prefix run. The prefix always runs (`lp_ex`: `StoreTotal` [P],
`ArchTotal`, P0's `update_timestamp`), and it writes only `FAULT_IP`, `CUR_TIME`, `CONSUMED`
(`lp_mem`), so every word below is the same at `s` and `X`. With `SlSets` [J]:

* `tm_of`: `SlHere.tm` (`TimerRB`: this core's tree has `TIMER_MIN` as its leftmost key, whose
  nodes are TCBs of `T`, armed, with this core in `TIMER_HEIGHT >> 8`).
* `ntf_of`: `SlHere.ntf` (`ScExtra0.bnd`: the bound notification is in `Nt`; `BndS.tb`: it is
  bound back).
* `scHere_of`: `ScHere` of the SC of a `Sch` thread of `T` with a nonzero SC, given its `CORE`
  word (`ScExtra0.bound`, `BoundInv.sact`, `SCsOK.act`); used by `dsc_of`'s pattern for
  `rh_of` (the release head: `SchedQueuesInv.release` / `inR` / `released`, `BoundInv.r`) and
  `usc_of` (the replied thread: `ReplyInv.back`, blocked on reply or receive).
  Their SCs' `CORE` words come from `core_of` (P2/SlAccJ.lean, P1's `ScAff`): the release head's
  `AFFINITY` is this core (`inR`), the replied thread's is by `SlHere.usc`'s hypothesis (line
  slco; formerly the premises `SlHereJ.rhc` / `uco`).
* `fbuf_of` / `rbuf_of`: `SlAccJ.fbuf` (m61's `FaultEnt.hbuf`) and `SlAccJ.rbuf` (P3's
  `JAtZ.rbufAt` at the entry state, the buffer words carried to the prefix state by `lp_mem`).

`slHere_of` assembles `SlHere` from the remaining `SlHereJ`; `sl_pathObl_h` / `sl_pathSide_h`
are `sl_pathObl_j` / `sl_pathSide_j` with `SlHere` so replaced (extra: `StoreTotal`, an Arch
state `a0` to run the prefix from).

Premises: `SlHereJ` (`ksb`, `cpu` [J] P3 placement; `cs`, `csc` [J] — `CUR_SC` / the current thread's SC: no
P1 invariant makes `CUR_SC` active (P1's entries take `L.cscW s ∈ Ac` as a hypothesis,
P1/QueueBudget2.lean), plus the `CORE` word; `ep` [J] fl4-sync); `SlAccK` (`pool` [J], `frl` [P],
`jz` [J] the entry is a `JAtZ` state with the layout's user words).
-/
import Fl4Proofs.P2.SlAccJ
import Fl4Proofs.P3.XTopJointRBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

theorem treeCore_of {v c : U64} (h : v.val >>> 8 = c.val) : treeCore v = c := by
  have hc : c.val = v.val / 256 := by rw [← h, Nat.shiftRight_eq_div_pow]
  unfold treeCore
  exact UScalar.eq_of_val_eq ((Classical.epsilon_spec (p := fun c' : U64 => c'.val = v.val / 256) ⟨c, hc⟩).trans hc.symm)

/-- **The prefix runs** from every entry state (P0 totality). -/
theorem lp_ex (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hT : TcbPlaced T) {s : S} (hcT : L.curW s ∈ T)
    (a : A) : ∃ X a1, LocalPre (st := st) ar s a (X, a1) := by
  obtain ⟨s1, e1, -⟩ := spec_ex_fd (obj.Tcb.set_reg.fault_ip (st := st) s (L.curW s)
    (core.num.U64.wrapping_sub (L.mem s (regA (L.curW s) layout.reg.NEXT_IP)) 2#u64) (hT _ hcT))
  obtain ⟨⟨X, a1⟩, e2, -⟩ := spec_ex_fd (Fl4Proofs.P0.sched.update_timestamp.p0 st ar s1 a hSt hA)
  exact ⟨X, a1, L.curW s, _, s1, cur_thread_ok s, reg_ok s _ _, e1, e2⟩

/-- **`SlHere.tm` from P1's timer trees.** -/
theorem tm_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (h0 : L.mem s (tmA (L := L) s) ≠ 0#u64) :
    K.heap (L.mem s (tmA (L := L) s)) = some .tcb ∧
      (L.mem s (fld (L.mem s (tmA (L := L) s)) oTIMER_DEADLINE)).val ≠ 0 ∧
      treeCore (L.mem s (fld (L.mem s (tmA (L := L) s)) oTIMER_HEIGHT)) = L.cpu s := by
  obtain ⟨⟨Q, R, hSQ⟩, -, hXI, -, -⟩ := E.hI a X a1 LP
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have eTm : L.mem X (tmA (L := L) X) = L.mem s (tmA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)
    rw [cX, nodeAt_of_ksb kX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  obtain ⟨tr, CT⟩ := hXI.2.2.rb.tree _ hSQ.cur
  have e0 : L.mem s (tmA (L := L) s) = tr.minKey := eTm.symm.trans CT.min
  have hyk : tr.minKey ∈ tr.keys := by
    rcases TRB.RBT.minKey_mem tr with e | e
    · exact absurd (e0.trans e) h0
    · exact e
  rw [e0]
  have hy := hSe.tcb (CT.inT _ hyk)
  have eD : L.mem X (tdA tr.minKey) = L.mem s (fld tr.minKey oTIMER_DEADLINE) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hy 3528#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp hy (by simp) (by simp) (by simp) (by simp))
  have eH : L.mem X (thA tr.minKey) = L.mem s (fld tr.minKey oTIMER_HEIGHT) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hy 3568#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp hy (by simp) (by simp) (by simp) (by simp))
  refine ⟨hy, fun hv => CT.armed _ hyk ?_, treeCore_of ?_⟩
  · rw [eD]
    exact UScalar.eq_of_val_eq (by rw [hv]; rfl)
  · rw [← eH, ← cX]
    exact CT.core _ hyk

/-- **`SlHere.ntf` from P1's bound links.** -/
theorem ntf_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (h0 : L.mem s (boundA (L.curW s)) ≠ 0#u64) :
    K.heap (L.mem s (boundA (L.curW s))) = some .ntfn ∧
      L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s := by
  obtain ⟨-, -, hXI, -, -⟩ := E.hI a X a1 LP
  have hc := E.hSt.1
  have eB : L.mem X (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hc 3368#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT hc hk hcp hc (by simp) (by simp) (by simp) (by simp))
  have h0X : L.mem X (boundA (L.curW s)) ≠ 0#u64 := by rw [eB]; exact h0
  have hNt := hXI.2.2.bnd _ E.hcT h0X
  have hbt := hXI.2.2.bs.tb _ E.hcT h0X
  rw [eB] at hNt hbt
  have hn := hSe.ntfn hNt
  obtain ⟨r, -, an⟩ := hX.ntW _ hn 24#u64 (by simp) (by simp)
  have eA : ntfnBtA (L.mem s (boundA (L.curW s))) = core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) 24#u64 := by
    unfold ntfnBtA layout.ntfn.BOUND_TCB
    rfl
  have eT : L.mem X (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) 24#u64) =
      L.mem s (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) 24#u64) :=
    lp_mem ar hA E.hT E.hN E.hcT LP an (not_slDS_reg hX E.hN E.hT E.hcT hc hk hcp
      (by rw [r]; intro c h; cases h) (by rw [r]; intro h; cases h))
  rw [eA, eT] at hbt
  exact ⟨hn, hbt⟩

/-- **`ScHere` of a `Sch` thread's nonzero SC** from P1's SC invariants, given its `CORE` word. -/
theorem scHere_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    {t : U64} (htT : t ∈ T) (hsch : Sch st X t) (hs0 : L.mem X (scA t) ≠ 0#u64)
    (hco : L.mem s (fld (L.mem s (scA t)) 16#u64) = L.cpu s) :
    ScHere (st := st) K Z Scs s (L.mem s (scA t)) := by
  obtain ⟨-, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  have ht := hSe.tcb htT
  have eSc : L.mem X (scA t) = L.mem s (scA t) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
  have hScs : L.mem X (scA t) ∈ Scs := (hXI.2.2.bound t htT hs0).1
  have hmx := (hSC.act _ hScs).1 (hB.sact t htT hsch hs0)
  rw [eSc] at hScs hmx
  have hz := hSe.sc hScs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA (L.mem s (scA t))) = L.mem s (maxA (L.mem s (scA t))) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 hk hcp
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  refine ⟨hz, hScs, ?_, hco⟩
  show L.mem s (maxA (L.mem s (scA t))) ≠ 0#u64
  rw [← em]
  exact hmx

/-- **`SlHere.rh` from P1's release queues** (the head's SC's `CORE` word by `core_of`: the
head is in this core's release queue, so its `AFFINITY` is this core, `SchedQueuesInv.inR`). -/
theorem rh_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    K.heap (L.mem s (rhA (L := L) s)) = some .tcb ∧
      ScHere (st := st) K Z Scs s (L.mem s (scA (L.mem s (rhA (L := L) s)))) := by
  obtain ⟨⟨Q, R, hSQ⟩, hB, -, -, -⟩ := E.hI a X a1 LP
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [cX, nodeAt_of_ksb kX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have hcC : L.cpu X ∈ Cs := hSQ.cur
  have hq := hSQ.release _ hcC
  have hhd : (L.relQ X (L.cpu X)).head = (R (L.cpu X)).headD 0#u64 := hq.head
  cases hl : R (L.cpu X) with
  | nil =>
    rw [hl] at hhd
    exact absurd (eRh.symm.trans hhd) h0
  | cons y ys =>
    rw [hl] at hhd
    have e : L.mem X (rhA (L := L) X) = y := hhd
    have hyR : y ∈ R (L.cpu X) := by rw [hl]; simp
    have hyT := hq.mem y hyR
    have haf := hSQ.inR _ hcC y hyR
    have hfl : (L.mem X (inqA y) &&& sched.Q_RELEASE) ≠ 0#u64 :=
      (hSQ.released y hyT).2 (by rw [haf]; exact hyR)
    rw [eRh] at e
    rw [e]
    have hs0 := hB.r y hyT hfl
    exact ⟨hSe.tcb hyT, scHere_of ar hA hX hSe E hk hcp LP hyT (Or.inr (Or.inl hfl)) hs0
      (core_of ar hA hX hSe E hk hcp LP hyT hs0 (haf.trans cX))⟩

/-- **`SlHere.usc` from P1's reply invariant** (the SC's `CORE` word by `core_of`, from the
thread's `AFFINITY`). -/
theorem usc_of (hA : P0.ArchTotal ar) (hX : RegionOKX K) (hSe : SlSets K T Rp Scs Nt H Z) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (hS : ¬ SlTrap st s) (lv : SlLive st found.1 s) (hs0 : L.mem s (scA (slThr st found.1 s)) ≠ 0#u64)
    (haf : L.mem s (affA (slThr st found.1 s)) = L.cpu s) :
    ScHere (st := st) K Z Scs s (L.mem s (scA (slThr st found.1 s))) := by
  have et : slThr st found.1 s = L.mem s (rTcbA found.1) := by unfold slThr; rw [if_neg hS]
  have lv' : L.mem s (rTcbA found.1) ≠ 0#u64 := by unfold SlLive at lv; rw [if_neg hS] at lv; exact lv
  rw [et] at hs0 haf ⊢
  obtain ⟨-, -, hXI, -, -⟩ := E.hI a X a1 LP
  have hrp := N.hrp hS
  have hRp : found.1 ∈ Rp := by
    rw [hSe.replies]
    show H found.1 = some .reply
    rw [← hSe.heap]
    exact hrp
  obtain ⟨r1, a1h⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  have eT : L.mem X (rTcbA found.1) = L.mem s (rTcbA found.1) :=
    lp_mem ar hA E.hT E.hN E.hcT LP a1h (not_slDS_of_obj N r1)
  have h0X : L.mem X (rTcbA found.1) ≠ 0#u64 := by rw [eT]; exact lv'
  obtain ⟨-, hT', -, hst⟩ := hXI.2.1.back _ hRp h0X
  rw [eT] at hT' hst
  have hBR : BlockedR (L.mem X (stA (L.mem s (rTcbA found.1)))) := by
    rcases hst with e | e
    · exact Or.inr e
    · exact Or.inl (Or.inr (Or.inl e))
  have ht := hSe.tcb hT'
  have eSc : L.mem X (scA (L.mem s (rTcbA found.1))) = L.mem s (scA (L.mem s (rTcbA found.1))) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
  have eAf : L.mem X (affA (L.mem s (rTcbA found.1))) = L.mem s (affA (L.mem s (rTcbA found.1))) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3520#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
  have hs0X : L.mem X (scA (L.mem s (rTcbA found.1))) ≠ 0#u64 := by rw [eSc]; exact hs0
  exact scHere_of ar hA hX hSe E hk hcp LP hT' (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hBR))))) hs0X
    (core_of ar hA hX hSe E hk hcp LP hT' hs0X (by rw [eAf]; exact haf))

/-- **What stays of `SlHere`** once its P1 parts come from the entry's invariants (`slHere_of`). -/
structure SlHereJ (K : KLayout) (Z : U64 → Nat) (Scs : Set U64) (found : U64 × U64) (s : S) : Prop where
  /-- [J] as `SlHere.ksb`. -/
  ksb : L.ksb s = K.ksb
  /-- [J] as `SlHere.cpu`. -/
  cpu : (L.cpu s).val < K.ncores
  /-- [J] as `SlHere.cs` (no P1 invariant makes `CUR_SC` active, nor relates its `CORE` word to
  this core). -/
  cs : ScHere (st := st) K Z Scs s (L.cscW s)
  /-- [J] as `SlHere.csc` (the current thread's SC: active only under `ACTION_RESUME_CURRENT`,
  `BoundInv.resume`, which the entry does not know). -/
  csc : ¬ SlTrap st s → ScHere (st := st) K Z Scs s (L.mem s (scA (L.curW s)))
  /-- [J] as `SlHere.ep`. -/
  ep : ¬ SlTrap st s → K.heap found.2 = some .ep

/-- **`SlHere` from the entry's P1 invariants**, `SlSets` and `SlHereJ` (the prefix run from
`a0`, `lp_ex`). -/
theorem slHere_of (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hX : RegionOKX K)
    (hSe : SlSets K T Rp Scs Nt H Z) (a0 : A) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hj : SlHereJ (st := st) K Z Scs found s) :
    SlHere (st := st) K Z Scs found s := by
  obtain ⟨X, a1, LP⟩ := lp_ex ar hSt hA E.hT E.hcT a0
  exact
  { ksb := Hj.ksb
    cpu := Hj.cpu
    tm := tm_of ar hA hX hSe E Hj.ksb Hj.cpu LP
    rh := fun h => rh_of ar hA hX hSe E Hj.ksb Hj.cpu LP h
    cs := Hj.cs
    csc := Hj.csc
    usc := fun hS lv ha h0 => usc_of ar hA hX hSe E N Hj.ksb Hj.cpu LP hS lv h0 ha
    ntf := fun _ h => ntf_of ar hA hX hSe E Hj.ksb Hj.cpu LP h
    ep := Hj.ep }

/-- **`SlAccJ.fbuf` from m61's receive buffer** (`FaultEnt.hbuf`: `BufOK U`, `FaultEnt.hU`: `U`'s
words are aligned), given that P1's user words `U` are the layout's user words. -/
theorem fbuf_of (hUu : ∀ b ∈ U, b ∈ K.user) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) (rb : U64)
    (hrb : msg.lookup_ipc_buffer st X true dest = ok rb) : BufW (fun b => Aligned b ∧ b ∈ K.user) rb := by
  obtain ⟨-, rest, FE⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r hc
  have hb := FE.hbuf
  rw [hrb, WP.spec_ok] at hb
  intro hne i hi
  have hu := hb hne i hi
  exact ⟨(FE.hU _ hu).1.1, hUu _ hu⟩

/-- **What stays of `SlAccJ`** once `fbuf` comes from `fbuf_of` and `rbuf` from `rbuf_of`. -/
structure SlAccK (K : KLayout) (Locks : S → U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  /-- [J] as `SlAccIn.pool`. -/
  pool : ∀ hi : U64, hi.val < 2048 → L.mem s (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
    Aligned (peAF (L.mem s (atAF K.ksb hi)) lo) ∧ region K (peAF (L.mem s (atAF K.ksb hi)) lo) = .none
  /-- [P] as `SlAccJ.frl`. -/
  frl : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → Locks s r
  /-- [J] the entry state is a state of the joint invariant (`P3.JAtZ`) whose user words
  (`Z.B`) are the layout's, as for `OwnMap.layoutJ` (P2/OwnJAtZ.lean). Gives `SlAccJ.rbuf`
  (`rbuf_of`, P3's `JAtZ.rbufAt`). -/
  jz : ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Hx : Heap) (Cx Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    Fl4Proofs.P3.JAtZ (L := L) arI AR Zx Hx Cx Ax Lst D s a' σ ∧ K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b}

/-- **`SlAccJ.rbuf` from the joint invariant** (line slco, P3's `JAtZ.rbufAt`): the current
thread's `IPC_BUFFER` word and its buffer slot's two words are not prefix words (a TCB word from
offset 192, a TCB slot's words: `not_slDS_tcb` / `not_slDS_reg`), so the prefix state agrees with
the entry on them (`lp_mem`). -/
theorem rbuf_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hk : L.ksb s = K.ksb) (hcp : (L.cpu s).val < K.ncores)
    {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets}
    {Hx : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'} {σ : Fl4Spec.State Unit}
    (J : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx Hx Cx Ax Lst D s a' σ)
    (hKu : K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b})
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {buf : U64}
    (hb : msg.lookup_ipc_buffer st X false (L.curW s) = ok buf) :
    BufW (fun b => Aligned b ∧ b ∈ K.user) buf := by
  have hc := E.hSt.1
  have e1 : L.mem X (ibA (L.curW s)) = L.mem s (ibA (L.curW s)) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hc 3512#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT hc hk hcp hc (by simp) (by simp) (by simp) (by simp))
  have es : sbA (L.curW s) = slotIdx (L.curW s) 2#u64 := by
    unfold sbA slotIdx
    congr 1
    simp [layout.tcb.SLOT_BUFFER, layout.cte.SIZE]
  obtain ⟨hsl, -, r8, -, al0, al8⟩ := hX.tslot _ hc 2#u64 (by simp)
  have r0 := hK.slot _ hsl
  have e2 : L.mem X (sbA (L.curW s)) = L.mem s (sbA (L.curW s)) := by
    rw [es]
    exact lp_mem ar hA E.hT E.hN E.hcT LP al0 (not_slDS_reg hX E.hN E.hT E.hcT hc hk hcp
      (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
  have e3 : L.mem X (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) =
      L.mem s (core.num.U64.wrapping_add (sbA (L.curW s)) 8#u64) := by
    rw [es]
    exact lp_mem ar hA E.hT E.hN E.hcT LP al8 (not_slDS_reg hX E.hN E.hT E.hcT hc hk hcp
      (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h))
  have hB := J.rbufAt e1 e2 e3 hb
  intro hne i hi
  have h := hB hne i hi
  simp only [Fl4Proofs.P3.ZUser, Set.mem_setOf_eq] at h
  refine ⟨h.1, ?_⟩
  rw [hKu]
  exact h.2

theorem slAccJ_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) (hUu : ∀ b ∈ U, b ∈ K.user)
    {s : S} (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hj : SlHereJ (st := st) K Z Scs found s)
    (Ak : SlAccK (st := st) ar K Locks found s) : SlAccJ (st := st) ar K Locks found s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, J, hKu⟩ := Ak.jz
  exact
  { pool := Ak.pool, frl := Ak.frl
    rbuf := fun _ a X a1 LP buf hb => rbuf_of ar hA hK hX E Hj.ksb Hj.cpu J hKu LP hb
    fbuf := fun hS a X a1 LP {_p _b _d _r} hc rb hrb => fbuf_of ar hUu E hS LP hc rb hrb }

variable {p : SProg Bool}

/-- **`PathObl` of the syscall entry**: `sl_pathObl_j` with `SlHere` from `slHere_of`
(`SlHereJ`; `StoreTotal` [P] and an Arch state to run the prefix from). -/
theorem sl_pathObl_h (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K)
    (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hSe : SlSets K T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K Locks found s) :
    PathObl st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (SlRS (st := st) K Locks) (SlWS (st := st) K Locks) (SlDS (L := L)) :=
  sl_pathObl_j ar hA hK hX hU hFp hz hm hSe hPE hE
    (fun s hP => slHere_of ar hSt hA hX hSe a0 (hPE s hP) (hE s hP) (hHj s hP))
    (fun s hP => slAccJ_of ar hA hK hX hUu (hPE s hP) (hHj s hP) (hAk s hP))

/-- **`PathSide` of the syscall entry**: `sl_pathSide_j` with `SlHere` from `slHere_of`. -/
theorem sl_pathSide_h (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hK : RegionOK K)
    (hX : RegionOKX K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    (hFp : IsProg (fun {A : Type} (ar : machine.Arch A) (st : machine.Store S) (s : S) (a : A) =>
      syscall.handle_syscall_local st ar s a n found) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hSe : SlSets K T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop} (hPE : ∀ s, P s → SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hE : ∀ s, P s → SlEnt (st := st) K Locks found s)
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
  sl_pathSide_j ar hSt hA hK hX hU hFp hz hm hSe hPE hE
    (fun s hP => slHere_of ar hSt hA hX hSe a0 (hPE s hP) (hE s hP) (hHj s hP))
    (fun s hP => slAccJ_of ar hA hK hX hUu (hPE s hP) (hHj s hP) (hAk s hP)) huf

end

end Fl4Proofs.P2.PathObl
