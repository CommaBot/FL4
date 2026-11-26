/-
# P2 (line vmscope, gen 6): io's `kd` is satisfiable; the syscall path's user-write frame without a P3 bundle

## 1. Vacuity check of the ∀-`Pre` fields with a fixed `m`
The AFFINITY counterexamples (`vmRPremP3_false`, `vmFPremNL_false`, `vtPremP7M_false`, P2/E2EPW11J8.lean) refute a
record field whose **conclusion** ties the fixed `m` to the state (`m (AFFINITY d) = mem s (AFFINITY d)` at every
`Pre` state): two `Pre` states that differ on one TCB's `AFFINITY` word (two threads homed on two cores) leave no `m`.
`IoPremX5.kd` (VX5) is `∀ s, IoPreX st i K m s → KernDetS (userV K).user i.Locks s`: `m` occurs only in the
**antecedent** (`IoPreX` = `IoPre ∧ AffAg K m s ∧ i.Q K m s`), the conclusion is `m`-free. So the field is antitone in
`m`'s constraint: it is implied by its `m`-free form at every `m` (**`ioPremX5_kd_of`**), and it holds for every `m`
whenever the lock map is determined by words off `(userV K).user` (**`ioPremX5_of_reads`**, **`ioPremX5_of_const`**).
**`ioPremX5_sat`**: at every layout (any `K.ncores`, in particular ≥ 2) there is an index with `∀ m, IoPremX5 st i K m`
(its lock map constant, the start fact's `j.Locks σ = hs` then fixes the constant to the held set). No counterexample
exists: verdict **satisfiable**.

**Every remaining ∀-`Pre` field with a fixed `m` in `serializable_fl4_localVX5`'s supplied records** (all records the
start facts ask for, native `StartU1`/`StartU`/`StartD`/… and VM-epoch `StartVX5`, enumerated): only
`IoPremX5.kd` (`m` in the antecedent only). Every other supplied `∀ s` field has no `m` (`VmFPremB.kd`, `VmRPremA.kd`,
`VtPremA0.kd`, `SlPremP6.kd`, `VxPremP3E.kd`, `StPremW3B.kd`, `IoPremW9.kd`, `IrqPremK2B.kd`, `DelPtePrem.lk`,
`InvPremW.lk`, `VxPremV2.kd`, `VtPremV2.kd`, `StPremX5.kd`, `IrqPremX5.kd`; `PlanLk`), and the index conventions
`hQ` bind their own `m'`. Fields with `m` in the conclusion (`IoPremW2B.mA`/`.qf`, `StPremK2B.pe`/`.uf`,
`VxPremP3.eu`, `VxPremV.eu`, `IoPremX2.qf`) are not supplied: each is derived by a proved theorem (`toP3`, `toX2`,
`toV`, `vxEu_of(V)`) and has the same `AffAg`-type agreement in its antecedent, so it is not of the refuted shape.

## 2. The syscall path's user-write frame from `UserLayX` (no P3 bundle)
`sl_pathsKC5`'s chain asks every frame fact at `SlJAt` (P3 bundle) states, which no guest-running state is. The
frame lemmas read only a few facts off the bundle; **`SlLX K s`** collects them: VX2's store-free `UserLayX`,
`RegionOK`, `UserOK`, the ASID-table words off the user words (`ua`), and state facts at `s` (`kc`: kernel base and
core; `cur`: the current thread is a heap TCB; `np`: this core's node placed; `hep`: the fault-handler endpoint cap
names a heap endpoint; `cn`: P1's `CnOff` at `∅, ∅, K.user` (the CSpace walk reads only aligned non-user slot words);
`ft`: what `reply_caps` returns is a heap reply and endpoint).
* **`SlLX.wr`**: `SlLX` survives an aligned user-word write (`curW_wr`, `fh_wr`, **`cn_wr`**, **`ft_wr`**, the
  last by `reply_caps_keep` run backwards: `WritesIn` is symmetric).
* the `SlJUB*` frame lemmas re-derived at `SlLX` (statements as the `SlJAt` ones, `B : SlLX` for `B : SlJAt`):
  `SlLX.curW_wr`, `flags_wr`, `trap_wr`, `fh_wr`, `replyCaps_wr`, `syncC_wr`, `entL_wr`, `slDS_wr`, `slRWS_wr`,
  `nuNode`, `nuKs`, `lp_wr`, `slCom_nuX`, `fltDec_nuX`, `flt_ptr_epX`, `SlLX.accR_wr`, `rrG`, `rrDR_nuX`,
  `SlLX.preRR_wr`, `nuNode64`, `nuAsid`, **`SlLX.preB_wrN`**, **`SlLX.preB_wrG`** (BXI by VX2's `bxi_userX`),
  **`slQ_wrX`** (`SlQ` across the write) and **`sl_hufX`** (`sl_localPathK`'s `huf` at `Pre := SlLX ∧ SlQ`, the
  locks by `KernDetS`).
* Consistency: **`SlLX.ofSlJAt`** (every P3 bundle state has it). VM epochs: **`SlLX.ofVtx`** — the epoch's
  `VtxBundle` (`ul`, `ok`, `uok`), `QPs` (`ua` by `QPs.uoff`), `SlPreB` at the state (`cur`, `np`) and
  **`SlEntS`** [S] (`cpu`, `hep`, `cn`, `ft` at a guest-running entry).

No new [J]. `SlEntS` is [S] (scope): P3's typedness of caps (`JPlaced.typed`) and `CnOff` (`JAtZ.capSW`) at a state
where another core runs a guest; a guest writes only its VCPU's data words and guest frames (`HwStepP`), none of which
is a cap-slot, TCB or node word (`VtxBundle.vsl`, VCPUs are `other 15` objects), so these facts are those of the last
native state; the entering core is one of the layout's (`cpu`).

## `SchedCore.aff` dependence (P3 chains currently force every TCB's `AFFINITY` to the current cpu)
Nothing proved here uses it: the io satisfiability lemmas are about the lock map, the `SlLX` frame lemmas use only
layout facts and the facts at the state itself. Only the consistency lemma **`SlLX.ofSlJAt`** goes through a P3
bundle (and so through states of a chain where `SchedCore.aff` holds); `SlLX.ofVtx` does not. `SlPreB.aff` (in
`SlQ`, the `Pre`) is the start state's own agreement with the map memory, not a chain fact.

## Not done (next)
The sl **slot** in VM epochs still needs, at `Pre := SlLX ∧ SlQ`: (a) `PathObl`'s entry facts (`SlEntJ` from
`hep`/`cur` — done here in substance —, `SlHereJ`'s `cscFacts` and `SlAccJ`'s `pool`/`rbuf`, the latter from P3's
`JAtZ.rbufAt`: two more [S] fields); (b) `ReadOnce` (`sl_rr_once`/`sl_hro`, `SlOF.B : SlJAt`, used via `regionOKX`,
`nuNode`, `nuKs`, `kc`, `slCom_nu`, `fltDec_nu`: a port of `SlOnceN`/`A`/`B`/`R1`/`R3` to `SlLX`); (c) `AvoidV`
/ PTE avoidance (`sl_avoidVK` / `sl_avoidVKE_rQ` take `Pre → SlJAt`). Route C (path at `K.toKLayout`, cut by
`AvoidV`) is the one available: route U fails (`NoVcpuRW` is false for `SlRS`, which holds every user word).

No sorry / admit / native_decide / bv_decide. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX5
open Aeneas Aeneas.Std Result

/-! ## Part 1: io's `kd` is satisfiable -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW RegionOK LayP)

noncomputable section
open Classical

section iokd
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`kd` at every `m` from its `m`-free form** (`m` occurs in `IoPremX5.kd` only in the antecedent). -/
theorem ioPremX5_kd_of {i : IoArg S} {K : KLayoutV}
    (h : ∀ s, IoPre st (userV K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac s → KernDetS (L := L) (userV K).user i.Locks s) (m : U64 → U64) :
    ∀ s, IoPreX st i K m s → KernDetS (L := L) (userV K).user i.Locks s :=
  fun s hP => h s hP.1

/-- **The record at every `m`** from the two index conventions and the `m`-free `kd`. -/
theorem ioPremX5_of_kd {i : IoArg S} {K : KLayoutV}
    (hQ : i.Q = fun K' m' s => IoQ st i.Cs i.Ω i.Sg i.Ac K'.toKLayout m' s)
    (hCs : i.Cs = {c : U64 | c.val < K.ncores})
    (h : ∀ s, IoPre st (userV K) K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac s → KernDetS (L := L) (userV K).user i.Locks s) :
    ∀ m, IoPremX5 st i K m :=
  fun m => ⟨hQ, hCs, ioPremX5_kd_of h m⟩

/-- **The record at every `m` from a lock map reading only aligned words off `(userV K).user`** at `IoPre`
states (`kernelDetS_of_reads`). -/
theorem ioPremX5_of_reads {i : IoArg S} {K : KLayoutV} {R : Set U64}
    (hQ : i.Q = fun K' m' s => IoQ st i.Cs i.Ω i.Sg i.Ac K'.toKLayout m' s)
    (hCs : i.Cs = {c : U64 | c.val < K.ncores})
    (hR : LkReads (L := L) R i.Locks) (hRa : ∀ x ∈ R, Aligned x) (hRU : ∀ x ∈ R, x ∉ (userV K).user) :
    ∀ m, IoPremX5 st i K m :=
  ioPremX5_of_kd hQ hCs (kernelDetS_of_reads hR hRa (fun _ _ => hRU))

/-- A constant lock map is determined by any words. -/
theorem kernDetS_const {U : Set U64} {Locks : S → U64 → Prop} (hc : ∀ s s', Locks s = Locks s') :
    ∀ s, KernDetS (L := L) U Locks s :=
  fun s s' _ _ _ _ => hc s' s

/-- **The record at every `m` for a constant lock map** (the locks a core holds through a local path: the start
fact's `j.Locks σ = hs` fixes the constant). -/
theorem ioPremX5_of_const {i : IoArg S} {K : KLayoutV}
    (hQ : i.Q = fun K' m' s => IoQ st i.Cs i.Ω i.Sg i.Ac K'.toKLayout m' s)
    (hCs : i.Cs = {c : U64 | c.val < K.ncores}) (hc : ∀ s s', i.Locks s = i.Locks s') :
    ∀ m, IoPremX5 st i K m :=
  ioPremX5_of_kd hQ hCs (fun s _ => kernDetS_const hc s)

/-- **`IoPremX5` is jointly satisfiable at every layout** (any core count, in particular `K.ncores ≥ 2`), for one
index and **every** `m` at once: the index with the layout's cores, `IoQ` and the constant lock map `hs`. Contrast
`vmRPremP3_false`: there the conclusion fixes `m` to each `Pre` state's `AFFINITY` words. -/
theorem ioPremX5_sat (K : KLayoutV) (number : I64) (Ω Sg Ac : Set U64) (hs : U64 → Prop) :
    ∃ i : IoArg S, i.Cs = {c : U64 | c.val < K.ncores} ∧ i.Locks = (fun _ => hs) ∧ ∀ m, IoPremX5 st i K m :=
  ⟨{ number := number, Cs := {c : U64 | c.val < K.ncores}, Ω := Ω, Sg := Sg, Ac := Ac, Locks := fun _ => hs,
      Q := fun K' m' s => IoQ st {c : U64 | c.val < K.ncores} Ω Sg Ac K'.toKLayout m' s },
    rfl, rfl, ioPremX5_of_const rfl rfl (fun _ _ => rfl)⟩

end iokd

end
end Fl4Proofs.P2.E2EP

/-! ## Part 2: `SlLX` and the frame lemmas -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section lx
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **What the syscall path's user-write frame reads off P3's bundle** (module docstring). -/
structure SlLX (K : KLayout) (s : S) : Prop where
  /-- VX2's store-free user-word layout. -/
  ul : Fl4Proofs.P2.E2EP.UserLayX L K
  /-- `RegionOK` of the layout. -/
  ok : RegionOK K
  /-- `UserOK` of the layout. -/
  uok : Fl4Proofs.P2.E2E.UserOK K
  /-- The ASID-table words are no user words. -/
  ua : ∀ x ∈ K.user, ∀ hi : U64, hi.val < 2048 → x ≠ atAF K.ksb hi
  /-- The kernel base is the layout's; the core is one of its cores. -/
  kc : L.ksb s = K.ksb ∧ (L.cpu s).val < K.ncores
  /-- The current thread is a heap TCB. -/
  cur : K.heap (L.curW s) = some .tcb ∧ TcbAddr (L.curW s)
  /-- This core's node is placed. -/
  np : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s)
  /-- The fault handler's endpoint cap names a heap endpoint (P3's `JPlaced.typed`). -/
  hep : IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    K.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep
  /-- The current thread's CSpace walk reads aligned non-user slot words only (P3's `JAtZ.capSW`). -/
  cn : CnOff (L := L) ∅ ∅ K.user s (L.curW s)
  /-- What `reply_caps` returns for the current thread is a heap reply and endpoint (P3's lookup typing). -/
  ft : ∀ found : U64 × U64, (∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found)) →
    K.heap found.1 = some .reply ∧ K.heap found.2 = some .ep

variable {K : KLayout} {s : S}

theorem SlLX.regionOKX (B : SlLX (L := L) K s) : RegionOKX K := B.ul.rx
theorem SlLX.regionOK (B : SlLX (L := L) K s) : RegionOK K := B.ok
theorem SlLX.layP (B : SlLX (L := L) K s) : LayP K := B.ul.lp
theorem SlLX.ncores_le (B : SlLX (L := L) K s) : K.ncores ≤ 64 := B.ul.nc
theorem SlLX.hCs (B : SlLX (L := L) K s) : ∀ c ∈ {c : U64 | c.val < K.ncores}, c.val < 64 :=
  fun _ hc => lt_of_lt_of_le hc B.ul.nc

theorem SlLX.userKs (B : SlLX (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {o : U64} (ho : o.val < 13568) : x ≠ core.num.U64.wrapping_add K.ksb o := B.ul.uks x hx o ho

theorem SlLX.userNode64 (B : SlLX (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {c : U64} (hc : c.val < 64) : x.val + 8 ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ x.val :=
  B.ul.unode x hx c hc s B.kc.1

theorem SlLX.userObj (B : SlLX (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {p : U64} {k : HKind} (hp : K.heap p = some k) (hk : ∀ z, k ≠ .other z) : ¬ InW p (2 ^ k.bits) x :=
  B.ul.uobj x hx p k hp hk

theorem SlLX.userAsid (B : SlLX (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {hi : U64} (hhi : hi.val < 2048) : x ≠ atAF (L.ksb s) hi := by
  rw [B.kc.1]; exact B.ua x hx hi hhi

/-- **The current thread is kept by a user-word write** (`SlJAt.curW_wr` at `SlLX`). -/
theorem SlLX.curW_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : L.curW (L.wr s b v) = L.curW s := by
  have hN := B.np
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  rw [curth_val] at hv
  unfold LawfulStore.curW
  rw [nodeAt_wr, LawfulStore.cpu_wr]
  refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
  have hbv : b.val = L.nodeBase s (L.cpu s) := by rw [e]; omega
  rcases B.userNode64 hb (Nat.lt_of_lt_of_le B.kc.2 B.ul.nc) with h | h <;> omega

/-- **The current thread's flags are kept by a user-word write.** -/
theorem SlLX.flags_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) :
    obj.Tcb.flags st (L.curW s) (L.wr s b v) = obj.Tcb.flags st (L.curW s) s := by
  obtain ⟨ht, hA⟩ := B.cur
  have hv := tcb_wadd_val hA (o := 3456#u64) (by decide)
  rw [flags_mem, flags_mem, B.layP.mem_wrT hb hba v ht (field_aligned hA (by decide) (by decide))
    (by rw [hv]; omega) (by rw [hv]; simp)]

/-- **`SlTrap` is kept by a user-word write.** -/
theorem SlLX.trap_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : SlTrap st (L.wr s b v) ↔ SlTrap st s := by
  unfold SlTrap
  rw [B.curW_wr hb hba v, B.flags_wr hb hba v]

/-- **The current thread's fault-handler cap is kept by a user-word write.** -/
theorem SlLX.fh_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) :
    obj.Slot.cap st (fhA (L := L) (L.wr s b v)) (L.wr s b v) = obj.Slot.cap st (fhA (L := L) s) s := by
  have ec := B.curW_wr hb hba v
  obtain ⟨ht, hA⟩ := B.cur
  have hf := hA.fits
  have hal := hA.align
  show obj.Slot.cap st (slotIdx (L.curW (L.wr s b v)) layout.tcb.SLOT_FAULT_HANDLER) (L.wr s b v) =
    obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) s
  rw [ec]
  have hv : (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER).val = (L.curW s).val + 96 := by
    have := slj_slotIdx_val (t := L.curW s) (i := layout.tcb.SLOT_FAULT_HANDLER)
      (by simp [layout.tcb.SLOT_FAULT_HANDLER]; omega)
    simpa [layout.tcb.SLOT_FAULT_HANDLER] using this
  have hv8 : (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64).val =
      (L.curW s).val + 104 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hv]; omega
  unfold obj.Slot.cap
  rw [L.read_pair_eq, L.read_pair_eq,
    B.layP.mem_wrT hb hba v ht (by unfold Aligned; rw [hv]; omega) (by rw [hv]; omega) (by rw [hv]; omega),
    B.layP.mem_wrT hb hba v ht (by unfold Aligned; rw [hv8]; omega) (by rw [hv8]; omega) (by rw [hv8]; omega)]

/-- The current thread's words read by `reply_caps` are no user word. -/
theorem SlLX.rcTcb (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user) :
    ∀ Kk : U64, (Kk.val = 0 ∨ Kk.val = 8 ∨ Kk.val = 256 + 8 * layout.reg.REPLY.val ∨
      Kk.val = 256 + 8 * layout.reg.CAP.val) → ¬ (core.num.U64.wrapping_add (L.curW s) Kk = b) := by
  obtain ⟨ht, hA⟩ := B.cur
  intro Kk hK e
  have hKv : Kk.val < 4096 := by
    rcases hK with h | h | h | h <;>
      (try simp [layout.reg.REPLY, layout.reg.R12, layout.reg.CAP, layout.reg.RDI] at h) <;> omega
  have hw := tcb_wadd_val hA hKv
  exact B.layP.user b hb _ .tcb ht (Or.inl rfl)
    ⟨by rw [← e, hw]; omega, by rw [← e, hw]; simp only [HKind.bits]; omega⟩

/-- **`reply_caps` of the current thread is kept by a user-word write** (P1's `reply_caps_keep` at `CnOff ∅ ∅
K.user`). -/
theorem SlLX.replyCaps_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {rp ep : U64}
    (hrc : fastpath.reply_caps st s (L.curW s) = ok (some (rp, ep))) :
    fastpath.reply_caps st (L.wr s b v) (L.curW s) = ok (some (rp, ep)) :=
  reply_caps_keep (T := ∅) (Cs := ∅) (Sg := K.user) B.cur.2 hrc (writesIn_wr hba) (B.rcTcb hb)
    (fun w hw e => hw.2 (by rw [e]; exact hb)) B.cn

/-- **`CnOff ∅ ∅ K.user` survives a user-word write** (the root cap is a TCB slot's, the walked slots' words are
aligned non-user words, so every cap read is unchanged). -/
theorem SlLX.cn_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : CnOff (L := L) ∅ ∅ K.user (L.wr s b v) (L.curW s) := by
  intro sl root hsl hroot
  obtain ⟨ht, -⟩ := B.cur
  have esl : sl = slotIdx (L.curW s) layout.tcb.SLOT_CTABLE := by
    rw [tcb_slot_val] at hsl; exact (ok_inj_ff hsl).symm
  subst esl
  have nts := nu_tslot B.ok B.regionOKX ht (i := layout.tcb.SLOT_CTABLE) (by simp [layout.tcb.SLOT_CTABLE])
  have hroot0 : obj.Slot.cap st (slotIdx (L.curW s) layout.tcb.SLOT_CTABLE) s = ok root := by
    rw [← hroot]; exact (cap_congr (wr_nu hba hb v nts.1) (wr_nu hba hb v nts.2)).symm
  obtain ⟨C, h1, h2, h3⟩ := B.cn _ root (tcb_slot_val _ _) hroot0
  have ek : ∀ p r m x, C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (x &&& m)) (L.wr s b v) = obj.Slot.cap st (cnSlot p (x &&& m)) s := by
    intro p r m x hC hm
    obtain ⟨c1, c2⟩ := h3 p r m x hC hm
    exact cap_congr (wr_nu hba hb v ⟨c1.1.1, c1.2⟩) (wr_nu hba hb v ⟨c2.1.1, c2.2⟩)
  refine ⟨C, h1, fun p r m x p' r' gs' g' hC hm e => h2 p r m x p' r' gs' g' hC hm
    (by rw [← ek p r m x hC hm]; exact e), fun p r m x hC hm => ?_⟩
  obtain ⟨c1, c2⟩ := h3 p r m x hC hm
  exact ⟨⟨OutsideObjs.ksb c1.1 (L.ksb_wr _ _ _), c1.2⟩, ⟨OutsideObjs.ksb c2.1 (L.ksb_wr _ _ _), c2.2⟩⟩

/-- **`ft` survives a user-word write**: what `reply_caps` returns after the write it returned before
(`reply_caps_keep` from the written state back to `s`; `WritesIn` is symmetric). -/
theorem SlLX.ft_wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) :
    ∀ found : U64 × U64, (∀ t, sched.cur_thread st (L.wr s b v) = ok t →
        fastpath.reply_caps st (L.wr s b v) t = ok (some found)) →
      K.heap found.1 = some .reply ∧ K.heap found.2 = some .ep := by
  intro found hf
  obtain ⟨rp, ep⟩ := found
  have ec := B.curW_wr hb hba v
  have h1 : fastpath.reply_caps st (L.wr s b v) (L.curW s) = ok (some (rp, ep)) := by
    have := hf _ (cur_thread_ok (L := L) (L.wr s b v)); rwa [ec] at this
  have W := writesIn_wr (st := st) (s := s) (v := v) hba
  have hW : WritesIn st (L.wr s b v) s (· = b) :=
    ⟨W.1.symm, W.2.1.symm, fun x hx hn => (W.2.2 x hx hn).symm⟩
  have hk : ∀ Kk : U64, (Kk.val = 0 ∨ Kk.val = 8 ∨ Kk.val = 256 + 8 * layout.reg.REPLY.val ∨
      Kk.val = 256 + 8 * layout.reg.CAP.val) → ¬ (core.num.U64.wrapping_add (L.curW s) Kk = b) := B.rcTcb hb
  have h0 : fastpath.reply_caps st s (L.curW s) = ok (some (rp, ep)) :=
    reply_caps_keep (T := ∅) (Cs := ∅) (Sg := K.user) B.cur.2 h1 hW hk
      (fun w hw e => hw.2 (by rw [e]; exact hb)) (B.cn_wr hb hba v)
  exact B.ft (rp, ep) fun t et => by
    rw [cur_thread_ok] at et
    rw [← ok_inj_ff et]
    exact h0

/-- **`SlLX` survives an aligned user-word write.** -/
theorem SlLX.wr (B : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    SlLX (L := L) K (L.wr s b v) where
  ul := B.ul
  ok := B.ok
  uok := B.uok
  ua := B.ua
  kc := ⟨by rw [L.ksb_wr]; exact B.kc.1, by rw [L.cpu_wr]; exact B.kc.2⟩
  cur := by rw [B.curW_wr hb hba v]; exact B.cur
  np := by rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) B.np
  hep := by rw [B.fh_wr hb hba v]; exact B.hep
  cn := by rw [B.curW_wr hb hba v]; exact B.cn_wr hb hba v
  ft := B.ft_wr hb hba v

/-- **fl4-sync's contract `SlSyncC` is kept by a user-word write.** -/
theorem SlLX.syncC_wr (h : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {n : I64} {found : U64 × U64} (C : SlSyncC st n found s) :
    SlSyncC st n found (L.wr s b v) := by
  have ec := h.curW_wr hb hba v
  have etr := h.trap_wr hb hba v
  refine ⟨?_, fun hS => C.arm fun h' => hS (etr.2 h')⟩
  intro t f et ef hf hn
  rw [cur_thread_ok] at et
  have e : t = L.curW s := by rw [← ec]; exact (ok_inj_ff et).symm
  subst e
  have ef' : obj.Tcb.flags st (L.curW s) s = ok f := by rw [← h.flags_wr hb hba v]; exact ef
  obtain ⟨rp, ep⟩ := found
  exact h.replyCaps_wr hb hba v (C.fd _ _ (cur_thread_ok (L := L) s) ef' hf hn)

/-- **The lock facts `SlEntL` are kept by a user-word write**, the locks kept (`hl` [P]). -/
theorem SlLX.entL_wr (h : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {Locks : S → U64 → Prop} {found : U64 × U64}
    (hl : Locks (L.wr s b v) = Locks s) (E : SlEntL (st := st) K Locks found s) :
    SlEntL (st := st) K Locks found (L.wr s b v) := by
  have etr := h.trap_wr hb hba v
  have efh := h.fh_wr hb hba v
  refine ⟨fun hS hE => ?_, fun hS => ?_⟩
  · rw [efh] at hE ⊢; rw [hl]; exact E.lep (etr.1 hS) hE
  · rw [hl]; exact E.lrp fun h' => hS (etr.2 h')

/-- **`SlDS` is kept by a user-word write.** -/
theorem SlLX.slDS_wr (h : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : SlDS (L := L) (L.wr s b v) = SlDS (L := L) s := by
  have ec := h.curW_wr hb hba v
  funext w
  simp only [SlDS, ec, nodeAt_wr, LawfulStore.cpu_wr]

/-- **`SlRS` / `SlWS` are kept by a user-word write**, the locks kept. -/
theorem SlLX.slRWS_wr (h : SlLX (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) (Locks : S → U64 → Prop) (hlk : Locks (L.wr s b v) = Locks s) :
    SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
      SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s := by
  have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
    E2E.ownDep h.ok h.uok _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  refine ⟨?_, ?_⟩ <;> funext w <;> simp only [SlRS, SlWS, RPerm, WPerm, GateOnly, eo, hlk, LawfulStore.cpu_wr]

/-- A node word of this core is `NU`. -/
theorem SlLX.nuNode (B : SlLX (L := L) K s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    NU K (L.nodeAt s (L.cpu s) o) := by
  obtain ⟨hk, hc⟩ := B.kc
  have v := nodeAt_val hN ho
  have hr : region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    B.regionOKX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact nu_of_region B.regionOKX (nodeAt_aligned hN ho h8) (by rw [hr]; intro h; cases h)

/-- A kernel global (the first 256 bytes of the block) is `NU`. -/
theorem SlLX.nuKs (B : SlLX (L := L) K s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 256) (h8 : o.val % 8 = 0) :
    NU K (core.num.U64.wrapping_add (L.ksb s) o) := by
  obtain ⟨hk, -⟩ := B.kc
  refine ⟨(rs_ks (Locks := fun _ _ => True) B.regionOKX hN hk ho h8).1, fun hx => ?_⟩
  rw [hk] at hx
  exact B.userKs hx (o := o) (by omega) rfl

/-- A node word of a core below 64 is `NU` (at any state with the same kernel base). -/
theorem SlLX.nuNode64 {X : S} (B : SlLX (L := L) K s) (hk : L.ksb X = L.ksb s)
    {T : Set U64} {c : U64} (hc : c.val < 64) (hN : NodePlaced st T X c) {o : U64} (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) : NU K (L.nodeAt X c o) := by
  refine ⟨nodeAt_aligned hN ho h8, fun hu => ?_⟩
  have h := B.userNode64 hu hc
  have v := nodeAt_val hN ho
  have e : L.nodeBase X c = L.nodeBase s c := by simp [LawfulStore.nodeBase, hk]
  rw [v, e] at h
  omega

/-- An ASID-table word is `NU` (at any state with the same kernel base). -/
theorem SlLX.nuAsid {X : S} (B : SlLX (L := L) K s) (hk : L.ksb X = L.ksb s)
    {hi : U64} (hhi : hi.val < 2048) : NU K (atAF (L.ksb X) hi) := by
  refine ⟨?_, fun hu => B.userAsid hu hhi (by rw [hk])⟩
  rw [hk, B.kc.1]; exact (B.regionOKX.asidT hi hhi).2

variable {A : Type} (ar : machine.Arch A)

/-- **The commuting lemma** (`SlJAt.lp_wr` at `SlLX`). -/
theorem SlLX.lp_wr (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    {T : Set U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hcH : K.heap (L.curW s) = some .tcb)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {a a1 : A} {X' : S}
    (LP' : LocalPre (st := st) ar (L.wr s b v) a (X', a1)) :
    ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' := by
  have ecur := B.curW_wr hb hba v
  have hX := B.regionOKX
  obtain ⟨KN, hKN, eKN⟩ := regA_eq (hT _ hcT) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 256 + 8 * layout.reg.NEXT_IP.val := hKN
  have nNx : NU K (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [eKN]
    exact nu_tcb hX hcH (by rw [hKN']; simp [layout.reg.NEXT_IP])
      (by rw [hKN']; simp [layout.reg.NEXT_IP]) (by rw [hKN']; simp [layout.reg.NEXT_IP])
  obtain ⟨X, LP, hag⟩ := lp_alt ar hA (Q := NU K) nu_al hT hN hcT (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) ecur
    (fun x hx => mem_wr_ne' hba hx.1 (fun e => hx.2 (e ▸ hb))) nNx
    (B.nuNode hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    (B.nuNode hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) LP'
  have hN' : NodePlaced st T (L.wr s b v) (L.cpu (L.wr s b v)) := by
    rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) hN
  obtain ⟨kX, cX, -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN hcT LP
  obtain ⟨kX', cX', -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN' (by rw [ecur]; exact hcT) LP'
  refine ⟨X, LP, ⟨?_, ?_, hag⟩⟩
  · rw [kX', kX, L.ksb_wr]
  · rw [cX', cX, L.cpu_wr]

variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The common words at a prefix state are `NU`** (`slCom_nu` at `SlLX`). -/
theorem slCom_nuX (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : SlCom (L := L) (NU K) X := by
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU K (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 => by rw [nX]; exact B.nuNode E.hN h1 h2
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem X (L.nodeAt X (L.cpu X) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 h3 h4 => by
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN h1 h2) (not_slDS_node E.hN E.hT E.hcT h1 h3 h4)
  have eTm : L.mem X (tmA (L := L) X) = L.mem s (tmA (L := L) s) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) :=
    eN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  refine ⟨nd, ?_, ?_, ⟨nd _ (by simp [l1Off]) (by simp [l1Off]), fun inv hinv => nd _ (by simp; omega)
    (by simp <;> omega)⟩, fun h => ?_, fun h => ?_⟩
  · rw [kX]; exact B.nuKs E.hN (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact B.nuKs E.hN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, -, -⟩ := tm_of ar hA hX (slSets_conv K) E hk hcp LP h
    exact nu_tcb hX ht (o := 3528#u64) (by simp) (by simp) (by simp)
  · rw [eRh] at h ⊢
    obtain ⟨ht, hz, hin, hmx, -⟩ := rh_of ar hA hX (slSets_conv K) E hk hcp LP h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    refine ⟨nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp), ?_⟩
    generalize L.mem s (scA (L.mem s (rhA (L := L) s))) = sc at hz hin hmx
    obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
    have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
      lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 hk hcp
        (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
    have hW : RefillsWF st X sc (K.heap.scBits sc) :=
      ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
    exact ScAcc.head (R := NU K) (W := fun _ => True)
      ⟨fun b ha hb => nu_sc hX hz ha hb, fun _ _ _ => trivial, trivial⟩ hW

/-- **The trap arm's read words at a prefix state are `NU`** (`fltDec_nu` at `SlLX`). -/
theorem fltDec_nuX (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : FltDec (L := L) (NU K) X (L.curW s) := by
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_nuX ar hA B E LP
  have hcH := E.hSt.1
  have fs := nu_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  obtain ⟨hs, -, r8, -, a0, a8⟩ := hX.tslot _ hcH layout.tcb.SLOT_FAULT_HANDLER
    (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have nd0 : ¬ SlDS (L := L) s (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [hK.slot _ hs]; intro c h; cases h)
      (by rw [hK.slot _ hs]; intro h; cases h)
  have nd8 : ¬ SlDS (L := L) s (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h)
  refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, fs, fun ptr bb x y g gr hcap => ?_⟩
  have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP a0 nd0) (lp_mem ar hA E.hT E.hN E.hcT LP a8 nd8)
  have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr bb x y g gr) := by
    rw [← ecap]; exact hcap
  have hpH : K.heap ptr = some .ep := by
    have h := B.hep ⟨ptr, bb, x, y, g, gr, hcap'⟩
    rwa [resPtr_ok hcap'] at h
  refine ⟨nu_ep hX hpH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE]), nu_ep hX hpH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD])
    (by simp [layout.ep.HEAD]), fun hst d hd => ?_⟩
  have hst' : L.epState X ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) X ptr)] at hst; exact ok_inj_ff hst
  have hdd : d = L.mem X (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) X ptr)] at hd; exact (ok_inj_ff hd).symm
  have hdT : K.heap d = some .tcb := by
    rw [hdd]; exact vm_headT (E.hI a X a1 LP) hpH hst'
  exact ⟨nu_tcb hX hdT (o := 3360#u64) (by simp) (by simp) (by simp),
    nu_tcb hX hdT (o := 3520#u64) (by simp) (by simp) (by simp),
    fun _ => ⟨nu_tcb hX hdT (o := 3432#u64) (by simp) (by simp) (by simp),
      nu_tcb hX hdT (o := 3464#u64) (by simp) (by simp) (by simp),
      nu_tcb hX hdT (o := 3592#u64) (by simp) (by simp) (by simp),
      nu_tcb hX hdT (o := 3448#u64) (by simp) (by simp) (by simp)⟩⟩

/-- **`SlAccR` survives a user-word write** (`SlJAt.accR_wr` at `SlLX`). -/
theorem SlLX.accR_wr (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) (R : SlAccR (st := st) ar K Locks found s) :
    SlAccR (st := st) ar K Locks found (L.wr s b v) := by
  refine ⟨fun hS' a X' a1 LP' ptr badge dest r C => ?_⟩
  have hS := (B.trap_wr hb hba v).1 hS'
  rw [B.curW_wr hb hba v] at C
  rw [hl]
  obtain ⟨X, LP, G⟩ := B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
  exact R.frl hS a X a1 LP (flt_chk_back (fltDec_nuX ar hA B E LP) G C)

/-- **The fault handler's endpoint at a prefix state is a heap endpoint** (`flt_ptr_ep` at `SlLX`). -/
theorem flt_ptr_epX (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (C : FaultChecks st X (L.curW s) ptr badge dest r) : K.heap ptr = some .ep := by
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have hcH := E.hSt.1
  obtain ⟨hs, -, r8, -, a0, a8⟩ := hX.tslot _ hcH layout.tcb.SLOT_FAULT_HANDLER
    (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have nd0 : ¬ SlDS (L := L) s (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [hK.slot _ hs]; intro c h; cases h)
      (by rw [hK.slot _ hs]; intro h; cases h)
  have nd8 : ¬ SlDS (L := L) s (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h)
  obtain ⟨-, ⟨sl, x, y, g, gr, hS, hcap, -⟩, -⟩ := C
  have esl : sl = fhA (L := L) s := by rw [tcb_slot_val] at hS; exact (ok_inj_ff hS).symm
  subst esl
  have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP a0 nd0) (lp_mem ar hA E.hT E.hN E.hcT LP a8 nd8)
  have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr badge x y g gr) := by
    rw [← ecap]; exact hcap
  have h := B.hep ⟨ptr, badge, x, y, g, gr, hcap'⟩
  rwa [resPtr_ok hcap'] at h

/-- **`ep` / `hrp` with the `n = SysReplyRecv` guard** (`SlJAt.rrG` at `SlLX`). -/
theorem SlLX.rrG (B : SlLX (L := L) K s) (h : SlFoundRC st n found s) :
    ¬ SlTrap st s → n = fl4_abi.syscall.SysReplyRecv →
      K.heap found.1 = some .reply ∧ K.heap found.2 = some .ep :=
  fun hS hn => B.ft found (h.rc hS hn)

/-- **The ReplyRecv checks' read words at a prefix state are `NU`** (`rrDR_nu` at `SlLX`). -/
theorem rrDR_nuX (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hC : SlSyncC st n found s) (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    RrDR (L := L) (NU K) X (L.curW s) found.1 found.2 := by
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_nuX ar hA B E LP
  have hcH := E.hSt.1
  obtain ⟨hrp, hep⟩ := B.rrG hC.fd hS (hC.arm hS)
  obtain ⟨⟨Q, Rq, hq⟩, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      NU K (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 h3 => nu_tcb hX hy h1 h2 h3
  have uT : ∀ u, L.mem X (rTcbA found.1) = u → u ≠ 0#u64 → K.heap u = some .tcb := fun u hu hu0 => by
    obtain ⟨-, hT', -, -⟩ := hXI.2.1.back _ hrp (by rw [hu]; exact hu0)
    rw [hu] at hT'; exact hT'
  obtain ⟨KM, hKM, eKM⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.MSG_INFO)
    (by simp [layout.reg.MSG_INFO])
  refine ⟨C.nd, C.dt, C.cd, C.tm, C.rh, tw _ hcH layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
    (by rw [st_val]), tw _ hcH 3464#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    tw _ hcH 3592#u64 (by simp) (by simp) (by simp), ?_, tw _ hcH 3368#u64 (by simp) (by simp) (by simp),
    tw _ hcH 3448#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    nu_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB]),
    nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT]),
    nu_ep hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE]),
    fun u hu hu0 => ?_, fun u hu hu0 _ => ?_, fun u hu hu0 _ hst hsc => ?_⟩
  · have hz := scs_heap (K := K) (hX0.bound _ hcH h0).1
    exact nu_scw hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  · have hKM' : KM.val = 256 + 8 * layout.reg.MSG_INFO.val := hKM
    rw [eKM]
    exact tw _ hcH KM (by rw [hKM']; simp [layout.reg.MSG_INFO]) (by rw [hKM']; simp [layout.reg.MSG_INFO])
      (by rw [hKM']; simp [layout.reg.MSG_INFO])
  · have eB : L.mem X (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hcH 3368#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT hcH hk hcp hcH (by simp) (by simp) (by simp) (by simp))
    have hn := (ntf_of ar hA hX (slSets_conv K) E hk hcp LP (by rw [← eB]; exact h0)).1
    rw [eB]
    obtain ⟨r1, -, a1⟩ := hX.ntW _ hn layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
      (by simp [layout.ntfn.TAIL_STATE])
    obtain ⟨r2, -, a2⟩ := hX.ntW _ hn layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    exact ⟨nu_of_region hX a1 (by rw [r1]; intro h; cases h), nu_of_region hX a2 (by rw [r2]; intro h; cases h)⟩
  · have hu' := uT u hu hu0
    exact ⟨tw _ hu' 3464#u64 (by simp) (by simp) (by simp), tw _ hu' 3520#u64 (by simp) (by simp) (by simp),
      tw _ hu' 3432#u64 (by simp) (by simp) (by simp), tw _ hu' 3448#u64 (by simp) (by simp) (by simp)⟩
  · have hu' := uT u hu hu0
    exact ⟨tw _ hu' layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega) (by rw [st_val]),
      tw _ hu' 3376#u64 (by simp) (by simp) (by simp), tw _ hu' 3592#u64 (by simp) (by simp) (by simp)⟩
  · have huT : u ∈ K.heap.tcbs := uT u hu hu0
    have hcS := (hX0.bound u huT hsc).1
    have hact := hB.sact u huT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) hsc
    have hWF := (hSC.all _ hcS).1 ((hSC.act _ hcS).1 hact)
    have hz := scs_heap (K := K) hcS
    exact ScAcc.head (R := NU K) (W := fun _ => True)
      ⟨fun b ha hb => nu_sc hX hz ha hb, fun _ _ _ => trivial, trivial⟩ hWF

/-- **The ReplyRecv-guarded fields of `SlPreB` across a user-word write** (`SlJAt.preRR_wr` at `SlLX`). -/
theorem SlLX.preRR_wr (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hC : SlSyncC st n found s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    SlPreRR (st := st) ar K Locks found K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits (L.wr s b v) := by
  have hX := B.regionOKX
  have ecur := B.curW_wr hb hba v
  have etr := B.trap_wr hb hba v
  have rws := B.slRWS_wr hb hba v Locks hl
  have back : ∀ a X' a1, LocalPre (st := st) ar (L.wr s b v) a (X', a1) →
      ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' :=
    fun a X' a1 LP' => B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
  refine ⟨fun hS' a X' a1 LP' u usc C => ?_, fun hS' a X' a1 LP' u usc C => ?_,
    fun hS' a X' a1 LP' u usc C => ?_⟩
  · have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
    rw [ecur] at C ⊢
    obtain ⟨X, LP, G⟩ := back a X' a1 LP'
    obtain ⟨hrp, hep⟩ := B.rrG hC.fd hS (hC.arm hS)
    have C0 := rr_chk_backG (rrDR_nuX ar hA B E hC hS LP) G C
    exact rrPl_ag hX (slCom_nuX ar hA B E LP).nd hrp hep (E.hI a X a1 LP) G (E.hPl hS a X a1 LP u usc C0)
  · have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
    rw [ecur] at C
    obtain ⟨X, LP, G⟩ := back a X' a1 LP'
    have C0 := rr_chk_backG (rrDR_nuX ar hA B E hC hS LP) G C
    have hu := (E.hSu hS a X a1 LP u usc C0).1
    rw [G.m (yieldA u) (nu_tcb hX hu (o := 3472#u64) (by simp) (by simp) (by simp))]
    exact E.hy0r hS a X a1 LP u usc C0
  · have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
    rw [ecur] at C ⊢
    obtain ⟨X, LP, G⟩ := back a X' a1 LP'
    have C0 := rr_chk_backG (rrDR_nuX ar hA B E hC hS LP) G C
    obtain ⟨h1, h2, h3, h4, h5⟩ := E.hSu hS a X a1 LP u usc C0
    rw [L.cpu_wr, hl, rws.2]
    exact ⟨h1, safe0_wr hX hb hba v h1 h2, h3, h4, h5⟩

/-- **`SlPreB` across a user-word write, no P3 bundle** (`SlJAt.preB_wrN` at `SlLX`; `BXI` by VX2's
`bxi_userX`). -/
theorem SlLX.preB_wrN (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hCs : ∀ c ∈ Cs, c.val < 64) (hC : SlSyncC st n found s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s)
    (R : SlPreRR (st := st) ar K Locks found K.heap.tcbs Cs Ω Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits (L.wr s b v)) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v) := by
  have hX := B.regionOKX
  have hK := B.regionOK
  have ecur := B.curW_wr hb hba v
  have etr := B.trap_wr hb hba v
  have rws := B.slRWS_wr hb hba v Locks hl
  have back : ∀ a X' a1, LocalPre (st := st) ar (L.wr s b v) a (X', a1) →
      ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' ∧ L.ksb X = L.ksb s :=
    fun a X' a1 LP' => by
      obtain ⟨X, LP, G⟩ := B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
      obtain ⟨kX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
      exact ⟨X, LP, G, kX⟩
  refine
  { hT := E.hT
    hN := by rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) E.hN
    hcT := by rw [ecur]; exact E.hcT
    hI := fun a X' a1 LP' => by
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact Fl4Proofs.P2.E2EP.bxi_userX B.ul (kX.trans B.kc.1) hCs (E.hI a X a1 LP) G
    hAs := fun a X' a1 LP' => by
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact asidOff_agN (fun hi hhi => B.nuAsid kX hhi) G (E.hAs a X a1 LP)
    aff := fun d hd => by
      rw [E.aff d hd]
      exact (wr_nu (x := fld d oAFFINITY) hba hb v
        (nu_tcb hX hd (by rw [oAFF_val]; omega) (by rw [oAFF_val]; omega) (by rw [oAFF_val]))).symm
    hSt := by
      rw [ecur, L.cpu_wr, hl]
      exact ⟨E.hSt.1, safe0_wr hX hb hba v E.hSt.1 E.hSt.2⟩
    hrecv := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nuX ar hA B E LP) G C
      have hd := (E.hSd hS a X a1 LP C0).1
      rw [G.m (stA dest) (nu_tcb hX hd (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))]
      exact E.hrecv hS a X a1 LP C0
    hF := fun hS' a X' a1 LP' => by
      have hS := etr.1 hS'
      rw [ecur]
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      refine ⟨asidOff_agN (fun hi hhi => B.nuAsid kX hhi) G (E.hF hS a X a1 LP).1,
        fun ptr badge dest r C => ?_⟩
      have C0 := flt_chk_back (fltDec_nuX ar hA B E LP) G C
      obtain ⟨hr, rest, F⟩ := (E.hF hS a X a1 LP).2 ptr badge dest r C0
      exact ⟨hr, rest, faultEnt_ag hK hX (fun y hy => hy) (flt_ptr_epX ar hA B E LP C0)
        (E.hSd hS a X a1 LP C0).1 (slCom_nuX ar hA B E LP).nd G F⟩
    hy0f := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nuX ar hA B E LP) G C
      have hd := (E.hSd hS a X a1 LP C0).1
      rw [G.m (yieldA dest) (nu_tcb hX hd (o := 3472#u64) (by simp) (by simp) (by simp))]
      exact E.hy0f hS a X a1 LP C0
    hTm := fun hS' a X' a1 LP' => by
      have hS := etr.1 hS'
      obtain ⟨X, LP, G, kX⟩ := back a X' a1 LP'
      exact timerOK_agN hX (fun y hy => hy) (fun c hc hN o ho h8 => B.nuNode64 kX (hCs c hc) hN ho h8) G
        (E.hTm hS a X a1 LP)
    hSd := fun hS' a X' a1 LP' ptr badge dest r C => by
      have hS := etr.1 hS'
      rw [ecur] at C ⊢
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have C0 := flt_chk_back (fltDec_nuX ar hA B E LP) G C
      obtain ⟨h1, h2, h3, h4⟩ := E.hSd hS a X a1 LP C0
      rw [L.cpu_wr, hl, rws.2]
      exact ⟨h1, safe0_wr hX hb hba v h1 h2, h3, h4⟩
    hPl := R.hPl
    hrz := fun hS' a X' a1 LP' => by
      have hS : ¬ SlTrap st s := fun h => hS' (etr.2 h)
      obtain ⟨X, LP, G, -⟩ := back a X' a1 LP'
      have hrp : K.heap found.1 = some .reply := (B.rrG hC.fd hS (hC.arm hS)).1
      rw [G.m (rNextA found.1) (nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT])
          (by simp [layout.reply.NEXT])),
        G.m (rPrevA found.1) (nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV])
          (by simp [layout.reply.PREV]))]
      exact E.hrz hS a X a1 LP
    hy0r := R.hy0r
    hSu := R.hSu
    hlk := fun hS' => by rw [hl]; exact E.hlk (fun h => hS' (etr.2 h)) }

/-- **`SlPreB` across a user-word write, no P3 bundle, no `UserOK`** (`Cs` below 64 cores, `SlSyncC`, `hl` [P]). -/
theorem SlLX.preB_wrG (hA : P0.ArchTotal ar) (B : SlLX (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hCs : ∀ c ∈ Cs, c.val < 64) (hC : SlSyncC st n found s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v) :=
  B.preB_wrN ar hA E hCs hC hb hba v hl (B.preRR_wr ar hA E hC hb hba v hl)

/-- **`SlQ` across a user-word write at a `SlLX` state** (`slQ_wrG` without the bundle). -/
theorem slQ_wrX (hA : P0.ArchTotal ar) (hCs : ∀ c ∈ Cs, c.val < 64) {m : U64 → U64}
    (B : SlLX (L := L) K s) (q : SlQ st ar Locks n found Cs Ω Sg Ac K m s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) (hl : Locks (L.wr s b v) = Locks s) :
    SlQ st ar Locks n found Cs Ω Sg Ac K m (L.wr s b v) :=
  ⟨B.preB_wrG ar hA q.1 hCs q.2.2.1 hb hba v hl, B.entL_wr hb hba v hl q.2.1,
    B.syncC_wr hb hba v q.2.2.1, B.accR_wr ar hA q.1 hb hba v hl q.2.2.2⟩

/-- **`sl_localPathK`'s `huf` at `Pre := SlLX K ∧ SlQ K m`**, the locks from `KernDetS` [P] (no P3 bundle). -/
theorem sl_hufX (hA : P0.ArchTotal ar) (hCs : ∀ c ∈ Cs, c.val < 64) {m : U64 → U64}
    (hKD : ∀ s : S, SlLX (L := L) K s → KernDetS (L := L) K.user Locks s) :
    ∀ s b v, (SlLX (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s) → b ∈ K.user → Aligned b →
      (SlLX (L := L) K (L.wr s b v) ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m (L.wr s b v)) ∧
        Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K Locks (L.wr s b v) = SlRS (st := st) K Locks s ∧
        SlWS (st := st) K Locks (L.wr s b v) = SlWS (st := st) K Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s := by
  intro s b v hP hb hba
  have hl := hlk_of_kernelDetU (P := fun s => SlLX (L := L) K s) hKD s b v hP.1 hb hba
  have rws := hP.1.slRWS_wr hb hba v Locks hl
  exact ⟨⟨hP.1.wr hb hba v, slQ_wrX ar hA hCs hP.1 hP.2 hb hba v hl⟩, hl, rws.1, rws.2, hP.1.slDS_wr hb hba v⟩

end lx

/-! ## Consistency: every P3 bundle state has `SlLX` -/

section cons
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S}

/-- `CnOff` with the empty object sets and a smaller frame set. -/
theorem cnOff_empty {T Cs Sg Sg' : Set U64} {t : U64} (hS : ∀ x, x ∈ Sg' → x ∈ Sg)
    (h : CnOff (L := L) T Cs Sg s t) : CnOff (L := L) ∅ ∅ Sg' s t := by
  intro sl root hsl hroot
  obtain ⟨C, h1, h2, h3⟩ := h sl root hsl hroot
  refine ⟨C, h1, h2, fun p r m x hC hm => ?_⟩
  obtain ⟨c1, c2⟩ := h3 p r m x hC hm
  exact ⟨⟨⟨c1.1.1, fun _ ht => ht.elim, fun _ hc => hc.elim⟩, fun hx => c1.2 (hS _ hx)⟩,
    ⟨⟨c2.1.1, fun _ ht => ht.elim, fun _ hc => hc.elim⟩, fun hx => c2.2 (hS _ hx)⟩⟩

open Fl4Proofs.P3 in
/-- **Every P3 bundle state has `SlLX`** (the bundle's layout facts, `SlJAtZ.curTcb`, P3's node placement,
`SlJAtZ.hep`, `SlJAtZ.cnOffU`, `SlJAt.foundTyped`). The bundle's chain states satisfy P3's `SchedCore.aff`; the
lemma does not use it beyond what `SlJAt` already carries. -/
theorem SlLX.ofSlJAt (B : SlJAt (L := L) K s) : SlLX (L := L) K s where
  ul := Fl4Proofs.P2.E2EP.UserLayX.ofSlJAt B
  ok := B.regionOK
  uok := B.userOK
  ua := fun x hx hi hhi => by
    have h := B.userAsid hx hhi
    rwa [B.kc.1] at h
  kc := B.kc
  cur := by obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact B.curTcb
  np := by obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact TInv.nodes B.j.blk _ B.j.kern.cpuCs
  hep := by obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B; exact fun hE => B.hep hE
  cn := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
    exact cnOff_empty (fun x hx => Or.inr hx) (B.cnOffU (cur_thread_ok (L := L) s))
  ft := fun _ h => B.foundTyped h

end cons

end Fl4Proofs.P2.PathObl

/-! ## Part 3: `SlLX` in VM epochs -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW RegionOK LayP)

section vm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The syscall entry's state facts at a guest-running entry** [S] (module docstring): the entering core is one
of the layout's, the fault-handler endpoint cap and `reply_caps`' result are typed, the CSpace walk reads aligned
non-user slot words. Natively all four come from P3's bundle (`SlLX.ofSlJAt`). -/
structure SlEntS (K : KLayoutP) (s : S) : Prop where
  /-- [S] -/
  cpu : (L.cpu s).val < K.ncores
  /-- [S] -/
  hep : IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
    K.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep
  /-- [S] -/
  cn : CnOff (L := L) ∅ ∅ K.user s (L.curW s)
  /-- [S] -/
  ft : ∀ found : U64 × U64, (∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some found)) →
    K.heap found.1 = some .reply ∧ K.heap found.2 = some .ep

/-- **`SlLX` at a VM-epoch state** from the epoch's `VtxBundle` [S], `QPs`, P1's `SlPreB` at the state and
`SlEntS` [S]; no P3 bundle. -/
theorem SlLX.ofVtx {K : KLayoutP} {s : S} (E : VtxBundle st L K) (q : QPs K st s)
    {A : Type} {ar : machine.Arch A} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
    {Cs Ω Sg Ac : Set U64}
    (P : SlPreB (st := st) ar K.toKLayout Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (e : SlEntS K s) : SlLX (L := L) K.toKLayout s where
  ul := E.ul
  ok := E.ok
  uok := E.uok
  ua := fun x hx hi hhi => q.uoff x (Or.inl hx) hi hhi
  kc := ⟨q.ksb, e.cpu⟩
  cur := ⟨P.hSt.1, P.hT _ P.hcT⟩
  np := P.hN
  hep := e.hep
  cn := e.cn
  ft := e.ft

/-- **`SlEntS` at every P3 bundle state** (consistency of the [S]). -/
theorem slEntS_of_slJAt {K : KLayoutP} {s : S} (B : SlJAt (L := L) K.toKLayout s) : SlEntS K s :=
  have X := SlLX.ofSlJAt B
  ⟨X.kc.2, X.hep, X.cn, X.ft⟩

end vm

end Fl4Proofs.P2.E2EP
