/-
P2 (tmofr gen 3): **the P2 stall tops tied to P3.**

## What P3 gives, what it does not

* `XG` (P1 `QueueEntry`): `∃ s0, EntAt P3Ok s0 ∧ Fr0 s0 s`. In `stallAt.viewsT` /
  `stallAt.allT` the predicate `P3Ok` is a free parameter that occurs in no
  conclusion, so `XG` holds at **every** state with `P3Ok := fun _ => True`
  (`xg_triv`: `s0 := s`, `Ent s s` and `Fr0 s s` by reflexivity). Not a P3 fact:
  the premise was vacuous.
* `TmoCap` [P] (`hcap`) at the view of the stalled core `d`: **discharged at
  every `JAtZ` state**, for every `d` whose current thread is a TCB of `H`.
  `tmoCapW_of_JAtZt` (`JAtZ.timeoutTyped` at slot 4 of any TCB of `H`, through
  `JPlaced.tcb`) gives the cap typed at `s`; `tmoCap_of_capW` carries it to every
  state the budget check reaches (SC words — `Ω` by `XInv.scW` — and the core's
  node words miss the TCB's slot words 128/136); `tmoCap_view` is the view at `d`.
* Of `stallAt.viewsT`'s per-core premises, the **executing core's**
  (`c0 = L.cpu s`) follow from P3 at a reachable entry state
  (`kernel_entry_reachU29`'s `J` and `SInvX σ`):
  - `idleSc_of_JAtZ`: `IdleSc c0` (`SchedSpec.idleSc`, `SchedSpec.tcb`'s SC word of
    the idle thread, l4v `valid_idle`'s `tcb_sched_context = Some idle_sc`,
    `SInvI.vi_idle`);
  - `curNB_of_JAtZ`: `c0`'s current thread is not `Blocked` (ct = idle: `TS_IDLE`;
    otherwise `SInvX.entered` and `JAtZ.curRunnable`: runnable state word);
  - `CoreInv c0` (`EntryInv.toView` of `JAtZ.entryInv` and `idleSc_of_JAtZ`), `hnq` at
    `c0` (`JAtZ.curQ0`), `hidS` at `c0` (`JAtZ.idleTS`).
* **Not derivable from P3** (named in the theorems below, P2's all-core
  invariant `AllCores` supplies them): every fact about a core `c ≠ c0`'s node
  words (`CUR_THREAD`, `IDLE_THREAD`, `SCHED_ACTION`, `CUR_SC`, `IDLE_SC`) and
  the threads they name. P3's relation ties only the executing core's node to
  the spec (`SchedRel … Z.c`, `SchedCore.cur : L.cpu s = Z.c`; `JKern.cur`); the
  spec (l4v's abstract seL4) has one current thread, one idle thread and one
  scheduler action, and no counterpart of other cores' nodes. Hence:
  `EntryInv` at the view of `d ≠ c0`, `IdleSc d`, `hnq`/`hidS` at `d`, the other
  cores' `CoreInv` and `curNB`, and `hown`/`hactK` (the set `OtherK d` is made of
  the other cores' idle/current/action threads; even for `d = c0` it names
  only cores `≠ c0`).

## Here

* `xg_triv`, `tmoCap_of_capW`, `tmoCap_view`, `tmoCapW_of_JAtZt`.
* **`stallAt.allZ`**: at every `JAtZ` state (mid-entry included), a remote stall
  of `d` from `AllCores` over `H`'s sets ends in `AllCores`: `stallAt.allT` with
  `XG` and `TmoCap` [P] gone. Input `AllCores` only.
* **`stallAt.allJ`**: from every `JReachU17` entry state, premises
  `kernel_entry_domInvU29`'s only: some `H Cs Ac` with `L.cpu s ∈ Cs`, P1's
  `EntryInv`, and every stall of a `d ∈ Cs` from `AllCores` ends in `AllCores`.
* **`stallAt.viewsZ`**: `stallAt.viewsT` at a `JAtZ` state without `XG` and
  `TmoCap`.
* **`stallAt.viewsJ`** (remote `d ≠ c0`) and **`stallAt.viewsJ0`** (`d = c0`):
  from every `JReachU17` entry state, premises `kernel_entry_reachU29`'s
  (= `kernel_entry_domInvU29`'s); the executing core's facts discharged; left:
  the facts about cores `≠ c0` listed above.

No existing statement changed.
-/
import Fl4Proofs.P2.StallAllT
import Fl4Proofs.P2.TmoFrE
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **`XG` holds at every state** for the entry predicate `fun _ => True`. -/
theorem xg_triv (s : S) : XG st T Cs Ω H Sg Scs Z (fun _ => True) s :=
  EntAt.xg ⟨s, trivial, WritesIn.refl _ _⟩

/-- **`TmoCap` from the cap typed at `s`**: the budget check's writes (SC words,
the core's node words) miss the current thread's timeout slot words. -/
theorem tmoCap_of_capW {s : S} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcw : TmoCapW st H Rp Nt s (L.curW s)) : TmoCap st Scs Z H Rp Nt s := by
  intro s' hw
  obtain ⟨⟨Q, R, q⟩, -, hX, -⟩ := h
  have hcT : L.curW s ∈ T := q.curT
  have KK : ∀ K : U64, K.val < 192 → K.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K hK h8 => by
      have hal := field_aligned (q.tcbs _ hcT) (show K.val < 4096 by omega) h8
      refine hw.mem_eq hal ?_
      rintro (⟨c, hc, hin⟩ | ⟨o, -, ho, -, e⟩)
      · exact out_ne_field (K := K) (q.omega _ (hX.1.scW c hc _ hal hin)) hcT (q.tcbs _ hcT) (by omega) rfl
      · exact node_ne_field (q.nodes _ q.cur) ho hcT (q.tcbs _ hcT) (by omega) e.symm
  exact (hcw.of_eq (KK 128#u64 (by simp) (by simp)) (KK 136#u64 (by simp) (by simp))).slot

/-- `tmoCap_of_capW` at the view of core `d`. -/
theorem tmoCap_view {d : U64} {s : S} (h : @EntryInv S (atCpu st d) (L.atCpu d) T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcw : TmoCapW st H Rp Nt s (curAt st d s)) : @TmoCap S (atCpu st d) (L.atCpu d) Scs Z H Rp Nt s :=
  tmoCap_of_capW (st := atCpu st d) (L := L.atCpu d) h hcw

end

open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **Every TCB's timeout handler cap is typed at a `JAtZ` state**
(`tmoCapW_of_JAtZ` for any TCB of `H`, not only the current thread). -/
theorem tmoCapW_of_JAtZt {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Zx : XSets} {H : Heap}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a σ) {t : U64} (ht : t ∈ Heap.tcbs H) :
    TmoCapW st H (Heap.replies H) (Heap.ntfns H) s t := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hsl : IsSlot Zx.th (core.num.U64.wrapping_add t 128#u64) :=
    ⟨t, 4, Or.inr ⟨(hJ.tcb t).2 ht, by simp [tcbSlots]⟩, slotOf4 _⟩
  have h1 := J.timeoutTyped hsl
  rw [slot_cap_dec, tmoSlot8_eq] at h1
  exact h1

/-- **The executing core's `IdleSc` at a `JAtZ` state** where the spec's idle
thread is valid (l4v `valid_idle`: its SC is `idle_sc`). -/
theorem idleSc_of_JAtZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Zx : XSets} {H : Heap}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a σ) (hv : SInvAll.SInvCQ σ) : IdleSc st (L.cpu s) s := by
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨y, hy, -, -, hysc, -⟩ := SInvI.vi_idle hv.1.1.1.vi
  obtain ⟨x, hkx, -, -, hxsc, -⟩ := hs.tcb _ hc.idleT
  rw [hs.idleTh, hkx] at hy
  cases hy
  rw [hysc] at hxsc
  have hw : (L.mem s (P1.scA (nodeW st s Zx.c layout.node.IDLE_THREAD))).bv = σ.idleSc :=
    (Notif.optRef_some hxsc.symm).2
  unfold IdleSc
  rw [hc.cur]
  exact Fl4Proofs.P3.Sched.bv_inj (hs.idleSc.trans hw.symm)

/-- **The executing core's current thread is not blocked at an entry state**
(`SInvX`: the idle thread, or a runnable thread when entered). -/
theorem curNB_of_JAtZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Zx : XSets} {H : Heap}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a σ) (hX : SInvX σ) :
    ¬ Blocked (L.mem s (P1.stA (L.curW s))) := by
  by_cases hct : σ.curThread = σ.idleThread
  · obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
    have ecw : L.curW s = nodeW st s Zx.c layout.node.CUR_THREAD := by
      unfold P1.LawfulStore.curW nodeW; rw [hc.cur]
    have eiw : L.idleW s = nodeW st s Zx.c layout.node.IDLE_THREAD := by
      unfold P1.LawfulStore.idleW nodeW; rw [hc.cur]
    have e : L.curW s = L.idleW s := by
      rw [ecw, eiw]
      exact Fl4Proofs.P3.Sched.bv_inj (hs.curThread.symm.trans (hct.trans hs.idleTh))
    rw [e, J.idleTS hX.cq.idleSt]
    exact tsIdle_nb
  · have hni := hX.entered hct
    obtain ⟨-, x, hkx, hrx⟩ := J.curRunnable hni (cur_thread_curW (L := L) s)
    have hcT : L.curW s ∈ Zx.T := by rw [J.tcbs_eq.1]; exact J.kern.curH
    have hrun : Runnable (L.mem s (P1.stA (L.curW s))) := by
      show Runnable (L.mem s (P1.stA (L.curW s))); rw [stA_tStA]
      exact (runnable_iff (J.xtop.fin.1.1.2.2.1.at_tcb hcT hkx).st).2 hrx
    exact fun hb => blocked_not_runnable hb hrun

/-- **(tmofr gen 3) A remote stall from `AllCores` at a `JAtZ` state ends in
`AllCores`**: `stallAt.allT` with `XG` (vacuous, `xg_triv`) and `TmoCap` [P]
(`tmoCapW_of_JAtZt`, `tmoCap_view`) discharged. Input: `AllCores` over `H`'s
sets (P2's all-core invariant). No named premise. -/
theorem stallAt.allZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Zx : XSets} {H : Heap}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a σ) {A' : Type} {ar : machine.Arch A'} (hA : P0.ArchTotal ar)
    {Cs Ac : Set U64} (d : U64) (hd : d ∈ Cs) (a0 : A')
    (h : AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
      (Heap.scBits H) Ac s) :
    stallAt st ar d s a0 ⦃ s' _ =>
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s' ∧ curAt st d s' = idleAt st d s' ∧
      (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ⦄ :=
  stallAt.allT (P3Ok := fun _ => True) hA d hd s a0 h
    (xg_triv (st := atCpu st d) (L := L.atCpu d) s)
    (tmoCap_view (h.inv d hd).1 (tmoCapW_of_JAtZt J (h.core hd).per.curT))

set_option maxHeartbeats 1000000 in
/-- **(tmofr gen 3) A remote stall keeps the invariants at every core's view,
at a `JAtZ` state**: `stallAt.viewsT` without `XG` and `TmoCap` [P]. Named
premises as `stallAt.views`: `hown`, `hactK`, `hcurNB`, `hnq` [J] (other cores'
node words, not in P3's relation). -/
theorem stallAt.viewsZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Zx : XSets} {H : Heap}
    {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a σ) {A' : Type} {ar : machine.Arch A'} (hA : P0.ArchTotal ar)
    {Cs Ac : Set U64} (d : U64) (a0 : A')
    (h : @EntryInv S (atCpu st d) (L.atCpu d) (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H)
      (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s)
    (hI : IdleSc st d s)
    (hC : ∀ c ∈ Cs, c ≠ d → CoreInv st (Heap.tcbs H) Cs (Heap.scs H) (Heap.scBits H) Ac c s)
    (hown : curAt st d s ∉ OtherK st (Heap.tcbs H) Cs d s)
    (hactK : actAt st d s ∈ Heap.tcbs H → actAt st d s ∉ OtherK st (Heap.tcbs H) Cs d s)
    (hcurNB : ∀ c ∈ Cs, c ≠ d → ¬ Blocked (L.mem s (P1.stA (curAt st c s))))
    (hnq : curAt st d s ≠ idleAt st d s → (L.mem s (P1.inqA (curAt st d s)) &&& sched.Q_QUEUED) = 0#u64)
    (hidS : L.mem s (P1.stA (idleAt st d s)) = sched.TS_IDLE) :
    stallAt st ar d s a0 ⦃ s' _ =>
      (∀ c ∈ Cs, @EntryInv S (atCpu st c) (L.atCpu c) (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H)
        (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ∧ IdleSc st c s') ∧
      OKeep st (Heap.tcbs H) Cs (Heap.scs H) (OtherK st (Heap.tcbs H) Cs d s) d s s' ∧
      curAt st d s' = idleAt st d s' ∧
      (actAt st d s' = actAt st d s ∨ actAt st d s' = 0#u64) ∧ (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ∧
      L.mem s' (P1.stA (idleAt st d s)) = sched.TS_IDLE ⦄ := by
  have hcT : curAt st d s ∈ Heap.tcbs H := by
    obtain ⟨⟨Q, R, q⟩, -⟩ := h
    exact q.curT
  exact stallAt.viewsT (P3Ok := fun _ => True) hA d s a0 h hI
    (xg_triv (st := atCpu st d) (L := L.atCpu d) s) (tmoCap_view h (tmoCapW_of_JAtZt J hcT))
    hC hown hactK hcurNB hnq hidS

set_option maxHeartbeats 4000000 in
/-- **(tmofr gen 3) A remote stall of `d` from `AllCores` ends in `AllCores`,
from every reachable entry state** (`stallAt.allZ` at `kernel_entry_domInvU29`'s
`J`). Premises: `kernel_entry_domInvU29`'s only; input `AllCores` (P2). -/
theorem stallAt.allJ {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (d : U64) (a0 : A), d ∈ Cs →
      AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s →
      stallAt st arI d s a0 ⦃ s' _ =>
        AllCores st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
          (Heap.scBits H) Ac s' ∧ curAt st d s' = idleAt st d s' ∧
        (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, -⟩ :=
    kernel_entry_domInvU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, J.kern.cpuCs, hI, fun d a0 hd h => stallAt.allZ J hA d hd a0 h⟩

set_option maxHeartbeats 4000000 in
/-- **(tmofr gen 3) A remote stall of a core `d ≠ L.cpu s` keeps the
invariants at every core's view, from every reachable entry state.** Premises:
`kernel_entry_reachU29`'s (= `kernel_entry_domInvU29`'s). The executing core's
`CoreInv` and `curNB` are discharged (`idleSc_of_JAtZ`, `curNB_of_JAtZ`), `XG` and
`TmoCap` too. Named premises left, all about cores other than the executing
one (not in P3's relation, module docstring): `hE`, `hI`, `hnq`, `hidS` [J] (core
`d`'s), `hC`, `hcurNB` [J] (the cores `∉ {d, L.cpu s}`), `hown`, `hactK` [J]
(`OtherK d`). -/
theorem stallAt.viewsJ {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (d : U64) (a0 : A), d ∈ Cs → d ≠ L.cpu s →
      ∀ (hE : @EntryInv S (atCpu st d) (L.atCpu d) (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H)
          (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s)
        (hI : IdleSc st d s)
        (hC : ∀ c ∈ Cs, c ≠ d → c ≠ L.cpu s → CoreInv st (Heap.tcbs H) Cs (Heap.scs H) (Heap.scBits H) Ac c s)
        (hown : curAt st d s ∉ OtherK st (Heap.tcbs H) Cs d s)
        (hactK : actAt st d s ∈ Heap.tcbs H → actAt st d s ∉ OtherK st (Heap.tcbs H) Cs d s)
        (hcurNB : ∀ c ∈ Cs, c ≠ d → c ≠ L.cpu s → ¬ Blocked (L.mem s (P1.stA (curAt st c s))))
        (hnq : curAt st d s ≠ idleAt st d s → (L.mem s (P1.inqA (curAt st d s)) &&& sched.Q_QUEUED) = 0#u64)
        (hidS : L.mem s (P1.stA (idleAt st d s)) = sched.TS_IDLE),
      stallAt st arI d s a0 ⦃ s' _ =>
        (∀ c ∈ Cs, @EntryInv S (atCpu st c) (L.atCpu c) (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H)
          (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ∧ IdleSc st c s') ∧
        OKeep st (Heap.tcbs H) Cs (Heap.scs H) (OtherK st (Heap.tcbs H) Cs d s) d s s' ∧
        curAt st d s' = idleAt st d s' ∧
        (actAt st d s' = actAt st d s ∨ actAt st d s' = 0#u64) ∧ (∀ c ∈ Cs, c ≠ d → actAt st c s' = actAt st c s) ∧
        L.mem s' (P1.stA (idleAt st d s)) = sched.TS_IDLE ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  have hI0 := J.entryInv hX.cr.2
  refine ⟨H, Cs, Ac, J.kern.cpuCs, hI0, fun d a0 hd hne hE hI hC hown hactK hcurNB hnq hidS => ?_⟩
  refine stallAt.viewsZ J hA d a0 hE hI (fun c hc hcd => ?_) hown hactK (fun c hc hcd => ?_) hnq hidS
  · by_cases e : c = L.cpu s
    · subst e
      exact CoreInv.of (EntryInv.toView hI0) (idleSc_of_JAtZ J hX.cq)
    · exact hC c hc hcd e
  · by_cases e : c = L.cpu s
    · subst e
      exact curNB_of_JAtZ J hX
    · exact hcurNB c hc hcd e

set_option maxHeartbeats 4000000 in
/-- **(tmofr gen 3) A stall of the executing core `L.cpu s` keeps the
invariants at every core's view, from every reachable entry state.** Premises:
`kernel_entry_reachU29`'s; the core's own `EntryInv` at its view, `IdleSc`,
`hnq`, `hidS` discharged, `XG` and `TmoCap` too. Named premises left (the other
cores', not in P3's relation): `hC`, `hcurNB`, `hown`, `hactK` [J]. -/
theorem stallAt.viewsJ0 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A)
        (hC : ∀ c ∈ Cs, c ≠ L.cpu s → CoreInv st (Heap.tcbs H) Cs (Heap.scs H) (Heap.scBits H) Ac c s)
        (hown : curAt st (L.cpu s) s ∉ OtherK st (Heap.tcbs H) Cs (L.cpu s) s)
        (hactK : actAt st (L.cpu s) s ∈ Heap.tcbs H →
          actAt st (L.cpu s) s ∉ OtherK st (Heap.tcbs H) Cs (L.cpu s) s)
        (hcurNB : ∀ c ∈ Cs, c ≠ L.cpu s → ¬ Blocked (L.mem s (P1.stA (curAt st c s)))),
      stallAt st arI (L.cpu s) s a0 ⦃ s' _ =>
        (∀ c ∈ Cs, @EntryInv S (atCpu st c) (L.atCpu c) (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H)
          (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ∧ IdleSc st c s') ∧
        OKeep st (Heap.tcbs H) Cs (Heap.scs H) (OtherK st (Heap.tcbs H) Cs (L.cpu s) s) (L.cpu s) s s' ∧
        curAt st (L.cpu s) s' = idleAt st (L.cpu s) s' ∧
        (actAt st (L.cpu s) s' = actAt st (L.cpu s) s ∨ actAt st (L.cpu s) s' = 0#u64) ∧
        (∀ c ∈ Cs, c ≠ L.cpu s → actAt st c s' = actAt st c s) ∧
        L.mem s' (P1.stA (idleAt st (L.cpu s) s)) = sched.TS_IDLE ⦄ := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, hX, -⟩ :=
    kernel_entry_reachU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  have hI0 := J.entryInv hX.cr.2
  refine ⟨H, Cs, Ac, J.kern.cpuCs, hI0, fun a0 hC hown hactK hcurNB => ?_⟩
  exact stallAt.viewsZ J hA (L.cpu s) a0 (EntryInv.toView hI0) (idleSc_of_JAtZ J hX.cq) hC hown hactK hcurNB
    (fun _ => J.curQ0 hX.ctQ) (J.idleTS hX.cq.idleSt)

end

end Fl4Proofs.P2.Stall
