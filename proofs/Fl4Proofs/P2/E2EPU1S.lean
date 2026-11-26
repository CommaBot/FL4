/-
# P2 (line satU, gen 1): start-level satisfiability of U1's io / st / irq / vx slots

`serializable_fl4_localU1` (P2/E2EPU2.lean, via `StartU1` / `StartU` of P2/E2EPU1.lean) had satisfiability lemmas
for vmF / vmR / sl / vt / delPte / CNodeDelete / Copy-Mint, but none for the io, st, irq and vx slots. This module
gives them, in the family of `startU_vmF_sat`: at an arbitrary state `σ` of the current chain (`Ch σ`), with the
slot's own entry fact from fl4-sync (below), the lemma constructs the record, the entry fact and the `StartU1`
disjunct at `m := L.mem σ`, core `L.cpu σ`, held set `lk σ` of the index's lock map. No assumption on the number of
cores and none on any state other than `σ`.

| slot | lemma | record (built) | entry (built) | inputs besides `Ch σ` and the index convention |
|---|---|---|---|---|
| io | `startU1_io_sat` | `IoPremW9`: `nv`, `hQ`, `kd`, `bunS` (= `σ`) | `IoEntJ9`: `ix` (`ioEntJ9_sat`), `hct` | `nv`, `hct` [P], `kd` [P] |
| st | `startU1_st_sat` | `StPremW3B`: `nv`, `bun` (= `σ`), `hQ`, `kd` | `StEntJ7`: `ix` (`bunIx_of`), `fd` | `nv`, `fd` (fl4-sync's `SetTimerFound`), `kd` [P] |
| irq | `startU1_irq_sat` | `K.vcpus = ∅ ∧ IrqPremK2B`: `bun` (= `σ`), `lt`, `kd`, `pl` | `Ch σ` | `nv`, `lt`, `kd` [P], `pl` [P] |
| vx | `startU1_vx_sat` | `VxPremP3E`: `nv`, `kd` | `VxEntJ8N`: `ix` (`bunIx_of`), `hv`, **`buf` derived** (`vxBuf_of`) | `nv`, `hv` (index choice `v := vOf σ`), `kd` [P] |

The entry conditions are fl4-sync's (`crates/fl4-sync/src/lib.rs`): io is `local_syscall`'s last arm
(`handle_ioport_local` with nothing locked: `observe(s, &[])`), st is `local_set_timer` (the `CAP` register's slot holds
a `Thread target` cap: `SetTimerFound`), irq is `local_timer_irq` (`plan_timer_irq` gives `p`, `with_locks` locks
`p`'s objects: `PlanLk`), vx is `local_vm_exit` (`l.vcpu = cur_vcpu s`: `hv`). The io / irq / vx lemmas need no
fact of the syscall / IRQ beyond these: the records and entry facts do not mention the syscall number, label or IRQ
line (the bodies decline themselves), so the lemmas hold at every chain state, in particular at the real entries.

## Vacuity check (no defect in the records)

- **No ∀-state field fixes a datum.** The only state-quantified record fields are the lock fields `kd` (io: at bundle
  states; st / vx: at every state; irq: at bundle states) and irq's `pl` (`PlanLk`: at every state the plan's
  objects are held). Neither mentions `m`. Both are satisfied by the lock map the glue actually has during a local
  run, the constant map `fun _ => hs` of its held set (the locks do not change while the body runs; fl4-sync takes
  them before `observe` and releases them after): `kernDetS_const`, `planLk_const`. With a constant map `kd` holds
  at every state, and `PlanLk` holds iff `hs` contains the plan's non-null notification / endpoint / reply, which is
  `with_locks`'s postcondition. So neither is contradicted by the actual locks (`startU1_io_satC`,
  `startU1_st_satC`, `startU1_irq_satC`, `startU1_vx_satC`: the four lemmas with the constant map, `kd` / `pl`
  discharged, io with `hs = ∅` as fl4-sync's port arm holds nothing).
  A *state-read* lock map (fl4-sync's lock words) would make `PlanLk` false (a state where the lock word is clear),
  and st / vx's unguarded `kd` false (a non-bundle state whose lookup walks a user word): the records are
  satisfiable only for constant-like maps. That is the index's choice, as for delPte (`planLocks p`), not a defect.
- **`m`-dependent facts are in the paths' `Pre`** (io's `IoQ`, vx's `VexitPEnt.aff0`), checked by the existing start
  conversions at the start state, where `m = L.mem σ`.
- **vx, scope note (not a record defect).** At P3 scope `K.vcpus = ∅` (every serial exit, `serC`), so every bundle
  state has `vOf st σ = 0` (`vOf_zero`) and the index's `v` is `0` (`vx_v0`). The slot starts (this lemma), but only
  at `v = 0`, where `handle_vcpu_exit_local` is the model's run and fl4-sync's `vm_local` declines before running it
  (`l.vcpu == 0`, lib.rs `vm_local`). A real VM exit (`cur_vcpu ≠ 0`) needs a VCPU in the layout, outside P3 scope —
  the same situation as vt's fire case (jsweep gen 2, `vt_noAcc`). Lifting it needs VCPUs in P3's layout (new
  `serC`), not a record change.

Named premises: `kd` [P] (as in the records; dischargeable by the constant map), `pl` [P] (`PlanLk`, idem),
`hct` [P] (`NonIdle`, as io's entry), `fd` (fl4-sync's `SetTimerFound`, st's entry [P]). vx's `buf` [P] is
**derived** here (`vxBuf_of`: `JAtZ.bufOK` + `JAtZ.bufU_B` + `EPlaced.balign`, as invj's `invBufJ8_of`). No new
[J] / [W] / [P]. No existing statement or file changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU2
import Fl4Proofs.P2.InvTrunc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)

noncomputable section
open Classical

/-! ## Lock maps the glue has: constant during a local run -/

section lk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **A constant lock map is determined by anything** (`kd` of every record, at every state). -/
theorem kernDetS_const (U : Set U64) (hs : U64 → Prop) (s : S) :
    KernDetS (L := L) U (fun _ : S => hs) s :=
  fun _ _ _ _ _ => rfl

/-- **`PlanLk` of a constant lock map**: the held set contains the plan's non-null objects (fl4-sync's
`with_locks` over `p.objects`, `local_timer_irq`). -/
theorem planLk_const (p : localtimer.TimerIrqPlan) (hs : U64 → Prop)
    (h : (p.ntfn ≠ 0#u64 → hs p.ntfn) ∧ (p.ep ≠ 0#u64 → hs p.ep) ∧ (p.reply ≠ 0#u64 → hs p.reply)) :
    PlanLk (fun _ : S => hs) p :=
  fun _ => h

end lk

/-! ## vx's `buf` at a bundle state -/

section buf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- **vx's `VxEntJ8N.buf` at every bundle state** (`JAtZ.bufOK`, `JAtZ.bufU_B`, `EPlaced.balign`, as
`invBufJ8_of`). No premise. -/
theorem vxBuf_of {K : KLayoutV} {s : S} (hJ : SlJAt (L := L) K.toKLayout s) :
    msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄ := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have hcur : L.curW s ∈ Heap.tcbs K.toKLayout.heap := B.j.kern.curH
  refine WP.spec_mono (B.j.bufOK hcur) fun w hw hne i hi => ?_
  obtain ⟨wp, hwp, e⟩ := B.j.bufU_B (hw hne i hi)
  refine ⟨?_, ?_⟩
  · show _ ∈ K.toKLayout.user
    rw [B.user]; exact ⟨wp, hwp, e⟩
  · rw [← e]; exact (B.j.xtop.fin.1.2.ep.balign _ hwp).1

/-- **At P3 scope vx's index has `v = 0`** (scope note in the module docstring): `hv` and `vOf_zero`. -/
theorem vx_v0 {K : KLayoutV} {i : VxArg S} {s : S} (hE : VxEntJ8N st i K s) : i.v = 0#u64 :=
  hE.hv.trans (vOf_zero hE.ix.ac.slJAt)

end buf

/-! ## The four start-level satisfiability lemmas -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {κ : Type}
  (SFQ : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → κ → Prop)

/-- **io's `StartU1` holds at every chain state with a non-idle current thread** (record `IoPremW9` and entry
`IoEntJ9` built; `m := L.mem σ`; any layout, any number of cores). Inputs: `nv` (P3 scope), `hct` [P], the index
convention (`Cs` / `Ω` / `Sg` / `Ac` the bundle's, `Q = IoQ`), `kd` [P]. -/
theorem startU1_io_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    (hct : NonIdle st arI AR MR σ) (a : A) :
    ∃ Ac : Set U64, ∀ j : IoArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac →
      j.Q = (fun K' m' s => IoQ st j.Cs j.Ω j.Sg j.Ac K'.toKLayout m' s) →
      (∀ s, SlJAt (L := L) K.toKLayoutV.toKLayout s → KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q
        (.inl (.io j)) := by
  obtain ⟨Ac, hE⟩ := ioEntJ9_sat st (K := K.toKLayoutV) (ChainOf.bun hC σ hσ) hct
  refine ⟨Ac, fun j e1 e2 e3 e4 hQ kd => ?_⟩
  have E := hE j e1 e2 e3 e4
  have h : IoPremW9 st j K.toKLayoutV (L.mem σ) := ⟨nv, hQ, kd, ⟨σ, E.ix.ac⟩⟩
  exact ⟨_, _, ⟨h, σ, a, ⟨hσ, E⟩, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **st's `StartU1` holds at every chain state where fl4-sync's `local_set_timer` found its target**
(`SetTimerFound`: the `CAP` register's slot holds `Thread target`; record `StPremW3B` and entry `StEntJ7` built,
pinned start; `m := L.mem σ`; any number of cores). Inputs: `nv`, `fd`, the index convention (`Q = StEntK`), `kd`
[P]. -/
theorem startU1_st_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {target : U64} (fd : Fl4Proofs.P3.SInvR.G5.SetTimerFound (L := L) σ target) (a : A) :
    ∃ Ac : Set U64, ∀ j : StArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.target = target →
      j.Q = (fun K' m' s => StEntK K'.toKLayout st K'.heap.tcbs j.Cs j.Ω K'.heap j.Sg K'.heap.replies
        K'.heap.scs K'.heap.ntfns K'.heap.scBits j.Ac j.target m' s) →
      (∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) (j.lk σ) q
        (.inl (.st j)) := by
  have hJ := ChainOf.bun hC σ hσ
  obtain ⟨Ac, BI⟩ := bunIx_of hJ
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 hQ kd => ?_⟩
  have E : StEntJ7 st j K.toKLayoutV σ := by
    refine ⟨?_, by rw [e5]; exact fd⟩
    rw [e1, e2, e3, e4]; exact BI
  have h : StPremW3B st j K.toKLayoutV (L.mem σ) := ⟨nv, ⟨σ, hJ⟩, hQ, kd⟩
  have hCs : ∀ c ∈ j.Cs, c.val < 64 := by
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, B⟩ := E.ix.ac
    exact fun c hc => B.j.kern.csLt c hc
  exact ⟨_, ((stSlotP3W st ar hA hm).liftAt j K.toKLayoutV (L.mem σ) hK.base hU.base
      (h.toA hCs).toW3.toP3).body σ a,
    ⟨h, σ, ⟨hσ, E⟩, fun _ => ⟨σ, a, rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩⟩, rfl⟩

/-- **irq's `StartU1` holds at every chain state** (record `K.vcpus = ∅ ∧ IrqPremK2B` built, entry `Ch σ`; any
number of cores). Inputs: `nv`, `lt` (the timer IRQ line below 128), `kd` [P], `pl` [P]. -/
theorem startU1_irq_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {j : IrqArg S} (lt : j.irq.val < 128)
    (kd : ∀ s, SlJAt (L := L) K.toKLayoutV.toKLayout s → KernDetS (L := L) (userV K.toKLayoutV).user j.lk s)
    (pl : PlanLk j.lk j.pl) (a : A) :
    ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) (j.lk σ) q (.inl (.irq j)) := by
  have h : K.vcpus = ∅ ∧ IrqPremK2B st j K.toKLayoutV (L.mem σ) :=
    ⟨nv, ⟨σ, ChainOf.bun hC σ hσ⟩, lt, kd, pl⟩
  exact ⟨_, _, ⟨h, σ, a, hσ, rfl, rfl, fun _ _ _ => rfl, rfl⟩, rfl⟩

/-- **vx's `StartU1` holds at every chain state** (record `VxPremP3E` and entry `VxEntJ8N` built, its `buf`
derived, pinned start; `m := L.mem σ`; any number of cores). Inputs: `nv`, the index convention (the bundle's sets,
`v := vOf st σ`, fl4-sync's `cur_vcpu`), `kd` [P]. At P3 scope `v = 0` (`vx_v0`, module docstring). -/
theorem startU1_vx_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    (a : A) :
    ∃ Ac : Set U64, ∀ j : VxArg S, j.T = K.heap.tcbs → j.Cs = {c : U64 | c.val < K.ncores} →
      j.Ω = K.heap.omega → j.H = K.heap → j.Sg = K.heap.frame → j.Rp = K.heap.replies → j.Scs = K.heap.scs →
      j.Nt = K.heap.ntfns → j.Z = K.heap.scBits → j.Ac = Ac → j.v = vOf st σ →
      (∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.lk s) →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) (j.lk σ) q
        (.inl (.vq (.inl j))) := by
  have hJ := ChainOf.bun hC σ hσ
  obtain ⟨Ac, BI⟩ := bunIx_of hJ
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hv kd => ?_⟩
  have E : VxEntJ8N st j K.toKLayoutV σ := by
    refine ⟨?_, hv, vxBuf_of st (K := K.toKLayoutV) hJ⟩
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]; exact BI
  have h : VxPremP3E st j K.toKLayoutV (L.mem σ) := ⟨nv, kd⟩
  exact ⟨_, ((vxSlotP3 st ar hA hm).path j K.toKLayoutV (L.mem σ) hK.base hU.base
      (h.toP3 (vxEu_of (m := L.mem σ) nv E))).body σ a,
    ⟨h, σ, ⟨hσ, E⟩, fun _ => ⟨σ, a, rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩⟩, rfl⟩

/-! ### With the glue's constant lock map (`kd` / `pl` discharged) -/

/-- **io with fl4-sync's port arm's locks** (nothing held: `Locks := fun _ _ => False`): no lock premise. -/
theorem startU1_io_satC {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    (hct : NonIdle st arI AR MR σ) (a : A) :
    ∃ Ac : Set U64, ∀ j : IoArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac →
      j.Q = (fun K' m' s => IoQ st j.Cs j.Ω j.Sg j.Ac K'.toKLayout m' s) → j.Locks = (fun _ _ => False) →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) (fun _ => False) q
        (.inl (.io j)) := by
  obtain ⟨Ac, H⟩ := startU1_io_sat st ar hA hm hSt a0 SFQ hK hU hC hσ nv hct a
  refine ⟨Ac, fun j e1 e2 e3 e4 hQ el => ?_⟩
  have := H j e1 e2 e3 e4 hQ (fun s _ => by rw [el]; exact kernDetS_const _ _ s)
  rw [el] at this
  exact this

/-- **st with a constant lock map** (the held set `hs` of `lookup_slot_locked`): no lock premise. -/
theorem startU1_st_satC {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {target : U64} (fd : Fl4Proofs.P3.SInvR.G5.SetTimerFound (L := L) σ target) (hs : U64 → Prop) (a : A) :
    ∃ Ac : Set U64, ∀ j : StArg S, j.Cs = {c : U64 | c.val < K.ncores} → j.Ω = K.heap.omega →
      j.Sg = K.heap.frame → j.Ac = Ac → j.target = target →
      j.Q = (fun K' m' s => StEntK K'.toKLayout st K'.heap.tcbs j.Cs j.Ω K'.heap j.Sg K'.heap.replies
        K'.heap.scs K'.heap.ntfns K'.heap.scBits j.Ac j.target m' s) → j.lk = (fun _ => hs) →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) hs q (.inl (.st j)) := by
  obtain ⟨Ac, H⟩ := startU1_st_sat st ar hA hm hSt a0 SFQ hK hU hC hσ nv fd a
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 hQ el => ?_⟩
  have := H j e1 e2 e3 e4 e5 hQ (fun s => by rw [el]; exact kernDetS_const _ _ s)
  rw [el] at this
  exact this

/-- **irq with fl4-sync's locks** (`with_locks` over the plan's objects: any constant held set containing the
plan's non-null notification / endpoint / reply): no lock premise. -/
theorem startU1_irq_satC {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    {j : IrqArg S} (lt : j.irq.val < 128) {hs : U64 → Prop} (el : j.lk = fun _ => hs)
    (hp : (j.pl.ntfn ≠ 0#u64 → hs j.pl.ntfn) ∧ (j.pl.ep ≠ 0#u64 → hs j.pl.ep) ∧
      (j.pl.reply ≠ 0#u64 → hs j.pl.reply)) (a : A) :
    ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) hs q (.inl (.irq j)) := by
  have := startU1_irq_sat st ar hA hm hSt a0 SFQ hK hU hC hσ nv lt
    (fun s _ => by rw [el]; exact kernDetS_const _ _ s) (by rw [el]; exact planLk_const _ _ hp) a
  rw [el] at this
  exact this

/-- **vx with a constant lock map** (the held set of `vm_locks`): no lock premise. -/
theorem startU1_vx_satC {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ) (nv : K.vcpus = ∅)
    (hs : U64 → Prop) (a : A) :
    ∃ Ac : Set U64, ∀ j : VxArg S, j.T = K.heap.tcbs → j.Cs = {c : U64 | c.val < K.ncores} →
      j.Ω = K.heap.omega → j.H = K.heap → j.Sg = K.heap.frame → j.Rp = K.heap.replies → j.Scs = K.heap.scs →
      j.Nt = K.heap.ntfns → j.Z = K.heap.scBits → j.Ac = Ac → j.v = vOf st σ → j.lk = (fun _ => hs) →
      ∃ q, StartU1 st ar hA hm hSt a0 arI AR MR SFQ Ch K (L.mem σ) hK hU (L.cpu σ) hs q
        (.inl (.vq (.inl j))) := by
  obtain ⟨Ac, H⟩ := startU1_vx_sat st ar hA hm hSt a0 SFQ hK hU hC hσ nv a
  refine ⟨Ac, fun j e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hv el => ?_⟩
  have := H j e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 hv (fun s => by rw [el]; exact kernDetS_const _ _ s)
  rw [el] at this
  exact this

end sat

end
end Fl4Proofs.P2.E2EP
