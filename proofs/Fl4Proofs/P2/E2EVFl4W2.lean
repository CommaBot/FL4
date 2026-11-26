/-
P2 (line famw, gen 1): **`fl4LocW` with proofs already in the tree wired in** (wiring only; new definitions).

`P2/E2EVFl4W.lean`'s `fl4LocW` / `serializable_fl4_localW` are unchanged; this module builds `fl4LocW2` from the same
slots, swapping the I/O port, `TCB_SetTimer` and timer-interrupt slots, and proves the same end-to-end statement over
it (`serializable_fl4_localW2`, by `serializable_fl4_localG`). It also gives the VM paths' start obligations from
lvm's `vexitEnt_of` / `vexitPEnt_of` / `vtmEnt_of`.

**1. `ReadOnce` at `userV K` (`ro` [W] of `io` / `st` / `irq`).** Finding: no `K → userV K` transfer of `ReadOnce`
is needed (nor would one hold in general: `once_mono` goes from more user words to fewer, and at `userV K` the
VCPU data words become racy). hpzg's proofs are generic in the layout, and the route-U slots already build their
paths at the layout `userV K` with `RegionOK (userV K)` / `UserOK (userV K)` (`regionOK_userV` / `userOK_userV`):
* `io`: `io_hro` at `K := userV K`, `P := SlJAt K.toKLayout ∧ Q`, its `IoPre (userV K)` from the slot's `pe` by
  `ioPre_userV` (exactly what `io_localPathVG` does for the path itself);
* `st`: `st_hro` at `K := userV K` and the canonical sets: its `Pre` is `StEntK (userV K) …`, which is `StEntV`;
* `irq`: **`irq_hroV`** (new, 6 lines): `irq_hroJ3`'s proof with `IrqPreV` in place of `IrqPreJ3` — the entry
  facts from `IrqPreV.entM`, the fire case from `irq_pathObl_V`'s `acc`, then hpzg's `irq_once_alt` at `userV K`.
`SlotU.pullK` (a `SlotU.pull` whose record map may use `RegionOKV K` / `UserOKV K`) carries the new records.

**2. The I/O port's `uf` [J].** It bundled `Q`, the locks and the sets `IoRS` / `IoWS` / `IoDS` under writes of
`userV K`'s user words. Now:
* **`SlJAt.curW_wrVD`**: a write of a VCPU data word keeps the current thread (the `CUR_THREAD` node word lies in
  `[ksb, ksb + 288000)`, every VCPU off `[ksb, ksb + 304384)` by `VcpuKsOff`, a `VFacts` field);
* **`ioRWDS_wrV`**: at a bundle state `IoRS (userV K)` / `IoWS (userV K)` / `IoDS` are kept by any aligned write of a
  `userV K` user word, the locks kept (stpost's `SlJAt.ioRWDS_wrSt` at `userV K`: `own (userV K)` reads no such word,
  `E2E.ownDep` at `regionOK_userV` / `userOK_userV`; the current thread by `curW_wr` or `curW_wrVD`);
* the locks by slhuf's `hlk_of_kernelDetU` from **`kd` [P]** (`KernDetS (userV K).user` at bundle states, the same
  premise as the `st` / `irq` slots of `fl4LocW`);
* so `IoPremW2.uf` [J] is replaced by **`qf` [J]** (the caller's `Q` alone survives such a write) and `kd` [P].
Stpost gen 11's canonical `IoQ` (`hIw` [J]) is not on int/j15; with it `qf` would become that line's `hIw`.

**3. The VM paths' starts.** `vxPre_ofJ`: the vexit `Pre` (`VexitEnt ∧ VexitPEnt`) at a start from
`vexitEnt_of` (`ksv` / `vin` / `vfar` / `nfar` derived) and `vexitPEnt_of` (`vfit` / `pusr` derived); `vtPre_ofJ`:
the vtimer `Pre` (`VtmEnt`) from `vexitEnt_of` at the bound VCPU `vOf st s` and `vtmEnt_of` (`iq` / `kr` / `tab`
derived). Their layout premises are `VFacts` [J] (`VcpuHeap` / `VcpuTabOff` / `PoolObj`, already asked of the
`io` / `st` / `irq` / `sl` slots), `SlJAt` (P3's bundle at the start state), P1's sets convention and **`hvK` [J]**
(the exiting / bound VCPU is one of the layout's). **`vxSlot_startJ`** / **`vtSlotW_startJ`**: the glue's
`Fl4StepV.start` for these two slots, i.e. `SlotN.startAt` with those `Pre`s. What is left of `VexitEnt` per start:
`inv` (`BXI`), `lay` (`StLay`), `ntw`, `cs`, `aff`, `curAff`, `cscCore` [J] and `vlk` [P]; of `VexitPEnt`: `usr`
[J], `buf` [P], `aff0` [J]; of `VtmEnt` additionally `AsidOff` [J]. (`VexitEnt`'s `ksv` / `vin` / `vfar` / `nfar`
and `VtmEnt`'s `iq` / `kr` / `tab` are no longer asked.)

## Premise table diff vs `serializable_fl4_localW`

| slot | removed | added |
|---|---|---|
| `io` (`IoPremW2`) | `ro` [W]; `uf` [J] (`Q` + locks + `IoRS` / `IoWS` / `IoDS`) | `qf` [J] (`Q` only), `kd` [P] (`KernDetS (userV K).user`, as `st` / `irq`) |
| `st` (`StPremK2`) | `ro` [W] | — |
| `irq` (`IrqPremK2`) | `ro` [W] | — |
| `vx` start | `VexitEnt.ksv` / `vin` / `vfar` / `nfar` [J]; `VexitPEnt.vfit` / `pusr` | `hvK` [J] (via `vxSlot_startJ`; `VFacts` [J] as the other slots) |
| `vt` start | `VtmEnt`'s `iq` / `kr` / `tab` and its `VexitEnt` part's `ksv` / `vin` / `vfar` / `nfar` | `hvK` [J] at `vOf st σ` (via `vtSlotW_startJ`) |

Net: −3 [W] (`ro` of `io` / `st` / `irq`: of the five path-`ro` [W]s only `sl`'s and the VM paths' remain), the
`io` `uf` [J] narrowed to its `Q` part. The `vx` / `vt` records themselves are unchanged (their start lemmas are
new theorems for the glue's `start` [P]).

## `Fl4StepV.start` [P] and `Fl4StepV.ser` [J]: what would discharge them (plan, nothing proved here)

Both are per core step of `ExecV` (`P2/E2EV.lean`'s `Fl4StepV`). The P3 source is stpost's `loc_chain_all`
(`P2/SlJStLocTop.lean`): from `JReachU17` at the boot state `s0` it gives ONE layout
`K* := layoutJ Z H (L.ksb s0) nc` for the whole chain, with `RegionOK K*`, `UserOK K*`, `E2E.Maps K* c` at every
exit ghost `c` (`SerExit.ExitGhost`), and clauses 1–10 (exit; trap arm; ReplyRecv fast path; I/O port;
`TCB_SetTimer`; timer interrupt; **7: `SlJAt K* σ` at every chain state**; frame-cap invocation; VM fault;
VM ReplyRecv, with the fl4-sync `found` input).

* **`ser` [J]** (`SerStep s c → RegionOKV K' ∧ UserOKV K' ∧ MapsV K' s'`): take `K'` := `K*` extended by the
  VCPU list (`KLayoutV` over `K*`, `vcpus` the glue's choice). Then `RegionOKV.base` / `UserOKV.base` are
  `loc_chain_all`'s `hK` / `hU` (layout constant along the chain, so `keep` is trivial too). Missing:
  (a) `RegionOKV`'s VCPU fields `none` / `disj` / `tcbw` — from `VcpuHeap` [J] (VCPUs are `other 15` heap
  objects) with `HeapOK` disjointness, as `vcpuKs_of_jkern` / `noVcpu_of_obj` already do for `VcpuKs` (a ~60-line
  lemma `regionOKV_of_JAtZ`; `tcbw` is arithmetic); (b) `MapsV K' s'` from `E2E.Maps K* s'`: `own` differs
  (`ownV` vs `own` on VCPU words), so the glue's exit ghost must set `own := ownV K'` — a change of
  `SerExit.ExitGhost` (a definition in the glue model, [P]) or a new `ExitGhostV`; `cls` / `ko` agree as is.
* **`start` [P]** (`∃ i, StartAt (LP i K s.mem hK hU) c (locks of c) s.mem k`): for `fl4LocW2.paths D`, pick the
  `Fl4Ix` constructor of the body the glue starts; `SlotU/C/N.startAt` (for `vx` / `vt`: `vxSlot_startJ` /
  `vtSlotW_startJ`) reduce it to (a) the slot's premise record at `(K, s.mem)` and (b) the path's `Pre` at an
  entry store state `σ` with `cpu σ = c`, `Locks σ = locks of c`, `σ` agreeing with `s.mem` off user words, and
  `k = body σ a`. For (b): `SlJAt K σ` is clause 7; `IoPre` / `StEntK` / `VexitEnt.inv` (`BXI`) at the canonical
  sets come from `JAtZ.entryInv` (as in `SlJAtZ.stLay` / `slJAt_slotJC`); the `found` input of `vmR` / `sl` is
  clause 10 / 3. What is not in the tree: (i) the correspondence between the `Cfg` step
  `s.ph c = .loc p0 (.start k) W` and a store state `σ` on the chain (`k` is the extracted body run at `σ`, the
  memory / core / lock agreement) — the glue-refinement fact, genuinely [P]; (ii) the per-path caller facts `Q`
  (io / st), `VmRPre` / `RdTab` (vmR), `IrqPreV`'s memory agreement (by (i)). So `start` would shrink to (i) plus
  the slot records, once (i) is stated as one glue premise `GlueEntry` (core `c` starts body `F σ a` at a chain
  state `σ` matching `s`) and a lemma `start_of_glueEntry` per slot is written from the `*_startAt` lemmas.
-/
import Fl4Proofs.P2.E2EVFl4W
import Fl4Proofs.P2.StOnce
import Fl4Proofs.P2.TmOnce
import Fl4Proofs.P2.IoOnce
import Fl4Proofs.P2.SlJStLocStart
import Fl4Proofs.P2.AccessLvmTj
open Aeneas Aeneas.Std Result

/-! ## The current thread under a VCPU-data-word write -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The current thread is kept by a VCPU-data-word write** at a bundle state (module docstring, item 2). -/
theorem SlJAt.curW_wrVD {K : OwnMapV.KLayoutV} {s : S} (h : SlJAt (L := L) K.toKLayout s)
    (hO : E2EV.VcpuKsOff K) {b : U64} (hb : E2EV.VData K b) (hba : Aligned b) (v : U64) :
    L.curW (L.wr s b v) = L.curW s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := TInv.nodes B.j.blk _ B.j.kern.cpuCs
  have hv := nodeAt_val hN (off := layout.node.CUR_THREAD) (by rw [curth_val]; omega)
  rw [curth_val] at hv
  simp only [LawfulStore.nodeBase, B.ksb] at hv
  unfold LawfulStore.curW
  rw [nodeAt_wr, LawfulStore.cpu_wr]
  refine mem_wr_ne' hba (nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val])) fun e => ?_
  have hbv : b.val = K.ksb.val + 13568 + (L.cpu s).val * 4288 := by rw [e]; omega
  obtain ⟨w, hin, -⟩ := hb
  obtain ⟨hw, h1, h2⟩ := hin
  have h64 := B.j.kern.csLt _ B.j.kern.cpuCs
  rcases hO w hw with h | h <;> omega

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## Generic: a slot under a new record that gives the old one at a well-formed layout -/

/-- **A slot under a new premise record** that gives the old one where `RegionOKV K` / `UserOKV K` hold. -/
def SlotU.pullK {ι : Type} (X : SlotU ι) (P : ι → KLayoutV → (U64 → U64) → Prop)
    (f : ∀ {i K m}, RegionOKV K → UserOKV K → P i K m → X.Prem i K m) : SlotU ι where
  Prem := P
  path i K m hK hU h := X.path i K m hK hU (f hK hU h)
  W i K m hK hU h := X.W i K m hK hU (f hK hU h)

/-! ## The I/O port's sets under a `userV K` user-word write -/

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- **`IoRS` / `IoWS` / `IoDS` at `userV K` are kept by an aligned write of a `userV K` user word** at a bundle
state, the locks kept (module docstring, item 2). -/
theorem ioRWDS_wrV (hK : RegionOKV K) (hU : UserOKV K) (hO : VcpuKsOff K) {Locks : S → U64 → Prop} {s : S}
    (B : SlJAt (L := L) K.toKLayout s) {b : U64} (hb : b ∈ (userV K).user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    IoRS (st := st) (userV K) Locks (L.wr s b v) = IoRS (st := st) (userV K) Locks s ∧
      IoWS (st := st) (userV K) Locks (L.wr s b v) = IoWS (st := st) (userV K) Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  have eo : OwnMap.own (userV K) (L.mem (L.wr s b v)) = OwnMap.own (userV K) (L.mem s) :=
    E2E.ownDep (regionOK_userV hK) (userOK_userV hK hU) _ _
      (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have ecur : L.curW (L.wr s b v) = L.curW s := by
    rcases mem_userV.1 hb with hb' | hb'
    · exact B.curW_wr hb' hba v
    · exact B.curW_wrVD hO hb' hba v
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_wr]

end io

/-! ## `ReadOnce` of the timer interrupt under `IrqPreV` -/

section irq
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}

/-- **`ReadOnce` of the timer interrupt tree at `userV K` under `IrqPreV`** (module docstring, item 1). -/
theorem irq_hroV (hA : P0.ArchTotal ar) (hKV : RegionOKV K) (hUV : UserOKV K) (vf : VFacts L K)
    (hirq : irq.val < 128) (hm : E2E.MasksWr st) (hPL : PlanLk lk pl) :
    E2E.ReadOnce st ar (R.localtimer.handle_timer_irq_local irq pl) (OwnMap.cls (userV K))
      (OwnMap.ko (userV K) m) (· ∈ (userV K).user) (IrqPreV K st m) (MaxR (userV K) st lk) := by
  intro s s' a _ hP hAlt _
  obtain ⟨Ω, Ac, hE⟩ := hP.entM hKV vf hirq
  have O := irq_pathObl_V ar hA hKV hUV vf hirq (irq_isProg S irq pl) (irq_noZero irq pl) hm hPL hP
  exact irq_once_alt ar hA (regionOK_userV hKV) hm hE.ent
    (fun s1 a1 _ h1 => O.acc s a (true, s1, a1) rfl h1 rfl) hAlt

end irq

/-! ## The VM paths' `Pre` at a start from lvm's `*_of` lemmas -/

section lvm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **The vexit path's `Pre` at a start** from `vexitEnt_of` and `vexitPEnt_of` (module docstring, item 3). -/
theorem vxPre_ofJ {i : VxArg S} {K : KLayoutV} {m : U64 → U64} {s : S}
    (hI : BXI st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s)
    (hL : StLay K.toKLayout st i.T i.Scs i.Z s)
    (ntw : ∀ p ∈ i.Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (aff : ∀ t ∈ i.T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (curAff : L.mem s (affA (L.curW s)) = L.cpu s) (cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s)
    (vlk : i.v ≠ 0#u64 → i.lk s i.v)
    (usr : ∀ x, x ∈ K.user → Aligned x → UsrW st i.T i.Cs i.H i.Sg i.Scs i.Z s x)
    (buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄)
    (aff0 : m (fld (L.curW s) oAFFINITY) = L.mem s (affA (L.curW s)))
    (hJ : SlJAt (L := L) K.toKLayout s) (vf : VFacts L K) (hKH : K.heap = i.H) (hTs : i.T = i.H.tcbs)
    (hΩ : i.Ω = i.H.omega) (hSg : i.Sg = i.H.frame) (hScs : ∀ c ∈ i.Scs, i.H c = some (.sc (i.Z c)))
    (hNt : ∀ q ∈ i.Nt, i.H q = some .ntfn) (hvK : i.v ≠ 0#u64 → i.v ∈ K.vcpus) :
    VxPre st i K m s :=
  ⟨vexitEnt_of hI hL ntw cs aff curAff cscCore vlk hJ vf.heap hKH hTs hΩ hScs hNt hvK,
    vexitPEnt_of hI usr buf aff0 hJ vf.heap hKH hTs hΩ hSg hScs hvK⟩

/-- **The vtimer path's `Pre` at a start** from `vexitEnt_of` at the bound VCPU and `vtmEnt_of` (module docstring,
item 3). -/
theorem vtPre_ofJ {i : VtArg S} {K : KLayoutV} {s : S}
    (hI : BXI st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s)
    (hL : StLay K.toKLayout st i.T i.Scs i.Z s)
    (ntw : ∀ p ∈ i.Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (aff : ∀ t ∈ i.T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (curAff : L.mem s (affA (L.curW s)) = L.cpu s) (cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s)
    (vlk : vOf st s ≠ 0#u64 → i.lk s (vOf st s))
    (hJ : SlJAt (L := L) K.toKLayout s) (vf : VFacts L K) (hKH : K.heap = i.H) (hTs : i.T = i.H.tcbs)
    (hΩ : i.Ω = i.H.omega) (hScs : ∀ c ∈ i.Scs, i.H c = some (.sc (i.Z c)))
    (hNt : ∀ q ∈ i.Nt, i.H q = some .ntfn) (hvK : vOf st s ≠ 0#u64 → vOf st s ∈ K.vcpus)
    (hAs : AsidOff (L := L) i.Ω i.Sg s) :
    VtPre st i K s :=
  vtmEnt_of (vexitEnt_of hI hL ntw cs aff curAff cscCore vlk hJ vf.heap hKH hTs hΩ hScs hNt hvK) hJ vf.heap vf.tab
    (vf.pool s hJ) hAs

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **Starting the vexit slot** (the glue's `Fl4StepV.start` for `vxSlot`, `Pre` by `vxPre_ofJ`). -/
theorem vxSlot_startJ (D : Dflt) {i : VxArg S} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K}
    {hU : UserOKV K} (h : VxPrem st ar i K m) {c : U64} {hs : U64 → Prop} {μ : U64 → U64} (σ : S) (a : A)
    (hP : VxPre st i K m σ) (hc : L.cpu σ = c) (hl : i.lk σ = hs)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    ∃ q, E2E.StartAt ((vxSlot st ar hA hm).fam D i K m hK hU) c hs μ q :=
  SlotN.startAt D (vxSlot st ar hA hm) (hK := hK) (hU := hU) h σ a hP hc hl hμ

/-- **Starting the vtimer slot at `vtimer_localPathW`** (`Pre` by `vtPre_ofJ`). -/
theorem vtSlotW_startJ (D : Dflt) {i : VtArg S} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K}
    {hU : UserOKV K} (h : VtPremW st ar i K m) {c : U64} {hs : U64 → Prop} {μ : U64 → U64} (σ : S) (a : A)
    (hP : VtPre st i K σ) (hc : L.cpu σ = c) (hl : i.lk σ = hs)
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    ∃ q, E2E.StartAt ((vtSlotW st ar hA hm).fam D i K m hK hU) c hs μ q :=
  SlotN.startAt D (vtSlotW st ar hA hm) (hK := hK) (hU := hU) h σ a hP hc hl hμ

end lvm

/-! ## The new records and slots -/

section fam
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **I/O port's premises, `ro` proved and `uf` split** (module docstring, items 1–2). -/
structure IoPremW2 (i : IoArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- `IoPre` at bundle states ([J] P1 facts, fl4-sync contract). -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    IoPre st K.toKLayout K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac s
  /-- [J] -/
  mA : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s → ∀ d, K.heap d = some .tcb →
    m (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)
  /-- [J] the caller's `Q` survives an aligned write of a `userV K` user word at a bundle state. -/
  qf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)
  /-- [P] at bundle states the locks are determined by the words off `(userV K).user`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.Locks s
  /-- The layout is a bundle layout (no premise: the start state itself). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ

variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)
include hA in
theorem IoPremW2.toIo {i : IoArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : IoPremW2 st i K m) : IoPrem st ar i K m where
  vf := h.vf
  pe := h.pe
  mA := h.mA
  uf s b v hJ hq hb hba := by
    have hl := hlk_of_kernelDetU h.kd s b v hJ hb hba
    have e := ioRWDS_wrV (st := st) hK hU h.vf.ks hJ hb hba v hl
    exact ⟨h.qf s b v hJ hq hb hba, hl, e.1, e.2.1, e.2.2⟩
  bun := h.bun
  ro := io_hro (K := userV K) (Locks := i.Locks) (m0 := m) hA (number := i.number)
    (P := fun s => SlJAt (L := L) K.toKLayout s ∧ i.Q K m s)
    (fun s hs => ioPre_userV hK (h.vf.v hs.1).1 (h.pe s hs.1 hs.2))

/-- **`TCB_SetTimer`'s premises, `ro` proved** (`StPremK` without `ro`). -/
structure StPremK2 (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- [J] `StEntK` at bundle states. -/
  pe : ∀ s, SlJAt (L := L) K.toKLayout s → i.Q K m s →
    StEntK K.toKLayout st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target m s
  /-- [J] -/
  eu : ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v)
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- [J] -/
  nu : ∀ s, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ (userV K).user
  /-- [J] -/
  uf : ∀ s b v, SlJAt (L := L) K.toKLayout s → i.Q K m s → b ∈ (userV K).user → Aligned b → i.Q K m (L.wr s b v)

include hA hm in
theorem StPremK2.toK {i : StArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : StPremK2 st i K m) : StPremK st ar i K m :=
  ⟨h.vf, h.pe, st_hro ar i.n hA (regionOK_userV hK) (userOK_userV hK hU) hm, h.eu, h.kd, h.nu, h.uf⟩

/-- **The timer interrupt's premises, `ro` proved** (`IrqPremK` without `ro`). -/
structure IrqPremK2 (i : IrqArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- [J] -/
  vf : VFacts L K
  /-- The IRQ's state word lies in the kernel-state block (the timer IRQ is 2). -/
  lt : i.irq.val < 128
  /-- [P] at bundle states the locks are determined by the words off `(userV K).user`. -/
  kd : ∀ s, SlJAt (L := L) K.toKLayout s → KernDetS (L := L) (userV K).user i.lk s
  /-- [P] -/
  pl : PlanLk i.lk i.pl

include hA hm in
theorem IrqPremK2.toK {i : IrqArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K)
    (h : IrqPremK2 st i K m) : IrqPremK st ar i K m :=
  ⟨h.vf, h.lt, irq_hroV ar hA hK hU h.vf h.lt hm h.pl, h.kd, h.pl⟩

/-- **I/O port slot, `ro` proved, `uf` split.** -/
def ioSlotW2 : SlotU (IoArg S) :=
  (ioSlot st ar hA hm).pullK (IoPremW2 st) (fun hK hU h => h.toIo st ar hA hK hU)

/-- **`TCB_SetTimer` slot, `ro` proved.** -/
def stSlotW2 : SlotU (StArg S) :=
  (stSlotK st ar hA hm).pullK (StPremK2 st) (fun hK hU h => h.toK st ar hA hm hK hU)

/-- **Timer interrupt slot, `ro` proved.** -/
def irqSlotW2 : SlotU (IrqArg S) :=
  (irqSlotK st ar hA hm).pullK (IrqPremK2 st) (fun hK hU h => h.toK st ar hA hm hK hU)

/-- **FL4's eight local paths, `fl4LocW` with the `io` / `st` / `irq` slots swapped** (module docstring). -/
def fl4LocW2 : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlot st ar hA hm
  io := ioSlotW2 st ar hA hm
  st := stSlotW2 st ar hA hm
  irq := irqSlotW2 st ar hA hm
  sl := slSlotK st ar hA hSt hm a0
  vq := fl4LQW st ar hA hm (fl4Dflt st ar hm)

/-- **FL4 end to end with rule 7 over its eight local paths, `ReadOnce` of io / st / irq proved**
(`serializable_fl4_local`'s statement over `fl4LocW2`; premise table in the module docstring). -/
theorem serializable_fl4_localW2 {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocW2 st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

end fam

end
end Fl4Proofs.P2.E2EV
