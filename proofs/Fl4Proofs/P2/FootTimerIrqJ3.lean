/-
# P2 (p2lf gen15–gen17): the timer interrupt local path with `Pre` = line slj's bundle

gen14 left `irq_pathsJ2` with `Pre := IrqEntIM … ∧ SlJAt K`, `IrqEntI`'s [J] parts `inv` / `lay` / `iq` /
`asid` / `aff` asked at each start at fixed word sets `Ω` / `Ac`. This file derives every one of them from
`SlJAt K s` (P3's `JAtZ` at the entry with `K` its layout), so the timer interrupt's `Pre` has
`sl_pathsK`'s shape: `IrqPreJ3 K st m s := SlJAt K s ∧` the store agreeing with the model memory `m` on aligned
kernel words.

* `SlJAtZ.irqStNone`: IRQ `i`'s state word (`ksb + 224 + 8 i`, `i < 128`) is aligned and in no region of the
  layout: off every object of `Zx.th` (P3 `IntLayout.st_out`, `JAtZ.intL`), so off every slot; off every
  non-`other` object of `H` (`JKern.hks`: outside `[ksb, ksb + 13568)`); below every node (`ksb + 13568`).
* `SlJAtZ.stLay`: `StLay` for `K` (`nd` by `slj_region_node` with `JAtZ.nodeAt_cur_val`; `tcb` / `sc` by
  `LayP.region_tcb` / `region_sc`; `dom` / `dtm` by `SlJAtZ.ksNone` at offsets 8 / 16).
* `SlJAtZ.irqEntI`: `IrqEntI` at P1's set convention, with `Ω := P3.OmegaU K.heap Zx (ksb s) σ` and `Ac := `
  `JAtZ`'s `Ac`: `inv` = P3 `JAtZ.bxiU`, `asid` = `JAtZ.asidOffU`, `aff` = P1 `XInv.core_eq` (ScAff) of
  `JAtZ.bxi`, `lay` = `stLay`, `iq` = `irqStNone`, `nth` by the convention. `slJAt_irqEntI`: `∃ Ω Ac, IrqEntI …`.
  `Ω` and `Ac` are ghost-dependent (`OmegaU` names `σ`'s buffer words and `Zx.P`'s pools), so they are chosen per
  entry state; every `PathObl` / `PathSide` field uses `Pre` at one state only, so a per-state choice suffices
  (`irq_obl_of_pt`).

**Narrowing: `iq` is false for `irq ≥ 128`.** `interrupt.state_off irq = ok (224 + 8 irq)` (wrapping) for every
`irq`, so `IrqLay.iq` / `IrqEntI.iq` ask region `.none` of `ksb + 224 + 8 irq` for an arbitrary `irq`. Under
`layoutJ` that fails, e.g. `irq = 1668`: `ksb + 224 + 8·1668 = ksb + 13568`, core 0's node word `CUR_THREAD`,
whose region is `.node 0`. The body declines on `irq > irqn::MAX = 127` before reading the state word, so gen16
narrows `IrqLay.iq` / `IrqLayR.iq` / `IrqEntI.iq` in place to `irq.val < 128 → …` (only a strengthening of the
theorems using them): the fire-case users (FireAk, FireOwn, LPP2, Own) take the bound from the accepted run
(`irq_lt_of_acc`, P2/FootTimerIrqLP.lean), FootTimerIrqDec from its own `MAX` test. gen15's premise `hirq` is gone.

* `irq_pathObl_J3` (`PathObl` at one entry state), `irq_pathSide_J3` (`PathSide`, `user_free` from slhuf's
  `SlJAt.userWr`), `irq_localPathJ3`, **`irq_pathsJ3`**: `E2E.Paths` member with `Pre := IrqPreJ3 K st m`;
  `irq_pathsJ3_startAt`:
  `Fl4Step.start` [P] asks `SlJAt K σ` (as `sl_pathsK_startAt`) and the memory agreement at the start state.
  `SlJAt K σ` at reachable entries for every `K` matching the stable ghosts: `slJAt_of_reachU17_stable` (P3
  `JReachU17`; the fixed-layout gap is line lay's, P2/SlJLay.lean).

**gen17: `hEU` gone.** `Pre` is `SlJAt K ∧` memory agreement; every `IrqEntI` fact is derived from `SlJAt` at the
state where it is used (`IrqPreJ3.entM`), so a user-word write only has to keep `SlJAt K` (line slhuf's
`SlJAt.userWr`, P2/SlJHuf.lean, no side condition) and the memory agreement on kernel words (kept here). `hlk` takes
syscall_local's guarded form (`SlJAt K s → b ∈ K.user → Aligned b → lk (wr) = lk s`, as `sl_huf` / `sl_pathsKU`), so
both local paths share one fl4-sync lock contract.

Premises of `irq_pathsJ3`: `hA` (`ArchTotal`), `hp` [P] (`IsProg`), `hz` [W] (`NoZero`), `hm` [P] (`MasksWr`),
`hro` [W] (per layout, `ReadOnce` under `IrqPreJ3`), `hlk` [P] (guarded: locks unchanged by a user-word write at a
`SlJAt` state), `hPL` [P] (`PlanLk`). No `IrqEnt` part and no user-write [J] premise is left.
-/
import Fl4Proofs.P2.FootTimerIrqJC
import Fl4Proofs.P2.SlJHuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section ks
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **An IRQ state word is aligned and in no region** (module docstring). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.irqStNone (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    {i : U64} (hi : i.val < 128) :
    Aligned (Fl4Proofs.P3.irqStA (L.ksb s) i) ∧ region K (Fl4Proofs.P3.irqStA (L.ksb s) i) = .none := by
  have hk := B.ksb
  have hO := B.j.intL.st_out i hi
  have hv := Fl4Proofs.P3.irqStA_val B.j.kern.ksbFit hi
  obtain ⟨Tr, Cq, hJ⟩ := B.j.jpl
  have hobj : ∀ p k, K.heap p = some k → (∀ z, k ≠ .other z) →
      ¬ InW p (2 ^ k.bits) (Fl4Proofs.P3.irqStA (L.ksb s) i) := by
    intro p k hp hk' ⟨g1, g2⟩
    rcases B.j.kern.hks p k hp hk' with e | e <;> omega
  refine ⟨hO.1, ?_⟩
  unfold region
  rw [dif_neg, dif_neg, dif_neg (fun ⟨t, ht, htb⟩ => hobj t _ ht (by intro z e; cases e) htb),
    dif_neg (fun ⟨p, hp, hpb⟩ => hobj p _ hp (by intro z e; cases e) hpb), dif_neg, dif_neg]
  · rintro ⟨p, z, hp, hpb⟩
    exact hobj p _ hp (by intro z' e; cases e) hpb
  · rintro ⟨p, ⟨hp, hpb⟩ | ⟨hp, hpb⟩⟩
    · exact hobj p _ hp (by intro z e; cases e) hpb
    · exact hobj p _ hp (by intro z e; cases e) hpb
  · rintro ⟨p, hp, g1, g2⟩
    rw [B.slots] at hp
    obtain ⟨q, j, hqi, rfl⟩ := hp
    obtain ⟨k, hk', hsz⟩ := hqi.size
    have hv' := hqi.val hJ.pl
    exact hO.2 q k hk' ⟨by omega, by omega⟩
  · rintro ⟨c, -, g1, -⟩
    rw [← hk] at g1
    omega

/-- **`StLay` from the bundle** (module docstring). -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.stLay (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) :
    StLay K st (Heap.tcbs K.heap) (Heap.scs K.heap) (Heap.scBits K.heap) s := by
  have hk := B.ksb
  have hP := B.layP
  have hf := B.j.kern.ksbFit
  have hal := B.j.kern.ksbAl
  have hkv : ∀ o : U64, o.val < 256 →
      (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
    intro o ho
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have ks' : ∀ o : U64, o.val < 256 → o.val % 8 = 0 →
      Aligned (core.num.U64.wrapping_add (L.ksb s) o) ∧
        region K (core.num.U64.wrapping_add (L.ksb s) o) = .none := by
    intro o ho h8
    have ha : Aligned (core.num.U64.wrapping_add (L.ksb s) o) := by
      unfold Aligned; rw [hkv o ho]; omega
    exact ⟨ha, B.ksNone _ ha (by rw [hkv o ho, ← hk]; omega) (by rw [hkv o ho, ← hk]; omega)⟩
  have d1 := ks' layout.ks.CUR_DOMAIN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  have d2 := ks' layout.ks.DOMAIN_TIME (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  refine ⟨fun o ho => ?_, fun t ht k h1 h2 => ?_, fun p hp b hb => ?_, d1.2, d2.2, d1.1, d2.1⟩
  · have hv := B.j.nodeAt_cur_val ho
    exact slj_region_node ⟨B.cpu, by rw [hv, ← hk]; omega, by rw [hv, ← hk]; omega⟩
  · have ht' : K.heap t = some .tcb := ht
    have hft := hP.heap.fits t _ ht'
    simp only [HKind.bits] at hft
    have hv : (fld t k).val = t.val + k.val := fld_val (by omega)
    exact hP.region_tcb ht' ⟨by rw [hv]; omega, by rw [hv]; omega⟩ (by rw [hv]; omega)
  · obtain ⟨z, hz⟩ := hp
    have e : Heap.scBits K.heap p = z := by simp only [Heap.scBits, hz]
    rw [e] at hb
    exact hP.region_sc hz hb

/-- **`IrqEntI` from the bundle** at P1's set convention (module docstring): `Ω = OmegaU`, `Ac` = `JAtZ`'s. -/
theorem _root_.Fl4Proofs.P2.PathObl.SlJAtZ.irqEntI (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ)
    {irq : U64} :
    IrqEntI K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} (Fl4Proofs.P3.OmegaU K.heap Zx (L.ksb s) σ) K.heap
      (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ax irq s := by
  have hL := B.stLay
  have e : Cx = {c : U64 | c.val < K.ncores} := Set.ext fun c => B.cs c
  subst e
  refine ⟨B.j.bxiU, hL, fun hb i hi => ?_, B.j.asidOffU,
    fun t ht h0 => (XInv.core_eq B.j.bxi.2.2.1 ht h0).symm, fun n hn => hn⟩
  rw [Fl4Proofs.P3.state_off_eq] at hi
  have hi' := ok_inj_ff hi
  subst hi'
  exact B.irqStNone hb

end ks

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`IrqEntI` at some word sets from line slj's bundle** (`SlJAtZ.irqEntI`). -/
theorem slJAt_irqEntI {K : KLayout} {s : S} {irq : U64} (h : SlJAt (L := L) K s) :
    ∃ Ω Ac : Set U64, IrqEntI K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
      (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact ⟨_, _, B.irqEntI⟩

/-- The timer interrupt's `Pre` in `irq_pathsJ3`: line slj's bundle `SlJAt K` and the store agreeing with the
model memory `m` on aligned kernel words (`sl_pathsK`'s `SlJAt K ∧ Q K m`). -/
def IrqPreJ3 (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (m : U64 → U64) (s : S) : Prop :=
  SlJAt (L := L) K s ∧ ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x

/-- `IrqEntM` at the entry from `IrqPreJ3` (word sets chosen per state). -/
theorem IrqPreJ3.entM {K : KLayout} {m : U64 → U64} {s : S} {irq : U64}
    (h : IrqPreJ3 K st m s) :
    ∃ Ω Ac : Set U64, IrqEntM K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
      (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq m s := by
  obtain ⟨Ω, Ac, hI⟩ := slJAt_irqEntI (st := st) h.1
  exact ⟨Ω, Ac, (IrqEntIM.entRM ⟨hI, h.2⟩ (irqLayK_of_slJAt hI.inv h.1)).entM (slJAt_slotJC h.1).slotJ⟩

end ent

section pt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`PathObl` is pointwise in `Pre`**: every field asks `Pre` at one state. -/
theorem irq_obl_of_pt {A X : Type} {f : machine.Store S → S → A → Result (X × S × A)} {Acc : X → Prop}
    {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}
    {User : U64 → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop} {RS WS DS : S → U64 → Prop}
    (h : ∀ s0, Pre s0 → PathObl.PathObl st f Acc own cls ko User Locks (fun s => s = s0) RS WS DS) :
    PathObl.PathObl st f Acc own cls ko User Locks Pre RS WS DS where
  acc s a r hP := (h s hP).acc s a r rfl
  dec_alt s a r hP := (h s hP).dec_alt s a r rfl
  read_own s x hP := (h s hP).read_own s x rfl
  write_own s x hP := (h s hP).write_own s x rfl
  aligned s x hP := (h s hP).aligned s x rfl
  move s a r hP := (h s hP).move s a r rfl

end pt

section path
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **`PathObl` of the timer interrupt at one `IrqPreJ3` entry state** (`irq_pathObl` at `P := (· = s0)`, the
fire case split as `irq_localPathJC2`'s). -/
theorem irq_pathObl_J3 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hPL : PlanLk lk pl) {s0 : S} (h0 : IrqPreJ3 K st m s0) :
    PathObl.PathObl st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a irq pl) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) lk (fun s => s = s0) (MaxR K st lk) (MaxW K st lk)
      (IrqDec st) := by
  obtain ⟨Ω, Ac, hE⟩ := h0.entM (irq := irq)
  have hQ := slJAt_slotJC (st := st) h0.1
  refine irq_pathObl ar hA hK hUO (P := fun s => s = s0) (fun s e => by subst e; exact hE.ent)
    (fun mm => hp A ar mm) hz hm (fun s e q hq => by subst e; exact irq_koF hE.ent hq)
    (Fl4Proofs.P2.ko_aligned hK hUO) ?_ ?_
  · rintro s a s1 a1 rfl hf h
    by_cases hnw : NoWake st s
    · exact irq_acc_fire_nw ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := hQ.bufAt
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        (hQ.slotJ.objLay (fun r hr => hr)) hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h)
        (hQ.slotJ.slotLayV (fun y hy => hy)) hf hnw h
  · rintro s a s1 a1 rfl h
    refine irq_move_acc ar hA hK hUO hp hE.k (fun hf => ?_) h
    by_cases hnw : NoWake st s
    · exact irq_move_fire_nw ar hA hK hUO hp hE.k hE.ent.ly hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := hQ.bufAt
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        (hQ.slotJ.objLay (fun r hr => hr)) hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h) hf hnw h

/-- **`PathSide` of the timer interrupt under `IrqPreJ3`**: `read_aligned` by `irq_alt` at the entry's word sets,
`user_free` from `SlJAt.userWr` (the bundle kept by a user-word write), the memory agreement on kernel words, and
`hlk` [P] (guarded lock contract, as syscall_local's). -/
theorem irq_pathSide_J3 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hlk : ∀ s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) :
    PathObl.PathSide st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a irq pl) (OwnMap.cls K)
      (OwnMap.ko K m) (· ∈ K.user) lk (IrqPreJ3 K st m) (MaxR K st lk) (MaxW K st lk) (IrqDec st) := by
  refine ⟨?_, fun s x _ hx => hx.2, Fl4Proofs.P2.ko_aligned hK hUO, ?_⟩
  · intro s s' a r hP hAlt h
    obtain ⟨Ω, Ac, hE⟩ := hP.entM (irq := irq)
    have O := irq_pathObl_J3 ar hA hK hUO hp hz hm hPL hP
    have eP : ∀ (mm : machine.Store S) (x : S),
        localtimer.handle_timer_irq_local mm ar x a irq pl = interp mm ar p x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    rcases irq_alt ar hA hK (fun mm => hp A ar mm) hz hm hE.ent
      (fun s1 a1 _ h1 => O.acc s a (true, s1, a1) rfl h1 rfl) hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
    · show localtimer.handle_timer_irq_local _ ar s' a irq pl = ok r
      rw [eP] at h2 ⊢
      exact interp_mono (fun _ hw => hw.2) (fun _ _ => trivial) p hz s' a r h2
    · show localtimer.handle_timer_irq_local _ ar s' a irq pl = ok r
      rw [eP] at h2 ⊢
      exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2
  · intro s b v h hb hba
    have keep : ∀ x, Aligned x → x ∉ K.user → L.mem (L.wr s b v) x = L.mem s x :=
      fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
    have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
      E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
    have hl := hlk s b v h.1 hb hba
    refine ⟨⟨h.1.userWr hb v, fun x hx hxu => by rw [keep x hx hxu]; exact h.2 x hx hxu⟩,
      hl, ?_, ?_, irq_dec_user s b v⟩
    · funext w; simp only [MaxR, RPerm, GateOnly, eo, hl, L.cpu_wr]
    · funext w; simp only [MaxW, WPerm, eo, hl, L.cpu_wr]

/-- **The timer interrupt local path with `Pre := IrqPreJ3 K st m`** (module docstring). -/
noncomputable def irq_localPathJ3 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ3 K st m) (MaxR K st lk))
    (hlk : ∀ s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  { S := S
    A := A
    X := Bool
    st := st
    L := L
    ar := ar
    F := irqBody S irq pl
    p := p
    Acc := fun b => b = true
    Locks := lk
    Pre := IrqPreJ3 K st m
    RS := MaxR K st lk
    WS := MaxW K st lk
    DS := IrqDec st
    isProg := PathObl.IsProg.on hp _ _ _
    obl := irq_obl_of_pt fun _ h0 => irq_pathObl_J3 ar hA hK hUO hp hz hm hPL h0
    side := irq_pathSide_J3 ar hA hK hUO hp hz hm hlk hPL
    once := hro
    total := fun s a => by
      obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
      exact ⟨r, e⟩
    masks := hm }

/-- **The timer interrupt as an `E2E.Paths` member with `Pre := IrqPreJ3 K st m`** (`SlJAt K ∧` memory
agreement: `sl_pathsK`'s shape). Premises: `hA`, `hp` [P], `hz` [W], `hm` [P], `hro` [W] (per layout), `hlk` [P]
(guarded, syscall_local's form), `hPL` [P]. -/
noncomputable def irq_pathsJ3 (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ3 K st m)
      (MaxR K st lk))
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) : E2E.Paths Unit :=
  fun _ K m hK hU =>
    irq_localPathJ3 (K := K) (m := m) ar hA hK hU hp hz hm (hro K m) (hlk K) hPL

/-- **`StartAt` for `irq_pathsJ3`**: `Fl4Step.start` [P] asks `SlJAt K σ` at the start state (as
`sl_pathsK_startAt`; P3 gives it at reachable entries for every `K` matching the stable ghosts,
`slJAt_of_reachU17_stable`), the memory agreement with `m`, and the glue's core / locks / memory. -/
theorem irq_pathsJ3_startAt (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ3 K st m)
      (MaxR K st lk))
    (hlk : ∀ (K : KLayout) s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hM : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = m x)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (irq_pathsJ3 ar hA hp hz hm hro hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ3 ar hA hp hz hm hro hlk hPL () K m hK hU).body σ a) :=
  ⟨σ, a, ⟨hJ, hM⟩, hc, hl, hμ, rfl⟩

end path

end Fl4Proofs.P2
