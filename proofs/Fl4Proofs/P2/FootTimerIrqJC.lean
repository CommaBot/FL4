/-
# P2 (p2lf gen14): the timer interrupt local path with its layout premise in `sl_pathsK`'s shape

gen13 left `irq_localPathP3J2` with the [J] premises `hUB` (UserOK + buffer lookup at every entry), `hSJ` (`SlotJ`),
`hTH` (`T` holds `H`'s TCBs), `hRp` (`Rp` holds `H`'s replies), and `IrqLay.cs` (an `IrqEnt` [J] part) false under
P3's layout. This file:

* `IrqLay.cs` / `IrqRd`'s slot class are narrowed in place to offsets below 192 (the six TCB slots; the only slot
  words the timer path reads are slot 1 and slot 4's, `irq_accG_rr_walk`), so they are strengthenings of every
  existing theorem. `slotCs_of_JAtZ` / `SlotJ.cs`: that `cs` for any TCB of `H` at a `JAtZ` state with `K` its
  layout (`IsSlotAt Zx.th y (k / 32)`, `tcbSlots = 6`).
* `IrqLayR` / `IrqEntR` / `IrqEntRM`: `IrqLay` / `IrqEnt` / `IrqEntM` without `cs` (`IrqLayR.lay` rebuilds `IrqLay`
  from `cs`).
* `SlotJC K st Cs H s` [J]: `SlotJ` with `JAtZ`'s core set the path's `Cs` (not just containing `K`'s cores);
  `SlotJC.bufAt`: `BufAt` at `s` from P3 `JAtZ.bufAtJ` under P1's set convention (`T = H.tcbs`, `Sg = H.frame`,
  `Scs = H.scs`, `Z = H.scBits`). `irq_bufAt_runB`: `hBA` (run form) from `BufAt` at `s` (`hUB` narrowed to
  `∃ U, BufAt … U s`, as decided for gen14).
* `irq_localPathJC`: the timer interrupt local path at P1's set convention, `Pre := IrqEntRM … ∧ Q` for any `Q`
  giving `SlotJC` (`hQ`). `hUB`, `hTH`, `hRp`, `hOL`, `hSL` and `IrqLay.cs` are all gone (BufAt, the slot and
  object layouts and `cs` come from `SlotJC`; `T` / `Rp` are `H`'s by the convention).
* `slJAt_slotJC`: line slj's syscall bundle `SlJAt K s` gives `SlotJC K st {c | c.val < K.ncores} K.heap s`.
* `irq_pathsJ : E2E.Paths Unit`: for every layout `K` and memory `m`, `irq_localPathJC` at `H = K.heap`,
  `Cs = {c | c.val < K.ncores}`, `Nt = K.heap.ntfns` and `Q := SlJAt K`, so its `Pre` is
  `IrqEntRM … ∧ SlJAt K` — the shape of `sl_pathsK`'s `SlJAt K ∧ Q K m` (P2/SlJLay.lean). `irq_pathsJ_startAt`:
  `Fl4Step.start` [P] asks `SlJAt K σ` and `IrqEntRM` at the start state, as for the syscall.
  `SlJAt K s` at reachable entries for every `K` matching the stable ghosts: `slJAt_of_reachU17_stable` (line lay).

Premises of `irq_localPathJC`: `hp` [P], `hz` [W], `hm` [P], `hro` [W], `IrqEntR`'s [J] parts (inv / lay / ly:
iq, kr, tab, ntw / asid / aff / nth), `hQ` (by construction in `irq_pathsJ`), `hEU` [J] (`IrqEntR` and `Q` kept by
a user-word write; `sl_pathsK`'s `huf` asks the same of `SlJAt`), `hlk` [P], `hPL` [P].
Premises of `irq_pathsJ`: the same per layout (`hro` / `hEU` / `hlk` for every `K`), with `Q = SlJAt K` and
`nth` trivial.

Stage 2 (same gen):
* `LayP.region_ntfnW`; `IrqLayK` (`IrqLay`'s `kr` / `tab` / `ntw`) and `irqLayK_of_slJAt`: all three from `SlJAt K`
  at a P1 state (`RegionOKX.ks` / `.asidT`, `SlJAtZ.pool`, `region_ntfnW` for `Nt = K.heap.ntfns`).
* `IrqEntI` / `IrqEntIM`: `IrqEnt` with only `IrqLay.iq` left of its layout part.
* `irq_localPathJC2` (`hQL` gives `IrqLayK` from `Q`), **`irq_pathsJ2`** (`Pre := IrqPreJ2 K … m` =
  `IrqEntIM … ∧ SlJAt K`), `irq_pathsJ2_startAt`.

Premises of `irq_pathsJ2`: `hp` [P], `hz` [W], `hm` [P], `hro` [W] (per layout), `IrqEntI`'s [J] parts (`inv`, `lay`,
`iq`, `asid`, `aff`; `nth` holds for `K.heap.ntfns`), `hEU` [J] (per layout: `IrqEntI` and `SlJAt K` kept by a
user-word write), `hlk` [P], `hPL` [P]; and at each start `Fl4Step.start` [P] asks `IrqPreJ2 K … m σ`.
-/
import Fl4Proofs.P2.FootTimerIrqSlotJ
import Fl4Proofs.P2.SlJLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Classical

section j
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`IrqLay.cs` from P3's joint invariant** for its layout, at any TCB `y` of `H` (module docstring). -/
theorem slotCs_of_JAtZ {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {H : Heap} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S}
    {a' : A'} {σ : Fl4Spec.State Unit} (J : Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cx Ax Lst D s a' σ) {n : Nat}
    (hn : ∀ c : U64, c.val < n → c ∈ Cx) {y : U64} (hyH : H y = some .tcb) :
    ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region (layoutJ Zx H (L.ksb s) n) (core.num.U64.wrapping_add y k) = .slot p ∧
        TcbSlot (layoutJ Zx H (L.ksb s) n) p ∧ (core.num.U64.wrapping_add y k).val - p.val < 16 := by
  have hP := layP_of_JAtZ J hn
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  intro k hk hk32
  have hth : Zx.th y = some .tcb := (hJ.tcb y).2 hyH
  have hf := hJ.heap.fits y _ hyH
  simp only [HKind.bits] at hf
  have hsa : Fl4Proofs.P3.IsSlotAt Zx.th y (k.val / 32) :=
    Or.inr ⟨hth, by unfold Fl4Proofs.P3.tcbSlots; omega⟩
  have hpv : (Fl4Proofs.P3.slotOf y (k.val / 32)).val = y.val + 32 * (k.val / 32) := hsa.val hJ.pl
  have hps : Fl4Proofs.P3.slotOf y (k.val / 32) ∈ (layoutJ Zx H (L.ksb s) n).slots := by
    show Fl4Proofs.P3.IsSlot Zx.th _
    exact ⟨y, _, hsa, rfl⟩
  have hkv : (core.num.U64.wrapping_add y k).val = y.val + k.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hin : InW (Fl4Proofs.P3.slotOf y (k.val / 32)) 32 (core.num.U64.wrapping_add y k) := by
    unfold InW; rw [hpv, hkv]; omega
  refine ⟨_, hP.region_slotW hps hin, ⟨y, hyH, ?_⟩, by rw [hpv, hkv]; omega⟩
  unfold InW; rw [hpv]
  constructor <;> omega

theorem SlotJ.cs {K : KLayout} {H : Heap} {s : S} (h : SlotJ K st H s) {y : U64} (hyH : H y = some .tcb) :
    ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p, region K (core.num.U64.wrapping_add y k) = .slot p ∧
      TcbSlot K p ∧ (core.num.U64.wrapping_add y k).val - p.val < 16 := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, J, hn, hK⟩ := h
  have := slotCs_of_JAtZ J hn hyH
  rwa [hK] at this

/-- **[J] The entry as a state of P3's joint invariant at the path's core set `Cs`, with `K` its layout**:
`SlotJ` with `JAtZ`'s `Cs` the given one. -/
def SlotJC (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Cs : Set U64) (H : Heap) (s : S) : Prop :=
  ∃ (A' : Type) (arI : machine.Arch A') (AR : A' → Fl4Spec.Cr3 → Prop) (Zx : Fl4Proofs.P3.XSets)
    (Ax : Set U64) (Lst : U64 → List U64) (D : Set U64) (a' : A') (σ : Fl4Spec.State Unit),
    Fl4Proofs.P3.JAtZ (L := L) arI AR Zx H Cs Ax Lst D s a' σ ∧ (∀ c : U64, c.val < K.ncores → c ∈ Cs) ∧
      layoutJ Zx H (L.ksb s) K.ncores = K

theorem SlotJC.slotJ {K : KLayout} {Cs : Set U64} {H : Heap} {s : S} (h : SlotJC K st Cs H s) : SlotJ K st H s := by
  obtain ⟨A', arI, AR, Zx, Ax, Lst, D, a', σ, J, hn, hK⟩ := h
  exact ⟨A', arI, AR, Zx, Cs, Ax, Lst, D, a', σ, J, hn, hK⟩

/-- **`BufAt` at a `SlotJC` entry** under P1's set convention (P3 `JAtZ.bufAtJ`, `U = BufU Zx σ`). -/
theorem SlotJC.bufAt {K : KLayout} {Cs : Set U64} {H : Heap} {s : S} (h : SlotJC K st Cs H s) :
    ∃ U : Set U64, BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s := by
  obtain ⟨A', arI, AR, Zx, Ax, Lst, D, a', σ, J, -, -⟩ := h
  exact ⟨_, J.bufAtJ⟩

/-- **Line slj's syscall bundle gives `SlotJC`** at the core set numbered by `K`. -/
theorem slJAt_slotJC {K : KLayout} {s : S} (h : SlJAt (L := L) K s) :
    SlotJC K st {c : U64 | c.val < K.ncores} K.heap s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have e : Cx = {c : U64 | c.val < K.ncores} := Set.ext fun c => B.cs c
  subst e
  exact ⟨A', arI, AR, Zx, Ax, Lst, D, a', σ, B.j, fun c hc => hc, B.lay⟩

end j

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- `IrqLay` without its slot field `cs` (gen14: `cs` comes from P3, `SlotJ.cs`). -/
structure IrqLayR (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Nt : Set U64) (irq : U64) (s : S) :
    Prop where
  iq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i →
    Aligned (core.num.U64.wrapping_add (L.ksb s) i) ∧ region K (core.num.U64.wrapping_add (L.ksb s) i) = .none
  kr : Aligned (krA (L := L) s) ∧ region K (krA (L := L) s) = .none
  tab : ∀ hi : U64, hi.val < 2048 →
    (Aligned (atAF (L.ksb s) hi) ∧ region K (atAF (L.ksb s) hi) = .none) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧ region K (peAF (L.mem s (atAF (L.ksb s) hi)) lo) = .none
  ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n

theorem IrqLayR.lay {irq : U64} {s : S} (h : IrqLayR K st Nt irq s)
    (hcs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16) : IrqLay K st Nt irq s :=
  ⟨h.iq, h.kr, h.tab, h.ntw, hcs⟩

/-- `IrqEnt` with `IrqLayR` for `IrqLay` (its [J] parts but `cs`). -/
structure IrqEntR (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (irq : U64) (s : S) : Prop where
  inv : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  lay : StLay K st T Scs Z s
  ly : IrqLayR K st Nt irq s
  asid : AsidOff (L := L) Ω Sg s
  aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  nth : ∀ n ∈ Nt, H n = some .ntfn

/-- `IrqEntR` and the store agreeing with the model memory `m` on aligned kernel words. -/
structure IrqEntRM (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (irq : U64) (m : U64 → U64) (s : S) : Prop where
  ent : IrqEntR K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s
  mem : ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x

/-- `IrqEnt` at P1's set convention from `IrqEntR` and `SlotJ` (its `cs`). -/
theorem IrqEntR.ent {irq : U64} {s : S}
    (h : IrqEntR K st (Heap.tcbs H) Cs Ω H Sg Rp Scs Nt Z Ac irq s) (hJ : SlotJ K st H s) :
    IrqEnt K st (Heap.tcbs H) Cs Ω H Sg Rp Scs Nt Z Ac irq s :=
  ⟨h.inv, h.lay, h.ly.lay (hJ.cs (h.inv.1.choose_spec.choose_spec.curT)), h.asid, h.aff, h.nth⟩

theorem IrqEntRM.entM {irq : U64} {m : U64 → U64} {s : S}
    (h : IrqEntRM K st (Heap.tcbs H) Cs Ω H Sg Rp Scs Nt Z Ac irq m s) (hJ : SlotJ K st H s) :
    IrqEntM K st (Heap.tcbs H) Cs Ω H Sg Rp Scs Nt Z Ac irq m s :=
  ⟨h.ent.ent hJ, h.mem⟩

end ent

section ba
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type} (ar : machine.Arch A)

/-- **`hBA` of `irq_acc_fire_wk2` / `irq_move_fire_wk2`** (the run form) from `BufAt` at the entry (`hUB`
narrowed: `irq_bufAt_run` asked P1 `UserOK` and the lookup fact). -/
theorem irq_bufAt_runB (hA : P0.ArchTotal ar) {s s' : S} {a a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    {U : Set U64} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hB : BufAt st T Cs H Sg Scs Z U s)
    (hq : IrqFire st ar s a) (h : localtimer.handle_timer_irq_local st ar s a irq p = ok (true, s', a')) :
    ∀ s1 a1 x s2 a2 s3 a3, sched.update_timestamp st ar s a = ok (s1, a1) →
      sched.check_budget st ar s1 a1 = ok (x, s2, a2) → interrupt.handle_interrupt st ar s2 a2 irq = ok (s3, a3) →
      BufAt st T Cs H Sg Scs Z U s3 := by
  intro s1' a1' x' s2' a2' s3' a3' eu' ecb' ehi'
  obtain ⟨mx, now, i2, tip, x, s1, s2, s3, a1, a2, a3, emx, hle, ei1, -, -, -, -, eu, -, -, ei2, eb4, -, -, -,
    -⟩ := fire_eqs ar hA hq h
  rw [eu] at eu'
  have e1 := ok_inj_ff eu'
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  exact hB.of_fr (fire_ibFr ar hA hI eu ei2 eb4 ecb' emx hle ei1 ehi')

end ba

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Nt Ac : Set U64} {H : Heap} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt is a local path at P1's set convention, its layout facts from P3** (module docstring):
`Pre := IrqEntRM … ∧ Q`, `Q` giving `SlotJC` at the path's `Cs`. -/
noncomputable def irq_localPathJC (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st) (Q : S → Prop)
    (hQ : ∀ s, Q s → SlotJC K st Cs H s)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (fun s => IrqEntRM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt (Heap.scBits H)
        Ac irq m s ∧ Q s) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEntR K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
        (Heap.scBits H) Ac irq s → Q s → b ∈ K.user → Aligned b →
      IrqEntR K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt (Heap.scBits H) Ac irq
        (L.wr s b v) ∧ Q (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  have hEM : ∀ s, (IrqEntRM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s) →
      IrqEntM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt (Heap.scBits H) Ac irq m s :=
    fun s h => h.1.entM (hQ s h.2).slotJ
  have hF : ∀ s a s1 a1, (IrqEntRM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s) → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl =
        ok (true, s1, a1) := fun s a s1 a1 hP hf h => by
    have hE := hEM s hP
    by_cases hnw : NoWake st s
    · exact irq_acc_fire_nw ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := (hQ s hP.2).bufAt
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        ((hQ s hP.2).slotJ.objLay (fun r hr => hr)) hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h)
        ((hQ s hP.2).slotJ.slotLayV (fun y hy => hy)) hf hnw h
  have hFm : ∀ s a s1 a1, (IrqEntRM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s) → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a irq pl = ok (true, s1, a1) := fun s a s1 a1 hP hf h => by
    have hE := hEM s hP
    by_cases hnw : NoWake st s
    · exact irq_move_fire_nw ar hA hK hUO hp hE.k hE.ent.ly hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := (hQ s hP.2).bufAt
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        ((hQ s hP.2).slotJ.objLay (fun r hr => hr)) hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h) hf hnw h
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
    Pre := fun s => IrqEntRM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s
    RS := MaxR K st lk
    WS := MaxW K st lk
    DS := IrqDec st
    isProg := hp
    obl := irq_pathObl ar hA hK hUO (fun s h => (hEM s h).ent) (fun mm => hp A ar mm) hz hm
      (fun s h q hq => irq_koF (hEM s h).ent hq) (Fl4Proofs.P2.ko_aligned hK hUO) hF
      (fun s a s1 a1 hP h => irq_move_acc ar hA hK hUO hp (hEM s hP).k (hFm s a s1 a1 hP · h) h)
    side := irq_pathSide ar hA hK (fun s h => (hEM s h).ent) (fun mm => hp A ar mm) hz hm (Fl4Proofs.P2.ko_aligned hK hUO) hF
      (fun s b v h hb hba => by
        have keep : ∀ x, Aligned x → x ∉ K.user → L.mem (L.wr s b v) x = L.mem s x :=
          fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
        have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
          E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
        obtain ⟨e1, e2⟩ := hEU s b v h.1.ent h.2 hb hba
        refine ⟨⟨⟨e1, fun x hx hxu => by rw [keep x hx hxu]; exact h.1.mem x hx hxu⟩, e2⟩,
          hlk s b v hb, ?_, ?_, irq_dec_user s b v⟩
        · funext w; simp only [MaxR, RPerm, GateOnly, eo, hlk s b v hb, L.cpu_wr]
        · funext w; simp only [MaxW, WPerm, eo, hlk s b v hb, L.cpu_wr])
    once := hro
    total := fun s a => by
      obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
      exact ⟨r, e⟩
    masks := hm }

end

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ω Ac : Set U64} {irq : U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- The timer interrupt's `Pre` for the layout `K` and memory `m` in `irq_pathsJ`: `IrqEntRM` at P1's set
convention for `K`'s heap and cores, and line slj's bundle `SlJAt K` (as `sl_pathsK`'s `Pre`). -/
def IrqPreJ (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Ω Ac : Set U64) (irq : U64)
    (m : U64 → U64) (s : S) : Prop :=
  IrqEntRM K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
    (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq m s ∧
    SlJAt (L := L) K s

/-- **The timer interrupt as an `E2E.Paths` member** (module docstring): for every layout `K` and memory `m`,
`irq_localPathJC` with `Pre := IrqPreJ K … m` (`IrqEntRM … ∧ SlJAt K`). -/
noncomputable def irq_pathsJ (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ K st Ω Ac irq m)
      (MaxR K st lk))
    (hEU : ∀ K s b v, IrqEntR K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq s →
      SlJAt (L := L) K s → b ∈ K.user → Aligned b →
      IrqEntR K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq (L.wr s b v) ∧
      SlJAt (L := L) K (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) : E2E.Paths Unit :=
  fun _ K m hK hU =>
    irq_localPathJC (K := K) (m := m) (H := K.heap) (Cs := {c : U64 | c.val < K.ncores}) (Nt := Heap.ntfns K.heap)
      (Ω := Ω) (Ac := Ac) ar hA hK hU hp hz hm (SlJAt (L := L) K) (fun _ h => slJAt_slotJC h) (hro K m)
      (hEU K) (hlk K) hPL

/-- **`StartAt` for `irq_pathsJ`** at the execution's layout `K`: `Fl4Step.start` [P] asks `IrqPreJ K … m σ`
(`IrqEntRM` and `SlJAt K σ`, as `sl_pathsK_startAt`) at the start state, plus the glue's core / locks / memory. -/
theorem irq_pathsJ_startAt (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ K st Ω Ac irq m)
      (MaxR K st lk))
    (hEU : ∀ K s b v, IrqEntR K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq s →
      SlJAt (L := L) K s → b ∈ K.user → Aligned b →
      IrqEntR K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq (L.wr s b v) ∧
      SlJAt (L := L) K (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {σ : S} (a : A) (hP : IrqPreJ K st Ω Ac irq m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (irq_pathsJ ar hA hp hz hm hro hEU hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ ar hA hp hz hm hro hEU hlk hPL () K m hK hU).body σ a) :=
  ⟨σ, a, hP, hc, hl, hμ, rfl⟩

end paths

/-! ## gen14, stage 2: `IrqLay`'s `kr` / `tab` / `ntw` from line slj's bundle -/

section lay2
variable {K : KLayout}

/-- **The region of a word of a notification is that notification** (as `LayP.region_objW`). -/
theorem _root_.Fl4Proofs.P2.OwnMap.LayP.region_ntfnW (h : LayP K) {p b : U64} (hp : K.heap p = some .ntfn)
    (hb : InW p (2 ^ 6) b) : region K b = .ntfn p := by
  have hex : ∃ q, K.heap q = some .ntfn ∧ InW q (2 ^ 6) b := ⟨p, hp, hb⟩
  unfold region
  rw [dif_neg (h.no_node (k := .ntfn) hp hb),
    dif_neg (h.no_slot (k := .ntfn) hp hb (by intro z e; cases e) (fun e => by cases e)), dif_neg, dif_pos hex]
  · have hc := Classical.choose_spec hex
    exact congrArg Region.ntfn (h.uniq (k := .ntfn) (k' := .ntfn) hc.1 hp hc.2 hb).1
  · rintro ⟨t, ht, htb⟩
    have := (h.uniq (k := .tcb) (k' := .ntfn) ht hp htb hb).2
    cases this

end lay2

section k
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}

/-- `IrqLay`'s kernel-root, ASID-table and notification fields (all from P3: `irqLayK_of_slJAt`). -/
structure IrqLayK (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Nt : Set U64) (s : S) : Prop where
  kr : Aligned (krA (L := L) s) ∧ region K (krA (L := L) s) = .none
  tab : ∀ hi : U64, hi.val < 2048 →
    (Aligned (atAF (L.ksb s) hi) ∧ region K (atAF (L.ksb s) hi) = .none) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      Aligned (peAF (L.mem s (atAF (L.ksb s) hi)) lo) ∧ region K (peAF (L.mem s (atAF (L.ksb s) hi)) lo) = .none
  ntw : ∀ n ∈ Nt, ∀ k : U64, k.val < 64 → region K (core.num.U64.wrapping_add n k) = .ntfn n

/-- **`IrqLayK` from line slj's bundle** at a P1 state (the kernel-state block's placement): the kernel root word
is a kernel global below `ksb + 256` (`RegionOKX.ks`), the ASID table words are `RegionOKX.asidT`, the pools
`SlJAtZ.pool`, a notification's words are its region (`LayP.region_ntfnW`). -/
theorem irqLayK_of_slJAt {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (h : SlJAt (L := L) K s) :
    IrqLayK K st (Heap.ntfns K.heap) s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have X := B.regionOKX
  have hP := B.layP
  have hk : L.ksb s = K.ksb := B.ksb
  have h0 := hI.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  refine ⟨?_, ?_, ?_⟩
  · have ha : Aligned (krA (L := L) s) := by
      unfold krA
      exact Fl4Proofs.P2.ks_aligned hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    have hv : (krA (L := L) s).val = (L.ksb s).val + 48 := by
      unfold krA
      rw [Fl4Proofs.P2.ks_word_val hN (by simp [layout.ks.KERNEL_ROOT])]
      simp [layout.ks.KERNEL_ROOT]
    exact ⟨ha, X.ks _ ha (by rw [hv, ← hk]; omega) (by rw [hv, ← hk]; omega)⟩
  · intro hi hhi
    rw [hk]
    refine ⟨⟨(X.asidT hi hhi).2, (X.asidT hi hhi).1⟩, fun lo hlo h0' => B.pool hi hhi h0' lo hlo⟩
  · intro n hn k hk'
    have hn' : K.heap n = some .ntfn := hn
    have hf := hP.heap.fits n _ hn'
    simp only [HKind.bits] at hf
    refine hP.region_ntfnW hn' ⟨?_, ?_⟩ <;>
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] <;>
      rw [Nat.mod_eq_of_lt (by omega)] <;> omega

/-- `IrqEnt` with only `IrqLay.iq` of its layout part (gen14 stage 2: `cs` from `SlotJ.cs`, `kr` / `tab` / `ntw`
from `irqLayK_of_slJAt`). [J] parts: `inv` / `lay` / `iq` / `asid` / `aff` / `nth`. -/
structure IrqEntI (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (irq : U64) (s : S) : Prop where
  inv : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  lay : StLay K st T Scs Z s
  iq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i →
    Aligned (core.num.U64.wrapping_add (L.ksb s) i) ∧ region K (core.num.U64.wrapping_add (L.ksb s) i) = .none
  asid : AsidOff (L := L) Ω Sg s
  aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  nth : ∀ n ∈ Nt, H n = some .ntfn

/-- `IrqEntI` and the store agreeing with the model memory `m` on aligned kernel words. -/
structure IrqEntIM (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (irq : U64) (m : U64 → U64) (s : S) : Prop where
  ent : IrqEntI K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s
  mem : ∀ x, Aligned x → x ∉ K.user → L.mem s x = m x

theorem IrqEntI.entR {irq : U64} {s : S} (h : IrqEntI K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hk : IrqLayK K st Nt s) : IrqEntR K st T Cs Ω H Sg Rp Scs Nt Z Ac irq s :=
  ⟨h.inv, h.lay, ⟨h.iq, hk.kr, hk.tab, hk.ntw⟩, h.asid, h.aff, h.nth⟩

theorem IrqEntIM.entRM {irq : U64} {m : U64 → U64} {s : S} (h : IrqEntIM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s)
    (hk : IrqLayK K st Nt s) : IrqEntRM K st T Cs Ω H Sg Rp Scs Nt Z Ac irq m s :=
  ⟨h.ent.entR hk, h.mem⟩

end k

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Nt Ac : Set U64} {H : Heap} {K : KLayout}
variable {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **The timer interrupt local path, `IrqEnt`'s layout part reduced to `iq`** (gen14 stage 2): `irq_localPathJC`
with `Pre := IrqEntIM … ∧ Q`, `Q` giving `SlotJC` (`hQ`) and `IrqLayK` (`hQL`, at a P1 state). -/
noncomputable def irq_localPathJC2 (hA : P0.ArchTotal ar) (hK : RegionOK K) (hUO : E2E.UserOK K)
    (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st) (Q : S → Prop)
    (hQ : ∀ s, Q s → SlotJC K st Cs H s)
    (hQL : ∀ s, IrqEntI K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq s → Q s → IrqLayK K st Nt s)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
      (fun s => IrqEntIM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt (Heap.scBits H)
        Ac irq m s ∧ Q s) (MaxR K st lk))
    (hEU : ∀ s b v, IrqEntI K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
        (Heap.scBits H) Ac irq s → Q s → b ∈ K.user → Aligned b →
      IrqEntI K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt (Heap.scBits H) Ac irq
        (L.wr s b v) ∧ Q (L.wr s b v))
    (hlk : ∀ s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) :=
  have hEM : ∀ s, (IrqEntIM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s) →
      IrqEntM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt (Heap.scBits H) Ac irq m s :=
    fun s h => (h.1.entRM (hQL s h.1.ent h.2)).entM (hQ s h.2).slotJ
  have hF : ∀ s a s1 a1, (IrqEntIM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s) → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (guard st (MaxR K st lk s) (MaxW K st lk s)) ar s a irq pl =
        ok (true, s1, a1) := fun s a s1 a1 hP hf h => by
    have hE := hEM s hP
    by_cases hnw : NoWake st s
    · exact irq_acc_fire_nw ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := (hQ s hP.2).bufAt
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        ((hQ s hP.2).slotJ.objLay (fun r hr => hr)) hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h)
        ((hQ s hP.2).slotJ.slotLayV (fun y hy => hy)) hf hnw h
  have hFm : ∀ s a s1 a1, (IrqEntIM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s) → IrqFire st ar s a →
      localtimer.handle_timer_irq_local st ar s a irq pl = ok (true, s1, a1) →
      localtimer.handle_timer_irq_local (mguard st
        (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (L.cpu s) (lk s) (L.mem x)
          (L.mem y))) ar s a irq pl = ok (true, s1, a1) := fun s a s1 a1 hP hf h => by
    have hE := hEM s hP
    by_cases hnw : NoWake st s
    · exact irq_move_fire_nw ar hA hK hUO hp hE.k hE.ent.ly hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := (hQ s hP.2).bufAt
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        ((hQ s hP.2).slotJ.objLay (fun r hr => hr)) hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h) hf hnw h
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
    Pre := fun s => IrqEntIM K st (Heap.tcbs H) Cs Ω H (Heap.frame H) (Heap.replies H) (Heap.scs H) Nt
      (Heap.scBits H) Ac irq m s ∧ Q s
    RS := MaxR K st lk
    WS := MaxW K st lk
    DS := IrqDec st
    isProg := hp
    obl := irq_pathObl ar hA hK hUO (fun s h => (hEM s h).ent) (fun mm => hp A ar mm) hz hm
      (fun s h q hq => irq_koF (hEM s h).ent hq) (Fl4Proofs.P2.ko_aligned hK hUO) hF
      (fun s a s1 a1 hP h => irq_move_acc ar hA hK hUO hp (hEM s hP).k (hFm s a s1 a1 hP · h) h)
    side := irq_pathSide ar hA hK (fun s h => (hEM s h).ent) (fun mm => hp A ar mm) hz hm
      (Fl4Proofs.P2.ko_aligned hK hUO) hF
      (fun s b v h hb hba => by
        have keep : ∀ x, Aligned x → x ∉ K.user → L.mem (L.wr s b v) x = L.mem s x :=
          fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
        have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
          E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
        obtain ⟨e1, e2⟩ := hEU s b v h.1.ent h.2 hb hba
        refine ⟨⟨⟨e1, fun x hx hxu => by rw [keep x hx hxu]; exact h.1.mem x hx hxu⟩, e2⟩,
          hlk s b v hb, ?_, ?_, irq_dec_user s b v⟩
        · funext w; simp only [MaxR, RPerm, GateOnly, eo, hlk s b v hb, L.cpu_wr]
        · funext w; simp only [MaxW, WPerm, eo, hlk s b v hb, L.cpu_wr])
    once := hro
    total := fun s a => by
      obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
      exact ⟨r, e⟩
    masks := hm }

end

section paths2
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ω Ac : Set U64} {irq : U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- The timer interrupt's `Pre` in `irq_pathsJ2`: `IrqEntIM` at P1's set convention for `K`'s heap and cores, and
line slj's bundle `SlJAt K`. -/
def IrqPreJ2 (K : KLayout) (st : machine.Store S) [L : LawfulStore st] (Ω Ac : Set U64) (irq : U64)
    (m : U64 → U64) (s : S) : Prop :=
  IrqEntIM K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
    (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq m s ∧
    SlJAt (L := L) K s

/-- **The timer interrupt as an `E2E.Paths` member, `IrqEnt`'s layout part reduced to `iq`** (gen14 stage 2):
`irq_localPathJC2` with `Pre := IrqPreJ2 K … m` (`IrqEntIM … ∧ SlJAt K`, `sl_pathsK`'s shape); `SlotJC` by
`slJAt_slotJC`, `IrqLayK` by `irqLayK_of_slJAt`. Premises: `hp` [P], `hz` [W], `hm` [P], `hro` [W] (per layout),
`IrqEntI`'s [J] parts (`inv` / `lay` / `iq` / `asid` / `aff`; `nth` holds for `K.heap.ntfns`), `hEU` [J] (per
layout: `IrqEntI` and `SlJAt K` kept by a user-word write), `hlk` [P], `hPL` [P]. -/
noncomputable def irq_pathsJ2 (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ2 K st Ω Ac irq m)
      (MaxR K st lk))
    (hEU : ∀ K s b v, IrqEntI K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq s →
      SlJAt (L := L) K s → b ∈ K.user → Aligned b →
      IrqEntI K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq (L.wr s b v) ∧
      SlJAt (L := L) K (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) : E2E.Paths Unit :=
  fun _ K m hK hU =>
    irq_localPathJC2 (K := K) (m := m) (H := K.heap) (Cs := {c : U64 | c.val < K.ncores})
      (Nt := Heap.ntfns K.heap) (Ω := Ω) (Ac := Ac) ar hA hK hU hp hz hm (SlJAt (L := L) K)
      (fun _ h => slJAt_slotJC h) (fun _ hE h => irqLayK_of_slJAt hE.inv h) (hro K m) (hEU K) (hlk K) hPL

/-- **`StartAt` for `irq_pathsJ2`**: `Fl4Step.start` [P] asks `IrqPreJ2 K … m σ` (`IrqEntIM` and `SlJAt K σ`) at
the start state, plus the glue's core / locks / memory (as `sl_pathsK_startAt`). -/
theorem irq_pathsJ2_startAt (hA : P0.ArchTotal ar) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p)
    (hm : E2E.MasksWr st)
    (hro : ∀ K m, E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user) (IrqPreJ2 K st Ω Ac irq m)
      (MaxR K st lk))
    (hEU : ∀ K s b v, IrqEntI K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq s →
      SlJAt (L := L) K s → b ∈ K.user → Aligned b →
      IrqEntI K st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac irq (L.wr s b v) ∧
      SlJAt (L := L) K (L.wr s b v))
    (hlk : ∀ (K : KLayout) s b v, b ∈ K.user → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {σ : S} (a : A) (hP : IrqPreJ2 K st Ω Ac irq m σ) {c : U64} {hs : U64 → Prop}
    (hc : L.cpu σ = c) (hl : lk σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (irq_pathsJ2 ar hA hp hz hm hro hEU hlk hPL () K m hK hU) c hs μ
      ((irq_pathsJ2 ar hA hp hz hm hro hEU hlk hPL () K m hK hU).body σ a) :=
  ⟨σ, a, hP, hc, hl, hμ, rfl⟩

end paths2

end Fl4Proofs.P2
