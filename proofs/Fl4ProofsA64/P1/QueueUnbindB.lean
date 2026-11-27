/-
P1 (aarch64): **`vcpu::unbind`, `vcpu::detach` and the thread kind's finalisation with a bound VCPU**, over
corrected placements (the two premises gen 25 found false: `FinPl`'s "no bound VCPU" thread clause and `rcw`'s
"`RUN_CALLER` is a user word").

* `VcObj T Ω Sg s v`: the facts of a VCPU object `vcpu::unbind` reads: its words `v + o` (`o < 4096`, aligned)
  are aligned words of `Ω` off `Sg` (`VcWords`, the shape of [P] `VcpuW`), its `TCB` and `RUN_CALLER` words are
  `0` or threads.
* **[P] `VcPl`** (the corrected placements, at every `Fr0 ∧ BXI` state from a decode start, as every
  `DelPlaceAt` field):
  - `vcb`: a thread's nonzero bound-VCPU word (TCB + 3664, `tl::VCPU`) names a VCPU object (`VcObj`). Replaces
    `FinPl`'s false "the word is 0". Source (crates/fl4-core/src/arch/aarch64/vcpu.rs): the word is written only
    by `set_bound` — `decode_set_tcb` (377–399: `vc` an invoked `.Vcpu` cap's object, after `vc + TCB := target`),
    `unbind` (306–316: `0`); a fresh TCB has it `0` (retype zeroes the object). `vc + TCB` is written by
    `decode_set_tcb` (a thread cap's TCB) and `unbind` (`0`), `vcpu::init` (`0`); `vc + RUN_CALLER` by
    `decode_run` (861: `ct`, the current thread), `cancel_run` / `complete_run` / `unbind` (`0`); a TCB's
    deletion runs `vcpu::detach` (`cancel_run`, so the `RUN_CALLER` of its run VCPU is cleared, and `unbind` of
    its bound VCPU), a VCPU's deletion `vcpu::finalise` (`unbind`).
  - `rcv`: a thread's nonzero `RUN_VCPU` word (TCB + 3672) names a VCPU object's words (`VcWords`). Replaces
    `rcw`'s false "`RUN_CALLER` of it is a user word" (`UserW`, outside `Ω`): `RUN_VCPU(ct) := vc` is written only
    by `decode_run` (862) for the invoked `.Vcpu vc` cap ([P] `VcpuW`: its words are in `Ω \ Sg`), cleared by
    `cancel_run` / `complete_run` / `unbind`.
  - `rbuf`: a thread's run frame (the frame of its IPC-buffer cap at its run VCPU's `RUN_OFFSET`, when
    `complete_run`'s checks pass) consists of `UsrW` words: the shape of P3Place's [P] `vmpl` (`RunBuf U` with
    `U` ⊆ `UsrW`), stated for every thread (`unbind` completes the run of a thread that need not be current).
    `UsrW` does not exclude `Ω` (frames are `.other` heap objects, QueueRetype `newKind`).
* `UbF s0 s s'`: `Cur0 s0 s'`, the idle thread kept, zero `RUN_VCPU` words kept zero, [J] `RunVcpuInv` kept.
* The steps: `UbF.ofW` (any writes of words outside the TCBs or of register words), `UbF.omega` (an `Ω \ Sg`
  word), `UbF.usr` (`UsrW` words), `UbF.regs`, `UbF.bnd0` / `UbF.rv0` (a TCB's bound-VCPU word, its
  `RUN_VCPU := 0`), `smp.remote_tcb_stall.ub`, `sched.set_thread_state.running_ub` (`TS_RUNNING_VM` → `RUNNING`).
* **`vcpu.complete_run.ub`** (any thread in `TS_RUNNING_VM`, current or not), **`vcpu.unbind.ub`**,
  **`vcpu.detach.ub`** (cancel_run, then the unbind of the bound VCPU), **`fin_thread.ubR`** (the thread kind's
  `finalise_cap_object` from a `Cur0R` state: `Cur0R` after; QueueFinThr7's `finThrRest` text after `detach`).

Named premises: **[P] `VcPl`** (new, above). No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueEntryGaps7
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
variable {A : Type _} {ar : machine.Arch A}

local macro "ubo" : tactic => `(tactic| first | omega | (simp; omega) | simp | (simp at *; omega))

/-- The facts of a VCPU object that `vcpu::unbind` reads (module docstring). -/
def VcObj (st : machine.Store S) [L : LawfulStore st] (T Ω Sg : Set U64) (s : S) (v : U64) : Prop :=
  VcWords Ω Sg v ∧
  (L.mem s (core.num.U64.wrapping_add v vcpu.TCB) = 0#u64 ∨ L.mem s (core.num.U64.wrapping_add v vcpu.TCB) ∈ T) ∧
  (L.mem s (core.num.U64.wrapping_add v vcpu.RUN_CALLER) = 0#u64 ∨
    L.mem s (core.num.U64.wrapping_add v vcpu.RUN_CALLER) ∈ T)

/-- **[P] (a64) The VCPU placements** (module docstring): `vcb` (a bound VCPU is a VCPU object), `rcv` (a run
VCPU's words are aligned words of `Ω` off `Sg`), `rbuf` (a thread's run frame consists of `UsrW` words), at every
`Fr0 ∧ BXI` state from `s0`. -/
structure VcPl (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (s0 : S) : Prop where
  vcb : ∀ (Ac : Set U64) (s : S) (p : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    p ∈ T → L.mem s (core.num.U64.wrapping_add p 3664#u64) ≠ 0#u64 →
    VcObj st T Ω Sg s (L.mem s (core.num.U64.wrapping_add p 3664#u64))
  rcv : ∀ (Ac : Set U64) (s : S) (p : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA p))
  rbuf : ∀ (Ac : Set U64) (s : S) (p : U64), Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    p ∈ T → RunBuf st {b | UsrW st T Cs H Sg Scs Z s b} s p

/-- The frame of an unbind step from `s` inside a step from `s0` (module docstring). -/
structure UbF (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (s0 s s' : S) : Prop where
  cur : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s'
  idle : L.idleW s' = L.idleW s
  rv0 : ∀ z ∈ T, L.mem s (runVcpuA z) = 0#u64 → L.mem s' (runVcpuA z) = 0#u64
  rvi : RunVcpuInv st T s → RunVcpuInv st T s'

/-- Every thread's bound-VCPU word kept. -/
def BndK (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ z ∈ T, L.mem s' (core.num.U64.wrapping_add z 3664#u64) = L.mem s (core.num.U64.wrapping_add z 3664#u64)

/-- Every thread's state word kept. -/
def StK (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ z ∈ T, L.mem s' (stA z) = L.mem s (stA z)

theorem UbF.refl {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) : UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s :=
  ⟨h, rfl, fun _ _ e => e, id⟩

theorem UbF.trans {s0 s s1 s2 : S} (h1 : UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s1)
    (h2 : UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1 s2) : UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s2 :=
  ⟨h2.cur, h2.idle.trans h1.idle, fun z hz e => h2.rv0 z hz (h1.rv0 z hz e), fun r => h2.rvi (h1.rvi r)⟩

theorem BndK.refl (s : S) : BndK st T s s := fun _ _ => rfl

theorem BndK.trans {s s1 s2 : S} (h1 : BndK st T s s1) (h2 : BndK st T s1 s2) : BndK st T s s2 :=
  fun z hz => (h2 z hz).trans (h1 z hz)

theorem StK.trans {s s1 s2 : S} (h1 : StK st T s s1) (h2 : StK st T s1 s2) : StK st T s s2 :=
  fun z hz => (h2 z hz).trans (h1 z hz)

/-- A TCB field outside a write set (words outside the objects, or other TCB fields) is kept. -/
theorem wi_keep {s s' : S} {B : U64 → Prop} (hw : WritesIn st s s' B) (hT : TcbPlaced T)
    {z K' : U64} (hz : z ∈ T) (hK' : K'.val < 4096) (h8 : K'.val % 8 = 0)
    (hB : ∀ b, B b → OutsideObjs st T Cs s b ∨
      ∃ y ∈ T, ∃ K : U64, K.val < 4096 ∧ (y = z → K.val ≠ K'.val) ∧ b = core.num.U64.wrapping_add y K) :
    L.mem s' (core.num.U64.wrapping_add z K') = L.mem s (core.num.U64.wrapping_add z K') :=
  hw.mem_eq (field_aligned (hT z hz) hK' h8) fun hb => by
    rcases hB _ hb with hO | ⟨y, hy, K, hK, hne, e⟩
    · exact out_ne_field hO hz (hT z hz) hK' rfl
    · exact field_ne (hT y hy) (hT z hz) hK hK' hne e.symm

/-- Writes outside the nodes keep the action, idle, current thread and current SC words. -/
theorem ani_of_wi {s s' : S} {B : U64 → Prop} (hw : WritesIn st s s' B) (hN : NodePlaced st T s (L.cpu s))
    (hc : L.cpu s ∈ Cs) (hT : TcbPlaced T)
    (hB : ∀ b, B b → OutsideObjs st T Cs s b ∨
      ∃ y ∈ T, ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add y K) :
    ANI st s s' ∧ L.cscW s' = L.cscW s := by
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
    intro o ho h8
    rw [hw.2.1, nodeAt_of_ksb hw.1]
    refine hw.mem_eq (nodeAt_aligned hN ho h8) fun hb => ?_
    rcases hB _ hb with hO | ⟨y, hy, K, hK, e⟩
    · exact out_ne_node hO hc hN ho rfl
    · exact node_ne_field hN ho hy (hT y hy) hK e
  refine ⟨⟨nd _ (by rw [act_val]; omega) (by rw [act_val]), nd _ (by rw [idle8]; omega) (by rw [idle8]),
    nd _ (by rw [curth0]; omega) (by rw [curth0])⟩, ?_⟩
  unfold LawfulStore.cscW LawfulStore.nodeA
  exact nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])

/-- **A step writing words outside the TCBs or register words** (`K < 3328`), with `BlkOK` after and its words
`Cur0W` words. -/
theorem UbF.ofW {s0 s s' : S} {B : U64 → Prop} {Ac' : Set U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' s') (hw : WritesIn st s s' B)
    (hC : ∀ b, B b → Cur0W st T Cs Ω H Sg Scs Z s b)
    (hB : ∀ b, B b → OutsideObjs st T Cs s b ∨
      ∃ y ∈ T, ∃ K : U64, K.val < 3328 ∧ b = core.num.U64.wrapping_add y K) :
    UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧ BndK st T s s' ∧ StK st T s s' := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have q := hb1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  have hct : L.curW s ∈ T := q.curT
  have kp : ∀ z ∈ T, ∀ K' : U64, 3328 ≤ K'.val → K'.val < 4096 → K'.val % 8 = 0 →
      L.mem s' (core.num.U64.wrapping_add z K') = L.mem s (core.num.U64.wrapping_add z K') :=
    fun z hz K' h1 h2 h3 => wi_keep hw hT hz h2 h3 fun b hb' => (hB b hb').imp id
      fun ⟨y, hy, K, hK, e⟩ => ⟨y, hy, K, by omega, fun _ => by omega, e⟩
  obtain ⟨an, ecs⟩ := ani_of_wi hw hN q.cur hT fun b hb' => (hB b hb').imp id
      fun ⟨y, hy, K, hK, e⟩ => ⟨y, hy, K, by omega, e⟩
  have kst : StK st T s s' := fun z hz => by rw [stA_eq]; exact kp _ hz _ (by simp) (by simp) (by simp)
  refine ⟨⟨Cur0.mk h (BlkOK.bxi hb) an.2.2 ecs (Or.inl ?_) (Or.inl an.1) (Or.inl (kst _ hct)) (hw.mono hC),
    an.2.1, fun z hz e => (kp z hz 3672#u64 (by simp) (by simp) (by simp)).trans e,
    fun hRV => hRV.keep kst (fun z hz => kp z hz 3672#u64 (by simp) (by simp) (by simp))⟩,
    fun z hz => kp z hz 3664#u64 (by simp) (by simp) (by simp), kst⟩
  rw [scA_eq]; exact kp _ hct _ (by simp) (by simp) (by simp)

/-- **A write of an aligned word of `Ω` off `Sg`** (a VCPU word). -/
theorem UbF.omega {s0 s : S} {b v : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ha : Aligned b)
    (hO : b ∈ Ω) (hS : b ∉ Sg) :
    UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s (L.wr s b v) ∧ BndK st T s (L.wr s b v) ∧ StK st T s (L.wr s b v) := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have hw := writesIn_wr (st := st) (s := s) (v := v) ha
  obtain ⟨hb2, -⟩ := blk_of_capw hb1.blk hw fun x e => by subst e; exact Or.inr ⟨hO, hS⟩
  exact UbF.ofW h hb2 hw (fun x e => by subst e; exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hO, hS⟩))))
    fun x e => by subst e; exact Or.inl (hb1.1.choose_spec.choose_spec.omega _ hO)

/-- **Writes of `UsrW` words** (the run-frame copy). -/
theorem UbF.usr {s0 s s' : S} {U : Set U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hw : WritesIn st s s' (· ∈ U)) :
    UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧ BndK st T s s' ∧ StK st T s s' := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  obtain ⟨hb2, -⟩ := bufw_xfer hb1.blk hU (hw.mono fun b hb => (Or.inr hb : XferFoot T U b))
  refine UbF.ofW h hb2 hw (fun b hb => ?_) fun b hb => Or.inl (hU b hb).out
  by_cases hO : b ∈ Ω
  · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hO, (hU b hb).sg⟩)))
  · exact Or.inr (Or.inr (Or.inr ⟨(hU b hb).out, hO, (hU b hb).eps⟩))

/-- **Register writes of a thread** (`RegW`). -/
theorem UbF.regs {s0 s s' : S} {y : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hy : y ∈ T)
    (hw : WritesIn st s s' (RegW y)) :
    UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧ BndK st T s s' ∧ StK st T s s' := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  obtain ⟨hb2, -⟩ := bufw_xfer (U := ∅) hb1.blk (fun b hb => absurd hb (by simp))
    (hw.mono fun b ⟨K, _, h2, h3, e⟩ => (Or.inl ⟨y, hy, K, h2, h3, e⟩ : XferFoot T ∅ b))
  refine UbF.ofW h hb2 hw (fun b ⟨K, h1, h2, h3, e⟩ => ?_) fun b ⟨K, _, h2, _, e⟩ => Or.inr ⟨y, hy, K, h2, e⟩
  subst e; exact Or.inl (kw_field hy (by omega) (by omega) ⟨by omega, by omega⟩)

/-- A write of a TCB's bound-VCPU word (3664) or `RUN_VCPU` word (3672) keeps `BlkOK` (`rv_all`'s proof). -/
theorem blk_vf {s : S} {t K v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hK : K.val = 3664 ∨ K.val = 3672) :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add t K) v) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  obtain ⟨b1, b2⟩ := bx_field (K := K) (v := v) h0 hB hX hSg.sub ht (by omega) (by omega)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega) (Or.inr (by omega))
  exact ⟨⟨Q, R, inv_wr_field h0 ht (by omega) (by omega)
    (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega)⟩, b1, b2,
    SCsOK.field h0 hS hX ht (by omega) (by omega) (by omega),
    ⟨hSg.sub, fun b hb => by rw [L.ksb_wr]; exact hSg.ks b hb, fun o h1 h2 => by rw [L.ksb_wr]; exact hSg.ksΩ o h1 h2⟩⟩

/-- The common part of the 3664 / 3672 writes. -/
theorem Cur0.vfC {s0 s : S} {t K v : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T)
    (hK : K.val = 3664 ∨ K.val = 3672) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (core.num.U64.wrapping_add t K) v) ∧
      L.idleW (L.wr s (core.num.U64.wrapping_add t K) v) = L.idleW s ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add t K) = v ∧
      ∀ z ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (z = t → K.val ≠ K'.val) →
        L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add z K') =
          L.mem s (core.num.U64.wrapping_add z K') := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have q := hb1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hN := q.nodes _ q.cur
  have hct : L.curW s ∈ T := q.curT
  have hK1 : K.val < 4096 := by omega
  have hK2 : K.val % 8 = 0 := by omega
  have ha := field_aligned (hT t ht) hK1 hK2
  have hw := writesIn_wr (st := st) (s := s) (v := v) ha
  have hb2 := blk_vf (v := v) hb1.blk ht hK
  have kp : ∀ z ∈ T, ∀ K' : U64, K'.val < 4096 → K'.val % 8 = 0 → (z = t → K.val ≠ K'.val) →
      L.mem (L.wr s (core.num.U64.wrapping_add t K) v) (core.num.U64.wrapping_add z K') =
        L.mem s (core.num.U64.wrapping_add z K') :=
    fun z hz K' h1 h2 hne => wi_keep (Cs := Cs) hw hT hz h1 h2 fun b e => Or.inr ⟨t, ht, K, hK1, fun e' => hne e'.symm, e⟩
  obtain ⟨an, ecs⟩ := ani_of_wi hw hN q.cur hT fun b e => Or.inr ⟨t, ht, K, hK1, e⟩
  refine ⟨Cur0.mk h (BlkOK.bxi hb2) an.2.2 ecs (Or.inl ?_) (Or.inl an.1) (Or.inl ?_)
    (hw.mono fun b e => ?_), an.2.1, L.mem_wr_same ha, kp⟩
  · rw [scA_eq]; exact kp _ hct _ (by simp) (by simp) (fun _ => by ubo)
  · rw [stA_eq]; exact kp _ hct _ (by simp) (by simp) (fun _ => by ubo)
  · subst e; exact Or.inl (kw_field ht (by omega) (by omega) ⟨by omega, by omega⟩)

/-- **A write of a thread's bound-VCPU word** (`set_bound`). -/
theorem UbF.bnd0 {s0 s : S} {t v : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T) :
    UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s (L.wr s (core.num.U64.wrapping_add t 3664#u64) v) ∧
      StK st T s (L.wr s (core.num.U64.wrapping_add t 3664#u64) v) := by
  obtain ⟨c, ei, -, kp⟩ := Cur0.vfC (K := 3664#u64) (v := v) h ht (Or.inl (by simp))
  have kst : StK st T s (L.wr s (core.num.U64.wrapping_add t 3664#u64) v) := fun z hz => by
    rw [stA_eq]; exact kp _ hz _ (by simp) (by simp) (fun _ => by simp)
  have krv : ∀ z ∈ T, L.mem (L.wr s (core.num.U64.wrapping_add t 3664#u64) v) (runVcpuA z) =
      L.mem s (runVcpuA z) := fun z hz => kp _ hz 3672#u64 (by simp) (by simp) (fun _ => by simp)
  exact ⟨⟨c, ei, fun z hz e => (krv z hz).trans e, fun hRV => hRV.keep kst krv⟩, kst⟩

/-- **A thread's `RUN_VCPU := 0`.** -/
theorem UbF.rv0w {s0 s : S} {t : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T) :
    UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s (L.wr s (core.num.U64.wrapping_add t 3672#u64) 0#u64) ∧
      BndK st T s (L.wr s (core.num.U64.wrapping_add t 3672#u64) 0#u64) ∧
      StK st T s (L.wr s (core.num.U64.wrapping_add t 3672#u64) 0#u64) ∧
      L.mem (L.wr s (core.num.U64.wrapping_add t 3672#u64) 0#u64) (runVcpuA t) = 0#u64 := by
  obtain ⟨c, ei, e0, kp⟩ := Cur0.vfC (K := 3672#u64) (v := 0#u64) h ht (Or.inr (by simp))
  have kst : StK st T s (L.wr s (core.num.U64.wrapping_add t 3672#u64) 0#u64) := fun z hz => by
    rw [stA_eq]; exact kp _ hz _ (by simp) (by simp) (fun _ => by simp)
  have krv : ∀ z ∈ T, z ≠ t → L.mem (L.wr s (core.num.U64.wrapping_add t 3672#u64) 0#u64) (runVcpuA z) =
      L.mem s (runVcpuA z) := fun z hz hne => kp _ hz 3672#u64 (by simp) (by simp) (fun e => absurd e hne)
  refine ⟨⟨c, ei, fun z hz e => ?_, fun hRV => ?_⟩,
    fun z hz => kp _ hz 3664#u64 (by simp) (by simp) (fun _ => by simp), kst, e0⟩
  · by_cases ez : z = t
    · subst ez; exact e0
    · exact (krv z hz ez).trans e
  · intro z hz hne
    rw [kst z hz]
    refine hRV z hz ?_
    by_cases ez : z = t
    · subst ez; exact absurd e0 hne
    · rwa [← krv z hz ez]

/-- **The stall of any thread.** -/
theorem smp.remote_tcb_stall.ub (hA : P0.ArchTotal ar) {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (a : A) (y : U64) :
    smp.remote_tcb_stall st ar s a y ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧ BndK st T s s' ∧
      StK st T s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have hct : L.curW s ∈ T := hb1.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (smp.remote_tcb_stall.bxi hA s a y hb1) ?_
  rintro ⟨s1, a1⟩ ⟨hb2, ea, ec, ei, ecs, fld, -, wn⟩
  have kst : StK st T s s1 := fun z hz => by rw [stA_eq]; exact fld z hz _ (by simp) (by simp)
  refine ⟨⟨Cur0.mk h hb2 ec ecs (Or.inl ?_) (Or.inl ea) (Or.inl (kst _ hct))
    (wn.mono fun _ hb' => NodeW.cur0w hb1.1.choose_spec.choose_spec.cur hb'), ei,
    fun z hz e => (fld z hz 3672#u64 (by simp) (by simp)).trans e,
    fun hRV => hRV.keep kst (fun z hz => fld z hz 3672#u64 (by simp) (by simp))⟩,
    fun z hz => fld z hz _ (by simp) (by simp), kst⟩
  rw [scA_eq]; exact fld _ hct _ (by simp) (by simp)

/-- **`set_thread_state y RUNNING` of a thread in `TS_RUNNING_VM`** (current or not) running no VCPU. -/
theorem sched.set_thread_state.running_ub {s0 s : S} {y : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (hy : y ∈ T) (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM) (hrv : L.mem s (runVcpuA y) = 0#u64) :
    sched.set_thread_state st s y sched.TS_RUNNING ⦃ s' => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧
      BndK st T s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := hb1.blk
  have hct : L.curW s ∈ T := h0.curT
  have hr : Runnable (L.mem s (stA y)) := by rw [hvm]; exact Or.inr (Or.inr rfl)
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ y :=
    hX.noref (h0.tcbs y hy) (runnable_ne_reply hr) (runnable_ne_recv hr)
  refine WP.spec_mono (WP.spec_and (sts_all s y _ Q R h0 hB hX hS hSg hy not_blocked_running running_ne
    (Or.inr (runnable_ok hr).1) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s y _ h0 hy)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, e1, k⟩, f1⟩
  have hb2 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac1 s' := ⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hS1, hSg1⟩
  refine ⟨⟨Cur0.mk h (BlkOK.bxi hb2) k.curW k.cscW (Or.inl (k.scf hct)) k.act ?_
    (Foot.cur0w f1 (Set.empty_subset _)), k.idleW, fun z hz e => ?_, fun hRV => RunVcpuInv.keepT hRV k (Or.inr hrv)⟩,
    fun z hz => k.fld z hz 3664#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)⟩
  · by_cases e : L.curW s = y
    · right; rw [e, e1]; exact nbr_runnable runnable_running
    · left; exact k.stf hct e
  · exact (k.fld z hz 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)).trans e

set_option maxHeartbeats 4000000 in
/-- **`complete_run` of any thread in `TS_RUNNING_VM`** (the run frame of `UsrW` words `U`, the run VCPU's words in
`Ω \ Sg`). -/
theorem vcpu.complete_run.ub (hA : P0.ArchTotal ar) {s0 s : S} {U : Set U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (y stop m1 m2 m3 : U64)
    (hy : y ∈ T) (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM)
    (hrc : L.mem s (runVcpuA y) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA y)))
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : RunBuf st U s y) :
    vcpu.complete_run st ar s a y stop m1 m2 m3 ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧
      BndK st T s s' ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have hT := hb1.1.choose_spec.choose_spec.tcbs
  have hta := hT y hy
  have hal : ∀ b ∈ U, Aligned b := fun b hb => (hU b hb).out.1
  unfold vcpu.complete_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add y 3672#u64) = 0#u64
  · rw [if_pos hv0]; exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s⟩
  rw [if_neg hv0]
  refine WP.spec_bind (hA.vcpu_flush_state _ _ _) fun a1 _ => ?_
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (· ∈ U)) ?_ fun s2 w2 => ?_
  · split
    · have hs : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by
        simp [obj.Tcb.slot, lift, sbWordA]
      rw [hs, bind_ok]
      refine WP.spec_bind (spec_eq' (P0.obj.Slot.cap.p0 st (sbWordA y) s L.total)) fun c hc0 => ?_
      obtain ⟨hc, -⟩ := hc0
      cases c
      all_goals try exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rename_i ptr size rights dev c1 c2 c3 c4
      refine WP.spec_bind (spec_eq' (P0.capability.FrameSize.bits.p0 size)) fun bits ⟨hbits, _⟩ => ?_
      have h63 : (bits &&& 63#u64).val < 64 := by
        rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
      refine WP.spec_bind (spec_eq' (P0.one_shift_positive _ h63)) fun sz ⟨hsz, _⟩ => ?_
      by_cases hd : dev = true
      · rw [if_pos hd]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rw [if_neg hd]
      split
      · rename_i hrw
        split
        · rename_i ho
          split
          · rename_i hlt
            have hlt' : (L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64))
                vcpu.RUN_OFFSET)).val < sz.val := hlt
            step as ⟨i7, hi7⟩
            split
            · rename_i hge
              have hge' : 1024 ≤ i7.val := by scalar_tac
              have hF := hbuf ptr size rights dev c1 c2 c3 c4 bits sz hc (by simpa using hd) hrw hbits hsz
                ho hlt' (by unfold runOffA runVcpuA; omega)
              exact vcpu.read_state_to_frame.fw hA s a1 _ _ _ hF hal
            · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
          · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  obtain ⟨F2, B2, S2⟩ := UbF.usr h hU w2
  have hw : VcWords Ω Sg (L.mem s (core.num.U64.wrapping_add y 3672#u64)) := hrc hv0
  have hx := hw vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
  obtain ⟨F3, B3, S3⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
  obtain ⟨F4, B4, S4, rv4⟩ := UbF.rv0w F3.cur hy
  refine vck_regs _ y stop m1 m2 m3 hta fun s10 w10 => ?_
  obtain ⟨F10, B10, S10⟩ := UbF.regs F4.cur hy w10
  have F := ((F2.trans F3).trans F4).trans F10
  have B := ((B2.trans B3).trans B4).trans B10
  have st10 : L.mem s10 (stA y) = sched.TS_RUNNING_VM := by
    rw [(((S2.trans S3).trans S4).trans S10) y hy]; exact hvm
  refine WP.spec_bind (sched.set_thread_state.running_ub F.cur hy st10 (F10.rv0 y hy rv4)) fun s11 ⟨F11, B11⟩ =>
    vck_vm_tail hA s11 a1 y ⟨F.trans F11, B.trans B11⟩

set_option maxHeartbeats 4000000 in
/-- **`vcpu::unbind` of a VCPU object** (`hV`: the VCPU's facts at every later `Cur0` state that keeps the
bound-VCPU words): completes or cancels the `ARMVCPURun` of its `RUN_CALLER`, then detaches its bound TCB. -/
theorem vcpu.unbind.ub (hA : P0.ArchTotal ar) {s0 s : S} (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0)
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (v : U64)
    (hV : ∀ s' : S, Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' → BndK st T s s' → VcObj st T Ω Sg s' v) :
    vcpu.unbind st ar s a v ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ⦄ := by
  have V0 := hV s h (BndK.refl s)
  unfold vcpu.unbind vcpu.set_bound
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec, eq_of_spec_fd P0.Consts.layout.tcb.VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1) ?_ ?_
  · split
    · rename_i hne
      have hc0 : L.mem s (core.num.U64.wrapping_add v vcpu.RUN_CALLER) ≠ 0#u64 := by simpa using hne
      have hcT := V0.2.2.resolve_left hc0
      refine WP.spec_bind (smp.remote_tcb_stall.ub hA h a _) ?_
      rintro ⟨s2, a2⟩ ⟨F2, B2, -⟩
      try simp only [uncurry_apply_pair, WP.uncurry'_pair]
      step with obj.Tcb.state.spec as ⟨i1, ei1⟩
      split
      · rename_i hvm
        obtain ⟨Ac2, hb2⟩ := F2.cur.bxi
        refine WP.spec_mono (vcpu.complete_run.ub hA F2.cur a2 _ _ _ _ _ hcT (by rw [← ei1]; exact hvm)
          (fun h0 => Pl.rcv Ac2 s2 _ F2.cur.fr hb2 hcT h0) (fun b hb => hb) (Pl.rbuf Ac2 s2 _ F2.cur.fr hb2 hcT)) ?_
        rintro ⟨s3, a3⟩ ⟨F3, B3⟩
        exact ⟨F2.trans F3, B2.trans B3⟩
      · have hx := V0.1 vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
        obtain ⟨F3, B3, -⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
        obtain ⟨F4, B4, -, -⟩ := UbF.rv0w F3.cur hcT
        exact (WP.spec_ok _).2 ⟨(F2.trans F3).trans F4, (B2.trans B3).trans B4⟩
    · exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  have V1 := hV s1 F1.cur B1
  split
  · exact (WP.spec_ok _).2 F1
  rename_i ht0
  have htT := V1.2.1.resolve_left ht0
  refine WP.spec_bind (smp.remote_tcb_stall.ub hA F1.cur a1 _) ?_
  rintro ⟨s2, a2⟩ ⟨F2, -, -⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine WP.spec_bind (hA.vcpu_flush a2 v) fun a3 _ => ?_
  have hx0 := V1.1 vcpu.TCB (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  have hx8 := V1.1 vcpu.OWNER_CPU (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])
  obtain ⟨F3, -, -⟩ := UbF.omega (v := 0#u64) F2.cur hx0.1 hx0.2.1 hx0.2.2
  obtain ⟨F4, -, -⟩ := UbF.omega (v := 0#u64) F3.cur hx8.1 hx8.2.1 hx8.2.2
  obtain ⟨F5, -⟩ := UbF.bnd0 (v := 0#u64) F4.cur htT
  obtain ⟨Ac5, hb5⟩ := F5.cur.bxi
  have hT5 := hb5.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ _ _ L.total) fun old _ => ?_
  refine WP.spec_bind (P0.regs.sanitise.p0 _ _) fun i4 _ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW _ (hT5 _ htT) (by simp [layout.reg.SPSR_EL1]) (WritesIn.refl _ _))
    fun s6 w6 => ?_
  obtain ⟨F6, -, -⟩ := UbF.regs F5.cur htT w6
  exact vck_vm_tail hA s6 a3 _ (((((F1.trans F2).trans F3).trans F4).trans F5).trans F6)

set_option maxHeartbeats 2000000 in
/-- **`vcpu::detach` of any thread**: `cancel_run` (its run VCPU's `RUN_CALLER` an `Ω \ Sg` word, `rcv`), then the
`unbind` of its bound VCPU (`vcb`). Ends with `RUN_VCPU p = 0`. -/
theorem vcpu.detach.ub (hA : P0.ArchTotal ar) {s0 s : S} (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0)
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (p : U64) (hp : p ∈ T) :
    vcpu.detach st ar s a p ⦃ s' _ => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s s' ∧
      L.mem s' (runVcpuA p) = 0#u64 ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  unfold vcpu.detach
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    L.mem r.1 (runVcpuA p) = 0#u64) ?_ ?_
  · unfold vcpu.cancel_run
    rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
    simp only [lift, bind_ok, L.read_eq, L.write_eq]
    split
    · rename_i hne
      have hv : L.mem s (runVcpuA p) ≠ 0#u64 := by simpa [runVcpuA] using hne
      have hw := Pl.rcv Ac1 s p h.fr hb1 hp hv
      have hx := hw vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
      obtain ⟨F1, B1, -⟩ := UbF.omega (v := 0#u64) h hx.1 hx.2.1 hx.2.2
      obtain ⟨F2, B2, -, e2⟩ := UbF.rv0w F1.cur hp
      exact (WP.spec_ok _).2 ⟨F1.trans F2, B1.trans B2, e2⟩
    · rename_i heq
      exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, UScalar.eq_of_val_eq (by simpa [runVcpuA] using heq)⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, rv1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  step with vcpu.bound.spec as ⟨v, ev⟩
  split
  · rename_i hne
    have hv0 : v ≠ 0#u64 := by simpa using hne
    refine WP.spec_mono (vcpu.unbind.ub hA Pl F1.cur a1 v fun s' h' b' => ?_) ?_
    · obtain ⟨Ac', hb'⟩ := h'.bxi
      have e' : L.mem s' (core.num.U64.wrapping_add p 3664#u64) = v := by rw [b' p hp, ev]
      have := Pl.vcb Ac' s' p h'.fr hb' hp (by rw [e']; exact hv0)
      rw [e'] at this; exact this
    · rintro ⟨s2, a2⟩ F2
      exact ⟨F1.trans F2, F2.rv0 p hp rv1⟩
  · exact (WP.spec_ok _).2 ⟨F1, rv1⟩

set_option maxHeartbeats 2000000 in
/-- **The thread kind's `finalise_cap_object` with a bound VCPU or a run in flight**, `Cur0R` to `Cur0R`:
the stall, `vcpu.detach.ub`, then QueueFinThr7's `finThrRest` (`blk`, `curR`) and QueueFinRvSt's `rvi`. -/
theorem fin_thread.ubR (hA : P0.ArchTotal ar) {s0 s : S} (Pl : VcPl st T Cs Ω H Sg Rp Scs Nt Z s0)
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hRV : RunVcpuInv st T s) (a : A) (p : U64) (fin : Bool)
    (hp : p ∈ T) (hid : p ≠ L.idleW s) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ∧
      RunVcpuInv st T r.2.1 ⦄ := by
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 ⟨h, hRV⟩
  rw [fin_thread_split]
  refine WP.spec_bind (smp.remote_tcb_stall.ub hA h a p) ?_
  rintro ⟨s1, a1⟩ ⟨F1, -, -⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  refine WP.spec_bind (vcpu.detach.ub hA Pl F1.cur a1 p hp) ?_
  rintro ⟨s2, a2⟩ ⟨F2, rv2⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have F12 := F1.trans F2
  obtain ⟨Ac2, hb2⟩ := F12.cur.bxi
  have hna : L.actionW s2 ≠ p := F12.cur.na p hp
  have hidle : L.idleW s2 ≠ p := by rw [F12.idle]; exact Ne.symm hid
  have hct : L.curW s2 ∈ T := hb2.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (WP.spec_and (WP.spec_and (finThrRest.blk hA s2 a2 p hb2.blk hp hna hidle rv2)
    (finThrRest.curR hA s2 a2 p (L.curW s2) hb2.blk hp hna hidle hct rv2))
    (finThrRest.rvi hA s2 a2 p hb2.blk hp hna hidle rv2 (F12.rvi hRV))) ?_
  rintro ⟨r1, s3, a3⟩ ⟨⟨⟨h3, f3⟩, ec, ecs, esc, ea, enb⟩, r3⟩
  exact ⟨Cur0.mk F12.cur (BlkOK.bxi h3) ec ecs esc ea (Or.inr (enb F12.cur.nb)) (FootD.cur0w f3 le_rfl), r3⟩

end

end Fl4ProofsA64.P1
