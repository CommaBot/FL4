/-
P1 (aarch64): **the SC `Bind` / `SchedControl_ConfigureFlags` / `TCB_SetSchedParams` migrations over the run
VCPU's `OWNER_CPU` word as an `Ω \ Sg` word** — the corrected form of QueueScBindVm's [P] `ScBindOwn` and
QueueDecTcb2 / QueueDecTcbB's `TcbPlace7.own` / `TcbPlace8.own`, which are **false as stated** (handoff §30):
after thread `A` runs `ARMVCPURun(vc)` its `RUN_VCPU` is `vc` (vcpu.rs:862), and those premises put
`vc + OWNER_CPU = vc + 8` (vcpu.rs:17) in the user words `U` (`∉ Ω` by `UserOK`) or make it a `UserW` word
(`∉ Ω`), but the VCPU is a `.other 12` heap object, so `vc + 8 ∈ Ω` (and [P] `VcpuW` says so at a decode of
`vc`). `migrate_tcb` writes exactly that word (smp.rs:25–33: `rv = RUN_VCPU(t)`, `rv + OWNER_CPU := cpu + 1`).

The corrected fact is the one [P] `VcPl.rcv` / `TcbPlace8.rcv` already states: a thread's nonzero `RUN_VCPU`
names a VCPU object's words (`VcWords Ω Sg`: aligned, in `Ω`, off `Sg`), so the `OWNER_CPU` write is an
`Ω \ Sg` (`CapW`) write and keeps every invariant (`blk_of_capw`'s argument, here for `BlkOKW` with an
exception set: `blkW_wrO`).

* `OmS Ω Sg` (the `Ω \ Sg` words), `ownA_vc` (a `VcWords` VCPU's `OWNER_CPU` word is one), `blkW_wrO`
  (`blkW_wrU` for an aligned `Ω \ Sg` word, the frame facts on `Sg` instead of `Ω`), `FootDU.kodO`.
* `_fV` twins of QueueScBindVm's chain, `hpo` → `VcWords` of the run VCPU: `migrate_tail_fV`,
  `smp.migrate_tcb.frame_fV` / `.kw_fV` (footprint `OmS` for `U`), `schedcontext.bind_tcb.blkF_fV`,
  `sc_bind_tcb.blkF_fV`, `sc_bind_stall.blk_fV`, `schedcontext.decode.dec_fV`, **`decGap_sc_fV`**.
* **`ScBindOwnV`** (the corrected `ScBindOwn`: at an entry-start decode, a nonzero `RUN_VCPU` names `VcWords`),
  **`ScBindOwnV.of_rcv`**: it follows from any `rcv`-shaped placement (`TcbPlace8.rcv`'s statement, at
  `Fr0` refl), so it is **not a new premise** of the records that carry `rcv`.
* QueueSchedCtl twins: `cfDV`, `schedcontext.configure_flags.blkV`, `schedcontext.decode_sched_control.decV`,
  **`decGap_schedControlV`**.
* QueueDecTcb2 twins: `tcs_tail2V`, `tcb.thread_control_sched.decV` (`hown` → `VcWords`).

Named premises: none new (`ScBindOwnV` is derived from `rcv`). No existing statement changed.
-/
import Fl4ProofsA64.P1.QueueDecVcpuRegA
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {Es : Set U64} {sx : U64}

/-- The words of `Ω` off `Sg` (VCPU words, cap-slot words of the other objects). -/
def OmS (Ω Sg : Set U64) : Set U64 := {b | b ∈ Ω ∧ b ∉ Sg}

/-- A `VcWords` VCPU's `OWNER_CPU` word is an aligned `Ω \ Sg` word. -/
theorem ownA_vc {v : U64} (h : VcWords Ω Sg v) : Aligned (ownA v) ∧ ownA v ∈ Ω ∧ ownA v ∉ Sg :=
  h vcpu.OWNER_CPU (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])

/-- **A write of one aligned `Ω \ Sg` word keeps `BlkOKW`** (`blkW_wrU`'s conclusion, with the frame on the
`Sg` words instead of `Ω`; the proof is `blk_of_capw`'s: the queues and the bound links read no such word, the
SC / reply / notification words are `Sg` words). -/
theorem blkW_wrO {X : Set U64} {d b v : U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (ha : Aligned b) (hbO : b ∈ Ω) (hbS : b ∉ Sg) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s b v) Q R ∧ BoundInv st T Ac (L.wr s b v) ∧
      XInvW st T Cs Ω Sg Rp Scs Nt Z d (L.wr s b v) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s b v) ∧
      SgOK st Ω Sg (L.wr s b v) ∧ TmFr st T Cs Nt s (L.wr s b v) ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s b v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Sg, L.mem (L.wr s b v) a = L.mem s a) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
        L.mem (L.wr s b v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      L.actionW (L.wr s b v) = L.actionW s := by
  have hw : WritesIn st s (L.wr s b v) (· = b) := writesIn_wr ha
  have hBw : ∀ x, x = b → L.Free s Ω Cs x ∨ TLow T x := fun x e => Or.inl (Or.inl (e ▸ hbO))
  have q : SchedQueuesInvX st T Cs Ω H X (L.wr s b v) Q R := inv_of_capw h hw hBw
  have hB' : BoundInv st T Ac (L.wr s b v) := BoundInv.capw h hB hw hBw
  have hT := h.tcbs
  have ho := h.omega b hbO
  have F0 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s b v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK h8 => hw.mem_eq (field_aligned (hT y hy) hK h8) fun e =>
      out_ne_field ho hy (hT y hy) hK (congrArg UScalar.val e)
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s b v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K _ hK h8 => F0 y hy K hK h8
  have f3 : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s b v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o) :=
    fun c hc o ho' h8 => hw.mem_eq (nodeAt_aligned (h.nodes c hc) ho' h8) fun e =>
      out_ne_node ho hc (h.nodes c hc) ho' (congrArg UScalar.val e)
  have sig : ∀ x ∈ Sg, L.mem (L.wr s b v) x = L.mem s x := fun x hx =>
    hw.mem_eq (h.omega _ (hSg.sub x hx)).1 fun e => hbS (e ▸ hx)
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho' h8 => by rw [hw.2.1, nodeAt_of_ksb hw.1]; exact f3 _ h.cur o ho' h8
  have ea : L.actionW (L.wr s b v) = L.actionW s := nd _ (by rw [act_val]; omega) (by rw [act_val])
  have ei : L.idleW (L.wr s b v) = L.idleW s := nd _ (by rw [idle8]; omega) (by rw [idle8])
  have ecs : L.cscW (L.wr s b v) = L.cscW s := nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have scf : ∀ y ∈ T, L.mem (L.wr s b v) (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have stf : ∀ y ∈ T, L.mem (L.wr s b v) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have rpf : ∀ y ∈ T, L.mem (L.wr s b v) (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp)
  have tm : TmFr st T Cs Nt s (L.wr s b v) :=
    TmFr.mk0 ⟨hw.1, fun y hy K k1 k2 k3 => F y hy K (by omega) (by omega) k3,
      fun c hc o ho' => f3 c hc o (by omega) (by omega), fun n hn => sig _ (hX.1.1.ntB n hn).2⟩
  have hX0 := hX.1
  have x0 : XInv0 st T Cs Ω Sg Rp Scs Nt Z (L.wr s b v) :=
    hX0.keep (fun r hr => ⟨sig _ (hX0.1.tcbW hr), sig _ (hX0.1.prevW hr), sig _ (hX0.1.nextW hr)⟩)
      (fun c hc => ⟨sig _ (hX0.1.fixW c hc).1, sig _ (hX0.1.fixW c hc).2⟩) scf rpf stf (by rw [ecs]; exact hX0.2.2.cur)
      (fun c hc => sig _ (hX0.1.repW c hc))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun n hn => sig _ (hX0.1.ntW n hn))
      ⟨hX0.2.2.tm.tmfr tm, hX0.2.2.ntb.tmfr tm, hX0.2.2.rb.tmfr tm, tm.2.2.2.1⟩
      (fun c hc => sig _ (hX0.1.snW c hc))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun c hc => sig _ (hX0.1.syW c hc))
      (fun c hc => sig _ (hX0.1.mxW c hc)) ei
  have xw : XInvW st T Cs Ω Sg Rp Scs Nt Z d (L.wr s b v) :=
    ⟨x0, hX.2.1.keep hX0.2.2.yt.1 (fun c hc => sig _ (hX0.1.fixW c hc).1) scf,
      hX.2.2.keep (fun t ht _ h0 => (hX0.2.2.bound t ht h0).1) (fun t ht _ => scf t ht)
        (fun c hc => sig _ (hX0.1.fixW c hc).2)
        (fun t ht _ => by rw [affA_eq]; exact F t ht _ (by simp) (by simp) (by simp))⟩
  have hS' : SCsOK st T Ω Sg Scs Z Ac (L.wr s b v) := by
    refine ⟨hS.sub, fun x hx => by rw [hw.1]; exact hS.ks x hx, fun o h1 h2 => by rw [hw.1]; exact hS.ksΩ o h1 h2,
      fun t ht hb' hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax (L.wr s b v) c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h0 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h0), hS.spSg,
      fun c hc h0 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h0), hS.repSg,
      fun c hc => by rw [hw.1]; exact hS.scKs c hc⟩
    rw [scf t ht] at hb' hne ⊢; rw [ecs] at hne ⊢; exact hS.disj t ht hb' hne
  exact ⟨q, hB', xw, hS',
    ⟨hSg.sub, fun x hx => by rw [hw.1]; exact hSg.ks x hx, fun o h1 h2 => by rw [hw.1]; exact hSg.ksΩ o h1 h2⟩,
    tm, F, sig, f3, ea⟩

/-- An `OmS`-widened `FootDU` lies in `KOD` (the `Ω \ Sg` words are `KO` words). -/
theorem FootDU.kodO {s s' : S} {Es : Set U64} (f : FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s') (hE : Es ⊆ EH H) :
    WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) :=
  WritesIn.mono (FootDU.kodu (Ω := Ω) (H := H) f hE) fun _ hb =>
    hb.elim Or.inl fun h => Or.inl (Or.inl (Or.inr h.1))

/-- **The corrected `ScBindOwn`** (module docstring): at an entry-start decode (`EntAt`, `DecPre`), a thread's
nonzero `RUN_VCPU` names a VCPU object's words (`VcWords Ω Sg`). -/
def ScBindOwnV (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop :=
  ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra →
    ∀ t ∈ T, L.mem s (runVcpuA t) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA t))

/-- `ScBindOwnV` from an `rcv`-shaped placement (`TcbPlace8.rcv`'s statement) at the decode start itself
(`Fr0` refl). -/
theorem ScBindOwnV.of_rcv
    (R : ∀ (Ac : Set U64) (s0 s : S) (p : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
      BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
      VcWords Ω Sg (L.mem s (runVcpuA p))) :
    ScBindOwnV st T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  fun Ac s _ _ hE D t ht hne => R Ac s s t hE (WritesIn.refl _ _) D.bxi ht hne

/-- **`migrate_tail` for a thread that may run a VCPU** (no `hrv`): when `RUN_VCPU ≠ 0`, the run VCPU's
`OWNER_CPU` word is an `Ω \ Sg` word (`hpo`: the run VCPU's `VcWords`), and its write keeps `BlkOKW` (`blkW_wrO`). -/
theorem migrate_tail_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s8 : S) (a : A)
    (sc dst cpu : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h8 : SchedQueuesInvX st T Cs Ω H X s8 Q R) (hB8 : BoundInv st T Ac s8) (hX8 : XInvW st T Cs Ω Sg Rp Scs Nt Z dst s8)
    (hS8 : SCsOK st T Ω Sg Scs Z Ac s8) (hSg8 : SgOK st Ω Sg s8) (hto : dst ∈ T)
    (htq : (L.mem s8 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s8 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hc' : cpu ∈ Cs) (hsc : sc ∈ Scs)
    (hcore : L.mem s8 (scA dst) ≠ 0#u64 → L.mem s8 (scCoreA (L.mem s8 (scA dst))) = cpu)
    (hpo : L.mem s8 (runVcpuA dst) ≠ 0#u64 → VcWords Ω Sg (L.mem s8 (runVcpuA dst))) :
    smp.migrate_tcb st ar s8 a dst cpu ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧
        (∀ y ∈ T, L.mem s' (stA y) = L.mem s8 (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s8 (replyA y)) ∧
        TmFr st T Cs Nt s8 s' ∧
        (L.mem s' (scA dst) = L.mem s8 (scA dst) ∧ L.mem s' (scTcbA sc) = L.mem s8 (scTcbA sc) ∧
          L.actionW s' = L.actionW s8) ⦄ := by
  have hT := h8.tcbs
  have hO := hX8.1.1
  have hm : scTcbA sc ∈ Ω := hSg8.sub _ (hO.fixW sc hsc).1
  have h0 : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac X dst s8 := ⟨⟨Q, R, h8⟩, hB8, hX8, hS8, hSg8⟩
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, eaf⟩
  split
  · refine WP.spec_bind (objects.debug_remove.w s8 dst h0 hto) fun s1 ⟨h1, m1, w1⟩ => ?_
    obtain ⟨st1, rp1, sc1, t1, a1, iq1⟩ := dbgW_keeps hT h8.nodes h8.cur (h8.omega _ hm) hto w1
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    have hcore1 : L.mem s1 (scA dst) ≠ 0#u64 → L.mem s1 (scCoreA (L.mem s1 (scA dst))) = cpu := fun h0' => by
      rw [sc1] at h0' ⊢
      have hco := h8.omega _ (hSg8.sub _ (hO.fixW _ (hX8.1.2.2.bound dst hto h0').1).2)
      rw [w1.mem_eq hco.1 (notDbgW_out hT h8.nodes hco)]; exact hcore h0'
    refine WP.spec_bind (hA.fpu_flush _ _) fun a2 _ => ?_
    refine WP.spec_bind (hA.fpu_release _ _) fun a3 _ => ?_
    have rv1 : L.mem s1 (runVcpuA dst) = L.mem s8 (runVcpuA dst) :=
      w1.mem_eq (field_aligned (K := 3672#u64) (hT dst hto) (by simp) (by simp))
        (notDbgW_field (K := 3672#u64) hT h8.nodes hto (by simp) (by simp))
    -- the rest, from a state with `migrate_tcb`'s facts after its VCPU steps
    have tail : ∀ (s1' : S) (a4 : A) (Q1 : U64 → U64 → List U64) (R1 : U64 → List U64),
        SchedQueuesInvX st T Cs Ω H X s1' Q1 R1 → BoundInv st T Ac s1' → XInvW st T Cs Ω Sg Rp Scs Nt Z dst s1' →
        SCsOK st T Ω Sg Scs Z Ac s1' → SgOK st Ω Sg s1' →
        (∀ y ∈ T, L.mem s1' (stA y) = L.mem s8 (stA y)) → (∀ y ∈ T, L.mem s1' (replyA y) = L.mem s8 (replyA y)) →
        TmFr st T Cs Nt s8 s1' → L.mem s1' (scA dst) = L.mem s8 (scA dst) →
        L.mem s1' (scTcbA sc) = L.mem s8 (scTcbA sc) → L.actionW s1' = L.actionW s8 →
        L.mem s1' (inqA dst) = L.mem s8 (inqA dst) →
        (L.mem s1' (scA dst) ≠ 0#u64 → L.mem s1' (scCoreA (L.mem s1' (scA dst))) = cpu) →
        (do
          let s3 ← obj.Tcb.set_affinity st dst s1' cpu
          let s4 ← objects.debug_append st s3 dst
          ok (s4, a4)) ⦃ s' _ => BlkOKX st T Cs Ω H Sg Rp Scs Nt Z Ac X s' ∧
            (∀ y ∈ T, L.mem s' (stA y) = L.mem s8 (stA y)) ∧ (∀ y ∈ T, L.mem s' (replyA y) = L.mem s8 (replyA y)) ∧
            TmFr st T Cs Nt s8 s' ∧
            (L.mem s' (scA dst) = L.mem s8 (scA dst) ∧ L.mem s' (scTcbA sc) = L.mem s8 (scTcbA sc) ∧
              L.actionW s' = L.actionW s8) ⦄ := by
      intro s1' a4 Q1 R1 q1 hB1 hX1 hS1 hSg1 st1 rp1 m1 sc1 t1 a1 iq1 hcore1
      refine WP.spec_bind (obj.Tcb.set_affinity.wr s1' dst cpu) fun s2 e2 => ?_
      subst e2
      obtain ⟨g2, st2, rp2, m2, sc2, t2, a2'⟩ := migrate_aff (sc := sc) q1 hB1 hX1 hS1 hSg1 hto
        (by rw [iq1]; exact htq) (by rw [iq1]; exact htr) hc' hsc hcore1
      have q2 := g2.1.choose_spec.choose_spec
      refine WP.spec_bind (objects.debug_append.x _ dst g2 hto) fun s3 ⟨h3, m3, w3⟩ => ?_
      obtain ⟨st3, rp3, sc3, t3, a3', -⟩ := dbgW_keeps hT q2.nodes q2.cur (q2.omega _ hm) hto w3
      exact (WP.spec_ok _).2 ⟨h3, fun y hy => (st3 y hy).trans ((st2 y hy).trans (st1 y hy)),
        fun y hy => (rp3 y hy).trans ((rp2 y hy).trans (rp1 y hy)), m1.trans (m2.trans m3),
        sc3.trans (sc2.trans sc1), t3.trans (t2.trans t1), a3'.trans (a2'.trans a1)⟩
    refine migrate_vcpu_any hA s1 a3 dst cpu _ (fun _ a4 => ?_) (fun hnz a4 => ?_)
    · try dsimp only
      exact tail s1 a4 Q1 R1 q1 hB1 hX1 hS1 hSg1 st1 rp1 m1 sc1 t1 a1 iq1 hcore1
    · try dsimp only
      have hV1 : VcWords Ω Sg (L.mem s1 (runVcpuA dst)) := by
        rw [rv1]; exact hpo (by rw [← rv1]; exact hnz)
      obtain ⟨oa, oO, oS⟩ := ownA_vc hV1
      obtain ⟨q1', hB1', hX1', hS1', hSg1', tm1, F1, O1, -, ea1⟩ := blkW_wrO (v := core.num.U64.wrapping_add cpu 1#u64)
        q1 hB1 hX1 hS1 hSg1 oa oO oS
      have scf : L.mem (L.wr s1 (ownA (L.mem s1 (runVcpuA dst))) (core.num.U64.wrapping_add cpu 1#u64)) (scA dst) =
          L.mem s1 (scA dst) := by rw [scA_eq]; exact F1 dst hto _ (by simp) (by simp) (by simp)
      refine tail _ a4 Q1 R1 q1' hB1' hX1' hS1' hSg1'
        (fun y hy => by rw [stA_eq, F1 y hy _ (by simp) (by simp) (by simp), ← stA_eq]; exact st1 y hy)
        (fun y hy => (F1 y hy _ (by simp) (by simp) (by simp)).trans (rp1 y hy)) (m1.trans tm1)
        (scf.trans sc1) ((O1 _ (hO.fixW sc hsc).1).trans t1) (ea1.trans a1)
        (by rw [inqA_eq, F1 dst hto _ (by simp) (by simp) (by simp), ← inqA_eq]; exact iq1) fun h0' => ?_
      rw [scf] at h0' ⊢
      rw [O1 _ (hX1.1.1.fixW _ (hX1.1.2.2.bound dst hto h0').1).2]
      exact hcore1 h0'
  · rename_i hne
    have e : af = cpu := UScalar.eq_of_val_eq (by simpa using hne)
    have hX : XInv st T Cs Ω Sg Rp Scs Nt Z s8 :=
      hX8.1.x hX8.2.1 (hX8.2.2.full fun _ h0' => by rw [hcore h0', ← eaf, e])
    try simp only [Aeneas.Std.bind_ok]
    exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h8⟩, hB8, hX, hS8, hSg8⟩, fun _ _ => rfl, fun _ _ => rfl, TmFr.refl (L := L) _,
      rfl, rfl, rfl⟩

/-- **`migrate_tcb` as a frame, for a thread that may run a VCPU**: the thread's affinity, the debug-list
words and, when `RUN_VCPU ≠ 0`, its run VCPU's `OWNER_CPU` word (an `Ω \ Sg` word, `hpo`). -/
theorem smp.migrate_tcb.frame_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) (hΩ : ∀ x ∈ Ω, OutsideObjs st T Cs s x)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA t))) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => WritesIn st s s' (fun b => b = affA t ∨ DbgW st T Cs s b ∨ b ∈ OmS Ω Sg) ∧
      DbgTz st T Cs s' ∧ (L.mem s (affA t) = cpu → s' = s) ⦄ := by
  have hta := hT t ht
  have haa : Aligned (affA t) := field_aligned (K := 3520#u64) hta (by simp) (by simp)
  unfold smp.migrate_tcb
  step with obj.Tcb.affinity.spec as ⟨af, haf⟩
  split
  · rename_i hne
    have hne' : L.mem s (affA t) ≠ cpu := fun e => by
      subst haf; rw [e] at hne; simp at hne
    refine WP.spec_bind (objects.debug_remove.frame s t hT hN hD hc ht) fun s1 ⟨w1, D1⟩ => ?_
    refine WP.spec_bind (hA.fpu_flush _ _) fun a2 _ => ?_
    refine WP.spec_bind (hA.fpu_release _ _) fun a3 _ => ?_
    have rv1 : L.mem s1 (runVcpuA t) = L.mem s (runVcpuA t) :=
      w1.mem_eq (field_aligned (K := 3672#u64) hta (by simp) (by simp))
        (notDbgW_field (K := 3672#u64) hT hN ht (by simp) (by simp))
    have tail : ∀ (s1' : S) (a4 : A), WritesIn st s s1' (fun b => DbgW st T Cs s b ∨ b ∈ OmS Ω Sg) →
        DbgTz st T Cs s1' →
        (do
          let s3 ← obj.Tcb.set_affinity st t s1' cpu
          let s4 ← objects.debug_append st s3 t
          ok (s4, a4)) ⦃ s' _ => WritesIn st s s' (fun b => b = affA t ∨ DbgW st T Cs s b ∨ b ∈ OmS Ω Sg) ∧
            DbgTz st T Cs s' ∧ (L.mem s (affA t) = cpu → s' = s) ⦄ := by
      intro s1 a4 w1 D1
      refine WP.spec_bind (obj.Tcb.set_affinity.wr s1 t cpu) fun s2 e2 => ?_
      subst e2
      have hN2 : ∀ c ∈ Cs, NodePlaced st T (L.wr s1 (affA t) cpu) c := fun c hc' => ((hN c hc').ksb w1.1).wr
      have D2 : DbgTz st T Cs (L.wr s1 (affA t) cpu) := by
        refine ⟨fun y hy => ?_, fun y hy => ?_, fun c hc' => ?_⟩
        · rw [show dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, L.mem_wr_ne haa (field_aligned (K := 3576#u64) (hT y hy) (by simp) (by simp))
            (fun e => field_ne (K1 := 3520#u64) (K2 := 3576#u64) hta (hT y hy) (by simp) (by simp)
              (fun _ => by simp) (UScalar.eq_of_val_eq e))]
          exact D1.dn y hy
        · rw [show dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, L.mem_wr_ne haa (field_aligned (K := 3584#u64) (hT y hy) (by simp) (by simp))
            (fun e => field_ne (K1 := 3520#u64) (K2 := 3584#u64) hta (hT y hy) (by simp) (by simp)
              (fun _ => by simp) (UScalar.eq_of_val_eq e))]
          exact D1.dp y hy
        · have hN1 := (hN c hc').ksb w1.1
          rw [nodeAt_wr, L.mem_wr_ne haa (nodeAt_aligned hN1 (by simp [debug_val]) (by simp [debug_val]))
            (fun e => node_ne_field (K := 3520#u64) hN1 (by simp [debug_val]) ht hta (by simp)
              (UScalar.eq_of_val_eq e).symm)]
          exact D1.dh c hc'
      have w2 : WritesIn st s (L.wr s1 (affA t) cpu) (fun b => b = affA t ∨ DbgW st T Cs s b ∨ b ∈ OmS Ω Sg) :=
        WritesIn.mono (WritesIn.trans w1 (writesIn_wr haa)) fun b hb => hb.elim Or.inr Or.inl
      have hc2 : L.mem (L.wr s1 (affA t) cpu) (affA t) ∈ Cs := by rw [L.mem_wr_same haa]; exact hcpu
      refine WP.spec_bind (objects.debug_append.frame _ t hT hN2 D2 hc2 ht) fun s3 ⟨w3, D3⟩ => ?_
      refine (WP.spec_ok _).2 ⟨WritesIn.mono (WritesIn.trans w2 w3) fun b hb => ?_, D3, fun e => absurd e hne'⟩
      rcases hb with hb | hb | ⟨c, hc', e⟩
      · exact hb
      · exact Or.inr (Or.inl (Or.inl hb))
      · exact Or.inr (Or.inl (Or.inr ⟨c, hc', by rw [e, nodeAt_wr, nodeAt_of_ksb w1.1]⟩))
    refine migrate_vcpu_any hA s1 a3 t cpu _ (fun _ a4 => ?_) (fun hnz a4 => ?_)
    · try dsimp only
      exact tail s1 a4 (w1.mono fun _ hb => Or.inl hb) D1
    · try dsimp only
      have hV1 : VcWords Ω Sg (L.mem s1 (runVcpuA t)) := by rw [rv1]; exact hpo (by rw [← rv1]; exact hnz)
      have hu : ownA (L.mem s1 (runVcpuA t)) ∈ OmS Ω Sg := ⟨(ownA_vc hV1).2.1, (ownA_vc hV1).2.2⟩
      have ho := (hΩ _ hu.1).ksb w1.1
      refine tail _ a4 ((w1.trans (writesIn_wr ho.1)).mono fun b hb => ?_)
        (DbgTz.wr_out hT (fun c hc' => (hN c hc').ksb w1.1) ho.1 (notDbgW_out hT (fun c hc' => (hN c hc').ksb w1.1) ho) D1)
      rcases hb with hb | rfl
      · exact Or.inl hb
      · exact Or.inr hu
  · try simp only [Aeneas.Std.bind_ok]
    exact (WP.spec_ok _).2 ⟨WritesIn.refl _ _, hD, fun _ => rfl⟩

/-- `migrate_tcb.kw` for a thread that may run a VCPU: `FootDU` with the `Ω \ Sg` words. -/
theorem smp.migrate_tcb.kw_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) (hΩ : ∀ x ∈ Ω, OutsideObjs st T Cs s x)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA t))) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s' ⦄ :=
  WP.spec_mono (smp.migrate_tcb.frame_fV hA s a t cpu hT hN hD hc hcpu ht hΩ hpo) fun _ hr => by
    obtain ⟨w, -⟩ := hr
    exact w.mono fun b hb => by
      rcases hb with e | hb | hb
      · exact Or.inl (Or.inl (by rw [e, affA_eq]; exact kw_field ht (by simp) (by simp) (by simp)))
      · exact Or.inl (Or.inr hb)
      · exact Or.inr hb

/-- **`bind_tcb` with its footprint, for a thread that may run a VCPU** (`bind_tcb.blkF` without `hrv`): the
footprint also holds the run VCPU's `OWNER_CPU` word, an `Ω \ Sg` word (`hpo`, `OmS`). -/
theorem schedcontext.bind_tcb.blkF_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA t))) :
    schedcontext.bind_tcb st ar s a sc t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have hta := hT t ht
  have hO := hX.1
  have hm : scTcbA sc ∈ Ω := hSg.sub _ (hO.fixW sc hsc).1
  have ho := h0.omega _ hm
  have hal : Aligned (scTcbA sc) := by
    obtain ⟨hP, hz⟩ := hO.sc sc hsc
    have := (sc_lo hP hz).1
    unfold Aligned; rw [scTcbA_val hP hz]; omega
  have htq : (L.mem s (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by
    by_contra hq; exact hB.q t ht hq ht0
  have htr : (L.mem s (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by
    by_contra hq; exact hB.r t ht hq ht0
  have hna : L.actionW s ≠ t := fun e => hB.act (e ▸ ht) (by rw [e]; exact ht0)
  have hnb : ∀ y ∈ T, L.mem s (scA y) ≠ sc := fun y hy e => by
    obtain ⟨-, h2, -⟩ := hX.2.2.bound y hy (by rw [e]; exact hsc0)
    rw [e, hc0] at h2; exact (hT y hy).ne0 (by rw [← h2]; rfl)
  have hdisj : sc ≠ L.cscW s → ∀ b, InSC sc (Z sc) b → Outside b (L.cscW s) (Z (L.cscW s)) := by
    intro hne b hb
    have := hO.scDisj sc hsc _ hX.2.2.cur hne
    unfold Outside; unfold InSC at hb; omega
  have hcore := hX.2.2.core sc hsc
  have hsA : Sch st s t → sc ∈ Ac := by
    rintro (e | e | e | e | ⟨e1, e2⟩ | e)
    · exact absurd htq e
    · exact absurd htr e
    · exact absurd e hna
    · exact absurd (by rw [e]; exact ht0) hB.idle
    · exact absurd (by rw [e2]; exact ht0) (hB.resume e1)
    · exact hbA e
  -- the two writes
  unfold schedcontext.bind_tcb
  step with obj.Tcb.set_sc.wr as ⟨s1, e1⟩
  step with obj.Sc.set_tcb.wr as ⟨s2, e2⟩
  subst e1 e2
  have fw2 : Foot st T Cs Sg Scs Z Es s (L.wr (L.wr s (scA t) sc) (scTcbA sc) t) := by
    have f1 : Foot st T Cs Sg Scs Z Es s (L.wr s (scA t) sc) := by
      rw [scA_eq]; exact foot_field hT ht (by simp) (by simp) (by simp) (by simp)
    exact f1.trans (foot_wr hal (kw_sg (hO.fixW sc hsc).1))
  obtain ⟨p8, pB, pX, pS, pSg, -, pfl, pcore, psc, ptc, pact⟩ :=
    donate_pair h0 hB hX.x0 hX.2.2.tsc.x hX.2.2.aff ht0 hS hSg ht hsc hsc0 hnb hcore hdisj hsA
      (fun e => hB.idle (by rw [e]; exact ht0))
  have hsw := bind_swap (L := L) (s := s) (scA_aligned hta) ho.1
    (fun e => out_ne_field (K := 3464#u64) ho ht hta (by simp) e)
  obtain ⟨h2, hB2, hX2, hS2, hSg2⟩ := agree_all p8 pB pX pS pSg (by simp) (by simp) hsw
  set s2 := L.wr (L.wr s (scA t) sc) (scTcbA sc) t with hs2
  have fl2 : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → (y = t → K.val ≠ 3464) →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K hK hK8 hne => (hsw _ (field_aligned (hT y hy) hK hK8)).trans (pfl y hy K hK hK8 hne)
  have sc2 : L.mem s2 (scA t) = sc := (hsw _ (scA_aligned hta)).trans psc
  have core2 : L.mem s2 (scCoreA sc) = L.mem s (scCoreA sc) :=
    (hsw _ (h0.omega _ ((objs_omega hO hSg.sub).2 sc hsc).2.1).1).trans pcore
  have ea2 : L.actionW s2 = L.actionW s := by
    have e : L.actionW s2 = L.actionW (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) := by
      unfold LawfulStore.actionW
      rw [show L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION =
        L.nodeAt (L.wr (L.wr s (scTcbA sc) t) (scA t) sc) (L.cpu (L.wr (L.wr s (scTcbA sc) t) (scA t) sc))
          layout.node.SCHED_ACTION by simp [hs2, nodeAt_wr]]
      exact hsw _ (nodeAt_aligned (p8.nodes _ p8.cur) (by rw [act_val]; omega) (by rw [act_val]))
    rw [e, pact]
  have iq2 : L.mem s2 (inqA t) = L.mem s (inqA t) := by
    rw [inqA_eq]; exact fl2 t ht _ (by simp) (by simp) (fun _ => by simp)
  -- migration
  have rv2 : L.mem s2 (runVcpuA t) = L.mem s (runVcpuA t) := fl2 t ht 3672#u64 (by simp) (by simp) (fun _ => by simp)
  have k2s : L.ksb s2 = L.ksb s := (L.ksb_wr _ _ _).trans (L.ksb_wr _ _ _)
  have hpo2 : L.mem s2 (runVcpuA t) ≠ 0#u64 → VcWords Ω Sg (L.mem s2 (runVcpuA t)) := fun hnz => by
    rw [rv2]; exact hpo (by rw [← rv2]; exact hnz)
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core2]; exact hcore
  refine WP.spec_bind (WP.spec_and (migrate_tail_fV hA s2 a sc t cpu Q R h2 hB2 hX2 hS2 hSg2 ht (by rw [iq2]; exact htq)
    (by rw [iq2]; exact htr) hc' hsc (fun _ => by rw [sc2, ecpu]) hpo2) (smp.migrate_tcb.kw_fV (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) (Cs := Cs)
      hA s2 a t cpu h2.tcbs h2.nodes ⟨hX2.1.2.2.tm.dn, hX2.1.2.2.tm.dp, hX2.1.2.2.tm.dh⟩ (h2.aff t ht) hc' ht h2.omega hpo2)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, -, sc3, -, ea3⟩, fw3⟩
  try simp only [WP.uncurry'_pair]
  rw [sc2] at sc3
  have fw3' : FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s3 := fw2.d.u.trans fw3
  -- the sporadic unblock check
  step with sporadic.sc_sporadic.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
      L.actionW s4 = L.actionW s ∧ FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s4) ?_ ?_
  · have ok3 : (ok s3 : Result S) ⦃ s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
        L.actionW s4 = L.actionW s ∧ FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s4 ⦄ :=
      (WP.spec_ok _).2 ⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, sc3, by rw [ea3, ea2], fw3'⟩
    split
    · step with sporadic.sc_active.val as ⟨b1, eb1⟩
      split
      · rename_i hb1
        step with sched.cur_sc.spec as ⟨c4, _⟩
        step with sc_ne.spec as ⟨b2⟩
        split
        · have hAc : sc ∈ Ac := (hS3.act sc hsc).2 (eb1 hb1)
          have hW : RefillsWF st s3 sc (Z sc) := hS3.wf hsc hAc
          have hSCin : SCin st s3 Ω sc (Z sc) := ⟨hW, hX3.1.scW sc hsc⟩
          have hN' := h3.nodes _ h3.cur
          have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
          have aR : Aligned (L.nodeA s3 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
          have oR : Outside (L.nodeA s3 layout.node.REPROGRAM) sc (Z sc) :=
            hSCin.node_out h3.omega h3.cur hN' (by rw [rp]; omega) (by rw [rp])
          refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 t sc h3 hB3 hX3 hS3 hSg3 ht sc3.symm hsc0
            hAc) (sporadic.unblock_check.fr hW ⟨aR, oR⟩)) fun s4 hh => ?_
          obtain ⟨⟨h4, hB4, hX4, hS4, hSg4, ea4, -, -, f4, -⟩, w4⟩ := hh
          have fw4 : Foot st T Cs Sg Scs Z Es s3 s4 := Foot.of w4 fun b hb => by
            rcases hb with hb | rfl
            · exact hb.kw hsc
            · exact kw_node h3.cur (by rw [rp]; omega) (by rw [rp]; omega)
          exact ⟨⟨⟨Q3, R3, h4⟩, hB4, hX4, hS4, hSg4⟩, by rw [scA_eq, f4 t ht _ (by simp) (by simp), ← scA_eq]; exact sc3,
            by rw [ea4, ea3, ea2], fw3'.trans fw4.d.u⟩
        · exact ok3
      · exact ok3
    · exact ok3
  rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, sc4, ea4, fw4⟩
  -- resume
  have tc4 : L.mem s4 (scTcbA sc) = t := by
    have := (hX4.2.2.bound t ht (by rw [sc4]; exact hsc0)).2.1; rwa [sc4] at this
  have hres : sc ≠ 0#u64 → L.mem s4 (scTcbA sc) ≠ 0#u64 →
      L.mem s4 (scTcbA sc) ∈ T ∧ OutsideObjs st T Cs s4 (scCoreA sc) ∧ L.mem s4 (scCoreA sc) ∈ Cs ∧
        L.actionW s4 ≠ L.mem s4 (scTcbA sc) := fun _ _ => by
    rw [tc4]
    exact ⟨ht, h4.omega _ ((objs_omega hX4.1 hSg4.sub).2 sc hsc).2.1, hX4.2.2.core sc hsc,
      by rw [ea4]; exact hna⟩
  refine WP.spec_bind (WP.spec_and (schedcontext.resume.all hA s4 a1 sc Q4 R4 h4 hB4 hX4 hSg4 hS4 hres)
    (schedcontext.resume.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) hA s4 a1 sc Q4 R4 h4 hres)) ?_
  rintro ⟨s5, a2⟩ ⟨⟨Q5, R5, h5, hB5, hX5, hSg5, f5⟩, fw5⟩
  have hS5 := hS4.fr f5
  have fw5' : FootDU st T Cs Sg Scs Z Es (OmS Ω Sg) s s5 := fw4.trans fw5.d.u
  try simp only [WP.uncurry'_pair]
  -- enqueue if schedulable
  step with sched.is_schedulable.spec' as ⟨b3, eb3⟩
  split
  · rename_i hb3
    obtain ⟨hrun, hbd, hrl, hrm⟩ := eb3 hb3
    have hA5 : L.mem s5 (scA t) ∈ Ac := (hS5.act _ (hX5.2.2.bound t ht hbd).1).2 hrm
    refine WP.spec_bind (WP.spec_and (sched.enqueue.sch s5 t Q5 R5 h5 hB5 hSg5 ht (fun _ => hrl) (fun _ => hrun)
      (fun _ => hbd) (fun _ => hA5)) (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s5 t h5 ht)) ?_
    rintro s6 ⟨⟨⟨⟨Q6, R6, h6⟩, hB6, f6⟩, -, -, -⟩, fw6⟩
    refine WP.spec_bind (WP.spec_and (sched.reschedule_required.sch s6 Q6 R6 h6 hB6 (hSg5.fr f6))
      (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s6 h6)) ?_
    rintro s7 ⟨⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, -, -, -⟩, fw7⟩
    exact (WP.spec_ok _).2 ⟨⟨⟨Q7, R7, h7⟩, hB7, (hX5.fr f6).fr f7, (hS5.fr f6).fr f7, (hSg5.fr f6).fr f7⟩,
      fw5'.trans (fw6.trans fw7).d.u⟩
  · exact (WP.spec_ok _).2 ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, fw5'⟩

/-- **SchedContext `Bind` (thread)**, `sc_bind_tcb.blkF` without `hrv` (`bind_tcb.blkF_f`). -/
theorem sc_bind_tcb.blkF_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (ct sc t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA t))) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.bind_tcb st ar s2 a sc t
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootDU st T Cs Sg Scs Z ∅ (OmS Ω Sg) s s' ⦄ := by
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s ct h hct (runnable_ok hr).1
    (runnable_ok hr).2) ?_
  rintro s2 ⟨h2, f2, e2, k2⟩
  have hbA2 : BlockedR (L.mem s2 (stA t)) → sc ∈ Ac := by
    by_cases e : t = ct
    · subst e; rw [e2]
      rintro (hb | hb)
      · exact absurd hb not_blocked_restart
      · exact absurd hb restart_ne.1
    · rw [k2.stf ht e]; exact hbA
  have rv2 : L.mem s2 (runVcpuA t) = L.mem s (runVcpuA t) :=
    k2.fld t ht 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  refine WP.spec_bind (schedcontext.bind_tcb.blkF_fV (Es := ∅) hA s2 a sc t h2 ht hsc hsc0 (by rw [k2.scf ht]; exact ht0)
    (by rw [(k2.fix sc hsc).1]; exact hc0) hbA2
    (fun hnz => by rw [rv2]; exact hpo (by rw [← rv2]; exact hnz))) ?_
  rintro ⟨s3, a2⟩ ⟨h3, f3⟩
  try simp only [WP.uncurry'_pair]
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h3, f2.d.u.trans f3⟩


/-- `sc_bind_stall.blk` without `hrv`: the target may run a VCPU, whose `OWNER_CPU` word is an `Ω \ Sg` word
(`hpo`, `VcWords`); the footprint stays `KOD ∨ U`. -/
theorem sc_bind_stall.blk_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a1 : A)
    (ct sc ptr : U64) (h1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hct : ct ∈ T)
    (run1 : Runnable (L.mem s1 (stA ct))) (hpT : ptr ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (z2 : L.mem s1 (scA ptr) = 0#u64) (z1 : L.mem s1 (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s1 (stA ptr)) → sc ∈ Ac)
    (hpo : L.mem s1 (runVcpuA ptr) ≠ 0#u64 → VcWords Ω Sg (L.mem s1 (runVcpuA ptr)))
    (hscO : scTcbA sc ∈ Ω) :
    (do
      let (s2, a2) ← smp.remote_tcb_stall st ar s1 a1 ptr
      let s3 ← sched.set_thread_state st s2 ct sched.TS_RESTART
      let (s4, a3) ← schedcontext.bind_tcb st ar s3 a2 sc ptr
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s4, a3)) ⦃ r s' _ =>
        r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ WritesIn st s1 s' (fun b => KOD st T Cs Ω H Sg Scs Z s1 b ∨ b ∈ U) ⦄ := by
  refine WP.spec_bind (smp.remote_tcb_stall.bxi hA s1 a1 ptr h1) ?_
  rintro ⟨s2, a2⟩ ⟨h2, -, -, -, -, f2, o2, w2⟩
  try simp only [WP.uncurry'_pair]
  have rv2 : L.mem s2 (runVcpuA ptr) = L.mem s1 (runVcpuA ptr) := by
    rw [runVcpuA]; exact f2 _ hpT _ (by simp) (by simp)
  refine WP.spec_mono (sc_bind_tcb.blkF_fV hA s2 a2 ct sc ptr h2.blk hct
    (by rw [stA_eq, f2 _ hct _ (by simp) (by simp), ← stA_eq]; exact run1) hpT hsc hsc0
    (by rw [scA_eq, f2 _ hpT _ (by simp) (by simp), ← scA_eq]; exact z2)
    (by rw [o2 _ hscO]; exact z1)
    (fun hb => hbA (by rw [stA_eq, ← f2 _ hpT _ (by simp) (by simp), ← stA_eq]; exact hb))
    (fun hnz => by rw [rv2] at hnz ⊢; exact hpo hnz)) fun r hr => ?_
  obtain ⟨r', s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨hr.1, hr.2.1, KODU.trans (w2.mono fun _ hb => NodeW.ko h1.1.choose_spec.choose_spec.cur hb)
    (FootDU.kodO hr.2.2 (Set.empty_subset _))⟩

set_option maxHeartbeats 800000 in
/-- **`schedcontext.decode`** keeps the invariants, `schedcontext.decode.dec` with the named premise
`BO : ScBindOwnV` (the corrected `ScBindOwn`, derived from `rcv`); the footprint also holds the user words. -/
theorem schedcontext.decode.dec_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (BO : ScBindOwnV st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (s : S) (a : A) (lbl sc : U64) (call : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize) (b : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.SchedContext sc b) extra) (he : EntAt st P3Ok s) :
    schedcontext.decode st ar s a lbl sc call extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧
      WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h := D.bxi
  obtain ⟨hsc, hsc0, hidle⟩ := D.cap.2.2 sc b rfl
  unfold schedcontext.decode
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  -- the stall
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      L.actionW r.1 = L.actionW s ∧ L.curW r.1 = L.curW s ∧ L.idleW r.1 = L.idleW s ∧ L.cscW r.1 = L.cscW s ∧
      (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem r.1 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ x ∈ Ω, L.mem r.1 x = L.mem s x) ∧ WritesIn st s r.1 (NodeW st s)) ?_ ?_
  · split
    · exact WP.spec_mono (smp.remote_tcb_stall.bxi hA s a i h) fun r hr => by
        obtain ⟨s', a'⟩ := r; simpa using hr
    · exact (WP.spec_ok _).2 ⟨h, rfl, rfl, rfl, rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl, WritesIn.refl _ _⟩
  rintro ⟨s1, a1⟩ ⟨h1, ea1, ec1, ei1, ecs1, f1, o1, w1⟩
  try simp only [WP.uncurry'_pair]
  have W1 : WritesIn st s s1 (KO st T Cs Ω H Sg Scs Z s) :=
    WritesIn.mono w1 fun _ hb => NodeW.ko h.1.choose_spec.choose_spec.cur hb
  have KT : ∀ {s' : S}, WritesIn st s1 s' (KO st T Cs Ω H Sg Scs Z s1) →
      WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) :=
    fun w => (KO.trans W1 w).mono fun _ hb => Or.inl (Or.inl hb)
  have KTD : ∀ {s' : S}, WritesIn st s1 s' (fun b => KOD st T Cs Ω H Sg Scs Z s1 b ∨ b ∈ U) →
      WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) :=
    fun w => KODU.trans W1 w
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.1.sub
  have run1 : Runnable (L.mem s1 (stA (L.curW s))) := by
    rw [stA_eq, f1 _ hct _ (by simp) (by simp), ← stA_eq]; exact D.run
  have act1 : L.actionW s1 = 0#u64 := ea1.trans D.act
  have idle1 : L.mem s1 (scTcbA sc) ≠ L.idleW s1 := by
    rw [o1 _ (hsub _ (hO.fixW sc hsc).1), ei1]; exact hidle
  have hU1 : UserOK st T Cs Ω H U s1 := D.user.ksb w1.1
  have hx1 := D.extra s1 w1
  have Er : ∀ e : error.SysError, (ok ((core.result.Result.Err (error.Exc.Sys e) : core.result.Result Unit error.Exc),
      s1, a1) : Result _) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧
        WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) ⦄ := fun e =>
    (WP.spec_ok _).2 ⟨DecPost.of_bxi h1 (by simp), W1.mono fun _ hb => Or.inl (Or.inl hb)⟩
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = L.curW s := ect.trans ec1
  subst ect'
  simp only [error.illegal, error.truncated, error.invalid_cap, bind_ok]
  split
  · -- Consumed
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
      (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
    obtain ⟨Q2, R2, x2⟩ := BXI.xs (sx := L.curW s) (BlkOK.bxi h2) (hU1.ksb k2.ksb)
    have hG2 : XG st T Cs Ω H Sg Scs Z P3Ok s2 :=
      ⟨s, he, Cur0W.trans (W1.mono fun _ hb => KO.cur0w hb) (Foot.cur0w f2 (Set.empty_subset _))⟩
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.xs hA E x2 hsc hct
        fun s' h' => XG.xs hG2 h' (hU1.ksb k2.ksb) hct)
      (schedcontext.set_consumed.blk hA s2 a1 sc (L.curW s) call h2 hsc hct)) fun s3 ⟨x3, _, f3, _⟩ => ?_
    have hst : L.mem s3 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, x3.fr.2.2.2.2.1 _ hct _ (by simp) (by simp) (by simp) (fun _ => by simp), ← stA_eq, e2]
    refine WP.spec_bind (WP.spec_and (sched.set_thread_state.running_bxi x3.bxi hct hst)
      (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 _ _ x3.1.1 hct)) fun s4 ⟨h4, f4⟩ => ?_
    exact (WP.spec_ok _).2 ⟨DecPost.of_bxi h4 (by simp), KT (KO.trans (Foot.ko f2 (Set.empty_subset _))
      (KO.trans (Foot.ko f3 (Set.empty_subset _)) (Foot.ko f4 (Set.empty_subset _))))⟩
  split
  · -- Bind
    refine WP.spec_bind (schedcontext.extra_cap.ok (fun sl hsl h0 => hx1 sl hsl h0)) fun o ho => ?_
    rcases o with _ | c
    · exact Er _
    have hcO := ho c rfl
    cases c
    all_goals first | exact Er _ | skip
    · -- a notification
      rename_i ptr _ _ _
      obtain ⟨hpN, -⟩ := hcO.1.2.1 ptr _ _ _ rfl
      dsimp only
      refine WP.spec_bind (obj.Sc.ntfn.val s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      rename_i hi1
      refine WP.spec_bind (obj.Ntfn.sc.val s1 ptr) fun i2 ei2 => ?_
      split
      · exact Er _
      rename_i hi2
      refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
        (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
      have z1 : L.mem s2 (ntfnScA ptr) = 0#u64 := by
        rw [k2.nsc ptr hpN, ← ei2]; exact UScalar.eq_of_val_eq (by simpa using hi2)
      have z2 : L.mem s2 (scNtfnA sc) = 0#u64 := by
        rw [k2.snt sc hsc, ← ei1]; exact UScalar.eq_of_val_eq (by simpa using hi1)
      refine WP.spec_bind (WP.spec_and (schedcontext.bind_ntfn.blk s2 sc ptr h2 hsc hsc0 hpN z1 z2)
        (schedcontext.bind_ntfn.ko s2 sc ptr h2 hsc hpN)) fun s3 ⟨h3, f3⟩ => ?_
      exact (WP.spec_ok _).2 ⟨DecPost.of_bxi (BlkOK.bxi h3) (by simp), KT (KO.trans (Foot.ko f2 (Set.empty_subset _)) f3)⟩
    · -- a thread
      rename_i ptr
      have hpT : ptr ∈ T := hcO.2.1 ptr rfl
      dsimp only
      refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      rename_i hi1
      refine WP.spec_bind (obj.Tcb.sc.spec s1 ptr) fun i2 ei2 => ?_
      split
      · exact Er _
      rename_i hi2
      have z1 : L.mem s1 (scTcbA sc) = 0#u64 := by rw [← ei1]; exact UScalar.eq_of_val_eq (by simpa using hi1)
      have z2 : L.mem s1 (scA ptr) = 0#u64 := by rw [← ei2]; exact UScalar.eq_of_val_eq (by simpa using hi2)
      refine WP.spec_bind (sched.is_blocked.br s1 ptr) fun bb hbb => ?_
      -- a64: AArch64 stalls the target (`remote_tcb_stall`) before the restart and the bind
      have fin : (BlockedR (L.mem s1 (stA ptr)) → sc ∈ Ac) →
          (do
            let (s2, a2) ← smp.remote_tcb_stall st ar s1 a1 ptr
            let s3 ← sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART
            let (s4, a3) ← schedcontext.bind_tcb st ar s3 a2 sc ptr
            ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s4, a3)) ⦃ r s' _ =>
              DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) ⦄ := by
        intro hbA
        have rv1 : L.mem s1 (runVcpuA ptr) = L.mem s (runVcpuA ptr) := by
          rw [runVcpuA]; exact f1 _ hpT _ (by simp) (by simp)
        refine WP.spec_mono (sc_bind_stall.blk_fV hA s1 a1 _ sc ptr h1 hct run1 hpT hsc hsc0 z2 z1 hbA
          -- a64: the target's run VCPU is a VCPU object's words (`ScBindOwnV`, from `rcv`)
          (fun hnz => by rw [rv1] at hnz ⊢; exact BO Ac s _ extra he D ptr hpT hnz)
          (hsub _ (hO.fixW sc hsc).1)) fun r hr => by
          obtain ⟨r', s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KTD hr.2.2⟩
      split
      · refine WP.spec_bind (sporadic.sc_released.act s1 sc) fun b1 hb1 => ?_
        split
        · rename_i hb1t
          exact fin fun _ => (h1.2.2.2.2.act sc hsc).2 (hb1 hb1t)
        · exact Er _
      · rename_i hbf
        exact fin fun hb => absurd hb (hbb (by simpa using hbf))
  split
  · -- UnbindObject
    refine WP.spec_bind (schedcontext.extra_cap.ok (fun sl hsl h0 => hx1 sl hsl h0)) fun o ho => ?_
    rcases o with _ | c
    · exact Er _
    have hcO := ho c rfl
    cases c
    all_goals first | exact Er _ | skip
    · rename_i ptr _ _ _
      dsimp only
      refine WP.spec_bind (obj.Sc.ntfn.val s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      exact WP.spec_mono (sc_unbind_ntfn.blkF s1 a1 _ sc h1.blk hct run1 hsc) fun r hr => by
        obtain ⟨r', s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KT (Foot.ko hr.2.2.1 (Set.empty_subset _))⟩
    · rename_i ptr
      dsimp only
      refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      split
      · exact Er _
      exact WP.spec_mono (sc_unbind_tcb.blkF s1 a1 _ sc h1.blk hct run1 hsc hsc0
        (fun hz e => hz (by rw [← e, act1])) (fun _ => Ne.symm idle1)) fun r hr => by
        obtain ⟨r', s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KT (Foot.ko hr.2.2.1 (Set.empty_subset _))⟩
  split
  · -- Unbind
    refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
    split
    · exact Er _
    exact WP.spec_mono (sc_unbind.blkF hA s1 a1 _ sc h1.blk hct run1 hsc hsc0
      (fun hz e => hz (by rw [← e, act1])) (fun _ => Ne.symm idle1)) fun r hr => by
      obtain ⟨r', s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨DecPost.of_bxi (BlkOK.bxi hr.2.1) (by rw [hr.1]; simp), KT (Foot.ko hr.2.2.1 (Set.empty_subset _))⟩
  split
  · -- YieldTo
    refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
    refine WP.spec_bind (obj.Tcb.is_null.spec i1) fun bn ebn => ?_
    split
    · exact Er _
    rename_i hbn
    refine WP.spec_bind (tcb_eq.blk i1 (L.curW s)) fun be ebe => ?_
    split
    · exact Er _
    rename_i hbe
    refine WP.spec_bind (obj.Tcb.prio.spec s1 i1) fun i2 _ => ?_
    refine WP.spec_bind (P0.obj.Tcb.mcp.p0 st (L.curW s) s1 hS) fun i3 _ => ?_
    split
    · exact Er _
    refine WP.spec_bind (obj.Tcb.yield_to.spec s1 (L.curW s)) fun i4 ei4 => ?_
    split
    · exact Er _
    rename_i hi4
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
      (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
    have hc2 : L.curW s2 = L.curW s := k2.curW.trans ec1
    have t2 : L.mem s2 (scTcbA sc) = i1 := (k2.fix sc hsc).1.trans ei1.symm
    have y2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
      unfold yieldA
      rw [k2.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)]
      rw [← yieldA, ← ei4]; exact UScalar.eq_of_val_eq (by simpa using hi4)
    refine WP.spec_bind (Y Ac s2 a1 sc call (BlkOK.bxi h2) (hU1.ksb k2.ksb) hsc hsc0 (by rw [hc2]; exact e2)
      (by rw [t2]; intro e; exact hbn (by rw [ebn, e]; rfl))
      (by rw [t2, hc2]; intro e; exact hbe (by rw [ebe, e]; simp))
      (by rw [hc2]; exact y2)
      (by rcases k2.act with e | e
          · left; rw [e, act1]
          · right; exact e)
      (by rw [hc2, k2.scf hct, scA_eq, f1 _ hct _ (by simp) (by simp), ← scA_eq]; exact h.2.1.resume D.act)
      (by rw [hc2, k2.scf hct, scA_eq, f1 _ hct _ (by simp) (by simp), ← scA_eq]
          exact D.cb.ac (h.2.1.resume D.act))
      (by rw [hc2, inqA_eq, k2.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩),
            f1 _ hct _ (by simp) (by simp), ← inqA_eq]; exact D.cb.nr)) ?_
    rintro ⟨s3, a2⟩ ⟨⟨Ac3, h3⟩, f3⟩
    try simp only [WP.uncurry'_pair]
    exact (WP.spec_ok _).2 ⟨DecPost.of_bxi h3 (by simp), KT (KO.trans (Foot.ko f2 (Set.empty_subset _)) f3)⟩
  · exact Er _

/-- **InvGaps' `schedContext`, discharged** but for the named `ScYieldGap`, over `ScBindOwnV` (from `rcv`). -/
theorem decGap_sc_fV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (BO : ScBindOwnV st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedContext := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i sc b
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact WP.spec_mono (schedcontext.decode.dec_fV hA E Y BO s a lbl sc call extra b D hE) fun _ hr => hr.1

end

/-! ## `SchedControl_ConfigureFlags` (QueueSchedCtl) -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {s : S}

set_option maxHeartbeats 4000000 in
/-- `configure_flags`' last block for a bound SC: the thread migrates to the
SC's core, the SC is resumed, and the thread is switched to, enqueued or
the remote core told to reprogram; the current core reschedules if the
thread is current. -/
theorem cfDV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s3 : S) (a1 : A) (i target cpu : U64)
    (h : BlkOKW st T Cs Ω H Sg Rp Scs Nt Z Ac ∅ i s3) (hi : i ∈ T)
    (htq : (L.mem s3 (inqA i) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s3 (inqA i) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : L.mem s3 (scA i) = target) (ht0 : target ≠ 0#u64) (htS : target ∈ Scs) (htA : target ∈ Ac)
    (hcpu : cpu ∈ Cs) (hna : ∀ y ∈ T, L.actionW s3 ≠ y) (hco3 : L.mem s3 (scCoreA target) = cpu)
    (hpo : L.mem s3 (runVcpuA i) ≠ 0#u64 → VcWords Ω Sg (L.mem s3 (runVcpuA i))) :
    (do
  let (s5, a3) ←
    smp.migrate_tcb st ar s3 a1 i cpu
  let (s6, a4) ←
    schedcontext.resume st ar s5 a3 target
  let i1 ← st.cur_cpu s6
  let (s7, a5) ←
    if cpu = i1
    then
      do
      let b1 ← sched.is_runnable st s6 i
      let t ←
        if b1
        then
          do
          let t1 ← sched.cur_thread st s6
          let b2 ←
            core.cmp.PartialEq.ne.trait_default
              obj.Tcb.Insts.CoreCmpPartialEqTcb i t1
          if b2
          then sched.possible_switch_to st s6 i
          else ok s6
        else ok s6
      ok (t, a4)
    else
      do
      let b1 ← sched.is_schedulable st s6 i
      if b1
      then
        let s8 ← sched.enqueue st s6 i
        smp.remote_reschedule st ar s8 a4 cpu
      else
        let s8 ← sched.set_reprogram_on st s6 cpu
        smp.remote_reschedule st ar s8 a4 cpu
  let t ← sched.cur_thread st s7
  let b1 ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq i t
  let t1 ←
    if b1
    then sched.reschedule_required st s7
    else ok s7
  ok (t1, a5)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  -- a64: `migrate_tcb` flushes a running VCPU of `i` (its `OWNER_CPU` word an `Ω \ Sg` word, `hpo`)
  refine WP.spec_bind (migrate_tail_fV hA s3 a1 target i cpu Q R h0 hB hX hS hSg hi htq htr hcpu htS
    (fun _ => by rw [hsc]; exact hco3) hpo) ?_
  rintro ⟨s5, a3⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, -, -, -, ⟨sc5, -, ea5⟩⟩ := hh
  have sc5' : L.mem s5 (scA i) = target := sc5.trans hsc
  have tc5 : L.mem s5 (scTcbA target) = i := by
    have := (hX5.2.2.bound i hi (by rw [sc5']; exact ht0)).2.1; rwa [sc5'] at this
  refine WP.spec_bind (schedcontext.resume.all hA s5 a3 target Q5 R5 h5 hB5 hX5 hSg5 hS5 fun _ _ => ?_) ?_
  · rw [tc5]
    exact ⟨hi, h5.omega _ ((objs_omega hX5.1 hSg5.sub).2 target htS).2.1, hX5.2.2.core target htS,
      by rw [ea5]; exact hna i hi⟩
  rintro ⟨s6, a4⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨Q6, R6, h6, hB6, hX6, hSg6, f6⟩ := hh
  have hS6 := hS5.fr f6
  have sc6 : L.mem s6 (scA i) = target := (f6.sc i hi).trans sc5'
  have hb6 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 := ⟨⟨Q6, R6, h6⟩, hB6, hX6, hS6, hSg6⟩
  step with LawfulStore.cur_cpu_spec as ⟨i1, ei1⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · step with sched.is_runnable.spec' as ⟨b1, hb1⟩
      refine WP.spec_bind (Pₘ := fun t => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t) ?_ fun t ht => (WP.spec_ok _).2 ht
      split
      · rename_i hb1t
        step with sched.cur_thread.spec as ⟨t1, _⟩
        step with tcb_ne.blk as ⟨b2, _⟩
        split
        · exact WP.spec_mono (sched.possible_switch_to.sch s6 i Q6 R6 h6 hB6 hSg6 hi (hb1 hb1t)
            (fun _ => by rw [sc6]; exact htA)) fun s7 ⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, _, _⟩ =>
              ⟨⟨Q7, R7, h7⟩, hB7, hX6.fr f7, hS6.fr f7, hSg6.fr f7⟩
        · exact (WP.spec_ok _).2 hb6
      · exact (WP.spec_ok _).2 hb6
    · step with sched.is_schedulable.spec' as ⟨b1, eb1⟩
      split
      · rename_i hb1
        obtain ⟨hrun, hbd, hrl, hrm⟩ := eb1 hb1
        have hA6 : L.mem s6 (scA i) ∈ Ac := (hS6.act _ (hX6.2.2.bound i hi hbd).1).2 hrm
        refine WP.spec_bind (sched.enqueue.sch s6 i Q6 R6 h6 hB6 hSg6 hi (fun _ => hrl) (fun _ => hrun)
          (fun _ => hbd) (fun _ => hA6)) ?_
        rintro s8 ⟨⟨⟨Q8, R8, h8⟩, hB8, f8⟩, -, -, -⟩
        exact WP.spec_mono (smp.remote_reschedule.blk a4 cpu ⟨⟨Q8, R8, h8⟩, hB8, hX6.fr f8, hS6.fr f8, hSg6.fr f8⟩)
          fun r hr => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr.1
      · refine WP.spec_bind (sched.set_reprogram_on.blk cpu hb6 hcpu) fun s8 hh8 => ?_
        exact WP.spec_mono (smp.remote_reschedule.blk a4 cpu hh8.1)
          fun r hr => by obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr.1
  rintro ⟨s7, a5⟩ h7
  try simp only [WP.uncurry'_pair] at h7 ⊢
  step with sched.cur_thread.spec as ⟨t, _⟩
  step with tcb_eq.blk as ⟨b1, _⟩
  refine WP.spec_bind (Pₘ := fun t1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t1) ?_ fun t1 h => (WP.spec_ok _).2 h
  split
  · obtain ⟨⟨Q7, R7, q7⟩, hB7, hX7, hS7, hSg7⟩ := h7
    exact WP.spec_mono (sched.reschedule_required.sch s7 Q7 R7 q7 hB7 hSg7)
      fun s' ⟨⟨⟨Q', R', q'⟩, hB', f'⟩, _, _, _⟩ => ⟨⟨Q', R', q'⟩, hB', hX7.fr f', hS7.fr f', hSg7.fr f'⟩
  · exact (WP.spec_ok _).2 h7

set_option maxHeartbeats 8000000 in
/-- **seL4 `schedControl_configureFlags` keeps the invariants**, the SC made
active (`insert target Ac`): its thread (if any) is taken out of the queues,
the refills are rewritten, the SC moves to `cpu`, the thread migrates and is
resumed, then the badge and the sporadic flag are set. -/
theorem schedcontext.configure_flags.blkV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (target cpu budget period max_refills badge flags : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htS : target ∈ Scs) (ht0 : target ≠ 0#u64) (hcpu : cpu ∈ Cs)
    (h2 : sporadic.MIN_REFILLS.val ≤ max_refills.val) (hm : max_refills.val ≤ absMax (Z target))
    (hna : ∀ y ∈ T, L.actionW s ≠ y)
    (hpo : ∀ p ∈ T, L.mem s (runVcpuA p) ≠ 0#u64 → VcWords Ω Sg (L.mem s (runVcpuA p))) :  -- a64: `migrate_tcb`'s VCPU flush
    schedcontext.configure_flags st ar s a target cpu budget period max_refills badge flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) r.1 ⦄ := by
  have hX := h.2.2.1
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc target htS
  have hTA : target ∈ insert target Ac := Set.mem_insert _ _
  unfold schedcontext.configure_flags
  step with obj.Sc.tcb.spec as ⟨i, ei⟩
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  have hiT : i ≠ 0#u64 → i ∈ T := fun h0 => by rw [ei]; exact hX.2.2.yt.1 target htS (by rw [← ei]; exact h0)
  have hsci : i ≠ 0#u64 → L.mem s (scA i) = target := fun h0 => by
    rw [ei]; exact hX.2.2.tsc target htS ht0 (by rw [← ei]; exact h0)
  have hbi : b = false → i ≠ 0#u64 := fun hf e => by rw [eb, e] at hf; simp at hf
  -- the thread out of the queues
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      (b = false → (L.mem r.1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem r.1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem r.1 (scA i) = target) ∧ (∀ y ∈ T, L.actionW r.1 ≠ y) ∧
        (∀ y ∈ T, L.mem r.1 (scA y) = target → y = i) ∧
        (b = false → L.mem r.1 (runVcpuA i) = L.mem s (runVcpuA i)) ∧ L.ksb r.1 = L.ksb s) ?_ ?_
  · split
    · rename_i hb
      exact (WP.spec_ok _).2 ⟨h, fun hf => absurd (hf.symm.trans hb) (by simp), hna, fun y hy e => by
        have := (hX.2.2.bound y hy (by rw [e]; exact ht0)).2.1
        rw [e, ← ei] at this; exact this.symm, fun hf => absurd (hf.symm.trans hb) (by simp), rfl⟩
    · rename_i hb
      have hi0 : i ≠ 0#u64 := hbi (by simpa using hb)
      exact WP.spec_mono (cfA hA a i target h (hiT hi0) hna) fun r ⟨h1, q1, r1, a1, s1, _, rv1, kb1⟩ =>
        ⟨h1, fun _ => ⟨q1, r1, s1.trans (hsci hi0)⟩, a1, fun y hy e => by
          have b1 := (h1.2.2.1.2.2.bound y hy (by rw [e]; exact ht0)).2.1
          have b2 := (h1.2.2.1.2.2.bound i (hiT hi0) (by rw [s1.trans (hsci hi0)]; exact ht0)).2.1
          rw [e] at b1; rw [s1.trans (hsci hi0)] at b2; exact b1.symm.trans b2, fun _ => rv1, kb1⟩
  rintro ⟨s1, a1⟩ ⟨h1, hq1, ha1, hu1, rv1, kb1⟩
  try simp only [WP.uncurry'_pair]
  -- the refills
  have keep : ∀ s2 : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 →
      L.actionW s2 = L.actionW s1 →
      (∀ y ∈ T, L.mem s2 (scA y) = L.mem s1 (scA y) ∧ L.mem s2 (stA y) = L.mem s1 (stA y) ∧
        L.mem s2 (inqA y) = L.mem s1 (inqA y)) →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
      (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
        (∀ y ∈ T, L.mem s2 (scA y) = target → y = i) := fun s2 h2' ea fl =>
    ⟨h2', fun hf => by
      have hiT' := hiT (hbi hf)
      obtain ⟨q, r, sc⟩ := hq1 hf
      rw [(fl i hiT').2.2, (fl i hiT').1]; exact ⟨q, r, sc⟩, fun y hy => by rw [ea]; exact ha1 y hy,
      fun y hy e => hu1 y hy (by rw [← (fl y hy).1]; exact e)⟩
  have RN : ∀ m bud per : U64, sporadic.MIN_REFILLS.val ≤ m.val → m.val ≤ absMax (Z target) →
      sporadic.refill_new st s1 target m bud per ⦃ s2 =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
        (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
          L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
        (∀ y ∈ T, L.mem s2 (scA y) = target → y = i) ∧ WritesIn st s1 s2 (RFW target (Z target)) ⦄ := fun m bud per hm2 hmm =>
    WP.spec_mono (sporadic.refill_new.fr m bud per hP hz hm2 hmm) fun s2 ⟨wf, w⟩ => by
      obtain ⟨h2', ea, -, -, fl⟩ := refill_blk h1 htS w wf
      obtain ⟨k1, k2, k3, k4⟩ := keep s2 h2' ea fl
      exact ⟨k1, k2, k3, k4, w⟩
  have RU : ∀ per bud m : U64, sporadic.MIN_REFILLS.val ≤ m.val → m.val ≤ absMax (Z target) →
      sporadic.refill_update st s1 target per bud m ⦃ s2 =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
        (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
          L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
        (∀ y ∈ T, L.mem s2 (scA y) = target → y = i) ∧ WritesIn st s1 s2 (RFW target (Z target)) ⦄ := fun per bud m hm2 hmm =>
    WP.spec_mono (sporadic.refill_update.fr per bud m hP hz hm2 hmm) fun s2 ⟨wf, w⟩ => by
      obtain ⟨h2', ea, -, -, fl⟩ := refill_blk h1 htS w wf
      obtain ⟨k1, k2, k3, k4⟩ := keep s2 h2' ea fl
      exact ⟨k1, k2, k3, k4, w⟩
  have hmin : sporadic.MIN_REFILLS.val ≤ absMax (Z target) := h2.trans hm
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
      (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s2 (scA i) = target) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
        (∀ y ∈ T, L.mem s2 (scA y) = target → y = i) ∧ WritesIn st s1 s2 (RFW target (Z target))) ?_ ?_
  · split
    · exact RN _ _ _ (le_refl _) hmin
    · step with obj.Sc.cpu.spec as ⟨i1, _⟩
      split
      · step with sporadic.sc_active.val as ⟨b1, _⟩
        split
        · split
          · exact RN _ _ _ h2 hm
          · step with sched.is_runnable.spec' as ⟨b2, _⟩
            split
            · exact RU _ _ _ h2 hm
            · exact RN _ _ _ h2 hm
        · exact RN _ _ _ h2 hm
      · exact RN _ _ _ h2 hm
  rintro s2 ⟨h2', hq2, ha2, hu2, w2⟩
  -- the core
  refine WP.spec_bind (obj.Sc.set_cpu.wr s2 target cpu) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, ea3, -, -, fl3⟩ := scword_blkW (d := i) h2' htS hTA (Or.inl (scCoreA_val hP hz))
    (fun _ => ⟨hcpu, fun t ht hne e => hne (hu2 t ht e)⟩)
  have hco3 : L.mem (L.wr s2 (scCoreA target) cpu) (scCoreA target) = cpu :=
    L.mem_wr_same (by obtain ⟨h8', -, -⟩ := sc_lo hP hz; have := scCoreA_val hP hz; unfold Aligned; omega)
  -- a64: the thread's `RUN_VCPU` word and the kernel base are kept from `s` (for `migrate_tcb`'s `hpo`)
  have rv3 : b = false → L.mem (L.wr s2 (scCoreA target) cpu) (runVcpuA i) = L.mem s (runVcpuA i) := fun hf => by
    have hiT' := hiT (hbi hf)
    have q1 := h1.1.choose_spec.choose_spec
    have q2 := h2'.1.choose_spec.choose_spec
    have hfa : Aligned (runVcpuA i) := field_aligned (K := 3672#u64) (q2.tcbs i hiT') (by simp) (by simp)
    have hcO : scCoreA target ∈ Ω := ((objs_omega h2'.2.2.1.1 h2'.2.2.2.2.sub).2 target htS).2.1
    have hrv2 : L.mem s2 (runVcpuA i) = L.mem s1 (runVcpuA i) :=
      w2.mem_eq hfa fun hh => out_ne_field (q1.omega _ (h1.2.2.1.1.scW target htS _ hfa (RFW.insc hP hz hh)))
        hiT' (q1.tcbs i hiT') (K := 3672#u64) (by simp) rfl
    rw [L.mem_wr_ne (by obtain ⟨h8', -, -⟩ := sc_lo hP hz; have := scCoreA_val hP hz; unfold Aligned; omega) hfa
      (fun e => out_ne_field (q2.omega _ hcO) hiT' (q2.tcbs i hiT') (K := 3672#u64) (by simp) e.symm), hrv2]
    exact rv1 hf
  have kb3 : L.ksb (L.wr s2 (scCoreA target) cpu) = L.ksb s := (L.ksb_wr _ _ _).trans (w2.1.trans kb1)
  -- the thread
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) r.1) ?_ ?_
  · split
    · rename_i hb
      have hi0 : i = 0#u64 := by rw [eb] at hb; simpa using hb
      exact (WP.spec_ok _).2 ⟨h3.1, h3.2.1, h3.2.2.1.1.x h3.2.2.1.2.1 (h3.2.2.1.2.2.full fun hiT0 _ =>
        ((h3.1.choose_spec.choose_spec.tcbs _ hiT0).ne0 (by rw [hi0]; simp)).elim), h3.2.2.2⟩
    · rename_i hb
      have hbf : b = false := by simpa using hb
      have hiT' := hiT (hbi hbf)
      obtain ⟨q2, r2, sc2⟩ := hq2 hbf
      exact cfDV hA _ a1 i target cpu h3 hiT' (by rw [(fl3 i hiT').2.2]; exact q2)
        (by rw [(fl3 i hiT').2.2]; exact r2) (by rw [(fl3 i hiT').1]; exact sc2) ht0 htS hTA hcpu
        (fun y hy => by rw [ea3]; exact ha2 y hy) hco3
        (fun hne => by rw [rv3 hbf] at hne ⊢; exact hpo i hiT' hne)
  rintro ⟨s4, a2⟩ h4
  try simp only [WP.uncurry'_pair] at h4 ⊢
  -- the badge and the sporadic flag
  refine WP.spec_bind (obj.Sc.set_badge.wr s4 target badge) fun s5 e5 => ?_
  subst e5
  have h5 := (scword_blk (v := badge) h4 htS hTA (Or.inr (Or.inl (by
    rw [sc_word_val hP hz (o := layout.sc.BADGE) (by simp [layout.sc.BADGE])]; simp [layout.sc.BADGE])))
    (fun e => by
      have := congrArg UScalar.val e
      rw [sc_word_val hP hz (o := layout.sc.BADGE) (by simp [layout.sc.BADGE]), scCoreA_val hP hz] at this; simp [layout.sc.BADGE] at this)).1
  simp only [lift, bind_ok]
  have spv : ∀ v : U64, BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac)
      (L.wr (L.wr s4 (core.num.U64.wrapping_add target layout.sc.BADGE) badge)
        (core.num.U64.wrapping_add target layout.sc.SPORADIC) v) := fun v =>
    (scword_blk (v := v) h5 htS hTA (Or.inr (Or.inr (by
      rw [sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])]; simp [layout.sc.SPORADIC])))
      (fun e => by
        have := congrArg UScalar.val e
        rw [sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC]), scCoreA_val hP hz] at this
        simp [layout.sc.SPORADIC] at this)).1
  split
  · exact WP.spec_bind (obj.Sc.set_sporadic.wr _ target 1#u64) fun s6 e6 => (WP.spec_ok _).2 (by subst e6; exact spv _)
  · exact WP.spec_bind (obj.Sc.set_sporadic.wr _ target 0#u64) fun s6 e6 => (WP.spec_ok _).2 (by subst e6; exact spv _)

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errDV" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (DecPost.of_bxi D.bxi (by simp))
  | (simp only [error.range, error.illegal, error.truncated, error.invalid_cap, bind_ok]
     exact (WP.spec_ok _).2 (DecPost.of_bxi D.bxi (by simp))))

set_option maxHeartbeats 8000000 in
/-- **`SchedControl_ConfigureFlags`** keeps the invariants, from `ScCtlPlace`. -/
theorem schedcontext.decode_sched_control.decV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {U : Set U64} (Pl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (BO : ScBindOwnV st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {a : A} {lbl cpu len buf : U64}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.SchedControl cpu) extra)
    (hE : EntAt st P3Ok s) :
    schedcontext.decode_sched_control st ar s a lbl cpu len buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hcpu := Pl.core Ac s _ extra hE D cpu rfl
  unfold schedcontext.decode_sched_control
  split
  · errDV
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  refine WP.spec_bind (schedcontext.extra_cap.gen (P := fun c => CapOK st T Rp Scs Nt H s c ∧
      ∀ ptr sz, c = .SchedContext ptr sz → sz.val = Z ptr)
    (fun sl hsl h0 => WP.spec_and (D.extra s (WritesIn.refl _ _) sl hsl h0) (Pl.size Ac s _ extra hE D sl hsl h0))) ?_
  rintro o ho
  rcases o with _ | c
  · errDV
  obtain ⟨hcO, hsz⟩ := ho c rfl
  simp only
  split
  · errDV
  refine WP.spec_bind (P0.sporadic.max_period_us.p0 ar a hA) fun max_us _ => ?_
  step with sporadic.min_budget_us.spec as ⟨min_us, _⟩
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 0#u64 hS) fun budget_us _ => ?_
  split
  · errDV
  refine WP.spec_bind (hA.us_to_ticks a budget_us) fun budget _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 1#u64 hS) fun period_us _ => ?_
  split
  · errDV
  refine WP.spec_bind (hA.us_to_ticks a period_us) fun period _ => ?_
  refine WP.spec_bind (sporadic.min_budget.ok hA a) fun mb _ => ?_
  split
  · errDV
  split
  · errDV
  split
  · errDV
  cases c
  all_goals first | errDV | skip
  rename_i ptr sz
  obtain ⟨hpS, hp0, -⟩ := hcO.2.2 ptr sz rfl
  have hszv := hsz ptr sz rfl
  dsimp only
  obtain ⟨hP, hz⟩ := D.bxi.2.2.1.1.sc ptr hpS
  have h64 := hP.lt64
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 2#u64 hS) fun er _ => ?_
  refine WP.spec_bind (sporadic.refill_absolute_max.val sz) fun mr hmr => ?_
  rw [hszv] at hmr
  have hab : 2 ≤ absMax (Z ptr) := by
    unfold absMax; rw [if_neg (by omega)]
    have : 2 ^ 7 ≤ 2 ^ Z ptr := Nat.pow_le_pow_right (by norm_num) hz
    omega
  have hlt := absMax_lt (Z ptr)
  simp only [lift, bind_ok]
  split
  · errDV
  rename_i hle
  have hsub : (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val = mr.val - 2 := by
    simp [core.num.U64.wrapping_sub_val_eq, sporadic.MIN_REFILLS, U64.size_def, U64.numBits]; omega
  have hle' : er.val ≤ mr.val - 2 := by have := hle; rw [gt_iff_val, hsub] at this; omega
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 3#u64 hS) fun badge _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 4#u64 hS) fun flags _ => ?_
  have ect' : ct = L.curW s := ect
  subst ect'
  have hr := runnable_ok D.run
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct hr.1 hr.2) ?_
  rintro s1 ⟨h1, -, -, k1⟩
  try simp only [lift, bind_ok]
  have hadd : (core.num.U64.wrapping_add er sporadic.MIN_REFILLS).val = er.val + 2 := by
    simp [core.num.U64.wrapping_add_val_eq, sporadic.MIN_REFILLS, U64.size_def, U64.numBits]; omega
  have hna : ∀ y ∈ T, L.actionW s1 ≠ y := fun y hy e => by
    rcases k1.act with e' | e'
    · rw [e', D.act] at e; exact notT_small hT (by simp) (e ▸ hy)
    · rw [e'] at e; exact notT_small hT (by simp) (e ▸ hy)
  -- a64: a thread's run VCPU is a VCPU object's words at the decode start (`ScBindOwnV`),
  -- carried to `s1` (the restart keeps every `RUN_VCPU` word and the kernel base)
  have hpo1 : ∀ p ∈ T, L.mem s1 (runVcpuA p) ≠ 0#u64 → VcWords Ω Sg (L.mem s1 (runVcpuA p)) := fun p hp hne => by
    have e : L.mem s1 (runVcpuA p) = L.mem s (runVcpuA p) :=
      k1.fld p hp 3672#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
    rw [e] at hne ⊢
    exact BO Ac s _ extra hE D p hp hne
  refine WP.spec_bind (schedcontext.configure_flags.blkV hA a ptr cpu budget period _ badge flags h1 hpS hp0 hcpu
    (by rw [hadd]; simp [sporadic.MIN_REFILLS]) (by rw [hadd]; omega) hna hpo1) ?_
  rintro ⟨s2, a2⟩ h2
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))

/-- **InvGaps' `schedControl`, discharged** from `ScCtlPlace`. -/
theorem decGap_schedControlV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    (Pl : ScCtlPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (BO : ScBindOwnV st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedControl := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact schedcontext.decode_sched_control.decV hA Pl BO D hE

end

/-! ## `TCB_SetSchedParams` (QueueDecTcb2) -/

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- `tcs_tail` with its result: `Ok`. -/
theorem tcs_tail2V {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s0 s1 : S) (a1 : A)
    (target : obj.Tcb) (mcp prio : U64) (sc : obj.Sc) (flags : U64)
    (h1 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (ht : target ∈ T) (pf : PFr st T Sg s0 s1)
    (ec : L.curW s1 = L.curW s0)
    (hrel : (L.mem s1 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s0 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s0 →
      (L.mem s0 (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s0 (scA target) ≠ 0#u64 ∧
        L.mem s0 (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s0 (scA target) = 0#u64 ∧
      L.mem s0 (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s0 (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s0 ≠ target ∧ L.idleW s0 ≠ target)
    (hown : ∀ s' : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' → WritesIn st s1 s' (Cur0W st T Cs Ω H Sg Scs Z s1) →
      L.mem s' (runVcpuA target) ≠ 0#u64 → VcWords Ω Sg (L.mem s' (runVcpuA target))) :
    (do
      let i1 ← lift (flags &&& tcb.SCHED_UPDATE_MCP)
      let s3 ←
        if i1 != 0#u64
        then obj.Tcb.set_mcp st target s1 mcp
        else ok s1
      let i2 ← lift (flags &&& tcb.SCHED_UPDATE_PRIO)
      let s4 ←
        if i2 != 0#u64
        then sched.set_priority st s3 target prio
        else ok s3
      let i3 ← lift (flags &&& tcb.SCHED_UPDATE_SC)
      if i3 != 0#u64
      then
        let b ← obj.Sc.is_null sc
        if b
        then
          let i4 ← obj.Tcb.sc st target s4
          let b1 ← obj.Sc.is_null i4
          if b1
          then ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s4, a1)
          else
            let s5 ← schedcontext.unbind_tcb st s4 i4
            ok (core.result.Result.Ok (), s5, a1)
        else
          let (s5, a2) ← schedcontext.bind_tcb st ar s4 a1 sc target
          ok (core.result.Result.Ok (), s5, a2)
      else ok (core.result.Result.Ok (), s4, a1)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧
        r.1 = .Ok () ⦄ := by
  have hT := h1.1.choose_spec.choose_spec.tcbs
  have hta := hT target ht
  simp only [lift, Aeneas.Std.bind_ok]
  -- `MCP`
  refine WP.spec_bind (Pₘ := fun s3 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3 ∧ PFr st T Sg s0 s3 ∧
      WritesIn st s1 s3 (Cur0W st T Cs Ω H Sg Scs Z s1) ∧ L.curW s3 = L.curW s0 ∧
      ((L.mem s3 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64 → (L.mem s0 (inqA target) &&& sched.Q_RELEASE) ≠ 0#u64))
    ?_ ?_
  · split
    · refine WP.spec_mono (obj.Tcb.set_mcp.wr s1 target mcp) fun s' e => ?_
      subst e
      obtain ⟨Q1, R1, h1'⟩ := h1.1
      have hN := h1'.nodes _ h1'.cur
      refine ⟨(plainW_all (K := 3440#u64) (v := mcp) h1 ht (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)).1,
        pf.trans (PFr.of_fr (fr_field (K := 3440#u64) h1' h1.2.2.2.2 ht (by simp) (by simp) (by simp))
          (Or.inl (act_wr_field hN ht hta rfl (by simp) (by simp)))),
        (writesIn_wr (field_aligned (K := 3440#u64) hta (by simp) (by simp))).mono fun _ e =>
          Or.inl (e ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp)),
        (cur_wr_field hN ht hta (by simp) (by simp)).trans ec, fun hf => hrel ?_⟩
      rwa [inqA_eq, L.mem_wr_ne (field_aligned (K := 3440#u64) hta (by simp) (by simp))
        (field_aligned (K := 3592#u64) hta (by simp) (by simp))
        (fun e => field_ne (K1 := 3440#u64) (K2 := 3592#u64) hta hta (by simp) (by simp) (fun _ => by simp)
          (UScalar.eq_of_val_eq e)), ← inqA_eq] at hf
    · exact (WP.spec_ok _).2 ⟨h1, pf, WritesIn.refl _ _, ec, hrel⟩
  rintro s3 ⟨h3, pf3, w3, ec3, hrel3⟩
  -- priority
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ PFr st T Sg s0 s4 ∧
      WritesIn st s1 s4 (Cur0W st T Cs Ω H Sg Scs Z s1)) ?_ ?_
  · split
    · rename_i hf
      obtain ⟨hv, hc⟩ := hprio (by simpa using hf)
      have hcur3 : target = L.mem s3 (L.nodeAt s3 (L.cpu s3) layout.node.CUR_THREAD) → target = L.curW s0 :=
        fun e => e.trans ec3
      refine WP.spec_mono (sched.set_priority.blk s3 target prio h3 ht hv
        (fun e => by
          by_contra hn; exact hrel3 hn (hc (hcur3 e)).1)
        (fun e => by rw [pf3.sc target ht]; exact (hc (hcur3 e)).2.1)
        (fun e => by rw [pf3.sc target ht]; exact (hc (hcur3 e)).2.2)) fun s4 hh =>
          ⟨hh.1, pf3.trans hh.2.2, Cur0W.trans w3 (Foot.cur0w hh.2.1 fun _ h => h)⟩
    · exact (WP.spec_ok _).2 ⟨h3, pf3, w3⟩
  rintro s4 ⟨h4, pf4, w4⟩
  -- the SC
  split
  · rename_i hfs
    have hfs' : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 := by simpa using hfs
    step with obj.Sc.is_null.spec as ⟨b, eb⟩
    split
    · rename_i hb
      have hsc0 : sc = 0#u64 := by simpa [eb] using hb
      obtain ⟨hna, hid⟩ := hunb hfs' hsc0
      step with obj.Tcb.sc.spec as ⟨i4, ei4⟩
      step with obj.Sc.is_null.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 ⟨h4, rfl⟩
      · rename_i hb1
        have hi0 : i4 ≠ 0#u64 := fun e => hb1 (by rw [eb1, e]; rfl)
        obtain ⟨hiS, hit, -⟩ := h4.2.2.1.2.2.bound target ht (by rw [← ei4]; exact hi0)
        rw [← ei4] at hiS hit
        have hT4 := h4.1.choose_spec.choose_spec.tcbs
        refine WP.spec_bind (schedcontext.unbind_tcb.blk s4 i4 h4 hiS hi0 (fun _ => ?_) (fun _ => ?_))
          fun s5 hh => (WP.spec_ok _).2 ⟨hh.1, rfl⟩
        · rw [hit]
          rcases pf4.act with e | e
          · rw [e]; exact hna
          · rw [e]; exact fun e' => notT_small hT4 (by simp) (e' ▸ ht)
        · rw [hit, pf4.idle]; exact hid
    · rename_i hb
      have hsc0 : sc ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      obtain ⟨hsc, ht0, hc0, hbA⟩ := hbind hfs' hsc0
      refine WP.spec_bind (schedcontext.bind_tcb.blkF_fV
        (Es := ∅) hA s4 a1 sc target h4 ht hsc hsc0
        (by rw [pf4.sc target ht]; exact ht0)
        (by rw [pf4.sig _ (h4.2.2.1.1.fixW sc hsc).1]; exact hc0)
        (fun hb' => hbA (by rw [← pf4.st target ht]; exact hb'))
        (fun hne => hown s4 h4 w4 hne)) fun r hr => ?_
      obtain ⟨s5, a2⟩ := r
      exact (WP.spec_ok _).2 ⟨hr.1, rfl⟩
  · exact (WP.spec_ok _).2 ⟨h4, rfl⟩


/-- **`thread_control_sched` with the fault-handler update**, the install
keeping `BlkOK` with the `CaiFr` frame and (for its error results) `Cur0`. -/
theorem tcb.thread_control_sched.decV {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hfl : (flags &&& tcb.SCHED_UPDATE_FAULT) ≠ 0#u64)
    (hinst : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      (BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ CaiFr st T Scs 0#u64 s r.2.1 ∧
      (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64)) ∧ Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄)
    (hown : ∀ s' : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' → Fr0 st T Cs Ω H Sg Scs Z s0 s' →
      L.mem s' (runVcpuA target) ≠ 0#u64 → VcWords Ω Sg (L.mem s' (runVcpuA target)))
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target) :
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 r.2.1 ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.thread_control_sched
  simp only [lift, Aeneas.Std.bind_ok]
  split
  · obtain ⟨c, sl⟩ := fh
    refine WP.spec_bind hinst ?_
    rintro ⟨r, s2, a1⟩ ⟨⟨h2, F2, ha2⟩, c2⟩
    simp only [uncurry_apply_pair] at h2 F2 ha2 c2 ⊢
    cases r with
    | Ok u =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, Aeneas.Std.bind_ok]
      obtain ⟨hp2, hb2, hu2⟩ := tcs_conds_of_caifr hT ht F2 ha2 hprio hbind hunb
      have := tcs_tail2V hA s2 s2 a1 target mcp prio sc flags h2 ht (PFr.refl _ _) rfl id hp2 hb2 hu2
        (fun s' hb' w' hne => hown s' hb' (Cur0W.trans c2.fr w') hne)
      simp only [lift, Aeneas.Std.bind_ok] at this
      exact WP.spec_mono this fun r hr => DecPost.of_bxi (BlkOK.bxi hr.1) (by rw [hr.2]; simp)
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        Aeneas.Std.bind_ok]
      exact WP.spec_bind (Pₘ := fun _ => True) (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial)
        fun _ _ => (WP.spec_ok _).2 trivial) fun _ _ => (WP.spec_ok _).2 (Cur0.post c2)
  · rename_i hn
    exfalso; simp at hn hfl; exact hfl hn

end

end Fl4ProofsA64.P1
