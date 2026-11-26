/-
P1 (a64): **the SC `Bind` of a thread that runs a VCPU** — `migrate_tcb`'s VCPU-flush branch keeps the
invariants, replacing the false [J] `ScBindRv` (QueueDecSc) by a placement premise.

`ScBindRv` (at a decode, a thread with no SC has `RUN_VCPU` 0) is **not** a kernel invariant of FL4 on
AArch64: a thread `A` that calls `ARMVCPURun` becomes `TS_RUNNING_VM` with `RUN_VCPU = vc`
(`vcpu::decode_run`); another thread may then `SchedContext_UnbindObject(sc_A, A)` (`schedcontext::decode`
checks only `sc.tcb = A` and `A ≠ caller`; `unbind_tcb` clears the SC fields and touches neither the state
nor `RUN_VCPU`), or `TCB_SetSchedParams` with a null SC (`thread_control_sched` → `unbind_tcb`), or delete
`sc_A` (`finalise` → `unbind_all_tcbs` → `unbind_tcb`). Afterwards `A` has no SC and `RUN_VCPU ≠ 0`. Nothing
on those paths ends the run (`complete_run` / `cancel_run` are the only writers of 0). A following
`SchedContext_Bind(sc', A)` with `sc'` on another core reaches `migrate_tcb`'s `rv ≠ 0` branch, which the
Rust code handles on purpose (flush the VCPU, its guest TCB's FPU, write `OWNER_CPU := cpu + 1`).

So this module proves that branch instead:
* `migrate_vcpu_any`: `migrate_tcb`'s VCPU steps for any `RUN_VCPU` (the store is `s1`, or `s1` with the run
  VCPU's `OWNER_CPU` word written, `ownA`);
* `blkW_wrU`: a write of one user word (`UserOK`) keeps `BlkOKW` and the frame facts (`xfer_keep`);
* `migrate_tail_f`, `smp.migrate_tcb.frame_f`, `smp.migrate_tcb.kw_f`, `schedcontext.bind_tcb.blkF_f`,
  `sc_bind_tcb.blkF_f`, `sc_bind_stall.blk_f`, `schedcontext.decode.dec_f`, `decGap_sc_f`: `_f` twins of
  the QueueIpc / QueueInvoke / QueueDecSc lemmas without `hrv`, the footprint widened by the user words `U`
  (`FootDU`, `KOD ∨ U`);
* `InvGaps2F` / `InvGaps2F.gaps`: `InvGaps2` with `scBindOwn` in place of `scBindRv`.

Named premise (replaces [J] `ScBindRv`):
* **[P] `ScBindOwn`** (`InvGaps2F.scBindOwn`): at a decode, the `OWNER_CPU` word of the VCPU a thread runs
  (`RUN_VCPU ≠ 0`) is a user word (`∈ U`, so `UserOK`: outside the TCBs, nodes, `Ω` and the endpoints).
  Placement, the same kind and shape as VcpuCheckInv's [P] `hpw` (the run VCPU's `RUN_CALLER` word in `U`):
  a VCPU is a heap object of its own and P1 has no `UsrW` for its words.
-/
import Fl4ProofsA64.P1.QueueEntryGaps
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {Es : Set U64} {sx : U64}

/-- a64: the address of a VCPU's `OWNER_CPU` word. -/
def ownA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.OWNER_CPU

/-- a64: AArch64 `migrate_tcb`'s VCPU steps for any `RUN_VCPU`: with `RUN_VCPU` 0 the store stays `s1`
(`migrate_vcpu_idle`); otherwise the run VCPU and its guest TCB's FPU are flushed (Arch calls) and the
VCPU's `OWNER_CPU` word is written. -/
theorem migrate_vcpu_any {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a2 : A)
    (t cpu : U64) (f : S × A → Result (S × A)) {P : S × A → Prop}
    (hf : L.mem s1 (runVcpuA t) = 0#u64 → ∀ a3, f (s1, a3) ⦃ P ⦄)
    (hf' : L.mem s1 (runVcpuA t) ≠ 0#u64 → ∀ a3,
      f (L.wr s1 (ownA (L.mem s1 (runVcpuA t))) (core.num.U64.wrapping_add cpu 1#u64), a3) ⦃ P ⦄) :
    (do
      let v ← vcpu.bound st s1 t
      let a3 ← if v != 0#u64 then ar.vcpu_flush a2 v else ok a2
      let i1 ← layout.tcb.RUN_VCPU
      let i2 ← lift (core.num.U64.wrapping_add t i1)
      let rv ← st.read s1 i2
      let r ←
        if rv != 0#u64
        then
          do
          let a5 ← ar.vcpu_flush a3 rv
          let i3 ← lift (core.num.U64.wrapping_add rv vcpu.TCB)
          let gt ← st.read s1 i3
          let a6 ←
            if gt != 0#u64
            then
              do
              let a7 ← ar.fpu_flush a5 gt
              ar.fpu_release a7 gt
            else ok a5
          let i4 ← lift (core.num.U64.wrapping_add rv vcpu.OWNER_CPU)
          let i5 ← lift (core.num.U64.wrapping_add cpu 1#u64)
          let s3 ← st.write s1 i4 i5
          ok (s3, a6)
        else ok (s1, a3)
      f r) ⦃ P ⦄ := by
  by_cases h0 : L.mem s1 (runVcpuA t) = 0#u64
  · exact migrate_vcpu_idle hA s1 a2 t cpu h0 f (hf h0)
  refine WP.spec_bind (P0.vcpu.bound.p0 st s1 t L.total) fun v _ => ?_
  refine WP.spec_bind (show (if (v != 0#u64) = true then ar.vcpu_flush a2 v else ok a2) ⦃ _ => True ⦄ from ?_)
    fun a3 _ => ?_
  · by_cases hv : (v != 0#u64) = true
    · rw [if_pos hv]; exact hA.vcpu_flush_spec _ _
    · rw [if_neg hv]; exact (WP.spec_ok _).2 trivial
  · refine WP.spec_bind P0.Consts.layout.tcb.RUN_VCPU.spec fun i1 ei1 => ?_
    subst ei1
    simp only [lift, bind_ok]
    refine WP.spec_bind (L.read_spec s1 _) fun rv erv => ?_
    have hrv : rv = L.mem s1 (runVcpuA t) := erv
    have hb : (rv != 0#u64) = true := by rw [hrv]; simpa using h0
    rw [if_pos hb]
    refine WP.spec_bind (Pₘ := fun r : S × A =>
      r.1 = L.wr s1 (ownA (L.mem s1 (runVcpuA t))) (core.num.U64.wrapping_add cpu 1#u64)) ?_ ?_
    · refine WP.spec_bind (hA.vcpu_flush_spec _ _) fun a5 _ => ?_
      try simp only [lift, bind_ok]
      refine WP.spec_bind (L.read_spec s1 _) fun gt _ => ?_
      refine WP.spec_bind (show (if (gt != 0#u64) = true then (do
          let a7 ← ar.fpu_flush a5 gt
          ar.fpu_release a7 gt) else ok a5) ⦃ _ => True ⦄ from ?_) fun a6 _ => ?_
      · by_cases hg : (gt != 0#u64) = true
        · rw [if_pos hg]
          exact WP.spec_bind (hA.fpu_flush_spec _ _) fun a7 _ => hA.fpu_release_spec _ _
        · rw [if_neg hg]; exact (WP.spec_ok _).2 trivial
      · try simp only [lift, bind_ok]
        refine WP.spec_bind (L.write_spec s1 _ _) fun s3 e3 => ?_
        subst e3
        simp only [WP.spec_ok]
        rw [hrv]; rfl
    · rintro ⟨s3, a6⟩ e3
      simp only at e3
      subst e3
      exact hf' h0 a6

/-- **A write of one user word keeps `BlkOKW`** (the `BlkOKW` pieces, `xfer_all`'s argument with `XInvW`
kept through `XInv0.keep` / `TSc.keep` / `ScAffX.keep`: a user word may be a timer-tree word of a
node outside `Cs`, so `Fr` does not hold) and every TCB field past the registers, every `Ω` word and every node word. -/
theorem blkW_wrU {X : Set U64} {d b v : U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hB : BoundInv st T Ac s) (hX : XInvW st T Cs Ω Sg Rp Scs Nt Z d s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H {x | x = b} s) :
    SchedQueuesInvX st T Cs Ω H X (L.wr s b v) Q R ∧ BoundInv st T Ac (L.wr s b v) ∧
      XInvW st T Cs Ω Sg Rp Scs Nt Z d (L.wr s b v) ∧ SCsOK st T Ω Sg Scs Z Ac (L.wr s b v) ∧
      SgOK st Ω Sg (L.wr s b v) ∧ TmFr st T Cs Nt s (L.wr s b v) ∧
      (∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 →
        L.mem (L.wr s b v) (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) ∧
      (∀ a ∈ Ω, L.mem (L.wr s b v) a = L.mem s a) ∧
      (∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
        L.mem (L.wr s b v) (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)) ∧
      L.actionW (L.wr s b v) = L.actionW s := by
  have hb : Aligned b := (hU b rfl).1.1
  have hw : WritesIn st s (L.wr s b v) (XferFoot T {x | x = b}) :=
    (writesIn_wr hb).mono fun x e => Or.inr e
  obtain ⟨f1, f2, f3, f4⟩ := xfer_keep h hU hw
  have hT := h.tcbs
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => by rw [hw.2.1, nodeAt_of_ksb hw.1]; exact f3 _ h.cur o ho h8
  have ea : L.actionW (L.wr s b v) = L.actionW s := nd _ (by rw [act_val]; omega) (by rw [act_val])
  have ec : L.curW (L.wr s b v) = L.curW s := nd _ (by rw [curth0]; omega) (by rw [curth0])
  have ei : L.idleW (L.wr s b v) = L.idleW s := nd _ (by rw [idle8]; omega) (by rw [idle8])
  have ecs : L.cscW (L.wr s b v) = L.cscW s := nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have F := f1
  have scf : ∀ y ∈ T, L.mem (L.wr s b v) (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have iqf : ∀ y ∈ T, L.mem (L.wr s b v) (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have stf : ∀ y ∈ T, L.mem (L.wr s b v) (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have blf : ∀ y ∈ T, L.mem (L.wr s b v) (blockA y) = L.mem s (blockA y) := fun y hy => by
    rw [blockA_eq]; exact F y hy _ (by simp) (by simp) (by simp)
  have hsb : ∀ y ∈ T, L.mem (L.wr s b v) (stA y) = L.mem s (stA y) ∧
      L.mem (L.wr s b v) (blockA y) = L.mem s (blockA y) := fun y hy => ⟨stf y hy, blf y hy⟩
  have q : SchedQueuesInvX st T Cs Ω H X (L.wr s b v) Q R := by
    refine inv_of_agree h hw.1 hw.2.1 (fun y hy => ⟨?_, ?_⟩) (fun c hc o h1 h2 _ => f3 c hc o h1 h2)
      iqf (fun y hy => F y hy _ (by simp) (by simp) (by simp))
      (fun y hy => Or.inl (F y hy _ (by simp) (by simp) (by simp))) (by rw [ea]; exact h.action) hsb
      (by rw [ea]; intro haT; rw [stf _ haT]; exact h.actOK haT)
      (h.eps.agreeE hw.1 hsb (fun y hy => ⟨?_, ?_⟩) f4)
      (by rw [show L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) layout.node.CUR_THREAD) =
          L.curW (L.wr s b v) from rfl, ec]; exact h.curT)
      (by rw [show L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) layout.node.IDLE_THREAD) =
          L.idleW (L.wr s b v) from rfl, ei]; exact h.idleT)
    · rw [nextA_eq']; exact F y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
    · rw [prevA_eq']; exact F y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
    · rw [nextA_eq']; exact F y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
    · rw [prevA_eq']; exact F y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  obtain ⟨hrΩ, hcΩ⟩ := objs_omega hX.1.1 hSg.sub
  have rpf : ∀ y ∈ T, L.mem (L.wr s b v) (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp)
  have tm : TmFr st T Cs Nt s (L.wr s b v) :=
    TmFr.mk0 ⟨hw.1, fun y hy K k1 k2 k3 => f1 y hy K (by omega) (by omega) k3,
      fun c hc o ho => f3 c hc o (by omega) (by omega), fun n hn => f2 _ (hSg.sub _ (hX.1.1.ntB n hn).2)⟩
  have hX0 := hX.1
  have x0 : XInv0 st T Cs Ω Sg Rp Scs Nt Z (L.wr s b v) :=
    hX0.keep (fun r hr => ⟨f2 _ (hrΩ r hr).1, f2 _ (hrΩ r hr).2.1, f2 _ (hrΩ r hr).2.2⟩)
      (fun c hc => ⟨f2 _ (hcΩ c hc).1, f2 _ (hcΩ c hc).2.1⟩) scf rpf stf (by rw [ecs]; exact hX0.2.2.cur)
      (fun c hc => f2 _ (hSg.sub _ (hX0.1.repW c hc)))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun n hn => f2 _ (hSg.sub _ (hX0.1.ntW n hn)))
      ⟨hX0.2.2.tm.tmfr tm, hX0.2.2.ntb.tmfr tm, hX0.2.2.rb.tmfr tm, tm.2.2.2.1⟩
      (fun c hc => f2 _ (hSg.sub _ (hX0.1.snW c hc)))
      (fun y hy => F y hy _ (by simp) (by simp) (by simp)) (fun c hc => f2 _ (hSg.sub _ (hX0.1.syW c hc)))
      (fun c hc => f2 _ (hcΩ c hc).2.2.1) ei
  have xw : XInvW st T Cs Ω Sg Rp Scs Nt Z d (L.wr s b v) :=
    ⟨x0, hX.2.1.keep hX0.2.2.yt.1 (fun c hc => f2 _ (hSg.sub _ (hX0.1.fixW c hc).1)) scf,
      hX.2.2.keep (fun t ht _ h0 => (hX0.2.2.bound t ht h0).1) (fun t ht _ => scf t ht)
        (fun c hc => f2 _ (hSg.sub _ (hX0.1.fixW c hc).2))
        (fun t ht _ => by rw [affA_eq]; exact F t ht _ (by simp) (by simp) (by simp))⟩
  have sig : ∀ x ∈ Sg, L.mem (L.wr s b v) x = L.mem s x := fun x hx => f2 x (hSg.sub x hx)
  have hS' : SCsOK st T Ω Sg Scs Z Ac (L.wr s b v) := by
    refine ⟨hS.sub, fun x hx => by rw [hw.1]; exact hS.ks x hx, fun o h1 h2 => by rw [hw.1]; exact hS.ksΩ o h1 h2,
      fun t ht hb' hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax (L.wr s b v) c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h0 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h0), hS.spSg,
      fun c hc h0 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h0), hS.repSg,
      fun c hc => by rw [hw.1]; exact hS.scKs c hc⟩
    rw [scf t ht] at hb' hne ⊢; rw [ecs] at hne ⊢; exact hS.disj t ht hb' hne
  exact ⟨q, hB.keep scf iqf ea ec ei stf h.curT h.idleT, xw, hS',
    ⟨hSg.sub, fun x hx => by rw [hw.1]; exact hSg.ks x hx, fun o h1 h2 => by rw [hw.1]; exact hSg.ksΩ o h1 h2⟩,
    tm, F, f2, f3, ea⟩

/-- **`migrate_tail` for a thread that may run a VCPU** (no `hrv`): when `RUN_VCPU ≠ 0`, the run VCPU's
`OWNER_CPU` word is a user word (`hpo`, [P] at the caller), and its write keeps `BlkOKW` (`blkW_wrU`). -/
theorem migrate_tail_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {X : Set U64} (s8 : S) (a : A)
    (sc dst cpu : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h8 : SchedQueuesInvX st T Cs Ω H X s8 Q R) (hB8 : BoundInv st T Ac s8) (hX8 : XInvW st T Cs Ω Sg Rp Scs Nt Z dst s8)
    (hS8 : SCsOK st T Ω Sg Scs Z Ac s8) (hSg8 : SgOK st Ω Sg s8) (hto : dst ∈ T)
    (htq : (L.mem s8 (inqA dst) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s8 (inqA dst) &&& sched.Q_RELEASE) = 0#u64)
    (hc' : cpu ∈ Cs) (hsc : sc ∈ Scs)
    (hcore : L.mem s8 (scA dst) ≠ 0#u64 → L.mem s8 (scCoreA (L.mem s8 (scA dst))) = cpu)
    (hpo : L.mem s8 (runVcpuA dst) ≠ 0#u64 →
      UserOK st T Cs Ω H {x | x = ownA (L.mem s8 (runVcpuA dst))} s8) :
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
      have hU1 : UserOK st T Cs Ω H {x | x = ownA (L.mem s1 (runVcpuA dst))} s1 := by
        rw [rv1]; exact (hpo (by rw [← rv1]; exact hnz)).ksb w1.1
      obtain ⟨q1', hB1', hX1', hS1', hSg1', tm1, F1, O1, -, ea1⟩ := blkW_wrU (v := core.num.U64.wrapping_add cpu 1#u64)
        q1 hB1 hX1 hS1 hSg1 hU1
      have scf : L.mem (L.wr s1 (ownA (L.mem s1 (runVcpuA dst))) (core.num.U64.wrapping_add cpu 1#u64)) (scA dst) =
          L.mem s1 (scA dst) := by rw [scA_eq]; exact F1 dst hto _ (by simp) (by simp) (by simp)
      refine tail _ a4 Q1 R1 q1' hB1' hX1' hS1' hSg1'
        (fun y hy => by rw [stA_eq, F1 y hy _ (by simp) (by simp) (by simp), ← stA_eq]; exact st1 y hy)
        (fun y hy => (F1 y hy _ (by simp) (by simp) (by simp)).trans (rp1 y hy)) (m1.trans tm1)
        (scf.trans sc1) ((O1 _ hm).trans t1) (ea1.trans a1)
        (by rw [inqA_eq, F1 dst hto _ (by simp) (by simp) (by simp), ← inqA_eq]; exact iq1) fun h0' => ?_
      rw [scf] at h0' ⊢
      rw [O1 _ (hSg1.sub _ (hX1.1.1.fixW _ (hX1.1.2.2.bound dst hto h0').1).2)]
      exact hcore1 h0'
  · rename_i hne
    have e : af = cpu := UScalar.eq_of_val_eq (by simpa using hne)
    have hX : XInv st T Cs Ω Sg Rp Scs Nt Z s8 :=
      hX8.1.x hX8.2.1 (hX8.2.2.full fun _ h0' => by rw [hcore h0', ← eaf, e])
    try simp only [Aeneas.Std.bind_ok]
    exact (WP.spec_ok _).2 ⟨⟨⟨Q, R, h8⟩, hB8, hX, hS8, hSg8⟩, fun _ _ => rfl, fun _ _ => rfl, TmFr.refl (L := L) _,
      rfl, rfl, rfl⟩

/-- **`migrate_tcb` as a frame, for a thread that may run a VCPU**: the thread's affinity, the debug-list
words and, when `RUN_VCPU ≠ 0`, its run VCPU's `OWNER_CPU` word (in the user words `U`, `hpo`). -/
theorem smp.migrate_tcb.frame_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) (hU : UserOK st T Cs Ω H U s)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → ownA (L.mem s (runVcpuA t)) ∈ U) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => WritesIn st s s' (fun b => b = affA t ∨ DbgW st T Cs s b ∨ b ∈ U) ∧
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
    have tail : ∀ (s1' : S) (a4 : A), WritesIn st s s1' (fun b => DbgW st T Cs s b ∨ b ∈ U) →
        DbgTz st T Cs s1' →
        (do
          let s3 ← obj.Tcb.set_affinity st t s1' cpu
          let s4 ← objects.debug_append st s3 t
          ok (s4, a4)) ⦃ s' _ => WritesIn st s s' (fun b => b = affA t ∨ DbgW st T Cs s b ∨ b ∈ U) ∧
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
      have w2 : WritesIn st s (L.wr s1 (affA t) cpu) (fun b => b = affA t ∨ DbgW st T Cs s b ∨ b ∈ U) :=
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
      have hu : ownA (L.mem s1 (runVcpuA t)) ∈ U := by rw [rv1]; exact hpo (by rw [← rv1]; exact hnz)
      have ho := (hU _ hu).1.ksb w1.1
      refine tail _ a4 ((w1.trans (writesIn_wr ho.1)).mono fun b hb => ?_)
        (DbgTz.wr_out hT (fun c hc' => (hN c hc').ksb w1.1) ho.1 (notDbgW_out hT (fun c hc' => (hN c hc').ksb w1.1) ho) D1)
      rcases hb with hb | rfl
      · exact Or.inl hb
      · exact Or.inr hu
  · try simp only [Aeneas.Std.bind_ok]
    exact (WP.spec_ok _).2 ⟨WritesIn.refl _ _, hD, fun _ => rfl⟩

/-- `migrate_tcb.kw` for a thread that may run a VCPU: `FootDU` with the user words `U`. -/
theorem smp.migrate_tcb.kw_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t cpu : U64) (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) (hD : DbgTz st T Cs s)
    (hc : L.mem s (affA t) ∈ Cs) (hcpu : cpu ∈ Cs) (ht : t ∈ T) (hU : UserOK st T Cs Ω H U s)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → ownA (L.mem s (runVcpuA t)) ∈ U) :
    smp.migrate_tcb st ar s a t cpu ⦃ s' _ => FootDU st T Cs Sg Scs Z Es U s s' ⦄ :=
  WP.spec_mono (smp.migrate_tcb.frame_f hA s a t cpu hT hN hD hc hcpu ht hU hpo) fun _ hr => by
    obtain ⟨w, -⟩ := hr
    exact w.mono fun b hb => by
      rcases hb with e | hb | hb
      · exact Or.inl (Or.inl (by rw [e, affA_eq]; exact kw_field ht (by simp) (by simp) (by simp)))
      · exact Or.inl (Or.inr hb)
      · exact Or.inr hb

/-- **`bind_tcb` with its footprint, for a thread that may run a VCPU** (`bind_tcb.blkF` without `hrv`): the
footprint also holds the run VCPU's `OWNER_CPU` word, a user word (`hpo`). -/
theorem schedcontext.bind_tcb.blkF_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (sc t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac)
    (hU : UserOK st T Cs Ω H U s)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → ownA (L.mem s (runVcpuA t)) ∈ U) :
    schedcontext.bind_tcb st ar s a sc t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootDU st T Cs Sg Scs Z Es U s s' ⦄ := by
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
  have hU2 : UserOK st T Cs Ω H U s2 := hU.ksb k2s
  have hpo2 : L.mem s2 (runVcpuA t) ≠ 0#u64 → ownA (L.mem s2 (runVcpuA t)) ∈ U := fun hnz => by
    rw [rv2]; exact hpo (by rw [← rv2]; exact hnz)
  have hpoU : L.mem s2 (runVcpuA t) ≠ 0#u64 →
      UserOK st T Cs Ω H {x | x = ownA (L.mem s2 (runVcpuA t))} s2 := fun hnz x hx => by
    rw [Set.mem_setOf_eq] at hx; subst hx; exact hU2 _ (hpo2 hnz)
  step with obj.Sc.cpu.spec as ⟨cpu, ecpu⟩
  have hc' : cpu ∈ Cs := by rw [ecpu, core2]; exact hcore
  refine WP.spec_bind (WP.spec_and (migrate_tail_f hA s2 a sc t cpu Q R h2 hB2 hX2 hS2 hSg2 ht (by rw [iq2]; exact htq)
    (by rw [iq2]; exact htr) hc' hsc (fun _ => by rw [sc2, ecpu]) hpoU) (smp.migrate_tcb.kw_f (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) (Cs := Cs)
      hA s2 a t cpu h2.tcbs h2.nodes ⟨hX2.1.2.2.tm.dn, hX2.1.2.2.tm.dp, hX2.1.2.2.tm.dh⟩ (h2.aff t ht) hc' ht hU2 hpo2)) ?_
  rintro ⟨s3, a1⟩ ⟨⟨⟨⟨Q3, R3, h3⟩, hB3, hX3, hS3, hSg3⟩, -, -, -, sc3, -, ea3⟩, fw3⟩
  try simp only [WP.uncurry'_pair]
  rw [sc2] at sc3
  have fw3' : FootDU st T Cs Sg Scs Z Es U s s3 := fw2.d.u.trans fw3
  -- the sporadic unblock check
  step with sporadic.sc_sporadic.spec as ⟨b, eb⟩
  refine WP.spec_bind (Pₘ := fun s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
      L.actionW s4 = L.actionW s ∧ FootDU st T Cs Sg Scs Z Es U s s4) ?_ ?_
  · have ok3 : (ok s3 : Result S) ⦃ s4 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ L.mem s4 (scA t) = sc ∧
        L.actionW s4 = L.actionW s ∧ FootDU st T Cs Sg Scs Z Es U s s4 ⦄ :=
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
  have fw5' : FootDU st T Cs Sg Scs Z Es U s s5 := fw4.trans fw5.d.u
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
theorem sc_bind_tcb.blkF_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (ct sc t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac)
    (hU : UserOK st T Cs Ω H U s)
    (hpo : L.mem s (runVcpuA t) ≠ 0#u64 → ownA (L.mem s (runVcpuA t)) ∈ U) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.bind_tcb st ar s2 a sc t
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ FootDU st T Cs Sg Scs Z ∅ U s s' ⦄ := by
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
  refine WP.spec_bind (schedcontext.bind_tcb.blkF_f (Es := ∅) hA s2 a sc t h2 ht hsc hsc0 (by rw [k2.scf ht]; exact ht0)
    (by rw [(k2.fix sc hsc).1]; exact hc0) hbA2
    (hU.ksb k2.ksb) (fun hnz => by rw [rv2]; exact hpo (by rw [← rv2]; exact hnz))) ?_
  rintro ⟨s3, a2⟩ ⟨h3, f3⟩
  try simp only [WP.uncurry'_pair]
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h3, f2.d.u.trans f3⟩


/-! ## The decode -/

theorem KODU.trans {s0 s s' : S} (h : WritesIn st s0 s (KO st T Cs Ω H Sg Scs Z s0))
    (hw : WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U)) :
    WritesIn st s0 s' (fun b => KOD st T Cs Ω H Sg Scs Z s0 b ∨ b ∈ U) :=
  (h.trans hw).mono fun _ hb => by
    rcases hb with hb | hb
    · exact Or.inl (Or.inl hb)
    rcases hb with hb | hu
    · rcases hb with hb | hb
      · exact Or.inl (Or.inl (KO.ksb h.1 hb))
      · exact Or.inl (Or.inr (DbgW.ksb h.1 hb))
    · exact Or.inr hu

theorem FootDU.kodu {s s' : S} {Es : Set U64} (f : FootDU st T Cs Sg Scs Z Es U s s') (hE : Es ⊆ EH H) :
    WritesIn st s s' (fun b => KOD st T Cs Ω H Sg Scs Z s b ∨ b ∈ U) :=
  WritesIn.mono f fun _ hb => hb.elim (fun hb => Or.inl (hb.elim (fun hb => Or.inl (Or.inl (KW.mono hb hE))) Or.inr))
    Or.inr

/-- **[P] (a64) `ScBindOwn`**: at a decode (`DecPre`), the `OWNER_CPU` word of the VCPU a thread runs
(`RUN_VCPU ≠ 0`) is a user word (`∈ U`). Placement, like VcpuCheckInv's [P] `hpw` (the run VCPU's
`RUN_CALLER` word in `U`): a VCPU is a heap object of its own, and P1 gives no `UsrW` for its words. It
replaces QueueDecSc's [J] `ScBindRv`, which is false (module docstring). -/
def ScBindOwn (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) : Prop :=
  ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra →
    ∀ t ∈ T, L.mem s (runVcpuA t) ≠ 0#u64 → ownA (L.mem s (runVcpuA t)) ∈ U

/-- `sc_bind_stall.blk` without `hrv`: the target may run a VCPU, whose `OWNER_CPU` word is a user word
(`hpo`); the footprint also holds the user words `U`. -/
theorem sc_bind_stall.blk_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s1 : S) (a1 : A)
    (ct sc ptr : U64) (h1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hct : ct ∈ T)
    (run1 : Runnable (L.mem s1 (stA ct))) (hpT : ptr ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (z2 : L.mem s1 (scA ptr) = 0#u64) (z1 : L.mem s1 (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s1 (stA ptr)) → sc ∈ Ac) (hU : UserOK st T Cs Ω H U s1)
    (hpo : L.mem s1 (runVcpuA ptr) ≠ 0#u64 → ownA (L.mem s1 (runVcpuA ptr)) ∈ U)
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
  refine WP.spec_mono (sc_bind_tcb.blkF_f hA s2 a2 ct sc ptr h2.blk hct
    (by rw [stA_eq, f2 _ hct _ (by simp) (by simp), ← stA_eq]; exact run1) hpT hsc hsc0
    (by rw [scA_eq, f2 _ hpT _ (by simp) (by simp), ← scA_eq]; exact z2)
    (by rw [o2 _ hscO]; exact z1)
    (fun hb => hbA (by rw [stA_eq, ← f2 _ hpT _ (by simp) (by simp), ← stA_eq]; exact hb))
    (hU.ksb w2.1) (fun hnz => by rw [rv2] at hnz ⊢; exact hpo hnz)) fun r hr => ?_
  obtain ⟨r', s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨hr.1, hr.2.1, KODU.trans (w2.mono fun _ hb => NodeW.ko h1.1.choose_spec.choose_spec.cur hb)
    (FootDU.kodu hr.2.2 (Set.empty_subset _))⟩

set_option maxHeartbeats 800000 in
/-- **`schedcontext.decode`** keeps the invariants, `schedcontext.decode.dec` with the named premise
**[P] `BO`** (`ScBindOwn`) in place of the false [J] `ScBindRv`; the footprint also holds the user words. -/
theorem schedcontext.decode.dec_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (BO : ScBindOwn st T Cs Ω H Sg Rp Scs Nt Z U)
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
        refine WP.spec_mono (sc_bind_stall.blk_f hA s1 a1 _ sc ptr h1 hct run1 hpT hsc hsc0 z2 z1 hbA hU1
          -- a64: the target's run VCPU's `OWNER_CPU` word is a user word ([P] `ScBindOwn`)
          (fun hnz => by rw [rv1] at hnz ⊢; exact BO Ac s _ extra D ptr hpT hnz)
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

/-- **InvGaps' `schedContext`, discharged** but for the named `ScYieldGap` and (a64) **[P] `ScBindOwn`**. -/
theorem decGap_sc_f {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U)
    (BO : ScBindOwn st T Cs Ω H Sg Rp Scs Nt Z U) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedContext := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  rename_i sc b
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact WP.spec_mono (schedcontext.decode.dec_f hA E Y BO s a lbl sc call extra b D hE) fun _ hr => hr.1

/-- `InvGaps2` with **[P] `scBindOwn`** (`ScBindOwn`) in place of the false [J] `scBindRv`. -/
structure InvGaps2F (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (Adm : PSets → Prop) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  untyped : DecGapG st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok .untyped
  reply : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .reply
  thread : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread
  irqControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqControl
  irqHandler : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .irqHandler
  schedControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .schedControl
  vspace : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vspace
  vcpu : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .vcpu
  ept : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ept
  ioPortControl : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPortControl
  ioPort : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ioPort
  /-- SchedContext `YieldTo`. -/
  yield : ScYieldGap st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- CNode `Delete` and `Revoke`. -/
  cnode : CnodeGaps st ar T Cs Ω H Sg Rp Scs Nt Z U
  /-- **[P] (a64)** At a decode the `OWNER_CPU` word of a running VCPU is a user word (`ScBindOwn`). -/
  scBindOwn : ScBindOwn st T Cs Ω H Sg Rp Scs Nt Z U

theorem InvGaps2F.gaps {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (G : InvGaps2F st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok) : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok :=
  ⟨G.untyped, G.reply, decGap_cnode C G.cnode, G.thread, G.irqControl, G.irqHandler, decGap_domain hA,
    decGap_sc_f hA E G.yield G.scBindOwn, G.schedControl, G.vspace, G.vcpu, G.ept, G.ioPortControl, G.ioPort,
    decGap_tdx hA E⟩

end

end Fl4ProofsA64.P1
