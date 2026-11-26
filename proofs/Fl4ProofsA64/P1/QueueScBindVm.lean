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
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64} {Es : Set U64}

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

end

end Fl4ProofsA64.P1
