/-
P1 (issue #16, g7b): **the SchedContext and SchedControl decodes with the
footprint `Foot`** (P1's `KW`, no debug-list word), for the P3 premise
`ScStepP1` (XTopJointKEntryU4's `JSchedCtxPathU4.rest` / `JSchedCPathU4.rest`,
INV-PLAN §1.U3L C9 / C14).

P1's `schedcontext.decode.dec` has the frame `KOD` (the debug-list words
too): Bind of a thread moves it to its SC's core (`smp.migrate_tcb`), and P1's
`decode_sched_control.dec` has no frame. When every thread already sits on
the SC's core (at `JAtZ`: `SchedRel`'s one core, every TCB's affinity and
every SC's core the current core), `migrate_tcb` is a no-op
(`smp.migrate_tcb.frame`) and no debug-list word is written:

* `schedcontext.decode.footK`: Consumed, Bind and UnbindObject (the labels
  of `ScJLabel`) keep `BlkOK` (some active set) and write within `Foot`;
  Bind of a thread through XTopJointTcbSsp's `bind_tcb.blkK`, Consumed
  without P1's `XferHyps` (`set_consumed.blk`; the state word kept by
  `set_consumed.rg`).
* `schedcontext.decode_sched_control.footK`: ConfigureFlags, the configured
  SC's thread on the core `cpu` (`cfAK`, `cfDK`, `configure_flags.blkK`: P1's
  `cfA` / `cfD` / `configure_flags.blk` with the footprint and the thread's
  affinity carried to the migration).
-/
import Fl4Proofs.P3.XTopJointTcbSsp
import Fl4Proofs.P1.QueueDeadYield
import Fl4Proofs.P1.QueueSchedCtl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- `RgWd` writes keep the TCBs' state words. -/
theorem rgw_keepSt {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hw : WritesIn st s s' (RgWd T Ω)) :
    ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) := by
  have hT := h.tcbs
  intro y hy
  rw [stA_eq]
  refine hw.mem_eq (field_aligned (K := 3328#u64) (hT y hy) (by simp) (by simp)) fun hb => ?_
  rcases hb with hm | ⟨z, hz, K, hK1, hK2, -, e⟩
  · exact out_ne_field (h.omega _ hm) hy (hT y hy) (K := 3328#u64) (by simp) rfl
  · exact field_ne (hT y hy) (hT z hz) (K1 := 3328#u64) (by simp) (by omega)
      (fun _ => by have : (3328#u64).val = 3328 := rfl; omega) e

/-- **SchedContext `Bind` (thread) with the footprint `Foot`**: P1's
`sc_bind_tcb.blkF` with `bind_tcb.blkK` (the thread already on the SC's
core). -/
theorem sc_bind_tcb.blkK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (ct sc t : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hct : ct ∈ T) (hr : Runnable (L.mem s (stA ct)))
    (ht : t ∈ T) (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (ht0 : L.mem s (scA t) = 0#u64) (hc0 : L.mem s (scTcbA sc) = 0#u64)
    (hbA : BlockedR (L.mem s (stA t)) → sc ∈ Ac) (haff : L.mem s (affA t) = L.mem s (scCoreA sc)) :
    (do
      let s2 ← sched.set_thread_state st s ct sched.TS_RESTART
      let (s3, a2) ← schedcontext.bind_tcb st ar s2 a sc t
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r s' _ =>
      r = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
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
  have haff2 : L.mem s2 (affA t) = L.mem s2 (scCoreA sc) := by
    rw [(k2.fix sc hsc).2.1, affA, k2.fld t ht _ (by simp) (by simp) (by simp) (by simp)
      (fun _ => ⟨by simp, by simp⟩)]
    exact haff
  refine WP.spec_bind (schedcontext.bind_tcb.blkK (Es := ∅) hA s2 a sc t h2 ht hsc hsc0 (by rw [k2.scf ht]; exact ht0)
    (by rw [(k2.fix sc hsc).1]; exact hc0) hbA2 haff2) ?_
  rintro ⟨s3, a2⟩ ⟨h3, f3⟩
  try simp only [WP.uncurry'_pair]
  exact (WP.spec_ok _).2 ⟨by first | trivial | rfl, h3, f2.trans f3⟩

/-- `bind_ntfn` writes two fixed words (`Sg`). -/
theorem schedcontext.bind_ntfn.foot (s : S) (c n : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : c ∈ Scs) (hn : n ∈ Nt) :
    schedcontext.bind_ntfn st s c n ⦃ s' => Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold schedcontext.bind_ntfn
  refine WP.spec_bind (obj.Ntfn.set_sc.wr s n c) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (obj.Sc.set_ntfn.wr _ c n) fun s2 e2 => ?_
  subst e2
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have alA : Aligned (ntfnScA n) := hO.ntAl n hn
  have alB : Aligned (scNtfnA c) := (h0.omega _ (hSg.sub _ (hO.snW c hc))).1
  refine ((writesIn_wr alA).trans (writesIn_wr alB)).mono fun b hb => ?_
  rcases hb with rfl | rfl
  · exact kw_sg (hO.ntW n hn)
  · exact kw_sg (hO.snW c hc)

/-- P1's `extra_cap.gen` from the first extra slot alone. -/
theorem schedcontext.extra_cap.gen0 {s : S} {extra : Aeneas.Std.Array obj.Slot 3#usize} {P : capability.Cap → Prop}
    (hx : ∀ sl, Aeneas.Std.Array.index_usize extra 0#usize = Result.ok sl → sl ≠ 0#u64 → obj.Slot.cap st sl s ⦃ c => P c ⦄) :
    schedcontext.extra_cap st s extra 0#usize ⦃ o => ∀ c, o = some c → P c ⦄ := by
  unfold schedcontext.extra_cap
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  split
  · simp_all
  refine WP.spec_bind (spec_eqv (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0)) fun sl hsl => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp
  rename_i h0
  refine WP.spec_bind (hx sl hsl.1 (by simpa using h0)) fun c hc => ?_
  exact (WP.spec_ok _).2 fun c' e => by cases e; exact hc

/-- The extra-cap facts the SchedContext decodes read: a notification cap
names a notification, a thread cap a thread. -/
def ScExtraOK (T Nt : Set U64) (c : capability.Cap) : Prop :=
  (∀ p x y z, c = capability.Cap.Notification p x y z → p ∈ Nt) ∧ (∀ p, c = capability.Cap.Thread p → p ∈ T)

set_option maxHeartbeats 8000000 in
/-- **`schedcontext.decode` with the footprint `Foot`** for Consumed, Bind
and UnbindObject (module docstring). -/
theorem schedcontext.decode.footK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (s : S) (a : A) (lbl sc : U64) (call : Bool) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hbk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hlbl : lbl = fl4_abi.label.SchedContextConsumed ∨ lbl = fl4_abi.label.SchedContextBind ∨
      lbl = fl4_abi.label.SchedContextUnbindObject)
    (hsc : sc ∈ Scs) (hsc0 : sc ≠ 0#u64)
    (hidle : L.mem s (scTcbA sc) ≠ 0#u64 → L.mem s (scTcbA sc) ≠ L.idleW s)
    (hrun : Runnable (L.mem s (stA (L.curW s)))) (hact : L.actionW s = 0#u64)
    (hx : ∀ s', WritesIn st s s' (NodeW st s) → ∀ sl, Aeneas.Std.Array.index_usize extra 0#usize = ok sl →
      sl ≠ 0#u64 → obj.Slot.cap st sl s' ⦃ c => ScExtraOK T Nt c ⦄)
    (haff : ∀ t ∈ T, L.mem s (affA t) = L.mem s (scCoreA sc)) :
    schedcontext.decode st ar s a lbl sc call extra ⦃ r s' _ =>
      (∃ Ac', BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' s') ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h := BlkOK.bxi hbk
  have hcur : L.cpu s ∈ Cs := h.1.choose_spec.choose_spec.cur
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
  have W1 : Foot st T Cs Sg Scs Z ∅ s s1 := Foot.of w1 fun _ ⟨o, ho, h88, e⟩ => e ▸ kw_node hcur ho h88
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hO := h.2.2.1.1
  have hsub := h.2.2.2.1.sub
  have run1 : Runnable (L.mem s1 (stA (L.curW s))) := by
    rw [stA_eq, f1 _ hct _ (by simp) (by simp), ← stA_eq]; exact hrun
  have act1 : L.actionW s1 = 0#u64 := ea1.trans hact
  have idle1 : L.mem s1 (scTcbA sc) ≠ 0#u64 → L.mem s1 (scTcbA sc) ≠ L.idleW s1 := by
    rw [o1 _ (hsub _ (hO.fixW sc hsc).1), ei1]; exact hidle
  have aff1 : ∀ t ∈ T, L.mem s1 (affA t) = L.mem s1 (scCoreA sc) := fun t ht => by
    rw [o1 _ ((objs_omega hO hsub).2 sc hsc).2.1, affA, f1 t ht _ (by simp) (by simp)]; exact haff t ht
  have hx1 := hx s1 w1
  have Er : ∀ e : error.SysError, (ok ((core.result.Result.Err (error.Exc.Sys e) : core.result.Result Unit error.Exc),
      s1, a1) : Result _) ⦃ r s' _ => (∃ Ac', BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' s') ∧
        Foot st T Cs Sg Scs Z ∅ s s' ⦄ := fun e =>
    (WP.spec_ok _).2 ⟨⟨Ac, h1.blk⟩, W1⟩
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = L.curW s := ect.trans ec1
  subst ect'
  simp only [error.illegal, error.truncated, error.invalid_cap, bind_ok]
  split
  · -- Consumed
    refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s1 _ h1.blk hct (runnable_ok run1).1
      (runnable_ok run1).2) fun s2 ⟨h2, f2, e2, k2⟩ => ?_
    refine WP.spec_bind (WP.spec_and (schedcontext.set_consumed.blk hA s2 a1 sc (L.curW s) call h2 hsc hct)
      (schedcontext.set_consumed.rg hA s2 a1 sc (L.curW s) call h2 hsc hct)) fun s3 ⟨⟨h3, f3, _⟩, w3⟩ => ?_
    have hst : L.mem s3 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [rgw_keepSt h2.1.choose_spec.choose_spec w3 _ hct, e2]
    refine WP.spec_bind (WP.spec_and (sched.set_thread_state.running_bxi (BlkOK.bxi h3) hct hst)
      (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 _ _
        h3.1.choose_spec.choose_spec hct)) fun s4 ⟨h4, f4⟩ => ?_
    exact (WP.spec_ok _).2 ⟨⟨Ac, h4.blk⟩, W1.trans (f2.trans (f3.trans f4))⟩
  split
  · -- Bind
    refine WP.spec_bind (schedcontext.extra_cap.gen0 (fun sl hsl h0 => hx1 sl hsl h0)) fun o ho => ?_
    rcases o with _ | c
    · exact Er _
    have hcO := ho c rfl
    cases c
    all_goals first | exact Er _ | skip
    · -- a notification
      rename_i ptr _ _ _
      have hpN := hcO.1 ptr _ _ _ rfl
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
        (schedcontext.bind_ntfn.foot s2 sc ptr h2 hsc hpN)) fun s3 ⟨h3, f3⟩ => ?_
      exact (WP.spec_ok _).2 ⟨⟨Ac, h3⟩, W1.trans (f2.trans f3)⟩
    · -- a thread
      rename_i ptr
      have hpT : ptr ∈ T := hcO.2 ptr rfl
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
      have fin : (BlockedR (L.mem s1 (stA ptr)) → sc ∈ Ac) →
          (do
            let s2 ← sched.set_thread_state st s1 (L.curW s) sched.TS_RESTART
            let (s3, a2) ← schedcontext.bind_tcb st ar s2 a1 sc ptr
            ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s3, a2)) ⦃ r s' _ =>
              (∃ Ac', BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' s') ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := fun hbA =>
        WP.spec_mono (sc_bind_tcb.blkK hA s1 a1 _ sc ptr h1.blk hct run1 hpT hsc hsc0 z2 z1 hbA (aff1 ptr hpT))
          fun r hr => by
            obtain ⟨r', s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨⟨Ac, hr.2.1⟩, W1.trans hr.2.2⟩
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
    refine WP.spec_bind (schedcontext.extra_cap.gen0 (fun sl hsl h0 => hx1 sl hsl h0)) fun o ho => ?_
    rcases o with _ | c
    · exact Er _
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
        exact ⟨⟨Ac, hr.2.1⟩, W1.trans hr.2.2.1⟩
    · rename_i ptr
      dsimp only
      refine WP.spec_bind (obj.Sc.tcb.spec s1 sc) fun i1 ei1 => ?_
      split
      · exact Er _
      split
      · exact Er _
      exact WP.spec_mono (sc_unbind_tcb.blkF s1 a1 _ sc h1.blk hct run1 hsc hsc0
        (fun hz e => hz (by rw [← e, act1])) (fun hz => Ne.symm (idle1 hz))) fun r hr => by
        obtain ⟨r', s', a'⟩ := r
        simp only [WP.uncurry'_pair] at hr ⊢
        exact ⟨⟨Ac, hr.2.1⟩, W1.trans hr.2.2.1⟩
  exfalso
  rcases hlbl with e | e | e <;> contradiction

/-! ## SchedControl ConfigureFlags with the footprint -/

/-- An SC word write (`CORE`, `BADGE`, `SPORADIC`): in `Foot`, and every
TCB's affinity kept. -/
theorem scw_foot {c a v : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs)
    (ha : a.val = c.val + 16 ∨ a.val = c.val + 48 ∨ a.val = c.val + 64) :
    Foot st T Cs Sg Scs Z ∅ s (L.wr s a v) ∧ ∀ y ∈ T, L.mem (L.wr s a v) (affA y) = L.mem s (affA y) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, hfit⟩ := sc_lo hP hz
  have hal : Aligned a := by unfold Aligned; omega
  have hin : InSC c (Z c) a := ⟨by omega, by omega⟩
  refine ⟨foot_wr hal (kw_sc hc hin), fun y hy => ?_⟩
  have hΩ := hO.scW c hc a hal hin
  exact L.mem_wr_ne hal (field_aligned (K := 3520#u64) (h0.tcbs y hy) (by simp) (by simp))
    (fun e => out_ne_field (h0.omega _ hΩ) hy (h0.tcbs y hy) (K := 3520#u64) (by simp) e.symm)

/-- `commit_time` writes within `Foot` (the current SC's ring and
`CONSUMED` word, the node's `CONSUMED` word). -/
theorem sched.commit_time.foot {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.commit_time st ar s a ⦃ s' => Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  have hc : L.cscW s ∈ Scs := hX.2.2.cur
  have hN' := h0.nodes _ h0.cur
  obtain ⟨hP, hz⟩ := hO.sc _ hc
  have cnv : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
  have aC : Aligned (L.nodeA s layout.node.CONSUMED) := nodeAt_aligned hN' (by rw [cnv]; omega) (by rw [cnv])
  have oC : Outside (L.nodeA s layout.node.CONSUMED) (L.cscW s) (Z (L.cscW s)) :=
    node_out_place (fun b hb hin => hO.scW _ hc b hb hin) h0.omega h0.cur hN' (by rw [cnv]; omega) (by rw [cnv])
  refine WP.spec_mono (sched.commit_time.fr hA a (hS.all _ hc).1 rfl aC oC) fun s' hw => Foot.of hw.1 fun b hb => ?_
  rcases hb with (hh | rfl) | rfl
  · exact kw_sc hc hh.inSC
  · obtain ⟨-, h128, -⟩ := sc_lo hP hz
    have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
    exact kw_sc hc ⟨by rw [hv]; simp, by rw [hv]; simp [layout.sc.CONSUMED]; omega⟩
  · exact kw_node h0.cur (by rw [cnv]; omega) (by rw [cnv]; omega)

theorem smp.remote_reschedule.foot {A : Type _} {ar : machine.Arch A} (a : A) (cpu : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    smp.remote_reschedule st ar s a cpu ⦃ s' _ => Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have hc := h.1.choose_spec.choose_spec.cur
  have hN := h.1.choose_spec.choose_spec.nodes _ hc
  unfold smp.remote_reschedule
  step with LawfulStore.cur_cpu_spec as ⟨i, ei⟩
  subst ei
  split
  · step with obj.node_get.spec as ⟨i1, _⟩
    try simp only [lift, bind_ok]
    step as ⟨i3, _⟩
    try simp only [lift, bind_ok]
    refine WP.spec_bind (obj.node_set.spec s _ _ _) fun s1 e1 => ?_
    subst e1
    simp only [WP.spec_ok, WP.uncurry'_pair]
    exact foot_node hN hc (by rw [ipi_val]; omega) (by rw [ipi_val]) (by rw [ipi_val]; omega)
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact Foot.refl _

theorem sched.set_reprogram_on.foot (cpu : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : cpu ∈ Cs) :
    sched.set_reprogram_on st s cpu ⦃ s' => Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  unfold sched.set_reprogram_on
  refine WP.spec_mono (obj.node_set.spec s cpu _ _) fun s' e => ?_
  subst e
  exact foot_node (h.1.choose_spec.choose_spec.nodes cpu hc) hc (by rw [repr_val]; omega) (by rw [repr_val])
    (by rw [repr_val]; omega)

/-- **P1's `cfA` with the footprint** and the thread's affinity kept. -/
theorem cfAK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A) (i target : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hi : i ∈ T) (hna : ∀ y ∈ T, L.actionW s ≠ y) :
    (do
      let (s2, a2) ← smp.remote_tcb_stall st ar s a i
      let s3 ← sched.release_remove st s2 i
      let s4 ← sched.dequeue st s3 i
      let s5 ← sched.cur_sc st s4
      let b1 ← obj.Sc.Insts.CoreCmpPartialEqSc.eq s5 target
      let t ← if b1 then sched.commit_time st ar s4 a2 else ok s4
      ok (t, a2)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
        (L.mem r.1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem r.1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        (∀ y ∈ T, L.actionW r.1 ≠ y) ∧ L.mem r.1 (scA i) = L.mem s (scA i) ∧ L.idleW r.1 = L.idleW s ∧
        Foot st T Cs Sg Scs Z ∅ s r.1 ∧ L.mem r.1 (affA i) = L.mem s (affA i) ⦄ := by
  have hT := h.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (WP.spec_and (smp.remote_tcb_stall.blk hA s a i h) (smp.remote_tcb_stall.spec hA s a i)) ?_
  rintro ⟨s2, a2⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨h2, fw2, ea2, -, ei2⟩, hs2⟩ := hh
  have sc2 : L.mem s2 (scA i) = L.mem s (scA i) ∧ L.mem s2 (affA i) = L.mem s (affA i) := by
    rcases hs2 with rfl | ⟨v, rfl⟩
    · exact ⟨rfl, rfl⟩
    · obtain ⟨⟨Q, R, h0⟩, -⟩ := h
      rw [scA_eq, affA]
      exact ⟨field_wr_node h0 h0.cur (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])
        hi (by simp) (by simp), field_wr_node h0 h0.cur (by simp [layout.node.IPI_PENDING])
        (by simp [layout.node.IPI_PENDING]) hi (by simp) (by simp)⟩
  obtain ⟨⟨Q2, R2, q2⟩, hB2, hX2, hS2, hSg2⟩ := h2
  have hc2 := q2.aff i hi
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.release_remove.sch s2 i Q2 R2 q2 hB2 hSg2 hi)
    (sched.release_remove.foot s2 i _ q2.tcbs hi (q2.nodes _ hc2) (q2.nodes _ q2.cur) (q2.release _ hc2)
      (q2.released i hi).1)) (sched.release_remove.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s2 i q2 hi)) ?_
  rintro s3 ⟨⟨⟨⟨⟨Q3, R3, q3⟩, hB3, f3⟩, ea3, -, -⟩, w3, iq3⟩, fw3⟩
  have af3 : L.mem s3 (affA i) = L.mem s2 (affA i) :=
    aff_qfoot q2.tcbs (q2.release _ hc2).mem (q2.nodes _ hc2) (q2.nodes _ q2.cur) hi w3 hi
  have hc3 := q3.aff i hi
  have hp3 := q3.prio i hi
  have r3 : (L.mem s3 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq3]; split
    · exact andn_qr_qr _
    · rename_i hn; exact not_not.1 hn
  refine WP.spec_bind (WP.spec_and (WP.spec_and (sched.dequeue.sch s3 i Q3 R3 q3 hB3 (hSg2.fr f3) hi)
    (sched.dequeue.foot s3 i _ q3.tcbs hi hp3 (q3.nodes _ hc3) (q3.nodes _ q3.cur) ((q3.ready _ hc3).1.rel _ hp3)
      (q3.queued i hi).1)) (sched.dequeue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s3 i q3 hi)) ?_
  rintro s4 ⟨⟨⟨⟨⟨Q4, R4, q4⟩, hB4, f4⟩, ea4, -⟩, w4, iq4⟩, fw4⟩
  have af4 : L.mem s4 (affA i) = L.mem s3 (affA i) :=
    aff_qfoot q3.tcbs ((q3.ready _ hc3).1.rel _ hp3).mem (q3.nodes _ hc3) (q3.nodes _ q3.cur) hi w4 hi
  have r4 : (L.mem s4 (inqA i) &&& sched.Q_RELEASE) = 0#u64 := by
    rw [iq4]; split
    · rw [andn_qq_qr]; exact r3
    · exact r3
  have n4 : (L.mem s4 (inqA i) &&& sched.Q_QUEUED) = 0#u64 := by
    rw [iq4]; split
    · exact andn_qq_qq _
    · rename_i hn; exact not_not.1 hn
  have h4 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s4 :=
    ⟨⟨Q4, R4, q4⟩, hB4, (hX2.fr f3).fr f4, (hS2.fr f3).fr f4, (hSg2.fr f3).fr f4⟩
  have sc4 : L.mem s4 (scA i) = L.mem s (scA i) := by rw [f4.sc i hi, f3.sc i hi, sc2.1]
  have ea : L.actionW s4 = L.actionW s := by rw [ea4, ea3, ea2]
  have ei : L.idleW s4 = L.idleW s := by
    have e4 := f4.idle; have e3 := f3.idle; rw [e4, e3, ei2]
  have fw : Foot st T Cs Sg Scs Z ∅ s s4 := fw2.trans (fw3.trans fw4)
  have af : L.mem s4 (affA i) = L.mem s (affA i) := by rw [af4, af3, sc2.2]
  step with sched.cur_sc.spec as ⟨s5, _⟩
  refine WP.spec_bind (Pₘ := fun _ => True) (by unfold obj.Sc.Insts.CoreCmpPartialEqSc.eq; simp) fun b1 _ => ?_
  refine WP.spec_bind (Pₘ := fun t5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t5 ∧ L.actionW t5 = L.actionW s4 ∧
      L.idleW t5 = L.idleW s4 ∧ (∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
        L.mem t5 (core.num.U64.wrapping_add y K) = L.mem s4 (core.num.U64.wrapping_add y K)) ∧
        Foot st T Cs Sg Scs Z ∅ s4 t5) ?_ ?_
  · split
    · exact WP.spec_mono (WP.spec_and (sched.commit_time.blk hA a2 h4) (sched.commit_time.foot hA a2 h4))
        fun t5 ⟨⟨h5, e1, _, _, e2, e3⟩, f5⟩ => ⟨h5, e1, e2, e3, f5⟩
    · exact (WP.spec_ok _).2 ⟨h4, rfl, rfl, fun _ _ _ _ _ => rfl, Foot.refl _⟩
  rintro t5 ⟨h5, ea5, ei5, fl5, f5⟩
  refine (WP.spec_ok _).2 ⟨h5, by rw [inqA_eq, fl5 i hi _ (by simp) (by simp), ← inqA_eq]; exact n4,
    by rw [inqA_eq, fl5 i hi _ (by simp) (by simp), ← inqA_eq]; exact r4,
    fun y hy => by rw [ea5, ea]; exact hna y hy,
    by rw [scA_eq, fl5 i hi _ (by simp) (by simp), ← scA_eq]; exact sc4, by rw [ei5, ei], fw.trans f5,
    by rw [affA, fl5 i hi _ (by simp) (by simp), ← affA]; exact af⟩

set_option maxHeartbeats 4000000 in
/-- **P1's `cfD` with the footprint**, the thread already on the core `cpu`
(`migrate_tcb` a no-op). -/
theorem cfDK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s3 : S) (a1 : A) (i target cpu : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (hi : i ∈ T)
    (htq : (L.mem s3 (inqA i) &&& sched.Q_QUEUED) = 0#u64) (htr : (L.mem s3 (inqA i) &&& sched.Q_RELEASE) = 0#u64)
    (hsc : L.mem s3 (scA i) = target) (ht0 : target ≠ 0#u64) (htS : target ∈ Scs) (htA : target ∈ Ac)
    (hcpu : cpu ∈ Cs) (hna : ∀ y ∈ T, L.actionW s3 ≠ y) (haff : L.mem s3 (affA i) = cpu) :
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
  ok (t1, a5)) ⦃ r => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ Foot st T Cs Sg Scs Z ∅ s3 r.1 ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  refine WP.spec_bind (WP.spec_and (migrate_tail hA s3 a1 target i cpu Q R h0 hB hX hS hSg hi htq htr hcpu htS)
    (smp.migrate_tcb.frame hA s3 a1 i cpu h0.tcbs h0.nodes ⟨hX.2.2.tm.dn, hX.2.2.tm.dp, hX.2.2.tm.dh⟩
      (h0.aff i hi) hcpu hi)) ?_
  rintro ⟨s5, a3⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨⟨⟨Q5, R5, h5⟩, hB5, hX5, hS5, hSg5⟩, -, -, -, ⟨sc5, -, ea5⟩⟩, -, -, hid⟩ := hh
  have e5 : s5 = s3 := hid haff
  have sc5' : L.mem s5 (scA i) = target := sc5.trans hsc
  have tc5 : L.mem s5 (scTcbA target) = i := by
    have := (hX5.2.2.bound i hi (by rw [sc5']; exact ht0)).2.1; rwa [sc5'] at this
  have hrs : target ≠ 0#u64 → L.mem s5 (scTcbA target) ≠ 0#u64 →
      L.mem s5 (scTcbA target) ∈ T ∧ OutsideObjs st T Cs s5 (scCoreA target) ∧ L.mem s5 (scCoreA target) ∈ Cs ∧
        L.actionW s5 ≠ L.mem s5 (scTcbA target) := fun _ _ => by
    rw [tc5]
    exact ⟨hi, h5.omega _ ((objs_omega hX5.1 hSg5.sub).2 target htS).2.1, hX5.2.2.core target htS,
      by rw [ea5]; exact hna i hi⟩
  refine WP.spec_bind (WP.spec_and (schedcontext.resume.all hA s5 a3 target Q5 R5 h5 hB5 hX5 hSg5 hS5 hrs)
    (schedcontext.resume.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) hA s5 a3 target Q5 R5 h5 hrs)) ?_
  rintro ⟨s6, a4⟩ hh
  simp only [WP.uncurry'_pair] at hh ⊢
  obtain ⟨⟨Q6, R6, h6, hB6, hX6, hSg6, f6⟩, fw6⟩ := hh
  rw [e5] at fw6
  have hS6 := hS5.fr f6
  have sc6 : L.mem s6 (scA i) = target := (f6.sc i hi).trans sc5'
  have hb6 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s6 := ⟨⟨Q6, R6, h6⟩, hB6, hX6, hS6, hSg6⟩
  step with LawfulStore.cur_cpu_spec as ⟨i1, ei1⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      Foot st T Cs Sg Scs Z ∅ s6 r.1) ?_ ?_
  · split
    · step with sched.is_runnable.spec' as ⟨b1, hb1⟩
      refine WP.spec_bind (Pₘ := fun t => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t ∧ Foot st T Cs Sg Scs Z ∅ s6 t) ?_
        fun t ht => (WP.spec_ok _).2 ht
      split
      · rename_i hb1t
        step with sched.cur_thread.spec as ⟨t1, _⟩
        step with tcb_ne.blk as ⟨b2, _⟩
        split
        · exact WP.spec_mono (WP.spec_and (sched.possible_switch_to.sch s6 i Q6 R6 h6 hB6 hSg6 hi (hb1 hb1t)
            (fun _ => by rw [sc6]; exact htA)) (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z)
              (Es := ∅) s6 i h6 hi)) fun s7 ⟨⟨⟨⟨Q7, R7, h7⟩, hB7, f7⟩, _, _⟩, fw7⟩ =>
              ⟨⟨⟨Q7, R7, h7⟩, hB7, hX6.fr f7, hS6.fr f7, hSg6.fr f7⟩, fw7⟩
        · exact (WP.spec_ok _).2 ⟨hb6, Foot.refl _⟩
      · exact (WP.spec_ok _).2 ⟨hb6, Foot.refl _⟩
    · step with sched.is_schedulable.spec' as ⟨b1, eb1⟩
      split
      · rename_i hb1
        obtain ⟨hrun, hbd, hrl, hrm⟩ := eb1 hb1
        have hA6 : L.mem s6 (scA i) ∈ Ac := (hS6.act _ (hX6.2.2.bound i hi hbd).1).2 hrm
        refine WP.spec_bind (WP.spec_and (sched.enqueue.sch s6 i Q6 R6 h6 hB6 hSg6 hi (fun _ => hrl)
          (fun _ => hrun) (fun _ => hbd) (fun _ => hA6))
          (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s6 i h6 hi)) ?_
        rintro s8 ⟨⟨⟨⟨Q8, R8, h8⟩, hB8, f8⟩, -, -, -⟩, fw8⟩
        have hb8 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s8 := ⟨⟨Q8, R8, h8⟩, hB8, hX6.fr f8, hS6.fr f8, hSg6.fr f8⟩
        exact WP.spec_mono (WP.spec_and (smp.remote_reschedule.blk a4 cpu hb8) (smp.remote_reschedule.foot a4 cpu hb8))
          fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact ⟨hr.1.1, fw8.trans hr.2⟩
      · refine WP.spec_bind (WP.spec_and (sched.set_reprogram_on.blk cpu hb6 hcpu)
          (sched.set_reprogram_on.foot cpu hb6 hcpu)) fun s8 hh8 => ?_
        exact WP.spec_mono (WP.spec_and (smp.remote_reschedule.blk a4 cpu hh8.1.1)
          (smp.remote_reschedule.foot a4 cpu hh8.1.1))
          fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact ⟨hr.1.1, hh8.2.trans hr.2⟩
  rintro ⟨s7, a5⟩ ⟨h7, fw7⟩
  try simp only [WP.uncurry'_pair]
  step with sched.cur_thread.spec as ⟨t, _⟩
  step with tcb_eq.blk as ⟨b1, _⟩
  refine WP.spec_bind (Pₘ := fun t1 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac t1 ∧ Foot st T Cs Sg Scs Z ∅ s7 t1) ?_
    fun t1 h => (WP.spec_ok _).2 ⟨h.1, fw6.trans (fw7.trans h.2)⟩
  split
  · obtain ⟨⟨Q7, R7, q7⟩, hB7, hX7, hS7, hSg7⟩ := h7
    exact WP.spec_mono (WP.spec_and (sched.reschedule_required.sch s7 Q7 R7 q7 hB7 hSg7)
      (sched.reschedule_required.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s7 q7))
      fun s' ⟨⟨⟨⟨Q', R', q'⟩, hB', f'⟩, _, _, _⟩, fw'⟩ => ⟨⟨⟨Q', R', q'⟩, hB', hX7.fr f', hS7.fr f', hSg7.fr f'⟩, fw'⟩
  · exact (WP.spec_ok _).2 ⟨h7, Foot.refl _⟩

/-- Refill writes (`RFW`) are `Foot` words and keep every TCB's affinity. -/
theorem rfw_foot {s s' : S} {c : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : c ∈ Scs)
    (w : WritesIn st s s' (RFW c (Z c))) :
    Foot st T Cs Sg Scs Z ∅ s s' ∧ ∀ y ∈ T, L.mem s' (affA y) = L.mem s (affA y) := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hO := hX.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  refine ⟨Foot.of w fun b hb => kw_sc hc (RFW.insc hP hz hb), fun y hy => ?_⟩
  have hal := field_aligned (K := 3520#u64) (h0.tcbs y hy) (by simp) (by simp)
  exact w.mem_eq hal fun hb => out_ne_field (h0.omega _ (hO.scW c hc _ hal (RFW.insc hP hz hb))) hy
    (h0.tcbs y hy) (K := 3520#u64) (by simp) rfl

set_option maxHeartbeats 8000000 in
/-- **P1's `configure_flags.blk` with the footprint `Foot`**, the SC's thread
(if any) on the core `cpu`. -/
theorem schedcontext.configure_flags.blkK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (a : A)
    (target cpu budget period max_refills badge flags : U64)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (htS : target ∈ Scs) (ht0 : target ≠ 0#u64) (hcpu : cpu ∈ Cs)
    (h2 : sporadic.MIN_REFILLS.val ≤ max_refills.val) (hm : max_refills.val ≤ absMax (Z target))
    (hna : ∀ y ∈ T, L.actionW s ≠ y)
    (haff : L.mem s (scTcbA target) ≠ 0#u64 → L.mem s (affA (L.mem s (scTcbA target))) = cpu) :
    schedcontext.configure_flags st ar s a target cpu budget period max_refills badge flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) r.1 ∧ Foot st T Cs Sg Scs Z ∅ s r.1 ⦄ := by
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
  have hai : i ≠ 0#u64 → L.mem s (affA i) = cpu := fun h0 => by
    rw [ei]; exact haff (by rw [← ei]; exact h0)
  have hbi : b = false → i ≠ 0#u64 := fun hf e => by rw [eb, e] at hf; simp at hf
  -- the thread out of the queues
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
      (b = false → (L.mem r.1 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem r.1 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem r.1 (scA i) = target ∧ L.mem r.1 (affA i) = cpu) ∧ (∀ y ∈ T, L.actionW r.1 ≠ y) ∧
      Foot st T Cs Sg Scs Z ∅ s r.1) ?_ ?_
  · split
    · rename_i hb
      exact (WP.spec_ok _).2 ⟨h, fun hf => absurd (hf.symm.trans hb) (by simp), hna, Foot.refl _⟩
    · rename_i hb
      have hi0 : i ≠ 0#u64 := hbi (by simpa using hb)
      exact WP.spec_mono (cfAK hA a i target h (hiT hi0) hna) fun r ⟨h1, q1, r1, a1, s1, _, f1, af1⟩ =>
        ⟨h1, fun _ => ⟨q1, r1, s1.trans (hsci hi0), af1.trans (hai hi0)⟩, a1, f1⟩
  rintro ⟨s1, a1⟩ ⟨h1, hq1, ha1, fw1⟩
  try simp only [WP.uncurry'_pair]
  -- the refills
  have keep : ∀ s2 : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 →
      L.actionW s2 = L.actionW s1 →
      (∀ y ∈ T, L.mem s2 (scA y) = L.mem s1 (scA y) ∧ L.mem s2 (stA y) = L.mem s1 (stA y) ∧
        L.mem s2 (inqA y) = L.mem s1 (inqA y)) →
      (∀ y ∈ T, L.mem s2 (affA y) = L.mem s1 (affA y)) →
      Foot st T Cs Sg Scs Z ∅ s1 s2 →
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
      (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s2 (scA i) = target ∧ L.mem s2 (affA i) = cpu) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
      Foot st T Cs Sg Scs Z ∅ s s2 := fun s2 h2' ea fl fa fw =>
    ⟨h2', fun hf => by
      have hiT' := hiT (hbi hf)
      obtain ⟨q, r, sc, af⟩ := hq1 hf
      rw [(fl i hiT').2.2, (fl i hiT').1, fa i hiT']; exact ⟨q, r, sc, af⟩, fun y hy => by rw [ea]; exact ha1 y hy,
      fw1.trans fw⟩
  have RN : ∀ m bud per : U64, sporadic.MIN_REFILLS.val ≤ m.val → m.val ≤ absMax (Z target) →
      sporadic.refill_new st s1 target m bud per ⦃ s2 =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
        (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
          L.mem s2 (scA i) = target ∧ L.mem s2 (affA i) = cpu) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
        Foot st T Cs Sg Scs Z ∅ s s2 ⦄ := fun m bud per hm2 hmm =>
    WP.spec_mono (sporadic.refill_new.fr m bud per hP hz hm2 hmm) fun s2 ⟨wf, w⟩ => by
      obtain ⟨h2', ea, -, -, fl⟩ := refill_blk h1 htS w wf
      obtain ⟨fw, fa⟩ := rfw_foot h1 htS w
      exact keep s2 h2' ea fl fa fw
  have RU : ∀ per bud m : U64, sporadic.MIN_REFILLS.val ≤ m.val → m.val ≤ absMax (Z target) →
      sporadic.refill_update st s1 target per bud m ⦃ s2 =>
        BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
        (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
          L.mem s2 (scA i) = target ∧ L.mem s2 (affA i) = cpu) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
        Foot st T Cs Sg Scs Z ∅ s s2 ⦄ := fun per bud m hm2 hmm =>
    WP.spec_mono (sporadic.refill_update.fr per bud m hP hz hm2 hmm) fun s2 ⟨wf, w⟩ => by
      obtain ⟨h2', ea, -, -, fl⟩ := refill_blk h1 htS w wf
      obtain ⟨fw, fa⟩ := rfw_foot h1 htS w
      exact keep s2 h2' ea fl fa fw
  have hmin : sporadic.MIN_REFILLS.val ≤ absMax (Z target) := h2.trans hm
  refine WP.spec_bind (Pₘ := fun s2 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) s2 ∧
      (b = false → (L.mem s2 (inqA i) &&& sched.Q_QUEUED) = 0#u64 ∧ (L.mem s2 (inqA i) &&& sched.Q_RELEASE) = 0#u64 ∧
        L.mem s2 (scA i) = target ∧ L.mem s2 (affA i) = cpu) ∧ (∀ y ∈ T, L.actionW s2 ≠ y) ∧
      Foot st T Cs Sg Scs Z ∅ s s2) ?_ ?_
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
  rintro s2 ⟨h2', hq2, ha2, fw2⟩
  -- the core
  refine WP.spec_bind (obj.Sc.set_cpu.wr s2 target cpu) fun s3 e3 => ?_
  subst e3
  obtain ⟨h3, ea3, -, -, fl3⟩ := scword_blk h2' htS hTA (Or.inl (scCoreA_val hP hz)) (fun _ => hcpu)
  obtain ⟨fw3, fa3⟩ := scw_foot (v := cpu) h2' htS (Or.inl (scCoreA_val hP hz))
  -- the thread
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac) r.1 ∧
      Foot st T Cs Sg Scs Z ∅ s r.1) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 ⟨h3, fw2.trans fw3⟩
    · rename_i hb
      have hbf : b = false := by simpa using hb
      have hiT' := hiT (hbi hbf)
      obtain ⟨q2, r2, sc2, af2⟩ := hq2 hbf
      exact WP.spec_mono (cfDK hA _ a1 i target cpu h3 hiT' (by rw [(fl3 i hiT').2.2]; exact q2)
        (by rw [(fl3 i hiT').2.2]; exact r2) (by rw [(fl3 i hiT').1]; exact sc2) ht0 htS hTA hcpu
        (fun y hy => by rw [ea3]; exact ha2 y hy) (by rw [fa3 i hiT']; exact af2))
        fun r hr => ⟨hr.1, fw2.trans (fw3.trans hr.2)⟩
  rintro ⟨s4, a2⟩ ⟨h4, fw4⟩
  try simp only [WP.uncurry'_pair]
  -- the badge and the sporadic flag
  refine WP.spec_bind (obj.Sc.set_badge.wr s4 target badge) fun s5 e5 => ?_
  subst e5
  have hbv : (core.num.U64.wrapping_add target layout.sc.BADGE).val = target.val + 16 ∨
      (core.num.U64.wrapping_add target layout.sc.BADGE).val = target.val + 48 ∨
      (core.num.U64.wrapping_add target layout.sc.BADGE).val = target.val + 64 := Or.inr (Or.inl (by
    rw [sc_word_val hP hz (o := layout.sc.BADGE) (by simp [layout.sc.BADGE])]; simp [layout.sc.BADGE]))
  have h5 := (scword_blk (v := badge) h4 htS hTA hbv
    (fun e => by
      have := congrArg UScalar.val e
      rw [sc_word_val hP hz (o := layout.sc.BADGE) (by simp [layout.sc.BADGE]), scCoreA_val hP hz] at this; simp [layout.sc.BADGE] at this)).1
  have fw5 := (scw_foot (v := badge) h4 htS hbv).1
  simp only [lift, bind_ok]
  have hsv : (core.num.U64.wrapping_add target layout.sc.SPORADIC).val = target.val + 16 ∨
      (core.num.U64.wrapping_add target layout.sc.SPORADIC).val = target.val + 48 ∨
      (core.num.U64.wrapping_add target layout.sc.SPORADIC).val = target.val + 64 := Or.inr (Or.inr (by
    rw [sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])]; simp [layout.sc.SPORADIC]))
  have spv : ∀ v : U64, BlkOK st T Cs Ω H Sg Rp Scs Nt Z (insert target Ac)
      (L.wr (L.wr s4 (core.num.U64.wrapping_add target layout.sc.BADGE) badge)
        (core.num.U64.wrapping_add target layout.sc.SPORADIC) v) ∧ Foot st T Cs Sg Scs Z ∅ s
      (L.wr (L.wr s4 (core.num.U64.wrapping_add target layout.sc.BADGE) badge)
        (core.num.U64.wrapping_add target layout.sc.SPORADIC) v) := fun v =>
    ⟨(scword_blk (v := v) h5 htS hTA hsv
      (fun e => by
        have := congrArg UScalar.val e
        rw [sc_word_val hP hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC]), scCoreA_val hP hz] at this
        simp [layout.sc.SPORADIC] at this)).1,
      fw4.trans (fw5.trans (scw_foot (v := v) h5 htS hsv).1)⟩
  split
  · exact WP.spec_bind (obj.Sc.set_sporadic.wr _ target 1#u64) fun s6 e6 => (WP.spec_ok _).2 (by subst e6; exact spv _)
  · exact WP.spec_bind (obj.Sc.set_sporadic.wr _ target 0#u64) fun s6 e6 => (WP.spec_ok _).2 (by subst e6; exact spv _)

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errK" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 ⟨⟨Ac, h⟩, Foot.refl _⟩
  | (simp only [error.range, error.illegal, error.truncated, error.invalid_cap, bind_ok]
     exact (WP.spec_ok _).2 ⟨⟨Ac, h⟩, Foot.refl _⟩))

set_option maxHeartbeats 8000000 in
/-- **`SchedControl_ConfigureFlags` with the footprint `Foot`** (P1's
`decode_sched_control.dec` from `BlkOK` and the decode's facts: the core
among the cores, an extra SC cap's object an SC of its size whose thread, if
any, is on the core `cpu`). -/
theorem schedcontext.decode_sched_control.footK {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {a : A} {lbl cpu len buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcpu : cpu ∈ Cs)
    (hrun : Runnable (L.mem s (stA (L.curW s)))) (hact : L.actionW s = 0#u64)
    (hx : ∀ sl, Aeneas.Std.Array.index_usize extra 0#usize = ok sl → sl ≠ 0#u64 →
      obj.Slot.cap st sl s ⦃ c => ∀ ptr sz, c = .SchedContext ptr sz →
      ptr ∈ Scs ∧ ptr ≠ 0#u64 ∧ sz.val = Z ptr ∧
      (L.mem s (scTcbA ptr) ≠ 0#u64 → L.mem s (affA (L.mem s (scTcbA ptr))) = cpu) ⦄) :
    schedcontext.decode_sched_control st ar s a lbl cpu len buf extra ⦃ r s' _ =>
      (∃ Ac', BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac' s') ∧ Foot st T Cs Sg Scs Z ∅ s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold schedcontext.decode_sched_control
  split
  · errK
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  refine WP.spec_bind (schedcontext.extra_cap.gen0 (fun sl hsl h0 => hx sl hsl h0)) ?_
  rintro o ho
  rcases o with _ | c
  · errK
  have hcO := ho c rfl
  simp only
  split
  · errK
  refine WP.spec_bind (P0.sporadic.max_period_us.p0 ar a hA) fun max_us _ => ?_
  step with sporadic.min_budget_us.spec as ⟨min_us, _⟩
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 0#u64 hS) fun budget_us _ => ?_
  split
  · errK
  refine WP.spec_bind (hA.us_to_ticks a budget_us) fun budget _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 1#u64 hS) fun period_us _ => ?_
  split
  · errK
  refine WP.spec_bind (hA.us_to_ticks a period_us) fun period _ => ?_
  refine WP.spec_bind (sporadic.min_budget.ok hA a) fun mb _ => ?_
  split
  · errK
  split
  · errK
  split
  · errK
  cases c
  all_goals first | errK | skip
  rename_i ptr sz
  obtain ⟨hpS, hp0, hszv, hpaff⟩ := hcO ptr sz rfl
  dsimp only
  obtain ⟨hP, hz⟩ := h.2.2.1.1.sc ptr hpS
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
  · errK
  rename_i hle
  have hsub : (core.num.U64.wrapping_sub mr sporadic.MIN_REFILLS).val = mr.val - 2 := by
    simp [core.num.U64.wrapping_sub_val_eq, sporadic.MIN_REFILLS, U64.size_def, U64.numBits]; omega
  have hle' : er.val ≤ mr.val - 2 := by have := hle; rw [gt_iff_val, hsub] at this; omega
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 3#u64 hS) fun badge _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s ct buf 4#u64 hS) fun flags _ => ?_
  have ect' : ct = L.curW s := ect
  subst ect'
  have hr := runnable_ok hrun
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ h hct hr.1 hr.2) ?_
  rintro s1 ⟨h1, f1, -, k1⟩
  try simp only [lift, bind_ok]
  have hadd : (core.num.U64.wrapping_add er sporadic.MIN_REFILLS).val = er.val + 2 := by
    simp [core.num.U64.wrapping_add_val_eq, sporadic.MIN_REFILLS, U64.size_def, U64.numBits]; omega
  have hna : ∀ y ∈ T, L.actionW s1 ≠ y := fun y hy e => by
    rcases k1.act with e' | e'
    · rw [e', hact] at e; exact notT_small hT (by simp) (e ▸ hy)
    · rw [e'] at e; exact notT_small hT (by simp) (e ▸ hy)
  have haff1 : L.mem s1 (scTcbA ptr) ≠ 0#u64 → L.mem s1 (affA (L.mem s1 (scTcbA ptr))) = cpu := by
    rw [(k1.fix ptr hpS).1]
    intro h0
    have hyT : L.mem s (scTcbA ptr) ∈ T := h.2.2.1.2.2.yt.1 ptr hpS h0
    rw [affA, k1.fld _ hyT _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩), ← affA]
    exact hpaff h0
  refine WP.spec_bind (schedcontext.configure_flags.blkK hA a ptr cpu budget period _ badge flags h1 hpS hp0 hcpu
    (by rw [hadd]; simp [sporadic.MIN_REFILLS]) (by rw [hadd]; omega) hna haff1) ?_
  rintro ⟨s2, a2⟩ ⟨h2, f2⟩
  exact (WP.spec_ok _).2 ⟨⟨_, h2⟩, f1.trans f2⟩

end

end Fl4Proofs.P1
