/-
P3 (line mmuAD, gen 21): **the VT-x binding steps over `DetAtB`, the derivable form of `DetAt`.**

## Why `DetAt` is not derivable as stated

`DetAt V th Ub s` (P3/JExtVSteps) asks, in its `buf` field, that every TCB's IPC-buffer lookup lands in `Ub t`
at *every* state reached from `s` by writes of `JW` / `CW` words. `JW` contains every slot word of `th`, in
particular each TCB's buffer-cap slot (`P1.sbWordA t`, TCB offset 64 / 72), which `msg.lookup_ipc_buffer` reads
(`P1.lookup_ipc_buffer_same`). A state reached by writing an arbitrary `Frame` cap there has an arbitrary buffer
address, so no fixed `Ub` with `DetPl.rep` (the `Ub` words none of `JW` / `SW`) satisfies `buf`: the field is
over-quantified, and no layout or invariant fact gives it. The steps only ever carry `DetAt` along their actual
footprints, whose `JW` part is the two **binding words** (`tVcpuA t`, `vTcbA v`).

## What this module does

* `BW V th`: the binding words (TCB VCPU words, `V`'s `TCB` words; `BW.jw`: they are `JW` words).
* **`DetAtB`**: `DetAt` with `buf` over states reached by `BW` / `CW` writes. `DetAtB.mono` along `BW ∨ CW`,
  `DetPost.footB` (a detach's footprint is `BW ∨ CW`), `CW.njwB`, and the node-word lemmas.
* **`vcpu_detach_jvB`**, **`vcpu_decode_settcb_jvB`**, **`vcpu_enter_nosigB`**, **`vcpu_finalise_jvB`**: the gen 20
  theorems (`vcpu_detach_jv`, `vcpu_decode_settcb_jv`, `vcpu_enter_nosig`, `vcpu_finalise_jv`) with `DetAt`
  replaced by `DetAtB`; the proofs are gen 20's (the `JW` footprints of the carried `DetAt` are `BW` ones).

* **`vcpu_enter_boundB`**: `vcpu.enter` of a bound thread, **every branch**, including the signalled one
  (vcpu.rs l. 1108-1116: `complete_signal`, then `report` on a full reply or `MSG_INFO := 0`), with `hns` replaced by
  `hcs` [J]: `complete_signal` from a state reached by the VCPU writes keeps `JExtV` / `RunVmB` / `DetAtB` and the
  thread's VCPU word. Missing fact behind `hcs`: a footprint of `notification.complete_signal` (badge register,
  notification state, `maybe_donate_sched_context`, `sporadic.unblock_check`) that excludes the binding words and
  writes no state word to `TS_RUNNING_VM`; P1 has it only as `Foot` (`KW`, which contains every TCB word at
  offsets 192..4095 but 3576 / 3584, VCPU and state words included) under the BlkOK bundle at the call state, and no
  VM-epoch fact provides that bundle.

Named premises (as gen 20, with `DetAtB` for `DetAt`), all [J]: `DetPl`, `DetAtB`, `FinPl`, and
`vcpu_decode_settcb_jvB`'s `hex` / `hct`, `vcpu_enter_nosigB`'s `hvi` / `hns`, `vcpu_enter_boundB`'s `hvi` / `hcs`. P3/JExtVLay derives `DetPl`,
`DetAtB`, `hct`, `hvi` from `JAtZ` + `JVm`. No [P] / [W] / [S] premise. No existing statement changed.
-/
import Fl4Proofs.P3.JExtVSteps2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- The binding words: every TCB's VCPU word and every `V` VCPU's `TCB` word. -/
def BW (V : Set U64) (th : TypedHeap) (b : U64) : Prop :=
  (∃ t, th t = some .tcb ∧ b = tVcpuA t) ∨ (∃ v ∈ V, b = vTcbA v)

theorem BW.jw {V : Set U64} {th : TypedHeap} {b : U64} (h : BW V th b) : JW V th b := Or.inr h

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **The per-state facts a detach needs, in derivable form** [J] (module docstring): `DetAt` with `buf` over
states reached by binding-word / `CW` writes. -/
structure DetAtB (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap)
    (Ub : U64 → Set U64) (s : S) : Prop where
  node : ∃ T, P1.NodePlaced st T s (L.cpu s)
  nd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ¬ JW V th b ∧ ¬ SW th b
  buf : ∀ s1, P1.WritesIn st s s1 (fun b => BW V th b ∨ CW st V th Ub s b) → ∀ t, th t = some .tcb →
    msg.lookup_ipc_buffer st s1 true t ⦃ P1.BufOK (Ub t) ⦄

variable {V X : Set U64} {th : TypedHeap} {Ub : U64 → Set U64}

/-- `DetAt` gives `DetAtB` (the converse fails, module docstring). -/
theorem DetAt.toB {s : S} (Da : DetAt st V th Ub s) : DetAtB st V th Ub s :=
  ⟨Da.node, Da.nd, fun s1 h => Da.buf s1 (h.mono fun b hb => hb.elim (fun h' => Or.inl h'.jw) Or.inr)⟩

theorem CW.njwB (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s) {b : U64} (hb : CW st V th Ub s b) :
    ¬ JW V th b := by
  rcases hb with e | e | ⟨t, ht, h | e⟩ | ⟨v, hv, h⟩
  · exact (Da.nd b (Or.inl e)).1
  · exact (Da.nd b (Or.inr e)).1
  · exact (D.rep t ht b h).1
  · exact D.pl.swjw b ⟨t, ht, e⟩
  · exact (D.vc v hv b h).1

theorem DetAtB.ipiA_al {s : S} (Da : DetAtB st V th Ub s) : P1.Aligned (ipiA st s) := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_aligned hN (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])

theorem DetAtB.actA_al {s : S} (Da : DetAtB st V th Ub s) : P1.Aligned (actA st s) := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])

theorem DetAtB.curA_al {s : S} (Da : DetAtB st V th Ub s) : P1.Aligned (curA st s) := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_aligned hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])

theorem DetAtB.cur_ne_ipi {s : S} (Da : DetAtB st V th Ub s) : curA st s ≠ ipiA st s := by
  obtain ⟨T, hN⟩ := Da.node
  exact P1.nodeAt_ne hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.IPI_PENDING])
    (by simp [layout.node.CUR_THREAD, layout.node.IPI_PENDING])

/-- `DetAtB` carried along a `BW` / `CW` footprint. -/
theorem DetAtB.mono {s s' : S} (Da : DetAtB st V th Ub s)
    (h : P1.WritesIn st s s' (fun b => BW V th b ∨ CW st V th Ub s b)) : DetAtB st V th Ub s' where
  node := by obtain ⟨T, hN⟩ := Da.node; exact ⟨T, by rw [h.2.1]; exact hN.ksb h.1⟩
  nd b hb := Da.nd b (by rw [ipiA_of h, actA_of h] at hb; exact hb)
  buf s1 h1 t ht := Da.buf s1 ((h.trans h1).mono fun b hb => hb.elim id fun h' => h'.elim Or.inl
    fun c => Or.inr (CW.of h c)) t ht

/-- A detach's footprint is binding words and `CW` words. -/
theorem DetPost.footB {t : U64} {s s' : S} (Dp : DetPost st V X th Ub t s s') (ht : th t = some .tcb)
    (hb : L.mem s (tVcpuA t) ≠ 0#u64 → L.mem s (tVcpuA t) ∈ V) :
    P1.WritesIn st s s' (fun b => BW V th b ∨ CW st V th Ub s b) :=
  Dp.foot.mono fun b h => by
    rcases h with ⟨h0, e | e⟩ | c
    · exact Or.inl (Or.inl ⟨t, ht, e⟩)
    · exact Or.inl (Or.inr ⟨_, hb h0, e⟩)
    · exact Or.inr c

set_option maxHeartbeats 8000000 in
/-- **`vcpu.detach` keeps the extension** (module docstring): `JExtV V X th` and `RunVmB th` afterwards, `t`'s VCPU
word 0, its old VCPU's `TCB` word 0, the writes those two words and `CW` words. -/
theorem vcpu_detach_jvB (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {t : U64} (ht : th t = some .tcb) :
    vcpu.detach st ar s a t ⦃ r => DetPost st V X th Ub t s r.1 ⦄ := by
  have P := D.pl
  have JWt : JW V th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  have aT : P1.Aligned (tVcpuA t) := P.jw _ JWt
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  split
  · rename_i hv0
    have h0 : L.mem s (tVcpuA t) = 0#u64 := by rw [← ev']; exact hv0
    exact (WP.spec_ok _).2 ⟨E, R, h0,
      fun w hw (e : L.mem s (tVcpuA t) = w) => absurd (e.symm.trans h0) (E.nz w hw), P1.WritesIn.refl _ _⟩
  rename_i hv0
  have hvne : L.mem s (tVcpuA t) ≠ 0#u64 := by rw [← ev']; exact hv0
  obtain ⟨hvV, hvt⟩ := (E.bnd t ht).resolve_left hvne
  rw [← ev'] at hvV hvt
  have JWb : JW V th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  have aB : P1.Aligned (vTcbA v) := P.jw _ JWb
  have aS : P1.Aligned (svmA v) := (D.vca v hvV).2
  have clS : ∀ b, b = svmA v → ¬ JW V th b ∧ ¬ SW th b := fun b e => D.vc v hvV b (Or.inr e)
  refine WP.spec_bind (vcpu_stall_w hA s a v Da.ipiA_al) ?_
  rintro ⟨s1, a1⟩ w1
  try simp only [uncurry_apply_pair]
  have w1' : P1.WritesIn st s s1 (· = ipiA st s) := w1
  have cl1 : ∀ b, b = ipiA st s → ¬ JW V th b ∧ ¬ SW th b := fun b e => Da.nd b (Or.inl e)
  have E1 := E.of_writes P w1' fun b hb => (cl1 b hb).1
  have R1 := R.of_clean P w1' cl1
  have kJ : ∀ b, JW V th b → L.mem s1 b = L.mem s b := fun b hb =>
    w1'.mem_eq (P.jw b hb) fun e => (cl1 b e).1 hb
  have Da1 : DetAtB st V th Ub s1 := Da.mono (w1'.mono fun b e => Or.inr (Or.inl e))
  refine WP.spec_bind (P1.obj.Tcb.state.spec s1 t) fun i ei => ?_
  refine WP.spec_bind (Pₘ := fun s2 => P1.WritesIn st s1 s2 (fun b => P1.RepW t (Ub t) b ∨ b = pendA v ∨
      b = P1.stA t ∨ b = actA st s) ∧ L.mem s2 (P1.stA t) ≠ 8#u64) ?_ ?_
  · split
    · have hpa : P1.Aligned (pendA (L.mem s1 (tVcpuA t))) := by
        rw [kJ _ JWt, ← ev']; exact (D.vca v hvV).1
      have hne : actA st s1 ≠ P1.stA t := fun e => (Da1.nd _ (Or.inr rfl)).2 ⟨t, ht, e⟩
      refine WP.spec_mono (vcpu_report_w hA a1 (D.ta t ht) (D.ua t ht) (Da1.buf s1 (P1.WritesIn.refl _ _) t ht)
        hpa (P.sw _ ⟨t, ht, rfl⟩) Da1.actA_al hne) fun s2 ⟨w, e⟩ => ⟨?_, by rw [e]; simp [sched.TS_RUNNING]⟩
      rw [kJ _ JWt, ← ev', actA_of w1'] at w
      exact w
    · rename_i hi8
      exact (WP.spec_ok _).2 ⟨P1.WritesIn.refl _ _, by rw [← ei]; simpa [sched.TS_RUNNING_VM] using hi8⟩
  intro s2 ⟨w2, h82⟩
  have cl2 : ∀ b, (P1.RepW t (Ub t) b ∨ b = pendA v ∨ b = P1.stA t ∨ b = actA st s) → ¬ JW V th b := by
    rintro b (h | e | e | e)
    · exact (D.rep t ht b h).1
    · exact (D.vc v hvV b (Or.inl e)).1
    · exact P.swjw b ⟨t, ht, e⟩
    · exact (Da.nd b (Or.inr e)).1
  have E2 := E1.of_writes P w2 cl2
  have R2 : RunVmB (L := L) th s2 := R1.of_foot P w2
    (fun t' ht' hw => by
      rcases hw with h | e | e | e
      · exact ((D.rep t ht _ h).2 ⟨t', ht', rfl⟩).elim
      · exact ((D.vc v hvV _ (Or.inl e)).2 ⟨t', ht', rfl⟩).elim
      · exact Or.inl (by rw [stA_inj e]; exact h82)
      · exact ((Da.nd _ (Or.inr e)).2 ⟨t', ht', rfl⟩).elim)
    (fun t' ht' hw => by
      have J' : JW V th (tVcpuA t') := Or.inr (Or.inl ⟨t', ht', rfl⟩)
      rcases hw with h | e | e | e
      · exact ((D.rep t ht _ h).1 J').elim
      · exact ((D.vc v hvV _ (Or.inl e)).1 J').elim
      · exact (P.swjw _ ⟨t, ht, e⟩ J').elim
      · exact ((Da.nd _ (Or.inr e)).1 J').elim)
  have k2 : ∀ b, JW V th b → L.mem s2 b = L.mem s1 b := fun b hb =>
    w2.mem_eq (P.jw b hb) fun h => cl2 b h hb
  have htv2 : L.mem s2 (tVcpuA t) = v := by rw [k2 _ JWt, kJ _ JWt]; exact ev'.symm
  have hvt2 : L.mem s2 (vTcbA v) = t := by rw [k2 _ JWb, kJ _ JWb]; exact hvt
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s5 e5 => ?_
  subst e5
  refine (WP.spec_ok _).2 ?_
  show DetPost st V X th Ub t s (L.wr (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64)
  have w34 : P1.WritesIn st s2 (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64)
      (fun b => b = vTcbA v ∨ b = tVcpuA t) := (P1.writesIn_wr aB).trans (P1.writesIn_wr aT)
  have m4T : L.mem (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (tVcpuA t) = 0#u64 := by
    rw [L.mem_wr _ _ _ _ aT aT, if_pos rfl]
  have m4B : L.mem (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (vTcbA v) = 0#u64 := by
    rw [L.mem_wr _ _ _ _ aT aB, if_neg (P.vb t ht v hvV), L.mem_wr _ _ _ _ aB aB, if_pos rfl]
  have E4 := E2.unbind_w P ht hvV htv2 hvt2 w34 m4T m4B
  have w5 : P1.WritesIn st (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64)
      (L.wr (L.wr (L.wr s2 (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (svmA v) 0#u64) (· = svmA v) :=
    P1.writesIn_wr aS
  refine ⟨E4.of_writes P w5 fun b e => (clS b e).1, ?_, ?_, ?_, ?_⟩
  · refine R2.of_foot P (w34.trans w5) (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)
    · have S' : SW th (P1.stA t') := ⟨t', ht', rfl⟩
      rcases hw with (e | e) | e
      · exact (P.swjw _ S' (Or.inr (Or.inr ⟨v, hvV, e⟩))).elim
      · exact (P.swjw _ S' (Or.inr (Or.inl ⟨t, ht, e⟩))).elim
      · exact ((clS _ e).2 S').elim
    · rcases hw with (e | e) | e
      · exact (P.vb t' ht' v hvV e).elim
      · exact Or.inl (by rw [tVcpuA_inj e]; exact h82)
      · exact ((clS _ e).1 (Or.inr (Or.inl ⟨t', ht', rfl⟩))).elim
  · rw [w5.mem_eq aT fun e => (clS _ e).1 JWt]; exact m4T
  · intro w hw e
    have ew : w = v := e.symm.trans ev'.symm
    subst ew
    rw [w5.mem_eq aB fun e => (clS _ e).1 JWb]; exact m4B
  · refine (((w1'.trans w2).trans w34).trans w5).mono fun b h => ?_
    unfold CW
    rcases h with ((e | (h | e | e | e)) | (e | e)) | e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hvV, Or.inl e⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr e⟩)))
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inl ⟨hvne, Or.inr (by rw [← ev']; exact e)⟩
    · exact Or.inl ⟨hvne, Or.inl e⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hvV, Or.inr e⟩)))


set_option maxHeartbeats 16000000 in
/-- **`vcpu.decode` at `X86VCPUSetTCB` keeps the extension** (module docstring): on a VCPU `v ∈ V`, with the
extra cap slots slots of `th` whose `Thread` caps name TCBs (`hex` [J]) and the current thread a TCB (`hct` [J]). -/
theorem vcpu_decode_settcb_jvB (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {len v buf : U64} {call : Bool}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hvV : v ∈ V)
    (hex : ∀ x ∈ extra.val, x ≠ 0#u64 → IsSlot th x ∧ ∀ p, capV (L.mem s) x = .Thread p → th p = some .tcb)
    (hct : th (L.mem s (curA st s)) = some .tcb) :
    vcpu.decode st ar s a fl4_abi.label.X86VCPUSetTCB len v call buf extra ⦃ r s' _ =>
      JExtV (L := L) V X th s' ∧ RunVmB (L := L) th s' ⦄ := by
  have P := D.pl
  unfold vcpu.decode
  refine WP.spec_bind (vcpu_stall_w hA s a v Da.ipiA_al) ?_
  rintro ⟨s1, a1⟩ w1
  try simp only [uncurry_apply_pair]
  have w1' : P1.WritesIn st s s1 (· = ipiA st s) := w1
  have cl1 : ∀ b, b = ipiA st s → ¬ JW V th b ∧ ¬ SW th b := fun b e => Da.nd b (Or.inl e)
  have E1 := E.of_writes P w1' fun b hb => (cl1 b hb).1
  have R1 := R.of_clean P w1' cl1
  have Da1 : DetAtB st V th Ub s1 := Da.mono (w1'.mono fun b e => Or.inr (Or.inl e))
  have LEAF : ∀ r : core.result.Result Unit error.Exc, (ok (r, s1, a1) : Result _) ⦃ r s' _ =>
      JExtV (L := L) V X th s' ∧ RunVmB (L := L) th s' ⦄ := fun r => (WP.spec_ok _).2 ⟨E1, R1⟩
  refine WP.spec_bind (P1.sched.cur_thread.spec s1) fun ct ect => ?_
  have hct1 : th ct = some .tcb := by
    have e1 : L.mem s1 (curA st s1) = L.mem s (curA st s) := by
      rw [curA_of w1']; exact w1'.mem_eq Da.curA_al Da.cur_ne_ipi
    have : ct = L.mem s (curA st s) := ect.trans e1
    rw [this]; exact hct
  refine WP.spec_bind (hA.virtualization a1) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun f _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_mono (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun _ _ => trivial
    · exact (WP.spec_ok _).2 trivial) fun value _ => ?_
  first | rw [if_pos trivial] | rw [if_pos rfl]
  refine WP.spec_bind (P1.idx_mem extra 0#usize (by simp)) fun x hx => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · simp only [error.truncated, bind_ok]; exact LEAF _
  rename_i hx0
  obtain ⟨hxs, hxt⟩ := hex x hx (by simpa using hx0)
  have ecap : capV (L.mem s1) x = capV (L.mem s) x := by
    unfold capV
    rw [w1'.mem_eq (P.jw _ (Or.inl ⟨x, hxs, Or.inl rfl⟩)) fun e => (cl1 _ e).1 (Or.inl ⟨x, hxs, Or.inl rfl⟩),
      w1'.mem_eq (P.jw _ (Or.inl ⟨x, hxs, Or.inr rfl⟩)) fun e => (cl1 _ e).1 (Or.inl ⟨x, hxs, Or.inr rfl⟩)]
  simp only [slot_cap_eq, capAt_capV, bind_ok]
  rw [ecap]
  generalize hc : capV (L.mem s) x = c
  cases c
  case Thread ptr =>
    have hp : th ptr = some .tcb := hxt ptr hc
    have JWp : JW V th (tVcpuA ptr) := Or.inr (Or.inl ⟨ptr, hp, rfl⟩)
    refine WP.spec_bind (P1.smp.remote_tcb_stall.spec hA s1 a1 ptr) ?_
    rintro ⟨s3, a2⟩ h3
    try simp only [uncurry_apply_pair]
    have w3 : P1.WritesIn st s1 s3 (· = ipiA st s1) := writesIn_or Da1.ipiA_al h3
    have cl3 : ∀ b, b = ipiA st s1 → ¬ JW V th b ∧ ¬ SW th b := fun b e => Da1.nd b (Or.inl e)
    have E3 := E1.of_writes P w3 fun b hb => (cl3 b hb).1
    have R3 := R1.of_clean P w3 cl3
    have Da3 : DetAtB st V th Ub s3 := Da1.mono (w3.mono fun b e => Or.inr (Or.inl e))
    refine WP.spec_bind (vcpu_detach_jvB hA D Da3 E3 R3 a2 hp) ?_
    rintro ⟨s4, a3⟩ P4
    try simp only [uncurry_apply_pair]
    have P4' : DetPost st V X th Ub ptr s3 s4 := P4
    have Da4 : DetAtB st V th Ub s4 := Da3.mono (P4'.footB hp fun h => ((E3.bnd ptr hp).resolve_left h).1)
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (P1.LawfulStore.read_spec s4 _) fun i1 ei1 => ?_
    refine WP.spec_bind (P1.obj.Tcb.is_null.spec i1) fun b1 eb1 => ?_
    have ei1' : i1 = L.mem s4 (vTcbA v) := ei1
    refine WP.spec_bind (Pₘ := fun r : S × A => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
        L.mem r.1 (tVcpuA ptr) = 0#u64 ∧ L.mem r.1 (vTcbA v) = 0#u64 ∧ DetAtB st V th Ub r.1) ?_ ?_
    · split
      · rename_i hb
        have h0 : i1 = 0#u64 := by simpa [eb1] using hb
        exact (WP.spec_ok _).2 ⟨P4'.ext, P4'.rvm, P4'.w0, by rw [← ei1', h0], Da4⟩
      · rename_i hb
        have h0 : i1 ≠ 0#u64 := fun e => hb (by simp [eb1, e])
        have hb4 : L.mem s4 (vTcbA v) ≠ 0#u64 := by rw [← ei1']; exact h0
        obtain ⟨hi1, hi1v⟩ := (P4'.ext.back v hvV).resolve_left hb4
        rw [← ei1'] at hi1 hi1v
        refine WP.spec_mono (vcpu_detach_jvB hA D Da4 P4'.ext P4'.rvm a3 hi1) fun r P5 => ?_
        have P5' : DetPost st V X th Ub i1 s4 r.1 := P5
        refine ⟨P5'.ext, P5'.rvm, ?_, P5'.b0 v hvV hi1v,
          Da4.mono (P5'.footB hi1 fun _ => by rw [hi1v]; exact hvV)⟩
        by_cases e : ptr = i1
        · rw [e]; exact P5'.w0
        · rw [P5'.foot.mem_eq (P.jw _ JWp) ?_]
          · exact P4'.w0
          rintro (⟨-, e' | e'⟩ | c)
          · exact e (tVcpuA_inj e')
          · rw [hi1v] at e'; exact P.vb ptr hp v hvV e'
          · exact CW.njwB D Da4 c JWp
    rintro ⟨s5, a4⟩ ⟨E5, R5, t5, b5, Da5⟩
    try simp only [uncurry_apply_pair]
    simp only [vcpu.set, lift, bind_ok]
    refine WP.spec_bind (P1.LawfulStore.write_spec s5 _ _) fun s6 e6 => ?_
    subst e6
    step as ⟨o, eo⟩
    subst eo
    try simp only [lift, bind_ok]
    refine WP.spec_bind (P1.LawfulStore.write_spec _ _ _) fun s7 e7 => ?_
    subst e7
    have aT : P1.Aligned (tVcpuA ptr) := P.jw _ JWp
    have aB : P1.Aligned (vTcbA v) := P.jw _ (Or.inr (Or.inr ⟨v, hvV, rfl⟩))
    have w7 : P1.WritesIn st s5 (L.wr (L.wr s5 (vTcbA v) ptr) (tVcpuA ptr) v)
        (fun b => b = vTcbA v ∨ b = tVcpuA ptr) := (P1.writesIn_wr aB).trans (P1.writesIn_wr aT)
    have m7T : L.mem (L.wr (L.wr s5 (vTcbA v) ptr) (tVcpuA ptr) v) (tVcpuA ptr) = v := by
      rw [L.mem_wr _ _ _ _ aT aT, if_pos rfl]
    have m7B : L.mem (L.wr (L.wr s5 (vTcbA v) ptr) (tVcpuA ptr) v) (vTcbA v) = ptr := by
      rw [L.mem_wr _ _ _ _ aT aB, if_neg (P.vb ptr hp v hvV), L.mem_wr _ _ _ _ aB aB, if_pos rfl]
    have E7 := E5.bind_w P hp hvV t5 b5 D.h0 w7 m7T m7B
    have R7 : RunVmB (L := L) th (L.wr (L.wr s5 (vTcbA v) ptr) (tVcpuA ptr) v) := R5.of_foot P w7
      (fun t' ht' hw => by
        rcases hw with e | e
        · exact (P.swjw _ ⟨t', ht', rfl⟩ (Or.inr (Or.inr ⟨v, hvV, e⟩))).elim
        · exact (P.swjw _ ⟨t', ht', rfl⟩ (Or.inr (Or.inl ⟨ptr, hp, e⟩))).elim)
      (fun t' ht' hw => by
        rcases hw with e | e
        · exact (P.vb t' ht' v hvV e).elim
        · exact Or.inr (by rw [tVcpuA_inj e, m7T]; exact E.nz v hvV))
    have Da7 : DetAtB st V th Ub (L.wr (L.wr s5 (vTcbA v) ptr) (tVcpuA ptr) v) := Da5.mono (w7.mono fun b h =>
      Or.inl (h.elim (fun e => Or.inr ⟨v, hvV, e⟩) fun e => Or.inl ⟨ptr, hp, e⟩))
    have hne : actA st (L.wr (L.wr s5 (vTcbA v) ptr) (tVcpuA ptr) v) ≠ P1.stA ct := fun e =>
      (Da7.nd _ (Or.inr rfl)).2 ⟨ct, hct1, e⟩
    refine WP.spec_bind (sts_w _ ct sched.TS_RESTART (P.sw _ ⟨ct, hct1, rfl⟩) Da7.actA_al hne) ?_
    intro s8 ⟨w8, m8⟩
    refine (WP.spec_ok _).2 ⟨E7.of_writes P w8 ?_, R7.of_foot P w8 ?_ ?_⟩
    · rintro b (e | e)
      · exact P.swjw b ⟨ct, hct1, e⟩
      · exact (Da7.nd b (Or.inr e)).1
    · intro t' ht' hw
      rcases hw with e | e
      · left; rw [stA_inj e, m8]; simp [sched.TS_RESTART]
      · exact ((Da7.nd _ (Or.inr e)).2 ⟨t', ht', rfl⟩).elim
    · intro t' ht' hw
      rcases hw with e | e
      · exact (P.swjw _ ⟨ct, hct1, e⟩ (Or.inr (Or.inl ⟨t', ht', rfl⟩))).elim
      · exact ((Da7.nd _ (Or.inr e)).1 (Or.inr (Or.inl ⟨t', ht', rfl⟩))).elim
  all_goals (simp only [error.illegal, bind_ok]; exact LEAF _)

set_option maxHeartbeats 16000000 in
/-- **`vcpu.enter` of a bound thread with no signal pending** (vcpu.rs l. 1073-1120, the branch ending in
`TS_RUNNING_VM`): keeps `JExtV` and `RunVmB` (gen 19's `RunVmB.enter` on the extracted function). `hvi` [J]: the
bound VCPU's internal words (offsets below 2^15 other than `TCB`) are aligned and none of `JW` / `SW` (the VCPU
object, `.other 15`, apart from TCBs / CNodes; P1's `vcpu_obj_aligned`). `hns` [J]: after those writes the bound
notification is 0 or not active — the branch condition; the signalled branch (`complete_signal`, l. 1108) is
open. -/
theorem vcpu_enter_nosigB (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {t : U64} (ht : th t = some .tcb)
    (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hvi : ∀ b, VW (L.mem s (tVcpuA t)) b → P1.Aligned b ∧ ¬ JW V th b ∧ ¬ SW th b)
    (hns : ∀ s', P1.WritesIn st s s' (VW (L.mem s (tVcpuA t))) → obj.Tcb.bound_ntfn st t s' ⦃ n =>
      n ≠ 0#u64 → obj.Ntfn.state st n s' ⦃ x => x ≠ obj.NTFN_ACTIVE ⦄ ⦄) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ := by
  have P := D.pl
  have JWt : JW V th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  unfold vcpu.enter vcpu.bound
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  rw [← ev'] at hv0 hvi hns
  rw [if_neg hv0]
  have VS : ∀ s1, P1.WritesIn st s s1 (VW v) → ∀ (o x : U64), o.val < 32768 → o.val % 8 = 0 →
      o.val ≠ 20480 → vcpu.set st s1 v o x ⦃ s' => P1.WritesIn st s s' (VW v) ⦄ := by
    intro s1 w1 o x h1 h2 h3
    have hb : VW v (core.num.U64.wrapping_add v o) := ⟨o, h1, h2, h3, rfl⟩
    unfold vcpu.set
    simp only [lift, bind_ok]
    exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
      subst e
      exact (w1.trans (P1.writesIn_wr (hvi _ hb).1)).mono fun b h => h.elim id fun e => e ▸ hb
  have VM : ∀ s1, P1.WritesIn st s s1 (VW v) → ∀ (f x : U64),
      vcpu.write_vmcs st s1 v f x ⦃ s' => P1.WritesIn st s s' (VW v) ⦄ := by
    intro s1 w1 f x
    unfold vcpu.write_vmcs
    refine WP.spec_bind (P1.vcpu.vmcs_addr.off v f) ?_
    rintro _ ⟨o, h1, h2, rfl⟩
    have hb : VW v (core.num.U64.wrapping_add v o) := ⟨o, by omega, h2, by omega, rfl⟩
    exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
      subst e
      exact (w1.trans (P1.writesIn_wr (hvi _ hb).1)).mono fun b h => h.elim id fun e => e ▸ hb
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 _ _ _ _ L.total) fun b _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun ip _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun ctl _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun intr _ => ?_
  refine WP.spec_bind (hA.virtualization a1) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun s1 => P1.WritesIn st s s1 (VW v)) ?_ fun s1 w1 => ?_
  · split
    · have hRIP : vcpu.svm.RIP = ok 1400#u64 := by unfold vcpu.svm.RIP vcpu.svm.SAVE; rfl
      simp only [hRIP, bind_ok, lift, vcpu.get, shl_eq _ 32#i32 (by decide) (by decide)]
      refine WP.spec_bind (VS _ (P1.WritesIn.refl _ _) 1400#u64 _ (by simp) (by simp) (by simp)) fun s2 w2 => ?_
      refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun old _ => ?_
      refine WP.spec_bind (VS _ w2 vcpu.svm.INTERCEPT_EXC _ (by simp [vcpu.svm.INTERCEPT_EXC])
        (by simp [vcpu.svm.INTERCEPT_EXC]) (by simp [vcpu.svm.INTERCEPT_EXC])) fun s3 w3 => ?_
      refine WP.spec_bind (P0.vcpu.full_reply.p0 _ _ _ L.total) fun b1 _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun intr1 _ => ?_
      · cases b1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact (WP.spec_ok _).2 trivial
        · simp only [↓reduceIte]
          exact WP.spec_bind (P1.LawfulStore.read_spec _ _) fun _ _ => (WP.spec_ok _).2 trivial
      exact VS _ w3 vcpu.svm.EVENT_INJ _ (by simp [vcpu.svm.EVENT_INJ]) (by simp [vcpu.svm.EVENT_INJ])
        (by simp [vcpu.svm.EVENT_INJ])
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (VM _ (P1.WritesIn.refl _ _) _ _) fun s2 w2 => ?_
      refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
      refine WP.spec_bind P0.vcpu.PRIMARY_FORCED.p0 fun i1 _ => ?_
      refine WP.spec_bind (VM _ w2 _ _) fun s3 w3 => ?_
      exact VM _ w3 _ _
  refine WP.spec_bind (VS _ w1 vcpu.VALID 0#u64 (by simp [vcpu.VALID]) (by simp [vcpu.VALID])
    (by simp [vcpu.VALID])) fun s2 w2 => ?_
  refine WP.spec_bind (VS _ w2 vcpu.PENDING 0#u64 (by simp [vcpu.PENDING]) (by simp [vcpu.PENDING])
    (by simp [vcpu.PENDING])) fun s3 w3 => ?_
  have E3 := E.of_writes P w3 fun b h => (hvi b h).2.1
  have R3 := R.of_clean P w3 fun b h => (hvi b h).2
  have m3 : L.mem s3 (tVcpuA t) ≠ 0#u64 := by
    rw [w3.mem_eq (P.jw _ JWt) fun h => (hvi _ h).2.1 JWt, ← ev']; exact hv0
  have hact : P1.Aligned (actA st s3) ∧ ¬ JW V th (actA st s3) ∧ ¬ SW th (actA st s3) := by
    rw [actA_of w3]; exact ⟨Da.actA_al, (Da.nd _ (Or.inr rfl)).1, (Da.nd _ (Or.inr rfl)).2⟩
  have FIN : (do
      let s4 ← sched.set_thread_state st s3 t sched.TS_RUNNING_VM
      ok (s4, a1)) ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ :=
    WP.spec_bind (sts_jv P E3 R3 ht hact (Or.inr m3)) fun s4 h4 => (WP.spec_ok _).2 h4
  refine WP.spec_bind (hns s3 w3) fun n hn => ?_
  split
  · rename_i hn0
    refine WP.spec_bind (hn (by simpa using hn0)) fun x hx => ?_
    split
    · rename_i hxa; exact absurd hxa hx
    · exact FIN
  · exact FIN


set_option maxHeartbeats 16000000 in
/-- **`vcpu.enter` of a bound thread, every branch** (vcpu.rs l. 1073-1120): the VMCS / VMCB / `VALID` / `PENDING`
writes, then (no notification bound, or not active) `TS_RUNNING_VM`, or (bound notification active, l. 1108-1116)
`complete_signal`, then `report` (a full reply: registers / IPC buffer, `PENDING`, state `TS_RUNNING`) or
`MSG_INFO := 0`. Keeps `JExtV` and `RunVmB`. Premises as `vcpu_enter_nosigB` but `hns` replaced by **`hcs`** [J]:
`complete_signal` (badge register, notification state, SC donation `maybe_donate_sched_context`, sporadic
`unblock_check`) from any state reached by the VCPU writes keeps `JExtV` / `RunVmB` / `DetAtB` and the thread's VCPU
word. P1 gives its footprint only as `Foot` (`KW`: every TCB word at offsets 192..4095 but 3576 / 3584, so VCPU and
state words included) under the BlkOK bundle (`notification.complete_signal.ipc` / `maybe_donate…tinvF`), which no
VM-epoch fact provides; a footprint excluding the binding words (P3's `TFoot` style) for these three functions is the
missing fact. -/
theorem vcpu_enter_boundB (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {t : U64} (ht : th t = some .tcb)
    (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hvi : ∀ b, VW (L.mem s (tVcpuA t)) b → P1.Aligned b ∧ ¬ JW V th b ∧ ¬ SW th b)
    (hcs : ∀ s3 (a1 : A) (n : U64), P1.WritesIn st s s3 (VW (L.mem s (tVcpuA t))) → n ≠ 0#u64 →
      notification.complete_signal st ar s3 a1 n t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
        DetAtB st V th Ub r.1 ∧ L.mem r.1 (tVcpuA t) = L.mem s (tVcpuA t) ⦄) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ := by
  have P := D.pl
  have JWt : JW V th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
  unfold vcpu.enter vcpu.bound
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  have hvV : v ∈ V := by
    have := ((E.bnd t ht).resolve_left hv0).1
    rw [← ev'] at this; exact this
  rw [← ev'] at hv0 hvi hcs
  rw [if_neg hv0]
  have VS : ∀ s1, P1.WritesIn st s s1 (VW v) → ∀ (o x : U64), o.val < 32768 → o.val % 8 = 0 →
      o.val ≠ 20480 → vcpu.set st s1 v o x ⦃ s' => P1.WritesIn st s s' (VW v) ⦄ := by
    intro s1 w1 o x h1 h2 h3
    have hb : VW v (core.num.U64.wrapping_add v o) := ⟨o, h1, h2, h3, rfl⟩
    unfold vcpu.set
    simp only [lift, bind_ok]
    exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
      subst e
      exact (w1.trans (P1.writesIn_wr (hvi _ hb).1)).mono fun b h => h.elim id fun e => e ▸ hb
  have VM : ∀ s1, P1.WritesIn st s s1 (VW v) → ∀ (f x : U64),
      vcpu.write_vmcs st s1 v f x ⦃ s' => P1.WritesIn st s s' (VW v) ⦄ := by
    intro s1 w1 f x
    unfold vcpu.write_vmcs
    refine WP.spec_bind (P1.vcpu.vmcs_addr.off v f) ?_
    rintro _ ⟨o, h1, h2, rfl⟩
    have hb : VW v (core.num.U64.wrapping_add v o) := ⟨o, by omega, h2, by omega, rfl⟩
    exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
      subst e
      exact (w1.trans (P1.writesIn_wr (hvi _ hb).1)).mono fun b h => h.elim id fun e => e ▸ hb
  refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 _ _ _ _ L.total) fun b _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun ip _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun ctl _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun intr _ => ?_
  refine WP.spec_bind (hA.virtualization a1) fun i _ => ?_
  refine WP.spec_bind (Pₘ := fun s1 => P1.WritesIn st s s1 (VW v)) ?_ fun s1 w1 => ?_
  · split
    · have hRIP : vcpu.svm.RIP = ok 1400#u64 := by unfold vcpu.svm.RIP vcpu.svm.SAVE; rfl
      simp only [hRIP, bind_ok, lift, vcpu.get, shl_eq _ 32#i32 (by decide) (by decide)]
      refine WP.spec_bind (VS _ (P1.WritesIn.refl _ _) 1400#u64 _ (by simp) (by simp) (by simp)) fun s2 w2 => ?_
      refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun old _ => ?_
      refine WP.spec_bind (VS _ w2 vcpu.svm.INTERCEPT_EXC _ (by simp [vcpu.svm.INTERCEPT_EXC])
        (by simp [vcpu.svm.INTERCEPT_EXC]) (by simp [vcpu.svm.INTERCEPT_EXC])) fun s3 w3 => ?_
      refine WP.spec_bind (P0.vcpu.full_reply.p0 _ _ _ L.total) fun b1 _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun intr1 _ => ?_
      · cases b1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact (WP.spec_ok _).2 trivial
        · simp only [↓reduceIte]
          exact WP.spec_bind (P1.LawfulStore.read_spec _ _) fun _ _ => (WP.spec_ok _).2 trivial
      exact VS _ w3 vcpu.svm.EVENT_INJ _ (by simp [vcpu.svm.EVENT_INJ]) (by simp [vcpu.svm.EVENT_INJ])
        (by simp [vcpu.svm.EVENT_INJ])
    · try simp only [lift, bind_ok]
      refine WP.spec_bind (VM _ (P1.WritesIn.refl _ _) _ _) fun s2 w2 => ?_
      refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
      refine WP.spec_bind P0.vcpu.PRIMARY_FORCED.p0 fun i1 _ => ?_
      refine WP.spec_bind (VM _ w2 _ _) fun s3 w3 => ?_
      exact VM _ w3 _ _
  refine WP.spec_bind (VS _ w1 vcpu.VALID 0#u64 (by simp [vcpu.VALID]) (by simp [vcpu.VALID])
    (by simp [vcpu.VALID])) fun s2 w2 => ?_
  refine WP.spec_bind (VS _ w2 vcpu.PENDING 0#u64 (by simp [vcpu.PENDING]) (by simp [vcpu.PENDING])
    (by simp [vcpu.PENDING])) fun s3 w3 => ?_
  have E3 := E.of_writes P w3 fun b h => (hvi b h).2.1
  have R3 := R.of_clean P w3 fun b h => (hvi b h).2
  have m3 : L.mem s3 (tVcpuA t) ≠ 0#u64 := by
    rw [w3.mem_eq (P.jw _ JWt) fun h => (hvi _ h).2.1 JWt, ← ev']; exact hv0
  have hact : P1.Aligned (actA st s3) ∧ ¬ JW V th (actA st s3) ∧ ¬ SW th (actA st s3) := by
    rw [actA_of w3]; exact ⟨Da.actA_al, (Da.nd _ (Or.inr rfl)).1, (Da.nd _ (Or.inr rfl)).2⟩
  have FIN : (do
      let s4 ← sched.set_thread_state st s3 t sched.TS_RUNNING_VM
      ok (s4, a1)) ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ :=
    WP.spec_bind (sts_jv P E3 R3 ht hact (Or.inr m3)) fun s4 h4 => (WP.spec_ok _).2 h4
  refine WP.spec_bind (P0.obj.Tcb.bound_ntfn.p0 st t s3 L.total) fun n _ => ?_
  split
  · rename_i hn0
    refine WP.spec_bind (P0.obj.Ntfn.state.p0 st n s3 L.total) fun x _ => ?_
    split
    · refine WP.spec_bind (hcs s3 a1 n w3 (by simpa using hn0)) ?_
      rintro ⟨s4, a2⟩ ⟨E4, R4, Da4, m4⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (P0.vcpu.full_reply.p0 st s4 t L.total) fun b1 _ => ?_
      split
      · refine WP.spec_bind (P0.obj.Tcb.reg.p0 st t s4 _ L.total) fun i3 _ => ?_
        have hpa : P1.Aligned (pendA (L.mem s4 (tVcpuA t))) := by rw [m4]; exact (D.vca v hvV).1
        have hne : actA st s4 ≠ P1.stA t := fun e => (Da4.nd _ (Or.inr rfl)).2 ⟨t, ht, e⟩
        refine WP.spec_bind (vcpu_report_w hA a2 (D.ta t ht) (D.ua t ht) (Da4.buf s4 (P1.WritesIn.refl _ _) t ht)
          hpa (P.sw _ ⟨t, ht, rfl⟩) Da4.actA_al hne) fun s5 ⟨w, e5⟩ => ?_
        have cl : ∀ b, (P1.RepW t (Ub t) b ∨ b = pendA (L.mem s4 (tVcpuA t)) ∨ b = P1.stA t ∨ b = actA st s4) →
            ¬ JW V th b := by
          rintro b (h | e | e | e)
          · exact (D.rep t ht b h).1
          · rw [m4] at e; exact (D.vc v hvV b (Or.inl e)).1
          · exact P.swjw b ⟨t, ht, e⟩
          · exact (Da4.nd b (Or.inr e)).1
        refine (WP.spec_ok _).2 ⟨E4.of_writes P w cl, R4.of_foot P w (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)⟩
        · rcases hw with h | e | e | e
          · exact ((D.rep t ht _ h).2 ⟨t', ht', rfl⟩).elim
          · rw [m4] at e; exact ((D.vc v hvV _ (Or.inl e)).2 ⟨t', ht', rfl⟩).elim
          · left; rw [stA_inj e, e5]; simp [sched.TS_RUNNING]
          · exact ((Da4.nd _ (Or.inr e)).2 ⟨t', ht', rfl⟩).elim
        · exact ((cl _ hw) (Or.inr (Or.inl ⟨t', ht', rfl⟩))).elim
      · refine WP.spec_bind (P1.obj.Tcb.set_reg.wrS s4 t layout.reg.MSG_INFO 0#u64 (D.ta t ht)
          (by simp [layout.reg.MSG_INFO, layout.reg.RSI])) fun s5 ⟨K, hK, e⟩ => ?_
        subst e
        have hr : (layout.reg.MSG_INFO).val = 1 := by simp [layout.reg.MSG_INFO, layout.reg.RSI]
        have hw := P1.writesIn_wr (st := st) (s := s4) (v := 0#u64)
          (P1.field_aligned (D.ta t ht) (K := K) (by omega) (by omega))
        have hR : P1.RepW t (Ub t) (core.num.U64.wrapping_add t K) := Or.inl ⟨K, by omega, by omega, by omega, rfl⟩
        have hd : ∀ b, b = core.num.U64.wrapping_add t K → ¬ JW V th b ∧ ¬ SW th b := fun b e =>
          e ▸ D.rep t ht _ hR
        exact (WP.spec_ok _).2 ⟨E4.of_writes P hw fun b h => (hd b h).1, R4.of_clean P hw hd⟩
    · exact FIN
  · exact FIN

set_option maxHeartbeats 8000000 in
/-- **`vcpu.finalise` keeps the extension** (module docstring) and leaves the VCPU's `TCB` word 0. -/
theorem vcpu_finalise_jvB (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAtB st V th Ub s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {v : U64} (hvV : v ∈ V)
    (F : FinPl st V th Ub s v) :
    vcpu.finalise st ar s a v ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ⦄ := by
  have P := D.pl
  have JWb : JW V th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  unfold vcpu.finalise
  refine WP.spec_bind (vcpu_stall_w hA s a v Da.ipiA_al) ?_
  rintro ⟨s1, a1⟩ w1
  try simp only [uncurry_apply_pair]
  have w1' : P1.WritesIn st s s1 (· = ipiA st s) := w1
  have cl1 : ∀ b, b = ipiA st s → ¬ JW V th b ∧ ¬ SW th b := fun b e => Da.nd b (Or.inl e)
  have E1 := E.of_writes P w1' fun b hb => (cl1 b hb).1
  have R1 := R.of_clean P w1' cl1
  have Da1 : DetAtB st V th Ub s1 := Da.mono (w1'.mono fun b e => Or.inr (Or.inl e))
  refine WP.spec_bind (hA.vcpu_release a1 v) fun a2 _ => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s1 _) fun t et => ?_
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec t) fun b eb => ?_
  have et' : t = L.mem s1 (vTcbA v) := et
  refine WP.spec_bind (Pₘ := fun r : S × A => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ P1.WritesIn st s r.1 (fun b => JW V th b ∨ CW st V th Ub s b)) ?_ ?_
  · have w1J : P1.WritesIn st s s1 (fun b => JW V th b ∨ CW st V th Ub s b) :=
      w1'.mono fun b e => Or.inr (Or.inl e)
    split
    · rename_i hb
      have h0 : t = 0#u64 := by simpa [eb] using hb
      exact (WP.spec_ok _).2 ⟨E1, R1, by rw [← et', h0], w1J⟩
    · rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by simp [eb, e])
      obtain ⟨htt, htv⟩ := (E1.back v hvV).resolve_left (by rw [← et']; exact ht0)
      rw [← et'] at htt htv
      refine WP.spec_mono (vcpu_detach_jvB hA D Da1 E1 R1 a2 htt) fun r Pd => ?_
      have Pd' : DetPost st V X th Ub t s1 r.1 := Pd
      exact ⟨Pd'.ext, Pd'.rvm, Pd'.b0 v hvV htv, (w1J.trans (Pd'.footJ htt fun _ => by
        rw [htv]; exact hvV)).mono fun b h => h.elim id fun h' => h'.elim Or.inl fun c => Or.inr (CW.of w1' c)⟩
  rintro ⟨s2, a3⟩ ⟨E2, R2, b2, w2⟩
  try simp only [uncurry_apply_pair]
  have kL : ∀ b, (b = P1.vNextA v ∨ b = vPrevA v) → L.mem s2 b = L.mem s b := fun b hb =>
    w2.mem_eq (F.own b hb).1 fun h => h.elim (F.own b hb).2.1 (F.own b hb).2.2
  refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun pv ep => ?_
  refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun nx en => ?_
  have ep' : pv = L.mem s (vPrevA v) := ep.trans (kL _ (Or.inr rfl))
  have en' : nx = L.mem s (P1.vNextA v) := en.trans (kL _ (Or.inl rfl))
  have hhd : P1.vHeadA st s2 = P1.vHeadA st s := by unfold P1.vHeadA; rw [w2.1]
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s2 s3 (fun b => b = P1.vHeadA st s ∨
      (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v))))) ?_ fun s3 w3 => ?_
  · split
    · refine WP.spec_mono (P1.obj.ks_set.spec s2 _ _) fun s3 e3 => ?_
      subst e3
      have ea : core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD = P1.vHeadA st s := hhd
      rw [ea]
      exact (P1.writesIn_wr (F.nbr _ (Or.inl rfl)).1).mono fun b e => Or.inl e
    · rename_i hp0
      have hp : L.mem s (vPrevA v) ≠ 0#u64 := by rw [← ep']; exact hp0
      unfold vcpu.set
      simp only [lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
      subst e3
      have ea : core.num.U64.wrapping_add pv vcpu.NEXT = P1.vNextA (L.mem s (vPrevA v)) := by
        rw [ep']; rfl
      rw [ea]
      exact (P1.writesIn_wr (F.nbr _ (Or.inr (Or.inl ⟨hp, rfl⟩))).1).mono fun b e => Or.inr ⟨hp, e⟩
  have FIN : ∀ s4, P1.WritesIn st s2 s4 (fun b => (b = P1.vHeadA st s ∨
      (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v)))) ∨
      (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))) →
      JExtV (L := L) V X th s4 ∧ RunVmB (L := L) th s4 ∧ L.mem s4 (vTcbA v) = 0#u64 := fun s4 w4 => by
    have hd : ∀ b, ((b = P1.vHeadA st s ∨ (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v)))) ∨
        (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))) → ¬ JW V th b ∧ ¬ SW th b :=
      fun b h => (F.nbr b (h.elim (fun h' => h'.elim Or.inl fun h'' => Or.inr (Or.inl h''))
        fun h' => Or.inr (Or.inr h'))).2
    exact ⟨E2.of_writes P w4 fun b h => (hd b h).1, R2.of_clean P w4 hd,
      by rw [w4.mem_eq (P.jw _ JWb) fun h => (hd _ h).1 JWb]; exact b2⟩
  split
  · rename_i hn0
    have hn : L.mem s (P1.vNextA v) ≠ 0#u64 := by rw [← en']; simpa using hn0
    unfold vcpu.set
    simp only [lift, bind_ok]
    refine WP.spec_bind (P1.LawfulStore.write_spec s3 _ _) fun s4 e4 => ?_
    subst e4
    have ea : core.num.U64.wrapping_add nx vcpu.PREV = vPrevA (L.mem s (P1.vNextA v)) := by rw [en']; rfl
    rw [ea]
    exact (WP.spec_ok _).2 (FIN _ ((w3.trans (P1.writesIn_wr
      (F.nbr _ (Or.inr (Or.inr ⟨hn, rfl⟩))).1)).mono fun b h => h.elim Or.inl fun e => Or.inr ⟨hn, e⟩))
  · exact (WP.spec_ok _).2 (FIN _ (w3.mono fun b h => Or.inl h))

end

end

end Fl4Proofs.P3
