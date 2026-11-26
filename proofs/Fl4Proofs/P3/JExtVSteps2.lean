/-
P3 (line mmuAD, gen 20): **`JExtV` across VT-x object creation / deletion, `vcpu.finalise`, `vcpu::enter`'s state
change and a representative native step** (on top of P3/JExtVSteps).

* `VtxCap.mono`, `JExtV.mono_X` (an EPT retype grows `X`), **`JExtV.grow`** (a VCPU retype grows `V`: the new VCPU
  has its `TCB` word 0, the typed heap's TCBs and slots unchanged, the old extension words kept),
  **`JExtV.shrink`** (deleting a VCPU whose `TCB` word is 0 and that no slot cap names — no `Vcpu` cap, no owned
  IO port — shrinks `V`). These are memory-effect lemmas: tying `grow` to the extracted VT-x retype
  (`create_arch_object` / `vcpu::init`, which zero the object and link it into the VCPU list) is open.
* **`vcpu_finalise_jv`**: the extracted `vcpu.finalise v` (stall, release, detach of its thread, list unlink)
  keeps `JExtV V X th` and `RunVmB th` and leaves `v`'s `TCB` word 0, so `JExtV.shrink` applies once no cap names
  `v` (the TCB finaliser's call of `vcpu::detach`, objects.rs l. 361, is `vcpu_detach_jv` itself).
* **`sts_jv`**: `sched.set_thread_state t x` on a TCB keeps `JExtV`, and keeps `RunVmB` when `x ≠ TS_RUNNING_VM`
  or `t`'s VCPU word is nonzero — the native thread-state step and `vcpu::enter`'s last step (vcpu.rs l. 1119,
  `TS_RUNNING_VM` on a bound thread: gen 19's `RunVmB.enter` on the extracted function); **`vcpu_enter_unbound`**:
  `vcpu.enter` of an unbound thread (vcpu.rs l. 1076) keeps both; **`vcpu_enter_nosig`**: `vcpu.enter` of a bound
  thread with no signal pending on its bound notification (the VMCS / VMCB / `VALID` / `PENDING` writes to the VCPU
  object, then `TS_RUNNING_VM`) keeps both. Open: the signalled branch (`complete_signal`, then `report` or
  `MSG_INFO := 0`, l. 1108-1116) — its footprint (notification words, SC donation) is not proved here.

Named premises, all [J] (placement, as in P3/JExtVSteps): `JWPl`, `DetPl`, `DetAt`, and `FinPl` (the VCPU's
`NEXT` / `PREV` words and its list neighbours' link words / the list head are aligned, none of `JW` / `SW`, the
VCPU's own link words none of the detach words `CW`; P1's `VtIoPlace` / `VListed` placement); `sts_jv`'s
`hact` (the current core's `SCHED_ACTION` word aligned and none of `JW` / `SW`); `vcpu_enter_nosig`'s `hvi` (the
bound VCPU's internal words `VW` aligned and none of `JW` / `SW`) and `hns` (the no-signal branch condition after
those writes). No [P] / [W] / [S] premise.
-/
import Fl4Proofs.P3.JExtVSteps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

theorem VtxCap.mono {V V' X X' : Set U64} (hV : V ⊆ V') (hX : X ⊆ X') {c : capability.Cap}
    (h : VtxCap V X c) : VtxCap V' X' c := by
  cases c with
  | Vcpu p => exact hV h
  | Ept p l m a v => exact hX h
  | Frame p sz r d m e a v =>
    have h' : m = true ∧ e = true → X.Nonempty := h
    exact fun hme => (h' hme).mono hX
  | IoPort f l o =>
    have h' : o ≠ 0#u64 → o ∈ V := h
    exact fun ho => hV (h' ho)
  | _ => trivial

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V X : Set U64} {th : TypedHeap} {s s' : S}

/-- **An EPT retype grows `X`.** -/
theorem JExtV.mono_X (E : JExtV (L := L) V X th s) {X' : Set U64} (hX : X ⊆ X') : JExtV (L := L) V X' th s where
  cap y hy := VtxCap.mono (fun _ h => h) hX (E.cap y hy)
  bnd := E.bnd
  back := E.back
  nz := E.nz

/-- **A VCPU retype grows `V`** (memory level, module docstring): the new VCPU `v ≠ 0` has its `TCB` word 0, the
typed heap keeps its TCBs and slots, and the step's footprint misses the old extension words. -/
theorem JExtV.grow (E : JExtV (L := L) V X th s) (P : JWPl V th) {v : U64} (hv0 : v ≠ 0#u64)
    {th' : TypedHeap} (htc : ∀ t, th' t = some .tcb ↔ th t = some .tcb) (hsl : ∀ y, IsSlot th' y → IsSlot th y)
    {W : U64 → Prop} (hW : P1.WritesIn st s s' W) (hd : ∀ b, W b → ¬ JW V th b)
    (hb : L.mem s' (vTcbA v) = 0#u64) : JExtV (L := L) (insert v V) X th' s' := by
  have E' := E.of_writes P hW hd
  refine ⟨fun y hy => VtxCap.mono (Set.subset_insert v V) (fun _ h => h) (E'.cap y (hsl y hy)),
    fun t ht => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rcases E'.bnd t ((htc t).1 ht) with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨Set.mem_insert_of_mem v h1, h2⟩
  · rcases Set.mem_insert_iff.1 hw with rfl | hw'
    · exact Or.inl hb
    · rcases E'.back w hw' with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨(htc _).2 h1, h2⟩
  · rcases Set.mem_insert_iff.1 hw with rfl | hw'
    · exact hv0
    · exact E'.nz w hw'

/-- **Deleting a VCPU shrinks `V`** (memory level): its `TCB` word 0, no slot cap a `Vcpu` cap to it or an IO
port cap it owns. -/
theorem JExtV.shrink (E : JExtV (L := L) V X th s) {v : U64} (hb : L.mem s (vTcbA v) = 0#u64)
    (h0 : th 0#u64 ≠ some .tcb)
    (hc : ∀ y, IsSlot th y → capV (L.mem s) y ≠ .Vcpu v ∧ ∀ f l, capV (L.mem s) y ≠ .IoPort f l v) :
    JExtV (L := L) (V \ {v}) X th s := by
  refine ⟨fun y hy => ?_, fun t ht => ?_, fun w hw => E.back w hw.1, fun w hw => E.nz w hw.1⟩
  · have h := E.cap y hy
    obtain ⟨hc1, hc2⟩ := hc y hy
    revert h hc1 hc2
    cases capV (L.mem s) y with
    | Vcpu p =>
      intro h hc1 _
      exact Set.mem_diff_of_mem h fun e => hc1 (by rw [Set.mem_singleton_iff.1 e])
    | IoPort f l o =>
      intro h _ hc2 ho
      exact Set.mem_diff_of_mem (h ho) fun e => hc2 f l (by rw [Set.mem_singleton_iff.1 e])
    | Ept p l m a w => intro h _ _; exact h
    | Frame p sz r d m e a w => intro h _ _; exact h
    | _ => intro _ _ _; trivial
  · rcases E.bnd t ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · refine Or.inr ⟨Set.mem_diff_of_mem h1 fun e => ?_, h2⟩
      rw [Set.mem_singleton_iff.1 e, hb] at h2
      rw [← h2] at ht
      exact h0 ht

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {V X : Set U64} {th : TypedHeap} {Ub : U64 → Set U64}

/-- **`sched.set_thread_state t x` keeps the extension** (module docstring): `JExtV` always; `RunVmB` when
`x ≠ TS_RUNNING_VM` or `t`'s VCPU word is nonzero. `hact` [J]: the current core's `SCHED_ACTION` word aligned and
none of `JW` / `SW`. -/
theorem sts_jv (P : JWPl V th) {s : S} (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) {t x : U64}
    (ht : th t = some .tcb)
    (hact : P1.Aligned (actA st s) ∧ ¬ JW V th (actA st s) ∧ ¬ SW th (actA st s))
    (hx : x ≠ 8#u64 ∨ L.mem s (tVcpuA t) ≠ 0#u64) :
    sched.set_thread_state st s t x ⦃ s' => JExtV (L := L) V X th s' ∧ RunVmB (L := L) th s' ⦄ := by
  have hS : SW th (P1.stA t) := ⟨t, ht, rfl⟩
  have hne : actA st s ≠ P1.stA t := fun e => hact.2.2 (e ▸ hS)
  refine WP.spec_mono (sts_w s t x (P.sw _ hS) hact.1 hne) fun s' ⟨w, m⟩ => ?_
  have hd : ∀ b, (b = P1.stA t ∨ b = actA st s) → ¬ JW V th b := by
    rintro b (e | e)
    · exact P.swjw b (e ▸ hS)
    · exact e ▸ hact.2.1
  refine ⟨E.of_writes P w hd, R.of_foot P w (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)⟩
  · rcases hw with e | e
    · rw [stA_inj e, m]
      have J : JW V th (tVcpuA t) := Or.inr (Or.inl ⟨t, ht, rfl⟩)
      rw [w.mem_eq (P.jw _ J) fun h => hd _ h J]
      exact hx
    · exact (hact.2.2 (e ▸ (⟨t', ht', rfl⟩ : SW th (P1.stA t')))).elim
  · have J : JW V th (tVcpuA t') := Or.inr (Or.inl ⟨t', ht', rfl⟩)
    exact (hd _ hw J).elim

/-- **`vcpu.enter` of an unbound thread** (vcpu.rs l. 1076: `MSG_INFO := 0`, a register word of the thread)
keeps the extension. -/
theorem vcpu_enter_unbound (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S}
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (a : A) {t : U64} (ht : th t = some .tcb)
    (h0 : L.mem s (tVcpuA t) = 0#u64) :
    vcpu.enter st ar s a t ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ⦄ := by
  have P := D.pl
  unfold vcpu.enter vcpu.bound
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  have ev' : v = L.mem s (tVcpuA t) := ev
  rw [if_pos (ev'.trans h0)]
  refine WP.spec_bind (P1.obj.Tcb.set_reg.wrS s t layout.reg.MSG_INFO 0#u64 (D.ta t ht)
    (by simp [layout.reg.MSG_INFO, layout.reg.RSI])) fun s1 ⟨K, hK, e⟩ => ?_
  subst e
  have hr : (layout.reg.MSG_INFO).val = 1 := by simp [layout.reg.MSG_INFO, layout.reg.RSI]
  have hw := P1.writesIn_wr (st := st) (s := s) (v := 0#u64)
    (P1.field_aligned (D.ta t ht) (K := K) (by omega) (by omega))
  have hR : P1.RepW t (Ub t) (core.num.U64.wrapping_add t K) := Or.inl ⟨K, by omega, by omega, by omega, rfl⟩
  have hd : ∀ b, b = core.num.U64.wrapping_add t K → ¬ JW V th b ∧ ¬ SW th b := fun b e =>
    e ▸ D.rep t ht _ hR
  exact (WP.spec_ok _).2 ⟨E.of_writes P hw fun b h => (hd b h).1, R.of_clean P hw hd⟩

/-- The VCPU-internal words of `v` other than its `TCB` word (`vcpu::enter`'s VMCS / VMCB / `VALID` / `PENDING`
writes). -/
def VW (v : U64) (b : U64) : Prop :=
  ∃ o : U64, o.val < 32768 ∧ o.val % 8 = 0 ∧ o.val ≠ 20480 ∧ b = core.num.U64.wrapping_add v o

set_option maxHeartbeats 16000000 in
/-- **`vcpu.enter` of a bound thread with no signal pending** (vcpu.rs l. 1073-1120, the branch ending in
`TS_RUNNING_VM`): keeps `JExtV` and `RunVmB` (gen 19's `RunVmB.enter` on the extracted function). `hvi` [J]: the
bound VCPU's internal words (offsets below 2^15 other than `TCB`) are aligned and none of `JW` / `SW` (the VCPU
object, `.other 15`, apart from TCBs / CNodes; P1's `vcpu_obj_aligned`). `hns` [J]: after those writes the bound
notification is 0 or not active — the branch condition; the signalled branch (`complete_signal`, l. 1108) is
open. -/
theorem vcpu_enter_nosig (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAt st V th Ub s)
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


/-- **The VCPU list's placement at a finalise** [J] (module docstring). -/
structure FinPl (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap)
    (Ub : U64 → Set U64) (s : S) (v : U64) : Prop where
  own : ∀ b, (b = P1.vNextA v ∨ b = vPrevA v) → P1.Aligned b ∧ ¬ JW V th b ∧ ¬ CW st V th Ub s b
  nbr : ∀ b, (b = P1.vHeadA st s ∨ (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v))) ∨
    (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))) →
    P1.Aligned b ∧ ¬ JW V th b ∧ ¬ SW th b

set_option maxHeartbeats 8000000 in
/-- **`vcpu.finalise` keeps the extension** (module docstring) and leaves the VCPU's `TCB` word 0. -/
theorem vcpu_finalise_jv (hA : P0.ArchTotal ar) (D : DetPl V th Ub) {s : S} (Da : DetAt st V th Ub s)
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
  have Da1 : DetAt st V th Ub s1 := Da.mono (w1'.mono fun b e => Or.inr (Or.inl e))
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
      refine WP.spec_mono (vcpu_detach_jv hA D Da1 E1 R1 a2 htt) fun r Pd => ?_
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
