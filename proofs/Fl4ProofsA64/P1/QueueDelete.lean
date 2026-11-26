-- AArch64 port of Fl4Proofs.P1.QueueDelete (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
-- a64: `thread_control_sched.blkE` takes `hrv` and named premise [J] `hinstR` (for AArch64's `blkC`);
-- `QueueDeleteRv` has the `_d` forms without it.
/-
P1: deleting a TCB cap slot that holds a null or an endpoint cap
(`cdt::delete` with `exposed`, as the fault-handler install of
`install_tcb_cap` does) keeps `BlkOK` with the `CaiFr` frame, and so does
the whole `install_tcb_cap` when the slot writes of `empty_slot` and
`insert` stay in cap-slot words (`CapW`), which the P3 side gets from its
slot frames.
-/
import Fl4ProofsA64.P1.QueueCaiFr
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The cap of a slot is null or an endpoint cap of the heap. -/
def NullOrEp (H : Heap) (c : capability.Cap) : Prop :=
  c = .Null ∨ ∃ ep b0 b1 b2 b3 b4, c = .Endpoint ep b0 b1 b2 b3 b4 ∧ H ep = some .ep

/-- A footprint step keeps every cap-slot word. -/
theorem foot_keeps_capw {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (f : Foot st T Cs Sg Scs Z (EH H) s s') :
    ∀ b, Aligned b → CapW T Ω Sg b → L.mem s' b = L.mem s b :=
  fun b hb hc => f.mem_eq hb fun hk => capw_not_kw h hc hb (le_refl _) (by omega) hk

/-- **`finalise_slot_immediate` of a null or endpoint cap**: the first round
ends the loop (an endpoint cap is finalised by `cancel_all_ipc` when final
and leaves nothing to clean up). -/
theorem cdt.finalise_slot_immediate.ep {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (slot : obj.Slot)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcap : obj.Slot.cap st slot s ⦃ c => NullOrEp H c ⦄) :
    cdt.finalise_slot_immediate st ar s a slot ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ Foot st T Cs Sg Scs Z (EH H) s r.2.1 ∧
      CaiFr st T Scs 0#u64 s r.2.1 ∧ (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ∧
      ∀ v, r.1 = .Ok v → v.cleanup = .Null ⦄ := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  apply loop.spec_decr_nat (measure := fun x => x.2.2.val) (inv := fun x => x.1 = s ∧ x.2.1 = a)
  · rintro ⟨s1, a1, f⟩ ⟨e1, e2⟩
    simp only at e1 e2
    subst e1 e2
    dsimp only
    unfold cdt.finalise_slot_immediate_loop.body
    split
    · rename_i hfuel
      step as ⟨fuel1, hf1⟩
      refine WP.spec_bind hcap fun c hc => ?_
      rcases hc with rfl | ⟨ep, b0, b1, b2, b3, b4, rfl, hH⟩
      · simp only [capability.Cap.is_null, bind_ok, if_true, WP.spec_ok]
        exact ⟨h, Foot.refl _, CaiFr.refl _ _, by first | trivial | exact Or.inl rfl | exact Or.inl trivial, fun v e => by cases e; rfl⟩
      · simp only [capability.Cap.is_null, bind_ok, Bool.false_eq_true, ite_false]
        refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 slot
          (.Endpoint ep b0 b1 b2 b3 b4) L.total) fun fin _ => ?_
        unfold objects.finalise_cap
        simp only [bind_ok]
        refine WP.spec_bind (fin_endpoint.fr (ar := ar) s1 a1 ep b0 b1 b2 b3 b4 fin h hH) ?_
        rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨e1, -, h2, f2, F2, ha2⟩
        simp only [Prod.mk.injEq] at e1
        obtain ⟨rfl, rfl⟩ := e1
        have hm : ({ep} : Set U64) ⊆ EH H := fun x hx => by
          rw [Set.mem_singleton_iff.1 hx]; exact Or.inl hH
        simp only [uncurry_apply_pair, WP.uncurry'_pair, cdt.cap_removable, bind_ok, if_true, WP.spec_ok]
        exact ⟨h2, f2.mono hm, F2, ha2, fun v e => by cases e; rfl⟩
    · simp only [WP.spec_ok]
      exact ⟨h, Foot.refl _, CaiFr.refl _ _, by first | trivial | exact Or.inl rfl | exact Or.inl trivial, fun v e => by cases e⟩
  · exact ⟨rfl, rfl⟩

/-- **`cdt::delete` (exposed) of a slot holding a null or endpoint cap**:
the finalisation, then `empty_slot`, which writes only cap-slot words from a
state agreeing with `s` on them (`hes`, with any further fact `P` about its
result). -/
theorem cdt.delete.ep {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (slot : obj.Slot)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcap : obj.Slot.cap st slot s ⦃ c => NullOrEp H c ⦄)
    {P : S → Prop}
    (hes : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 slot .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧ P r.1 ⦄) :
    cdt.delete st ar s a slot true ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ CaiFr st T Scs 0#u64 s r.2.1 ∧
      (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ∧ (r.1 = .Ok () → P r.2.1) ⦄ := by
  unfold cdt.delete
  simp only [if_true]
  refine WP.spec_bind (cdt.finalise_slot_immediate.ep (ar := ar) s a slot h hcap) ?_
  rintro ⟨r, s1, a1⟩ ⟨h1, f1, F1, ha1, hcl⟩
  have hT := h1.1.choose_spec.choose_spec.tcbs
  simp only [uncurry_apply_pair, WP.uncurry'_pair] at hcl ⊢
  cases r with
  | Ok v =>
    have hv := hcl v rfl
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, hv]
    refine WP.spec_bind (hes s1 a1 (foot_keeps_capw h f1)) ?_
    rintro ⟨s2, a2⟩ ⟨w2, hP⟩
    obtain ⟨h2, -, -, -, ea2, -, -, -⟩ := blk_of_capw h1 w2 (fun b hb => hb)
    simp only [uncurry_apply_pair, WP.uncurry'_pair, WP.spec_ok]
    exact ⟨h2, F1.trans hT (CaiFr.of_capw h1 w2 (fun b hb => hb)), by rw [ea2]; exact ha1, fun _ => hP⟩
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok]
    refine WP.spec_bind (Pₘ := fun r1 => ∃ v, r1 = core.result.Result.Err v)
      (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial) fun v _ => (WP.spec_ok _).2 ⟨v, rfl⟩) ?_
    rintro r1 ⟨v, rfl⟩
    exact (WP.spec_ok _).2 ⟨h1, F1, ha1, fun e' => by cases e'⟩

/-- **`install_tcb_cap` over a slot holding a null or endpoint cap** (the
fault-handler install of `thread_control_sched`): `BlkOK` with the `CaiFr`
frame and the scheduler action kept or `CHOOSE_NEW`, which is what
`tcb.thread_control_sched.blkC` asks of its `hinst`.  `hslot` is the slot
part, from a state that agrees with `s` on the cap-slot words: `empty_slot`
writes only cap-slot words, and so does `still_valid`'s `insert`. -/
theorem tcb.install_tcb_cap.cai {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (target : obj.Tcb)
    (slot : obj.Slot) (index : U64) (new_cap : capability.Cap) (src : obj.Slot) (root : U64)
    (hroot : obj.Tcb.slot target index = ok root) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot new_cap src ⦃ b1 => b1 = true →
          cdt.insert st r.1 new_cap src root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄) :
    tcb.install_tcb_cap st ar s a target slot index new_cap src ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ CaiFr st T Scs 0#u64 s r.2.1 ∧
      (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64) ⦄ := by
  unfold tcb.install_tcb_cap
  rw [hroot]
  simp only [bind_ok]
  refine WP.spec_bind (cdt.delete.ep (ar := ar) s a root h hcap
    (P := fun s2 => tcb.still_valid st s2 target slot new_cap src ⦃ b1 => b1 = true →
      cdt.insert st s2 new_cap src root ⦃ s3 => WritesIn st s2 s3 (CapW T Ω Sg) ⦄ ⦄) hslot) ?_
  rintro ⟨r, s2, a2⟩ ⟨h2, F2, ha2, hP⟩
  have hT := h2.1.choose_spec.choose_spec.tcbs
  simp only [uncurry_apply_pair, WP.uncurry'_pair] at hP ⊢
  cases r with
  | Ok u =>
    have hins := hP (by cases u; rfl)
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True)
      (by unfold capability.Cap.is_null; split <;> exact (WP.spec_ok _).2 trivial) fun b _ => ?_
    split
    · exact (WP.spec_ok _).2 ⟨h2, F2, ha2⟩
    · refine WP.spec_bind hins fun b1 hb1 => ?_
      split
      · rename_i e
        refine WP.spec_bind (hb1 e) fun s3 w3 => ?_
        obtain ⟨h3, -, -, -, ea3, -, -, -⟩ := blk_of_capw h2 w3 (fun b hb => hb)
        exact (WP.spec_ok _).2 ⟨h3, F2.trans hT (CaiFr.of_capw h2 w3 (fun b hb => hb)), by rw [ea3]; exact ha2⟩
      · exact (WP.spec_ok _).2 ⟨h2, F2, ha2⟩
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_ok]
    refine WP.spec_bind (Pₘ := fun _ => True)
      (WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial) fun _ _ => (WP.spec_ok _).2 trivial) ?_
    intro _ _
    exact (WP.spec_ok _).2 ⟨h2, F2, ha2⟩

/-- **`thread_control_sched` with the fault-handler install discharged**:
the old fault-handler cap is null or an endpoint cap, and the slot part of
the install stays in cap-slot words (`hslot`, as in `install_tcb_cap.cai`).
a64: `hrv` (caller-level) and named premise **[J] `hinstR`**, passed to AArch64's `blkC`; `blkE_d` in
`QueueDeleteRv` discharges `hinstR` from `hcap` / `hslot`. -/
theorem tcb.thread_control_sched.blkE {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T) (root : U64)
    (hroot : obj.Tcb.slot target layout.tcb.SLOT_FAULT_HANDLER = ok root)
    (hcap : obj.Slot.cap st root s ⦃ c => NullOrEp H c ⦄)
    (hslot : ∀ (s1 : S) (a1 : A), (∀ b, Aligned b → CapW T Ω Sg b → L.mem s1 b = L.mem s b) →
      cdt.empty_slot st ar s1 a1 root .Null ⦃ r => WritesIn st s1 r.1 (CapW T Ω Sg) ∧
        tcb.still_valid st r.1 target slot fh.1 fh.2 ⦃ b1 => b1 = true →
          cdt.insert st r.1 fh.1 fh.2 root ⦃ s3 => WritesIn st r.1 s3 (CapW T Ω Sg) ⦄ ⦄ ⦄)
    (hprio : (flags &&& tcb.SCHED_UPDATE_PRIO) ≠ 0#u64 → prio.val < 256 ∧ (target = L.curW s →
      (L.mem s (inqA target) &&& sched.Q_RELEASE) = 0#u64 ∧ L.mem s (scA target) ≠ 0#u64 ∧
        L.mem s (scA target) ∈ Ac))
    (hbind : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → sc ∈ Scs ∧ L.mem s (scA target) = 0#u64 ∧
      L.mem s (scTcbA sc) = 0#u64 ∧ (BlockedR (L.mem s (stA target)) → sc ∈ Ac))
    (hunb : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc = 0#u64 → L.actionW s ≠ target ∧ L.idleW s ≠ target)
    (hrv : (flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → sc ≠ 0#u64 → L.mem s (runVcpuA target) = 0#u64)  -- a64
    (hinstR : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      L.mem r.2.1 (runVcpuA target) = L.mem s (runVcpuA target) ⦄) :  -- a64: [J]
    tcb.thread_control_sched st ar s a target slot fh mcp prio sc flags ⦃ r =>
      BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  tcb.thread_control_sched.blkC hA s a target slot fh mcp prio sc flags h ht
    (tcb.install_tcb_cap.cai s a target slot _ fh.1 fh.2 root hroot h hcap hslot) hprio hbind hunb hrv hinstR

end

end Fl4ProofsA64.P1
