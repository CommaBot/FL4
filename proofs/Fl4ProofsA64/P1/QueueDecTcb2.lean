/-
P1 (aarch64): InvGaps' `thread` family, continued (port of Fl4Proofs.P1.QueueDecTcb2, reworked for AArch64):
`CopyRegisters` and the other labels on top of QueueDecTcb's / QueueDecTcbRR's, `SetSchedParams` from `SspHyps`,
the AArch64 labels `SetPACKeys`, `SetHighVSpace` and `SetEPTRoot` (Stage-2), and the family's decode
(`tcb.decode.dec`, `decGap_thread`).

a64 (beyond the x86_64 text):
* **Install chain over the seven slots** (`W7`): `tcb.install_tcb_cap.cur0` (index < 7) and `tcb.install_buffer.cur0`
  delete the old cap with `W7.cdt.delete.cur0` (`W7.DelGaps`, QueueSlots7) and insert with `TcbPlace7.ins7`; the
  insert's writes are `W7.CapW` writes (`Cur0.capw7`). So `SetHighVSpace` (slot 6, TCB offsets 192–223, not an
  x86-shaped `CapW` word) is proved: the HIGH_VSPACE `hslot` gap is closed. `SetIPCBuffer` is re-proved over
  `W7.DelGaps` (`tcb.decode_set_ipc_buffer.dec7`, QueueDecTcb's text).
* **Suspend of a thread in an `ARMVCPURun`**: `sched.suspend` starts with `vcpu::cancel_run`; `sched.suspend.blk7`
  / `.rr7` use QueueFinThr7's `vcpu.cancel_run.w7` and then the old proof from the state with `RUN_VCPU = 0`
  (`vcpu.cancel_run.eq0`). So `Suspend`, `CopyRegisters` (suspend of the source) and `ReadRegisters`
  (`tcb.decode_read_registers.dec7`) need no `hrv`; they take the run VCPU's `RUN_CALLER` word as a user word
  (`TcbPlace7.rcw`).
* `SetPACKeys` (`tcb.decode_set_pac_keys.dec`): the ten key words, `PAC_FLAGS`, `PAC_EPOCH` are TCB words below 3328
  (`XferFoot`), the epoch from the arch (`next_pac_epoch`).
* `SetEPTRoot` (A64: a Stage-2 `Ept` cap into `SLOT_EPT`, then the caller's restart, `Cur0.restartEnd`) is proved
  inside `tcb.decode.dec`: **x86_64's named gap `TcbGaps.setEPTRoot` is not needed on AArch64** (`decGap_thread`
  takes `SspHyps` only).
* `ConfigureSingleStepping` is a no-op on AArch64 (`debug.configure_single_stepping.rf`).

Named premises: `SspHyps` (as x86_64); **[P] `TcbPlace7`**: `rcw` (W7.DelPlaceAt.rcw's shape at `Fr0` states of a
decode) and `ins7` (`CdtHyps.ins` with the target a W7 cap-slot word). Removed against x86_64: `TcbGaps.setEPTRoot`.
-/
import Fl4ProofsA64.P1.QueueDecTcbRR
import Fl4ProofsA64.P1.QueueFinThr7
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-! ## AArch64 placement facts of the thread family -/

/-- **[P] The thread family's AArch64 placement facts** (P3's):
* `rcw`: at a state inside a decode (`Fr0` from the decode's start), a thread's run VCPU's `RUN_CALLER` word is a
  user word (VCPUs are heap objects outside the TCBs, nodes, cap slots and endpoints; the kind and shape of
  `W7.DelPlaceAt.rcw` and VcpuCheckInv's `hpw`). Used by `Suspend`, `CopyRegisters` and `ReadRegisters` when the
  suspended thread is in an `ARMVCPURun`.
* `own`: the same for the run VCPU's `OWNER_CPU` word (`SetSchedParams`' SC bind migrates a running VCPU:
  QueueScBindVm's [P] `ScBindOwn` at the `Fr0` states of a decode).
* `ins7`: `CdtHyps.ins` with the target a W7 cap-slot word (the seventh TCB slot `SLOT_HIGH_VSPACE` included). -/
structure TcbPlace7 (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop where
  rcw : ∀ (Ac : Set U64) (s0 s : S) (p : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
    UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA p)) vcpu.RUN_CALLER)
  own : ∀ (Ac : Set U64) (s0 s : S) (p : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → p ∈ T → L.mem s (runVcpuA p) ≠ 0#u64 →
    UserW st T Cs Ω H s (ownA (L.mem s (runVcpuA p)))
  ins7 : ∀ (Ac : Set U64) (s0 s : S) (c srcC : capability.Cap) (x y : U64), EntAt st P3Ok s0 →
    Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CapW T Ω Sg x → W7.CapW T Ω Sg y →
    cdt.insert_with_cap st s c srcC x y ⦃ s' => WritesIn st s s' (W7.CapW T Ω Sg) ⦄

/-! ## Suspend of any thread -/

/-- `cancel_run` of a thread that runs no VCPU returns its state. -/
theorem vcpu.cancel_run.eq0 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : U64)
    (h : L.mem s (runVcpuA t) = 0#u64) : vcpu.cancel_run st ar s a t = ok (s, a) := by
  unfold vcpu.cancel_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq]
  unfold runVcpuA at h
  simp [h]

/-- **`sched.suspend` of any thread** (an `ARMVCPURun` in flight or not): `BlkOK`. -/
theorem sched.suspend.blk7 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hna : L.actionW s ≠ t)
    (hrc : L.mem s (runVcpuA t) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA t)) vcpu.RUN_CALLER)) :
    sched.suspend st ar s a t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  unfold sched.suspend
  refine WP.spec_bind (vcpu.cancel_run.w7 s a t h ht hrc) ?_
  rintro ⟨s1, a1⟩ ⟨-, h1, rv1, -, ani1, -, -⟩
  have hs := sched.suspend.blk (ar := ar) s1 a1 t h1 ht (by rw [ani1.1]; exact hna) rv1
  unfold sched.suspend at hs
  rw [vcpu.cancel_run.eq0 s1 a1 t rv1] at hs
  simp only [bind_ok] at hs
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  exact WP.spec_mono hs fun r hr => by obtain ⟨s2, a2⟩ := r; exact hr.1

/-- **`sched.suspend` of any thread, ReadRegisters' form**: `BlkOK`, the kernel-stack base, the caller not blocked,
and `XG` kept. -/
theorem sched.suspend.rr7 {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) (hna : L.actionW s ≠ t) (hct : L.curW s ∈ T)
    (hnb : ¬ BlockedR (L.mem s (stA (L.curW s)))) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hrc : L.mem s (runVcpuA t) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA t)) vcpu.RUN_CALLER)) :
    sched.suspend st ar s a t ⦃ s' _ => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ L.ksb s' = L.ksb s ∧
      ¬ BlockedR (L.mem s' (stA (L.curW s))) ∧ XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  unfold sched.suspend
  refine WP.spec_bind (vcpu.cancel_run.w7 s a t h ht hrc) ?_
  rintro ⟨s1, a1⟩ ⟨-, h1, rv1, w1, ani1, -, fld1⟩
  have hT := h.1.choose_spec.choose_spec.tcbs
  have nb1 : ¬ BlockedR (L.mem s1 (stA (L.curW s))) := by
    rw [stA_eq, fld1 _ hct 3328#u64 (by simp) (by simp) (by simp) (fun _ => by simp), ← stA_eq]; exact hnb
  have wc : WritesIn st s s1 (Cur0W st T Cs Ω H Sg Scs Z s) := w1.mono fun b hb => by
    rcases hb with hb | hb
    · exact Or.inr (Or.inr (Or.inr hb))
    · exact Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp))
  have hG1 := hG.of_fr wc
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h1
  have hs := WP.spec_and (sched.suspend.blk (ar := ar) s1 a1 t ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ ht
      (by rw [ani1.1]; exact hna) rv1)
    (sched.suspend.curR (ar := ar) s1 a1 t (L.curW s) Q R h0 ht hB hX hSg hS (by rw [ani1.1]; exact hna)
      (hX.2.2.yt.2.1 t ht) hct rv1)
  unfold sched.suspend at hs
  rw [vcpu.cancel_run.eq0 s1 a1 t rv1] at hs
  simp only [bind_ok] at hs
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine WP.spec_mono hs fun r hr => ?_
  obtain ⟨s2, a2⟩ := r
  obtain ⟨⟨h2, f2⟩, ⟨-, -, -, -, nb⟩⟩ := hr
  exact ⟨h2, f2.1.trans w1.1, nb nb1, hG1.foot f2⟩

/-! ## Small AArch64 steps -/

/-- The caller's restart at the end of a step inside a decode keeps `Cur0`. -/
theorem Cur0.restartEnd {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  have nb := h.nb
  refine WP.spec_mono (sched.set_thread_state.restart_blk (Es := ∅) s _ hb.blk hct (fun h' => nb (Or.inl h'))
    (fun e => nb (Or.inr e))) fun s' ⟨h', f', est, k⟩ => ?_
  exact Cur0.mk h (BlkOK.bxi h') k.curW k.cscW (Or.inl (k.scf hct)) k.act (Or.inr (by rw [est]; exact nbr_restart))
    (WritesIn.mono f' fun _ hb => Or.inl (KW.mono hb (Set.empty_subset _)))

/-- `tcb::extra(c, 0)`: a non-null extra slot. -/
theorem tcb.extra.mem0 (c : tcb.Ctx) :
    tcb.extra c 0#usize ⦃ o => ∀ x, o = some x → x ∈ c.extra.val ∧ x ≠ 0#u64 ⦄ := by
  unfold tcb.extra
  have hl0 : (0#usize).val < c.extra.val.length := by rw [c.extra.property]; simp
  simp only [show ¬ (0#usize ≥ 3#usize) by simp, ↓reduceIte]
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec c.extra 0#usize hl0) fun sl hsl => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 fun x e => by cases e
  · rename_i h0
    exact (WP.spec_ok _).2 fun x e => by
      cases e; exact ⟨hsl ▸ List.getElem_mem hl0, by simpa using h0⟩

/-- A TCB word below 3328 is an `XferFoot` word. -/
theorem tcb_wr_rf {s : S} {t K v : U64} (hT : TcbPlaced T) (ht : t ∈ T) (hK : K.val < 3328) (h8 : K.val % 8 = 0) :
    WritesIn st s (L.wr s (core.num.U64.wrapping_add t K) v) (XferFoot T ∅) :=
  (writesIn_wr (field_aligned (hT t ht) (by omega) h8)).mono fun _ e => Or.inl ⟨t, ht, K, hK, h8, e⟩

/-! ## `SetPACKeys` -/

/-- `write_pac_keys`' loop: the ten key words (TCB offsets 1696..1768). -/
theorem tcb.write_pac_keys_loop.rf {s0 s : S} {t i : U64} {keys : Aeneas.Std.Array U64 10#usize}
    (hT : TcbPlaced T) (ht : t ∈ T) (h : WritesIn st s0 s (XferFoot T ∅)) :
    tcb.write_pac_keys_loop st s t keys i ⦃ s' => WritesIn st s0 s' (XferFoot T ∅) ⦄ := by
  unfold tcb.write_pac_keys_loop
  apply loop.spec_decr_nat (measure := fun y => 10 - y.2.2.val)
    (inv := fun y => y.2.1 = t ∧ WritesIn st s0 y.1 (XferFoot T ∅))
  · rintro ⟨s1, t1, j⟩ ⟨e1, h1⟩
    simp only at e1 h1
    subst t1
    try dsimp only
    unfold tcb.write_pac_keys_loop.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 10 := by scalar_tac
    try simp only [lift, bind_ok]
    step as ⟨i2, hi2⟩
    try simp only [lift, bind_ok]
    have hl : (UScalar.cast .Usize j : Usize).val < keys.val.length := by
      rw [keys.property, cast_usize_small (by omega)]; simp; omega
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ hl) fun v _ => ?_
    refine WP.spec_bind (LawfulStore.write_spec _ _ v) fun s2 e2 => ?_
    subst e2
    step as ⟨j2, hj2⟩
    have eK : core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.PAC_KEYS) i2 =
        core.num.U64.wrapping_add t (core.num.U64.wrapping_add layout.tcb.PAC_KEYS i2) := by
      apply UScalar.eq_of_val_eq
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      omega
    have hKv : (core.num.U64.wrapping_add layout.tcb.PAC_KEYS i2).val = 1696 + j.val * 8 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have W : WritesIn st s0 (L.wr s1 (core.num.U64.wrapping_add (core.num.U64.wrapping_add t layout.tcb.PAC_KEYS) i2) v)
        (XferFoot T ∅) := rf_trans h1 (by rw [eK]; exact tcb_wr_rf hT ht (by omega) (by omega))
    first
      | exact ⟨⟨rfl, W⟩, by omega⟩
      | exact ⟨W, by omega⟩
      | exact ⟨⟨rfl, W⟩, by simp only; omega⟩
      | exact ⟨W, by simp only; omega⟩
  · exact ⟨rfl, h⟩

set_option hygiene false in
/-- `SetPACKeys`' tail after the caller's restart (`h2 : BlkOK … s2`, arch state `a1`). -/
local macro "pacTail" : tactic => `(tactic| (
  repeat (refine WP.spec_bind (P0.tcb.arg.p0 st s2 _ _ hS) fun _ _ => ?_)
  refine WP.spec_bind (tcb.write_pac_keys_loop.rf (s0 := s2) hT ht (WritesIn.refl _ _)) fun s3 w3 => ?_
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec s3 _ flags) fun s4 e4 => ?_
  subst e4
  refine WP.spec_bind (hA.next_pac_epoch a1) ?_
  rintro ⟨ep, a3⟩ -
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec _ _ ep) fun s5 e5 => ?_
  subst e5
  have w5 := rf_trans (rf_trans w3 (tcb_wr_rf (v := flags) (K := layout.tcb.PAC_FLAGS) hT ht (by simp) (by simp)))
    (tcb_wr_rf (v := ep) (K := layout.tcb.PAC_EPOCH) hT ht (by simp) (by simp))
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_rf h2 w5).1))
  ))

/-- **`SetPACKeys`** after the stall: the caller's restart, then TCB words below 3328 (`XferFoot`). -/
theorem tcb.decode_set_pac_keys.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_pac_keys st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  unfold tcb.decode_set_pac_keys
  split
  · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  simp only [lift, bind_ok]
  split
  · simp only [error.invalid_arg, bind_ok]; exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
  split
  · refine WP.spec_bind (hA.has_pauth a1) fun b _ => ?_
    split
    · refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
      pacTail
    · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
  · refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    pacTail

/-! ## `ReadRegisters` with the suspend of any thread -/

set_option maxHeartbeats 8000000 in
/-- **`read_registers`** from the caller `curW s` not blocked: the invariants after. -/
theorem tcb.read_registers.bxi7 {A : Type _} {ar : machine.Arch A} (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {src n : U64} {sus call : Bool} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hs : src ∈ T)
    (hna : L.actionW s ≠ src) (hct : L.curW s ∈ T) (hnb : ¬ BlockedR (L.mem s (stA (L.curW s))))
    (hU : UserOK st T Cs Ω H U s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hrc : L.mem s (runVcpuA src) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA src)) vcpu.RUN_CALLER)) :
    tcb.read_registers st ar s a src sus n call ⦃ r => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := by
  unfold tcb.read_registers
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.ksb r.1 = L.ksb s ∧
      ¬ BlockedR (L.mem r.1 (stA (L.curW s))) ∧ XG st T Cs Ω H Sg Scs Z P3Ok r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.suspend.rr7 s a src h hs hna hct hnb hG hrc) fun r hr => by
        obtain ⟨s1, a1⟩ := r; exact hr
    · exact (WP.spec_ok _).2 ⟨h, rfl, hnb, hG⟩
  rintro ⟨s1, a1⟩ ⟨h1, k1, nb1, hG1⟩
  try simp only [uncurry_apply_pair]
  split
  swap
  · exact WP.spec_bind (sched.set_thread_state.running_nbr h1.bxi hct nb1) fun s2 h2 => (WP.spec_ok _).2 h2
  obtain ⟨Q1, R1, x1⟩ := BXI.xs (sx := 0#u64) (BlkOK.bxi h1) (hU.ksb k1)
  have x1s := x1
  have TL : ∀ (s' : S) (x y : U64), XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q1 R1 0#u64 s1 s' →
      (do
        let i ← lift (core.num.U64.wrapping_add x y)
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 i
        let s5 ← msg.set_msg_info st s' (L.curW s) mi
        let s6 ← sched.set_thread_state st s5 (L.curW s) sched.TS_RUNNING
        ok (s6, a1)) ⦃ r => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ⦄ := fun s' x y x' => by
    simp only [lift, bind_ok]
    refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
    refine WP.spec_bind (Pₘ := fun s5 => XS st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q1 R1 0#u64 s1 s5) ?_ fun s5 x5 => ?_
    · unfold msg.set_msg_info
      exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
        obj.Tcb.set_reg.xs (v := w) x' hct (by simp [layout.reg.MSG_INFO, layout.reg.X1])
    have est : L.mem s5 (stA (L.curW s)) = L.mem s1 (stA (L.curW s)) := by
      rw [stA_eq]; exact x5.fr.2.2.2.2.1 _ hct 3328#u64 (by simp) (by simp) (by simp) (fun _ => by simp)  -- a64: `XferFrA`
    refine WP.spec_bind (sched.set_thread_state.running_nbr x5.bxi hct (est ▸ nb1)) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 h6
  refine WP.spec_bind (E.buf _ _ _ _ s1 (L.curW s) hG1 x1.1 hct) fun buf hb => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.xs (v := 0#u64) x1s hct (by simp [layout.reg.BADGE, layout.reg.X0]))
    fun s2 x2 => ?_
  refine WP.spec_bind (tcb.read_registers_loop0.xs x2 hct) ?_
  rintro ⟨s3, i⟩ x3
  try simp only [uncurry_apply_pair]
  -- the remaining tree: loops, then the tail
  have B0 : ∀ {b : Bool}, (buf != 0#u64) = b → b = true → buf ≠ 0#u64 := fun {b} hb hb' => by
    subst hb'; simpa using hb
  repeat' (first
    | exact TL _ _ _ ‹_›
    | (refine WP.spec_bind (tcb.read_registers_loop1.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop3.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop5.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop7.xs ‹_› hb (by simpa using ‹(buf != 0#u64) = true›)) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop2.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop4.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | (refine WP.spec_bind (tcb.read_registers_loop6.xs ‹_› hct) ?_
       rintro ⟨_, _⟩ _; try simp only [uncurry_apply_pair])
    | split
    | (step as ⟨_, _⟩))


set_option maxHeartbeats 4000000 in
/-- **`ReadRegisters`** after the stall, the caller's buffer from `XferHyps`. -/
theorem tcb.decode_read_registers.dec7 {A : Type _} {ar : machine.Arch A} (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_read_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have c1 := h1.cur0 D
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  unfold tcb.decode_read_registers
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · simp only [error.truncated, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun n _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · step as ⟨i, _⟩
    simp only [error.range, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  step as ⟨i, _⟩
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · simp only [error.range, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · simp only [error.illegal, error.sys, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  rename_i hne
  have hne' : t ≠ L.curW s := by
    intro e; apply hne; rw [e, show ct = L.curW s from ect.trans h1.cur]; simp
  refine WP.spec_bind (WP.spec_and (h1.restart D)
    (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2))) ?_
  rintro s2 ⟨⟨h2, hna, ec2, -⟩, ⟨-, f2, est2, k2⟩⟩
  rw [h1.cur] at est2
  simp only [lift, bind_ok]
  have hU2 : UserOK st T Cs Ω H U s2 := D.user.ksb (f2.1.trans h1.node.1)
  have nb2 : ¬ BlockedR (L.mem s2 (stA (L.curW s2))) := by rw [ec2, est2]; exact nbr_restart
  rw [← ec2] at hct
  have FR : Fr0 st T Cs Ω H Sg Scs Z s s2 := Cur0W.trans c1.fr (Foot.cur0w f2 (Set.empty_subset _))
  refine WP.spec_bind (tcb.read_registers.bxi7 E h2 ht (hna t ht) hct nb2 hU2 ⟨s, hE, FR⟩
    (fun hne => TP.rcw Ac s s2 t hE FR (BlkOK.bxi h2) ht hne)) ?_
  rintro ⟨s3, a3⟩ h3
  exact (WP.spec_ok _).2 (DecPost.ok_bxi h3)

/-! ## `CopyRegisters` -/

/-- A second stall from a stalled state. -/
theorem Stalled.stall {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s s1 : S} {a1 : A} {y : U64}
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    smp.remote_tcb_stall st ar s1 a1 y ⦃ s2 _ => Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s2 ⦄ := by
  refine WP.spec_mono (smp.remote_tcb_stall.bxi hA s1 a1 y h1.bxi) ?_
  rintro ⟨s2, a2⟩ ⟨hb2, ea, ec, -, ecs, fld, -, wn⟩
  refine ⟨hb2, ea.trans h1.act, ec.trans h1.cur, ecs.trans h1.csc,
    fun z hz K hK hK8 => (fld z hz K hK hK8).trans (h1.fld z hz K hK hK8), ?_⟩
  refine (h1.node.trans wn).mono fun b hb => ?_
  rcases hb with hb | ⟨o, ho, h88, e⟩
  · exact hb
  · exact ⟨o, ho, h88, by rw [e, h1.node.2.1, nodeAt_of_ksb h1.node.1]⟩

set_option maxHeartbeats 2000000 in
theorem tcb.copy_registers.blk {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {dest src flags : U64} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hd : dest ∈ T) (hs : src ∈ T)
    (hna : L.actionW s ≠ src)
    (hrc : L.mem s (runVcpuA src) ≠ 0#u64 →
      UserW st T Cs Ω H s (core.num.U64.wrapping_add (L.mem s (runVcpuA src)) vcpu.RUN_CALLER)) :
    tcb.copy_registers st ar s a dest src flags ⦃ r => r.1 = .Ok () ∧ BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  unfold tcb.copy_registers
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.suspend.blk7 s a src h hs hna hrc) fun r hr => by obtain ⟨s1, a1⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (Pₘ := fun r : S × A => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_ ?_
  · split
    · exact WP.spec_mono (sched.restart.tinv hA s1 a1 dest h1 hd) fun r hr => by obtain ⟨s2, a2⟩ := r; exact hr
    · exact (WP.spec_ok _).2 h1
  rintro ⟨s2, a2⟩ h2
  try simp only [uncurry_apply_pair]
  have TL : ∀ s3 : S, WritesIn st s2 s3 (XferFoot T ∅) →
      (do
        let s5 ← tcb.post_modify_registers st s3 dest
        let t ← sched.cur_thread st s5
        let b ← obj.Tcb.Insts.CoreCmpPartialEqTcb.eq dest t
        if b then do
          let s6 ← sched.reschedule_required st s5
          ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a2)
        else ok (core.result.Result.Ok (), s5, a2)) ⦃ r => r.1 = .Ok () ∧
          BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ := fun s3 w3 => by
    refine WP.spec_bind (tcb.post_modify_registers.rf (s := s3) hT hd) fun s5 w5 => ?_
    have h5 := (blk_rf h2 (rf_trans w3 w5)).1
    refine WP.spec_bind (sched.cur_thread.spec s5) fun t1 _ => ?_
    simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
    split
    · exact WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => (WP.spec_ok _).2 ⟨rfl, h6.1⟩
    · exact (WP.spec_ok _).2 ⟨rfl, h5⟩
  split
  · refine WP.spec_bind (tcb.copy_registers_loop0.rf (s0 := s2) hT hd (WritesIn.refl _ _)) fun s3 w3 => ?_
    refine WP.spec_bind (P0.obj.Tcb.reg.p0 st dest s3 _ hS) fun pc _ => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.rf (v := pc) (s := s3) hT hd (by simp [layout.reg.NEXT_IP]))
      fun s4 w4 => ?_
    split
    · refine WP.spec_bind (tcb.copy_registers_loop1.rf (s0 := s2) hT hd (rf_trans w3 w4)) fun s5 w5 => ?_
      exact TL s5 w5
    · exact TL s4 (rf_trans w3 w4)
  · split
    · refine WP.spec_bind (tcb.copy_registers_loop2.rf (s0 := s2) hT hd (WritesIn.refl _ _)) fun s3 w3 => ?_
      exact TL s3 w3
    · exact TL s2 (WritesIn.refl _ _)

set_option maxHeartbeats 2000000 in
/-- **`CopyRegisters`** after the stall. -/
theorem tcb.decode_copy_registers.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_copy_registers st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_copy_registers
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun flags _ => ?_
  refine WP.spec_bind (tcb.thread_arg.tcb (pos := 1#u64) D h1.node hxm hx0) ?_
  rintro r ⟨-, hT2⟩
  rcases r with src | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hsrc := hT2 src rfl
  refine WP.spec_bind (h1.stall hA (y := src)) ?_
  rintro ⟨s1', a1'⟩ h1'
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (WP.spec_and (h1'.restart D) (h1'.restart0 D)) fun s2 ⟨⟨h2, hna, _, _⟩, c2⟩ => ?_
  refine WP.spec_mono (tcb.copy_registers.blk hA h2 ht hsrc (hna src hsrc)
    (fun hne => TP.rcw Ac s s2 src hE c2.fr (BlkOK.bxi h2) hsrc hne)) ?_
  rintro ⟨r, s3, a3⟩ ⟨e, h3⟩
  simp only at e h3 ⊢
  subst e
  exact DecPost.ok_bxi (BlkOK.bxi h3)

/-! ## `ConfigureSingleStepping` -/

set_option maxHeartbeats 2000000 in
theorem tcb.decode_configure_single_stepping.dec {A : Type _} {ar : machine.Arch A}
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_configure_single_stepping st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  unfold tcb.decode_configure_single_stepping
  refine WP.spec_bind (sched.cur_thread.spec s1) fun ct ect => ?_
  have ect' : ct = L.curW s := ect.trans h1.cur
  subst ect'
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun bp _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun n _ => ?_
  refine WP.spec_bind (tcb.restart_caller.blk (Es := ∅) s1 h1.bxi.blk (est ▸ hr.1) (est ▸ hr.2)) ?_
  rintro s2 ⟨h2, -, est2, k⟩
  rw [h1.cur] at est2 k
  refine WP.spec_bind (debug.configure_single_stepping.rf (s := s2) (a := a1) (bp := bp) (n := n) (rep := false)
    hT ht) ?_
  rintro ⟨cons, s3, a3⟩ w3
  try simp only [uncurry_apply_pair]
  have TL : ∀ (s4 : S), WritesIn st s2 s4 (XferFoot T ∅) →
      (do
        let s5 ← sched.set_thread_state st s4 (L.curW s) sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s5, a3)) ⦃ r s' _ =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := fun s4 w4 => by
    obtain ⟨b4, -, -, f4⟩ := blk_rf h2 w4
    have e4 : L.mem s4 (stA (L.curW s)) = sched.TS_RESTART := by
      rw [stA_eq, f4 _ hct _ (by simp) (by simp) (by simp), ← stA_eq, est2]
    refine WP.spec_bind (sched.set_thread_state.running_bxi (BlkOK.bxi b4) hct e4) fun s5 h5 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi h5)
  have RW : ∀ (v : U64) (b : U64), (do
        let (len, s4) ← msg.set_mr st s3 (L.curW s) b 0#u64 v
        let s5 ← tcb.reply_words st s4 (L.curW s) len
        let s6 ← sched.set_thread_state st s5 (L.curW s) sched.TS_RUNNING
        ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s6, a3)) ⦃ r s' _ =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := fun v b => by
    refine WP.spec_bind (msg.set_mr.rf0 hT hct) ?_
    rintro ⟨n4, s4⟩ w4
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (tcb.reply_words.rf hT hct) fun s5 w5 => ?_
    exact TL s5 (rf_trans w3 (rf_trans w4 w5))
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s3 true _ hS) fun b _ => ?_
    split
    · split
      · exact RW _ _
      · exact RW _ _
    · exact RW _ _
  · exact TL s3 w3

/-! ## `thread_control_caps` within `Cur0` -/

theorem Cur0.resched {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    sched.reschedule_required st s ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  obtain ⟨Ac', hb⟩ := h.bxi
  have hct : L.curW s ∈ T := hb.1.choose_spec.choose_spec.curT
  obtain ⟨⟨Q, R, q⟩, -, -, hSg, -⟩ := id hb
  refine WP.spec_mono (WP.spec_and (sched.reschedule_required.blk s hb.blk)
    (sched.reschedule_required.curR s Q R q hSg hct)) fun s' ⟨⟨h', f'⟩, ec, ecs, esc, ea, enb⟩ => ?_
  exact Cur0.mk h (BlkOK.bxi h') ec ecs esc ea (Or.inr (enb h.nb)) (Foot.cur0w f' (Set.empty_subset _))

theorem tcb_slot_val (p i : U64) : obj.Tcb.slot p i = ok (slotIdx p i) := by
  unfold obj.Tcb.slot slotIdx
  simp [lift, cte_size]

/-- **`install_tcb_cap`** of a TCB cap slot (a64: any of the seven, `W7`), the source a cap slot or null. -/
theorem tcb.install_tcb_cap.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s0 s : S} {a : A} {target slot index src : U64} {c : capability.Cap}
    (hE : EntAt st P3Ok s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : target ∈ T) (hi : index.val < 7)
    (hsrc : src ≠ 0#u64 → CapW T Ω Sg src) :
    tcb.install_tcb_cap st ar s a target slot index c src ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  have hW := W7.tcb_slotIdxW (Ω := Ω) (Sg := Sg) hT ht hi
  unfold tcb.install_tcb_cap
  rw [tcb_slot_val]
  simp only [bind_ok]
  refine WP.spec_bind (W7.cdt.delete.cur0 hA (G _ hE) h hW) ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 h1
  refine WP.spec_bind (tcb.still_valid.nz s1 target slot c src) fun b hbv => ?_
  split
  · rename_i hb'
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    have hW0 : W7.CapW T Ω Sg (slotIdx target index) := by
      have := hW.2 0#u64 (by simp) (by simp)
      have h0 : core.num.U64.wrapping_add (slotIdx target index) 0#u64 = slotIdx target index := by
        apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
      rwa [h0] at this
    refine WP.spec_bind (Pₘ := fun s2 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s2) ?_
      fun s2 h2 => (WP.spec_ok _).2 h2
    unfold cdt.insert
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st src s1 hS) fun sc _ => ?_
    exact WP.spec_mono (C.ins7 Ac1 s0 s1 c sc src _ hE h1.fr hb1 (hsrc (hbv hb')) hW0) fun s2 w2 => h1.capw7 w2 fun _ hb => hb
  · exact (WP.spec_ok _).2 h1

/-- **`install_buffer`**, the buffer's source slot a cap slot or null. -/
theorem tcb.install_buffer.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s0 s : S} {a : A} {target slot baddr : U64} {buffer : capability.Cap × obj.Slot}
    (hE : EntAt st P3Ok s0) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : target ∈ T)
    (hsrc : buffer.2 ≠ 0#u64 → CapW T Ω Sg buffer.2) :
    tcb.install_buffer st ar s a target slot baddr buffer ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  obtain ⟨Ac', hb⟩ := h.bxi
  have hT := hb.1.choose_spec.choose_spec.tcbs
  unfold tcb.install_buffer
  rw [tcb_slot_val]
  simp only [bind_ok]
  have hW := W7.tcb_slotIdxW (Ω := Ω) (Sg := Sg) (i := layout.tcb.SLOT_BUFFER) hT ht (by simp [layout.tcb.SLOT_BUFFER])
  refine WP.spec_bind (W7.cdt.delete.cur0 hA (G _ hE) h hW) ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨Ac1, hb1⟩ := h1.bxi
  have hT1 := hb1.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (obj.Tcb.set_ipc_buffer.wr s1 target baddr) fun s2 e2 => ?_
  subst e2
  have h2 : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s1 (core.num.U64.wrapping_add target 3512#u64) baddr) := by
    have hct : L.curW s1 ∈ T := hb1.1.choose_spec.choose_spec.curT
    obtain ⟨an, fr⟩ := fld_wr (K := 3512#u64) (v := baddr) hb1 ht (by simp) (by simp)
    exact Cur0.mk h1 (bxi_field hb1 ht (by simp) (by simp) (by simp) (by simp)) an.2.2
      (cscW_wr_field hT1 (hb1.1.choose_spec.choose_spec.nodes _ hb1.1.choose_spec.choose_spec.cur) ht
        (by simp) (by simp))
      (Or.inl (by rw [scA_eq]; exact fr _ hct _ (by simp) (by simp) (fun _ => by simp)))
      (Or.inl an.1) (Or.inl (by rw [stA_eq]; exact fr _ hct _ (by simp) (by simp) (fun _ => by simp)))
      (WritesIn.mono (writesIn_wr (field_aligned (hT1 target ht) (by simp) (by simp))) fun _ hb =>
        Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp)))
  obtain ⟨vc, vs⟩ := buffer
  simp only at hsrc
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tcb.still_valid.nz _ target slot vc vs) fun b hbv => ?_
  refine WP.spec_bind (Pₘ := fun s3 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s3) ?_ fun s3 h3 => ?_
  · split
    · rename_i hb'
      obtain ⟨Ac2, hb2⟩ := h2.bxi
      have hW0 : W7.CapW T Ω Sg (slotIdx target layout.tcb.SLOT_BUFFER) := by
        have := hW.2 0#u64 (by simp) (by simp)
        have h0 : core.num.U64.wrapping_add (slotIdx target layout.tcb.SLOT_BUFFER) 0#u64 =
            slotIdx target layout.tcb.SLOT_BUFFER := by
          apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rwa [h0] at this
      unfold cdt.insert
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st vs _ hS) fun sc _ => ?_
      exact WP.spec_mono (C.ins7 Ac2 s0 _ vc sc vs _ hE h2.fr hb2 (hsrc (hbv hb')) hW0) fun s' w => h2.capw7 w fun _ hb => hb
    · exact (WP.spec_ok _).2 h2
  refine WP.spec_bind (sched.cur_thread.spec s3) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · exact WP.spec_bind (Cur0.resched h3) fun s4 h4 => (WP.spec_ok _).2 h4
  · exact (WP.spec_ok _).2 h3

/-- The install step's continuation shape. -/
theorem inst_bind {A : Type _} {s0 : S} {m : Result ((core.result.Result Unit error.Exc) × S × A)}
    {k : S → A → Result ((core.result.Result Unit error.Exc) × S × A)}
    (hm : m ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄)
    (hk : ∀ s' a', Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' → k s' a' ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄) :
    (do
      let (r, s1, a1) ← m
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => k s1 a1
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual Unit
          (core.convert.FromSame error.Exc) residual
        ok (r1, s1, a1)) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄ := by
  refine WP.spec_bind hm ?_
  rintro ⟨r, s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  rcases r with _ | e
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]; exact hk s1 a1 h1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 h1

set_option maxHeartbeats 4000000 in
/-- **`SetTimeoutEndpoint`** after the stall. -/
theorem tcb.decode_set_timeout_endpoint.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_timeout_endpoint st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_timeout_endpoint
  refine WP.spec_bind (tcb.extra_with_length.mem _ 0#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c1)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun th _ => ?_
  refine WP.spec_bind (P0.faults.valid_fault_handler.p0 th) fun b _ => ?_
  split
  swap
  · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  exact inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_TIMEOUT_HANDLER])
    (fun _ => hxw x hxm hx0)) fun s' a' h' => (WP.spec_ok _).2 h'

theorem tcb.extra_with_length.memi (c : tcb.Ctx) (i : Usize) (n : U64) (hi : i.val < 3) :
    tcb.extra_with_length c i n ⦃ r => ∀ x, r = .Ok x → x ∈ c.extra.val ∧ x ≠ 0#u64 ⦄ := by
  unfold tcb.extra_with_length tcb.extra
  have hl : i.val < c.extra.val.length := by rw [c.extra.property]; simpa using hi
  simp only [show ¬ (i ≥ 3#usize) by simp; omega, ↓reduceIte]
  refine WP.spec_bind (Pₘ := fun o => ∀ x, o = some x → x ∈ c.extra.val ∧ x ≠ 0#u64) ?_ fun o ho => ?_
  · refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec c.extra i hl) fun sl hsl => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · exact (WP.spec_ok _).2 fun x e => by cases e
    · rename_i h0
      exact (WP.spec_ok _).2 fun x e => by
        cases e; exact ⟨hsl ▸ List.getElem_mem hl, by simpa using h0⟩
  rcases o with _ | x
  · simp [error.truncated]
  · simp only
    split
    · exact (WP.spec_ok _).2 fun y e => by cases e; exact ho x rfl
    · simp [error.truncated]

set_option hygiene false in
/-- An error leaf at the stalled `Cur0` state `c1`. -/
local macro "errc" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post c1)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, error.invalid_cap, error.illegal, error.truncated]
     exact (WP.spec_ok _).2 (Cur0.post c1)))

set_option hygiene false in
/-- An extra-slot read with its error leaf. -/
local macro "xslot" i:term : tactic => `(tactic| (
  refine WP.spec_bind (tcb.extra_with_length.memi _ $i _ (by simp)) ?_
  rintro r hx
  rcases r with x | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl))

set_option maxHeartbeats 8000000 in
/-- **`SetSpace`** after the stall. -/
theorem tcb.decode_set_space.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_space st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_space
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun cdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun vdata _ => ?_
  refine WP.spec_bind (P0.tcb.derive_roots.p0 st s1 t cdata vdata x1 x2 hS) fun r _ => ?_
  rcases r with ⟨cc, vc⟩ | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x0 s1 hS) fun fh _ => ?_
  refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fh) fun b _ => ?_
  split
  swap
  · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  simp only [lift, bind_ok]
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    (fun _ => hxw x0 hxm0 hx00)) fun s3 a3 c3 => ?_
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c3 ht (by simp [layout.tcb.SLOT_CTABLE])
    (fun _ => hxw x1 hxm1 hx01)) fun s4 a4 c4 => ?_
  exact inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c4 ht (by simp [layout.tcb.SLOT_VTABLE])
    (fun _ => hxw x2 hxm2 hx02)) fun s5 a5 c5 => (WP.spec_ok _).2 c5

set_option maxHeartbeats 8000000 in
/-- **`Configure`** after the stall. -/
theorem tcb.decode_configure.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_configure st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_configure
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun cdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun vdata _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun baddr _ => ?_
  refine WP.spec_bind (tcb.derive_for_buffer.slot s1 baddr x2) ?_
  rintro r hbf
  rcases r with bf | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hbf' := hbf bf rfl
  refine WP.spec_bind (P0.tcb.derive_roots.p0 st s1 t cdata vdata x0 x1 hS) fun r _ => ?_
  rcases r with ⟨cc, vc⟩ | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  refine WP.spec_mono (P₀ := fun r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s r.2.1) ?_ fun r hr => by
    obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  simp only [lift, bind_ok]
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_CTABLE])
    (fun _ => hxw x0 hxm0 hx00)) fun s4 a4 c4 => ?_
  refine inst_bind (tcb.install_tcb_cap.cur0 hA G C hE c4 ht (by simp [layout.tcb.SLOT_VTABLE])
    (fun _ => hxw x1 hxm1 hx01)) fun s5 a5 c5 => ?_
  exact inst_bind (tcb.install_buffer.cur0 hA G C hE c5 ht (fun h0 => by
    rcases hbf' with e | e
    · rw [e]; exact hxw x2 hxm2 hx02
    · exact absurd e h0)) fun s6 a6 c6 => (WP.spec_ok _).2 c6

/-! ## `SetSchedParams` -/

/-- `tcs_tail` with its result: `Ok`. -/
theorem tcs_tail2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s0 s1 : S) (a1 : A)
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
      L.mem s' (runVcpuA target) ≠ 0#u64 → UserW st T Cs Ω H s' (ownA (L.mem s' (runVcpuA target)))) :
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
      refine WP.spec_bind (schedcontext.bind_tcb.blkF_f
        (U := {b | L.mem s4 (runVcpuA target) ≠ 0#u64 ∧ b = ownA (L.mem s4 (runVcpuA target))})
        (Es := ∅) hA s4 a1 sc target h4 ht hsc hsc0
        (by rw [pf4.sc target ht]; exact ht0)
        (by rw [pf4.sig _ (h4.2.2.1.1.fixW sc hsc).1]; exact hc0)
        (fun hb' => hbA (by rw [← pf4.st target ht]; exact hb'))
        (fun b ⟨hne, e⟩ => e ▸ hown s4 h4 w4 hne) (fun hne => ⟨hne, rfl⟩)) fun r hr => ?_
      obtain ⟨s5, a2⟩ := r
      exact (WP.spec_ok _).2 ⟨hr.1, rfl⟩
  · exact (WP.spec_ok _).2 ⟨h4, rfl⟩


/-- **`thread_control_sched` with the fault-handler update**, the install
keeping `BlkOK` with the `CaiFr` frame and (for its error results) `Cur0`. -/
theorem tcb.thread_control_sched.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A)
    (target : obj.Tcb) (slot : obj.Slot) (fh : capability.Cap × obj.Slot) (mcp prio : U64) (sc : obj.Sc)
    (flags : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : target ∈ T)
    (hfl : (flags &&& tcb.SCHED_UPDATE_FAULT) ≠ 0#u64)
    (hinst : tcb.install_tcb_cap st ar s a target slot layout.tcb.SLOT_FAULT_HANDLER fh.1 fh.2 ⦃ r =>
      (BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ∧ CaiFr st T Scs 0#u64 s r.2.1 ∧
      (L.actionW r.2.1 = L.actionW s ∨ L.actionW r.2.1 = 1#u64)) ∧ Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.2.1 ⦄)
    (hown : ∀ s' : S, BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' → Fr0 st T Cs Ω H Sg Scs Z s0 s' →
      L.mem s' (runVcpuA target) ≠ 0#u64 → UserW st T Cs Ω H s' (ownA (L.mem s' (runVcpuA target))))
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
      have := tcs_tail2 hA s2 s2 a1 target mcp prio sc flags h2 ht (PFr.refl _ _) rfl id hp2 hb2 hu2
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

/-- What `sched_params_sc` checks: the SC is null (and the target is not the
caller), or a non-null SC object which, when it is not the target's SC
already, is bound to nothing, the target has none, and it is released (so
active, `SCsOK.act`) when the target is blocked. -/
theorem tcb.sched_params_sc.ok {s : S} (t sl : U64)
    (hc : obj.Slot.cap st sl s ⦃ c => CapOK st T Rp Scs Nt H s c ⦄) (hS : SCsOK st T Ω Sg Scs Z Ac s) :
    tcb.sched_params_sc st s t sl ⦃ r => ∀ v, r = .Ok v → (v = 0#u64 ∧ t ≠ L.curW s) ∨
      (v ∈ Scs ∧ v ≠ 0#u64 ∧ (L.mem s (scA t) ≠ v → L.mem s (scA t) = 0#u64 ∧ L.mem s (scTcbA v) = 0#u64 ∧
        (BlockedR (L.mem s (stA t)) → v ∈ Ac))) ⦄ := by
  unfold tcb.sched_params_sc
  refine WP.spec_bind hc fun c hcO => ?_
  cases c
  all_goals first | (simp [error.invalid_cap]; done) | skip
  · -- null
    step with sched.cur_thread.spec as ⟨ct, ect⟩
    simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
    split
    · simp [error.illegal]
    · rename_i hne
      exact (WP.spec_ok _).2 fun v e => by
        cases e; exact Or.inl ⟨rfl, fun e' => hne (by subst e'; simp [ect, LawfulStore.curW])⟩
  · -- an SC
    rename_i ptr b
    obtain ⟨hpS, hp0, -⟩ := hcO.2.2 ptr b rfl
    dsimp only
    step with obj.Tcb.sc.spec as ⟨i, ei⟩
    split
    · rename_i hne
      split
      · simp [error.illegal]
      · rename_i hi0
        step with obj.Sc.tcb.spec as ⟨j, ej⟩
        split
        · simp [error.illegal]
        · rename_i hj0
          have hz : L.mem s (scA t) ≠ ptr → L.mem s (scA t) = 0#u64 ∧ L.mem s (scTcbA ptr) = 0#u64 := fun _ =>
            ⟨by rw [← ei]; exact UScalar.eq_of_val_eq (by simpa using hi0),
              by rw [← ej]; exact UScalar.eq_of_val_eq (by simpa using hj0)⟩
          refine WP.spec_bind (sched.is_blocked.br s t) fun bb hbb => ?_
          split
          · refine WP.spec_bind (sporadic.sc_released.act s ptr) fun b1 hb1 => ?_
            split
            · rename_i hb1t
              refine (WP.spec_ok _).2 fun v e => ?_
              cases e
              exact Or.inr ⟨hpS, hp0, fun hne => ⟨(hz hne).1, (hz hne).2, fun _ => (hS.act ptr hpS).2 (hb1 hb1t)⟩⟩
            · simp [error.illegal]
          · rename_i hbf
            refine (WP.spec_ok _).2 fun v e => ?_
            cases e
            exact Or.inr ⟨hpS, hp0, fun hne => ⟨(hz hne).1, (hz hne).2, fun hb => absurd hb (hbb (by simpa using hbf))⟩⟩
    · rename_i heq
      have hz : L.mem s (scA t) ≠ ptr → L.mem s (scA t) = 0#u64 ∧ L.mem s (scTcbA ptr) = 0#u64 := fun hne =>
        absurd (by rw [← ei]; exact UScalar.eq_of_val_eq (by simpa using heq)) hne
      refine WP.spec_bind (sched.is_blocked.br s t) fun bb hbb => ?_
      split
      · refine WP.spec_bind (sporadic.sc_released.act s ptr) fun b1 hb1 => ?_
        split
        · rename_i hb1t
          refine (WP.spec_ok _).2 fun v e => ?_
          cases e
          exact Or.inr ⟨hpS, hp0, fun hne => ⟨(hz hne).1, (hz hne).2, fun _ => (hS.act ptr hpS).2 (hb1 hb1t)⟩⟩
        · simp [error.illegal]
      · rename_i hbf
        refine (WP.spec_ok _).2 fun v e => ?_
        cases e
        exact Or.inr ⟨hpS, hp0, fun hne => ⟨(hz hne).1, (hz hne).2, fun hb => absurd hb (hbb (by simpa using hbf))⟩⟩

theorem ssp_flags :
    (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT) &&& tcb.SCHED_UPDATE_FAULT ≠ 0#u64 ∧
    (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC) &&&
      tcb.SCHED_UPDATE_FAULT ≠ 0#u64 ∧
    (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT) &&& tcb.SCHED_UPDATE_SC = 0#u64 ∧
    (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT) &&& tcb.SCHED_UPDATE_PRIO ≠ 0#u64 ∧
    (tcb.SCHED_UPDATE_MCP ||| tcb.SCHED_UPDATE_PRIO ||| tcb.SCHED_UPDATE_FAULT ||| tcb.SCHED_UPDATE_SC) &&&
      tcb.SCHED_UPDATE_PRIO ≠ 0#u64 := by
  unfold tcb.SCHED_UPDATE_MCP tcb.SCHED_UPDATE_PRIO tcb.SCHED_UPDATE_FAULT tcb.SCHED_UPDATE_SC
  decide

set_option maxHeartbeats 8000000 in
/-- **`SetSchedParams`** after the stall, from `SspHyps`. -/
theorem tcb.decode_set_sched_params.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1)
    (hΩ : ∀ x ∈ Ω, L.mem s1 x = L.mem s x) (hid1 : L.idleW s1 = L.idleW s) :
    tcb.decode_set_sched_params st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have c1 := h1.cur0 D
  have hxw := P.extraW Ac s _ _ hE D
  have hb1 := h1.bxi.blk
  unfold tcb.decode_set_sched_params
  refine WP.spec_bind (tcb.extra_with_length.memi _ 0#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x0 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm0, hx00⟩ := hx x0 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 1#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x1 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm1, hx01⟩ := hx x1 rfl
  refine WP.spec_bind (tcb.extra_with_length.memi _ 2#usize _ (by simp)) ?_
  rintro r hx
  rcases r with x2 | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm2, hx02⟩ := hx x2 rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun mcp _ => ?_
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun prio _ => ?_
  refine WP.spec_bind (tcb.thread_arg.tcb (pos := 1#u64) D h1.node hxm0 hx00) ?_
  rintro r ⟨-, hT2⟩
  rcases r with auth | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hauth := hT2 auth rfl
  refine WP.spec_bind (tcb.check_prio.le s1 mcp auth) ?_
  rintro r ⟨-, -⟩
  rcases r with u | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (tcb.check_prio.le s1 prio auth) ?_
  rintro r ⟨-, hle⟩
  rcases r with u | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hv : prio.val < 256 := lt_of_le_of_lt (hle rfl) (by rw [h1.fld auth hauth 3440#u64 (by simp) (by simp)]; exact P.mcp Ac s auth hE D.bxi hauth)
  refine WP.spec_bind (tcb.sched_params_sc.ok t x1 (D.extra s1 h1.node x1 hxm1 hx01) hb1.2.2.2.1) ?_
  rintro r hsp
  rcases r with v | e
  swap
  · errc
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hsp := hsp v rfl
  simp only [lift, bind_ok]
  refine WP.spec_bind (obj.Tcb.sc.spec s1 t) fun i1 ei1 => ?_
  -- the restart, then the install and the scheduling words
  have est : L.mem s1 (stA (L.curW s1)) = L.mem s (stA (L.curW s)) := by
    rw [h1.cur, stA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
  have hr := runnable_ok D.run
  have hsc0 := P.curSc Ac s _ _ hE D
  have run : ∀ (flags : U64), (flags &&& tcb.SCHED_UPDATE_FAULT) ≠ 0#u64 →
      ((flags &&& tcb.SCHED_UPDATE_SC) ≠ 0#u64 → L.mem s1 (scA t) ≠ v) → ∀ fhc : capability.Cap,
      (do
        let s2 ← tcb.restart_caller st s1
        tcb.thread_control_sched st ar s2 a1 t slot (fhc, x2) mcp prio v flags) ⦃ r =>
          DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2.1 ⦄ := by
    intro flags hfl hfs fhc
    refine WP.spec_bind (WP.spec_and (WP.spec_and (h1.restart D) (h1.restart0 D))
      (tcb.restart_caller.blk (Es := EH H) s1 hb1 (est ▸ hr.1) (est ▸ hr.2))) ?_
    rintro s2 ⟨⟨⟨h2, hna, ec2, k⟩, c2⟩, ⟨_, f2, est2, _⟩⟩
    have agree : ∀ b, Aligned b → CapW T Ω Sg b → L.mem s2 b = L.mem s b := fun b hb hw => by
      rw [f2.mem_eq hb fun hk => capw_not_kw hb1 hw hb (le_refl _) (by omega) hk]
      rcases hw with ⟨y, hy, K, hK, rfl⟩ | ⟨hm, -⟩
      · have := field_val (hT y hy) (by omega : K.val < 4096)
        have := (hT y hy).align
        unfold Aligned at hb
        exact h1.fld y hy K (by omega) (by omega)
      · exact hΩ b hm
    have einq : L.mem s2 (inqA (L.curW s)) = L.mem s (inqA (L.curW s)) := by
      rw [k.inqf hct, inqA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
    have esc : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) := by
      rw [k.scf hct, scA_eq]; exact h1.fld _ hct _ (by simp) (by simp)
    refine tcb.thread_control_sched.dec hA a1 t slot (fhc, x2) mcp prio v flags h2 ht hfl
      (WP.spec_and (tcb.install_tcb_cap.cai s2 a1 t slot _ fhc x2 _ (tcb_slot_val _ _) h2
          (Y.fh Ac s t extra hE D s2 agree) (fun s1' a1' hag => Y.slot Ac s t extra hE D slot x2 fhc hxm2 hx02 s1' a1'
            fun b hb hw => (hag b hb hw).trans (agree b hb hw)))
        (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_FAULT_HANDLER])
          (fun _ => hxw x2 hxm2 hx02)))
      (fun s' hb' f' hne => C.own Ac s s' t hE f' (BlkOK.bxi hb') ht hne)
      (fun _ => ⟨hv, fun e => by rw [e, ec2, einq, esc]; exact ⟨D.cb.nr, hsc0, D.cb.ac hsc0⟩⟩) ?_ ?_
    · intro hf h0
      have hne := hfs hf
      rcases hsp with ⟨e0, -⟩ | ⟨hvS, -, hc⟩
      · exact absurd e0 h0
      obtain ⟨z1, z2, z3⟩ := hc hne
      refine ⟨hvS, by rw [k.scf ht]; exact z1, by rw [(k.fix v hvS).1]; exact z2, fun hb => z3 ?_⟩
      by_cases e : t = L.curW s
      · rw [e, ← h1.cur, est2] at hb
        exact absurd hb nbr_restart
      · rwa [stA_eq, k.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e' e), ← stA_eq] at hb
    · intro _ _
      refine ⟨hna t ht, ?_⟩
      rw [k.idleW, hid1]
      exact fun e => Y.idle Ac s t extra hE D e.symm
  split
  · rename_i hne
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s1 hS) fun fhc _ => ?_
    refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fhc) fun b _ => ?_
    split
    swap
    · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    exact WP.spec_mono (run _ ssp_flags.2.1 (fun _ e => by rw [ei1, e] at hne; simp at hne) fhc)
      fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact hr
  · refine WP.spec_bind (P0.obj.Slot.cap.p0 st x2 s1 hS) fun fhc _ => ?_
    refine WP.spec_bind (P0.faults.valid_fault_handler.p0 fhc) fun b _ => ?_
    split
    swap
    · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    exact WP.spec_mono (run _ ssp_flags.1 (fun hf => absurd ssp_flags.2.2.1 hf) fhc)
      fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact hr

/-! ## `SetIPCBuffer` over the seven slots -/

set_option hygiene false in
/-- An error leaf at a `Cur0` state `hc`. -/
local macro "errC" hc:term : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post $hc)
  | (simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok, error.truncated, error.illegal]
     exact (WP.spec_ok _).2 (Cur0.post $hc)))

set_option maxHeartbeats 4000000 in
/-- **`SetIPCBuffer`** after the stall (a64: over `W7.DelGaps`), from `DelGaps` (the buffer slot's
delete), `CdtHyps` (the insert) and the extra slots' placement. -/
theorem tcb.decode_set_ipc_buffer.dec7 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_ipc_buffer st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have c1 := h1.cur0 D
  unfold tcb.decode_set_ipc_buffer
  refine WP.spec_bind (tcb.extra_with_length.mem _ 1#u64) ?_
  rintro r ⟨-, hx⟩
  rcases r with x | e
  swap
  · errC c1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨hxm, hx0⟩ := hx x rfl
  refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun baddr _ => ?_
  refine WP.spec_bind (tcb.derive_for_buffer.slot s1 baddr x) ?_
  rintro r hr
  rcases r with v | e
  swap
  · errC c1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  have hv2 := hr v rfl
  refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
  unfold tcb.thread_control_caps
  simp only [lift, bind_ok, tcb.UPDATE_FAULT, tcb.UPDATE_TIMEOUT, tcb.UPDATE_SPACE, tcb.UPDATE_IPC_BUFFER]
  simp
  refine WP.spec_bind (Pₘ := fun r : (core.result.Result Unit error.Exc) × S × A =>
    DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2.1) ?_ ?_
  swap
  · rintro ⟨r, s', a'⟩ hr
    dsimp only at hr
    try simp only [uncurry_apply_pair]
    rcases r with _ | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      exact (WP.spec_ok _).2 hr
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 hr
  -- `install_buffer`
  unfold tcb.install_buffer obj.Tcb.slot
  simp only [lift, bind_ok, layout.tcb.SLOT_BUFFER, cte_size]
  refine WP.spec_bind (W7.cdt.delete.cur0 hA (G _ hE) c2 (W7.slotW_to7 (tcb_slotW hT ht))) ?_
  rintro ⟨r, s3, a3⟩ c3
  try simp only [uncurry_apply_pair] at c3 ⊢
  rcases r with _ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
      bind_tc_ok]
    exact (WP.spec_ok _).2 (Cur0.post c3)
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  obtain ⟨Ac3, hb3⟩ := c3.bxi
  refine WP.spec_bind (obj.Tcb.set_ipc_buffer.wr s3 t baddr) fun s4 e4 => ?_
  subst e4
  have h4 := (plainW_all (K := 3512#u64) (v := baddr) hb3.blk ht (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp)).1
  have f4 : Fr0 st T Cs Ω H Sg Scs Z s (L.wr s3 (core.num.U64.wrapping_add t 3512#u64) baddr) :=
    Cur0W.trans c3.fr (WritesIn.mono (writesIn_wr (field_aligned (hT t ht) (by simp) (by simp))) fun _ hb =>
      Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp)))
  obtain ⟨vc, vs⟩ := v
  simp only at hv2
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (tcb.still_valid.nz _ t slot vc vs) fun b hbv => ?_
  refine WP.spec_bind (Pₘ := fun s5 => BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac3 s5) ?_ fun s5 h5 => ?_
  · split
    · rename_i hb
      have hvs : vs = x := hv2.resolve_right (hbv hb)
      subst hvs
      have hxW := hxw vs hxm hx0
      have hbW : CapW T Ω Sg (core.num.U64.wrapping_add t (core.num.U64.wrapping_mul 2#u64 32#u64)) := by
        have := (tcb_slotW (Ω := Ω) (Sg := Sg) hT ht).2 0#u64 (by simp) (by simp)
        have h0 : ∀ y : U64, core.num.U64.wrapping_add y 0#u64 = y := fun y => by
          apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
        rwa [h0] at this
      unfold cdt.insert
      refine WP.spec_bind (P0.obj.Slot.cap.p0 st vs _ hS) fun sc _ => ?_
      exact WP.spec_mono (C.ins Ac3 s _ vc sc vs _ hE f4 (BlkOK.bxi h4) hxW hbW) fun s' w =>
        (blk_of_capw h4 w fun _ hb => hb).1
    · exact (WP.spec_ok _).2 h4
  refine WP.spec_bind (sched.cur_thread.spec s5) fun ct _ => ?_
  simp only [obj.Tcb.Insts.CoreCmpPartialEqTcb.eq, bind_ok]
  split
  · refine WP.spec_bind (sched.reschedule_required.blk s5 h5) fun s6 h6 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h6.1))
  · exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h5))

set_option maxHeartbeats 4000000 in
/-- **`SetHighVSpace`** (AArch64, `decode_set_high_vspace`) after the stall: the caller's restart and the install
into the seventh slot `SLOT_HIGH_VSPACE` (W7 install chain), of the null cap or the derived `HighVSpace` cap. -/
theorem tcb.decode_set_high_vspace.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (G : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s s1 : S} {a1 : A} {t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hxw : ∀ sl ∈ extra.val, sl ≠ 0#u64 → CapW T Ω Sg sl)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra) (hE : EntAt st P3Ok s)
    (h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1) :
    tcb.decode_set_high_vspace st ar s1 a1 t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have ht : t ∈ T := D.cap.2.1 t rfl
  have c1 := h1.cur0 D
  unfold tcb.decode_set_high_vspace
  refine WP.spec_bind (tcb.extra.mem0 _) ?_
  rintro o ho
  rcases o with _ | x
  · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  obtain ⟨hxm, hx0⟩ := ho x rfl
  simp only
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun cap _ => ?_
  cases cap <;> try (simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1))
  · -- the null cap: clear the slot
    refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
    exact WP.spec_mono (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_HIGH_VSPACE])
      (fun _ => hxw x hxm hx0)) fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
  · -- a `HighVSpace` cap
    dsimp only
    split
    · refine WP.spec_bind (P0.vspace.find_high_asid.p0 st s1 _ hS) fun r _ => ?_
      rcases r with r1 | e
      · simp only
        split
        · refine WP.spec_bind (P0.objects.derive_cap.p0 st s1 x _ hS) fun r2 _ => ?_
          rcases r2 with v | e
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
            refine WP.spec_bind (h1.restart0 D) fun s2 c2 => ?_
            exact WP.spec_mono (tcb.install_tcb_cap.cur0 hA G C hE c2 ht (by simp [layout.tcb.SLOT_HIGH_VSPACE])
              (fun _ => hxw x hxm hx0)) fun r hr => by obtain ⟨r1, r2, r3⟩ := r; exact Cur0.post hr
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
              bind_tc_ok]
            exact (WP.spec_ok _).2 (Cur0.post c1)
        · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
      · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    · simp only [error.invalid_cap, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)

set_option maxHeartbeats 4000000 in
/-- **`tcb.decode`** keeps the invariants (a64: every label proved, `SetEPTRoot` / `SetPACKeys` /
`SetHighVSpace` included), from `SspHyps`, `TcbPlace`, `TcbPlace7`, `W7.DelGaps` and `CdtHyps`. -/
theorem tcb.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Gd : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    {s : S} {a : A} {lbl t len buf : U64} {call : Bool} {slot : obj.Slot}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s (.Thread t) extra)
    (hE : EntAt st P3Ok s) :
    tcb.decode st ar s a lbl t { length := len, buf, call, slot, extra } ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have ht : t ∈ T := D.cap.2.1 t rfl
  have hS : P0.StoreTotal st := L.total
  have hT := D.bxi.1.choose_spec.choose_spec.tcbs
  have hxw := P.extraW Ac s _ _ hE D
  unfold tcb.decode
  refine WP.spec_bind (smp.remote_tcb_stall.bxi hA s a t D.bxi) ?_
  rintro ⟨s1, a1⟩ ⟨hb1, ea, ec, eid, ecs, fld, eΩ, wn⟩
  have h1 : Stalled st T Cs Ω H Sg Rp Scs Nt Z Ac s s1 := ⟨hb1, ea, ec, ecs, fld, wn⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine spec_ite (fun hc => ?_) fun hc0 => ?_
  · -- SetPACKeys
    subst hc
    unfold tcb.decode_arch
    rw [if_pos rfl]
    exact tcb.decode_set_pac_keys.dec hA D h1
  refine spec_ite (fun hc => ?_) fun _ => ?_
  · -- SetHighVSpace
    subst hc
    unfold tcb.decode_arch
    rw [if_neg hc0]
    exact tcb.decode_set_high_vspace.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- SetEPTRoot (AArch64: a Stage-2 `Ept` cap into `SLOT_EPT`)
    have c1 := h1.cur0 D
    have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun x hx => ?_
    simp only [obj.Slot.is_null, bind_ok]
    split
    · simp only [error.truncated, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    rename_i hx0
    have hxm : x ∈ extra.val := hx ▸ List.getElem_mem hl0
    have hx0' : x ≠ 0#u64 := by simpa using hx0
    refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s1 hS) fun cap _ => ?_
    cases cap <;> try (simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1))
    dsimp only
    split
    · split
      · refine WP.spec_bind (P0.objects.derive_cap.p0 st s1 x _ hS) fun r2 _ => ?_
        rcases r2 with v | e
        swap
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 (Cur0.post c1)
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, tcb_slot_val]
        have hW := W7.tcb_slotIdxW (Ω := Ω) (Sg := Sg) (i := layout.tcb.SLOT_EPT) hT ht (by simp [layout.tcb.SLOT_EPT])
        refine WP.spec_bind (W7.cdt.delete.cur0 hA (Gd _ hE) c1 hW) ?_
        rintro ⟨r3, s4, a2⟩ c4
        try simp only [uncurry_apply_pair] at c4 ⊢
        rcases r3 with _ | e
        swap
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
            bind_tc_ok]
          exact (WP.spec_ok _).2 (Cur0.post c4)
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        obtain ⟨Ac4, hb4⟩ := c4.bxi
        have hW0 : W7.CapW T Ω Sg (slotIdx t layout.tcb.SLOT_EPT) := by
          have := hW.2 0#u64 (by simp) (by simp)
          have h0 : core.num.U64.wrapping_add (slotIdx t layout.tcb.SLOT_EPT) 0#u64 = slotIdx t layout.tcb.SLOT_EPT := by
            apply UScalar.eq_of_val_eq; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]
          rwa [h0] at this
        refine WP.spec_bind (Pₘ := fun s5 => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s s5) ?_ fun s5 c5 => ?_
        · unfold cdt.insert
          refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s4 hS) fun sc _ => ?_
          exact WP.spec_mono (TP.ins7 Ac4 s s4 v sc x _ hE c4.fr hb4 (hxw x hxm hx0') hW0) fun s' w =>
            c4.capw7 w fun _ hb => hb
        refine WP.spec_bind (sched.cur_thread.spec s5) fun ct ect => ?_
        have e : ct = L.curW s5 := ect
        subst e
        refine WP.spec_bind (Cur0.restartEnd c5) fun s6 c6 => ?_
        exact (WP.spec_ok _).2 (Cur0.post c6)
      · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
    · simp only [error.illegal, bind_ok]; exact (WP.spec_ok _).2 (Cur0.post c1)
  refine spec_ite (fun _ => tcb.decode_read_registers.dec7 E TP D hE h1) fun _ => ?_
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_write_registers.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_copy_registers.dec hA TP D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Suspend
    refine WP.spec_bind (WP.spec_and (h1.restart D) (h1.restart0 D)) fun s2 ⟨⟨h2, hna, _, _⟩, c2⟩ => ?_
    refine WP.spec_bind (sched.suspend.blk7 s2 a1 t h2 ht (hna t ht)
      (fun hne => TP.rcw Ac s s2 t hE c2.fr (BlkOK.bxi h2) ht hne)) ?_
    rintro ⟨s3, a2⟩ h3
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- Resume
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (sched.restart.tinv hA s2 a1 t h2 ht) ?_
    rintro ⟨s3, a2⟩ h3
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_configure.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_priority.dec _ P D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_priority.dec _ P D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_sched_params.dec hA Gd TP P Y D hE h1 eΩ eid
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_ipc_buffer.dec7 hA Gd C hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_space.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_timeout_endpoint.dec hA Gd TP hxw D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_bind_notification.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- UnbindNotification
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s1 t) fun i _ => ?_
    split
    · simp only [error.illegal, bind_ok]
      exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (notification.unbind_notification.blk s2 t h2 ht) fun s3 h3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h3))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_configure_single_stepping.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.set_breakpoint_checked.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_get_breakpoint.dec E D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · -- UnsetBreakpoint
    have c1 := h1.cur0 D
    refine WP.spec_bind (P0.tcb.arg.p0 st s1 _ _ hS) fun bp _ => ?_
    refine WP.spec_bind (debug.check_bp_num.lt bp) ?_
    rintro r ⟨-, hbp⟩
    rcases r with _ | e
    swap
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      exact (WP.spec_ok _).2 (Cur0.post c1)
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    refine WP.spec_bind (h1.restart D) fun s2 ⟨h2, _, _, _⟩ => ?_
    refine WP.spec_bind (debug.unset_breakpoint.rf (s := s2) hT ht (hbp rfl)) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_rf h2 w3).1))
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_tls_base.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.decode_set_flags.dec hA D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.set_timer.dec D h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.fpu_transfer.dec hA P D hE h1
  refine spec_ite (fun _ => ?_) fun _ => ?_
  · exact tcb.fpu_transfer.dec hA P D hE h1
  exact (WP.spec_ok _).2 (DecPost.of_bxi h1.bxi (by simp))

/-- **InvGaps' `thread`, from `SspHyps`, `TcbPlace`, `TcbPlace7`, `W7.DelGaps` and `CdtHyps`** (a64: no
`TcbGaps.setEPTRoot`; the AArch64 labels are proved). -/
theorem decGap_thread {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (Y : SspHyps st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (P : TcbPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (Gd : W7.DelGaps st ar T Cs Ω H Sg Rp Scs Nt Z P3Ok) (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (TP : TcbPlace7 st T Cs Ω H Sg Rp Scs Nt Z P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .thread := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact tcb.decode.dec hA Y P E Gd C TP D hE

end

end Fl4ProofsA64.P1
