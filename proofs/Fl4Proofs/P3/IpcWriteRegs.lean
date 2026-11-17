/-
P3 (DESIGN.md §9), TCB invocations: **WriteRegisters on `IRel`**
(`tcb::write_registers` against l4v `invoke_tcb WriteRegisters`): the steps;
the leaf from `JAtZ` is IpcWriteRegsJ's `writeRegsXHypJ` (the former
`writeRegsXHyp_of` is retired).

The two register loops (`wr_loop0`, `wr_loop1`) write the target's frame
and integer registers, sanitised (IpcFaultReply's `RgInv`, `set_reg_rg_inv`,
`sanitise_eq`), from the syscall arguments (`WrRead`: the value read at each
step); then the restart PC, `post_modify_registers`, the optional restart
(`restart_tcb_irel`) and the reschedule of the current thread.
-/
import Fl4Proofs.P3.IpcResume
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Ipc

noncomputable section

theorem frame_regs_val : regs.FRAME_REGISTERS.val = Fl4Spec.frameRegisters.map regIdx := by
  unfold regs.FRAME_REGISTERS layout.reg.RAX layout.reg.RBX layout.reg.RCX layout.reg.RDX layout.reg.RSI
    layout.reg.RDI layout.reg.RBP layout.reg.R8 layout.reg.R9 layout.reg.R10 layout.reg.R11 layout.reg.R12
    layout.reg.R13 layout.reg.R14 layout.reg.R15 layout.reg.FAULT_IP layout.reg.RSP layout.reg.FLAGS
  rfl

theorem gp_regs_val : regs.GP_REGISTERS.val = Fl4Spec.gpRegisters.map regIdx := by
  unfold regs.GP_REGISTERS layout.reg.FS_BASE layout.reg.GS_BASE
  rfl

/-- The registers WriteRegisters writes, in order. -/
abbrev wrRegs : List Fl4Spec.Register := Fl4Spec.frameRegisters ++ Fl4Spec.gpRegisters

theorem wrRegs_length : wrRegs.length = 20 := rfl

theorem cast_to_us' (i : U64) (h : i.val < 2 ^ 32) : (UScalar.cast .Usize i).val = i.val := by
  rw [UScalar.cast_val_eq]
  refine Nat.mod_eq_of_lt ?_
  rw [UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with e | e <;> rw [e] <;> omega

section Loops
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

variable (T E R B SR) in
/-- **The value WriteRegisters writes at step `j`**: from any state of the
loop's invariant after `j` writes, the syscall argument `j + 2` reads as the
`j`-th value. -/
def WrRead (s0 : S) (σ0 : Fl4Spec.State Unit) (dest : U64) (x0 : Fl4Spec.Tcb) (ct buf n : U64)
    (V : List Fl4Spec.Word) : Prop :=
  ∀ (j : Nat) (i2 : U64) (s' : S), i2.val = j + 2 → j < n.val →
    RgInv (L := L) T E R B SR s0 σ0 dest x0 s' (wrRegs.take j) (V.take j) →
    ∃ w, msg.syscall_arg st s' ct buf i2 = ok w ∧ w.bv = V[j]!

set_option maxHeartbeats 4000000 in
/-- **The frame-register loop of `write_registers`.** -/
theorem wr_loop0 (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {dest : U64} (hd : dest ∈ T) {x0 : Fl4Spec.Tcb} {ct buf n : U64} (hn : n.val ≤ 20) {V : List Fl4Spec.Word}
    (hVl : n.val ≤ V.length) (hRd : WrRead (L := L) T E R B SR s0 σ0 dest x0 ct buf n V)
    (s1 : S) (hI : RgInv (L := L) T E R B SR s0 σ0 dest x0 s1 [] []) :
    tcb.write_registers_loop0 st s1 dest buf ct n 0#u64 ⦃ s2 =>
      RgInv (L := L) T E R B SR s0 σ0 dest x0 s2 (wrRegs.take (min n.val 18)) (V.take (min n.val 18)) ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hgl : Fl4Spec.gpRegisters.length = 2 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.write_registers_loop0
  apply loop.spec_decr_nat (measure := fun x => 18 - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 18 ∧
      RgInv (L := L) T E R B SR s0 σ0 dest x0 x.1 (wrRegs.take x.2.val) (V.take x.2.val))
  · rintro ⟨s', i⟩ ⟨hi, hI'⟩
    unfold tcb.write_registers_loop0.body
    simp only at hi hI' ⊢
    by_cases h1 : i < tcb.N_FRAME
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h1; rw [hf] at this; omega
      exact this ▸ hI'
    rw [if_pos h1]
    have hi18 : i.val < 18 := by have := (P1.gt_iff_val).1 h1; rwa [hf] at this
    by_cases h2 : i < n
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h2; omega
      exact this ▸ hI'
    rw [if_pos h2]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h2
    simp only [lift, bind_ok]
    refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
    rintro r hr
    have hrv : r = regIdx wrRegs[i.val] := by
      rw [hr, List.getElem_of_eq frame_regs_val, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega), wrRegs, List.getElem_append_left (show i.val < Fl4Spec.frameRegisters.length by omega)]
    subst hrv
    obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := i) (y := 2#u64) (by scalar_tac))
    rw [h2e, bind_ok]
    have hi2 : i2.val = i.val + 2 := by simpa using h2v
    obtain ⟨w0, hw0, hw0v⟩ := hRd i.val i2 s' hi2 hin hI'
    rw [hw0, bind_ok]
    obtain ⟨w, hw, hwv⟩ := sanitise_eq wrRegs[i.val] w0
    rw [hw, bind_ok]
    rw [hw0v] at hwv
    have hl : (wrRegs.take i.val).length = (V.take i.val).length := by
      simp [List.length_take]; omega
    refine WP.spec_bind (set_reg_rg_inv hH hP hd hI' hl wrRegs[i.val] V[i.val]! w hwv) ?_
    rintro s2 hI2
    obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hi4 : i4.val = i.val + 1 := by simpa using h4v
    refine ⟨⟨by show i4.val ≤ min n.val 18; rw [hi4]; exact Nat.le_min.2 ⟨by omega, by omega⟩, ?_⟩,
      by show 18 - i4.val < 18 - i.val; omega⟩
    show RgInv (L := L) T E R B SR s0 σ0 dest x0 s2 (wrRegs.take i4.val) (V.take i4.val)
    have hVl' : i.val < V.length := by omega
    have hiL : i.val < wrRegs.length := by rw [wrRegs_length]; omega
    rw [hi4, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl']
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl']
    exact hI2
  · exact ⟨by simp, by simpa using hI⟩

set_option maxHeartbeats 4000000 in
/-- **The integer-register loop of `write_registers`.** -/
theorem wr_loop1 (hH : EpHyps st T E R B SR) (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    {dest : U64} (hd : dest ∈ T) {x0 : Fl4Spec.Tcb} {ct buf n : U64} (hn : n.val ≤ 20) {V : List Fl4Spec.Word}
    (hVl : n.val ≤ V.length) (hRd : WrRead (L := L) T E R B SR s0 σ0 dest x0 ct buf n V)
    (s1 : S) (hI : RgInv (L := L) T E R B SR s0 σ0 dest x0 s1 (wrRegs.take (min n.val 18)) (V.take (min n.val 18))) :
    tcb.write_registers_loop1 st s1 dest buf ct n 0#u64 ⦃ s2 =>
      RgInv (L := L) T E R B SR s0 σ0 dest x0 s2 (wrRegs.take n.val) (V.take n.val) ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hgl : Fl4Spec.gpRegisters.length = 2 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.write_registers_loop1
  apply loop.spec_decr_nat (measure := fun x => 2 - x.2.val)
    (inv := fun x => x.2.val ≤ 2 ∧ (18 + x.2.val ≤ n.val ∨ (x.2.val = 0 ∧ n.val ≤ 18)) ∧
      RgInv (L := L) T E R B SR s0 σ0 dest x0 x.1 (wrRegs.take (min n.val (18 + x.2.val)))
        (V.take (min n.val (18 + x.2.val))))
  · rintro ⟨s', k⟩ ⟨hk2, hkn, hI'⟩
    unfold tcb.write_registers_loop1.body
    simp only at hk2 hkn hI' ⊢
    by_cases h1 : k < tcb.N_GP
    swap
    · rw [if_neg h1, WP.spec_ok]
      have hk : k.val = 2 := by have := (P1.gt_iff_val).not.1 h1; rw [hg] at this; omega
      have : min n.val (18 + k.val) = n.val := by omega
      rw [this] at hI'; exact hI'
    rw [if_pos h1]
    have hk2' : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rwa [hg] at this
    obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
    rw [hie, bind_ok]
    have hiv' : i.val = k.val + 18 := by rw [← hf]; simpa using hiv
    by_cases h2 : i < n
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : min n.val (18 + k.val) = n.val := by have := (P1.gt_iff_val).not.1 h2; omega
      rw [this] at hI'; exact hI'
    rw [if_pos h2]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h2
    have hm : min n.val (18 + k.val) = i.val := by omega
    rw [hm] at hI'
    simp only [lift, bind_ok]
    refine WP.spec_bind (Array.index_usize_spec _ _ (by rw [cast_to_us' k (by omega)]; simp; omega)) ?_
    rintro r hr
    have hrv : r = regIdx wrRegs[i.val] := by
      rw [hr, List.getElem_of_eq gp_regs_val, List.getElem_map]
      congr 1
      simp only [wrRegs, hiv', cast_to_us' k (by omega)]
      rw [List.getElem_append_right (by rw [hfl]; omega)]
      simp [hfl]
    subst hrv
    obtain ⟨i2, h2e, h2v⟩ := spec_exists (U64.add_spec (x := i) (y := 2#u64) (by scalar_tac))
    rw [h2e, bind_ok]
    have hi2 : i2.val = i.val + 2 := by simpa using h2v
    obtain ⟨w0, hw0, hw0v⟩ := hRd i.val i2 s' hi2 hin hI'
    rw [hw0, bind_ok]
    obtain ⟨w, hw, hwv⟩ := sanitise_eq wrRegs[i.val] w0
    rw [hw, bind_ok]
    rw [hw0v] at hwv
    have hl : (wrRegs.take i.val).length = (V.take i.val).length := by
      simp [List.length_take]; omega
    refine WP.spec_bind (set_reg_rg_inv hH hP hd hI' hl wrRegs[i.val] V[i.val]! w hwv) ?_
    rintro s2 hI2
    obtain ⟨k1, h4e, h4v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hk1 : k1.val = k.val + 1 := by simpa using h4v
    refine ⟨⟨by show k1.val ≤ 2; omega, by show 18 + k1.val ≤ n.val ∨ (k1.val = 0 ∧ n.val ≤ 18); omega, ?_⟩,
      by show 2 - k1.val < 2 - k.val; omega⟩
    show RgInv (L := L) T E R B SR s0 σ0 dest x0 s2 (wrRegs.take (min n.val (18 + k1.val)))
      (V.take (min n.val (18 + k1.val)))
    have hm1 : min n.val (18 + k1.val) = i.val + 1 := by omega
    have hVl' : i.val < V.length := by omega
    have hiL : i.val < wrRegs.length := by rw [wrRegs_length]; omega
    rw [hm1, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl']
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl']
    exact hI2
  · refine ⟨by simp, by simp; omega, ?_⟩
    simpa using hI

end Loops

section Read
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

set_option maxHeartbeats 4000000 in
/-- **`WrRead` from the arguments at the loop's start**: a register argument
(2 or 3, read before any write could reach it: the target's first write is
`FaultIP`) or a word of the caller's mapped IPC buffer (no TCB word). -/
theorem wrRead_of (hP : EPlaced T E R B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    (hR0 : EpStateRel T E R B (L.mem s0) σ0) {dest : U64} (hd : dest ∈ T) {x0 : Fl4Spec.Tcb}
    (hk0 : σ0.kheap dest.bv = some (.tcb x0)) {ct : U64} (hct : ct ∈ T) {buf : U64} {sp : Fl4Spec.Word}
    (hbm : buf ≠ 0#u64 → BufMap B buf sp) {n : U64} (hn : n.val ≤ 20) {V : List Fl4Spec.Word}
    (hargs : ∀ (j : Nat) (i2 : U64), i2.val = j + 2 → j < n.val →
      ∃ w, msg.syscall_arg st s0 ct buf i2 = ok w ∧ w.bv = V[j]!) :
    WrRead (L := L) T E R B SR s0 σ0 dest x0 ct buf n V := by
  intro j i2 s' hi2 hj hI
  obtain ⟨w, hw, hwv⟩ := hargs j i2 hi2 hj
  refine ⟨w, ?_, hwv⟩
  rw [← hw]
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have reg_eq : ∀ (u : S) (t i : U64), obj.Tcb.reg st t u i = ok (L.mem u (regA t i)) := by
    intro u t i
    obtain ⟨v, hv, hv'⟩ := Sched.rrt_exists (Endp.obj.Tcb.reg.spec (st := st) u t i); rw [hv, hv']
  have bg_eq : ∀ (u : S) (w i : U64), msg.buf_get st u w i = ok (L.mem u (fl4BufA w i)) := by
    intro u w i
    obtain ⟨v, hv, hv'⟩ := Sched.rrt_exists (msg.buf_get.spec (st := st) u w i); rw [hv, hv']
  unfold msg.syscall_arg
  by_cases h4 : i2 < msg.N_MSG_REGISTERS
  · rw [if_pos h4, if_pos h4]
    have h4' : i2.val < 4 := by have := (P1.gt_iff_val).1 h4; rwa [hN] at this
    obtain ⟨r, hr, rfl⟩ := Sched.rrt_exists (msg_register_spec i2 h4')
    rw [hr, bind_ok, bind_ok, reg_eq, reg_eq]
    congr 1
    by_cases hcd : ct = dest
    · subst hcd
      have h1 := (hI.1.at_tcb (x := sanRegs x0 (wrRegs.take j) (V.take j)) hd (by simp [updK])).regs (mrIdx i2.val)
      have h0 := (hR0.at_tcb hd hk0).regs (mrIdx i2.val)
      apply eq_of_bv
      rw [h1, h0]
      have hj1 : j = 0 ∨ j = 1 := by omega
      rcases hj1 with rfl | rfl
      · rfl
      · rw [hi2]
        cases V with
        | nil => rfl
        | cons v vs =>
          show (setReg x0 .faultIP (Fl4Spec.sanitiseRegister false .faultIP v)).tcbArch.tcbContext.userRegs (mrIdx 3) = _
          rw [Notif.setReg_regs, Function.update_of_ne (by decide)]
    · exact snd_reg_keep hP hct hd hcd hI.2.2.1 _
  · rw [if_neg h4, if_neg h4]
    by_cases hb : buf != 0#u64
    · rw [if_pos hb, if_pos hb]
      have hb0 : buf ≠ 0#u64 := by simpa using hb
      simp only [lift, bind_ok]
      rw [bg_eq, bg_eq]
      congr 1
      set k := core.num.U64.wrapping_add i2 1#u64 with hk
      have hkv : k.val = i2.val + 1 := by
        rw [hk]; simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      exact buf_keep hP hd hI.2.2.1 (hbm hb0 k (by omega))
    · rw [if_neg hb, if_neg hb]

end Read

section Spec
open Fl4Spec

theorem zipSanM_uc (uc : UserContext) : ∀ (rs : List Register) (vs : List Word),
    ∃ l, NonDet.zipWithM (fun r v => setRegister r (sanitiseRegister false r v)) rs vs uc =
      ({(l, ucSan uc rs vs)}, False)
  | r :: rs, v :: vs => by
    obtain ⟨l, hl⟩ := zipSanM_uc (setRegUc uc r (sanitiseRegister false r v)) rs vs
    refine ⟨() :: l, ?_⟩
    show (NonDet.bind (setRegister r _) fun c => NonDet.bind (NonDet.zipWithM _ rs vs) fun cs => NonDet.pure (c :: cs)) uc = _
    rw [show (NonDet.bind (setRegister r (sanitiseRegister false r v)) fun c =>
        NonDet.bind (NonDet.zipWithM (fun r v => setRegister r (sanitiseRegister false r v)) rs vs) fun cs =>
          NonDet.pure (c :: cs)) =
        (setRegister r (sanitiseRegister false r v) >>= fun c =>
          NonDet.zipWithM (fun r v => setRegister r (sanitiseRegister false r v)) rs vs >>= fun cs =>
            pure (c :: cs)) from rfl]
    rw [nd_bind_one (show setRegister r (sanitiseRegister false r v) uc =
      ({((), setRegUc uc r (sanitiseRegister false r v))}, False) from rfl), nd_bind_one hl]
    rfl
  | [], _ => ⟨[], rfl⟩
  | _ :: _, [] => ⟨[], rfl⟩

/-- The spec's WriteRegisters, before its empty result. -/
def specWr (dest : ObjRef) (resume : Bool) (V : List Word) : SMonad Unit Unit := do
  let self ← NonDet.gets fun s : State Unit => s.curThread
  let b ← archGetSanitiseRegisterInfo dest
  asUser dest <| do
    let _ ← NonDet.zipWithM (fun r v => setRegister r (sanitiseRegister b r v))
      (frameRegisters ++ gpRegisters) V
    let pc ← getRestartPC
    setNextPC pc
  archPostModifyRegisters self dest
  NonDet.when resume <| restart dest
  NonDet.when (dest = self) rescheduleRequired

/-- The register part of the spec's WriteRegisters. -/
theorem wr_regs_eq {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x)) (V : List Word) :
    asUser (Z := Unit) t (do
      let _ ← NonDet.zipWithM (fun r v => setRegister r (sanitiseRegister false r v))
        (frameRegisters ++ gpRegisters) V
      let pc ← getRestartPC
      setNextPC pc) σ =
      ({((), updK σ t (.tcb (setReg (sanRegs x (frameRegisters ++ gpRegisters) V) .nextIP
        ((sanRegs x (frameRegisters ++ gpRegisters) V).tcbArch.tcbContext.userRegs .faultIP))))}, False) := by
  obtain ⟨l, hl⟩ := zipSanM_uc (archTcbContextGet x.tcbArch) (frameRegisters ++ gpRegisters) V
  rw [asUser_det hk (a := ()) (uc' := setRegUc (ucSan (archTcbContextGet x.tcbArch) (frameRegisters ++ gpRegisters) V) .nextIP
    ((ucSan (archTcbContextGet x.tcbArch) (frameRegisters ++ gpRegisters) V).userRegs .faultIP))
    (by
      rw [nd_bind_one hl, nd_bind_one (show getRestartPC (ucSan (archTcbContextGet x.tcbArch) (frameRegisters ++ gpRegisters) V) =
        ({((ucSan (archTcbContextGet x.tcbArch) (frameRegisters ++ gpRegisters) V).userRegs .faultIP,
          ucSan (archTcbContextGet x.tcbArch) (frameRegisters ++ gpRegisters) V)}, False) from rfl)]
      rfl)]
  rw [← sanRegs_eq]
  rfl

end Spec

end

end Fl4Proofs.P3.Endp

namespace Fl4Proofs.P3.Ipc
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Sched

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
variable {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

/-- FL4's current thread, as the spec's (`SchedRel`). -/
theorem cur_thread_bv {s : S} {σ : Fl4Spec.State Unit} (hS : SchedRel st N T C c s σ) :
    sched.cur_thread st s ⦃ v => v.bv = σ.curThread ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  refine WP.spec_mono (P1.sched.cur_thread.spec s) ?_
  rintro v rfl
  rw [hs.curThread, ← hc.cur]; rfl

end

end

end Fl4Proofs.P3.Ipc

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

theorem and1_ne0 (f : U64) : ((f &&& 1#u64) != 0#u64) = Fl4Spec.testBit f.bv 0 := by
  have e : (f &&& 1#u64).val = f.val % 2 := by
    simp [UScalar.val_and, Nat.and_one_is_mod]
  show _ = f.val.testBit 0
  rw [Nat.testBit_zero]
  have h2 : f.val % 2 = 0 ∨ f.val % 2 = 1 := by omega
  rcases h2 with h | h
  · have : (f &&& 1#u64) = 0#u64 := UScalar.eq_of_val_eq (by rw [e, h]; rfl)
    simp [this, h]
  · have : (f &&& 1#u64) ≠ 0#u64 := fun h' => by have := congrArg UScalar.val h'; rw [e, h] at this; simp at this
    simp [this, h]

theorem invokeTcb_wr (dest : Fl4Spec.ObjRef) (resume : Bool) (V : List Fl4Spec.Word) (arch : Fl4Spec.ArchCopyRegisterSets) :
    Fl4Spec.invokeTcb (Z := Unit) (.writeRegisters dest resume V arch) =
      Fl4Spec.NonDetE.liftE (specWr dest resume V >>= fun _ => pure []) := by
  unfold Fl4Spec.invokeTcb specWr
  simp only [Fl4Proofs.P3.Sched.nd_assoc_f]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

end

end

end Fl4Proofs.P3
