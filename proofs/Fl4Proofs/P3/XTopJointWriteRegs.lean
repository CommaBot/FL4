/-
P3 (DESIGN.md §9), TCB: **WriteRegisters' work at `J`** (IpcWriteRegsJ's
`write_registers_irelS` with `JAtZ` carried; the label itself is
XTopJointTcb's `tcb_write_regsJ`).

* `reg_wr_irelN`: `IRel` across any register write of a TCB (IpcSuspend's
  `reg_wr_irel` without its `badge_register` exclusion: the notification
  relation by `ntfn_lift_rcv`).
* `JAtZ.sanWrJ`: the next sanitised register of the target at `J`
  (`JAtZ.regWrJ`), the spec's TCB `sanRegs` growing by the register.
* `wrJ_loop0`, `wrJ_loop1`: `write_registers`' loops (as `wr_loop0`,
  `wr_loop1`) with `JAtZ` and FL4's write set (the target's register words)
  carried beside IpcFaultReply's `RgInv`.
* `JAtZ.writeRegsJ`: `tcb::write_registers` at `J` for a target other than
  the caller: the loops, the restart PC and `post_modify_registers`
  (`JAtZ.regWrJ`), then, resumed, XTopJointRestart's `JAtZ.restartTcbJ`
  (the target's cap in a slot kept across the register words by
  `IRel.iframe_of`; `CurInv`, `CurRun` and no switch kept: the caller's TCB
  untouched), its spec outcome `specWr`.
-/
import Fl4Proofs.P3.XTopJointRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`IRel` across a register write of a TCB** (module docstring). -/
theorem reg_wr_irelN {th : TypedHeap} {cr : Fl4Spec.Cr3} {N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}
    {c : U64} (hP0 : IPlaced N T E R B) {s : S} {σ : Fl4Spec.State Unit}
    (hX : IRel st th cr N T C E R B c s σ) {t : U64} (ht : t ∈ T) {x : Fl4Spec.Tcb}
    (hk : σ.kheap t.bv = some (.tcb x)) (r : Fl4Spec.Register) (v : U64) :
    IRel st th cr N T C E R B c (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) := by
  obtain ⟨hIR, hSRT⟩ := hX
  have hPe := hP0.e
  obtain ⟨hR1, hW1, hS1⟩ := write_reg_rel hPe s σ hIR.toE ht hk r v
  have hSRT' : SRT st th cr N T C E R B c (SRE st N T C E R B c)
      (L.wr s (regA t (regIdx r)) v) (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))) :=
    ⟨hSRT.1.stableE hW1 hS1, hSRT.2.1.stableE hPe hSRT.2.2 hW1 hS1, hSRT.2.2.mono hW1.1 (SzKeep.epStep hS1)⟩
  have hN := ntfn_lift_rcv hP0.toC hIR.toN hR1 ht ((agree_wr_reg (hPe.tcb t ht) r v).mono fun _ h => h.1)
    (fun q hq => by simp [Notif.updK, hq]) hk
    (show (Notif.updK σ t.bv (.tcb (Notif.setReg x r v.bv))).kheap t.bv = some (.tcb (Notif.setReg x r v.bv)) by
      simp [Notif.updK]) rfl
  exact ⟨IpcRel.of hN hR1 (sched_sc hSRT'.2.1), hSRT'⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A}

set_option maxHeartbeats 8000000 in
/-- **The next sanitised register of the target at `J`** (module docstring). -/
theorem JAtZ.sanWrJ {σ0 : Fl4Spec.State Unit} {p : U64} {x0 : Fl4Spec.Tcb} {rs : List Fl4Spec.Register}
    {vs : List Fl4Spec.Word} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a (updK σ0 p.bv (.tcb (sanRegs x0 rs vs))))
    (hpT : p ∈ Z.T) (hl : rs.length = vs.length) (r : Fl4Spec.Register) (v : Fl4Spec.Word) (w : U64)
    (hw : w.bv = Fl4Spec.sanitiseRegister false r v) :
    ∃ V, JAtZ (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D (L.wr s (regA p (regIdx r)) w) a
      (updK σ0 p.bv (.tcb (sanRegs x0 (rs ++ [r]) (vs ++ [v])))) := by
  have hk : (updK σ0 p.bv (.tcb (sanRegs x0 rs vs))).kheap p.bv = some (.tcb (sanRegs x0 rs vs)) := by
    simp [updK]
  have hX := reg_wr_irelN J.ip (J.xtop.irelK J.ks J.buf) hpT hk r w
  obtain ⟨V, J1⟩ := J.regWrJ hpT hk r w hX
  refine ⟨V, ?_⟩
  have e : updK (updK σ0 p.bv (.tcb (sanRegs x0 rs vs))) p.bv (.tcb (setReg (sanRegs x0 rs vs) r w.bv)) =
      updK σ0 p.bv (.tcb (sanRegs x0 (rs ++ [r]) (vs ++ [v]))) := by
    rw [sanRegs_snoc x0 rs vs hl r v, ← hw]; simp only [updK, Function.update_idem]
  rw [← e]; exact J1

/-- One register write of the target inside its register words. -/
theorem wr_regW {s' : S} {p : U64} (hpT : P1.TcbAddr p) (r : Fl4Spec.Register) (w : U64) {s0 : S}
    (hw : P1.WritesIn st s0 s' (RcvReg p)) :
    P1.WritesIn st s0 (L.wr s' (regA p (regIdx r)) w) (RcvReg p) :=
  (hw.trans (P1.writesIn_wr (a_reg hpT r).1)).mono fun _ hb =>
    hb.elim id fun e => ⟨r, congrArg UScalar.val e⟩

set_option maxHeartbeats 8000000 in
/-- **The frame-register loop of `write_registers` at `J`** (as `wr_loop0`). -/
theorem wrJ_loop0 {SR : S → Fl4Spec.State Unit → Prop} (hH : EpHyps st Z.T Z.E Z.R Z.B SR)
    (hP : EPlaced Z.T Z.E Z.R Z.B) {s0 : S} {σ0 : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s0 a σ0)
    {dest : U64} (hd : dest ∈ Z.T) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap dest.bv = some (.tcb x0))
    {ct buf n : U64} (hn : n.val ≤ 20) {V : List Fl4Spec.Word}
    (hVl : n.val ≤ V.length) (hRd : WrRead (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 ct buf n V)
    (hI : RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 s0 [] []) :
    tcb.write_registers_loop0 st s0 dest buf ct n 0#u64 ⦃ s2 =>
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 s2 (wrRegs.take (min n.val 18)) (V.take (min n.val 18)) ∧
      (∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s2 a
        (updK σ0 dest.bv (.tcb (sanRegs x0 (wrRegs.take (min n.val 18)) (V.take (min n.val 18)))))) ∧
      P1.WritesIn st s0 s2 (RcvReg dest) ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hgl : Fl4Spec.gpRegisters.length = 2 := rfl
  have hwl : wrRegs.length = 20 := rfl
  have hta := hP.tcb dest hd
  unfold tcb.write_registers_loop0
  apply loop.spec_decr_nat (measure := fun x => 18 - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 18 ∧
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 x.1 (wrRegs.take x.2.val) (V.take x.2.val) ∧
      (∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D x.1 a
        (updK σ0 dest.bv (.tcb (sanRegs x0 (wrRegs.take x.2.val) (V.take x.2.val))))) ∧
      P1.WritesIn st s0 x.1 (RcvReg dest))
  · rintro ⟨s', i⟩ ⟨hi, hI', ⟨V', J'⟩, hw'⟩
    unfold tcb.write_registers_loop0.body
    simp only at hi hI' J' hw' ⊢
    by_cases h1 : i < tcb.N_FRAME
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h1; rw [hf] at this; omega
      rw [← this]; exact ⟨hI', ⟨V', J'⟩, hw'⟩
    rw [if_pos h1]
    have hi18 : i.val < 18 := by have := (P1.gt_iff_val).1 h1; rwa [hf] at this
    by_cases h2 : i < n
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h2; omega
      rw [← this]; exact ⟨hI', ⟨V', J'⟩, hw'⟩
    rw [if_pos h2]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h2
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
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
    refine WP.spec_bind (WP.spec_and (set_reg_rg_inv hH hP hd hI' hl wrRegs[i.val] V[i.val]! w hwv)
      (Endp.obj.Tcb.set_reg.spec s' dest _ w)) ?_
    rintro s2 ⟨hI2, rfl⟩
    obtain ⟨V2, J2⟩ := J'.sanWrJ hd hl wrRegs[i.val] V[i.val]! w hwv
    have hw2 := wr_regW hta wrRegs[i.val] w hw'
    obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hi4 : i4.val = i.val + 1 := by simpa using h4v
    refine ⟨⟨by show i4.val ≤ min n.val 18; rw [hi4]; exact Nat.le_min.2 ⟨by omega, by omega⟩, ?_⟩,
      by show 18 - i4.val < 18 - i.val; omega⟩
    dsimp only
    have hVl' : i.val < V.length := by omega
    have hiL : i.val < wrRegs.length := by rw [wrRegs_length]; omega
    rw [hi4, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl']
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl']
    exact ⟨hI2, ⟨V2, J2⟩, hw2⟩
  · refine ⟨by simp, by simpa using hI, ⟨Z.vs, ?_⟩, P1.WritesIn.refl _ _⟩
    show JAtZ (L := L) arI AR (Z.mv Z.G Z.vs) H Cs Ac Lst D s0 a (updK σ0 dest.bv (.tcb (sanRegs x0 [] [])))
    rw [show sanRegs x0 [] [] = x0 from rfl, Endp.updK_self hk0]
    simpa using J

set_option maxHeartbeats 8000000 in
/-- **The integer-register loop of `write_registers` at `J`** (as
`wr_loop1`). -/
theorem wrJ_loop1 {SR : S → Fl4Spec.State Unit → Prop} (hH : EpHyps st Z.T Z.E Z.R Z.B SR)
    (hP : EPlaced Z.T Z.E Z.R Z.B) {s0 s1 : S} {σ0 : Fl4Spec.State Unit}
    {dest : U64} (hd : dest ∈ Z.T) {x0 : Fl4Spec.Tcb}
    {ct buf n : U64} (hn : n.val ≤ 20) {V : List Fl4Spec.Word}
    (hVl : n.val ≤ V.length) (hRd : WrRead (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 ct buf n V)
    (hI : RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 s1 (wrRegs.take (min n.val 18)) (V.take (min n.val 18)))
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a
        (updK σ0 dest.bv (.tcb (sanRegs x0 (wrRegs.take (min n.val 18)) (V.take (min n.val 18))))))
    (hw : P1.WritesIn st s0 s1 (RcvReg dest)) :
    tcb.write_registers_loop1 st s1 dest buf ct n 0#u64 ⦃ s2 =>
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 s2 (wrRegs.take n.val) (V.take n.val) ∧
      (∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D s2 a
        (updK σ0 dest.bv (.tcb (sanRegs x0 (wrRegs.take n.val) (V.take n.val))))) ∧
      P1.WritesIn st s0 s2 (RcvReg dest) ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hgl : Fl4Spec.gpRegisters.length = 2 := rfl
  have hwl : wrRegs.length = 20 := rfl
  have hta := hP.tcb dest hd
  unfold tcb.write_registers_loop1
  apply loop.spec_decr_nat (measure := fun x => 2 - x.2.val)
    (inv := fun x => x.2.val ≤ 2 ∧ (18 + x.2.val ≤ n.val ∨ (x.2.val = 0 ∧ n.val ≤ 18)) ∧
      RgInv (L := L) Z.T Z.E Z.R Z.B SR s0 σ0 dest x0 x.1 (wrRegs.take (min n.val (18 + x.2.val)))
        (V.take (min n.val (18 + x.2.val))) ∧
      (∃ V', JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac Lst D x.1 a
        (updK σ0 dest.bv (.tcb (sanRegs x0 (wrRegs.take (min n.val (18 + x.2.val)))
          (V.take (min n.val (18 + x.2.val))))))) ∧
      P1.WritesIn st s0 x.1 (RcvReg dest))
  · rintro ⟨s', k⟩ ⟨hk2, hkn, hI', ⟨V', J'⟩, hw'⟩
    unfold tcb.write_registers_loop1.body
    simp only at hk2 hkn hI' J' hw' ⊢
    by_cases h1 : k < tcb.N_GP
    swap
    · rw [if_neg h1, WP.spec_ok]
      have hk : k.val = 2 := by have := (P1.gt_iff_val).not.1 h1; rw [hg] at this; omega
      have : min n.val (18 + k.val) = n.val := by omega
      rw [this] at hI' J'; exact ⟨hI', ⟨V', J'⟩, hw'⟩
    rw [if_pos h1]
    have hk2' : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rwa [hg] at this
    obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
    rw [hie, bind_ok]
    have hiv' : i.val = k.val + 18 := by rw [← hf]; simpa using hiv
    by_cases h2 : i < n
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : min n.val (18 + k.val) = n.val := by have := (P1.gt_iff_val).not.1 h2; omega
      rw [this] at hI' J'; exact ⟨hI', ⟨V', J'⟩, hw'⟩
    rw [if_pos h2]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h2
    have hm : min n.val (18 + k.val) = i.val := by omega
    rw [hm] at hI' J'
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' k (by omega)]; simp; omega)) ?_
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
    refine WP.spec_bind (WP.spec_and (set_reg_rg_inv hH hP hd hI' hl wrRegs[i.val] V[i.val]! w hwv)
      (Endp.obj.Tcb.set_reg.spec s' dest _ w)) ?_
    rintro s2 ⟨hI2, rfl⟩
    obtain ⟨V2, J2⟩ := J'.sanWrJ hd hl wrRegs[i.val] V[i.val]! w hwv
    have hw2 := wr_regW hta wrRegs[i.val] w hw'
    obtain ⟨k1, h4e, h4v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hk1 : k1.val = k.val + 1 := by simpa using h4v
    refine ⟨⟨by show k1.val ≤ 2; omega, by show 18 + k1.val ≤ n.val ∨ (k1.val = 0 ∧ n.val ≤ 18); omega, ?_⟩,
      by show 2 - k1.val < 2 - k.val; omega⟩
    dsimp only
    have hm1 : min n.val (18 + k1.val) = i.val + 1 := by omega
    have hVl' : i.val < V.length := by omega
    have hiL : i.val < wrRegs.length := by rw [wrRegs_length]; omega
    rw [hm1, List.take_succ, List.take_succ, List.getElem?_eq_getElem hiL, List.getElem?_eq_getElem hVl']
    simp only [Option.toList_some]
    rw [← getElem!_pos V i.val hVl']
    exact ⟨hI2, ⟨V2, J2⟩, hw2⟩
  · refine ⟨by simp, by simp; omega, by simpa using hI, ⟨Z.vs, by simpa using J⟩, hw⟩


set_option maxHeartbeats 32000000 in
/-- **`write_registers` at `J`** (module docstring): the target `p` not the
caller `ct`; its cap in a slot (`hxS`, `hcap`, for `JAtZ.restartTcbJ`);
`CurInv`, `CurRun` and no switch at the start (the caller's restart's);
the caller's buffer mapped and the syscall arguments read at the start
(`wrRead_of`); the platform's `MIN_BUDGET` [P]. -/
theorem JAtZ.writeRegsJ (hAT : P0.ArchTotal arI)
    (hSd : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e d, ts = .blockedOnSend e d)
    (hNt : JCancelAt (L := L) arI AR Z.th fun ts => ∃ n, ts = .blockedOnNotification n)
    (hRv : JCancelAt (L := L) arI AR Z.th fun ts => ∃ e r d, ts = .blockedOnReceive e r d)
    (hRp : JCancelAt (L := L) arI AR Z.th fun ts => ∃ r, ts = .blockedOnReply r)
    (hmb : sporadic.min_budget arI a ⦃ mb => mb.bv = Fl4Spec.MIN_BUDGET ⦄)
    {s1 : S} {σ1 : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s1 a σ1)
    {p ct buf : U64} (hpT : p ∈ Z.T) (hpc : p ≠ ct) (hcur : σ1.curThread = ct.bv) (hctT : ct ∈ Z.T)
    {x0 : U64} (hxS : IsSlot Z.th x0) (hcap : capAt (L.mem s1) x0 = ok (.Thread p))
    (hC : CurInv σ1) (hns : ∀ u, σ1.schedulerAction ≠ .switchThread u) (hcr : CurRun σ1)
    {sp : Fl4Spec.Word} (hbm : buf ≠ 0#u64 → BufMap Z.B buf sp)
    (resume : Bool) (n : U64) {V : List Fl4Spec.Word} (hVn : V.length = n.val)
    (hargs : ∀ (j : Nat) (i2 : U64), i2.val = j + 2 → j < n.val →
      ∃ w, msg.syscall_arg st s1 ct buf i2 = ok w ∧ w.bv = V[j]!) :
    tcb.write_registers st arI s1 a p resume n buf ⦃ r => r.2 = a ∧ ∃ σ',
      specWr p.bv resume V σ1 = ({((), σ')}, False) ∧
      ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ := by
  have hP0 := J.ip
  have hI := J.xtop.irelK J.ks J.buf
  have hS := hI.2.2.1
  have hta := hP0.e.tcb p hpT
  have hne : p.bv ≠ ct.bv := fun e => hpc (P1.eq_of_bv e)
  obtain ⟨x, hk, -⟩ := hI.1.tcb p hpT
  unfold tcb.write_registers
  refine WP.spec_bind (cur_thread_bv hS) ?_
  rintro ct' hct'
  obtain rfl : ct = ct' := (P1.eq_of_bv (hct'.trans hcur)).symm
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := tcb.N_FRAME) (y := tcb.N_GP) (by rw [hf, hg]; scalar_tac))
  rw [hie, bind_ok]
  have hi20 : i.val = 20 := by have := hiv; simp only [hf, hg] at this ⊢; omega
  obtain ⟨n', hn'e, hn'v⟩ : ∃ n' : U64, (if n > i then ok i else ok n : Result U64) = ok n' ∧
      n'.val = min n.val 20 := by
    by_cases h : n > i
    · exact ⟨i, if_pos h, by have := (P1.gt_iff_val).1 h; omega⟩
    · exact ⟨n, if_neg h, by have := (P1.gt_iff_val).not.1 h; omega⟩
  rw [hn'e, bind_ok]
  have hH := ipcCore_top (st := st) (th := Z.th) (cr := σ1.archState.x64CurrentCr3) (N := Z.N) (C := Z.C)
    (c := Z.c) hP0.e
  have hEH := hH.epHyps hP0
  have hSR := IpcRel.toSRN hI.1 hI.2
  have hI0 := rgInv_init (L := L) (T := Z.T) (E := Z.E) (R := Z.R) (B := Z.B) hI.1.toE hSR.1 hk
  have hn20 : n'.val ≤ 20 := by omega
  have hVl : n'.val ≤ V.length := by omega
  have hRd : WrRead (L := L) Z.T Z.E Z.R Z.B
      (SRS st Z.T (SRT st Z.th σ1.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c
        (SRE st Z.N Z.T Z.C Z.E Z.R Z.B Z.c))) s1 σ1 p x ct buf n' V :=
    wrRead_of hP0.e hI.1.toE hpT hk hctT hbm hn20 fun j i2 hi2 hj => hargs j i2 hi2 (by omega)
  refine WP.spec_bind (wrJ_loop0 hEH hP0.e J hpT hk hn20 hVl hRd hI0) ?_
  rintro s2 ⟨hI2, ⟨V2, J2⟩, hw2⟩
  refine WP.spec_bind (wrJ_loop1 (Z := Z.mv Z.G V2) hEH hP0.e hpT hn20 hVl hRd hI2 J2 hw2) ?_
  rintro s3 ⟨-, ⟨V3, J3⟩, hw3⟩
  rw [sanRegs_take x wrRegs V n'.val (by rw [wrRegs_length]; omega)] at J3
  set x2 := sanRegs x wrRegs V with hx2
  have hX3 := J3.xtop.irelK J3.ks J3.buf
  have hk2 : (updK σ1 p.bv (.tcb x2)).kheap p.bv = some (.tcb x2) := by simp [updK]
  obtain ⟨x2', hk2', hTR2⟩ := hX3.1.tcb p hpT
  rw [hk2] at hk2'; cases hk2'
  -- the restart PC
  have hF : layout.reg.FAULT_IP = regIdx .faultIP := by unfold layout.reg.FAULT_IP; rfl
  have hNx : layout.reg.NEXT_IP = regIdx .nextIP := by unfold layout.reg.NEXT_IP; rfl
  refine WP.spec_bind (Endp.obj.Tcb.reg.spec s3 p _) ?_
  rintro pc hpc'
  have hpcv : pc.bv = x2.tcbArch.tcbContext.userRegs .faultIP := by rw [hpc', hF]; exact hTR2.regs .faultIP
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s3 p _ pc) ?_
  rintro s4 rfl
  rw [hNx]
  obtain ⟨V4, J4⟩ := J3.regWrJ hpT hk2 .nextIP pc (reg_wr_irelN J3.ip hX3 hpT hk2 .nextIP pc)
  rw [hpcv] at J4
  set x3 := setReg x2 .nextIP (x2.tcbArch.tcbContext.userRegs .faultIP) with hx3
  have e3 : updK (updK σ1 p.bv (.tcb x2)) p.bv (.tcb x3) = updK σ1 p.bv (.tcb x3) := by
    simp only [updK, Function.update_idem]
  rw [e3] at J4
  have hk3 : (updK σ1 p.bv (.tcb x3)).kheap p.bv = some (.tcb x3) := by simp [updK]
  have hX4 := J4.xtop.irelK J4.ks J4.buf
  -- `post_modify_registers`: the target is not the caller
  have hpm : tcb.post_modify_registers st (L.wr s3 (regA p (regIdx .nextIP)) pc) p ⦃ s5 =>
      s5 = L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc) (regA p (regIdx .errorRegister)) 0#u64 ⦄ := by
    unfold tcb.post_modify_registers
    refine WP.spec_bind (cur_thread_bv hX4.2.2.1) ?_
    rintro ct3 hc3
    obtain rfl : ct = ct3 := (P1.eq_of_bv (hc3.trans hcur)).symm
    rw [tcb_ne_eq, bind_ok]
    simp only [ne_eq, hpc, not_false_eq_true, decide_true, ↓reduceIte]
    have hE : layout.reg.ERROR = regIdx .errorRegister := by unfold layout.reg.ERROR; rfl
    rw [hE]; exact Endp.obj.Tcb.set_reg.spec _ p _ 0#u64
  refine WP.spec_bind hpm ?_
  rintro s5 rfl
  obtain ⟨V5, J5⟩ := J4.regWrJ hpT hk3 .errorRegister 0#u64 (reg_wr_irelN J4.ip hX4 hpT hk3 .errorRegister 0#u64)
  set x4 := setReg x3 .errorRegister (0#u64).bv with hx4
  have e4 : updK (updK σ1 p.bv (.tcb x3)) p.bv (.tcb x4) = updK σ1 p.bv (.tcb x4) := by
    simp only [updK, Function.update_idem]
  rw [e4] at J5
  have hpm4 : Fl4Spec.archPostModifyRegisters (Z := Unit) ct.bv p.bv (updK σ1 p.bv (.tcb x3)) =
      ({((), updK σ1 p.bv (.tcb x4))}, False) := by
    unfold Fl4Spec.archPostModifyRegisters Fl4Spec.NonDet.when
    rw [if_pos (fun e => hpc (P1.eq_of_bv e)), asUser_setRegister_eq _ _ hk3, ← e4]
    rfl
  -- the restart's premises at the state after the register words
  have hX5 := J5.xtop.irelK J5.ks J5.buf
  have hkc : ∀ q, q ≠ p.bv → (updK σ1 p.bv (.tcb x4)).kheap q = σ1.kheap q := fun q hq => by simp [updK, hq]
  have hctp : σ1.curThread ≠ p.bv := by rw [hcur]; exact Ne.symm hne
  have hcr4 : CurRun (updK σ1 p.bv (.tcb x4)) := fun y hy => hcr y ((hkc _ hctp).symm.trans hy)
  have hC4 : CurInv (updK σ1 p.bv (.tcb x4)) := by
    obtain ⟨xt, hkt, h1, h2⟩ := hC.tcb
    obtain ⟨y0, n0, hy0⟩ := hC.sc
    have hscp : σ1.curSc ≠ p.bv := fun e => by rw [e, hk] at hy0; cases hy0
    exact ⟨⟨xt, (hkc _ hctp).trans hkt, h1, h2⟩, ⟨y0, n0, (hkc _ hscp).trans hy0⟩,
      fun hn y n hy => hC.active hn y n ((hkc _ hscp).symm.trans hy), hC.notRel⟩
  have hw5 := wr_regW hta .errorRegister 0#u64 (wr_regW hta .nextIP pc hw3)
  have hIF := IRel.iframe_of hI hw5 fun _ ⟨r, hb⟩ => by
    have := regIdx_lt r
    have hr := regA_val hta (regIdx_lt r)
    exact Or.inr (Or.inr (Or.inl ⟨p, hpT, by omega, by omega⟩))
  have hcap5 : capAt (L.mem (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc) (regA p (regIdx .errorRegister)) 0#u64))
      x0 = ok (.Thread p) := by
    rw [capAt_capV, hIF.1.capV hxS, ← capAt_capV]; exact hcap
  -- the restart
  have hrs : (if resume then sched.restart st arI (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc)
      (regA p (regIdx .errorRegister)) 0#u64) a p else ok (L.wr (L.wr s3 (regA p (regIdx .nextIP)) pc)
      (regA p (regIdx .errorRegister)) 0#u64, a)) ⦃ r => r.2 = a ∧ ∃ σ6,
      Fl4Spec.NonDet.when resume (Fl4Spec.restart (Z := Unit) p.bv) (updK σ1 p.bv (.tcb x4)) =
        ({((), σ6)}, False) ∧ σ6.curThread = ct.bv ∧
      ∃ (V' : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZ (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ6 ⦄ := by
    cases resume
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      exact ⟨trivial, _, rfl, hcur, V5, Ac, Lst, D, J5⟩
    · simp only [↓reduceIte]
      refine WP.spec_mono (WP.spec_and (J5.restartTcbJ (Z := Z.mv Z.G V5) hAT hSd hNt hRv hRp hmb hpT hxS hcap5
        hC4 hns hcr4)
        (restart_tcb_irelS (ar := arI) hP0 (removeTcbHypP_ok hP0) _ a _ hX5 hpT J5.sv J5.obj J5.inv
          (fun x' hk' => removeTcbOK_fault hP0 hX5 hpT hk' J5.removeTcbOK)
          (Sched.restartSpecOK_of J5.inv J5.sv.scSpor) hmb)) ?_
      rintro r ⟨⟨h1, σ6, h2, V', Ac', Lst', D', J6⟩, -, σ6', h2', -, hc6, -⟩
      have e6 : σ6' = σ6 := by
        rw [h2] at h2'; exact ((Prod.mk.inj (Set.singleton_injective (congrArg Prod.fst h2'))).2).symm
      subst e6
      exact ⟨h1, σ6', by simpa [Fl4Spec.NonDet.when] using h2, hc6.trans hcur, V', Ac', Lst', D', J6⟩
  refine WP.spec_bind hrs ?_
  rintro ⟨s6, a1⟩ ⟨rfl, σ6, hrs6, hct6, V6, Ac6, Lst6, D6, J6⟩
  refine WP.spec_bind (cur_thread_bv (J6.xtop.irelK J6.ks J6.buf).2.2.1) ?_
  rintro ct5 hc5
  obtain rfl : ct = ct5 := (P1.eq_of_bv (hc5.trans hct6)).symm
  unfold obj.Tcb.Insts.CoreCmpPartialEqTcb.eq
  simp only [bind_ok, hpc, decide_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
  refine ⟨trivial, σ6, ?_, V6, Ac6, Lst6, D6, J6⟩
  unfold specWr
  rw [nd_gets_bind, hcur, nd_bind_one (show Fl4Spec.archGetSanitiseRegisterInfo (Z := Unit) p.bv σ1 =
    ({(false, σ1)}, False) from rfl), nd_bind_one (wr_regs_eq hk V), nd_bind_one hpm4, nd_bind_one hrs6]
  unfold Fl4Spec.NonDet.when
  rw [if_neg (fun e => hpc (P1.eq_of_bv e))]
  rfl

end

end

end Fl4Proofs.P3
