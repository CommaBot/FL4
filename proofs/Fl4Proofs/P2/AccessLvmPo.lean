/-
# P2 (line lvm, gen 7): **the pending-exit case of `local_vm_exit` under `ownV`** (gen 6's `hP` / `hPm`)

For rule 7's map `OwnMapV.ownV K` and gen 5's sets `VexitRS` / `VexitWS`:

* `VPU K v`: the words the report writes besides the current thread's registers: aligned user words (its IPC
  buffer) and `v.PENDING`;
* `VexitPEnt`: the pending case's entry facts (below);
* `vcpu_rd` / `pending_wr`: every aligned word of a VCPU `v` that does not wrap is readable under `ownV` by the
  holder of `lock v` (rule 7: binding words the gate's, the rest `lock v`'s); `v.PENDING` is writable by it;
* **`vexit_acc_own_p`**: `PathObl.acc` of an accepted run with a pending exit, on
  `guard st (VexitRS …) (VexitWS …)` (`vexit_accG_p`; the buffer words are user words, `v.PENDING` and the VCPU's
  words (VMCS shadow included, P1's `vcpu.vmcs_addr.off`) `lock v`'s, the current thread's `STATE` an `IrqWr`
  word, `irq_wr_own`);
* **`vexit_move_p`**: `PathObl.move` of such a run: on the checked store whose writes are `ownV`'s `StepOK`
  (`StWrOKV`) it is the real run (`vexit_accG_p`: user and VCPU words decide nothing, `stepOK_nondec`; the
  `STATE := RUNNING` write of a thread homed here and not queued, `stepOK_state`), and `interp_gd` makes it the
  run on `mguard`;
* **`vexit_localPathP`**: `local_vm_exit` as an `E2E.LocalPath` under `ownV` with `Pre = VexitEnt ∧ VexitPEnt`,
  gen 6's `vexit_localPath` with its pending-exit premises `hP` / `hPm` discharged.

Premises (fields of `VexitPEnt`):
* `usr` [J]: aligned user words are `UsrW` (outside every TCB, node, endpoint, notification, frame word, the
  kernel-global area and every SC: P1's `UserOK.usrW`, as `vcpu.check.vck`'s user set);
* `pusr` [J]: so is `v.PENDING` (P1 `vcpu.check.vck`'s `hpw` [P]: a VCPU is a heap object of its own);
* `buf` [P]: the current thread's IPC buffer lies in aligned user words (P1 `vcpu.check.vck`'s `hbuf` [P]);
* `vfit` [J]: the VCPU `v` does not wrap (`v + 0x8000 ≤ 2^64`; P1's heap places objects below `2^64`);
* `aff0` [J]: the ownership map's memory `m` agrees with the entry state on the current thread's `AFFINITY` (as
  `IrqEntK.mem`).
Premises of `vexit_localPathP` otherwise gen 6's: `hp` [P], `hz` [W], `hm` [P], `hro` [W], `hK` / `hU` [J],
`VexitEnt`'s fields, `hEU` [J] (now for `VexitEnt ∧ VexitPEnt`), `hlk` [P] (aligned user writes only, gen 10).
-/
import Fl4Proofs.P2.AccessLvmPw
import Fl4Proofs.P2.AccessLvmLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu VcpuGate vcpuOwner RegionOKV UserOKV rpermV_of_own rpermV_vcpu
  wpermV_vcpu wpermV_of_own' stepOKV_of_stepOK ownV_on vcpu_nondec)
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}

/-- The words the report writes besides the registers: aligned user words and `v.PENDING`. -/
def VPU (K : KLayoutV) (v : U64) : Set U64 :=
  {x | (x ∈ K.user ∧ Aligned x) ∨ x = core.num.U64.wrapping_add v vcpu.PENDING}

/-- **The pending-exit case's entry facts** (module docstring). -/
structure VexitPEnt (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap)
    (Sg Scs : Set U64) (Z : U64 → Nat) (m : U64 → U64) (v : U64) (s : S) : Prop where
  usr : ∀ x, x ∈ K.user → Aligned x → UsrW st T Cs H Sg Scs Z s x
  pusr : v ≠ 0#u64 → UsrW st T Cs H Sg Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING)
  buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄
  vfit : v ≠ 0#u64 → v.val + 32768 ≤ 2 ^ 64
  aff0 : m (fld (L.curW s) oAFFINITY) = L.mem s (affA (L.curW s))

theorem vadd_val {v o : U64} (hfit : v.val + 32768 ≤ 2 ^ 64) (ho : o.val < 32768) :
    (core.num.U64.wrapping_add v o).val = v.val + o.val := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, UScalar.size]
  omega

/-- **Every word of a VCPU is readable by the holder of `lock v`** (the binding words being the gate's). -/
theorem vcpu_rd (hK : RegionOKV K) {m : U64 → U64} {c v o : U64} {lk : U64 → Prop} (hv : v ∈ K.vcpus)
    (hfit : v.val + 32768 ≤ 2 ^ 64) (ho : o.val < 32768) (hl : lk v) :
    RPerm (ownV K) c lk m (core.num.U64.wrapping_add v o) := by
  have e := vadd_val hfit ho
  have hin : InVcpu K v (core.num.U64.wrapping_add v o) := ⟨hv, by unfold InW; omega⟩
  by_cases hg : VcpuGate ((core.num.U64.wrapping_add v o).val - v.val)
  · exact Or.inr (by unfold GateOnly; rw [ownV_on hK hin]; simp only [vcpuOwner, if_pos hg])
  · exact rpermV_vcpu hK hin hg hl

/-- `v`'s `PENDING` is writable by the holder of `lock v`. -/
theorem pending_wr (hK : RegionOKV K) {m : U64 → U64} {c v : U64} {lk : U64 → Prop}
    (hin : InVcpu K v (core.num.U64.wrapping_add v vcpu.PENDING)) (hl : lk v) :
    WPerm (ownV K) c lk m (core.num.U64.wrapping_add v vcpu.PENDING) := by
  refine wpermV_vcpu hK hin ?_ hl
  have h1 := hin.2.1
  have h2 := hin.2.2
  have hvb : v.val < 2 ^ 64 := by scalar_tac
  have hv : (core.num.U64.wrapping_add v vcpu.PENDING).val = v.val + 20520 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, UScalar.size] at h1 h2 ⊢
    omega
  rw [hv]
  unfold VcpuGate
  omega

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop} {v n : U64} {m : U64 → U64}

/-- The pending case's report facts in `vexit_accG_p`'s form. -/
theorem VexitPEnt.rep {s : S} (hP : VexitPEnt K st T Cs H Sg Scs Z m v s) (hv0 : v ≠ 0#u64) :
    (∀ x ∈ VPU K v, UsrW st T Cs H Sg Scs Z s x) ∧ core.num.U64.wrapping_add v vcpu.PENDING ∈ VPU K v ∧
      msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK (VPU K v) b ⦄ := by
  refine ⟨fun x hx => ?_, Or.inr rfl, WP.spec_mono hP.buf fun b hb hb0 i hi => Or.inl (hb hb0 i hi)⟩
  change (x ∈ K.user ∧ Aligned x) ∨ x = core.num.U64.wrapping_add v vcpu.PENDING at hx
  rcases hx with ⟨hu, ha⟩ | rfl
  · exact hP.usr x hu ha
  · exact hP.pusr hv0

/-- An aligned VCPU word: `v` itself is aligned (its `PENDING` is), and `v + o` for an aligned `o`. -/
theorem vcpu_al {v o : U64} (hfit : v.val + 32768 ≤ 2 ^ 64)
    (hpa : Aligned (core.num.U64.wrapping_add v vcpu.PENDING)) (ho : o.val < 32768) (h8 : o.val % 8 = 0) :
    Aligned (core.num.U64.wrapping_add v o) := by
  have hP : vcpu.PENDING.val = 20520 := by simp [vcpu.PENDING]
  have e1 := vadd_val hfit (o := vcpu.PENDING) (by rw [hP]; omega)
  unfold Aligned at hpa ⊢
  rw [vadd_val hfit ho]
  rw [e1, hP] at hpa
  omega

/-- **`acc` of an accepted `local_vm_exit` with a pending exit** under `ownV` (module docstring). -/
theorem vexit_acc_own_p (hA : P0.ArchTotal ar) (hK : RegionOKV K) {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s) (hP : VexitPEnt K st T Cs H Sg Scs Z m v s)
    (hpd : VPend st v s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
      ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -, -, eok, -⟩ := vexit_split ar h
  obtain ⟨haff, -, hsct, hcore⟩ := current_vm_ok_true eok
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  have ht' : TcbAddr (L.curW s) := hI.1.choose_spec.choose_spec.tcbs _ hcT
  have hin := hE.vin hv0
  have hl := hE.vlk hv0
  have hfit := hP.vfit hv0
  have hpa : Aligned (core.num.U64.wrapping_add v vcpu.PENDING) := (hP.pusr hv0).out.1
  obtain ⟨hU, hpU, hbuf⟩ := hP.rep hv0
  have gV : VW (VexitRS K st lk s) v := fun o ho h8 =>
    ⟨vcpu_al hfit hpa ho h8, Or.inr (vcpu_rd hK hin.1 hfit ho hl)⟩
  refine vexit_accG_p (gS := guard st (VexitRS K st lk s) (VexitWS K st lk s)) (R := VexitRS K st lk s)
    (W := VexitWS K st lk s) (U := VPU K v) ar hA hI
    (fun hok w ha hw => ⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hok.aff hok.core hw)⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ => ⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩)
    (fun _ => ⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩)
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨q1, Or.inr q2⟩)
    hU hpU hbuf
    (fun x hx => by
      change (x ∈ K.user ∧ Aligned x) ∨ x = core.num.U64.wrapping_add v vcpu.PENDING at hx
      rcases hx with ⟨hu, ha⟩ | rfl
      · exact ⟨⟨ha, Or.inl hu⟩, ⟨ha, Or.inl hu⟩⟩
      · exact ⟨⟨hpa, Or.inr (pending_rd hK hin hl)⟩, ⟨hpa, Or.inr (pending_wr hK hin hl)⟩⟩)
    gV
    (fun f b e => by
      have hx := vcpu.vmcs_addr.off v f
      rw [e, WP.spec_ok] at hx
      obtain ⟨o, ho, h8, rfl⟩ := hx
      exact gV o (by omega) h8)
    (fun X _ _ => gst_write (W := VexitWS K st lk s)
      ⟨by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp),
        Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok (Or.inr (Or.inl ⟨3328#u64, by simp, by simp, by simp,
          stA_eq _⟩))))⟩)
    hpd h

/-- **`move` of an accepted `local_vm_exit` with a pending exit** under `ownV` (module docstring). -/
theorem vexit_move_p (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (Bool × S × A)} {p : SProg Bool}
    (hF : IsProg F p) (eF : ∀ mm : machine.Store S, F ar mm = fun s a => localvm.handle_vcpu_exit_local mm ar s a v n)
    {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s) (hP : VexitPEnt K st T Cs H Sg Scs Z m v s)
    (hpd : VPend st v s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem y))) ar s a v n = ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -⟩ := vexit_split ar h
  have hI := hE.inv
  have hL := hE.lay
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  have hin := hE.vin hv0
  have hpa : Aligned (core.num.U64.wrapping_add v vcpu.PENDING) := (hP.pusr hv0).out.1
  obtain ⟨hUs, hpU, hbuf⟩ := hP.rep hv0
  have heap : K.heap (L.curW s) = some .tcb := hK.base.tcbOf _ _ (hL.tcb _ hcT 3328#u64 (by simp) (by simp))
  have es : stA (L.curW s) = fld (L.curW s) oSTATE := by rw [stA_eq]; rfl
  have hg : localvm.handle_vcpu_exit_local (gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) ar s a v n =
      ok (true, s', a') :=
    vexit_accG_p (gS := gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (W := WAll (StWrOKV st K m (L.cpu s) (lk s))) (U := VPU K v) ar hA hI (fun _ _ _ _ => trivial)
      (fun _ w ha hw hn x _ => stepOKV_of_stepOK hK
        (stepOK_nondec hK.base hU.base ha (irq_wr_nondec hK.base hI hL hw hn)))
      (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) hUs hpU hbuf
      (fun x hx => by
        refine ⟨trivial, fun X w => ?_⟩
        change (x ∈ K.user ∧ Aligned x) ∨ x = core.num.U64.wrapping_add v vcpu.PENDING at hx
        rcases hx with ⟨hu, ha⟩ | rfl
        · exact stepOKV_of_stepOK hK (stepOK_nondec hK.base hU.base ha (fun hd => (decW_ok hU.base hd).2 hu))
        · exact stepOKV_of_stepOK hK (stepOK_nondec hK.base hU.base hpa (vcpu_nondec hK hin)))
      (fun _ _ _ => trivial) (fun _ _ _ => trivial)
      (fun X hX haffX => gd_write (by
        show StWrOKV st K m (L.cpu s) (lk s) X (stA (L.curW s)) sched.TS_RUNNING
        unfold StWrOKV
        rw [es]
        exact stepOKV_of_stepOK hK (stepOK_state hK.base hU.base heap haffX
          (by rw [hP.aff0]; exact hE.curAff)
          (fun hq => absurd hq (by rw [← es, hX]; simp [QueuedState, sched.TS_RUNNING_VM]))
          (fun hq => absurd hq (by simp [QueuedState, sched.TS_RUNNING])))))
      hpd h
  have eP : ∀ mm : machine.Store S, localvm.handle_vcpu_exit_local mm ar s a v n = interp mm ar p s a := by
    intro mm
    have e1 := congrFun (congrFun (eF mm) s) a
    have e2 := congrFun (congrFun (hF A ar mm) s) a
    try simp only at e1
    rw [← e1]
    exact e2
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOKV st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
      (lk s) (L.mem x) (L.mem y)) (I := fun _ => True)
    (fun x q w x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

variable {p : SProg Bool}

/-- **`local_vm_exit` is a local path under `ownV`, the pending-exit case included** (module docstring):
gen 6's `vexit_localPath` at `Pre = VexitEnt ∧ VexitPEnt`, `hP` / `hPm` by `vexit_acc_own_p` /
`vexit_move_p`. -/
noncomputable def vexit_localPathP (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vexitBody S v n) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ VexitPEnt K st T Cs H Sg Scs Z m v s)
      (VexitRS K st lk))
    (hEU : ∀ s b v', VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ VexitPEnt K st T Cs H Sg Scs Z m v s →
      b ∈ K.user → Aligned b →
      VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n (L.wr s b v') ∧
        VexitPEnt K st T Cs H Sg Scs Z m v (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vexit_localPath ar hA hK hU hp hz hm hro hEU hlk
    (fun _ _ _ _ hE hX hpd h => vexit_acc_own_p ar hA hK hE hX hpd h)
    (fun _ _ _ _ hE hX hpd h => vexit_move_p ar hA hK hU hp (fun _ => rfl) hE hX hpd h)

end

end Fl4Proofs.P2
