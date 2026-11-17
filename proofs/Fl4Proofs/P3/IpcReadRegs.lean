/-
P3 (DESIGN.md §9), TCB invocations: **ReadRegisters' steps** (the leaf
from `JAtZ` is IpcReadRegsJ's `readRegsXHypJ`; `readRegsXHyp_of` is retired): `tcb::read_registers` (the source's
suspend, then, called, the source's registers into the caller's message
words, the message info and `Running`) against l4v `invoke_tcb
ReadRegisters` and the reply tail (`specTail`).

The source's suspend on `IRel` (`suspend_irelY`), back at `XTopAt`; the
caller stays `Restart` (IpcStK's `st_suspend`). The badge, then the message
words at VSpace's `RInv` (the spec's `set_mrs` state after the badge, as
XTopReply's `replyStateB`): a register word by `regw_inv` (`rr_regw`), a
buffer word by `bufw_inv` (`rr_bufw`); the copy loops (`rr_loop0`,
`rr_loop1`, `rr_loopG`); then the message info and `Running`
(`rr_tail_inv`).
-/
import Fl4Proofs.P3.IpcCopyRegs
import Fl4Proofs.P3.IpcStK
import Fl4Proofs.P3.XTopReply
import Fl4Proofs.P3.XTopTcbData
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {th : TypedHeap} {P L4 L3 L2 L1 N T C E R : Set U64} {B : Set (U64 × Fl4Spec.Word)} {c : U64}

set_option maxHeartbeats 4000000 in
/-- **A message-register word** (`MR0`..`MR3`) of the caller keeps `RInv`. -/
theorem rr_regw {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) (x0 : Fl4Spec.Tcb)
    (buf : Option Fl4Spec.ObjRef) (s : S) (a : A) (ms : List Fl4Spec.Word)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (j : Nat) (hj : j = ms.length) (h4 : ms.length < 4) (v : U64) :
    Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G (L.wr s (regA ct (regIdx (mrIdx j))) v) a
      (MrS σ0 ct.bv x0 buf (ms ++ [v.bv])) := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  have hcurM : ct.bv = (MrS σ0 ct.bv x0 buf ms).curThread := by rw [MrS_cur]; exact hcur
  have hI1 := regw_inv s a _ hI ct htcb hcurM hkx (mrIdx j) v
  cases buf with
  | none =>
    have e := Endp.mrStateN_snoc_lt σ0 ct.bv x0 ms v.bv j hj h4
    simp only [MrS] at hI1 ⊢; rw [← e]; exact hI1
  | some p =>
    have e := Endp.mrState_snoc_lt σ0 ct.bv x0 p ms v.bv j hj h4
    simp only [MrS] at hI1 ⊢; rw [← e]; exact hI1

set_option maxHeartbeats 4000000 in
/-- **A message word in the caller's IPC buffer** (`MR4` on) keeps `RInv`. -/
theorem rr_bufw {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap ct.bv = some (.tcb x0))
    (p : Fl4Spec.ObjRef) (w : U64) (hbm : BufMap B w p) (s : S) (a : A) (ms : List Fl4Spec.Word)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 (some p) ms))
    (hBP : BufPlaced (L := L) N C B c s σ0) (k : U64) (hk : k.val = ms.length + 1) (h4 : 4 ≤ ms.length)
    (h120 : ms.length < 120) (v : U64) :
    Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G (L.wr s (fl4BufA w k) v) a
      (MrS σ0 ct.bv x0 (some p) (ms ++ [v.bv])) := by
  have hwB := hbm k (by omega)
  have hBP' : BufPlaced (L := L) N C B c s (MrS σ0 ct.bv x0 (some p) ms) := hBP.mono rfl (MrS_sc hk0 _ _)
  have hI1 := bufw_inv s a _ hI hBP' hwB v
  simp only [hk] at hI1
  simp only [MrS] at hI1 ⊢
  rw [← Endp.mrState_snoc_ge _ _ _ _ _ _ h4 h120]
  exact hI1

/-- The source's register words in an `RInv` state of the caller's reply. -/
theorem rr_src_reg {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} {σ0 : Fl4Spec.State Unit}
    {ct src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef} {s : S} {a : A}
    {ms : List Fl4Spec.Word} (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf ms))
    (r : Fl4Spec.Register) :
    (L.mem s (regA src (regIdx r))).bv = xs.tcbArch.tcbContext.userRegs r := by
  have hE := hI.2.2.2.2.1.1.2.1
  have hk : (MrS σ0 ct.bv x0 buf ms).kheap src.bv = some (.tcb xs) := by rw [MrS_kheap_ne _ _ _ _ _ hne]; exact hks
  exact (hE.at_tcb hsT hk).regs r

/-- The source's registers ReadRegisters replies with. -/
def rrOf (xs : Fl4Spec.Tcb) (n : U64) : List Fl4Spec.Word :=
  (wrRegs.take n.val).map fun r => xs.tcbArch.tcbContext.userRegs r

theorem rrOf_length (xs : Fl4Spec.Tcb) (n : U64) : (rrOf xs n).length = min n.val 20 := by
  rw [rrOf, List.length_map, List.length_take, wrRegs_length]

theorem rrOf_take_succ (xs : Fl4Spec.Tcb) (n : U64) (i : Nat) (hi : i < min n.val 20) :
    (rrOf xs n).take (i + 1) = (rrOf xs n).take i ++
      [xs.tcbArch.tcbContext.userRegs (wrRegs[i]'(by rw [wrRegs_length]; omega))] := by
  have hl : i < (rrOf xs n).length := by rw [rrOf_length]; exact hi
  have e : (rrOf xs n)[i]'hl = xs.tcbArch.tcbContext.userRegs (wrRegs[i]'(by rw [wrRegs_length]; omega)) := by
    simp only [rrOf, List.getElem_map, List.getElem_take]
  rw [List.take_succ, List.getElem?_eq_getElem hl, e]
  rfl

set_option maxHeartbeats 8000000 in
/-- **The frame registers into the caller's message registers** (`MR0`..`MR3`). -/
theorem rr_loop0 {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) (htcb : th ct = some .tcb) (hcur : ct.bv = σ0.curThread) (x0 : Fl4Spec.Tcb)
    (buf : Option Fl4Spec.ObjRef) {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) (s : S) (a : A)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 buf [])) :
    tcb.read_registers_loop0 st s src n ct 0#u64 ⦃ r => r.2.val = min n.val 4 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.1 a (MrS σ0 ct.bv x0 buf ((rrOf xs n).take r.2.val)) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.read_registers_loop0
  apply loop.spec_decr_nat (measure := fun x => 4 - x.2.val)
    (inv := fun x => x.2.val ≤ min n.val 4 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G x.1 a (MrS σ0 ct.bv x0 buf ((rrOf xs n).take x.2.val)) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s)
  · rintro ⟨s', i⟩ ⟨hi, hI', hk', hc'⟩
    unfold tcb.read_registers_loop0.body
    simp only at hi hI' hk' hc' ⊢
    by_cases h1 : i < n
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 4 := by have := (P1.gt_iff_val).not.1 h1; omega
      exact ⟨this, hI', hk', hc'⟩
    rw [if_pos h1]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    have h2 : i < tcb.N_FRAME := (P1.gt_iff_val).2 (by rw [hf]; omega)
    rw [if_pos h2]
    by_cases h3 : i < msg.N_MSG_REGISTERS
    swap
    · rw [if_neg h3, WP.spec_ok]
      have : i.val = min n.val 4 := by have := (P1.gt_iff_val).not.1 h3; rw [hN] at this; omega
      exact ⟨this, hI', hk', hc'⟩
    rw [if_pos h3]
    have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h3; rwa [hN] at this
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[i.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq frame_regs_val, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega), wrRegs, List.getElem_append_left (show i.val < Fl4Spec.frameRegisters.length by omega)]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r3 rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s' ct _ _) ?_
    rintro s2 rfl
    obtain ⟨i4, h4e, h4v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hi4' : i4.val = i.val + 1 := by simpa using h4v
    have hlen : ((rrOf xs n).take i.val).length = i.val := by simp [List.length_take, rrOf_length]; omega
    have hI2 := rr_regw σ0 ct htcb hcur x0 buf s' a _ hI' i.val hlen.symm (by omega)
      (L.mem s' (regA src (regIdx (wrRegs[i.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks hI', ← rrOf_take_succ xs n i.val (by omega)] at hI2
    refine ⟨⟨by show i4.val ≤ min n.val 4; omega, by rw [hi4']; exact hI2,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc'⟩,
      by show 4 - i4.val < 4 - i.val; omega⟩
  · exact ⟨by simp, by simpa using hI, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **The frame registers past `MR3` into the caller's IPC buffer.** -/
theorem rr_loop1 {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap ct.bv = some (.tcb x0)) (pb : Fl4Spec.ObjRef) (w : U64)
    (hbm : BufMap B w pb) {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) (s : S) (a : A) (i0 : U64)
    (hi0 : 4 ≤ i0.val) (hi0n : i0.val ≤ min n.val 18)
    (hBP : BufPlaced (L := L) N C B c s σ0)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take i0.val))) :
    tcb.read_registers_loop1 st s src n w i0 ⦃ r => r.2.val = min n.val 18 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.1 a
        (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take r.2.val)) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  unfold tcb.read_registers_loop1
  apply loop.spec_decr_nat (measure := fun x => 18 - x.2.val)
    (inv := fun x => 4 ≤ x.2.val ∧ x.2.val ≤ min n.val 18 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G x.1 a
        (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take x.2.val)) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s)
  · rintro ⟨s', i⟩ ⟨hi4, hi, hI', hk', hc'⟩
    unfold tcb.read_registers_loop1.body
    simp only at hi4 hi hI' hk' hc' ⊢
    by_cases h1 : i < n
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h1; omega
      exact ⟨this, hI', hk', hc'⟩
    rw [if_pos h1]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h1
    by_cases h2 : i < tcb.N_FRAME
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : i.val = min n.val 18 := by have := (P1.gt_iff_val).not.1 h2; rw [hf] at this; omega
      exact ⟨this, hI', hk', hc'⟩
    rw [if_pos h2]
    have hi18 : i.val < 18 := by have := (P1.gt_iff_val).1 h2; rwa [hf] at this
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' i (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[i.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq frame_regs_val, List.getElem_map]
      congr 1
      simp [cast_to_us' i (by omega), wrRegs, List.getElem_append_left (show i.val < Fl4Spec.frameRegisters.length by omega)]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h3e, bind_ok]
    have hi3 : i3.val = i.val + 1 := by simpa using h3v
    refine WP.spec_bind (Endp.msg.buf_set.spec s' w i3 _) ?_
    rintro s2 rfl
    rw [WP.spec_ok]
    have hlen : ((rrOf xs n).take i.val).length = i.val := by simp [List.length_take, rrOf_length]; omega
    have hBP' : BufPlaced (L := L) N C B c s' σ0 := hBP.mono hk' (fun _ _ _ h => h)
    have hI2 := rr_bufw σ0 ct hk0 pb w hbm s' a _ hI' hBP' i3 (by rw [hlen]; exact hi3) (by omega) (by omega)
      (L.mem s' (regA src (regIdx (wrRegs[i.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks hI', ← rrOf_take_succ xs n i.val (by omega)] at hI2
    refine ⟨⟨by show 4 ≤ i3.val; omega, by show i3.val ≤ min n.val 18; omega, by rw [hi3]; exact hI2,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc'⟩,
      by show 18 - i3.val < 18 - i.val; omega⟩
  · exact ⟨hi0, hi0n, hI, rfl, rfl⟩

set_option maxHeartbeats 8000000 in
/-- **The integer registers into the caller's IPC buffer** (`read_registers`'
loops 3, 5, 7, 9). -/
theorem rr_loopGB {A : Type} {AR : A → Fl4Spec.Cr3 → Prop} {G : MdbGhost} (σ0 : Fl4Spec.State Unit)
    (ct : U64) {x0 : Fl4Spec.Tcb} (hk0 : σ0.kheap ct.bv = some (.tcb x0)) (pb : Fl4Spec.ObjRef) (w : U64)
    (hbm : BufMap B w pb) {src : U64} (hne : src.bv ≠ ct.bv) (hsT : src ∈ T) {xs : Fl4Spec.Tcb}
    (hks : σ0.kheap src.bv = some (.tcb xs)) (n : U64) (s : S) (a : A) (hn : 18 < n.val)
    (hBP : BufPlaced (L := L) N C B c s σ0)
    (hI : Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G s a (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take 18)))
    (body : S → U64 → Result (ControlFlow (S × U64) (S × U64)))
    (hbody : ∀ s k, body s k = if k < tcb.N_GP then (do
        let i ← k + tcb.N_FRAME
        if i < n then do
          let i1 ← lift (UScalar.cast .Usize k)
          let i2 ← Aeneas.Std.Array.index_usize regs.GP_REGISTERS i1
          let v ← obj.Tcb.reg st src s i2
          let i3 ← i + 1#u64
          let s1 ← msg.buf_set st s w i3 v
          let k1 ← k + 1#u64
          ok (ControlFlow.cont (s1, k1))
        else ok (ControlFlow.done (s, k)))
      else ok (ControlFlow.done (s, k))) :
    loop (fun (x : S × U64) => body x.1 x.2) (s, 0#u64) ⦃ r => 18 + r.2.val = min n.val 20 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G r.1 a
        (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take (18 + r.2.val))) ∧
      L.ksb r.1 = L.ksb s ∧ L.cpu r.1 = L.cpu s ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  have hfl : Fl4Spec.frameRegisters.length = 18 := rfl
  have hwl : wrRegs.length = 20 := rfl
  apply loop.spec_decr_nat (measure := fun x => 2 - x.2.val)
    (inv := fun x => 18 + x.2.val ≤ min n.val 20 ∧
      Vs.RInv (L := L) th P L4 L3 L2 L1 N T C E R B c AR G x.1 a
        (MrS σ0 ct.bv x0 (some pb) ((rrOf xs n).take (18 + x.2.val))) ∧
      L.ksb x.1 = L.ksb s ∧ L.cpu x.1 = L.cpu s)
  · rintro ⟨s', k⟩ ⟨hk, hI', hk', hc'⟩
    simp only at hk hI' hk' hc' ⊢
    rw [hbody]
    by_cases h1 : k < tcb.N_GP
    swap
    · rw [if_neg h1, WP.spec_ok]
      have : 18 + k.val = min n.val 20 := by have := (P1.gt_iff_val).not.1 h1; rw [hg] at this; omega
      exact ⟨this, hI', hk', hc'⟩
    rw [if_pos h1]
    have hk2 : k.val < 2 := by have := (P1.gt_iff_val).1 h1; rwa [hg] at this
    obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := k) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
    rw [hie, bind_ok]
    have hiv' : i.val = k.val + 18 := by rw [← hf]; simpa using hiv
    by_cases h2 : i < n
    swap
    · rw [if_neg h2, WP.spec_ok]
      have : 18 + k.val = min n.val 20 := by have := (P1.gt_iff_val).not.1 h2; omega
      exact ⟨this, hI', hk', hc'⟩
    rw [if_pos h2]
    have hin : i.val < n.val := (P1.gt_iff_val).1 h2
    simp only [lift, bind_ok]
    refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ _ (by rw [cast_to_us' k (by omega)]; simp; omega)) ?_
    rintro rr hrr
    have hrv : rr = regIdx (wrRegs[18 + k.val]'(by omega)) := by
      rw [hrr, List.getElem_of_eq gp_regs_val, List.getElem_map]
      congr 1
      simp only [wrRegs, cast_to_us' k (by omega)]
      rw [List.getElem_append_right (by rw [hfl]; omega)]
      simp [hfl]
    subst hrv
    refine WP.spec_bind (Endp.obj.Tcb.reg.spec s' src _) ?_
    rintro v rfl
    obtain ⟨i3, h3e, h3v⟩ := spec_exists (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h3e, bind_ok]
    have hi3 : i3.val = i.val + 1 := by simpa using h3v
    refine WP.spec_bind (Endp.msg.buf_set.spec s' w i3 _) ?_
    rintro s2 rfl
    obtain ⟨k1, h4e, h4v⟩ := spec_exists (U64.add_spec (x := k) (y := 1#u64) (by scalar_tac))
    rw [h4e, bind_ok, WP.spec_ok]
    have hk1 : k1.val = k.val + 1 := by simpa using h4v
    have hlen : ((rrOf xs n).take (18 + k.val)).length = 18 + k.val := by
      simp [List.length_take, rrOf_length]; omega
    have hBP' : BufPlaced (L := L) N C B c s' σ0 := hBP.mono hk' (fun _ _ _ h => h)
    have hI2 := rr_bufw σ0 ct hk0 pb w hbm s' a _ hI' hBP' i3 (by rw [hlen]; omega) (by omega) (by omega)
      (L.mem s' (regA src (regIdx (wrRegs[18 + k.val]'(by omega)))))
    rw [rr_src_reg hne hsT hks hI', ← rrOf_take_succ xs n (18 + k.val) (by omega)] at hI2
    refine ⟨⟨by show 18 + k1.val ≤ min n.val 20; omega, by rw [hk1, ← Nat.add_assoc]; exact hI2,
      by show L.ksb (L.wr s' _ _) = L.ksb s; rw [L.ksb_wr]; exact hk',
      by show L.cpu (L.wr s' _ _) = L.cpu s; rw [L.cpu_wr]; exact hc'⟩,
      by show 2 - k1.val < 2 - k.val; omega⟩
  · exact ⟨by simp; omega, by simpa using hI, rfl, rfl⟩

/-- **The integer registers into message registers**: none (the integer
registers are words 18 and 19, past `MR3`; loops 2, 4, 6, 8). -/
theorem rr_loopGR (n : U64) (s : S)
    (body : S → U64 → Result (ControlFlow (S × U64) (S × U64)))
    (hbody : ∀ s k, body s k = if k < tcb.N_GP then (do
        let i ← k + tcb.N_FRAME
        if i < n then
          if i < msg.N_MSG_REGISTERS then do
            let i1 ← lift (UScalar.cast .Usize k)
            let i2 ← Aeneas.Std.Array.index_usize regs.GP_REGISTERS i1
            let v ← obj.Tcb.reg st src s i2
            let i3 ← msg.msg_register i
            let s1 ← obj.Tcb.set_reg st ct s i3 v
            let k1 ← k + 1#u64
            ok (ControlFlow.cont (s1, k1))
          else ok (ControlFlow.done (s, k))
        else ok (ControlFlow.done (s, k)))
      else ok (ControlFlow.done (s, k))) :
    loop (fun (x : S × U64) => body x.1 x.2) (s, 0#u64) ⦃ r => r = (s, 0#u64) ⦄ := by
  have hf : tcb.N_FRAME.val = 18 := by unfold tcb.N_FRAME; rfl
  have hg : tcb.N_GP.val = 2 := by unfold tcb.N_GP; rfl
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  apply loop.spec_decr_nat (measure := fun _ => 0) (inv := fun x => x = (s, 0#u64))
  · rintro x rfl
    simp only
    rw [hbody]
    have h1 : (0#u64 : U64) < tcb.N_GP := (P1.gt_iff_val).2 (by rw [hg]; decide)
    rw [if_pos h1]
    obtain ⟨i, hie, hiv⟩ := spec_exists (U64.add_spec (x := 0#u64) (y := tcb.N_FRAME) (by rw [hf]; scalar_tac))
    rw [hie, bind_ok]
    have hiv' : i.val = 18 := by rw [← hf]; simpa using hiv
    have h3 : ¬ i < msg.N_MSG_REGISTERS := fun h => by have := (P1.gt_iff_val).1 h; rw [hN] at this; omega
    split <;> (try rw [if_neg h3]) <;> rw [WP.spec_ok]
  · rfl

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 8000000 in
/-- **The message info and `Running` after the message words**, at `XTop`
against `specTail true` (the badge written first, as `replyStateB`). -/
theorem rr_tail_xtop {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s1 : S} {a1 : A} {σy : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s1 a1 σy) {ct : U64} (hcur : ct.bv = σy.curThread) {x : Fl4Spec.Tcb}
    (hk : σy.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .restart)
    (hact : OutsideObjects Z.th (L.nodeAt s1 (L.cpu s1) layout.node.SCHED_ACTION))
    {s2 : S} {G' : MdbGhost} {ms : List Fl4Spec.Word}
    (hI : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR G' s2 a1
      (MrS (Notif.updK σy ct.bv (.tcb (Notif.setReg x Fl4Spec.badge_register 0))) ct.bv
        (Notif.setReg x Fl4Spec.badge_register 0) (Endp.ipcBufOf true x) ms))
    (hks : L.ksb s2 = L.ksb s1) (hcpu : L.cpu s2 = L.cpu s1) (hlen : ms.length ≤ Fl4Spec.msgMaxLength)
    (hfr : ∀ p, Endp.ipcBufOf true x = some p → ∀ z ∈ Endp.mrPairs ms,
      (Endp.bufAddr p z.1).toNat % 8 = 0 ∧ Fl4Spec.inUserFrame (Endp.bufAddr p z.1) σy)
    (n : U64) (hn : n.val = mrLen (Endp.ipcBufOf true x) ms.length) (hn128 : n.val < 128) :
    (do
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      let s6 ← msg.set_msg_info st s2 ct mi
      let s7 ← sched.set_thread_state st s6 ct sched.TS_RUNNING
      ok (s7, a1)) ⦃ res =>
      L.mem res.1 (stA ct) ≠ sched.TS_RESTART ∧
      ∃ z ∈ (specTail true ct.bv ms σy).1, RelTopM (L := L) res.1 z.2 ∧ XTop (L := L) AR res.1 res.2 z.2 ⦄ := by
  have htcb := (hX.curTcb hcur.symm).1
  set xA := Notif.setReg x Fl4Spec.badge_register 0 with hxA
  have hcurA : ct.bv = (Notif.updK σy ct.bv (.tcb xA)).curThread := hcur
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_bind (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s3 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have hkA := MrS_kheap_t (Notif.updK σy ct.bv (.tcb xA)) ct.bv xA (Endp.ipcBufOf true x) ms
  have hI2 := regw_inv _ a1 _ hI ct htcb (by rw [MrS_cur]; exact hcurA) hkA Fl4Spec.msg_info_register v
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen (Endp.ipcBufOf true x) ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  have hI3 : Vs.RInv (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.N Z.T Z.C Z.E Z.R Z.B Z.c AR G'
      (L.wr s2 (regA ct (regIdx Fl4Spec.msg_info_register)) v) a1 (replyStateB σy ct.bv x (Endp.ipcBufOf true x) ms) := by
    unfold replyStateB; rw [← hvd]; exact hI2
  have hks3 : L.ksb (L.wr s2 (regA ct (regIdx Fl4Spec.msg_info_register)) v) = L.ksb s1 := by rw [L.ksb_wr]; exact hks
  have hcp3 : L.cpu (L.wr s2 (regA ct (regIdx Fl4Spec.msg_info_register)) v) = L.cpu s1 := by rw [L.cpu_wr]; exact hcpu
  have hact3 : OutsideObjects Z.th (L.nodeAt (L.wr s2 (regA ct (regIdx Fl4Spec.msg_info_register)) v)
      (L.cpu (L.wr s2 (regA ct (regIdx Fl4Spec.msg_info_register)) v)) layout.node.SCHED_ACTION) := by
    rw [hcp3, Sched.nodeAt_ksb hks3]; exact hact
  have hcode : sched.TS_RUNNING.val = Notif.tsCode .running := by unfold sched.TS_RUNNING; rfl
  refine WP.spec_bind (WP.spec_and (sts_inv _ a1 _ hI3 ct htcb (by rw [replyStateB_cur]; exact hcur)
    (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs]; rfl) hact3 .running (by decide) _ hcode)
    (set_thread_state_cases _ ct sched.TS_RUNNING)) ?_
  rintro s5 ⟨⟨hI5, hst5, -⟩, hcs⟩
  have hk5 : L.ksb s5 = L.ksb s1 := by rcases hcs with rfl | rfl <;> simp [L.ksb_wr, hks]
  rw [WP.spec_ok]
  refine ⟨by rw [hst5]; exact run_ne_rst, _, by rw [specTail_data hk hrs ms hlen hfr]; exact Set.mem_singleton _,
    hI5.relTop, ?_⟩
  have hz : Sched.SzKeep σy (Notif.stsAct (Notif.updK (replyState σy ct.bv x ms) ct.bv
      (.tcb { replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running })) ct.bv) := by
    refine szKeep_tcbOnly (t := ct.bv) (fun q hq => ?_)
      ⟨{ replyTcbB x (Endp.ipcBufOf true x) ms with tcbState := .running }, by rw [Notif.stsAct_kheap]; simp [Notif.updK]⟩
    rw [Notif.stsAct_kheap, Notif.updK_kheap, Function.update_of_ne hq, replyStateB_kheap_ne _ _ _ _ _ hq]
  exact ⟨_, hX.ofRInv hI5 hk5 hz⟩

section SpecRR
open Fl4Spec

theorem mapM_getRegister (uc : UserContext) : ∀ rs : List Register,
    NonDet.mapM getRegister rs uc = ({(rs.map uc.userRegs, uc)}, False)
  | [] => rfl
  | r :: rs => by
    show (NonDet.bind (getRegister r) fun b => NonDet.bind (NonDet.mapM getRegister rs) fun bs =>
      NonDet.pure (b :: bs)) uc = _
    rw [show (NonDet.bind (getRegister r) fun b => NonDet.bind (NonDet.mapM getRegister rs) fun bs =>
      NonDet.pure (b :: bs)) = (getRegister r >>= fun b => NonDet.mapM getRegister rs >>= fun bs =>
        pure (b :: bs)) from rfl]
    rw [nd_bind_one (show getRegister r uc = ({(uc.userRegs r, uc)}, False) from rfl), nd_bind_one (mapM_getRegister uc rs)]
    rfl

theorem asUser_mapM_get {σ : State Unit} {t : ObjRef} {x : Tcb} (hk : σ.kheap t = some (.tcb x))
    (rs : List Register) :
    asUser (Z := Unit) t (NonDet.mapM getRegister rs) σ = ({(rs.map x.tcbArch.tcbContext.userRegs, σ)}, False) := by
  rw [asUser_det hk (mapM_getRegister _ rs)]
  have e : ({ x with tcbArch := archTcbContextSet (archTcbContextGet x.tcbArch) x.tcbArch } : Tcb) = x := by
    cases x; rfl
  rw [e, Endp.updK_self hk]
  rfl

/-- The spec's `set_thread_state` with one outcome: the TCB was there. -/
theorem sts_tcb {σ σ1 : State Unit} {t : ObjRef} {ts : ThreadState}
    (h : setThreadState (Z := Unit) t ts σ = ({((), σ1)}, False)) :
    ∃ x0, σ.kheap t = some (.tcb x0) ∧ σ1 = Notif.stsAct (Notif.updK σ t (.tcb { x0 with tcbState := ts })) t := by
  cases hk : σ.kheap t with
  | none =>
    have hm : ((), σ1) ∈ (setThreadState (Z := Unit) t ts σ).1 := by rw [h]; rfl
    obtain ⟨y, hy, -⟩ := hm
    obtain ⟨z, hz, -⟩ := hy
    unfold NonDet.getsThe getTcb readObject at hz
    rw [hk] at hz; exact hz.elim
  | some k =>
    cases k with
    | tcb x0 =>
      refine ⟨x0, rfl, ?_⟩
      rw [Notif.setThreadState_eq ts hk] at h
      exact ((Prod.mk.inj (Set.singleton_eq_singleton_iff.1 (congrArg Prod.fst h))).2).symm
    | _ =>
      have hm : ((), σ1) ∈ (setThreadState (Z := Unit) t ts σ).1 := by rw [h]; rfl
      obtain ⟨y, hy, -⟩ := hm
      obtain ⟨z, hz, -⟩ := hy
      unfold NonDet.getsThe getTcb readObject at hz
      rw [hk] at hz; exact hz.elim

end SpecRR

end

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

end

end Fl4Proofs.P3
