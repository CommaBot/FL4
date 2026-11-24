/-
P1: the VCPU objects' steps.  A VCPU is a heap object of kind `.other 15`
(`newKind`), so its words are untracked object words (`CapW`, in `Ω` off
the frame words: `vcpu_obj_capw`); the TCBs' VCPU word (offset 3664) is a
field no invariant reads (`plainW_all`).  The steps keep `Cur0`: a VCPU
word write (`vcpu.set.cur0`, `vcpu.write_vmcs.cur0`), a TCB's VCPU word,
the stall, a thread's VCPU report and `detach`.  P3's facts are one
structure, `VcpuPlace`.
-/
import Fl4Proofs.P1.QueueVcpuLink
import Fl4Proofs.P1.QueueDecTcbRR
import Fl4Proofs.P1.VcpuReport
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {P3Ok : S → Prop}
variable {H : Heap} {Cs Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- A word of a VCPU heap object is aligned. -/
theorem vcpu_obj_aligned (hH : HeapOK H) {v o : U64} (hv : H v = some (.other 15)) (ho : o.val < 2 ^ 15)
    (h8 : o.val % 8 = 0) : Aligned (core.num.U64.wrapping_add v o) := by
  have hal := hH.align v _ hv
  have hfit := hH.fits v _ hv
  rw [show (HKind.other 15).bits = 15 from rfl] at hal hfit
  have hb : (core.num.U64.wrapping_add v o).val = v.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  unfold Aligned; rw [hb]; omega

/-- **A VCPU word write keeps `Cur0`.** -/
theorem Cur0.vword (hH : HeapOK H) {s0 s : S} {v o x : U64} (hv : H v = some (.other 15)) (ho : o.val < 2 ^ 15)
    (h8 : o.val % 8 = 0) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 (L.wr s (core.num.U64.wrapping_add v o) x) :=
  h.capw (writesIn_wr (vcpu_obj_aligned hH hv ho h8)) fun b e => e ▸ vcpu_obj_capw hH hv ho h8

theorem vcpu.set.cur0 (hH : HeapOK H) {s0 s : S} {v o x : U64} (hv : H v = some (.other 15))
    (ho : o.val < 2 ^ 15) (h8 : o.val % 8 = 0) (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) :
    vcpu.set st s v o x ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold vcpu.set
  simp only [lift, bind_ok]
  exact WP.spec_mono (LawfulStore.write_spec s _ x) fun s' e => e ▸ h.vword hH hv ho h8

/-- `wrapping_add` reassociates when the offsets do not wrap. -/
theorem wadd_assoc (v a b : U64) (h : a.val + b.val < 2 ^ 64) :
    core.num.U64.wrapping_add (core.num.U64.wrapping_add v a) b =
      core.num.U64.wrapping_add v (core.num.U64.wrapping_add a b) := by
  apply UScalar.eq_of_val_eq
  have ha : (core.num.U64.wrapping_add a b).val = a.val + b.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  simp only [core.num.U64.wrapping_add_val_eq, ha]
  rw [Nat.mod_add_mod, Nat.add_assoc]


theorem vcpu.vmcs_addr.off (v f : U64) :
    vcpu.vmcs_addr v f ⦃ a => ∃ o : U64, o.val < 20480 ∧ o.val % 8 = 0 ∧ a = core.num.U64.wrapping_add v o ⦄ := by
  unfold vcpu.vmcs_addr
  simp only [lift, bind_ok]
  step as ⟨i1, hi1⟩
  step as ⟨i2, hi2⟩
  step as ⟨i4, hi4⟩
  step as ⟨i6, hi6⟩
  step as ⟨i8, hi8⟩
  have b0 : (f &&& 255#u64).val < 256 := by
    simp only [UScalar.val_and]; exact lt_of_le_of_lt (Nat.and_le_right) (by simp)
  have b1 : i1.val < 128 := by
    have : i1.val = (f &&& 255#u64).val >>> 1 := by simpa using hi1
    rw [this, Nat.shiftRight_eq_div_pow]; omega
  have b3 : (i2 &&& 3#u64).val < 4 := by
    simp only [UScalar.val_and]; exact lt_of_le_of_lt (Nat.and_le_right) (by simp)
  have b4 : i4.val < 512 := by
    have hx : i2.val &&& 3 < 4 := lt_of_le_of_lt Nat.and_le_right (by decide)
    have : i4.val ≤ (i2.val &&& 3) <<< 7 := by
      simp only [UScalar.val_and] at hi4; rw [hi4]; exact Nat.mod_le _ _
    rw [Nat.shiftLeft_eq] at this; omega
  have b7 : (i6 &&& 3#u64).val < 4 := by
    simp only [UScalar.val_and]; exact lt_of_le_of_lt (Nat.and_le_right) (by simp)
  have b8 : i8.val < 2048 := by
    have hx : i6.val &&& 3 < 4 := lt_of_le_of_lt Nat.and_le_right (by decide)
    have : i8.val ≤ (i6.val &&& 3) <<< 9 := by
      simp only [UScalar.val_and] at hi8; rw [hi8]; exact Nat.mod_le _ _
    rw [Nat.shiftLeft_eq] at this; omega
  have b5 : (i1 ||| i4).val < 512 := by
    simp only [UScalar.val_or]; exact Nat.or_lt_two_pow (n := 9) (by omega) (by omega)
  have b9 : ((i1 ||| i4) ||| i8).val < 2048 := by
    simp only [UScalar.val_or]; exact Nat.or_lt_two_pow (n := 11) (by simp only [UScalar.val_or] at b5; omega)
      (by omega)
  step as ⟨i11, hi11⟩
  refine ⟨core.num.U64.wrapping_add vcpu.SHADOW i11, ?_, ?_, ?_⟩
  · simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vcpu.SHADOW]; omega
  · simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vcpu.SHADOW]; omega
  · exact wadd_assoc v _ _ (by simp [vcpu.SHADOW]; omega)

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}
variable {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- `XS` with the `Cur0W` frame from `s0` (for a `Cur0` state's reply). -/
def XSV (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s0 s : S) : Prop :=
  XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s ∧ WritesIn st s0 s (Cur0W st T Cs Ω H Sg Scs Z s0)

theorem XSV.start {s : S} {X : Set U64} (h : XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s) :
    XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s s := ⟨h, WritesIn.refl _ _⟩

theorem XSV.foot {s0 s s' : S} {X : Set U64} (h : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hw : WritesIn st s s' (XferFoot T U)) : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' :=
  ⟨h.1.foot hw, Cur0W.trans h.2 (hw.mono fun _ hb => XferFoot.cur0w h.1.1.2.2.2.2.2 hb)⟩

theorem XSV.capw {s0 s s' : S} {X : Set U64} {B : U64 → Prop} (h : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b) : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' :=
  ⟨h.1.capw hw hB, Cur0W.trans h.2 (hw.mono fun b hb => Or.inr (Or.inr (Or.inl (hB b hb))))⟩

theorem XSV.bxi {s0 s : S} (h : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac ∅ Q R s0 s) :
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s := h.1.bxi

theorem obj.Tcb.set_reg.xsv {s0 s : S} {y r v : U64} (h : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s) (hy : y ∈ T)
    (hr : r.val < 384) :
    obj.Tcb.set_reg st y s r v ⦃ s' => XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  have hT := h.1.1.1.tcbs
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s y r v (hT y hy) hr) fun s' ⟨K, hK, e⟩ => ?_
  subst e
  exact XSV.foot h ((writesIn_wr (field_aligned (hT y hy) (by omega) (by omega))).mono fun b e =>
    Or.inl ⟨y, hy, K, by omega, by omega, e⟩)

theorem msg.buf_set.xsv {s0 s : S} {buf i v : U64} (h : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hb : BufOK U buf) (h0 : buf ≠ 0#u64) (hi : i.val < 128) :
    msg.buf_set st s buf i v ⦃ s' => XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s' ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact XSV.foot h ((writesIn_wr (h.1.1.2.2.2.2.2 _ hu).1.1).mono fun b e => Or.inr (e ▸ hu))

theorem msg.set_mr.xsv {s0 s : S} {y buf i v : U64} (h : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0 r.2 ∧ r.1.val ≤ i.val + 4 ⦄ := by
  unfold msg.set_mr
  split
  · have hreg : ∀ j, msg.msg_register j ⦃ r => r.val < 384 ⦄ := fun j => by
      unfold msg.msg_register
      split; · simp [layout.reg.R10]
      split; · simp [layout.reg.R8]
      split; · simp [layout.reg.R9]
      simp [layout.reg.R15]
    refine WP.spec_bind (hreg i) fun r hr => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xsv (v := v) h hy hr) fun s1 h1 => ?_
    try simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 ⟨h1, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (msg.buf_set.xsv (v := v) h hb h0 hi1) fun s1 h1 => ?_
      refine (WP.spec_ok _).2 ⟨h1, ?_⟩
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · exact (WP.spec_ok _).2 ⟨h, by simp [msg.N_MSG_REGISTERS]⟩

/-- `Cur0` from an `XS` stretch started at a `Cur0` state. -/
theorem Cur0.ofXS {s0 s s' : S} {Ac' : Set U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (x : XSV st T Cs Ω H Sg Rp Scs Nt Z U Ac' ∅ Q R s s') : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' := by
  have hct : L.curW s ∈ T := h.2.choose_spec.1.1.choose_spec.choose_spec.curT
  obtain ⟨ea, ec, -, ecs, f, -, -⟩ := x.1.fr
  refine Cur0.mk h x.bxi ec ecs (Or.inl ?_) (Or.inl ea) (Or.inl ?_) x.2
  · rw [scA_eq]; exact f _ hct _ (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact f _ hct _ (by simp) (by simp) (by simp)

/-- **A thread not blocked set running keeps `Cur0`.** -/
theorem sched.set_thread_state.running_cur0 {s0 s : S} {t : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s)
    (ht : t ∈ T) (hr : ¬ BlockedR (L.mem s (stA t))) :
    sched.set_thread_state st s t sched.TS_RUNNING ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ∧
      L.ksb s' = L.ksb s ⦄ := by
  have h' := h
  obtain ⟨-, Ac', ⟨⟨Q, R, h0⟩, hB, hX, hSg, hS⟩, -, -, -, -, -⟩ := h'
  have hnb : ¬ Blocked (L.mem s (stA t)) := fun h => hr (Or.inl h)
  have hnr : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := fun h => hr (Or.inr h)
  have hnv : L.mem s (stA t) ≠ sched.TS_BLOCKED_ON_RECV := fun h => hnb (Or.inr (Or.inl h))
  have hnoref : ∀ r ∈ Rp, L.mem s (rTcbA r) ≠ t := hX.noref (h0.tcbs t ht) hnr hnv
  have hct : L.curW s ∈ T := h0.curT
  refine WP.spec_mono (WP.spec_and (sts_all s t _ Q R h0 hB hX hS hSg ht not_blocked_running running_ne
    (Or.inr hnb) hnoref
    ⟨fun _ _ _ _ _ => runnable_running, fun _ _ _ => runnable_running, fun _ => runnable_running⟩)
    (sched.set_thread_state.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := ∅) s t _ h0 ht)) ?_
  rintro s' ⟨⟨h1, hB1, hX1, hS1, hSg1, est, k⟩, f1⟩
  refine ⟨Cur0.mk h ⟨⟨Q, R, h1.congrX empty_congr⟩, hB1, hX1, hSg1, hS1⟩ k.curW k.cscW (Or.inl (k.scf hct)) k.act ?_
    (Foot.cur0w f1 (Set.empty_subset _)), k.ksb⟩
  by_cases e : t = L.curW s
  · subst e; rw [est]; exact Or.inr (nbr_runnable runnable_running)
  · left; rw [stA_eq]
    exact k.fld _ hct _ (by simp) (by simp) (by simp) (by simp) (fun e' => absurd e'.symm e)

/-- **A TCB's VCPU word write keeps `Cur0`** (a field no invariant reads). -/
theorem Cur0.tvcpu {s0 s : S} {t v : U64} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (ht : t ∈ T) :
    Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 (L.wr s (core.num.U64.wrapping_add t 3664#u64) v) := by
  have h' := h
  obtain ⟨-, Ac', hX, -, -, -, -, -⟩ := h'
  have hb := hX.blk
  have hT := hX.1.choose_spec.choose_spec.tcbs
  have hct : L.curW s ∈ T := hX.1.choose_spec.choose_spec.curT
  have hN := hX.1.choose_spec.choose_spec.nodes _ hX.1.choose_spec.choose_spec.cur
  obtain ⟨b, f, ani⟩ := plainW_all (K := 3664#u64) (v := v) hb ht (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
  have al := field_aligned (hT t ht) (K := 3664#u64) (by simp) (by simp)
  have k1 : (3664#u64 : U64).val < 4096 := by simp
  have n1 : core.num.U64.wrapping_add t 3664#u64 ≠ core.num.U64.wrapping_add (L.curW s) 3464#u64 :=
    field_ne (hT t ht) (hT _ hct) k1 (by simp) (fun _ => by simp)
  have n2 : core.num.U64.wrapping_add t 3664#u64 ≠ core.num.U64.wrapping_add (L.curW s) 3328#u64 :=
    field_ne (hT t ht) (hT _ hct) k1 (by simp) (fun _ => by simp)
  have n3 : L.nodeAt s (L.cpu s) layout.node.CUR_SC ≠ core.num.U64.wrapping_add t 3664#u64 :=
    node_ne_field hN (by simp [layout.node.CUR_SC]) ht (hT t ht) k1
  refine Cur0.step h b ani.2.2 ?_ (Or.inl ?_) (Or.inl ani.1) (fun hn => ?_)
    (WritesIn.mono (writesIn_wr al) fun _ hb => Or.inl (hb ▸ kw_field (Es := EH H) ht (by simp) (by simp) (by simp)))
  · simp only [LawfulStore.cscW, LawfulStore.nodeA, L.cpu_wr, nodeAt_of_ksb (L.ksb_wr s _ v)]
    exact L.mem_wr_ne al (nodeAt_aligned hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
      (fun e => n3 (UScalar.eq_of_val_eq e).symm)
  · rw [scA_eq]
    exact L.mem_wr_ne al (field_aligned (hT _ hct) (by simp) (by simp)) (fun e => n1 (UScalar.eq_of_val_eq e))
  · rw [stA_eq, L.mem_wr_ne al (field_aligned (hT _ hct) (by simp) (by simp)) (fun e => n2 (UScalar.eq_of_val_eq e)),
      ← stA_eq]
    exact hn

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}
variable {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem vcpu.get.any (s : S) (v o : U64) : vcpu.get st s v o ⦃ _ => True ⦄ := by
  unfold vcpu.get; simp only [lift, bind_ok]
  exact WP.spec_mono (LawfulStore.read_spec s _) fun _ _ => trivial

theorem vcpu.read_vmcs.any (s : S) (v f : U64) : vcpu.read_vmcs st s v f ⦃ _ => True ⦄ := by
  unfold vcpu.read_vmcs
  exact WP.spec_bind (vcpu.vmcs_addr.off v f) fun _ _ => WP.spec_mono (LawfulStore.read_spec s _) fun _ _ => trivial

/-- A VCPU word write within `XS`. -/
theorem vcpu.set.xs (hH : HeapOK H) {s0 s : S} {v o x : U64} (hv : H v = some (.other 15))
    (ho : o.val < 2 ^ 15) (h8 : o.val % 8 = 0)
    (h : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 s) :
    vcpu.set st s v o x ⦃ s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 s' ⦄ := by
  unfold vcpu.set
  simp only [lift, bind_ok]
  exact WP.spec_mono (LawfulStore.write_spec s _ x) fun s' e => e ▸
    XSV.capw h (writesIn_wr (vcpu_obj_aligned hH hv ho h8)) fun b e => e ▸ vcpu_obj_capw hH hv ho h8

theorem vcpu.report_loop0.xs {s0 s : S} {t v b i : U64}
    (h : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 s) (ht : t ∈ H.tcbs) (hb : BufOK U b) :
    vcpu.report_loop0 st s t v b i ⦃ s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report_loop0
  apply loop.spec_decr_nat (measure := fun y => 30 - y.2.val)
    (inv := fun y => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    try dsimp only
    unfold vcpu.report_loop0.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hj
    have hj' : j.val < 30 := by simpa [vcpu.NUM_MRS] using hj
    step as ⟨i0, hi0⟩
    step as ⟨i1, _⟩
    refine WP.spec_bind (vcpu.get.any _ _ _) fun val _ => ?_
    refine WP.spec_bind (msg.set_mr.xsv (v := val) h1 ht hb (by omega)) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    try simp only [uncurry_apply_pair]
    step as ⟨j2, hj2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

theorem vcpu.report_loop1.xs {s0 s : S} {t v b j : U64}
    (h : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 s) (ht : t ∈ H.tcbs) (hb : BufOK U b) :
    vcpu.report_loop1 st s t v b j ⦃ s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.report_loop1
  apply loop.spec_decr_nat (measure := fun y => 15 - y.2.val)
    (inv := fun y => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac ∅ Q R s0 y.1)
  · rintro ⟨s1, k⟩ h1
    simp only at h1
    try dsimp only
    unfold vcpu.report_loop1.body
    try dsimp only
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hk
    have hk' : k.val < 15 := by simpa using hk
    step as ⟨i0, hi0⟩
    step as ⟨i1, _⟩
    step as ⟨i2, _⟩
    refine WP.spec_bind (vcpu.get.any _ _ _) fun val _ => ?_
    refine WP.spec_bind (msg.set_mr.xsv (v := val) h1 ht hb (by omega)) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    try simp only [uncurry_apply_pair]
    step as ⟨k2, hk2⟩
    exact ⟨h2, by first | omega | (dsimp only; omega)⟩
  · exact h

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

/-- `vcpu.report`'s four state words of a VCPU without an exit yet. -/
def rFour (st : machine.Store S) {A : Type _} (ar : machine.Arch A) (s1 : S) (a : A) (t b v : U64) : Result S := do
  let i1 ← ar.virtualization a
  let flags ←
    if i1 = 2#u64
    then
      do
      let i2 ← vcpu.svm.RFLAGS
      vcpu.get st s1 v i2
    else vcpu.read_vmcs st s1 v vcpu.vmx.GUEST_RFLAGS
  let int ←
    if i1 = 2#u64
    then vcpu.get st s1 v vcpu.svm.INT_STATE
    else
      vcpu.read_vmcs st s1 v
        vcpu.vmx.GUEST_INTERRUPTABILITY
  let cr3 ←
    if i1 = 2#u64
    then do
         let i2 ← vcpu.svm.CR3
         vcpu.get st s1 v i2
    else ok 0#u64
  let cr2 ←
    if i1 = 2#u64
    then do
         let i2 ← vcpu.svm.CR2
         vcpu.get st s1 v i2
    else vcpu.get st s1 v vcpu.CR2
  let (_, s3) ← msg.set_mr st s1 t b 7#u64 flags
  let (_, s4) ← msg.set_mr st s3 t b 8#u64 int
  let (_, s5) ← msg.set_mr st s4 t b 9#u64 cr3
  let (_, s6) ← msg.set_mr st s5 t b 29#u64 cr2
  ok s6

/-- `vcpu.report`'s tail: the pending words, `PENDING`, the message info and badge, running. -/
def rTail (st : machine.Store S) (s2 : S) (t b badge : U64) (pending : Bool) (f : S → Result S) : Result S := do
  let s3 ←
    if pending
    then ok s2
    else
      do
      let (_, s4) ← msg.set_mr st s2 t b 3#u64 0#u64
      let (_, s5) ← msg.set_mr st s4 t b 4#u64 0#u64
      ok s5
  let s4 ← f s3
  if pending
  then
    let s5 ←
      obj.Tcb.set_reg st t s4 layout.reg.MSG_INFO 1#u64
    if pending
    then
      let s6 ← obj.Tcb.set_reg st t s5 layout.reg.BADGE 0#u64
      sched.set_thread_state st s6 t sched.TS_RUNNING
    else
      let s6 ← obj.Tcb.set_reg st t s5 layout.reg.BADGE badge
      sched.set_thread_state st s6 t sched.TS_RUNNING
  else
    let s5 ←
      obj.Tcb.set_reg st t s4 layout.reg.MSG_INFO 0#u64
    if pending
    then
      let s6 ← obj.Tcb.set_reg st t s5 layout.reg.BADGE 0#u64
      sched.set_thread_state st s6 t sched.TS_RUNNING
    else
      let s6 ← obj.Tcb.set_reg st t s5 layout.reg.BADGE badge
      sched.set_thread_state st s6 t sched.TS_RUNNING

theorem rFour.xs {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s1 : S} {a : A} {t b v : U64}
    {Ac1 : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (x : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 s1) (ht : t ∈ H.tcbs) (hb : BufOK U b) :
    rFour st ar s1 a t b v ⦃ s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold rFour
  refine WP.spec_bind (hA.virtualization a) fun i1 _ => ?_
  have RD : ∀ (m : Result U64), (m = vcpu.get st s1 v vcpu.svm.INT_STATE ∨ True) → True := fun _ _ => trivial
  clear RD
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_bind (vcpu.svm.RFLAGS.spec) fun _ _ => vcpu.get.any _ _ _
    · exact vcpu.read_vmcs.any _ _ _) fun flags _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact vcpu.get.any _ _ _
    · exact vcpu.read_vmcs.any _ _ _) fun int _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_bind (vcpu.svm.CR3.spec) fun _ _ => vcpu.get.any _ _ _
    · exact (WP.spec_ok _).2 trivial) fun cr3 _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact WP.spec_bind (vcpu.svm.CR2.spec) fun _ _ => vcpu.get.any _ _ _
    · exact vcpu.get.any _ _ _) fun cr2 _ => ?_
  refine WP.spec_bind (msg.set_mr.xsv x ht hb (by simp)) ?_
  rintro ⟨_, s3⟩ ⟨x3, -⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.xsv x3 ht hb (by simp)) ?_
  rintro ⟨_, s4⟩ ⟨x4, -⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.xsv x4 ht hb (by simp)) ?_
  rintro ⟨_, s5⟩ ⟨x5, -⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (msg.set_mr.xsv x5 ht hb (by simp)) ?_
  rintro ⟨_, s6⟩ ⟨x6, -⟩
  try simp only [uncurry_apply_pair]
  exact (WP.spec_ok _).2 x6

theorem report_final {s0 s sX : S} {t : U64} {Ac1 : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s)
    (x : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s sX) (ht : t ∈ H.tcbs)
    (nb : ¬ BlockedR (L.mem sX (stA t))) :
    sched.set_thread_state st sX t sched.TS_RUNNING ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ∧
      L.ksb s' = L.ksb s ⦄ :=
  WP.spec_mono (sched.set_thread_state.running_cur0 (h.ofXS x) ht nb) fun _ ⟨c, k⟩ =>
    ⟨c, k.trans x.1.fr.2.2.2.2.2.2⟩

theorem rTail.spec {s0 s s2 : S} {t b badge : U64} {pending : Bool} {Ac1 : Set U64}
    {Q : U64 → U64 → List U64} {R : U64 → List U64} {f : S → Result S}
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s)
    (x : XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s2) (ht : t ∈ H.tcbs) (hb : BufOK U b)
    (hst : ¬ BlockedR (L.mem s (stA t)))
    (hf : ∀ s3, XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s3 →
      f s3 ⦃ s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s' ⦄) :
    rTail st s2 t b badge pending f ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ∧
      L.ksb s' = L.ksb s ⦄ := by
  have NB : ∀ s', XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s' →
      ¬ BlockedR (L.mem s' (stA t)) := fun s' x => by
    rw [stA_eq, x.1.fr.2.2.2.2.1 _ ht _ (by simp) (by simp) (by simp), ← stA_eq]; exact hst
  unfold rTail
  refine WP.spec_bind (Pₘ := fun s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s') ?_
    fun s3 x3 => ?_
  · split
    · exact (WP.spec_ok _).2 x
    · refine WP.spec_bind (msg.set_mr.xsv x ht hb (by simp)) ?_
      rintro ⟨_, s4⟩ ⟨x4, -⟩
      try simp only [uncurry_apply_pair]
      refine WP.spec_bind (msg.set_mr.xsv x4 ht hb (by simp)) ?_
      rintro ⟨_, s5⟩ ⟨x5, -⟩
      exact (WP.spec_ok _).2 x5
  refine WP.spec_bind (hf s3 x3) fun s4 x4 => ?_
  have FIN : ∀ (m i : U64), (do
      let s5 ← obj.Tcb.set_reg st t s4 layout.reg.MSG_INFO m
      let s6 ← obj.Tcb.set_reg st t s5 layout.reg.BADGE i
      sched.set_thread_state st s6 t sched.TS_RUNNING) ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ∧
        L.ksb s' = L.ksb s ⦄ := fun m i =>
    WP.spec_bind (obj.Tcb.set_reg.xsv x4 ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])) fun s5 x5 =>
      WP.spec_bind (obj.Tcb.set_reg.xsv x5 ht (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s6 x6 =>
        report_final h x6 ht (NB _ x6)
  split <;> first | exact FIN _ _ | (split <;> exact FIN _ _)

set_option maxHeartbeats 16000000 in
/-- **A VCPU-bound thread's report keeps `Cur0`**: its message registers and
IPC buffer (user words, `XferHyps.buf`), the VCPU's `PENDING` word, and the
thread set running. -/
theorem vcpu.report.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) (hH : HeapOK H) {s0 s : S} {a : A} {t badge : U64}
    (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) (he : EntAt st P3Ok s0)
    (hU : UserOK st H.tcbs Cs H.omega H U s)
    (ht : t ∈ H.tcbs) (hst : ¬ BlockedR (L.mem s (stA t)))
    (hbd : L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      H (L.mem s (core.num.U64.wrapping_add t 3664#u64)) = some (.other 15)) :
    vcpu.report st ar s a t badge ⦃ s' => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s' ∧
      L.ksb s' = L.ksb s ⦄ := by
  obtain ⟨Ac1, hX⟩ := h.bxi
  obtain ⟨Q, R, x0⟩ := BXI.xs hX hU
  have x00 := XSV.start x0
  -- #80 / #81: `vcpu.report.gen` with `P` the `XSV` stretch from `s`
  have NB : ∀ s', XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s' →
      ¬ BlockedR (L.mem s' (stA t)) := fun s' x => by
    rw [stA_eq, x.1.fr.2.2.2.2.1 _ ht _ (by simp) (by simp) (by simp), ← stA_eq]; exact hst
  refine vcpu.report.gen (Bok := BufOK U) (vOk := fun v => H v = some (.other 15))
    (P := fun s' => XSV st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac1 ∅ Q R s s') hA
    ⟨fun s1 b i v hb h1 hi => WP.spec_mono (msg.set_mr.xsv h1 ht hb (by omega)) fun r hr => hr.1,
     fun s1 r v h1 hr => obj.Tcb.set_reg.xsv h1 ht (by
       rcases hr with rfl | rfl | rfl <;>
         simp [layout.reg.MSG_INFO, layout.reg.BADGE, layout.reg.FAULT_IP, layout.reg.RSI, layout.reg.RDI]),
     fun s1 v h1 hv => vcpu.set.xs hH hv (by simp [vcpu.PENDING]) (by simp [vcpu.PENDING]) h1⟩
    (fun s1 x1 => report_final h x1 ht (NB _ x1)) x00
    (E.buf _ _ _ _ s t ⟨s0, he, h.fr⟩ x0.1 ht) (fun h0 _ => hbd h0)
end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

/-- **The VCPU objects' placement** (P3's, over the heap's sets): the heap is
well formed, a VCPU's `TCB` word is null or a TCB, a TCB's VCPU word is null
or a VCPU, and the listed VCPUs are VCPU objects off the kernel-global
area. -/
structure VcpuPl (st : machine.Store S) [L : LawfulStore st] (H : Heap) (Cs Rp Scs Nt : Set U64) (Z : U64 → Nat)
    (s0 : S) : Prop where
  heap : HeapOK H
  tcb : ∀ (Ac : Set U64) (s : S) (v : U64), Fr0 st H.tcbs Cs H.omega H H.frame Scs Z s0 s → BXI st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s →
    H v = some (.other 15) → Tz H.tcbs (L.mem s (core.num.U64.wrapping_add v vcpu.TCB))
  bound : ∀ (Ac : Set U64) (s : S) (t : U64), Fr0 st H.tcbs Cs H.omega H H.frame Scs Z s0 s → BXI st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s → t ∈ H.tcbs →
    L.mem s (core.num.U64.wrapping_add t 3664#u64) ≠ 0#u64 →
      H (L.mem s (core.num.U64.wrapping_add t 3664#u64)) = some (.other 15)
  listed : ∀ (Ac : Set U64) (s : S) (v : U64), Fr0 st H.tcbs Cs H.omega H H.frame Scs Z s0 s → BXI st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s →
    VListed st s v → H v = some (.other 15) ∧ (v.val + 2 ^ 15 ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ v.val)

set_option maxHeartbeats 4000000 in
/-- **`detach` keeps `Cur0`**: the VCPU's stall, the thread's report when it
runs in the VCPU, the VCPU's `TCB` word and the thread's VCPU word cleared. -/
theorem vcpu.detach.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : XferHyps st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) {s0 s : S} (P : VcpuPl st H Cs Rp Scs Nt Z s0) {a : A}
    {t : U64} (h : Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s) (he : EntAt st P3Ok s0)
    (hU : UserOK st H.tcbs Cs H.omega H U s) (ht : t ∈ H.tcbs) :
    vcpu.detach st ar s a t ⦃ r => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 r.1 ∧
      L.ksb r.1 = L.ksb s ⦄ := by
  unfold vcpu.detach vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  split
  · exact (WP.spec_ok _).2 ⟨h, rfl⟩
  rename_i hv0
  obtain ⟨Ac1, hX⟩ := h.bxi
  have hv : H v = some (.other 15) := by rw [ev]; exact P.bound Ac1 s t h.fr hX ht (by rw [← ev]; exact hv0)
  refine WP.spec_bind (vcpu.stall.cur0 hA a v h) ?_
  rintro ⟨s1, a1⟩ ⟨h1, k1, -⟩
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (obj.Tcb.state.spec s1 t) fun i ei => ?_
  refine WP.spec_bind (Pₘ := fun s2 => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s0 s2 ∧
      L.ksb s2 = L.ksb s) ?_ fun s2 ⟨h2, k2⟩ => ?_
  · split
    · rename_i hrv
      obtain ⟨Ac2, hX1⟩ := h1.bxi
      refine WP.spec_mono (vcpu.report.cur0 hA E P.heap h1 he (hU.ksb k1) ht ?_
        (fun hn => P.bound Ac2 s1 t h1.fr hX1 ht hn)) fun s' ⟨c, k⟩ => ⟨c, k.trans k1⟩
      rw [← ei, hrv]; exact nbr_runnable (by unfold Runnable; simp)
    · exact (WP.spec_ok _).2 ⟨h1, k1⟩
  simp only [vcpu.set, lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
  subst e3
  have h3 := h2.vword P.heap hv (o := vcpu.TCB) (x := 0#u64) (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  step as ⟨o2, ho2⟩
  subst ho2
  try simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.write_spec _ _ _) fun s4 e4 => ?_
  subst e4
  exact (WP.spec_ok _).2 ⟨h3.tvcpu ht, by rw [L.ksb_wr, L.ksb_wr]; exact k2⟩

end

end Fl4Proofs.P1
