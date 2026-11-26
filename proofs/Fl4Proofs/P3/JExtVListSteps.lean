/-
P3 (line mmuAD, gen 23): **`VList` across `vcpu::init` (insertion at the head) and `vcpu::finalise` (unlink).**

* `VWL v`: the VCPU's own words other than `TCB` / `NEXT` / `PREV` (offsets 20480 / 20488 / 20496). Every write
  of `init` after its two link writes and the head write lands there: `vsetL_w`, `vmcsL_w`, the loops
  `vcpu.init_loop0.footL`, `init_loop1.footL`, `reset_svm_loop.footL`, `reset_svm.footL` (copies of P3/JExtVInit's
  with the smaller word set: `XCR0` 20504, IO bitmap from 24576, VMCB below 1768 and `SVM_CPU` 20536, VMCS below
  20480).
* **`vcpu.init.vals`**: `init` writes only `VWL v`, `v`'s `NEXT`, the head word and the old head's `PREV`, and
  leaves `NEXT v = old head`, `head = v`, `PREV (old head) = v`. Premises: `hv` (VFits), `hha` (head aligned),
  `hhv` (head outside `v`'s object), `hhd` (an old head is a fitting VCPU apart from `v`, the head word outside it).
* **`vcpu_init_vlist`**: `VList V th s` ⇒ `VList (insert v V) th' s'` after `init`. Premises (all placement of the
  new object, [J] as gen 22's `create_vcpu_grow`): `hf` / `hvv` (the VCPUs of `V` fit and are pairwise apart:
  `JVLay.vfit` / `vv`), `hap` (the new object apart from them: the retype's freshness), `hhv` (the head word in no
  VCPU: `JVm.ks`), `hv0`, `hvV` (`v ∉ V`), **`hz`: the new `PREV` word is 0** (the retype's zeroing, `WinZero` as
  `create_vcpu_grow_win`; `init` never writes it), `hth` / `hsw` (typed heap's words not grown), `hko` (the new
  `TCB` word is not the head word).
* **`create_vcpu_growL`**: `objects.create_arch_object … X86Vcpu v` gives `Cap.Vcpu v`, `JExtV (insert v V) X th'`
  and `VList (insert v V) th'` together.
* **`vlist_unlink`** (memory level) and **`vcpu_finalise_vl`**: `vcpu.finalise v` (stall, release, detach, unlink)
  keeps `JExtV V X th`, `RunVmB th`, leaves `v`'s `TCB` word 0 and gives **`VList (V \ {v}) th`**. Premises: `Ly`
  (JVLay), `Da` (DetAtB), `hnd` [J] (as `JVLay.finPl`), `hhv` [J] (the head word in no VCPU of `V`), and
  **`hhc` [J]: the head word is no detach word `CW`** — what is missing is that no IPC-buffer word (`U`, user
  frames) is the kernel-global head word; the node, TCB and VCPU parts of `CW` follow from `JKern` / `JVm`
  (`JAtZ.hhc` below derives `hhc` from exactly that buffer fact `hU`).

No [P] / [W] / [S] premise; no existing statement changed.
-/
import Fl4Proofs.P3.JExtVList
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P0.Consts

noncomputable section

theorem vl_val_ne {a b : U64} (h : a ≠ b) : a.val ≠ b.val := fun e => h (UScalar.eq_of_val_eq e)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {V X U : Set U64} {th : TypedHeap}

/-- The VCPU's words other than `TCB` / `NEXT` / `PREV`. -/
def VWL (v b : U64) : Prop :=
  ∃ o : U64, o.val < 32768 ∧ o.val % 8 = 0 ∧ o.val ≠ 20480 ∧ o.val ≠ 20488 ∧ o.val ≠ 20496 ∧
    b = core.num.U64.wrapping_add v o

theorem vwl_val {v b : U64} (hv : VFits v) (h : VWL v b) :
    v.val ≤ b.val ∧ b.val < v.val + 32768 ∧ b.val ≠ v.val + 20480 ∧ b.val ≠ v.val + 20488 ∧
      b.val ≠ v.val + 20496 := by
  obtain ⟨o, h1, -, h3, h4, h5, rfl⟩ := h
  rw [vfits_wadd hv h1]; omega

theorem vwl_vw {v b : U64} (h : VWL v b) : VW v b := by
  obtain ⟨o, h1, h2, h3, -, -, e⟩ := h; exact ⟨o, h1, h2, h3, e⟩

theorem vset_eq (s : S) (v o x : U64) :
    vcpu.set st s v o x ⦃ s' => s' = L.wr s (core.num.U64.wrapping_add v o) x ⦄ := by
  unfold vcpu.set; simp only [lift, bind_ok]; exact P1.LawfulStore.write_spec s _ _

theorem vsetL_w {s0 s1 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VWL v b → W b)
    (h : P1.WritesIn st s0 s1 W) (o x : U64) (h1 : o.val < 32768) (h2 : o.val % 8 = 0) (h3 : o.val ≠ 20480)
    (h4 : o.val ≠ 20488) (h5 : o.val ≠ 20496) :
    vcpu.set st s1 v o x ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  have hb : VWL v (core.num.U64.wrapping_add v o) := ⟨o, h1, h2, h3, h4, h5, rfl⟩
  have ha := (vw_of_off hv h1 h2 h3).2
  unfold vcpu.set
  simp only [lift, bind_ok]
  exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
    subst e
    exact (h.trans (P1.writesIn_wr ha)).mono fun b hb' => hb'.elim id fun e => e ▸ hW _ hb

theorem vmcsL_w {s0 s1 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VWL v b → W b)
    (h : P1.WritesIn st s0 s1 W) (f x : U64) :
    vcpu.write_vmcs st s1 v f x ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.write_vmcs
  refine WP.spec_bind (P1.vcpu.vmcs_addr.off v f) ?_
  rintro _ ⟨o, h1, h2, rfl⟩
  have hb : VWL v (core.num.U64.wrapping_add v o) := ⟨o, by omega, h2, by omega, by omega, by omega, rfl⟩
  have ha := (vw_of_off hv (o := o) (by omega) h2 (by omega)).2
  exact WP.spec_mono (P1.LawfulStore.write_spec s1 _ _) fun s' e => by
    subst e
    exact (h.trans (P1.writesIn_wr ha)).mono fun b hb' => hb'.elim id fun e => e ▸ hW _ hb

theorem vcpu.init_loop0.footL {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VWL v b → W b)
    (s : S) (i : U64) (h : P1.WritesIn st s0 s W) :
    vcpu.init_loop0 st s v i ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.init_loop0
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 1024 - x.2.val)
    (inv := fun x => P1.WritesIn st s0 x.1 W)
  · rintro ⟨x0, x1⟩ hx
    simp only at hx
    dsimp only
    unfold vcpu.init_loop0.body
    split
    · rename_i hlt
      have hlt' : x1.val < 1024 := by simpa using hlt
      step as ⟨i1, hi1⟩
      step as ⟨i2, hi2⟩
      have hio : i2.val = 24576 + i1.val := by rw [hi2]; simp [vcpu.IO]
      refine WP.spec_bind (vsetL_w hv hW hx i2 _ (by omega) (by omega) (by omega) (by omega) (by omega))
        fun s1 w1 => ?_
      step as ⟨i3, hi3⟩
      exact ⟨w1, by scalar_tac⟩
    · exact (WP.spec_ok _).2 hx
  · exact h

theorem vcpu.init_loop1.footL (hA : P0.ArchTotal ar) {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v)
    (hW : ∀ b, VWL v b → W b) (s : S) (a : A) (j : Usize) (h : P1.WritesIn st s0 s W) :
    vcpu.init_loop1 st ar s a v j ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.init_loop1
  apply loop.spec_decr_nat (measure := fun x : S × Usize => 73 - x.2.val)
    (inv := fun x => P1.WritesIn st s0 x.1 W)
  · rintro ⟨x0, x1⟩ hx
    simp only at hx
    dsimp only
    unfold vcpu.init_loop1.body
    simp only [lift, bind_ok]
    split
    · rename_i hlt
      step as ⟨f, _⟩
      refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
      refine WP.spec_bind (Pₘ := fun s2 => P1.WritesIn st s0 s2 W) ?_ fun s2 h2 => ?_
      · split
        · exact vmcsL_w hv hW hx _ _
        · exact (WP.spec_ok _).2 hx
      step as ⟨j1, hj1⟩
      exact ⟨h2, by scalar_tac⟩
    · exact (WP.spec_ok _).2 hx
  · exact h

theorem vcpu.reset_svm_loop.footL {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VWL v b → W b)
    (s : S) (off : U64) (h8 : off.val % 8 = 0) (h : P1.WritesIn st s0 s W) :
    vcpu.reset_svm_loop st s v off ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  unfold vcpu.reset_svm_loop
  apply loop.spec_decr_nat (measure := fun x : S × U64 => 1169 - x.2.val)
    (inv := fun x => x.2.val % 8 = 0 ∧ P1.WritesIn st s0 x.1 W)
  · rintro ⟨x0, x1⟩ ⟨hx8, hx⟩
    simp only at hx hx8
    dsimp only
    unfold vcpu.reset_svm_loop.body
    split
    · rename_i hle
      have hle' : x1.val ≤ 1168 := by simpa using hle
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun attr _ => ?_
      · repeat' split
        all_goals exact (WP.spec_ok _).2 trivial
      step as ⟨i, _⟩
      simp only [lift, bind_ok]
      refine WP.spec_bind (vsetL_w hv hW hx x1 _ (by omega) hx8 (by omega) (by omega) (by omega)) fun s1 w1 => ?_
      step as ⟨off1, hoff1⟩
      first
        | exact ⟨⟨by omega, w1⟩, by scalar_tac⟩
        | omega
        | scalar_tac
    · exact (WP.spec_ok _).2 hx
  · exact ⟨h8, h⟩

theorem vcpu.reset_svm.footL {s0 : S} {v : U64} {W : U64 → Prop} (hv : VFits v) (hW : ∀ b, VWL v b → W b)
    (s : S) (h : P1.WritesIn st s0 s W) :
    vcpu.reset_svm st s v ⦃ s' => P1.WritesIn st s0 s' W ⦄ := by
  have hv' := hv
  obtain ⟨hv1, hv2⟩ := hv'
  unfold vcpu.reset_svm
  refine WP.spec_bind (vsetL_w hv hW h vcpu.SVM_CPU 0#u64 (by simp [vcpu.SVM_CPU]) (by simp [vcpu.SVM_CPU])
    (by simp [vcpu.SVM_CPU]) (by simp [vcpu.SVM_CPU]) (by simp [vcpu.SVM_CPU])) fun s1 w1 => ?_
  simp only [lift, bind_ok]
  step with vcpu.svm.END.spec as ⟨i1, e1⟩
  subst e1
  step as ⟨i2, hi2⟩
  have hi2v : i2.val = 744 := by scalar_tac
  have hp : (core.num.U64.wrapping_add v 1024#u64).val = v.val + 1024 := vfits_wadd hv (by simp)
  refine WP.spec_bind (P1.LawfulStore.zero_spec s1 _ _) fun s2 e2 => ?_
  subst e2
  have z : P1.WritesIn st s1 (L.zr s1 (core.num.U64.wrapping_add v 1024#u64) i2)
      (fun b => (core.num.U64.wrapping_add v 1024#u64).val ≤ b.val ∧
        b.val < (core.num.U64.wrapping_add v 1024#u64).val + i2.val) :=
    ⟨L.ksb_zr _ _ _, L.cpu_zr _ _ _, fun b hb hnb => by
      rw [L.mem_zr _ _ _ _ (by unfold P1.Aligned; rw [hp]; omega) (by omega) (by rw [hp]; omega) hb, if_neg hnb]⟩
  have w2 := wi_mono_al (w1.trans z) fun b hb hh => hh.elim id fun hr => by
    obtain ⟨o, h1, h2, h3, e⟩ := vw_of_val hv hb (by omega) (by omega) (by omega)
    have := congrArg UScalar.val e
    rw [vfits_wadd hv h1] at this
    exact hW _ ⟨o, h1, h2, h3, by omega, by omega, e⟩
  refine WP.spec_bind (vcpu.reset_svm_loop.footL hv hW _ 1024#u64 (by simp) w2) fun s3 w3 => ?_
  refine WP.spec_bind (vsetL_w hv hW w3 1040#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s4 w4 => ?_
  refine WP.spec_bind (vsetL_w hv hW w4 1048#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s5 w5 => ?_
  step as ⟨i3, _⟩
  step with vcpu.svm.EFER.spec as ⟨i4, e4⟩
  subst e4
  refine WP.spec_bind (vsetL_w hv hW w5 1232#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s6 w6 => ?_
  step with vcpu.svm.CR0.spec as ⟨i5, e5⟩
  subst e5
  refine WP.spec_bind (vsetL_w hv hW w6 1368#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s7 w7 => ?_
  step with vcpu.svm.DR6.spec as ⟨i6, e6⟩
  subst e6
  refine WP.spec_bind (vsetL_w hv hW w7 1384#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s8 w8 => ?_
  step with vcpu.svm.DR7.spec as ⟨i7, e7⟩
  subst e7
  refine WP.spec_bind (vsetL_w hv hW w8 1376#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s9 w9 => ?_
  step with vcpu.svm.RFLAGS.spec as ⟨i8, e8⟩
  subst e8
  refine WP.spec_bind (vsetL_w hv hW w9 1392#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s10 w10 => ?_
  step with vcpu.svm.RIP.spec as ⟨i9, e9⟩
  subst e9
  refine WP.spec_bind (vsetL_w hv hW w10 1400#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
    fun s11 w11 => ?_
  step with vcpu.svm.G_PAT.spec as ⟨i10, e10⟩
  subst e10
  exact vsetL_w hv hW w11 1640#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp)

/-- `init`'s precise words (module docstring). -/
def InitL (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (v b : U64) : Prop :=
  VWL v b ∨ b = P1.vNextA v ∨ b = P1.vHeadA st s ∨
    (L.mem s (P1.vHeadA st s) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vHeadA st s)))

set_option maxHeartbeats 4000000 in
/-- **`vcpu::init`'s list writes** (module docstring). -/
theorem vcpu.init.vals (hA : P0.ArchTotal ar) (s : S) (a : A) {v : U64} (hv : VFits v)
    (hha : P1.Aligned (P1.vHeadA st s))
    (hhv : (P1.vHeadA st s).val < v.val ∨ v.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhd : L.mem s (P1.vHeadA st s) ≠ 0#u64 → VFits (L.mem s (P1.vHeadA st s)) ∧
      ((L.mem s (P1.vHeadA st s)).val + 32768 ≤ v.val ∨ v.val + 32768 ≤ (L.mem s (P1.vHeadA st s)).val) ∧
      ((P1.vHeadA st s).val < (L.mem s (P1.vHeadA st s)).val ∨
        (L.mem s (P1.vHeadA st s)).val + 32768 ≤ (P1.vHeadA st s).val)) :
    vcpu.init st ar s a v ⦃ s' => P1.WritesIn st s s' (InitL st s v) ∧
      L.mem s' (P1.vNextA v) = L.mem s (P1.vHeadA st s) ∧ L.mem s' (P1.vHeadA st s) = v ∧
      (L.mem s (P1.vHeadA st s) ≠ 0#u64 → L.mem s' (vPrevA (L.mem s (P1.vHeadA st s))) = v) ⦄ := by
  have hv' := hv
  obtain ⟨hv1, hv2⟩ := hv'
  have enx : (P1.vNextA v).val = v.val + 20488 := lay_next_val hv2
  have anx : P1.Aligned (P1.vNextA v) := by unfold P1.Aligned; omega
  have dHN : (P1.vHeadA st s).val ≠ (P1.vNextA v).val := by omega
  unfold vcpu.init
  step with P1.obj.ks_get.spec as ⟨hd, ehd⟩
  have ehd' : hd = L.mem s (P1.vHeadA st s) := ehd
  subst ehd'
  refine WP.spec_bind (vset_eq s v vcpu.NEXT _) fun s1 e1 => ?_
  subst e1
  have ea1 : core.num.U64.wrapping_add v vcpu.NEXT = P1.vNextA v := rfl
  rw [ea1]
  -- after the first link write
  refine WP.spec_bind (Pₘ := fun s2 => P1.WritesIn st s s2 (InitL st s v) ∧
      L.mem s2 (P1.vNextA v) = L.mem s (P1.vHeadA st s) ∧
      (L.mem s (P1.vHeadA st s) ≠ 0#u64 → L.mem s2 (vPrevA (L.mem s (P1.vHeadA st s))) = v)) ?_
    fun s2 ⟨w2, n2, p2⟩ => ?_
  · have w1 : P1.WritesIn st s (L.wr s (P1.vNextA v) (L.mem s (P1.vHeadA st s))) (InitL st s v) :=
      (P1.writesIn_wr anx).mono fun b e => Or.inr (Or.inl e)
    split
    · rename_i hn
      have hn' : L.mem s (P1.vHeadA st s) ≠ 0#u64 := by simpa using hn
      obtain ⟨hf, hap, -⟩ := hhd hn'
      have epv : (vPrevA (L.mem s (P1.vHeadA st s))).val = (L.mem s (P1.vHeadA st s)).val + 20496 :=
        lay_prev_val hf.2
      have apv : P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s))) := by
        have := hf.1; unfold P1.Aligned; omega
      refine WP.spec_mono (vset_eq _ _ vcpu.PREV v) fun s' e => ?_
      subst e
      have ea : core.num.U64.wrapping_add (L.mem s (P1.vHeadA st s)) vcpu.PREV =
          vPrevA (L.mem s (P1.vHeadA st s)) := rfl
      rw [ea]
      refine ⟨(w1.trans (P1.writesIn_wr apv)).mono fun b h => h.elim id fun e => Or.inr (Or.inr (Or.inr ⟨hn', e⟩)),
        ?_, fun _ => L.mem_wr_same apv⟩
      rw [L.mem_wr_ne apv anx (by have := hf.1; omega), L.mem_wr_same anx]
    · rename_i hn
      have hn' : L.mem s (P1.vHeadA st s) = 0#u64 := UScalar.eq_of_val_eq (by simpa using hn)
      exact (WP.spec_ok _).2 ⟨w1, L.mem_wr_same anx, fun h => absurd hn' h⟩
  refine WP.spec_bind (P1.obj.ks_set.spec s2 _ _) fun s3 e3 => ?_
  subst e3
  have ea : core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD = P1.vHeadA st s := by
    unfold P1.vHeadA; rw [w2.1]
  rw [ea]
  have FIN : ∀ s', P1.WritesIn st (L.wr s2 (P1.vHeadA st s) v) s' (VWL v) →
      P1.WritesIn st s s' (InitL st s v) ∧ L.mem s' (P1.vNextA v) = L.mem s (P1.vHeadA st s) ∧
        L.mem s' (P1.vHeadA st s) = v ∧
        (L.mem s (P1.vHeadA st s) ≠ 0#u64 → L.mem s' (vPrevA (L.mem s (P1.vHeadA st s))) = v) := by
    intro s' w'
    have nvw : ∀ b, (b.val < v.val ∨ v.val + 32768 ≤ b.val ∨ b.val = v.val + 20488) → ¬ VWL v b :=
      fun b hb h => by have := vwl_val hv h; omega
    refine ⟨((w2.trans (P1.writesIn_wr hha)).trans w').mono fun b h => ?_, ?_, ?_, fun hn => ?_⟩
    · rcases h with (h | e) | h
      · exact h
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inl h
    · rw [w'.mem_eq anx (nvw _ (Or.inr (Or.inr enx))), L.mem_wr_ne hha anx dHN]; exact n2
    · rw [w'.mem_eq hha (nvw _ (by omega)), L.mem_wr_same hha]
    · obtain ⟨hf, hap, hhh⟩ := hhd hn
      have epv : (vPrevA (L.mem s (P1.vHeadA st s))).val = (L.mem s (P1.vHeadA st s)).val + 20496 :=
        lay_prev_val hf.2
      have apv : P1.Aligned (vPrevA (L.mem s (P1.vHeadA st s))) := by
        have := hf.1; unfold P1.Aligned; omega
      rw [w'.mem_eq apv (nvw _ (by omega)), L.mem_wr_ne hha apv (by omega)]; exact p2 hn
  have hW : ∀ b, VWL v b → VWL v b := fun _ h => h
  have w3 := P1.WritesIn.refl (st := st) (L.wr s2 (P1.vHeadA st s) v) (VWL v)
  refine WP.spec_bind (hA.vcpu_capability a 0#u64) fun i _ => ?_
  refine WP.spec_bind (vsetL_w hv hW w3 vcpu.XCR0 i (by simp [vcpu.XCR0]) (by simp [vcpu.XCR0])
    (by simp [vcpu.XCR0]) (by simp [vcpu.XCR0]) (by simp [vcpu.XCR0])) fun s4 w4 => ?_
  refine WP.spec_bind (vcpu.init_loop0.footL hv hW s4 0#u64 w4) fun s5 w5 => ?_
  refine WP.spec_bind (hA.virtualization a) fun i1 _ => ?_
  split
  · refine WP.spec_bind (vcpu.reset_svm.footL hv hW s5 w5) fun s6 w6 => ?_
    refine WP.spec_bind (vsetL_w hv hW w6 0#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
      fun s7 w7 => ?_
    step as ⟨i2, _⟩
    step with vcpu.EXCEPTIONS.spec as ⟨i3, _⟩
    simp only [lift, bind_ok]
    refine WP.spec_bind (vsetL_w hv hW w7 8#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
      fun s8 w8 => ?_
    refine WP.spec_bind (vsetL_w hv hW w8 16#u64 _ (by simp) (by simp) (by simp) (by simp) (by simp))
      fun s9 w9 => ?_
    step as ⟨i5, _⟩
    refine WP.spec_bind (vsetL_w hv hW w9 vcpu.svm.INT_CTL _ (by simp [vcpu.svm.INT_CTL])
      (by simp [vcpu.svm.INT_CTL]) (by simp [vcpu.svm.INT_CTL]) (by simp [vcpu.svm.INT_CTL])
      (by simp [vcpu.svm.INT_CTL])) fun s10 w10 => ?_
    exact WP.spec_mono (vsetL_w hv hW w10 vcpu.svm.NESTED_CTL _ (by simp [vcpu.svm.NESTED_CTL])
      (by simp [vcpu.svm.NESTED_CTL]) (by simp [vcpu.svm.NESTED_CTL]) (by simp [vcpu.svm.NESTED_CTL])
      (by simp [vcpu.svm.NESTED_CTL])) FIN
  · refine WP.spec_bind (vcpu.init_loop1.footL hA hv hW s5 a 0#usize w5) fun s6 w6 => ?_
    step as ⟨i2, _⟩
    refine WP.spec_bind (P0.vcpu.sanitize_vmcs.p0 _ _ _ _ hA) fun r _ => ?_
    simp only [lift, bind_ok]
    refine WP.spec_bind (vmcsL_w hv hW w6 _ _) fun s7 w7 => ?_
    refine WP.spec_bind (vmcsL_w hv hW w7 _ _) fun s8 w8 => ?_
    exact WP.spec_mono (vmcsL_w hv hW w8 _ _) FIN

/-- **`VList` grows at `vcpu::init`** (module docstring; placement premises [J]). -/
theorem vcpu_init_vlist (hA : P0.ArchTotal ar) {s : S} (a : A) (Vl : VList st V th s)
    (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hvv : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    {v : U64} (hv : VFits v) (hv0 : v ≠ 0#u64) (hvV : v ∉ V)
    (hap : ∀ w ∈ V, w.val + 32768 ≤ v.val ∨ v.val + 32768 ≤ w.val)
    (hhv : ∀ w, w ∈ insert v V → (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hz : L.mem s (vPrevA v) = 0#u64) {th' : TypedHeap} (hth : ∀ b, JW V th' b → JW V th b)
    (hsw : ∀ b, SW th' b → SW th b) (hko : vTcbA v ≠ P1.vHeadA st s) :
    vcpu.init st ar s a v ⦃ s' => P1.WritesIn st s s' (InitL st s v) ∧ VList st (insert v V) th' s' ⦄ := by
  obtain ⟨l, hnd, hm, hh, hs⟩ := Vl.lst
  have hha := Vl.hd.1
  have hv' := hv
  obtain ⟨hv1, hv2⟩ := hv'
  have hhd0 : L.mem s (P1.vHeadA st s) ≠ 0#u64 → L.mem s (P1.vHeadA st s) ∈ V := Vl.head
  refine WP.spec_mono (vcpu.init.vals hA s a hv hha (hhv v (Set.mem_insert v V)) fun hn => ?_) ?_
  · have hw := hhd0 hn
    exact ⟨⟨(hf _ hw).1, (hf _ hw).2⟩, hap _ hw, hhv _ (Set.mem_insert_of_mem v hw)⟩
  intro s' ⟨w, vn, vh, vp⟩
  refine ⟨w, ?_⟩
  have ea : P1.vHeadA st s' = P1.vHeadA st s := by unfold P1.vHeadA; rw [w.1]
  have epv : (vPrevA v).val = v.val + 20496 := lay_prev_val hv2
  have enx : (P1.vNextA v).val = v.val + 20488 := lay_next_val hv2
  -- a word of another VCPU of `V`, or off every VCPU of `V`, untouched
  have keep : ∀ b, P1.Aligned b → (b.val < v.val ∨ v.val + 32768 ≤ b.val) → b ≠ P1.vHeadA st s →
      (∀ hn : L.mem s (P1.vHeadA st s) ≠ 0#u64, b ≠ vPrevA (L.mem s (P1.vHeadA st s))) →
      L.mem s' b = L.mem s b := by
    intro b hb h1 h2 h3
    refine w.mem_eq hb ?_
    rintro (h | e | e | ⟨hn, e⟩)
    · have := vwl_val hv h; omega
    · rw [e] at h1; omega
    · exact h2 e
    · exact h3 hn e
  have hl : ∀ u ∈ l, u ∈ V := fun u hu => (hm u).1 hu
  have hvl : v ∉ l := fun h => hvV (hm v |>.1 h)
  refine ⟨⟨v :: l, List.nodup_cons.2 ⟨hvl, hnd⟩, fun x => ?_, ?_, ?_⟩, ?_⟩
  · simp only [List.mem_cons, Set.mem_insert_iff, hm]
  · rw [ea, vh]; rfl
  · refine VSeg.insert hs hnd hv0 ?_ ?_ ?_ ?_ ?_
    · rw [w.mem_eq (by unfold P1.Aligned; omega) ?_]; exact hz
      rintro (h | e | e | ⟨hn, e⟩)
      · have := vwl_val hv h; omega
      · have := congrArg UScalar.val e; omega
      · have := congrArg UScalar.val e; have := hhv v (Set.mem_insert v V); omega
      · have hw := hhd0 hn
        have := congrArg UScalar.val e
        rw [lay_prev_val (hf _ hw).2] at this
        rcases hap _ hw with h' | h' <;> omega
    · rw [vn, hh]
    · intro x l' e
      have hx : x = L.mem s (P1.vHeadA st s) := by rw [hh, e]; rfl
      have hn : L.mem s (P1.vHeadA st s) ≠ 0#u64 := by
        rw [← hx]; exact hs.ne0 x (by rw [e]; simp)
      rw [hx]; exact vp hn
    · intro u hu
      have huV := hl u hu
      have f := hf u huV
      have e1 := lay_next_val f.2
      refine keep _ (by unfold P1.Aligned; omega) (by rcases hap u huV with h | h <;> omega)
        (fun e => by have := congrArg UScalar.val e; have := hhv u (Set.mem_insert_of_mem v huV); omega)
        (fun hn e => ?_)
      have hw := hhd0 hn
      have := congrArg UScalar.val e
      rw [lay_prev_val (hf _ hw).2] at this
      have := (hf _ hw).1
      omega
    · intro u hu hne
      have huV := hl u hu
      have f := hf u huV
      have e1 := lay_prev_val f.2
      refine keep _ (by unfold P1.Aligned; omega) (by rcases hap u huV with h | h <;> omega)
        (fun e => by have := congrArg UScalar.val e; have := hhv u (Set.mem_insert_of_mem v huV); omega)
        (fun hn e => ?_)
      have hw := hhd0 hn
      have := congrArg UScalar.val e
      rw [lay_prev_val (hf _ hw).2] at this
      have hne' : u ≠ L.mem s (P1.vHeadA st s) := by rw [hh]; exact hne
      rcases hvv u huV _ hw hne' with h | h <;> omega
  · rw [ea]
    refine ⟨hha, fun h => ?_, fun h => Vl.hd.2.2 (hsw _ h)⟩
    rcases jw_insert h with h | e
    · exact Vl.hd.2.1 (hth _ h)
    · exact hko e.symm

set_option maxHeartbeats 4000000 in
/-- **The VT-x VCPU creation grows both `JExtV` and `VList`** (module docstring; premises [J] as in
`create_vcpu_grow` and `vcpu_init_vlist`). -/
theorem create_vcpu_growL (hA : P0.ArchTotal ar) {s : S} (E : JExtV (L := L) V X th s) (P : JWPl V th) (a : A)
    (Vl : VList st V th s) (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hvv : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    {v : U64} (hv : VFits v) (hv0 : v ≠ 0#u64) (hvV : v ∉ V)
    (hap : ∀ w ∈ V, w.val + 32768 ≤ v.val ∨ v.val + 32768 ≤ w.val)
    (hhv : ∀ w, w ∈ insert v V → (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hz : L.mem s (vPrevA v) = 0#u64) (hzt : L.mem s (vTcbA v) = 0#u64)
    (hd : ∀ b, InitW st s v b → ¬ JW V th b)
    {th' : TypedHeap} (htc : ∀ t, th' t = some .tcb ↔ th t = some .tcb) (hsl : ∀ y, IsSlot th' y → IsSlot th y)
    (hko : vTcbA v ≠ P1.vHeadA st s) (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ JExtV (L := L) (insert v V) X th' r.2.1 ∧
        VList st (insert v V) th' r.2.1 ⦄ := by
  have hth : ∀ b, JW V th' b → JW V th b := by
    rintro b (⟨y, hy, e⟩ | ⟨t, ht, e⟩ | h)
    · exact Or.inl ⟨y, hsl y hy, e⟩
    · exact Or.inr (Or.inl ⟨t, (htc t).1 ht, e⟩)
    · exact Or.inr (Or.inr h)
  have hsw : ∀ b, SW th' b → SW th b := fun b ⟨t, ht, e⟩ => ⟨t, (htc t).1 ht, e⟩
  have hv' := hv
  obtain ⟨hv1, hv2⟩ := hv'
  unfold objects.create_arch_object
  rw [if_pos rfl]
  refine WP.spec_bind (vcpu_init_vlist hA a Vl hf hvv hv hv0 hvV hap hhv hz hth hsw hko) fun s1 ⟨w, Vl'⟩ => ?_
  have wI : P1.WritesIn st s s1 (InitW st s v) := w.mono fun b h => by
    rcases h with h | e | e | h
    · exact Or.inl (vwl_vw h)
    · refine Or.inl ⟨vcpu.NEXT, by simp [vcpu.NEXT], by simp [vcpu.NEXT], by simp [vcpu.NEXT], e⟩
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr h)
  have e2 : (vTcbA v).val = v.val + 20480 := lay_vTcb_val hv2
  have ht0 : L.mem s1 (vTcbA v) = 0#u64 := by
    rw [w.mem_eq (by unfold P1.Aligned; omega) ?_]; exact hzt
    rintro (h | e | e | ⟨hn, e⟩)
    · have := vwl_val hv h; omega
    · have := congrArg UScalar.val e; rw [lay_next_val hv2] at this; omega
    · exact hko e
    · have hw := Vl.head hn
      have := congrArg UScalar.val e
      rw [lay_prev_val (hf _ hw).2] at this
      rcases hap _ hw with h' | h' <;> omega
  exact (WP.spec_ok _).2 ⟨rfl, E.grow P hv0 htc hsl wI hd ht0, Vl'⟩

/-! ## Unlink -/

/-- **The list after `finalise`'s four link writes** (module docstring). -/
theorem vlist_unlink {s s2 s4 : S} (Vl : VList st V th s)
    (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hvv : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    {v : U64} (hvV : v ∈ V) (k2 : ∀ b, LW st V s b → L.mem s2 b = L.mem s b) (hk2 : L.ksb s2 = L.ksb s)
    (w4 : P1.WritesIn st s2 s4 (fun b => (L.mem s (vPrevA v) = 0#u64 ∧ b = P1.vHeadA st s) ∨
      (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v))) ∨
      (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))))
    (vH : L.mem s (vPrevA v) = 0#u64 → L.mem s4 (P1.vHeadA st s) = L.mem s (P1.vNextA v))
    (vN : L.mem s (vPrevA v) ≠ 0#u64 → L.mem s4 (P1.vNextA (L.mem s (vPrevA v))) = L.mem s (P1.vNextA v))
    (vP : L.mem s (P1.vNextA v) ≠ 0#u64 → L.mem s4 (vPrevA (L.mem s (P1.vNextA v))) = L.mem s (vPrevA v)) :
    VList st (V \ {v}) th s4 := by
  obtain ⟨l, hnd, hm, hh, hs⟩ := Vl.lst
  have hal : ∀ b, LW st V s b → P1.Aligned b := fun b hb => Vl.lw_al hf hb
  have pvV : L.mem s (vPrevA v) ≠ 0#u64 → L.mem s (vPrevA v) ∈ V := Vl.hP v hvV
  have nxV : L.mem s (P1.vNextA v) ≠ 0#u64 → L.mem s (P1.vNextA v) ∈ V := Vl.next v hvV
  have m4 : ∀ b, LW st V s b → b ≠ P1.vHeadA st s →
      (L.mem s (vPrevA v) ≠ 0#u64 → b ≠ P1.vNextA (L.mem s (vPrevA v))) →
      (L.mem s (P1.vNextA v) ≠ 0#u64 → b ≠ vPrevA (L.mem s (P1.vNextA v))) → L.mem s4 b = L.mem s b :=
    fun b hb h1 h2 h3 => (w4.mem_eq (hal b hb) (by
      rintro (⟨-, e⟩ | ⟨h, e⟩ | ⟨h, e⟩)
      · exact h1 e
      · exact h2 h e
      · exact h3 h e)).trans (k2 b hb)
  have hvl : v ∈ l := (hm v).2 hvV
  obtain ⟨l', hnd', hm', hs', hh'⟩ := VSeg.unlink (m := L.mem s) (m' := L.mem s4) hs hnd hvl
    (fun u hu huv hup => by
      have huV := (hm u).1 hu
      have f := hf u huV
      have e1 := lay_next_val f.2
      refine m4 _ (Or.inr ⟨u, huV, Or.inl rfl⟩)
        (fun e => by have := congrArg UScalar.val e; have := hhv u huV; omega) (fun h e => ?_) (fun h e => ?_)
      · have hw := pvV h
        have := congrArg UScalar.val e
        rw [lay_next_val (hf _ hw).2] at this
        exact vl_val_ne hup (by omega)
      · have hw := nxV h
        have := congrArg UScalar.val e
        rw [lay_prev_val (hf _ hw).2] at this
        have := (hf _ hw).1
        omega)
    (fun u hu huv hun => by
      have huV := (hm u).1 hu
      have f := hf u huV
      have e1 := lay_prev_val f.2
      refine m4 _ (Or.inr ⟨u, huV, Or.inr rfl⟩)
        (fun e => by have := congrArg UScalar.val e; have := hhv u huV; omega) (fun h e => ?_) (fun h e => ?_)
      · have hw := pvV h
        have := congrArg UScalar.val e
        rw [lay_next_val (hf _ hw).2] at this
        have := (hf _ hw).1
        omega
      · have hw := nxV h
        have := congrArg UScalar.val e
        rw [lay_prev_val (hf _ hw).2] at this
        exact vl_val_ne hun (by omega))
    vN vP
  have ea : P1.vHeadA st s4 = P1.vHeadA st s := by unfold P1.vHeadA; rw [w4.1, hk2]
  refine ⟨⟨l', hnd', fun w => ?_, ?_, hs'⟩, ?_⟩
  · simp only [Set.mem_diff, Set.mem_singleton_iff]; rw [hm', hm]
  · rw [ea, hh']
    by_cases hp0 : L.mem s (vPrevA v) = 0#u64
    · rw [if_pos hp0]; exact vH hp0
    · rw [if_neg hp0, ← hh]
      refine (w4.mem_eq Vl.hd.1 ?_).trans (k2 _ (Or.inl rfl))
      rintro (⟨h, -⟩ | ⟨h, e⟩ | ⟨h, e⟩)
      · exact hp0 h
      · have hw := pvV h
        have := congrArg UScalar.val e
        rw [lay_next_val (hf _ hw).2] at this
        have := hhv _ hw
        omega
      · have hw := nxV h
        have := congrArg UScalar.val e
        rw [lay_prev_val (hf _ hw).2] at this
        have := hhv _ hw
        omega
  · rw [ea]
    exact ⟨Vl.hd.1, fun h => Vl.hd.2.1 (jw_mono_V Set.diff_subset h), Vl.hd.2.2⟩

set_option maxHeartbeats 8000000 in
/-- **`vcpu.finalise` unlinks**: `vcpu_finalise_jvB`'s conclusion and `VList (V \ {v})` (module docstring;
`hnd`, `hhv`, `hhc` [J]). -/
theorem vcpu_finalise_vl (hA : P0.ArchTotal ar) (Ly : JVLay V th U) {s : S} (Da : DetAtB st V th (fun _ => U) s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s)) (a : A) {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a v ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) th r.1 ⦄ := by
  have D := Ly.detPl
  have F : FinPl st V th (fun _ => U) s v := Ly.finPlV Vl hvV hnd
  have P := D.pl
  have hf := Ly.vfit
  have JWb : JW V th (vTcbA v) := Or.inr (Or.inr ⟨v, hvV, rfl⟩)
  unfold vcpu.finalise
  refine WP.spec_bind (vcpu_stall_w hA s a v Da.ipiA_al) ?_
  rintro ⟨s1, a1⟩ w1
  try simp only [uncurry_apply_pair]
  have w1' : P1.WritesIn st s s1 (· = ipiA st s) := w1
  have cl1 : ∀ b, b = ipiA st s → ¬ JW V th b ∧ ¬ SW th b := fun b e => Da.nd b (Or.inl e)
  have E1 := E.of_writes P w1' fun b hb => (cl1 b hb).1
  have R1 := R.of_clean P w1' cl1
  have Da1 : DetAtB st V th (fun _ => U) s1 := Da.mono (w1'.mono fun b e => Or.inr (Or.inl e))
  refine WP.spec_bind (hA.vcpu_release a1 v) fun a2 _ => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (P1.LawfulStore.read_spec s1 _) fun t et => ?_
  refine WP.spec_bind (P1.obj.Tcb.is_null.spec t) fun b eb => ?_
  have et' : t = L.mem s1 (vTcbA v) := et
  refine WP.spec_bind (Pₘ := fun r : S × A => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ P1.WritesIn st s r.1 (fun b => JW V th b ∨ CW st V th (fun _ => U) s b)) ?_ ?_
  · have w1J : P1.WritesIn st s s1 (fun b => JW V th b ∨ CW st V th (fun _ => U) s b) :=
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
      have Pd' : DetPost st V X th (fun _ => U) t s1 r.1 := Pd
      exact ⟨Pd'.ext, Pd'.rvm, Pd'.b0 v hvV htv, (w1J.trans (Pd'.footJ htt fun _ => by
        rw [htv]; exact hvV)).mono fun b h => h.elim id fun h' => h'.elim Or.inl fun c => Or.inr (CW.of w1' c)⟩
  rintro ⟨s2, a3⟩ ⟨E2, R2, b2, w2⟩
  try simp only [uncurry_apply_pair]
  have k2 : ∀ b, LW st V s b → L.mem s2 b = L.mem s b := by
    intro b hb
    rcases hb with e | ⟨w, hw, e | e⟩
    · rw [e]; exact w2.mem_eq Vl.hd.1 fun h => h.elim Vl.hd.2.1 hhc
    · have o := Ly.finOwn (b := b) hw hnd (Or.inl (by rw [e]; exact lay_next_val (hf w hw).2))
      exact w2.mem_eq o.1 fun h => h.elim o.2.1 o.2.2
    · have o := Ly.finOwn (b := b) hw hnd (Or.inr (by rw [e]; exact lay_prev_val (hf w hw).2))
      exact w2.mem_eq o.1 fun h => h.elim o.2.1 o.2.2
  refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun pv ep => ?_
  refine WP.spec_bind (P1.LawfulStore.read_spec s2 _) fun nx en => ?_
  have ep' : pv = L.mem s (vPrevA v) := ep.trans (k2 _ (Or.inr ⟨v, hvV, Or.inr rfl⟩))
  have en' : nx = L.mem s (P1.vNextA v) := en.trans (k2 _ (Or.inr ⟨v, hvV, Or.inl rfl⟩))
  subst ep' en'
  have hhd : P1.vHeadA st s2 = P1.vHeadA st s := by unfold P1.vHeadA; rw [w2.1]
  have pvV : L.mem s (vPrevA v) ≠ 0#u64 → L.mem s (vPrevA v) ∈ V := Vl.hP v hvV
  have nxV : L.mem s (P1.vNextA v) ≠ 0#u64 → L.mem s (P1.vNextA v) ∈ V := Vl.next v hvV
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s2 s3 (fun b =>
      (L.mem s (vPrevA v) = 0#u64 ∧ b = P1.vHeadA st s) ∨
      (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v)))) ∧
      (L.mem s (vPrevA v) = 0#u64 → L.mem s3 (P1.vHeadA st s) = L.mem s (P1.vNextA v)) ∧
      (L.mem s (vPrevA v) ≠ 0#u64 → L.mem s3 (P1.vNextA (L.mem s (vPrevA v))) = L.mem s (P1.vNextA v))) ?_
    fun s3 ⟨w3, v3a, v3b⟩ => ?_
  · split
    · rename_i hp0
      refine WP.spec_mono (P1.obj.ks_set.spec s2 _ _) fun s3 e3 => ?_
      subst e3
      have ea : core.num.U64.wrapping_add (L.ksb s2) layout.ks.VCPU_HEAD = P1.vHeadA st s := hhd
      rw [ea]
      exact ⟨(P1.writesIn_wr Vl.hd.1).mono fun b e => Or.inl ⟨hp0, e⟩, fun _ => L.mem_wr_same Vl.hd.1,
        fun h => absurd hp0 h⟩
    · rename_i hp0
      have al := (F.nbr _ (Or.inr (Or.inl ⟨hp0, rfl⟩))).1
      unfold vcpu.set
      simp only [lift, bind_ok]
      refine WP.spec_mono (P1.LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
      subst e3
      have ea : core.num.U64.wrapping_add (L.mem s (vPrevA v)) vcpu.NEXT = P1.vNextA (L.mem s (vPrevA v)) := rfl
      rw [ea]
      exact ⟨(P1.writesIn_wr al).mono fun b e => Or.inr ⟨hp0, e⟩, fun h => absurd h hp0,
        fun _ => L.mem_wr_same al⟩
  have FIN : ∀ s4, P1.WritesIn st s2 s4 (fun b => (L.mem s (vPrevA v) = 0#u64 ∧ b = P1.vHeadA st s) ∨
      (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v))) ∨
      (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))) →
      (L.mem s (vPrevA v) = 0#u64 → L.mem s4 (P1.vHeadA st s) = L.mem s (P1.vNextA v)) →
      (L.mem s (vPrevA v) ≠ 0#u64 → L.mem s4 (P1.vNextA (L.mem s (vPrevA v))) = L.mem s (P1.vNextA v)) →
      (L.mem s (P1.vNextA v) ≠ 0#u64 → L.mem s4 (vPrevA (L.mem s (P1.vNextA v))) = L.mem s (vPrevA v)) →
      JExtV (L := L) V X th s4 ∧ RunVmB (L := L) th s4 ∧ L.mem s4 (vTcbA v) = 0#u64 ∧
        VList st (V \ {v}) th s4 := fun s4 w4 vH vN vP => by
    have hd : ∀ b, ((L.mem s (vPrevA v) = 0#u64 ∧ b = P1.vHeadA st s) ∨
        (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v))) ∨
        (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))) → ¬ JW V th b ∧ ¬ SW th b := by
      rintro b (⟨-, e⟩ | h | h)
      · exact (F.nbr b (Or.inl e)).2
      · exact (F.nbr b (Or.inr (Or.inl h))).2
      · exact (F.nbr b (Or.inr (Or.inr h))).2
    exact ⟨E2.of_writes P w4 fun b h => (hd b h).1, R2.of_clean P w4 hd,
      by rw [w4.mem_eq (P.jw _ JWb) fun h => (hd _ h).1 JWb]; exact b2,
      vlist_unlink Vl hf Ly.vv hhv hvV k2 w2.1 w4 vH vN vP⟩
  split
  · rename_i hn0
    have hn : L.mem s (P1.vNextA v) ≠ 0#u64 := by simpa using hn0
    have hw := nxV hn
    have al := (F.nbr _ (Or.inr (Or.inr ⟨hn, rfl⟩))).1
    have epn := lay_prev_val (hf _ hw).2
    have fn := (hf _ hw).1
    unfold vcpu.set
    simp only [lift, bind_ok]
    refine WP.spec_bind (P1.LawfulStore.write_spec s3 _ _) fun s4 e4 => ?_
    subst e4
    have ea : core.num.U64.wrapping_add (L.mem s (P1.vNextA v)) vcpu.PREV = vPrevA (L.mem s (P1.vNextA v)) := rfl
    rw [ea]
    refine (WP.spec_ok _).2 (FIN _ ((w3.trans (P1.writesIn_wr al)).mono fun b h => ?_) ?_ ?_ ?_)
    · rcases h with h | e
      · rcases h with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨hn, e⟩)
    · intro hp0
      rw [L.mem_wr_ne al Vl.hd.1 (by have := hhv _ hw; omega)]; exact v3a hp0
    · intro hp0
      have hpw := pvV hp0
      have epp := lay_next_val (hf _ hpw).2
      have fp := (hf _ hpw).1
      rw [L.mem_wr_ne al (by unfold P1.Aligned; omega) (by omega)]; exact v3b hp0
    · intro _; exact L.mem_wr_same al
  · rename_i hn0
    have hn : L.mem s (P1.vNextA v) = 0#u64 := UScalar.eq_of_val_eq (by simpa using hn0)
    refine (WP.spec_ok _).2 (FIN _ (w3.mono fun b h => ?_) v3a v3b fun h => absurd hn h)
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end

/-! ## `hhc` / `hhv` / `hnd` at a joint state -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {ar : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

/-- The head word lies in no VCPU of `V` (`JVm.ks`: VCPUs off the kernel-global area). -/
theorem JAtZ.hhv (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val := by
  intro w hw
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  rcases Jv.ks w hw with e | e <;> omega

/-- **`hhc` at a joint state** from the one missing fact `hU` [J] (no IPC-buffer word is the head word): the
node words (`JKern.nodeFit` / base), the TCB words (`JKern.hks`: TCBs off the kernel-global area), the state words
(`VList.hd`) and the VCPU words (`JVm.ks`) are no head word. -/
theorem JAtZ.hhc (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    (Vl : VList st V Z.th s) (hU : P1.vHeadA st s ∉ BufU Z σ) :
    ¬ CW st V Z.th (fun _ => BufU Z σ) s (P1.vHeadA st s) := by
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  have hN := J.nodePl
  have hnb : L.nodeBase s (L.cpu s) = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 := rfl
  rintro (e | e | ⟨t, ht, hr | e⟩ | ⟨w, hw, e | e⟩)
  · have n1 := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
    have n2 := congrArg UScalar.val e
    unfold ipiA at n2
    omega
  · have n1 := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    have n2 := congrArg UScalar.val e
    unfold actA at n2
    omega
  · rcases hr with ⟨K, k1, k2, k3, e⟩ | hu
    · have Ly := J.jvLay Jv
      have e1 := congrArg UScalar.val e
      rw [lay_tw_val (Ly.tA t ht) (K := K) (by omega)] at e1
      have hT := J.kern.hks t .tcb (J.zH.1 t (J.thT t ht)) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at hT
      omega
    · exact hU hu
  · exact Vl.hd.2.2 ⟨t, ht, e⟩
  · have e1 := congrArg UScalar.val e
    rw [lay_pend_val ((J.jvLay Jv).vfit w hw).2] at e1
    rcases Jv.ks w hw with h | h <;> omega
  · have e1 := congrArg UScalar.val e
    rw [lay_svm_val ((J.jvLay Jv).vfit w hw).2] at e1
    rcases Jv.ks w hw with h | h <;> omega

/-- The current core's node words lie outside every VCPU of `V` (as in `JAtZ.finPl`). -/
theorem JAtZ.hnd (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val := by
  intro b hb w hw
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hN := J.nodePl
  have hb' : L.nodeBase s (L.cpu s) ≤ b.val ∧ b.val < L.nodeBase s (L.cpu s) + 4288 := by
    rcases hb with rfl | rfl
    · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
      have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
      unfold ipiA; rw [e]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
      have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
      unfold actA; rw [e]; omega
  rcases J.kern.hnd w _ (Jv.heap w hw) (L.cpu s) J.kern.cpuCs with e | e <;>
    (try simp only [P1.HKind.bits, h15] at e) <;> omega

/-- **`vcpu_finalise_vl` at a joint state**: only `hU` [J] (no IPC-buffer word is the head word) left. -/
theorem vcpu_finalise_vlJ (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s)
    (Vl : VList st V Z.th s) (hU : P1.vHeadA st s ∉ BufU Z σ) (a' : A) {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) Z.th r.1 ⦄ :=
  vcpu_finalise_vl hA (J.jvLay Jv) (J.detAtB Jv) E R Vl (J.hnd Jv) (J.hhv Jv) (J.hhc Jv Vl hU) a' hvV

end

end

end Fl4Proofs.P3
