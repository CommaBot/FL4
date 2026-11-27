/-
P3x for virtualization (line virt, gen 16, item 3): **`create_new_objects` over `n` VCPUs** — the loop of FL4's
`Retype` (objects.rs `create_new_objects`, extracted `objects.create_new_objects_loop`) for `X86Vcpu`, on top of
gen 15's per-object step (P3/VirtRetypeInit).

* `AgreeAtAL` (aligned words of the object except the links `NEXT` / `PREV`), `VcpuRelVmx.congrAL`,
  `VcpuRelSvm.congrAL`, `VRelInit.congrAL`: the next object's `init` rewrites the previous head's `PREV` word only.
* **`create_vcpu_listR`**: `create_arch_object … X86Vcpu v` gives `Cap.Vcpu v`, the arch state unchanged, `init`'s
  precise footprint (`InitL`), `VList (insert v V)` (mmuAD's `vcpu_init_vlist`) and `VRelInit` (gen 15's
  `create_vcpu_rel`) together — `create_vcpu_growLR` without its `JExtV` half.
* `vI B j`: the `j`-th new object `B + j·2^15`. `RInv`: the loop invariant at counter `i` — kernel base fixed,
  `VList` over `V` and the first `i` new objects, every one of them related (`VRelInit`), the rest of the window
  zero (`WinZero`), and the caller's companion invariant `M s i` (the capability-derivation side).
* **`vcpu_iter`**: one iteration (create + `insert_new_cap`) keeps `RInv`.
* **`create_new_objects_vcpu`**: the whole loop: after `objects.create_new_objects … X86Vcpu … n base …` the arch
  state is unchanged, `VList` lists `V` and all `n` new VCPUs, every new VCPU relates to `initVcpu virtKind`
  (`VRelInit`), and `M s' n` holds. With gen 15's `retype_vcpu_rel` each new object then relates (`VRelAt`) to the
  spec's state after `fl4InvokeUntypedV`'s hook, for the hook's address list containing it
  (**`create_new_objects_vcpu_rel`**).

The capability-derivation side (`insert_new_cap`'s MDB effects) is a parameter `M` of the theorem with two
obligations, not a premise: `hMc` (`M` survives a footprint inside the window, the VCPUs of `V` and the head word)
and `hIns` (`insert_new_cap` of the `i`-th cap keeps `M` up to `i + 1` and writes only words of a set `FW`). The
placement hypotheses (`hFW`: `FW` misses the window, the VCPUs of `V` and the head word; the window misses `V` and
the head word) are the retype's freshness facts, state hypotheses as in gen 15. Instantiating `M` with P3's
`LoopInv` (P3/UntypedLoop, `insert_new_frame`) is the next step.

Named premises: `CapAgree ar a` [P], `VirtCodeAgree ar a` [P] (unchanged). No new premise. New file only; no
existing statement changed.
-/
import Fl4Proofs.P3.VirtReplyKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtRetypeLoop
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtReplyKeep

noncomputable section

/-! ## Aligned agreement off the links -/

/-- Agreement on the aligned words of the VCPU object at `v` other than `NEXT` / `PREV`. -/
def AgreeAtAL (mem mem' : Word → Word) (v : Word) : Prop :=
  ∀ o, o < VcpuLay.SIZE → o.toNat % 8 = 0 → o ≠ 0x5008 → o ≠ 0x5010 → mem' (v + o) = mem (v + o)

theorem agAL {mem mem' : Word → Word} {v o : Word} (hm : AgreeAtAL mem mem' v) (h1 : o < VcpuLay.SIZE)
    (h2 : o.toNat % 8 = 0) (h3 : o ≠ 0x5008 ∧ o ≠ 0x5010) : mem' (v + o) = mem (v + o) := hm o h1 h2 h3.1 h3.2

theorem VcpuRelCommon.congrAL {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtAL mem mem' v)
    (h : VcpuRelCommon mem v vs) : VcpuRelCommon mem' v vs where
  tcb := by rw [agAL hm tcb_lt (by decide) (by decide)]; exact h.tcb
  valid := by rw [agAL hm valid_lt (by decide) (by decide)]; exact h.valid
  pending := by rw [agAL hm pending_lt (by decide) (by decide)]; exact h.pending
  mrs i := by
    have := exitOff_nat i
    rw [agAL hm (exitOff_lt i) (by omega) (ne_links_of_ge (exitOff_ge i))]; exact h.mrs i
  gpr i := by
    have := gprOff_nat i
    rw [agAL hm (gprOff_lt i) (by omega) (ne_links_of_ge (gprOff_ge i))]; exact h.gpr i
  xcr0 := by rw [agAL hm xcr0_lt (by decide) (by decide)]; exact h.xcr0
  ibpb := by rw [agAL hm ibpb_lt (by decide) (by decide)]; exact h.ibpb

theorem VcpuRelVmx.congrAL {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtAL mem mem' v)
    (h : VcpuRelVmx mem v vs) : VcpuRelVmx mem' v vs :=
  { VcpuRelCommon.congrAL hm h.toVcpuRelCommon with
    vmcs := fun f hf => by
      rw [agAL hm (vmcsOff_lt hf) (vmcsOff_nat f).2 (ne_links_of_lt (VirtRetypeInit.vmcsOff_lt_tcb f))]; exact h.vmcs f hf
    msr := fun m i hi => by
      rw [agAL hm (msrOff_lt hi) (msrOff_cases (msrOff_of_slot hi)).2.2.1 (ne_links_of_ge (msrOff_ge hi))]
      exact h.msr m i hi
    cr2 := by rw [agAL hm cr2_lt (by decide) (by decide)]; exact h.cr2
    io := fun p => by
      rw [agAL hm (ioOff_lt p) (ioOff_nat p).2.2 (ne_links_of_ge (ioOff_ge p))]; exact h.io p }

theorem VcpuRelSvm.congrAL {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtAL mem mem' v)
    (h : VcpuRelSvm mem v vs) : VcpuRelSvm mem' v vs :=
  { VcpuRelCommon.congrAL hm h.toVcpuRelCommon with
    vmcb := fun off hr hh hx => by
      rw [agAL hm (svmOff_lt hr) (readable_nat hr).1 (ne_links_of_lt (svmOff_lt5 hr))]; exact h.vmcb off hr hh hx }

theorem VRelInit.congrAL {mem mem' : Word → Word} {v : Word} (hm : AgreeAtAL mem mem' v) (h : VRelInit mem v) :
    VRelInit mem' v :=
  ⟨fun e => VcpuRelSvm.congrAL hm (h.1 e), fun e => VcpuRelVmx.congrAL hm (h.2 e)⟩

theorem size_nat {o : Word} (h : o < VcpuLay.SIZE) : o.toNat < 32768 := by
  have : VcpuLay.SIZE.toNat = 32768 := rfl
  rw [BitVec.lt_def, this] at h; exact h

theorem links_nat {o : Word} (h : o ≠ 0x5008 ∧ o ≠ 0x5010) : o.toNat ≠ 20488 ∧ o.toNat ≠ 20496 :=
  ⟨fun e => h.1 (BitVec.eq_of_toNat_eq (by rw [e]; rfl)), fun e => h.2 (BitVec.eq_of_toNat_eq (by rw [e]; rfl))⟩

/-! ## One VCPU: list and relation -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

set_option maxHeartbeats 4000000 in
/-- **One VCPU creation: list, footprint and relation** (module docstring). -/
theorem create_vcpu_listR (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {s : S}
    (Vl : VList st V th s) (hf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64)
    (hvv : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val)
    {v : U64} (hv : VFits v) (hv0 : v ≠ 0#u64) (hvV : v ∉ V)
    (hap : ∀ w ∈ V, w.val + 32768 ≤ v.val ∨ v.val + 32768 ≤ w.val)
    (hhv : ∀ w, w ∈ insert v V → (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    {A0 k win : Nat} (hwz : WinZero (L.mem s) A0 k win False) (hin : A0 ≤ v.val ∧ v.val + 32768 ≤ A0 + win * k)
    (hko : vTcbA v ≠ P1.vHeadA st s) (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ r.2.2 = a ∧ P1.WritesIn st s r.2.1 (InitL st s v) ∧
        VList st (insert v V) th r.2.1 ∧ VRelInit (memW st r.2.1) v.bv ⦄ := by
  have hzv := vzero_of_win hwz hin
  have hv2 := hv.2
  have hv1 := hv.1
  have hz : L.mem s (vPrevA v) = 0#u64 := by
    have e := lay_prev_val hv2
    exact hzv _ (by unfold P1.Aligned; rw [e]; omega) (by rw [e]; omega) (by rw [e]; omega)
  have hl := initListOut_of Vl hf hap (hhv v (Set.mem_insert v V))
  have h1 : objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu v dev ⦃ r =>
      r.1 = capability.Cap.Vcpu v ∧ r.2.2 = a ∧ P1.WritesIn st s r.2.1 (InitL st s v) ∧
        VList st (insert v V) th r.2.1 ⦄ := by
    unfold objects.create_arch_object
    rw [if_pos rfl]
    exact WP.spec_bind (vcpu_init_vlist hA a Vl hf hvv hv hv0 hvV hap hhv hz (fun _ h => h) (fun _ h => h) hko)
      fun s1 h => (WP.spec_ok _).2 ⟨rfl, rfl, h.1, h.2⟩
  refine WP.spec_mono (spec_and2 h1 (create_vcpu_rel hc hk hv hzv hl dev)) ?_
  rintro r ⟨⟨e1, e2, e3, e4⟩, -, e5⟩
  exact ⟨e1, e2, e3, e4, e5⟩

end

/-! ## The loop -/

/-- The `j`-th new object of a VCPU retype at `B`. -/
def vI (B j : Nat) : U64 := ⟨BitVec.ofNat 64 (B + j * 32768)⟩

theorem vI_val {B j : Nat} (h : B + j * 32768 < 2 ^ 64) : (vI B j).val = B + j * 32768 := by
  show (BitVec.ofNat 64 (B + j * 32768)).toNat = _
  simp only [BitVec.toNat_ofNat]; omega

/-- The VCPUs after `i` iterations: `V` and the first `i` new objects. -/
def VsI (V : Set U64) (B i : Nat) : Set U64 := {w | w ∈ V ∨ ∃ j, j < i ∧ w = vI B j}

theorem vsI_succ (V : Set U64) (B i : Nat) : insert (vI B i) (VsI V B i) = VsI V B (i + 1) := by
  ext w
  simp only [VsI, Set.mem_insert_iff, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | h | ⟨j, hj, rfl⟩)
    · exact Or.inr ⟨i, by omega, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, by omega, rfl⟩
  · rintro (h | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl h)
    · by_cases e : j = i
      · subst e; exact Or.inl rfl
      · exact Or.inr (Or.inr ⟨j, by omega, rfl⟩)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap}

/-- The static placement of a VCPU retype of `n` objects at `B` (the retype's freshness; state hypotheses). -/
structure RPl (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (B n : Nat) (hd : U64) : Prop where
  bal : B % 32768 = 0
  b0 : 0 < B
  bfit : B + n * 32768 < 2 ^ 64
  vf : ∀ w ∈ V, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64
  vv : ∀ w ∈ V, ∀ w' ∈ V, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val
  vw : ∀ w ∈ V, w.val + 32768 ≤ B ∨ B + n * 32768 ≤ w.val
  hv : ∀ w ∈ V, hd.val < w.val ∨ w.val + 32768 ≤ hd.val
  hw : hd.val + 8 ≤ B ∨ B + n * 32768 ≤ hd.val

/-- **The loop invariant** (module docstring). -/
structure RInv (st : machine.Store S) [L : P1.LawfulStore st] (V : Set U64) (th : TypedHeap) (B n : Nat)
    (k0 : U64) (M : S → Nat → Prop) (s : S) (i : Nat) : Prop where
  ksb : L.ksb s = k0
  vl : VList st (VsI V B i) th s
  rel : ∀ j, j < i → VRelInit (memW st s) (vI B j).bv
  win : WinZero (L.mem s) (B + i * 32768) 32768 (n - i) False
  m : M s i

theorem hd_of_ksb {s s' : S} (h : L.ksb s' = L.ksb s) : P1.vHeadA st s' = P1.vHeadA st s := by
  unfold P1.vHeadA; rw [h]

section
variable {B n : Nat} {hd : U64} (R : RPl st V B n hd)
include R

theorem RPl.vIv {j : Nat} (hj : j < n) : (vI B j).val = B + j * 32768 := by
  exact vI_val (B := B) (j := j) (lt_of_le_of_lt (by omega) R.bfit)

theorem RPl.vIfit {j : Nat} (hj : j < n) : VFits (vI B j) := by
  have e := R.vIv hj; have := R.bal; have := R.bfit
  exact ⟨by rw [e]; omega, by rw [e]; omega⟩

/-- Every VCPU after `i ≤ n` iterations fits; two of them are apart. -/
theorem RPl.fitI {i : Nat} (hi : i ≤ n) : ∀ w ∈ VsI V B i, w.val % 32768 = 0 ∧ w.val + 32768 ≤ 2 ^ 64 := by
  rintro w (h | ⟨j, hj, rfl⟩)
  · exact R.vf w h
  · exact R.vIfit (by omega)

theorem RPl.memI {i : Nat} (hi : i ≤ n) {w : U64} (hw : w ∈ VsI V B i) :
    (w ∈ V ∧ (w.val + 32768 ≤ B ∨ B + n * 32768 ≤ w.val)) ∨ ∃ j, j < i ∧ w.val = B + j * 32768 := by
  rcases hw with h | ⟨j, hj, rfl⟩
  · exact Or.inl ⟨h, R.vw w h⟩
  · exact Or.inr ⟨j, hj, R.vIv (by omega)⟩

theorem RPl.apI {i : Nat} (hi : i ≤ n) :
    ∀ w ∈ VsI V B i, ∀ w' ∈ VsI V B i, w ≠ w' → w.val + 32768 ≤ w'.val ∨ w'.val + 32768 ≤ w.val := by
  intro w hw w' hw' hne
  have hne' : w.val ≠ w'.val := fun e => hne (UScalar.eq_of_val_eq e)
  rcases hw with h | ⟨j, hj, rfl⟩ <;> rcases hw' with h' | ⟨j', hj', rfl⟩
  · exact R.vv w h w' h' hne
  · have := R.vw w h; have := R.vIv (j := j') (by omega); omega
  · have := R.vw w' h'; have := R.vIv (j := j) (by omega); omega
  · have e1 := R.vIv (j := j) (by omega); have e2 := R.vIv (j := j') (by omega)
    rw [e1, e2] at hne' ⊢
    have : j ≠ j' := fun e => hne' (by rw [e])
    rcases Nat.lt_or_gt_of_ne this with h | h
    · left; have : j * 32768 + 32768 ≤ j' * 32768 := by nlinarith
      omega
    · right; have : j' * 32768 + 32768 ≤ j * 32768 := by nlinarith
      omega

theorem RPl.hdI {i : Nat} (hi : i ≤ n) : ∀ w ∈ VsI V B i, hd.val < w.val ∨ w.val + 32768 ≤ hd.val := by
  rintro w (h | ⟨j, hj, rfl⟩)
  · exact R.hv w h
  · have := R.vIv (j := j) (by omega); have := R.hw
    have : j * 32768 + 32768 ≤ n * 32768 := by nlinarith
    omega

end

theorem winZero_shift {m m' : U64 → U64} {A0 k win : Nat} (h : WinZero m A0 k (win + 1) False)
    (hk : k = 32768) (hm : ∀ w : U64, P1.Aligned w → A0 + k ≤ w.val → w.val < A0 + (win + 1) * k → m' w = m w) :
    WinZero m' (A0 + k) k win False := by
  intro w hw h1 h2
  subst hk
  have h2' : w.val < A0 + (win + 1) * 32768 := by
    have : (win + 1) * 32768 = win * 32768 + 32768 := by ring
    omega
  rw [hm w hw h1 h2']
  exact Or.inl ((h w hw (by omega) h2').resolve_right fun h => h.1)

/-- The words `vcpu::init` may write during a VCPU retype: the window, the head word, the VCPUs of `V`. -/
def CrW (V : Set U64) (B n : Nat) (hd : U64) (b : U64) : Prop :=
  (B ≤ b.val ∧ b.val < B + n * 32768) ∨ b = hd ∨ ∃ w ∈ V, w.val ≤ b.val ∧ b.val < w.val + 32768

set_option maxHeartbeats 8000000 in
/-- **The creation half of one iteration** (module docstring). -/
theorem iter_create (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {B n : Nat} {hd k0 : U64}
    (R : RPl st V B n hd) (hhd : ∀ s : S, L.ksb s = k0 → P1.vHeadA st s = hd) (M : S → Nat → Prop)
    (hMc : ∀ s s' i, M s i → P1.WritesIn st s s' (CrW V B n hd) → M s' i)
    {s : S} {i : Nat} (hi : i < n) (I : RInv st V th B n k0 M s i) (dev : Bool) :
    objects.create_arch_object st ar s a fl4_abi.consts.object.X86Vcpu (vI B i) dev ⦃ r =>
      r.1 = capability.Cap.Vcpu (vI B i) ∧ r.2.2 = a ∧
        RInv st V th B n k0 (fun s' _ => M s' i) r.2.1 (i + 1) ⦄ := by
  have hiN : i ≤ n := Nat.le_of_lt hi
  have ev := R.vIv hi
  have hv := R.vIfit hi
  have hb0 := R.b0
  have hbw := R.hw
  have eh : P1.vHeadA st s = hd := hhd s I.ksb
  have hv0 : vI B i ≠ 0#u64 := fun e => by
    have := congrArg UScalar.val e; rw [ev] at this; simp at this; omega
  have hvV : vI B i ∉ VsI V B i := by
    rintro (h | ⟨j, hj, e⟩)
    · have := R.vw _ h; omega
    · have := congrArg UScalar.val e; rw [ev, R.vIv (by omega)] at this; omega
  have hvI : vI B i ∈ VsI V B (i + 1) := Or.inr ⟨i, by omega, rfl⟩
  have hap : ∀ w ∈ VsI V B i, w.val + 32768 ≤ (vI B i).val ∨ (vI B i).val + 32768 ≤ w.val := by
    intro w hw
    have hw' : w ∈ VsI V B (i + 1) := by rw [← vsI_succ]; exact Set.mem_insert_of_mem _ hw
    have hne : w ≠ vI B i := fun e => hvV (e ▸ hw)
    exact R.apI hi w hw' _ hvI hne
  have hhv : ∀ w, w ∈ insert (vI B i) (VsI V B i) →
      (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val := by
    intro w hw; rw [vsI_succ] at hw; rw [eh]; exact R.hdI hi w hw
  have hin : B + i * 32768 ≤ (vI B i).val ∧ (vI B i).val + 32768 ≤ B + i * 32768 + (n - i) * 32768 := by
    rw [ev]; omega
  have hko : vTcbA (vI B i) ≠ P1.vHeadA st s := by
    intro e; have := congrArg UScalar.val e; rw [lay_vTcb_val hv.2, eh, ev] at this; omega
  refine WP.spec_mono (create_vcpu_listR hA hc hk I.vl (R.fitI hiN) (R.apI hiN) hv hv0 hvV hap hhv I.win hin hko
    dev) ?_
  rintro ⟨cap, s2, a2⟩ ⟨e1, e2, w, Vl', hrel⟩
  simp only at e1 e2 w Vl' hrel ⊢
  refine ⟨e1, e2, ?_⟩
  have hk2 : L.ksb s2 = k0 := w.1.trans I.ksb
  -- `InitL`'s words: in the new object, the head word, or the old head's `PREV` word
  have hIL : ∀ b, InitL st s (vI B i) b → (B + i * 32768 ≤ b.val ∧ b.val < B + (i + 1) * 32768) ∨ b = hd ∨
      ∃ h0 ∈ VsI V B i, b.val = h0.val + 20496 ∧ h0.val + 32768 ≤ 2 ^ 64 := by
    rintro b (h | e | e | ⟨hn, e⟩)
    · have := vwl_val hv h; rw [ev] at this; left; omega
    · have := congrArg UScalar.val e; rw [lay_next_val hv.2, ev] at this; left; omega
    · right; left; rw [e, eh]
    · right; right
      have hw := I.vl.head hn
      have hf := (R.fitI hiN) _ hw
      exact ⟨_, hw, by rw [e, lay_prev_val hf.2], hf.2⟩
  refine ⟨hk2, vsI_succ V B i ▸ Vl', fun j hj => ?_, ?_, ?_⟩
  · by_cases hji : j = i
    · subst hji; exact hrel
    have hj' : j < i := by omega
    have hvj := R.vIfit (j := j) (by omega)
    have evj := R.vIv (j := j) (by omega)
    refine VRelInit.congrAL (fun o h1 h2 h3 h4 => ?_) (I.rel j hj')
    have ho := size_nat h1
    have hl := links_nat ⟨h3, h4⟩
    have hval := vo_val hvj ho
    have hal : P1.Aligned (⟨(vI B j).bv + o⟩ : U64) := by unfold P1.Aligned; rw [hval]; have := hvj.1; omega
    unfold memW
    rw [w.mem_eq hal ?_]
    intro hb
    rcases hIL _ hb with h | e | ⟨h0, hh0, e, -⟩
    · rw [hval, evj] at h; omega
    · have := congrArg UScalar.val e; rw [hval, evj] at this; omega
    · rw [hval, evj] at e
      rcases R.memI hiN hh0 with ⟨-, h'⟩ | ⟨j', hj'', e'⟩
      · omega
      · omega
  · have e1 : n - i = n - (i + 1) + 1 := by omega
    have hw0 := I.win
    rw [e1] at hw0
    have := winZero_shift hw0 rfl fun x hx g1 g2 => w.mem_eq hx fun hb => by
      rcases hIL _ hb with h | e | ⟨h0, hh0, e, -⟩
      · omega
      · rw [e] at g1 g2; omega
      · rcases R.memI hiN hh0 with ⟨-, h'⟩ | ⟨j', hj'', e'⟩
        · have : (n - (i + 1) + 1) * 32768 = (n - i) * 32768 := by rw [← e1]
          omega
        · omega
    rwa [show B + i * 32768 + 32768 = B + (i + 1) * 32768 by ring] at this
  · exact hMc s s2 i I.m (w.mono fun b hb => by
      rcases hIL _ hb with h | e | ⟨h0, hh0, e, -⟩
      · left; omega
      · right; left; exact e
      · rcases R.memI hiN hh0 with ⟨hm, -⟩ | ⟨j', hj'', e'⟩
        · right; right; exact ⟨h0, hm, by omega, by omega⟩
        · left; omega)

/-- **The `insert_new_cap` half of one iteration** (module docstring). -/
theorem iter_ins {B n : Nat} {hd k0 : U64} (R : RPl st V B n hd) (hhd : ∀ s : S, L.ksb s = k0 → P1.vHeadA st s = hd)
    (M : S → Nat → Prop) {FW : U64 → Prop}
    (hFW : ∀ b, FW b → (b.val + 8 ≤ B ∨ B + n * 32768 ≤ b.val) ∧ b ≠ hd ∧
      ∀ w ∈ V, b.val + 8 ≤ w.val ∨ w.val + 32768 ≤ b.val)
    {s2 s3 : S} {i : Nat} (hi : i < n) (I : RInv st V th B n k0 (fun s' _ => M s' i) s2 (i + 1))
    (hM : M s3 (i + 1)) (hW : P1.WritesIn st s2 s3 FW) : RInv st V th B n k0 M s3 (i + 1) := by
  have hiN : i + 1 ≤ n := hi
  have hbw := R.hw
  refine ⟨hW.1.trans I.ksb, ?_, fun j hj => ?_, fun x hx g1 g2 => ?_, hM⟩
  · refine I.vl.writes hW fun b hb => ⟨I.vl.lw_al (R.fitI hiN) hb, fun hf => ?_⟩
    obtain ⟨f1, f2, f3⟩ := hFW b hf
    rcases hb with e | ⟨w, hw, e | e⟩
    · exact f2 (e.trans (hhd s2 I.ksb))
    all_goals
      have hfw := (R.fitI hiN) w hw
      have := congrArg UScalar.val e
      first | rw [lay_next_val hfw.2] at this | rw [lay_prev_val hfw.2] at this
      rcases R.memI hiN hw with ⟨hm, -⟩ | ⟨j', hj', e'⟩
      · have := f3 w hm; omega
      · omega
  · have hvj := R.vIfit (j := j) (by omega)
    have evj := R.vIv (j := j) (by omega)
    refine VRelInit.congrA (fun o h1 _ => ?_) (I.rel j hj)
    have ho := size_nat h1
    have hval := vo_val hvj ho
    have hal : P1.Aligned (⟨(vI B j).bv + o⟩ : U64) := by unfold P1.Aligned; rw [hval]; have := hvj.1; omega
    unfold memW
    rw [hW.mem_eq hal fun hf => by have := (hFW _ hf).1; rw [hval, evj] at this; omega]
  · rw [hW.mem_eq hx fun hf => by have := (hFW _ hf).1; omega]
    exact I.win x hx g1 g2

theorem object_size_vcpu (us : U64) : objects.object_size fl4_abi.consts.object.X86Vcpu us = ok (some 15#u64) := by
  unfold objects.object_size; rw [if_pos rfl]; simp [fl4_abi.consts.bits.VCPU]

set_option maxHeartbeats 8000000 in
/-- **`create_new_objects` over `n` VCPUs** (module docstring). -/
theorem create_new_objects_vcpu (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a) {B n : Nat}
    {hd : U64} (R : RPl st V B n hd) {s : S} (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (M : S → Nat → Prop) (hMc : ∀ s s' i, M s i → P1.WritesIn st s s' (CrW V B n hd) → M s' i)
    {FW : U64 → Prop} (hFW : ∀ b, FW b → (b.val + 8 ≤ B ∨ B + n * 32768 ≤ b.val) ∧ b ≠ hd ∧
      ∀ w ∈ V, b.val + 8 ≤ w.val ∨ w.val + 32768 ≤ b.val)
    (parent dest off : U64) (hIns : ∀ iw : U64, iw.val < n → ∀ s2, M s2 iw.val →
      cdt.insert_new_cap st s2 parent (slotAddr dest.bv (core.num.U64.wrapping_add off iw).bv)
        (capability.Cap.Vcpu (vI B iw.val)) ⦃ s3 => M s3 (iw.val + 1) ∧ P1.WritesIn st s2 s3 FW ⦄)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False) (hM0 : M s 0)
    (nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu parent dest off nW base us dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧ (∀ j, j < n → VRelInit (memW st res.1) (vI B j).bv) ∧
        M res.1 n ⦄ := by
  have hbf := R.bfit
  have I0 : RInv st V th B n (L.ksb s) M s 0 := by
    refine ⟨rfl, ?_, fun j hj => absurd hj (Nat.not_lt_zero _), by simpa using hwz, hM0⟩
    have e : VsI V B 0 = V := by
      ext w; simp only [VsI, Set.mem_setOf_eq]
      exact ⟨fun h => h.elim id fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _), Or.inl⟩
    rw [e]; exact Vl
  unfold objects.create_new_objects
  rw [object_size_vcpu]
  simp only [bind_ok]
  unfold objects.create_new_objects_loop
  have h63 : (15#u64 &&& 63#u64).val = 15 := by decide
  refine loop.spec_decr_nat (measure := fun x => n - x.2.2.val)
    (inv := fun x => x.2.1 = a ∧ x.2.2.val ≤ n ∧ RInv st V th B n (L.ksb s) M x.1 x.2.2.val) _ _ _ ?_
    ⟨rfl, by simp, I0⟩
  rintro ⟨s1, a1, i⟩ ⟨ha, hin, I⟩
  simp only at ha hin I ⊢
  subst ha
  unfold objects.create_new_objects_loop.body
  by_cases hit : i < nW
  · rw [if_pos hit]
    have hit' : i.val < n := by rw [← hnW]; exact hit
    simp only [lift, bind_ok]
    obtain ⟨i2, hi2, hv2, -⟩ := spec_exists (UScalar.ShiftLeft_spec i (15#u64 &&& 63#u64) _
      (by rw [h63]; simp [UScalarTy.U64_numBits_eq]) rfl)
    rw [hi2]; simp only [bind_ok]
    have hi2v : i2.val = i.val * 32768 := by
      rw [hv2, h63, Nat.shiftLeft_eq]
      simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
    have hi3 : core.num.U64.wrapping_add base i2 = vI B i.val := by
      have e : (core.num.U64.wrapping_add base i2).val = B + i.val * 32768 := by
        have hlt : B + i.val * 32768 < 2 ^ 64 := lt_of_le_of_lt (by omega) hbf
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hi2v]
        omega
      exact u64_ofNat_eq _ _ e
    rw [hi3, create_object_vcpu]
    refine WP.spec_bind (iter_create hA hc hk R (fun s' e => hhd s' e) M hMc hit' I dev) fun r hr => ?_
    obtain ⟨cap, s2, a2⟩ := r
    obtain ⟨e1, e2, I'⟩ := hr
    simp only at e1 e2 I' ⊢
    subst e1 e2
    obtain ⟨sl, hsl, hsle⟩ := spec_exists (slot_index_spec dest (core.num.U64.wrapping_add off i))
    rw [hsl]; simp only [bind_ok]
    subst hsle
    refine WP.spec_bind (hIns i hit' s2 I'.m) fun s3 h3 => ?_
    step as ⟨i5, hi5⟩
    have hi5' : i5.val = i.val + 1 := by omega
    refine ⟨by omega, ?_, by omega⟩
    rw [hi5']
    exact iter_ins R (fun s' e => hhd s' e) M hFW hit' I' h3.1 h3.2
  · rw [if_neg hit, WP.spec_ok]
    have : i.val = n := by have : ¬ i.val < nW.val := hit; omega
    rw [this] at I
    exact ⟨rfl, I.vl, I.rel, I.m⟩

end

/-! ## Linked to the spec's retype hook -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A} {a : A}
variable {V : Set U64} {th : TypedHeap} {Z : Type}

set_option maxHeartbeats 4000000 in
/-- **The VCPU retype loop, related to the spec** (module docstring): every new VCPU relates (`VRelAt`) to the
spec's state after `fl4InvokeUntypedV`'s hook for an address list containing it. -/
theorem create_new_objects_vcpu_rel (hA : P0.ArchTotal ar) (hc : CapAgree ar a) (hk : VirtCodeAgree ar a)
    {B n : Nat} {hd : U64} (R : RPl st V B n hd) {s : S} (hhd : ∀ s' : S, L.ksb s' = L.ksb s → P1.vHeadA st s' = hd)
    (M : S → Nat → Prop) (hMc : ∀ s s' i, M s i → P1.WritesIn st s s' (CrW V B n hd) → M s' i)
    {FW : U64 → Prop} (hFW : ∀ b, FW b → (b.val + 8 ≤ B ∨ B + n * 32768 ≤ b.val) ∧ b ≠ hd ∧
      ∀ w ∈ V, b.val + 8 ≤ w.val ∨ w.val + 32768 ≤ b.val)
    (parent dest off : U64) (hIns : ∀ iw : U64, iw.val < n → ∀ s2, M s2 iw.val →
      cdt.insert_new_cap st s2 parent (slotAddr dest.bv (core.num.U64.wrapping_add off iw).bv)
        (capability.Cap.Vcpu (vI B iw.val)) ⦃ s3 => M s3 (iw.val + 1) ∧ P1.WritesIn st s2 s3 FW ⦄)
    (Vl : VList st V th s) (hwz : WinZero (L.mem s) B 32768 n False) (hM0 : M s 0)
    (nW base us : U64) (hnW : nW.val = n) (hbase : base.val = B) (dev : Bool) :
    objects.create_new_objects st ar s a fl4_abi.consts.object.X86Vcpu parent dest off nW base us dev ⦃ res =>
      res.2 = a ∧ VList st (VsI V B n) th res.1 ∧ M res.1 n ∧
        ∀ j, j < n → ∀ (l : List ObjRef) (σ : State Z) (x : Unit × State Z),
          x ∈ (NonDet.mapMx (fun v => setVcpu (Z := Z) v (initVcpu virtKind)) l σ).1 → (vI B j).bv ∈ l →
          VRelAt (memW st res.1) x.2 (vI B j).bv ⦄ :=
  WP.spec_mono (create_new_objects_vcpu hA hc hk R hhd M hMc hFW parent dest off hIns Vl hwz hM0 nW base us hnW
    hbase dev) fun _ ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h4, fun j hj l σ x hx hm => retype_vcpu_rel (h3 j hj) l hx hm⟩

end

end
end Fl4Proofs.P3.VirtRetypeLoop
