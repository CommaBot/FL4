/-
P3x for virtualization (line virt, gen 23, item 1, second part): **`VCapped` across the deletion of a `Vcpu` cap**
(`cdt::delete`, either `exposed`), and the sharper footprint of `vcpu::finalise` it needs.

Is `VCapped` true on reachable states? Its only threat is a deletion that removes the *last* `Vcpu v` cap while `v`
stays listed. FL4 cannot do that: `finalise_slot_*` (cdt.rs l. 243-297) passes `fin = is_final_capability_with_cap`
(cdt.rs l. 163-175) to `finalise_cap`, whose `Vcpu` arm runs `vcpu::finalise` exactly when `fin` (objects.rs l. 265),
and `vcpu::finalise` unlinks `v` from the VCPU list (vcpu.rs l. 737-753). `fin = false` only when the slot's MDB
`prev` or `next` holds a cap `same_object_as` it, and for a `Vcpu v` cap that is `Vcpu v` itself (`soB_vcpu_left`,
`soB_vcpu_right`: objects.rs l. 137-152 / 123), which the deletion leaves in place. (A `Vcpu` cap finalises to a
`Null` remainder, so no zombie and no preemption point intervenes: `finImm_vcpu` / `finDef_vcpu`.) So no
counterexample: the invariant holds on this path, and this module proves it.

* `soB_vcpu_left`, `soB_vcpu_right`; **`isFinal_vcpu_false`** (a non-final `Vcpu v` cap has an MDB neighbour holding
  `Vcpu v`); `finCap_vcpu` (`finalise_cap (Vcpu v) fin`: remainder and cleanup `Null`, the state kept unless `fin`,
  then `vcpu.finalise`); `finImm_vcpu`, `finDef_vcpu`, **`delete_vcpu_ok`** (`cdt.delete` of a slot holding `Vcpu v`
  returns `Ok`: `is_final`, then `vcpu.finalise` iff final, then `empty_slot … Null`).
* **`vcpu_finalise_vlW`**: P3/JExtVListSteps' `vcpu_finalise_vl` (same hypotheses, same proof) with its write set
  exposed: `BW ∪ CW ∪ LW` (the binding words, the detach words, the list's link words).
* `SlR th b` (a word inside a slot of the typed heap), `slotsSame_of_writes`, `nSl_v`, `nSl_t`,
  **`finW_nSl`** (no word of that write set lies in a slot), so `vcpu.finalise` keeps every slot (`SlotsSame`).
* **`delete_vcpu_vcapped`**: from `VCappedM V` and the layout / list facts, every `Ok` outcome of `cdt.delete` on a
  slot holding `Vcpu v` has some `V' ⊆ V` (`V \ {v}` when the cap was final, `V` otherwise) with **`VList V'`** and
  **`VCappedM V'`** after.

Named premise: **`hns` [J]** (`delete_vcpu_vcapped`, `finW_nSl`): the current core's node words `ipiA` / `actA` and the
VCPU list's head word lie in no slot of the typed heap. Justification: they are kernel-global words (the per-core node
block at `ksb + 13568 + cpu * 4288` and the KS block's `VCPU_HEAD` at `ksb + 80`, fl4-core layout.rs `ks` / `node`),
in the kernel's own image, never inside an untyped-retyped CNode or TCB object; it is the slot analogue of
`vcpu_finalise_vl`'s `hnd` [J] / `hhv` [J] (node / head words off the VCPUs) and is derived the same way at a joint
state (`JKern.hks` / `JKern.hnd`: typed-heap objects off the kernel-global area, as `JAtZ.hnd` / `JAtZ.hhv`). True on
every reachable state (the typed heap only grows by retypes from untyped memory, which never covers the kernel image).
Used unchanged: `vcpu_finalise_vl`'s `hnd`, `hhv`, `hhc` [J] (as hypotheses of `vcpu_finalise_vlW`, the same
statement shape). The slot-placement hypothesis `hSV`-style facts are not needed here (the VCPU-side words are placed by
`JVLay`). No [P]/[W]. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVCapped
import Fl4Proofs.P3.JExtVListSteps
import Fl4Proofs.P3.CnFrame
import Fl4Proofs.P3.EmptyRefine
import Fl4Proofs.P3.MdbRename
import Fl4Proofs.P3.FinDefs
import Fl4Proofs.P3.Restart
import Fl4Proofs.P3.StateFrame
import Fl4Proofs.P3.MdbInv
import Fl4Proofs.P3.JExtVLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVCappedDel
open fl4_core Classical Fl4Proofs.P0.Consts Fl4Proofs.P3 Fl4Proofs.P3.VirtVCapped

noncomputable section

/-! ## `same_object_as` on a `Vcpu` cap -/

theorem soB_vcpu_eq (v : U64) (b : capability.Cap) : soB (.Vcpu v) b = srB (.Vcpu v) b := by
  cases b <;> rfl

theorem soB_vcpu_left {v : U64} {b : capability.Cap} (h : soB (.Vcpu v) b = true) : b = .Vcpu v := by
  rw [soB_vcpu_eq] at h
  have := key_of_sr h (by simp [okey]) rfl
  cases b <;> simp [okey] at this
  subst this; rfl

theorem soB_vcpu_right {a : capability.Cap} {v : U64} (h : soB a (.Vcpu v) = true) : a = .Vcpu v := by
  cases a
  all_goals first
    | (simp [soB] at h; done)
    | (exact (soB_vcpu_left h).symm)
    | (have h' := h; simp only [soB] at h'; have := srB_vcpu_right rfl h'; simp [shape] at this)

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **A non-final `Vcpu v` cap has an MDB neighbour holding `Vcpu v`** (cdt.rs l. 163-175). -/
theorem isFinal_vcpu_false {s : S} {slot v : U64}
    (h : cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok false) :
    (prevOf (L.mem s) slot ≠ 0#u64 ∧ capV (L.mem s) (prevOf (L.mem s) slot) = .Vcpu v) ∨
    (nextOf (L.mem s) slot ≠ 0#u64 ∧ capV (L.mem s) (nextOf (L.mem s) slot) = .Vcpu v) := by
  unfold cdt.is_final_capability_with_cap at h
  simp only [slot_prev_eq, slot_next_eq, is_null_eq, slot_cap_eq, capAt_capV, soB_eq, bind_ok] at h
  by_cases hp : prevOf (L.mem s) slot = 0#u64
  · by_cases hn : nextOf (L.mem s) slot = 0#u64
    · simp [hp, hn] at h
    · cases hb : soB (.Vcpu v) (capV (L.mem s) (nextOf (L.mem s) slot))
      · simp [hp, hn, hb] at h
      · exact Or.inr ⟨hn, soB_vcpu_left hb⟩
  · cases ha : soB (capV (L.mem s) (prevOf (L.mem s) slot)) (.Vcpu v)
    · by_cases hn : nextOf (L.mem s) slot = 0#u64
      · simp [hp, hn, ha] at h
      · cases hb : soB (.Vcpu v) (capV (L.mem s) (nextOf (L.mem s) slot))
        · simp [hp, hn, ha, hb] at h
        · exact Or.inr ⟨hn, soB_vcpu_left hb⟩
    · exact Or.inl ⟨hp, soB_vcpu_right ha⟩

/-- `finalise_cap` of a `Vcpu` cap (objects.rs l. 265): no remainder, no cleanup; `vcpu::finalise` iff final. -/
theorem finCap_vcpu {s : S} {a : A} {v : U64} {fin : Bool} {y : (capability.Cap × capability.Cap) × S × A}
    (h : objects.finalise_cap st arI s a (.Vcpu v) fin false = ok y) :
    y.1 = (.Null, .Null) ∧ (fin = false → y.2 = (s, a)) ∧ (fin = true → vcpu.finalise st arI s a v = ok y.2) := by
  unfold objects.finalise_cap at h
  simp only [bind_ok] at h
  unfold objects.finalise_cap_object at h
  cases fin
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases P1.ok_inj_ff h
    exact ⟨rfl, fun _ => rfl, fun h => absurd h (by decide)⟩
  · simp only [↓reduceIte] at h
    obtain ⟨⟨s1, a1⟩, hf, h⟩ := P1.bind_eq_ok h
    try dsimp only at h
    cases P1.ok_inj_ff h
    exact ⟨rfl, fun h => absurd h (by decide), fun _ => hf⟩

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` on a slot holding `Vcpu v` returns at its first round. -/
theorem finImm_vcpu {s : S} {a : A} {slot v : U64} (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_immediate st arI s a slot = ok y) :
    ∃ fin s1 a1, cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok fin ∧
      (fin = false → s1 = s ∧ a1 = a) ∧ (fin = true → vcpu.finalise st arI s a v = ok (s1, a1)) ∧
      y = (.Ok { success := true, cleanup := .Null }, s1, a1) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, h⟩ := P1.bind_eq_ok h
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨w, hw, -⟩ := spec_exists (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body at hb
  have hcn : capability.Cap.Vcpu v ≠ .Null := vcpu_ne_null v
  simp only [hf, ↓reduceIte, hw, bind_ok, slot_cap_eq, hc, cap_is_null_ne hcn, Bool.false_eq_true] at hb
  obtain ⟨fin, hfin, hb⟩ := P1.bind_eq_ok hb
  obtain ⟨⟨⟨rem, cl⟩, s1, a1⟩, hfc, -⟩ := P1.bind_eq_ok hb
  obtain ⟨e1, e2, e3⟩ := finCap_vcpu arI hfc
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  rw [hfc] at hb
  simp only [cdt.cap_removable, bind_ok, ↓reduceIte, uncurry_apply_pair] at hb
  cases P1.ok_inj_ff hb
  try dsimp only at h
  cases P1.ok_inj_ff h
  exact ⟨fin, s1, a1, hfin, fun h0 => by simpa using e2 h0, e3, rfl⟩

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_deferred` on a slot holding `Vcpu v` returns at its first round. -/
theorem finDef_vcpu {s : S} {a : A} {slot v : U64} (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_deferred st arI s a slot = ok y) :
    ∃ fin s1 a1, cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok fin ∧
      (fin = false → s1 = s ∧ a1 = a) ∧ (fin = true → vcpu.finalise st arI s a v = ok (s1, a1)) ∧
      y = (.Ok { success := true, cleanup := .Null }, s1, a1) := by
  unfold cdt.finalise_slot_deferred cdt.finalise_slot_deferred_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, h⟩ := P1.bind_eq_ok h
  have hf : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨w, hw, -⟩ := spec_exists (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_deferred_loop.body at hb
  have hcn : capability.Cap.Vcpu v ≠ .Null := vcpu_ne_null v
  simp only [hf, ↓reduceIte, hw, bind_ok, slot_cap_eq, hc, cap_is_null_ne hcn, Bool.false_eq_true] at hb
  obtain ⟨fin, hfin, hb⟩ := P1.bind_eq_ok hb
  obtain ⟨⟨⟨rem, cl⟩, s1, a1⟩, hfc, -⟩ := P1.bind_eq_ok hb
  obtain ⟨e1, e2, e3⟩ := finCap_vcpu arI hfc
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl⟩ := e1
  rw [hfc] at hb
  simp only [cdt.cap_removable, bind_ok, ↓reduceIte, uncurry_apply_pair] at hb
  cases P1.ok_inj_ff hb
  try dsimp only at h
  cases P1.ok_inj_ff h
  exact ⟨fin, s1, a1, hfin, fun h0 => by simpa using e2 h0, e3, rfl⟩

/-- **`cdt::delete` of a slot holding `Vcpu v`** (cdt.rs l. 300-316): `Ok`, after `is_final`, `vcpu.finalise` iff
final, and `empty_slot … Null`. -/
theorem delete_vcpu_ok {s : S} {a : A} {slot v : U64} {exposed : Bool} (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st arI s a slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ fin s1 a1, cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok fin ∧
      (fin = false → s1 = s ∧ a1 = a) ∧ (fin = true → vcpu.finalise st arI s a v = ok (s1, a1)) ∧
      cdt.empty_slot st arI s1 a1 slot .Null = ok y.2 := by
  unfold cdt.delete at h
  cases exposed
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    unfold cdt.delete_deferred at h
    obtain ⟨⟨r, s1, a1⟩, hf, h⟩ := P1.bind_eq_ok h
    obtain ⟨fin, s1', a1', hfin, h0, h1, e⟩ := finDef_vcpu arI hc hf
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    obtain ⟨cf, ecf, h⟩ := P1.bind_eq_ok h
    simp only [core.result.Result.Insts.CoreOpsTry.branch] at ecf
    cases P1.ok_inj_ff ecf
    try dsimp only at h
    simp only [↓reduceIte] at h
    obtain ⟨⟨s2, a2⟩, he, h⟩ := P1.bind_eq_ok h
    cases P1.ok_inj_ff h
    exact ⟨rfl, fin, s1, a1, hfin, h0, h1, he⟩
  · simp only [↓reduceIte] at h
    obtain ⟨⟨r, s1, a1⟩, hf, h⟩ := P1.bind_eq_ok h
    obtain ⟨fin, s1', a1', hfin, h0, h1, e⟩ := finImm_vcpu arI hc hf
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    obtain ⟨cf, ecf, h⟩ := P1.bind_eq_ok h
    simp only [core.result.Result.Insts.CoreOpsTry.branch] at ecf
    cases P1.ok_inj_ff ecf
    try dsimp only at h
    obtain ⟨⟨s2, a2⟩, he, h⟩ := P1.bind_eq_ok h
    cases P1.ok_inj_ff h
    exact ⟨rfl, fin, s1, a1, hfin, h0, h1, he⟩

end

/-! ## `vcpu.finalise` with its write set -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {V X U : Set U64} {th : TypedHeap}

set_option maxHeartbeats 8000000 in
/-- **`vcpu.finalise` unlinks**: `vcpu_finalise_jvB`'s conclusion and `VList (V \ {v})` (module docstring;
`hnd`, `hhv`, `hhc` [J]). -/
theorem vcpu_finalise_vlW (hA : P0.ArchTotal ar) (Ly : JVLay V th U) {s : S} (Da : DetAtB st V th (fun _ => U) s)
    (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s) (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s)) (a : A) {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a v ⦃ r => JExtV (L := L) V X th r.1 ∧ RunVmB (L := L) th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) th r.1 ∧
      P1.WritesIn st s r.1 (fun b => BW V th b ∨ CW st V th (fun _ => U) s b ∨ LW st V s b) ⦄ := by
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
      L.mem r.1 (vTcbA v) = 0#u64 ∧ P1.WritesIn st s r.1 (fun b => JW V th b ∨ CW st V th (fun _ => U) s b) ∧
      P1.WritesIn st s r.1 (fun b => BW V th b ∨ CW st V th (fun _ => U) s b)) ?_ ?_
  · have w1J : P1.WritesIn st s s1 (fun b => JW V th b ∨ CW st V th (fun _ => U) s b) :=
      w1'.mono fun b e => Or.inr (Or.inl e)
    have w1B : P1.WritesIn st s s1 (fun b => BW V th b ∨ CW st V th (fun _ => U) s b) :=
      w1'.mono fun b e => Or.inr (Or.inl e)
    split
    · rename_i hb
      have h0 : t = 0#u64 := by simpa [eb] using hb
      exact (WP.spec_ok _).2 ⟨E1, R1, by rw [← et', h0], w1J, w1B⟩
    · rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by simp [eb, e])
      obtain ⟨htt, htv⟩ := (E1.back v hvV).resolve_left (by rw [← et']; exact ht0)
      rw [← et'] at htt htv
      refine WP.spec_mono (vcpu_detach_jvB hA D Da1 E1 R1 a2 htt) fun r Pd => ?_
      have Pd' : DetPost st V X th (fun _ => U) t s1 r.1 := Pd
      exact ⟨Pd'.ext, Pd'.rvm, Pd'.b0 v hvV htv, (w1J.trans (Pd'.footJ htt fun _ => by
        rw [htv]; exact hvV)).mono fun b h => h.elim id fun h' => h'.elim Or.inl fun c => Or.inr (CW.of w1' c),
        (w1B.trans (Pd'.footB htt fun _ => by
        rw [htv]; exact hvV)).mono fun b h => h.elim id fun h' => h'.elim Or.inl fun c => Or.inr (CW.of w1' c)⟩
  rintro ⟨s2, a3⟩ ⟨E2, R2, b2, w2, w2B⟩
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
        VList st (V \ {v}) th s4 ∧
        P1.WritesIn st s s4 (fun b => BW V th b ∨ CW st V th (fun _ => U) s b ∨ LW st V s b) :=
      fun s4 w4 vH vN vP => by
    have hd : ∀ b, ((L.mem s (vPrevA v) = 0#u64 ∧ b = P1.vHeadA st s) ∨
        (L.mem s (vPrevA v) ≠ 0#u64 ∧ b = P1.vNextA (L.mem s (vPrevA v))) ∨
        (L.mem s (P1.vNextA v) ≠ 0#u64 ∧ b = vPrevA (L.mem s (P1.vNextA v)))) → ¬ JW V th b ∧ ¬ SW th b := by
      rintro b (⟨-, e⟩ | h | h)
      · exact (F.nbr b (Or.inl e)).2
      · exact (F.nbr b (Or.inr (Or.inl h))).2
      · exact (F.nbr b (Or.inr (Or.inr h))).2
    exact ⟨E2.of_writes P w4 fun b h => (hd b h).1, R2.of_clean P w4 hd,
      by rw [w4.mem_eq (P.jw _ JWb) fun h => (hd _ h).1 JWb]; exact b2,
      vlist_unlink Vl hf Ly.vv hhv hvV k2 w2.1 w4 vH vN vP,
      (w2B.trans w4).mono fun b h => h.elim (fun h' => h'.elim Or.inl fun c => Or.inr (Or.inl c)) fun h' =>
        Or.inr (Or.inr (by
          rcases h' with ⟨-, e⟩ | ⟨h0, e⟩ | ⟨h0, e⟩
          exacts [Or.inl e, Or.inr ⟨_, pvV h0, Or.inl e⟩, Or.inr ⟨_, nxV h0, Or.inr e⟩]))⟩
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

/-! ## Slot words are not in the finalisation's write set -/

/-- A word inside some slot of the typed heap. -/
def SlR (th : TypedHeap) (b : U64) : Prop := ∃ y, IsSlot th y ∧ y.val ≤ b.val ∧ b.val < y.val + 32

theorem not_slotWd_of (hP : Placed th) {b : U64} (h : ¬ SlR th b) :
    ¬ ∃ x k, IsSlot th x ∧ Off k ∧ b = wordOf x k := by
  rintro ⟨x, k, hx, hk, rfl⟩
  exact h ⟨x, hx, by rw [slot_word_val hP hx hk]; omega, by rw [slot_word_val hP hx hk]; have := hk.lt; omega⟩

/-- A step writing only words outside the slots keeps every slot. -/
theorem slotsSame_of_writes (hP : Placed th) {s s' : S} {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hn : ∀ b, W b → ¬ SlR th b) : SlotsSame th (L.mem s) (L.mem s') := by
  intro a ha
  have g : ∀ k, Off k → L.mem s' (wordOf a k) = L.mem s (wordOf a k) := fun k hk =>
    hW.mem_eq (slot_word_aligned hP ha hk) fun hb => not_slotWd_of hP (hn _ hb) ⟨a, k, ha, hk, rfl⟩
  have g0 := g 0#u64 off0
  rw [wordOf_zero] at g0
  exact ⟨g0, g _ off8, g _ off16, g _ off24⟩

theorem nSl_v (Ly : JVLay V th U) {v : U64} (hv : v ∈ V) {b : U64} (h1 : v.val ≤ b.val)
    (h2 : b.val < v.val + 32768) : ¬ SlR th b := by
  rintro ⟨y, hy, g1, g2⟩
  obtain ⟨p, k, hk, f1, f2, -, -⟩ := lay_slot_in Ly.pl hy
  rcases Ly.vap v hv p k hk with e | e <;> omega

theorem nSl_t (Ly : JVLay V th U) {t : U64} (ht : th t = some .tcb) {b : U64} {K : Nat}
    (hb : b.val = t.val + K) (hK1 : 192 ≤ K) (hK2 : K < 4096) : ¬ SlR th b := by
  rintro ⟨y, hy, g1, g2⟩
  obtain ⟨p, k, hk, f1, f2, f3, -⟩ := lay_slot_in Ly.pl hy
  by_cases e : p = t
  · subst e; rw [ht] at hk; cases hk; have := f3 rfl; omega
  · rcases Ly.pl.disj p t k .tcb hk ht e with e' | e' <;>
      (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega

/-- **No word `vcpu.finalise` writes lies in a slot** (`hns` [J] for the kernel-global words; the rest by `JVLay`). -/
theorem finW_nSl (Ly : JVLay V th U) {s : S}
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b) :
    ∀ b, (BW V th b ∨ CW st V th (fun _ => U) s b ∨ LW st V s b) → ¬ SlR th b := by
  have hf := Ly.vfit
  rintro b ((⟨t, ht, rfl⟩ | ⟨w, hw, rfl⟩) | (e | e | ⟨t, ht, hr | rfl⟩ | ⟨w, hw, rfl | rfl⟩) |
    (e | ⟨w, hw, rfl | rfl⟩))
  · exact nSl_t Ly ht (lay_tVcpu_val (Ly.tA t ht)) (by norm_num) (by norm_num)
  · have := lay_vTcb_val (hf w hw).2; exact nSl_v Ly hw (by omega) (by omega)
  · exact hns b (Or.inl e)
  · exact hns b (Or.inr (Or.inl e))
  · rcases hr with ⟨K, k1, k2, -, rfl⟩ | hu
    · exact nSl_t Ly ht (lay_tw_val (Ly.tA t ht) (by omega)) (by omega) (by omega)
    · rintro ⟨y, hy, g1, g2⟩; exact Ly.usl b hu y hy ⟨g1, g2⟩
  · exact nSl_t Ly ht (lay_stA_val (Ly.tA t ht)) (by norm_num) (by norm_num)
  · have := lay_pend_val (hf w hw).2; exact nSl_v Ly hw (by omega) (by omega)
  · have := lay_svm_val (hf w hw).2; exact nSl_v Ly hw (by omega) (by omega)
  · exact hns b (Or.inr (Or.inr e))
  · have := lay_next_val (hf w hw).2; exact nSl_v Ly hw (by omega) (by omega)
  · have := lay_prev_val (hf w hw).2; exact nSl_v Ly hw (by omega) (by omega)

/-- A linked slot's non-null `prev` is another slot. -/
theorem mdb_prev_slot (hP : Placed th) {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) {x : U64}
    (hx : x ∈ G.chains.flatten) (hxs : IsSlot th x) (hp : prevOf mem x ≠ 0#u64) :
    IsSlot th (prevOf mem x) ∧ prevOf mem x ≠ x := by
  obtain ⟨h1, h2⟩ := hM.prev_link hx hp
  refine ⟨((hM.members _).1 h1).1, fun e => ?_⟩
  rw [e] at h2
  rcases hM.next_mem hx with h | ⟨-, h⟩
  · rw [h] at h2; exact hxs.ne_zero hP h2.symm
  · exact h h2

/-- A linked slot's non-null `next` is another slot. -/
theorem mdb_next_slot {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G) {x : U64}
    (hx : x ∈ G.chains.flatten) (hn : nextOf mem x ≠ 0#u64) :
    IsSlot th (nextOf mem x) ∧ nextOf mem x ≠ x := by
  rcases hM.next_mem hx with h | ⟨h1, h2⟩
  · exact absurd h hn
  · exact ⟨((hM.members _).1 h1).1, h2⟩

/-! ## The deletion keeps `VCapped` -/

variable (arI : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **`cdt::delete` of a slot holding `Vcpu v` keeps `VCapped`** (module docstring): `VList V'` and `VCappedM V'`
after, `V' = V \ {v}` if the cap was final (`vcpu::finalise` ran), `V` otherwise. -/
theorem delete_vcpu_vcapped (hA : P0.ArchTotal arI) (Ly : JVLay V th U) {s : S}
    (Da : DetAtB st V th (fun _ => U) s) (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s)
    (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s))
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b)
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) (hVC : VCappedM V th (L.mem s))
    {a : A} {slot v : U64} {exposed : Bool} (hx : IsSlot th slot) (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st arI s a slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ V', V' ⊆ V ∧ VList st V' th y.2.1 ∧ VCappedM V' th (L.mem y.2.1) := by
  have hP := Ly.pl
  obtain ⟨hy1, fin, s1, a1, hfin, hf0, hf1, he⟩ := delete_vcpu_ok arI hc h
  refine ⟨hy1, ?_⟩
  have hcv : capV (L.mem s) slot = .Vcpu v := capV_of_capAt hc
  have hvV : v ∈ V := by have := E.cap slot hx; rw [hcv] at this; exact this
  have hxm : slot ∈ G.chains.flatten := (hM.members slot).2 ⟨hx, _, hc, vcpu_ne_null v⟩
  -- every other VCPU's cap lies in a slot other than `slot`
  have hoth : ∀ w ∈ V, w ≠ v → ∃ y, IsSlot th y ∧ y ≠ slot ∧ capV (L.mem s) y = .Vcpu w := by
    intro w hw hwv
    obtain ⟨y0, hy0, hc0⟩ := hVC w hw
    refine ⟨y0, hy0, ?_, hc0⟩
    rintro rfl; rw [hcv] at hc0; cases hc0; exact hwv rfl
  -- the state after the finalisation
  obtain ⟨V1, hV1, Vl1, hSS, hk1, hcap1⟩ : ∃ V1, V1 ⊆ V ∧ VList st V1 th s1 ∧
      SlotsSame th (L.mem s) (L.mem s1) ∧ L.ksb s1 = L.ksb s ∧
      ∀ w ∈ V1, ∃ y, IsSlot th y ∧ y ≠ slot ∧ capV (L.mem s) y = .Vcpu w := by
    cases fin
    · obtain ⟨rfl, rfl⟩ := hf0 rfl
      refine ⟨V, fun _ h => h, Vl, SlotsSame.refl _ _, rfl, fun w hw => ?_⟩
      by_cases hwv : w = v
      · subst hwv
        rcases isFinal_vcpu_false hfin with ⟨hp, hpc⟩ | ⟨hn, hnc⟩
        · obtain ⟨g1, g2⟩ := mdb_prev_slot hP hM hxm hx hp
          exact ⟨_, g1, g2, hpc⟩
        · obtain ⟨g1, g2⟩ := mdb_next_slot hM hxm hn
          exact ⟨_, g1, g2, hnc⟩
      · exact hoth w hw hwv
    · have hF := P1.spec_at (vcpu_finalise_vlW hA Ly Da E R Vl hnd hhv hhc a hvV) (hf1 rfl)
      obtain ⟨-, -, -, Vl', hw⟩ := hF
      refine ⟨V \ {v}, Set.diff_subset, Vl', slotsSame_of_writes hP hw (finW_nSl Ly hns), hw.1, fun w hw' => ?_⟩
      exact hoth w hw'.1 hw'.2
  -- the slot and its links at `s1`
  have hc1 : capAt (L.mem s1) slot = ok (.Vcpu v) := by rw [hSS.capAt hx]; exact hc
  have hM1 : MdbLinks th (L.mem s1) G := hM.of_same hSS
  have hpv : prevOf (L.mem s1) slot = 0#u64 ∨
      (IsSlot th (prevOf (L.mem s1) slot) ∧ prevOf (L.mem s1) slot ≠ slot) := by
    by_cases hp : prevOf (L.mem s1) slot = 0#u64
    · exact Or.inl hp
    · exact Or.inr (mdb_prev_slot hP hM1 hxm hx hp)
  have hnx : nextOf (L.mem s1) slot = 0#u64 ∨
      (IsSlot th (nextOf (L.mem s1) slot) ∧ nextOf (L.mem s1) slot ≠ slot) := by
    by_cases hn : nextOf (L.mem s1) slot = 0#u64
    · exact Or.inl hn
    · exact Or.inr (mdb_next_slot hM1 hxm hn)
  have hPN : prevOf (L.mem s1) slot ≠ 0#u64 → nextOf (L.mem s1) slot ≠ 0#u64 →
      prevOf (L.mem s1) slot ≠ nextOf (L.mem s1) slot := fun h1 h2 => hM1.prev_ne_next hP hxm h1 h2
  have hEW := (P1.spec_at (empty_slot_mem (ar := arI) hP s1 a1 slot hx _ hc1 (vcpu_ne_null v) hpv hnx hPN) he).1
  have hF2 := (P1.spec_at (Vs.empty_frame2 (ar := arI) hP s1 a1 slot hx _ hc1 (hpv.imp_right And.left)
    (hnx.imp_right And.left)) he).1
  refine ⟨V1, hV1, ?_, fun w hw => ?_⟩
  · -- the list words are no slot words
    have hhd : P1.vHeadA st s1 = P1.vHeadA st s := by unfold P1.vHeadA; rw [hk1]
    refine Vl1.frame hF2.1 (fun b hb => hF2.2.2 b ?_ ?_) (fun _ h => h) (fun _ h => h)
    · rcases hb with e | ⟨w, hw, e | e⟩
      · rw [e, hhd]; exact Vl.hd.1
      · have := lay_next_val (Ly.vfit w (hV1 hw)).2; have := (Ly.vfit w (hV1 hw)).1
        unfold P1.Aligned; rw [e]; omega
      · have := lay_prev_val (Ly.vfit w (hV1 hw)).2; have := (Ly.vfit w (hV1 hw)).1
        unfold P1.Aligned; rw [e]; omega
    · refine not_slotWd_of hP ?_
      rcases hb with e | ⟨w, hw, e | e⟩
      · rw [e, hhd]; exact hns _ (Or.inr (Or.inr rfl))
      · have := lay_next_val (Ly.vfit w (hV1 hw)).2
        exact nSl_v Ly (hV1 hw) (by rw [e]; omega) (by rw [e]; omega)
      · have := lay_prev_val (Ly.vfit w (hV1 hw)).2
        exact nSl_v Ly (hV1 hw) (by rw [e]; omega) (by rw [e]; omega)
  · obtain ⟨y0, hy0, hne, hc0⟩ := hcap1 w hw
    refine ⟨y0, hy0, ?_⟩
    have e0 := hEW y0 hy0 0#u64 off0
    have e8 := hEW y0 hy0 8#u64 off8
    rw [wordOf_zero] at e0
    simp [hne] at e0 e8
    rw [capV_of_words e0 e8, hSS.capV hy0]; exact hc0

end

end
end Fl4Proofs.P3.VirtVCappedDel
