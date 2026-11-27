/-
P3x for virtualization (line virt, gen 26, items 1-2): **the final `Vcpu` delete refutes `JExtV` and keeps
`JExtV2`.**

* `empty_vcpu_post`: `cdt.empty_slot … Null` of a slot holding `Vcpu v` (MDB-linked): the slot's cap becomes
  `Null`, every other slot keeps its cap, and every aligned word outside the slots keeps its value (P3/Empty's
  `empty_slot_mem`, P3/CnFrame's `empty_frame2`).
* **`final_delete_not_jextV`** — gen 25's counterexample mechanised: at a state satisfying `JExtV V X`, with the
  `Vcpu v` slot's cap final (`is_final_capability_with_cap = true`) and **another** slot `y1` holding
  `IoPort f l v`, every `Ok` outcome of `cdt.delete` (either `exposed`) has a VCPU list `V' ⊆ V` (`VList`,
  `VCappedM`, gen 23's `delete_vcpu_vcapped`) with `v ∉ V'` (gen 25's `delete_vcpu_final_alone`: no `Vcpu v` cap
  left), `y1` still holding `IoPort f l v`, and **`¬ JExtV V'' X' th` for every `V''` not containing `v`** — in
  particular not at the new list `V'`. The entry shape is reachable (gen 25, VirtVFinal docstring: retype VCPU `v`
  with one `Vcpu v` cap — final; IoPortControl issues `IoPort f l 0`, ioport.rs l. 102; `X86VCPUEnableIOPort` on
  `v` rewrites it to `IoPort f l v`, vcpu.rs l. 1046; at that state `JExtV V X` holds, `v ∈ V`). So `JExtV` (and
  `JAtZV`, whose field `extv : JExtV` it is, so `JAtZV3`) is not an invariant of FL4's reachable VM-epoch states.
* TCB-only transfers (P3/JExtV2's `thTcb`): `placed_thTcb`, `jw_thTcb`, `sw_thTcb`, `bw_thTcb`, `cw_thTcb`,
  `lay_thTcb`, `detB_thTcb`, `vl_thTcb`, `rvm_toTcb`, `rvm_ofTcb` (every placement fact the VCPU finaliser needs
  only weakens when CNodes leave the typed heap).
* `post_empty_jv2`: `JExtV2` / `RunVmB` / `NoIoTcb` across `empty_slot`.
* **`delete_vcpu_jv2`** — the corrected statement: `cdt.delete` (either `exposed`) of a slot holding `Vcpu v`
  from a state with **`JExtV2 V X`** (stale IO-port owners allowed), `RunVmB`, `VcpuChunked` and `NoIoTcb`:
  `Ok`; if the cap was final, `JExtV2 (V \ {v}) X`, `RunVmB` and `NoIoTcb` after; if not, `JExtV2 V X`, `RunVmB`
  and `NoIoTcb` after. The final case runs `vcpu.finalise` through gen 23's `vcpu_finalise_vlW` at the TCB-only
  heap (`JExtV2.toTcb`), its slot frame (`finW_nSl`) at `th`, and `JExtV2.shrink` with gen 25's `vcpu_alone`.

Named premise (new): **`hT : NoIoTcb th (L.mem s)` [J]** (`delete_vcpu_jv2`; kept: `NoIoTcb` after in both
cases) — no TCB cap slot holds an IO-port cap with a nonzero owner. Justification (FL4 source): a TCB's six cap
slots (`tl::SLOT_CTABLE` … `SLOT_EPT`, arch/x86_64/layout.rs l. 9-14) are written only by `install_tcb_cap`
(tcb.rs l. 68-75, from `TCB_Configure` / `SetSpace` / `SetSchedParams`-style decoders l. 121-128 / 154: the
CSpace root must be a CNode cap, `derive_roots` l. 189-192; the VSpace root a mapped PML4 cap, l. 193-196 /
vspace.rs l. 174-176; the fault and timeout handlers `valid_fault_handler`: an endpoint or null, faults.rs l. 57-63,
tcb.rs l. 620/644/655), by `install_buffer` (l. 88-100, a frame cap, `check_valid_ipc_buffer` vspace.rs l. 179),
by `TCBSetEPTRoot` (l. 410-417, an `Ept` cap) and by `cdt::delete` / `empty_slot` (to `Null`); CNode operations
and retype reach only CNode slots (CSpace lookup resolves into CNodes). So no TCB slot ever holds an `IoPort` cap
on a reachable state (owned or not) — not false on reachable states; derivable at a joint state as a [J] field
of the VM-epoch bundle. Used unchanged: `delete_vcpu_vcapped`'s / `vcpu_finalise_vlW`'s `hnd`, `hhv`, `hhc`, `hns`
[J]; `VcpuChunked` stays a state hypothesis (gen 24: a [J] field to be). No existing statement changed; new file.
-/
import Fl4Proofs.P3.VirtVFinal
import Fl4Proofs.P3.JExtV2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtJExtV2Del
open fl4_core Classical Fl4Proofs.P3 Fl4Proofs.P3.VirtVCapped Fl4Proofs.P3.VirtVCappedDel
  Fl4Proofs.P3.VirtVChunk Fl4Proofs.P3.VirtVFinal

noncomputable section

/-! ## The TCB-only heap keeps every placement fact the finaliser needs -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {V U : Set U64} {th : TypedHeap}

theorem placed_thTcb (hP : Placed th) : Placed (thTcb th) where
  align p k h := hP.align p k (thTcb_some h).1
  fits p k h := hP.fits p k (thTcb_some h).1
  disj p q kp kq hp hq hne := hP.disj p q kp kq (thTcb_some hp).1 (thTcb_some hq).1 hne
  high p k h := hP.high p k (thTcb_some h).1

theorem jw_thTcb {b : U64} (h : JW V (thTcb th) b) : JW V th b := by
  rcases h with ⟨y, hy, e⟩ | ⟨t, ht, e⟩ | hv
  · exact Or.inl ⟨y, isSlot_thTcb hy, e⟩
  · exact Or.inr (Or.inl ⟨t, thTcb_tcb.1 ht, e⟩)
  · exact Or.inr (Or.inr hv)

theorem sw_thTcb {b : U64} : SW (thTcb th) b ↔ SW th b :=
  ⟨fun ⟨t, ht, e⟩ => ⟨t, thTcb_tcb.1 ht, e⟩, fun ⟨t, ht, e⟩ => ⟨t, thTcb_tcb.2 ht, e⟩⟩

theorem bw_thTcb {b : U64} : BW V (thTcb th) b ↔ BW V th b := by
  unfold BW
  constructor
  · rintro (⟨t, ht, e⟩ | h)
    · exact Or.inl ⟨t, thTcb_tcb.1 ht, e⟩
    · exact Or.inr h
  · rintro (⟨t, ht, e⟩ | h)
    · exact Or.inl ⟨t, thTcb_tcb.2 ht, e⟩
    · exact Or.inr h

theorem cw_thTcb {Ub : U64 → Set U64} {s : S} {b : U64} :
    CW st V (thTcb th) Ub s b ↔ CW st V th Ub s b := by
  unfold CW
  constructor
  · rintro (e | e | ⟨t, ht, h⟩ | h)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl ⟨t, thTcb_tcb.1 ht, h⟩))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (e | e | ⟨t, ht, h⟩ | h)
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl ⟨t, thTcb_tcb.2 ht, h⟩))
    · exact Or.inr (Or.inr (Or.inr h))

theorem lay_thTcb (Ly : JVLay V th U) : JVLay V (thTcb th) U where
  pl := placed_thTcb Ly.pl
  thk q k h := Or.inl (thTcb_some h).2
  tA t ht := Ly.tA t (thTcb_tcb.1 ht)
  vfit := Ly.vfit
  vap v hv p k hk := Ly.vap v hv p k (thTcb_some hk).1
  vv := Ly.vv
  ua := Ly.ua
  usl b hb y hy := Ly.usl b hb y (isSlot_thTcb hy)
  ut b hb t ht := Ly.ut b hb t (thTcb_tcb.1 ht)
  uv := Ly.uv

theorem detB_thTcb {Ub : U64 → Set U64} {s : S} (Da : DetAtB st V th Ub s) : DetAtB st V (thTcb th) Ub s where
  node := Da.node
  nd b hb := ⟨fun h => (Da.nd b hb).1 (jw_thTcb h), fun h => (Da.nd b hb).2 (sw_thTcb.1 h)⟩
  buf s1 hw t ht := Da.buf s1 (hw.mono fun _ hb => hb.imp bw_thTcb.1 cw_thTcb.1) t (thTcb_tcb.1 ht)

theorem vl_thTcb {s : S} (Vl : VList st V th s) : VList st V (thTcb th) s :=
  ⟨Vl.lst, Vl.hd.1, fun h => Vl.hd.2.1 (jw_thTcb h), fun h => Vl.hd.2.2 (sw_thTcb.1 h)⟩

theorem rvm_toTcb {s : S} (R : RunVmB (L := L) th s) : RunVmB (L := L) (thTcb th) s :=
  fun t ht => R t (thTcb_tcb.1 ht)

theorem rvm_ofTcb {s : S} (R : RunVmB (L := L) (thTcb th) s) : RunVmB (L := L) th s :=
  fun t ht => R t (thTcb_tcb.2 ht)

end

/-! ## `empty_slot` of the deleted slot -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {V X U : Set U64} {th : TypedHeap}

/-- **`empty_slot` of a `Vcpu v` slot**: the slot nulled, the other slots' caps and the words outside slots kept. -/
theorem empty_vcpu_post (hP : Placed th) {s1 : S} {a1 : A} {G : MdbGhost} (hM1 : MdbLinks th (L.mem s1) G)
    {slot v : U64} (hxm : slot ∈ G.chains.flatten) (hx : IsSlot th slot)
    (hc1 : capAt (L.mem s1) slot = ok (.Vcpu v)) {y2 : S × A}
    (he : cdt.empty_slot st arI s1 a1 slot .Null = ok y2) :
    (∀ y0, IsSlot th y0 → capV (L.mem y2.1) y0 = if y0 = slot then .Null else capV (L.mem s1) y0) ∧
    (∀ b, P1.Aligned b → ¬ SlR th b → L.mem y2.1 b = L.mem s1 b) := by
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
  refine ⟨fun y0 hy0 => ?_, fun b hb hn => hF2.2.2 b hb (not_slotWd_of hP hn)⟩
  have e0 := hEW y0 hy0 0#u64 off0
  have e8 := hEW y0 hy0 8#u64 off8
  rw [wordOf_zero] at e0
  by_cases hne : y0 = slot
  · rw [if_pos hne] at e0 e8
    rw [if_pos hne]
    unfold capV; rw [e0, e8]; rfl
  · simp [hne] at e0 e8
    rw [if_neg hne]
    exact capV_of_words e0 e8

/-- **`JExtV2`, `RunVmB` and `NoIoTcb` across `empty_slot`** (the words of the extension are no slot words). -/
theorem post_empty_jv2 (Ly : JVLay V th U) {s s1 s2 : S}
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b)
    {V1 : Set U64} (hV1 : V1 ⊆ V) (E1 : JExtV2 (L := L) V1 X th s1) (R1 : RunVmB (L := L) th s1)
    (T1 : NoIoTcb th (L.mem s1)) {slot : U64}
    (hcp : ∀ y0, IsSlot th y0 → capV (L.mem s2) y0 = if y0 = slot then .Null else capV (L.mem s1) y0)
    (hfr : ∀ b, P1.Aligned b → ¬ SlR th b → L.mem s2 b = L.mem s1 b) :
    JExtV2 (L := L) V1 X th s2 ∧ RunVmB (L := L) th s2 ∧ NoIoTcb th (L.mem s2) := by
  have P := Ly.detPl.pl
  have kT : ∀ t, th t = some .tcb → L.mem s2 (tVcpuA t) = L.mem s1 (tVcpuA t) := fun t ht =>
    hfr _ (P.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))) (finW_nSl Ly hns _ (Or.inl (Or.inl ⟨t, ht, rfl⟩)))
  have kV : ∀ w ∈ V1, L.mem s2 (vTcbA w) = L.mem s1 (vTcbA w) := fun w hw =>
    hfr _ (P.jw _ (Or.inr (Or.inr ⟨w, hV1 hw, rfl⟩))) (finW_nSl Ly hns _ (Or.inl (Or.inr ⟨w, hV1 hw, rfl⟩)))
  have kS : ∀ t, th t = some .tcb → L.mem s2 (P1.stA t) = L.mem s1 (P1.stA t) := fun t ht =>
    hfr _ (P.sw _ ⟨t, ht, rfl⟩)
      (finW_nSl Ly hns _ (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inr rfl⟩))))))
  refine ⟨⟨fun y hy => ?_, fun t ht => ?_, fun w hw => ?_, E1.nz⟩, fun t ht hs => ?_, fun y hy f l o hc => ?_⟩
  · rw [hcp y hy]
    by_cases e : y = slot
    · rw [if_pos e]; trivial
    · rw [if_neg e]; exact E1.cap y hy
  · rw [kT t ht]
    rcases E1.bnd t ht with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [kV _ h1]; exact h2⟩
  · rw [kV w hw]
    rcases E1.back w hw with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, by rw [kT _ h1]; exact h2⟩
  · rw [kT t ht]
    exact R1 t ht (by rw [← kS t ht]; exact hs)
  · rw [hcp y (isSlot_thTcb hy)] at hc
    by_cases e : y = slot
    · rw [if_pos e] at hc; cases hc
    · rw [if_neg e] at hc; exact T1 y hy f l o hc

/-! ## The counterexample -/

set_option maxHeartbeats 4000000 in
/-- **The final `Vcpu v` delete with an IO-port cap owned by `v` elsewhere refutes `JExtV`** (module
docstring). -/
theorem final_delete_not_jextV (hA : P0.ArchTotal arI) (Ly : JVLay V th U) {s : S}
    (Da : DetAtB st V th (fun _ => U) s) (E : JExtV (L := L) V X th s) (R : RunVmB (L := L) th s)
    (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s))
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b)
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) (hVC : VCappedM V th (L.mem s)) (hK : VcpuChunked G (L.mem s))
    {a : A} {slot v : U64} {exposed : Bool} (hx : IsSlot th slot) (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    (hfin : cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok true)
    {y1 f l : U64} (hy1 : IsSlot th y1) (hne1 : y1 ≠ slot) (hio : capV (L.mem s) y1 = .IoPort f l v)
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st arI s a slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ V', V' ⊆ V ∧ VList st V' th y.2.1 ∧ VCappedM V' th (L.mem y.2.1) ∧ v ∉ V' ∧
      capV (L.mem y.2.1) y1 = .IoPort f l v ∧ ∀ (V'' X' : Set U64), v ∉ V'' → ¬ JExtV (L := L) V'' X' th y.2.1 := by
  have hP := Ly.pl
  have hcv : capV (L.mem s) slot = .Vcpu v := capV_of_capAt hc
  have hvV : v ∈ V := by have := E.cap slot hx; rw [hcv] at this; exact this
  have hv0 : v ≠ 0#u64 := E.nz v hvV
  obtain ⟨hy1', V', hV', Vl', hC'⟩ := delete_vcpu_vcapped arI hA Ly Da E R Vl hnd hhv hhc hns hM hVC hx hc h
  obtain ⟨-, fin', hfin', hal⟩ := delete_vcpu_final_alone arI hA Ly Da E R Vl hnd hhv hhc hns hM hK hx hc h
  have hft : fin' = true := eq_of_ok_eq (hfin'.symm.trans hfin)
  have hno := hal hft
  -- the IO-port cap at `y1` is kept
  obtain ⟨-, fin, s1, a1, hfin2, -, hf1, he⟩ := delete_vcpu_ok arI hc h
  have hft2 : fin = true := eq_of_ok_eq (hfin2.symm.trans hfin)
  obtain ⟨-, -, -, -, hw⟩ := P1.spec_at (vcpu_finalise_vlW hA Ly Da E R Vl hnd hhv hhc a hvV) (hf1 hft2)
  have hSS := slotsSame_of_writes hP hw (finW_nSl Ly hns)
  have hc1 : capAt (L.mem s1) slot = ok (.Vcpu v) := by rw [hSS.capAt hx]; exact hc
  have hxm : slot ∈ G.chains.flatten := (hM.members slot).2 ⟨hx, _, hc, vcpu_ne_null v⟩
  have emp := empty_vcpu_post arI hP (hM.of_same hSS) hxm hx hc1 he
  have hio' : capV (L.mem y.2.1) y1 = .IoPort f l v := by
    rw [emp.1 y1 hy1, if_neg hne1, hSS.capV hy1]; exact hio
  refine ⟨hy1', V', hV', Vl', hC', fun hv' => ?_, hio', fun V'' X' hv'' =>
    not_jextV_of_stale hy1 hio' hv0 hv''⟩
  obtain ⟨y0, hy0, hc0⟩ := hC' v hv'
  exact hno y0 hy0 hc0

/-! ## The corrected statement -/

set_option maxHeartbeats 4000000 in
/-- **The `Vcpu` delete keeps `JExtV2`** (module docstring); `hT` [J] (`NoIoTcb`, module docstring). -/
theorem delete_vcpu_jv2 (hA : P0.ArchTotal arI) (Ly : JVLay V th U) {s : S}
    (Da : DetAtB st V th (fun _ => U) s) (E : JExtV2 (L := L) V X th s) (R : RunVmB (L := L) th s)
    (Vl : VList st V th s)
    (hnd : ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val)
    (hhv : ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val)
    (hhc : ¬ CW st V th (fun _ => U) s (P1.vHeadA st s))
    (hns : ∀ b, (b = ipiA st s ∨ b = actA st s ∨ b = P1.vHeadA st s) → ¬ SlR th b)
    (hT : NoIoTcb th (L.mem s))
    {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) (hK : VcpuChunked G (L.mem s))
    {a : A} {slot v : U64} {exposed : Bool} (hx : IsSlot th slot) (hc : capAt (L.mem s) slot = ok (.Vcpu v))
    {y : core.result.Result Unit error.Exc × S × A} (h : cdt.delete st arI s a slot exposed = ok y) :
    y.1 = .Ok () ∧ ∃ fin, cdt.is_final_capability_with_cap st s slot (.Vcpu v) = ok fin ∧
      (fin = true → JExtV2 (L := L) (V \ {v}) X th y.2.1 ∧ RunVmB (L := L) th y.2.1 ∧ NoIoTcb th (L.mem y.2.1)) ∧
      (fin = false → JExtV2 (L := L) V X th y.2.1 ∧ RunVmB (L := L) th y.2.1 ∧ NoIoTcb th (L.mem y.2.1)) := by
  have hP := Ly.pl
  obtain ⟨hy1, fin, s1, a1, hfin, hf0, hf1, he⟩ := delete_vcpu_ok arI hc h
  refine ⟨hy1, fin, hfin, ?_⟩
  have hcv : capV (L.mem s) slot = .Vcpu v := capV_of_capAt hc
  have hxm : slot ∈ G.chains.flatten := (hM.members slot).2 ⟨hx, _, hc, vcpu_ne_null v⟩
  have hvV : v ∈ V := by have := E.cap slot hx; rw [hcv] at this; exact this
  cases fin
  · obtain ⟨rfl, rfl⟩ := hf0 rfl
    refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
    have emp := empty_vcpu_post arI hP hM hxm hx hc he
    exact post_empty_jv2 Ly hns (fun _ h => h) E R hT emp.1 emp.2
  · refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    have hf := hf1 rfl
    have hhc' : ¬ CW st V (thTcb th) (fun _ => U) s (P1.vHeadA st s) := fun h => hhc (cw_thTcb.1 h)
    obtain ⟨E1', R1', hb1, -, hw⟩ := P1.spec_at (vcpu_finalise_vlW hA (lay_thTcb Ly) (detB_thTcb Da)
      (E.toTcb hT) (rvm_toTcb R) (vl_thTcb Vl) hnd hhv hhc' a hvV) hf
    have hw' : P1.WritesIn st s s1 (fun b => BW V th b ∨ CW st V th (fun _ => U) s b ∨ LW st V s b) :=
      hw.mono fun _ hb => hb.imp bw_thTcb.1 (Or.imp cw_thTcb.1 id)
    have hSS := slotsSame_of_writes hP hw' (finW_nSl Ly hns)
    have E1 : JExtV2 (L := L) V X th s1 := JExtV2.ofTcb E1' fun y hy => by rw [hSS.capV hy]; exact E.cap y hy
    have T1 : NoIoTcb th (L.mem s1) := fun y hy f l o hc' =>
      hT y hy f l o (by rw [← hSS.capV (isSlot_thTcb hy)]; exact hc')
    have hc1 : capAt (L.mem s1) slot = ok (.Vcpu v) := by rw [hSS.capAt hx]; exact hc
    have emp := empty_vcpu_post arI hP (hM.of_same hSS) hxm hx hc1 he
    obtain ⟨E2, R2, T2⟩ := post_empty_jv2 Ly hns (fun _ h => h) E1 (rvm_ofTcb R1') T1 emp.1 emp.2
    have hb2 : L.mem y.2.1 (vTcbA v) = 0#u64 := by
      rw [emp.2 _ (Ly.detPl.pl.jw _ (Or.inr (Or.inr ⟨v, hvV, rfl⟩)))
        (finW_nSl Ly hns _ (Or.inl (Or.inr ⟨v, hvV, rfl⟩)))]
      exact hb1
    obtain ⟨hpn, hnn⟩ := isFinal_vcpu_true hfin
    have halone := vcpu_alone hP hM hK hxm hcv hpn hnn
    have hno : ∀ y0, IsSlot th y0 → capV (L.mem y.2.1) y0 ≠ .Vcpu v := fun y0 hy0 hcy => by
      rw [emp.1 y0 hy0] at hcy
      by_cases hne : y0 = slot
      · rw [if_pos hne] at hcy; cases hcy
      · rw [if_neg hne, hSS.capV hy0] at hcy
        have hy0m : y0 ∈ G.chains.flatten := (hM.members y0).2 ⟨hy0, _, by rw [capAt_capV, hcy], vcpu_ne_null v⟩
        exact hne (halone y0 hy0m hcy)
    exact ⟨E2.shrink hb2 Ly.detPl.h0 hno, R2, T2⟩

end

end
end Fl4Proofs.P3.VirtJExtV2Del
