/-
P1 (aarch64, gen 50): **CNode Copy / Mint at decode level carry the MDB facts** — `cnode.decode_copy`
(cnode.rs:48–73) with label `CNodeCopy` or `CNodeMint` keeps `MdbS` (MdbLoop: `MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧
ClsA` over some ghost), onto gen 49's `cdt.insert_with_cap.mdbO` with its hypotheses on the new cap discharged by
MdbCopy (`cnode.copied_cap.al` / `.wf`).

* **`stt_osk`**: `set_thread_state`'s two words (the thread's `STATE`, the core's `SCHED_ACTION`) are no `OS` slot
  word — every `OS` slot's four words kept (`OSKeep`; `stt_capk`'s argument over all four words).
* **`cnode.decode_copy.mdbS`**: every outcome's state satisfies `MdbS`. Error outcomes return the start state; the
  insertion runs after `ensure_empty_slot` (the destination is `Null`), `lookup_source_slot`, a non-null source cap
  (so the source is a chain member, `MdbLk.members`), `copied_cap` (no move, new cap `EncWf` from the decoded
  source cap's `EncWf`, `AlN` the source cap) and a non-null new cap (`AlN.ne`: `AlikeA`), then `set_thread_state`
  (`stt_osk`: `MdbS.keep`, the source and destination caps kept).

* (gen 60) **`cnode.decode_copy.gen`**: the one Copy / Mint / Move / Mutate traversal, for any invariant `P` kept by
  the `move_cap` step (`CpMv`) and the `insert_with_cap` step (`CpIns`); `mdbSX` is its instance with MdbS's steps
  `cnode.decode_copy.mvS` / `insS` (gen 57's `trX` and gen 60's `CoverA` form are the others).

Case hypotheses (no named premise): the destination slot (looked up by the caller, `cnode.decode`) and every slot
`lookup_source_slot` returns at the start state lie in `OS`, and the destination is canonical
(`obj.sext48 dest = dest`, as gen 48/49's insertion lemmas take it; see gen 50's finding on canonical `OS` slots).
-/
import Fl4ProofsA64.P1.MdbCopy
import Fl4ProofsA64.P1.MdbMove
import Fl4ProofsA64.P1.MdbLoop
import Fl4ProofsA64.P1.QueueS2Unm
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-- **`set_thread_state` keeps every `OS` slot's four words** (module docstring). -/
theorem stt_osk (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s s1 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) {t : U64} (ht : t ∈ T)
    (w1 : WritesIn st s s1 (fun b => b = stA t ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    OSKeep st OS s s1 := by
  refine OSKeep.of_writes hO w1 ?_
  rintro b hb (e | e)
  · rcases hb with hl | ⟨hΩ, -⟩
    · exact W7.tlow_ne_field (K := 3328#u64) q.tcbs ht (by simp) (by simp) hl (by rw [e, stA_eq])
    · exact out_ne_field (K := 3328#u64) (q.omega b hΩ) ht (q.tcbs t ht) (by simp) (by rw [← stA_eq, ← e])
  · rcases hb with hl | ⟨hΩ, -⟩
    · exact W7.tlow_ne_node (o := layout.node.SCHED_ACTION) q.tcbs (q.nodes _ q.cur)
        (by simp [layout.node.SCHED_ACTION]) hl e.symm
    · exact out_ne_node (q.omega b hΩ) q.cur (q.nodes _ q.cur) (o := layout.node.SCHED_ACTION)
        (by simp [layout.node.SCHED_ACTION]) (by rw [e])

set_option hygiene false in
/-- An error leaf of the decode: the start state, `MdbS` held. -/
local macro "mleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 hm
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact (WP.spec_ok _).2 hm | exact hm))

/-- (gen 60) **The decode's `move_cap` step, for an invariant `P`**: from the decode's start state `s`, after
`set_thread_state` (`OSKeep`), a non-null source `v` of `OS`, an empty `dest`, `copied_cap` returning a non-null cap
and `is_move = true`. -/
def CpMv (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (lbl len buf dest : U64) (P : S → Prop) :
    Prop :=
  ∀ (s2 : S) (v : U64) (nc : capability.Cap), OSKeep st OS s s2 →
    WritesIn st s s2 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    v ∈ OS → capA st s v ≠ .Null →
    capA st s dest = .Null → cnode.copied_cap st s lbl len buf v (capA st s v) = ok (.Ok (nc, true)) →
    nc ≠ .Null → cdt.move_cap st s2 nc v dest ⦃ s3 => P s3 ⦄

/-- (gen 60) **The decode's `insert_with_cap` step, for an invariant `P`** (`is_move = false`). -/
def CpIns (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (lbl len buf dest : U64) (P : S → Prop) :
    Prop :=
  ∀ (s2 : S) (v : U64) (nc : capability.Cap), OSKeep st OS s s2 →
    WritesIn st s s2 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    v ∈ OS → capA st s v ≠ .Null →
    capA st s dest = .Null → cnode.copied_cap st s lbl len buf v (capA st s v) = ok (.Ok (nc, false)) →
    nc ≠ .Null → cdt.insert_with_cap st s2 nc (capA st s v) v dest ⦃ s3 => P s3 ⦄

theorem CpMv.and {s : S} {lbl len buf dest : U64} {P P' : S → Prop} (h : CpMv st OS s lbl len buf dest P)
    (h' : CpMv st OS s lbl len buf dest P') : CpMv st OS s lbl len buf dest fun x => P x ∧ P' x :=
  fun s2 v nc k w hv hs0 hd0 he hn0 =>
    WP.spec_and (h s2 v nc k w hv hs0 hd0 he hn0) (h' s2 v nc k w hv hs0 hd0 he hn0)

theorem CpIns.and {s : S} {lbl len buf dest : U64} {P P' : S → Prop} (h : CpIns st OS s lbl len buf dest P)
    (h' : CpIns st OS s lbl len buf dest P') : CpIns st OS s lbl len buf dest fun x => P x ∧ P' x :=
  fun s2 v nc k w hv hs0 hd0 he hn0 =>
    WP.spec_and (h s2 v nc k w hv hs0 hd0 he hn0) (h' s2 v nc k w hv hs0 hd0 he hn0)

/-- `copied_cap` returning `is_move = true` at one of the four labels: Move / Mutate. -/
theorem cnode.copied_cap.lblT {s : S} {lbl len buf v : U64} {c nc : capability.Cap}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate) (hc : CapRt.EncWf c)
    (he : cnode.copied_cap st s lbl len buf v c = ok (.Ok (nc, true))) :
    lbl = fl4_abi.label.CNodeMove ∨ lbl = fl4_abi.label.CNodeMutate := by
  rcases hl4 with h | h | h | h
  · have w := cnode.copied_cap.wf (st := st) s lbl len buf v c (Or.inl h) hc
    rw [he, WP.spec_ok] at w; exact absurd (w nc true rfl).1 (by decide)
  · have w := cnode.copied_cap.wf (st := st) s lbl len buf v c (Or.inr h) hc
    rw [he, WP.spec_ok] at w; exact absurd (w nc true rfl).1 (by decide)
  · exact Or.inl h
  · exact Or.inr h

/-- `copied_cap` returning `is_move = false` at one of the four labels: Copy / Mint. -/
theorem cnode.copied_cap.lblF {s : S} {lbl len buf v : U64} {c nc : capability.Cap}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate) (hc : CapRt.EncWf c)
    (he : cnode.copied_cap st s lbl len buf v c = ok (.Ok (nc, false))) :
    lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint := by
  rcases hl4 with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · have w := cnode.copied_cap.mv (st := st) s lbl len buf v c (Or.inl h) hc
    rw [he, WP.spec_ok] at w; exact absurd (w nc false rfl).1 (by decide)
  · have w := cnode.copied_cap.mv (st := st) s lbl len buf v c (Or.inr h) hc
    rw [he, WP.spec_ok] at w; exact absurd (w nc false rfl).1 (by decide)

set_option maxHeartbeats 2000000 in
/-- (gen 60) **The one CNode Copy / Mint / Move / Mutate traversal at decode level** (gen 51's `mdbSX` proof, the
`MdbS` steps abstracted): any invariant `P` of the start state, kept by the `move_cap` step (`CpMv`) and the
`insert_with_cap` step (`CpIns`), holds at every outcome. Gen 51's `mdbSX` and gen 57's `trX` are its instances. -/
theorem cnode.decode_copy.gen (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) {P : S → Prop} (hm : P s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {lbl len buf dest : U64}
    (hsrc : ∀ sl ∈ extra.val, sl ≠ 0#u64 → ∀ (i d : U64),
      cspace.lookup_source_slot st s (capA st s sl) i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄)
    (hmv : CpMv st OS s lbl len buf dest P) (hins : CpIns st OS s lbl len buf dest P) :
    cnode.decode_copy st s lbl len buf extra dest ⦃ r => P r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode_copy
  simp only [error.illegal, error.truncated, cnode.missing_source, bind_ok]
  split
  · mleaf
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl hsl => ?_
  have hslm : sl ∈ extra.val := hsl ▸ List.getElem_mem hl0
  simp only [obj.Slot.is_null, bind_ok]
  split
  · mleaf
  rename_i hsl0'
  have hsl0 : sl ≠ 0#u64 := by simpa using hsl0'
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun si _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun sd _ => ?_
  rw [capA_eq s sl, bind_ok]
  -- the destination is empty
  by_cases hd0 : capA st s dest = .Null
  swap
  · unfold cdt.ensure_empty_slot
    rw [capA_eq, bind_ok, is_null_f hd0, bind_ok]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    mleaf
  have ee : cdt.ensure_empty_slot st s dest = ok (core.result.Result.Ok ()) := by
    unfold cdt.ensure_empty_slot
    rw [capA_eq, bind_ok, hd0, is_null_t, bind_ok]; rfl
  rw [ee, bind_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (hsrc sl hslm hsl0 si sd) fun r1 hr1 => ?_
  rcases r1 with v | e1
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    mleaf
  have hv : v ∈ OS := hr1 v rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [capA_eq, bind_ok]
  by_cases hs0 : capA st s v = .Null
  · rw [hs0, is_null_t, bind_ok]
    simp only [↓reduceIte, bind_ok]
    mleaf
  rw [is_null_f hs0, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (spec_eqv (P0.cnode.copied_cap.p0 st s lbl len buf v (capA st s v) hS)) fun r2 h2 => ?_
  rcases r2 with ⟨nc, mv⟩ | e2
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    mleaf
  have he := h2.1
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  by_cases hn0 : nc = .Null
  · subst hn0
    rw [is_null_t, bind_ok]
    simp only [↓reduceIte, bind_ok]
    mleaf
  rw [is_null_f hn0, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (sched.set_thread_state.vckW2 s ct sched.TS_RESTART q.tcbs (q.nodes _ q.cur) hct)
    fun s2 hw => ?_
  have k2 : OSKeep st OS s s2 := stt_osk hO q hct hw.1
  have w2 : WritesIn st s s2
      (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have e : ct = L.curW s := ect
    rw [← e]; exact hw.1
  cases mv
  · try simp only [Bool.false_eq_true, ↓reduceIte]
    exact WP.spec_bind (hins s2 v nc k2 w2 hv hs0 hd0 he hn0) fun s3 h3 => (WP.spec_ok _).2 h3
  · try simp only [ite_true, if_true, ↓reduceIte]
    exact WP.spec_bind (hmv s2 v nc k2 w2 hv hs0 hd0 he hn0) fun s3 h3 => (WP.spec_ok _).2 h3

/-- (gen 60) **`MdbS`'s `move_cap` step** (gen 51's `mdbSX` move branch). -/
theorem cnode.decode_copy.mvS (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) : CpMv st OS s lbl len buf dest (MdbS st OS) := by
  intro s2 v nc k2 _ hv hs0 hd0 he hn0
  have hc2 : ∀ y ∈ OS, capA st s2 y = capA st s y := fun y hy => by
    unfold capA; rw [(k2 y hy).1, (k2 y hy).2.1]
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have h2 := cnode.copied_cap.mv (st := st) s lbl len buf v (capA st s v)
    (cnode.copied_cap.lblT hl4 hwf he) hwf
  rw [he, WP.spec_ok] at h2
  obtain ⟨-, hal, hwn⟩ := h2 nc true rfl
  exact cdt.move_cap.mdbS hO (hm.keep k2) hv (by rw [hc2 v hv]; exact hs0) hd
    (by rw [hc2 dest hd]; exact hd0) hdc hwn hn0 (by rw [hc2 v hv]; exact hal.ne hn0)

/-- (gen 60) **`MdbS`'s `insert_with_cap` step** (gen 51's `mdbSX` copy branch). -/
theorem cnode.decode_copy.insS (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest) : CpIns st OS s lbl len buf dest (MdbS st OS) := by
  intro s2 v nc k2 _ hv hs0 hd0 he hn0
  have hc2 : ∀ y ∈ OS, capA st s2 y = capA st s y := fun y hy => by
    unfold capA; rw [(k2 y hy).1, (k2 y hy).2.1]
  have hwf : CapRt.EncWf (capA st s v) := CapRt.decodeF_encWf _ _
  have hw2 := cnode.copied_cap.wf (st := st) s lbl len buf v (capA st s v)
    (cnode.copied_cap.lblF hl4 hwf he) hwf
  have ha2 := cnode.copied_cap.al (st := st) s lbl len buf v (capA st s v)
  rw [he, WP.spec_ok] at hw2 ha2
  have hwn := (hw2 nc false rfl).2
  have hal := ha2 nc rfl
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm.keep k2
  have hsm : v ∈ G.flatten := (hM.members v).2 ⟨hv, by rw [hc2 v hv]; exact hs0⟩
  exact WP.spec_mono (cdt.insert_with_cap.mdbO hO hM hRO hK hN hC hsm hd (by rw [hc2 dest hd]; exact hd0) hdc
    (hc2 v hv) hwn hn0 (hal.ne hn0)) fun s3 h3 => ⟨_, h3⟩

/-- (gen 51) **CNode Copy / Mint / Move / Mutate at decode level keep `MdbS`**, the source lookup's hypothesis only
for the root read from a non-null extra slot (gen 50's `cnode.decode_copy.mdbS`'s proof, moved and extended by the
move branch, `cdt.move_cap.mdbS`; that lemma is its instance). -/
theorem cnode.decode_copy.mdbSX (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hm : MdbS st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {lbl len buf dest : U64}
    (hl4 : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest)
    (hsrc : ∀ sl ∈ extra.val, sl ≠ 0#u64 → ∀ (i d : U64),
      cspace.lookup_source_slot st s (capA st s sl) i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄) :
    cnode.decode_copy st s lbl len buf extra dest ⦃ r => MdbS st OS r.2 ⦄ :=
  cnode.decode_copy.gen hO q hm hsrc (cnode.decode_copy.mvS hO hm hl4 hd hdc)
    (cnode.decode_copy.insS hO hm hl4 hd hdc)

set_option maxHeartbeats 2000000 in
/-- **CNode Copy / Mint at decode level keep `MdbS`** (module docstring). -/
theorem cnode.decode_copy.mdbS (hO : OSOK T Ω Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hm : MdbS st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {lbl len buf dest : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (hd : dest ∈ OS) (hdc : obj.sext48 dest = ok dest)
    (hsrc : ∀ (c : capability.Cap) (i d : U64),
      cspace.lookup_source_slot st s c i d ⦃ r => ∀ x, r = .Ok x → x ∈ OS ⦄) :
    cnode.decode_copy st s lbl len buf extra dest ⦃ r => MdbS st OS r.2 ⦄ :=
  cnode.decode_copy.mdbSX hO q hm (hl.elim Or.inl fun h => Or.inr (Or.inl h)) hd hdc fun _ _ _ i d => hsrc _ i d

end ST
end R
end W7

end

end Fl4ProofsA64.P1
