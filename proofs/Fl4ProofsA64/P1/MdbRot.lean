/-
P1 (aarch64, gen 52): **CNode Rotate at decode level keeps the MDB facts**, and the whole CNode copy family
(Copy / Mint / Move / Mutate / Rotate) through `cnode.decode` / `decode_invocation` in one statement.

* **`cdt.swap.mdbS`**: `cdt::swap` of two distinct canonical `OS` slots holding non-null caps, writing encodable
  non-null caps `AlikeA` the ones they replace, keeps `MdbS` — `cdt.swap.lrW` (MdbStepF, gen 48's `swap.lr` proof
  moved to any encodable caps), the two slots' old cap words written back (links unchanged), the renamed ghost by
  `swap_post` (MdbNull, `swap.mdbN`'s argument moved), then `MdbS.alike` (MdbMove) to the real end state — the same
  write-back as gen 51's `cdt.move_cap.mdbS`.
* **`cnode.rotate_slots.inOS`**: every `Ok (src, pivot)` of `rotate_slots` (cnode.rs:150–173) from two extra slots of
  `OS` has `src`, `pivot` in `OS` (`lookup_src_in` / `lookup_piv_in`, roots `RootOK.of_slot`), `pivot ≠ src`,
  `pivot ≠ dest`, both caps non-null, and `dest` null when `src ≠ dest` (`ensure_empty_slot`).
* **`cnode.decode_rotate.mdbS`** (cnode.rs:126–147): error leaves return the start state; after `set_thread_state`
  (`stt_osk`) either `swap` (`src = dest`: `cdt.swap.mdbS`, new caps from `update_cap_data true`,
  `objects.update_cap_data.al` / `.wf`) or two `move_cap`s (pivot → `dest`, then source → the emptied pivot slot:
  `cdt.move_cap.mdbS` twice, the first one's caps from `cdt.move_cap.lr`). Canonicity of `dest` / `pivot` / `src`
  from `OSOK.canon` under `WinOK`.
* **`cnode.decode.cnode_mdbS`** / **`syscall.decode_invocation.cnode_mdbS`**: Copy / Mint / Move / Mutate / Rotate
  in one statement (gen 51's `copy_mdbS` for the first four).

* (gen 60) **`cnode.decode_rotate.gen`** (steps `RtSw` / `RtMv`), **`cnode.decode.rotG`**, **`cnode.decode.cnodeG`**:
  the one Rotate traversal and the five-label dispatch for any invariant `P`; the `MdbS` tops above are their
  instances (steps `cnode.decode_rotate.swS` / `mvS`).

Case hypotheses as gen 51's `copy_mdbS` (decode inputs: the invoked slot in `OS`, extra slots `0` or in `OS`;
`WinOK T Ω`). No named premise.
-/
import Fl4ProofsA64.P1.MdbLook
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

theorem capA_dec (s : S) (x : U64) :
    capability.Cap.decode (L.mem s x) (L.mem s (wa x 8#u64)) = ok (capA st s x) := by
  have e := capA_eq (st := st) s x; rw [DPF.slot_cap_dec] at e; exact e

set_option maxHeartbeats 2000000 in
/-- **`swap` of `AlikeA` caps keeps `MdbS`** (module docstring). -/
theorem cdt.swap.mdbS (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {x1 x2 : U64} {c1 c2 : capability.Cap}
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (h10 : capA st s x1 ≠ .Null) (h20 : capA st s x2 ≠ .Null) (hw1 : CapRt.EncWf c1) (hw2 : CapRt.EncWf c2)
    (hn1 : c1 ≠ .Null) (hn2 : c2 ≠ .Null) (ha1 : AlikeA c1 (capA st s x1)) (ha2 : AlikeA c2 (capA st s x2)) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => MdbS st OS s' ⦄ := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm
  have h0 : ∀ y ∈ OS, y ≠ 0#u64 := hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have F := hM.lkF h0
  have g1 : x1 ∈ G.flatten := (hM.members x1).2 ⟨hx1, h10⟩
  have g2 : x2 ∈ G.flatten := (hM.members x2).2 ⟨hx2, h20⟩
  refine WP.spec_mono (cdt.swap.lrW hO (LR.self s) hx1 hx2 hne hs1 hs2 hw1 hw2
    (fun h => inOS _ (F.pvm _ g1 h)) (fun h => inOS _ (F.nxm _ g1 h))
    (fun h => inOS _ (F.pvm _ g2 h)) (fun h => inOS _ (F.nxm _ g2 h))) ?_
  rintro s' ⟨hL, e1, e2, ek⟩
  -- write the old caps back: `x1` ← `x2`'s old words, `x2` ← `x1`'s old words
  have La := hL.wr2 hO hx1 (w0 := L.mem s x2) (w1 := L.mem s (wa x2 8#u64))
  have la := set_cap_links (st := st) (s := s') (w0 := L.mem s x2) (w1 := L.mem s (wa x2 8#u64)) hO hx1
  have ca1 : capA st (L.wr (L.wr s' x1 (L.mem s x2)) (wa x1 8#u64) (L.mem s (wa x2 8#u64))) x1 = capA st s x2 :=
    capA_wr2_self hO hx1 (capA_dec s x2)
  have cao : ∀ y ∈ OS, y ≠ x1 →
      capA st (L.wr (L.wr s' x1 (L.mem s x2)) (wa x1 8#u64) (L.mem s (wa x2 8#u64))) y = capA st s' y :=
    fun y hy n => capA_wr2_other hO hx1 hy n
  generalize L.wr (L.wr s' x1 (L.mem s x2)) (wa x1 8#u64) (L.mem s (wa x2 8#u64)) = sa at La la ca1 cao
  have Lb := La.wr2 hO hx2 (w0 := L.mem s x1) (w1 := L.mem s (wa x1 8#u64))
  have lb := set_cap_links (st := st) (s := sa) (w0 := L.mem s x1) (w1 := L.mem s (wa x1 8#u64)) hO hx2
  have cb2 : capA st (L.wr (L.wr sa x2 (L.mem s x1)) (wa x2 8#u64) (L.mem s (wa x1 8#u64))) x2 = capA st s x1 :=
    capA_wr2_self hO hx2 (capA_dec s x1)
  have cbo : ∀ y ∈ OS, y ≠ x2 →
      capA st (L.wr (L.wr sa x2 (L.mem s x1)) (wa x2 8#u64) (L.mem s (wa x1 8#u64))) y = capA st sa y :=
    fun y hy n => capA_wr2_other hO hx2 hy n
  generalize L.wr (L.wr sa x2 (L.mem s x1)) (wa x2 8#u64) (L.mem s (wa x1 8#u64)) = sb at Lb lb cb2 cbo
  obtain ⟨P1, P2, P3, P4, P5⟩ := swap_post h0 hM hRO hK hN hC hx1 g2 hne Lb
    (by rw [cbo x1 hx1 hne, ca1]) cb2 (fun y hy n1 n2 => by rw [cbo y hy n2, cao y hy n1]; exact ek y hy n1 n2)
  refine MdbS.alike ⟨_, P1, P2, P3, P4, P5⟩
    (fun x hx => ⟨((lb x hx).1.trans (la x hx).1).symm, ((lb x hx).2.trans (la x hx).2).symm⟩)
    (fun x hx => ?_) (fun x hx => ?_)
  · by_cases a1 : x = x1
    · subst a1; rw [e1, cbo x hx hne, ca1]; exact ⟨fun h => absurd h hn2, fun h => absurd h h20⟩
    by_cases a2 : x = x2
    · subst a2; rw [e2, cb2]; exact ⟨fun h => absurd h hn1, fun h => absurd h h10⟩
    · rw [cbo x hx a2, cao x hx a1]
  · by_cases a1 : x = x1
    · subst a1; rw [e1, cbo x hx hne, ca1]; exact ha2
    by_cases a2 : x = x2
    · subst a2; rw [e2, cb2]; exact ha1
    · rw [cbo x hx a2, cao x hx a1]; exact AlikeA.refl _

theorem slot_ne (a b : obj.Slot) :
    core.cmp.PartialEq.ne.trait_default obj.Slot.Insts.CoreCmpPartialEqSlot a b = ok (decide (a ≠ b)) := by
  unfold core.cmp.PartialEq.ne.trait_default core.cmp.PartialEq.ne.default
  simp [obj.Slot.Insts.CoreCmpPartialEqSlot.eq]
  exact ⟨fun h => by rw [h], fun h => by first | exact UScalar.eq_of_val_eq h | (cases a; cases b; simp_all)⟩

set_option hygiene false in
/-- An error leaf of `rotate_slots`: an `Err` result. -/
local macro "rleaf" : tactic => `(tactic| first
  | (rw [WP.spec_ok]; intro x y h; cases h)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source,
      WP.spec_ok]
     intro x y h; cases h))

set_option maxHeartbeats 2000000 in
/-- **`rotate_slots`'s slots** (module docstring). -/
theorem cnode.rotate_slots.inOS {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (buf : U64)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {e0 e1 : U64}
    (h0e : Aeneas.Std.Array.index_usize extra 0#usize = ok e0) (h1e : Aeneas.Std.Array.index_usize extra 1#usize = ok e1)
    (h0 : e0 ∈ OS) (h1 : e1 ∈ OS) (dest : U64) :
    cnode.rotate_slots st s buf extra dest ⦃ r => ∀ x y, r = .Ok (x, y) → x ∈ OS ∧ y ∈ OS ∧ y ≠ x ∧ y ≠ dest ∧
      capA st s x ≠ .Null ∧ capA st s y ≠ .Null ∧ (x ≠ dest → capA st s dest = .Null) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.rotate_slots
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun pi _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun pd _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun si _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun sd _ => ?_
  rw [h0e, bind_ok, capA_eq s e0, bind_ok, h1e, bind_ok, capA_eq s e1, bind_ok]
  refine WP.spec_bind (lookup_src_in hT _ (RootOK.of_slot hT h1 (capA_eq s e1)) si sd) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rleaf
  have hv : v ∈ OS := hr v rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (lookup_piv_in hT _ (RootOK.of_slot hT h0 (capA_eq s e0)) pi pd) fun r1 hr1 => ?_
  rcases r1 with p | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rleaf
  have hp : p ∈ OS := hr1 p rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, obj.Slot.Insts.CoreCmpPartialEqSlot.eq, slot_ne]
  by_cases hpv : p = v
  · simp only [hpv, decide_true, ↓reduceIte]
    rleaf
  simp only [hpv, decide_false, Bool.false_eq_true, ↓reduceIte]
  by_cases hpd : p = dest
  · simp only [hpd, decide_true, ↓reduceIte]
    rleaf
  simp only [hpd, decide_false, Bool.false_eq_true, ↓reduceIte]
  -- the two cap checks, shared by both branches
  have tail : (v ≠ dest → capA st s dest = .Null) →
      (do
        let c ← obj.Slot.cap st v s
        let b3 ← capability.Cap.is_null c
        if b3
        then cnode.missing_source (obj.Slot × obj.Slot) sd true
        else
          let c1 ← obj.Slot.cap st p s
          let b4 ← capability.Cap.is_null c1
          if b4
          then cnode.missing_source (obj.Slot × obj.Slot) pd false
          else ok (core.result.Result.Ok (v, p))) ⦃ r => ∀ x y, r = .Ok (x, y) → x ∈ OS ∧ y ∈ OS ∧ y ≠ x ∧
            y ≠ dest ∧ capA st s x ≠ .Null ∧ capA st s y ≠ .Null ∧ (x ≠ dest → capA st s dest = .Null) ⦄ := by
    intro hdn
    rw [capA_eq s v, bind_ok]
    by_cases hv0 : capA st s v = .Null
    · rw [hv0, is_null_t, bind_ok]
      simp only [↓reduceIte]
      rleaf
    rw [is_null_f hv0, bind_ok]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [capA_eq s p, bind_ok]
    by_cases hp0 : capA st s p = .Null
    · rw [hp0, is_null_t, bind_ok]
      simp only [↓reduceIte]
      rleaf
    rw [is_null_f hp0, bind_ok]
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    intro x y h
    cases h
    exact ⟨hv, hp, hpv, hpd, hv0, hp0, hdn⟩
  by_cases hvd : v = dest
  · simp only [hvd, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, bind_ok]
    subst hvd
    exact tail fun h => absurd rfl h
  simp only [hvd, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, bind_ok]
  by_cases hd0 : capA st s dest = .Null
  swap
  · unfold cdt.ensure_empty_slot
    rw [capA_eq, bind_ok, is_null_f hd0, bind_ok]
    simp only [Bool.false_eq_true, ↓reduceIte, bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    rleaf
  have ee : cdt.ensure_empty_slot st s dest = ok (core.result.Result.Ok ()) := by
    unfold cdt.ensure_empty_slot
    rw [capA_eq, bind_ok, hd0, is_null_t, bind_ok]; rfl
  rw [ee, bind_ok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  exact tail fun _ => hd0

set_option hygiene false in
/-- An error leaf of the decode: the start state, `MdbS` held. -/
local macro "mleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 hm
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact (WP.spec_ok _).2 hm | exact hm))

/-- (gen 60) **CNode Rotate's `swap` step (`src = dest`), for an invariant `P`**: from the decode's start state
`s`, after `set_thread_state` (`OSKeep`), `rotate_slots`' facts and the two `update_cap_data` results. -/
def RtSw (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (dest : U64) (P : S → Prop) : Prop :=
  ∀ (s3 : S) (src pv sd pd : U64) (ns np : capability.Cap), OSKeep st OS s s3 →
    WritesIn st s s3 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    src ∈ OS → pv ∈ OS → pv ≠ src →
    pv ≠ dest → capA st s src ≠ .Null → capA st s pv ≠ .Null → src = dest →
    objects.update_cap_data true sd (capA st s src) = ok ns → objects.update_cap_data true pd (capA st s pv) = ok np →
    ns ≠ .Null → np ≠ .Null → cdt.swap st s3 ns src np pv ⦃ s4 => P s4 ⦄

/-- (gen 60) **CNode Rotate's two `move_cap` steps (`src ≠ dest`), for an invariant `P`.** -/
def RtMv (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (dest : U64) (P : S → Prop) : Prop :=
  ∀ (s3 : S) (src pv sd pd : U64) (ns np : capability.Cap), OSKeep st OS s s3 →
    WritesIn st s s3 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) →
    src ∈ OS → pv ∈ OS → pv ≠ src →
    pv ≠ dest → capA st s src ≠ .Null → capA st s pv ≠ .Null → src ≠ dest → capA st s dest = .Null →
    objects.update_cap_data true sd (capA st s src) = ok ns → objects.update_cap_data true pd (capA st s pv) = ok np →
    ns ≠ .Null → np ≠ .Null →
    cdt.move_cap st s3 np pv dest ⦃ s4 => cdt.move_cap st s4 ns src pv ⦃ s5 => P s5 ⦄ ⦄

theorem RtSw.and {s : S} {dest : U64} {P P' : S → Prop} (h : RtSw st OS s dest P) (h' : RtSw st OS s dest P') :
    RtSw st OS s dest fun x => P x ∧ P' x :=
  fun s3 src pv sd pd ns np k w a1 a2 a3 a4 a5 a6 a7 e1 e2 n1 n2 =>
    WP.spec_and (h s3 src pv sd pd ns np k w a1 a2 a3 a4 a5 a6 a7 e1 e2 n1 n2)
      (h' s3 src pv sd pd ns np k w a1 a2 a3 a4 a5 a6 a7 e1 e2 n1 n2)

theorem RtMv.and {s : S} {dest : U64} {P P' : S → Prop} (h : RtMv st OS s dest P) (h' : RtMv st OS s dest P') :
    RtMv st OS s dest fun x => P x ∧ P' x :=
  fun s3 src pv sd pd ns np k w a1 a2 a3 a4 a5 a6 a7 a8 e1 e2 n1 n2 =>
    WP.spec_mono (WP.spec_and (h s3 src pv sd pd ns np k w a1 a2 a3 a4 a5 a6 a7 a8 e1 e2 n1 n2)
      (h' s3 src pv sd pd ns np k w a1 a2 a3 a4 a5 a6 a7 a8 e1 e2 n1 n2)) fun _ h2 => WP.spec_and h2.1 h2.2

set_option maxHeartbeats 4000000 in
/-- (gen 60) **The one CNode Rotate traversal at decode level** (gen 52's `decode_rotate.mdbS` proof, the steps
abstracted): any invariant `P` of the start state kept by the `swap` step (`RtSw`) and the two `move_cap` steps
(`RtMv`) holds at every outcome. -/
theorem cnode.decode_rotate.gen (hO : OSOK T Ω Sg OS) {X : Set U64}
    {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) {P : S → Prop} (hm : P s) {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {len buf dest : U64} (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS)
    (hsw : RtSw st OS s dest P) (hmv : RtMv st OS s dest P) :
    cnode.decode_rotate st s len buf extra dest ⦃ r => P r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode_rotate
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · mleaf
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  have hl1 : (1#usize).val < extra.val.length := by rw [extra.property]; simp
  obtain ⟨e0, h0e, h0v⟩ := spec_ex (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0)
  obtain ⟨e1, h1e, h1v⟩ := spec_ex (Aeneas.Std.Array.index_usize_spec extra 1#usize hl1)
  have m0 : e0 ∈ extra.val := h0v ▸ List.getElem_mem hl0
  have m1 : e1 ∈ extra.val := h1v ▸ List.getElem_mem hl1
  rw [h0e, bind_ok]
  simp only [obj.Slot.is_null, bind_ok]
  split
  · mleaf
  rename_i n0'
  have n0 : e0 ≠ 0#u64 := by simpa using n0'
  rw [h1e, bind_ok]
  try simp only [obj.Slot.is_null, bind_ok]
  split
  · mleaf
  rename_i n1'
  have n1 : e1 ≠ 0#u64 := by simpa using n1'
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have hct : ct ∈ T := by rw [ect]; exact q.curT
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun pd _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun sd _ => ?_
  refine WP.spec_bind (cnode.rotate_slots.inOS hT buf h0e h1e (hx e0 m0 n0) (hx e1 m1 n1) dest) fun r hr => ?_
  rcases r with ⟨src, pv⟩ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    mleaf
  obtain ⟨hsrc, hpv, hps, hpd, hs0, hp0, hdn⟩ := hr _ _ rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  rw [capA_eq s src, bind_ok]
  refine WP.spec_bind (spec_eqv (P0.objects.update_cap_data.p0 true sd (capA st s src))) fun ns u1 => ?_
  rw [capA_eq s pv, bind_ok]
  refine WP.spec_bind (spec_eqv (P0.objects.update_cap_data.p0 true pd (capA st s pv))) fun np u2 => ?_
  by_cases hns : ns = .Null
  · subst hns
    rw [is_null_t, bind_ok]
    simp only [↓reduceIte, bind_ok]
    mleaf
  rw [is_null_f hns, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hnp : np = .Null
  · subst hnp
    rw [is_null_t, bind_ok]
    simp only [↓reduceIte, bind_ok]
    mleaf
  rw [is_null_f hnp, bind_ok]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine WP.spec_bind (sched.set_thread_state.vckW2 s ct sched.TS_RESTART q.tcbs (q.nodes _ q.cur) hct)
    fun s3 hw => ?_
  have k3 : OSKeep st OS s s3 := stt_osk hO q hct hw.1
  have w3 : WritesIn st s s3
      (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
    have e : ct = L.curW s := ect
    rw [← e]; exact hw.1
  simp only [obj.Slot.Insts.CoreCmpPartialEqSlot.eq, bind_ok]
  by_cases hsd : src = dest
  · -- `swap`
    simp only [hsd, decide_true, ↓reduceIte]
    have hsw' := hsw s3 _ _ sd pd ns np k3 w3 hsrc hpv hps hpd hs0 hp0 hsd u1.1 u2.1 hns hnp
    subst hsd
    exact WP.spec_bind hsw' fun s4 h4 => (WP.spec_ok _).2 h4
  · -- two `move_cap`s: the pivot into `dest`, then the source into the pivot slot
    simp only [hsd, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine WP.spec_bind (hmv s3 src pv sd pd ns np k3 w3 hsrc hpv hps hpd hs0 hp0 hsd (hdn hsd) u1.1 u2.1 hns hnp)
      fun s4 h4 => ?_
    exact WP.spec_bind h4 fun s5 h5 => (WP.spec_ok _).2 h5

/-- (gen 60) **`MdbS`'s `swap` step** (gen 52's `decode_rotate.mdbS` swap branch). -/
theorem cnode.decode_rotate.swS (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {s : S} (hm : MdbS st OS s) {dest : U64} :
    RtSw st OS s dest (MdbS st OS) := by
  intro s3 src pv sd pd ns np k3 _ hsrc hpv hps hpd hs0 hp0 hsd e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => by
    unfold capA; rw [(k3 y hy).1, (k3 y hy).2.1]
  have has := objects.update_cap_data.al true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have hap := objects.update_cap_data.al true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at has hwns
  rw [e2, WP.spec_ok] at hap hwnp
  exact cdt.swap.mdbS hO (hm.keep k3) hsrc hpv (Ne.symm hps) (hO.canon hW hsrc) (hO.canon hW hpv)
    (by rw [hc3 src hsrc]; exact hs0) (by rw [hc3 pv hpv]; exact hp0) hwns hwnp hns hnp
    (by rw [hc3 src hsrc]; exact has.ne hns) (by rw [hc3 pv hpv]; exact hap.ne hnp)

/-- (gen 60) **`MdbS`'s two `move_cap` steps** (gen 52's `decode_rotate.mdbS` move branch). -/
theorem cnode.decode_rotate.mvS (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {s : S} (hm : MdbS st OS s) {dest : U64}
    (hd : dest ∈ OS) : RtMv st OS s dest (MdbS st OS) := by
  intro s3 src pv sd pd ns np k3 _ hsrc hpv hps hpd hs0 hp0 hsd hd0 e1 e2 hns hnp
  have hc3 : ∀ y ∈ OS, capA st s3 y = capA st s y := fun y hy => by
    unfold capA; rw [(k3 y hy).1, (k3 y hy).2.1]
  have has := objects.update_cap_data.al true sd (capA st s src)
  have hwns := objects.update_cap_data.wf true sd (capA st s src) (CapRt.decodeF_encWf _ _)
  have hap := objects.update_cap_data.al true pd (capA st s pv)
  have hwnp := objects.update_cap_data.wf true pd (capA st s pv) (CapRt.decodeF_encWf _ _)
  rw [e1, WP.spec_ok] at has hwns
  rw [e2, WP.spec_ok] at hap hwnp
  have m3 := hm.keep k3
  obtain ⟨G, hM, -, -, -, -⟩ := id m3
  have F := hM.lkF hO.nz
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have gp : pv ∈ G.flatten := (hM.members pv).2 ⟨hpv, by rw [hc3 pv hpv]; exact hp0⟩
  refine WP.spec_mono (WP.spec_and
    (cdt.move_cap.mdbS hO m3 hpv (by rw [hc3 pv hpv]; exact hp0) hd (by rw [hc3 dest hd]; exact hd0)
      (hO.canon hW hd) hwnp hnp (by rw [hc3 pv hpv]; exact hap.ne hnp))
    (cdt.move_cap.lr hO (LR.self s3) hpv hd hpd (hO.canon hW hd) hwnp
      (fun h => inOS _ (F.pvm _ gp h)) (fun h => inOS _ (F.nxm _ gp h)))) fun s4 h4 => ?_
  obtain ⟨m4, -, -, e4p, e4k⟩ := h4
  have c4s : capA st s4 src = capA st s src := by rw [e4k src hsrc hps.symm hsd, hc3 src hsrc]
  exact cdt.move_cap.mdbS hO m4 hsrc (by rw [c4s]; exact hs0) hpv e4p (hO.canon hW hpv) hwns hns
    (by rw [c4s]; exact has.ne hns)

/-- **CNode Rotate at decode level keeps `MdbS`** (module docstring). -/
theorem cnode.decode_rotate.mdbS (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω) {X : Set U64}
    {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S} (q : SchedQueuesInvX st T Cs Ω H X s Q Rq)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbS st OS s) {extra : Aeneas.Std.Array obj.Slot 3#usize}
    {len buf dest : U64} (hd : dest ∈ OS) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode_rotate st s len buf extra dest ⦃ r => MdbS st OS r.2 ⦄ :=
  cnode.decode_rotate.gen hO q hT hm hx (cnode.decode_rotate.swS hO hW hm) (cnode.decode_rotate.mvS hO hW hm hd)

theorem lbl_rot_ge : fl4_abi.label.CNodeRotate ≥ fl4_abi.label.CNodeCopy := by
  first | decide | (simp only [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeRotate]; decide) | simp [fl4_abi.label.CNodeCopy, fl4_abi.label.CNodeRotate]

theorem lbl_rot_gt : ¬ fl4_abi.label.CNodeRotate ≤ fl4_abi.label.CNodeMutate := by
  first | decide | (simp only [fl4_abi.label.CNodeMutate, fl4_abi.label.CNodeRotate]; decide) | simp [fl4_abi.label.CNodeMutate, fl4_abi.label.CNodeRotate]

theorem lbl_rot_ne (l : U64) (h : l = fl4_abi.label.CNodeRevoke ∨ l = fl4_abi.label.CNodeDelete ∨
    l = fl4_abi.label.CNodeCancelBadgedSends) : ¬ fl4_abi.label.CNodeRotate = l := by
  rcases h with rfl | rfl | rfl <;> (first | decide | (simp only [fl4_abi.label.CNodeRevoke, fl4_abi.label.CNodeDelete, fl4_abi.label.CNodeCancelBadgedSends, fl4_abi.label.CNodeRotate]; decide) | simp [fl4_abi.label.CNodeRevoke, fl4_abi.label.CNodeDelete, fl4_abi.label.CNodeCancelBadgedSends, fl4_abi.label.CNodeRotate])

set_option maxHeartbeats 2000000 in
/-- (gen 60) **`cnode.decode` at CNode Rotate, for an invariant `P`** (gen 52's `rot_mdbS` traversal, abstracted;
`Dq` as `cnode.decode.copyG`). -/
theorem cnode.decode.rotG {A : Type _} {ar : machine.Arch A} {s : S} {P : S → Prop} (hm : P s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {len buf : U64} (c : capability.Cap) {Dq : U64 → Prop}
    (hlk : ∀ i d : U64, cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → Dq x ⦄)
    (hin : ∀ dest, Dq dest → cnode.decode_rotate st s len buf extra dest ⦃ r => P r.2 ⦄) :
    cnode.decode st ar s a fl4_abi.label.CNodeRotate len c buf extra ⦃ r s' _ => P s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · mleaf
  split
  · mleaf
  split
  · mleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (hlk idx dep) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    mleaf
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  rw [if_pos lbl_rot_ge, if_neg lbl_rot_gt, if_neg (lbl_rot_ne _ (Or.inl rfl)),
    if_neg (lbl_rot_ne _ (Or.inr (Or.inl rfl))), if_neg (lbl_rot_ne _ (Or.inr (Or.inr rfl))), if_pos trivial]
  refine WP.spec_bind (hin v (hr v rfl)) fun r2 h2 => ?_
  rcases r2 with ⟨r1, s1⟩
  exact (WP.spec_ok _).2 h2

/-- (gen 60) **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate, for an invariant `P`**: the dispatch
of gen 52's `cnode_mdbS`, onto `copyG` / `rotG`. -/
theorem cnode.decode.cnodeG {A : Type _} {ar : machine.Arch A} {s : S} {P : S → Prop} (hm : P s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) {Dq : U64 → Prop}
    (hlk : ∀ i d : U64, cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → Dq x ⦄)
    (hcp : (lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate) → ∀ dest, Dq dest → cnode.decode_copy st s lbl len buf extra dest ⦃ r => P r.2 ⦄)
    (hrt : ∀ dest, Dq dest → cnode.decode_rotate st s len buf extra dest ⦃ r => P r.2 ⦄) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => P s' ⦄ := by
  rcases hl with h | h | h | h | rfl
  · exact cnode.decode.copyG hm a (Or.inl h) c hlk (hcp (Or.inl h))
  · exact cnode.decode.copyG hm a (Or.inr (Or.inl h)) c hlk (hcp (Or.inr (Or.inl h)))
  · exact cnode.decode.copyG hm a (Or.inr (Or.inr (Or.inl h))) c hlk (hcp (Or.inr (Or.inr (Or.inl h))))
  · exact cnode.decode.copyG hm a (Or.inr (Or.inr (Or.inr h))) c hlk (hcp (Or.inr (Or.inr (Or.inr h))))
  · exact cnode.decode.rotG hm a c hlk hrt

/-- **`cnode.decode` at CNode Rotate keeps `MdbS`** (module docstring). -/
theorem cnode.decode.rot_mdbS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbS st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {len buf : U64}
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a fl4_abi.label.CNodeRotate len c buf extra ⦃ r s' _ => MdbS st OS s' ⦄ :=
  cnode.decode.rotG hm a c (lookup_tgt_in hT c hc) fun _ hv => cnode.decode_rotate.mdbS hO hW q hT hm hv hx

/-- **`cnode.decode` at CNode Copy / Mint / Move / Mutate / Rotate keeps `MdbS`** (module docstring). -/
theorem cnode.decode.cnode_mdbS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hW : WinOK T Ω)
    {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbS st OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) {lbl len buf : U64}
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (c : capability.Cap) (hc : RootOK OS c) (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => MdbS st OS s' ⦄ :=
  cnode.decode.cnodeG hm a hl c (lookup_tgt_in hT c hc)
    (fun hl4 _ hv => cnode.decode_copy.mdbSX hO q hm hl4 hv (hO.canon hW hv) fun sl hsl hs0 i d =>
      lookup_src_in hT _ (RootOK.of_slot hT (hx sl hsl hs0) (capA_eq s sl)) i d)
    fun _ hv => cnode.decode_rotate.mdbS hO hW q hT hm hv hx

/-- **CNode Copy / Mint / Move / Mutate / Rotate at `decode_invocation`** of a CNode cap read from an `OS` slot
keep `MdbS`. -/
theorem syscall.decode_invocation.cnode_mdbS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hW : WinOK T Ω) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64} {s : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q Rq) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hm : MdbS st OS s)
    (a : A) {lbl : U64} (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint ∨ lbl = fl4_abi.label.CNodeMove ∨
      lbl = fl4_abi.label.CNodeMutate ∨ lbl = fl4_abi.label.CNodeRotate)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS) :
    syscall.decode_invocation st ar s a lbl len slot cap blk call don fp buf extra ⦃ r s' _ => MdbS st OS s' ⦄ :=
  syscall.decode_invocation.cnodeG hm a len slot cap blk call don fp buf extra hf
    (cnode.decode.cnode_mdbS hO hW q hT hm a hl cap (RootOK.of_slot hT hslot hcap) hx)

end ST
end R
end W7

end

end Fl4ProofsA64.P1
