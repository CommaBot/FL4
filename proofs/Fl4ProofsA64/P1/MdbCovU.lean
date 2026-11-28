/-
P1 (aarch64, gen 61): **`hcd` of the retype from the untyped decode's destination lookup** (goal 2 of gen 61).

* **`untyped.retype_dest.cnode`**: `untyped.retype_dest` (untyped.rs:44–60) returns `Ok dest` only for a CNode cap
  `CNode dest r _ _` held by an `OS` slot (the extra slot itself at depth 0, else the slot `cspace.lookup_target_slot`
  finds from the extra slot's cap: gen 30's `lookup_tgt_in`) with the window inside the node, `off + win ≤ 2 ^ r`
  (the checks `off ≤ 2^r − 1`, `1 ≤ win`, `win ≤ 2^r − off`; `r < 64` from `RootOK.of_slot`).
* **`untyped.retype_dest.cov`**: hence each destination slot `djA dest off j`, `j < win`, is an `OS` slot (`CapIn`
  of the held CNode cap) and covered by an `OS` cap (MdbCovL's `SlotCov.cov`, `MdbST.reg`): the retype's `hdO` and
  `hcd` (l4v `ex_cte_cap_wp_to` of `retype_region`'s targets).
* **`untyped.retype.stAD`**: MdbCovR's `untyped.retype.stA` with `hdO` / `hcd` replaced by the decode's
  `retype_dest` result at the retype's state (the decode's `set_thread_state` restart keeps every cap: the caller
  rewrites the equation along `OSKeep`).

No named premise.
-/
import Fl4ProofsA64.P1.MdbUZK
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {Sg : Set U64}
variable {H : Heap} {Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

theorem cnode_of_some {c : capability.Cap} {d r : U64} (h : untyped.cnode_of c = ok (some (d, r))) :
    ∃ g b, c = .CNode d r g b := by
  cases c <;> simp [untyped.cnode_of] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨_, _, rfl⟩

theorem cnode_of_tot (c : capability.Cap) : ∃ o, untyped.cnode_of c = ok o := by
  cases c <;> exact ⟨_, rfl⟩

set_option hygiene false in
/-- `retype_dest`'s common tail from the node cap `c` read from the `OS` slot `y` (`hc : capA st s y = c`). -/
local macro "rdtail" : tactic => `(tactic| (
  obtain ⟨o, ho⟩ := cnode_of_tot c
  rw [ho, bind_ok]
  rcases o with _ | ⟨dest, radix⟩
  · simp only [WP.spec_ok]; try (intro d h; cases h)
  obtain ⟨g, b, rfl⟩ := cnode_of_some ho
  have hr64 : radix.val < 64 :=
    (RootOK.of_slot (c := .CNode dest radix g b) hT hy (by rw [capA_eq, hc])).2 dest radix g b rfl
  have h63 : 2 ^ radix.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  try dsimp only
  try simp only [lift, bind_ok]
  refine WP.spec_bind (shl1_val hr64) fun ns hns => ?_
  have hns1 : 1 ≤ ns.val := by rw [hns]; exact Nat.one_le_two_pow
  have hs1 : (core.num.U64.wrapping_sub ns 1#u64).val = ns.val - 1 := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega
  try simp only [lift, bind_ok]
  split
  · simp only [error.range, lift, bind_ok, WP.spec_ok]; try (intro d h; cases h)
  rename_i h1
  split
  · simp only [error.range, WP.spec_ok]; try (intro d h; cases h)
  split
  · simp only [error.range, WP.spec_ok]; try (intro d h; cases h)
  try simp only [lift, bind_ok]
  split
  · simp only [error.range, lift, bind_ok, WP.spec_ok]; try (intro d h; cases h)
  rename_i h4
  simp only [WP.spec_ok]
  intro d hdd
  cases hdd
  have h1' : off.val ≤ ns.val - 1 := by
    have := h1; simp only [gt_iff_lt, not_lt] at this
    have : off.val ≤ (core.num.U64.wrapping_sub ns 1#u64).val := this
    omega
  have hoff : (core.num.U64.wrapping_sub ns off).val = ns.val - off.val := by
    simp [core.num.U64.wrapping_sub_val_eq, U64.size_def, U64.numBits]; omega
  have h4' : win.val ≤ ns.val - off.val := by
    have := h4; simp only [gt_iff_lt, not_lt] at this
    have : win.val ≤ (core.num.U64.wrapping_sub ns off).val := this
    omega
  exact ⟨_, hy, radix, g, b, hc, by omega⟩))

set_option maxHeartbeats 2000000 in
/-- **`retype_dest`'s `Ok dest`: a held CNode cap of `dest` whose node holds the window** (module docstring). -/
theorem untyped.retype_dest.cnode {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) {x idx dep off win : U64}
    (hx : x ∈ OS) :
    untyped.retype_dest st s x idx dep off win ⦃ r => ∀ d, r = .Ok d →
      ∃ y ∈ OS, ∃ rd g b, capA st s y = .CNode d rd g b ∧ off.val + win.val ≤ 2 ^ rd.val ⦄ := by
  unfold untyped.retype_dest
  split
  · rw [capA_eq, bind_ok]
    have hy : x ∈ OS := hx
    generalize hc : capA st s x = c
    rdtail
  · rw [capA_eq, bind_ok]
    refine WP.spec_bind (lookup_tgt_in hT (capA st s x) (RootOK.of_slot hT hx (capA_eq s x)) idx dep)
      fun r hr => ?_
    rcases r with v | e
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      rw [capA_eq, bind_ok]
      have hy : v ∈ OS := hr v rfl
      generalize hc : capA st s v = c
      rdtail
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from,
        bind_tc_ok]
      first
      | exact (WP.spec_ok _).2 fun nc h => (by cases h)
      | (simp only [WP.spec_ok]; intro nc h; cases h)

/-- **The retype's `hdO` and `hcd` from `retype_dest`** (module docstring). -/
theorem untyped.retype_dest.cov (hO : OSOK T Ω Sg OS) {s : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hm : MdbST st OS s) {x idx dep off win dest : U64} (hx : x ∈ OS)
    (hd : untyped.retype_dest st s x idx dep off win = ok (.Ok dest)) :
    ∀ j, j < win.val → djA dest off j ∈ OS ∧ ∃ z ∈ OS, CovBy (capA st s z) (djA dest off j) := by
  have h := untyped.retype_dest.cnode (idx := idx) (dep := dep) (off := off) (win := win) hT hx
  rw [hd, WP.spec_ok] at h
  obtain ⟨y, hy, rd, g, b, hc, hle⟩ := h dest rfl
  intro j hj
  have hR := RootOK.of_slot hT hy (by rw [capA_eq, hc])
  have hr : rd.val < 64 := hR.2 dest rd g b rfl
  have h63 : 2 ^ rd.val ≤ 2 ^ 63 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hjv : (⟨BitVec.ofNat 64 j⟩ : U64).val = j := by
    show (BitVec.ofNat 64 j).toNat = j
    simp only [BitVec.toNat_ofNat]; omega
  have hi : (wa off ⟨BitVec.ofNat 64 j⟩).val < 2 ^ (rd.val % 64) := by
    rw [wa_val, hjv, Nat.mod_eq_of_lt (show off.val + j < 2 ^ 64 by omega), Nat.mod_eq_of_lt hr]; omega
  have hin : djA dest off j ∈ OS := hR.1.1 dest rd g b rfl _ hi
  refine ⟨hin, SlotCov.cov hO hm.reg (fun z hz p r g b h => (RootOK.of_slot hT hz (capA_eq s z)).2 p r g b h) hin
    ⟨y, hy, dest, rd, g, b, hc, _, hi, rfl⟩⟩

section arch
variable {A : Type _} {ar : machine.Arch A}

/-- **Retype carrying `StA`, the destination from `retype_dest`** (module docstring). -/
theorem untyped.retype.stAD {Sg : Set U64} (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) {s : S} {H' : Heap} (hSt : StA st H OS s) (a : A)
    {src p sb fi : U64} {dev : Bool} (hsrc : src ∈ OS) (hcs : capA st s src = .Untyped p sb fi dev)
    (nt us dcn off len base : U64) (device : Bool) (hdv : device = dev) (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : base.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ base.val)
    (hAw : base.val + len.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ base.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ base.val + len.val * 2 ^ (zA nt.val us).val))
    (hnA : Aligned (nwA st s)) (hnC : ¬ W7.CapW H.tcbs H.omega Sg (nwA st s))
    (hnF : ∀ u ∈ OS, ∀ p b i, capA st s u = .Untyped p b i false →
      (nwA st s).val < p.val + i.val ∨ p.val + 2 ^ b.val ≤ (nwA st s).val)
    (hhd0 : L.mem s (nwA st s) = 0#u64 ∨ H (L.mem s (nwA st s)) = some .tcb)
    (hdn : ∀ j, j < len.val → capA st s (djA dcn off j) = .Null)
    (hdc : ∀ j, j < len.val → obj.sext48 (djA dcn off j) = ok (djA dcn off j))
    (hinj : ∀ j l, j < len.val → l < len.val → djA dcn off j = djA dcn off l → j = l)
    (hcan : ∀ j, j < len.val → CapRt.Canonical (bjA base (zA nt.val us) j)) (hus : us.val < 64)
    {Rp Nt : Set U64} (hT : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s) {x idx dep : U64} (hx : x ∈ OS)
    (hd : untyped.retype_dest st s x idx dep off len = ok (.Ok dcn)) :
    untyped.retype st ar s a src false base nt us dcn off len device ⦃ r => r.1 = .Ok () ∧
      StA st H' OS r.2.1 ⦄ :=
  have hdc' := untyped.retype_dest.cov hO hT hSt.1 hx hd
  untyped.retype.stA hA hH hO hSt a hsrc hcs nt us dcn off len base device hdv hn hz hdev hal hfi hA0 hAw hH' hnA hnC
    hnF hhd0 (fun j hj => (hdc' j hj).1) hdn hdc hinj hcan hus fun j hj => (hdc' j hj).2

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1
