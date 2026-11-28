/-
P1 (aarch64, gen 62): **the carried bundle `StZ` at the untyped decode** (goal 2 of gen 62) — QueueDecUt's one
traversal of `untyped::decode` for any post (`untyped.decode.decG`, gen 62, `dec` its instance) with `StZ`:

* **`StZ.restart`**: the decode's `set_thread_state` restart (the current TCB's `STATE` word, the core's
  `SCHED_ACTION` node word; `stt_osk`: no `OS` slot word) keeps `StZ` — caps kept (`OSKeep`), `UtZeroA` by
  `UtZeroA.stt` with `hnS` from `KsOffA` (MdbUZK), `KsOffA` by `UBm.keepO`; **`StZ.restartEq`**: the same from the
  restart's equation.
* **`untyped.retype.stZU`**: a non-reset retype the decode checked (`UtArgs … false …` at the decode's start `s0`,
  run from the restart state `s2`) carries `StZ`: MdbZK's `untyped.retype.stZQ` with the destination's slots in `OS`
  and covered (`hdO` / `hcd`) from `UtArgs`'s `retype_dest` equation (MdbCovU's `retype_dest.cov` at `s0`, moved to
  `s2` by `OSKeep`), canonical (`hdc`, `OSOK.canon`), and the source cap read at `s2` (`OSKeep`). The arithmetic of
  the decode's size / alignment / window checks against the free index (`hn`, `hz`, `hus`, `hal`, `hfi`, `hA0`,
  `hAw`, `hinj`, `hcan`), the empty window (`hdn`, `ensure_empty_slots`), the device kinds (`hdev`) and the heap
  growth (`hH'`) remain case hypotheses (the x86 derivations are P3 `retCtx_of_args` / `ensure_empty_slots_eq`
  over the spec relation; their A64 P1 form is owed).
* **`untyped.decode.stZ`**: `untyped::decode` (Untyped_Retype) keeps `StZ` (some grown heap): error leaves at the
  start state, the shared-frame extension (`hsh`, case hypothesis), the retype after the restart (`hRet`: from
  `StZ` at the restart state; for the non-reset case `untyped.retype.stZU` discharges it, the reset case is the
  chunked RAM reset loop, owed).

No named premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.MdbZK
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts Fl4Proofs.P3

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {Sg : Set U64}
variable {H : Heap} {Cs Rp Nt : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

variable {OS : Set U64}

/-- **The decode's restart keeps `StZ`** (module docstring). -/
theorem StZ.restart (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s s2 : S} (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq)
    (h : StZ st H Cs OS s) (k : OSKeep st OS s s2)
    (w : WritesIn st s s2 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    StZ st H Cs OS s2 := by
  obtain ⟨⟨hS, hR, hV, hZ, hC⟩, hz, hK⟩ := h
  exact ⟨⟨MdbST.keepO hO hS k, UtRev.keep hR k, ValidUntypedA.keepO hV k,
    UtZeroA.stt hH hV hZ q.curT (KsOffA.hnS hK q) k w, CoverA.keepO hC k⟩,
    ZombiesFinal.recap hz fun _ hy => Or.inl (k.capA hy), KsOffA.of_ub hK w.1 (UBm.keepO k)⟩

/-- **The restart's equation gives its frame** (`sched.set_thread_state.vckW2`, `stt_osk`). -/
theorem restart_frame (hO : OSOK H.tcbs H.omega Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s s2 : S} (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq)
    (e : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s2) :
    OSKeep st OS s s2 ∧
      WritesIn st s s2 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) := by
  have h := sched.set_thread_state.vckW2 s (L.curW s) sched.TS_RESTART q.tcbs (q.nodes _ q.cur) q.curT
  rw [e, WP.spec_ok] at h
  exact ⟨stt_osk hO q q.curT h.1, h.1⟩

theorem StZ.restartEq (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} {s s2 : S} (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq)
    (h : StZ st H Cs OS s) (e : sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s2) :
    StZ st H Cs OS s2 :=
  StZ.restart hH hO q h (restart_frame hO q e).1 (restart_frame hO q e).2

section arch
variable {A : Type _} {ar : machine.Arch A}

/-- **A non-reset retype the decode checked carries `StZ`** (module docstring). -/
theorem untyped.retype.stZU (hA : P0.ArchTotal ar) (hH : HeapOK H)
    (hO : OSOK H.tcbs H.omega Sg OS) (hW : WinOK H.tcbs H.omega) {s0 s2 : S} {H' : Heap}
    (hT0 : SlotTy st H.tcbs H.omega Sg H Rp Nt OS s0) (hS0 : MdbST st OS s0) (k : OSKeep st OS s0 s2)
    (hSt : StZ st H Cs OS s2) {X : Set U64} {Q : U64 → U64 → List U64} {Rq : U64 → List U64}
    (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s2 Q Rq) (hDb : DbgTz st H.tcbs Cs s2) (h0 : 0#u64 ∈ Cs) (a : A)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (hx : ∀ x ∈ extra.val, x ≠ 0#u64 → x ∈ OS)
    {slot p sb fi aligned nt us dest off win : U64} {dev : Bool} (hsrc : slot ∈ OS)
    (hcs : capA st s0 slot = .Untyped p sb fi dev)
    (hU : UtArgs st s0 extra slot p sb fi dev false aligned nt us dest off win)
    (hn : nt.val < 15)
    (hz : (zA nt.val us).val < 64) (hdev : dev = true → nt.val ≠ 1 ∧ nt.val ≠ 12 ∧ nt.val ≠ 14)
    (hal : aligned.val % 8 = 0)
    (hfi : fi.val < 2 ^ sb.val) (hA0 : p.val + fi.val ≤ aligned.val)
    (hAw : aligned.val + win.val * 2 ^ (zA nt.val us).val ≤ p.val + 2 ^ sb.val)
    (hH' : ∀ q k, H' q = some k → H q = some k ∨
      (nt.val ≠ 0 ∧ aligned.val ≤ q.val ∧ q.val + 2 ^ k.bits ≤ aligned.val + win.val * 2 ^ (zA nt.val us).val))
    (hdn : ∀ j, j < win.val → capA st s0 (djA dest off j) = .Null)
    (hinj : ∀ j l, j < win.val → l < win.val → djA dest off j = djA dest off l → j = l)
    (hcan : ∀ j, j < win.val → CapRt.Canonical (bjA aligned (zA nt.val us) j)) (hus : us.val < 64) :
    untyped.retype st ar s2 a slot false aligned nt us dest off win dev ⦃ r => r.1 = .Ok () ∧
      StZ st H' Cs OS r.2.1 ⦄ := by
  obtain ⟨x, hxm, hx0, idx, dep, val, -, -, erd, -⟩ := hU
  have hdc' := untyped.retype_dest.cov hO hT0 hS0 (hx x hxm hx0) erd
  have hdO : ∀ j, j < win.val → djA dest off j ∈ OS := fun j hj => (hdc' j hj).1
  exact untyped.retype.stZQ hA hH hO hSt q hDb h0 a hsrc (by rw [k.capA hsrc]; exact hcs) nt us dest off win
    aligned dev rfl hn hz hdev hal hfi hA0 hAw hH' hdO (fun j hj => by rw [k.capA (hdO j hj)]; exact hdn j hj)
    (fun j hj => hO.canon hW (hdO j hj)) hinj hcan hus
    fun j hj => by
      obtain ⟨z, hz', hcv⟩ := (hdc' j hj).2
      exact ⟨z, hz', by rw [k.capA hz']; exact hcv⟩

/-- **`untyped::decode` keeps `StZ`** (module docstring). -/
theorem untyped.decode.stZ (hA : P0.ArchTotal ar) {s : S} (hSt : StZ st H Cs OS s)
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len slot buf ptr sb fi : U64) (dev : Bool)
    (hsh : machine.sharing_enabled st s = ok true →
      untyped.retype_shared st ar s a len slot (.Untyped ptr sb fi dev) buf extra ⦃ r s' _ =>
        ∃ H' : Heap, StZ st H' Cs OS s' ⦄)
    (hRet : ∀ (s2 : S) (reset : Bool) (aligned nt us dest off win : U64),
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART = ok s2 →
      UtArgs st s extra slot ptr sb fi dev reset aligned nt us dest off win → StZ st H Cs OS s2 →
      untyped.retype st ar s2 a slot reset aligned nt us dest off win dev ⦃ r s' _ =>
        ∃ H' : Heap, StZ st H' Cs OS s' ⦄)
    (hH : HeapOK H) (hO : OSOK H.tcbs H.omega Sg OS) {X : Set U64} {Q : U64 → U64 → List U64}
    {Rq : U64 → List U64} (q : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q Rq) :
    untyped.decode st ar s a lbl len slot (.Untyped ptr sb fi dev) buf extra ⦃ r s' _ =>
      ∃ H' : Heap, StZ st H' Cs OS s' ⦄ :=
  untyped.decode.decG (P := fun _ s' => ∃ H' : Heap, StZ st H' Cs OS s') hA a lbl len slot buf ptr sb fi dev
    (fun _ => ⟨H, hSt⟩) hsh fun s2 reset aligned nt us dest off win e hU =>
      hRet s2 reset aligned nt us dest off win e hU (StZ.restartEq hH hO q hSt e)

end arch

end ST
end R
end W7

end

end Fl4ProofsA64.P1
