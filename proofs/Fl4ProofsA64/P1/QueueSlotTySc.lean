/-
P1 (aarch64, gen 31): **the SchedContext kind over `SlotTy`** (any finality), `J` to `J`.

`finalise_cap` of a final SC cap (objects.rs `finalise_cap_object`, Funs.lean `objects.finalise_cap_object`):
`unbind_all_tcbs`, the notification and reply unbinding, `complete_yield_to`, the `REFILL_MAX` / `SPORADIC` clears.
* `Cur0`: the existing `finGap_sc` (QueueFinThr);
* `RunVcpuInv`: the existing `W7.R.finRv_sc` (QueueFinRvSt);
* `SlotTy`: QueueFoot7B's `K7.fin_sc.blk` (a `K7.Foot ∅` footprint: TCB fields from 224, node words, frame words,
  SC words), kept off `OS` by QueueSlotTyEp's `OSKeep.of_kw7` under `ScApart`.

**`finJ_sc`**, **`cdt.delete.sc`**. Case hypothesis (at the state the deletion starts from, not over a word class):
`ScPlAt x s`, the existing `FinPl` of the slot's SC cap (P3's placement: the SC is one of `Scs`, not at `0`, and
its thread, if any, is not the idle thread; QueueDecDel's `FinPl`). On reachable states an SC cap names an SC
object (it is created by retype, objects.rs `create_object`) and the idle thread's SC has no cap (boot.rs creates
it without one), so `FinPl` holds there. No new named premise; no existing statement changed.

Not covered here: the Thread kind. Its `RunVcpuInv` part (`W7.R.finRv_thread`) needs [P] `rcw` of `DelPlaceAt`,
which gen 28–29 refuted as stated (every `DelPlaceAt` field is false at some `Fr0 ∧ BXI` state, QueueDelPlaceFalse);
a thread top over `J` needs `VcTy` (a VCPU typing carried in `J`, handoff §33) first.
-/
import Fl4ProofsA64.P1.QueueSlotTyEp
import Fl4ProofsA64.P1.QueueFoot7B
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

theorem dc_sc {p b : U64} : Fl4ProofsA64.P1.DelCapOK T Ω Sg H Rp Nt (.SchedContext p b) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all

/-- The case hypothesis: the slot holds an SC cap with P3's placement (`FinPl`). -/
def ScPlAt (st : machine.Store S) [L : LawfulStore st] (Scs : Set U64) (x : U64) (s : S) : Prop :=
  ∀ c, obj.Slot.cap st x s = ok c → (∃ p b, c = .SchedContext p b) ∧ FinPl st Scs s c

set_option maxHeartbeats 2000000 in
/-- **The SchedContext kind, any finality**: `FinJ`. -/
theorem finJ_sc {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS : Set U64} (hO : OSOK T Ω Sg OS)
    (hA : ScApart Scs Z OS) {s0 s : S} {x : U64} (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hk : ScPlAt st Scs x s) :
    FinJ st ar T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s x := by
  intro a c fin hc
  obtain ⟨⟨p, b, rfl⟩, hpl⟩ := hk c hc
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p b rfl
  obtain ⟨Ac', hb⟩ := h.parts
  have q := hb.1.choose_spec.choose_spec
  have hsub : ∀ b ∈ Sg, b ∈ Ω := by obtain ⟨-, -, -, -, hSg⟩ := hb.blk; exact hSg.sub
  have hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p) := fun h0 =>
    h.1.1.na _ (hb.2.2.1.2.2.yt.1 p hpS h0)
  have G := Fl4ProofsA64.P1.finGap_sc (ar := ar) hP Ac s0 s a _ fin h.1.1 dc_sc hpl ⟨p, b, rfl⟩
  have Rv : objects.finalise_cap st ar s a (.SchedContext p b) fin false ⦃ r => RunVcpuInv st T r.2.1 ⦄ :=
    Fl4ProofsA64.P1.W7.R.finRv_sc (ar := ar) hP (a := a) (fin := fin) h.1.1 h.1.2 hpl
  have F : objects.finalise_cap st ar s a (.SchedContext p b) fin false ⦃ r =>
      r.1 = (.Null, .Null) ∧ K7.Foot st T Cs Sg Scs Z ∅ s r.2.1 ⦄ := by
    rw [fin_cap_eq_obj (by simp)]
    refine WP.spec_mono (WP.spec_and (fin_sc.rem hP s a p b fin)
      (K7.fin_sc.blk (ar := ar) hP s a p b fin hb.blk hpS hp0 hna hid)) fun r hr => ?_
    obtain ⟨e, _, _, _, f⟩ := hr
    exact ⟨e, f⟩
  refine WP.spec_mono (WP.spec_and G (WP.spec_and Rv F)) ?_
  rintro r ⟨⟨c0, -, -⟩, rv, e, f⟩
  exact ⟨e, ⟨c0, rv⟩, h.2.keep (OSKeep.of_kw7 hO q hsub hA (fun e he => absurd he (Set.notMem_empty e)) f)⟩

/-- **The exposed `cdt.delete` of an SC slot of `OS` keeps `J`** (any finality), under `ScApart` and P3's
placement of the SC cap (`ScPlAt`). -/
theorem cdt.delete.sc {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar) {OS : Set U64}
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) {s0 s : S} {a : A} {x : U64}
    (h : J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 s) (hx : x ∈ OS) (hk : ScPlAt st Scs x s) :
    cdt.delete st ar s a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s0 r.2.1 ⦄ :=
  cdt.delete.finJ hO h hx (finJ_sc hP hO hA h hk)

end ST
end R
end W7

end

end Fl4ProofsA64.P1
