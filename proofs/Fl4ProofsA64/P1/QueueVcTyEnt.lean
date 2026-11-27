/-
P1 (aarch64, gen 32): **`JV` from the entry fact**: at an `EntAt` decode start, under [J] `SlotTyEntV`
(QueueVcTy), the decode's restart starts `JV`, and from every state it reaches the `JV` tops of QueueVcTy /
QueueVcTyThr apply with no apartness or placement hypothesis left.

* **`JV.restart`**: the restart (`set_thread_state` of the caller to `RESTART`: its `STATE` word and the current
  core's `SCHED_ACTION` word, `sts_fine`) starts `J` (`J.restart`) and keeps `VcTy` (`DS.sts`).
* **`JV.restart_ent`**: the same from [J] `SlotTyEntV` at an `EntAt` state (`SlotTyEntV.entAt`; the TCBs are placed
  at every `BXI` state), with, at every state the restart reaches, the exposed `cdt.delete` of a `FinTriv`, an
  endpoint / notification / reply or an SC slot of `OS` keeping `JV`, and the finalisation of a thread cap of an
  `OS` slot (bound VCPU or run in flight included) ending in `JV`.

Consumes [J] `SlotTyEntV`; no other premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueVcTyThr
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

/-- **The decode's restart starts `JV`** (and keeps every `OS` word). -/
theorem JV.restart {OS Vc Ub : Set U64} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧ OSKeep st OS s s1 ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  have hct : L.curW s ∈ T := q.curT
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  refine WP.spec_mono (WP.spec_and (J.restart hO D hT) (sts_fine s _ sched.TS_RESTART (q.nodes _ q.cur)
    (q.tcbs _ hct))) fun s1 hh => ⟨And.intro hh.1.1 (hv.keepZ (DS.sts hO hV q hW hct hh.2).2), hh.1.2⟩

/-- **`JV` from [J] `SlotTyEntV` at an `EntAt` decode start**, and the `JV` tops at every state the restart
reaches (module docstring). -/
theorem JV.restart_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntV st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
        JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧
        (∀ (a : A) (x : U64), x ∈ OS → CapFinTrivAt st x s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) ∧
        (∀ (a : A) (x : U64), x ∈ OS → EpNtRpAt st x s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) ∧
        (∀ (a : A) (x : U64), x ∈ OS → ScPlAt st Scs x s1 →
          cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) ∧
        (∀ (a : A) (x p : U64) (fin : Bool), x ∈ OS → obj.Slot.cap st x s1 = ok (.Thread p) →
          p ≠ L.idleW s1 →
          objects.finalise_cap st ar s1 a (.Thread p) fin false ⦃ r =>
            r.1 = (if fin then .Zombie p capability.ZOMBIE_TCB 7#u64 else .Null, .Null) ∧
            JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hsc, hV, hv⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, WP.spec_mono (JV.restart hO hV D hT hv) fun s1 h1 =>
    ⟨h1.1, fun a x hx hk => cdt.delete.fintrivV hP hO hV h1.1 hx hk,
      fun a x hx hk => cdt.delete.eprnV hP hO hsc hV h1.1 hx hk,
      fun a x hx hk => cdt.delete.scV hP hO hsc hV h1.1 hx hk,
      fun a x p fin hx hc hid => finJV_thread hP hO hsc hV h1.1 hx hc hid a fin⟩⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
