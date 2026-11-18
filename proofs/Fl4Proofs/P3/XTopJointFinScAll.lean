/-
P3 (DESIGN.md §9), CSpace: **`unbind_all_tcbs` of an SC at `J`** (the first
step of a final SC cap's finalisation, XTopJointFinSc's `JAtZ.finScJ`):
`JAtZ.unbindAllJ`.

As XTop's `unbind_all_tcbs_refines`: nothing without a bound thread; else
the remote stall (a no-op, `remote_tcb_stall_id`) and `unbind_tcb`, which is
XTopJointFinThreadSc's `JAtZ.unbindTcbJ` (the reschedule when the SC's
thread is the current thread included). Its premises come from `JAtZ`: the
SC's `TCB` word names a TCB of the sets (P1's `ScExtra.yt`) whose `SC` word
names the SC back (P1's `ScExtra.tsc`), so its spec SC field is the SC (the
IPC relation's `sc`); not the switch target nor the idle thread by the
action and idle words (`JAtZ.spec_of_words`; P1's `unbind_all_tcbs.blk`
preconditions).
-/
import Fl4Proofs.P3.XTopJointFinThreadSc
import Fl4Proofs.P3.XTopJointFinScReply
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

set_option maxHeartbeats 8000000 in
/-- **`unbind_all_tcbs` of an SC at `J`** (module docstring): for an SC of
the SCs, non-null, not the idle SC, its thread (if any) neither the
scheduler action nor the idle thread. -/
theorem JAtZ.unbindAllJ {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hpC : p ∈ Z.C) (hp0 : p ≠ 0#u64)
    (hpi : p.bv ≠ Fl4Spec.idleScPtr)
    (hna : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (P1.scTcbA p))
    (hidle : L.mem s (P1.scTcbA p) ≠ 0#u64 → L.idleW s ≠ L.mem s (P1.scTcbA p)) :
    schedcontext.unbind_all_tcbs st arI s a p ⦃ r => ∃ σ',
      Fl4Spec.schedContextUnbindAllTcbs (Z := Unit) p.bv σ = ({((), σ')}, False) ∧
      JTP (L := L) arI AR Z H Cs r.1 r.2 σ' ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  obtain ⟨y, n, hk, hx⟩ := hs.scs p hpC
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p y n hp0 hk).2⟩
  unfold schedcontext.unbind_all_tcbs
  step with P1.obj.Sc.tcb.spec as ⟨i, hi⟩
  have hiw : L.mem s (P1.scTcbA p) = i := by rw [hi]
  rw [scTcbA_eq] at hi
  have hyi : y.scTcb = optRef i := by rw [hx.tcb, hi]
  by_cases hi0 : i = 0#u64
  · subst hi0
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    refine ⟨σ, ?_, Z.vs, Ac, Lst, D, J⟩
    unfold Fl4Spec.schedContextUnbindAllTcbs
    rw [nd_bind_one (getSchedContext_eq hk), hyi, optRef_zero]
    unfold Fl4Spec.NonDet.when; rw [if_neg (by simp)]; rfl
  · have hyt : y.scTcb = some i.bv := by rw [hyi, Notif.optRef_ne hi0]
    have h0 : L.mem s (P1.scTcbA p) ≠ 0#u64 := by rw [hiw]; exact hi0
    have hiT : i ∈ Z.T := by
      rw [J.tcbs_eq.1, ← hiw]; exact J.blk.2.2.1.2.2.yt.1 p hpS h0
    have hback : L.mem s (P1.scA i) = p := by
      have := J.blk.2.2.1.2.2.tsc p hpS hp0 h0; rw [hiw] at this; exact this
    obtain ⟨x, hkx, hRx⟩ := J.xtop.ipc.tcb i hiT
    have hsp : x.tcbSchedContext = some p.bv := by rw [hRx.sc, hback, Notif.optRef_ne hp0]
    have h1 := hna h0; rw [hiw] at h1
    have h2 := hidle h0; rw [hiw] at h2
    obtain ⟨hsa, hid⟩ := J.spec_of_words h1 h2
    have hne : (i != 0#u64) = true := by simpa using hi0
    simp only [hne, ↓reduceIte]
    refine WP.spec_bind (remote_tcb_stall_id (ar := arI) a hS hiT) ?_
    rintro ⟨s1, a1⟩ he
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine WP.spec_bind (J.unbindTcbJ hiT hpC hkx hsp hsa hid) ?_
    rintro s2 ⟨σ2, h2, Ac2, Lst2, D2, J2⟩
    rw [WP.spec_ok]
    refine ⟨σ2, ?_, Z.vs, Ac2, Lst2, D2, J2⟩
    unfold Fl4Spec.schedContextUnbindAllTcbs
    rw [nd_bind_one (getSchedContext_eq hk)]
    unfold Fl4Spec.NonDet.when; rw [if_pos ⟨by rw [hyt]; simp, hpi⟩]; exact h2

end

end

end Fl4Proofs.P3
