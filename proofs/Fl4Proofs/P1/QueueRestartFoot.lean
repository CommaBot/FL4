/-
P1: **`restart`'s footprint** (`sched.restart.allK`): `sched.restart.all`
with P1's write set `Foot` (`KW`) across the whole operation: `cancel_ipc`
(`ipc.cancel_ipc.kw`), the `Restart` state (`set_thread_state.kwP`), the
unblock check (its ring and the current core's `REPROGRAM` word),
`schedcontext::resume` (`resume.kw`) and `possible_switch_to`
(`possible_switch_to.kw`). Used at `J` for core 0's `DEBUG_TCBS` word
(`JAtZ.kw_dbg`).
-/
import Fl4Proofs.P1.QueueRestart
import Fl4Proofs.P1.QueueFinal
import Fl4Proofs.P1.QueueFootS
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
theorem sched.restart.allK (hA : P0.ArchTotal ar) (s : S) (a : A) (t : obj.Tcb)
    (Q : U64 → U64 → List U64) (R : U64 → List U64) (h : SchedQueuesInv st T Cs Ω H s Q R) (ht : t ∈ T)
    (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) :
    sched.restart st ar s a t ⦃ s' _ => ∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R' ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TmFr st T Cs Nt s s' ∧
      Foot st T Cs Sg Scs Z (EH H) s s' ⦄ := by
  have hSg := hS.sg
  have hsub := hSg.sub
  have hT := h.tcbs
  unfold sched.restart
  step with sched.is_stopped.spec as ⟨b, b_post⟩
  split
  swap
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q, R, h, hB, hX, hS, TmFr.refl (L := L) _, Foot.refl _⟩
  rename_i hb
  have hnr : ¬ Runnable (L.mem s (stA t)) := b_post hb
  have hna : L.actionW s ≠ t := fun e => hnr (by have := (h.actOK (e ▸ ht)).1; rwa [e] at this)
  have hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t := fun hs => by
    obtain ⟨h1, h2⟩ := hX.2.1.reply t ht hs
    exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩
  refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a t Q R h ht hB hX hsub)
    (ipc.cancel_ipc.kw (Sg := Sg) (Scs := Scs) (Z := Z) s a t h ht hX.1 hsub hreply
      (fun h1 h2 => (hX.2.1.recv t ht h1 h2).1))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, hB1, hX1, nb1, nr1, hst1, k1, -⟩, fw1⟩
  try simp only [WP.uncurry'_pair]
  have na1 : L.actionW s1 ≠ t := by
    rcases hst1 with e | ⟨-, e⟩
    · intro ea
      have := (h1.actOK (ea ▸ ht)).1; rw [ea, e] at this; exact not_runnable_inactive this
    · rw [e]; exact hna
  -- the `Restart` state
  refine WP.spec_bind (WP.spec_and (sched.set_thread_state.inv s1 t _ Q R h1 ht not_blocked_restart (Or.inr nb1)
    ⟨fun _ _ _ _ _ => runnable_restart, fun _ _ _ => runnable_restart, fun _ => runnable_restart⟩)
    (WP.spec_and (sched.set_thread_state.state s1 t _ Q R h1 ht hX1.1 hsub)
      (sched.set_thread_state.kwP (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 t _ hT (h1.nodes _ h1.cur)
        h1.cur ht))) ?_
  rintro s2 ⟨h2', ⟨e2, k2⟩, fw2⟩
  have h2 : SchedQueuesInv st T Cs Ω H s2 Q R := h2'.congrX empty_congr
  have nrr : sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_REPLY ∧ sched.TS_RESTART ≠ sched.TS_BLOCKED_ON_RECV := by
    obtain ⟨-, -, h3', -⟩ := ts_vals
    rw [ts_restart, ts_reply, h3']; decide
  have hB2 := hB1.keepT h1 k2 (by rw [e2]; exact not_blocked_restart) (by rw [e2]; exact nrr.1)
  have hX2 := hX1.keepT k2 (by rw [e2]; exact nrr)
    (fun r hr e => absurd e (hX1.noref (h1.tcbs t ht) nr1 (fun e' => nb1 (Or.inr (Or.inl e'))) r hr))
  have hS2 : SCsOK st T Ω Sg Scs Z Ac s2 := (hS.keepT hX k1).keepT hX1 k2
  have k12 := k1.trans k2
  have tm2 : TmFr st T Cs Nt s s2 := TmFr.of_keepT k12
  have hSg2 : SgOK st Ω Sg s2 := ⟨hsub, fun b hb => by rw [k12.ksb]; exact hSg.ks b hb,
    fun o h1' h2'' => by rw [k12.ksb]; exact hSg.ksΩ o h1' h2''⟩
  have na2 : L.actionW s2 ≠ t := by
    rcases k2.act with e | e
    · rw [e]; exact na1
    · rw [e]; intro e'; exact notT_small hT (by simp) (e' ▸ ht)
  have sc2 : L.mem s2 (scA t) = L.mem s (scA t) := k12.scf ht
  -- the SC: unblock check
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  refine WP.spec_bind (Pₘ := fun s3 => SchedQueuesInv st T Cs Ω H s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SgOK st Ω Sg s3 ∧ L.actionW s3 ≠ t ∧ L.mem s3 (scA t) = i ∧
      SCsOK st T Ω Sg Scs Z Ac s3 ∧ TmFr st T Cs Nt s2 s3 ∧ Foot st T Cs Sg Scs Z (EH H) s2 s3) ?_ ?_
  · split
    · rename_i hb1
      obtain ⟨hi0, hsp⟩ := b1_post hb1
      have hbt : L.mem s2 (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
      obtain ⟨hiS, -, -⟩ := hX2.2.2.bound t ht hbt
      rw [← i_post] at hiS
      -- a sporadic SC is active, so well formed
      have hW2 : RefillsWF st s2 i (Z i) := hS2.wf hiS (hS2.spor i hiS hsp)
      have hSCin : SCin st s2 Ω i (Z i) := ⟨hW2, hX2.1.scW i hiS⟩
      step with sched.cur_sc.spec as ⟨c4, _⟩
      step with sc_ne.spec as ⟨b2⟩
      split
      · have hN' := h2.nodes _ h2.cur
        have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
        have aR : Aligned (L.nodeA s2 layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
        have oR : Outside (L.nodeA s2 layout.node.REPROGRAM) i (Z i) :=
          hSCin.node_out h2.omega h2.cur hN' (by rw [rp]; omega) (by rw [rp])
        refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.fr hW2 ⟨aR, oR⟩)
          (sporadic.unblock_check.wf hW2 ⟨aR, oR⟩)) fun s3 hw3 => ?_
        have w3 := hw3.1
        have hS3 := SCsOK.ring h2 hS2 hX2 hiS w3 hw3.2
        have wF : WritesIn st s2 s3 (L.Free s2 Ω Cs) := w3.mono' fun b hb hh => by
          rcases hh with hh | hh
          · exact Or.inl (hX2.1.scW i hiS b hb hh.inSC)
          · exact hh ▸ free_cur_node h2.cur (by simp [rp, LowFree])
        have h3 := inv_of_free h2 wF
        have hB3 := hB2.free h2 wF
        have nP : ∀ b, (InRing i (Z i) b ∨ b = L.nodeA s2 layout.node.REPROGRAM) → Aligned b →
            ¬ Prot T Rp Scs Nt b := fun b hh hb => by
          rcases hh with hh | hh
          · exact not_prot_ring h2 hX2.1 hiS hb (Or.inl hh)
          · exact hh ▸ not_prot_node h2 hX2.1 hsub h2.cur (by rw [rp]; omega)
        have kn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 56 →
            L.mem s3 (L.nodeA s2 o) = L.mem s2 (L.nodeA s2 o) := fun o ho h8 h56 => by
          refine w3.mem_eq (nodeAt_aligned hN' ho h8) ?_
          rintro (hh | hh)
          · have hm := hX2.1.scW i hiS _ (nodeAt_aligned hN' ho h8) hh.inSC
            exact out_ne_node (h2.omega _ hm) h2.cur hN' ho rfl
          · have := congrArg UScalar.val hh
            simp only [LawfulStore.nodeA] at this
            rw [nodeAt_val hN' ho, nodeAt_val hN' (by rw [rp]; omega), rp] at this; omega
        have hX3 : XInv st T Cs Ω Sg Rp Scs Nt Z s3 := hX2.writes hT
          (w3.mono' fun b hb hh => fun hp => nP b hh hb hp) (fun b hb => hb) (by
            unfold LawfulStore.cscW; rw [cscW_eq w3.1 w3.2.1, kn _ (by simp [layout.node.CUR_SC])
              (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])]; exact hX2.2.2.cur)
            (hX2.tn (TmFr.of_ring h2 hX2 hsub hiS w3)) (by
              unfold LawfulStore.idleW; rw [w3.2.1, nodeAt_of_ksb w3.1]
              exact kn _ (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega))
        refine ⟨h3, hB3, hX3, ⟨hsub, fun b hb => by rw [w3.1]; exact hSg2.ks b hb,
          fun o h1' h2'' => by rw [w3.1]; exact hSg2.ksΩ o h1' h2''⟩, ?_⟩
        unfold LawfulStore.actionW
        rw [w3.2.1, nodeAt_of_ksb w3.1]
        rw [show L.mem s3 (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) =
            L.mem s2 (L.nodeAt s2 (L.cpu s2) layout.node.SCHED_ACTION) from
          kn _ (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)]
        refine ⟨na2, ?_, hS3, TmFr.of_ring h2 hX2 hsub hiS w3, Foot.of' w3 fun b _ hh => ?_⟩
        swap
        · rcases hh with hh | hh
          · exact kw_sc hiS hh.inSC
          · rw [hh]; exact kw_node h2.cur (by rw [rp]; omega) (by rw [rp]; decide)
        rw [w3.mem_eq (scA_aligned (hT t ht)) ?_, i_post]
        rintro (hh | hh)
        · have hm := hX2.1.scW i hiS _ (scA_aligned (hT t ht)) hh.inSC
          rw [scA_eq] at hm
          exact out_ne_field (h2.omega _ hm) ht (hT t ht) (by simp) rfl
        · rw [scA_eq] at hh
          exact node_ne_field hN' (by rw [rp]; omega) ht (hT t ht) (by simp) hh.symm
      · exact (WP.spec_ok _).2 ⟨h2, hB2, hX2, hSg2, na2, i_post.symm, hS2, TmFr.refl (L := L) _, Foot.refl _⟩
    · exact (WP.spec_ok _).2 ⟨h2, hB2, hX2, hSg2, na2, i_post.symm, hS2, TmFr.refl (L := L) _, Foot.refl _⟩
  rintro s3 ⟨h3, hB3, hX3, hSg3, na3, sc3, hS3, tm3, fw3⟩
  -- `resume`
  have hsc3 : i ≠ 0#u64 → L.mem s3 (scTcbA i) ≠ 0#u64 →
      L.mem s3 (scTcbA i) ∈ T ∧ OutsideObjs st T Cs s3 (scCoreA i) ∧ L.mem s3 (scCoreA i) ∈ Cs ∧
        L.actionW s3 ≠ L.mem s3 (scTcbA i) := fun hi0 _ => by
    obtain ⟨hiS, hti, hci⟩ := hX3.2.2.bound t ht (by rw [sc3]; exact hi0)
    rw [sc3] at hiS hti hci
    rw [hti]
    exact ⟨ht, h3.omega _ ((objs_omega hX3.1 hsub).2 i hiS).2.1, hci, na3⟩
  refine WP.spec_bind (WP.spec_and (schedcontext.resume.all hA s3 a1 i Q R h3 hB3 hX3 hSg3 hS3 hsc3)
    (schedcontext.resume.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a1 i Q R h3 hsc3)) ?_
  rintro ⟨s4, a2⟩ ⟨⟨Q4, R4, h4, hB4, hX4, hSg4, fr4⟩, fw4⟩
  have hS4 := hS3.fr fr4
  have tm4 : TmFr st T Cs Nt s s4 := tm2.trans (tm3.trans (TmFr.of_fr fr4 hX3.1 h3.nodes))
  try simp only [WP.uncurry'_pair]
  -- `possible_switch_to`
  step with sched.is_schedulable.spec' as ⟨b2, b2_post⟩
  split
  · rename_i hb2
    obtain ⟨hrun4, hbd4, -, hmx4⟩ := b2_post hb2
    refine WP.spec_bind (WP.spec_and (sched.possible_switch_to.sch s4 t Q4 R4 h4 hB4 hSg4 ht hrun4
      (fun _ => (hS4.act _ (hX4.2.2.bound t ht hbd4).1).2 hmx4))
      (sched.possible_switch_to.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s4 t h4 ht)) ?_
    rintro s5 ⟨⟨⟨hi5, hB5, f5⟩, -, -⟩, fw5⟩
    simp only [WP.spec_ok, WP.uncurry'_pair]
    obtain ⟨Q5, R5, h5⟩ := hi5
    exact ⟨Q5, R5, h5, hB5, hX4.fr f5, hS4.fr f5, tm4.trans (TmFr.of_fr f5 hX4.1 h4.nodes),
      fw1.trans (fw2.trans (fw3.trans (fw4.trans fw5)))⟩
  · simp only [WP.spec_ok, WP.uncurry'_pair]; exact ⟨Q4, R4, h4, hB4, hX4, hS4, tm4, fw1.trans (fw2.trans (fw3.trans fw4))⟩

end

end Fl4Proofs.P1
