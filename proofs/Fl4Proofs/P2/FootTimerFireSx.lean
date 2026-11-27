/-
# P2 (p2lf): the waking fire tail after a switch to another thread

When a waking signal leaves the woken thread as the action, `schedule`'s `schedSw` switches to a thread `d` (the
woken thread, the current thread re-queued, or the old head of the highest ready queue); the rest of the tail is
`schedRes` (`schedTail`), `activate_thread`, `cur_thread` and `vcpu::check` from the state `X` it ends in.

* `SwTail st gS ar X a`: that rest on `gS` is the real one.
* `aw_of_sw`: `AwTailG` at the post-`awaken` state `Y` from the guarded `schedSw` and `SwTail` at every state the
  real `schedSw` ends in.
* `schedTail_fpS`: `schedTail` from a state whose current thread `d` may run on an SC other than the current one
  writes only the action word, `Ω` words and this core's low free node words (`FreeCd`), as `switch_to_nvm`'s
  (P1 `FastTailNvm`) middle.
* `sw_tail`: `SwTail` at `X` from `switch_hsw_hfr`'s premises and `d`'s words (as `aw_tail_resume`'s second
  half, with `d` for the current thread).

* (lvm gen 10) `schedTail_fpSB` (any `B` holding the low free node words, the action word and both SCs' words),
  `sw_tail_core` (`hnvm` dropped, `hvc` for a `d` running a VM); `sw_tail` keeps its statement.
No named premises.
-/
import Fl4Proofs.P2.FootTimerFireTk
import Fl4Proofs.P2.FootTimerFireSwT
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (ScAcc rhA tmA RdHead NodeSt bind_guard_congr)

section defs
variable {S : Type} {A : Type}

/-- The tail after `schedSw` from the state `X` it ends in, on `gS`. -/
def SwTail (st gS : machine.Store S) (ar : machine.Arch A) (X : S) (a : A) : Prop :=
  PathObl.LT.schedRes gS ar X a = PathObl.LT.schedRes st ar X a ∧
    ∀ s4 a4, PathObl.LT.schedRes st ar X a = ok (s4, a4) →
      sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 ∧
      ∀ s5 a5, sched.activate_thread st ar s4 a4 = ok (s5, a5) →
        sched.cur_thread gS s5 = sched.cur_thread st s5 ∧
        ∀ t, sched.cur_thread st s5 = ok t → vcpu.check gS ar s5 a5 t = vcpu.check st ar s5 a5 t

end defs

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {R W : U64 → Prop}
variable {T Cs Ω : Set U64}
variable {A : Type} (ar : machine.Arch A)

/-- **`AwTailG` from the guarded `schedSw` and `SwTail` after it** (module docstring). -/
theorem aw_of_sw {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W] (Y : S) (a : A)
    (rA : R (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION))
    (hact : L.actionW Y ≠ sched.ACTION_RESUME_CURRENT)
    (hsw : schedSw gS ar Y a (L.actionW Y) = schedSw st ar Y a (L.actionW Y))
    (hX : ∀ X a', schedSw st ar Y a (L.actionW Y) = ok (X, a') → SwTail st gS ar X a') :
    AwTailG st gS ar Y a := by
  have hb : (L.actionW Y != sched.ACTION_RESUME_CURRENT) = true := bne_iff_ne.mpr hact
  refine ⟨actTail.guard ar Y a rA (fun _ => hsw) (fun s3 a2 e => ?_), fun s4 a4 e => ?_⟩
  · rw [if_pos hb] at e; exact (hX s3 a2 e).1
  · unfold actTail at e
    rw [eq_of_spec_fd (sched.action.spec (L := L) Y)] at e
    simp only [bind_ok] at e
    rw [if_pos hb] at e
    obtain ⟨x, h1, h2⟩ := bind_eq_ok e
    obtain ⟨s3, a2⟩ := x
    simp only [Aeneas.Std.uncurry_apply_pair] at h2
    exact (hX s3 a2 h1).2 s4 a4 h2

set_option maxHeartbeats 4000000 in
/-- **`schedTail` after a switch writes only the action word and `FreeCd`** (module docstring). -/
theorem schedTail_fpS (hA : P0.ArchTotal ar) (X : S) (a : A) {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω X d) (hcur : L.curW X = d)
    (hc : SCq st X Ω (L.cscW X) zc)
    (ht : L.mem X (scA d) ≠ L.cscW X → SCin st X Ω (L.mem X (scA d)) zt ∧
      ∀ b, InSC (L.mem X (scA d)) zt b → Outside b (L.cscW X) zc) :
    schedTail (st := st) ar X a ⦃ r => WritesIn st X r.1
      (fun b => FreeCd (L := L) X Ω b ∨ b = L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) ⦄ := by
  have hd' := P.hT d P.hd
  have aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val])
  unfold schedTail
  refine WP.spec_bind (sched.set_action.spec X _) fun X1 e1 => ?_
  have kX : L.ksb X1 = L.ksb X := by rw [e1, L.ksb_wr]
  have cX : L.cpu X1 = L.cpu X := by rw [e1, LawfulStore.cpu_wr]
  have PX := P.ksb kX cX
  have w1 : WritesIn st X X1
      (fun b => FreeCd (L := L) X Ω b ∨ b = L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) := by
    rw [e1]; exact (writesIn_wr aA).mono fun b hb => Or.inr hb
  have fc : ∀ b, FreeCd (L := L) X1 Ω b → FreeCd (L := L) X Ω b := by
    rintro b (h | ⟨o, ho, e⟩)
    · exact Or.inl h
    · exact Or.inr ⟨o, ho, by rw [e, cX, nodeAt_of_ksb kX]⟩
  have ag : ∀ b, Aligned b → b ≠ L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION → L.mem X1 b = L.mem X b :=
    fun b hb h => by rw [e1, mem_wr_ne' aA hb (Ne.symm h)]
  have agΩ : ∀ b ∈ Ω, L.mem X1 b = L.mem X b := fun b hb => ag b (P.hΩ b hb).1
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [act_val]; omega) (by rw [e]))
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X1 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    ag _ (P.tcbAl hK h8) (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm)
  have csA : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecs : L.mem X1 (L.nodeA X1 layout.node.CUR_SC) = L.cscW X := by
    unfold LawfulStore.nodeA LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    exact ag _ csA (nodeAt_ne P.hN (by simp [layout.node.CUR_SC]) (by rw [act_val]; omega)
      (by rw [act_val]; simp [layout.node.CUR_SC]))
  have hcur1 : L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD) = d := by
    unfold LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX, ag _ P.curAl (nodeAt_ne P.hN (by rw [curth_val]; omega) (by rw [act_val]; omega)
      (by rw [curth_val, act_val]; omega))]
    exact hcur
  have esc : L.mem X1 (scA d) = L.mem X (scA d) := by rw [scA_eq]; exact agT _ (by simp) (by simp)
  have hcX : SCq st X1 Ω (L.mem X1 (L.nodeA X1 layout.node.CUR_SC)) zc := by
    rw [ecs]
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X1 (L.cscW X) = L.rmax X (L.cscW X) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD))) ≠ L.mem X1 (L.nodeA X1 layout.node.CUR_SC) →
      SCin st X1 Ω (L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem X1 (L.nodeA X1 layout.node.CUR_SC)) zc := by
    rw [hcur1, esc, ecs]
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.agree agΩ, h2⟩
  have fN : ∀ o : U64, LowFree o.val → FreeCd (L := L) X1 Ω (L.nodeA X1 o) := fun o ho => Or.inr ⟨o, ho, rfl⟩
  refine WP.spec_bind (sched.switch_sched_context.fp hA X1 a (zt := zt) (zc := zc) (B := FreeCd (L := L) X1 Ω)
    PX.hcC PX.hN PX.hΩ hcX htX (fN _ (by simp [layout.node.REPROGRAM, LowFree]))
    (fN _ (by simp [layout.node.CONSUMED, LowFree])) (fN _ (by simp [layout.node.CUR_SC, LowFree]))
    (fun hne b hb h => Or.inl ((htX hne).1.2 b hb h.inSC))
    (fun b hb h => by
      rcases h with h | rfl
      · exact Or.inl (hcX.2.1 b hb h.inSC)
      · exact Or.inl (hcX.2.1 _ hb hcX.2.2.1.1))) ?_
  rintro ⟨s4, a2⟩ ⟨w4, -⟩
  try simp only [WP.uncurry'_pair]
  have P4 := PX.ksb w4.1 w4.2.1
  have fN4 : ∀ o : U64, LowFree o.val → FreeCd (L := L) X1 Ω (L.nodeAt s4 (L.cpu s4) o) := fun o ho =>
    Or.inr ⟨o, ho, by rw [w4.2.1, nodeAt_of_ksb w4.1]⟩
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st X1 r.1 (FreeCd (L := L) X1 Ω)) ?_ ?_
  · split
    · refine WP.spec_bind (sched.set_next_interrupt.fp hA s4 a2 (B := FreeCd (L := L) X1 Ω) P4.hN
        (fN4 _ (by simp [layout.node.ARMED, LowFree]))) ?_
      rintro ⟨s6, a4⟩ w6
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (obj.node_set.spec s6 c _ _) fun s7 e7 => ?_
      subst e7
      simp only [WP.spec_ok]
      have w7 : WritesIn st s6 (L.wr s6 (L.nodeAt s6 c layout.node.REPROGRAM) 0#u64) (FreeCd (L := L) X1 Ω) := by
        rw [ec, nodeAt_of_ksb w6.1]
        exact (writesIn_wr (nodeAt_aligned P4.hN (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]))).mono fun b e => by
            rw [e]; exact fN4 _ (by simp [layout.node.REPROGRAM, LowFree])
      exact ((w4.trans w6).trans w7).mono fun b hb => by
        rcases hb with (h | h) | h <;> exact h
    · exact (WP.spec_ok _).2 w4
  rintro ⟨s5, a3⟩ w5
  try simp only [WP.uncurry'_pair]
  have P5 := PX.ksb w5.1 w5.2.1
  refine WP.spec_mono (smp.send_pending.fp hA s5 a3 (B := FreeCd (L := L) X1 Ω) P5.hN
    (Or.inr ⟨layout.node.IPI_PENDING, by simp [layout.node.IPI_PENDING, LowFree],
      by rw [w5.2.1, nodeAt_of_ksb w5.1]⟩)) fun r w6' => ?_
  exact (w1.trans ((w5.trans w6').mono fun b hb => hb.elim id id)).mono fun b hb =>
    hb.elim id (fun h => Or.inl (fc b h))

set_option maxHeartbeats 4000000 in
/-- **`schedTail` after a switch writes only `B`** (`schedTail_fpSB`, lvm gen 10): `schedTail_fpS` for any `B` holding
this core's low free node words, its action word and the words of the current SC and of `d`'s SC. -/
theorem schedTail_fpSB (hA : P0.ArchTotal ar) (X : S) (a : A) {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω X d) (hcur : L.curW X = d)
    (hc : SCq st X Ω (L.cscW X) zc)
    (ht : L.mem X (scA d) ≠ L.cscW X → SCin st X Ω (L.mem X (scA d)) zt ∧
      ∀ b, InSC (L.mem X (scA d)) zt b → Outside b (L.cscW X) zc)
    {B : U64 → Prop} (hBn : ∀ o : U64, LowFree o.val → B (L.nodeAt X (L.cpu X) o))
    (hBa : B (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION))
    (hBc : ∀ b, Aligned b → InSC (L.cscW X) zc b → B b)
    (hBt : L.mem X (scA d) ≠ L.cscW X → ∀ b, Aligned b → InSC (L.mem X (scA d)) zt b → B b) :
    schedTail (st := st) ar X a ⦃ r => WritesIn st X r.1 B ⦄ := by
  have hd' := P.hT d P.hd
  have aA : Aligned (L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val])
  unfold schedTail
  refine WP.spec_bind (sched.set_action.spec X _) fun X1 e1 => ?_
  have kX : L.ksb X1 = L.ksb X := by rw [e1, L.ksb_wr]
  have cX : L.cpu X1 = L.cpu X := by rw [e1, LawfulStore.cpu_wr]
  have PX := P.ksb kX cX
  have w1 : WritesIn st X X1 B := by
    rw [e1]; exact (writesIn_wr aA).mono fun b hb => by rw [hb]; exact hBa
  have ag : ∀ b, Aligned b → b ≠ L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION → L.mem X1 b = L.mem X b :=
    fun b hb h => by rw [e1, mem_wr_ne' aA hb (Ne.symm h)]
  have agΩ : ∀ b ∈ Ω, L.mem X1 b = L.mem X b := fun b hb => ag b (P.hΩ b hb).1
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [act_val]; omega) (by rw [e]))
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X1 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    ag _ (P.tcbAl hK h8) (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm)
  have csA : Aligned (L.nodeAt X (L.cpu X) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecs : L.mem X1 (L.nodeA X1 layout.node.CUR_SC) = L.cscW X := by
    unfold LawfulStore.nodeA LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    exact ag _ csA (nodeAt_ne P.hN (by simp [layout.node.CUR_SC]) (by rw [act_val]; omega)
      (by rw [act_val]; simp [layout.node.CUR_SC]))
  have hcur1 : L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD) = d := by
    unfold LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX, ag _ P.curAl (nodeAt_ne P.hN (by rw [curth_val]; omega) (by rw [act_val]; omega)
      (by rw [curth_val, act_val]; omega))]
    exact hcur
  have esc : L.mem X1 (scA d) = L.mem X (scA d) := by rw [scA_eq]; exact agT _ (by simp) (by simp)
  have hcX : SCq st X1 Ω (L.mem X1 (L.nodeA X1 layout.node.CUR_SC)) zc := by
    rw [ecs]
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X1 (L.cscW X) = L.rmax X (L.cscW X) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD))) ≠ L.mem X1 (L.nodeA X1 layout.node.CUR_SC) →
      SCin st X1 Ω (L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem X1 (scA (L.mem X1 (L.nodeA X1 layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem X1 (L.nodeA X1 layout.node.CUR_SC)) zc := by
    rw [hcur1, esc, ecs]
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.agree agΩ, h2⟩
  have fN : ∀ o : U64, LowFree o.val → B (L.nodeA X1 o) := fun o ho => by
    show B (L.nodeAt X1 (L.cpu X1) o)
    rw [cX, nodeAt_of_ksb kX]; exact hBn o ho
  refine WP.spec_bind (sched.switch_sched_context.fp hA X1 a (zt := zt) (zc := zc) (B := B)
    PX.hcC PX.hN PX.hΩ hcX htX (fN _ (by simp [layout.node.REPROGRAM, LowFree]))
    (fN _ (by simp [layout.node.CONSUMED, LowFree])) (fN _ (by simp [layout.node.CUR_SC, LowFree]))
    (fun hne b hb h => by
      simp only [hcur1, esc, ecs] at hne h
      exact hBt hne b hb h.inSC)
    (fun b hb h => by
      rcases h with h | rfl
      · simp only [ecs] at h; exact hBc b hb h.inSC
      · simp only [ecs] at hb ⊢; exact hBc _ hb hc.2.2.1.1)) ?_
  rintro ⟨s4, a2⟩ ⟨w4, -⟩
  try simp only [WP.uncurry'_pair]
  have P4 := PX.ksb w4.1 w4.2.1
  have fN4 : ∀ o : U64, LowFree o.val → B (L.nodeAt s4 (L.cpu s4) o) := fun o ho => by
    rw [w4.2.1, cX, nodeAt_of_ksb (w4.1.trans kX)]; exact hBn o ho
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st X1 r.1 B) ?_ ?_
  · split
    · refine WP.spec_bind (sched.set_next_interrupt.fp hA s4 a2 (B := B) P4.hN
        (fN4 _ (by simp [layout.node.ARMED, LowFree]))) ?_
      rintro ⟨s6, a4⟩ w6
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (obj.node_set.spec s6 c _ _) fun s7 e7 => ?_
      subst e7
      simp only [WP.spec_ok]
      have w7 : WritesIn st s6 (L.wr s6 (L.nodeAt s6 c layout.node.REPROGRAM) 0#u64) B := by
        rw [ec, nodeAt_of_ksb w6.1]
        exact (writesIn_wr (nodeAt_aligned P4.hN (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]))).mono fun b e => by
            rw [e]; exact fN4 _ (by simp [layout.node.REPROGRAM, LowFree])
      exact ((w4.trans w6).trans w7).mono fun b hb => by
        rcases hb with (h | h) | h <;> exact h
    · exact (WP.spec_ok _).2 w4
  rintro ⟨s5, a3⟩ w5
  try simp only [WP.uncurry'_pair]
  have P5 := PX.ksb w5.1 w5.2.1
  refine WP.spec_mono (smp.send_pending.fp hA s5 a3 (B := B) P5.hN
    (by rw [w5.2.1, cX, nodeAt_of_ksb (w5.1.trans kX)]; exact hBn _ (by simp [layout.node.IPI_PENDING, LowFree])))
    fun r w6' => ?_
  exact (w1.trans ((w5.trans w6').mono fun b hb => hb.elim id id)).mono fun b hb => hb.elim id id

set_option maxHeartbeats 16000000 in
/-- **The tail after a switch to `d`, final `vcpu::check` of a thread running a VM asked** (`sw_tail_core`, lvm
gen 10): `sw_tail` without `hnvm`; when `d` runs a VM the final `vcpu::check` is `hvc`'s, given that `schedTail`
wrote only this core's node words and the words of the current SC and `d`'s. -/
theorem sw_tail_core {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) (X : S) (a : A) {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω X d) (hcur : L.curW X = d)
    (hc : SCq st X Ω (L.cscW X) zc)
    (ht : L.mem X (scA d) ≠ L.cscW X → SCin st X Ω (L.mem X (scA d)) zt ∧
      ∀ b, InSC (L.mem X (scA d)) zt b → Outside b (L.cscW X) zc)
    (hact : L.mem X (scA d) = L.cscW X → L.rmax X (L.cscW X) ≠ 0#u64)
    (hrh : L.mem X (rhA (L := L) X) ≠ 0#u64 → L.mem X (rhA (L := L) X) ∈ T ∧
      R (scA (L.mem X (rhA (L := L) X))) ∧
      ∃ zq, SCin st X Ω (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq ∧
        (∀ b, Aligned b → InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → R b) ∧
        (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.cscW X →
          ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → Outside b (L.cscW X) zc) ∧
        (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.mem X (scA d) → L.mem X (scA d) ≠ L.cscW X →
          ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → Outside b (L.mem X (scA d)) zt))
    (htm : L.mem X (tmA (L := L) X) ≠ 0#u64 → L.mem X (tmA (L := L) X) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64))
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o))
    (hdt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME))
    (hSc : ScAcc R W (L.cscW X) zc) (hSi : L.mem X (scA d) ≠ L.cscW X → ScAcc R W (L.mem X (scA d)) zt)
    (hy0 : L.mem X (yieldA d) = 0#u64)
    (haff : L.mem X (affA d) = L.cpu X)
    (rYt : R (yieldA d)) (rSt : R (stA d)) (rFi : R (regA d layout.reg.FAULT_IP))
    (wNi : W (regA d layout.reg.NEXT_IP)) (rSc : R (scA d)) (rIq : R (inqA d))
    (rMd : R (maxA (L.mem X (scA d))))
    (hwS : ∀ X', L.mem X' (stA d) = sched.TS_RESTART → L.mem X' (affA d) = L.cpu X →
      gS.write X' (stA d) sched.TS_RUNNING = st.write X' (stA d) sched.TS_RUNNING)
    (hvc : L.mem X (stA d) = sched.TS_RUNNING_VM → ∀ s4 a4,
      WritesIn st X s4 (fun b => (∃ o : U64, o.val < 4288 ∧ b = L.nodeAt X (L.cpu X) o) ∨ InSC (L.cscW X) zc b ∨
        (L.mem X (scA d) ≠ L.cscW X ∧ InSC (L.mem X (scA d)) zt b)) →
      L.curW s4 = d → ∀ s5 a5, sched.activate_thread st ar s4 a4 = ok (s5, a5) →
      vcpu.check gS ar s5 a5 d = vcpu.check st ar s5 a5 d) :
    SwTail st gS ar X a := by
  have hd' := P.hT d P.hd
  have hres := PathObl.switch_hsw_hfr (gS := gS) hA X a P hcur hc ht hact hrh htm hNd hdt hSc hSi rSc
  refine ⟨PathObl.LT.schedRes.guard ar X a hNd hres.1 hres.2, fun s4 a4 esc => ?_⟩
  have hfp := schedTail_fpSB ar hA X a P hcur hc ht
    (B := fun b => (FreeCd (L := L) X Ω b ∨ b = L.nodeAt X (L.cpu X) layout.node.SCHED_ACTION) ∧
      ((∃ o : U64, o.val < 4288 ∧ b = L.nodeAt X (L.cpu X) o) ∨ InSC (L.cscW X) zc b ∨
        (L.mem X (scA d) ≠ L.cscW X ∧ InSC (L.mem X (scA d)) zt b)))
    (fun o ho => ⟨Or.inl (Or.inr ⟨o, ho, rfl⟩), Or.inl ⟨o, by simp only [LowFree] at ho; omega, rfl⟩⟩)
    ⟨Or.inr rfl, Or.inl ⟨_, by rw [act_val]; omega, rfl⟩⟩
    (fun b hb hin => ⟨Or.inl (Or.inl (hc.2.1 b hb hin)), Or.inr (Or.inl hin)⟩)
    (fun hne b hb hin => ⟨Or.inl (Or.inl ((ht hne).1.2 b hb hin)), Or.inr (Or.inr ⟨hne, hin⟩)⟩)
  have eT : PathObl.LT.schedRes st ar X a = schedTail (st := st) ar X a := rfl
  rw [← eT, esc, WP.spec_ok] at hfp
  have w34 := hfp
  have e4N : ∀ o, L.nodeAt s4 (L.cpu s4) o = L.nodeAt X (L.cpu X) o := fun o => by
    rw [w34.2.1, nodeAt_of_ksb w34.1]
  have tK4 : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s4 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) :=
    fun K hK h8 => w34.mem_eq (P.tcbAl hK h8) (fun hb => hb.1.elim (P.tcb_nfree hK)
      (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm))
  have hcur4 : L.curW s4 = d := by
    unfold LawfulStore.curW
    rw [w34.2.1, nodeAt_of_ksb w34.1, w34.mem_eq P.curAl ?_]
    · exact hcur
    rintro ⟨h | e, -⟩
    · exact P.cur_nfree h
    · exact nodeAt_ne P.hN (by rw [curth_val]; omega) (by rw [act_val]; omega) (by rw [curth_val, act_val]; omega) e
  have hy4 : L.mem s4 (yieldA d) = 0#u64 := by
    unfold yieldA; rw [tK4 _ (by simp) (by simp)]; exact hy0
  have hst4 : L.mem s4 (stA d) = L.mem X (stA d) := by
    rw [stA_eq, tK4 _ (by simp) (by simp)]
  have sc4 : L.mem s4 (scA d) = L.mem X (scA d) := by
    rw [scA_eq, tK4 _ (by simp) (by simp)]
  have aff4 : L.mem s4 (affA d) = L.cpu X := by
    unfold affA; rw [tK4 _ (by simp) (by simp)]; exact haff
  have hN4 : NodePlaced st T s4 (L.cpu s4) := by rw [w34.2.1]; exact P.hN.ksb w34.1
  have nrm4 : NodeSt (L := L) R W s4 := by
    unfold PathObl.NodeSt
    rw [e4N, e4N]
    exact ⟨(hNd _ (by rw [curth_val]; omega) (by rw [curth_val])).1,
      (hNd _ (by rw [act_val]; omega) (by rw [act_val])).1, (hNd _ (by rw [act_val]; omega) (by rw [act_val])).2⟩
  have eNx : regA d layout.reg.NEXT_IP = core.num.U64.wrapping_add d 368#u64 := by
    obtain ⟨K, hK, e⟩ := regA_eq hd' (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
    rw [e]
    congr 1
    apply UScalar.eq_of_val_eq
    rw [hK]
    simp [layout.reg.NEXT_IP]
  have aNx : Aligned (regA d layout.reg.NEXT_IP) := by
    rw [eNx]; exact field_aligned hd' (by simp) (by simp)
  have sA : Aligned (stA d) := by rw [stA_eq]; exact field_aligned hd' (by simp) (by simp)
  have aA : Aligned (affA d) := field_aligned hd' (by simp) (by simp)
  have nNs : regA d layout.reg.NEXT_IP ≠ stA d := by
    rw [eNx, stA_eq]; exact tcb_word_ne hd' hd' (by simp) (by simp) (fun _ => by simp)
  have nNa : regA d layout.reg.NEXT_IP ≠ affA d := by
    rw [eNx]; exact tcb_word_ne hd' hd' (by simp) (by simp) (fun _ => by simp)
  have gac : sched.activate_thread gS ar s4 a4 = sched.activate_thread st ar s4 a4 :=
    activate_thread.gw ar s4 a4 hcur4 hd' hy4 nrm4 rYt rSt rFi wNi
      (fun hr pc => hwS _ (by rw [mem_wr_ne' aNx sA nNs]; exact hr) (by rw [mem_wr_ne' aNx aA nNa]; exact aff4))
      rSc (by rw [sc4]; exact rMd) rIq
  refine ⟨gac, fun s5 a5 eac => ?_⟩
  obtain ⟨w45, hst5⟩ := activate_fp ar P.hT P.hd hN4 hcur4 hy4 eac
  have e5N : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt X (L.cpu X) o := fun o => by
    rw [w45.2.1, nodeAt_of_ksb w45.1, e4N]
  by_cases hvm : L.mem X (stA d) = sched.TS_RUNNING_VM
  · refine ⟨PathObl.sched.cur_thread.guard s5
      (by rw [e5N]; exact (hNd _ (by rw [curth_val]; omega) (by rw [curth_val])).1), fun t et => ?_⟩
    have hcur5' : L.curW s5 = d := by
      obtain ⟨w45', -⟩ := activate_fp ar P.hT P.hd hN4 hcur4 hy4 eac
      unfold LawfulStore.curW
      rw [w45'.2.1, nodeAt_of_ksb w45'.1]
      refine (w45'.mem_eq (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val])) ?_).trans ?_
      · rintro (e | e | e)
        · exact tcb_node_ne hN4 P.hd hd' (by simp) (by rw [curth_val]; omega) e.symm
        · rw [stA_eq] at e
          exact tcb_node_ne hN4 P.hd hd' (by simp) (by rw [curth_val]; omega) e.symm
        · have e' := congrArg UScalar.val e
          rw [nodeAt_val hN4 (by rw [curth_val]; omega), nodeAt_val hN4 (by rw [act_val]; omega), curth_val,
            act_val] at e'
          omega
      · exact hcur4
    rw [cur_thread_ok, hcur5'] at et
    obtain rfl := ok_inj_ff et
    exact hvc hvm s4 a4 (w34.mono fun b hb => hb.2) hcur4 s5 a5 eac
  have hst5' : L.mem s5 (stA d) ≠ sched.TS_RUNNING_VM := by
    rcases hst5 with e | e
    · rw [e]; simp [sched.TS_RUNNING, sched.TS_RUNNING_VM]
    · rw [e, hst4]; exact hvm
  have hcur5 : L.curW s5 = d := by
    have e : L.curW s5 = L.curW s4 := by
      unfold LawfulStore.curW
      rw [w45.2.1, nodeAt_of_ksb w45.1]
      refine w45.mem_eq (nodeAt_aligned hN4 (by rw [curth_val]; omega) (by rw [curth_val])) ?_
      rintro (e | e | e)
      · exact tcb_node_ne hN4 P.hd hd' (by simp) (by rw [curth_val]; omega) e.symm
      · rw [stA_eq] at e
        exact tcb_node_ne hN4 P.hd hd' (by simp) (by rw [curth_val]; omega) e.symm
      · have e' := congrArg UScalar.val e
        rw [nodeAt_val hN4 (by rw [curth_val]; omega), nodeAt_val hN4 (by rw [act_val]; omega), curth_val,
          act_val] at e'
        omega
    rw [e, hcur4]
  refine ⟨PathObl.sched.cur_thread.guard s5
    (by rw [e5N]; exact (hNd _ (by rw [curth_val]; omega) (by rw [curth_val])).1), fun t et => ?_⟩
  rw [cur_thread_ok, hcur5] at et
  have et' := ok_inj_ff et
  subst et'
  exact vcpu.check.guard_nvm ar s5 a5 _ rSt hst5'

/-- **The tail after a switch to `d`** (module docstring). -/
theorem sw_tail {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]
    (hA : P0.ArchTotal ar) (X : S) (a : A) {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω X d) (hcur : L.curW X = d)
    (hc : SCq st X Ω (L.cscW X) zc)
    (ht : L.mem X (scA d) ≠ L.cscW X → SCin st X Ω (L.mem X (scA d)) zt ∧
      ∀ b, InSC (L.mem X (scA d)) zt b → Outside b (L.cscW X) zc)
    (hact : L.mem X (scA d) = L.cscW X → L.rmax X (L.cscW X) ≠ 0#u64)
    (hrh : L.mem X (rhA (L := L) X) ≠ 0#u64 → L.mem X (rhA (L := L) X) ∈ T ∧
      R (scA (L.mem X (rhA (L := L) X))) ∧
      ∃ zq, SCin st X Ω (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq ∧
        (∀ b, Aligned b → InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → R b) ∧
        (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.cscW X →
          ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → Outside b (L.cscW X) zc) ∧
        (L.mem X (scA (L.mem X (rhA (L := L) X))) ≠ L.mem X (scA d) → L.mem X (scA d) ≠ L.cscW X →
          ∀ b, InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) zq b → Outside b (L.mem X (scA d)) zt))
    (htm : L.mem X (tmA (L := L) X) ≠ 0#u64 → L.mem X (tmA (L := L) X) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64))
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o))
    (hdt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME))
    (hSc : ScAcc R W (L.cscW X) zc) (hSi : L.mem X (scA d) ≠ L.cscW X → ScAcc R W (L.mem X (scA d)) zt)
    (hy0 : L.mem X (yieldA d) = 0#u64) (hnvm : L.mem X (stA d) ≠ sched.TS_RUNNING_VM)
    (haff : L.mem X (affA d) = L.cpu X)
    (rYt : R (yieldA d)) (rSt : R (stA d)) (rFi : R (regA d layout.reg.FAULT_IP))
    (wNi : W (regA d layout.reg.NEXT_IP)) (rSc : R (scA d)) (rIq : R (inqA d))
    (rMd : R (maxA (L.mem X (scA d))))
    (hwS : ∀ X', L.mem X' (stA d) = sched.TS_RESTART → L.mem X' (affA d) = L.cpu X →
      gS.write X' (stA d) sched.TS_RUNNING = st.write X' (stA d) sched.TS_RUNNING) :
    SwTail st gS ar X a :=
  sw_tail_core ar hA X a P hcur hc ht hact hrh htm hNd hdt hSc hSi hy0 haff rYt rSt rFi wNi rSc rIq rMd hwS
    (fun h => absurd h hnvm)

end main

end Fl4Proofs.P2
