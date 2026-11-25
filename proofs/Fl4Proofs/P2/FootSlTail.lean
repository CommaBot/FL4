/-
# P2 (line p2sl): the fast paths' common tail, with its write footprint

Both fast paths of `syscall.handle_syscall_local` end with
`fastpath.switch_to Y a d` (the handler after a fault, the faulting thread
after a ReplyRecv). P1's `switch_to_nvm` reads the tail through the coarse
footprint `FreeCd` (every `Ω` word and the low node words). Here the tail's
writes are bounded by any word set `B` that holds

* every word of the current core's node,
* the current SC's refill ring and `CONSUMED` word,
* `d`'s SC's refill ring (when it is not the current SC),
* `d`'s words below and at its state word (`NEXT_IP`, the state),

when `d` yields to no SC (`YIELD_TO = 0`: `complete_yield_to` would write
the SC it yields to): `sl_switch_to_foot`. `sl_activate_foot` is
`activate_thread`'s part.

No premises.
-/
import Fl4Proofs.P1.FastTailRR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

section
variable {S : Type _} {A : Type _} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A}
variable {T Cs Ω : Set U64}

/-- The words `activate_thread` of `d` may write from `X`: a register of `d`
below its state word, its state word, the current core's action word. -/
def ActW (X : S) (d : U64) (b : U64) : Prop :=
  (∃ K : U64, K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add d K) ∨ b = stA d ∨
    b = actA (L := L) X

/-- **`activate_thread` of the current thread `d`, which yields to no SC**,
writes only `ActW`. -/
theorem sl_activate_foot (X : S) (a : A) {d : U64} (hd : TcbAddr d) (hN : NodePlaced st T X (L.cpu X))
    (hcur : L.curW X = d) (hy : L.mem X (yieldA d) = 0#u64) :
    sched.activate_thread st ar X a ⦃ r => WritesIn st X r.1 (ActW (L := L) X d) ⦄ := by
  unfold sched.activate_thread
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have ect' : ct = d := by rw [ect]; exact hcur
  subst ect'
  step with obj.Tcb.yield_to.spec as ⟨i, ei⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = X) ?_ ?_
  · split
    · rename_i hv; exfalso; rw [ei, hy] at hv; simp at hv
    · exact (WP.spec_ok _).2 rfl
  rintro ⟨s1, a1⟩ e1
  simp only at e1; subst e1
  try simp only [WP.uncurry'_pair]
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  have sA : Aligned (stA ct) := by rw [stA_eq]; exact field_aligned hd (by simp) (by simp)
  have aA : Aligned (actA (L := L) s1) := nodeAt_aligned hN (by rw [act_val]; omega) (by rw [act_val])
  split
  · step with obj.Tcb.reg.spec as ⟨pc, _⟩
    refine WP.spec_bind (obj.Tcb.set_reg.wrK s1 ct layout.reg.NEXT_IP pc hd (by simp [layout.reg.NEXT_IP])) ?_
    rintro s2 ⟨K, hK, e2⟩
    subst e2
    have hK' : K.val < 3328 := by rw [hK]; simp [layout.reg.NEXT_IP]
    have kA : Aligned (core.num.U64.wrapping_add ct K) := field_aligned hd (by omega) (by rw [hK]; omega)
    refine WP.spec_bind (set_thread_state_act _ ct sched.TS_RUNNING) fun s4 e4 => ?_
    simp only [WP.spec_ok]
    have w1 : WritesIn st s1 (L.wr s1 (core.num.U64.wrapping_add ct K) pc) (ActW (L := L) s1 ct) :=
      (writesIn_wr kA).mono fun b e => Or.inl ⟨K, hK', by rw [hK]; omega, e⟩
    have w2 : ∀ Y : S, WritesIn st Y (L.wr Y (stA ct) sched.TS_RUNNING) (ActW (L := L) s1 ct) := fun Y =>
      (writesIn_wr sA).mono fun b e => Or.inr (Or.inl e)
    rcases e4 with e | e <;> subst e
    · exact (w1.trans (w2 _)).mono fun b hb => hb.elim id id
    · rw [actA_wr]
      exact ((w1.trans (w2 _)).trans ((writesIn_wr aA).mono fun b e => Or.inr (Or.inr e))).mono
        fun b hb => by rcases hb with (h | h) | h <;> exact h
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)

set_option maxHeartbeats 1600000 in
/-- **The fast paths' tail `switch_to Y a d`** writes only words of any set
`B` holding the current core's node, the current SC's ring and `CONSUMED`
word, `d`'s SC's ring, and `d`'s words up to its state word, when `d`
yields to no SC (module docstring). -/
theorem sl_switch_to_foot (hA : P0.ArchTotal ar) (Y : S) (a : A) {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω Y d)
    (hc : SCq st Y Ω (L.cscW Y) zc)
    (ht : L.mem Y (scA d) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA d)) zt ∧
      ∀ b, InSC (L.mem Y (scA d)) zt b → Outside b (L.cscW Y) zc)
    (hy0 : L.mem Y (yieldA d) = 0#u64) {B : U64 → Prop}
    (hBn : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → B (L.nodeAt Y (L.cpu Y) o))
    (hBc : ∀ b, Aligned b → (InRing (L.cscW Y) zc b ∨
      b = core.num.U64.wrapping_add (L.cscW Y) layout.sc.CONSUMED) → B b)
    (hBt : L.mem Y (scA d) ≠ L.cscW Y → ∀ b, Aligned b → InRing (L.mem Y (scA d)) zt b → B b)
    (hBd : ∀ K : U64, K.val ≤ 3328 → K.val % 8 = 0 → B (core.num.U64.wrapping_add d K)) :
    fastpath.switch_to st ar Y a d ⦃ r => WritesIn st Y r.1 B ⦄ := by
  have hd' := P.hT d P.hd
  unfold fastpath.switch_to
  refine WP.spec_bind (vspace.set_vm_root.same hA Y a d) ?_
  rintro ⟨Y1, a1⟩ e1
  simp only at e1; subst Y1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (sched.set_cur_thread.spec Y d) fun s2 e2 => ?_
  subst e2
  refine WP.spec_bind (sched.set_action.spec _ sched.ACTION_RESUME_CURRENT) fun s3 e3 => ?_
  subst e3
  simp only [nodeAt_wr, LawfulStore.cpu_wr]
  have cA := P.curAl
  have aA : Aligned (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION) :=
    nodeAt_aligned P.hN (by rw [act_val]; omega) (by rw [act_val])
  have nAC : L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD := by
    apply ne_of_valne
    rw [nodeAt_val P.hN (by rw [act_val]; omega), nodeAt_val P.hN (by rw [curth_val]; omega), act_val, curth_val]
    omega
  generalize hX : L.wr (L.wr Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD) d)
    (L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION) sched.ACTION_RESUME_CURRENT = X
  have kX : L.ksb X = L.ksb Y := by rw [← hX, L.ksb_wr, L.ksb_wr]
  have cX : L.cpu X = L.cpu Y := by rw [← hX, LawfulStore.cpu_wr, LawfulStore.cpu_wr]
  have PX := P.ksb kX cX
  have w0 : WritesIn st Y X B := by
    rw [← hX]
    exact ((writesIn_wr cA).trans (writesIn_wr aA)).mono fun b hb => by
      rcases hb with e | e <;> rw [e]
      · exact hBn _ (by rw [curth_val]; omega) (by rw [curth_val])
      · exact hBn _ (by rw [act_val]; omega) (by rw [act_val])
  have ag : ∀ b, Aligned b → b ≠ L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD →
      b ≠ L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION → L.mem X b = L.mem Y b := by
    intro b hb h1 h2
    rw [← hX, mem_wr_ne' aA hb (Ne.symm h2), mem_wr_ne' cA hb (Ne.symm h1)]
  have agΩ : ∀ b ∈ Ω, L.mem X b = L.mem Y b := fun b hb => ag b (P.hΩ b hb).1
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [curth_val]; omega) (by rw [e]))
    (fun e => out_ne_node (P.hΩ b hb) P.hcC P.hN (by rw [act_val]; omega) (by rw [e]))
  have agT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem X (core.num.U64.wrapping_add d K) = L.mem Y (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    ag _ (P.tcbAl hK h8) (fun e => node_ne_field P.hN (by rw [curth_val]; omega) P.hd hd' hK e.symm)
      (fun e => node_ne_field P.hN (by rw [act_val]; omega) P.hd hd' hK e.symm)
  have csA : Aligned (L.nodeAt Y (L.cpu Y) layout.node.CUR_SC) :=
    nodeAt_aligned P.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have ecs : L.mem X (L.nodeA X layout.node.CUR_SC) = L.cscW Y := by
    unfold LawfulStore.nodeA LawfulStore.cscW LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX]
    have v24 := nodeAt_val P.hN (off := layout.node.CUR_SC) (by simp [layout.node.CUR_SC])
    have v0 := nodeAt_val P.hN (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])
    have v16 := nodeAt_val P.hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    refine ag _ csA ?_ ?_ <;> apply ne_of_valne
    · rw [v24, v0]; simp [layout.node.CUR_SC, layout.node.CUR_THREAD]
    · rw [v24, v16]; simp [layout.node.CUR_SC, layout.node.SCHED_ACTION]
  have hcur : L.mem X (L.nodeA X layout.node.CUR_THREAD) = d := by
    unfold LawfulStore.nodeA
    rw [cX, nodeAt_of_ksb kX, ← hX, mem_wr_ne' aA cA nAC, L.mem_wr_same cA]
  have esc : L.mem X (scA d) = L.mem Y (scA d) := by rw [scA_eq]; exact agT _ (by simp) (by simp)
  have eyt : L.mem X (yieldA d) = L.mem Y (yieldA d) := agT 3472#u64 (by simp) (by simp)
  have hcX : SCq st X Ω (L.mem X (L.nodeA X layout.node.CUR_SC)) zc := by
    rw [ecs]
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X (L.cscW Y) = L.rmax Y (L.cscW Y) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD))) ≠ L.mem X (L.nodeA X layout.node.CUR_SC) →
      SCin st X Ω (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt ∧
      ∀ b, InSC (L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD)))) zt b →
        Outside b (L.mem X (L.nodeA X layout.node.CUR_SC)) zc := by
    rw [hcur, esc, ecs]
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.agree agΩ, h2⟩
  -- the tail's words: `B` words that are `Ω` words or low node words
  let C : U64 → Prop := fun b => B b ∧ FreeCd (L := L) X Ω b
  have cN : ∀ Z : S, L.ksb Z = L.ksb X → L.cpu Z = L.cpu X → ∀ o : U64, LowFree o.val →
      C (L.nodeAt Z (L.cpu Z) o) := by
    intro Z hk hcz o ho
    have e : L.nodeAt Z (L.cpu Z) o = L.nodeAt X (L.cpu X) o := by rw [hcz, nodeAt_of_ksb hk]
    have e' : L.nodeAt X (L.cpu X) o = L.nodeAt Y (L.cpu Y) o := by rw [cX, nodeAt_of_ksb kX]
    simp only [LowFree] at ho
    refine ⟨?_, Or.inr ⟨o, by simp only [LowFree]; exact ho, e⟩⟩
    rw [e, e']; exact hBn o (by omega) ho.2.1
  have cNA : ∀ o : U64, LowFree o.val → C (L.nodeA X o) := fun o ho => cN X rfl rfl o ho
  refine WP.spec_bind (sched.switch_sched_context.fp hA X a1 (zt := zt) (zc := zc) (B := C)
    PX.hcC PX.hN PX.hΩ hcX htX (cNA _ (by simp [layout.node.REPROGRAM, LowFree]))
    (cNA _ (by simp [layout.node.CONSUMED, LowFree])) (cNA _ (by simp [layout.node.CUR_SC, LowFree]))
    (fun hne b hb h => by
      have hne' := hne
      rw [hcur, esc, ecs] at hne'
      have h' := h
      rw [hcur, esc] at h'
      exact ⟨hBt hne' b hb h', Or.inl ((htX hne).1.2 b hb h.inSC)⟩)
    (fun b hb h => by
      refine ⟨hBc b hb (by rw [ecs] at h; exact h), ?_⟩
      rcases h with h | rfl
      · exact Or.inl (hcX.2.1 b hb h.inSC)
      · exact Or.inl (hcX.2.1 _ hb hcX.2.2.1.1))) ?_
  rintro ⟨s4, a2⟩ ⟨w4, -⟩
  try simp only [WP.uncurry'_pair]
  have P4 := PX.ksb w4.1 w4.2.1
  step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st X r.1 C) ?_ ?_
  · split
    · refine WP.spec_bind (sched.set_next_interrupt.fp hA s4 a2 (B := C) P4.hN
        (cN s4 w4.1 w4.2.1 _ (by simp [layout.node.ARMED, LowFree]))) ?_
      rintro ⟨s6, a4⟩ w6
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (obj.node_set.spec s6 c _ _) fun s7 e7 => ?_
      subst e7
      simp only [WP.spec_ok]
      have w7 : WritesIn st s6 (L.wr s6 (L.nodeAt s6 c layout.node.REPROGRAM) 0#u64) C := by
        rw [ec, nodeAt_of_ksb w6.1]
        exact (writesIn_wr (nodeAt_aligned P4.hN (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]))).mono fun b e => by
            rw [e]; exact cN s4 w4.1 w4.2.1 _ (by simp [layout.node.REPROGRAM, LowFree])
      exact ((w4.trans w6).trans w7).mono fun b hb => by
        rcases hb with (h | h) | h <;> exact h
    · exact (WP.spec_ok _).2 w4
  rintro ⟨s5, a3⟩ w5
  try simp only [WP.uncurry'_pair]
  have P5 := PX.ksb w5.1 w5.2.1
  refine WP.spec_bind (smp.send_pending.fp hA s5 a3 (B := C) P5.hN
    (cN s5 w5.1 w5.2.1 _ (by simp [layout.node.IPI_PENDING, LowFree]))) ?_
  rintro ⟨s6, a4⟩ w6'
  try simp only [WP.uncurry'_pair]
  have w6 : WritesIn st X s6 C := (w5.trans w6').mono fun b hb => hb.elim id id
  have P6 := PX.ksb w6.1 w6.2.1
  have kT : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem s6 (core.num.U64.wrapping_add d K) = L.mem X (core.num.U64.wrapping_add d K) := fun K hK h8 =>
    w6.mem_eq (PX.tcbAl hK h8) fun h => PX.tcb_nfree hK h.2
  have cur6 : L.curW s6 = d := by
    show L.mem s6 (L.nodeAt s6 (L.cpu s6) layout.node.CUR_THREAD) = d
    rw [w6.2.1, nodeAt_of_ksb w6.1, w6.mem_eq PX.curAl fun h => PX.cur_nfree h.2]; exact hcur
  have y6 : L.mem s6 (yieldA d) = 0#u64 := by
    rw [show yieldA d = core.num.U64.wrapping_add d 3472#u64 from rfl, kT _ (by simp) (by simp)]
    rw [show core.num.U64.wrapping_add d 3472#u64 = yieldA d from rfl, eyt]; exact hy0
  refine WP.spec_mono (sl_activate_foot (ar := ar) s6 a4 hd' P6.hN cur6 y6) fun r hr => ?_
  have hact : ∀ b, ActW (L := L) s6 d b → B b := by
    rintro b (⟨K, hK, h8, rfl⟩ | rfl | rfl)
    · exact hBd K (by omega) h8
    · rw [stA_eq]; exact hBd _ (by simp) (by simp)
    · have e : actA (L := L) s6 = L.nodeAt Y (L.cpu Y) layout.node.SCHED_ACTION := by
        show L.nodeAt s6 (L.cpu s6) _ = _
        rw [w6.2.1, nodeAt_of_ksb w6.1, cX, nodeAt_of_ksb kX]
      rw [e]; exact hBn _ (by rw [act_val]; omega) (by rw [act_val])
  exact (w0.trans ((w6.trans hr).mono fun b hb => hb.elim (fun h => h.1) (hact b))).mono
    fun b hb => hb.elim id id

end

end Fl4Proofs.P2
