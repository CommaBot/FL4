/-
# P2: the guarded-store lemma for the fast paths' tail `switch_to`

`fastpath.switch_to.guard`: `switch_to Y a d` (the handler after a fault,
the faulting thread after a ReplyRecv) runs on `guard st R W` as on `st`
when, at its entry state `Y`, with `c` the current SC and `i` = `d`'s SC:

* `R` reads and `W` writes every word of the current core's node (`hNd`);
* `R` / `W` hold `c` and (when `i ≠ c`) `i` as `ScAcc` (whole SC read, ring
  and `CONSUMED` written);
* `R` holds `set_vm_root d`'s words (`RdVm`), the kernel's `DOMAIN_TIME`,
  `d`'s `SC`, `YIELD_TO`, state, `FAULT_IP`, `IN_QUEUES` words, and `W`
  `d`'s `NEXT_IP` and state;
* the release head `rh` (when there is one): its `SC` word, and its SC `q`
  read whole (`hrh`); the timer-min thread's deadline (`htm`);

under the tail facts of `P2/FootSlTail.lean`'s `sl_switch_to_foot` (P1's
`TailPld`, `SCq` of `c`, `SCin` of `i` disjoint from `c`, `YIELD_TO = 0`)
and, for the reads after `switch_sched_context` (known issue A):

* `hact`: when `i = c`, `c` is active (`REFILL_MAX ≠ 0`), so its ring is
  still well formed when `set_next_interrupt` reads its head; the callers
  have it from P1 (the thread's SC is active, `RefillsWF`, `min_le`);
* `q` is well formed and among `Ω` (`SCin`), and disjoint from `c` and `i`
  unless equal to one of them: its head refill is read after the switch
  wrote the rings of `c` and `i`.

The run: `TWo`-sets bound the writes (`switch_sched_context.fp`,
`set_next_interrupt.fp`, `send_pending.fp` of P1), so the node words,
TCB fields and `q`'s SC words the later callees read keep their entry
values or their ring invariant.

Generic over the Arch instance up to `P0.ArchTotal` (P1's `.fp` lemmas). No
premises.
-/
import Fl4Proofs.P2.AccessReply
import Fl4Proofs.P1.FastTailRR
import Fl4Proofs.P2.AccessVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {T Cs Ω : Set U64}

/-- Words of the node at offsets `O`, the rings of `c` and (when distinct)
`i`, and `c`'s `CONSUMED`. -/
def TWo (Y : S) (O : Nat → Prop) (c i : U64) (zc zt : Nat) (b : U64) : Prop :=
  (∃ o : U64, O o.val ∧ b = L.nodeA Y o) ∨ InRing c zc b ∨
    b = core.num.U64.wrapping_add c layout.sc.CONSUMED ∨ (i ≠ c ∧ InRing i zt b)

theorem TWo.mono {Y : S} {O O' : Nat → Prop} {c i : U64} {zc zt : Nat} (h : ∀ n, O n → O' n) {b : U64}
    (hb : TWo (L := L) Y O c i zc zt b) : TWo (L := L) Y O' c i zc zt b := by
  rcases hb with ⟨o, ho, e⟩ | h2 | h3 | h4
  · exact Or.inl ⟨o, h _ ho, e⟩
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr (Or.inl h3))
  · exact Or.inr (Or.inr (Or.inr h4))

/-- An aligned word outside `Ω` and off the node words `O` is not in `TWo`. -/
theorem not_TWo {Y : S} {O : Nat → Prop} {c i : U64} {zc zt : Nat}
    (hcΩ : ∀ x, Aligned x → InSC c zc x → x ∈ Ω) (hcC : InSC c zc (core.num.U64.wrapping_add c layout.sc.CONSUMED))
    (hiΩ : i ≠ c → ∀ x, Aligned x → InSC i zt x → x ∈ Ω) {b : U64} (hb : Aligned b) (hΩ : b ∉ Ω)
    (hn : ∀ o : U64, O o.val → b ≠ L.nodeA Y o) : ¬ TWo (L := L) Y O c i zc zt b := by
  rintro (⟨o, ho, e⟩ | h2 | rfl | ⟨hne, h4⟩)
  · exact hn o ho e
  · exact hΩ (hcΩ _ hb h2.inSC)
  · exact hΩ (hcΩ _ hb hcC)
  · exact hΩ (hiΩ hne _ hb h4.inSC)

/-- A TCB field is not in `TWo`. -/
theorem field_not_TWo {Y : S} {d : U64} {O : Nat → Prop} {c i : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω Y d) (hO : ∀ n, O n → n < 4288)
    (hcΩ : ∀ x, Aligned x → InSC c zc x → x ∈ Ω) (hcC : InSC c zc (core.num.U64.wrapping_add c layout.sc.CONSUMED))
    (hiΩ : i ≠ c → ∀ x, Aligned x → InSC i zt x → x ∈ Ω) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096)
    (h8 : K.val % 8 = 0) : ¬ TWo (L := L) Y O c i zc zt (core.num.U64.wrapping_add y K) := by
  have hy' := P.hT y hy
  refine not_TWo hcΩ hcC hiΩ (field_aligned hy' hK h8) (fun hm => out_ne_field (P.hΩ _ hm) hy hy' hK rfl) ?_
  intro o ho e
  exact node_ne_field P.hN (hO _ ho) hy hy' hK e.symm

/-- A node word at an offset off `O` is not in `TWo`. -/
theorem node_not_TWo {Y : S} {d : U64} {O : Nat → Prop} {c i : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω Y d) (hO : ∀ n, O n → n < 4288)
    (hcΩ : ∀ x, Aligned x → InSC c zc x → x ∈ Ω) (hcC : InSC c zc (core.num.U64.wrapping_add c layout.sc.CONSUMED))
    (hiΩ : i ≠ c → ∀ x, Aligned x → InSC i zt x → x ∈ Ω) {o' : U64} (ho' : o'.val < 4288) (h8 : o'.val % 8 = 0)
    (hno : ¬ O o'.val) : ¬ TWo (L := L) Y O c i zc zt (L.nodeA Y o') := by
  refine not_TWo hcΩ hcC hiΩ (nodeAt_aligned P.hN ho' h8)
    (fun hm => out_ne_node (P.hΩ _ hm) P.hcC P.hN ho' rfl) ?_
  intro o ho e
  have := congrArg UScalar.val e
  simp only [LawfulStore.nodeA] at this
  rw [nodeAt_val P.hN ho', nodeAt_val P.hN (hO _ ho)] at this
  exact hno (by rw [show o'.val = o.val by omega]; exact ho)

/-- An SC `q` disjoint from `c` and (unless equal) from `i` keeps its words
under `TWo` writes when its words are among `Ω`. -/
theorem sc_out_TWo {Y : S} {d : U64} {O : Nat → Prop} {c i q : U64} {zc zt zq : Nat}
    (P : TailPld (L := L) T Cs Ω Y d) (hO : ∀ n, O n → n < 4288 ∧ n % 8 = 0)
    (hqΩ : ∀ x, Aligned x → InSC q zq x → x ∈ Ω)
    (hcC : InSC c zc (core.num.U64.wrapping_add c layout.sc.CONSUMED))
    (hqc : ∀ b, InSC q zq b → Outside b c zc) (hqi : i ≠ c → ∀ b, InSC q zq b → Outside b i zt) :
    ∀ b, Aligned b → TWo (L := L) Y O c i zc zt b → Outside b q zq := by
  rintro b hb (⟨o, ho, rfl⟩ | h2 | rfl | ⟨hne, h4⟩)
  · exact node_out_place hqΩ P.hΩ P.hcC P.hN (hO _ ho).1 (hO _ ho).2
  · by_contra hn; unfold Outside at hn; push Not at hn
    have := hqc b ⟨hn.1, hn.2⟩; unfold Outside at this; unfold InRing at h2; omega
  · by_contra hn; unfold Outside at hn; push Not at hn
    have := hqc _ ⟨hn.1, hn.2⟩; unfold Outside at this; unfold InSC at hcC; omega
  · by_contra hn; unfold Outside at hn; push Not at hn
    have := hqi hne b ⟨hn.1, hn.2⟩; unfold Outside at this; unfold InRing at h4; omega

set_option maxHeartbeats 4000000 in
/-- **`switch_to Y a d`** (module docstring). -/
theorem fastpath.switch_to.guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (Y : S) (a : A)
    {d : U64} {zc zt : Nat}
    (P : TailPld (L := L) T Cs Ω Y d)
    (hc : SCq st Y Ω (L.cscW Y) zc)
    (ht : L.mem Y (scA d) ≠ L.cscW Y → SCin st Y Ω (L.mem Y (scA d)) zt ∧
      ∀ b, InSC (L.mem Y (scA d)) zt b → Outside b (L.cscW Y) zc)
    (hact : L.mem Y (scA d) = L.cscW Y → L.rmax Y (L.cscW Y) ≠ 0#u64)
    (hy0 : L.mem Y (yieldA d) = 0#u64)
    (hrh : L.mem Y (rhA (L := L) Y) ≠ 0#u64 → L.mem Y (rhA (L := L) Y) ∈ T ∧
      R (scA (L.mem Y (rhA (L := L) Y))) ∧
      ∃ zq, SCin st Y Ω (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq ∧
        (∀ b, Aligned b → InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → R b) ∧
        (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.cscW Y →
          ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → Outside b (L.cscW Y) zc) ∧
        (L.mem Y (scA (L.mem Y (rhA (L := L) Y))) ≠ L.mem Y (scA d) → L.mem Y (scA d) ≠ L.cscW Y →
          ∀ b, InSC (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq b → Outside b (L.mem Y (scA d)) zt))
    (htm : L.mem Y (tmA (L := L) Y) ≠ 0#u64 → L.mem Y (tmA (L := L) Y) ∈ T ∧
      R (core.num.U64.wrapping_add (L.mem Y (tmA (L := L) Y)) 3528#u64))
    (hRV : RdVm (L := L) R Y d)
    (hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeA Y o) ∧ W (L.nodeA Y o))
    (hdt : R (core.num.U64.wrapping_add (L.ksb Y) layout.ks.DOMAIN_TIME))
    (hSc : ScAcc R W (L.cscW Y) zc) (hSi : L.mem Y (scA d) ≠ L.cscW Y → ScAcc R W (L.mem Y (scA d)) zt)
    (hsc : R (scA d)) (hyt : R (yieldA d)) (hst : R (stA d)) (hrg : R (regA d layout.reg.FAULT_IP))
    (hwr : W (regA d layout.reg.NEXT_IP)) (hw : W (stA d)) (hinq : R (inqA d)) :
    fastpath.switch_to (PathObl.guard st R W) ar Y a d = fastpath.switch_to st ar Y a d := by
  have hd' := P.hT d P.hd
  have hcΩ : ∀ x, Aligned x → InSC (L.cscW Y) zc x → x ∈ Ω := hc.2.1
  have hcC : InSC (L.cscW Y) zc (core.num.U64.wrapping_add (L.cscW Y) layout.sc.CONSUMED) := hc.2.2.1.1
  have hiΩ : L.mem Y (scA d) ≠ L.cscW Y → ∀ x, Aligned x → InSC (L.mem Y (scA d)) zt x → x ∈ Ω :=
    fun hne => (ht hne).1.2
  -- the offsets
  let Osw : Nat → Prop := fun n => n = 24 ∨ n = 40 ∨ n = 56
  let Oall : Nat → Prop := fun n => n = 0 ∨ n = 16 ∨ n = 24 ∨ n = 40 ∨ n = 56 ∨ n = 80 ∨ n = 120
  have hOsw : ∀ n, Osw n → n < 4288 ∧ n % 8 = 0 := by
    intro n hn; rcases hn with h | h | h <;> subst h <;> decide
  have hOall : ∀ n, Oall n → n < 4288 ∧ n % 8 = 0 := by
    intro n hn; rcases hn with h | h | h | h | h | h | h <;> subst h <;> decide
  have swall : ∀ n, Osw n → Oall n := by
    intro n hn; rcases hn with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  let TA := TWo (L := L) Y Oall (L.cscW Y) (L.mem Y (scA d)) zc zt
  have fNot : ∀ {y K : U64}, y ∈ T → K.val < 4096 → K.val % 8 = 0 →
      ¬ TA (core.num.U64.wrapping_add y K) := fun hy hK h8 =>
    field_not_TWo P (fun n hn => (hOall n hn).1) hcΩ hcC hiΩ hy hK h8
  unfold fastpath.switch_to
  rw [vspace.set_vm_root.guard ar Y a d hRV]
  refine bind_guard_congr rfl fun p1 h1 => ?_
  obtain ⟨Yv, a1⟩ := p1
  have e1 := post_of_ok (vspace.set_vm_root.same hA Y a d) h1
  simp only at e1; subst Yv
  simp only [Aeneas.Std.uncurry_apply_pair]
  rw [sched.set_cur_thread.guard Y d (hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).2]
  refine bind_guard_congr rfl fun s2 h2 => ?_
  have e2 := post_of_ok (sched.set_cur_thread.spec Y d) h2
  subst e2
  rw [sched.set_action.guard (L.wr Y (L.nodeAt Y (L.cpu Y) layout.node.CUR_THREAD) d) _ (by rw [nd_wr]; exact (hNd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2)]
  refine bind_guard_congr rfl fun s3 h3 => ?_
  have e3 := post_of_ok (sched.set_action.spec _ sched.ACTION_RESUME_CURRENT) h3
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
  have nX : ∀ o, L.nodeA X o = L.nodeA Y o := fun o => by
    unfold LawfulStore.nodeA; rw [cX, nodeAt_of_ksb kX]
  have w0 : WritesIn st Y X TA := by
    rw [← hX]
    exact ((writesIn_wr cA).trans (writesIn_wr aA)).mono fun b hb => by
      rcases hb with e | e
      · exact Or.inl ⟨layout.node.CUR_THREAD, by simp [Oall, layout.node.CUR_THREAD], e⟩
      · exact Or.inl ⟨layout.node.SCHED_ACTION, by simp [Oall, layout.node.SCHED_ACTION], e⟩
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
  have hcX : SCq st X Ω (L.cscW Y) zc := by
    refine ⟨fun hm => ?_, hc.2.1, hc.2.2⟩
    have em : L.rmax X (L.cscW Y) = L.rmax Y (L.cscW Y) :=
      agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
    exact (hc.1 (em ▸ hm)).agree fun b hb hin => agΩ b (hc.2.1 b hb hin)
  have htX : L.mem Y (scA d) ≠ L.cscW Y →
      RefillsWF st X (L.mem Y (scA d)) zt ∧ ∀ b, InSC (L.mem Y (scA d)) zt b → Outside b (L.cscW Y) zc := by
    intro hne
    obtain ⟨h1, h2⟩ := ht hne
    exact ⟨h1.1.agree fun b hb hin => agΩ b (h1.2 b hb hin), h2⟩
  -- `switch_sched_context`
  refine bind_guard_congr ?_ fun p4 h4 => ?_
  · refine sched.switch_sched_context.guard hA X a1 (T := T) (zc := zc) (zt := zt) PX.hN
      (show L.mem X (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD))) = L.mem Y (scA d) by rw [hcur, esc])
      ecs (fun o ho h8 => ?_) hcX.1 hc.2.2.2 htX hSc hSi (fun o ho h8 => by rw [nX]; exact hNd o ho h8)
      (show R (scA (L.mem X (L.nodeA X layout.node.CUR_THREAD))) by rw [hcur]; exact hsc)
    refine ⟨nodeAt_aligned PX.hN ho h8, node_out_place hc.2.1 PX.hΩ PX.hcC PX.hN ho h8, fun hne => ?_⟩
    exact node_out_place (ht hne).1.2 PX.hΩ PX.hcC PX.hN ho h8
  obtain ⟨s4, a2⟩ := p4
  simp only [Aeneas.Std.uncurry_apply_pair]
  have F4 := post_of_ok (sched.switch_sched_context.fp hA X a1 (zt := zt) (zc := zc)
    (B := TWo (L := L) Y Osw (L.cscW Y) (L.mem Y (scA d)) zc zt) PX.hcC PX.hN PX.hΩ
    (by rw [ecs]; exact hcX)
    (by rw [hcur, esc, ecs]; intro hne; exact ⟨⟨(htX hne).1, (ht hne).1.2⟩, (ht hne).2⟩)
    (by rw [nX]; exact Or.inl ⟨layout.node.REPROGRAM, by simp [Osw, layout.node.REPROGRAM], rfl⟩)
    (by rw [nX]; exact Or.inl ⟨layout.node.CONSUMED, by simp [Osw, layout.node.CONSUMED], rfl⟩)
    (by rw [nX]; exact Or.inl ⟨layout.node.CUR_SC, by simp [Osw, layout.node.CUR_SC], rfl⟩)
    (fun hne b _ h => by
      rw [hcur, esc, ecs] at hne; rw [hcur, esc] at h
      exact Or.inr (Or.inr (Or.inr ⟨hne, h⟩)))
    (fun b _ h => by
      rw [ecs] at h
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h)))) h4
  rw [hcur, esc, ecs] at F4
  obtain ⟨w34, -, wfc, wfi⟩ := F4
  have w4 : WritesIn st Y s4 TA :=
    (w0.trans w34).mono fun b hb => hb.elim id (TWo.mono swall)
  have k4 : L.ksb s4 = L.ksb Y := w4.1
  have c4 : L.cpu s4 = L.cpu Y := w4.2.1
  have n4 : ∀ o, L.nodeA s4 o = L.nodeA Y o := fun o => by
    unfold LawfulStore.nodeA; rw [c4, nodeAt_of_ksb k4]
  have P4 := P.ksb k4 c4
  have cur4 : L.curW s4 = d := by
    show L.mem s4 (L.nodeAt s4 (L.cpu s4) layout.node.CUR_THREAD) = d
    have e : L.nodeAt s4 (L.cpu s4) layout.node.CUR_THREAD = L.nodeA X layout.node.CUR_THREAD := by
      change L.nodeA s4 _ = _; rw [n4, nX]
    rw [e, w34.mem_eq (by rw [nX]; exact cA) ?_, hcur]
    rw [nX]
    exact node_not_TWo P (fun n hn => (hOsw n hn).1) hcΩ hcC hiΩ (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD]) (by simp [Osw, layout.node.CUR_THREAD])
  have sc4 : L.mem s4 (scA d) = L.mem Y (scA d) := by
    rw [scA_eq]; exact w4.mem_eq (P.tcbAl (by simp) (by simp)) (fNot P.hd (by simp) (by simp))
  -- the thread's SC, well formed after the switch
  have rmaxc : L.rmax X (L.cscW Y) = L.rmax Y (L.cscW Y) := agΩ _ (hc.2.1 _ hc.2.2.2.2 hc.2.2.2.1)
  have hd4 : RdHead (L := L) R s4 (L.mem Y (scA d)) := by
    by_cases hic : L.mem Y (scA d) = L.cscW Y
    · rw [hic]; exact hSc.head (wfc (by rw [rmaxc]; exact hact hic))
    · exact (hSi hic).head (wfi hic)
  -- the node words, unchanged
  have nkeep : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → ¬ Oall o.val →
      L.mem s4 (L.nodeA s4 o) = L.mem Y (L.nodeA Y o) := fun o ho h8 hno => by
    rw [n4]; exact w4.mem_eq (nodeAt_aligned P.hN ho h8)
      (node_not_TWo P (fun n hn => (hOall n hn).1) hcΩ hcC hiΩ ho h8 hno)
  have rh4 : L.mem s4 (rhA (L := L) s4) = L.mem Y (rhA (L := L) Y) :=
    nkeep layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [Oall, layout.node.RELEASE_HEAD])
  have tm4 : L.mem s4 (tmA (L := L) s4) = L.mem Y (tmA (L := L) Y) :=
    nkeep layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [Oall, layout.node.TIMER_MIN])
  have hrs4 : L.mem s4 (rhA (L := L) s4) ≠ 0#u64 → R (scA (L.mem s4 (rhA (L := L) s4))) ∧
      RdHead (L := L) R s4 (L.mem s4 (scA (L.mem s4 (rhA (L := L) s4)))) := by
    rw [rh4]
    intro h0
    obtain ⟨hrT, hrs, zq, hqin, hqR, hqc, hqi⟩ := hrh h0
    have eq4 : L.mem s4 (scA (L.mem Y (rhA (L := L) Y))) = L.mem Y (scA (L.mem Y (rhA (L := L) Y))) := by
      rw [scA_eq]; exact w4.mem_eq ((P.hT _ hrT) |> fun h => field_aligned h (by simp) (by simp))
        (fNot hrT (by simp) (by simp))
    refine ⟨hrs, ?_⟩
    rw [eq4]
    by_cases hqc' : L.mem Y (scA (L.mem Y (rhA (L := L) Y))) = L.cscW Y
    · rw [hqc']
      refine hSc.head (wfc ?_)
      rw [rmaxc]
      have := hqin.1.min_le
      rw [hqc'] at this
      intro e; rw [e] at this; revert this; simp [sporadic.MIN_REFILLS]
    by_cases hqi' : L.mem Y (scA (L.mem Y (rhA (L := L) Y))) = L.mem Y (scA d)
    · have hne : L.mem Y (scA d) ≠ L.cscW Y := fun e => hqc' (hqi'.trans e)
      rw [hqi']; exact (hSi hne).head (wfi hne)
    · have hwf : RefillsWF st s4 (L.mem Y (scA (L.mem Y (rhA (L := L) Y)))) zq :=
        hqin.1.writesIn w4 (sc_out_TWo P hOall hqin.2 hcC (hqc hqc') (hqi hqi'))
      exact (⟨hqR, fun _ _ _ => trivial, trivial⟩ : ScAcc R (fun _ => True) _ zq).head hwf
  have htd4 : L.mem s4 (tmA (L := L) s4) ≠ 0#u64 →
      R (core.num.U64.wrapping_add (L.mem s4 (tmA (L := L) s4)) 3528#u64) := by
    rw [tm4]; exact fun h0 => (htm h0).2
  -- `REPROGRAM`, `set_next_interrupt`
  simp only [guard_cur_cpu, L.cur_cpu_eq, bind_ok]
  have rpR : R (L.nodeAt s4 (L.cpu s4) layout.node.REPROGRAM) := by
    change R (L.nodeA s4 _); rw [n4]; exact (hNd _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).1
  rw [obj.node_get.guard s4 _ _ rpR, node_get_ok]
  simp only [bind_ok]
  -- the words after the switch: `ARMED`, `REPROGRAM`, `IPI_PENDING`
  let O2 : Nat → Prop := fun n => n = 56 ∨ n = 80 ∨ n = 120
  have o2all : ∀ n, O2 n → Oall n := by
    intro n hn; rcases hn with h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have hO2 : ∀ n, O2 n → n < 4288 ∧ n % 8 = 0 := fun n hn => hOall n (o2all n hn)
  let N2 : U64 → Prop := TWo (L := L) Y O2 (L.cscW Y) (L.mem Y (scA d)) zc zt
  refine bind_guard_congr ?_ fun p5 h5 => ?_
  · split
    · rw [sched.set_next_interrupt.guard ar s4 a2 (fun o ho h8 => by rw [n4]; exact hNd o ho h8)
        (by rw [k4]; exact hdt) (by rw [cur4]; exact hsc) (by rw [cur4, sc4]; exact hd4) hrs4 htd4]
      refine bind_guard_congr rfl fun p6 h6 => ?_
      obtain ⟨s6, a4⟩ := p6
      simp only [Aeneas.Std.uncurry_apply_pair]
      have w6 := post_of_ok (sched.set_next_interrupt.fp hA s4 a2 (B := fun _ => True) P4.hN trivial) h6
      have e : L.nodeAt s6 (L.cpu s4) layout.node.REPROGRAM = L.nodeA Y layout.node.REPROGRAM := by
        rw [nodeAt_of_ksb w6.1]; exact n4 _
      rw [obj.node_set.guard s6 _ _ _ (by rw [e]; exact (hNd _ (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).2)]
    · rfl
  obtain ⟨s5, a3⟩ := p5
  simp only [Aeneas.Std.uncurry_apply_pair]
  have w5 : WritesIn st s4 s5 N2 := by
    split at h5
    · obtain ⟨⟨s6, a4⟩, h6, h7⟩ := bind_eq_ok h5
      have w6 := post_of_ok (sched.set_next_interrupt.fp hA s4 a2
        (B := N2) P4.hN (by change N2 (L.nodeA s4 _); rw [n4]; exact Or.inl ⟨layout.node.ARMED, by simp [O2, layout.node.ARMED], rfl⟩)) h6
      simp only [Aeneas.Std.uncurry_apply_pair] at h7
      obtain ⟨s7, h7', h8⟩ := bind_eq_ok h7
      have h8' := ok_inj_ff h8
      simp only [Prod.mk.injEq] at h8'
      obtain ⟨rfl, rfl⟩ := h8'
      have e7 := post_of_ok (obj.node_set.spec s6 _ _ _) h7'
      subst e7
      have e : L.nodeAt s6 (L.cpu s4) layout.node.REPROGRAM = L.nodeA Y layout.node.REPROGRAM := by
        rw [nodeAt_of_ksb w6.1]; exact n4 _
      rw [e]
      refine (w6.trans (writesIn_wr (nodeAt_aligned P.hN (by simp [layout.node.REPROGRAM])
        (by simp [layout.node.REPROGRAM])))).mono fun b hb => hb.elim id fun h => ?_
      rw [h]; exact Or.inl ⟨layout.node.REPROGRAM, by simp [O2, layout.node.REPROGRAM], rfl⟩
    · have h5' := ok_inj_ff h5
      simp only [Prod.mk.injEq] at h5'
      obtain ⟨rfl, rfl⟩ := h5'
      exact WritesIn.refl _ _
  have P5 := P4.ksb w5.1 w5.2.1
  have n5 : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeA Y o := fun o => by
    rw [w5.2.1, nodeAt_of_ksb w5.1]; exact n4 o
  rw [smp.send_pending.guard ar s5 a3 (by rw [n5]; exact (hNd _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])).1)
    (by rw [n5]; exact (hNd _ (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])).2)]
  refine bind_guard_congr rfl fun p6 h6 => ?_
  obtain ⟨s6, a4⟩ := p6
  simp only [Aeneas.Std.uncurry_apply_pair]
  have w6' := post_of_ok (smp.send_pending.fp hA s5 a3 (B := N2) P5.hN
    (by rw [n5]; exact Or.inl ⟨layout.node.IPI_PENDING, by simp [O2, layout.node.IPI_PENDING], rfl⟩)) h6
  have w46 : WritesIn st s4 s6 N2 := (w5.trans w6').mono fun b hb => hb.elim id id
  have w6 : WritesIn st Y s6 TA := (w4.trans w46).mono fun b hb => hb.elim id (TWo.mono o2all)
  have n6 : ∀ o, L.nodeAt s6 (L.cpu s6) o = L.nodeA Y o := fun o => by
    rw [w6.2.1, nodeAt_of_ksb w6.1]; rfl
  have cur6 : L.curW s6 = d := by
    have e : L.curW s6 = L.mem s6 (L.nodeA s4 layout.node.CUR_THREAD) := by
      show L.mem s6 (L.nodeAt s6 (L.cpu s6) _) = _
      rw [n6, n4]
    rw [e, w46.mem_eq (by rw [n4]; exact cA) ?_]
    · exact cur4
    · rw [n4]
      exact node_not_TWo P (fun n hn => (hO2 n hn).1) hcΩ hcC hiΩ (by simp [layout.node.CUR_THREAD])
        (by simp [layout.node.CUR_THREAD]) (by simp [O2, layout.node.CUR_THREAD])
  have y6 : L.mem s6 (yieldA d) = 0#u64 := by
    rw [show yieldA d = core.num.U64.wrapping_add d 3472#u64 from rfl,
      w6.mem_eq (P.tcbAl (by simp) (by simp)) (fNot P.hd (by simp) (by simp))]
    exact hy0
  have sc6 : L.mem s6 (scA d) = L.mem Y (scA d) := by
    rw [scA_eq]; exact w6.mem_eq (P.tcbAl (by simp) (by simp)) (fNot P.hd (by simp) (by simp))
  have hmx : R (maxA (L.mem s6 (scA d))) := by
    rw [sc6]
    by_cases hic : L.mem Y (scA d) = L.cscW Y
    · rw [hic]; exact hSc.rd _ hc.2.2.2.2 hc.2.2.2.1
    · exact (hSi hic).off (ht hic).1.1 layout.sc.REFILL_MAX (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  have hn6 : NodeSt (L := L) R W s6 := by
    unfold NodeSt; rw [n6, n6]
    exact ⟨(hNd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1, (hNd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1,
      (hNd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).2⟩
  exact sched.activate_thread.guard ar s6 a4 cur6 hd' y6 hn6 hyt hst hrg hwr hw hsc hmx hinq

end

end Fl4Proofs.P2.PathObl
