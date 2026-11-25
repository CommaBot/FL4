/-
# P2: `schedule` after the I/O port invocation (line p2io)

With the current thread's SC the current SC (`SwOK.i`), the run of `schedRes`
(`set_action`, `switch_sched_context`, `set_next_interrupt`, `send_pending`)
writes only `SwB x c zc`: six words of the current core's node and the words of
the current SC `c`.  So it keeps the current thread, its TCB words, and the
timer / release heads, and its accesses stay inside `R` / `W`.

* `SwOK`: the facts at the invocation's end state;
* `SwOK.tcb`, `SwOK.node`: words outside `SwB`;
* `SwOK.sw_guard`, `SwOK.sw_fp`: `switch_sched_context`;
* `SwOK.sni_guard`: `set_next_interrupt` after it;
* `SwOK.schedRes`: the whole run writes `SwB`;
* `FinOK.of_sw`: `FinOK` from `SwOK`.

Premises: none (`SwOK` is a hypothesis, discharged at the path's entry).
-/
import Fl4Proofs.P2.AccessIoKeep
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st]
variable {T Cs Ω : Set U64} {x y : S} {c : U64} {zc : Nat}

/-- Offsets of the node words `schedRes` writes: `SCHED_ACTION`, `CUR_SC`,
`CONSUMED`, `REPROGRAM`, `ARMED`, `IPI_PENDING`. -/
def SwNode (o : U64) : Prop :=
  o.val = 16 ∨ o.val = 24 ∨ o.val = 40 ∨ o.val = 56 ∨ o.val = 80 ∨ o.val = 120

theorem SwNode.lt {o : U64} (h : SwNode o) : o.val < 4288 ∧ o.val % 8 = 0 := by
  unfold SwNode at h; omega

/-- The words `schedRes` may write from `x`. -/
def SwB (st : machine.Store S) [L : LawfulStore st] (x : S) (c : U64) (zc : Nat) (b : U64) : Prop :=
  (∃ o : U64, SwNode o ∧ b = L.nodeAt x (L.cpu x) o) ∨ InSC c zc b

/-- The state `schedRes` starts from: placement, the current thread bound to
the current SC `c` (`hcsc`), which is active and well formed, the accesses of
its own words, and the release-head SC either `c` or with its `HEAD` word
outside `c`. -/
structure SwOK (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (R W : U64 → Prop)
    (x : S) (c : U64) (zc : Nat) : Prop where
  tp : TcbPlaced T
  cpu : L.cpu x ∈ Cs
  np : NodePlaced st T x (L.cpu x)
  om : ∀ a ∈ Ω, OutsideObjs st T Cs x a
  cT : L.curW x ∈ T
  csc : L.mem x (L.nodeA x layout.node.CUR_SC) = c
  i : L.mem x (scA (L.curW x)) = c
  q : SCq st x Ω c zc
  act : L.rmax x c ≠ 0#u64
  acc : ScAcc R W c zc
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt x (L.cpu x) o) ∧ W (L.nodeAt x (L.cpu x) o)
  sc : R (scA (L.curW x))
  dt : R (core.num.U64.wrapping_add (L.ksb x) layout.ks.DOMAIN_TIME)
  td : L.mem x (tmA (L := L) x) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem x (tmA (L := L) x)) 3528#u64)
  rs : L.mem x (rhA (L := L) x) ≠ 0#u64 → R (scA (L.mem x (rhA (L := L) x))) ∧
    RdHead (L := L) R x (L.mem x (scA (L.mem x (rhA (L := L) x))))
  rh : L.mem x (rhA (L := L) x) ≠ 0#u64 → L.mem x (rhA (L := L) x) ∈ T ∧
    (L.mem x (scA (L.mem x (rhA (L := L) x))) = c ∨
      (headA (L.mem x (scA (L.mem x (rhA (L := L) x)))) ∈ Ω ∧
        Outside (headA (L.mem x (scA (L.mem x (rhA (L := L) x))))) c zc))

theorem SwOK.out (F : SwOK st T Cs Ω R W x c zc) (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    Outside (L.nodeAt x (L.cpu x) o) c zc := node_out_place F.q.2.1 F.om F.cpu F.np ho h8

theorem SwOK.tcb (F : SwOK st T Cs Ω R W x c zc) {t K : U64} (ht : t ∈ T) (hK : K.val < 4096)
    (h8 : K.val % 8 = 0) : Aligned (core.num.U64.wrapping_add t K) ∧
      ¬ SwB st x c zc (core.num.U64.wrapping_add t K) := by
  have ha := field_aligned (F.tp t ht) hK h8
  refine ⟨ha, ?_⟩
  rintro (⟨o, ho, e⟩ | hin)
  · exact node_ne_field F.np ho.lt.1 ht (F.tp t ht) hK e.symm
  · have := (F.om _ (F.q.2.1 _ ha hin)).2.1 t ht
    rw [tcb_wadd_val (F.tp t ht) hK] at this; omega

theorem SwOK.node (F : SwOK st T Cs Ω R W x c zc) (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hn : ¬ SwNode o) : ¬ SwB st x c zc (L.nodeAt x (L.cpu x) o) := by
  rintro (⟨o', ho', e⟩ | hin)
  · by_cases hv : o.val = o'.val
    · unfold SwNode at hn ho'; omega
    · exact nodeAt_ne F.np ho ho'.lt.1 hv e
  · have := F.out o ho h8
    unfold Outside at this; unfold InSC at hin; omega

theorem wi_node {A : U64 → Prop} (w : WritesIn st x y A) (o : U64) :
    L.nodeAt y (L.cpu y) o = L.nodeAt x (L.cpu x) o := by
  rw [w.2.1, nodeAt_of_ksb w.1]

theorem SwOK.nodeM (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (SwB st x c zc)) (o : U64)
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (hn : ¬ SwNode o) :
    L.mem y (L.nodeAt y (L.cpu y) o) = L.mem x (L.nodeAt x (L.cpu x) o) := by
  rw [wi_node w]; exact w.2.2 _ (nodeAt_aligned F.np ho h8) (F.node o ho h8 hn)

theorem SwOK.curM (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (SwB st x c zc)) :
    L.curW y = L.curW x :=
  F.nodeM w _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    (by simp [SwNode, layout.node.CUR_THREAD])

theorem SwOK.tcbM (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (SwB st x c zc)) {t K : U64}
    (ht : t ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0) :
    L.mem y (core.num.U64.wrapping_add t K) = L.mem x (core.num.U64.wrapping_add t K) :=
  w.2.2 _ (F.tcb ht hK h8).1 (F.tcb ht hK h8).2

/-- The words written before `schedRes` from the path's entry (`FAULT_IP`, the
core's `CUR_TIME` and `CONSUMED`, the invocation's `IoTW`) and by its
`set_action`. -/
def IoPW (st : machine.Store S) [L : LawfulStore st] (x : S) (b : U64) : Prop :=
  (∃ o : U64, (o.val = 16 ∨ o.val = 40 ∨ o.val = 48) ∧ b = L.nodeAt x (L.cpu x) o) ∨ IoTW (L.curW x) b

section
variable (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (IoPW st x))
include F w

theorem SwOK.nodeP (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0)
    (hn : ¬ (o.val = 16 ∨ o.val = 40 ∨ o.val = 48)) :
    L.mem y (L.nodeAt y (L.cpu y) o) = L.mem x (L.nodeAt x (L.cpu x) o) := by
  rw [wi_node w]
  refine w.2.2 _ (nodeAt_aligned F.np ho h8) ?_
  rintro (⟨o', ho', e⟩ | ⟨r, hr, e⟩ | e)
  · by_cases hv : o.val = o'.val
    · omega
    · exact nodeAt_ne F.np ho (by omega) hv e
  · have hv := congrArg UScalar.val e
    rw [regA_val (F.tp _ F.cT) hr, nodeAt_val F.np ho] at hv
    have := F.np.disj _ F.cT; omega
  · exact node_ne_field F.np ho F.cT (F.tp _ F.cT) (by rw [st_val]; omega) e

theorem SwOK.tcbP {t K : U64} (ht : t ∈ T) (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hge : 3328 < K.val) :
    L.mem y (core.num.U64.wrapping_add t K) = L.mem x (core.num.U64.wrapping_add t K) := by
  refine w.2.2 _ (field_aligned (F.tp t ht) hK h8) ?_
  rintro (⟨o, ho, e⟩ | hi)
  · exact node_ne_field F.np (by omega) ht (F.tp t ht) hK e.symm
  · exact iotw_tcb (F.tp _ F.cT) (F.tp t ht) hK hge hi

theorem SwOK.omP {b : U64} (hb : b ∈ Ω) : L.mem y b = L.mem x b := by
  refine w.2.2 _ (F.om b hb).1 ?_
  have ht := F.tp _ F.cT
  have h1 := (F.om b hb).2.1 _ F.cT
  rintro (⟨o, ho, e⟩ | ⟨r, hr, e⟩ | e)
  · exact out_ne_node (F.om b hb) F.cpu F.np (by omega) (congrArg UScalar.val e).symm
  · have hv := congrArg UScalar.val e
    rw [regA_val ht hr] at hv; omega
  · have hv := congrArg UScalar.val e
    unfold stA at hv
    rw [tcb_wadd_val ht (by rw [st_val]; omega), st_val] at hv; omega

theorem SwOK.wfP (h : RefillsWF st x c zc) : RefillsWF st y c zc :=
  h.agree fun b hb hin => F.omP w (F.q.2.1 b hb hin)

/-- **`SwOK` survives the path's writes before `schedRes`** and its
`set_action`. -/
theorem SwOK.frame : SwOK st T Cs Ω R W y c zc := by
  have hcur : L.curW y = L.curW x := F.nodeP w _ (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hcsc : L.mem y (L.nodeA y layout.node.CUR_SC) = L.mem x (L.nodeA x layout.node.CUR_SC) :=
    F.nodeP w _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have htm : L.mem y (tmA (L := L) y) = L.mem x (tmA (L := L) x) :=
    F.nodeP w _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hrh : L.mem y (rhA (L := L) y) = L.mem x (rhA (L := L) x) :=
    F.nodeP w _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have hcs : ∀ t ∈ T, L.mem y (scA t) = L.mem x (scA t) := fun t ht =>
    F.tcbP w ht (K := 3464#u64) (by simp) (by simp) (by simp)
  have hmx : L.rmax y c = L.rmax x c := F.omP w (F.q.2.1 _ F.q.2.2.2.2 F.q.2.2.2.1)
  refine ⟨F.tp, ?_, ?_, ?_, ?_, hcsc.trans F.csc, ?_, ⟨?_, F.q.2⟩, ?_, F.acc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w.2.1]; exact F.cpu
  · rw [w.2.1]; exact F.np.ksb w.1
  · exact fun a ha => (F.om a ha).ksb w.1
  · rw [hcur]; exact F.cT
  · rw [hcur, hcs _ F.cT]; exact F.i
  · rw [hmx]; exact fun h => F.wfP w (F.q.1 h)
  · rw [hmx]; exact F.act
  · intro o ho h8; rw [wi_node w]; exact F.nd o ho h8
  · rw [hcur]; exact F.sc
  · rw [w.1]; exact F.dt
  · rw [htm]; exact F.td
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]
    refine ⟨(F.rs h0).1, ?_⟩
    rcases (F.rh h0).2 with e | ⟨ho, ho'⟩
    · rw [e]; exact F.acc.head (F.wfP w (F.q.1 F.act))
    · have hb : L.rhead y (L.mem x (scA (L.mem x (rhA (L := L) x)))) =
          L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))) := F.omP w ho
      have := (F.rs h0).2
      unfold RdHead at this ⊢
      rw [hb]; exact this
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]; exact F.rh h0

end

/-- `SwOK` survives `set_action`. -/
theorem SwOK.act_wr (F : SwOK st T Cs Ω R W x c zc) (v : U64) :
    SwOK st T Cs Ω R W (L.wr x (L.nodeAt x (L.cpu x) layout.node.SCHED_ACTION) v) c zc ∧
    WritesIn st x (L.wr x (L.nodeAt x (L.cpu x) layout.node.SCHED_ACTION) v) (SwB st x c zc) := by
  have w0 := writesIn_wr (L := L) (s := x) (v := v) (nodeAt_aligned F.np (off := layout.node.SCHED_ACTION)
    (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
  exact ⟨F.frame (w0.mono fun b hb => Or.inl ⟨_, by simp [layout.node.SCHED_ACTION], hb⟩),
    w0.mono fun b hb => Or.inl ⟨_, by simp [SwNode, layout.node.SCHED_ACTION], hb⟩⟩

theorem SwOK.sw_guard {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (F : SwOK st T Cs Ω R W x c zc)
    (a : A) : sched.switch_sched_context gS ar x a = sched.switch_sched_context st ar x a :=
  sched.switch_sched_context.guard hA x a (zc := zc) (zt := zc) F.np F.i F.csc
    (fun o ho h8 => ⟨nodeAt_aligned F.np ho h8, F.out o ho h8, fun h => absurd rfl h⟩)
    F.q.1 F.q.2.2.2 (fun h => absurd rfl h) F.acc (fun h => absurd rfl h) F.nd F.sc

theorem SwOK.sw_fp {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (F : SwOK st T Cs Ω R W x c zc)
    {a a' : A} (h : sched.switch_sched_context st ar x a = ok (y, a')) :
    WritesIn st x y (SwB st x c zc) ∧ RefillsWF st y c zc := by
  have hi : L.mem x (scA (L.mem x (L.nodeA x layout.node.CUR_THREAD))) = L.mem x (L.nodeA x layout.node.CUR_SC) :=
    F.i.trans F.csc.symm
  have p := post_of_ok (sched.switch_sched_context.fp hA x a (T := T) (Ω := Ω) (Cs := Cs) (zt := zc) (zc := zc)
    (B := SwB st x c zc) F.cpu F.np F.om (by rw [F.csc]; exact F.q) (fun h => absurd hi h)
    (Or.inl ⟨_, by simp [SwNode, layout.node.REPROGRAM], rfl⟩)
    (Or.inl ⟨_, by simp [SwNode, layout.node.CONSUMED], rfl⟩)
    (Or.inl ⟨_, by simp [SwNode, layout.node.CUR_SC], rfl⟩)
    (fun h => absurd hi h)
    (fun b _ hb => by
      rw [F.csc] at hb
      rcases hb with hb | hb
      · exact Or.inr ⟨by unfold InRing at hb; omega, hb.2⟩
      · subst hb; exact Or.inr F.q.2.2.1.1)) h
  refine ⟨p.1, ?_⟩
  have := p.2.2.1
  rw [F.csc] at this
  exact this F.act

/-- The state after `switch_sched_context`, as the rest of `schedRes` needs it. -/
theorem SwOK.sni_guard {A : Type} (ar : machine.Arch A) (F : SwOK st T Cs Ω R W x c zc) (a : A)
    (w : WritesIn st x y (SwB st x c zc)) (hwf : RefillsWF st y c zc) :
    sched.set_next_interrupt gS ar y a = sched.set_next_interrupt st ar y a := by
  have hcur := F.curM w
  have hcs : L.mem y (scA (L.curW x)) = L.mem x (scA (L.curW x)) :=
    F.tcbM w F.cT (K := 3464#u64) (by simp) (by simp)
  have htm := F.nodeM w layout.node.TIMER_MIN (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
    (by simp [SwNode, layout.node.TIMER_MIN])
  have hrh := F.nodeM w layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD])
    (by simp [layout.node.RELEASE_HEAD]) (by simp [SwNode, layout.node.RELEASE_HEAD])
  refine sched.set_next_interrupt.guard ar y a ?_ ?_ ?_ ?_ ?_ ?_
  · intro o ho h8
    show R (L.nodeAt y (L.cpu y) o) ∧ W (L.nodeAt y (L.cpu y) o)
    rw [wi_node w]; exact F.nd o ho h8
  · rw [w.1]; exact F.dt
  · rw [hcur]; exact F.sc
  · rw [hcur, hcs, F.i]; exact F.acc.head hwf
  · intro h0
    rw [hrh] at h0 ⊢
    have e1 : L.mem y (scA (L.mem x (rhA (L := L) x))) = L.mem x (scA (L.mem x (rhA (L := L) x))) :=
      F.tcbM w (F.rh h0).1 (K := 3464#u64) (by simp) (by simp)
    rw [e1]
    refine ⟨(F.rs h0).1, ?_⟩
    rcases (F.rh h0).2 with e | ⟨ho, ho'⟩
    · rw [e]; exact F.acc.head hwf
    · have hb : L.rhead y (L.mem x (scA (L.mem x (rhA (L := L) x)))) =
          L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))) :=
        w.2.2 _ (F.om _ ho).1 (by
          rintro (⟨o, hoo, e⟩ | hin)
          · exact out_ne_node (F.om _ ho) F.cpu F.np hoo.lt.1 (congrArg UScalar.val e).symm
          · unfold Outside at ho'; unfold InSC at hin; omega)
      have := (F.rs h0).2
      unfold RdHead at this ⊢
      rw [hb]; exact this
  · show L.mem _ (tmA (L := L) _) ≠ 0#u64 → _
    rw [htm]; exact F.td

/-- **The run writes `SwB`.** -/
theorem SwOK.schedRes {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (F : SwOK st T Cs Ω R W x c zc)
    {a a1 : A} (h : schedRes st ar x a = ok (y, a1)) : WritesIn st x y (SwB st x c zc) := by
  unfold PathObl.schedRes at h
  rw [set_action_ok] at h
  simp only [bind_ok] at h
  obtain ⟨F4, w4⟩ := F.act_wr sched.ACTION_RESUME_CURRENT
  revert h F4 w4
  generalize L.wr x (L.nodeAt x (L.cpu x) layout.node.SCHED_ACTION) sched.ACTION_RESUME_CURRENT = s4
  intro h F4 w4
  have tr : ∀ {s5 : S}, WritesIn st s4 s5 (SwB st s4 c zc) → WritesIn st x s5 (SwB st x c zc) := fun w =>
    w4.trans1 (w.mono fun b hb => by
      rcases hb with ⟨o, ho, e⟩ | hb
      · exact Or.inl ⟨o, ho, by rw [e, wi_node w4]⟩
      · exact Or.inr hb)
  obtain ⟨⟨s5, a3⟩, h5, h⟩ := bind_eq_ok h
  have w5 := tr (F4.sw_fp hA h5).1
  simp only [Aeneas.Std.uncurry_apply_pair, L.cur_cpu_eq, bind_ok] at h
  rw [node_get_ok] at h
  simp only [bind_ok, bind_tc_ok] at h
  obtain ⟨⟨s6, a4⟩, h6, h⟩ := bind_eq_ok h
  have np5 : NodePlaced st T s5 (L.cpu s5) := by rw [w5.2.1]; exact F.np.ksb w5.1
  have nB : ∀ {z : S}, WritesIn st x z (SwB st x c zc) → ∀ o, SwNode o → SwB st x c zc (L.nodeAt z (L.cpu z) o) :=
    fun w o ho => Or.inl ⟨o, ho, wi_node w o⟩
  have w6 : WritesIn st x s6 (SwB st x c zc) := by
    by_cases hb : (L.mem s5 (L.nodeAt s5 (L.cpu s5) layout.node.REPROGRAM) != 0#u64) = true
    · rw [ite_eq_left hb] at h6
      obtain ⟨⟨s7, a5⟩, h7, h6⟩ := bind_eq_ok h6
      have w7 := w5.trans1 (post_of_ok (sched.set_next_interrupt.fp hA s5 a3 (T := T) (B := SwB st x c zc) np5
        (nB w5 _ (by simp [SwNode, layout.node.ARMED]))) h7)
      simp only [Aeneas.Std.uncurry_apply_pair] at h6
      obtain ⟨s8, h8, h6⟩ := bind_eq_ok h6
      rw [eq_ok_of_spec (obj.node_set.spec (L := L) s7 _ _ _)] at h8
      have e := ok_inj_ff h6
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      cases ok_inj_ff h8
      have ec : L.nodeAt s7 (L.cpu s5) layout.node.REPROGRAM = L.nodeAt x (L.cpu x) layout.node.REPROGRAM := by
        rw [nodeAt_of_ksb w7.1, w5.2.1]
      rw [ec]
      exact w7.trans1 ((writesIn_wr (nodeAt_aligned F.np (by simp [layout.node.REPROGRAM])
        (by simp [layout.node.REPROGRAM]))).mono fun b hb => Or.inl ⟨_, by simp [SwNode, layout.node.REPROGRAM], hb⟩)
    · rw [ite_eq_right hb] at h6
      have e := ok_inj_ff h6
      simp only [Prod.mk.injEq] at e
      obtain ⟨rfl, -⟩ := e
      exact w5
  simp only [Aeneas.Std.uncurry_apply_pair] at h
  have np6 : NodePlaced st T s6 (L.cpu s6) := by rw [w6.2.1]; exact F.np.ksb w6.1
  exact w6.trans1 (post_of_ok (smp.send_pending.fp hA s6 a4 (T := T) (B := SwB st x c zc) np6
    (nB w6 _ (by simp [SwNode, layout.node.IPI_PENDING]))) h)

/-- The current thread's words `activate_thread` touches, and its state. -/
structure ActOK (R W : U64 → Prop) (x : S) : Prop where
  y0 : L.mem x (yieldA (L.curW x)) = 0#u64
  st : L.mem x (stA (L.curW x)) = sched.TS_RESTART ∨ L.mem x (stA (L.curW x)) = sched.TS_RUNNING
  ryl : R (yieldA (L.curW x))
  rst : R (stA (L.curW x))
  rfi : R (regA (L.curW x) layout.reg.FAULT_IP)
  wnx : W (regA (L.curW x) layout.reg.NEXT_IP)
  rin : R (inqA (L.curW x))

theorem sts_mem {z z1 : S} {t v : U64} (hT : TcbAddr t) (hcur : L.curW z = t)
    (hn : L.nodeAt z (L.cpu z) layout.node.SCHED_ACTION ≠ stA t ∧
      Aligned (L.nodeAt z (L.cpu z) layout.node.SCHED_ACTION))
    (hc : L.nodeAt z (L.cpu z) layout.node.CUR_THREAD ≠ L.nodeAt z (L.cpu z) layout.node.SCHED_ACTION ∧
      Aligned (L.nodeAt z (L.cpu z) layout.node.CUR_THREAD))
    (hcs : L.nodeAt z (L.cpu z) layout.node.CUR_THREAD ≠ stA t)
    (e : sched.set_thread_state st z t v = ok z1) : L.mem z1 (stA t) = v ∧ L.curW z1 = t ∧
      L.ksb z1 = L.ksb z ∧ L.cpu z1 = L.cpu z := by
  have aS : Aligned (stA t) := field_aligned hT (by rw [st_val]; omega) (by rw [st_val])
  unfold sched.set_thread_state at e
  rw [set_state_ok'] at e; simp only [bind_ok] at e
  have h1 : L.mem (L.wr z (stA t) v) (stA t) = v := L.mem_wr_same aS
  have h2 : L.curW (L.wr z (stA t) v) = t := by
    unfold LawfulStore.curW
    rw [nd_wr, mem_wr_ne' aS hc.2 (fun e => hcs e.symm)]; exact hcur
  have kk : L.nodeAt (L.wr z (stA t) v) (L.cpu (L.wr z (stA t) v)) layout.node.SCHED_ACTION =
      L.nodeAt z (L.cpu z) layout.node.SCHED_ACTION := nd_wr _ _ _ _
  have kc : L.nodeAt (L.wr z (stA t) v) (L.cpu (L.wr z (stA t) v)) layout.node.CUR_THREAD =
      L.nodeAt z (L.cpu z) layout.node.CUR_THREAD := nd_wr _ _ _ _
  have kb : L.ksb (L.wr z (stA t) v) = L.ksb z := L.ksb_wr _ _ _
  have cb : L.cpu (L.wr z (stA t) v) = L.cpu z := LawfulStore.cpu_wr _ _ _
  revert e h1 h2 kk kc kb cb
  generalize L.wr z (stA t) v = u
  intro e h1 h2 kk kc kb cb
  have done : ∀ {u1 : S}, sched.set_action st u sched.ACTION_CHOOSE_NEW = ok u1 →
      L.mem u1 (stA t) = v ∧ L.curW u1 = t ∧ L.ksb u1 = L.ksb z ∧ L.cpu u1 = L.cpu z := fun {u1} e1 => by
    rw [set_action_ok, kk] at e1
    cases ok_inj_ff e1
    refine ⟨by rw [mem_wr_ne' hn.2 aS hn.1]; exact h1, ?_,
      (L.ksb_wr _ _ _).trans kb, (LawfulStore.cpu_wr _ _ _).trans cb⟩
    unfold LawfulStore.curW at h2 ⊢
    rw [nd_wr, kc, mem_wr_ne' hn.2 hc.2 (fun e => hc.1 e.symm), ← kc]; exact h2
  have same : ∀ {u1 : S}, ok u = ok u1 → L.mem u1 (stA t) = v ∧ L.curW u1 = t ∧
      L.ksb u1 = L.ksb z ∧ L.cpu u1 = L.cpu z := fun {u1} e1 => by
    cases ok_inj_ff e1; exact ⟨h1, h2, kb, cb⟩
  unfold sched.schedule_tcb at e
  obtain ⟨t1, -, e⟩ := bind_eq_ok e
  obtain ⟨b, -, e⟩ := bind_eq_ok e
  split at e
  · obtain ⟨i, -, e⟩ := bind_eq_ok e
    split at e
    · obtain ⟨b1, -, e⟩ := bind_eq_ok e
      split at e
      · exact same e
      · exact done e
    · exact same e
  · exact same e

/-- **`FinOK` from `SwOK` and `ActOK`** at the invocation's end state. -/
theorem FinOK.of_sw {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a3 : A}
    (k : L.ksb x = L.ksb s) (hc : L.cpu x = L.cpu s) (hnd : NoDue (L := L) x)
    (ha : L.actionW x = sched.ACTION_RESUME_CURRENT)
    (F : SwOK st T Cs Ω R W x c zc) (H : ActOK (L := L) R W x)
    (hw : SWr gS st (L.curW x) sched.TS_RUNNING) : FinOK (L := L) gS R W ar s x a3 := by
  have hT := F.tp _ F.cT
  have st4 : layout.tcb.STATE.val < 4096 := by rw [st_val]; omega
  have hs : ∀ {s1 : S} {a1 : A}, sched.schedule st ar x a3 = ok (s1, a1) → WritesIn st x s1 (SwB st x c zc) := by
    intro s1 a1 h
    rw [schedule_res_eq st ar x a3 (awaken_none ar x a3 hnd.1 hnd.2)
      (by rw [eq_of_spec_fd (sched.action.spec (L := L) x), ha])] at h
    exact F.schedRes hA h
  refine ⟨k, hc, hnd, F.td, F.rs, ha, ?_, ?_, ?_, ?_⟩
  · intro s4 h4
    rw [set_action_ok] at h4; cases ok_inj_ff h4
    exact (F.act_wr _).1.sw_guard hA a3
  · intro s4 s5 a4 h4 h5
    rw [set_action_ok] at h4; cases ok_inj_ff h4
    obtain ⟨F4, w4⟩ := F.act_wr sched.ACTION_RESUME_CURRENT
    obtain ⟨w5, hwf⟩ := F4.sw_fp hA h5
    have k5 : L.ksb s5 = L.ksb x := w5.1.trans w4.1
    have c5 : L.cpu s5 = L.cpu x := w5.2.1.trans w4.2.1
    refine ⟨k5, c5, fun _ => ⟨F4.sni_guard ar a4 w5 hwf, fun s7 a5 h7 => ?_⟩⟩
    have w7 := post_of_ok (sched.set_next_interrupt.fp hA s5 a4 (T := T) (B := fun _ => True)
      (by rw [w5.2.1]; exact F4.np.ksb w5.1) trivial) h7
    exact ⟨w7.1.trans k5, w7.2.1.trans c5⟩
  · intro s1 a1 h1
    have w := hs h1
    have hcur := F.curM w
    have tm : ∀ {K : U64}, K.val < 4096 → K.val % 8 = 0 →
        L.mem s1 (core.num.U64.wrapping_add (L.curW x) K) = L.mem x (core.num.U64.wrapping_add (L.curW x) K) :=
      fun h4 h8 => F.tcbM w F.cT h4 h8
    have e3 : L.mem s1 (scA (L.curW x)) = c := (tm (K := 3464#u64) (by simp) (by simp)).trans F.i
    have eN : ∀ o : U64, L.nodeAt s1 (L.cpu s1) o = L.nodeAt x (L.cpu x) o := fun o => wi_node w o
    refine sched.activate_thread.guardV ar s1 a1 hcur hT ((tm (K := 3472#u64) (by simp) (by simp)).trans H.y0)
      ?_ H.ryl H.rst H.rfi H.wnx hw F.sc ?_ H.rin
    · unfold NodeSt
      rw [eN, eN]
      have n0 := F.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      have n1 := F.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
      exact ⟨n0.1, n1.1, n1.2⟩
    · rw [e3]; exact F.acc.rd _ F.q.2.2.2.2 F.q.2.2.2.1
  · intro s1 a1 s2 a2 h1 h2
    have w := hs h1
    have hcur := F.curM w
    have hst : L.mem s1 (stA (L.curW x)) = L.mem x (stA (L.curW x)) := F.tcbM w F.cT st4 (by rw [st_val])
    have hy : L.mem s1 (yieldA (L.curW x)) = L.mem x (yieldA (L.curW x)) :=
      F.tcbM w F.cT (K := 3472#u64) (by simp) (by simp)
    have eN : ∀ o : U64, L.nodeAt s1 (L.cpu s1) o = L.nodeAt x (L.cpu x) o := fun o => wi_node w o
    have n0 := F.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
    have np1 : NodePlaced st T s1 (L.cpu s1) := by rw [w.2.1]; exact F.np.ksb w.1
    have key : L.mem s2 (stA (L.curW x)) = sched.TS_RUNNING ∧ L.curW s2 = L.curW x ∧ L.ksb s2 = L.ksb s1 ∧
        L.cpu s2 = L.cpu s1 := by
      unfold sched.activate_thread at h2
      rw [cur_thread_ok, hcur] at h2
      simp only [bind_ok] at h2
      rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s1 (L.curW x)),
        show L.mem s1 (yieldA (L.curW x)) = 0#u64 from hy.trans H.y0] at h2
      simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, Aeneas.Std.uncurry_apply_pair] at h2
      rw [state_ok', hst] at h2
      simp only [bind_ok] at h2
      split at h2
      · obtain ⟨pc, -, h2⟩ := bind_eq_ok h2
        rw [set_reg_ok'] at h2
        simp only [bind_ok] at h2
        obtain ⟨z1, hz, h2⟩ := bind_eq_ok h2
        have e := ok_inj_ff h2
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        have ct : layout.node.CUR_THREAD.val < 4288 := by simp [layout.node.CUR_THREAD]
        have ct8 : layout.node.CUR_THREAD.val % 8 = 0 := by simp [layout.node.CUR_THREAD]
        have sa : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
        have sa8 : layout.node.SCHED_ACTION.val % 8 = 0 := by simp [layout.node.SCHED_ACTION]
        have hr : layout.reg.NEXT_IP.val < 384 := by simp [layout.reg.NEXT_IP]
        have aR : Aligned (regA (L.curW x) layout.reg.NEXT_IP) := by
          unfold Aligned; rw [regA_val hT hr]; have := hT.align; omega
        have nR : regA (L.curW x) layout.reg.NEXT_IP ≠ L.nodeAt s1 (L.cpu s1) layout.node.CUR_THREAD := fun e => by
          have hv := congrArg UScalar.val e
          rw [regA_val hT hr, nodeAt_val np1 ct] at hv
          have := np1.disj _ F.cT; omega
        obtain ⟨p1, p2, p3, p4⟩ := sts_mem (t := L.curW x) (v := sched.TS_RUNNING) hT
          (by show L.mem _ (L.nodeAt _ _ _) = _
              rw [nd_wr, mem_wr_ne' aR (nodeAt_aligned np1 ct ct8) nR]; exact hcur)
          (by rw [nd_wr]; exact ⟨node_ne_field np1 sa F.cT hT st4, nodeAt_aligned np1 sa sa8⟩)
          (by rw [nd_wr, nd_wr]
              exact ⟨nodeAt_ne np1 ct sa (by simp [layout.node.CUR_THREAD, layout.node.SCHED_ACTION]),
                nodeAt_aligned np1 ct ct8⟩)
          (by rw [nd_wr]; exact node_ne_field np1 ct F.cT hT st4) hz
        exact ⟨p1, p2, p3.trans (L.ksb_wr _ _ _), p4.trans (LawfulStore.cpu_wr _ _ _)⟩
      · rename_i hne
        have e := ok_inj_ff h2
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, -⟩ := e
        exact ⟨hst.trans (H.st.resolve_left hne), hcur, rfl, rfl⟩
    obtain ⟨e1, e2, e3, e4⟩ := key
    refine ⟨?_, ?_, ?_⟩
    · rw [e4, nodeAt_of_ksb e3, eN]; exact n0.1
    · rw [e2]; exact H.rst
    · rw [e2]; exact e1

end

end Fl4Proofs.P2.PathObl
