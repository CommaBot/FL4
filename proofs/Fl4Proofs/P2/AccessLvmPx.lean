/-
# P2 (line lvm, gen 7): pieces of the **pending-exit** walk of `local_vm_exit`

With `PENDING ≠ 0` at the entry, the work's `vcpu.check` runs `vcpu.report` (the current thread's registers, its
IPC buffer, `v.PENDING`, then `STATE := RUNNING`), and `check_budget` / `schedule` / `activate_thread` /
`vcpu.check` run after those writes. Pieces:

* `vcpu.check_pend` / **`vcpu.check.guard_pend`**: `vcpu.check` of a `RUNNING_VM` thread with a pending exit is the
  report, on any store answering the state, binding and `PENDING` words and the report as `st`;
* `vcpu.check_nvm`: `vcpu.check` of a thread not in `RUNNING_VM` (after the report: now `RUNNING`) changes nothing
  (its guard is FootTimerIrqAcc's `vcpu.check.guard_nvm`); `lvm_consumed_ok`: `consumed` reads the node word;
* `sc_head_keep`, `suff_congr`: `sufficient` reads only the SC's head words (so it survives writes off the SC);
* `rel_ag`, `nodue_ag`: `RelNone` / `NoDueT` survive writes that keep this core's node words, the threads' SC
  and deadline words and the SC words (the report's writes: `irq_quiet_schedule`'s facts for the report's write
  set instead of the timer handler's `HW`);
* `repFr_finX`: the report's last step (`set_thread_state TS_RUNNING`) on a store whose `STATE` write is answered
  as `st`'s at each frame state (gen 5's `repFr_fin` with a per-state write, for the checked store of `move`).

No named premises.
-/
import Fl4Proofs.P2.AccessLvmOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.PathObl (NodeSt)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- `vcpu.check` of a `RUNNING_VM` thread with a pending exit is its report. -/
theorem vcpu.check_pend (s : S) (a : A) (t v : U64) (hst : L.mem s (stA t) = sched.TS_RUNNING_VM)
    (eb : vcpu.bound st s t = ok v) (hv0 : v ≠ 0#u64) {p : U64} (ep : vcpu.get st s v vcpu.PENDING = ok p)
    (hp : p ≠ 0#u64) :
    vcpu.check st ar s a t = (do let s1 ← vcpu.report st ar s a t 0#u64; ok (s1, a)) := by
  have hb : (v != 0#u64) = true := bne_iff_ne.mpr hv0
  have hb2 : (p != 0#u64) = true := bne_iff_ne.mpr hp
  unfold vcpu.check
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t), hst]
  simp only [bind_ok, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [eb]
  simp only [bind_ok]
  rw [if_pos hb, ep]
  simp only [bind_ok]
  rw [if_pos hb2]

/-- `vcpu.check` of a thread not in `RUNNING_VM` changes nothing. -/
theorem vcpu.check_nvm (s : S) (a : A) (t : U64) (h : L.mem s (stA t) ≠ sched.TS_RUNNING_VM) :
    vcpu.check st ar s a t = ok (s, a) := by
  unfold vcpu.check
  rw [eq_of_spec_fd (obj.Tcb.state.spec (L := L) s t)]
  simp only [bind_ok]
  rw [if_pos (bne_iff_ne.mpr h)]

/-- `consumed` reads this core's node word. -/
theorem lvm_consumed_ok (s : S) :
    sched.consumed st s = ok (L.mem s (L.nodeAt s (L.cpu s) layout.node.CONSUMED)) := by
  unfold sched.consumed
  simp only [L.cur_cpu_eq, bind_ok, node_get_ok]

variable {R W : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **`vcpu.check` with a pending exit on a guarded store**: the state, binding and `PENDING` words, and the
report (`hrep`). -/
theorem vcpu.check.guard_pend (s : S) (a : A) (t v : U64) (hst : R (stA t))
    (hvw : R (core.num.U64.wrapping_add t 3664#u64)) (hp : R (core.num.U64.wrapping_add v vcpu.PENDING))
    (eb : vcpu.bound st s t = ok v) (hv0 : v ≠ 0#u64) {p : U64} (ep : vcpu.get st s v vcpu.PENDING = ok p)
    (hp0 : p ≠ 0#u64)
    (hrep : vcpu.report gS ar s a t 0#u64 = vcpu.report st ar s a t 0#u64) :
    vcpu.check gS ar s a t = vcpu.check st ar s a t := by
  have hb : (v != 0#u64) = true := bne_iff_ne.mpr hv0
  have hb2 : (p != 0#u64) = true := bne_iff_ne.mpr hp0
  unfold vcpu.check
  rw [PathObl.obj.Tcb.state.guard _ s hst]
  refine PathObl.bind_guard_congr rfl fun i _ => ?_
  refine ite_congr rfl (fun _ => rfl) (fun _ => ?_)
  rw [vcpu.bound.guardT s t hvw, eb]
  simp only [bind_ok]
  rw [if_pos hb, if_pos hb, vcpu.get.guard s v _ hp, ep]
  simp only [bind_ok]
  rw [if_pos hb2, if_pos hb2, hrep]

end

/-! ## `sufficient` and `RelNone` / `NoDueT` across writes off the SCs and nodes -/

section keep
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- A well formed SC's head index and head refill survive writes that keep its words. -/
theorem sc_head_keep {X Y : S} {sc : U64} {z : Nat} (wf : RefillsWF st X sc z)
    (keep : ∀ b, Aligned b → InSC sc z b → L.mem Y b = L.mem X b) :
    L.rhead Y sc = L.rhead X sc ∧ L.refill Y sc (L.rhead X sc) = L.refill X sc (L.rhead X sc) := by
  obtain ⟨h8, hm, hfit⟩ := wf.bounds
  obtain ⟨-, -, -, hhd, -, hri⟩ := wf.inside
  obtain ⟨r1, r2, r3⟩ := hri (L.rhead X sc) wf.head_lt
  have hmin := wf.min_le
  simp at hmin
  refine ⟨keep _ (by unfold Aligned; rw [hhd]; omega) ⟨by rw [hhd]; omega, by rw [hhd]; omega⟩, ?_⟩
  simp only [LawfulStore.refill]
  rw [keep _ (by unfold Aligned; rw [r1]; omega) ⟨by rw [r1]; omega, by rw [r1]; omega⟩,
    keep _ (by unfold Aligned; rw [r2]; omega) ⟨by rw [r2]; omega, by rw [r2]; omega⟩]

/-- `SCq` survives writes that keep the SC's words (FootTimerFireNw's `SCq.agree'`, not imported here). -/
theorem scq_agree' {X Y : S} {c : U64} {z : Nat} (h : SCq st X Ω c z)
    (ag : ∀ b, Aligned b → InSC c z b → L.mem Y b = L.mem X b) : SCq st Y Ω c z := by
  have em : L.rmax Y c = L.rmax X c := ag _ h.2.2.2.2 h.2.2.2.1
  exact ⟨fun hm => (h.1 (em ▸ hm)).agree fun b hb hin => ag b hb hin, h.2.1, h.2.2⟩

/-- `sufficient` reads only the SC's head refill. -/
theorem suff_congr {A : Type} (ar : machine.Arch A) {X Y : S} {a : A} {sc u : U64}
    (h : L.rhead Y sc = L.rhead X sc ∧ L.refill Y sc (L.rhead X sc) = L.refill X sc (L.rhead X sc)) :
    sporadic.sufficient st ar Y a sc u = sporadic.sufficient st ar X a sc u := by
  unfold sporadic.sufficient sporadic.capacity
  rw [eq_of_spec_fd (sporadic.head.spec (L := L) X sc), eq_of_spec_fd (sporadic.head.spec (L := L) Y sc), h.1,
    h.2]

/-- **`RelNone` across writes** that keep this core's node words, every thread's SC word and every SC's words. -/
theorem rel_ag {X Y : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac X) (kY : L.ksb Y = L.ksb X)
    (cY : L.cpu Y = L.cpu X)
    (nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem Y (L.nodeAt X (L.cpu X) o) = L.mem X (L.nodeAt X (L.cpu X) o))
    (tf : ∀ y ∈ T, L.mem Y (scA y) = L.mem X (scA y))
    (keep : ∀ c ∈ Scs, ∀ b, Aligned b → InSC c (Z c) b → L.mem Y b = L.mem X b)
    (h : RelNone st X) : RelNone st Y := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, -, hS⟩ := hI
  have hcC := hq.cur
  have eA : ∀ o, L.nodeAt Y (L.cpu Y) o = L.nodeAt X (L.cpu X) o := fun o => by rw [cY, nodeAt_of_ksb kY]
  have eh := nd layout.node.RELEASE_HEAD (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  have ect : L.curTime Y = L.curTime X := by
    unfold LawfulStore.curTime LawfulStore.nodeA
    rw [eA]
    exact nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  unfold RelNone at h ⊢
  rw [ect, eA, eh]
  generalize hh : L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = h0 at h ⊢
  rcases h with h | h
  · exact Or.inl h
  by_cases h00 : h0 = 0#u64
  · exact Or.inl h00
  right
  have hrel := hq.release _ hcC
  have hmem : h0 ∈ R (L.cpu X) := by
    have e := hrel.head
    change L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) = _ at e
    rw [hh] at e
    cases hR : R (L.cpu X) with
    | nil => rw [hR] at e; exact absurd e h00
    | cons x xs => rw [hR] at e; simp only [List.headD_cons] at e; subst e; simp
  have hhT : h0 ∈ T := hq.memTR hcC hmem
  rw [tf h0 hhT]
  have haff : L.mem X (affA h0) = L.cpu X := hq.inR _ hcC h0 hmem
  have hrb : (L.mem X (inqA h0) &&& sched.Q_RELEASE) ≠ 0#u64 := (hq.released h0 hhT).2 (by rw [haff]; exact hmem)
  have hsc0 : L.mem X (scA h0) ≠ 0#u64 := hB.r h0 hhT hrb
  have hscS : L.mem X (scA h0) ∈ Scs := (hX.2.2.bound h0 hhT hsc0).1
  have hAc : L.mem X (scA h0) ∈ Ac := hB.sact h0 hhT (Or.inr (Or.inl hrb)) hsc0
  generalize hsc : L.mem X (scA h0) = sc at h hscS hAc ⊢
  have hmax : L.rmax X sc ≠ 0#u64 := (hS.act sc hscS).1 hAc
  obtain ⟨hwf, -, -⟩ := hS.all sc hscS
  obtain ⟨e1, e2⟩ := sc_head_keep (hwf hmax) (keep sc hscS)
  rw [e1, e2]
  exact h

/-- **`NoDueT` across writes** that keep this core's `TIMER_MIN` and the threads' deadline words. -/
theorem nodue_ag {X Y : S} {now : U64} (kY : L.ksb Y = L.ksb X) (cY : L.cpu Y = L.cpu X)
    (hm : Tz T (L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN)))
    (nd : L.mem Y (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN) = L.mem X (L.nodeAt X (L.cpu X) layout.node.TIMER_MIN))
    (tf : ∀ y ∈ T, L.mem Y (tdA y) = L.mem X (tdA y)) (h : NoDueT st X now) : NoDueT st Y now := by
  unfold NoDueT at h ⊢
  rw [cY, nodeAt_of_ksb kY, nd]
  rcases hm with h0 | hmT
  · exact Or.inl h0
  rcases h with h | h
  · exact Or.inl h
  right
  rw [tf _ hmT]
  exact h

end keep

/-! ## The report's last step on a store answering its `STATE` write per state -/

section fin
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac U : Set U64} {H : Heap} {Z : U64 → Nat}
variable {R W : U64 → Prop} {gS : machine.Store S} [PathObl.GRd gS st R] [PathObl.GWr gS st W]

/-- **The report's last step is guarded at every frame state**, the `STATE` write answered as `st`'s at each
(`hw`; gen 5's `repFr_fin` with `W (stA t)`). -/
theorem repFr_finX {s0 : S} {t : U64} (ht : TcbAddr t) (hsU : scA t ∉ U) (hn : NodeSt (L := L) R W s0)
    (hw : ∀ X, RepFr st T Cs Ω H Sg Rp Scs Nt Z Ac t U s0 X →
      gS.write X (stA t) sched.TS_RUNNING = st.write X (stA t) sched.TS_RUNNING)
    (h1 : R (stA t)) (h2 : R (scA t)) (h3 : R (maxA (L.mem s0 (scA t)))) (h4 : R (inqA t)) :
    ∀ s1, RepFr st T Cs Ω H Sg Rp Scs Nt Z Ac t U s0 s1 →
      sched.set_thread_state gS s1 t sched.TS_RUNNING = sched.set_thread_state st s1 t sched.TS_RUNNING := by
  intro s1 hr
  have w := hr.2.2
  have aS : Aligned (stA t) := by rw [stA_eq]; exact field_aligned ht (by simp) (by simp)
  have aC : Aligned (scA t) := field_aligned ht (by simp) (by simp)
  have nSC : stA t ≠ scA t := by
    rw [stA_eq]; exact tcb_word_ne ht ht (by simp) (by simp) (fun _ => by simp)
  refine set_thread_state.gw s1 t _ (NodeSt.of_wi hn w) (hw s1 hr) h1 h2 ?_ h4
  rw [mem_wr_ne' aS aC nSC, w.2.2 _ aC (scA_not_repW ht hsU)]
  exact h3

end fin

end Fl4Proofs.P2
