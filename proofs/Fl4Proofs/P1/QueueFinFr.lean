/-
P1: field-level frames for the thread-finalisation steps after the unbinds
(`fin_thread`: `timer.remove`, `complete_yield_to`, `suspend`,
`debug_remove`): each keeps the finalised thread's `SC` and `BOUND_NTFN`
fields, and `suspend` leaves its state `INACTIVE`.
-/
import Fl4Proofs.P1.QueueKeeps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **`timer.remove`** keeps every TCB field outside the timer fields
3528–3568 (`TKeep`), so every thread's `SC`, `BOUND_NTFN` and `STATE`. -/
theorem timer.remove.keepF (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    timer.remove st s t ⦃ s' => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ TKeep st T s s' ∧
      ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (boundA y) = L.mem s (boundA y) ∧
        L.mem s' (stA y) = L.mem s (stA y) ⦄ :=
  WP.spec_mono (timer.remove.tf (s0 := s) s t (TF.start h) ht) fun s' ⟨h', _, _, k, _⟩ =>
    ⟨h', k, fun y hy => ⟨by rw [scA_eq]; exact k y hy _ (by simp) (by simp) (by simp),
      k y hy 3368#u64 (by simp) (by simp) (by simp), by rw [stA_eq]; exact k y hy _ (by simp) (by simp) (by simp)⟩⟩

/-- **`complete_yield_to`** keeps every thread's `SC`, `BOUND_NTFN` and
`STATE` (it writes the yielder's registers and `YIELD_TO` and the SC's
words). -/
theorem schedcontext.complete_yield_to.keepF {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S)
    (a : A) (y : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ≠ 0#u64 → y ∈ T) :
    schedcontext.complete_yield_to st ar s a y ⦃ s' _ =>
      ∀ x ∈ T, L.mem s' (scA x) = L.mem s (scA x) ∧ L.mem s' (boundA x) = L.mem s (boundA x) ∧
        L.mem s' (stA x) = L.mem s (stA x) ⦄ :=
  WP.spec_mono (schedcontext.complete_yield_to.cs hA s a y h hy) fun r hr => by
    obtain ⟨s', a'⟩ := r
    exact csw_keep h.1.choose_spec.choose_spec hr fun _ hb => hb

/-- **`suspend`** keeps the thread's `SC` and `BOUND_NTFN` fields and leaves
it `INACTIVE`. -/
theorem sched.suspend.keepF {A : Type _} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    sched.suspend st ar s a t ⦃ s' _ => L.mem s' (scA t) = L.mem s (scA t) ∧
      L.mem s' (boundA t) = L.mem s (boundA t) ∧ L.mem s' (stA t) = sched.TS_INACTIVE ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hsub := hSg.sub
  have hT := h0.tcbs
  have hta := hT t ht
  obtain ⟨hO, hR, hE⟩ := hX
  unfold sched.suspend
  refine WP.spec_bind (ipc.cancel_ipc.all s a t Q R h0 ht hB ⟨hO, hR, hE⟩ hsub) ?_
  rintro ⟨s1, a1⟩ ⟨h1, -, hX1, -, -, -, k1, -⟩
  try simp only [WP.uncurry'_pair]
  have F1 : ∀ K : U64, (K.val = 3464 ∨ K.val = 3368 ∨ K.val = 3472) →
      L.mem s1 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := fun K hK =>
    k1.fld t ht K (by omega) (by omega) (by omega) (by omega) (fun _ => ⟨by omega, by omega⟩)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧
      ∀ K : U64, (K.val = 3464 ∨ K.val = 3368 ∨ K.val = 3472) →
        L.mem s2 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K)) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, -⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      exact ⟨h2, fun K hK => (f2 K (by omega) (by omega) (by simp; omega)).trans (F1 K hK)⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1⟩
  rintro s2 ⟨h2, F2⟩
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ((h2.ready _ hc2).1.rel _ hp2)
      (h2.queued t ht).1)) ?_
  rintro s3 ⟨h3, hw3, -⟩
  have F3 : ∀ K : U64, (K.val = 3464 ∨ K.val = 3368 ∨ K.val = 3472) →
      L.mem s3 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := fun K hK =>
    (field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht (K := K) (by omega) (by omega)
      (by omega) (fun _ => by omega)).trans (F2 K hK)
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.inv s3 t _ R h3 ht)
    (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur) (h3.release _ hc3)
      (h3.released t ht).1)) ?_
  rintro s4 ⟨h4, hw4, -⟩
  have F4 : ∀ K : U64, (K.val = 3464 ∨ K.val = 3368 ∨ K.val = 3472) →
      L.mem s4 (core.num.U64.wrapping_add t K) = L.mem s (core.num.U64.wrapping_add t K) := fun K hK =>
    (field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht (K := K) (by omega) (by omega)
      (by omega) (fun _ => by omega)).trans (F3 K hK)
  refine WP.spec_bind (Pₘ := fun s5 => ∃ Q5 R5, SchedQueuesInv st T Cs Ω H s5 Q5 R5 ∧
      L.mem s5 (scA t) = L.mem s (scA t) ∧ L.mem s5 (boundA t) = L.mem s (boundA t)) ?_ ?_
  · unfold schedcontext.cancel_yield_to
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · exact (WP.spec_ok _).2 ⟨_, _, h4, by rw [scA_eq]; exact F4 _ (by simp), F4 3368#u64 (by simp)⟩
    step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
    split
    · rename_i _ hy
      have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) := F4 3472#u64 (by simp)
      have hyS : yt ∈ Scs := by
        rw [yt_post, y4]; exact hE.yt.2.1 t ht (by rw [← y4, ← yt_post]; simpa using hy)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      have hm := hsub _ (hO.syW yt hyS)
      obtain ⟨h5, -, f5⟩ := omega_wr (v := 0#u64) h4 hm
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      obtain ⟨h6, f6, -⟩ := field_wr_keep (K := 3472#u64) (v := 0#u64) h5 ht (by simp) (by simp) (by simp)
      refine ⟨_, _, h6, ?_, ?_⟩
      · rw [scA_eq]
        exact (f6 3464#u64 (by simp) (by simp) (by simp)).trans
          ((f5 t ht 3464#u64 (by simp) (by simp)).trans (F4 _ (by simp)))
      · exact (f6 3368#u64 (by simp) (by simp) (by simp)).trans
          ((f5 t ht 3368#u64 (by simp) (by simp)).trans (F4 3368#u64 (by simp)))
    · exact (WP.spec_ok _).2 ⟨_, _, h4, by rw [scA_eq]; exact F4 _ (by simp), F4 3368#u64 (by simp)⟩
  rintro s5 ⟨Q5, R5, h5, e1, e2⟩
  refine WP.spec_bind (sched.set_thread_state.state s5 t sched.TS_INACTIVE Q5 R5 h5 ht hO.ksb hsub) ?_
  rintro s6 ⟨est, k6⟩
  refine (WP.spec_ok _).2 ⟨(k6.scf ht).trans e1, ?_, est⟩
  show L.mem _ (core.num.U64.wrapping_add t 3368#u64) = _
  rw [k6.fld t ht 3368#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)]
  exact e2

/-- The three fields of every thread. -/
def Keep3 (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) ∧ L.mem s' (boundA y) = L.mem s (boundA y) ∧
    L.mem s' (stA y) = L.mem s (stA y)

theorem Keep3.trans {s1 s2 s3 : S} (h1 : Keep3 st T s1 s2) (h2 : Keep3 st T s2 s3) : Keep3 st T s1 s3 :=
  fun y hy => ⟨(h2 y hy).1.trans (h1 y hy).1, (h2 y hy).2.1.trans (h1 y hy).2.1,
    (h2 y hy).2.2.trans (h1 y hy).2.2⟩

theorem keep3_field {s : S} {x K v : U64} (hT : TcbPlaced T) (hx : x ∈ T) (hK : K.val < 4096) (hK8 : K.val % 8 = 0)
    (h1 : K.val ≠ 3464) (h2 : K.val ≠ 3368) (h3 : K.val ≠ 3328) :
    Keep3 st T s (L.wr s (core.num.U64.wrapping_add x K) v) := by
  have k : ∀ y ∈ T, ∀ K0 : U64, (K0.val = 3464 ∨ K0.val = 3368 ∨ K0.val = 3328) →
      L.mem (L.wr s (core.num.U64.wrapping_add x K) v) (core.num.U64.wrapping_add y K0) =
        L.mem s (core.num.U64.wrapping_add y K0) := fun y hy K0 hK0 =>
    L.mem_wr_ne (field_aligned (hT x hx) hK hK8) (field_aligned (hT y hy) (by omega) (by omega))
      (fun e => field_ne (hT x hx) (hT y hy) hK (by omega) (fun _ => by omega) (UScalar.eq_of_val_eq e))
  intro y hy
  exact ⟨by rw [scA_eq]; exact k y hy _ (by simp), k y hy 3368#u64 (by simp), by rw [stA_eq]; exact k y hy _ (by simp)⟩

theorem keep3_node {s : S} {c o v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288)
    (ho8 : o.val % 8 = 0) : Keep3 st T s (L.wr s (L.nodeAt s c o) v) := by
  have k : ∀ y ∈ T, ∀ K0 : U64, (K0.val = 3464 ∨ K0.val = 3368 ∨ K0.val = 3328) →
      L.mem (L.wr s (L.nodeAt s c o) v) (core.num.U64.wrapping_add y K0) =
        L.mem s (core.num.U64.wrapping_add y K0) := fun y hy K0 hK0 =>
    L.mem_wr_ne (nodeAt_aligned hN ho ho8) (field_aligned (hT y hy) (by omega) (by omega))
      (fun e => node_ne_field hN ho hy (hT y hy) (by omega) (UScalar.eq_of_val_eq e))
  intro y hy
  exact ⟨by rw [scA_eq]; exact k y hy _ (by simp), k y hy 3368#u64 (by simp), by rw [stA_eq]; exact k y hy _ (by simp)⟩

/-- **`debug_remove`** keeps every thread's `SC`, `BOUND_NTFN` and `STATE`. -/
theorem objects.debug_remove.keepF (s : S) (t : U64) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    objects.debug_remove st s t ⦃ s' => Keep3 st T s s' ⦄ := by
  have h0 := h.1.choose_spec.choose_spec
  have hT := h0.tcbs
  have hc : L.mem s (affA t) ∈ Cs := h0.aff t ht
  have hTm := h.2.2.1.2.2.tm
  unfold objects.debug_remove
  step with obj.Tcb.affinity.spec as ⟨cpu, ecpu⟩
  step with obj.node_get.spec as ⟨hd, ehd⟩
  step with obj.Tcb.debug_next.val as ⟨nx, enx⟩
  step with obj.Tcb.debug_prev.val as ⟨pv, epv⟩
  have hcpu : cpu ∈ Cs := by rw [ecpu]; exact hc
  have tnx : Tz T nx := by rw [enx]; exact hTm.dn t ht
  have tpv : Tz T pv := by rw [epv]; exact hTm.dp t ht
  have dbg : ∀ {s1 : S} {x : U64} (v : U64), x ∈ T → (K : U64) → (K.val = 3576 ∨ K.val = 3584) →
      Keep3 st T s s1 → Keep3 st T s (L.wr s1 (core.num.U64.wrapping_add x K) v) := fun v hx K hK k =>
    k.trans (keep3_field hT hx (by omega) (by omega) (by omega) (by omega) (by omega))
  have k0 : Keep3 st T s s := fun _ _ => ⟨rfl, rfl, rfl⟩
  refine WP.spec_bind (Pₘ := fun s1 => Keep3 st T s s1 ∧ L.ksb s1 = L.ksb s) ?_ ?_
  · split
    · exact WP.spec_mono (obj.node_set.spec s cpu _ nx) fun s1 e => by
        subst e
        exact ⟨keep3_node hT (h0.nodes cpu hcpu) (by simp [layout.node.DEBUG_TCBS])
          (by simp [layout.node.DEBUG_TCBS]), L.ksb_wr _ _ _⟩
    · split
      · rename_i _ hp
        have hpT : pv ∈ T := tpv.ne0 (by simpa using hp)
        exact WP.spec_mono (obj.Tcb.set_debug_next.wr s pv nx) fun s1 e => by
          subst e; exact ⟨dbg nx hpT 3576#u64 (by simp) k0, L.ksb_wr _ _ _⟩
      · exact (WP.spec_ok _).2 ⟨k0, rfl⟩
  intro s1 ⟨k1, b1⟩
  refine WP.spec_bind (Pₘ := fun s2 => Keep3 st T s s2) ?_ ?_
  · split
    · rename_i hn
      have hnT : nx ∈ T := tnx.ne0 (by simpa using hn)
      exact WP.spec_mono (obj.Tcb.set_debug_prev.wr s1 nx pv) fun s2 e => by
        subst e; exact dbg pv hnT 3584#u64 (by simp) k1
    · exact (WP.spec_ok _).2 k1
  intro s2 k2
  refine WP.spec_bind (obj.Tcb.set_debug_prev.wr s2 t 0#u64) fun s3 e3 => ?_
  subst e3
  refine WP.spec_mono (obj.Tcb.set_debug_next.wr _ t 0#u64) fun s4 e4 => ?_
  subst e4
  exact dbg 0#u64 ht 3576#u64 (by simp) (dbg 0#u64 ht 3584#u64 (by simp) k2)

end

end Fl4Proofs.P1
