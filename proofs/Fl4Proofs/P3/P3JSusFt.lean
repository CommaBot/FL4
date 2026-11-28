/-
P3 (p3J gen 41): **`suspend` in `KWN ∅ False`** (P1 QueueFinal's `sched.suspend.kw` walk mirrored at `Kp = ∅`,
`Nd = False`, `Es = EH H`, as gen 37's P3JNtfnFt mirrored the notification finalisation). P2-level, namespace
`Fl4Proofs.P1`, FL4 only.

FL4 `sched.rs` `suspend` (`vcpu::cancel_run` — a no-op on x86_64, P1 SyscallGen's `suspend_eq_old` — then
`cancel_ipc`, the fault-IP copy, `dequeue`, `release_remove`, `cancel_yield_to`, `set_thread_state Inactive`). P1's
`sched.suspend.kw` gives a `Foot` (`KW`), which allows other cores' node words 8 / 32 that `Mc.ProjW` excludes. Each
step here is a `FootN ∅ False` step: `cancel_ipc` by P3JRecvFtN's `ipc.cancel_ipc.kwN0`, the fault-IP word (TCB
offset 392) by P2's `footN_field`, the queue removals by P2's `sched.dequeue.kwN` / `sched.release_remove.kwN`, the
yield-from word of the SC by `footN0_sgw`, the yield-to field (offset 3472) by `footN_field`, the state by
`set_thread_state.kwNP`.

* **`sched.suspend.kwN0`** (from `BlkOK`, as P1's `sched.suspend.blk`).

`suspend` is shared by the Thread labels Suspend / Read- / CopyRegisters (bucket 2 of the architect's TCB plan)
and by a final thread cap's finalisation (`fin_thread`, the deletion of bucket 3).

`AcK` is vacuous at `Kp = ∅`. No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JThPrio
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 41) **`suspend` in `KWN ∅ False`** (P1 `sched.suspend.kw`; module docstring). -/
theorem sched.suspend.kwN0 {A : Type} {ar : machine.Arch A} (s : S) (a : A) (t : obj.Tcb)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    sched.suspend st ar s a t ⦃ s' _ => FootN st ∅ False T Cs Sg Scs Z (EH H) s s' ⦄ := by
  obtain ⟨⟨Q, R, h⟩, hB, hX, -, hSg⟩ := hb
  have hsub := hSg.sub
  have hT := h.tcbs
  have hta := hT t ht
  obtain ⟨hO, hR, hE⟩ := hX
  have hreply : L.mem s (stA t) = sched.TS_BLOCKED_ON_REPLY → ReplyT st Rp Scs s t := fun hs => by
    obtain ⟨h1, h2⟩ := hR.reply t ht hs
    exact ⟨h1, h2, hR.next _ h1, hR.prev _ h1⟩
  rw [Fl4Proofs.P1.suspend_eq_old]; unfold sched.suspend_old
  refine WP.spec_bind (WP.spec_and (ipc.cancel_ipc.all s a t Q R h ht hB ⟨hO, hR, hE⟩ hsub)
    (ipc.cancel_ipc.kwN0 s a t h ht ⟨hO, hR, hE⟩ hsub hreply (fun h1 h2 => (hR.recv t ht h1 h2).1))) ?_
  rintro ⟨s1, a1⟩ ⟨⟨h1, -, -, -, -, -, k1, -⟩, fw1⟩
  try simp only [WP.uncurry'_pair]
  have y1 : L.mem s1 (yieldA t) = L.mem s (yieldA t) :=
    k1.fld t ht _ (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)
  step with obj.Tcb.state.spec as ⟨i, i_post⟩
  refine WP.spec_bind (Pₘ := fun s2 => SchedQueuesInv st T Cs Ω H s2 Q R ∧
      L.mem s2 (yieldA t) = L.mem s1 (yieldA t) ∧ FootN st ∅ False T Cs Sg Scs Z (EH H) s s2) ?_ ?_
  · split
    · step with obj.Tcb.reg.spec as ⟨ip⟩
      refine WP.spec_mono (obj.Tcb.set_reg.fault_ip s1 t ip hta) fun s2 e => ?_
      subst e
      obtain ⟨h2, f2, -⟩ := field_wr_keep (K := 392#u64) (v := ip) h1 ht (by simp) (by simp) (by simp)
      exact ⟨h2, f2 _ (by simp) (by simp) (by simp),
        fw1.trans (footN_field (K := 392#u64) hT h1.nodes h1.cur ht (by simp) (by simp) (by simp) (by simp))⟩
    · exact (WP.spec_ok _).2 ⟨h1, rfl, fw1⟩
  rintro s2 ⟨h2, y2, fw2⟩
  have hc2 := h2.aff t ht
  have hp2 := h2.prio t ht
  have hW2 : ∀ w ∈ Q (L.mem s2 (affA t)) (L.mem s2 (prioA t)), w ∈ T := fun w hw => h2.memT hc2 hp2 hw
  refine WP.spec_bind (WP.spec_and (sched.dequeue.inv s2 t Q R h2 ht)
    (WP.spec_and (sched.dequeue.foot s2 t _ hT ht hp2 (h2.nodes _ hc2) (h2.nodes _ h2.cur)
      ((h2.ready _ hc2).1.rel _ hp2) (h2.queued t ht).1)
      (sched.dequeue.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s2 t h2 ht
        (Set.notMem_empty t)))) ?_
  rintro s3 ⟨h3, ⟨hw3, -⟩, fw3⟩
  have y3 : L.mem s3 (yieldA t) = L.mem s2 (yieldA t) :=
    field_qfoot hT hW2 (h2.nodes _ hc2) (h2.nodes _ h2.cur) ht hw3 ht (K := 3472#u64) (by simp) (by simp) (by simp)
      (fun _ => by simp)
  have hc3 := h3.aff t ht
  have hW3 : ∀ w ∈ R (L.mem s3 (affA t)), w ∈ T := fun w hw => h3.memTR hc3 hw
  refine WP.spec_bind (WP.spec_and (sched.release_remove.foot s3 t _ hT ht (h3.nodes _ hc3) (h3.nodes _ h3.cur)
      (h3.release _ hc3) (h3.released t ht).1)
    (sched.release_remove.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 t h3 ht
      (Set.notMem_empty t))) ?_
  rintro s4 ⟨⟨hw4, -⟩, fw4⟩
  have y4 : L.mem s4 (yieldA t) = L.mem s (yieldA t) :=
    (field_qfoot hT hW3 (h3.nodes _ hc3) (h3.nodes _ h3.cur) ht hw4 ht (K := 3472#u64) (by simp) (by simp) (by simp)
      (fun _ => by simp)).trans (y3.trans (y2.trans y1))
  have f04 := fw2.trans (fw3.trans fw4)
  have NP4 : ∀ c ∈ Cs, NodePlaced st T s4 c := fun c hc => (h.nodes c hc).ksb f04.1
  have hc4 : L.cpu s4 ∈ Cs := by rw [f04.2.1]; exact h.cur
  refine WP.spec_bind (Pₘ := fun s5 => FootN st ∅ False T Cs Sg Scs Z (EH H) s s5) ?_ ?_
  · unfold schedcontext.cancel_yield_to
    step with obj.Tcb.is_null.spec as ⟨b, b_post⟩
    split
    · exact (WP.spec_ok _).2 f04
    step with obj.Tcb.yield_to.spec as ⟨yt, yt_post⟩
    split
    · rename_i _ hy
      have hyS : yt ∈ Scs := by
        rw [yt_post, y4]; exact hE.yt.2.1 t ht (by rw [← y4, ← yt_post]; simpa using hy)
      step with obj.Sc.set_yield_from.spec as ⟨s5, s5_post⟩
      subst s5_post
      have f5 : FootN st ∅ False T Cs Sg Scs Z (EH H) s4 (L.wr s4 (scYieldFromA yt) 0#u64) :=
        footN0_sgw h hsub f04.1 f04.2.1 (h.omega _ (hsub _ (hO.syW yt hyS))).1 (hO.syW yt hyS)
      refine WP.spec_mono (obj.Tcb.set_yield_to.spec _ t 0#u64) fun s6 e => ?_
      subst e
      have NP5 : ∀ c ∈ Cs, NodePlaced st T (L.wr s4 (scYieldFromA yt) 0#u64) c :=
        fun c hc => (NP4 c hc).ksb (L.ksb_wr _ _ _)
      exact (f04.trans f5).trans (by
        rw [show yieldA t = core.num.U64.wrapping_add t 3472#u64 from rfl]
        exact footN_field hT NP5 (by rw [L.cpu_wr]; exact hc4) ht (by simp) (by simp) (by simp) (by simp))
    · exact (WP.spec_ok _).2 f04
  intro s5 f5
  refine WP.spec_bind (sched.set_thread_state.kwNP (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
    (Es := EH H) s5 t _ hT (fun c hc => (h.nodes c hc).ksb f5.1) (by rw [f5.2.1]; exact h.cur) ht
    (Set.notMem_empty t)) fun s6 f6 => ?_
  exact (WP.spec_ok _).2 (f5.trans f6)

end

end Fl4Proofs.P1
