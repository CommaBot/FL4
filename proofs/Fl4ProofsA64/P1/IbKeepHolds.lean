-- AArch64 port of Fl4Proofs.P1.IbKeepHolds (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1 (KENTRY-PLAN a6f, gap 1 of int6): **`ibKeep_holds`** discharges the core's
deferred `IbKeep st ar` (QueueSignal): `timer::fire`'s loop steps keep the
three words `lookup_ipc_buffer` reads of every TCB (`IbFr`).

* `timer.remove`: its `TF` frame keeps every TCB word below the timer fields
  (`TKeep`; the `IPC_BUFFER` word 3512 and the buffer slot 64/72 among them).
* the current node's `REPROGRAM` write: a node word, no TCB word.
* `send_signal`: `notification.send_signal.tinvFK` (QueueFootS) gives its
  footprint as `FootDUB` (`KWB`: `KW` without the `IPC_BUFFER` word, the debug
  lists, and the user words `U`); `BufKeep.of_blkDBU` (QueueFinal) turns that
  into the buffer words kept, `UsrW` putting `U` outside the TCBs.

a64 (AArch64 rework): `ibKeep_holds` is **not** derived in its stated form. `IbKeep`'s `send_signal` clause has
no [J] `RunVcpuInv`, and AArch64's `send_signal` needs it: the woken thread's SC donation runs `migrate_tcb`,
which writes the thread's VCPU state unless its `RUN_VCPU` is 0, and without `RunVcpuInv` nothing places that
write outside the TCBs' buffer words. So `notification.send_signal.ibFr` takes [J] `hRV`, and the `IbKeep`-taking
lemmas get `IbKeep`-free twins proved here with the three `ibFr` lemmas in place of `IbKeep` (the fire loop
carries `RunVcpuInv` anyway): `timer.fire_loop.tinv_ib`, `timer.fire.tinv_ib`, `sched.schedule.tinv_ib`,
`sched.schedule.entry_ib` (from RunVcpuKeep's `_rv` forms) and `timer.fire_loop.tinvF_ib`, `timer.fire.tinvF_ib`,
`sched.schedule.sfoot_ib`, `timer.fire.kw_ib`, `sched.schedule.kw_ib` (from QueueFootS). Their texts are those
lemmas' with `IbKeep`'s three clauses replaced by `timer.remove.ibFr`, `send_signal.ibFr` and `reprogram.ibFr`.
So **[J] `IbKeep` is discharged** for every AArch64 `timer::fire` / `schedule` path through these twins.

Named premises: [J] `RunVcpuInv` (`hRV`, see `RunVcpu`), no other.
-/
import Fl4ProofsA64.P1.QueueFootS
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- `BufKeep` (QueueFoot) is `IbFr` (QueueSignal) with the key-space base. -/
theorem IbFr.of_bufKeep {T : Set U64} {s s' : S} (hk : L.ksb s' = L.ksb s) (k : BufKeep st T s s') :
    IbFr (L := L) T s s' :=
  ⟨hk, fun y hy => k y hy⟩

/-- `timer.remove` keeps the buffer-lookup words. -/
theorem timer.remove.ibFr {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    (s : S) (t : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T) :
    timer.remove st s t ⦃ s' => IbFr (L := L) T s s' ⦄ := by
  refine WP.spec_mono (timer.remove.tf (s0 := s) s t (TF.start h) ht) fun s' hf => ?_
  have tk := hf.2.2.2.1
  refine ⟨hf.2.1.1, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact tk y hy 3512#u64 (by simp) (by simp) (Or.inl (by simp))
  · rw [sbWordA_eq]; exact tk y hy 64#u64 (by simp) (by simp) (Or.inl (by simp))
  · rw [sbWordA8_eq]; exact tk y hy 72#u64 (by simp) (by simp) (Or.inl (by simp))

/-- The current node's `REPROGRAM` write keeps the buffer-lookup words. -/
theorem reprogram.ibFr {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
    (s : S) (v : U64) (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    IbFr (L := L) T s (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) := by
  obtain ⟨⟨Q, R, h0⟩, -⟩ := h
  have hT := h0.tcbs
  have hN := h0.nodes _ h0.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) := nodeAt_aligned hN (by rw [rp]; omega) (by rw [rp])
  have fld : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 →
      L.mem (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) v) (core.num.U64.wrapping_add y K) =
        L.mem s (core.num.U64.wrapping_add y K) := fun y hy K hK hK8 =>
    L.mem_wr_ne aR (field_aligned (hT y hy) hK hK8)
      (fun e => node_ne_field hN (by rw [rp]; omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e))
  refine ⟨L.ksb_wr _ _ _, fun y hy => ⟨?_, ?_, ?_⟩⟩
  · exact fld y hy 3512#u64 (by simp) (by simp)
  · rw [sbWordA_eq]; exact fld y hy 64#u64 (by simp) (by simp)
  · rw [sbWordA8_eq]; exact fld y hy 72#u64 (by simp) (by simp)

/-- `send_signal` keeps the buffer-lookup words (from its `FootDUB` footprint). -/
theorem notification.send_signal.ibFr {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (n bd : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hn : n ∈ Nt) (hH : H n = some .ntfn)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv`
    notification.send_signal st ar s a n bd ⦃ s' _ => IbFr (L := L) T s s' ⦄ := by
  refine WP.spec_mono (notification.send_signal.tinvFK hA s a n bd h hn hH hBA.1 hBA.2 hRV) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  have f := hr.2.1
  exact IbFr.of_bufKeep f.1 (BufKeep.of_blkDBU (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (fun b hb => (hBA.1 b hb).out)
    (WritesIn.mono f fun _ hb => by
      rcases hb with (hb | hb) | hb
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr hb)))

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). `timer.fire_loop.tinv` with [J] `RvKeep` discharged (`timer.remove.rvi`, `send_signal.rvi`; the loop's
notifications are typed by `hNt`). -/
theorem timer.fire_loop.tinv_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hRV : RunVcpuInv st T s) :
    timer.fire_loop st ar s a now i ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧
      RunVcpuInv st T s' ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ IbFr (L := L) T s x.1 ∧ RunVcpuInv st T x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, f1, r1⟩
    simp only at h1 f1 r1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, f1, r1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hI1, f1, r1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (WP.spec_and (timer.remove.tinv s1 t hI1 htT) (timer.remove.ibFr s1 t hI1 htT))
        (timer.remove.rvi s1 t hI1 r1 htT)) fun s2 hh2 => ?_
      obtain ⟨⟨h2, f2⟩, r2⟩ := hh2
      have f12 := f1.trans f2
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ IbFr (L := L) T s r.1 ∧
          RunVcpuInv st T r.1)
        ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinv hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2 r2)
            (notification.send_signal.ibFr hA s2 a1 n bd h2 hn (hNt n hn) hb2 r2)) (notification.send_signal.rvi hA s2 a1 n bd h2 hn (hNt n hn) r2))
            fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact ⟨hr.1.1, f12.trans hr.1.2, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, f12, r2⟩
      rintro ⟨s3, a3⟩ ⟨h3, f3, r3⟩
      simp only at h3 f3 r3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      exact ⟨reprogram.tinv h3, f3.trans (reprogram.ibFr s3 1#u64 h3), reprogram.rvi h3 r3, by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, f1, r1⟩
  · exact ⟨h, IbFr.refl s, hRV⟩

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). `timer.fire.tinv` without [J] `RvKeep`. -/
theorem timer.fire.tinv_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hRV : RunVcpuInv st T s) :
    timer.fire st ar s a ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧ IbFr (L := L) T s s' ∧
      RunVcpuInv st T s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.tinv_ib hA hNt s a now 0#u64 h hBA hRV

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). `sched.schedule.tinv` without [J] `RvKeep`. -/
theorem sched.schedule.tinv_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :
    sched.schedule st ar s a ⦃ s' _ => (∃ Q' R', SchedQueuesInv st T Cs Ω H s' Q' R') ∧ BoundInv st T Ac s' ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧ SCsOK st T Ω Sg Scs Z Ac s' ∧ TimerOK st T Cs s' ∧ L.cscW s' ∈ Ac ∧
      L.actionW s' = 0#u64 ∧ L.cscW s' = L.mem s' (scA (L.curW s')) ⦄ := by
  refine WP.spec_mono (sched.schedule.inv hA s a Q R h hB hS hX
    (WP.spec_mono (timer.fire.tinv_ib hA hNt s a (BlkOK.tinv ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩) hBA hRV)
      fun r hr => by
      obtain ⟨s', a'⟩ := r
      simp only [WP.uncurry'_pair] at hr ⊢
      exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2.2.1, hr.1.2.2.1⟩)) fun r hr => ?_
  obtain ⟨s', a'⟩ := r
  simp only [WP.uncurry'_pair] at hr ⊢
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.1.2.2.tm, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2⟩

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). `sched.schedule.entry` without [J] `RvKeep`. -/
theorem sched.schedule.entry_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hS : SCsOK st T Ω Sg Scs Z Ac s)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hSg : SgOK st Ω Sg s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :
    sched.schedule st ar s a ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (sched.schedule.tinv_ib hA hNt s a Q R h hB hS hX hSg hBA hRV) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    obtain ⟨⟨Q', R', h'⟩, hB', hX', hS', hT', hA', ha', hc'⟩ := hr
    refine ⟨⟨Q', R', h'⟩, hB', hX', hS', hT', hA', fun e => ?_, fun _ => hc'⟩
    rw [ha'] at e
    have e' := e.symm
    unfold LawfulStore.curW at e'
    exact (h'.tcbs _ h'.curT).ne0 (by rw [e']; rfl)

theorem timer.fire_loop.tinvF_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A) (now i : U64)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv`, carried through the loop (`send_signal.rvi`)
    timer.fire_loop st ar s a now i ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootDU st T Cs Sg Scs Z (EH H) U s s' ⦄ := by
  unfold timer.fire_loop
  refine WP.spec_mono (P₀ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
    FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ RunVcpuInv st T r.1) ?_
    fun r hr => by obtain ⟨s', a'⟩ := r; exact ⟨hr.1, hr.2.1⟩
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac x.1 ∧ FootDU st T Cs Sg Scs Z (EH H) U s x.1 ∧
      IbFr (L := L) T s x.1 ∧ RunVcpuInv st T x.1)
  · rintro ⟨s1, a1, i1⟩ ⟨h1, F1, f1, r1⟩
    simp only at h1 F1 f1 r1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with obj.node_get.spec as ⟨t, et⟩
      step with obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 ⟨h1, F1, f1, r1⟩
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      have hI1 := h1
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := h1
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ T := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 ⟨hI1, F1, f1, r1⟩
      step with obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      refine WP.spec_bind (WP.spec_and (WP.spec_and (timer.remove.tf (s0 := s1) s1 t (TF.start hI1) htT)
        (timer.remove.ibFr s1 t hI1 htT)) (timer.remove.rvi s1 t hI1 r1 htT)) ?_
      rintro s2 ⟨⟨⟨h2, f2, -⟩, g2⟩, r2⟩
      have F2 : FootDU st T Cs Sg Scs Z (EH H) U s s2 := F1.trans (FootD.u (Foot.d (f2.mono (Set.empty_subset _))))
      have f12 := f1.trans g2
      step with obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧
          FootDU st T Cs Sg Scs Z (EH H) U s r.1 ∧ IbFr (L := L) T s r.1 ∧ RunVcpuInv st T r.1) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (boundA t) ≠ 0#u64 := by rw [← en]; exact bne_ne hn0
          have hn : n ∈ Nt := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hb2 := hBA.of_fr f12
          exact WP.spec_mono (WP.spec_and (WP.spec_and
            (notification.send_signal.tinvF hA s2 a1 n bd h2 hn (hNt n hn) hb2.1 hb2.2 r2)
            (notification.send_signal.ibFr hA s2 a1 n bd h2 hn (hNt n hn) hb2 r2)) (notification.send_signal.rvi hA s2 a1 n bd h2 hn (hNt n hn) r2))
            fun r hr => by
            obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1.1, F2.trans hr.1.1.2.1, f12.trans hr.1.2, hr.2⟩
        · exact (WP.spec_ok _).2 ⟨h2, F2, f12, r2⟩
      rintro ⟨s3, a3⟩ ⟨h3, F3, f3, r3⟩
      simp only at h3 F3 f3 r3
      try simp only [WP.uncurry'_pair]
      step with LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have hc3 := h3.1.choose_spec.choose_spec.cur
      exact ⟨reprogram.tinv h3, F3.trans (FootD.u (Foot.d (foot_node (h3.1.choose_spec.choose_spec.nodes _ hc3) hc3
        (by rw [rp]; omega) (by rw [rp]) (by rw [rp]; omega)))), f3.trans (reprogram.ibFr s3 1#u64 h3), reprogram.rvi h3 r3, by omega⟩
    · exact (WP.spec_ok _).2 ⟨h1, F1, f1, r1⟩
  · exact ⟨h, FootD.u (Foot.d (Foot.refl _)), IbFr.refl s, hRV⟩

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). seL4 MCS `fireTimers` (l4h): `timer::fire` keeps `TInv`. -/
theorem timer.fire.tinvF_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv`
    timer.fire st ar s a ⦃ s' _ => TInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      FootDU st T Cs Sg Scs Z (EH H) U s s' ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (obj.node_get.spec s c _) fun now _ => ?_
  exact timer.fire_loop.tinvF_ib hA hNt s a now 0#u64 h hBA hRV

theorem sched.schedule.sfoot_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv`
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ SFoot st T Cs Sg Scs Z H rf.1 s' ⦄ := by
  unfold sched.schedule sched.awaken
  -- `awaken`
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ ∃ rf : S × A,
      timer.fire st ar s a = ok rf ∧ FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ SFoot st T Cs Sg Scs Z H rf.1 r.1) ?_ ?_
  · refine WP.spec_bind (spec_eq' (timer.fire.tinvF_ib hA hNt s a h.tinv hBA hRV)) ?_
    rintro ⟨s1, a1⟩ ⟨hf1, ⟨⟨Q1, R1, h1⟩, hB1, hX1, hS1, hSg1⟩, F1⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (WP.spec_and (sched.awaken_loop.sch s1 _ Q1 R1 h1 hB1 hS1.sg)
      (sched.awaken_loop.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 _ Q1 R1 h1 hB1 hS1.sg)) ?_
    rintro s2 ⟨⟨P2, -⟩, F2⟩
    exact (WP.spec_ok _).2 ⟨P2.good hS1 hX1, (s1, a1), hf1, F1, F2.sfoot⟩
  rintro ⟨s1, a1⟩ ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, rf, hrf, Fd, F1⟩
  -- `check_domain_time` does nothing with one domain
  unfold sched.check_domain_time sched.is_cur_domain_expired
  simp only [layout.NUM_DOMAINS, fl4_abi.config.NUM_DOMAINS]
  have hnd : ¬ ((1#u64) > (1#u64)) := by simp
  simp only [hnd, ↓reduceIte, bind_ok, Bool.false_eq_true]
  step with sched.action.spec as ⟨act, act_post⟩
  -- the action
  refine WP.spec_bind (Pₘ := fun r => Good st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ L.mem r.1 (scA (L.curW r.1)) ≠ 0#u64 ∧
      L.mem r.1 (scA (L.curW r.1)) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 r.1) ?_ ?_
  · split
    · rename_i hnr
      step with sched.cur_thread.spec as ⟨ct, ct_post⟩
      have hctT : ct ∈ T := by rw [ct_post]; exact h1.curT
      step with sched.is_schedulable.spec' as ⟨wr, wr_post⟩
      refine WP.spec_bind (Pₘ := fun s4 => Post st T Cs Ω H Sg Ac s1 s4 ∧ L.actionW s4 = L.actionW s1 ∧
          Foot st T Cs Sg Scs Z (EH H) s1 s4) ?_ ?_
      · split
        · exact WP.spec_mono (WP.spec_and (sched.enqueue.sch s1 ct Q1 R1 h1 hB1 hS1.sg hctT (fun _ => (wr_post ‹_›).2.2.1)
            (fun _ => (wr_post ‹_›).1) (fun _ => (wr_post ‹_›).2.1)
            (fun _ => (hS1.act _ (hX1.2.2.bound _ hctT (wr_post ‹_›).2.1).1).2 (wr_post ‹_›).2.2.2))
            (sched.enqueue.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s1 ct h1 hctT))
            fun s4 h4 => ⟨h4.1.1, h4.1.2.1, h4.2⟩
        · exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, Fr.refl _ _⟩, rfl, Foot.refl _⟩
      rintro s4 ⟨⟨⟨Q4, R4, h4⟩, hB4, f4⟩, ea4, F4⟩
      have hS4 := hS1.fr f4
      have hX4 := hX1.fr f4
      have hact4 : L.actionW s4 = act := ea4.trans act_post.symm
      split
      · exact WP.spec_mono (WP.spec_and (sched.schedule_choose_new_thread.sch hA s4 a1 Q4 R4 h4 hB4 hS4 hX4)
          (sched.schedule_choose_new_thread.sfoot (Scs := Scs) (Z := Z) hA s4 a1 Q4 R4 h4 hB4 hS4.sg)) fun r hr => by
            obtain ⟨s', a'⟩ := r
            simp only [WP.uncurry'_pair] at hr ⊢
            exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfoot.trans hr.2⟩
      rename_i hnc
      have hT : act ∈ T := by
        rcases h4.action with e | e | e
        · exfalso; rw [hact4] at e; rw [e, resume_val] at hnr; simp at hnr
        · exfalso; rw [hact4] at e; rw [e, choose_val] at hnc; simp at hnc
        · rw [hact4] at e; exact e
      have hbd : L.mem s4 (scA act) ≠ 0#u64 := by have := hB4.act (hact4 ▸ hT); rw [hact4] at this; exact this
      have L1 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT true)
        (cand_choose.sfoot (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT true)
      have L3 := WP.spec_and (cand_choose hA s4 a1 act Q4 R4 h4 hB4 hS4 hX4 hact4 hT false)
        (cand_choose.sfoot (Scs := Scs) (Z := Z) hA s4 a1 act Q4 R4 h4 hB4 hS4 hact4 hT false)
      simp only [↓reduceIte, Bool.false_eq_true] at L1 L3
      replace L1 := WP.spec_mono L1 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfoot.trans hr.2⟩
      replace L3 := WP.spec_mono L3 (P₁ := WP.uncurry' fun s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 s')
        fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1, hr.1.2.1, hr.1.2.2, F4.sfoot.trans hr.2⟩
      have L2 : sched.switch_to_thread st ar s4 a1 act ⦃ s' _ => Good st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
          L.mem s' (scA (L.curW s')) ≠ 0#u64 ∧ L.mem s' (scA (L.curW s')) ∈ Ac ∧ SFoot st T Cs Sg Scs Z H s1 s' ⦄ :=
        WP.spec_mono (WP.spec_and (sched.switch_to_thread.sch hA s4 a1 act Q4 R4 h4 hB4 hS4.sg hT hbd
          (by have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this))
          (sched.switch_to_thread.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) hA s4 a1 act h4 hT)) fun r hr => by
          obtain ⟨s', a'⟩ := r
          simp only [WP.uncurry'_pair] at hr ⊢
          exact ⟨hr.1.1.good hS4 hX4, by rw [hr.1.2.1, hr.1.1.fr.sc act hT]; exact hbd, by
            rw [hr.1.2.1, hr.1.1.fr.sc act hT]; have := hB4.actA (hact4 ▸ hT); rwa [hact4] at this,
            (F4.trans hr.2).sfoot⟩
      step with sched.cur_thread.spec as ⟨ct1, _⟩
      step with sched.idle_thread.spec' as ⟨t, _⟩
      step with tcb_eq.spec as ⟨b⟩
      refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun fastfail _ => ?_
      · split
        · simp
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split <;> simp
      split
      · step with sched.cur_domain.spec' as ⟨i⟩
        step with obj.Tcb.prio.spec as ⟨i1, _⟩
        step with sched.is_highest_prio.ok s4 Q4 R4 h4 as ⟨b1⟩
        split
        · split
          · step with obj.Tcb.prio.spec as ⟨i2, _⟩
            split
            · exact L1
            · exact L2
          · exact L2
        · exact L3
      · split
        · step with obj.Tcb.prio.spec as ⟨i, _⟩
          step with obj.Tcb.prio.spec as ⟨i1, _⟩
          split
          · exact L1
          · exact L2
        · exact L2
    · rename_i hr0
      have e0 : L.actionW s1 = 0#u64 := by
        rw [← act_post]; rw [resume_val] at hr0
        apply UScalar.eq_of_val_eq; simpa using hr0
      exact (WP.spec_ok _).2 ⟨⟨⟨Q1, R1, h1⟩, hB1, hS1, hX1⟩, hB1.resume e0, hB1.curA h1.curT e0, SFoot.refl _⟩
  rintro ⟨s3, a2⟩ ⟨⟨⟨Q3, R3, h3⟩, hB3, hS3, hX3⟩, hcb1, hcb2, F3⟩
  have hcb := And.intro hcb1 hcb2
  try simp only [WP.uncurry'_pair]
  -- resume, then switch the SC
  rw [resume_val]
  refine WP.spec_bind (WP.spec_and (sched.set_action.sch s3 0#u64 Q3 R3 h3 hB3 hS3.sg (Or.inl rfl)
    (fun hT => absurd hT (notT_small h3.tcbs (by simp))) (fun hT => absurd hT (notT_small h3.tcbs (by simp)))
    (fun _ => hcb) (fun hT => absurd hT (notT_small h3.tcbs (by simp))))
    (sched.set_action.kw (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 0#u64 (h3.nodes _ h3.cur) h3.cur)) ?_
  rintro s4 ⟨⟨P4, ea4, -, -⟩, F4⟩
  obtain ⟨⟨Q4, R4, h4⟩, hB4, hS4, hX4⟩ := P4.good hS3 hX3
  have hcT := h4.curT
  have hb4 : L.mem s4 (scA (L.curW s4)) ≠ 0#u64 := hB4.resume ea4
  have hO4 := hX4.1
  have hsub4 := hS4.sub
  have hts : L.mem s4 (scA (L.curW s4)) ∈ Scs := (hX4.2.2.bound _ hcT hb4).1
  have hcs : L.cscW s4 ∈ Scs := hX4.2.2.cur
  obtain ⟨hPc, hzc⟩ := hO4.sc _ hcs
  obtain ⟨h8c, h128c, -⟩ := sc_lo hPc hzc
  have hvc := sc_word_val hPc hzc (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hcq : SCq st s4 Ω (L.cscW s4) (Z (L.cscW s4)) := by
    obtain ⟨a1, a2, a3⟩ := maxA_facts hO4 hcs
    exact ⟨(hS4.all _ hcs).1, fun b hb hi => hsub4 _ ((hS4.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩, by unfold Aligned; rw [hvc, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩
  have htin : SCin st s4 Ω (L.mem s4 (scA (L.curW s4))) (Z (L.mem s4 (scA (L.curW s4)))) :=
    (hS4.scin hts (hB4.curA hcT ea4)).mono hsub4
  have hN4 := h4.nodes _ h4.cur
  refine WP.spec_bind (WP.spec_and (sched.switch_sched_context.free hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
    (zc := Z (L.cscW s4)) h4.cur hN4 h4.omega hcq
    (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩))
    (sched.switch_sched_context.fp hA s4 a2 (zt := Z (L.mem s4 (scA (L.curW s4))))
      (zc := Z (L.cscW s4))
      (B := SchedW st T Cs Sg Scs Z H s4) h4.cur hN4 h4.omega
      hcq (fun hne => ⟨htin, hS4.disj _ hcT hb4 hne⟩)
      (Or.inl (kw_node h4.cur (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])))
      (Or.inl (kw_node h4.cur (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])))
      (Or.inl (kw_node h4.cur (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])))
      (fun _ b _ hr => Or.inl (kw_sc hts hr.inSC))
      (fun b _ hr => by
        rcases hr with hr | rfl
        · exact Or.inl (kw_sc hcs hr.inSC)
        · exact Or.inl (kw_sc hcs (show InSC (L.cscW s4) (Z (L.cscW s4))
            (core.num.U64.wrapping_add (L.cscW s4) layout.sc.CONSUMED) from
            ⟨by rw [hvc]; omega, by rw [hvc, hcv]; omega⟩))))) ?_
  rintro ⟨s5, a3⟩ ⟨w5, w5', -, -, -⟩
  simp only [WP.uncurry'_pair] at w5 w5' ⊢
  have h5 := (free_step h4 hB4 w5).1
  step with LawfulStore.cur_cpu_spec as ⟨c, c_post⟩
  step with obj.node_get.spec as ⟨i, _⟩
  refine WP.spec_bind (Pₘ := fun r => SchedQueuesInv st T Cs Ω H r.1 Q4 R4 ∧ SFoot st T Cs Sg Scs Z H s5 r.1) ?_ ?_
  · split
    · have hB5 := (free_step h4 hB4 w5).2
      refine WP.spec_bind (WP.spec_and (sched.set_next_interrupt.free (Ω := Ω) hA s5 a3 h5.cur (h5.nodes _ h5.cur))
        (sched.set_next_interrupt.fp hA s5 a3 (B := SchedW st T Cs Sg Scs Z H s5) (h5.nodes _ h5.cur)
          (Or.inl (kw_node h5.cur (by simp [layout.node.ARMED]) (by simp [layout.node.ARMED]))))) ?_
      rintro ⟨s7, a5⟩ ⟨w7, w7'⟩
      simp only [WP.uncurry'_pair] at w7 w7' ⊢
      have h7 := free_step h5 hB5 w7
      step with obj.node_set.spec as ⟨s8, s8_post⟩
      try simp only [WP.spec_ok]
      have w8 : WritesIn st s5 s8 (L.Free s5 Ω Cs) := by
        rw [s8_post, c_post]
        exact w7.free_trans (free_node_write w7.1 h5.cur (h5.nodes _ h5.cur)
          (by simp [layout.node.REPROGRAM, LowFree]))
      have hN7 : NodePlaced st T s7 (L.cpu s7) := by rw [w7.2.1]; exact (h5.nodes _ h5.cur).ksb w7.1
      have F8 : SFoot st T Cs Sg Scs Z H s7 s8 := by
        rw [s8_post, c_post, ← w7.2.1]
        exact (foot_node (Es := EH H) hN7 (by rw [w7.2.1]; exact h5.cur) (by simp [layout.node.REPROGRAM])
          (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])).sfoot
      exact ⟨(free_step h5 hB5 w8).1, w7'.trans F8 |>.mono fun b hb => Or.elim hb id fun hb => SchedW.ksb w7'.1 hb⟩
    · exact (WP.spec_ok _).2 ⟨h5, SFoot.refl _⟩
  rintro ⟨s6, a4⟩ ⟨h6, F6⟩
  try simp only [WP.uncurry'_pair]
  exact WP.spec_mono (smp.send_pending.fp hA s6 a4 (B := SchedW st T Cs Sg Scs Z H s6) (h6.nodes _ h6.cur)
      (Or.inl (kw_node h6.cur (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])))
      -- a64: the second word of the `IPI_PENDING` pair
      (Or.inl (kw_node h6.cur (by simp [layout.node.IPI_PENDING_HI]) (by simp [layout.node.IPI_PENDING_HI]))))
      fun r w => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at w ⊢
    exact ⟨rf, hrf, Fd, F1.trans (F3.trans ((F4.sfoot.trans w5').trans (F6.trans w)))⟩

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). **The footprint of `timer::fire`** (`KW` with the heap's endpoints and
notifications). -/
theorem timer.fire.kw_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv`
    timer.fire st ar s a ⦃ s' _ => FootDU st T Cs Sg Scs Z (EH H) U s s' ⦄ :=
  WP.spec_mono (timer.fire.tinvF_ib hA hNt s a h.tinv hBA hRV) fun r hr => by
    obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hr ⊢; exact hr.2

/-- a64, no [J] `IbKeep` (the `ibFr` lemmas here). **The footprint of `schedule`**: the timers' (`FootDU`: `KW`, the debug
lists and, int6, the user words of a signalled VMEnter caller's IPC buffer),
then the words of `SchedW`. -/
theorem sched.schedule.kw_ib {U : Set U64} {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s)
    (hRV : RunVcpuInv st T s) :  -- a64: [J] `RunVcpuInv`
    sched.schedule st ar s a ⦃ s' _ => ∃ rf : S × A, timer.fire st ar s a = ok rf ∧
      FootDU st T Cs Sg Scs Z (EH H) U s rf.1 ∧ WritesIn st rf.1 s' (SchedW st T Cs Sg Scs Z H rf.1) ⦄ :=
  sched.schedule.sfoot_ib hA hNt s a h hBA hRV

end

end Fl4ProofsA64.P1
