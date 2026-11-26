-- AArch64 port of Fl4Proofs.P1.QueueDebug (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: EntryHyps' `debug` discharged: the debug syscalls (`debug_syscall`) of
the current thread keep `EntryInv`.  They write a register of the current
thread (`CapIdentify`, `GetThreadAffinity`) or the name of the thread the
invoked cap names (`NameThread`); that thread is a TCB (`DbgOK`, a P3
placement fact like `recvOK`'s).
-/
import Fl4ProofsA64.P1.QueueFpu
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- A write of a TCB field other than `SC` from offset 192 keeps
`EntryInv` when it keeps `BlkOK` and the scheduler's current/action/idle words. -/
theorem EntryInv.wr_field {s : S} {y K v : U64} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y ∈ T)
    (hK' : K.val < 4096) (hK8 : K.val % 8 = 0) (hne : K.val ≠ 3464) (hne2 : K.val ≠ 3368) (hne3 : K.val ≠ 3328)
    (hb : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add y K) v))
    (hn : ANI st s (L.wr s (core.num.U64.wrapping_add y K) v)) :
    EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac (L.wr s (core.num.U64.wrapping_add y K) v) := by
  have h0 := h.1.choose_spec.choose_spec
  have w : WritesIn st s (L.wr s (core.num.U64.wrapping_add y K) v) (CSW T Ω) :=
    (writesIn_wr (field_aligned (h0.tcbs y hy) hK' hK8)).mono fun b e =>
      Or.inr ⟨y, hy, K, hK', hK8, hne, hne2, hne3, e⟩
  obtain ⟨ecs, esc⟩ := cs_of_writes h0 w (fun b hb => hb)
  exact EntryInv.of_step h hb ecs hn.2.2 (Or.inl hn.1) esc

/-- A register write of a TCB. -/
theorem EntryInv.set_reg {s : S} {t r v : U64} (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ht : t ∈ T)
    (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  WP.spec_mono (obj.Tcb.set_reg.wrK s t r v (h.1.choose_spec.choose_spec.tcbs t ht) hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    obtain ⟨hb, -, hn⟩ := regW_all (K := K) (v := v) (EntryInv.bxi h).blk ht (by omega) (by omega) (by omega)
    exact EntryInv.wr_field h ht (by omega) (by omega) (by omega) (by omega) (by omega) hb hn

theorem syscall.thread_of.some (c : capability.Cap) :
    syscall.thread_of c ⦃ o => ∀ x, o = some x → c = .Thread x ⦄ := by
  cases c <;> simp [syscall.thread_of]

/-- `name_thread`: the 8 name words of the TCB `x`. -/
theorem syscall.name_thread_loop.entry (s : S) (x src w : U64) (dn : Bool)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hx : x ∈ T) :
    syscall.name_thread_loop st s x src w dn ⦃ s' => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold syscall.name_thread_loop
  apply loop.spec_decr_nat (measure := fun y => 8 - y.2.1.val) (inv := fun y => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac y.1)
  · rintro ⟨s1, w1, d1⟩ h1
    simp only at h1
    dsimp only
    unfold syscall.name_thread_loop.body
    split
    · rename_i hw
      have hw' : w1.val < 8 := by simpa using hw
      refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> step*) fun v _ => ?_
      refine WP.spec_bind (Pₘ := fun _ => True) (by
        split
        · exact (WP.spec_ok _).2 trivial
        · step*
          all_goals first | exact (WP.spec_ok _).2 trivial | (split <;> step*)) ?_
      rintro ⟨d2, v1⟩ -
      try simp only [WP.uncurry'_pair]
      refine WP.spec_bind (Pₘ := fun _ => True) (by split <;> exact (WP.spec_ok _).2 trivial) fun v2 _ => ?_
      unfold obj.Tcb.name_addr layout.tcb.NAME layout.tcb.F
      step as ⟨nm, hnm⟩
      step as ⟨i1, hi1⟩
      simp only [lift, bind_ok]
      step with LawfulStore.write_spec as ⟨s2, e2⟩
      step as ⟨w2, hw2⟩
      subst e2
      have hT := h1.1.choose_spec.choose_spec.tcbs
      let K : U64 := ⟨BitVec.ofNat 64 (3600 + 8 * w1.val)⟩
      have hK : K.val = 3600 + 8 * w1.val := by
        show (BitVec.ofNat 64 (3600 + 8 * w1.val)).toNat = _
        simp; omega
      have ea : core.num.U64.wrapping_add (core.num.U64.wrapping_add x nm) i1 = core.num.U64.wrapping_add x K := by
        apply UScalar.eq_of_val_eq
        rw [field_val (hT x hx) (by omega)]
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at hnm hi1 ⊢
        have := (hT x hx).fits
        omega
      rw [ea]
      obtain ⟨hb, -, hn⟩ := plainW_all (K := K) (v := v2) (EntryInv.bxi h1).blk hx (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      exact ⟨EntryInv.wr_field h1 hx (by omega) (by omega) (by omega) (by omega) (by omega) hb hn, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- **EntryHyps' `debug`: the debug syscalls keep `EntryInv`.**  `hdbg`: a
thread cap the current thread invokes names a TCB. -/
theorem syscall.debug_syscall.entry {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (n : I64) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hdbg : syscall.invoked_cap st s (L.curW s) ⦃ c => ∀ x, c = .Thread x → x ∈ T ⦄) :
    syscall.debug_syscall st ar s a (L.curW s) n ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hcT : L.curW s ∈ T := h.1.choose_spec.choose_spec.curT
  have hr : layout.reg.CAP.val < 384 := by simp [layout.reg.CAP]
  have K0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ :=
    (WP.spec_ok _).2 ⟨Ac, h⟩
  unfold syscall.debug_syscall
  split
  · exact WP.spec_bind (hA.halt a) fun _ _ => (WP.spec_ok _).2 ⟨Ac, h⟩
  split
  · exact (WP.spec_ok _).2 ⟨Ac, h⟩
  split
  · refine WP.spec_bind (P0.syscall.invoked_cap.p0 st s _ hS) fun c _ => ?_
    refine WP.spec_bind (P0.syscall.cap_type_code.p0 c) fun i _ => ?_
    exact WP.spec_bind (EntryInv.set_reg (v := i) h hcT hr) fun s1 h1 => (WP.spec_ok _).2 ⟨Ac, h1⟩
  split
  · unfold syscall.debug_name_thread
    refine WP.spec_bind (Pₘ := fun r : S × A => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.1) ?_
      fun r h1 => by obtain ⟨s1, a1⟩ := r; exact (WP.spec_ok _).2 ⟨Ac, h1⟩
    refine WP.spec_bind hdbg fun c hc => ?_
    refine WP.spec_bind (syscall.thread_of.some c) fun o ho => ?_
    rcases o with _ | x
    · exact WP.spec_bind (hA.halt a) fun _ _ => (WP.spec_ok _).2 h
    have hx := hc x (ho x rfl)
    refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s true _ hS) fun buf _ => ?_
    split
    · exact WP.spec_bind (hA.halt a) fun _ _ => (WP.spec_ok _).2 h
    · simp only [lift, bind_ok]
      exact WP.spec_bind (syscall.name_thread_loop.entry s x _ 0#u64 false h hx) fun s1 h1 =>
        (WP.spec_ok _).2 h1
  have aff : (do
      let c ← syscall.invoked_cap st s (L.curW s)
      let o ← syscall.thread_of c
      match o with
      | none => do
        let a1 ← ar.halt a
        ok (true, s, a1)
      | some target => do
        let aff ← obj.Tcb.affinity st target s
        let s1 ← obj.Tcb.set_reg st (L.curW s) s layout.reg.CAP aff
        ok (true, s1, a)) ⦃ _ s' _ => ∃ Ac', EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac' s' ⦄ := by
    refine WP.spec_bind (P0.syscall.invoked_cap.p0 st s _ hS) fun c _ => ?_
    refine WP.spec_bind (syscall.thread_of.some c) fun o _ => ?_
    rcases o with _ | x
    · exact WP.spec_bind (hA.halt a) fun _ _ => (WP.spec_ok _).2 ⟨Ac, h⟩
    · step with obj.Tcb.affinity.spec as ⟨af, _⟩
      exact WP.spec_bind (EntryInv.set_reg (v := af) h hcT hr) fun s1 h1 => (WP.spec_ok _).2 ⟨Ac, h1⟩
  repeat (first | exact aff | exact (WP.spec_ok _).2 ⟨Ac, h⟩ | split)

end

end Fl4ProofsA64.P1
