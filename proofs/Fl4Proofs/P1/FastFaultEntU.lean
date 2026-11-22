/-
# The fault fast path's reads with IPC-buffer words among the kernel words (FL4 #16, m73)

m61–m64's `FaultEnt` asks the receive buffer's words `U` outside the other
kernel words `Ω` (`FaultEnt.hU : b ∈ U → OutsideObjs ∧ b ∉ Ω`), and `Ω` is
the set the P1 invariants (`BXI`) are stated over. At P3's joint relation
`Ω = Heap.omega H` holds every word of every `other` object of `H`, frames
included, so a handler's IPC-buffer words are `Ω` words there (KENTRY-PLAN
m72's OBSTRUCTION). P3's IPC transfer handles the same fact by splitting the
buffer words into `Ω \ Sg` words and user words (`blkX_bufw`).

Here the fault path does not restate `FaultEnt`: the run's reads (m58–m61
`faultReads_of`, `usOff_of`, m63 `finReads_of`, m70 `faultNvm_of`) are
already stated over an arbitrary word set, so they are used at a second word
set `Ω'` instead of `Ω`. `BXI.reΩ` moves `BXI` from `Ω` to any `Ω'` whose
words are `Ω` words or words of a set `V` placed like kernel words (outside
the TCBs and nodes, off the endpoints and notifications), that holds the
frame words `Sg` and the kernel-state block: every invariant of `BXI` reads
`Ω` only through "an `Ω` word is outside the TCBs / nodes / endpoints"
(anti-monotone) or "these words are `Ω` words" (`Sg`, the SCs' words, the
block). P3 takes `Ω' = (Ω \ U) ∪ V`, `U` the IPC-buffer words, `V` the
ASID-table and pool words, so `FaultEnt.hU` holds at `Ω'` (`U ∩ Ω' = ∅`) and
`AsidOff Ω' Sg` from its own VSpace relation.

* `BXI.reΩ` (above);
* `faultEntAt_ofT`: m64's `faultEntAt_of` with `EntryHyps0.tmoOK` /
  `XferHyps.buf` replaced by the facts it read: the current thread not
  blocked, the fault-handler cap typed, `U`'s placement and every TCB's
  receive buffer in `U` (`BufOK`);
* `faultRecv_ofT`: m70's `faultRecv_of` with the cap typing as an argument;
* `fastFault_of`: `FaultOK ∧ FaultNvm` at such a state (`faultOK_of`,
  FastTailFault's `faultNvm_ofR`).
-/
import Fl4Proofs.P1.FastTailFault
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **`BXI` over another word set** (module docstring). -/
theorem BXI.reΩ {T Cs Ω Ω' V : Set U64} {H : Heap} {Sg Rp Scs Nt Ac : Set U64} {Z : U64 → Nat} {s : S}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hsub : ∀ a ∈ Ω', a ∈ Ω ∨ a ∈ V)
    (hV : ∀ a ∈ V, OutsideObjs st T Cs s a ∧
      ∀ e, (H e = some .ep ∨ H e = some .ntfn) → a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val)
    (hSg : ∀ b ∈ Sg, b ∈ Ω')
    (hks : ∀ o : U64, o.val < 13568 → o.val % 8 = 0 → core.num.U64.wrapping_add (L.ksb s) o ∈ Ω') :
    BXI st T Cs Ω' H Sg Rp Scs Nt Z Ac s := by
  obtain ⟨⟨Q, R, hSQ⟩, hB, ⟨hO, hR, hX⟩, hSgK, hS⟩ := h
  obtain ⟨E, EQ, w1, w2, w3, w4, w5, w6⟩ := hSQ.eps
  have hΩ' : ∀ a ∈ Ω', OutsideObjs st T Cs s a := fun a ha =>
    (hsub a ha).elim (hSQ.omega a) fun hv => (hV a hv).1
  have w3' : ∀ e ∈ E, ∀ a ∈ Ω', a.val + 8 ≤ e.val ∨ e.val + 16 ≤ a.val := by
    intro e he a ha
    rcases hsub a ha with h1 | h1
    · exact w3 e he a h1
    · exact (hV a h1).2 e ((w6.2.2.1 e).1 he)
  refine ⟨⟨Q, R, { hSQ with eps := ⟨E, EQ, w1, w2, w3', w4, w5, w6⟩, omega := hΩ' }⟩, hB,
    ⟨{ hO with scW := fun c hc b hb hin => hSg _ ((hS.all c hc).2.2 b hb hin) }, hR, hX⟩,
    ⟨hSg, hSgK.ks, hks⟩, { hS with sub := hSg, ksΩ := hks }⟩

variable {A : Type _} (ar : machine.Arch A)

/-- **`FaultEntAt` from the facts `faultEntAt_of` read** (module
docstring): `BXI`, the current thread not blocked (`CanBlock.nb`), the
fault-handler cap typed (`EntryHyps0.tmoOK`'s third part), `U` outside the
TCBs and nodes and off `Ω` (`UserOK`), every TCB's receive buffer in `U`
(`XferHyps.buf`), `AsidOff`. -/
theorem faultEntAt_ofT {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {s : S} {t : obj.Tcb} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (et : sched.cur_thread st s = ok t)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s))))
    (hcap : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hU : ∀ b ∈ U, OutsideObjs st T Cs s b ∧ b ∉ Ω)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hAs : AsidOff (L := L) Ω Sg s) :
    FaultEntAt (L := L) T Cs Ω U Sg Rp s t := by
  refine ⟨hAs, fun ptr badge dest r hc => ?_⟩
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := hc.cap
  have hpH : H ptr = some .ep := by
    have h1 := hcap
    rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
    exact h1.1 ptr badge x y g gr rfl
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, w3, w4, -, w6⟩ := hW
  have hpE : ptr ∈ E := (w6.2.2.1 ptr).2 (Or.inl hpH)
  obtain ⟨hEP, hEN, hQ⟩ := w1 ptr hpE
  have hst : L.epState s ptr = obj.EP_RECV := by
    have h1 := hc.ep
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s ptr)] at h1; exact ok_inj_ff h1
  have hst2 : L.epState s ptr = 2#u64 := by rw [hst, ep_recv_val']
  have hhd : dest = L.mem s (epHeadA ptr) := by
    have h1 := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s ptr)] at h1; exact (ok_inj_ff h1).symm
  have hr : r = L.mem s (replyA dest) := by
    have h1 := hc.reply
    rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) s dest)] at h1; exact (ok_inj_ff h1).symm
  cases hl : EQ ptr with
  | nil =>
    have h1 := (w6.2.2.2.2.2 ptr hpE hl).1 hpH
    rw [hst2] at h1; exact absurd h1 (by decide)
  | cons y0 rest =>
    rw [hl] at hQ
    have hy0 : y0 = dest := by
      have h1 := hQ.head
      simp only [LawfulStore.epQ, List.headD_cons] at h1
      rw [hhd]; exact h1.symm
    subst hy0
    have hmem : y0 ∈ EQ ptr := by rw [hl]; exact List.mem_cons_self
    have hdT : y0 ∈ T := hQ.mem y0 List.mem_cons_self
    obtain ⟨-, -, hbl⟩ := w4 ptr hpE y0 hmem
    obtain ⟨k1, -, k3⟩ := w6.2.2.2.2.1 ptr hpE y0 hmem
    have hrecv : L.mem s (stA y0) = sched.TS_BLOCKED_ON_RECV := by
      rcases hbl with e | e | e
      · have := k1 e; rw [hst2] at this; exact absurd this (by decide)
      · exact e
      · have := k3 e; rw [hst2] at this; exact absurd this (by decide)
    have hdt : y0 ≠ t := by
      rintro rfl
      rw [et'] at hbl; exact hnb hbl
    have hr0 : L.mem s (replyA y0) ≠ 0#u64 := by rw [← hr]; exact hc.r0
    have hrR : r ∈ Rp := by rw [hr]; exact (hX.2.1.recv y0 hdT hrecv hr0).1
    have hrΩ : rTcbA r ∈ Ω := by
      refine hSg.sub _ (hX.1.rpW r hrR _ ?_ ?_ ?_)
      · show (rTcbA r).val % 8 = 0
        rw [rTcbA_val0]; have := (hX.1.rp r hrR).1; omega
      · rw [rTcbA_val0]
      · rw [rTcbA_val0]; omega
    refine ⟨hrR, rest, ?_⟩
    exact {
      hT := hSQ.tcbs
      ht := by rw [et']; exact hSQ.curT
      hE := hEP
      hEN := hEN
      hq := hQ
      hst := hst
      hdt := hdt
      hcC := hSQ.cur
      hN := hSQ.nodes _ hSQ.cur
      hU := hU
      hΩ := hSQ.omega
      hEΩ := w3 ptr hpE
      hrΩ := hrΩ
      hcur := by rw [et']; rfl
      hact := by
        have h1 := hc.act
        rw [eq_of_spec_fd (sched.action.spec (L := L) s)] at h1; exact ok_inj_ff h1
      hbuf := hbuf y0 hdT
      hrep := hr.symm
      hsc := (here_facts (L := L) hc.here).sc }

/-- **The handler an accepted fault fast path finds is blocked on receive**
(m70's `faultRecv_of` with the fault-handler cap typing as an argument). -/
theorem faultRecv_ofT {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {s : S} {t : obj.Tcb} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (et : sched.cur_thread st s = ok t)
    (hcap : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    {ptr badge dest r : U64} (hc : FaultChecks st s t ptr badge dest r) :
    L.mem s (stA dest) = sched.TS_BLOCKED_ON_RECV := by
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := hc.cap
  have hpH : H ptr = some .ep := by
    have h1 := hcap
    rw [← et', esl, WP.spec_ok, ecap, WP.spec_ok] at h1
    exact h1.1 ptr badge x y g gr rfl
  obtain ⟨E, EQ, hW⟩ := hSQ.eps
  obtain ⟨w1, -, -, w4, -, w6⟩ := hW
  have hpE : ptr ∈ E := (w6.2.2.1 ptr).2 (Or.inl hpH)
  obtain ⟨-, -, hQ⟩ := w1 ptr hpE
  have hst : L.epState s ptr = obj.EP_RECV := by
    have h1 := hc.ep
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s ptr)] at h1; exact ok_inj_ff h1
  have hst2 : L.epState s ptr = 2#u64 := by rw [hst, ep_recv_val']
  have hhd : dest = L.mem s (epHeadA ptr) := by
    have h1 := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s ptr)] at h1; exact (ok_inj_ff h1).symm
  cases hl : EQ ptr with
  | nil =>
    have h1 := (w6.2.2.2.2.2 ptr hpE hl).1 hpH
    rw [hst2] at h1; exact absurd h1 (by decide)
  | cons y0 rest =>
    rw [hl] at hQ
    have hy0 : y0 = dest := by
      have h1 := hQ.head
      simp only [LawfulStore.epQ, List.headD_cons] at h1
      rw [hhd]; exact h1.symm
    subst hy0
    have hmem : y0 ∈ EQ ptr := by rw [hl]; exact List.mem_cons_self
    obtain ⟨-, -, hbl⟩ := w4 ptr hpE y0 hmem
    obtain ⟨k1, -, k3⟩ := w6.2.2.2.2.1 ptr hpE y0 hmem
    rcases hbl with e | e | e
    · have := k1 e; rw [hst2] at this; exact absurd this (by decide)
    · exact e
    · have := k3 e; rw [hst2] at this; exact absurd this (by decide)

/-- **The general fault path's reads and `FaultNvm` at one state** where
`fastpath.fault` is entered, from `BXI` and the facts of `faultEntAt_ofT`
(module docstring). -/
theorem fastFault_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    (hA : P0.ArchTotal ar) {s : S} {a : A} {t : obj.Tcb} {n : U64}
    (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (et : sched.cur_thread st s = ok t)
    (hnb : ¬ Blocked (L.mem s (stA (L.curW s))))
    (hcap : obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hU : ∀ b ∈ U, OutsideObjs st T Cs s b ∧ b ∉ Ω)
    (hbuf : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hAs : AsidOff (L := L) Ω Sg s) :
    FaultOK (L := L) ar s a t n ∧ FaultNvm (L := L) ar s a t n := by
  have hF := faultEntAt_ofT hI et hnb hcap hU hbuf hAs
  exact ⟨faultOK_of ar hI hF, faultNvm_ofR ar hA hI (fun hc => faultRecv_ofT hI et hcap hc) hF⟩

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- **A declined debug syscall changes nothing** (`debug_syscall.same` with
the Arch value too: every `false` return is `ok (false, s, a)`). -/
theorem syscall.debug_syscall.same2 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (t : obj.Tcb) (n : I64) : syscall.debug_syscall st ar s a t n ⦃ b s' a' => b = false → s' = s ∧ a' = a ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have F : ∀ {s1 : S} {a1 : A}, (ok (true, s1, a1) : Result (Bool × S × A)) ⦃ b s' a' =>
      b = false → s' = s ∧ a' = a ⦄ :=
    (WP.spec_ok _).2 fun h => by cases h
  unfold syscall.debug_syscall
  split
  · exact WP.spec_bind (hA.halt a) fun _ _ => F
  split
  · exact F
  split
  · refine WP.spec_bind (P0.syscall.invoked_cap.p0 st s _ hS) fun c _ => ?_
    refine WP.spec_bind (P0.syscall.cap_type_code.p0 c) fun i _ => ?_
    exact WP.spec_bind (P0.obj.Tcb.set_reg.p0 st t s _ i hS) fun _ _ => F
  split
  · refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun _ _ => F
    exact WP.spec_mono (P0.syscall.debug_name_thread.p0 st ar s a t hS hA) fun _ _ => trivial
  have aff : (do
      let c ← syscall.invoked_cap st s t
      let o ← syscall.thread_of c
      match o with
      | none => do
        let a1 ← ar.halt a
        ok (true, s, a1)
      | some target => do
        let aff ← obj.Tcb.affinity st target s
        let s1 ← obj.Tcb.set_reg st t s layout.reg.CAP aff
        ok (true, s1, a)) ⦃ b s' a' => b = false → s' = s ∧ a' = a ⦄ := by
    refine WP.spec_bind (P0.syscall.invoked_cap.p0 st s _ hS) fun c _ => ?_
    refine WP.spec_bind (P0.syscall.thread_of.p0 c) fun o _ => ?_
    rcases o with _ | x
    · exact WP.spec_bind (hA.halt a) fun _ _ => F
    · refine WP.spec_bind (P0.obj.Tcb.affinity.p0 st x s hS) fun af _ => ?_
      exact WP.spec_bind (P0.obj.Tcb.set_reg.p0 st t s _ af hS) fun _ _ => F
  repeat (first | exact aff | exact F | exact (WP.spec_ok _).2 (fun _ => ⟨rfl, rfl⟩) | split)

end

end Fl4Proofs.P1
