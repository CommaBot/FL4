/-
# The fault fast path's entry-state facts derived (FL4 #56, m64 (d3'))

m63's `FastFaultPre` asked, at each state where `handle_syscall_fast` enters
`fastpath.fault`, for `FaultEntAt`: the ASID placement `AsidOff` [J] and, for
every accepted check, m61's `FaultEnt`. Here `FaultEnt` is derived at that
state from what holds there:

* the P1 invariants `BXI` and `XG` (`syscall.budget_ok.bxc`);
* the typing of the fault-handler cap, `EntryHyps0.tmoOK` (the same field the
  general fault path `faults.handle_fault.bxi` reads; from Hyps4's
  `P3Place.tmoOK`, i.e. P3's cap relation): the handler's endpoint is a heap
  endpoint, so `EpsWit` places it and gives its queue;
* the receive buffer from `XferHyps.buf` (Hyps4's `P3Place.xfer`);
* `dest ≠ t`: queue members are `Blocked` (`EpsWit`), the current thread is
  not (`CanBlock.nb`, from the same `tmoOK`);
* the handler blocked on receive (the endpoint is RECV, `EpTy`), so its reply
  is a reply object (`ReplyInv0.recv`) whose words are `Sg ⊆ Ω` words.

`AsidOff` is moved from the kernel entry state to the fast path's entry
state (`AsidOff.ent`: the entry prefix writes a TCB register and node words,
the table and pools are `Ω` words). The top `kernel_entry.entry_of7` is
`entry_of6` with `hFP : FastFaultPre` replaced by `AsidOff Ω Sg s` at the
kernel entry state.
-/
import Fl4Proofs.P1.FastFinInv
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

theorem obj.Ep.head.spec' (s : S) (ep : obj.Ep) :
    obj.Ep.head st ep s ⦃ v => v = L.mem s (epHeadA ep) ⦄ := by
  unfold obj.Ep.head; step*; simp_all [epHeadA]

/-- **The ASID placement survives the entry prefix**: the `FAULT_IP` write
and a passing `budget_ok` write a TCB register of the current thread and the
current node's words; the ASID table and pool words are `Ω` words, outside
the TCBs and nodes. -/
theorem AsidOff.ent {T Cs Ω Sg : Set U64} {e s : S} (hT : TcbPlaced T) (hcur : L.curW e ∈ T)
    (hc : L.cpu e ∈ Cs) (hN : NodePlaced st T e (L.cpu e)) (hΩ : ∀ a ∈ Ω, OutsideObjs st T Cs e a)
    (hE : Ent st e s) (h : AsidOff (L := L) Ω Sg e) : AsidOff (L := L) Ω Sg s := by
  have keep : ∀ b ∈ Ω, L.mem s b = L.mem e b := by
    intro b hb
    obtain ⟨ha, hTo, hNo⟩ := hΩ b hb
    refine hE.2.2 b ha ?_
    rintro (⟨K, hK, rfl⟩ | ⟨o, -, ho, -, rfl⟩)
    · have hK4 : K.val < 4096 := by rw [hK]; simp [layout.reg.FAULT_IP]
      have := hTo _ hcur
      rw [tcb_wadd_val (hT _ hcur) hK4] at this
      omega
    · have := hNo _ hc
      rw [nodeAt_val hN ho] at this
      omega
  intro hi hlt
  obtain ⟨a1, a2, a3⟩ := h hi hlt
  rw [hE.1, keep _ a1]
  exact ⟨a1, a2, a3⟩

variable {A : Type _} (ar : machine.Arch A)

/-- **(d3') `FaultEntAt` at the fast path's entry state** from the P1
invariants there (`BXI`, `XG`), the fault-handler cap typing
(`EntryHyps0.tmoOK`), the receive buffer (`XferHyps.buf`) and `AsidOff`. -/
theorem faultEntAt_of {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {P3Ok : S → Prop}
    (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {t : obj.Tcb} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (et : sched.cur_thread st s = ok t) (hAs : AsidOff (L := L) Ω Sg s) :
    FaultEntAt (L := L) T Cs Ω U Sg Rp s t := by
  refine ⟨hAs, fun ptr badge dest r hc => ?_⟩
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  obtain ⟨hCB, hUO, hcap⟩ := E0.tmoOK Ac s hG hI
  obtain ⟨⟨Q, R, hSQ⟩, hB, hX, hSg, hS⟩ := hI
  -- the handler cap names a heap endpoint
  obtain ⟨sl, x, y, g, gr, esl, ecap, -⟩ := hc.cap
  have hpH : H ptr = some .ep := by
    have h1 := hcap layout.tcb.SLOT_FAULT_HANDLER (Or.inr rfl)
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
      rw [et'] at hbl; exact hCB.nb hbl
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
      hU := fun b hb => ⟨(hUO b hb).1, (hUO b hb).2.1⟩
      hΩ := hSQ.omega
      hEΩ := w3 ptr hpE
      hrΩ := hrΩ
      hcur := by rw [et']; rfl
      hact := by
        have h1 := hc.act
        rw [eq_of_spec_fd (sched.action.spec (L := L) s)] at h1; exact ok_inj_ff h1
      hbuf := XH.buf Ac ∅ Q R s y0 hG ⟨hSQ, hB, hX, hS, hSg, hUO⟩ hdT
      hrep := hr.symm
      hsc := (here_facts (L := L) hc.here).sc }

/-- **(d3') `FastFaultPre` from `AsidOff` at the kernel entry state**: at
each state where `fastpath.fault` is entered, `BXI` and `XG` come from
`budget_ok.bxc` (after `reg_entry` and, on the out-of-range route,
`EntryHyps0.debug` + `debug_syscall.same`), `AsidOff` from the entry state by
`AsidOff.ent` (the prefix is `Ent`), and `faultEntAt_of` gives the rest. -/
theorem FastFaultPre.of_asid {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {P3Ok : S → Prop} (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (XH : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    {s : S} {a : A} {n : I64} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hAs : AsidOff (L := L) Ω Sg s) : FastFaultPre (L := L) ar T Cs Ω U Sg Rp s a n := by
  intro t nx s1 et enx es1
  have h0 := h.1.choose_spec.choose_spec
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  have htT : t ∈ T := by rw [et']; exact h0.curT
  have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := reg_entry (r := layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) h htT
      (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at this; exact this
  have hW := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (h0.tcbs t htT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW
  obtain ⟨K, hK, e1⟩ := hW
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h0.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have e1' : s1 = L.wr s (core.num.U64.wrapping_add (L.curW s) K) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [e1, et']
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal e1' (WritesIn.refl _ _)⟩
  have hN1 : NodePlaced st T s1 (L.cpu s1) := (h1.1.choose_spec.choose_spec).nodes _ h1.1.choose_spec.choose_spec.cur
  have hcur0 : L.curW s ∈ T := h0.curT
  have hAs2 : ∀ s2, WritesIn st s1 s2 (L.NodeOf s1 (L.cpu s1) fun _ => True) → AsidOff (L := L) Ω Sg s2 :=
    fun s2 w2 => AsidOff.ent h0.tcbs hcur0 h0.cur (h0.nodes _ h0.cur) h0.omega (Ent.prefix hK hal e1' w2) hAs
  refine ⟨fun s2 a2 t2 hb et2 => ?_, fun t1 s3 a3 et1 hd => ?_⟩
  · have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
    rw [hb, WP.spec_ok] at hx
    have hf := syscall.budget_ok.fr hA s1 a hN1
    rw [hb, WP.spec_ok] at hf
    exact faultEntAt_of ar E0 XH hx.1 (hx.2.2 rfl) et2 (hAs2 s2 (hf rfl))
  · intro s2 a2 t2 hb et2
    have et1' : t1 = L.curW s1 := by
      rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s1)] at et1; exact (ok_inj_ff et1).symm
    have hd' := hd
    rw [et1'] at hd'
    have hdi := E0.debug Ac s1 a n he1 h1
    rw [hd', WP.spec_ok] at hdi
    obtain ⟨Ac3, h3⟩ := hdi
    have hsame := syscall.debug_syscall.same (L := L) hA s1 a (L.curW s1) n
    rw [hd', WP.spec_ok] at hsame
    have e3 : s3 = s1 := hsame rfl
    subst e3
    have hx := syscall.budget_ok.bxc hA E0 s3 a3 h3 he1.xg
    rw [hb, WP.spec_ok] at hx
    have hf := syscall.budget_ok.fr hA s3 a3 hN1
    rw [hb, WP.spec_ok] at hf
    exact faultEntAt_of ar E0 XH hx.1 (hx.2.2 rfl) et2 (hAs2 s2 (hf rfl))

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`**, `entry_of6` with the fault
half's premise `hFP : FastFaultPre` (facts at the states where
`fastpath.fault` is entered) replaced by the ASID placement `AsidOff` [J] at
the kernel entry state (m64 (d3'): `FastFaultPre.of_asid`; the handler cap
typing and the receive buffer from Hyps4's `P3Place`). `StoreExt` [P] and the
ReplyRecv half `FastRRP` [P] unchanged; `entry_of6` kept. -/
theorem kernel_entry.entry_of7 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hRR : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter →
      FastRRP (st := st) ar s a number (fun r => ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' r.1)) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  exact kernel_entry.entry_of6 hA GF hσ s a hP h hX
    (fun number _ => FastFaultPre.of_asid ar hA E0 (GF _ hσ).1.xfer hP h hAs) hRR

end

end Fl4Proofs.P1
