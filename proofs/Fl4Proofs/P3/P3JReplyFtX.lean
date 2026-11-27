/-
P2-level (p3J gen 34): **`do_reply_transfer` in `IpcWN ∅ False … ∅`** from a state whose cap-slot words are those
of a `NoBufCap` state `sE` (P1's `do_reply_transfer.foot` gives `IpcFoot` only, from P1's `XferHyps`, which
P1/EntryVacuous refutes at every entry state). Namespace `Fl4Proofs.P1`, FL4 only.

* `TLK T sE s`: `s` has `sE`'s key-space base and the words below offset 192 (the six cap slots) of every TCB of `T`.
  It gives `BufK T sE s` (`TLK.bufK`) and, from the timeout-handler caps typed at `sE`, the typed timeout-handler cap
  at `s` (`TLK.tmo`, P2's `TmoCapW.of_eq`). Kept by every write of a `KW` word (P1's `capw_not_kw` at a `BlkOK`
  state), a debug-list word, or a transfer register word (`XferRegW T ∅`, offsets ≥ 256): `TLK.step`,
  `rx_notKW`, `rx_notDbg`, `rx_notReg`.
* `sporadic.unblock_check.kwN`: P2's `unblock_sporadic.kwN` body for `unblock_check` alone (the SC from `RPre`'s
  `Ac` fact, not from `sc_sporadic`).
* `ipc.do_ipc_transfer.nbR`: P3JFltX's `do_ipc_transfer.nbX` with P2's `RS` the transfer's own register / SC-word
  footprint (`XSFC.start`'s closure is exactly such writes), so the cap-slot words are seen to be kept.
* `reply_tail.footNB`: P1's `reply_tail.foot` with P2's `possible_switch_to.kwN`, `postpone.kwN` and
  `handle_timeout.footN` (P3JFltX's `xferOKRS_nb` / `xferFootOKC_nb`, `XG` at `P3Ok := True` by `xg_triv`, the
  timeout cap by `TLK.tmo`).
* **`ipc.do_reply_transfer.footNB`**: P1's `do_reply_transfer.foot` walk: `reply_remove` by P1's `.blk` (invariants)
  and P3JReplyFtN's `kwDN0` (footprint; `DbgTz` from `XInv`'s `tm`), `unblock_check` by `.all` and `.kwN`, the
  `NullFault` transfer by `nbR` + P2's `XferWC.ipcN`, the fault reply by P1's `.rf` / `.rg` + `xfer_all`,
  `clear_fault` by `footN_field`, `set_thread_state` by P2's `.kwN`, the tail by `reply_tail.footNB`.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JReplyFtN
import Fl4Proofs.P2.StallAllJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- (p3J gen 34) `s` has `sE`'s key-space base and the cap-slot words of every TCB of `T`. -/
def TLK (T : Set U64) (sE s : S) : Prop :=
  L.ksb s = L.ksb sE ∧ ∀ y ∈ T, ∀ K : U64, K.val < 192 → K.val % 8 = 0 →
    L.mem s (core.num.U64.wrapping_add y K) = L.mem sE (core.num.U64.wrapping_add y K)

theorem TLK.refl (s : S) : TLK (L := L) T s s := ⟨rfl, fun _ _ _ _ _ => rfl⟩

theorem TLK.bufK {sE s : S} (h : TLK (L := L) T sE s) : BufK (L := L) T sE s := by
  refine ⟨h.1, fun y hy => ?_⟩
  rw [sbWordA8_eq, sbWordA_eq]
  exact ⟨h.2 y hy _ (by simp) (by simp), h.2 y hy _ (by simp) (by simp)⟩

theorem TLK.tmo {sE s : S} (hm : ∀ t ∈ T, TmoCapW st H Rp Nt sE t) (h : TLK (L := L) T sE s) {t : U64}
    (ht : t ∈ T) : TmoCapW st H Rp Nt s t :=
  (hm t ht).of_eq (h.2 t ht 128#u64 (by simp) (by simp)) (h.2 t ht 136#u64 (by simp) (by simp))

theorem TLK.step {sE s s' : S} {B : U64 → Prop} (hT : TcbPlaced T) (h : TLK (L := L) T sE s)
    (w : WritesIn st s s' B)
    (hB : ∀ y ∈ T, ∀ K : U64, K.val < 192 → K.val % 8 = 0 → ¬ B (core.num.U64.wrapping_add y K)) :
    TLK (L := L) T sE s' :=
  ⟨w.1.trans h.1, fun y hy K hK h8 =>
    (w.mem_eq (field_aligned (hT y hy) (by omega) h8) (hB y hy K hK h8)).trans (h.2 y hy K hK h8)⟩

theorem rx_notKW {s : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) {y K : U64} (hy : y ∈ T)
    (hK : K.val < 192) (h8 : K.val % 8 = 0) :
    ¬ KW st T Cs Sg Scs Z (EH H) s (core.num.U64.wrapping_add y K) := fun hk =>
  capw_not_kw h (Or.inl ⟨y, hy, K, hK, rfl⟩)
    (field_aligned (h.1.choose_spec.choose_spec.tcbs y hy) (by omega) h8) le_rfl (by omega) hk

theorem rx_notDbg {s : S} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c) {y K : U64} (hy : y ∈ T)
    (hK : K.val < 192) : ¬ DbgW st T Cs s (core.num.U64.wrapping_add y K) := by
  rintro (⟨y', hy', e | e⟩ | ⟨c, hc, e⟩)
  · exact tlow_ne_field (K := 3576#u64) hT hy' (by simp) (by simp) ⟨y, hy, K, hK, rfl⟩ e
  · exact tlow_ne_field (K := 3584#u64) hT hy' (by simp) (by simp) ⟨y, hy, K, hK, rfl⟩ e
  · exact tlow_ne_node hT (hN c hc) (by simp [debug_val]) ⟨y, hy, K, hK, rfl⟩ e.symm

theorem rx_notReg (hT : TcbPlaced T) {y K : U64} (hy : y ∈ T) (hK : K.val < 192) :
    ¬ XferRegW T ∅ (core.num.U64.wrapping_add y K) := by
  rintro (⟨y', hy', K', h1, h2, -, e⟩ | hu)
  · exact tlow_ne_field hT hy' (by omega) (by omega) ⟨y, hy, K, hK, rfl⟩ e
  · exact absurd hu (Set.notMem_empty _)

variable {Es : Set U64} {Kp : Set U64} {Nd : Prop}

/-- (p3J gen 34) **`unblock_check` in `KWN`** (P2's `unblock_sporadic.kwN` body). -/
theorem sporadic.unblock_check.kwN {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} (s : S)
    (t i : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) (i_post : i = L.mem s (scA t)) (hi0 : i ≠ 0#u64)
    (hiA : i ∈ Ac) :
    sporadic.unblock_check st s i ⦃ s' => FootN st Kp Nd T Cs Sg Scs Z Es s s' ⦄ := by
  have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
  obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
  rw [← i_post] at hiS
  have hW : RefillsWF st s i (Z i) := hS.wf hiS hiA
  have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
  have hN' := h.nodes _ h.cur
  have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
  have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
  have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
    hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
  refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootN.of' w3 (fun b hb hh => ?_)
    (AcK.of_eq (actionW_of w3 hN' (by
      rintro (hh | e)
      · exact notAct_omega h (hX.1.scW i hiS _ (act_aligned hN') hh.inSC)
      · exact notAct_node hN' hN' (by rw [rp]; omega) (by rw [rp]; omega) e)))
  rcases hh with hh | rfl
  · exact ⟨hh.kw hiS, notIdW_ring h hX hiS hb hh⟩
  · exact ⟨kw_node h.cur (by rw [rp]; omega) (by rw [rp]; omega),
      notIdW_node h.nodes h.cur (by rw [rp]; omega) (idOff_ge (by rw [rp]; omega))⟩

variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- (p3J gen 34) **The message transfer from a `BufK` state, with its own register / SC-word footprint as `RS`**
(P3JFltX's `nbX`). -/
theorem ipc.do_ipc_transfer.nbR {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) {s : S} {a : A} {snd ep badge rcv : U64} {grant : Bool} (hs : snd ∈ T)
    (hr : rcv ∈ T) (hI : XI st T Cs Ω H Sg Rp Scs Nt Z ∅ Ac X Q R s) (hrs : BufK (L := L) T sE s) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅
        (fun s0 s1 => WritesIn st s0 s1 (fun b => XferRegW T ∅ b ∨ ∃ c ∈ Scs, InSC c (Z c) b)) Ac X Q R s s' ⦄ := by
  have hP0 : P0.StoreTotal st := L.total
  have h0 : XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅
      (fun s0 s1 => WritesIn st s0 s1 (fun b => XferRegW T ∅ b ∨ ∃ c ∈ Scs, InSC c (Z c) b)) Ac X Q R s s :=
    XSFC.start hI (WritesIn.refl _ _) fun _ _ r w => (r.trans w).mono fun _ hb => hb.elim id id
  have hl := lookup_ipc_buffer_noBuf (hN.of_bufK hrs) hr true
  have hb0 : BufOK ∅ 0#u64 := fun h => (h rfl).elim
  unfold ipc.do_ipc_transfer
  rw [hl, bind_ok]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hP0) fun ft _ => ?_
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false snd hP0) fun sb _ => ?_
    exact do_normal_transfer_rb0 h0 hr hb0
  · exact ipc.do_fault_transfer.xsfc hA h0 hs hr hb0

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **The tail of `do_reply_transfer` in `IpcWN ∅ False … ∅`** (P1's `reply_tail.foot`). -/
theorem reply_tail.footNB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z (EH H) sE)
    (hTmo : ∀ t ∈ T, TmoCapW st H Rp Nt sE t)
    {s3 : S} {a2 : A} {i ft : U64}
    (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (r : RTail st T Ac s3 i) (hK : TLK (L := L) T sE s3) :
    (do
      let i3 ← obj.Tcb.sc st i s3
      let b2 ← obj.Sc.is_null i3
      if b2 then ok (s3, a2)
      else
        let b3 ← sched.is_runnable st s3 i
        if b3 then
          let b4 ← sporadic.ready st s3 i3
          if b4 then
            let b5 ← sporadic.sufficient st ar s3 a2 i3 0#u64
            if b5 then
              let s4 ← sched.possible_switch_to st s3 i
              ok (s4, a2)
            else
              let b6 ← faults.valid_timeout_handler st s3 i
              if b6 then
                if ft != fl4_abi.consts.fault.Timeout then
                  let badge ← obj.Sc.badge st i3 s3
                  faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
                else
                  let s4 ← sched.postpone st s3 i3
                  ok (s4, a2)
              else
                let s4 ← sched.postpone st s3 i3
                ok (s4, a2)
          else
            let b5 ← faults.valid_timeout_handler st s3 i
            if b5 then
              if ft != fl4_abi.consts.fault.Timeout then
                let badge ← obj.Sc.badge st i3 s3
                faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
              else
                let s4 ← sched.postpone st s3 i3
                ok (s4, a2)
            else
              let s4 ← sched.postpone st s3 i3
              ok (s4, a2)
        else ok (s3, a2)) ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s3 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have q0 := h.1.choose_spec.choose_spec
  step with obj.Tcb.sc.spec as ⟨i3, ei3⟩
  step with obj.Sc.is_null.spec as ⟨b2, eb2⟩
  split
  · exact (WP.spec_ok _).2 (IpcFootN.refl _)
  rename_i hb2
  have hi0 : L.mem s3 (scA i) ≠ 0#u64 := fun e => hb2 (by rw [eb2, ei3, e]; rfl)
  subst ei3
  refine WP.spec_bind (sched.is_runnable.spec' s3 i) fun b3 hb3 => ?_
  split
  swap
  · exact (WP.spec_ok _).2 (IpcFootN.refl _)
  have PP : (do
      let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
      ok (s4, a2)) ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s3 s' ⦄ := by
    obtain ⟨⟨Q, R, h0⟩, hB, hX, hSg, hSc⟩ := h
    obtain ⟨hcS, htc, hcc⟩ := hX.2.2.bound i r.mem hi0
    have hm : scCoreA (L.mem s3 (scA i)) ∈ Ω := hSg.sub _ (hX.1.fixW _ hcS).2
    exact WP.spec_bind (sched.postpone.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H)
      s3 _ Q R h0 (by rw [htc]; exact r.mem) (by rw [htc]; exact r.nr) (h0.omega _ hm) hcc
      (by rw [htc]; exact Set.notMem_empty _)) fun s4 h4 => (WP.spec_ok _).2 (FootN.ipc h4)
  have hxf := xferOKRS_nb (Ω := Ω) (H := H) (Rp := Rp) (Nt := Nt) (P3Ok := fun _ => True) hA hN hP
  have hxw := xferFootOKC_nb (Ω := Ω) (H := H) (Rp := Rp) (Nt := Nt)
    (G := XG st T Cs Ω H Sg Scs Z (fun _ => True)) hA hN hP
  have TO : ∀ badge : U64, faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge) ⦃ s' _ =>
      IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s3 s' ⦄ := fun badge =>
    WP.spec_mono (faults.handle_timeout.footN (Kp := ∅) (Nd := False) hA hxf hxw s3 a2 i _ h.blk
      (fun b hb => absurd hb (Set.notMem_empty b)) r.cb (TLK.tmo hTmo hK r.mem).slot
      (fun _ _ _ h1 w => bufK_kw hP h1 w) hK.bufK (xg_triv s3) (Set.notMem_empty _)
      (fun y hy => absurd hy (Set.notMem_empty y)) (fun y hy => absurd hy (Set.notMem_empty y)) actOut_empty)
      fun rr hr => by
        obtain ⟨s', a'⟩ := rr
        simp only [WP.uncurry'_pair] at hr ⊢
        exact hr.1
  have VT : (do
      let b6 ← faults.valid_timeout_handler st s3 i
      if b6 then
        if ft != fl4_abi.consts.fault.Timeout then
          let badge ← obj.Sc.badge st (L.mem s3 (scA i)) s3
          faults.handle_timeout st ar s3 a2 i (error.Fault.Timeout badge)
        else
          let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
          ok (s4, a2)
      else
        let s4 ← sched.postpone st s3 (L.mem s3 (scA i))
        ok (s4, a2)) ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s3 s' ⦄ := by
    refine WP.spec_bind (P0.faults.valid_timeout_handler.p0 st s3 i hS) fun b6 _ => ?_
    split
    · split
      · exact WP.spec_bind (P0.obj.Sc.badge.p0 st _ s3 hS) fun badge _ => TO badge
      · exact PP
    · exact PP
  refine WP.spec_bind (sporadic.ready.spec s3 _) fun b4 _ => ?_
  split
  · refine WP.spec_bind (sporadic.sufficient.ok hA s3 a2 _ 0#u64) fun b5 _ => ?_
    split
    · exact WP.spec_bind (sched.possible_switch_to.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z)
        (Es := EH H) s3 i q0 r.mem (Set.notMem_empty _) actOut_empty) fun s4 h4 => (WP.spec_ok _).2 (FootN.ipc h4)
    · exact VT
  · exact VT

set_option maxHeartbeats 4000000 in
/-- (p3J gen 34) **`do_reply_transfer` in `IpcWN ∅ False … ∅`** (module docstring). -/
theorem ipc.do_reply_transfer.footNB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z (EH H) sE)
    (hTmo : ∀ t ∈ T, TmoCapW st H Rp Nt sE t)
    (s : S) (a : A) (ct r : U64) (grant : Bool) (h : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hr : r ∈ Rp)
    (hct : ct ∈ T) (hK0 : TLK (L := L) T sE s) :
    ipc.do_reply_transfer st ar s a ct r grant ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hT := h.1.choose_spec.choose_spec.tcbs
  have hD : DbgTz st T Cs s := ⟨h.2.2.1.2.2.tm.dn, h.2.2.1.2.2.tm.dp, h.2.2.1.2.2.tm.dh⟩
  have h0 := h.1.choose_spec.choose_spec
  unfold ipc.do_reply_transfer
  refine WP.spec_bind (obj.Reply.tcb.blk s r) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (IpcFootN.refl _)
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  obtain ⟨-, hiT, -, -⟩ := h.2.2.1.2.1.back r hr (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · exact (WP.spec_ok _).2 (IpcFootN.refl _)
  rename_i hv
  have hst : L.mem s (stA i) = sched.TS_BLOCKED_ON_REPLY := by
    rw [← ev]; apply UScalar.eq_of_val_eq; simpa [sched.TS_BLOCKED_ON_REPLY] using hv
  have hni : L.idleW s ≠ i := fun e => h.2.1.idleNB (by rw [e, hst]; exact Or.inr rfl)
  refine WP.spec_bind (WP.spec_and (ipc.reply_remove.blk (Es := EH H) hA s a r i h.blk hr hiT ei.symm hst)
    (ipc.reply_remove.kwDN0 (Es := EH H) hA s a r i h0 h.2.2.1 h.2.2.2.1.sub hD hr hiT)) ?_
  rintro ⟨s3, a2⟩ ⟨⟨h3b, st3, -, sca3, id3⟩, G3⟩
  try simp only [WP.uncurry'_pair]
  have T3 : TLK (L := L) T sE s3 := TLK.step hT hK0 (WritesA.w G3) fun y hy K hK h8 hh =>
    hh.1.elim (rx_notKW h.blk hy hK h8) (rx_notDbg hT h0.nodes hy hK)
  have I3 : IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s3 := FootDN.ipc G3
  have h3 := BlkOK.bxi h3b
  obtain ⟨dq3, dr3, da3⟩ := blocked_out h3.1.choose_spec.choose_spec hiT (by rw [st3]; exact not_runnable_inactive)
  have R3 : RPre st T Ac s3 i := ⟨hiT, st3, dq3, dr3, da3, by rw [id3]; exact hni, sca3⟩
  -- the SC's refills
  step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
  refine WP.spec_bind (sporadic.sc_sporadic.spec s3 i2) fun b1 hb1 => ?_
  refine WP.spec_bind (Pₘ := fun s4 => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s4 ∧ RPre st T Ac s4 i ∧
    IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s4 ∧ TLK (L := L) T sE s4) ?_ ?_
  · split
    · rename_i hb1t
      have hi20 := (hb1 hb1t).1
      step with obj.Sc.cpu.spec as ⟨cpu, _⟩
      step with obj.node_get.spec as ⟨cs, _⟩
      split
      · obtain ⟨⟨Q, R, q3⟩, hB3, hX3, hSg3, hS3⟩ := h3
        refine WP.spec_mono (WP.spec_and (sporadic.unblock_check.all s3 i i2 q3 hB3 hX3 hS3 hSg3 hiT ei2 hi20
          (by rw [ei2]; exact sca3 (by rw [← ei2]; exact hi20)))
          (sporadic.unblock_check.kwN (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z) (Es := EH H) s3 i i2
            q3 hX3 hS3 hiT ei2 hi20 (by rw [ei2]; exact sca3 (by rw [← ei2]; exact hi20)))) ?_
        rintro s4 ⟨⟨q4, hB4, hX4, hS4, hSg4, ea4, -, ei4, f4, -⟩, fu⟩
        refine ⟨⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩, R3.keep ?_ ?_ ?_ ea4 ei4, I3.trans (FootN.ipc fu),
          TLK.step hT T3 (WritesA.w fu) fun y hy K hK h8 hh => rx_notKW h3b hy hK h8 hh.1⟩
        · rw [stA_eq]; exact f4 i hiT _ (by simp) (by simp)
        · rw [inqA_eq]; exact f4 i hiT _ (by simp) (by simp)
        · rw [scA_eq]; exact f4 i hiT _ (by simp) (by simp)
      · exact (WP.spec_ok _).2 ⟨h3, R3, I3, T3⟩
    · exact (WP.spec_ok _).2 ⟨h3, R3, I3, T3⟩
  rintro s4 ⟨h4, R4, G4, T4⟩
  have h4b := h4.blk
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st i s4 hS) fun ft _ => ?_
  refine WP.spec_bind (Pₘ := fun r : S × A => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac r.1 ∧ RTail st T Ac r.1 i ∧
    IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s r.1 ∧ TLK (L := L) T sE r.1) ?_ ?_
  · split
    · -- the message
      obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩ := h4
      have hU4 : UserOK st T Cs Ω H ∅ s4 := fun b hb => absurd hb (Set.notMem_empty b)
      refine WP.spec_bind (ipc.do_ipc_transfer.nbR (grant := grant) (ep := 0#u64) (badge := 0#u64) (a := a2)
        hA hN hct hiT ⟨q4, hB4, hX4, hS4, hSg4, hU4⟩ T4.bufK) ?_
      rintro s5 ⟨⟨q5, hB5, hX5, hS5, hSg5, -⟩, ⟨ea5, -, ei5, -, f5, -, -⟩, w5, r5, -⟩
      have h5 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s5 := ⟨⟨Q, R, q5⟩, hB5, hX5, hSg5, hS5⟩
      have R5 : RPre st T Ac s5 i := R4.keep (by rw [stA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [inqA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [scA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp)) ea5 ei5
      have W5 : IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s4 s5 := XferWC.ipcN q4 hX4 hU4 hSg4.sub w5
      have T5 : TLK (L := L) T sE s5 := TLK.step hT T4 r5 fun y hy K hK h8 hh =>
        hh.elim (rx_notReg hT hy hK) fun hc => rx_notKW h4b hy hK h8 (Or.inr (Or.inr (Or.inr (Or.inl hc))))
      refine WP.spec_bind (WP.spec_and (R5.set h5 not_blocked_running running_ne)
        (sched.set_thread_state.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H)
          s5 i _ q5 hiT (Set.notMem_empty _))) fun s6 h6 => ?_
      exact (WP.spec_ok _).2 ⟨h6.1.1, h6.1.2, (G4.trans W5).trans (FootN.ipc h6.2),
        TLK.step hT T5 (WritesA.w h6.2) fun y hy K hK h8 hh => rx_notKW h5.blk hy hK h8 hh.1⟩
    · -- the fault reply
      refine WP.spec_bind (WP.spec_and (faults.handle_fault_reply.rf (s := s4) (a := a2) (snd := ct) hT hiT)
        (faults.handle_fault_reply.rg (s := s4) (a := a2) (snd := ct) hT hiT)) ?_
      rintro ⟨rs, s5, a3⟩ ⟨w5, g5⟩
      try simp only [WP.uncurry'_pair]
      obtain ⟨⟨Q, R, q4⟩, hB4, hX4, hSg4, hS4⟩ := h4
      have hU4 : UserOK st T Cs Ω H ∅ s4 := fun b hb => absurd hb (Set.notMem_empty b)
      obtain ⟨q5, hB5, hX5, hS5, hSg5, ea5, -, ei5, -, f5, -⟩ :=
        xfer_all (U := ∅) q4 hB4 hX4 hS4 hSg4 hU4 w5
      have h5 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s5 := ⟨⟨Q, R, q5⟩, hB5, hX5, hSg5, hS5⟩
      have R5 : RPre st T Ac s5 i := R4.keep (by rw [stA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [inqA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp))
        (by rw [scA_eq]; exact f5 i hiT _ (by simp) (by simp) (by simp)) ea5 ei5
      have W5 : IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s4 s5 :=
        XferWC.ipcN q4 hX4 hU4 hSg4.sub (w5.mono fun _ hb => Or.inl hb)
      have T5 : TLK (L := L) T sE s5 := TLK.step hT T4 g5 fun y hy K hK _ hh => rx_notReg hT hy hK hh
      unfold faults.clear_fault
      refine WP.spec_bind (obj.Tcb.set_fault_type.spec s5 i _) fun s6 e6 => ?_
      subst e6
      have h6 := bxi_field (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault) h5 hiT (by simp) (by simp)
        (by simp) (by simp)
      have hN5 := h5.1.choose_spec.choose_spec.nodes _ h5.1.choose_spec.choose_spec.cur
      have n6 := ani_field (K := 3376#u64) (v := fl4_abi.consts.fault.NullFault) hT hN5 hiT (by simp) (by simp)
      have fw : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3376 →
          L.mem (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) (core.num.U64.wrapping_add i K) =
            L.mem s5 (core.num.U64.wrapping_add i K) := fun K a1 a2 a3 =>
        L.mem_wr_ne (field_aligned (K := 3376#u64) (hT i hiT) (by simp) (by simp)) (field_aligned (hT i hiT) a1 a2)
          (fun e => field_ne (K1 := 3376#u64) (hT i hiT) (hT i hiT) (by simp) a1 (fun _ => by simp; omega)
            (UScalar.eq_of_val_eq e))
      have R6 : RPre st T Ac (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) i :=
        R5.keep (by rw [stA_eq]; exact fw _ (by simp) (by simp) (by simp))
          (by rw [inqA_eq]; exact fw _ (by simp) (by simp) (by simp))
          (by rw [scA_eq]; exact fw _ (by simp) (by simp) (by simp)) n6.1 n6.2.1
      have q5' := h5.1.choose_spec.choose_spec
      have F6 : FootN st ∅ False T Cs Sg Scs Z (EH H) s5 (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) :=
        footN_field (K := 3376#u64) hT q5'.nodes q5'.cur hiT (by simp) (by simp) (by simp) (by simp)
      have T6 : TLK (L := L) T sE (L.wr s5 (faultA i) fl4_abi.consts.fault.NullFault) :=
        TLK.step hT T5 (WritesA.w F6) fun y hy K hK h8 hh => rx_notKW h5.blk hy hK h8 hh.1
      have q6 := h6.1.choose_spec.choose_spec
      split
      · refine WP.spec_bind (WP.spec_and (R6.set h6 not_blocked_restart restart_ne)
          (sched.set_thread_state.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H)
            _ i _ q6 hiT (Set.notMem_empty _))) fun s7 h7 => ?_
        exact (WP.spec_ok _).2 ⟨h7.1.1, h7.1.2, G4.trans (W5.trans ((FootN.ipc F6).trans (FootN.ipc h7.2))),
          TLK.step hT T6 (WritesA.w h7.2) fun y hy K hK h8 hh => rx_notKW h6.blk hy hK h8 hh.1⟩
      · refine WP.spec_bind (WP.spec_and (R6.set h6 not_blocked_inactive inactive_ne)
          (sched.set_thread_state.kwN (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H)
            _ i _ q6 hiT (Set.notMem_empty _))) fun s7 h7 => ?_
        exact (WP.spec_ok _).2 ⟨h7.1.1, h7.1.2, G4.trans (W5.trans ((FootN.ipc F6).trans (FootN.ipc h7.2))),
          TLK.step hT T6 (WritesA.w h7.2) fun y hy K hK h8 hh => rx_notKW h6.blk hy hK h8 hh.1⟩
  rintro ⟨s6, a6⟩ ⟨h6, r6, F6, T6⟩
  try simp only [WP.uncurry'_pair]
  refine WP.spec_mono (reply_tail.footNB (ft := ft) (a2 := a6) hA hN hP hTmo h6 r6 T6) fun rr hr => ?_
  obtain ⟨s', a'⟩ := rr
  simp only [WP.uncurry'_pair] at hr ⊢
  exact F6.trans hr

end

end Fl4Proofs.P1
