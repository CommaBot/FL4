/-
P2 (p2j, KWN step 5): **`send_ipc` and the timeout fault in `KWN`**.

* `IpcFootN`: P1's `IpcFoot` (`IpcW`: `KW`, the receiver's user context and
  IPC buffer, cap-slot words, debug-list words) without node identity
  words; `refl`/`trans`, `FootDN.ipc`, `FootN.ipc`, `XferWC.ipcN` (the
  transfer's words are no node identity words, from the invariants at the
  transfer's start and `UserOK`).
* `send_ipc.footPN` (P1 `send_ipc.footP` over `KWN` steps), `send_ipc.footN`,
  `handle_timeout.footN`: a timeout fault writes only `IpcW` words and no
  node identity word.
* `tmoKC_N`: the timeout faults of a budget check keep `GN s0` (`XG` and an
  `IpcFootN` footprint from `s0`), as `TmoKC` (`P2/FootN3.lean`): at the
  states the check itself reaches. `CanBlock` is proved there, `RS s s` comes
  from `RS` at the check's start. (p2j4: this replaces `tmoKG_N`, whose
  premises `EntryHyps0` — see `P2/BlkUCheck.lean` — and `hRSX` quantified
  over all `XG`/`BXI` states.) **Named premise `hcap` [P]**: the timeout
  handler cap is typed at those states. `GN s0` is kept by `KWN` steps
  (`GN.foot`), so with `check_budget.allGN` the budget path from `s0` writes
  no node identity word of `s0`.
* (p2j3) the exclusion layer: `send_ipc.footPN`/`footN` and
  `handle_timeout.footN` take the sender `t ∉ Kp`, the protected threads
  not blocked (so the woken receiver is none of them) and, for a
  donation, `¬ Nd`; `tmoKC_N` runs in `Nd` mode and derives these from
  `s0` (the current thread and the `Kp` states are protected words).
  (p2j4) the transfer's footprint is taken as `XferFootOKC`
  (`P2/XferN.lean`: only SC `CONSUMED` words; a named premise [J] of the
  stall theorems since p2j8), so `XferWC.ipcN` needs no premise (the earlier
  `XferHdr` [P] is gone).
* (p2j13) **`XferOKRS` [J]**: P1's `XferOK` only at states with `RS s s`
  (docstring there); `xferOK_rs` gives P1's `XferOK` at the guard `XGR`
  (`XG` and `RS s s`) from it and `XferFootOKC`, `XGR.faultG` the fault
  IPC's guard. `send_ipc.footPN`/`footN`, `handle_timeout.footN` and
  `tmoKC_N` take it in place of the unguarded `XferOK` at `XG`;
  `send_ipc.footN`/`handle_timeout.footN` also give `XG` at the end, so
  `tmoKC_N` no longer takes P1's `TmoXG`. P1 is unchanged (follow-up:
  restate `xferOK_of` from an `RS` carrying P3's cap relation).
-/
import Fl4Proofs.P2.FootN3
import Fl4Proofs.P2.FootN4
import Fl4Proofs.P2.XferN
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- `IpcW` without the node identity words. -/
def IpcWN {S : Type _} (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat)
    (Es U : Set U64) (s0 : S) (b : U64) : Prop :=
  IpcW st T Cs Ω Sg Scs Z Es U s0 b ∧ ¬ IdW st Kp Nd T Cs Scs s0 b

/-- A footprint inside `IpcWN`. -/
abbrev IpcFootN {S : Type _} (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat)
    (Es U : Set U64) (s s' : S) : Prop :=
  WritesA st T Kp s s' (IpcWN st Kp Nd T Cs Ω Sg Scs Z Es U s)

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64} {Kp : Set U64} {Nd : Prop}

theorem IpcFootN.refl (s : S) : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s := WritesA.refl _ _

theorem IpcFootN.trans {s₁ s₂ s₃ : S} (h₁ : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s₁ s₂)
    (h₂ : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s₂ s₃) : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s₁ s₃ :=
  WritesA.mono (WritesA.trans h₁ h₂) fun b hb =>
    Or.elim hb id fun hb => ⟨IpcW.ksb h₁.1 hb.1, notIdW_ksb h₁.1.symm h₁.2.1.symm hb.2⟩

theorem IpcFootN.ipc {s s' : S} (h : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') : IpcFoot st T Cs Ω Sg Scs Z Es U s s' :=
  WritesIn.mono (WritesA.w h) fun _ hb => hb.1

/-- An `IpcFootN` footprint keeps the node identity words. -/
theorem IpcFootN.idKeep {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') {b : U64} (hb : Aligned b)
    (hi : IdW st Kp Nd T Cs Scs s b) : L.mem s' b = L.mem s b :=
  f.mem_eq hb fun hk => hk.2 hi

theorem FootDN.ipc {s s' : S} (h : FootDN st Kp Nd T Cs Sg Scs Z Es s s') : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s' :=
  WritesA.mono h fun _ hb => ⟨hb.1.elim Or.inl fun hd => Or.inr (Or.inr (Or.inr hd)), hb.2⟩

theorem FootN.ipc {s s' : S} (h : FootN st Kp Nd T Cs Sg Scs Z Es s s') : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s' :=
  FootDN.ipc h.d

/-- An SC's `CONSUMED` word is no SC's `REPLY` or `TCB` word. -/
theorem cons_ne_hdr {s : S} (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) {c c' : U64} (hc : c ∈ Scs) (hc' : c' ∈ Scs) :
    core.num.U64.wrapping_add c layout.sc.CONSUMED ≠ scReplyA c' ∧
      core.num.U64.wrapping_add c layout.sc.CONSUMED ≠ scTcbA c' := by
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨hP', hz'⟩ := hO.sc c' hc'
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have a1 : (core.num.U64.wrapping_add c layout.sc.CONSUMED).val = c.val + 8 := by rw [hv, hcv]
  have hr := scReplyA_val hP' hz'
  have ht := scTcbA_val hP' hz'
  have h7 : 128 ≤ 2 ^ Z c := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hz)
  have h7' : 128 ≤ 2 ^ Z c' := le_trans (by norm_num) (Nat.pow_le_pow_right (by omega) hz')
  refine ⟨fun e2 => ?_, fun e2 => ?_⟩
  · have := congrArg UScalar.val e2
    rw [a1, hr] at this
    by_cases e : c = c'
    · subst e; omega
    · rcases hO.scDisj c hc c' hc' e with d | d <;> omega
  · have := congrArg UScalar.val e2
    rw [a1, ht] at this
    by_cases e : c = c'
    · subst e; omega
    · rcases hO.scDisj c hc c' hc' e with d | d <;> omega

/-- **The transfer's `XferWC` footprint is an `IpcWN` footprint** (no premise:
the transfer's SC words are `CONSUMED` words, no SC link). -/
theorem XferWC.ipcN {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s' : S}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hU : UserOK st T Cs Ω H U s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (w : WritesIn st s s' (XferWC T U Ω Sg Scs (L.ksb s))) :
    IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s' := by
  have hO := hX.1
  have hN := h.nodes _ h.cur
  have hact : L.actionW s' = L.actionW s := by
    refine actionW_of w hN ?_
    have e16 : layout.node.SCHED_ACTION.val = 16 := act_val
    rintro ((⟨y, hy, K, hK, -, e⟩ | hu) | ⟨⟨y, hy, K, hK, e⟩ | ⟨hm, -⟩, -⟩ | ⟨c, hc, e⟩)
    · exact node_ne_field hN (by omega) hy (h.tcbs y hy) (by omega) e
    · exact out_ne_node (hU _ hu).1 h.cur hN (by omega) rfl
    · exact node_ne_field hN (by omega) hy (h.tcbs y hy) (by omega) e
    · exact notAct_omega h hm
    · exact notAct_omega h (hO.scW c hc _ (act_aligned hN) (e ▸ (consW_in hO hc).2))
  refine ⟨w.1, w.2.1, fun b hb hn => w.2.2 b hb fun hx => hn ⟨?_, ?_⟩, AcK.of_eq hact⟩
  · rcases hx with hx | hx | ⟨c, hc, e⟩
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inl (kw_sc hc (by rw [e]; exact (consW_in hO hc).2))
  · rcases hx with (⟨y, hy, K, hK, -, e⟩ | hu) | ⟨⟨y, hy, K, hK, e⟩ | ⟨hm, hns⟩, -⟩ | ⟨c, hc, e⟩
    · subst e; exact notIdW_field h.tcbs h.nodes hy (by omega)
    · exact notIdW_out h.nodes (hU b hu).1 fun _ c hc =>
        ⟨fun e => (hU b hu).2.1 (by rw [e]; exact hsub _ (hO.repW c hc)),
          fun e => (hU b hu).2.1 (by rw [e]; exact hsub _ (hO.fixW c hc).1)⟩
    · subst e; exact notIdW_field h.tcbs h.nodes hy (by omega)
    · exact notIdW_out h.nodes (h.omega _ hm) fun _ c hc =>
        ⟨fun e => hns (by rw [e]; exact hO.repW c hc), fun e => hns (by rw [e]; exact (hO.fixW c hc).1)⟩
    · subst e
      exact notIdW_out h.nodes (h.omega _ (hO.scW c hc _ hb (consW_in hO hc).2)) fun _ c' hc' => cons_ne_hdr hO hc hc'

/-- **[J] P1's `XferOK` at the states with `RS s s`** (p2j13): the message
transfer keeps the invariants, `XferFr` and `G`, from every state where `G`
and `RS s s` hold. P1's `XferOK` asks this at every `G` state; at `G = XG`
it is unguarded (`XG` lets every cap-slot word be rewritten) and its only
discharge, P1's `xferOK_of`, takes the vacuous `XferHyps`. Here `RS` is the
caller's relation, kept by `KW` writes (`hRSK`), which write no TCB cap slot;
so with an `RS` carrying the typing of the caps the transfer reads (the
receiver's IPC-buffer slot, the extra-cap and receive slots: P3's cap
relation) this premise is not refuted the way `XferHyps.buf_false` refutes
`XferHyps`. Discharge: from P3's cap relation in `RS` (P1 follow-up: restate
`xferOK_of` from such an `RS` instead of `XferHyps`). -/
def XferOKRS (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (RS : S → S → Prop)
    (G : S → Prop) : Prop :=
  ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s : S) (a : A) (snd ep badge : U64)
    (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
    SchedQueuesInvX st T Cs Ω H X s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s →
    SCsOK st T Ω Sg Scs Z Ac s → SgOK st Ω Sg s → UserOK st T Cs Ω H U s → RS s s → G s →
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      SchedQueuesInvX st T Cs Ω H X s' Q R ∧ BoundInv st T Ac s' ∧ XInv st T Cs Ω Sg Rp Scs Nt Z s' ∧
      SCsOK st T Ω Sg Scs Z Ac s' ∧ SgOK st Ω Sg s' ∧ XferFr st T Rp s s' ∧ G s' ⦄

/-- `XG` with `RS` on the diagonal: the guard P1's `XferOK` gets from
`XferOKRS` (`xferOK_rs`). -/
abbrev XGR (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (P3Ok : S → Prop) (RS : S → S → Prop) (s : S) : Prop :=
  XG st T Cs Ω H Sg Scs Z P3Ok s ∧ RS s s

/-- **P1's `XferOK` at the guard `XGR`**, from `XferOKRS` and `XferFootOKC`
(the end's `RS s' s'` from `RS s s'` and `hRSK`). -/
theorem xferOK_rs {A : Type _} {ar : machine.Arch A} {RS : S → S → Prop}
    (hxr : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2) :
    XferOK st ar T Cs Ω H Sg Rp Scs Nt Z U (XGR st T Cs Ω H Sg Scs Z P3Ok RS) := by
  intro Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hG
  exact WP.spec_mono (WP.spec_and (hxr Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hG.2 hG.1)
    (hxw Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hG.2 hG.1)) fun s' hh =>
    ⟨hh.1.1, hh.1.2.1, hh.1.2.2.1, hh.1.2.2.2.1, hh.1.2.2.2.2.1, hh.1.2.2.2.2.2.1,
      hh.1.2.2.2.2.2.2, hRSK s s' s' hh.2.2 (WritesIn.refl s' _)⟩

/-- **A fault IPC's guard `XGR`** from `XG` and `RS` at its start (P1's
`XG.faultG`; the fault and the endpoint dequeue are `KW` steps). -/
theorem XGR.faultG {RS : S → S → Prop}
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    {s : S} {t : U64} {f : error.Fault} (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (hrs : RS s s)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t) :
    FaultG st H (XGR st T Cs Ω H Sg Scs Z P3Ok RS) s t f := by
  intro s1 e s2 e1 hH hst e2
  refine ⟨XG.faultG (f := f) hG h hU hc s1 e s2 e1 hH hst e2, ?_⟩
  have ht := hc.mem
  obtain ⟨⟨Q1, R1, q1⟩, -⟩ := (spec_at (faults.set_fault.blk s t f h ht hU hc) e1).1
  have F1 := spec_at (faults.set_fault.kw (Cs := Cs) (Sg := Sg) (Z := Z) (Scs := Scs) (Es := EH H) s t f
    h.1.choose_spec.choose_spec.tcbs ht) e1
  have F2 := spec_at (endpoint.ep_dequeue.head_kw (Cs := Cs) (Sg := Sg) (Z := Z) (Scs := Scs) q1 hH hst) e2
  exact hRSK s1 s1 s2 (hRSK s s s1 hrs F1) F2

/-- **A property `send_ipc` keeps**, `KWN` steps (P1 `send_ipc.footP` with `KW`
replaced by `KWN` and the transfer's start a `FootN` step): under `send_ipc.ipc`'s hypotheses, a
property `Pst` of the states that holds at the start, is kept by `KW` steps
(`hPK`) and holds after the message transfer from a state the receiver's
dequeue (a `KW` step from `s`) reached (`hxP`), holds at the end
(`send_ipc.foot`: `IpcFoot` from `s`; `send_ipc.xg`: `XG`). -/
theorem endpoint.send_ipc.footPN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {RS : S → S → Prop} (hxf : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2) (s : S) (a : A) (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) (hRS0 : RS s s)
    (hKt : t ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) (hdK : can_donate = true → ¬ Nd) (hKa : ActOut st T Kp s) (Pst : S → Prop)
    (hPK : ∀ s1 s2 : S, Pst s1 → FootDN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2 → Pst s2) (hP0 : Pst s)
    (hxP : ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s1 : S) (a : A) (snd ep badge : U64)
      (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
      SchedQueuesInvX st T Cs Ω H X s1 Q R → BoundInv st T Ac s1 → XInv st T Cs Ω Sg Rp Scs Nt Z s1 →
      SCsOK st T Ω Sg Scs Z Ac s1 → SgOK st Ω Sg s1 → UserOK st T Cs Ω H U s1 →
      FootN st Kp Nd T Cs Sg Scs Z (EH H) s s1 → XG st T Cs Ω H Sg Scs Z P3Ok s1 →
      ipc.do_ipc_transfer st ar s1 a snd ep badge grant rcv ⦃ s2 => Pst s2 ⦄) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => Pst s' ⦄ := by
  have hidle := hc.ni
  have hT := h.tcbs
  have ht := hc.mem
  have hta := hT t ht
  rcases ep_state3 h hH with e0 | e0 | e0
  · exact WP.spec_mono (endpoint.send_ipc.blockFootN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply can_donate t e h (fun _ => hc) hH (Or.inl e0) hKt (hdrΩ_of hX hSg.sub)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hPK _ _ hP0 hh.d
  · exact WP.spec_mono (endpoint.send_ipc.blockFootN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) ar s a blocking do_call badge
      can_grant can_grant_reply can_donate t e h (fun _ => hc) hH (Or.inr e0) hKt (hdrΩ_of hX hSg.sub)) fun r hh => by
        obtain ⟨s', a'⟩ := r; simp only [WP.uncurry'_pair] at hh ⊢; exact hPK _ _ hP0 hh.d
  -- a receiving endpoint
  obtain ⟨hdT, hbe, -, hds⟩ := ep_head h hH (Or.inr rfl) e0
  have hds := hds rfl
  set hd := (L.epQ s e).head with hhd
  have hdt : hd ≠ t := fun e' => hc.nb (by rw [← e', hds]; exact Or.inr (Or.inl rfl))
  have hdi : L.idleW s ≠ hd := fun e' => hB.idleNB (by rw [e', hds]; exact Or.inl (Or.inr (Or.inl rfl)))
  have hKd : hd ∉ Kp := fun hk => hKB hd hk (by rw [hds]; exact Or.inr (Or.inl rfl))
  have hdta := hT hd hdT
  unfold endpoint.send_ipc
  step with obj.Ep.state.spec as ⟨v, hv⟩
  have hv2 : v = 2#u64 := hv.trans e0
  rw [hv2]
  simp only [ep_idle_val, ep_send_val', show ¬ ((2#u64) = 0#u64) from by decide,
    show ¬ ((2#u64) = 1#u64) from by decide, ↓reduceIte]
  have hsub := hSg.sub
  step with endpoint.get_queue.spec as ⟨q, eq⟩
  subst eq
  have hdq := endpoint.ep_dequeue.inv s hd Q R h hdT (by simp) (Or.inr (Or.inl hds))
  rw [hbe] at hdq
  obtain ⟨E0, EQ0, hEW0⟩ := h.eps
  have heE0 : e ∈ E0 := (hEW0.2.2.2.2.2.2.2.1 e).2 (Or.inl hH)
  obtain ⟨hE0, hEN0, hq0⟩ := hEW0.1 e heE0
  have hdm : hd ∈ EQ0 e := by
    have := hEW0.2.2.2.2.1 hd hdT (by simp) (Or.inr (Or.inl hds)); rw [hbe] at this; exact this.2
  refine WP.spec_bind (WP.spec_and hdq (endpoint.ep_dequeue.foot s e hd (EQ0 e) hT hE0 hq0 hdm)) ?_
  rintro s1 ⟨⟨h1, f1, o1, n1, k1, c1, nc1⟩, w1⟩
  have F1 : FootN st Kp Nd T Cs Sg Scs Z (EH H) s s1 :=
    FootN.of' w1 (hk := AcK.of_eq (EpFoot.act hT h.nodes h.cur hq0.mem hE0 hEN0 w1)) fun b _ hb => EpFoot.kwN hT h.nodes hq0.mem (Or.inl hH) hE0 hEN0 (hEW0.2.2.1 e heE0) (hdrΩ_of hX hSg.sub) hb
  obtain ⟨hB1, hX1, hS1, hSg1, ea1, ec1, ei1⟩ := frame_bx h hB hX hS hSg f1 o1 n1 k1
    (TmFr.mk0 ⟨k1, fun y hy K a b c => f1 y hy K (by omega) c (by omega) (by omega),
      fun c hc o ho => nc1 c hc o (by omega) (by omega), fun n' hn' => o1 _ (hSg.sub _ (hX.1.ntB n' hn').2)⟩)
  refine WP.spec_bind (WP.spec_and (hxf _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1)
      (hRSK s s s1 hRS0 F1.foot) (hG.foot F1.foot))
    (hxP _ _ _ _ s1 a t e badge can_grant hd ht hdT h1 hB1 hX1 hS1 hSg1 (hU.ksb k1) F1 (hG.foot F1.foot))) ?_
  rintro s2 ⟨⟨h2, hB2, hX2, hS2, hSg2, ⟨ea2, ec2, ei2, ecs2, f2, o2, -⟩, -⟩, F2⟩
  have F : ∀ y ∈ T, ∀ K : U64, 3328 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s2 (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K) :=
    fun y hy K h0 hK hK8 h1' h2' => (f2 y hy K h0 hK hK8).trans (f1 y hy K hK hK8 h1' h2')
  have Fst : ∀ y ∈ T, L.mem s2 (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Frp : ∀ y ∈ T, L.mem s2 (replyA y) = L.mem s (replyA y) := fun y hy =>
    F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fiq : ∀ y ∈ T, L.mem s2 (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have Fsc : ∀ y ∈ T, L.mem s2 (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact F y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea2' : L.actionW s2 = L.actionW s := ea2.trans ea1
  have ei2' : L.idleW s2 = L.idleW s := ei2.trans ei1
  have Ka2 : ActOut st T Kp s2 := hKa.step (AcK.of_eq ea2')
  step with obj.Tcb.reply_obj.spec as ⟨i, ei⟩
  have hds2 : L.mem s2 (stA hd) = sched.TS_BLOCKED_ON_RECV := (Fst hd hdT).trans hds
  -- the reply object leaves the receiver
  refine WP.spec_bind (Pₘ := fun s3 => ∃ X3 : Set U64, SchedQueuesInvX st T Cs Ω H X3 s3 Q R ∧ BoundInv st T Ac s3 ∧
      XInv st T Cs Ω Sg Rp Scs Nt Z s3 ∧ SCsOK st T Ω Sg Scs Z Ac s3 ∧ SgOK st Ω Sg s3 ∧ ExcT X3 hd ∧
      (hd ∈ X3 ∨ ¬ Blocked (L.mem s3 (stA hd))) ∧ ¬ Runnable (L.mem s3 (stA hd)) ∧
      (hd ∈ X3 → L.mem s3 (replyA hd) = 0#u64) ∧ (hd ∉ X3 → L.mem s3 (stA hd) = sched.TS_INACTIVE) ∧
      ((i != 0#u64) = true → hd ∉ X3 ∧ i ∈ Rp ∧ L.mem s3 (rTcbA i) = 0#u64) ∧
      L.mem s3 (stA t) = L.mem s (stA t) ∧ L.mem s3 (inqA t) = L.mem s (inqA t) ∧
      L.mem s3 (scA t) = L.mem s (scA t) ∧ L.actionW s3 ≠ t ∧ L.idleW s3 = L.idleW s ∧
      L.mem s3 (scA hd) = L.mem s (scA hd) ∧ Pst s3 ∧ ActOut st T Kp s3) ?_ ?_
  · split
    · rename_i hi
      have hi0 : i ≠ 0#u64 := by simpa using hi
      obtain ⟨hiR, hit⟩ := hX2.2.1.recv hd hdT hds2 (by rw [← ei]; exact hi0)
      rw [← ei] at hiR hit
      refine WP.spec_mono (WP.spec_and (ipc.reply_unlink.inv s2 i hd Q R h2 hdT hX2.1 hsub hiR hit
        (by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl))) (Or.inl (Or.inr rfl)))
        (ipc.reply_unlink.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s2 i hd h2 hX2 hsub hiR hdT hKd)) fun s3 hh' => ?_
      obtain ⟨hh, fu⟩ := hh'
      obtain ⟨h3, e3, k3, z3⟩ := hh
      have hclr : ∀ r ∈ Rp, L.mem s2 (rTcbA r) = hd → L.mem s3 (rTcbA r) = 0#u64 := by
        intro r hr er
        obtain ⟨-, -, b2, -⟩ := hX2.2.1.back r hr (by rw [er]; exact fun e0 => hdta.ne0 (by rw [e0]; rfl))
        rw [er, ← ei] at b2; rw [← b2]; exact z3
      refine ⟨_, h3, hB2.keepT h2 k3 (by rw [e3]; exact not_blocked_inactive) (by rw [e3]; exact inactive_ne.1),
        hX2.keepT k3 (by rw [e3]; exact inactive_ne) hclr, hS2.keepT hX2 k3,
        ⟨hsub, fun b hb => by rw [k3.ksb]; exact hSg2.ks b hb, fun o h1' h2' => by rw [k3.ksb]; exact hSg2.ksΩ o h1' h2'⟩,
        fun y hy => ?_, Or.inr (by rw [e3]; exact not_blocked_inactive), by rw [e3]; exact not_runnable_inactive,
        fun hm => absurd rfl hm.2, fun _ => e3, fun _ => ⟨fun hm => hm.2 rfl, hiR, z3⟩,
        (k3.stf ht (Ne.symm hdt)).trans (Fst t ht), (k3.inqf ht).trans (Fiq t ht), (k3.scf ht).trans (Fsc t ht),
        ?_, k3.idleW.trans ei2', (k3.scf hdT).trans (Fsc hd hdT), hPK _ _ F2 fu.d, fu.out Ka2⟩
      · obtain ⟨hy1, hy2⟩ := hy
        rcases hy1 with hy1 | hy1
        · exact absurd hy1 (Set.notMem_empty _)
        · exact absurd hy1 hy2
      · rcases k3.act with e' | e'
        · rw [e', ea2']; exact hc.na
        · rw [e']; exact fun e2 => notT_small hT (by simp) (e2 ▸ ht)
    · rename_i hi
      have hi0 : i = 0#u64 := by simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hi; exact hi
      refine (WP.spec_ok _).2 ⟨_, h2, hB2, hX2, hS2, hSg2, fun y hy => by simpa using hy, Or.inl (Or.inr rfl),
        by rw [hds2]; exact blocked_not_runnable (Or.inr (Or.inl rfl)), fun _ => by rw [← ei, hi0],
        fun hm => absurd (Or.inr rfl) hm, fun hi' => absurd hi0 (by simpa using hi'),
        Fst t ht, Fiq t ht, Fsc t ht, by rw [ea2']; exact hc.na, ei2', Fsc hd hdT, F2, Ka2⟩
  rintro s3 ⟨X3, h3, hB3, hX3, hS3, hSg3, hXc3, hx3, hnr3, hz3, hin3, hpu3, st3, iq3, sc3, na3, ei3, shd3, F3, Ka3⟩
  have hdA3 : L.mem s3 (scA hd) ≠ 0#u64 → L.mem s3 (scA hd) ∈ Ac := fun h0 => by
    rw [shd3] at h0 ⊢
    exact hB.sact hd hdT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hds]; exact Or.inr (Or.inl rfl))))))))
      h0
  have htA3 : L.mem s3 (scA t) ≠ 0#u64 → L.mem s3 (scA t) ∈ Ac := fun h0 => by
    rw [sc3] at h0 ⊢; exact hc.ac h0
  have htq3 : (L.mem s3 (inqA t) &&& sched.Q_QUEUED) = 0#u64 := by rw [iq3]; exact hc.nq
  have htr3 : (L.mem s3 (inqA t) &&& sched.Q_RELEASE) = 0#u64 := by rw [iq3]; exact hc.nr
  have hnb3 : ¬ Blocked (L.mem s3 (stA t)) := by rw [st3]; exact hc.nb
  have hnrp3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY := by rw [st3]; exact hc.nrp
  have hcold3 : L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_REPLY ∧ L.mem s3 (stA t) ≠ sched.TS_BLOCKED_ON_RECV :=
    ⟨hnrp3, fun e' => hnb3 (Or.inr (Or.inl e'))⟩
  obtain ⟨dq, dr, da⟩ := blocked_out h3 hdT hnr3
  have hidle3 : L.idleW s3 ≠ t := by rw [ei3]; exact hidle
  have hnt3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ t := hX3.noref hta hcold3.1 hcold3.2
  have hnd3 : ∀ r ∈ Rp, L.mem s3 (rTcbA r) ≠ hd := by
    by_cases hm : hd ∈ X3
    · exact hX3.noref0 hdta (hz3 hm)
    · have e' := hin3 hm
      exact hX3.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
  refine WP.spec_bind (Pₘ := fun r : S × A => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1) ?_ ?_
  rotate_left
  · rintro ⟨s4, a1⟩ ⟨X4, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc4, hx4, hnr4, hdA4, f4⟩
    try simp only [WP.uncurry'_pair]
    refine WP.spec_mono (send_tail.footN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s4 a1 hd Q4 R4 h4 hB4 hX4 hS4
      hSg4 hdT hXc4 hx4 hnr4 hdA4 hKd (f4.out Ka3)) fun r hr => ?_
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact hPK _ _ F3 (f4.trans hr.d)
  have Ppush : (i != 0#u64) = true → ipc.reply_push st ar s3 a t hd i can_donate ⦃ r => ∃ X4 : Set U64,
      (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hi
    obtain ⟨hdX, hiR, hiz⟩ := hpu3 hi
    have hi0 : i ≠ 0#u64 := by simpa using hi
    refine WP.spec_mono (WP.spec_and (ipc.reply_push.ipc hA s3 a t hd i can_donate Q R h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT hdt dq dr da (by rw [ei3]; exact hdi) htA3)
      (ipc.reply_push.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a t hd i can_donate h3
      (fun y hy => absurd (hXc3 y hy ▸ hy) hdX) (Or.inr hnb3) hB3 hX3 hS3 hSg3 ht htq3 htr3 na3 hidle3 hcold3
      hiR hi0 hiz hdT htA3 hKt hdK Ka3)) fun r hh' => ?_
    obtain ⟨s4, a4⟩ := r
    simp only [WP.uncurry'_pair] at hh'
    obtain ⟨hh, fk⟩ := hh'
    obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, sc4⟩ := hh
    have e4 : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT hdt).trans (hin3 hdX)
    exact ⟨∅, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, fun y hy => absurd hy (Set.notMem_empty _),
      Or.inr (by rw [e4]; exact not_blocked_inactive),
      hX4.noref hdta (by rw [e4]; exact inactive_ne.1) (by rw [e4]; exact inactive_ne.2), fun h0 => by
        rcases sc4 with e | e
        · rw [e] at h0 ⊢; exact hdA3 h0
        · rw [e] at h0 ⊢; exact htA3 h0, fk⟩
  have Pinact : (do
      let s5 ← sched.set_thread_state st s3 t sched.TS_INACTIVE
      ok (s5, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    refine WP.spec_bind (WP.spec_and (sts_all s3 t _ Q R h3 hB3 hX3 hS3 hSg3 ht not_blocked_inactive inactive_ne (Or.inr hnb3)
      hnt3 ⟨fun c hc' p hp hm => absurd hm (h3.notQ ht htq3 hc' hp), fun c hc' hm => absurd hm (h3.notR ht htr3 hc'),
        fun e' => absurd e' na3⟩)
      (sched.set_thread_state.kwN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s3 t _ h3 ht hKt)) fun s4 hh' => ?_
    obtain ⟨hh, fk⟩ := hh'
    obtain ⟨h4, hB4, hX4, hS4, hSg4, -, k4⟩ := hh
    refine (WP.spec_ok _).2 ⟨{y | y ∈ X3 ∧ y ≠ t}, ⟨Q, R, h4⟩, hB4, hX4, hS4, hSg4,
      fun y hy => hXc3 y hy.1, ?_, fun r hr => ?_, fun h0 => by rw [k4.scf hdT] at h0 ⊢; exact hdA3 h0, fk.d⟩
    · rcases hx3 with hm | hnb
      · exact Or.inl ⟨hm, hdt⟩
      · exact Or.inr (by rw [k4.stf hdT hdt]; exact hnb)
    · rcases k4.rtcb r hr with e' | ⟨-, e'⟩
      · rw [e']; exact hnd3 r hr
      · rw [e']; exact fun e2 => hdta.ne0 (by rw [← e2]; rfl)
  have Pok : (ok (s3, a) : Result (S × A)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ :=
    (WP.spec_ok _).2 ⟨X3, ⟨Q, R, h3⟩, hB3, hX3, hS3, hSg3, hXc3, hx3, hnd3, hdA3, FootDN.refl _⟩
  have Pdon : can_donate = true → (do
      let i2 ← obj.Tcb.sc st hd s3
      if i2 = 0#u64 then do
          let i3 ← obj.Tcb.sc st t s3
          schedcontext.donate st ar s3 a i3 hd
        else ok (s3, a)) ⦃ r => ∃ X4 : Set U64, (∃ Q4 R4, SchedQueuesInvX st T Cs Ω H X4 r.1 Q4 R4) ∧
      BoundInv st T Ac r.1 ∧ XInv st T Cs Ω Sg Rp Scs Nt Z r.1 ∧ SCsOK st T Ω Sg Scs Z Ac r.1 ∧ SgOK st Ω Sg r.1 ∧
      ExcT X4 hd ∧ (hd ∈ X4 ∨ ¬ Blocked (L.mem r.1 (stA hd))) ∧ (∀ r' ∈ Rp, L.mem r.1 (rTcbA r') ≠ hd) ∧
      (L.mem r.1 (scA hd) ≠ 0#u64 → L.mem r.1 (scA hd) ∈ Ac) ∧
      FootDN st Kp Nd T Cs Sg Scs Z (EH H) s3 r.1 ⦄ := by
    intro hcd
    step with obj.Tcb.sc.spec as ⟨i2, ei2⟩
    split
    · rename_i hi2
      step with obj.Tcb.sc.spec as ⟨i3, ei3'⟩
      have hsc0 : L.mem s3 (scA t) ≠ 0#u64 := by rw [sc3]; exact hdon hcd
      obtain ⟨hiS, hitc, -⟩ := hX3.2.2.bound t ht hsc0
      rw [← ei3'] at hiS hitc
      refine WP.spec_mono (WP.spec_and (schedcontext.donate.ipc hA s3 a i3 hd t Q R h3 hB3 hX3 hS3 hSg3 ht ei3'.symm
        (by rw [ei3', sc3]; exact hdon hcd) ⟨htq3, htr3, na3⟩ hidle3 hdT (by rw [← ei2, hi2]) dq dr da hdt
        (by rw [ei3']; exact htA3 (by rw [sc3]; exact hdon hcd)) (by rw [ei3]; exact hdi))
        (schedcontext.donate.kwIN (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) hA s3 a i3 hd h3 hX3.1 hSg3.sub
          hX3.dbg (hX3.2.2.core i3 hiS) hiS hdT (hdK hcd) Ka3 fun _ => by rw [hitc]; exact ⟨ht, htq3, htr3⟩))
        fun r hh' => ?_
      obtain ⟨s4, a4⟩ := r
      simp only [WP.uncurry'_pair] at hh'
      obtain ⟨hh, fk⟩ := hh'
      obtain ⟨⟨⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4⟩, st4, rp4, sd4⟩ := hh
      refine ⟨X3, ⟨Q4, R4, h4⟩, hB4, hX4, hS4, hSg4, hXc3, ?_, ?_,
        fun _ => by rw [sd4, ei3']; exact htA3 (by rw [sc3]; exact hdon hcd), fk⟩
      · rcases hx3 with hm | hnb
        · exact Or.inl hm
        · exact Or.inr (by rw [st4 hd hdT]; exact hnb)
      · by_cases hm : hd ∈ X3
        · exact hX4.noref0 hdta (by rw [rp4 hd hdT]; exact hz3 hm)
        · have e' : L.mem s4 (stA hd) = sched.TS_INACTIVE := (st4 hd hdT).trans (hin3 hm)
          exact hX4.noref hdta (by rw [e']; exact inactive_ne.1) (by rw [e']; exact inactive_ne.2)
    · exact Pok
  split
  · repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush (by assumption)
  · step with obj.Tcb.fault_type.any as ⟨i1, _⟩
    repeat' split
    all_goals first
      | exact Pinact
      | exact Ppush (by assumption)
      | exact Pdon (by assumption)
      | exact Pok



/-- A `KWN`/`IpcWN` footprint keeps the `STATE` of the protected threads. -/
theorem IpcFootN.stK {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') (hT : TcbPlaced T) {y : U64}
    (hyT : y ∈ T) (hy : y ∈ Kp) : L.mem s' (stA y) = L.mem s (stA y) :=
  f.idKeep (by rw [stA_eq]; exact field_aligned (hT y hyT) (by simp) (by simp))
    (Or.inr (Or.inl ⟨y, hyT, hT y hyT, hy, Or.inl rfl⟩))

/-- … and their `IN_QUEUES`. -/
theorem IpcFootN.iqK {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') (hT : TcbPlaced T) {y : U64}
    (hyT : y ∈ T) (hy : y ∈ Kp) : L.mem s' (inqA y) = L.mem s (inqA y) :=
  f.idKeep (by rw [inqA_eq]; exact field_aligned (hT y hyT) (by simp) (by simp))
    (Or.inr (Or.inl ⟨y, hyT, hT y hyT, hy, Or.inr rfl⟩))

/-- In no-donation mode an `IpcWN` footprint keeps the current thread. -/
theorem IpcFootN.curK {s s' : S} (f : IpcFootN st Kp Nd T Cs Ω Sg Scs Z Es U s s') (hNd : Nd)
    (NP : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) : L.curW s' = L.curW s := by
  unfold LawfulStore.curW
  rw [nodeAt_of_ksb f.1, f.2.1]
  exact f.idKeep (nodeAt_aligned NP (by rw [curth0]; omega) (by rw [curth0]))
    (Or.inl ⟨_, hc, _, Or.inr (Or.inr (Or.inr ⟨hNd, rfl, by rw [curth0]⟩)), rfl⟩)

/-- **`send_ipc`'s footprint in `IpcWN`** (P1 `send_ipc.foot`). -/
theorem endpoint.send_ipc.footN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {RS : S → S → Prop} (hxf : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok)) (s : S) (a : A)
    (blocking do_call : Bool)
    (badge : U64) (can_grant can_grant_reply can_donate : Bool) (t e : U64)
    (Q : U64 → U64 → List U64) (R : U64 → List U64)
    (h : SchedQueuesInv st T Cs Ω H s Q R) (hB : BoundInv st T Ac s) (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s)
    (hS : SCsOK st T Ω Sg Scs Z Ac s) (hSg : SgOK st Ω Sg s) (hU : UserOK st T Cs Ω H U s)
    (hc : CanBlock st T Ac s t) (hdon : can_donate = true → L.mem s (scA t) ≠ 0#u64)
    (hH : H e = some .ep) (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKt : t ∉ Kp) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y))) (hdK : can_donate = true → ¬ Nd)
    (hKa : ActOut st T Kp s) :
    endpoint.send_ipc st ar s a blocking do_call badge can_grant can_grant_reply can_donate t e
      ⦃ s' _ => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s' ∧ XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ :=
  endpoint.send_ipc.footPN hA hxf hRSK s a blocking do_call badge can_grant can_grant_reply can_donate t e Q R h hB hX hS
    hSg hU hc hdon hH hG hRS0 hKt hKB hdK hKa
    (fun s' => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s' ∧ XG st T Cs Ω H Sg Scs Z P3Ok s')
    (fun _ _ p f => ⟨IpcFootN.trans p.1 (FootDN.ipc f), XG.footD p.2 (FootDN.footD f)⟩) ⟨IpcFootN.refl s, hG⟩
    fun Ac' X Q' R' s1 a' snd ep badge' grant rcv hs hr h1 hB1 hX1 hS1 hSg1 hU1 F1 hG1 =>
      WP.spec_mono (WP.spec_and (hxw Ac' X Q' R' s1 a' snd ep badge' grant rcv hs hr h1 hB1 hX1 hS1 hSg1 hU1
        (hRSK s s s1 hRS0 F1.foot) hG1) (hxf Ac' X Q' R' s1 a' snd ep badge' grant rcv hs hr h1 hB1 hX1 hS1 hSg1 hU1
        (hRSK s s s1 hRS0 F1.foot) hG1))
        fun s2 hh => ⟨(FootN.ipc F1).trans (XferWC.ipcN h1 hX1 hU1 hSg1.sub hh.1.1), hh.2.2.2.2.2.2.2⟩

/-- **A timeout fault's footprint in `IpcWN`** (P1 `handle_timeout.foot`). -/
theorem faults.handle_timeout.footN {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {U : Set U64}
    {RS : S → S → Prop} (hxf : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok)) {Ac : Set U64} (s : S) (a : A)
    (t : obj.Tcb) (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : UserOK st T Cs Ω H U s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hRS0 : RS s s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s)
    (hKt : t ∉ Kp) (hKT : ∀ y ∈ Kp, y ∈ T) (hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)))
    (hKa : ActOut st T Kp s) :
    faults.handle_timeout st ar s a t f ⦃ s' _ => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s s' ∧
      XG st T Cs Ω H Sg Scs Z P3Ok s' ⦄ := by
  have ht := hc.mem
  unfold faults.handle_timeout
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s r.2.1 ∧
      XG st T Cs Ω H Sg Scs Z P3Ok r.2.1) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨IpcFootN.refl s, hG⟩ | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    have q0 := h.1.choose_spec.choose_spec
    refine WP.spec_bind (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.kwN (Cs := Cs) (Sg := Sg) (Kp := Kp) (Nd := Nd) (Scs := Scs) (Z := Z) (Es := EH H) s t f q0.tcbs q0.nodes q0.cur ht)) ?_
    rintro s1 ⟨⟨h1, hU1, hc1⟩, F1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.footN (Nd := Nd) hA hxf hxw s1 a true false b g gr false t p Q1 R1 q1 hB1 hX1 hS1
      hSg1 hU1 hc1 (fun e => by cases e) hpH hRSK (hRSK s s s1 hRS0 F1.foot) (hG.foot F1.foot) hKt
      (fun y hy => by
        rw [IpcFootN.stK (Ω := Ω) (U := U) (Es := EH H) (FootN.ipc F1) q0.tcbs (hKT y hy) hy]; exact hKB y hy)
      (fun e => by cases e) (F1.out hKa)) ?_
    rintro ⟨s2, a1⟩ h2
    try simp only [WP.uncurry'_pair] at h2
    exact (WP.spec_ok _).2 ⟨(FootN.ipc F1).trans h2.1, h2.2⟩
  · rintro ⟨x, s2, a2⟩ h2
    exact (WP.spec_ok _).2 h2

/-- The states a budget check from `s0` passes: `XG` states reached by an
`IpcWN` footprint. -/
def GN (st : machine.Store S) [L : LawfulStore st] (Kp : Set U64) (Nd : Prop) (T Cs Ω : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) (s0 s : S) : Prop :=
  XG st T Cs Ω H Sg Scs Z P3Ok s ∧ IpcFootN st Kp Nd T Cs Ω Sg Scs Z (EH H) U s0 s

/-- `GN s0` is kept by `KWN` steps. -/
theorem GN.foot {s0 s1 s2 : S} (g : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s1)
    (f : FootN st Kp Nd T Cs Sg Scs Z (EH H) s1 s2) : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s2 :=
  ⟨g.1.foot f.foot, g.2.trans (FootN.ipc f)⟩

theorem GN.refl {s0 : S} (g : XG st T Cs Ω H Sg Scs Z P3Ok s0) : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s0 :=
  ⟨g, IpcFootN.refl s0⟩

/-- At `GN s0` states the action and the current thread stay unprotected. -/
theorem GN.out {s0 s : S} (g : GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0 s) (hNd : Nd)
    (NP0 : NodePlaced st T s0 (L.cpu s0)) (hc0 : L.cpu s0 ∈ Cs) (hKa : ActOut st T Kp s0) (hKc : L.curW s0 ∉ Kp) :
    ActOut st T Kp s ∧ L.curW s ∉ Kp :=
  ⟨g.2.out hKa, by rw [g.2.curK hNd NP0 hc0]; exact hKc⟩

/-- **Timeout faults keep `GN s0`** (`TmoKC` from the budget check's start
`s1`, itself a `GN s0` state): the current thread can block (`CanBlock`) by
`CurOK` and its queue flag and idleness at `s1`, which `ChgW` writes keep.
Premises: the transfer (`XferOKRS` [J], `XferFootOKC` [J]), `RS` at `s1`
(P1's per-call `hRS0`), and the typing of the current thread's timeout
handler cap, `hcap` [P], at the states `ChgW` writes reach from `s1`. -/
theorem tmoKC_N {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {RS : S → S → Prop} (hxf : XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hxw : XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok))
    (hRSK : ∀ s0 s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (KW st T Cs Sg Scs Z (EH H) s1) → RS s2 s2)
    (hNd : Nd) (hKT : ∀ y ∈ Kp, y ∈ T)
    (Ac : Set U64) (s0 s1 : S) (hKc : L.curW s0 ∉ Kp) (hKB0 : ∀ y ∈ Kp, ¬ Blocked (L.mem s0 (stA y)))
    (NP0 : NodePlaced st T s0 (L.cpu s0)) (hc0 : L.cpu s0 ∈ Cs) (hKa0 : ActOut st T Kp s0)
    (h1 : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1) (hRS1 : RS s1 s1) (hU1 : UserOK st T Cs Ω H U s1)
    (hnq : (L.mem s1 (inqA (L.curW s1)) &&& sched.Q_QUEUED) = 0#u64) (hni : L.idleW s1 ≠ L.curW s1)
    (hcap : ∀ s : S, WritesIn st s1 s (ChgW st Scs Z s1) →
      obj.Tcb.slot (L.curW s) layout.tcb.SLOT_TIMEOUT_HANDLER ⦃ sl =>
        obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄) :
    TmoKC st ar T Cs Ω H Sg Rp Scs Nt Z Ac s1 (GN st Kp Nd T Cs Ω H Sg Scs Z U P3Ok s0) :=
  fun s a f Q R h hB hX hSg hS hw hok hG => by
    obtain ⟨⟨Q1, R1, q1⟩, -, hX1, -, -⟩ := h1
    have hKt : L.curW s ∉ Kp := by rw [hG.2.curK hNd NP0 hc0]; exact hKc
    have hKB : ∀ y ∈ Kp, ¬ Blocked (L.mem s (stA y)) := fun y hy => by
      rw [hG.2.stK h.tcbs (hKT y hy) hy]; exact hKB0 y hy
    have hk : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s := ⟨⟨Q, R, h⟩, hB, hX, hS, hSg⟩
    have c40 : layout.node.CONSUMED.val = 40 := by simp [layout.node.CONSUMED]
    have wF : WritesIn st s1 s (L.Free s1 Ω Cs) := hw.mono' fun b hb hh => by
      rcases hh with ⟨c, hc, hin⟩ | e
      · exact Or.inl (hX1.1.scW c hc b hb hin)
      · exact e ▸ free_cur_node q1.cur (by unfold LowFree; omega)
    obtain ⟨-, kc, ki, -⟩ := free_keys q1 wF
    have hcT := q1.curT
    have kq : L.mem s (inqA (L.curW s1)) = L.mem s1 (inqA (L.curW s1)) := by
      rw [inqA_eq]
      refine wF.mem_eq (field_aligned (q1.tcbs _ hcT) (by simp) (by simp)) ?_
      rintro (hm | ⟨c, hc, o, ho, e⟩)
      · exact out_ne_field (q1.omega _ hm) hcT (q1.tcbs _ hcT) (by simp) rfl
      · exact node_ne_field (q1.nodes c hc) (by simp only [LowFree] at ho; omega) hcT (q1.tcbs _ hcT) (by simp) e.symm
    have hrs : RS s s := hRSK s1 s1 s hRS1 (hw.mono fun b hh => by
      rcases hh with ⟨c, hc, hin⟩ | e
      · exact kw_sc hc hin
      · exact e ▸ kw_node q1.cur (by omega) (by omega))
    have hc : CanBlock st T Ac s (L.curW s) :=
      ⟨h.curT, fun hb => blocked_not_runnable hb hok.run, runnable_ne_reply hok.run,
        by rw [kc, kq]; exact hnq, hok.rel, hok.act, by rw [ki, kc]; exact hni,
        fun _ => (hS.act _ (hX.2.2.bound _ h.curT hok.bnd).1).2 hok.rmx⟩
    have hU : UserOK st T Cs Ω H U s := hU1.ksb hw.1
    refine WP.spec_mono (WP.spec_and (faults.handle_timeout.bxi hA (xferOK_rs hxf hxw hRSK) s a _ f
      (XGR.faultG hRSK hG.1 hrs hk hU hc) hk hU hc (hcap s hw))
      (faults.handle_timeout.footN (Nd := Nd) hA hxf hxw s a _ f hk hU hc (hcap s hw) hRSK
        hrs hG.1 hKt hKT hKB (hG.2.out hKa0))) ?_
    rintro ⟨s', a'⟩ hr
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨BlkOK.bxi hr.1, hr.2.2, hG.2.trans hr.2.1⟩

end

end Fl4Proofs.P1
