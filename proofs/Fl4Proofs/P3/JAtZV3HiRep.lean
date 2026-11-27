/-
P3 (line mmuAD, gen 41): **the caller's replies at `JAtZV3`** — FL4's success tail of `handle_invocation`
(`flTail`: `reply_success_empty` when called, then `TS_RUNNING`, for a still-`Restart` caller) and the in-decode
VCPU replies (`vcpu.reply`, one word; `vcpuReplyWs`, a word list), each against the spec's
`replyFromKernel (0, ms)` then `setThreadState .running` (`specTail` with the caller `Restart`, P3/XTopReply's
`specTail_data`).

* `zv_MrS_jMrSt`: P3/ReplyFailX's `MrS` is P3/XTopJointFault's `jMrSt`.
* `zv_setMr_ret`: `set_mr`'s returned length is `jMrRet pb (i + 1)` (XTopJointFault's `setMrJ` without the `MrJ`
  part).
* **`JAtZV3.replyWords3`**: `tcb.reply_words n` (badge 0, message info of length `n`) at `JAtZV3` from the spec's
  `set_mrs` state of the words `ms` to `replyStateB` (XTopJointData's `JAtZ.replyTailJ` with gen 33's
  `JAtZV3.regWr` in place of `JAtZ.regWrJ`).
* **`JAtZV3.wsLoop3`**: `vcpuReplyWsLoop` (P3/JAtZV3VDec) at `JAtZV3` along `jMrSt` (gen 34's `setMrJ3`), with the
  returned count.
* **`JAtZV3.flTail3`**: XTopJointReplyTail's `JAtZ.flTailJ` at `JAtZV3` (`runJ`, `replyWords3` with no words).
* **`JAtZV3.replyWsRun3`**: `vcpuReplyWs ct call ws` from a `Running` caller (`wsLoop3`, `replyWords3`, `runRJ`).
* **`JAtZV3.vreply3`**: `vcpu.reply call y` from a `Running` caller (`setMrJ3` of MR0, `replyWords3` with length 1,
  `runRJ`).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3HiRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

theorem zv_MrS_jMrSt (σ0 : Fl4Spec.State Unit) (t : Fl4Spec.ObjRef) (x : Fl4Spec.Tcb) (pb : Option Fl4Spec.ObjRef)
    (ms : List Fl4Spec.Word) : MrS σ0 t x pb ms = jMrSt σ0 t x pb ms := by
  cases pb <;> rfl

theorem zv_jMrRet_mrLen (pb : Option Fl4Spec.ObjRef) (n : Nat) : jMrRet pb n = mrLen pb n := by
  cases pb <;> simp only [jMrRet, mrLen] <;> omega

/-- **`set_mr`'s returned length** (module docstring). -/
theorem zv_setMr_ret {B : Set (U64 × Fl4Spec.Word)} {rcv rw : U64} {pb : Option Fl4Spec.ObjRef} (hb : JBufR B rw pb)
    (s : S) (i v : U64) (hi : i.val < 120) :
    msg.set_mr st s rcv rw i v ⦃ r => r.1.val = jMrRet pb (i.val + 1) ⦄ := by
  have hN : msg.N_MSG_REGISTERS.val = 4 := by unfold msg.N_MSG_REGISTERS; rfl
  unfold msg.set_mr
  by_cases h4 : i < msg.N_MSG_REGISTERS
  · have hi4 : i.val < 4 := by have := (P1.gt_iff_val).1 h4; omega
    simp only [h4, ↓reduceIte]
    refine WP.spec_bind (Endp.msg_register_spec i hi4) ?_
    rintro r rfl
    refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s rcv _ v) ?_
    rintro s1 rfl
    unfold lift
    apply ok_bind_spec
    simp only [WP.spec_ok]
    have e : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [e]; cases pb <;> simp only [jMrRet] <;> omega
  · have hi4 : 4 ≤ i.val := by
      have : ¬ i.val < 4 := fun h' => h4 ((P1.gt_iff_val).2 (by rw [hN]; exact h')); omega
    rw [if_neg h4]
    cases pb with
    | none =>
      have hb' : rw = 0#u64 := hb
      subst hb'
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      rw [hN]; simp only [jMrRet]; omega
    | some p =>
      obtain ⟨hrw0, -, -⟩ := hb
      have hb1 : (rw != 0#u64) = true := by simp [hrw0]
      simp only [hb1, ↓reduceIte]
      unfold lift
      apply ok_bind_spec
      refine WP.spec_bind (Endp.msg.buf_set.spec s rw _ v) ?_
      rintro s1 rfl
      apply ok_bind_spec
      simp only [WP.spec_ok]
      have hiv : (core.num.U64.wrapping_add i 1#u64).val = i.val + 1 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      rw [hiv]; simp only [jMrRet]

set_option maxHeartbeats 4000000 in
/-- **`reply_words` at `JAtZV3`** (module docstring). -/
theorem JAtZV3.replyWords3 {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef}
    {ms : List Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 buf ms)) (hct : ct ∈ Z.T)
    (n : U64) (hn : n.val = mrLen buf ms.length) (hn128 : n.val < 128) :
    tcb.reply_words st s ct n ⦃ s4 =>
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s4 a (replyStateB σ0 ct.bv x0 buf ms) ⦄ := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  unfold tcb.reply_words
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  have J1 := J.regWr hct hkx Fl4Spec.badge_register 0#u64
  rw [Endp.regIdx_badge] at J1
  rw [mrS_setReg σ0 ct.bv x0 buf ms badge_not_mr] at J1
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J1
  set xA := Notif.setReg x0 Fl4Spec.badge_register 0
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_mono (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s2 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have hkA := MrS_kheap_t (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms
  have J2 := J1.regWr hct hkA Fl4Spec.msg_info_register v
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen buf ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  have eR : Notif.updK (MrS (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms) ct.bv
      (.tcb (Notif.setReg (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))
        Fl4Spec.msg_info_register v.bv)) = replyStateB σ0 ct.bv x0 buf ms := by
    unfold replyStateB; rw [hvd]
  rw [eR] at J2
  exact J2

theorem zv_jMrRet_le (pb : Option Fl4Spec.ObjRef) (n : Nat) : jMrRet pb n ≤ n := by
  cases pb <;> simp only [jMrRet] <;> omega

set_option maxHeartbeats 4000000 in
/-- **The word loop at `JAtZV3`** (module docstring). -/
theorem JAtZV3.wsLoop3 {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {pb : Option Fl4Spec.ObjRef}
    (hct : ct ∈ Z.T) (hq : ∀ p, pb = some p → Endp.ipcBufOf true x0 = some p) {b : U64} (hb : JBufR Z.B b pb) :
    ∀ (ws : List U64) (ms : List Fl4Spec.Word) (s : S) (i n : U64),
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ0 ct.bv x0 pb ms) → i.val = ms.length →
      n.val = jMrRet pb ms.length → ms.length + ws.length ≤ 120 →
      vcpuReplyWsLoop st ct b s ws i n ⦃ r =>
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D r.1 a (jMrSt σ0 ct.bv x0 pb (ms ++ ws.map (·.bv))) ∧
        r.2.val = jMrRet pb (ms.length + ws.length) ⦄
  | [], ms, s, i, n, J, _, hn, _ => by
    rw [vcpuReplyWsLoop_nil, WP.spec_ok]
    simp only [List.map_nil, List.append_nil, List.length_nil, Nat.add_zero]
    exact ⟨J, hn⟩
  | w :: ws, ms, s, i, n, J, hi, hn, hl => by
    simp only [List.length_cons] at hl
    rw [vcpuReplyWsLoop_cons]
    refine WP.spec_bind (WP.spec_and (setMrJ3 J hct hq hb i (by omega) (by omega) w)
      (zv_setMr_ret hb s i w (by omega))) ?_
    rintro ⟨n1, s1⟩ ⟨J1, hn1⟩
    try simp only [uncurry_apply_pair]
    simp only at J1 hn1
    have em : mrUpd ms i.val w.bv = ms ++ [w.bv] := by unfold mrUpd; rw [if_neg (by omega)]
    rw [em] at J1
    obtain ⟨i2, h2e, h2v⟩ := P1.spec_ex_fd (U64.add_spec (x := i) (y := 1#u64) (by scalar_tac))
    rw [h2e, bind_ok]
    have hi2 : i2.val = i.val + 1 := by simpa using h2v
    refine WP.spec_mono (JAtZV3.wsLoop3 hct hq hb ws (ms ++ [w.bv]) s1 i2 n1 J1
      (by simp; omega) (by rw [hn1, hi]; simp) (by simp; omega)) ?_
    rintro r ⟨Jr, hr⟩
    refine ⟨?_, ?_⟩
    · simpa [List.append_assoc] using Jr
    · rw [hr]; simp only [List.length_append, List.length_cons, List.length_nil]; congr 1; omega

/-- FL4's `flTail` does nothing when the caller is not `Restart` (its state word, by `IRel`). -/
theorem JAtZV3.flTailNo (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState ≠ .restart) (call : Bool) :
    flTail (st := st) ct call s a ⦃ res => res = (.Ok (), s, a) ⦄ := by
  have B := J.z2.zv.base
  have hI := B.xtop.irelK B.ks B.buf
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct hct
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA ct)).val = tsCode x.tcbState := hTR.st
  have hss : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by rw [P1.stA_eq, ← tStA_eq, hst]
  unfold flTail
  refine WP.spec_bind (tcb_state_spec' (st := st) s ct) ?_
  rintro i rfl
  have hr : L.mem s (stA ct) ≠ sched.TS_RESTART := by
    intro h
    apply hrs
    apply tsCode_two
    rw [← hss]
    show (L.mem s (stA ct)).val = 2
    rw [h]; unfold sched.TS_RESTART; rfl
  rw [if_neg hr, WP.spec_ok]

set_option maxHeartbeats 4000000 in
/-- **FL4's success tail for an empty result at `JAtZV3`** (module docstring; XTopJointReplyTail's
`JAtZ.flTailJ`). -/
theorem JAtZV3.flTail3 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (call : Bool) :
    flTail (st := st) ct call s a ⦃ res => res.1 = .Ok () ∧
      ∃ z ∈ (specTail call ct.bv [] σ).1, ∃ Lst' : U64 → List U64,
        JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D res.2.1 res.2.2 z.2 ⦄ := by
  have B := J.z2.zv.base
  have hI := B.xtop.irelK B.ks B.buf
  obtain ⟨x0, hk0, hTR⟩ := hI.1.tcb ct hct
  rw [hk] at hk0; cases hk0
  have hst : (L.mem s (tStA ct)).val = tsCode x.tcbState := hTR.st
  have hss : (L.mem s (P1.stA ct)).val = tsCode x.tcbState := by rw [P1.stA_eq, ← tStA_eq, hst]
  by_cases hrs : x.tcbState = .restart
  · unfold flTail
    refine WP.spec_bind (tcb_state_spec' (st := st) s ct) ?_
    rintro i rfl
    have hr : L.mem s (stA ct) = sched.TS_RESTART := by
      apply UScalar.eq_of_val_eq
      show (L.mem s (P1.stA ct)).val = _
      rw [hss, hrs]; unfold sched.TS_RESTART; rfl
    rw [if_pos hr]
    cases call
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
      refine WP.spec_bind (J.runJ hct hk hrs) ?_
      rintro s2 ⟨Lst', J2⟩
      refine (WP.spec_ok _).2 ⟨rfl, ((), stsAct (updK σ ct.bv (.tcb { x with tcbState := .running })) ct.bv), ?_,
        Lst', J2⟩
      rw [specTail_nil hk false, if_pos hrs]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Notif.setThreadState_eq .running hk]; exact Set.mem_singleton _
    · simp only [↓reduceIte]
      have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (MrS σ ct.bv x (Endp.ipcBufOf true x) []) := by
        rw [MrS_nil hk]; exact J
      have e : msg.reply_success_empty st s ct = tcb.reply_words st s ct 0#u64 := by
        unfold msg.reply_success_empty tcb.reply_words; rfl
      rw [e]
      refine WP.spec_bind (J0.replyWords3 hct 0#u64 (by cases Endp.ipcBufOf true x <;> rfl) (by decide)) ?_
      intro s4 J4
      refine WP.spec_bind (J4.runJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs])) ?_
      rintro s5 ⟨Lst', J5⟩
      refine (WP.spec_ok _).2 ⟨rfl, ((), stsAct (updK (replyStateB σ ct.bv x (Endp.ipcBufOf true x) []) ct.bv
        (.tcb { replyTcbB x (Endp.ipcBufOf true x) [] with tcbState := .running })) ct.bv), ?_, Lst', J5⟩
      rw [specTail_data hk hrs [] (by simp) (fun p _ z hz => by simp [Endp.mrPairs] at hz)]
      exact Set.mem_singleton _
  · refine WP.spec_mono (J.flTailNo hct hk hrs call) ?_
    rintro res rfl
    refine ⟨rfl, ((), σ), ?_, Lst, J⟩
    rw [specTail_nil hk call, if_neg hrs]; exact Set.mem_singleton _

/-- The caller's buffer word for a reply (P3/JAtZV3VRvmcb's `readVmcbJ`). -/
theorem JAtZV3.replyBuf (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) :
    msg.lookup_ipc_buffer st s true ct ⦃ bw => JBufR Z.B bw (Endp.ipcBufOf true x) ⦄ := by
  have B := J.z2.zv.base
  have hcth : Z.th ct = some .tcb := B.thTcb hct
  obtain ⟨x0, hkx, hwr⟩ := B.buf ct hct
  rw [hk] at hkx; cases hkx
  have hBC := bufCover_of_frameCover (T := Z.T) B.bok B.fcov
  refine WP.spec_mono (Endp.lookup_buf_full s σ B.xtop.rel.2.1.1 B.xtop.rel.2.1.2.1 hcth hk B.bok true) ?_
  intro bw hbw
  obtain ⟨hrw0, hrwp⟩ := hbw
  show JBufR Z.B bw (Endp.ipcBufOf true x)
  have hb : JBufR Z.B bw (Endp.ipcBufOf true x) := by
    cases hrb : Endp.ipcBufOf true x with
    | none => exact hrw0.2 hrb
    | some rp =>
      have hrwv : bw.bv = rp := hrwp hwr rp hrb
      exact ⟨(fun e => by have := hrw0.1 e; rw [hrb] at this; cases this),
        hBC ct hct x true rp hk hrb bw hrwv, hrwv⟩
  exact hb

set_option maxHeartbeats 4000000 in
/-- **`reply_words` at `JAtZV3` with a continuation** (as `replyWords3`). -/
theorem JAtZV3.replyWordsK {σ0 : Fl4Spec.State Unit} {ct : U64} {x0 : Fl4Spec.Tcb} {buf : Option Fl4Spec.ObjRef}
    {ms : List Fl4Spec.Word}
    (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (MrS σ0 ct.bv x0 buf ms)) (hct : ct ∈ Z.T)
    (n : U64) (hn : n.val = mrLen buf ms.length) (hn128 : n.val < 128) {β : Type} (K : S → Result β)
    {Q : β → Prop}
    (hK : ∀ s4, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s4 a (replyStateB σ0 ct.bv x0 buf ms) → K s4 ⦃ Q ⦄) :
    (do
      let s3 ← obj.Tcb.set_reg st ct s layout.reg.BADGE 0#u64
      let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 n
      let s4 ← msg.set_msg_info st s3 ct mi
      K s4) ⦃ Q ⦄ := by
  have hkx := MrS_kheap_t σ0 ct.bv x0 buf ms
  refine WP.spec_bind (Endp.obj.Tcb.set_reg.spec s ct layout.reg.BADGE 0#u64) ?_
  rintro s1 rfl
  have J1 := J.regWr hct hkx Fl4Spec.badge_register 0#u64
  rw [Endp.regIdx_badge] at J1
  rw [mrS_setReg σ0 ct.bv x0 buf ms badge_not_mr] at J1
  have e0 : U64.bv 0#u64 = (0 : Fl4Spec.Word) := rfl
  rw [e0] at J1
  set xA := Notif.setReg x0 Fl4Spec.badge_register 0
  unfold msginfo.MessageInfo.new
  simp only [bind_ok]
  refine WP.spec_bind (Endp.set_msg_info_spec _ ct 0#u64 n hn128) ?_
  rintro s2 ⟨v, rfl, hv⟩
  rw [← Endp.regIdx_msgInfo]
  have hkA := MrS_kheap_t (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms
  have J2 := J1.regWr hct hkA Fl4Spec.msg_info_register v
  have hvd : v.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen (mrLen buf ms.length), 0, 0, 0⟩ := by
    rw [hv]; congr 2
    apply BitVec.eq_of_toNat_eq; simp only [Fl4Spec.natToLen, BitVec.toNat_ofNat, UScalar.bv_toNat, ← hn]; omega
  have eR : Notif.updK (MrS (Notif.updK σ0 ct.bv (.tcb xA)) ct.bv xA buf ms) ct.bv
      (.tcb (Notif.setReg (Endp.withRegs xA (Endp.mrRegs xA.tcbArch.tcbContext.userRegs ms))
        Fl4Spec.msg_info_register v.bv)) = replyStateB σ0 ct.bv x0 buf ms := by
    unfold replyStateB; rw [hvd]
  rw [eR] at J2
  exact hK _ J2

set_option maxHeartbeats 4000000 in
/-- **`vcpuReplyWs` from a `Running` caller at `JAtZV3`** (module docstring). -/
theorem JAtZV3.replyWsRun3 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .running) (call : Bool)
    (ws : List U64) (hl : ws.length ≤ 120) :
    vcpuReplyWs st s ct call ws ⦃ r => ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r a
      (stsAct (updK (if call then replyState σ ct.bv x (ws.map (·.bv)) else σ) ct.bv
        (.tcb { (if call then replyTcbB x (Endp.ipcBufOf true x) (ws.map (·.bv)) else x) with
          tcbState := .running })) ct.bv) ⦄ := by
  unfold vcpuReplyWs
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact J.runRJ hct hk hrs
  · simp only [↓reduceIte]
    refine WP.spec_bind (J.replyBuf hct hk) ?_
    intro bw hb
    have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ ct.bv x (Endp.ipcBufOf true x) []) := by
      rw [jMrSt_nil hk]; exact J
    refine WP.spec_bind (JAtZV3.wsLoop3 hct (fun p h => h) hb ws [] s 0#u64 0#u64 J0 rfl
      (by cases Endp.ipcBufOf true x <;> rfl) (by simpa using hl)) ?_
    rintro ⟨s2, n⟩ ⟨J2, hn⟩
    try simp only [uncurry_apply_pair]
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at J2 hn
    rw [← zv_MrS_jMrSt] at J2
    have hn' : n.val = mrLen (Endp.ipcBufOf true x) (ws.map (·.bv)).length := by
      rw [hn, zv_jMrRet_mrLen, List.length_map]
    have hn128 : n.val < 128 := by
      have := zv_jMrRet_le (Endp.ipcBufOf true x) ws.length; omega
    exact J2.replyWordsK hct n hn' hn128 _ fun s4 J4 =>
      J4.runRJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs])

set_option maxHeartbeats 4000000 in
/-- **`vcpu.reply` from a `Running` caller at `JAtZV3`** (module docstring). -/
theorem JAtZV3.vreply3 (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {ct : U64}
    (hcur : sched.cur_thread st s = ok ct) (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (hrs : x.tcbState = .running) (call : Bool) (y : U64) :
    vcpu.reply st s call y ⦃ r => ∃ Lst' : U64 → List U64, JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst' D r a
      (stsAct (updK (if call then replyState σ ct.bv x [y.bv] else σ) ct.bv
        (.tcb { (if call then replyTcbB x (Endp.ipcBufOf true x) [y.bv] else x) with
          tcbState := .running })) ct.bv) ⦄ := by
  unfold vcpu.reply
  rw [hcur, bind_ok]
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    exact J.runRJ hct hk hrs
  · simp only [↓reduceIte]
    refine WP.spec_bind (Pₘ := fun s1 => JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a
      (replyStateB σ ct.bv x (Endp.ipcBufOf true x) [y.bv])) ?_ ?_
    · refine WP.spec_bind (J.replyBuf hct hk) ?_
      intro bw hb
      have J0 : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a (jMrSt σ ct.bv x (Endp.ipcBufOf true x) []) := by
        rw [jMrSt_nil hk]; exact J
      refine WP.spec_bind (setMrJ3 J0 hct (fun p h => h) hb 0#u64 (by simp) (by simp) y) ?_
      rintro ⟨n1, s2⟩ J2
      try simp only [uncurry_apply_pair]
      have em : mrUpd [] (0#u64 : U64).val y.bv = [y.bv] := by unfold mrUpd; simp
      simp only at J2
      rw [em, ← zv_MrS_jMrSt] at J2
      exact J2.replyWords3 hct 1#u64 (by cases Endp.ipcBufOf true x <;> rfl) (by decide)
    · intro s1 J1
      exact J1.runRJ hct (replyStateB_kheap_t _ _ _ _ _) (by rw [replyTcbB_state, hrs])

end

end

end Fl4Proofs.P3
