/-
P3 (DESIGN.md §9): more endpoint theorems against the combined relation
`CombRel` (`TcbRel.lean`).

* `ntfn_lift_rcv`: the notification relation survives writes to the
  receiver's registers and the IPC buffer words only, with only the
  receiver's TCB changed in the spec (state kept). It is the frame of every
  message transfer; the new badge register is read off `EpStateRel`.
* `ntfn_reply_write`: and writes to a reply object.
* `do_ipc_transfer_regs_comb`, `do_ipc_transfer_buf_comb`: the transfers.
* `send_ipc_noblock_comb`: non-blocking send with no receiver.
* `receive_ipc_block_comb`: blocking receive.
-/
import Fl4Proofs.P3.TcbRel
import Fl4Proofs.P3.EpFaultMore
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Endp
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif

noncomputable section

section
variable {N T E R : Set U64} {B : Set (U64 × Fl4Spec.Word)}

/-- **The notification relation over a message transfer.** -/
theorem ntfn_lift_rcv (hP : CPlaced N T E R B) {m m' : U64 → U64} {σ σ' : Fl4Spec.State Unit}
    (hN : NtfnStateRel N T m σ) (hE' : EpStateRel T E R B m' σ') {rcv : U64} (hr : rcv ∈ T)
    (hA : Agree m m' (fun b => ¬ RcvReg rcv b ∧ ¬ BufW B b))
    (hk : ∀ p, p ≠ rcv.bv → σ'.kheap p = σ.kheap p) {xr : Fl4Spec.Tcb} (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {x' : Fl4Spec.Tcb} (hkr' : σ'.kheap rcv.bv = some (.tcb x')) (hst : x'.tcbState = xr.tcbState) :
    NtfnStateRel N T m' σ' := by
  let P : Nat → Prop := fun v => ¬ (∃ r, v = (regA rcv (regIdx r)).val) ∧ ¬ ∃ wp ∈ B, v = wp.1.val
  have hA' : ∀ a, Aligned a → P a.val → m' a = m a := fun a ha h =>
    hA a ha ⟨h.1, fun ⟨wp, hw, he⟩ => h.2 ⟨wp, hw, congrArg UScalar.val he⟩⟩
  have hra := hP.n.tcb rcv hr
  have hPt : ∀ y ∈ T, ∀ k, (3328 ≤ k ∨ y ≠ rcv) → 256 ≤ k → k < 4096 → P (y.val + k) := by
    intro y hy k hk h1 h2
    refine ⟨?_, ?_⟩
    · rintro ⟨r, hv⟩
      rw [regA_val hra (regIdx_lt r)] at hv
      have := regIdx_lt r
      by_cases e : y = rcv
      · subst e
        rcases hk with hk | hk
        · omega
        · exact absurd rfl hk
      · have := tcb_disj hP.e hr hy e; omega
    · rintro ⟨wp, hw, hv⟩; have := hP.e.bt wp hw y hy; omega
  have hPn : ∀ n ∈ N, ∀ k, k < 40 → P (n.val + k) := by
    intro n hn k hk
    refine ⟨?_, ?_⟩
    · rintro ⟨r, hv⟩
      rw [regA_val hra (regIdx_lt r)] at hv
      have := regIdx_lt r; have := hP.n.disj n hn rcv hr; omega
    · rintro ⟨wp, hw, hv⟩; have := hP.nb n hn wp hw; omega
  have hmem : ∀ y ∈ T, MemberEq m m' y := by
    intro y hy
    have hya := hP.n.tcb y hy
    exact ⟨hA' _ (a_st hya).1 (by rw [val_st hya]; exact hPt y hy _ (Or.inl (by omega)) (by omega) (by omega)),
      hA' _ (a_blk hya).1 (by rw [val_blk hya]; exact hPt y hy _ (Or.inl (by omega)) (by omega) (by omega)),
      tlinksEq_of hya P hA' (hPt y hy _ (Or.inl (by omega)) (by omega) (by omega))
        (hPt y hy _ (Or.inl (by omega)) (by omega) (by omega))⟩
  refine ⟨fun n hn => ?_, fun t ht => ?_⟩
  · obtain ⟨x, hkx, hx⟩ := hN.ntfn n hn
    have hnr : n.bv ≠ rcv.bv := kheap_ne hkx hkr (fun _ h1 h2 => by subst h1; cases h2)
    exact ⟨x, by rw [hk _ hnr, hkx], hx.frame (nwordsEq_of (hP.n.ntfn n hn) P hA' (hPn n hn))
      fun y hy _ => hmem y hy⟩
  · have hta := hP.n.tcb t ht
    by_cases e : t = rcv
    · subst e
      obtain ⟨x, hkx, hx⟩ := hN.tcb t ht
      rw [hkr] at hkx
      injection hkx with hkx; injection hkx with hkx; subst hkx
      have hE1 := hE'.at_tcb hr hkr'
      refine ⟨x', hkr', ⟨hE1.st, fun n hn => ?_, ?_, hE1.prio⟩⟩
      · rw [(hmem t ht).2.1]; exact hx.blk n (hst ▸ hn)
      · show (m' (badgeRegA t)).bv = (x'.tcbArch.tcbContext.userRegs Fl4Spec.badge_register)
        rw [badgeRegA_eq_regA]; exact hE1.regs _
    · obtain ⟨x, hkx, hx⟩ := hN.tcb t ht
      have htr : t.bv ≠ rcv.bv := bv_inj e
      refine ⟨x, by rw [hk _ htr, hkx], hx.frame (tfieldsEq_of hta P hA' ?_ ?_ ?_ ?_)⟩ <;>
        exact hPt t ht _ (Or.inr e) (by omega) (by omega)

/-- The notification relation over a write to a reply object. -/
theorem ntfn_reply_write {Z : Type} (hP : CPlaced N T E R B) {m m' : U64 → U64} {σ : Fl4Spec.State Z}
    (hN : NtfnStateRel N T m σ) {r : U64} (hr : r ∈ R) (hA : Agree m m' (fun b => b.val ≠ r.val))
    {xr : Fl4Spec.Reply} (hkr : σ.kheap r.bv = some (.reply xr)) (y : Fl4Spec.Reply) :
    NtfnStateRel N T m' (updK σ r.bv (.reply y)) := by
  refine hN.frame hP.n (fun a ha hf => hA a ha ?_) ⟨fun p x h => ?_, fun p x h => ⟨x, ?_, rfl, rfl, rfl⟩⟩
  · rcases hf with ⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩
    · have := hP.nr n hn r hr; omega
    · have hta := hP.n.tcb t ht
      have := hP.e.rt r hr t ht
      rcases h with h | h | h | h | h | h <;> subst h
      · rw [val_st hta]; omega
      · rw [val_blk hta]; omega
      · rw [badgeRegA_eq_regA, regA_val hta (regIdx_lt _)]; have := regIdx_lt Fl4Spec.badge_register; omega
      · rw [val_prio hta]; omega
      · rw [val_next hta]; omega
      · rw [val_prev hta]; omega
  · have : p ≠ r.bv := kheap_ne h hkr (fun _ h1 h2 => by subst h1; cases h2)
    simp [this, h]
  · have : p ≠ r.bv := kheap_ne h hkr (fun _ h1 h2 => by subst h1; cases h2)
    simp [this, h]

end

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st] {N T E R : Set U64}
  {B : Set (U64 × Fl4Spec.Word)} {SR : S → Fl4Spec.State Unit → Prop}

/-- **`do_ipc_transfer`, registers only**, against the combined relation. -/
theorem do_ipc_transfer_regs_comb (hC : CombHyps st N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hP : CPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    (hrb : ipcBufOf true xr = none) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ =
        ({((), updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv)))}, False) ∧
      CombRel N T E R B (L.mem s') (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ∧
      SR s' (updK σ rcv.bv (.tcb (xferTcb xr xs badge.bv))) ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_regs (ar := ar) hC.epHyps hBf hP.e s a σ hRC.2 hSR hs hr hne hks hkr hf hrb
    ep badge grant hcaps) ?_
  rintro s' ⟨h1, h2, h3, h4⟩
  refine ⟨h1, ⟨ntfn_lift_rcv hP hRC.1 h2 hr (h4.mono fun _ h => h.1) (fun p hp => by simp [hp]) hkr
    (by simp only [updK_kheap, Function.update_self]; exact rfl) (xferTcb_state _ _ _), h2⟩, h3⟩

/-- **`do_ipc_transfer` with a receive buffer**, against the combined
relation. -/
theorem do_ipc_transfer_buf_comb (hC : CombHyps st N T E R B SR) (hBf : EpBufHyps st T E R B SR)
    (hBm : EpBufMapHyps st T E R B SR) (hP : CPlaced N T E R B)
    (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr)) (hf : xs.tcbFault = none)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool)
    (hcaps : grant = false ∨ ipcBufOf false xs = none ∨
      Fl4Spec.unat (Fl4Spec.dataToMessageInfo (xs.tcbArch.tcbContext.userRegs Fl4Spec.msg_info_register)).miExtraCaps = 0) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      CombRel N T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_buf (ar := ar) hC.epHyps hBf hBm hP.e s a σ hRC.2 hSR hs hr hne hks hkr hf
    hrb ep badge grant hcaps) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
  exact ⟨σ', h1, ⟨ntfn_lift_rcv hP hRC.1 h2 hr h4 h5 hkr h6 h7, h2⟩, h3⟩

/-- **`do_ipc_transfer` of a faulted sender** into a receiver with an IPC
buffer, against the combined relation. -/
theorem do_ipc_transfer_fault_comb (hC : CombHyps st N T E R B SR) (hBm : EpBufMapHyps st T E R B SR)
    (hP : CPlaced N T E R B) (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {snd rcv : U64} (hs : snd ∈ T) (hr : rcv ∈ T) (hne : snd ≠ rcv) {xs xr : Fl4Spec.Tcb}
    (hks : σ.kheap snd.bv = some (.tcb xs)) (hkr : σ.kheap rcv.bv = some (.tcb xr))
    {f : Fl4Spec.Fault} (hf : xs.tcbFault = some f) (hok : FaultOK (L := L) s snd xs f)
    {rp : Fl4Spec.ObjRef} (hrb : ipcBufOf true xr = some rp) (ep badge : U64) (grant : Bool) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' => ∃ σ',
      Fl4Spec.doIpcTransfer (Z := Unit) snd.bv (some ep.bv) badge.bv grant rcv.bv σ = ({((), σ')}, False) ∧
      CombRel N T E R B (L.mem s') σ' ∧ SR s' σ' ⦄ := by
  refine WP.spec_mono (do_ipc_transfer_fault (ar := ar) hC.epHyps hBm hP.e s a σ hRC.2 hSR hs hr hne hks hkr hf
    hok hrb ep badge grant) ?_
  rintro s' ⟨σ', h1, h2, h3, h4, h5, x', h6, h7⟩
  exact ⟨σ', h1, ⟨ntfn_lift_rcv hP hRC.1 h2 hr h4 h5 hkr h6 h7, h2⟩, h3⟩

/-- **Non-blocking send** with no receiver, against the combined relation:
nothing changes. -/
theorem send_ipc_noblock_comb (s : S) (a : A) (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ)
    (hSR : SR s σ) {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock false x) (call : Bool) (badge : U64) (g gr d : Bool) (t : U64) :
    endpoint.send_ipc st ar s a false call badge g gr d t e ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.sendIpc (Z := Unit) false call badge.bv g gr d t.bv e.bv σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ :=
  WP.spec_mono (send_ipc_noblock (ar := ar) s a σ hRC.2 he hk hc call badge g gr d t) fun r ⟨h1, h2⟩ => by
    subst h1; exact ⟨rfl, σ, h2, hRC, hSR⟩

/-- **Blocking receive** on an idle endpoint or one with waiting receivers,
against the combined relation. -/
theorem receive_ipc_block_comb (hC : CombHyps st N T E R B SR) (hP' : CPlaced N T E R B) (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hRC : CombRel N T E R B (L.mem s) σ) (hSR : SR s σ)
    {t : U64} (ht : t ∈ T) {xt : Fl4Spec.Tcb} (hkt : σ.kheap t.bv = some (.tcb xt))
    (hnb : tsCode xt.tcbState ≠ 3 ∧ tsCode xt.tcbState ≠ 4) (hbn : xt.tcbBoundNotification = none)
    (hnn : ∀ m, xt.tcbState ≠ .blockedOnNotification m)
    {e : U64} (he : e ∈ E) {x : Fl4Spec.Endpoint} (hk : σ.kheap e.bv = some (.endpoint x))
    (hc : CanBlock true x)
    (hsort : ∀ xs, QueueRel (L.mem s) T .Ep (qOf (L.mem s) e) xs → PrioSorted (fun y => L.mem s (prioA y)) xs)
    (cb : U64) (c1 c2 c3 c4 : Bool) {rc : capability.Cap} {rc' : Fl4Spec.Cap} {rv : U64}
    (hrc : ReplyArg R (L.mem s) rc rc' rv) (b : Fl4Spec.Badge) (rights : Fl4Spec.CapRights) :
    endpoint.receive_ipc st ar s a t (.Endpoint e cb c1 c2 c3 c4) true rc ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
  have hH := hC.epHyps
  have hP := hP'.e
  have hR := hRC.2
  have hN := hRC.1
  have hqn := not_member hN ht hkt hnn
  have hx := hR.at_ep he hk
  have hxt := hR.at_tcb ht hkt
  have hta := hP.tcb t ht
  have hq := not_queued hR ht hkt hnb
  have htq : t.bv ∉ x.epQueue := hq e he x hk
  have hbound : L.mem s (tBoundA t) = 0#u64 := optRef_none (hxt.bound.symm.trans hbn)
  have hns : ∀ q, x ≠ .sendEP q := fun q h => by subst h; simp [CanBlock] at hc
  have hspec0 := receiveIpc_noSend b rights true (replyArg_spec hP hR hrc) hkt hbn hk hns
  set x1 : Fl4Spec.Tcb := { xt with tcbState := .blockedOnReceive e.bv (optRef rv) { receiverCanGrant := false } }
  set σ1 := updK σ t.bv (.tcb x1)
  set s3 := L.wr (L.wr (L.wr s (tStA t) sched.TS_BLOCKED_ON_RECV) (tBlockA t) e) (tReplyA t) rv
  obtain ⟨hA3, r1, r2, r3, hW3⟩ := block_recv_writes (L := L) hP s ht e rv
  have v1 := val_st hta; have v2 := val_blk hta; have v3 := val_reply hta
  have hR1 : EpStateRel T E R B (L.mem s3) σ1 := by
    refine hR.upd_tcb hP ht x1 (hA3.mono fun b hb => ?_) (Or.inl hq) ?_
    · have n1 : b.val ≠ (tStA t).val := fun h => hb.2 (TF.of_val (a_st hta).2 h)
      have n2 : b.val ≠ (tBlockA t).val := fun h => hb.2 (TF.of_val (a_blk hta).2 h)
      have n3 : b.val ≠ (tReplyA t).val := fun h => hb.2 (TF.of_val (a_reply hta).2 h)
      omega
    refine hxt.restate hta (hA3.mono fun b hb => ?_) rfl rfl rfl rfl ?_ ?_ ?_ ?_ ?_
    · have := hb.2; omega
    · rw [r1]; unfold sched.TS_BLOCKED_ON_RECV; rfl
    · intro e' h; simp only [x1, Fl4Spec.epBlocked, Option.some.injEq] at h; subst h; rw [r2]
    · intro e' d'' h; simp [x1] at h
    · intro e' r d'' h
      simp only [x1, Fl4Spec.ThreadState.blockedOnReceive.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      refine ⟨by rw [r3], fun hne => ?_⟩
      rw [r3]
      by_cases h0 : rv = 0#u64
      · rw [h0, optRef_zero] at hne; exact absurd rfl hne
      · exact (replyArg_ne hP hrc h0).1
    · intro r h; simp [x1] at h
  have hN1 : NtfnStateRel N T (L.mem s3) σ1 := by
    have hxt1 := hN.at_tcb ht hkt
    have g3 : ∀ b, Aligned b → (b.val < t.val + 3328 ∨ t.val + 3368 ≤ b.val) → L.mem s3 b = L.mem s b :=
      fun b hb hv => hA3 b hb (by omega)
    refine ntfn_upd_fields hP' hN ht x1 g3 hqn ⟨?_, ?_, ?_, ?_⟩
    · rw [r1]; unfold sched.TS_BLOCKED_ON_RECV; rfl
    · intro n h; simp [x1] at h
    · show (L.mem s3 (badgeRegA t)).bv = badgeOf xt
      rw [g3 _ (by rw [badgeRegA_eq_regA]; exact (a_reg hta _).1) (by
        rw [badgeRegA_eq, tw_val hta (by simp)]; left; simp)]
      exact hxt1.badge
    · show (L.mem s3 (prioA t)).val = xt.tcbPriority.toNat
      rw [g3 _ (a_prio hta).1 (by rw [val_prio hta]; omega)]
      exact hxt1.prio
  have hS1 : EpStep σ σ1 := EpStep.tcb hkt _ xt.tcbArch
  have hSR1 := hH.stable _ _ _ _ hSR hW3 hS1
  set σ2 := stsAct σ1 t.bv
  have hnt : e.bv ≠ t.bv := kheap_ne hk hkt (fun _ h1 h2 => by subst h1; cases h2)
  have hk2 : σ2.kheap e.bv = some (.endpoint x) := by simp [σ2, σ1, stsAct_kheap, hnt, hk]
  have hkt2 : σ2.kheap t.bv = some (.tcb x1) := by simp [σ2, σ1, stsAct_kheap]
  have hspec : Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
      (Fl4Spec.NonDet.maybeM (fun r => Fl4Spec.setReplyObjRef Fl4Spec.replyTcbUpdate r (some t.bv)) (optRef rv) >>=
        fun _ => Fl4Spec.tcbEpAppend t.bv e.bv true) σ2 := by
    rw [hspec0]
    unfold Fl4Spec.receiveIpcBlocked
    rw [if_pos rfl, nd_bind_one (setThreadState_eq _ hkt)]
  have hprio3 : ∀ y ∈ T, L.mem s3 (prioA y) = L.mem s (prioA y) := by
    intro y hy
    have hya := hP.tcb y hy
    refine hA3 _ (a_prio hya).1 ?_
    have := val_prio hya
    by_cases eyt : y = t
    · subst eyt; omega
    · have := tcb_disj hP ht hy eyt; omega
  have key : (do
      let s3 ← endpoint.wait_for_sender st s t e true rv
      ok (s3, a)) ⦃ r => r.2 = a ∧
      ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ = ({((), σ')}, False) ∧
        CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
    unfold endpoint.wait_for_sender
    simp only [↓reduceIte]
    step as ⟨s1', h1⟩
    step as ⟨s2', h2⟩
    step as ⟨s3', h3⟩
    subst h1 h2 h3
    refine WP.spec_bind (hC.scheduleTcb _ σ1 t hR1 hSR1 ht) ?_
    rintro s4 ⟨hf4, hfN4, hS4⟩
    have hR2 : EpStateRel T E R B (L.mem s4) σ2 := hR1.frame hP hf4 (KView.stsAct' _ _)
    have hN2 : NtfnStateRel N T (L.mem s4) σ2 := hN1.frame hP'.n hfN4 (Notif.KView.stsAct _ _)
    have hfoot : ∀ {a'}, Aligned a' ∧ TF t a' → L.mem s4 a' = L.mem s3 a' := fun h =>
      hf4 _ h.1 (Or.inr (Or.inr (Or.inl ⟨t, ht, Or.inl h.2⟩)))
    have hprio4 : ∀ y ∈ T, L.mem s4 (prioA y) = L.mem s (prioA y) := fun y hy => by
      have hya := hP.tcb y hy
      rw [hf4 _ (a_prio hya).1 (Or.inr (Or.inr (Or.inl ⟨y, hy, Or.inl (a_prio hya).2⟩))), hprio3 y hy]
    have tail : ∀ (s5 : S) (σ3 : Fl4Spec.State Unit), EpStateRel T E R B (L.mem s5) σ3 →
        NtfnStateRel N T (L.mem s5) σ3 → SR s5 σ3 →
        σ3.kheap e.bv = some (.endpoint x) → σ3.kheap t.bv = some (.tcb x1) →
        (∀ y ∈ T, L.mem s5 (prioA y) = L.mem s (prioA y)) →
        L.mem s5 (tStA t) = sched.TS_BLOCKED_ON_RECV → L.mem s5 (tBlockA t) = e →
        (Fl4Spec.NonDet.maybeM (fun r => Fl4Spec.setReplyObjRef Fl4Spec.replyTcbUpdate r (some t.bv)) (optRef rv) σ2 =
          ({((), σ3)}, False)) →
        (do
          let s6 ← endpoint.ep_append st s5 e t obj.EP_RECV
          ok (s6, a)) ⦃ r => r.2 = a ∧
          ∃ σ', Fl4Spec.receiveIpc (Z := Unit) t.bv (.endpointCap e.bv b rights) true rc' σ =
            ({((), σ')}, False) ∧ CombRel N T E R B (L.mem r.1) σ' ∧ SR r.1 σ' ⦄ := by
      intro s5 σ3 hR3 hN3 hS3 hk3 hkt3 hpr5 hst5 hb5 hm
      have hsort5 := sorted_transfer hP.tcb hx (hR3.at_ep he hk3) hpr5 hsort
      have htst : (L.mem s5 (tStA t)).val = if true = true then 3 else 4 := by
        rw [hst5]; unfold sched.TS_BLOCKED_ON_RECV; rfl
      have happ := ep_append_rel hH hP s5 σ3 hR3 hS3 ht hkt3 he hk3 true hc htq htst hb5 hsort5
      simp only [↓reduceIte] at happ
      obtain ⟨xs, hQ, hxs, hB⟩ := (hR3.at_ep he hk3).queue
      have htxs : t ∉ xs := fun h => htq (by rw [hxs]; exact List.mem_map_of_mem h)
      have hqa := WP.spec_mono (ep_append_full hP s5 he t obj.EP_RECV xs hQ ht htxs) fun _ h => h.2.2.1
      refine WP.spec_bind (WP.spec_and happ hqa) ?_
      rintro s6 ⟨⟨σ', hσ', hR', hS'⟩, hQA⟩
      have hq3 : ∀ y ∈ x.epQueue, ∃ z, σ3.kheap y = some (.tcb z) ∧ z.tcbPriority = prioOf σ3 y := by
        intro y hy
        rw [hxs] at hy
        obtain ⟨y', hy'x, rfl⟩ := List.mem_map.1 hy
        obtain ⟨z, hz, -⟩ := hR3.tcb y' (hQ.mem y' hy'x)
        exact ⟨z, hz, by simp [prioOf, hz]⟩
      have hσ2 := hσ'
      rw [tcbEpAppend_eq hk3 hkt3 (prioOf σ3) hq3] at hσ2
      have hσe : σ' = updK σ3 e.bv (.endpoint (Fl4Spec.updateEpQueue x
          (specIns x.epQueue (prioOf σ3) x1.tcbPriority t.bv) true)) := by
        have := congrArg Prod.fst hσ2
        simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at this
        exact this.symm
      have hkv : Notif.KView σ3 σ' := by
        rw [hσe]
        refine ⟨fun p y h => ?_, fun p y h => ⟨y, ?_, rfl, rfl, rfl⟩⟩
        · have : p ≠ e.bv := by intro h'; rw [h', hk3] at h; cases h
          simp [this, h]
        · have : p ≠ e.bv := by intro h'; rw [h', hk3] at h; cases h
          simp [this, h]
      have hW : ∀ w ∈ t :: xs, w ∈ T ∧ (L.mem s5 (tStA w)).val ≠ 6 := by
        intro w hw
        rcases List.mem_cons.1 hw with rfl | hw
        · exact ⟨ht, by rw [htst]; simp⟩
        · exact ⟨hQ.mem w hw, by rcases (hB w hw).2 with h | h <;> rw [h] <;> simp⟩
      have hN' := ntfn_frame_ep hP' hN3 he hW hQA hkv
      simp only [WP.spec_ok]
      exact ⟨by simp, σ', by rw [hspec, nd_bind_one hm]; exact hσ', ⟨hN', hR'⟩, hS'⟩
    by_cases h0 : rv = 0#u64
    · simp only [h0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      apply ok_bind_spec
      refine tail s4 σ2 hR2 hN2 hS4 hk2 hkt2 hprio4 ?_ ?_ (by rw [h0, optRef_zero]; rfl)
      · rw [hfoot (a_st hta), r1]
      · rw [hfoot (a_blk hta), r2]
    · have hne : (rv != 0#u64) = true := by simp [h0]
      simp only [hne, ↓reduceIte]
      obtain ⟨hrR, -⟩ := replyArg_ne hP hrc h0
      obtain ⟨xr, hkr, -⟩ := hR2.reply rv hrR
      obtain ⟨e1, hR5, hS5, hA5⟩ := reply_link_rel hH hP s4 σ2 hR2 hS4 hrR hkr hta
      have hN5 := ntfn_reply_write hP' hN2 hrR hA5 hkr { xr with replyTcb := some t.bv }
      step as ⟨s6', h6⟩
      subst h6
      have hnr : rv.bv ≠ e.bv := kheap_ne hkr hk2 (fun _ h1 h2 => by subst h1; cases h2)
      have hnr' : rv.bv ≠ t.bv := kheap_ne hkr hkt2 (fun _ h1 h2 => by subst h1; cases h2)
      have hdis := hP.rt rv hrR t ht
      refine tail _ _ hR5 hN5 hS5 (by simp [Ne.symm hnr, hk2]) (by simp [Ne.symm hnr', hkt2]) ?_ ?_ ?_ ?_
      · intro y hy
        have hya := hP.tcb y hy
        have := hP.rt rv hrR y hy
        rw [hA5 _ (a_prio hya).1 (by show (prioA y).val ≠ rv.val; rw [val_prio hya]; omega), hprio4 y hy]
      · rw [hA5 _ (a_st hta).1 (by show (tStA t).val ≠ rv.val; rw [val_st hta]; omega), hfoot (a_st hta), r1]
      · rw [hA5 _ (a_blk hta).1 (by show (tBlockA t).val ≠ rv.val; rw [val_blk hta]; omega), hfoot (a_blk hta), r2]
      · rw [optRef_ne h0]; exact e1
  apply receive_ipc_pre s a t e cb c1 c2 c3 c4 true rc rc' rv hrc hbound
  step as ⟨st1, hst1⟩
  rw [hst1, epState_eq]
  cases x with
  | idleEP =>
    rw [hx.1, if_pos ep_state_vals.1.symm]
    exact key
  | recvEP q =>
    rw [hx.1, if_neg (by rw [ep_state_vals.1]; decide), if_pos ep_state_vals.2.2.symm]
    exact key
  | sendEP q => exact absurd rfl (hns q)

end

end

end Fl4Proofs.P3.Endp
