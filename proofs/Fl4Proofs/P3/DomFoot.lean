/-
P3 (DESIGN.md §9): **FL4's half of `DomFrame` from P1's footprints**.

* `DecFootP1`: a cap's branch of `decode_invocation` writes in `KW` of P1's
  sets (`Foot`), `KW` lying apart from the domain schedule (`KWDom`);
  `decDomHyp_of_foot` turns it into `DecDomHyp` (AllDom), for any cap.
* `decFootP1_notification`: the notification cap's, from P1's
  `set_thread_state.restart_blk` and `send_signal.tinvF`.
* `IpcFoot`, `SendIpcFootP1`, `ReplyFootP1`: P1-shaped footprints of the
  IPC leaves under P1's own preconditions (`KW`, `XferFoot`, `CapW` apart);
  `ipcFoot_apart`; `decWritesHyp_endpoint`, `decWritesHyp_reply`: the endpoint
  and reply caps'.
* `DecWritesHyp`, `decDomHyp_of_writes`: from any write footprint apart from
  the domain schedule (the IRQ and IO-port caps, whose writes lie outside
  P1's `KW`).
-/
import Fl4Proofs.P3.AllDom
import Fl4Proofs.P1.QueueFootS
import Fl4Proofs.P1.QueueInvoke
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)

/-- **`DecDomHyp` in P1's shape**: the cap's branch of `decode_invocation`
writes in `KW` of P1's sets (`Foot`), `KW` lying apart from the domain
schedule. -/
def DecFootP1 (s : S) (ar : A) (lbl length slot : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∃ (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap),
    syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      P1.Foot st T Cs Sg Scs Z (P1.EH H) s r.2.1 ⦄ ∧ KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s

/-- **`DecDomHyp` from P1's footprint**, for any cap. -/
theorem decDomHyp_of_foot {s : S} {ar : A} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool}
    {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (h : DecFootP1 (L := L) arI s ar lbl length slot c blk call don fp buf extra) :
    DecDomHyp (L := L) arI s ar lbl length slot c blk call don fp buf extra := by
  obtain ⟨T, Cs, Sg, Scs, Z, H, hf, hD⟩ := h
  refine WP.spec_mono hf fun r hr => ⟨hr.1, fun o ho => ?_⟩
  obtain ⟨h1, h2⟩ := Sched.domOffs_lt ho
  refine hr.mem_eq (ksW_al hkf hka h1 h2) fun hk => ?_
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hD _ (ksW_al hkf hka h1 h2) hk with e | e <;> rw [hv] at e <;> omega

/-- **The notification cap's footprint**: the restart of a caller blocked on
nothing (P1's `set_thread_state.restart_blk`), then `send_signal`
(`send_signal.tinvF`), both writing in `KW`; with no send right, nothing. -/
theorem decFootP1_notification {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac : Set U64} (hA : P0.ArchTotal arI) (s : S) (ar : A) (lbl length slot : U64) (p b : U64) (sd rv : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hctT : ct ∈ T) (hnb : ¬ P1.Blocked (L.mem s (P1.stA ct)))
    (hnr : L.mem s (P1.stA ct) ≠ sched.TS_BLOCKED_ON_REPLY) (hpN : p ∈ Nt) (hH : H p = some .ntfn)
    (hD : KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s) :
    DecFootP1 (L := L) arI s ar lbl length slot (.Notification p b sd rv) blk call don fp buf extra := by
  refine ⟨T, Cs, Sg, Scs, Z, H, ?_, hD⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases sd
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact P1.Foot.refl _
  · simp only [↓reduceIte]
    refine WP.spec_bind (P1.sched.set_thread_state.restart_blk (Es := P1.EH H) s ct hB hctT hnb hnr) ?_
    rintro s1 ⟨hB1, f1, -, -⟩
    refine WP.spec_bind (P1.notification.send_signal.tinvF hA s1 ar p b hB1 hpN hH) ?_
    rintro ⟨s2, a1⟩ ⟨-, f2⟩
    exact (WP.spec_ok _).2 (f1.trans f2)


/-- **`DecDomHyp` from any write footprint** apart from the domain schedule
(the IRQ and IO-port decodes write kernel-global words past it, outside
P1's `KW`). -/
def DecWritesHyp (s : S) (ar : A) (lbl length slot : U64) (c : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) : Prop :=
  ∃ W : U64 → Prop, (∀ b, P1.Aligned b → W b → b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val) ∧
    syscall.decode_invocation st arI s ar lbl length slot c blk call don fp buf extra ⦃ r =>
      P1.WritesIn st s r.2.1 W ⦄

theorem decDomHyp_of_writes {s : S} {ar : A} {lbl length slot : U64} {c : capability.Cap} {blk call don fp : Bool}
    {buf : U64} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) (hka : (L.ksb s).val % 8 = 0)
    (h : DecWritesHyp (L := L) arI s ar lbl length slot c blk call don fp buf extra) :
    DecDomHyp (L := L) arI s ar lbl length slot c blk call don fp buf extra := by
  obtain ⟨W, hW, hf⟩ := h
  refine WP.spec_mono hf fun r hr => ⟨hr.1, fun o ho => ?_⟩
  obtain ⟨h1, h2⟩ := Sched.domOffs_lt ho
  refine hr.mem_eq (ksW_al hkf hka h1 h2) fun hk => ?_
  have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
  rcases hW _ (ksW_al hkf hka h1 h2) hk with e | e <;> rw [hv] at e <;> omega

/-- **The IPC leaves' footprint** (P1's `send_ipc`/`do_reply_transfer`): `KW`,
the message transfer's words (`XferFoot`: the receiver's context and user
memory), and cap-slot words (`CapW`: a grant's receive slot and its MDB
neighbours) apart from the first 256 bytes of the kernel-global block. -/
def IpcFoot (T Cs Ω Sg Scs : Set U64) (Z : U64 → Nat) (H : P1.Heap) (U : Set U64) (s : S) (b : U64) : Prop :=
  P1.KW st T Cs Sg Scs Z (P1.EH H) s b ∨ P1.XferFoot T U b ∨
    (P1.CapW T Ω Sg b ∧ (b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val)) ∨ P1.DbgW st T Cs s b

/-- **P1's footprint of `send_ipc`** (for the P1 side), under
`send_ipc.ipc`'s preconditions (`XferOK`, an endpoint, a caller that can
block, the donation condition, `UserOK`) and P1's placement premise `RS`
(the receive slots and MDB neighbours apart from the first 256 bytes). -/
def SendIpcFootP1 (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac U : Set U64)
    (P3Ok : S → Prop) (RS : S → Prop) (ct p : U64) (blk call : Bool) (b : U64) (g gr don : Bool) : Prop :=
  P1.XferOK st arI T Cs Ω H Sg Rp Scs Nt Z U (P1.XG st T Cs Ω H Sg Scs Z P3Ok) → H p = some .ep →
  ∀ (s1 : S) (a : A), P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → P1.CanBlock st T Ac s1 ct →
    (don = true → L.mem s1 (P1.scA ct) ≠ 0#u64) → P1.UserOK st T Cs Ω H U s1 → RS s1 →
    P1.XG st T Cs Ω H Sg Scs Z P3Ok s1 →
    endpoint.send_ipc st arI s1 a blk call b g gr don ct p ⦃ s' _ =>
      P1.WritesIn st s1 s' (IpcFoot (L := L) T Cs Ω Sg Scs Z H U s1) ⦄

/-- **P1's footprint of `do_reply_transfer`** (for the P1 side), under
`do_reply_transfer.bxi`'s preconditions and the placement premise `RS`. -/
def ReplyFootP1 (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac U : Set U64)
    (P3Ok : S → Prop) (RS : S → Prop) (ct r : U64) (g : Bool) : Prop :=
  P1.XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok → r ∈ Rp → ct ∈ T →
  ∀ (s1 : S) (a : A), P1.BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → P1.UserOK st T Cs Ω H U s1 → RS s1 →
    P1.XG st T Cs Ω H Sg Scs Z P3Ok s1 →
    ipc.do_reply_transfer st arI s1 a ct r g ⦃ s' _ =>
      P1.WritesIn st s1 s' (IpcFoot (L := L) T Cs Ω Sg Scs Z H U s1) ⦄

/-- **The IPC footprint lies apart from the domain schedule**: `KW` by
`KWDom`; `XferFoot`'s TCB words by the TCBs' placement (`hTk`), its user
words since they are not in `Ω` (`UserOK`) while the kernel-global words are
(`SCsOK.ksΩ`); the cap-slot words by their own condition. -/
theorem ipcFoot_apart {T Cs Ω Sg Scs : Set U64} {Z : U64 → Nat} {H : P1.Heap} {U Ac : Set U64} {s : S}
    (hD : KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s) (hTP : P1.TcbPlaced T)
    (hN : ∀ c ∈ Cs, P1.NodePlaced st T s c)
    (hTk : ∀ y ∈ T, y.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ y.val)
    (hUO : P1.UserOK st T Cs Ω H U s) (hSC : P1.SCsOK st T Ω Sg Scs Z Ac s)
    (hka : (L.ksb s).val % 8 = 0) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) :
    ∀ b, P1.Aligned b → IpcFoot (L := L) T Cs Ω Sg Scs Z H U s b →
      b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val := by
  intro b hb h
  rcases h with h | (⟨y, hy, K, hK, -, rfl⟩ | h) | ⟨-, h⟩ | (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · exact hD b hb h
  · have hf := (hTP y hy).fits
    have hv : (core.num.U64.wrapping_add y K).val = y.val + K.val := by
      rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, U64.numBits]; omega
    rw [hv]; rcases hTk y hy with e | e <;> omega
  · by_contra hc
    simp only [not_or, not_le] at hc
    have hb8 := hb; unfold P1.Aligned at hb8
    have hlt : b.val - (L.ksb s).val < 256 := by omega
    obtain ⟨o, ho⟩ : ∃ o : U64, o.val = b.val - (L.ksb s).val := ⟨⟨BitVec.ofNat 64 (b.val - (L.ksb s).val)⟩, by
      show (BitVec.ofNat 64 _).toNat = _; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)⟩
    have hm := hSC.ksΩ o (by omega) (by omega)
    have e : core.num.U64.wrapping_add (L.ksb s) o = b := by
      apply UScalar.eq_of_val_eq
      rw [core.num.U64.wrapping_add_val_eq]; simp [U64.size_def, U64.numBits]; omega
    rw [e] at hm
    exact (hUO b h).2.1 hm
  · exact h
  · have hf := (hTP y hy).fits
    have h3 : (3576#u64).val = 3576 := by simp
    rw [e, show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hTP y hy) (by simp)]
    rcases hTk y hy with e' | e' <;> omega
  · have hf := (hTP y hy).fits
    have h3 : (3584#u64).val = 3584 := by simp
    rw [e, show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hTP y hy) (by simp)]
    rcases hTk y hy with e' | e' <;> omega
  · rw [e, P1.nodeAt_val (hN c hc) (by simp [layout.node.DEBUG_TCBS])]
    unfold P1.LawfulStore.nodeBase
    right; omega

/-- **The endpoint cap's write footprint** (`DecWritesHyp`): the caller's
restart (`restart_blk`, a `Foot`) then `send_ipc` (`SendIpcFootP1`). -/
theorem decWritesHyp_endpoint {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac U : Set U64} {RS P3Ok : S → Prop} (s : S) (ar : A) (lbl length slot : U64) (p b : U64) (sd rv g gr : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hcb : P1.CanBlock st T Ac s ct) (hdon : don = true → L.mem s (P1.scA ct) ≠ 0#u64)
    (hUO : P1.UserOK st T Cs Ω H U s) (hxf : P1.XferOK st arI T Cs Ω H Sg Rp Scs Nt Z U (P1.XG st T Cs Ω H Sg Scs Z P3Ok))
    (hH : H p = some .ep) (hRS : ∀ s1, P1.Foot st T Cs Sg Scs Z (P1.EH H) s s1 → RS s1)
    (hXG : ∀ s1, P1.Foot st T Cs Sg Scs Z (P1.EH H) s s1 → P1.XG st T Cs Ω H Sg Scs Z P3Ok s1)
    (hsend : SendIpcFootP1 (L := L) arI T Cs Ω H Sg Rp Scs Nt Z Ac U P3Ok RS ct p blk call b g gr don)
    (hD : KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s)
    (hTk : ∀ y ∈ T, y.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ y.val)
    (hka : (L.ksb s).val % 8 = 0) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64)
    (hcbs : ∀ s1, P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 → P1.Foot st T Cs Sg Scs Z (P1.EH H) s s1 →
      L.mem s1 (P1.stA ct) = sched.TS_RESTART → P1.CanBlock st T Ac s1 ct ∧
        (don = true → L.mem s1 (P1.scA ct) ≠ 0#u64)) :
    DecWritesHyp (L := L) arI s ar lbl length slot (.Endpoint p b sd rv g gr) blk call don fp buf extra := by
  obtain ⟨⟨Q, R, hq⟩, -, -, hSC, -⟩ := id hB
  refine ⟨IpcFoot (L := L) T Cs Ω Sg Scs Z H U s,
    ipcFoot_apart hD hq.tcbs hq.nodes hTk hUO hSC hka hkf, ?_⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases sd
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact P1.WritesIn.refl _ _
  · simp only [↓reduceIte]
    refine WP.spec_bind (P1.sched.set_thread_state.restart_blk (Es := P1.EH H) s ct hB hcb.mem hcb.nb hcb.nrp) ?_
    rintro s1 ⟨hB1, f1, hst1, -⟩
    obtain ⟨hcb1, hdon1⟩ := hcbs s1 hB1 f1 hst1
    refine WP.spec_bind (hsend hxf hH s1 ar hB1 hcb1 hdon1 (hUO.ksb f1.1) (hRS s1 f1) (hXG s1 f1)) ?_
    rintro ⟨s2, a1⟩ f2
    simp only [WP.uncurry'] at f2
    refine (WP.spec_ok _).2 ((P1.WritesIn.trans f1 f2).mono fun x hx => ?_)
    rcases hx with hx | hx
    · exact Or.inl hx
    unfold IpcFoot at hx
    rcases hx with hx | hx | ⟨hc, hl⟩ | hx
    · exact Or.inl (P1.KW.ksb f1.1 hx)
    · exact Or.inr (Or.inl hx)
    · rw [f1.1] at hl; exact Or.inr (Or.inr (Or.inl ⟨hc, hl⟩))
    · exact Or.inr (Or.inr (Or.inr (P1.DbgW.ksb f1.1 hx)))


/-- **The reply cap's write footprint** (`DecWritesHyp`): the caller's
restart (`restart_blk`) then `do_reply_transfer` (`ReplyFootP1`). -/
theorem decWritesHyp_reply {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac U : Set U64} {RS P3Ok : S → Prop} (s : S) (ar : A) (lbl length slot : U64) (r : U64) (g : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hctT : ct ∈ T) (hnb : ¬ P1.Blocked (L.mem s (P1.stA ct)))
    (hnr : L.mem s (P1.stA ct) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hUO : P1.UserOK st T Cs Ω H U s) (hE : P1.XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (hr : r ∈ Rp)
    (hRS : ∀ s1, P1.Foot st T Cs Sg Scs Z (P1.EH H) s s1 → RS s1)
    (hXG : ∀ s1, P1.Foot st T Cs Sg Scs Z (P1.EH H) s s1 → P1.XG st T Cs Ω H Sg Scs Z P3Ok s1)
    (hrep : ReplyFootP1 (L := L) arI T Cs Ω H Sg Rp Scs Nt Z Ac U P3Ok RS ct r g)
    (hD : KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s)
    (hTk : ∀ y ∈ T, y.val + 4096 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ y.val)
    (hka : (L.ksb s).val % 8 = 0) (hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64) :
    DecWritesHyp (L := L) arI s ar lbl length slot (.Reply r g) blk call don fp buf extra := by
  obtain ⟨⟨Q, R, hq⟩, -, -, hSC, -⟩ := id hB
  refine ⟨IpcFoot (L := L) T Cs Ω Sg Scs Z H U s,
    ipcFoot_apart hD hq.tcbs hq.nodes hTk hUO hSC hka hkf, ?_⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (P1.sched.set_thread_state.restart_blk (Es := P1.EH H) s ct hB hctT hnb hnr) ?_
  rintro s1 ⟨hB1, f1, -, -⟩
  obtain ⟨hq1, hb1, hx1, hs1, hg1⟩ := hB1
  refine WP.spec_bind (hrep hE hr hctT s1 ar ⟨hq1, hb1, hx1, hg1, hs1⟩ (hUO.ksb f1.1) (hRS s1 f1) (hXG s1 f1)) ?_
  rintro ⟨s2, a1⟩ f2
  simp only [WP.uncurry'] at f2
  refine (WP.spec_ok _).2 ((P1.WritesIn.trans f1 f2).mono fun x hx => ?_)
  rcases hx with hx | hx
  · exact Or.inl hx
  unfold IpcFoot at hx
  rcases hx with hx | hx | ⟨hc, hl⟩ | hx
  · exact Or.inl (P1.KW.ksb f1.1 hx)
  · exact Or.inr (Or.inl hx)
  · rw [f1.1] at hl; exact Or.inr (Or.inr (Or.inl ⟨hc, hl⟩))
  · exact Or.inr (Or.inr (Or.inr (P1.DbgW.ksb f1.1 hx)))

end

end

end Fl4Proofs.P3
