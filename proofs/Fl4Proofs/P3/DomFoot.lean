/-
P3 (DESIGN.md §9): **FL4's half of `DomFrame` from P1's footprints**.

* `DecFootP1`: a cap's branch of `decode_invocation` writes in `KW` of P1's
  sets (`Foot`), `KW` lying apart from the domain schedule (`KWDom`);
  `decDomHyp_of_foot` turns it into `DecDomHyp` (AllDom), for any cap.
* `decFootP1_notification`: the notification cap's, from P1's
  `set_thread_state.restart_blk` and `send_signal.tinvF`.
* `decFootP1_endpoint`, `decFootP1_reply`: the endpoint and reply caps',
  from the restart and P1-shaped footprints of the leaves
  (`SendIpcFootP1`, `ReplyFootP1`, for the P1 side).
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
  rcases hD _ hk with e | e <;> rw [hv] at e <;> omega

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
  ∃ W : U64 → Prop, (∀ b, W b → b.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 256 ≤ b.val) ∧
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
  rcases hW _ hk with e | e <;> rw [hv] at e <;> omega

/-- **P1's footprint of `send_ipc`** for the restarted caller (for the P1
side): from `BlkOK`, a write in `KW`. -/
def SendIpcFootP1 (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (ct p : U64) (blk call : Bool) (b : U64) (g gr don : Bool) : Prop :=
  ∀ (s1 : S) (a : A), P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 →
    endpoint.send_ipc st arI s1 a blk call b g gr don ct p ⦃ s' _ => P1.Foot st T Cs Sg Scs Z (P1.EH H) s1 s' ⦄

/-- **The endpoint cap's footprint**: the restart (`restart_blk`) then
`send_ipc` (`SendIpcFootP1`). -/
theorem decFootP1_endpoint {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac : Set U64} (s : S) (ar : A) (lbl length slot : U64) (p b : U64) (sd rv g gr : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hctT : ct ∈ T) (hnb : ¬ P1.Blocked (L.mem s (P1.stA ct)))
    (hnr : L.mem s (P1.stA ct) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hsend : SendIpcFootP1 (L := L) arI T Cs Ω H Sg Rp Scs Nt Z Ac ct p blk call b g gr don)
    (hD : KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s) :
    DecFootP1 (L := L) arI s ar lbl length slot (.Endpoint p b sd rv g gr) blk call don fp buf extra := by
  refine ⟨T, Cs, Sg, Scs, Z, H, ?_, hD⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  cases sd
  · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact P1.Foot.refl _
  · simp only [↓reduceIte]
    refine WP.spec_bind (P1.sched.set_thread_state.restart_blk (Es := P1.EH H) s ct hB hctT hnb hnr) ?_
    rintro s1 ⟨hB1, f1, -, -⟩
    refine WP.spec_bind (hsend s1 ar hB1) ?_
    rintro ⟨s2, a1⟩ f2
    exact (WP.spec_ok _).2 (f1.trans f2)

/-- **P1's footprint of `do_reply_transfer`** for the restarted caller (for
the P1 side): from `BlkOK`, a write in `KW`. -/
def ReplyFootP1 (T Cs Ω : Set U64) (H : P1.Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (ct r : U64) (g : Bool) : Prop :=
  ∀ (s1 : S) (a : A), P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s1 →
    ipc.do_reply_transfer st arI s1 a ct r g ⦃ s' _ => P1.Foot st T Cs Sg Scs Z (P1.EH H) s1 s' ⦄

/-- **The reply cap's footprint**: the restart then `do_reply_transfer`
(`ReplyFootP1`). -/
theorem decFootP1_reply {T Cs Ω : Set U64} {H : P1.Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac : Set U64} (s : S) (ar : A) (lbl length slot : U64) (r : U64) (g : Bool)
    (blk call don fp : Bool) (buf : U64) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (hB : P1.BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (hctT : ct ∈ T) (hnb : ¬ P1.Blocked (L.mem s (P1.stA ct)))
    (hnr : L.mem s (P1.stA ct) ≠ sched.TS_BLOCKED_ON_REPLY)
    (hrep : ReplyFootP1 (L := L) arI T Cs Ω H Sg Rp Scs Nt Z Ac ct r g)
    (hD : KWDom (L := L) T Cs Sg Scs Z (P1.EH H) s) :
    DecFootP1 (L := L) arI s ar lbl length slot (.Reply r g) blk call don fp buf extra := by
  refine ⟨T, Cs, Sg, Scs, Z, H, ?_, hD⟩
  unfold syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  refine WP.spec_bind (P1.sched.set_thread_state.restart_blk (Es := P1.EH H) s ct hB hctT hnb hnr) ?_
  rintro s1 ⟨hB1, f1, -, -⟩
  refine WP.spec_bind (hrep s1 ar hB1) ?_
  rintro ⟨s2, a1⟩ f2
  exact (WP.spec_ok _).2 (f1.trans f2)

end

end

end Fl4Proofs.P3
