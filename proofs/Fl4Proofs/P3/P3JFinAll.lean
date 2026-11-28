/-
P3 (p3J gen 43): **bucket 3, the per-kind finaliser dispatch inside `ProjW`, and `post_cap_deletion`**.

* **`NatFinKind c`**: `c` is no IRQ handler cap and no arch cap with a finaliser (frame, page table / directory,
  PDPT, PML4, VCPU, EPT, ASID pool, IO port). **`natFinKind_of_kw`**: a cap abstracting to a `SInvCk.KW` cap (the
  cap kinds of a `CKI` state, P3JCkW) is `NatFinKind` or an IRQ handler cap; with P3JMcBuf's `kw_of_cki`
  (**`JAtZ.natFinKind_of_cki`**) every typed-heap slot of a `CKI` `JAtZ` state holds one. So the VSpace / IO-port /
  VCPU / EPT finalisers (FL4 `objects.rs` l.264–303) are never reached from a slot of a `CKI` state: their
  footprints are not needed on dispatch states.
* **`fin_cap.kwDN0`** (P1 namespace): `finalise_cap` of a `NatFinKind` cap from a `BlkOK` state, under P1's
  deletion bundle (QueueDecDel's `DelCapOK`, `FinPl`) and the scheduler action naming no thread (`Cur0`'s), is a
  `FootDN ∅ False` step — one case per kind: P3JNtfnFt's `fin_cap_ntfn.kwN0`, P3JEpFt's `fin_cap_ep.kwN0`, P3JFinFt's
  `fin_cap_reply.kwDN0` / `fin_cap_cnode.same` / `fin_cap_zombie.same` / `fin_cap_noop.same`, P3JScThFt's
  `fin_cap_sc.kwN0` / `fin_cap_thread.kwDN0` (the SC's thread is a thread of `T`: `ScExtra`'s `yt`).
* **`KsBW s0`** (the kernel-state block words `ksb + o`, `o < 13568`), `obj.ks_set.ksBW`, `ioport.apply.ksBW`,
  `ioport.set_mask.ksBW`, **`objects.post_cap_deletion.ksBW`** (FL4 `objects.rs` l.408–414: an IRQ handler's
  `deleted_irq_handler` writes its IRQ-state word, an IO port cap's `free_ioports` the IO-port bitmap words; P1
  QueueDelFin's `post_cap_deletion.cur0` walk with the frame `KsBW`).
* P3: **`JAtZ.finCapProjW`**, **`JAtZ.postCapDelProjW`** (`KsBW` words are `ProjW`'s kernel-block words).

Not covered: the IRQ handler kind of `finalise_cap` (its `deleting_irq_handler` deletes the IRQ slot's notification
cap, `delete_one`; gen 37's `delete_one_ntfnProjW` needs the `WJL` / `DState` context of the deletion loop).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JScThFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

/-- (p3J gen 43) **The cap kinds with a native finaliser** (module docstring). -/
def NatFinKind (c : capability.Cap) : Prop :=
  match c with
  | .IrqHandler _ | .Frame .. | .PageTable .. | .PageDirectory .. | .Pdpt .. | .Pml4 .. | .Vcpu _ | .Ept ..
  | .AsidPool .. | .IoPort .. => False
  | _ => True

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 43) **`finalise_cap` of a `NatFinKind` cap in `FootDN ∅ False`** (module docstring). -/
theorem fin_cap.kwDN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A)
    (c : capability.Cap) (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hc : DelCapOK T Ω Sg H Rp Nt c) (hpl : FinPl st Scs s c) (hact : ∀ y ∈ T, L.actionW s ≠ y)
    (hk : NatFinKind c) :
    objects.finalise_cap st ar s a c fin ex ⦃ r => FootDN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  have noop : (objects.finalise_cap st ar s a c fin ex ⦃ x => x.2.1 = s ⦄) →
      objects.finalise_cap st ar s a c fin ex ⦃ r => FootDN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ :=
    fun hh => WP.spec_mono hh fun _ e => e ▸ FootDN.refl _
  cases c with
  | Null => exact noop (fin_cap_noop.same s a _ fin ex (Or.inl rfl))
  | Untyped p b f d => exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inl ⟨_, _, _, _, rfl⟩)))
  | Endpoint p b0 b1 b2 b3 b4 =>
    exact WP.spec_mono (fin_cap_ep.kwN0 s a p b0 b1 b2 b3 b4 fin ex h (hc.1.1 p b0 b1 b2 b3 b4 rfl)) fun _ F => F.d
  | Notification n b0 b1 b2 =>
    obtain ⟨hn, hH⟩ := hc.1.2.1 n b0 b1 b2 rfl
    exact WP.spec_mono (fin_cap_ntfn.kwN0 s a n b0 b1 b2 fin ex h hn hH) fun _ F => F.d
  | Reply p g => exact fin_cap_reply.kwDN0 hA s a p g fin ex h (hc.1.2.2 p g rfl)
  | CNode p r g b => exact noop (fin_cap_cnode.same s a p r g b fin ex)
  | Thread p =>
    have hpT : p ∈ T := hc.2.2.2.2.2 p rfl
    obtain ⟨hpi, hv0⟩ := hpl.1 p rfl
    exact fin_cap_thread.kwDN0 hA s a p fin ex h hpT (hact p hpT) (Ne.symm hpi) hv0
  | IrqControl => exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inr (Or.inl rfl))))
  | IrqHandler i => simp [NatFinKind] at hk
  | Zombie p t n => exact noop (fin_cap_zombie.same s a p t n fin ex)
  | Domain => exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  | SchedContext p b =>
    obtain ⟨hp, hp0, hid⟩ := hpl.2 p b rfl
    exact WP.spec_mono (fin_cap_sc.kwN0 (Es := EH H) hA s a p b fin ex h hp hp0
      (fun h0 => hact _ (h.2.2.1.2.2.yt.1 p hp h0)) hid) fun _ F => F.d
  | SchedControl x =>
    exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))))))
  | Frame _ _ _ _ _ _ _ _ => simp [NatFinKind] at hk
  | PageTable _ _ _ _ => simp [NatFinKind] at hk
  | PageDirectory _ _ _ _ => simp [NatFinKind] at hk
  | Pdpt _ _ _ _ => simp [NatFinKind] at hk
  | Pml4 _ _ _ => simp [NatFinKind] at hk
  | Vcpu _ => simp [NatFinKind] at hk
  | Ept _ _ _ _ _ => simp [NatFinKind] at hk
  | AsidControl =>
    exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  | AsidPool _ _ => simp [NatFinKind] at hk
  | IoPortControl =>
    exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))
  | IoPort _ _ _ => simp [NatFinKind] at hk
  | TdxControl =>
    exact noop (fin_cap_noop.same s a _ fin ex (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))))

/-- (p3J gen 43) **The kernel-state block words** of `s0` (module docstring). -/
def KsBW (st : machine.Store S) [L : LawfulStore st] (s0 : S) (b : U64) : Prop :=
  ∃ o : U64, o.val < 13568 ∧ o.val % 8 = 0 ∧ b = core.num.U64.wrapping_add (L.ksb s0) o

/-- (p3J gen 43) A kernel-state block write after a `KsBW` step is a `KsBW` step. -/
theorem obj.ks_set.ksBW {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 s : S}
    (h0 : SchedQueuesInvX st T Cs Ω H X s0 Q R) (w : WritesIn st s0 s (KsBW st s0)) {o v : U64}
    (ho : o.val < 13568) (h8 : o.val % 8 = 0) :
    obj.ks_set st s o v ⦃ s' => WritesIn st s0 s' (KsBW st s0) ⦄ := by
  refine WP.spec_mono (obj.ks_set.spec s o v) fun s' e => ?_
  subst e
  rw [w.1]
  exact w.trans1 ((writesIn_wr (ks_aligned h0 ho h8)).mono fun b e => ⟨o, ho, h8, e⟩)

theorem ioport.apply.ksBW {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 s : S}
    (h0 : SchedQueuesInvX st T Cs Ω H X s0 Q R) (h : WritesIn st s0 s (KsBW st s0)) {w p : U64} {set : Bool}
    (hw : w.val < 1024) : ioport.apply st s w p set ⦃ s' => WritesIn st s0 s' (KsBW st s0) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ioport.apply ioport.word_off
  simp only [lift, bind_ok]
  refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 5344 + 8 * w.val) ?_ fun o ho => ?_
  · refine WP.spec_bind P0.Consts.layout.ks.IOPORT_BITMAP.spec fun b eb => ?_
    subst eb
    refine (WP.spec_ok _).2 ?_
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.obj.ks_get.p0 st s _ hS) fun v _ => ?_
  split
  · exact obj.ks_set.ksBW h0 h (by omega) (by omega)
  · exact obj.ks_set.ksBW h0 h (by omega) (by omega)

/-- (p3J gen 43) `set_mask` writes only IO-port bitmap words (P1 `ioport.set_mask.cur0`'s walk). -/
theorem ioport.set_mask.ksBW {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 s : S}
    (h0 : SchedQueuesInvX st T Cs Ω H X s0 Q R) (h : WritesIn st s0 s (KsBW st s0)) {f l : U64} {set : Bool}
    (hl : l.val < 65536) (hfl : f.val ≤ l.val) :
    ioport.set_mask st s f l set ⦃ s' => WritesIn st s0 s' (KsBW st s0) ⦄ := by
  unfold ioport.set_mask
  step as ⟨lw, hlw⟩
  step as ⟨hw, hhw⟩
  have b1 : lw.val ≤ hw.val := by
    rw [hlw, hhw, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_div_right hfl
  have b2 : hw.val < 1024 := by rw [hhw, Nat.shiftRight_eq_div_pow]; omega
  simp only [lift, bind_ok]
  split
  · refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
    exact ioport.apply.ksBW h0 h (by omega)
  · rename_i hne
    have b3 : lw.val < hw.val := by
      rcases Nat.lt_or_eq_of_le b1 with e | e
      · exact e
      · exact absurd (UScalar.eq_of_val_eq e) hne
    refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
    refine WP.spec_bind (ioport.apply.ksBW h0 h (by omega)) fun s1 h1 => ?_
    step as ⟨w, hw1⟩
    refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s0 s2 (KsBW st s0)) ?_ fun s2 h2 => ?_
    · unfold ioport.set_mask_loop
      apply loop.spec_decr_nat (measure := fun y : S × U64 => hw.val - y.2.val)
        (inv := fun y => WritesIn st s0 y.1 (KsBW st s0))
      · rintro ⟨s3, w3⟩ h3
        simp only at h3
        dsimp only
        unfold ioport.set_mask_loop.body
        split
        · rename_i hlt
          have hlt' : w3.val < hw.val := by simpa using hlt
          refine WP.spec_bind (ioport.apply.ksBW h0 h3 (by omega)) fun s4 h4 => ?_
          step as ⟨w4, hw4⟩
          exact ⟨h4, by omega⟩
        · exact (WP.spec_ok _).2 h3
      · exact h1
    · refine WP.spec_bind (P0.ioport.pattern.p0 _ _) fun _ _ => ?_
      exact ioport.apply.ksBW h0 h2 b2

/-- (p3J gen 43) **`post_cap_deletion` writes only kernel-state block words** (module docstring; P1
`objects.post_cap_deletion.cur0`'s walk). -/
theorem objects.post_cap_deletion.ksBW {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s : S} {a : A} {c : capability.Cap}
    (h0 : SchedQueuesInvX st T Cs Ω H X s Q R) (hi : ∀ i, c = .IrqHandler i → i.val < 128)
    (hp : ∀ f l o, c = .IoPort f l o → f.val ≤ l.val ∧ l.val < 65536) :
    objects.post_cap_deletion st ar s a c ⦃ r => WritesIn st s r.1 (KsBW st s) ⦄ := by
  unfold objects.post_cap_deletion
  cases c
  all_goals try exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · rename_i irq
    have hi := hi irq rfl
    unfold interrupt.deleted_irq_handler
    refine WP.spec_bind (Pₘ := fun r : S × A => WritesIn st s r.1 (KsBW st s)) ?_ ?_
    · unfold interrupt.set_irq_state interrupt.state_off
      simp only [lift, bind_ok]
      refine WP.spec_bind (Pₘ := fun o : U64 => o.val = 224 + 8 * irq.val) ?_ fun o ho => ?_
      · refine WP.spec_bind P0.Consts.layout.ks.IRQ_STATE.spec fun b eb => ?_
        subst eb
        refine (WP.spec_ok _).2 ?_
        simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (obj.ks_set.ksBW (v := interrupt.IRQ_INACTIVE) h0 (WritesIn.refl _ _) (by omega)
        (by omega)) fun s1 h1 => ?_
      exact WP.spec_bind (hA.mask_irq a irq _) fun a1 _ => (WP.spec_ok _).2 h1
    rintro ⟨s1, a1⟩ h1
    exact WP.spec_bind (hA.irq_free a1 irq) fun a2 _ => (WP.spec_ok _).2 h1
  · rename_i f l o
    obtain ⟨hfl, hl⟩ := hp f l o rfl
    unfold ioport.free_ioports
    exact WP.spec_bind (ioport.set_mask.ksBW h0 (WritesIn.refl _ _) hl hfl) fun s1 h1 => (WP.spec_ok _).2 h1

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- (p3J gen 43) **A cap of a `CKI` kind is `NatFinKind` or an IRQ handler cap** (module docstring). -/
theorem natFinKind_of_kw {c : capability.Cap} (h : SInvCk.KW (absCap c)) :
    P1.NatFinKind c ∨ ∃ i, c = .IrqHandler i := by
  cases c <;> simp_all [P1.NatFinKind, absCap, SInvCk.KW]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 43) **Every typed-heap slot of a `CKI` `JAtZ` state holds a `NatFinKind` or IRQ handler cap**
(module docstring). -/
theorem JAtZ.natFinKind_of_cki {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (hC : SInvCk.CKI σ) {x : U64} (hx : IsSlot Z.th x) :
    P1.NatFinKind (capV (L.mem s) x) ∨ ∃ i, capV (L.mem s) x = .IrqHandler i :=
  natFinKind_of_kw (Mc.kw_of_cki J hC hx)

/-- (p3J gen 43) **`finalise_cap` of a `NatFinKind` cap at a `JAtZ` state writes only `ProjW`** (module
docstring; hypotheses P1's deletion bundle `DelCapOK` / `FinPl` and `Cur0`'s action fact). -/
theorem JAtZ.finCapProjW (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {c : capability.Cap}
    (hc : P1.DelCapOK (P1.Heap.tcbs H) (P1.Heap.omega H) (P1.Heap.frame H) H (P1.Heap.replies H)
      (P1.Heap.ntfns H) c)
    (hpl : P1.FinPl st (P1.Heap.scs H) s c) (hact : ∀ y ∈ P1.Heap.tcbs H, L.actionW s ≠ y)
    (hk : P1.NatFinKind c) (fin ex : Bool) :
    objects.finalise_cap st arI s a c fin ex ⦃ r => P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.fin_cap.kwDN0 hA s a c fin ex J.blk hc hpl hact hk) fun _ F =>
    footDN_projW J.kern.heap h0.nodes F

/-- (p3J gen 43) **`post_cap_deletion` at a `JAtZ` state writes only `ProjW`** (module docstring). -/
theorem JAtZ.postCapDelProjW (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {c : capability.Cap}
    (hi : ∀ i, c = .IrqHandler i → i.val < 128)
    (hp : ∀ f l o, c = .IoPort f l o → f.val ≤ l.val ∧ l.val < 65536) :
    objects.post_cap_deletion st arI s a c ⦃ r => P1.WritesIn st s r.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  refine WP.spec_mono (P1.objects.post_cap_deletion.ksBW hA h0 hi hp) fun _ w => w.mono fun b hb => ?_
  obtain ⟨o, ho, -, rfl⟩ := hb
  have hv := P1.ks_val h0 ho
  exact Or.inr (Or.inl ⟨by rw [hv]; omega, by rw [hv]; omega⟩)

end

end Fl4Proofs.P3
