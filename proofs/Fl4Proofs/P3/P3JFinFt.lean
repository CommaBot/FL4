/-
P3 (p3J gen 42): **bucket 3, more per-kind finaliser footprints inside `ProjW`**: a reply cap's finalisation in
`KWN ∅ False` plus the debug-list words (`FootDN ∅ False`, P1 QueueReplyPop's `fin_reply.blk` walk mirrored), and the
cap kinds whose finalisation writes no memory at all (CNode, Zombie, Null, Untyped, the control caps). FL4
`objects.rs` `finalise_cap_object`: the `Reply` arm (`reply_remove` of a thread blocked on the reply, `cancel_ipc`
of one blocked on receive with it), the `CNode` arm (returns a Zombie cap, no store write), the `Zombie` arm and the
control caps (no-op).

* **`fin_reply.kwDN0`** (`reply_remove` by P3JReplyFtN's `ipc.reply_remove.kwDN0`, `DbgTz` from `XInv`;
  `cancel_ipc` by P3JRecvFtN's `ipc.cancel_ipc.kwN0`), **`fin_cap_reply.kwDN0`**.
* **`fin_cap_cnode.same`**, **`fin_cap_zombie.same`**, **`fin_cap_noop.same`**: the store is unchanged.
* P3: `footDN_projW` (a `FootDN ∅ False` step over `H`'s sets is a `ProjW` step: `kwN_projW` / `dbgW_projW`),
  **`JAtZ.finReplyProjW`**, **`JAtZ.finCnodeProjW`**, **`JAtZ.finZombieProjW`**, **`JAtZ.finNoopProjW`**.

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P3.P3JEpFt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P2.Stall

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}
variable {Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- (p3J gen 42) **A reply cap's object finalisation in `FootDN ∅ False`** (P1 `fin_reply.blk`). -/
theorem fin_reply.kwDN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x : Bool) (fin : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp) :
    objects.finalise_cap_object st ar s a (.Reply p x) fin ⦃ r =>
      FootDN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  unfold objects.finalise_cap_object
  dsimp only
  split
  swap
  · exact (WP.spec_ok _).2 (FootDN.refl _)
  refine WP.spec_bind (obj.Reply.tcb.blk s p) fun i ei => ?_
  step with obj.Tcb.is_null.spec as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootDN.refl _)
  rename_i hb
  have hi0 : i ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
  have hX := h.2.2.1
  obtain ⟨-, hiT, -, -⟩ := hX.2.1.back p hp (by rw [← ei]; exact hi0)
  rw [← ei] at hiT
  have hD : DbgTz st T Cs s := ⟨hX.2.2.tm.dn, hX.2.2.tm.dp, hX.2.2.tm.dh⟩
  step with obj.Tcb.state.spec as ⟨v, ev⟩
  split
  · refine WP.spec_bind (ipc.reply_remove.kwDN0 (Es := EH H) hA s a p i h.1.choose_spec.choose_spec hX
      h.2.2.2.2.sub hD hp hiT) ?_
    rintro ⟨s1, a1⟩ f1
    exact (WP.spec_ok _).2 f1
  split
  · obtain ⟨⟨Q, R, h0⟩, hB, -, hS, hSg⟩ := h
    refine WP.spec_bind (ipc.cancel_ipc.kwN0 s a i h0 hiT hX hSg.sub (fun hs => by
        obtain ⟨h1, h2⟩ := hX.2.1.reply i hiT hs
        exact ⟨h1, h2, hX.2.1.next _ h1, hX.2.1.prev _ h1⟩) (fun hs h0' => (hX.2.1.recv i hiT hs h0').1)) ?_
    rintro ⟨s1, a1⟩ f1
    simp only [WP.uncurry'_pair] at f1
    exact (WP.spec_ok _).2 f1.d
  · exact (WP.spec_ok _).2 (FootDN.refl _)

/-- (p3J gen 42) **`finalise_cap` of a reply cap in `FootDN ∅ False`** (module docstring). -/
theorem fin_cap_reply.kwDN0 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (s : S) (a : A) (p : U64)
    (x : Bool) (fin ex : Bool) (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hp : p ∈ Rp) :
    objects.finalise_cap st ar s a (.Reply p x) fin ex ⦃ r =>
      FootDN st ∅ False T Cs Sg Scs Z (EH H) s r.2.1 ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  exact fin_reply.kwDN0 hA s a p x fin h hp

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- (p3J gen 42) **`finalise_cap` of a CNode cap writes no memory** (module docstring). -/
theorem fin_cap_cnode.same {A : Type} {ar : machine.Arch A} (s : S) (a : A) (p r g b : U64) (fin ex : Bool) :
    objects.finalise_cap st ar s a (.CNode p r g b) fin ex ⦃ x => x.2.1 = s ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  simp only [objects.finalise_cap_object, bind_ok]
  split
  · simp only [lift, bind_ok]
    step as ⟨n, hn⟩
  · exact (WP.spec_ok _).2 rfl

/-- (p3J gen 42) **`finalise_cap` of a Zombie cap writes no memory** (module docstring). -/
theorem fin_cap_zombie.same {A : Type} {ar : machine.Arch A} (s : S) (a : A) (p t n : U64) (fin ex : Bool) :
    objects.finalise_cap st ar s a (.Zombie p t n) fin ex ⦃ x => x.2.1 = s ⦄ := by
  rw [fin_cap_eq_obj (by simp)]
  simp only [objects.finalise_cap_object, bind_ok]
  exact (WP.spec_ok _).2 rfl

/-- (p3J gen 42) **`finalise_cap` of a Null / Untyped / control cap writes no memory** (module docstring). -/
theorem fin_cap_noop.same {A : Type} {ar : machine.Arch A} (s : S) (a : A) (c : capability.Cap) (fin ex : Bool)
    (hc : c = .Null ∨ (∃ x y z w, c = .Untyped x y z w) ∨ c = .IrqControl ∨ c = .Domain ∨
      (∃ x, c = .SchedControl x) ∨ c = .AsidControl ∨ c = .IoPortControl ∨ c = .TdxControl) :
    objects.finalise_cap st ar s a c fin ex ⦃ x => x.2.1 = s ⦄ := by
  rcases hc with rfl | ⟨_, _, _, _, rfl⟩ | rfl | rfl | ⟨_, rfl⟩ | rfl | rfl | rfl <;>
    simp [objects.finalise_cap, objects.finalise_cap_object]

end

end Fl4Proofs.P1

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- (p3J gen 42) **A `FootDN ∅ False` step over `H`'s sets is a `ProjW` step** (module docstring). -/
theorem footDN_projW {s s' : S} (hH : P1.HeapOK H) (hNP : ∀ c ∈ Cs, P1.NodePlaced st (P1.Heap.tcbs H) s c)
    (F : P1.FootDN st ∅ False (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (P1.EH H)
      s s') : P1.WritesIn st s s' (Mc.ProjW (L := L) H Cs s) :=
  (P1.WritesA.w F).mono fun _ hb => hb.1.elim (fun hk => Mc.kwN_projW hH hNP ⟨hk, hb.2⟩)
    (fun hd => Mc.dbgW_projW hH hNP hd)

/-- (p3J gen 42) **`finalise_cap` of a reply cap of `Z.R` at a `JAtZ` state writes only `ProjW`** (module
docstring). -/
theorem JAtZ.finReplyProjW (hA : P0.ArchTotal arI) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {p : U64} (hp : p ∈ Z.R) (x fin ex : Bool) :
    objects.finalise_cap st arI s a (.Reply p x) fin ex ⦃ r =>
      P1.WritesIn st s r.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ := by
  have h0 := J.blk.1.choose_spec.choose_spec
  exact WP.spec_mono (P1.fin_cap_reply.kwDN0 hA s a p x fin ex J.blk (J.zH.2.2.1 p hp)) fun _ F =>
    footDN_projW J.kern.heap h0.nodes F

/-- (p3J gen 42) **`finalise_cap` of a CNode cap writes only `ProjW`** (it writes nothing). -/
theorem finCnodeProjW (s : S) (a : A) (p r g b : U64) (fin ex : Bool) :
    objects.finalise_cap st arI s a (.CNode p r g b) fin ex ⦃ x =>
      P1.WritesIn st s x.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ :=
  WP.spec_mono (P1.fin_cap_cnode.same s a p r g b fin ex) fun _ e => e ▸ P1.WritesIn.refl _ _

/-- (p3J gen 42) **`finalise_cap` of a Zombie cap writes only `ProjW`** (it writes nothing). -/
theorem finZombieProjW (s : S) (a : A) (p t n : U64) (fin ex : Bool) :
    objects.finalise_cap st arI s a (.Zombie p t n) fin ex ⦃ x =>
      P1.WritesIn st s x.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ :=
  WP.spec_mono (P1.fin_cap_zombie.same s a p t n fin ex) fun _ e => e ▸ P1.WritesIn.refl _ _

/-- (p3J gen 42) **`finalise_cap` of a Null / Untyped / control cap writes only `ProjW`** (it writes nothing). -/
theorem finNoopProjW (s : S) (a : A) (c : capability.Cap) (fin ex : Bool)
    (hc : c = .Null ∨ (∃ x y z w, c = .Untyped x y z w) ∨ c = .IrqControl ∨ c = .Domain ∨
      (∃ x, c = .SchedControl x) ∨ c = .AsidControl ∨ c = .IoPortControl ∨ c = .TdxControl) :
    objects.finalise_cap st arI s a c fin ex ⦃ x =>
      P1.WritesIn st s x.2.1 (Mc.ProjW (L := L) H Cs s) ⦄ :=
  WP.spec_mono (P1.fin_cap_noop.same s a c fin ex hc) fun _ e => e ▸ P1.WritesIn.refl _ _

end

end Fl4Proofs.P3
