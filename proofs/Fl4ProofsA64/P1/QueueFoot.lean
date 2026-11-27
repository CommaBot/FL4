-- AArch64 port of Fl4Proofs.P1.QueueFoot (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: footprints.  `KW` is the set of words the kernel operations of P1 write:
the TCBs' words past their cap slots (`tcb::NUM_SLOTS` slots of `cte::SIZE`
bytes at the start of the object), the cores' node words, the frame words
`Sg` (reply objects, the SCs' `TCB`/`CORE`/`REPLY` words, the
notifications' frame words), the SC objects, and the queue words of the
endpoints and notifications `Es`.  A cap slot lies outside all of these (a
CNode slot is in a CNode, a TCB slot below offset 192 of its TCB, an IRQ slot
in the kernel-global area), so an operation with a `KW` footprint keeps every
cap slot.
-/
import Fl4ProofsA64.P1.QueueIpc
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- The words the kernel operations write (relative to the nodes of `s0`). -/
def KW (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 192 ≤ K.val ∧ K.val < 4096 ∧ K.val ≠ 3576 ∧ K.val ≠ 3584 ∧
    b = core.num.U64.wrapping_add y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ o.val ≠ 88 ∧ b = L.nodeAt s0 c o) ∨
  b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨
  (∃ e ∈ Es, b = epHeadA e ∨ b = epTSA e)

/-- A footprint inside `KW`. -/
abbrev Foot (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesIn st s s' (KW st T Cs Sg Scs Z Es s)

variable {Es : Set U64}

theorem KW.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : KW st T Cs Sg Scs Z Es s1 b) :
    KW st T Cs Sg Scs Z Es s0 b := by
  rcases h with h | ⟨c, hc, o, ho, h88, e⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, hc, o, ho, h88, by rw [e, nodeAt_of_ksb hk]⟩)
  · exact Or.inr (Or.inr h)

theorem KW.mono {s0 : S} {b : U64} {Es' : Set U64} (h : KW st T Cs Sg Scs Z Es s0 b) (hE : Es ⊆ Es') :
    KW st T Cs Sg Scs Z Es' s0 b := by
  rcases h with h | h | h | h | ⟨e, he, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e, hE he, h⟩)))

theorem Foot.refl (s : S) : Foot st T Cs Sg Scs Z Es s s := WritesIn.refl _ _

theorem Foot.trans {s₁ s₂ s₃ : S} (h₁ : Foot st T Cs Sg Scs Z Es s₁ s₂) (h₂ : Foot st T Cs Sg Scs Z Es s₂ s₃) :
    Foot st T Cs Sg Scs Z Es s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => KW.ksb h₁.1 hb

theorem Foot.mono {s s' : S} {Es' : Set U64} (h : Foot st T Cs Sg Scs Z Es s s') (hE : Es ⊆ Es') :
    Foot st T Cs Sg Scs Z Es' s s' :=
  WritesIn.mono h fun _ hb => KW.mono hb hE

theorem Foot.of {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) (hB : ∀ b, B b → KW st T Cs Sg Scs Z Es s b) :
    Foot st T Cs Sg Scs Z Es s s' := h.mono hB

theorem Foot.of' {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → KW st T Cs Sg Scs Z Es s b) : Foot st T Cs Sg Scs Z Es s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh)⟩

/-! ## The words of `KW` -/

theorem kw_field {s : S} {y K : U64} (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    KW st T Cs Sg Scs Z Es s (core.num.U64.wrapping_add y K) := Or.inl ⟨y, hy, K, hK, hK', hKd.1, hKd.2, rfl⟩

theorem kw_node {s : S} {c o : U64} (hc : c ∈ Cs) (ho : o.val < 4288) (h88 : o.val ≠ 88) :
    KW st T Cs Sg Scs Z Es s (L.nodeAt s c o) :=
  Or.inr (Or.inl ⟨c, hc, o, ho, h88, rfl⟩)

theorem kw_sg {s : S} {b : U64} (hb : b ∈ Sg) : KW st T Cs Sg Scs Z Es s b := Or.inr (Or.inr (Or.inl hb))

theorem kw_sc {s : S} {c b : U64} (hc : c ∈ Scs) (hb : InSC c (Z c) b) : KW st T Cs Sg Scs Z Es s b :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, hb⟩)))

theorem kw_ep {s : S} {e b : U64} (he : e ∈ Es) (hb : b = epHeadA e ∨ b = epTSA e) : KW st T Cs Sg Scs Z Es s b :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, hb⟩)))

theorem foot_wr {s : S} {a v : U64} (ha : Aligned a) (hk : KW st T Cs Sg Scs Z Es s a) :
    Foot st T Cs Sg Scs Z Es s (L.wr s a v) :=
  (writesIn_wr ha).mono fun b hb => hb ▸ hk

theorem foot_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584) :
    Foot st T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  foot_wr (field_aligned (hT y hy) hK' hK8) (kw_field hy hK hK' hKd)

theorem foot_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) : Foot st T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s c o) v) :=
  foot_wr (nodeAt_aligned hN ho h8) (kw_node hc ho h88)

theorem LinkOf.kw {s : S} {l : tcbqueue.Link} {W : List U64} {b : U64} (hW : ∀ w ∈ W, w ∈ T) (h : LinkOf l W b) :
    KW st T Cs Sg Scs Z Es s b := by
  obtain ⟨w, hw, e | e⟩ := h <;> subst e
  · rw [nextA_eq']; exact kw_field (hW w hw) (by cases l <;> simp [nextOff]) (by cases l <;> simp [nextOff])
      (by cases l <;> simp [nextOff])
  · rw [prevA_eq']; exact kw_field (hW w hw) (by cases l <;> simp [prevOff]) (by cases l <;> simp [prevOff])
      (by cases l <;> simp [prevOff])

theorem LawfulStore.NodeOf.kw {s : S} {c : U64} {P : Nat → Prop} {b : U64} (hc : c ∈ Cs) (hP : ∀ o, P o → o ≠ 88)
    (h : L.NodeOf s c P b) : KW st T Cs Sg Scs Z Es s b := by
  obtain ⟨o, hPo, ho, -, rfl⟩ := h; exact kw_node hc ho (hP _ hPo)

theorem LawfulStore.QFoot.kw {s : S} {W : List U64} {c : U64} {P : Nat → Prop} {t b : U64} (hW : ∀ w ∈ W, w ∈ T)
    (hc : c ∈ Cs) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (hP : ∀ o, P o → o ≠ 88) (h : L.QFoot s W c P t b) :
    KW st T Cs Sg Scs Z Es s b := by
  rcases h with h | h | h | h
  · exact h.kw hW
  · exact h.kw hc hP
  · subst h; rw [inqA_eq]; exact kw_field ht (by simp) (by simp) (by simp)
  · exact h.kw hcpu (fun o e => by omega)

theorem EpFoot.kw {s : S} {W : List U64} {e b : U64} (hW : ∀ w ∈ W, w ∈ T) (he : e ∈ Es) (h : EpFoot W e b) :
    KW st T Cs Sg Scs Z Es s b := by
  rcases h with h | h | h
  · exact h.kw hW
  · exact kw_ep he (Or.inl h)
  · exact kw_ep he (Or.inr h)

theorem InRing.kw {s : S} {c b : U64} (hc : c ∈ Scs) (h : InRing c (Z c) b) : KW st T Cs Sg Scs Z Es s b :=
  kw_sc hc h.inSC



/-! ## `KWB`: `KW` without the TCBs' IPC-buffer word (KENTRY-PLAN a6f)

`msg.lookup_ipc_buffer` reads a TCB's `IPC_BUFFER` word (offset 3512) and its
buffer cap slot (offsets 64 and 72). The slot words lie outside `KW`, but
offset 3512 is in `KW`'s TCB clause. No scheduler operation writes it, so `KWB`
leaves it out (as `KW` leaves out the debug links); a `KWB` footprint keeps
every TCB's buffer lookup (`BufKeep.of_footB`). -/

/-- `KW` with the TCBs' `IPC_BUFFER` word (offset 3512) left out. -/
def KWB (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s0 : S) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 192 ≤ K.val ∧ K.val < 4096 ∧ K.val ≠ 3576 ∧ K.val ≠ 3584 ∧ K.val ≠ 3512 ∧
    b = core.num.U64.wrapping_add y K) ∨
  (∃ c ∈ Cs, ∃ o : U64, o.val < 4288 ∧ o.val ≠ 88 ∧ b = L.nodeAt s0 c o) ∨
  b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨
  (∃ e ∈ Es, b = epHeadA e ∨ b = epTSA e)

/-- A footprint inside `KWB`. -/
abbrev FootB (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesIn st s s' (KWB st T Cs Sg Scs Z Es s)

theorem KWB.kw {s0 : S} {b : U64} (h : KWB st T Cs Sg Scs Z Es s0 b) : KW st T Cs Sg Scs Z Es s0 b := by
  rcases h with ⟨y, hy, K, h1, h2, h3, h4, -, e⟩ | h | h
  · exact Or.inl ⟨y, hy, K, h1, h2, h3, h4, e⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem KWB.ksb {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (h : KWB st T Cs Sg Scs Z Es s1 b) :
    KWB st T Cs Sg Scs Z Es s0 b := by
  rcases h with h | ⟨c, hc, o, ho, h88, e⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨c, hc, o, ho, h88, by rw [e, nodeAt_of_ksb hk]⟩)
  · exact Or.inr (Or.inr h)

theorem KWB.mono {s0 : S} {b : U64} {Es' : Set U64} (h : KWB st T Cs Sg Scs Z Es s0 b) (hE : Es ⊆ Es') :
    KWB st T Cs Sg Scs Z Es' s0 b := by
  rcases h with h | h | h | h | ⟨e, he, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e, hE he, h⟩)))

theorem FootB.foot {s s' : S} (h : FootB st T Cs Sg Scs Z Es s s') : Foot st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono h fun _ hb => hb.kw

theorem FootB.refl (s : S) : FootB st T Cs Sg Scs Z Es s s := WritesIn.refl _ _

theorem FootB.trans {s₁ s₂ s₃ : S} (h₁ : FootB st T Cs Sg Scs Z Es s₁ s₂) (h₂ : FootB st T Cs Sg Scs Z Es s₂ s₃) :
    FootB st T Cs Sg Scs Z Es s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => Or.elim hb id fun hb => KWB.ksb h₁.1 hb

theorem FootB.mono {s s' : S} {Es' : Set U64} (h : FootB st T Cs Sg Scs Z Es s s') (hE : Es ⊆ Es') :
    FootB st T Cs Sg Scs Z Es' s s' :=
  WritesIn.mono h fun _ hb => KWB.mono hb hE

theorem FootB.of {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B) (hB : ∀ b, B b → KWB st T Cs Sg Scs Z Es s b) :
    FootB st T Cs Sg Scs Z Es s s' := h.mono hB

theorem FootB.of' {s s' : S} {B : U64 → Prop} (h : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → KWB st T Cs Sg Scs Z Es s b) : FootB st T Cs Sg Scs Z Es s s' :=
  ⟨h.1, h.2.1, fun b hb hn => h.2.2 b hb fun hh => hn (hB b hb hh)⟩

theorem kwB_field {s : S} {y K : U64} (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584 ∧ K.val ≠ 3512) :
    KWB st T Cs Sg Scs Z Es s (core.num.U64.wrapping_add y K) :=
  Or.inl ⟨y, hy, K, hK, hK', hKd.1, hKd.2.1, hKd.2.2, rfl⟩

theorem kwB_node {s : S} {c o : U64} (hc : c ∈ Cs) (ho : o.val < 4288) (h88 : o.val ≠ 88) :
    KWB st T Cs Sg Scs Z Es s (L.nodeAt s c o) :=
  Or.inr (Or.inl ⟨c, hc, o, ho, h88, rfl⟩)

theorem kwB_sg {s : S} {b : U64} (hb : b ∈ Sg) : KWB st T Cs Sg Scs Z Es s b := Or.inr (Or.inr (Or.inl hb))

theorem kwB_sc {s : S} {c b : U64} (hc : c ∈ Scs) (hb : InSC c (Z c) b) : KWB st T Cs Sg Scs Z Es s b :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨c, hc, hb⟩)))

theorem kwB_ep {s : S} {e b : U64} (he : e ∈ Es) (hb : b = epHeadA e ∨ b = epTSA e) : KWB st T Cs Sg Scs Z Es s b :=
  Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, hb⟩)))

theorem footB_wr {s : S} {a v : U64} (ha : Aligned a) (hk : KWB st T Cs Sg Scs Z Es s a) :
    FootB st T Cs Sg Scs Z Es s (L.wr s a v) :=
  (writesIn_wr ha).mono fun b hb => hb ▸ hk

theorem footB_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hK8 : K.val % 8 = 0) (hKd : K.val ≠ 3576 ∧ K.val ≠ 3584 ∧ K.val ≠ 3512) :
    FootB st T Cs Sg Scs Z Es s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  footB_wr (field_aligned (hT y hy) hK' hK8) (kwB_field hy hK hK' hKd)

theorem footB_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (hc : c ∈ Cs) (ho : o.val < 4288)
    (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) : FootB st T Cs Sg Scs Z Es s (L.wr s (L.nodeAt s c o) v) :=
  footB_wr (nodeAt_aligned hN ho h8) (kwB_node hc ho h88)

theorem LinkOf.kwB {s : S} {l : tcbqueue.Link} {W : List U64} {b : U64} (hW : ∀ w ∈ W, w ∈ T) (h : LinkOf l W b) :
    KWB st T Cs Sg Scs Z Es s b := by
  obtain ⟨w, hw, e | e⟩ := h <;> subst e
  · rw [nextA_eq']; exact kwB_field (hW w hw) (by cases l <;> simp [nextOff]) (by cases l <;> simp [nextOff])
      (by cases l <;> simp [nextOff])
  · rw [prevA_eq']; exact kwB_field (hW w hw) (by cases l <;> simp [prevOff]) (by cases l <;> simp [prevOff])
      (by cases l <;> simp [prevOff])

theorem LawfulStore.NodeOf.kwB {s : S} {c : U64} {P : Nat → Prop} {b : U64} (hc : c ∈ Cs) (hP : ∀ o, P o → o ≠ 88)
    (h : L.NodeOf s c P b) : KWB st T Cs Sg Scs Z Es s b := by
  obtain ⟨o, hPo, ho, -, rfl⟩ := h; exact kwB_node hc ho (hP _ hPo)

theorem LawfulStore.QFoot.kwB {s : S} {W : List U64} {c : U64} {P : Nat → Prop} {t b : U64} (hW : ∀ w ∈ W, w ∈ T)
    (hc : c ∈ Cs) (hcpu : L.cpu s ∈ Cs) (ht : t ∈ T) (hP : ∀ o, P o → o ≠ 88) (h : L.QFoot s W c P t b) :
    KWB st T Cs Sg Scs Z Es s b := by
  rcases h with h | h | h | h
  · exact h.kwB hW
  · exact h.kwB hc hP
  · subst h; rw [inqA_eq]; exact kwB_field ht (by simp) (by simp) (by simp)
  · exact h.kwB hcpu (fun o e => by omega)

theorem EpFoot.kwB {s : S} {W : List U64} {e b : U64} (hW : ∀ w ∈ W, w ∈ T) (he : e ∈ Es) (h : EpFoot W e b) :
    KWB st T Cs Sg Scs Z Es s b := by
  rcases h with h | h | h
  · exact h.kwB hW
  · exact kwB_ep he (Or.inl h)
  · exact kwB_ep he (Or.inr h)

theorem InRing.kwB {s : S} {c b : U64} (hc : c ∈ Scs) (h : InRing c (Z c) b) : KWB st T Cs Sg Scs Z Es s b :=
  kwB_sc hc h.inSC

theorem FootB.of0 {s s' : S} (f : FootB st T Cs ∅ ∅ Z ∅ s s') : FootB st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono f fun b hb => by
    rcases hb with h | h | hm | ⟨c, hc, -⟩ | ⟨e, he, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd hm (Set.notMem_empty _)
    · exact absurd hc (Set.notMem_empty _)
    · exact absurd he (Set.notMem_empty _)


/-! ## Endpoint words outside a footprint -/

/-- The queue words of a heap endpoint or notification are outside `KW ∅`. -/
theorem ep_not_kw {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e b : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (he : H e = some .ep ∨ H e = some .ntfn) (hb : b = epHeadA e ∨ b = epTSA e) :
    ¬ KW st T Cs Sg Scs Z ∅ s b := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
  obtain ⟨hE, hEN, -⟩ := hEW.1 e heE
  have hΩ := hEW.2.2.1 e heE
  have hv : b.val = e.val ∨ b.val = e.val + 8 := by
    rcases hb with rfl | rfl
    · exact Or.inl epHeadA_val
    · exact Or.inr (epTSA_val hE)
  have hfit := hE.fits
  rintro (⟨y, hy, K, h1, h2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', -⟩)
  · rw [field_val (h.tcbs y hy) h2] at hv
    have := hE.disj y hy; omega
  · rw [nodeAt_val (h.nodes c hc) ho] at hv
    have := hEN.1 c hc; omega
  · have := hΩ b (hsub b hm); omega
  · have hal : Aligned b := by
      rcases hb with rfl | rfl
      · exact (ep_aligned hE).1
      · exact (ep_aligned hE).2
    have := hΩ b (hO.scW c hc b hal hin); omega
  · exact absurd he' (Set.notMem_empty e')

/-- **No `KW` word is a debug-list word** (`KW` leaves out the TCBs' debug
links and the nodes' debug-list heads). -/
theorem kw_not_dbg {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {b : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (hal : Aligned b) (hk : KW st T Cs Sg Scs Z Es s b) : ¬ DbgW st T Cs s b := by
  have hT := h.tcbs
  rcases hk with ⟨y, hy, K, h1, h2, h3, h4, e⟩ | ⟨c, hc, o, ho, ho88, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', hb⟩
  · subst e; exact notDbgW_field hT h.nodes hy h2 ⟨h3, h4⟩
  · subst e; exact notDbgW_node hT h.nodes hc ho ho88
  · exact notDbgW_out hT h.nodes (h.omega _ (hsub _ hm))
  · exact notDbgW_out hT h.nodes (h.omega _ (hO.scW c hc _ hal hin))
  · obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := h.eps
    have heE : e' ∈ E := (ty.2.2.1 e').2 (hE e' he')
    obtain ⟨hE', hEN, -⟩ := w1 e' heE
    obtain ⟨o1, o2⟩ := ep_out hE' hEN
    rcases hb with rfl | rfl
    · exact notDbgW_out hT h.nodes o1
    · exact notDbgW_out hT h.nodes o2

/-- A `KW` footprint keeps the debug lists typed. -/
theorem DbgTz.of_foot {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (f : Foot st T Cs Sg Scs Z Es s s') (D : DbgTz st T Cs s) : DbgTz st T Cs s' :=
  DbgTz.of_writes h.tcbs h.nodes f (fun _ hal hk => kw_not_dbg h hO hsub hE hal hk) D

/-! ### `KW` with no frame, SC or endpoint words (TCB fields and node words) -/

theorem kw0_not_dbg {s : S} {b : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hk : KW st T Cs ∅ ∅ Z ∅ s b) : ¬ DbgW st T Cs s b := by
  rcases hk with ⟨y, hy, K, h1, h2, h3, h4, rfl⟩ | ⟨c, hc, o, ho, ho88, rfl⟩ | hm | ⟨c, hc, -⟩ | ⟨e, he, -⟩
  · exact notDbgW_field hT hN hy h2 ⟨h3, h4⟩
  · exact notDbgW_node hT hN hc ho ho88
  · exact absurd hm (Set.notMem_empty _)
  · exact absurd hc (Set.notMem_empty _)
  · exact absurd he (Set.notMem_empty _)

theorem kw0_out {s : S} {a b : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (ha : OutsideObjs st T Cs s a) (hk : KW st T Cs ∅ ∅ Z ∅ s b) : b ≠ a := by
  rcases hk with ⟨y, hy, K, h1, h2, -, -, rfl⟩ | ⟨c, hc, o, ho, -, rfl⟩ | hm | ⟨c, hc, -⟩ | ⟨e, he, -⟩
  · exact fun e => out_ne_field ha hy (hT y hy) h2 (congrArg UScalar.val e)
  · exact fun e => out_ne_node ha hc (hN c hc) ho (congrArg UScalar.val e)
  · exact absurd hm (Set.notMem_empty _)
  · exact absurd hc (Set.notMem_empty _)
  · exact absurd he (Set.notMem_empty _)

/-- A footprint of TCB fields and node words keeps the debug lists typed. -/
theorem Foot0.dbg {s s' : S} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (f : Foot st T Cs ∅ ∅ Z ∅ s s') (D : DbgTz st T Cs s) : DbgTz st T Cs s' :=
  DbgTz.of_writes hT hN f (fun _ _ hk => kw0_not_dbg hT hN hk) D

/-- A footprint of TCB fields and node words keeps the other objects' words. -/
theorem Foot0.out {s s' : S} {a : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (f : Foot st T Cs ∅ ∅ Z ∅ s s') (ha : OutsideObjs st T Cs s a) : L.mem s' a = L.mem s a :=
  f.mem_eq ha.1 (fun hk => kw0_out hT hN ha hk rfl)

theorem Foot.of0 {s s' : S} (f : Foot st T Cs ∅ ∅ Z ∅ s s') : Foot st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono f fun b hb => by
    rcases hb with h | h | hm | ⟨c, hc, -⟩ | ⟨e, he, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd hm (Set.notMem_empty _)
    · exact absurd hc (Set.notMem_empty _)
    · exact absurd he (Set.notMem_empty _)

/-- A `KW ∅` footprint keeps the queue of a heap endpoint or notification. -/
theorem Foot.epQ {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {e : U64}
    (f : Foot st T Cs Sg Scs Z ∅ s s') (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (he : H e = some .ep ∨ H e = some .ntfn) :
    L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e) := by
  obtain ⟨E, EQ, hEW⟩ := h.eps
  have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
  obtain ⟨hE, -, -⟩ := hEW.1 e heE
  exact ⟨f.mem_eq (ep_aligned hE).1 (ep_not_kw h hO hsub he (Or.inl rfl)),
    f.mem_eq (ep_aligned hE).2 (ep_not_kw h hO hsub he (Or.inr rfl))⟩


/-! ## The receive buffer's lookup (moved from FastFaultInv, KENTRY-PLAN a6f) -/

/-- The IPC-buffer word of a TCB. -/
def ibA (t : U64) : U64 := core.num.U64.wrapping_add t 3512#u64
/-- The IPC-buffer cap slot of a TCB. -/
def sbA (t : U64) : U64 := core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_BUFFER layout.cte.SIZE)

theorem ipc_buffer_ok (s : S) (t : obj.Tcb) : obj.Tcb.ipc_buffer st t s = ok (L.mem s (ibA t)) := by
  have h : obj.Tcb.ipc_buffer st t s ⦃ r => r = L.mem s (ibA t) ⦄ := by
    unfold obj.Tcb.ipc_buffer; step*; simp_all [ibA]
  generalize obj.Tcb.ipc_buffer st t s = m at h ⊢
  cases m <;> simp_all [WP.spec_vis, WP.spec_div, WP.spec_ok]

theorem sbA_val {t : U64} (h : TcbAddr t) : (sbA t).val = t.val + 64 := by
  have := h.fits
  unfold sbA layout.tcb.SLOT_BUFFER layout.cte.SIZE
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
  all_goals omega

/-- **`lookup_ipc_buffer` reads three words**: the IPC-buffer word and the
buffer cap slot's two words (either receiver flag; lcv: the sender's buffer). -/
theorem lookup_buf_agreeB {s s' : S} {t : U64} (b : Bool) (h1 : L.mem s' (ibA t) = L.mem s (ibA t))
    (h2 : L.mem s' (sbA t) = L.mem s (sbA t))
    (h3 : L.mem s' (core.num.U64.wrapping_add (sbA t) 8#u64) = L.mem s (core.num.U64.wrapping_add (sbA t) 8#u64)) :
    msg.lookup_ipc_buffer st s' b t = msg.lookup_ipc_buffer st s b t := by
  unfold msg.lookup_ipc_buffer
  rw [ipc_buffer_ok, ipc_buffer_ok, h1]
  have hs : obj.Tcb.slot t layout.tcb.SLOT_BUFFER = ok (sbA t) := by simp [obj.Tcb.slot, lift, sbA]
  rw [hs]; simp only [bind_ok]
  have hc : obj.Slot.cap st (sbA t) s' = obj.Slot.cap st (sbA t) s := by
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, h2, h3]
  rw [hc]

/-- **`lookup_ipc_buffer` reads three words** (the receiver's lookup:
`lookup_buf_agreeB` at `true`). -/
theorem lookup_buf_agree {s s' : S} {t : U64} (h1 : L.mem s' (ibA t) = L.mem s (ibA t))
    (h2 : L.mem s' (sbA t) = L.mem s (sbA t))
    (h3 : L.mem s' (core.num.U64.wrapping_add (sbA t) 8#u64) = L.mem s (core.num.U64.wrapping_add (sbA t) 8#u64)) :
    msg.lookup_ipc_buffer st s' true t = msg.lookup_ipc_buffer st s true t :=
  lookup_buf_agreeB true h1 h2 h3

/-! ## The buffer words and their frame (KENTRY-PLAN a6f) -/

theorem sbA_field {y : U64} (h : TcbAddr y) : sbA y = core.num.U64.wrapping_add y 64#u64 :=
  UScalar.eq_of_val_eq (by rw [sbA_val h, field_val h (by simp)]; simp)

theorem sbA8_field {y : U64} (h : TcbAddr y) :
    core.num.U64.wrapping_add (sbA y) 8#u64 = core.num.U64.wrapping_add y 72#u64 := by
  apply UScalar.eq_of_val_eq
  have := h.fits
  rw [field_val h (by simp)]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, sbA_val h]
  omega

/-- The words `msg.lookup_ipc_buffer` reads for the TCBs of `T`: the
`IPC_BUFFER` word and the buffer cap slot's two words (`lookup_buf_agreeB`). -/
def BufW (T : Set U64) (b : U64) : Prop :=
  ∃ y ∈ T, b = ibA y ∨ b = sbA y ∨ b = core.num.U64.wrapping_add (sbA y) 8#u64

theorem BufW.field {b : U64} (hT : TcbPlaced T) (h : BufW T b) :
    ∃ y ∈ T, ∃ K : U64, (K.val = 3512 ∨ K.val = 64 ∨ K.val = 72) ∧ b = core.num.U64.wrapping_add y K := by
  obtain ⟨y, hy, e | e | e⟩ := h
  · exact ⟨y, hy, 3512#u64, Or.inl (by simp), e⟩
  · exact ⟨y, hy, 64#u64, Or.inr (Or.inl (by simp)), e.trans (sbA_field (hT y hy))⟩
  · exact ⟨y, hy, 72#u64, Or.inr (Or.inr (by simp)), e.trans (sbA8_field (hT y hy))⟩

/-- **`s'` keeps every buffer lookup of `T`**: the three words of each TCB. -/
def BufKeep (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s s' : S) : Prop :=
  ∀ y ∈ T, L.mem s' (ibA y) = L.mem s (ibA y) ∧ L.mem s' (sbA y) = L.mem s (sbA y) ∧
    L.mem s' (core.num.U64.wrapping_add (sbA y) 8#u64) = L.mem s (core.num.U64.wrapping_add (sbA y) 8#u64)

theorem BufKeep.refl (s : S) : BufKeep st T s s := fun _ _ => ⟨rfl, rfl, rfl⟩

theorem BufKeep.trans {s₁ s₂ s₃ : S} (h₁ : BufKeep st T s₁ s₂) (h₂ : BufKeep st T s₂ s₃) : BufKeep st T s₁ s₃ :=
  fun y hy => ⟨(h₂ y hy).1.trans (h₁ y hy).1, (h₂ y hy).2.1.trans (h₁ y hy).2.1,
    (h₂ y hy).2.2.trans (h₁ y hy).2.2⟩

/-- **The buffer fact**: every TCB of `T`'s receive-buffer lookup satisfies
`Bok` (the callers' `Bok` is `BufOK U`: the buffer's words are user words). -/
def BufFact (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (Bok : U64 → Prop) (s : S) : Prop :=
  ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ Bok ⦄

/-- **The buffer fact carries along `BufKeep`.** -/
theorem BufFact.keep {Bok : U64 → Prop} {s s' : S} (h : BufFact st T Bok s) (k : BufKeep st T s s') :
    BufFact st T Bok s' := fun y hy => by
  obtain ⟨k1, k2, k3⟩ := k y hy
  rw [lookup_buf_agree k1 k2 k3]; exact h y hy

/-- Writes away from the buffer words keep them. -/
theorem BufKeep.of_writes {s s' : S} {B : U64 → Prop} (hT : TcbPlaced T) (w : WritesIn st s s' B)
    (hB : ∀ b, Aligned b → B b → ¬ BufW T b) : BufKeep st T s s' := fun y hy => by
  have hy' := hT y hy
  have a1 : Aligned (ibA y) := field_aligned hy' (by simp) (by simp)
  have a2 : Aligned (sbA y) := by rw [sbA_field hy']; exact field_aligned hy' (by simp) (by simp)
  have a3 : Aligned (core.num.U64.wrapping_add (sbA y) 8#u64) := by
    rw [sbA8_field hy']; exact field_aligned hy' (by simp) (by simp)
  exact ⟨w.mem_eq a1 (fun hb => hB _ a1 hb ⟨y, hy, Or.inl rfl⟩),
    w.mem_eq a2 (fun hb => hB _ a2 hb ⟨y, hy, Or.inr (Or.inl rfl)⟩),
    w.mem_eq a3 (fun hb => hB _ a3 hb ⟨y, hy, Or.inr (Or.inr rfl)⟩)⟩

/-- A TCB field past the cap slots other than `IPC_BUFFER` is no buffer word. -/
theorem notBufW_field {y K : U64} (hT : TcbPlaced T) (hy : y ∈ T) (hK : 192 ≤ K.val) (hK' : K.val < 4096)
    (hKb : K.val ≠ 3512) : ¬ BufW T (core.num.U64.wrapping_add y K) := by
  intro h
  obtain ⟨y', hy', K', hK'v, e⟩ := h.field hT
  exact field_ne (hT y hy) (hT y' hy') hK' (by omega) (fun _ => by omega) e

theorem notBufW_node {s : S} {c o : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s c) (ho : o.val < 4288) :
    ¬ BufW T (L.nodeAt s c o) := by
  intro h
  obtain ⟨y, hy, K, hK, e⟩ := h.field hT
  exact node_ne_field hN ho hy (hT y hy) (by omega) e

theorem notBufW_out {s : S} {a : U64} (hT : TcbPlaced T) (ha : OutsideObjs st T Cs s a) : ¬ BufW T a := by
  intro h
  obtain ⟨y, hy, K, hK, e⟩ := h.field hT
  exact out_ne_field ha hy (hT y hy) (by omega) (congrArg UScalar.val e).symm

theorem notBufW_dbg {s : S} {b : U64} (hT : TcbPlaced T) (hN : ∀ c ∈ Cs, NodePlaced st T s c)
    (hb : DbgW st T Cs s b) : ¬ BufW T b := by
  rcases hb with ⟨y, hy, e | e⟩ | ⟨c, hc, e⟩
  · subst e; exact notBufW_field (K := 3576#u64) hT hy (by simp) (by simp) (by simp)
  · subst e; exact notBufW_field (K := 3584#u64) hT hy (by simp) (by simp) (by simp)
  · subst e; exact notBufW_node hT (hN c hc) (by simp [debug_val])

/-- **No `KWB` word is a buffer word** (as `kw_not_dbg`). -/
theorem kwB_notBufW {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {b : U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (hal : Aligned b) (hk : KWB st T Cs Sg Scs Z Es s b) :
    ¬ BufW T b := by
  have hT := h.tcbs
  rcases hk with ⟨y, hy, K, h1, h2, -, -, h5, e⟩ | ⟨c, hc, o, ho, -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', hb⟩
  · subst e; exact notBufW_field hT hy h1 h2 h5
  · subst e; exact notBufW_node hT (h.nodes c hc) ho
  · exact notBufW_out hT (h.omega _ (hsub _ hm))
  · exact notBufW_out hT (h.omega _ (hO.scW c hc _ hal hin))
  · obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := h.eps
    have heE : e' ∈ E := (ty.2.2.1 e').2 (hE e' he')
    obtain ⟨hE', hEN, -⟩ := w1 e' heE
    obtain ⟨o1, o2⟩ := ep_out hE' hEN
    rcases hb with rfl | rfl
    · exact notBufW_out hT o1
    · exact notBufW_out hT o2

/-- A footprint inside `KWB` and the debug-list words. -/
abbrev FootDB (st : machine.Store S) [L : LawfulStore st] (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64)
    (s s' : S) : Prop :=
  WritesIn st s s' (fun b => KWB st T Cs Sg Scs Z Es s b ∨ DbgW st T Cs s b)

theorem FootB.d {s s' : S} (f : FootB st T Cs Sg Scs Z Es s s') : FootDB st T Cs Sg Scs Z Es s s' :=
  WritesIn.mono f fun _ hb => Or.inl hb

theorem FootDB.trans {s₁ s₂ s₃ : S} (h₁ : FootDB st T Cs Sg Scs Z Es s₁ s₂)
    (h₂ : FootDB st T Cs Sg Scs Z Es s₂ s₃) : FootDB st T Cs Sg Scs Z Es s₁ s₃ :=
  WritesIn.mono (WritesIn.trans h₁ h₂) fun b hb => by
    rcases hb with hb | hb | hb
    · exact hb
    · exact Or.inl (KWB.ksb h₁.1 hb)
    · exact Or.inr (DbgW.ksb h₁.1 hb)

theorem FootDB.mono {s s' : S} {Es' : Set U64} (f : FootDB st T Cs Sg Scs Z Es s s') (hE : Es ⊆ Es') :
    FootDB st T Cs Sg Scs Z Es' s s' :=
  WritesIn.mono f fun _ hb => Or.elim hb (fun h => Or.inl (KWB.mono h hE)) Or.inr

/-- **A `KWB` footprint keeps every buffer lookup.** -/
theorem BufKeep.of_footB {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (f : FootB st T Cs Sg Scs Z Es s s') : BufKeep st T s s' :=
  BufKeep.of_writes h.tcbs f fun _ hal hk => kwB_notBufW h hO hsub hE hal hk

/-- **A `KWB`, debug-list and outside-word footprint keeps every buffer
lookup** (`U`: e.g. the IPC-buffer words of a full-state report). -/
theorem BufKeep.of_footDBU {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    {U : Set U64} (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn)
    (hU : ∀ b ∈ U, OutsideObjs st T Cs s b)
    (f : WritesIn st s s' (fun b => KWB st T Cs Sg Scs Z Es s b ∨ DbgW st T Cs s b ∨ b ∈ U)) : BufKeep st T s s' :=
  BufKeep.of_writes h.tcbs f fun _ hal hk => by
    rcases hk with hk | hk | hk
    · exact kwB_notBufW h hO hsub hE hal hk
    · exact notBufW_dbg h.tcbs h.nodes hk
    · exact notBufW_out h.tcbs (hU _ hk)

/-- **A `FootDB` footprint keeps every buffer lookup.** -/
theorem BufKeep.of_footDB {X : Set U64} {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInvX st T Cs Ω H X s Q R) (hO : ObjsOK st Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω)
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) (f : FootDB st T Cs Sg Scs Z Es s s') : BufKeep st T s s' :=
  BufKeep.of_footDBU (U := ∅) h hO hsub hE (fun _ hb => absurd hb (Set.notMem_empty _))
    (WritesIn.mono f fun _ hb => Or.elim hb Or.inl (fun hb => Or.inr (Or.inl hb)))


/-- **A `Foot` step that keeps every TCB's `IPC_BUFFER` word is a `FootB`
step** (e.g. a cancel or state change with its `KeepT0` field frame). -/
theorem FootB.of_foot {s s' : S} (f : Foot st T Cs Sg Scs Z Es s s')
    (hib : ∀ y ∈ T, L.mem s' (ibA y) = L.mem s (ibA y)) : FootB st T Cs Sg Scs Z Es s s' := by
  refine ⟨f.1, f.2.1, fun b hb hn => ?_⟩
  by_cases hk : KW st T Cs Sg Scs Z Es s b
  · rcases hk with ⟨y, hy, K, h1, h2, h3, h4, e⟩ | hk
    · by_cases h5 : K.val = 3512
      · have eK : K = 3512#u64 := UScalar.eq_of_val_eq (by simp [h5])
        subst eK e
        exact hib y hy
      · exact absurd (Or.inl ⟨y, hy, K, h1, h2, h3, h4, h5, e⟩) hn
    · exact absurd (Or.inr hk) hn
  · exact f.2.2 b hb hk

/-- A TCB field frame (every field but the `Ep` links, as `KeepT0.fld` /
`ntfn_state_all`) keeps the buffer words. -/
theorem BufKeep.of_fields {s s' : S} (hT : TcbPlaced T)
    (f : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3496 → K.val ≠ 3504 →
      L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)) :
    BufKeep st T s s' := fun y hy =>
  ⟨f y hy 3512#u64 (by simp) (by simp) (by simp) (by simp),
    by rw [sbA_field (hT y hy)]; exact f y hy 64#u64 (by simp) (by simp) (by simp) (by simp),
    by rw [sbA8_field (hT y hy)]; exact f y hy 72#u64 (by simp) (by simp) (by simp) (by simp)⟩

/-- `KeepT0` (the cancel / state-change frame) keeps the buffer words. -/
theorem KeepT0.bufKeep {t : U64} {s s' : S} (hT : TcbPlaced T) (k : KeepT0 st T Cs Rp Scs Nt t s s') :
    BufKeep st T s s' :=
  fun y hy =>
    ⟨k.fld y hy 3512#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩),
      by rw [sbA_field (hT y hy)]
         exact k.fld y hy 64#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩),
      by rw [sbA8_field (hT y hy)]
         exact k.fld y hy 72#u64 (by simp) (by simp) (by simp) (by simp) (fun _ => ⟨by simp, by simp⟩)⟩

/-! ## The current core's scheduler words -/

/-- The current core's `CUR_THREAD`, `IDLE_THREAD` and `SCHED_ACTION` words are kept. -/
def ANI (st : machine.Store S) [L : LawfulStore st] (s s' : S) : Prop :=
  L.actionW s' = L.actionW s ∧ L.idleW s' = L.idleW s ∧ L.curW s' = L.curW s

theorem ANI.refl (s : S) : ANI st s s := ⟨rfl, rfl, rfl⟩
theorem ANI.trans {s₁ s₂ s₃ : S} (h₁ : ANI st s₁ s₂) (h₂ : ANI st s₂ s₃) : ANI st s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.trans h₁.2.2⟩

theorem ani_wr {s : S} {a v : U64} {T : Set U64} (hN : NodePlaced st T s (L.cpu s)) (ha : Aligned a)
    (hn : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16) → a.val ≠ (L.nodeAt s (L.cpu s) o).val) :
    ANI st s (L.wr s a v) := by
  have nd : ∀ o : U64, (o.val = 0 ∨ o.val = 8 ∨ o.val = 16) →
      L.mem (L.wr s a v) (L.nodeAt (L.wr s a v) (L.cpu (L.wr s a v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho => by
      simp only [LawfulStore.cpu_wr, nodeAt_wr]
      exact L.mem_wr_ne ha (nodeAt_aligned hN (by omega) (by omega)) (hn o ho)
  exact ⟨by unfold LawfulStore.actionW; exact nd _ (by rw [act_val]; omega),
    by unfold LawfulStore.idleW; exact nd _ (by rw [idle8]; omega),
    by unfold LawfulStore.curW; exact nd _ (by rw [curth0]; omega)⟩

theorem ani_field {s : S} {y K v : U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hy : y ∈ T)
    (hK : K.val < 4096) (hK8 : K.val % 8 = 0) : ANI st s (L.wr s (core.num.U64.wrapping_add y K) v) :=
  ani_wr hN (field_aligned (hT y hy) hK hK8) fun o ho e =>
    node_ne_field hN (by omega) hy (hT y hy) hK (UScalar.eq_of_val_eq e).symm

theorem ani_out {s : S} {a v : U64} (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs)
    (ho : OutsideObjs st T Cs s a) : ANI st s (L.wr s a v) :=
  ani_wr hN ho.1 fun o h e => out_ne_node ho hc hN (by omega) e.symm

theorem ani_node {s : S} {c o v : U64} (hN : NodePlaced st T s c) (hN' : NodePlaced st T s (L.cpu s))
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) (hno : c = L.cpu s → o.val ≠ 0 ∧ o.val ≠ 8 ∧ o.val ≠ 16) :
    ANI st s (L.wr s (L.nodeAt s c o) v) :=
  ani_wr hN' (nodeAt_aligned hN ho h8) fun o' h e =>
    node_ne_node hN hN' ho (by omega) (fun hc => by have := hno hc; omega) e

/-! ## The scheduler queues -/

section queues
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

theorem sched.enqueue.kwB (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  refine WP.spec_mono (sched.enqueue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (fun h0 => h.notQ ht h0 hc hp)) fun s' hh => FootB.of hh.1 fun b hb => hb.kwB ?_ hc h.cur ht (fun o ho => by omega)
  intro w hw
  rcases List.mem_cons.1 hw with rfl | hw
  · exact ht
  · exact (hR1.1.rel _ hp).mem w hw

theorem sched.enqueue.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.enqueue st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.enqueue.kwB s t h ht) fun _ f => f.foot

theorem sched.dequeue.kwB (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  have hp := h.prio t ht
  have hR1 := h.ready _ hc
  exact WP.spec_mono (sched.dequeue.foot s t _ h.tcbs ht hp (h.nodes _ hc) (h.nodes _ h.cur) (hR1.1.rel _ hp)
    (h.queued t ht).1) fun s' hh => FootB.of hh.1 fun b hb => hb.kwB (hR1.1.rel _ hp).mem hc h.cur ht (fun o ho => by omega)

theorem sched.dequeue.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.dequeue st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.dequeue.kwB s t h ht) fun _ f => f.foot

theorem sched.release_remove.kwB (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hc := h.aff t ht
  exact WP.spec_mono (sched.release_remove.foot s t _ h.tcbs ht (h.nodes _ hc) (h.nodes _ h.cur) (h.release _ hc)
    (h.released t ht).1) fun s' hh => FootB.of hh.1 fun b hb => hb.kwB (h.release _ hc).mem hc h.cur ht (fun o ho => by unfold RelOffs at ho; omega)

theorem sched.release_remove.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.release_remove st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.release_remove.kwB s t h ht) fun _ f => f.foot

/-- A footprint keeps the placement of the current core's node. -/
theorem Foot.curN {s s' : S} {Es : Set U64} (f : Foot st T Cs Sg Scs Z Es s s') (hN : NodePlaced st T s (L.cpu s)) :
    NodePlaced st T s' (L.cpu s') := by rw [f.2.1]; exact hN.ksb f.1

theorem sched.set_action.kwB (s : S) (v : U64) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_action st s v ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_action.spec s v) fun s' e => by
    subst e; exact footB_node hN hc (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)

theorem sched.set_action.kw (s : S) (v : U64) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.set_action st s v ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_action.kwB s v hN hc) fun _ f => f.foot

theorem sched.schedule_tcb.kwB (s : S) (t : obj.Tcb) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.schedule_tcb st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.schedule_tcb
  step with sched.cur_thread.spec as ⟨t1, e1⟩
  step with tcb_eq.blk as ⟨b, eb⟩
  split
  · step with sched.action.spec as ⟨i, ei⟩
    split
    · step with sched.is_schedulable.spec as ⟨b1, eb1⟩
      split
      · exact (WP.spec_ok _).2 (FootB.refl _)
      · exact sched.set_action.kwB s _ hN hc
    · exact (WP.spec_ok _).2 (FootB.refl _)
  · exact (WP.spec_ok _).2 (FootB.refl _)

theorem sched.schedule_tcb.kw (s : S) (t : obj.Tcb) (hN : NodePlaced st T s (L.cpu s)) (hc : L.cpu s ∈ Cs) :
    sched.schedule_tcb st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.schedule_tcb.kwB s t hN hc) fun _ f => f.foot

theorem sched.set_thread_state.kwB (s : S) (t : obj.Tcb) (v : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) : sched.set_thread_state st s t v ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.set_thread_state
  refine WP.spec_bind (obj.Tcb.set_state.spec s t v) fun s1 e1 => ?_
  subst e1
  refine WP.spec_mono (sched.schedule_tcb.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) _ t (by rw [LawfulStore.cpu_wr]; exact (h.nodes _ h.cur).ksb (L.ksb_wr _ _ _))
    (by rw [LawfulStore.cpu_wr]; exact h.cur)) fun s2 f2 => ?_
  have f1 : FootB st T Cs Sg Scs Z Es s (L.wr s (stA t) v) := by
    rw [stA_eq]; exact footB_field h.tcbs ht (by simp) (by simp) (by simp) (by simp)
  exact f1.trans f2

theorem sched.set_thread_state.kw (s : S) (t : obj.Tcb) (v : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (ht : t ∈ T) : sched.set_thread_state st s t v ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.set_thread_state.kwB s t v h ht) fun _ f => f.foot

theorem sched.reschedule_required.kwB (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold sched.reschedule_required
  step with sched.action.spec as ⟨act, act_post⟩
  have hpart : (if (act != sched.ACTION_RESUME_CURRENT) = true then
      if (act != sched.ACTION_CHOOSE_NEW) = true then do
        let b ← sched.is_schedulable st s act
        if b = true then sched.enqueue st s act else ok s
      else ok s
    else ok s) ⦃ s1 => FootB st T Cs Sg Scs Z Es s s1 ⦄ := by
    split
    · split
      · rename_i h1 h2
        have hT : act ∈ T := by
          rcases h.action with e | e | e
          · rw [← act_post] at e; exfalso; rw [e, resume_val] at h1; simp at h1
          · rw [← act_post] at e; exfalso; rw [e, choose_val] at h2; simp at h2
          · rw [← act_post] at e; exact e
        step with sched.is_schedulable.spec as ⟨b, hb⟩
        split
        · exact sched.enqueue.kwB s act h hT
        · exact (WP.spec_ok _).2 (FootB.refl _)
      · exact (WP.spec_ok _).2 (FootB.refl _)
    · exact (WP.spec_ok _).2 (FootB.refl _)
  refine WP.spec_bind hpart fun s1 f1 => ?_
  exact WP.spec_mono (sched.set_action.kwB s1 _ (by rw [f1.2.1]; exact (h.nodes _ h.cur).ksb f1.1)
    (by rw [f1.2.1]; exact h.cur)) fun s2 f2 => f1.trans f2

theorem sched.reschedule_required.kw (s : S) (h : SchedQueuesInvX st T Cs Ω H X s Q R) :
    sched.reschedule_required st s ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.reschedule_required.kwB s h) fun _ f => f.foot

theorem sched.possible_switch_to.kwB (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  have hST : P0.StoreTotal st := L.total
  unfold sched.possible_switch_to sched.cur_domain
  step as ⟨i, ei⟩
  split
  · exact (WP.spec_ok _).2 (FootB.refl _)
  step as ⟨b, eb⟩
  split
  · exact (WP.spec_ok _).2 (FootB.refl _)
  step as ⟨i1, ei1⟩
  step as ⟨i2, ei2⟩
  split
  · exact sched.enqueue.kwB s t h ht
  step as ⟨i3, ei3⟩
  step as ⟨i4, ei4⟩
  split
  · exact sched.enqueue.kwB s t h ht
  step as ⟨i5, ei5⟩
  split
  · refine WP.spec_bind (WP.spec_and (sched.reschedule_required.inv s Q R h) (sched.reschedule_required.kwB (Sg := Sg) (Scs := Scs) (Z := Z) (Es := Es) s h)) ?_
    rintro s1 ⟨⟨⟨Q1, h1⟩, -, -⟩, f1⟩
    exact WP.spec_mono (sched.enqueue.kwB s1 t h1 ht) fun s2 f2 => f1.trans f2
  · exact sched.set_action.kwB s _ (h.nodes _ h.cur) h.cur

theorem sched.possible_switch_to.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R) (ht : t ∈ T) :
    sched.possible_switch_to st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (sched.possible_switch_to.kwB s t h ht) fun _ f => f.foot

theorem endpoint.unblock_sporadic.kwB (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold endpoint.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootB.of w3 fun b hb => ?_
      rcases hb with hb | rfl
      · exact hb.kwB hiS
      · exact kwB_node h.cur (by rw [rp]; omega) (by rw [rp]; omega)
    · exact (WP.spec_ok _).2 (FootB.refl _)
  · exact (WP.spec_ok _).2 (FootB.refl _)

theorem endpoint.unblock_sporadic.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    endpoint.unblock_sporadic st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (endpoint.unblock_sporadic.kwB s t h hX hS ht) fun _ f => f.foot

theorem notification.unblock_sporadic.kwB (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold notification.unblock_sporadic
  step with obj.Tcb.sc.spec as ⟨i, i_post⟩
  step with sporadic.sc_sporadic.spec as ⟨b1, b1_post⟩
  split
  · rename_i hb1
    obtain ⟨hi0, hsp⟩ := b1_post hb1
    have hbt : L.mem s (scA t) ≠ 0#u64 := by rw [← i_post]; exact hi0
    obtain ⟨hiS, -, -⟩ := hX.2.2.bound t ht hbt
    rw [← i_post] at hiS
    have hW : RefillsWF st s i (Z i) := hS.wf hiS (hS.spor i hiS hsp)
    have hSCin : SCin st s Ω i (Z i) := ⟨hW, hX.1.scW i hiS⟩
    step with sched.cur_sc.spec as ⟨c4, _⟩
    step with sc_ne.spec as ⟨b2⟩
    split
    · have hN' := h.nodes _ h.cur
      have rp : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
      have aR : Aligned (L.nodeA s layout.node.REPROGRAM) := nodeAt_aligned hN' (by rw [rp]; omega) (by rw [rp])
      have oR : Outside (L.nodeA s layout.node.REPROGRAM) i (Z i) :=
        hSCin.node_out h.omega h.cur hN' (by rw [rp]; omega) (by rw [rp])
      refine WP.spec_mono (sporadic.unblock_check.fr hW ⟨aR, oR⟩) fun s3 w3 => FootB.of w3 fun b hb => ?_
      rcases hb with hb | rfl
      · exact hb.kwB hiS
      · exact kwB_node h.cur (by rw [rp]; omega) (by rw [rp]; omega)
    · exact (WP.spec_ok _).2 (FootB.refl _)
  · exact (WP.spec_ok _).2 (FootB.refl _)

theorem notification.unblock_sporadic.kw (s : S) (t : obj.Tcb) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hS : SCsOK st T Ω Sg Scs Z Ac s) (ht : t ∈ T) :
    notification.unblock_sporadic st s t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (notification.unblock_sporadic.kwB s t h hX hS ht) fun _ f => f.foot

theorem ipc.reply_unlink.kwB (s : S) (r t : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht : t ∈ T) :
    ipc.reply_unlink st s r t ⦃ s' => FootB st T Cs Sg Scs Z Es s s' ⦄ := by
  unfold ipc.reply_unlink
  refine WP.spec_bind (obj.Reply.set_tcb.spec s r 0#u64) fun s1 e1 => ?_
  subst e1
  have hm : rTcbA r ∈ Ω := hsub _ (hX.1.tcbW hr)
  have ha := (h.omega _ hm).1
  have h1 := inv_of_free h ((writesIn_wr (v := 0#u64) ha).mono fun b hb => hb ▸ Or.inl hm)
  exact WP.spec_mono (sched.set_thread_state.kwB _ t _ h1 ht) fun s2 f2 =>
    (footB_wr ha (kwB_sg (hX.1.tcbW hr))).trans f2

theorem ipc.reply_unlink.kw (s : S) (r t : U64) (h : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hX : XInv st T Cs Ω Sg Rp Scs Nt Z s) (hsub : ∀ b ∈ Sg, b ∈ Ω) (hr : r ∈ Rp) (ht : t ∈ T) :
    ipc.reply_unlink st s r t ⦃ s' => Foot st T Cs Sg Scs Z Es s s' ⦄ :=
  WP.spec_mono (ipc.reply_unlink.kwB s r t h hX hsub hr ht) fun _ f => f.foot

end queues

end

end Fl4ProofsA64.P1
