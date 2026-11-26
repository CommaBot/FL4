-- AArch64 port of Fl4Proofs.P1.QueueXferFoot (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: the message transfer's footprint (`XferFootOK`): `do_ipc_transfer`
writes only the receiver's user context and IPC buffer (`XferFoot`), cap-slot
words apart from the first 256 bytes of the kernel-global block (a granted
cap's receive slot and its CDT neighbours, `XferKG`), and the sender's SC's
words (a timeout fault's `CONSUMED`).  QueueXfer's steps, on `XSF`: `XS` with
the footprint from the transfer's start.

a64: the footprint also has the sender's `FAULT_W1` word (`trap_extra_mrs`, QueueXfer): `XferWA … sx`
(`XferW` plus that word), `XferStepW` (the writes `RS` / `RD` must survive: `XferRegW`, SC words and a TCB's
`FAULT_W1` word; `XferKG.step` / `.stepD` are stated over it, the A64 shape of x86's), `XSF` carries the
sender `sx` and its frame is `XferFrA`; `XSF.fw1`, `trap_extra_mrs_loop.xsf`, `trap_extra_mrs.xsf`; the
theorem is **`xferFootOK_ofA`** (`XferFootOKA`, the footprint `XferWA … snd`). Named premises: none beyond
the placement structures `XferHyps` / `XferKG` (hypotheses of the theorem, as on x86; `XferKG.step` /
`.stepD` are [P]-class placement facts about P3's `RS` / `RD`, now also over `FAULT_W1` writes).
-/
import Fl4ProofsA64.P1.QueueXfer
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

/-- The word at `b` lies apart from the first 256 bytes of the kernel-global
block at `k`. -/
def KG (k b : U64) : Prop := b.val + 8 ≤ k.val ∨ k.val + 256 ≤ b.val

/-- The words the transfer writes besides cap slots and SC words: the
receiver's registers (TCB offsets in `[256, 3328)`) and user words. -/
def XferRegW (T U : Set U64) (b : U64) : Prop :=
  (∃ y ∈ T, ∃ K : U64, 256 ≤ K.val ∧ K.val < 3328 ∧ K.val % 8 = 0 ∧ b = core.num.U64.wrapping_add y K) ∨ b ∈ U

theorem XferRegW.foot {T U : Set U64} {b : U64} (h : XferRegW T U b) : XferFoot T U b := by
  rcases h with ⟨y, hy, K, -, h2, h3, e⟩ | h
  · exact Or.inl ⟨y, hy, K, h2, h3, e⟩
  · exact Or.inr h

/-- The transfer's words: the receiver's user context and IPC buffer, cap-slot
words apart from the kernel-global block's first 256 bytes, SC words. -/
def XferW (T U Ω Sg Scs : Set U64) (Z : U64 → Nat) (k b : U64) : Prop :=
  XferFoot T U b ∨ (CapW T Ω Sg b ∧ KG k b) ∨ (∃ c ∈ Scs, InSC c (Z c) b)

/-- a64: the transfer's words (`XferW`) and the sender `sx`'s `FAULT_W1` word. -/
def XferWA (T U Ω Sg Scs : Set U64) (Z : U64 → Nat) (k sx b : U64) : Prop :=
  XferW T U Ω Sg Scs Z k b ∨ b = core.num.U64.wrapping_add sx 3392#u64

/-- a64: the writes `RS` and `RD` are kept by: registers and user words, SC words, a TCB's `FAULT_W1`. -/
def XferStepW (T U Scs : Set U64) (Z : U64 → Nat) (b : U64) : Prop :=
  XferRegW T U b ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨ ∃ y ∈ T, b = core.num.U64.wrapping_add y 3392#u64

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

theorem WritesIn.and {s s' : S} {A B : U64 → Prop} (h1 : WritesIn st s s' A) (h2 : WritesIn st s s' B) :
    WritesIn st s s' (fun b => A b ∧ B b) :=
  ⟨h1.1, h1.2.1, fun b hb hn => by
    by_cases ha : A b
    · exact h2.2.2 b hb fun hb' => hn ⟨ha, hb'⟩
    · exact h1.2.2 b hb ha⟩

/-- `XS` with the footprint from `s0`. -/
def XSF (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (U : Set U64) (RS : S → S → Prop) (Ac X : Set U64) (Q : U64 → U64 → List U64)
    (R : U64 → List U64) (sx : U64) (s0 s : S) : Prop :=
  XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s ∧
    (XferFrA st T Rp sx s0 s ∧ WritesIn st s0 s (XferWA T U Ω Sg Scs Z (L.ksb s0) sx) ∧ RS s0 s ∧
      ∀ s1 s2 : S, RS s0 s1 → WritesIn st s1 s2 (XferStepW T U Scs Z) →
        RS s0 s2)

variable {U X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {RS : S → S → Prop} {P3Ok : S → Prop} {sx : U64}
  {RD : S → U64 → Prop}

theorem XSF.xs {s0 s : S} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) :
    XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R sx s0 s :=
  ⟨h.1, h.2.1, h.2.2.1.mono fun _ hb => by
    rcases hb with (hb | hb | hb) | e
    exacts [Or.inl (Or.inl hb), Or.inl (Or.inr (Or.inl hb.1)), Or.inl (Or.inr (Or.inr hb)), Or.inr e]⟩

theorem XSF.ksb {s0 s : S} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) : L.ksb s = L.ksb s0 :=
  h.2.1.2.2.2.2.2.2

theorem XSF.start {s : S} (h : XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s) (h0 : RS s s)
    (hst : ∀ s1 s2 : S, RS s s1 → WritesIn st s1 s2 (XferStepW T U Scs Z) →
      RS s s2) :
    XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s s := ⟨h, XferFrA.refl _ s, WritesIn.refl s _, h0, hst⟩

theorem XSF.rs {s0 s : S} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) : RS s0 s := h.2.2.2.1

/-- A register or user-word write. -/
theorem XSF.foot {s0 s s' : S} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hw : WritesIn st s s' (XferRegW T U)) : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' := by
  have h' := XS.foot h.xs (hw.mono fun _ hb => hb.foot)
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans hw).mono (fun b hb => hb.elim id fun hb => Or.inl (Or.inl hb.foot)),
    h.2.2.2.2 _ _ h.rs (hw.mono fun b hb => Or.inl hb), h.2.2.2.2⟩

/-- A write of cap-slot words apart from the kernel-global block's first 256 bytes. -/
theorem XSF.capw {s0 s s' : S} {B : U64 → Prop} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hw : WritesIn st s s' B) (hB : ∀ b, B b → CapW T Ω Sg b ∧ KG (L.ksb s0) b) (hrs : RS s0 s') :
    XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' := by
  have h' := XS.capw h.xs hw fun b hb => (hB b hb).1
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans hw).mono (fun b hb => hb.elim id fun hb => Or.inl (Or.inr (Or.inl (hB b hb)))),
    hrs, h.2.2.2.2⟩

/-- A write of an SC's `CONSUMED` word. -/
theorem XSF.consumed {s0 s : S} {c v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hc : c ∈ Scs) :
    XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 (L.wr s (core.num.U64.wrapping_add c layout.sc.CONSUMED) v) := by
  have h' := XS.consumed (v := v) h.xs hc
  have hO := h.1.2.2.1.1
  obtain ⟨hP, hz⟩ := hO.sc c hc
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  have hal : Aligned (core.num.U64.wrapping_add c layout.sc.CONSUMED) := by unfold Aligned; rw [hv, hcv]; omega
  have hin : InSC c (Z c) (core.num.U64.wrapping_add c layout.sc.CONSUMED) := ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans (writesIn_wr (v := v) hal)).mono (fun b hb =>
    hb.elim id fun e => Or.inl (Or.inr (Or.inr ⟨c, hc, e ▸ hin⟩))),
    h.2.2.2.2 _ _ h.rs ((writesIn_wr (v := v) hal).mono fun b e => Or.inr (Or.inl ⟨c, hc, e ▸ hin⟩)), h.2.2.2.2⟩

/-- a64: the sender's `FAULT_W1` write (`XS.fw1`). -/
theorem XSF.fw1 {s0 s : S} {v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hs : sx ∈ T) :
    XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 (L.wr s (core.num.U64.wrapping_add sx 3392#u64) v) := by
  have h' := XS.fw1 (v := v) h.xs hs
  have ha : Aligned (core.num.U64.wrapping_add sx 3392#u64) := field_aligned (h.1.1.tcbs sx hs) (by simp) (by simp)
  have hw := writesIn_wr (st := st) (s := s) (v := v) ha
  exact ⟨h'.1, h'.2.1, (h.2.2.1.trans hw).mono (fun b hb => hb.elim id fun e => Or.inr e),
    h.2.2.2.2 _ _ h.rs (hw.mono fun b e => Or.inr (Or.inr ⟨sx, hs, e⟩)), h.2.2.2.2⟩

/-- The slot `src` is one of the extra caps the transfer's sender looked up at
the transfer's start `s0`. -/
def ExtraFrom (st : machine.Store S) [L : LawfulStore st] (T : Set U64) (s0 : S) (src : U64) : Prop :=
  ∃ y ∈ T, ∃ (b : U64) (tag : msginfo.MessageInfo) (ex : Aeneas.Std.Array obj.Slot 3#usize),
    ipc.lookup_extra_caps st s0 y b tag = ok (.Ok ex) ∧ src ∈ ex.val ∧ src ≠ 0#u64

/-- The placement facts of the transfer's footprint (P3's), at states related
by `RS` to the transfer's start (P3: a typed heap the state agrees with): the
receive slot and the words the CDT insert of a granted cap writes lie apart
from the first 256 bytes of the kernel-global block (they are CNode, TCB or
IRQ-node slots); the insert and the transfer's other writes keep `RS`. -/
structure XferKG (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (RS : S → S → Prop) (RD : S → U64 → Prop) : Prop where
  slot : ∀ Ac X Q R (s0 s : S) (y b : U64), XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s → RS s0 s → y ∈ T →
    ipc.get_receive_slot st s y b ⦃ d => d = 0#u64 ∨ (KG (L.ksb s) d ∧ RD s d) ⦄
  ins : ∀ Ac X Q R (s0 s : S) (src dest : U64) (cap c : capability.Cap), XI st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s →
    RS s0 s → RD s dest → ExtraFrom st T s0 src → obj.Slot.cap st src s = ok cap →
    objects.derive_cap st s src cap = ok (.Ok c) → c ≠ .Null →
    CapW T Ω Sg src → CapW T Ω Sg dest → KG (L.ksb s) dest →
    cdt.insert st s c src dest ⦃ s' => WritesIn st s s' (KG (L.ksb s)) ∧ RS s0 s' ⦄
  /-- `RS` is kept by the transfer's other writes: user context, IPC buffer, SC words. -/
  step : ∀ s0 s s' : S, RS s0 s → WritesIn st s s' (XferStepW T U Scs Z) →
    RS s0 s'
  /-- The receive slot's `RD` is kept by the same writes. -/
  stepD : ∀ (s s' : S) (d : U64), RD s d →
    WritesIn st s s' (XferStepW T U Scs Z) → RD s' d

theorem obj.Tcb.set_reg.xsf {s0 s : S} {y r v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hy : y ∈ T)
    (hr : r.val < 384) :
    obj.Tcb.set_reg st y s r v ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' ⦄ := by
  have hT := h.1.1.tcbs
  refine WP.spec_mono (obj.Tcb.set_reg.wrK s y r v (hT y hy) hr) fun s' ⟨K, hK, e⟩ => ?_
  subst e
  exact h.foot ((writesIn_wr (field_aligned (hT y hy) (by omega) (by omega))).mono fun b e =>
    Or.inl ⟨y, hy, K, by omega, by omega, by omega, e⟩)

theorem msg.buf_set.xsf {s0 s : S} {buf i v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hb : BufOK U buf) (h0 : buf ≠ 0#u64) (hi : i.val < 128) :
    msg.buf_set st s buf i v ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact h.foot ((writesIn_wr (h.1.2.2.2.2.2 _ hu).1.1).mono fun b e => Or.inr (e ▸ hu))

theorem msg.buf_set.rw {s0 s : S} {buf i v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hb : BufOK U buf) (h0 : buf ≠ 0#u64) (hi : i.val < 128) :
    msg.buf_set st s buf i v ⦃ s' => WritesIn st s s' (XferRegW T U) ⦄ := by
  unfold msg.buf_set
  simp only [lift, bind_ok]
  refine WP.spec_mono (LawfulStore.write_spec s _ v) fun s' e => ?_
  subst e
  have hu := hb h0 i hi
  exact (writesIn_wr (h.1.2.2.2.2.2 _ hu).1.1).mono fun b e => Or.inr (e ▸ hu)

theorem msg.set_mr.xsf {s0 s : S} {y buf i v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ∧ r.1.val ≤ i.val + 4 ⦄ := by
  unfold msg.set_mr
  split
  · have hreg : ∀ j, msg.msg_register j ⦃ r => r.val < 384 ⦄ := fun j => by
      unfold msg.msg_register
      split; · simp [layout.reg.X2]
      split; · simp [layout.reg.X3]
      split; · simp [layout.reg.X4]
      simp [layout.reg.X5]
    refine WP.spec_bind (hreg i) fun r hr => ?_
    refine WP.spec_bind (obj.Tcb.set_reg.xsf (v := v) h hy hr) fun s1 h1 => ?_
    try simp only [lift, bind_ok]
    refine (WP.spec_ok _).2 ⟨h1, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  · split
    · rename_i hne
      have h0 : buf ≠ 0#u64 := by simpa using hne
      simp only [lift, bind_ok]
      have hi1 : (core.num.U64.wrapping_add i 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
      refine WP.spec_bind (msg.buf_set.xsf (v := v) h hb h0 hi1) fun s1 h1 => ?_
      refine (WP.spec_ok _).2 ⟨h1, ?_⟩
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · exact (WP.spec_ok _).2 ⟨h, by simp [msg.N_MSG_REGISTERS]⟩

theorem msg.copy_mrs_loop0.xsf {s0 s : S} {snd rcv n i : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hr : rcv ∈ T) :
    msg.copy_mrs_loop0 st s snd rcv n i ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop0
  apply loop.spec_decr_nat (measure := fun y => 4 - y.2.val)
    (inv := fun y => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 y.1)
  · rintro ⟨s1, i1⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop0.body
    split
    · split
      · rename_i _ hi
        have hi' : i1.val < 4 := by simpa [msg.N_MSG_REGISTERS] using hi
        refine WP.spec_bind (msg.msg_register.lt i1) fun rg hrg => ?_
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 rg hS) fun v _ => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xsf (v := v) h1 hr hrg) fun s2 h2 => ?_
        step as ⟨i2, hi2⟩
        exact ⟨h2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem msg.copy_mrs_loop1.xsf {s0 s : S} {sb rb n i : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hb : BufOK U rb) (h0 : rb ≠ 0#u64) :
    msg.copy_mrs_loop1 st s sb rb n i ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold msg.copy_mrs_loop1
  apply loop.spec_decr_nat (measure := fun y => 120 - y.2.val)
    (inv := fun y => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold msg.copy_mrs_loop1.body
    split
    · split
      · rename_i _ hi
        have hi' : j.val < 120 := by simpa [msg.MSG_MAX_LENGTH] using hi
        step
        have hi2 := i1_post
        refine WP.spec_bind (P0.msg.buf_get.p0 st s1 sb i1 hS) fun v _ => ?_
        refine WP.spec_bind (msg.buf_set.xsf (v := v) h1 hb h0 (by omega)) fun s2 h2 => ?_
        exact (WP.spec_ok _).2 ⟨h2, by first | omega | (dsimp only; omega)⟩
      · exact (WP.spec_ok _).2 h1
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem msg.copy_mrs.xsf {s0 s : S} {snd sb rcv rb n : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hr : rcv ∈ T) (hb : BufOK U rb) :
    msg.copy_mrs st s snd sb rcv rb n ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ := by
  unfold msg.copy_mrs
  refine WP.spec_bind (msg.copy_mrs_loop0.xsf (snd := snd) (n := n) (i := 0#u64) h hr) ?_
  rintro ⟨s1, i⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  split
  · exact (WP.spec_ok _).2 h1
  rename_i h0 _
  exact msg.copy_mrs_loop1.xsf h1 hb h0

theorem ipc.transfer_caps_loop.xsf (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (K : XferKG st T Cs Ω H Sg Rp Scs Nt Z U RS RD) {s0 s : S}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rb : U64} {out : msginfo.MessageInfo} {dest i : U64}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hG : ∀ s', XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s')
    (hx : ∀ sl ∈ extra.val, sl = 0#u64 ∨ CapW T Ω Sg sl) (hxp : ∀ sl ∈ extra.val, sl ≠ 0#u64 → ExtraFrom st T s0 sl)
    (hd : dest = 0#u64 ∨ (CapW T Ω Sg dest ∧ KG (L.ksb s0) dest ∧ RD s dest))
    (hb : BufOK U rb) (h0 : rb ≠ 0#u64) :
    ipc.transfer_caps_loop st s extra ep rb out dest i ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.transfer_caps_loop
  apply loop.spec_decr_nat (measure := fun y => 3 - y.2.2.2.val)
    (inv := fun y => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 y.1 ∧ (y.2.2.1 = 0#u64 ∨ (CapW T Ω Sg y.2.2.1 ∧ KG (L.ksb s0) y.2.2.1 ∧ RD y.1 y.2.2.1)))
  · rintro ⟨s1, o1, d1, j⟩ ⟨h1, hd1⟩
    simp only at h1 hd1
    dsimp only
    unfold ipc.transfer_caps_loop.body
    split
    · rename_i hj
      have hj' : j.val < 3 := by simpa using hj
      have hc : (UScalar.cast .Usize j).val = j.val := by
        have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        simp only [UScalar.cast_val_eq, UScalar.size, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by omega)
      have hl : (UScalar.cast .Usize j).val < extra.val.length := by
        rw [hc, extra.property]; simp; omega
      simp only [lift, bind_ok]
      refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra _ hl) fun sl hsl => ?_
      simp only [obj.Slot.is_null, bind_ok]
      split
      · exact (WP.spec_ok _).2 h1
      rename_i hsl0
      refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra _ hl) fun slot hslot => ?_
      have hsx : ExtraFrom st T s0 slot := hxp slot (hslot ▸ List.getElem_mem hl) fun e => hsl0 (by
        rw [hsl, ← hslot, e]; rfl)
      have hsw : CapW T Ω Sg slot := by
        rcases hx slot (hslot ▸ List.getElem_mem hl) with e | e
        · have e' : sl = 0#u64 := by rw [hsl, ← hslot]; exact e
          exact absurd (by simp [e']) hsl0
        · exact e
      refine WP.spec_bind (spec_eq' (P0.obj.Slot.cap.p0 st slot s1 hS)) fun cap ⟨hcap, _⟩ => ?_
      refine WP.spec_bind (P0.ipc.unwrapped_badge.p0 cap ep) fun o _ => ?_
      rcases o with _ | badge
      · simp only [obj.Slot.is_null, bind_ok]
        split
        · exact (WP.spec_ok _).2 h1
        rename_i hd0
        have hdw : CapW T Ω Sg d1 ∧ KG (L.ksb s0) d1 ∧ RD s1 d1 := hd1.resolve_left fun e => hd0 (by simp [e])
        refine WP.spec_bind (spec_eq' (P0.objects.derive_cap.p0 st s1 slot cap hS)) fun r ⟨hdc, _⟩ => ?_
        rcases r with c | _
        · simp only
          refine WP.spec_bind (spec_eq' (P0.capability.Cap.is_null.p0 c)) fun b2 ⟨hb2, _⟩ => ?_
          split
          · exact (WP.spec_ok _).2 h1
          rename_i hb2f
          have hcn : c ≠ .Null := fun e => by subst e; simp [capability.Cap.is_null] at hb2; subst hb2; exact hb2f rfl
          refine WP.spec_bind (WP.spec_and (E.ins _ _ _ _ s1 c slot d1 (hG s1 h1) h1.1 hsw hdw.1)
            (K.ins _ _ _ _ s0 s1 slot d1 cap c h1.1 h1.rs hdw.2.2 hsx hcap hdc hcn hsw hdw.1 (by rw [h1.ksb]; exact hdw.2.1)))
            fun s2 ⟨hw2, hk2, hr2⟩ => ?_
          step
          exact ⟨h1.capw (hw2.and hk2) (fun b hb => ⟨hb.1, by rw [← h1.ksb]; exact hb.2⟩) hr2, Or.inl trivial,
            by omega⟩
        · exact (WP.spec_ok _).2 h1
      · simp only [msg.BUF_CAPS, msg.BUF_USER_DATA, msg.MSG_MAX_LENGTH]
        step
        step
        try simp only [lift, bind_ok]
        have hix : (core.num.U64.wrapping_add i3 j).val < 128 := by
          simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
        refine WP.spec_bind (WP.spec_and (msg.buf_set.xsf (v := badge) h1 hb h0 hix)
          (msg.buf_set.rw (v := badge) h1 hb h0 hix)) fun s2 ⟨h2, w2⟩ => ?_
        step*
        refine ⟨h2, ?_, by omega⟩
        rcases hd1 with e | ⟨e1, e2, e3⟩
        · exact Or.inl e
        · exact Or.inr ⟨e1, e2, K.stepD _ _ _ e3 (w2.mono fun b hb => Or.inl hb)⟩
    · exact (WP.spec_ok _).2 h1
  · exact ⟨h, hd⟩

theorem ipc.transfer_caps.xsf (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (K : XferKG st T Cs Ω H Sg Rp Scs Nt Z U RS RD) {s0 s : S}
    {info : msginfo.MessageInfo} {extra : Aeneas.Std.Array obj.Slot 3#usize} {ep rcv rb : U64}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hr : rcv ∈ T)
    (hG : ∀ s', XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s')
    (hx : ∀ sl ∈ extra.val, sl = 0#u64 ∨ CapW T Ω Sg sl) (hxp : ∀ sl ∈ extra.val, sl ≠ 0#u64 → ExtraFrom st T s0 sl)
    (hb : BufOK U rb) :
    ipc.transfer_caps st s info extra ep rcv rb ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ := by
  unfold ipc.transfer_caps
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun out _ => ?_
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun s1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  split
  · exact (WP.spec_ok _).2 h
  rename_i h0
  refine WP.spec_bind (WP.spec_and (E.slot _ _ _ _ s rcv rb (hG s h) h.1 hr) (K.slot _ _ _ _ s0 s rcv rb h.1 h.rs hr))
    fun dest ⟨hd1, hd2⟩ => ?_
  have hd : dest = 0#u64 ∨ (CapW T Ω Sg dest ∧ KG (L.ksb s0) dest ∧ RD s dest) := by
    rcases hd1 with e | e
    · exact Or.inl e
    · rcases hd2 with e' | e'
      · exact Or.inl e'
      · exact Or.inr ⟨e, by rw [← h.ksb]; exact e'.1, e'.2⟩
  refine WP.spec_bind (ipc.transfer_caps_loop.xsf (out := out) (i := 0#u64) E K h hG hx hxp hd hb h0) ?_
  rintro ⟨s2, o2, i⟩ h2
  exact (WP.spec_ok _).2 h2

theorem ipc.do_normal_transfer.xsf (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) (K : XferKG st T Cs Ω H Sg Rp Scs Nt Z U RS RD) {s0 : S}
    {snd sb ep badge rcv rb : U64} {grant : Bool}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s0) (hs : snd ∈ T) (hr : rcv ∈ T) (hb : BufOK U rb)
    (hG : ∀ s', XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' → XG st T Cs Ω H Sg Scs Z P3Ok s') :
    ipc.do_normal_transfer st s0 snd sb ep badge grant rcv rb ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (P0.msg.msg_info.p0 st s0 snd hS) fun tag _ => ?_
  have noX : ∀ sl ∈ ipc.NO_EXTRA_CAPS.val, sl ≠ 0#u64 → ExtraFrom st T s0 sl := fun sl hsl h0 => by
    rcases (ipc.no_extra (T := T) (Ω := Ω) (Sg := Sg) sl hsl) with e | e
    · exact absurd e h0
    · exfalso; simp [ipc.NO_EXTRA_CAPS, Aeneas.Std.Array.make] at hsl; exact h0 hsl
  refine WP.spec_bind (Pₘ := fun e : Aeneas.Std.Array obj.Slot 3#usize => (∀ sl ∈ e.val, sl = 0#u64 ∨ CapW T Ω Sg sl) ∧
    ∀ sl ∈ e.val, sl ≠ 0#u64 → ExtraFrom st T s0 sl) ?_ fun extra ⟨hx, hxp⟩ => ?_
  · split
    · refine WP.spec_bind (spec_eq' (E.extra _ _ _ _ s0 snd sb tag (hG s0 h) h.1 hs)) fun r ⟨hlk, hr'⟩ => ?_
      rcases r with e | _
      · exact (WP.spec_ok _).2 ⟨hr' e rfl, fun sl hsl h0 => ⟨snd, hs, sb, tag, e, hlk, hsl, h0⟩⟩
      · exact (WP.spec_ok _).2 ⟨ipc.no_extra, noX⟩
    · exact (WP.spec_ok _).2 ⟨ipc.no_extra, noX⟩
  refine WP.spec_bind (msg.copy_mrs.xsf (snd := snd) (sb := sb) (n := tag.length) h hr hb) ?_
  rintro ⟨n, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (ipc.transfer_caps.xsf (info := tag) (ep := ep) E K h1 hr hG hx hxp hb) ?_
  rintro ⟨out, s2⟩ h2
  simp only at h2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s3 => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xsf h3 hr (by simp [layout.reg.BADGE, layout.reg.X0])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xsf (v := w) h2 hr (by simp [layout.reg.MSG_INFO, layout.reg.X1])

theorem faults.copy_mrs_fault_loop0.xsf {s0 s : S} {snd rcv : U64} {regs : Slice U64} {i : Usize}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hr : rcv ∈ T) (hi : i.val ≤ (Slice.len regs).val) :
    faults.copy_mrs_fault_loop0 st s snd rcv regs i ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.1 ∧
      r.2.val ≤ (Slice.len regs).val ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop0
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 y.1 ∧ y.2.val ≤ (Slice.len regs).val)
  · rintro ⟨s1, j⟩ ⟨h1, hj1⟩
    simp only at h1 hj1
    dsimp only
    unfold faults.copy_mrs_fault_loop0.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      simp only [lift, bind_ok]
      split
      · step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
        refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
        refine WP.spec_bind (msg.msg_register.lt _) fun rg hrg => ?_
        refine WP.spec_bind (obj.Tcb.set_reg.xsf (v := v) h1 hr hrg) fun s2 h2 => ?_
        step as ⟨j2, hj2⟩
        exact ⟨h2, by omega, by omega⟩
      · exact (WP.spec_ok _).2 ⟨h1, hj1⟩
    · rename_i hj
      exact (WP.spec_ok _).2 ⟨h1, hj1⟩
  · exact ⟨h, hi⟩

theorem faults.copy_mrs_fault_loop1.xsf {s0 s : S} {snd buf : U64} {regs : Slice U64} {i : Usize}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64)
    (hl : (Slice.len regs).val < 127) :
    faults.copy_mrs_fault_loop1 st s snd regs buf i ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.copy_mrs_fault_loop1
  apply loop.spec_decr_nat (measure := fun y => (Slice.len regs).val - y.2.val)
    (inv := fun y => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.copy_mrs_fault_loop1.body
    dsimp only
    split
    · rename_i hj
      have hj' : j.val < (Slice.len regs).val := by simpa using hj
      step with Aeneas.Std.Slice.index_usize_spec as ⟨r0, _⟩
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
      simp only [lift, bind_ok]
      have hc : (UScalar.cast .U64 j).val = j.val := by
        have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        have := j.hBounds
        simp only [UScalar.cast_val_eq, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)
      have hix : (core.num.U64.wrapping_add (UScalar.cast .U64 j) 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hc]; omega
      refine WP.spec_bind (msg.buf_set.xsf (v := v) h1 hb h0 hix) fun s2 h2 => ?_
      step as ⟨j2, hj2⟩
      exact ⟨h2, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

theorem faults.copy_mrs_fault.xsf {s0 s : S} {snd rcv buf : U64} {regs : Slice U64}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hr : rcv ∈ T) (hb : BufOK U buf)
    (hl : (Slice.len regs).val < 127) :
    faults.copy_mrs_fault st s snd rcv regs buf ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' ⦄ := by
  unfold faults.copy_mrs_fault
  refine WP.spec_bind (faults.copy_mrs_fault_loop0.xsf (snd := snd) (regs := regs) (i := 0#usize) h hr (by simp)) ?_
  rintro ⟨s1, i⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · rename_i hne
    exact faults.copy_mrs_fault_loop1.xsf h1 hb (by simpa using hne) hl
  · exact (WP.spec_ok _).2 h1

theorem faults.set_mrs_lookup_failure.xsf {s0 s : S} {rcv buf off : U64} {lf : error.LookupFault}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hr : rcv ∈ T) (hb : BufOK U buf) (ho : off.val < 124) :
    faults.set_mrs_lookup_failure st s rcv buf lf off ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ := by
  unfold faults.set_mrs_lookup_failure
  have hk : ∀ k : U64, k.val < 4 → (core.num.U64.wrapping_add off k).val < 127 := fun k hk => by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  refine WP.spec_bind (P0.error.LookupFault.type_code.p0 lf) fun i _ => ?_
  refine WP.spec_bind (msg.set_mr.xsf (v := i) h hr hb (by omega)) ?_
  rintro ⟨i1, s1⟩ ⟨h1, -⟩
  simp only at h1
  try simp only [WP.uncurry'_pair]
  split
  · exact (WP.spec_ok _).2 h1
  · try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xsf h1 hr hb (hk 1#u64 (by simp))) fun r hr' => hr'.1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xsf h1 hr hb (hk 1#u64 (by simp))) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xsf h2 hr hb (hk 2#u64 (by simp))) fun r hr' => hr'.1
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xsf h1 hr hb (hk 1#u64 (by simp))) ?_
    rintro ⟨_, s2⟩ ⟨h2, -⟩
    simp only at h2
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    refine WP.spec_bind (msg.set_mr.xsf h2 hr hb (hk 2#u64 (by simp))) ?_
    rintro ⟨_, s3⟩ ⟨h3, -⟩
    simp only at h3
    try simp only [WP.uncurry'_pair]
    try simp only [lift, bind_ok]
    exact WP.spec_mono (msg.set_mr.xsf h3 hr hb (hk 3#u64 (by simp))) fun r hr' => hr'.1

theorem schedcontext.update_consumed.xsf {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} {a : A}
    {c : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hc : c ∈ Scs) :
    schedcontext.update_consumed st ar s a c ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ := by
  unfold schedcontext.update_consumed
  step with obj.Sc.consumed.spec as ⟨x, _hx⟩
  split
  · step as ⟨y, hy⟩
    refine WP.spec_bind (obj.Sc.set_consumed.spec' s c y) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ => (WP.spec_ok _).2 (h.consumed hc)
  · refine WP.spec_bind (obj.Sc.set_consumed.spec' s c 0#u64) fun s1 e1 => ?_
    subst e1
    exact WP.spec_bind (hA.ticks_to_us a _) fun i _ => (WP.spec_ok _).2 (h.consumed hc)

/-- Some `set_mr`s in a row, ending the computation. -/
theorem set_mr_lastF {s0 s : S} {y buf i v : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hy : y ∈ T) (hb : BufOK U buf) (hi : i.val < 127) :
    msg.set_mr st s y buf i v ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ :=
  WP.spec_mono (msg.set_mr.xsf h hy hb hi) fun _ h' => h'.1

/-- a64: `trap_extra_mrs`'s copy (`trap_extra_mrs_loop.xs`). -/
theorem faults.trap_extra_mrs_loop.xsf {s0 s : S} {snd buf : U64} {i : Usize}
    (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s) (hb : BufOK U buf) (h0 : buf ≠ 0#u64) :
    faults.trap_extra_mrs_loop st s snd buf i ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.trap_extra_mrs_loop
  apply loop.spec_decr_nat (measure := fun y => 24 - y.2.val)
    (inv := fun y => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 y.1)
  · rintro ⟨s1, j⟩ h1
    simp only at h1
    dsimp only
    unfold faults.trap_extra_mrs_loop.body
    have hl24 : (Slice.len (Array.to_slice faults.TRAP_EXTRA_MESSAGE)).val = 24 := by simp
    simp only [lift, bind_ok]
    split
    · rename_i hj
      have hj' : j.val < 24 := by rw [← hl24]; simpa using hj
      have hl : j.val < faults.TRAP_EXTRA_MESSAGE.val.length := by rw [faults.TRAP_EXTRA_MESSAGE.property]; simpa using hj'
      refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec _ j hl) fun r0 _ => ?_
      refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s1 r0 hS) fun v _ => ?_
      try simp only [lift, bind_ok]
      have hc : (UScalar.cast .U64 j).val = j.val := by
        have : 2 ^ System.Platform.numBits ≤ 2 ^ 64 := by
          rcases System.Platform.numBits_eq with e | e <;> simp [e]
        have := j.hBounds
        simp only [UScalar.cast_val_eq, UScalarTy.numBits]
        exact Nat.mod_eq_of_lt (by simp [Usize.size] at *; omega)
      have hix : (core.num.U64.wrapping_add (core.num.U64.wrapping_add faults.TRAP_EXTRA_FIRST
          (UScalar.cast .U64 j)) 1#u64).val < 128 := by
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, hc, faults.TRAP_EXTRA_FIRST]; omega
      refine WP.spec_bind (msg.buf_set.xsf (v := v) h1 hb h0 hix) fun s2 h2 => ?_
      step as ⟨j2, hj2⟩
      exact ⟨h2, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h

/-- a64: **`trap_extra_mrs`** on `XSF` (`trap_extra_mrs.xs`). -/
theorem faults.trap_extra_mrs.xsf {s0 s : S} {buf n : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 s)
    (hs : sx ∈ T) (hb : BufOK U buf) :
    faults.trap_extra_mrs st s sx buf n ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R sx s0 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.trap_extra_mrs
  split
  · exact (WP.spec_ok _).2 h
  rename_i h0
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (P0.obj.Tcb.flags.p0 st sx s hS) fun fl _ => ?_
  simp only [lift, bind_ok]
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (obj.Tcb.set_fault_w1.wr s sx 1#u64) fun s1 e1 => ?_
  subst e1
  refine WP.spec_bind (faults.trap_extra_mrs_loop.xsf (snd := sx) (i := 0#usize) (h.fw1 hs) hb h0) fun s2 h2 => ?_
  exact WP.spec_bind P0.faults.TRAP_FULL_LENGTH.p0 fun _ _ => (WP.spec_ok _).2 h2

set_option hygiene false in
/-- One `set_mr` of the receiver, from the state of `hcur`. -/
local macro "smrF" : tactic => `(tactic| (
  refine WP.spec_bind (msg.set_mr.xsf hcur hr hb (by simp)) ?_
  rintro ⟨_, s'⟩ ⟨hcur, -⟩
  try simp only at hcur
  try simp only [WP.uncurry'_pair]))

theorem faults.set_mrs_fault.xsf {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {snd rcv buf : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hb : BufOK U buf) :
    faults.set_mrs_fault st ar s a snd rcv buf ⦃ r => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold faults.set_mrs_fault
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hS) fun ty _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w0.p0 st snd s hS) fun w0 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w1.p0 st snd s hS) fun w1 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_w2.p0 st snd s hS) fun w2 _ => ?_
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st snd s _ hS) fun pc _ => ?_
  have hcur := h
  split
  · smrF; smrF; smrF
    refine WP.spec_bind (P0.faults.lookup_failure.p0 st s' snd hS) fun lf _ => ?_
    exact faults.set_mrs_lookup_failure.xsf hcur hr hb (by simp)
  split
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (faults.copy_mrs_fault.xsf (snd := snd) h hr hb (by simp [faults.SYSCALL_MESSAGE])) fun s2 h2 => ?_
    -- a64: the 13th word, then `trap_extra_mrs`
    refine WP.spec_bind (msg.set_mr.xsf h2 hr hb (by simp)) ?_
    rintro ⟨n, s3⟩ ⟨h3, -⟩
    simp only at h3
    try simp only [WP.uncurry'_pair]
    exact faults.trap_extra_mrs.xsf h3 hs hb
  split
  · try simp only [lift, bind_ok]
    refine WP.spec_bind (faults.copy_mrs_fault.xsf (snd := snd) h hr hb (by simp [faults.EXCEPTION_MESSAGE]))
      fun s2 hcur => ?_
    smrF
    exact set_mr_lastF hcur hr hb (by simp)
  split
  · step with obj.Tcb.sc.spec as ⟨c, hc⟩
    simp only [obj.Sc.is_null, bind_ok]
    split
    · exact set_mr_lastF h hr hb (by simp)
    rename_i hne
    have hc0 : L.mem s (scA snd) ≠ 0#u64 := by rw [← hc]; simpa using hne
    have hcS : c ∈ Scs := hc ▸ (h.1.2.2.1.2.2.bound snd hs hc0).1
    refine WP.spec_bind (schedcontext.update_consumed.xsf hA h hcS) ?_
    rintro ⟨cons, s1⟩ h1
    simp only at h1
    try simp only [WP.uncurry'_pair]
    refine WP.spec_bind (msg.set_mr.xsf h1 hr hb (by simp)) ?_
    rintro ⟨len, s2⟩ ⟨h2, hl2⟩
    simp only at h2 hl2
    try simp only [WP.uncurry'_pair]
    exact set_mr_lastF h2 hr hb (by simp at hl2; omega)
  split
  · smrF
    refine WP.spec_bind (msg.set_mr.xsf hcur hr hb (by simp)) ?_
    rintro ⟨ret, s2⟩ ⟨hcur, -⟩
    simp only at hcur
    try simp only [WP.uncurry'_pair]
    split
    · split
      · smrF
        exact set_mr_lastF hcur hr hb (by simp)
      · exact (WP.spec_ok _).2 hcur
    · exact (WP.spec_ok _).2 hcur
  split
  · smrF; smrF; smrF
    exact set_mr_lastF hcur hr hb (by simp)
  -- a64: VCPUFault, VGICMaintenance, VPPIEvent: one `set_mr` each
  split
  · exact set_mr_lastF h hr hb (by simp)
  split
  · split
    · exact set_mr_lastF h hr hb (by simp)
    · exact (WP.spec_ok _).2 h
  split
  · exact set_mr_lastF h hr hb (by simp)
  · exact (WP.spec_ok _).2 h

theorem ipc.do_fault_transfer.xsf {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s : S} {a : A}
    {badge snd rcv rb : U64} (h : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s) (hs : snd ∈ T) (hr : rcv ∈ T)
    (hb : BufOK U rb) :
    ipc.do_fault_transfer st ar s a badge snd rcv rb ⦃ s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_fault_transfer
  refine WP.spec_bind (faults.set_mrs_fault.xsf hA h hs hr hb) ?_
  rintro ⟨sent, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s1 hS) fun ft _ => ?_
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
  refine WP.spec_bind (Pₘ := fun s3 => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xsf h3 hr (by simp [layout.reg.BADGE, layout.reg.X0])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xsf (v := w) h1 hr (by simp [layout.reg.MSG_INFO, layout.reg.X1])


/-- **The message transfer's footprint** (a64: `XferFootOK` with `XferWA`): `do_ipc_transfer` writes in
`XferWA` (`XferW` and the sender's `FAULT_W1`). -/
def XferFootOKA (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (RS : S → S → Prop)
    (G : S → Prop) : Prop :=
  ∀ (Ac X : Set U64) (Q : U64 → U64 → List U64) (R : U64 → List U64) (s : S) (a : A) (snd ep badge : U64)
    (grant : Bool) (rcv : U64), snd ∈ T → rcv ∈ T →
    SchedQueuesInvX st T Cs Ω H X s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s →
    SCsOK st T Ω Sg Scs Z Ac s → SgOK st Ω Sg s → UserOK st T Cs Ω H U s → RS s s → G s →
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      WritesIn st s s' (XferWA T U Ω Sg Scs Z (L.ksb s) snd) ∧ RS s s' ⦄

/-- **The transfer's footprint, discharged** from `XferHyps` and `XferKG`. -/
theorem xferFootOK_ofA {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (K : XferKG st T Cs Ω H Sg Rp Scs Nt Z U RS RD) :
    XferFootOKA st ar T Cs Ω H Sg Rp Scs Nt Z U RS (XG st T Cs Ω H Sg Scs Z P3Ok) := by
  intro Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hrs hG0
  have hP : P0.StoreTotal st := L.total
  have h0 : XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s := XSF.start ⟨h, hB, hX, hS, hSg, hU⟩ hrs (K.step s)
  have hG : ∀ s', XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s' → XG st T Cs Ω H Sg Scs Z P3Ok s' :=
    fun s' h' => XG.xs hG0 h'.xs hU hs
  refine WP.spec_mono (P₀ := fun s' => XSF st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R snd s s') ?_
    fun s' h' => ⟨h'.2.2.1, h'.2.2.2.1⟩
  unfold ipc.do_ipc_transfer
  refine WP.spec_bind (E.buf _ _ _ _ s rcv hG0 h0.1 hr) fun rb hb => ?_
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hP) fun ft _ => ?_
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false snd hP) fun sb _ => ?_
    exact ipc.do_normal_transfer.xsf E K h0 hs hr hb hG
  · exact ipc.do_fault_transfer.xsf hA h0 hs hr hb

end

end Fl4ProofsA64.P1
