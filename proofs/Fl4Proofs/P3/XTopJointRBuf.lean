/-
P3 (line rbuf): **the current thread's IPC buffer lies in user memory**, the
P2 premise `rbuf` (`SlAccIn.rbuf` / `SlAccJ.rbuf` / `SlAccK.rbuf`,
P2/SlAccL.lean, P2/SlHereJ.lean on par/p2sl), discharged from `JAtZ`.

`JAtZ.bufUser`: at a `JAtZ` state every thread of `Z.th`'s IPC buffer, for
either receiver flag (`false` also takes a read-only frame), is made of
aligned words of `Z.B`: `BufCover` puts the spec buffer in `Z.B` word by word
(`Endp.BufMap`), `balign` aligns them. This is `JAtZ.sbufOK`
(P3/XTopJointKEntryInvL.lean) with the user set in place of "outside the TCBs
and nodes".

`JAtZ.curBufUser` is the current thread's case, `JAtZ.rbufAt` the same at any
later state `X` that agrees with the `JAtZ` state on the three words
`msg.lookup_ipc_buffer` reads (`IPC_BUFFER` and the buffer cap slot, P1
`lookup_buf_agreeB`).

**Bridge to P2.** P2 takes the layout of the joint invariant's ghosts,
`OwnMap.layoutJ Z H ksb n` (P2/OwnJAtZ.lean on par/p2sl), whose user set is
`{b | ∃ wp ∈ Z.B, wp.1 = b}`; P2's `BufW P buf` is P1's `BufOK {b | P b} buf`.
So `rbufAt`'s conclusion, `P1.BufOK {b | P1.Aligned b ∧ ∃ wp ∈ Z.B, wp.1 = b}
buf`, is by definition `BufW (fun b => Aligned b ∧ b ∈ (layoutJ Z H ksb n).user)
buf`, the conclusion of `rbuf` at the prefix state `X` for `L.curW s`. Its
three agreement hypotheses are the prefix's frame on the current TCB's
`IPC_BUFFER` / `SLOT_BUFFER` words (the prefix writes only node and lock
words; P2 `lp_mem` with `not_slDS`).

No premise is added: everything comes from `JAtZ`.
-/
import Fl4Proofs.P3.XTopJointKEntryInvL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
open Fl4Proofs.P3.SInvR.G4

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The user words of the joint invariant: aligned words of `Z.B` (P2's
`(layoutJ Z H ksb n).user`, aligned). -/
def ZUser (Z : XSets) : Set U64 := {b | P1.Aligned b ∧ ∃ wp ∈ Z.B, wp.1 = b}

set_option maxHeartbeats 8000000 in
/-- **Every thread's IPC buffer in user memory** (module docstring). -/
theorem JAtZ.bufUser {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {y : U64} (hth : Z.th y = some .tcb) (rb : Bool) :
    msg.lookup_ipc_buffer st s rb y ⦃ w => P1.BufOK (ZUser Z) w ⦄ := by
  have hyT := J.thT y hth
  obtain ⟨xd, hk, hws⟩ := J.buf y hyT
  obtain ⟨hOK, hBC, -⟩ := J.xferH
  refine WP.spec_mono (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hth hk hOK rb) ?_
  rintro w ⟨h0, hp⟩ hw0 i hi
  cases hb : Endp.ipcBufOf rb xd with
  | none => exact absurd (h0.2 hb) hw0
  | some p' =>
    have e := hp hws p' hb
    have hwB := hBC y hyT xd rb p' hk hb w e i hi
    exact ⟨(J.xtop.fin.1.2.ep.balign _ hwB).1, _, hwB, rfl⟩

/-- **The current thread's IPC buffer in user memory.** -/
theorem JAtZ.curBufUser {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (rb : Bool) :
    msg.lookup_ipc_buffer st s rb (L.curW s) ⦃ w => P1.BufOK (ZUser Z) w ⦄ :=
  J.bufUser (J.curW_tcb (cur_thread_curW (L := L) s)) rb

/-- **P2's `rbuf`** (module docstring): at any state `X` agreeing with the
`JAtZ` state `s` on the current thread's buffer words, the `is_receiver =
false` lookup of `L.curW s` gives a buffer of aligned `Z.B` words. -/
theorem JAtZ.rbufAt {s X : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (h1 : L.mem X (P1.ibA (L.curW s)) = L.mem s (P1.ibA (L.curW s)))
    (h2 : L.mem X (P1.sbA (L.curW s)) = L.mem s (P1.sbA (L.curW s)))
    (h3 : L.mem X (core.num.U64.wrapping_add (P1.sbA (L.curW s)) 8#u64) =
      L.mem s (core.num.U64.wrapping_add (P1.sbA (L.curW s)) 8#u64))
    {buf : U64} (hb : msg.lookup_ipc_buffer st X false (L.curW s) = ok buf) :
    P1.BufOK (ZUser Z) buf := by
  have h := J.curBufUser false
  rw [← P1.lookup_buf_agreeB false h1 h2 h3, hb] at h
  exact spec_ok_post h rfl

end

end

end Fl4Proofs.P3
