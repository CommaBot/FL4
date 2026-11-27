-- AArch64 port of Fl4Proofs.P1.QueueDecCnode (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
P1: InvGaps' `cnode` family: `cnode.decode` keeps the invariants, from
`DecPre`, the CDT placement facts `CdtHyps` (the slots the lookups return
are cap-slot words, the caps in them are typed, and the CDT writes of
`insert_with_cap`/`move_cap`/`swap` stay in cap-slot words) and the named delete and
revoke steps (`CnodeGaps`).  Copy/Mint/Move/Mutate/Rotate are the caller's
restart and cap-slot writes (`blk_of_capw`); CancelBadgedSends is
`cancel_badged_sends.blkF`.
-/
import Fl4ProofsA64.P1.QueueDecDom
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/- `FootD.cur0w` (a kernel-word and debug-list footprint is a `Cur0W` frame)
is in `QueueFinal`. -/

/-- The current node's words (but its debug head) are `Cur0W` words. -/
theorem NodeW.cur0w {s : S} {b : U64} (hc : L.cpu s ∈ Cs) (h : NodeW st s b) : Cur0W st T Cs Ω H Sg Scs Z s b := by
  obtain ⟨o, ho, h88, rfl⟩ := h
  exact Or.inl (kw_node hc ho h88)

/-- The CDT placement facts (P3's: cap slots, `valid_caps`, `valid_mdb`). -/
structure CdtHyps (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (P3Ok : S → Prop) : Prop where
  tgt : ∀ (Ac : Set U64) (s : S) (c : capability.Cap) (i d : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    cspace.lookup_target_slot st s c i d ⦃ r => ∀ x, r = .Ok x → CapW T Ω Sg x ⦄
  src : ∀ (Ac : Set U64) (s : S) (c : capability.Cap) (i d : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    cspace.lookup_source_slot st s c i d ⦃ r => ∀ x, r = .Ok x → CapW T Ω Sg x ⦄
  rot : ∀ (Ac : Set U64) (s : S) (b : U64) (e : Aeneas.Std.Array obj.Slot 3#usize) (d : U64),
    EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    cnode.rotate_slots st s b e d ⦃ r => ∀ x, r = .Ok x → CapW T Ω Sg x.1 ∧ CapW T Ω Sg x.2 ⦄
  slotcap : ∀ (Ac : Set U64) (s : S) (x : U64), EntAt st P3Ok s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → CapW T Ω Sg x →
    obj.Slot.cap st x s ⦃ c => CapOK st T Rp Scs Nt H s c ⦄
  /-- The insertion footprint for the helper taking the previously loaded
  source cap. This is a placement obligation for either source-cap value;
  the snapshot equality is established separately by the P3 Copy proof. -/
  ins : ∀ (Ac : Set U64) (s0 s : S) (c srcC : capability.Cap) (x y : U64), EntAt st P3Ok s0 →
    Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CapW T Ω Sg x → CapW T Ω Sg y →
    cdt.insert_with_cap st s c srcC x y ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄
  mv : ∀ (Ac : Set U64) (s0 s : S) (c : capability.Cap) (x y : U64), EntAt st P3Ok s0 →
    Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    CapW T Ω Sg x → CapW T Ω Sg y → cdt.move_cap st s c x y ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄
  sw : ∀ (Ac : Set U64) (s0 s : S) (c1 : capability.Cap) (x : U64) (c2 : capability.Cap) (y : U64),
    EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → CapW T Ω Sg x → CapW T Ω Sg y →
    cdt.swap st s c1 x c2 y ⦃ s' => WritesIn st s s' (CapW T Ω Sg) ⦄

/-- The named CNode steps: Delete and Revoke of a cap slot, after the
caller's restart (seL4 `cteDelete`, `cteRevoke`: finalisation of every
object type, preemptible). -/
structure CnodeGaps (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) : Prop where
  del : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize) (x : U64),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s c e → CapW T Ω Sg x →
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄
  rev : ∀ (Ac : Set U64) (s : S) (a : A) (c : capability.Cap) (e : Aeneas.Std.Array obj.Slot 3#usize) (x : U64),
    DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s c e → CapW T Ω Sg x →
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.revoke st ar s1 a x) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄

theorem cnode.full_endpoint.ep (c : capability.Cap) :
    cnode.full_endpoint c ⦃ o => ∀ p b, o = some (p, b) → ∃ x y z w, c = .Endpoint p b x y z w ⦄ := by
  unfold cnode.full_endpoint
  cases c <;> simp
  repeat' split
  all_goals simp

/-- The restart and then cap-slot writes. -/
theorem restart_capw {s : S} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) {m : S → Result S}
    (hm : ∀ s1, Fr0 st T Cs Ω H Sg Scs Z s s1 → BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s1 →
      m s1 ⦃ s' => WritesIn st s1 s' (CapW T Ω Sg) ⦄) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      let s2 ← m s1
      ok ((core.result.Result.Ok () : core.result.Result Unit error.Exc), s2)) ⦃ r =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 ⟨h1, f1, _, _⟩ => ?_
  refine WP.spec_bind (hm s1 (Foot.cur0w f1 (Set.empty_subset _)) (BlkOK.bxi h1)) fun s2 w2 => ?_
  exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_of_capw h1 w2 fun _ hb => hb).1))

set_option hygiene false in
/-- An error leaf with the state unchanged. -/
local macro "errleaf" : tactic => `(tactic| first
  | exact D.err _
  | exact (WP.spec_ok _).2 (D.err _)
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     first | exact D.err _ | exact (WP.spec_ok _).2 (D.err _)))

set_option maxHeartbeats 2000000 in
theorem cnode.decode_copy.dec (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (lbl len buf dest : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hd : CapW T Ω Sg dest) :
    cnode.decode_copy st s lbl len buf extra dest ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode_copy
  simp only [error.illegal, error.truncated, cnode.missing_source, bind_ok]
  split
  · errleaf
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · errleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun si _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun sd _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st sl s hS) fun root _ => ?_
  refine WP.spec_bind (P0.cdt.ensure_empty_slot.p0 st s dest hS) fun r0 _ => ?_
  rcases r0 with _ | e0
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (C.src Ac s root si sd hE D.bxi) fun r1 hr1 => ?_
  rcases r1 with v | e1
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf
  have hv := hr1 v rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st v s hS) fun sc _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 sc) fun b1 _ => ?_
  split
  · errleaf
  refine WP.spec_bind (P0.cnode.copied_cap.p0 st s lbl len buf v sc hS) fun r2 _ => ?_
  rcases r2 with ⟨nc, mv⟩ | e2
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 nc) fun b2 _ => ?_
  split
  · errleaf
  cases mv
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact restart_capw D fun s1 f1 h1 => C.ins Ac s s1 nc sc v dest hE f1 h1 hv hd
  · simp only [↓reduceIte]
    exact restart_capw D fun s1 f1 h1 => C.mv Ac s s1 nc v dest hE f1 h1 hv hd

set_option maxHeartbeats 2000000 in
theorem cnode.decode_rotate.dec (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (len buf dest : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hd : CapW T Ω Sg dest) :
    cnode.decode_rotate st s len buf extra dest ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold cnode.decode_rotate
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  have hl1 : (1#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun sl _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · errleaf
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 1#usize hl1) fun sl1 _ => ?_
  try simp only [obj.Slot.is_null, bind_ok]
  split
  · errleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun pd _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun sd _ => ?_
  refine WP.spec_bind (C.rot Ac s buf extra dest hE D.bxi) fun r hr => ?_
  rcases r with ⟨src, pv⟩ | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf
  obtain ⟨hsrc, hpv⟩ := hr _ rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  try simp only [uncurry_apply_pair]
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st src s hS) fun c _ => ?_
  refine WP.spec_bind (P0.objects.update_cap_data.p0 true sd c) fun ns _ => ?_
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st pv s hS) fun c1 _ => ?_
  refine WP.spec_bind (P0.objects.update_cap_data.p0 true pd c1) fun np _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 ns) fun b2 _ => ?_
  split
  · errleaf
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 np) fun b3 _ => ?_
  split
  · errleaf
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s3 ⟨h3, f3', _, _⟩ => ?_
  have f3 : Fr0 st T Cs Ω H Sg Scs Z s s3 := Foot.cur0w f3' (Set.empty_subset _)
  refine WP.spec_bind (P0.obj.Slot.Insts.CoreCmpPartialEqSlot.eq.p0 src dest) fun b4 _ => ?_
  split
  · refine WP.spec_bind (C.sw Ac s s3 ns src np pv hE f3 (BlkOK.bxi h3) hsrc hpv) fun s4 w4 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_of_capw h3 w4 fun _ hb => hb).1))
  · refine WP.spec_bind (C.mv Ac s s3 np pv dest hE f3 (BlkOK.bxi h3) hpv hd) fun s4 w4 => ?_
    have h4 := (blk_of_capw h3 w4 fun _ hb => hb).1
    have f4 : Fr0 st T Cs Ω H Sg Scs Z s s4 :=
      Cur0W.trans f3 (WritesIn.mono w4 fun _ hb => Or.inr (Or.inr (Or.inl hb)))
    refine WP.spec_bind (C.mv Ac s s4 ns src pv hE f4 (BlkOK.bxi h4) hsrc hpv) fun s5 w5 => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi (blk_of_capw h4 w5 fun _ hb => hb).1))

theorem cnode.decode_cancel_badged_sends.dec (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (dest : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (hd : CapW T Ω Sg dest) :
    cnode.decode_cancel_badged_sends st s dest ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄ := by
  have hct : L.curW s ∈ T := D.bxi.1.choose_spec.choose_spec.curT
  unfold cnode.decode_cancel_badged_sends
  simp only [error.illegal, bind_ok]
  refine WP.spec_bind (C.slotcap Ac s dest hE D.bxi hd) fun c hc => ?_
  refine WP.spec_bind (cnode.full_endpoint.ep c) fun o ho => ?_
  rcases o with _ | ⟨p, b⟩
  · errleaf
  obtain ⟨x, y, z, w, rfl⟩ := ho p b rfl
  have hH : H p = some .ep := hc.1.1 _ _ _ _ _ _ rfl
  try simp only [uncurry_apply_pair]
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (sched.set_thread_state.restart_blk (Es := ∅) s _ D.bxi.blk hct (runnable_ok D.run).1
    (runnable_ok D.run).2) fun s1 ⟨h1, _, _, _⟩ => ?_
  split
  · refine WP.spec_bind (endpoint.cancel_badged_sends.blkF s1 p b h1 hH) fun s2 ⟨h2, _⟩ => ?_
    exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h2))
  · exact (WP.spec_ok _).2 (DecPost.ok_bxi (BlkOK.bxi h1))

/-- The three-result form of the `(r, s)` decoders. -/
theorem lift2 {A : Type _} {s : S} {a : A} {m : Result ((core.result.Result Unit error.Exc) × S)}
    (h : m ⦃ r => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r.1 r.2 ⦄) :
    (do let (r1, s1) ← m; ok (r1, s1, a)) ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ :=
  WP.spec_bind h fun r hr => by obtain ⟨r1, s1⟩ := r; exact (WP.spec_ok _).2 hr

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode`** keeps the invariants. -/
theorem cnode.decode.dec {A : Type _} {ar : machine.Arch A} (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (G : CnodeGaps st ar T Cs Ω H Sg Rp Scs Nt Z U) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (lbl len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hE : EntAt st P3Ok s) (c : capability.Cap) :
    cnode.decode st ar s a lbl len c buf extra ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · errleaf
  split
  · errleaf
  split
  · errleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun idx _ => ?_
  refine WP.spec_bind (P0.msg.syscall_arg.p0 st s _ buf _ hS) fun dep _ => ?_
  refine WP.spec_bind (C.tgt Ac s c idx dep hE D.bxi) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    errleaf
  have hv := hr v rfl
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  repeat' (first
    | exact (WP.spec_ok _).2 (D.err _)
    | exact lift2 (cnode.decode_copy.dec C lbl len buf v D hE hv)
    | exact lift2 (cnode.decode_cancel_badged_sends.dec C v D hE hv)
    | exact lift2 (cnode.decode_rotate.dec C len buf v D hE hv)
    | exact G.del Ac s a _ extra v D hv
    | exact G.rev Ac s a _ extra v D hv
    | split)

/-- **InvGaps' `cnode`, discharged** but for the named `CnodeGaps`. -/
theorem decGap_cnode {A : Type _} {ar : machine.Arch A} (C : CdtHyps st T Cs Ω H Sg Rp Scs Nt Z P3Ok)
    (G : CnodeGaps st ar T Cs Ω H Sg Rp Scs Nt Z U) : DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .cnode := by
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D _hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 (DecPost.keep D.bxi (by simp))
  · exact cnode.decode.dec C G a lbl len buf D hE _

end

end Fl4ProofsA64.P1
