/-
P1: InvGaps' `ept` family (`ept.decode`).  An EPT table cap's `Unmap`
restarts the caller, unmaps the table (one EPT entry cleared), clears the
table and updates the cap; its `Map` writes one EPT entry of the root's walk,
restarts the caller and updates the cap.  The EPT entries are words of EPT
table objects (untracked object words), which is P3's `EptPlace`.
-/
import Fl4Proofs.P1.QueueDecVcpu
import Fl4Proofs.P1.QueueDecVs
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {P3Ok : S → Prop}
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

/-- An EPT table at `s`: every walk from it ends at an aligned untracked
object word. -/
def EptTbl (st : machine.Store S) (Ω Sg : Set U64) (s : S) (r : U64) : Prop :=
  ∀ gpa level, ept.lookup st s r gpa level ⦃ o => ∀ x, o = .Ok x → Aligned x ∧ x ∈ Ω ∧ x ∉ Sg ⦄

/-- **The EPT tables' placement** (P3's): a found EPT root is an EPT table,
and an invoked non-root EPT table cap's table holds no tracked word. -/
structure EptPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  /-- At the caller's restart after the decode's start `s0` (its footprint `Foot`). -/
  find : ∀ (Ac : Set U64) (s0 s : S) (asid : U64), EntAt st P3Ok s0 → Fr0 st T Cs Ω H Sg Scs Z s0 s →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s →
    ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → EptTbl st Ω Sg s r1 ⦄
  tbl : ∀ (Ac : Set U64) (s : S) (cap : capability.Cap) (extra : Aeneas.Std.Array obj.Slot 3#usize),
    EntAt st P3Ok s → DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra → ∀ ptr level m asid va,
      cap = .Ept ptr level m asid va → level ≠ 0#u64 → FreeRegion Ω Sg ptr 4096#u64

/-- **`ept.unmap`** from a found EPT table: at most one EPT entry cleared. -/
theorem ept.unmap.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A)
    (asid gpa ptr level : U64) (table : Bool)
    (hf : ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → EptTbl st Ω Sg s r1 ⦄)
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    ept.unmap st ar s a asid gpa ptr level table ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ept.unmap
  refine WP.spec_bind hf ?_
  rintro (r1 | e) hr
  swap
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (hr r1 rfl gpa level) ?_
  rintro (x | e) hx
  swap
  · exact (WP.spec_ok _).2 h
  obtain ⟨al, hΩ, hSg⟩ := hx x rfl
  try dsimp only
  refine WP.spec_bind (LawfulStore.read_spec s x) fun e _ => ?_
  have fin : (do
      let s1 ← st.write s x 0#u64
      ept.invalidate st ar s1 a r1) ⦃ r => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ⦄ := by
    refine WP.spec_bind (LawfulStore.write_spec s x 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (ept.invalidate.same hA _ a r1) fun r er => ?_
    rw [er]
    exact Cur0.capw h (writesIn_wr al) fun b hb => Or.inr (hb ▸ ⟨hΩ, hSg⟩)
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact (WP.spec_ok _).2 trivial
    split <;> exact (WP.spec_ok _).2 trivial) fun large _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · simp only [lift, bind_ok]
      step*
    · exact (WP.spec_ok _).2 trivial) fun mask _ => ?_
  simp only [lift, bind_ok, layout.paddr]
  split
  · exact (WP.spec_ok _).2 h
  split
  · split
    · exact (WP.spec_ok _).2 h
    split
    · exact (WP.spec_ok _).2 h
    · exact fin
  · split
    · exact (WP.spec_ok _).2 h
    · exact fin

/-- A found root's walk, through `ept.root` and `ept.slot`. -/
theorem ept.slot.place {s : S} {r gpa level : U64} (hr : EptTbl st Ω Sg s r) :
    ept.slot st s r gpa level ⦃ o => ∀ x, o = .Ok x → Aligned x ∧ x ∈ Ω ∧ x ∉ Sg ⦄ := by
  unfold ept.slot
  refine WP.spec_bind (hr gpa level) ?_
  rintro (x | e) hx
  · exact (WP.spec_ok _).2 fun y ey => by cases ey; exact hx x rfl
  · simp only [core.result.Result.map_err]
    refine WP.spec_bind (Pₘ := fun _ => True) ((WP.spec_ok _).2 trivial) fun m _ => ?_
    exact (WP.spec_ok _).2 fun y ey => by cases ey

theorem ept.root.place {s : S} {c : capability.Cap}
    (hf : ∀ asid, ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → EptTbl st Ω Sg s r1 ⦄) :
    ept.root st s c ⦃ o => ∀ r1 a1, o = .Ok (r1, a1) → EptTbl st Ω Sg s r1 ⦄ := by
  have bad : ∀ {α : Type} (P : core.result.Result α error.Exc → Prop),
      (∀ e, P (.Err e)) → error.invalid_cap α 1#u64 ⦃ P ⦄ := fun P hP => by
    simp only [error.invalid_cap, error.sys, bind_ok, WP.spec_ok]; exact hP _
  unfold ept.root
  cases c
  all_goals try (exact bad _ fun e r1 a1 h => by cases h)
  rename_i ptr i b asid va
  repeat' (first | exact bad _ fun e r1 a1 h => by cases h | split)
  refine WP.spec_bind (hf _) ?_
  rintro (r1 | e) hr
  · refine WP.spec_bind ((WP.spec_ok _).2 rfl) fun x ex => ?_
    subst ex
    refine WP.spec_bind ((WP.spec_ok _).2 rfl) fun y ey => ?_
    subst ey
    try dsimp only
    split
    · exact bad _ fun e r1 a1 h => by cases h
    · exact (WP.spec_ok _).2 fun r2 a2 h => by cases h; exact hr r1 rfl
  · simp only [core.result.Result.map_err, ept.root.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once,
      bind_ok, core.result.Result.Insts.CoreOpsTry.branch]
    try dsimp only
    simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {H : Heap} {Cs Rp Scs Nt : Set U64} {Z : U64 → Nat} {U Ac : Set U64}

set_option hygiene false in
/-- An error leaf at the decode's start. -/
local macro "eerr" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 (Cur0.post c0)
  | (simp only [error.truncated, error.illegal, error.invalid_arg, error.invalid_cap, error.range, error.sys, bind_ok]
     exact (WP.spec_ok _).2 (Cur0.post c0)))

set_option maxHeartbeats 8000000 in
/-- **`ept.decode`** on an EPT table cap. -/
theorem ept.decode.dec {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : EptPlace st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U P3Ok) {s : S} {a : A}
    {lbl len buf : U64} {slot : obj.Slot} {ptr level asid vaddr : U64} {mapped : Bool}
    {extra : Aeneas.Std.Array obj.Slot 3#usize}
    (D : DecPre st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z U Ac s (.Ept ptr level mapped asid vaddr) extra)
    (hslot : CapSlotW H.tcbs H.omega H.frame slot) (hE : EntAt st P3Ok s) :
    ept.decode st ar s a lbl len (.Ept ptr level mapped asid vaddr) slot buf extra ⦃ r s' _ =>
      DecPost st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have c0 := Cur0.ofPre D
  have hsw : SlotW H.tcbs H.omega H.frame slot := ⟨hslot.1, hslot.2⟩
  unfold ept.decode
  dsimp only
  split
  swap
  · eerr
  rename_i hl0
  have hz := P.tbl Ac s _ extra hE D ptr level mapped asid vaddr rfl (by simpa using hl0)
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact (WP.spec_ok _).2 trivial
    split <;> exact (WP.spec_ok _).2 trivial) ?_
  rintro ⟨map, unmap⟩ -
  refine WP.spec_bind (sched.cur_thread.spec s) fun ct ect => ?_
  have e : ct = L.curW s := ect
  subst e
  split
  · -- unmap
    refine WP.spec_bind (P0.cdt.is_final_capability.p0 st s slot hS) fun b _ => ?_
    split
    swap
    · exact (WP.spec_ok _).2 (Cur0.post c0)
    refine WP.spec_bind (Cur0.restart D) fun s1 h1 => ?_
    obtain ⟨Ac1, hb1⟩ := h1.bxi
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st H.tcbs Cs H.omega H H.frame Rp Scs Nt Z Ac s r.1) ?_ ?_
    · split
      · refine WP.spec_bind (ept.unmap.cur0 hA a asid vaddr ptr level true (P.find Ac1 s s1 asid hE h1.fr hb1) h1) ?_
        rintro ⟨s3, a2⟩ h3
        try simp only [uncurry_apply_pair]
        refine WP.spec_bind (LawfulStore.zero_spec s3 ptr 4096#u64) fun s4 e4 => ?_
        subst e4
        exact (WP.spec_ok _).2 (Cur0.zr h3 hz)
      · exact (WP.spec_ok _).2 h1
    rintro ⟨s2, a1⟩ h2
    try simp only [uncurry_apply_pair]
    refine WP.spec_bind (obj.Slot.set_cap.capw (s := s2) hsw) fun s3 w3 => ?_
    exact (WP.spec_ok _).2 (h2.capw w3 fun _ hb => hb).post
  split
  swap
  · eerr
  -- map
  split
  · eerr
  have hl0 : (0#usize : Usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun x _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  · eerr
  split
  · eerr
  refine WP.spec_bind (P0.msg.syscall_arg.p0 _ _ _ _ _ L.total) fun i _ => ?_
  simp only [lift, bind_ok]
  step as ⟨i2, _⟩
  step as ⟨i3, _⟩
  step with ept.LIMIT.spec as ⟨i5, _⟩
  split
  · eerr
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c _ => ?_
  refine WP.spec_bind (ept.root.place (P.find Ac s s · hE (WritesIn.refl _ _) D.bxi)) ?_
  rintro (⟨r1, asid1⟩ | er) hr
  all_goals
    refine WP.spec_bind (Pₘ := fun c => c = _) ((WP.spec_ok _).2 rfl) fun cf ecf => ?_
    subst ecf
    try dsimp only
  swap
  · unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
    try dsimp only
    refine WP.spec_bind (Pₘ := fun _ => True) (by simp [core.convert.FromSame.from]) fun _ _ => ?_
    exact (WP.spec_ok _).2 (Cur0.post c0)
  refine WP.spec_bind (ept.slot.place (hr r1 asid1 rfl)) ?_
  rintro (v1 | er) hr2
  all_goals
    refine WP.spec_bind (Pₘ := fun c => c = _) ((WP.spec_ok _).2 rfl) fun cf ecf => ?_
    subst ecf
    try dsimp only
  swap
  · unfold core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
    try dsimp only
    refine WP.spec_bind (Pₘ := fun _ => True) (by simp [core.convert.FromSame.from]) fun _ _ => ?_
    exact (WP.spec_ok _).2 (Cur0.post c0)
  obtain ⟨al, hΩ, hSg⟩ := hr2 v1 rfl
  refine WP.spec_bind (LawfulStore.read_spec s v1) fun e6 _ => ?_
  try simp only [lift, bind_ok]
  split
  · exact (WP.spec_ok _).2 (Cur0.post c0)
  refine WP.spec_bind (Cur0.restart D) fun s2 h2 => ?_
  simp only [layout.paddr, bind_ok, lift]
  refine WP.spec_bind (LawfulStore.write_spec s2 v1 _) fun s3 e3 => ?_
  subst e3
  have h3 := Cur0.capw h2 (writesIn_wr (v := core.num.U64.wrapping_sub ptr layout.PPTR_BASE ||| 7#u64) al)
    fun b hb => Or.inr (hb ▸ ⟨hΩ, hSg⟩)
  refine WP.spec_bind (obj.Slot.set_cap.capw (s := L.wr s2 v1 (core.num.U64.wrapping_sub ptr layout.PPTR_BASE ||| 7#u64))
    hsw) fun s4 w4 => ?_
  exact (WP.spec_ok _).2 (h3.capw w4 fun _ hb => hb).post

/-- **The EPT tables' placement for the decode** (P3's), over the heap's sets. -/
structure EptPlaceH (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (U : Set U64) (P3Ok : S → Prop) : Prop where
  sets : T = H.tcbs ∧ Ω = H.omega ∧ Sg = H.frame
  pl : EptPlace st T Cs Ω H Sg Rp Scs Nt Z U P3Ok

end

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **InvGaps' `ept` family**, from the EPT tables' placement. -/
theorem decGap_ept {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : EptPlaceH st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) :
    DecGap st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok .ept := by
  obtain ⟨⟨eT, eΩ, eSg⟩, Pl⟩ := P
  subst eT eΩ eSg
  intro Ac s a lbl len slot cap blk call don fp buf extra hf D hslot hE
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  exact ept.decode.dec hA Pl D hslot hE

end

end Fl4Proofs.P1
