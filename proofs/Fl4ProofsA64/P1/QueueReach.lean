/-
P1 (aarch64, gen 45): **the VSpace typings narrowed to reachable tables** (Architect ruling, gen 44/45): `Te` and
`Tb` stay the placement sets of all live tables (orphan tables are never dropped; deletion keeps them); only the
"non-leaf entry points at a lower-level table" clauses — `S2Ty.desc` (QueueS2Ty) and its Stage-1 analogue
`VsTy.desc` (QueueVsTy) — are narrowed to the tables reachable from the live ASID-pool entries (l4v
`valid_vspace_objs` over `vs_lookup`, the shape of x86 `EptCore`'s walk field).

* **`S2Reach st Pp Re bits s t`** (inductive): `t` is the untagged value of a tag-1 (`ROOT_S2`) entry of a pool of
  `Pp`, or is named by a table descriptor (`e & 3 = 3`) at a positive depth of a reachable table.
* **`VsReach st Pp Hr Lv s t`** (inductive): `t` is a `HighVSpace` root of `Hr`, the value of a nonzero tag-0
  (`ROOT_S1`) pool entry, the untagged value of a tag-2 (`ROOT_HIGH`) entry, or is named by a table descriptor at a
  level `< 3` of a reachable table.
  The pools `Pp` (resp. `Hr`) are the live ASID pools (resp. live `HighVSpace` roots), as in QueueVsTy's /
  QueueHiTy's reading of these ghost sets; a Stage-1 / Stage-2 VSpace's deletion clears its pool entry
  (`delete_asid`, vspace.rs:529–548), so its tables stop being reachable while staying in `Tb` / `Te`.
* **`S2TyR st n Pp Hr Te Re bits s`**: `S2Ty` with `desc` asked only of reachable tables (`tag`, `hi` unchanged);
  **`VsTyR st kb Pp Hr Tb Lv s`**: `VsTy` with `desc` asked only of reachable tables (`tbl`, `pool` unchanged).
* `S2Rt` / `VsRt`: the reachable part of `Te` / `Tb`.

**The narrowed typing is the old typing over the reachable part** (`S2TyR.iff`, `VsTyR.iff`):
`S2TyR … Te … ↔ ∃ T ⊆ Te, S2Ty … T …` and, with `Hr ⊆ Tb`, `VsTyR … Tb … ↔ ∃ T ⊆ Tb, Hr ⊆ T ∧ VsTy … T …` — a
sub-table-set satisfying the old typing contains every reachable table (`S2Ty.reach`, `VsTy.reach`), and the
reachable part satisfies it (`S2TyR.sub`, `VsTyR.sub`). So every existing lemma over `S2Ty` / `VsTy` is reused as an
instance at `T = S2Rt` / `VsRt` (no statement or proof of an existing lemma changes; the old typing implies the new,
`S2Ty.toR`, `VsTy.toR`). The walk invariants (`EkI`, `EkD`, `UtI`, `LkI`) instantiated at `S2Rt` / `VsRt` carry
"the current table is reachable". Every hypothesis the reused lemmas take about the table sets is monotone
(`S2OK.sub`, `gran_mono`, `S2Pl.mono`, `S1Pl.mono`, `HrOK.mono`) or antitone (`UnmZ.anti`, `UnmT.anti`), so those
over `Te` / `Tb` give those over the reachable part, and a hypothesis "`t ∉ Te`" becomes "`t` is not reachable".

Re-established over the narrowed typings (instances, file QueueReach):
* walks: `ept.find.tyR`, `ept.lookup_slot_loop.tyR`, `ept.lookup_slot.tyR`, `ept.lookup_slot_loop.tyDR`,
  `ept.lookup_slot.tyDR`, `ept.unmap_table_loop.tyR`, `ept.unmap.zR`, `ept.unmap_table.zR`,
  `vspace.unmap_page_table.s2R`;
* rebuild lemmas: `S2TyR.keep`, `S2TyR.of_hr`, `S2TyR.wr`, `S2TyR.wr3`, `S2TyR.addT` (no side condition: an
  unreachable new object owes nothing — `S2TyR.mono`), `S2TyR.congr`, `S2TyR.map_table`, `S2TyR.assign1`,
  `S2TyR.drop` (the reachable form: a set of tables named by no tag-1 entry and by no reachable descriptor outside
  it is unreachable), `VsTyR.keepZ`, `VsTyR.wr`, `VsTyR.addT`, `VsTyR.congrL`, `VsTyR.map_table` (the new table
  only **unreachable**, not outside `Tb`), `VsTyR.assign1`;
* deletion (gen 41's loops): **`cdt.delete.zqETR`**, **`cdt.delete.threadQETR`** (`JV ∧ VsTyR ∧ S2TyR` from
  `JV ∧ VsTyR ∧ S2TyR`).

No named premise; new definitions and theorems only, no existing file edited but the root import.
-/
import Fl4ProofsA64.P1.QueueS1Map
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

local notation "wa" => core.num.U64.wrapping_add

namespace W7
namespace R
namespace ST

/-! ## Reachability and the narrowed typings -/

/-- **The Stage-2 tables reachable from the pools** (module docstring). -/
inductive S2Reach (st : machine.Store S) [L : LawfulStore st] (Pp : Set U64) (Re bits : U64 → Nat) (s : S) :
    U64 → Prop
  | root {p o : U64} : p ∈ Pp → o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa p o) &&& 3#u64) = 1#u64 →
      S2Reach st Pp Re bits s (L.mem s (wa p o) &&& ~~~3#u64)
  | step {p o : U64} : S2Reach st Pp Re bits s p → 0 < Re p → o.val < 2 ^ bits p → o.val % 8 = 0 →
      (L.mem s (wa p o) &&& 3#u64) = 3#u64 →
      S2Reach st Pp Re bits s (wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE)

/-- **The Stage-1 tables reachable from the pools and the `HighVSpace` roots** (module docstring). -/
inductive VsReach (st : machine.Store S) [L : LawfulStore st] (Pp Hr : Set U64) (Lv : U64 → Nat) (s : S) :
    U64 → Prop
  | hr {R : U64} : R ∈ Hr → VsReach st Pp Hr Lv s R
  | root0 {p o : U64} : p ∈ Pp → o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
      (L.mem s (wa p o) &&& 3#u64) = 0#u64 → VsReach st Pp Hr Lv s (L.mem s (wa p o))
  | root2 {p o : U64} : p ∈ Pp → o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa p o) &&& 3#u64) = 2#u64 →
      VsReach st Pp Hr Lv s (L.mem s (wa p o) &&& ~~~3#u64)
  | step {p o : U64} : VsReach st Pp Hr Lv s p → Lv p < 3 → o.val < 4096 → o.val % 8 = 0 →
      (L.mem s (wa p o) &&& 3#u64) = 3#u64 →
      VsReach st Pp Hr Lv s (wa (L.mem s (wa p o) &&& vspace.ADDR_MASK) layout.PPTR_BASE)

/-- **The narrowed Stage-2 typing**: `S2Ty` with `desc` asked only of reachable tables. -/
structure S2TyR (st : machine.Store S) [L : LawfulStore st] (n : U64) (Pp Hr Te : Set U64) (Re bits : U64 → Nat)
    (s : S) : Prop where
  tag : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    ((L.mem s (wa p o) &&& 3#u64) = 0#u64 ∧ L.mem s (wa p o) ∉ Hr) ∨
    ((L.mem s (wa p o) &&& 3#u64) = 2#u64 ∧ (L.mem s (wa p o) &&& ~~~3#u64) ∈ Hr) ∨
    ((L.mem s (wa p o) &&& 3#u64) = 1#u64 ∧ (L.mem s (wa p o) &&& ~~~3#u64) ∈ Te ∧
      Re (L.mem s (wa p o) &&& ~~~3#u64) + 1 = s2lv n ∧ s2rb n ≤ bits (L.mem s (wa p o) &&& ~~~3#u64))
  hi : ∀ R ∈ Hr, (L.mem s (wa R 4088#u64) &&& 3#u64) = 3#u64
  desc : ∀ p ∈ Te, S2Reach st Pp Re bits s p → 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 →
    (L.mem s (wa p o) &&& 3#u64) = 3#u64 →
    wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE ∈ Te ∧
      Re (wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE) + 1 = Re p

/-- **The narrowed Stage-1 typing**: `VsTy` with `desc` asked only of reachable tables. -/
structure VsTyR (st : machine.Store S) [L : LawfulStore st] (kb : U64) (Pp Hr Tb : Set U64) (Lv : U64 → Nat)
    (s : S) : Prop where
  tbl : ∀ o : U64, 772352 ≤ o.val → o.val < 773376 → o.val % 8 = 0 → L.mem s (wa kb o) ≠ 0#u64 →
    L.mem s (wa kb o) ∈ Pp
  pool : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → L.mem s (wa p o) ≠ 0#u64 →
    ((L.mem s (wa p o) &&& 3#u64) = 0#u64 → L.mem s (wa p o) ∈ Tb ∧ Lv (L.mem s (wa p o)) = 0) ∧
    ((L.mem s (wa p o) &&& 3#u64) = 2#u64 →
      (L.mem s (wa p o) &&& ~~~3#u64) ∈ Tb ∧ Lv (L.mem s (wa p o) &&& ~~~3#u64) = 0)
  desc : ∀ p ∈ Tb, VsReach st Pp Hr Lv s p → Lv p < 3 → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
    (L.mem s (wa p o) &&& 3#u64) = 3#u64 →
    wa (L.mem s (wa p o) &&& vspace.ADDR_MASK) layout.PPTR_BASE ∈ Tb ∧
      Lv (wa (L.mem s (wa p o) &&& vspace.ADDR_MASK) layout.PPTR_BASE) = Lv p + 1

/-- The reachable Stage-2 objects of `Te`. -/
def S2Rt (st : machine.Store S) [L : LawfulStore st] (Pp Te : Set U64) (Re bits : U64 → Nat) (s : S) : Set U64 :=
  {p | p ∈ Te ∧ S2Reach st Pp Re bits s p}

/-- The reachable Stage-1 tables of `Tb`. -/
def VsRt (st : machine.Store S) [L : LawfulStore st] (Pp Hr Tb : Set U64) (Lv : U64 → Nat) (s : S) : Set U64 :=
  {p | p ∈ Tb ∧ VsReach st Pp Hr Lv s p}

section eqv
variable {kb n : U64} {Pp Tb Pt Hr Te T' : Set U64} {Lv Re bits : U64 → Nat}

theorem S2Rt_sub {s : S} : S2Rt st Pp Te Re bits s ⊆ Te := fun _ h => h.1

theorem VsRt_sub {s : S} : VsRt st Pp Hr Tb Lv s ⊆ Tb := fun _ h => h.1

theorem hr_rt {s : S} (hH : Hr ⊆ Tb) : Hr ⊆ VsRt st Pp Hr Tb Lv s := fun _ hR => ⟨hH hR, .hr hR⟩

/-- **The old Stage-2 typing implies the narrowed one.** -/
theorem _root_.Fl4ProofsA64.P1.S2Ty.toR {s : S} (h : S2Ty st n Pp Hr Te Re bits s) : S2TyR st n Pp Hr Te Re bits s :=
  ⟨h.tag, h.hi, fun p hp _ => h.desc p hp⟩

/-- **The old Stage-1 typing implies the narrowed one.** -/
theorem _root_.Fl4ProofsA64.P1.VsTy.toR {s : S} (h : VsTy st kb Pp Tb Lv s) : VsTyR st kb Pp Hr Tb Lv s :=
  ⟨h.tbl, h.pool, fun p hp _ => h.desc p hp⟩

/-- **A table set with the old Stage-2 typing contains every reachable table.** -/
theorem _root_.Fl4ProofsA64.P1.S2Ty.reach {s : S} (h : S2Ty st n Pp Hr T' Re bits s) {p : U64} (hr : S2Reach st Pp Re bits s p) :
    p ∈ T' := by
  induction hr with
  | @root q o hq ho h8 h1 =>
    have hne : L.mem s (wa q o) ≠ 0#u64 := fun e => by rw [e] at h1; exact absurd h1 (by decide)
    rcases h.tag q hq o ho h8 hne with ⟨e, -⟩ | ⟨e, -⟩ | ⟨-, hT, -⟩
    · rw [e] at h1; exact absurd h1 (by decide)
    · rw [e] at h1; exact absurd h1 (by decide)
    · exact hT
  | @step q o _ hr ho h8 h3 ih => exact (h.desc q ih hr o ho h8 h3).1

/-- **A table set with the old Stage-1 typing containing `Hr` contains every reachable table.** -/
theorem _root_.Fl4ProofsA64.P1.VsTy.reach {s : S} (h : VsTy st kb Pp T' Lv s) (hH : Hr ⊆ T') {p : U64}
    (hr : VsReach st Pp Hr Lv s p) : p ∈ T' := by
  induction hr with
  | hr hR => exact hH hR
  | @root0 q o hq ho h8 hne h0 => exact ((h.pool q hq o ho h8 hne).1 h0).1
  | @root2 q o hq ho h8 h2 =>
    have hne : L.mem s (wa q o) ≠ 0#u64 := fun e => by rw [e] at h2; exact absurd h2 (by decide)
    exact ((h.pool q hq o ho h8 hne).2 h2).1
  | @step q o _ hl ho h8 h3 ih => exact (h.desc q ih hl o ho h8 h3).1

/-- **The old Stage-2 typing over a sub-table-set gives the narrowed one.** -/
theorem _root_.Fl4ProofsA64.P1.S2Ty.toRsub {s : S} (h : S2Ty st n Pp Hr T' Re bits s) (hT : T' ⊆ Te) : S2TyR st n Pp Hr Te Re bits s := by
  refine ⟨fun p hp o ho h8 hne => ?_, h.hi, fun p _ hr hpos o ho h8 h3 => ?_⟩
  · rcases h.tag p hp o ho h8 hne with a | a | ⟨a, b, c, d⟩
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨a, hT b, c, d⟩)
  · obtain ⟨a, b⟩ := h.desc p (h.reach hr) hpos o ho h8 h3
    exact ⟨hT a, b⟩

/-- **The old Stage-1 typing over a sub-table-set containing `Hr` gives the narrowed one.** -/
theorem _root_.Fl4ProofsA64.P1.VsTy.toRsub {s : S} (h : VsTy st kb Pp T' Lv s) (hT : T' ⊆ Tb) (hH : Hr ⊆ T') :
    VsTyR st kb Pp Hr Tb Lv s := by
  refine ⟨h.tbl, fun p hp o ho h8 hne => ?_, fun p _ hr hl o ho h8 h3 => ?_⟩
  · obtain ⟨a, b⟩ := h.pool p hp o ho h8 hne
    exact ⟨fun h0 => by obtain ⟨c, d⟩ := a h0; exact ⟨hT c, d⟩,
      fun h2 => by obtain ⟨c, d⟩ := b h2; exact ⟨hT c, d⟩⟩
  · obtain ⟨a, b⟩ := h.desc p (h.reach hH hr) hl o ho h8 h3
    exact ⟨hT a, b⟩

/-- **The narrowed Stage-2 typing is the old one over the reachable objects.** -/
theorem S2TyR.sub {s : S} (h : S2TyR st n Pp Hr Te Re bits s) :
    S2Ty st n Pp Hr (S2Rt st Pp Te Re bits s) Re bits s := by
  refine ⟨fun p hp o ho h8 hne => ?_, h.hi, fun p hp hpos o ho h8 h3 => ?_⟩
  · rcases h.tag p hp o ho h8 hne with a | a | ⟨a, b, c, d⟩
    · exact Or.inl a
    · exact Or.inr (Or.inl a)
    · exact Or.inr (Or.inr ⟨a, ⟨b, S2Reach.root hp ho h8 a⟩, c, d⟩)
  · obtain ⟨a, b⟩ := h.desc p hp.1 hp.2 hpos o ho h8 h3
    exact ⟨⟨a, S2Reach.step hp.2 hpos ho h8 h3⟩, b⟩

/-- **The narrowed Stage-1 typing is the old one over the reachable tables.** -/
theorem VsTyR.sub {s : S} (h : VsTyR st kb Pp Hr Tb Lv s) : VsTy st kb Pp (VsRt st Pp Hr Tb Lv s) Lv s := by
  refine ⟨h.tbl, fun p hp o ho h8 hne => ?_, fun p hp hl o ho h8 h3 => ?_⟩
  · obtain ⟨a, b⟩ := h.pool p hp o ho h8 hne
    exact ⟨fun h0 => by obtain ⟨c, d⟩ := a h0; exact ⟨⟨c, VsReach.root0 hp ho h8 hne h0⟩, d⟩,
      fun h2 => by obtain ⟨c, d⟩ := b h2; exact ⟨⟨c, VsReach.root2 hp ho h8 h2⟩, d⟩⟩
  · obtain ⟨a, b⟩ := h.desc p hp.1 hp.2 hl o ho h8 h3
    exact ⟨⟨a, VsReach.step hp.2 hl ho h8 h3⟩, b⟩

/-- **`S2TyR` is `S2Ty` over some sub-table-set.** -/
theorem S2TyR.iff {s : S} : S2TyR st n Pp Hr Te Re bits s ↔ ∃ T' ⊆ Te, S2Ty st n Pp Hr T' Re bits s :=
  ⟨fun h => ⟨_, S2Rt_sub, h.sub⟩, fun ⟨_, hT, h⟩ => h.toRsub hT⟩

/-- **`VsTyR` is `VsTy` over some sub-table-set containing `Hr`.** -/
theorem VsTyR.iff {s : S} (hH : Hr ⊆ Tb) :
    VsTyR st kb Pp Hr Tb Lv s ↔ ∃ T' ⊆ Tb, Hr ⊆ T' ∧ VsTy st kb Pp T' Lv s :=
  ⟨fun h => ⟨_, VsRt_sub, hr_rt hH, h.sub⟩, fun ⟨_, hT, hH', h⟩ => h.toRsub hT hH'⟩

/-- **The narrowed typing grows with `Te`** (an unreachable object owes nothing). -/
theorem S2TyR.mono {s : S} (h : S2TyR st n Pp Hr Te Re bits s) (hT : Te ⊆ T') : S2TyR st n Pp Hr T' Re bits s :=
  h.sub.toRsub (S2Rt_sub.trans hT)

theorem VsTyR.mono {s : S} (h : VsTyR st kb Pp Hr Tb Lv s) (hH : Hr ⊆ Tb) (hT : Tb ⊆ T') :
    VsTyR st kb Pp Hr T' Lv s :=
  h.sub.toRsub (VsRt_sub.trans hT) (hr_rt hH)

/-! ## The table-set hypotheses at the reachable part -/

theorem S2Pl.mono (hD : S2Pl kb Pp Tb Te bits) {Tb' : Set U64} (hT : T' ⊆ Te) (hB : Tb' ⊆ Tb) :
    S2Pl kb Pp Tb' T' bits :=
  ⟨fun p hp => hD.pa p (hT hp), fun b hb => hD.pp b (ptwb_mono hT hb),
    fun b hb hb' => hD.tb b (ptwb_mono hT hb) (ptw_mono hB hb'), fun b hb => hD.asw b (ptwb_mono hT hb),
    fun p hp q hq o o' ho h8 ho' h8' e => hD.un p (hT hp) q (hT hq) o o' ho h8 ho' h8' e⟩

theorem S1Pl.mono (hD : S1Pl kb Pp Tb) (hT : T' ⊆ Tb) : S1Pl kb Pp T' :=
  ⟨fun p hp => hD.pa p (hT hp), fun b hb => hD.pp b (ptw_mono hT hb), fun b hb => hD.asw b (ptw_mono hT hb),
    fun p hp q hq o o' ho h8 ho' h8' e => hD.un p (hT hp) q (hT hq) o o' ho h8 ho' h8' e⟩

theorem _root_.Fl4ProofsA64.P1.HrOK.mono (h : HrOK kb Pp Tb Lv Hr) (hT : T' ⊆ Tb) (hH : Hr ⊆ T') : HrOK kb Pp T' Lv Hr :=
  ⟨hH, h.lv, fun t ht => h.tb t (hT ht), h.pp, h.asw⟩

theorem UnmZ.anti {OS : Set U64} {s : S} (hU : UnmZ st OS Pt Te bits s) (hT : T' ⊆ Te) :
    UnmZ st OS Pt T' bits s :=
  ⟨fun x hx p asid v hc => by
    obtain ⟨a, b⟩ := hU.pt x hx p asid v hc
    exact ⟨a, fun o ho h8 => ⟨fun hw => (b o ho h8).1 (ptwb_mono hT hw), (b o ho h8).2⟩⟩,
   fun x hx p asid v hc => by
    obtain ⟨a, b⟩ := hU.ept x hx p asid v hc
    exact ⟨a, fun o ho h8 => ⟨fun hw => (b o ho h8).1 (ptwb_mono hT hw), (b o ho h8).2⟩⟩⟩

theorem UnmT.anti {OS : Set U64} {s : S} (hU : UnmT st OS Tb s) (hT : T' ⊆ Tb) : UnmT st OS T' s :=
  fun x hx p m hc o ho h8 hw => hU x hx p m hc o ho h8 (ptw_mono hT hw)

end eqv

/-! ## The walks over the narrowed typings -/

section walkR
variable {kb n : U64} {Pp Tb Hr Te : Set U64} {Lv Re bits : U64 → Nat}

/-- **`ept::find` returns a reachable Stage-2 root.** -/
theorem ept.find.tyR {s : S} (h : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st n Pp Hr Te Re bits s)
    (hk : L.ksb s = kb) (asid : U64) :
    ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → r1 ∈ S2Rt st Pp Te Re bits s ∧ Re r1 + 1 = s2lv n ∧
      s2rb n ≤ bits r1 ⦄ :=
  ept.find.ty h.sub h2.sub hk asid

/-- **The Stage-2 walk stays in the reachable objects** (invariant `EkI` at `S2Rt`: the current table is
reachable). -/
theorem ept.lookup_slot_loop.tyR {s : S} (h2 : S2TyR st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr)
    (ipa shift slot rem : U64) (hi : EkI (S2Rt st Pp Te Re bits s) Re bits (shift, slot, rem)) :
    ept.lookup_slot_loop st s ipa shift slot rem ⦃ r => PtWb (S2Rt st Pp Te Re bits s) bits r.2 ⦄ :=
  ept.lookup_slot_loop.ty h2.sub (S2OK.sub hS S2Rt_sub) ipa shift slot rem hi

theorem ept.lookup_slot.tyR {s : S} (h2 : S2TyR st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) {root : U64}
    (hr : root ∈ S2Rt st Pp Te Re bits s) (hre : Re root + 1 = s2lv n) (hrb : s2rb n ≤ bits root) (ipa : U64) :
    ept.lookup_slot st s root ipa n ⦃ lu => PtWb (S2Rt st Pp Te Re bits s) bits lu.slot ⦄ :=
  ept.lookup_slot.ty h2.sub (S2OK.sub hS S2Rt_sub) hr hre hrb ipa

theorem ept.lookup_slot_loop.tyDR {s : S} (h2 : S2TyR st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr)
    (ipa shift slot rem : U64) (hi : EkD (S2Rt st Pp Te Re bits s) Re bits (shift, slot, rem)) :
    ept.lookup_slot_loop st s ipa shift slot rem ⦃ r => ∃ p ∈ S2Rt st Pp Te Re bits s, ∃ o : U64,
      o.val < 2 ^ bits p ∧ o.val % 8 = 0 ∧ r.2 = wa p o ∧ r.1.val = 9 * Re p + 12 ⦄ :=
  ept.lookup_slot_loop.tyD h2.sub (S2OK.sub hS S2Rt_sub) ipa shift slot rem hi

theorem ept.lookup_slot.tyDR {s : S} (h2 : S2TyR st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) {root : U64}
    (hr : root ∈ S2Rt st Pp Te Re bits s) (hre : Re root + 1 = s2lv n) (hrb : s2rb n ≤ bits root) (ipa : U64) :
    ept.lookup_slot st s root ipa n ⦃ lu => ∃ p ∈ S2Rt st Pp Te Re bits s, ∃ o : U64, o.val < 2 ^ bits p ∧
      o.val % 8 = 0 ∧ lu.slot = wa p o ∧ lu.shift.val = 9 * Re p + 12 ⦄ :=
  ept.lookup_slot.tyD h2.sub (S2OK.sub hS S2Rt_sub) hr hre hrb ipa

theorem ept.unmap_table_loop.tyR {s : S} (h2 : S2TyR st n Pp Hr Te Re bits s) (hS : S2OK Te bits Hr)
    (ipa pt table shift mask rem : U64) (hi : UtI (S2Rt st Pp Te Re bits s) Re bits (table, shift, mask, rem)) :
    ept.unmap_table_loop st s ipa pt table shift mask rem ⦃ r => ∀ sl, r = some sl →
      PtWb (S2Rt st Pp Te Re bits s) bits sl ⦄ :=
  ept.unmap_table_loop.ty h2.sub (S2OK.sub hS S2Rt_sub) ipa pt table shift mask rem hi

end walkR

section wrR
variable {A : Type _} {ar : machine.Arch A} {kb : U64} {Pp Tb Hr Te : Set U64} {Lv Re bits : U64 → Nat}

theorem ept.unmap.zR (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) {s : S} (h : VsTyR st kb Pp Hr Tb Lv s)
    (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) (hk : L.ksb s = kb) (a : A)
    (asid ipa ptr shift : U64) (it : Bool) :
    ept.unmap st ar s a asid ipa ptr shift it ⦃ r => Wr0 st (Gran (S2Rt st Pp Te Re bits s) bits) s r.1 ⦄ :=
  ept.unmap.z hA hPl h.sub h2.sub (S2OK.sub hS S2Rt_sub) hk a asid ipa ptr shift it

theorem ept.unmap_table.zR (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) {s : S} (h : VsTyR st kb Pp Hr Tb Lv s)
    (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s) (hS : S2OK Te bits Hr) (hk : L.ksb s = kb) (a : A)
    (asid ipa pt : U64) :
    ept.unmap_table st ar s a asid ipa pt ⦃ r => Wr0 st (Gran (S2Rt st Pp Te Re bits s) bits) s r.1 ⦄ :=
  ept.unmap_table.z hA hPl h.sub h2.sub (S2OK.sub hS S2Rt_sub) hk a asid ipa pt

/-- **`unmap_page_table` over the narrowed typings**: unchanged, or a word of a reachable Stage-1 table outside
`Hr` or of a reachable Stage-2 object written `0`. -/
theorem vspace.unmap_page_table.s2R (hA : P0.ArchTotal ar) (hPl : ArchPlat ar) (hO : HrOK kb Pp Tb Lv Hr)
    (hS : S2OK Te bits Hr) {s : S} (h0 : VsTyR st kb Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hk : L.ksb s = kb) (a : A) (asid vaddr pt : U64) :
    vspace.unmap_page_table st ar s a asid vaddr pt ⦃ r =>
      Wr0 st (TbO (VsRt st Pp Hr Tb Lv s) Hr ∪ Gran (S2Rt st Pp Te Re bits s) bits) s r.1 ⦄ :=
  vspace.unmap_page_table.s2 hA hPl (hO.mono VsRt_sub (hr_rt hO.sub)) (S2OK.sub hS S2Rt_sub) h0.sub h2.sub hk a asid
    vaddr pt

end wrR

/-! ## The rebuild lemmas over the narrowed typings -/

section rebR
variable {kb n : U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}

theorem S2TyR.keep {s s' : S} (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) (hS : S2OK Te bits Hr)
    (h : S2TyR st n Pp Hr Te Re bits s) (z : VsZ st kb Pt s s') (k : HrW st Hr s s') :
    S2TyR st n Pp Hr Te Re bits s' :=
  (h.sub.keep hPp ((gran_mono S2Rt_sub).trans hTe) (S2OK.sub hS S2Rt_sub) z k).toRsub S2Rt_sub

theorem S2TyR.of_hr {s : S} (h : HrTy st Pp Hr s) : S2TyR st n Pp Hr ∅ Re bits s :=
  (S2Ty.of_hr h).toR

theorem S2TyR.wr (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    (hS : S2OK Te bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64)) {s : S} {b v : U64} (hb : Aligned b)
    (h : S2TyR st n Pp Hr Te Re bits s)
    (hp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → v ≠ 0#u64 →
      TagC n Hr (S2Rt st Pp Te Re bits s) Re bits v)
    (hh : ∀ R ∈ Hr, wa R 4088#u64 ≠ b)
    (hd : ∀ p ∈ S2Rt st Pp Te Re bits s, 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 → wa p o = b →
      (v &&& 3#u64) = 3#u64 → DescC (S2Rt st Pp Te Re bits s) Re v (Re p)) :
    S2TyR st n Pp Hr Te Re bits (L.wr s b v) :=
  (S2Ty.wr hal hPp ((gran_mono S2Rt_sub).trans hTe) (S2OK.sub hS S2Rt_sub) hRal hb h.sub hp hh hd).toRsub S2Rt_sub

theorem S2TyR.wr3 (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTe : Gran Te bits ⊆ Pt)
    (hS : S2OK Te bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64)) {s : S} {b v : U64} (hb : Aligned b)
    (h : S2TyR st n Pp Hr Te Re bits s)
    (hp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → v ≠ 0#u64 →
      TagC n Hr (S2Rt st Pp Te Re bits s) Re bits v)
    (hh : ∀ R ∈ Hr, wa R 4088#u64 = b → (v &&& 3#u64) = 3#u64)
    (hd : ∀ p ∈ S2Rt st Pp Te Re bits s, 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 → wa p o = b →
      (v &&& 3#u64) = 3#u64 → DescC (S2Rt st Pp Te Re bits s) Re v (Re p)) :
    S2TyR st n Pp Hr Te Re bits (L.wr s b v) :=
  (S2Ty.wr3 hal hPp ((gran_mono S2Rt_sub).trans hTe) (S2OK.sub hS S2Rt_sub) hRal hb h.sub hp hh hd).toRsub S2Rt_sub

/-- **A new Stage-2 object joins `Te`** — no side condition: unreachable objects owe nothing. -/
theorem S2TyR.addT {s : S} {t : U64} (h : S2TyR st n Pp Hr Te Re bits s) : S2TyR st n Pp Hr (insert t Te) Re bits s :=
  h.mono (Set.subset_insert t Te)

theorem S2TyR.congr {s : S} {Re' bits' : U64 → Nat} (h : S2TyR st n Pp Hr Te Re bits s)
    (hRe : ∀ p ∈ Te, Re' p = Re p) (hbits : ∀ p ∈ Te, bits' p = bits p) : S2TyR st n Pp Hr Te Re' bits' s :=
  (S2Ty.congr h.sub (fun p hp => hRe p hp.1) (fun p hp => hbits p hp.1)).toRsub S2Rt_sub

/-- **`ept::map_table`'s descriptor write over the narrowed typing**: the slot of a reachable table written with a
table descriptor of `t`; `t` joins `Te` (it may already be there, unreachable). -/
theorem S2TyR.map_table (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) {t : U64}
    (hTe : Gran (insert t Te) bits ⊆ Pt) (hS : S2OK (insert t Te) bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64))
    {s : S} (h : S2TyR st n Pp Hr Te Re bits s) {p o v : U64} (hp : p ∈ S2Rt st Pp Te Re bits s)
    (ho : o.val < 2 ^ bits p) (h8 : o.val % 8 = 0)
    (hun : ∀ q ∈ insert t Te, ∀ o' : U64, o'.val < 2 ^ bits q → o'.val % 8 = 0 → wa q o' = wa p o → q = p)
    (hnp : ∀ q ∈ Pp, ∀ o' : U64, o'.val < 4096 → o'.val % 8 = 0 → wa q o' ≠ wa p o)
    (hRt : Re t + 1 = Re p)
    (hz : 0 < Re t → ∀ o : U64, o.val < 2 ^ bits t → o.val % 8 = 0 → (L.mem s (wa t o) &&& 3#u64) ≠ 3#u64)
    (hvt : wa (v &&& ept.ADDR_MASK) layout.PPTR_BASE = t) :
    S2TyR st n Pp Hr (insert t Te) Re bits (L.wr s (wa p o) v) :=
  have hsub : insert t (S2Rt st Pp Te Re bits s) ⊆ insert t Te := Set.insert_subset_insert S2Rt_sub
  (S2Ty.map_table hal hPp ((gran_mono hsub).trans hTe) (S2OK.sub hS hsub) hRal h.sub hp ho h8
    (fun q hq => hun q (hsub hq)) hnp hRt hz hvt).toRsub hsub

theorem S2TyR.assign1 (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) {r : U64}
    (hTe : Gran (insert r Te) bits ⊆ Pt) (hS : S2OK (insert r Te) bits Hr) (hRal : ∀ R ∈ Hr, Aligned (wa R 4088#u64))
    {s : S} (h : S2TyR st n Pp Hr Te Re bits s) {q o v : U64} (hq : q ∈ Pp) (ho : o.val < 4096) (h8 : o.val % 8 = 0)
    (hhr : ∀ R ∈ Hr, wa R 4088#u64 ≠ wa q o)
    (hv1 : (v &&& 3#u64) = 1#u64) (hvr : (v &&& ~~~3#u64) = r) (hRr : Re r + 1 = s2lv n) (hrb : s2rb n ≤ bits r)
    (hz : ∀ o : U64, o.val < 2 ^ bits r → o.val % 8 = 0 → (L.mem s (wa r o) &&& 3#u64) ≠ 3#u64) :
    S2TyR st n Pp Hr (insert r Te) Re bits (L.wr s (wa q o) v) :=
  have hsub : insert r (S2Rt st Pp Te Re bits s) ⊆ insert r Te := Set.insert_subset_insert S2Rt_sub
  (S2Ty.assign1 hal hPp ((gran_mono hsub).trans hTe) (S2OK.sub hS hsub) hRal h.sub hq ho h8 hhr hv1 hvr hRr hrb
    hz).toRsub hsub

/-- **The reachable form of `S2Ty.drop`**: tables named by no tag-1 pool entry and by no descriptor of a reachable
table outside them are unreachable. -/
theorem S2TyR.drop {D : Set U64} {s : S} (h : S2TyR st n Pp Hr Te Re bits s)
    (htag : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa p o) &&& 3#u64) = 1#u64 →
      (L.mem s (wa p o) &&& ~~~3#u64) ∉ D)
    (hdesc : ∀ p ∈ S2Rt st Pp Te Re bits s, p ∉ D → 0 < Re p → ∀ o : U64, o.val < 2 ^ bits p → o.val % 8 = 0 →
      (L.mem s (wa p o) &&& 3#u64) = 3#u64 → wa (L.mem s (wa p o) &&& ept.ADDR_MASK) layout.PPTR_BASE ∉ D) :
    ∀ d ∈ D, ¬ S2Reach st Pp Re bits s d :=
  fun _ hd hr => ((S2Ty.drop h.sub htag hdesc).reach hr).2 hd

theorem VsTyR.keepZ {s s' : S} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hH : Hr ⊆ Tb) (h : VsTyR st kb Pp Hr Tb Lv s)
    (k : VsZ st kb Pt s s') : VsTyR st kb Pp Hr Tb Lv s' :=
  (h.sub.keepZ hPp (VsRt_sub.trans hTb) k).toRsub VsRt_sub (hr_rt hH)

theorem VsTyR.wr (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hH : Hr ⊆ Tb) {s : S}
    {b v : U64} (hb : Aligned b) (h : VsTyR st kb Pp Hr Tb Lv s)
    (ht : ∀ o : U64, 772352 ≤ o.val → o.val < 773376 → o.val % 8 = 0 → wa kb o = b → v ≠ 0#u64 → v ∈ Pp)
    (hp : ∀ p ∈ Pp, ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b → v ≠ 0#u64 →
      PoolC (VsRt st Pp Hr Tb Lv s) Lv v)
    (hd : ∀ p ∈ VsRt st Pp Hr Tb Lv s, Lv p < 3 → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → wa p o = b →
      (v &&& 3#u64) = 3#u64 → VDescC (VsRt st Pp Hr Tb Lv s) Lv v (Lv p)) :
    VsTyR st kb Pp Hr Tb Lv (L.wr s b v) :=
  (VsTy.wr hal hPp (VsRt_sub.trans hTb) hb h.sub ht hp hd).toRsub VsRt_sub (hr_rt hH)

/-- **A new table joins `Tb`** — no side condition. -/
theorem VsTyR.addT {s : S} {t : U64} (hH : Hr ⊆ Tb) (h : VsTyR st kb Pp Hr Tb Lv s) :
    VsTyR st kb Pp Hr (insert t Tb) Lv s :=
  h.mono hH (Set.subset_insert t Tb)

theorem VsTyR.congrL {s : S} {Lv' : U64 → Nat} (hH : Hr ⊆ Tb) (h : VsTyR st kb Pp Hr Tb Lv s)
    (hL : ∀ p ∈ Tb, Lv' p = Lv p) : VsTyR st kb Pp Hr Tb Lv' s := by
  have h1 : VsTy st kb Pp (VsRt st Pp Hr Tb Lv s) Lv' s := VsTy.congrL h.sub fun p hp => hL p hp.1
  exact h1.toRsub VsRt_sub (hr_rt hH)

/-- **A Stage-1 table map's descriptor write over the narrowed typing**: the new table need only be unreachable
(not outside `Tb`). -/
theorem VsTyR.map_table (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) {t : U64} (hTb : insert t Tb ⊆ Pt)
    (hH : Hr ⊆ Tb) (hP1 : S1Pl kb Pp (insert t Tb)) {s : S} (h : VsTyR st kb Pp Hr Tb Lv s)
    (ht : t ∉ VsRt st Pp Hr Tb Lv s) {p o v : U64} (hp : p ∈ VsRt st Pp Hr Tb Lv s) (ho : o.val < 4096)
    (h8 : o.val % 8 = 0) (hz : ∀ o : U64, o.val < 4096 → o.val % 8 = 0 → (L.mem s (wa t o) &&& 3#u64) ≠ 3#u64)
    (hvt : wa (v &&& vspace.ADDR_MASK) layout.PPTR_BASE = t) :
    VsTyR st kb Pp Hr (insert t Tb) (Function.update Lv t (Lv p + 1)) (L.wr s (wa p o) v) :=
  have hsub : insert t (VsRt st Pp Hr Tb Lv s) ⊆ insert t Tb := Set.insert_subset_insert VsRt_sub
  (VsTy.map_table hal hPp (hsub.trans hTb) (hP1.mono hsub) h.sub ht hp ho h8 hz hvt).toRsub hsub
    ((hr_rt hH).trans (Set.subset_insert t _))

theorem VsTyR.assign1 (hal : ∀ w, VsR kb Pt w → Aligned w) (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hH : Hr ⊆ Tb) {s : S}
    (h : VsTyR st kb Pp Hr Tb Lv s) {q o v : U64} (hq : q ∈ Pp) (ho : o.val < 4096) (h8 : o.val % 8 = 0)
    (hnA : ¬ AsW kb (wa q o)) (hv1 : (v &&& 3#u64) = 1#u64) :
    VsTyR st kb Pp Hr Tb Lv (L.wr s (wa q o) v) :=
  (VsTy.assign1 hal hPp (VsRt_sub.trans hTb) h.sub hq ho h8 hnA hv1).toRsub VsRt_sub (hr_rt hH)

end rebR

/-! ## The deletion keeps the narrowed typings -/

section delR
variable {OS Vc Ub D Fp : Set U64} {Pp Tb Pt Hr Te : Set U64} {Lv Re bits : U64 → Nat}
variable {A : Type _} {ar : machine.Arch A}

/-- **The exposed `cdt.delete` of a `ZQ S2Q` slot keeps `JV` and the narrowed typings** (gen 41's
`cdt.delete.zqET` at the reachable parts). -/
theorem cdt.delete.zqETR (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hX : XQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.zqET hP hPl hO hA hV hDO hDC hPp (VsRt_sub.trans hTb) ((gran_mono S2Rt_sub).trans hTe)
    hR (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub) hW hIO hap h hx hxI hD hX hN hY.sub h2.sub)
    fun _ ⟨j, y, z⟩ => ⟨j, y.toRsub VsRt_sub (hr_rt hH.sub), z.toRsub S2Rt_sub⟩

/-- **The thread kind over a domain of `ZQ S2Q` caps keeps `JV` and the narrowed typings** (gen 41's
`cdt.delete.threadQET` at the reachable parts). -/
theorem cdt.delete.threadQETR (hP : P0.ArchTotal ar) (hPl : ArchPlat ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt) (hTe : Gran Te bits ⊆ Pt) {s0 s : S}
    (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt) (hH : HrOK (L.ksb s0) Pp Tb Lv Hr) (hS : S2OK Te bits Hr)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x p : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st S2Q Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s) (hN : IrqN st (L.ksb s0) s)
    (hY : VsTyR st (L.ksb s0) Pp Hr Tb Lv s) (h2 : S2TyR st hPl.ipa Pp Hr Te Re bits s)
    (hc : obj.Slot.cap st x s = ok (.Thread p)) (hid : p ≠ L.idleW s) (hpF : p ∉ Fp)
    (hcov : ∀ i : U64, i.val < 7 → slotIdx p i ∈ D) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      VsTyR st (L.ksb s0) Pp Hr Tb Lv r.2.1 ∧ S2TyR st hPl.ipa Pp Hr Te Re bits r.2.1 ⦄ :=
  WP.spec_mono (cdt.delete.threadQET hP hPl hO hA hV hDO hDC hPp (VsRt_sub.trans hTb)
    ((gran_mono S2Rt_sub).trans hTe) hR (hH.mono VsRt_sub (hr_rt hH.sub)) (S2OK.sub hS S2Rt_sub) hW hIO hap h hx hxI hD
    hN hY.sub h2.sub hc hid hpF hcov)
    fun _ ⟨j, y, z⟩ => ⟨j, y.toRsub VsRt_sub (hr_rt hH.sub), z.toRsub S2Rt_sub⟩

end delR

end ST
end R
end W7

end

end Fl4ProofsA64.P1
