/-
P3 (line mmuAD, gen 42b14): **the EPT table unmap's perform half at `EptCore`** — after P3/EptTableUnmapDec's decode
(the restart, P3/EptUnmapRel's `ept::unmap` with `UnmapOut`), FL4's `s.zero(ptr, 4096)` and `set_cap` of the unmapped
cap (crates/fl4-core/src/ept.rs l. 276-282) against the spec's `performEptInvocation (.tableUnmap …)`
(Fl4Spec/Ext/VirtEptInv l. 227-233: `guestUnmap`, then `getEpt ptr` / `setObject ptr (.ept l 0)`, then `setCap`).

* Spec: `storeGuestEntry_eq`, **`performTableUnmap_some`** / **`performTableUnmap_none`** (the perform's single
  outcome; an unmapped cap's unmap does nothing on the spec side), `EptTableUnmapSpec` (restart, then perform).
* Walk paths: `PoolAt.uniq`, `eptChild_inj`, `eptChild_lkLvl`, **`GPath.inv`** (a path at a nonzero level ends with a
  walked entry of the path one level up), **`GPath.uniq`** (one table per ASID, address and level),
  `guestIndex_gKey` / **`GPath.congr`** (a path depends only on the address bits at or above its level),
  **`lookup_of_path`** (`guestLookupSlot` follows a path), **`guestUnmap_reach`** (`guestUnmap` of a reachable table
  clears its parent entry).
* **`EptCore.unmapUnreach`** (the Architect's "unique path from `EptNamed` + `is_final_capability`"): after the unmap
  (either outcome of `UnmapOut`), the unmapped table `ptr` of the final mapped cap `Ept ptr lv true asid va` is
  reached by no path at a nonzero level. A path to `ptr` is a path before (`GPath.storeNW`); `EptNamed` names it by a
  mapped cap, which is `dest` by finality (`huq`), so it runs along `asid` and `va`'s bits above `lv` (`EptNamed.all`);
  its parent is the table `ept::unmap` looked up (`GPath.congr` + `GPath.uniq`): a hit cleared that entry, and a miss
  is impossible (`guestUnmap_reach`: the spec's tests pass on a walked entry naming `ptr`).
* **`EptCore.clearZ`**: `EptCore` across the zeroing of a table of `X` on both sides with every slot kept
  (P3/EptStep3's `EptCore.clear` with `UnmappedEmpty` and `EptNamed` after proved: paths after are paths before).
* **`EptCore.unmapSlot`**: `EptCore` across the rewrite of the unique cap `dest` to a zero, unreachable table `ptr`
  into the unmapped `Ept ptr lv false 0 0` (FL4 `set_cap`, spec `setCap`, a `CnK` step).

No named premise. New file; root import after `P3.EptTableUnmapDec`. No existing statement changed.
-/
import Fl4Proofs.P3.EptTableUnmapDec
import Fl4Proofs.P3.EptTableMapV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-! ## Spec side -/

section Spec
open Fl4Spec Fl4Proofs.P3.Notif

theorem storeGuestEntry_eq {σ : State Unit} {t : ObjRef} {l : Nat} {es : BitVec 9 → Word}
    (ht : σ.kheap t = some (.archObj (.ept l es))) (i : BitVec 9) (e : Word) :
    storeGuestEntry (Z := Unit) t i e σ = ({((), updK σ t (.archObj (.ept l (Function.update es i e))))}, False) := by
  unfold storeGuestEntry
  rw [Notif.nd_bind_one (getEpt_eq ht)]
  exact setObject_eq ht rfl

/-- **The spec's perform of the unmap of a mapped table** (`performEptInvocation (.tableUnmap … (some …) …)`):
`guestUnmap` (single outcome `σ2`), the table `ptr` cleared, then the CNode slot `(pc, idx)` set to the unmapped cap. -/
theorem performTableUnmap_some {σ σ2 : State Unit} {asid gpa ptr : ObjRef} {lv : Nat}
    (hG : guestUnmap (Z := Unit) asid gpa ptr lv true σ = ({((), σ2)}, False)) {l : Nat} {es : BitVec 9 → Word}
    (hk : σ2.kheap ptr = some (.archObj (.ept l es))) {pc : ObjRef} {r : Nat} {cs : CnodeContents}
    {idx : List Bool} (hkc : σ2.kheap pc = some (.cnode r cs)) (hwf : wellFormedCnodeN r cs) (hidx : idx.length = r) :
    performEptInvocation (Z := Unit) (.tableUnmap ptr lv (some (asid, gpa)) (pc, idx)) σ =
      ({((), setCnodeSlot (updK σ2 ptr (.archObj (.ept l fun _ => 0))) pc r cs idx
        (.archObjectCap (.eptCap ptr lv none)))}, False) := by
  have hpc : ptr ≠ pc := Endp.kheap_ne hk hkc (fun _ h1 h2 => by subst h1; cases h2)
  unfold performEptInvocation
  dsimp only
  rw [Notif.nd_bind_one hG, Notif.nd_bind_one (getEpt_eq hk)]
  dsimp only
  rw [Notif.nd_bind_one (setObject_eq (o' := .archObj (.ept l fun _ => 0)) hk rfl)]
  have hk' : (updK σ2 ptr (.archObj (.ept l fun _ => 0))).kheap pc = some (.cnode r cs) := by
    simp [updK, hpc.symm, hkc]
  exact setCap_cnode _ hk' hwf hidx

/-- The spec's perform of the unmap of an unmapped table: nothing (the `none` arm's `return ()` leaves the
perform; the slot already holds the unmapped cap, `absCap` of FL4's `Ept ptr level false 0 0`). -/
theorem performTableUnmap_none (σ : State Unit) (ptr : ObjRef) (lv : Nat) (sl : CslotPtr) :
    performEptInvocation (Z := Unit) (.tableUnmap ptr lv none sl) σ = ({((), σ)}, False) := by
  unfold performEptInvocation
  dsimp only
  rfl

/-- The spec after the table unmap's decode: `set_thread_state cur Restart`, then the perform, with the single
outcome `σ'`. -/
def EptTableUnmapSpec (σ : State Unit) (ptr : ObjRef) (lv : Nat) (mp : Option (Asid × VSpaceRef)) (sl : CslotPtr)
    (σ' : State Unit) : Prop :=
  (setThreadState (Z := Unit) σ.curThread .restart >>= fun _ =>
    performEptInvocation (.tableUnmap ptr lv mp sl)) σ = ({((), σ')}, False)

end Spec

/-! ## Walk paths -/

theorem PoolAt.uniq {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {e e' : Fl4Spec.ObjRef} (h : PoolAt σ hi lo e) (h' : PoolAt σ hi lo e') : e' = e := by
  obtain ⟨p, f, h1, h2, h3⟩ := h
  obtain ⟨p', f', h1', h2', h3'⟩ := h'
  rw [h1] at h1'
  cases h1'
  rw [h2] at h2'
  cases h2'
  rw [h3] at h3'
  cases h3'
  rfl

theorem eptChild_inj {l l' c : Nat} (h : eptChild l = some c) (h' : eptChild l' = some c) : l' = l := by
  rcases eptChild_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rcases eptChild_cases h' with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> first | rfl | (exact absurd h (by decide))

theorem eptChild_lkLvl {l c : Nat} (h : eptChild l = some c) : l = lkLvl c := by
  rcases eptChild_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- **A path at a nonzero level ends with a walked entry of a path one level up.** -/
theorem GPath.inv {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {gpa : Fl4Spec.Word} {c : Nat} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo gpa c u) (hc : c ≠ 0) :
    ∃ l t es, eptChild l = some c ∧ GPath σ hi lo gpa l t ∧ σ.kheap t = some (.archObj (.ept l es)) ∧
      GWalkE l es (Fl4Spec.guestIndex gpa c) ∧
      u = Fl4Spec.ptrFromPAddr (es (Fl4Spec.guestIndex gpa c) &&& Fl4Spec.guestPteAddress) := by
  cases h with
  | root _ _ => exact absurd rfl hc
  | step hp hk hch hw => exact ⟨_, _, _, hch, hp, hk, hw, rfl⟩

/-- **One table per ASID, address and level.** -/
theorem GPath.uniq {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {gpa : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo gpa l u) :
    ∀ {u'}, GPath σ hi lo gpa l u' → u' = u := by
  induction h with
  | root hp h1 =>
    intro u' h'
    obtain ⟨e', he', -, rfl⟩ := h'.zero
    rw [PoolAt.uniq hp he']
  | @step l c t es _ hk hc _ ih =>
    intro u' h'
    have hc0 : c ≠ 0 := by rcases eptChild_cases hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    obtain ⟨l', t', es', hc', hp', hk', -, rfl⟩ := h'.inv hc0
    obtain rfl := eptChild_inj hc hc'
    obtain rfl := ih hp'
    rw [hk] at hk'
    cases hk'
    rfl

/-- The index at `c ≥ l` of the address bits above `l` is the address's. -/
theorem guestIndex_gKey (x : Fl4Spec.Word) {l c : Nat} (hl : l < 64) (hlc : l ≤ c) (hc : c ≤ 39) :
    Fl4Spec.guestIndex (gKey x l) c = Fl4Spec.guestIndex x c := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [guestIndex_getLsbD _ _ hj, guestIndex_getLsbD _ _ hj, gKey_getLsbD x hl (by omega)]
  simp [show l ≤ c + j by omega]

theorem GPath.congrM {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {g g' : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo g l u) (m : Nat)
    (hix : ∀ c, c ≠ 0 → m ≤ c → c ≤ 39 → Fl4Spec.guestIndex g c = Fl4Spec.guestIndex g' c)
    (hm : l = 0 ∨ m ≤ l) : GPath σ hi lo g' l u := by
  induction h with
  | root hp h1 => exact .root hp h1
  | @step l c t es _ hk hc hw ih =>
    have hcs := eptChild_cases hc
    have hc0 : c ≠ 0 := by omega
    have hmc : m ≤ c := hm.resolve_left hc0
    have e := hix c hc0 hmc (by omega)
    have hl' : l = 0 ∨ m ≤ l := by omega
    rw [e] at hw ⊢
    exact .step (ih hl') hk hc hw

/-- **A path depends only on the address bits at or above its level.** -/
theorem GPath.congr {σ : Fl4Spec.State Unit} {hi : Fl4Spec.AsidHighIndex} {lo : Fl4Spec.AsidLowIndex}
    {g g' : Fl4Spec.Word} {l : Nat} {u : Fl4Spec.ObjRef} (h : GPath σ hi lo g l u) {m : Nat} (hm : l = 0 ∨ m ≤ l)
    (hix : ∀ c, c ≠ 0 → m ≤ c → c ≤ 39 → Fl4Spec.guestIndex g c = Fl4Spec.guestIndex g' c) : GPath σ hi lo g' l u :=
  h.congrM m hix hm

section Spec2
open Fl4Spec Fl4Proofs.P3.Notif

/-- **`guestLookupSlot` follows a path** to the table one level above `lv`. -/
theorem lookup_of_path {σ : State Unit} {hi : AsidHighIndex} {lo : AsidLowIndex} {g : Word} {e : ObjRef}
    (hp : PoolAt σ hi lo e) {lv : Nat} {t : ObjRef} (hlv : lv = 39 ∨ lv = 30 ∨ lv = 21)
    (h : GPath σ hi lo g (lkLvl lv) t) :
    (guestLookupSlot (Z := Unit) (asidEntryRoot e) g lv).run σ = ({(.ok t, σ)}, False) := by
  unfold guestLookupSlot
  -- the root
  have hroot : ∀ u, GPath σ hi lo g 0 u → u = asidEntryRoot e := fun u hu => by
    obtain ⟨e', he', -, rfl⟩ := hu.zero
    rw [PoolAt.uniq hp he']
  -- one step down from a level-`l` table
  have hstep : ∀ {l c u}, GPath σ hi lo g c u → eptChild l = some c → ∃ t0 es, GPath σ hi lo g l t0 ∧
      σ.kheap t0 = some (.archObj (.ept l es)) ∧ GWalkE l es (guestIndex g c) ∧
      u = ptrFromPAddr (es (guestIndex g c) &&& guestPteAddress) := by
    intro l c u hu hc
    have hc0 : c ≠ 0 := by rcases eptChild_cases hc with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> omega
    obtain ⟨l', t0, es, hc', hp0, hk, hw, rfl⟩ := hu.inv hc0
    obtain rfl := eptChild_inj hc hc'
    exact ⟨t0, es, hp0, hk, hw, rfl⟩
  have hnot : ∀ {l es i}, GWalkE l es i → ¬ (es i &&& 1 = 0 ∨ es i &&& 128 ≠ 0) := fun hw h =>
    h.elim hw.2.2.1 fun h' => h' hw.2.2.2
  rcases hlv with rfl | rfl | rfl
  · have h0 : GPath σ hi lo g 0 t := h
    rw [hroot t h0, go_stop _ _ (by omega)]
  · have h1 : GPath σ hi lo g 39 t := h
    obtain ⟨t0, es0, hp0, hk0, hw0, rfl⟩ := hstep h1 (show eptChild 0 = some 39 from rfl)
    rw [← hroot t0 hp0, go_gt _ hk0 (by omega), if_neg (hnot hw0), go_stop _ _ (by omega)]
  · have h2 : GPath σ hi lo g 30 t := h
    obtain ⟨t1, es1, hp1, hk1, hw1, rfl⟩ := hstep h2 (show eptChild 39 = some 30 from rfl)
    obtain ⟨t0, es0, hp0, hk0, hw0, rfl⟩ := hstep hp1 (show eptChild 0 = some 39 from rfl)
    rw [← hroot t0 hp0, go_gt _ hk0 (by omega), if_neg (hnot hw0), go_gt _ hk1 (by omega), if_neg (hnot hw1),
      go_stop _ _ (by omega)]

/-- **`guestUnmap` of a table reachable through a walked entry of `tp` clears that entry.** -/
theorem guestUnmap_reach {σ : State Unit} {asid g : Word} {lv : Nat} (hlv : lv = 39 ∨ lv = 30 ∨ lv = 21)
    {tp : ObjRef} (hp : GPath σ (asidHighBitsOf asid) (asidLowBitsOf asid) g (lkLvl lv) tp)
    {l : Nat} {es : BitVec 9 → Word} (hk : σ.kheap tp = some (.archObj (.ept l es)))
    (hw : GWalkE l es (guestIndex g lv)) {ptr : ObjRef}
    (hptr : ptr = ptrFromPAddr (es (guestIndex g lv) &&& guestPteAddress)) :
    guestUnmap (Z := Unit) asid g ptr lv true σ = storeGuestEntry (Z := Unit) tp (guestIndex g lv) 0 σ := by
  obtain ⟨e, he, h1, -⟩ := hp.root_tag
  obtain ⟨p, f, hp1, hp2, hp3⟩ := he
  have hF : ExceptT.run (findGuestRoot (Z := Unit) asid) σ = ({(.ok (asidEntryRoot e), σ)}, False) := by
    rw [findGuestRoot_some hp1 hp2, hp3]
    have h1' : ¬ e &&& 1 = 0 := by rw [h1]; decide
    simp only [gRootRes, if_neg h1']
  have hL := lookup_of_path ⟨p, f, hp1, hp2, hp3⟩ hlv hp
  refine guestUnmap_hit hF hL hk ?_
  rintro (h | ⟨-, h⟩ | h)
  · exact hw.2.2.1 h
  · apply h; simp only [unmapLarge, Bool.not_true, Bool.false_and]; exact decide_eq_false (fun h' => h' hw.2.2.2)
  · apply h
    have hm : unmapMsk lv true = guestPteAddress := by simp [unmapMsk, unmapLarge]
    rw [hm, hptr]
    unfold addrFromPPtr ptrFromPAddr
    exact (BitVec.add_sub_cancel _ _).symm

end Spec2

/-! ## `EptCore` -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]
variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **The unmapped table is unreachable after the unmap** (module docstring): from `EptCore` at the restart state, the
final mapped cap `Ept ptr lv true asid va` in `dest` (no other slot names `ptr`: `huq`, from finality) and
P3/EptUnmapRel's `UnmapOut`: the spec's single outcome `σ2` (unchanged, or the parent entry cleared), and `ptr` is
reached at `σ2` by no path at a nonzero level. -/
theorem EptCore.unmapUnreach (C : EptCore (L := L) X XL th s σ) {dest ptr lv asid va : U64} (hd : IsSlot th dest)
    (hdc : capV (L.mem s) dest = .Ept ptr lv true asid va) (hlv : lv.val = 39 ∨ lv.val = 30 ∨ lv.val = 21)
    (huq : ∀ y, IsSlot th y → y ≠ dest → ∀ l (mm : Bool) a v, capV (L.mem s) y ≠ .Ept ptr l mm a v) {s3 : S}
    (hU : UnmapOut (L := L) X XL σ s asid va ptr lv true s3
      (Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv lv.val true σ)) :
    ∃ σ2 : Fl4Spec.State Unit,
      Fl4Spec.guestUnmap (Z := Unit) asid.bv va.bv ptr.bv lv.val true σ = ({((), σ2)}, False) ∧
      ((s3 = s ∧ σ2 = σ) ∨
        (∃ t ∈ X, ∃ es, XL t = lkLvl lv.val ∧
          GPath σ (Fl4Spec.asidHighBitsOf asid.bv) (Fl4Spec.asidLowBitsOf asid.bv) va.bv (lkLvl lv.val) t.bv ∧
          σ.kheap t.bv = some (.archObj (.ept (XL t) es)) ∧
          s3 = L.wr s (eptA t (Fl4Spec.guestIndex va.bv lv.val)) 0#u64 ∧
          σ2 = Notif.updK σ t.bv (.archObj (.ept (XL t) (Function.update es (Fl4Spec.guestIndex va.bv lv.val) 0))))) ∧
      ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ2 hi lo g l ptr.bv := by
  have hl64 : lv.val < 64 := by omega
  -- a path to `ptr` runs along `asid` and `va`'s bits, at `lv`
  have key : ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → GPath σ hi lo g l ptr.bv →
      l = lv.val ∧ hi = Fl4Spec.asidHighBitsOf asid.bv ∧ lo = Fl4Spec.asidLowBitsOf asid.bv ∧ va.bv = gKey g l := by
    intro hi lo g l hg hl hp
    obtain ⟨y, p, lv', a, v, hy, hpu, hlv', -, -, -, hc⟩ := C.named.ex hi lo g l _ hg hp hl
    have hpp : p = ptr := P1.eq_of_bv hpu
    rw [hpp] at hc
    have hyd : y = dest := by
      by_contra hne
      exact huq y hy hne lv' true a v hc
    rw [hyd, hdc] at hc
    obtain ⟨-, e1, -, -, -⟩ := capability.Cap.Ept.inj hc
    obtain ⟨-, a1, a2, a3⟩ := C.named.all hi lo g l _ hg hp hl dest ptr lv true asid va hd rfl hdc
    exact ⟨by rw [← hlv', ← e1], a1.symm, a2.symm, a3⟩
  have hlk : lkLvl lv.val = 0 ∨ lv.val ≤ lkLvl lv.val := by
    rcases hlv with h | h | h <;> rw [h] <;> decide
  have hix : ∀ g : Fl4Spec.Word, va.bv = gKey g lv.val →
      ∀ c, c ≠ 0 → lv.val ≤ c → c ≤ 39 → Fl4Spec.guestIndex g c = Fl4Spec.guestIndex va.bv c := by
    intro g hv c _ h1 h2
    rw [hv, guestIndex_gKey g hl64 h1 h2]
  rcases hU with ⟨rfl, ho⟩ |
    ⟨t, ht, es, hXt, hP, hk, hn, rfl, ho⟩
  · refine ⟨σ, ho, Or.inl ⟨rfl, rfl⟩, ?_⟩
    intro hi lo g l hg hl hp
    obtain ⟨rfl, rfl, rfl, hv⟩ := key hi lo g l hg hl hp
    obtain ⟨l', tp, es', hc', hpp, hkp, hwp, hptr⟩ := hp.inv hl
    obtain rfl := eptChild_lkLvl hc'
    have hpv := hpp.congr hlk (hix g hv)
    have hi0 := hix g hv lv.val (by omega) le_rfl (by omega)
    rw [hi0] at hwp hptr
    rw [guestUnmap_reach hlv hpv hkp hwp hptr, storeGuestEntry_eq hkp] at ho
    have e1 := congrArg Prod.fst ho
    simp only [Set.singleton_eq_singleton_iff, Prod.mk.injEq, true_and] at e1
    have h2 : (Notif.updK σ tp (.archObj (.ept (lkLvl lv.val)
        (Function.update es' (Fl4Spec.guestIndex va.bv lv.val) 0)))).kheap tp = σ.kheap tp := by rw [e1]
    rw [hkp, Notif.updK_kheap, Function.update_self] at h2
    injection h2 with h2; injection h2 with h2; injection h2 with h2a h2
    have h3 := congrFun h2 (Fl4Spec.guestIndex va.bv lv.val)
    rw [Function.update_self] at h3
    exact hwp.2.2.1 (by rw [← h3]; simp)
  · set i := Fl4Spec.guestIndex va.bv lv.val with hi_def
    refine ⟨Notif.updK σ t.bv (.archObj (.ept (XL t) (Function.update es i 0))), by rw [ho, storeGuestEntry_eq hk], Or.inr ⟨t, ht, es, hXt, hP, hk, rfl, rfl⟩, ?_⟩
    intro hi lo g l hg hl hp
    have hk2 : (Notif.updK σ t.bv (.archObj (.ept (XL t) (Function.update es i 0)))).kheap t.bv =
        some (.archObj (.ept (XL t) (Function.update es i 0))) := by simp [Notif.updK]
    have hoth : ∀ r, r ≠ t.bv → (Notif.updK σ t.bv (.archObj (.ept (XL t) (Function.update es i 0)))).kheap r =
        σ.kheap r := fun r hr => by simp [Notif.updK, hr]
    have hnw : ¬ GWalkE (XL t) (Function.update es i 0) i := fun h => h.2.2.1 (by simp)
    have hp0 := GPath.storeNW hk hk2 hoth rfl hnw hp
    obtain ⟨rfl, rfl, rfl, hv⟩ := key hi lo g l hg hl hp0
    obtain ⟨l', tp, es', hc', hpp, hkp, hwp, -⟩ := hp.inv hl
    obtain rfl := eptChild_lkLvl hc'
    have hpv := (GPath.storeNW hk hk2 hoth rfl hnw hpp).congr hlk (hix g hv)
    have htp : tp = t.bv := hP.uniq hpv
    subst htp
    rw [hk2] at hkp
    injection hkp with hkp; injection hkp with hkp; injection hkp with hla hes
    have hi0 := hix g hv lv.val (by omega) le_rfl (by omega)
    rw [hi0, ← hes, ← hXt] at hwp
    exact hnw hwp

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across the zeroing of a table of `X` on both sides, every slot kept** (module docstring). -/
theorem EptCore.clearZ (C : EptCore (L := L) X XL th s σ) {s' : S} {ptr : U64} (hpX : ptr ∈ X) {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hW : ∀ b, W b → ptr.val ≤ b.val ∧ b.val < ptr.val + 4096)
    (hz : ∀ i : BitVec 9, L.mem s' (eptA ptr i) = 0#u64) (hSS : SlotsSame th (L.mem s) (L.mem s')) :
    EptCore (L := L) X XL th s' (Notif.updK σ ptr.bv (.archObj (.ept (XL ptr) fun _ => 0))) := by
  set σ' := Notif.updK σ ptr.bv (.archObj (.ept (XL ptr) fun _ => 0)) with hσ'
  obtain ⟨esp, hkp, -⟩ := C.rel.obj ptr hpX
  have hk' : σ'.kheap ptr.bv = some (.archObj (.ept (XL ptr) fun _ => 0)) := by simp [hσ', Notif.updK]
  have hoth : ∀ r, r ≠ ptr.bv → σ'.kheap r = σ.kheap r := fun r hr => by simp [hσ', Notif.updK, hr]
  have hat : σ'.archState.x64AsidTable = σ.archState.x64AsidTable := rfl
  have hpa : ∀ hi lo e, PoolAt σ' hi lo e → PoolAt σ hi lo e := by
    rintro hi lo e ⟨q, f, g1, g2, g3⟩
    have hq : q ≠ ptr.bv := fun e' => by subst e'; rw [hk'] at g2; cases g2
    exact ⟨q, f, g1, by rw [← hoth q hq]; exact g2, g3⟩
  have hge : ∀ x, GuestEntry σ' x → GuestEntry σ x := by
    rintro x ⟨hi, q, f, lo, h1, h2, h3⟩
    exact (hpa hi lo x ⟨q, f, h1, h2, h3⟩).guest
  have hxk : ∀ t ∈ X, t ≠ ptr → σ'.kheap t.bv = σ.kheap t.bv :=
    fun t _ hne => hoth _ (fun h => hne (P1.eq_of_bv h))
  refine C.clear hpX hw (fun b hb => Or.inl (hW b hb)) hz hk' hxk
    (fun y hy p l a v mm hc => ⟨y, a, v, mm, hy, by rw [← hSS.capV hy]; exact hc⟩)
    (C.exte.of_eq fun y hy => hSS.capV hy) (fun r l es hk => ?_) hge (fun o ko' ho => ?_) ?_
    (EptSlotStep.ofSS hSS) ?_
  · by_cases hr : r = ptr.bv
    · subst hr; exact ⟨_, _, hkp⟩
    · rw [hoth r hr] at hk; exact ⟨l, es, hk⟩
  · by_cases hr : o = ptr.bv
    · subst hr
      rw [hk'] at ho; cases ho
      exact ⟨_, hkp, by rw [ept_bits, ept_bits]⟩
    · exact ⟨ko', by rw [← hoth o hr]; exact ho, rfl⟩
  · -- `UnmappedEmpty` after
    intro y hy p l a v hc
    rw [hSS.capV hy] at hc
    have hpX' : p ∈ X := by have h := C.exte.cap y hy; rw [hc] at h; exact h
    obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy p l a v hc
    refine ⟨fun i => ?_, ?_, fun y' hy' hne l' mm a' v' hc' =>
      h3 y' hy' hne l' mm a' v' (by rw [← hSS.capV hy']; exact hc'), fun e he h1' => h4 e (hge e he) h1'⟩
    · by_cases hp : p = ptr
      · rw [hp]; exact hz i
      · have hpl := C.rel.place p hpX'
        have e1 := eptA_val hpl.2 i
        have hi9 := i.isLt
        have hap := C.inTable hpX hpX' hp i
        rw [hw.mem_eq (b := eptA p i) (by unfold P1.Aligned; rw [e1]; omega) (fun hb => by
          have := hW _ hb; omega)]
        exact h1 i
    · by_cases hp : p = ptr
      · rw [hp]; exact hk'
      · rw [hxk p hpX' hp]; exact h2
  · -- `EptNamed` after: paths after are paths before
    have hobj : ∀ r l es, σ'.kheap r = some (.archObj (.ept l es)) →
        σ.kheap r = some (.archObj (.ept l es)) ∨ es = fun _ => 0 := by
      intro r l es hk
      by_cases hr : r = ptr.bv
      · subst hr; rw [hk'] at hk; cases hk; exact Or.inr rfl
      · exact Or.inl (by rw [← hoth r hr]; exact hk)
    exact C.named.keep (GPath.mono' (fun hi lo e h _ => Or.inl (hpa hi lo e h)) hobj)
      (C.named.inj.mono hat fun hi lo e h _ => hpa hi lo e h)
      (fun y p lv a v hy hc _ => ⟨y, hy, by rw [hSS.capV hy]; exact hc⟩)
      (fun y p lv mm a v hy hc => Or.inl ⟨y, hy, by rw [← hSS.capV hy]; exact hc⟩)

set_option maxHeartbeats 4000000 in
/-- **`EptCore` across the rewrite of the unique cap to a zero, unreachable table into the unmapped cap** (module
docstring). -/
theorem EptCore.unmapSlot (C : EptCore (L := L) X XL th s σ) {s' : S} {σ' : Fl4Spec.State Unit} {W : U64 → Prop}
    (hw : P1.WritesIn st s s' W) (hW : ∀ b, W b → ∀ u ∈ X, b.val < u.val ∨ u.val + 4096 ≤ b.val)
    {dest ptr lv a0 v0 : U64} {mm0 : Bool} (hd : IsSlot th dest)
    (hdc : capV (L.mem s) dest = .Ept ptr lv mm0 a0 v0) (hlv : lv.val ≠ 0)
    (hz : ∀ i : BitVec 9, L.mem s (eptA ptr i) = 0#u64)
    (hkz : σ.kheap ptr.bv = some (.archObj (.ept (XL ptr) fun _ => 0)))
    (huq : ∀ y, IsSlot th y → y ≠ dest → ∀ l (mm : Bool) a v, capV (L.mem s) y ≠ .Ept ptr l mm a v)
    (hun : ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ hi lo g l ptr.bv)
    (hcap' : capV (L.mem s') dest = .Ept ptr lv false 0#u64 0#u64)
    (hcp : ∀ y, IsSlot th y → y ≠ dest → capV (L.mem s') y = capV (L.mem s) y)
    (hcn : Ipc.CnK σ σ') : EptCore (L := L) X XL th s' σ' := by
  have hpX : ptr ∈ X := by have h := C.exte.cap dest hd; rw [hdc] at h; exact h
  have hXp : XL ptr = lv.val := (C.capL dest hd ptr lv a0 v0 mm0 hdc).symm
  have hmem : ∀ u ∈ X, ∀ i : BitVec 9, L.mem s' (eptA u i) = L.mem s (eptA u i) := by
    intro u hu i
    have hpl := C.rel.place u hu
    have e1 := eptA_val hpl.2 i
    have hi9 := i.isLt
    exact hw.mem_eq (b := eptA u i) (by unfold P1.Aligned; rw [e1]; omega)
      (fun hb => by rcases hW _ hb u hu with h | h <;> omega)
  have hun' : ∀ hi lo g l, g.toNat < 2 ^ 47 → l ≠ 0 → ¬ GPath σ' hi lo g l ptr.bv := fun hi lo g l hg hl hp =>
    hun hi lo g l hg hl (GPath.ofArch (cnK_asid hcn).symm (fun p ao h => (cnK_arch hcn).1 h) hp)
  have N := C.named.cnK hcn
  refine C.ofObj (fun t ht => ?_) hw.1 (fun y hy p l a v mm hc => ?_)
    ⟨fun y hy => ?_, ⟨fun y hy p l a v hc => ?_, fun y hy p sz r d a v hc => ?_⟩, fun y hy p l a v hc => ?_⟩
    (fun r l es hk => ⟨l, es, (cnK_arch hcn).1 hk⟩) (cnK_entry hcn) (cnK_size hcn) ?_ ?_ (EptWalk.cnK C.walk hcn) ?_
  · obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
    exact ⟨es, (cnK_arch hcn).2 hk, fun i hi => by rw [hmem t ht i]; exact hwd i hi⟩
  · by_cases e : y = dest
    · rw [e, hcap'] at hc
      obtain ⟨rfl, rfl, -, -, -⟩ := capability.Cap.Ept.inj hc
      exact ⟨dest, a0, v0, mm0, hd, hdc⟩
    · exact ⟨y, a, v, mm, hy, by rw [← hcp y hy e]; exact hc⟩
  · by_cases e : y = dest
    · rw [e, hcap']; exact hpX
    · rw [hcp y hy e]; exact C.exte.cap y hy
  · by_cases e : y = dest
    · rw [e, hcap'] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.vtop.1 y hy p l a v hc
  · by_cases e : y = dest
    · rw [e, hcap'] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.vtop.2 y hy p sz r d a v hc
  · by_cases e : y = dest
    · rw [e, hcap'] at hc; cases hc
    · rw [hcp y hy e] at hc; exact C.exte.anz y hy p l a v hc
  · -- `UnmappedEmpty` after
    intro y hy p l a v hc
    by_cases e : y = dest
    · rw [e, hcap'] at hc
      obtain ⟨e1, e2, -, e4, e5⟩ := capability.Cap.Ept.inj hc
      subst e1 e2 e4 e5
      refine ⟨fun i => by rw [hmem _ hpX i]; exact hz i, (cnK_arch hcn).2 hkz,
        fun y' hy' hne l' mm a' v' hc' => ?_, fun e he h1 hr => ?_⟩
      · rw [e] at hne
        rw [hcp y' hy' hne] at hc'
        exact huq y' hy' hne l' mm a' v' hc'
      · obtain ⟨u, hu, h2, h3⟩ := C.tag e (cnK_entry hcn e he) h1
        have hup : u = ptr := P1.eq_of_bv (h2.trans hr)
        rw [hup, hXp] at h3
        exact hlv h3
    · rw [hcp y hy e] at hc
      have hpp : p ≠ ptr := fun hp => huq y hy e l false a v (by rw [← hp]; exact hc)
      have hpX' : p ∈ X := by have h := C.exte.cap y hy; rw [hc] at h; exact h
      obtain ⟨h1, h2, h3, h4⟩ := C.ue y hy p l a v hc
      refine ⟨fun i => by rw [hmem p hpX' i]; exact h1 i, (cnK_arch hcn).2 h2, fun y' hy' hne l' mm a' v' hc' => ?_,
        fun e he h1' => h4 e (cnK_entry hcn e he) h1'⟩
      by_cases e' : y' = dest
      · rw [e', hcap'] at hc'
        exact hpp (capability.Cap.Ept.inj hc').1.symm
      · exact h3 y' hy' hne l' mm a' v' (by rw [← hcp y' hy' e']; exact hc')
  · -- `EptSlotOK`: `dest` held a cap of level `lv ≠ 0`, so it is no TCB's `SLOT_EPT`
    intro t' ht'
    by_cases e : cslotAddr (t'.bv, Fl4Spec.tcbCnodeIndex 5) = dest
    · exfalso
      rcases C.eslot t' ht' with h | ⟨p, a, v, h⟩ <;> rw [e, hdc] at h
      · cases h
      · exact hlv (by rw [(capability.Cap.Ept.inj h).2.1]; rfl)
    · exact Or.inr (Or.inr ⟨ht', hcp _ (isSlot_eptSlot ht') e⟩)
  · -- `EptNamed` after: `dest` names no reachable table
    refine ⟨fun hi lo gpa l u hg hp hl => ?_, fun hi lo gpa l u hg hp hl y p lv' mm a v hy hpu hc => ?_, N.inj⟩
    · obtain ⟨y, p, lv', a, v, hy, hpu, h1, h2, h3, h4, hc⟩ := N.ex hi lo gpa l u hg hp hl
      have hyd : y ≠ dest := fun e => by
        rw [e, hdc] at hc
        obtain ⟨rfl, -⟩ := capability.Cap.Ept.inj hc
        rw [← hpu] at hp
        exact hun' hi lo gpa l hg hl hp
      exact ⟨y, p, lv', a, v, hy, hpu, h1, h2, h3, h4, by rw [hcp y hy hyd]; exact hc⟩
    · by_cases e : y = dest
      · rw [e, hcap'] at hc
        obtain ⟨rfl, -⟩ := capability.Cap.Ept.inj hc
        rw [← hpu] at hp
        exact (hun' hi lo gpa l hg hl hp).elim
      · exact N.all hi lo gpa l u hg hp hl y p lv' mm a v hy hpu (by rw [← hcp y hy e]; exact hc)

end

end

end Fl4Proofs.P3
