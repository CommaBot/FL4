/-
# P2 (line pte, gen 1): **rule 8 of the ownership map**, the leaf page-table entries

`OwnMap.own` (rules 1–6) and `OwnMapV.ownV` (rule 7, VCPUs) give every page-table word to the gate ("everything
else", region `.none`). A local `X86PageMap`, and a local `CNodeDelete` of a mapped frame, write one leaf PTE
beside the gate, so `PathObl.write_own` cannot hold for them under `ownV`. This module adds, **beside** `ownV`
(which stays as it is, with all its users):

* `KLayoutP`: `KLayoutV` plus the set `ptes` of leaf page-table entries (8-byte words of the small-page tables
  below `USER_TOP` that a local path may lock; a ghost the serial entries alone change, as `slots`);
* **rule 8**: a word `e ∈ K.ptes` is **`lock e`'s** (`ownP_pte`), whatever memory holds (the owner reads no word);
* `ownP K m b`: `lock b` on a PTE word, `ownV K m b` elsewhere (`ownP_off`); with `K.ptes = ∅` it **is** `ownV`
  (`ownP_empty`), so nothing changes for a layout without PTEs.

Why `lock e` (handoff `stpost.md`, generation 12, "PTE-lock investigation"): the PTE a local path writes is
protected by fl4-store's word lock on that PTE's own address:
* the plan: `crates/fl4-core/src/localinv.rs` `add_pte` (l. 88-91), Delete l. 225-235, PageMap l. 251-253;
* the lock: fl4-sync `local_invocation` (`crates/fl4-sync/src/lib.rs` l. 521-545) locks `(p.locks[i], 8 if i ==
  p.pte else 32)` through `with_locks` → fl4-store `lock::try_lock_object` (a hash collision only declines);
* the gate: plan, locks and run happen after `try_enter_local`; the gate holder closes and drains every active
  core (`lib.rs` l. 150-183), which `Serial`'s gate models;
* upper page-table levels and the ASID table change only under the gate (`localinv.rs` l. 19-25, 147-149): they
  stay `.none` / gate-owned here, so a local path may read them (`GateOnly`) and never write them.

Carry-over facts, as `OwnMapVcpu`'s for rule 7:
* `ownP_congr` / `ownP_upd_nondec`: owners read only `own`'s `DecW` words (a PTE decides nothing: `pte_nondec`);
* **`moveHeldP`**: `Serial.MoveHeld (ownP K)` (from `OwnMapV.moveHeldV` off the PTEs);
* **`ownDepP`**: `E2E.OwnDep (ownP K) (· ∈ K.user)`;
* per-write checks: **`stepOKP_of_stepOKV`** (every `StepOK` for `ownV` is one for `ownP`: rule 8's owners depend
  on no memory word), **`stepOKP_pte`** (a write of PTE words moves no owner and has a free class),
  `wpermP_of_V` (every `ownV` write permission is an `ownP` one: a held `ownV` word is not a PTE),
  `rpermP_of_V` (off the PTEs), **`wpermP_pte`** / `rpermP_pte` (holding `lock e` permits `e`).

Layout facts `RegionOKP` / `UserOKP` [J] (from P1's typed heap and the page-table walk, `HeapOK`: page-table
pages are untyped `.none` memory, disjoint from every object, slot, node and VCPU; entries are 8-byte aligned and
not user memory). With `K.ptes = ∅` both are `RegionOKV` / `UserOKV` (`regionOKP_empty`, `userOKP_empty`).

Nothing here edits `OwnMap.own`, `OwnMapV.ownV`, `E2E.Paths` / `Exec` or `E2EV.PathsV` / `ExecV`.
-/
import Fl4Proofs.P2.OwnMapVcpu
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.OwnMapP
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO MoveHeld)
open Fl4Proofs.P2.OwnMap (KLayout InW fld own region RegionOK DecW)
open Fl4Proofs.P2.OwnMapV (KLayoutV InVcpu ownV RegionOKV UserOKV)

noncomputable section
open Classical

/-- `KLayoutV` with the leaf page-table entries a local path may lock. -/
structure KLayoutP extends KLayoutV where
  /-- The leaf page-table entries (8-byte words, addressed by their own address). -/
  ptes : Set U64

/-- A layout without PTE words: rule 8 is void there (`ownP_empty`). -/
def KLayoutV.noPte (K : KLayoutV) : KLayoutP := { toKLayoutV := K, ptes := ∅ }

/-- **Rule 8**: a leaf PTE is `lock e`'s; `ownV` elsewhere. Memory-independent on the PTEs. -/
def ownP (K : KLayoutP) (m : U64 → U64) (b : U64) : Owner U64 U64 :=
  if b ∈ K.ptes then .lock b else ownV K.toKLayoutV m b

/-- **Layout facts for rule 8** [J] (module docstring): PTE words lie in `own`'s `.none` region and in no VCPU. -/
structure RegionOKP (K : KLayoutP) : Prop where
  base : RegionOKV K.toKLayoutV
  none : ∀ e ∈ K.ptes, region K.toKLayout e = .none
  novcpu : ∀ e ∈ K.ptes, ¬ ∃ v, InVcpu K.toKLayoutV v e

/-- **User memory and alignment** [J]: as `UserOKV`, and PTE words are aligned kernel words. -/
structure UserOKP (K : KLayoutP) : Prop where
  base : UserOKV K.toKLayoutV
  kern : ∀ e ∈ K.ptes, Aligned e ∧ e ∉ K.user

variable {K : KLayoutP}

theorem ownP_pte {m : U64 → U64} {b : U64} (h : b ∈ K.ptes) : ownP K m b = .lock b := by
  unfold ownP; rw [if_pos h]

theorem ownP_off {m : U64 → U64} {b : U64} (h : b ∉ K.ptes) : ownP K m b = ownV K.toKLayoutV m b := by
  unfold ownP; rw [if_neg h]

/-- **With no PTE words, `ownP` is `ownV`.** -/
theorem ownP_empty (h : K.ptes = ∅) : ownP K = ownV K.toKLayoutV := by
  funext m b
  exact ownP_off (by rw [h]; exact Set.notMem_empty b)

theorem ownP_noPte (K : KLayoutV) : ownP (KLayoutV.noPte K) = ownV K := ownP_empty rfl

theorem regionOKP_empty (h : K.ptes = ∅) (hK : RegionOKV K.toKLayoutV) : RegionOKP K :=
  ⟨hK, fun e he => by rw [h] at he; exact absurd he (Set.notMem_empty e),
    fun e he => by rw [h] at he; exact absurd he (Set.notMem_empty e)⟩

theorem userOKP_empty (h : K.ptes = ∅) (hU : UserOKV K.toKLayoutV) : UserOKP K :=
  ⟨hU, fun e he => by rw [h] at he; exact absurd he (Set.notMem_empty e)⟩

/-- Under `ownV` a PTE word is the gate's ("everything else"). -/
theorem ownV_pte (hK : RegionOKP K) {m : U64 → U64} {e : U64} (h : e ∈ K.ptes) :
    ownV K.toKLayoutV m e = .gate := by
  rw [OwnMapV.ownV_off (hK.novcpu e h)]
  unfold own; rw [hK.none e h]

/-- A PTE word decides no `own` owner. -/
theorem pte_nondec (hK : RegionOKP K) {e : U64} (h : e ∈ K.ptes) : ¬ DecW K.toKLayout e :=
  OwnMap.nondec_of_region hK.base.base (Or.inr (Or.inr (Or.inr (Or.inl (hK.none e h)))))

/-- `ownP` reads only `own`'s deciding words (`DecW`). -/
theorem ownP_congr (hK : RegionOKP K) {m m' : U64 → U64} (h : ∀ d, DecW K.toKLayout d → m d = m' d) :
    ownP K m = ownP K m' := by
  funext b
  by_cases hb : b ∈ K.ptes
  · rw [ownP_pte hb, ownP_pte hb]
  · rw [ownP_off hb, ownP_off hb, OwnMapV.ownV_congr hK.base h]

theorem ownP_upd_nondec (hK : RegionOKP K) {a : U64} (ha : ¬ DecW K.toKLayout a) (m : U64 → U64) (v : U64) :
    ownP K (Function.update m a v) = ownP K m :=
  ownP_congr hK fun d hd => Function.update_of_ne (fun e : d = a => ha (e ▸ hd)) _ _

/-! ## `MoveHeld` and `OwnDep` -/

/-- **`MoveHeld` for `ownP`.** A PTE word's owner never moves and a PTE decides nothing; off the PTEs
`OwnMapV.moveHeldV` applies (with the PTE words of `m'` put back to `m`'s, which no `ownV` owner reads). -/
theorem moveHeldP (hK : RegionOKP K) : MoveHeld (ownP K) := by
  intro c hs m m' a v x ha hag hx
  by_cases hxp : x ∈ K.ptes
  · exact absurd (by rw [ownP_pte hxp, ownP_pte hxp]) hx
  · simp only [ownP_off hxp] at hx ⊢
    by_cases hap : a ∈ K.ptes
    · exfalso
      exact hx (by rw [OwnMapV.ownV_upd_nondec hK.base (pte_nondec hK hap)])
    · rw [ownP_off hap] at ha
      let m'' : U64 → U64 := fun y => if y ∈ K.ptes then m y else m' y
      have hag'' : ∀ y, PO c hs (ownV K.toKLayoutV m y) → m'' y = m y := by
        intro y hy
        by_cases hy' : y ∈ K.ptes
        · simp only [m'', if_pos hy']
        · simp only [m'', if_neg hy']; exact hag y (by rw [ownP_off hy']; exact hy)
      obtain ⟨h1, h2⟩ := OwnMapV.moveHeldV hK.base c hs m m'' a v x ha hag'' hx
      have nd : ∀ d, DecW K.toKLayout d → d ∉ K.ptes := fun d hd hp => pte_nondec hK hp hd
      have e1 : ownV K.toKLayoutV m'' = ownV K.toKLayoutV m' := OwnMapV.ownV_congr hK.base fun d hd => by
        simp only [m'', if_neg (nd d hd)]
      have e2 : ownV K.toKLayoutV (Function.update m'' a v) = ownV K.toKLayoutV (Function.update m' a v) :=
        OwnMapV.ownV_congr hK.base fun d hd => by
          by_cases hda : d = a
          · subst hda; simp only [Function.update_self]
          · simp only [Function.update_of_ne hda, m'', if_neg (nd d hd)]
      rw [← e1, ← e2]; exact ⟨h1, h2⟩

/-- **`OwnDep` for `ownP`**: owners depend on aligned kernel words only. -/
theorem ownDepP (hK : RegionOKP K) (hU : UserOKP K) : E2E.OwnDep (ownP K) (· ∈ K.user) := by
  intro m m' h
  exact ownP_congr hK fun d hd => h d (OwnMap.decW_ok hU.base.base hd).1 (OwnMap.decW_ok hU.base.base hd).2

/-! ## Classes and the per-write check -/

/-- A PTE word's value class is untracked. -/
theorem ko_pte (hK : RegionOKP K) {e : U64} (h : e ∈ K.ptes) (m0 : U64 → U64) :
    OwnMap.ko K.toKLayout m0 e = .free :=
  OwnMap.ko_free_of_nondec hK.base.base (pte_nondec hK h) m0

/-- **The per-write check of a write to PTE words**: changing only such words moves no owner and keeps every
tracked class. -/
theorem stepOKP_pte (hK : RegionOKP K) {m m' : U64 → U64} (h : ∀ y, m' y ≠ m y → y ∈ K.ptes)
    (m0 : U64 → U64) (User : U64 → Prop) (c : U64) (lk : U64 → Prop) :
    PathObl.StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) User c lk m m' := by
  have e : ownP K m' = ownP K m := ownP_congr hK fun d hd => by
    by_contra hne
    exact pte_nondec hK (h d hne) hd
  refine ⟨fun x hx => absurd (by rw [e]) hx, fun x hx _ => ?_⟩
  exact Or.inr (Or.inr (ko_pte hK (h x hx) m0))

/-- **`ownV`'s per-write check is `ownP`'s**, for every step: a PTE word's owner never moves, and off the PTEs the
two maps agree. -/
theorem stepOKP_of_stepOKV {m m' : U64 → U64}
    {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop} {c : U64} {lk : U64 → Prop}
    (hs : PathObl.StepOK (ownV K.toKLayoutV) cls ko User c lk m m') :
    PathObl.StepOK (ownP K) cls ko User c lk m m' := by
  refine ⟨fun x hx => ?_, hs.2⟩
  by_cases hxp : x ∈ K.ptes
  · exact absurd (by rw [ownP_pte hxp, ownP_pte hxp]) hx
  · simp only [ownP_off hxp] at hx ⊢
    exact hs.1 x hx

theorem rpermP_of_V {m : U64 → U64} {x c : U64} {lk : U64 → Prop} (hx : x ∉ K.ptes)
    (h : PathObl.RPerm (ownV K.toKLayoutV) c lk m x) : PathObl.RPerm (ownP K) c lk m x := by
  unfold PathObl.RPerm PathObl.GateOnly at *; rw [ownP_off hx]; exact h

/-- **Every `ownV` write permission is an `ownP` one**: a word a path may write under `ownV` is held, so not the
gate's, so not a PTE word. -/
theorem wpermP_of_V (hK : RegionOKP K) {m : U64 → U64} {x c : U64} {lk : U64 → Prop}
    (h : PathObl.WPerm (ownV K.toKLayoutV) c lk m x) : PathObl.WPerm (ownP K) c lk m x := by
  by_cases hx : x ∈ K.ptes
  · unfold PathObl.WPerm at h; rw [ownV_pte hK hx] at h; exact absurd h id
  · unfold PathObl.WPerm at *; rw [ownP_off hx]; exact h

/-- **A path holding `lock e` may write (and read) the PTE `e`.** -/
theorem wpermP_pte {m : U64 → U64} {e c : U64} {lk : U64 → Prop} (h : e ∈ K.ptes) (hl : lk e) :
    PathObl.WPerm (ownP K) c lk m e := by
  unfold PathObl.WPerm; rw [ownP_pte h]; exact hl

theorem rpermP_pte {m : U64 → U64} {e c : U64} {lk : U64 → Prop} (h : e ∈ K.ptes) (hl : lk e) :
    PathObl.RPerm (ownP K) c lk m e :=
  Or.inl (wpermP_pte h hl)

/-- Without `lock e`, a PTE word is neither held nor the gate's: no local path may read it. -/
theorem not_rpermP_pte {m : U64 → U64} {e c : U64} {lk : U64 → Prop} (h : e ∈ K.ptes) (hl : ¬ lk e) :
    ¬ PathObl.RPerm (ownP K) c lk m e := by
  unfold PathObl.RPerm PathObl.GateOnly
  rw [ownP_pte h]
  rintro (h1 | h1)
  · exact hl h1
  · cases h1

/-- A VCPU word is no PTE word, so `ownP` is `ownV` there. -/
theorem ownP_vcpu (hK : RegionOKP K) {m : U64 → U64} {v b : U64} (h : InVcpu K.toKLayoutV v b) :
    ownP K m b = ownV K.toKLayoutV m b :=
  ownP_off fun hp => hK.novcpu b hp ⟨v, h⟩

end

end Fl4Proofs.P2.OwnMapP
