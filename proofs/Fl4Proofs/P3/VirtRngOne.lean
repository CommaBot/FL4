/-
P3x for virtualization (line virt, gen 28, item 1): **`VcpuOneChain` along every `MdbStep`**, through an inductive
strengthening.

## Why `VcpuOneChain` alone is not kept by a generic step

`VcpuOneChain G mem` (P3/VirtVChunkIns: all `Vcpu v` caps lie in one ghost chain) is not preserved by
`MdbStep.recap` / `MdbStep.rename` as stated: `CapAlike c' c` (P3/MdbStep) fixes `c'`'s range, physicality,
untyped-ness, frame-ness and objects, but not its constructor, so `recap` may turn a cap of the same range that is
not a `Vcpu` cap (e.g. a zombie `Zombie v 10 n`: size `10 + 5 = 15` bits, object `v`) into `Vcpu v` in another
chain than the existing `Vcpu v` caps. FL4 never does this, but the step relation allows it. What every
constructor keeps is the same statement for **every exact range class**:

* `RngKey c`: `c` is physical, not untyped, not a frame (the caps `NoOverlap` lets share a range only exactly);
* **`RngOne mem G`**: two members whose caps are `RngKey` with the same base and top lie in a common chain.

`Vcpu v` caps are `RngKey` with range `[v, v + 2^15)`, so **`vcpuOneChain_of_rngOne`**: `RngOne` + the ghost's
members distinct (`MdbLinks.tree.nodup`) give `VcpuOneChain`; with `MdbInv`, `VcpuChunked`
(**`vcpuChunked_of_rngOne`**).

## `RngOne` along an `MdbStep` (**`mdbStep_rngOne`**)

By induction on the step, carrying `UtInv` (P3/UntypedUtInv; each case's `UtInv` lemma is MdbStepInv's):
* `keep`, `recap`, `setFi`: the ghost kept, each member's cap `NoA`-alike (`rngOne_congr`; `setFi`'s cap is untyped
  before and after, not `RngKey`);
* `insert` (`InsCtx`: the new cap and the source's new cap have the source's shape, `NoA.of_shape`), `nonphys`
  (the new cap is not physical), `frameAlias` (a frame), `pool` (an ASID pool cap over a childless untyped cap's
  whole region: an old physical cap meeting it is the untyped cap or an untyped ancestor, `UtInv.drange` +
  `MdbInv.anc_ut`): `rngOne_insG`;
* `remove` (`remG`: chains with the slot erased, members distinct): `rem_common`;
* `rename` (`renG`: chains mapped, caps `CapAlike`);
* `retype` (`RetypeDelta`): old chains inside new ones (`hch`), the new caps fresh — an old physical non-untyped
  cap misses the source's free part (`RetypeDelta.old_out`), the new caps lie in it (`new_rng`) and are pairwise
  disjoint (`cj_disj`). No hypothesis on the new caps' kind: the VCPU retype and every native retype alike.
* `trans`.

So `RngOne` is kept by every operation whose P3 post carries an `MdbStep`: the native retypes (UntypedSuccess
`retype_full`, UtTcbRetC, UntypedPml4, …), the VCPU retype (VirtRetFullV2), `cdt::insert` / move / swap /
`empty_slot` (MdbStepOps), the deletes and the revoke / CNode-zombie loops (DelDef, DelFull, CnodeRevoke: their
posts carry `MdbStep`), TCB cap installs (TcbCaps), the in-place cap rewrites that are `recap` / `setFi` steps.
Instances stated here: **`retype_full_rngOne`** (native non-TCB, non-PML4 retypes), **`set_cap_rngOne`** /
**`set_cap_vcpuOneChain`** (an in-place `Slot::set_cap` keeping the cap's range class resp. its `Vcpu`-ness — e.g.
`EnableIOPort`'s IO-port rewrite, which is not an `MdbStep` in mmuAD's posts).

No named premise. `RngOne` is a new **state** fact (the candidate [J] field replacing `VcpuOneChain`, which it
implies); it holds at boot iff every exact range class of non-untyped, non-frame physical caps lies in one chain
(each boot object has one cap). New file only; no existing statement changed.
-/
import Fl4Proofs.P3.MdbStepInv
import Fl4Proofs.P3.VirtVChunkIns
import Fl4Proofs.P3.UntypedSuccess
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtRngOne
open fl4_core Fl4Proofs.P3 Classical

noncomputable section

/-- A cap in an exact range class (module docstring): physical, not untyped, not a frame. -/
def RngKey (c : capability.Cap) : Prop := physF c = true ∧ isUt c = false ∧ isFrame c = false

/-- **Every exact range class of `RngKey` caps lies in one chain** (module docstring). -/
def RngOne (mem : U64 → U64) (G : MdbGhost) : Prop :=
  ∀ y ∈ G.chains.flatten, ∀ y' ∈ G.chains.flatten, RngKey (capV mem y) → RngKey (capV mem y') →
    baseF (capV mem y) = baseF (capV mem y') → topF (capV mem y) = topF (capV mem y') →
    ∃ ch ∈ G.chains, y ∈ ch ∧ y' ∈ ch

theorem noA_key {c' c : capability.Cap} (h : NoA c' c) (hk : RngKey c') : RngKey c :=
  ⟨by rw [← h.phys]; exact hk.1, by rw [← h.ut]; exact hk.2.1, by rw [← h.frame]; exact hk.2.2⟩

theorem key_vcpu (v : U64) : RngKey (.Vcpu v) := ⟨physF_vcpu v, rfl, rfl⟩

/-- **`RngOne` with the ghost kept and each member's cap alike** (when `RngKey` after). -/
theorem rngOne_congr {mem mem' : U64 → U64} {G : MdbGhost} (h : RngOne mem G)
    (hk : ∀ z ∈ G.chains.flatten, RngKey (capV mem' z) → NoA (capV mem' z) (capV mem z)) : RngOne mem' G := by
  intro y hy y' hy' k k' hb ht
  have a := hk y hy k
  have a' := hk y' hy' k'
  exact h y hy y' hy' (noA_key a k) (noA_key a' k') (by rw [← a.base, ← a'.base]; exact hb)
    (by rw [← a.top, ← a'.top]; exact ht)

theorem insAfter_keep {src dest z : U64} {d : List U64} (hz : z ∈ d) : z ∈ Mdb.insAfter src dest d := by
  by_cases hs : src ∈ d
  · exact (mem_insAfter hs).2 (Or.inr hz)
  · rw [Mdb.insAfter_of_not_mem hs]; exact hz

theorem insAfter_dest {src dest : U64} {d : List U64} (hs : src ∈ d) : dest ∈ Mdb.insAfter src dest d :=
  (mem_insAfter hs).2 (Or.inl rfl)

/-- **`RngOne` across `insG`**: old members' caps alike, the new cap alike the source's or alone in its class. -/
theorem rngOne_insG {mem mem' : U64 → U64} {G : MdbGhost} {src dest : U64} (b : Bool) (h : RngOne mem G)
    (hsrc : src ∈ G.chains.flatten)
    (hk : ∀ z ∈ G.chains.flatten, RngKey (capV mem' z) → NoA (capV mem' z) (capV mem z))
    (hdst : RngKey (capV mem' dest) → NoA (capV mem' dest) (capV mem src) ∨
      ∀ z ∈ G.chains.flatten, RngKey (capV mem z) → baseF (capV mem z) = baseF (capV mem' dest) →
        topF (capV mem z) = topF (capV mem' dest) → False) :
    RngOne mem' (insG G src dest b) := by
  have chn : ∀ d ∈ G.chains, Mdb.insAfter src dest d ∈ (insG G src dest b).chains :=
    fun d hd => List.mem_map.2 ⟨d, hd, rfl⟩
  intro y hy y' hy' k k' hb ht
  rcases (mem_flatten_ins hsrc).1 hy with e | hy0 <;> rcases (mem_flatten_ins hsrc).1 hy' with e' | hy0'
  · obtain ⟨d, hd, hsd⟩ := List.mem_flatten.1 hsrc
    rw [e, e']; exact ⟨_, chn d hd, insAfter_dest hsd, insAfter_dest hsd⟩
  · rw [e] at k hb ht ⊢
    have a1 := hk y' hy0' k'
    rcases hdst k with a | hno
    · obtain ⟨d, hd, hs, hy2⟩ := h src hsrc y' hy0' (noA_key a k) (noA_key a1 k')
        (by rw [← a.base, hb, a1.base]) (by rw [← a.top, ht, a1.top])
      exact ⟨_, chn d hd, insAfter_dest hs, insAfter_keep hy2⟩
    · exact (hno y' hy0' (noA_key a1 k') (by rw [← a1.base]; exact hb.symm)
        (by rw [← a1.top]; exact ht.symm)).elim
  · rw [e'] at k' hb ht ⊢
    have a1 := hk y hy0 k
    rcases hdst k' with a | hno
    · obtain ⟨d, hd, hy2, hs⟩ := h y hy0 src hsrc (noA_key a1 k) (noA_key a k')
        (by rw [← a1.base, hb, a.base]) (by rw [← a1.top, ht, a.top])
      exact ⟨_, chn d hd, insAfter_keep hy2, insAfter_dest hs⟩
    · exact (hno y hy0 (noA_key a1 k) (by rw [← a1.base]; exact hb) (by rw [← a1.top]; exact ht)).elim
  · have a := hk y hy0 k
    have a' := hk y' hy0' k'
    obtain ⟨d, hd, h1, h2⟩ := h y hy0 y' hy0' (noA_key a k) (noA_key a' k')
      (by rw [← a.base, ← a'.base]; exact hb) (by rw [← a.top, ← a'.top]; exact ht)
    exact ⟨_, chn d hd, insAfter_keep h1, insAfter_keep h2⟩

theorem rem_common {α : Type} [DecidableEq α] {x y y' : α} {chains : List (List α)} {d : List α}
    (hd : d ∈ chains) (hy : y ∈ d) (hy' : y' ∈ d) (hx : y ≠ x) (hx' : y' ≠ x) :
    ∃ ch ∈ Mdb.removeChains x chains, y ∈ ch ∧ y' ∈ ch := by
  have m1 : y ∈ d.erase x := (List.mem_erase_of_ne hx).2 hy
  have m2 : y' ∈ d.erase x := (List.mem_erase_of_ne hx').2 hy'
  refine ⟨d.erase x, ?_, m1, m2⟩
  unfold Mdb.removeChains
  refine List.mem_filter.2 ⟨List.mem_map.2 ⟨d, hd, rfl⟩, ?_⟩
  have hne : d.erase x ≠ [] := List.ne_nil_of_mem m1
  cases hc : d.erase x with
  | nil => exact absurd hc hne
  | cons a l => rfl

/-! ## Along a step -/

set_option maxHeartbeats 4000000 in
/-- **`RngOne` (and `UtInv`) along any `MdbStep`** (module docstring). -/
theorem mdbStep_rngOne {mem mem' : U64 → U64} {G G' : MdbGhost} (hS : MdbStep mem G mem' G') :
    UtInv mem G → RngOne mem G → UtInv mem' G' ∧ RngOne mem' G' := by
  induction hS with
  | keep hM hc hr =>
    intro hU hO
    exact ⟨hU.of_caps hM hc, rngOne_congr hO fun z hz _ => by rw [hc z hz]; exact NoA.refl _⟩
  | recap hM x0 ha _ hc hr =>
    intro hU hO
    have hk : ∀ z ∈ _, CapAlike _ _ := fun z hz => by
      by_cases e : z = x0
      · subst e; exact ha
      · rw [hc z hz e]; exact CapAlike.refl _
    exact ⟨hU.of_alike hM (fun z hz => (hk z hz).utEq), rngOne_congr hO fun z hz _ => (hk z hz).noA⟩
  | @setFi th m m' g hM hI x p sb fi f dev hx hcx hcx' hf hdir hc hr =>
    intro hU hO
    refine ⟨?_, rngOne_congr hO fun z hz kz => ?_⟩
    · rcases hdir with hle | hnd
      · exact hU.raise_fi hM hx hcx hcx' hf hle hc
      · exact hU.reset_fi hM hI hx hcx hnd hcx' hf hc
    · by_cases e : z = x
      · rw [e, hcx'] at kz; exact absurd kz.2.1 (by simp [isUt])
      · rw [hc z hz e]; exact NoA.refl _
  | @insert th m m' g src dest c c1 h hc1 hutc hok b hb _ =>
    intro hU hO
    refine ⟨h.utinv hU hc1 hutc b hb, rngOne_insG b hO h.hsrc (fun z hz _ => ?_) (fun _ => Or.inl ?_)⟩
    · have hzs : IsSlot th z := ((h.hM.members z).1 hz).1
      have hzd : z ≠ dest := fun e => h.hdest (e ▸ hz)
      rw [h.hcap z hzs, if_neg hzd]
      by_cases e : z = src
      · rw [if_pos e, e]; exact NoA.of_shape h.hsh1
      · rw [if_neg e]; exact NoA.refl _
    · rw [h.hcap dest h.hd, if_pos rfl]; exact NoA.of_shape h.hsh
  | nonphys hM b hsrc hdest hsp hcd hcp hrefs hc hr =>
    intro hU hO
    refine ⟨hU.nonphys hM b hsrc hdest hsp hcd hcp hc, rngOne_insG b hO hsrc
      (fun z hz _ => by rw [hc z hz]; exact NoA.refl _) (fun k => ?_)⟩
    rw [hcd] at k
    exact absurd (k.1.symm.trans hcp) (by decide)
  | remove hM x hc hr =>
    intro hU hO
    refine ⟨hU.remove hM hc, ?_⟩
    have nd := hM.tree.nodup
    intro y hy y' hy' k k' hb ht
    change y ∈ (Mdb.removeChains x _).flatten at hy
    change y' ∈ (Mdb.removeChains x _).flatten at hy'
    obtain ⟨hy0, hyx⟩ := (Mdb.mem_removeChains nd).1 hy
    obtain ⟨hy0', hyx'⟩ := (Mdb.mem_removeChains nd).1 hy'
    rw [hc y hy0 hyx] at k hb ht
    rw [hc y' hy0' hyx'] at k' hb ht
    obtain ⟨d, hd, h1, h2⟩ := hO y hy0 y' hy0' k k' hb ht
    exact rem_common hd h1 h2 hyx hyx'
  | rename hM e ha _ =>
    intro hU hO
    refine ⟨hU.rename hM e (fun z hz => (ha z hz).1.utEq), ?_⟩
    intro y hy y' hy' k k' hb ht
    change y ∈ (List.map (List.map e) _).flatten at hy
    change y' ∈ (List.map (List.map e) _).flatten at hy'
    obtain ⟨c1, hc1, hyc⟩ := List.mem_flatten.1 hy
    obtain ⟨d1, hd1, rfl⟩ := List.mem_map.1 hc1
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hyc
    obtain ⟨c2, hc2, hyc'⟩ := List.mem_flatten.1 hy'
    obtain ⟨d2, hd2, rfl⟩ := List.mem_map.1 hc2
    obtain ⟨z', hz', rfl⟩ := List.mem_map.1 hyc'
    have hz0 := List.mem_flatten.2 ⟨d1, hd1, hz⟩
    have hz0' := List.mem_flatten.2 ⟨d2, hd2, hz'⟩
    have a := (ha z hz0).1.noA
    have a' := (ha z' hz0').1.noA
    obtain ⟨d, hd, h1, h2⟩ := hO z hz0 z' hz0' (noA_key a k) (noA_key a' k')
      (by rw [← a.base, ← a'.base]; exact hb) (by rw [← a.top, ← a'.top]; exact ht)
    exact ⟨d.map e, List.mem_map.2 ⟨d, hd, rfl⟩, List.mem_map.2 ⟨z, h1, rfl⟩, List.mem_map.2 ⟨z', h2, rfl⟩⟩
  | @frameAlias th m m' g hM hI src dest b hsrc hdest ptr rt fa fv q0 vm mm hsC hcd hq1 hq2 hcin hcr halg hc hrd hr _ _ =>
    intro hU hO
    have hsF : isFrame (capV m src) = true := by rw [hsC]; rfl
    have hcF : isFrame (capV m' dest) = true := by rw [hcd]; rfl
    refine ⟨Vs.utinv_alias hM hI hU b hsrc hsF hdest hcF hcin hcr rfl hc, rngOne_insG b hO hsrc
      (fun z hz _ => by rw [hc z hz]; exact NoA.refl _) (fun k => ?_)⟩
    exact absurd (k.2.2.symm.trans hcF) (by decide)
  | @pool th m m' g hM hI x val p sb f q bb d hx hcx hf hnd hval hcf hbA htA hc hr _ =>
    intro hU hO
    refine ⟨Vs.utinv_pool hM hU hx hcx hf hnd hval hcf hbA htA hc, rngOne_insG true hO hx
      (fun z hz _ => by rw [hc z hz]; exact NoA.refl _) (fun _ => Or.inr ?_)⟩
    intro z hz kz hbz htz
    have hux : isUt (capV m x) = true := by rw [hcx]; rfl
    by_cases hzx : z = x
    · rw [hzx] at kz; exact absurd (kz.2.1.symm.trans hux) (by decide)
    have hrx := hU.reg x hx (by rw [hcx]; exact physF_ut _ _ _ _)
    rw [hcf, hbA] at hbz
    rw [hcf, htA] at htz
    have hd : ¬ Disj (capV m z) (capV m x) := by
      unfold Disj; rw [hbz, htz]; omega
    rcases hU.drange x hx p sb f d hcx z hz hzx kz.1 hd with e | e
    · exact hnd z e
    · exact absurd (kz.2.1.symm.trans (hI.anc_ut e hux)) (by decide)
  | @retype th m0 m1 mf G0 Gf src p sb fi nfi dev A k w dslot cj h hI hch hr hvc =>
    intro hU hO
    refine ⟨h.utinv hU, ?_⟩
    have old : ∀ z ∈ G0.chains.flatten, RngKey (capV mf z) → capV mf z = capV m0 z := by
      intro z hz kz
      rw [h.F2b z hz] at kz ⊢
      by_cases e : z = src
      · rw [e, h.hcs1] at kz; exact absurd kz.2.1 (by simp [isUt])
      · exact h.hc1 z hz e
    intro y hy y' hy' ky ky' hb ht
    rcases h.F1 y hy with hy0 | ⟨j, hj, rfl⟩ <;> rcases h.F1 y' hy' with hy0' | ⟨l, hl, rfl⟩
    · have e1 := old y hy0 ky
      have e2 := old y' hy0' ky'
      rw [e1] at ky hb ht
      rw [e2] at ky' hb ht
      obtain ⟨d, hd, h1, h2⟩ := hO y hy0 y' hy0' ky ky' hb ht
      obtain ⟨ch', hch', hsub⟩ := hch d hd
      exact ⟨ch', hch', hsub y h1, hsub y' h2⟩
    · have e1 := old y hy0 ky
      rw [e1] at ky hb ht
      rw [h.F2a l hl] at ky' hb ht
      have hd := h.old_out hU hy0 ky.1 ky.2.1
      obtain ⟨n1, n2, n3⟩ := h.new_rng hU hl
      unfold DisjR at hd
      omega
    · have e2 := old y' hy0' ky'
      rw [e2] at ky' hb ht
      rw [h.F2a j hj] at ky hb ht
      have hd := h.old_out hU hy0' ky'.1 ky'.2.1
      obtain ⟨n1, n2, n3⟩ := h.new_rng hU hj
      unfold DisjR at hd
      omega
    · rw [h.F2a j hj] at ky hb ht
      rw [h.F2a l hl] at ky' hb ht
      by_cases hjl : j = l
      · subst hjl
        obtain ⟨c0, hc0, hyc⟩ := List.mem_flatten.1 hy
        exact ⟨c0, hc0, hyc, hyc⟩
      · obtain ⟨n1, n2, n3⟩ := h.new_rng hU hj
        rcases h.cj_disj hU hj hl hjl with g | g <;> omega
  | trans _ _ ih1 ih2 =>
    intro hU hO
    obtain ⟨a, b⟩ := ih1 hU hO
    exact ih2 a b

/-! ## `VcpuOneChain` and `VcpuChunked` from `RngOne` -/

/-- **`VcpuOneChain` from `RngOne`** (the ghost's members distinct). -/
theorem vcpuOneChain_of_rngOne {mem : U64 → U64} {G : MdbGhost} (hnd : G.chains.flatten.Nodup)
    (h : RngOne mem G) : VirtVChunkIns.VcpuOneChain G mem := by
  intro v ch hch ch' hch' y hy y' hy' h1 h2
  have hy0 := List.mem_flatten.2 ⟨ch, hch, hy⟩
  have hy0' := List.mem_flatten.2 ⟨ch', hch', hy'⟩
  obtain ⟨d, hd, a, b⟩ := h y hy0 y' hy0' (by rw [h1]; exact key_vcpu v) (by rw [h2]; exact key_vcpu v)
    (by rw [h1, h2]) (by rw [h1, h2])
  exact (VirtVChunkIns.vchain_eq hnd hch hd hy a).trans (VirtVChunkIns.vchain_eq hnd hd hch' b hy')

/-- **`VcpuChunked` from `MdbInv` and `RngOne`.** -/
theorem vcpuChunked_of_rngOne {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hI : MdbInv mem G) (h : RngOne mem G) : VirtVChunk.VcpuChunked G mem :=
  VirtVChunkIns.vcpuChunked_of hI (vcpuOneChain_of_rngOne hM.tree.nodup h)

/-- **A step keeps `RngOne` and gives `VcpuOneChain` after.** -/
theorem rngOne_step {th' : TypedHeap} {mem mem' : U64 → U64} {G G' : MdbGhost} (hS : MdbStep mem G mem' G')
    (hU : UtInv mem G) (hO : RngOne mem G) (hM' : MdbLinks th' mem' G') :
    RngOne mem' G' ∧ VirtVChunkIns.VcpuOneChain G' mem' :=
  ⟨(mdbStep_rngOne hS hU hO).2, vcpuOneChain_of_rngOne hM'.tree.nodup (mdbStep_rngOne hS hU hO).2⟩

/-- **`VcpuOneChain` with the ghost kept and each member's `Vcpu`-ness kept.** -/
theorem vcpuOneChain_congr {mem mem' : U64 → U64} {G : MdbGhost} (h : VirtVChunkIns.VcpuOneChain G mem)
    (hk : ∀ z ∈ G.chains.flatten, ∀ v, capV mem' z = .Vcpu v → capV mem z = .Vcpu v) :
    VirtVChunkIns.VcpuOneChain G mem' := by
  intro v ch hch ch' hch' y hy y' hy' h1 h2
  exact h v ch hch ch' hch' y hy y' hy' (hk y (List.mem_flatten.2 ⟨ch, hch, hy⟩) v h1)
    (hk y' (List.mem_flatten.2 ⟨ch', hch', hy'⟩) v h2)

/-! ## Instances -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **An in-place `Slot::set_cap` keeping the cap's range class keeps `RngOne`** (ghost unchanged). -/
theorem set_cap_rngOne {th : TypedHeap} (hP : Placed th) (s : S) {a : U64} (ha : IsSlot th a) (c : capability.Cap)
    (he : EncWf c) {G : MdbGhost} (hM : MdbLinks th (L.mem s) G) (hO : RngOne (L.mem s) G)
    (hc : RngKey c → NoA c (capV (L.mem s) a)) :
    obj.Slot.set_cap st a s c ⦃ s' => RngOne (L.mem s') G ⦄ := by
  refine WP.spec_mono (set_cap_upd (L := L) hP s ha c he) fun s' hs => ?_
  obtain ⟨h1, h2, -, -⟩ := hs
  refine rngOne_congr hO fun z hz kz => ?_
  by_cases e : z = a
  · rw [e, h1] at kz ⊢; exact hc kz
  · rw [h2 z ((hM.members z).1 hz).1 e]; exact NoA.refl _

/-- **An in-place `Slot::set_cap` keeping the cap's `Vcpu`-ness keeps `VcpuOneChain`** (ghost unchanged). -/
theorem set_cap_vcpuOneChain {th : TypedHeap} (hP : Placed th) (s : S) {a : U64} (ha : IsSlot th a)
    (c : capability.Cap) (he : EncWf c) {G : MdbGhost} (hM : MdbLinks th (L.mem s) G)
    (hO : VirtVChunkIns.VcpuOneChain G (L.mem s)) (hc : ∀ v, c = .Vcpu v → capV (L.mem s) a = .Vcpu v) :
    obj.Slot.set_cap st a s c ⦃ s' => VirtVChunkIns.VcpuOneChain G (L.mem s') ⦄ := by
  refine WP.spec_mono (set_cap_upd (L := L) hP s ha c he) fun s' hs => ?_
  obtain ⟨h1, h2, -, -⟩ := hs
  refine vcpuOneChain_congr hO fun z hz v hv => ?_
  by_cases e : z = a
  · rw [e, h1] at hv; rw [e]; exact hc v hv
  · rw [h2 z ((hM.members z).1 hz).1 e] at hv; exact hv

/-- **The native retype keeps `RngOne` and gives `VcpuOneChain`** (UntypedSuccess's `retype_full`: every object
type but TCBs and PML4s; its post's `MdbStep` through `rngOne_step`). -/
theorem retype_full_rngOne {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hcan : CanonR p.val (p.val + 2 ^ sb.val)) (hhigh : dev = false → 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (nt us : U64) (t : Fl4Spec.ApiObjectType) (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz47 : zOf nt.val us.val ≤ 47)
    (hsc : nt.val = 5 → 7 ≤ us.val) (hct0 : nt.val = 4 → us.val ≠ 0)
    {dest : U64} {r : Nat} (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (off win : U64) (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : dev = false → ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hdevT : dev = true → nt.val ≠ 4)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (hb : bitsApi t us.val = zOf nt.val us.val)
    (hO : RngOne (L.mem s) G) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      res.1 = .Ok () ∧ ∃ G' th', MdbLinks th' (L.mem res.2.1) G' ∧ RngOne (L.mem res.2.1) G' ∧
        VirtVChunkIns.VcpuOneChain G' (L.mem res.2.1) ⦄ := by
  refine WP.spec_mono (retype_full arI ar th s σ G hR hV hP hM hC hI hU horig hpp hidx hcap hpal hpfit hfi hcan
    hhigh nt us t ht hn hus hz47 hsc hct0 hdest hr off win hwin hw1 hmem hempty hfree hzero hdevT bitsApi hb) ?_
  rintro res ⟨h1, -, σ', G', th', -, -, -, -, hM', -, -, ⟨-, hS⟩, -⟩
  exact ⟨h1, G', th', hM', rngOne_step hS hU hO hM'⟩

end

end
end Fl4Proofs.P3.VirtRngOne
