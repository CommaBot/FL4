/-
P3x for virtualization (line virt, gen 27, item 2): **`VcpuChunked` across the insertions** (`cdt::insert`,
the retype's `insert_new_cap`), and its split into a part every P3 bundle already carries and a small new one.

## `VcpuChunked` = `MdbInv.chunk` + `VcpuOneChain`

`VcpuChunked G mem` (P3/VirtVChunk) has two halves: (1) inside one ghost chain the `Vcpu v` positions form an interval;
(2) all `Vcpu v` caps lie in one chain. Half (1) is **not new**: `MdbInv.chunk` (P3/MdbInv: every chain is
`ChunkL (srF mem)`, l4v `mdb_chunked` along a chain) gives it, because FL4's `same_region_as` on a `Vcpu v` cap is
"the other cap is `Vcpu v`" (objects.rs l. 123; extracted arm `Vcpu p => if p = ptr then ok true else ok false`, all
other arms `ok false`): `srB_vcpu_left`, VirtVFinal's `srB_vcpu_self`, `ca_sub`, `chunkL_sub3`,
**`vcpuChunk1_of_mdbInv`**. So **`vcpuChunked_of`**: `MdbInv mem G ∧ VcpuOneChain G mem → VcpuChunked G mem`, and
`vcpuChunked_iff` (given `MdbInv`). Every P3 step lemma already keeps `MdbInv`; the only new carried fact is
**`VcpuOneChain`** (half (2)).

## `VcpuOneChain` across the insertions

* `vchain_eq` (two chains sharing a member are equal: `G.chains.flatten` nodup), `mem_insAfter`.
* **`vcpuOneChain_insG`** (ghost level, `insG G src dest b`, InsertRefine): the new slot `dest` was in no chain, the
  members' caps are kept, and a `Vcpu v` cap at `dest` comes from a `Vcpu v` source **or** names a VCPU no member's
  cap names (a fresh object).
* **`insert_vcpuOneChain`** (FL4 level, `cdt::insert c src dest`, cdt.rs l. 28-46, through TcbCaps'
  `insert_caps_nofull`): from `VcpuOneChain G` before, `VcpuOneChain (insG G src dest b)` after for any `b`, when
  `c = Vcpu v` only for a `Vcpu v` source (FL4's copy / mint / move derive the cap from the source,
  `objects::derive_cap` keeps the object of a `Vcpu` cap; `update_cap_data` keeps it, objects.rs). Composes with
  InsertRefine's `insert_refines'` (`G' = insG …`) by `WP.spec_and`.
* **`vcpuOneChain_retExp`** (the retype's insertions, all at once): from `RetExp` (UntypedExp: old non-untyped caps
  kept, untyped caps stay untyped, new members are the window slots with the caps `vcj A j`), `ChSub G G'`
  (P3/VirtRetFullV2: each old chain inside one new chain — the loop invariant's chain clause), and freshness (no old
  member names a new VCPU): `VcpuOneChain G m → VcpuOneChain G' m'`. **`fresh_of_jextV2`**: freshness from `JExtV2`
  (an old `Vcpu p` cap has `p ∈ V`) when no VCPU of `V` is a new object.

No named premise. New file only; no existing statement changed.
-/
import Fl4Proofs.P3.VirtVChunkKeep
import Fl4Proofs.P3.VirtRetFullV2
import Fl4Proofs.P3.TcbCaps
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtVChunkIns
open fl4_core Fl4Proofs.P3 Classical Fl4Proofs.P3.VirtVChunk Fl4Proofs.P3.VirtVChunkKeep Fl4Proofs.P3.VirtVFinal
open Fl4Proofs.P3.VirtRetFullV2 Fl4Proofs.P3.VirtRetypeLoop Fl4Proofs.P3.VirtLoopFrame

noncomputable section

/-! ## Half (1) from `MdbInv.chunk` -/

/-- `same_region_as (Vcpu v) c` only for `c = Vcpu v` (objects.rs l. 123). -/
theorem srB_vcpu_left {v : U64} {c : capability.Cap} (h : srB (.Vcpu v) c = true) : c = .Vcpu v := by
  have e := srB_eq (.Vcpu v) c
  rw [h] at e
  cases c <;> simp [objects.same_region_as] at e
  all_goals first | rw [UScalar.eq_of_val_eq e] | rw [e] | simp_all

section
variable {α : Type}

theorem ca_sub {R : α → α → Bool} {a : α} : ∀ {L : List α}, Mdb.CA R a L → ∀ {b c : α}, [b, c].Sublist L →
    R a c = true → R a b = true
  | [], _, b, c, hs, _ => absurd hs.length_le (by simp)
  | y :: L, h, b, c, hs, hc => by
    cases hs with
    | cons _ hs' => exact ca_sub h.2 hs' hc
    | cons_cons _ hs' =>
      cases hrb : R a y
      · have := h.1 hrb c (hs'.subset (List.mem_singleton_self c))
        rw [hc] at this; cases this
      · rfl

theorem chunkL_sub3 {R : α → α → Bool} : ∀ {ch : List α}, Mdb.ChunkL R ch → ∀ {a b c : α}, [a, b, c].Sublist ch →
    R a c = true → R a b = true
  | [], _, a, b, c, hs, _ => absurd hs.length_le (by simp)
  | x :: t, h, a, b, c, hs, hc => by
    cases hs with
    | cons _ hs' => exact chunkL_sub3 h.2 hs' hc
    | cons_cons _ hs' => exact ca_sub h.1 hs' hc

theorem vchain_eq_aux : ∀ {chains : List (List α)}, chains.Pairwise (fun a b => List.Disjoint a b) →
    ∀ {ch1 ch2 : List α}, ch1 ∈ chains → ch2 ∈ chains → ∀ {x : α}, x ∈ ch1 → x ∈ ch2 → ch1 = ch2
  | [], _, _, _, h1, _, _, _, _ => by simp at h1
  | c :: cs, hp, ch1, ch2, h1, h2, x, hx1, hx2 => by
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.1 h1 with e1 | h1' <;> rcases List.mem_cons.1 h2 with e2 | h2'
    · rw [e1, e2]
    · rw [e1] at hx1; exact (hp.1 ch2 h2' hx1 hx2).elim
    · rw [e2] at hx2; exact (hp.1 ch1 h1' hx2 hx1).elim
    · exact vchain_eq_aux hp.2 h1' h2' hx1 hx2

/-- Two chains sharing a member are equal (the ghost's members are distinct). -/
theorem vchain_eq {chains : List (List α)} (hnd : chains.flatten.Nodup) {ch1 ch2 : List α}
    (h1 : ch1 ∈ chains) (h2 : ch2 ∈ chains) {x : α} (hx1 : x ∈ ch1) (hx2 : x ∈ ch2) : ch1 = ch2 :=
  vchain_eq_aux (List.nodup_flatten.1 hnd).2 h1 h2 hx1 hx2

theorem mem_insAfter [DecidableEq α] {x y z : α} : ∀ {l : List α}, z ∈ Mdb.insAfter x y l →
    z ∈ l ∨ (z = y ∧ x ∈ l)
  | [], h => by simp [Mdb.insAfter] at h
  | a :: l, h => by
    unfold Mdb.insAfter at h
    by_cases ha : a = x
    · rw [if_pos ha] at h
      rcases List.mem_cons.1 h with h | h
      · exact Or.inl (by simp [h])
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inr ⟨h, by simp [ha]⟩
        · exact Or.inl (List.mem_cons_of_mem _ h)
    · rw [if_neg ha] at h
      rcases List.mem_cons.1 h with h | h
      · exact Or.inl (by simp [h])
      · rcases mem_insAfter h with h' | ⟨h1, h2⟩
        · exact Or.inl (List.mem_cons_of_mem _ h')
        · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩

end

section
variable {G : MdbGhost} {mem mem' : U64 → U64}

/-- **Half (1) of `VcpuChunked` from `MdbInv`** (module docstring). -/
theorem vcpuChunk1_of_mdbInv (hI : MdbInv mem G) (v : U64) :
    ∀ ch ∈ G.chains, ChunkI (fun y => capV mem y = .Vcpu v) ch := by
  intro ch hch
  refine I_of_chunk3 fun a b c hs pa pc => ?_
  have hf : isFrame (capV mem a) = false := by rw [pa]; try rfl
  have hR : srF mem a c = true := by
    rw [srF_nf hf]; unfold srM; rw [pa, pc]; exact srB_vcpu_self v
  have hb := chunkL_sub3 (hI.chunk ch hch) hs hR
  rw [srF_nf hf] at hb; unfold srM at hb; rw [pa] at hb
  exact srB_vcpu_left hb

/-- **All `Vcpu v` caps lie in one ghost chain** (`VcpuChunked`'s second half). -/
def VcpuOneChain (G : MdbGhost) (mem : U64 → U64) : Prop :=
  ∀ v, ∀ ch ∈ G.chains, ∀ ch' ∈ G.chains, ∀ y ∈ ch, ∀ y' ∈ ch',
      capV mem y = .Vcpu v → capV mem y' = .Vcpu v → ch = ch'

/-- **`VcpuChunked` from `MdbInv` and `VcpuOneChain`** (module docstring). -/
theorem vcpuChunked_of (hI : MdbInv mem G) (hO : VcpuOneChain G mem) : VcpuChunked G mem :=
  ⟨fun v ch hch => vcpuChunk1_of_mdbInv hI v ch hch, hO⟩

theorem vcpuChunked_iff (hI : MdbInv mem G) : VcpuChunked G mem ↔ VcpuOneChain G mem :=
  ⟨fun h => h.2, vcpuChunked_of hI⟩

/-- **`VcpuOneChain` across `insG`** (module docstring). -/
theorem vcpuOneChain_insG (hO : VcpuOneChain G mem) (hnd : G.chains.flatten.Nodup) {src dest : U64} (b : Bool)
    (hk : ∀ y ∈ G.chains.flatten, capV mem' y = capV mem y)
    (hc : ∀ v, capV mem' dest = .Vcpu v →
      capV mem src = .Vcpu v ∨ ∀ y ∈ G.chains.flatten, capV mem y ≠ .Vcpu v) :
    VcpuOneChain (insG G src dest b) mem' := by
  intro v c1 hc1 c2 hc2 y hy y' hy' h1 h2
  obtain ⟨d1, hd1, rfl⟩ := List.mem_map.1 hc1
  obtain ⟨d2, hd2, rfl⟩ := List.mem_map.1 hc2
  suffices d1 = d2 by rw [this]
  have hm : ∀ d ∈ G.chains, ∀ z ∈ d, z ∈ G.chains.flatten := fun d hd z hz => List.mem_flatten.2 ⟨d, hd, hz⟩
  have old : ∀ d ∈ G.chains, ∀ z ∈ Mdb.insAfter src dest d, capV mem' z = .Vcpu v →
      (z ∈ d ∧ capV mem z = .Vcpu v) ∨ (z = dest ∧ src ∈ d) := by
    intro d hd z hz hcz
    rcases mem_insAfter hz with h | h
    · exact Or.inl ⟨h, by rw [← hk z (hm d hd z h)]; exact hcz⟩
    · exact Or.inr h
  rcases old d1 hd1 y hy h1 with ⟨m1, p1⟩ | ⟨e1, s1⟩ <;>
    rcases old d2 hd2 y' hy' h2 with ⟨m2, p2⟩ | ⟨e2, s2⟩
  · exact hO v d1 hd1 d2 hd2 y m1 y' m2 p1 p2
  · rw [e2] at h2
    rcases hc v h2 with hs | hn
    · exact hO v d1 hd1 d2 hd2 y m1 src s2 p1 hs
    · exact absurd p1 (hn y (hm d1 hd1 y m1))
  · rw [e1] at h1
    rcases hc v h1 with hs | hn
    · exact hO v d1 hd1 d2 hd2 src s1 y' m2 hs p2
    · exact absurd p2 (hn y' (hm d2 hd2 y' m2))
  · exact vchain_eq hnd hd1 hd2 s1 s2

/-- **`VcpuOneChain` across the retype's insertions** (module docstring). -/
theorem vcpuOneChain_retExp {th : TypedHeap} {m m' : U64 → U64} {G' : MdbGhost} {A w : Nat}
    {dslot : Nat → U64} {xs : U64} (hE : RetExp th th m m' G G' A 32768 w dslot (vcj A) xs) (hCS : ChSub G G')
    (hnd' : G'.chains.flatten.Nodup) (hfit : A + w * 32768 ≤ 2 ^ 64)
    (hfresh : ∀ y ∈ G.chains.flatten, ∀ j, j < w → capV m y ≠ .Vcpu (vI A j))
    (hO : VcpuOneChain G m) : VcpuOneChain G' m' := by
  have cls : ∀ z ∈ G'.chains.flatten, ∀ v, capV m' z = .Vcpu v →
      (z ∈ G.chains.flatten ∧ capV m z = .Vcpu v) ∨ ∃ j, j < w ∧ z = dslot j ∧ v = vI A j := by
    intro z hz v hc
    rcases hE.gmem z hz with hg | ⟨j, hj, e⟩
    · cases hu : isUt (capV m z)
      · exact Or.inl ⟨hg, by rw [← (hE.keep z hg hu).2]; exact hc⟩
      · have := hE.utk z hg hu; rw [hc] at this; simp [isUt] at this
    · refine Or.inr ⟨j, hj, e, ?_⟩
      rw [e, hE.newc j hj] at hc
      exact (capability.Cap.Vcpu.inj hc).symm
  intro v c1 hc1 c2 hc2 y hy y' hy' h1 h2
  have hym := List.mem_flatten.2 ⟨c1, hc1, hy⟩
  have hym' := List.mem_flatten.2 ⟨c2, hc2, hy'⟩
  rcases cls y hym v h1 with ⟨g1, p1⟩ | ⟨j1, hj1, e1, v1⟩ <;>
    rcases cls y' hym' v h2 with ⟨g2, p2⟩ | ⟨j2, hj2, e2, v2⟩
  · obtain ⟨d1, hd1, hyd⟩ := List.mem_flatten.1 g1
    obtain ⟨d2, hd2, hyd'⟩ := List.mem_flatten.1 g2
    have e := hO v d1 hd1 d2 hd2 y hyd y' hyd' p1 p2
    subst e
    obtain ⟨ch', hch', hsub⟩ := hCS d1 hd1
    exact (vchain_eq hnd' hc1 hch' hy (hsub y hyd)).trans (vchain_eq hnd' hch' hc2 (hsub y' hyd') hy')
  · rw [v2] at p1; exact absurd p1 (hfresh y g1 j2 hj2)
  · rw [v1] at p2; exact absurd p2 (hfresh y' g2 j1 hj1)
  · have hj : j1 = j2 := by
      have h12 : vI A j1 = vI A j2 := v1.symm.trans v2
      have a1 := vI_val (B := A) (j := j1) (by omega)
      have a2 := vI_val (B := A) (j := j2) (by omega)
      rw [h12] at a1
      have : j1 * 32768 = j2 * 32768 := by omega
      omega
    subst hj
    rw [e1] at hy; rw [e2] at hy'
    exact vchain_eq hnd' hc1 hc2 hy hy'

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **Freshness from `JExtV2`**: an old member's `Vcpu p` cap has `p ∈ V`. -/
theorem fresh_of_jextV2 {V X : Set U64} {th : TypedHeap} {s : S} {G : MdbGhost} (E : JExtV2 (L := L) V X th s)
    (hM : MdbLinks th (L.mem s) G) {A w : Nat} (hV : ∀ v ∈ V, ∀ j, j < w → v ≠ vI A j) :
    ∀ y ∈ G.chains.flatten, ∀ j, j < w → capV (L.mem s) y ≠ .Vcpu (vI A j) := by
  intro y hy j hj hc
  have h := E.cap y ((hM.members y).1 hy).1
  rw [hc] at h
  exact hV _ h j hj rfl

/-- **`cdt::insert` keeps `VcpuOneChain`** (module docstring). -/
theorem insert_vcpuOneChain {th : TypedHeap} (hP : Placed th) (s : S) (G : MdbGhost)
    (hM : MdbLinks th (L.mem s) G) (hO : VcpuOneChain G (L.mem s))
    {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest) (hdest : dest ∉ G.chains.flatten)
    {srcC : capability.Cap} (hsrcC : capAt (L.mem s) src = ok srcC)
    (c : capability.Cap) (he : EncWf c) (hfull : fullF srcC c = none)
    (hc : ∀ v, c = .Vcpu v → srcC = .Vcpu v) (b : Bool) :
    cdt.insert st s c src dest ⦃ s' => VcpuOneChain (insG G src dest b) (L.mem s') ⦄ := by
  refine WP.spec_mono (insert_caps_nofull hP s G hM hsrc hd hdest hsrcC c he hfull) fun s' h => ?_
  refine vcpuOneChain_insG hO hM.tree.nodup b (fun y hy => ?_) (fun v hv => Or.inl ?_)
  · have hys : IsSlot th y := ((hM.members y).1 hy).1
    have hne : y ≠ dest := fun e => hdest (e ▸ hy)
    rw [h y hys, if_neg hne]
  · rw [h dest hd, if_pos rfl] at hv
    rw [capV_of_capAt hsrcC]; exact hc v hv

end

end
end Fl4Proofs.P3.VirtVChunkIns
