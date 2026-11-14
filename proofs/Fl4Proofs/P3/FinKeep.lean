/-
P3 (DESIGN.md §9), CSpace: **`FinInv` is kept** (the generic step).

`FinM.view` is the one lemma the CSpace operations need: after an operation,
read each slot of the new MDB back to a slot of the old one (`f`), whose cap
it resembles (`CapSim`: the same object key, generic references, kind and
same-region behaviour), the new chains being images (`φ`) of old chains;
slots with fresh caps (overlapping nothing, in nobody's region) need no
reading back. Two slots read back to the same old slot (an inserted copy and
its source) must not hold zombies. Instances: `FinM.of_caps` (caps kept),
`FinM.rename` (move, swap), `FinM.remove` (empty), `FinM.insert` (a derived
copy), `FinM.fresh_ins` (a fresh cap), `FinM.recap` (one slot's cap
replaced).
-/
import Fl4Proofs.P3.FinBase
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical

noncomputable section

/-- Two caps alike for `FinInv`. -/
structure CapSim (c' c : capability.Cap) : Prop where
  key : okey c' = okey c
  refs : Fl4Spec.genObjRefs (absCap c') = Fl4Spec.genObjRefs (absCap c)
  zb : isZb c' = isZb c
  fr : isFrame c' = isFrame c
  srl : ∀ b, srB c' b = srB c b
  srr : ∀ b, srB b c' = srB b c

theorem CapSim.refl (c : capability.Cap) : CapSim c c := ⟨rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem refs_of_shape {c' c : capability.Cap} (h : shape c' = shape c) :
    Fl4Spec.genObjRefs (absCap c') = Fl4Spec.genObjRefs (absCap c) := by
  cases c' <;> cases c <;> simp only [shape, reduceCtorEq, capability.Cap.Untyped.injEq,
    capability.Cap.Endpoint.injEq, capability.Cap.Notification.injEq, capability.Cap.Reply.injEq,
    capability.Cap.CNode.injEq, capability.Cap.SchedControl.injEq, capability.Cap.Frame.injEq,
    capability.Cap.PageTable.injEq, capability.Cap.PageDirectory.injEq, capability.Cap.Pdpt.injEq,
    capability.Cap.Pml4.injEq, capability.Cap.AsidPool.injEq] at h <;>
    first
    | rfl
    | (simp_all; done)
    | (obtain ⟨rfl, -⟩ := h; simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt,
        Fl4Spec.archGenRefs, Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef, absCap])
    | (subst h; rfl)
    | (simp [Fl4Spec.genObjRefs, Fl4Spec.objRefs, Fl4Spec.capIrqs, Fl4Spec.capIrqOpt,
        Fl4Spec.archGenRefs, Fl4Spec.archCapSetMap, Fl4Spec.archGenObjRefs, Fl4Spec.aobjRef, absCap, h])

theorem isFrame_of_shape {c' c : capability.Cap} (h : shape c' = shape c) : isFrame c' = isFrame c := by
  cases c' <;> cases c <;> simp_all [shape, isFrame]

theorem CapSim.of_shape {c' c : capability.Cap} (h : shape c' = shape c) (hk : okey c' = okey c) : CapSim c' c :=
  ⟨hk, refs_of_shape h, isZb_of_shape h, isFrame_of_shape h, fun b => srB_congr h rfl,
    fun b => srB_congr rfl h⟩

/-! ## The generic step -/

/-- **`FinM` after an operation**, read back through `f` (see the header). -/
theorem FinM.view {mem mem' : U64 → U64} {G G' : MdbGhost} (hF : FinM mem G)
    (hnd : G'.chains.flatten.Nodup) (fresh : U64 → Prop) (f : U64 → U64) (φ : List U64 → List U64)
    (hφ : ∀ ch' ∈ G'.chains, ∃ ch ∈ G.chains, ch' = φ ch ∧ ∀ z ∈ ch', ¬ fresh z → f z ∈ ch)
    (hcap : ∀ z ∈ G'.chains.flatten, ¬ fresh z → CapSim (capV mem' z) (capV mem (f z)))
    (hcoll : ∀ z ∈ G'.chains.flatten, ∀ w ∈ G'.chains.flatten, ¬ fresh z → ¬ fresh w → z ≠ w → f z = f w →
      isZb (capV mem' z) = false)
    (hfresh : ∀ z ∈ G'.chains.flatten, fresh z → ∀ w ∈ G'.chains.flatten, w ≠ z →
      ¬ Ovl (absCap (capV mem' z)) (absCap (capV mem' w)) ∧ srB (capV mem' z) (capV mem' w) = false ∧
      (isFrame (capV mem' w) = true → srB (capV mem' w) (capV mem' z) = false)) :
    FinM mem' G' := by
  -- each non-fresh slot reads back to an old member
  have hold : ∀ z ∈ G'.chains.flatten, ¬ fresh z → f z ∈ G.chains.flatten := by
    intro z hz hfz
    obtain ⟨ch', hch', hzc⟩ := List.mem_flatten.1 hz
    obtain ⟨ch, hch, -, hin⟩ := hφ ch' hch'
    exact List.mem_flatten.2 ⟨ch, hch, hin z hzc hfz⟩
  have hovl : ∀ z ∈ G'.chains.flatten, ∀ w ∈ G'.chains.flatten, ¬ fresh z → ¬ fresh w →
      Ovl (absCap (capV mem' z)) (absCap (capV mem' w)) → Ovl (absCap (capV mem (f z))) (absCap (capV mem (f w))) := by
    intro z hz w hw hfz hfw h
    unfold Ovl at h ⊢; rwa [(hcap z hz hfz).refs, (hcap w hw hfw).refs] at h
  have hmemf : ∀ ch ∈ G'.chains, ∀ z ∈ ch, z ∈ G'.chains.flatten := fun ch hch z hz =>
    List.mem_flatten.2 ⟨ch, hch, hz⟩
  refine ⟨fun ch1 hch1 ch2 hch2 x hx y hy hov => ?_, fun x hx y hy hxy hov hzx hzy => ?_,
    fun x hx y hy hxy hfr hsr => ?_, fun x hx y hy hxy hzx hov => ?_⟩
  · -- conn
    by_cases hxy : x = y
    · subst hxy; exact chain_unique hnd hch1 hch2 hx hy
    by_cases hfx : fresh x
    · exact absurd hov (hfresh x (hmemf _ hch1 x hx) hfx y (hmemf _ hch2 y hy) (Ne.symm hxy)).1
    by_cases hfy : fresh y
    · exact absurd hov.symm (hfresh y (hmemf _ hch2 y hy) hfy x (hmemf _ hch1 x hx) hxy).1
    obtain ⟨c1, hc1, rfl, hin1⟩ := hφ ch1 hch1
    obtain ⟨c2, hc2, rfl, hin2⟩ := hφ ch2 hch2
    rw [hF.conn c1 hc1 c2 hc2 (f x) (hin1 x hx hfx) (f y) (hin2 y hy hfy)
      (hovl x (hmemf _ hch1 x hx) y (hmemf _ hch2 y hy) hfx hfy hov)]
  · -- key
    by_cases hfx : fresh x
    · exact absurd hov (hfresh x hx hfx y hy (Ne.symm hxy)).1
    by_cases hfy : fresh y
    · exact absurd hov.symm (hfresh y hy hfy x hx hxy).1
    rw [(hcap x hx hfx).key, (hcap y hy hfy).key]
    by_cases e : f x = f y
    · rw [e]
    · exact hF.key _ (hold x hx hfx) _ (hold y hy hfy) e (hovl x hx y hy hfx hfy hov)
        (by rw [← (hcap x hx hfx).zb]; exact hzx) (by rw [← (hcap y hy hfy).zb]; exact hzy)
  · -- fnest
    by_cases hfx : fresh x
    · have := (hfresh x hx hfx y hy (Ne.symm hxy)).2.1
      unfold srM at hsr; rw [this] at hsr; cases hsr
    by_cases hfy : fresh y
    · have := (hfresh y hy hfy x hx hxy).2.2 hfr
      unfold srM at hsr; rw [this] at hsr; cases hsr
    rw [(hcap x hx hfx).key, (hcap y hy hfy).key]
    by_cases e : f x = f y
    · rw [e]
    · refine hF.fnest _ (hold x hx hfx) _ (hold y hy hfy) e (by rw [← (hcap x hx hfx).fr]; exact hfr) ?_
      unfold srM at hsr ⊢
      rw [(hcap x hx hfx).srl, (hcap y hy hfy).srr] at hsr; exact hsr
  · -- zfin
    by_cases hfx : fresh x
    · exact (hfresh x hx hfx y hy (Ne.symm hxy)).1 hov
    by_cases hfy : fresh y
    · exact (hfresh y hy hfy x hx hxy).1 hov.symm
    by_cases e : f x = f y
    · rw [hcoll x hx y hy hfx hfy hxy e] at hzx; cases hzx
    · exact hF.zfin _ (hold x hx hfx) _ (hold y hy hfy) e (by rw [← (hcap x hx hfx).zb]; exact hzx)
        (hovl x hx y hy hfx hfy hov)

/-! ## Instances -/

/-- The caps of the MDB kept. -/
theorem FinM.of_caps {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) (hnd : G.chains.flatten.Nodup)
    (h : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z) : FinM mem' G :=
  hF.view hnd (fun _ => False) id id (fun ch hch => ⟨ch, hch, rfl, fun z hz _ => hz⟩)
    (fun z hz _ => by rw [h z hz]; exact CapSim.refl _) (fun z _ w _ _ _ hzw e => absurd e hzw)
    (fun _ _ h => h.elim)

/-- One slot's cap replaced by a like one. -/
theorem FinM.recap {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) (hnd : G.chains.flatten.Nodup)
    (x : U64) (hx : CapSim (capV mem' x) (capV mem x))
    (h : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) : FinM mem' G :=
  hF.view hnd (fun _ => False) id id (fun ch hch => ⟨ch, hch, rfl, fun z hz _ => hz⟩)
    (fun z hz _ => by
      by_cases e : z = x
      · subst e; exact hx
      · rw [h z hz e]; exact CapSim.refl _)
    (fun z _ w _ _ _ hzw e => absurd e hzw) (fun _ _ h => h.elim)

/-- One slot's cap replaced by a fresh one (overlapping no other cap). -/
theorem FinM.refresh {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) (hnd : G.chains.flatten.Nodup)
    (x : U64) (h : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z)
    (hfr : ∀ w ∈ G.chains.flatten, w ≠ x →
      ¬ Ovl (absCap (capV mem' x)) (absCap (capV mem' w)) ∧ srB (capV mem' x) (capV mem' w) = false ∧
      (isFrame (capV mem' w) = true → srB (capV mem' w) (capV mem' x) = false)) : FinM mem' G :=
  hF.view hnd (fun z => z = x) id id (fun ch hch => ⟨ch, hch, rfl, fun z hz _ => hz⟩)
    (fun z hz hzx => by rw [h z hz hzx]; exact CapSim.refl _) (fun z _ w _ _ _ hzw e => absurd e hzw)
    (fun z _ hzx w hw hwz => by subst hzx; exact hfr w hw hwz)

theorem mem_renG {G : MdbGhost} (e : U64 ≃ U64) (z : U64) :
    z ∈ (renG G e).chains.flatten ↔ e.symm z ∈ G.chains.flatten := by
  show z ∈ (G.chains.map (List.map e)).flatten ↔ _
  simp only [List.map_flatten.symm, List.mem_map]
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro h; exact ⟨_, h, by simp⟩

/-- Caps renamed along `e` (move, swap). -/
theorem FinM.rename {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) (e : U64 ≃ U64)
    (hnd : (renG G e).chains.flatten.Nodup)
    (hcap : ∀ a ∈ G.chains.flatten, CapSim (capV mem' (e a)) (capV mem a)) : FinM mem' (renG G e) := by
  refine hF.view hnd (fun _ => False) e.symm (List.map e) (fun ch' hch' => ?_) (fun z hz _ => ?_)
    (fun z _ w _ _ _ hzw h => absurd (e.symm.injective h) hzw) (fun _ _ h => h.elim)
  · obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    refine ⟨ch, hch, rfl, fun z hz _ => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hz
    simpa using ha
  · have := hcap (e.symm z) ((mem_renG e z).1 hz)
    simpa using this

/-- A slot emptied (removed from its chain). -/
theorem FinM.remove {th : TypedHeap} {mem mem' : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    (hF : FinM mem G) (x : U64) (hnd : (remG G x).chains.flatten.Nodup)
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ x → capV mem' z = capV mem z) : FinM mem' (remG G x) := by
  have hn0 := hM.tree.nodup
  refine hF.view hnd (fun _ => False) id (fun ch => @List.erase U64 instBEqOfDecidableEq ch x) (fun ch' hch' => ?_) (fun z hz _ => ?_)
    (fun z _ w _ _ _ hzw h => absurd h hzw) (fun _ _ h => h.elim)
  · obtain ⟨hm, -⟩ := List.mem_filter.1 hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hm
    exact ⟨ch, hch, rfl, fun z hz _ => (@List.erase_sublist U64 instBEqOfDecidableEq x ch).subset hz⟩
  · have h := (Mdb.mem_removeChains hn0).1 hz
    rw [hcap z h.1 h.2]; exact CapSim.refl _

/-- A copy of `src`'s cap inserted at `dest` (`src`'s own cap kept alike). -/
theorem FinM.insert {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) {src dest : U64}
    (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten) (b : Bool)
    (hnd : (insG G src dest b).chains.flatten.Nodup)
    (hcd : CapSim (capV mem' dest) (capV mem src)) (hzd : isZb (capV mem' dest) = false)
    (hcs : CapSim (capV mem' src) (capV mem src))
    (hcap : ∀ z ∈ G.chains.flatten, z ≠ src → capV mem' z = capV mem z) : FinM mem' (insG G src dest b) := by
  have hne : ∀ z ∈ G.chains.flatten, z ≠ dest := fun z hz e => hdest (e ▸ hz)
  refine hF.view hnd (fun _ => False) (fun z => if z = dest then src else z) (Mdb.insAfter src dest)
    (fun ch' hch' => ?_) (fun z hz _ => ?_) (fun z hz w hw _ _ hzw e => ?_) (fun _ _ h => h.elim)
  · obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    refine ⟨ch, hch, rfl, fun z hz _ => ?_⟩
    by_cases hs : src ∈ ch
    · rcases (mem_insAfter hs).1 hz with rfl | hz
      · simp [hs]
      · rw [if_neg (hne z (List.mem_flatten.2 ⟨ch, hch, hz⟩))]; exact hz
    · rw [Mdb.insAfter_of_not_mem hs] at hz
      rw [if_neg (hne z (List.mem_flatten.2 ⟨ch, hch, hz⟩))]; exact hz
  · rcases (mem_flatten_ins hsrc).1 hz with rfl | hz0
    · simp only [↓reduceIte]; exact hcd
    · rw [if_neg (hne z hz0)]
      by_cases e : z = src
      · subst e; exact hcs
      · rw [hcap z hz0 e]; exact CapSim.refl _
  · have hzs : ∀ u ∈ (insG G src dest b).chains.flatten, (if u = dest then src else u) = src → u = dest ∨ u = src := by
      intro u _ h; by_cases e : u = dest
      · exact Or.inl e
      · rw [if_neg e] at h; exact Or.inr h
    by_cases hz0 : z = dest
    · subst hz0; exact hzd
    · rw [if_neg hz0] at e
      by_cases hw0 : w = dest
      · subst hw0; simp only [↓reduceIte] at e; subst e
        rw [hcs.zb, ← hcd.zb]; exact hzd
      · rw [if_neg hw0] at e; exact absurd e hzw

/-- A fresh cap inserted at `dest` (overlapping no other cap, in nobody's
region): a control cap's child. -/
theorem FinM.fresh_ins {mem mem' : U64 → U64} {G : MdbGhost} (hF : FinM mem G) {src dest : U64}
    (hsrc : src ∈ G.chains.flatten) (hdest : dest ∉ G.chains.flatten) (b : Bool)
    (hnd : (insG G src dest b).chains.flatten.Nodup)
    (hcap : ∀ z ∈ G.chains.flatten, capV mem' z = capV mem z)
    (hfr : ∀ w ∈ G.chains.flatten,
      ¬ Ovl (absCap (capV mem' dest)) (absCap (capV mem' w)) ∧ srB (capV mem' dest) (capV mem' w) = false ∧
      (isFrame (capV mem' w) = true → srB (capV mem' w) (capV mem' dest) = false)) :
    FinM mem' (insG G src dest b) := by
  have hne : ∀ z ∈ G.chains.flatten, z ≠ dest := fun z hz e => hdest (e ▸ hz)
  refine hF.view hnd (fun z => z = dest) id (Mdb.insAfter src dest)
    (fun ch' hch' => ?_) (fun z hz hzd => ?_) (fun z _ w _ _ _ hzw e => absurd e hzw)
    (fun z _ hzd w hw hwz => ?_)
  · obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    refine ⟨ch, hch, rfl, fun z hz hzd => ?_⟩
    by_cases hs : src ∈ ch
    · rcases (mem_insAfter hs).1 hz with h | hz
      · exact absurd h hzd
      · exact hz
    · rw [Mdb.insAfter_of_not_mem hs] at hz; exact hz
  · rcases (mem_flatten_ins hsrc).1 hz with h | hz0
    · exact absurd h hzd
    · rw [hcap z hz0]; exact CapSim.refl _
  · subst hzd
    rcases (mem_flatten_ins hsrc).1 hw with h | hw0
    · exact absurd h hwz
    · exact hfr w hw0

/-! ## The chains are determined by the links -/

theorem walk_det {α : Type} (nx : α → α) (z : α) : ∀ (L1 L2 : List α) (x : α),
    (x :: L1).IsChain (fun a b => nx a = b) → (x :: L2).IsChain (fun a b => nx a = b) →
    (∀ l ∈ (x :: L1).getLast?, nx l = z) → (∀ l ∈ (x :: L2).getLast?, nx l = z) →
    (∀ y ∈ L1, y ≠ z) → (∀ y ∈ L2, y ≠ z) → L1 = L2 := by
  intro L1
  induction L1 with
  | nil =>
    intro L2 x _ h2 e1 _ _ n2
    have hx : nx x = z := e1 x (by simp)
    cases L2 with
    | nil => rfl
    | cons y L2 =>
      have := (List.isChain_cons_cons.1 h2).1
      exact absurd (this.symm.trans hx) (n2 y (by simp))
  | cons y L1 ih =>
    intro L2 x h1 h2 e1 e2 n1 n2
    have hy := (List.isChain_cons_cons.1 h1).1
    cases L2 with
    | nil =>
      have : nx x = z := e2 x (by simp)
      exact absurd (hy.symm.trans this) (n1 y (by simp))
    | cons y' L2 =>
      have hy' := (List.isChain_cons_cons.1 h2).1
      have e : y = y' := hy.symm.trans hy'
      subst e
      rw [ih L2 y (List.isChain_cons_cons.1 h1).2 (List.isChain_cons_cons.1 h2).2
        (fun l hl => e1 l (by simpa using hl)) (fun l hl => e2 l (by simpa using hl))
        (fun u hu => n1 u (by simp [hu])) (fun u hu => n2 u (by simp [hu]))]

theorem chains_same {th : TypedHeap} (hP : Placed th) {mem : U64 → U64} {G1 G2 : MdbGhost}
    (h1 : MdbLinks th mem G1) (h2 : MdbLinks th mem G2) {ch1 ch2 : List U64} (hc1 : ch1 ∈ G1.chains)
    (hc2 : ch2 ∈ G2.chains) {x : U64} (hx1 : x ∈ ch1) (hx2 : x ∈ ch2) : ch1 = ch2 := by
  have nz1 : ∀ y ∈ ch1, y ≠ 0#u64 := fun y hy =>
    ((h1.members y).1 (List.mem_flatten.2 ⟨ch1, hc1, hy⟩)).1.ne_zero hP
  have nz2 : ∀ y ∈ ch2, y ≠ 0#u64 := fun y hy =>
    ((h2.members y).1 (List.mem_flatten.2 ⟨ch2, hc2, hy⟩)).1.ne_zero hP
  have k1 := h1.chain _ hc1
  have k2 := h2.chain _ hc2
  have l1 := h1.last _ hc1 (List.ne_nil_of_mem hx1)
  have l2 := h2.last _ hc2 (List.ne_nil_of_mem hx2)
  have f1 := h1.head _ hc1 (List.ne_nil_of_mem hx1)
  have f2 := h2.head _ hc2 (List.ne_nil_of_mem hx2)
  obtain ⟨A1, B1, rfl⟩ := List.append_of_mem hx1
  obtain ⟨A2, B2, rfl⟩ := List.append_of_mem hx2
  rw [List.isChain_append] at k1 k2
  have hB : B1 = B2 := by
    refine walk_det (nextOf mem) 0#u64 B1 B2 x (k1.2.1.imp fun _ _ h => h.1) (k2.2.1.imp fun _ _ h => h.1)
      (fun l hl => ?_) (fun l hl => ?_) (fun u hu => nz1 u (by simp [hu])) (fun u hu => nz2 u (by simp [hu]))
    · have : l = (A1 ++ x :: B1).getLast (List.ne_nil_of_mem hx1) := by
        rw [List.getLast_append_of_ne_nil _ (by simp)]
        obtain ⟨_, e⟩ := List.mem_getLast?_eq_getLast hl
        exact e
      rw [this]; exact l1
    · have : l = (A2 ++ x :: B2).getLast (List.ne_nil_of_mem hx2) := by
        rw [List.getLast_append_of_ne_nil _ (by simp)]
        obtain ⟨_, e⟩ := List.mem_getLast?_eq_getLast hl
        exact e
      rw [this]; exact l2
  have hA : A1 = A2 := by
    have r1 : (A1 ++ [x]).IsChain (fun a b => nextOf mem a = b ∧ prevOf mem b = a) := by
      have := (List.isChain_append (l₁ := A1 ++ [x]) (l₂ := B1)).1 (by simpa using
        (List.isChain_append.2 k1))
      exact this.1
    have r2 : (A2 ++ [x]).IsChain (fun a b => nextOf mem a = b ∧ prevOf mem b = a) := by
      have := (List.isChain_append (l₁ := A2 ++ [x]) (l₂ := B2)).1 (by simpa using
        (List.isChain_append.2 k2))
      exact this.1
    have q1 : (x :: A1.reverse).IsChain (fun a b => prevOf mem a = b) := by
      have := List.isChain_reverse.2 (r1.imp fun _ _ h => h.2)
      simpa using this
    have q2 : (x :: A2.reverse).IsChain (fun a b => prevOf mem a = b) := by
      have := List.isChain_reverse.2 (r2.imp fun _ _ h => h.2)
      simpa using this
    have e := walk_det (prevOf mem) 0#u64 A1.reverse A2.reverse x q1 q2 (fun l hl => ?_) (fun l hl => ?_)
      (fun u hu => nz1 u (by simp at hu; simp [hu])) (fun u hu => nz2 u (by simp at hu; simp [hu]))
    · exact List.reverse_injective e
    · have : l = (A1 ++ x :: B1).head (List.ne_nil_of_mem hx1) := by
        cases A1 with
        | nil => simp at hl ⊢; exact hl.symm
        | cons a A => simp at hl ⊢; rw [List.getLast?_eq_getLast (by simp)] at hl; simp at hl; exact hl.symm
      rw [this]; exact f1
    · have : l = (A2 ++ x :: B2).head (List.ne_nil_of_mem hx2) := by
        cases A2 with
        | nil => simp at hl ⊢; exact hl.symm
        | cons a A => simp at hl ⊢; rw [List.getLast?_eq_getLast (by simp)] at hl; simp at hl; exact hl.symm
      rw [this]; exact f2
  rw [hA, hB]

/-- **`FinM` does not depend on the ghost tree**, only on the links. -/
theorem FinM.of_links {th : TypedHeap} (hP : Placed th) {mem : U64 → U64} {G1 G2 : MdbGhost}
    (h1 : MdbLinks th mem G1) (h2 : MdbLinks th mem G2) (hF : FinM mem G1) : FinM mem G2 := by
  have hm : ∀ z, z ∈ G2.chains.flatten ↔ z ∈ G1.chains.flatten := fun z => (h2.members z).trans (h1.members z).symm
  refine ⟨fun c1 hc1 c2 hc2 x hx y hy hov => ?_, fun x hx y hy => hF.key x ((hm x).1 hx) y ((hm y).1 hy),
    fun x hx y hy => hF.fnest x ((hm x).1 hx) y ((hm y).1 hy), fun x hx y hy => hF.zfin x ((hm x).1 hx) y ((hm y).1 hy)⟩
  obtain ⟨d1, hd1, hxd⟩ := List.mem_flatten.1 ((hm x).1 (List.mem_flatten.2 ⟨c1, hc1, hx⟩))
  obtain ⟨d2, hd2, hyd⟩ := List.mem_flatten.1 ((hm y).1 (List.mem_flatten.2 ⟨c2, hc2, hy⟩))
  have e := hF.conn d1 hd1 d2 hd2 x hxd y hyd hov
  subst e
  rw [← chains_same hP h1 h2 hd1 hc1 hxd hx, chains_same hP h1 h2 hd1 hc2 hyd hy]

end

end Fl4Proofs.P3
