/-
P3 (DESIGN.md §9), CSpace: the derivation-tree relation after an insertion,
from how the slot words change (memory-level, independent of the code).
-/
import Fl4Proofs.P3.Mdb
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

theorem insAfter_ne_nil {x y : α} [DecidableEq α] {l : List α} (h : l ≠ []) : Mdb.insAfter x y l ≠ [] := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => unfold Mdb.insAfter; split <;> simp

theorem mem_insAfter {x y z : α} [DecidableEq α] {l : List α} (hx : x ∈ l) : z ∈ Mdb.insAfter x y l ↔ z = y ∨ z ∈ l := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hx
  induction A with
  | nil => simp [Mdb.insAfter]; tauto
  | cons a A ih =>
    by_cases ha : a = x
    · subst ha; simp [Mdb.insAfter]; tauto
    · simp only [List.cons_append, Mdb.insAfter, ha, ↓reduceIte, List.mem_cons]
      rw [ih (by simp)]; simp; tauto

theorem chain_unique {L : List (List α)} (hn : L.flatten.Nodup) {c1 c2 : List α} {a : α}
    (h1 : c1 ∈ L) (h2 : c2 ∈ L) (ha1 : a ∈ c1) (ha2 : a ∈ c2) : c1 = c2 := by
  induction L with
  | nil => simp at h1
  | cons c L ih =>
    simp only [List.flatten_cons] at hn
    have hd := List.disjoint_of_nodup_append hn
    have hn' := (List.nodup_append.1 hn).2.1
    simp only [List.mem_cons] at h1 h2
    rcases h1 with rfl | h1 <;> rcases h2 with rfl | h2
    · rfl
    · exact (hd ha1 (List.mem_flatten.2 ⟨_, h2, ha2⟩)).elim
    · exact (hd ha2 (List.mem_flatten.2 ⟨_, h1, ha1⟩)).elim
    · exact ih hn' h1 h2

/-- How the slot words change in an insertion of `dest` after `src` whose
`next` was `N`. -/
structure InsLinks (th : TypedHeap) (mem mem' : U64 → U64) (src dest : U64) : Prop where
  prev : ∀ a, IsSlot th a → prevOf mem' a = if a = dest then src
    else if nextOf mem src ≠ 0#u64 ∧ a = nextOf mem src then dest else prevOf mem a
  next : ∀ a, IsSlot th a → nextOf mem' a = if a = dest then nextOf mem src
    else if a = src then dest else nextOf mem a
  cap_dest : ∃ c, capAt mem' dest = ok c ∧ c ≠ .Null
  cap_src : ∃ c, capAt mem' src = ok c ∧ c ≠ .Null
  cap_other : ∀ a, IsSlot th a → a ≠ dest → a ≠ src → capAt mem' a = capAt mem a

theorem MdbLinks.insert {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64} {G : MdbGhost}
    (hM : MdbLinks th mem G) {src dest : U64} (hsrc : src ∈ G.chains.flatten) (hd : IsSlot th dest)
    (hdest : dest ∉ G.chains.flatten) {np : Option U64} (hcase : Mdb.InsCase G.par src np)
    (hL : InsLinks th mem mem' src dest) :
    MdbLinks th mem' ⟨G.chains.map (Mdb.insAfter src dest), Function.update G.par dest np⟩ := by
  have hslot : ∀ a, a ∈ G.chains.flatten → IsSlot th a := fun a h => ((hM.members a).1 h).1
  have hs := hslot src hsrc
  have hnd := hM.tree.nodup
  obtain ⟨ch0, hch0, hsch⟩ := List.mem_flatten.1 hsrc
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hsch
  have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 hnd).1 _ hch0
  obtain ⟨hsA, hsB⟩ := Mdb.nodup_mid hnd0
  have hdisjAB : ∀ x, x ∈ A → x ∉ B := fun x hx hb =>
    (List.disjoint_of_nodup_append hnd0 hx (List.mem_cons_of_mem _ hb)).elim
  have hmem0 : ∀ x, x ∈ A ++ src :: B → x ∈ G.chains.flatten := fun x hx => List.mem_flatten.2 ⟨_, hch0, hx⟩
  have hdne : ∀ x, x ∈ G.chains.flatten → x ≠ dest := fun x hx e => hdest (e ▸ hx)
  -- `next` of `src`
  set N := nextOf mem src with hNdef
  have hc0 := hM.chain _ hch0
  have hN : (B = [] ∧ N = 0#u64) ∨ (∃ b0 B', B = b0 :: B' ∧ N = b0) := by
    cases B with
    | nil =>
      left; refine ⟨rfl, ?_⟩
      have := hM.last _ hch0 (by simp)
      simpa using this
    | cons b0 B' =>
      right; refine ⟨b0, B', rfl, ?_⟩
      rw [List.isChain_append] at hc0
      exact (List.isChain_cons_cons.1 hc0.2.1).1.1
  -- only `B`'s head can be `N`
  have hnotN : ∀ b, b ∉ B → ¬ (N ≠ 0#u64 ∧ b = N) := by
    rintro b hb ⟨hz, rfl⟩
    rcases hN with ⟨-, h⟩ | ⟨b0, B', rfl, h⟩
    · exact hz h
    · exact hb (h ▸ List.mem_cons_self)
  have hnotN' : ∀ b, b ∈ G.chains.flatten → (∀ c ∈ G.chains, b ∈ c → c ≠ A ++ src :: B) → ¬ (N ≠ 0#u64 ∧ b = N) := by
    intro b hb hc
    apply hnotN
    intro hbB
    obtain ⟨c, hc1, hbc⟩ := List.mem_flatten.1 hb
    exact hc c hc1 hbc (chain_unique hnd hc1 hch0 hbc (by simp [hbB]))
  have hsrcN : ¬ (N ≠ 0#u64 ∧ src = N) := hnotN src hsB
  -- the relation, before and after
  set R := fun a b => nextOf mem a = b ∧ prevOf mem b = a
  set R' := fun a b => nextOf mem' a = b ∧ prevOf mem' b = a
  have hkeep : ∀ a b, a ∈ G.chains.flatten → b ∈ G.chains.flatten → a ≠ src → ¬ (N ≠ 0#u64 ∧ b = N) →
      R a b → R' a b := by
    rintro a b ha hb has hbN ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [hL.next a (hslot a ha)]; simp [hdne a ha, has, h1]
    · rw [hL.prev b (hslot b hb), ← hNdef]; simp only [hdne b hb, ↓reduceIte, hbN, h2]
  refine ⟨Mdb.MdbOK.insert hM.tree hsrc hdest hcase, ?_, ?_, ?_, ?_, ?_⟩
  · intro ch' hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    exact insAfter_ne_nil (hM.ne_nil ch hch)
  · intro ch' hch'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    by_cases hsc : src ∈ ch
    · have e := chain_unique hnd hch hch0 hsc hsch
      subst e
      rw [Mdb.insAfter_split hsA]
      apply Mdb.isChain_ins hc0
      · intro a b ha hb hr
        exact hkeep a b (hmem0 a (by simp [ha])) (hmem0 b (by simp [hb])) (fun e => hsA (e ▸ ha))
          (hnotN b (hdisjAB b hb)) hr
      · intro x hx hr
        have hxA : x ∈ A := List.mem_of_getLast? hx
        exact hkeep x src (hmem0 x (by simp [hxA])) hsrc (fun e => hsA (e ▸ hxA)) hsrcN hr
      · refine ⟨?_, ?_⟩
        · rw [hL.next src hs]; simp [hdne src hsrc]
        · rw [hL.prev dest hd]; simp
      · intro y hy
        rcases hN with ⟨rfl, -⟩ | ⟨b0, B', rfl, hb0⟩
        · simp at hy
        · simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy
          subst hy
          have hb0d : b0 ≠ dest := hdne b0 (hmem0 b0 (by simp))
          have hb0s : b0 ≠ src := fun e => hsB (e ▸ List.mem_cons_self)
          refine ⟨?_, ?_⟩
          · rw [hL.next dest hd, ← hNdef]; simp [hb0]
          · rw [hL.prev b0 (hslot b0 (hmem0 b0 (by simp))), ← hNdef]
            have hz : N ≠ 0#u64 := by
              intro h; rw [h] at hb0; exact (hslot b0 (hmem0 b0 (by simp))).ne_zero hP hb0.symm
            simp only [hb0d, ↓reduceIte, hb0, ne_eq, and_true]
            rw [if_pos (hb0 ▸ hz)]
      · intro a b ha hb hr
        have hbB : b ∈ B := List.mem_of_mem_tail hb
        refine hkeep a b (hmem0 a (by simp [ha])) (hmem0 b (by simp [hbB])) (fun e => hsB (e ▸ ha)) ?_ hr
        rintro ⟨hz, rfl⟩
        rcases hN with ⟨rfl, -⟩ | ⟨b0, B', rfl, hb0⟩
        · simp at ha
        · have hn' : (b0 :: B').Nodup := (List.nodup_append.1 (List.nodup_cons.1 (List.nodup_middle.1 hnd0)).2).2.1
          simp only [List.tail_cons] at hb
          rw [hb0] at hb
          exact (List.nodup_cons.1 hn').1 hb
    · rw [Mdb.insAfter_of_not_mem hsc]
      apply (hM.chain ch hch).imp_of_mem_imp
      intro a b ha hb hr
      have hcne : ∀ c ∈ G.chains, b ∈ c → c ≠ A ++ src :: B := by
        intro c hc hbc e; subst e
        exact hsc (chain_unique hnd hch hc hb hbc ▸ hsch)
      exact hkeep a b (List.mem_flatten.2 ⟨_, hch, ha⟩) (List.mem_flatten.2 ⟨_, hch, hb⟩)
        (fun e => hsc (e ▸ ha)) (hnotN' b (List.mem_flatten.2 ⟨_, hch, hb⟩) hcne) hr
  · -- heads
    intro ch' hch' hne'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    by_cases hsc : src ∈ ch
    · have e := chain_unique hnd hch hch0 hsc hsch
      subst e
      simp only [Mdb.insAfter_split hsA] at hne' ⊢
      have h0 := hM.head _ hch0 (by simp)
      cases A with
      | nil =>
        simp only [List.nil_append, List.head_cons] at h0 ⊢
        rw [hL.prev src hs, ← hNdef]; simp only [hdne src hsrc, ↓reduceIte, hsrcN, h0]
      | cons x A' =>
        simp only [List.cons_append, List.head_cons] at h0 ⊢
        have hx : x ∈ G.chains.flatten := hmem0 x (by simp)
        rw [hL.prev x (hslot x hx), ← hNdef]
        simp only [hdne x hx, ↓reduceIte, hnotN x (hdisjAB x (by simp)), h0]
    · simp only [Mdb.insAfter_of_not_mem hsc] at hne' ⊢
      have hx : ch.head hne' ∈ G.chains.flatten := List.mem_flatten.2 ⟨_, hch, List.head_mem hne'⟩
      have hcne : ∀ c ∈ G.chains, ch.head hne' ∈ c → c ≠ A ++ src :: B := by
        intro c hc hbc e; subst e
        exact hsc (chain_unique hnd hch hc (List.head_mem hne') hbc ▸ hsch)
      rw [hL.prev _ (hslot _ hx), ← hNdef]
      simp only [hdne _ hx, ↓reduceIte, hnotN' _ hx hcne, hM.head ch hch hne']
  · -- lasts
    intro ch' hch' hne'
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    by_cases hsc : src ∈ ch
    · have e := chain_unique hnd hch hch0 hsc hsch
      subst e
      simp only [Mdb.insAfter_split hsA] at hne' ⊢
      rcases hN with ⟨rfl, hN0⟩ | ⟨b0, B', rfl, hb0⟩
      · have : (A ++ [src, dest]).getLast hne' = dest := by simp
        rw [this, hL.next dest hd]; simpa using hN0
      · have h0 := hM.last _ hch0 (by simp)
        have e1 : (A ++ src :: dest :: b0 :: B').getLast hne' = (b0 :: B').getLast (by simp) := by
          rw [List.getLast_append_of_ne_nil _ (by simp)]; simp [List.getLast_cons]
        have e2 : (A ++ src :: b0 :: B').getLast (by simp) = (b0 :: B').getLast (by simp) := by
          rw [List.getLast_append_of_ne_nil _ (by simp)]; simp [List.getLast_cons]
        rw [e2] at h0
        rw [e1]
        have hl : (b0 :: B').getLast (by simp) ∈ b0 :: B' := List.getLast_mem _
        have hlf : (b0 :: B').getLast (by simp) ∈ G.chains.flatten := hmem0 _ (by simp [hl])
        have hls : (b0 :: B').getLast (by simp) ≠ src := fun e => hsB (e ▸ hl)
        rw [hL.next _ (hslot _ hlf), if_neg (hdne _ hlf), if_neg hls, h0]
    · simp only [Mdb.insAfter_of_not_mem hsc] at hne' ⊢
      have hx : ch.getLast hne' ∈ G.chains.flatten := List.mem_flatten.2 ⟨_, hch, List.getLast_mem hne'⟩
      have hls : ch.getLast hne' ≠ src := fun e => hsc (e ▸ List.getLast_mem hne')
      rw [hL.next _ (hslot _ hx), if_neg (hdne _ hx), if_neg hls, hM.last ch hch hne']
  · -- members
    have hmemiff : ∀ a, a ∈ (G.chains.map (Mdb.insAfter src dest)).flatten ↔ a = dest ∨ a ∈ G.chains.flatten := by
      intro a
      simp only [List.mem_flatten, List.mem_map]
      constructor
      · rintro ⟨_, ⟨ch, hch, rfl⟩, ha⟩
        by_cases hsc : src ∈ ch
        · rcases (mem_insAfter hsc).1 ha with h | h
          · exact Or.inl h
          · exact Or.inr ⟨ch, hch, h⟩
        · rw [Mdb.insAfter_of_not_mem hsc] at ha; exact Or.inr ⟨ch, hch, ha⟩
      · rintro (rfl | ⟨ch, hch, ha⟩)
        · exact ⟨_, ⟨_, hch0, rfl⟩, (mem_insAfter hsch).2 (Or.inl rfl)⟩
        · by_cases hsc : src ∈ ch
          · exact ⟨_, ⟨ch, hch, rfl⟩, (mem_insAfter hsc).2 (Or.inr ha)⟩
          · exact ⟨_, ⟨ch, hch, rfl⟩, by rw [Mdb.insAfter_of_not_mem hsc]; exact ha⟩
    intro a
    rw [hmemiff]
    by_cases had : a = dest
    · subst had; simp only [true_or, true_iff]; exact ⟨hd, hL.cap_dest⟩
    · by_cases has : a = src
      · subst has; simp only [had, false_or]
        exact ⟨fun _ => ⟨hs, hL.cap_src⟩, fun _ => hsrc⟩
      · simp only [had, false_or]
        rw [hM.members a]
        constructor
        · rintro ⟨ha, hc⟩; exact ⟨ha, by rw [hL.cap_other a ha had has]; exact hc⟩
        · rintro ⟨ha, hc⟩; exact ⟨ha, by rw [← hL.cap_other a ha had has]; exact hc⟩

/-! ## Abstract slots and their addresses -/

theorem tcbCnodeIndex_blVal (i : Nat) (hi : i < tcbSlots) : blVal 0 (Fl4Spec.tcbCnodeIndex i) = i := by
  simp only [tcbSlots] at hi
  interval_cases i <;> rfl

theorem tcbCnodeIndex_inj {i j : Nat} (hi : i < tcbSlots) (hj : j < tcbSlots)
    (h : Fl4Spec.tcbCnodeIndex i = Fl4Spec.tcbCnodeIndex j) : i = j := by
  rw [← tcbCnodeIndex_blVal i hi, ← tcbCnodeIndex_blVal j hj, h]

/-- The concrete slot of an abstract slot of the typed heap. -/
theorem AbsSlot.at {th : TypedHeap} {sl : Fl4Spec.CslotPtr} (h : AbsSlot th sl) :
    ∃ p i, IsSlotAt th p i ∧ sl.1 = p.bv ∧ cslotAddr sl = slotOf p i := by
  obtain ⟨p, h1, h2 | ⟨ht, i, hi, hidx⟩⟩ := h
  · refine ⟨p, blVal 0 sl.2, Or.inl ⟨_, h2, blVal_lt _⟩, h1, ?_⟩
    obtain ⟨a, b⟩ := sl; simp only at h1; subst h1; exact slotAddr_ofBl _ _
  · refine ⟨p, i, Or.inr ⟨ht, hi⟩, h1, ?_⟩
    obtain ⟨a, b⟩ := sl; simp only at h1 hidx; subst h1 hidx
    show slotAddr p.bv (Fl4Spec.ofBl _) = _
    rw [slotAddr_ofBl, tcbCnodeIndex_blVal i hi]

theorem AbsSlot.isSlot {th : TypedHeap} {sl : Fl4Spec.CslotPtr} (h : AbsSlot th sl) : IsSlot th (cslotAddr sl) := by
  obtain ⟨p, i, hi, -, he⟩ := h.at; exact ⟨p, i, hi, he⟩

theorem slotOf_inj {th : TypedHeap} (hP : Placed th) {p q : U64} {i j : Nat} (hi : IsSlotAt th p i)
    (hj : IsSlotAt th q j) (h : slotOf p i = slotOf q j) : p = q ∧ i = j := by
  by_contra hne
  rcases hi.apart hP hj hne with h' | h' <;> rw [h] at h' <;> omega

theorem cslotAddr_inj {th : TypedHeap} (hP : Placed th) {sl sl' : Fl4Spec.CslotPtr} (h : AbsSlot th sl)
    (h' : AbsSlot th sl') (he : cslotAddr sl = cslotAddr sl') : sl = sl' := by
  obtain ⟨a, idx⟩ := sl; obtain ⟨a', idx'⟩ := sl'
  obtain ⟨p, hp1, hp⟩ := h; obtain ⟨q, hq1, hq⟩ := h'
  simp only at hp1 hq1 hp hq; subst hp1 hq1
  rcases hp with hp | ⟨ht, i, hi, rfl⟩ <;> rcases hq with hq | ⟨ht', j, hj, rfl⟩
  · have e := slotOf_inj hP (Or.inl ⟨_, hp, blVal_lt idx⟩) (Or.inl ⟨_, hq, blVal_lt idx'⟩)
      (by rw [← slotAddr_ofBl, ← slotAddr_ofBl]; exact he)
    obtain ⟨rfl, e2⟩ := e
    rw [hp] at hq
    have hl : idx.length = idx'.length := by injection hq with h; injection h
    rw [idx_inj hl e2]
  · exfalso
    have e := slotOf_inj hP (Or.inl ⟨_, hp, blVal_lt idx⟩) (Or.inr ⟨ht', hj⟩)
      (by rw [← slotAddr_ofBl, ← tcbCnodeIndex_blVal j hj, ← slotAddr_ofBl]; exact he)
    obtain ⟨rfl, -⟩ := e; rw [hp] at ht'; cases ht'
  · exfalso
    have e := slotOf_inj hP (Or.inr ⟨ht, hi⟩) (Or.inl ⟨_, hq, blVal_lt idx'⟩)
      (by rw [← tcbCnodeIndex_blVal i hi, ← slotAddr_ofBl, ← slotAddr_ofBl]; exact he)
    obtain ⟨rfl, -⟩ := e; rw [hq] at ht; cases ht
  · have e := slotOf_inj hP (Or.inr ⟨ht, hi⟩) (Or.inr ⟨ht', hj⟩)
      (by rw [← tcbCnodeIndex_blVal i hi, ← tcbCnodeIndex_blVal j hj, ← slotAddr_ofBl, ← slotAddr_ofBl]; exact he)
    obtain ⟨rfl, rfl⟩ := e; rfl

/-! ## The spec's CDT after an insertion -/

theorem CdtRel.insert {Z : Type} {th : TypedHeap} (hP : Placed th) {mem mem' : U64 → U64}
    {σ σ' : Fl4Spec.State Z} {G : MdbGhost} (hC : CdtRel th mem σ G) (chains' : List (List U64))
    {srcSl destSl : Fl4Spec.CslotPtr} (hs : AbsSlot th srcSl) (hd : AbsSlot th destSl) (b v : Bool)
    (hcdt : σ'.cdt = Function.update σ.cdt destSl (if b then some srcSl else σ.cdt srcSl))
    (hio : σ'.isOriginalCap = Function.update σ.isOriginalCap destSl v)
    (hrev : ∀ a, IsSlot th a → revOf mem' a = if a = cslotAddr destSl then v else revOf mem a) :
    CdtRel th mem' σ' ⟨chains', Function.update G.par (cslotAddr destSl)
      (if b then some (cslotAddr srcSl) else G.par (cslotAddr srcSl))⟩ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro sl hsl
    rw [hcdt]
    by_cases he : sl = destSl
    · subst he
      simp only [Function.update_self]
      cases b
      · simpa using hC.cdt srcSl hs
      · simp
    · have hne : cslotAddr sl ≠ cslotAddr destSl := fun e => he (cslotAddr_inj hP hsl hd e)
      simp only [Function.update_of_ne he, Function.update_of_ne hne]
      exact hC.cdt sl hsl
  · intro sl q hq
    rw [hcdt] at hq
    by_cases he : sl = destSl
    · subst he
      simp only [Function.update_self] at hq
      cases b
      · exact ⟨hd, (hC.cdt_slot _ _ (by simpa using hq)).2⟩
      · simp at hq; subst hq; exact ⟨hd, hs⟩
    · rw [Function.update_of_ne he] at hq; exact hC.cdt_slot sl q hq
  · intro sl hsl
    rw [hio, hrev _ hsl.isSlot]
    by_cases he : sl = destSl
    · subst he; simp
    · have hne : cslotAddr sl ≠ cslotAddr destSl := fun e => he (cslotAddr_inj hP hsl hd e)
      simp only [Function.update_of_ne he, hne, ↓reduceIte]
      exact hC.orig sl hsl
  · intro a x hax
    by_cases he : a = cslotAddr destSl
    · exact ⟨destSl, hd, he.symm⟩
    · simp only [Function.update_of_ne he] at hax
      exact hC.par_slot a x hax

/-- The `next` of a linked slot is null or another linked slot. -/
theorem MdbLinks.next_mem {th : TypedHeap} {mem : U64 → U64} {G : MdbGhost} (hM : MdbLinks th mem G)
    {src : U64} (hsrc : src ∈ G.chains.flatten) :
    nextOf mem src = 0#u64 ∨ (nextOf mem src ∈ G.chains.flatten ∧ nextOf mem src ≠ src) := by
  obtain ⟨ch0, hch0, hsch⟩ := List.mem_flatten.1 hsrc
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hsch
  have hnd0 : (A ++ src :: B).Nodup := (List.nodup_flatten.1 hM.tree.nodup).1 _ hch0
  have hc0 := hM.chain _ hch0
  cases B with
  | nil => left; simpa using hM.last _ hch0 (by simp)
  | cons b0 B' =>
    right
    rw [List.isChain_append] at hc0
    have h1 := (List.isChain_cons_cons.1 hc0.2.1).1.1
    rw [h1]
    refine ⟨List.mem_flatten.2 ⟨_, hch0, by simp⟩, fun e => (Mdb.nodup_mid hnd0).2 (by simp [e])⟩

end

end Fl4Proofs.P3
