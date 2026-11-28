/-
P1 (aarch64, gen 50): **the MDB loop field complete** — `LoopMZ`'s (QueueZombieQ, gen 50) five obligations for
`MdbS` (MdbLoop) all discharged, so the MDB facts `MdbLk ∧ RngOneA64 ∧ KindA ∧ NullLk ∧ ClsA` go through gen 41's
exposed deletion and gen 39's deferred deletion with no obligation left as a hypothesis.

* **`fin`** — **`finXQM`**: the finalisation of a `ZQ` cap keeps `MdbS`, and a `Zombie p t _` remainder leaves the slot
  `ZrA`-ready. Per finaliser: the `K` class writes only `VsR` words (`FinKT`, `JV.vsr`: `OSKeep`); leaves, threads,
  VCPUs and SCs keep every `OS` word (`finL`, `finXT`, `osk_sc`); a final `IrqHandler` runs **`cdt.delete_one.mdbS`**
  on its IRQ-node slot (a notification or `Null`: the notification finaliser keeps every `OS` word, then
  `empty_slot` with a `Null` cleanup, gen 49's `cdt.empty_slot.mdbO`) — **`finalise_cap.irq_mdbS`**; `CNode` / `Zombie`
  finalisation keeps the state.
* **`ZrA st OS s x p t`**: slot `x` holds a key cap of base `p`, and either no other `OS` slot holds a key cap of base
  `p`, or `x` already holds `Zombie p t _`. A `CNode p` / `Thread p` remainder comes only from a final cap
  (objects.rs `finalise_cap_object`: `if fin`), and **`final_uniq`** turns finality into "no other key cap of base
  `p`": a second one has the class (`ClsA`), lies in the chain (`RngOneA64.one`), so a chain neighbour has the class
  (**`MdbLk.cls_nb`**, `chunk`) and the kind (`KindA`), hence is `same_object_as` the cap (`so_cnode`, `so_thread`)
  and `is_final_capability` (cdt.rs:158–175) would have answered `false`.
* **`setz`** — **`obj.Slot.set_cap.mdbZ`**: the `Zombie` write keeps `MdbS` from `ZrA`: the unique case by
  **`MdbS.setU`** (a key cap of base `p` replacing the only key cap of base `p`: class and kind may change); the
  same-`Zombie` case by gen 46/47/49's in-place `set_cap` lemmas (a decoded `Zombie`'s type is below 256,
  `CapRt.decodeF_encWf`, so the rewritten cap has the same class).
* **`LoopMZ.mdb`**: the instance; **`cdt.delete.zqIGTmdbF`**, **`cdt.delete_deferred.zqGmdbF`**: gen 49's
  `zqIGTmdb` / `zqGmdb` without `hfin` / `hsetz`.

Named premises: none. No case hypothesis beyond those of gen 49's loop statements.
-/
import Fl4ProofsA64.P1.MdbLoop
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

/-! ## Caps: key, base, class -/

theorem RngKeyA.zombie (p t n : U64) : RngKeyA (.Zombie p t n) := by
  have h := physA_eq (.Zombie p t n)
  simp only [objects.cap_is_physical] at h
  exact ⟨(okinj h).symm, rfl, rfl⟩

theorem RngKeyA.cnode (p r g b : U64) : RngKeyA (.CNode p r g b) := by
  have h := physA_eq (.CNode p r g b)
  simp only [objects.cap_is_physical] at h
  exact ⟨(okinj h).symm, rfl, rfl⟩

theorem RngKeyA.thread (p : U64) : RngKeyA (.Thread p) := by
  have h := physA_eq (.Thread p)
  simp only [objects.cap_is_physical] at h
  exact ⟨(okinj h).symm, rfl, rfl⟩

theorem ptrA_zombie (p t n : U64) : ptrA (.Zombie p t n) = p := by
  have h := ptrA_eq (.Zombie p t n); simp only [capability.Cap.ptr] at h; exact (okinj h).symm

theorem ptrA_cnode (p r g b : U64) : ptrA (.CNode p r g b) = p := by
  have h := ptrA_eq (.CNode p r g b); simp only [capability.Cap.ptr] at h; exact (okinj h).symm

theorem ptrA_thread (p : U64) : ptrA (.Thread p) = p := by
  have h := ptrA_eq (.Thread p); simp only [capability.Cap.ptr] at h; exact (okinj h).symm

theorem sizeA_cnode (p r g b : U64) : sizeA (.CNode p r g b) = wa r fl4_abi.consts.bits.SLOT := by
  have h := sizeA_eq (.CNode p r g b); simp only [objects.cap_size_bits] at h; exact (okinj h).symm

/-- A `Zombie`'s class does not depend on its count. -/
theorem clsA_zombie (p t n n' : U64) : clsA (.Zombie p t n) = clsA (.Zombie p t n') := by
  have e : sizeA (.Zombie p t n) = sizeA (.Zombie p t n') :=
    okinj ((sizeA_eq (.Zombie p t n)).symm.trans
      ((rfl : objects.cap_size_bits (.Zombie p t n) = objects.cap_size_bits (.Zombie p t n')).trans
        (sizeA_eq _)))
  unfold clsA; rw [ptrA_zombie, ptrA_zombie, e]

theorem wa_cancel {a b k : U64} (h : wa a k = wa b k) : a = b := by
  have h' := congrArg UScalar.val h
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits] at h'
  have hk : k.val < 2 ^ 64 := by have := k.hBounds; simpa using this
  have ha : a.val < 2 ^ 64 := by have := a.hBounds; simpa using this
  have hb : b.val < 2 ^ 64 := by have := b.hBounds; simpa using this
  apply UScalar.eq_of_val_eq
  omega

theorem and255 {t : U64} (h : t.val < 256) : t &&& 255#u64 = t := by
  apply UScalar.eq_of_val_eq
  have e : (t &&& 255#u64).val = t.val &&& 255 := by simp
  rw [e, show (255 : Nat) = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

/-- Two caps of the `CNode` kind and class are `same_object_as` each other. -/
theorem so_cnode (p r g b : U64) (d : capability.Cap) (kd : kindA d = kindA (.CNode p r g b))
    (cd : clsA d = clsA (.CNode p r g b)) :
    objects.same_object_as (.CNode p r g b) d = ok true ∧ objects.same_object_as d (.CNode p r g b) = ok true := by
  cases d <;> simp only [kindA] at kd <;> try omega
  rename_i p' r' g' b'
  have e1 := ptrA_of_cls cd
  have e2 := congrArg Prod.snd cd
  simp only [clsA] at e2
  rw [ptrA_cnode, ptrA_cnode] at e1
  rw [sizeA_cnode, sizeA_cnode] at e2
  have e3 := wa_cancel e2
  subst e1; subst e3
  simp [objects.same_object_as, objects.same_region_as]

/-- Two caps of the `Thread` kind and base are `same_object_as` each other. -/
theorem so_thread (p : U64) (d : capability.Cap) (kd : kindA d = kindA (.Thread p))
    (cd : clsA d = clsA (.Thread p)) :
    objects.same_object_as (.Thread p) d = ok true ∧ objects.same_object_as d (.Thread p) = ok true := by
  cases d <;> simp only [kindA] at kd <;> try omega
  rename_i p'
  have e1 := ptrA_of_cls cd
  rw [ptrA_thread, ptrA_thread] at e1
  subst e1
  simp [objects.same_object_as, objects.same_region_as]

/-! ## Finality ⇒ the only key cap of its base -/

section fin
variable {OS : Set U64} {G : List (List U64)}

theorem is_final_wc (s : S) (x : U64) :
    cdt.is_final_capability st s x = cdt.is_final_capability_with_cap st s x (capA st s x) := by
  unfold cdt.is_final_capability; rw [capA_eq, bind_ok]

/-- **A chain neighbour of the class** (generalises gen 47's `MdbLk.pt_nb` from `PageTable` to any class): another
`OS` slot with a key cap of `x`'s class ⇒ `x`'s `NEXT` or `PREV` neighbour holds a key cap of the class. -/
theorem MdbLk.cls_nb {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s) {x y : U64} (hx : x ∈ OS)
    (hy : y ∈ OS) (hne : y ≠ x) (kx : RngKeyA (capA st s x)) (ky : RngKeyA (capA st s y))
    (hcl : clsA (capA st s y) = clsA (capA st s x)) :
    ∃ b ∈ OS, RngKeyA (capA st s b) ∧ clsA (capA st s b) = clsA (capA st s x) ∧
      (NxA st s x = b ∨ L.mem s (wa x 16#u64) = b) := by
  have hxG : x ∈ G.flatten := (hM.members x).2 ⟨hx, fun e => RngKeyA.not_null (e ▸ kx)⟩
  have hyG : y ∈ G.flatten := (hM.members y).2 ⟨hy, fun e => RngKeyA.not_null (e ▸ ky)⟩
  have inOS : ∀ ch ∈ G, ∀ (n : Nat) (w : U64), ch[n]? = some w → w ∈ OS := fun ch hch n w e =>
    ((hM.members w).1 (List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩)).1
  obtain ⟨ch, hch, hxc, hyc⟩ := hRO.one x hxG y hyG kx ky hcl.symm
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hxc
  obtain ⟨k, hk, hyk⟩ := List.getElem_of_mem hyc
  have ei : ch[i]? = some x := by rw [getElem?_of_lt hi, hxi]
  have ek : ch[k]? = some y := by rw [getElem?_of_lt hk, hyk]
  have hik : i ≠ k := fun e => hne (by subst e; exact hyk.symm.trans hxi)
  rcases Nat.lt_or_gt_of_ne hik with hlt | hlt
  · have h1 : i + 1 < ch.length := by omega
    have e1 := getElem?_of_lt h1
    have hb := inOS ch hch _ _ e1
    have hcl' : RngKeyA (capA st s ch[i + 1]) ∧ clsA (capA st s ch[i + 1]) = clsA (capA st s x) := by
      by_cases e : i + 1 = k
      · have : ch[i + 1] = y := by rw [← hyk]; congr
        rw [this]; exact ⟨ky, hcl⟩
      · exact hRO.chunk ch hch i (i + 1) k x _ y ei e1 ek (by omega) (by omega) kx ky hcl.symm
    exact ⟨_, hb, hcl'.1, hcl'.2, Or.inl (hM.chain ch hch i x _ ei e1).1⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have h1 : j < ch.length := by omega
    have e1 := getElem?_of_lt h1
    have hb := inOS ch hch _ _ e1
    have hcl' : RngKeyA (capA st s ch[j]) ∧ clsA (capA st s ch[j]) = clsA (capA st s x) := by
      by_cases e : j = k
      · have : ch[j] = y := by rw [← hyk]; congr
        rw [this]; exact ⟨ky, hcl⟩
      · obtain ⟨kb, cb⟩ := hRO.chunk ch hch k j (j + 1) y _ x ek e1 ei (by omega) (by omega) ky kx hcl
        exact ⟨kb, cb.trans hcl⟩
    exact ⟨_, hb, hcl'.1, hcl'.2, Or.inr (hM.chain ch hch j _ x e1 ei).2⟩

/-- **Finality ⇒ no other key cap of the base** (module docstring), for a cap `same_object_as` every cap of its kind
and class (`CNode`, `Thread`). -/
theorem final_uniq (h0 : ∀ y ∈ OS, y ≠ 0#u64) {s : S} (hM : MdbLk st OS G s) (hRO : RngOneA64 st G s)
    (hK : KindA st OS s) (hC : ClsA st OS s) {x p : U64} {c : capability.Cap} (hx : x ∈ OS)
    (hcx : capA st s x = c) (hk : RngKeyA c) (hp : ptrA c = p)
    (hso : ∀ d, kindA d = kindA c → clsA d = clsA c →
      objects.same_object_as c d = ok true ∧ objects.same_object_as d c = ok true)
    (hf : cdt.is_final_capability_with_cap st s x c = ok true) :
    ∀ y ∈ OS, y ≠ x → RngKeyA (capA st s y) → ptrA (capA st s y) ≠ p := by
  intro y hy hne ky hpy
  subst hcx
  have hcl := hC.cls y hy x hx ky hk (hpy.trans hp.symm)
  obtain ⟨b, hb, kb, cb, hl⟩ := hM.cls_nb hRO hx hy hne hk ky hcl
  have kdb := hK.kind b hb x hx kb hk (ptrA_of_cls cb)
  obtain ⟨s1, s2⟩ := hso _ kdb cb
  have hf' : cdt.is_final_capability st s x = ok true := by rw [is_final_wc]; exact hf
  rcases hl with hl | hl
  · exact Bool.false_ne_true (okinj ((is_final.false_next rfl hl (h0 b hb) rfl s1).symm.trans hf'))
  · exact Bool.false_ne_true (okinj ((is_final.false_prev rfl hl (h0 b hb) rfl s2).symm.trans hf'))

end fin

/-! ## The `Zombie` write -/

/-- **The slot is ready for a `Zombie p t _`** (module docstring). -/
def ZrA (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (s : S) (x p t : U64) : Prop :=
  RngKeyA (capA st s x) ∧ ptrA (capA st s x) = p ∧
    ((∀ y ∈ OS, y ≠ x → RngKeyA (capA st s y) → ptrA (capA st s y) ≠ p) ∨ ∃ n, capA st s x = .Zombie p t n)

section setz
variable {OS : Set U64}

theorem OSKeep.capA {s s' : S} (k : OSKeep st OS s s') {y : U64} (hy : y ∈ OS) : capA st s' y = capA st s y := by
  unfold W7.R.ST.capA; rw [(k y hy).1, (k y hy).2.1]

theorem zr_z {s : S} {x p t n : U64} (hc : obj.Slot.cap st x s = ok (.Zombie p t n)) : ZrA st OS s x p t := by
  have hcx : capA st s x = .Zombie p t n := okinj ((capA_eq s x).symm.trans hc)
  exact ⟨by rw [hcx]; exact RngKeyA.zombie p t n, by rw [hcx, ptrA_zombie], Or.inr ⟨n, hcx⟩⟩

/-- `ZrA` of the unique kind along a step keeping every `OS` slot's words. -/
theorem zr_keep {s s' : S} (k : OSKeep st OS s s') {x p t : U64} (hx : x ∈ OS) (h : ZrA st OS s x p t) :
    ZrA st OS s' x p t := by
  obtain ⟨k0, p0, hu⟩ := h
  refine ⟨by rw [k.capA hx]; exact k0, by rw [k.capA hx]; exact p0, ?_⟩
  rcases hu with hu | ⟨n, e⟩
  · exact Or.inl fun y hy hne ky => by rw [k.capA hy] at ky ⊢; exact hu y hy hne ky
  · exact Or.inr ⟨n, by rw [k.capA hx]; exact e⟩

/-- **A key cap of base `p` replacing the only key cap of base `p`** keeps `MdbS` (class and kind may change). -/
theorem MdbS.setU (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {x0 p w0 w1 : U64} {c : capability.Cap}
    (hx0 : x0 ∈ OS) (hd : capability.Cap.decode w0 w1 = ok c) (hk : RngKeyA c) (hp : ptrA c = p)
    (hk0 : RngKeyA (capA st s x0)) (hp0 : ptrA (capA st s x0) = p)
    (hu : ∀ y ∈ OS, y ≠ x0 → RngKeyA (capA st s y) → ptrA (capA st s y) ≠ p) :
    MdbS st OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm
  have hc0 : capA st s x0 ≠ .Null := fun e => RngKeyA.not_null (e ▸ hk0)
  have hcn : c ≠ .Null := fun e => RngKeyA.not_null (e ▸ hk)
  have e0 : capA st (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) x0 = c := capA_wr2_self hO hx0 hd
  have eo : ∀ y ∈ OS, y ≠ x0 → capA st (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) y = capA st s y :=
    fun y hy hne => capA_wr2_other hO hx0 hy hne
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have nb : ∀ y ∈ OS, y ≠ x0 → RngKeyA (capA st s y) → ∀ d : capability.Cap, ptrA d = p →
      clsA (capA st s y) ≠ clsA d :=
    fun y hy hne ky d hd' e => hu y hy hne ky ((ptrA_of_cls e).trans hd')
  have nbp : ∀ y ∈ OS, y ≠ x0 → RngKeyA (capA st s y) → ptrA (capA st s y) = p → False :=
    fun y hy hne ky e => hu y hy hne ky e
  refine ⟨G, hM.set_cap hO hx0 hd hcn hc0, ⟨fun y hy y' hy' ky ky' hcl => ?_,
    fun ch hch i j k y z y' hi hj hk' hij hjk ky ky' hcl => ?_⟩, ⟨fun x hx y hy kx ky hpe => ?_⟩,
    hN.set_cap hO hx0 hd hcn, ⟨fun x hx y hy kx ky hpe => ?_⟩⟩
  · -- RngOneA64.one
    by_cases e1 : y = x0
    · by_cases e2 : y' = x0
      · subst e1; subst e2
        obtain ⟨ch, hch, hyc⟩ := List.mem_flatten.1 hy
        exact ⟨ch, hch, hyc, hyc⟩
      · subst e1
        rw [e0, eo y' (inOS y' hy') e2] at hcl
        rw [eo y' (inOS y' hy') e2] at ky'
        exact absurd hcl.symm (nb y' (inOS y' hy') e2 ky' c hp)
    · by_cases e2 : y' = x0
      · subst e2
        rw [e0, eo y (inOS y hy) e1] at hcl
        rw [eo y (inOS y hy) e1] at ky
        exact absurd hcl (nb y (inOS y hy) e1 ky c hp)
      · rw [eo y (inOS y hy) e1] at ky hcl
        rw [eo y' (inOS y' hy') e2] at ky' hcl
        exact hRO.one y hy y' hy' ky ky' hcl
  · -- RngOneA64.chunk
    have mem : ∀ {n w}, ch[n]? = some w → w ∈ OS := fun e =>
      inOS _ (List.mem_flatten.2 ⟨ch, hch, List.mem_of_getElem? e⟩)
    have hnd := ch_nodup hM.nodup hch
    have dyz : y ≠ z := fun e => by subst e; have := nd_idx hnd hi hj; omega
    have dzy' : z ≠ y' := fun e => by subst e; have := nd_idx hnd hj hk'; omega
    have dyy' : y ≠ y' := fun e => by subst e; have := nd_idx hnd hi hk'; omega
    by_cases ez : z = x0
    · subst ez
      have ey : y ≠ z := dyz
      rw [eo y (mem hi) ey] at ky hcl
      rw [eo y' (mem hk') (Ne.symm dzy')] at ky' hcl
      obtain ⟨kz, cz⟩ := hRO.chunk ch hch i j k y z y' hi hj hk' hij hjk ky ky' hcl
      exact absurd cz.symm (nb y (mem hi) ey ky _ hp0)
    · rw [eo z (mem hj) ez]
      by_cases ey : y = x0
      · subst ey
        have e2 : y' ≠ y := Ne.symm dyy'
        rw [e0, eo y' (mem hk') e2] at hcl
        rw [eo y' (mem hk') e2] at ky'
        exact absurd hcl.symm (nb y' (mem hk') e2 ky' c hp)
      · by_cases ey' : y' = x0
        · subst ey'
          rw [e0, eo y (mem hi) ey] at hcl
          rw [eo y (mem hi) ey] at ky
          exact absurd hcl (nb y (mem hi) ey ky c hp)
        · rw [eo y (mem hi) ey] at ky hcl ⊢
          rw [eo y' (mem hk') ey'] at ky' hcl
          exact hRO.chunk ch hch i j k y z y' hi hj hk' hij hjk ky ky' hcl
  · -- KindA
    by_cases ex : x = x0
    · by_cases ey : y = x0
      · rw [ex, ey]
      · subst ex
        rw [e0, eo y hy ey] at hpe
        rw [eo y hy ey] at ky
        exact (nbp y hy ey ky (hpe.symm.trans hp)).elim
    · by_cases ey : y = x0
      · subst ey
        rw [e0, eo x hx ex] at hpe
        rw [eo x hx ex] at kx
        exact (nbp x hx ex kx (hpe.trans hp)).elim
      · rw [eo x hx ex] at kx hpe ⊢
        rw [eo y hy ey] at ky hpe ⊢
        exact hK.kind x hx y hy kx ky hpe
  · -- ClsA
    by_cases ex : x = x0
    · by_cases ey : y = x0
      · rw [ex, ey]
      · subst ex
        rw [e0, eo y hy ey] at hpe
        rw [eo y hy ey] at ky
        exact (nbp y hy ey ky (hpe.symm.trans hp)).elim
    · by_cases ey : y = x0
      · subst ey
        rw [e0, eo x hx ex] at hpe
        rw [eo x hx ex] at kx
        exact (nbp x hx ex kx (hpe.trans hp)).elim
      · rw [eo x hx ex] at kx hpe ⊢
        rw [eo y hy ey] at ky hpe ⊢
        exact hC.cls x hx y hy kx ky hpe

/-- **The same `Zombie` rewritten** (another count) keeps `MdbS`. -/
theorem MdbS.setZ (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {x0 p t n n0 w0 w1 : U64} (hx0 : x0 ∈ OS)
    (hd : capability.Cap.decode w0 w1 = ok (.Zombie p t n)) (hz : capA st s x0 = .Zombie p t n0) :
    MdbS st OS (L.wr (L.wr s x0 w0) (wa x0 8#u64) w1) := by
  obtain ⟨G, hM, hRO, hK, hN, hC⟩ := hm
  have inOS : ∀ y ∈ G.flatten, y ∈ OS := fun y hy => ((hM.members y).1 hy).1
  have kk : RngKeyA (.Zombie p t n : capability.Cap) ↔ RngKeyA (capA st s x0) := by
    rw [hz]; exact ⟨fun _ => RngKeyA.zombie _ _ _, fun _ => RngKeyA.zombie _ _ _⟩
  have cl : RngKeyA (capA st s x0) → clsA (.Zombie p t n) = clsA (capA st s x0) := fun _ => by
    rw [hz]; exact clsA_zombie p t n n0
  have pk : RngKeyA (capA st s x0) → ptrA (.Zombie p t n) = ptrA (capA st s x0) ∧
      kindA (.Zombie p t n) = kindA (capA st s x0) := fun _ => by
    rw [hz, ptrA_zombie, ptrA_zombie]; exact ⟨rfl, rfl⟩
  exact ⟨G, hM.set_cap hO hx0 hd (fun e => by cases e) (by rw [hz]; exact fun e => by cases e),
    hRO.set_cap hO inOS hx0 hd kk cl, hK.set_cap hO hx0 hd kk pk, hN.set_cap hO hx0 hd (fun e => by cases e),
    hC.set_cap hO hx0 hd kk cl⟩

/-- **`setz`**: the `Zombie` write into a `ZrA`-ready slot keeps `MdbS`. -/
theorem obj.Slot.set_cap.mdbZ (hO : OSOK T Ω Sg OS) {s : S} (hm : MdbS st OS s) {x p t n : U64} (hx : x ∈ OS)
    (hp : Canon p) (hz : ZrA st OS s x p t) : obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => MdbS st OS s' ⦄ := by
  rw [set_cap_zombie, WP.spec_ok]
  have hd := decode_zw p t n hp
  obtain ⟨k0, p0, hu | ⟨n0, hz0⟩⟩ := hz
  · exact hm.setU hO hx hd (RngKeyA.zombie _ _ _) (ptrA_zombie _ _ _) k0 p0 hu
  · have hw : CapRt.EncWf (capA st s x) := CapRt.decodeF_encWf _ _
    rw [hz0] at hw
    have ht : t.val < 256 := hw.2
    rw [and255 ht] at hd
    exact hm.setZ hO hx hd hz0

end setz

/-! ## `fin` -/

section zq
variable {OS Vc Ub D Fp : Set U64} {kb : U64} {Pt : Set U64} {K : capability.Cap → Prop} {Ty : S → Prop}
variable {A : Type _} {ar : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`delete_one` of an IRQ-node slot holding a notification or `Null` keeps `MdbS`.** -/
theorem cdt.delete_one.mdbS (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    {isl : U64} (hisl : isl ∈ OS) (hN : ∀ c, obj.Slot.cap st isl s = ok c → IrqNt c) (hm : MdbS st OS s) :
    cdt.delete_one st ar s a isl ⦃ r => MdbS st OS r.1 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.delete_one
  obtain ⟨c, hc⟩ := DPF.spec_tot (P0.obj.Slot.cap.p0 st isl s hS)
  rw [hc, bind_ok]
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 hm
  refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s isl c hS) fun fin _ => ?_
  have hl : ZL c := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨n, b0, b1, b2, rfl⟩))
    · exact zl_null
  have hnI : ∀ i, c ≠ .IrqHandler i := by
    rcases hN c hc with ⟨n, b0, b1, b2, rfl⟩ | rfl <;> intro i e <;> cases e
  rw [← fc_eq_fco ar s a fin hnI]
  refine WP.spec_bind (finL hP hO hA hV h hisl hc hl a fin) ?_
  rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨e2, h2, k2⟩
  try simp only at e2 h2 k2
  try dsimp only
  obtain ⟨G, hM, hRO, hK, hN', hC⟩ := hm.keep k2
  refine WP.spec_mono (cdt.empty_slot.mdbO (Pw := fun _ => False) hO hM hRO hK hN' hC hisl (fun _ e => e.elim)
    fun s1 a1 _ => ?_) fun _ ⟨G', h'⟩ => ⟨G', h'⟩
  rw [pcd_null]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)

set_option maxHeartbeats 2000000 in
/-- **A final `IrqHandler` cap's `finalise_cap` keeps `MdbS`** (its IRQ-node slot a notification or `Null`). -/
theorem finalise_cap.irq_mdbS (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S} {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s)
    {irq kb' : U64} (hIO : irqSlotA kb' irq ∈ OS)
    (hN : ∀ c, obj.Slot.cap st (irqSlotA kb' irq) s = ok c → IrqNt c) (hk : L.ksb s = kb') (hm : MdbS st OS s) :
    objects.finalise_cap st ar s a (.IrqHandler irq) true false ⦃ r => r.1 = (.Null, .IrqHandler irq) ∧
      MdbS st OS r.2.1 ⦄ := by
  unfold objects.finalise_cap
  simp only [↓reduceIte]
  unfold interrupt.deleting_irq_handler
  refine WP.spec_bind (Pₘ := fun r : S × A => MdbS st OS r.1) ?_ ?_
  · refine WP.spec_bind (interrupt.irq_slot.val s irq) fun isl e => ?_
    subst e
    rw [hk]
    exact cdt.delete_one.mdbS hP hO hA hV h hIO hN hm
  · rintro ⟨s2, a2⟩ h2
    first
    | (simp only [objects.finalise_cap_object, ↓reduceIte, WP.spec_ok]; exact ⟨rfl, h2⟩)
    | (simp only [objects.finalise_cap_object, ↓reduceIte]; exact (WP.spec_ok _).2 ⟨rfl, h2⟩)
    | (simp [objects.finalise_cap_object, WP.spec_ok]; exact h2)

theorem fin_cnode.f (s : S) (a : A) (p r g b : U64) :
    objects.finalise_cap st ar s a (.CNode p r g b) false false = ok ((.Null, .Null), s, a) := by
  first
  | rfl
  | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]; done)
  | (simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok, Bool.false_eq_true, ↓reduceIte]; rfl)

set_option maxHeartbeats 4000000 in
/-- **`fin`** (module docstring): the finalisation of a `ZQ` cap at the finality just computed keeps `MdbS`, and a
`Zombie` remainder leaves the slot `ZrA`-ready. -/
theorem finXQM (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) (hK : FinKT st ar kb Pt Ty K) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hIO : IrqOK OS D (L.ksb s0))
    (hN : IrqN st (L.ksb s0) s) (hY : Ty s) (hk : L.ksb s = kb) {x : U64} (hx : x ∈ OS)
    {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c)
    (hX : ZQ K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c) (a : A) (fin : Bool)
    (hm : MdbS st OS s) (hf : cdt.is_final_capability_with_cap st s x c = ok fin) :
    objects.finalise_cap st ar s a c fin false ⦃ r => MdbS st OS r.2.1 ∧
      ∀ p t n, r.1.1 = .Zombie p t n → ZrA st OS r.2.1 x p t ⦄ := by
  have hcx : capA st s x = c := okinj ((capA_eq s x).symm.trans hc)
  obtain ⟨G, hM, hRO, hKA, hNL, hC⟩ := hm
  have hm : MdbS st OS s := ⟨G, hM, hRO, hKA, hNL, hC⟩
  rcases hX with ⟨hz, -⟩ | ⟨-, hk'⟩
  swap
  · refine WP.spec_mono (hK s a c fin hY hk hk') ?_
    rintro r ⟨e, w, -⟩
    obtain ⟨-, k2, -, -⟩ := JV.vsr hO hV hR h w
    exact ⟨hm.keep k2, fun p t n e' => by simp [e] at e'⟩
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  rcases hz with ((hl | ⟨p, r, g, b, rfl, -⟩ | ⟨p, t, n, rfl, -⟩) | ⟨p, rfl, hid, hcov⟩ | ⟨v, rfl, hvV⟩) |
    ⟨p, b, rfl, hp, hp0, hpI⟩ | ⟨irq, rfl⟩
  · exact WP.spec_mono (finL hP hO hA hV h hx hc hl a fin) fun r ⟨e, _, k2⟩ =>
      ⟨hm.keep k2, fun p t n e' => by simp [e] at e'⟩
  · cases fin
    · rw [fin_cnode.f, WP.spec_ok]
      exact ⟨hm, fun p' t' n' e' => by simp at e'⟩
    · refine WP.spec_mono (fin_cnode.z ar s a p r g b true) ?_
      rintro q ⟨e1, -, e3⟩
      rw [e1]
      refine ⟨hm, fun p' t' n' e' => ?_⟩
      rcases e3 with e3 | ⟨n, e3, -⟩
      · rw [e3] at e'; cases e'
      · rw [e3] at e'
        simp only [capability.Cap.Zombie.injEq] at e'
        obtain ⟨rfl, rfl, -⟩ := e'
        refine ⟨by rw [hcx]; exact RngKeyA.cnode _ _ _ _, by rw [hcx, ptrA_cnode], Or.inl ?_⟩
        exact final_uniq hO.nz hM hRO hKA hC hx hcx (RngKeyA.cnode _ _ _ _) (ptrA_cnode _ _ _ _)
          (so_cnode p r g b) hf
  · rw [fin_zombie.z, WP.spec_ok]
    refine ⟨hm, fun p' t' n' e' => ?_⟩
    simp only [capability.Cap.Zombie.injEq] at e'
    obtain ⟨rfl, rfl, -⟩ := e'
    exact zr_z hc
  · have e := fin_cap_eq_obj (st := st) (ar := ar) (s := s) (a := a) (c := .Thread p) (fin := fin) (ex := false)
      (by simp)
    have R := fin_thread.rem (st := st) hP s a p fin
    rw [← e] at R
    refine WP.spec_mono (WP.spec_and (finXT hP hO hA hV h hx hc (Or.inr (Or.inl ⟨p, rfl, hid, hcov⟩)) a fin) R) ?_
    rintro r ⟨⟨-, -, k2, -, -⟩, e2⟩
    refine ⟨hm.keep k2, fun p' t n e' => ?_⟩
    rw [e2] at e'
    cases fin
    · simp at e'
    · simp only [↓reduceIte, capability.Cap.Zombie.injEq] at e'
      obtain ⟨rfl, rfl, -⟩ := e'
      refine zr_keep k2 hx ⟨by rw [hcx]; exact RngKeyA.thread _, by rw [hcx, ptrA_thread], Or.inl ?_⟩
      exact final_uniq hO.nz hM hRO hKA hC hx hcx (RngKeyA.thread _) (ptrA_thread _) (so_thread p) hf
  · refine WP.spec_mono (WP.spec_and (finXT (D := D) hP hO hA hV h hx hc (Or.inr (Or.inr ⟨v, rfl, hvV⟩)) a fin)
      (finJV_vcpu hP hO hV h hc hvV a _ fin hc)) ?_
    rintro r ⟨⟨-, -, k2, -, -⟩, e2, -⟩
    exact ⟨hm.keep k2, fun p t n e' => by simp [e2] at e'⟩
  · have hk2 := scpl_of h hc hp hp0 hpI rfl
    refine WP.spec_mono (WP.spec_and (osk_sc hP hO hA h a fin hk2 hc) (finJV_sc hP hO hA hV h hk2 a _ fin hc)) ?_
    rintro r ⟨⟨k2, -, -⟩, e2, -⟩
    exact ⟨hm.keep k2, fun p t n e' => by simp [e2] at e'⟩
  · have hi : irq.val < 5376 := hty.1.2.1 irq rfl
    cases fin
    · rw [finalise_cap.nonfin ar s a (irqH_nonfin irq), WP.spec_ok]
      exact ⟨hm, fun _ _ _ e' => by simp at e'⟩
    · refine WP.spec_mono (finalise_cap.irq_mdbS hP hO hA hV h (hIO.1 irq hi) (hN irq hi) h.ksb hm) ?_
      rintro r ⟨e, m2⟩
      exact ⟨m2, fun p t n e' => by simp [e] at e'⟩

/-! ## The instance and the deletions -/

/-- **The MDB loop field, every obligation discharged** (module docstring). -/
theorem LoopMZ.mdb (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    (hDO : D ⊆ OS) (hDC : DCan D) {s0 : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0))
    (hap : IrqStApart OS (L.ksb s0)) :
    LoopMZ st ar OS D (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0) (XQF st K Vc D Scs Fp Ty (L.ksb s0))
      (ZrA st OS) (MdbS st OS) where
  fin s a x c f hC m hx hc hX hf := finXQM hP hO hA hV hR hK hC hIO hX.2.2 hX.2.1 hC.ksb hx hc hX.1 a f m hf
  zz _ _ _ _ _ hc := zr_z hc
  setz _ _ _ _ _ _ m hx hp hz := obj.Slot.set_cap.mdbZ hO m hx hp hz
  swap _ _ _ _ m hp hy _ hz := cdt.cap_swap_for_delete.mdbS hO hDO hDC m hp hy hz
  pre _ _ h m := sched.preemption_point.mdbS hP hO hV h (by rw [h.ksb]; exact hW) m
  emp _ _ _ _ h m hx hcl := cdt.empty_slot.mdbS hP hO h hap m hx hcl

set_option maxHeartbeats 1000000 in
/-- **`MdbS` through gen 41's exposed deletion, no obligation left** (gen 49's `zqIGTmdb` without `hfin` /
`hsetz`). -/
theorem cdt.delete.zqIGTmdbF (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {x I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hx : x ∈ OS) (hxI : ¬ IslN (L.ksb s0) x)
    (hD : DomQ st K Vc D Scs Fp I Is s) (hX : XQ st K Vc D Scs Fp I Is x s) (hI : L.idleW s = I)
    (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s) (hm : MdbS st OS s) :
    cdt.delete st ar s a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧ Ty r.2.1 ∧
      MdbS st OS r.2.1 ⦄ :=
  cdt.delete.zqIGTMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY
    (LoopMZ.mdb hP hO hA hV hDO hDC hR hK hW hIO hap) hm

set_option maxHeartbeats 1000000 in
/-- **`MdbS` through gen 39's deferred deletion, no obligation left** (gen 49's `zqGmdb` without `hfin` /
`hsetz`). -/
theorem cdt.delete_deferred.zqGmdbF (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : D ⊆ OS) (hDC : DCan D)
    {s0 s : S} (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s0) Pt)
    (hK : FinKT st ar (L.ksb s0) Pt Ty K) (hTy : TyK st (L.ksb s0) Pt Ty)
    (hW : WuApart OS (L.ksb s0)) (hIO : IrqOK OS D (L.ksb s0)) (hap : IrqStApart OS (L.ksb s0))
    {a : A} {y I Is : U64}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hy : y ∈ D) (hD : DomQ st K Vc D Scs Fp I Is s)
    (hI : L.idleW s = I) (hIs : L.mem s (scA I) = Is) (hN : IrqN st (L.ksb s0) s) (hY : Ty s)
    (hm : MdbS st OS s) :
    cdt.delete_deferred st ar s a y ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 r.2.1 ∧
      DomQ st K Vc D Scs Fp I Is r.2.1 ∧ OKD st OS D (L.ksb s0) s r.2.1 ∧ L.idleW r.2.1 = I ∧
      L.mem r.2.1 (scA I) = Is ∧ Ty r.2.1 ∧ MdbS st OS r.2.1 ⦄ :=
  cdt.delete_deferred.zqGMZ (a := a) hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY
    (LoopMZ.mdb hP hO hA hV hDO hDC hR hK hW hIO hap) hm

end zq

end ST
end R
end W7

end

end Fl4ProofsA64.P1
