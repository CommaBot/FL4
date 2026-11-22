/-
P3 (DESIGN.md §9), invariant line G1 (g5i, KENTRY-PLAN g5i): **`PerfGapZ`
proved** — the untyped perform keeps `ZR` (l4v `untyped_ranges_zero` with
`valid_untyped` for data pages; the `invoke_untyped_invs` argument), so
SpecInvUtZS4's `kentry_zr_of` / `kcall_zr_of` hold with no premise
(`kentry_zr`, `kcall_zr`). Spec side only (outside the `JAtZ` cone).

* The zero stores (`zp_storeWord0_out`, `zp_mapStore0_out`, `zp_upto_cover`:
  UtResetSpecJ's lemmas, restated here outside the `JAtZ` cone):
  `delete_objects` of an untyped region zeroes every byte of it
  (`zp_deleteObjects_out`).
* The reset (`zp_reset`): after `delete_objects` of a non-device source's
  region, the state satisfies `ZS U1 D1` with the sets of the decode state
  plus the source's region as a free part (`(base, bits, 0)`): its bytes are
  zero and, by `UtPgR`'s containment clause, every data page meeting it lay
  inside it and was removed. The chunk loop (`clear_memory`, the source's
  free index, preemption points) keeps `ZS U1 D1`. So every outcome has `ZR`,
  the region zero and no data page meeting it.
* The retype (`zp_tail`, from `TailOK` at its start state): the new free
  index, the new pages (inside `[rb, rb + len·2^o)`) and the new untyped
  children `(p, sz, 0)` are added to the canonical sets (`zp_good`): a new
  page misses every other untyped's free part and lies inside every other
  untyped region it meets — `UtDisj` and, for an untyped ancestor of the
  source, SpecInvUt's strengthened `UtDesc` (Nest: the source's region lies
  in its ancestor's); a new child's region is zero and meets no page. Then
  `retype_region`, `init_arch_objects` and the `create_cap` loop keep the
  sets (`zp_yk_retype`, `zp_hu_createCap`).
* **`perfGapZ : PerfGapZ`**, **`kentry_zr`**, **`kcall_zr`** (no premise).
-/
import Fl4Proofs.P3.SpecInvUtZS4
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Zero stores -/

/-- The bytes of the 8-byte word at `q`. -/
def ZB8 (q y : Word) : Prop := ∃ k : Nat, k < 8 ∧ y = q + BitVec.ofNat 64 k

theorem zp_fold_upd0 (q : Word) (v : Int → Word8) (hv : ∀ i, v i = 0) :
    ∀ (l : List Int) (m : Word → Word8),
      l.foldl (fun m i => Function.update m (q + BitVec.ofInt 64 i) (v i)) m =
        fun y => if ∃ i ∈ l, y = q + BitVec.ofInt 64 i then 0 else m y
  | [], m => by funext y; simp
  | i :: l, m => by
    simp only [List.foldl]
    rw [zp_fold_upd0 q v hv l]
    funext y
    have hiff : (∃ j ∈ i :: l, y = q + BitVec.ofInt 64 j) ↔ y = q + BitVec.ofInt 64 i ∨
        ∃ j ∈ l, y = q + BitVec.ofInt 64 j := by
      constructor
      · rintro ⟨j, hj, e⟩
        rcases List.mem_cons.1 hj with rfl | hj
        · exact Or.inl e
        · exact Or.inr ⟨j, hj, e⟩
      · rintro (e | ⟨j, hj, e⟩)
        · exact ⟨i, List.mem_cons.2 (Or.inl rfl), e⟩
        · exact ⟨j, List.mem_cons.2 (Or.inr hj), e⟩
    by_cases h1 : ∃ j ∈ l, y = q + BitVec.ofInt 64 j
    · rw [if_pos h1, if_pos (hiff.2 (Or.inr h1))]
    · rw [if_neg h1]
      by_cases h2 : y = q + BitVec.ofInt 64 i
      · rw [if_pos (hiff.2 (Or.inl h2)), h2, Function.update_self, hv]
      · rw [if_neg (fun h => (hiff.1 h).elim h2 h1), Function.update_of_ne h2]

theorem zp_intUpto_bytes (q y : Word) : (∃ i ∈ intUpto 0 7, y = q + BitVec.ofInt 64 i) ↔ ZB8 q y := by
  have h8 : ((7 : Int) - 0 + 1).toNat = 8 := rfl
  unfold intUpto
  rw [h8]
  constructor
  · rintro ⟨i, hi, e⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hi
    refine ⟨k, List.mem_range.1 hk, ?_⟩
    rw [e]; congr 1; simp
  · rintro ⟨k, hk, e⟩
    refine ⟨(0 : Int) + (k : Int), List.mem_map.2 ⟨k, List.mem_range.2 hk, rfl⟩, ?_⟩
    rw [e]; congr 1; simp

theorem zp_storeWord0_out {q : Word} {ms : MachineState} {x : Unit × MachineState}
    (hx : x ∈ (storeWord q 0 ms).1) :
    x.2 = { ms with underlyingMemory := fun y => if ZB8 q y then 0 else ms.underlyingMemory y } := by
  unfold storeWord at hx
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨-, rfl⟩ := hz
  rw [Set.mem_singleton_iff.1 hx]
  dsimp only
  rw [zp_fold_upd0 q _ (fun i => getD_allZero wordRsplit_zero _)]
  refine congrArg (fun u => ({ ms with underlyingMemory := u } : MachineState)) (funext fun y => ?_)
  by_cases h : ZB8 q y
  · rw [if_pos ((zp_intUpto_bytes q y).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((zp_intUpto_bytes q y).1 h')), if_neg h]

theorem zp_mapStore0_out : ∀ (l : List Word) (ms : MachineState) (x : Unit × MachineState),
    x ∈ (NonDet.mapMx (fun p => storeWord p 0) l ms).1 →
    x.2 = { ms with underlyingMemory := fun y => if ∃ q ∈ l, ZB8 q y then 0 else ms.underlyingMemory y }
  | [], ms, x, hx => by
    rw [Set.mem_singleton_iff.1 hx]
    have e : (fun y => if ∃ q ∈ ([] : List Word), ZB8 q y then (0 : Word8) else ms.underlyingMemory y) =
        ms.underlyingMemory := funext fun y => by simp
    rw [e]
  | a :: l, ms, x, hx => by
    obtain ⟨z, hz, hx⟩ := hx
    rw [zp_mapStore0_out l z.2 x hx, zp_storeWord0_out hz]
    refine congrArg (fun u => ({ ms with underlyingMemory := u } : MachineState)) (funext fun y => ?_)
    show (if ∃ q ∈ l, ZB8 q y then (0 : Word8) else (if ZB8 a y then 0 else ms.underlyingMemory y)) = _
    have hiff : (∃ q ∈ a :: l, ZB8 q y) ↔ ZB8 a y ∨ ∃ q ∈ l, ZB8 q y := by
      constructor
      · rintro ⟨q, hq, e⟩
        rcases List.mem_cons.1 hq with rfl | hq
        · exact Or.inl e
        · exact Or.inr ⟨q, hq, e⟩
      · rintro (e | ⟨q, hq, e⟩)
        · exact ⟨a, List.mem_cons.2 (Or.inl rfl), e⟩
        · exact ⟨q, List.mem_cons.2 (Or.inr hq), e⟩
    by_cases h1 : ∃ q ∈ l, ZB8 q y
    · rw [if_pos h1, if_pos (hiff.2 (Or.inr h1))]
    · rw [if_neg h1]
      by_cases h2 : ZB8 a y
      · rw [if_pos h2, if_pos (hiff.2 (Or.inl h2))]
      · rw [if_neg h2, if_neg (fun h => (hiff.1 h).elim h2 h1)]

/-- **The words of `uptoEnumStep a (a + 8) c` cover `[a, c]`** (`c = a + n - 1`, no wrap). -/
theorem zp_upto_cover {a c : Word} {n : Nat} (hn0 : 0 < n) (hfit : a.toNat + n ≤ 2 ^ 64)
    (hc : c.toNat = a.toNat + n - 1) (y : Word) (h1 : a.toNat ≤ y.toNat) (h2 : y.toNat < a.toNat + n) :
    ∃ q ∈ uptoEnumStep a (a + BitVec.ofNat 64 wordSize) c, ZB8 q y := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by norm_num
  have hca : ¬ c < a := by rw [BitVec.lt_def, hc]; omega
  have hb : a + BitVec.ofNat 64 wordSize - a = 8#64 := by
    rw [add_sub_cancel_left]; rfl
  have hd : ((c - a) / 8#64).toNat = (n - 1) / 8 := by
    rw [BitVec.toNat_udiv, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, hc]; omega), hc]
    have : (8#64 : Word).toNat = 8 := rfl
    rw [this]; congr 1; omega
  unfold uptoEnumStep uptoEnum
  rw [if_neg hca, hb, hd]
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0]
  have hy := y.isLt
  set d := y.toNat - a.toNat with hd'
  refine ⟨a + BitVec.ofNat 64 (d / 8) * 8#64, List.mem_map.2 ⟨BitVec.ofNat 64 (d / 8),
    List.mem_map.2 ⟨d / 8, by rw [List.mem_range'_1]; omega, rfl⟩, rfl⟩, d % 8, Nat.mod_lt _ (by decide), ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h64, Nat.reduceMod]
  rw [h64] at hfit hy
  omega

theorem zp_dmo_mem {α : Type} {mop : NonDet MachineState α} {σ : State Unit} {z : α × State Unit}
    (hz : z ∈ (doMachineOp (Z := Unit) mop σ).1) :
    ∃ ms', (z.1, ms') ∈ (mop σ.machineState).1 ∧ z.2 = { σ with machineState := ms' } := by
  unfold doMachineOp at hz
  obtain ⟨a, ha, hz⟩ := hz
  rw [Set.mem_singleton_iff.1 ha] at hz
  obtain ⟨⟨⟨r, ms'⟩, s'⟩, ⟨hb1, hb2⟩, hz⟩ := hz
  simp only at hb2
  subst hb2
  obtain ⟨c, hc, hz⟩ := hz
  rw [Set.mem_singleton_iff.1 hc] at hz
  rw [Set.mem_singleton_iff.1 hz]
  exact ⟨ms', hb1, rfl⟩

theorem zp_toNat_add_sub1 {a : Word} {n : Nat} (hn0 : 0 < n) (hfit : a.toNat + n ≤ 2 ^ 64) (hn : n < 2 ^ 64) :
    (a + BitVec.ofNat 64 n - 1).toNat = a.toNat + n - 1 := by
  rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  have h1 : (1 : Word).toNat = 1 := rfl
  rw [h1]
  rcases Nat.lt_or_ge (a.toNat + n) (2 ^ 64) with h | h
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : a.toNat + n = 2 ^ 64 := by omega
    rw [this, Nat.mod_self]; omega

/-- **`delete_objects` of an aligned region** zeroes its bytes, writes only zeros and removes
exactly the objects of `delR`. -/
theorem zp_deleteObjects_out {pu : Word} {sz : Nat} (hsz : sz < 64) (hfit : pu.toNat + 2 ^ sz ≤ 2 ^ 64)
    {σ : State Unit} {y : Unit × State Unit} (hy : y ∈ (deleteObjects (Z := Unit) pu sz σ).1) :
    (∀ x, y.2.kheap x = if x ∈ delR pu sz then none else σ.kheap x) ∧
    (∀ a : Word, y.2.machineState.underlyingMemory a = 0 ∨
      y.2.machineState.underlyingMemory a = σ.machineState.underlyingMemory a) ∧
    (∀ a : Word, pu.toNat ≤ a.toNat → a.toNat < pu.toNat + 2 ^ sz → y.2.machineState.underlyingMemory a = 0) := by
  unfold deleteObjects at hy
  obtain ⟨z, hz, hy⟩ := hy
  rw [Set.mem_singleton_iff.1 hy]
  obtain ⟨ms', hms, e⟩ := zp_dmo_mem hz
  rw [e]
  unfold freeMemory at hms
  have h1 := zp_mapStore0_out _ _ _ hms
  simp only at h1
  have hlt : 2 ^ sz < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) hsz
  have hc : (pu + 2 ^ sz - 1).toNat = pu.toNat + 2 ^ sz - 1 := by
    rw [pow2_word' hsz]; exact zp_toNat_add_sub1 (Nat.two_pow_pos _) hfit hlt
  refine ⟨fun x => rfl, fun a => ?_, fun a ha1 ha2 => ?_⟩
  · show ms'.underlyingMemory a = 0 ∨ ms'.underlyingMemory a = _
    rw [h1]; dsimp only; split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · show ms'.underlyingMemory a = 0
    rw [h1]; dsimp only
    rw [if_pos (zp_upto_cover (Nat.two_pow_pos _) hfit hc a ha1 ha2)]

/-! ## The set form -/

theorem zp_zr {U : UtSet} {D : PgSet} {σ : State Unit} (h : ZS U D σ) : ZR σ := ⟨U, D, h⟩

theorem zp_ik {U : UtSet} {D : PgSet} {α : Type} {m : NonDet (State Unit) α} (hG : GoodZ U D)
    (hH : IKH (HU U) m) (hY : YK D (FU U) m) : SInv.IK (ZS U D) m :=
  fun σ h x hx => ⟨hG, hH σ h.2.1 x hx, hY σ h.2.2 x hx⟩

theorem zp_mapMx_mem {P : State Unit → Prop} {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ xs : List α, (∀ a ∈ xs, SInv.IK P (g a)) → SInv.IK P (NonDet.mapMx g xs)
  | [], _ => SInv.ik_pure' _
  | a :: xs, h => SInv.ik_bind' (h a (by simp)) fun _ => zp_mapMx_mem xs fun b hb => h b (by simp [hb])

theorem zp_disj {U : UtSet} {D : PgSet} (hG : GoodZ U D) : DisjF D (FU U) := by
  rintro o sz ho a ha ⟨b, n, f, hU, hfa⟩
  exact (hG b n f hU o sz ho).1 a ha hfa

theorem zp_yk_retype {D : PgSet} {F : Set Nat} (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef)
    (n oB : Nat) (ty : ApiObjectType) (dev : Bool)
    (hD : ∀ q ∈ retPtrs ptr n (bA ty oB), ty ≠ .untyped → ∀ d psz,
      defaultObject ty dev oB d = .archObj (.dataPage false psz) → D q psz) :
    YK D F (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy
  rcases (SInvU.retypeRegionWith_out hy).2 with e | ⟨hty, e⟩
  · rw [e]; exact h
  · rw [e]
    refine ⟨h.1, fun o sz ho => ?_, h.2.2⟩
    simp only [SInvU.retKh] at ho
    split_ifs at ho with hm
    · exact hD o hm hty _ _ (Option.some.inj ho)
    · exact h.2.1 o sz ho

theorem zp_dflt_pg {ty : ApiObjectType} (hty : ty ≠ .untyped) {dev : Bool} {sz : Nat} {d : Domain}
    {psz : VMPageSize} (h : defaultObject ty dev sz d = .archObj (.dataPage false psz)) :
    dev = false ∧ fl4ObjBitsApi ty sz = pageBitsForSize psz := by
  cases ty with
  | untyped => exact absurd rfl hty
  | archObject a =>
    cases a <;> simp [defaultObject, defaultArchObject] at h <;> obtain ⟨rfl, rfl⟩ := h <;> exact ⟨rfl, rfl⟩
  | _ => simp [defaultObject] at h

theorem zp_ret_in {rb q : ObjRef} {L o : Nat} (hq : q ∈ retPtrs rb L o) (hfit : rb.toNat + L * 2 ^ o ≤ 2 ^ 64) :
    rb.toNat ≤ q.toNat ∧ q.toNat + 2 ^ o ≤ rb.toNat + L * 2 ^ o := by
  obtain ⟨k, hk, rfl⟩ := retPtrs_mem hq
  have hpo := Nat.two_pow_pos o
  have m2 : (k + 1) * 2 ^ o ≤ L * 2 ^ o := Nat.mul_le_mul_right _ hk
  have e2 : (k + 1) * 2 ^ o = k * 2 ^ o + 2 ^ o := Nat.succ_mul _ _
  rw [ptrAdd_toNat (by omega)]; omega

theorem zp_hu_createCap {U : UtSet} (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev : Bool) (d : CslotPtr)
    (p : ObjRef) (h : UtIn U (defaultCap ty p sz dev)) : IKH (HU U) (createCap (Z := Unit) ty sz src dev (d, p)) := by
  unfold createCap; hv_auto

theorem zp_hu_clear {U : UtSet} (p : Word) (n : Nat) : IKH (HU U) (doMachineOp (Z := Unit) (clearMemory p n)) :=
  WLH.msk _ (mt_clearMemory _ _)

theorem zp_hu_pp {U : UtSet} : IKHE (HU U) (preemptionPoint (Z := Unit)) := by hv_auto

theorem zp_hu_apr {U : UtSet} (d : Bool) (n : Nat) : IKH (HU U) (archPostResetUntyped (Z := Unit) d n) := by
  unfold archPostResetUntyped; exact ik_pure _

/-! ## The retype -/

/-- **What the retype needs at its start state** `τ` (the source `s`, its region
`(base, bits)`, the window `[rb, rb + L·2^o)`). -/
structure TailOK (τ : State Unit) (s : CslotPtr) (dev : Bool) (base rb : ObjRef) (bits L o : Nat) : Prop where
  cap : ∃ f, SInvU.capAt τ s = some (.untypedCap dev base bits f)
  b64 : bits < 64
  fit : base.toNat + 2 ^ bits ≤ 2 ^ 64
  lo : base.toNat ≤ rb.toNat
  hi : rb.toNat + L * 2 ^ o ≤ base.toNat + 2 ^ bits
  mem : dev = false → ∀ a : Word, rb.toNat ≤ a.toNat → a.toNat < base.toNat + 2 ^ bits →
    τ.machineState.underlyingMemory a = 0
  pg : dev = false → ∀ q psz, τ.kheap q = some (.archObj (.dataPage false psz)) → ∀ a ∈ pgB q psz,
    ¬ (rb.toNat ≤ a ∧ a < base.toNat + 2 ^ bits)
  oth : dev = false → ∀ sl b n f, sl ≠ s → SInvU.capAt τ sl = some (.untypedCap false b n f) →
    (∀ a, rb.toNat ≤ a → a < base.toNat + 2 ^ bits → a ∉ fr b n f) ∧
    ((∃ a, rb.toNat ≤ a ∧ a < base.toNat + 2 ^ bits ∧ a ∈ rg b n) → ∀ a, a ∈ rg base bits → a ∈ rg b n)

/-- The caps after the free-index write: the source's new cap, the rest of `τ`'s. -/
def CapsAfter (τ σ3 : State Unit) (s : CslotPtr) (nc : Cap) : Prop :=
  ∀ p cref a, capOpt (σ3.kheap p) cref = some a →
    (p = s.1 ∧ cref = s.2 ∧ a = nc) ∨ ((p ≠ s.1 ∨ cref ≠ s.2) ∧ capOpt (τ.kheap p) cref = some a)

/-- The untyped children of an untyped retype. -/
def Kids (dev : Bool) (ty : ApiObjectType) (sz : Nat) (ps : List ObjRef) : UtSet :=
  fun b n f => dev = false ∧ ty = .untyped ∧ n = sz ∧ f = 0 ∧ b ∈ ps

/-- The new data pages of a retype. -/
def NewPg (dev : Bool) (ty : ApiObjectType) (sz : Nat) (ps : List ObjRef) : PgSet :=
  fun q psz => ty ≠ .untyped ∧ q ∈ ps ∧ ∃ d, defaultObject ty dev sz d = .archObj (.dataPage false psz)

set_option maxHeartbeats 4000000 in
/-- **The sets after the free-index write are good** (module docstring). -/
theorem zp_good {τ σ3 : State Unit} {s : CslotPtr} {dev : Bool} {base rb : ObjRef} {ty : ApiObjectType}
    {sz bits L : Nat} (hR : UtPgR τ) (hT : TailOK τ s dev base rb bits L (fl4ObjBitsApi ty sz))
    (hC : CapsAfter τ σ3 s (.untypedCap dev base bits (rb.toNat + L * 2 ^ fl4ObjBitsApi ty sz - base.toNat))) :
    GoodZ (fun b n f => HasU σ3 b n f ∨ Kids dev ty sz (retPtrs rb L (fl4ObjBitsApi ty sz)) b n f)
      (fun q psz => PgOf τ q psz ∨ NewPg dev ty sz (retPtrs rb L (fl4ObjBitsApi ty sz)) q psz) := by
  obtain ⟨f0, hc0⟩ := hT.cap
  have hfitR : rb.toNat + L * 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64 := le_trans hT.hi hT.fit
  have hlo := hT.lo
  have hhi := hT.hi
  -- a new page lies in the window
  have hnew : ∀ q psz, NewPg dev ty sz (retPtrs rb L (fl4ObjBitsApi ty sz)) q psz → dev = false ∧
      ∀ a ∈ pgB q psz, rb.toNat ≤ a ∧ a < rb.toNat + L * 2 ^ fl4ObjBitsApi ty sz := by
    rintro q psz ⟨hty, hq, d, hd⟩
    obtain ⟨hdev, hpb⟩ := zp_dflt_pg hty hd
    obtain ⟨h1, h2⟩ := zp_ret_in hq hfitR
    refine ⟨hdev, fun a ha => ?_⟩
    simp only [pgB, Set.mem_setOf_eq] at ha
    rw [← hpb] at ha
    omega
  intro b n f hU q psz hq
  rcases hU with ⟨p, cref, hcp⟩ | ⟨hdev, hty, hn, hf, hb⟩
  · rcases hC p cref _ hcp with ⟨rfl, rfl, e⟩ | ⟨hne, hcτ⟩
    · -- the source with its new free index
      simp only [Cap.untypedCap.injEq] at e
      obtain ⟨hd, hb, hn, hf⟩ := e
      subst hd
      rw [hb, hn, hf]
      rcases hq with hq | hq
      · have hcs : capOpt (τ.kheap s.1) s.2 = some (.untypedCap false base bits f0) := by
          rw [← capAt_capOpt]; exact hc0
        refine ⟨fun a ha hfa => hT.pg rfl q psz hq a ha ⟨?_, hfa.2⟩, (hR _ _ _ _ _ hcs q psz hq).2⟩
        have := hfa.1; omega
      · obtain ⟨-, hin⟩ := hnew q psz hq
        refine ⟨fun a ha hfa => ?_, fun _ a ha => ?_⟩
        · have := hin a ha; have := hfa.1; omega
        · have := hin a ha; exact ⟨by omega, by omega⟩
    · rcases hq with hq | hq
      · exact hR p cref b n f hcτ q psz hq
      · obtain ⟨hdev, hin⟩ := hnew q psz hq
        have hcs : SInvU.capAt τ (p, cref) = some (.untypedCap false b n f) := by
          rw [capAt_capOpt]; exact hcτ
        have hsl : (p, cref) ≠ s := by
          intro e; subst e; rcases hne with h | h <;> exact h rfl
        obtain ⟨o1, o2⟩ := hT.oth hdev (p, cref) b n f hsl hcs
        refine ⟨fun a ha hfa => o1 a (hin a ha).1 (by have := (hin a ha).2; omega) hfa,
          fun ⟨a, ha, har⟩ a' ha' => ?_⟩
        have h2 := o2 ⟨a, (hin a ha).1, by have := (hin a ha).2; omega, har⟩
        exact h2 a' ⟨by have := (hin a' ha').1; omega, by have := (hin a' ha').2; omega⟩
  · -- an untyped child: no new page, the old pages miss the window
    have hq' : PgOf τ q psz := by
      rcases hq with hq | ⟨hne, -⟩
      · exact hq
      · exact absurd hty hne
    rw [hn, hf]
    have hin := zp_ret_in hb hfitR
    have hsz : fl4ObjBitsApi ty sz = sz := by subst hty; rfl
    rw [hsz] at hin hhi
    have hmiss : ∀ a ∈ pgB q psz, a ∉ rg b sz := by
      intro a ha har
      exact hT.pg hdev q psz hq' a ha ⟨by have := har.1; omega, by have := har.2; omega⟩
    refine ⟨fun a ha hfa => hmiss a ha ⟨by have := hfa.1; omega, hfa.2⟩, fun ⟨a, ha, har⟩ => ?_⟩
    exact absurd har (hmiss a ha)

set_option maxHeartbeats 4000000 in
/-- **The retype keeps `ZR`** from `TailOK` at its start state. -/
theorem zp_tail {τ : State Unit} (hZ : ZR τ) {s : CslotPtr} {base rb : ObjRef} {ty : ApiObjectType} {sz bits : Nat}
    {slots : List CslotPtr} {dev : Bool} (hT : TailOK τ s dev base rb bits slots.length (fl4ObjBitsApi ty sz)) :
    ∀ y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi (.retype s false base rb ty sz slots dev)) τ).1,
      ZR y.2 := by
  intro y hy
  have hS := zs_canon hZ
  obtain ⟨-, hR0⟩ := zr_iff.1 hZ
  obtain ⟨f0, hc0⟩ := hT.cap
  have hfi : unat (rb + (BitVec.ofNat 64 slots.length <<< fl4ObjBitsApi ty sz) - base) =
      rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat :=
    fi_new hT.b64 hT.lo hT.hi hT.fit
  simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte] at hy
  replace hy := run_returnOk_bind_mem hy
  obtain ⟨x, hx, e⟩ := run_liftE_mem hy
  rw [e]
  obtain ⟨x1, hx1, hx⟩ := hx
  obtain ⟨e1, hc1⟩ := getCap_capAt hx1
  obtain ⟨cap, s1⟩ := x1
  simp only at e1 hc1; subst s1
  rw [hc0] at hc1; cases hc1
  obtain ⟨x2, hx2, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx2
  obtain ⟨x3, hx3, hx⟩ := hx; obtain rfl := Set.mem_singleton_iff.1 hx3
  obtain ⟨x4, hx4, hx⟩ := hx
  simp only [bitsOf] at hx4
  rw [hfi] at hx4
  -- the memory half before the write, with the window
  let F0 : Set Nat := {a | a ∈ FU (HasU τ) ∨
    (dev = false ∧ rb.toNat ≤ a ∧ a < base.toNat + 2 ^ bits)}
  have hY0 : YP (PgOf τ) F0 τ := by
    refine ⟨fun o psz ho a ha hF => ?_, fun _ _ h => h, fun a hF => ?_⟩
    · rcases hF with hF | ⟨hdev, h1, h2⟩
      · exact hS.2.2.1 o psz ho a ha hF
      · exact hT.pg hdev o psz ho a ha ⟨h1, h2⟩
    · rcases hF with hF | ⟨hdev, h1, h2⟩
      · exact hS.2.2.2.2 a hF
      · exact hT.mem hdev a h1 h2
  have hY4 : YP (PgOf τ) F0 x4.2 := yk_setCap _ _ τ hY0 x4 hx4
  have hC : CapsAfter τ x4.2 s (.untypedCap dev base bits
      (rb.toNat + slots.length * 2 ^ fl4ObjBitsApi ty sz - base.toNat)) :=
    (vih_setCap_out (o := s.1) (r := s.2) hx4).2
  have hG := zp_good (L := slots.length) hR0 hT hC
  -- the state after the write satisfies `ZS` at the new sets
  have hZ4 : ZS (fun b n f => HasU x4.2 b n f ∨ Kids dev ty sz (retPtrs rb slots.length (fl4ObjBitsApi ty sz)) b n f)
      (fun q psz => PgOf τ q psz ∨ NewPg dev ty sz (retPtrs rb slots.length (fl4ObjBitsApi ty sz)) q psz) x4.2 := by
    refine ⟨hG, fun p cref c hc b n f e => ?_, zp_disj hG, fun q psz hq => Or.inl (hY4.2.1 q psz hq),
      fun a ha => hY4.2.2 a ?_⟩
    · subst e; exact ⟨f, Or.inl ⟨p, cref, hc⟩, Or.inl le_rfl⟩
    · obtain ⟨b, n, f, hU, hfa⟩ := ha
      rcases hU with ⟨p, cref, hcp⟩ | ⟨hdev, hty, hn, hf, hb⟩
      · rcases hC p cref _ hcp with ⟨-, -, e⟩ | ⟨-, hcτ⟩
        · simp only [Cap.untypedCap.injEq] at e
          obtain ⟨hd, hb, hn, hf⟩ := e
          rw [hb, hn, hf] at hfa
          have := hfa.1; have := hfa.2; have := hT.lo
          exact Or.inr ⟨hd.symm, by omega, by omega⟩
        · exact Or.inl ⟨b, n, f, ⟨p, cref, hcτ⟩, hfa⟩
      · rw [hn, hf] at hfa
        have hin := zp_ret_in hb (le_trans hT.hi hT.fit)
        have hsz : fl4ObjBitsApi ty sz = sz := by subst hty; rfl
        have hhi := hT.hi
        rw [hsz] at hin hhi
        have := hfa.1; have := hfa.2
        exact Or.inr ⟨hdev, by omega, by omega⟩
  -- `retype_region`, `init_arch_objects`, the `create_cap` loop
  obtain ⟨x5, hx5, hx⟩ := hx
  have hp5 := (SInvU.retypeRegionWith_out hx5).1
  have hZ5 := zp_ik hG (hu_retypeRegionWith _ _ _ _ _ _)
    (zp_yk_retype _ _ _ _ _ _ fun q hq hty d psz hd => Or.inr ⟨hty, hq, d, hd⟩) x4.2 hZ4 x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hZ6 := zp_ik hG (by hv_auto) (yk_initArchObjects _ _ _ _ _ _) x5.2 hZ5 x6 hx6
  rw [hp5] at hx
  refine zp_zr ((zp_mapMx_mem _ fun dp hdp => ?_) x6.2 hZ6 x hx)
  obtain ⟨d, p⟩ := dp
  have hp : p ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz) := (List.of_mem_zip hdp).2
  have hut : UtIn (fun b n f => HasU x4.2 b n f ∨ Kids dev ty sz (retPtrs rb slots.length (fl4ObjBitsApi ty sz)) b n f)
      (defaultCap ty p sz dev) := by
    intro b n f e
    by_cases hty : ty = .untyped
    · subst hty
      simp only [defaultCap, Cap.untypedCap.injEq] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      exact ⟨0, Or.inr ⟨rfl, rfl, rfl, rfl, hp⟩, Or.inl le_rfl⟩
    · exact absurd e (defaultCap_nonUt hty p sz dev false b n f)
  exact zp_ik hG (zp_hu_createCap _ _ _ _ _ _ hut) (yk_createCap _ _ _ _ _)

/-! ## The reset -/

/-- The sets after `delete_objects`: the decode state's caps and the source's region as a free part. -/
def ResU (σ : State Unit) (dev : Bool) (base : ObjRef) (bits : Nat) : UtSet :=
  fun b n f => HasU σ b n f ∨ (dev = false ∧ b = base ∧ n = bits ∧ f = 0)

theorem zp_utIn_res {σ : State Unit} {dev : Bool} {base : ObjRef} {bits : Nat} (f : Nat) :
    UtIn (ResU σ dev base bits) (.untypedCap dev base bits f) := by
  intro b n f' e
  simp only [Cap.untypedCap.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact ⟨0, Or.inr ⟨rfl, rfl, rfl, rfl⟩, Or.inl (Nat.zero_le _)⟩

set_option maxHeartbeats 4000000 in
/-- **`reset_untyped_cap` keeps `ZR`**, and a non-device source's region is then zero
and meets no data page (every outcome, finished or preempted). -/
theorem zp_reset {σ : State Unit} (hZ : ZR σ) {s : CslotPtr} {dev : Bool} {base : ObjRef} {bits fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev base bits fi)) (hb : bits < 64)
    (hfit : base.toNat + 2 ^ bits ≤ 2 ^ 64) :
    ∀ z ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, ZR z.2 ∧
      (dev = false → (∀ a : Word, a.toNat ∈ rg base bits → z.2.machineState.underlyingMemory a = 0) ∧
        ∀ q psz, z.2.kheap q = some (.archObj (.dataPage false psz)) → ∀ a ∈ pgB q psz, a ∉ rg base bits) := by
  have hS := zs_canon hZ
  obtain ⟨hZ0, hR0⟩ := zr_iff.1 hZ
  intro z hz
  unfold resetUntypedCap at hz
  obtain ⟨x, hx, hz⟩ := run_liftE_bind_mem hz
  obtain ⟨cap, s0⟩ := x
  obtain ⟨hs, hcx⟩ := getCap_capAt hx
  simp only at hs hcx; rw [hs] at hz
  rw [hc] at hcx; cases hcx
  replace hz := run_returnOk_bind_mem hz
  replace hz := run_returnOk_bind_mem hz
  dsimp only at hz
  by_cases h0 : fi = 0
  · rw [if_pos (show freeIndexOf (Cap.untypedCap dev base bits fi) = 0 from h0)] at hz
    obtain rfl := Set.mem_singleton_iff.1 hz
    subst h0
    refine ⟨hZ, fun hdev => ?_⟩
    subst hdev
    have hcs : capOpt (σ.kheap s.1) s.2 = some (.untypedCap false base bits 0) := by
      rw [← capAt_capOpt]; exact hc
    refine ⟨fun a ha => hZ0 _ _ _ _ _ hcs a (by have := ha.1; omega) ha.2, fun q psz hq a ha har => ?_⟩
    exact (hR0 _ _ _ _ _ hcs q psz hq).1 a ha ⟨by have := har.1; omega, har.2⟩
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev base bits fi) = 0 from h0)] at hz
    obtain ⟨z1, hz1, hz⟩ := run_liftE_bind_mem hz
    simp only [bitsOf, objRefOf] at hz1
    obtain ⟨hk1, hm1, hr1⟩ := zp_deleteObjects_out hb hfit hz1
    have hpd := mem_delR_iff hb hfit
    -- the sets after `delete_objects`
    have hG1 : GoodZ (ResU σ dev base bits) (PgOf z1.2) := by
      intro b n f hU q psz hq
      have hq' : z1.2.kheap q = some (.archObj (.dataPage false psz)) := hq
      rw [hk1 q] at hq'
      by_cases hqd : q ∈ delR base bits
      · rw [if_pos hqd] at hq'; cases hq'
      rw [if_neg hqd] at hq'
      have hqσ : PgOf σ q psz := hq'
      rcases hU with ⟨p, cref, hcp⟩ | ⟨hdev, hb', hn', hf'⟩
      · exact hR0 p cref b n f hcp q psz hqσ
      · subst hdev
        rw [hb', hn', hf']
        have hcs : capOpt (σ.kheap s.1) s.2 = some (.untypedCap false base bits fi) := by
          rw [← capAt_capOpt]; exact hc
        have hno : ∀ a ∈ pgB q psz, a ∉ rg base bits := by
          intro a ha har
          have hin := (hR0 _ _ _ _ _ hcs q psz hqσ).2 ⟨a, ha, har⟩ q.toNat ⟨le_refl _, by
            have := Nat.two_pow_pos (pageBitsForSize psz); omega⟩
          exact hqd ((hpd q).2 hin)
        refine ⟨fun a ha hfa => hno a ha ⟨by have := hfa.1; omega, hfa.2⟩, fun ⟨a, ha, har⟩ => ?_⟩
        exact absurd har (hno a ha)
    have hZ1 : ZS (ResU σ dev base bits) (PgOf z1.2) z1.2 := by
      refine ⟨hG1, fun p cref c hc' => ?_, zp_disj hG1, fun _ _ h => h, fun a ha => ?_⟩
      · intro b n f e
        obtain ⟨f1, hU, hf⟩ := hu_deleteObjects base bits σ hS.2.1 z1 hz1 p cref c hc' b n f e
        exact ⟨f1, Or.inl hU, hf⟩
      · obtain ⟨b, n, f, hU, hfa⟩ := ha
        rcases hU with hU | ⟨-, rfl, rfl, rfl⟩
        · rcases hm1 a with e | e
          · exact e
          · rw [e]; exact hS.2.2.2.2 a ⟨b, n, f, hU, hfa⟩
        · exact hr1 a (by have := hfa.1; omega) hfa.2
    -- the rest of the reset keeps the sets
    have hrest : ZS (ResU σ dev base bits) (PgOf z1.2) z.2 := by
      refine (?_ : SInv.IKE (ZS (ResU σ dev base bits) (PgOf z1.2)) _) z1.2 hZ1 z hz
      try simp only [isDeviceUntypedCap, bitsOf, objRefOf, freeIndexOf]
      repeat' (first
        | (exact zp_ik hG1 (hu_setCap _ _ (zp_utIn_res _)) (yk_setCap _ _))
        | (exact zp_ik hG1 (zp_hu_clear _ _) (yk_dmo (mz_clearMemory _ _)))
        | (exact zp_ik hG1 zp_hu_pp yk_preemptionPoint)
        | (exact zp_ik hG1 (zp_hu_apr _ _) (yk_archPostResetUntyped _ _))
        | (refine ike_mapMEx_mem _ fun _ _ => ?_)
        | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE))
    refine ⟨zp_zr hrest, fun hdev => ⟨fun a ha => hrest.2.2.2.2 a ⟨base, bits, 0, Or.inr ⟨hdev, rfl, rfl, rfl⟩,
      by have := ha.1; have := ha.2; exact ⟨by omega, by omega⟩⟩, fun q psz hq a ha har => ?_⟩⟩
    have hq1 := hrest.2.2.2.1 q psz hq
    exact (hG1 base bits 0 (Or.inr ⟨hdev, rfl, rfl, rfl⟩) q psz hq1).1 a ha
      ⟨by have := har.1; omega, har.2⟩

/-! ## `PerfGapZ` -/

set_option maxHeartbeats 4000000 in
/-- **The untyped perform keeps `ZR`** (SpecInvUtZS2's obligation, proved). -/
theorem perfGapZ : PerfGapZ := by
  intro N ui σ hP hN hZ hD y hy
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) (.invokeUntyped ui) :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
  have hok : UtGapOK (uV σ) ui := hf
  obtain ⟨h1, -, -⟩ := hok
  have hI : UtInv' σ := hP.1.1
  obtain ⟨hZ0, hR0⟩ := zr_iff.1 hZ
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hok' := h1
  obtain ⟨bits, fi, hc0, -, -, -, -, hr⟩ := hok'
  have hc' : SInvU.capAt σ s = some (.untypedCap dev base bits fi) := hc0
  obtain ⟨bits', fi', hc'', hfit, h1r, -, h3r⟩ := utRet_region hI.1.2.1 (utRetOK_of_V h1)
  rw [hc'] at hc''; cases hc''
  obtain ⟨hbits, -⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc'
  cases reset
  · -- no reset: the window lies in the source's free part
    simp only [Bool.false_eq_true, ↓reduceIte] at h1r
    refine zp_tail hZ ⟨⟨fi, hc'⟩, hbits, hfit, by omega, h3r, fun hdev a ha1 ha2 => ?_,
      fun hdev q psz hq a ha har => ?_, fun hdev sl' b n f hne hcs => ⟨fun a ha1 ha2 hfa => ?_, fun ⟨a, ha1, ha2, har⟩ => ?_⟩⟩ y hy
    · subst hdev
      have hcs : capOpt (σ.kheap s.1) s.2 = some (.untypedCap false base bits fi) := by
        rw [← capAt_capOpt]; exact hc'
      exact hZ0 _ _ _ _ _ hcs a (by omega) ha2
    · subst hdev
      have hcs : capOpt (σ.kheap s.1) s.2 = some (.untypedCap false base bits fi) := by
        rw [← capAt_capOpt]; exact hc'
      exact (hR0 _ _ _ _ _ hcs q psz hq).1 a ha ⟨by omega, har.2⟩
    · exact hI.1.2.2.1 s sl' dev base bits fi false b n f (Ne.symm hne) hc' hcs a ⟨by omega, ha2⟩ hfa
    · rcases hI.1.2.2.2.1 s sl' dev base bits fi false b n f (Ne.symm hne) hc' hcs
        ⟨a, ⟨by omega, ha2⟩, har⟩ with ⟨-, hr', -⟩ | ⟨-, -, hin⟩
      · exact (hr' a har ⟨by omega, ha2⟩).elim
      · exact hin
  · -- reset
    have hk : ∀ c, σ.cdt c ≠ some s := hr rfl
    simp only [↓reduceIte] at h1r
    simp only [invokeUntypedWith, NonDetE.whenE, ↓reduceIte] at hy
    rw [ExceptT.run_bind] at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hRz := nv_reset hP hc' hk z hz
    have hPz := reset_utInv' hI (detypeOK_of hP.1) hc' hk z hz
    obtain ⟨hZz, hMz⟩ := zp_reset hZ hc' hbits hfit z hz
    obtain ⟨r, s2⟩ := z
    cases r with
    | error e =>
      first
        | (obtain rfl := Set.mem_singleton_iff.1 hy; exact hZz)
        | (dsimp only at hy; obtain rfl := Set.mem_singleton_iff.1 hy; exact hZz)
    | ok u => ?_
    try dsimp only at hy
    have hy' : y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi
        (.retype s false base rb ty sz slots dev)) s2).1 := by
      simp only [invokeUntypedWith, NonDetE.whenE, Bool.false_eq_true, ↓reduceIte]
      exact run_returnOk_bind_mem' hy
    obtain ⟨-, ⟨f2, hf2⟩, -, -, -⟩ := hRz
    obtain ⟨-, hRS⟩ := hPz
    change RSV s dev base bits σ.cdt (uV s2) at hRS
    obtain ⟨-, -, -, -, hR5, -, -⟩ := hRS
    refine zp_tail hZz ⟨⟨f2, hf2⟩, hbits, hfit, by omega, h3r, fun hdev a ha1 ha2 => ?_,
      fun hdev q psz hq a ha har => ?_, fun hdev sl' b n f hne hcs => ⟨fun a ha1 ha2 hfa => ?_, fun ⟨a, ha1, ha2, har⟩ => ?_⟩⟩ y hy'
    · exact (hMz hdev).1 a ⟨by omega, ha2⟩
    · exact (hMz hdev).2 q psz hq a ha ⟨by omega, har.2⟩
    · exact (hR5 sl' false b n f hne hcs).1 a ⟨by omega, ha2⟩ hfa
    · exact ((hR5 sl' false b n f hne hcs).2 ⟨a, ⟨by omega, ha2⟩, har⟩).2

/-- **`ZR` across the syscall entry** (no premise; `UtInv3`: the carried untyped invariant). -/
theorem kentry_zr (c : Syscall) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZR σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ZR y.2 :=
  kentry_zr_of perfGapZ c hU hZ

/-- **`ZR` across every kernel event** (no premise). -/
theorem kcall_zr (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZR σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZR y.2 :=
  kcall_zr_of perfGapZ rep ev hU hZ

end

end Fl4Proofs.P3.SInvUZ
