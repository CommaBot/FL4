/-
P3 (issue #16, s26): **`PerfGapD` proved** — the untyped perform keeps `ZD`
(l4v `valid_untyped` for device untyped caps; the `invoke_untyped_invs`
argument), so SpecInvDvS4's `kentry_zd_of` / `kcall_zd_of` hold with no
premise (`kentry_zd`, `kcall_zd`, `kentry_devRange`, `kcall_devRange`). Spec
side only (outside the `JAtZ` cone); SpecInvUtZP's structure with the device
flag and every object kind.

* The decode's size check for scheduling contexts (`okv_fl4DecodeSc`:
  `decode_untyped_invocation` refuses a scheduling context below
  `minSchedContextBits`), so every new object is no larger than the retype's
  object size (`objBits_default_le`).
* The reset (`zq_reset`): after `delete_objects` of the source's region the
  state satisfies `ZSD` with the decode state's caps plus the source's region
  as a free part `(base, bits, 0)` (a device source's objects lie in its used
  part, so `delete_objects` removes every object meeting the region); the chunk
  loop keeps those sets. So every outcome has `ZD` and, for a device source,
  no object meeting the region.
* The retype (`zq_tail`, from `TailD` at its start state): the new free
  index, the new objects (inside the window `[rb, rb + len·2^o)`) and the new
  device untyped children `(p, sz, 0)` are added to the canonical sets
  (`zq_good`): a new object lies in the used part of every device cap whose
  region it meets — the source (its new free index), another cap by
  `UtDisj` / `UtDesc` (Nest: the source's region lies in its ancestor's, and
  misses its free part); a new child's region holds no object.
* **`perfGapD : PerfGapD`**, **`kentry_zd`**, **`kcall_zd`** (no premise).
-/
import Fl4Proofs.P3.SpecInvDvS4
open Classical

namespace Fl4Proofs.P3.SInvDV
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-! ## The size check of the decode -/

/-- The decode's size check for scheduling contexts. -/
def ScSzU : UntypedInvocation → Prop
  | .retype _ _ _ _ ty sz _ _ => ty = .schedContextObject → minSchedContextBits ≤ sz

def ScSzOK : Fl4Invocation → Prop
  | .invokeUntyped ui => ScSzU ui
  | _ => True

set_option maxHeartbeats 4000000 in
theorem okv_decodeUntypedSc {w : UView} (label : Data) (args : List Data) (slot : CslotPtr) {dev : Bool}
    {p : ObjRef} {n f : Nat} (ex : List Cap) :
    OkV w ScSzU (decodeUntypedInvocationWith (Z := Unit) fl4ObjBitsApi label args slot (.untypedCap dev p n f) ex) := by
  unfold decodeUntypedInvocationWith
  repeat' okv_step
  all_goals first
    | exact okv_throw _
    | (refine okv_returnOk ?_; intro h; simp_all)
    | (refine okv_returnOk ?_; intro h; subst h; simp only [minSchedContextBits] at *; omega)

set_option maxHeartbeats 4000000 in
theorem okv_fl4DecodeSc {w : UView} (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr)
    (cap : Cap) (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    OkV w ScSzOK (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  cases cap with
  | untypedCap d p n f =>
    unfold fl4DecodeInvocation
    exact okv_liftME (okv_decodeUntypedSc label args sl _)
  | _ =>
    unfold fl4DecodeInvocation
    repeat' (first
      | exact okv_throw _ | exact okv_returnOk trivial
      | (exact okv_liftME (okv_triv fun _ => trivial))
      | (refine okv_ite ?_ ?_)
      | (unfold fl4DecodeTcbInvocation)
      | (dsimp only)
      | split)

/-- **A new object is no larger than the retype's object size** (the decode's check for scheduling contexts). -/
theorem objBits_default_le {ty : ApiObjectType} (hty : ty ≠ .untyped) {sz : Nat}
    (hsc : ty = .schedContextObject → minSchedContextBits ≤ sz) (dev : Bool) (d : Domain) :
    objBits (defaultObject ty dev sz d) ≤ fl4ObjBitsApi ty sz := by
  cases ty with
  | untyped => exact absurd rfl hty
  | schedContextObject =>
    have := hsc rfl
    simp only [defaultObject, objBits, fl4ObjBitsApi, objBitsApi]
    omega
  | archObject a =>
    cases a <;> simp [defaultObject, defaultArchObject, objBits, archKobjSize, fl4ObjBitsApi, objBitsApi]
  | _ =>
    first
      | (simp [defaultObject, objBits, fl4ObjBitsApi, objBitsApi, fl4TcbBits, tcbBits, cteLevelBits, slotBits]; done)
      | (simp [defaultObject, objBits, fl4ObjBitsApi, objBitsApi, cteLevelBits, slotBits]; omega)

/-! ## Helpers (SpecInvUtZP's, restated) -/

theorem zq_ret_in {rb q : ObjRef} {L o : Nat} (hq : q ∈ retPtrs rb L o) (hfit : rb.toNat + L * 2 ^ o ≤ 2 ^ 64) :
    rb.toNat ≤ q.toNat ∧ q.toNat + 2 ^ o ≤ rb.toNat + L * 2 ^ o := by
  obtain ⟨k, hk, rfl⟩ := retPtrs_mem hq
  have hpo := Nat.two_pow_pos o
  have m2 : (k + 1) * 2 ^ o ≤ L * 2 ^ o := Nat.mul_le_mul_right _ hk
  have e2 : (k + 1) * 2 ^ o = k * 2 ^ o + 2 ^ o := Nat.succ_mul _ _
  rw [ptrAdd_toNat (by omega)]; omega

theorem zq_mapMx_mem {P : State Unit → Prop} {α γ : Type} {g : α → NonDet (State Unit) γ} :
    ∀ xs : List α, (∀ a ∈ xs, SInv.IK P (g a)) → SInv.IK P (NonDet.mapMx g xs)
  | [], _ => SInv.ik_pure' _
  | a :: xs, h => SInv.ik_bind' (h a (by simp)) fun _ => zq_mapMx_mem xs fun b hb => h b (by simp [hb])

theorem zq_hd_createCap {U : UtSetD} (ty : ApiObjectType) (sz : Nat) (src : CslotPtr) (dev : Bool) (d : CslotPtr)
    (p : ObjRef) (h : UtInD U (defaultCap ty p sz dev)) : IKH (HUD U) (createCap (Z := Unit) ty sz src dev (d, p)) := by
  unfold createCap; hv_auto

theorem zq_hd_clear {U : UtSetD} (p : Word) (n : Nat) : IKH (HUD U) (doMachineOp (Z := Unit) (clearMemory p n)) :=
  WLH.msk _ (mt_clearMemory _ _)

theorem zq_hd_pp {U : UtSetD} : IKHE (HUD U) (preemptionPoint (Z := Unit)) := by hv_auto

theorem zq_hd_apr {U : UtSetD} (d : Bool) (n : Nat) : IKH (HUD U) (archPostResetUntyped (Z := Unit) d n) := by
  unfold archPostResetUntyped; exact ik_pure _

/-! ## The retype -/

/-- **What the retype needs at its start state** `τ` (the source `s`, its region
`(base, bits)`, the window `[rb, rb + L·2^o)`). -/
structure TailD (τ : State Unit) (s : CslotPtr) (dev : Bool) (base rb : ObjRef) (bits L o : Nat) : Prop where
  cap : ∃ f, SInvU.capAt τ s = some (.untypedCap dev base bits f)
  b64 : bits < 64
  fit : base.toNat + 2 ^ bits ≤ 2 ^ 64
  lo : base.toNat ≤ rb.toNat
  hi : rb.toNat + L * 2 ^ o ≤ base.toNat + 2 ^ bits
  /-- a device source: every object misses its region or lies below the window -/
  src : dev = true → ∀ q ko, τ.kheap q = some ko → InUsed base bits (rb.toNat - base.toNat) q (objBits ko)
  /-- every other device cap: the window misses its free part; if the window meets its region, the source's
  region lies in it -/
  oth : ∀ sl b n f, sl ≠ s → SInvU.capAt τ sl = some (.untypedCap true b n f) →
    (∀ a, rb.toNat ≤ a → a < base.toNat + 2 ^ bits → a ∉ utFr b n f) ∧
    ((∃ a, rb.toNat ≤ a ∧ a < base.toNat + 2 ^ bits ∧ a ∈ utR b n) → ∀ a, a ∈ utR base bits → a ∈ utR b n)

/-- The device untyped children of an untyped retype. -/
def KidsD (dev : Bool) (ty : ApiObjectType) (sz : Nat) (ps : List ObjRef) : UtSetD :=
  fun b n f => dev = true ∧ ty = .untyped ∧ n = sz ∧ f = 0 ∧ b ∈ ps

/-- The new objects of a retype. -/
def NewOb (dev : Bool) (ty : ApiObjectType) (sz : Nat) (ps : List ObjRef) : ObSet :=
  fun q k => ty ≠ .untyped ∧ q ∈ ps ∧ ∃ d, k = objBits (defaultObject ty dev sz d)

set_option maxHeartbeats 4000000 in
/-- **The sets after the free-index write are good** (module docstring). -/
theorem zq_good {τ σ3 : State Unit} {s : CslotPtr} {dev : Bool} {base rb : ObjRef} {ty : ApiObjectType}
    {sz bits L : Nat} (hR : DevRangeS τ) (hT : TailD τ s dev base rb bits L (fl4ObjBitsApi ty sz))
    (hob : ty ≠ .untyped → ∀ d, objBits (defaultObject ty dev sz d) ≤ fl4ObjBitsApi ty sz)
    (hC : ∀ p cref a, capOpt (σ3.kheap p) cref = some a →
      (p = s.1 ∧ cref = s.2 ∧ a = .untypedCap dev base bits (rb.toNat + L * 2 ^ fl4ObjBitsApi ty sz - base.toNat)) ∨
      ((p ≠ s.1 ∨ cref ≠ s.2) ∧ capOpt (τ.kheap p) cref = some a)) :
    GoodD (fun b n f => HasUD σ3 b n f ∨ KidsD dev ty sz (retPtrs rb L (fl4ObjBitsApi ty sz)) b n f)
      (fun q k => ObOf τ q k ∨ NewOb dev ty sz (retPtrs rb L (fl4ObjBitsApi ty sz)) q k) := by
  have hfitR : rb.toNat + L * 2 ^ fl4ObjBitsApi ty sz ≤ 2 ^ 64 := le_trans hT.hi hT.fit
  have hlo := hT.lo
  have hhi := hT.hi
  -- a new object lies in the window
  have hnew : ∀ q k, NewOb dev ty sz (retPtrs rb L (fl4ObjBitsApi ty sz)) q k →
      rb.toNat ≤ q.toNat ∧ q.toNat + 2 ^ k ≤ rb.toNat + L * 2 ^ fl4ObjBitsApi ty sz := by
    rintro q k ⟨hty, hq, d, rfl⟩
    obtain ⟨h1, h2⟩ := zq_ret_in hq hfitR
    have : 2 ^ objBits (defaultObject ty dev sz d) ≤ 2 ^ fl4ObjBitsApi ty sz :=
      Nat.pow_le_pow_right (by decide) (hob hty d)
    exact ⟨h1, by omega⟩
  intro b n f hU q k hq
  rcases hU with ⟨p, cref, hcp⟩ | ⟨hdev, hty, hn, hf, hb⟩
  · rcases hC p cref _ hcp with ⟨rfl, rfl, e⟩ | ⟨hne, hcτ⟩
    · -- the source with its new free index
      simp only [Cap.untypedCap.injEq] at e
      obtain ⟨hd, hb, hn, hf⟩ := e
      subst hd
      rw [hb, hn, hf]
      rcases hq with ⟨ko, hko, rfl⟩ | hq
      · exact inUsed_mono (Or.inl (by omega)) (hT.src rfl q ko hko)
      · obtain ⟨h1, h2⟩ := hnew q k hq
        exact Or.inr ⟨by omega, by omega⟩
    · rcases hq with ⟨ko, hko, rfl⟩ | hq
      · exact hR p cref b n f hcτ q ko hko
      · obtain ⟨h1, h2⟩ := hnew q k hq
        have hcs : SInvU.capAt τ (p, cref) = some (.untypedCap true b n f) := by
          rw [dv_capAt_capOpt]; exact hcτ
        have hsl : (p, cref) ≠ s := by
          intro e; subst e; rcases hne with h | h <;> exact h rfl
        obtain ⟨o1, o2⟩ := hT.oth (p, cref) b n f hsl hcs
        exact inUsed_of_nest (lo := rb.toNat) (hi := base.toNat + 2 ^ bits) h1 (by omega)
          (fun a h1 h2 => o1 a h1 h2)
          (fun ⟨a, ha1, ha2, ha3⟩ a' h1' h2' => o2 ⟨a, ha1, ha2, ha3⟩ a' ⟨by omega, h2'⟩)
  · -- a device untyped child: no new object, the old objects miss the window
    rcases hq with ⟨ko, hko, rfl⟩ | ⟨hne, -⟩
    · rw [hn, hf]
      have hin := zq_ret_in hb hfitR
      have hsz : fl4ObjBitsApi ty sz = sz := by subst hty; rfl
      rw [hsz] at hin hhi
      left
      have hk0 := Nat.two_pow_pos (objBits ko)
      rcases hT.src hdev q ko hko with (h | h) | ⟨h1, h2⟩
      · left; omega
      · right; omega
      · left; omega
    · exact absurd hty hne

set_option maxHeartbeats 4000000 in
/-- **The retype keeps `ZD`** from `TailD` at its start state. -/
theorem zq_tail {τ : State Unit} (hZ : ZD τ) {s : CslotPtr} {base rb : ObjRef} {ty : ApiObjectType} {sz bits : Nat}
    {slots : List CslotPtr} {dev : Bool} (hT : TailD τ s dev base rb bits slots.length (fl4ObjBitsApi ty sz))
    (hob : ty ≠ .untyped → ∀ d, objBits (defaultObject ty dev sz d) ≤ fl4ObjBitsApi ty sz) :
    ∀ y ∈ (ExceptT.run (invokeUntypedWith (Z := Unit) fl4ObjBitsApi (.retype s false base rb ty sz slots dev)) τ).1,
      ZD y.2 := by
  intro y hy
  have hR0 := zd_iff.1 hZ
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
  simp only [Fl4Spec.bitsOf] at hx4
  rw [hfi] at hx4
  have hO4 : OIn (ObOf τ) x4.2 := ob_setCap _ _ τ (fun o ko h => ⟨ko, h, rfl⟩) x4 hx4
  have hC := (vih_setCap_out (o := s.1) (r := s.2) hx4).2
  have hG := zq_good (L := slots.length) hR0 hT hob hC
  have hZ4 : ZSD (fun b n f => HasUD x4.2 b n f ∨ KidsD dev ty sz (retPtrs rb slots.length (fl4ObjBitsApi ty sz)) b n f)
      (fun q k => ObOf τ q k ∨ NewOb dev ty sz (retPtrs rb slots.length (fl4ObjBitsApi ty sz)) q k) x4.2 := by
    refine ⟨hG, fun p cref c hc b n f e => ?_, fun q ko hq => Or.inl (hO4 q ko hq)⟩
    subst e; exact ⟨f, Or.inl ⟨p, cref, hc⟩, Or.inl le_rfl⟩
  -- `retype_region`, `init_arch_objects`, the `create_cap` loop
  obtain ⟨x5, hx5, hx⟩ := hx
  have hp5 := (SInvU.retypeRegionWith_out hx5).1
  have hZ5 := zq_ik hG (hd_retypeRegionWith _ _ _ _ _ _)
    (ob_retypeIn _ _ _ _ _ _ fun hty q hq d => Or.inr ⟨hty, hq, d, rfl⟩) x4.2 hZ4 x5 hx5
  obtain ⟨x6, hx6, hx⟩ := hx
  have hZ6 := zq_ik hG (by hv_auto) (ob_initArchObjects _ _ _ _ _ _) x5.2 hZ5 x6 hx6
  rw [hp5] at hx
  refine ⟨_, _, (zq_mapMx_mem _ fun dp hdp => ?_) x6.2 hZ6 x hx⟩
  obtain ⟨d, p⟩ := dp
  have hp : p ∈ retPtrs rb slots.length (fl4ObjBitsApi ty sz) := (List.of_mem_zip hdp).2
  have hut : UtInD (fun b n f => HasUD x4.2 b n f ∨ KidsD dev ty sz (retPtrs rb slots.length (fl4ObjBitsApi ty sz)) b n f)
      (defaultCap ty p sz dev) := by
    intro b n f e
    by_cases hty : ty = .untyped
    · subst hty
      simp only [defaultCap, Cap.untypedCap.injEq] at e
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e
      exact ⟨0, Or.inr ⟨rfl, rfl, rfl, rfl, hp⟩, Or.inl le_rfl⟩
    · exact absurd e (defaultCap_nonUt hty p sz dev true b n f)
  exact zq_ik hG (zq_hd_createCap _ _ _ _ _ _ hut) (ob_createCap _ _ _ _ _)

/-! ## The reset -/

/-- The sets after `delete_objects`: the decode state's caps and a device source's region as a free part. -/
def ResUD (σ : State Unit) (dev : Bool) (base : ObjRef) (bits : Nat) : UtSetD :=
  fun b n f => HasUD σ b n f ∨ (dev = true ∧ b = base ∧ n = bits ∧ f = 0)

theorem zq_utIn_res {σ : State Unit} {dev : Bool} {base : ObjRef} {bits : Nat} (f : Nat) :
    UtInD (ResUD σ dev base bits) (.untypedCap dev base bits f) := by
  intro b n f' e
  simp only [Cap.untypedCap.injEq] at e
  obtain ⟨rfl, rfl, rfl, rfl⟩ := e
  exact ⟨0, Or.inr ⟨rfl, rfl, rfl, rfl⟩, Or.inl (Nat.zero_le _)⟩

set_option maxHeartbeats 4000000 in
/-- **`reset_untyped_cap` keeps `ZD`**, and no object then meets a device source's region (every
outcome, finished or preempted). -/
theorem zq_reset {σ : State Unit} (hZ : ZD σ) {s : CslotPtr} {dev : Bool} {base : ObjRef} {bits fi : Nat}
    (hc : SInvU.capAt σ s = some (.untypedCap dev base bits fi)) (hb : bits < 64)
    (hfit : base.toNat + 2 ^ bits ≤ 2 ^ 64) (hfi : fi ≤ 2 ^ bits) :
    ∀ z ∈ (ExceptT.run (resetUntypedCap (Z := Unit) s) σ).1, ZD z.2 ∧
      (dev = true → ∀ q ko, z.2.kheap q = some ko → InUsed base bits 0 q (objBits ko)) := by
  have hR0 := zd_iff.1 hZ
  have hcs : capOpt (σ.kheap s.1) s.2 = some (.untypedCap dev base bits fi) := by
    rw [← dv_capAt_capOpt]; exact hc
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
    refine ⟨hZ, fun hdev q ko hq => ?_⟩
    subst hdev
    exact hR0 _ _ _ _ _ hcs q ko hq
  · rw [if_neg (show ¬ freeIndexOf (Cap.untypedCap dev base bits fi) = 0 from h0)] at hz
    obtain ⟨z1, hz1, hz⟩ := run_liftE_bind_mem hz
    simp only [Fl4Spec.bitsOf, Fl4Spec.objRefOf] at hz1
    obtain ⟨hk1, -, -, -⟩ := deleteObjects_kheap hz1
    have hpd := mem_delR_iff hb hfit
    -- the objects left miss a device source's region
    have hmiss : dev = true → ∀ q ko, z1.2.kheap q = some ko → InUsed base bits 0 q (objBits ko) := by
      intro hdev q ko hq
      subst hdev
      rw [hk1 q] at hq
      by_cases hqd : q ∈ delR base bits
      · rw [if_pos hqd] at hq; cases hq
      rw [if_neg hqd] at hq
      rcases hR0 _ _ _ _ _ hcs q ko hq with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exfalso
        apply hqd
        refine (hpd q).2 ⟨h1, ?_⟩
        have := Nat.two_pow_pos (objBits ko)
        omega
    -- the sets after `delete_objects`
    have hG1 : GoodD (ResUD σ dev base bits) (ObOf z1.2) := by
      rintro b n f hU q k ⟨ko, hq, rfl⟩
      rcases hU with ⟨p, cref, hcp⟩ | ⟨hdev, hb', hn', hf'⟩
      · have hq' : σ.kheap q = some ko := by
          rw [hk1 q] at hq; split_ifs at hq; exact hq
        exact hR0 p cref b n f hcp q ko hq'
      · rw [hb', hn', hf']
        exact hmiss hdev q ko hq
    have hZ1 : ZSD (ResUD σ dev base bits) (ObOf z1.2) z1.2 := by
      refine ⟨hG1, fun p cref c hc' => ?_, fun o ko h => ⟨ko, h, rfl⟩⟩
      intro b n f e
      obtain ⟨f1, hU, hf⟩ := hd_deleteObjects base bits σ (zq_hud_canon σ) z1 hz1 p cref c hc' b n f e
      exact ⟨f1, Or.inl hU, hf⟩
    -- the rest of the reset keeps the sets
    have hrest : ZSD (ResUD σ dev base bits) (ObOf z1.2) z.2 := by
      refine (?_ : SInv.IKE (ZSD (ResUD σ dev base bits) (ObOf z1.2)) _) z1.2 hZ1 z hz
      try simp only [isDeviceUntypedCap, bitsOf, objRefOf, freeIndexOf]
      repeat' (first
        | (exact zq_ik hG1 (hd_setCap _ _ (zq_utIn_res _)) (ob_setCap _ _))
        | (exact zq_ik hG1 (zq_hd_clear _ _) (ob_dmo _))
        | (exact zq_ik hG1 zq_hd_pp ob_preemptionPoint)
        | (exact zq_ik hG1 (zq_hd_apr _ _) (ob_archPostResetUntyped _ _))
        | (refine ike_mapMEx_mem _ fun _ _ => ?_)
        | ik_step0 | (unfold NonDet.unless) | (unfold NonDetE.whenE) | split)
    refine ⟨⟨_, _, hrest⟩, fun hdev q ko hq => ?_⟩
    obtain ⟨ko1, hq1, e1⟩ := hrest.2.2 q ko hq
    rw [e1]
    exact hmiss hdev q ko1 hq1

/-! ## `PerfGapD` -/

set_option maxHeartbeats 4000000 in
/-- **The untyped perform keeps `ZD`** (SpecInvDvS2's obligation, proved). -/
theorem perfGapD : PerfGapD := by
  intro N ui σ hP hN hZ hD y hy
  obtain ⟨fp, label, args, ci, sl, cap, ex, buf, σ0, s0, hv, hc, hex, hmem⟩ := hD
  have hf : GapOKN (uV σ) (.invokeUntyped ui) :=
    okv_fl4DecodeG fp label args ci sl cap ex buf hc (fun p hp => (hex p hp).1) σ0 hv _ s0 hmem
  have hsc : ScSzOK (.invokeUntyped ui) :=
    okv_fl4DecodeSc (w := uV σ) fp label args ci sl cap ex buf σ0 hv _ s0 hmem
  have hok : UtGapOK (uV σ) ui := hf
  obtain ⟨h1, -, -⟩ := hok
  have hI : UtInv' σ := hP.1.1
  have hR0 := zd_iff.1 hZ
  obtain ⟨s, reset, base, rb, ty, sz, slots, dev⟩ := ui
  have hob : ty ≠ .untyped → ∀ d, objBits (defaultObject ty dev sz d) ≤ fl4ObjBitsApi ty sz :=
    fun hty d => objBits_default_le hty hsc dev d
  have hok' := h1
  obtain ⟨bits, fi, hc0, -, -, -, -, hr⟩ := hok'
  have hc' : SInvU.capAt σ s = some (.untypedCap dev base bits fi) := hc0
  obtain ⟨bits', fi', hc'', hfit, h1r, -, h3r⟩ := utRet_region hI.1.2.1 (utRetOK_of_V h1)
  rw [hc'] at hc''; cases hc''
  obtain ⟨hbits, -⟩ := UtWf.fit (σ := σ) hI.1.2.1 hc'
  have hcs : capOpt (σ.kheap s.1) s.2 = some (.untypedCap dev base bits fi) := by
    rw [← dv_capAt_capOpt]; exact hc'
  cases reset
  · -- no reset: the window lies in the source's free part
    simp only [Bool.false_eq_true, ↓reduceIte] at h1r
    refine zq_tail hZ ⟨⟨fi, hc'⟩, hbits, hfit, by omega, h3r, fun hdev q ko hq => ?_,
      fun sl' b n f hne hcs' => ⟨fun a ha1 ha2 hfa => ?_, fun ⟨a, ha1, ha2, har⟩ => ?_⟩⟩ hob y hy
    · subst hdev
      exact inUsed_mono (Or.inl (by omega)) (hR0 _ _ _ _ _ hcs q ko hq)
    · exact hI.1.2.2.1 s sl' dev base bits fi true b n f (Ne.symm hne) hc' hcs' a ⟨by omega, ha2⟩ hfa
    · rcases hI.1.2.2.2.1 s sl' dev base bits fi true b n f (Ne.symm hne) hc' hcs'
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
    obtain ⟨hZz, hMz⟩ := zq_reset hZ hc' hbits hfit (hI.1.2.1 s dev base bits fi hc').2.2 z hz
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
    refine zq_tail hZz ⟨⟨f2, hf2⟩, hbits, hfit, by omega, h3r, fun hdev q ko hq => ?_,
      fun sl' b n f hne hcs' => ⟨fun a ha1 ha2 hfa => ?_, fun ⟨a, ha1, ha2, har⟩ => ?_⟩⟩ hob y hy'
    · exact inUsed_mono (Or.inl (Nat.zero_le _)) (hMz hdev q ko hq)
    · exact (hR5 sl' true b n f hne hcs').1 a ⟨by omega, ha2⟩ hfa
    · exact ((hR5 sl' true b n f hne hcs').2 ⟨a, ⟨by omega, ha2⟩, har⟩).2

/-- **`ZD` across the syscall entry** (no premise; `UtInv3`: the carried untyped invariant). -/
theorem kentry_zd (c : Syscall) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZD σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, ZD y.2 :=
  kentry_zd_of perfGapD c hU hZ

/-- **`ZD` across every kernel event** (no premise). -/
theorem kcall_zd (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ) (hZ : ZD σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, ZD y.2 :=
  kcall_zd_of perfGapD rep ev hU hZ

/-- **[J] C26's spec invariant across the syscall entry.** -/
theorem kentry_devRange (c : Syscall) {σ : State Unit} (hU : UtInv3 σ) (hD : DevRangeS σ) :
    ∀ y ∈ ((fl4KernelEntrySyscall (Z := Unit) true c) σ).1, DevRangeS y.2 :=
  fun y hy => zd_iff.1 (kentry_zd c hU (zd_iff.2 hD) y hy)

/-- **[J] C26's spec invariant across every kernel event.** -/
theorem kcall_devRange (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ) (hD : DevRangeS σ) :
    ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) σ).1, DevRangeS y.2 :=
  fun y hy => zd_iff.1 (kcall_zd rep ev hU (zd_iff.2 hD) y hy)

/-- **[J] C26's spec invariant across the FaultIP write.** -/
theorem faultIP_devRange (t : ObjRef) {σ : State Unit} (hD : DevRangeS σ) :
    ∀ y ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1, DevRangeS y.2 :=
  fun y hy => zd_iff.1 (zd_fl4SyscallFaultIP t σ (zd_iff.2 hD) y hy)

/-- **[J] C26's spec invariant across the budget check** (`updateTimeStamp`, `checkBudgetRestart`). -/
theorem budget_devRange {σ : State Unit} (hD : DevRangeS σ) :
    ∀ y ∈ ((updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart) σ).1, DevRangeS y.2 := by
  have h : IKH ZD (updateTimeStamp (Z := Unit) >>= fun _ => checkBudgetRestart) :=
    SInv.ik_bind (ik_zd (fun _ => WLH.uts) (fun _ => ob_updateTimeStamp))
      fun _ => ik_zd (fun _ => hd_checkBudgetRestart) (fun _ => ob_checkBudgetRestart)
  exact fun y hy => zd_iff.1 (h σ (zd_iff.2 hD) y hy)

/-- **[J] C26's spec invariant across the FaultIP write and then any kernel event.** -/
theorem fip_kcall_devRange (t : ObjRef) (rep : Bool) (ev : Event) {σ : State Unit} (hU : UtInv3 σ)
    (hD : DevRangeS σ) : ∀ w ∈ (fl4SyscallFaultIP (Z := Unit) t σ).1, ∀ y ∈ ((fl4CallKernel (Z := Unit) rep ev) w.2).1,
      DevRangeS y.2 := by
  intro w hw y hy
  have hP : P3 σ.interruptIrqNode w.2 := p3_of_view (uk_mem (fun _ => uk_fl4SyscallFaultIP _) hw) (utInv3_iff.1 hU)
  have hN : NodeIs σ.interruptIrqNode w.2 := nk_fl4SyscallFaultIP _ σ rfl w hw
  exact zd_iff.1 (zd_fl4CallKernel perfGapD rep ev _ w.2 hP hN (zd_iff.2 (faultIP_devRange t hD w hw)) y hy)

end

end Fl4Proofs.P3.SInvDV
