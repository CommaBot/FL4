
/-! ## The object half of the arch performs but MakePool -/

/-- The arch invocations other than MakePool. -/
def NotMp : Fl4ArchInvocation → Prop
  | .spec (.invokeASIDControl _) => False
  | _ => True

set_option maxHeartbeats 4000000 in
theorem ob_archPerformInvocation_nc {O : ObSet} (ai : ArchInvocation) (h : ∀ a, ai ≠ .invokeASIDControl a) :
    OBKE O (archPerformInvocation (Z := Unit) ai) := by
  cases ai with
  | invokeASIDControl a => exact absurd rfl (h a)
  | _ => unfold archPerformInvocation; ob_auto

set_option maxHeartbeats 4000000 in
theorem ob_fl4ArchPerform_nc {O : ObSet} (fa : Fl4ArchInvocation) (h : NotMp fa) :
    OBKE O (fl4ArchPerformInvocation (Z := Unit) fa) := by
  cases fa with
  | spec ai =>
    simp only [fl4ArchPerformInvocation]
    exact ob_archPerformInvocation_nc ai (fun a e => by subst e; exact h)
  | _ => simp only [fl4ArchPerformInvocation]; ob_auto

/-! ## ReadFPU -/

set_option maxHeartbeats 4000000 in
/-- **The FL4 TCB extensions keep `ZD`** (the ReadFPU frame write is a machine operation). -/
theorem zd_invokeFl4Tcb (i : Fl4TcbInvocation) : IKHE ZD (invokeFl4Tcb (Z := Unit) i) :=
  ike_zd (fun _ => by cases i <;> simp only [invokeFl4Tcb] <;> hv_auto)
    (fun _ => by cases i <;> simp only [invokeFl4Tcb] <;> ob_auto)

/-! ## Retypes: the object half with the new objects -/

/-- `retype_region` keeps `OIn O` when `O` holds the new objects. -/
theorem ob_retypeIn {O : ObSet} (bA : ApiObjectType → Nat → Nat) (ptr : ObjRef) (n oB : Nat) (ty : ApiObjectType)
    (dev : Bool) (hD : ty ≠ .untyped → ∀ q ∈ retPtrs ptr n (bA ty oB), ∀ d, O q (objBits (defaultObject ty dev oB d))) :
    OBK O (retypeRegionWith (Z := Unit) bA ptr n oB ty dev) := by
  intro σ h y hy
  rcases (SInvU.retypeRegionWith_out hy).2 with e | ⟨hty, e⟩
  · rw [e]; exact h
  · rw [e]
    intro o ko ho
    simp only [SInvU.retKh] at ho
    split_ifs at ho with hm
    · cases ho; exact hD hty o hm _
    · exact h o ko ho

theorem zq_ik {U : UtSetD} {O : ObSet} {α : Type} {m : NonDet (State Unit) α} (hG : GoodD U O)
    (hH : IKH (HUD U) m) (hY : OBK O m) : SInv.IK (ZSD U O) m :=
  fun σ h x hx => ⟨hG, hH σ h.2.1 x hx, hY σ h.2.2 x hx⟩

theorem zq_hud_canon (σ : State Unit) : HUD (HasUD σ) σ := by
  intro p cref c hc b n f e
  subst e
  exact ⟨f, ⟨p, cref, hc⟩, Or.inl le_rfl⟩

/-- An object inside a region `[r, r + 2^m)` that misses a cap's free part and lies in its region when it meets it. -/
theorem inUsed_of_nest {b r : ObjRef} {n f m k : Nat} {o : ObjRef} (hk : 2 ^ k ≤ 2 ^ m)
    (ho1 : r.toNat ≤ o.toNat) (ho2 : o.toNat + 2 ^ k ≤ r.toNat + 2 ^ m)
    (hfr : ∀ x ∈ utR r m, x ∉ utFr b n f)
    (hin : (∃ x, x ∈ utR r m ∧ x ∈ utR b n) → ∀ x ∈ utR r m, x ∈ utR b n) : InUsed b n f o k := by
  have hk0 : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases hd : o.toNat + 2 ^ k ≤ b.toNat ∨ b.toNat + 2 ^ n ≤ o.toNat
  · exact Or.inl hd
  · right
    have hm : ∃ x, x ∈ utR r m ∧ x ∈ utR b n :=
      ⟨max o.toNat b.toNat, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    have h1 := hin hm o.toNat ⟨ho1, by omega⟩
    have h2 := hin hm (o.toNat + 2 ^ k - 1) ⟨by omega, by omega⟩
    have h3 := hfr (o.toNat + 2 ^ k - 1) ⟨by omega, by omega⟩
    obtain ⟨h1a, -⟩ := h1
    obtain ⟨-, h2b⟩ := h2
    have : ¬ (b.toNat + f ≤ o.toNat + 2 ^ k - 1 ∧ o.toNat + 2 ^ k - 1 < b.toNat + 2 ^ n) := h3
    exact ⟨h1a, by omega⟩

/-! ## MakePool -/

theorem asidPool_bits (d : Domain) :
    objBits (defaultObject (.archObject .asidPoolObj) false 0 d) = 12 := rfl

set_option maxHeartbeats 4000000 in
/-- **MakePool keeps `ZD`** (module docstring). -/
theorem zd_makePool {σ : State Unit} (hI : UtInv' σ) (hDT : DetypeOK σ) (hZ : ZD σ) {a : AsidControlInvocation}
    (hm : MpOK σ a) : ∀ y ∈ (performAsidControlInvocation (Z := Unit) a σ).1, ZD y.2 := by
  have hR0 := zd_iff.1 hZ
  intro y hy
  cases a with
  | makePool frame slot parent base =>
    obtain ⟨dev, fi, hc, hk⟩ := hm
    unfold performAsidControlInvocation at hy
    obtain ⟨z, hz, hy⟩ := hy
    have hP := detype_PR hI hDT hc hk hz
    obtain ⟨hk1, -, -, -⟩ := deleteObjects_kheap hz
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hxs, hxc⟩ := getCap_capAt hx
    obtain ⟨pcap, s1⟩ := x
    simp only at hxs hxc; subst hxs
    obtain ⟨hR1, hR2, hR3, hR4, hR5, hR6, hR7⟩ := hP.2
    have hex : (z.2.kheap parent.1).isSome = true := by
      unfold capAt at hxc; cases e : z.2.kheap parent.1 with
      | none => rw [e] at hxc; cases hxc
      | some _ => rfl
    obtain ⟨f, hf⟩ := hR1.resolve_right (fun e => by
      have e' : (z.2.kheap parent.1).isSome = false := e; rw [hex] at e'; cases e')
    have hpc : pcap = .untypedCap dev frame page_bits f := Option.some.inj (hxc.symm.trans hf)
    subst hpc
    obtain ⟨z2, hz2, hy⟩ := hy
    obtain ⟨z3, hz3, hy⟩ := hy
    have hC := (vih_setCap_out (o := parent.1) (r := parent.2) hz2).2
    -- the caps of the decode state
    have hcσ : ∀ p cref c, capOpt (z.2.kheap p) cref = some c → capOpt (σ.kheap p) cref = some c := by
      intro p cref c h
      rw [hk1 p] at h
      split_ifs at h
      · simp [capOpt] at h
      · exact h
    have hcs : capOpt (σ.kheap parent.1) parent.2 = some (.untypedCap dev frame page_bits fi) := by
      rw [← dv_capAt_capOpt]; exact hc
    -- the sets after the free-index write: the caps then, the old objects and the pool
    let O2 : ObSet := fun o k => ObOf z.2 o k ∨ (o.toNat = frame.toNat ∧ k ≤ 12)
    have hG : GoodD (HasUD z2.2) O2 := by
      rintro b n f2 ⟨p, cref, hcp⟩ o k hO
      rcases hC p cref _ hcp with ⟨rfl, rfl, e⟩ | ⟨hne, hcz⟩
      · -- the parent, written back full
        simp only [maxFreeIndexUpdate, freeIndexUpdate, untypedSzBits, maxFreeIndex, Cap.untypedCap.injEq] at e
        obtain ⟨hd, hb, hn, hf2⟩ := e
        subst hd
        rw [hb, hn, hf2]
        rcases hO with ⟨ko, hko, rfl⟩ | ⟨ho, hkk⟩
        · have hko' : σ.kheap o = some ko := by
            rw [hk1 o] at hko; split_ifs at hko; exact hko
          exact inUsed_mono (Or.inr le_rfl) (hR0 _ _ _ _ _ hcs o ko hko')
        · right
          have : 2 ^ k ≤ 2 ^ page_bits := Nat.pow_le_pow_right (by decide) hkk
          exact ⟨by omega, by omega⟩
      · rcases hO with ⟨ko, hko, rfl⟩ | ⟨ho, hkk⟩
        · have hko' : σ.kheap o = some ko := by
            rw [hk1 o] at hko; split_ifs at hko; exact hko
          exact hR0 p cref b n f2 (hcσ p cref _ hcz) o ko hko'
        · have hsl : (p, cref) ≠ parent := by
            intro e; subst e; rcases hne with h | h <;> exact h rfl
          have hcv : (uV z.2).2.1 (p, cref) = some (.untypedCap true b n f2) := by
            show SInvU.capAt z.2 (p, cref) = _; rw [dv_capAt_capOpt]; exact hcz
          obtain ⟨o1, o2⟩ := hR5 (p, cref) true b n f2 hsl hcv
          have hkp : 2 ^ k ≤ 2 ^ page_bits := Nat.pow_le_pow_right (by decide) hkk
          have hpb : (2 : Nat) ^ page_bits = 4096 := rfl
          exact inUsed_of_nest (r := frame) (m := page_bits) hkp (by omega) (by omega) o1
            (fun hm' => (o2 hm').2)
    have hO2 : OIn O2 z2.2 := fun o ko h => Or.inl (ob_setCap _ _ z.2 (fun o ko h => ⟨ko, h, rfl⟩) z2 hz2 o ko h)
    have hZ2 : ZSD (HasUD z2.2) O2 z2.2 := ⟨hG, zq_hud_canon _, hO2⟩
    have hZ3 : ZSD (HasUD z2.2) O2 z3.2 := by
      refine zq_ik hG (hd_retypeRegion _ _ _ _ _) ?_ z2.2 hZ2 z3 hz3
      rw [← retypeRegionWith_objBitsApi]
      refine ob_retypeIn _ _ _ _ _ _ fun _ q hq d => Or.inr ⟨?_, by rw [asidPool_bits]⟩
      simp only [retPtrs, List.range_one, List.map_cons, List.map_nil, List.mem_singleton, Nat.zero_mul] at hq
      subst hq
      unfold ptrAdd; rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero, Nat.mod_eq_of_lt frame.isLt]
    refine ⟨_, _, (zq_ik hG (by hv_auto) (by ob_auto)) z3.2 hZ3 y hy⟩

/-! ## The arch performs -/

variable {N : Irq → ObjRef}

set_option maxHeartbeats 4000000 in
/-- **The arch performs keep `ZD`** (MakePool from the decode's `ArchOKN`). -/
theorem zd_fl4Arch (fa : Fl4ArchInvocation) (σ : State Unit) (hP : P3 N σ) (hZ : ZD σ)
    (hA : GapOKN (uV σ) (.invokeArchObject fa)) :
    ∀ y ∈ ((fl4ArchPerformInvocation (Z := Unit) fa).run σ).1, ZD y.2 := by
  cases fa
  case spec ai =>
    cases ai
    case invokeASIDControl a =>
      intro y hy
      simp only [fl4ArchPerformInvocation, archPerformInvocation] at hy
      obtain ⟨x, hx, rfl⟩ := mem_liftE' hy
      try unfold archNoReturn at hx
      obtain ⟨z, hz, hx⟩ := hx
      rw [Set.mem_singleton_iff.1 hx]
      have hm : MpOK σ a := by cases a; exact hA.1
      exact zd_makePool hP.1.1 (detypeOK_of hP.1) hZ hm z hz
    all_goals exact ike_zd (fun _ => hd_fl4ArchPerformInvocation _) (fun _ => ob_fl4ArchPerform_nc _ (by trivial)) σ hZ
  all_goals exact ike_zd (fun _ => hd_fl4ArchPerformInvocation _) (fun _ => ob_fl4ArchPerform_nc _ (by trivial)) σ hZ

end

end Fl4Proofs.P3.SInvDV
