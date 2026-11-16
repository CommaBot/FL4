/-
P3: **`JPlaced` across retype** (ScPlace's joint placement), from
`RetPostN` and P1's heap after.

* `HOut H H' lo hi A k w K`: **P1's half, in one shape** — the heap after
  is `H` with the objects meeting the dropped region `[lo, hi)` (the
  window, or with a reset the untyped cap's region) removed and the new
  objects `K` at the window's slots.  `hOut_of_steps` derives it from P1's
  `ResetP1Step` (`reset_step`) and `RetypeP1Step` (`creation_step`).
* `HeapOK` of the heap after (`heapOK_out`).
* `JPlaced.retype`: the placement after, its scheduler side (`tr`, the
  spec's SCs `sc`) and the IRQ slots as hypotheses.
-/
import Fl4Proofs.P3.RetypeBridge
import Fl4Proofs.P3.ScPlace
import Fl4Proofs.P3.UntypedFrame
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

/-- **P1's heap after a retype** (module docstring). -/
def HOut (H H' : Heap) (lo hi A k w : Nat) (K : Option HKind) : Prop :=
  ∀ q, H' q = if NewAt A k w q ∧ K.isSome then K else
    if ∃ kd, H q = some kd ∧ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) then none else H q

theorem objTypeOf_inj {n m : Nat} {t : Fl4Spec.ApiObjectType} (hn : objTypeOf n = some t)
    (hm : objTypeOf m = some t) : n = m := by
  have hn' : n < 19 := by by_contra h; have := (objTypeOf_none n).2 (by omega); rw [this] at hn; cases hn
  have hm' : m < 19 := by by_contra h; have := (objTypeOf_none m).2 (by omega); rw [this] at hm; cases hm
  interval_cases n <;> interval_cases m <;>
    first | rfl | (simp only [objTypeOf, Fl4Spec.archDataToObjType] at hn hm; rw [← hm] at hn; simp at hn)

/-- **`HOut` from P1's two steps**: the reset's heap (`H` off the region,
or `H` itself with no reset, the region then the window) and the creation's
(`creation_step`'s three facts over the window). -/
theorem hOut_of_steps {H H1 H' : Heap} {lo hi A k w : Nat} {K : Option HKind}
    (hk1 : 1 ≤ k) (hlo : lo ≤ A) (hhi : A + w * k ≤ hi)
    (hH1 : (H1 = H ∧ lo = A ∧ hi = A + w * k) ∨
      ∀ q, H1 q = if MeetsR lo hi q.val (q.val + 2 ^ ((H q).elim 0 HKind.bits)) then none else H q)
    (hkeep : ∀ q kd, H1 q = some kd → ¬ MeetsR A (A + w * k) q.val (q.val + 2 ^ kd.bits) → H' q = some kd)
    (hshape : ∀ q kd, H' q = some kd → (H1 q = some kd ∧ ¬ MeetsR A (A + w * k) q.val (q.val + 2 ^ kd.bits)) ∨
      (NewAt A k w q ∧ K = some kd))
    (hnew : ∀ q, NewAt A k w q → ∀ kd, K = some kd → H' q = some kd) :
    HOut H H' lo hi A k w K := by
  -- the window lies in the region; the reset's heap misses the region
  have hm1 : ∀ q kd, H1 q = some kd → (H q = some kd ∧ (MeetsR A (A + w * k) q.val (q.val + 2 ^ kd.bits) →
      MeetsR lo hi q.val (q.val + 2 ^ kd.bits))) ∧
      (MeetsR lo hi q.val (q.val + 2 ^ kd.bits) → MeetsR A (A + w * k) q.val (q.val + 2 ^ kd.bits)) := by
    intro q kd hq
    rcases hH1 with ⟨rfl, rfl, rfl⟩ | h
    · exact ⟨⟨hq, id⟩, id⟩
    · rw [h q] at hq
      split_ifs at hq with hm
      refine ⟨⟨hq, fun hw => absurd ?_ hm⟩, fun hm' => absurd ?_ hm⟩
      · rw [hq]; simp only [Option.elim]; unfold MeetsR at hw ⊢; omega
      · rw [hq]; exact hm'
  have hH1H : ∀ q kd, H q = some kd → ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) → H1 q = some kd := by
    intro q kd hq hm
    rcases hH1 with ⟨rfl, -, -⟩ | h
    · exact hq
    · rw [h q, hq]; exact if_neg (by simpa only [Option.elim] using hm)
  intro q
  by_cases hN : NewAt A k w q ∧ K.isSome
  · rw [if_pos hN]
    obtain ⟨kd, hkd⟩ := Option.isSome_iff_exists.1 hN.2
    rw [hkd]; exact hnew q hN.1 kd hkd
  rw [if_neg hN]
  cases hq' : H' q with
  | some kd =>
    rcases hshape q kd hq' with ⟨h1, hnm⟩ | ⟨hna, hK⟩
    · obtain ⟨⟨hH, -⟩, hin⟩ := hm1 q kd h1
      rw [if_neg (fun ⟨kd', hk', hm⟩ => by rw [hH] at hk'; cases hk'; exact hnm (hin hm)), hH]
    · exact absurd ⟨hna, by rw [hK]; rfl⟩ hN
  | none =>
    split_ifs with hm
    · rfl
    · cases hHq : H q with
      | none => rfl
      | some kd =>
        exfalso
        have h1 := hH1H q kd hHq (fun h => hm ⟨kd, hHq, h⟩)
        have := hkeep q kd h1 (fun hw => hm ⟨kd, hHq, (hm1 q kd h1).1.2 hw⟩)
        rw [hq'] at this; cases this

/-! ## Caps and the objects they name -/

theorem capRange {c : capability.Cap} {p b : U64} (hp : ptrF c = p) (hs : sizeF c = b) (hb : b.val < 64)
    (hfit : p.val + 2 ^ b.val ≤ 2 ^ 64) : baseF c = p.val ∧ topF c = p.val + 2 ^ b.val - 1 := by
  refine ⟨by unfold baseF; rw [hp], ?_⟩
  unfold topF
  rw [hp, hs]
  have hm := maskF_val (b := b) hb
  have h1 : 1 ≤ 2 ^ b.val := Nat.one_le_two_pow
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hm]
  omega

theorem range_ep (p b : U64) (x1 x2 x3 x4 : Bool) (hfit : p.val + 2 ^ 4 ≤ 2 ^ 64) :
    baseF (.Endpoint p b x1 x2 x3 x4) = p.val ∧ topF (.Endpoint p b x1 x2 x3 x4) = p.val + 2 ^ 4 - 1 :=
  capRange (b := 4#u64) (ok_inj (ptr_eq _).symm)
    (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits, fl4_abi.consts.bits.ENDPOINT])) (by decide) hfit
theorem range_ntfn (p b : U64) (x1 x2 : Bool) (hfit : p.val + 2 ^ 6 ≤ 2 ^ 64) :
    baseF (.Notification p b x1 x2) = p.val ∧ topF (.Notification p b x1 x2) = p.val + 2 ^ 6 - 1 :=
  capRange (b := 6#u64) (ok_inj (ptr_eq _).symm)
    (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits, fl4_abi.consts.bits.NOTIFICATION])) (by decide) hfit
theorem range_reply (p : U64) (g : Bool) (hfit : p.val + 2 ^ 5 ≤ 2 ^ 64) :
    baseF (.Reply p g) = p.val ∧ topF (.Reply p g) = p.val + 2 ^ 5 - 1 :=
  capRange (b := 5#u64) (ok_inj (ptr_eq _).symm)
    (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits, fl4_abi.consts.bits.REPLY])) (by decide) hfit

/-- A physical non-untyped cap in the MDB covers its range. -/
theorem covered_of_cap {m : U64 → U64} {G : MdbGhost} {y : U64} {c : capability.Cap} (hy : y ∈ G.chains.flatten)
    (hc : capV m y = c) (hph : physF c = true) (hu : isUt c = false) {p : U64} {b : Nat}
    (hr : baseF c = p.val ∧ topF c = p.val + 2 ^ b - 1) : Covered m G p.val (p.val + 2 ^ b) := by
  have := Nat.one_le_two_pow (n := b)
  exact ⟨y, hy, by rw [hc]; exact hph, by rw [hc]; exact hu, by rw [hc, hr.1], by rw [hc, hr.2]; omega⟩

theorem capTyped_ut {H : Heap} {Rp Nt : Set U64} {c : capability.Cap} (h : isUt c = true) : CapTyped H Rp Nt c := by
  obtain ⟨q, sz, f, d, rfl⟩ := isUt_iff.1 h
  unfold CapTyped; simp

theorem capTyped_null {H : Heap} {Rp Nt : Set U64} : CapTyped H Rp Nt .Null := by
  unfold CapTyped; simp

/-- **A kept cap stays typed** when the objects it covers are kept. -/
theorem capTyped_keep {H H' : Heap} {m : U64 → U64} {G : MdbGhost} {y : U64} {c : capability.Cap}
    (hHO : HeapOK H) (hy : y ∈ G.chains.flatten) (hc : capV m y = c)
    (hT : CapTyped H (Heap.replies H) (Heap.ntfns H) c)
    (hkeep : ∀ q kd, H q = some kd → Covered m G q.val (q.val + 2 ^ kd.bits) → H' q = some kd) :
    CapTyped H' (Heap.replies H') (Heap.ntfns H') c := by
  obtain ⟨he, hn, hr⟩ := hT
  refine ⟨fun p b x1 x2 x3 x4 e => ?_, fun p b x1 x2 e => ?_, fun p g e => ?_⟩
  · have hp := he p b x1 x2 x3 x4 e
    subst e
    exact hkeep p _ hp (covered_of_cap hy hc (ok_inj (phys_eq _).symm) rfl (range_ep _ _ _ _ _ _ (hHO.fits p _ hp)))
  · obtain ⟨hpN, hp⟩ := hn p b x1 x2 e
    subst e
    have h' := hkeep p _ hp (covered_of_cap hy hc (ok_inj (phys_eq _).symm) rfl
      (range_ntfn _ _ _ _ (hHO.fits p _ hp)))
    exact ⟨h', h'⟩
  · have hp : H p = some .reply := hr p g e
    subst e
    exact hkeep p _ hp (covered_of_cap hy hc (ok_inj (phys_eq _).symm) rfl (range_reply _ _ (hHO.fits p _ hp)))

/-- **A new cap is typed** over the heap with the new objects. -/
theorem capTyped_new {H : Heap} {n : Nat} {base us : U64} {dev : Bool} (hn : n ≤ 13)
    (he : n = 2 → H base = some .ep) (hnt : n = 3 → H base = some .ntfn) (hr : n = 6 → H base = some .reply) :
    CapTyped H (Heap.replies H) (Heap.ntfns H) (newCapOf n base us dev) := by
  interval_cases n <;> unfold CapTyped <;> simp [newCapOf, Heap.replies, Heap.ntfns] at *
  · exact he
  · exact hnt
  · exact hr

/-! ## The heap after -/

theorem HOut.some {H H' : Heap} {lo hi A k w : Nat} {K : Option HKind} (hO : HOut H H' lo hi A k w K) {q : U64}
    {kd : HKind} (h : H' q = some kd) :
    (NewAt A k w q ∧ K = some kd) ∨
      (H q = some kd ∧ ¬ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) ∧ ¬ (NewAt A k w q ∧ K.isSome)) := by
  rw [hO q] at h
  split_ifs at h with h1 h2
  · exact Or.inl ⟨h1.1, h⟩
  · exact Or.inr ⟨h, fun hm => h2 ⟨kd, h, hm⟩, h1⟩

theorem newAt_val {A k w : Nat} {q : U64} (h : NewAt A k w q) (hk : 1 ≤ k) :
    ∃ j, j < w ∧ q.val = A + j * k ∧ A ≤ q.val ∧ q.val + k ≤ A + w * k := by
  obtain ⟨j, hj, hq⟩ := h
  have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at this
  exact ⟨j, hj, hq, by omega, by omega⟩

/-- **The heap after is placed** (`HeapOK`). -/
theorem heapOK_out {H H' : Heap} {lo hi A k w : Nat} {K : Option HKind} (hH : HeapOK H)
    (hO : HOut H H' lo hi A k w K) (hlo : lo ≤ A) (hhi : A + w * k ≤ hi) (hk1 : 1 ≤ k) (hA : A % k = 0)
    (hkd : ∀ kd, K = some kd → 2 ^ kd.bits ∣ k) (hfit : A + w * k ≤ 2 ^ 64)
    (hlt : ∀ kd, K = some kd → kd.bits < 64) (hsc : ∀ z, K = some (.sc z) → 7 ≤ z) : HeapOK H' := by
  have hkb : ∀ kd, K = some kd → 2 ^ kd.bits ≤ k := fun kd h => Nat.le_of_dvd (by omega) (hkd kd h)
  refine ⟨fun p kd hp => ?_, fun p kd hp => ?_, fun p kd hp => ?_, fun p z hp => ?_, fun p kd q kd' hp hq hpq => ?_⟩
  · rcases hO.some hp with ⟨hn, hK⟩ | ⟨h, -⟩
    · obtain ⟨j, hj, hv, -⟩ := newAt_val hn hk1
      rw [hv]
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans (hkd kd hK) (Nat.dvd_of_mod_eq_zero hA))
        (Nat.dvd_trans (hkd kd hK) (Nat.dvd_mul_left k j)))
    · exact hH.align p kd h
  · rcases hO.some hp with ⟨hn, hK⟩ | ⟨h, -⟩
    · obtain ⟨j, hj, hv, h1, h2⟩ := newAt_val hn hk1
      have := hkb kd hK; omega
    · exact hH.fits p kd h
  · rcases hO.some hp with ⟨-, hK⟩ | ⟨h, -⟩
    · exact hlt kd hK
    · exact hH.lt64 p kd h
  · rcases hO.some hp with ⟨-, hK⟩ | ⟨h, -⟩
    · exact hsc z hK
    · exact hH.scmin p z h
  · rcases hO.some hp with ⟨hn, hK⟩ | ⟨h, hm, hnn⟩ <;> rcases hO.some hq with ⟨hn', hK'⟩ | ⟨h', hm', hnn'⟩
    · obtain ⟨i, hi, hv, -⟩ := newAt_val hn hk1
      obtain ⟨j, hj, hv', -⟩ := newAt_val hn' hk1
      rw [hK] at hK'; cases hK'
      have hb := hkb kd hK
      have hij : i ≠ j := fun e => hpq (UScalar.eq_of_val_eq (by rw [hv, hv', e]))
      rcases Nat.lt_or_gt_of_ne hij with h | h
      · have : (i + 1) * k ≤ j * k := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul, Nat.one_mul] at this; left; omega
      · have : (j + 1) * k ≤ i * k := Nat.mul_le_mul_right _ h
        rw [Nat.add_mul, Nat.one_mul] at this; right; omega
    · obtain ⟨i, hi, hv, h1, h2⟩ := newAt_val hn hk1
      have hb := hkb kd hK
      unfold MeetsR at hm'; omega
    · obtain ⟨j, hj, hv', h1, h2⟩ := newAt_val hn' hk1
      have hb := hkb kd' hK'
      unfold MeetsR at hm; omega
    · exact hH.disj p kd q kd' h h' hpq

end

/-! ## `JPlaced` across retype -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem tcbSlot_win {A w j i v p : Nat} (hp : p = A + j * 4096) (hj : (j + 1) * 4096 ≤ w * 4096) (hi : i < 6)
    (hv : v = p + 32 * i ∨ v = p + 32 * i + 8) : A ≤ v ∧ v < A + w * 4096 := by
  rw [Nat.add_mul, Nat.one_mul] at hj; omega

theorem tcbSlot_notInT {A j j' i v p : Nat} (hp : p = A + j * 4096) (hi : i < 6)
    (hv : v = p + 32 * i ∨ v = p + 32 * i + 8) (h1 : A + j' * 4096 + 256 ≤ v) (h2 : v < A + j' * 4096 + 4096) :
    False := by
  rcases Nat.lt_trichotomy j' j with h | h | h
  · have : (j' + 1) * 4096 ≤ j * 4096 := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  · subst h; omega
  · have : (j + 1) * 4096 ≤ j' * 4096 := Nat.mul_le_mul_right _ h
    rw [Nat.add_mul, Nat.one_mul] at this; omega

theorem win_lt {A w j k : Nat} (hj : j < w) (hk : 1 ≤ k) (hfit : A + w * k ≤ 2 ^ 64) : A + j * k < 2 ^ 64 := by
  have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
  rw [Nat.add_mul, Nat.one_mul] at this; omega

theorem tcbSlot_al {p i : Nat} (hp : p % 32 = 0) : (p + 32 * i) % 8 = 0 := by omega

theorem sts_cpu (s : S) (t v : U64) : sched.set_thread_state st s t v ⦃ s' => L.cpu s' = L.cpu s ⦄ := by
  unfold sched.set_thread_state sched.schedule_tcb
  rw [tcb_set_state_eq]; simp only [bind_ok]
  step*
  all_goals subst_vars; simp

theorem nodeAt_val' {s : S} {c off : U64} (hf : (L.ksb s).val + 13568 + (c.val + 1) * 4288 ≤ 2 ^ 64)
    (ho : off.val < 4288) : (L.nodeAt s c off).val = (L.ksb s).val + 13568 + c.val * 4288 + off.val := by
  have hk := (L.ksb s).hBounds
  have hc := c.hBounds
  simp [LawfulStore.nodeAt, core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq,
    U64.size_def, U64.numBits, UScalar.size] at hk hc ⊢
  rw [Nat.add_mul, Nat.one_mul] at hf
  omega

theorem node_ge {s s1 : S} {c off : U64} (hnf : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64)
    (hk : L.ksb s1 = L.ksb s) (hc : c.val ≤ (L.cpu s).val) (ho : off.val < 4288) :
    (L.ksb s).val + 13568 ≤ (L.nodeAt s1 c off).val := by
  have hm : (c.val + 1) * 4288 ≤ ((L.cpu s).val + 1) * 4288 := Nat.mul_le_mul_right _ (Nat.succ_le_succ hc)
  have hf : (L.ksb s1).val + 13568 + (c.val + 1) * 4288 ≤ 2 ^ 64 :=
    le_trans (by rw [hk]; exact Nat.add_le_add_left hm _) hnf
  rw [nodeAt_val' hf ho, hk, Nat.add_assoc]
  exact Nat.le_add_right _ _

theorem capV_zero {m : U64 → U64} {a : U64} (h0 : m a = 0#u64) (h8 : m (wordOf a 8#u64) = 0#u64) :
    capV m a = .Null := by
  unfold capV; rw [h0, h8]; rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8000 in
/-- **`JPlaced` across a retype** (module docstring): from the placement
before, `JCovD`, `RetPostN` with the retype done, the FL4 type number `n`
of the spec type, the kernel-global area placed, the current thread a TCB, the preemption point's
write frame (`hPPW`, P1's `PPW`) and the IRQ slots' caps null or in the MDB: the typed heap, spec state and window after, such that
over any P1 heap after in `HOut`'s shape (the dropped region `[lo, hi)`),
with the new TCBs among `Tr'` and the spec's SCs in `C'` and the heap after,
the placement holds. -/
theorem JPlaced.retype {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs Tr C : Set U64} {s : S}
    {σ : Fl4Spec.State Unit} {A' : Type} {arI : machine.Arch A'} {ar : A'}
    {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A'}
    (hJP : JPlaced (L := L) th H Tr C s σ) (hJ : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G)
    (hI : MdbInv (L.mem s) G) (hM : MdbLinks th (L.mem s) G)
    (hRP : RetPostN (L := L) th (L.mem s) G σ arI ar s bitsApi (L.ksb s) (.retype sl rs pb rb t us slots dev) res)
    (hok : res.1 = .Ok ())
    (n : Nat) (hnT : objTypeOf n = some t) (hn13 : n ≤ 13)
    (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ 2 ^ bitsApi t us)
    (hlt : ∀ kd, newKind n us = some kd → kd.bits < 64) (hsc7 : ∀ z, newKind n us = some (.sc z) → 7 ≤ z)
    (hdevT : n = 1 → dev = false) (hz1 : n = 1 → 2 ^ bitsApi t us = 4096)
    (hka : (L.ksb s).val % 8 = 0) (hnf : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64)
    (hcurT : ∀ ct, sched.cur_thread st s = ok ct → th ct = some .tcb)
    (hPPW : ∀ (s1 : S) (a1 : A'), sched.preemption_point st arI s1 a1 ⦃ r => WritesIn st s1 r.2.1 (PPW st s1) ⦄)
    (hirqG : ∀ i : U64, i.val < 128 →
      capV (L.mem s) (nodeA (L.ksb s) i) = .Null ∨ nodeA (L.ksb s) i ∈ G.chains.flatten):
    ∃ (th' : TypedHeap) (σ' : Fl4Spec.State Unit) (A k w lo hi : Nat),
      A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧ lo ≤ A ∧ A + w * k ≤ hi ∧
      ((lo = A ∧ hi = A + w * k) ∨ ∃ (ct : U64) (s0 sR : S) (a1 : A') (p sb fi : U64) (d : Bool),
        sched.cur_thread st s = ok ct ∧ sched.set_thread_state st s ct sched.TS_RESTART = ok s0 ∧
        untyped.reset_untyped st arI s0 ar (cslotAddr sl) = ok (.Ok (), sR, a1) ∧
        capAt (L.mem s0) (cslotAddr sl) = ok (.Untyped p sb fi d) ∧ lo = p.val ∧ hi = p.val + 2 ^ sb.val) ∧
      ∀ H' : Heap, HOut H H' lo hi A k w (newKind n us) →
        (∀ (c : U64) y n', c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n') → H' c = some (.sc n')) →
        JPlaced (L := L) th' H' {q | q ∈ Tr ∨ th' q = some .tcb}
          {c | c ∈ C ∨ (c ≠ 0#u64 ∧ ∃ y n', σ'.kheap c.bv = some (.schedContext y n'))} res.2.1 σ' := by
  obtain ⟨-, -, -, -, σ', G', th', -, -, hP', -, -, hM', -, -, -, -, -, hks, A, k, w, dslot, cj, hE,
    ⟨ct, s0, hct, hs0, hbr⟩, hut⟩ := hRP
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, hlo, hhi, hRF, hsl,
    ⟨n0, hn0, hthx, uu, huu, hcjE⟩, hdsC, hW, hWZ, hHd⟩
  · rw [hok] at e; cases e
  have e0 := objTypeOf_inj hn0 hnT
  subst n0
  have hk1 := hE.k1
  -- the dropped region is uncovered
  have hunc : ∀ a b, a < b → Covered (L.mem s) G a b → b ≤ lo ∨ hi ≤ a := by
    rcases hor with ⟨-, -, rfl, rfl⟩ | ⟨a1, p, sb, fi, d, hr, hc, hcs, hp8, hsb4, hxG, hnd, rfl, rfl, -⟩
    · intro a b hab hc
      obtain ⟨x0, hx0, p0, sb0, fi0, d0, hc0, h1, h2, h3⟩ := hE.src
      rcases h3 with h3 | h3
      · rcases ut_free_fi hU hx0 hc0 hab hc with e | e <;> omega
      · rcases ut_free hU hI hx0 hc0 h3 hab hc with e | e <;> omega
    · intro a b hab hcv
      exact ut_free hU hI hxG (capV_of_capAt hcs) hnd hab hcv
  -- the window fits
  have hfit : A + w * k ≤ 2 ^ 64 := by
    obtain ⟨x0, hx0, p0, sb0, fi0, d0, hc0, h1, h2, -⟩ := hE.src
    have hreg := hU.reg x0 hx0 (by rw [hc0]; exact physF_ut _ _ _ _)
    rw [hc0] at hreg
    obtain ⟨-, -, hf⟩ := ut_range (capV_ut_sb hc0) hreg
    omega
  -- the IRQ slots' words: outside the objects, the untyped regions and the nodes
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := le_trans (Nat.le_add_right _ _) hnf
  have hSA : layout.node.SCHED_ACTION.val = 16 := by unfold layout.node.SCHED_ACTION; rfl
  have hDB : layout.node.DEBUG_TCBS.val = 88 := by unfold layout.node.DEBUG_TCBS; rfl
  have hCT : layout.node.CUR_TIME.val = 48 := by unfold layout.node.CUR_TIME; rfl
  have hCO : layout.node.CONSUMED.val = 40 := by unfold layout.node.CONSUMED; rfl
  have hWU : layout.ks.WORK_UNITS.val = 40 := by unfold layout.ks.WORK_UNITS; rfl
  have hOb : ∀ q kd, H q = some kd → ∀ v : U64, (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 →
      ¬ (q.val ≤ v.val ∧ v.val < q.val + 2 ^ kd.bits) := fun q kd hq v h1 h2 hin => by
    rcases hJP.ks q kd hq with e | e <;> omega
  have hSl : ∀ a, IsSlot th a → ∀ v : U64, (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 →
      ¬ (a.val ≤ v.val ∧ v.val < a.val + 32) := fun a ha v h1 h2 hin => by
    obtain ⟨q, kq, hq, e1, e2, -⟩ := hJP.slot_in ha
    exact hOb q kq hq v h1 h2 ⟨by omega, by omega⟩
  have hUt : ∀ x ∈ G.chains.flatten, ∀ p sb fi d, capV (L.mem s) x = .Untyped p sb fi d →
      ∀ v : U64, (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 →
      ¬ (p.val ≤ v.val ∧ v.val < p.val + 2 ^ sb.val) := fun x hx p sb fi d hc v h1 h2 hin => by
    rcases (hJ.ks x hx p sb fi d hc).1 with e | e <;> omega
  have hNd : ∀ (s1 : S) (c off : U64), L.ksb s1 = L.ksb s → c.val ≤ (L.cpu s).val → off.val < 4288 →
      (L.ksb s).val + 13568 ≤ (L.nodeAt s1 c off).val := fun s1 c off hk hc ho => node_ge hnf hk hc ho
  have hct' := hcurT ct hct
  have hstv : (stA ct).val = ct.val + 3328 := by
    have htf := hJP.pl.fits ct _ hct'
    rw [stA_eq, wordOf_val (by simp [objSize] at htf; simp; omega)]; simp
  obtain ⟨s0', hs0', hF1⟩ := spec_exists (set_thread_state_frame (L := L) s ct sched.TS_RESTART
    (by have hta := hJP.pl.align ct _ hct'; unfold P1.Aligned; rw [hstv]; omega)
    (by unfold P1.Aligned; rw [nodeAt_val' hnf (by rw [hSA]; decide), hSA]; omega))
  rw [hs0] at hs0'; cases eq_of_ok_eq hs0'
  obtain ⟨s0k, hs0k, hk0⟩ := spec_exists (sts_ksb_ret (L := L) s ct sched.TS_RESTART)
  rw [hs0] at hs0k; cases eq_of_ok_eq hs0k
  obtain ⟨s0c, hs0c, hc0⟩ := spec_exists (sts_cpu (L := L) s ct sched.TS_RESTART)
  rw [hs0] at hs0c; cases eq_of_ok_eq hs0c
  have hstA : ∀ v : U64, (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 → v.val ≠ (stA ct).val := by
    intro v h1 h2 e
    exact hOb ct _ ((hJP.tcb ct).1 hct') v h1 h2 ⟨by rw [e, hstv]; omega, by rw [e, hstv]; simp only [HKind.bits]; omega⟩
  -- the words kept from the restart to the creation's start
  have hK1 : ∀ v : U64, P1.Aligned v → (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 →
      L.mem sR v = L.mem s v ∧ L.ksb sR = L.ksb s := by
    intro v hv h1 h2
    have e1 : L.mem s0 v = L.mem s v := hF1 v hv (hstA v h1 h2)
      (fun e => by have := hNd s (L.cpu s) layout.node.SCHED_ACTION rfl (le_refl _) (by rw [hSA]; decide); omega)
    rcases hor with ⟨rfl, -, -, -⟩ | ⟨a1, p, sb, fi, d, hr, hc, hcs, hp8, hsb4, hxG, -, -, -, -⟩
    · exact ⟨e1, hk0⟩
    · have hcv := capV_of_capAt hcs
      have hsb := capV_ut_sb hcv
      have hreg := hU.reg _ hxG (by rw [hcv]; exact physF_ut _ _ _ _)
      rw [hcv] at hreg
      obtain ⟨-, -, hpf⟩ := ut_range hsb hreg
      have hxs : IsSlot th (cslotAddr sl) := ((hM.members _).1 hxG).1
      have hxa := hxs.align hJP.pl
      have hxf := hxs.fit hJP.pl
      obtain ⟨⟨r1, sR', a1'⟩, hrr, hWR, hQ⟩ := spec_exists (reset_frame (L := L) arI s0 ar (cslotAddr sl) hc hp8 hsb4 hpf
        (hU.fib _ hxG _ _ _ _ hcv) (by omega) (by omega)
        (Q := fun t => L.ksb t = L.ksb s0 ∧ L.cpu t = L.cpu s0)
        ⟨fun s1 a n _ _ _ _ ⟨h1, h2⟩ => ⟨by simp [h1], by simp [h2]⟩,
         fun s1 c ⟨h1, h2⟩ => WP.spec_mono (set_cap_kc (L := L) _ s1 c) fun s' ⟨k1, k2⟩ => ⟨k1.trans h1, k2.trans h2⟩⟩
        ⟨rfl, rfl⟩ (PW := PPW st s0)
        (fun s1 a1 ⟨q1, q2⟩ => WP.spec_mono (hPPW s1 a1) fun r ⟨hk, hc, hm⟩ =>
          ⟨⟨hk, hc, fun b hb hn => hm b hb (fun hp => hn (PPW.of q1 q2 hp))⟩, ⟨hk.trans q1, hc.trans q2⟩⟩))
      rw [hr] at hrr; cases eq_of_ok_eq hrr
      refine ⟨(hWR.2.2 v hv ?_).trans e1, hWR.1.trans hk0⟩
      rintro (hin | hin | hin)
      · exact hUt _ hxG _ _ _ _ hcv v h1 h2 hin
      · exact hSl _ hxs v h1 h2 ⟨hin.1, by omega⟩
      · rcases hin with e | e | e
        · have : (core.num.U64.wrapping_add (L.ksb s0) layout.ks.WORK_UNITS).val = (L.ksb s).val + 40 := by
            rw [hk0, core.num.U64.wrapping_add_val_eq, hWU]
            simp [U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits]; omega
          rw [e] at h1; omega
        · have := hNd s0 (L.cpu s0) layout.node.CUR_TIME hk0 (by rw [hc0]) (by rw [hCT]; decide)
          unfold LawfulStore.nodeA at e; rw [e] at h2; omega
        · have := hNd s0 (L.cpu s0) layout.node.CONSUMED hk0 (by rw [hc0]) (by rw [hCO]; decide)
          unfold LawfulStore.nodeA at e; rw [e] at h2; omega
  have hT4 : t = .tcbObject → k = 4096 := fun hT => by rw [ek]; exact hz1 (objTypeOf_tcb (hT ▸ hnT))
  have hirq : ∀ i : U64, i.val < 128 →
      capV (L.mem res.2.1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
    intro i hi
    have hv0 := nodeA_val hkf hi
    have hv8 : (wordOf (nodeA (L.ksb s) i) 8#u64).val = (nodeA (L.ksb s) i).val + 8 :=
      wordOf_val (by rw [hv0]; simp; omega)
    have key : ∀ v : U64, P1.Aligned v → (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 →
        L.mem res.2.1 v = L.mem s v := by
      intro v hv h1 h2
      obtain ⟨e1, hkR⟩ := hK1 v hv h1 h2
      refine (hW.2.2 v hv ?_).trans e1
      obtain ⟨x0, hx0, p0, sb0, fi0, d0, hc0, hp0, hw0, -⟩ := hE.src
      have hwin : ¬ (A ≤ v.val ∧ v.val < A + w * k) := fun ⟨a1, a2⟩ =>
        hUt x0 hx0 _ _ _ _ hc0 v h1 h2 ⟨by omega, by omega⟩
      rintro ((⟨hT, hL⟩ | ⟨a, ha, a1, a2⟩) | ⟨-, a1, a2⟩)
      · rcases hL with ⟨a, ha, a1, a2⟩ | ⟨j, hj, hI⟩ | e | ⟨hne, he⟩
        · exact hSl a (hsl a ha) v h1 h2 ⟨a1, a2⟩
        · have hk4 := hT4 hT
          have hjv : (⟨BitVec.ofNat 64 (A + j * 4096)⟩ : U64).val = A + j * 4096 := by
            have hl := win_lt hj (by omega) (show A + w * 4096 ≤ 2 ^ 64 by rw [← hk4]; exact hfit)
            show (BitVec.ofNat 64 (A + j * 4096)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hl]
          obtain ⟨b1, b2, -⟩ := hI
          rw [hjv] at b1 b2
          have : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
          rw [Nat.add_mul, Nat.one_mul] at this
          exact hwin ⟨by omega, by rw [hk4]; omega⟩
        · have := hNd sR 0#u64 layout.node.DEBUG_TCBS hkR (Nat.zero_le _) (by rw [hDB]; decide)
          rw [← e] at this; omega
        · rcases hHd hT with e0 | hh
          · exact hne e0
          · exact hOb _ _ ((hJP.tcb _).1 hh) v h1 h2 ⟨by omega, by simp [HKind.bits]; omega⟩
      · exact hSl a (hsl a ha) v h1 h2 ⟨a1, a2⟩
      · exact hwin ⟨a1, a2⟩
    unfold capV
    rw [key _ (by unfold P1.Aligned; rw [hv0, show (L.ksb s).val + 1248 + 32 * i.val = 8 * (((L.ksb s).val + 1248) / 8 + 4 * i.val) by omega]; omega)
      (by rw [hv0]; omega) (by rw [hv0]; omega),
      key _ (by unfold P1.Aligned; rw [hv8, hv0]; omega) (by rw [hv8, hv0]; omega) (by rw [hv8, hv0]; omega)]
  refine ⟨th', σ', A, k, w, lo, hi, eA, ek, ew, hlo, hhi, ?_, fun H' hO hSC => ?_⟩
  · rcases hor with ⟨-, -, h1, h2⟩ | ⟨a1, p, sb, fi, d, hr, hc, -, -, -, -, -, h1, h2, -⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨ct, s0, sR, a1, p, sb, fi, d, hct, hs0, hr, hc, h1, h2⟩
  have hRk : k = 2 ^ bitsApi t us := ek
  -- the objects a cap in the MDB covers are kept
  have hkeepH : ∀ q kd, H q = some kd → Covered (L.mem s) G q.val (q.val + 2 ^ kd.bits) → H' q = some kd := by
    intro q kd hq hc
    have hb1 := Nat.one_le_two_pow (n := kd.bits)
    have hm := hunc _ _ (by omega) hc
    have n1 : ¬ (NewAt A k w q ∧ (newKind n us).isSome) := by
      rintro ⟨hn, -⟩; obtain ⟨j, hj, hv, h1, h2⟩ := newAt_val hn hk1; omega
    have n2 : ¬ ∃ kd', H q = some kd' ∧ MeetsR lo hi q.val (q.val + 2 ^ kd'.bits) := by
      rintro ⟨kd', hk', hm'⟩; rw [hq] at hk'; cases hk'; unfold MeetsR at hm'; omega
    rw [hO q, if_neg n1, if_neg n2]; exact hq
  -- the typed heap before the creation
  have hthR : ∀ q kd, thR q = some kd → 1 ≤ objSize kd → th q = some kd ∧ ¬ (lo ≤ q.val ∧ q.val < hi) := by
    intro q kd hq h1
    have hfree := hRF q kd hq
    rcases hor with ⟨-, rfl, -, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩
    · exact ⟨hq, by omega⟩
    · exact ⟨(restrictTh_some hq).1, by omega⟩
  have hthR' : ∀ q kd, th q = some kd → ¬ (lo ≤ q.val ∧ q.val < hi) → thR q = some kd := by
    intro q kd hq hout
    rcases hor with ⟨-, rfl, -, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl⟩
    · exact hq
    · rw [restrictTh_out hout]; exact hq
  have hth' := hthx.1
  have hout_new : ∀ q, NewAt A k w q → lo ≤ q.val ∧ q.val < hi := fun q hn => by
    obtain ⟨j, hj, hv, h1, h2⟩ := newAt_val hn hk1; omega
  have hks' : L.ksb res.2.1 = L.ksb s := hks
  refine ⟨heapOK_out hJP.heap hO hlo hhi hk1 hAk (fun kd hK => ?_) hfit hlt hsc7, hP', fun q => ⟨fun h => ?_, fun h => ?_⟩,
    fun p r h => ?_, fun q h => Or.inr h,
    fun c y n' hc hk => ⟨Or.inr ⟨hc, y, n', hk⟩, hSC c y n' hc hk⟩, fun p kd hp => ?_, fun a ha => ?_, fun i hi => ?_, fun t' ht' => ?_⟩
  -- the new objects' size divides the slot size
  · rw [hRk]; exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).1 (hbits kd hK))
  -- TCBs
  · rw [hth' q] at h
    split_ifs at h with hN
    · have hn1 : n = 1 := by unfold thKindN at h; split_ifs at h with h1 h4 <;> simp_all
      subst hn1
      rw [hO q, if_pos ⟨hN.1, rfl⟩]; rfl
    · obtain ⟨hth, hout⟩ := hthR q _ h (by simp [objSize])
      have hH := (hJP.tcb q).1 hth
      have n1 : ¬ (NewAt A k w q ∧ (newKind n us).isSome) := fun ⟨hn, _⟩ => hout (hout_new q hn)
      have n2 : ¬ ∃ kd, H q = some kd ∧ MeetsR lo hi q.val (q.val + 2 ^ kd.bits) := by
        rintro ⟨kd, hk', hm⟩; rw [hH] at hk'; cases hk'
        have := hRF q _ h; unfold MeetsR at hm; simp only [HKind.bits, objSize] at hm this; omega
      rw [hO q, if_neg n1, if_neg n2]; exact hH
  · rcases hO.some h with ⟨hn, hK⟩ | ⟨hH, hm, -⟩
    · have hn1 : n = 1 := by unfold newKind at hK; split_ifs at hK <;> simp_all
      subst hn1
      rw [hth' q, if_pos ⟨hn, rfl⟩]; rfl
    · have hth := (hJP.tcb q).2 hH
      have hout : ¬ (lo ≤ q.val ∧ q.val < hi) := by unfold MeetsR at hm; simp only [HKind.bits] at hm; omega
      rw [hth' q, if_neg (fun ⟨hn, _⟩ => hout (hout_new q hn))]; exact hthR' q _ hth hout
  -- CNodes
  · rw [hth' p] at h
    split_ifs at h with hN
    · have hn4 : n = 4 ∧ r = us := by unfold thKindN at h; split_ifs at h with h1 h4 <;> simp_all
      obtain ⟨rfl, rfl⟩ := hn4
      rw [hO p, if_pos ⟨hN.1, rfl⟩]; rfl
    · obtain ⟨hth, hout⟩ := hthR p _ h (by simp only [objSize]; have := Nat.one_le_two_pow (n := r); omega)
      have hH := hJP.cnode p r hth
      have n1 : ¬ (NewAt A k w p ∧ (newKind n us).isSome) := fun ⟨hn, _⟩ => hout (hout_new p hn)
      have n2 : ¬ ∃ kd, H p = some kd ∧ MeetsR lo hi p.val (p.val + 2 ^ kd.bits) := by
        rintro ⟨kd, hk', hm⟩; rw [hH] at hk'; cases hk'
        have := hRF p _ h
        have e32 : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [Nat.pow_add]; ring
        unfold MeetsR at hm; simp only [HKind.bits, objSize, e32] at hm this; omega
      rw [hO p, if_neg n1, if_neg n2]; exact hH
  -- outside the kernel-global area
  · rw [hks']
    rcases hO.some hp with ⟨hn, hK⟩ | ⟨hH, -⟩
    · obtain ⟨x0, hx0, p0, sb0, fi0, d0, hc0, h1, h2, -⟩ := hE.src
      obtain ⟨j, hj, hv, ha1, ha2⟩ := newAt_val hn hk1
      have hb := hbits kd hK
      rw [← hRk] at hb
      rcases (hJ.ks x0 hx0 p0 sb0 fi0 d0 hc0).1 with e | e
      · left; omega
      · right; omega
    · exact hJP.ks p kd hH
  -- the slots' caps
  · by_cases hm : a ∈ G'.chains.flatten
    · rcases hE.gmem a hm with ha0 | ⟨j, hj, rfl⟩
      · cases hu : isUt (capV (L.mem s) a)
        · obtain ⟨-, e⟩ := hE.keep a ha0 hu
          rw [e]
          exact capTyped_keep hJP.heap ha0 rfl (hJP.typed a ((hM.members a).1 ha0).1) hkeepH
        · exact capTyped_ut (hE.utk a ha0 hu)
      · rw [hE.newc j hj, hcjE]
        unfold cjOf
        have hlt' : rb.toNat + j * k < 2 ^ 64 := by
          have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
          rw [Nat.add_mul, Nat.one_mul] at this; rw [← eA]; omega
        have hv : (⟨BitVec.ofNat 64 (A + j * k)⟩ : U64).val = A + j * k := by
          show (BitVec.ofNat 64 (A + j * k)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [eA]; exact hlt')]
        have hnew : NewAt A k w ⟨BitVec.ofNat 64 (A + j * k)⟩ := ⟨j, hj, hv⟩
        have hK : ∀ kd, newKind n us = some kd → H' ⟨BitVec.ofNat 64 (A + j * k)⟩ = some kd := fun kd hK => by
          rw [hO, if_pos ⟨hnew, by rw [hK]; rfl⟩, hK]
        exact capTyped_new hn13 (fun h2 => hK _ (by subst h2; rfl)) (fun h3 => hK _ (by subst h3; rfl))
          (fun h6 => hK _ (by subst h6; rfl))
    · have hnull : capV (L.mem res.2.1) a = .Null := by
        by_contra hne
        exact hm ((hM'.members a).2 ⟨ha, _, capAt_capV _ _, hne⟩)
      rw [hnull]; exact capTyped_null
  -- the IRQ slots
  · rw [hks']
    have e := hirq i hi
    rcases hirqG i hi with h0 | hmem
    · rw [e, h0]; exact capTyped_null
    · rw [e]
      cases hu : isUt (capV (L.mem s) (nodeA (L.ksb s) i))
      · exact capTyped_keep hJP.heap hmem rfl (hJP.irq i hi) hkeepH
      · exact capTyped_ut hu
  -- the fault-handler slots
  · obtain ⟨p3, i3, hi3, hp3, ha3⟩ := (show AbsSlot th' (t'.bv, Fl4Spec.tcbCnodeIndex 3) from
      ⟨t', rfl, Or.inr ⟨ht', 3, by decide, rfl⟩⟩).at
    have e3 : p3 = t' := bv_inj hp3.symm
    subst e3
    have hthp := ht'
    rw [hth' p3] at hthp
    split_ifs at hthp with hN
    · -- a new TCB: its slots are zero
      have hn1 : n = 1 := by unfold thKindN at hthp; split_ifs at hthp with h1 h4 <;> simp_all
      subst hn1
      have htT : t = .tcbObject := by have := hnT; simp [objTypeOf] at this; exact this.symm
      have hk4 : k = 4096 := by rw [hRk]; exact hz1 rfl
      have hWZ' := hWZ ⟨hdevT rfl, by rw [htT]; simp⟩
      subst hk4
      obtain ⟨j, hj, hjv⟩ := hN.1
      have hiv := hi3.val hP'
      have hi6 : i3 < 6 := by
        rcases hi3 with ⟨r, hr, -⟩ | ⟨-, h⟩
        · rw [ht'] at hr; cases hr
        · simpa [tcbSlots] using h
      have hj1 : (j + 1) * 4096 ≤ w * 4096 := Nat.mul_le_mul_right _ hj
      have hz : ∀ v : U64, P1.Aligned v → v.val = p3.val + 32 * i3 ∨ v.val = p3.val + 32 * i3 + 8 →
          L.mem res.2.1 v = 0#u64 := by
        intro v hv hvv
        have hvw := tcbSlot_win hjv hj1 hi6 hvv
        rcases hWZ' v hv hvw.1 hvw.2 with e | ⟨-, j', hj', hI⟩
        · exact e
        · exfalso
          have hj'v : (⟨BitVec.ofNat 64 (A + j' * 4096)⟩ : U64).val = A + j' * 4096 := by
            have hlt2 : A + j' * 4096 < 2 ^ 64 := win_lt hj' (by decide) hfit
            show (BitVec.ofNat 64 (A + j' * 4096)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt2]
          obtain ⟨h1, h2, -⟩ := hI
          rw [hj'v] at h1 h2
          exact tcbSlot_notInT hjv hi6 hvv h1 h2
      generalize hadef : cslotAddr (p3.bv, Fl4Spec.tcbCnodeIndex 3) = a at ha3 ⊢
      have hav : a.val = p3.val + 32 * i3 := by rw [ha3, hiv]
      have hal3 : a.val % 8 = 0 := by rw [hav]; exact tcbSlot_al (by have := hP'.align p3 _ ht'; simpa [objSize] using this)
      have h8 : (wordOf a 8#u64).val = a.val + 8 := by
        rw [ha3]; exact slot_word_val hP' ⟨p3, i3, hi3, rfl⟩ (Or.inr (Or.inl rfl))
      left
      refine capV_zero (hz a hal3 (Or.inl hav)) (hz _ ?_ (Or.inr ?_))
      · show (wordOf a 8#u64).val % 8 = 0; rw [h8, Nat.add_mod_right]; exact hal3
      · rw [h8, hav]
    · -- an old TCB: its slot kept, or still empty
      obtain ⟨hth, hout⟩ := hthR p3 _ hthp (by simp [objSize])
      have has : AbsSlot th (p3.bv, Fl4Spec.tcbCnodeIndex 3) := ⟨p3, rfl, Or.inr ⟨hth, 3, by decide, rfl⟩⟩
      by_cases hm : cslotAddr (p3.bv, Fl4Spec.tcbCnodeIndex 3) ∈ G'.chains.flatten
      · rcases hE.gmem _ hm with ha0 | ⟨j, hj, hj'⟩
        · rcases hJP.fh p3 hth with e | ⟨ep, b0, b1, b2, b3, b4, e⟩
          · obtain ⟨-, c, hc, hcn⟩ := (hM.members _).1 ha0
            rw [capAt_capV] at hc; have hc' := eq_of_ok_eq hc; rw [e] at hc'; exact absurd hc'.symm hcn
          · have hu : isUt (capV (L.mem s) (cslotAddr (p3.bv, Fl4Spec.tcbCnodeIndex 3))) = false := by rw [e]; rfl
            right; rw [(hE.keep _ ha0 hu).2, e]; exact ⟨ep, b0, b1, b2, b3, b4, rfl⟩
        · exfalso
          obtain ⟨q, r, hq, i, hi, hqi⟩ := hdsC j hj
          obtain ⟨p4, i4, hi4, hp4, ha4⟩ := has.at
          have e4 : p4 = p3 := bv_inj hp4.symm
          subst e4
          have := slotOf_inj hJP.pl (Or.inl ⟨r, hq, hi⟩) hi4 (by rw [← hqi, ← hj', ha4])
          rw [this.1, hth] at hq; cases hq
      · left
        by_contra hne
        exact hm ((hM'.members _).2 ⟨⟨p3, i3, hi3, ha3⟩, _, capAt_capV _ _, hne⟩)

end

end Fl4Proofs.P3.Sched
