/-
P3 (DESIGN.md §9), untyped: **a retype that starts after the restart**
(handoff/utj.md Round 13, item 3d). The no-reset retype lemmas start at the
decode state with the restart; with a reset, FL4's `untyped::retype` runs the
same body after `reset_untyped`, from the reset's post-state. The pieces of
the no-reset proofs that read the restart, from one state instead:

* `RetFrameB`/`RetFrameIB`/`RetPostNB`: `RetFrame`/`RetFrameI`/`RetPostN`
  after their restart (`RetFrame` is `∃ ct s0`, the restart `s → s0`, then
  `RetFrameB`); `Sched.JPlaced.retypeG`: `JPlaced.retype` from them (a copy
  of its proof: the restart's facts there were unused but for the outcome).
* `RetPostB`: `RetPost` without the restart; `retype_body`: `retype_full`
  packaged as it (`retype_cont_all` after the restart).
* `JAtZ.free_dead`: the objects meeting a range in a RAM untyped's free part
  are in the dead set (`RegionUnrefJ`'s premise).
* `JAtZ.create_noresetB`: `JAtZ.create_noresetW` from one `JAtZ` state, the
  kept-reference facts (`KeptRefsP3`, `DbgTimerKept`) at that state.
-/
import Fl4Proofs.P3.UtEpJ
import Fl4Proofs.P3.UtResetZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P3 Fl4Proofs.P1 Classical

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **`RetFrame` after its restart** (`RetFrame` is `∃ ct s0`, the restart
`s → s0`, and this): the retype's frame from a state `s0`, the source cap
read at `s` in the reset branch. With `s0 = s` it is the frame of a retype
that starts after the restart (and the reset), handoff/utj.md Round 13. -/
def RetFrameB {A' : Type} (arI : machine.Arch A') (ar : A')
    (th th' : TypedHeap) (G : MdbGhost) (s s0 : S) (x : U64) (A k win A0 k0 w0 : Nat) (pml4 T Z : Prop)
    (tK : Nat → Prop) (us : Nat) (cj : Nat → capability.Cap) (dv : Bool) (dslot : Nat → U64) (RB : Prop)
    (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  ((res.1 = .Err .Preempted ∧ untyped.reset_untyped st arI s0 ar x = ok res) ∨
     (res.1 = .Ok () ∧ (A = A0 ∧ k = k0 ∧ win = w0 ∧ A % k = 0) ∧ ∃ sR thR lo hi,
       ((sR = s0 ∧ thR = th ∧ lo = A ∧ hi = A + win * k ∧ (RB → (∃ p sb d, capAt (L.mem s0) x = ok (.Untyped p sb 0#u64 d)) ∧
          untyped.reset_untyped st arI s0 ar x = ok (.Ok (), s0, ar))) ∨
        ∃ a1 p sb fi d, untyped.reset_untyped st arI s0 ar x = ok (.Ok (), sR, a1) ∧
          capAt (L.mem s0) x = ok (.Untyped p sb fi d) ∧ capAt (L.mem s) x = ok (.Untyped p sb fi d) ∧ p.val % 8 = 0 ∧ 4 ≤ sb.val ∧
          x ∈ G.chains.flatten ∧ (∀ y, ¬ Mdb.Desc G.par y x) ∧ lo = p.val ∧ hi = p.val + 2 ^ sb.val ∧
          thR = restrictTh th lo hi ∧ RB) ∧
       lo ≤ A ∧ A + win * k ≤ hi ∧ RegionFree thR lo hi ∧
       (∀ a, IsSlot thR a → IsSlot th a) ∧ (∃ n0, tK n0 ∧ ThX thR th' A k win n0 us ∧ ∃ uu : U64, uu.val = us ∧ cj = cjOf n0 uu dv A k) ∧ DslotC th dslot win ∧
       WFrame (L := L) sR res.2.1 (fun v => ((T ∧ TcbLoopW thR A win (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)
         (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan thR v) ∨
         (pml4 ∧ A ≤ v.val ∧ v.val < A + win * k)) ∧
       (Z → WinZero (L.mem res.2.1) A k win T) ∧
       (T → L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS) = 0#u64 ∨ th (L.mem sR (L.nodeAt sR 0#u64 layout.node.DEBUG_TCBS)) = some .tcb)))

/-- `RetFrameB` for an untyped invocation (as `RetFrameI`). -/
def RetFrameIB {A' : Type} (arI : machine.Arch A') (ar : A')
    (th : TypedHeap) (G : MdbGhost) (s s0 : S) (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (inv : Fl4Spec.UntypedInvocation)
    (A k win : Nat) (dslot : Nat → U64) (cj : Nat → capability.Cap) (th' : TypedHeap) (res : core.result.Result Unit error.Exc × S × A') :
    Prop :=
  match inv with
  | .retype sl rs _ rb t us slots dev => RetFrameB (L := L) arI ar th th' G s s0 (cslotAddr sl) A k win rb.toNat
      (2 ^ bitsApi t us) slots.length (t = .archObject .pml4Obj)
      (t = .tcbObject) (dev = false ∧ t ≠ .archObject .pml4Obj) (fun n0 => objTypeOf n0 = some t) us cj dev dslot
      (rs = true) res ∧
    (res.1 = .Ok () → ∀ j, j < win → isUt (cj j) = true → t = .untyped)

/-- **`RetPostN` after its restart**: the invocation run from `σ1` (the
spec's state after the restart, or any state the retype starts from), the
frame `RetFrameIB` from `s0`; `σ` is the state `FinInv` is read at. -/
def RetPostNB {A' : Type} (th : TypedHeap) (m : U64 → U64) (G : MdbGhost) (σ σ1 : Fl4Spec.State Unit)
    (arI : machine.Arch A') (ar : A') (s s0 : S)
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (ks : U64)
    (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  NSat (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 (fun _ => True) ∧
    ∃ e σ' G' th', ((res.1 = .Ok () ∧ e = .ok ()) ∨ (res.1 = .Err .Preempted ∧ e = .error ())) ∧
      NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 (fun y => y.1 = e ∧ KSame σ' y.2) ∧
      Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
      MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
      UtInv (L.mem res.2.1) G' ∧ MdbStep m G (L.mem res.2.1) G' ∧
      (FinInv th m σ G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = ks ∧
      ∃ A k w dslot cj, RetExp th th' m (L.mem res.2.1) G G' A k w dslot cj (invSrc inv) ∧
        RetFrameIB (L := L) arI ar th G s s0 bitsApi inv A k w dslot cj th' res

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
/-- **`JPlaced.retype` after its restart**: the same from `RetPostNB` (the run
from `σ1`, `KSz σ σ1`; the frame from `s0`), so also for a retype that
starts after the restart and the reset (handoff/utj.md Round 13). -/
theorem JPlaced.retypeGS {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs Tr C : Set U64} {s : S}
    {σ : Fl4Spec.State Unit} {A' : Type} {arI : machine.Arch A'} {ar : A'}
    {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A'}
    (hJP : JPlaced (L := L) th H Tr C s σ) (hJ : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G)
    (hI : MdbInv (L.mem s) G) (hM : MdbLinks th (L.mem s) G)
    {σ1 : Fl4Spec.State Unit} {s0 : S} (hksz : KSz σ σ1)
    (hRP : RetPostNB (L := L) th (L.mem s) G σ σ1 arI ar s s0 bitsApi (L.ksb s) (.retype sl rs pb rb t us slots dev) res)
    (hok : res.1 = .Ok ())
    (n : Nat) (hnT : objTypeOf n = some t) (hn13 : n ≤ 13)
    (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ 2 ^ bitsApi t us)
    (hlt : ∀ kd, newKind n us = some kd → kd.bits < 64) (hsc7 : ∀ z, newKind n us = some (.sc z) → 7 ≤ z)
    (hdevT : n = 1 → dev = false) (hz1 : n = 1 → 2 ^ bitsApi t us = 4096)
    (hka : (L.ksb s).val % 8 = 0) (hnf : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64)
    (hcurT : ∀ ct, sched.cur_thread st s = ok ct → th ct = some .tcb)
    (hL : IntLayout th (L.ksb s))
    (hgc : ∀ y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1,
      ∀ o sz cs y0 n0, σ.kheap o = some (.cnode sz cs) → ¬ Fl4Spec.wellFormedCnodeN sz cs →
        y.2.kheap o ≠ some (.schedContext y0 n0))
    {p0 sb0 fi0 : U64} {d0 : Bool} (hcs0 : capV (L.mem s) (cslotAddr sl) = .Untyped p0 sb0 fi0 d0)
    (hk0 : p0.val + 2 ^ sb0.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p0.val)
    (hSF0 : ∀ o ko, σ.kheap o = some ko →
      (o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p0.val ∨ p0.val + 2 ^ sb0.val ≤ o.toNat) ∨
      (p0.val ≤ o.toNat ∧ o.toNat + 2 ^ Fl4Spec.objBits ko ≤ p0.val + fi0.val))
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap d0 p0.bv sb0.val fi0.val, σ1)}, False))
    (hbelow : rs = false → p0.val + fi0.val ≤ rb.toNat) (hdevS : n = 5 → d0 = false)
    (hiw : idleScW (L := L) res.2.1 = idleScW (L := L) s) :
    ∃ (th' : TypedHeap) (σ' : Fl4Spec.State Unit) (A k w lo hi : Nat),
      A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧ lo ≤ A ∧ A + w * k ≤ hi ∧
      ((lo = A ∧ hi = A + w * k) ∨ ∃ (sR : S) (a1 : A') (p sb fi : U64) (d : Bool),
        untyped.reset_untyped st arI s0 ar (cslotAddr sl) = ok (.Ok (), sR, a1) ∧
        capAt (L.mem s0) (cslotAddr sl) = ok (.Untyped p sb fi d) ∧ lo = p.val ∧ hi = p.val + 2 ^ sb.val ∧ rs = true) ∧
      NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1
          (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
      (rs = false → ThX th th' A k w n us) ∧
      ∀ H' : Heap, HOut H H' lo hi A k w (newKind n us) →
        JPlaced (L := L) th' H' {q | q ∈ Tr ∨ th' q = some .tcb}
          {c | c ∈ C ∨ (c ≠ 0#u64 ∧ ∃ y n', σ'.kheap c.bv = some (.schedContext y n'))} res.2.1 σ' := by
  obtain ⟨-, e, σ', G', th', he, hhas, hP', -, -, hM', -, -, -, -, -, hks, A, k, w, dslot, cj, hE,
    hbr, hut⟩ := hRP
  rcases hbr with ⟨e, -⟩ | ⟨-, ⟨eA, ek, ew, hAk⟩, sR, thR, lo, hi, hor, hlo, hhi, hRF, hsl,
    ⟨n0, hn0, hthx, uu, huu, hcjE⟩, hdsC, hW, hWZ, hHd⟩
  · rw [hok] at e; cases e
  have e0 := objTypeOf_inj hn0 hnT
  subst n0
  have hk1 := hE.k1
  -- the dropped region is uncovered
  have hunc : ∀ a b, a < b → Covered (L.mem s) G a b → b ≤ lo ∨ hi ≤ a := by
    rcases hor with ⟨-, -, rfl, rfl, -⟩ | ⟨a1, p, sb, fi, d, hr, hc, hcs, hp8, hsb4, hxG, hnd, rfl, rfl, -, -⟩
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
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := le_trans (Nat.le_add_right _ _) hnf
  have hSA : layout.node.SCHED_ACTION.val = 16 := by unfold layout.node.SCHED_ACTION; rfl
  have hDB : layout.node.DEBUG_TCBS.val = 88 := by unfold layout.node.DEBUG_TCBS; rfl
  have hCT : layout.node.CUR_TIME.val = 48 := by unfold layout.node.CUR_TIME; rfl
  have hCO : layout.node.CONSUMED.val = 40 := by unfold layout.node.CONSUMED; rfl
  have hWU : layout.ks.WORK_UNITS.val = 40 := by unfold layout.ks.WORK_UNITS; rfl
  have hUt : ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV (L.mem s) x = .Untyped p sb fi false →
      ∀ v : U64, (L.ksb s).val + 1248 ≤ v.val → v.val < (L.ksb s).val + 5344 →
      ¬ (p.val ≤ v.val ∧ v.val < p.val + 2 ^ sb.val) := fun x hx p sb fi hc v h1 h2 hin => by
    rcases (hJ.ks x hx p sb fi hc).1 with e | e <;> omega
  have hNd : ∀ (s1 : S) (c off : U64), L.ksb s1 = L.ksb s → c.val ≤ (L.cpu s).val → off.val < 4288 →
      (L.ksb s).val + 13568 ≤ (L.nodeAt s1 c off).val := fun s1 c off hk hc ho => node_ge hnf hk hc ho
  have hT4 : t = .tcbObject → k = 4096 := fun hT => by rw [ek]; exact hz1 (objTypeOf_tcb (hT ▸ hnT))
  -- the dropped region and the window: in the source RAM untyped's region, off the kernel-state block
  have hreg : hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo := by
    obtain ⟨hxG, p1, sb1, fi1', fi2, d1, e0, -, hpA, -, hAs, -, -⟩ := hE.usrc
    have e0' : capV (L.mem s) (cslotAddr sl) = .Untyped p1 sb1 fi1' d1 := e0
    have hxG : cslotAddr sl ∈ G.chains.flatten := hxG
    rw [hcs0] at e0'; cases e0'
    have hk := hk0
    rcases hor with ⟨-, -, rfl, rfl, -⟩ | ⟨a1, p, sb, fi, d, hr, hc, hcs, -, -, -, -, rfl, rfl, -, -⟩
    · omega
    · have hcv' := capV_of_capAt hcs
      rw [hcs0] at hcv'; cases hcv'
      omega
  -- the spec's SCs after: old ones outside the region, or new ones of the window
  have hscO : ∀ (c : U64) y n', c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n') →
      (∃ y0, σ.kheap c.bv = some (.schedContext y0 n') ∧
        ((c.val + 2 ^ (Fl4Spec.minSchedContextBits + n') ≤ lo ∨ hi ≤ c.val) ∧ ¬ NewAt A k w c)) ∨
      (t = .schedContextObject ∧ n' = us - Fl4Spec.minSchedContextBits ∧ NewAt A k w c) := by
    intro c yc n' hc0 hk
    obtain ⟨y0, hy0, hy01, hK⟩ := hhas
    have hy0ok : y0.1 = .ok () := by
      rcases he with ⟨-, h⟩ | ⟨h, -⟩
      · rw [hy01, h]
      · rw [hok] at h; cases h
    obtain ⟨-, hkh⟩ := invokeUntyped_kheap bitsApi sl rs pb rb t us slots dev σ1 hg y0 hy0
    rw [← hK.1] at hk
    obtain ⟨hxG, p1, sb1, fi1', fi2, d1, e0, -, hpA, -, hAs, -, -⟩ := hE.usrc
    have e0' : capV (L.mem s) (cslotAddr sl) = .Untyped p1 sb1 fi1' d1 := e0
    have hxG : cslotAddr sl ∈ G.chains.flatten := hxG
    rw [hcs0] at e0'; cases e0'
    rcases hkh c.bv _ hk with ⟨ko1, h1, e1, hR⟩ | ⟨ht, hm, cd, ecd⟩
    · obtain ⟨ko0, h0, e00⟩ := hksz c.bv ko1 h1
      have hty := e00.trans e1
      rcases sc_of_aType hty with ⟨y00, rfl⟩ | ⟨sz, cs, rfl, hnw⟩
      swap; · exact absurd hk (hgc y0 hy0 _ _ _ _ _ h0 hnw)
      left
      refine ⟨y00, h0, ?_⟩
      have hOW := old_windowP hU hxG hcs0 hSF0 h0 hR (A := A) (fun hr => by rw [eA]; exact hbelow hr)
      simp only [Fl4Spec.objBits] at hOW
      have hcv : c.bv.toNat = c.val := rfl
      rw [hcv] at hOW
      have hnw : ¬ NewAt A k w c := by
        intro hn; obtain ⟨j, hj, hv, h1', h2'⟩ := newAt_val hn hk1
        have := Nat.one_le_two_pow (n := Fl4Spec.minSchedContextBits + n')
        rcases hOW with (e | e) | ⟨-, -, e⟩ <;> omega
      refine ⟨?_, hnw⟩
      rcases hor with ⟨-, -, rfl, rfl, -⟩ | ⟨a1, p, sb, fi, d, hr, hc, hcs, -, -, -, -, rfl, rfl, -, hrsT⟩
      · rcases hOW with (e | e) | ⟨-, -, e⟩
        · left; omega
        · right; omega
        · left; omega
      · have hcv' := capV_of_capAt hcs
        rw [hcs0] at hcv'; cases hcv'
        rcases hOW with e | ⟨hr', -⟩
        · exact e
        · rw [hrsT] at hr'; cases hr'
    · have hsc := sc_of_default ecd ht
      right
      refine ⟨hsc.1, hsc.2, ?_⟩
      by_cases hy1 : y0.1 = .ok ()
      swap; · exact absurd hy0ok hy1
      rw [if_pos hy1] at hm
      obtain ⟨j, hj, hjc⟩ := regionPtrs_mem hm
      refine ⟨j, by rw [ew]; exact hj, ?_⟩
      have hjk : j * k + k ≤ w * k := by
        have := Nat.mul_le_mul_right k (show j + 1 ≤ w by rw [ew]; omega); rw [Nat.add_mul, Nat.one_mul] at this; exact this
      have hfit' : p0.val + 2 ^ sb0.val ≤ 2 ^ 64 := by
        have hreg := hU.reg _ hxG (by rw [hcs0]; exact physF_ut _ _ _ _)
        rw [hcs0] at hreg
        exact (ut_range (capV_ut_sb hcs0) hreg).2.2
      have : c.bv.toNat = A + j * k := by
        rw [hjc, eA, ← ek]; exact ptrAdd_toNat (by rw [← eA]; omega)
      exact this
  refine ⟨th', σ', A, k, w, lo, hi, eA, ek, ew, hlo, hhi, ?_, ?_, fun hrs => ?_, fun H' hO => ?_⟩
  · rcases hor with ⟨-, -, h1, h2, -⟩ | ⟨a1, p, sb, fi, d, hr, hc, -, -, -, -, -, h1, h2, -, hRB⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨sR, a1, p, sb, fi, d, hr, hc, h1, h2, hRB⟩
  · rcases he with ⟨-, rfl⟩ | ⟨h, -⟩
    · exact hhas
    · rw [hok] at h; cases h
  · rcases hor with ⟨-, rfl, -, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hRB⟩
    · exact hthx
    · rw [hrs] at hRB; cases hRB
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
    rcases hor with ⟨-, rfl, -, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩
    · exact ⟨hq, by omega⟩
    · exact ⟨(restrictTh_some hq).1, by omega⟩
  have hthR' : ∀ q kd, th q = some kd → ¬ (lo ≤ q.val ∧ q.val < hi) → thR q = some kd := by
    intro q kd hq hout
    rcases hor with ⟨-, rfl, -, -⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, rfl, -⟩
    · exact hq
    · rw [restrictTh_out hout]; exact hq
  have hth' := hthx.1
  have hout_new : ∀ q, NewAt A k w q → lo ≤ q.val ∧ q.val < hi := fun q hn => by
    obtain ⟨j, hj, hv, h1, h2⟩ := newAt_val hn hk1; omega
  have hks' : L.ksb res.2.1 = L.ksb s := hks
  have hSC : ∀ (c : U64) y n', c ≠ 0#u64 → σ'.kheap c.bv = some (.schedContext y n') →
      H' c = some (.sc (n' + Fl4Spec.minSchedContextBits)) := by
    intro c y n' hc hk
    rcases hscO c y n' hc hk with ⟨y0, h0, hout, hnw⟩ | ⟨ht, hn', hnw⟩
    · have hH := (hJP.sc c y0 n' hc h0).2
      have n1 : ¬ (NewAt A k w c ∧ (newKind n us).isSome) := fun ⟨h, _⟩ => hnw h
      have n2 : ¬ ∃ kd', H c = some kd' ∧ MeetsR lo hi c.val (c.val + 2 ^ kd'.bits) := by
        rintro ⟨kd', hk', hm'⟩; rw [hH] at hk'; cases hk'
        unfold MeetsR at hm'; simp only [HKind.bits] at hm'
        rw [Nat.add_comm n'] at hm'; omega
      rw [hO c, if_neg n1, if_neg n2]; exact hH
    · subst ht
      have h5 : n = 5 := objTypeOf_inj hnT (by rfl)
      subst h5
      have hz := hsc7 us (by simp [newKind])
      rw [hO c, if_pos ⟨hnw, by simp [newKind]⟩]
      simp only [newKind]; simp; rw [hn']; unfold Fl4Spec.minSchedContextBits; omega
  have htyped : ∀ a, IsSlot th' a → CapTyped H' (Heap.replies H') (Heap.ntfns H') (capV (L.mem res.2.1) a) := by
    intro a ha
    by_cases hm : a ∈ G'.chains.flatten
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
  refine ⟨heapOK_out hJP.heap hO hlo hhi hk1 hAk (fun kd hK => ?_) hfit hlt hsc7, hP', fun q => ⟨fun h => ?_, fun h => ?_⟩,
    fun p r h => ?_, fun q h => Or.inr h,
    fun c y n' hc hk => ⟨Or.inr ⟨hc, y, n', hk⟩, hSC c y n' hc hk⟩, fun p kd hp hko => ?_, fun p z hp => ?_,
    fun a ha => ?_, fun i hi128 => ?_, fun t' ht' => ?_, fun t' ht' => ?_,
    fun a ha => ?_⟩
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
    · obtain ⟨hx0, p0', sb0', fi0', fi1, d0', hc0, -, h1, -, h2, -, -⟩ := hE.usrc
      have e0' : capV (L.mem s) (cslotAddr sl) = .Untyped p0' sb0' fi0' d0' := hc0
      rw [hcs0] at e0'
      simp only [capability.Cap.Untyped.injEq] at e0'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e0'
      obtain ⟨j, hj, hv, ha1, ha2⟩ := newAt_val hn hk1
      have hb := hbits kd hK
      rw [← hRk] at hb
      rcases hk0 with e | e
      · left; omega
      · right; omega
    · exact hJP.ks p kd hH hko
  · rw [hks']
    rcases hO.some hp with ⟨hn, hK⟩ | ⟨hH, -⟩
    · obtain ⟨hx0, p0', sb0', fi0', fi1, d0', hc0, -, h1, -, h2, -, -⟩ := hE.usrc
      have e0' : capV (L.mem s) (cslotAddr sl) = .Untyped p0' sb0' fi0' d0' := hc0
      rw [hcs0] at e0'
      simp only [capability.Cap.Untyped.injEq] at e0'
      obtain ⟨rfl, rfl, rfl, rfl⟩ := e0'
      obtain ⟨j, hj, hv, ha1, ha2⟩ := newAt_val hn hk1
      have hb := hbits _ hK
      rw [← hRk] at hb
      simp only [HKind.bits] at hb
      rcases hk0 with e | e
      · left; omega
      · right; left; omega
    · exact hJP.ksIn p z hH
  -- the slots' caps
  · exact htyped a ha
  -- the IRQ slots: slots of the typed heap after (`IntLayout`, the region off the kernel-state block)
  · rw [hks']
    have hv := nodeA_val hkf hi128
    have hout : ¬ (lo ≤ (nodeA (L.ksb s) i).val ∧ (nodeA (L.ksb s) i).val < hi) := by rw [hv]; omega
    have hth1 : th' (nodeA (L.ksb s) i) = some (.cnode 0) := by
      rw [hth' _, if_neg (fun ⟨hn, _⟩ => hout (hout_new _ hn))]
      exact hthR' _ _ (hL.node i hi128) hout
    have hA : AbsSlot th' ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl (by simpa using hth1)⟩
    have hS := hA.isSlot
    rw [cslotAddr_nil] at hS
    exact htyped _ hS
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
  -- the IPC-buffer slots
  · obtain ⟨p3, i3, hi3, hp3, ha3⟩ := (show AbsSlot th' (t'.bv, Fl4Spec.tcbCnodeIndex 2) from
      ⟨t', rfl, Or.inr ⟨ht', 2, by decide, rfl⟩⟩).at
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
      generalize hadef : cslotAddr (p3.bv, Fl4Spec.tcbCnodeIndex 2) = a at ha3 ⊢
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
      have has : AbsSlot th (p3.bv, Fl4Spec.tcbCnodeIndex 2) := ⟨p3, rfl, Or.inr ⟨hth, 2, by decide, rfl⟩⟩
      by_cases hm : cslotAddr (p3.bv, Fl4Spec.tcbCnodeIndex 2) ∈ G'.chains.flatten
      · rcases hE.gmem _ hm with ha0 | ⟨j, hj, hj'⟩
        · rcases hJP.bfs p3 hth with e | ⟨q0, sz0, r0, m0, e0, a0, v0, e⟩
          · obtain ⟨-, c, hc, hcn⟩ := (hM.members _).1 ha0
            rw [capAt_capV] at hc; have hc' := eq_of_ok_eq hc; rw [e] at hc'; exact absurd hc'.symm hcn
          · have hu : isUt (capV (L.mem s) (cslotAddr (p3.bv, Fl4Spec.tcbCnodeIndex 2))) = false := by rw [e]; rfl
            right; rw [(hE.keep _ ha0 hu).2, e]; exact ⟨q0, sz0, r0, m0, e0, a0, v0, rfl⟩
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
  -- the slots' EPT and frame caps' objects
  · clear hUt
    by_cases hm : a ∈ G'.chains.flatten
    · rcases hE.gmem a hm with ha0 | ⟨j, hj, rfl⟩
      · cases hu : isUt (capV (L.mem s) a)
        · obtain ⟨-, e⟩ := hE.keep a ha0 hu
          rw [e]
          have hC := hJP.cobj a ((hM.members a).1 ha0).1
          -- an apartness from `H`'s objects carries over: the cap's own range is
          -- covered, so it misses the dropped region and the new objects
          have hkeepA : ∀ c, capV (L.mem s) a = c → physF c = true → FrApartH H c → FrApartH H' c := by
            intro c hc hp hA q kq hq hkq
            have hbt := hU.reg a ha0 (by rw [hc]; exact hp)
            rw [hc] at hbt
            have hcv := hunc (baseF c) (topF c + 1) (by omega) ⟨a, ha0, by rw [hc]; exact hp, hu, by rw [hc], by rw [hc]⟩
            rw [hO q] at hq
            split_ifs at hq with h1 h2
            · obtain ⟨j, hj, hv, ha1, ha2⟩ := newAt_val h1.1 hk1
              have hb := hbits kq hq
              rw [← hRk] at hb
              have hb1 : 1 ≤ 2 ^ kq.bits := Nat.one_le_two_pow
              omega
            · exact hA q kq hq hkq
          cases hc : capV (L.mem s) a with
          | Ept p lv m' a' va =>
            rw [hc] at hC
            obtain ⟨⟨n2, hH, hb, ht⟩, hA⟩ := hC
            have hp : physF (.Ept p lv m' a' va) = true := ok_inj (phys_eq _).symm
            exact ⟨⟨n2, hkeepH p _ hH ⟨a, ha0, by rw [hc]; exact hp, hu, by rw [hc]; exact hb,
              by rw [hc]; simp only [HKind.bits]; exact ht⟩, hb, ht⟩, hkeepA _ hc hp hA⟩
          | Frame p sz r d m' ep a' va =>
            rw [hc] at hC
            exact hkeepA _ hc (ok_inj (phys_eq _).symm) hC
          | PageTable p m' a' va =>
            rw [hc] at hC
            exact hkeepA _ hc (ok_inj (phys_eq _).symm) hC
          | PageDirectory p m' a' va =>
            rw [hc] at hC
            exact hkeepA _ hc (ok_inj (phys_eq _).symm) hC
          | Pdpt p m' a' va =>
            rw [hc] at hC
            exact hkeepA _ hc (ok_inj (phys_eq _).symm) hC
          | Pml4 p m' a' =>
            rw [hc] at hC
            exact hkeepA _ hc (ok_inj (phys_eq _).symm) hC
          | SchedContext p sb =>
            rw [hc] at hC
            obtain ⟨hH, hpi⟩ := hC
            have hfit := hJP.heap.fits p _ hH
            have hlt := hJP.heap.lt64 p _ hH
            simp only [HKind.bits] at hfit hlt
            exact ⟨hkeepH p _ hH (covered_of_cap ha0 hc (ok_inj (phys_eq _).symm) rfl
              (capRange (b := sb) (ok_inj (ptr_eq _).symm)
                (ok_inj (by rw [← size_eq]; simp [objects.cap_size_bits])) hlt hfit)), by rw [hiw]; exact hpi⟩
          | _ => trivial
        · obtain ⟨q, sz, f, d, e⟩ := isUt_iff.1 (hE.utk a ha0 hu)
          rw [e]; trivial
      · rw [hE.newc j hj]
        have hb := hE.cbase j hj
        have ht := hE.ctop j hj
        have hnk : ∀ p sz r d m' ep a' va, cj j = .Frame p sz r d m' ep a' va →
            ∀ kd, newKind n us = some kd → ∃ z, kd = .other z := by
          intro p sz r d m' ep a' va hc kd hk
          rw [hcjE] at hc; unfold cjOf at hc
          exact newKind_other_of (by have := newCapOf_frame hc; omega) hk
        -- a new table's object is an `other` one too
        have hnkT : ∀ p m' a' va, (cj j = .PageTable p m' a' va ∨ cj j = .PageDirectory p m' a' va ∨
            cj j = .Pdpt p m' a' va) → ∀ kd, newKind n us = some kd → ∃ z, kd = .other z := by
          intro p m' a' va hc kd hk
          rw [hcjE] at hc; unfold cjOf at hc
          exact newKind_other_of (by have := newCapOf_tab hc; omega) hk
        -- (f1) a new PML4's object is an `other` one too (type 8, `newCapOf_pml4`)
        have hnkP : ∀ p m' a', cj j = .Pml4 p m' a' → ∀ kd, newKind n us = some kd → ∃ z, kd = .other z := by
          intro p m' a' hc kd hk
          rw [hcjE] at hc; unfold cjOf at hc
          exact newKind_other_of (by have := newCapOf_pml4 hc; omega) hk
        have hfrT : ∀ c', cj j = c' → (∀ kd, newKind n us = some kd → ∃ z, kd = .other z) →
            FrApartH H' c' := by
          intro c' hc hK q kq hq hkq
          have hb' := hb
          have ht' := ht
          rw [hc] at hb' ht'
          rw [hO q] at hq
          split_ifs at hq with h1 h2
          · obtain ⟨z, rfl⟩ := hK kq hq; exact absurd rfl (hkq z)
          · have hm' : ¬ MeetsR lo hi q.val (q.val + 2 ^ kq.bits) := fun hm' => h2 ⟨kq, hq, hm'⟩
            unfold MeetsR at hm'
            have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
            rw [Nat.add_mul, Nat.one_mul] at this
            rw [hb', ht']; omega
        have hne : ∀ p lv m' a' va, cj j ≠ .Ept p lv m' a' va := by
          intro p lv m' a' va hc
          rw [hcjE] at hc; unfold cjOf at hc
          exact newCapOf_ne_ept hc
        cases hc : cj j with
        | Ept p lv m' a' va => exact absurd hc (hne p lv m' a' va)
        | Frame p sz r d m' ep a' va =>
          have hK := hnk p sz r d m' ep a' va hc
          rw [hc] at hb ht
          intro q kq hq hkq
          rw [hO q] at hq
          split_ifs at hq with h1 h2
          · obtain ⟨z, rfl⟩ := hK kq hq; exact absurd rfl (hkq z)
          · have hm' : ¬ MeetsR lo hi q.val (q.val + 2 ^ kq.bits) := fun hm' => h2 ⟨kq, hq, hm'⟩
            unfold MeetsR at hm'
            have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
            rw [Nat.add_mul, Nat.one_mul] at this
            rw [hb, ht]; omega
        | PageTable p m' a' va => exact hfrT _ hc (hnkT p m' a' va (Or.inl hc))
        | PageDirectory p m' a' va => exact hfrT _ hc (hnkT p m' a' va (Or.inr (Or.inl hc)))
        | Pdpt p m' a' va => exact hfrT _ hc (hnkT p m' a' va (Or.inr (Or.inr hc)))
        | Pml4 p m' a' => exact hfrT _ hc (hnkP p m' a' hc)
        | SchedContext p sb =>
          -- a new SC: `H'`'s at the window's slot, of the cap's size, in the
          -- source (RAM) untyped's region, so not the idle SC (`IdleOut`)
          have hsc := newCapOf_sc (by rw [hcjE] at hc; unfold cjOf at hc; exact hc)
          obtain ⟨rfl, rfl, rfl⟩ := hsc
          have hlt' : A + j * k < 2 ^ 64 := by
            have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
            rw [Nat.add_mul, Nat.one_mul] at this; omega
          have hv : (⟨BitVec.ofNat 64 (A + j * k)⟩ : U64).val = A + j * k := by
            show (BitVec.ofNat 64 (A + j * k)).toNat = _; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt']
          refine ⟨hOut_newSc hO huu hj hv, fun hi => ?_⟩
          obtain ⟨hxG, p1, sb1, fi1', fi2, d1, e0, -, hpA, -, hAs, -, -⟩ := hE.usrc
          have e0' : capV (L.mem s) (cslotAddr sl) = .Untyped p1 sb1 fi1' d1 := e0
          rw [hcs0] at e0'
          simp only [capability.Cap.Untyped.injEq] at e0'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := e0'
          have hd : d0 = false := hdevS rfl
          subst hd
          have hI := (hJ.idleOut _ hxG _ _ _ hcs0 _ (Or.inr (hi.trans hiw))).1
          have : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
          rw [Nat.add_mul, Nat.one_mul] at this
          rw [hv] at hI; omega
        | _ => trivial
    · have hnull : capV (L.mem res.2.1) a = .Null := by
        by_contra hne
        exact hm ((hM'.members a).2 ⟨ha, _, capAt_capV _ _, hne⟩)
      rw [hnull]; trivial

/-- **`JPlaced.retypeGS` for a RAM source**: the source's kernel-state-block
apartness from `JCovD.ks`, its spec-object fact from `SpecFree`. -/
theorem JPlaced.retypeG {th : TypedHeap} {H : Heap} {G : MdbGhost} {D Cs Tr C : Set U64} {s : S}
    {σ : Fl4Spec.State Unit} {A' : Type} {arI : machine.Arch A'} {ar : A'}
    {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {sl : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef}
    {t : Fl4Spec.ApiObjectType} {us : Nat} {slots : List Fl4Spec.CslotPtr} {dev : Bool}
    {res : core.result.Result Unit error.Exc × S × A'}
    (hJP : JPlaced (L := L) th H Tr C s σ) (hJ : JCovD (L := L) th H G D Cs s) (hU : UtInv (L.mem s) G)
    (hI : MdbInv (L.mem s) G) (hM : MdbLinks th (L.mem s) G)
    {σ1 : Fl4Spec.State Unit} {s0 : S} (hksz : KSz σ σ1)
    (hRP : RetPostNB (L := L) th (L.mem s) G σ σ1 arI ar s s0 bitsApi (L.ksb s) (.retype sl rs pb rb t us slots dev) res)
    (hok : res.1 = .Ok ())
    (n : Nat) (hnT : objTypeOf n = some t) (hn13 : n ≤ 13)
    (hbits : ∀ kd, newKind n us = some kd → 2 ^ kd.bits ≤ 2 ^ bitsApi t us)
    (hlt : ∀ kd, newKind n us = some kd → kd.bits < 64) (hsc7 : ∀ z, newKind n us = some (.sc z) → 7 ≤ z)
    (hdevT : n = 1 → dev = false) (hz1 : n = 1 → 2 ^ bitsApi t us = 4096)
    (hka : (L.ksb s).val % 8 = 0) (hnf : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64)
    (hcurT : ∀ ct, sched.cur_thread st s = ok ct → th ct = some .tcb)
    (hL : IntLayout th (L.ksb s))
    (hSF : SpecFree (L.mem s) G σ)
    (hgc : ∀ y ∈ ((Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1).1,
      ∀ o sz cs y0 n0, σ.kheap o = some (.cnode sz cs) → ¬ Fl4Spec.wellFormedCnodeN sz cs →
        y.2.kheap o ≠ some (.schedContext y0 n0))
    {p0 sb0 fi0 : U64} {d0 : Bool} (hcs0 : capV (L.mem s) (cslotAddr sl) = .Untyped p0 sb0 fi0 d0) (hd0 : d0 = false)
    (hg : Fl4Spec.getCap (Z := Unit) sl σ1 = ({(.untypedCap d0 p0.bv sb0.val fi0.val, σ1)}, False))
    (hbelow : rs = false → p0.val + fi0.val ≤ rb.toNat) (hdevS : n = 5 → d0 = false)
    (hiw : idleScW (L := L) res.2.1 = idleScW (L := L) s) :
    ∃ (th' : TypedHeap) (σ' : Fl4Spec.State Unit) (A k w lo hi : Nat),
      A = rb.toNat ∧ k = 2 ^ bitsApi t us ∧ w = slots.length ∧ lo ≤ A ∧ A + w * k ≤ hi ∧
      ((lo = A ∧ hi = A + w * k) ∨ ∃ (sR : S) (a1 : A') (p sb fi : U64) (d : Bool),
        untyped.reset_untyped st arI s0 ar (cslotAddr sl) = ok (.Ok (), sR, a1) ∧
        capAt (L.mem s0) (cslotAddr sl) = ok (.Untyped p sb fi d) ∧ lo = p.val ∧ hi = p.val + 2 ^ sb.val ∧ rs = true) ∧
      NHas (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi (.retype sl rs pb rb t us slots dev)).run σ1
          (fun y => y.1 = .ok () ∧ KSame σ' y.2) ∧
      (rs = false → ThX th th' A k w n us) ∧
      ∀ H' : Heap, HOut H H' lo hi A k w (newKind n us) →
        JPlaced (L := L) th' H' {q | q ∈ Tr ∨ th' q = some .tcb}
          {c | c ∈ C ∨ (c ≠ 0#u64 ∧ ∃ y n', σ'.kheap c.bv = some (.schedContext y n'))} res.2.1 σ' := by
  have hxG : cslotAddr sl ∈ G.chains.flatten := by
    obtain ⟨-, e, σ', G', th', he, hhas, hP', -, -, hM', -, -, -, -, -, hks, A, k, w, dslot, cj, hE, hbr⟩ := hRP
    exact hE.usrc.1
  have hc' : capV (L.mem s) (cslotAddr sl) = .Untyped p0 sb0 fi0 false := by rw [hcs0, hd0]
  exact JPlaced.retypeGS hJP hJ hU hI hM hksz hRP hok n hnT hn13 hbits hlt hsc7 hdevT hz1 hka hnf hcurT hL hgc
    hcs0 (hJ.ks _ hxG p0 sb0 fi0 hc').1 (fun o ko h => hSF _ hxG p0 sb0 fi0 hc' o ko h) hg hbelow hdevS hiw

end

end

end Fl4Proofs.P3.Sched

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section
/-- **`RetPost` without the restart**: the invocation's single outcome from
`σ1`, the frame from `s0` (`RetFrameIB` with `s = s0`). -/
def RetPostB {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A' : Type} (th : TypedHeap)
    (m : U64 → U64) (G : MdbGhost) (σ1 : Fl4Spec.State Unit) (ar : A')
    (arI : machine.Arch A') (s0 : S) (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat) (ks : U64)
    (inv : Fl4Spec.UntypedInvocation) (res : core.result.Result Unit error.Exc × S × A') : Prop :=
  res.1 = .Ok () ∧ res.2.2 = ar ∧
    ∃ σ' G' th', (Fl4Spec.invokeUntypedWith (Z := Unit) bitsApi inv).run σ1 = ({(.ok (), σ')}, False) ∧
      Placed th' ∧ StateRel th' (L.mem res.2.1) σ' ∧ SlotsValid th' (L.mem res.2.1) ∧
      MdbLinks th' (L.mem res.2.1) G' ∧ CdtRel th' (L.mem res.2.1) σ' G' ∧ MdbInv (L.mem res.2.1) G' ∧
      UtInv (L.mem res.2.1) G' ∧ MdbStep m G (L.mem res.2.1) G' ∧
      (FinInv th m σ1 G → FinInv th' (L.mem res.2.1) σ' G') ∧ L.ksb res.2.1 = ks ∧
      ∃ A k w dslot cj, RetExp th th' m (L.mem res.2.1) G G' A k w dslot cj (invSrc inv) ∧
        RetFrameIB (L := L) arI ar th G s0 s0 bitsApi inv A k w dslot cj th' res

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem RetPostB.toNB {A' : Type} {th : TypedHeap} {m : U64 → U64} {G : MdbGhost} {σ1 : Fl4Spec.State Unit} {ar : A'}
    {arI : machine.Arch A'} {s0 : S} {bitsApi : Fl4Spec.ApiObjectType → Nat → Nat} {ks : U64}
    {inv : Fl4Spec.UntypedInvocation} {res : core.result.Result Unit error.Exc × S × A'}
    (h : RetPostB (L := L) th m G σ1 ar arI s0 bitsApi ks inv res) :
    RetPostNB (L := L) th m G σ1 σ1 arI ar s0 s0 bitsApi ks inv res := by
  obtain ⟨h1, -, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, hE⟩ := h
  exact ⟨nsat_det hrun trivial, .ok (), σ', G', th', Or.inl ⟨h1, rfl⟩, nhas_det hrun ⟨rfl, KSame.refl _⟩,
    hP', hR', hV', hM', hC', hI', hU', hSt, hFin, hks, hE⟩

/-- **The retype without a reset from any state** (`retype_full` as
`RetPostB`): `retype_cont_all` after the restart, for a RAM untyped and the
types 0, 2..7, 9..13. -/
theorem retype_body {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat)
    (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz47 : zOf nt.val us.val ≤ 47)
    (hsc : nt.val = 5 → 7 ≤ us.val) (hct0 : nt.val = 4 → us.val ≠ 0)
    (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      RetPostB (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false) res ⦄ := by
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hn1 : nt.val ≠ 1 := by omega
  obtain ⟨hA1, hWA2, hA3, -⟩ := retype_region p fi sb.val (zOf nt.val us.val) win.val hsb (by omega) hpal hpfit hfi hw1 hmem
  have hsl : ∀ a, IsSlot th a → a.val + 32 ≤ (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ∨
      (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val ≤ a.val := by
    intro a ha
    obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
    rcases hfree q kq hq with h | h
    · left; omega
    · right; omega
  have hzA : ZeroRegion (L.mem s) (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat
      ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val) :=
    fun w hw h1 h2 => hzero w hw (by omega) (by omega)
  refine WP.spec_mono (retype_full (L := L) arI ar th s σ G hR hV hP hM hC hI hU horig hpp hidx hcap hpal hpfit
    hfi (CanonR.of_high hhigh) (fun _ => hhigh) nt us t ht hn hus hz47 hsc hct0 hdest hr off win hwin hw1 hmem hempty hfree (fun _ => hzero)
    (fun h => by cases h) bitsApi hb) ?_
  rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w,
    dslot, cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩
  exact ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt', hFin, hks, _, _, _, dslot, cj, hE,
    ⟨Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s, th, _, _,
      Or.inl ⟨rfl, rfl, rfl, rfl, fun h => by cases h⟩, le_rfl, le_rfl, hthx.2, fun a h => h,
      ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC, hWf.mono fun v hv => Or.inl (Or.inr hv),
      fun _ => winZero_of_slots hWf hzA hsl _, fun hT => absurd (objTypeOf_tcb (hT ▸ ht)) hn1⟩,
     fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩

/-- **The PML4 retype without a reset from any state** (`retype_full_pml4` as
`RetPostB`; `retype_cont_pml4R` after the restart): the new PML4s' kernel half
written, the global PML4 a spec PML4 off the region. -/
theorem retype_body_pml4 {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val)
    (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat)
    (ht : objTypeOf nt.val = some t) (hn8 : nt.val = 8) (hus : us.val < 64)
    (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hb : bitsApi t us.val = zOf nt.val us.val)
    (hgpm : HasPm σ σ.archState.x64GlobalPml4) (hga : σ.archState.x64GlobalPml4.toNat % 4096 = 0)
    (hgf : σ.archState.x64GlobalPml4.toNat + 4096 ≤ 2 ^ 64)
    (hgreg : ¬ (p.val ≤ σ.archState.x64GlobalPml4.toNat ∧ σ.archState.x64GlobalPml4.toNat < p.val + 2 ^ sb.val)) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win false ⦃ res =>
      RetPostB (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) false) res ∧
        (∀ w : U64, P1.Aligned w → (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat ≤ w.val →
          w.val < (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val →
          (w.val - (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat) % 2 ^ zOf nt.val us.val < 2048 →
          L.mem res.2.1 w = 0#u64) ⦄ := by
  have htP : t = .archObject .pml4Obj := by
    have := ht; rw [hn8] at this; simpa [objTypeOf, Fl4Spec.archDataToObjType] using this.symm
  have hsb : sb.val < 64 := capAt_untyped_inv hcap
  have hfull := retype_full_pml4 (L := L) arI ar th s σ G hR hV hP hM hC hI hU horig hpp hidx hcap hpal hpfit
    hfi hhigh nt us _ ht hn8 hus hdest hr off win hwin hw1 hmem hempty hfree hzero bitsApi (by rw [← htP]; exact hb) hgpm
    hga hgf hgreg rfl
  rw [← htP] at hfull
  have hWA2 : (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat % 2 ^ zOf nt.val us.val = 0 :=
    (retype_region p fi sb.val (zOf nt.val us.val) win.val hsb (by simp [zOf, hn8]) hpal hpfit hfi hw1 hmem).2.1
  obtain ⟨hWA1, -, hWA3, -⟩ :=
    retype_region p fi sb.val (zOf nt.val us.val) win.val hsb (by simp [zOf, hn8]) hpal hpfit hfi hw1 hmem
  refine WP.spec_mono hfull ?_
  rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w,
    dslot, cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩
  refine ⟨?_, fun w0 hw0 g1 g2 g3 => ?_⟩
  rotate_left
  · -- the new PML4s' user halves: zero before (`hzero`), written by no step
    have hns : ¬ SlotSpan th w0 := by
      rintro ⟨a, ha, a1, a2⟩
      obtain ⟨q, kq, hq, hq1, hq2, -⟩ := slot_in_object hP ha
      rcases hfree q kq hq with h | h <;> omega
    rw [hWf.2.2 w0 hw0 (by
      rintro (h | ⟨-, -, h⟩)
      · exact hns h
      · exact absurd h (Nat.not_le.2 g3))]
    exact hzero w0 hw0 (by omega) (by omega)
  exact ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt', hFin, hks, _, _, _, dslot, cj, hE,
    ⟨Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s, th, _, _,
      Or.inl ⟨rfl, rfl, rfl, rfl, fun h => by cases h⟩, le_rfl, le_rfl, hthx.2, fun a h => h,
      ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC,
      hWf.mono fun v hv => hv.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr ⟨htP, h.1, h.2.1⟩),
      fun ⟨_, hne⟩ => absurd htP hne, fun hT => absurd (htP.symm.trans hT) (by simp)⟩,
     fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The objects meeting a range in a RAM untyped's free part are dead**
(`RegionUnrefJ`'s premise; `retype_window_dead` for any such range): not
covered (`ut_free_fi`), not idle (`IdleOut`) nor in the kernel-state block
(`UtKsApart`) of the cap. -/
theorem JAtZ.free_dead {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) {x : U64} (hx : x ∈ Z.G.chains.flatten) {p sb fi : U64}
    (hcv : capV (L.mem s) x = .Untyped p sb fi false) {lo hi : Nat} (hlo : p.val + fi.val ≤ lo)
    (hhi : hi ≤ p.val + 2 ^ sb.val) : ∀ q kd, H q = some kd → RegionD H lo hi q → q ∈ D := by
  intro q kd hq hr
  unfold RegionD MeetsR at hr
  rw [hq] at hr
  simp only [Option.elim] at hr
  have io := J.jcov.idleOut x hx p sb fi hcv
  have hk := (J.jcov.ks x hx p sb fi hcv).1
  rcases J.jcov.h q kd hq with hc | hd | hi | hi
  · rcases ut_free_fi J.ut hx hcv (by have := Nat.one_le_two_pow (n := kd.bits); omega) hc with e | e <;> omega
  · exact hd
  · have := (io q hi).2.2 kd hq; omega
  · obtain ⟨k1, k2⟩ := hi.2 kd hq; omega

set_option maxHeartbeats 4000000 in
/-- **`JAtZ.create_noresetW` from one `JAtZ` state**: the creation starts at
the `JAtZ` state itself (after the restart, or after a reset), entered
(`Entered`: no switch pending, the current thread runnable); the kept objects'
and FL4's lists' references to the window's objects are the premise `hRU` at
that state (`RegionUnrefJ`'s conclusion there; no restart in between). -/
theorem JAtZ.create_noresetB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi false))
    {s' : S} {th' : TypedHeap} {G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G G' A0 k w dslot cj (cslotAddr (pp.bv, idx)))
    (hRU : KeptRefsP3 (L := L) H (RegionD H A0 (A0 + w * k)) s ∧ DbgTimerKept (L := L) H (RegionD H A0 (A0 + w * k)) Cs s)
    {n us : Nat} (hcjU : newKind n us ≠ none → ∀ j, j < w → isUt (cj j) = false)
    (hn : n ≠ 1 ∧ (n = 5 → 7 ≤ us)) (hk : k = 2 ^ zOf n us) (hAk : A0 % k = 0)
    {T pml4 : Prop} (hT : ¬ T)
    (hW : WFrame (L := L) s s' (fun v => ((T ∧ TcbLoopW Z.th A0 w (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)
      (L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) v) ∨ SlotSpan Z.th v) ∨
      (pml4 ∧ A0 ≤ v.val ∧ v.val < A0 + w * k)))
    (hWZ : (∀ z, newKind n us ≠ some (.other z)) → WinZero (L.mem s') A0 k w T) (hidl : IdleKeep (L := L) s s') :
    ∃ (H' : Heap) (Ac' : Set U64),
      BlkOK st (Heap.tcbs H') Cs (Heap.omega H') H' (Heap.frame H') (Heap.replies H') (Heap.scs H')
        (Heap.ntfns H') (Heap.scBits H') Ac' s' ∧
      HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) ∧
      JCovD (L := L) th' H' G' {q | q ∈ D ∧ ¬ NewQ A0 k w cj q} Cs s' := by
  let ex : Aeneas.Std.Array obj.Slot 3#usize := Aeneas.Std.Array.repeat 3#usize 0#u64
  have hres : σ.schedulerAction ≠ .chooseNewThread := by rw [hni.2]; simp
  have UJ := J.utJoint (extra := ex) hres hpp hidx rfl hcap (by
    intro x hx h0; exfalso; apply h0; simpa [ex, Aeneas.Std.Array.repeat, List.mem_replicate] using hx)
  have hfr : Frame2 (L := L) s s (stA (L.curW s)) (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
    fun _ _ _ _ => rfl
  obtain ⟨hP, ⟨-, -, hM, -, hI⟩, -⟩ := J.xtop.rel
  have hS := J.xtop.fin.1.1.1
  have hact : ∀ y ∈ H.tcbs, L.actionW s ≠ y := fun y hy =>
    actionW_ne_of hS (by rw [J.tcbs_eq.1]; exact hy) (fun e => by rw [hni.2] at e; cases e)
  obtain ⟨-, x, hkx, hrx⟩ := J.curRunnable hni (cur_thread_eq s)
  have hcT : L.curW s ∈ Z.T := by rw [J.tcbs_eq.1]; exact J.kern.curH
  have hrun : Runnable (L.mem s (stA (L.curW s))) := by
    show Runnable (L.mem s (P1.stA (L.curW s))); rw [stA_tStA]; exact (runnable_iff (J.xtop.fin.1.1.2.2.1.at_tcb hcT hkx).st).2 hrx
  -- the window, in the source's free part
  have hcv := capV_of_capAt hcap
  obtain ⟨hxG, p1, sb1, fi0', fi1, d1, e0, -, hpA, -, hAs, -, -⟩ := hE.usrc
  rw [hcv] at e0
  simp only [capability.Cap.Untyped.injEq] at e0
  obtain ⟨hp1, hsb1, hfi1, -⟩ := e0
  subst p1 sb1 fi0'
  have hAs' : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have U := J.utc _ p sb fi false hAs' hcap rfl
  obtain ⟨hk1', hk2, -⟩ := J.jcov.ks _ hxG p sb fi hcv
  have hk1 : 1 ≤ k := hE.k1
  have hfitW : A0 + w * k ≤ 2 ^ 64 := le_trans hAs U.pfit
  have hpos : 0 < A0 := by
    have := U.high (notDev_ram hcv); omega
  have RD : ∀ q kd, H q = some kd → RegionD H A0 (A0 + w * k) q → q ∈ D ∧ DeadP (L := L) H s q := by
    intro q kd hq hr
    refine (retype_window_dead J.jcov J.ut hI hE ⟨p, sb, fi, hcv⟩).1 q kd hq ?_
    unfold RegionD at hr; rw [hq] at hr; simp only [Option.elim] at hr
    unfold MeetsR at hr; unfold MeetsW; omega
  have hreg : A0 + w * k ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ A0 := by rcases hk1' with h | h <;> omega
  obtain ⟨hKR, hDT⟩ := hRU
  have hdrop := dead_dropOK UJ RD hfr rfl rfl rfl rfl hact hrun hKR hDT hreg
  have hRON : RegionOffNodes st Cs s A0 (A0 + w * k) := by
    refine ⟨fun c hc => ?_, ?_⟩
    · rcases hk2 c hc with h | h <;> omega
    · rcases hk1' with h | h <;> omega
  have hb1 := J.blk
  have hTm : TimerOK st H.tcbs Cs s := hb1.2.2.1.2.2.tm
  obtain ⟨Tr, Cq, hJP⟩ := J.jpl
  have hSC : SlotCapW Z.th H.tcbs H.omega H.frame := slotCapW_of_in hP J.kern.heap (fun a ha => hJP.slot_in ha)
  have hsoff : ∀ v, SlotSpan Z.th v → (∀ y, H y = some .tcb → v ≠ dnA y ∧ v ≠ dpA y) ∧
      (∀ c ∈ Cs, v.val < L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ v.val) := fun v hv => by
    obtain ⟨o1, o2⟩ := slot_word_off hJP J.kern.hnd hv
    exact ⟨o1, fun c hc => o2 c hc⟩
  have hn1 : n ≠ 1 := hn.1
  have hdbg : DbgLinksOK st H Cs s' A0 (A0 + w * k) A0 k w n := by
    refine dbgLinks_nonTcb hn1 hdrop hTm hW (fun v hv => ?_) (fun y hy => ?_) (fun c hc => ?_)
    · rcases hv with (⟨hT', -⟩ | hsl) | ⟨-, hv1, hv2⟩
      · exact absurd hT' hT
      · obtain ⟨o1, o2⟩ := hsoff v hsl
        refine ⟨fun y hy _ => o1 y hy, fun c hc e => ?_⟩
        have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
        have := o2 c hc
        rw [e, hv0] at this
        have : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
        omega
      · refine ⟨fun y hy hyD => ?_, fun c hc e => ?_⟩
        · have hy' : H y = some .tcb := hy
          have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
          have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
          refine ⟨fun e => hyD ?_, fun e => hyD ?_⟩ <;>
            (unfold RegionD MeetsR; rw [hy']; simp only [Option.elim, HKind.bits, Nat.reducePow]; subst e; omega)
        · have hv0 := nodeAt_val (hTm.npl c hc) (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
          have h4 : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
          have hc2 := hk2 c hc
          subst e
          rw [hv0] at hv1 hv2
          rcases hc2 with h | h <;> omega
    · have hal := J.kern.heap.align y .tcb hy
      simp only [HKind.bits] at hal
      have hdn : (dnA y).val = y.val + 3576 := tcb_word J.kern.heap hy (by simp)
      have hdp : (dpA y).val = y.val + 3584 := tcb_word J.kern.heap hy (by simp)
      unfold P1.Aligned
      rw [hdn, hdp]; omega
    · exact nodeAt_aligned (hTm.npl c hc) (by simp [layout.node.DEBUG_TCBS]) (by simp [layout.node.DEBUG_TCBS])
  have hkd : ∀ kd, newKind n us = some kd → 2 ^ kd.bits = k := fun kd h => by rw [newKind_bits h, hk]
  have hwp : WinPlaced A0 k w n us := by
    refine ⟨fun kd h => ?_, hfitW, hpos, hn.2⟩
    rw [hkd kd h]
    exact ⟨hAk, Nat.mod_self _⟩
  have hh0 : L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ≠ 0#u64 →
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) ∈ Heap.tcbs H :=
    fun hne => (hTm.dh _ J.kern.cs0).resolve_left hne
  obtain ⟨H', Ac', hb', hkeep, hshape, hnew, hdead'⟩ := creation_step (n := n) (us := us) hb1
    (fun kd h => (hkd kd h).le) hdrop hRON hdbg hwp hW hP hSC J.kern.cs0 hh0 (fun h => absurd h hT) hfitW
    (fun _ hz w0 hw0 h1 h2 => Or.inl ((hWZ hz w0 hw0 h1 h2).resolve_right (fun h => hT h.1))) (fun h => absurd h hn1)
  have hout : HOut H H' A0 (A0 + w * k) A0 k w (newKind n us) :=
    hOut_of_steps hk1 le_rfl le_rfl (Or.inl ⟨rfl, rfl, rfl⟩) hkeep hshape hnew
  have hdk : ∀ q kd, H q = some kd → DeadP (L := L) H s q → DeadQ st H s q := fun q kd hq hd =>
    deadQ_keep J.kern.heap hq hd (fun _ _ _ _ => rfl) rfl (fun hqt e => hact q hqt e.symm)
  have hnewQ : ∀ q, NewAt A0 k w q → newKind n us ≠ none → NewQ A0 k w cj q := by
    rintro q ⟨j, hj, hq⟩ hK
    exact ⟨j, hj, hq, hcjU hK j hj⟩
  refine ⟨H', Ac', hb', hout, J.jcov.retype hE (fun q kd hq => ?_) (fun q hqD hnq e hd => ?_) hW.1
    hidl ⟨p, sb, fi, hcv⟩⟩
  · rcases hshape q kd hq with ⟨h1, hm⟩ | ⟨hna', hk'⟩
    · refine Or.inl ⟨h1, ?_⟩
      rintro ⟨j, hj, hv, -⟩
      apply hm
      unfold MeetsR
      have h1' : (j + 1) * k ≤ w * k := Nat.mul_le_mul_right _ hj
      rw [Nat.add_mul, Nat.one_mul] at h1'
      have := Nat.one_le_two_pow (n := kd.bits)
      omega
    · exact Or.inr ⟨hnewQ q hna' (by rw [hk']; simp), (hkd kd hk').le⟩
  · cases hHq : H q with
    | none => exact DeadP.none (e.trans hHq)
    | some kd =>
      have hq' : H' q = some kd := e.trans hHq
      rcases hshape q kd hq' with ⟨h1, -⟩ | ⟨hna', hk''⟩
      · exact hdead' q (hq'.trans h1.symm) (hdk q kd hHq hd)
      · exact absurd (hnewQ q hna' (by rw [hk'']; simp)) hnq


end

end

end Fl4Proofs.P3
