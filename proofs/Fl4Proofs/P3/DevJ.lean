/-
P3 (losfair/FL4#34), untyped: **the device untyped caps' apartness at `J`**
(`DevApart`, carried alongside `JAtZ`, not a field of it) and the pieces of
the device retype that do not need `JAtZ`'s RAM-only facts.

Owner decision (2026-11-19, handoff/devretype.md "dj2 line"): the kernel's
boot skips device memory whose pointer range meets the kernel image
`[KERNEL_ELF_BASE, KERNEL_ELF_TOP)`. A device untyped's pointer range then
misses every name in the kernel image (the kernel-state block `ks` with the
per-core nodes and the ASID-table area, the idle objects) and every RAM
object (RAM objects are named by pointers of RAM physical addresses, which a
device range never contains); retype keeps this, a device child's range
being a sub-range of its parent's.

* `DevApart` [J] (l4v `valid_untyped` / `pspace_no_overlap` for device caps
  with `valid_global_refs` / `kernel_window`: no untyped range covers a
  kernel object): for each device untyped cap of the MDB, its range is
  aligned, misses the kernel-state block, the nodes, the ASID-table area,
  the idle objects and every typed-heap object, and an `H` object meeting it
  lies below the cap's free index (a device frame retyped from it or a
  descendant). True from boot by the boot check (no `H` object then lies in a
  device range), kept by retype (the new frames lie below the source's new
  free index) and by the device reset (which drops the region's objects).
* `DevApart.srcOK`: a device source's `SrcOK` (ScPlaceRet), so
  `retype_window_deadS` / `JCovD.retypeS` apply to the device retype.
* `retype_bodyD`: UtBodyJ's `retype_body` for any device flag (the window
  zero only for a RAM cap), from `retype_full`. It keeps `retype_full`'s
  `2^64 - 2^47 ≤ p` (not unused: `loop_step` needs it for the new caps'
  encoding, `canonical_of_high`, and their pointers ≠ 0), so a device cap
  whose pointer wrapped into the lower half (physical ≥ 512 GiB) is not
  covered yet (handoff/devretype.md "dj2 line").
* `JAtZ.create_noresetBD`: UtBodyJ's `create_noresetB` for a device source.
-/
import Fl4Proofs.P3.DevFree
import Fl4Proofs.P3.UtBodyJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **[J] The device untyped caps' apartness** (module docstring; l4v
`valid_untyped` / `pspace_no_overlap` for device caps, `valid_global_refs`,
`kernel_window`): every device untyped cap of the MDB has an aligned range
off the kernel-state block, the nodes, the ASID-table area, the idle objects
and the typed heap's objects, and every `H` object meeting the range lies in
its used part `[p, p + fi)`. -/
def DevApart (th : TypedHeap) (H : Heap) (G : MdbGhost) (Cs : Set U64) (s : S) : Prop :=
  ∀ x ∈ G.chains.flatten, ∀ p sb fi, capV (L.mem s) x = .Untyped p sb fi true →
    p.val % 2 ^ sb.val = 0 ∧
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val) ∧
    (∀ c ∈ Cs, p.val + 2 ^ sb.val ≤ L.nodeBase s c ∨ L.nodeBase s c + 4288 ≤ p.val) ∧
    (p.val + 2 ^ sb.val ≤ (L.ksb s).val + 288000 ∨ (L.ksb s).val + 288000 + 16384 ≤ p.val) ∧
    (∀ q, IdleAt (L := L) s q → q.val < p.val ∨ p.val + 2 ^ sb.val ≤ q.val) ∧
    RegionFree th p.val (p.val + 2 ^ sb.val) ∧
    (∀ q kd, H q = some kd → q.val + 2 ^ kd.bits ≤ p.val ∨ p.val + 2 ^ sb.val ≤ q.val ∨
      (p.val ≤ q.val ∧ q.val + 2 ^ kd.bits ≤ p.val + fi.val))

/-- **A device source's `SrcOK`**: its region off the kernel-state block and
the idle objects (`DevApart`), the new caps no RAM untypeds. -/
theorem DevApart.srcOK {th th' : TypedHeap} {H : Heap} {G G' : MdbGhost} {Cs : Set U64} {s : S}
    {m' : U64 → U64} {A k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap} {xs : U64}
    (hD : DevApart (L := L) th H G Cs s) (hE : RetExp th th' (L.mem s) m' G G' A k w dslot cj xs)
    {p sb fi : U64} (hc : capV (L.mem s) xs = .Untyped p sb fi true)
    (hcj : ∀ j, j < w → ∀ p sb fi, cj j ≠ .Untyped p sb fi false) :
    SrcOK (L := L) th H s xs w cj := by
  obtain ⟨hxs, -⟩ := hE.usrc
  obtain ⟨-, k1, -, -, hid, hth, hH⟩ := hD xs hxs p sb fi hc
  refine ⟨p, sb, fi, true, hc, k1, fun q hq => ⟨hid q hq, fun kd hk => ?_, fun kd hk => ?_⟩, fun _ => hcj⟩
  · rcases hid q hq with h' | h'
    · rcases hth q kd hk with h | h
      · left; rw [Nat.max_def]; split <;> omega
      · right; exact h
    · right; exact h'
  · rcases hid q hq with h' | h'
    · rcases hH q kd hk with h | h | ⟨h1, -⟩
      · left; exact h
      · right; exact h
      · omega
    · right; exact h'

/-- **The retype without a reset from any state, any device flag**
(UtBodyJ's `retype_body`; the window zero only for a RAM cap, no CNodes from
a device cap; the source in the kernel half, `hhigh`). -/
theorem retype_bodyD {A' : Type} (arI : machine.Arch A') (ar : A') (th : TypedHeap) (s : S)
    (σ : Fl4Spec.State Unit) (G : MdbGhost)
    (hR : StateRel th (L.mem s) σ) (hV : SlotsValid th (L.mem s)) (hP : Placed th)
    (hM : MdbLinks th (L.mem s) G) (hC : CdtRel th (L.mem s) σ G) (hI : MdbInv (L.mem s) G)
    (hU : UtInv (L.mem s) G) (horig : ∀ sl, σ.isOriginalCap sl = true → AbsSlot th sl)
    {pp : U64} {rs : Nat} (hpp : th pp = some (.cnode rs)) {idx : List Bool} (hidx : idx.length = rs)
    {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    (hpal : p.val % 2 ^ sb.val = 0) (hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64) (hfi : fi.val ≤ 2 ^ sb.val)
    (hhigh : 2 ^ 64 - 2 ^ 47 ≤ p.val) (hfree : RegionFree th (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hzero : dev = false → ZeroRegion (L.mem s) (p.val + fi.val) (p.val + 2 ^ sb.val))
    (bitsApi : Fl4Spec.ApiObjectType → Nat → Nat)
    (nt us dest off win : U64) (t : Fl4Spec.ApiObjectType) (r : Nat)
    (ht : objTypeOf nt.val = some t)
    (hn : nt.val = 0 ∨ (2 ≤ nt.val ∧ nt.val ≤ 13 ∧ nt.val ≠ 8)) (hus : us.val < 64) (hz47 : zOf nt.val us.val ≤ 47)
    (hsc : nt.val = 5 → 7 ≤ us.val) (hct0 : nt.val = 4 → us.val ≠ 0) (hdevT : dev = true → nt.val ≠ 4)
    (hdest : th dest = some (.cnode r)) (hr : r < 64)
    (hwin : off.val + win.val ≤ 2 ^ r) (hw1 : 1 ≤ win.val)
    (hmem : win.val ≤ ((1#64 <<< sb.val : BitVec 64) - fi.bv).toNat >>> zOf nt.val us.val)
    (hempty : ∀ i : Nat, off.val ≤ i → i < off.val + win.val →
      capAt (L.mem s) (slotAddr dest.bv (BitVec.ofNat 64 i)) = ok .Null)
    (hb : bitsApi t us.val = zOf nt.val us.val) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
      ⟨Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      RetPostB (L := L) th (L.mem s) G σ ar arI s bitsApi (L.ksb s) (.retype (pp.bv, idx) false p.bv
        (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val) dev) res ⦄ := by
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
  have hzA : dev = false → ZeroRegion (L.mem s) (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat
      ((Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat + win.val * 2 ^ zOf nt.val us.val) :=
    fun hd w hw h1 h2 => hzero hd w hw (by omega) (by omega)
  refine WP.spec_mono (retype_full (L := L) arI ar th s σ G hR hV hP hM hC hI hU horig hpp hidx hcap hpal hpfit
    hfi hhigh nt us t ht hn hus hz47 hsc hct0 hdest hr off win hwin hw1 hmem hempty hfree hzero
    hdevT bitsApi hb) ?_
  rintro res ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', ⟨hU', hSt'⟩, -, hFin, hks, hWf, A, k, w,
    dslot, cj, hE, rfl, rfl, rfl, hnu, hthx, hcjE, hdsC⟩
  exact ⟨h1, h2, σ', G', th', hrun, hP', hR', hV', hM', hC', hI', hU', hSt', hFin, hks, _, _, _, dslot, cj, hE,
    ⟨Or.inr ⟨h1, ⟨rfl, by rw [hb], by simp [windowSlots], hWA2⟩, s, th, _, _,
      Or.inl ⟨rfl, rfl, rfl, rfl, fun h => by cases h⟩, le_rfl, le_rfl, hthx.2, fun a h => h,
      ⟨nt.val, ht, hthx, us, rfl, hcjE⟩, hdsC, hWf.mono fun v hv => Or.inl (Or.inr hv),
      fun hZ => winZero_of_slots hWf (hzA hZ.1) hsl _, fun hT => absurd (objTypeOf_tcb (hT ▸ ht)) hn1⟩,
     fun _ j hj hu => by have h0 := hnu j hj hu; rw [h0] at ht; simpa [objTypeOf] using ht.symm⟩⟩

end

/-- An aligned range fits below `2^64`. -/
theorem fit_of_al {p sb : Nat} (hp : p < 2 ^ 64) (hsb : sb < 64) (ha : p % 2 ^ sb = 0) : p + 2 ^ sb ≤ 2 ^ 64 := by
  obtain ⟨m, rfl⟩ := Nat.dvd_of_mod_eq_zero ha
  have e : (2 : Nat) ^ 64 = 2 ^ sb * 2 ^ (64 - sb) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e] at hp ⊢
  have hm : m < 2 ^ (64 - sb) := Nat.lt_of_mul_lt_mul_left hp
  calc 2 ^ sb * m + 2 ^ sb = 2 ^ sb * (m + 1) := (Nat.mul_succ _ _).symm
    _ ≤ 2 ^ sb * 2 ^ (64 - sb) := Nat.mul_le_mul_left _ hm

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

set_option maxHeartbeats 4000000 in
/-- **`JAtZ.create_noresetB` for a device source** (UtBodyJ): P1's creation
from one `JAtZ` state, the source a device untyped cap. The RAM facts of the
source (`JAtZ.utc`, `JCovD.ks`/`idleOut`) are replaced by `DevApart` (its
range aligned, off the kernel-state block, the nodes and the idle objects)
and `DevApart.srcOK` (the new caps no RAM untypeds, `hcjR`); the window's
base positive (`hpos`) is P1's `WinPlaced` (a RAM cap's from its kernel-half
pointer; for a device cap it fails only at the pointer 0). -/
theorem JAtZ.create_noresetBD {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ)
    {pp : U64} {rs : Nat} {idx : List Bool} (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs)
    {p sb fi : U64} (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi true))
    (hDA : DevApart (L := L) Z.th H Z.G Cs s)
    {s' : S} {th' : TypedHeap} {G' : MdbGhost} {A0 k w : Nat} {dslot : Nat → U64} {cj : Nat → capability.Cap}
    (hE : RetExp Z.th th' (L.mem s) (L.mem s') Z.G G' A0 k w dslot cj (cslotAddr (pp.bv, idx)))
    (hRU : KeptRefsP3 (L := L) H (RegionD H A0 (A0 + w * k)) s ∧ DbgTimerKept (L := L) H (RegionD H A0 (A0 + w * k)) Cs s)
    {n us : Nat} (hcjU : newKind n us ≠ none → ∀ j, j < w → isUt (cj j) = false)
    (hcjR : ∀ j, j < w → ∀ p sb fi, cj j ≠ .Untyped p sb fi false) (hpos : 0 < A0)
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
  obtain ⟨hpal, hk1', hk2, -⟩ := hDA _ hxG p sb fi hcv
  have hpfit : p.val + 2 ^ sb.val ≤ 2 ^ 64 := fit_of_al (show p.val < 2 ^ 64 from p.bv.isLt) (capV_ut_sb hcv) hpal
  have hSO := hDA.srcOK hE hcv hcjR
  have hk1 : 1 ≤ k := hE.k1
  have hfitW : A0 + w * k ≤ 2 ^ 64 := le_trans hAs hpfit
  have RD : ∀ q kd, H q = some kd → RegionD H A0 (A0 + w * k) q → q ∈ D ∧ DeadP (L := L) H s q := by
    intro q kd hq hr
    refine (retype_window_deadS J.jcov J.ut hI hE hSO).1 q kd hq ?_
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
  refine ⟨H', Ac', hb', hout, J.jcov.retypeS hE (fun q kd hq => ?_) (fun q hqD hnq e hd => ?_) hW.1
    hidl hSO⟩
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
