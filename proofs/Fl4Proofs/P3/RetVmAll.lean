/-
P3 (line mmuAD, gen 42b27): **one `VmEptState.retype` over the retype bodies** — the Architect's ruling
(2026-11-28 19:55Z) item 2 for every type number but the VCPU's (0..13, 15..18), RAM and device sources.

* **`JAtZB.winDev`**: a device untyped cap's free part misses every spec object (`DevFreeT`) and the kernel-state
  block (`DevApart`), and the cap's region fits (`fit_of_al`).
* **`VmEptState.ofPostD`**: P3/RetVm's `VmEptState.ofPost` for a device body (`utDevBodyJ`, `utUtDevBodyJ`): the
  window's facts from `winDev`, through P3/RetVm's `JVm.winOff` / `EptCore.winOff` (the device bodies make no
  guest table, so the 15..18 hypotheses of `VmEptState.ofRet` are vacuous).
* **`defObj_bits`**, **`pmObj_bits`**: the bodies' object predicates (`DefObj`, `PmObj`) fit their window slot
  (`hob`): `objBits_default_le` (P3/SpecInvDvP) with `objTypeOf_some`, the SC size bound from `RetCtx.size`.
* **`VmEptState.retype`**: from `VmEptState V X XL` at a retype body's entry (the bodies' common hypotheses, the
  RAM-only `UtFreeZ` / `UtNodesAt` and the device-only `DevApart` / `DevFreeT` as `dev`-guarded hypotheses), FL4's
  `untyped.retype` (no reset) of a type `nt ≠ 14` ⦃ the spec's `fl4InvokeUntypedV` has the single outcome `ok`,
  `Ok ()`, and `VmEptState V (RetTabs ∪ X) (RetLvl XL)` after ⦄. Dispatch: 0 → `utUtBodyJ` / `utUtDevBodyJ`,
  1 → `utTcbBodyJ` (footprint `RetWdT`: `retFootV_T` / `retFootE_T`), 4 → `utCnBodyJ`, 5 → `utScBodyJ`,
  8 → `utPmBodyJ` (`RetWdW`: `retFootV_W` / `retFootE_W`, `PmObj`), 9..11 on a device → `utDevBodyJ`, every other
  RAM type (2, 3, 6, 7, 9..13, 15..18) → `utEpBodyJ`; slot-only footprints by `retFootV_slot` / `retFootE_slot`; then
  `ofPost` (RAM) or `ofPostD` (device).

Not covered: the VCPU (`nt = 14`). Its `VmState`-entry retype needs `JAtZB` at the state after FL4's VCPU retype, and
no such fact exists: the VCPU retype facts (P3/VirtRetFullV2 `retype_full_vcpu2`, P3/VirtUtInvVR2 `RetPostVR2`,
P3/VirtRetFrameV `retype_vcpu_frame`) are at `StateRel` / `JExtV2` level, and the ruling keeps type 14 off the
`JAtZB` bodies (handoff `# gen 42b27`).

No named premise. No `sorry`; only the three standard axioms.
-/
import Fl4Proofs.P3.RetVm
import Fl4Proofs.P3.UtDevUt
import Fl4Proofs.P3.SpecInvDvP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **A body's default objects fit their window slot** (`hob` for `DefObj`). -/
theorem defObj_bits (σ : Fl4Spec.State Unit) {nt us : Nat} {t : Fl4Spec.ApiObjectType} (hty : objTypeOf nt = some t)
    (hsc : nt = 5 → 7 ≤ us) (dev : Bool) :
    t ≠ .untyped → ∀ q ko, DefObj σ t dev us q ko → Fl4Spec.objBits ko ≤ zOf nt us := by
  intro htu q ko h
  unfold DefObj at h
  subst h
  have h1t : objTypeOf 1 = some .tcbObject := by simp [objTypeOf]
  by_cases h1 : nt = 1
  · subst h1
    rw [h1t] at hty
    cases hty
    exact le_trans (SInvDV.objBits_default_le htu (fun e => by cases e) dev _)
      (by simp [Fl4Spec.fl4ObjBitsApi, Fl4Spec.fl4TcbBits, zOf])
  · have hT : t ≠ .tcbObject := fun e => h1 (Sched.objTypeOf_inj hty (by rw [e]; exact h1t))
    obtain ⟨-, hb, -, -, -, hS⟩ := objTypeOf_some hty h1 us
    refine le_trans (SInvDV.objBits_default_le htu (fun e => ?_) dev _)
      (by rw [Fl4Spec.fl4ObjBitsApi_of_ne hT, hb])
    have := hsc (hS.1 e)
    simp only [Fl4Spec.minSchedContextBits]
    omega

/-- **The PML4 body's objects fit their window slot** (`hob` for `PmObj`). -/
theorem pmObj_bits {t : Fl4Spec.ApiObjectType} {dev : Bool} {us : Nat} :
    t ≠ .untyped → ∀ q ko, PmObj t dev us q ko → Fl4Spec.objBits ko ≤ zOf 8 us := by
  rintro - q ko ⟨pt, rfl, -⟩
  simp [Fl4Spec.objBits, Fl4Spec.archKobjSize, Fl4Spec.tableSize, Fl4Spec.ptTranslationBits, Fl4Spec.wordSizeBits, zOf]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64} {XL : U64 → Nat}

open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A device window** (inside the free part of a device untyped cap of an `AbsSlot`) misses every spec object
(`DevFreeT`) and the kernel-state block (`DevApart`); the cap's region fits. -/
theorem JAtZB.winDev (B : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hDA : DevApart (L := L) Z.th H Z.G Cs s)
    (hDF : DevFreeT (L.mem s) Z.G σ) {sl : Fl4Spec.CslotPtr} {p sb fi : U64}
    (hAs : AbsSlot Z.th sl) (hcap : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi true))
    {lo hi : Nat} (h1 : p.val + fi.val ≤ lo) (h2 : hi ≤ p.val + 2 ^ sb.val) :
    (∀ o ko, σ.kheap o = some ko → o.toNat + 2 ^ Fl4Spec.objBits ko ≤ lo ∨ hi ≤ o.toNat) ∧
    (hi ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ lo) ∧ p.val + 2 ^ sb.val ≤ 2 ^ 64 := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := B.xtop.rel
  have hxG : cslotAddr sl ∈ Z.G.chains.flatten := (hM.members _).2 ⟨hAs.isSlot, _, hcap, by simp⟩
  obtain ⟨a1, a2, -⟩ := hDA _ hxG p sb fi (capV_of_capAt hcap)
  refine ⟨fun o ko hk => ?_, by rcases a2 with h | h <;> omega,
    fit_of_al (show p.val < 2 ^ 64 from p.bv.isLt) (capAt_untyped_inv hcap) a1⟩
  have := Nat.one_le_two_pow (n := Fl4Spec.objBits ko)
  rcases hDF _ hxG p sb fi true (capV_of_capAt hcap) ⟨rfl, trivial⟩ o ko hk with h | h
  · rcases h with h | h <;> omega
  · omega

/-- **`VmEptState` after a device body's `UtBodyPostB`** (types 0, 9..11 from a device untyped): as
`VmEptState.ofPost`, the window's facts from `JAtZB.winDev`. -/
theorem VmEptState.ofPostD (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s a σ) {nt : Nat}
    {Xp : XSets → P1.Heap → Set U64 → S → Fl4Spec.State Unit → Prop} {W : Nat → Nat → U64 → Prop}
    {O : Fl4Spec.ApiObjectType → Bool → Nat → Fl4Spec.ObjRef → Fl4Spec.KernelObject → Prop}
    {src : Fl4Spec.CslotPtr} {rs : Bool} {pb rb : Fl4Spec.ObjRef} {t : Fl4Spec.ApiObjectType} {us : Nat}
    {slots : List Fl4Spec.CslotPtr} {res : core.result.Result Unit error.Exc × S × A}
    (h : UtBodyPostB (L := L) arI AR Z.th Z.G H s σ nt Xp W O (.retype src rs pb rb t us slots true) res)
    (hAs : AbsSlot Z.th src) (hDA : DevApart (L := L) Z.th H Z.G Cs s) (hDF : DevFreeT (L.mem s) Z.G σ)
    (hFV : RetFootV (L := L) V Z.th s (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hFE : RetFootE X (W rb.toNat (rb.toNat + slots.length * 2 ^ zOf nt us)))
    (hty : objTypeOf nt = some t) (hn13 : nt ≤ 13)
    (hob : t ≠ .untyped → ∀ q ko, O t true us q ko → Fl4Spec.objBits ko ≤ zOf nt us) :
    ∃ σ', (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype src rs pb rb t us slots true)).run σ =
        ({(.ok (), σ')}, False) ∧
      res.1 = .Ok () ∧ ∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        VmEptState (L := L) arI V (RetTabs nt us rb slots.length ∪ X) (RetLvl nt us rb slots.length XL) AR Z' H' Cs'
          Ac' Lst' D' res.2.1 res.2.2 σ' := by
  obtain ⟨σ', hrun, hok, -, Z', H', Cs', Ac', Lst', D', B', -, -, -, hR⟩ := h
  have R := hR _ _ _ _ _ _ _ _ rfl
  obtain ⟨k, -, -, hk, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨p, sb, fi, hsrc, h1, h2⟩, -⟩ := id R
  subst hk
  have hcap : capAt (L.mem s) (cslotAddr src) = ok (.Untyped p sb fi true) := by rw [capAt_capV, hsrc]
  obtain ⟨hσ, hK, hfit⟩ := J.1.1.winDev hDA hDF hAs hcap h1 h2
  exact ⟨σ', hrun, hok, Z', H', Cs', Ac', Lst', D',
    J.ofRet B' R hFV hFE hty (by omega) (J.1.2.vm.winOff hσ) (J.2.winOff hσ) hK hob (by omega)
      (fun h _ => absurd h (by omega)) (fun h _ => absurd h (by omega)) (fun h _ => absurd h (by omega))⟩

set_option maxHeartbeats 4000000 in
/-- **`VmEptState` across a retype of any type but the VCPU** (module docstring): the bodies' common entry
hypotheses at a `VmEptState` state, the RAM-only facts `hZ0` / `hKN` and the device-only facts `hDA` / `hDF`. -/
theorem VmEptState.retype {s : S} {ar : A} {σ : Fl4Spec.State Unit}
    (J : VmEptState (L := L) arI V X XL AR Z H Cs Ac Lst D s ar σ) [VxE Z]
    (hni : Entered σ) {pp : U64} {rs : Nat} {idx : List Bool}
    (hpp : Z.th pp = some (.cnode rs)) (hidx : idx.length = rs) {p sb fi : U64} {dev : Bool}
    (hcap : capAt (L.mem s) (cslotAddr (pp.bv, idx)) = ok (.Untyped p sb fi dev))
    {nt us dest off win : U64} {t : Fl4Spec.ApiObjectType} {r : Nat} {reset : Bool} {fiv : U64}
    (hn14 : nt.val ≠ 14) (hc0 : Z.c = 0#u64)
    (hctx : RetCtx (L := L) Z.th s σ (pp.bv, idx) sb fi dev nt us dest off win t r reset fiv) (hfiv : fiv = fi)
    (hBO : BufObjHyp Z.B σ) (hAF : ArchFitHyp H σ)
    (hRU : ∀ lo hi : Nat, p.val + fi.val ≤ lo → hi ≤ p.val + 2 ^ sb.val →
      KeptRefsP3 (L := L) H (RegionD H lo hi) s ∧ DbgTimerKept (L := L) H (RegionD H lo hi) Cs s)
    (hZ0 : dev = false → UtFreeZ σ (p.val + fi.val) (p.val + 2 ^ sb.val))
    (hKN : dev = false → UtNodesAt (L.ksb s) p sb)
    (hDA : dev = true → DevApart (L := L) Z.th H Z.G Cs s) (hDF : dev = true → DevFreeT (L.mem s) Z.G σ) :
    untyped.retype st arI s ar (cslotAddr (pp.bv, idx)) false
        ⟨Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)⟩ nt us dest off win dev ⦃ res =>
      ∃ σ', (Fl4Spec.fl4InvokeUntypedV (Z := Unit) (.retype (pp.bv, idx) false p.bv
          (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val)) t us.val (windowSlots dest r off.val win.val)
          dev)).run σ = ({(.ok (), σ')}, False) ∧
        res.1 = .Ok () ∧ ∃ (Z' : XSets) (H' : P1.Heap) (Cs' Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
          VmEptState (L := L) arI V
            (RetTabs nt.val us.val (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
              (windowSlots dest r off.val win.val).length ∪ X)
            (RetLvl nt.val us.val (Fl4Spec.alignUp (p.bv + fiv.bv) (zOf nt.val us.val))
              (windowSlots dest r off.val win.val).length XL) AR Z' H' Cs' Ac' Lst' D' res.2.1 res.2.2 σ' ⦄ := by
  subst fiv
  have hAs : AbsSlot Z.th (pp.bv, idx) := ⟨pp, rfl, Or.inl (by simpa [hidx] using hpp)⟩
  have hty := hctx.ty
  have hsc : nt.val = 5 → 7 ≤ us.val := fun h => by have := hctx.size.2.2.2.2; omega
  have hD := defObj_bits σ hty hsc
  have FVs := J.1.1.retFootV_slot J.1.2
  have FEs := J.1.1.retFootE_slot J.2
  cases dev
  · -- a RAM source
    have hZ := hZ0 rfl
    have hN := hKN rfl
    have hU := J.1.1.utc _ p sb fi false hAs hcap rfl
    obtain ⟨h1, -, h2, -⟩ := retype_region p fi sb.val (zOf nt.val us.val) win.val (capAt_untyped_inv hcap)
      (by have := hctx.size.2.1; omega) hU.pal hU.pfit hU.fiLe hctx.window.1 hctx.memory
    have h2' : (Fl4Spec.alignUp (p.bv + fi.bv) (zOf nt.val us.val)).toNat +
        (windowSlots dest r off.val win.val).length * 2 ^ zOf nt.val us.val ≤ p.val + 2 ^ sb.val := by
      rw [show (windowSlots dest r off.val win.val).length = win.val by simp [windowSlots]]; exact h2
    have hcase : nt.val = 0 ∨ nt.val = 1 ∨ nt.val = 4 ∨ nt.val = 5 ∨ nt.val = 8 ∨
        (nt.val = 2 ∨ nt.val = 3 ∨ nt.val = 6 ∨ (ArchTab nt.val ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11)) := by
      have hlt : nt.val < 19 := by
        by_contra hc; rw [(objTypeOf_none _).2 (by omega)] at hty; cases hty
      unfold ArchTab; omega
    rcases hcase with e | e | e | e | e | e
    · exact WP.spec_mono (J.1.1.utUtBodyJ hni hpp hidx hcap e hc0 hctx rfl hBO hAF hRU) fun res h =>
        J.ofPost h hAs FVs FEs hty hn14 (hD false)
    · exact WP.spec_mono (J.1.1.utTcbBodyJ hni hpp hidx hcap e hc0 hctx rfl hBO hAF hRU) fun res h =>
        J.ofPost h hAs (J.1.1.retFootV_T J.1.2 hAs hcap h1 h2') (J.1.1.retFootE_T J.2 hAs hcap h1 h2') hty hn14
          (hD false)
    · exact WP.spec_mono (J.1.1.utCnBodyJ hni hpp hidx hcap e hc0 hctx rfl hBO hAF hRU) fun res h =>
        J.ofPost h hAs FVs FEs hty hn14 (hD false)
    · exact WP.spec_mono (J.1.1.utScBodyJ hni hpp hidx hcap e hc0 hctx rfl hBO hAF hRU) fun res h =>
        J.ofPost h hAs FVs FEs hty hn14 (hD false)
    · exact WP.spec_mono (J.1.1.utPmBodyJ hni hpp hidx hcap e hc0 hctx rfl hBO hAF hRU) fun res h =>
        J.ofPost h hAs (J.1.1.retFootV_W J.1.2 hAs hcap h1 h2') (J.1.1.retFootE_W J.2 hAs hcap h1 h2') hty hn14
          (by rw [e]; exact pmObj_bits)
    · exact WP.spec_mono (J.1.1.utEpBodyJ hni hpp hidx hcap e hc0 hctx rfl hBO hAF hRU hZ hN) fun res h =>
        J.ofPost h hAs FVs FEs hty hn14 (hD false)
  · -- a device source: untypeds and frames only (`RetCtx.device`)
    have hDA' := hDA rfl
    have hDF' := hDF rfl
    have hdv : nt.val = 0 ∨ nt.val = 9 ∨ nt.val = 10 ∨ nt.val = 11 := by
      by_cases h1 : nt.val = 1
      · exfalso
        have e : t = .tcbObject := by rw [h1] at hty; simpa [objTypeOf] using hty.symm
        subst e
        rcases hctx.device rfl with h | h
        · simp [Fl4Spec.isFrameType] at h
        · cases h
      · obtain ⟨-, -, hF, hU, -⟩ := objTypeOf_some hty h1 us.val
        rcases hctx.device rfl with h | h
        · exact Or.inr (hF.1 h)
        · exact Or.inl (hU.1 h)
    rcases hdv with e | e
    · exact WP.spec_mono (J.1.1.utUtDevBodyJ hni hpp hidx hcap e hc0 hctx rfl hDA' hDF' hBO hAF hRU) fun res h =>
        J.ofPostD h hAs hDA' hDF' FVs FEs hty (by omega) (hD true)
    · exact WP.spec_mono (J.1.1.utDevBodyJ hni hpp hidx hcap e hc0 hctx rfl hDA' hDF' hBO hAF hRU) fun res h =>
        J.ofPostD h hAs hDA' hDF' FVs FEs hty (by omega) (hD true)

end

end

end Fl4Proofs.P3
