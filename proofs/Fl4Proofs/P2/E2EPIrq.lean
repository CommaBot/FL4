/-
P2 (line pte, gen 5): **the timer interrupt reads no PTE word** (the `irq` field of `P3AvP3`, discharged).

The timer interrupt's read set is `MaxR (userV K)` = `RPerm ∧ Aligned ∧ ∉ user`: it already **excludes user words**.
So no generic-read-set copy of its walks is needed: the existing fixed-`MaxR` walks (`irq_acc_own` with the fire
case `irq_acc_fire_nw` / `irq_acc_fire_wk2`, and `irq_dec_guard`), instantiated at the layout
**`userP K`** = `userV K` with the PTE words added to its user set, run on `guard (MaxR (userP K))`, and
`MaxR (userP K) ⊆ MaxR (userV K) ∖ ptes` (`own` does not read `user`, so the permissions are the same). This is the
generic-read-set argument with `hR` discharged once, by the layout: any excluded set the walks' layout facts can carry
as user words (here: PTEs are region `.none`, `RegionOKP.none`) comes out of the same proofs; the VCPU data words were
the first instance (`userV`).

The layout facts at `userP K`, from `userV K`'s and PTE facts: `regionOK_userP` (fieldwise), `stLay_userP`
(`StLay.user`: a PTE is region `.none`; `domU` / `dtmU`: the domain words are no PTE words), `irqLay_userP`
(`iqU` / `krU` / `tabU`: the IRQ-state word, the kernel root and the ASID words are no PTE words), `irqEnt_userP`.
The PTE facts come from **`PteSl`** [J] (gen 3) at the bundle state the timer interrupt's `Pre` (`IrqPreV`) carries:
kernel-state words by `KsNoE` with `L.ksb s = K.ksb` (`slJAt_ksb`; the IRQ-state offset `224 + 8 irq < 13568`:
`state_off_lt`), the ASID words by `TabNoE`. **No new premise.**

`avoidE_liftAtV`: `AvoidE` of a route-U path gives `AvoidE` of its slot lift (`liftV ∘ atV`; `atV` only shrinks the
user set, which strengthens `Alt`). **`irq_avoidP`**.
-/
import Fl4Proofs.P2.E2EPLvm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## Route U: `AvoidE` through the slot lift -/

/-- **`AvoidE` of a route-U path gives `AvoidE` of its lift** (`atV` shrinks the user set: `Alt` gets stronger). -/
theorem avoidE_liftAtV {K : KLayoutV} {m : U64 → U64} {E : U64 → Prop} (hK : RegionOKV K)
    (P : E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user))
    (W : NoVcpuRW K P) (h : AvoidE E P) :
    AvoidE E (LocalPath.liftV hK (LocalPath.atV hK P W) (noVcpuRd_atV hK P W)) := by
  letI := P.L
  have au : ∀ {R : U64 → Prop} {s s' : P.S},
      PathObl.Alt P.st R (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) s s' →
      PathObl.Alt P.st R (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user) s s' :=
    fun hA => ⟨hA.cpu, hA.ksb, hA.masks, hA.read, fun x hx hu hk => hA.clsEq x hx (fun h => hu (Or.inl h)) hk⟩
  obtain ⟨ha, hd, hp⟩ := h
  refine ⟨ha, ?_, ?_⟩
  · intro s a r hs hr hn s' r' hA h'
    exact hd s a r hs hr hn s' r' (au hA) h'
  · intro st' N σ g a
    obtain ⟨s, hs, hA⟩ := g
    exact hp st' N σ ⟨s, hs, au hA⟩ a

/-! ## The layout with the PTE words added to `userV K`'s user set -/

/-- `userV K` with the PTE words as user words too. -/
def userP (K : KLayoutP) : KLayout :=
  { userV K.toKLayoutV with user := {x | x ∈ (userV K.toKLayoutV).user ∨ x ∈ K.ptes} }

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}

theorem regionOK_userP (hK : RegionOKV K.toKLayoutV) : OwnMap.RegionOK (userP K) where
  tcb := hK.base.tcb
  slot := hK.base.slot
  ntfn := hK.base.ntfn
  scw := hK.base.scw
  tcbOf := hK.base.tcbOf
  slotOf := hK.base.slotOf
  ntfnOf := hK.base.ntfnOf

theorem stLay_userP (hK : RegionOKP K) {s : S} (hL : StLay (userV K.toKLayoutV) st T Scs Z s)
    (h1 : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes)
    (h2 : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes) :
    StLay (userP K) st T Scs Z s where
  nd := hL.nd
  tcb := hL.tcb
  sc := hL.sc
  dom := hL.dom
  dtm := hL.dtm
  domA := hL.domA
  dtmA := hL.dtmA
  user b hb := Or.elim hb (fun h => hL.user b h) (fun h => hK.none b h)
  domU hb := Or.elim hb hL.domU h1
  dtmU hb := Or.elim hb hL.dtmU h2

theorem irqLay_userP {irq : U64} {s : S} (hY : IrqLay (userV K.toKLayoutV) st Nt irq s)
    (hiq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → core.num.U64.wrapping_add (L.ksb s) i ∉ K.ptes)
    (hkr : krA (L := L) s ∉ K.ptes) (htab : TabNoE (L := L) (· ∈ K.ptes) s) :
    IrqLay (userP K) st Nt irq s where
  iq := hY.iq
  kr := hY.kr
  tab := hY.tab
  ntw := hY.ntw
  cs := hY.cs
  iqU hb i hi hu := Or.elim hu (hY.iqU hb i hi) (hiq hb i hi)
  krU hu := Or.elim hu hY.krU hkr
  tabU hi hhi := ⟨fun hu => Or.elim hu (hY.tabU hi hhi).1 (htab hi hhi).1,
    fun lo hlo hne hu => Or.elim hu ((hY.tabU hi hhi).2 lo hlo hne) ((htab hi hhi).2 lo hlo hne)⟩

theorem irqEnt_userP (hK : RegionOKP K) {irq : U64} {s : S}
    (hE : IrqEnt (userV K.toKLayoutV) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s)
    (hiq : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → core.num.U64.wrapping_add (L.ksb s) i ∉ K.ptes)
    (hkr : krA (L := L) s ∉ K.ptes) (htab : TabNoE (L := L) (· ∈ K.ptes) s)
    (h1 : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes)
    (h2 : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes) :
    IrqEnt (userP K) st T Cs Ω H Sg Rp Scs Nt Z Ac irq s :=
  { hE with lay := stLay_userP hK hE.lay h1 h2, ly := irqLay_userP hE.ly hiq hkr htab }

/-- The IRQ-state offset lies in the kernel-state block. -/
theorem state_off_lt {irq i : U64} (hb : irq.val < 128) (h : interrupt.state_off irq = ok i) : i.val < 13568 := by
  obtain ⟨j, hj, hjv⟩ : ∃ j, interrupt.state_off irq = ok j ∧ j.val = 224 + 8 * irq.val := by
    unfold interrupt.state_off
    simp only [lift, bind_ok]
    rw [eq_of_spec_fd layout.ks.IRQ_STATE.spec]
    simp only [bind_ok]
    refine ⟨_, rfl, ?_⟩
    simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits,
      UScalar.size]
    try omega
  have e : j = i := Result.ok_injective (hj.symm.trans h)
  subst e
  omega

/-- **The kernel-state-block PTE facts at a bundle state**, from `PteSl`. -/
theorem pteKs_at (hPS : PteSl st K) {s : S} (hJ : SlJAt (L := L) K.toKLayout s) {o : U64} (ho : o.val < 13568) :
    core.num.U64.wrapping_add (L.ksb s) o ∉ K.ptes := by
  rw [slJAt_ksb hJ]; exact hPS.1 o ho

end lay

/-! ## The irq slot -/

section irq
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The timer interrupt's route-U path reads no PTE word**, from `PteSl` [J]. -/
theorem irq_avoidP_path (i : IrqArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (irqSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) ((irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  have hKr := regionOK_userP hK.base
  have facts : ∀ s, IrqPreV K.toKLayoutV st m s →
      ∃ Ω Ac : Set U64, IrqEnt (userP K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap
        (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac
        i.irq s := by
    intro s hs
    obtain ⟨Ω, Ac, hE⟩ := hs.entM hK.base vf h.2.lt
    exact ⟨Ω, Ac, irqEnt_userP hK hE.ent (fun hb j hj => pteKs_at hPS hs.1 (state_off_lt hb hj))
      (pteKs_at hPS hs.1 (by simp [layout.ks.KERNEL_ROOT])) (hPS.2 s hs.1)
      (pteKs_at hPS hs.1 (by simp [layout.ks.CUR_DOMAIN]))
      (pteKs_at hPS hs.1 (by simp [layout.ks.DOMAIN_TIME]))⟩
  refine avoidE_of_entry (P := (irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h)
    (E := (· ∈ K.ptes)) (irq_noZero i.irq i.pl) (IsProg.on (irq_isProg S i.irq i.pl) _ _ _)
    (fun s => MaxR (L := L) (userP K) st i.lk s) (fun s => MaxW (L := L) (userP K) st i.lk s)
    (fun s x _ hx hp => hx.2.2 (Or.inr hp)) ?_
    (fun s => MaxR (L := L) (userP K) st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => ⟨hx.2.1, ⟨hx.1, hx.2.1, fun hu => hx.2.2 (Or.inl hu)⟩, fun hp => hx.2.2 (Or.inr hp)⟩)
    (fun s x hs hx => by
      obtain ⟨Ω, Ac, hE⟩ := facts s hs
      exact (hE.dec hx).1) ?_
  · intro s a r hs hr hb
    have hs' : IrqPreV K.toKLayoutV st m s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localtimer.handle_timer_irq_local st ar s a i.irq i.pl = ok (true, s1, a1) := hr
    obtain ⟨Ω, Ac, hE⟩ := facts s hs'
    have hEK : IrqEntK (userP K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac (L.mem s) s :=
      ⟨hE.inv, hE.lay, fun _ _ _ => rfl, hE.asid⟩
    have hQ := slJAt_slotJC (st := st) hs'.1
    have hOL : ObjLay (userP K) K.heap (Heap.replies K.heap) := hQ.slotJ.objLay (fun r hr => hr)
    have hSL : SlotLayV (userP K) st (Heap.tcbs K.heap) s := hQ.slotJ.slotLayV (fun y hy => hy)
    have g : localtimer.handle_timer_irq_local (guard st (MaxR (userP K) st i.lk s) (MaxW (userP K) st i.lk s))
        ar s a i.irq i.pl = ok (true, s1, a1) :=
      irq_acc_own ar hA hKr hEK hE.ly hE.aff (fun hf => by
        by_cases hnw : NoWake st s
        · exact irq_acc_fire_nw ar hA hKr hEK hE.ly hE.aff hE.nth hf hnw hr'
        · obtain ⟨U, hB⟩ := hQ.bufAt
          exact irq_acc_fire_wk2 ar hA hKr hEK hE.ly hE.aff hE.nth hOL h.2.pl
            (irq_bufAt_runB ar hA hE.inv hB hf hr') hSL hf hnw hr') hr'
    exact g
  · intro s a r hs hr hb
    have hs' : IrqPreV K.toKLayoutV st m s := hs
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localtimer.handle_timer_irq_local st ar s a i.irq i.pl = ok (false, s1, a1) := hr
      obtain ⟨Ω, Ac, hE⟩ := facts s hs'
      have g : localtimer.handle_timer_irq_local (guard st (MaxR (userP K) st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl = ok (false, s1, a1) :=
        irq_dec_guard ar hA hKr hE.inv hE.lay hE.ly hE.aff hE.nth hr'
      exact g
    · exact absurd rfl hb

/-- **The timer interrupt reads no PTE word** (the `irq` field of `P3AvP`), from `PteSl` [J]. -/
theorem irq_avoidP (i : IrqArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (hPS : PteSl st K) (h : (irqSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K ((irqSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)) := by
    rintro P W rfl
    exact avoidE_liftAtV hK.base _ W (irq_avoidP_path st ar hA hm i K m hK hU hPS h)
  exact key _ _ (SlotU.fam_pos _ _ h)

end irq

end
end Fl4Proofs.P2.E2EP
