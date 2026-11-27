/-
P2 (line famw, gen 4): **vt's `ro` [W] discharged at P3 scope** (new definitions only; no existing statement changes,
no lvm / hpzg file edited, no `kernel_entry_reach*` touched).

`VtPremP3.ro` (int16's vt slot, `vtimer_localPathF`) is `ReadOnce` of the VM-timer tree at `Pre := VtPre` with
`RS := VexitRS`. hpzg's `vtimer_hro` (P2/LvmOnce.lean) proves exactly that from `hVU` [J], `hTU` [J] and the fire /
decline runs on the user-free guard `guard st (VexitRSU s) …` (`hFU` / `hDU`). This file supplies those:

* **`vtimer_dec_ownU`** / **`vtimer_acc_fnw_ownU`** / **`vtimer_acc_fwk_ownU`**: lvm's `vtimer_dec_own` /
  `vtimer_acc_fnw_own` / `vtimer_acc_fwk_own` (gen 9/10, P2/AccessLvmTd/Tf/Tv.lean) re-run at `R := VexitRSU`, i.e.
  lvm's generic `vtimer_decG` / `vtimer_accG_fnw` / `vtimer_accG_fwk` (they hold for any read set) with every read
  callback paired with `∉ K.user`. **No read of the fire or decline path is a user word**:
  - words in a typed region (`fire_rdG`'s `region ≠ .none`, `loc_rd_own`'s TCB words, SC words, endpoint words,
    `lkw_own`'s queue links, the VSpace slot words `slot_rdVU`): `StLay.nu` (a user word has region `.none`,
    `StLay.user`; this is the lemma int16's docstring missed);
  - `FireRd` / `IrqRd` / `TmWords` words: `fire_rd_nu` / `vexit_rd_nu` / `tmw_nu` (with `irqLay_ofVtm`);
  - the domain words: `StLay.domU` / `dtmU`; the bound notification's `TAIL_STATE`: `ntfn_tail_nu`;
  - the bound VCPU's `PENDING`: `VcpuNU` (`vcpuNU_empty` at `K.vcpus = ∅`);
  - the IRQ state word, the kernel root word, the ASID table and pool words: `VtmU` (`hTU`).
  The IPC buffer of a woken thread is only **written** (`UserOK` / `BufOK U` enter `vtimer_accG_fwk` as write-side
  facts; `VexitWS` allows user words), never read, so no fire-path read is a user word.
* `VtPremP5` = `VtPremP3` minus `ro` [W], plus `nv` (`K.vcpus = ∅`, the glue's layout choice at P3 scope) and
  **`tu` [J]**: `∀ s, VtPre s → VtmU K st irq s` (hpzg's `hTU`). `VtPremP5.toP3` builds `ro` by `vtimer_hro`.
  `vtSlotP3W5` = int16's `vtSlotP3` with records `VtPremP5` (`SlotN.pullK`: same path, `ro` built from the slot's
  `RegionOKV`); `fl4LocP3W5` = `fl4LocP3W` with it; `StartP3W5` = `StartP3W4` (famw gen 3) with the vt index's
  record `VtPremP5`; **`serializable_fl4_localW5`**.

**Why `tu` [J] stays (not derived here).** `ReadOnce` quantifies over every `VtPre` state, and `VtPre` (lvm's `VtmEnt`)
carries no bundle: it gives the IRQ-state / kernel-root / ASID words region `.none`, which does not exclude user
words (user words are region `.none` too). At a bundle state P3 gives all of `VtmU` (`irqLayK_of_slJAt`'s `iqU` /
`krU` / `tabU`); at an arbitrary `VtPre` state the IRQ-state and kernel-root words reduce to layout facts once
`L.ksb s = K.ksb` is pinned (from `StLay.nd`) and `SlJAt.userKs` at one bundle state, but the **ASID pool words**
`peAF (mem s (atAF hi)) lo` depend on the state's memory, and nothing in `VtPre` keeps a pool pointer off user
frames (both are `.other` heap objects). So `tu` is the residue: a [J] about non-bundle `VtPre` states, true at
bundle states.

## Premise table diff vs `serializable_fl4_localW4`

| slot | removed | added |
|---|---|---|
| vt (record) | `ro` [W] | `nv` (glue's layout choice), `tu` [J] (`VtmU` at `VtPre` states: IRQ state, kernel root, ASID table / pool words are no user words) |

Remaining [W] of the P3-scope chain: sl `ro` only.
-/
import Fl4Proofs.P2.E2EVFl4W4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu RegionOKV UserOKV rpermV_of_own wpermV_of_own'
  stepOKV_of_stepOK)

section ownU
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- **`IrqLay` at a VM-timer entry**: the region facts from `VtmEnt`, the non-user facts from `VtmU`. -/
theorem irqLay_ofVtm {s : S} {irq n : U64} (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (hTU : VtmU K st irq s) : IrqLay K.toKLayout st Nt irq s :=
  ⟨fun hb i hi => ⟨(hE.iq hb i hi).1, (hE.iq hb i hi).2.1⟩, ⟨hE.kr.1, hE.kr.2.1⟩,
    fun hi hhi => ⟨⟨(hE.tab hi hhi).1.1, (hE.tab hi hhi).1.2.1⟩,
      fun lo hlo hne => ⟨((hE.tab hi hhi).2 lo hlo hne).1, ((hE.tab hi hhi).2 lo hlo hne).2.1⟩⟩,
    hE.ent.ntw, hE.ent.cs, hTU.iqU, hTU.krU, hTU.tabU⟩

/-- **The VSpace slot words of a local thread are in `VexitRSU`** (`slot_rdV` and their slot regions). -/
theorem slot_rdVU (hK : RegionOKV K) {s : S} (hT : TcbPlaced T) (hSL : SlotLayV K.toKLayout st T s)
    (hL : StLay K.toKLayout st T Scs Z s) {y : U64} (hy : LocT st T s y) :
    VexitRSU K st lk s (vtA y) ∧ VexitRSU K st lk s (core.num.U64.wrapping_add (vtA y) 8#u64) := by
  obtain ⟨r1, r2⟩ := slot_rdV (lk := lk) hK hT hSL hL.user hy
  have hy' := hT y hy.1
  have e1 : vtA y = core.num.U64.wrapping_add y 32#u64 := by
    apply UScalar.eq_of_val_eq
    rw [vtA_val hy', tcb_wadd_val hy' (by simp)]; simp
  have e2 : core.num.U64.wrapping_add (vtA y) 8#u64 = core.num.U64.wrapping_add y 40#u64 := by
    apply UScalar.eq_of_val_eq
    have := hy'.fits
    rw [tcb_wadd_val hy' (by simp)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vtA_val hy']
    omega
  obtain ⟨p1, q1, -⟩ := hSL y hy 32#u64 (Or.inl (by simp))
  obtain ⟨p2, q2, -⟩ := hSL y hy 40#u64 (Or.inr (by simp))
  exact ⟨⟨r1, hL.nu (by rw [e1, q1]; intro e; cases e)⟩, ⟨r2, hL.nu (by rw [e2, q2]; intro e; cases e)⟩⟩

/-- **`vtimer_dec_own` on the user-free read set `VexitRSU`** (module docstring): `hDU` of `vtimer_hro`. -/
theorem vtimer_dec_ownU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hTU : VtmU K st irq s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (false, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (IrqDec st s)) ar s a irq p n =
      ok (false, s', a') := by
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hY := irqLay_ofVtm hE hTU
  have rD : VexitRSU K st lk s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩
  exact vtimer_decG (gS := guard st (VexitRSU K st lk s) (IrqDec st s)) (R := VexitRSU K st lk s)
    (W := IrqDec st s) ar hA hI
    (fun w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL E.ntw E.cs E.aff E.curAff E.cscCore hw)⟩, vexit_rd_nu hI hL E.ntw E.cs hw⟩)
    rD
    ⟨⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩
    (fun hb i hi => ⟨⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩, hTU.iqU hb i hi⟩)
    (fun hne w ha hw => ⟨⟨ha, Or.inr (tmw_ownV hK hI hL E.ntw hne hw)⟩, tmw_nu hI hL hY hne hw⟩)
    (fun s1 tip k1 c1 m1 etip esp ct now =>
      fire_rdG hK.base hI hL E.ntw (lk := lk s) (fun w hp ha hr => ⟨⟨ha, Or.inr (rpV hK hr hp)⟩, hL.nu hr⟩) rD hNt k1 c1 m1
        etip esp ct now)
    (fun hv0 => ⟨⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩, hVU _ _ (E.vin hv0)⟩)
    (fun n' hbn hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL E.ntw hn⟩)
    (Or.inl rfl) (Or.inr rfl) h

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop}

/-- **`vtimer_acc_fnw_own` on `VexitRSU`** (module docstring): the non-waking half of `hFU`. -/
theorem vtimer_acc_fnw_ownU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hTU : VtmU K st irq s) (hq : IrqFire st ar s a) (hNW : NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a irq p n =
      ok (true, s', a') := by
  have hb := vtimer_irq_lt ar h
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hY := irqLay_ofVtm hE hTU
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  have rD : VexitRSU K st lk s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩
  have wr : ∀ (X : S) (w v' : U64), VexitWS K st lk s w →
      (guard st (VexitRSU K st lk s) (VexitWS K st lk s)).write X w v' = st.write X w v' :=
    fun X w v' hw => PathObl.GWr.write (g := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) hw X v'
  exact vtimer_accG_fnw (gS := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) (R := VexitRSU K st lk s)
    (W := VexitWS K st lk s) ar hA hI hNt
    (fun hok hTm w ha hw => ⟨⟨ha, Or.inr (fire_rdV hK hI hL E.ntw E.cs E.aff hok hTm hw)⟩, fire_rd_nu hI hL hY hw⟩)
    (fun hok hTm w ha hw _ => ⟨ha, Or.inr (fire_wrV hK hI hL E.ntw hok hTm hw)⟩)
    (fun i hi => ⟨⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩, hTU.iqU hb i hi⟩)
    rD ⟨⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩
    (fun s1 k1 c1 m1 now => by
      obtain ⟨mx, tip, -, -, -, etip, eb, -⟩ := vtimer_split ar h
      exact fire_rdG hK.base hI hL E.ntw (lk := lk s) (fun w hp ha hr => ⟨⟨ha, Or.inr (rpV hK hr hp)⟩, hL.nu hr⟩) rD hNt k1 c1
        m1 etip eb _ now)
    (fun X y v' hy ha _ => wr X _ v' ⟨field_aligned (hT y hy) (by simp) (by simp),
      Or.inr (wpermV_of_own' hK (held_core (ftree_own hL hT hy ha (k := 3568#u64) (by simp) (by simp) (by simp))))⟩)
    (fun X y v' hy ha _ _ _ => wr X _ v' ⟨field_aligned (hT y hy) (by simp) (by simp),
      Or.inr (wpermV_of_own' hK (held_core (ftree_own hL hT hy ha (k := 3528#u64) (by simp) (by simp) (by simp))))⟩)
    hvb ⟨⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩, hVU _ _ (E.vin hv0)⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL E.ntw hn⟩)
    (E.vfar hv0) (fun hn => E.nfar n hbn hn)
    (fun hne hb0 => pending_not_sad hK hE hv0 hne hb0)
    hq hNW h

set_option maxHeartbeats 16000000 in
/-- **`vtimer_acc_fwk_own` on `VexitRSU`** (module docstring): the waking half of `hFU`. -/
theorem vtimer_acc_fwk_ownU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hNt : ∀ q ∈ Nt, H q = some .ntfn)
    {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan} {U : Set U64}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hTU : VtmU K st irq s) (hOL : ObjLay K.toKLayout H Rp) (hPL : PlanLk lk p)
    (hU : UserOK st T Cs Ω H U s) (hbU : ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hSL : SlotLayV K.toKLayout st T s) (pSg : core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ Sg)
    (hq : IrqFire st ar s a) (hWk : ¬ NoWake st s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a irq p n =
      ok (true, s', a') := by
  have hb := vtimer_irq_lt ar h
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  obtain ⟨-, tip, -, -, -, etip, eb, -⟩ := vtimer_split ar h
  obtain ⟨hPE, hPR⟩ := plan_pe_pr hE.ent.inv etip eb
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  have hY := irqLay_ofVtm hE hTU
  have hT : TcbPlaced T := hI.1.choose_spec.choose_spec.tcbs
  have vRd : ∀ w, Aligned w → region K.toKLayout w ≠ .none → RPerm (own K.toKLayout) (L.cpu s) (lk s) (L.mem s) w →
      VexitRSU K st lk s w := fun w ha hr hp => ⟨⟨ha, Or.inr (rpV hK hr hp)⟩, hL.nu hr⟩
  have vWr : ∀ w, Aligned w → WPerm (own K.toKLayout) (L.cpu s) (lk s) (L.mem s) w → VexitWS K st lk s w :=
    fun w ha hp => ⟨ha, Or.inr (wpermV_of_own' hK hp)⟩
  have treg : ∀ {y k : U64}, y ∈ T → 256 ≤ k.val → k.val < 4096 →
      region K.toKLayout (core.num.U64.wrapping_add y k) ≠ .none := fun hy h1 h2 => by
    have e := hL.tcb _ hy _ h1 h2
    unfold fld at e
    rw [e]; simp
  have rD : VexitRSU K st lk s (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN) :=
    ⟨⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩
  have wr : ∀ (X : S) (w v' : U64), VexitWS K st lk s w →
      (guard st (VexitRSU K st lk s) (VexitWS K st lk s)).write X w v' = st.write X w v' :=
    fun X w v' hw => PathObl.GWr.write (g := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) hw X v'
  have g3328 : ¬ GateField (3328#u64 : U64).val := by unfold GateField; simp
  have t3328 : ¬ TimerField (3328#u64 : U64).val := by unfold TimerField; simp
  have f3328 : ¬ GField (3328#u64 : U64).val := by unfold GField; simp
  exact vtimer_accG_fwk (gS := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) (R := VexitRSU K st lk s)
    (W := VexitWS K st lk s) (Lk := lk s) (U := U) ar hA hI hNt
    (fun hok hTm w ha hw => ⟨⟨ha, Or.inr (fire_rdV hK hI hL E.ntw E.cs E.aff hok hTm hw)⟩, fire_rd_nu hI hL hY hw⟩)
    (fun hok hTm w ha hw _ => ⟨ha, Or.inr (fire_wrV hK hI hL E.ntw hok hTm hw)⟩)
    (fun i hi => ⟨⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩, hTU.iqU hb i hi⟩)
    rD ⟨⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩
    (fun s1 k1 c1 m1 now =>
      fire_rdG hK.base hI hL E.ntw (lk := lk s) (fun w hp ha hr => ⟨⟨ha, Or.inr (rpV hK hr hp)⟩, hL.nu hr⟩) rD hNt k1 c1
        m1 etip eb _ now)
    (fun X y v' hy ha _ => wr X _ v' ⟨field_aligned (hT y hy) (by simp) (by simp),
      Or.inr (wpermV_of_own' hK (held_core (ftree_own hL hT hy ha (k := 3568#u64) (by simp) (by simp) (by simp))))⟩)
    (fun X y v' hy ha _ _ _ => wr X _ v' ⟨field_aligned (hT y hy) (by simp) (by simp),
      Or.inr (wpermV_of_own' hK (held_core (ftree_own hL hT hy ha (k := 3528#u64) (by simp) (by simp) (by simp))))⟩)
    hvb ⟨⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩, hVU _ _ (E.vin hv0)⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL E.ntw hn⟩)
    (E.vfar hv0) (fun hn => E.nfar n hbn hn) pSg (pending_not_q hK hE hOL hv0) E.aff
    (fun y hy K h1 h2 h3 ht hg => vRd _ (field_aligned (hT y hy.1) h2 h3) (treg hy.1 h1 h2)
      (loc_rd_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, ht, hg, rfl⟩))))
    (fun y hy K h1 h2 h3 hga ht hg _ _ => vWr _ (field_aligned (hT y hy.1) h2 h3)
      (loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, K, h1, h2, h3, hga, ht, hg, rfl⟩))))
    (fun q hq hc b ha hb => vRd _ ha (by rw [hL.sc _ hq _ hb]; simp)
      (loc_rd_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb⟩))))
    (fun q hq hc b ha hb h16 => vWr _ ha (loc_wr_own hI hL (Or.inr (Or.inr ⟨q, hq, hc, hb, h16⟩))))
    (fun y hy hqs hlk k hk => by
      have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inl ⟨y, hy, hqs, hlk, k, hk, rfl⟩)
      have ha := field_aligned (hT y hy) (K := k) (by omega) (by omega)
      exact ⟨vRd _ ha (treg hy (by omega) (by omega)) o.2, vWr _ ha o.1⟩)
    (fun X y v' hy _ _ _ => wr X _ v' (vWr _ (by rw [stA_eq]; exact field_aligned (hT y hy.1) (by simp) (by simp))
      (loc_wr_own hI hL (Or.inr (Or.inl ⟨y, hy, 3328#u64, by simp, by simp, by simp, g3328, t3328, f3328,
        stA_eq _⟩)))))
    (fun hn => (hPL s).1 hn) (fun hep => (hPL s).2.1 hep)
    (fun hok hTm h1 h2 k hk h8 h24 => by
      have h0 := hI.1.choose_spec.choose_spec
      obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur h1
      obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ (hI.2.2.1.2.2.bnd _ q1 h2)
      exact ⟨by unfold Aligned; rw [ntfn_word_val p1 p2 hk]; omega,
        Or.inr (fire_wrV hK hI hL E.ntw hok hTm (Or.inr (Or.inr ⟨h1, h2, k, hk, h8, h24, rfl⟩)))⟩)
    (fun hep k h1 h2 => by
      obtain ⟨hH, hal⟩ := hPE hep
      have o := lkw_own hI hL (Lk := lk s) (fun _ h => h) (Or.inr ⟨p.ep, (hPL s).2.1 hep, hOL.1 _ hH k h1⟩)
      exact ⟨vRd _ (hal k h1 h2) (by rw [hOL.1 _ hH k h1]; simp) o.2, vWr _ (hal k h1 h2) o.1⟩)
    (fun hr => by
      obtain ⟨hR, hal⟩ := hPR hr
      have o := lkw_own hI hL (Lk := lk s) (w := rTcbA p.reply) (fun _ h => h)
        (Or.inr ⟨p.reply, (hPL s).2.2 hr, by unfold rTcbA; exact hOL.2 _ hR _ (by simp [layout.reply.TCB])⟩)
      exact vWr _ hal o.1)
    hU hbU hE.asid (fun y hy => slot_rdVU (lk := lk) hK hT hSL hL hy)
    ⟨⟨hE.kr.1, Or.inr (rpermV_of_own hE.kr.2.2 (rperm_none hE.kr.2.1 _))⟩, hTU.krU⟩
    (fun hi hhi => ⟨⟨⟨(hE.tab hi hhi).1.1, Or.inr (rpermV_of_own (hE.tab hi hhi).1.2.2
        (rperm_none (hE.tab hi hhi).1.2.1 _))⟩, (hTU.tabU hi hhi).1⟩,
      fun lo hlo hne => ⟨⟨((hE.tab hi hhi).2 lo hlo hne).1, Or.inr (rpermV_of_own ((hE.tab hi hhi).2 lo hlo hne).2.2
        (rperm_none ((hE.tab hi hhi).2 lo hlo hne).2.1 _))⟩, (hTU.tabU hi hhi).2 lo hlo hne⟩⟩)
    hq hWk h

end ownU
end Fl4Proofs.P2

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY region TcbSlot)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-- A native slot under a new premise record giving the old one at the slot's layout facts. -/
def SlotN.pullK {ι : Type} (X : SlotN ι) (P : ι → KLayoutV → (U64 → U64) → Prop)
    (f : ∀ {i K m}, RegionOKV K → UserOKV K → P i K m → X.Prem i K m) : SlotN ι where
  Prem := P
  path i K m hK hU h := X.path i K m hK hU (f hK hU h)

section vt
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vt's premises with `ro` discharged** (module docstring): `VtPremP3` minus `ro` [W], plus `nv` and `tu` [J]. -/
structure VtPremP5 (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope; gives `VcpuNU`). -/
  nv : K.vcpus = ∅
  /-- [J] hpzg's `hTU`: at every `VtPre` state the IRQ state word, the kernel root word and the ASID table / pool
  words are no user words (P3 gives it at bundle states, `irqLayK_of_slJAt`; module docstring). -/
  tu : ∀ s, VtPre st i K s → VtmU K st i.irq s
  /-- [J] -/
  eu : ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] the map memory agrees with the entry on every thread's `AFFINITY`. -/
  M : ∀ s, VtPre st i K s → ∀ y ∈ i.T, m (fld y oAFFINITY) = L.mem s (affA y)
  /-- [J] endpoints and replies lie in their object regions. -/
  OL : ObjLay K.toKLayout i.H i.Rp
  /-- [P] the glue holds the plan's notification / endpoint / reply locks. -/
  PL : PlanLk i.lk i.pl
  /-- [J] some user-word set with P1 `UserOK` holding every TCB's IPC-buffer lookup. -/
  UB : ∀ s, VtPre st i K s → ∃ U : Set U64, Fl4Proofs.P1.UserOK st i.T i.Cs i.Ω i.H U s ∧
    ∀ y ∈ i.T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [J] the VSpace slot words of this core's threads lie in TCB slot regions. -/
  SL : ∀ s, VtPre st i K s → SlotLayV K.toKLayout st i.T s
  /-- [J] the bound VCPU's `PENDING` is no frame word. -/
  pSg : ∀ s, VtPre st i K s → core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ i.Sg

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

include hA hm in
/-- **`VtPremP3` from `VtPremP5`**: `ro` by hpzg's `vtimer_hro` with `hFU` / `hDU` from the `VexitRSU` runs. -/
theorem VtPremP5.toP3 {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (hK : RegionOKV K) (h : VtPremP5 st i K m) :
    VtPremP3 st ar i K m where
  ro := vtimer_hro ar hA hK (vcpuNU_empty h.nv) hm h.tu
    (fun s a s1 a1 hE hq hr => by
      by_cases hNW : NoWake st s
      · exact vtimer_acc_fnw_ownU ar hA hK (vcpuNU_empty h.nv) h.Nt hE (h.tu s hE) hq hNW hr
      · obtain ⟨U, hU, hbU⟩ := h.UB s hE
        exact vtimer_acc_fwk_ownU ar hA hK (vcpuNU_empty h.nv) h.Nt hE (h.tu s hE) h.OL h.PL hU hbU (h.SL s hE)
          (h.pSg s hE) hq hNW hr)
    (fun s a s1 a1 hE hr => vtimer_dec_ownU ar hA hK (vcpuNU_empty h.nv) h.Nt hE (h.tu s hE) hr)
  eu := h.eu
  kd := h.kd
  Nt := h.Nt
  M := h.M
  OL := h.OL
  PL := h.PL
  UB := h.UB
  SL := h.SL
  pSg := h.pSg

/-- **vt slot at P3 scope, `ro` discharged** (`vtSlotP3`'s path at the record `VtPremP5.toP3`). -/
def vtSlotP3W5 : SlotN (VtArg S) :=
  (vtSlotP3 st ar hA hm).pullK (VtPremP5 st) (fun hK _ h => h.toP3 st ar hA hm hK)

/-- lvm's paths at P3 scope with vt's `ro` discharged. -/
def fl4LQP3W5 (D : Dflt) : PathsV (VxArg S ⊕ VtArg S) :=
  PathsV.sum ((vxSlotP3 st ar hA hm).fam D) ((vtSlotP3W5 st ar hA hm).fam D)

variable (hSt : P0.StoreTotal st) (a0 : A)

/-- **`fl4LocP3W` with vt's `ro` discharged.** -/
def fl4LocP3W5 : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlot st ar hA hm
  vmR := vmRSlotP3 st ar hA hm
  io := ioSlotP3W st ar hA hm
  st := stSlotP3W st ar hA hm
  irq := irqSlotP3W st ar hA hm
  sl := slSlotP3 st ar hA hSt hm a0
  vq := fl4LQP3W5 st ar hA hm (fl4Dflt st ar hm)

/-- **The start fact of `fl4LocP3W5`**: `StartP3W4` with the vt index's record `VtPremP5`. -/
def StartP3W5 (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vq (.inr j) => ∃ h : VtPremP5 st j K m, GlueAt ((vtSlotP3W5 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VtEntJ4 st j K σ) c hs m q
  | i => StartP3W4 st ar hA hSt hm a0 Ch K m hK hU c hs q i

/-- **`StartAt` of `fl4LocP3W5`'s family from the start fact**, given clause 7 on the chain. -/
theorem startAt_P3W5 {Ch : S → Prop} {K : KLayoutV} (hCh : ∀ σ, Ch σ → SlJAt (L := L) K.toKLayout σ)
    {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K} {c : U64} {hs : U64 → Prop} {q : SP}
    {i : Fl4IxW (S := S)} (h : StartP3W5 st ar hA hm hSt a0 Ch K m hK hU c hs q i) :
    StartAt ((fl4LocP3W5 st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K m hK hU) c hs m q := by
  cases i with
  | vq j =>
    cases j with
    | inl j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .vq (.inl j)) h)
    | inr j =>
      obtain ⟨h, hG⟩ := h
      show StartAt ((vtSlotP3W5 st ar hA hm).fam (fl4Dflt st ar hm) j K m hK hU) c hs m q
      rw [SlotN.fam_pos _ _ h]
      exact hG.startAt fun σ he _ => (he.2.toJ st).pre st (hCh σ he.1)
  | vmF j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .vmF j) h)
  | vmR j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .vmR j) h)
  | io j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .io j) h)
  | st j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .st j) h)
  | irq j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .irq j) h)
  | sl j => exact startAt_P3W st ar hA hSt hm a0 hCh (startP3W_of_W4 st ar hA hSt hm a0 (i := .sl j) h)

end vt

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

omit [Fl4Proofs.P1.PlainStore st] in
/-- **`fl4LocP3W5` over `ExecV`.** -/
theorem serializable_fl4_localP3W5V {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV ((fl4LocP3W5 st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localG _ _ h0 hA0 hK0 hU0 hM0 h hq

end top

end
end Fl4Proofs.P2.E2EV
