/-
P2 (line pte, gen 4): **the VM-timer and VM-exit paths read no PTE word** (the `vt` and `vx` fields of `P3AvP2`,
discharged) and **`serializable_fl4_localP3P3`**.

* **`avoidE_of_entry`** (generic, any path, any excluded set `E`): `AvoidE E P` from two runs at the *entry* state
  on guarded stores whose read sets avoid `E` — an accepted run on `guard (Ra s) (Wa s)` (combined with the path's
  own `acc` by `within_and`) and a declined run on `guard (Rd s) (Wd s)` with `Rd s ⊆ RS s` (carried to every
  alternative by `interp_agree`, `NoZero`). This is how the decline half of `AvoidE` follows from entry-state walks.
* **The layout trick** `KLayoutP.pteU K`: `K`'s VCPU layout with **the PTE words as its "user" set**. `own` / `ownV`
  / `region` do not read `user`, so every region fact transfers by definition, and hpzg / famw's user-free walks at
  `R := VexitRSU (pteU K)` (`vtimer_acc_ownU`, famw gen 4's `vtimer_acc_fnw_ownU` / `vtimer_acc_fwk_ownU` /
  `vtimer_dec_ownU`, merged from par/famw 3ec6f9a8) become **PTE-free** walks: `VexitRSU (pteU K) s ⊆ VexitRS K s ∖ ptes`.
  Their user-side premises at `pteU K` are PTE facts: `StLay.user` (a PTE is region `.none`: `RegionOKP.none`),
  `VcpuNU` (a PTE is in no VCPU: `RegionOKP.novcpu`), and `VtmP` below.
* **`VtmP K st irq s` [J]** (per `VtPre` state; the PTE counterpart of famw's `VtmU` / `tu`): the two domain words,
  the IRQ state word, the kernel root word and the ASID table / pool words are no PTE words. Source: P1 `HeapOK`
  (page-table pages, the kernel-state block, the ASID table and the ASID pools are distinct objects). Not derived
  from `PteSl`: `PteSl`'s table half is stated at bundle (`SlJAt`) states, and `VtPre` carries no bundle (famw gen 4's
  docstring: the pool words depend on the state's memory).
* vx: hpzg's `vexit_acc_own_npU` / `vexit_acc_own_pU` / `vexit_dec_ownU` (P2/LvmOnce.lean) copied as
  `vexit_acc_own_npP` / `vexit_acc_own_pP` / `vexit_dec_ownP` at `R := VexitRSP K = VexitRS K ∖ ptes`, `W` unchanged
  (the pending case writes the caller's IPC buffer, user words, so the `pteU` layout cannot be used there: `VexitPEnt`
  ties the buffer to `K.user`); each read's "no PTE" fact is the original's "no user" lemma at `pteU K`
  (`vexit_rd_nu`, `ntfn_tail_nu` with `stLay_pteU`; `vcpu_nu` with `vcpuNU_pteU`), the domain words from
  **`VxP K s` [J]** (per `VxPre` state; P1 `HeapOK`).
* **`vt_avoidP`**, **`vx_avoidP`**, `P3AvP3` (= `P3AvP2` − `vt` − `vx` + `vtP` [J] + `vxP` [J]), `P3AvP3.toP2`,
  **`serializable_fl4_localP3P3`**.

Remaining [W] (`P3AvP3` fields): vmF, vmR, io, stm, irq (module docstring of `P2/E2EPSlP.lean` for the reasons).
-/
import Fl4Proofs.P2.E2EPSlP
import Fl4Proofs.P2.E2EVFl4W5
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## `AvoidE` from entry-state walks -/

section gen
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **`AvoidE` from guarded runs at the entry state** (module docstring). -/
theorem avoidE_of_entry (P : E2E.LocalPath own cls ko User) {E : U64 → Prop} (hz : NoZero P.p)
    (hprog : IsProgOn (P.F P.ar) P.ar P.st (@AltOf P.S P.st P.L P.Pre (rsE E P.RS) cls ko User) P.p)
    (Ra Wa : P.S → U64 → Prop) (hRa : ∀ s x, P.Pre s → Ra s x → ¬ E x)
    (hacc : ∀ s a r, P.Pre s → P.F P.ar P.st s a = ok r → P.Acc r.1 →
      P.F P.ar (guard P.st (Ra s) (Wa s)) s a = ok r)
    (Rd Wd : P.S → U64 → Prop) (hRd : ∀ s x, P.Pre s → Rd s x → Aligned x ∧ P.RS s x ∧ ¬ E x)
    (hWd : ∀ s x, P.Pre s → Wd s x → Aligned x)
    (hdec : ∀ s a r, P.Pre s → P.F P.ar P.st s a = ok r → ¬ P.Acc r.1 →
      P.F P.ar (guard P.st (Rd s) (Wd s)) s a = ok r) :
    AvoidE E P := by
  letI := P.L
  have e := fun (st' : machine.Store P.S) (N : Narrow P.st st') (σ : P.S)
    (g : AltOf P.st P.Pre P.RS cls ko User σ) (a : P.A) => P.isProg st' N σ g a
  refine ⟨?_, ?_, hprog⟩
  · intro s a r hs h hac
    have g0 : AltOf P.st P.Pre P.RS cls ko User s := AltOf.pre hs
    have w1 := (interp_guard P.p s a r ((e _ (Narrow.guard _ _ _) s g0 a).symm.trans (P.obl.acc s a r hs h hac))).2
    have w2 := (interp_guard P.p s a r ((e _ (Narrow.guard _ _ _) s g0 a).symm.trans (hacc s a r hs h hac))).2
    exact (e _ (Narrow.guard _ _ _) s g0 a).trans (guard_of_within P.p s a r ((e _ (Narrow.self _) s g0 a).symm.trans h)
      (Within.mono (fun b hb => ⟨hb.1, hRa s b hs hb.2⟩) (fun b hb => hb.1) P.p s a (Fl4Proofs.P2.E2E.within_and P.p s a w1 w2)))
  · intro s a r hs h hn s' r' hA h'
    have g0 : AltOf P.st P.Pre P.RS cls ko User s := AltOf.pre hs
    have g1 : AltOf P.st P.Pre P.RS cls ko User s' := ⟨s, hs, hA⟩
    obtain ⟨x, s1, a1⟩ := r
    have hg := (e _ (Narrow.guard _ _ _) s g0 a).symm.trans (hdec s a _ hs h hn)
    obtain ⟨s1', hg'⟩ := interp_agree P.masks (fun w hw => (hRd s w hs hw).1) (fun w hw => hWd s w hs hw) P.p hz
      s s' a x s1 a1 hA.ksb hA.cpu hA.masks (fun w hw => hA.read w (hRd s w hs hw).2.1) hg
    obtain ⟨hr', w⟩ := interp_guard P.p s' a _ hg'
    have er : r' = (x, s1', a1) := Result.ok_injective (((e _ (Narrow.self _) s' g1 a).symm.trans h').symm.trans hr')
    subst er
    exact (e _ (Narrow.guard _ _ _) s' g1 a).trans (guard_of_within P.p s' a _ hr'
      (Within.mono (fun b hb => (hRd s b hs hb).2.2) (fun _ _ => trivial) P.p s' a w))

end gen

/-! ## The layout with the PTE words as "user" words -/

/-- `K`'s VCPU layout with the PTE words as its user set (module docstring). -/
def _root_.Fl4Proofs.P2.OwnMapP.KLayoutP.pteU (K : KLayoutP) : KLayoutV := { K.toKLayoutV with user := K.ptes }

section lvm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}

/-- **`VtmP`** [J] (module docstring): the kernel-state, IRQ-state, kernel-root and ASID words a VM-timer run reads
are no PTE words. Source: P1 `HeapOK` (distinct objects). -/
structure VtmP (K : KLayoutP) (st : machine.Store S) [L : LawfulStore st] (irq : U64) (s : S) : Prop where
  domP : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes
  dtmP : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes
  iqP : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → core.num.U64.wrapping_add (L.ksb s) i ∉ K.ptes
  krP : krA (L := L) s ∉ K.ptes
  tabP : TabNoE (L := L) (· ∈ K.ptes) s

theorem regionOK_pteU (hK : RegionOKP K) : OwnMap.RegionOK K.pteU.toKLayout where
  tcb := hK.base.base.tcb
  slot := hK.base.base.slot
  ntfn := hK.base.base.ntfn
  scw := hK.base.base.scw
  tcbOf := hK.base.base.tcbOf
  slotOf := hK.base.base.slotOf
  ntfnOf := hK.base.base.ntfnOf

theorem regionOKV_pteU (hK : RegionOKP K) : RegionOKV K.pteU where
  base := regionOK_pteU hK
  none := hK.base.none
  disj := hK.base.disj
  tcbw := hK.base.tcbw

theorem stLay_pteU (hK : RegionOKP K) {s : S} (hL : StLay K.toKLayout st T Scs Z s)
    (h1 : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes)
    (h2 : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes) :
    StLay K.pteU.toKLayout st T Scs Z s where
  nd := hL.nd
  tcb := hL.tcb
  sc := hL.sc
  dom := hL.dom
  dtm := hL.dtm
  domA := hL.domA
  dtmA := hL.dtmA
  user b hb := hK.none b hb
  domU := h1
  dtmU := h2

theorem vcpuNU_pteU (hK : RegionOKP K) : VcpuNU K.pteU := fun v b hv hp => hK.novcpu b hp ⟨v, hv⟩

theorem vtmU_pteU {irq : U64} {s : S} (h : VtmP K st irq s) : VtmU K.pteU st irq s :=
  ⟨h.iqP, h.krP, fun hi hhi => h.tabP hi hhi⟩

theorem vtmEnt_pteU (hK : RegionOKP K) {lk : S → U64 → Prop} {irq n : U64} {s : S}
    (hE : VtmEnt K.toKLayoutV st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hP : VtmP K st irq s) :
    VtmEnt K.pteU st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s :=
  { hE with ent := { hE.ent with lay := stLay_pteU hK hE.ent.lay hP.domP hP.dtmP } }

/-- A word of the PTE-free read set `VexitRSU (pteU K)` is an aligned word of `VexitRS K` and no PTE word. -/
theorem vexitRSU_pteU {lk : S → U64 → Prop} {s : S} {x : U64} (h : VexitRSU K.pteU st lk s x) :
    Aligned x ∧ VexitRS K.toKLayoutV st lk s x ∧ x ∉ K.ptes :=
  ⟨h.1.1, ⟨h.1.1, Or.inr (h.1.2.resolve_left h.2)⟩, h.2⟩

end lvm


/-! ## The VM-exit path (vx): hpzg's user-free walks re-run at `VexitRS ∖ ptes` -/

section vxw
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutP}

/-- `VexitRS` without the PTE words. -/
def VexitRSP (K : KLayoutP) (st : machine.Store S) [L : LawfulStore st] (lk : S → U64 → Prop) (s : S) (x : U64) :
    Prop :=
  VexitRS K.toKLayoutV st lk s x ∧ x ∉ K.ptes

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop} {v n : U64} {m : U64 → U64}

/-- **`vexit_acc_own_np` on the user-free read set.** -/
theorem vexit_acc_own_npP (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hK : RegionOKV K.toKLayoutV) (hVU : VcpuNU K.pteU) {s s' : S} {a a' : A}
    (hE : VexitEnt K.toKLayoutV st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hdom : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes)
    (hdtm : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes)
    (hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRSP K st lk s) (VexitWS K.toKLayoutV st lk s)) ar s a v n =
      ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -⟩ := vexit_split ar h
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  have hLp := stLay_pteU hKP hL hdom hdtm
  refine vexit_accG_np (gS := guard st (VexitRSP K st lk s) (VexitWS K.toKLayoutV st lk s)) (R := VexitRSP K st lk s)
    (W := VexitWS K.toKLayoutV st lk s) ar hA hI
    (fun hok w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hok.aff hok.core hw)⟩,
      vexit_rd_nu hI hLp hE.ntw hE.cs hw⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ => ⟨⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩, hdom⟩)
    (fun _ => ⟨⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩, hdtm⟩)
    ⟨⟨(hE.vfar hv0).1.1, Or.inr (pending_rd hK (hE.vin hv0) (hE.vlk hv0))⟩, hVU _ _ (hE.vin hv0)⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hLp hE.ntw hn⟩)
    (hE.vfar hv0) (fun hn => hE.nfar n hbn hn) hp0 h

/-- **`vexit_dec_own` on the user-free read set.** -/
theorem vexit_dec_ownP (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hK : RegionOKV K.toKLayoutV) (hVU : VcpuNU K.pteU) {s s' : S} {a a' : A}
    (hE : VexitEnt K.toKLayoutV st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hdom : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes)
    (hdtm : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (false, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRSP K st lk s) (IrqDec st s)) ar s a v n =
      ok (false, s', a') := by
  have hI := hE.inv
  have hL := hE.lay
  have hLp := stLay_pteU hKP hL hdom hdtm
  exact vexit_decG (gS := guard st (VexitRSP K st lk s) (IrqDec st s)) (R := VexitRSP K st lk s)
    (W := IrqDec st s) ar hA hI
    (fun w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hE.curAff hE.cscCore hw)⟩,
      vexit_rd_nu hI hLp hE.ntw hE.cs hw⟩)
    ⟨⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩, hdom⟩
    ⟨⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩, hdtm⟩
    (fun hv0 => ⟨⟨(hE.vfar hv0).1.1, Or.inr (pending_rd hK (hE.vin hv0) (hE.vlk hv0))⟩, hVU _ _ (hE.vin hv0)⟩)
    (fun n' hbn hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hLp hE.ntw hn⟩)
    (Or.inl rfl) (Or.inr rfl) h

/-- **`vexit_acc_own_p` on the user-free read set** (`vexit_accG_pW`: the IPC buffer is only written). -/
theorem vexit_acc_own_pP (hA : P0.ArchTotal ar) (hKP : RegionOKP K) (hK : RegionOKV K.toKLayoutV) (hVU : VcpuNU K.pteU) {s s' : S} {a a' : A}
    (hE : VexitEnt K.toKLayoutV st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hdom : core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes)
    (hdtm : core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes) (hP : VexitPEnt K.toKLayoutV st T Cs H Sg Scs Z m v s)
    (hpd : VPend st v s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRSP K st lk s) (VexitWS K.toKLayoutV st lk s)) ar s a v n =
      ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -, -, eok, -⟩ := vexit_split ar h
  obtain ⟨haff, -, hsct, hcore⟩ := current_vm_ok_true eok
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  have hLp := stLay_pteU hKP hL hdom hdtm
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  have ht' : TcbAddr (L.curW s) := hI.1.choose_spec.choose_spec.tcbs _ hcT
  have hin := hE.vin hv0
  have hl := hE.vlk hv0
  have hfit := hP.vfit hv0
  have hpa : Aligned (core.num.U64.wrapping_add v vcpu.PENDING) := (hP.pusr hv0).out.1
  obtain ⟨hU, hpU, hbuf⟩ := hP.rep hv0
  have gV : VW (VexitRSP K st lk s) v := fun o ho h8 =>
    ⟨⟨vcpu_al hfit hpa ho h8, Or.inr (vcpu_rd hK hin.1 hfit ho hl)⟩, vcpu_nu hVU hin.1 hfit ho⟩
  refine vexit_accG_pW (gS := guard st (VexitRSP K st lk s) (VexitWS K.toKLayoutV st lk s)) (R := VexitRSP K st lk s)
    (W := VexitWS K.toKLayoutV st lk s) (U := VPU K.toKLayoutV v) ar hA hI
    (fun hok w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hok.aff hok.core hw)⟩,
      vexit_rd_nu hI hLp hE.ntw hE.cs hw⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ => ⟨⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩, hdom⟩)
    (fun _ => ⟨⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩, hdtm⟩)
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hLp hE.ntw hn⟩)
    hU hpU hbuf
    (fun x hx => by
      change (x ∈ K.user ∧ Aligned x) ∨ x = core.num.U64.wrapping_add v vcpu.PENDING at hx
      rcases hx with ⟨hu, ha⟩ | rfl
      · exact ⟨ha, Or.inl hu⟩
      · exact ⟨hpa, Or.inr (pending_wr hK hin hl)⟩)
    ⟨⟨hpa, Or.inr (pending_rd hK hin hl)⟩, hVU _ _ hin⟩
    gV
    (fun f b e => by
      have hx := vcpu.vmcs_addr.off v f
      rw [e, WP.spec_ok] at hx
      obtain ⟨o, ho, h8, rfl⟩ := hx
      exact gV o (by omega) h8)
    (fun X _ _ => gst_write (W := VexitWS K.toKLayoutV st lk s)
      ⟨by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp),
        Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok (Or.inr (Or.inl ⟨3328#u64, by simp, by simp, by simp,
          stA_eq _⟩))))⟩)
    hpd h

/-- **`VxP`** [J] (per vx entry state): the two domain words are no PTE words (P1 `HeapOK`). -/
def VxP (K : KLayoutP) (s : S) : Prop :=
  core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN ∉ K.ptes ∧
    core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME ∉ K.ptes

end vxw

/-! ## The vt and vx slots -/

section vt
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **The VM-timer slot's path reads no PTE word**, from `VtmP` [J] at its entry states. -/
theorem vt_avoidP_path (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m)
    (hP : ∀ s, VtPre st i K.toKLayoutV s → VtmP K st i.irq s) :
    AvoidP K ((vtSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have hK' := regionOKV_pteU hK
  have hVU := vcpuNU_pteU hK
  refine avoidE_of_entry (P := (vtSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h)
    (E := (· ∈ K.ptes)) (vtimer_noZero i.irq i.pl i.n) (IsProg.on (vtimer_isProg S i.irq i.pl i.n) _ _ _)
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => VexitWS (L := L) K.pteU st i.lk s)
    (fun s x _ hx => (vexitRSU_pteU (L := L) hx).2.2) ?_
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => vexitRSU_pteU (L := L) hx)
    (fun s x hs hx => ((show VtPre st i K.toKLayoutV s from hs).ent.dec hx).1) ?_
  · intro s a r hs hr hb
    have hs' : VtPre st i K.toKLayoutV s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) := hr
    have hE' := vtmEnt_pteU hK hs' (hP s hs')
    have hTU := vtmU_pteU (hP s hs')
    have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (VexitWS K.pteU st i.lk s))
        ar s a i.irq i.pl i.n = ok (true, s1, a1) :=
      vtimer_acc_ownU ar hA hK' hVU hE' hTU (fun hq => by
        by_cases hNW : NoWake st s
        · exact vtimer_acc_fnw_ownU ar hA hK' hVU h.Nt hE' hTU hq hNW hr'
        · obtain ⟨U, hUs, hbU⟩ := h.UB s hs'
          exact vtimer_acc_fwk_ownU ar hA hK' hVU h.Nt hE' hTU h.OL h.PL hUs hbU (h.SL s hs') (h.pSg s hs') hq hNW
            hr') hr'
    exact g
  · intro s a r hs hr hb
    have hs' : VtPre st i K.toKLayoutV s := hs
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (false, s1, a1) := hr
      have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl i.n = ok (false, s1, a1) :=
        vtimer_dec_ownU ar hA hK' hVU h.Nt (vtmEnt_pteU hK hs' (hP s hs')) (vtmU_pteU (hP s hs')) hr'
      exact g
    · exact absurd rfl hb

/-- **The VM-timer path reads no PTE word** (the `vt` field of `P3AvP`). -/
theorem vt_avoidP (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m)
    (hP : ∀ s, VtPre st i K.toKLayoutV s → VtmP K st i.irq s) :
    AvoidP K ((vtSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have e := SlotN.fam_pos (fl4Dflt st ar hm) (vtSlotP3 st ar hA hm) (hK := hK.base) (hU := hU.base) h
  rw [e]
  exact vt_avoidP_path st ar hA hm i K m hK hU h hP

/-- **The VM-exit slot's path reads no PTE word**, from `VxP` [J] at its entry states. -/
theorem vx_avoidP_path (i : VxArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m)
    (hP : ∀ s, VxPre st i K.toKLayoutV m s → VxP (L := L) K s) :
    AvoidP K ((vxSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h) := by
  have hVU := vcpuNU_pteU hK
  refine avoidE_of_entry (P := (vxSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h)
    (E := (· ∈ K.ptes)) (vexit_noZero i.v i.n) (IsProg.on (vexit_isProg S i.v i.n) _ _ _)
    (fun s => VexitRSP (L := L) K st i.lk s) (fun s => VexitWS (L := L) K.toKLayoutV st i.lk s)
    (fun s x _ hx => hx.2) ?_
    (fun s => VexitRSP (L := L) K st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => ⟨hx.1.1, hx.1, hx.2⟩)
    (fun s x hs hx => ((show VxPre st i K.toKLayoutV m s from hs).1.dec hx).1) ?_
  · intro s a r hs hr hb
    have hs' : VxPre st i K.toKLayoutV m s := hs
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vcpu_exit_local st ar s a i.v i.n = ok (true, s1, a1) := hr
    have hd := hP s hs'
    have g : localvm.handle_vcpu_exit_local (guard st (VexitRSP K st i.lk s) (VexitWS K.toKLayoutV st i.lk s))
        ar s a i.v i.n = ok (true, s1, a1) := by
      by_cases hp0 : vcpu.get st s i.v vcpu.PENDING = ok 0#u64
      · exact vexit_acc_own_npP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hp0 hr'
      · exact vexit_acc_own_pP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hs'.2 hp0 hr'
    exact g
  · intro s a r hs hr hb
    have hs' : VxPre st i K.toKLayoutV m s := hs
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vcpu_exit_local st ar s a i.v i.n = ok (false, s1, a1) := hr
      have hd := hP s hs'
      have g : localvm.handle_vcpu_exit_local (guard st (VexitRSP K st i.lk s) (IrqDec st s))
          ar s a i.v i.n = ok (false, s1, a1) :=
        vexit_dec_ownP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hr'
      exact g
    · exact absurd rfl hb

/-- **The VM-exit path reads no PTE word** (the `vx` field of `P3AvP`). -/
theorem vx_avoidP (i : VxArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m)
    (hP : ∀ s, VxPre st i K.toKLayoutV m s → VxP (L := L) K s) :
    AvoidP K ((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base) := by
  have e := SlotN.fam_pos (fl4Dflt st ar hm) (vxSlotP3 st ar hA hm) (hK := hK.base) (hU := hU.base) h
  rw [e]
  exact vx_avoidP_path st ar hA hm i K m hK hU h hP

/-- **`P3AvP2` with `vt` and `vx` discharged**: `vtP` [J] (`VtmP`) and `vxP` [J] (`VxP`) at their entry states. -/
structure P3AvP3 : Prop where
  pteSl : ∀ K : KLayoutP, RegionOKP K → K.ptes ≠ ∅ → PteSl st K
  vtP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m → ∀ s, VtPre st i K.toKLayoutV s → VtmP K st i.irq s
  vmF : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmF.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vmR : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmR.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  io : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).io.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  stm : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).st.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).st.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  irq : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).irq.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).irq.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  vxP : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m → ∀ s, VxPre st i K.toKLayoutV m s → VxP (L := L) K s

theorem P3AvP3.toP2 (h : P3AvP3 st ar hA hSt hm a0) : P3AvP2 st ar hA hSt hm a0 where
  pteSl := h.pteSl
  vmF := h.vmF
  vmR := h.vmR
  io := h.io
  stm := h.stm
  irq := h.irq
  vx i K m hK hU he hp := vx_avoidP st ar hA hm i K m hK hU hp (h.vxP i K m hK hU he hp)
  vt i K m hK hU he hp := vt_avoidP st ar hA hm i K m hK hU hp (h.vtP i K m hK hU he hp)

/-- **FL4 end to end with rules 7 and 8, `K.ptes` arbitrary, syscall_local's, the VM timer's and the VM exit's PTE
premises discharged** (`serializable_fl4_localP3P2` with `P3AvP3`: `vt` / `vx` [W] replaced by `VtmP` / `VxP` [J]). -/
theorem serializable_fl4_localP3P3 (hAv : P3AvP3 st ar hA hSt hm a0) {s0 s : Cfg U64 U64 U64 U64}
    {K0 K : KLayoutP} (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3P st ar hA hSt hm a0 (P3AvP2.toP3 st ar hA hSt hm a0 (P3AvP3.toP2 st ar hA hSt hm a0 hAv)))
      s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localP3P2 st ar hA hSt hm a0 (P3AvP3.toP2 st ar hA hSt hm a0 hAv) h0 hA0 hK0 hU0 hM0 h hq

end vt

end
end Fl4Proofs.P2.E2EP
