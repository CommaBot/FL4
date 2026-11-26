/-
# P2: `ReadOnce` of the `local_vm_exit` and `local_vm_timer_irq` trees (line hpzg, gen 5)

`vexit_localPathPG` / `vtimer_localPathG` (`P2/ProgGenLvLP.lean`) left `hro` [W]: `E2E.ReadOnce` of the generated
tree with `RS = VexitRS`. Unlike `MaxR` (timer interrupt, `P2/TmOnce.lean`), `VexitRS` holds the user words
(`Aligned x ∧ (x ∈ K.user ∨ RPerm (ownV K) …)`), and a user word is racy for `Once` whatever the read set, so a run
guarded on `VexitRS` is not yet `Once`. The read set actually used is user-free:

* `VexitRSU s := VexitRS s ∧ ∉ K.user`. Every word the accepted and declined walks read is in it: `IrqRd` words lie
  in typed regions (`vexit_rd_nu`, `StLay.user`), the domain words by `StLay.domU` / `dtmU`, the bound notification's
  `TAIL_STATE` in its `.ntfn` region (`ntfn_tail_nu`), the VCPU's words (its `PENDING`, the report's `VW` and VMCS
  shadow) by `VcpuNU` [J], the IRQ state / kernel root / ASID words by `VtmU` [J]. The IPC buffer (user words) is
  only written by the report: `vexit_accG_pW` (`P2/AccessLvmPw.lean`, `vexit_accG_p` with `U` write-only).
* `once_of_guardU` (`P2/OnceU.lean`): a run on `guard st (VexitRSU s) W` is `Once` for `VexitRS s` (user writes
  only grow the touched set; no user word is read).
* As `TmOnce`: every alternative's run is the entry's guarded run (`interp_agree` on `VexitRSU s ⊆ VexitRS s`).

Results:
* `vexit_acc_own_npU` / `vexit_acc_own_pU` / `vexit_dec_ownU`: gen 6/7's `vexit_acc_own_np` / `vexit_acc_own_p` /
  `vexit_dec_own` on `VexitRSU`; `vexit_once_alt`, **`vexit_hroP`** (`hro` of `vexit_localPathPG`),
  **`vexit_localPathPG2`**: `local_vm_exit` (pending case included) with `IsProg`, `NoZero`, `ReadOnce` discharged.
  Premises: `vexit_localPathP`'s minus `hp` / `hz` / `hro`, plus **[J] `hVU : VcpuNU K`** (no VCPU word is a user
  word).
* `vtimer_acc_ownU`: `vtimer_acc_own` on `VexitRSU`, the fire case a premise on the same guard; `vtimer_once_alt`,
  **`vtimer_hro`**, **`vtimer_localPathG2`**: `local_vm_timer_irq` with `IsProg`, `NoZero`, `ReadOnce` discharged.
  Premises: `vtimer_localPath`'s minus `hp` / `hz` / `hro`, with **`hFU` [W]** (fire case, acc) and **`hDU` [W]**
  (declines) stated on `guard st (VexitRSU s) …` instead of `VexitRS s` (they imply `vtimer_localPath`'s `hF` / `hD`
  by `interp_mono`; lvm gen 9's `vtimer_decG` / `vtimer_accG_fnw` are generic in the read set, so their `VexitRSU`
  instances discharge `hDU` and the non-waking part of `hFU` the same way), plus **[J] `hVU`** and **[J] `hTU`**
  (`VtmU`: the IRQ state word, the kernel root word and the ASID table / pool words are no user words; `IrqLayR`'s
  `iqU` / `krU` / `tabU`, which P3 gives from `SlJAt`, `irqLayK_of_slJAt`).
-/
import Fl4Proofs.P2.ProgGenLvLP
import Fl4Proofs.P2.OnceU
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu VcpuGate RegionOKV UserOKV rpermV_of_own rpermV_vcpu
  wpermV_vcpu wpermV_of_own')
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}

/-- The user-free part of `VexitRS` (module docstring). -/
def VexitRSU (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (lk : S → U64 → Prop) (s : S) (x : U64) :
    Prop :=
  VexitRS K st lk s x ∧ x ∉ K.user

/-- **No VCPU word is a user word** [J] (VCPUs are kernel objects; P3 layout). -/
def VcpuNU (K : KLayoutV) : Prop := ∀ v b, InVcpu K v b → b ∉ K.user

/-- **The IRQ state word, the kernel root word and the ASID words are no user words** [J] (`IrqLayR.iqU` / `krU` /
`tabU`, from `SlJAt`). -/
structure VtmU (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (irq : U64) (s : S) : Prop where
  iqU : irq.val < 128 → ∀ i, interrupt.state_off irq = ok i → core.num.U64.wrapping_add (L.ksb s) i ∉ K.user
  krU : krA (L := L) s ∉ K.user
  tabU : ∀ hi : U64, hi.val < 2048 → atAF (L.ksb s) hi ∉ K.user ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 → peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user

/-- **No word of `IrqRd` is a user word** at a VM entry (`irq_rd_nu` with `VexitEnt`'s `ntw` / `cs`). -/
theorem vexit_rd_nu {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    {w : U64} (h : IrqRd st Z s w) : w ∉ K.user := by
  have h0 := hI.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := h0.curT
  have hcs : L.cscW s ∈ Scs := hI.2.2.1.2.2.cur
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, -, h4, h5, h6, rfl⟩ | h | ⟨hne, rfl | h⟩ | ⟨hne, hw⟩ |
      ⟨k, hk, hk32, -, rfl⟩
  · exact hL.nu_node ho
  · exact hL.nu_tcb hcT h1 h2
  · exact hL.nu_sc hcs h
  · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
    exact hL.nu_tcb r1 (by simp) (by simp)
  · obtain ⟨r1, r2, r3, r4, -⟩ := rel_facts hI hne
    exact hL.nu_sc r4 h
  · obtain ⟨q1, -⟩ := tmin_facts (BXI.blk hI) h0.cur hne
    rcases hw with ⟨k, hk, rfl⟩ | ⟨-, ⟨k, hk, rfl⟩ | ⟨hb, rfl | rfl⟩⟩
    · exact hL.nu_tcb q1 (by omega) (by omega)
    · exact hL.nu_tcb q1 (by omega) (by omega)
    all_goals
      have hNt := hI.2.2.1.2.2.bnd _ q1 hb
    · exact hL.nu (by rw [ntw _ hNt layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])]; intro e; cases e)
    · exact hL.nu (by rw [ntw _ hNt layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB])]; intro e; cases e)
  · obtain ⟨p, hr, -, -⟩ := cs k hk hk32
    exact hL.nu (by rw [hr]; intro e; cases e)

/-- The current thread's bound notification's `TAIL_STATE` is no user word (its `.ntfn` region). -/
theorem ntfn_tail_nu {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (hb : L.mem s (boundA (L.curW s)) ≠ 0#u64) :
    core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) layout.ntfn.TAIL_STATE ∉ K.user := by
  have h0 := hI.1.choose_spec.choose_spec
  have hNt := hI.2.2.1.2.2.bnd _ h0.curT hb
  have e : region K.toKLayout
      (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) layout.ntfn.TAIL_STATE) =
        .ntfn (L.mem s (boundA (L.curW s))) :=
    ntw _ hNt layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
  exact hL.nu (by rw [e]; intro e; cases e)

/-- A word `v + o` of a VCPU `v` that does not wrap is no user word (`VcpuNU`). -/
theorem vcpu_nu (hVU : VcpuNU K) {v o : U64} (hv : v ∈ K.vcpus) (hfit : v.val + 32768 ≤ 2 ^ 64)
    (ho : o.val < 32768) : core.num.U64.wrapping_add v o ∉ K.user := by
  have e := vadd_val hfit ho
  exact hVU v _ ⟨hv, by unfold InW; omega⟩

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop} {v n : U64} {m : U64 → U64}

/-- **`vexit_acc_own_np` on the user-free read set.** -/
theorem vexit_acc_own_npU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a v n =
      ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -⟩ := vexit_split ar h
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  refine vexit_accG_np (gS := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) (R := VexitRSU K st lk s)
    (W := VexitWS K st lk s) ar hA hI
    (fun hok w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hok.aff hok.core hw)⟩,
      vexit_rd_nu hI hL hE.ntw hE.cs hw⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ => ⟨⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩)
    (fun _ => ⟨⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩)
    ⟨⟨(hE.vfar hv0).1.1, Or.inr (pending_rd hK (hE.vin hv0) (hE.vlk hv0))⟩, hVU _ _ (hE.vin hv0)⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL hE.ntw hn⟩)
    (hE.vfar hv0) (fun hn => hE.nfar n hbn hn) hp0 h

/-- **`vexit_dec_own` on the user-free read set.** -/
theorem vexit_dec_ownU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (false, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRSU K st lk s) (IrqDec st s)) ar s a v n =
      ok (false, s', a') := by
  have hI := hE.inv
  have hL := hE.lay
  exact vexit_decG (gS := guard st (VexitRSU K st lk s) (IrqDec st s)) (R := VexitRSU K st lk s)
    (W := IrqDec st s) ar hA hI
    (fun w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hE.curAff hE.cscCore hw)⟩,
      vexit_rd_nu hI hL hE.ntw hE.cs hw⟩)
    ⟨⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩
    ⟨⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩
    (fun hv0 => ⟨⟨(hE.vfar hv0).1.1, Or.inr (pending_rd hK (hE.vin hv0) (hE.vlk hv0))⟩, hVU _ _ (hE.vin hv0)⟩)
    (fun n' hbn hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL hE.ntw hn⟩)
    (Or.inl rfl) (Or.inr rfl) h

/-- **`vexit_acc_own_p` on the user-free read set** (`vexit_accG_pW`: the IPC buffer is only written). -/
theorem vexit_acc_own_pU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s) (hP : VexitPEnt K st T Cs H Sg Scs Z m v s)
    (hpd : VPend st v s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a v n =
      ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -, -, eok, -⟩ := vexit_split ar h
  obtain ⟨haff, -, hsct, hcore⟩ := current_vm_ok_true eok
  have hok : IrqOk st s := ⟨haff, hsct, hcore⟩
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  have ht' : TcbAddr (L.curW s) := hI.1.choose_spec.choose_spec.tcbs _ hcT
  have hin := hE.vin hv0
  have hl := hE.vlk hv0
  have hfit := hP.vfit hv0
  have hpa : Aligned (core.num.U64.wrapping_add v vcpu.PENDING) := (hP.pusr hv0).out.1
  obtain ⟨hU, hpU, hbuf⟩ := hP.rep hv0
  have gV : VW (VexitRSU K st lk s) v := fun o ho h8 =>
    ⟨⟨vcpu_al hfit hpa ho h8, Or.inr (vcpu_rd hK hin.1 hfit ho hl)⟩, vcpu_nu hVU hin.1 hfit ho⟩
  refine vexit_accG_pW (gS := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) (R := VexitRSU K st lk s)
    (W := VexitWS K st lk s) (U := VPU K v) ar hA hI
    (fun hok w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hok.aff hok.core hw)⟩,
      vexit_rd_nu hI hL hE.ntw hE.cs hw⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ => ⟨⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩)
    (fun _ => ⟨⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩)
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL hE.ntw hn⟩)
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
    (fun X _ _ => gst_write (W := VexitWS K st lk s)
      ⟨by rw [stA_eq]; exact field_aligned ht' (by simp) (by simp),
        Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok (Or.inr (Or.inl ⟨3328#u64, by simp, by simp, by simp,
          stA_eq _⟩))))⟩)
    hpd h

variable {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64}

/-- **An alternative's run of the VM-exit tree is `Once`** (module docstring). -/
theorem vexit_once_alt (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hm : E2E.MasksWr st)
    {s s' : S} {a : A} (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hX : VexitPEnt K st T Cs H Sg Scs Z m v s)
    (hAlt : Alt st (VexitRS K st lk s) cls ko (· ∈ K.user) s s') :
    Once st ar (VexitRS K st lk s) (· ∈ K.user) ∅ ∅ (R.localvm.handle_vcpu_exit_local v n) s' a := by
  have hz := vexit_noZero v n
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vcpu_exit_local mm ar x a v n = interp mm ar (R.localvm.handle_vcpu_exit_local v n) x a :=
    fun mm x => congrFun (congrFun (vexit_isProg S v n A ar mm) x) a
  have hR1 : ∀ w, VexitRSU K st lk s w → Aligned w := fun _ hw => hw.1.1
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localvm.handle_vcpu_exit_local (guard st (VexitRSU K st lk s) W') ar s a v n = ok (x, s1, a1) →
      Once st ar (VexitRS K st lk s) (· ∈ K.user) ∅ ∅ (R.localvm.handle_vcpu_exit_local v n) s' a := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa _ hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks
      (fun w hw => hAlt.read w hw.1) hg
    exact once_of_guardU (User := (· ∈ K.user)) (fun q hq => ⟨hq.1, hq.2⟩) _ hz ∅ ∅ s' a _ hg'
  obtain ⟨r, hr⟩ : ∃ r, localvm.handle_vcpu_exit_local st ar s a v n = ok r := by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localvm.handle_vcpu_exit_local.p0 st ar s a v n LawfulStore.total hA)
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  · exact tr (W' := IrqDec st s) (fun _ hw => (hE.dec hw).1) (vexit_dec_ownU ar hA hK hVU hE hr)
  · by_cases hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64
    · exact tr (W' := VexitWS K st lk s) (fun _ hw => hw.1) (vexit_acc_own_npU ar hA hK hVU hE hp0 hr)
    · exact tr (W' := VexitWS K st lk s) (fun _ hw => hw.1) (vexit_acc_own_pU ar hA hK hVU hE hX hp0 hr)

/-- **`hro` of `vexit_localPathPG` holds** (module docstring). -/
theorem vexit_hroP (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hm : E2E.MasksWr st) :
    ReadOnce st ar (R.localvm.handle_vcpu_exit_local v n) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user) (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ VexitPEnt K st T Cs H Sg Scs Z m v s)
      (VexitRS K st lk) :=
  fun _ _ _ _ hE hAlt _ => vexit_once_alt ar hA hK hVU hm hE.1 hE.2 hAlt

/-- **`local_vm_exit` with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring): `vexit_localPathPG`
with `hro := vexit_hroP`. Premises: `hA`, `hK` [J], `hU` [J], `hm` [P], **`hVU` [J]**, `hEU` [J], `hlk` [P], and
`VexitEnt` / `VexitPEnt`'s fields. -/
noncomputable def vexit_localPathPG2 (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st) (hVU : VcpuNU K)
    (hEU : ∀ s b v', VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ VexitPEnt K st T Cs H Sg Scs Z m v s →
      b ∈ K.user → Aligned b →
      VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n (L.wr s b v') ∧
        VexitPEnt K st T Cs H Sg Scs Z m v (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  vexit_localPathPG ar hA hK hU hm (vexit_hroP ar hA hK hVU hm) hEU hlk

/-! ## `local_vm_timer_irq` -/

variable {irq : U64} {pl : localtimer.TimerIrqPlan}

/-- **`vtimer_acc_own` on the user-free read set**, the fire case a premise on the same guard. -/
theorem vtimer_acc_ownU (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) {s s' : S} {a a' : A}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hTU : VtmU K st irq s)
    (hF : IrqFire st ar s a → localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s))
      ar s a irq pl n = ok (true, s', a'))
    (h : localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s', a')) :
    localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
      ok (true, s', a') := by
  have hb := vtimer_irq_lt ar h
  obtain ⟨hvb, hv0, hbn⟩ := vtimer_bnd ar h
  have E := hE.ent
  have hI := E.inv
  have hL := E.lay
  exact vtimer_accG (gS := guard st (VexitRSU K st lk s) (VexitWS K st lk s)) (R := VexitRSU K st lk s)
    (W := VexitWS K st lk s) ar hA hI
    (fun hok w ha hw => ⟨⟨ha, Or.inr (vexit_rd hK hI hL E.ntw E.cs E.aff hok.aff hok.core hw)⟩,
      vexit_rd_nu hI hL E.ntw E.cs hw⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ i hi => ⟨⟨(hE.iq hb i hi).1,
      Or.inr (rpermV_of_own (hE.iq hb i hi).2.2 (rperm_none (hE.iq hb i hi).2.1 _))⟩, hTU.iqU hb i hi⟩)
    (fun _ => ⟨⟨hL.domA, Or.inr (rpermV_of_own E.ksv.1 (rperm_none hL.dom _))⟩, hL.domU⟩)
    (fun _ => ⟨⟨hL.dtmA, Or.inr (rpermV_of_own E.ksv.2 (rperm_none hL.dtm _))⟩, hL.dtmU⟩)
    (fun _ => ⟨⟨hE.kr.1, Or.inr (rpermV_of_own hE.kr.2.2 (rperm_none hE.kr.2.1 _))⟩, hTU.krU⟩)
    (fun _ hi hhi => ⟨⟨⟨(hE.tab hi hhi).1.1,
        Or.inr (rpermV_of_own (hE.tab hi hhi).1.2.2 (rperm_none (hE.tab hi hhi).1.2.1 _))⟩, (hTU.tabU hi hhi).1⟩,
      fun lo hlo hne => ⟨⟨((hE.tab hi hhi).2 lo hlo hne).1,
        Or.inr (rpermV_of_own ((hE.tab hi hhi).2 lo hlo hne).2.2 (rperm_none ((hE.tab hi hhi).2 lo hlo hne).2.1 _))⟩,
        (hTU.tabU hi hhi).2 lo hlo hne⟩⟩)
    hE.asid hvb
    ⟨⟨(E.vfar hv0).1.1, Or.inr (pending_rd hK (E.vin hv0) (E.vlk hv0))⟩, hVU _ _ (E.vin hv0)⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL E.ntw E.curAff hn
      exact ⟨⟨q1, Or.inr q2⟩, ntfn_tail_nu hI hL E.ntw hn⟩)
    (E.vfar hv0) (fun hn => E.nfar n hbn hn) hF h

/-- **An alternative's run of the VM-timer tree is `Once`** (module docstring); fire case `hF` and declines `hD` on
the user-free guard. -/
theorem vtimer_once_alt (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hm : E2E.MasksWr st)
    {s s' : S} {a : A} (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s) (hTU : VtmU K st irq s)
    (hF : ∀ s1 a1, IrqFire st ar s a → localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hD : ∀ s1 a1, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1))
    (hAlt : Alt st (VexitRS K st lk s) cls ko (· ∈ K.user) s s') :
    Once st ar (VexitRS K st lk s) (· ∈ K.user) ∅ ∅ (R.localvm.handle_vm_timer_irq_local irq pl n) s' a := by
  have hz := vtimer_noZero irq pl n
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n =
        interp mm ar (R.localvm.handle_vm_timer_irq_local irq pl n) x a :=
    fun mm x => congrFun (congrFun (vtimer_isProg S irq pl n A ar mm) x) a
  have hR1 : ∀ w, VexitRSU K st lk s w → Aligned w := fun _ hw => hw.1.1
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) W') ar s a irq pl n = ok (x, s1, a1) →
      Once st ar (VexitRS K st lk s) (· ∈ K.user) ∅ ∅ (R.localvm.handle_vm_timer_irq_local irq pl n) s' a := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa _ hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks
      (fun w hw => hAlt.read w hw.1) hg
    exact once_of_guardU (User := (· ∈ K.user)) (fun q hq => ⟨hq.1, hq.2⟩) _ hz ∅ ∅ s' a _ hg'
  obtain ⟨r, hr⟩ : ∃ r, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok r := by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq pl n LawfulStore.total hA)
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  · exact tr (W' := IrqDec st s) (fun _ hw => (hE.ent.dec hw).1) (hD s1 a1 hr)
  · exact tr (W' := VexitWS K st lk s) (fun _ hw => hw.1)
      (vtimer_acc_ownU ar hA hK hVU hE hTU (fun hf => hF s1 a1 hf hr) hr)

/-- **`hro` of `vtimer_localPathG` holds** (module docstring), given `hTU` [J], `hVU` [J] and the user-free fire /
decline guards. -/
theorem vtimer_hro (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hVU : VcpuNU K) (hm : E2E.MasksWr st)
    (hTU : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → VtmU K st irq s)
    (hFU : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hDU : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1)) :
    ReadOnce st ar (R.localvm.handle_vm_timer_irq_local irq pl n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user) (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n) (VexitRS K st lk) :=
  fun s _ a _ hE hAlt _ => vtimer_once_alt ar hA hK hVU hm hE (hTU s hE) (fun s1 a1 => hFU s a s1 a1 hE)
    (fun s1 a1 => hDU s a s1 a1 hE) hAlt

/-- **`local_vm_timer_irq` with `IsProg`, `NoZero` and `ReadOnce` discharged** (module docstring):
`vtimer_localPathG` with `hro := vtimer_hro`, its `hF` / `hD` from the user-free `hFU` / `hDU` (`interp_mono`).
Premises: `hA`, `hK` [J], `hU` [J], `hm` [P], **`hVU` [J]**, **`hTU` [J]**, `hEU` [J], `hlk` [P], **`hFU` [W]**,
`hFm` [W], **`hDU` [W]**, and `VtmEnt`'s fields. -/
noncomputable def vtimer_localPathG2 (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st) (hVU : VcpuNU K)
    (hTU : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → VtmU K st irq s)
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s)
    (hFU : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s1, a1))
    (hDU : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRSU K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1)) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  have hz := vtimer_noZero irq pl n
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n =
        interp mm ar (R.localvm.handle_vm_timer_irq_local irq pl n) x a :=
    fun mm x a => congrFun (congrFun (vtimer_isProg S irq pl n A ar mm) x) a
  vtimer_localPathG ar hA hK hU hm (vtimer_hro ar hA hK hVU hm hTU hFU hDU) hEU hlk
    (fun s a s1 a1 hE hf h => by
      have g := hFU s a s1 a1 hE hf h
      rw [eP] at g ⊢
      exact interp_mono (fun _ hw => hw.1) (fun _ hw => hw) _ hz s a _ g)
    hFm
    (fun s a s1 a1 hE h => by
      have g := hDU s a s1 a1 hE h
      rw [eP] at g ⊢
      exact interp_mono (fun _ hw => hw.1) (fun _ hw => hw) _ hz s a _ g)

end

end Fl4Proofs.P2
