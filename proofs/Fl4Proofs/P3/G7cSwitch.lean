/-
P3 (DESIGN.md §9), scheduler, g7c (KENTRY-PLAN g7c): **the CR3 after a
thread switch**: `switch_to_thread`, `switch_to_idle_thread`,
`choose_thread` give `AR` at the spec outcome's CR3.

* `RootOK AR T P s a σ`: the facts at a switch state that relate FL4's
  address-space root to the spec's (`AR` at some CR3; `VsRel`, `KRootRel`;
  every TCB of `T` a spec TCB whose vtable is FL4's slot-1 cap, a mapped
  PML4 cap with a non-zero ASID; the idle TCB's vtable no mapped PML4 cap,
  `IdleVt` [J]).
* `switch_to_thread_ar` / `switch_to_idle_thread_ar`: every outcome of the
  spec switch has the CR3 FL4's arch state is `AR`-related to
  (G7cRoot's `set_vm_root_ar` / `set_kernel_vm_root_ar` and
  `switchToThread_cr3` / `switchToIdleThread_cr3`), given that FL4's switch
  terminates.
* `choose_thread_refinesFA`: ScArchF's `choose_thread_refinesF` with
  `AR r.2 σ'.cr3` added to the post.
-/
import Fl4Proofs.P3.G7cRoot
import Fl4Proofs.P3.ScScheduleF
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.Sched
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Vs

noncomputable section

section
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A} [L : LawfulStore st]
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- **The root facts at a switch state** (module docstring). -/
structure RootOK (AR : A → Fl4Spec.Cr3 → Prop) (T P : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit) : Prop where
  ar : ∃ c0, AR a c0
  vs : VsRel P (L.mem s) (L.ksb s) σ
  kr : KRootRel (L.mem s) (L.ksb s) σ
  vt : ∀ t ∈ T, ∃ (x : Fl4Spec.Tcb) (cp : capability.Cap), σ.kheap t.bv = some (.tcb x) ∧
    capAt (L.mem s) (slotOf t 1) = ok cp ∧ x.tcbVtable = absCap cp ∧ ∀ p asid, cp = .Pml4 p true asid → asid ≠ 0#u64
  /-- [J] `IdleVt`: the idle TCB's vtable is no mapped PML4 cap (FL4 switches
  to the kernel root for the idle thread, the spec to the idle TCB's vtable). -/
  idle : ∃ x : Fl4Spec.Tcb, σ.kheap σ.idleThread = some (.tcb x) ∧
    ∀ p asid, x.tcbVtable ≠ .archObjectCap (.pml4Cap p (some asid))

theorem switch_to_thread_ar (hRef : ArchRefines ar AR) {T P : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hO : RootOK (L := L) AR T P s a σ) {t : U64} (ht : t ∈ T)
    (hfin : sched.switch_to_thread st ar s a t ⦃ _ => True ⦄) :
    sched.switch_to_thread st ar s a t ⦃ r => ∀ σ', Fl4Spec.switchToThread (Z := Unit) t.bv σ = ({((), σ')}, False) →
      AR r.2 σ'.archState.x64CurrentCr3 ⦄ := by
  obtain ⟨c0, hA⟩ := hO.ar
  obtain ⟨x, cp, hkx, hc, hv, hasid⟩ := hO.vt t ht
  refine WP.spec_mono (P1.spec_eq' hfin) ?_
  rintro r ⟨hr, -⟩
  unfold sched.switch_to_thread at hr
  obtain ⟨⟨s1, a1⟩, h1, hr⟩ := bind_ok_inv hr
  obtain ⟨s2, -, hr⟩ := bind_ok_inv hr
  obtain ⟨s3, -, hr⟩ := bind_ok_inv hr
  obtain rfl : (s3, a1) = r := by simpa using hr
  obtain ⟨-, c, hcl, hAc⟩ := spec_ok_post (set_vm_root_ar hRef s a σ hA hO.vs hO.kr hkx hc hv hasid) h1
  intro σ' hσ'
  rw [switchToThread_cr3 (hcl σ rfl rfl rfl) hσ']
  exact hAc

theorem switch_to_idle_thread_ar (hRef : ArchRefines ar AR) {T P : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hO : RootOK (L := L) AR T P s a σ)
    (hfin : sched.switch_to_idle_thread st ar s a ⦃ _ => True ⦄) :
    sched.switch_to_idle_thread st ar s a ⦃ r => ∀ σ', Fl4Spec.switchToIdleThread (Z := Unit) σ = ({((), σ')}, False) →
      AR r.2 σ'.archState.x64CurrentCr3 ⦄ := by
  obtain ⟨c0, hA⟩ := hO.ar
  obtain ⟨x, hkx, hvt⟩ := hO.idle
  refine WP.spec_mono (P1.spec_eq' hfin) ?_
  rintro r ⟨hr, -⟩
  unfold sched.switch_to_idle_thread at hr
  obtain ⟨it, -, hr⟩ := bind_ok_inv hr
  obtain ⟨⟨s1, a1⟩, h1, hr⟩ := bind_ok_inv hr
  obtain ⟨s2, -, hr⟩ := bind_ok_inv hr
  obtain rfl : (s2, a1) = r := by simpa using hr
  obtain ⟨-, hAc⟩ := spec_ok_post (set_kernel_vm_root_ar hRef s a σ hO.kr hA) h1
  intro σ' hσ'
  rw [switchToIdleThread_cr3 (setVmRoot_other hkx hvt) hσ']
  exact hAc

set_option maxHeartbeats 2000000 in
/-- **`choose_thread_refinesF` with the CR3** (module docstring). -/
theorem choose_thread_refinesFA (hRef : ArchRefines ar AR) {N T C P : Set U64} {c : U64} (s : S) (a : A)
    (σ : Fl4Spec.State Unit) (hO : RootOK (L := L) AR T P s a σ)
    (hS : SchedRel st N T C c s σ) (hR : NtfnStateRel N T (L.mem s) σ) (hN : NSC N C σ) (hI : Inv σ)
    (hvm : ∀ t ∈ T, vspace.set_vm_root st ar s a t ⦃ r => ∃ σ1, Fl4Spec.archSwitchToThread (Z := Unit) t.bv σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeepsF σ σ1 ⦄)
    (hvmi : vspace.set_kernel_vm_root st ar s a ⦃ r => ∃ σ1, Fl4Spec.archSwitchToIdleThread (Z := Unit) σ =
      ({((), σ1)}, False) ∧ SchedRel st N T C c r.1 σ1 ∧ NtfnStateRel N T (L.mem r.1) σ1 ∧ ArchKeeps σ σ1 ⦄)
    (hidleT : (nodeW st s c layout.node.IDLE_THREAD).bv = σ.idleThread) :
    sched.choose_thread st ar s a ⦃ r => ∃ σ', Fl4Spec.chooseThread (Z := Unit) σ = ({((), σ')}, False) ∧
      SchedRel st N T C c r.1 σ' ∧ NtfnStateRel N T (L.mem r.1) σ' ∧ NSC N C σ' ∧ Inv σ' ∧
      (σ'.curThread = σ.idleThread ∨ Fl4Spec.schedulable σ'.curThread σ = true) ∧
      σ'.curSc = σ.curSc ∧ σ'.releaseQueue = σ.releaseQueue ∧ HeapEqUpToFpu σ σ' ∧
      σ'.schedulerAction = σ.schedulerAction ∧ TK σ σ' ∧ WritesIn st s r.1 (SFoot st T c s) ∧
      AR r.2 σ'.archState.x64CurrentCr3 ⦄ := by
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  unfold sched.choose_thread
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok]
  step with LawfulStore.cur_cpu_spec as ⟨cpu, hcpu⟩
  rw [hc.cur] at hcpu
  subst cpu
  unfold sched.bitmap_dom sched.l1_off
  rw [num_domains_eq, if_neg (by decide)]
  simp only [bind_ok, lift]
  step with obj.node_get.spec as ⟨l1, hl1⟩
  have hl1' : l1 = L.l1W s c := by
    rw [hl1]; unfold LawfulStore.l1W; congr 2
    unfold layout.node.L1_BITMAP l1Off w64; rfl
  subst hl1'
  split
  · rename_i hne0
    have hne : L.l1W s c ≠ 0#u64 := by simpa using hne0
    refine choose_pick_k s σ hS hne _ _ ?_
    rintro t ⟨ht, hteq, p, hmem⟩
    have hsw := switch_to_thread_refinesF s a σ hS hR hN ht (hvm t ht)
    refine WP.spec_mono (WP.spec_and hsw (switch_to_thread_ar hRef hO ht (WP.spec_mono hsw fun _ _ => trivial))) ?_
    rintro r ⟨⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hAR⟩
    obtain ⟨hsch, x, scp, hk, hsc, hdom⟩ := ready_sched hS hI hmem
    refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inr (by rw [h6]; exact hsch), h7, h8, h9, h10, h11, h12, hAR σ' h1⟩
    unfold Fl4Spec.chooseThread
    rw [nd_gets_bind, nd_gets_bind, if_neg (by rw [← choose_empty hS]; exact hne), ← hteq,
      guardedSwitchTo_eq hk hsc hsch hdom]
    exact h1
  · rename_i hne0
    have he : L.l1W s c = 0#u64 := by apply UScalar.eq_of_val_eq; simpa using hne0
    have hsw := switch_to_idle_thread_refines s a σ hS hR hN hidleT hvmi
    refine WP.spec_mono (WP.spec_and hsw (switch_to_idle_thread_ar hRef hO (WP.spec_mono hsw fun _ _ => trivial))) ?_
    rintro r ⟨⟨σ', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩, hAR⟩
    refine ⟨σ', ?_, h2, h3, h4, h5 hI, Or.inl h6, h7, h8, HeapEqUpToFpu.of_eq h9, h10, h11, h12, hAR σ' h1⟩
    unfold Fl4Spec.chooseThread
    rw [nd_gets_bind, nd_gets_bind, if_pos ((choose_empty hS).1 he)]
    exact h1

end

end

end Fl4Proofs.P3.Sched
