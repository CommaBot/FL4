/-
P3 (line mmuAD, gen 31): **the scheduler family's yield steps at `JAtZV3`**: `set_consumed` and
`complete_yield_to` from a VM-epoch state (gen 30's "Next" item 2).

* Copies over `JAtZB` (generator `scratch/mmu24_jatzb_gen.py setConsumedJ completeYieldJ`; the other 33
  dependencies are already in P3/JAtZBWr / JAtZBSched / JAtZBYield): `finW_keeps`, `finW_scOut`, `deadP_qk`,
  `finW_irq`, `kern_keep`, `tdkeep_of`, `finW_utc`, `cs_frameB`, `vkeep_of`, `cs_frameI`, `reg_frameF`,
  `reg_frame`, `setConsumedJ`, `completeYieldJD`, `completeYieldJ`. Proofs verbatim, except: every post ends in
  `JAtZB`; `cs_frameB` loses its `hext : JExt` argument and `cs_frameI` its `J.ext` entry (`JAtZB` has no `ext`
  field; `JAtZB.cs_frameV` takes none); `kern_keep`'s `unfold nodeW` is qualified `Sched.nodeW` (gen-24 trap).
* **`JAtZB.reg_frameFZ`**, **`JAtZB.setConsumedJV`**: `reg_frameF` / `setConsumedJ` with the post at `Z` itself
  (the existential VSpace sets of the originals are always `Z.vs`), plus the `FinW` footprint and the spec step's
  `QKY` shape (both already `have`s in the proofs).
* **`zv_qky`**: a `QKY` spec step (SC consumed/yield fields, TCB registers/yield/fault) keeps every arch object,
  every object's size, makes no new `runningVM` thread and no new or changed VCPU object — `JAtZV3.ofBS`'s
  `hvk`/`hsz`/`hrv`/`hnv`. **`JAtZB.finW_nh`**: a `FinW` word is not the VCPU-list head word.
* **`JAtZV3.setConsumedJ`**, **`JAtZV3.completeYieldJ`**: `set_consumed p y true` and `complete_yield_to y` at
  `JAtZV3 V X` for any `V`, premises exactly `JAtZ.setConsumedJ`'s / `JAtZ.completeYieldJ`'s (the latter through
  `JAtZV3.setConsumedJ` and gen 30's `JAtZV3.cancelYieldJ`).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

/-- **What a `QKY` spec step keeps of the VM epoch** (module docstring). -/
theorem zv_qky {σ σ' : Fl4Spec.State Unit} (h : Sched.QKY σ σ') :
    (∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = σ.kheap p) ∧
    (∀ o ko', σ'.kheap o = some ko' → ∃ ko, σ.kheap o = some ko ∧ Fl4Spec.objBits ko' = Fl4Spec.objBits ko) ∧
    (∀ o x', σ'.kheap o = some (.tcb x') → x'.tcbState = .runningVM →
      ∃ x, σ.kheap o = some (.tcb x) ∧ x.tcbState = .runningVM) ∧
    (∀ p (vs : Fl4Spec.VcpuState), σ'.kheap p = some (.archObj (.vcpu vs)) →
      σ.kheap p = some (.archObj (.vcpu vs))) := by
  refine ⟨fun p ao hp => ?_, fun o ko' ho => ?_, fun o x' ho hx => ?_, fun p vs hp => ?_⟩
  · rcases h.kh p with k | ⟨x, y, h1, -⟩ | ⟨z, w, n, h1, -⟩
    · exact k
    · rw [hp] at h1; cases h1
    · rw [hp] at h1; cases h1
  · rcases h.kh o with k | ⟨x, y, h1, h2, -⟩ | ⟨z, w, n, h1, h2, -⟩
    · exact ⟨ko', by rw [← k]; exact ho, rfl⟩
    · rw [ho] at h2; cases h2
      exact ⟨_, h1, rfl⟩
    · rw [ho] at h2; cases h2
      exact ⟨_, h1, rfl⟩
  · rcases h.kh o with k | ⟨x, y, h1, h2, h3⟩ | ⟨z, w, n, h1, h2, -⟩
    · exact ⟨x', by rw [← k]; exact ho, hx⟩
    · have e : (some (Fl4Spec.KernelObject.tcb x') : Option Fl4Spec.KernelObject) = some (.tcb y) :=
        ho.symm.trans h2
      simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at e
      subst e
      refine ⟨x, h1, ?_⟩
      rw [← hx, h3]
    · rw [ho] at h2; cases h2
  · rcases h.kh p with k | ⟨x, y, h1, h2, -⟩ | ⟨z, w, n, h1, h2, -⟩
    · rw [← k]; exact hp
    · rw [hp] at h2; cases h2
    · rw [hp] at h2; cases h2

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

-- from Fl4Proofs/P3/XTopJointFinW.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **The frame words a finalisation keeps**: the TCBs' `MCP`, `YIELD_TO` and
IPC-buffer words, the SCs' `REPLY` words, the replies' links. -/
theorem JAtZB.finW_keeps {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) :
    (∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (yieldA t) = L.mem s (yieldA t)) ∧
    (∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t)) ∧
    (∀ q ∈ Z.C, L.mem s' (scReplyA q) = L.mem s (scReplyA q)) ∧
    (∀ r ∈ Z.R, L.mem s' (rPrevA r) = L.mem s (rPrevA r) ∧ L.mem s' (rNextA r) = L.mem s (rNextA r)) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have tsw : ∀ b, Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ b → TSW Z.T Z.C b := fun b hb => Ipc.FinW.tsw hS hb
  refine ⟨fun t ht => ⟨hw.mem_eq (mcpA_aligned hT ht) fun hb => ((tsw _ hb).1 t ht).1 (mcpA_val hT ht),
      hw.mem_eq (flagsA_aligned hT ht) fun hb => Ipc.FinW.nf hS hb t ht rfl⟩,
    fun t ht => hw.mem_eq (yieldA_aligned hT ht) fun hb => ((tsw _ hb).1 t ht).2.1 (yieldA_val hT ht),
    fun t ht => hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => ((tsw _ hb).1 t ht).2.2 (tIpcBufA_val (hT t ht)),
    fun q hq => hw.mem_eq (sc_reply_word hS hq).1 fun hb => (tsw _ hb).2 q hq rfl, fun r hr => ?_⟩
  have hal := J.rp.align r hr
  have h8 := rPrevA_val hal
  have h16 := rNextA_val hal
  have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
    hw.mem_eq (J.rp.aligned hr ha) fun hb => by
      rcases hb with hb | ⟨y, hy, K, -, hK, -, -, -, e⟩
      · exact hb.ne_rword hS J.rp hr ha rfl
      · have := J.rp.tcb r hr y hy; omega
  exact ⟨k _ (Or.inl h8), k _ (Or.inr h16)⟩

end

-- from Fl4Proofs/P3/XTopJointFinW.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **The header words of `H`'s SCs outside `Z.C` are kept** by a
finalisation (`sc_out_keep`'s argument). -/
theorem JAtZB.finW_scOut {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) {q : U64} {z : Nat}
    (hq : H q = some (.sc z)) (hqC : q ∉ Z.C) {K : U64} (hK8 : K.val % 8 = 0) (hK : K.val < 128) :
    L.mem s' (scW q K) = L.mem s (scW q K) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R, hc, -⟩ := hS.lists
  have hH := J.kern.heap
  have hal := hH.align q _ hq
  have hfit := hH.fits q _ hq
  have hz := hH.scmin q z hq
  simp only [P1.HKind.bits] at hal hfit
  have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
  have hq8 : q.val % 8 = 0 := by
    have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
    rw [← Nat.mod_mod_of_dvd q.val hd, hal]
  have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  refine hw.mem_eq (by show (scW q K).val % 8 = 0; rw [hv]; omega) fun hb => ?_
  rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    have hne : q ≠ y := fun e => by rw [e, hHy] at hq; cases hq
    have := hH.disj q _ y _ hq hHy hne
    simp only [P1.HKind.bits] at this
    omega
  · have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
    have := J.kern.hnd q _ hq Z.c hcC
    simp only [P1.HKind.bits] at this
    omega
  · have hHn : H n = some .ntfn := J.zH.2.2.2 n hn
    have hne : q ≠ n := fun e => by rw [e, hHn] at hq; cases hq
    have := hH.disj q _ n _ hq hHn hne
    simp only [P1.HKind.bits] at this
    omega
  · have hHs := (hJ.sc sc x n (J.c0 sc hsc) hk).2
    have hne : q ≠ sc := fun e => hqC (e ▸ hsc)
    have := hH.disj q _ sc _ hq hHs hne
    simp only [P1.HKind.bits] at this
    omega

end

-- from Fl4Proofs/P3/XTopJointRegFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **The dead stay dead across a quiet step** (`deadP_keep`). -/
theorem JAtZB.deadP_qk (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s3 : S} {σ3 : Fl4Spec.State Unit}
    (hA : QKY σ σ3) (hS3 : SchedRel st Z.N Z.T Z.C Z.c s3 σ3)
    (hI3 : IpcRel Z.N Z.T Z.E Z.R Z.B (L.mem s3) σ3)
    (hw : P1.WritesIn st s s3 (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (k3 : ∀ q ∈ Z.C, L.mem s3 (P1.scReplyA q) = L.mem s (P1.scReplyA q)) (hAS : ActSched σ3)
    (hY3 : YieldRel Z.T Z.C (L.mem s3) σ3) (hYK : YKeep σ σ3) :
    ∀ q ∈ D, DeadP (L := L) H s3 q := fun q hq => by
  have hd := J.jcov.dead q hq
  refine J.deadP_keep hS3 hI3 (fun x hx _ => ?_)
    (fun x hx => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ?_) (fun hqC => k3 q hqC)
    (fun z hz hqC K hK8 hK => J.finW_scOut hw hz hqC hK8 hK) hA.idle hAS hY3 (hYK.dk q.bv) hd
  · obtain ⟨y, hy, e⟩ := hA.tcb hx
    exact ⟨y, hy, by rw [e], by rw [e], Or.inl (by rw [e])⟩
  · obtain ⟨w, hw, e⟩ := hA.sc hx
    exact ⟨w, hw, Or.inl (by rw [e]), Or.inl (by rw [e])⟩

end

-- from Fl4Proofs/P3/XTopJointFinW.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **The IRQ node's caps are kept** by a finalisation (its words lie in the
kernel-state block; the TCBs, notifications and SCs outside it, the node
after it). -/
theorem JAtZB.finW_irq {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ)) (i : U64) (hi : i.val < 128) :
    capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := J.kern.ksbFit
  refine irqNode_keep hw hkf J.kern.ksbAl (fun b hb => ?_) i hi
  rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
  · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
  · simp only [P1.LawfulStore.nodeBase] at g1; omega
  · have := J.nk n hn; omega
  · have := (hS.scOut sc hsc x n hk b ⟨g1, g2⟩).2.2.2; omega

end

-- from Fl4Proofs/P3/DeadKeep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JKern` across a step** keeping the kernel-state base, the core, the
current thread and SC, the original bits (new ones only at `AbsSlot`s), the
global PML4 and the arch
objects (ScJointRest's `sc_kern` for any write set). -/
theorem JAtZB.kern_keep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {D' : Set U64}
    (hks : L.ksb s' = L.ksb s) (hcpu : L.cpu s' = L.cpu s)
    (hS' : Sched.SchedRel st Z.N Z.T Z.C Z.c s' σ')
    (hct : σ'.curThread = σ.curThread) (hcsc : σ'.curSc = σ.curSc)
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true ∨ AbsSlot Z.th sl)
    (hgp : (σ'.archState.x64GlobalPml4, σ'.archState.x64Plat) = (σ.archState.x64GlobalPml4, σ.archState.x64Plat))
    (hao : ∀ p ao, σ.kheap p = some (.archObj ao) → σ'.kheap p = some (.archObj ao))
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    JKern (L := L) arI H Cs D' Z.th s' σ' := by
  have hpl : σ'.archState.x64Plat = σ.archState.x64Plat := congrArg Prod.snd hgp
  replace hgp : σ'.archState.x64GlobalPml4 = σ.archState.x64GlobalPml4 := congrArg Prod.fst hgp
  have K := J.kern
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  obtain ⟨Q', R', hc', hs'⟩ := hS'.lists
  have ecw : L.curW s' = L.curW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curThread; have h2 := hs.curThread
    unfold P1.LawfulStore.curW
    rw [hcpu, hna, hc.cur]
    unfold Sched.nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hct]
  have ecs : L.cscW s' = L.cscW s := by
    apply P1.eq_of_bv
    have h1 := hs'.curSc; have h2 := hs.curSc
    unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
    rw [hcpu, hna, hc.cur]
    unfold Sched.nodeW at h1 h2
    rw [hna] at h1
    rw [← h1, ← h2, hcsc]
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hks]
  obtain ⟨pt, hpt⟩ := K.gpm
  refine ⟨fun sl h => (horig sl h).elim (K.orig sl) id, by rw [ecw, hct]; exact K.cur,
    by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
    by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
    ⟨pt, by rw [hgp]; exact hao _ _ hpt⟩, by rw [hgp]; exact K.ga, by rw [hgp]; exact K.gf,
    K.heap, K.h0, by rw [hks]; exact K.hks, by rw [hks]; exact K.hksIn, fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
    by rw [hks]; exact K.ksbFit, by rw [hks]; exact K.ksbAl, by rw [hks, hcpu]; exact K.nodeFit,
    by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
    K.csLt, K.cs0, K.csN, K.tdx.frame hpl⟩
  rw [hna, hDbg]; exact K.head

end

-- from Fl4Proofs/P3/JointAt.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`TdKeep` from a `WritesIn` footprint missing every TCB's deadline word.** -/
theorem JAtZB.tdkeep_of (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {W : U64 → Prop}
    (hW : P1.WritesIn st s s' W) (hWV : ∀ b, W b → ∀ t ∈ Z.T, b ≠ P1.tdA t) : Sched.TdKeep (L := L) H s s' :=
  Sched.TdKeep.of_writes J.ip.e.tcb (fun _ ht => J.tcbZ ht) hW hWV

end

-- from Fl4Proofs/P3/XTopJointFinW.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

set_option maxHeartbeats 1000000 in
/-- **The untyped caps' facts after a finalisation**: the caps kept (the slots
same), the free parts zero (no `FinW` word there: the TCBs are typed, the
notifications and SCs are spec objects outside it, `SpecFree`, the node is
outside every untyped cap, `JCovD`), the rest by the kept kernel state, CDT,
original bits and the node-0 `DEBUG_TCBS` word (`hDbg`). -/
theorem JAtZB.finW_utc {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
  have hS := J.xtop.fin.1.1.1
  have hR := J.xtop.fin.1.1.2.2.1
  obtain ⟨Q, R, hc, hs⟩ := hS.lists
  have hks : L.ksb s' = L.ksb s := hw.1
  have hcpu : L.cpu s' = L.cpu s := hw.2.1
  have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hks
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
    rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
  have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
  have U := J.utc sl p sb fi dev hsl hcap0 hdv
  have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
    (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases finW_cases hS hb with ⟨y, hy, g1, g2⟩ | ⟨g1, g2⟩ | ⟨n, hn, g1, g2⟩ | ⟨sc, hsc, x, n, hk, g1, g2⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 Z.c hcC
      omega
    · obtain ⟨x, hx, -⟩ := hR.ntfn n hn
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) n.bv _ hx
      simp only [Fl4Spec.objBits, Fl4Spec.ntfnBits, UScalar.bv_toNat] at this
      omega
    · have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) sc.bv _ hk
      simp only [Fl4Spec.objBits, UScalar.bv_toNat] at this
      rw [Nat.add_comm Fl4Spec.minSchedContextBits n] at this
      omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

end

-- from Fl4Proofs/P3/XTopJointStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`cs_frameV` with the VSpace sets put back** (`XTopAt` at `Z`'s sets
after; the CSpace fields and `JRest` from a post at any sets `V'`, which they
do not mention). -/
theorem JAtZB.cs_frameB {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : XVs} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' Z.vs) s' a' σ') (hkb : KBack σ σ') (hbf : JBuf (L := L) Z s' σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hvc : Vs.VsSlotsW Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.mem s'))
    (hlv : LiveDN (L := L) Z.th H Cs G' s' σ') (hzD : ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ D')
    (hcy : JCarryS Z.B H σ') (hdu : DevFrom Z.G G' (L.mem s) (L.mem s') ∧ Sched.UtFrom Z.G G' (L.mem s) (L.mem s'))
    (hvy : VsTyp (L := L) (Z.mv G' Z.vs) s' σ') (hAF : ArchFwd σ σ') (hvn : (Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s'))) :
    JAtZB (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameV (hvn := hvn) hks hX hkb hbf ⟨hC.del, hC.ut, hC.finM, hC.sfree⟩
    ⟨R.call, R.rfree, R.rrecv, R.yld, R.mcp, R.buf, R.rp, R.apart, R.jpl, R.jcov, R.kern, R.utc, R.nsc, R.inv,
      R.cur, R.own, R.off, R.act, R.bsa, R.isorted, R.curRun, R.blk⟩ hvc hlv hzD hcy hdu hvy hAF

end

-- from Fl4Proofs/P3/XTopJointStep.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **The VCPU words kept by a step whose writes miss them** (KENTRY-PLAN
g2b): `VKeep` from a `WritesIn` footprint with no TCB's VCPU word. -/
theorem JAtZB.vkeep_of {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hWV : ∀ b, W b → ∀ t ∈ Z.T, b ≠ tVcpuA t) : VKeep (L := L) Z.th s s' :=
  VKeep.of_writes J.ip.e.tcb J.thT hW hWV

end

-- from Fl4Proofs/P3/XTopJointStep.lean (EXT)
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **`cs_frameV` after IPC work** (`IRel` after, VSpace sets `V'`): the
sets put back to `Z`'s (`XTopAt.vs_backO`: FL4 wrote only `OObj` words, the
spec kept the arch state, arch objects and SC sizes) and the slots kept
(`SlotsSame`, so `JAtZ.vsc` carries over). -/
theorem JAtZB.cs_frameI {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {G' : MdbGhost} {V' : XVs} {s' : S} {a' : A}
    {σ' : Fl4Spec.State Unit} {Ac' : Set U64} {Lst' : U64 → List U64} {D' : Set U64} (hks : L.ksb s' = L.ksb s)
    (hX : XTopAt (L := L) AR (Z.mv G' V') s' a' σ') {W : U64 → Prop} (hW : P1.WritesIn st s s' W)
    (hWO : ∀ b, W b → Vs.OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ b) (hWV : ∀ b, W b → ∀ t ∈ Z.T, b ≠ tVcpuA t)
    (har : σ'.archState = σ.archState)
    (hao : ∀ q ao, σ.kheap q = some (.archObj ao) → σ'.kheap q = some (.archObj ao)) (hsz : Sched.SzKeep σ σ')
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hkb : KBack σ σ') (hfk : IpcFrKeep σ σ')
    (hC : JCs (L := L) (Z.mv G' V') s' σ') (R : JRest (L := L) arI (Z.mv G' V') H Cs Ac' Lst' D' s' σ')
    (hK : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s') (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (hidl : L.idleW s' = L.idleW s) (hDD : ∀ p ∈ ZTcb (L := L) Z.th s, p ∈ D') :
    JAtZB (L := L) arI AR (Z.mv G' Z.vs) H Cs Ac' Lst' D' s' a' σ' :=
  J.cs_frameB (hvn := (J.vsW hW hWO)) hks (J.xtop.vs_backO hX hW hWO har hao hsz) hkb (J.bfK hfk (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy))
    hC R (J.vsc.of_eq fun y hy => hSS.capV hy)
    (J.liveX hX rfl rfl rfl hSS hK horig hidl fun p hp => R.jcov.dead p (hDD p hp)) (J.zDX hSS hDD) (J.carry.of_ao hkb hao)
    (devFrom_same J.xtop.rel.2.1.2.2.1 hX.rel.2.1.2.2.1 hSS) (J.carry.vsSame hSS hks (ArchFwd.of_eq hao))
    (ArchFwd.of_eq hao)

end

-- from Fl4Proofs/P3/XTopJointRegFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across a register step** (module docstring): FL4 writing TCB
registers and fault words and SCs' consumed words, the spec a quiet step
keeping the yield fields (`YKeep`), `Inv` after given (`Inv.scFields`,
`ArchStep.inv`). -/
theorem JAtZB.reg_frameF (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (RegFW Z.T Z.C)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZB (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with (hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with (⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hwF
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qk hA hS3 hI3.1 hwF k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.finW_irq hwF)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwF.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac' Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 hA.mcpKeep, J.buf.frame kb hA.bufKeep, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc)
        (DXKeep.of_dbg hKd (J.tdkeep_of hwF fun _ hb => Ipc.FinW.ntd J.xtop.fin.1.1.1 hb)), hkern,
      J.finW_utc hwF hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, hInv, hA.cur J.cur, hA.own J.own, hA.off J.off,
      hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.sameB J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  exact ⟨Z.vs, J.cs_frameI hks hX3 hwF (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback hA.ipcFr hC R hKd hck.orig (J.idleW_keep hS3 hA.idle hA.isc).1 J.zD⟩

end

-- from Fl4Proofs/P3/XTopJointRegFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JAtZ` across a register step** (`reg_frameF` without fault words). -/
theorem JAtZB.reg_frame (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (RegCW Z.T Z.C)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    ∃ V', JAtZB (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst D s' a σ' :=
  J.reg_frameF hI3 (hw.mono fun _ h => Or.inl h) hA hyk hInv hblk hfoot

end

-- from Fl4Proofs/P3/XTopJointYield.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`set_consumed` of a yield-to pair at `J`** (module docstring). -/
theorem JAtZB.setConsumedJ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {p y : U64} (hpC : p ∈ Z.C)
    (hy : y ∈ Z.T) :
    schedcontext.set_consumed st arI s a p y true ⦃ s1 => ∃ σ1,
      Fl4Spec.setConsumed (Z := Unit) p.bv y.bv σ = ({((), σ1)}, False) ∧ YKeep σ σ1 ∧
      ∃ V, JAtZB (L := L) arI AR (Z.mv Z.G V) H Cs Ac Lst D s1 a σ1 ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨z, n, hkz, -⟩ := hs.scs p hpC
  obtain ⟨x, hkx, -⟩ := hs.tcb y hy
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p z n (J.c0 p hpC) hkz).2⟩
  have hyT : y ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact hy
  have hta := hc.tcbs y hy
  refine WP.spec_mono (WP.spec_and (set_consumed_irel (ar := arI) J.ip s a σ hI hpC hkz hy hkx hmax htu)
    (P1.schedcontext.set_consumed.blk hAT s a p y true J.blk hpS hyT)) ?_
  rintro s1 ⟨⟨σ1, he, hI1, hw⟩, hP1⟩
  obtain ⟨v, w, he'⟩ := Sched.setConsumed_shape hkz hkx
  have e := the_result he' he
  subst e
  have hA := QKY.upd2 (w := Fl4Spec.scConsumedUpdate (fun _ => v) z) (x' := Endp.replyTcb x w) hkz hkx rfl rfl
  have hyk := ykeep_upd2 (w := Fl4Spec.scConsumedUpdate (fun _ => v) z) (x' := Endp.replyTcb x w) hkz hkx rfl rfl
  have hpy : y.bv ≠ p.bv := fun e => by rw [e, hkz] at hkx; cases hkx
  have hk1 : (updSc σ p.bv (Fl4Spec.scConsumedUpdate (fun _ => v) z) n).kheap y.bv = some (.tcb x) := by
    simp only [updSc, updK, Function.update_of_ne hpy]; exact hkx
  have hInv := (archStep_updTcb (x' := Endp.replyTcb x w) hk1 rfl).inv (J.inv.scFields hkz rfl rfl rfl rfl)
  have hw' : P1.WritesIn st s _ (RegCW Z.T Z.C) := hw.mono fun b hb => by
    rcases hb with rfl | ⟨r, rfl⟩
    · exact Or.inr ⟨p, hpC, rfl⟩
    · have hv := regA_val hta (regIdx_lt r)
      have := regIdx_lt r
      exact Or.inl ⟨y, hy, by rw [hv]; omega, by rw [hv]; omega⟩
  obtain ⟨V, J1⟩ := J.reg_frame hI1 hw' hA hyk hInv hP1.1 hP1.2.1
  exact ⟨_, he', hyk, V, J1⟩

end

-- from Fl4Proofs/P3/XTopJointYield.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **The yielder's `complete_yield_to` at `J`** (module docstring), the dead set kept. -/
theorem JAtZB.completeYieldJD (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZB (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  obtain ⟨Q, R0, hc, hs⟩ := J.xtop.fin.1.1.1.lists
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := J.yld.tcb y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb2' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb2']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA y) = 0#u64
  · have : (L.mem s (yieldA y) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, completeYieldTo_none hky (by rw [eyt, hi0, Notif.optRef_zero]), Z.vs, Ac, Lst, J⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA y) = p := ⟨_, rfl⟩
  rw [hp] at hi0 eyt ⊢
  have hb' : (p != 0#u64) = true := by simp [hi0]
  simp only [hb', ↓reduceIte]
  obtain ⟨hpC, -⟩ := J.yld.toSc y hy (by rw [hp]; exact hi0)
  rw [hp] at hpC
  refine WP.spec_bind (J.setConsumedJ hAT hmax htu hpC hy) ?_
  rintro s1 ⟨σ1, he1, hyk, V1, J1⟩
  have hm1 : L.mem s1 (yieldA y) = p := by
    obtain ⟨x1, hk1, e1⟩ := J1.yld.tcb y hy
    obtain ⟨x1', hk1', e1'⟩ := hyk.1 _ xy hky
    rw [hk1] at hk1'; cases hk1'
    rw [eyt, Notif.optRef_ne hi0] at e1'
    rw [e1'] at e1
    exact P1.eq_of_bv (Notif.optRef_some e1.symm).2
  refine WP.spec_bind (J1.cancelYieldJD hy hm1 hi0) ?_
  rintro s2 ⟨σ2, he2, -, -, Ac2, Lst2, J2⟩
  refine (WP.spec_ok _).2 ⟨σ2, ?_, V1, Ac2, Lst2, J2⟩
  rw [completeYieldTo_some hky (by rw [eyt, Notif.optRef_ne hi0]), nd_bind_one he1]
  exact he2

end

-- from Fl4Proofs/P3/XTopJointYield.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- `completeYieldJD` with the dead set existential. -/
theorem JAtZB.completeYieldJ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (V : XVs) (Ac' : Set U64) (Lst' : U64 → List U64) (D' : Set U64),
        JAtZB (L := L) arI AR (Z.mv Z.G V) H Cs Ac' Lst' D' r.1 r.2 σ' ⦄ :=
  WP.spec_mono (J.completeYieldJD hAT hmax htu hy) fun _ ⟨σ', he, V, Ac', Lst', J'⟩ => ⟨σ', he, V, Ac', Lst', D, J'⟩

end


-- from Fl4Proofs/P3/XTopJointRegFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`reg_frameF` at `Z` itself, with the footprint**: the witness of `reg_frameF` is `Z.vs`, so the
post-state `JAtZB` is at `Z`; also names the `FinW` footprint (gen 31, for the VM-epoch lift). -/
theorem JAtZB.reg_frameFZ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {σ' : Fl4Spec.State Unit}
    {Ac' : Set U64}
    (hI3 : IRel st Z.th σ.archState.x64CurrentCr3 Z.N Z.T Z.C Z.E Z.R Z.B Z.c s' σ')
    (hw : P1.WritesIn st s s' (RegFW Z.T Z.C)) (hA : QKY σ σ') (hyk : YKeep σ σ') (hInv : Inv σ')
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac' s')
    (hfoot : P1.WritesIn st s s' (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) ∅ s)) :
    P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) ∧
      JAtZB (L := L) arI AR Z H Cs Ac' Lst D s' a σ' := by
  have hI := J.xtop.irelK J.ks J.buf
  have hT : TcbPlaced Z.T := J.ip.e.tcb
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  have hF : IFrame (L := L) Z.th s s' := IRel.iframe_of hI hw fun b hb => by
    rcases hb with (hb | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩
    · obtain ⟨y, hy, h1, h2⟩ := hb
      exact Or.inr (Or.inr (Or.inl ⟨y, hy, h1, by omega⟩))
    · obtain ⟨x0, n0, hk0, hx0⟩ := hs.scs q hq
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨q, hq, x0, n0, hk0, hx0.in_obj (hx0.hdr (K := 8#u64) (by simp) (by simp)).2⟩))))))
    · exact Or.inr (Or.inr (Or.inl ⟨y, hy, by omega, by omega⟩))
  have hwF : P1.WritesIn st s s' (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) := hw.mono fun b hb => by
    rcases hb with (⟨y, hy, k1, k2⟩ | ⟨q, hq, rfl⟩) | ⟨y, hy, hb⟩
    · exact Or.inr ⟨y, hy, b.val - y.val, by omega, by omega, by omega, by omega, by omega, by omega⟩
    · exact Or.inl (KFoot.of_sw (sw_hdr hS hq (K := 8#u64) (by simp) (by simp) (by decide)))
    · exact Or.inr ⟨y, hy, 3376, by omega, by omega, by omega, by omega, by omega, hb⟩
  have hck : Fl4Proofs.P3.CKeep σ σ' := hA.ckeepP
  have hAR : AR a σ.archState.x64CurrentCr3 := J.xtop.fin.1.1.2.2.2.2.2.2
  obtain ⟨V', hX3⟩ := XTopAt.irel_same J.xtop hI3 hAR hF.1 hck.cdt hck.orig hck.ks hF.2
  have hks : L.ksb s' = L.ksb s := hF.2
  obtain ⟨k1, k2, kb, k3, k4⟩ := J.finW_keeps hwF
  have ck := hA.callKeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 hA.khrb
  have hDbg := J.kw_dbg (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hKd := J.kw_dbgKeep (hfoot.mono fun b hb => kw_empty_mono hb _)
  have hS3 : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hI3.2.2.1
  have hAI3 : ActIdle σ' := hA.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := J.deadP_qk hA hS3 hI3.1 hwF k3 hAI3.1 (J.yld.frame k2 hyk) hyk
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    exact ⟨Tr, Cq, hJ.same hF.1 (fun q y n _ hq => hA.szKeep q.bv y n hq) hks (J.finW_irq hwF)
      (J.idleW_keep hS3 hA.idle hA.isc).2⟩
  have hkern := J.kern_keep hks hwF.2.1 hS3 hA.ct hA.csc (fun sl h => Or.inl (by rw [← hA.orig]; exact h))
    (by rw [hA.arch])
    (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hDbg
    (D' := D)
  have R : JRest (L := L) arI (Z.mv Z.G V') H Cs Ac' Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 hyk, J.mcp.frame k1 hA.mcpKeep, J.buf.frame kb hA.bufKeep, hRP',
      J.apart.sc_frame hks hA.szKeep, hjpl, J.jcov_keep hks hF.1 hdead (J.idleW_keep hS3 hA.idle hA.isc)
        (DXKeep.of_dbg hKd (J.tdkeep_of hwF fun _ hb => Ipc.FinW.ntd J.xtop.fin.1.1.1 hb)), hkern,
      J.finW_utc hwF hF.1 hA.cdt hA.orig hA.arch hDbg, hA.nsc J.nsc, hInv, hA.cur J.cur, hA.own J.own, hA.off J.off,
      hAI3, hA.bsa J.bsa, hA.isorted J.isorted, hA.curRunM J.curRun, hblk⟩
  have hC0 := JCs.sameB J hF.1 hA.ksz
  have hC : JCs (L := L) (Z.mv Z.G V') s' σ' := ⟨hC0.del, hC0.ut, hC0.finM, hC0.sfree⟩
  have JZ := J.cs_frameI hks hX3 hwF (fun b hb => Ipc.FinW.oobj J.xtop.fin.1.1.1 hb) (fun b hb => Ipc.FinW.nv J.xtop.fin.1.1.1 hb) hA.arch (fun q ao h => (hA.oth (fun _ e => by cases e) (fun _ _ e => by cases e)).2 h) hA.szKeep hF.1 hA.kback hA.ipcFr hC R hKd hck.orig (J.idleW_keep hS3 hA.idle hA.isc).1 J.zD
  exact ⟨hwF, JZ⟩

end

-- from Fl4Proofs/P3/XTopJointYield.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`setConsumedJ` at `Z`, with the step's footprint and spec shape** (`QKY`): gen 31, for the
VM-epoch lift. -/
theorem JAtZB.setConsumedJV (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {p y : U64} (hpC : p ∈ Z.C)
    (hy : y ∈ Z.T) :
    schedcontext.set_consumed st arI s a p y true ⦃ s1 => ∃ σ1,
      Fl4Spec.setConsumed (Z := Unit) p.bv y.bv σ = ({((), σ1)}, False) ∧ YKeep σ σ1 ∧
      QKY σ σ1 ∧ P1.WritesIn st s s1 (Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ) ∧
      JAtZB (L := L) arI AR Z H Cs Ac Lst D s1 a σ1 ⦄ := by
  have hS := J.xtop.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hS.lists
  obtain ⟨z, n, hkz, -⟩ := hs.scs p hpC
  obtain ⟨x, hkx, -⟩ := hs.tcb y hy
  have hI := J.xtop.irelK J.ks J.buf
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hpS : p ∈ P1.Heap.scs H := ⟨_, (hJ.sc p z n (J.c0 p hpC) hkz).2⟩
  have hyT : y ∈ P1.Heap.tcbs H := by rw [← J.tcbs_eq.1]; exact hy
  have hta := hc.tcbs y hy
  refine WP.spec_mono (WP.spec_and (set_consumed_irel (ar := arI) J.ip s a σ hI hpC hkz hy hkx hmax htu)
    (P1.schedcontext.set_consumed.blk hAT s a p y true J.blk hpS hyT)) ?_
  rintro s1 ⟨⟨σ1, he, hI1, hw⟩, hP1⟩
  obtain ⟨v, w, he'⟩ := Sched.setConsumed_shape hkz hkx
  have e := the_result he' he
  subst e
  have hA := QKY.upd2 (w := Fl4Spec.scConsumedUpdate (fun _ => v) z) (x' := Endp.replyTcb x w) hkz hkx rfl rfl
  have hyk := ykeep_upd2 (w := Fl4Spec.scConsumedUpdate (fun _ => v) z) (x' := Endp.replyTcb x w) hkz hkx rfl rfl
  have hpy : y.bv ≠ p.bv := fun e => by rw [e, hkz] at hkx; cases hkx
  have hk1 : (updSc σ p.bv (Fl4Spec.scConsumedUpdate (fun _ => v) z) n).kheap y.bv = some (.tcb x) := by
    simp only [updSc, updK, Function.update_of_ne hpy]; exact hkx
  have hInv := (archStep_updTcb (x' := Endp.replyTcb x w) hk1 rfl).inv (J.inv.scFields hkz rfl rfl rfl rfl)
  have hw' : P1.WritesIn st s _ (RegCW Z.T Z.C) := hw.mono fun b hb => by
    rcases hb with rfl | ⟨r, rfl⟩
    · exact Or.inr ⟨p, hpC, rfl⟩
    · have hv := regA_val hta (regIdx_lt r)
      have := regIdx_lt r
      exact Or.inl ⟨y, hy, by rw [hv]; omega, by rw [hv]; omega⟩
  obtain ⟨hwF, J1⟩ := J.reg_frameFZ hI1 (hw'.mono fun _ h => Or.inl h) hA hyk hInv hP1.1 hP1.2.1
  exact ⟨_, he', hyk, hA, hwF, J1⟩

end

section
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **A `FinW` word is not the VCPU-list head word** (module docstring). -/
theorem JAtZB.finW_nh (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {b : U64}
    (h : Ipc.FinW (st := st) Z.T Z.N Z.C Z.c s σ b) : b ≠ P1.vHeadA st s := by
  rcases h with hk | ⟨y, hy, K, h1, h2, -, -, -, e⟩
  · exact J.tfoot_nh (Or.inl hk)
  · intro eb
    subst eb
    have hvh : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
    have d := J.kern.hks y _ (J.zH.1 y hy) (fun _ h => by cases h)
    simp only [P1.HKind.bits, Nat.reducePow] at d
    omega

/-- **`set_consumed p y true` at `JAtZV3 V X`** (module docstring). -/
theorem JAtZV3.setConsumedJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {p y : U64} (hpC : p ∈ Z.C)
    (hy : y ∈ Z.T) :
    schedcontext.set_consumed st arI s a p y true ⦃ s1 => ∃ σ1,
      Fl4Spec.setConsumed (Z := Unit) p.bv y.bv σ = ({((), σ1)}, False) ∧ YKeep σ σ1 ∧
      JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s1 a σ1 ⦄ := by
  have B := J.z2.zv.base
  have hS := B.xtop.fin.1.1.1
  refine WP.spec_mono (B.setConsumedJV hAT hmax htu hpC hy) fun s1 ⟨σ1, he, hyk, hA, hwF, B'⟩ => ⟨σ1, he, hyk, ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := zv_qky hA
  exact J.ofBS B' hwF (fun b hb => Ipc.FinW.oobj hS hb) (fun b hb => B.finW_nh hb)
    (B.vkeep_of hwF fun b hb => Ipc.FinW.nv hS hb)
    (fun u hu => by obtain ⟨vu, hvu⟩ := J.z2.zv.vm.spec u hu; exact h1 _ _ hvu) h2 h3 h4

/-- **`complete_yield_to y` at `JAtZV3 V X`** (module docstring; P3/XTopJointYield's `JAtZ.completeYieldJD`
proof with the `JAtZV3` steps). -/
theorem JAtZV3.completeYieldJ (J : JAtZV3 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (hAT : P0.ArchTotal arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄) {y : U64} (hy : y ∈ Z.T) :
    schedcontext.complete_yield_to st arI s a y ⦃ r => ∃ σ',
      Fl4Spec.completeYieldTo (Z := Unit) y.bv σ = ({((), σ')}, False) ∧
      ∃ (Ac' : Set U64) (Lst' : U64 → List U64),
        JAtZV3 (L := L) arI V X AR Z H Cs Ac' Lst' D r.1 r.2 σ' ⦄ := by
  have B := J.z2.zv.base
  obtain ⟨Q, R0, hc, hs⟩ := B.xtop.fin.1.1.1.lists
  have hy0 : y ≠ 0#u64 := fun e => (hc.tcbs y hy).ne0 (by rw [e]; rfl)
  obtain ⟨xy, hky, eyt⟩ := B.yld.tcb y hy
  unfold schedcontext.complete_yield_to
  step with obj.Tcb.is_null.spec as ⟨b, hb⟩
  have hb2' : b = false := by rw [hb]; exact decide_eq_false hy0
  rw [hb2']
  simp only [Bool.false_eq_true, ↓reduceIte]
  step with obj.Tcb.yield_to.spec as ⟨i, hi⟩
  subst hi
  by_cases hi0 : L.mem s (yieldA y) = 0#u64
  · have : (L.mem s (yieldA y) != 0#u64) = false := by simp [hi0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨σ, completeYieldTo_none hky (by rw [eyt, hi0, Notif.optRef_zero]), Ac, Lst, J⟩
  obtain ⟨p, hp⟩ : ∃ p, L.mem s (yieldA y) = p := ⟨_, rfl⟩
  rw [hp] at hi0 eyt ⊢
  have hb' : (p != 0#u64) = true := by simp [hi0]
  simp only [hb', ↓reduceIte]
  obtain ⟨hpC, -⟩ := B.yld.toSc y hy (by rw [hp]; exact hi0)
  rw [hp] at hpC
  refine WP.spec_bind (J.setConsumedJ hAT hmax htu hpC hy) ?_
  rintro s1 ⟨σ1, he1, hyk, J1⟩
  have hm1 : L.mem s1 (yieldA y) = p := by
    obtain ⟨x1, hk1, e1⟩ := J1.z2.zv.base.yld.tcb y hy
    obtain ⟨x1', hk1', e1'⟩ := hyk.1 _ xy hky
    rw [hk1] at hk1'; cases hk1'
    rw [eyt, Notif.optRef_ne hi0] at e1'
    rw [e1'] at e1
    exact P1.eq_of_bv (Notif.optRef_some e1.symm).2
  refine WP.spec_bind (J1.cancelYieldJ hy hm1 hi0) ?_
  rintro s2 ⟨σ2, he2, Ac2, Lst2, J2⟩
  refine (WP.spec_ok _).2 ⟨σ2, ?_, Ac2, Lst2, J2⟩
  rw [completeYieldTo_some hky (by rw [eyt, Notif.optRef_ne hi0]), nd_bind_one he1]
  exact he2

end

end

end

end Fl4Proofs.P3
