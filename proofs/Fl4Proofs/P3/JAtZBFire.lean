/-
P3 (line mmuAD, gen 32): **FL4's TCB timers (`timer.fire`) over `JAtZB`** — ScFireJ's chain with `JAtZ` → `JAtZB`
(the joint invariant without `JExt`, the VM-epoch base of `JAtZV`/`JAtZV3`), produced by `scratch/mmu32_jatzb_gen.py`
(gen 24's generator with the gen 31 signature bug fixed: the signature now ends at the first `:=` outside brackets,
so `JAtZ.fireJ (hSig : SignalJHyp (L := L) …) … (J : JAtZ …)` is found) and the decls missing over `JAtZB` kept:
`JAtZB.otherTmOK`, `tw_word`, `tmw_word`, `tmw_obj`, `tmw_ne_tcb`, `tmw_ne_obj`, `tmw_ne_node`, `tmw_slots`,
`deadP_hstep`, `notDbg_tw`, `jcov_keepX`, `tmw_utc`, `tmw_step`, `reprogramJ`; by hand (same text, `JAtZ` → `JAtZB`):
**`SignalJHypB`**, **`FireInvB`**, **`fire_loopJB`**, then **`JAtZB.fireJ`**. Every post `JAtZ` → `JAtZB`.
Other edit: `JAtZB.tmw_step` calls `JAtZB.cs_frameK`, which has no `tVcpuA` (JExt) argument, so the original's
TCB-VCPU-word frame argument is dropped.

Named premise: **`SignalJHypB` [J]** — ScFireJ's `SignalJHyp` [J] with `JAtZ` → `JAtZB` (`send_signal` from a
`JAtZB` state at a notification of `N` against the spec's `sendSignal`, deterministic, `JAtZB` after at fresh VSpace
sets, domain time kept). Why it stays [J] (exactly): over `JAtZ`, ScSignalJ's `signalJHyp_of` reduces `SignalJHyp`
to `SignalRestJHyp` [J], the case of an idle notification whose bound thread is `RunningVM` — FL4's
`send_signal` then `remote_tcb_stall`s the thread (the VM exits on another core) while the spec's `sendSignal` only
sets the badge: the spec has no VM-exit-on-signal (Ext/VirtEntry: FL4 #80/#81/#85 and the signal exit are not yet
modelled, owned by the virt line), so no refinement is possible; the waking cases are proved over `JAtZ` only
(`signal_badge_post`, `signal_waitDJ`, `signal_boundDJ`, ScSignalDonJ), and their `JAtZB` copies (the same
generator method) are the next step, after which `SignalJHypB` reduces to `SignalRestJHypB` exactly as over `JAtZ`.
Not false on reachable states: it is the JAtZB-level statement of `SignalJHyp`, whose non-runningVM cases are
theorems over `JAtZ`. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV3Sched
import Fl4Proofs.P3.ScFireJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
variable {Lst : U64 → List U64} {D : Set U64}

-- from Fl4Proofs/P3/XTopJoint.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc

/-- **The other cores' timer words on `JAt`** (`OtherTmOK`): each other
core's node misses `H`'s objects (`JKern.hnd`), which hold the slots' CNodes
and TCBs (`JPlaced`), the sets' objects (`zH`), the SCs (`JPlaced.sc`) and the
arch objects (`SpecCover.arch`); it lies below the ASID table (`JKern.csLt`)
and misses the IPC-buffer words (`nodeB`). -/
theorem JAtZB.otherTmOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    OtherTmOK (L := L) Z Cs s σ := by
  intro c' hc' e
  have hX := J.xtop
  have K := J.kern
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hTe : Z.T = P1.Heap.tcbs H :=
    Set.ext fun t => ⟨fun h => J.zH.1 t h, fun h => J.thT t ((hJ.tcb t).2 h)⟩
  have hNP : P1.NodePlaced st Z.T s c' := by rw [hTe]; exact P1.TInv.nodes J.blk c' hc'
  have hlt := K.csLt c' hc'
  have hnb : L.nodeBase s c' = (L.ksb s).val + 13568 + c'.val * 4288 := rfl
  have hout : ∀ p k, H p = some k → p.val + 2 ^ k.bits ≤ L.nodeBase s c' ∨ L.nodeBase s c' + 4288 ≤ p.val :=
    fun p k hp => K.hnd p k hp c' hc'
  refine ⟨hNP, fun o ho => ?_⟩
  have hv := P1.nodeAt_val hNP (off := o) (by omega)
  have hb : L.nodeBase s c' ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val + 8 ≤ L.nodeBase s c' + 4288 := by
    rw [hv]; omega
  -- a word in an object of `H` of `2 ^ k.bits` bytes is not in the node
  have miss : ∀ p k, H p = some k → ¬ (p.val ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val < p.val + 2 ^ k.bits) :=
    fun p k hp ⟨h1, h2⟩ => by rcases hout p k hp with h | h <;> omega
  have hVs := hX.fin.2.1
  have hPt := hX.fin.2.2.1
  have arch : ∀ q : U64, (∃ ao, σ.kheap q.bv = some (.archObj ao)) →
      ¬ (q.val ≤ (L.nodeAt s c' o).val ∧ (L.nodeAt s c' o).val < q.val + 4096) := by
    rintro q ⟨ao, hq⟩ ⟨h1, h2⟩
    obtain ⟨n, hn, hH⟩ := J.cover.arch _ ao hq
    have : (4096 : Nat) ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hn; simpa using this
    exact miss q _ hH ⟨h1, by simp only [P1.HKind.bits]; omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- no VSpace object
    rintro (⟨q, r, hq, h1, h2⟩ | ⟨t, ht, h1, h2⟩ | ⟨q, hq, h1, h2⟩ | ⟨h1, h2⟩)
    · exact miss q _ (hJ.cnode q r hq) ⟨h1, by simp only [P1.HKind.bits]; rw [pow_add]; omega⟩
    · exact miss t _ ((hJ.tcb t).1 ht) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · refine arch q ?_ ⟨h1, h2⟩
      rcases hq with hq | hq | hq | hq | hq
      · obtain ⟨f, hf, -⟩ := hVs.pool q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l4 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l3 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l2 q hq; exact ⟨_, hf⟩
      · obtain ⟨f, hf, -⟩ := hPt.l1 q hq; exact ⟨_, hf⟩
    · rw [hnb] at hb; omega
  · -- no endpoint-relation word
    rintro (⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨t, ht, h | h⟩ | ⟨wp, hwp, h⟩)
    · exact miss e _ (J.zH.2.1 e he) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · exact miss r _ (J.zH.2.2.1 r hr) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · obtain ⟨h1, h2⟩ := h; unfold Endp.TOffN at h2
      exact miss t _ (J.zH.1 t ht) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · unfold Endp.TL at h
      exact miss t _ (J.zH.1 t ht) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
    · have := J.nodeB wp hwp c' (J.kern.csLt c' hc'); rw [← h] at this; omega
  · -- no notification-relation word
    rintro (⟨n, hn, h1, h2⟩ | ⟨t, ht, h⟩)
    · exact miss n _ (J.zH.2.2.2 n hn) ⟨h1, by simp only [P1.HKind.bits]; omega⟩
    · have hv' := nfootT_val (hX.fin.1.1.1.placed.tcb t ht) h
      exact miss t _ (J.zH.1 t ht) ⟨by omega, by simp only [P1.HKind.bits]; omega⟩
  · -- no SC word
    intro sc hsc x n hk ⟨h1, h2⟩
    obtain ⟨-, hH⟩ := hJ.sc sc x n (J.c0 sc hsc) hk
    exact miss sc _ hH ⟨h1, by simp only [P1.HKind.bits]; omega⟩

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **A timer word, by value**: a TCB's timer fields (offsets 3528..3576), or
a timer-tree or `REPROGRAM` word of a core's node. -/
theorem JAtZB.tw_word {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : P1.TW st Z.T Cs s b) :
    (∃ y ∈ Z.T, y.val + 3528 ≤ b.val ∧ b.val < y.val + 3576) ∨
    (∃ c ∈ Cs, ∃ o : Nat, (o = 104 ∨ o = 112) ∧ b.val = L.nodeBase s c + o) := by
  have hNP : ∀ c ∈ Cs, P1.NodePlaced st Z.T s c := fun c hc => by
    rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk c hc
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  rcases hb with ⟨y, hy, K, h1, h2, rfl⟩ | ⟨c', hc', o, ho, rfl⟩
  · left
    exact ⟨y, hy, by rw [Notif.tfield_val (hT y hy) (by omega)]; omega,
      by rw [Notif.tfield_val (hT y hy) (by omega)]; omega⟩
  · right; exact ⟨c', hc', o.val, ho, P1.nodeAt_val (hNP c' hc') (by omega)⟩

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

theorem JAtZB.tmw_word {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) :
    (∃ y ∈ Z.T, y.val + 3528 ≤ b.val ∧ b.val < y.val + 3576) ∨
    (∃ c ∈ Cs, ∃ o : Nat, (o = 104 ∨ o = 112 ∨ o = 56) ∧ b.val = L.nodeBase s c + o) := by
  rcases hb with hb | rfl
  · rcases J.tw_word hb with h | ⟨c, hc, o, ho, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, o, by omega, e⟩
  · right
    obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
    have hcC : Z.c ∈ Cs := hcq.cur ▸ J.kern.cpuCs
    have hN : P1.NodePlaced st Z.T s Z.c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
    have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
    exact ⟨Z.c, hcC, 56, by omega, by rw [P1.nodeAt_val hN (by omega), h56]⟩

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **A timer word lies in no object of `H`** but a TCB's timer fields. -/
theorem JAtZB.tmw_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k)
    (hin : p.val ≤ b.val ∧ b.val < p.val + 2 ^ k.bits) :
    k = .tcb ∧ p ∈ Z.T ∧ p.val + 3528 ≤ b.val ∧ b.val < p.val + 3576 := by
  have hH := J.kern.heap
  rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c, hc, o, ho, e⟩
  · have hHy : H y = some .tcb := J.zH.1 y hy
    by_cases hne : p = y
    · subst hne; rw [hHy] at hp; cases hp; exact ⟨rfl, hy, g1, g2⟩
    · have := hH.disj p _ y _ hp hHy hne
      have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := rfl
      rw [e12] at this; omega
  · have := J.kern.hnd p k hp c hc
    rcases ho with rfl | rfl | rfl <;> omega

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- A timer word is no TCB word off the timer fields. -/
theorem JAtZB.tmw_ne_tcb {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {t : U64} (ht : t ∈ Z.T) {w : U64} {K : Nat}
    (hwv : w.val = t.val + K) (hK : K < 3528 ∨ (3576 ≤ K ∧ K < 4096)) : b ≠ w := fun e => by
  subst e
  have := J.tmw_obj hb (J.zH.1 t ht) (by simp only [P1.HKind.bits]; omega)
  omega

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- A timer word is no word of a non-TCB object of `H`. -/
theorem JAtZB.tmw_ne_obj {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {p : U64} {k : P1.HKind} (hp : H p = some k) (hk : k ≠ .tcb)
    {w : U64} (hw : p.val ≤ w.val ∧ w.val < p.val + 2 ^ k.bits) : b ≠ w := fun e => by
  subst e; exact hk (J.tmw_obj hb hp hw).1

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- A timer word is no node word off the timer-tree and `REPROGRAM` words. -/
theorem JAtZB.tmw_ne_node {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : TmW (L := L) Z.T Cs Z.c s b) {c : U64} (hc : c ∈ Cs) {o : U64} (ho : o.val < 4288)
    (h1 : o.val ≠ 104) (h2 : o.val ≠ 112) (h3 : o.val ≠ 56) : b ≠ L.nodeAt s c o := fun e => by
  have hN : P1.NodePlaced st Z.T s c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk c hc
  have hv := P1.nodeAt_val hN ho
  have hnb : ∀ c, L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := fun _ => rfl
  rw [← e] at hv
  rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c', hc', o', ho', e'⟩
  · have := J.kern.hnd y _ (J.zH.1 y hy) c hc
    simp only [P1.HKind.bits] at this; omega
  · simp only [hnb] at hv e'
    by_cases hcc : c' = c
    · subst hcc; omega
    · have : c'.val ≠ c.val := fun h => hcc (UScalar.eq_of_val_eq h)
      rcases Nat.lt_or_gt_of_ne this with h | h
      · have : c'.val * 4288 + 4288 ≤ c.val * 4288 := by nlinarith
        omega
      · have : c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
        omega

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- `SlotsSame` across timer-word writes: the slots lie in `Z.th`'s objects,
which are `H`'s (`JPlaced`), at a TCB's cap slots (below offset 256). -/
theorem JAtZB.tmw_slots {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s)) : SlotsSame Z.th (L.mem s) (L.mem s') := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hPl := hJ.pl
  intro x hx
  have hf := hx.fit hPl
  have hal := hx.align hPl
  obtain ⟨p, i, hi, rfl⟩ := id hx
  have hv := hi.val hPl
  -- the slot's 32 bytes lie in `p`'s object of `H`, below 256 if a TCB
  have hin : ∃ k, H p = some k ∧ p.val + 32 * (i + 1) ≤ p.val + 2 ^ k.bits ∧ (k = .tcb → 32 * (i + 1) ≤ 256) := by
    rcases hi with ⟨r, hp, hr⟩ | ⟨hp, hr⟩
    · refine ⟨_, hJ.cnode p r hp, ?_, fun e => by cases e⟩
      simp only [P1.HKind.bits]
      have : 2 ^ (r + 5) = 32 * 2 ^ r := by rw [pow_add]; ring
      rw [this]
      have : i + 1 ≤ 2 ^ r := hr
      nlinarith
    · refine ⟨_, (hJ.tcb p).1 hp, ?_, fun _ => ?_⟩
      · simp only [P1.HKind.bits]; simp [tcbSlots] at hr; omega
      · simp [tcbSlots] at hr; omega
  obtain ⟨k, hHk, hsz, htcb⟩ := hin
  have w : ∀ kk : U64, kk.val < 32 → kk.val % 8 = 0 → L.mem s' (wordOf (slotOf p i) kk) = L.mem s (wordOf (slotOf p i) kk) := by
    intro kk hk hk8
    have hv' := wordOf_val (a := slotOf p i) (k := kk) (by omega)
    refine hw.2.2 _ (by unfold P1.Aligned; rw [hv']; omega) fun hb => ?_
    have g := J.tmw_obj hb hHk (by rw [hv', hv]; omega)
    have g2 := htcb g.1
    rw [hv', hv] at g
    omega
  refine ⟨?_, w 8#u64 (by decide) (by decide), w 16#u64 (by decide) (by decide), w 24#u64 (by decide) (by decide)⟩
  have := w 0#u64 (by decide) (by decide)
  rwa [wordOf_zero] at this

end


-- from Fl4Proofs/P3/DeadKeep.lean
section
open fl4_core Classical Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **The dead stay dead across a heap-keeping step** (`deadP_keep` with
every object but the CNodes kept, `HStep`). -/
theorem JAtZB.deadP_hstep {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
    {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {s' : S} {a' : A} {σ' : Fl4Spec.State Unit}
    {G' : MdbGhost} (hX' : XTopAt (L := L) AR { Z with G := G' } s' a' σ') (hC : HStep σ σ')
    (hRW : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q))
    (hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K)) (hAS : ActSched σ')
    (hY' : YieldRel Z.T Z.C (L.mem s') σ') (hYK : YKeep σ σ')
    {q : U64} (hd : DeadP (L := L) H s q) : DeadP (L := L) H s' q :=
  J.deadP_keep hX'.fin.1.1.1 hX'.ipc (fun x hx _ => let ⟨y, hy, hc⟩ := hC.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
    (fun x hx => (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx)
    (fun x hx => ⟨x, hC.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
    (fun x hx => ⟨x, (hC.look (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx, rfl⟩)
    (fun x n hx => ⟨x, hC.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (hRW q) (fun z hz _ => hOut q z hz) hC.idle hAS hY'
    (hYK.dk q.bv) hd

end


-- from Fl4Proofs/P3/LiveFrame.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

/-- **A word apart from the TCBs' debug links and the nodes' debug heads is no
debug word** (the links at TCB offsets 3576 and 3584). -/
theorem JAtZB.notDbg_tw {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (htcb : ∀ y ∈ Z.T, ∀ (w : U64) (K : Nat), w.val = y.val + K → 3576 ≤ K → K < 4096 → b ≠ w)
    (hnode : ∀ c ∈ Cs, b ≠ L.nodeAt s c layout.node.DEBUG_TCBS) :
    ¬ P1.DbgW st (P1.Heap.tcbs H) Cs s b := by
  obtain ⟨⟨Q, R, hq⟩, -⟩ := J.blk
  have hT := hq.tcbs
  have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
  rintro (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · have h3 : (3576#u64 : U64).val = 3576 := by simp
    exact htcb y (by rw [hTe]; exact hy) _ 3576
      (by rw [show P1.dnA y = core.num.U64.wrapping_add y 3576#u64 from rfl, P1.field_val (hT y hy) (by simp), h3])
      le_rfl (by norm_num) e
  · have h3 : (3584#u64 : U64).val = 3584 := by simp
    exact htcb y (by rw [hTe]; exact hy) _ 3584
      (by rw [show P1.dpA y = core.num.U64.wrapping_add y 3584#u64 from rfl, P1.field_val (hT y hy) (by simp), h3])
      (by norm_num) (by norm_num) e
  · exact hnode c hc e

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **`JCovD` across a step keeping every slot**, the dead set's `DeadX`
carried by the caller (`JAtZ.jcov_keep` with `hdx` in place of a
`DXKeep`: the timer steps write deadline words). -/
theorem JAtZB.jcov_keepX {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hks : L.ksb s' = L.ksb s)
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s')) (hdead : ∀ q ∈ D, DeadP (L := L) H s' q)
    (hidl : Sched.IdleKeep (L := L) s s')
    (hdx : ∀ q ∈ D, Sched.DeadX (L := L) H Cs s q → Sched.DeadX (L := L) H Cs s' q) :
    JCovD (L := L) Z.th H Z.G D Cs s' := by
  obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
  have hsl : ∀ x ∈ Z.G.chains.flatten, IsSlot Z.th x := fun x h => ((hM.members x).1 h).1
  exact J.jcov.same (fun y hy _ _ => ⟨hy, hSS.capV (hsl y hy)⟩) (fun q hq _ => hdead q hq)
    (J.jcov.ks.keep hks fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩) hidl hks
    (J.jcov.idleOut.keep hidl fun x hx p sb fi d hc => ⟨x, hx, fi, by rw [← hSS.capV (hsl x hx)]; exact hc⟩) hdx

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 2000000 in
/-- **The untyped caps' facts across timer-word writes** (`finW_utc`'s
argument: no timer word in an untyped cap's free part, the TCBs being typed
and the nodes outside every untyped region). -/
theorem JAtZB.tmw_utc {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} {σ' : Fl4Spec.State Unit}
    (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s))
    (hSS : SlotsSame Z.th (L.mem s) (L.mem s'))
    (hcdt : σ'.cdt = σ.cdt) (horig : σ'.isOriginalCap = σ.isOriginalCap)
    (harch : σ'.archState = σ.archState)
    (hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS)) :
    ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s') (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s' σ' Z.G sl p sb fi := by
  intro sl p sb fi dev hsl hcap hdv
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
  have hfi := U.fiLe
  have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
  refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_, U.sb4, U.nostr, U.nsFree,
    fun h0 => U.ns (by rw [hcdt] at h0; exact h0),
    ?_, fun g => by rw [hna]; exact U.dwReg (B g),
    fun g => by rw [harch]; exact U.gReg (B g)⟩
  · intro g w hal h1 h2
    rw [hw.mem_eq hal fun hb => ?_]
    · exact U.zero (B g) w hal h1 h2
    rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c, hc, o, ho, e⟩
    · have hth : Z.th y = some .tcb := (hJ.tcb y).2 (J.zH.1 y hy)
      have := U.free y .tcb hth
      simp only [objSize] at this; omega
    · have := (J.jcov.ks _ hxm p sb fi (ramCap_of_notDev hcv (B g))).2.1 c hc
      omega
  · intro g h0 hf0
    rw [hcdt] at h0
    obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
    exact ⟨fun sl' h => r1 sl' (by rw [← horig]; exact h), by rw [hna, hDbg]; exact r3⟩

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **`JAtZ` across timer-word writes** (module docstring): the timer words
written, `REPROGRAM` kept or set to 1, P1's `BlkOK` after given; a dead TCB's
deadline word stays 0 (`hTd`). -/
theorem JAtZB.tmw_step {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {s' : S} (hw : P1.WritesIn st s s' (TmW (L := L) Z.T Cs Z.c s))
    (hR : L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = L.mem s (L.nodeAt s Z.c layout.node.REPROGRAM) ∨
      L.mem s' (L.nodeAt s Z.c layout.node.REPROGRAM) = 1#u64)
    (hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s')
    (hTd : ∀ q ∈ D, H q = some .tcb → L.mem s (P1.tdA q) = 0#u64 → L.mem s' (P1.tdA q) = 0#u64) :
    ∃ r : Bool, JAtZB (L := L) arI AR Z H Cs Ac Lst D s' a { σ with reprogramTimer := σ.reprogramTimer || r } := by
  obtain ⟨r, hX'⟩ := J.xtop.tmStep J.otherTmOK hw hR
  refine ⟨r, ?_⟩
  set σ' : Fl4Spec.State Unit := { σ with reprogramTimer := σ.reprogramTimer || r } with hσ'
  have F : Sched.NFr true σ.curThread σ σ' := Sched.NFr.rt _ σ _
  have hS := J.xtop.fin.1.1.1
  have hS' : SchedRel st Z.N Z.T Z.C Z.c s' σ' := hX'.fin.1.1.1
  obtain ⟨Q, R0, hc, -⟩ := hS.lists
  have hT := hc.tcbs
  have hks : L.ksb s' = L.ksb s := hw.1
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  -- the frame words
  have k1 : ∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t) := fun t ht =>
    ⟨hw.mem_eq (mcpA_aligned hT ht) fun hb => J.tmw_ne_tcb hb ht (mcpA_val hT ht) (by omega) rfl,
      hw.mem_eq (flagsA_aligned hT ht) fun hb => J.tmw_ne_tcb hb ht (flagsA_val hT ht) (by omega) rfl⟩
  have k2 : ∀ t ∈ Z.T, L.mem s' (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    hw.mem_eq (yieldA_aligned hT ht) fun hb => J.tmw_ne_tcb hb ht (yieldA_val hT ht) (by omega) rfl
  have kb : ∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    hw.mem_eq (tIpcBufA_aligned (hT t ht)) fun hb => J.tmw_ne_tcb hb ht (tIpcBufA_val (hT t ht)) (by omega) rfl
  -- a word of an SC of `H`
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s' w = L.mem s w := fun q z hq w hal h1 h2 =>
    hw.mem_eq hal fun hb => J.tmw_ne_obj hb hq (fun e => by cases e) (by simp only [P1.HKind.bits]; omega) rfl
  have k3 : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj hS hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word hS hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s' (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧ L.mem s' (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      hw.mem_eq (J.rp.aligned hr ha) fun hb => J.tmw_ne_obj hb hHr (fun e => by cases e)
        (by simp only [P1.HKind.bits]; omega) rfl
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hH.align q _ hq
    have hfit := hH.fits q _ hq
    have hz := hH.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word and the IRQ node
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) = L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) :=
    hw.mem_eq J.kern.dwAl fun hb => J.tmw_ne_node hb J.kern.cs0 (by simp)
      (by simp) (by simp) (by simp) rfl
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s') (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hw J.kern.ksbFit J.kern.ksbAl fun b hb => by
      rcases J.tmw_word hb with ⟨y, hy, g1, g2⟩ | ⟨c, hc, o, ho, e⟩
      · have := hJ.ks y _ (J.zH.1 y hy) (fun _ e => by cases e); simp only [P1.HKind.bits] at this; omega
      · simp only [P1.LawfulStore.nodeBase] at e; omega
  have hSS := J.tmw_slots hw
  -- the dead stay dead
  have hAI : ActIdle σ' := F.actIdle J.act
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_hstep (G' := Z.G) hX' ⟨fun p => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (fun q hq => k3 q hq) hOut
      hAI.1 (J.yld.frame k2 F.ykeep) F.ykeep (J.jcov.dead q hq)
  have ck := F.ckeep
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hks ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hks hirq (J.idleW_keep hS' F.sk.idle F.sk.isc).2⟩
  have hkern := J.kern_keep hks hw.2.1 hS' F.sk.ct F.sk.csc (fun sl h => Or.inl (by rw [← F.sk.orig]; exact h))
    (by rw [F.sk.arch])
    (fun q ao h => F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)) hDbg
    (D' := D)
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hw fun b hb =>
    J.notDbg_tw (fun y hy w K hwv h1 h2 => J.tmw_ne_tcb hb hy hwv (Or.inr ⟨h1, h2⟩))
      (fun c hc => J.tmw_ne_node hb hc (by simp [P1.debug_val]) (by simp [P1.debug_val]) (by simp [P1.debug_val])
        (by simp [P1.debug_val]))
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 F.ykeep, J.mcp.frame k1 F.mcpKeep, J.buf.frame kb F.bufKeep, hRP',
      J.apart.sc_frame hks F.szKeep, hjpl, J.jcov_keepX hks hSS hdead (J.idleW_keep hS' F.sk.idle F.sk.isc)
        (fun q hq h => h.keepT hKd (hTd q hq)), hkern,
      J.tmw_utc hw hSS F.sk.cdt F.sk.orig F.sk.arch hDbg, F.nsc J.nsc, J.inv.rt _,
      J.cur.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curInv, F.own J.own, F.off J.off,
      hAI, F.bsa J.bsa, F.isorted J.isorted,
      J.curRun.imp (fun e => by rw [(F.act rfl).1]; exact e) F.curRunW, hblk⟩
  exact J.cs_frameK (hvn := J.vsSS (G' := Z.G) hX' hks hSS (Vs.ArchShr.of_ao F.sk.arch fun q ao h =>
    F.othF h (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e))) hks hX' F.kback F.ipcFr (J.carry.frame subset_rfl F.ipcFr F.ksz) (JCs.sameB J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy)
    hSS hKd F.sk.idle

end


-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **The `REPROGRAM` write** at the end of a fired timer: `JAtZ` after,
`reprogram_timer` set. -/
theorem JAtZB.reprogramJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    JAtZB (L := L) arI AR Z H Cs Ac Lst D
      (L.wr s (L.nodeAt s (L.cpu s) layout.node.REPROGRAM) 1#u64) a { σ with reprogramTimer := true } := by
  obtain ⟨Q, R0, hc, -⟩ := J.xtop.fin.1.1.1.lists
  have hcC : Z.c ∈ Cs := hc.cur ▸ J.kern.cpuCs
  have hN : P1.NodePlaced st Z.T s Z.c := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk Z.c hcC
  have hal : P1.Aligned (L.nodeAt s Z.c layout.node.REPROGRAM) :=
    P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM])
  rw [hc.cur]
  have hw : P1.WritesIn st s (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64) (TmW (L := L) Z.T Cs Z.c s) :=
    (P1.writesIn_wr hal).mono fun b hb => Or.inr hb
  have hblk := P1.reprogram.tinv (v := 1#u64) (P1.BlkOK.tinv J.blk)
  rw [hc.cur] at hblk
  have hTd : ∀ q ∈ D, H q = some .tcb → L.mem s (P1.tdA q) = 0#u64 →
      L.mem (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64) (P1.tdA q) = 0#u64 := fun q _ hH h0 => by
    have hqT : q ∈ Z.T := by rw [J.tcbs_eq.1]; exact hH
    have hT := hc.tcbs
    exact ((P1.writesIn_wr hal).mem_eq (P1.field_aligned (hT q hqT) (K := 3528#u64) (by simp) (by simp))
      fun hb => P1.node_ne_field hN (o := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM]) hqT (hT q hqT)
        (K := 3528#u64) (by simp) hb.symm).trans h0
  obtain ⟨r, J'⟩ := J.tmw_step hw (Or.inr (P1.LawfulStore.mem_wr_same hal)) hblk hTd
  have hrp := J'.xtop.fin.1.1.1.repr
  have e : (σ.reprogramTimer || r) = true := by
    have e1 : (σ.reprogramTimer || r) = decide (Sched.nodeW st (L.wr s (L.nodeAt s Z.c layout.node.REPROGRAM) 1#u64)
      Z.c layout.node.REPROGRAM ≠ 0#u64) := hrp
    rw [e1]; unfold Sched.nodeW
    rw [P1.nodeAt_of_ksb (hw.1) Z.c layout.node.REPROGRAM, P1.LawfulStore.mem_wr_same hal]; simp
  rw [e] at J'
  exact J'

end


section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

variable (arI) in
/-- **`send_signal` keeps `JAtZB`** [J] (ScFireJ's `SignalJHyp` with `JAtZ` → `JAtZB`, gen 32; JAtZBFire module docstring): from `JAtZ` at a
notification of `N`, FL4's `send_signal` against the spec's `send_signal`
(deterministic, not failing), `JAtZ` after at fresh VSpace sets
(`XTopAt.irel_same`'s), the domain time kept. The IPC side is proved on
`IRel` (`send_signal_top`); the `JAtZ` lift (the footprint and spec frame
of a notification's wake: the dequeue or the bound receiver's
`cancel_ipc`, the restart, the SC donation, the switch, the sporadic
check) is not. -/
def SignalJHypB (AR : A → Fl4Spec.Cr3 → Prop) (H : P1.Heap) (Cs : Set U64) : Prop :=
  ∀ (Z : XSets) (Ac : Set U64) (Lst : U64 → List U64) (D : Set U64) (s : S) (a : A) (σ : Fl4Spec.State Unit)
    (n badge : U64), JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ → n ∈ Z.N →
    notification.send_signal st arI s a n badge ⦃ r => ∃ (σ' : Fl4Spec.State Unit) (V' : XVs) (Ac' : Set U64)
      (Lst' : U64 → List U64) (D' : Set U64),
      Fl4Spec.sendSignal (Z := Unit) n.bv badge.bv σ = ({((), σ')}, False) ∧ σ'.domainTime = σ.domainTime ∧
      JAtZB (L := L) arI AR (Z.mv Z.G V') H Cs Ac' Lst' D' r.1 r.2 σ' ⦄

/-- The loop's invariant: `JAtZ` at fresh VSpace sets after some fired
timers, the domain time kept. -/
def FireInvB (AR : A → Fl4Spec.Cr3 → Prop) (Z : XSets) (H : P1.Heap) (Cs : Set U64) (σ : Fl4Spec.State Unit)
    (s : S) (a : A) : Prop :=
  ∃ (σ1 : Fl4Spec.State Unit) (V1 : XVs) (Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
    Fires σ σ1 ∧ σ1.domainTime = σ.domainTime ∧ JAtZB (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s a σ1

set_option maxHeartbeats 8000000 in
/-- **The TCB timers' loop keeps `FireInv`** (module docstring). -/
theorem fire_loopJB (hSig : SignalJHypB (L := L) arI AR H Cs) {σ : Fl4Spec.State Unit} (s : S) (a : A) (now i : U64)
    (h : FireInvB (L := L) (arI := arI) AR Z H Cs σ s a) :
    timer.fire_loop st arI s a now i ⦃ r => FireInvB (L := L) (arI := arI) AR Z H Cs σ r.1 r.2 ⦄ := by
  unfold timer.fire_loop
  apply loop.spec_decr_nat (measure := fun x => 32 - x.2.2.val)
    (inv := fun x => FireInvB (L := L) (arI := arI) AR Z H Cs σ x.1 x.2.1)
  · rintro ⟨s1, a1, i1⟩ h1
    try simp only at h1
    obtain ⟨σ1, V1, Ac1, Lst1, D1, hF1, hd1, J1⟩ := id h1
    have hTe : Z.T = P1.Heap.tcbs H := J1.tcbs_eq.1
    unfold timer.fire_loop.body
    dsimp only
    split
    · rename_i hi
      have hi32 : i1.val < 32 := by simpa using hi
      step with P1.LawfulStore.cur_cpu_spec as ⟨c, ec⟩
      step with P1.obj.node_get.spec as ⟨t, et⟩
      step with P1.obj.Tcb.is_null.spec as ⟨b, eb⟩
      split
      · exact (WP.spec_ok _).2 h1
      rename_i hb
      have ht0 : t ≠ 0#u64 := fun e => hb (by rw [eb, e]; rfl)
      obtain ⟨⟨Q1, R1, h1q⟩, -, hX1, -, -⟩ := id J1.blk
      have hTm1 := hX1.2.2.tm
      have htT : t ∈ P1.Heap.tcbs H := by
        have := hTm1.min _ h1q.cur
        rw [← ec] at this; rw [← et] at this
        rcases this with e | e
        · exact absurd e ht0
        · exact e
      step with P1.obj.Tcb.timer_deadline.val as ⟨d, ed⟩
      split
      · exact (WP.spec_ok _).2 h1
      step with P1.obj.Tcb.timer_badge.val as ⟨bd, ebd⟩
      have hI1 := P1.BlkOK.tinv J1.blk
      refine WP.spec_bind (WP.spec_and (P1.timer.remove.tf (s0 := s1) s1 t (P1.TF.start hI1) htT)
        (P1.timer.remove.rb s1 t hI1.tcbs htT hI1.rb hI1.nodes)) ?_
      rintro s2 ⟨⟨h2, -, -, -, hw2⟩, -, -, -, hrb2⟩
      -- a dead (unarmed) TCB stays unarmed
      have hTd2 : ∀ q ∈ D1, H q = some .tcb → L.mem s1 (P1.tdA q) = 0#u64 → L.mem s2 (P1.tdA q) = 0#u64 :=
        fun q _ hH h0 => remove_td hI1.tcbs hI1.nodes hrb2 (show q ∈ P1.Heap.tcbs H from hH) h0
      -- `timer::remove` keeps `JAtZ` and the spec state
      have hw2' : P1.WritesIn st s1 s2 (TmW (L := L) Z.T Cs Z.c s1) :=
        hw2.mono fun b hb => Or.inl (by rw [hTe]; exact hb)
      have hR2 : L.mem s2 (L.nodeAt s1 Z.c layout.node.REPROGRAM) = L.mem s1 (L.nodeAt s1 Z.c layout.node.REPROGRAM) := by
        obtain ⟨Q, R0, hc, -⟩ := J1.xtop.fin.1.1.1.lists
        have hcC : Z.c ∈ Cs := by have := J1.kern.cpuCs; rw [hc.cur] at this; exact this
        have hN : P1.NodePlaced st Z.T s1 Z.c := by rw [hTe]; exact P1.TInv.nodes J1.blk Z.c hcC
        refine hw2.mem_eq (P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
          fun hb => ?_
        have hb' : P1.TW st Z.T Cs s1 (L.nodeAt s1 Z.c layout.node.REPROGRAM) := by rw [hTe]; exact hb
        have hv := P1.nodeAt_val hN (off := layout.node.REPROGRAM) (by simp [layout.node.REPROGRAM])
        have h56 : layout.node.REPROGRAM.val = 56 := by simp [layout.node.REPROGRAM]
        rcases J1.tw_word hb' with ⟨y, hy, g1, g2⟩ | ⟨c', hc', o, ho, e⟩
        · have := J1.kern.hnd y _ (J1.zH.1 y hy) Z.c hcC
          simp only [P1.HKind.bits] at this; omega
        · have hnb : ∀ c, L.nodeBase s1 c = (L.ksb s1).val + 13568 + c.val * 4288 := fun _ => rfl
          simp only [hnb] at hv e
          by_cases hcc : c' = Z.c
          · subst hcc; omega
          · have : c'.val ≠ Z.c.val := fun h => hcc (UScalar.eq_of_val_eq h)
            rcases Nat.lt_or_gt_of_ne this with h | h
            · have : c'.val * 4288 + 4288 ≤ Z.c.val * 4288 := by nlinarith
              omega
            · have : Z.c.val * 4288 + 4288 ≤ c'.val * 4288 := by nlinarith
              omega
      obtain ⟨r2, J2⟩ := J1.tmw_step hw2' (Or.inl hR2) h2 hTd2
      have e2 : (σ1.reprogramTimer || r2) = σ1.reprogramTimer := by
        have g1 : (σ1.reprogramTimer || r2) = decide (Sched.nodeW st s2 Z.c layout.node.REPROGRAM ≠ 0#u64) :=
          J2.xtop.fin.1.1.1.repr
        have g0 : σ1.reprogramTimer = decide (Sched.nodeW st s1 Z.c layout.node.REPROGRAM ≠ 0#u64) :=
          J1.xtop.fin.1.1.1.repr
        rw [g1, g0]; unfold Sched.nodeW
        rw [P1.nodeAt_of_ksb hw2.1, hR2]
      rw [e2] at J2
      have J2' : JAtZB (L := L) arI AR (Z.mv Z.G V1) H Cs Ac1 Lst1 D1 s2 a1 σ1 := J2
      step with P1.obj.Tcb.bound_ntfn.val as ⟨n, en⟩
      refine WP.spec_bind (Pₘ := fun r : S × A => ∃ (σ2 : Fl4Spec.State Unit) (V2 : XVs) (Ac2 : Set U64)
          (Lst2 : U64 → List U64) (D2 : Set U64), (σ2 = σ1 ∨ Signal σ1 σ2) ∧ σ2.domainTime = σ1.domainTime ∧
          JAtZB (L := L) arI AR (Z.mv Z.G V2) H Cs Ac2 Lst2 D2 r.1 r.2 σ2) ?_ ?_
      · split
        · rename_i hn0
          have hn0' : L.mem s2 (P1.boundA t) ≠ 0#u64 := by rw [← en]; exact P1.bne_ne hn0
          have hnH : n ∈ P1.Heap.ntfns H := by rw [en]; exact h2.2.2.1.2.2.bnd t htT hn0'
          have hnN : n ∈ Z.N := J2'.hset.2.1 n hnH
          refine WP.spec_mono (hSig _ _ _ _ _ _ _ n bd J2' hnN) ?_
          rintro r ⟨σ2, V2, Ac2, Lst2, D2, hss, hd2, J3⟩
          exact ⟨σ2, V2, Ac2, Lst2, D2, Or.inr ⟨n.bv, bd.bv, hss⟩, hd2, J3⟩
        · exact (WP.spec_ok _).2 ⟨σ1, V1, Ac1, Lst1, D1, Or.inl rfl, rfl, J2'⟩
      rintro ⟨s3, a3⟩ ⟨σ2, V2, Ac2, Lst2, D2, hsig, hd2, J3⟩
      try simp only at J3
      try simp only [WP.uncurry'_pair]
      step with P1.LawfulStore.cur_cpu_spec as ⟨c3, ec3⟩
      step with P1.obj.node_set.spec as ⟨s4, es4⟩
      step as ⟨i4, ei4⟩
      try simp only [WP.spec_ok]
      subst es4 ec3
      refine ⟨⟨{ σ2 with reprogramTimer := true }, V2, Ac2, Lst2, D2,
        Relation.ReflTransGen.tail hF1 ⟨σ2, hsig, rfl⟩, (hd2.trans hd1 : σ2.domainTime = σ.domainTime),
        J3.reprogramJ⟩, by omega⟩
    · exact (WP.spec_ok _).2 h1
  · exact h


end

-- from Fl4Proofs/P3/ScFireJ.lean
section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 4000000 in
/-- **`JAtZ` across FL4's TCB timers** (module docstring). -/
theorem JAtZB.fireJ (hSig : SignalJHypB (L := L) arI AR H Cs) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    timer.fire st arI s a ⦃ r => FireInvB (L := L) (arI := arI) AR Z H Cs σ r.1 r.2 ⦄ := by
  unfold timer.fire
  refine WP.spec_bind (L.cur_cpu_spec s) fun c _ => ?_
  refine WP.spec_bind (P1.obj.node_get.spec s c _) fun now _ => ?_
  exact fire_loopJB hSig s a now 0#u64 ⟨σ, Z.vs, Ac, Lst, D, Relation.ReflTransGen.refl, rfl, J⟩

end


end

end

end Fl4Proofs.P3
