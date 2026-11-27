/-
P3 (line mmuAD, gen 28): **the binding steps at `JAtZV2`** (gen 27's "Next" item 1).

* **`XTopAt.tcbWrK`** (P3/XTopTcbFpu's `XTopAt.tcbWrF`, proof verbatim, the offset range widened by 3664) and
  **`XTopAt.tvcpuWr`**: FL4's write of a TCB's VCPU word `tVcpuA t` (offset 3664, read by none of `XTopAt`'s
  relations: not a `SchedRel` field, not `EFoot` / `NFoot`, not a slot) keeps `XTopAt`, the spec state kept.
* **`JAtZB.tvcpuWrJ`**: the same write keeps `JAtZB` (σ unchanged). Pattern of P3/JAtZBWr's `frameWrJ`, with the
  word's facts from its TCB: slots by `TopPlaced.disj` (the word is an `OObj` TCB word past 256), the other TCB
  fields by offset / `tcb_disj`, SC / reply words by `HeapOK.disj`, the untyped free regions by `UtCapP3.free`,
  P1's `BlkOK` by `P1.plainW_all` (offset 3664 is read by no P1 invariant), the debug words by `kw_field` +
  `JAtZB.kw_dbg` / `kw_dbgKeep`, the IRQ node by `ksOut`.
* **`JAtZV.linkWr`**: FL4's two link writes (`v.TCB := x`, then `t.VCPU := y`, for `t` a typed-heap TCB and
  `v ∈ V`) keep `JAtZB` (`JAtZB.vcpuWrJ` — gen 24's copy covers every VCPU word, the `TCB` word included —
  then `tvcpuWrJ`), `VList` (neither word is a list word: the head is not `JW`, NEXT/PREV are other offsets /
  other objects by `JVLay.vv` / `vap`) and `JVm`; `JExtV` / `RunVmB` at the post-state are arguments.
* **`JAtZV2.bind`** (no premise): an unbound typed-heap TCB `t` (`t.VCPU = 0`) and an unbound VCPU `v ∈ V`
  (`v.TCB = 0`); FL4 writes `v.TCB := t`, `t.VCPU := v` (vcpu.rs l. 859-860, `X86VCPUSetTCB` after its two
  detaches), the spec replaces `v`'s VCPU object by any `vs'` with `vs'.tcb = some t` (the last step of
  `associateVcpuTcb`, `vcpuUpdate v (tcb := some t)`): `JAtZV2` kept. `JExtV` by gen 20's `JExtV.bind_w`,
  `RunVmB` by `RunVmB.of_foot` (the new VCPU word is `v ≠ 0`), the spec side by gen 27's `JAtZV.vcpuSpec'`,
  `VBind` by gen 26's `VBind.set` (`t ≠ 0`: `DetPl.h0`).
* **`JAtZV2.unbind`**: a bound pair `t ↔ v` whose thread's state word is not 8 (`TS_RUNNING_VM`); FL4 writes
  `v.TCB := 0`, `t.VCPU := 0` (vcpu.rs l. 733-734), the spec sets `v`'s `tcb := none` (`vcpuDetach`'s last step):
  `JAtZV2` kept. The state-word condition is the statement's scope, not a gap: `vcpu::detach` / `vcpuDetach`
  first `report` a `TS_RUNNING_VM` thread (which sets `TS_RUNNING`), and the unbind is false without it (a
  `TS_RUNNING_VM` thread with VCPU word 0 breaks `RunVmB`).

What is **not** proved: the extracted `vcpu::detach` / `X86VCPUSetTCB` bodies end to end at `JAtZV2`. Around
the two link writes they also run `vcpu::stall` (current core's `IPI_PENDING` node word, VCPU `PENDING`), the
`report` branch (thread state, message registers, IPC buffer, `SCHED_ACTION`: a thread-state step, scheduler
family) and the `SVM_CPU` write (a non-link VCPU word: gen 27's `JAtZV2.vcpuWr` covers it). Their `JAtZB`
frames (node words, `report`'s spec step `vmReport`) are not built; the spec ops `associateVcpuTcb` /
`vcpuDetach` are related to `updK` only through their last `vcpuUpdate` (no `vcpuUpdate` outcome lemma: the
extended spec modules `Fl4Spec.Ext.Virt*` are not in the proof build's import closure).

No named premise. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZBSched
import Fl4Proofs.P3.JAtZBVcpuX
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Ipc Fl4Proofs.P3.Endp

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type}

set_option maxHeartbeats 4000000 in
/-- **A TCB word at offset `Kv` read by no relation, written** (`XTopAt.tcbWrF`'s proof verbatim with the offset
range widened by the VCPU word, offset 3664: none of `SchedRel`'s fields, `EFoot`, `NFoot`, the slots). -/
theorem XTopAt.tcbWrK {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) (wa : U64) (Kv : Nat)
    (hKw : (512 ≤ Kv ∧ Kv < 3208 ∧ Kv % 8 = 0) ∨ Kv = 3664) (hwav : wa.val = t.val + Kv)
    (v : U64) :
    XTopAt (L := L) AR Z (L.wr s (wa) v) a σ := by
  have hSch := hX.fin.1.1.1
  obtain ⟨Q, R0, hc, hs⟩ := hSch.lists
  have hT := hc.tcbs
  have hta := hT t ht
  have hP := hX.fin.1.2
  have hPe := hP.ep
  have hkf : (L.ksb s).val + 13568 ≤ 2 ^ 64 := by have := hP.vs.ksb_fit; omega
  have hka := hP.vs.ksb_al
  have hko := hc.ksOut t ht
  have hwv : wa.val = t.val + Kv := hwav
  have hwa : P1.Aligned (wa) := by unfold P1.Aligned; rw [hwv]; have := hta.align; omega
  have hw : P1.WritesIn st s (L.wr s (wa) v) (· = wa) := P1.writesIn_wr hwa
  have hne : ∀ b : U64, P1.Aligned b → b.val ≠ t.val + Kv →
      L.mem (L.wr s (wa) v) b = L.mem s b := fun b hb hbv =>
    hw.mem_eq hb fun e => hbv (by rw [e, hwv])
  -- the scheduler relation
  have hN := hc.node
  have hnd := hN.disj t ht
  have hSA : Sched.SAgree st Z.T Z.C Z.c s (L.wr s (wa) v) := by
    refine ⟨hw.1, hw.2.1, fun o ho h8 _ _ _ _ _ => hne _ (P1.nodeAt_aligned hN ho h8) ?_, fun y hy K hK => ?_,
      hne _ ?_ ?_, hne _ ?_ ?_, fun sc hsc b hb hin => hne _ hb ?_⟩
    · rw [P1.nodeAt_val hN ho]; omega
    · obtain ⟨h1, h2, -⟩ := Sched.schedField_ok hK
      refine hne _ (P1.field_aligned (hT y hy) h1 h2) ?_
      rw [Notif.tfield_val (hT y hy) h1]
      by_cases e : y = t
      · subst e; rcases hK with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega
      · have := tcb_disj hPe ht hy e; omega
    · unfold Sched.curDomA; unfold P1.Aligned
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.curDomA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.dtA; unfold P1.Aligned
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · unfold Sched.dtA
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    · have := (hSch.scOutIn hsc hin).2.2.1 t ht; omega
  have hSch' : Sched.SchedRel st Z.N Z.T Z.C Z.c (L.wr s (wa) v) σ := by
    refine hSch.of_sagree hSA ?_ ?_ ⟨rfl, rfl, fun _ => Or.inl rfl⟩
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hne _ (P1.nodeAt_aligned hN (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
        (by rw [P1.nodeAt_val hN (by simp [layout.node.SCHED_ACTION])]; simp only [layout.node.SCHED_ACTION]; simp; omega)
    · unfold Sched.nodeW; rw [Sched.nodeAt_ksb hw.1]
      exact hne _ (P1.nodeAt_aligned hN (by simp [layout.node.REPROGRAM]) (by simp [layout.node.REPROGRAM]))
        (by rw [P1.nodeAt_val hN (by simp [layout.node.REPROGRAM])]; simp only [layout.node.REPROGRAM]; simp; omega)
  refine hX.frameStep hw (fun b hb => by subst hb; exact Or.inr (Or.inr (Or.inl ⟨t, ht, by omega, by omega⟩)))
    (fun b hb hf => ?_) (fun b hb hf => ?_) (fun hb => ?_) (fun hb => ?_) rfl rfl rfl rfl rfl rfl rfl rfl hSch' ?_ ?_ ?_
    hX.fin.1.1.2.2.2.2.2.2
  · -- not read by the endpoint relation
    subst hb
    rcases hf with ⟨e, he, h⟩ | ⟨r, hr, h⟩ | ⟨y, hy, h | h⟩ | ⟨wp, hwp, h⟩
    · have := hPe.et e he t ht; omega
    · have := hPe.rt r hr t ht; omega
    · obtain ⟨h1, h2⟩ := h
      unfold Endp.TOffN at h2
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
    · unfold Endp.TL at h
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
    · have := hPe.bt wp hwp t ht; rw [← h] at this; omega
  · -- not read by the notification relation
    subst hb
    rcases hf with ⟨n, hn, h1, h2⟩ | ⟨y, hy, h⟩
    · have := hSch.placed.disj n hn t ht; omega
    · have hv := nfootT_val (hT y hy) h
      by_cases e : y = t
      · subst e; omega
      · have := tcb_disj hPe ht hy e; omega
  · -- not the kernel root
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.KERNEL_ROOT).val = (L.ksb s).val + 48 := by
      unfold layout.ks.KERNEL_ROOT
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := congrArg UScalar.val hb
    rw [hkv, hwv] at this; omega
  · -- not the FEATURES word (#65)
    have hkv : (core.num.U64.wrapping_add (L.ksb s) layout.ks.FEATURES).val = (L.ksb s).val + 72 := by
      unfold layout.ks.FEATURES
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    have := congrArg UScalar.val hb
    rw [hkv, hwv] at this; omega
  · -- the IRQ relation
    have hI := hX.fin.1.1.2.2.2.1
    refine ⟨fun i hi => ?_, fun i hi => hI.node i hi⟩
    have hv := irqStA_val hkf hi
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)]
    exact hI.st i hi
  · -- the IO-port relation
    have hI := hX.fin.1.1.2.2.2.2.1
    intro p hp
    have hwi : (wI p).val < 1024 := by rw [wI_val hp]; omega
    have hv := ioA_val hkf hwi
    unfold bitOf
    rw [hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)]
    exact hI p hp
  · -- the domain schedule
    refine hX.rel.2.2.2.1.frame (fun o ho => ?_) rfl rfl
    have h8 := domOffs_lt' ho
    have hv := ksW_val (kb := L.ksb s) (o := o) (by omega)
    exact hne _ (by unfold P1.Aligned; rw [hv]; omega) (by rw [hv]; omega)

/-- **A TCB's VCPU word written** (`tVcpuA t`, offset 3664) keeps `XTopAt`, the spec state kept. -/
theorem XTopAt.tvcpuWr {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (hX : XTopAt (L := L) AR Z s a σ) {t : U64} (ht : t ∈ Z.T) (v : U64) :
    XTopAt (L := L) AR Z (L.wr s (tVcpuA t) v) a σ := by
  obtain ⟨Q, R0, hc, -⟩ := hX.fin.1.1.1.lists
  exact hX.tcbWrK ht _ 3664 (Or.inr rfl) (Sched.tVcpuA_val hc.tcbs ht) v

end

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 16000000 in
/-- **A TCB's VCPU word written at `JAtZB`** (module docstring; the spec state kept). -/
theorem JAtZB.tvcpuWrJ (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) (v : U64) :
    JAtZB (L := L) arI AR Z H Cs Ac Lst D (L.wr s (tVcpuA t) v) a σ := by
  set s1 := L.wr s (tVcpuA t) v with hs1
  have F : ArFr σ σ := ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP := J.xtop.fin.1.2
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  have hal : P1.Aligned (tVcpuA t) := Sched.tVcpuA_aligned hT ht
  have hwv : (tVcpuA t).val = t.val + 3664 := Sched.tVcpuA_val hT ht
  have hW : P1.WritesIn st s s1 (· = tVcpuA t) := P1.writesIn_wr hal
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  have hO : OObj st Z.N Z.T Z.C Z.E Z.R Z.B Z.c s σ (tVcpuA t) :=
    Or.inr (Or.inr (Or.inl ⟨t, ht, by omega, by omega⟩))
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_of_vobj hP.pl fun b hb hv => hW.mem_eq hb fun e => hP.disj b (by rw [e]; exact hO) hv
  have hX1 : XTopAt (L := L) AR Z s1 a σ := J.xtop.tvcpuWr ht v
  -- the frame words
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have htH : H t = some .tcb := J.zH.1 t ht
  have objK : ∀ p k, H p = some k → k ≠ .tcb → ∀ w' : U64, P1.Aligned w' → p.val ≤ w'.val →
      w'.val < p.val + 2 ^ k.bits → L.mem s1 w' = L.mem s w' := by
    intro p k hp hk w' hal' g1 g2
    have hne : t ≠ p := fun e => by subst e; rw [htH] at hp; exact hk (Option.some.inj hp).symm
    refine hW.mem_eq hal' fun hb => ?_
    rw [hb, hwv] at g1 g2
    have d := hHk.disj t _ p k htH hp hne
    have e12 : (2 : Nat) ^ P1.HKind.bits .tcb = 4096 := by simp [P1.HKind.bits]
    rw [e12] at d
    omega
  have tcbK : ∀ y ∈ Z.T, ∀ w' : U64, P1.Aligned w' → y.val ≤ w'.val → w'.val < y.val + 4096 →
      w'.val ≠ y.val + 3664 → L.mem s1 w' = L.mem s w' := by
    intro y hy w' hal' g1 g2 g3
    refine hW.mem_eq hal' fun hb => ?_
    rw [hb, hwv] at g1 g2 g3
    by_cases e : y = t
    · subst e; exact g3 rfl
    · have := tcb_disj hP.ep ht hy e; omega
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) ∧ L.mem s1 (flagsA t) = L.mem s (flagsA t) := fun t ht =>
    ⟨tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
        (by rw [mcpA_val hT ht]; omega),
      tcbK t ht _ (flagsA_aligned hT ht) (by rw [flagsA_val hT ht]; omega) (by rw [flagsA_val hT ht]; omega)
        (by rw [flagsA_val hT ht]; omega)⟩
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
      (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega) (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w' : U64, P1.Aligned w' → q.val ≤ w'.val → w'.val < q.val + 2 ^ z →
      L.mem s1 w' = L.mem s w' := fun q z hq w' hal' g1 g2 =>
    objK q _ hq (fun e => by cases e) w' hal' g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s1 (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s1 (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s1 (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal' := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s1 a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal')), k _ (Or.inr (rNextA_val hal'))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s1 (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal' := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal' hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal']
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- P1's `BlkOK` and the kernel footprint (`plainW_all`: offset 3664 is read by no P1 invariant)
  obtain ⟨hblk, -, -⟩ := P1.plainW_all (K := 3664#u64) (v := v) J.blk htH (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp)
  have hfoot : P1.WritesIn st s s1 (P1.KW st (P1.Heap.tcbs H) Cs (P1.Heap.frame H) (P1.Heap.scs H)
      (P1.Heap.scBits H) (P1.EH H) s) := hW.mono fun b hb => by
    rw [hb]; exact P1.kw_field (K := 3664#u64) (Es := P1.EH H) htH (by simp) (by simp) (by simp)
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := J.kw_dbg hfoot
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s1 := J.kw_dbgKeep hfoot
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      have ko := hcq.ksOut t ht
      simp only [Nat.reducePow] at ko
      rw [hb, hwv]; omega
  -- the dead stay dead
  have hAI : ActIdle σ := J.act.ar F
  have yk : YKeep σ σ := ⟨fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩,
    fun p x n hp => ⟨x, F.sc.2 hp, rfl⟩, fun p y n hp => ⟨y, F.sc.1 hp, rfl⟩⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s1 q := fun q hq =>
    J.deadP_keep hX1.fin.1.1.1 hX1.ipc
      (fun x hx _ => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl, rfl, Or.inl rfl⟩)
      (fun x hx => (F.look (fun _ e => by cases e)).2 hx)
      (fun x hx => ⟨x, F.ntfn.2 hx, Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, (F.look (fun _ e => by cases e)).2 hx, rfl⟩)
      (fun x n hx => ⟨x, F.sc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q) (fun z hz _ => hOut q z hz) F.idle hAI.1
      (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- the untyped caps' facts
  have hutc : ∀ sl p sb fi dev, AbsSlot Z.th sl → capAt (L.mem s1) (cslotAddr sl) = ok (.Untyped p sb fi dev) → dev = false →
      Sched.UtCapP3 (L := L) arI Z.th s1 σ Z.G sl p sb fi := by
    intro sl p sb fi dev hsl hcap hdv
    have hna : ∀ c o, L.nodeAt s1 c o = L.nodeAt s c o := P1.nodeAt_of_ksb hkb
    obtain ⟨-, ⟨-, -, hM, -, -⟩, -⟩ := J.xtop.rel
    have hcv : capV (L.mem s) (cslotAddr sl) = .Untyped p sb fi dev := by
      rw [← hSS.capV hsl.isSlot]; exact capV_of_capAt hcap
    have hcap0 : capAt (L.mem s) (cslotAddr sl) = ok (.Untyped p sb fi dev) := by rw [capAt_capV, hcv]
    have U := J.utc sl p sb fi dev hsl hcap0 hdv
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_,
      U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0),
      ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [F.gpml4]; exact U.gReg (B g)⟩
    · intro g w' hal' h1 h2
      rw [hW.mem_eq hal' fun hb => ?_]
      · exact U.zero (B g) w' hal' h1 h2
      rw [hb, hwv] at h1 h2
      have hth : Z.th t = some .tcb := (hJ.tcb t).2 htH
      have := U.free t .tcb hth
      simp only [objSize] at this; omega
    · intro g h0 hf0
      rw [F.cdt] at h0
      obtain ⟨r1, r3⟩ := U.rst (B g) h0 hf0
      exact ⟨fun sl' h => r1 sl' (by rw [← F.orig]; exact h), by rw [hna, hDbg]; exact r3⟩
  -- the spec's frames
  have ck : Sched.CKeep σ σ := ⟨fun q y n hq => ⟨y, F.sc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (F.look (fun _ e => by cases e)).2 hq, rfl, rfl⟩, fun p x n hp => ⟨x, F.sc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 F.khrb
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s1 σ :=
    ⟨Tr, Cq, hJ.same hSS (fun q y n _ hq => F.szKeep q.bv y n hq) hkb hirq (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc).2⟩
  have hkern := J.kern_keepA hkb hcpu hX1.fin.1.1.1 F hDbg
  have hTd : Sched.TdKeep (L := L) H s s1 := fun q hq =>
    tcbK q (J.tcbZ hq) _ (P1.field_aligned (J.ip.e.tcb q (J.tcbZ hq)) (K := 3528#u64) (by simp) (by simp))
      (by rw [J.tdA_val' (J.tcbZ hq)]; omega) (by rw [J.tdA_val' (J.tcbZ hq)]; omega)
      (by rw [J.tdA_val' (J.tcbZ hq)]; omega)
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s1 σ :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, J.jcov_keep hkb hSS hdead (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc) (DXKeep.of_dbg hKd hTd), hkern,
      hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F, J.own.ar F,
      J.off.ar F, hAI, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, hblk⟩
  exact J.cs_frameK (hvn := J.vsSS (G' := Z.G) hX1 hkb hSS (Vs.ArchShr.refl _)) hkb hX1 F.kback F.ipcFr (J.carry.frame subset_rfl F.ipcFr F.ksz) (JCs.sameB J hSS F.ksz) R (Vs.VsSlotsT.of_eq fun y hy => hSS.capV hy)
    hSS hKd F.idle

end

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical

/-- The two link words' writes (`VCPU.TCB := x`, then `t.VCPU := y`) as one footprint. -/
theorem link_writes {v t x y : U64} (hv : P1.Aligned (vTcbA v)) (ht : P1.Aligned (tVcpuA t)) :
    P1.WritesIn st s (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y) (fun b => b = vTcbA v ∨ b = tVcpuA t) :=
  (P1.writesIn_wr hv).trans (P1.writesIn_wr ht)

set_option maxHeartbeats 8000000 in
/-- **The link words written at `JAtZV`**: FL4's writes of a VCPU's `TCB` word and a TCB's VCPU word keep
`JAtZB` (`JAtZB.vcpuWrJ`, `JAtZB.tvcpuWrJ`), `VList` (neither is a list word) and `JVm`; the extension's two
remaining parts (`JExtV`, `RunVmB`), which do read these words, are given at the post-state. -/
theorem JAtZV.linkWr (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t v : U64}
    (ht : Z.th t = some .tcb) (hv : v ∈ V) (x y : U64)
    (E' : JExtV (L := L) V X Z.th (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y))
    (R' : RunVmB (L := L) Z.th (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y)) :
    JAtZV (L := L) arI V X AR Z H Cs Ac Lst D (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y) a σ := by
  have B := J.base
  have Ly := B.jvLay J.vm
  have hf := Ly.vfit v hv
  have hvt := lay_vTcb_val hf.2
  have halv : P1.Aligned (vTcbA v) := by unfold P1.Aligned; rw [hvt]; omega
  have hta := Ly.tA t ht
  have htv := lay_tVcpu_val hta
  have halt : P1.Aligned (tVcpuA t) := by unfold P1.Aligned; rw [htv]; have := hta.align; omega
  -- no IPC-buffer word lies in the VCPU
  have hnB : ∀ wp ∈ Z.B, wp.1 ≠ vTcbA v := by
    intro wp hwp e
    obtain ⟨q, vms, hq, q1, q2⟩ := B.carry.bufPg wp hwp
    obtain ⟨y', hy⟩ := J.vm.spec v hv
    have hne : q ≠ v.bv := fun e' => by rw [e', hy] at hq; cases hq
    have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
      simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
    have ev : wp.1.val = (vTcbA v).val := by rw [e]
    rcases J.vm.sep v hv q _ hq hne with e1 | e1
    · rw [eb] at e1; omega
    · omega
  have B1 := B.vcpuWrJ (J.vm.spec v hv) (J.vm.heap v hv) (J.vm.ks v hv) halv (by omega) (by omega) hnB x
  have B2 := B1.tvcpuWrJ (B.thT t ht) y
  have hW := link_writes (st := st) (s := s) (x := x) (y := y) halv halt
  have Vl' : VList st V Z.th (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y) := J.vl.writes hW fun b hb => by
    refine ⟨J.vl.lw_al Ly.vfit hb, ?_⟩
    rintro (e | e) <;> subst e
    · rcases hb with e | ⟨u, hu, e | e⟩
      · exact J.vl.hd.2.1 (by rw [← e]; exact Or.inr (Or.inr ⟨v, hv, rfl⟩))
      · have ew := congrArg UScalar.val e
        rw [hvt, lay_next_val (Ly.vfit u hu).2] at ew
        by_cases hu' : u = v
        · subst hu'; omega
        · rcases Ly.vv u hu v hv hu' with h | h <;> omega
      · have ew := congrArg UScalar.val e
        rw [hvt, lay_prev_val (Ly.vfit u hu).2] at ew
        by_cases hu' : u = v
        · subst hu'; omega
        · rcases Ly.vv u hu v hv hu' with h | h <;> omega
    · rcases hb with e | ⟨u, hu, e | e⟩
      · exact J.vl.hd.2.1 (by rw [← e]; exact Or.inr (Or.inl ⟨t, ht, rfl⟩))
      · have ew := congrArg UScalar.val e
        rw [htv, lay_next_val (Ly.vfit u hu).2] at ew
        have d := Ly.vap u hu t _ ht
        simp only [objSize] at d
        omega
      · have ew := congrArg UScalar.val e
        rw [htv, lay_prev_val (Ly.vfit u hu).2] at ew
        have d := Ly.vap u hu t _ ht
        simp only [objSize] at d
        omega
  have Jv' : JVm (L := L) V H (L.wr (L.wr s (vTcbA v) x) (tVcpuA t) y) σ :=
    ⟨J.vm.spec, J.vm.heap, fun v hv => by rw [hW.1]; exact J.vm.ks v hv, J.vm.sep⟩
  exact ⟨B2, E', R', Jv', Vl'⟩

set_option maxHeartbeats 8000000 in
/-- **Binding at `JAtZV2`** (module docstring): an unbound TCB `t` of the typed heap and an unbound VCPU `v ∈ V`;
FL4 writes `v.TCB := t` then `t.VCPU := v` (vcpu.rs l. 859-860), the spec replaces `v`'s VCPU object by one with
`tcb = some t` (`associateVcpuTcb`'s last step, `vcpuUpdate v (tcb := some t)`). No premise. -/
theorem JAtZV2.bind (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t v : U64}
    (ht : Z.th t = some .tcb) (hv : v ∈ V) (hw0 : L.mem s (tVcpuA t) = 0#u64) (hb0 : L.mem s (vTcbA v) = 0#u64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap v.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (htcb : Fl4Spec.VcpuState.tcb vs' = some t.bv) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr (L.wr s (vTcbA v) t) (tVcpuA t) v) a
      (Notif.updK σ v.bv (.archObj (.vcpu vs'))) := by
  have Jz := J.zv
  have P := Jz.base.jwPl Jz.vm
  have h0 : Z.th 0#u64 ≠ some .tcb := (Jz.base.detPl Jz.vm).h0
  have halv : P1.Aligned (vTcbA v) := P.jw _ (Or.inr (Or.inr ⟨v, hv, rfl⟩))
  have halt : P1.Aligned (tVcpuA t) := P.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))
  have hW := link_writes (st := st) (s := s) (x := t) (y := v) halv halt
  have hne : tVcpuA t ≠ vTcbA v := P.vb t ht v hv
  have h1 : L.mem (L.wr (L.wr s (vTcbA v) t) (tVcpuA t) v) (tVcpuA t) = v := L.mem_wr_same halt
  have h2 : L.mem (L.wr (L.wr s (vTcbA v) t) (tVcpuA t) v) (vTcbA v) = t := by
    rw [L.mem_wr_ne halt halv (fun e => hne (UScalar.eq_of_val_eq e)), L.mem_wr_same halv]
  have E' := Jz.extv.bind_w P ht hv hw0 hb0 h0 hW h1 h2
  have R' : RunVmB (L := L) Z.th (L.wr (L.wr s (vTcbA v) t) (tVcpuA t) v) := by
    refine Jz.rvm.of_foot P hW (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)
    · exfalso
      exact P.swjw _ ⟨t', ht', rfl⟩ (by
        rcases hw with e | e
        · rw [e]; exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
        · rw [e]; exact Or.inr (Or.inl ⟨t, ht, rfl⟩))
    · right
      rcases hw with e | e
      · exact absurd e (P.vb t' ht' v hv)
      · rw [tVcpuA_inj e, h1]; exact Jz.extv.nz v hv
  have Z0 := Jz.linkWr ht hv t v E' R'
  have ht0 : t ≠ 0#u64 := fun e => h0 (by rw [← e]; exact ht)
  refine ⟨Z0.vcpuSpec' hv hk vs', J.vb.set vs' (fun w hw hwv => ?_) (Or.inr ⟨t, ht0, htcb, h2⟩)⟩
  exact hW.mem_eq (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩))) (by
    rintro (e | e)
    · exact hwv (vTcbA_inj e)
    · exact P.vb t ht w hw e.symm)

set_option maxHeartbeats 8000000 in
/-- **Unbinding at `JAtZV2`** (module docstring): a bound pair `t ↔ v` (`t.VCPU = v`, `v.TCB = t`) whose thread is
not in `TS_RUNNING_VM` (the state word is not 8: `vcpu::detach` / `vcpuDetach` report a `TS_RUNNING_VM` thread
first, which leaves it `TS_RUNNING`); FL4 writes `v.TCB := 0` then `t.VCPU := 0` (vcpu.rs l. 733-734), the spec
replaces `v`'s VCPU object by one with `tcb = none` (`vcpuDetach`'s last step). No premise beyond the
statement's scope (`hst`). -/
theorem JAtZV2.unbind (J : JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t v : U64}
    (ht : Z.th t = some .tcb) (hv : v ∈ V) (htv : L.mem s (tVcpuA t) = v) (hvt : L.mem s (vTcbA v) = t)
    (hst : L.mem s (P1.stA t) ≠ 8#u64)
    {vs : Fl4Spec.VcpuState} (hk : σ.kheap v.bv = some (.archObj (.vcpu vs))) (vs' : Fl4Spec.VcpuState)
    (htcb : Fl4Spec.VcpuState.tcb vs' = none) :
    JAtZV2 (L := L) arI V X AR Z H Cs Ac Lst D (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) a
      (Notif.updK σ v.bv (.archObj (.vcpu vs'))) := by
  have Jz := J.zv
  have P := Jz.base.jwPl Jz.vm
  have halv : P1.Aligned (vTcbA v) := P.jw _ (Or.inr (Or.inr ⟨v, hv, rfl⟩))
  have halt : P1.Aligned (tVcpuA t) := P.jw _ (Or.inr (Or.inl ⟨t, ht, rfl⟩))
  have hW := link_writes (st := st) (s := s) (x := 0#u64) (y := 0#u64) halv halt
  have hne : tVcpuA t ≠ vTcbA v := P.vb t ht v hv
  have h1 : L.mem (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (tVcpuA t) = 0#u64 := L.mem_wr_same halt
  have h2 : L.mem (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) (vTcbA v) = 0#u64 := by
    rw [L.mem_wr_ne halt halv (fun e => hne (UScalar.eq_of_val_eq e)), L.mem_wr_same halv]
  have E' := Jz.extv.unbind_w P ht hv htv hvt hW h1 h2
  have R' : RunVmB (L := L) Z.th (L.wr (L.wr s (vTcbA v) 0#u64) (tVcpuA t) 0#u64) := by
    refine Jz.rvm.of_foot P hW (fun t' ht' hw => ?_) (fun t' ht' hw => ?_)
    · exfalso
      exact P.swjw _ ⟨t', ht', rfl⟩ (by
        rcases hw with e | e
        · rw [e]; exact Or.inr (Or.inr ⟨v, hv, rfl⟩)
        · rw [e]; exact Or.inr (Or.inl ⟨t, ht, rfl⟩))
    · left
      rcases hw with e | e
      · exact absurd e (P.vb t' ht' v hv)
      · rw [tVcpuA_inj e]; exact hst
  have Z0 := Jz.linkWr ht hv 0#u64 0#u64 E' R'
  refine ⟨Z0.vcpuSpec' hv hk vs', J.vb.set vs' (fun w hw hwv => ?_) (Or.inl ⟨htcb, h2⟩)⟩
  exact hW.mem_eq (P.jw _ (Or.inr (Or.inr ⟨w, hw, rfl⟩))) (by
    rintro (e | e)
    · exact hwv (vTcbA_inj e)
    · exact P.vb t ht w hw e.symm)

end

end

end Fl4Proofs.P3
