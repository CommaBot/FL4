/-
P3 (line mmuAD, gen 39): **`JAtZ.vsStepJX` at `JAtZB`** — the base of the VM-epoch invariant across a step that
rewrites one CNode slot's two cap words with a cap of the same shape (P3/XTopJointVsMap's VSpace frame), for the
EnableIOPort `set_cap` (P3/JAtZV3SlotIo).

* Copies over `JAtZB` (names `JAtZB.<same name>`, statements and proofs verbatim with `J : JAtZ` read as
  `J : JAtZB`; none of them reads `JAtZ.ext`): `scOut`, `utFrom`, `sfree_keep`, `jcs_slot`, `mdbL`,
  `slotCapW`, `thOfTcb`, `tabNodeW`, `vsNodeWX`, `tabObjW`, `vsObjWX`, `vsW_alX`, `cslot_other`, `cslotW_val`, `cslotW_node`, `vsxNodeW`, `vsxNodeWX`,
  `cslotW_obj`, `vsxObjW`, `vsxObjWX`, `vsx_utcX` (from P3/JointAt, P3/DeadKeep, P3/XTopJointStep,
  P3/XTopJointFinVs, P3/XTopJointVsMap); **`LiveDN.simXB`** (P3/LiveFrame's `LiveDN.simX`).
  (Since mmuAD gen 42b3 `vsFr_node`, `vsNodeW`, `vobj_apart`, `vsFr_sc`, `vsObjW`, `vsW_al` are no longer copied
  here: P3/XTopJointFinVs states them over `JAtZB`, the `JAtZ` names as corollaries; likewise `utFrom`,
  `sfree_keep`, `jcs_slot`, `jcov_cover` (gen 42b4) (P3/DeadKeep), `slotCapW` (P3/JointAt) and `thOfTcb` (P3/XTopJointStep).)
* **`JAtZB.vsStepJXB`**: `JAtZ.vsStepJX` with `JAtZB` for `JAtZ` at both ends; the `JExt` part of the final
  `cs_frameV` (and its premise `hvf`, the VT-x flag of the new cap, which only fed `JExt.nat`) dropped, since
  `JAtZB.cs_frameV` has no `JExt` argument.

No named premise. No existing statement changed.

(mmuAD gen 42b17) Copies removed (the originals are now stated over `JAtZB` in place): P3/JointAt `mdbL`, `scOut`;
P3/XTopJointVsMap `cslotW_node`, `cslotW_obj`, `cslotW_val`, `cslot_other`, `tabNodeW`, `tabObjW`, `vsNodeWX`,
`vsObjWX`, `vsW_alX`, `vsxNodeW`, `vsxNodeWX`, `vsxObjW`, `vsxObjWX`, `vsx_utcX`.
-/
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.JAtZBWr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

set_option maxHeartbeats 4000000 in
/-- **`LiveDN` across a step changing slots only up to `LSim`, at `JAtZB`** (P3/LiveFrame's `LiveDN.simX`, proof verbatim) (a frame cap's
mapping, an untyped cap's free index; KENTRY-PLAN g2i): the debug words, the
original bits and the spec's idle thread kept, the TCB zombies' TCBs dead
after. -/
theorem LiveDN.simXB {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hLv : LiveDN (L := L) Z.th H Cs Z.G s σ)
    {Z' : XSets} {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (hX' : XTopAt (L := L) AR Z' s' a' σ')
    (hth : Z'.th = Z.th) (hT : Z'.T = Z.T) (hc : Z'.c = Z.c)
    (hdead : ∀ p ∈ ZTcb (L := L) Z.th s, Sched.DeadP (L := L) H s' p)
    (hid : σ'.idleThread = σ.idleThread) (hdk : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s')
    (horig : ∀ sl, σ'.isOriginalCap sl = true → σ.isOriginalCap sl = true)
    (hsim : ∀ y, IsSlot Z.th y → LSim (capV (L.mem s') y) (capV (L.mem s) y)) :
    LiveDN (L := L) Z.th H Cs Z'.G s' σ' ∧ ∀ p ∈ ZTcb (L := L) Z.th s', p ∈ ZTcb (L := L) Z.th s := by
  obtain ⟨hL, ⟨lst, hDW⟩, hN⟩ := hLv
  have hM := J.xtop.rel.2.1.2.2.1
  have hM' : MdbLinks Z.th (L.mem s') Z'.G := by rw [← hth]; exact hX'.rel.2.1.2.2.1
  have hks : L.ksb s' = L.ksb s := hdk.1
  have hmemS : ∀ y ∈ Z.G.chains.flatten, IsSlot Z.th y := fun y hy => ((hM.members y).1 hy).1
  have hmemN : ∀ y ∈ Z.G.chains.flatten, capV (L.mem s) y ≠ .Null := fun y hy => by
    obtain ⟨-, c0, h0, hn0⟩ := (hM.members y).1 hy
    rw [capV_of_capAt h0]; exact hn0
  have hinG' : ∀ y, IsSlot Z.th y → capV (L.mem s') y ≠ .Null → y ∈ Z'.G.chains.flatten := fun y hy hn =>
    (hM'.members y).2 ⟨hy, _, capAt_capV _ _, hn⟩
  have hU : ∀ y, IsSlot Z.th y → InUse (L.mem s') σ' y → InUse (L.mem s) σ y := by
    intro y hy hu
    rcases hu with hu | ⟨x, hx, ho⟩
    · exact Or.inl fun h => hu (((hsim y hy).1).2 h)
    · exact Or.inr ⟨x, hx, horig x ho⟩
  have hTz : P1.DbgTz st (P1.Heap.tcbs H) Cs s := ⟨J.blk.2.2.1.2.2.tm.dn, J.blk.2.2.1.2.2.tm.dp, J.blk.2.2.1.2.2.tm.dh⟩
  have hc0 : 0#u64 ∈ Cs := J.kern.cs0
  have hhd : dbgHead (L := L) s' = dbgHead (L := L) s := by
    unfold dbgHead
    rw [nodeAt_of_ksb hdk.1]
    exact hdk.2 _ (Or.inr ⟨0#u64, hc0, rfl⟩)
  have hNt : ∀ k, dbgNth (L.mem s') k (dbgHead (L := L) s') = dbgNth (L.mem s) k (dbgHead (L := L) s) :=
    fun k => by
      rw [hhd]
      exact dbgNth_keep (fun y hy => hdk.2 _ (Or.inl ⟨y, hy, Or.inl rfl⟩)) (fun y hy => hTz.dn y hy) k _
        (hTz.dh _ hc0)
  have hZ : ∀ y, IsSlot Z.th y → ∀ p zt n, capV (L.mem s') y = .Zombie p zt n → capV (L.mem s) y = .Zombie p zt n :=
    fun y hy p zt n h => ((hsim y hy).2.2.2 p zt n).1 h
  have hL' : LiveJ (L := L) Z.th H Z'.G s' σ' := by
    refine ⟨fun q i hqi hu => ?_, fun k hk hki => ?_, fun y hy p zt n hz i hpi hni hu => ?_,
      fun y hy p zt n hz hzt => ?_⟩
    · rcases hL.slots q i hqi (hU _ ⟨q, i, hqi, rfl⟩ hu) with ⟨y, hy, hr⟩ | hb
      · have hyS := hmemS y hy
        exact Or.inl ⟨y, hinG' y hyS (fun h => hmemN y hy (((hsim y hyS).1).1 h)), ((hsim y hyS).2.1 q).2 hr⟩
      · exact Or.inr (by rw [hks]; exact hb)
    · rw [hNt] at hk hki ⊢
      obtain ⟨y, hy, hr⟩ := hL.dbg k hk (by rw [← hid]; exact hki)
      have hyS := hmemS y hy
      exact ⟨y, hinG' y hyS (fun h => hmemN y hy (((hsim y hyS).1).1 h)), ((hsim y hyS).2.2.1 _).2 hr⟩
    · exact hL.zslots y hy p zt n (hZ y hy p zt n hz) i hpi hni (hU _ ⟨p, i, hpi, rfl⟩ hu)
    · exact hdead p ⟨y, hy, zt, n, hZ y hy p zt n hz, hzt⟩
  refine ⟨⟨hL', ⟨lst, ?_⟩, fun sl hA h => ?_⟩, fun p ⟨y, hy, zt, n, hz, h65⟩ => ⟨y, hy, zt, n, hZ y hy p zt n hz, h65⟩⟩
  · obtain ⟨Q0, R0, hc0', -⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨Q1, R1, hc1, -⟩ := hX'.fin.1.1.1.lists
    have hTe : Z.T = P1.Heap.tcbs H := J.tcbs_eq.1
    refine hDW.of_keep hdk fun y hy => ?_
    rw [hc1.aff y (by rw [hT, hTe]; exact hy), hc0'.aff y (by rw [hTe]; exact hy), hc]
  · cases ho : σ'.isOriginalCap sl
    · rfl
    · have h1 := horig sl ho
      rw [hN sl hA (((hsim _ hA.isSlot).1).1 h)] at h1
      cases h1


set_option maxHeartbeats 16000000 in
/-- **`JAtZB.vsStepJXB`: P3/XTopJointVsMap's `JAtZ.vsStepJX` at `JAtZB`** (proof verbatim, the `JExt` part and its `hvf` dropped). Its docstring: **`JAtZ` across a VSpace map, unmap or ASID assignment after the
restart** (module docstring): FL4 writes the VSpace words and the invoked
CNode slot's cap words (`VsXW`), that slot's cap of the same shape after and
no untyped cap, the other slots kept (`hcap`), the slots' MDB words kept
(`hl`); the spec steps by `VsSFr`; `XTopAt` after at the same sets. At the
same dead set and P1's sets. `vsStepJX`: also writing the frames `X` of
tables outside the sets (`TabsArch`: spec arch objects, so `other` objects
of `H`, apart from every other object, node and untyped free part), with
the table sets `L3'`, `L2'`, `L1'` after (`XTopAt` and the slots' placement there). -/
theorem JAtZB.vsStepJXB {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Ap : VsApart (L := L) Z H Cs s)
    {pc : U64} {r : Nat} {idx : List Bool} (hpc : Z.th pc = some (.cnode r)) (hidx : idx.length = r)
    {X : Set U64} (hXa : TabsArch X σ) {L3' L2' L1' : Set U64}
    {s' : S} {a' : A} {σ' : Fl4Spec.State Unit} (hX' : XTopAt (L := L) AR (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) s' a' σ') (F : VsSFr σ σ')
    (hW : P1.WritesIn st s s' (fun b => VsXW Z (L.ksb s) (cslotAddr (pc.bv, idx)) b ∨ PtW X b))
    (hcap : ∀ y, IsSlot Z.th y → y ≠ cslotAddr (pc.bv, idx) → capV (L.mem s') y = capV (L.mem s) y)
    (hsh : shape (capV (L.mem s') (cslotAddr (pc.bv, idx))) = shape (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hok : okey (capV (L.mem s') (cslotAddr (pc.bv, idx))) = okey (capV (L.mem s) (cslotAddr (pc.bv, idx))))
    (hnu : isUt (capV (L.mem s) (cslotAddr (pc.bv, idx))) = false)
    (hl : ∀ y, IsSlot Z.th y → L.mem s' (wordOf y 16#u64) = L.mem s (wordOf y 16#u64) ∧
      L.mem s' (wordOf y 24#u64) = L.mem s (wordOf y 24#u64))
    (hvc : Vs.VsSlotsW Z.th Z.P Z.L4 L3' L2' L1' (L.mem s'))
    (hgr : Z.L3 ⊆ L3' ∧ Z.L2 ⊆ L2' ∧ Z.L1 ⊆ L1') (hvn : (Z.vx = ∅ → Vs.VsNamed Z.th (L.mem s') (L.ksb s'))) :
    JAtZB (L := L) arI AR (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) H Cs Ac Lst D s' a' σ' := by
  set x := cslotAddr (pc.bv, idx) with hxdef
  have hkb : L.ksb s' = L.ksb s := hW.1
  have hcpu : L.cpu s' = L.cpu s := hW.2.1
  obtain ⟨σm, F1, C2⟩ := F.mid
  -- the slots' caps: the same shape everywhere
  have hS : ∀ y, IsSlot Z.th y → shape (capV (L.mem s') y) = shape (capV (L.mem s) y) := by
    intro y hy
    by_cases e : y = x
    · rw [e]; exact hsh
    · rw [hcap y hy e]
  have hUt : ∀ y, IsSlot Z.th y → isUt (capV (L.mem s') y) = true → capV (L.mem s') y = capV (L.mem s) y := by
    intro y hy hu
    by_cases e : y = x
    · exfalso
      rw [e, ← isUt_shape, hsh, isUt_shape, hnu] at hu; cases hu
    · exact hcap y hy e
  have hUK : UtKept Z.th (L.mem s) (L.mem s') := utKept_ofShape hS fun y hy _ => by
    by_cases e : y = x
    · exfalso
      have : isUt (capV (L.mem s) y) = true := by assumption
      rw [e, hnu] at this; cases this
    · exact hcap y hy e
  have hCK : CoverKept Z.th (L.mem s) (L.mem s') := coverKept_ofShape hS
  have hDel : DelInv Z.th (L.mem s') := J.del.ofShape hS hl
  -- `XTopAt` after: its relations
  obtain ⟨-, ⟨-, -, hM', -, -⟩, hFI', -, hMO', -, -⟩ := hX'.rel
  have hVR1 : VsRel Z.P (L.mem s') (L.ksb s) σ' := by have := hX'.fin.2.1; rwa [hkb] at this
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w : U64, P1.Aligned w → p.val ≤ w.val →
      w.val < p.val + 2 ^ k.bits → L.mem s' w = L.mem s w := fun p k hp hk w hal g1 g2 =>
    hW.mem_eq hal fun hb => by rcases J.vsxObjWX Ap hXa hpc hidx hb hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w : U64, P1.Aligned w → t.val ≤ w.val → w.val < t.val + 4096 →
      L.mem s' w = L.mem s w := fun t ht w hal g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w hal g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s' (mcpA t) = L.mem s (mcpA t) ∧ L.mem s' (flagsA t) = L.mem s (flagsA t) := fun t ht =>
    ⟨tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega),
      tcbK t ht _ (flagsA_aligned hT ht) (by rw [flagsA_val hT ht]; omega) (by rw [flagsA_val hT ht]; omega)⟩
  have k2 : ∀ t ∈ Z.T, L.mem s' (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s' (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w : U64, P1.Aligned w → q.val ≤ w.val → w.val < q.val + 2 ^ z →
      L.mem s' w = L.mem s w := fun q z hq w hal g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w hal g1 (by simpa only [P1.HKind.bits] using g2)
  have k3 : ∀ q ∈ Z.C, L.mem s' (P1.scReplyA q) = L.mem s (P1.scReplyA q) := fun q hq => by
    obtain ⟨xq, nq, hkq, hin⟩ := screply_obj J.xtop.fin.1.1.1 hq
    have hHq := (hJ.sc q xq nq (J.c0 q hq) hkq).2
    exact scw q _ hHq _ (sc_reply_word J.xtop.fin.1.1.1 hq).1 hin.1 hin.2
  have k4 : ∀ r ∈ Z.R, L.mem s' (P1.rPrevA r) = L.mem s (P1.rPrevA r) ∧
      L.mem s' (P1.rNextA r) = L.mem s (P1.rNextA r) := by
    intro r hr
    have hal := J.rp.align r hr
    have hHr : H r = some .reply := J.zH.2.2.1 r hr
    have k : ∀ a' : U64, (a'.val = r.val + 8 ∨ a'.val = r.val + 16) → L.mem s' a' = L.mem s a' := fun a' ha =>
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
        (by simp only [P1.HKind.bits]; omega)
    exact ⟨k _ (Or.inl (rPrevA_val hal)), k _ (Or.inr (rNextA_val hal))⟩
  have hOut : ∀ q z, H q = some (.sc z) → ∀ K : U64, K.val % 8 = 0 → K.val < 128 →
      L.mem s' (scW q K) = L.mem s (scW q K) := by
    intro q z hq K hK8 hK
    have hal := hHk.align q _ hq
    have hfit := hHk.fits q _ hq
    have hz := hHk.scmin q z hq
    simp only [P1.HKind.bits] at hal hfit
    have h128 : 2 ^ 7 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    have hq8 : q.val % 8 = 0 := by
      have hd : 8 ∣ 2 ^ z := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ z))
      rw [← Nat.mod_mod_of_dvd q.val hd, hal]
    have hv : (scW q K).val = q.val + K.val := scW_val (by omega)
    exact scw q z hq _ (by show (scW q K).val % 8 = 0; rw [hv]; omega) (by omega) (by omega)
  -- the debug word
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hDbg : L.mem s' (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by rcases J.vsxNodeWX hXa hpc hidx hb J.kern.cs0 with e | e <;> omega
  -- the spec's frames
  have hlook : ∀ {p : Fl4Spec.ObjRef} {ko : Fl4Spec.KernelObject}, (∀ a, ko ≠ .archObj a) →
      (∀ r cs, ko ≠ .cnode r cs) → (∀ x, ko ≠ .tcb x) → (σ'.kheap p = some ko ↔ σ.kheap p = some ko) :=
    fun ha hc ht => F.look ha hc ht
  have lsc : ∀ {p : Fl4Spec.ObjRef} {y : Fl4Spec.SchedContext} {n : Nat},
      (σ'.kheap p = some (.schedContext y n) ↔ σ.kheap p = some (.schedContext y n)) :=
    hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)
  -- the dead stay dead
  have hAI : Sched.ActIdle σ' := (J.act.ar F1).cn C2
  have yk : YKeep σ σ' := ⟨fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.yld⟩,
    fun p x n hp => ⟨x, lsc.2 hp, rfl⟩, fun p y n hp => ⟨y, lsc.1 hp, rfl⟩⟩
  have hdead : ∀ q ∈ D, DeadP (L := L) H s' q := fun q hq =>
    J.deadP_keep hX'.fin.1.1.1 hX'.ipc
      (fun x hx _ => let ⟨y, hy, hc⟩ := F.tcbF hx; ⟨y, hy, hc.st, hc.ntfn, Or.inl hc.sc⟩)
      (fun x hx => (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx)
      (fun x hx => ⟨x, (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx,
        Or.inl rfl, rfl, Or.inl rfl⟩)
      (fun x hx => ⟨x, (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hx, rfl⟩)
      (fun x n hx => ⟨x, lsc.2 hx, Or.inl rfl, Or.inl rfl⟩) (k3 q) (fun z hz _ => hOut q z hz) F.idle hAI.1
      (J.yld.frame k2 yk) (yk.dk q.bv) (J.jcov.dead q hq)
  -- P1's `BlkOK`: the VSpace words untracked, the slot's words cap-slot words
  have hslw : ∀ b, (b = x ∨ b = wordOf x 8#u64) → SlotWd Z.th b := by
    have hA : AbsSlot Z.th (pc.bv, idx) := ⟨pc, rfl, Or.inl (by simpa [hidx] using hpc)⟩
    rintro b (rfl | rfl)
    · exact ⟨x, hA.isSlot, 0#u64, Or.inl rfl, (wordOf_zero x).symm⟩
    · exact ⟨x, hA.isSlot, 8#u64, Or.inr (Or.inl rfl), rfl⟩
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s' := by
    refine (P1.blk_of_capw_untracked J.blk hW fun b hb0 => ?_).1
    have hb1 : (VsW Z (L.ksb s) b ∨ PtW X b) ∨ (b = x ∨ b = wordOf x 8#u64) := by
      rcases hb0 with (hb | hb) | hb
      · exact Or.inl (Or.inl hb)
      · exact Or.inr hb
      · exact Or.inl (Or.inr hb)
    rcases hb1 with hb | hb
    · refine Or.inr ⟨⟨J.vsW_alX hXa hb, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, fun hf => ?_⟩
      · rcases J.vsObjWX Ap hXa hb (p := t) (k := .tcb) ht (fun _ e => by cases e) with e | e
        · left; omega
        · right; simpa [P1.HKind.bits] using e
      · rcases J.vsNodeWX hXa hb hc with e | e <;> omega
      · rcases he with he | he
        · have hb8 : b.val % 8 = 0 := J.vsW_alX hXa hb
          have ha := hHk.align e _ he
          simp only [P1.HKind.bits] at ha
          rcases J.vsObjWX Ap hXa hb he (fun _ e => by cases e) with e | e
          · left; omega
          · right; simp only [P1.HKind.bits] at e; omega
        · have hb8 : b.val % 8 = 0 := J.vsW_alX hXa hb
          have ha := hHk.align e _ he
          simp only [P1.HKind.bits] at ha
          rcases J.vsObjWX Ap hXa hb he (fun _ e => by cases e) with e | e
          · left; omega
          · right; simp only [P1.HKind.bits] at e; omega
      · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
        have hko : ∀ z, k ≠ .other z := by
          rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
        obtain ⟨g1, g2⟩ := hin
        rcases J.vsObjWX Ap hXa hb hp hko with e | e <;> omega
    · exact Or.inl (J.slotCapW P1.tlow_slots b (hslw b hb))
  -- the spec's keeps
  have ck : Sched.CKeep σ σ' := ⟨fun q y n hq => ⟨y, lsc.2 hq, rfl⟩,
    fun q x hq => ⟨x, (hlook (fun _ e => by cases e) (fun _ _ e => by cases e) (fun _ e => by cases e)).2 hq, rfl, rfl⟩,
    fun p x n hp => ⟨x, lsc.1 hp⟩⟩
  obtain ⟨hCR', hRP'⟩ := CallRel.carry J.call J.rp ⟨k3, k4⟩ hkb ck
  have hRF' := RFree.carry J.rfree J.call k4 ck
  have hRR' := J.rrecv.frame k4 (F1.khrb.trans C2.toHStep.khrb)
  have hidl : Sched.IdleKeep (L := L) s s' := J.idleW_keep hX'.fin.1.1.1 F.idle F.isc
  have hjpl : ∃ Tr Cq, JPlaced (L := L) Z.th H Tr Cq s' σ' := ⟨Tr, Cq, hJ.ofShape F.szKeep hkb J.intL hS (fun t ht => by
    have hs : IsSlot Z.th (cslotAddr (t.bv, Fl4Spec.tcbCnodeIndex 2)) :=
      AbsSlot.isSlot ⟨t, rfl, Or.inr ⟨ht, 2, by decide, rfl⟩⟩
    rw [hcap _ hs (fun e => cnode_slot_ne_tcb J.xtop.rel.1 hpc hidx ht 2 (by decide) e.symm)]
    exact hJ.bfs t ht) hidl.2⟩
  have hKd : P1.DbgKeep st (P1.Heap.tcbs H) Cs s s' := dbgKeep_of_writes J.blk hW fun b hb =>
    J.notDbg (fun p hp => J.vsxObjWX Ap hXa hpc hidx hb hp (fun z h => by cases h))
      (fun c hc => J.vsxNodeWX hXa hpc hidx hb hc)
  have hTd : Sched.TdKeep (L := L) H s s' := fun q hq =>
    tcbK q (J.tcbZ hq) (P1.tdA q) (P1.field_aligned (hT q (J.tcbZ hq)) (K := 3528#u64) (by simp) (by simp))
      (by rw [J.tdA_val' (J.tcbZ hq)]; omega) (by rw [J.tdA_val' (J.tcbZ hq)]; omega)
  have hjc := J.jcov_cover hkb hM' hCK hUK hdead hidl (DXKeep.of_dbg hKd hTd)
  have hJC := J.jcs_slot hM' hMO' hFI' hUK F.ksz hDel
  -- `JKern`
  have hkern : JKern (L := L) arI H Cs D Z.th s' σ' := by
    have K := J.kern
    have hna : ∀ c o, L.nodeAt s' c o = L.nodeAt s c o := P1.nodeAt_of_ksb hkb
    obtain ⟨Q, R, hc, hs⟩ := J.xtop.fin.1.1.1.lists
    obtain ⟨Q', R', hc', hs'⟩ := hX'.fin.1.1.1.lists
    have ecw : L.curW s' = L.curW s := by
      apply P1.eq_of_bv
      have h1 := hs'.curThread; have h2 := hs.curThread
      unfold P1.LawfulStore.curW
      rw [hcpu, hna, hc.cur]
      unfold Sched.nodeW at h1 h2
      rw [hna] at h1
      rw [← h1, ← h2, F.ct]
    have ecs : L.cscW s' = L.cscW s := by
      apply P1.eq_of_bv
      have h1 := hs'.curSc; have h2 := hs.curSc
      unfold P1.LawfulStore.cscW P1.LawfulStore.nodeA
      rw [hcpu, hna, hc.cur]
      unfold Sched.nodeW at h1 h2
      rw [hna] at h1
      rw [← h1, ← h2, F.csc]
    have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp only [P1.LawfulStore.nodeBase, hkb]
    refine ⟨fun sl h => K.orig sl (by rw [← F.orig]; exact h), by rw [ecw, F.ct]; exact K.cur,
      by rw [ecw]; exact K.curT, by rw [hcpu, hna]; exact K.act, by rw [hna]; exact K.dwAl,
      by rw [hna]; exact K.dwObj, by rw [hna, hna, hcpu, ecw]; exact K.dwNe, ?_,
      by rw [F.arch]; exact F.hasPm K.gpm, by rw [F.arch]; exact K.ga, by rw [F.arch]; exact K.gf,
      K.heap, K.h0, by rw [hkb]; exact K.hks, by rw [hkb]; exact K.hksIn,
      fun p k hp c hc => by rw [hnb]; exact K.hnd p k hp c hc,
      by rw [hkb]; exact K.ksbFit, by rw [hkb]; exact K.ksbAl, by rw [hkb, hcpu]; exact K.nodeFit,
      by rw [hcpu]; exact K.cpuCs, by rw [ecw]; exact K.curH, by rw [ecs]; exact K.cscH,
      K.csLt, K.cs0, K.csN, K.tdx.frame (by rw [F.arch])⟩
    rw [hna, hDbg]; exact K.head
  have hutc := J.vsx_utcX hpc hidx hXa hW hVR1 (fun i h => by rw [F.arch]; exact h) hUt F.cdt F.orig
    (by rw [F.arch]) hDbg
  have R : JRest (L := L) arI (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) H Cs Ac Lst D s' σ' :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk,
      J.mcp.frame k1 (fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.mcpF⟩),
      J.buf.frame kb (fun p x hp => let ⟨y, hy, hc⟩ := F.tcbF hp; ⟨y, hy, hc.buf⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, hjc, hkern, hutc, (J.nsc.ar F1).cn C2.toHStep, (J.inv.ar F1).cn C2,
      CurInvW.cn (CurInvW.ar J.cur F1) C2, (J.own.ar F1).cn C2.toHStep, (J.off.ar F1).cn C2.toHStep, hAI,
      (J.bsa.ar F1).cn C2.toHStep, (J.isorted.ar F1).cn C2.toHStep,
      (J.curRun.ar F1).cn C2.toHStep (Or.inr C2.act), hblk⟩
  -- the buffer fields (`JBuf`): objects kept, arch objects of the same type,
  -- CNode slots or TCB caps changed (each TCB's buffer slot kept: the
  -- invoked slot is a CNode slot); the invoked slot's cap of the same object
  -- key (`hok`, so the same frame range)
  have hbf : JBuf (L := L) Z s' σ' := by
    obtain ⟨-, ⟨hSR', -⟩, -⟩ := hX'.rel
    have hfk : IpcFrKeep σ σ' := by
      refine IpcFrKeep.of_slot2 (th := Z.th) (mem := L.mem s) (mem' := L.mem s') (fun p => ?_) J.xtop.rel.2.1.1
        hSR' (fun t x0 hx => ?_) (fun q hq => ?_)
      · rcases F.kh p with e | h | h | ⟨x0, y0, h1, h2, hco⟩
        · exact Or.inl e
        · exact Or.inr (Or.inr (Or.inr h))
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl ⟨x0, y0, h1, h2, hco.2.1⟩))
      · rcases F.kh t with e | ⟨a0, a1, -, h2, -⟩ | ⟨r0, cs, cs', -, h2⟩ | ⟨x1, y1, h1, -, -⟩
        · exact J.thOfTcb (by rw [← e]; exact hx)
        · rw [hx] at h2; cases h2
        · rw [hx] at h2; cases h2
        · exact J.thOfTcb h1
      · left
        have hs : IsSlot Z.th (slotOf q 2) := ⟨q, 2, Or.inr ⟨hq, by simp [tcbSlots]⟩, rfl⟩
        have he : cslotAddr (q.bv, Fl4Spec.tcbCnodeIndex 2) = slotOf q 2 := by
          show slotAddr q.bv (Fl4Spec.ofBl _) = _
          rw [slotAddr_ofBl, tcbCnodeIndex_blVal 2 (by decide)]
        have hne : slotOf q 2 ≠ x := fun e =>
          cnode_slot_ne_tcb J.xtop.rel.1 hpc hidx hq 2 (by decide) (by rw [he, e])
        rw [capAt_capV, capAt_capV, hcap _ hs hne]
    refine ⟨J.bok.keep hfk, J.fcov.ipcFr hfk, fun y hy => ?_⟩
    by_cases e : y = x
    · rw [e]
      exact Vs.FrIn.of_okey hok ((J.fcap x (by rw [← e]; exact hy)).mono fun _ => UFr.keep hfk.page)
    · rw [hcap y hy e]; exact (J.fcap y hy).mono fun _ => UFr.keep hfk.page
  have hLS := LiveDN.simXB J J.live hX' rfl rfl rfl (fun p hp => R.jcov.dead p (J.zD p hp)) F.idle hKd
    (fun sl h => by first | rwa [F.orig] at h | rwa [← F.orig] at h)
    (fun y hy => LSim.of_shape (hS y hy))
  -- `vsTyp` after (jc3): the invoked slot's cap of the same object key, the
  -- others kept; the spec's arch objects of the same type; the sets grown
  have hTT : ∀ R, Vs.TabSlots Z.th R (L.mem s) → Vs.TabSlots Z.th R (L.mem s') := fun R h y hy => by
    by_cases e : y = x
    · rw [e]; exact (h x (by rw [← e]; exact hy)).of_okey hok
    · rw [hcap y hy e]; exact h y hy
  have hAF : ArchFwd σ σ' := fun p ao hp => by
    rcases F.kh p with e | ⟨a0, a1, h1, h2, ht⟩ | ⟨r, cs, cs', h1, -⟩ | ⟨x, y, h1, -⟩
    · exact ⟨ao, by rw [e]; exact hp, rfl⟩
    · rw [hp] at h1; cases h1; exact ⟨a1, h2, ht⟩
    · rw [hp] at h1; cases h1
    · rw [hp] at h1; cases h1
  have hvy : VsTyp (L := L) (Z.mv Z.G (Z.P, Z.L4, L3', L2', L1')) s' σ' :=
    J.carry.vsTyp.step hTT (tabSet_mono hgr.2.2 hgr.2.1 hgr.1) subset_rfl rfl hkb hAF
  exact J.cs_frameV (V' := (Z.P, Z.L4, L3', L2', L1')) (hvn := hvn) hkb hX' F.kback hbf ⟨hJC.del, hJC.ut, hJC.finM, hJC.sfree⟩ R
    hvc
    hLS.1 (fun p hp => J.zD p (hLS.2 p hp))
    ⟨J.carry.bufPg.frame subset_rfl (fun p vms hp => by
      rcases F.kh p with e | ⟨a0, a1, h1, h2, ht⟩ | ⟨r, cs, cs', h1, -⟩ | ⟨x, y, h1, -⟩
      · rw [e]; exact hp
      · rw [hp] at h1; cases h1; rw [h2, aaType_userData.1 ht]
      · rw [hp] at h1; cases h1
      · rw [hp] at h1; cases h1),
      J.carry.archFit.frame F.ksz⟩ (devFrom_kept J.mdbL hM' J.ut hUK) hvy hAF


end

end

end Fl4Proofs.P3
