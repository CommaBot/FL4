/-
P3 (DESIGN.md §9), TCB: **ReadFPU's frame writes at `J`** (for XTopJointTcb's
`tcb_read_fpuJ`: FL4's `copy_words` of a TCB's FPU image into a user frame).

* `FpuFrameJHyp` [J]: the destination frame cap's facts at the invocation's
  start that `JAtZ` does not carry (the cap's range meeting no non-`other`
  object of `H` is `JPlaced.cobj`'s `FrApartH`, which also keeps it off the
  TCBs; module docstring below).
* `JAtZ.frameWrJ`: a word that is not an IPC-buffer word written at `J`, the
  spec state kept: `XTopAt.userWr` (a `UserW` word), the slots kept (the word
  misses the VSpace objects, hence the slots, `vobj_of_slot`), the nodes and
  the IRQ node kept (the word misses the kernel's global data), the untyped
  caps' free parts untouched (the word lies in a spec object, `SpecFree`),
  P1's `BlkOK` by `blk_of_untracked` (as XTopJointData's `JAtZ.userWrJ`).
* `JAtZ.frameWordJ`: any frame word at `J`: an IPC-buffer word by
  `JAtZ.userWrJ` (the spec's user memory updated), another by
  `JAtZ.frameWrJ`.
* `JAtZ.copyFrameJ`: the 337-word copy into the frame at `J`
  (`copy_words_inv`), the spec's machine state some `ms`.

## `FpuFrameJHyp` [J]

For the frame cap in the first extra slot (non-device): (a) its range lies in
a spec user data page (l4v `valid_cap`: `typ_at (AArch (AUserData sz)) p` for
a non-device `PageCap`; a DeriveSubframe alias lies inside the large frame's
page); (b) its range misses the CNodes of `Z.th` and (c) FL4's page tables
and ASID pools (l4v `pspace_distinct` of the data page against the CNodes and
the page tables, carried through the state relation; neither is derivable
from `JAtZ`: `H` holds CNodes as `other` objects, which `FrApartH` does not
cover, and FL4's tables are not tied to `H`'s objects); (d) its range
misses FL4's kernel-global data `[ksb, ksb + ks::SIZE)` (`ks::SIZE` =
304384: the kernel-state block, the 64 cores' nodes, the ASID table; l4v
`valid_global_refs`: no cap's range meets the kernel's global references).
For FL4 (crates/fl4-core, fl4-kernel): the kernel-global data is the static
`KsArea` in the kernel image (fl4-kernel lib.rs), and RAM frames are retyped
from RAM untypeds, which miss the kernel image; device frames are excluded
(`fpu_transfer` rejects `is_device`). Only the entry state is asked; the
facts are carried across the caller's restart and the arch's `fpu_flush`.
-/
import Fl4Proofs.P3.XTopJointData
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- **ReadFPU's destination frame at the invocation's start** [J] (module
docstring): the non-device frame cap at `x` lies in a spec data page (a),
misses the CNodes of `Z.th` (b) and FL4's VSpace tables and ASID pools (c),
and misses FL4's kernel-global data (d). (The TCBs' part of `VObj` is not
asked: `JPlaced.tcb` with `JPlaced.cobj`'s `FrApartH`.) -/
def FpuFrameJHyp (Z : XSets) (s : S) (σ : Fl4Spec.State Unit) (x : U64) : Prop :=
  ∀ (p : U64) (sz : capability.FrameSize) (r : U64) (m ep : Bool) (asid va : U64),
    capV (L.mem s) x = .Frame p sz r false m ep asid va →
    (∃ (o : Fl4Spec.ObjRef) (vms : Fl4Spec.VMPageSize), σ.kheap o = some (.archObj (.dataPage false vms)) ∧
      o.toNat ≤ p.val ∧ p.val + 2 ^ frameBitsN sz ≤ o.toNat + 2 ^ Fl4Spec.pageBitsForSize vms) ∧
    (∀ q rr, Z.th q = some (.cnode rr) → p.val + 2 ^ frameBitsN sz ≤ q.val ∨ q.val + 32 * 2 ^ rr ≤ p.val) ∧
    (∀ q, (q ∈ Z.P ∨ q ∈ Z.L4 ∨ q ∈ Z.L3 ∨ q ∈ Z.L2 ∨ q ∈ Z.L1) →
      p.val + 2 ^ frameBitsN sz ≤ q.val ∨ q.val + 4096 ≤ p.val) ∧
    (p.val + 2 ^ frameBitsN sz ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ p.val)

end

/-- An aligned frame fits below `2^64`, at least a page, 8-byte aligned. -/
theorem frame_fit {p : U64} {sz : capability.FrameSize} (h : p.val % 2 ^ frameBitsN sz = 0) :
    4096 ≤ 2 ^ frameBitsN sz ∧ p.val % 8 = 0 ∧ p.val + 2 ^ frameBitsN sz ≤ 2 ^ 64 := by
  have hp : p.val < 2 ^ 64 := p.bv.isLt
  cases sz <;> simp only [frameBitsN, Nat.reducePow] at h ⊢ <;> omega

/-- The last byte of an aligned frame cap. -/
theorem frame_topF {p : U64} {sz : capability.FrameSize} (r : U64) (d m ep : Bool) (a va : U64)
    (h : p.val % 2 ^ frameBitsN sz = 0) :
    baseF (.Frame p sz r d m ep a va) = p.val ∧
      topF (.Frame p sz r d m ep a va) = p.val + 2 ^ frameBitsN sz - 1 := by
  obtain ⟨bs, ts⟩ := frame_range p sz r d m a va ep
  obtain ⟨h4, -, hfit⟩ := frame_fit h
  have hb : (fbitsF sz).val = frameBitsN sz := by rw [fbitsF_val]; cases sz <;> rfl
  have hb64 : (fbitsF sz).val < 64 := by rw [hb]; cases sz <;> simp [frameBitsN]
  have hmk : (maskF (fbitsF sz)).val = 2 ^ frameBitsN sz - 1 := by rw [maskF_val hb64, hb]
  refine ⟨bs, ?_⟩
  rw [ts]
  simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmk]
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

open Fl4Proofs.P1 in
set_option maxHeartbeats 16000000 in
/-- **A frame word that is not an IPC-buffer word, written at `J`** (module
docstring; the spec state kept). -/
theorem JAtZ.frameWrJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {w : U64}
    (hu : UserW (L := L) Z s σ w) (hnB : ∀ wp ∈ Z.B, wp.1 ≠ w)
    (hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val)
    (hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko)
    (hks : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val) (v : U64) :
    JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a σ := by
  set s1 := L.wr s w v with hs1
  have F : ArFr σ σ := ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hP := J.xtop.fin.1.2
  have hal : P1.Aligned w := hu.al
  have hW : P1.WritesIn st s s1 (· = w) := P1.writesIn_wr hal
  have hkb : L.ksb s1 = L.ksb s := hW.1
  have hcpu : L.cpu s1 = L.cpu s := hW.2.1
  have hSS : SlotsSame Z.th (L.mem s) (L.mem s1) :=
    slotsSame_wr hP.pl s v hal fun x hx ⟨h1, h2⟩ =>
      hu.vobj (vobj_of_slot hP.pl Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) hx h1 h2)
  have hX1 : XTopAt (L := L) AR Z s1 a σ := J.xtop.userWr hu hnB v
  -- the frame words
  obtain ⟨Q, R0, hcq, -⟩ := J.xtop.fin.1.1.1.lists
  have hT := hcq.tcbs
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hHk := J.kern.heap
  have objK : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → ∀ w' : U64, P1.Aligned w' → p.val ≤ w'.val →
      w'.val < p.val + 2 ^ k.bits → L.mem s1 w' = L.mem s w' := fun p k hp hk w' hal' g1 g2 =>
    hW.mem_eq hal' fun hb => by rw [hb] at g1 g2; rcases hAp p k hp hk with e | e <;> omega
  have tcbK : ∀ t ∈ Z.T, ∀ w' : U64, P1.Aligned w' → t.val ≤ w'.val → w'.val < t.val + 4096 →
      L.mem s1 w' = L.mem s w' := fun t ht w' hal' g1 g2 =>
    objK t .tcb (J.zH.1 t ht) (fun _ e => by cases e) w' hal' g1 (by simpa [P1.HKind.bits] using g2)
  have k1 : ∀ t ∈ Z.T, L.mem s1 (mcpA t) = L.mem s (mcpA t) := fun t ht =>
    tcbK t ht _ (mcpA_aligned hT ht) (by rw [mcpA_val hT ht]; omega) (by rw [mcpA_val hT ht]; omega)
  have k2 : ∀ t ∈ Z.T, L.mem s1 (P1.yieldA t) = L.mem s (P1.yieldA t) := fun t ht =>
    tcbK t ht _ (yieldA_aligned hT ht) (by rw [yieldA_val hT ht]; omega) (by rw [yieldA_val hT ht]; omega)
  have kb : ∀ t ∈ Z.T, L.mem s1 (tIpcBufA t) = L.mem s (tIpcBufA t) := fun t ht =>
    tcbK t ht _ (tIpcBufA_aligned (hT t ht)) (by rw [tIpcBufA_val (hT t ht)]; omega)
      (by rw [tIpcBufA_val (hT t ht)]; omega)
  have scw : ∀ q z, H q = some (.sc z) → ∀ w' : U64, P1.Aligned w' → q.val ≤ w'.val → w'.val < q.val + 2 ^ z →
      L.mem s1 w' = L.mem s w' := fun q z hq w' hal' g1 g2 =>
    objK q _ hq (fun _ e => by cases e) w' hal' g1 (by simpa only [P1.HKind.bits] using g2)
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
      objK r _ hHr (fun _ e => by cases e) a' (J.rp.aligned hr ha) (by omega)
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
  -- the debug word and the IRQ node: in the kernel-global data, which the word misses
  have hN0 : P1.NodePlaced st Z.T s 0#u64 := by rw [J.tcbs_eq.1]; exact P1.TInv.nodes J.blk _ J.kern.cs0
  have hnb0 : L.nodeBase s 0#u64 = (L.ksb s).val + 13568 := by
    show (L.ksb s).val + 13568 + (0#u64 : U64).val * 4288 = _; simp
  have hDbg : L.mem s1 (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) =
      L.mem s (L.nodeAt s 0#u64 layout.node.DEBUG_TCBS) := by
    have hdv := P1.nodeAt_val hN0 (off := layout.node.DEBUG_TCBS) (by simp [layout.node.DEBUG_TCBS])
    have hdo : layout.node.DEBUG_TCBS.val < 4288 := by simp [layout.node.DEBUG_TCBS]
    exact hW.mem_eq J.kern.dwAl fun hb => by
      rw [hb, hnb0] at hdv; omega
  have hirq : ∀ i : U64, i.val < 128 → capV (L.mem s1) (nodeA (L.ksb s) i) = capV (L.mem s) (nodeA (L.ksb s) i) :=
    irqNode_keep hW J.kern.ksbFit J.kern.ksbAl fun b hb => by
      rw [hb]; omega
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
  -- P1's `BlkOK`
  have hblk : P1.BlkOK st (P1.Heap.tcbs H) Cs (P1.Heap.omega H) H (P1.Heap.frame H) (P1.Heap.replies H)
      (P1.Heap.scs H) (P1.Heap.ntfns H) (P1.Heap.scBits H) Ac s1 := by
    refine (P1.blk_of_untracked J.blk hW fun b hb => ⟨⟨by rw [hb]; exact hal, fun t ht => ?_, fun c hc => ?_⟩,
      fun e he => ?_, fun hf => ?_⟩).1
    · subst hb
      rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
      · left; omega
      · right; simpa [P1.HKind.bits] using e
    · subst hb
      have hcl := J.kern.csLt c hc
      have hnb : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
      omega
    · subst hb
      rcases he with he | he
      · rcases hAp e _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
      · rcases hAp e _ he (fun _ e => by cases e) with e | e
        · left; omega
        · right; simp only [P1.HKind.bits] at e; omega
    · subst hb
      obtain ⟨-, p, k, hp, hk, hin⟩ := hf
      have hko : ∀ z, k ≠ .other z := by
        rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
      obtain ⟨g1, g2⟩ := hin
      rcases hAp p k hp hko with e | e <;> omega
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
    have hxm : cslotAddr sl ∈ Z.G.chains.flatten :=
      (hM.members _).2 ⟨hsl.isSlot, _, hcap0, fun h => by cases h⟩
    have B := notDev_back (capV_of_capAt hcap) (capV_of_capAt hcap0)
    refine ⟨U.pal, U.pfit, U.fiLe, fun g => U.high (B g), fun g => by rw [hcpu, hna]; exact U.actZ (B g), U.free, ?_,
      U.sb4, U.nostr, U.nsFree,
      fun h0 => U.ns (by rw [F.cdt] at h0; exact h0),
      ?_, fun g => by rw [hna]; exact U.dwReg (B g),
      fun g => by rw [F.gpml4]; exact U.gReg (B g)⟩
    · intro g w' hal' h1 h2
      rw [hW.mem_eq hal' fun hb => ?_]
      · exact U.zero (B g) w' hal' h1 h2
      rw [hb] at h1 h2
      obtain ⟨o, ko, hko, g1, g2⟩ := hObj
      have := J.sfree _ hxm p sb fi (by rw [hcv, hdv]) o ko hko
      omega
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
  have R : JRest (L := L) arI { Z with G := Z.G } H Cs Ac Lst D s1 σ :=
    ⟨hCR', hRF', hRR', J.yld.frame k2 yk, J.mcp.frame k1 (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩),
      J.buf.frame kb (fun p x hp => ⟨x, (F.look (fun _ e => by cases e)).2 hp, rfl⟩), hRP',
      J.apart.sc_frame hkb F.szKeep, hjpl, J.jcov_keep hkb hSS hdead (J.idleW_keep hX1.fin.1.1.1 F.idle F.isc), hkern,
      hutc, J.nsc.ar F, J.inv.ar F, CurInvW.ar J.cur F, J.own.ar F,
      J.off.ar F, hAI, J.bsa.ar F, J.isorted.ar F, J.curRun.ar F, hblk⟩
  exact J.cs_frame (G' := Z.G) hkb hX1 F.kback (JCs.same J hSS F.ksz) R (J.vsc.of_eq fun y hy => hSS.capV hy)

/-- **A frame word written at `J`** (`JAtZ.userWrJ` for an IPC-buffer word,
`JAtZ.frameWrJ` for another), the spec's machine state some `ms`. -/
theorem JAtZ.frameWordJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hBP : BufPlaced (L := L) Z.N Z.C Z.B Z.c s σ) {w : U64}
    (hu : UserW (L := L) Z s σ w)
    (hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val)
    (hObj : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ w.val ∧ w.val < o.toNat + 2 ^ Fl4Spec.objBits ko)
    (hks : w.val + 8 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ w.val) (v : U64) :
    ∃ ms, JAtZ (L := L) arI AR Z H Cs Ac Lst D (L.wr s w v) a { σ with machineState := ms } := by
  by_cases hB : ∃ wp ∈ Z.B, wp.1 = w
  · obtain ⟨wp, hwp, rfl⟩ := hB
    exact ⟨_, J.userWrJ hBP hwp hAp hObj v⟩
  · push_neg at hB
    exact ⟨σ.machineState, J.frameWrJ hu hB hAp hObj hks v⟩

set_option maxHeartbeats 8000000 in
/-- **ReadFPU's copy into the frame at `J`** (`copy_words_inv` with
`JAtZ.frameWordJ`): the 2696 bytes at `f` miss every non-`other` object of
`H`, the VSpace objects and the kernel-global data, and lie in a spec object;
`BufPlaced` at every `XTopAt` state of the typed heap (the decode's premise). -/
theorem JAtZ.copyFrameJ (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (hBPl : ∀ (Z' : XSets) s' a' σ', Z'.th = Z.th → XTopAt (L := L) AR Z' s' a' σ' →
      Vs.BufPlaced (L := L) Z'.N Z'.C Z'.B Z'.c s' σ')
    (src f : U64) (hf8 : f.val % 8 = 0) (hfit : f.val + 2696 ≤ 2 ^ 64)
    (hApR : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → f.val + 2696 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ f.val)
    (hObjR : ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ f.val ∧ f.val + 2696 ≤ o.toNat + 2 ^ Fl4Spec.objBits ko)
    (hVR : ∀ w : U64, f.val ≤ w.val → w.val < f.val + 2696 → ¬ VObj Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 (L.ksb s) w)
    (hksR : f.val + 2696 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ f.val) :
    tcb.copy_words st s src f 337#u64 ⦃ s' =>
      ∃ ms, JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a { σ with machineState := ms } ⦄ := by
  refine WP.spec_mono (copy_words_inv (fun s' => L.ksb s' = L.ksb s ∧
    ∃ ms, JAtZ (L := L) arI AR Z H Cs Ac Lst D s' a { σ with machineState := ms }) s src f 337#u64
    ⟨rfl, σ.machineState, J⟩ ?_) (fun _ h => h.2)
  rintro s2 i ⟨hk2, ms, J2⟩ hi v
  have hi' : i.val < 337 := hi
  set w := core.num.U64.wrapping_add f (core.num.U64.wrapping_mul i 8#u64) with hw
  have hwv : w.val = f.val + 8 * i.val := by
    rw [hw]
    simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
    simp [U64.size, U64.numBits]
    omega
  have hAp : ∀ q k, H q = some k → (∀ z, k ≠ .other z) → w.val + 8 ≤ q.val ∨ q.val + 2 ^ k.bits ≤ w.val :=
    fun q k hq hk => by rcases hApR q k hq hk with e | e <;> omega
  have hks : w.val + 8 ≤ (L.ksb s2).val ∨ (L.ksb s2).val + 304384 ≤ w.val := by rw [hk2]; omega
  obtain ⟨Q, R0, hc, -⟩ := J2.xtop.fin.1.1.1.lists
  have hcZ : Z.c.val < 64 := by rw [← hc.cur]; exact J2.kern.csLt _ J2.kern.cpuCs
  have hnbc : L.nodeBase s2 Z.c = (L.ksb s2).val + 13568 + Z.c.val * 4288 := rfl
  obtain ⟨Tr, Cq, hJ⟩ := J2.jpl
  have hu : UserW (L := L) Z s2 { σ with machineState := ms } w := by
    refine ⟨show w.val % 8 = 0 by omega, ⟨by omega, fun t ht => ?_, fun sc hsc x n hk => ?_⟩,
      fun hv => hVR w (by omega) (by omega) (by rw [← hk2]; exact hv), fun e he => ?_, fun r hr => ?_,
      fun n hn => ?_⟩
    · rcases hAp t _ (J2.zH.1 t ht) (fun _ e => by cases e) with e | e
      · exact Or.inl e
      · simp only [P1.HKind.bits] at e; exact Or.inr (by omega)
    · rcases hAp sc _ (hJ.sc sc x n (J2.c0 sc hsc) hk).2 (fun _ e => by cases e) with e | e
      · exact Or.inl e
      · simp only [P1.HKind.bits] at e; exact Or.inr e
    · rcases hAp e _ (J2.zH.2.1 e he) (fun _ e => by cases e) with e | e
      · exact Or.inl e
      · simp only [P1.HKind.bits] at e; exact Or.inr (by omega)
    · rcases hAp r _ (J2.zH.2.2.1 r hr) (fun _ e => by cases e) with e | e
      · exact Or.inl e
      · simp only [P1.HKind.bits] at e; exact Or.inr (by omega)
    · rcases hAp n _ (J2.zH.2.2.2 n hn) (fun _ e => by cases e) with e | e
      · exact Or.inl e
      · simp only [P1.HKind.bits] at e; exact Or.inr (by omega)
  have hObj : ∃ o ko, ({ σ with machineState := ms } : Fl4Spec.State Unit).kheap o = some ko ∧ o.toNat ≤ w.val ∧
      w.val < o.toNat + 2 ^ Fl4Spec.objBits ko := by
    obtain ⟨o, ko, hko, g1, g2⟩ := hObjR
    exact ⟨o, ko, hko, by omega, by omega⟩
  obtain ⟨ms', J3⟩ := J2.frameWordJ (hBPl Z s2 a _ rfl J2.xtop) hu hAp hObj hks v
  exact ⟨by rw [L.ksb_wr, hk2], ms', J3⟩

end

end

end Fl4Proofs.P3
