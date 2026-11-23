/-
P3 (issue #16, FL4 #71), VSpace: **a PML4 cap's decode at `JAt` with
`X86PML4FrameBatch`** (KENTRY-PLAN fb3j).

* `decode_invocation_pml4_fbJV`: the batch label. FL4's
  `vspace::decode_frame_batch` replies in the decode (the reply class,
  `XCap`'s right disjunct, as a frame cap's GetAddress): the decode's
  checks against `decodeFrameBatch`, the loop entry by entry against
  `fbEntry` (from the spec's state *before* its `Restart`, transferred by
  SpecFbRestart's `performFrameBatch_restart`), the deferred
  `invalidate_asid` against `flushAll`, the reply and `TS_RUNNING` by
  VsFbReply's `fbTail_inv`, and `JAt` after (proved, `JPath`'s PML4 arm
  stays `True`). OPEN (the one FrameBatch site left on the P3 chain;
  scratch stub `proofs/scratch/fb3scratch.py`).
* `decode_invocation_pml4JV`: every label: the batch above, any other by
  XTopJointVsMap's `decode_invocation_pml4JVn`. The callers
  (XTopJointEntry, XTopJointKEntry13P, XTopJointKEntry23P) pass the
  message (`args`, `hlen`, `hargs`), the extra caps (`ExtraOK`,
  `ExtraNamed`) and the invoked slot (`AbsSlot`, its cap), as their other
  VSpace caps.
-/
import Fl4Proofs.P3.XTopJointVsMap
import Fl4Proofs.P3.JEntryIrq
import Fl4Proofs.P3.VsFbDec
import Fl4Proofs.P3.VsFbReply
import Fl4Proofs.P3.XTopJointVsReply
import Fl4Proofs.P3.SpecFbRestart
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

/-! ## The spec's loop, entry by entry (for `fb_loopJ`) -/

section SpecLoop
open Fl4Spec

theorem fbRun_nil_mem (b : Fl4FrameBatchInvocation) (n : Nat) (d : Bool) (σ : State Unit) :
    ((n, (0 : Data), d), σ) ∈ (fbRun (Z := Unit) b [] n d σ).1 := rfl

theorem fbRun_cons_err {b : Fl4FrameBatchInvocation} {w : Data × Data × Data} {ws : List (Data × Data × Data)}
    {n : Nat} {d : Bool} {σ τ : State Unit} {c : Data} (h : (.error c, τ) ∈ ((fbEntry (Z := Unit) b w).run σ).1) :
    ((n, c, d), τ) ∈ (fbRun (Z := Unit) b (w :: ws) n d σ).1 := by
  unfold fbRun
  exact ⟨_, h, rfl⟩

theorem fbRun_cons_ok {b : Fl4FrameBatchInvocation} {w : Data × Data × Data} {ws : List (Data × Data × Data)}
    {n : Nat} {d d' : Bool} {σ τ : State Unit} {y : (Nat × Data × Bool) × State Unit}
    (h : (.ok d', τ) ∈ ((fbEntry (Z := Unit) b w).run σ).1) (h2 : y ∈ (fbRun (Z := Unit) b ws (n + 1) (d || d') τ).1) :
    y ∈ (fbRun (Z := Unit) b (w :: ws) n d σ).1 := by
  unfold fbRun
  exact ⟨_, h, h2⟩

end SpecLoop

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}

/-- The batch `fbDecQ` decodes (its checks passed). -/
def fbDecB (p : Fl4Spec.ObjRef) (asid : Fl4Spec.Asid) (args : List Fl4Spec.Data)
    (ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) (op : Fl4Spec.FbOp) : Fl4Spec.Fl4FrameBatchInvocation :=
  { vspace := p, asid := asid, op := op, depth := Fl4Spec.dataToNat ((Fl4Spec.the args[0]? >>> 16) &&& 0x7f#64),
    mapRights := (Fl4Spec.the args[0]? >>> 24) &&& 0xf#64, capRights := (Fl4Spec.the args[0]? >>> 28) &&& 0xf#64,
    attr := (Fl4Spec.the args[0]? >>> 32) &&& 0x1f#64,
    deferDelete := decide (Fl4Spec.the args[0]? &&& (1#64 <<< 40) ≠ 0),
    cnode := (Fl4Spec.the ex[0]?).1,
    destCnode := if op = .copyMap ∧ ex.length > 1 then (Fl4Spec.the ex[1]?).1 else (Fl4Spec.the ex[0]?).1,
    entries := Fl4Spec.fbEntries args op.words (Fl4Spec.dataToNat ((Fl4Spec.the args[0]? >>> 8) &&& 0xff#64)) }

theorem fbDecQ_ok {p : Fl4Spec.ObjRef} {asid : Fl4Spec.Asid} {args : List Fl4Spec.Data}
    {ex : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)} {op : Fl4Spec.FbOp}
    (h3 : ¬ args.length < 1 + op.words * Fl4Spec.dataToNat ((Fl4Spec.the args[0]? >>> 8) &&& 0xff#64))
    (hl0 : ¬ ex.length < 1) (h5 : Fl4Spec.isCnodeCap (Fl4Spec.the ex[0]?).1 = true)
    (h6 : Fl4Spec.isCnodeCap (if op = .copyMap ∧ ex.length > 1 then (Fl4Spec.the ex[1]?).1
      else (Fl4Spec.the ex[0]?).1) = true) :
    fbDecQ p asid args ex op = .ok (fbDecB p asid args ex op) := by
  unfold fbDecQ; rw [if_neg h3, if_neg hl0, if_pos h5, if_pos h6]; rfl

/-- `isCnodeCap` of the abstraction of a native cap that is no CNode. -/
theorem fb_notCN {c : capability.Cap} (h : ∀ a b d e, c ≠ .CNode a b d e) : Fl4Spec.isCnodeCap (absCap c) = false := by
  cases c <;> first | rfl | exact absurd rfl (h _ _ _ _)

theorem fb_isCN {c : capability.Cap} (h : Fl4Spec.isCnodeCap (absCap c) = true) :
    ∃ a b d e, c = .CNode a b d e := by
  by_contra hn
  push_neg at hn
  rw [fb_notCN hn] at h
  exact absurd h (by decide)

/-- `XTopAt` at another machine state (same memory) and arch state (XTopJointIrq's `XTopAt.msAR`,
which is downstream of this module). -/
theorem XTopAt.msAR' {s : S} {a : A} {σ : Fl4Spec.State Unit} (hX : XTopAt (L := L) AR Z s a σ)
    (ms : Fl4Spec.MachineState) (a' : A) (hum : ms.underlyingMemory = σ.machineState.underlyingMemory)
    (hAR : AR a' σ.archState.x64CurrentCr3) : XTopAt (L := L) AR Z s a' { σ with machineState := ms } :=
  hX.frameStep (P1.WritesIn.refl s (fun _ => False)) (fun _ h => h.elim) (fun _ h => h.elim) (fun _ h => h.elim) id id
    rfl rfl rfl rfl hum rfl rfl rfl (hX.fin.1.1.1.spec_congr rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    ⟨hX.fin.1.1.2.2.2.1.st, hX.fin.1.1.2.2.2.1.node⟩ hX.fin.1.1.2.2.2.2.1 hX.rel.2.2.2.1 hAR

/-- **The batch's deferred `invalidate_asid` at `J`**: the spec's `flushAll` (machine state only,
`flushAll_ok`), `JAtZ` kept (XTopJointFpu's `JAtZ.arFrS`). -/
theorem JAtZ.fbFlushJ (hA : ArchRefines arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (vs : Fl4Spec.ObjRef) (asid : U64) :
    arI.invalidate_asid a asid ⦃ a' => ∃ σ', ((), σ') ∈ (Fl4Spec.flushAll (Z := Unit) vs asid.bv σ).1 ∧
      σ'.kheap = σ.kheap ∧ σ'.curThread = σ.curThread ∧ JAtZ (L := L) arI AR Z H Cs Ac Lst D s a' σ' ⦄ := by
  refine WP.spec_mono (hA.invAsid a _ asid J.xtop.fin.1.1.2.2.2.2.2.2) ?_
  intro a' hAR
  obtain ⟨-, ⟨y, hy⟩, h3⟩ := flushAll_ok vs asid.bv σ
  obtain ⟨ms, e, hum⟩ := h3 _ hy
  obtain ⟨u, σ'⟩ := y
  cases u
  simp only at e
  subst e
  exact ⟨_, hy, rfl, rfl, J.arFrS ⟨fun _ => Or.inl rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩ (J.xtop.msAR' ms a' hum hAR)⟩

set_option maxHeartbeats 8000000 in
/-- **The batch's reply registers at `J`** (XTopJointVsReply's `JAtZ.reply1RJ` with two words): the
badge, `MR0`, `MR1` and the message info of `ct`, the spec's `replyTcb2`. -/
theorem JAtZ.fbRegsJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x)) (d e w : U64)
    (hw : w.bv = Fl4Spec.messageInfoToData ⟨Fl4Spec.natToLen 2, 0, 0, 0⟩) :
    ∃ Z' : XSets, ct ∈ Z'.T ∧ JAtZ (L := L) arI AR Z' H Cs Ac Lst D
      (L.wr (L.wr (L.wr (L.wr s (Endp.regA ct (Endp.regIdx Fl4Spec.badge_register)) 0#u64)
          (Endp.regA ct (Endp.regIdx (Endp.mrIdx 0))) d) (Endp.regA ct (Endp.regIdx (Endp.mrIdx 1))) e)
          (Endp.regA ct (Endp.regIdx Fl4Spec.msg_info_register)) w) a
      (updK σ ct.bv (.tcb (Endp.replyTcb2 x d.bv e.bv))) := by
  have hXb := badge_wr_irel J.ip (J.xtop.irelK J.ks J.buf) hct hk 0#u64
  rw [badgeRegA_eq_regA] at hXb
  obtain ⟨V1, J1⟩ := J.regWrJ hct hk Fl4Spec.badge_register 0#u64 hXb
  set x1 := setReg x Fl4Spec.badge_register (0#u64 : U64).bv with hx1
  have hk1 : (updK σ ct.bv (.tcb x1)).kheap ct.bv = some (.tcb x1) := by simp [updK]
  have hX2 := reg_wr_irel J1.ip (J1.xtop.irelK J1.ks J1.buf) hct hk1 (Endp.mrIdx 0) (by decide) d
  obtain ⟨V2, J2⟩ := J1.regWrJ hct hk1 (Endp.mrIdx 0) d hX2
  set x2 := setReg x1 (Endp.mrIdx 0) d.bv with hx2
  have hk2 : (updK (updK σ ct.bv (.tcb x1)) ct.bv (.tcb x2)).kheap ct.bv = some (.tcb x2) := by simp [updK]
  have hX3 := reg_wr_irel J2.ip (J2.xtop.irelK J2.ks J2.buf) hct hk2 (Endp.mrIdx 1) (by decide) e
  obtain ⟨V3, J3⟩ := J2.regWrJ hct hk2 (Endp.mrIdx 1) e hX3
  set x3 := setReg x2 (Endp.mrIdx 1) e.bv with hx3
  have hk3 : (updK (updK (updK σ ct.bv (.tcb x1)) ct.bv (.tcb x2)) ct.bv (.tcb x3)).kheap ct.bv =
      some (.tcb x3) := by simp [updK]
  have hX4 := reg_wr_irel J3.ip (J3.xtop.irelK J3.ks J3.buf) hct hk3 Fl4Spec.msg_info_register (by decide) w
  obtain ⟨V4, J4⟩ := J3.regWrJ hct hk3 Fl4Spec.msg_info_register w hX4
  have hxC : setReg x3 Fl4Spec.msg_info_register w.bv = Endp.replyTcb2 x d.bv e.bv := by
    rw [hw]; rfl
  rw [updK_updK, updK_updK, updK_updK, hxC] at J4
  refine ⟨_, ?_, J4⟩
  exact hct

set_option maxHeartbeats 8000000 in
/-- **VsFbReply's `fbTail` of a runnable thread at `J`** (as XTopJointVsReply's `JAtZ.reply1RJ`):
`JAt` at the spec's state with the two-word reply (when called) and `Running`. -/
theorem JAtZ.fbTailJ {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) {ct : U64} (hct : ct ∈ Z.T)
    {x : Fl4Spec.Tcb} (hk : σ.kheap ct.bv = some (.tcb x))
    (hrs : x.tcbState = .restart ∨ x.tcbState = .running ∨ x.tcbState = .runningVM) (call : Bool) (d e : U64) :
    Vs.fbTail (st := st) s ct call d e ⦃ s2 => JAt (L := L) arI AR s2 a (stsAct (updK σ ct.bv
      (.tcb { (if call then Endp.replyTcb2 x d.bv e.bv else x) with tcbState := .running })) ct.bv) ⦄ := by
  unfold Vs.fbTail
  cases call
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_ok]
    refine WP.spec_mono (J.runRJ hct hk hrs) ?_
    rintro s2 ⟨Lst', D', J2⟩
    exact ⟨_, _, _, _, _, _, J2⟩
  · simp only [↓reduceIte]
    refine WP.spec_bind (Vs.fbTail_words s ct d e) ?_
    rintro s5 ⟨w, rfl, hw⟩
    obtain ⟨Z', hct', J4⟩ := J.fbRegsJ arI hct hk d e w hw
    have hkC : (updK σ ct.bv (.tcb (Endp.replyTcb2 x d.bv e.bv))).kheap ct.bv =
        some (.tcb (Endp.replyTcb2 x d.bv e.bv)) := by simp [updK]
    refine WP.spec_mono (J4.runRJ hct' hkC hrs) ?_
    rintro s6 ⟨Lst', D', J6⟩
    rw [updK_updK] at J6
    exact ⟨_, _, _, _, _, _, J6⟩

/-- Reduce a tuple-`let` continuation applied to a pair (MachKeepG4d's `fb_red`). -/
macro "fbj_red" : tactic =>
  `(tactic| ((try simp only [WP.uncurry'_pair]) <;> (try simp only [uncurry_apply_pair]) <;> (try simp only [Aeneas.Std.uncurry]) <;> (try dsimp only)))

/-- The state the batch's loop carries (KENTRY-PLAN fb3k): `JAtZ`, the message words still readable
(the batch writes no register or IPC-buffer word of `ct`), the current thread and its thread state. -/
def FbMidJ (σ : Fl4Spec.State Unit) (ct buf : U64) (args : List U64) (x : S) (a : A) (τ : Fl4Spec.State Unit) :
    Prop :=
  (∃ (Z1 : XSets) (H1 : P1.Heap) (Cs1 Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
    JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 x a τ) ∧
  (∀ (i : U64) v, args[i.val]? = some v → msg.syscall_arg st x ct buf i = ok v) ∧
  τ.curThread = σ.curThread ∧
  (∀ x0 : Fl4Spec.Tcb, σ.kheap ct.bv = some (.tcb x0) →
    ∃ y : Fl4Spec.Tcb, τ.kheap ct.bv = some (.tcb y) ∧ y.tcbState = x0.tcbState)

/-- A failing entry's code as the loop computes it, against the spec's. -/
def FbErrOK (b : Fl4Spec.Fl4FrameBatchInvocation) (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data)
    (τ τ1 : Fl4Spec.State Unit) : error.Exc → Prop
  | .Sys e1 => error.SysError.code e1 ⦃ c => (.error c.bv, τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b w).run τ).1 ⦄
  | _ => (.error fl4_abi.consts.error.IllegalOperation.bv, τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b w).run τ).1

theorem fbEntries_drop {A : List Fl4Spec.Data} {w n d : Nat} (hd : d < n) :
    (Fl4Spec.fbEntries A w n).drop d = (Fl4Spec.the A[1 + w * d]?, if w > 1 then Fl4Spec.the A[1 + w * d + 1]? else 0,
      if w > 2 then Fl4Spec.the A[1 + w * d + 2]? else 0) :: (Fl4Spec.fbEntries A w n).drop (d + 1) := by
  unfold Fl4Spec.fbEntries
  rw [List.drop_eq_getElem_cons (by simpa using hd)]
  simp

theorem fbEntries_drop_n {A : List Fl4Spec.Data} {w n : Nat} : (Fl4Spec.fbEntries A w n).drop n = [] := by
  unfold Fl4Spec.fbEntries; simp

theorem fb_the_arg {args : List U64} {i : Nat} (h : i < args.length) :
    Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[i]? = args[i].bv := by
  rw [List.getElem?_map, List.getElem?_eq_getElem h]; rfl

set_option maxHeartbeats 8000000 in
/-- **One entry of the batch at `J`** (KENTRY-PLAN fb3k, step 2): FL4's `frame_batch_entry` from a
`FbMidJ` state has an outcome of the spec's `fbEntry` (its error code as the loop computes it), `FbMidJ`
after, the deferred flag as the spec's. OPEN. -/
theorem fb_entryJ (hA : ArchRefines arI AR) (hT : P0.ArchTotal arI) (σ : Fl4Spec.State Unit) (ct buf : U64)
    (args : List U64) (p asid : U64) (h0 : asid ≠ 0#u64)
    (b : Fl4Spec.Fl4FrameBatchInvocation) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hb : fbDecP p.bv asid.bv (args.map UScalar.bv) excaps = .ok b)
    (a0 : U64) (ha0 : args[0]? = some a0)
    (n words op depth mr cr attr : U64) (dd : Bool) (cnode dcnode : capability.Cap)
    (hop : op = a0 &&& vspace.frame_batch.OP) (hw : words.val = b.op.words)
    (hn : n = (⟨a0.bv >>> 8⟩ : U64) &&& 255#u64) (hdp : depth = (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64)
    (hmr : mr = (⟨a0.bv >>> 24⟩ : U64) &&& 15#u64) (hcr : cr = (⟨a0.bv >>> 28⟩ : U64) &&& 15#u64)
    (hat : attr = (⟨a0.bv >>> 32⟩ : U64) &&& 31#u64)
    (hdd : ∃ d : U64, d = 1099511627776#u64 ∧ dd = (a0 &&& d != 0#u64))
    (hbc : b.cnode = absCap cnode) (hbd : b.destCnode = absCap dcnode)
    (hcnC : ∃ a b d e, cnode = .CNode a b d e) (hdc6 : Fl4Spec.isCnodeCap (absCap dcnode) = true)
    (hbv : b.vspace = p.bv) (hba : b.asid = asid.bv)
    (x : S) (a : A) (τ : Fl4Spec.State Unit) (hM : FbMidJ (L := L) (AR := AR) arI σ ct buf args x a τ)
    (w : Fl4Spec.Data × Fl4Spec.Data × Fl4Spec.Data) (w0 w1 w2 : U64)
    (hw0 : w0.bv = w.1) (hw1 : w1.bv = w.2.1) (hw2 : w2.bv = w.2.2) (df : Bool) :
    vspace.frame_batch_entry st arI x a
      { root := p, asid := asid, op := op, depth := depth, map_rights := mr, cap_rights := cr, attr := attr,
        defer_delete := dd, cnode := cnode, dest_cnode := dcnode } w0 w1 w2 df ⦃ r =>
      ∃ τ1, FbMidJ (L := L) (AR := AR) arI σ ct buf args r.2.1 r.2.2.1 τ1 ∧
        ((r.1 = .Ok () ∧ ∃ d', (.ok d', τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b w).run τ).1 ∧ r.2.2.2 = (df || d')) ∨
          (∃ e, r.1 = .Err e ∧ r.2.2.2 = df ∧ FbErrOK b w τ τ1 e)) ⦄ := by
  fail "FB3 OPEN: the FrameBatch refinement (KENTRY-PLAN fb3j)"

set_option maxHeartbeats 8000000 in
/-- **The batch's loop at `J`** (the decode's checks passed): FL4's loop has an outcome of the spec's
`fbRun` over the batch's entries from `σ` (entries done, the failing entry's code, whether a deferred
delete cleared an entry), with `JAtZ` after, the current thread and its thread state kept. OPEN (the
one FrameBatch stub left; KENTRY-PLAN fb3k). -/
theorem fb_loopI (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (h0 : asid ≠ 0#u64) (length buf : U64)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False))
    (b : Fl4Spec.Fl4FrameBatchInvocation)
    (hb : fbDecP p.bv asid.bv (args.map UScalar.bv) excaps = .ok b)
    (a0 : U64) (ha0 : args[0]? = some a0)
    (n words op depth mr cr attr : U64) (dd : Bool) (cnode dcnode : capability.Cap)
    (hop : op = a0 &&& vspace.frame_batch.OP) (hw : words.val = b.op.words)
    (hn : n = (⟨a0.bv >>> 8⟩ : U64) &&& 255#u64) (hdp : depth = (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64)
    (hmr : mr = (⟨a0.bv >>> 24⟩ : U64) &&& 15#u64) (hcr : cr = (⟨a0.bv >>> 28⟩ : U64) &&& 15#u64)
    (hat : attr = (⟨a0.bv >>> 32⟩ : U64) &&& 31#u64)
    (hdd : ∃ d : U64, d = 1099511627776#u64 ∧ dd = (a0 &&& d != 0#u64))
    (hcn : ∃ x, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok cnode)
    (hdcn : dcnode = cnode ∨ ∃ x, vspace.extra extra 1#usize = ok (some x) ∧ capAt (L.mem s) x = ok dcnode)
    (hbc : b.cnode = absCap cnode) (hbd : b.destCnode = absCap dcnode)
    (hcnC : ∃ a b d e, cnode = .CNode a b d e) (hdc6 : Fl4Spec.isCnodeCap (absCap dcnode) = true)
    (hbe : b.entries = Fl4Spec.fbEntries (args.map UScalar.bv) b.op.words n.val)
    (hln : 1 + words.val * n.val ≤ args.length)
    (hbv : b.vspace = p.bv) (hba : b.asid = asid.bv) :
    vspace.decode_frame_batch_loop st arI s ar buf ct n words p asid op depth mr cr attr dd cnode dcnode
        0#u64 false ⦃ r => ∃ (τ : Fl4Spec.State Unit) (Z1 : XSets) (H1 : P1.Heap) (Cs1 Ac1 : Set U64)
        (Lst1 : U64 → List U64) (D1 : Set U64),
      ((r.2.2.1.val, r.2.2.2.1.bv, r.2.2.2.2), τ) ∈ (Fl4Spec.fbRun (Z := Unit) b b.entries 0 false σ).1 ∧
      JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 r.1 r.2.1 τ ∧ τ.curThread = σ.curThread ∧
      ∀ x : Fl4Spec.Tcb, σ.kheap ct.bv = some (.tcb x) →
        ∃ y : Fl4Spec.Tcb, τ.kheap ct.bv = some (.tcb y) ∧ y.tcbState = x.tcbState ⦄ := by
  have hw3 : words.val ≤ 3 := by rw [hw]; cases b.op <;> decide
  have hn255 : n.val ≤ 255 := by rw [hn, UScalar.val_and]; exact Nat.le_trans Nat.and_le_right (by decide)
  unfold vspace.decode_frame_batch_loop
  apply loop.spec_decr_nat (measure := fun x => match x with | (_, _, d, _) => n.val - d.val)
    (inv := fun x => ∃ τ, FbMidJ (L := L) (AR := AR) arI σ ct buf args x.1 x.2.1 τ ∧ x.2.2.1.val ≤ n.val ∧
      ∀ y ∈ (Fl4Spec.fbRun (Z := Unit) b (b.entries.drop x.2.2.1.val) x.2.2.1.val x.2.2.2 τ).1,
        y ∈ (Fl4Spec.fbRun (Z := Unit) b b.entries 0 false σ).1)
  · rintro ⟨x0, x1, x2, x3⟩ ⟨τ, hM, hle, hpre⟩
    dsimp only at hM hle hpre
    unfold vspace.decode_frame_batch_loop.body
    dsimp only
    have harg : ∀ k : U64, (hk : k.val < args.length) → msg.syscall_arg st x0 ct buf k = ok args[k.val] :=
      fun k hk => hM.2.1 k _ (List.getElem?_eq_getElem hk)
    by_cases hd : x2 < n
    · rw [if_pos hd]
      have hx : x2.val < n.val := hd
      have hm : words.val * x2.val ≤ 3 * 255 := Nat.mul_le_mul hw3 (by omega)
      have hw1' : 1 ≤ words.val := by rw [hw]; cases b.op <;> decide
      have hk : 1 + words.val * (x2.val + 1) ≤ args.length :=
        le_trans (by have := Nat.mul_le_mul_left words.val (show x2.val + 1 ≤ n.val by omega); omega) hln
      step as ⟨i3, hi3⟩
      step as ⟨i4, hi4⟩
      have hi4' : i4.val = 1 + b.op.words * x2.val := by rw [hi4, hi3, hw]
      rw [harg i4 (by rw [Nat.mul_succ] at hk; omega)]
      simp only [bind_ok]
      refine WP.spec_bind (Pₘ := fun w1 : U64 => w1.bv = (if b.op.words > 1 then
          Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val + 1]? else 0)) ?_ ?_
      · by_cases h1 : words > 1#u64
        · have h1' : b.op.words > 1 := by rw [← hw]; scalar_tac
          rw [if_pos h1, if_pos h1']
          step as ⟨i5, hi5⟩
          rw [harg i5 (by rw [Nat.mul_succ] at hk; omega)]
          refine (WP.spec_ok _).2 ?_
          rw [fb_the_arg (i := 1 + b.op.words * x2.val + 1) (by rw [Nat.mul_succ] at hk; rw [← hw]; omega)]
          simp only [hi5, hi4']
        · have h1' : ¬ b.op.words > 1 := by rw [← hw]; scalar_tac
          rw [if_neg h1, if_neg h1']
          exact (WP.spec_ok _).2 rfl
      intro w1 hw1
      refine WP.spec_bind (Pₘ := fun w2 : U64 => w2.bv = (if b.op.words > 2 then
          Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val + 2]? else 0)) ?_ ?_
      · by_cases h2 : words > 2#u64
        · have h2' : b.op.words > 2 := by rw [← hw]; scalar_tac
          rw [if_pos h2, if_pos h2']
          step as ⟨i5, hi5⟩
          rw [harg i5 (by rw [Nat.mul_succ] at hk; omega)]
          refine (WP.spec_ok _).2 ?_
          rw [fb_the_arg (i := 1 + b.op.words * x2.val + 2) (by rw [Nat.mul_succ] at hk; rw [← hw]; omega)]
          simp only [hi5, hi4']
        · have h2' : ¬ b.op.words > 2 := by rw [← hw]; scalar_tac
          rw [if_neg h2, if_neg h2']
          exact (WP.spec_ok _).2 rfl
      intro w2 hw2
      have hdrop := fbEntries_drop (A := (args.map UScalar.bv : List Fl4Spec.Data)) (w := b.op.words) hx
      refine WP.spec_bind (fb_entryJ arI hA hT σ ct buf args p asid h0 b excaps hb a0 ha0 n words op depth mr cr attr
        dd cnode dcnode hop hw hn hdp hmr hcr hat hdd hbc hbd hcnC hdc6 hbv hba x0 x1 τ hM
        (Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val]?,
          if b.op.words > 1 then Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val + 1]? else 0,
          if b.op.words > 2 then Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val + 2]? else 0)
        _ w1 w2 (by rw [fb_the_arg (i := 1 + b.op.words * x2.val) (by rw [Nat.mul_succ] at hk; rw [← hw]; omega)]; simp only [hi4']) hw1 hw2 x3) ?_
      rintro ⟨r, s1, a1, d1⟩ ⟨τ1, hM1, hres⟩
      fbj_red
      rcases hres with ⟨hr, d', hmem, hd1⟩ | ⟨e, hr, hd1, hE⟩
      · try dsimp only at hr hd1
        subst hr
        fbj_red
        step as ⟨done2, hd2⟩
        try simp only [WP.spec_ok]
        try dsimp only
        refine ⟨⟨τ1, hM1, by omega, ?_⟩, by omega⟩
        intro y hy
        apply hpre
        rw [hbe] at hy ⊢
        rw [hdrop]
        rw [hd2] at hy
        try dsimp only at hd1
        rw [hd1] at hy
        exact fbRun_cons_ok hmem hy
      · try dsimp only at hr hd1
        subst hr
        fbj_red
        have hpost : ∀ c : U64, (.error c.bv, τ1) ∈ ((Fl4Spec.fbEntry (Z := Unit) b
            (Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val]?,
              if b.op.words > 1 then Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val + 1]? else 0,
              if b.op.words > 2 then Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[1 + b.op.words * x2.val + 2]? else 0)).run τ).1 →
            ∃ (τ : Fl4Spec.State Unit) (Z1 : XSets) (H1 : P1.Heap) (Cs1 Ac1 : Set U64) (Lst1 : U64 → List U64) (D1 : Set U64),
              ((x2.val, c.bv, d1), τ) ∈ (Fl4Spec.fbRun (Z := Unit) b b.entries 0 false σ).1 ∧
              JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 s1 a1 τ ∧ τ.curThread = σ.curThread ∧
              ∀ x : Fl4Spec.Tcb, σ.kheap ct.bv = some (.tcb x) →
                ∃ y : Fl4Spec.Tcb, τ.kheap ct.bv = some (.tcb y) ∧ y.tcbState = x.tcbState := by
          intro c hc
          obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩, -, hcur1, hct1⟩ := hM1
          refine ⟨τ1, Z1, H1, Cs1, Ac1, Lst1, D1, hpre _ ?_, J1, hcur1, hct1⟩
          rw [hbe, hdrop, hd1]
          exact fbRun_cons_err hc
        cases e with
        | Sys e1 =>
          refine WP.spec_bind hE ?_
          intro c hc
          exact (WP.spec_ok _).2 (hpost c hc)
        | _ => exact (WP.spec_ok _).2 (hpost _ hE)
    · rw [if_neg hd]
      have hxn : x2.val = n.val := by have : ¬ x2.val < n.val := hd; omega
      refine (WP.spec_ok _).2 ?_
      obtain ⟨⟨Z1, H1, Cs1, Ac1, Lst1, D1, J1⟩, -, hcur1, hct1⟩ := hM
      refine ⟨τ, Z1, H1, Cs1, Ac1, Lst1, D1, hpre _ ?_, J1, hcur1, hct1⟩
      rw [hbe, hxn, fbEntries_drop_n, ← hxn]
      exact fbRun_nil_mem b _ _ _
  · refine ⟨σ, ⟨⟨Z, H, Cs, Ac, Lst, D, J⟩, hargs, rfl, fun x hk => ⟨x, hk, rfl⟩⟩, by simp, fun y hy => ?_⟩
    simpa using hy

/-- Reassociating a bind under a spec. -/
theorem fb_assoc_spec {α β γ : Type} {m : Result α} {g : α → Result β} {k : β → Result γ} {P : γ → Prop}
    (h : ((m >>= g) >>= k) ⦃ x => P x ⦄) : (m >>= fun x => g x >>= k) ⦃ x => P x ⦄ := by
  rw [bind_assoc_eq] at h; exact h

set_option maxHeartbeats 8000000 in
/-- **The batch's loop and tail at `JAt`** (the decode's checks passed; module docstring): the
loop against `fbRun` from `σ`, moved to the spec's `Restart` by SpecFbRestart, the deferred
`invalidate_asid` against `flushAll`, the reply and `TS_RUNNING` by VsFbReply's `fbTail_inv`, `JAt`
after. -/
theorem fb_loopJ (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (h0 : asid ≠ 0#u64) (length buf : U64) (blk call don : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (hf : ExceptT.run (Fl4Spec.findVspaceForAsid (Z := Unit) asid.bv) σ = ({(.ok p.bv, σ)}, False))
    (b : Fl4Spec.Fl4FrameBatchInvocation)
    (hb : fbDecP p.bv asid.bv (args.map UScalar.bv) excaps = .ok b)
    (a0 : U64) (ha0 : args[0]? = some a0)
    (n words op depth mr cr attr : U64) (dd : Bool) (cnode dcnode : capability.Cap)
    (hop : op = a0 &&& vspace.frame_batch.OP) (hw : words.val = b.op.words)
    (hn : n = (⟨a0.bv >>> 8⟩ : U64) &&& 255#u64) (hdp : depth = (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64)
    (hmr : mr = (⟨a0.bv >>> 24⟩ : U64) &&& 15#u64) (hcr : cr = (⟨a0.bv >>> 28⟩ : U64) &&& 15#u64)
    (hat : attr = (⟨a0.bv >>> 32⟩ : U64) &&& 31#u64)
    (hdd : ∃ d : U64, d = 1099511627776#u64 ∧ dd = (a0 &&& d != 0#u64))
    (hcn : ∃ x, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok cnode)
    (hdcn : dcnode = cnode ∨ ∃ x, vspace.extra extra 1#usize = ok (some x) ∧ capAt (L.mem s) x = ok dcnode)
    (hbc : b.cnode = absCap cnode) (hbd : b.destCnode = absCap dcnode)
    (hcnC : ∃ a b d e, cnode = .CNode a b d e) (hdc6 : Fl4Spec.isCnodeCap (absCap dcnode) = true)
    (hbe : b.entries = Fl4Spec.fbEntries (args.map UScalar.bv) b.op.words n.val)
    (hln : 1 + words.val * n.val ≤ args.length)
    (hbv : b.vspace = p.bv) (hba : b.asid = asid.bv)
    (K : S × A × U64 × U64 × Bool → Result (core.result.Result Unit error.Exc × S × A))
    (hK : ∀ s1 a1 done1 err deferred, K (s1, a1, done1, err, deferred) = (do
    let a2 ← if deferred then arI.invalidate_asid a1 asid else ok a1
    let s2 ←
      if call
      then
        do
        let rbuf ← msg.lookup_ipc_buffer st s1 true ct
        let s3 ← obj.Tcb.set_reg st ct s1 layout.reg.BADGE 0#u64
        let (_, s4) ← msg.set_mr st s3 ct rbuf 0#u64 done1
        let (len, s5) ← msg.set_mr st s4 ct rbuf 1#u64 err
        let mi ← msginfo.MessageInfo.new 0#u64 0#u64 0#u64 len
        msg.set_msg_info st s5 ct mi
      else ok s1
    let s3 ← sched.set_thread_state st s2 ct sched.TS_RUNNING
    ok (core.result.Result.Ok (), s3, a2))) :
    (vspace.decode_frame_batch_loop st arI s ar buf ct n words p asid op depth mr cr attr dd cnode dcnode
        0#u64 false >>= K) ⦃ res =>
      TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
            (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv) (.pml4Cap p.bv (some asid.bv)) excaps)))
        ct s res ⦄ := by
  obtain ⟨hcur, x, hk, hrun⟩ := J.curRunnable hni hct
  have hfd := decodeFrameBatch_run (args := args.map UScalar.bv) (ex := excaps) hf
  have hDs : ExceptT.run (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
      (.pml4Cap p.bv (some asid.bv)) excaps) σ = ({(.ok b, σ)}, False) := by rw [hfd, hb]
  refine WP.spec_bind (fb_loopI arI s ar σ J hni hA hT ct hct p asid h0 length buf args hlen hargs extra excaps
    hXO hXN hf b hb a0 ha0 n words op depth mr cr attr dd cnode dcnode hop hw hn hdp hmr hcr hat hdd hcn hdcn
    hbc hbd hcnC hdc6 hbe hln hbv hba) ?_
  rintro ⟨s1, a1, d1, e1, df⟩ ⟨τ, Z1, H1, Cs1, Ac1, Lst1, D1, hrun1, J1, hcurτ, hy⟩
  obtain ⟨y, hky, hys⟩ := hy x hk
  rw [hK]
  -- the deferred invalidation
  have hflush : (if df then arI.invalidate_asid a1 asid else ok a1) ⦃ a2 => ∃ τ',
      ((), τ') ∈ (Fl4Spec.NonDet.when (df = true) (Fl4Spec.flushAll (Z := Unit) b.vspace b.asid) τ).1 ∧
      τ'.kheap = τ.kheap ∧ τ'.curThread = τ.curThread ∧ JAtZ (L := L) arI AR Z1 H1 Cs1 Ac1 Lst1 D1 s1 a2 τ' ⦄ := by
    cases df
    · simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
      refine ⟨τ, ?_, rfl, rfl, J1⟩
      unfold Fl4Spec.NonDet.when; rw [if_neg (by decide)]; rfl
    · simp only [↓reduceIte]
      refine WP.spec_mono (J1.fbFlushJ arI hA b.vspace asid) ?_
      rintro a2 ⟨τ', hτ', hkh, hct', J2⟩
      refine ⟨τ', ?_, hkh, hct', J2⟩
      unfold Fl4Spec.NonDet.when; rw [if_pos trivial, hba]; exact hτ'
  refine WP.spec_bind hflush ?_
  rintro a2 ⟨τ', hτ', hkh, hct', J2⟩
  -- the spec's batch, then moved after its `Restart`
  have hd : BitVec.ofNat 64 d1.val = d1.bv := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by scalar_tac)
  have hperf : ([d1.bv, e1.bv], τ') ∈ (Fl4Spec.performFrameBatch (Z := Unit) b σ).1 := by
    rw [← hd]
    unfold Fl4Spec.performFrameBatch
    exact ⟨_, hrun1, _, hτ', rfl⟩
  obtain ⟨y', hky', -, hperf1⟩ := SInv.performFrameBatch_restart b hk hperf
  have hky2 : τ'.kheap ct.bv = some (.tcb y) := by rw [hkh]; exact hky
  rw [hky2] at hky'
  simp only [Option.some.injEq, Fl4Spec.KernelObject.tcb.injEq] at hky'
  subst hky'
  have hrx : Fl4Spec.runnable y.tcbState = true := by rw [hys]; exact hrun
  have hcur' : τ'.curThread = ct.bv := hct'.trans (hcurτ.trans hcur)
  have htcb1 : Z1.th ct = some .tcb := (J2.xtop.curTcb hcur').1
  have hcT1 : ct ∈ Z1.T := J2.thT ct htcb1
  have hI2 : Vs.RInv (L := L) Z1.th Z1.P Z1.L4 Z1.L3 Z1.L2 Z1.L1 Z1.N Z1.T Z1.C Z1.E Z1.R Z1.B Z1.c AR Z1.G s1 a2 τ' :=
    ⟨J2.xtop.rel.2.1, J2.xtop.rel.2.2.1, J2.xtop.rel.2.2.2.2.1, J2.xtop.rel.2.2.2.1, J2.xtop.fin⟩
  -- the reply and `Running`
  refine fb_assoc_spec (WP.spec_bind (WP.spec_and (Vs.fbTail_inv s1 a2 τ' hI2 ct htcb1 hcur'.symm hky2 hrx
    J2.kern.act call d1 e1) (J2.fbTailJ arI hcT1 hky2 (runnable3 hrx) call d1 e1)) ?_)
  rintro s3 ⟨⟨hne, -, -⟩, Z3, H3, Cs3, Ac3, Lst3, D3, J3⟩
  refine (WP.spec_ok _).2 ?_
  exact Or.inr ⟨rfl, hne, _, DecOut.of_eq (run_liftME_ok (run_liftME_ok hDs)), _,
    by rw [hcur]; exact Notif.setThreadState_eq .restart hk, _, _, mem_liftE (ε := Unit) (x := (_, _)) hperf1,
    _, Vs.specTail_fb τ' ct hky2 call d1 e1, J3.xtop.relTop, ⟨_, _, _, _, _, _, J3⟩⟩


set_option maxHeartbeats 8000000 in
/-- **The FrameBatch label on a PML4 cap at `JAt`** (module docstring): the decode's checks against
SpecFbDec's `fbDecP`, the loop and tail by `fb_loopJ`. -/
theorem decode_invocation_pml4_fbJV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data) (hlb : lbl = fl4_abi.label.X86PML4FrameBatch)
    (hslb : Fl4Spec.dataToNat slbl = Fl4Spec.fl4FrameBatchLabel)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (h0 : mp = true → asid ≠ 0#u64) (length buf : U64) (blk call don fp : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Pml4 p mp asid) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  have hX := J.xtop
  have hR := hX.fin.2.1
  have hPl : Placed Z.th := J.xtop.rel.1
  have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J⟩
  have hnf : lbl ≠ fl4_abi.label.X86PML4Flush := by
    intro h
    have h1 : fl4_abi.label.X86PML4FrameBatch.val = 90 := by simp [fl4_abi.label.X86PML4FrameBatch]
    have h2 : fl4_abi.label.X86PML4Flush.val = 46 := by simp [fl4_abi.label.X86PML4Flush]
    rw [← h, hlb] at h2; omega
  have hnF : ¬ Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel := by
    rw [hslb]; decide
  refine Or.inr ?_
  unfold DecOKRMX syscall.decode_invocation
  rw [hct]; simp only [bind_ok]
  unfold vspace.decode
  rw [hct]; simp only [bind_ok]
  rw [if_neg hnf, if_pos hlb]
  have hspec : specDec fp slbl (args.map UScalar.bv) ci sl (.Pml4 p mp asid) excaps buffer =
      Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
          (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
            (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps)) := by
    show Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
      (Fl4Spec.fl4ArchDecodeInvocation (Z := Unit) slbl (args.map UScalar.bv) ci sl
        (.pml4Cap p.bv (if mp then some asid.bv else none)) excaps) = _
    unfold Fl4Spec.fl4ArchDecodeInvocation; dsimp only
    rw [if_neg hnF, if_pos hslb]
  rw [hspec]
  unfold vspace.decode_frame_batch
  rw [hct]; simp only [bind_ok]
  cases mp
  · simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    exact fb_err (L := L) (e := .Sys (.InvalidCapability 0#u64)) (e' := .invalidCapability 0) rfl (Or.inr ⟨0#u64, rfl, rfl⟩) hJ0
  simp only [↓reduceIte]
  have h0' := h0 rfl
  refine WP.spec_bind (check_vspace_fb s σ hR p asid h0') ?_
  rintro r (⟨rfl, hf⟩ | ⟨e, rfl, hdec⟩)
  swap
  · rw [fb_mapErr_err]
    simp only [bind_tc_ok, bind_ok, fb_branch_err, fb_fromResidual, WP.spec_ok]
    exact fb_err (L := L) (e := .Sys (.InvalidCapability 0#u64)) (e' := .invalidCapability 0) (hdec _ _)
      (Or.inr ⟨0#u64, rfl, rfl⟩) hJ0
  rw [fb_mapErr_ok]
  simp only [bind_tc_ok, bind_ok, fb_branch_ok]
  try simp only [WP.uncurry'_pair]
  try simp only [uncurry_apply_pair]
  try simp only [Aeneas.Std.uncurry]
  try dsimp only
  have hfd := decodeFrameBatch_run (args := args.map UScalar.bv) (ex := excaps) hf
  -- no header
  by_cases hl1 : length < 1#u64
  · simp only [hl1, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    have h1 : (args.map UScalar.bv).length < 1 := by rw [List.length_map, ← hlen]; scalar_tac
    exact fb_err (L := L) (e := .Sys .TruncatedMessage) (e' := .truncatedMessage) (by rw [hfd, fbDecP_short h1])
      (Or.inl trivial) hJ0
  simp only [hl1, ↓reduceIte]
  have h1 : ¬ (args.map UScalar.bv).length < 1 := by rw [List.length_map, ← hlen]; scalar_tac
  obtain ⟨a0, ha0⟩ : ∃ a0, args[0]? = some a0 := by
    cases h : args with
    | nil => rw [h] at h1; simp at h1
    | cons a r => exact ⟨a, rfl⟩
  have hhd : Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? = a0.bv := by
    rw [List.getElem?_map, ha0]; rfl
  rw [hargs 0#u64 a0 ha0]
  simp only [bind_ok, lift]
  rw [show vspace.frame_batch.COUNT_SHIFT = 8#u64 from (by unfold vspace.frame_batch.COUNT_SHIFT; rfl),
        show a0 >>> (8#u64 : U64) = ok ⟨a0.bv >>> 8⟩ from shr_u64_eq a0 8#u64 (by decide)]
  simp only [bind_ok, lift]
  rw [show vspace.frame_batch.DEPTH_SHIFT = 16#u64 from (by unfold vspace.frame_batch.DEPTH_SHIFT; rfl),
        show a0 >>> (16#u64 : U64) = ok ⟨a0.bv >>> 16⟩ from shr_u64_eq a0 16#u64 (by decide)]
  simp only [bind_ok, lift]
  refine WP.spec_bind (fb_words a0) ?_
  rintro words hw
  refine WP.spec_bind P0.Consts.vspace.frame_batch.DEFINED.spec ?_
  rintro i2 hi2
  try simp only [bind_ok, lift]
  have hdep : Fl4Spec.dataToNat ((a0.bv >>> 16) &&& 0x7f#64) =
      ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64).val := fb_and_val _ _
  have hnn : Fl4Spec.dataToNat ((a0.bv >>> 8) &&& 0xff#64) = ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64).val :=
    fb_and_val _ _
  have hIA : ∀ (hh : Fl4Spec.fbOpOf (Fl4Spec.dataToNat (a0.bv &&& 0x3#64)) = none ∨
      (a0.bv &&& ~~~Fl4Spec.fbDefined ≠ 0 ∨ Fl4Spec.dataToNat ((a0.bv >>> 16) &&& 0x7f#64) = 0 ∨
        Fl4Spec.dataToNat ((a0.bv >>> 16) &&& 0x7f#64) > 64)),
      TopPostRMX (L := L) (JAt (L := L) arI AR) σ blk call don
        (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4Invocation.invokeArchObject
          (Fl4Spec.NonDetE.liftME Fl4Spec.Fl4ArchInvocation.frameBatch
            (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv) (.pml4Cap p.bv (some asid.bv)) excaps)))
        ct s (.Err (.Sys (.InvalidArgument 0#u64)), s, ar) := fun hh =>
    fb_err (L := L) (e := .Sys (.InvalidArgument 0#u64)) (e' := .invalidArgument 0)
      (by rw [hfd, fbDecP_hdr h1 (by rw [hhd]; exact hh)]) (Or.inl rfl) hJ0
  -- reserved bits
  by_cases hd1 : ((a0 &&& ~~~i2) != 0#u64) = true
  · simp only [hd1, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inr (Or.inl ((fb_defined' a0 i2 hi2).1 hd1)))
  simp only [hd1, Bool.false_eq_true, ↓reduceIte]
  have hd1' : ¬ a0.bv &&& ~~~Fl4Spec.fbDefined ≠ 0 := fun h => hd1 ((fb_defined' a0 i2 hi2).2 h)
  rcases hw with ⟨rfl, hnone⟩ | ⟨op', hop', hwv, hw0, hcpy⟩
  · simp only [eq_self_iff_true, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inl hnone)
  simp only [hw0, ↓reduceIte]
  by_cases hd2 : (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64 = 0#u64
  · simp only [hd2, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inr (Or.inr (Or.inl (by rw [hdep, hd2]; rfl))))
  simp only [hd2, ↓reduceIte]
  by_cases hd3 : (⟨a0.bv >>> 16⟩ : U64) &&& 127#u64 > 64#u64
  · simp only [hd3, ↓reduceIte, error.invalid_arg, bind_ok, WP.spec_ok]
    exact hIA (Or.inr (Or.inr (Or.inr (by rw [hdep]; scalar_tac))))
  simp only [hd3, ↓reduceIte]
  have h2 : ¬ (Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? &&& ~~~Fl4Spec.fbDefined ≠ 0 ∨
      Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 16) &&& 0x7f#64) = 0 ∨
      Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 16) &&& 0x7f#64) > 64) := by
    rw [hhd, hdep]
    have : ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64).val ≠ 0 := fun h => hd2 (UScalar.eq_of_val_eq (by simpa using h))
    have : ¬ ((⟨a0.bv >>> 16⟩ : U64) &&& 127#u64).val > 64 := fun h => hd3 (by scalar_tac)
    tauto
  have hQ := fbDecP_some (p := p.bv) (asid := asid.bv) (ex := excaps) h1 (by rw [hhd]; exact hop') h2
  -- the entries' words
  have hwn : words.val * ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64).val ≤ 3 * 255 := by
    have : ((⟨a0.bv >>> 8⟩ : U64) &&& 255#u64).val ≤ 255 := by
      rw [UScalar.val_and]; exact Nat.le_trans Nat.and_le_right (by decide)
    have : words.val ≤ 3 := by rw [hwv]; cases op' <;> decide
    exact Nat.mul_le_mul (by assumption) (by assumption)
  step as ⟨i5, hi5⟩
  step as ⟨i6, hi6⟩
  by_cases hl2 : length < i6
  · simp only [hl2, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    have h3 : (args.map UScalar.bv : List Fl4Spec.Data).length < 1 + op'.words *
        Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 8) &&& 0xff#64) := by
      rw [List.length_map, hhd, hnn, ← hwv, ← hlen]; scalar_tac
    exact fb_err (L := L) (e := .Sys .TruncatedMessage) (e' := .truncatedMessage)
      (by rw [hfd, hQ]; unfold fbDecQ; rw [if_pos h3]) (Or.inl trivial) hJ0
  simp only [hl2, ↓reduceIte]
  have h3 : ¬ (args.map UScalar.bv : List Fl4Spec.Data).length < 1 + op'.words *
      Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 8) &&& 0xff#64) := by
    rw [List.length_map, hhd, hnn, ← hwv, ← hlen]; scalar_tac
  -- extra cap 0: the lookup CNode
  obtain ⟨hXl, hXs, hXz⟩ := hXO
  rw [vsExtra_at extra 0#usize (by decide) _ (exAt_idx0 extra)]
  simp only [bind_ok]
  by_cases hx0 : exAt extra 0 = 0#u64
  · simp only [hx0, ↓reduceIte, error.truncated, bind_ok, WP.spec_ok]
    have hl0 : excaps.length < 1 := by
      by_contra hn
      have := (srcOK_facts hPl (hXs 0 (by omega))).1
      exact this hx0
    exact fb_err (L := L) (e := .Sys .TruncatedMessage) (e' := .truncatedMessage)
      (by rw [hfd, hQ]; unfold fbDecQ; rw [if_neg h3, if_pos hl0]) (Or.inl trivial) hJ0
  simp only [hx0, ↓reduceIte]
  have hl0 : ¬ excaps.length < 1 := fun h => hx0 (hXz 0 (by omega) (by decide))
  obtain ⟨y0, rest, hy⟩ : ∃ y0 rest, excaps = y0 :: rest := by
    cases h : excaps with
    | nil => rw [h] at hl0; simp at hl0
    | cons a r => exact ⟨a, r, rfl⟩
  obtain ⟨-, -, -, cv, hcv, hy1, -, -, -⟩ := srcOK_facts hPl (hXs 0 (by omega))
  have hthe0 : (Fl4Spec.the excaps[0]?).1 = absCap cv := by subst hy; exact hy1
  rw [slot_cap_eq, hcv]
  simp only [bind_ok]
  cases cv
  case CNode cp cr cg cgs =>
    simp only [bind_ok, ↓reduceIte]
    have h5 : Fl4Spec.isCnodeCap (Fl4Spec.the excaps[0]?).1 = true := by rw [hthe0]; rfl
    have hcn : ∃ x, vspace.extra extra 0#usize = ok (some x) ∧ capAt (L.mem s) x = ok (.CNode cp cr cg cgs) :=
      ⟨exAt extra 0, by rw [vsExtra_at extra 0#usize (by decide) _ (exAt_idx0 extra), if_neg hx0], hcv⟩
    -- extra cap 1: the destination CNode (`dest_cnode`)
    rw [vsExtra_at extra 1#usize (by decide) _ (exAt_idx1 extra)]
    simp only [bind_ok]
    refine WP.spec_bind (show _ ⦃ dc => (dc = .CNode cp cr cg cgs ∨
        ∃ x, vspace.extra extra 1#usize = ok (some x) ∧ capAt (L.mem s) x = ok dc) ∧
        (if op' = .copyMap ∧ excaps.length > 1 then (Fl4Spec.the excaps[1]?).1
          else (Fl4Spec.the excaps[0]?).1) = absCap dc ⦄ from ?_) ?_
    · by_cases hx1 : exAt extra 1 = 0#u64
      · simp only [hx1, ↓reduceIte, WP.spec_ok]
        have hl1 : ¬ excaps.length > 1 := fun h => (srcOK_facts hPl (hXs 1 h)).1 hx1
        exact ⟨Or.inl (by first | rfl | trivial), by rw [if_neg (fun h => hl1 h.2)]; exact hthe0⟩
      simp only [hx1, ↓reduceIte]
      have hl1 : excaps.length > 1 := by
        by_contra hn
        exact hx1 (hXz 1 (by omega) (by decide))
      have hx1e : vspace.extra extra 1#usize = ok (some (exAt extra 1)) := by
        rw [vsExtra_at extra 1#usize (by decide) _ (exAt_idx1 extra), if_neg hx1]
      by_cases hcm : op' = .copyMap
      · have hcm' : a0 &&& vspace.frame_batch.OP = vspace.frame_batch.COPY_MAP := hcpy.2 hcm
        simp only [hcm', ↓reduceIte]
        obtain ⟨-, -, -, cv1, hcv1, hy11, -, -, -⟩ := srcOK_facts hPl (hXs 1 hl1)
        rw [slot_cap_eq, hcv1, WP.spec_ok]
        refine ⟨Or.inr ⟨_, hx1e, hcv1⟩, ?_⟩
        rw [if_pos ⟨hcm, hl1⟩, List.getElem?_eq_getElem hl1]; exact hy11
      · have hcm' : ¬ a0 &&& vspace.frame_batch.OP = vspace.frame_batch.COPY_MAP := fun h => hcm (hcpy.1 h)
        simp only [hcm', ↓reduceIte, WP.spec_ok]
        exact ⟨Or.inl (by first | rfl | trivial), by rw [if_neg (fun h => hcm h.1)]; exact hthe0⟩
    rintro dc ⟨hdcn, hdeq⟩
    refine WP.spec_bind (show _ ⦃ b1 => b1 = Fl4Spec.isCnodeCap (absCap dc) ⦄ from ?_) ?_
    · cases dc <;> first | exact rfl | (simp only [WP.spec_ok]; rfl) | (simp only [WP.spec_ok]; decide) | simp [WP.spec_ok, absCap, Fl4Spec.isCnodeCap]
    rintro b1 rfl
    by_cases h6 : Fl4Spec.isCnodeCap (absCap dc) = true
    swap
    · simp only [h6, Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
      have h6' : ¬ Fl4Spec.isCnodeCap (if op' = .copyMap ∧ excaps.length > 1 then (Fl4Spec.the excaps[1]?).1
          else (Fl4Spec.the excaps[0]?).1) = true := by rw [hdeq]; exact h6
      have hE : ExceptT.run (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
          (.pml4Cap p.bv (some asid.bv)) excaps) σ = ({(.error (.invalidCapability 2), σ)}, False) := by
        rw [hfd, hQ]; unfold fbDecQ; rw [if_neg h3, if_neg hl0, if_pos h5, if_neg h6']
      exact fb_err (L := L) (e := .Sys (.InvalidCapability 2#u64)) hE (Or.inr ⟨2#u64, rfl, rfl⟩) hJ0
    simp only [h6, ↓reduceIte]
    have h6' : Fl4Spec.isCnodeCap (if op' = .copyMap ∧ excaps.length > 1 then (Fl4Spec.the excaps[1]?).1
        else (Fl4Spec.the excaps[0]?).1) = true := by rw [hdeq]; exact h6
    have hb : fbDecP p.bv asid.bv (args.map UScalar.bv) excaps = .ok (fbDecB p.bv asid.bv (args.map UScalar.bv) excaps op') :=
      hQ.trans (fbDecQ_ok h3 hl0 h5 h6')
    rw [show vspace.frame_batch.MAP_RIGHTS_SHIFT = 24#u64 from (by unfold vspace.frame_batch.MAP_RIGHTS_SHIFT; rfl),
      show a0 >>> (24#u64 : U64) = ok ⟨a0.bv >>> 24⟩ from shr_u64_eq a0 24#u64 (by decide)]
    simp only [bind_ok, lift]
    rw [show vspace.frame_batch.CAP_RIGHTS_SHIFT = 28#u64 from (by unfold vspace.frame_batch.CAP_RIGHTS_SHIFT; rfl),
      show a0 >>> (28#u64 : U64) = ok ⟨a0.bv >>> 28⟩ from shr_u64_eq a0 28#u64 (by decide)]
    simp only [bind_ok, lift]
    rw [show vspace.frame_batch.ATTR_SHIFT = 32#u64 from (by unfold vspace.frame_batch.ATTR_SHIFT; rfl),
      show a0 >>> (32#u64 : U64) = ok ⟨a0.bv >>> 32⟩ from shr_u64_eq a0 32#u64 (by decide)]
    simp only [bind_ok, lift]
    refine WP.spec_bind P0.Consts.vspace.frame_batch.DEFER_DELETE_FLUSH.spec ?_
    rintro i13 hi13
    try simp only [bind_ok, lift]
    exact fb_loopJ arI s ar σ J hni hA hT ct hct p asid h0' length buf blk call don args hlen hargs extra excaps
      ⟨hXl, hXs, hXz⟩ hXN hf _ hb a0 ha0 _ words _ _ _ _ _ _ _ _ rfl hwv rfl rfl rfl rfl rfl
      ⟨i13, hi13, rfl⟩ hcn hdcn hthe0 hdeq ⟨_, _, _, _, rfl⟩ h6
      (by show Fl4Spec.fbEntries _ _ (Fl4Spec.dataToNat ((Fl4Spec.the (args.map UScalar.bv : List Fl4Spec.Data)[0]? >>> 8) &&& 0xff#64)) = _
          rw [hhd, hnn]
          try rfl)
      (by have h3' := h3; rw [List.length_map, hhd, hnn, ← hwv] at h3'; omega)
      rfl rfl _ (fun _ _ _ _ _ => rfl)
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte, error.invalid_cap, bind_ok, WP.spec_ok]
    have h5 : ¬ Fl4Spec.isCnodeCap (Fl4Spec.the excaps[0]?).1 = true := by
      rw [hthe0]
      intro h
      obtain ⟨_, _, _, _, he⟩ := fb_isCN h
      cases he
    have hE : ExceptT.run (Fl4Spec.decodeFrameBatch (Z := Unit) (args.map UScalar.bv)
        (.pml4Cap p.bv (some asid.bv)) excaps) σ = ({(.error (.invalidCapability 1), σ)}, False) := by
      rw [hfd, hQ]; unfold fbDecQ; rw [if_neg h3, if_neg hl0, if_neg h5]
    exact fb_err (L := L) (e := .Sys (.InvalidCapability 1#u64)) hE (Or.inr ⟨1#u64, rfl, rfl⟩) hJ0

set_option maxHeartbeats 4000000 in
/-- **A PML4 cap at `JAt`**, every label (module docstring). -/
theorem decode_invocation_pml4JV (s : S) (ar : A) (σ : Fl4Spec.State Unit)
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s ar σ) (hni : Entered σ) (hA : ArchRefines arI AR)
    (hT : P0.ArchTotal arI)
    (lbl : U64) (slbl : Fl4Spec.Data)
    (hlbl : Fl4Spec.dataToNat slbl = Fl4Spec.fl4Pml4FlushLabel ↔ lbl = fl4_abi.label.X86PML4Flush)
    (hlfb : Fl4Spec.dataToNat slbl = Fl4Spec.fl4FrameBatchLabel ↔ lbl = fl4_abi.label.X86PML4FrameBatch)
    (ct : U64) (hct : sched.cur_thread st s = ok ct)
    (p asid : U64) (mp : Bool) (h0 : mp = true → asid ≠ 0#u64) (length buf : U64) (blk call don fp : Bool)
    (args : List U64) (hlen : length.val = args.length)
    (hargs : ∀ (i : U64) x, args[i.val]? = some x → msg.syscall_arg st s ct buf i = ok x)
    (sl : Fl4Spec.CslotPtr) (hAs : AbsSlot Z.th sl) (hc : capAt (L.mem s) (cslotAddr sl) = ok (.Pml4 p mp asid))
    (extra : Aeneas.Std.Array obj.Slot 3#usize) (excaps : List (Fl4Spec.Cap × Fl4Spec.CslotPtr))
    (hXO : ExtraOK Z.th (L.mem s) extra excaps) (hXN : ExtraNamed Z.th (L.mem s) extra)
    (ci : Fl4Spec.CapRef) (buffer : Option Fl4Spec.ObjRef) :
    XCap (L := L) arI (JAt (L := L) arI AR) s ar σ lbl length (cslotAddr sl) (.Pml4 p mp asid) blk call don fp buf
      extra slbl (args.map UScalar.bv) ci sl excaps buffer ct := by
  by_cases hb : lbl = fl4_abi.label.X86PML4FrameBatch
  · exact decode_invocation_pml4_fbJV arI s ar σ J hni hA hT lbl slbl hb (hlfb.2 hb) ct hct p asid mp h0 length buf
      blk call don fp args hlen hargs sl hAs hc extra excaps hXO hXN ci buffer
  · exact decode_invocation_pml4JVn (st := st) (L := L) arI s ar σ J hni hA hT lbl slbl hlbl ⟨fun h => hb (hlfb.1 h), hb⟩ ct hct p asid
      mp h0 length _ buf blk call don fp extra _ ci sl excaps buffer

end

end

end Fl4Proofs.P3
