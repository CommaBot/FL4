/-
# P2 (line invj, generation 5): the CNodeDelete **PTE-arm** decode block on the guarded store (`delAccP`)

stpost's `delAcc` (P2/InvBlk.lean) for a mapped small RAM frame cap with a non-zero ASID whose leaf `e` the plan
locked (`DelEntP`). The frame finalisation is `unmap_page`; on a store reading `IoRS s` (every `VsW` word is
there, `VsW.ioRS`) and writing `e` it is `unmapLeaf` at `e` on both stores (`unmap_pte`, `unmapLeaf.guard`), so
it runs as on `st`; then `empty_slot` at `unmap_page`'s state, whose slot words are the decode state's (`e` is no
slot word).

* `finCap_frame_pte_any`, `finImm_frame_pte_any` (any store), `cdt.finalise_slot_immediate.guard_frameP`,
  `cdt.delete.guard_frameP`;
* **`delAccP`**: the decode and the reply run on any store reading `IoRS s` and writing a superset of `IoWS s` and
  of the locked `VsW` words (`hWe`) as on `st`.

No named premise (`hvs` / `hlf` as in `delFinP`; `hWe` is the write set's obligation, met by the ownP path's write
set, rule 8). No existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteFinOK
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section any
variable {S : Type} {A : Type} (ar : machine.Arch A)

/-- `finalise_cap` of a mapped non-device non-EPT small frame cap with a non-zero ASID, on any store. -/
theorem finCap_frame_pte_any (m : machine.Store S) {x x1 : S} {a a1 : A} {fp rt asid va : U64} {fin : Bool}
    (hA : asid ≠ 0#u64) (hu : vspace.unmap_page m ar x a .Small asid va fp = ok (x1, a1)) :
    objects.finalise_cap m ar x a (.Frame fp .Small rt false true false asid va) fin false =
      ok ((.Null, .Null), x1, a1) := by
  have hA' : (asid != 0#u64) = true := by simpa using hA
  unfold objects.finalise_cap objects.finalise_cap_object
  simp only [bind_ok, ↓reduceIte, hA', Bool.false_eq_true, hu]
  cases fin <;> simp only [Bool.false_eq_true, ↓reduceIte, uncurry_apply_pair] <;> rw [hu] <;>
    simp only [bind_ok, uncurry_apply_pair]

set_option maxHeartbeats 4000000 in
/-- `finalise_slot_immediate` on a slot holding such a frame cap, on any store whose finality check returns. -/
theorem finImm_frame_pte_any (m : machine.Store S) {x x1 : S} {a a1 : A} {slot fp rt asid va : U64} {fin : Bool}
    (hc : obj.Slot.cap m slot x = ok (.Frame fp .Small rt false true false asid va)) (hA : asid ≠ 0#u64)
    (hf : cdt.is_final_capability_with_cap m x slot (.Frame fp .Small rt false true false asid va) = ok fin)
    (hu : vspace.unmap_page m ar x a .Small asid va fp = ok (x1, a1)) :
    cdt.finalise_slot_immediate m ar x a slot = ok (.Ok { success := true, cleanup := .Null }, x1, a1) := by
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop
  rw [loop]
  have hfu : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_ex_fd (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  have hb : cdt.finalise_slot_immediate_loop.body m ar slot x a layout.WALK_FUEL =
      ok (ControlFlow.done (.Ok { success := true, cleanup := .Null }, x1, a1)) := by
    unfold cdt.finalise_slot_immediate_loop.body
    simp only [hfu, ↓reduceIte, hv, bind_ok, hc, capability.Cap.is_null, Bool.false_eq_true, hf,
      finCap_frame_pte_any ar m hA hu, cdt.cap_removable, uncurry_apply_pair]
  dsimp only
  rw [hb]
  simp only [bind_ok]

end any

section g
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
  [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **`finalise_slot_immediate` of a mapped frame slot on the guarded store**, run-relative. -/
theorem cdt.finalise_slot_immediate.guard_frameP {x : S} {a : A} {slot fp rt asid va : U64}
    (hc : obj.Slot.cap st slot x = ok (.Frame fp .Small rt false true false asid va)) (hA : asid ≠ 0#u64)
    (hug : vspace.unmap_page gS ar x a .Small asid va fp = vspace.unmap_page st ar x a .Small asid va fp)
    (r0 : R slot) (r8 : R (core.num.U64.wrapping_add slot 8#u64))
    (hfg : cdt.is_final_capability_with_cap gS x slot (.Frame fp .Small rt false true false asid va) =
      cdt.is_final_capability_with_cap st x slot (.Frame fp .Small rt false true false asid va))
    {y : core.result.Result cdt.Finalised error.Exc × S × A}
    (h : cdt.finalise_slot_immediate st ar x a slot = ok y) :
    cdt.finalise_slot_immediate gS ar x a slot = ok y := by
  obtain ⟨x1, a1, hu, ey⟩ := finImm_frame_pte ar hc hA h
  subst ey
  unfold cdt.finalise_slot_immediate cdt.finalise_slot_immediate_loop at h
  rw [loop] at h
  obtain ⟨cf, hb, -⟩ := bind_eq_ok h
  have hfu : layout.WALK_FUEL > 0#u64 := by simp [layout.WALK_FUEL, U64.rMax]
  obtain ⟨v, hv, -⟩ := spec_ex_fd (U64.sub_spec (x := layout.WALK_FUEL) (y := 1#u64)
    (by simp [layout.WALK_FUEL, U64.rMax]))
  unfold cdt.finalise_slot_immediate_loop.body at hb
  simp only [hfu, ↓reduceIte, hv, bind_ok, hc, capability.Cap.is_null, Bool.false_eq_true] at hb
  obtain ⟨fin, efin, -⟩ := bind_eq_ok hb
  exact finImm_frame_pte_any ar gS (by rw [obj.Slot.cap.guard (gS := gS) slot x r0 r8]; exact hc) hA
    (by rw [hfg]; exact efin) (by rw [hug]; exact hu)

/-- **Deleting a mapped frame slot on the guarded store**, run-relative (given `empty_slot` transfers at
`unmap_page`'s states). -/
theorem cdt.delete.guard_frameP {x : S} {a : A} {dest fp rt asid va : U64}
    (hc : obj.Slot.cap st dest x = ok (.Frame fp .Small rt false true false asid va)) (hA : asid ≠ 0#u64)
    (hug : vspace.unmap_page gS ar x a .Small asid va fp = vspace.unmap_page st ar x a .Small asid va fp)
    (r0 : R dest) (r8 : R (core.num.U64.wrapping_add dest 8#u64))
    (hfg : cdt.is_final_capability_with_cap gS x dest (.Frame fp .Small rt false true false asid va) =
      cdt.is_final_capability_with_cap st x dest (.Frame fp .Small rt false true false asid va))
    (hes : ∀ x1 a1, vspace.unmap_page st ar x a .Small asid va fp = ok (x1, a1) →
      ∀ y', cdt.empty_slot st ar x1 a1 dest .Null = ok y' → cdt.empty_slot gS ar x1 a1 dest .Null = ok y')
    {y : core.result.Result Unit error.Exc × S × A}
    (h : cdt.delete st ar x a dest true = ok y) : cdt.delete gS ar x a dest true = ok y := by
  unfold cdt.delete at h ⊢
  simp only [↓reduceIte] at h ⊢
  obtain ⟨y1, hf, -⟩ := bind_eq_ok h
  obtain ⟨x1, a1, hu, ey⟩ := finImm_frame_pte ar hc hA hf
  subst ey
  rw [cdt.finalise_slot_immediate.guard_frameP ar hc hA hug r0 r8 hfg hf]
  rw [hf] at h
  simp only [bind_ok, uncurry_apply_pair, core.result.Result.Insts.CoreOpsTry.branch] at h ⊢
  revert h
  exact tr_bind (fun y' e _ => hes x1 a1 hu y' e) (fun _ _ h => h)

end g

section acc
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 2000000 in
/-- (invj gen 5) **The PTE-arm Delete decode and its reply on any store reading `IoRS s` and writing a superset
of `IoWS s` and the locked `VsW` words** run as on `st` (run-relative), at an entry with `IoPre` and `DelEnt`, after the prefix and checks
(`InvChk`), for a message of length at least 2. -/
theorem delAccP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWS (st := st) K Locks s b → W b)
    (E : DelEntP st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (hvs : ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRd st K s asid va)
    (hlf : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → VsW K e)
    (hWe : ∀ b, VsW K b → Locks s b → W b)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, Cw, hcs, hlk, hdc, ⟨hA0, he, -, hle⟩, hC, hcl, hWk, hd, hdO, hLd,
    hpv, hnx⟩ := E
  have hVe : VsW K e := hlf asid va e he
  have hX : ∀ b, (fun b => b = e) b → VsW K b := fun b hb => by subst hb; exact hVe
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.ent (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned P.tA h1 h2) (preW_tcb P.tA P.np P.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r8 : L.mem s2 (regA (L.curW s) layout.reg.R8) = L.mem s (regA (L.curW s) layout.reg.R8) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
      (by simp [layout.reg.R8]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode cp cr cg cgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s) layout.reg.R10))
      (L.mem s2 (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) := by
    rw [r10, r8]
    unfold cspace.lookup_target_slot cspace.lookup_slot_for_cnode_op at hlk ⊢
    simp only [bind_ok, ↓reduceIte] at hlk ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R8) < 1#u64
    · rw [if_pos d1] at hlk; simp at hlk
    rw [if_neg d1] at hlk ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R8) > cspace.WORD_BITS
    · rw [if_pos d2] at hlk; simp at hlk
    rw [if_neg d2] at hlk ⊢
    unfold cspace.resolve_address_bits at hlk ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlk
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCn' eres
    rw [eres']; simp only [bind_ok]; exact hl
  have hdc2 : obj.Slot.cap st dest s2 = ok (.Frame fp .Small rt false true false asid va) := by
    rw [cap_agree hL hd ag]; exact hdc
  have hpv2 : L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots := by
    rw [ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))]
    exact fun h0 => (hpv h0).1
  have hnx2 : ∀ nx, obj.Slot.next st dest s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hd ag]; exact e) h0).1
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ SlotW K (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notSlot ho
  have hmxS : ¬ SlotW K (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : SlotOK (L := L) K s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notSlot (P.hT _ P.cT) h1 h2, hmxS⟩
  have O' : SlotOKX (L := L) K (fun b => b = e) s2 (L.curW s) := by
    refine ⟨fun o ho => ?_, fun k h1 h2 => P.tcb_notSlotX hX (P.hT _ P.cT) h1 h2, ?_⟩
    · rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notSlotX hX ho
    · rw [← hct, I.F.i]; exact P.sc_notSlotX hX (P.hSc _ P.cscS) I.F.q.2.2.2.1
  -- the words
  have hLd' := hLd
  have hnT := notTcbSlot_of hdO
  have hnf := nof_of_frame_slot hdc
  have e0 : core.num.U64.wrapping_add dest 0#u64 = dest := wadd_zero (hL dest hd).2
  have dR : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → IoRS (st := st) K Locks s (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => (P.lockSlot hd hLd' ho h8).1
  have dW : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → W (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => hWs _ ((P.lockSlot hd hLd' ho h8).2 (Or.inr ⟨hnT, hnf⟩))
  have r0 : IoRS (st := st) K Locks s dest := by have := dR 0#u64 (by simp) (by simp); rwa [e0] at this
  have w0' : W dest := by have := dW 0#u64 (by simp) (by simp); rwa [e0] at this
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 =>
    (P.lockSlot hq hl ho h8).1
  have nW : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 → 16 ≤ o.val →
      W (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 h16 =>
    hWs _ ((P.lockSlot hq hl ho h8).2 (Or.inl h16))
  have nR0 : ∀ q, q ∈ K.slots → Locks s q → IoRS (st := st) K Locks s q := fun q hq hl => by
    have := nR q hq hl 0#u64 (by simp) (by simp); rwa [wadd_zero (hL q hq).2] at this
  -- the node, the caller's words
  have hctR : IoRS (st := st) K Locks s (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) →
      NodeSt (L := L) (IoRS (st := st) K Locks s) W x := by
    have n0 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact n0
    · rw [hn]; exact n1
    · rw [hn]; exact n1w
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  have rst := P.stw (Locks := Locks)
  have rsc : IoRS (st := st) K Locks s (scA (L.curW s)) :=
    P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K Locks s (inqA (L.curW s)) :=
    (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact P.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2 : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  -- the decode
  rw [decode_cnode_eq ar] at hy
  have hdg : syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot (.CNode cp cr cg cgb)
      true true true false buf p.extra = cnode.decode gS ar s2 a1 fl4_abi.label.CNodeDelete length
        (.CNode cp cr cg cgb) buf p.extra := by
    unfold syscall.decode_invocation
    rw [sched.cur_thread.guard (gS := gS) s2 hctR, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have hreg : ∀ i : U64, i.val < 2 → ∀ r, msg.msg_register i = ok r →
      IoRS (st := st) K Locks s (regA (L.curW s) r) := by
    intro i hi r hr
    unfold msg.msg_register at hr
    by_cases h0 : i = 0#u64
    · rw [if_pos h0] at hr; cases ok_inj_ff hr; exact (P.reg (by simp [layout.reg.R10])).1
    · rw [if_neg h0] at hr
      have h1 : i = 1#u64 := by
        apply UScalar.eq_of_val_eq
        have : i.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simp [e]))
        simp; omega
      rw [if_pos h1] at hr; cases ok_inj_ff hr; exact (P.reg (by simp [layout.reg.R8])).1
  have hRc2 : WalkRc (st := st) (IoRS (st := st) K Locks s) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact P.slot (hWk p r m y hp hm).1 (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  have hRd : IoRS (st := st) K Locks s dest ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add dest 8#u64) :=
    ⟨r0, dR 8#u64 (by simp) (by simp)⟩
  -- the frame finalisation: `unmap_page` is `unmapLeaf` at the plan's leaf on both stores
  have hr3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      ∀ b, VsW K b → st.read x3 b = st.read s b := fun x3 hs3 b hb => by
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    rw [L.read_eq, L.read_eq, K3.mem hb.1 (P.vs_notIoTW hb), w0.2.2 b hb.1 (P.vs_notPreW hb)]
  have hk3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      st.ks_base x3 = st.ks_base s := fun x3 hs3 => by
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    rw [L.ks_base_eq, L.ks_base_eq, K3.1.1, w0.1]
  have hu3S : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 → ∀ a' : A,
      vspace.unmap_page st ar x3 a' .Small asid va fp = unmapLeaf st ar x3 a' e asid va fp := by
    intro x3 hs3 a'
    obtain ⟨hva, -, hV⟩ := hvs dest fp rt asid va hd hdc hA0
    exact unmap_pte ar (hr3 x3 hs3) (hk3 x3 hs3) hV hva he a'
  have hug : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 → ∀ a' : A,
      vspace.unmap_page gS ar x3 a' .Small asid va fp = vspace.unmap_page st ar x3 a' .Small asid va fp := by
    intro x3 hs3 a'
    obtain ⟨hva, -, hV⟩ := hvs dest fp rt asid va hd hdc hA0
    rw [unmap_pte ar (fun b hb => (gst_read (VsW.ioRS (Locks := Locks) (s := s) hb)).trans (hr3 x3 hs3 b hb))
      (by rw [show gS.ks_base = st.ks_base from gst_ks_base]; exact hk3 x3 hs3) hV hva he a',
      unmapLeaf.guard ar x3 a' asid va fp (VsW.ioRS (Locks := Locks) (s := s) hVe) (hWe e hVe hle), hu3S x3 hs3 a']
  -- the deletion at the state after `set_thread_state RESTART`
  have hdel : ∀ s3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok s3 →
      ∀ y', cdt.delete st ar s3 a1 dest true = ok y' → cdt.delete gS ar s3 a1 dest true = ok y' := by
    intro s3 hs3 y' hy'
    have K3 : KeepA (L := L) s2 (L.curW s) s3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    have ag3 : ∀ b, SlotW K b → Aligned b → L.mem s3 b = L.mem s b := fun b hs hb =>
      (K3.mem hb (O.notT hK hs)).trans (ag b hs hb)
    have hc3 : obj.Slot.cap st dest s3 = ok (.Frame fp .Small rt false true false asid va) := by
      rw [cap_agree hL hd ag3]; exact hdc
    have ep3 : L.mem s3 (core.num.U64.wrapping_add dest layout.cte.PREV) =
        L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) :=
      ag3 _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
        (by simp [layout.cte.PREV]))
    have r16 := dR layout.cte.PREV (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])
    have r24 := dR layout.cte.NEXT (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
    have hfg : cdt.is_final_capability_with_cap gS s3 dest (.Frame fp .Small rt false true false asid va) =
        cdt.is_final_capability_with_cap st s3 dest (.Frame fp .Small rt false true false asid va) := by
      refine cdt.is_final_capability_with_cap.guard s3 dest _ r16 r24 (fun h0 => ?_) (fun nx e h0 => ?_)
      · rw [ep3] at h0 ⊢
        obtain ⟨hq, hl⟩ := hpv h0
        exact ⟨nR0 _ hq hl, nR _ hq hl 8#u64 (by simp) (by simp)⟩
      · rw [next_agree hL hd ag3] at e
        obtain ⟨hq, hl⟩ := hnx nx e h0
        exact ⟨nR0 _ hq hl, nR _ hq hl 8#u64 (by simp) (by simp)⟩
    refine cdt.delete.guard_frameP ar hc3 hA0 (hug s3 hs3 a1) r0 hRd.2 hfg (fun x1 a2 hu1 y'' he => ?_) hy'
    rw [hu3S s3 hs3] at hu1
    have ag1 : ∀ b, SlotW K b → Aligned b → L.mem x1 b = L.mem s b := by
      intro b hs hb
      rcases unmapLeaf_st ar hu1 with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ag3 b hs hb
      · rw [L.mem_wr_ne hVe.1 hb (fun hv => P.vs_notSlot hVe ((UScalar.eq_of_val_eq hv) ▸ hs))]
        exact ag3 b hs hb
    have ep1 : L.mem x1 (core.num.U64.wrapping_add dest layout.cte.PREV) =
        L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) :=
      ag1 _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
        (by simp [layout.cte.PREV]))
    refine cdt.empty_slot.guard_null ar r0 hRd.2 r16 r24 w0' (dW 8#u64 (by simp) (by simp))
      (dW 16#u64 (by simp) (by simp)) (dW 24#u64 (by simp) (by simp)) (fun h0 => ?_) (fun nx e h0 => ?_) he
    · rw [ep1] at h0 ⊢
      obtain ⟨hq, hl⟩ := hpv h0
      exact ⟨nR _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]),
        nW _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
    · rw [next_agree hL hd ag1] at e
      obtain ⟨hq, hl⟩ := hnx nx e h0
      exact ⟨nW _ hq hl _ (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]),
        nR _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]),
        nW _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
  have hmx2 : IoRS (st := st) K Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  refine ⟨?_, ?_⟩
  · rw [hdg]
    have h := hy
    unfold cnode.decode at h ⊢
    rw [if_neg lblD1, if_neg lblD2, if_neg hlen] at h ⊢
    rw [sched.cur_thread.guard (gS := gS) s2 hctR]
    rw [cur_thread_ok, hct] at h ⊢
    simp only [bind_ok] at h ⊢
    rw [msg.syscall_arg.guard_lt (gS := gS) s2 (L.curW s) buf 0#u64 (by simp [msg.N_MSG_REGISTERS])
        (hreg 0#u64 (by simp)),
      msg.syscall_arg.guard_lt (gS := gS) s2 (L.curW s) buf 1#u64 (by simp [msg.N_MSG_REGISTERS])
        (hreg 1#u64 (by simp))]
    rw [sarg0_reg, sarg1_reg, reg_ok, reg_ok] at h ⊢
    simp only [bind_ok] at h ⊢
    rw [hlk2] at h
    rw [cspace.lookup_target_slot.guardM (gS := gS) Cw hRc2 hcl2 hC hRd hlk2]
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lblD3, lblD4, ↓reduceIte] at h ⊢
    revert h
    rw [sched.set_thread_state.guard (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hWs _ rst.2) rst.1 rsc hmx2 riq]
    refine tr_bind_same (fun s3 hs3 => ?_)
    exact hdel s3 hs3 y
  · intro z hz'
    obtain ⟨hy1, kx⟩ := cnDelP_keep ar hK O' ha2 hrun hL hlen hlk2 hd hdc2 hA0 hu3S rfl (P.vs_notSlot hVe) hVe.1
      hpv2 hnx2 hy
    obtain ⟨r, x, a2⟩ := y
    simp only at hy1 kx hz' ⊢
    subst hy1
    have Fx := kx.sched hK O'
    refine invRep.guard_ok (gS := gS) rst.1 (hWs _ rst.2) rsc riq (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz'
    intro s5 es5
    have k5 : KeepA (L := L) x (L.curW s) s5 := by
      unfold msg.reply_success_empty at es5
      rw [set_reg_ok'] at es5; simp only [bind_ok] at es5
      obtain ⟨mi, -, es5⟩ := bind_eq_ok es5
      unfold msg.set_msg_info at es5
      obtain ⟨w, -, es5⟩ := bind_eq_ok es5
      rw [set_reg_ok'] at es5
      cases ok_inj_ff es5
      exact ((KeepA.refl kx.2.1 kx.2.2).wr_reg Fx rB384).wr_reg Fx rM384
    have k6 := kx.keepA (k5.wr Fx (b := stA (L.curW s)) (v := sched.TS_RUNNING) (Or.inr rfl) (fun _ => Or.inr rfl))
    have k5' := kx.keepA k5
    refine ⟨hN s5 (fun o => (k5'.node o).trans (hnd2 o)), ?_⟩
    have e6 : L.mem (L.wr s5 (stA (L.curW s)) sched.TS_RUNNING) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      k6.tcbF hK O' (k := 3464#u64) (by simp) (by simp) (by simp)
    rw [e6, hsc2]; exact hmxR

end acc

end Fl4Proofs.P2.PathObl
