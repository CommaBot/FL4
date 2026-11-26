/-
# P2 (line invj, generation 7): the `acc` chain on the region-tagged read set `IoRSR`

Scripted copies (P2/InvDelPteIoR.lean's lemmas in place of the `IoPre` lemmas over `IoRS`):

* **`delFinR`** (invj gen 5's `delFinP`), **`truncAccR`** / **`truncFinR`** (invj gen 1's `truncAcc8` /
  `truncFin8`): the PTE-arm block's `FinOK` and the truncated block on a store reading `IoRSR s`;
* **`inv_acc_genR`** (stpost's `inv_acc_gen2`): the accepted run on a guarded store reading `IoRSR s` as `st`,
  given the decode block (`hblk`, with `FinOK` over `IoRSR s`) and the seen / invoked-slot words in `IoRSR s`.

`IoRSR ⊆ IoRSP` (`ioRSR_P`), so none of these reads an unlocked leaf entry. Heartbeats: `delFinR` and `truncFinR`
keep their sources' `maxHeartbeats 4000000` (`delFinP`, `truncFin8`). No named premise. New module; no existing
statement changes.
-/
import Fl4Proofs.P2.InvDelPteIoR
import Fl4Proofs.P2.InvTrunc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)

section finR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 4000000 in
/-- (invj gen 5) **`FinOK` after the CNodeDelete PTE-arm decode block** (stpost's `delFin`) (the I/O port's `io_hfin` route with the
Delete arm's slot writes): at an accepted run's post-prefix state `s2` (`InvChk`), a decode of the CNode cap at the
plan's slot at `CNodeDelete` with `length ≥ 2`, then `invRep`, reply `Ok ()` and leave `FinOK`. Inputs: `IoPre` and
`DelEnt` at the entry, the plan's slot a capability slot, the write set `W` covering the prefix words (`IoWr`) and
the caller's `STATE`. -/
theorem delFinR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSR st K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : W (stA (L.curW s)))
    (E : DelEntP st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (hvs : ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRd st K s asid va)
    (hlf : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → VsW K e)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRSR st K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, Cw, hcs, hlk, hdc, ⟨hA0, he, -, -⟩, hC, hcl, hWk, hd, -, -, hpv,
    hnx⟩ := E
  have hVe : VsW K e := hlf asid va e he
  have hX : ∀ b, (fun b => b = e) b → VsW K b := fun b hb => by subst hb; exact hVe
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.entR (Locks := Locks) hW
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => P.lay.slot8 q hq
  have w0 := prefix_writes ar hA P.tp P.np P.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact P.slot_keep w0 hq hbq hb
  -- the invoked cap is the CNode cap
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL hsl ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  -- the registers `R10`, `R8`
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
  -- the target lookup at `s2`
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
  -- the target's facts at `s2`
  have hdc2 : obj.Slot.cap st dest s2 = ok (.Frame fp .Small rt false true false asid va) := by
    rw [cap_agree hL hd ag]; exact hdc
  have hpv2 : L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s2 (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots := by
    rw [ag _ (slotW_of hL hd (by simp [layout.cte.PREV])) (slot_al hL hd (by simp [layout.cte.PREV])
      (by simp [layout.cte.PREV]))]
    exact fun h0 => (hpv h0).1
  have hnx2 : ∀ nx, obj.Slot.next st dest s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hd ag]; exact e) h0).1
  -- the scheduler facts at `s2` (io_hfin)
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hy2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s2 (L.curW s))] at ey; exact ok_inj_ff ey
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have A0 := Ent.acc
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  -- the slot words miss the node, the TCB fields and the SC words
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ SlotWX K (fun b => b = e) (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notSlotX hX ho
  have hmx : ¬ SlotWX K (fun b => b = e) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notSlotX hX (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : SlotOKX (L := L) K (fun b => b = e) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notSlotX hX (P.hT _ P.cT) h1 h2, hmx⟩
  -- the run
  have hu3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 → ∀ a' : A,
      vspace.unmap_page st ar x3 a' .Small asid va fp = unmapLeaf st ar x3 a' e asid va fp := by
    intro x3 hs3 a'
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    obtain ⟨hva, -, hV⟩ := hvs dest fp rt asid va hd hdc hA0
    refine unmap_pte ar (fun b hb => ?_) ?_ hV hva he a'
    · rw [L.read_eq, L.read_eq, K3.mem hb.1 (P.vs_notIoTW hb), w0.2.2 b hb.1 (P.vs_notPreW hb)]
    · rw [L.ks_base_eq, L.ks_base_eq, K3.1.1, w0.1]
  obtain ⟨hz2, kz⟩ := decDelP_keep ar hK O ha2 hrun hL hlen hlk2 hd hdc2 hA0 hu3 rfl (P.vs_notSlot hVe) hVe.1
    hpv2 hnx2 hy hz
  refine ⟨hz2, ?_⟩
  -- `Ω` cut to the SC words
  have hrh0 : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ K.heap.scs ∧
      InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (K.heap.scBits (L.mem s (scA (L.mem s (rhA (L := L) s)))))
        (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) := fun h0 => by
    obtain ⟨-, hc, -⟩ := bxi_rh P.bxi h0
    obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact ⟨hc, by omega, by omega⟩
  have F0' := I.F0.shrink P.cscS rfl hrh0
  have F2' := F0'.frame I.w
  have rh0' : RhSc st {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b} s := fun h0 => by
    obtain ⟨-, hc, ha⟩ := bxi_rh P.bxi h0
    obtain ⟨hW', hΩ⟩ := bxi_scin P.bxi hc ha
    exact ⟨_, hW', fun b hb hin => ⟨hΩ b hb hin, _, hc, hin⟩⟩
  have rh2' := rh0'.frame F0' I.w
  have Q0 := QOK.of_sw F2' rh2' I.tm
  rw [hct] at Q0
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b},
      ¬ SlotWX K (fun b => b = e) b := by
    rintro b ⟨-, c', hc', hin⟩
    exact P.sc_notSlotX hX (P.hSc _ hc') hin
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ SlotWX K (fun b => b = e) (tdA (L.mem s2 (tmA (L := L) s2))) := fun h0 => by
    unfold tdA
    exact P.tcb_notSlotX hX (I.tm h0) (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ SlotWX K (fun b => b = e) (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ SlotWX K (fun b => b = e) (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ SlotWX K (fun b => b = e) (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact P.tcb_notSlotX hX (F2'.rh h0).1 (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ SlotWX K (fun b => b = e) b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameEX w3 hn2 (fun t ht k h1 h2 => P.tcb_notSlotX hX ht (by omega) h2) ho'
  refine FinOK.of_sw hA (kz.1.1.trans I.k) (kz.1.2.1.trans I.cp) FIN.1 kz.2.1 Fz ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [hcur3]; exact SWr.of_W hsw)
  · rw [hcur3]
    exact (kz.tcbF hK O (k := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact kz.2.2
  · rw [hcur3]; exact A0.ryl
  · rw [hcur3]; exact A0.rst
  · rw [hcur3]; exact A0.rfi
  · rw [hcur3]; exact A0.wnx
  · rw [hcur3]; exact A0.rin


/-- (stpost gen 14) **The truncated Delete block on a store reading `IoRSR s` and the aligned user words as `st`**
(run-relative): the decode (no access beyond the current-thread read) and the error reply (`reply_error`: the
buffer lookup, `BADGE`, the buffer word, `MSG_INFO`). [J] `hbuf : InvBufJ8`. -/
theorem truncAccR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap} {cp cr cg cgb : U64}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hR : ∀ b, IoRSR st K Locks s b → R b) (hRu : ∀ b, UserW K b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWu : ∀ b, UserW K b → W b)
    (hcs : obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb)) (hsl : p.slot ∈ K.slots) (hbuf : InvBufJ8 (st := st) K s)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (hlen : length < 2#u64)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.entR (Locks := Locks) (P.ioWr (Locks := Locks))
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
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf b (by rw [← hlb]; exact eb) hne i hi
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.ndR (Locks := Locks) layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  rw [decode_cnode_eq ar, cnode_decode_trunc ar st hlen] at hy
  cases ok_inj_ff hy
  refine ⟨?_, fun z hz => ?_⟩
  · unfold syscall.decode_invocation
    rw [sched.cur_thread.guard (gS := gS) s2 hctR, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
    exact cnode_decode_trunc ar gS hlen
  · obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
    obtain ⟨hb1, hb2⟩ := P.lay.tslot _ (P.hT _ P.cT) _ bsl hbsl (by simp [layout.tcb.SLOT_BUFFER])
    have hbs := P.slotR (Locks := Locks) hb1 (Or.inl hb2)
    have hI : R (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
      hR _ (P.gateR (Locks := Locks) (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    have hlk := msg.lookup_ipc_buffer.guard (gS := gS) s2 true (L.curW s) hbsl hI (hR _ hbs.1) (hR _ hbs.2)
    unfold invRep at hz ⊢
    revert hz
    refine tr_bind (fun q e _ => ?_) (fun _ _ h => h)
    revert e
    exact tr_bind (fun s5 e _ => syscall.reply_error.guard_trunc8 (gS := gS) hlk (hW.reg _ rB384) (hW.reg _ rM384)
      (fun b eb hne i hi => ⟨hRu _ (hbuf2 b eb hne i hi), hWu _ (hbuf2 b eb hne i hi)⟩) e) (fun _ _ h => h)

set_option maxHeartbeats 4000000 in
/-- (stpost gen 14) **`FinOK` after the truncated Delete block** (delFin's route, with the buffer word an aligned
user word written instead of slot words): reply `Ok ()`. [J] `hbuf : InvBufJ8`. -/
theorem truncFinR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap} {cp cr cg cgb : U64}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSR st K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (hcs : obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb)) (hsl : p.slot ∈ K.slots) (hbuf : InvBufJ8 (st := st) K s)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap) (hlen : length < 2#u64)
    (hy : syscall.decode_invocation st ar s2 a1 fl4_abi.label.CNodeDelete length p.slot cap true true true false
      buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRSR st K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C
  have Ent := P.entR (Locks := Locks) hW
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
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf b (by rw [← hlb]; exact eb) hne i hi
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hy2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s2 (L.curW s))] at ey; exact ok_inj_ff ey
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact Ent.run
  have A0 := Ent.acc
  have hK0 := SchedOK.of_sw I.F (by rw [hct]; exact Hf.sc) (by rw [hct]; exact Hf.nr)
  rw [hct] at hK0
  have hK : SchedOK (L := L) s2 (L.curW s) := hK0
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW K (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact P.node_notUser ho
  have hmx : ¬ UserW K (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1
  have O : UsrOK (L := L) K s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => P.tcb_notUser (P.hT _ P.cT) h1 h2, hmx⟩
  obtain ⟨hz2, kz⟩ := truncRun8 ar hK O ha2 hrun hlen hbuf2 hy hz
  refine ⟨hz2, ?_⟩
  have hrh0 : L.mem s (rhA (L := L) s) ≠ 0#u64 → L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ K.heap.scs ∧
      InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (K.heap.scBits (L.mem s (scA (L.mem s (rhA (L := L) s)))))
        (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) := fun h0 => by
    obtain ⟨-, hc, -⟩ := bxi_rh P.bxi h0
    obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact ⟨hc, by omega, by omega⟩
  have F0' := I.F0.shrink P.cscS rfl hrh0
  have F2' := F0'.frame I.w
  have rh0' : RhSc st {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b} s := fun h0 => by
    obtain ⟨-, hc, ha⟩ := bxi_rh P.bxi h0
    obtain ⟨hW', hΩ⟩ := bxi_scin P.bxi hc ha
    exact ⟨_, hW', fun b hb hin => ⟨hΩ b hb hin, _, hc, hin⟩⟩
  have rh2' := rh0'.frame F0' I.w
  have Q0 := QOK.of_sw F2' rh2' I.tm
  rw [hct] at Q0
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ UserW K b := by
    rintro b ⟨-, c', hc', hin⟩
    exact P.sc_notUser (P.hSc _ hc') hin
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ UserW K (tdA (L.mem s2 (tmA (L := L) s2))) := fun h0 => by
    unfold tdA
    exact P.tcb_notUser (I.tm h0) (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ UserW K (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ UserW K (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ UserW K (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact P.tcb_notUser (F2'.rh h0).1 (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ UserW K b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameU w3 hn2 (fun t ht k h1 h2 => P.tcb_notUser ht (by omega) h2) ho'
  refine FinOK.of_sw hA (kz.1.1.trans I.k) (kz.1.2.1.trans I.cp) FIN.1 kz.2.1 Fz ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    (by rw [hcur3]; exact hsw)
  · rw [hcur3]
    exact (kz.tcbF hK O (k := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact kz.2.2
  · rw [hcur3]; exact A0.ryl
  · rw [hcur3]; exact A0.rst
  · rw [hcur3]; exact A0.rfi
  · rw [hcur3]; exact A0.wnx
  · rw [hcur3]; exact A0.rin



end finR

section accR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **The accepted run on a guarded store `gS` reading `IoRSR s` as `st` and writing a set `W` the prefix's words lie
in (`IoWr`)**, from the entry facts, [J] `hSeen`, [J] `hps` and the decode block `hblk` on `gS`. -/
theorem inv_acc_genR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSR st K Locks s)]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (hSeen : ∀ x, SeenW p x → IoRSR st K Locks s x)
    (hps : IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS (IoRSR st K Locks s) W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  refine syscall.handle_invocation_local.guard_acc2 (gS := gS) ar (P.entR (Locks := Locks) hW).acc.nd
    (P.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1
    (P.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    (P.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (hW.reg _ (by simp [layout.reg.FAULT_IP]))
    ?_ (fun x => still_holds_congr p x (fun w hw => GRd.read (hSeen w hw) x)) hps hblk h
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (P.midR (Locks := Locks) (P.ioWr (Locks := Locks)) hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩



end accR

end Fl4Proofs.P2.PathObl
