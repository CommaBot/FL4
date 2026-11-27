/-
(slhuf gen 13) **128-word copy** of `InvCMTail.lean` (gen 12): stpost's 512-word `InvBufJ` is false at P3 states
(invj gen 1), so the buffer facts are the 128-word `InvBufJ8` (invj's InvTrunc8) and every declaration is renamed
with suffix `8`; `512` bounds are `128`. Otherwise verbatim.

# P2 (line slhuf, gen 12): the kernel tail after the Copy / Mint decode (`InvCMTailW` discharged)

F-once's [W] `InvCMTailW` (P2/InvCMDecOnce.lean): at an accepted Copy / Mint entry, for the decode's result and the
reply, (a) an `Ok` reply runs alike on `guard st (IoRS s) ⊤` and (b) `finish` after the reply does too.

* `invPostG_eq_invRep8` (`rfl` per result);
* (b) from F-fin's generic `cmFin8` (P2/InvCMFin.lean) at `gS := guard st (IoRS s) ⊤` (`W := ⊤`, so `IoWr` and the
  `STATE` write are trivial) and `syscall.finish.guard_resume`, as the last lines of `invTail.guard2`;
* (a) from F-fin's `cmDec8` (the decode's `Ok` result keeps `KeepU` at `KSU8 K` from the post-check state) and
  stpost's `invRep.guard_okS` (InvMove): the reply's reads (the caller's `STATE`, `SC`, `IN_QUEUE`, node words,
  the current SC's `REFILL_MAX`) are `IoRS s` words, unchanged by the decode and the reply registers;
* **`invCMTailW_of8`**: `InvCMTailW` at any `P` giving `IoPre`, `InvCMArm`, `CMEnt`, `p.slot ∈ K.slots` and
  [J] `InvBufJ8` (cmFin's, for the error reply's buffer words). No user word is read by the tail, so neither
  `hnul` nor a sender-side buffer fact is needed.

No existing statement changes.
-/
import Fl4Proofs.P2.InvCMDecOnce
import Fl4Proofs.P2.InvCMFin8
import Fl4Proofs.P2.InvMove
import Fl4Proofs.P2.InvTrunc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section tail
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem invPostG_eq_invRep8 {A : Type} (m : machine.Store S) (x : S) (a : A) (t : U64)
    (r : core.result.Result Unit error.Exc) : invPostG m x a t r = invRep m t x a r := by
  cases r <;> rfl

set_option maxHeartbeats 8000000 in
/-- (slhuf gen 12) **`InvCMTailW` discharged**: at a `P` entry with `IoPre`, the Copy / Mint label (`InvCMArm`),
the arm's entry facts (`CMEnt`), the plan's slot a capability slot and [J] `InvBufJ8`, the `Ok` reply and `finish`
after the reply run on `guard st (IoRS s) ⊤` as on `st`. -/
theorem invCMTailW_of8 {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64}
    {p : localinv.Plan} {K : KLayout} {Locks : S → U64 → Prop} {Cs Ω Sg Ac : Set U64} {P : S → Prop}
    (hPE : ∀ s, P s → IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits Ac s)
    (harm : ∀ s, P s → InvCMArm st s) (hE : ∀ s, P s → CMEnt st K Cs Locks p s)
    (hsl : ∀ s, P s → p.slot ∈ K.slots) (hbuf : ∀ s, P s → InvBufJ8 st K s) :
    InvCMTailW st ar number p K Locks P := by
  intro s a info nx s1 s2 a1 buf length cap r x a2 z hP _ emi C _ hcap hd hz
  have PE := hPE s hP
  have hl := harm s hP (L.curW s) info (cur_thread_ok s) emi
  have hz' : invRep st (L.curW s) x a2 r = ok z := by rw [← invPostG_eq_invRep8]; exact hz
  obtain ⟨cp, cr, cg, cgb, dest, x1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, Cw, hcs, hex, -, hlk,
    hrc, hlss, hsc, -, -, hC, hCr, hcl, hWk, hs1K, -, hdK, -, -, hsK, -, -, hnx⟩ := hE s hP
  have C0 := C
  obtain ⟨-, es1, eu, eac, ey, ehere, -⟩ := C0
  have Ent := PE.ent (Locks := Locks) (PE.ioWr (Locks := Locks))
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA Ent es1 eu Hf.sc
  have hct : L.curW s2 = L.curW s := I.cur
  have hL : Slot8 K := fun q hq => PE.lay.slot8 q hq
  have w0 := prefix_writes ar hA PE.tp PE.np PE.cT es1 eu
  have ag : ∀ b, SlotW K b → Aligned b → L.mem s2 b = L.mem s b := fun b hs hb => by
    obtain ⟨q, hq, hbq⟩ := hs
    exact PE.slot_keep w0 hq hbq hb
  -- the invoked cap is the CNode cap
  have hcap' : cap = .CNode cp cr cg cgb := by
    rw [cap_agree hL (hsl s hP) ag, hcs] at hcap; exact (ok_inj_ff hcap).symm
  subst hcap'
  -- the registers `R10`, `R8`, `R9`, `R15`
  have tk : ∀ k : U64, k.val < 4096 → k.val % 8 = 0 → k.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) k) = L.mem s (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 h3 => w0.2.2 _ (field_aligned PE.tA h1 h2) (preW_tcb PE.tA PE.np PE.cT h1 h3)
  have r10 : L.mem s2 (regA (L.curW s) layout.reg.R10) = L.mem s (regA (L.curW s) layout.reg.R10) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R10) (by simp [layout.reg.R10])
      (by simp [layout.reg.R10]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r8 : L.mem s2 (regA (L.curW s) layout.reg.R8) = L.mem s (regA (L.curW s) layout.reg.R8) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R8) (by simp [layout.reg.R8])
      (by simp [layout.reg.R8]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r9 : L.mem s2 (regA (L.curW s) layout.reg.R9) = L.mem s (regA (L.curW s) layout.reg.R9) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R9) (by simp [layout.reg.R9])
      (by simp [layout.reg.R9]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r15 : L.mem s2 (regA (L.curW s) layout.reg.R15) = L.mem s (regA (L.curW s) layout.reg.R15) := by
    have e := reg_keepK (st := st) PE.tA (r := layout.reg.R15) (by simp [layout.reg.R15])
      (by simp [layout.reg.R15]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  -- the lookups at `s2`
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hCn' : ∀ p1 r1 gs1 g1, capability.Cap.CNode cp cr cg cgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hC
  have hCr' : ∀ p1 r1 gs1 g1, capability.Cap.CNode rp rr rg rgb = .CNode p1 r1 gs1 g1 → Cw p1 r1 := by
    intro p1 r1 gs1 g1 e; cases e; exact hCr
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
  have hlss2 : cspace.lookup_source_slot st s2 (.CNode rp rr rg rgb) (L.mem s2 (regA (L.curW s) layout.reg.R9))
      (L.mem s2 (regA (L.curW s) layout.reg.R15)) = ok (.Ok src) := by
    rw [r9, r15]
    unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at hlss ⊢
    simp only [bind_ok, ↓reduceIte] at hlss ⊢
    by_cases d1 : L.mem s (regA (L.curW s) layout.reg.R15) < 1#u64
    · rw [if_pos d1] at hlss; simp at hlss
    rw [if_neg d1] at hlss ⊢
    by_cases d2 : L.mem s (regA (L.curW s) layout.reg.R15) > cspace.WORD_BITS
    · rw [if_pos d2] at hlss; simp at hlss
    rw [if_neg d2] at hlss ⊢
    unfold cspace.resolve_address_bits at hlss ⊢
    obtain ⟨res, eres, hl⟩ := bind_eq_ok hlss
    have eres' := rab_loop_congr2 st Cw slotK hcl 66 _ _ 65#u64 res (by simp) hCr' eres
    rw [eres']; simp only [bind_ok]; exact hl
  have hrc2 : obj.Slot.cap st x1 s2 = ok (.CNode rp rr rg rgb) := by
    rw [cap_agree hL hs1K ag]; exact hrc
  have hsc2 : obj.Slot.cap st src s2 = ok (.Frame fp sz rt d mp false asid va) := by
    rw [cap_agree hL hsK ag]; exact hsc
  have hnx2 : ∀ nx, obj.Slot.next st src s2 = ok nx → nx ≠ 0#u64 → nx ∈ K.slots := fun nx e h0 =>
    (hnx nx (by rw [← next_agree hL hsK ag]; exact e) h0).1
  have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
    lookup_buf_keep PE.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf s hP b (by rw [← hlb]; exact eb) hne i hi
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
  -- slot and user words miss the node, the TCB fields and the SC words
  have hn2 : ∀ o : U64, o.val < 4288 → ¬ UserW (KSU8 K) (L.nodeAt s2 (L.cpu s2) o) := fun o ho => by
    rw [I.cp, nodeAt_of_ksb I.k]; exact not_usu8 (PE.node_notUser ho) (PE.node_notSlot ho)
  have hmx : ¬ UserW (KSU8 K) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact not_usu8 (PE.sc_notUser (PE.hSc _ PE.cscS) I.F.q.2.2.2.1) (PE.sc_notSlot (PE.hSc _ PE.cscS) I.F.q.2.2.2.1)
  have htU : ∀ t, K.heap t = some .tcb → ∀ k : U64, 192 ≤ k.val → k.val < 4096 →
      ¬ UserW (KSU8 K) (core.num.U64.wrapping_add t k) := fun t ht k h1 h2 =>
    not_usu8 (PE.tcb_notUser ht h1 h2) (PE.tcb_notSlot ht h1 h2)
  have O : UsrOK (L := L) (KSU8 K) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => htU _ (PE.hT _ PE.cT) k h1 h2, hmx⟩
  have hy : syscall.decode_invocation st ar s2 a1 info.label length p.slot (.CNode cp cr cg cgb) true true true false
      buf p.extra = ok (r, x, a2) := by rw [decInv_eq_CN]; exact hd
  -- (b) `FinOK` at the read guard (`cmFin8`)
  have hWt : IoWr st (fun _ : U64 => True) K.heap.scBits s :=
    ⟨fun _ _ _ => trivial, fun _ _ => trivial, fun _ _ _ => trivial, trivial⟩
  obtain ⟨-, F⟩ := cmFin8 (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) hA PE hWt
    (SWr.of_W trivial) (hE s hP) (hsl s hP) (hbuf s hP) hl C hcap hy hz'
  have hNd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) ∧ True := fun o h1 h2 => ⟨(PE.nd o h1 h2).1, trivial⟩
  refine ⟨fun hr => ?_, fun y hy' => ?_⟩
  swap
  · rw [syscall.finish.guard_resume ar z.1 z.2.1 (nd_at hNd F.k F.c) F.nd F.td F.rs F.ha F.hsw F.hfr F.hact F.hvc]
    exact hy'
  -- (a) the `Ok` reply
  subst hr
  rw [invPostG_eq_invRep8]
  have hy2 := hy
  rw [decode_cnode_eq ar] at hy2
  have hex' : Aeneas.Std.Array.index_usize p.extra 0#usize = ok x1 := hex
  rcases cmDec8 ar hK O ha2 hrun hL hl hlk2 hdK hex' hrc2 hlss2 hsc2 hsK hnx2 hy2 with ⟨-, kx⟩ | ⟨e, hr1, -⟩
  swap
  · cases hr1
  have Fx := kx.sched hK O
  have rst := PE.stw (Locks := Locks)
  have rsc : IoRS (st := st) K Locks s (scA (L.curW s)) :=
    PE.gate (off := 3464#u64) PE.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRS (st := st) K Locks s (inqA (L.curW s)) :=
    (PE.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRS (st := st) K Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts PE.bxi.2.2.1.1 PE.cscS
    exact PE.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2' : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  refine invRep.guard_okS (gS := PathObl.guard st (IoRS (st := st) K Locks s) (fun _ => True)) rst.1
    (SWr.of_W trivial) rsc riq trivial trivial ?_ hz'
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
  have hn5 : ∀ o, L.nodeAt s5 (L.cpu s5) o = L.nodeAt s (L.cpu s) o := fun o => (k5'.node o).trans (hnd2 o)
  refine ⟨⟨?_, ?_, trivial⟩, ?_⟩
  · rw [hn5]
    exact (PE.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  · rw [hn5]
    exact (PE.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION])
      (by simp [layout.node.SCHED_ACTION])).1
  · have e6 : L.mem (L.wr s5 (stA (L.curW s)) sched.TS_RUNNING) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      k6.tcbF hK O (k := 3464#u64) (by simp) (by simp) (by simp)
    rw [e6, hsc2']; exact hmxR

end tail

end Fl4Proofs.P2.PathObl
