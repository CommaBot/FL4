/-
# P2 (line unify, gen 2): the Copy / Mint `acc` chain on the region-tagged read set `IoRSR`

slhuf's Copy / Mint chain (`cmAccZ`, `cmFin8`, `inv_acc_gen3`) states its read facts for `IoRS s`, which holds the
leaf page-table entries (region `.none`). Scripted copies over invj's `IoRSR` (`IoRS` at words of a region other
than `.none` or kernel-global words, P2/InvDelPteIoR.lean), as invj gen 7 did for the Delete chain:

* **`cmAccZR`** (the decode block and reply on any store reading `R ⊇ IoRSR s` and the aligned user words);
* **`cmFin8R`** (`FinOK` over `IoRSR` after the block);
* **`inv_acc_gen3R`** (the accepted run on a guarded store reading `IoRSR s`, given the block).

Heartbeats: `cmAccZR` 4M (as `cmAccZ`); `cmFin8R` 4M (its source `cmFin8` carries 8M, the copy fits in 4M).
No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteAccR
import Fl4Proofs.P2.InvCMPathZ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section accZR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 4000000 in
/-- (unify gen 2) **slhuf's `cmAccZ` on a store reading `IoRSR s`** (and the aligned user words): scripted copy,
`IoRS` → `IoRSR`, the `IoPre` lemmas → their `…R` versions. -/
theorem cmAccZR {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hR : ∀ b, IoRSR st K Locks s b → R b) (hRu : ∀ b, UserW K b → R b)
    (hW : IoWr st W K.heap.scBits s) (hWu : ∀ b, UserW K b → W b)
    (hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) → W (core.num.U64.wrapping_add q o))
    (hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K q → NullOrFrame (L.mem s q) →
      ∀ x v, NullOrFrame v → gS.write x q v = st.write x q v)
    (hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr gS st (L.curW s) v)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots)
    (hz0 : CMDestZ st p s)
    (hbufC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation gS ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z → invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  obtain ⟨cp, cr, cg, cgb, dest, sx, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, Cw, hcs, he, hs10,
    hlk, hsc1, hls, hsrc, hdc0, hdn, hC, hC', hcl, hWk, hs1K, hs1O, hd, hdO, hLd, hsK, hsO, hLs, hnx⟩ := E
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
  have rk : ∀ r : U64, r.val < 384 → r.val ≠ 17 →
      L.mem s2 (regA (L.curW s) r) = L.mem s (regA (L.curW s) r) := fun r h1 h2 => by
    have e := reg_keepK (st := st) P.tA (r := r) h1 h2 tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r10 := rk layout.reg.R10 (by simp [layout.reg.R10]) (by simp [layout.reg.R10])
  have r8 := rk layout.reg.R8 (by simp [layout.reg.R8]) (by simp [layout.reg.R8])
  have r9 := rk layout.reg.R9 (by simp [layout.reg.R9]) (by simp [layout.reg.R9])
  have r15 := rk layout.reg.R15 (by simp [layout.reg.R15]) (by simp [layout.reg.R15])
  have slotK : ∀ p r, Cw p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s2 = obj.Slot.cap st (cnSlot p (x &&& m)) s :=
    fun p r hp m hm x => cap_agree hL (hWk p r m x hp hm).1 ag
  have hlk2 : cspace.lookup_target_slot st s2 (.CNode cp cr cg cgb) (L.mem s2 (regA (L.curW s2) layout.reg.R10))
      (L.mem s2 (regA (L.curW s2) layout.reg.R8)) = ok (.Ok dest) := by
    rw [hct, r10, r8]; exact lts_keep8 Cw slotK hcl hC hlk
  have hls2 : cspace.lookup_source_slot st s2 (.CNode rp rr rg rgb) (L.mem s2 (regA (L.curW s2) layout.reg.R9))
      (L.mem s2 (regA (L.curW s2) layout.reg.R15)) = ok (.Ok src) := by
    rw [hct, r9, r15]; exact lss_keep8 Cw slotK hcl hC' hls
  have hsc1' : obj.Slot.cap st sx s2 = ok (.CNode rp rr rg rgb) := by rw [cap_agree hL hs1K ag]; exact hsc1
  have hsrc2 : obj.Slot.cap st src s2 = ok (.Frame fp sz rt d mp false asid va) := by
    rw [cap_agree hL hsK ag]; exact hsrc
  have hRc2 : WalkRc (st := st) R s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    have h := P.slotR (Locks := Locks) (hWk p r m y hp hm).1 (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    exact ⟨hR _ h.1, hR _ h.2⟩
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  -- the slot words
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      R (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 => hR _ (P.lockSlotR hq hl ho h8)
  have nR0 : ∀ q, q ∈ K.slots → Locks s q → R q := fun q hq hl => by
    have := nR q hq hl 0#u64 (by simp) (by simp); rwa [wadd_zero (hL q hq).2] at this
  have hdR : R dest ∧ R (core.num.U64.wrapping_add dest 8#u64) := ⟨nR0 _ hd hLd, nR _ hd hLd 8#u64 (by simp) (by simp)⟩
  have hsR : SlotRd R src := ⟨nR0 _ hsK hLs, nR _ hsK hLs 8#u64 (by simp) (by simp),
    nR _ hsK hLs _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
  have hnR : ∀ n, obj.Slot.next st src s2 = ok n → n ≠ 0#u64 → SlotRd R n := by
    intro n e h0
    rw [next_agree hL hsK ag] at e
    obtain ⟨hq, hl⟩ := hnx n e h0
    exact ⟨nR0 _ hq hl, nR _ hq hl 8#u64 (by simp) (by simp),
      nR _ hq hl _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])⟩
  have hs1R : R sx ∧ R (core.num.U64.wrapping_add sx 8#u64) := by
    have h := P.slotR (Locks := Locks) hs1K (Or.inr (cap_not_nof hsc1 (Or.inl ⟨_, _, _, _, rfl⟩)))
    exact ⟨hR _ h.1, hR _ h.2⟩
  have hnT := notTcbSlot_of hdO
  have hnfd : NullOrFrame (L.mem s dest) := by
    have h0 := hz0 cp cr cg cgb dest hcs hlk
    have e0 : core.num.U64.wrapping_add dest layout.cte.CAP0 = dest := by
      apply UScalar.eq_of_val_eq
      rw [core.num.U64.wrapping_add_val_eq, Fl4Proofs.P0.Consts.layout.cte.CAP0.val_eq, Nat.add_zero]
      exact Nat.mod_eq_of_lt (by scalar_tac)
    rw [e0] at h0; rw [h0]; exact OwnMap.nof_zero
  -- the node, the caller's words
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.ndR layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hrg2 : Regs R (L.curW s2) := by rw [hct]; exact fun r hr => hR _ (P.regR hr).1
  have hbufR : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      R (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) := fun h0 i hi => hRu _ (hbufC h0 i hi)
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W x := by
    have n0 : IoRSR st K Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.ndR layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRSR st K Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.ndR layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact hR _ n0
    · rw [hn]; exact hR _ n1
    · rw [hn]; exact n1w
  have hnd2 : ∀ o, L.nodeAt s2 (L.cpu s2) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [I.cp, nodeAt_of_ksb I.k]
  have rst := P.stwR (Locks := Locks)
  have rsc : IoRSR st K Locks s (scA (L.curW s)) :=
    P.gateR (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField])
  have riq : IoRSR st K Locks s (inqA (L.curW s)) :=
    (P.homeR (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
  have hmxR : IoRSR st K Locks s (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact P.cscaccR.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩
  have hsc2 : L.mem s2 (scA (L.curW s)) = L.cscW s := by rw [← hct]; exact I.F.i
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
  have hmx2 : IoRSR st K Locks s
      (maxA (L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)))) := by
    have kw := (KeepA.refl ha2 hrun).wr hK (b := stA (L.curW s)) (v := sched.TS_RESTART) (Or.inr rfl)
      (fun _ => Or.inl rfl)
    have e : L.mem (L.wr s2 (stA (L.curW s)) sched.TS_RESTART) (scA (L.curW s)) = L.mem s2 (scA (L.curW s)) :=
      kw.mem (field_aligned P.tA (by simp) (by simp)) (iotw_field P.tA (by simp) (by simp))
    rw [e, hsc2]
    exact hmxR
  -- `set_thread_state RESTART` and the insertion
  have hset : sched.set_thread_state gS s2 (L.curW s2) sched.TS_RESTART =
      sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART := by
    rw [hct]
    exact sched.set_thread_state.guardV (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hst _ (Or.inl rfl)) (hR _ rst.1)
      (hR _ rsc) (hR _ hmx2) (hR _ riq)
  have hins : ∀ x3, sched.set_thread_state st s2 (L.curW s2) sched.TS_RESTART = ok x3 → ∀ nc : capability.Cap,
      (∀ w0 w1, capability.Cap.encode nc = ok (w0, w1) → NullOrFrame w0) →
      cdt.insert_with_cap gS x3 nc (.Frame fp sz rt d mp false asid va) src dest =
        cdt.insert_with_cap st x3 nc (.Frame fp sz rt d mp false asid va) src dest := by
    intro x3 hs3 nc hnc
    rw [hct] at hs3
    have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
    have ag3 : ∀ b, SlotW K b → Aligned b → L.mem x3 b = L.mem s b := fun b hs hb =>
      (K3.mem hb (O.notT hK hs)).trans (ag b hs hb)
    refine cdt.insert_with_cap.guardF8 (gS := gS) x3 nc src dest hnc
      (nR _ hsK hLs _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))
      (hwS src _ hsK hLs (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
        (Or.inl (by simp [layout.cte.NEXT])))
      (hw0 dest hd hLd hnT hnfd)
      (hwS dest 8#u64 hd hLd (by simp) (by simp) (by simp) (Or.inr ⟨hnT, hnfd⟩))
      (hwS dest _ hd hLd (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])
        (Or.inl (by simp [layout.cte.PREV])))
      (nR _ hd hLd _ (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))
      (hwS dest _ hd hLd (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])
        (Or.inl (by simp [layout.cte.NEXT])))
      (fun n e h0 => ?_)
    rw [next_agree hL hsK ag3] at e
    obtain ⟨hq, hl⟩ := hnx n e h0
    exact hwS n _ hq hl (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV]) (by simp [layout.cte.PREV])
      (Or.inl (by simp [layout.cte.PREV]))
  -- the decode
  rw [decode_cnode_eq ar] at hy
  have hdg : syscall.decode_invocation gS ar s2 a1 lbl length p.slot (.CNode cp cr cg cgb)
      true true true false buf p.extra = cnode.decode gS ar s2 a1 lbl length (.CNode cp cr cg cgb) buf p.extra := by
    unfold syscall.decode_invocation
    rw [sched.cur_thread.guard (gS := gS) s2 hctR, cur_thread_ok]
    simp only [bind_ok, Bool.false_eq_true, ↓reduceIte]
  have hcopy := cnode.decode_copy.guardCM8 (gS := gS) (lbl := lbl) (length := length) Cw hl hctR hrg2 hbufR he hs10
    hs1R hsc1' hdR hRc2 hcl2 hC' hsR hls2 hsrc2 hnR hset hins
  refine ⟨by rw [hdg, cnode.decode.guardCM8 (gS := gS) ar Cw hl hctR hrg2 hRc2 hcl2 hC hdR hlk2 hcopy]; exact hy, ?_⟩
  -- the reply
  intro z hz
  obtain ⟨-, hcase⟩ := cm_dec_st8 ar hl hlk2 he hs10 hsc1' hls2 hsrc2 hy
  obtain ⟨r, x, a2⟩ := y
  simp only at hcase hz ⊢
  cases r with
  | Ok u =>
    cases u
    have kx : KeepS st K s2 (L.curW s) x := by
      rcases hcase with hx | ⟨-, x3, nc, hs3, -, hins3⟩
      · rw [hx]; exact KeepS.of_keepA (KeepA.refl ha2 hrun)
      · rw [hct] at hs3
        have K3 : KeepA (L := L) s2 (L.curW s) x3 := (KeepA.refl ha2 hrun).sts hK (Or.inl rfl) hs3
        have ag3 : ∀ b, SlotW K b → Aligned b → L.mem x3 b = L.mem s b := fun b hs hb =>
          (K3.mem hb (O.notT hK hs)).trans (ag b hs hb)
        exact (KeepS.of_keepA K3).slots hK O (insert_frame_keep8 hL hd hsK
          (fun n e h0 => (hnx n (by rw [← next_agree hL hsK ag3]; exact e) h0).1) hins3)
    have Fx := kx.sched hK O
    refine invRep.guard_okS (gS := gS) (hR _ rst.1) (hst _ (Or.inr rfl)) (hR _ rsc) (hR _ riq)
      (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz
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
      k6.tcbF hK O (k := 3464#u64) (by simp) (by simp) (by simp)
    rw [e6, hsc2]; exact hR _ hmxR
  | Err e =>
    have hx : x = s2 := by
      rcases hcase with hx | ⟨h, -⟩
      · exact hx
      · cases h
    rw [hx] at hz ⊢
    obtain ⟨bsl, hbsl⟩ := buffer_slot_ok (L.curW s)
    obtain ⟨hb1, hb2⟩ := P.lay.tslot _ (P.hT _ P.cT) _ bsl hbsl (by simp [layout.tcb.SLOT_BUFFER])
    have hbs := P.slotR (Locks := Locks) hb1 (Or.inl hb2)
    have hI : R (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
      hR _ (P.gateR (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
      lookup_buf_keep P.tA true tk
    have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
      intro b eb
      rw [hlb] at eb
      exact ⟨fun h0 i hi => hWu _ (hbuf b eb h0 i (by omega)), fun h0 i hi => hRu _ (hbuf b eb h0 i (by omega))⟩
    rw [invRep.guard_err8 (gS := gS) e (fun e1 => syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1 hbsl hI
      (hR _ hbs.1) (hR _ hbs.2) (fun r hr => hW.reg r hr) hbw)]
    exact hz

end accZR

section finR
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 4000000 in
/-- (unify gen 2) **slhuf's `cmFin8` with `FinOK` over `IoRSR`** (scripted copy, `IoRS` → `IoRSR`,
`IoPre.ent` → `IoPre.entR`). -/
theorem cmFin8R {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSR st K Locks s)] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hsw : SWr gS st (L.curW s) sched.TS_RUNNING)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y)
    (hz : invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z) :
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRSR st K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨cp, cr, cg, cgb, dest, x1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, Cw, hcs, hex, -, hlk,
    hrc, hlss, hsc, -, -, hC, hCr, hcl, hWk, hs1K, -, hdK, -, -, hsK, -, -, hnx⟩ := E
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
  -- the registers `R10`, `R8`, `R9`, `R15`
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
  have r9 : L.mem s2 (regA (L.curW s) layout.reg.R9) = L.mem s (regA (L.curW s) layout.reg.R9) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R9) (by simp [layout.reg.R9])
      (by simp [layout.reg.R9]) tk
    rw [reg_ok, reg_ok] at e; exact ok_inj_ff e
  have r15 : L.mem s2 (regA (L.curW s) layout.reg.R15) = L.mem s (regA (L.curW s) layout.reg.R15) := by
    have e := reg_keepK (st := st) P.tA (r := layout.reg.R15) (by simp [layout.reg.R15])
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
    lookup_buf_keep P.tA true tk
  have hbuf2 : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64)) := fun b eb hne i hi =>
    hbuf b (by rw [← hlb]; exact eb) hne i hi
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
    rw [I.cp, nodeAt_of_ksb I.k]; exact not_usu8 (P.node_notUser ho) (P.node_notSlot ho)
  have hmx : ¬ UserW (KSU8 K) (maxA (L.mem s2 (scA (L.curW s)))) := by
    rw [← hct, I.F.i]
    exact not_usu8 (P.sc_notUser (P.hSc _ P.cscS) I.F.q.2.2.2.1) (P.sc_notSlot (P.hSc _ P.cscS) I.F.q.2.2.2.1)
  have htU : ∀ t, K.heap t = some .tcb → ∀ k : U64, 192 ≤ k.val → k.val < 4096 →
      ¬ UserW (KSU8 K) (core.num.U64.wrapping_add t k) := fun t ht k h1 h2 =>
    not_usu8 (P.tcb_notUser ht h1 h2) (P.tcb_notSlot ht h1 h2)
  have O : UsrOK (L := L) (KSU8 K) s2 (L.curW s) :=
    ⟨hn2, fun k h1 h2 => htU _ (P.hT _ P.cT) k h1 h2, hmx⟩
  -- the run
  have hex' : Aeneas.Std.Array.index_usize p.extra 0#usize = ok x1 := hex
  obtain ⟨hz2, kz⟩ := cmRun8 ar hK O ha2 hrun hL hl hlk2 hdK hex' hrc2 hlss2 hsc2 hsK hnx2 hbuf2 hy hz
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
  have ho' : ∀ b ∈ {b | b ∈ Ω ∧ ∃ c' ∈ K.heap.scs, InSC c' (K.heap.scBits c') b}, ¬ UserW (KSU8 K) b := by
    rintro b ⟨-, c', hc', hin⟩
    exact not_usu8 (P.sc_notUser (P.hSc _ hc') hin) (P.sc_notSlot (P.hSc _ hc') hin)
  have stm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSU8 K) (tdA (L.mem s2 (tmA (L := L) s2))) :=
    fun h0 => by
      unfold tdA
      exact htU _ (I.tm h0) _ (by simp) (by simp)
  have srh : L.mem s2 (rhA (L := L) s2) ≠ 0#u64 → ¬ UserW (KSU8 K) (scA (L.mem s2 (rhA (L := L) s2))) ∧
      ¬ UserW (KSU8 K) (headA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))) ∧
      ¬ UserW (KSU8 K) (rtA (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2))))
        (L.rhead s2 (L.mem s2 (scA (L.mem s2 (rhA (L := L) s2)))))) := fun h0 => by
    refine ⟨?_, ?_⟩
    · unfold scA; exact htU _ (F2'.rh h0).1 _ (by simp) (by simp)
    obtain ⟨zr, hW', hΩ⟩ := rh2' h0
    obtain ⟨h8, hmm, hfit⟩ := hW'.bounds
    obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW'.inside
    obtain ⟨e1, e2, e3⟩ := hrt _ hW'.head_lt
    exact ⟨ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩),
      ho' _ (hΩ _ (by unfold Aligned; omega) ⟨by omega, by omega⟩)⟩
  have FIN := kz.fin hK O Q0 Hf.nd I.F.td I.F.rs stm srh
  have hcur3 : L.curW z.1 = L.curW s := kz.cur hK O
  have w3 : WritesIn st s2 z.1 (fun b => IoPW st s2 b ∨ UserW (KSU8 K) b) :=
    kz.1.mono fun b hb => hb.imp_left fun h => Or.inr (by rw [hct]; exact h)
  have Fz := F2'.frameU w3 hn2 (fun t ht k h1 h2 => htU t (P.hT t ht) k (by omega) h2) ho'
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

/-- (unify gen 2) **slhuf's `inv_acc_gen3` on a store reading `IoRSR s`** (scripted copy, as invj's
`inv_acc_genR` of `inv_acc_gen2`). -/
theorem inv_acc_gen3R {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRSR st K Locks s)]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (hSeen : ∀ x, SeenW p x → IoRSR st K Locks s x)
    (hps : IoRSR st K Locks s p.slot ∧ IoRSR st K Locks s (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf →
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
  refine syscall.handle_invocation_local.guard_acc3 (gS := gS) ar (P.entR (Locks := Locks) hW).acc.nd
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
