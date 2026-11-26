/-
# P2 (line slhuf, gen 14): the Copy / Mint decode block with the plan's raw-zero target (no `hnul`)

fl4-core's `plan_with` now admits a Copy / Mint only when the target's first cap word is `0` (commit "fl4-core: localinv
Copy/Mint requires raw-zero dest"), not merely when it decodes to Null. So the target's word is a Null / Frame
encoding by the plan itself, and gen 13's [J] `hnul` (`InvNulJ`: canonical slot words) is not needed:
* `CMDestZ st p s`: the target the arm looks up (from the invoked CNode cap, R10 / R8) has first word 0;
* `cmAccZ`, `cmAccGZ`, `cmAccGdZ`: `cmAcc8` / `cmAccG8` / `cmAccGd8` (P2/InvCMAcc8.lean) with `hnul` replaced by
  `hz0 : CMDestZ st p s` (verbatim otherwise; the helpers are InvCMAcc8's).
-/
import Fl4Proofs.P2.InvCMAcc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)

section dz
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- (slhuf gen 14) **The Copy / Mint target's first word is 0** (what `plan_with` now checks): for the invoked slot's
CNode cap and the target lookup from `R10` / `R8`, the target's `CAP0` word is `0`. -/
def CMDestZ (p : localinv.Plan) (s : S) : Prop :=
  ∀ cp cr cg cgb dest, obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) →
    cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
      (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) →
    L.mem s (core.num.U64.wrapping_add dest layout.cte.CAP0) = 0#u64

end dz

section accZ
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 4000000 in
/-- (slhuf gen 12; gen 14 `hz0`) **The Copy / Mint decode block on any store answering as `st`** (run-relative): reads of
`IoRS s` and of aligned user words, writes of `IoTW`-side words (`hW`), of aligned user words (the error reply's
buffer words), of locked capability-slot words (`hwS`, per word; `hw0`, a locked non-TCB Null / Frame slot's
`CAP0` written with a Null / Frame word) and the caller's `STATE` (`hst`, per value). At an entry with `IoPre`
and `CMEnt`, after the prefix and checks (`InvChk`), for any message length: `cnode.decode`'s Copy / Mint arm
(truncated, `DeleteFirst`, lookup, `copied_cap` errors and the successful `insert_with_cap`) and `invRep`
(`reply_error` on an error, `reply_success_empty` / `set_thread_state RUNNING` on `Ok`).
Hypotheses beyond `CMEnt`: `hz0 : CMDestZ` (the target's first word is `0`, as the plan checks; gen 14, in place
of gen 12's `hnul`), `hbufC` (the decode's
buffer words, when the buffer is set, are aligned user words) and [J] `hbuf : InvBufJ8` (the error reply's
buffer). -/
theorem cmAccZ {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hR : ∀ b, IoRS (st := st) K Locks s b → R b) (hRu : ∀ b, UserW K b → R b)
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
  have Ent := P.ent (Locks := Locks) (P.ioWr (Locks := Locks))
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
    have h := P.slot (Locks := Locks) (hWk p r m y hp hm).1 (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    exact ⟨hR _ h.1, hR _ h.2⟩
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  -- the slot words
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      R (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 => hR _ (P.lockSlot hq hl ho h8).1
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
    have h := P.slot (Locks := Locks) hs1K (Or.inr (cap_not_nof hsc1 (Or.inl ⟨_, _, _, _, rfl⟩)))
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
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
  have hrg2 : Regs R (L.curW s2) := by rw [hct]; exact fun r hr => hR _ (P.reg hr).1
  have hbufR : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      R (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) := fun h0 i hi => hRu _ (hbufC h0 i hi)
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) → NodeSt (L := L) R W x := by
    have n0 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    have n1 : IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
    have n1w : W (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hW.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])
    intro x hn
    refine ⟨?_, ?_, ?_⟩
    · rw [hn]; exact hR _ n0
    · rw [hn]; exact hR _ n1
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
  have hmx2 : IoRS (st := st) K Locks s
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
    have hbs := P.slot (Locks := Locks) hb1 (Or.inl hb2)
    have hI : R (core.num.U64.wrapping_add (L.curW s) 3512#u64) :=
      hR _ (P.gate (off := 3512#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
    have hlb : msg.lookup_ipc_buffer st s2 true (L.curW s) = msg.lookup_ipc_buffer st s true (L.curW s) :=
      lookup_buf_keep P.tA true tk
    have hbw : ∀ b, msg.lookup_ipc_buffer st s2 true (L.curW s) = ok b → BufW W b ∧ BufW R b := by
      intro b eb
      rw [hlb] at eb
      exact ⟨fun h0 i hi => hWu _ (hbuf b eb h0 i (by omega)), fun h0 i hi => hRu _ (hbuf b eb h0 i (by omega))⟩
    rw [invRep.guard_err8 (gS := gS) e (fun e1 => syscall.reply_error.guard (gS := gS) s2 (L.curW s) e1 hbsl hI
      (hR _ hbs.1) (hR _ hbs.2) (fun r hr => hW.reg r hr) hbw)]
    exact hz

/-- (slhuf gen 12) **`cmAccZ` on the store guarded to the user-word sets** `guard st (InvCMRS s) (InvCMWS s)` (the
`InvBlkUW2` store): the slot, `CAP0` and `STATE` writes are `IoWS` words (`IoPre.lockSlot`, `IoPre.stw`). -/
theorem cmAccGZ {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots)
    (hz0 : CMDestZ st p s)
    (hbufC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) ar s2 a1
        lbl length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) (L.curW s) y.2.1 y.2.2 y.1
        = ok z :=
  cmAccZ (gS := guard st (InvCMRS (st := st) K Locks s) (InvCMWS (st := st) K Locks s)) hA P
    (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) (P.ioWr.mono (fun _ h => ioWS_cm h))
    (fun _ h => ⟨h.1, Or.inl h.2⟩)
    (fun q o hq hlk ho h8 _ hw => ioWS_cm ((P.lockSlot hq hlk ho h8).2 hw))
    (fun q hq hlk hT hn x v _ => by
      have h := (P.lockSlot hq hlk (o := 0#u64) (by simp) (by simp)).2 (Or.inr ⟨hT, hn⟩)
      rw [wadd_zero (P.lay.slot8 q hq).2] at h
      exact gst_write (ioWS_cm h))
    (fun _ _ => SWr.of_W (ioWS_cm P.stw.2)) E hsl hz0 hbufC hbuf hl C hcap hy

/-- (slhuf gen 12) **`cmAccZ` on p2sl's checked store with slot `CAP0` writes, reading the user-word set**
`gd st (InvCMRS s) (PWs …)` (the `InvBlkGdUW2` store): the destination's `CAP0` write (Null → the derived
Frame cap's word) is a `PWs` slot write, the other slot words and user words are non-deciding aligned words
(`PW`), `STATE` as stpost's `gds_write_state`. [J] `hK` (`RegionOK`), `hU` (`UserOK`), `hLA` (`IoLayA`). -/
theorem cmAccGdZ {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {lbl length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    (E : CMEnt st K Cs Locks p s) (hsl : p.slot ∈ K.slots)
    (hz0 : CMDestZ st p s)
    (hbufC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
      UserW K (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)))
    (hbuf : InvBufJ8 st K s)
    (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (C : InvChk st ar s a (L.curW s) p nx s1 s2 a1)
    (hcap : obj.Slot.cap st p.slot s2 = ok cap)
    (hy : syscall.decode_invocation st ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y) :
    syscall.decode_invocation (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
        ar s2 a1 lbl length p.slot cap true true true false buf p.extra = ok y ∧
    ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
      invRep (gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)))
        (L.curW s) y.2.1 y.2.2 y.1 = ok z := by
  have hS0 : OwnMap.Safe0 (L.cpu s) (Locks s) (L.mem s) (L.curW s) := by
    refine ⟨?_, fun hq => absurd hq ?_⟩
    · rw [← OwnMap.affA_fld]; exact P.curAff
    · rw [← OwnMap.stA_fld]; exact nq_run P.run
  have hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K q ∧ NullOrFrame (L.mem s q))) →
      WAll (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s)) (core.num.U64.wrapping_add q o) := by
    intro q o hq _ ho h8 h8' _
    obtain ⟨q8, qf⟩ := P.lay.slot8 q hq
    have hv := slot_word_val qf ho
    have hr := P.lay.slotw q hq _ (slot_inW qf ho)
    have hne : core.num.U64.wrapping_add q o ≠ q := fun e => by
      have := congrArg UScalar.val e; rw [hv] at this; omega
    have ha : Aligned (core.num.U64.wrapping_add q o) := by unfold Aligned; rw [hv]; omega
    exact fun _ _ => Or.inl (Or.inl ⟨ha, OwnMap.nondec_slotw hK hr hne⟩)
  exact cmAccZ (gS := gd st (InvCMRS (st := st) K Locks s) (OwnMap.PWs (L := L) K (L.cpu s) (Locks s) (L.mem s))) hA P
    (fun _ h => ioRS_cm h) (fun _ h => ⟨h.1, Or.inl h.2⟩) (mvWrS P hK hLA)
    (fun b hb _ _ => Or.inl (Or.inl ⟨hb.1, fun hd => (OwnMap.decW_ok hU hd).2 hb.2⟩))
    hwS (fun q hq hlk hT hn x v hv => OwnMap.gds_write_cap0 hq hT hlk hn hv)
    (fun v hv X => OwnMap.gds_write_state (P.hT _ P.cT) hS0 (fun hq => absurd hq (nq_run hv)))
    E hsl hz0 hbufC hbuf hl C hcap hy

end accZ

end Fl4Proofs.P2.PathObl
