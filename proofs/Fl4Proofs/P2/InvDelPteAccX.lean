/-
# P2 (line invj, generation 6): the PTE-arm Delete decode block on a read set without the unlocked leaves (`delAccX`)

gen 5's `delAccP` asks the guarded store to answer every `IoRS s` word, and `IoRS` holds every region-`.none` word,
the unlocked leaf page-table entries included, which under pte's rule 8 (`ownP`) are `lock b`'s: no local path may
read them. **`delAccX`** is `delAccP` (scripted copy) for any read set `R` that contains

* the `IoRS` words off a set `X` of `VsW` words (`hR`; for the ownP path `X = K.ptes`): every other read of the
  block is a slot / node / TCB / register / SC word, region `≠ .none`, so off `X` (`IoPre.vs_notSlot`,
  `IoPre.node/tcb/sc_notSlotX`);
* the locked leaves (`hRe`: the one `unmapLeaf` reads);

with the walk's read set `VsW ∧ ¬ X` (`hvs` with `VsRdG`, proved at every bundle state by `SlJAtZ.vsRdX`) and
`unmap_pteG`. So the block reads no leaf entry other than the locked `e`.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelPteG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section accX
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayout}

set_option maxHeartbeats 2000000 in
/-- (invj gen 6) **`delAccP` on a read set without the unlocked leaf entries**: the decode and the reply run as on
`st` on any store reading `R` — any set containing the `IoRS` words off `X` (`hR`) and the locked leaves (`hRe`),
`X` a set of `VsW` words (`hXv`; the leaf entries) — given that the walk reads only `VsW` words off `X` (`hvs`,
`SlJAtZ.vsRdX`). The write set need only contain the locked leaf `unmapLeaf` writes (`hWe`). -/
theorem delAccX {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {s : S} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A}
    {R W X : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (P : IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hW : IoWr st W K.heap.scBits s) (hWs : ∀ b, IoWS (st := st) K Locks s b → W b)
    (E : DelEntP st K Cs Locks p s) (hsl : p.slot ∈ K.slots) (hlen : ¬ length < 2#u64)
    (hvs : ∀ sl fp rt asid va, sl ∈ K.slots →
      obj.Slot.cap st sl s = ok (.Frame fp .Small rt false true false asid va) → asid ≠ 0#u64 →
      va ≤ fl4_abi.consts.USER_TOP ∧ localinv.small_page_entry st s asid va ≠ ok (some 0#u64) ∧
        VsRdG st (fun b => VsW K b ∧ ¬ X b) s asid va)
    (hXv : ∀ b, X b → VsW K b) (hR : ∀ b, IoRS (st := st) K Locks s b → ¬ X b → R b)
    (hRe : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → Locks s e → R e)
    (hlf : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → VsW K e)
    (hWe : ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → Locks s e → W e)
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
  have nXs : ∀ b, SlotW K b → ¬ X b := fun b hs hx => P.vs_notSlot (hXv _ hx) hs
  have nXn : ∀ o : U64, o.val < 4288 → ¬ X (L.nodeAt s (L.cpu s) o) := fun o ho hx =>
    P.node_notSlotX hXv ho (Or.inr hx)
  have nXt : ∀ k : U64, 192 ≤ k.val → k.val < 4096 → ¬ X (core.num.U64.wrapping_add (L.curW s) k) :=
    fun k h1 h2 hx => P.tcb_notSlotX hXv (P.hT _ P.cT) h1 h2 (Or.inr hx)
  have nXr : ∀ r : U64, r.val < 384 → ¬ X (regA (L.curW s) r) := fun r hr hx => by
    obtain ⟨k, hk, ek⟩ := regA_eq P.tA hr
    rw [ek] at hx
    exact nXt k (by omega) (by omega) hx
  have sW0 : ∀ q, q ∈ K.slots → SlotW K q := fun q hq => by
    have := slotW_of hL hq (o := 0#u64) (by simp); rwa [wadd_zero (hL q hq).2] at this
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
  have dR : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → R (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => hR _ (P.lockSlot hd hLd' ho h8).1 (nXs _ (slotW_of hL hd ho))
  have dW : ∀ o : U64, o.val < 32 → o.val % 8 = 0 → W (core.num.U64.wrapping_add dest o) :=
    fun o ho h8 => hWs _ ((P.lockSlot hd hLd' ho h8).2 (Or.inr ⟨hnT, hnf⟩))
  have r0 : R dest := by have := dR 0#u64 (by simp) (by simp); rwa [e0] at this
  have w0' : W dest := by have := dW 0#u64 (by simp) (by simp); rwa [e0] at this
  have nR : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 →
      R (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 =>
    hR _ (P.lockSlot hq hl ho h8).1 (nXs _ (slotW_of hL hq ho))
  have nW : ∀ q, q ∈ K.slots → Locks s q → ∀ o : U64, o.val < 32 → o.val % 8 = 0 → 16 ≤ o.val →
      W (core.num.U64.wrapping_add q o) := fun q hq hl o ho h8 h16 =>
    hWs _ ((P.lockSlot hq hl ho h8).2 (Or.inl h16))
  have nR0 : ∀ q, q ∈ K.slots → Locks s q → R q := fun q hq hl => by
    have := nR q hq hl 0#u64 (by simp) (by simp); rwa [wadd_zero (hL q hq).2] at this
  -- the node, the caller's words
  have hctR : R (L.nodeAt s2 (L.cpu s2) layout.node.CUR_THREAD) := by
    rw [I.cp, nodeAt_of_ksb I.k]
    exact hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
      (nXn _ (by simp [layout.node.CUR_THREAD]))
  have hN : ∀ x : S, (∀ o, L.nodeAt x (L.cpu x) o = L.nodeAt s (L.cpu s) o) →
      NodeSt (L := L) (R) W x := by
    have n0 : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) :=
      hR _ (P.nd layout.node.CUR_THREAD (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
        (nXn _ (by simp [layout.node.CUR_THREAD]))
    have n1 : R (L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION) :=
      hR _ (P.nd layout.node.SCHED_ACTION (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])).1
        (nXn _ (by simp [layout.node.SCHED_ACTION]))
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
  have rstR : R (stA (L.curW s)) :=
    hR _ rst.1 (nXt layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega))
  have rsc : R (scA (L.curW s)) :=
    hR _ (P.gate (off := 3464#u64) P.cT (by simp) (by simp) (by simp) (by simp [GateField]))
      (nXt 3464#u64 (by simp) (by simp))
  have riq : R (inqA (L.curW s)) :=
    hR _ (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
      (nXt 3592#u64 (by simp) (by simp))
  have hmxR : R (maxA (L.cscW s)) := by
    have hmx := maxA_facts P.bxi.2.2.1.1 P.cscS
    exact hR _ (P.cscacc.rd _ hmx.1 ⟨hmx.2.1, hmx.2.2⟩)
      (fun hx => P.sc_notSlotX hXv (P.hSc _ P.cscS) ⟨hmx.2.1, hmx.2.2⟩ (Or.inr hx))
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
      R (regA (L.curW s) r) := by
    intro i hi r hr
    unfold msg.msg_register at hr
    by_cases h0 : i = 0#u64
    · rw [if_pos h0] at hr; cases ok_inj_ff hr
      exact hR _ (P.reg (by simp [layout.reg.R10])).1 (nXr _ (by simp [layout.reg.R10]))
    · rw [if_neg h0] at hr
      have h1 : i = 1#u64 := by
        apply UScalar.eq_of_val_eq
        have : i.val ≠ 0 := fun e => h0 (UScalar.eq_of_val_eq (by simp [e]))
        simp; omega
      rw [if_pos h1] at hr; cases ok_inj_ff hr
      exact hR _ (P.reg (by simp [layout.reg.R8])).1 (nXr _ (by simp [layout.reg.R8]))
  have hRc2 : WalkRc (st := st) (R) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    have hq := (hWk p r m y hp hm).1
    have hs := P.slot (Locks := Locks) hq (Or.inr (cap_not_nof hc (Or.inl ⟨_, _, _, _, rfl⟩)))
    exact ⟨hR _ hs.1 (nXs _ (sW0 _ hq)), hR _ hs.2 (nXs _ (slotW_of hL hq (by simp)))⟩
  have hcl2 : WalkCl (st := st) s2 Cw := by
    intro p r m y p' r' gs' g' hp hm hc
    rw [cap_agree hL (hWk p r m y hp hm).1 ag] at hc
    exact hcl p r m y p' r' gs' g' hp hm hc
  have hRd : R dest ∧ R (core.num.U64.wrapping_add dest 8#u64) :=
    ⟨r0, dR 8#u64 (by simp) (by simp)⟩
  -- the frame finalisation: `unmap_page` is `unmapLeaf` at the plan's leaf on both stores
  have hr3 : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 →
      ∀ b, (fun b => VsW K b ∧ ¬ X b) b → st.read x3 b = st.read s b := fun x3 hs3 b hb0 => by
    have hb := hb0.1
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
    exact unmap_pteG ar (hr3 x3 hs3) (hk3 x3 hs3) hV hva he a'
  have hug : ∀ x3, sched.set_thread_state st s2 (L.curW s) sched.TS_RESTART = ok x3 → ∀ a' : A,
      vspace.unmap_page gS ar x3 a' .Small asid va fp = vspace.unmap_page st ar x3 a' .Small asid va fp := by
    intro x3 hs3 a'
    obtain ⟨hva, -, hV⟩ := hvs dest fp rt asid va hd hdc hA0
    rw [unmap_pteG ar (fun b hb => (gst_read (hR _ (VsW.ioRS (Locks := Locks) (s := s) hb.1) hb.2)).trans
        (hr3 x3 hs3 b hb))
      (by rw [show gS.ks_base = st.ks_base from gst_ks_base]; exact hk3 x3 hs3) hV hva he a',
      unmapLeaf.guard ar x3 a' asid va fp (hRe asid va e he hle) (hWe asid va e he hle), hu3S x3 hs3 a']
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
  have hmx2 : R
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
    rw [sched.set_thread_state.guard (gS := gS) s2 (L.curW s) _ (hN s2 hnd2) (hWs _ rst.2) rstR rsc hmx2 riq]
    refine tr_bind_same (fun s3 hs3 => ?_)
    exact hdel s3 hs3 y
  · intro z hz'
    obtain ⟨hy1, kx⟩ := cnDelP_keep ar hK O' ha2 hrun hL hlen hlk2 hd hdc2 hA0 hu3S rfl (P.vs_notSlot hVe) hVe.1
      hpv2 hnx2 hy
    obtain ⟨r, x, a2⟩ := y
    simp only at hy1 kx hz' ⊢
    subst hy1
    have Fx := kx.sched hK O'
    refine invRep.guard_ok (gS := gS) rstR (hWs _ rst.2) rsc riq (hW.reg _ rB384) (hW.reg _ rM384) ?_ hz'
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

end accX

end Fl4Proofs.P2.PathObl
