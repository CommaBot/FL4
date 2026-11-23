/-
P1: **writes of the debug lists keep the invariants** — a retype of TCBs
links the new TCBs into the debug lists, so retype's writes are cap-slot
words, untracked words and the debug-list words (`DbgW`: the TCBs' `dn`/`dp`
links and each core's `DEBUG_TCBS` head).  `BlkOK` reads the debug lists
only through `TimerOK`'s typing of them, so it survives any states agreeing
off those words with the debug links typed after (`blk_of_agreeD`), and the
writes give the agreement (`blk_of_writesD`).
-/
import Fl4Proofs.P1.QueueHeapAdd
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- The frames off the debug-list words: TCB fields from 192 but the debug
links, node words but the list head, frame words and endpoint words. -/
structure AgreeD (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg : Set U64)
    (s s' : S) : Prop where
  ksb : L.ksb s' = L.ksb s
  cpu : L.cpu s' = L.cpu s
  fld : ∀ y ∈ T, ∀ K : U64, 192 ≤ K.val → K.val < 4096 → K.val % 8 = 0 → K.val ≠ 3576 → K.val ≠ 3584 →
    L.mem s' (core.num.U64.wrapping_add y K) = L.mem s (core.num.U64.wrapping_add y K)
  nod : ∀ c ∈ Cs, ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 88 →
    L.mem s' (L.nodeAt s c o) = L.mem s (L.nodeAt s c o)
  sig : ∀ b ∈ Sg, L.mem s' b = L.mem s b
  epw : ∀ e, (H e = some .ep ∨ H e = some .ntfn) →
    L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e)

/- `DbgTz` (the debug lists typed) is in `QueueObjs`. -/

section
variable {s s' : S} (G : AgreeD st T Cs H Sg s s')
include G

theorem AgreeD.cur (hc : L.cpu s ∈ Cs) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h88 : o.val ≠ 88) :
    L.mem s' (L.nodeAt s' (L.cpu s') o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
  rw [G.cpu, nodeAt_of_ksb G.ksb]; exact G.nod _ hc o ho h8 h88

end

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **The scheduler queues over states agreeing off the debug lists.** -/
theorem SchedQueuesInv.agreeD {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (h : SchedQueuesInv st T Cs Ω H s Q R) (G : AgreeD st T Cs H Sg s s') : SchedQueuesInv st T Cs Ω H s' Q R := by
  have hT := h.tcbs
  have fld := G.fld
  have hsb : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) ∧ L.mem s' (blockA y) = L.mem s (blockA y) :=
    fun y hy => ⟨by rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp),
      by rw [blockA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)⟩
  have hact : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact G.cur h.cur (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  obtain ⟨E, EQ, w1, w2, w5, w3, w4, w6⟩ := h.eps
  have k3 := w6.2.2.1
  have hnb : ∀ c, L.nodeBase s' c = L.nodeBase s c := fun c => by simp [LawfulStore.nodeBase, G.ksb]
  have ew : ∀ e ∈ E, L.mem s' (epHeadA e) = L.mem s (epHeadA e) ∧ L.mem s' (epTSA e) = L.mem s (epTSA e) :=
    fun e he => G.epw e ((k3 e).1 he)
  refine inv_of_agree h G.ksb G.cpu (fun y hy => ⟨?_, ?_⟩)
    (fun c hc o h1 h2 h3 => G.nod c hc o h1 h2 (by omega))
    (fun y hy => by rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp))
    (fun y hy => by unfold affA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp))
    (fun y hy => Or.inl (by unfold prioA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)))
    (by rw [hact]; exact h.action) hsb
    (by rw [hact]; intro haT; rw [(hsb _ haT).1]; exact h.actOK haT) ?_
    (by rw [G.cur h.cur (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)]; exact h.curT)
    (by rw [G.cur h.cur (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)]; exact h.idleT)
  · rw [nextA_eq']
    exact fld y hy _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
  · rw [prevA_eq']
    exact fld y hy _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
  refine ⟨E, EQ, fun e he => ?_, w2, w5, fun e he y hy => ?_, fun y hy hyX hb => ?_,
    w6.agree (fun y hy => Or.inl hy) (fun y hy _ _ => hsb y hy) (fun _ _ _ hy => hy)
      (fun e he y hy => (hsb y ((w1 e he).2.2.mem y hy)).1)
      (fun e he _ => by simp only [LawfulStore.epState, (ew e he).2])
      (fun e he h0 => Or.inl ⟨h0, by simp only [LawfulStore.epState, (ew e he).2]⟩)⟩
  · obtain ⟨hE, hEN, hq⟩ := w1 e he
    have eq : L.epQ s' e = L.epQ s e := by
      simp only [LawfulStore.epQ, (ew e he).1, (ew e he).2]
    refine ⟨hE, ⟨fun c hc => by rw [hnb]; exact hEN.1 c hc, by rw [G.ksb]; exact hEN.2⟩, ?_⟩
    rw [eq]
    have hp : ∀ y ∈ EQ e, L.mem s' (prevA .Ep y) = L.mem s (prevA .Ep y) := fun y hy => by
      rw [prevA_eq']
      exact fld y (hq.mem y hy) _ (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff]) (by simp [prevOff])
        (by simp [prevOff])
    have hn : ∀ y ∈ EQ e, L.mem s' (nextA .Ep y) = L.mem s (nextA .Ep y) := fun y hy => by
      rw [nextA_eq']
      exact fld y (hq.mem y hy) _ (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff]) (by simp [nextOff])
        (by simp [nextOff])
    exact ⟨hq.nodup, hq.mem, hq.head, hq.last, hq.seg.congr fun y hy => ⟨hp y hy, hn y hy⟩⟩
  · have hyT := (w1 e he).2.2.mem y hy
    rw [(hsb y hyT).1, (hsb y hyT).2]; exact w3 e he y hy
  · rw [(hsb y hy).1] at hb
    rw [(hsb y hy).2]; exact w4 y hy hyX hb

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **`BlkOK` over states agreeing off the debug lists, the debug links typed after.** -/
theorem BlkOK.agreeD {s s' : S} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (G : AgreeD st T Cs H Sg s s')
    (D : DbgTz st T Cs s') : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, hSg⟩ := h
  have hT := h0.tcbs
  have fld := G.fld
  have sig := G.sig
  have hsc : ∀ y ∈ T, L.mem s' (scA y) = L.mem s (scA y) := fun y hy => by
    rw [scA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hst : ∀ y ∈ T, L.mem s' (stA y) = L.mem s (stA y) := fun y hy => by
    rw [stA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have hinq : ∀ y ∈ T, L.mem s' (inqA y) = L.mem s (inqA y) := fun y hy => by
    rw [inqA_eq]; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)
  have ea : L.actionW s' = L.actionW s := by
    unfold LawfulStore.actionW; exact G.cur h0.cur (by rw [act_val]; omega) (by rw [act_val]) (by rw [act_val]; omega)
  have ec : L.curW s' = L.curW s := by
    unfold LawfulStore.curW; exact G.cur h0.cur (by rw [curth0]; omega) (by rw [curth0]) (by rw [curth0]; omega)
  have ei : L.idleW s' = L.idleW s := by
    unfold LawfulStore.idleW; exact G.cur h0.cur (by rw [idle8]; omega) (by rw [idle8]) (by rw [idle8]; omega)
  have ecs : L.cscW s' = L.cscW s := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    exact G.cur h0.cur (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have hB' : BoundInv st T Ac s' :=
    hB.mk' hsc (fun y hy hf => Or.inl (by rw [← hinq y hy]; exact hf))
      (fun y hy hf => Or.inr (Or.inl (by rw [← hinq y hy]; exact hf)))
      (fun haT => by rw [ea] at haT ⊢; exact ⟨haT, hB.act haT⟩) (by rw [ei]; exact ⟨h0.idleT, hB.idle⟩)
      (fun h0' => by rw [ea] at h0'; rw [ec]; exact ⟨h0.curT, hB.resume h0'⟩)
      (hB.nb ei (hst _ h0.idleT))
      (fun y hy hS _ => Or.inl (Sch.of_eq (fun hf => by rwa [hinq y hy] at hf) (fun hf => by rwa [hinq y hy] at hf)
        ea ei ec (hst y hy) hS))
  have tm := hX.2.2.tm
  have tmo : TimerOK st T Cs s' := by
    refine ⟨fun c hc => (tm.npl c hc).ksb G.ksb, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun c hc => ?_,
      fun c hc => ?_, fun y hy hd c hcv => ?_, D.dn, D.dp, D.dh⟩
    · rw [show tlA y = core.num.U64.wrapping_add y 3544#u64 from rfl,
        fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact tm.lt y hy
    · rw [show trA y = core.num.U64.wrapping_add y 3552#u64 from rfl,
        fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact tm.rt y hy
    · rw [show tpA y = core.num.U64.wrapping_add y 3560#u64 from rfl,
        fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact tm.pt y hy
    · rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])
        (by rw [timer_root_val]; omega)]; exact tm.root c hc
    · rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])
        (by rw [timer_min_val]; omega)]; exact tm.min c hc
    · rw [show tdA y = core.num.U64.wrapping_add y 3528#u64 from rfl,
        fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)] at hd
      rw [show thA y = core.num.U64.wrapping_add y 3568#u64 from rfl,
        fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)] at hcv
      exact tm.core y hy hd c hcv
  have ntb : NtbOK st T Nt s' := fun n hn => by rw [sig _ (hX.1.ntB n hn).2]; exact hX.2.2.ntb n hn
  have rb : TimerRB st T Cs s' := hX.2.2.rb.congr
    ⟨fun y hy => fld y hy 3528#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
      fun y hy => fld y hy 3544#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
      fun y hy => fld y hy 3552#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
      fun y hy => fld y hy 3560#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
      fun y hy => fld y hy 3568#u64 (by simp) (by simp) (by simp) (by simp) (by simp),
      fun c hc => by
        rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_root_val]; omega) (by rw [timer_root_val])
          (by rw [timer_root_val]; omega)],
      fun c hc => by
        rw [nodeAt_of_ksb G.ksb, G.nod c hc _ (by rw [timer_min_val]; omega) (by rw [timer_min_val])
          (by rw [timer_min_val]; omega)]⟩
  have hX' : XInv st T Cs Ω Sg Rp Scs Nt Z s' :=
    hX.keep (fun r hr => ⟨sig _ (hX.1.tcbW hr), sig _ (hX.1.prevW hr), sig _ (hX.1.nextW hr)⟩)
      (fun c hc => ⟨sig _ (hX.1.fixW c hc).1, sig _ (hX.1.fixW c hc).2⟩) hsc
      (fun y hy => by unfold replyA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp)) hst
      (by rw [ecs]; exact hX.2.2.cur) (fun c hc => sig _ (hX.1.repW c hc))
      (fun y hy => by unfold boundA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp))
      (fun n hn => sig _ (hX.1.ntW n hn)) ⟨tmo, ntb, rb, fun n hn => sig _ (hX.1.ntB n hn).2⟩
      (fun c hc => sig _ (hX.1.snW c hc))
      (fun y hy => by unfold yieldA; exact fld y hy _ (by simp) (by simp) (by simp) (by simp) (by simp))
      (fun c hc => sig _ (hX.1.syW c hc))
      (fun c hc => sig _ (hX.1.mxW c hc)) ei
  have hS' : SCsOK st T Ω Sg Scs Z Ac s' := by
    refine ⟨hS.sub, fun b hb => by rw [G.ksb]; exact hS.ks b hb, fun o h1 h2 => by rw [G.ksb]; exact hS.ksΩ o h1 h2,
      fun t ht hb hne => ?_, fun c hc => (hS.all c hc).agree sig,
      fun c hc => by rw [show L.rmax s' c = L.rmax s c from sig _ (hS.all c hc).2.1]; exact hS.act c hc,
      fun c hc h1 => hS.spor c hc (by rw [← sig _ (hS.spSg c hc)]; exact h1), hS.spSg,
      fun c hc h1 => hS.rep c hc (by rw [← sig _ (hS.repSg c hc)]; exact h1), hS.repSg⟩
    rw [hsc t ht] at hb hne ⊢; rw [ecs] at hne ⊢; exact hS.disj t ht hb hne
  exact ⟨⟨Q, R, h0.agreeD G⟩, hB', hX', hS',
    ⟨hSg.sub, fun b hb => by rw [G.ksb]; exact hSg.ks b hb, fun o h1 h2 => by rw [G.ksb]; exact hSg.ksΩ o h1 h2⟩⟩

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

/-- **Writes of cap-slot, untracked and debug-list words agree off the debug lists.** -/
theorem agreeD_of_writes {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B)
    (hB : ∀ b, B b → CapW T Ω Sg b ∨ Untracked st T Cs H Sg s b ∨ DbgW st T Cs s b) :
    AgreeD st T Cs H Sg s s' := by
  obtain ⟨⟨Q, R, h0⟩, -, hX, -, hSg⟩ := h
  have hT := h0.tcbs
  obtain ⟨E, EQ, w1, -, w3, -, -, -, -, k3, -⟩ := h0.eps
  refine ⟨hw.1, hw.2.1, fun y hy K hK0 hK hK8 h1 h2 => ?_, fun c hc o ho h8 h88 => ?_, fun b hb => ?_,
    fun e he => ?_⟩
  · refine hw.mem_eq (field_aligned (hT y hy) hK hK8) fun hb => ?_
    rcases hB _ hb with (hl | ⟨hm, -⟩) | hu | (⟨y', hy', e | e⟩ | ⟨c, hc, e⟩)
    · exact tlow_ne_field hT hy hK0 hK hl rfl
    · exact out_ne_field (h0.omega _ hm) hy (hT y hy) hK rfl
    · exact out_ne_field hu.out hy (hT y hy) hK rfl
    · exact field_ne (hT y' hy') (hT y hy) (K1 := 3576#u64) (by simp) hK (fun _ => by simp; omega) e.symm
    · exact field_ne (hT y' hy') (hT y hy) (K1 := 3584#u64) (by simp) hK (fun _ => by simp; omega) e.symm
    · exact node_ne_field (h0.nodes c hc) (by rw [debug_val]; omega) hy (hT y hy) hK e.symm
  · have hN := h0.nodes c hc
    refine hw.mem_eq (nodeAt_aligned hN ho h8) fun hb => ?_
    rcases hB _ hb with (hl | ⟨hm, -⟩) | hu | (⟨y', hy', e | e⟩ | ⟨c', hc', e⟩)
    · exact tlow_ne_node hT hN ho hl rfl
    · exact out_ne_node (h0.omega _ hm) hc hN ho rfl
    · exact out_ne_node hu.out hc hN ho rfl
    · exact node_ne_field hN ho hy' (hT y' hy') (by simp) e
    · exact node_ne_field hN ho hy' (hT y' hy') (by simp) e
    · exact node_ne_node hN (h0.nodes c' hc') ho (by rw [debug_val]; omega)
        (fun _ => by rw [debug_val]; exact h88) (congrArg UScalar.val e)
  · have ho := h0.omega _ (hSg.sub b hb)
    refine hw.mem_eq ho.1 fun hb' => ?_
    rcases hB _ hb' with (hl | ⟨-, hn⟩) | hu | (⟨y', hy', e | e⟩ | ⟨c, hc, e⟩)
    · exact tlow_ne_out hT ho hl
    · exact hn hb
    · exact hu.sg hb
    · exact out_ne_field (K := 3576#u64) ho hy' (hT y' hy') (by simp) (by rw [e]; rfl)
    · exact out_ne_field (K := 3584#u64) ho hy' (hT y' hy') (by simp) (by rw [e]; rfl)
    · exact out_ne_node ho hc (h0.nodes c hc) (by rw [debug_val]; omega) (by rw [e])
  · have heE : e ∈ E := (k3 e).2 he
    obtain ⟨hP, hON, -⟩ := w1 e heE
    obtain ⟨a1, a2⟩ := ep_aligned hP
    have hv1 := (epHeadA_val : (epHeadA e).val = e.val)
    have hv2 := epTSA_val hP
    have notB : ∀ a : U64, (a.val = e.val ∨ a.val = e.val + 8) → ¬ B a := fun a ha hb => by
      rcases hB _ hb with (⟨t, ht, K, hK, rfl⟩ | ⟨hm, -⟩) | hu | (⟨y', hy', e' | e'⟩ | ⟨c, hc, e'⟩)
      · have := field_val (hT t ht) (by omega : K.val < 4096); have := hP.disj t ht; omega
      · have := w3 e heE a hm; omega
      · have := hu.eps e he; omega
      · have hv : a.val = y'.val + 3576 := by
          rw [e', show dnA y' = core.num.U64.wrapping_add y' 3576#u64 from rfl, field_val (hT y' hy') (by simp)]; simp
        have := hP.disj y' hy'; omega
      · have hv : a.val = y'.val + 3584 := by
          rw [e', show dpA y' = core.num.U64.wrapping_add y' 3584#u64 from rfl, field_val (hT y' hy') (by simp)]; simp
        have := hP.disj y' hy'; omega
      · have hv : a.val = L.nodeBase s c + 88 := by
          rw [e', nodeAt_val (h0.nodes c hc) (by rw [debug_val]; omega), debug_val]
        have := hON.1 c hc; omega
    exact ⟨hw.mem_eq a1 (notB _ (Or.inl hv1)), hw.mem_eq a2 (notB _ (Or.inr hv2))⟩

/-- **Writes of cap-slot, untracked and debug-list words keep `BlkOK`**, the
debug links typed after. -/
theorem blk_of_writesD {s s' : S} {B : U64 → Prop} (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hw : WritesIn st s s' B)
    (hB : ∀ b, B b → CapW T Ω Sg b ∨ Untracked st T Cs H Sg s b ∨ DbgW st T Cs s b) (D : DbgTz st T Cs s') :
    BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s' :=
  h.agreeD (agreeD_of_writes h hw hB) D

end

end Fl4Proofs.P1
