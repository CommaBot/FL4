/-
# P2 (line invj, generation 5): `FinOK` after the CNodeDelete **PTE-arm** decode block (`delFinP`)

stpost's `delFin` (P2/InvBlkFin.lean) for a mapped small RAM frame cap with a non-zero ASID whose leaf the plan
locked (`del_coreP`): the decode block writes the caller's `IoTW` words, capability-slot words and the leaf `e`
(`decDelP_keep`). `e` is a `VsW` word (region `.none`), so it misses the node, the TCB fields and the SC words, and
every fact `finish` needs survives it.

* `SwOK.nodeEX` / `tcbEX` / `omEX` / **`frameEX`**: InvBlkFin's `frame` section copied verbatim by a script with
  `SlotW K` replaced by `SlotWX K X`;
* `IoPre.node_notSlotX` / `tcb_notSlotX` / `sc_notSlotX` (for `X ⊆ VsW K`), `IoPre.vs_notSlot`;
* `SlJAtZ.leafVsW` / **`invLeafJ_of`**: a found small-page entry is a `VsW` word at every `SlJAt` state (an entry of
  an `L1` table, `lookup_pt_slot_rel`, then gen 1's `SlJAtZ.tabVsW`);
* `DelEntP` (stpost's `DelEnt` for the PTE arm), **`delEntP_of`** (from `InvQFP`, `InvCdtJ`, `0 ∉ K.slots`);
* **`delFinP`**: `FinOK` after the decode block at an accepted run's post-prefix state.

No named premise (`delFinP`'s `hvs` / `hlf` are the facts `invVsJ_of` / `invLeafJ_of` give at `SlJAt`). No existing
statement changes.
-/
import Fl4Proofs.P2.InvDelPteDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  slotOwner)

/-! ## `SwOK` across slot writes and `X` writes (scripted copy of InvBlkFin's `frame` section) -/

section frameX
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {K : KLayout} {X : U64 → Prop} {T Cs Ω : Set U64} {x y : S} {c : U64} {zc : Nat}

section
variable (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (fun b => IoPW st x b ∨ SlotWX K X b))
  (hn : ∀ o : U64, o.val < 4288 → ¬ SlotWX K X (L.nodeAt x (L.cpu x) o))
  (ht : ∀ t ∈ T, ∀ k : U64, 3328 < k.val → k.val < 4096 → ¬ SlotWX K X (core.num.U64.wrapping_add t k))
  (ho : ∀ b ∈ Ω, ¬ SlotWX K X b)
include F w hn

theorem SwOK.nodeEX (o : U64) (ho' : o.val < 4288) (h8 : o.val % 8 = 0)
    (hno : ¬ (o.val = 16 ∨ o.val = 40 ∨ o.val = 48)) :
    L.mem y (L.nodeAt y (L.cpu y) o) = L.mem x (L.nodeAt x (L.cpu x) o) := by
  rw [wi_node w]
  refine w.2.2 _ (nodeAt_aligned F.np ho' h8) ?_
  rintro ((⟨o', ho'', e⟩ | ⟨r, hr, e⟩ | e) | hs)
  · by_cases hv : o.val = o'.val
    · omega
    · exact nodeAt_ne F.np ho' (by omega) hv e
  · have hv := congrArg UScalar.val e
    rw [regA_val (F.tp _ F.cT) hr, nodeAt_val F.np ho'] at hv
    have := F.np.disj _ F.cT; omega
  · exact node_ne_field F.np ho' F.cT (F.tp _ F.cT) (by rw [st_val]; omega) e
  · exact hn o ho' hs

omit hn in
include ht in
theorem SwOK.tcbEX {t k : U64} (htT : t ∈ T) (hk : k.val < 4096) (h8 : k.val % 8 = 0) (hge : 3328 < k.val) :
    L.mem y (core.num.U64.wrapping_add t k) = L.mem x (core.num.U64.wrapping_add t k) := by
  refine w.2.2 _ (field_aligned (F.tp t htT) hk h8) ?_
  rintro ((⟨o, ho', e⟩ | hi) | hs)
  · exact node_ne_field F.np (by omega) htT (F.tp t htT) hk e.symm
  · exact iotw_tcb (F.tp _ F.cT) (F.tp t htT) hk hge hi
  · exact ht t htT k hge hk hs

omit hn in
include ho in
theorem SwOK.omEX {b : U64} (hb : b ∈ Ω) : L.mem y b = L.mem x b := by
  refine w.2.2 _ (F.om b hb).1 ?_
  have htt := F.tp _ F.cT
  have h1 := (F.om b hb).2.1 _ F.cT
  rintro ((⟨o, ho', e⟩ | ⟨r, hr, e⟩ | e) | hs)
  · exact out_ne_node (F.om b hb) F.cpu F.np (by omega) (congrArg UScalar.val e).symm
  · have hv := congrArg UScalar.val e
    rw [regA_val htt hr] at hv; omega
  · have hv := congrArg UScalar.val e
    unfold stA at hv
    rw [tcb_wadd_val htt (by rw [st_val]; omega), st_val] at hv; omega
  · exact ho b hb hs

include ht ho in
/-- **`SwOK` survives the prefix writes and slot writes** missing the node, the TCB fields and `Ω`. -/
theorem SwOK.frameEX : SwOK st T Cs Ω R W y c zc := by
  have hcur : L.curW y = L.curW x := F.nodeEX w hn _ (by simp [layout.node.CUR_THREAD])
    (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hcsc : L.mem y (L.nodeA y layout.node.CUR_SC) = L.mem x (L.nodeA x layout.node.CUR_SC) :=
    F.nodeEX w hn _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have htm : L.mem y (tmA (L := L) y) = L.mem x (tmA (L := L) x) :=
    F.nodeEX w hn _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have hrh : L.mem y (rhA (L := L) y) = L.mem x (rhA (L := L) x) :=
    F.nodeEX w hn _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  have hcs : ∀ t ∈ T, L.mem y (scA t) = L.mem x (scA t) := fun t htT =>
    F.tcbEX w ht htT (k := 3464#u64) (by simp) (by simp) (by simp)
  have hmx : L.rmax y c = L.rmax x c := F.omEX w ho (F.q.2.1 _ F.q.2.2.2.2 F.q.2.2.2.1)
  have wfE : RefillsWF st x c zc → RefillsWF st y c zc := fun h =>
    h.agree fun b hb hin => F.omEX w ho (F.q.2.1 b hb hin)
  refine ⟨F.tp, ?_, ?_, ?_, ?_, hcsc.trans F.csc, ?_, ⟨?_, F.q.2⟩, ?_, F.acc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w.2.1]; exact F.cpu
  · rw [w.2.1]; exact F.np.ksb w.1
  · exact fun a ha => (F.om a ha).ksb w.1
  · rw [hcur]; exact F.cT
  · rw [hcur, hcs _ F.cT]; exact F.i
  · rw [hmx]; exact fun h => wfE (F.q.1 h)
  · rw [hmx]; exact F.act
  · intro o ho' h8; rw [wi_node w]; exact F.nd o ho' h8
  · rw [hcur]; exact F.sc
  · rw [w.1]; exact F.dt
  · rw [htm]; exact F.td
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]
    refine ⟨(F.rs h0).1, ?_⟩
    rcases (F.rh h0).2 with e | ⟨ho', ho''⟩
    · rw [e]; exact F.acc.head (wfE (F.q.1 F.act))
    · have hb : L.rhead y (L.mem x (scA (L.mem x (rhA (L := L) x)))) =
          L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))) := F.omEX w ho ho'
      have := (F.rs h0).2
      unfold RdHead at this ⊢
      rw [hb]; exact this
  · rw [hrh]
    intro h0
    rw [hcs _ (F.rh h0).1]; exact F.rh h0

end
end frameX

/-! ## The leaf is a `VsW` word -/

section leaf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {X : U64 → Prop}

theorem IoPre.vs_notSlot (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {b : U64} (hv : VsW K b) : ¬ SlotW K b :=
  fun hs => by
    obtain ⟨q, hq⟩ := P.slotW_region hs
    rw [hv.2.1] at hq; cases hq

theorem IoPre.node_notSlotX (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hX : ∀ b, X b → VsW K b) {o : U64}
    (ho : o.val < 4288) : ¬ SlotWX K X (L.nodeAt s (L.cpu s) o) := by
  rintro (hs | hx)
  · exact P.node_notSlot ho hs
  · have hn := P.lay.node _ _ (P.inNode o ho)
    rw [(hX _ hx).2.1] at hn; cases hn

theorem IoPre.tcb_notSlotX (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hX : ∀ b, X b → VsW K b) {t k : U64}
    (ht : K.heap t = some .tcb) (h1 : 192 ≤ k.val) (h2 : k.val < 4096) :
    ¬ SlotWX K X (core.num.U64.wrapping_add t k) := by
  rintro (hs | hx)
  · exact P.tcb_notSlot ht h1 h2 hs
  · have := P.lay.tcbw t ht k h1 h2
    unfold fld at this
    rw [(hX _ hx).2.1] at this; cases this

theorem IoPre.sc_notSlotX (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hX : ∀ b, X b → VsW K b) {c : U64}
    {zb : Nat} (hc : K.heap c = some (.sc zb)) {b : U64} (hin : InSC c zb b) : ¬ SlotWX K X b := by
  rintro (hs | hx)
  · exact P.sc_notSlot hc hin hs
  · have := P.lay.scw c zb hc b ⟨hin.1, hin.2⟩
    rw [(hX _ hx).2.1] at this; cases this

end leaf

section words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
  {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
  {σ : Fl4Spec.State Unit}

/-- **A found small-page entry is a `VsW` word** at a bundle state. -/
theorem SlJAtZ.leafVsW (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K s a' σ) {asid va e : U64}
    (hc : localinv.small_page_entry st s asid va = ok (some e)) : VsW K e := by
  obtain ⟨hSR, hVs, hPt, hPI, -⟩ := B.j.xtop.fin
  have hTP := hSR.2
  unfold localinv.small_page_entry at hc
  obtain ⟨r, hr, hL4⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.find_vspace_for_asid_L4 (st := st) s σ hVs hPI asid)
  rw [hr] at hc
  cases r with
  | Err e =>
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at hc
    exact absurd (ok_inj_ff hc) (by simp)
  | Ok root =>
    have hroot := hL4 root rfl
    simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok] at hc
    unfold localinv.page_entry at hc
    by_cases hu : va > fl4_abi.consts.USER_TOP
    · rw [if_pos hu] at hc
      exact absurd (ok_inj_ff hc) (by simp)
    · rw [if_neg hu] at hc
      have hv : Fl4Proofs.P3.Vs.UserV va := by
        unfold Fl4Proofs.P3.Vs.UserV
        have hU : fl4_abi.consts.USER_TOP.val = 140737488355327 := by unfold fl4_abi.consts.USER_TOP; rfl
        have : ¬ fl4_abi.consts.USER_TOP.val < va.val := hu
        omega
      unfold vspace.small_page_entry at hc
      obtain ⟨r2, hr2, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pt_slot_rel s σ hPt hTP.pt hroot va hv)
      rw [hr2] at hc
      simp only [bind_ok] at hc
      cases r2 with
      | Err e =>
        simp only [core.result.Result.ok] at hc
        exact absurd (ok_inj_ff hc) (by simp)
      | Ok x =>
        simp only [core.result.Result.ok] at hc
        have ex : x = e := Option.some.inj (ok_inj_ff hc)
        subst ex
        obtain ⟨q, hq, e⟩ := hsl x rfl
        rw [e]
        exact B.tabVsW (Or.inr (Or.inr (Or.inr hq))) (Fl4Proofs.P3.Vs.vIdx_lt _ _)

/-- (invj gen 5) **A found small-page entry is a `VsW` word at every state of `P`**, for `P` implying `SlJAt K`.
No premise. -/
theorem invLeafJ_of {P : S → Prop} (hP : ∀ s, P s → SlJAt (L := L) K s) :
    ∀ s, P s → ∀ asid va e, localinv.small_page_entry st s asid va = ok (some e) → VsW K e := by
  intro s hs asid va e he
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hP s hs
  exact B.leafVsW he

end words

/-! ## The entry facts -/

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64} {s : S}

variable (st) in
/-- (invj gen 5) **The PTE arm's entry facts** (stpost's `DelEnt` with a mapped frame cap, a non-zero ASID and the
plan's locked leaf `e`). -/
def DelEntP (K : KLayout) (Cs : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (s : S) : Prop :=
  ∃ (cp cr cg cgb dest fp rt asid va e : U64) (C : U64 → U64 → Prop),
    obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧
    cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
      (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
    obj.Slot.cap st dest s = ok (.Frame fp .Small rt false true false asid va) ∧
    (asid ≠ 0#u64 ∧ localinv.small_page_entry st s asid va = ok (some e) ∧ e ≠ 0#u64 ∧ Locks s e) ∧
    C cp cr ∧ WalkCl (st := st) s C ∧
    (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
      OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
    dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧ Locks s dest ∧
    (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV) ∈ K.slots ∧
      Locks s (L.mem s (core.num.U64.wrapping_add dest layout.cte.PREV))) ∧
    (∀ nx, obj.Slot.next st dest s = ok nx → nx ≠ 0#u64 → nx ∈ K.slots ∧ Locks s nx)

/-- (invj gen 5) **`DelEntP` at the entry** from `InvQFP`, `InvCdtJ` at `s` and `0 ∉ K.slots`. -/
theorem delEntP_of {P : S → Prop} (hPs : P s) (hq : InvQFP st Cs Ω Sg Ac Locks p K μ s)
    (hcdt : InvCdtJ st K P) (hz : (0#u64) ∉ K.slots) : DelEntP st K Cs Locks p s := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, C, hcap, -, htg, hdc, hCc, hcl, hC, hdK, hdO, hLd, hLp,
    hLn, -, hA, he, he0, hle⟩ := del_coreP hq
  have hd0 : dest ≠ 0#u64 := fun e => hz (e ▸ hdK)
  obtain ⟨hcP, hcN⟩ := hcdt s dest hPs hdK
  exact ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, C, hcap, htg, hdc, ⟨hA, he, he0, hle⟩, hCc, hcl, hC, hdK,
    hdO, hLd hd0, fun hp => ⟨hcP hp, hLp hp⟩, fun nx e hne => ⟨hcN nx e hne, hLn nx e hne⟩⟩

end ent

section finP
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S}

set_option maxHeartbeats 4000000 in
/-- (invj gen 5) **`FinOK` after the CNodeDelete PTE-arm decode block** (stpost's `delFin`) (the I/O port's `io_hfin` route with the
Delete arm's slot writes): at an accepted run's post-prefix state `s2` (`InvChk`), a decode of the CNode cap at the
plan's slot at `CNodeDelete` with `length ≥ 2`, then `invRep`, reply `Ok ()` and leave `FinOK`. Inputs: `IoPre` and
`DelEnt` at the entry, the plan's slot a capability slot, the write set `W` covering the prefix words (`IoWr`) and
the caller's `STATE`. -/
theorem delFinP {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {a : A}
    {nx : U64} {s1 s2 : S} {a1 : A} {length buf : U64} {cap : capability.Cap}
    {y : (core.result.Result Unit error.Exc) × S × A} {z : S × A × core.result.Result Unit error.Exc}
    {W : U64 → Prop} {gS : machine.Store S} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
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
    z.2.2 = .Ok () ∧ FinOK (L := L) gS (IoRS (st := st) K Locks s) W ar s z.1 z.2.1 := by
  obtain ⟨cp, cr, cg, cgb, dest, fp, rt, asid, va, e, Cw, hcs, hlk, hdc, ⟨hA0, he, -, -⟩, hC, hcl, hWk, hd, -, -, hpv,
    hnx⟩ := E
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

end finP

end Fl4Proofs.P2.PathObl
