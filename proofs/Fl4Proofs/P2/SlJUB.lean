/-
# P2 (line slhuf, gen 4): user-blind entry facts

`sl_pathsKC` (P2/SlJQ.lean) left two frame premises: `hPBw` [J] (`SlPreB` survives a write
of a user word) and `hArw` [P] (`SlAccR` does). Both quantify over the `LocalPre`
successors `X` of the entry state. This module gives the generic machinery to carry such facts
across a user-word write, and discharges `hArw`.

## Machinery
* `NU K`: the aligned words that are not user words of the layout. `nu_of_region`: every
  aligned word of a layout region (node, slot, TCB, notification, endpoint / reply, SC) is
  `NU` (`RegionOKX.kern`). `SlJAt.userKs`: no user word lies in the kernel-state block (P3's
  `BufPlaced.far`), so the kernel globals are `NU` too (`SlJAt.nuKs`).
* **The commuting lemma** `SlJAt.lp_wr`: a prefix run (`LocalPre`: the `FAULT_IP` write and
  `update_timestamp`) from `L.wr s b v` (`b` a user word) has a prefix run from `s` with the
  same Arch state whose end state agrees with it on every `NU` word, kernel base and core
  (`Ag st (NU K) X X'`). This is P2's `lp_alt` at `Q := NU K`. Stated word by word only:
  `LawfulStore` has no extensionality.
* `slCom_nu`, `fltDec_nu`: the words the trap arm's checks read at a prefix state are `NU`
  (`FltDec (NU K)`), from the bundle and `SlPreB` (its `BXI` at the prefix state names the
  endpoint head and the release head as TCBs, `tm_of` / `rh_of` the timer-min thread).
* `flt_chk_back`: checks passing at a state agreeing on `R` with `X` pass at `X`, given
  `FltDec R X t` (P2's `vm_chk_back` for any read set).

## Discharged
* **`SlJAt.accR_wr`**: `SlAccR` survives a user-word write at a bundle state, given `SlPreB`
  there and the locks (`hlk` [P]). No other premise.
* `slQ_wrU`, **`sl_pathsKC2`**, `sl_pathsKC2_startAt`: `sl_pathsKC` without `hArw`.
  Remaining premises: `hPBw` [J], `hlk` [P], `hpz`, and `hSt`, `hA`, `hm`, `a0`.
-/
import Fl4Proofs.P2.SlJVm
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- The aligned words that are not user words of the layout `K`. -/
def NU (K : KLayout) (x : U64) : Prop := Aligned x ∧ x ∉ K.user

theorem nu_al {K : KLayout} : ∀ b, NU K b → Aligned b := fun _ h => h.1

/-- An aligned word of a layout region is `NU`. -/
theorem nu_of_region {K : KLayout} (hX : RegionOKX K) {b : U64} (ha : Aligned b)
    (hr : region K b ≠ .none) : NU K b := ⟨ha, hX.kern b hr⟩

/-- An aligned TCB word from offset 192 is `NU`. -/
theorem nu_tcb {K : KLayout} (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {o : U64}
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) :
    NU K (core.num.U64.wrapping_add t o) := by
  obtain ⟨r, -, a⟩ := hX.tcbW t ht o h1 h2 h3
  exact nu_of_region hX a (by rw [r]; intro h; cases h)

/-- An aligned word of a heap SC is `NU`. -/
theorem nu_sc {K : KLayout} (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z))
    {b : U64} (ha : Aligned b) (hb : InSC sc z b) : NU K b :=
  nu_of_region hX ha (by rw [hX.scW sc z hz b hb]; intro h; cases h)

/-- An endpoint's two words are `NU`. -/
theorem nu_ep {K : KLayout} (hX : RegionOKX K) {p : U64} (hp : K.heap p = some .ep) {o : U64}
    (h1 : o.val < 16) (h2 : o.val % 8 = 0) : NU K (core.num.U64.wrapping_add p o) := by
  obtain ⟨r, a⟩ := hX.epW p hp o h1 h2
  exact nu_of_region hX a (by rw [r]; intro h; cases h)

/-- A TCB's cap slot's two words are `NU`. -/
theorem nu_tslot {K : KLayout} (hK : RegionOK K) (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb)
    {i : U64} (hi : i.val < 6) :
    NU K (slotIdx t i) ∧ NU K (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨hs, -, r8, -, a0, a8⟩ := hX.tslot t ht i hi
  exact ⟨nu_of_region hX a0 (by rw [hK.slot _ hs]; intro h; cases h),
    nu_of_region hX a8 (by rw [r8]; intro h; cases h)⟩

theorem SlJAt.kc {K : KLayout} {s : S} (B : SlJAt (L := L) K s) :
    L.ksb s = K.ksb ∧ (L.cpu s).val < K.ncores := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := B
  exact ⟨B.ksb, B.cpu⟩

/-- **No user word lies in the kernel-state block** (P3's `BufPlaced.far`: user words lie below
the block or beyond the last node). -/
theorem SlJAt.userKs {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {x : U64} (hx : x ∈ K.user)
    {o : U64} (ho : o.val < 13568) : x ≠ core.num.U64.wrapping_add K.ksb o := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := B
  rw [B.user] at hx
  obtain ⟨wp, hw, rfl⟩ := hx
  have hf := B.j.bufPlacedJ.far wp hw
  have kf := B.j.kern.ksbFit
  have hk := B.ksb
  simp only [LawfulStore.nodeBase] at hf
  rw [hk] at hf kf
  intro e
  have hv := congrArg UScalar.val e
  have e2 : (core.num.U64.wrapping_add K.ksb o).val = K.ksb.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  rw [e2] at hv
  omega

/-- A node word of this core is `NU` at a bundle state. -/
theorem SlJAt.nuNode {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    NU K (L.nodeAt s (L.cpu s) o) := by
  obtain ⟨hk, hc⟩ := B.kc
  have v := nodeAt_val hN ho
  have hr : region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    B.regionOKX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact nu_of_region B.regionOKX (nodeAt_aligned hN ho h8) (by rw [hr]; intro h; cases h)

/-- A kernel global (the first 256 bytes of the block) is `NU` at a bundle state. -/
theorem SlJAt.nuKs {K : KLayout} {s : S} (B : SlJAt (L := L) K s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 256) (h8 : o.val % 8 = 0) :
    NU K (core.num.U64.wrapping_add (L.ksb s) o) := by
  obtain ⟨hk, -⟩ := B.kc
  refine ⟨(rs_ks (Locks := fun _ _ => True) B.regionOKX hN hk ho h8).1, fun hx => ?_⟩
  rw [hk] at hx
  exact B.userKs hx (o := o) (by omega) rfl

/-! ## The commuting lemma -/

variable {A : Type} (ar : machine.Arch A)

/-- **A prefix run from `L.wr s b v` (`b` a user word) is a prefix run from `s`, up to the `NU`
words** (P2's `lp_alt` at `Q := NU K`): same Arch state, end states agreeing on `NU K`, kernel
base and core. -/
theorem SlJAt.lp_wr (hA : P0.ArchTotal ar) {K : KLayout} {s : S} (B : SlJAt (L := L) K s)
    {T : Set U64} (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T)
    (hcH : K.heap (L.curW s) = some .tcb)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) {a a1 : A} {X' : S}
    (LP' : LocalPre (st := st) ar (L.wr s b v) a (X', a1)) :
    ∃ X, LocalPre (st := st) ar s a (X, a1) ∧ Ag st (NU K) X X' := by
  have ecur := B.curW_wr hb hba v
  have hX := B.regionOKX
  obtain ⟨KN, hKN, eKN⟩ := regA_eq (hT _ hcT) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 256 + 8 * layout.reg.NEXT_IP.val := hKN
  have nNx : NU K (regA (L.curW s) layout.reg.NEXT_IP) := by
    rw [eKN]
    exact nu_tcb hX hcH (by rw [hKN']; simp [layout.reg.NEXT_IP])
      (by rw [hKN']; simp [layout.reg.NEXT_IP]) (by rw [hKN']; simp [layout.reg.NEXT_IP])
  obtain ⟨X, LP, hag⟩ := lp_alt ar hA (Q := NU K) nu_al hT hN hcT (L.ksb_wr _ _ _) (L.cpu_wr _ _ _) ecur
    (fun x hx => mem_wr_ne' hba hx.1 (fun e => hx.2 (e ▸ hb))) nNx
    (B.nuNode hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    (B.nuNode hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) LP'
  have hN' : NodePlaced st T (L.wr s b v) (L.cpu (L.wr s b v)) := by
    rw [L.cpu_wr]; exact NodePlaced.of_ksb (L.ksb_wr _ _ _) hN
  obtain ⟨kX, cX, -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN hcT LP
  obtain ⟨kX', cX', -⟩ := sl_pre_agree (Cs := ∅) ar hA hT hN' (by rw [ecur]; exact hcT) LP'
  refine ⟨X, LP, ⟨?_, ?_, hag⟩⟩
  · rw [kX', kX, L.ksb_wr]
  · rw [cX', cX, L.cpu_wr]

end

/-! ## Checks back along an agreeing state -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **Fault checks passing at a state agreeing with `X` on `R` pass at `X`**, given that `R`
holds the words the trap arm reads at `X` (`FltDec`; P2's `vm_chk_back` for any read set). -/
theorem flt_chk_back {R : U64 → Prop} {X y : S} {t ptr badge dest r : U64}
    (D : FltDec (L := L) R X t) (G : Ag st R X y)
    (C : FaultChecks st y t ptr badge dest r) : FaultChecks st X t ptr badge dest r := by
  obtain ⟨hA, ⟨sl, x, yy, g, gr, hS, hcap, hg⟩, hep, hh, hrep, hr0, hhe, ⟨d, p, hd, hp, hhi⟩⟩ := C
  have esl : sl = slotIdx t layout.tcb.SLOT_FAULT_HANDLER := by
    rw [tcb_slot_val] at hS; exact (ok_inj_ff hS).symm
  subst esl
  rw [cap_congr_ag G D.fh.1 D.fh.2] at hcap
  obtain ⟨rts, rhd, hdd⟩ := D.ep ptr badge x yy g gr hcap
  have eep : obj.Ep.state st ptr y = obj.Ep.state st ptr X := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) y ptr), eq_of_spec_fd (obj.Ep.state.spec (L := L) X ptr)]
    unfold LawfulStore.epState
    rw [G.m (epTSA ptr) rts]
  rw [eep] at hep
  have ehd : obj.Ep.head st ptr y = obj.Ep.head st ptr X := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) y ptr), eq_of_spec_fd (obj.Ep.head.spec' (L := L) X ptr)]
    exact congrArg ok (G.m (epHeadA ptr) rhd)
  rw [ehd] at hh
  have DD := hdd hep dest hh
  have HF := here_facts (L := L) hhe
  have haf : L.mem X (affA dest) = L.cpu X := by rw [← G.m _ DD.af, ← G.c]; exact HF.aff
  obtain ⟨rD, rS, rQ, rP⟩ := DD.rest haf
  have erp : obj.Tcb.reply_obj st dest y = obj.Tcb.reply_obj st dest X := by
    rw [eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) y dest),
      eq_of_spec_fd (obj.Tcb.reply_obj.spec (L := L) X dest)]
    exact congrArg ok (G.m _ DD.rp)
  rw [erp] at hrep
  have ehere : fastpath.schedulable_here st y dest = fastpath.schedulable_here st X dest :=
    here_congr G (D.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
      (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
      (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])) D.tm D.rh D.dt D.cd
      DD.af rD rS rQ
  rw [ehere] at hhe
  have ecd : sched.cur_domain st y = sched.cur_domain st X := by
    rw [cur_domain_ok, cur_domain_ok, G.k]
    exact congrArg ok (G.m _ D.cd)
  rw [ecd] at hd
  have epr : obj.Tcb.prio st dest y = obj.Tcb.prio st dest X := by
    rw [eq_of_spec_fd (obj.Tcb.prio.spec (L := L) y dest), eq_of_spec_fd (obj.Tcb.prio.spec (L := L) X dest)]
    exact congrArg ok (G.m _ rP)
  rw [epr] at hp
  have bm' : RdBitmap (L := L) R y := RdBitmap.congr G.k G.c D.bm
  have h1 : sched.is_highest_prio (PathObl.guard st R (fun _ => True)) X d p =
      sched.is_highest_prio st X d p :=
    sched.is_highest_prio.guard (gS := PathObl.guard st R (fun _ => True)) X d p D.bm
  have h2 : sched.is_highest_prio (PathObl.guard st R (fun _ => True)) y d p =
      sched.is_highest_prio st y d p :=
    sched.is_highest_prio.guard (gS := PathObl.guard st R (fun _ => True)) y d p bm'
  have ehi : sched.is_highest_prio st y d p = sched.is_highest_prio st X d p :=
    ro_congr G (fun m z => sched.is_highest_prio m z d p) (fun _ => rfl) h1 h2
  rw [ehi] at hhi
  have hact : sched.action st X = ok sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) _)] at hA ⊢
    rw [← ok_inj_ff hA]
    unfold LawfulStore.actionW
    rw [G.node, G.m _ (D.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))]
  exact ⟨hact, ⟨_, x, yy, g, gr, tcb_slot_val _ _, hcap, hg⟩, hep, hh, hrep, hr0, hhe, ⟨d, p, hd, hp, hhi⟩⟩

end

/-! ## The trap arm's read words are `NU` at a prefix state -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **The common words at a prefix state are `NU`** (`slCom_of` for `NU K`). -/
theorem slCom_nu (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : SlCom (L := L) (NU K) X := by
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU K (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 => by rw [nX]; exact B.nuNode E.hN h1 h2
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → o.val ≠ 48 → o.val ≠ 40 →
      L.mem X (L.nodeAt X (L.cpu X) o) = L.mem s (L.nodeAt s (L.cpu s) o) := fun o h1 h2 h3 h4 => by
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN h1 h2) (not_slDS_node E.hN E.hT E.hcT h1 h3 h4)
  have eTm : L.mem X (tmA (L := L) X) = L.mem s (tmA (L := L) s) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN])
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) :=
    eN _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
  refine ⟨nd, ?_, ?_, ⟨nd _ (by simp [l1Off]) (by simp [l1Off]), fun inv hinv => nd _ (by simp; omega)
    (by simp <;> omega)⟩, fun h => ?_, fun h => ?_⟩
  · rw [kX]; exact B.nuKs E.hN (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact B.nuKs E.hN (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, -, -⟩ := tm_of ar hA hX (slSets_conv K) E hk hcp LP h
    exact nu_tcb hX ht (o := 3528#u64) (by simp) (by simp) (by simp)
  · rw [eRh] at h ⊢
    obtain ⟨ht, hz, hin, hmx, -⟩ := rh_of ar hA hX (slSets_conv K) E hk hcp LP h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    refine ⟨nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp), ?_⟩
    generalize L.mem s (scA (L.mem s (rhA (L := L) s))) = sc at hz hin hmx
    obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
    have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
      lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 hk hcp
        (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
    have hW : RefillsWF st X sc (K.heap.scBits sc) :=
      ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
    exact ScAcc.head (R := NU K) (W := fun _ => True)
      ⟨fun b ha hb => nu_sc hX hz ha hb, fun _ _ _ => trivial, trivial⟩ hW

/-- **The trap arm's read words at a prefix state are `NU`** (`FltDec (NU K)`). -/
theorem fltDec_nu (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : FltDec (L := L) (NU K) X (L.curW s) := by
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_nu ar hA B E LP
  have hcH := E.hSt.1
  have fs := nu_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  obtain ⟨hs, -, r8, -, a0, a8⟩ := hX.tslot _ hcH layout.tcb.SLOT_FAULT_HANDLER
    (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have nd0 : ¬ SlDS (L := L) s (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [hK.slot _ hs]; intro c h; cases h)
      (by rw [hK.slot _ hs]; intro h; cases h)
  have nd8 : ¬ SlDS (L := L) s (core.num.U64.wrapping_add (slotIdx (L.curW s) layout.tcb.SLOT_FAULT_HANDLER) 8#u64) :=
    not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp (by rw [r8]; intro c h; cases h) (by rw [r8]; intro h; cases h)
  refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, fs, fun ptr bb x y g gr hcap => ?_⟩
  have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP a0 nd0) (lp_mem ar hA E.hT E.hN E.hcT LP a8 nd8)
  have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr bb x y g gr) := by
    rw [← ecap]; exact hcap
  have hpH : K.heap ptr = some .ep := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B'⟩ := B
    have h := B'.hep ⟨ptr, bb, x, y, g, gr, hcap'⟩
    rwa [resPtr_ok hcap'] at h
  refine ⟨nu_ep hX hpH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE]), nu_ep hX hpH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD])
    (by simp [layout.ep.HEAD]), fun hst d hd => ?_⟩
  have hst' : L.epState X ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) X ptr)] at hst; exact ok_inj_ff hst
  have hdd : d = L.mem X (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) X ptr)] at hd; exact (ok_inj_ff hd).symm
  have hdT : K.heap d = some .tcb := by
    rw [hdd]; exact vm_headT (E.hI a X a1 LP) hpH hst'
  exact ⟨nu_tcb hX hdT (o := 3360#u64) (by simp) (by simp) (by simp),
    nu_tcb hX hdT (o := 3520#u64) (by simp) (by simp) (by simp),
    fun _ => ⟨nu_tcb hX hdT (o := 3432#u64) (by simp) (by simp) (by simp),
      nu_tcb hX hdT (o := 3464#u64) (by simp) (by simp) (by simp),
      nu_tcb hX hdT (o := 3592#u64) (by simp) (by simp) (by simp),
      nu_tcb hX hdT (o := 3448#u64) (by simp) (by simp) (by simp)⟩⟩

/-- **`SlAccR` survives a user-word write** at a bundle state, given `SlPreB` there and the
locks (`hlk` [P]). -/
theorem SlJAt.accR_wr (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) (R : SlAccR (st := st) ar K Locks found s) :
    SlAccR (st := st) ar K Locks found (L.wr s b v) := by
  refine ⟨fun hS' a X' a1 LP' ptr badge dest r C => ?_⟩
  have hS := (B.trap_wr hb hba v).1 hS'
  rw [B.curW_wr hb hba v] at C
  rw [hl]
  obtain ⟨X, LP, G⟩ := B.lp_wr ar hA E.hT E.hN E.hcT E.hSt.1 hb hba v LP'
  exact R.frl hS a X a1 LP (flt_chk_back (fltDec_nu ar hA B E LP) G C)

end

/-! ## The syscall local path without `hArw` -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Locks : S → U64 → Prop}
variable {A : Type}
variable {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`hQ` for `SlQ` with `SlAccR`'s frame proved** (`SlJAt.accR_wr`): premises `hPBw` [J]
and the locks (`hlk` [P]). -/
theorem slQ_wrU (ar : machine.Arch A) (hA : P0.ArchTotal ar)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → SlQ st ar Locks n found Cs Ω Sg Ac K m s → b ∈ K.user →
      Aligned b → SlQ st ar Locks n found Cs Ω Sg Ac K m (L.wr s b v) :=
  fun K m s b v hJ q hb hba =>
    ⟨hPBw K m s b v hJ q.1 hb hba, hJ.entL_wr hb hba v (hlk K s b v hJ hb hba) q.2.1,
      hJ.syncC_wr hb hba v q.2.2.1, hJ.accR_wr ar hA q.1 hb hba v (hlk K s b v hJ hb hba) q.2.2.2⟩

/-- **The syscall local path with the canonical `Q`, `SlAccR`'s frame proved** (`sl_pathsKC`
without `hArw`). Premises: `hPBw` [J], `hlk` [P], `hpz`, and `hSt`, `hA`, `hm`, `a0`. -/
noncomputable def sl_pathsKC2 (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks)) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKF (Locks := Locks) ar hSt hA hm a0 (SlQ st ar Locks n found Cs Ω Sg Ac)
    (fun _ _ _ _ q => q.1) (fun _ _ _ _ q => q.2.1) (fun _ _ _ _ q => q.2.2.1) (fun _ _ _ _ q => q.2.2.2)
    (slQ_wrU ar hA hPBw hlk) hlk hpz

/-- **`StartAt` for `sl_pathsKC2`**. -/
theorem sl_pathsKC2_startAt (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hPBw : ∀ K m s b v, SlJAt (L := L) K s →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s → b ∈ K.user → Aligned b →
      SlPreB (st := st) ar K Locks m n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
        K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hpz : ∀ K m, ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m) (· ∈ K.user)
        (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
        (SlRS (st := st) K Locks))
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC2 (Locks := Locks) ar hSt hA hm a0 hPBw hlk hpz () K m hK hU) c hs μ
      ((sl_pathsKC2 (Locks := Locks) ar hSt hA hm a0 hPBw hlk hpz () K m hK hU).body σ a) :=
  sl_pathsKF_startAt ar hSt hA hm a0 _ _ _ _ _ (slQ_wrU ar hA hPBw hlk) hlk hpz K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl
