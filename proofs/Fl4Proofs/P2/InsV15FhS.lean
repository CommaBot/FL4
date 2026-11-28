/-
# P2 (line p3mc, gen 49): `InsV15V` at every sl start — the foreign branch by the foreign-handler pattern

Gen 48 closed the sl starts whose decided thread is homed (`SlHPm`). The other sl starts (`¬ SlHome`: the decided
thread live and homed off the core in `ρ`) have the `VSafe9` certificate `sl_fh_safe` (P2/SlFhCert), whose run from
one store state is split out in place this generation (`slfh_run`, statement of `sl_fh_safe` unchanged); the pattern
of P2/InsV15Fh (`insA_narrow_tr_gd`) gives its `InsA` twin.

## The read set off the paging words
The run reads `Rd` (`SlFhR`: the prefix words, the current SC's head refill, and the declining arms' words at every
dispatch state of the entry) and the decided thread's `SlFhW` words. `RTK K b` (region-tagged or kernel-static;
`RTW K = RTK K.toKLayout`): every word `SlFhR` names is one (`rtk_*` helpers; **`slCom_rt`**, **`fltDecT_rt`**,
**`rrDecT_rt`**, **`rdHead_hereRT`**: the region facts of `slCom_nu` / `fltDec_nu` / `rrDec_nu` / `rdHead_hereN`,
which state them only as `NU`), so `Rd ∧ RTK` (with `SR`'s "no PTE word") avoids `PWE K E'` (`rt_notPWE'`).

* **`PathObl.sl_fh_insA`**: the `InsA` twin of `sl_fh_safe` (guard read set `Rd ∪ SlFhW d`, write set `SlDS σ`, all
  off `G`).
* **`sl_fh_insA_annV`**: the `InsA` counterpart of `sl_fh_annV` (P2/SlFhView), read set `((SlRS ∧ NU) ∧ SR) ∧ RTW`.
* **`sl_k0_insAF`** (as `sl_k0_fhB`, P2/E2EPU16), **`sl_insA_annV_all`** (every sl start without a VCPU;
  `sl_insA_annV_h` of gen 48 where `SlHome`), `SlPm`, **`insAP_sl_view`**.

No named premise. Existing file touched: P2/SlFhCert (`slfh_run` split out of `sl_fh_safe`); every existing
statement byte-identical.
-/
import Fl4Proofs.P2.InsV15FhR
import Fl4Proofs.P2.SlFhView
import Fl4Proofs.P2.E2EPU16
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own region GateField TimerField GField RegionOK)
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsA narrowSP)

noncomputable section
open Classical

/-- A region-tagged or kernel-static word of a layout (module docstring). -/
def RTK (K : KLayout) (b : U64) : Prop :=
  region K b ≠ .none ∨ ∃ o : U64, o.val < 13568 ∧ b = core.num.U64.wrapping_add K.ksb o

section rt
variable {K : KLayout}

theorem rtk_of {b : U64} {r : OwnMap.Region} (h : region K b = r) (hr : r ≠ .none) : RTK K b :=
  Or.inl (by rw [h]; exact hr)

theorem rtk_tcb (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {o : U64}
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) : RTK K (core.num.U64.wrapping_add t o) := by
  obtain ⟨r, -, -⟩ := hX.tcbW t ht o h1 h2 h3
  exact rtk_of r (by simp)

theorem rtk_sc (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) {b : U64}
    (hb : InSC sc z b) : RTK K b :=
  rtk_of (hX.scW sc z hz b hb) (by simp)

theorem rtk_scw (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) {o : U64}
    (ho : o.val < 128) (h8 : o.val % 8 = 0) : RTK K (core.num.U64.wrapping_add sc o) := by
  obtain ⟨-, -, -, rm⟩ := sc_off hX hz ho h8
  exact rtk_of rm (by simp)

theorem rtk_ep (hX : RegionOKX K) {p : U64} (hp : K.heap p = some .ep) {o : U64}
    (h1 : o.val < 16) (h2 : o.val % 8 = 0) : RTK K (core.num.U64.wrapping_add p o) := by
  obtain ⟨r, -⟩ := hX.epW p hp o h1 h2
  exact rtk_of r (by simp)

theorem rtk_rp (hX : RegionOKX K) {p : U64} (hp : K.heap p = some .reply) {o : U64}
    (h1 : o.val < 32) (h2 : o.val % 8 = 0) : RTK K (core.num.U64.wrapping_add p o) := by
  obtain ⟨r, -⟩ := hX.rpW p hp o h1 h2
  exact rtk_of r (by simp)

theorem rtk_reg (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {r : U64} (hr : r.val < 384) :
    RTK K (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact rtk_tcb hX ht (by omega) (by omega) (by omega)

theorem rtk_tslot (hK : RegionOK K) (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {i : U64}
    (hi : i.val < 6) :
    RTK K (slotIdx t i) ∧ RTK K (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨hs, -, r8, -, -, -⟩ := hX.tslot t ht i hi
  exact ⟨rtk_of (hK.slot _ hs) (by simp), rtk_of r8 (by simp)⟩

theorem scAccRT (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) :
    ScAcc (RTK K) (fun _ => True) sc z :=
  ⟨fun b _ hb => rtk_sc hX hz hb, fun _ _ _ => trivial, trivial⟩

variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- A node word of this core at a bundle state is region-tagged. -/
theorem SlJAt.rtNode {s : S} (B : SlJAt (L := L) K s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) {o : U64} (ho : o.val < 4288) : RTK K (L.nodeAt s (L.cpu s) o) := by
  obtain ⟨hk, hc⟩ := B.kc
  have v := nodeAt_val hN ho
  have hr : region K (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    B.regionOKX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact rtk_of hr (by simp)

/-- A kernel global at a bundle state is kernel-static. -/
theorem SlJAt.rtKs {s : S} (B : SlJAt (L := L) K s) {o : U64} (ho : o.val < 256) :
    RTK K (core.num.U64.wrapping_add (L.ksb s) o) := by
  obtain ⟨hk, -⟩ := B.kc
  exact Or.inr ⟨o, by omega, by rw [hk]⟩

end rt

section sl
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **The common words at a prefix state are region-tagged or kernel-static** (the region facts of `slCom_nu`). -/
theorem slCom_rt (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : SlCom (L := L) (RTK K) X := by
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → RTK K (L.nodeAt X (L.cpu X) o) :=
    fun o h1 _ => by rw [nX]; exact B.rtNode E.hN h1
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
  · rw [kX]; exact B.rtKs (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact B.rtKs (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, -, -⟩ := tm_of ar hA hX (slSets_conv K) E hk hcp LP h
    exact rtk_tcb hX ht (o := 3528#u64) (by simp) (by simp) (by simp)
  · rw [eRh] at h ⊢
    obtain ⟨ht, hz, hin, hmx, -⟩ := rh_of ar hA hX (slSets_conv K) E hk hcp LP h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 hk hcp ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    refine ⟨rtk_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp), ?_⟩
    generalize L.mem s (scA (L.mem s (rhA (L := L) s))) = sc at hz hin hmx
    obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
    have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
      lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 hk hcp
        (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
    have hW : RefillsWF st X sc (K.heap.scBits sc) :=
      ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
    exact ScAcc.head (scAccRT hX hz) hW

set_option maxHeartbeats 4000000 in
/-- **The trap arm's words before the decided thread's at a prefix state are region-tagged or kernel-static** (the
region facts of `fltDec_nu`). -/
theorem fltDecT_rt (hA : P0.ArchTotal ar) {s : S} (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) : FltDecT (L := L) (RTK K) X (L.curW s) := by
  have B := F.B
  have E := F.E
  have hX := B.regionOKX
  have hK := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_rt ar hA B E LP
  have hcH := E.hSt.1
  have fs := rtk_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
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
  exact ⟨rtk_ep hX hpH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE]), rtk_ep hX hpH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD])
    (by simp [layout.ep.HEAD])⟩

set_option maxHeartbeats 4000000 in
/-- **The ReplyRecv arm's words before the replied thread's at a prefix state are region-tagged or kernel-static**
(the region facts of `rrDR_nu` / `rrDec_nu`). -/
theorem rrDecT_rt (hA : P0.ArchTotal ar) {s : S} (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    RrDecT (L := L) (RTK K) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have hC := F.C
  have Hh := F.Hh
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_rt ar hA B E LP
  have hcH := E.hSt.1
  obtain ⟨hrp, hep⟩ := B.rrG hC.fd hS (hC.arm hS)
  obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have tw : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      RTK K (core.num.U64.wrapping_add (L.curW s) o) := fun o h1 h2 h3 => rtk_tcb hX hcH h1 h2 h3
  obtain ⟨hz, -, -, -⟩ := Hh.csc hS
  have eS : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
  refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, tw layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega)
    (by rw [st_val]), tw 3464#u64 (by simp) (by simp) (by simp), ?_, tw 3592#u64 (by simp) (by simp) (by simp),
    rtk_reg hX hcH (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO]),
    tw 3368#u64 (by simp) (by simp) (by simp), tw 3448#u64 (by simp) (by simp) (by simp), ?_,
    rtk_rp hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB]),
    rtk_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT]),
    rtk_ep hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE]) (by simp [layout.ep.TAIL_STATE])⟩
  · rw [eS]
    exact rtk_scw hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX]) (by simp [layout.sc.REFILL_MAX])
  · intro nt hnt hne
    have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
    have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
    subst en
    have h0 : L.mem X (boundA (L.curW s)) ≠ 0#u64 := fun h0 => by rw [h0] at hne; simp at hne
    have eB : L.mem X (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hcH 3368#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT hcH hk hcp hcH (by simp) (by simp) (by simp) (by simp))
    have hn := (ntf_of ar hA hX (slSets_conv K) E hk hcp LP (by rw [← eB]; exact h0)).1
    rw [eB]
    obtain ⟨r1, -, -⟩ := hX.ntW _ hn layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
      (by simp [layout.ntfn.TAIL_STATE])
    obtain ⟨r2, -, -⟩ := hX.ntW _ hn layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    exact ⟨rtk_of r1 (by simp), rtk_of r2 (by simp)⟩

/-- **The head refill of an SC homed here at the prefix state is region-tagged** (`rdHead_hereN`'s region facts). -/
theorem rdHead_hereRT (hA : P0.ArchTotal ar) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (Hh : SlHere (st := st) K K.heap.scBits K.heap.scs found s) {a X a1}
    (LP : LocalPre (st := st) ar s a (X, a1))
    {sc : U64} (hs : ScHere (st := st) K K.heap.scBits K.heap.scs s sc) : RdHead (L := L) (RTK K) X sc := by
  obtain ⟨hz, hin, hmx, -⟩ := hs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  have hW : RefillsWF st X sc (K.heap.scBits sc) :=
    ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
  exact ScAcc.head (scAccRT hX hz) hW

variable {Rd : U64 → Prop} {σ : S} {a : A}

set_option maxHeartbeats 4000000 in
/-- **The sl body at an entry whose decided thread is another core's is `InsA` in its re-annotated form** (the
`InsA` twin of `sl_fh_safe`; module docstring). -/
theorem sl_fh_insA {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b) (hA : P0.ArchTotal ar) {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64}
    (hc : L.cpu σ = c) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ) {R0 Qv : U64 → Prop}
    (hGQ : ∀ b, G b → Qv b)
    (D : SlFhR (st := st) ar found Rd σ a) (hR0 : ∀ q, Rd q → (R0 q ∧ Qv q) ∧ ¬ User q)
    (lv : SlLive st found.1 σ)
    (hgo : (R0 (affA (slThr st found.1 σ)) ∧ Qv (affA (slThr st found.1 σ))) ∧ ¬ User (affA (slThr st found.1 σ)))
    (hρd : ρ (affA (slThr st found.1 σ)) ≠ c)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hDU : ∀ q, SlDS (L := L) σ q → ¬ User q)
    (hH : ∀ x, SlDS (L := L) σ x → HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, SlDS (L := L) σ b → StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v)))
    (hRdG : ∀ b, Rd b → ¬ G b) (hWG : ∀ b, SlFhW (slThr st found.1 σ) b → ¬ G b)
    (hDG : ∀ b, SlDS (L := L) σ b → ¬ G b) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅
        (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_syscall_local n found) ∅ a)) := by
  have ht := F.N.hthr lv
  have hX := F.B.regionOKX
  have aD : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      Aligned (core.num.U64.wrapping_add (slThr st found.1 σ) o) :=
    fun o h1 h2 h3 => (hX.tcbW _ ht o h1 h2 h3).2.2
  have hAa : Aligned (affA (slThr st found.1 σ)) := aD 3520#u64 (by simp) (by simp) (by simp)
  refine insA_narrow_tr_gd ar hQ hL hO hmk hGo hGko hGU _ hc hGQ
    (Rc := fun b => Rd b ∨ b = affA (slThr st found.1 σ))
    (Rg := fun b => Rd b ∨ SlFhW (slThr st found.1 σ) b) (Wd := SlDS (L := L) σ)
    (by rintro b (hb | rfl); exacts [D.al b hb, hAa])
    (by rintro q (hq | rfl); exacts [hR0 q hq, hgo])
    (by
      rintro b (hb | rfl | rfl | rfl | rfl | rfl)
      · exact D.al b hb
      · exact aD 3360#u64 (by simp) (by simp) (by simp)
      · rw [stA_eq]; exact aD 3328#u64 (by simp) (by simp) (by simp)
      · exact aD 3376#u64 (by simp) (by simp) (by simp)
      · exact aD 3464#u64 (by simp) (by simp) (by simp)
      · exact hAa)
    (by rintro b (hb | hb); exacts [hRdG b hb, hWG b hb])
    (fun b hb => Or.inr (hDG b hb))
    (fun x hx => ⟨(SlDS.ws F.P.preG hx).1, fun _ => hH x hx⟩)
    hRPO hρμ ?_
  intro s sc sk _ hag
  have G0 : Ag st Rd σ s := ⟨sk, sc, fun b hb => (hag b (Or.inl hb)).trans (hRdρ b hb)⟩
  have hoff : L.mem s (affA (slThr st found.1 σ)) ≠ L.cpu σ := by rw [hag _ (Or.inr rfl), hc]; exact hρd
  exact slfh_run ar hA F (Ro := fun x => R0 x ∧ Qv x) D hR0 lv hgo hDU hSO G0 hoff

end sl

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg VEq Safe narrowSP PO HeldV InsA InsAP insAP_of_insA insA_narrow)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-- **A word off `K.ptes` that is region-tagged or kernel-static is no paging word of the epoch.** -/
theorem rt_notPWE' {K : KLayoutP} (hK : RegionOKP K) {E : U64 → U64} {b : U64} (hp : b ∉ K.ptes)
    (hr : RTK K.toKLayout b) : ¬ PWE K E b := by
  intro hw
  rcases hr with hr | ⟨o, ho, rfl⟩
  · exact hr (pwe_region hK hw)
  · rcases hw with hw | hw
    · exact hp hw
    · exact hw.2.2.2.2 o ho rfl

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **U9's armed sl program is `InsA` at a view start whose decided thread is another core's** (the `InsA`
counterpart of `sl_fh_annV`; module docstring). -/
theorem sl_fh_insA_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hU : UserOKP K)
    (nv : K.vcpus = ∅) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ) {σ : S} {a : A}
    (F : SlOF (st := st) ar K.toKLayout Locks (view K.toKLayout c ρ) n found Cs Ω Sg Ac σ)
    (V : SlVC (L := L) K c ρ σ) (hl : Locks σ = hs)
    (lv : SlLive st found.1 σ) (hρ : ρ (fld (slThr st found.1 σ) oAFFINITY) ≠ c) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout Locks)) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_syscall_local n found) ∅ a)) := by
  have hK := V.hK
  have hc := V.cpu
  have B := F.B
  have E := F.E
  have hX := B.regionOKX
  have hK0 := B.regionOK
  obtain ⟨hk, hcp⟩ := B.kc
  have ht := F.N.hthr lv
  -- the read sets, cut to the region-tagged and kernel-static words
  let Rd : U64 → Prop := fun q =>
    ((SlRS (st := st) K.toKLayout Locks σ q ∧ NU K.toKLayout q) ∧ SR K c ρ q) ∧ RTK K.toKLayout q
  have PD := preDec_v ar V B E
  have D : SlFhR (st := st) ar found Rd σ a :=
    { al := fun b hb => hb.1.1.1.1
      pd := ⟨fun o h1 h2 => ⟨⟨⟨(F.P.preG.nd o h1 h2).1, B.nuNode E.hN h1 h2⟩, PD.nd o h1 h2⟩, B.rtNode E.hN h1⟩,
        Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
        ⟨⟨⟨F.P.preG.fl, nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp)⟩, PD.fl⟩,
          rtk_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp)⟩,
        ⟨⟨⟨F.P.preG.nx, nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])⟩, PD.nx⟩,
          rtk_reg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])⟩,
        Or.inl rfl⟩
      hd := fun X a1 csc LP hcs => by
        have h1 := F.P.hhd a X a1 csc LP hcs
        obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
        have e : csc = L.cscW σ := by
          rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
          rw [← ok_inj_ff hcs]; exact ecs
        subst e
        exact RdHead.meet (RdHead.meet (RdHead.meet h1 (rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs))
          (rdHead_v ar hA V B E F.Hh LP F.Hh.cs V.csc)) (rdHead_hereRT ar hA hX E F.Hh LP F.Hh.cs)
      fT := fun hS X a1 LP => FltDecT.meet (FltDecT.meet (FltDecT.meet (F.D.fT hS a X a1 LP)
        (FltDec.toT (fltDec_nu ar hA B E LP))) (fltDecT_v ar hA F V LP)) (fltDecT_rt ar hA F LP)
      rT := fun hS X a1 LP => RrDecT.meet (RrDecT.meet (RrDecT.meet (F.D.rT hS a X a1 LP)
        (RrDec.toT (rrDec_nu ar hA F hS LP))) (rrDecT_v0 ar hA F V hS LP (rrDR0_v ar hA F V hS LP)))
        (rrDecT_rt ar hA F hS LP) }
  have hR0 : ∀ q, Rd q → (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout Locks)) σ q ∧
      VO K c ρ q) ∧ q ∉ K.user := fun q hq =>
    ⟨⟨⟨⟨hq.1.1.1, not_vData_empty nv⟩, hq.1.2.2⟩, hq.1.2.1.2⟩, hq.1.1.2.2⟩
  -- the decided thread's `AFFINITY`
  have afI := F.I.af lv
  obtain ⟨rA, -, -⟩ := hX.tcbW _ ht 3520#u64 (by simp) (by simp) (by simp)
  have rA' : region K.toKLayout (affA (slThr st found.1 σ)) = .tcb (slThr st found.1 σ) := rA
  have hpA : affA (slThr st found.1 σ) ∉ K.ptes := fun hp => by
    have h := hK.none _ hp
    rw [rA'] at h
    cases h
  have hgo : (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout Locks)) σ
      (affA (slThr st found.1 σ)) ∧ VO K c ρ (affA (slThr st found.1 σ))) ∧ affA (slThr st found.1 σ) ∉ K.user := by
    refine ⟨⟨⟨⟨afI.1, not_vData_empty nv⟩, hpA⟩, ?_⟩, hX.kern _ (by rw [rA']; intro h; cases h)⟩
    show ownP K (view K.toKLayout c ρ) (affA (slThr st found.1 σ)) = ownP K ρ (affA (slThr st found.1 σ))
    rw [ownP_eq_own nv hpA, ownP_eq_own nv hpA]
    exact (OwnMap.own_aff_gate hK0 ht _).trans (OwnMap.own_aff_gate hK0 ht _).symm
  have hρd : ρ (affA (slThr st found.1 σ)) ≠ c := by rw [OwnMap.affA_fld]; exact hρ
  -- the paging words of the epoch
  have hnG : ∀ b, region K.toKLayout b ≠ .none → ¬ PWE K E' b := fun b hb hp => hb (pwe_region hK hp)
  have hRdG : ∀ b, Rd b → ¬ PWE K E' b := fun b hb => rt_notPWE' hK hb.1.2.2 hb.2
  have tR : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      region K.toKLayout (core.num.U64.wrapping_add (slThr st found.1 σ) o) = .tcb (slThr st found.1 σ) :=
    fun o h1 h2 h3 => (hX.tcbW _ ht o h1 h2 h3).1
  have hWG : ∀ b, SlFhW (slThr st found.1 σ) b → ¬ PWE K E' b := by
    rintro b (rfl | rfl | rfl | rfl | rfl)
    · have h := tR 3360#u64 (by simp) (by simp) (by simp)
      exact hnG _ (by unfold replyA; rw [h]; simp)
    · have h := tR 3328#u64 (by simp) (by simp) (by simp)
      exact hnG _ (by rw [stA_eq, h]; simp)
    · have h := tR 3376#u64 (by simp) (by simp) (by simp)
      exact hnG _ (by rw [h]; simp)
    · have h := tR 3464#u64 (by simp) (by simp) (by simp)
      exact hnG _ (by unfold scA; rw [h]; simp)
    · exact hnG _ (by rw [rA']; simp)
  have hDG : ∀ b, SlDS (L := L) σ b → ¬ PWE K E' b := fun b hb => by
    rcases slDS_region hX E.hN E.hT E.hcT E.hSt.1 hk hcp hb with h | ⟨h, -⟩
    · exact hnG _ (by rw [h]; simp)
    · exact hnG _ (by rw [h]; simp)
  -- the memories
  have hRdρ : ∀ b, Rd b → ρ b = L.mem σ b := fun b hb =>
    hb.1.2.1.1.symm.trans (V.hm b hb.1.1.2.1 hb.1.1.2.2).symm
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => V.hm x hx hu
  have hRPO : ∀ x, x ∉ K.user →
      (rsE (· ∈ K.ptes) (rsV K.toKLayoutV (SlRS (st := st) K.toKLayout Locks)) σ x ∧ VO K c ρ x) →
      PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm (hx.1.1.1.2.resolve_left hu)
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have hDU := slDS_nu hX F.N
  have PA := preAcc_v ar V B E
  have hH : ∀ x, SlDS (L := L) σ x → HeldV c hs (ownP K μ x) := by
    intro x hx
    have hW := (SlDS.ws F.P.preG hx).2.resolve_left (hDU x hx)
    have hr := slDS_region hX E.hN E.hT E.hcT E.hSt.1 hk hcp hx
    have hpx : x ∉ K.ptes := fun hp => by
      have h := hK.none _ hp
      rcases hr with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    have hvn : VN K c ρ x := by
      rcases hx with rfl | rfl | rfl
      · exact PA.fi.1
      · exact (PA.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2.1
      · exact (PA.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2.1
    have h1 : HeldV c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hpx, ← hc, ← hl]
      unfold WPerm at hW
      revert hW
      cases OwnMap.own K.toKLayout (L.mem σ) x <;> exact id
    rw [eown, hvn.2] at h1
    rw [hV.1 _ (Or.inl h1)]
    exact h1
  have hSO : ∀ (z : S) b v, SlDS (L := L) σ b →
      StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem z)
        (L.mem (L.wr z b v)) := by
    intro z b v hb
    have ha := (SlDS.ws F.P.preG hb).1
    have hsw : SafeW K.toKLayout b := by
      rcases slDS_region hX E.hN E.hT E.hcT E.hSt.1 hk hcp hb with h | ⟨h, hv⟩
      · exact Or.inl ⟨_, h⟩
      · exact Or.inr (Or.inl ⟨_, 392, E.hSt.1, h, by omega, hv, by omega, by omega, by omega, by omega, by omega,
          by omega⟩)
    exact stepOK_safeP hK nv B.ioLayA ha hsw
  exact PathObl.sl_fh_insA (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) hmk (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) hA hc F (fun b hb => vo_of_pwe hK hb) D hR0 lv hgo hρd
    hRdρ hRPO (fun x hx => hV.2.1 x hx) hDU hH hSO hRdG hWG hDG

end main

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

set_option maxHeartbeats 4000000 in
/-- **The sl body's re-annotation is `InsA` at every view start whose decided thread is not homed** (module
docstring; the `InsA` counterpart of `sl_k0_fhB`). -/
theorem sl_k0_insAF (j : SlArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (nv : K.vcpus = ∅) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (h0 : SlV0 st K c ρ) (hF : ¬ SlHome st K c ρ j)
    (hS : StartAt (fl4LocW11JB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  by_cases hp : (slSlotB st ar hA (masksWr_plain st) L.total a0).Prem j K.toKLayoutV (view K.toKLayout c ρ)
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = (slSlotB st ar hA (masksWr_plain st) L.total a0).path j K.toKLayoutV (view K.toKLayout c ρ)
          hK.base hU.base hp →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := hS'
      have hc' : L.cpu σ = c := hc
      have hl' : j.Locks σ = hs := hl
      have hm' : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
      obtain ⟨⟨hJ0, hq0⟩, hQP0⟩ := id hpre
      have hJ0' : SlJAt (L := L) K.toKLayout σ := hJ0
      have hq0' : Fl4Proofs.P2.PathObl.SlQ st ar j.Locks j.n j.found j.Cs j.Ω j.Sg j.Ac K.toKLayout
          (view K.toKLayout c ρ) σ := hq0
      have hQP0' : QPs K st σ := hQP0
      have F0 := slOF_of ar L.total hA a0 hJ0' hq0'
      have V0 := slVC_of ar nv hK hU F0 hQP0' hc' hm' h0
      have hfor : SlLive st j.found.1 σ ∧ ρ (fld (slThr st j.found.1 σ) oAFFINITY) ≠ c := by
        by_contra hn
        exact hF ⟨σ, hc', hQP0'.ksb, hm', fun lv => by_contra fun hne => hn ⟨lv, hne⟩⟩
      have h := sl_fh_insA_annV ar hA (masksWr_plain st) hU nv E' hV F0 V0 hl' hfor.1 hfor.2 (a := a)
      unfold LocalPath.body
      first
        | (rw [hc]; exact h)
        | (convert h using 4 <;> first | rfl | exact hc | exact hc.symm)
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (SlotC.fam_pos _ _ hp) hS
  · have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout)
        (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) (· ∈ K.user)) (W : AvoidV K.toKLayoutV P)
        (hAv : AvoidP K ((LocalPath.cutLiftV hK.base hU.base
          (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv (view K.toKLayout c ρ)) P W).rJ K (fun b hb => Or.inl hb))),
        P = LocalPath.void (fl4Dflt st ar (masksWr_plain st)) (OwnMap.ko_aligned hK.base.base hU.base.base
          (view K.toKLayout c ρ)) →
        StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx (view K.toKLayout c ρ)) _ hAv) c hs
          (view K.toKLayout c ρ) k0 →
        InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
          (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
      rintro P W hAv rfl hS'
      obtain ⟨σ, a, hpre, -⟩ := hS'
      exact absurd hpre.1 id
    exact key _ _ (allB st ar hA (masksWr_plain st) L.total a0 (.sl j) K (view K.toKLayout c ρ) hK hU)
      (dif_neg hp) hS

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **`sl_insA_annV_all` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem sl_insA_annV_all_C (P : LocPlatCR st arI AR MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : SlArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.sl j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  by_cases hH : SlHome st K c ρ j
  · exact sl_insA_annV_h_C st ar hA a0 P E nv hC J hsf hM hV hH
  · have h' : StartU2B st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.sl j) := hsf
    have hE := epochPteN_view_of J nv hM hV
    have hS := startAt_slB_C st ar hA a0 P.run (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
    have h0 := sl_v0_SFB_C st ar hA a0 P (hK := hK) (hU := hU) hC nv hsf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact sl_k0_insAF st ar hA a0 j K hK hU nv c _ ρ s.mem k E hV h0 hH hS

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every sl start without a VCPU** (module docstring; gen 48's
`sl_insA_annV_h` where the decided thread is homed). -/
theorem sl_insA_annV_all (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR) {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {j : SlArg S} (E : U64 → U64) (nv : K.vcpus = ∅)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
      (.inl (.sl j)))
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) :=
  sl_insA_annV_all_C st ar hA a0 (locPlatCR_of P hIoa) E nv hC J hsf hM hV

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The sl indices of the PageMap index type. -/
def SlPm : IxV13Pm S → Prop
  | .inl (.inl (.sl _)) => True
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`insAP_sl_view` on the re-based platform** (gen 54, in place: `P : LocPlatCR` for `P : LocPlat` / `hIoa`). -/
theorem insAP_sl_view_C (P : LocPlatCR st arI AR MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : SlPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.sl j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.sl j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (sl_insA_annV_all_C st ar hA a0 P E nv hC J hsf' hM hV)

set_option maxHeartbeats 4000000 in
/-- **`InsV15V`'s obligation of `nativePmKAD B` at every sl start** (module docstring). -/
theorem insAP_sl_view (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (nv : K.vcpus = ∅) (hx : SlPm (S := S) i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch)
    (J : EpochJV K E s) (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) :=
  insAP_sl_view_C st ar hA a0 (locPlatCR_of P hIoa) B E nv hx hC J hM hV hsf

end pm

end
end Fl4Proofs.P2.E2EP
