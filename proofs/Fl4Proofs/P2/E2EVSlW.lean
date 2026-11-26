/-
P2 (line vlift, gen 4): **syscall_local's read words lie outside the VCPU data words**, word by word.

syscall_local (`sl_localPath`, `P2/SlLP.lean`) reads from `SlRS s` (aligned user words and words `own` lets it read),
which holds the VCPU data words (gate-owned, region `.none`). To cut its read set to `rsV K SlRS`
(`LocalPath.cutV`, `P2/E2EVCutP.lean`) every word its runs read must be shown outside `VData`. This module redoes
the word facts of `P2/SlDecL.lean` / `P2/SlAccL.lean` for the cut set `SlRV K Locks s = rsV K (SlRS K Locks) s`:
each producer's word is in `SlRS s` (the old lemma) and is no VCPU data word, because

* it lies in a region other than `.none` (TCB words `RegionOKX.tcbW`, slot words `RegionOK.slot` /
  `RegionOKX.tslot`, node words `RegionOKX.node`, SC words `RegionOKX.scW`, endpoint / reply words
  `RegionOKX.epW` / `rpW`, notification words `RegionOKX.ntW`) and `RegionOKV.none` puts every VCPU word in region
  `.none` (`notVData_of_region'`); or
* it is a kernel global of the kernel-state block (`VcpuKs`, derived in `P2/E2EVHeap.lean` from `VcpuHeap` [J] and
  P3's `JKern.hksIn`); or
* it is an ASID-table or ASID-pool word (`TabNoV`, derived by `tabNoV_of` from `VcpuTabOff` [J] / `PoolObj` [J]); or
* it is a user word (`UserObj` [J], `user_noVcpu`).

Then the bundles the guard walks take, for the cut set: `PreAcc` (`preAccV`), `RdHead` (`rdHead_hereV`, `hhdV`),
`SlCom` (`slComV`) and the declining arms' `SlDecInR` (`slDecInV`; `SlDecInR` is `SlDecIn` over any read set `R`).
No premise beyond those named arguments.
-/
import Fl4Proofs.P2.SlLP
import Fl4Proofs.P2.E2EVHeap
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Locks : S → U64 → Prop}

/-- **syscall_local's cut read set**: `SlRS` without the VCPU data words. -/
abbrev SlRV (K : KLayoutV) (Locks : S → U64 → Prop) (s : S) : U64 → Prop :=
  rsV K (SlRS (st := st) K.toKLayout Locks) s

/-! ## Words outside the VCPU data words -/

theorem nv_tcb (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) : ¬ VData K (core.num.U64.wrapping_add t o) :=
  notVData_of_region' hK (by rw [(hX.tcbW t ht o h1 h2 h3).1]; intro e; cases e)

theorem nv_tslot (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) :
    ¬ VData K (slotIdx t i) ∧ ¬ VData K (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨hs, -, h8, -, -, -⟩ := hX.tslot t ht i hi
  exact ⟨notVData_of_region' hK (by rw [hK.base.slot _ hs]; intro e; cases e),
    notVData_of_region' hK (by rw [h8]; intro e; cases e)⟩

theorem nv_sc (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) {b : U64} (hb : InSC sc z b) : ¬ VData K b :=
  notVData_of_region' hK (by rw [hX.scW sc z hz b hb]; intro e; cases e)

theorem nv_obj (hK : RegionOKV K) {x p : U64} (h : region K.toKLayout x = .obj p) : ¬ VData K x :=
  notVData_of_region' hK (by rw [h]; intro e; cases e)

theorem nv_ks (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S} (hk : L.ksb s = K.ksb) {o : U64}
    (ho : o.val < 13568) : ¬ VData K (core.num.U64.wrapping_add (L.ksb s) o) := by
  rw [hk]; exact notVData_of_noVcpu (noVcpu_ks hks hf ho)

theorem nv_user (hH : HeapOK K.heap) (hV : VcpuHeap K) (hU : UserObj K) {b : U64} (hb : b ∈ K.user) :
    ¬ VData K b :=
  notVData_of_noVcpu (user_noVcpu hH hV hU hb)

/-! ## The producers for the cut set -/

theorem sv_tcbGate (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : GateField o.val) {s : S} :
    SlRV (st := st) K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨rs_tcb_gate hX ht h1 h2 h3 hg, nv_tcb hK hX ht h1 h2 h3⟩

theorem sv_tcbHome (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val)
    (hT : ¬ TimerField o.val) (hG : ¬ GField o.val) {s : S} (hh : L.mem s (affA t) = L.cpu s) :
    SlRV (st := st) K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨(rs_tcb_home hX ht h1 h2 h3 hg hT hG hh).1, nv_tcb hK hX ht h1 h2 h3⟩

theorem sv_tcbSafe (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val)
    (hT : ¬ TimerField o.val) {s : S} (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) :
    SlRV (st := st) K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨(rw_tcb_safe hX ht h1 h2 h3 hg hT hs).1, nv_tcb hK hX ht h1 h2 h3⟩

theorem sv_regs (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) {r : U64} (hr : r.val < 384) :
    SlRV (st := st) K Locks s (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact sv_tcbSafe hK hX ht (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
    (by simp only [TimerField]; omega) hs

theorem sv_tslot (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) {s : S} :
    SlRV (st := st) K Locks s (slotIdx t i) ∧
      SlRV (st := st) K Locks s (core.num.U64.wrapping_add (slotIdx t i) 8#u64) :=
  ⟨⟨(rs_tslot hK.base hX ht hi).1, (nv_tslot hK hX ht hi).1⟩,
    ⟨(rs_tslot hK.base hX ht hi).2, (nv_tslot hK hX ht hi).2⟩⟩

theorem sv_node (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {T : Set U64} {s : S}
    (hN : NodePlaced st T s (L.cpu s)) (hk : L.ksb s = K.ksb) (hc : (L.cpu s).val < K.ncores) {o : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) : SlRV (st := st) K Locks s (L.nodeAt s (L.cpu s) o) := by
  have v := nodeAt_val hN ho
  have hr : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    hX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact ⟨(rs_node hX hN hk hc ho h8).1, notVData_of_region' hK (by rw [hr]; intro e; cases e)⟩

theorem sv_ks (hX : RegionOKX K.toKLayout) (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {T : Set U64}
    {s : S} (hN : NodePlaced st T s (L.cpu s)) (hk : L.ksb s = K.ksb) {o : U64} (ho : o.val < 256)
    (h8 : o.val % 8 = 0) : SlRV (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb s) o) :=
  ⟨rs_ks hX hN hk ho h8, nv_ks hks hf hk (by omega)⟩

theorem sv_timer (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hd : (L.mem s (fld t oTIMER_DEADLINE)).val ≠ 0)
    (hc : treeCore (L.mem s (fld t oTIMER_HEIGHT)) = L.cpu s) :
    SlRV (st := st) K Locks s (core.num.U64.wrapping_add t 3528#u64) :=
  ⟨rs_timer hK.base hX ht hd hc, nv_tcb hK hX ht (by simp) (by simp) (by simp)⟩

theorem sv_ntfn (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {s : S} {t nt o : U64}
    (hn : K.heap nt = some .ntfn) (hb : L.mem s (fld nt 24#u64) = t) (ht : K.heap t = some .tcb)
    (hh : L.mem s (affA t) = L.cpu s) (ho : o.val < 64) (h8 : o.val % 8 = 0) (h24 : o.val ≠ 24) :
    SlRV (st := st) K Locks s (core.num.U64.wrapping_add nt o) :=
  ⟨rs_ntfn hX hn hb ht hh ho h8 h24,
    notVData_of_region' hK (by rw [(hX.ntW nt hn o ho h8).1]; intro e; cases e)⟩

theorem sv_lock (hK : RegionOKV K) {s : S} {x p : U64} (ha : Aligned x) (h : region K.toKLayout x = .obj p)
    (hl : Locks s p) : SlRV (st := st) K Locks s x :=
  ⟨slRS_of_lock ha h hl, nv_obj hK h⟩

theorem sv_user (hH : HeapOK K.heap) (hV : VcpuHeap K) (hU : UserObj K) {s : S} {x : U64}
    (h : Aligned x ∧ x ∈ K.user) : SlRV (st := st) K Locks s x :=
  ⟨(slRW_of_user h).1, nv_user hH hV hU h.2⟩

/-- An SC homed here, for the cut read set. -/
theorem sv_scAcc (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {s : S} {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) (hc : L.mem s (fld sc 16#u64) = L.cpu s) :
    ScAcc (SlRV (st := st) K Locks s) (SlWS (st := st) K.toKLayout Locks s) sc z :=
  have H := scAcc_here (st := st) (Locks := Locks) hX hz hc
  ⟨fun b ha hb => ⟨H.rd b ha hb, nv_sc hK hX hz hb⟩, H.wr, H.cons⟩

/-- `scAcc_wn` for the cut read set. -/
theorem sv_scAccWN (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {s : S} {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) (hc : L.mem s (fld sc 16#u64) = L.cpu s) :
    ScAcc (SlRV (st := st) K Locks s) (SlWN (st := st) K.toKLayout Locks s) sc z :=
  have H := scAcc_wn (st := st) (Locks := Locks) hK.base hX hz hc
  ⟨fun b ha hb => ⟨H.rd b ha hb, nv_sc hK hX hz hb⟩, H.wr, H.cons⟩

/-! ## The bundles for the cut set -/

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- `preAcc_of` for the cut read set. -/
theorem preAccV (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) :
    PreAcc (L := L) (SlRV (st := st) K Locks s) (SlWS (st := st) K.toKLayout Locks s) s := by
  have P := preAcc_of ar hX E Hh
  have hc := E.hSt.1
  obtain ⟨KN, hKN, eKN⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 368 := by rw [hKN]; simp [layout.reg.NEXT_IP]
  refine ⟨fun o h1 h2 => ⟨sv_node hK hX E.hN Hh.ksb Hh.cpu h1 h2, (P.nd o h1 h2).2⟩,
    ⟨P.fl, nv_tcb hK hX hc (o := 3456#u64) (by simp) (by simp) (by simp)⟩, ⟨P.nx, ?_⟩, P.fi⟩
  rw [eKN]
  exact nv_tcb hK hX hc (by omega) (by omega) (by omega)

/-- `rdHead_here` for the cut read set. -/
theorem rdHead_hereV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    {sc : U64} (hs : ScHere (st := st) K.toKLayout Z Scs s sc) :
    RdHead (L := L) (SlRV (st := st) K Locks s) X sc := by
  obtain ⟨hz, hin, hmx, hco⟩ := hs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  have hW : RefillsWF st X sc (Z sc) :=
    ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
  exact ScAcc.head (sv_scAcc hK hX hz hco) hW

/-- `hhd_of` for the cut read set. -/
theorem hhdV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) {a X a1 csc} (LP : LocalPre (st := st) ar s a (X, a1))
    (hcs : sched.cur_sc st X = ok csc) : RdHead (L := L) (SlRV (st := st) K Locks s) X csc := by
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have e : csc = L.cscW s := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
    rw [← ok_inj_ff hcs]; exact ecs
  subst e
  exact rdHead_hereV ar hA hK hX E Hh LP Hh.cs

/-- `slCom_of` for the cut read set. -/
theorem slComV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hks : VcpuKs K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlCom (L := L) (SlRV (st := st) K Locks s) X := by
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → SlRV (st := st) K Locks s (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 => by rw [nX]; exact sv_node hK hX E.hN Hh.ksb Hh.cpu h1 h2
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
  · rw [kX]; exact sv_ks hX hks hf E.hN Hh.ksb (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact sv_ks hX hks hf E.hN Hh.ksb (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, hd, hc⟩ := Hh.tm h
    exact sv_timer hK hX ht hd hc
  · rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := Hh.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    exact ⟨sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      rdHead_hereV ar hA hK hX E Hh LP hs⟩

/-- **`SlDecIn` over any read set `R`** (`P2/SlHome.lean`'s `SlDecIn` is the case `R = SlRS s`). -/
structure SlDecInR (R : U64 → Prop) (found : U64 × U64) (s : S) : Prop where
  fT : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → FltDecT (L := L) R X (L.curW s)
  fD : SlTrap st s → SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s → ∀ a X a1,
    LocalPre (st := st) ar s a (X, a1) → DestDec (L := L) R X (slThr st found.1 s)
  rT : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) →
    RrDecT (L := L) R X (L.curW s) found.1 found.2
  rU : ¬ SlTrap st s → SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s → ∀ a X a1,
    LocalPre (st := st) ar s a (X, a1) → UDec (L := L) R X (slThr st found.1 s)

set_option maxHeartbeats 4000000 in
/-- **`slDecIn_of` for the cut read set.** -/
theorem slDecInV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hks : VcpuKs K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s) :
    SlDecInR (st := st) ar (SlRV (st := st) K Locks s) found s := by
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s :=
    slThrIn_of hK.base hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have hc := E.hSt.1
  have hcA : L.mem s (affA (L.curW s)) = L.cpu s := E.hSt.2.1
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have hfh : ∀ hS : SlTrap st s, ¬ VData K (fhA (L := L) s) ∧
      ¬ VData K (core.num.U64.wrapping_add (fhA (L := L) s) 8#u64) := fun _ =>
    nv_tslot hK hX hc (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have afV : ∀ lv : SlLive st found.1 s, SlRV (st := st) K Locks s (affA (slThr st found.1 s)) := fun lv =>
    ⟨(I.af lv).1, nv_tcb hK hX (N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)⟩
  refine ⟨fun hS a X a1 LP => ?_, fun hS lv hh a X a1 LP => ?_, fun hS a X a1 LP => ?_,
    fun hS lv hh a X a1 LP => ?_⟩
  · -- the trap arm, apart from the receiver
    have C := slComV ar hA hK hX hks hf E Hh LP
    obtain ⟨f0, f8, d0, d8⟩ := I.fh hS
    have ecap : obj.Slot.cap st (fhA (L := L) s) X = obj.Slot.cap st (fhA (L := L) s) s :=
      cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP f0.1 d0) (lp_mem ar hA E.hT E.hN E.hcT LP f8.1 d8)
    refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, ⟨⟨f0, (hfh hS).1⟩, ⟨f8, (hfh hS).2⟩⟩,
      fun ptr b x y g gr hcap => ?_⟩
    have hcap' : obj.Slot.cap st (fhA (L := L) s) s = ok (capability.Cap.Endpoint ptr b x y g gr) := by
      rw [← ecap]; exact hcap
    have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := by rw [resPtr_ok hcap']; rfl
    have hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s) := ⟨ptr, b, x, y, g, gr, hcap'⟩
    obtain ⟨r1, -, r2, -⟩ := I.eh hS hE
    have he := N.hep hS hE
    rw [hp] at r1 r2 he
    obtain ⟨q1, -⟩ := hX.epW _ he layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
    obtain ⟨q2, -⟩ := hX.epW _ he layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])
    exact ⟨⟨r2, nv_obj hK q2⟩, ⟨r1, nv_obj hK q1⟩⟩
  · -- the receiver, homed here
    have ht := N.hthr lv
    refine ⟨?_, afV lv, fun _ => ⟨sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      sv_tcbHome hK hX ht (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh,
      sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField])⟩⟩
    exact sv_tcbHome hK hX ht (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField]) hh
  · -- the ReplyRecv arm, apart from the replied thread
    have C := slComV ar hA hK hX hks hf E Hh LP
    obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have home : ∀ {o : U64}, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → ¬ GateField o.val →
        ¬ TimerField o.val → ¬ GField o.val →
        SlRV (st := st) K Locks s (core.num.U64.wrapping_add (L.curW s) o) := fun h1 h2 h3 h4 h5 h6 =>
      sv_tcbHome hK hX hc h1 h2 h3 h4 h5 h6 hcA
    have gate : ∀ {o : U64}, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → GateField o.val →
        SlRV (st := st) K Locks s (core.num.U64.wrapping_add (L.curW s) o) := fun h1 h2 h3 h4 =>
      sv_tcbGate hK hX hc h1 h2 h3 h4
    obtain ⟨hz, -, -, hco⟩ := Hh.csc hS
    have eS : L.mem X (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
      aT _ E.hcT 3464#u64 (by simp) (by simp) (by simp)
    obtain ⟨KM, hKM, eKM⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.MSG_INFO)
      (by simp [layout.reg.MSG_INFO, layout.reg.RSI])
    have hKM' : KM.val = 264 := by rw [hKM]; simp [layout.reg.MSG_INFO, layout.reg.RSI]
    obtain ⟨r1, a1'⟩ := hX.rpW _ (N.hrp hS) layout.reply.NEXT (by simp [layout.reply.NEXT])
      (by simp [layout.reply.NEXT])
    obtain ⟨r2, a2⟩ := hX.epW _ (Hh.ep hS) layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])
    obtain ⟨rt1, -⟩ := hX.rpW _ (N.hrp hS) layout.reply.TCB (by simp [layout.reply.TCB])
      (by simp [layout.reply.TCB])
    refine ⟨C.nd, C.dt, C.cd, C.bm, C.tm, C.rh, ?_, gate (by simp) (by simp) (by simp) (by simp [GateField]),
      ?_, home (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField]),
      ?_, gate (by simp) (by simp) (by simp) (by simp [GateField]),
      gate (by simp) (by simp) (by simp) (by simp [GateField]), fun nt hnt hne => ?_,
      ⟨(I.rt hS).1, nv_obj hK rt1⟩,
      sv_lock hK a1' r1 (N.lrp hS), sv_lock hK a2 r2 (E.hlk hS)⟩
    · rw [stA_eq]
      exact home (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])
    · rw [eS]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (sv_scAcc hK hX hz hco).rd _ am hin
    · rw [eKM]
      exact home (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
        (by simp only [TimerField]; omega) (by simp only [GField]; omega)
    · have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
      have en : nt = L.mem s (boundA (L.curW s)) := by
        rw [← ok_inj_ff e1]; exact aT _ E.hcT 3368#u64 (by simp) (by simp) (by simp)
      have hne' : L.mem s (boundA (L.curW s)) ≠ 0#u64 := by
        rw [← en]; intro h0; rw [h0] at hne; simp at hne
      obtain ⟨hn, hb⟩ := Hh.ntf hS hne'
      rw [en]
      exact ⟨sv_ntfn hK hX hn hb hc hcA (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])
          (by simp [layout.ntfn.TAIL_STATE]),
        sv_ntfn hK hX hn hb hc hcA (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])⟩
  · -- the replied thread, homed here
    have ht := N.hthr lv
    refine ⟨?_, sv_tcbHome hK hX ht (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh,
      sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]), afV lv,
      fun _ => ⟨sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
        sv_tcbHome hK hX ht (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
          (by simp [TimerField]) (by simp [GField]) hh,
        sv_tcbGate hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]), fun usc eu hne => ?_⟩⟩
    · rw [stA_eq]
      exact sv_tcbHome hK hX ht (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh
    · have eU : L.mem X (scA (slThr st found.1 s)) = L.mem s (scA (slThr st found.1 s)) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      have e1 : usc = L.mem s (scA (slThr st found.1 s)) := by
        rw [tcb_sc_ok] at eu; rw [← ok_inj_ff eu, eU]
      subst e1
      exact rdHead_hereV ar hA hK hX E Hh LP (Hh.usc hS lv hh hne)

end

end
end Fl4Proofs.P2.E2EV
