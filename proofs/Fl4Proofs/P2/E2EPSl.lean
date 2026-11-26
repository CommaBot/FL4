/-
P2 (line pte, gen 3): **syscall_local's runs read no word of an excluded set `Ex`**, for any `Ex` disjoint from the
words the walks read: the generic-set copy of `P2/E2EVSlW.lean`, `E2EVSlA.lean`, `E2EVSlD.lean` (vlift gen 4, the
`VData K` instance; those files are unchanged). Every declaration is the original's name with an `E` suffix.

The four facts about `Ex` the walks use (in place of the VCPU-specific ones):
* `RegionOKE Ex K` [J]: `RegionOK` and **no `Ex` word lies in a region other than `.none`** (TCB, slot, node, SC,
  endpoint / reply, notification words; was `RegionOKV.none` via `notVData_of_region'`);
* `KsNoE Ex K` [J]: **no `Ex` word in the kernel-state block** `[ksb, ksb + 13568)` (was `VcpuKs`);
* `UserNoE Ex K` [J]: **no `Ex` word is user memory** (was `UserObj`);
* `TabNoE Ex s` [J] (per state): **no `Ex` word is an ASID-table or ASID-pool word** (was `TabNoV`).
`VcpuHeap` is no longer used (its slots take `True`).

Results: `sl_avAccE`, `sl_avDecE`, `sl_avoidVE`, **`sl_avoidVKE`** (`AvoidE Ex (sl_localPathK …)`, with
`slJAt_fitE` giving the block's fit and `HeapOK` from `SlJAt`); the VCPU instance **`sl_avoidVK'`** recovers
`AvoidV K (sl_localPathK …)` from it (sanity check).
-/
import Fl4Proofs.P2.E2EVSlD
import Fl4Proofs.P2.E2EPCut
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

/-! ## The facts about the excluded set -/

/-- [J] `RegionOK` and no `Ex` word in a region other than `.none`. -/
structure RegionOKE (Ex : U64 → Prop) (K : KLayoutV) : Prop where
  base : RegionOK K.toKLayout
  reg : ∀ b, region K.toKLayout b ≠ .none → ¬ Ex b

/-- [J] No `Ex` word in the kernel-state block. -/
def KsNoE (Ex : U64 → Prop) (K : KLayoutV) : Prop :=
  ∀ o : U64, o.val < 13568 → ¬ Ex (core.num.U64.wrapping_add K.ksb o)

/-- [J] No `Ex` word is user memory. -/
def UserNoE (Ex : U64 → Prop) (K : KLayoutV) : Prop := ∀ b ∈ K.user, ¬ Ex b

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- [J] (per state) No `Ex` word is an ASID-table word or a word of a pool the table names. -/
def TabNoE (Ex : U64 → Prop) (s : S) : Prop :=
  ∀ hi : U64, hi.val < 2048 → ¬ Ex (atAF (L.ksb s) hi) ∧
    ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      ¬ Ex (peAF (L.mem s (atAF (L.ksb s) hi)) lo)

end


section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ex : U64 → Prop} {K : KLayoutV} {Locks : S → U64 → Prop}

/-- **syscall_local's cut read set**: `SlRS` without the VCPU data words. -/
abbrev SlRVE (Ex : U64 → Prop) (K : KLayoutV) (Locks : S → U64 → Prop) (s : S) : U64 → Prop :=
  Fl4Proofs.P2.E2EP.rsE Ex (SlRS (st := st) K.toKLayout Locks) s

/-! ## Words outside the VCPU data words -/

theorem nv_tcbE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) : ¬ Ex (core.num.U64.wrapping_add t o) :=
  hK.reg _ (by rw [(hX.tcbW t ht o h1 h2 h3).1]; intro e; cases e)

theorem nv_tslotE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) :
    ¬ Ex (slotIdx t i) ∧ ¬ Ex (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨hs, -, h8, -, -, -⟩ := hX.tslot t ht i hi
  exact ⟨hK.reg _ (by rw [hK.base.slot _ hs]; intro e; cases e),
    hK.reg _ (by rw [h8]; intro e; cases e)⟩

theorem nv_scE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) {b : U64} (hb : InSC sc z b) : ¬ Ex b :=
  hK.reg _ (by rw [hX.scW sc z hz b hb]; intro e; cases e)

theorem nv_objE (hK : RegionOKE Ex K) {x p : U64} (h : region K.toKLayout x = .obj p) : ¬ Ex x :=
  hK.reg _ (by rw [h]; intro e; cases e)

theorem nv_ksE (hks : KsNoE Ex K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S} (hk : L.ksb s = K.ksb) {o : U64}
    (ho : o.val < 13568) : ¬ Ex (core.num.U64.wrapping_add (L.ksb s) o) := by
  rw [hk]; exact hks o ho

theorem nv_userE (hH : HeapOK K.heap) (hV : True) (hU : UserNoE Ex K) {b : U64} (hb : b ∈ K.user) :
    ¬ Ex b :=
  hU b hb

/-! ## The producers for the cut set -/

theorem sv_tcbGateE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : GateField o.val) {s : S} :
    SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨rs_tcb_gate hX ht h1 h2 h3 hg, nv_tcbE hK hX ht h1 h2 h3⟩

theorem sv_tcbHomeE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val)
    (hT : ¬ TimerField o.val) (hG : ¬ GField o.val) {s : S} (hh : L.mem s (affA t) = L.cpu s) :
    SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨(rs_tcb_home hX ht h1 h2 h3 hg hT hG hh).1, nv_tcbE hK hX ht h1 h2 h3⟩

theorem sv_tcbSafeE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t o : U64} (ht : K.heap t = some .tcb)
    (h1 : 192 ≤ o.val) (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val)
    (hT : ¬ TimerField o.val) {s : S} (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) :
    SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add t o) :=
  ⟨(rw_tcb_safe hX ht h1 h2 h3 hg hT hs).1, nv_tcbE hK hX ht h1 h2 h3⟩

theorem sv_regsE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) {r : U64} (hr : r.val < 384) :
    SlRVE (st := st) Ex K Locks s (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact sv_tcbSafeE hK hX ht (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
    (by simp only [TimerField]; omega) hs

theorem sv_tslotE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) {s : S} :
    SlRVE (st := st) Ex K Locks s (slotIdx t i) ∧
      SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add (slotIdx t i) 8#u64) :=
  ⟨⟨(rs_tslot hK.base hX ht hi).1, (nv_tslotE hK hX ht hi).1⟩,
    ⟨(rs_tslot hK.base hX ht hi).2, (nv_tslotE hK hX ht hi).2⟩⟩

theorem sv_nodeE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {T : Set U64} {s : S}
    (hN : NodePlaced st T s (L.cpu s)) (hk : L.ksb s = K.ksb) (hc : (L.cpu s).val < K.ncores) {o : U64}
    (ho : o.val < 4288) (h8 : o.val % 8 = 0) : SlRVE (st := st) Ex K Locks s (L.nodeAt s (L.cpu s) o) := by
  have v := nodeAt_val hN ho
  have hr : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) :=
    hX.node _ _ ⟨hc, by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega,
      by rw [v]; simp only [LawfulStore.nodeBase, hk]; omega⟩
  exact ⟨(rs_node hX hN hk hc ho h8).1, hK.reg _ (by rw [hr]; intro e; cases e)⟩

theorem sv_ksE (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {T : Set U64}
    {s : S} (hN : NodePlaced st T s (L.cpu s)) (hk : L.ksb s = K.ksb) {o : U64} (ho : o.val < 256)
    (h8 : o.val % 8 = 0) : SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add (L.ksb s) o) :=
  ⟨rs_ks hX hN hk ho h8, nv_ksE hks hf hk (by omega)⟩

theorem sv_timerE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hd : (L.mem s (fld t oTIMER_DEADLINE)).val ≠ 0)
    (hc : treeCore (L.mem s (fld t oTIMER_HEIGHT)) = L.cpu s) :
    SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add t 3528#u64) :=
  ⟨rs_timer hK.base hX ht hd hc, nv_tcbE hK hX ht (by simp) (by simp) (by simp)⟩

theorem sv_ntfnE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {s : S} {t nt o : U64}
    (hn : K.heap nt = some .ntfn) (hb : L.mem s (fld nt 24#u64) = t) (ht : K.heap t = some .tcb)
    (hh : L.mem s (affA t) = L.cpu s) (ho : o.val < 64) (h8 : o.val % 8 = 0) (h24 : o.val ≠ 24) :
    SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add nt o) :=
  ⟨rs_ntfn hX hn hb ht hh ho h8 h24,
    hK.reg _ (by rw [(hX.ntW nt hn o ho h8).1]; intro e; cases e)⟩

theorem sv_lockE (hK : RegionOKE Ex K) {s : S} {x p : U64} (ha : Aligned x) (h : region K.toKLayout x = .obj p)
    (hl : Locks s p) : SlRVE (st := st) Ex K Locks s x :=
  ⟨slRS_of_lock ha h hl, nv_objE hK h⟩

theorem sv_userE (hH : HeapOK K.heap) (hV : True) (hU : UserNoE Ex K) {s : S} {x : U64}
    (h : Aligned x ∧ x ∈ K.user) : SlRVE (st := st) Ex K Locks s x :=
  ⟨(slRW_of_user h).1, nv_userE hH hV hU h.2⟩

/-- An SC homed here, for the cut read set. -/
theorem sv_scAccE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {s : S} {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) (hc : L.mem s (fld sc 16#u64) = L.cpu s) :
    ScAcc (SlRVE (st := st) Ex K Locks s) (SlWS (st := st) K.toKLayout Locks s) sc z :=
  have H := scAcc_here (st := st) (Locks := Locks) hX hz hc
  ⟨fun b ha hb => ⟨H.rd b ha hb, nv_scE hK hX hz hb⟩, H.wr, H.cons⟩

/-- `scAcc_wn` for the cut read set. -/
theorem sv_scAccWNE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {s : S} {sc : U64} {z : Nat}
    (hz : K.heap sc = some (.sc z)) (hc : L.mem s (fld sc 16#u64) = L.cpu s) :
    ScAcc (SlRVE (st := st) Ex K Locks s) (SlWN (st := st) K.toKLayout Locks s) sc z :=
  have H := scAcc_wn (st := st) (Locks := Locks) hK.base hX hz hc
  ⟨fun b ha hb => ⟨H.rd b ha hb, nv_scE hK hX hz hb⟩, H.wr, H.cons⟩

/-! ## The bundles for the cut set -/

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- `preAcc_of` for the cut read set. -/
theorem preAccVE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) :
    PreAcc (L := L) (SlRVE (st := st) Ex K Locks s) (SlWS (st := st) K.toKLayout Locks s) s := by
  have P := preAcc_of ar hX E Hh
  have hc := E.hSt.1
  obtain ⟨KN, hKN, eKN⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])
  have hKN' : KN.val = 368 := by rw [hKN]; simp [layout.reg.NEXT_IP]
  refine ⟨fun o h1 h2 => ⟨sv_nodeE hK hX E.hN Hh.ksb Hh.cpu h1 h2, (P.nd o h1 h2).2⟩,
    ⟨P.fl, nv_tcbE hK hX hc (o := 3456#u64) (by simp) (by simp) (by simp)⟩, ⟨P.nx, ?_⟩, P.fi⟩
  rw [eKN]
  exact nv_tcbE hK hX hc (by omega) (by omega) (by omega)

/-- `rdHead_here` for the cut read set. -/
theorem rdHead_hereVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    {sc : U64} (hs : ScHere (st := st) K.toKLayout Z Scs s sc) :
    RdHead (L := L) (SlRVE (st := st) Ex K Locks s) X sc := by
  obtain ⟨hz, hin, hmx, hco⟩ := hs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  have hW : RefillsWF st X sc (Z sc) :=
    ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
  exact ScAcc.head (sv_scAccE hK hX hz hco) hW

/-- `hhd_of` for the cut read set. -/
theorem hhdVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) {a X a1 csc} (LP : LocalPre (st := st) ar s a (X, a1))
    (hcs : sched.cur_sc st X = ok csc) : RdHead (L := L) (SlRVE (st := st) Ex K Locks s) X csc := by
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have e : csc = L.cscW s := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
    rw [← ok_inj_ff hcs]; exact ecs
  subst e
  exact rdHead_hereVE ar hA hK hX E Hh LP Hh.cs

/-- `slCom_of` for the cut read set. -/
theorem slComVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlCom (L := L) (SlRVE (st := st) Ex K Locks s) X := by
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → SlRVE (st := st) Ex K Locks s (L.nodeAt X (L.cpu X) o) :=
    fun o h1 h2 => by rw [nX]; exact sv_nodeE hK hX E.hN Hh.ksb Hh.cpu h1 h2
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
  · rw [kX]; exact sv_ksE hX hks hf E.hN Hh.ksb (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
  · rw [kX]; exact sv_ksE hX hks hf E.hN Hh.ksb (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
  · rw [eTm] at h ⊢
    obtain ⟨ht, hd, hc⟩ := Hh.tm h
    exact sv_timerE hK hX ht hd hc
  · rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := Hh.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    exact ⟨sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      rdHead_hereVE ar hA hK hX E Hh LP hs⟩

-- (`SlDecInR` is the original's, already generic in the read set.)

set_option maxHeartbeats 4000000 in
/-- **`slDecIn_of` for the cut read set.** -/
theorem slDecInVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s) :
    SlDecInR (st := st) ar (SlRVE (st := st) Ex K Locks s) found s := by
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s :=
    slThrIn_of hK.base hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have hc := E.hSt.1
  have hcA : L.mem s (affA (L.curW s)) = L.cpu s := E.hSt.2.1
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have hfh : ∀ hS : SlTrap st s, ¬ Ex (fhA (L := L) s) ∧
      ¬ Ex (core.num.U64.wrapping_add (fhA (L := L) s) 8#u64) := fun _ =>
    nv_tslotE hK hX hc (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have afV : ∀ lv : SlLive st found.1 s, SlRVE (st := st) Ex K Locks s (affA (slThr st found.1 s)) := fun lv =>
    ⟨(I.af lv).1, nv_tcbE hK hX (N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)⟩
  refine ⟨fun hS a X a1 LP => ?_, fun hS lv hh a X a1 LP => ?_, fun hS a X a1 LP => ?_,
    fun hS lv hh a X a1 LP => ?_⟩
  · -- the trap arm, apart from the receiver
    have C := slComVE ar hA hK hX hks hf E Hh LP
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
    exact ⟨⟨r2, nv_objE hK q2⟩, ⟨r1, nv_objE hK q1⟩⟩
  · -- the receiver, homed here
    have ht := N.hthr lv
    refine ⟨?_, afV lv, fun _ => ⟨sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
      sv_tcbHomeE hK hX ht (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh,
      sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField])⟩⟩
    exact sv_tcbHomeE hK hX ht (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField]) hh
  · -- the ReplyRecv arm, apart from the replied thread
    have C := slComVE ar hA hK hX hks hf E Hh LP
    obtain ⟨-, -, aT, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have home : ∀ {o : U64}, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → ¬ GateField o.val →
        ¬ TimerField o.val → ¬ GField o.val →
        SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add (L.curW s) o) := fun h1 h2 h3 h4 h5 h6 =>
      sv_tcbHomeE hK hX hc h1 h2 h3 h4 h5 h6 hcA
    have gate : ∀ {o : U64}, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → GateField o.val →
        SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add (L.curW s) o) := fun h1 h2 h3 h4 =>
      sv_tcbGateE hK hX hc h1 h2 h3 h4
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
      ⟨(I.rt hS).1, nv_objE hK rt1⟩,
      sv_lockE hK a1' r1 (N.lrp hS), sv_lockE hK a2 r2 (E.hlk hS)⟩
    · rw [stA_eq]
      exact home (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField]) (by simp [GField])
    · rw [eS]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (sv_scAccE hK hX hz hco).rd _ am hin
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
      exact ⟨sv_ntfnE hK hX hn hb hc hcA (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE])
          (by simp [layout.ntfn.TAIL_STATE]),
        sv_ntfnE hK hX hn hb hc hcA (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])⟩
  · -- the replied thread, homed here
    have ht := N.hthr lv
    refine ⟨?_, sv_tcbHomeE hK hX ht (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh,
      sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]), afV lv,
      fun _ => ⟨sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]),
        sv_tcbHomeE hK hX ht (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
          (by simp [TimerField]) (by simp [GField]) hh,
        sv_tcbGateE hK hX ht (by simp) (by simp) (by simp) (by simp [GateField]), fun usc eu hne => ?_⟩⟩
    · rw [stA_eq]
      exact sv_tcbHomeE hK hX ht (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField]) hh
    · have eU : L.mem X (scA (slThr st found.1 s)) = L.mem s (scA (slThr st found.1 s)) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      have e1 : usc = L.mem s (scA (slThr st found.1 s)) := by
        rw [tcb_sc_ok] at eu; rw [← ok_inj_ff eu, eU]
      subst e1
      exact rdHead_hereVE ar hA hK hX E Hh LP (Hh.usc hS lv hh hne)

end



section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ex : U64 → Prop} {K : KLayoutV} {Locks : S → U64 → Prop}

theorem cutLE {s : S} {W : U64 → Prop} {x : U64} (h : SlRS (st := st) K.toKLayout Locks s x ∧ W x)
    (hv : ¬ Ex x) : SlRVE (st := st) Ex K Locks s x ∧ W x :=
  ⟨⟨h.1, hv⟩, h.2⟩

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- `slAccC_of` for the cut read set. -/
theorem slAccCVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoE (L := L) Ex s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlAccC (L := L) Z (SlRVE (st := st) Ex K Locks s) (SlWN (st := st) K.toKLayout Locks s) X := by
  have C := slComVE ar hA hK hX hks hf E Hh LP
  obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have hTN' := hTN
  unfold TabNoE at hTN'
  rw [Hh.ksb] at hTN'
  refine ⟨fun o h1 h2 => by
      rw [nX]
      exact ⟨sv_nodeE hK hX E.hN Hh.ksb Hh.cpu h1 h2, (rs_node hX E.hN Hh.ksb Hh.cpu h1 h2).2,
        nonDec_node hK.base hX E.hN Hh.ksb Hh.cpu h1 h2⟩, C.dt, C.cd, ?_, ?_, C.tm, ?_⟩
  · show SlRVE (st := st) Ex K Locks s (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
    rw [kX]
    exact sv_ksE hX hks hf E.hN Hh.ksb (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
  · intro hi hhi
    rw [kX, Hh.ksb]
    obtain ⟨r0, a0⟩ := hX.asidT hi hhi
    have e0 : L.mem X (atAF K.ksb hi) = L.mem s (atAF K.ksb hi) :=
      lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
        (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
    refine ⟨⟨slRS_of_gate a0 (by simp only [own, r0]), (hTN' hi hhi).1⟩, fun lo hlo hne => ?_⟩
    rw [e0] at hne ⊢
    obtain ⟨a1', r1⟩ := Ai.pool hi hhi hne lo hlo
    exact ⟨slRS_of_gate a1' (by simp only [own, r1]), (hTN' hi hhi).2 lo hlo hne⟩
  · intro h
    obtain ⟨h1, h3⟩ := C.rh h
    refine ⟨h1, ?_, h3⟩
    rw [eRh] at h ⊢
    obtain ⟨ht, hs⟩ := Hh.rh h
    have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu ht (by simp) (by simp) (by simp) (by simp))
    rw [eS]
    obtain ⟨hz, -, -, hco⟩ := hs
    exact (sv_scAccE hK hX hz hco).rd

set_option maxHeartbeats 4000000 in
/-- **`fltAcc_wn` for the cut read set.** -/
theorem fltAccVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoE (L := L) Ex s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) Z (SlRVE (st := st) Ex K Locks s) (SlWN (st := st) K.toKLayout Locks s) X (L.curW s) ptr dest r := by
  have hKb := hK.base
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s := slThrIn_of hKb hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccCVE ar hA hK hX hks hf E Hh Ai hTN LP
  obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hep, hlk⟩ := trap_ep ar hA E N I hS LP hc
  obtain ⟨hdt, hds, -, -⟩ := E.hSd hS a X a1 LP hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, hco⟩ := Ai.dsc hS a X a1 LP hc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hdt (by simp) (by simp) (by simp) (by simp))
  obtain ⟨r1, a1h⟩ := hX.epW _ hep layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  obtain ⟨r2, a2h⟩ := hX.epW _ hep layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])
  obtain ⟨hrp, hlr⟩ := Ai.frp hS a X a1 LP hc
  obtain ⟨r3, a3h⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  exact
  { nd := C.nd
    dt := C.dt
    cd := C.cd
    kr := C.kr
    tab := C.tab
    fh := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact sv_tslotE hK hX hc0 (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    eph := cutLE (slRWN_of_lock hKb a1h r1 hlk) (nv_objE hK r1)
    ept := cutLE (slRWN_of_lock hKb a2h r2 hlk) (nv_objE hK r2)
    tf := fun o ho => cutLE (rwn_tcb hKb hX hc0 (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
      (by simp only [TimerField]; omega) hs0 (by omega)) (nv_tcbE hK hX hc0 (by omega) (by omega) (by omega))
    treg := fun _ hr => sv_regsE hK hX hc0 hs0 hr
    trp := (rwn_tcb hKb hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    drp := sv_tcbSafeE hK hX hdt (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    daf := sv_tcbGateE hK hX hdt (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    ddo := sv_tcbGateE hK hX hdt (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dsc0 := sv_tcbGateE hK hX hdt (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    diq := sv_tcbSafeE hK hX hdt (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    dpr := sv_tcbGateE hK hX hdt (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dyt := sv_tcbSafeE hK hX hdt (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    dst := by
      rw [stA_eq]
      exact sv_tcbSafeE hK hX hdt (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds
    dfi := sv_regsE hK hX hdt hds (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    den := sv_tcbSafeE hK hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds
    dib := sv_tcbGateE hK hX hdt (o := 3512#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dvt := by
      rw [vtA_slot]
      exact sv_tslotE hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact sv_tslotE hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨(rwn_tcb hKb hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hKb hX hdt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hKb hX hdt (o := 3480#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2,
      (rwn_tcb hKb hX hdt (o := 3488#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds (by simp)).2⟩
    dreg := fun _ hr => (regs_wn hKb hX hdt hds hr).2
    nxt := fun hne => by
      obtain ⟨hnt, hq, hb⟩ := Ai.nq hS a X a1 LP hc hne
      have eSt : L.mem X (stA (L.mem X (nextA .Ep dest))) = L.mem s (stA (L.mem X (nextA .Ep dest))) := by
        rw [stA_eq]
        exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hnt 3328#u64 (by simp) (by simp) (by simp)).2.2
          (nT hnt (by simp) (by simp) (by simp) (by simp))
      have eBl : L.mem X (blockA (L.mem X (nextA .Ep dest))) = L.mem s (blockA (L.mem X (nextA .Ep dest))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hnt 3336#u64 (by simp) (by simp) (by simp)).2.2
          (nT hnt (by simp) (by simp) (by simp) (by simp))
      rw [eSt] at hq
      rw [eBl] at hb
      exact ⟨(rw_tcb_q hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GField]) hq
        (by rw [hb]; exact hlk)).2, nonDec_tcb hKb hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp)⟩
    buf := fun rb hrb hne i hi => ⟨(slRW_of_user (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)).2,
      nonDec_user hKb hX (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)⟩
    rt := (slRWN_of_lock hKb a3h r3 hlr).2
    spo := by
      rw [eSc]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (sv_scAccE hK hX hz hco).rd _ am hin
    dsc := by
      rw [eSc]
      exact sv_scAccWNE hK hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact sv_scAccWNE hK hX hz' hco'
    tm := C.tm
    rh := C.rh }

set_option maxHeartbeats 4000000 in
/-- **`rrAcc_wn` for the cut read set.** -/
theorem rrAccVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hH : HeapOK K.heap) (hV : True) (hUo : UserNoE Ex K) {s : S}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoE (L := L) Ex s) (hS : ¬ SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAcc (L := L) Z (SlRVE (st := st) Ex K Locks s) (SlWN (st := st) K.toKLayout Locks s) X (L.curW s) found.1 found.2
      u usc := by
  have hKb := hK.base
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s := slThrIn_of hKb hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccCVE ar hA hK hX hks hf E Hh Ai hTN LP
  have D := (slDecInVE ar hA hK hX hks hf E N Hh).rT hS a X a1 LP
  obtain ⟨-, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hut, hus, -, -, -⟩ := E.hSu hS a X a1 LP u usc hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have eu : u = slThr st found.1 s := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    exact h1
  have lv : SlLive st found.1 s := slLive_rr (st := st) hS (by rw [← eu]; exact u_ne0 hc.u0)
  have haf : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by rw [← eu, affA_fld]; exact hus.1
  have eusc : usc = L.mem s (scA u) := by
    have h1 := hc.sc
    rw [tcb_sc_ok] at h1
    rw [← ok_inj_ff h1]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hut 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hut (by simp) (by simp) (by simp) (by simp))
  have husc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hn⟩ := hc.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec usc)] at hb
    rw [← ok_inj_ff hb] at hn
    simpa using hn
  have Hs := Hh.usc hS lv haf (by rw [← eu, ← eusc]; exact husc0)
  rw [← eu, ← eusc] at Hs
  obtain ⟨hz, hin0, hmx0, hco⟩ := Hs
  have hrp := N.hrp hS
  have hlr := N.lrp hS
  obtain ⟨rt1, rta⟩ := hX.rpW _ hrp layout.reply.TCB (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])
  obtain ⟨rn1, rna⟩ := hX.rpW _ hrp layout.reply.NEXT (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])
  obtain ⟨rp1, rpa⟩ := hX.rpW _ hrp layout.reply.PREV (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])
  obtain ⟨eh1, eha⟩ := hX.epW _ (Hh.ep hS) layout.ep.HEAD (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])
  obtain ⟨et1, eta⟩ := hX.epW _ (Hh.ep hS) layout.ep.TAIL_STATE (by simp [layout.ep.TAIL_STATE])
    (by simp [layout.ep.TAIL_STATE])
  obtain ⟨-, aC, hinC, rC⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have eC : L.mem X (core.num.U64.wrapping_add usc layout.sc.CORE) = L.cpu X := by
    rw [lp_mem ar hA E.hT E.hN E.hcT LP aC (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rC]; intro c h; cases h) (by rw [rC]; intro h; cases h)), cX]
    have e : core.num.U64.wrapping_add usc layout.sc.CORE = fld usc 16#u64 := by simp [fld, layout.sc.CORE]
    rw [e]
    exact hco
  exact
  { nd := C.nd
    dt := C.dt
    cd := C.cd
    kr := C.kr
    tab := C.tab
    tSt := D.tSt
    tSc := D.tSc
    tMx := D.tMx
    tIq := D.tIq
    tMi := D.tMi
    tBn := D.tBn
    tPr := D.tPr
    tReg := fun _ hr => sv_regsE hK hX hc0 hs0 hr
    tBuf := ⟨_, tcb_slot_val _ _, sv_tcbGateE hK hX hc0 (o := 3512#u64) (by simp) (by simp) (by simp)
      (by simp [GateField]), (sv_tslotE hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1,
      (sv_tslotE hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    tBw := fun buf hb hne i hi => sv_userE hH hV hUo (Ai.rbuf hS a X a1 LP buf hb hne i hi)
    ntf := D.ntf
    wRp := (rwn_tcb hKb hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    wEn := (rwn_tcb hKb hX hc0 (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    wEp := (rwn_tcb hKb hX hc0 (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0 (by simp)).2
    rRt := D.rRt
    rNx := D.rNx
    rPv := sv_lockE hK rpa rp1 hlr
    wNx := (slRWN_of_lock hKb rna rn1 hlr).2
    wPv := (slRWN_of_lock hKb rpa rp1 hlr).2
    wRt := (slRWN_of_lock hKb rta rt1 hlr).2
    uSt := by
      rw [stA_eq]
      exact sv_tcbSafeE hK hX hut (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hus
    uFt := cutLE (rwn_tcb hKb hX hut (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus (by simp)) (nv_tcbE hK hX hut (o := 3376#u64) (by simp) (by simp) (by simp))
    uSc := sv_tcbGateE hK hX hut (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uPr := sv_tcbGateE hK hX hut (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uAf := sv_tcbGateE hK hX hut (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uDo := sv_tcbGateE hK hX hut (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uIq := sv_tcbSafeE hK hX hut (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus
    uMx := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (sv_scAccE hK hX hz hco).rd _ am hin
    uReg := fun _ hr => (regs_wn hKb hX hut hus hr).2
    uYt := sv_tcbSafeE hK hX hut (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus
    uFi := sv_regsE hK hX hut hus (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    uVt := by
      rw [vtA_slot]
      exact sv_tslotE hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := D.eTS
    wEh := (slRWN_of_lock hKb eha eh1 (E.hlk hS)).2
    wEt := (slRWN_of_lock hKb eta et1 (E.hlk hS)).2
    spo := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (sv_scAccE hK hX hz hco).rd _ am hin
    cor := (sv_scAccE hK hX hz hco).rd _ aC hinC
    ccs := by
      rw [eC]
      exact (C.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    uHd := rdHead_hereVE ar hA hK hX E Hh LP ⟨hz, hin0, hmx0, hco⟩
    uscA := sv_scAccWNE hK hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact sv_scAccWNE hK hX hz' hco'
    tm := C.tm
    rh := C.rh }

/-- **`AvoidV.acc` for syscall_local**: an accepted run is the same run on `guard st (SlRVE K Locks s) (SlWS s)`
(p2sl's `sl_acc` with the cut bundles). -/
theorem sl_accVE (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hks : KsNoE Ex K)
    (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hH : HeapOK K.heap) (hV : True) (hUo : UserNoE Ex K) {s s1 : S}
    {a a1 : A}
    (E : SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K.toKLayout Locks found s) (Hh : SlHere (st := st) K.toKLayout Z Scs found s)
    (Ai : SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s) (hTN : TabNoE (L := L) Ex s)
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) :
    syscall.handle_syscall_local (guard st (SlRVE (st := st) Ex K Locks s) (SlWS (st := st) K.toKLayout Locks s))
      ar s a n found = ok (true, s1, a1) := by
  exact syscall.handle_syscall_local.guard_acc
    (gS := guard st (SlRVE (st := st) Ex K Locks s) (SlWS (st := st) K.toKLayout Locks s))
    (R := SlRVE (st := st) Ex K Locks s) (W := SlWS (st := st) K.toKLayout Locks s) ar hA E.hT E.hN E.hcT
    (preAccVE ar hK hX E Hh) (fun X a1 csc LP hcs => hhdVE ar hA hK hX E Hh LP hcs) (E.hI a) (E.hAs a)
    (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
    (fun h' X a1 LP {_p _b _d _r} hc => (fltAccVE ar hA hK hX hks hf E N Hh Ai hTN h' LP hc).wmono (fun _ h => h.1))
    (fun h' X a1 hP {_p _b _d _r} hc =>
      ⟨SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) (E.hSd h' a X a1 hP hc).2.2.1,
        fun _ _ => SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) (E.hSd h' a X a1 hP hc).2.2.2⟩)
    (fun h' => E.hPl h' a) (fun h' => E.hrz h' a) (fun h' => E.hy0r h' a)
    (fun h' X a1 LP u usc hc => (rrAccVE ar hA hK hX hks hf hH hV hUo E N Hh Ai hTN h' LP hc).wmono (fun _ h => h.1))
    (fun h' X a1 hP u usc hc =>
      have hw := E.hSu h' a X a1 hP u usc hc
      { tR := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.1
        tN := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.1
        tB := fun _ _ => gst_write (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.1
        bl := fun _ => gst_write (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.1
        uI := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.2
        uR := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.2
        uN := SWr.of_W (W := SlWS (st := st) K.toKLayout Locks s) hw.2.2.2.2 })
    h

end



section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ex : U64 → Prop} {K : KLayoutV} {Locks : S → U64 → Prop}

/-- The words `slTW t` of a heap TCB are no VCPU data words. -/
theorem nv_twE (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) {t b : U64} (ht : K.heap t = some .tcb)
    (hb : slTW t b) : ¬ Ex b := by
  obtain ⟨-, h⟩ := hb
  rcases h with rfl | rfl | rfl | rfl
  · exact nv_tcbE hK hX ht (o := 3360#u64) (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact nv_tcbE hK hX ht (o := 3328#u64) (by simp) (by simp) (by simp)
  · exact nv_tcbE hK hX ht (o := 3376#u64) (by simp) (by simp) (by simp)
  · exact nv_tcbE hK hX ht (o := 3464#u64) (by simp) (by simp) (by simp)

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxHeartbeats 4000000 in
/-- `sl_home` for the cut read set. -/
theorem sl_homeVE (hA : P0.ArchTotal ar) {s : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hpre : PreAcc (L := L) (SlRVE (st := st) Ex K Locks s) (SlWS (st := st) K.toKLayout Locks s) s)
    (hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SlRVE (st := st) Ex K Locks s) X csc)
    (I : SlThrIn (st := st) K.toKLayout Locks found.1 s)
    (D : SlDecInR (st := st) ar (SlRVE (st := st) Ex K Locks s) found s)
    (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true)
    (hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s) :
    syscall.handle_syscall_local (guard st (SlRVE (st := st) Ex K Locks s) (SlDS (L := L) s)) ar s a n found = ok r := by
  have hp : PreDec (L := L) (SlRVE (st := st) Ex K Locks s) (SlDS (L := L) s) s :=
    ⟨fun o h1 h2 => (hpre.nd o h1 h2).1, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hpre.fl, hpre.nx,
      Or.inl rfl⟩
  refine syscall.handle_syscall_local.guard_dec (gS := guard st (SlRVE (st := st) Ex K Locks s) (SlDS (L := L) s))
    hA E.hT E.hN E.hcT hp (fun X a1 csc LP e => hhd a X a1 csc LP e) ?_ ?_ h
  · intro hS X a1 n' LP hf
    refine fastpath.fault.guard_dec (gS := guard st (SlRVE (st := st) Ex K Locks s) (SlDS (L := L) s))
      (FltDec.of (D.fT hS a X a1 LP) ?_) hf hn
    intro ptr bb x y g gr hc hst d hd
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X ptr), e1] at hd
    rw [← ok_inj_ff hd]
    exact D.fD hS (slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc hst) hh a X a1 LP
  · intro hS X a1 LP hf
    refine fastpath.reply_recv_found.guard_dec (gS := guard st (SlRVE (st := st) Ex K Locks s) (SlDS (L := L) s))
      (RrDec.of (D.rT hS a X a1 LP) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hu, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    rw [h1]
    exact D.rU hS lv hh a X a1 LP

set_option maxHeartbeats 8000000 in
/-- `sl_away` for the cut read set (the decided thread's `slTW` words only once it is live). -/
theorem sl_awayVE (hA : P0.ArchTotal ar) {s s' : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hpre : PreAcc (L := L) (SlRVE (st := st) Ex K Locks s) (SlWS (st := st) K.toKLayout Locks s) s)
    (hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SlRVE (st := st) Ex K Locks s) X csc)
    (I : SlThrIn (st := st) K.toKLayout Locks found.1 s)
    (D : SlDecInR (st := st) ar (SlRVE (st := st) Ex K Locks s) found s)
    (hafV : SlLive st found.1 s → ¬ Ex (affA (slThr st found.1 s)))
    (Al : Alt st (SlRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0)
      (· ∈ K.user) s s')
    (hh : L.mem s (affA (slThr st found.1 s)) ≠ L.cpu s)
    (h : syscall.handle_syscall_local st ar s' a n found = ok r) :
    syscall.handle_syscall_local
      (guard st (fun b => SlRVE (st := st) Ex K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
        (fun _ => True))
      ar s' a n found = ok r := by
  have hn : r.1 ≠ true := fun e => hh (slThr_acc ar hA E I Al h e)
  have hcur := sl_alt_cur E.preG Al
  have hTr := slTrap_alt E.preG.fl Al hcur
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ T := by rw [hcur]; exact E.hcT
  have hp : PreDec (L := L)
      (fun b => SlRVE (st := st) Ex K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
      (fun _ => True) s' :=
    ⟨fun o h1 h2 => Or.inl (by rw [slDS_node Al.ksb Al.cpu]; exact (hpre.nd o h1 h2).1), trivial, trivial,
      Or.inl (by rw [hcur]; exact hpre.fl), Or.inl (by rw [hcur]; exact hpre.nx), trivial⟩
  have hct : SlRS (st := st) K.toKLayout Locks s (ctA (L := L) s) :=
    (E.preG.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have hcn : SlRS (st := st) K.toKLayout Locks s (cnA (L := L) s) :=
    (E.preG.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  have PA : ∀ X' a1', LocalPre (st := st) ar s' a (X', a1') → ∃ X, LocalPre (st := st) ar s a (X, a1') ∧
      (∀ b, SlRS (st := st) K.toKLayout Locks s b → L.mem X' b = L.mem X b) ∧ L.ksb X' = L.ksb X ∧
        L.cpu X' = L.cpu X := by
    intro X' a1' LP'
    obtain ⟨X, LP, hag⟩ := lp_alt ar hA (fun b hb => hb.1) E.hT E.hN E.hcT Al.ksb Al.cpu hcur Al.read
      E.preG.nx hct hcn LP'
    obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    obtain ⟨hkX', hcX', -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP'
    exact ⟨X, LP, hag, by rw [hkX', hkX, Al.ksb], by rw [hcX', hcX, Al.cpu]⟩
  have hrest : SlLive st found.1 s → ∀ X X' a1', LocalPre (st := st) ar s a (X, a1') →
      (∀ b, SlRS (st := st) K.toKLayout Locks s b → L.mem X' b = L.mem X b) → L.cpu X' = L.cpu X →
      L.mem X' (affA (slThr st found.1 s)) ≠ L.cpu X' := by
    intro lv X X' a1' LP hag hcX e
    have af := I.af lv
    apply hh
    obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hcX, hcX0]
  refine syscall.handle_syscall_local.guard_dec
    (gS := guard st (fun b => SlRVE (st := st) Ex K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
      (fun _ => True))
    hA E.hT hN' hc' hp ?_ ?_ ?_ h
  · intro X' a1' csc LP' ecsc
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have rcs : SlRS (st := st) K.toKLayout Locks s (L.nodeA X layout.node.CUR_SC) := by
      unfold LawfulStore.nodeA; rw [hcX, nodeAt_of_ksb hkX]
      exact (E.preG.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    have en : L.nodeA X' layout.node.CUR_SC = L.nodeA X layout.node.CUR_SC := by
      unfold LawfulStore.nodeA; exact slDS_node hk hc
    have ecsc' : sched.cur_sc st X = ok csc := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X')] at ecsc
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X), ← hag _ rcs, ← en]
      exact ecsc
    exact RdHead.mono (fun b hb => Or.inl hb) (RdHead.congr (fun b hb => hag b hb.1) (hhd a X a1' csc LP ecsc'))
  · intro hS' X' a1' n' LP' hf
    have hS := hTr.1 hS'
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    have DT := FltDecT.congr hk hc (fun b hb => hag b hb.1) (D.fT hS a X a1' LP)
    rw [hcur] at hf ⊢
    refine fastpath.fault.guard_dec
      (gS := guard st (fun b => SlRVE (st := st) Ex K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
        (fun _ => True))
      (FltDec.of (FltDecT.mono (fun b hb => Or.inl hb) DT) ?_) hf hn
    intro ptr bb x y g gr hcp hst' d hd
    have hc0 : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr bb x y g gr) :=
      (cap_congr (hag _ DT.fh.1.1) (hag _ DT.fh.2.1)).symm.trans hcp
    have hst : obj.Ep.state st ptr X = ok obj.EP_RECV :=
      (ep_state_congr (hag _ (DT.ep ptr bb x y g gr hcp).1.1)).symm.trans hst'
    have lv := slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc0 hst
    have af := I.af lv
    have aA : Aligned (affA (slThr st found.1 s)) := af.1.1
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc0
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X' ptr), hag _ (DT.ep ptr bb x y g gr hcp).2.1, e1] at hd
    rw [← ok_inj_ff hd]
    exact ⟨Or.inr ⟨lv, by unfold replyA; exact tw_al aA (by simp), Or.inl rfl⟩, Or.inl ⟨af.1, hafV lv⟩,
      fun e => absurd e (hrest lv X X' a1' LP hag hc)⟩
  · intro hS' X' a1' LP' hf
    have hS : ¬ SlTrap st s := fun h' => hS' (hTr.2 h')
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    have DT := RrDecT.congr hk hc (fun b hb => hag b hb.1) (D.rT hS a X a1' LP)
    rw [hcur] at hf ⊢
    refine fastpath.reply_recv_found.guard_dec
      (gS := guard st (fun b => SlRVE (st := st) Ex K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
        (fun _ => True))
      (RrDec.of (RrDecT.mono (fun b hb => Or.inl hb) DT) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X' found.1
    rw [hu, WP.spec_ok, hag _ DT.rRt.1, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    have af := I.af lv
    have aA : Aligned (affA (slThr st found.1 s)) := af.1.1
    rw [h1]
    exact ⟨Or.inr ⟨lv, by rw [stA_eq]; exact tw_al aA (by simp), Or.inr (Or.inl rfl)⟩,
      Or.inr ⟨lv, tw_al aA (by simp), Or.inr (Or.inr (Or.inl rfl))⟩,
      Or.inr ⟨lv, by unfold scA; exact tw_al aA (by simp), Or.inr (Or.inr (Or.inr rfl))⟩,
      Or.inl ⟨af.1, hafV lv⟩, fun e => absurd e (hrest lv X X' a1' LP hag hc)⟩

end

/-! ## `AvoidV` for syscall_local -/

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ex : U64 → Prop} {K : KLayoutV} {Locks : S → U64 → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

/-- The entry facts p2sl derives at a `P` state (`slEnt_of`, `slHere_of`, `slAccIn_of`). -/
def SlEntAllE (ar : machine.Arch A) (K : KLayoutV) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64)
    (found : U64 × U64) (T Cs Ω U Sg Rp Scs Nt Ac : Set U64) (H : Heap) (Z : U64 → Nat) (s : S) : Prop :=
  SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s ∧
    SlEnt (st := st) K.toKLayout Locks found s ∧ SlHere (st := st) K.toKLayout Z Scs found s ∧
    SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s

/-- **`AvoidV.acc` for syscall_local.** -/
theorem sl_avAccE (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K) {P : S → Prop}
    (hX : ∀ s, P s → RegionOKX K.toKLayout)
    (hent : ∀ s, P s → SlEntAllE (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hks : ∀ s, P s → KsNoE Ex K) (hf : ∀ s, P s → K.ksb.val + 13568 ≤ 2 ^ 64)
    (hTN : ∀ s, P s → TabNoE (L := L) Ex s)
    (hH : ∀ s, P s → HeapOK K.heap) (hV : True) (hUo : UserNoE Ex K) :
    Fl4Proofs.P2.E2EP.AvAccE Ex st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true) P
      (SlRS (st := st) K.toKLayout Locks) (SlWS (st := st) K.toKLayout Locks) := by
  rintro s a ⟨b, s1, a1⟩ hP h hb
  beta_reduce at h ⊢
  obtain ⟨E0, N, Hh, Ai⟩ := hent s hP
  have hb' : b = true := hb
  subst hb'
  exact sl_accVE ar hA hK (hX s hP) (hks s hP) (hf s hP) (hH s hP) hV hUo E0 N Hh Ai (hTN s hP) h

/-- **`AvoidV.dec` for syscall_local.** -/
theorem sl_avDecE (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKE Ex K)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) {p : SProg Bool} (hFp : IsProg (slBody S n found) p) (hz : NoZero p)
    {P : S → Prop} (hX' : ∀ s, P s → RegionOKX K.toKLayout)
    (hent : ∀ s, P s → SlEntAllE (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hks' : ∀ s, P s → KsNoE Ex K) (hf' : ∀ s, P s → K.ksb.val + 13568 ≤ 2 ^ 64) :
    Fl4Proofs.P2.E2EP.AvDecE Ex st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P (SlRS (st := st) K.toKLayout Locks) := by
  have hKb := hK.base
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar p x a :=
    fun mm x a => congrFun (congrFun (hFp A ar mm) x) a
  intro s a r hP h hn s' r' Al h'
  beta_reduce at h h' ⊢
  obtain ⟨E0, N, Hh, Ai⟩ := hent s hP
  have hX := hX' s hP
  have hks := hks' s hP
  have hf := hf' s hP
  have E := slPre_of ar hA hKb hX E0 N Hh Ai
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s := slThrIn_of hKb hX E.preG E0.hSt.1 N
  have D := slDecInVE ar hA hK hX hks hf E0 N Hh
  have hpre := preAccVE ar hK hX E0 Hh
  have hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SlRVE (st := st) Ex K Locks s) X csc := fun a X a1 csc LP e => hhdVE ar hA hK hX E0 Hh LP e
  have hn' : r.1 ≠ true := hn
  by_cases hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s
  · obtain ⟨b, s1, a1⟩ := r
    have hg := sl_homeVE ar hA E hpre hhd I D h hn' hh
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1.1) (fun w hw => (SlDS.ws E.preG hw).1) _ hz s s' a b
      s1 a1 Al.ksb Al.cpu Al.masks (fun w hw => Al.read w hw.1) hg
    have h2 := interp_to (st := st) (st' := st) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      rfl rfl rfl _ hz s' a _ hg'
    rw [eP] at h' ⊢
    rw [h2] at h'
    rw [← h']
    exact interp_mono (fun _ hq => hq.2) (fun _ _ => trivial) _ hz s' a _ hg'
  · have hg := sl_awayVE ar hA E hpre hhd I D
      (fun lv => nv_tcbE hK hX (N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)) Al hh h'
    rw [eP] at hg ⊢
    exact interp_mono (fun q hq => hq.elim (fun h1 => h1.2) (fun h2 => nv_twE hK hX (N.hthr h2.1) h2.2))
      (fun _ _ => trivial) _ hz s' a _ hg

/-- **`AvoidV` for syscall_local** (module docstring). -/
theorem sl_avoidVE (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hK : RegionOKE Ex K) (hX : RegionOKX K.toKLayout) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hSe : SlSets K.toKLayout T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop}
    (hPE : ∀ s, P s → SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hEj : ∀ s, P s → SlEntJ (st := st) K.toKLayout Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K.toKLayout Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K.toKLayout Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hks : KsNoE Ex K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hTN : ∀ s, P s → TabNoE (L := L) Ex s)
    (hH : HeapOK K.heap) (hV : True) (hUo : UserNoE Ex K) :
    Fl4Proofs.P2.E2EP.AvoidE Ex (sl_localPath ar hSt hA hK.base hX hU hm hSe hUu a0 hPE hEj hHj hAk huf hpz) := by
  have hKb := hK.base
  have hent : ∀ s, P s → SlEntAllE (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s := by
    intro s hP
    have E0 := hPE s hP
    have N := slEnt_of ar hSt hA hX hSe a0 E0 (hEj s hP)
    have Hh := slHere_of ar hSt hA hX hSe a0 E0 N (hHj s hP)
    exact ⟨E0, N, Hh, slAccIn_of ar hA hKb hX hSe E0 N Hh (slAccJ_of ar hA hKb hX hUu E0 (hHj s hP) (hAk s hP))⟩
  letI : LawfulStore (sl_localPath ar hSt hA hK.base hX hU hm hSe hUu a0 hPE hEj hHj hAk huf hpz).st := L
  exact ⟨sl_avAccE ar hA hK (fun _ _ => hX) hent (fun _ _ => hks) (fun _ _ => hf) hTN (fun _ _ => hH) hV hUo,
    sl_avDecE ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 (fun _ _ => hX) hent (fun _ _ => hks) (fun _ _ => hf),
    IsProg.on hpz.choose_spec.1 _ _ _⟩

/-- The kernel-state block's fit and `HeapOK` at a P3-related entry (`SlJAt`). -/
theorem slJAt_fitE {s : S} (h : SlJAt (L := L) K.toKLayout s) : K.ksb.val + 13568 ≤ 2 ^ 64 ∧ HeapOK K.heap := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hk : K.ksb = L.ksb s := B.ksb.symm
  have hf := B.j.kern.ksbFit
  rw [← hk] at hf
  exact ⟨hf, B.layP.heap⟩

/-- **`AvoidV` for syscall_local in the form the path families use** (`sl_localPathK`, `P2/SlJLay.lean`: P3's
bundle `SlJAt K s` at its start states): `sl_avoidVE`'s VCPU premises from `SlJAt` (`slJAt_vfactsE`), leaving
`RegionOKV` [J], `VcpuHeap` [J], `VcpuTabOff` [J], `PoolObj` [J] (per state) and `UserObj` [J]. -/
theorem sl_avoidVKE (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKE Ex K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlJAt (L := L) K.toKLayout s)
    (hPE : ∀ s, P s → SlPreB (st := st) ar K.toKLayout Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ s, P s → SlEntR (st := st) K.toKLayout Locks found s)
    (hHr : ∀ s, P s → SlHereR (st := st) K.toKLayout found s)
    (hAr : ∀ s, P s → SlAccR (st := st) ar K.toKLayout Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hks : ∀ s, P s → KsNoE Ex K) (hTN : ∀ s, P s → TabNoE (L := L) Ex s) (hUo : UserNoE Ex K) :
    Fl4Proofs.P2.E2EP.AvoidE Ex (sl_localPathK ar hSt hA hm a0 hK.base hU hJ hPE hEr hHr hAr huf hpz) := by
  have hKb := hK.base
  have hX : ∀ s, P s → RegionOKX K.toKLayout := fun s hP => (hJ s hP).regionOKX
  have VF : ∀ s, P s → KsNoE Ex K ∧ K.ksb.val + 13568 ≤ 2 ^ 64 ∧ HeapOK K.heap ∧ TabNoE (L := L) Ex s :=
    fun s hP => ⟨hks s hP, (slJAt_fitE (hJ s hP)).1, (slJAt_fitE (hJ s hP)).2, hTN s hP⟩
  have hent : ∀ s, P s → SlEntAllE (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s := by
    intro s hP
    have E0 := hPE s hP
    have hSe := slSets_conv K.toKLayout
    have N := slEnt_of ar hSt hA (hX s hP) hSe a0 E0 ((hJ s hP).entJ E0.hN (hEr s hP))
    have Hh := slHere_of ar hSt hA (hX s hP) hSe a0 E0 N ((hJ s hP).hereJ (hHr s hP))
    exact ⟨E0, N, Hh, slAccIn_of ar hA hKb (hX s hP) hSe E0 N Hh
      (slAccJ_of ar hA hKb (hX s hP) (fun _ h => h) E0 ((hJ s hP).hereJ (hHr s hP)) ((hJ s hP).accK (hAr s hP)))⟩
  letI : LawfulStore (sl_localPathK ar hSt hA hm a0 hK.base hU hJ hPE hEr hHr hAr huf hpz).st := L
  exact ⟨sl_avAccE ar hA hK hX hent (fun s hP => (VF s hP).1) (fun s hP => (VF s hP).2.1)
      (fun s hP => (VF s hP).2.2.2) (fun s hP => (VF s hP).2.2.1) trivial hUo,
    sl_avDecE ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 hX hent (fun s hP => (VF s hP).1)
      (fun s hP => (VF s hP).2.1),
    IsProg.on hpz.choose_spec.1 _ _ _⟩

end av


/-! ## The VCPU instance (sanity check) -/

section vinst
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Locks : S → U64 → Prop}
variable {A : Type} {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

theorem slJAt_vcpuKs {s : S} (h : SlJAt (L := L) K.toKLayout s) (hV : VcpuHeap K) : VcpuKs K := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact vcpuKs_of_jkern B.j.kern rfl B.ksb.symm hV

theorem slJAt_tabNoV {s : S} (h : SlJAt (L := L) K.toKLayout s) (hV : VcpuHeap K) (hT : VcpuTabOff K)
    (hPo : PoolObj (L := L) K s) : TabNoV (L := L) K s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  exact tabNoV_of B.layP.heap hV hT hPo B.ksb.symm

theorem regionOKE_vcpu (hK : RegionOKV K) : RegionOKE (VData K) K := ⟨hK.base, fun _ h => notVData_of_region' hK h⟩

/-- **`sl_avoidVK` recovered from the generic copy** (`Ex := VData K`). -/
theorem sl_avoidVK' (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKV K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlJAt (L := L) K.toKLayout s)
    (hPE : ∀ s, P s → SlPreB (st := st) ar K.toKLayout Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ s, P s → SlEntR (st := st) K.toKLayout Locks found s)
    (hHr : ∀ s, P s → SlHereR (st := st) K.toKLayout found s)
    (hAr : ∀ s, P s → SlAccR (st := st) ar K.toKLayout Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hV : VcpuHeap K) (hT : VcpuTabOff K) (hPo : ∀ s, P s → PoolObj (L := L) K s) (hUo : UserObj K) :
    AvoidV K (sl_localPathK ar hSt hA hm a0 hK.base hU hJ hPE hEr hHr hAr huf hpz) := by
  have h := sl_avoidVKE (Ex := VData K) ar hSt hA hm a0 (regionOKE_vcpu hK) hU hJ hPE hEr hHr hAr huf hpz
    (fun s hP => fun o ho => notVData_of_noVcpu (noVcpu_ks (slJAt_vcpuKs (hJ s hP) hV) (slJAt_fitE (hJ s hP)).1 ho))
    (fun s hP => slJAt_tabNoV (hJ s hP) hV hT (hPo s hP))
    (fun b hb => notVData_of_noVcpu (hUo b hb))
  exact ⟨h.acc, h.dec, h.prog⟩

end vinst

end
end Fl4Proofs.P2.E2EV
