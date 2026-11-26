/-
# P2 (line slhuf, gen 5): `hufR` of the VM ReplyRecv local path discharged

`rr_localPathJ` (P2/SlJVm.lean) took `hufR` [J]: at a `VmRRPreJ` state a write of a user word
keeps the `VmRPre` part, `RdTab`, the locks and the read / write / decline sets `IoRS`, `IoWS`,
`IoDS`. Here it is proved at the canonical sets (`T = Heap.tcbs K.heap`, `Scs`, `Nt`, `Z` the
heap's, as `SlQ` and P3's `JAtZ.entryInv`), for any `Ω`, `Sg`, `Ac` and `Cs` below 64 cores,
from the locks alone (`hlk` [P]):

* `SlJAt.ioRWDS_wr`: `IoRS`, `IoWS`, `IoDS` are kept (`own` reads no user word, `E2E.ownDep`;
  the current thread and core are kept);
* `SlJAt.rdTab_wr`: `RdTab` is kept (the ASID-table words are `NU`, `SlJAt.nuAsid`);
* `SlJAt.vmBase_wr`: `VmBase` is kept (`bxi_userJ`; every other field reads node, TCB or SC
  words, all `NU`);
* `SlJAt.vmRPre_wr`: `VmRPre` is kept. `mid`: a prefix run from the written state is one from
  `s` up to `NU` (`SlJAt.lp_wr`); `BXI` by `bxi_userJ`, `AsidOff` by `asidOff_agN`; the
  ReplyRecv checks moved back by `rr_chk_backG` with the read set `RrDR (NU K)`, obtained from
  P2's `rr_dr` (`RrDR` for `IoRS s`, and `IoRS ⊆ NU`); `RRPl` by `rrPl_ag`; the receiver's
  `YIELD_TO` is a TCB word. `nb`, `nbt`: reply / TCB / bound-notification words;
* **`vm_hufRK`**: `hufR` at the canonical sets, from `hCs` (`Cs` below 64 cores, [P], a fact
  about the set alone) and `hlk` [P];
* **`rr_localPathJK`**: `rr_localPathJ` at the canonical sets with `hufR` discharged.
  Remaining premises: `hCs` [P], `hlk` [P], and `rr_localPathJ`'s others (`hmA`, `hpz` with
  `hro` [W], `hm`, `hLA`, `hK`, `hU`, `hA`).
-/
import Fl4Proofs.P2.SlJUB4
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-- **`IoRS`, `IoWS`, `IoDS` are kept by a user-word write** at a bundle state (locks kept). -/
theorem SlJAt.ioRWDS_wr {s : S} (B : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b)
    (v : U64) (hl : Locks (L.wr s b v) = Locks s) :
    IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
      IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  have eo : own K (L.mem (L.wr s b v)) = own K (L.mem s) :=
    E2E.ownDep B.regionOK B.userOK _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  have ecur := B.curW_wr hb hba v
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, WPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]

/-- **`RdTab` is kept by a user-word write** at a bundle state (the ASID-table words are `NU`). -/
theorem SlJAt.rdTab_wr {s : S} (B : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user) (hba : Aligned b)
    (v : U64) (e : IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s)
    (h : RdTab (L := L) (IoRS (st := st) K Locks s) s) :
    RdTab (L := L) (IoRS (st := st) K Locks (L.wr s b v)) (L.wr s b v) := by
  rw [e]
  intro hi hhi
  have ea : L.mem (L.wr s b v) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
    wr_nu hba hb v (B.nuAsid rfl hhi)
  rw [L.ksb_wr, ea]
  exact h hi hhi

variable {Cs Ω Sg Ac : Set U64}

/-- **`VmBase` is kept by a user-word write** at a bundle state (canonical sets, `Cs` below 64
cores). -/
theorem SlJAt.vmBase_wr {s : S} (B : SlJAt (L := L) K s) (hCs : ∀ c ∈ Cs, c.val < 64)
    (P : VmBase st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    VmBase st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac
      (L.wr s b v) := by
  have hX := B.regionOKX
  have Gw : Ag st (NU K) s (L.wr s b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have ecur := B.curW_wr hb hba v
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem (L.wr s b v) (L.nodeAt (L.wr s b v) (L.cpu (L.wr s b v)) o) = L.mem s (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => by rw [Gw.node]; exact Gw.m _ (B.nuNode P.np ho h8)
  have ecsc : L.cscW (L.wr s b v) = L.cscW s := eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have etm : L.mem (L.wr s b v) (tmA (L := L) (L.wr s b v)) = L.mem s (tmA (L := L) s) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hcH : K.heap (L.curW s) = some .tcb := P.hT _ P.cT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := P.bxi
  refine
  { bxi := bxi_userJ B rfl hCs P.bxi Gw
    csc := by rw [ecsc]; exact P.csc
    hcsc := ?_
    run := ?_
    lay := P.lay
    kb := by rw [L.ksb_wr]; exact P.kb
    nc := by rw [L.cpu_wr]; exact P.nc
    hT := P.hT
    hSc := P.hSc
    curAff := ?_
    cscCore := ?_
    affSc := ?_
    tmc := ?_ }
  · have e : L.mem (L.wr s b v) (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact P.hcsc
  · have e : L.mem (L.wr s b v) (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact P.run
  · have e : L.mem (L.wr s b v) (affA (L.curW s)) = L.mem s (affA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, L.cpu_wr, e]; exact P.curAff
  · have e : L.mem (L.wr s b v) (scCoreA (L.cscW s)) = L.mem s (scCoreA (L.cscW s)) :=
      wr_nu hba hb v (nu_scw hX (P.hSc _ P.cscS) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, L.cpu_wr, e]; exact P.cscCore
  · intro t ht h0
    have es : L.mem (L.wr s b v) (scA t) = L.mem s (scA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h0 ⊢
    have hsc := (hXI.2.2.bound t ht h0).1
    have ec : L.mem (L.wr s b v) (scCoreA (L.mem s (scA t))) = L.mem s (scCoreA (L.mem s (scA t))) :=
      wr_nu hba hb v (nu_scw hX (P.hSc _ hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem (L.wr s b v) (affA t) = L.mem s (affA t) :=
      wr_nu hba hb v (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact P.affSc t ht h0
  · intro h0
    rw [etm] at h0 ⊢
    have hT := (hXI.2.2.tm.min _ hq.cur).resolve_left h0
    have ed : L.mem (L.wr s b v) (tdA (L.mem s (tmA (L := L) s))) = L.mem s (tdA (L.mem s (tmA (L := L) s))) :=
      wr_nu hba hb v (nu_tcb hX hT (o := 3528#u64) (by simp) (by simp) (by simp))
    have eh : L.mem (L.wr s b v) (thA (L.mem s (tmA (L := L) s))) = L.mem s (thA (L.mem s (tmA (L := L) s))) :=
      wr_nu hba hb v (nu_tcb hX hT (o := 3568#u64) (by simp) (by simp) (by simp))
    rw [ed, eh, L.cpu_wr]; exact P.tmc h0

variable {A : Type} {ar : machine.Arch A}

/-- **`VmRPre` is kept by a user-word write** at a bundle state (canonical sets, `Cs` below 64
cores, the locks kept, the reply a heap reply). -/
theorem SlJAt.vmRPre_wr (hA : P0.ArchTotal ar) {s : S} (B : SlJAt (L := L) K s) (hCs : ∀ c ∈ Cs, c.val < 64)
    {rptr ep : U64}
    (Q : VmRPre st ar K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac
      Locks s rptr ep)
    (hrp : K.heap rptr = some .reply) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64)
    (hl : Locks (L.wr s b v) = Locks s) :
    VmRPre st ar K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac
      Locks (L.wr s b v) rptr ep := by
  have P := Q.base
  have hX := B.regionOKX
  have ecur := B.curW_wr hb hba v
  have hcH : K.heap (L.curW s) = some .tcb := P.hT _ P.cT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := P.bxi
  refine
  { base := B.vmBase_wr hCs P hb hba v
    mid := ?_
    lk := by rw [hl]; exact Q.lk
    nb := ?_
    hEp := Q.hEp
    hRp := Q.hRp
    hNt := Q.hNt
    nbt := ?_ }
  · intro a X' a2 LP'
    obtain ⟨X, LP, G⟩ := B.lp_wr ar hA P.tp P.np P.cT hcH hb hba v LP'
    obtain ⟨kX, cX, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA P.tp P.np P.cT LP
    obtain ⟨hI, hAs, hP⟩ := Q.mid a X a2 LP
    have hnd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → NU K (L.nodeAt X (L.cpu X) o) :=
      fun o h1 h2 => by rw [cX, nodeAt_of_ksb kX]; exact B.nuNode P.np h1 h2
    have D : RrDR (L := L) (NU K) X (L.curW s) rptr ep := by
      obtain ⟨t, nx, s1, et, enx, e1, eu⟩ := LP
      rw [cur_thread_ok] at et
      obtain rfl := ok_inj_ff et
      rw [set_reg_ok'] at e1
      obtain rfl := ok_inj_ff e1
      have hN1 : NodePlaced st K.heap.tcbs
          (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))
          (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) (core.num.U64.wrapping_sub nx 2#u64))) := by
        rw [LawfulStore.cpu_wr]; exact P.np.wr
      obtain ⟨⟨n0, a3⟩, hn, -⟩ := spec_ex_fd (hA.now a)
      rw [update_timestamp_ok ar hN1 hn] at eu
      have eX : X = rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n0 :=
        (Prod.mk.inj (ok_inj_ff eu)).1.symm
      subst eX
      exact (rr_dr Q hrp Q.hEp _ n0).alt ⟨rfl, rfl, fun _ _ => rfl⟩ (fun x hx => ⟨hx.1, hx.2.1⟩)
    refine ⟨bxi_userJ B kX hCs hI G, asidOff_agN (fun hi hhi => B.nuAsid kX hhi) G hAs, fun u usc C' => ?_⟩
    rw [ecur] at C' ⊢
    have C := rr_chk_backG D G C'
    obtain ⟨Pl, hy⟩ := hP u usc C
    refine ⟨rrPl_ag hX hnd hrp Q.hEp hI G Pl, ?_⟩
    rw [G.m (yieldA u) (nu_tcb hX Pl.hu (o := 3472#u64) (by simp) (by simp) (by simp))]
    exact hy
  · rw [wr_nu (x := rPrevA rptr) hba hb v (nu_rp hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV])
        (by simp [layout.reply.PREV])),
      wr_nu (x := rNextA rptr) hba hb v (nu_rp hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT])
        (by simp [layout.reply.NEXT]))]
    exact Q.nb
  · have eb : L.mem (L.wr s b v) (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      wr_nu hba hb v (nu_tcb hX hcH (o := 3368#u64) (by simp) (by simp) (by simp))
    rw [ecur, eb]
    intro h0
    have hn : L.mem s (boundA (L.curW s)) ∈ K.heap.ntfns := hXI.2.2.bnd _ hcH h0
    obtain ⟨r, -, a⟩ := hX.ntW _ hn 24#u64 (by simp) (by simp)
    have hnu : NU K (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) 24#u64) :=
      nu_of_region hX a (by rw [r]; intro h; cases h)
    rw [wr_nu (x := fld (L.mem s (boundA (L.curW s))) 24#u64) hba hb v hnu]
    exact Q.nbt h0

/-- **`hufR` of `rr_localPathJ` at the canonical sets** (module docstring): from `Cs` below 64
cores (`hCs`, [P]) and the locks (`hlk` [P]). -/
theorem vm_hufRK (hA : P0.ArchTotal ar) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    {rptr ep : U64} :
    ∀ s b v, VmRRPreJ st ar K K.heap.tcbs Cs Ω Sg K.heap.scs K.heap.ntfns K.heap.scBits Ac Locks rptr ep s →
      b ∈ K.user → Aligned b →
      ((K.heap ep = some .ep →
          VmRPre st ar K K.heap.tcbs Cs Ω K.heap Sg (Heap.replies K.heap) K.heap.scs K.heap.ntfns
            K.heap.scBits Ac Locks (L.wr s b v) rptr ep) ∧
        RdTab (L := L) (IoRS (st := st) K Locks (L.wr s b v)) (L.wr s b v)) ∧
      Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := fun s b v hE hb hba => by
  obtain ⟨B, hV, hT, hf⟩ := hE
  have hl := hlk s b v B hb hba
  obtain ⟨hrp, hep⟩ := B.vmFound hf
  obtain ⟨eR, eW, eD⟩ := B.ioRWDS_wr hb hba v hl
  exact ⟨⟨fun _ => B.vmRPre_wr hA hCs (hV hep) hrp hb hba v hl, B.rdTab_wr hb hba v eR hT⟩, hl, eR, eW, eD⟩

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM ReplyRecv local path with the bundle, `hufR` discharged** (`rr_localPathJ` at the
canonical sets). Premises: `hCs` [P] (`Cs` below 64 cores), `hlk` [P] (the glue's locks are not
changed by a user-word write), and `rr_localPathJ`'s `hA`, `hK`, `hU`, `hLA`, `hm`, `hmA`, `hpz`. -/
noncomputable def rr_localPathJK (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (hmA : ∀ s, VmRRPreJ st ar K K.heap.tcbs Cs Ω Sg K.heap.scs K.heap.ntfns K.heap.scBits Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d OwnMap.oAFFINITY) = L.mem s (fld d OwnMap.oAFFINITY))
    (hpz : ∃ p : SProg Bool, IsProg (rrBody S rptr ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPreJ st ar K K.heap.tcbs Cs Ω Sg K.heap.scs K.heap.ntfns K.heap.scBits Ac Locks rptr ep s →
        (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → E2E.Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) :=
  rr_localPathJ ar hA hK hU hLA hm hmA (vm_hufRK hA hCs hlk) hpz

end

end Fl4Proofs.P2.PathObl
