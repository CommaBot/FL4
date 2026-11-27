/-
P2 (line jsweep, gen 3): **vmF's `uf` [J] discharged** — `serializable_fl4_localW11PJ10`.

`VmFPremA.uf` (E2EPW11J8) asks that the VM-fault path's `Pre` part `VmPre`, the locks and the sets `IoRS` / `IoWS`
/ `IoDS` survive an aligned user-word write at **every** `VmPre` state of the index, not only at bundle states. It
does, at the index's canonical sets (the start state's `BunIxV`), with `Cs` below 64 cores, given the locks:

* **Locks** by the record's new **`kd`** [P] (`KernDetS (userV K).user i.Locks s` at every state, the same premise
  vt / st / vx already carry): `hlk_of_lkDetS`.
* **`IoRS` / `IoWS` / `IoDS`** (`ioRWDS_wrX`): `own` reads no user word (`E2E.ownDep` with the layout's `RegionOK` /
  `UserOK` from any bundle state), the core is kept, the current thread is a node word (`NU`, `nuNodeAt`).
* **`VmBase`** (`vmBase_ag`): `SlJAt.vmBase_wr` with the bundle state `σb` separated from the frame state `X`: the
  kernel base of `X` is the layout's (`VmBase.kb`), its core below the layout's core count (`VmBase.nc`), so its node
  words are `NU` (`SlJAt.nuNode64`); `BXI` by `bxi_userJ`; the other fields read TCB / SC words. Stated for any
  agreeing pair (`Ag st (NU K) X X'`), so it also serves after `update_timestamp`.
* **`VmFootHyps`** (`vmFootHyps_ag`): across an `NU`-agreeing pair (`BXI` by `bxi_userJ`; the fault-handler cap by
  `cap_congr_ag` of the TCB's slot words; `OutsideObjs` by `OutsideObjs.ksb`; the IPC buffers by `lookup_buf_agree`,
  the buffer words are words of a heap TCB, which holds no user word, `SlJAt.userObj`; `AsidOff` by `asidOff_agN`).
* **The `update_timestamp` commutation at a non-bundle state** (`ut_agX`): `update_timestamp` from `L.wr X b v`
  ends at a state agreeing on `NU` with `update_timestamp` from `X` (same Arch state; `vm_ag_upd`, the two clock
  words being node words of `X`). Then `VmFPre.hyp` by `vmFootHyps_ag`; `VmFPre.lk` / `hyt` and `VmGlue` by moving
  the fault checks / the handler cap back with `vm_chk_back` / `cap_congr_ag` along the `IoRS`-agreement (P2's
  `vm_dfOf` read facts at the entry's `update_timestamp` state); the receiver's `YIELD_TO` is a TCB word.
* `RdTab` by `SlJAt.nuAsid`.
* **`vmPre_wrX`** (all of the above at canonical sets), **`vmF_uf_of`**: `VmFPremA.uf` from the start state's
  `VmFEntJ10` (its `BunIxV` gives the canonical sets and `Cs` below 64, `SlJAtZ.csLt`) and `kd`.

Records and the top:
* **`VmFPremB`** = `nv`, `bun`, `kd` [P] (no `uf`); `VmFPremB.toA` (from a `VmFEntJ10` state).
* **`StartB`** [P]: `StartA` with vmF at `∃ h : VmFPremB, ∃ σ, (Ch σ ∧ VmFEntJ10 σ) ∧ ∀ h', GlueAt (· = σ)` (the start
  state pinned before the record's `uf` is formed, as vt's `eu` in `StartA`); **`startA_of_B`**.
* **`serializable_fl4_localW11PJ10`**: `serializable_fl4_localW11PJ8`'s premises with `StartB` starts.
* Satisfiability: **`startB_vmF_sat`**, **`startA_vmF_satK`** (`startA_vmF_sat` without `uf`, taking `kd`): at
  any chain state with vmF's entry facts.

No new [W] / [J]; the one new [P] is `VmFPremB.kd`. No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11J9
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld own oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## Frames at a non-bundle state -/

section fr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Kl : KLayout} {Cs Ω U Sg Ac : Set U64}

/-- A node word of a state with the layout's kernel base and a core of the layout is `NU`. -/
theorem nuNodeAt {σb X : S} (B : SlJAt (L := L) Kl σb) (hk : L.ksb X = L.ksb σb) (hc : (L.cpu X).val < Kl.ncores)
    {T : Set U64} (hN : NodePlaced st T X (L.cpu X)) {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    NU Kl (L.nodeAt X (L.cpu X) o) :=
  B.nuNode64 hk (lt_of_lt_of_le hc B.ncores_le) hN ho h8

/-- **`VmBase` across an `NU`-agreeing pair** at any `VmBase` state (canonical sets, `Cs` below 64 cores). -/
theorem vmBase_ag {σb X X' : S} (B : SlJAt (L := L) Kl σb) (hCs : ∀ c ∈ Cs, c.val < 64)
    (P : VmBase st Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac X)
    (G : Ag st (NU Kl) X X') :
    VmBase st Kl Kl.heap.tcbs Cs Ω Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac X' := by
  have hX := B.regionOKX
  have hk : L.ksb X = L.ksb σb := by rw [← P.kb]; exact B.kc.1.symm
  have nd : ∀ {o : U64}, o.val < 4288 → o.val % 8 = 0 → NU Kl (L.nodeAt X (L.cpu X) o) :=
    fun ho h8 => nuNodeAt B hk P.nc P.np ho h8
  have eN : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      L.mem X' (L.nodeAt X' (L.cpu X') o) = L.mem X (L.nodeAt X (L.cpu X) o) :=
    fun o ho h8 => by rw [G.node]; exact G.m _ (nd ho h8)
  have ecur : L.curW X' = L.curW X := eN _ (by rw [curth_val]; omega) (by rw [curth_val])
  have ecsc : L.cscW X' = L.cscW X := eN _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have etm : L.mem X' (tmA (L := L) X') = L.mem X (tmA (L := L) X) :=
    eN _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  have hcH : Kl.heap (L.curW X) = some .tcb := P.hT _ P.cT
  obtain ⟨⟨Qq, Rq, hq⟩, -, hXI, -, -⟩ := P.bxi
  refine
  { bxi := bxi_userJ B hk hCs P.bxi G
    csc := by rw [ecsc]; exact P.csc
    hcsc := ?_
    run := ?_
    lay := P.lay
    kb := by rw [G.k]; exact P.kb
    nc := by rw [G.c]; exact P.nc
    hT := P.hT
    hSc := P.hSc
    curAff := ?_
    cscCore := ?_
    affSc := ?_
    tmc := ?_ }
  · have e : L.mem X' (scA (L.curW X)) = L.mem X (scA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [ecur, ecsc, e]; exact P.hcsc
  · have e : L.mem X' (stA (L.curW X)) = L.mem X (stA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact P.run
  · have e : L.mem X' (affA (L.curW X)) = L.mem X (affA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ecur, G.c, e]; exact P.curAff
  · have e : L.mem X' (scCoreA (L.cscW X)) = L.mem X (scCoreA (L.cscW X)) :=
      G.m _ (nu_scw hX (P.hSc _ P.cscS) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    rw [ecsc, G.c, e]; exact P.cscCore
  · intro t ht h0
    have es : L.mem X' (scA t) = L.mem X (scA t) :=
      G.m _ (nu_tcb hX ht (o := 3464#u64) (by simp) (by simp) (by simp))
    rw [es] at h0 ⊢
    have hsc := (hXI.2.2.bound t ht h0).1
    have ec : L.mem X' (scCoreA (L.mem X (scA t))) = L.mem X (scCoreA (L.mem X (scA t))) :=
      G.m _ (nu_scw hX (P.hSc _ hsc) (o := layout.sc.CORE) (by simp [layout.sc.CORE])
        (by simp [layout.sc.CORE]))
    have ea : L.mem X' (affA t) = L.mem X (affA t) :=
      G.m _ (nu_tcb hX ht (o := 3520#u64) (by simp) (by simp) (by simp))
    rw [ec, ea]; exact P.affSc t ht h0
  · intro h0
    rw [etm] at h0 ⊢
    have hT := (hXI.2.2.tm.min _ hq.cur).resolve_left h0
    have ed : L.mem X' (tdA (L.mem X (tmA (L := L) X))) = L.mem X (tdA (L.mem X (tmA (L := L) X))) :=
      G.m _ (nu_tcb hX hT (o := 3528#u64) (by simp) (by simp) (by simp))
    have eh : L.mem X' (thA (L.mem X (tmA (L := L) X))) = L.mem X (thA (L.mem X (tmA (L := L) X))) :=
      G.m _ (nu_tcb hX hT (o := 3568#u64) (by simp) (by simp) (by simp))
    rw [ed, eh, G.c]; exact P.tmc h0

/-- **`VmFootHyps` across an `NU`-agreeing pair** (canonical sets, `Cs` below 64 cores; module docstring). -/
theorem vmFootHyps_ag {σb X X' : S} (B : SlJAt (L := L) Kl σb) (hk : L.ksb X = L.ksb σb)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (h : VmFootHyps (L := L) Kl.heap.tcbs Cs Ω U Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Ac Kl.heap
      Kl.heap.scBits X)
    (G : Ag st (NU Kl) X X') :
    VmFootHyps (L := L) Kl.heap.tcbs Cs Ω U Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Ac Kl.heap
      Kl.heap.scBits X' := by
  have hX := B.regionOKX
  have hK := B.regionOK
  have h0 := h.bxi.1.choose_spec.choose_spec
  have hN : NodePlaced st Kl.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have ecur : L.curW X' = L.curW X := by
    show L.mem X' (L.nodeAt X' (L.cpu X') layout.node.CUR_THREAD) = L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)
    rw [G.node]
    exact G.m _ (B.nuNode64 hk (hCs _ h0.cur) hN (by rw [curth_val]; omega) (by rw [curth_val]))
  have hcH : Kl.heap (L.curW X) = some .tcb := h0.curT
  have tw : ∀ y, Kl.heap y = some .tcb → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      L.mem X' (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 => by
    have ht' : TcbAddr y := h0.tcbs y hy
    exact G.m _ ⟨field_aligned ht' h1 h2, fun hu => B.userObj hu hy (fun z e => by cases e)
      (by unfold InW; rw [field_val ht' h1]; simp only [HKind.bits]; omega)⟩
  refine ⟨bxi_userJ B hk hCs h.bxi G, ?_, ?_, fun b hb => ⟨(h.user b hb).1.ksb G.k, (h.user b hb).2⟩, ?_,
    asidOff_agN (fun hi hhi => B.nuAsid hk hhi) G h.asid⟩
  · have e : L.mem X' (stA (L.curW X)) = L.mem X (stA (L.curW X)) :=
      G.m _ (nu_tcb hX hcH (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega)
        (by rw [st_val]))
    rw [ecur, e]; exact h.nb
  · have hc := h.cap
    obtain ⟨n0, n8⟩ := nu_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    rw [ecur]
    rw [tcb_slot_val, WP.spec_ok] at hc ⊢
    rw [cap_congr_ag G n0 n8]
    exact hc
  · intro y hy
    have ht' : TcbAddr y := h0.tcbs y hy
    have e1 : L.mem X' (ibA y) = L.mem X (ibA y) := tw y hy 3512#u64 (by simp) (by simp)
    have e2 : L.mem X' (sbA y) = L.mem X (sbA y) := by rw [sbA_field ht']; exact tw y hy 64#u64 (by simp) (by simp)
    have e3 : L.mem X' (core.num.U64.wrapping_add (sbA y) 8#u64) =
        L.mem X (core.num.U64.wrapping_add (sbA y) 8#u64) := by
      rw [sbA8_field ht']; exact tw y hy 72#u64 (by simp) (by simp)
    rw [lookup_buf_agree e1 e2 e3]
    exact h.buf y hy

variable {A : Type} {ar : machine.Arch A}

/-- **The `update_timestamp` commutation at a non-bundle state** (module docstring): a run from an `NU`-agreeing
state ends `NU`-agreeing with the run from `X`, at the same Arch state. -/
theorem ut_agX (hA : P0.ArchTotal ar) {σb X X' : S} (B : SlJAt (L := L) Kl σb) (hk : L.ksb X = L.ksb σb)
    (hc : (L.cpu X).val < Kl.ncores) {T : Set U64} (hN : NodePlaced st T X (L.cpu X)) (G : Ag st (NU Kl) X X')
    {a a1 : A} {s1' : S} (eu' : sched.update_timestamp st ar X' a = ok (s1', a1)) :
    ∃ s1, sched.update_timestamp st ar X a = ok (s1, a1) ∧ L.ksb s1 = L.ksb X ∧ Ag st (NU Kl) s1 s1' := by
  obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
  have eu := update_timestamp_ok ar hN hn
  obtain ⟨ea, G1⟩ := vm_ag_upd nu_al G
    (nuNodeAt B hk hc hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]))
    (nuNodeAt B hk hc hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])) eu eu'
  subst ea
  exact ⟨_, eu, utW_ksb X n, G1⟩

variable {Locks : S → U64 → Prop}

/-- **`IoRS`, `IoWS`, `IoDS` are kept by a user-word write** at any state whose current thread is kept (locks kept;
`SlJAt.ioRWDS_wr` without the bundle at the written state). -/
theorem ioRWDS_wrX {σb X : S} (B : SlJAt (L := L) Kl σb) {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b)
    (v : U64) (hl : Locks (L.wr X b v) = Locks X) (ecur : L.curW (L.wr X b v) = L.curW X) :
    IoRS (st := st) Kl Locks (L.wr X b v) = IoRS (st := st) Kl Locks X ∧
      IoWS (st := st) Kl Locks (L.wr X b v) = IoWS (st := st) Kl Locks X ∧
      IoDS (st := st) (L.wr X b v) = IoDS (st := st) X := by
  have eo : own Kl (L.mem (L.wr X b v)) = own Kl (L.mem X) :=
    E2E.ownDep B.regionOK B.userOK _ _ (fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb)))
  refine ⟨?_, ?_, ?_⟩ <;> funext w
  · simp only [IoRS, RPerm, WPerm, GateOnly, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoWS, WPerm, eo, hl, LawfulStore.cpu_wr]
  · simp only [IoDS, ecur, LawfulStore.cpu_wr, nodeAt_of_ksb (L.ksb_wr _ _ _)]

/-- **`VmPre` and the sets across a user-word write at any `VmPre` state** (canonical sets, `Cs` below 64 cores,
the locks kept; module docstring). -/
theorem vmPre_wrX (hA : P0.ArchTotal ar) {σb X : S} (B : SlJAt (L := L) Kl σb) (hCs : ∀ c ∈ Cs, c.val < 64)
    (P : VmPre st ar Kl Kl.heap.tcbs Cs Ω U Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      Locks X)
    {b : U64} (hb : b ∈ Kl.user) (hba : Aligned b) (v : U64) (hl : Locks (L.wr X b v) = Locks X) :
    VmPre st ar Kl Kl.heap.tcbs Cs Ω U Kl.heap Sg Kl.heap.replies Kl.heap.scs Kl.heap.ntfns Kl.heap.scBits Ac
      Locks (L.wr X b v) ∧
      IoRS (st := st) Kl Locks (L.wr X b v) = IoRS (st := st) Kl Locks X ∧
      IoWS (st := st) Kl Locks (L.wr X b v) = IoWS (st := st) Kl Locks X ∧
      IoDS (st := st) (L.wr X b v) = IoDS (st := st) X := by
  obtain ⟨F, Gl, Tb⟩ := P
  have Pb := F.base
  have hX := B.regionOKX
  have hk : L.ksb X = L.ksb σb := by rw [← Pb.kb]; exact B.kc.1.symm
  have hN := Pb.np
  have G : Ag st (NU Kl) X (L.wr X b v) := ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have ecur : L.curW (L.wr X b v) = L.curW X := by
    show L.mem (L.wr X b v) (L.nodeAt (L.wr X b v) (L.cpu (L.wr X b v)) layout.node.CUR_THREAD) =
      L.mem X (L.nodeAt X (L.cpu X) layout.node.CUR_THREAD)
    rw [G.node]
    exact G.m _ (nuNodeAt B hk Pb.nc hN (by rw [curth_val]; omega) (by rw [curth_val]))
  obtain ⟨eR, eW, eD⟩ := ioRWDS_wrX (Locks := Locks) B hb hba v hl ecur
  -- the run from the written state against the run from `X`
  have UT : ∀ a s1' a1, sched.update_timestamp st ar (L.wr X b v) a = ok (s1', a1) →
      ∃ s1, sched.update_timestamp st ar X a = ok (s1, a1) ∧ L.ksb s1 = L.ksb X ∧
        Ag st (IoRS (st := st) Kl Locks X) s1 s1' ∧ L.curW s1' = L.curW X ∧ VmDF st Kl Kl.heap.tcbs Locks X s1 ∧
        Ag st (NU Kl) s1 s1' := by
    intro a s1' a1 eu'
    obtain ⟨s1, eu, k1, G1⟩ := ut_agX hA B hk Pb.nc hN G eu'
    have D := vm_dfOf hA F Gl eu
    have G1R : Ag st (IoRS (st := st) Kl Locks X) s1 s1' := ⟨G1.k, G1.c, fun x hx => G1.m x ⟨hx.1, hx.2.1⟩⟩
    have ec : L.curW s1' = L.curW X := by
      show L.mem s1' (L.nodeAt s1' (L.cpu s1') layout.node.CUR_THREAD) = _
      rw [G1R.node, G1R.m _ (D.nd _ (by rw [curth_val]; omega) (by rw [curth_val]))]
      exact D.cur
    exact ⟨s1, eu, k1, G1R, ec, D, G1⟩
  refine ⟨⟨⟨vmBase_ag B hCs Pb G, ?_, ?_, F.hEp, F.hRp, ?_⟩, ?_, ?_⟩, eR, eW, eD⟩
  · intro a s1' a1 eu'
    obtain ⟨s1, eu, k1, -, -, -, G1⟩ := UT a s1' a1 eu'
    exact vmFootHyps_ag B (by rw [k1, hk]) hCs (F.hyp a s1 a1 eu) G1
  · intro a s1' a1 ptr badge dest r eu' C'
    obtain ⟨s1, eu, -, G1R, ec, D, -⟩ := UT a s1' a1 eu'
    rw [ec] at C'
    have C := vm_chk_back D G1R C'
    rw [← D.cur] at C
    rw [hl]
    exact F.lk a s1 a1 ptr badge dest r eu C
  · intro a s1' a1 ptr badge dest r eu' C'
    obtain ⟨s1, eu, -, G1R, ec, D, -⟩ := UT a s1' a1 eu'
    rw [ec] at C'
    have C := vm_chk_back D G1R C'
    have hdT : Kl.heap dest = some .tcb := by
      obtain ⟨-, ⟨sl, x, y, g, gr, hS, hcap, -⟩, hep, hh, -⟩ := C
      obtain ⟨-, -, hHT⟩ := D.ep sl ptr badge x y g gr hS hcap
      have hst : L.epState s1 ptr = obj.EP_RECV := by
        rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at hep; exact ok_inj_ff hep
      have hdd : dest = L.mem s1 (epHeadA ptr) := by
        rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)] at hh; exact (ok_inj_ff hh).symm
      rw [hdd]; exact hHT hst
    rw [← D.cur] at C
    rw [wr_nu (x := yieldA dest) hba hb v (nu_tcb hX hdT (o := 3472#u64) (by simp) (by simp) (by simp))]
    exact F.hyt a s1 a1 ptr badge dest r eu C
  · intro a s1' a1 sl ptr badge x y g gr eu' hsl hcap
    obtain ⟨s1, eu, -, G1R, ec, D, -⟩ := UT a s1' a1 eu'
    rw [ec] at hsl
    obtain ⟨r0, r8⟩ := D.sl sl hsl
    rw [cap_congr_ag G1R r0 r8] at hcap
    rw [hl]
    exact Gl a s1 a1 sl ptr badge x y g gr eu (by rw [D.cur]; exact hsl) hcap
  · rw [eR]
    intro hi hhi
    have ea : L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) :=
      wr_nu hba hb v (B.nuAsid hk hhi)
    rw [L.ksb_wr, ea]
    exact Tb hi hhi

end fr

/-! ## vmF's `uf` from the start state -/

section uf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} {ar : machine.Arch A}
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **`VmFPremA.uf` from the start state's entry facts and `kd`** (module docstring). -/
theorem vmF_uf_of (hA : P0.ArchTotal ar) {i : VmFArg S} {K : KLayoutV} {σ : S}
    (E : VmFEntJ10 st ar arI AR MR i K σ) (kd : ∀ s, KernDetS (L := L) (userV K).user i.Locks s) :
    ∀ s b v, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
      b ∈ (userV K).user → Aligned b →
      VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks (L.wr s b v) ∧
        i.Locks (L.wr s b v) = i.Locks s ∧
        IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
        IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro s b v hP hb hba
  have hl : i.Locks (L.wr s b v) = i.Locks s := hlk_of_lkDetS (kd s) hb hba v rfl
  have B : SlJAt (L := L) K.toKLayout σ := E.ix.toU.slJAtS.slJAt
  have hCs : ∀ c ∈ i.Cs, c.val < 64 := by
    obtain ⟨A', arI', AR', Zx, Lst, D, a', τ, Bz, -, -⟩ := E.ix.ac
    exact Bz.csLt
  obtain ⟨hKH, hT, -, hRp, hScs, hNt, hZ, -⟩ := E.ix
  rw [userV_empty E.nv] at hP hb ⊢
  rw [hT, hRp, hScs, hNt, hZ] at hP ⊢
  rw [← hKH] at hP ⊢
  obtain ⟨h1, h2, h3, h4⟩ := vmPre_wrX hA B hCs hP hb hba v hl
  exact ⟨h1, hl, h2, h3, h4⟩

end uf

/-! ## The record and the start fact -/

section prem
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's record without `uf`** (module docstring). -/
structure VmFPremB (i : VmFArg S) (K : KLayoutV) : Prop where
  /-- No VCPU in the layout (the glue's choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user` (as vt's
  / st's / vx's `kd`). -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.Locks s

variable {st ar}

/-- **`VmFPremA` from `VmFPremB` and a `VmFEntJ10` state.** -/
theorem VmFPremB.toA (hA : P0.ArchTotal ar) {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop}
    {MR : A3 → Fl4Spec.MachineState → Prop} {i : VmFArg S} {K : KLayoutV} {σ : S} (h : VmFPremB st i K)
    (E : VmFEntJ10 st ar arI AR MR i K σ) : VmFPremA st ar i K :=
  ⟨h.nv, h.bun, vmF_uf_of hA E h.kd⟩

end prem

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **The start fact with vmF at `VmFPremB`** [P] (module docstring). -/
def StartB (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .vmF j => ∃ q0, (∃ _h : VmFPremB st j K.toKLayoutV, ∃ σ : S,
      (Ch σ ∧ VmFEntJ10 st ar arI AR MR j K.toKLayoutV σ) ∧
      ∀ h' : VmFPremA st ar j K.toKLayoutV,
        GlueAt ((vmFSlotA st ar hA hm).liftAt j K.toKLayoutV m hK.base hU.base h') (fun σ' : S => σ' = σ)
          c hs m q0) ∧
      q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅
  | i => StartA st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartB` gives `StartA`.** -/
theorem startA_of_B {Ch : S → Prop} {K : KLayoutP} {m : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartB st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartA st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | vmF j =>
    obtain ⟨q0, ⟨h1, σ, ⟨hC, hE⟩, hG⟩, e⟩ := h
    exact ⟨q0, ⟨h1.toA hA hE, (hG (h1.toA hA hE)).mono fun σ' e' _ => by rw [e']; exact ⟨hC, hE⟩⟩, e⟩
  | vmR j => exact h
  | io j => exact h
  | st j => exact h
  | irq j => exact h
  | sl j => exact h
  | vq j => exact h

end start

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **FL4 end to end, W11's glue, PTE convention, the `AFFINITY` agreement in the paths' `Pre`, vmF's `uf`
discharged** (module docstring): `serializable_fl4_localW11PJ8` with `StartB` starts. vmF's record is `nv`, `bun`,
`kd` [P]. -/
theorem serializable_fl4_localW11PJ10 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesCanon st K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPJ (fl4LocW11JA st ar hA hm hSt a0) (StartB st ar hA hm hSt a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  have h' := ExecWPJ.mono st (SF' := StartA st ar hA hm hSt a0 arI AR MR)
    (fun _ _ _ _ _ _ _ _ _ hsf => startA_of_B st ar hA hm hSt a0 hsf) h
  exact serializable_fl4_localW11PJ8 st ar hA hm hSt a0 P hIoa h0 hA0 hB hc0 hM0 h' hq

end top

/-! ## Satisfiability at a chain state -/

section sat
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **vmF's `StartB` holds at every chain state with vmF's entry facts** (memory `L.mem σ`, core `L.cpu σ`, locks
`j.Locks σ`), given the [P] `kd`. -/
theorem startB_vmF_sat {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ)
    {j : VmFArg S} (hE : VmFEntJ10 st ar arI AR MR j K.toKLayoutV σ)
    (kd : ∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) (a : A) :
    ∃ q, StartB st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmF j) := by
  have h : VmFPremB st j K.toKLayoutV := ⟨hE.nv, ⟨σ, ChainOf.bun hC σ hσ⟩, kd⟩
  exact ⟨_, ((vmFSlotA st ar hA hm).liftAt j K.toKLayoutV (L.mem σ) hK.base hU.base (h.toA hA hE)).body σ a,
    ⟨h, σ, ⟨hσ, hE⟩, fun _ => ⟨σ, a, rfl, rfl, rfl, fun _ _ _ => rfl, rfl⟩⟩, rfl⟩

/-- **`startA_vmF_sat` without `uf`**: vmF's `StartA` at every chain state with vmF's entry facts, given `kd` [P]. -/
theorem startA_vmF_satK {Ch : S → Prop} {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K)
    {σe σ : S} (hC : ChainOf (L := L) arI AR MR σe K.toKLayoutV.toKLayout Ch) (hσ : Ch σ)
    {j : VmFArg S} (hE : VmFEntJ10 st ar arI AR MR j K.toKLayoutV σ)
    (kd : ∀ s, KernDetS (L := L) (userV K.toKLayoutV).user j.Locks s) (a : A) :
    ∃ q, StartA st ar hA hm hSt a0 arI AR MR Ch K (L.mem σ) hK hU (L.cpu σ) (j.Locks σ) q (.vmF j) := by
  obtain ⟨q, hq⟩ := startB_vmF_sat st ar hA hm hSt a0 hK hU hC hσ hE kd a
  exact ⟨q, startA_of_B st ar hA hm hSt a0 hq⟩

end sat

end
end Fl4Proofs.P2.E2EP
