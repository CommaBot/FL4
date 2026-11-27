/-
# P2: `PathObl.acc` for the VM ReplyRecv local path (line p2e, VM paths)

The accepted run of `syscall.handle_reply_recv_vm_local` (fl4-sync's `local_syscall` with
`found = (rptr, ep)`, the reply object and the endpoint it locked) on any store answering the
I/O line's maximal sets `IoRS K Locks s` / `IoWS K Locks s` (`P2/AccessIoOwn.lean`) as `st`, at its
entry state `s` (the counterpart of `VmMidF.tailAcc` / `vm_accG` of the VM-fault path).

* `rrX s v n`: the state after the prefix (`FAULT_IP := v`, then `update_timestamp`'s two node words);
  `rrX_mem` / `rrX_tcb` / `rrX_node` / `rrX_out`: the words it keeps;
* `VmRPre`: the entry facts (module docstring of `AccessVmPre`'s `VmBase`, P1's facts at the dispatch
  state, the locks, the typing of the found objects and of the bound notification);
* `VmBase.ntfnRd`: a word of the current thread's bound notification is readable;
* `rr_u_home`: the receiver is homed on this core and `BLOCKED_ON_REPLY` at the entry;
* `VmRPre.rrAccV`: p2e's `RrAccV` for `IoRS K Locks s` and any `W` holding the `VmWd` words of
  `IoWS K Locks s`, at the dispatch state;
* `rr_vm_accG`: **the accepted VM ReplyRecv local path on any store answering its words as `st`**
  (`GRd` / `GWr` on `VmWd` words, the `STATE` / `BLOCK_OBJ` writes `RrSW` a hypothesis, as `VmSW`)
  ends as the real run; `rr_vm_acc`: on `PathObl.guard st (IoRS K Locks s) (IoWS K Locks s)`.

Premises (fields of `VmRPre`, and `hTab` [J] as for `vm_acc`):
* `base`: `VmBase`'s, as tagged there;
* `mid` [J]: P1's facts at the dispatch state after the prefix (`LocalPre`): `BXI`, `AsidOff`, and
  under the fast path's checks m68's placement `RRPl` (P1 `rrPl_ofG`) and the receiver's
  `YIELD_TO = 0` (`hy0` of `sl_rr_foot`, as `VmFPre.hyt`);
* `lk` [P]: fl4-sync's `local_syscall` holds the locks of the reply object and the endpoint;
* `nb` [P]: fl4-sync's check under the lock that the reply has no call-stack neighbours
  (`rr_vm_local_foot`'s `hnb`);
* `hEp` [P]: the layout types `ep` an endpoint (fl4-sync found it through the caller's endpoint
  capability);
* `hRp`, `hNt` [J]: the layout's heap types P1's reply objects and notifications (`K.heap = H` at
  P3's `layoutJ`), a notification being 64 aligned bytes of its own region (as `VmLay.epw`);
* `nbt` [J]: the current thread's bound notification names it back (`BOUND_TCB`; l4v's
  `sym_refs` of the bound-notification references).
-/
import Fl4Proofs.P2.AccessVmRRL
import Fl4Proofs.P2.AccessVmTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InW fld own region GateField TimerField GField)

/-! ## The state after the prefix -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs : Set U64} {s : S}

/-- The state after the prefix of `handle_reply_recv_vm_local`: the current thread's `FAULT_IP`
written `v`, then `update_timestamp` (`utW`). -/
def rrX (s : S) (v n : U64) : S := utW (L := L) (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v) n

theorem rrX_ksb (s : S) (v n : U64) : L.ksb (rrX (L := L) s v n) = L.ksb s := by
  unfold rrX; rw [utW_ksb, L.ksb_wr]

theorem rrX_cpu (s : S) (v n : U64) : L.cpu (rrX (L := L) s v n) = L.cpu s := by
  unfold rrX; rw [utW_cpu, LawfulStore.cpu_wr]

theorem rrX_nodeAt (s : S) (v n o : U64) :
    L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n)) o = L.nodeAt s (L.cpu s) o := by
  rw [rrX_cpu, nodeAt_of_ksb (rrX_ksb s v n)]

theorem fip_eqV (hc : TcbAddr (L.curW s)) :
    ∃ k : U64, k.val = 392 ∧ regA (L.curW s) layout.reg.FAULT_IP = core.num.U64.wrapping_add (L.curW s) k := by
  obtain ⟨k, hk, e⟩ := regA_eq hc (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
  exact ⟨k, by rw [hk]; simp [layout.reg.FAULT_IP], e⟩

/-- The prefix writes `FAULT_IP` and the node's `CUR_TIME` / `CONSUMED` only. -/
theorem rrX_mem (hN : NodePlaced st T s (L.cpu s)) (hc : TcbAddr (L.curW s)) (v n : U64) {b : U64}
    (hb : Aligned b) (h0 : b ≠ regA (L.curW s) layout.reg.FAULT_IP) (h1 : b ≠ ctA (L := L) s)
    (h2 : b ≠ cnA (L := L) s) : L.mem (rrX (L := L) s v n) b = L.mem s b := by
  obtain ⟨k, hk, e⟩ := fip_eqV (L := L) hc
  have aF : Aligned (regA (L.curW s) layout.reg.FAULT_IP) := by
    rw [e]; exact field_aligned hc (by omega) (by omega)
  have hN1 : NodePlaced st T (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)
      (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)) := by
    rw [LawfulStore.cpu_wr]; exact hN.wr
  unfold rrX
  rw [utW_mem hN1 n hb (by rw [ctA_wr]; exact h1) (by rw [cnA_wr]; exact h2)]
  exact mem_wr_ne' aF hb (Ne.symm h0)

/-- A TCB word other than the current thread's `FAULT_IP` is kept by the prefix. -/
theorem rrX_tcb (hN : NodePlaced st T s (L.cpu s)) (hT : TcbPlaced T) (hcT : L.curW s ∈ T) (v n : U64)
    {y Kx : U64} (hy : y ∈ T) (hK : Kx.val < 4096) (h8 : Kx.val % 8 = 0) (hne : y = L.curW s → Kx.val ≠ 392) :
    L.mem (rrX (L := L) s v n) (core.num.U64.wrapping_add y Kx) = L.mem s (core.num.U64.wrapping_add y Kx) := by
  obtain ⟨k, hk, e⟩ := fip_eqV (L := L) (hT _ hcT)
  refine rrX_mem hN (hT _ hcT) v n (field_aligned (hT y hy) hK h8) ?_
    (fun e' => node_ne_field hN (by simp [layout.node.CUR_TIME]) hy (hT y hy) hK e'.symm)
    (fun e' => node_ne_field hN (by simp [layout.node.CONSUMED]) hy (hT y hy) hK e'.symm)
  rw [e]
  exact field_ne (hT y hy) (hT _ hcT) hK (by omega) (fun h => by rw [hk]; exact hne h)

/-- A node word other than `CUR_TIME` / `CONSUMED` is kept by the prefix. -/
theorem rrX_node (hN : NodePlaced st T s (L.cpu s)) (hc : TcbAddr (L.curW s)) (hcT : L.curW s ∈ T) (v n : U64)
    {o : U64} (ho : o.val < 4288) (h8 : o.val % 8 = 0) (h1 : o.val ≠ layout.node.CUR_TIME.val)
    (h2 : o.val ≠ layout.node.CONSUMED.val) :
    L.mem (rrX (L := L) s v n) (L.nodeAt s (L.cpu s) o) = L.mem s (L.nodeAt s (L.cpu s) o) := by
  obtain ⟨k, hk, e⟩ := fip_eqV (L := L) hc
  refine rrX_mem hN hc v n (nodeAt_aligned hN ho h8) ?_ (nodeAt_ne hN ho (by simp [layout.node.CUR_TIME]) h1)
    (nodeAt_ne hN ho (by simp [layout.node.CONSUMED]) h2)
  rw [e]; exact node_ne_field hN ho hcT hc (by omega)

/-- A word outside the TCBs and nodes is kept by the prefix. -/
theorem rrX_out (hN : NodePlaced st T s (L.cpu s)) (hc : TcbAddr (L.curW s)) (hcT : L.curW s ∈ T)
    (hcC : L.cpu s ∈ Cs) (v n : U64) {b : U64} (hb : OutsideObjs st T Cs s b) :
    L.mem (rrX (L := L) s v n) b = L.mem s b := by
  obtain ⟨k, hk, e⟩ := fip_eqV (L := L) hc
  refine rrX_mem hN hc v n hb.1 ?_
    (fun e' => out_ne_node (o := layout.node.CUR_TIME) hb hcC hN (by simp [layout.node.CUR_TIME]) (by rw [e']))
    (fun e' => out_ne_node (o := layout.node.CONSUMED) hb hcC hN (by simp [layout.node.CONSUMED]) (by rw [e']))
  rw [e]
  intro e'
  exact out_ne_field hb hcT hc (K := k) (by omega) (by rw [e'])

theorem rrX_csc (hN : NodePlaced st T s (L.cpu s)) (hc : TcbAddr (L.curW s)) (hcT : L.curW s ∈ T) (v n : U64) :
    L.cscW (rrX (L := L) s v n) = L.cscW s := by
  unfold LawfulStore.cscW LawfulStore.nodeA
  rw [rrX_nodeAt]
  exact rrX_node hN hc hcT v n (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
    (by simp [layout.node.CUR_SC, layout.node.CUR_TIME]) (by simp [layout.node.CUR_SC, layout.node.CONSUMED])

theorem rdHead_rrX {R : U64 → Prop} (hN : NodePlaced st T s (L.cpu s)) (hc : TcbAddr (L.curW s))
    (hcT : L.curW s ∈ T) (hcC : L.cpu s ∈ Cs) (v n : U64) {c : U64} (hO : OutsideObjs st T Cs s (headA c))
    (h : RdHead (L := L) R s c) : RdHead (L := L) R (rrX (L := L) s v n) c := by
  have e : L.rhead (rrX (L := L) s v n) c = L.rhead s c := rrX_out hN hc hcT hcC v n hO
  unfold RdHead at h ⊢; rw [e]; exact h

theorem zero_and_not1 : (0#u64 &&& ~~~1#u64) = 0#u64 := by
  apply eq_of_bv; simp [UScalar.bv_and]

end

/-! ## The entry facts -/

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s : S} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- **The entry facts of the VM ReplyRecv local path** for `found = (rptr, ep)` (module
docstring). -/
structure VmRPre {A : Type} (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (K : KLayout)
    (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64)
    (Locks : S → U64 → Prop) (s : S) (rptr ep : U64) : Prop where
  base : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s
  /-- [J] P1's facts at the dispatch state (`hy0` [J] for the receiver's `YIELD_TO`). -/
  mid : ∀ a s2 a2, LocalPre (st := st) ar s a (s2, a2) →
    BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s2 ∧ AsidOff (L := L) Ω Sg s2 ∧
    ∀ u usc, RRChecksG st ar fl4_abi.consts.fault.VMFault s2 a2 (L.curW s) rptr ep u usc →
      RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z s2 (L.curW s) rptr ep u usc ∧ L.mem s2 (yieldA u) = 0#u64
  /-- [P] fl4-sync holds the reply object's and the endpoint's locks. -/
  lk : Locks s rptr ∧ Locks s ep
  /-- [P] fl4-sync's no-neighbour check of the reply object. -/
  nb : L.mem s (rPrevA rptr) = 0#u64 ∧ L.mem s (rNextA rptr) = 0#u64
  /-- [P] the endpoint is typed an endpoint in the layout. -/
  hEp : K.heap ep = some .ep
  /-- [J] reply objects are typed in the layout. -/
  hRp : ∀ r ∈ Rp, K.heap r = some .reply
  /-- [J] notifications are typed, 64 aligned bytes of their own region. -/
  hNt : ∀ p ∈ Nt, K.heap p = some .ntfn ∧ p.val % 64 = 0 ∧ p.val + 64 ≤ 2 ^ 64 ∧
    ∀ b, InW p 64 b → region K b = .ntfn p
  /-- [J] the bound notification's `BOUND_TCB` is the current thread. -/
  nbt : L.mem s (boundA (L.curW s)) ≠ 0#u64 → L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s

/-- A word (not `BOUND_TCB`) of a notification bound to the current thread is readable: its owner
is the current thread's home core. -/
theorem VmBase.ntfnRd (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {p : U64}
    (hreg : ∀ b, InW p 64 b → region K b = .ntfn p) (h64 : p.val % 64 = 0) (hfit : p.val + 64 ≤ 2 ^ 64)
    (hbt : L.mem s (fld p 24#u64) = L.curW s) {o : U64} (ho : o.val < 64) (h8 : o.val % 8 = 0) (h24 : o.val ≠ 24) :
    IoRS (st := st) K Locks s (core.num.U64.wrapping_add p o) := by
  have hv : (core.num.U64.wrapping_add p o).val = p.val + o.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hr := hreg (core.num.U64.wrapping_add p o) ⟨by rw [hv]; omega, by rw [hv]; omega⟩
  have hn24 : ¬ ((core.num.U64.wrapping_add p o).val - p.val = 24) := by rw [hv]; omega
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (core.num.U64.wrapping_add p o) := by
    unfold WPerm
    simp only [own, hr]
    unfold OwnMap.ntfnOwner
    rw [if_neg hn24, hbt, if_pos (P.hT _ P.cT)]
    exact P.curAff
  exact ⟨by unfold Aligned; rw [hv]; omega, P.region_kernel (Or.inl (by rw [hr]; simp)), Or.inl hw⟩

variable {A : Type} {ar : machine.Arch A}

/-- **The receiver is homed on this core and blocked on the reply** at the entry. -/
theorem rr_u_home (P : VmBase st K T Cs Ω H Sg Rp Scs Nt Z Ac s) {a2 : A} {v n rptr ep u usc : U64}
    (Pl : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z (rrX (L := L) s v n) (L.curW s) rptr ep u usc)
    (C : RRChecksG st ar fl4_abi.consts.fault.VMFault (rrX (L := L) s v n) a2 (L.curW s) rptr ep u usc) :
    L.mem s (affA u) = L.cpu s ∧ L.mem s (stA u) = sched.TS_BLOCKED_ON_REPLY := by
  have hN := P.np
  have hT := P.tp
  have hcT := P.cT
  have hut : u ≠ L.curW s := Pl.hut
  obtain ⟨bh, hbh, hbt⟩ := C.here
  subst hbt
  have HF := here_facts (L := L) hbh
  have eaff : L.mem (rrX (L := L) s v n) (affA u) = L.mem s (affA u) :=
    rrX_tcb hN hT hcT v n Pl.hu (Kx := 3520#u64) (by simp) (by simp) (fun h => absurd h hut)
  have est : L.mem (rrX (L := L) s v n) (stA u) = L.mem s (stA u) :=
    rrX_tcb hN hT hcT v n Pl.hu (Kx := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val])
      (fun h => absurd h hut)
  obtain ⟨ist, hist, hist'⟩ := C.ust
  have hv := obj.Tcb.state.spec (L := L) (rrX (L := L) s v n) u
  rw [hist, WP.spec_ok] at hv
  refine ⟨by rw [← eaff, HF.aff, rrX_cpu], ?_⟩
  rw [← est, ← hv]
  have h5 : ist.val = 5 := by simpa using hist'
  exact UScalar.eq_of_val_eq (by rw [h5]; simp [sched.TS_BLOCKED_ON_REPLY])

/-- **`RrAccV` for the VM paths' sets** at the dispatch state `rrX s v n`, from `VmRPre` and P1's
placement `RRPl` there (`hAs`: P1's `AsidOff`; `hTab` [J] the ASID words readable). -/
theorem VmRPre.rrAccV {rptr ep : U64} (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    {a2 : A} {v n u usc : U64}
    (Pl : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z (rrX (L := L) s v n) (L.curW s) rptr ep u usc)
    (C : RRChecksG st ar fl4_abi.consts.fault.VMFault (rrX (L := L) s v n) a2 (L.curW s) rptr ep u usc)
    (hAs : AsidOff (L := L) Ω Sg (rrX (L := L) s v n))
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s) {W : U64 → Prop}
    (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b) :
    RrAccV (L := L) Z (IoRS (st := st) K Locks s) W (rrX (L := L) s v n) (L.curW s) rptr ep u usc := by
  have P := Q.base
  have hN := P.np
  have hT := P.tp
  have hcT := P.cT
  have hc := P.tA
  obtain ⟨⟨Qs, Rq, hq⟩, -, ⟨hO, -, -⟩, -, -⟩ := P.bxi
  have hcC : L.cpu s ∈ Cs := hq.cur
  have hu := Pl.hu
  have hut : u ≠ L.curW s := Pl.hut
  obtain ⟨haff, -⟩ := rr_u_home P Pl C
  -- `u`'s SC, on this core
  have escu : L.mem (rrX (L := L) s v n) (scA u) = L.mem s (scA u) :=
    rrX_tcb hN hT hcT v n hu (Kx := 3464#u64) (by simp) (by simp) (fun h => absurd h hut)
  have husc : L.mem s (scA u) = usc := by rw [← escu]; exact Pl.husc
  have hcore : L.mem s (scCoreA usc) = L.cpu s := by
    rw [← husc, P.affSc u hu (by rw [husc]; exact Pl.hsc0), haff]
  have hacc := P.scacc (Locks := Locks) Pl.hcS hcore
  -- the caller's SC is the current SC
  obtain ⟨b0, hsch0, hb0⟩ := C.sch
  subst hb0
  have hsp := sched.is_schedulable.spec' (L := L) (rrX (L := L) s v n) (L.curW s)
  rw [hsch0, WP.spec_ok] at hsp
  obtain ⟨-, hts0, -, -⟩ := hsp rfl
  have esct : L.mem (rrX (L := L) s v n) (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    rrX_tcb hN hT hcT v n hcT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
  have ecsc : L.cscW s = L.mem s (scA (L.curW s)) := P.hcsc (by rw [← esct]; exact hts0)
  -- the reply object and the endpoint (locked)
  have rp := Pl.hO.rp rptr Pl.hrR
  have hrK := Q.hRp rptr Pl.hrR
  have aRt : IoRS (st := st) K Locks s (rTcbA rptr) ∧ IoWS (st := st) K Locks s (rTcbA rptr) := by
    have h := rTcbA_val0 rptr; have := rp.1; have := rp.2
    exact P.reply hrK (b := rTcbA rptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.1
  have aNx : IoRS (st := st) K Locks s (rNextA rptr) ∧ IoWS (st := st) K Locks s (rNextA rptr) := by
    have h := rNextA_val rp; have := rp.1; have := rp.2
    exact P.reply hrK (b := rNextA rptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.1
  have aPv : IoRS (st := st) K Locks s (rPrevA rptr) ∧ IoWS (st := st) K Locks s (rPrevA rptr) := by
    have h := rPrevA_val rp; have := rp.1; have := rp.2
    exact P.reply hrK (b := rPrevA rptr) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.1
  have dRt : VmWd K (rTcbA rptr) := by
    have h := rTcbA_val0 rptr; have := rp.1; have := rp.2
    exact P.wdRp hrK (b := rTcbA rptr) ⟨by omega, by omega⟩
  have dNx : VmWd K (rNextA rptr) := by
    have h := rNextA_val rp; have := rp.1; have := rp.2
    exact P.wdRp hrK (b := rNextA rptr) ⟨by omega, by omega⟩
  have dPv : VmWd K (rPrevA rptr) := by
    have h := rPrevA_val rp; have := rp.1; have := rp.2
    exact P.wdRp hrK (b := rPrevA rptr) ⟨by omega, by omega⟩
  have aEh : IoWS (st := st) K Locks s (epHeadA ep) := by
    have h := epHeadA_val (ep := ep); have := Pl.hE.fits; have := Pl.hE.align
    exact (P.ep Q.hEp (b := epHeadA ep) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.2).2
  have aTS : IoRS (st := st) K Locks s (epTSA ep) ∧ IoWS (st := st) K Locks s (epTSA ep) := by
    have h := epTSA_val Pl.hE; have := Pl.hE.fits; have := Pl.hE.align
    exact P.ep Q.hEp (b := epTSA ep) ⟨by omega, by omega⟩ (by unfold Aligned; omega) Q.lk.2
  have dEh : VmWd K (epHeadA ep) := by
    have h := epHeadA_val (ep := ep); have := Pl.hE.fits; have := Pl.hE.align
    exact P.wdEp Q.hEp (b := epHeadA ep) ⟨by omega, by omega⟩
  have dTS : VmWd K (epTSA ep) := by
    have h := epTSA_val Pl.hE; have := Pl.hE.fits; have := Pl.hE.align
    exact P.wdEp Q.hEp (b := epTSA ep) ⟨by omega, by omega⟩
  -- node words
  have etm : L.mem (rrX (L := L) s v n) (tmA (L := L) (rrX (L := L) s v n)) = L.mem s (tmA (L := L) s) := by
    show L.mem (rrX (L := L) s v n) (L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n))
      layout.node.TIMER_MIN) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hc hcT v n (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      (by simp [layout.node.TIMER_MIN, layout.node.CUR_TIME]) (by simp [layout.node.TIMER_MIN, layout.node.CONSUMED])
  have erh : L.mem (rrX (L := L) s v n) (rhA (L := L) (rrX (L := L) s v n)) = L.mem s (rhA (L := L) s) := by
    show L.mem (rrX (L := L) s v n) (L.nodeAt (rrX (L := L) s v n) (L.cpu (rrX (L := L) s v n))
      layout.node.RELEASE_HEAD) = _
    rw [rrX_nodeAt]
    exact rrX_node hN hc hcT v n (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CUR_TIME])
      (by simp [layout.node.RELEASE_HEAD, layout.node.CONSUMED])
  refine
  { nd := fun o ho h8 => by
      rw [rrX_nodeAt]; exact ⟨(P.nd o ho h8).1, hW _ (P.wdNode ho) (P.nd o ho h8).2⟩
    dt := by rw [rrX_ksb]; exact P.ksw (by simp [layout.ks.DOMAIN_TIME]) (by simp [layout.ks.DOMAIN_TIME])
    cd := by rw [rrX_ksb]; exact P.ksw (by simp [layout.ks.CUR_DOMAIN]) (by simp [layout.ks.CUR_DOMAIN])
    kr := by unfold krA; rw [rrX_ksb]; exact P.ksw (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := ?_
    tSt := P.stw.1
    tSc := P.gate (off := 3464#u64) hcT (by simp) (by simp) (by simp) (by simp [GateField])
    tMx := by
      rw [esct, ← ecsc]
      have hw := sc_word_in hO P.cscS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (P.cscacc (Locks := Locks)).rd _ hw.1 hw.2
    tIq := (P.home (off := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    tMi := (P.reg (r := layout.reg.MSG_INFO) (lt384 (Or.inr (Or.inr (Or.inr rfl))))).1
    tBn := P.gate (off := 3368#u64) hcT (by simp) (by simp) (by simp) (by simp [GateField])
    tPr := P.gate (off := 3448#u64) hcT (by simp) (by simp) (by simp) (by simp [GateField])
    ntf := ?_
    wRp := hW _ (P.wdTcb (off := 3360#u64) hcT (by simp) (by simp) (by simp))
      (P.home (off := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2
    wEn := hW _ (P.wdTcb (off := 3496#u64) hcT (by simp) (by simp) (by simp))
      (P.home (off := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2
    wEp := hW _ (P.wdTcb (off := 3504#u64) hcT (by simp) (by simp) (by simp))
      (P.home (off := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2
    rRt := aRt.1
    rNx := aNx.1
    rPv := aPv.1
    wNx := hW _ dNx aNx.2
    wPv := hW _ dPv aPv.2
    wRt := hW _ dRt aRt.2
    uSt := by
      rw [stA_eq]
      exact (P.homeOf (off := 3328#u64) hu haff (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField])).1
    uFt := ⟨(P.homeOf (off := 3376#u64) hu haff (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) (by simp [GField])).1,
      hW _ (P.wdTcb (off := 3376#u64) hu (by simp) (by simp) (by simp))
        (P.homeOf (off := 3376#u64) hu haff (by simp) (by simp) (by simp) (by simp [GateField])
          (by simp [TimerField]) (by simp [GField])).2⟩
    uSc := P.gate (off := 3464#u64) hu (by simp) (by simp) (by simp) (by simp [GateField])
    uPr := P.gate (off := 3448#u64) hu (by simp) (by simp) (by simp) (by simp [GateField])
    uAf := P.gate (off := 3520#u64) hu (by simp) (by simp) (by simp) (by simp [GateField])
    uDo := P.gate (off := 3432#u64) hu (by simp) (by simp) (by simp) (by simp [GateField])
    uIq := (P.homeOf (off := 3592#u64) hu haff (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])).1
    uMx := by
      have hw := sc_word_in hO Pl.hcS (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact hacc.rd _ hw.1 hw.2
    uNi := hW _ (P.wdReg hu (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP]))
      (P.regOf hu haff (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).2
    uYt := (P.homeOf (off := 3472#u64) hu haff (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) (by simp [GField])).1
    uFi := (P.regOf hu haff (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    uVt := P.tslot hu (tcb_slot_eq u layout.tcb.SLOT_VTABLE) (by simp [layout.tcb.SLOT_VTABLE])
    eTS := aTS.1
    wEh := hW _ dEh aEh
    wEt := hW _ dTS aTS.2
    spo := by
      have hw := sc_word_in hO Pl.hcS (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact hacc.rd _ hw.1 hw.2
    cor := by
      have hw := sc_word_in hO Pl.hcS (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
      exact hacc.rd _ hw.1 hw.2
    ccs := ?_
    uHd := hacc.head Pl.hWF
    uscA := P.scaccW hW Pl.hcS hacc
    csc := by rw [rrX_csc hN hc hcT v n]; exact P.scaccW hW P.cscS P.cscacc
    tm := fun h0 => by rw [etm] at h0 ⊢; exact P.td h0
    rh := fun h0 => by
      rw [erh] at h0 ⊢
      obtain ⟨hrT, -, -⟩ := bxi_rh P.bxi h0
      have e1 : L.mem (rrX (L := L) s v n) (scA (L.mem s (rhA (L := L) s))) =
          L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        rrX_tcb hN hT hcT v n hrT (Kx := 3464#u64) (by simp) (by simp) (fun _ => by simp)
      rw [e1]
      obtain ⟨hqS, hqA⟩ := P.rsAcc (Locks := Locks) h0
      exact ⟨(P.rs h0).1, hqA.rd, rdHead_rrX hN hc hcT hcC v n (bxi_headOut P.bxi hqS) (P.rs h0).2⟩ }
  · -- the ASID words
    intro hi hhi
    have hA1 := hAs hi hhi
    rw [rrX_ksb] at hA1 ⊢
    have e : L.mem (rrX (L := L) s v n) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) :=
      rrX_out hN hc hcT hcC v n (hq.omega _ hA1.1)
    rw [e]
    exact hTab hi hhi
  · -- the bound notification
    intro nn hnn hne
    have hv := obj.Tcb.bound_ntfn.val (L := L) (rrX (L := L) s v n) (L.curW s)
    rw [hnn, WP.spec_ok] at hv
    subst hv
    have h0 : L.mem (rrX (L := L) s v n) (boundA (L.curW s)) ≠ 0#u64 := bne_iff_ne.mp hne
    have eb : L.mem (rrX (L := L) s v n) (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      rrX_tcb hN hT hcT v n hcT (Kx := 3368#u64) (by simp) (by simp) (fun _ => by simp)
    obtain ⟨hNn, -⟩ := Pl.hNt h0
    obtain ⟨-, h64, hfit, hreg⟩ := Q.hNt _ hNn
    have hbt := Q.nbt (by rw [← eb]; exact h0)
    rw [← eb] at hbt
    exact ⟨P.ntfnRd hreg h64 hfit hbt (o := layout.ntfn.TAIL_STATE) (by simp [layout.ntfn.TAIL_STATE])
        (by simp [layout.ntfn.TAIL_STATE]) (by simp [layout.ntfn.TAIL_STATE]),
      P.ntfnRd hreg h64 hfit hbt (o := layout.ntfn.SC) (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
        (by simp [layout.ntfn.SC])⟩
  · -- the current SC word of `usc`'s core: this node's
    have hw := sc_word_in hO Pl.hcS (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
    have eo : OutsideObjs st T Cs s (scCoreA usc) :=
      (Pl.hΩ _ (Pl.hSg.sub _ (Pl.scSg _ hw.1 hw.2))).ksb (rrX_ksb s v n).symm
    have e1 : L.mem (rrX (L := L) s v n) (core.num.U64.wrapping_add usc layout.sc.CORE) =
        L.cpu (rrX (L := L) s v n) := by
      rw [rrX_cpu]; exact (rrX_out hN hc hcT hcC v n eo).trans hcore
    rw [e1, rrX_nodeAt]
    exact (P.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1

/-! ## The accepted run -/

/-- **The accepted VM ReplyRecv local path on any store `gS`** answering `IoRS K Locks s` words as
`st`, the `VmWd` words of `IoWS K Locks s` (`hW`) and the `STATE` / `BLOCK_OBJ` writes (`hSW`: p2sl's
`RrSW` for a receiver of `T` homed on this core and blocked on the reply) as `st`: an accepted run on
`gS` ends exactly as the real run. Premises: `VmRPre`'s, `hTab` [J] (as `vm_accG`). -/
theorem rr_vm_accG (hA : P0.ArchTotal ar) {s' : S} {a a' : A} {rptr ep : U64}
    (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    {gS : machine.Store S} {W : U64 → Prop} [GRd gS st (IoRS (st := st) K Locks s)] [GWr gS st W]
    (hW : ∀ b, VmWd K b → IoWS (st := st) K Locks s b → W b)
    (hSW : ∀ u, u ∈ T → L.mem s (affA u) = L.cpu s → L.mem s (stA u) = sched.TS_BLOCKED_ON_REPLY →
      RrSW (L := L) gS (L.curW s) ep u)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (true, s', a')) :
    syscall.handle_reply_recv_vm_local gS ar s a (rptr, ep) = ok (true, s', a') := by
  have P := Q.base
  have hN := P.np
  have hcT := P.cT
  have hc := P.tA
  have hcC : L.cpu s ∈ Cs := by obtain ⟨⟨Qs, Rq, hq⟩, -, -, -, -⟩ := P.bxi; exact hq.cur
  have hnode : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      IoRS (st := st) K Locks s (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o) :=
    fun o ho h8 => ⟨(P.nd o ho h8).1, hW _ (P.wdNode ho) (P.nd o ho h8).2⟩
  have hpre : ∀ v s1 s2 a1, obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → ∃ n, s2 = rrX (L := L) s v n := by
    intro v s1 s2 a1 e1 eu
    rw [set_reg_ok'] at e1
    obtain rfl := ok_inj_ff e1
    have hN1 : NodePlaced st T (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)
        (L.cpu (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v)) := by
      rw [LawfulStore.cpu_wr]; exact hN.wr
    obtain ⟨⟨n, a2⟩, hn, -⟩ := spec_ex_fd (hA.now a)
    rw [update_timestamp_ok ar hN1 hn] at eu
    exact ⟨n, (Prod.mk.inj (ok_inj_ff eu)).1.symm⟩
  refine syscall.handle_reply_recv_vm_local.guard_acc (gS := gS) ar
    (hnode _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])).1
    (P.home (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).1
    (P.reg (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP])).1
    (hW _ (P.wdReg hcT (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP]))
      (P.reg (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).2) ?_ ?_ ?_ ?_ h
  · intro v s1 e1
    rw [set_reg_ok'] at e1
    obtain rfl := ok_inj_ff e1
    rw [ctA_wr, cnA_wr]
    exact ⟨(hnode _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1,
      (hnode _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).2,
      (hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1,
      (hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).2⟩
  · intro v s1 s2 a1 e1 eu
    obtain ⟨n, rfl⟩ := hpre v s1 s2 a1 e1 eu
    rw [rrX_nodeAt, rrX_nodeAt]
    exact ⟨(hnode _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1,
      (hnode _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1⟩
  · intro v s1 s2 a1 csc e1 eu ecsc
    obtain ⟨n, rfl⟩ := hpre v s1 s2 a1 e1 eu
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) _)] at ecsc
    have e : csc = L.cscW s := by
      rw [← rrX_csc hN hc hcT v n]; exact (ok_inj_ff ecsc).symm
    subst e
    exact rdHead_rrX hN hc hcT hcC v n (bxi_headOut P.bxi P.cscS) (P.cscacc.head P.cscwf)
  · intro nx s1 s2 a1 enx e1 eu h'
    have hLP : LocalPre (st := st) ar s a (s2, a1) := ⟨L.curW s, nx, s1, cur_thread_ok s, enx, e1, eu⟩
    obtain ⟨n, rfl⟩ := hpre _ s1 s2 a1 e1 eu
    obtain ⟨hI2, hAs2, hP2⟩ := Q.mid a _ a1 hLP
    obtain ⟨u0, usc0, C0, -⟩ := reply_recv_vm_found_acc st ar h'
    have Pl0 := (hP2 u0 usc0 C0).1
    have keep : ∀ b ∈ Ω, L.mem (rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n) b = L.mem s b :=
      fun b hb => rrX_out hN hc hcT hcC _ n ((Pl0.hΩ b hb).ksb (rrX_ksb s _ n).symm)
    have hrz : L.mem (rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n) (rNextA rptr) &&& ~~~1#u64 = 0#u64 ∧
        L.mem (rrX (L := L) s (core.num.U64.wrapping_sub nx 2#u64) n) (rPrevA rptr) &&& ~~~1#u64 = 0#u64 :=
      ⟨by rw [keep _ (Pl0.hSg.sub _ (Pl0.hO.nextW Pl0.hrR)), Q.nb.2]; exact zero_and_not1,
       by rw [keep _ (Pl0.hSg.sub _ (Pl0.hO.prevW Pl0.hrR)), Q.nb.1]; exact zero_and_not1⟩
    exact fastpath_vm.reply_recv_vm_found.guard (gS := gS) (R := IoRS (st := st) K Locks s) (W := W) ar hA hI2
      (fun u usc C => (hP2 u usc C).1) hrz (fun u usc C => (hP2 u usc C).2) hAs2
      (fun u usc C => Q.rrAccV (hP2 u usc C).1 C hAs2 hTab hW)
      (fun u usc C => hSW u (hP2 u usc C).1.hu (rr_u_home P (hP2 u usc C).1 C).1
        (rr_u_home P (hP2 u usc C).1 C).2) h'

/-- **The accepted VM ReplyRecv local path on the guarded store** (`acc` for
`handle_reply_recv_vm_local`): an accepted run on `PathObl.guard st (IoRS K Locks s) (IoWS K Locks s)`
ends exactly as the real run (`rr_vm_accG`). Premises: `VmRPre`'s, `hTab` [J]. -/
theorem rr_vm_acc (hA : P0.ArchTotal ar) {s' : S} {a a' : A} {rptr ep : U64}
    (Q : VmRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks s rptr ep)
    (hTab : RdTab (L := L) (IoRS (st := st) K Locks s) s)
    (h : syscall.handle_reply_recv_vm_local st ar s a (rptr, ep) = ok (true, s', a')) :
    syscall.handle_reply_recv_vm_local (PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s))
      ar s a (rptr, ep) = ok (true, s', a') := by
  refine rr_vm_accG (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hA Q hTab
    (fun _ _ hb => hb) ?_ h
  intro u hu haff _
  have P := Q.base
  have hsu := (P.homeOf (Locks := Locks) (off := 3328#u64) hu haff (by simp) (by simp) (by simp) (by simp [GateField])
    (by simp [TimerField]) (by simp [GField])).2
  have hst := (P.stw (Locks := Locks)).2
  have hbo := (P.home (Locks := Locks) (off := 3336#u64) (by simp) (by simp) (by simp) (by simp [GateField]) (by simp [TimerField])).2
  have e : core.num.U64.wrapping_add u layout.tcb.STATE = core.num.U64.wrapping_add u 3328#u64 := stA_eq u
  have hsu' : IoWS (st := st) K Locks s (core.num.U64.wrapping_add u layout.tcb.STATE) := by rw [e]; exact hsu
  exact ⟨SWr.of_W (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hst,
    SWr.of_W (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hst,
    fun _ _ => gst_write hst, fun _ => gst_write hbo,
    SWr.of_W (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hsu',
    SWr.of_W (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hsu',
    SWr.of_W (gS := PathObl.guard st (IoRS (st := st) K Locks s) (IoWS (st := st) K Locks s)) hsu'⟩

end

end Fl4Proofs.P2.PathObl
