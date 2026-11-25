/-
# P2 (line p2sl): the accepted arms' read / write facts from the ownership map

`fltAcc_of` / `rrAcc_of`: `SlPreB`'s `hRWfG` / `hRWrG` (`FltAcc` / `RrAcc` for the sets `SlRS s` /
`SlWS s` at the prefix state), word by word through `OwnMap.own`, like `slDecIn_of`
(P2/SlDecL.lean):

* node words of this core (`rs_node`), the kernel globals and `KERNEL_ROOT` (`rs_ks`), the ASID
  table (`RegionOKX.asidT`) and the pools it names (`SlAccIn.pool`): gate-owned;
* the TCB words of the current thread, the receiver / replied thread: gate fields (`rs_tcb_gate`),
  or, the thread fit for its `STATE` writes (`Safe0`: homed here, queued only on a held lock;
  `SlPreB.hSt` / `hSd` / `hSu`), its home core's or, for the queue links, its queue lock's
  (`rw_tcb_safe`); their slots (`rs_tslot`); registers (`regs_safe`);
* the next queued thread's `EP_PREV` (trap arm, `SlAccIn.nq`): the handler endpoint's lock
  (`rw_tcb_q`);
* endpoint / reply object words: their lock (`slRW_of_lock`, fl4-sync's locks);
* SC words of SCs homed here (`scAcc_here`; `SlHere.cs` / `usc` / `rh`, `SlAccIn.dsc`);
* IPC buffer words: user words (`SlAccIn.fbuf` / `rbuf`; `SlWS` admits aligned user words).

Premises: `SlAccIn` [J]/[P] (each field tagged there), `RegionOKX` (with `asidT` [J]), `SlEnt`,
`SlHere`, `SlPreB` (its `hRWfG` / `hRWrG` are not used here).
-/
import Fl4Proofs.P2.SlDecL
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayout} {Locks : S → U64 → Prop}

/-! ## Owners to the read / write sets -/

/-- A word of a locked object is in the read and write sets. -/
theorem slRW_of_lock {s : S} {x p : U64} (ha : Aligned x) (h : region K x = .obj p) (hl : Locks s p) :
    SlRS (st := st) K Locks s x ∧ SlWS (st := st) K Locks s x := by
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) x := by
    show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) x)
    simp only [own, h]
    exact hl
  exact ⟨⟨ha, Or.inr (Or.inl hw)⟩, ⟨ha, Or.inr hw⟩⟩

/-- An aligned user word is in the read and write sets. -/
theorem slRW_of_user {s : S} {x : U64} (h : Aligned x ∧ x ∈ K.user) :
    SlRS (st := st) K Locks s x ∧ SlWS (st := st) K Locks s x :=
  ⟨⟨h.1, Or.inl h.2⟩, ⟨h.1, Or.inl h.2⟩⟩

/-- A non-gate, non-timer word of a thread fit for its `STATE` writes (`Safe0`: homed here,
queued only on a held lock) is in the read and write sets. -/
theorem rw_tcb_safe (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hg : ¬ GateField o.val) (hT : ¬ TimerField o.val) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) ∧
      SlWS (st := st) K Locks s (core.num.U64.wrapping_add t o) := by
  by_cases hG : GField o.val
  · have ha := (hX.tcbW t ht o h1 h2 h3).2.2
    have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (core.num.U64.wrapping_add t o) := by
      show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) (core.num.U64.wrapping_add t o))
      rw [own_tcbW hX ht h1 h2 h3]
      simp only [tcbOwner, if_neg hg, if_neg hT, if_pos hG, gOwner]
      by_cases hq : QueuedState (L.mem s (fld t oSTATE))
      · rw [if_pos hq]; exact hs.2 hq
      · rw [if_neg hq]; exact hs.1
    exact ⟨⟨ha, Or.inr (Or.inl hw)⟩, ⟨ha, Or.inr hw⟩⟩
  · exact rs_tcb_home hX ht h1 h2 h3 hg hT hG (by rw [affA_fld]; exact hs.1)

/-- A queue link of a thread queued on a held lock is in the read and write sets. -/
theorem rw_tcb_q (hX : RegionOKX K) {t o : U64} (ht : K.heap t = some .tcb) (h1 : 192 ≤ o.val)
    (h2 : o.val < 4096) (h3 : o.val % 8 = 0) (hG : GField o.val) {s : S}
    (hq : QueuedState (L.mem s (stA t))) (hl : Locks s (L.mem s (blockA t))) :
    SlRS (st := st) K Locks s (core.num.U64.wrapping_add t o) ∧
      SlWS (st := st) K Locks s (core.num.U64.wrapping_add t o) := by
  have hg : ¬ GateField o.val := by unfold GField at hG; unfold GateField; omega
  have hT : ¬ TimerField o.val := by unfold GField at hG; unfold TimerField; omega
  have ha := (hX.tcbW t ht o h1 h2 h3).2.2
  rw [stA_fld] at hq
  have hw : WPerm (own K) (L.cpu s) (Locks s) (L.mem s) (core.num.U64.wrapping_add t o) := by
    show HeldBy (L.cpu s) (Locks s) (own K (L.mem s) (core.num.U64.wrapping_add t o))
    rw [own_tcbW hX ht h1 h2 h3]
    simp only [tcbOwner, if_neg hg, if_neg hT, if_pos hG, gOwner, if_pos hq]
    exact hl
  exact ⟨⟨ha, Or.inr (Or.inl hw)⟩, ⟨ha, Or.inr hw⟩⟩

/-- A register address as an offset into the TCB (no placement needed). -/
theorem regA_eq' {t r : U64} (hr : r.val < 384) :
    ∃ o : U64, o.val = 256 + 8 * r.val ∧ regA t r = core.num.U64.wrapping_add t o := by
  have hv : (⟨BitVec.ofNat 64 (256 + 8 * r.val)⟩ : U64).val = 256 + 8 * r.val := by
    show (BitVec.ofNat 64 (256 + 8 * r.val)).toNat = _
    simp; omega
  refine ⟨⟨BitVec.ofNat 64 (256 + 8 * r.val)⟩, hv, ?_⟩
  apply UScalar.eq_of_val_eq
  unfold regA
  simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits, hv]
  omega

/-- The registers of a thread fit for its `STATE` writes. -/
theorem regs_safe (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {s : S}
    (hs : Safe0 (L.cpu s) (Locks s) (L.mem s) t) {r : U64} (hr : r.val < 384) :
    SlRS (st := st) K Locks s (regA t r) ∧ SlWS (st := st) K Locks s (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact rw_tcb_safe hX ht (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
    (by simp only [TimerField]; omega) hs

/-- A TCB slot's two words are in the read set. -/
theorem rs_tslot (hK : RegionOK K) (hX : RegionOKX K) {t i : U64} (ht : K.heap t = some .tcb)
    (hi : i.val < 6) {s : S} :
    SlRS (st := st) K Locks s (slotIdx t i) ∧
      SlRS (st := st) K Locks s (core.num.U64.wrapping_add (slotIdx t i) 8#u64) := by
  obtain ⟨-, -, -, -, a0, a8⟩ := hX.tslot t ht i hi
  obtain ⟨g0, g8⟩ := own_tslot hK hX ht hi (L.mem s)
  exact ⟨slRS_of_gate a0 g0, slRS_of_gate a8 g8⟩

theorem vtA_slot (t : U64) : vtA t = slotIdx t layout.tcb.SLOT_VTABLE := by
  unfold vtA slotIdx layout.cte.SIZE
  rfl

/-! ## The new entry facts -/

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

/-- **The entry facts the accepted arms need beyond `SlEnt` / `SlHere`**, at the entry state `s`
(prefix state `X`, under the arm's checks). -/
structure SlAccIn (K : KLayout) (Locks : S → U64 → Prop) (Z : U64 → Nat) (Scs : Set U64)
    (found : U64 × U64) (s : S) : Prop where
  /-- [J] the ASID pools the table names are untyped kernel words: in no typed object of the
  layout (region `.none`, so gate-owned) and aligned (P1 `AsidOff` puts them among the kernel
  words `Ω`; the p2e VM line's `hTab` [J], P2/AccessVmTail.lean: the pools as their own region
  kind of the ownership map, discharged by P3's layout). -/
  pool : ∀ hi : U64, hi.val < 2048 → L.mem s (atAF K.ksb hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
    Aligned (peAF (L.mem s (atAF K.ksb hi)) lo) ∧ region K (peAF (L.mem s (atAF K.ksb hi)) lo) = .none
  /-- [J]/[P] trap arm: the receiver's reply object is a heap reply (P1 reply invariant: a thread
  blocked on receive with a nonzero `REPLY_OBJ` names a reply) and fl4-sync holds its lock
  (`lock_object(m, r, ..)`, crates/fl4-sync/src/lib.rs l.695). -/
  frp : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → K.heap r = some .reply ∧ Locks s r
  /-- [J] trap arm: the receiver's SC (nonzero: `schedulable_here`) is homed here (P1: a thread's
  bound SC is on the thread's core). -/
  dsc : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → ScHere (st := st) K Z Scs s (L.mem s (scA dest))
  /-- [J] trap arm: when the receiver is not the queue's tail, the next queued thread is a heap TCB
  blocked on receive on the handler endpoint (P1's endpoint queue invariant: `QueueRel` of the
  endpoint's queue, its members' `STATE` / `BLOCK_OBJ`). -/
  nq : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → (L.epQ X ptr).end ≠ dest →
    K.heap (L.mem X (nextA .Ep dest)) = some .tcb ∧ QueuedState (L.mem X (stA (L.mem X (nextA .Ep dest)))) ∧
      L.mem X (blockA (L.mem X (nextA .Ep dest))) = ptr
  /-- [J] trap arm: the receiver's IPC buffer words are aligned user words (P1 `BufW` / P3: a
  thread's IPC buffer lies in a frame, `K.user`). -/
  fbuf : SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ {ptr badge dest r : U64},
    FaultChecks st X (L.curW s) ptr badge dest r → ∀ rb, msg.lookup_ipc_buffer st X true dest = ok rb →
    BufW (fun b => Aligned b ∧ b ∈ K.user) rb
  /-- [J] ReplyRecv arm: the current thread's IPC buffer words are aligned user words. -/
  rbuf : ¬ SlTrap st s → ∀ a X a1, LocalPre (st := st) ar s a (X, a1) → ∀ buf,
    msg.lookup_ipc_buffer st X false (L.curW s) = ok buf → BufW (fun b => Aligned b ∧ b ∈ K.user) buf

/-! ## Common words at the prefix state -/

/-- The node, kernel globals, ASID words, timer and release-head words at the prefix state. -/
structure SlAccC (Z : U64 → Nat) (R W : U64 → Prop) (X : S) : Prop where
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt X (L.cpu X) o) ∧ W (L.nodeAt X (L.cpu X) o)
  dt : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.DOMAIN_TIME)
  cd : R (core.num.U64.wrapping_add (L.ksb X) layout.ks.CUR_DOMAIN)
  kr : R (krA (L := L) X)
  tab : RdTab (L := L) R X
  tm : L.mem X (tmA (L := L) X) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem X (tmA (L := L) X)) 3528#u64)
  rh : L.mem X (rhA (L := L) X) ≠ 0#u64 → R (scA (L.mem X (rhA (L := L) X))) ∧
    (∀ b, Aligned b → InSC (L.mem X (scA (L.mem X (rhA (L := L) X)))) (Z (L.mem X (scA (L.mem X (rhA (L := L) X))))) b →
      R b) ∧
    RdHead (L := L) R X (L.mem X (scA (L.mem X (rhA (L := L) X))))

theorem slAccC_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (Hh : SlHere (st := st) K Z Scs found s) (Ai : SlAccIn (st := st) ar K Locks Z Scs found s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) :
    SlAccC (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X := by
  have C := slCom_of ar hA hK hX E Hh LP
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
  refine ⟨fun o h1 h2 => by rw [nX]; exact rs_node hX E.hN Hh.ksb Hh.cpu h1 h2, C.dt, C.cd, ?_, ?_, C.tm, ?_⟩
  · show SlRS (st := st) K Locks s (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
    rw [kX]
    exact rs_ks hX E.hN Hh.ksb (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
  · intro hi hhi
    rw [kX, Hh.ksb]
    obtain ⟨r0, a0⟩ := hX.asidT hi hhi
    have e0 : L.mem X (atAF K.ksb hi) = L.mem s (atAF K.ksb hi) :=
      lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
        (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
    refine ⟨slRS_of_gate a0 (by simp only [own, r0]), fun lo hlo hne => ?_⟩
    rw [e0] at hne ⊢
    obtain ⟨a1', r1⟩ := Ai.pool hi hhi hne lo hlo
    exact slRS_of_gate a1' (by simp only [own, r1])
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
    exact (scAcc_here hX hz hco).rd

/-! ## The trap arm -/

/-- The checks' endpoint is the heap endpoint named by the fault-handler cap at the entry, whose
lock fl4-sync holds. -/
theorem trap_ep (hA : P0.ArchTotal ar) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (I : SlThrIn (st := st) K Locks found.1 s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) : K.heap ptr = some .ep ∧ Locks s ptr := by
  obtain ⟨sl, x, y, g, gr, hsl, hcap, -⟩ := hc.cap
  rw [tcb_slot_val] at hsl
  obtain rfl := ok_inj_ff hsl
  obtain ⟨f1, f2, f3, f4⟩ := I.fh hS
  rw [cap_congr (lp_mem ar hA E.hT E.hN E.hcT LP f1.1 f3) (lp_mem ar hA E.hT E.hN E.hcT LP f2.1 f4)] at hcap
  have hp : resPtr (obj.Slot.cap st (fhA (L := L) s) s) = ptr := resPtr_ok hcap
  have hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s) := ⟨_, _, _, _, _, _, hcap⟩
  have he := N.hep hS hE
  have hl := N.lep hS hE
  rw [hp] at he hl
  exact ⟨he, hl⟩

set_option maxHeartbeats 4000000 in
/-- **`SlPreB.hRWfG` from the ownership map.** -/
theorem fltAcc_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X (L.curW s) ptr dest r := by
  have I : SlThrIn (st := st) K Locks found.1 s := slThrIn_of hK hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccC_of ar hA hK hX E Hh Ai LP
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
      exact ⟨(I.fh hS).1, (I.fh hS).2.1⟩
    eph := slRW_of_lock a1h r1 hlk
    ept := slRW_of_lock a2h r2 hlk
    tf := fun o ho => rw_tcb_safe hX hc0 (by omega) (by omega) (by omega) (by simp only [GateField]; omega)
      (by simp only [TimerField]; omega) hs0
    treg := fun _ hr => (regs_safe hX hc0 hs0 hr).1
    trp := (rw_tcb_safe hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0).2
    drp := (rw_tcb_safe hX hdt (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    daf := rs_tcb_gate hX hdt (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    ddo := rs_tcb_gate hX hdt (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dsc0 := rs_tcb_gate hX hdt (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    diq := (rw_tcb_safe hX hdt (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    dpr := rs_tcb_gate hX hdt (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dyt := (rw_tcb_safe hX hdt (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    dst := by
      rw [stA_eq]
      exact (rw_tcb_safe hX hdt (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds).1
    dfi := (regs_safe hX hdt hds (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    den := (rw_tcb_safe hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hds).1
    dib := rs_tcb_gate hX hdt (o := 3512#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    dvt := by
      rw [vtA_slot]
      exact rs_tslot hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact rs_tslot hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨(rw_tcb_safe hX hdt (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds).2,
      (rw_tcb_safe hX hdt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds).2,
      (rw_tcb_safe hX hdt (o := 3480#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds).2,
      (rw_tcb_safe hX hdt (o := 3488#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hds).2⟩
    dreg := fun _ hr => (regs_safe hX hdt hds hr).2
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
      exact (rw_tcb_q hX hnt (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GField]) hq
        (by rw [hb]; exact hlk)).2
    buf := fun rb hrb hne i hi => (slRW_of_user (Ai.fbuf hS a X a1 LP hc rb hrb hne i hi)).2
    rt := (slRW_of_lock a3h r3 hlr).2
    spo := by
      rw [eSc]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (scAcc_here hX hz hco).rd _ am hin
    dsc := by
      rw [eSc]
      exact scAcc_here hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact scAcc_here hX hz' hco'
    tm := C.tm
    rh := C.rh }

/-! ## The ReplyRecv arm -/

set_option maxHeartbeats 4000000 in
/-- **`SlPreB.hRWrG` from the ownership map.** -/
theorem rrAcc_of (hA : P0.ArchTotal ar) (hK : RegionOK K) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (N : SlEnt (st := st) K Locks found s) (Hh : SlHere (st := st) K Z Scs found s)
    (Ai : SlAccIn (st := st) ar K Locks Z Scs found s) (hS : ¬ SlTrap st s)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) :
    RrAcc (L := L) Z (SlRS (st := st) K Locks s) (SlWS (st := st) K Locks s) X (L.curW s) found.1 found.2 u usc := by
  have I : SlThrIn (st := st) K Locks found.1 s := slThrIn_of hK hX (preAcc_of ar hX E Hh) E.hSt.1 N
  have C := slAccC_of ar hA hK hX E Hh Ai LP
  have D := (slDecIn_of ar hA hK hX E N Hh).rT hS a X a1 LP
  obtain ⟨-, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  have hs0 := E.hSt.2
  obtain ⟨hut, hus, -, -, -⟩ := E.hSu hS a X a1 LP u usc hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  -- the replied thread is the decided thread; its SC is homed here
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
    tReg := fun _ hr => (regs_safe hX hc0 hs0 hr).1
    tBuf := ⟨_, tcb_slot_val _ _, rs_tcb_gate hX hc0 (o := 3512#u64) (by simp) (by simp) (by simp)
      (by simp [GateField]), (rs_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1,
      (rs_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    tBw := fun buf hb hne i hi => (slRW_of_user (Ai.rbuf hS a X a1 LP buf hb hne i hi)).1
    ntf := D.ntf
    wRp := (rw_tcb_safe hX hc0 (o := 3360#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0).2
    wEn := (rw_tcb_safe hX hc0 (o := 3496#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0).2
    wEp := (rw_tcb_safe hX hc0 (o := 3504#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hs0).2
    rRt := D.rRt
    rNx := D.rNx
    rPv := (slRW_of_lock rpa rp1 hlr).1
    wNx := (slRW_of_lock rna rn1 hlr).2
    wPv := (slRW_of_lock rpa rp1 hlr).2
    wRt := (slRW_of_lock rta rt1 hlr).2
    uSt := by
      rw [stA_eq]
      exact (rw_tcb_safe hX hut (o := 3328#u64) (by simp) (by simp) (by simp) (by simp [GateField])
        (by simp [TimerField]) hus).1
    uFt := rw_tcb_safe hX hut (o := 3376#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus
    uSc := rs_tcb_gate hX hut (o := 3464#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uPr := rs_tcb_gate hX hut (o := 3448#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uAf := rs_tcb_gate hX hut (o := 3520#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uDo := rs_tcb_gate hX hut (o := 3432#u64) (by simp) (by simp) (by simp) (by simp [GateField])
    uIq := (rw_tcb_safe hX hut (o := 3592#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus).1
    uMx := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
        (by simp [layout.sc.REFILL_MAX])
      exact (scAcc_here hX hz hco).rd _ am hin
    uReg := fun _ hr => (regs_safe hX hut hus hr).2
    uYt := (rw_tcb_safe hX hut (o := 3472#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField]) hus).1
    uFi := (regs_safe hX hut hus (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])).1
    uVt := by
      rw [vtA_slot]
      exact rs_tslot hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := D.eTS
    wEh := (slRW_of_lock eha eh1 (E.hlk hS)).2
    wEt := (slRW_of_lock eta et1 (E.hlk hS)).2
    spo := by
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact (scAcc_here hX hz hco).rd _ am hin
    cor := (scAcc_here hX hz hco).rd _ aC hinC
    ccs := by
      rw [eC]
      exact (C.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    uHd := rdHead_here ar hA hX E Hh LP ⟨hz, hin0, hmx0, hco⟩
    uscA := scAcc_here hX hz hco
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, hco'⟩ := Hh.cs
      exact scAcc_here hX hz' hco'
    tm := C.tm
    rh := C.rh }

end

end Fl4Proofs.P2.PathObl
