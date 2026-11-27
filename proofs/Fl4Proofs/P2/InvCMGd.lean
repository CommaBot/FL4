/-
# P2 (line p3mc, gen 28): every Copy / Mint run on a checked store reading a cut read set and user words

Handoff §32d item 2. As gen 27's `inv_run_gdV` / gen 28's `inv_run_gdA` for CNodeDelete:

* **`inv_acc_gen3V`**: gen 27's `inv_acc_genV` (`guard_acc2`) with the decode block given the IPC-buffer lookup
  (`guard_acc3`, as unify gen 2's `inv_acc_gen3R`);
* **`inv_run_gdCM`**: at a Copy / Mint entry (`SlJAt ∧ InvQCMW`) **every** run of the invocation — accepted
  (`inv_acc_gen3V` with the decode block `cmAccZV` / `cmFin8V`, P2/InvCMV) or declined (`inv_dec_genV` +
  `io_alt_midRV` at the entry itself) — runs on the checked store `gd st R Pw` as on `st`, for any read set `R`
  holding the `IoRS s` words off `K.ptes` of the run's word classes (`GCl`), the slot words and the aligned user
  words, and any write predicate `Pw` allowing the prefix's words (`IoWr`), the locked slots' non-base words, the
  write of a Null / Frame value into a locked non-TCB slot holding Null / Frame (the derived Frame cap into
  `dest`'s `CAP0`), the caller's two `STATE` writes and the aligned user words.

No named premise. New module; no existing statement changes.
-/
import Fl4Proofs.P2.InvDelGdA
import Fl4Proofs.P2.InvCMV
import Fl4Proofs.P2.E2EPU2C
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot
  oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section accCM
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop}

/-- (p3mc gen 28) **`inv_acc_genV` with the decode block given the IPC-buffer lookup** (`guard_acc3`, as unify gen 2's
`inv_acc_gen3R` of `inv_acc_genR`). -/
theorem inv_acc_gen3V {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {number : I64} {p : localinv.Plan}
    {s s' : S} {a a' : A} {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R]
    [GWr gS st W] (P : IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s) (hW : IoWr st W Z s)
    (Ent : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac R W s)
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP))
    (hMid : ∀ C, (∀ p r gs g, obj.Slot.cap st (L.curW s) s = ok (.CNode p r gs g) → C p r) →
      WalkCl (st := st) s C → (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots) →
      L.mem s (scA (L.curW s)) = L.cscW s → ∀ info, msg.msg_info st s (L.curW s) = ok info →
      IoMid (L := L) R W s s (L.curW s) info (L.mem s (regA (L.curW s) layout.reg.CAP)) C (L.curW s))
    (hSeen : ∀ x, SeenW p x → R x)
    (hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64))
    (hblk : ∀ info nx s1 s2 a1 buf length cap, msg.msg_info st s (L.curW s) = ok info →
      InvChk st ar s a (L.curW s) p nx s1 s2 a1 →
      msg.lookup_ipc_buffer st s2 false (L.curW s) = ok buf →
      (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length) else ok info.length) = ok length →
        obj.Slot.cap st p.slot s2 = ok cap →
      ∀ y, syscall.decode_invocation st ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y →
        syscall.decode_invocation gS ar s2 a1 info.label length p.slot cap true true true false buf p.extra = ok y ∧
        ∀ z, invRep st (L.curW s) y.2.1 y.2.2 y.1 = ok z →
          invRep gS (L.curW s) y.2.1 y.2.2 y.1 = ok z ∧ z.2.2 = core.result.Result.Ok () ∧
          FinOK (L := L) gS R W ar s z.1 z.2.1)
    (h : syscall.handle_invocation_local st ar s a number p = ok (true, s', a')) :
    syscall.handle_invocation_local gS ar s a number p = ok (true, s', a') := by
  obtain ⟨info, -, -, -, ht⟩ := handle_inv_inv h
  obtain ⟨nx0, s10, s20, a10, -, -, es10, eu0, -, -, -, hh0, -⟩ := invTail_inv ht
  have hsc2 := (here_facts hh0).sc
  have w := prefix_writes ar hA P.tp P.np P.cT es10 eu0
  have e1 : L.mem s20 (scA (L.curW s)) = L.mem s (scA (L.curW s)) :=
    w.2.2 _ (field_aligned P.tA (by simp) (by simp)) (preW_tcb P.tA P.np P.cT (K := 3464#u64) (by simp) (by simp))
  have hsc0 : L.mem s (scA (L.curW s)) = L.cscW s := (P.hcsc (by rw [← e1]; exact hsc2)).symm
  obtain ⟨C, hroot, hcl, hC⟩ := P.walk
  obtain ⟨⟨Q, Rq, hq⟩, hbd, ⟨hO, -, hX⟩, -, hS⟩ := P.bxi
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  refine syscall.handle_invocation_local.guard_acc3 (gS := gS) ar Ent.acc.nd hmi hfl hnx
    (hW.reg _ (by simp [layout.reg.FAULT_IP]))
    ?_ (fun x => still_holds_congr p x (fun w hw => GRd.read (hSeen w hw) x)) hps hblk h
  intro info nx s1 s2 a1 emi enx es1 eu
  have M2 := io_hmid' (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT
    (hMid C hroot hcl (fun p r m y hp hm => (hC p r m y hp hm).1) hsc0)
    (fun p r m y hp hm => (hC p r m y hp hm).2) (fun x hx => (P.fin x hx).2) (hd hX.cur)
    (fun h0 => ⟨(bxi_rh P.bxi h0).1, hd (bxi_rh P.bxi h0).2.1⟩) info nx _ s2 a1 emi enx es1 eu
  exact ⟨M2.k, M2.c, M2.cur, M2.yld, M2.rh, M2.td, M2.rs, M2.dt, M2.cd, M2.af, M2.dom, M2.iok.1.sc, M2.iok.1.inq,
    M2.iok.1.ib, M2.iok.1.bs⟩

end accCM

end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own region TcbSlot NullOrFrame GateField TimerField)

section gdCM
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 4000000 in
/-- **Every Copy / Mint run runs on the checked store `gd st R Pw` as on `st`**, user words read and written
(module docstring). -/
theorem inv_run_gdCM {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {Cs Ω Sg Ac : Set U64}
    {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayoutP} {m : U64 → U64}
    (hK : RegionOKP K) (hU : UserOKP K) {s : S}
    (hE : SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
    (hks : KsNoE (· ∈ K.ptes) K.toKLayoutV)
    {R G : U64 → Prop} {Pw : S → U64 → U64 → Prop}
    (Gc : GCl st K.toKLayout K.toKLayout.heap.scBits G s)
    (hR : ∀ b, IoRS (st := st) K.toKLayout Locks s b → b ∉ K.ptes → G b → R b)
    (hGs : ∀ b, SlotW K.toKLayout b → G b)
    (hW : IoWr st (WAll Pw) K.toKLayout.heap.scBits s)
    (hwS : ∀ q o, q ∈ K.slots → Locks s q → o.val < 32 → o.val % 8 = 0 → 8 ≤ o.val →
      (16 ≤ o.val ∨ (¬ TcbSlot K.toKLayout q ∧ NullOrFrame (L.mem s q))) →
        WAll Pw (core.num.U64.wrapping_add q o))
    (hw0 : ∀ q, q ∈ K.slots → Locks s q → ¬ TcbSlot K.toKLayout q → NullOrFrame (L.mem s q) →
      ∀ x v, NullOrFrame v → Pw x q v)
    (hst : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING →
      ∀ x, Pw x (core.num.U64.wrapping_add (L.curW s) layout.tcb.STATE) v)
    (hRu : ∀ b, PathObl.UserW K.toKLayout b → R b) (hWu : ∀ b, PathObl.UserW K.toKLayout b → WAll Pw b)
    {a : A} {number : I64} {r : Bool × S × A}
    (h : syscall.handle_invocation_local st ar s a number p = ok r) :
    syscall.handle_invocation_local (gd st R Pw) ar s a number p = ok r := by
  obtain ⟨hJ, hq⟩ := hE
  have PE := hq.1.1.1
  have hL : Slot8 K.toKLayout := fun q hq => PE.lay.slot8 q hq
  have hR' : ∀ b, IoRSR st K.toKLayout Locks s b → G b → R b := fun b h g =>
    hR b h.1 (ioRSR_rsE hK hks h).2 g
  have hSeen : ∀ x, SeenW p x → R x := by
    intro x hx
    obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, -, -, -, -, -, -,
      -, -, -, -, -, -, -, -, -, -, hdK, -, hLd, hsK, -, hLs, -, hSn⟩ := cm_coreW hq
    have hd0 : dest ≠ 0#u64 := fun e => hz_of K.toKLayout s hJ (e ▸ hdK)
    have hsr0 : src ≠ 0#u64 := fun e => hz_of K.toKLayout s hJ (e ▸ hsK)
    rcases hSn x hx with rfl | rfl | rfl | rfl
    · exact hR' _ (PE.lockSlotR hdK (hLd hd0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0]))
        (hGs _ (slotW_of hL hdK (by simp [layout.cte.CAP0])))
    · exact hR' _ (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0]))
        (hGs _ (slotW_of hL hsK (by simp [layout.cte.CAP0])))
    · exact hR' _ (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1]))
        (hGs _ (slotW_of hL hsK (by simp [layout.cte.CAP1])))
    · exact hR' _ (PE.lockSlotR hsK (hLs hsr0) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT]))
        (hGs _ (slotW_of hL hsK (by simp [layout.cte.NEXT])))
  have hps : R p.slot ∧ R (core.num.U64.wrapping_add p.slot 8#u64) := by
    have e := cmPsRN (L := L) hq
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_coreW hq
    exact ⟨hR' _ e.1 (Gc.sl _ hsK).1, hR' _ e.2 (Gc.sl _ hsK).2⟩
  have hmi : R (regA (L.curW s) layout.reg.MSG_INFO) :=
    hR' _ (PE.regR (Locks := Locks) (by simp [layout.reg.MSG_INFO])).1 (Gc.r _ (by simp [layout.reg.MSG_INFO]))
  have hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    hR' _ (PE.homeR (Locks := Locks) (off := 3456#u64) (by simp) (by simp) (by simp) (by simp [GateField])
      (by simp [TimerField])).1 (Gc.t _ (by simp) (by simp) (by simp))
  have hnx : R (regA (L.curW s) layout.reg.NEXT_IP) :=
    hR' _ (PE.regR (Locks := Locks) (by simp [layout.reg.NEXT_IP])).1 (Gc.r _ (by simp [layout.reg.NEXT_IP]))
  have Ent := PE.entV Gc hR' hW
  have hst' : ∀ v, v = sched.TS_RESTART ∨ v = sched.TS_RUNNING → SWr (gd st R Pw) st (L.curW s) v :=
    fun v hv X => gd_write (hst v hv X)
  obtain ⟨b, s', a'⟩ := r
  by_cases hb : b = true
  · subst hb
    refine inv_acc_gen3V (gS := gd st R Pw) (W := WAll Pw) hA PE hW Ent hmi hfl hnx
      (fun C hroot hcl hsl hsc0 info emi => PE.midV Gc hR' hW hroot hcl hsl hsc0 info emi) hSeen hps ?_ h
    intro info nx s1 s2 a1 buf length cap emi C hb' hl hcap y hy
    have hlb := hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi
    have E := cmEnt_ofW (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQCMW st Cs Ω Sg Ac Locks p K.toKLayout m s)
      ⟨hJ, hq⟩ hq (invCdtJ_of (fun _ h => h.1)) (hz_of _ s hJ)
    have hsl := cmSl_ofW hq
    have hbC : buf ≠ 0#u64 → ∀ i : U64, i.val < 128 →
        PathObl.UserW K.toKLayout (core.num.U64.wrapping_add buf (core.num.U64.wrapping_mul i 8#u64)) :=
      invBufSJ8_of hJ buf (by rw [← lib_prefix hA PE C false]; exact hb')
    obtain ⟨hdec, hrep⟩ := cmAccZV (R := R) (G := G) (gS := gd st R Pw) hA PE Gc hGs hR' hRu hW hWu hwS
      (fun q hq' hlk hT hn x v hv => gd_write (hw0 q hq' hlk hT hn x v hv)) hst' E hsl (cmDestZ_of hq) hbC
      (invBufJ8_of hJ) hlb C hcap hy
    refine ⟨hdec, fun z hz' => ?_⟩
    obtain ⟨h1, h2⟩ := cmFin8V (Locks := Locks) (gS := gd st R Pw) hA PE Ent (hst' _ (Or.inr rfl)) E hsl
      (invBufJ8_of hJ) hlb C hcap hy hz'
    exact ⟨hrep z hz', h1, h2⟩
  · exact inv_dec_genV (gS := gd st R Pw) (W := WAll Pw) Ent.acc.nd hmi hfl hnx
      (hW.reg _ (by simp [layout.reg.FAULT_IP]))
      (fun nx s1 s2 a1 _ e1 e2 => io_alt_midRV (m0 := m) hA PE Gc hR' (Alt.refl s) e1 e2) hSeen h hb

end gdCM

end Fl4Proofs.P2.E2EP
