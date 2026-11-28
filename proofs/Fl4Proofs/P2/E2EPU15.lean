/-
# P2 (line p3mc, gen 15): U15, sl's `VSafe9` discharged at the starts whose decided thread is homed (or absent)

## The sl starts discharged (`SlHAt`)
An sl start (`StartV2 … (.inl (.sl j))`) at core `c`'s view of `ρ` whose **decided thread** (`slThr`: the trap arm's
handler-endpoint head, the ReplyRecv arm's replied thread) is, when live (`SlLive`), homed on `c` in `ρ`. The fact is
stated at some state with the view's kernel words (`SlHAt`); every start state of the epoch at that view has the same
decided thread (`slThr_ag`: it is read from aligned kernel words).

## The proof (`sl_k0_safe`)
At such a start `σ` (`SlJAt`, `SlQ`, `QPs`, the view's kernel words) the glue's chain gives action 0 and a running
current thread (`sl_v0_SF`, P2/SlVBase), so `SlVC` (`slVC_of`: current thread, current SC, release head, SCs with a
nonzero back-pointer homed on `c`). Then `LocalPath.safeVQ` (as `vmR_k0_safe`, U14) with `Q` = agreement with `σ` on
the aligned kernel words, the core, the kernel base and the frame masks:
* **accepted** runs from every such start `s0` are runs on `guard (SlRS s0 ∧ SR) (SlWS s0 ∧ VNW)` (`sl_acc_v`,
  P2/SlBRun, applied at `s0` itself: its decided thread is `σ`'s, so homed);
* **declined** runs from `s0` are runs on `guard (SlRS s0 ∧ SR) (SlDS s0)` (`sl_dec_v`), moved to every alternative
  of `s0` by `run_transfer` (the alternative agrees with `s0` on `SlRS s0`).
`SR ⊆ VN ∧ ¬ PTE`, `VNW` as `safeVQ` asks.

**The caller's message registers and IPC buffer** (read by the non-VM `fastpath.reply_recv_found`): the registers are
the current thread's TCB words (homed), the buffer words user words in no region, which the view keeps with their
owner (P2/SlVAccR's docstring). Accepted runs are not moved between start states (they may read different buffer
values at different `s0`): the narrowed run is proved at each `s0`.

## U15
`U15At := U14At ∨ SlHAt`: **`serializable_fl4_localU15`** (`ExecWPRV10 … (¬IoIx) U15At StartV2`),
**`serializable_fl4_localU14of15`**.

## Premises of `serializable_fl4_localU15` vs `serializable_fl4_localU14`
* **Removed: `VSafe9` [J] at the sl starts with `SlHAt`** (decided thread homed on `c`, or not live). Nothing added.
* `VSafe9` [J] stays at the sl starts whose decided thread is another core's (the foreign-thread decline
  certificate, as U13's `vmR_fh_annV` / U10's `vmF_fh_annV`, is not done), and at st, irq, vq, invocation starts;
  `VSafe` [J] unchanged.

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.SlBRun
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP
  xsafeRunH_inv)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD)

noncomputable section
open Classical

/-! ## The decided thread at agreeing states, the view context -/

section ag
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

set_option maxHeartbeats 2000000 in
/-- **The decided thread is read from aligned kernel words.** -/
theorem slThr_ag {Kl : KLayout} {rp : U64} {s s' : S} (hJ : SlJAt (L := L) Kl s) {T : Set U64}
    (hN : NodePlaced st T s (L.cpu s)) (hcH : Kl.heap (L.curW s) = some .tcb)
    (hrp : ¬ SlTrap st s → NU Kl (rTcbA rp)) (G : Ag st (NU Kl) s s') :
    slThr st rp s' = slThr st rp s ∧ (SlLive st rp s' ↔ SlLive st rp s) := by
  have hX := hJ.regionOKX
  have hK := hJ.regionOK
  have ecur : L.curW s' = L.curW s := by
    unfold LawfulStore.curW
    rw [G.node]
    exact G.m _ (hJ.nuNode hN (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))
  have hT : SlTrap st s' ↔ SlTrap st s := by
    unfold SlTrap
    rw [ecur, PathObl.flags_ok, PathObl.flags_ok, G.m _ (nu_tcb hX hcH (o := 3456#u64) (by simp) (by simp) (by simp))]
  obtain ⟨n0, n8⟩ := nu_tslot hK hX hcH (i := layout.tcb.SLOT_FAULT_HANDLER) (by simp [layout.tcb.SLOT_FAULT_HANDLER])
  have hf : fhA (L := L) s' = fhA (L := L) s := congrArg (fun t => slotIdx t layout.tcb.SLOT_FAULT_HANDLER) ecur
  have ecap : obj.Slot.cap st (fhA (L := L) s) s' = obj.Slot.cap st (fhA (L := L) s) s :=
    cap_congr (G.m _ n0) (G.m _ n8)
  have hEp : IsEp (obj.Slot.cap st (fhA (L := L) s) s) →
      Kl.heap (resPtr (obj.Slot.cap st (fhA (L := L) s) s)) = some .ep := fun h => by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, B'⟩ := hJ
    exact B'.hep h
  refine ⟨?_, ?_⟩
  · unfold slThr
    by_cases hS : SlTrap st s
    · rw [if_pos (hT.2 hS), if_pos hS, hf, ecap]
      by_cases hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s)
      · have eh : L.mem s' (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) =
            L.mem s (epHeadA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) :=
          G.m _ (nu_ep hX (hEp hE) (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD]))
        rw [if_pos hE, if_pos hE, eh]
      · rw [if_neg hE, if_neg hE]
    · rw [if_neg (fun h => hS (hT.1 h)), if_neg hS, G.m _ (hrp hS)]
  · unfold SlLive
    by_cases hS : SlTrap st s
    · rw [if_pos (hT.2 hS), if_pos hS, hf, ecap]
      by_cases hE : IsEp (obj.Slot.cap st (fhA (L := L) s) s)
      · have et : L.mem s' (epTSA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) =
            L.mem s (epTSA (resPtr (obj.Slot.cap st (fhA (L := L) s) s))) :=
          G.m _ (nu_ep hX (hEp hE) (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
            (by simp [layout.ep.TAIL_STATE]))
        rw [ep_state_congr (st := st) et]
      · exact ⟨fun h => absurd h.1 hE, fun h => absurd h.1 hE⟩
    · rw [if_neg (fun h => hS (hT.1 h)), if_neg hS, G.m _ (hrp hS)]

variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The view context of an sl start state** (module docstring). -/
theorem slVC_of {K : KLayoutP} (nv : K.vcpus = ∅) (hK : RegionOKP K) (hU : UserOKP K) {c : U64}
    {ρ : U64 → U64} {s : S} (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s)
    (hq : QPs K st s) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x) (h0 : SlV0 st K c ρ) :
    SlVC (L := L) K c ρ s := by
  obtain ⟨hact, hrun⟩ := sl_view_act F.B F.E.hN F.E.hSt.1 hc hm h0
  obtain ⟨Cs', Ac', Ω', BV, BP⟩ := sl_vmBase nv hK hq.ks F.B hrun
  have scn : L.mem s (scA (L.curW s)) ≠ 0#u64 := BV.bxi.2.1.resume hact
  exact
  { hK := hK
    cpu := hc
    hm := hm
    cur := vm_cur_home hK BV hm
    csc := (vm_homes BP hm).1 scn
    rh := (vm_homes BP hm).2
    scb := fun p hp h0 => vm_sc_home_of_tcb BP hm hp h0
    ks := hq.ks
    ksb := hq.ksb
    tab := hq.tab
    upte := userNoE_pte hU
    scn := scn }

end ag

/-! ## The sl body at a view start whose decided thread is homed -/

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

/-- **The decided thread is homed on `c` (or not live)**, seen at some state with the view's kernel words. -/
def SlHome (K : KLayoutP) (c : U64) (ρ : U64 → U64) (j : SlArg S) : Prop :=
  ∃ σ' : S, L.cpu σ' = c ∧ L.ksb σ' = K.ksb ∧
    (∀ x, Aligned x → x ∉ K.user → L.mem σ' x = view K.toKLayout c ρ x) ∧
    (SlLive st j.found.1 σ' → ρ (fld (slThr st j.found.1 σ') oAFFINITY) = c)

end body

/-! ## The discharged sl starts -/

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end all

/-! ## U15 -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
