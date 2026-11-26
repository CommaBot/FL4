/-
# P2 (line vmscope, gen 3): the VM-timer slot with its fire case in VM epochs — `serializable_fl4_localVX2`

`serializable_fl4_localVX2S` (P2/E2EPVX2.lean) runs U1's family in native epochs and the VM-exit slot in VM epochs.
This module adds **the VM-timer slot (`local_vm_timer_irq`) with its whole fire case** in VM epochs, at layouts with
VCPUs. At P3 scope the vt slot (`vtSlotA`, jsweep gen 2) has no accepted run (`vt_noAcc`: acceptance needs a bound
VCPU, which `VexitEnt.vin` puts in `K.vcpus = ∅`); here acceptance is real, so the fire case is proved again.

**Why not `vtSlotP3`'s records.** `VtPremP3.M` (one memory agreeing on every thread's `AFFINITY` word at *every*
`Pre` state) is false on SMP (jsweep gen 2, `vtPremP7M_false`). The fire-case facts are therefore **pointwise**:
conjuncts of the path's `Pre`, kept by user writes, given at the start state.

* **`vtimer_pathOblQ`** / **`vtimer_pathSideQ`** (namespace `Fl4Proofs.P2`): lvm's `vtimer_pathObl` /
  `vtimer_pathSide` at `Pre = VtmEnt ∧ Q` with the fire premises `hF` / `hFm` asked only at `Pre` states (their
  proofs use them only at the entry state: `vtimer_alt`, `vtimer_acc_own`, `vtimer_move`).
* **`VtFx`**: the fire-case facts at a state — `AffAg` (jsweep's agreement on `AFFINITY` words, used by `move`),
  `ub` (P1 `UserOK` of some user set holding every TCB's IPC-buffer lookup, for the waking case), `sl` (`SlotLayV`)
  and `pSg` (the bound VCPU's `PENDING` is no frame word). **`VtPreV`** = `VtmEnt ∧ VtmU ∧ VtFx` (`VtmU`: the IRQ
  state, kernel root and ASID table / pool words are no user words, needed by `ReadOnce`).
* **`vtmEnt_wrV`**, **`vtmU_wrV`**, **`vtFx_wr`**: each conjunct survives an aligned user-word write at any layout
  (`UserLayX` instead of a P3 bundle; no `nv`; `vexitEnt_wrV` for the VM-exit part, the ASID-table words `NU` from
  `VtmU`'s own `tabU`).
* **`vtimer_localPathV`**: `local_vm_timer_irq` as an `E2E.LocalPath` under `ownV` at `Pre = VtPreV`, fire case by
  `vtimer_acc_fnw_own` / `vtimer_acc_fwk_own` (acc), `vtimer_move_fnw` / `vtimer_move_fwk` (move, `AffAg` at the
  entry), `vtimer_acc_fnw_ownU` / `vtimer_acc_fwk_ownU` (ReadOnce, `hVU := VcpuNU`); `OL` from `UserLayX.lp`
  (`objLay_of_layP`), `PL` [P].
* **`VtIx`** (index convention), **`VtPremV`** (`ix`, `kd` [P], `PL` [P], `ul`, `vu`), **`vtEu_ofV`** (the path's
  `hEU` from `UserLayX`), **`vtSlotV`**, **`vt_avoidPV_path`** / **`vt_avoidPV`** (no PTE word read under `QPs`; the
  fire branch as `vt_avoidPJ_path`'s), **`vtSlotPV`** (cut, lifted to `ownP`).
* **`VtPremV2`** (`ix`, `kd`, `PL`; no [S]) and **`VtPremV2.toV`** (the rest from the epoch's `VtxBundle`);
  **`VtStartV2`** [S] (a VM epoch `K.vcpus ≠ ∅`, the record, and the start state with `VtPreV ∧ QPs`, its core,
  locks and memory link as `GlueAt` [P]); **`vtStartV2_at`**; **`vtStartV2_sat`** (satisfiability: at any state with
  the entry facts and any `m` agreeing off user words the start fact holds, `AffAg` derived from the link,
  **`affAg_of_linkP`**).
* **`StartVX3`**, **`serializable_fl4_localVX3G`**, **`serializable_fl4_localVX2`** = VX2S's family ⊕ `vtSlotPV`.

## The VM-exit notification (handoff vmscope gen 2 "Open point")
`fl4_sync::local_vm_exit` computes `vm_locks(s, cur_vcpu(s))` — reading the current thread's `BOUND_NTFN` and VCPU
words — before `with_locks` takes the locks. **Not a race**, for two independent reasons (Rust, verified against
the code): (1) the whole closure runs inside `try_local`'s active window (`try_enter_local` set this core's active
flag with the gate seen open, SeqCst Dekker handshake); every writer of `BOUND_NTFN` (`notification::bind_notification`
/ `unbind_notification` / `unbind_maybe_notification`, callers `tcb::decode` BindNotification / UnbindNotification
and `objects` finalisation) runs under the serial gate, which drains active local paths before it writes, and no
local path writes the word (`localinv` handles frame caps only, `localtimer` never binds). So the word cannot change
between the read and the body. (2) Even so, the body re-checks under the locks: `handle_vcpu_exit_local` declines
unless `vcpu::bound(ct) == v` and `ct.bound_ntfn == n`, and reads `n`'s state only after that check (`||`
short-circuit), as do `handle_vm_timer_irq_local`, `handle_vm_enter_local` and `vm_entry_ready`. Derived here:
**`vexit_acc_bound`** / **`vtimer_acc_bound`** (from the extracted code): every accepted run has `v = vOf s` and
`n` = the current thread's bound notification at its entry state; with the glue's [P] **`NtfnLk`** (`n ≠ 0 → lk s n`,
fl4-sync's `with_locks` over `(n, NTFN_BYTES)`) **`vexit_acc_ntfnLk`** / **`vtimer_acc_ntfnLk`**: an accepted run's
bound notification is one the core holds.

## Premises of `serializable_fl4_localVX2` (difference from VX2S)
| where | premise | tag |
|---|---|---|
| vt record `VtPremV2` | `ix` (index convention), `kd` (locks determined by kernel words), `PL` (plan locks held) | conv., [P], [P] |
| vt record, derived | `ul : UserLayX`, `vu : VcpuNU` from the epoch's `VtxBundle` | — |
| vt start `VtStartV2` | `K.vcpus ≠ ∅` (the glue uses this slot in VM epochs) | conv. |
| vt start entry | `VtmEnt` (lvm's entry facts), `VtmU`, `VtFx`'s `ub`, `sl`, `pSg`, `QPs` at the start state | [S] |
| vt start entry, derived | `VtFx.aff` from the memory link (`affAg_of_linkP`) | — |
| vt start | core, locks, memory link, armed program (`GlueAt`'s data) | [P] |
| VX2S's premises | unchanged | |

[S] justification (fl4-core `localvm.rs`, `localtimer.rs`, `layout.rs`): `VtmU` — the IRQ-state word and the kernel
root are words of the kernel-state block (`ks::IRQ_STATE`, `ks::KERNEL_ROOT`, below 13568), the ASID table its words
at `ks::ASID_TABLE = 288000`, the pool entries words of untyped-retyped ASID-pool objects: never user frames; `ub` —
user frames are `other` objects of the heap, apart from TCBs, nodes, endpoints and notifications, and every IPC
buffer is a user frame (`lookup_ipc_buffer` returns a frame cap's page); `sl` — a TCB's VTABLE / EPT slots are at
offsets 32 / 40 of its CNode-slot block (`tcb::SLOT_*`); `pSg` — `PENDING` is a word of the VCPU object (32 KiB,
`other 15`), never a frame word. At native states each is P3's (`irqLayK_of_slJAt`, `SlJAt.userObj`,
`slotLayV_all`, `usrW_vcpu`); a running guest changes none of them. No new [J] / [W]. No existing statement or file
changed except the root import list.
-/
import Fl4Proofs.P2.E2EPVX2
open Aeneas Aeneas.Std Result

/-! ## `PathObl` / `PathSide` of the VM-timer path with the fire premises pointwise -/

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard mguard RPerm WPerm GateOnly StepOK SProg IsProg NoZero interp interp_agree
  interp_mono interp_guard interp_to_mguard)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV RegionOKV UserOKV stepOKV_of_stepOK ownDepV)
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {irq n : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
  {p : SProg Bool} {m : U64 → U64}

/-- **`vtimer_pathObl` at `Pre = VtmEnt ∧ Q`, the fire premises asked at `Pre` states only.** -/
theorem vtimer_pathOblQ (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s) {Q : S → Prop}
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → Q s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → Q s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s1, a1))
    (hD : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1)) :
    PathObl.PathObl st (fun mm s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n) (fun b => b = true)
      (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) lk
      (fun s => VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s ∧ Q s) (VexitRS K st lk) (VexitWS K st lk)
      (IrqDec st) := by
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n = interp mm ar p x a :=
    fun mm x a => congrFun (congrFun (hp A ar mm) x) a
  have hQ : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → ∀ (x : S) (q v' : U64), IrqDec st s q →
      StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem (L.wr x q v')) := by
    intro s hE x q v' hq
    obtain ⟨a1, -, c, hc⟩ := hE.ent.dec hq
    refine stepOKV_of_stepOK hK ⟨fun w hw => absurd (own_keep hK.base hU.base a1 (Or.inl ⟨c, hc⟩) x v' w) hw,
      fun w hw _ => ?_⟩
    by_cases hwq : w = q
    · subst hwq; exact Or.inr (Or.inr (by simp only [OwnMap.ko, hc]))
    · by_cases hf : OwnMap.ko K.toKLayout m w = .free
      · exact Or.inr (Or.inr hf)
      · exact absurd (mem_wr_ne' a1 (OwnMap.ko_aligned hK.base hU.base m w hf) (fun e => hwq e.symm)) hw
  have dec : ∀ s a r, (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s ∧ Q s) →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok r → r.1 ≠ true →
      ∀ s' r', PathObl.Alt st (VexitRS K st lk s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' →
      localvm.handle_vm_timer_irq_local st ar s' a irq pl n = ok r' →
      r'.1 ≠ true ∧
      localvm.handle_vm_timer_irq_local (guard st (fun _ => True) (IrqDec st s)) ar s' a irq pl n = ok r' ∧
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s' a irq pl n = ok r' := by
    intro s a r hE hr hn s' r' hAlt h'
    rcases vtimer_alt ar hA hK (fun mm => hp A ar mm) hz hm hE.1 (fun hf s1 a1 => hF s a s1 a1 hE.1 hE.2 hf)
      (fun s1 a1 => hD s a s1 a1 hE.1)
      hAlt h' with ⟨s1, a1, e, -, -⟩ | ⟨s1, a1, -, h1, h2⟩
    · rw [hr] at e
      exact absurd (by rw [Result.ok_injective e]) hn
    · rw [eP] at h2
      refine ⟨by rw [h1]; exact Bool.false_ne_true, ?_, ?_⟩
      · rw [eP]; exact interp_mono (fun _ _ => trivial) (fun _ h => h) p hz s' a r' h2
      · rw [eP]; exact interp_to_mguard (fun x q v' hq => hQ s hE.1 x q v' hq) p hz s' a r' h2
  refine ⟨?_, dec, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact vtimer_acc_own ar hA hK hE.1 (fun hf => hF s a s1 a1 hE.1 hE.2 hf h) h
  · intro s x _ hx hu; exact vexit_read_own hx hu
  · intro s x hE hx hu
    exact vexit_write_own hK (fun q hq => ⟨(hE.1.ent.dec hq).2.1, (hE.1.ent.dec hq).2.2⟩) hx hu
  · intro s x hE hx
    exact vexit_aligned (fun q hq => (hE.1.ent.dec hq).1) hx
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (dec s a _ hE h Bool.false_ne_true s _ (PathObl.Alt.refl s) h).2.2
    · exact vtimer_move ar hA hK hU hp (fun _ => rfl) hE.1 (fun hf => hFm s a s1 a1 hE.1 hE.2 hf h) h

/-- **`vtimer_pathSide` at `Pre = VtmEnt ∧ Q`, the fire premise asked at `Pre` states only.** -/
theorem vtimer_pathSideQ (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s) {Q : S → Prop}
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → Q s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hD : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1))
    (hEU : ∀ s b v', (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s ∧ Q s) → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v') ∧ Q (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s) :
    PathObl.PathSide st (fun mm s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user) lk (fun s => VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s ∧ Q s)
      (VexitRS K st lk) (VexitWS K st lk) (IrqDec st) := by
  refine ⟨?_, fun s x _ hx => hx.1, OwnMap.ko_aligned hK.base hU.base m, fun s b v' hE hb hba =>
    ⟨hEU s b v' hE hb hba, hlk s b v' hb hba, vexitRS_wr_user hK hU hb hba (hlk s b v' hb hba),
      vexitWS_wr_user hK hU hb hba (hlk s b v' hb hba), irq_dec_user s b v'⟩⟩
  intro s s' a r hE hAlt h
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp A ar mm) x) a
  rcases vtimer_alt ar hA hK (fun mm => hp A ar mm) hz hm hE.1 (fun hf s1 a1 => hF s a s1 a1 hE.1 hE.2 hf)
      (fun s1 a1 => hD s a s1 a1 hE.1)
    hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
  · show localvm.handle_vm_timer_irq_local _ ar s' a irq pl n = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a r h2
  · show localvm.handle_vm_timer_irq_local _ ar s' a irq pl n = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2

end

/-! ## The VM-exit notification: an accepted run's is the bound one (Open point, module docstring) -/

section bnd
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **An accepted local VM exit exits the current thread's bound VCPU and names its bound notification** at its
entry state (`handle_vcpu_exit_local` re-checks both under the locks). -/
theorem vexit_acc_bound {s s' : S} {a a' : A} {v n : U64}
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    v = vOf st s ∧ L.mem s (boundA (L.curW s)) = n := by
  obtain ⟨-, -, -, eb, en, -⟩ := vexit_split ar h
  have hvb : vcpu.bound st s (L.curW s) = ok (vOf st s) := eq_of_spec_fd (vcpu.bound.spec (L := L) s _)
  rw [hvb] at eb
  rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en
  exact ⟨(ok_inj_ff eb).symm, ok_inj_ff en⟩

/-- **The glue holds the VM path's notification** [P] (fl4-sync's `vm_locks` lists `(n, NTFN_BYTES)`, `with_locks`
locks every nonzero object before the body runs). -/
def NtfnLk (lk : S → U64 → Prop) (n : U64) (s : S) : Prop := n ≠ 0#u64 → lk s n

/-- **An accepted local VM exit's bound notification is held** (from `NtfnLk` [P] and `vexit_acc_bound`). -/
theorem vexit_acc_ntfnLk {lk : S → U64 → Prop} {s s' : S} {a a' : A} {v n : U64} (hl : NtfnLk lk n s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a'))
    (h0 : L.mem s (boundA (L.curW s)) ≠ 0#u64) : lk s (L.mem s (boundA (L.curW s))) := by
  rw [(vexit_acc_bound ar h).2] at h0 ⊢
  exact hl h0

/-- **An accepted VM-timer run names the current thread's bound notification** (`vtimer_bnd`). -/
theorem vtimer_acc_bound {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a')) :
    vOf st s ≠ 0#u64 ∧ L.mem s (boundA (L.curW s)) = n :=
  ⟨(vtimer_bnd ar h).2.1, (vtimer_bnd ar h).2.2⟩

/-- **An accepted VM-timer run's bound notification is held** (`NtfnLk` [P]). -/
theorem vtimer_acc_ntfnLk {lk : S → U64 → Prop} {s s' : S} {a a' : A} {irq n : U64} {p : localtimer.TimerIrqPlan}
    (hl : NtfnLk lk n s) (h : localvm.handle_vm_timer_irq_local st ar s a irq p n = ok (true, s', a'))
    (h0 : L.mem s (boundA (L.curW s)) ≠ 0#u64) : lk s (L.mem s (boundA (L.curW s))) := by
  rw [(vtimer_acc_bound ar h).2] at h0 ⊢
  exact hl h0

end bnd

end Fl4Proofs.P2

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW RegionOK LayP)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## The fire-case facts and the frame lemmas -/

section fr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The fire-case facts at a state** (module docstring). -/
structure VtFx (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg : Set U64) (m : U64 → U64) (s : S) : Prop where
  /-- The map memory agrees with the state on every TCB's `AFFINITY` word (jsweep's `AffAg`). -/
  aff : AffAg st K.toKLayout m s
  /-- [S] some user-word set with P1 `UserOK` holding every TCB's IPC-buffer lookup. -/
  ub : ∃ U : Set U64, Fl4Proofs.P1.UserOK st T Cs Ω H U s ∧
    ∀ y ∈ T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [S] the VSpace slot words of this core's threads lie in TCB slot regions. -/
  sl : SlotLayV K.toKLayout st T s
  /-- [S] the bound VCPU's `PENDING` is no frame word. -/
  pSg : core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ Sg

/-- **The VM-timer path's `Pre` in VM epochs**: lvm's `VtmEnt`, `VtmU` and the fire-case facts. -/
abbrev VtPreV (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (lk : S → U64 → Prop) (irq n : U64) (m : U64 → U64)
    (s : S) : Prop :=
  VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s ∧ (VtmU K st irq s ∧ VtFx K st T Cs Ω H Sg m s)

variable {K : KLayoutV} {Cs Ω Sg Ac : Set U64} {lk : S → U64 → Prop} {irq n : U64}

/-- **`VtmEnt` across a user-word write at any layout** (`vtmEnt_wr` without `nv` and without a P3 bundle: the
VM-exit part by `vexitEnt_wrV`, the ASID-table words `NU` by `hat`). -/
theorem vtmEnt_wrV {X : S} (B : UserLayX L K.toKLayout) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hlk : ∀ s b w, b ∈ K.user → Aligned b → lk (L.wr s b w) = lk s)
    (hat : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user)
    (hE : VtmEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk irq n
      X) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    VtmEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk irq n
      (L.wr X b v) := by
  have hX := B.rx
  have E := hE.ent
  have h0 := E.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have hk : L.ksb X = K.ksb := ksb_of_stLay E.lay hN
  have G : Ag st (NU K.toKLayout) X (L.wr X b v) :=
    ⟨L.ksb_wr _ _ _, L.cpu_wr _ _ _, fun x hx => wr_nu hba hb v hx⟩
  have ecur : L.curW (L.wr X b v) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact wr_nu hba hb v ⟨nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]),
      E.lay.nu_node (by rw [curth_val]; omega)⟩
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  have evOf : vOf st (L.wr X b v) = vOf st X := by
    unfold vOf
    rw [ecur]
    exact wr_nu hba hb v (nu_tcb hX hcH (o := 3664#u64) (by simp) (by simp) (by simp))
  have hna : ∀ hi : U64, hi.val < 2048 → NU K.toKLayout (atAF (L.ksb X) hi) := fun hi hhi => by
    rw [hk]; exact ⟨(hX.asidT hi hhi).2, hat hi hhi⟩
  have ekr : krA (L := L) (L.wr X b v) = krA (L := L) X := by unfold krA; rw [L.ksb_wr]
  refine ⟨?_, by rw [L.ksb_wr]; exact hE.iq, by rw [ekr]; exact hE.kr, fun hi hhi => ?_,
    asidOff_agN hna G hE.asid⟩
  · rw [evOf]
    exact vexitEnt_wrV B hCs hlk E hb hba v
  · have eA : L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) := G.m _ (hna hi hhi)
    rw [L.ksb_wr, eA]
    exact hE.tab hi hhi

/-- **`VtmU` across a user-word write** (the ASID-table words are `NU` by `VtmU`'s own `tabU`). -/
theorem vtmU_wrV {X : S} (hX : RegionOKX K.toKLayout) (hk : L.ksb X = K.ksb) (h : VtmU K st irq X) {b : U64}
    (hb : b ∈ K.user) (hba : Aligned b) (v : U64) : VtmU K st irq (L.wr X b v) := by
  have hna : ∀ hi : U64, hi.val < 2048 → NU K.toKLayout (atAF (L.ksb X) hi) := fun hi hhi =>
    ⟨by rw [hk]; exact (hX.asidT hi hhi).2, (h.tabU hi hhi).1⟩
  have ekr : krA (L := L) (L.wr X b v) = krA (L := L) X := by unfold krA; rw [L.ksb_wr]
  refine ⟨?_, by rw [ekr]; exact h.krU, fun hi hhi => ?_⟩
  · rw [L.ksb_wr]; exact h.iqU
  · have eA : L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) := wr_nu hba hb v (hna hi hhi)
    rw [L.ksb_wr, eA]
    exact h.tabU hi hhi

/-- **The fire-case facts across a user-word write** (`AFFINITY`, IPC-buffer and VCPU words are TCB words, `NU` by
`UserLayX.userObj`; `UserOK` reads the kernel base only; `LocT` reads `AFFINITY` and the core). -/
theorem vtFx_wr {X : S} (B : UserLayX L K.toKLayout) {m : U64 → U64}
    (hE : VtmEnt K st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac lk irq n
      X) (h : VtFx K st K.heap.tcbs Cs Ω K.heap Sg m X) {b : U64} (hb : b ∈ K.user) (hba : Aligned b) (v : U64) :
    VtFx K st K.heap.tcbs Cs Ω K.heap Sg m (L.wr X b v) := by
  have hX := B.rx
  have E := hE.ent
  have h0 := E.inv.1.choose_spec.choose_spec
  have hT : TcbPlaced K.heap.tcbs := h0.tcbs
  have hN : NodePlaced st K.heap.tcbs X (L.cpu X) := h0.nodes _ h0.cur
  have ecur : L.curW (L.wr X b v) = L.curW X := by
    unfold LawfulStore.curW
    rw [nodeAt_wr, L.cpu_wr]
    exact wr_nu hba hb v ⟨nodeAt_aligned hN (by rw [curth_val]; omega) (by rw [curth_val]),
      E.lay.nu_node (by rw [curth_val]; omega)⟩
  have hcH : K.heap (L.curW X) = some .tcb := h0.curT
  have evOf : vOf st (L.wr X b v) = vOf st X := by
    unfold vOf
    rw [ecur]
    exact wr_nu hba hb v (nu_tcb hX hcH (o := 3664#u64) (by simp) (by simp) (by simp))
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, o.val < 4096 → o.val % 8 = 0 →
      L.mem (L.wr X b v) (core.num.U64.wrapping_add y o) = L.mem X (core.num.U64.wrapping_add y o) :=
    fun y hy o h1 h2 => wr_nu hba hb v ⟨field_aligned (hT y hy) h1 h2, fun hu => B.userObj hu hy
      (fun z e => by cases e) (by unfold InW; rw [field_val (hT y hy) h1]; simp only [HKind.bits]; omega)⟩
  refine ⟨fun d hd => ?_, ?_, fun y hy k hk => ?_, by rw [evOf]; exact h.pSg⟩
  · have e : L.mem (L.wr X b v) (fld d oAFFINITY) = L.mem X (fld d oAFFINITY) :=
      tw d hd oAFFINITY (by simp [oAFFINITY]) (by simp [oAFFINITY])
    rw [h.aff d hd, e]
  · obtain ⟨U, hU, hbU⟩ := h.ub
    refine ⟨U, hU.ksb (L.ksb_wr _ _ _), fun y hy => ?_⟩
    have ht := hT y hy
    have e1 : L.mem (L.wr X b v) (ibA y) = L.mem X (ibA y) := tw y hy 3512#u64 (by simp) (by simp)
    have e2 : L.mem (L.wr X b v) (sbA y) = L.mem X (sbA y) := by
      rw [sbA_field ht]; exact tw y hy 64#u64 (by simp) (by simp)
    have e3 : L.mem (L.wr X b v) (core.num.U64.wrapping_add (sbA y) 8#u64) =
        L.mem X (core.num.U64.wrapping_add (sbA y) 8#u64) := by
      rw [sbA8_field ht]; exact tw y hy 72#u64 (by simp) (by simp)
    rw [lookup_buf_agree e1 e2 e3]
    exact hbU y hy
  · obtain ⟨hy1, hy2⟩ := hy
    have e : L.mem (L.wr X b v) (affA y) = L.mem X (affA y) := tw y hy1 3520#u64 (by simp) (by simp)
    exact h.sl y ⟨hy1, e.symm.trans (hy2.trans (L.cpu_wr X b v))⟩ k hk

/-- **`AffAg` at a start state** from the glue's memory link, at a layout with ownership facts (`affAg_of_link`
for `KLayoutP`, at the base layout). -/
theorem affAg_of_linkP {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) {m : U64 → U64} {s : S}
    (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem s x = m x) : AffAg st K.toKLayout m s := by
  intro d hd
  obtain ⟨h1, h2⟩ := (userOK_userV hK.base hU.base).tcb d hd oAFFINITY (Or.inl rfl)
  exact (hμ _ h1 (fun hu => h2 (mem_userV.2 (Or.inl hu)))).symm

end fr

/-! ## The VM-timer path in VM epochs -/

section vt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} {ar : machine.Arch A} {irq n : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
  {m : U64 → U64}

variable (ar) in
/-- **The VM-timer local path at a layout with VCPUs, fire case proved** (module docstring). Premises: `hA`, `hK`,
`hU`, `hm` as every path; `hVU` (`VcpuNU`, from the epoch's bundle), `hTH` (index: `T` are heap TCBs), `hOL`
(`ObjLay`, from `UserLayX.lp`), `hPL` [P], `hEU` (`Pre` kept by user writes, `vtEu_ofV`), `hlk` [P], `hNt`. -/
noncomputable def vtimer_localPathV (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st) (hVU : VcpuNU K) (hTH : ∀ y ∈ T, K.heap y = some .tcb)
    (hOL : ObjLay K.toKLayout H Rp) (hPL : PlanLk lk pl)
    (hEU : ∀ s b v', VtPreV K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n m s → b ∈ K.user → Aligned b →
      VtPreV K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n m (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s)
    (hNt : ∀ q ∈ Nt, H q = some .ntfn) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vtimerBody S irq pl n
  p := R.localvm.handle_vm_timer_irq_local irq pl n
  Acc := fun b => b = true
  Locks := lk
  Pre := VtPreV K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n m
  RS := VexitRS K st lk
  WS := VexitWS K st lk
  DS := IrqDec st
  isProg := PathObl.IsProg.on (vtimer_isProg S irq pl n) _ _ _
  obl := vtimer_pathOblQ (m := m) ar hA hK hU (vtimer_isProg S irq pl n) (vtimer_noZero irq pl n) hm
    (Q := fun s => VtmU K st irq s ∧ VtFx K st T Cs Ω H Sg m s)
    (fun s a s1 a1 hE hQ hf h => by
      by_cases hNW : NoWake st s
      · exact vtimer_acc_fnw_own ar hA hK hNt hE hf hNW h
      · obtain ⟨U, hUs, hbU⟩ := hQ.2.ub
        exact vtimer_acc_fwk_own ar hA hK hNt hE hOL hPL hUs hbU hQ.2.sl hQ.2.pSg hf hNW h)
    (fun s a s1 a1 hE hQ hf h => by
      have hM : ∀ y ∈ T, m (fld y oAFFINITY) = L.mem s (affA y) := fun y hy => hQ.2.aff y (hTH y hy)
      by_cases hNW : NoWake st s
      · exact vtimer_move_fnw ar hA hK hU hNt (vtimer_isProg S irq pl n) (fun _ => rfl) hE hM hf hNW h
      · obtain ⟨U, hUs, hbU⟩ := hQ.2.ub
        exact vtimer_move_fwk ar hA hK hU hNt (vtimer_isProg S irq pl n) (fun _ => rfl) hE hOL hPL hUs hbU
          hQ.2.pSg hM hf hNW h)
    (fun _ _ _ _ hE h => vtimer_dec_own ar hA hK hNt hE h)
  side := vtimer_pathSideQ (m := m) ar hA hK hU (vtimer_isProg S irq pl n) (vtimer_noZero irq pl n) hm
    (Q := fun s => VtmU K st irq s ∧ VtFx K st T Cs Ω H Sg m s)
    (fun s a s1 a1 hE hQ hf h => by
      by_cases hNW : NoWake st s
      · exact vtimer_acc_fnw_own ar hA hK hNt hE hf hNW h
      · obtain ⟨U, hUs, hbU⟩ := hQ.2.ub
        exact vtimer_acc_fwk_own ar hA hK hNt hE hOL hPL hUs hbU hQ.2.sl hQ.2.pSg hf hNW h)
    (fun _ _ _ _ hE h => vtimer_dec_own ar hA hK hNt hE h) hEU hlk
  once := fun s _ a _ hE hAlt _ =>
    vtimer_once_alt ar hA hK hVU hm hE.1 hE.2.1
      (fun s1 a1 hf h => by
        by_cases hNW : NoWake st s
        · exact vtimer_acc_fnw_ownU ar hA hK hVU hNt hE.1 hE.2.1 hf hNW h
        · obtain ⟨U, hUs, hbU⟩ := hE.2.2.ub
          exact vtimer_acc_fwk_ownU ar hA hK hVU hNt hE.1 hE.2.1 hOL hPL hUs hbU hE.2.2.sl hE.2.2.pSg hf hNW h)
      (fun _ _ h => vtimer_dec_ownU ar hA hK hVU hNt hE.1 hE.2.1 h) hAlt
  total := fun s a => by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq pl n LawfulStore.total hA)
    exact ⟨r, e⟩
  masks := hm

end vt

/-! ## The slot -/

section slot
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- The VM-timer path's `Pre` at an index. -/
abbrev VtPreA (i : VtArg S) (K : KLayoutV) (m : U64 → U64) (s : S) : Prop :=
  VtPreV K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.irq i.n m s

/-- **The VM-timer index's sets are the layout's** (index convention, as `VxIx`). -/
structure VtIx (i : VtArg S) (K : KLayoutV) : Prop where
  hKH : K.heap = i.H
  hT : i.T = i.H.tcbs
  hRp : i.Rp = i.H.replies
  hScs : i.Scs = i.H.scs
  hNt : i.Nt = i.H.ntfns
  hZ : i.Z = i.H.scBits
  hCs : i.Cs = {c : U64 | c.val < K.ncores}

/-- **The VM-timer record at a layout with VCPUs** (module docstring). -/
structure VtPremV (i : VtArg S) (K : KLayoutV) : Prop where
  /-- Index convention. -/
  ix : VtIx i K
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- [P] the glue holds the plan's notification / endpoint / reply locks. -/
  PL : PlanLk i.lk i.pl
  /-- The user-word layout facts (from the epoch's `VtxBundle`). -/
  ul : UserLayX L K.toKLayout
  /-- No VCPU word is a user word (from the epoch's `VtxBundle`). -/
  vu : VcpuNU K

variable {st}

theorem VtPremV.th {i : VtArg S} {K : KLayoutV} (h : VtPremV st i K) : ∀ y ∈ i.T, K.heap y = some .tcb :=
  fun y hy => by rw [h.ix.hT, ← h.ix.hKH] at hy; exact hy

theorem VtPremV.ol {i : VtArg S} {K : KLayoutV} (h : VtPremV st i K) : ObjLay K.toKLayout i.H i.Rp := by
  rw [h.ix.hRp, ← h.ix.hKH]
  exact objLay_of_layP h.ul.lp (fun r hr => hr)

theorem VtPremV.nt {i : VtArg S} {K : KLayoutV} (h : VtPremV st i K) : ∀ q ∈ i.Nt, i.H q = some .ntfn :=
  fun q hq => by rw [h.ix.hNt] at hq; exact hq

theorem VtPremV.lkU {i : VtArg S} {K : KLayoutV} (h : VtPremV st i K) :
    ∀ s b v', b ∈ K.user → Aligned b → i.lk (L.wr s b v') = i.lk s :=
  fun s b v' hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.kd s) s b v' trivial
    (mem_userV.2 (Or.inl hb)) hba

/-- **The VM-timer path's `Pre` is kept by aligned user writes** (from `UserLayX` and the index convention). -/
theorem vtEu_ofV {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (h : VtPremV st i K) :
    ∀ s b v', VtPreA st i K m s → b ∈ K.user → Aligned b → VtPreA st i K m (L.wr s b v') := by
  have hCs : ∀ c ∈ i.Cs, c.val < 64 := by
    intro c hc
    rw [h.ix.hCs] at hc
    exact Nat.lt_of_lt_of_le hc h.ul.nc
  have hlk := h.lkU
  have hKH := h.ix.hKH
  have hT := h.ix.hT
  have hRp := h.ix.hRp
  have hScs := h.ix.hScs
  have hNt := h.ix.hNt
  have hZ := h.ix.hZ
  intro s b v hP hb hba
  obtain ⟨hE, hTU, hX⟩ := hP
  have hE' : VtmEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.irq i.n s := hE
  have hX' : VtFx K st i.T i.Cs i.Ω i.H i.Sg m s := hX
  show VtmEnt K st i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.lk i.irq i.n (L.wr s b v) ∧
    (VtmU K st i.irq (L.wr s b v) ∧ VtFx K st i.T i.Cs i.Ω i.H i.Sg m (L.wr s b v))
  rw [hT, hRp, hScs, hNt, hZ, ← hKH] at hE' ⊢
  rw [hT, ← hKH] at hX'
  have h0 := hE'.ent.inv.1.choose_spec.choose_spec
  have hk : L.ksb s = K.ksb := ksb_of_stLay hE'.ent.lay (h0.nodes _ h0.cur)
  have hat : ∀ hi : U64, hi.val < 2048 → atAF K.ksb hi ∉ K.user := fun hi hhi => by
    rw [← hk]; exact (hTU.tabU hi hhi).1
  exact ⟨vtmEnt_wrV h.ul hCs hlk hat hE' hb hba v, vtmU_wrV h.ul.rx hk hTU hb hba v,
    vtFx_wr h.ul hE' hX' hb hba v⟩

variable (st)

/-- **The VM-timer slot at a layout with VCPUs, fire case proved.** -/
def vtSlotV : SlotN (VtArg S) where
  Prem i K _ := VtPremV st i K
  path i K m hK hU h :=
    vtimer_localPathV (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (irq := i.irq) (n := i.n) (pl := i.pl) (m := m) ar hA hK hU hm
      h.vu h.th h.ol h.PL (vtEu_ofV h) h.lkU h.nt

/-- **The VM-timer path at a layout with VCPUs reads no PTE word under `QPs`** (`vt_avoidPJ_path`'s proof with the
fire facts from `Pre`). -/
theorem vt_avoidPV_path (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotV st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vtSlotV st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb)) := by
  have hK' := regionOKV_pteU hK
  have hVU := vcpuNU_pteU hK
  have hP : ∀ s, QPs K st s → VtmP K st i.irq s := fun s hq => vtmP_of_ksb i.irq hq.ks hq.ksb hq.tab
  have hp : VtPremV st i K.toKLayoutV := h
  refine avoidE_of_entry (P := ((vtSlotV st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb))
    (E := (· ∈ K.ptes)) (vtimer_noZero i.irq i.pl i.n) (IsProg.on (vtimer_isProg S i.irq i.pl i.n) _ _ _)
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => VexitWS (L := L) K.pteU st i.lk s)
    (fun s x _ hx => (vexitRSU_pteU (L := L) hx).2.2) ?_
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => vexitRSU_pteU (L := L) hx)
    (fun s x hs hx => by
      obtain ⟨hs1, -⟩ := hs
      exact ((show VtPreA st i K.toKLayoutV m s from hs1).1.ent.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VtPreA st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) := hr
    have hE' := vtmEnt_pteU hK hs'.1 (hP s hq)
    have hTU := vtmU_pteU (hP s hq)
    have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (VexitWS K.pteU st i.lk s))
        ar s a i.irq i.pl i.n = ok (true, s1, a1) :=
      vtimer_acc_ownU ar hA hK' hVU hE' hTU (fun hq => by
        by_cases hNW : NoWake st s
        · exact vtimer_acc_fnw_ownU ar hA hK' hVU hp.nt hE' hTU hq hNW hr'
        · obtain ⟨U, hUs, hbU⟩ := hs'.2.2.ub
          exact vtimer_acc_fwk_ownU ar hA hK' hVU hp.nt hE' hTU hp.ol hp.PL hUs hbU hs'.2.2.sl hs'.2.2.pSg hq hNW
            hr') hr'
    exact g
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VtPreA st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (false, s1, a1) := hr
      have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl i.n = ok (false, s1, a1) :=
        vtimer_dec_ownU ar hA hK' hVU hp.nt (vtmEnt_pteU hK hs'.1 (hP s hq)) (vtmU_pteU (hP s hq)) hr'
      exact g
    · exact absurd rfl hb

/-- **The VM-timer slot's family member reads no PTE word under `QPs`.** -/
theorem vt_avoidPV (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) :
    AvoidP K (((vtSlotV st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  by_cases hp : (vtSlotV st ar hA hm).Prem i K.toKLayoutV m
  · have key : ∀ P, P = (vtSlotV st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
        AvoidP K (P.rJ K (fun b hb => Or.inl hb)) := by
      rintro P rfl
      exact vt_avoidPV_path st ar hA hm i K m hK hU hp
    exact key _ (SlotN.fam_pos _ _ hp)
  · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)

/-- **The VM-timer slot under `ownP`**: restricted to `QPs` states, PTE-cut, lifted. -/
def vtSlotPV : PathsP (VtArg S) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (vt_avoidPV st ar hA hm i K m hK hU)

/-- **The VM-timer record without the bundle's fields**: index convention, `kd` [P], `PL` [P]. -/
structure VtPremV2 (i : VtArg S) (K : KLayoutV) : Prop where
  ix : VtIx i K
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- [P] -/
  PL : PlanLk i.lk i.pl

variable {st}

/-- **`VtPremV` from `VtPremV2` and the epoch's bundle.** -/
theorem VtPremV2.toV {K : KLayoutP} {i : VtArg S} (h : VtPremV2 st i K.toKLayoutV) (E : VtxBundle st L K) :
    VtPremV st i K.toKLayoutV :=
  ⟨h.ix, h.kd, h.PL, E.ul, E.vcpuNU⟩

end slot

/-! ## The start fact and the tops -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The VM-timer slot's start fact** [S] (module docstring): a VM epoch, the record `VtPremV2`, and the glue's
start state with the path's `Pre` (`VtmEnt`, `VtmU`, the fire facts: [S] entry) and `QPs`, its core, locks and
memory link ([P], as `GlueAt`), the armed program the cut of the slot's body there, for the record the epoch's bundle
gives. -/
def VtStartV2 (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64) (hs : U64 → Prop)
    (q : SP) (j : VtArg S) : Prop :=
  K.vcpus ≠ ∅ ∧ ∃ q0, (∃ h : VtPremV2 st j K.toKLayoutV, ∃ (σ : S) (a : A),
      (VtPreA st j K.toKLayoutV m σ ∧ QPs K st σ) ∧ L.cpu σ = c ∧ j.lk σ = hs ∧
      (∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) ∧
      ∀ E : VtxBundle st L K,
        q0 = ((vtSlotV st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toV E)).body σ a) ∧
    q = cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) c q0 ∅

variable {st ar hA hm}

/-- **`StartAt` of the VM-timer slot** from its start fact and the epoch's bundle. -/
theorem vtStartV2_at {K : KLayoutP} {μ : U64 → U64} {hK : RegionOKP K} {hU : UserOKP K} {c : U64}
    {hs : U64 → Prop} {q : SP} {j : VtArg S} (E : VtxBundle st L K) (h : VtStartV2 st ar hA hm K μ hK hU c hs q j) :
    StartAt (vtSlotPV st ar hA hm j K μ hK hU) c hs μ q := by
  obtain ⟨-, q0, ⟨hp, σ, a, he, hc, hl, hμ, hq⟩, rfl⟩ := h
  have key : ∀ (Pf : LocalPath (ownV K.toKLayoutV) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user))
      (hAv : AvoidP K (Pf.rJ K (fun b hb => Or.inl hb))),
      Pf = (vtSlotV st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toV E) →
      StartAt (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv) c hs μ
        (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c q0 ∅) := by
    rintro Pf hAv rfl
    refine ⟨σ, a, he, hc, hl, hμ, ?_⟩
    refine Eq.trans ?_ (body_cutLiftP hK hU (fun x hx => ko_pte hK hx μ) _ hAv σ a).symm
    change _ = cutP _ _ _ _ (((vtSlotV st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toV E)).L.cpu σ)
      (((vtSlotV st ar hA hm).path j K.toKLayoutV μ hK.base hU.base (hp.toV E)).body σ a) ∅
    rw [hc, ← hq E]
  exact key _ _ (SlotN.fam_pos _ _ (hp.toV E))

variable (st ar hA hm)

/-- **Satisfiability of `VtStartV2`**: at any state of a VM epoch with the record, the entry facts ([S]: `VtmEnt`,
`VtmU`, `ub`, `sl`, `pSg`) and `QPs`, and any memory `m` agreeing with it off the user words, the start fact holds
at its core, its locks and the cut body there; the `AffAg` conjunct is derived from the agreement. -/
theorem vtStartV2_sat {K : KLayoutP} (hK : RegionOKP K) (hU : UserOKP K) (hne : K.vcpus ≠ ∅)
    (E0 : VtxBundle st L K) {j : VtArg S} (h : VtPremV2 st j K.toKLayoutV) {σ : S} (a : A) {m : U64 → U64}
    (hE : VtmEnt K.toKLayoutV st j.T j.Cs j.Ω j.H j.Sg j.Rp j.Scs j.Nt j.Z j.Ac j.lk j.irq j.n σ)
    (hTU : VtmU K.toKLayoutV st j.irq σ)
    (hub : ∃ U : Set U64, Fl4Proofs.P1.UserOK st j.T j.Cs j.Ω j.H U σ ∧
      ∀ y ∈ j.T, msg.lookup_ipc_buffer st σ true y ⦃ b => BufOK U b ⦄)
    (hsl : SlotLayV K.toKLayout st j.T σ)
    (hpSg : core.num.U64.wrapping_add (vOf st σ) vcpu.PENDING ∉ j.Sg)
    (hq : QPs K st σ) (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem σ x = m x) :
    VtStartV2 st ar hA hm K m hK hU (L.cpu σ) (j.lk σ)
      (cutP (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (L.cpu σ)
        (((vtSlotV st ar hA hm).path j K.toKLayoutV m hK.base hU.base (h.toV E0)).body σ a) ∅) j :=
  ⟨hne, _, ⟨h, σ, a, ⟨⟨hE, hTU, affAg_of_linkP hK hU hμ, hub, hsl, hpSg⟩, hq⟩, rfl, rfl, hμ, fun _ => rfl⟩, rfl⟩

/-- **The start facts with the VM-exit and VM-timer slots** (VX2S's, the VM-timer slot at `VtStartV2`). -/
def StartVX3 {ιN : Type}
    (SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop)
    (Ch : S → Prop) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (q : SP) : (ιN ⊕ VxArg S) ⊕ VtArg S → Prop
  | .inl i => StartVX2 st ar hA hm SFN Ch K m hK hU c hs q i
  | .inr j => VtStartV2 st ar hA hm K m hK hU c hs q j

/-- **FL4 end to end with native and VM epochs, the VM-exit and VM-timer slots in VM epochs, generic in the native
family** (`serializable_fl4_localVX2SG` with the VM-timer slot added). -/
theorem serializable_fl4_localVX3G (P : LocPlat st arI AR MR) {ιN : Type} (LN : PathsP ιN)
    {SFN : (S → Prop) → ∀ K : KLayoutP, (U64 → U64) → RegionOKP K → UserOKP K → U64 → (U64 → Prop) → SP → ιN → Prop}
    (hSFN : ∀ (Ch : S → Prop) (K : KLayoutP) (s : Cfg U64 U64 U64 U64) (hK : RegionOKP K) (hU : UserOKP K) c hs q i,
      (∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) →
      (∃ s1 : Cfg U64 U64 U64 U64, (K.vcpus = ∅ ∧ K.ptes = ptesR K s1.mem) ∧ ∀ x, GateW K x → s.mem x = s1.mem x) →
      SFN Ch K s.mem hK hU c hs q i → StartAt (LN i K s.mem hK hU) c hs s.mem q)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX2 (PathsP.sum (PathsP.sum LN (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm))
      (StartVX3 st ar hA hm SFN) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R hB hc0
  have hX := (execVX_of_VX2 hc0.1 h).1
  refine serializable_e2eP _ h0 hA0 hK0 hU0 hM0 (execP_of_VX P ?_ h0 hA0 hB hc0 hM0 hX).1 hq
  intro Ch K s hK hU c hs q i hN hsf
  obtain ⟨hV, hsf⟩ := hsf
  rcases i with (i | j) | j
  · have hsf' : K.vcpus = ∅ ∧ SFN Ch K s.mem hK hU c hs q i := hsf
    obtain ⟨nv, hsf'⟩ := hsf'
    obtain ⟨hX, hE⟩ := hN nv
    exact hSFN Ch K s hK hU c hs q i hX.chainOf hE hsf'
  · have hsf' : VxStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vxStartV_at st ar hA hm (vxStartV_of_V2 (hV (vxStartV2_ne hsf')) hsf')
  · have hsf' : VtStartV2 st ar hA hm K s.mem hK hU c hs q j := hsf
    exact vtStartV2_at (hV hsf'.1) hsf'

/-- **FL4 end to end with every U1 slot, a real VM exit and the VM timer with its fire case in VM epochs** (module
docstring): `serializable_fl4_localVX2S` with the VM-timer slot `vtSlotPV` added; its start fact `VtStartV2` ([S]
entry facts, record `VtPremV2`: index convention, `kd` / `PL` [P]). No [W]; no new [J]. -/
theorem serializable_fl4_localVX2 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : S → Prop} (h0 : Init s0) (hA0 : ArmInv s0)
    (hB : SerExitW P K0.toKLayoutV Ch0) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecVX2 (PathsP.sum (PathsP.sum (PathsP.sum (fl4LocW11JA st ar hA hm hSt a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA hm) (invSlotU st ar hA hm)) (cmSlotU st ar hA hm)))
        (vxSlotPV st ar hA hm)) (vtSlotPV st ar hA hm))
      (StartVX3 st ar hA hm (StartU1 st ar hA hm hSt a0 arI AR MR (StartInvU2 st ar hA hm))) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  refine serializable_fl4_localVX3G st ar hA hm P _ ?_ h0 hA0 hB hc0 hM0 h hq
  intro Ch K s hK hU c hs q i hC hE hsf
  rcases i with i | ((j | j) | j)
  · exact startAt_U st ar hA hm hSt a0 P hIoa hC hE hsf
  · exact delPteStart_at st ar hA hm hC hE hsf
  · exact invStartU2_at st ar hA hm hC hE hsf
  · exact cmStartU2_at st ar hA hm hC hE hsf

end top

end
end Fl4Proofs.P2.E2EP
