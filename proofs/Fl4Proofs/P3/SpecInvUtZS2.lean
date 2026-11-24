/-
P3 (DESIGN.md §9), invariant line G1 (g5h, KENTRY-PLAN g5h): **the perform /
shell half of `ZR` (l4v `untyped_ranges_zero` with `valid_untyped` for data
pages)**, g5g's proofs/scratch/g5g/S.tail.lean restructured (spec side only;
outside the `JAtZ` cone).

g5g's tail ran `zr_auto` across whole performs and decodes (every node tried
`ik_zr` with every `hv_leaf` / `yk_leaf` rule before unfolding). Here every
function is split once at its top, `zr_split`: `ik_zr` / `ike_zr` with the
cap half by `hv_auto` and the memory half by `yk_auto` separately, each of
which meets its existing leaf lemma at once.

* `zr_pin`: `ZR` kept given the cap half at the state's own sets and the
  memory half; `utIn_of_view`, `utIn_ci3`, `utIn_refEq`: ut7's CNode decode
  facts (`CnOKN`: an inserted / moved cap is the source slot's or no untyped
  cap) give `UtIn U` of the written caps.
* The performs: `zr_invokeCnode` (`CnOKN`), `zr_invokeIrqHandler` (`IrqHOKN`:
  a notification cap), `hu_invokeTcb` (the installs re-read their source,
  `hu_checkCapAt_ins`), the others by `zr_split`; `zr_fl4Perform` per
  invocation kind, the untyped perform by `PerfGapZ`.
* `PerfGapZ` (the untyped perform; a ∀-states obligation, not a premise of
  any invariant top), `IKZ` (`ZR` from `P3 N ∧ NodeIs N ∧ ZR`) and its binds.
* SpecInvUtZS3: the shell `zr_handleInvocationR` (ut7's
  `p3N_handleInvocationR` with `ZR`); SpecInvUtZS4: the syscalls
  `zr_fl4HandleSyscall` (per syscall), the events, the entry: `kentry_zr_of`,
  `kcall_zr_of` (given `PerfGapZ`), `kcall_zr_other`, `zr_fl4SyscallFaultIP`
  (no premise).
-/
import Fl4Proofs.P3.SpecInvUtZS
open Classical

namespace Fl4Proofs.P3.SInvUZ
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvU

noncomputable section

set_option maxHeartbeats 1000000

/-- `ZR` of a function: the cap half by `hv_auto`, the memory half by `yk_auto`. -/
macro "zr_split" : tactic => `(tactic| first
  | ((with_reducible refine ike_zr (fun _ => ?_) (fun _ _ => ?_)); (focus (hv_auto; done)); (yk_auto; done))
  | ((with_reducible refine ik_zr (fun _ => ?_) (fun _ _ => ?_)); (focus (hv_auto; done)); (yk_auto; done)))

/-! ## Pinned form and the written caps -/

theorem zr_pin {α : Type} {m : NonDet (State Unit) α} {σ : State Unit} (hZ : ZR σ)
    (hH : ∀ U, HU U σ → ∀ y ∈ (m σ).1, HU U y.2) (hY : ∀ D F, YK D F m) : ∀ y ∈ (m σ).1, ZR y.2 := by
  obtain ⟨U, D, hG, hU, hP⟩ := hZ
  intro y hy
  exact ⟨U, D, hG, hH U hU y hy, hY D (FU U) σ hP y hy⟩

theorem utIn_of_view {U : UtSet} {σ : State Unit} (h : HU U σ) {sl : CslotPtr} {c : Cap}
    (hc : (uV σ).2.1 sl = some c) : UtIn U c := by
  have h1 : SInvU.capAt σ sl = some c := hc
  rw [capAt_capOpt] at h1
  exact utIn_of_slot h h1

theorem utIn_ci3 {U : UtSet} {σ : State Unit} (h : HU U σ) {c : Cap} {src : CslotPtr}
    (hc : CI3 (uV σ) c src) : UtIn U c := by
  obtain ⟨c0, hs, hc⟩ := hc
  rcases hc with ⟨e, -⟩ | hR
  · subst e; exact utIn_of_view h hs
  · exact utIn_noUt (fun b n f => hR.2.2.2.2 false b n f) U

theorem utIn_refEq {U : UtSet} {σ : State Unit} (h : HU U σ) {s : CslotPtr} {c0 c : Cap}
    (hs : (uV σ).2.1 s = some c0) (hR : RefEq c0 c) : UtIn U c := by
  rcases hR with e | hR
  · subst e; exact utIn_of_view h hs
  · exact utIn_noUt (fun b n f => hR.2.2.2.2.2.1 false b n f) U

/-! ## The performs -/

set_option maxHeartbeats 4000000 in
theorem zr_invokeCnode (ci : CnodeInvocation) (σ : State Unit) (hZ : ZR σ) (hok : CnOKN (uV σ) ci) :
    ∀ y ∈ ((invokeCnode (Z := Unit) ci).run σ).1, ZR y.2 := by
  refine zr_pin hZ (fun U hU => ?_) (fun D F => yk_invokeCnode ci)
  cases ci with
  | insertCall c s d =>
    have hc : UtIn U c := utIn_ci3 hU hok.1
    have k : IKHE (ε := Unit) (HU U) (invokeCnode (Z := Unit) (.insertCall c s d)) := by
      simp only [invokeCnode]; hv_auto
    exact k σ hU
  | moveCall c s d =>
    obtain ⟨c0, hs, -, hR, -⟩ := hok
    have hc : UtIn U c := utIn_refEq hU hs hR
    have k : IKHE (ε := Unit) (HU U) (invokeCnode (Z := Unit) (.moveCall c s d)) := by
      simp only [invokeCnode]; hv_auto
    exact k σ hU
  | rotateCall c1 c2 s1 s2 s3 =>
    obtain ⟨c1', c2', h1, h2, hR1, -, hR2, -⟩ := hok
    have hc1 : UtIn U c1 := utIn_refEq hU h1 hR1
    have hc2 : UtIn U c2 := utIn_refEq hU h2 hR2
    have k : IKHE (ε := Unit) (HU U) (invokeCnode (Z := Unit) (.rotateCall c1 c2 s1 s2 s3)) := by
      simp only [invokeCnode]; split <;> hv_auto
    exact k σ hU
  | revokeCall s => exact hu_capRevoke s σ hU
  | deleteCall s => exact hu_capDelete s σ hU
  | cancelBadgedSendsCall c =>
    have k : IKHE (ε := Unit) (HU U) (invokeCnode (Z := Unit) (.cancelBadgedSendsCall c)) := by
      simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> hv_auto
    exact k σ hU

set_option maxHeartbeats 4000000 in
theorem zr_invokeIrqHandler (i : IrqHandlerInvocation) (σ : State Unit) (hZ : ZR σ)
    (hok : InvOKN (uV σ) (.invokeIRQHandler i)) :
    ∀ y ∈ (invokeIrqHandler (Z := Unit) i σ).1, ZR y.2 := by
  refine zr_pin hZ (fun U hU => ?_) (fun D F => yk_invokeIrqHandler i)
  cases i with
  | setIRQHandler irq c sl =>
    have hn : isNtfnCap c = true := hok.2.2
    have hc : UtIn U c := utIn_noUt (fun b n f e => by subst e; simp [isNtfnCap] at hn) U
    have k : IKH (HU U) (invokeIrqHandler (Z := Unit) (.setIRQHandler irq c sl)) := by
      simp only [invokeIrqHandler]; hv_auto
    exact k σ hU
  | aCKIrq irq =>
    have k : IKH (HU U) (invokeIrqHandler (Z := Unit) (.aCKIrq irq)) := by
      simp only [invokeIrqHandler]; hv_auto
    exact k σ hU
  | clearIRQHandler irq =>
    have k : IKH (HU U) (invokeIrqHandler (Z := Unit) (.clearIRQHandler irq)) := by
      simp only [invokeIrqHandler]; hv_auto
    exact k σ hU

set_option maxHeartbeats 4000000 in
/-- The TCB invocations: every install re-reads its source slot (`hu_checkCapAt_ins`). -/
theorem hu_invokeTcb {U : UtSet} (i : TcbInvocation) : IKHE (HU U) (invokeTcb (Z := Unit) i) := by
  cases i <;> simp only [invokeTcb] <;> hv_auto

theorem zr_invokeTcb (i : TcbInvocation) : IKHE ZR (invokeTcb (Z := Unit) i) :=
  ike_zr (fun _ => hu_invokeTcb i) (fun _ _ => yk_invokeTcb i)

set_option maxHeartbeats 4000000 in
theorem zrp_endpoint (blk call don : Bool) (ep : ObjRef) (b : Word) (g gr : Bool) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeEndpoint ep b g gr)) := by
  simp only [fl4PerformInvocation]; zr_split

set_option maxHeartbeats 4000000 in
theorem zrp_notification (blk call don : Bool) (ep : ObjRef) (b : Word) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeNotification ep b)) := by
  simp only [fl4PerformInvocation]; zr_split

set_option maxHeartbeats 4000000 in
theorem zrp_domain (blk call don : Bool) (d : DomainInvocation) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeDomain d)) := by
  simp only [fl4PerformInvocation]; zr_split

set_option maxHeartbeats 4000000 in
theorem zrp_reply (blk call don : Bool) (r : ObjRef) (g : Bool) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeReply r g)) := by
  simp only [fl4PerformInvocation]; zr_split

set_option maxHeartbeats 4000000 in
theorem zrp_irqControl (blk call don : Bool) (i : Fl4IrqControlInvocation) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeIRQControl i)) := by
  simp only [fl4PerformInvocation]; zr_split

set_option maxHeartbeats 4000000 in
theorem zrp_schedContext (blk call don : Bool) (i : SchedContextInvocation) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedContext i)) := by
  simp only [fl4PerformInvocation]; zr_split

set_option maxHeartbeats 4000000 in
theorem zrp_schedControl (blk call don : Bool) (i : SchedControlInvocation) :
    IKHE ZR (fl4PerformInvocation (Z := Unit) blk call don (.invokeSchedControl i)) := by
  simp only [fl4PerformInvocation]; zr_split

/-! ## `zr_fl4Perform` -/

/-- **The remaining obligation** (not an invariant premise): the untyped
perform keeps `ZR` for an invocation decoded from the state's view. -/
def PerfGapZ : Prop :=
  ∀ (N : Irq → ObjRef) (ui : UntypedInvocation) (σ : State Unit), P3 N σ → NodeIs N σ → ZR σ →
    DecodedFrom (uV σ) (.invokeUntyped ui) → ∀ y ∈ ((fl4InvokeUntyped (Z := Unit) ui).run σ).1, ZR y.2

variable {N : Irq → ObjRef}

set_option maxHeartbeats 4000000 in
theorem zr_fl4Perform (hG : PerfGapZ) (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit)
    (hP : P3 N σ) (hN : NodeIs N σ) (hZ : ZR σ) (hI : InvZ (uV σ) inv) (hO : InvOKN (uV σ) inv)
    (hD : DecodedFrom (uV σ) inv) :
    ∀ y ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, ZR y.2 := by
  intro y hy
  cases inv with
  | invokeUntyped ui =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]; exact hG N ui σ hP hN hZ hD z hz
  | invokeFl4TCB i =>
    simp only [fl4PerformInvocation] at hy
    exact zr_invokeFl4Tcb i σ hZ hP.1.2.2.2.1 hI y hy
  | invokeCNode ci =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]; exact zr_invokeCnode ci σ hZ hO z hz
  | invokeIRQHandler i =>
    simp only [fl4PerformInvocation] at hy
    obtain ⟨z, hz, e⟩ := mem_ret_bindE hy
    rw [e]
    obtain ⟨x, hx, rfl⟩ := mem_liftE' hz
    exact zr_invokeIrqHandler i σ hZ hO x hx
  | invokeArchObject fa =>
    simp only [fl4PerformInvocation] at hy
    cases fa with
    | tdx i => exact zr_tdx i σ hZ hP.1.2.2.2.1 hI y hy
    | _ =>
      exact ike_zr (fun _ => hu_fl4ArchPerformInvocation _)
        (fun _ _ => yk_fl4ArchPerformInvocation _ (fun _ h => by cases h)) σ hZ y hy
  | invokeTCB i =>
    simp only [fl4PerformInvocation] at hy
    exact zr_invokeTcb i σ hZ y hy
  | invokeEndpoint ep b g gr => exact zrp_endpoint blk call don ep b g gr σ hZ y hy
  | invokeNotification ep b => exact zrp_notification blk call don ep b σ hZ y hy
  | invokeDomain d => exact zrp_domain blk call don d σ hZ y hy
  | invokeReply r g => exact zrp_reply blk call don r g σ hZ y hy
  | invokeIRQControl i => exact zrp_irqControl blk call don i σ hZ y hy
  | invokeSchedContext i => exact zrp_schedContext blk call don i σ hZ y hy
  | invokeSchedControl i => exact zrp_schedControl blk call don i σ hZ y hy

/-! ## The invocation shell -/

/-- `ZR` kept from a `P3 N ∧ NodeIs N ∧ ZR` state. -/
def IKZ {α : Type} (m : NonDet (State Unit) α) : Prop :=
  ∀ (N : Irq → ObjRef) σ, P3 N σ → NodeIs N σ → ZR σ → ∀ y ∈ (m σ).1, ZR y.2

abbrev IKZE {ε α : Type} (m : NonDetE (State Unit) ε α) : Prop := IKZ (ExceptT.run m)

theorem ikz_of_ik {α : Type} {m : NonDet (State Unit) α} (h : IKH ZR m) : IKZ m :=
  fun _ σ _ _ hZ y hy => h σ hZ y hy

theorem ikze_bind_uk {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : ∀ v, UKE v m) (hmN : ∀ N, NKE N m) (hmZ : IKHE ZR m) (hg : ∀ a, IKZE (g a)) : IKZE (m >>= g) := by
  intro N σ hI hN hZ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a N z.2 (p3_of_view (hm (uV σ) σ rfl z hz) hI) (hmN N σ hN z hz) (hmZ σ hZ z hz) y hy
  · exact hmZ σ hZ z hz

theorem ikze_bind {ε α β : Type} {m : NonDetE (State Unit) ε α} {g : α → NonDetE (State Unit) ε β}
    (hm : IKZE m) (hg : ∀ a, IKHE ZR (g a)) : IKZE (m >>= g) := by
  intro N σ hI hN hZ y hy
  obtain ⟨z, hz, ⟨a, ha, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE' hy
  · exact hg a z.2 (hm N σ hI hN hZ z hz) y hy
  · exact hm N σ hI hN hZ z hz

theorem ikz_bind_post {α β : Type} {m : NonDet (State Unit) α} {g : α → NonDet (State Unit) β}
    (hm : IKZ m) (hg : ∀ a, IKH ZR (g a)) : IKZ (m >>= g) := by
  intro N σ hI hN hZ y ⟨x, hx, hy⟩
  exact hg x.1 x.2 (hm N σ hI hN hZ x hx) y hy

theorem zr_restart (thread : ObjRef) :
    IKHE (ε := Unit) ZR (withoutPreemption (Z := Unit) (setThreadState thread .restart)) := by
  zr_split

set_option maxHeartbeats 4000000 in
theorem zr_hiFront (thread : ObjRef) (cptr : CapRef) (info : MessageInfo) :
    IKHE (ε := Fault) ZR (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer)) := by
  zr_split

set_option maxHeartbeats 4000000 in
theorem zr_hiDecode (thread : ObjRef) (fp : Bool) (info : MessageInfo) (cptr : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) :
    IKHE ZR (do
        let args ← NonDetE.liftE <| getMrs (Z := Unit) thread buf info
        fl4DecodeInvocation fp info.miLabel args cptr sl cap ex buf) := by
  zr_split


end

end Fl4Proofs.P3.SInvUZ
