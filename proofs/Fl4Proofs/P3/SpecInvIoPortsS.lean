/-
P3 (DESIGN.md §9), invariant line G1 (g5c, KENTRY-PLAN g5c): **l4v
`valid_ioports` ∧ `ioports_no_overlap` across the whole kernel entry** (spec
side only; outside the `JAtZ` cone; vih3's SpecInvValidIrqHandlersS with
`IOI` for `VI`).

* The decode's carry (l4v: the caps of `decode_invocation`'s result are
  `cte_wp_at` / `valid_cap` facts at the perform): `InvIo σ inv` — the caps a
  CNode invocation writes and the set-handler cap are caps of `σ` (`IoIn (Has
  σ)`), an unmap's slot holds its cap (`AtSl`), and an IO port control issue's
  range is well formed and free (`is_ioport_range_free`). `okd_fl4Decode_io`;
  `invIo_of` transports it across steps keeping the caps and the allocated
  ports (`set_thread_state Restart`).
* `ioi_ioCtl`: the issue (`set_ioport_mask f l True`, then `cap_insert
  (IOPortCap f l)`) keeps `IOI`: the new range is allocated and, being free
  before, overlaps no existing cap.
* The performs (`ioi_fl4Perform`), the shell `ioi_handleInvocationR`, the
  syscalls, every event, `fl4CallKernel`, the syscall entry.
* **`ioi_fl4KernelEntrySyscall`** / **`ioi_fl4CallKernel`**: `IOI` across
  `fl4KernelEntrySyscall rep c` / `fl4CallKernel rep ev` (every event) with no
  side condition; `boot_IOI` at the spec's initial state. The statements over
  g5a's `SpecIoP` (`ioi_iff`, `kentry_ioi`, `kcall_ioi`, `boot_ioi`) are in
  XTopJointKEntry37E (SpecInvG5's namespace is kept out of this module).
-/
import Fl4Proofs.P3.SpecInvIoPortsX
import Fl4Proofs.P3.SpecFbQ
open Classical

namespace Fl4Proofs.P3.SInvIo
open Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.SInv Fl4Proofs.P3.SInvV Fl4Proofs.P3.SInvDom

noncomputable section

set_option maxHeartbeats 1000000

macro_rules | `(tactic| ioi_leaf) => `(tactic| hv_leaf)
macro_rules | `(tactic| ioi_leaf) => `(tactic| iok_leaf)

/-! ## The decode's carry -/

/-- The caps a CNode invocation writes are in `S`. -/
def CnIo (S : IoSet) (i : CnodeInvocation) : Prop :=
  match i with
  | .insertCall c _ _ => IoIn S c
  | .moveCall c _ _ => IoIn S c
  | .rotateCall c1 c2 _ _ _ => IoIn S c1 ∧ IoIn S c2
  | _ => True

/-- The facts an arch invocation needs at its perform. -/
def ArchIo (σ : State Unit) (ai : ArchInvocation) : Prop :=
  match ai with
  | .invokePage (.pageUnmap c sl) => AtSl sl (.archObjectCap c) σ
  | .invokePageTable (.pageTableUnmap c sl) => AtSl sl c σ
  | .invokePageDirectory (.pageDirectoryUnmap c sl) => AtSl sl c σ
  | .invokePDPT (.pdptUnmap c sl) => AtSl sl c σ
  | .invokeIOPortControl (.ioPortControlInvocation f l _ _) => f ≤ l ∧ ∀ q, f ≤ q → q ≤ l → ioA σ q = false
  | _ => True

/-- The facts an invocation needs at its perform. -/
def InvIo (σ : State Unit) (inv : Fl4Invocation) : Prop :=
  match inv with
  | .invokeCNode i => CnIo (Has σ) i
  | .invokeIRQHandler (.setIRQHandler _ c _) => IoIn (Has σ) c
  | .invokeArchObject (.spec ai) => ArchIo σ ai
  | _ => True

theorem atSl_of {sl : CslotPtr} {c : Cap} {σ σ' : State Unit} (e : hV σ' = hV σ) (h : AtSl sl c σ) :
    AtSl sl c σ' := by unfold AtSl; rw [hV_cap e]; exact h

theorem archIo_of {σ σ' : State Unit} (e : hV σ' = hV σ) (ea : ioA σ' = ioA σ) {ai : ArchInvocation}
    (h : ArchIo σ ai) : ArchIo σ' ai := by
  cases ai with
  | invokePage i => cases i <;> first | trivial | exact atSl_of e h
  | invokePageTable i => cases i <;> first | trivial | exact atSl_of e h
  | invokePageDirectory i => cases i <;> first | trivial | exact atSl_of e h
  | invokePDPT i => cases i <;> first | trivial | exact atSl_of e h
  | invokeIOPortControl i =>
    cases i
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, fun q a b => by rw [ea]; exact h2 q a b⟩
  | _ => trivial

theorem invIo_of {σ σ' : State Unit} (e : hV σ' = hV σ) (ea : ioA σ' = ioA σ) {inv : Fl4Invocation}
    (h : InvIo σ inv) : InvIo σ' inv := by
  have eh := has_of_hV e
  cases inv with
  | invokeCNode i => show CnIo (Has σ') i; rw [eh]; exact h
  | invokeIRQHandler i =>
    cases i with
    | setIRQHandler irq c sl => show IoIn (Has σ') c; rw [eh]; exact h
    | _ => trivial
  | invokeArchObject fa =>
    cases fa with
    | spec ai => exact archIo_of e ea h
    | _ => trivial
  | _ => trivial

theorem ioIn_maskCap {S : IoSet} {c : Cap} (h : IoIn S c) (r : CapRights) : IoIn S (maskCap r c) := by
  intro f l e; apply h f l
  cases c <;> simp_all [maskCap, capRightsUpdate]
  all_goals first | done | (rename_i a; cases a <;> simp_all [acapRightsUpdate])

theorem ioIn_updateCapData {S : IoSet} {c : Cap} (h : IoIn S c) (p : Bool) (w : Data) :
    IoIn S (updateCapData p w c) := by
  intro f l e; apply h f l
  unfold updateCapData at e
  split_ifs at e <;> first
    | (cases c <;> simp_all [badgeUpdate]; done)
    | (cases e; done)
    | (simp only [archUpdateCapData] at e; cases c <;> simp_all [isArchCap, Cap.theArchCap]; done)
    | (cases c <;> simp_all; done)
    | (dsimp only at e; split_ifs at e <;> cases e)
    | exact e

theorem okv_getCap_io {S : IoSet} {σ0 : State Unit} (hv : HI S σ0) (sl : CslotPtr) :
    OkV σ0 (fun c => IoIn S c) (NonDetE.liftE (ε := SyscallError) (getCap (Z := Unit) sl)) := by
  intro s hs a s' h
  obtain ⟨y, hy, e⟩ := mem_liftE_inv' h
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  obtain ⟨o, r⟩ := sl
  obtain ⟨e1, e2⟩ := vih_mem_getCap hy
  rw [e1]
  exact ⟨hs, ioIn_of_slot (hi_of_hV hs hv) e2⟩

theorem okv_deriveCap_io {S : IoSet} {σ0 : State Unit} (sl : CslotPtr) (c : Cap) (hc : IoIn S c) :
    OkV σ0 (fun c' => IoIn S c') (deriveCap (Z := Unit) sl c) := by
  intro s hs a s' h
  have e : hV s' = hV s := hv_deriveCap (P := fun x => hV x = hV s) _ _ s rfl _ h
  exact ⟨e.trans hs, ioIn_deriveCap hc h⟩

macro "io_cn_close" : tactic => `(tactic| first
  | assumption
  | (refine ioIn_updateCapData (ioIn_maskCap ?_ _) _ _; assumption)
  | (refine ioIn_maskCap ?_ _; assumption)
  | (refine ioIn_updateCapData ?_ _ _; assumption)
  | (split <;> first
      | assumption
      | (refine ioIn_updateCapData (ioIn_maskCap ?_ _) _ _; assumption)
      | (refine ioIn_maskCap ?_ _; assumption)
      | (refine ioIn_updateCapData ?_ _ _; assumption)))

set_option maxHeartbeats 4000000 in
theorem okv_decodeCnode_io {S : IoSet} {σ0 : State Unit} (hv : HI S σ0) (label : Data) (args : List Data)
    (cap : Cap) (excaps : List Cap) :
    OkV σ0 (fun i => CnIo S i) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  unfold decodeCnodeInvocation
  repeat' (first
    | (refine okv_bind (okv_getCap_io hv _) fun c0 hc0 => ?_)
    | (refine okv_bind (okv_ite_app _ (okv_returnOk ?_) (okv_deriveCap_io (S := S) _ _ ?_)) fun c1 hc1 => ?_)
    | okv_step)
  all_goals first
    | (refine okv_returnOk ?_; simp only [CnIo]; io_cn_close; done)
    | (refine okv_returnOk ?_; simp only [CnIo]; constructor <;> io_cn_close; done)
    | io_cn_close

theorem okd_decodeCnode_io (label : Data) (args : List Data) (cap : Cap) (excaps : List Cap) (s : State Unit) :
    OkDAt s (fun s' i => InvIo s' (.invokeCNode i)) (decodeCnodeInvocation (Z := Unit) label args cap excaps) := by
  intro a s' h
  have e : hV s' = hV s := hv_decodeCnodeInvocation (P := fun x => hV x = hV s) _ _ _ _ s rfl _ h
  have hc := (okv_decodeCnode_io (S := Has s) (fun _ _ h => h) label args cap excaps s rfl a s' h).2
  show CnIo (Has s') a
  rw [has_of_hV e]; exact hc

theorem okd_decodeIrqHandler_io (label : Data) (irq : Irq) (cps : List (Cap × CslotPtr)) (s : State Unit) :
    OkDAt s (fun s' v => InvIo s' (.invokeIRQHandler v)) (decodeIrqHandlerInvocation (Z := Unit) label irq cps) := by
  unfold decodeIrqHandlerInvocation
  repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk trivial
    | exact okdAt_returnOk (ioIn_noIo (fun f l e => by simp_all [isNtfnCap]) _)
    | split)

/-- `when_E c (throw e)` then a continuation from `¬ c`. -/
theorem okdAt_whenE_throw {ε β : Type} {σ : State Unit} {P : State Unit → β → Prop} (c : Prop) [Decidable c]
    (e : ε) {k : Unit → NonDetE (State Unit) ε β} (h : ¬ c → OkDAt σ P (k ())) :
    OkDAt σ P (NonDetE.whenE c (NonDetE.throwError e) >>= k) := by
  unfold NonDetE.whenE
  split
  · exact okdAt_bind fun a s hs => (okdAt_throw (P := fun _ _ => False) e a s hs).elim
  · rename_i hc
    refine okdAt_bind fun a s hs => ?_
    have : ((.ok a, s) : Except ε Unit × State Unit) = (.ok (), σ) := Set.mem_singleton_iff.1 hs
    simp only [Prod.mk.injEq] at this
    obtain ⟨-, rfl⟩ := this
    exact h hc

theorem okdAt_liftE_fail {ε α : Type} {σ : State Unit} {P : State Unit → α → Prop} :
    OkDAt σ P (NonDetE.liftE (ε := ε) (NonDet.fail : NonDet (State Unit) α)) := by
  intro a s h
  obtain ⟨y, hy, -⟩ := mem_liftE_inv' h
  exact hy.elim

theorem okdAt_pure' {ε α : Type} {σ : State Unit} {P : State Unit → α → Prop} {v : α} (h : P σ v) :
    OkDAt σ P (pure v : NonDetE (State Unit) ε α) := by
  intro a s hb
  rw [ExceptT.run_pure] at hb
  have e := Set.mem_singleton_iff.1 hb
  simp only [Prod.mk.injEq, Except.ok.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  exact h

theorem okd_ioCtl (label : Data) (args : List Data) (slot : CslotPtr) (cap : ArchCap) (ex : List Cap)
    (s0 s : State Unit) :
    OkDAt s (fun s' ai => hV s' = hV s0 → ArchIo s' ai)
      (decodeIoportControlInvocation (Z := Unit) label args slot cap ex) := by
  unfold decodeIoportControlInvocation
  split
  · split
    · dsimp only
      refine okdAt_whenE_throw _ _ fun hfl => ?_
      refine okdAt_bind fun chk s1 h1 => ?_
      obtain ⟨y, hy, e⟩ := mem_liftE_inv' h1
      simp only [Prod.mk.injEq, Except.ok.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      unfold isIoportRangeFree at hy
      obtain ⟨z, hz, hy⟩ := hy
      obtain rfl := Set.mem_singleton_iff.1 hz
      obtain rfl := Set.mem_singleton_iff.1 hy
      refine okdAt_whenE_throw _ _ fun hchk => ?_
      intro a s' h _
      have hv : ∃ d, a = .invokeIOPortControl (.ioPortControlInvocation (ucast 16 (the args[0]?))
          (ucast 16 (the args[1]?)) d slot) :=
        (okdAt_bind fun d _ _ => okdAt_bind fun _ _ _ => okdAt_returnOk ⟨d, rfl⟩ :
          OkDAt s (fun _ a => ∃ d, a = .invokeIOPortControl (.ioPortControlInvocation (ucast 16 (the args[0]?))
            (ucast 16 (the args[1]?)) d slot)) _) a s' h
      have ea : ioA s' = ioA s := (by iok_auto : IoKE (ioA s) _) s rfl _ h
      obtain ⟨d, rfl⟩ := hv
      have hE := of_decide_eq_true (Classical.not_not.1 hchk)
      refine ⟨BitVec.not_lt.1 hfl, fun q h1 h2 => ?_⟩
      rw [ea]
      cases hq : s.archState.x64AllocatedIoPorts q
      · exact hq
      · exfalso
        have hm : q ∈ ({x | ucast 16 (the args[0]?) ≤ x ∧ x ≤ ucast 16 (the args[1]?)} ∩
            {x | s.archState.x64AllocatedIoPorts x = true} : Set IoPort) := ⟨⟨h1, h2⟩, hq⟩
        rw [hE] at hm; exact hm
    · exact okdAt_throw _
  · exact okdAt_throw _

set_option maxHeartbeats 4000000 in
/-- The unmaps' results name the invoked slot and cap. -/
theorem okd_archDecode_io (label : Data) (args : List Data) (x : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (s0 : State Unit) (hat : AtSl cte (.archObjectCap cap) s0) (s : State Unit) :
    OkDAt s (fun s' ai => hV s' = hV s0 → ArchIo s' ai) (archDecodeInvocation (Z := Unit) label args x cte cap ex) := by
  unfold archDecodeInvocation
  split
  all_goals try unfold decodePdptInvocation
  all_goals try unfold decodePageDirectoryInvocation
  all_goals try unfold decodePageTableInvocation
  all_goals try unfold decodePageInvocation
  all_goals try unfold decodePortInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okd_ioCtl _ _ _ _ _ _ _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_returnOk (fun e => atSl_of e hat)
    | exact okdAt_liftE_fail
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split
    | dsimp only)

set_option maxHeartbeats 4000000 in
theorem okd_fl4ArchDecode_io (label : Data) (args : List Data) (x : CapRef) (cte : CslotPtr) (cap : ArchCap)
    (ex : List (Cap × CslotPtr)) (s0 : State Unit) (hat : AtSl cte (.archObjectCap cap) s0) (σ : State Unit) :
    OkDAt σ (fun s' fa => hV s' = hV s0 → InvIo s' (.invokeArchObject fa))
      (fl4ArchDecodeInvocation (Z := Unit) label args x cte cap ex) := by
  unfold fl4ArchDecodeInvocation
  repeat' (first
    | exact okdAt_liftME (okd_archDecode_io _ _ _ _ _ _ s0 hat σ)
    | exact okdAt_liftME (fun _ _ _ _ => trivial)
    | (apply okdAt_ite)
    | split)

set_option maxHeartbeats 4000000 in
theorem okd_fl4Decode_io (fp : Bool) (label : Data) (args : List Data) (ci : CapRef) (sl : CslotPtr) (cap : Cap)
    (ex : List (Cap × CslotPtr)) (buf : Option ObjRef) (s0 : State Unit) (hat : AtSl sl cap s0) (σ : State Unit) :
    OkDAt σ (fun s' inv => hV s' = hV s0 → InvIo s' inv)
      (fl4DecodeInvocation (Z := Unit) fp label args ci sl cap ex buf) := by
  unfold fl4DecodeInvocation
  split
  all_goals try unfold fl4DecodeTcbInvocation
  all_goals repeat' (first
    | exact okdAt_throw _
    | exact okdAt_returnOk (fun _ => trivial)
    | exact okdAt_liftME (fun a s h _ => okd_decodeCnode_io _ _ _ _ _ a s h)
    | exact okdAt_liftME (fun a s h _ => okd_decodeIrqHandler_io _ _ _ _ _ a s h)
    | exact okdAt_liftME (okd_fl4ArchDecode_io _ _ _ _ _ _ s0 hat σ)
    | exact okdAt_liftME (fun _ _ _ _ => trivial)
    | exact okdAt_pure' (fun _ => okd_decodeIrqHandler_io _ _ _ _ _ _ (by assumption))
    | exact okdAt_pure' (fun _ => okd_decodeCnode_io _ _ _ _ _ _ _ (by assumption))
    | exact okdAt_pure' (fun _ => trivial)
    | (apply okdAt_ite)
    | (refine okdAt_bind fun _ _ _ => ?_)
    | split)

/-! ## The performs -/

/-- `IKp` of `VS S` from the cap half pinned at a state and the allocated ports. -/
theorem ikp_vs {S : IoSet} {α : Type} {m : NonDet (State Unit) α} {σ : State Unit} (hH : IKp (HI S) σ m)
    (hI : ∀ a, IoK a m) : IKp (VS S) σ m := by
  intro h x hx
  have h2 : ioA x.2 = ioA σ := hI (ioA σ) σ rfl x hx
  exact ⟨hH h.1 x hx, by rw [h2]; exact h.2⟩

/-- **The IO port control issue keeps `IOI`** for a well formed free range. -/
theorem ioi_ioCtl (f l : IoPort) (d c : CslotPtr) (σ : State Unit) (h : IOI σ) (hfl : f ≤ l)
    (hfree : ∀ q, f ≤ q → q ≤ l → ioA σ q = false) :
    ∀ x ∈ (performIoportControlInvocation (Z := Unit) (.ioPortControlInvocation f l d c) σ).1, IOI x.2 := by
  simp only [performIoportControlInvocation]
  intro x hx
  obtain ⟨y, hy, hx⟩ := hx
  have ey := setIoportMask_out hy
  obtain ⟨z, hz, hx⟩ := hx
  obtain rfl := Set.mem_singleton_iff.1 hz
  let S' : IoSet := fun f' l' => Has σ f' l' ∨ (f' = f ∧ l' = l)
  have hS : VS S' y.2 := by
    refine ⟨fun f' l' hh => Or.inl (by rw [ey] at hh; exact hh), ?_, ?_⟩
    · intro f' l' hs
      rw [ey]
      show f' ≤ l' ∧ ∀ q, f' ≤ q → q ≤ l' → (if q ≥ f ∧ q ≤ l then true else σ.archState.x64AllocatedIoPorts q) = true
      rcases hs with hs | ⟨rfl, rfl⟩
      · obtain ⟨hle, hal⟩ := h.1 f' l' hs
        refine ⟨hle, fun q h1 h2 => ?_⟩
        split_ifs
        · rfl
        · exact hal q h1 h2
      · exact ⟨hfl, fun q h1 h2 => by rw [if_pos ⟨h1, h2⟩]⟩
    · intro f1 l1 f2 l2 h1 h2 ⟨q, a1, a2, a3, a4⟩
      rcases h1 with h1 | ⟨rfl, rfl⟩ <;> rcases h2 with h2 | ⟨rfl, rfl⟩
      · exact h.2 f1 l1 f2 l2 h1 h2 ⟨q, a1, a2, a3, a4⟩
      · exfalso; have := (h.1 f1 l1 h1).2 q a1 a2; rw [hfree q a3 a4] at this; cases this
      · exfalso; have := (h.1 f2 l2 h2).2 q a3 a4; rw [hfree q a1 a2] at this; cases this
      · exact ⟨rfl, rfl⟩
  have := ik_vs (S := S') (hi_capInsert _ _ _ (fun f' l' e => Or.inr (by
    simp only [Cap.archObjectCap.injEq, ArchCap.ioPortCap.injEq] at e; exact ⟨e.1.symm, e.2.symm⟩)))
    (fun a => iok_capInsert _ _ _) y.2 hS x hx
  exact ioi_of_vs this

theorem ioi_archPerform (ai : ArchInvocation) (σ : State Unit) (h : IOI σ) (hc : ArchIo σ ai) :
    ∀ x ∈ ((archPerformInvocation (Z := Unit) ai).run σ).1, IOI x.2 := by
  have lift : ∀ {m : NonDet (State Unit) (List Data)}, (∀ y ∈ (m σ).1, IOI y.2) →
      ∀ x ∈ ((NonDetE.liftE (ε := Unit) m).run σ).1, IOI x.2 := by
    intro m hm x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    exact hm y hy
  have nr : ∀ {m : NonDet (State Unit) Unit}, (∀ y ∈ (m σ).1, IOI y.2) →
      ∀ y ∈ (archNoReturn (Z := Unit) m σ).1, IOI y.2 := by
    intro m hm y hy
    unfold archNoReturn at hy
    obtain ⟨z, hz, hy⟩ := hy
    rw [Set.mem_singleton_iff.1 hy]; exact hm z hz
  have vsp : ∀ {α : Type} {m : NonDet (State Unit) α}, IKp (HI (Has σ)) σ m → (∀ a, IoK a m) →
      ∀ y ∈ (m σ).1, IOI y.2 :=
    fun hH hI y hy => ioi_of_vs (ikp_vs hH hI (vs_of_ioi h) y hy)
  unfold archPerformInvocation
  refine lift ?_
  cases ai with
  | invokePageTable i =>
    exact nr (vsp (hi_performPageTableInvocation i σ fun c sl e => by subst e; exact hc)
      (fun _ => iok_performPageTableInvocation _))
  | invokePageDirectory i =>
    exact nr (vsp (hi_performPageDirectoryInvocation i σ fun c sl e => by subst e; exact hc)
      (fun _ => iok_performPageDirectoryInvocation _))
  | invokePDPT i =>
    exact nr (vsp (hi_performPdptInvocation i σ fun c sl e => by subst e; exact hc)
      (fun _ => iok_performPdptInvocation _))
  | invokePage i =>
    exact vsp (hi_performPageInvocation i σ fun c sl e => by subst e; exact hc)
      (fun _ => iok_performPageInvocation _)
  | invokeIOPortControl i =>
    obtain ⟨f, l, d, c⟩ := i
    exact nr (ioi_ioCtl f l d c σ h hc.1 hc.2)
  | _ => exact (by simp only; ioi_auto : IKH IOI _) σ h

theorem ioi_capAt_capOpt (σ : State Unit) (sl : CslotPtr) : SInvU.capAt σ sl = capOpt (σ.kheap sl.1) sl.2 := by
  unfold SInvU.capAt
  cases σ.kheap sl.1 with
  | none => rfl
  | some o => cases o <;> first | rfl | (simp only [SInvU.capView, capOpt]; split <;> rfl)

theorem ioi_noIo_frame {c : Cap} (hc : Fl4Proofs.P3.SInv.IsFrameCap c) :
    ∀ f l, c ≠ .archObjectCap (.ioPortCap f l) :=
  fun f l e => by subst e; exact hc

/-- fb3e: **the frame batch keeps `IOI`** (`SInv.ik_fbEntryX_of`): it inserts and writes frame caps only, its
maps are decoded `ArchSpecOKN` page invocations (an unmap's slot holds its cap), its deletes empty frame slots. -/
theorem ioi_performFrameBatch (b : Fl4FrameBatchInvocation) : IKH IOI (performFrameBatch (Z := Unit) b) :=
  Fl4Proofs.P3.SInv.ik_performFrameBatchX (fun w => Fl4Proofs.P3.SInv.ik_fbEntryX_of b w
    Fl4Proofs.P3.SInv.fbx_lookupTargetSlot Fl4Proofs.P3.SInv.fbx_lookupSourceSlot
    Fl4Proofs.P3.SInv.fbx_ensureEmpty Fl4Proofs.P3.SInv.fbx_deriveCap
    (fun s c src dest _ hs hc _ _ _ _ _ =>
      ik_ioi (fun S => hi_capInsert c src dest (ioIn_noIo (ioi_noIo_frame hc) S)) (fun _ => iok_capInsert _ _ _) s hs)
    (fun sl v => Fl4Proofs.P3.SInv.ik_fbMapQ (Q := fun t iv => ArchIo t iv) b sl v
      (fun _ _ _ _ _ _ => Fl4Proofs.P3.SInv.fbx_decodePageInvocation _ _ _ _ _)
      (fun s dev p R mt sz m hcap iv t h => by
        have hat : AtSl sl (.archObjectCap (.pageCap dev p R mt sz m)) s := by
          unfold AtSl; rw [← ioi_capAt_capOpt]; exact hcap
        have hfr : hV t = hV s :=
          (show IKHE (fun s' => hV s' = hV s) (decodePageInvocation (Z := Unit) fbPageMapLabel [v, b.mapRights, b.attr]
            sl (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), sl)]) by hv_auto) s rfl _ h
        have h2 := okd_archDecode_io fbPageMapLabel [v, b.mapRights, b.attr] ([] : CapRef) sl
          (.pageCap dev p R mt sz m) [(.archObjectCap (.pml4Cap b.vspace (some b.asid)), sl)] s hat s
        simp only [archDecodeInvocation] at h2
        exact h2 iv t h hfr)
      (fun s pi hs hq x hx => ioi_of_vs (ikp_vs (S := Has s) (hi_performPageInvocation pi s (fun c0 sl0 e => by
          subst e; exact hq))
        (fun _ => iok_performPageInvocation _) (vs_of_ioi hs) x hx)))
    (fun sl => by
      unfold fbDelX
      refine ike_liftE (ik_bind (Fl4Proofs.P3.SInv.fbx_ik_getCap _) fun c => ?_)
      split
      · exact ik_bind (Fl4Proofs.P3.SInv.fbx_isFinalCap _) fun _ =>
          ik_bind (ik_ioi (fun _ => hv_archFinaliseCap _ _) (fun _ => iok_archFinaliseCap _ _)) fun _ =>
            fun s hs x hx => ioi_emptySlot_p sl .nullCap s (clOk_noIo (fun f l e => by cases e) sl s) hs x hx
      · exact ik_fail)
    (fun _ _ _ _ => by unfold unmapPageUnflushed; ioi_auto)
    (fun s _ _ _ _ _ _ sl hs _ x hx => ioi_setCap_noIo _ sl (fun f l e => by cases e) s hs x hx))
    (ik_ioi (fun _ => hv_flushAll _ _) (fun _ => iok_flushAll _ _))

theorem ioi_fl4ArchPerform (fa : Fl4ArchInvocation) (σ : State Unit) (h : IOI σ)
    (hc : InvIo σ (.invokeArchObject fa)) :
    ∀ x ∈ ((fl4ArchPerformInvocation (Z := Unit) fa).run σ).1, IOI x.2 := by
  cases fa with
  | spec ai => exact ioi_archPerform ai σ h hc
  | frameBatch bi =>
    intro x hx
    simp only [fl4ArchPerformInvocation] at hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    exact ioi_performFrameBatch bi σ h y hy
  | _ => exact (by simp only [fl4ArchPerformInvocation]; ioi_auto : IKHE IOI _) σ h

theorem ioi_invokeCnode (i : CnodeInvocation) (σ : State Unit) (h : IOI σ) (hc : CnIo (Has σ) i) :
    ∀ x ∈ ((invokeCnode (Z := Unit) i).run σ).1, IOI x.2 := by
  have vs : ∀ {m : NonDet (State Unit) Unit}, IKH (HI (Has σ)) m → (∀ a, IoK a m) →
      ∀ x ∈ ((NonDetE.liftE (ε := Unit) m).run σ).1, IOI x.2 := by
    intro m hH hI x hx
    obtain ⟨y, hy, rfl⟩ := mem_liftE_inv' hx
    exact ioi_of_vs (ik_vs hH hI σ (vs_of_ioi h) y hy)
  cases i with
  | insertCall c s d => exact vs (hi_capInsert c s d hc) (fun _ => iok_capInsert _ _ _)
  | moveCall c s d => exact vs (hi_capMove c s d hc) (fun _ => iok_capMove _ _ _)
  | rotateCall c1 c2 s1 s2 s3 =>
    simp only [invokeCnode]
    split
    · exact vs (hi_capSwap _ _ _ _ hc.1 hc.2) (fun _ => iok_capSwap _ _ _ _)
    · exact vs (ik_bind (hi_capMove _ _ _ hc.2) fun _ => hi_capMove _ _ _ hc.1)
        (fun _ => ik_bind (iok_capMove _ _ _) fun _ => iok_capMove _ _ _)
  | revokeCall s => exact ioi_capRevoke s σ h
  | deleteCall s => exact ioi_capDelete s σ h
  | cancelBadgedSendsCall c =>
    exact (by simp only [invokeCnode]; split <;> (try (exfalso; simp_all; done)) <;> ioi_auto : IKHE IOI _) σ h

theorem ioi_invokeIrqHandler (i : IrqHandlerInvocation) (σ : State Unit) (h : IOI σ)
    (hc : InvIo σ (.invokeIRQHandler i)) :
    ∀ x ∈ (invokeIrqHandler (Z := Unit) i σ).1, IOI x.2 := by
  have hI : ∀ a, IoK a (invokeIrqHandler (Z := Unit) i) := fun _ => by
    cases i <;> simp only [invokeIrqHandler] <;> iok_auto
  cases i with
  | setIRQHandler irq c sl =>
    have hc' : IoIn (Has σ) c := hc
    have key : IKH (HI (Has σ)) (invokeIrqHandler (Z := Unit) (.setIRQHandler irq c sl)) := by
      simp only [invokeIrqHandler]
      exact ik_bind (hv_getIrqSlot _) fun s => ik_bind (hi_capDeleteOne s) fun _ => hi_capInsert c sl s hc'
    exact fun x hx => ioi_of_vs (ik_vs key hI σ (vs_of_ioi h) x hx)
  | _ =>
    exact ik_ioi (fun _ => by simp only [invokeIrqHandler]; hv_auto) hI σ h

set_option maxHeartbeats 8000000 in
theorem ioi_fl4Perform (blk call don : Bool) (inv : Fl4Invocation) (σ : State Unit) (h : IOI σ)
    (hc : InvIo σ inv) :
    ∀ x ∈ ((fl4PerformInvocation (Z := Unit) blk call don inv).run σ).1, IOI x.2 := by
  cases inv with
  | invokeCNode i =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    obtain ⟨z, hz, ⟨u, hu, hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
    · obtain rfl := Set.mem_singleton_iff.1 hx
      exact ioi_invokeCnode i σ h hc _ hz
    · exact ioi_invokeCnode i σ h hc _ hz
  | invokeIRQHandler i =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    obtain ⟨z, hz, ⟨u, hu, hx⟩ | ⟨e, he, rfl⟩⟩ := mem_bindE_inv' hx
    · obtain ⟨w, hw, rfl⟩ := mem_liftE_inv' hz
      obtain rfl := Set.mem_singleton_iff.1 hx
      exact ioi_invokeIrqHandler i σ h hc w hw
    · obtain ⟨w, -, rfl⟩ := mem_liftE_inv' hz; cases he
  | invokeArchObject fa =>
    intro x hx
    simp only [fl4PerformInvocation] at hx
    exact ioi_fl4ArchPerform fa σ h hc x hx
  | _ => exact (show IKHE (ε := Unit) IOI (fl4PerformInvocation (Z := Unit) blk call don _) from by
      simp only [fl4PerformInvocation]; ioi_auto) σ h

/-! ## The invocation shell -/

set_option maxHeartbeats 8000000 in
/-- **The invocation keeps `IOI`.** -/
theorem ioi_handleInvocationR (rep calling blocking don fp : Bool) (cptr : CapRef) :
    IKHE (ε := Unit) IOI (fl4HandleInvocationR (Z := Unit) rep calling blocking don fp cptr) := by
  unfold fl4HandleInvocationR
  refine ike_bind (by ioi_auto) fun thread => ike_bind (by ioi_auto) fun info => ?_
  intro σ hs y hy
  have h1 : ∀ w ∈ ((ExceptT.run (do
       let (cap, slot) ← capFaultOnFailure (ofBl cptr) false <| lookupCapAndSlot (Z := Unit) thread cptr
       let buffer ← NonDetE.liftE <| lookupIpcBuffer false thread
       let extracaps ← lookupExtraCaps thread buffer info
       NonDetE.returnOk (slot, cap, extracaps, buffer))) σ).1, IOI w.2 :=
    fun w hw => (by ioi_auto : IKHE (ε := Fault) IOI _) σ hs w hw
  refine syscall_post' (I := IOI) (Q := IOI) h1 ?_ ?_ ?_ ?_ y hy
  · intro f s hs v hv; exact (by ioi_auto : IKH IOI _) s hs v hv
  · intro a s has w hw
    obtain ⟨sl, cap, ex, buf⟩ := a
    exact (by ioi_auto : IKHE IOI _) s (h1 _ has) w hw
  · intro e s hs v hv; exact (by ioi_auto : IKH IOI _) s hs v hv
  · intro a s b s' has hbs hI y hy
    obtain ⟨sl, cap, ex, buf⟩ := a
    have hcap : capOpt (s.kheap sl.1) sl.2 = some cap := okCap_front thread cptr info σ _ s has
    have eE : hV s' = hV s := (by hv_auto : IKHE (fun x => hV x = hV s) _) s rfl _ hbs
    have eA : ioA s' = ioA s := (by iok_auto : IoKE (ioA s) _) s rfl _ hbs
    have hd : InvIo s' b :=
      okdAt_bind (fun _ s1 _ => okd_fl4Decode_io _ _ _ _ _ _ _ _ s hcap s1) b s' hbs eE
    obtain ⟨z, hz, ⟨u, hu, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
    · have hz' : hV z.2 = hV s' := (by hv_auto : IKHE (ε := Unit) (fun x => hV x = hV s')
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' rfl z hz
      have hzA : ioA z.2 = ioA s' := (by iok_auto : IoKE (ioA s')
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' rfl z hz
      have hz1 : IOI z.2 := (by ioi_auto : IKHE (ε := Unit) IOI
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz
      obtain ⟨r, s1⟩ := z
      simp only at hu; subst hu
      have hd1 : InvIo s1 b := invIo_of hz' hzA hd
      obtain ⟨z2, hz2, ⟨rp, hr, hy⟩ | ⟨e, -, rfl⟩⟩ := mem_bindE_inv' hy
      · obtain ⟨r2, s2⟩ := z2
        simp only at hr; subst hr
        have hs2 := ioi_fl4Perform blocking calling don b s1 hz1 hd1 _ hz2
        exact (by ioi_auto : IKHE IOI _) s2 hs2 y hy
      · exact ioi_fl4Perform blocking calling don b s1 hz1 hd1 _ hz2
    · exact (by ioi_auto : IKHE (ε := Unit) IOI
        (withoutPreemption (Z := Unit) (setThreadState thread .restart))) s' hI z hz

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_handleInvocationR _ _ _ _ _ _)

/-! ## The kernel entry -/

set_option maxHeartbeats 8000000 in
theorem ioi_fl4HandleSyscall (rep : Bool) (c : Syscall) : IKHE (ε := Unit) IOI (fl4HandleSyscall (Z := Unit) rep c) := by
  cases c <;> simp only [fl4HandleSyscall] <;> ioi_auto

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_fl4HandleSyscall _ _)

set_option maxHeartbeats 8000000 in
theorem ioi_handleEvent_other (ev : Event) (h : ∀ c, ev ≠ .syscallEvent c) :
    IKHE (ε := Unit) IOI (handleEvent (Z := Unit) ev) := by
  cases ev with
  | syscallEvent c => exact absurd rfl (h c)
  | _ => simp only [handleEvent]; ioi_auto

set_option maxHeartbeats 4000000 in
theorem ioi_fl4HandleEvent (rep : Bool) (ev : Event) : IKHE (ε := Unit) IOI (fl4HandleEvent (Z := Unit) rep ev) := by
  by_cases h : ∃ c, ev = .syscallEvent c
  · obtain ⟨c, rfl⟩ := h
    simp only [fl4HandleEvent]
    ioi_auto
  · rw [fl4HandleEvent_other rep ev fun c e => h ⟨c, e⟩]
    exact ioi_handleEvent_other ev fun c e => h ⟨c, e⟩

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_fl4HandleEvent _ _)

set_option maxHeartbeats 4000000 in
/-- **`fl4CallKernel` keeps `IOI`, for every event.** -/
theorem ioi_fl4CallKernel (rep : Bool) (ev : Event) : IKH IOI (fl4CallKernel (Z := Unit) rep ev) := by
  unfold fl4CallKernel; ioi_auto

macro_rules | `(tactic| ioi_leaf) => `(tactic| with_reducible exact ioi_fl4CallKernel _ _)

theorem ioi_fl4KernelEntrySyscall (rep : Bool) (c : Syscall) :
    IKH IOI (fl4KernelEntrySyscall (Z := Unit) rep c) := by
  unfold fl4KernelEntrySyscall; ioi_auto

/-! ## The statements: `SpecIoP ∧ IoNoOverlap` -/

/-- **[J] spec** (l4v `ioports_no_overlap`): two IO-port caps with overlapping
ranges have equal ranges. -/
def IoNoOverlap (σ : State Unit) : Prop :=
  ∀ sl sl' f l f' l', SInvU.capAt σ sl = some (.archObjectCap (.ioPortCap f l)) →
    SInvU.capAt σ sl' = some (.archObjectCap (.ioPortCap f' l')) → Ovl f l f' l' → f = f' ∧ l = l'

theorem boot_noIo (f l : IoPort) : ¬ Has (initASt (Z := Unit)) f l := by
  rintro ⟨p, cref, hc⟩
  simp only [initASt, initKheap, Function.update_apply] at hc
  split_ifs at hc <;>
    first
    | (simp [capOpt] at hc; done)
    | (simp only [capOpt] at hc; done)
    | (simp only [capOpt, emptyCnode] at hc; split_ifs at hc <;> simp_all; done)
    | (simp only [capOpt, tcbCnodeMap, Function.update_apply] at hc; split_ifs at hc <;> simp_all; done)

theorem boot_IOI : IOI (initASt (Z := Unit)) :=
  ⟨fun f l hh => absurd hh (boot_noIo f l), fun f l _ _ hh => absurd hh (boot_noIo f l)⟩

end

end Fl4Proofs.P3.SInvIo
