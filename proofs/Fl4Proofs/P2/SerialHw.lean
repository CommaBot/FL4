/-
P2 (line lvm, gen 4): **a hardware step beside the cores' steps**, for the guest's lock-free writes of a
running VCPU's words (`OwnMapV.VmRunFrame` [P]).

`Serial.Step` is a step of a core. While core `c` runs a bound thread in the guest, with no lock held, the
hardware (`fl4_arch_x86_64::vm::run` / `vm::vmx_exit`, trusted) changes words of the running VCPU `v` (exit
record, `REGS`, `PENDING`, `SVM_CPU`, VMCB/VMCS state), and `Arch::vcpu_sync` writes `v`'s shadow words. This
module adds that as a step kind **beside** `Step` (`XGReach` / `XSafeRun` have a third constructor `hw`),
without editing `Serial.Step` (every P2 module imports it):

* `HwWr s a x l`: the hardware writes word `a := x`, where `a`'s owner is the lock `l` (for a VCPU word,
  `lock v`), **no core holds `l`**, the write moves no owner, and `a`'s class is untracked (`ko a = .free`).
  `hwCfg s a x` is the state after it: memory updated, and the write appended to the log as an entry of its
  own (`.wr a x .done`), so the serial order explains it.
* `inv_hw`: `InvH` is kept (the serial history `H` takes the same write): no in-progress local path holds
  `l`, so none has written `a` or may read it.
* `sinv_hw`: `SInv` is kept: to every in-progress local path the write is `Foreign` (`Safe.foreign`).
* `sinv_stepX`: `SerialSafe.sinv_step` with its reachability premise replaced by the one fact it uses (a
  closed gate has no local path in progress), so that it applies along `XGReach`.
* **`serializable_safeX`**: `SerialSafe.serializable_safe` for executions with hardware steps (`XSafeRun`):
  where no local path is in progress, memory is the serial run of the completed entries, hardware writes
  included, in completion order.

Premise (in `HwWr`, discharged for FL4 in `E2EV.HwStepV` from `VmRunFrame` [P]): the hardware writes only
while no core holds `l`. For a VCPU, `lock v` is taken by fl4-sync's local VM entries only for a VCPU bound
to the current thread of the taking core, which is then not in the guest; `TRUSTED`'s glue
(`vm_locks` / `vm_timer_locks` / `vcpu_locks`) and `vcpu.stall` (the gate forces a VM exit before a serial
body touches `v`) are where this is read off.
-/
import Fl4Proofs.P2.SerialSafe

namespace Fl4Proofs.P2.Serial

noncomputable section

variable {A V C L : Type} [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- **A hardware write** of `a := x` in `s` (module docstring): `a` is the lock `l`'s, which no core holds;
the write moves no owner; `a`'s class is untracked. -/
structure HwWr (s : Cfg A V C L) (a : A) (x : V) (l : L) : Prop where
  own : s.own s.mem a = .lock l
  free : s.lk l = none
  keep : s.own (Function.update s.mem a x) = s.own s.mem
  ko : s.ko a = .free

/-- The state after a hardware write: memory updated, the write logged as its own entry. -/
def hwCfg (s : Cfg A V C L) (a : A) (x : V) : Cfg A V C L :=
  { s with mem := Function.update s.mem a x, log := s.log ++ [.wr a x .done] }

theorem HwWr.ne_of_held {s : Cfg A V C L} {a : A} {x : V} {l : L} (h : HwWr s a x l) {d : C} {y : A}
    (hy : Held s.lk d (s.own s.mem y)) : y ≠ a := by
  rintro rfl; rw [h.own] at hy
  change s.lk l = some d at hy
  rw [h.free] at hy; cases hy

theorem HwWr.ne_of_perm {s : Cfg A V C L} {a : A} {x : V} {l : L} (h : HwWr s a x l) {d : C} {y : A}
    (hy : Perm s d y) : y ≠ a := by
  rcases hy with hy | hy
  · exact h.ne_of_held hy
  · rintro rfl; rw [h.own] at hy; cases hy

/-- **The invariant is kept by a hardware write**, the history taking the same write. -/
theorem inv_hw {m0 : A → V} {s : Cfg A V C L} {H : A → V} (I : InvH m0 s H) {a : A} {x : V} {l : L}
    (h : HwWr s a x l) : InvH m0 (hwCfg s a x) (Function.update H a x) where
  hist := RunAll.snoc I.hist (.wr (.done _))
  clo := I.clo
  drn := I.drn
  agree y hy := by
    show Function.update s.mem a x y = Function.update H a x y
    by_cases hya : y = a
    · subst hya; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hya, Function.update_of_ne hya]; exact I.agree y hy
  loc d p0 p W hd := by
    have L0 := I.loc d p0 p W hd
    refine L0.mono (s' := hwCfg s a x) (fun y hy => ?_) (fun y hy => ?_) (fun y hy => ?_)
      (fun y hy => ?_) rfl rfl (fun y hy => ?_)
    · show Held s.lk d (s.own (Function.update s.mem a x) y); rw [h.keep]; exact hy
    · show Held s.lk d (s.own (Function.update s.mem a x) y) ∨ s.own (Function.update s.mem a x) y = .gate
      rw [h.keep]; exact hy
    · exact Function.update_of_ne (h.ne_of_perm hy) _ _
    · exact Function.update_of_ne (h.ne_of_held (L0.held y hy)) _ _
    · have hya : y ≠ a := by
        rintro rfl; rw [h.ko] at hy; rcases hy with hy | hy <;> cases hy
      rw [Function.update_of_ne hya]
  clsinv y := by
    show s.cls y (Function.update s.mem a x y) = s.cls y (Function.update H a x y) ∨
      ∃ e p0 p W, s.ph e = .loc p0 p W ∧ y ∈ W ∧ (s.ko y = .core e ∨ s.ko y = .free)
    by_cases hya : y = a
    · subst hya; left; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hya, Function.update_of_ne hya]; exact I.clsinv y

/-- **`SInv` is kept by a hardware write**: to every in-progress local path it is `Foreign`. -/
theorem sinv_hw {s : Cfg A V C L} (I : SInv s) {a : A} {x : V} {l : L} (h : HwWr s a x l) :
    SInv (hwCfg s a x) := by
  intro d p0 q W hd
  rcases I d p0 q W hd with hg | hS
  · exact Or.inl hg
  · right
    have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem a x := by
      refine ⟨?_, fun y hy => absurd (by rw [h.keep]) hy, ?_⟩
      · rw [h.own]; rintro (hl | hl)
        · change s.lk l = some d at hl; rw [h.free] at hl; cases hl
        · cases hl
      · right; rw [h.ko]; exact ⟨(fun e => by cases e), (fun e => by cases e)⟩
    exact Safe.foreign hS hF

/-- Executions whose local-path accesses respect ownership, with hardware writes. -/
inductive XGReach (s0 : Cfg A V C L) : Cfg A V C L → Prop
  | refl : XGReach s0 s0
  | step {s s' : Cfg A V C L} {c : C} :
      XGReach s0 s → Allowed s c → Step s c s' → XGReach s0 s'
  | hw {s : Cfg A V C L} {a : A} {x : V} {l : L} :
      XGReach s0 s → HwWr s a x l → XGReach s0 (hwCfg s a x)

theorem xgreach_inv {s0 s : Cfg A V C L} (h0 : Init s0) (h : XGReach s0 s) :
    ∃ H, InvH s0.mem s H := by
  induction h with
  | refl => exact ⟨_, inv_init h0⟩
  | step _ hal hs ih =>
    obtain ⟨H, I⟩ := ih
    exact I.step hal hs
  | hw _ hh ih =>
    obtain ⟨H, I⟩ := ih
    exact ⟨_, inv_hw I hh⟩

/-- `no_overlap` with hardware writes. -/
theorem no_overlapX {s0 s : Cfg A V C L} (h0 : Init s0) (h : XGReach s0 s) :
    s.gate = .closed → NoLoc s := by
  obtain ⟨H, I⟩ := xgreach_inv h0 h
  exact I.clo

/-- `serializable_quiescent` with hardware writes. -/
theorem serializable_quiescentX {s0 s : Cfg A V C L} (h0 : Init s0) (h : XGReach s0 s)
    (hq : NoLoc s) : RunAll s.log s0.mem s.mem := by
  obtain ⟨H, I⟩ := xgreach_inv h0 h
  have : s.mem = H := funext fun x =>
    I.agree x (fun d q0 q U hd => absurd (by rw [hd]; trivial) (hq d))
  rw [this]; exact I.hist

/-- **`SerialSafe.sinv_step`** with its reachability premise replaced by the one fact it uses. -/
theorem sinv_stepX {s s' : Cfg A V C L} {c : C} (hno : s.gate = .closed → NoLoc s)
    (hA : ArmInv s) (hB : ∀ p0 k W, s.ph c = .loc p0 (.start k) W →
      Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem k) (I : SInv s)
    (hal : Allowed s c) (hst : Step s c s') : SInv s' := by
  intro d p0 q W hd
  cases hst with
  | arm p hc =>
    have hd' : Function.update s.ph c (.arm p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | back hc _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @enter p hc _ =>
    have hd' : Function.update s.ph c (.loc p p ∅) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      exact Or.inl ((hA d _ hc).glue _ _ _)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rd p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | rd _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rds p1 a k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | rds hk => exact Or.inl (hk _)
      · cases hS with
        | rds h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @rdc p1 a K k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 (k (s.mem a)) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | rdc _ _ hk => exact Or.inl (hk _)
      · cases hS with
        | rdc _ _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @start p1 k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      exact Or.inr (hB _ _ _ hc)
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | @wr p1 a v k W1 hc =>
    have hd' : Function.update s.ph c (.loc p1 k (insert a W1)) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg
      · cases hS with
        | wr _ _ _ h => exact Or.inr (h _ (.refl _))
    · rw [Function.update_of_ne hdc] at hd'
      rcases I d p0 q W hd' with hg | hS
      · exact Or.inl hg
      · right
        simp only [Allowed, hc] at hal
        obtain ⟨hb, hmv, hcl⟩ := hal
        have hcd : c ≠ d := Ne.symm hdc
        have hF : Foreign s.own s.cls s.ko d (fun l => s.lk l = some d) s.mem a v := by
          refine ⟨not_PO_of_held hcd hb, fun x hx =>
            ⟨not_PO_of_held hcd (hmv x hx).1, not_PO_of_held hcd (hmv x hx).2⟩, ?_⟩
          rcases hcl with h | h | h
          · exact Or.inl h
          · refine Or.inr ⟨?_, ?_⟩
            · rw [h]; intro e; cases e
            · rw [h]; intro e; exact hcd (ClsOwner.core.inj e)
          · refine Or.inr ⟨?_, ?_⟩
            · rw [h]; intro e; cases e
            · rw [h]; intro e; cases e
        exact Safe.foreign (q := q) hS hF
  | @lock p1 l k W1 b hc hb =>
    have hd' : Function.update s.ph c (.loc p1 (k b) W1) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
      rcases I d _ _ _ hc with hg | hS
      · cases hg with
        | lock hk => exact Or.inl (hk b)
      · cases hS
    · rw [Function.update_of_ne hdc] at hd'
      refine sinv_keep (s := s) (lk' := if b then Function.update s.lk l (some c) else s.lk)
        rfl rfl (fun l' => ?_) rfl rfl (I d p0 q W hd')
      cases b with
      | false => rw [if_neg (by decide)]
      | true =>
        rw [if_pos rfl]
        by_cases hl : l' = l
        · subst hl
          rw [Function.update_self, hb rfl]
          exact ⟨fun h => absurd (Option.some.inj h) (Ne.symm hdc), fun h => by cases h⟩
        · rw [Function.update_of_ne hl]
  | @leave p1 W1 hc =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      refine sinv_keep (s := s) (lk' := release s.lk c) rfl rfl (fun l' => ?_) rfl rfl
        (I d p0 q W hd')
      show (if s.lk l' = some c then none else s.lk l') = some d ↔ s.lk l' = some d
      by_cases hl : s.lk l' = some c
      · rw [if_pos hl, hl]
        exact ⟨(fun h => by cases h), fun h => absurd (Option.some.inj h) (Ne.symm hdc)⟩
      · rw [if_neg hl]
  | take p hc _ =>
    have hd' : Function.update s.ph c (.ser p) d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'; exact I d p0 q W hd'
  | scan e _ _ _ => exact I d p0 q W hd
  | drain _ _ _ => exact I d p0 q W hd
  | serial keep own' cls' ko' _ hg _ _ =>
    have hd' : Function.update s.ph c .idle d = .loc p0 q W := hd
    by_cases hdc : d = c
    · subst hdc; rw [Function.update_self] at hd'; cases hd'
    · rw [Function.update_of_ne hdc] at hd'
      exact absurd (by rw [hd']; trivial) (hno hg d)


/-- An execution whose core steps are `SafeStep`s, with hardware writes. -/
inductive XSafeRun (s0 : Cfg A V C L) : Cfg A V C L → Prop
  | refl : XSafeRun s0 s0
  | step {s s' : Cfg A V C L} {c : C} :
      XSafeRun s0 s → Step s c s' → SafeStep s c s' → XSafeRun s0 s'
  | hw {s : Cfg A V C L} {a : A} {x : V} {l : L} :
      XSafeRun s0 s → HwWr s a x l → XSafeRun s0 (hwCfg s a x)

/-- **Every step of an `XSafeRun` is `Allowed`** (`safeRun_greach` with hardware writes). -/
theorem xsafeRun_greach {s0 s : Cfg A V C L} (h0 : Init s0) (hA0 : ArmInv s0)
    (h : XSafeRun s0 s) : XGReach s0 s ∧ SInv s ∧ ArmInv s := by
  induction h with
  | refl => exact ⟨.refl, fun d p0 q W hd => absurd (by rw [hd]; trivial) (h0.2 d), hA0⟩
  | @step s s' c _ hst hok ih =>
    obtain ⟨hr, hS, hA⟩ := ih
    have hal := allowed_of_sinv hS c
    exact ⟨.step hr hal hst, sinv_stepX (no_overlapX h0 hr) hA hok.start hS hal hst,
      armInv_step hA hst hok⟩
  | hw _ hh ih =>
    obtain ⟨hr, hS, hA⟩ := ih
    exact ⟨.hw hr hh, sinv_hw hS hh, hA⟩

/-- **Every `XSafeRun` is a serial one** (`serializable_safe` with hardware writes): where it reaches a
state with no local path in progress, memory is what running the completed entries, the hardware's writes
included, one after another in completion order produces from the initial memory (a speculative read
returning any value, as there). -/
theorem serializable_safeX {s0 s : Cfg A V C L} (h0 : Init s0) (hA0 : ArmInv s0)
    (h : XSafeRun s0 s) (hq : NoLoc s) : RunAll s.log s0.mem s.mem :=
  serializable_quiescentX h0 (xsafeRun_greach h0 hA0 h).1 hq

end

end Fl4Proofs.P2.Serial
