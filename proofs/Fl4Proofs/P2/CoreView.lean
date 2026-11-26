/-
# P2/P3 (line p3mc, gen 1): **core `c`'s view of a shared memory**

P3's joint invariant is a single-core refinement: `Sched.SchedCore.cur : L.cpu s = c` and
`SchedCore.aff : ∀ t ∈ T, L.mem s (affA t) = c` (P3/SchedRel.lean l.71–72), `SchedRel.core : ∀ sc ∈ C,
L.mem s (scW sc 16) = c` (l.133), with `JAtZ.tcbs_eq` (`T` = every TCB of the heap) and `JAtZ.hscC` (`C` ⊇ every SC
of the heap). So at a P3 state every TCB and every SC is homed on the current core, and two P3 states agreeing on
kernel memory run on one core (`GlueCross.chain_cpu_eq`, `crossCoreView_false`). This module defines what replaces
"the memory" when core `c` looks at an SMP state: **`view K c m`**, the memory `m` with every word that says another
core exists rewritten, so that P3's statements can be applied per core (DESIGN of the line: `WS/handoff/p3mc.md`).

## The view (`repl`, `view`)

For a word `b`, by its region (`OwnMap.region`, memory-independent):

* a TCB `t` homed elsewhere (`m (t + AFFINITY) ≠ c`): `AFFINITY := c` (`SchedCore.aff`), `SC := 0` and
  `DEBUG_NEXT`/`DEBUG_PREV := 0` (the thread is passive and on no debug list in `c`'s view: `Inv.rd`, `QRdy`,
  `BlockedScActive`, `DbgWFL.mem` then ask nothing of it at `c`'s clock), `IN_QUEUES := 0` (`SchedCore.queued` /
  `released`: it is in none of `c`'s queues), and `STATE := Inactive` when it is running, restarting, idle or running a
  VM (`Hidden`: a runnable thread outside `c`'s queues would break `Inv.rd`); blocked states are kept (the thread may be
  in a shared endpoint, notification or reply, which `c`'s view must show);
* a scheduling context whose `CORE` word is not `c`: `CORE := c` (`SchedRel.core`), `TCB := 0` (unbound, matching
  the TCB side);
* core `d ≠ c`'s node: the release queue head/tail, the debug list head, the priority bitmaps and the ready queues
  `:= 0` (P1's `SchedQueuesInvX` over all cores then holds with `d`'s queues empty);
* every other word: `m`'s.

## What is proved

* **`view_aff`, `view_sc_core`**: at `view K c m`, every TCB of the heap has `AFFINITY = c` and every SC has
  `CORE = c`, **for every memory `m` and every core `c`**. The constraint that refutes the cross-core view
  (`GlueCross.slJAt_aff`: at a chain state every `AFFINITY` word is the state's `cpu`) holds of every core's view of
  one memory, so it no longer forces all local starts of an epoch onto one core (`GlueCross.start_two_cores`) once the
  start fact is asked at `view K c μ` instead of `μ`.
* **`view_home`, `view_node_self`, `view_eq_of_own`**: words of `c`'s own threads, `c`'s node, and every word owned
  (`OwnMap.own`) by core `c` or by a lock are unchanged. Every rewritten word is owned by the gate or by another core
  (`repl_own`): a local path of core `c` is allowed to write neither (`PathObl.write_own`), and of the gate-owned
  ones (`AFFINITY`, `SC`, `DEBUG_*` of other cores' threads, `CORE` of other cores' SCs) an accepted run of core
  `c` reads none by DESIGN §7 (it declines on a thread's `AFFINITY` before touching another core's thread).
* **`view_mix_own`** (the local step of core `c` commutes with `c`'s view): for writes `W` owned by core `c` or by
  locks, `view K c (mix W m₂ m) = mix W m₂ (view K c m)`. With `GlueFrame.frame_acc`, the accepted run of `c` from a
  state with memory `view K c H` ends in `view K c H'` for Serial's completion memory `H' = mix W _ H`.
* **`view_frame`** (another core's step changes `c`'s view only where it wrote): for writes `W` with no gate-owned
  word, `view K c (mix W m₂ m) x = view K c m x` for `x ∉ W`.
* **`view_idem`**, and the `ownP` forms (`ownP_eq_own`, `repl_ownP`, `view_mix_ownP`, `view_frameP`) for the
  layouts of the U2/U4/U5 executions (`KLayoutP`).

No premise is introduced; no existing statement changed.
-/
import Fl4Proofs.P2.OwnMapPte
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.CoreView
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner mix mix_mem mix_nmem)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.OwnMapV (KLayoutV InVcpu ownV RegionOKV ownV_off)
open Fl4Proofs.P2.OwnMapP (KLayoutP ownP RegionOKP ownP_off)

noncomputable section
open Classical

/-! ## Definitions -/

/-- The thread states core `c`'s view hides of another core's thread: running (1), restart (2), idle (7), running a
VM (8) (`sched::TS_*`). -/
def Hidden (v : U64) : Prop := v.val = 1 ∨ v.val = 2 ∨ v.val = 7 ∨ v.val = 8

/-- The TCB offsets set to 0 for another core's thread: `SC` (3464), `IN_QUEUES` (3592), `DEBUG_NEXT` (3576),
`DEBUG_PREV` (3584) (`arch/x86_64/layout.rs`, `F = 0xd00`). -/
def TZero (o : Nat) : Prop := o = 3464 ∨ o = 3592 ∨ o = 3576 ∨ o = 3584

/-- The replacement of offset `o` of the TCB `t` whose word holds `v` (module docstring). -/
def tcbRepl (m : U64 → U64) (c t : U64) (o : Nat) (v : U64) : Option U64 :=
  if m (fld t oAFFINITY) = c then none
  else if o = 3520 then some c
  else if TZero o then some 0#u64
  else if o = 3328 ∧ Hidden v then some 0#u64
  else none

/-- The replacement of offset `o` of the SC `p` (`CORE` 16, `TCB` 24; `layout.rs` `sc`). -/
def scRepl (m : U64 → U64) (c p : U64) (o : Nat) : Option U64 :=
  if m (fld p 16#u64) = c then none
  else if o = 16 then some c
  else if o = 24 then some 0#u64
  else none

/-- The node words of another core cleared in `c`'s view: `RELEASE_HEAD`/`TAIL` (64, 72), `DEBUG_TCBS` (88), the
bitmaps and ready queues (128 … 4263; `layout.rs` `node`). -/
def QWord (o : Nat) : Prop := o = 64 ∨ o = 72 ∨ o = 88 ∨ (128 ≤ o ∧ o < 4264)

/-- The offset of `b` in core `d`'s node. -/
def nodeOff (K : KLayout) (d b : U64) : Nat := b.val - (K.ksb.val + 13568 + d.val * 4288)

/-- The replacement of a word `b` of core `d`'s node. -/
def nodeRepl (K : KLayout) (c d b : U64) : Option U64 :=
  if d = c then none else if QWord (nodeOff K d b) then some 0#u64 else none

/-- The replacement of word `b`, deciding words read in `m`, the word's own value `v`. -/
def repl2 (K : KLayout) (c : U64) (m : U64 → U64) (v b : U64) : Option U64 :=
  match region K b with
  | .tcb t => tcbRepl m c t (b.val - t.val) v
  | .sc p => scRepl m c p (b.val - p.val)
  | .node d => nodeRepl K c d b
  | _ => none

/-- The replacement of word `b` in `c`'s view of `m` (module docstring). -/
def repl (K : KLayout) (c : U64) (m : U64 → U64) (b : U64) : Option U64 := repl2 K c m (m b) b

/-- **Core `c`'s view of the memory `m`** (module docstring). -/
def view (K : KLayout) (c : U64) (m : U64 → U64) (b : U64) : U64 := (repl K c m b).getD (m b)

theorem view_none {K : KLayout} {c : U64} {m : U64 → U64} {b : U64} (h : repl K c m b = none) :
    view K c m b = m b := by
  simp [view, h]

theorem view_some {K : KLayout} {c : U64} {m : U64 → U64} {b w : U64} (h : repl K c m b = some w) :
    view K c m b = w := by
  simp [view, h]

/-! ## Who owns a rewritten word -/

theorem tcbRepl_own {m : U64 → U64} {c t : U64} {o : Nat} {v w : U64} (h : tcbRepl m c t o v = some w) :
    tcbOwner m t o = .gate ∨ ∃ d, d ≠ c ∧ tcbOwner m t o = .core d := by
  unfold tcbRepl at h
  by_cases ha : m (fld t oAFFINITY) = c
  · rw [if_pos ha] at h; cases h
  rw [if_neg ha] at h
  have home : ¬ GateField o → ¬ TimerField o → ¬ GField o → tcbOwner m t o = .core (m (fld t oAFFINITY)) := by
    intro h1 h2 h3; unfold tcbOwner; rw [if_neg h1, if_neg h2, if_neg h3]
  have gate : GateField o → tcbOwner m t o = .gate := by
    intro h1; unfold tcbOwner; rw [if_pos h1]
  by_cases h1 : o = 3520
  · exact Or.inl (gate (by unfold GateField; omega))
  rw [if_neg h1] at h
  by_cases h2 : TZero o
  · unfold TZero at h2
    rcases h2 with h2 | h2 | h2 | h2
    · exact Or.inl (gate (by unfold GateField; omega))
    · exact Or.inr ⟨_, ha, home (by unfold GateField; omega) (by unfold TimerField; omega)
        (by unfold GField; omega)⟩
    · exact Or.inl (gate (by unfold GateField; omega))
    · exact Or.inl (gate (by unfold GateField; omega))
  rw [if_neg h2] at h
  by_cases h3 : o = 3328 ∧ Hidden v
  · exact Or.inr ⟨_, ha, home (by unfold GateField; omega) (by unfold TimerField; omega)
      (by unfold GField; omega)⟩
  rw [if_neg h3] at h; cases h

/-- **Every rewritten word is owned by the gate or by another core.** -/
theorem repl2_own {K : KLayout} {c : U64} {m : U64 → U64} {v b w : U64} (h : repl2 K c m v b = some w) :
    own K m b = .gate ∨ ∃ d, d ≠ c ∧ own K m b = .core d := by
  unfold repl2 at h
  cases hr : region K b with
  | tcb t =>
    rw [hr] at h
    have e : own K m b = tcbOwner m t (b.val - t.val) := by simp only [own, hr]
    rw [e]; exact tcbRepl_own h
  | sc p =>
    rw [hr] at h
    change scRepl m c p (b.val - p.val) = some w at h
    have e : own K m b = if b.val = p.val + 16 then .gate else .core (m (fld p 16#u64)) := by
      simp only [own, hr]
    rw [e]
    unfold scRepl at h
    by_cases hc : m (fld p 16#u64) = c
    · rw [if_pos hc] at h; cases h
    rw [if_neg hc] at h
    by_cases h16 : b.val - p.val = 16
    · left; rw [if_pos (by omega)]
    rw [if_neg h16] at h
    by_cases h24 : b.val - p.val = 24
    · right; exact ⟨_, hc, by rw [if_neg (by omega)]⟩
    rw [if_neg h24] at h; cases h
  | node d =>
    rw [hr] at h
    change nodeRepl K c d b = some w at h
    have e : own K m b = .core d := by simp only [own, hr]
    rw [e]
    unfold nodeRepl at h
    by_cases hd : d = c
    · rw [if_pos hd] at h; cases h
    exact Or.inr ⟨d, hd, rfl⟩
  | slot p => rw [hr] at h; cases h
  | ntfn p => rw [hr] at h; cases h
  | obj p => rw [hr] at h; cases h
  | none => rw [hr] at h; cases h

theorem repl_own {K : KLayout} {c : U64} {m : U64 → U64} {b w : U64} (h : repl K c m b = some w) :
    own K m b = .gate ∨ ∃ d, d ≠ c ∧ own K m b = .core d :=
  repl2_own h

/-- A rewritten word lies in a TCB, an SC or a node. -/
theorem repl2_region {K : KLayout} {c : U64} {m : U64 → U64} {v b w : U64} (h : repl2 K c m v b = some w) :
    region K b ≠ .none := by
  intro hr
  unfold repl2 at h
  rw [hr] at h; cases h

/-- Words owned by core `c` or a lock are not rewritten. -/
theorem repl2_none_of_own {K : KLayout} {c : U64} {m : U64 → U64} {v b : U64}
    (ho : own K m b = .core c ∨ ∃ l, own K m b = .lock l) : repl2 K c m v b = none := by
  cases hr : repl2 K c m v b with
  | none => rfl
  | some w =>
    exfalso
    rcases repl2_own hr with hg | ⟨d, hd, hd'⟩
    · rcases ho with ho | ⟨l, ho⟩ <;> rw [hg] at ho <;> cases ho
    · rcases ho with ho | ⟨l, ho⟩ <;> rw [hd'] at ho <;> cases ho
      exact hd rfl

/-- **`c`'s view keeps every word owned by core `c` or by a lock.** -/
theorem view_eq_of_own {K : KLayout} {c : U64} {m : U64 → U64} {b : U64}
    (ho : own K m b = .core c ∨ ∃ l, own K m b = .lock l) : view K c m b = m b :=
  view_none (repl2_none_of_own ho)

/-! ## The view's scheduler words -/

/-- **At `c`'s view every TCB of the heap is homed on `c`** (P3 `SchedCore.aff` at the view; module docstring). -/
theorem view_aff {K : KLayout} (hK : RegionOK K) {t : U64} (ht : K.heap t = some .tcb) (c : U64)
    (m : U64 → U64) : view K c m (fld t oAFFINITY) = c := by
  obtain ⟨hr, ho⟩ := hK.tcb t ht oAFFINITY (Or.inl rfl)
  by_cases ha : m (fld t oAFFINITY) = c
  · have : repl K c m (fld t oAFFINITY) = none := by
      simp only [repl, repl2, hr, tcbRepl, if_pos ha]
    rw [view_none this, ha]
  · have : repl K c m (fld t oAFFINITY) = some c := by
      simp only [repl, repl2, hr, tcbRepl, if_neg ha]
      rw [if_pos (by rw [ho, oAFF_val])]
    exact view_some this

/-- **At `c`'s view every SC is on core `c`** (P3 `SchedRel.core` at the view). -/
theorem view_sc_core {K : KLayout} (hK : RegionOK K) {p b : U64} (hb : region K b = .sc p) (c : U64)
    (m : U64 → U64) : view K c m (fld p 16#u64) = c := by
  obtain ⟨hr, hv⟩ := hK.scw p b hb
  by_cases ha : m (fld p 16#u64) = c
  · have : repl K c m (fld p 16#u64) = none := by
      simp only [repl, repl2, hr, scRepl, if_pos ha]
    rw [view_none this, ha]
  · have : repl K c m (fld p 16#u64) = some c := by
      simp only [repl, repl2, hr, scRepl, if_neg ha]
      rw [if_pos (by omega)]
    exact view_some this

/-- The words of a thread homed on `c` are unchanged. -/
theorem view_home {K : KLayout} {c : U64} {m : U64 → U64} {b t : U64} (hb : region K b = .tcb t)
    (ha : m (fld t oAFFINITY) = c) : view K c m b = m b :=
  view_none (by simp only [repl, repl2, hb, tcbRepl, if_pos ha])

/-- The words of an SC on `c` are unchanged. -/
theorem view_sc_home {K : KLayout} {c : U64} {m : U64 → U64} {b p : U64} (hb : region K b = .sc p)
    (ha : m (fld p 16#u64) = c) : view K c m b = m b :=
  view_none (by simp only [repl, repl2, hb, scRepl, if_pos ha])

/-- `c`'s own node is unchanged. -/
theorem view_node_self {K : KLayout} {c : U64} {m : U64 → U64} {b : U64} (hb : region K b = .node c) :
    view K c m b = m b :=
  view_none (by simp [repl, repl2, hb, nodeRepl])

/-- Another core's queue words read empty. -/
theorem view_node_other {K : KLayout} {c d : U64} {m : U64 → U64} {b : U64} (hb : region K b = .node d)
    (hd : d ≠ c) (hq : QWord (nodeOff K d b)) : view K c m b = 0#u64 :=
  view_some (by simp only [repl, repl2, hb, nodeRepl, if_neg hd, if_pos hq])

/-- Another core's thread: its `SC`, `IN_QUEUES` and debug links read 0. -/
theorem view_tzero {K : KLayout} {c : U64} {m : U64 → U64} {b t : U64} (hb : region K b = .tcb t)
    (ha : m (fld t oAFFINITY) ≠ c) (ho : TZero (b.val - t.val)) : view K c m b = 0#u64 := by
  have h1 : b.val - t.val ≠ 3520 := by unfold TZero at ho; omega
  exact view_some (by simp only [repl, repl2, hb, tcbRepl, if_neg ha, if_neg h1, if_pos ho])

/-- Another core's thread is not running, restarting, idle or in a VM in `c`'s view. -/
theorem view_state {K : KLayout} {c : U64} {m : U64 → U64} {b t : U64} (hb : region K b = .tcb t)
    (ha : m (fld t oAFFINITY) ≠ c) (ho : b.val - t.val = 3328) : ¬ Hidden (view K c m b) := by
  have h1 : b.val - t.val ≠ 3520 := by omega
  have h2 : ¬ TZero (b.val - t.val) := by unfold TZero; omega
  by_cases hh : Hidden (m b)
  · have : repl K c m b = some 0#u64 := by
      simp only [repl, repl2, hb, tcbRepl, if_neg ha, if_neg h1, if_neg h2]
      rw [if_pos ⟨ho, hh⟩]
    rw [view_some this]; unfold Hidden; simp
  · have : repl K c m b = none := by
      simp only [repl, repl2, hb, tcbRepl, if_neg ha, if_neg h1, if_neg h2]
      rw [if_neg (fun h => hh h.2)]
    rw [view_none this]; exact hh

/-- **The view is idempotent.** -/
theorem view_idem {K : KLayout} (hK : RegionOK K) (c : U64) (m : U64 → U64) :
    view K c (view K c m) = view K c m := by
  funext b
  cases hr : region K b with
  | tcb t =>
    have ha := view_aff hK (hK.tcbOf t b hr) c m
    exact view_none (by simp only [repl, repl2, hr, tcbRepl, if_pos ha])
  | sc p =>
    have ha := view_sc_core hK hr c m
    exact view_none (by simp only [repl, repl2, hr, scRepl, if_pos ha])
  | node d =>
    unfold view repl repl2
    simp only [hr]
    cases nodeRepl K c d b <;> rfl
  | slot p => exact view_none (by simp only [repl, repl2, hr])
  | ntfn p => exact view_none (by simp only [repl, repl2, hr])
  | obj p => exact view_none (by simp only [repl, repl2, hr])
  | none => exact view_none (by simp only [repl, repl2, hr])

/-! ## Steps and the view -/

/-- Two memories with the same deciding words (`AFFINITY` of the TCBs, `CORE` of the SCs). -/
def DecEq (K : KLayout) (m m' : U64 → U64) : Prop :=
  (∀ t, K.heap t = some .tcb → m' (fld t oAFFINITY) = m (fld t oAFFINITY)) ∧
    ∀ p b, region K b = .sc p → m' (fld p 16#u64) = m (fld p 16#u64)

/-- **The replacement reads only the deciding words** (and the word's own value). -/
theorem repl2_decEq {K : KLayout} (hK : RegionOK K) {c : U64} {m m' : U64 → U64} (h : DecEq K m m')
    (v b : U64) : repl2 K c m' v b = repl2 K c m v b := by
  unfold repl2
  cases hr : region K b with
  | tcb t => simp only [tcbRepl, h.1 t (hK.tcbOf t b hr)]
  | sc p => simp only [scRepl, h.2 p b hr]
  | node d => rfl
  | slot p => rfl
  | ntfn p => rfl
  | obj p => rfl
  | none => rfl

/-- Writes with no gate-owned word keep the deciding words. -/
theorem decEq_mix {K : KLayout} (hK : RegionOK K) {W : Set U64} {m m₂ : U64 → U64}
    (hW : ∀ b ∈ W, own K m b ≠ .gate) : DecEq K m (mix W m₂ m) := by
  refine ⟨fun t ht => mix_nmem fun hb => hW _ hb (own_aff_gate hK ht m), fun p b hb => mix_nmem fun hx => ?_⟩
  obtain ⟨hr, hv⟩ := hK.scw p b hb
  exact hW _ hx (by simp only [own, hr]; rw [if_pos hv])

/-- **Another core's step changes `c`'s view only where it wrote** (writes with no gate-owned word). -/
theorem view_frame {K : KLayout} (hK : RegionOK K) (c : U64) {W : Set U64} {m m₂ : U64 → U64}
    (hW : ∀ b ∈ W, own K m b ≠ .gate) {x : U64} (hx : x ∉ W) : view K c (mix W m₂ m) x = view K c m x := by
  have e : repl K c (mix W m₂ m) x = repl K c m x := by
    unfold repl; rw [repl2_decEq hK (decEq_mix hK hW), mix_nmem hx]
  unfold view; rw [e, mix_nmem hx]

/-- **Core `c`'s step commutes with `c`'s view** (writes owned by `c` or by locks; module docstring). -/
theorem view_mix_own {K : KLayout} (hK : RegionOK K) (c : U64) {W : Set U64} {m m₂ : U64 → U64}
    (hW : ∀ b ∈ W, own K m b = .core c ∨ ∃ l, own K m b = .lock l) :
    view K c (mix W m₂ m) = mix W m₂ (view K c m) := by
  have hng : ∀ b ∈ W, own K m b ≠ .gate := by
    intro b hb hg; rcases hW b hb with h | ⟨l, h⟩ <;> rw [hg] at h <;> cases h
  funext x
  by_cases hx : x ∈ W
  · rw [mix_mem hx]
    have e : repl K c (mix W m₂ m) x = none := by
      unfold repl; rw [repl2_decEq hK (decEq_mix hK hng)]; exact repl2_none_of_own (hW x hx)
    rw [view_none e, mix_mem hx]
  · rw [mix_nmem hx]; exact view_frame hK c hng hx

/-! ## The layouts with VCPUs and PTEs (`ownP`) -/

/-- `ownP` is `own` on the TCBs, SCs and nodes (VCPU and PTE words lie in `own`'s `.none` region). -/
theorem ownP_eq_own {K : KLayoutP} (hK : RegionOKP K) {m : U64 → U64} {b : U64}
    (hb : region K.toKLayout b ≠ .none) : ownP K m b = own K.toKLayout m b := by
  rw [ownP_off (fun hp => hb (hK.none b hp)), ownV_off (fun ⟨v, hv⟩ => hb (hK.base.none v b hv))]

theorem repl_ownP {K : KLayoutP} (hK : RegionOKP K) {c : U64} {m : U64 → U64} {b w : U64}
    (h : repl K.toKLayout c m b = some w) : ownP K m b = .gate ∨ ∃ d, d ≠ c ∧ ownP K m b = .core d := by
  rw [ownP_eq_own hK (repl2_region h)]; exact repl_own h

theorem view_eq_of_ownP {K : KLayoutP} (hK : RegionOKP K) {c : U64} {m : U64 → U64} {b : U64}
    (ho : ownP K m b = .core c ∨ ∃ l, ownP K m b = .lock l) : view K.toKLayout c m b = m b := by
  cases hr : repl K.toKLayout c m b with
  | none => exact view_none hr
  | some w =>
    exfalso
    rcases repl_ownP hK hr with hg | ⟨d, hd, hd'⟩
    · rcases ho with ho | ⟨l, ho⟩ <;> rw [hg] at ho <;> cases ho
    · rcases ho with ho | ⟨l, ho⟩ <;> rw [hd'] at ho <;> cases ho
      exact hd rfl

theorem decEq_mixP {K : KLayoutP} (hK : RegionOKP K) {W : Set U64} {m m₂ : U64 → U64}
    (hW : ∀ b ∈ W, ownP K m b ≠ .gate) : DecEq K.toKLayout m (mix W m₂ m) := by
  have hB := hK.base.base
  refine ⟨fun t ht => mix_nmem fun hb => ?_, fun p b hb => mix_nmem fun hx => ?_⟩
  · obtain ⟨hr, -⟩ := hB.tcb t ht oAFFINITY (Or.inl rfl)
    exact hW _ hb (by rw [ownP_eq_own hK (by rw [hr]; intro h; cases h)]; exact own_aff_gate hB ht m)
  · obtain ⟨hr, hv⟩ := hB.scw p b hb
    exact hW _ hx (by rw [ownP_eq_own hK (by rw [hr]; intro h; cases h)]; simp only [own, hr]; rw [if_pos hv])

/-- `view_frame` for `ownP`. -/
theorem view_frameP {K : KLayoutP} (hK : RegionOKP K) (c : U64) {W : Set U64} {m m₂ : U64 → U64}
    (hW : ∀ b ∈ W, ownP K m b ≠ .gate) {x : U64} (hx : x ∉ W) :
    view K.toKLayout c (mix W m₂ m) x = view K.toKLayout c m x := by
  have e : repl K.toKLayout c (mix W m₂ m) x = repl K.toKLayout c m x := by
    unfold repl; rw [repl2_decEq hK.base.base (decEq_mixP hK hW), mix_nmem hx]
  unfold view; rw [e, mix_nmem hx]

/-- **`view_mix_own` for `ownP`**: core `c`'s step (writes owned by `c` or by locks, PTE locks included) commutes
with `c`'s view. -/
theorem view_mix_ownP {K : KLayoutP} (hK : RegionOKP K) (c : U64) {W : Set U64} {m m₂ : U64 → U64}
    (hW : ∀ b ∈ W, ownP K m b = .core c ∨ ∃ l, ownP K m b = .lock l) :
    view K.toKLayout c (mix W m₂ m) = mix W m₂ (view K.toKLayout c m) := by
  have hng : ∀ b ∈ W, ownP K m b ≠ .gate := by
    intro b hb hg; rcases hW b hb with h | ⟨l, h⟩ <;> rw [hg] at h <;> cases h
  funext x
  by_cases hx : x ∈ W
  · rw [mix_mem hx]
    have e : repl K.toKLayout c (mix W m₂ m) x = none := by
      unfold repl; rw [repl2_decEq hK.base.base (decEq_mixP hK hng), mix_mem hx]
      cases hr : repl2 K.toKLayout c m (m₂ x) x with
      | none => rfl
      | some w =>
        exfalso
        have hreg := repl2_region hr
        rcases repl2_own hr with hg | ⟨d, hd, hd'⟩
        · rw [← ownP_eq_own hK hreg] at hg
          rcases hW x hx with ho | ⟨l, ho⟩ <;> rw [hg] at ho <;> cases ho
        · rw [← ownP_eq_own hK hreg] at hd'
          rcases hW x hx with ho | ⟨l, ho⟩ <;> rw [hd'] at ho <;> cases ho
          exact hd rfl
    rw [view_none e, mix_mem hx]
  · rw [mix_nmem hx]; exact view_frameP hK c hng hx

/-- **Every core's view of one memory homes every TCB on that core** (`view_aff` at each core): the equation
`GlueCross.slJAt_aff` imposes at a chain state of core `c` holds of `view K c μ` for every `μ` and every `c`, so two
cores' views of one memory are not refuted by `GlueCross.chain_cpu_eq`'s argument. -/
theorem views_aff {K : KLayout} (hK : RegionOK K) (μ : U64 → U64) {t : U64} (ht : K.heap t = some .tcb) :
    ∀ c d : U64, view K c μ (fld t oAFFINITY) = c ∧ view K d μ (fld t oAFFINITY) = d :=
  fun c d => ⟨view_aff hK ht c μ, view_aff hK ht d μ⟩

end

end Fl4Proofs.P2.CoreView
