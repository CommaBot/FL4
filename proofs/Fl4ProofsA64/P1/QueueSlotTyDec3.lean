/-
P1 (aarch64, gen 32): **the CNode `Delete` decode for SchedContext and IrqHandler targets** over `SlotTy`.

Gen 31's generic decode (`syscall.decode_invocation.del_gen`, QueueSlotTyDec2) carries the target's case across
the decode's restart through `OSKeep` and the words outside the TCBs and nodes. The two remaining cases read more:

* **SchedContext** (`ScPlAt x s`, QueueSlotTySc): the slot's cap (an `OS` word), the SC's `TCB` word `scTcbA p` (a
  word of `Ω`, `objs_omega`, so outside the TCBs and nodes, `SchedQueuesInvX.omega`) and the **idle thread word**
  `idleW`, a node word (the current core's `IDLE_THREAD`, offset 8). The restart writes the caller's `STATE` word
  and at most the current core's `SCHED_ACTION` word (offset 16; `sts_fine`), so it keeps `idleW`
  (**`restart_idle`**). The generic decode is restated with this one more conjunct in the restart frame
  (`J.restartI`, `cnode_del_genI`, `cnode.decode.del_genI`, **`syscall.decode_invocation.del_genI`**), then
  `ScPlAt.keep`, **`syscall.decode_invocation.del_sc`** (under `ScApart`) and
  **`syscall.decode_invocation.del_sc_ent`** (from [J] `SlotTyEntS`, no apartness hypothesis left).
* **IrqHandler** (`IrqAt x s`: the slot holds `IrqHandler irq` and the IRQ node slot `irqSlotA (ks s) irq` is
  `IslTriv`, QueueSlotTyIrq): reads the slot's cap, the IRQ node slot's cap and finality (`OS` words,
  `is_final.keep`), its `FinTriv` case (`FinTriv.keep`) and the `ks` base (kept by every write, `WritesIn`). So gen
  31's generic decode applies unchanged: `IrqAt.keep`, **`syscall.decode_invocation.del_irq`** (under
  `IrqStApart OS (ks s)`) and **`syscall.decode_invocation.del_irq_ent`** (from [J] `SlotTyEntI`).

Case hypotheses only (facts of the decode start, read through `TgtP`); no new named premise; no existing
statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotTyDec2
import Fl4ProofsA64.P1.QueueSlotTySc
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

/-! ## The restart keeps the idle-thread word -/

/-- **The decode's restart keeps the idle thread word** (`IDLE_THREAD`, node offset 8; the restart writes the
caller's `STATE` and the `SCHED_ACTION` word, offset 16). -/
theorem restart_idle {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s s1 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s Q R)
    (hw : WritesIn st s s1 (fun b => b = stA (L.curW s) ∨ b = L.nodeAt s (L.cpu s) layout.node.SCHED_ACTION)) :
    L.idleW s1 = L.idleW s := by
  have hN := q.nodes _ q.cur
  have hct : L.curW s ∈ T := q.curT
  have h8 : layout.node.IDLE_THREAD.val < 4288 := by rw [idle8]; omega
  unfold LawfulStore.idleW
  rw [hw.2.1, nodeAt_of_ksb hw.1]
  refine hw.mem_eq (nodeAt_aligned hN h8 (by rw [idle8])) fun hb => ?_
  rcases hb with e | e
  · rw [stA_eq] at e
    exact node_ne_field hN h8 hct (q.tcbs _ hct) (K := 3328#u64) (by simp) e
  · exact nodeAt_ne hN h8 (by rw [act_val]; omega) (by rw [idle8, act_val]; omega) e

/-- **The decode's restart**: gen 31's `J.restartW` and the idle thread word kept. -/
theorem J.restartI {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
      J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 ∧ OSKeep st OS s s1 ∧
        (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) ∧ L.idleW s1 = L.idleW s ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  have hct : L.curW s ∈ T := q.curT
  refine WP.spec_mono (WP.spec_and (J.restartW hO D hT) (sts_fine s _ sched.TS_RESTART (q.nodes _ q.cur)
    (q.tcbs _ hct))) fun s1 hh => ⟨hh.1.1, hh.1.2.1, hh.1.2.2, restart_idle q hh.2⟩

/-! ## The generic decode with the idle word in the restart frame -/

/-- The restart, then the exposed `cdt.delete` of a slot of `OS` (gen 31's `cnode_del_gen` with `idleW` kept). -/
theorem cnode_del_genI {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {a : A}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hG : ∀ s1, J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s →
      cdt.delete st ar s1 a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s r.2.1 ⦄) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ :=
  WP.spec_bind (J.restartI hO D hT) fun s1 h1 =>
    WP.spec_mono (hG s1 h1.1 h1.2.1 h1.2.2.1 h1.2.2.2) fun r hr => by
      obtain ⟨r', s', a'⟩ := r; exact ⟨hr.1.post, hr.2⟩

set_option hygiene false in
local macro "eleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 ⟨D.err _, hT⟩
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     exact (WP.spec_ok _).2 ⟨D.err _, hT⟩))

set_option maxHeartbeats 4000000 in
/-- `cnode.decode` at `CNodeDelete`, generic in the target's case `P` (gen 31's `cnode.decode.del_gen` with
`idleW` kept by the restart). -/
theorem cnode.decode.del_genI {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (c : capability.Cap) (hc : RootOK OS c) {P : U64 → Prop} (hk : TgtP st P s c buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s →
      cdt.delete st ar s1 a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s r.2.1 ⦄) :
    cnode.decode st ar s a fl4_abi.label.CNodeDelete len c buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · eleaf
  split
  · eleaf
  split
  · eleaf
  step with sched.cur_thread.spec as ⟨ct, ect⟩
  have e : ct = L.curW s := ect
  subst e
  refine WP.spec_bind (spec_eqv (P0.msg.syscall_arg.p0 st s _ buf _ hS)) fun idx hidx => ?_
  refine WP.spec_bind (spec_eqv (P0.msg.syscall_arg.p0 st s _ buf _ hS)) fun dep hdep => ?_
  refine WP.spec_bind (WP.spec_and (lookup_tgt_in hT c hc idx dep)
    (spec_eqv (P0.cspace.lookup_target_slot.p0 st s c idx dep hS))) fun r hr => ?_
  rcases r with v | e
  swap
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    eleaf
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  split
  · rename_i h; exact absurd h lbl_c1
  split
  · rename_i h; exact absurd h lbl_c2
  split
  · exact cnode_del_genI hO D hT (hG v (hr.1 v rfl) (hk idx dep v hidx.1 hdep.1 hr.2.1))
  · rename_i h; first | exact absurd rfl h | exact absurd trivial h | simp at h

set_option maxHeartbeats 2000000 in
/-- **The CNode `Delete` invocation, decode level, generic in the target's case `P`**, the deletion given the
restart frame with `idleW` kept. -/
theorem syscall.decode_invocation.del_genI {A : Type _} {ar : machine.Arch A} {OS : Set U64}
    (hO : OSOK T Ω Sg OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    {P : U64 → Prop} (hk : TgtP st P s cap buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s →
      cdt.delete st ar s1 a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s r.2.1 ⦄) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hR := RootOK.of_slot hT hslot hcap
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨DecPost.keep D.bxi (by simp), hT⟩
  · exact cnode.decode.del_genI hO a len buf D hT _ hR hk hG

/-! ## SchedContext targets -/

/-- **`ScPlAt` across the restart**: the slot's cap (an `OS` word), the SC's `TCB` word (a word of `Ω`, outside
the TCBs and nodes) and the idle thread word are kept. -/
theorem ScPlAt.keep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS : Set U64} {s s1 : S}
    {x : U64} (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hx : x ∈ OS) (k : OSKeep st OS s s1)
    (hout : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) (hi : L.idleW s1 = L.idleW s)
    (hk : ScPlAt st Scs x s) : ScPlAt st Scs x s1 := by
  intro c hc
  have hc0 : obj.Slot.cap st x s = ok c := by
    rw [DPF.slot_cap_dec, (k x hx).1, (k x hx).2.1, ← DPF.slot_cap_dec] at hc; exact hc
  obtain ⟨⟨p, b, rfl⟩, hpl⟩ := hk _ hc0
  refine ⟨⟨p, b, rfl⟩, And.intro (fun p' e => by cases e) (fun p' b' e => ?_)⟩
  have ep : p' = p := by simp only [capability.Cap.SchedContext.injEq] at e; exact e.1.symm
  rw [ep]
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p b rfl
  have e1 : L.mem s1 (scTcbA p) = L.mem s (scTcbA p) :=
    hout _ (q.omega _ ((objs_omega hob hsub).2 p hpS).1)
  refine ⟨hpS, hp0, fun h0 => ?_⟩
  rw [e1] at h0
  rw [e1, hi]
  exact hid h0

/-- **The CNode `Delete` of an SC target** (any finality), under `ScApart`: the target's cap is an SC cap with
P3's placement (`ScPlAt`) at the decode start. -/
theorem syscall.decode_invocation.del_sc {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    {OS : Set U64} (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => ScPlAt st Scs x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hb := D.bxi
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  refine syscall.decode_invocation.del_genI hO a len slot cap blk call don fp buf extra D hT hf hslot hcap hk ?_
  intro x hx hkx s1 h1 k1 o1 i1
  exact cdt.delete.sc hP hO hA h1 hx (ScPlAt.keep q hX.1 hSg.sub hx k1 o1 i1 hkx)

/-- **The SC decode on the entry fact** ([J] `SlotTyEntS`): no apartness hypothesis left. -/
theorem syscall.decode_invocation.del_sc_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntS st T Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64),
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => ScPlAt st Scs x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  obtain ⟨OS, hO, hT, -, -, hA⟩ := hJ.entAt hE
  exact ⟨OS, hO, hT, fun a len slot blk call don fp buf hf hs hc hk =>
    syscall.decode_invocation.del_sc hP hO hA a len slot cap blk call don fp buf extra D hT hf hs hc hk⟩

/-! ## IrqHandler targets -/

/-- The case of an IrqHandler target: the slot holds `IrqHandler irq` and the IRQ's node slot is `IslTriv`. -/
def IrqAt (st : machine.Store S) [L : LawfulStore st] (OS : Set U64) (x : U64) (s : S) : Prop :=
  ∃ irq, obj.Slot.cap st x s = ok (.IrqHandler irq) ∧ IslTriv st OS (irqSlotA (L.ksb s) irq) s

/-- **`IslTriv` across a step that keeps the `OS` words and the words outside the TCBs and nodes.** -/
theorem IslTriv.keep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS : Set U64} {s s1 : S}
    {isl : U64} (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (k : OSKeep st OS s s1)
    (hout : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) (hk : IslTriv st OS isl s) :
    IslTriv st OS isl s1 := by
  obtain ⟨hi, hk⟩ := hk
  refine ⟨hi, fun c fin hc hf => ?_⟩
  have hc0 : obj.Slot.cap st isl s = ok c := by
    rw [DPF.slot_cap_dec, (k isl hi).1, (k isl hi).2.1, ← DPF.slot_cap_dec] at hc; exact hc
  have hf0 : cdt.is_final_capability_with_cap st s isl c = ok fin := by
    rw [← is_final.keep hT k hi c]; exact hf
  have hty := (hT isl hi).1 c (by rw [DPF.slot_cap_dec] at hc0; exact hc0)
  obtain ⟨h1, h2⟩ := hk c fin hc0 hf0
  exact ⟨FinTriv.keep q hob hsub hty hout h1, h2⟩

/-- **`IrqAt` across such a step** (it also keeps the `ks` base). -/
theorem IrqAt.keep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS : Set U64} {s s1 : S}
    {x : U64} (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hx : x ∈ OS) (k : OSKeep st OS s s1)
    (hout : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) (hks : L.ksb s1 = L.ksb s)
    (hk : IrqAt st OS x s) : IrqAt st OS x s1 := by
  obtain ⟨irq, hc, hi⟩ := hk
  refine ⟨irq, ?_, ?_⟩
  · rw [DPF.slot_cap_dec, (k x hx).1, (k x hx).2.1, ← DPF.slot_cap_dec]; exact hc
  · rw [hks]; exact IslTriv.keep q hob hsub hT k hout hi

/-- **The CNode `Delete` of an IrqHandler target** (final or not), under `IrqStApart` at the decode start's `ks`
base: the target's case `IrqAt` at the decode start. -/
theorem syscall.decode_invocation.del_irq {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hap : IrqStApart OS (L.ksb s))
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => IrqAt st OS x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hb := D.bxi
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  refine syscall.decode_invocation.del_gen hO a len slot cap blk call don fp buf extra D hT hf hslot hcap hk ?_
  intro x hx hkx s1 h1 k1 o1
  have hks : L.ksb s1 = L.ksb s := h1.1.fr.1
  obtain ⟨irq, hc, hi⟩ := IrqAt.keep q hX.1 hSg.sub hT hx k1 o1 hks hkx
  exact cdt.delete.irq hP hO h1 hx hc hi hap

/-- **The IrqHandler decode on the entry fact** ([J] `SlotTyEntI`): no apartness hypothesis left. -/
theorem syscall.decode_invocation.del_irq_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntI st T Ω Sg H Rp Nt P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64),
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => IrqAt st OS x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  obtain ⟨OS, hO, hT, -, hap⟩ := hJ.entAt hE
  exact ⟨OS, hO, hT, fun a len slot blk call don fp buf hf hs hc hk =>
    syscall.decode_invocation.del_irq hP hO a len slot cap blk call don fp buf extra D hT hap hf hs hc hk⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
