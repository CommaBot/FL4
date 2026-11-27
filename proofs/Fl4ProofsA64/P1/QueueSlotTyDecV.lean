/-
P1 (aarch64, gen 33): **the CNode `Delete` decode over `JV`**: gen 31–32's generic decode (QueueSlotTyDec2 /
QueueSlotTyDec3, `del_genI`) with `VcTy` carried, and its instances for every kind covered over `JV`.

* `JV.restartI`: the decode's restart starts `JV` (QueueVcTyEnt's `JV.restart`) with gen 32's restart frame
  (every `OS` word, every word outside the TCBs and nodes, the idle-thread word kept);
* `cnode_del_genV`, `cnode.decode.del_genV`, **`syscall.decode_invocation.del_genV`**: post
  `DecPost ∧ SlotTy ∧ VcTy` at the end state, for a deletion that keeps `JV` from every state the restart
  reaches;
* instances (post `DecPost ∧ SlotTy ∧ VcTy`): **`del_fintrivV`**, **`del_eprnV`**, **`del_scV`**, **`del_irqV`**,
  **`del_zv`** (a Zombie / thread / CNode / leaf target over a leaf domain `D`: QueueZombieV), and on the entry
  facts **`delV_ent`** (the four `SlotTyEntV` kinds, [J] `SlotTyEntV`) and **`del_zv_ent`** ([J] `SlotTyEntZ`).

Case hypotheses only (facts of the decode start: `TgtP` of the target's case; for `del_zv` the domain `D ⊆ OS`
leaf-typed and the target `XOK`); no new premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueIrqV
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

section decv
variable {OS Vc Ub : Set U64}

/-- **The decode's restart over `JV`**, with the restart frame. -/
theorem JV.restartI (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
      JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧ OSKeep st OS s s1 ∧
        (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) ∧ L.idleW s1 = L.idleW s ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  have hct : L.curW s ∈ T := q.curT
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  refine WP.spec_mono (WP.spec_and (J.restartI hO D hT) (sts_fine s _ sched.TS_RESTART (q.nodes _ q.cur)
    (q.tcbs _ hct))) fun s1 hh => ⟨⟨hh.1.1, hv.keepZ (DS.sts hO hV q hW hct hh.2).2⟩, hh.1.2.1, hh.1.2.2.1,
      hh.1.2.2.2⟩

/-- The restart, then the exposed `cdt.delete` of a slot, over `JV`. -/
theorem cnode_del_genV {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} {a : A} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hG : ∀ s1, JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s →
      cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
          VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  WP.spec_bind (JV.restartI hO hV D hT hv) fun s1 h1 =>
    WP.spec_mono (hG s1 h1.1 h1.2.1 h1.2.2.1 h1.2.2.2) fun r hr => by
      obtain ⟨r', s', a'⟩ := r; exact ⟨hr.1.1.post, hr.1.2, hr.2⟩

set_option hygiene false in
local macro "eleafV" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 ⟨D.err _, hT, hv⟩
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     exact (WP.spec_ok _).2 ⟨D.err _, hT, hv⟩))

set_option maxHeartbeats 4000000 in
/-- `cnode.decode` at `CNodeDelete` over `JV`, generic in the target's case `P`. -/
theorem cnode.decode.del_genV {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (c : capability.Cap) (hc : RootOK OS c) {P : U64 → Prop} (hk : TgtP st P s c buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s →
      cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) :
    cnode.decode st ar s a fl4_abi.label.CNodeDelete len c buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · eleafV
  split
  · eleafV
  split
  · eleafV
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
    eleafV
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  split
  · rename_i h; exact absurd h lbl_c1
  split
  · rename_i h; exact absurd h lbl_c2
  split
  · exact cnode_del_genV hO hV D hT hv (hG v (hr.1 v rfl) (hk idx dep v hidx.1 hdep.1 hr.2.1))
  · rename_i h; first | exact absurd rfl h | exact absurd trivial h | simp at h

set_option maxHeartbeats 2000000 in
/-- **The CNode `Delete` invocation over `JV`, decode level, generic in the target's case `P`.** -/
theorem syscall.decode_invocation.del_genV {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    {P : U64 → Prop} (hk : TgtP st P s cap buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s →
      cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have hR := RootOK.of_slot hT hslot hcap
  cases cap <;> simp [capFam] at hf
  unfold syscall.decode_invocation
  step with sched.cur_thread.spec as ⟨ct, _⟩
  try dsimp only
  split
  · exact (WP.spec_ok _).2 ⟨DecPost.keep D.bxi (by simp), hT, hv⟩
  · exact cnode.decode.del_genV hO hV a len buf D hT hv _ hR hk hG

/-! ## Instances -/

/-- `XOK` across a step that keeps the `OS` words and the idle-thread word. -/
theorem XOK.keep {D : Set U64} {s s1 : S} {x : U64} (hx : x ∈ OS) (k : OSKeep st OS s s1)
    (hi : L.idleW s1 = L.idleW s) (hX : XOK st D x s) : XOK st D x s1 := fun c hc => by
  rw [k.cap hx] at hc
  rw [hi]
  exact hX c hc

/-- **The CNode `Delete` of a `FinTriv` target over `JV`.** -/
theorem syscall.decode_invocation.del_fintrivV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => CapFinTrivAt st x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have hb := D.bxi
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  refine syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk ?_
  intro x hx hkx s1 h1 k1 o1 _
  exact cdt.delete.fintrivV hP hO hV h1 hx (CapFinTrivAt.keep q hX.1 hSg.sub hT hx k1 o1 hkx)

/-- **The CNode `Delete` of an endpoint / notification / reply target over `JV`** (any finality). -/
theorem syscall.decode_invocation.del_eprnV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => EpNtRpAt st x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 _ _ => cdt.delete.eprnV hP hO hA hV h1 hx (hkx.keep hx k1)

/-- **The CNode `Delete` of an SC target over `JV`** (any finality). -/
theorem syscall.decode_invocation.del_scV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => ScPlAt st Scs x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have hb := D.bxi
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  refine syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk ?_
  intro x hx hkx s1 h1 k1 o1 i1
  exact cdt.delete.scV hP hO hA hV h1 hx (ScPlAt.keep q hX.1 hSg.sub hx k1 o1 i1 hkx)

/-- **The CNode `Delete` of an IrqHandler target over `JV`** (final or not), under `IrqStApart`. -/
theorem syscall.decode_invocation.del_irqV {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hap : IrqStApart OS (L.ksb s))
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => IrqAt st OS x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have hb := D.bxi
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  refine syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk ?_
  intro x hx hkx s1 h1 k1 o1 _
  have hks : L.ksb s1 = L.ksb s := h1.ksb
  obtain ⟨irq, hc, hi⟩ := IrqAt.keep q hX.1 hSg.sub hT hx k1 o1 hks hkx
  exact cdt.delete.irqV hP hO hV h1 hx hc hi hap

/-- **The CNode `Delete` of a Zombie / thread / CNode / leaf target over a leaf domain, over `JV`** (QueueZombieV;
any finality), under `ScApart` and `WuApart`: the domain `D ⊆ OS` leaf-typed and the target `XOK` at the decode
start. -/
theorem syscall.decode_invocation.del_zv {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) {Dm : Set U64} (hDO : Dm ⊆ OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hW : WuApart OS (L.ksb s)) (hD : DomL st Dm s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XOK st Dm x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genV hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 _ i1 => cdt.delete.zv hP hO hA hV hDO hW h1 hx (hD.osk hDO k1) (hkx.keep hx k1 i1)

end decv

/-! ## On the entry facts -/

/-- **The `JV` decode instances on [J] `SlotTyEntV`**: at an `EntAt` decode start there are placed, typed ghost
sets for which the CNode `Delete` of a `FinTriv`, endpoint / notification / reply, SC or IrqHandler target keeps
the invariants, `SlotTy` and `VcTy`; no apartness hypothesis is left. -/
theorem syscall.decode_invocation.delV_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntV st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64),
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        (TgtP st (fun x => CapFinTrivAt st x s) s cap buf ∨ TgtP st (fun x => EpNtRpAt st x s) s cap buf ∨
          TgtP st (fun x => ScPlAt st Scs x s) s cap buf ∨ TgtP st (fun x => IrqAt st OS x s) s cap buf) →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, hap, hA, hV, hv⟩ := hJ.entAt hE q.tcbs
  refine ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf hf hs hc hk => ?_⟩
  rcases hk with hk | hk | hk | hk
  · exact syscall.decode_invocation.del_fintrivV hP hO hV a len slot cap blk call don fp buf extra D hT hv hf hs hc hk
  · exact syscall.decode_invocation.del_eprnV hP hO hA hV a len slot cap blk call don fp buf extra D hT hv hf hs hc hk
  · exact syscall.decode_invocation.del_scV hP hO hA hV a len slot cap blk call don fp buf extra D hT hv hf hs hc hk
  · exact syscall.decode_invocation.del_irqV hP hO hV a len slot cap blk call don fp buf extra D hT hv hap hf hs hc hk

/-- **The Zombie / thread / CNode decode on [J] `SlotTyEntZ`**: no apartness hypothesis left; the case hypotheses
are the leaf domain and the target's `XOK` at the decode start. -/
theorem syscall.decode_invocation.del_zv_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntZ st T Cs Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS Vc Ub, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧ VcTy st T Cs Ω H Sg Scs Z Vc Ub s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64) (Dm : Set U64),
        Dm ⊆ OS → DomL st Dm s → capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => XOK st Dm x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
            VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  obtain ⟨OS, Vc, Ub, hO, hT, -, -, hA, hV, hv, hW⟩ := hJ.entAt hE q.tcbs
  exact ⟨OS, Vc, Ub, hO, hT, hv, fun a len slot blk call don fp buf Dm hDO hD hf hs hc hk =>
    syscall.decode_invocation.del_zv hP hO hA hV hDO a len slot cap blk call don fp buf extra D hT hv hW hD hf hs hc hk⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
