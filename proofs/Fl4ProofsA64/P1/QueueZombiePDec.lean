/-
P1 (aarch64, gen 37): **the CNode `Delete` decode over the `ZS` and `ZP` loops** — gen 36's open item: QueueSlotTyDecV's
`del_genV` hands its callback `OSKeep`, the words outside the TCBs and nodes and the idle word, but not the idle
thread's `SC` field `scA I`, which the `ZS` domain's SC clause (`p ≠ Is`) is stated against.

* **`JV.restartS`**: the decode's restart (`set_thread_state(cur, TS_RESTART)`, QueueSlotTyDec's `sts_fine`: the
  current thread's `STATE` word and the node's `SCHED_ACTION` word) also keeps every thread's `SC` field (`ScK`).
* `cnode_del_genS`, `cnode.decode.del_genS`, **`syscall.decode_invocation.del_genS`**: QueueSlotTyDecV's
  `del_genV` texts with `ScK` handed to the callback as well.
* Instances: **`syscall.decode_invocation.del_zs`** (the `ZS` loop from the decode start: domain and target stated
  at the decode's start state, its idle word and idle `SC` field), **`syscall.decode_invocation.del_zp`** (the `ZP`
  loop: `VsTy` at the decode start is kept by the restart — its words are outside the TCBs and nodes).

Case hypotheses at the decode start (as gen 33–36's decode instances): the domain facts, `TgtP` of the target's
case. No named premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueZombieP
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

section decs
variable {OS Vc Ub : Set U64}

/-- **The decode's restart over `JV`** with gen 33's restart frame and every thread's `SC` field kept. -/
theorem JV.restartS (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
      (JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 ∧ OSKeep st OS s s1 ∧
        (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) ∧ L.idleW s1 = L.idleW s) ∧ ScK st T s s1 ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  have hct : L.curW s ∈ T := q.curT
  refine WP.spec_and (JV.restartI hO hV D hT hv) (WP.spec_mono (sts_fine s _ sched.TS_RESTART (q.nodes _ q.cur)
    (q.tcbs _ hct)) fun s1 w => ScK.of_w q.tcbs w fun z hz hb => ?_)
  rcases hb with e | e
  · exact field_ne (q.tcbs z hz) (q.tcbs _ hct) (K1 := 3464#u64) (K2 := 3328#u64) (by simp) (by simp)
      (fun _ => by first | decide | simp | omega) (by rw [← scA_eq, ← stA_eq]; exact e)
  · exact node_ne_field (o := layout.node.SCHED_ACTION) (q.nodes _ q.cur)
      (by first | (rw [act_val]; omega) | decide | (simp [layout.node.SCHED_ACTION]; done)) hz (q.tcbs z hz)
      (K := 3464#u64) (by simp) (by rw [← scA_eq]; exact e.symm)

/-- The restart, then the exposed `cdt.delete` of a slot, over `JV` (callback with `ScK`). -/
theorem cnode_del_genS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} {a : A} {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hG : ∀ s1, JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s → ScK st T s s1 →
      cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
          VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  WP.spec_bind (JV.restartS hO hV D hT hv) fun s1 h1 =>
    WP.spec_mono (hG s1 h1.1.1 h1.1.2.1 h1.1.2.2.1 h1.1.2.2.2 h1.2) fun r hr => by
      obtain ⟨r', s', a'⟩ := r; exact ⟨hr.1.1.post, hr.1.2, hr.2⟩

set_option hygiene false in
local macro "eleafS" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 ⟨D.err _, hT, hv⟩
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     exact (WP.spec_ok _).2 ⟨D.err _, hT, hv⟩))

set_option maxHeartbeats 2000000 in
/-- **`cnode.decode` of `CNodeDelete` over `JV`** (QueueSlotTyDecV's `cnode.decode.del_genV` text, callback with
`ScK`). -/
theorem cnode.decode.del_genS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (c : capability.Cap) (hc : RootOK OS c) {P : U64 → Prop} (hk : TgtP st P s c buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s → ScK st T s s1 →
      cdt.delete st ar s1 a x true ⦃ r => JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s r.2.1 ⦄) :
    cnode.decode st ar s a fl4_abi.label.CNodeDelete len c buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cnode.decode
  simp only [error.illegal, error.truncated, bind_ok]
  split
  · eleafS
  split
  · eleafS
  split
  · eleafS
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
    eleafS
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  split
  · rename_i h; exact absurd h lbl_c1
  split
  · rename_i h; exact absurd h lbl_c2
  split
  · exact cnode_del_genS hO hV D hT hv (hG v (hr.1 v rfl) (hk idx dep v hidx.1 hdep.1 hr.2.1))
  · rename_i h; first | exact absurd rfl h | exact absurd trivial h | simp at h

set_option maxHeartbeats 2000000 in
/-- **The CNode `Delete` invocation over `JV`, decode level, generic in the target's case `P`** (the callback with
`ScK`). -/
theorem syscall.decode_invocation.del_genS {A : Type _} {ar : machine.Arch A} (hO : OSOK T Ω Sg OS)
    (hV : VcOK T Scs Z OS Vc Ub)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    {P : U64 → Prop} (hk : TgtP st P s cap buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) → L.idleW s1 = L.idleW s → ScK st T s s1 →
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
  · exact cnode.decode.del_genS hO hV a len buf D hT hv _ hR hk hG

/-! ## The `ZS` and `ZP` loops at decode level -/

variable {Dm Fp : Set U64}

/-- **The `ZS` loop at decode level**: the CNode `Delete` of a target slot of `OS` (no IRQ-node slot) whose cap is
`ZS` over a canonical domain `Dm ⊆ OS` of `ZS` caps, both stated at the decode's start state (its idle word and the
idle thread's `SC` field), keeps `SlotTy` and `VcTy` with `DecPost`. -/
theorem syscall.decode_invocation.del_zs {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : Dm ⊆ OS) (hDC : DCan Dm)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hW : WuApart OS (L.ksb s)) (hIO : IrqOK OS Dm (L.ksb s))
    (hap : IrqStApart OS (L.ksb s)) (hN : IrqN st (L.ksb s) s)
    (hD : DomS st Vc Dm Scs (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XS st Vc Dm Scs (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧ ¬ IslN (L.ksb s) x) s
      cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genS hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 _ i1 K1 => by
      have hIT : L.idleW s ∈ T := D.bxi.1.choose_spec.choose_spec.idleT
      exact cdt.delete.zsI hP hO hA hV hDO hDC hW hIO hap h1 hx hkx.2 (hD.oka hIO.2 hDO (OKA.of_osk k1))
        (hkx.1.oka hx hkx.2 (OKA.of_osk k1)) i1 (K1 _ hIT) (hN.oka hIO (OKA.of_osk k1))

/-- **The `ZP` loop at decode level** (frames and VSpace roots at frame positions of the domain; `VsTy` at the
decode start). -/
theorem syscall.decode_invocation.del_zp {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS) (hV : VcOK T Scs Z OS Vc Ub) (hDO : Dm ⊆ OS) (hDC : DCan Dm)
    {Pp Tb Pt : Set U64} {Lv : U64 → Nat} (hPp : Pp ⊆ Pt) (hTb : Tb ⊆ Pt)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (hR : VrOK Ω Sg Scs Z OS Vc Ub (L.ksb s) Pt)
    (hW : WuApart OS (L.ksb s)) (hIO : IrqOK OS Dm (L.ksb s))
    (hap : IrqStApart OS (L.ksb s)) (hN : IrqN st (L.ksb s) s) (hY : VsTy st (L.ksb s) Pp Tb Lv s)
    (hD : DomP st Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => XP st Vc Dm Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x s ∧
      ¬ IslN (L.ksb s) x) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ∧
        VcTy st T Cs Ω H Sg Scs Z Vc Ub s' ⦄ :=
  syscall.decode_invocation.del_genS hO hV a len slot cap blk call don fp buf extra D hT hv hf hslot hcap hk
    fun x hx hkx s1 h1 k1 o1 i1 K1 => by
      have q := D.bxi.1.choose_spec.choose_spec
      have hIT : L.idleW s ∈ T := q.idleT
      have hY1 : VsTy st (L.ksb s) Pp Tb Lv s1 :=
        hY.keepZ hPp hTb (VsZ.of_keep fun b hb => o1 b (q.omega _ (hR.om b hb)))
      exact cdt.delete.zpI hP hO hA hV hDO hDC hPp hTb hR hW hIO hap h1 hx hkx.2
        (hD.oka hIO.2 hDO (OKA.of_osk k1)) (hkx.1.oka hx hkx.2 (OKA.of_osk k1)) i1 (K1 _ hIT)
        (hN.oka hIO (OKA.of_osk k1)) hY1

end decs

end ST
end R
end W7

end

end Fl4ProofsA64.P1
