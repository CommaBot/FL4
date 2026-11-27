/-
P1 (aarch64, gen 31): **the CNode `Delete` decode over `SlotTy` for the kinds whose case is read through the
finality or object words**: `FinTriv` targets and endpoint / notification / reply targets.

Gen 30's decode tops (QueueSlotTyDec) cover `TrivK` targets only: their case hypothesis `CapTrivAt` reads the
target slot's cap words alone, which the decode's restart keeps (`OSKeep`). Here:

* **`is_final.keep`**: `cdt.is_final_capability_with_cap` at `x ∈ OS` reads `x`'s `PREV` / `NEXT` words and the
  caps of the linked slots (cdt.rs 163–175; Funs.lean `cdt.is_final_capability_with_cap`). Under `SlotTy` the
  links are `0` or slots of `OS` (`LinkOK`, `NextOK`), and a `0` link's cap is not read; so the result is the same
  at any state with the same `OS` words.
* **`J.restartW`**: the decode's restart (`set_thread_state` of the caller, `sts_fine`: its `STATE` word and the
  current core's `SCHED_ACTION` word) also keeps every word outside the TCBs and the nodes (`OutsideObjs`).
* `FinTriv.keep`, **`CapFinTrivAt.keep`**: the `FinTriv` case carried across such a step: the endpoint state word
  (`epTSA`, outside the TCBs and nodes by `EpsWit` / `ep_out`) and the reply's `TCB` word (in `Sg`,
  `ObjsOK.tcbW`, so in `Ω`, outside the TCBs and nodes) are kept, and so is the finality (`is_final.keep`).
* The generic decode lemmas `cnode_del_gen`, `cnode.decode.del_gen`, **`syscall.decode_invocation.del_gen`**: the
  case is any target predicate `P` (`TgtP`, at the decode start) for which the deletion keeps `J` from every state
  the restart reaches.
* Instances (no named premise, case hypotheses only):
  * **`syscall.decode_invocation.del_fintriv`** (`TgtFinTriv`: the target `CapFinTrivAt` at the decode start);
  * **`syscall.decode_invocation.del_eprn`** (the target an endpoint / notification / reply cap, any finality,
    under `ScApart`), and **`syscall.decode_invocation.del_eprn_ent`** from [J] `SlotTyEntS` at an `EntAt` state
    (no apartness hypothesis left).

No new premise; no existing statement changed.
-/
import Fl4ProofsA64.P1.QueueSlotTyEp
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

/-! ## The finality is a function of the `OS` words -/

set_option maxHeartbeats 2000000 in
/-- **`is_final_capability_with_cap` at a slot of `OS` is the same at two states with the same `OS` words**
(`SlotTy` at the first: the links are null or slots of `OS`). -/
theorem is_final.keep {OS : Set U64} {s s' : S} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (k : OSKeep st OS s s')
    {x : U64} (hx : x ∈ OS) (c : capability.Cap) :
    cdt.is_final_capability_with_cap st s' x c = cdt.is_final_capability_with_cap st s x c := by
  have hxo := hT x hx
  obtain ⟨-, -, k16, k24⟩ := k x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpl : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  have capk : ∀ y, LinkOK OS y → y ≠ 0#u64 → obj.Slot.cap st y s' = obj.Slot.cap st y s := fun y hy h0 => by
    have hyO := hy.resolve_left h0
    rw [DPF.slot_cap_dec, DPF.slot_cap_dec, (k y hyO).1, (k y hyO).2.1]
  have hnx' : obj.sext48 (L.mem s' (wa x 24#u64)) = ok nx := by rw [k24]; exact hnx
  unfold cdt.is_final_capability_with_cap
  rw [slot_prev_eq, slot_prev_eq, k16, slot_next_of hnx', slot_next_of hnx]
  simp only [bind_ok, obj.Slot.is_null]
  by_cases hp0 : L.mem s (wa x 16#u64) = 0#u64
  · by_cases hn0 : nx = 0#u64
    · simp [hp0, hn0]
    · simp [hp0, hn0, capk nx hnl hn0]
  · by_cases hn0 : nx = 0#u64
    · simp [hp0, hn0, capk _ hpl hp0]
    · simp [hp0, hn0, capk _ hpl hp0, capk nx hnl hn0]

/-! ## The restart keeps the words outside the TCBs and nodes -/

/-- **The decode's restart**: `J`, every `OS` word kept, every word outside the TCBs and nodes kept. -/
theorem J.restartW {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra)
    (hT : SlotTy st T Ω Sg H Rp Nt OS s) :
    sched.set_thread_state st s (L.curW s) sched.TS_RESTART ⦃ s1 =>
      J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 ∧ OSKeep st OS s s1 ∧
        ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b ⦄ := by
  have q := D.bxi.1.choose_spec.choose_spec
  have hct : L.curW s ∈ T := q.curT
  refine WP.spec_mono (WP.spec_and (J.restart hO D hT) (sts_fine s _ sched.TS_RESTART (q.nodes _ q.cur)
    (q.tcbs _ hct))) fun s1 hh => ⟨hh.1.1, hh.1.2, fun b hb => hh.2.mem_eq hb.1 fun hF => ?_⟩
  rcases hF with e | e
  · exact out_ne_field hb hct (q.tcbs _ hct) (K := 3328#u64) (by simp) (by rw [e, stA_eq])
  · exact out_ne_node hb q.cur (q.nodes _ q.cur) (o := layout.node.SCHED_ACTION) (by rw [act_val]; omega)
      (by rw [e])

/-! ## The `FinTriv` case across such a step -/

theorem FinTriv.keep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS : Set U64} {s s1 : S}
    {c : capability.Cap} {fin : Bool} (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hty : CapTy T Ω Sg H Rp Nt OS c)
    (hout : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) (hk : FinTriv st s c fin) :
    FinTriv st s1 c fin := by
  rcases hk with h | h | ⟨p, b, x, y, z, w, rfl, he⟩ | ⟨p, b, rfl, hr⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨p, b, x, y, z, w, rfl, ?_⟩))
    have hH := hty.1.1.1 p b x y z w rfl
    obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := q.eps
    obtain ⟨hE', hEN, -⟩ := w1 p ((ty.2.2.1 p).2 (Or.inl hH))
    unfold LawfulStore.epState at he ⊢
    rw [hout _ (ep_out hE' hEN).2]
    exact he
  · refine Or.inr (Or.inr (Or.inr (Or.inl ⟨p, b, rfl, ?_⟩)))
    have hp := hty.1.1.2.2 p b rfl
    rw [hout _ (q.omega _ (hsub _ (hob.tcbW hp)))]
    exact hr
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- **`CapFinTrivAt` across a step that keeps the `OS` words and the words outside the TCBs and nodes.** -/
theorem CapFinTrivAt.keep {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {OS : Set U64}
    {s s1 : S} {x : U64} (q : SchedQueuesInvX st T Cs Ω H X s Q R) (hob : ObjsOK st Ω Sg Rp Scs Nt Z s)
    (hsub : ∀ b ∈ Sg, b ∈ Ω) (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hx : x ∈ OS) (k : OSKeep st OS s s1)
    (hout : ∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) (hk : CapFinTrivAt st x s) :
    CapFinTrivAt st x s1 := by
  intro c fin hc hf
  have hc0 : obj.Slot.cap st x s = ok c := by
    rw [DPF.slot_cap_dec, (k x hx).1, (k x hx).2.1, ← DPF.slot_cap_dec] at hc; exact hc
  have hf0 : cdt.is_final_capability_with_cap st s x c = ok fin := by
    rw [← is_final.keep hT k hx c]; exact hf
  have hty := (hT x hx).1 c (by rw [DPF.slot_cap_dec] at hc0; exact hc0)
  exact FinTriv.keep q hob hsub hty hout (hk c fin hc0 hf0)

/-- `EpNtRpAt` reads the slot's cap words only. -/
theorem EpNtRpAt.keep {OS : Set U64} {s s1 : S} {x : U64} (hx : x ∈ OS) (k : OSKeep st OS s s1)
    (hk : EpNtRpAt st x s) : EpNtRpAt st x s1 := by
  intro c hc
  rw [DPF.slot_cap_dec, (k x hx).1, (k x hx).2.1, ← DPF.slot_cap_dec] at hc
  exact hk c hc

/-! ## The generic CNode `Delete` decode -/

/-- **The restart, then the exposed `cdt.delete` of a slot of `OS`**, for a deletion that keeps `J` from every
state the restart reaches. -/
theorem cnode_del_gen {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S} {a : A}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} {x : U64}
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hG : ∀ s1, J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) →
      cdt.delete st ar s1 a x true ⦃ r => J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s r.2.1 ⦄) :
    (do
      let s1 ← sched.set_thread_state st s (L.curW s) sched.TS_RESTART
      cdt.delete st ar s1 a x true) ⦃ r s' _ =>
        DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ :=
  WP.spec_bind (J.restartW hO D hT) fun s1 h1 =>
    WP.spec_mono (hG s1 h1.1 h1.2.1 h1.2.2) fun r hr => by
      obtain ⟨r', s', a'⟩ := r; exact ⟨hr.1.post, hr.2⟩

/-- The case hypothesis: the slot the CNode lookup returns at the decode start satisfies `P`. -/
def TgtP (st : machine.Store S) [L : LawfulStore st] (P : U64 → Prop) (s : S) (c : capability.Cap) (buf : U64) :
    Prop :=
  ∀ i d x, msg.syscall_arg st s (L.curW s) buf 0#u64 = ok i → msg.syscall_arg st s (L.curW s) buf 1#u64 = ok d →
    cspace.lookup_target_slot st s c i d = ok (.Ok x) → P x

set_option hygiene false in
local macro "eleaf" : tactic => `(tactic| first
  | exact (WP.spec_ok _).2 ⟨D.err _, hT⟩
  | (simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_ok, bind_tc_ok, error.illegal, error.truncated, cnode.missing_source]
     exact (WP.spec_ok _).2 ⟨D.err _, hT⟩))

set_option maxHeartbeats 4000000 in
/-- **`cnode.decode` at `CNodeDelete`**, generic in the target's case `P`. -/
theorem cnode.decode.del_gen {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS) {s : S}
    {cap : capability.Cap} {extra : Aeneas.Std.Array obj.Slot 3#usize} (a : A) (len buf : U64)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (c : capability.Cap) (hc : RootOK OS c) {P : U64 → Prop} (hk : TgtP st P s c buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) →
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
  · exact cnode_del_gen hO D hT (hG v (hr.1 v rfl) (hk idx dep v hidx.1 hdep.1 hr.2.1))
  · rename_i h; first | exact absurd rfl h | exact absurd trivial h | simp at h

set_option maxHeartbeats 2000000 in
/-- **The CNode `Delete` invocation, decode level, generic in the target's case `P`.** -/
theorem syscall.decode_invocation.del_gen {A : Type _} {ar : machine.Arch A} {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    {P : U64 → Prop} (hk : TgtP st P s cap buf)
    (hG : ∀ x ∈ OS, P x → ∀ s1, J st T Cs Ω H Sg Rp Scs Nt Z Ac OS s s1 → OSKeep st OS s s1 →
      (∀ b, OutsideObjs st T Cs s b → L.mem s1 b = L.mem s b) →
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
  · exact cnode.decode.del_gen hO a len buf D hT _ hR hk hG

/-! ## Instances -/

/-- **The CNode `Delete` of a `FinTriv` target** (gen 30's `cdt.delete.fintriv` at the decode level): the
target's cap is `FinTriv` for the finality computed at the decode start. -/
theorem syscall.decode_invocation.del_fintriv {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    {OS : Set U64} (hO : OSOK T Ω Sg OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => CapFinTrivAt st x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  have hb := D.bxi
  have q := hb.1.choose_spec.choose_spec
  obtain ⟨-, -, hX, -, hSg⟩ := hb.blk
  refine syscall.decode_invocation.del_gen hO a len slot cap blk call don fp buf extra D hT hf hslot hcap hk ?_
  intro x hx hkx s1 h1 k1 o1
  exact cdt.delete.fintriv hP hO h1 hx (CapFinTrivAt.keep q hX.1 hSg.sub hT hx k1 o1 hkx)

/-- **The CNode `Delete` of an endpoint / notification / reply target** (any finality), under `ScApart`. -/
theorem syscall.decode_invocation.del_eprn {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    {OS : Set U64} (hO : OSOK T Ω Sg OS) (hA : ScApart Scs Z OS)
    {s : S} (a : A) (len : U64) (slot : obj.Slot) (cap : capability.Cap) (blk call don fp : Bool) (buf : U64)
    (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) (hT : SlotTy st T Ω Sg H Rp Nt OS s)
    (hf : capFam cap = .cnode) (hslot : slot ∈ OS) (hcap : obj.Slot.cap st slot s = ok cap)
    (hk : TgtP st (fun x => EpNtRpAt st x s) s cap buf) :
    syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra ⦃ r s' _ =>
      DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ :=
  syscall.decode_invocation.del_gen hO a len slot cap blk call don fp buf extra D hT hf hslot hcap hk
    fun x hx hkx s1 h1 k1 _ => cdt.delete.eprn hP hO hA h1 hx (hkx.keep hx k1)

/-- **On the entry fact** ([J] `SlotTyEntS`): at an `EntAt` decode start there is a placed, typed `OS` for which
the CNode `Delete` of an endpoint / notification / reply target keeps the invariants and `SlotTy`; no apartness
hypothesis is left. -/
theorem syscall.decode_invocation.del_eprn_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEntS st T Ω Sg H Rp Scs Nt Z P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64),
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => EpNtRpAt st x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  obtain ⟨OS, hO, hT, -, -, hA⟩ := hJ.entAt hE
  exact ⟨OS, hO, hT, fun a len slot blk call don fp buf hf hs hc hk =>
    syscall.decode_invocation.del_eprn hP hO hA a len slot cap blk call don fp buf extra D hT hf hs hc hk⟩

/-- **The `FinTriv` decode on the entry fact** ([J] `SlotTyEnt`, the weakest entry fact). -/
theorem syscall.decode_invocation.del_fintriv_ent {A : Type _} {ar : machine.Arch A} (hP : P0.ArchTotal ar)
    (hJ : SlotTyEnt st T Ω Sg H Rp Nt P3Ok) {s : S} (hE : EntAt st P3Ok s) {cap : capability.Cap}
    {extra : Aeneas.Std.Array obj.Slot 3#usize} (D : DecPre st T Cs Ω H Sg Rp Scs Nt Z U Ac s cap extra) :
    ∃ OS, OSOK T Ω Sg OS ∧ SlotTy st T Ω Sg H Rp Nt OS s ∧
      ∀ (a : A) (len : U64) (slot : obj.Slot) (blk call don fp : Bool) (buf : U64),
        capFam cap = .cnode → slot ∈ OS → obj.Slot.cap st slot s = ok cap →
        TgtP st (fun x => CapFinTrivAt st x s) s cap buf →
        syscall.decode_invocation st ar s a fl4_abi.label.CNodeDelete len slot cap blk call don fp buf extra
          ⦃ r s' _ => DecPost st T Cs Ω H Sg Rp Scs Nt Z Ac s r s' ∧ SlotTy st T Ω Sg H Rp Nt OS s' ⦄ := by
  obtain ⟨OS, hO, hT⟩ := hJ.entAt hE
  exact ⟨OS, hO, hT, fun a len slot blk call don fp buf hf hs hc hk =>
    syscall.decode_invocation.del_fintriv hP hO a len slot cap blk call don fp buf extra D hT hf hs hc hk⟩

end ST
end R
end W7

end

end Fl4ProofsA64.P1
