/-
# The ReplyRecv run's cap lookups at `X8` (FL4 #56, m68 (R-a') item (3))

The general path's `handle_recv` looks up `t`'s `CAP` and `REPLY` caps at
`X8`; the fast path looked them up at the dispatch state `X0`. They agree when
the run writes none of the words the two walks read:

* `t`'s registers and its `CTABLE` slot: TCB words below the state word, kept
  to `X8` (`rr_x8`'s `htw`: `handle_fault_reply` writes only the receiver
  `u`'s registers);
* the cap slots of the CNodes the walks reach (`p + (x &&& mask r) * 32`, two
  words each): P1 does not type CNode objects, so this enters as the narrow
  premise `CnOff` [J] at the dispatch state (l4v `valid_cap` / `cap_table_at`
  of CNode caps with `pspace_distinct`: a CNode cap names a CNode object of
  `2 ^ radix` slots, apart from every TCB, the cores' nodes and the frame
  words `Sg` of SCs, replies and notifications).

`rab_body_congr2` / `rab_body_cont2` / `rab_body_done2` refine m67's loop
lemmas to the slots the walk actually indexes (`x &&& mask r`);
`rab_loop_congr2` / `rab_loop_slot` are the fuel inductions; `lk8_of` derives
m66's `lk8`. The bundle left is `RRReads5` (m67's `nvm` only); top
`kernel_entry.entry_of9`.
-/
import Fl4Proofs.P1.FastRRFoot
import Fl4Proofs.P1.RabCongr
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} (st : machine.Store S)

/-- The loop body reads only the slots `x &&& mask r` of the CNode it walks. -/
theorem rab_body_congr2 {s s' : S} {cptr n fuel : U64} {cap : capability.Cap}
    (h : ∀ p r gs g, cap = .CNode p r gs g → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s' = obj.Slot.cap st (cnSlot p (x &&& m)) s) :
    cspace.resolve_address_bits_loop.body st s' cptr cap n fuel =
      cspace.resolve_address_bits_loop.body st s cptr cap n fuel := by
  cases cap with
  | CNode p r gs g =>
    obtain ⟨m, hm, -⟩ := spec_ex_fd (P0.cspace.mask.p0 r)
    have hp := h p r gs g rfl m hm
    unfold cspace.resolve_address_bits_loop.body
    simp only [obj.Slot.index, lift, bind_ok, cnSlot, hm] at hp ⊢
    simp only [hp]
  | _ => rfl

set_option maxHeartbeats 1600000 in
/-- A continuing step read a CNode cap from a slot `x &&& mask r` and spent
one unit of fuel. -/
theorem rab_body_cont2 {s : S} {cptr n fuel p r gs g : U64} {x : capability.Cap × U64 × U64}
    (h : cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel = ok (ControlFlow.cont x)) :
    ∃ m y : U64, cspace.mask r = ok m ∧ obj.Slot.cap st (cnSlot p (y &&& m)) s = ok x.1 ∧
      x.2.2.val < fuel.val := by
  obtain ⟨m, hm, -⟩ := spec_ex_fd (P0.cspace.mask.p0 r)
  unfold cspace.resolve_address_bits_loop.body at h
  simp only [obj.Slot.index, lift, bind_ok, bind_tc_ok, hm] at h
  revert h
  repeat' (first
    | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
    | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
    | (with_reducible refine eq_ite_imp (fun _ => ?_) (fun _ => ?_))
    | (intro h; simp at h; done))
  all_goals (intro h; split at h <;> (try (simp at h; done)))
  all_goals
    have e := ok_inj_ff h
    simp only [ControlFlow.cont.injEq] at e
    subst e
    exact ⟨m, _, hm, ‹obj.Slot.cap st _ s = ok _›, sub1_lt ‹¬ fuel = 0#u64› ‹fuel - 1#u64 = ok _›⟩

set_option maxHeartbeats 1600000 in
/-- A step that ends with a found slot found it at `x &&& mask r` of the
CNode it walks. -/
theorem rab_body_done2 {s : S} {cptr n fuel p r gs g : U64} {res : cspace.Resolved}
    (h : cspace.resolve_address_bits_loop.body st s cptr (.CNode p r gs g) n fuel =
      ok (ControlFlow.done (core.result.Result.Ok res))) :
    ∃ m y : U64, cspace.mask r = ok m ∧ res.slot = cnSlot p (y &&& m) := by
  obtain ⟨m, hm, -⟩ := spec_ex_fd (P0.cspace.mask.p0 r)
  unfold cspace.resolve_address_bits_loop.body at h
  simp only [obj.Slot.index, lift, bind_ok, bind_tc_ok, hm] at h
  revert h
  repeat' (first
    | (with_reducible_and_instances refine eq_bind_imp (fun _ _ => ?_))
    | (with_reducible_and_instances refine eq_bind_imp' (fun _ _ => ?_))
    | (with_reducible refine eq_ite_imp (fun _ => ?_) (fun _ => ?_))
    | (intro h; simp at h; done))
  all_goals (intro h; try (split at h <;> (try (simp at h; done))))
  all_goals
    have e := ok_inj_ff h
    simp only [ControlFlow.done.injEq, core.result.Result.Ok.injEq] at e
    subst e
    exact ⟨m, _, hm, rfl⟩

/-- **`resolve_address_bits_loop` read congruence on the indexed slots**:
m67's `rab_loop_congr` with the slots the walk indexes (`x &&& mask r`). -/
theorem rab_loop_congr2 {s s' : S} {cptr : U64} (C : U64 → U64 → Prop)
    (hag : ∀ p r, C p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) s' = obj.Slot.cap st (cnSlot p (x &&& m)) s)
    (hcl : ∀ p r m x p' r' gs' g', C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (x &&& m)) s = ok (.CNode p' r' gs' g') → C p' r') :
    ∀ (N : Nat) (cap : capability.Cap) (n fuel : U64) (res : core.result.Result cspace.Resolved error.LookupFault),
      fuel.val < N → (∀ p r gs g, cap = .CNode p r gs g → C p r) →
      cspace.resolve_address_bits_loop st cap s cptr n fuel = ok res →
      cspace.resolve_address_bits_loop st cap s' cptr n fuel = ok res := by
  intro N
  induction N with
  | zero => intro _ _ _ _ hf; omega
  | succ N ih =>
    intro cap n fuel res hf hc h
    rw [rabLoop_unfold] at h ⊢
    rw [rab_body_congr2 st (fun p r gs g e => hag p r (hc p r gs g e))]
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    rw [hy]; simp only [bind_ok]
    cases y with
    | done z => exact hk
    | cont x =>
      cases cap with
      | CNode p r gs g =>
        obtain ⟨m, y, hm, hoff, hlt⟩ := rab_body_cont2 st hy
        exact ih x.1 x.2.1 x.2.2 res (by omega)
          (fun p' r' gs' g' e => hcl p r m y p' r' gs' g' (hc _ _ _ _ rfl) hm (e ▸ hoff)) hk
      | _ => simp [cspace.resolve_address_bits_loop.body] at hy

/-- **The slot a walk finds is an indexed slot of a CNode of the closure.** -/
theorem rab_loop_slot {s : S} {cptr : U64} (C : U64 → U64 → Prop)
    (hcl : ∀ p r m x p' r' gs' g', C p r → cspace.mask r = ok m →
      obj.Slot.cap st (cnSlot p (x &&& m)) s = ok (.CNode p' r' gs' g') → C p' r') :
    ∀ (N : Nat) (cap : capability.Cap) (n fuel : U64) (res : cspace.Resolved),
      fuel.val < N → (∀ p r gs g, cap = .CNode p r gs g → C p r) →
      cspace.resolve_address_bits_loop st cap s cptr n fuel = ok (core.result.Result.Ok res) →
      ∃ p r m y, C p r ∧ cspace.mask r = ok m ∧ res.slot = cnSlot p (y &&& m) := by
  intro N
  induction N with
  | zero => intro _ _ _ _ hf; omega
  | succ N ih =>
    intro cap n fuel res hf hc h
    rw [rabLoop_unfold] at h
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    cases cap with
    | CNode p r gs g =>
      cases y with
      | done z =>
        have ez : z = core.result.Result.Ok res := ok_inj_ff hk
        subst ez
        obtain ⟨m, y, hm, hs⟩ := rab_body_done2 st hy
        exact ⟨p, r, m, y, hc _ _ _ _ rfl, hm, hs⟩
      | cont x =>
        obtain ⟨m, y, hm, hoff, hlt⟩ := rab_body_cont2 st hy
        exact ih x.1 x.2.1 x.2.2 res (by omega)
          (fun p' r' gs' g' e => hcl p r m y p' r' gs' g' (hc _ _ _ _ rfl) hm (e ▸ hoff)) hk
    | _ =>
      simp [cspace.resolve_address_bits_loop.body] at hy
      subst hy; simp at hk

end

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- A cap-slot word: outside every TCB and node, not a frame word. -/
def CapSW (T Cs Sg : Set U64) (s : S) (b : U64) : Prop := OutsideObjs st T Cs s b ∧ b ∉ Sg

/-- **`CnOff` [J]** (l4v `valid_cap` / `cap_table_at` for CNode caps,
`valid_objs`, `pspace_distinct`): at the dispatch state `s`, the CNode caps
reachable from `t`'s CSpace root (a predicate `C` on CNode pointer / radix,
true of the root's, closed under the CNode caps read from the slots
`x &&& mask r` of a `C` CNode) index only cap-slot words (`CapSW`, both words
of each slot). Why a premise: P1 types no CNode object (`InvHyps.lookupSlot`
covers only the slot a lookup finds), so nothing places a CNode's slots
apart from the TCBs, nodes and frame words. Reachability: a CNode cap names a
CNode object of `2 ^ radix` 32-byte slots (`cap_table_at radix p`; a radix
below 64, the slots `x &&& mask r < 2 ^ r` inside it); kernel objects are
pairwise distinct, and TCBs, the per-core nodes (kernel globals), SCs, replies
and notifications are other objects. -/
def CnOff (T Cs Sg : Set U64) (s : S) (t : U64) : Prop :=
  ∀ sl root, obj.Tcb.slot t layout.tcb.SLOT_CTABLE = ok sl → obj.Slot.cap st sl s = ok root →
    ∃ C : U64 → U64 → Prop, (∀ p r gs g, root = .CNode p r gs g → C p r) ∧
      (∀ p r m x p' r' gs' g', C p r → cspace.mask r = ok m →
        obj.Slot.cap st (cnSlot p (x &&& m)) s = ok (.CNode p' r' gs' g') → C p' r') ∧
      (∀ p r m x, C p r → cspace.mask r = ok m →
        CapSW (L := L) T Cs Sg s (cnSlot p (x &&& m)) ∧
        CapSW (L := L) T Cs Sg s (core.num.U64.wrapping_add (cnSlot p (x &&& m)) 8#u64))

variable {T Cs Ω Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- A cap-slot word is no footprint word. -/
theorem rrw_capw {X0 : S} {t rptr ep u usc b : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc) (hb : CapSW (L := L) T Cs Sg X0 b) :
    ¬ RRW (L := L) T Rp X0 t u rptr usc (Z usc) b := by
  obtain ⟨⟨hba, oT, oN⟩, hS⟩ := hb
  have nT : ∀ y ∈ T, ∀ K : U64, K.val < 4096 → b ≠ core.num.U64.wrapping_add y K := fun y hy K hK e => by
    have := oT y hy; rw [e, tcb_wadd_val (P.hT y hy) hK] at this; omega
  have nN : ∀ off : U64, off.val < 4288 → b ≠ L.nodeAt X0 (L.cpu X0) off := fun off ho e => by
    have := oN _ P.hcC; rw [e, nodeAt_val P.hN ho] at this; omega
  intro hw
  rcases hw with e | e | e | e | e | e | e | e | e
  · rw [stA_eq] at e; exact nT t P.ht _ (by decide) e
  · rw [stA_eq] at e; exact nT u P.hu _ (by decide) e
  · exact nT u P.hu _ (by decide) e
  · rcases e with ⟨y, hy, K, -, h2, -, e⟩ | e
    · exact nT y hy K (by omega) e
    · exact e
  · exact hS (P.rpS _ e)
  · exact hS (e ▸ P.rtS)
  · exact hS (P.scSg b hba e.inSC)
  · exact nN _ (by simp [layout.node.REPROGRAM]) e
  · exact nN _ (by simp [layout.node.SCHED_ACTION]) e

/-- **(3) m66's `lk8`** at `X8` from the fast path's lookups at `X0`, `t`'s
words below the state kept (`rr_x8`), the footprint `RRW` and `CnOff`. -/
theorem lk8_of {X0 X8 : S} {t rptr ep u usc : U64}
    (P : RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hrc : fastpath.reply_caps st X0 t = ok (some (rptr, ep)))
    (w08 : WritesIn st X0 X8 (RRW (L := L) T Rp X0 t u rptr usc (Z usc)))
    (htw : ∀ K : U64, K.val < 3328 → K.val % 8 = 0 →
      L.mem X8 (core.num.U64.wrapping_add t K) = L.mem X0 (core.num.U64.wrapping_add t K))
    (hCn : CnOff (L := L) T Cs Sg X0 t) :
    ∃ i i1 b0 b1 b3 b4 g, obj.Tcb.reg st t X8 layout.reg.CAP = ok i1 ∧
      cspace.lookup_cap st X8 t i1 = ok (core.result.Result.Ok (capability.Cap.Endpoint ep b0 b1 true b3 b4)) ∧
      obj.Tcb.reg st t X8 layout.reg.REPLY = ok i ∧
      cspace.lookup_cap st X8 t i = ok (core.result.Result.Ok (capability.Cap.Reply rptr g)) := by
  have ht' := P.hT t P.ht
  obtain ⟨⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, ⟨i1, found1, b0, b1, b3, b4, hi1, hr1, hc1⟩⟩⟩ :=
    reply_caps_some st hrc
  obtain ⟨C, hC0, hcl, hW⟩ := hCn sl root hsl hroot
  -- cap-slot words agree
  have capK : ∀ b, CapSW (L := L) T Cs Sg X0 b → L.mem X8 b = L.mem X0 b := fun b hb =>
    w08.mem_eq hb.1.1 (rrw_capw P hb)
  have slotK : ∀ p r, C p r → ∀ m, cspace.mask r = ok m → ∀ x : U64,
      obj.Slot.cap st (cnSlot p (x &&& m)) X8 = obj.Slot.cap st (cnSlot p (x &&& m)) X0 := by
    intro p r hp m hm x
    obtain ⟨h1, h2⟩ := hW p r m x hp hm
    unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, capK _ h1, capK _ h2]
  -- the root slot (`t`'s TCB words 0 and 8)
  have esl : sl = core.num.U64.wrapping_add t (core.num.U64.wrapping_mul layout.tcb.SLOT_CTABLE layout.cte.SIZE) := by
    simp only [obj.Tcb.slot, lift, bind_ok] at hsl; exact (ok_inj_ff hsl).symm
  have tf := ht'.fits
  have vsl : sl.val = t.val := by
    rw [esl]; simp [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq, U64.size_def, U64.numBits]
    all_goals omega
  have e0 : sl = core.num.U64.wrapping_add t 0#u64 := by
    apply UScalar.eq_of_val_eq; rw [vsl, tcb_wadd_val ht' (by decide)]; simp
  have e8 : core.num.U64.wrapping_add sl 8#u64 = core.num.U64.wrapping_add t 8#u64 := by
    apply UScalar.eq_of_val_eq; rw [tcb_wadd_val ht' (by decide)]
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, vsl]; omega
  have hroot8 : obj.Slot.cap st sl X8 = ok root := by
    rw [← hroot]; unfold obj.Slot.cap; rw [L.read_pair_eq, L.read_pair_eq, e8, e0,
      htw 0#u64 (by decide) (by decide), htw 8#u64 (by decide) (by decide)]
  -- registers
  have hreg : ∀ r : U64, r.val < 384 → obj.Tcb.reg st t X8 r = obj.Tcb.reg st t X0 r := by
    intro r hr
    obtain ⟨K, hK, eK⟩ := regA_eq ht' hr
    rw [reg_ok, reg_ok, eK, htw K (by omega) (by omega)]
  have hCAP : (layout.reg.CAP).val < 384 := by simp
  have hREP : (layout.reg.REPLY).val < 384 := by simp
  -- the walks and the found slots
  have look : ∀ (cptr : U64) (fd : cspace.Resolved) (c : capability.Cap),
      cspace.resolve_address_bits st X0 root cptr cspace.WORD_BITS = ok (core.result.Result.Ok fd) →
      obj.Slot.cap st fd.slot X0 = ok c → cspace.lookup_cap st X8 t cptr = ok (core.result.Result.Ok c) := by
    intro cptr fd c hr' hc'
    have hr8 : cspace.resolve_address_bits st X8 root cptr cspace.WORD_BITS = ok (core.result.Result.Ok fd) :=
      rab_loop_congr2 st C slotK hcl 66 root _ 65#u64 _ (by simp) hC0 hr'
    obtain ⟨p, r, m, y, hp, hm, hs⟩ := rab_loop_slot st C hcl 66 root _ 65#u64 fd (by simp) hC0 hr'
    have hc8 : obj.Slot.cap st fd.slot X8 = ok c := by rw [hs, slotK p r hp m hm y, ← hs]; exact hc'
    exact lookup_cap_of_found hsl hroot8 hr8 hc8
  exact ⟨i, i1, b0, b1, b3, b4, g, by rw [hreg _ hCAP]; exact hi1, look i1 found1 _ hr1 hc1,
    by rw [hreg _ hREP]; exact hi, look i found _ hr hc⟩

/-! ## The assembly without `lk8` -/

/-- **The ReplyRecv read left after m68 (3)**: m67's end-state read `nvm`. -/
structure RRReads5 (u : U64) (X15 : S) (a2 : A) : Prop where
  nvm : ∀ s' a', fastpath.switch_to st ar X15 a2 u = ok (s', a') →
    L.mem s' (stA (L.curW s')) ≠ sched.TS_RUNNING_VM

/-- `RRPre3` with `RRReads5` (`nvm` only) in place of `RRReads4`. -/
def RRPre5G (ty : U64) (X0 : S) (a : A) : Prop :=
  ∀ (t rptr ep u usc : U64) (X1 X2 : S) (a1 : A) (b9 : Bool) (X3 : S),
    sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
    RRChecksG st ar ty X0 a t rptr ep u usc →
    obj.Tcb.set_state st t X0 sched.TS_RESTART = ok X1 →
    ipc.reply_remove st ar X1 a rptr u = ok (X2, a1) →
    sporadic.sc_sporadic st X2 usc = ok b9 →
    (if b9 then do
      let i13 ← obj.Sc.cpu st usc X2
      let i14 ← obj.node_get st X2 i13 layout.node.CUR_SC
      if usc != i14 then sporadic.unblock_check st X2 usc else ok X2
    else ok X2) = ok X3 →
    ∀ (X4 : S) (a2 : A) (X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 : S),
      faults.handle_fault_reply st ar X3 a1 u t = ok (true, X4, a2) →
      faults.clear_fault st X4 u = ok X5 →
      obj.Tcb.set_state st u X5 sched.TS_RESTART = ok X6 →
      sched.set_action st X6 u = ok X7 →
      obj.Tcb.set_state st t X7 sched.TS_RUNNING = ok X8 →
      obj.Tcb.set_block_obj st t X8 ep = ok X9 →
      obj.Tcb.set_state st t X9 sched.TS_BLOCKED_ON_RECV = ok X10 →
      obj.Tcb.set_reply_obj st t X10 rptr = ok X11 →
      obj.Reply.set_tcb st rptr X11 t = ok X12 →
      obj.Tcb.set_ep_next st t X12 0#u64 = ok X13 →
      obj.Tcb.set_ep_prev st t X13 0#u64 = ok X14 →
      obj.Ep.set_queue st ep X14 t t obj.EP_RECV = ok X15 →
      RRReads5 (L := L) ar u X15 a2

/-- `RRPre5G` at an UnknownSyscall fault (pf1). -/
abbrev RRPre5 (X0 : S) (a : A) : Prop :=
  RRPre5G (L := L) ar fl4_abi.consts.fault.UnknownSyscall X0 a


theorem RRPre3.of5G {ty : U64} [HfrRestart st ar ty] {X0 : S} {a : A}
    (hP : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecksG st ar ty X0 a t rptr ep u usc → RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : RRSum (L := L) Scs X0) (hCn : ∀ t, sched.cur_thread st X0 = ok t → CnOff (L := L) T Cs Sg X0 t)
    (h : RRPre5G (L := L) ar ty X0 a) : RRPre3G (L := L) ar ty X0 a := by
  intro t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3 X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15
    e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15
  have P := hP t rptr ep u usc hct hrc hC
  obtain ⟨-, -, -, w08, htw, -⟩ := rr_x8G ar P hC (hS usc P.hcS) e1 e2 e3s e3 e4 e5 e6 e7 e8
  exact ⟨lk8_of P hrc w08 htw (hCn t hct),
    (h t rptr ep u usc X1 X2 a1 b9 X3 hct hrc hC e1 e2 e3s e3 X4 a2 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15
      e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15).nvm⟩

/-- `RRPre3.of5G` at an UnknownSyscall fault (pf1). -/
theorem RRPre3.of5 {X0 : S} {a : A}
    (hP : ∀ t rptr ep u usc, sched.cur_thread st X0 = ok t → fastpath.reply_caps st X0 t = ok (some (rptr, ep)) →
      RRChecks st ar X0 a t rptr ep u usc → RRPl (L := L) T Cs Ω Sg Rp Scs Nt Z X0 t rptr ep u usc)
    (hS : RRSum (L := L) Scs X0) (hCn : ∀ t, sched.cur_thread st X0 = ok t → CnOff (L := L) T Cs Sg X0 t)
    (h : RRPre5 (L := L) ar X0 a) : RRPre3 (L := L) ar X0 a := by
  apply RRPre3.of5G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


/-- `RRPre5` at every dispatch state of the entry. -/
def RRPreAt5G (ty : U64) (s : S) (a : A) : Prop :=
  ∀ t nx s1 s2 a2, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) → RRPre5G (L := L) ar ty s2 a2

/-- `RRPreAt5G` at an UnknownSyscall fault (pf1). -/
abbrev RRPreAt5 (s : S) (a : A) : Prop :=
  RRPreAt5G (L := L) ar fl4_abi.consts.fault.UnknownSyscall s a


/-- **`CnOffAt` [J]**: `CnOff` of the current thread at every dispatch state of
the entry (see `CnOff`). -/
def CnOffAt (T Cs Sg : Set U64) (s : S) (a : A) : Prop :=
  ∀ t nx s1 s2 a2, sched.cur_thread st s = ok t → obj.Tcb.reg st t s layout.reg.NEXT_IP = ok nx →
    obj.Tcb.set_reg st t s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
    syscall.budget_ok st ar s1 a = ok (true, s2, a2) →
    ∀ t', sched.cur_thread st s2 = ok t' → CnOff (L := L) T Cs Sg s2 t'

theorem RRPreAt2.of5G {ty : U64} [HfrRestart st ar ty] {U Ac : Set U64} {H : Heap} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSum : RRSumAt (L := L) ar Scs s a) (hCn : CnOffAt (L := L) ar T Cs Sg s a)
    (hR : RRPreAt5G (L := L) ar ty s a) : RRPreAt2G (L := L) ar ty s a := by
  intro t nx s1 s2 a2 et enx es1 hb
  have h0 := h.1.choose_spec.choose_spec
  have et' : t = L.curW s := by
    rw [eq_of_spec_fd (sched.cur_thread.spec (L := L) s)] at et; exact (ok_inj_ff et).symm
  have htT : t ∈ T := by rw [et']; exact h0.curT
  have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := by
    have := reg_entry (r := layout.reg.FAULT_IP) (v := core.num.U64.wrapping_sub nx 2#u64) h htT
      (by simp [layout.reg.FAULT_IP])
    rw [es1, WP.spec_ok] at this; exact this
  have hW := obj.Tcb.set_reg.wrK (L := L) s t layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64)
    (h0.tcbs t htT) (by simp [layout.reg.FAULT_IP])
  rw [es1, WP.spec_ok] at hW
  obtain ⟨K, hK, e1⟩ := hW
  have hal : Aligned (core.num.U64.wrapping_add (L.curW s) K) := by
    rw [← et']; exact field_aligned (h0.tcbs t htT)
      (by rw [hK]; simp [layout.reg.FAULT_IP]) (by rw [hK]; simp [layout.reg.FAULT_IP])
  have e1' : s1 = L.wr s (core.num.U64.wrapping_add (L.curW s) K) (core.num.U64.wrapping_sub nx 2#u64) := by
    rw [e1, et']
  have he1 : EntAt st P3Ok s1 := ⟨s, hP, Ent.prefix hK hal e1' (WritesIn.refl _ _)⟩
  have hx := syscall.budget_ok.bxc hA E0 s1 a h1 he1.xg
  rw [hb, WP.spec_ok] at hx
  have hPl := fun t' rptr ep u usc (et2 : sched.cur_thread st s2 = ok t') hrc
    (hC : RRChecksG st ar ty s2 a2 t' rptr ep u usc) => rrPl_ofG ar E0 hNt hx.1 (hx.2.2 rfl) et2 hrc hC
  exact RRPre2.of3G ar hPl (hSum t nx s1 s2 a2 et enx es1 hb)
    (RRPre3.of5G ar hPl (hSum t nx s1 s2 a2 et enx es1 hb) (hCn t nx s1 s2 a2 et enx es1 hb)
      (hR t nx s1 s2 a2 et enx es1 hb))

/-- `RRPreAt2.of5G` at an UnknownSyscall fault (pf1). -/
theorem RRPreAt2.of5 {U Ac : Set U64} {H : Heap} {P3Ok : S → Prop}
    (hA : P0.ArchTotal ar) (E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s : S} {a : A} (hP : P3Ok s) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hSum : RRSumAt (L := L) ar Scs s a) (hCn : CnOffAt (L := L) ar T Cs Sg s a)
    (hR : RRPreAt5 (L := L) ar s a) : RRPreAt2 (L := L) ar s a := by
  apply RRPreAt2.of5G (ty := fl4_abi.consts.fault.UnknownSyscall) <;> assumption


end

section top
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {P3Ok : S → Prop}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {U : Set U64}

/-- **Native kernel entries keep `EntryInv`, ReplyRecv half from one read**
(m68): `entry_of8` with `hRP : RRPreAt3` (`lk8`, `nvm`) replaced by
`hRP : RRPreAt5` (m67's `nvm` only) and the CNode placement `hCn : CnOffAt`
[J] at the dispatch states (`lk8_of`).
**Vacuous** (p1g): its premise bundles are contradictory with the `EntryInv` premise
(P1/EntryVacuous). Use P3's `kernel_entry_entryInvU29` (P3/XTopJointEntryInv29),
which has this conclusion from U29's premises. -/
theorem kernel_entry.entry_of9 {A : Type _} {ar : machine.Arch A} {Adm : PSets → Prop} (hA : P0.ArchTotal ar)
    (GF : ∀ σ : PSets, Adm σ → Hyps4 st ar Adm Cs U P3Ok σ)
    (hσ : Adm ⟨T, Ω, H, Sg, Rp, Scs, Nt, Z⟩) {Ac : Set U64} (s : S) (a : A) (hP : P3Ok s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hX : StoreExt st)
    (hAs : AsidOff (L := L) Ω Sg s)
    (hNv : ∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → FaultNvmPre (L := L) ar s a number)
    (hSum : RRSumAt (L := L) ar Scs s a)
    (hCn : CnOffAt (L := L) ar T Cs Sg s a)
    (hRP : RRPreAt5 (L := L) ar s a) :
    (∀ number : I64, number ≠ fl4_abi.syscall.SysVMEnter → syscall.handle_syscall st ar s a number ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) ∧
    (∀ irq : U64, syscall.handle_interrupt_entry st ar s a irq ⦃ s' _ =>
      ∃ σ', Adm σ' ∧ ∃ Ac', EntryInvs st Cs σ' Ac' s' ⦄) := by
  have E0 : EntryHyps0 st ar T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
    have G3 : InvGaps st ar Adm T Cs Ω H Sg Rp Scs Nt Z U P3Ok := by
      obtain ⟨P, C, ⟨V, Pd⟩, Pt, G, -⟩ := GF _ hσ
      exact (G.gaps3 hA hσ C Pd Pt P.xfer).gaps hA P C
    exact (EntryHyps.of_gaps hA hσ (fun σ'' h'' => (GF σ'' h'').1) (GF _ hσ).1 G3).toEntryHyps0
  have hNt : ∀ n ∈ Nt, H n = some .ntfn := (GF _ hσ).2.2.2.2.2
  exact kernel_entry.entry_of7r2 hA GF hσ s a hP h hX hAs hNv (RRPreAt2.of5 ar hA E0 hNt hP h hSum hCn hRP)

end top

end Fl4Proofs.P1
