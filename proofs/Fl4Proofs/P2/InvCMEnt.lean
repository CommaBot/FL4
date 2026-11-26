/-
# P2 (line slhuf, gen 12): what `plan_with` decides at CNodeCopy / CNodeMint

`localinv::plan_with` (crates/fl4-core/src/localinv.rs l.194–206) admits a Copy / Mint only when
* the invoked cap is a CNode cap and the first extra cap's slot is not null;
* the target (`lookup_target_slot` from args 0/1, the registers `R10` / `R8`) and the source
  (`lookup_source_slot` from the first extra cap's cap, args 2/3, the registers `R9` / `R15`) are found;
* **the source cap is a non-EPT Frame cap** (`matches!(src_cap, Cap::Frame { is_ept: false, .. })`) and the target's
  first cap word decodes to `Null`;
* the locks on the target, the source and the source's CDT successor are taken (`p.add`, at most 4).

So an Untyped source is rejected by the plan: `set_untyped_cap_as_full` never writes the source's cap words on this
path (it does so only for an Untyped source), and no arm cut is assumed (gen 11's finding 1 is closed).

* `read_cap_val` (`Plan.read_cap` reads the slot's cap, at any fill below the bound), `sarg2_reg`, `sarg3_reg`;
* `CMW dest src`: the four words the plan records (target `CAP0`, source `CAP0` / `CAP1` / `NEXT`);
* **`plan_with_cmF`**: the facts above, with the locks (`PHeld`) and the seen words (`SeenAddr (CMW dest src)`).

No premises.
-/
import Fl4Proofs.P2.InvSeen
import Fl4Proofs.P2.InvCMG
import Fl4Proofs.P2.InvCM
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

section plan
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

theorem sarg2_reg (s : S) (t buf : U64) :
    msg.syscall_arg st s t buf 2#u64 = obj.Tcb.reg st t s layout.reg.R9 := by
  unfold msg.syscall_arg
  rw [if_pos (by simp [msg.N_MSG_REGISTERS])]
  simp [msg.msg_register]

theorem sarg3_reg (s : S) (t buf : U64) :
    msg.syscall_arg st s t buf 3#u64 = obj.Tcb.reg st t s layout.reg.R15 := by
  unfold msg.syscall_arg
  rw [if_pos (by simp [msg.N_MSG_REGISTERS])]
  simp [msg.msg_register]

/-- `Plan.read_cap` reads the slot's cap (a plan with room for two more seen words). -/
theorem read_cap_val {q : localinv.Plan} {s : S} {sl : obj.Slot} {x : capability.Cap × localinv.Plan}
    (h : localinv.Plan.read_cap st q s sl = ok x) (hn : q.nseen.val + 2 ≤ 4) :
    obj.Slot.cap st sl s = ok x.1 := by
  unfold localinv.Plan.read_cap at h
  obtain ⟨i, ei, h⟩ := bind_eq_ok h
  obtain ⟨⟨w0, q1⟩, e1, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
  obtain ⟨⟨w1, q2⟩, e2, h⟩ := bind_eq_ok h
  try simp only [uncurry_apply_pair] at h
  try dsimp only at h
  obtain ⟨c, ec, h⟩ := bind_eq_ok h
  have e := ok_inj_ff h
  subst e
  simp only [lift, ok.injEq] at ei ei1
  obtain ⟨v1, n1, -, -, -, -, -⟩ := plan_read_eq e1 (by omega)
  obtain ⟨v2, -, -, -, -, -, -⟩ := plan_read_eq e2 (by simp only at n1; omega)
  simp only at v1 v2 n1
  have h0 : i = sl := by
    rw [← ei]; apply UScalar.eq_of_val_eq
    rw [core.num.U64.wrapping_add_val_eq]; simp only [layout.cte.CAP0.val_eq, Nat.add_zero]
    exact Nat.mod_eq_of_lt (by scalar_tac)
  have h1 : i1 = core.num.U64.wrapping_add sl 8#u64 := by
    rw [← ei1]; apply UScalar.eq_of_val_eq
    rw [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_add_val_eq, layout.cte.CAP1.val_eq]; rfl
  subst h0 h1
  unfold obj.Slot.cap
  rw [L.read_pair_eq, ← v1, ← v2]
  simp only [bind_ok]
  exact ec

/-- The four words a Copy / Mint plan records: the target's `CAP0`, the source's `CAP0`, `CAP1`, `NEXT`. -/
def CMW (dest src x : U64) : Prop :=
  x = core.num.U64.wrapping_add dest layout.cte.CAP0 ∨ x = core.num.U64.wrapping_add src layout.cte.CAP0 ∨
    x = core.num.U64.wrapping_add src layout.cte.CAP1 ∨ x = core.num.U64.wrapping_add src layout.cte.NEXT

/-- The conclusion of `plan_with_cmF`. -/
def CMPlan (st : machine.Store S) [L : LawfulStore st] (s : S) (t : obj.Tcb) (slot : obj.Slot)
    (extra : Array obj.Slot 3#usize) (p : localinv.Plan) : Prop :=
  ∃ (cp cr cg cgb dest s1 src fp rt asid va : U64) (sz : capability.FrameSize) (d mp : Bool)
    (rc : capability.Cap) (c1 : capability.Cap),
    obj.Slot.cap st slot s = ok (.CNode cp cr cg cgb) ∧
    Aeneas.Std.Array.index_usize extra 0#usize = ok s1 ∧ s1 ≠ 0#u64 ∧
    cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA t layout.reg.R10))
      (L.mem s (regA t layout.reg.R8)) = ok (.Ok dest) ∧
    obj.Slot.cap st s1 s = ok rc ∧
    cspace.lookup_source_slot st s rc (L.mem s (regA t layout.reg.R9)) (L.mem s (regA t layout.reg.R15)) =
      ok (.Ok src) ∧
    obj.Slot.cap st src s = ok (.Frame fp sz rt d mp false asid va) ∧
    capability.Cap.decode (L.mem s (core.num.U64.wrapping_add dest layout.cte.CAP0)) 0#u64 = ok c1 ∧
    capability.Cap.is_null c1 = ok true ∧
    (dest ≠ 0#u64 → PHeld p dest) ∧ (src ≠ 0#u64 → PHeld p src) ∧
    (∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → PHeld p nx) ∧
    SeenAddr (CMW dest src) p

set_option hygiene false in
/-- The Copy / Mint arm of `plan_with` (the two labels' arms are the same text). -/
local macro "cm_arm" : tactic => `(tactic| (
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · simp at h
    have hcn : ∃ cp cr cg cgb, cap = .CNode cp cr cg cgb := by
      cases cap <;> simp at eb ⊢
    obtain ⟨cp, cr, cg, cgb, rfl⟩ := hcn
    simp only [↓reduceIte] at h
    obtain ⟨s1, es1, h⟩ := bind_eq_ok h
    obtain ⟨b1, eb1, h⟩ := bind_eq_ok h
    unfold obj.Slot.is_null at eb1
    have hb1 := ok_inj_ff eb1
    have hs10 : s1 ≠ 0#u64 := by
      intro e0
      rw [e0] at hb1
      simp at hb1
      subst hb1
      simp at h
    have hb1f : b1 = false := by rw [← hb1]; simp [hs10]
    subst hb1f
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨i, ei, h⟩ := bind_eq_ok h
    obtain ⟨i1, ei1, h⟩ := bind_eq_ok h
    obtain ⟨r, er, h⟩ := bind_eq_ok h
    obtain ⟨o, eo, h⟩ := bind_eq_ok h
    obtain ⟨cf, ecf, h⟩ := bind_eq_ok h
    unfold localinv.reg_arg at ei ei1
    rw [sarg0_reg, reg_ok] at ei
    rw [sarg1_reg, reg_ok] at ei1
    have hi := ok_inj_ff ei
    have hi1 := ok_inj_ff ei1
    subst hi hi1
    cases r with
    | Err e =>
      simp only [core.result.Result.ok] at eo
      cases ok_inj_ff eo
      simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
      cases ok_inj_ff ecf
      simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at h
    | Ok dest =>
      simp only [core.result.Result.ok] at eo
      cases ok_inj_ff eo
      simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf
      cases ok_inj_ff ecf
      try simp only at h
      obtain ⟨rc, erc, h⟩ := bind_eq_ok h
      obtain ⟨i2, ei2, h⟩ := bind_eq_ok h
      obtain ⟨i3, ei3, h⟩ := bind_eq_ok h
      obtain ⟨r1, er1, h⟩ := bind_eq_ok h
      obtain ⟨o1, eo1, h⟩ := bind_eq_ok h
      obtain ⟨cf1, ecf1, h⟩ := bind_eq_ok h
      unfold localinv.reg_arg at ei2 ei3
      rw [sarg2_reg, reg_ok] at ei2
      rw [sarg3_reg, reg_ok] at ei3
      have hi2 := ok_inj_ff ei2
      have hi3 := ok_inj_ff ei3
      subst hi2 hi3
      cases r1 with
      | Err e =>
        simp only [core.result.Result.ok] at eo1
        cases ok_inj_ff eo1
        simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf1
        cases ok_inj_ff ecf1
        simp [core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual] at h
      | Ok src =>
        simp only [core.result.Result.ok] at eo1
        cases ok_inj_ff eo1
        simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch] at ecf1
        cases ok_inj_ff ecf1
        try simp only at h
        obtain ⟨i4, ei4, h⟩ := bind_eq_ok h
        simp only [lift, ok.injEq] at ei4
        subst ei4
        obtain ⟨⟨w0, q1⟩, e1, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        try dsimp only at h
        obtain ⟨⟨scap, q2⟩, e2, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        try dsimp only at h
        obtain ⟨i5, ei5, h⟩ := bind_eq_ok h
        simp only [lift, ok.injEq] at ei5
        subst ei5
        obtain ⟨⟨i6, q3⟩, e3, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        try dsimp only at h
        obtain ⟨nxt, enx, h⟩ := bind_eq_ok h
        obtain ⟨x4, e4, h⟩ := bind_eq_ok h
        rcases x4 with ⟨q4, b2⟩
        try simp only [uncurry_apply_pair] at h
        try dsimp only at h
        cases b2
        · simp at h
        try simp only [↓reduceIte] at h
        have hfr : ∃ fp sz rt d mp asid va, scap = .Frame fp sz rt d mp false asid va ∧ q4 = q3 := by
          cases scap with
          | Frame fp sz rt d mp ep asid va =>
            cases ep <;> simp at e4
            exact ⟨fp, sz, rt, d, mp, asid, va, rfl, e4.symm⟩
          | _ => simp at e4
        obtain ⟨fp, sz, rt, d, mp, asid, va, hsc0, hq4⟩ := hfr
        rw [hsc0] at e2
        obtain ⟨dc, ec1, h⟩ := bind_eq_ok h
        obtain ⟨b3, eb3, h⟩ := bind_eq_ok h
        cases b3
        · simp at h
        simp only [↓reduceIte] at h
        obtain ⟨⟨b4, q5⟩, e5, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        try dsimp only at h
        obtain ⟨⟨p6, ok1⟩, e6, h⟩ := bind_eq_ok h
        try simp only [uncurry_apply_pair] at h
        try dsimp only at h
        obtain ⟨hok, rfl⟩ := some_if_eq h
        subst hok
        cases b4
        · simp at e6
        simp only [↓reduceIte] at e6
        obtain ⟨⟨b5, q7⟩, e7, e6⟩ := bind_eq_ok e6
        try simp only [uncurry_apply_pair] at e6
        try dsimp only at e6
        cases b5
        · simp at e6
        simp only [↓reduceIte] at e6
        obtain ⟨⟨ok2, q8⟩, e8, e6⟩ := bind_eq_ok e6
        try simp only [uncurry_apply_pair] at e6
        try dsimp only at e6
        have e6' := ok_inj_ff e6
        simp only [Prod.mk.injEq] at e6'
        obtain ⟨rfl, rfl⟩ := e6'
        -- the reads
        obtain ⟨r1v, r1n, r1s, -, -, -, -⟩ := plan_read_eq e1 (by simp)
        have n1 : q1.nseen.val = 1 := by
          first | exact r1n | (simp at r1n; omega) | (simp only at r1n; omega)
        have hsc := read_cap_val e2 (by omega)
        obtain ⟨c2n, c2s, -, -, -, -⟩ := plan_read_cap_eq e2 (by omega)
        have n2 : q2.nseen.val = q1.nseen.val + 2 := c2n
        obtain ⟨r3v, -, r3s, -, -, -, -⟩ := plan_read_eq e3 (by omega)
        have r1v' : w0 = L.mem s (core.num.U64.wrapping_add dest layout.cte.CAP0) := r1v
        have r3v' : i6 = L.mem s (core.num.U64.wrapping_add src layout.cte.NEXT) := r3v
        have hsc' : obj.Slot.cap st src s = ok (.Frame fp sz rt d mp false asid va) := hsc
        subst r1v' r3v'
        obtain ⟨a5h, a5d, a5s, a5nn, -, -, -⟩ := plan_add_eq e5 rfl
        obtain ⟨a7h, a7d, a7s, a7nn, -, -, -⟩ := plan_add_eq e7 rfl
        obtain ⟨a8h, a8d, a8s, a8nn, -, -, -⟩ := plan_add_eq e8 rfl
        have a5s' : q5.seen = q4.seen := a5s
        have a7s' : q7.seen = q5.seen := a7s
        have a8s' : q8.seen = q7.seen := a8s
        have a5n' : q5.nseen = q4.nseen := a5nn
        have a7n' : q7.nseen = q5.nseen := a7nn
        have a8n' : q8.nseen = q7.nseen := a8nn
        have a5h' : ∀ y, PHeld q4 y → PHeld q5 y := a5h
        have a7h' : ∀ y, PHeld q5 y → PHeld q7 y := a7h
        have a8h' : ∀ y, PHeld q7 y → PHeld q8 y := a8h
        have a5d' : dest ≠ 0#u64 → PHeld q5 dest := a5d
        have a7d' : src ≠ 0#u64 → PHeld q7 src := a7d
        have a8d' : nxt ≠ 0#u64 → PHeld q8 nxt := a8d
        have hS : SeenAddr (CMW dest src) q8 := by
          have s1' : SeenAddr (CMW dest src) q1 := r1s _ (fun j _ hj => by simp at hj) (Or.inl rfl)
          have s2' : SeenAddr (CMW dest src) q2 := c2s _ s1' (Or.inr (Or.inl rfl)) (Or.inr (Or.inr (Or.inl rfl)))
          have s3' : SeenAddr (CMW dest src) q3 := r3s _ s2' (Or.inr (Or.inr (Or.inr rfl)))
          intro j hj hjn
          have e' : q8.seen = q3.seen := by rw [a8s', a7s', a5s', hq4]
          have e'' : q8.nseen = q3.nseen := by rw [a8n', a7n', a5n', hq4]
          have hj' : j < q3.seen.val.length := by rw [← e']; exact hj
          have := s3' j hj' (by rw [← e'']; exact hjn)
          simp only [e']
          exact this
        have hnx : ∀ nx', obj.Slot.next st src s = ok nx' → nxt = nx' := by
          intro nx' e
          unfold obj.Slot.next obj.Slot.next_word at e
          simp only [lift, bind_ok, L.read_eq] at e
          unfold obj.Slot.next_of_word at enx
          rw [enx] at e
          try simp only [bind_ok, bind_tc_ok] at e
          exact ok_inj_ff e
        exact ⟨cp, cr, cg, cgb, dest, s1, src, fp, rt, asid, va, sz, d, mp, rc, dc, ecap, es1, hs10, er, erc, er1,
          hsc', ec1, eb3, fun hd => a8h' _ (a7h' _ (a5d' hd)), fun hd => a8h' _ (a7d' hd),
          fun nx' e hne => by rw [← hnx nx' e] at hne ⊢; exact a8d' hne, hS⟩))

set_option maxHeartbeats 16000000 in
/-- (slhuf gen 12) **What `plan_with` decides at `CNodeCopy` / `CNodeMint`**, with its locks and seen words
(module docstring): in particular the source cap is a non-EPT Frame cap (never an Untyped). -/
theorem plan_with_cmF {s : S} {t : obj.Tcb} {lbl : U64} {slot : obj.Slot} {extra : Array obj.Slot 3#usize}
    {p : localinv.Plan} (hl : lbl = fl4_abi.label.CNodeCopy ∨ lbl = fl4_abi.label.CNodeMint)
    (h : localinv.plan_with st s t lbl slot extra = ok (some p)) : CMPlan st s t slot extra p := by
  unfold localinv.plan_with at h
  obtain ⟨q, eq, h⟩ := bind_eq_ok h
  obtain ⟨cap, ecap, h⟩ := bind_eq_ok h
  unfold localinv.Plan.new at eq
  have hq := ok_inj_ff eq
  subst hq
  rcases hl with rfl | rfl
  · rw [if_pos rfl] at h
    cm_arm
  · rw [if_neg lbl_mint_ne_copy, if_pos rfl] at h
    cm_arm

end plan

/-! ## The entry facts of the arm (the Copy / Mint analogue of `DelEnt`) -/

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- `plan_fields` with the `plan_with` call it ends in (stpost's P3 `plan_fieldsW`, copied: P3 is not imported). -/
theorem plan_fieldsWCM {s : S} {n : I64} {p : localinv.Plan} (h : localinv.plan st s n = ok (some p)) :
    ∃ t info cptr r buf e, sched.cur_thread st s = ok t ∧ msg.msg_info st s t = ok info ∧
      obj.Tcb.reg st t s layout.reg.CAP = ok cptr ∧
      cspace.lookup_slot st s t cptr = ok (core.result.Result.Ok r) ∧
      msg.lookup_ipc_buffer st s false t = ok buf ∧
      ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok e) ∧
      localinv.plan_with st s t info.label r.slot e = ok (some p) := by
  unfold localinv.plan at h
  split at h
  · simp at h
  obtain ⟨t, et, h⟩ := bind_eq_ok h
  obtain ⟨info, ei, h⟩ := bind_eq_ok h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  split at h
  swap
  · simp at h
  obtain ⟨cptr, ec, h⟩ := bind_eq_ok h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  cases r with
  | Err _ => simp at h
  | Ok r1 =>
    try simp only at h
    obtain ⟨buf, eb, h⟩ := bind_eq_ok h
    obtain ⟨r2, er2, h⟩ := bind_eq_ok h
    cases r2 with
    | Err _ => simp at h
    | Ok e =>
      try simp only at h
      exact ⟨t, info, cptr, r1, buf, e, et, ei, ec, er, eb, er2, h⟩

/-- (slhuf gen 12) **The plan's data flow at the entry**: its extra caps are `lookup_extra_caps`'s, and
`plan_with` on its own slot and extra caps returns it. -/
theorem plan_fieldsCM {s : S} {n : I64} {p : localinv.Plan} (h : localinv.plan st s n = ok (some p)) :
    ∃ t info buf, sched.cur_thread st s = ok t ∧ msg.msg_info st s t = ok info ∧
      msg.lookup_ipc_buffer st s false t = ok buf ∧
      ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok p.extra) ∧
      localinv.plan_with st s t info.label p.slot p.extra = ok (some p) := by
  obtain ⟨t, info, cptr, r, buf, e, et, ei, ec, er, eb, ee, hsl, hex⟩ := plan_fields h
  obtain ⟨t', info', cptr', r', buf', e', et', ei', ec', er', eb', ee', hpw⟩ := plan_fieldsWCM h
  have h1 : t' = t := ok_inj_ff (et'.symm.trans et)
  rw [h1] at ei' ec' er' eb' ee' hpw
  have h2 : info' = info := ok_inj_ff (ei'.symm.trans ei)
  rw [h2] at ee' hpw
  have h3 : cptr' = cptr := ok_inj_ff (ec'.symm.trans ec)
  rw [h3] at er'
  have h4 : r' = r := by have := ok_inj_ff (er'.symm.trans er); cases this; rfl
  rw [h4] at hpw
  have h5 : buf' = buf := ok_inj_ff (eb'.symm.trans eb)
  rw [h5] at ee'
  have h6 : e' = e := by have := ok_inj_ff (ee'.symm.trans ee); cases this; rfl
  rw [h6] at hpw
  rw [hsl, hex]
  exact ⟨t, info, buf, et, ei, eb, ee, hpw⟩

variable (st) in
/-- (slhuf gen 12) **The plan's extra caps at the entry** (`localinv.plan`'s data flow, kept: `InvPlanD` forgets
where its extra caps come from): `lookup_extra_caps` returns them and `plan_with` on them returns the plan. -/
def InvEx (p : localinv.Plan) (s : S) : Prop :=
  ∃ info buf, msg.msg_info st s (L.curW s) = ok info ∧ msg.lookup_ipc_buffer st s false (L.curW s) = ok buf ∧
    ipc.lookup_extra_caps st s (L.curW s) buf info = ok (core.result.Result.Ok p.extra) ∧
    localinv.plan_with st s (L.curW s) info.label p.slot p.extra = ok (some p)

/-- (slhuf gen 12) **`InvEx` from the plan at the entry** (`loc_chain_all` clause 8's input `hp`). -/
theorem invEx_of_plan {s : S} {n : I64} {p : localinv.Plan} (h : localinv.plan st s n = ok (some p)) :
    InvEx st p s := by
  obtain ⟨t, info, buf, et, ei, eb, ee, hpw⟩ := plan_fieldsCM h
  have ht : t = L.curW s := ok_inj_ff (et.symm.trans (cur_thread_ok s))
  subst ht
  exact ⟨info, buf, ei, eb, ee, hpw⟩

variable (st) in
/-- (slhuf gen 12) **The canonical `Q` of the Copy / Mint path**: `InvQCM` with the plan's lookup (`InvLk`) and its
extra caps (`InvEx`); all three from `localinv.plan` at the entry (`invQCM_intro`, `invLk_of_plan`,
`invEx_of_plan`). -/
def InvQCMF (Cs Ω Sg Ac : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (K : KLayout)
    (m : U64 → U64) (s : S) : Prop :=
  InvQCM st Cs Ω Sg Ac Locks p K m s ∧ InvLk st p s ∧ InvEx st p s

variable (st) in
/-- (slhuf gen 12) **The Copy / Mint arm's facts at the entry** (the `DelEnt` analogue): the invoked slot holds a
CNode cap; the target `dest` (from `R10` / `R8` over it) is a capability slot outside the objects, its first word
decoding to `Null`, its lock held; the first extra cap `s1 ≠ 0` is a capability slot holding a CNode cap; the source
`src` (from `R9` / `R15` over it) is a capability slot outside the objects holding a non-EPT Frame cap, its lock
held; `src`'s CDT successor, when not null, is a capability slot whose lock is held; both CNodes lie in a closed
walk set `C` whose radix-masked slots are capability slots outside the objects. -/
def CMEnt (K : KLayout) (Cs : Set U64) (Locks : S → U64 → Prop) (p : localinv.Plan) (s : S) : Prop :=
  ∃ (cp cr cg cgb dest s1 rp rr rg rgb src fp rt asid va : U64) (sz : capability.FrameSize) (d mp : Bool)
    (c1 : capability.Cap) (C : U64 → U64 → Prop),
    obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧
    Aeneas.Std.Array.index_usize p.extra 0#usize = ok s1 ∧ s1 ≠ 0#u64 ∧
    cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
      (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
    obj.Slot.cap st s1 s = ok (.CNode rp rr rg rgb) ∧
    cspace.lookup_source_slot st s (.CNode rp rr rg rgb) (L.mem s (regA (L.curW s) layout.reg.R9))
      (L.mem s (regA (L.curW s) layout.reg.R15)) = ok (.Ok src) ∧
    obj.Slot.cap st src s = ok (.Frame fp sz rt d mp false asid va) ∧
    capability.Cap.decode (L.mem s (core.num.U64.wrapping_add dest layout.cte.CAP0)) 0#u64 = ok c1 ∧
    capability.Cap.is_null c1 = ok true ∧
    C cp cr ∧ C rp rr ∧ WalkCl (st := st) s C ∧
    (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
      OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
    s1 ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s s1 ∧
    dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧ Locks s dest ∧
    src ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s src ∧ Locks s src ∧
    (∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → nx ∈ K.slots ∧ Locks s nx)

end ent

end Fl4Proofs.P2.PathObl
