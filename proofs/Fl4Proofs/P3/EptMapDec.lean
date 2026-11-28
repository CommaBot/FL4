/-
P3 (line mmuAD, gen 42b9): **the EPT table map's decode, past the guest-address bound, at `EptCore`** — FL4's
`ept::decode` map label (crates/fl4-core/src/ept.rs l. 294-310: `ept::root` of `ex[0]`'s cap, `ept::slot` (the walk
`ept::lookup`), the `DeleteFirst` test on the entry, then the caller's restart, the entry write `paddr(ptr) | 7` and
`set_cap` of the mapped cap) against the extended spec's `decodeEptInvocation` (Fl4Spec/Ext/VirtEptInv l. 160-173:
`eptCapRoot`, `guestSlot`, `getEpt`, the `deleteFirst` test, `.tableMap`). The arms before the bound are
P3/JAtZV3EptE (`zv_eptF_*`) and P3/JAtZV3EptG (`zv_eptF_gpa`); this file takes their negations as hypotheses.

* `run_seq_ok` / `run_seq_err`: one spec bind with a single outcome.
* **`EptCore.mapDec`**: from `EptCore` and the base's ASID-table relation `VsRel`, an unmapped `Ept ptr level`
  cap (`level` 39, 30 or 21), the map label, `length ≥ 2`, a non-null `ex[0]`, FL4's first argument word `i` with its
  masked guest address `g` below `2^47`, and a spec argument list whose first word is `i`: FL4's `ept.decode`
  returns `res` and the spec decoder (first extra cap `ex[0]`'s abstract cap) has a single outcome, related by
  **`MapDecOut`**: either both fail with related errors (`ErrRel`: the root's `FailedLookup` / `InvalidCapability 1`,
  the walk's `FailedLookup false (MissingCapability sh)`, `DeleteFirst`) with FL4's state unchanged; or both succeed:
  the spec decodes `.tableMap ptr level sl t idx asid1 g` for a table `t ∈ X` at level `lkLvl level`, reachable
  from the guest-tagged root of `ex[0]`'s cap, whose entry `idx = guestIndex g level` is not present on either
  side, and FL4's state after is `set_cap dest (wr s2 (eptA t idx) (paddr ptr | 7)) (Ept ptr level true asid1 g)`
  with `s2` the caller's restart.

The perform half (`VmEptState` after: base, `VcpuCore`, `EptCore` with `EptSlotOK`) is not in this file.
Gen 42b13 (the Architect's `hz0` decision (i)): `EptCore.mapDec` takes `hxe : IsSlot th (exAt ex 0)` and
`MapDecOut`'s success arm also gives `asid1 ≠ 0` (the root cap is a mapped `Ept` slot cap, `JExtEpt.anz`).
Gen 42b11: `MapDecOut`'s success arm also gives `asid1 < 2^20` (the root cap's ASID field; for `set_cap`'s
`EncWf` at the perform).
Gen 42b10: `MapDecOut`'s success arm also gives the pool entry at `asid1`'s indices (`PoolAt`) and the walk path
`GPath` to `t` at `asid1`'s ASID bits and the masked address `g` (what P3/EptTableMap's `EptCore.tableMap` takes).

No named premise (the level range `hlv` is a hypothesis of the step, to be discharged by the level field the
Architect approved, gen 42b9 ruling (b)). New file only; root import after `P3.EptRoot`.
-/
import Fl4Proofs.P3.EptRoot
import Fl4Proofs.P3.JAtZV3EptG
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section Spec
open Fl4Spec

theorem run_seq_ok {ε α β : Type} {m : NonDetE (State Unit) ε α} {k : α → NonDetE (State Unit) ε β}
    {s : State Unit} {a : α} {r : Set (Except ε β × State Unit) × Prop}
    (h : m.run s = ({(.ok a, s)}, False)) (h2 : (k a).run s = r) : (m >>= k).run s = r := by
  rw [run_bind_ok h, h2]

theorem run_seq_err {ε α β : Type} {m : NonDetE (State Unit) ε α} {k : α → NonDetE (State Unit) ε β}
    {s : State Unit} {e : ε} {r : Set (Except ε β × State Unit) × Prop}
    (h : m.run s = ({(.error e, s)}, False)) (h2 : r = ({(.error e, s)}, False)) : (m >>= k).run s = r := by
  rw [run_bind_error h, h2]

end Spec

theorem gpa_lt_of {g : U64} (hg : ¬ g.bv ≥ Fl4Spec.guestGpaLimit) : g.val < 2 ^ 47 := by
  have hL : (Fl4Spec.guestGpaLimit).toNat = 140737488355328 := by unfold Fl4Spec.guestGpaLimit; decide
  have h' : ¬ (Fl4Spec.guestGpaLimit).toNat ≤ g.bv.toNat := hg
  rw [hL] at h'
  show g.bv.toNat < _
  omega

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}

/-- **The outcome of the table map's decode past the bound** (module docstring). -/
def MapDecOut (X : Set U64) (XL : U64 → Nat) (σ : Fl4Spec.State Unit) (s : S) (a : A) (ct dest ptr level g : U64)
    (sl : Fl4Spec.CslotPtr) (res : core.result.Result Unit error.Exc × S × A)
    (o : Set (Except Fl4Spec.SyscallError Fl4Spec.EptInvocation × Fl4Spec.State Unit) × Prop) : Prop :=
  (∃ e e', res = (.Err e, s, a) ∧ ErrRel e e' ∧ o = ({(.error e', σ)}, False)) ∨
  (∃ t asid1 ent, t ∈ X ∧ XL t = lkLvl level.val ∧ asid1.val < 2 ^ 20 ∧ asid1 ≠ 0#u64 ∧ GuestEntry σ ent ∧ ent &&& 1 = 1 ∧
    Relation.ReflTransGen (GStep σ) (Fl4Spec.asidEntryRoot ent) t.bv ∧
    PoolAt σ (Fl4Spec.asidHighBitsOf asid1.bv) (Fl4Spec.asidLowBitsOf asid1.bv) ent ∧
    GPath σ (Fl4Spec.asidHighBitsOf asid1.bv) (Fl4Spec.asidLowBitsOf asid1.bv) g.bv (lkLvl level.val) t.bv ∧
    L.mem s (eptA t (Fl4Spec.guestIndex g.bv level.val)) &&& 1#u64 = 0#u64 ∧
    (∃ es, σ.kheap t.bv = some (.archObj (.ept (XL t) es)) ∧ es (Fl4Spec.guestIndex g.bv level.val) &&& 1 = 0) ∧
    o = ({(.ok (.tableMap ptr.bv level.val sl t.bv (Fl4Spec.guestIndex g.bv level.val) asid1.bv g.bv), σ)}, False) ∧
    ∃ s2, sched.set_thread_state st s ct sched.TS_RESTART = ok s2 ∧
      res = (.Ok (), wrCap (L := L) (L.wr s2 (eptA t (Fl4Spec.guestIndex g.bv level.val))
        (core.num.U64.wrapping_sub ptr layout.PPTR_BASE ||| 7#u64)) dest (.Ept ptr level true asid1 g), a))

variable {X : Set U64} {XL : U64 → Nat} {th : TypedHeap} {s : S} {σ : Fl4Spec.State Unit}
open Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched
  Fl4Proofs.P1

set_option maxHeartbeats 4000000 in
/-- **The table map's decode past the guest-address bound** (module docstring). -/
theorem EptCore.mapDec (C : EptCore (L := L) X XL th s σ) {P : Set U64} (hR : VsRel P (L.mem s) (L.ksb s) σ)
    (a : A) {lbl len ptr level asid va : U64} (dest buf : U64) (ex : Array obj.Slot 3#usize) (h0 : level ≠ 0#u64)
    (hlv : level.val = 39 ∨ level.val = 30 ∨ level.val = 21)
    (hu : lbl.val ≠ (Fl4Spec.eptTableLabels level.val).2) (hm : lbl.val = (Fl4Spec.eptTableLabels level.val).1)
    (hl : ¬ len.val < 2) (hz : exAt ex 0 ≠ 0#u64) (hxe : IsSlot th (exAt ex 0)) {ct : U64}
    (hct : sched.cur_thread st s = ok ct) {i : U64} (hsa : msg.syscall_arg st s ct buf 0#u64 = ok i)
    (hg : ¬ (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ≥ Fl4Spec.guestGpaLimit)
    (args : List Fl4Spec.Data) (ha0 : args.getD 0 0 = i.bv) (hn : ¬ args.length < 2)
    (sl sl0 : Fl4Spec.CslotPtr) (rest : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)) :
    ∃ g : U64, g.bv = (i.bv &&& ~~~((1#64 <<< level.val) - 1)) ∧ g.val < 2 ^ 47 ∧
    ∃ res, ept.decode st arI s a lbl len (.Ept ptr level false asid va) dest buf ex = ok res ∧
      MapDecOut (L := L) X XL σ s a ct dest ptr level g sl res
        (ExceptT.run (Fl4Spec.decodeEptInvocation (Z := Unit) lbl.bv args sl (.eptCap ptr.bv level.val none)
          ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ) := by
  have hl64 : level.val < 64 := by omega
  have hl0 : level.val ≠ 0 := by omega
  have hu' : lbl ≠ (eptLbl level).2 := zv_lblNe (zv_eptLbl_val level).2 hu
  have hm' : lbl = (eptLbl level).1 := zv_lblEq (zv_eptLbl_val level).1 hm
  obtain ⟨z, hz2, hzv⟩ := shl_radix hl64
  have hz1 : 1 ≤ z.val := by rw [hzv]; exact (zv_pow64 hl64).1
  obtain ⟨i3, hi3, hi3v, -⟩ := spec_exists (U64.sub_spec (x := z) (y := 1#u64) (by scalar_tac))
  obtain ⟨i5, hi5, hi5v⟩ := spec_exists Fl4Proofs.P0.Consts.ept.LIMIT.spec
  have hm3 := zv_gpaMask hl64 hzv (by rw [hi3v]; rfl)
  have hgb : U64.bv (i &&& ~~~i3) = (i.bv &&& ~~~((1#64 <<< level.val) - 1)) := by
    show UScalar.bv (i &&& ~~~i3) = _
    rw [UScalar.bv_and, UScalar.bv_not]
    exact congrArg (fun x => i.bv &&& ~~~x) hm3
  have hgv : (i &&& ~~~i3).val < 2 ^ 47 := gpa_lt_of (g := i &&& ~~~i3) (by rw [hgb]; exact hg)
  refine ⟨i &&& ~~~i3, hgb, hgv, ?_⟩
  generalize hG : (i &&& ~~~i3 : U64) = g at hgb hgv
  have hge : ¬ g >= i5 := by
    subst hi5v
    show ¬ (140737488355328#u64).val ≤ g.val
    have : (140737488355328#u64 : U64).val = 2 ^ 47 := rfl
    omega
  -- FL4: to the root
  unfold ept.decode
  dsimp only
  rw [if_pos (show (level != 0#u64) = true by simpa using h0), zv_eptLblIf, bind_ok]
  generalize eptLbl level = q at hu' hm' ⊢
  obtain ⟨mL, uL⟩ := q
  dsimp only at hu' hm'
  simp only [uncurry_apply_pair]
  have g2 : ¬ len < 2#u64 := by scalar_tac
  rw [hct, bind_ok, if_neg hu', if_pos hm', if_neg g2, zv_ex0Idx, bind_ok, zv_ex0Null, bind_ok,
    if_neg (show ¬ (decide (exAt ex 0 = 0#u64) = true) by simpa using hz),
    if_neg (show ¬ (false = true) by decide), hsa, bind_ok]
  simp only [lift, bind_ok, hz2, hi3, hi5, hG]
  rw [if_neg hge, slot_cap_eq, capAt_capV, bind_ok]
  obtain ⟨r, hr, o, ho, hro⟩ := P1.spec_ex_fd (ept_root_rel (st := st) s σ hR (capV (L.mem s) (exAt ex 0)))
  rw [hr, bind_ok]
  -- the spec, to the root
  have hD : ExceptT.run (Fl4Spec.decodeEptInvocation (Z := Unit) lbl.bv args sl (.eptCap ptr.bv level.val none)
      ((absCap (capV (L.mem s) (exAt ex 0)), sl0) :: rest)) σ =
      ExceptT.run (do
        let (r, asid) ← Fl4Spec.eptCapRoot (absCap (capV (L.mem s) (exAt ex 0)))
        let tbl ← Fl4Spec.guestSlot r g.bv level.val
        let (_, es) ← Fl4Spec.NonDetE.liftE (Fl4Spec.getEpt tbl)
        Fl4Spec.NonDetE.whenE (es (Fl4Spec.guestIndex g.bv level.val) &&& 1 ≠ 0) <|
          Fl4Spec.NonDetE.throwError .deleteFirst
        Fl4Spec.NonDetE.returnOk (Fl4Spec.EptInvocation.tableMap ptr.bv level.val sl tbl
          (Fl4Spec.guestIndex g.bv level.val) asid g.bv) : Fl4Spec.SEMonad Unit Fl4Spec.EptInvocation) σ := by
    have h1 : Fl4Spec.dataToNat lbl.bv ≠ (Fl4Spec.eptTableLabels level.val).2 := by rw [zv_dataToNat]; exact hu
    have h2 : Fl4Spec.dataToNat lbl.bv = (Fl4Spec.eptTableLabels level.val).1 := by rw [zv_dataToNat]; exact hm
    unfold Fl4Spec.decodeEptInvocation
    dsimp only
    rw [if_neg hl0]
    generalize Fl4Spec.eptTableLabels level.val = q at h1 h2 ⊢
    obtain ⟨mL', uL'⟩ := q
    dsimp only at h1 h2 ⊢
    rw [if_neg h1, if_pos h2, if_neg hn, if_neg (by simp), ha0]
    refine run_seq_ok (by
      unfold Fl4Spec.NonDetE.whenE
      rw [if_neg (show ¬ (i.bv &&& ~~~(((1 : Fl4Spec.Word) <<< level.val) - 1) ≥ Fl4Spec.guestGpaLimit) from hg)]
      rfl) ?_
    have hgb2 : UScalar.bv g = i.bv &&& ~~~(((1 : Fl4Spec.Word) <<< level.val) - 1) := hgb
    rw [hgb2]
  rw [hD]
  rcases hro with ⟨e, e', rfl, rfl, hee⟩ | ⟨rt, asid1, va1, ent, hc0, rfl, rfl, hge1, h1, hrt⟩
  · -- the root fails on both sides
    simp only [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok]
    refine ⟨_, rfl, Or.inl ⟨e, e', rfl, hee, ?_⟩⟩
    exact run_seq_err ho rfl
  -- the root found: the walk
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  show ∃ res, (do
      let r2 ← ept.slot st s rt g level
      _) = ok res ∧ _
  have hlv4 : level.val = 39 ∨ level.val = 30 ∨ level.val = 21 ∨ level.val = 12 := by omega
  obtain ⟨root, hrX, hrb, hr0, hlk⟩ := C.lookup hge1.guest h1 hgv hlv4
  have hrr : root = rt := P1.eq_of_bv (hrb.trans hrt.symm)
  subst hrr
  unfold ept.slot
  rcases hlk with ⟨t, ht, hXt, hreach, hpath, hlr, hlo⟩ | ⟨sh, hlr, hlo⟩
  · rw [hlr, bind_ok]
    simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
    rw [L.read_eq, bind_ok]
    -- the entry, on both sides
    obtain ⟨es, hk, hwd⟩ := C.rel.obj t ht
    have hrange : XL t ≠ 0 ∨ (Fl4Spec.guestIndex g.bv level.val).toNat < 256 := by
      by_cases h0' : XL t = 0
      · right
        have h39 : level.val = 39 := by
          rw [hXt] at h0'
          rcases hlv with h | h | h <;> rw [h] at h0' <;> first | exact h | (simp [lkLvl] at h0')
        rw [guestIndex_toNat, h39, Nat.shiftRight_eq_div_pow]
        exact eptRootIdx_lt hgv
      · exact Or.inl h0'
    have b1 := ew_and (hwd _ hrange) mask1_ok
    have hslot : (Fl4Spec.guestSlot (Z := Unit) root.bv g.bv level.val).run σ = ({(.ok t.bv, σ)}, False) := by
      unfold Fl4Spec.guestSlot
      rw [hrb]
      exact runE_handleE_ok hlo
    have hgE : (Fl4Spec.NonDetE.liftE (ε := Fl4Spec.SyscallError) (Fl4Spec.getEpt (Z := Unit) t.bv)).run σ =
        ({(.ok (XL t, es), σ)}, False) := run_liftE (getEpt_eq hk)
    by_cases hp : L.mem s (eptA t (Fl4Spec.guestIndex g.bv level.val)) &&& 1#u64 = 0#u64
    · have hpb : (L.mem s (eptA t (Fl4Spec.guestIndex g.bv level.val)) &&& 1#u64 != 0#u64) = false := by
        simpa using hp
      have hes : es (Fl4Spec.guestIndex g.bv level.val) &&& 1 = 0 := by
        have := (u_and_zero _ _).1 hp
        exact b1.symm.trans this
      rw [hpb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      obtain ⟨s2, hs2, -⟩ := P1.spec_ex_fd (set_thread_state_cases (L := L) s ct sched.TS_RESTART)
      rw [hs2, bind_ok]
      simp only [layout.paddr, lift, bind_ok]
      rw [L.write_eq, bind_ok, set_cap_eq, bind_ok]
      have ha20 : asid1.val < 2 ^ 20 := by
        have h := capAt_capV (L.mem s) (exAt ex 0)
        rw [capAt_words] at h
        have h2 := decode_encWf h
        rw [hc0] at h2
        exact h2.2.2.1
      refine ⟨_, rfl, Or.inr ⟨t, asid1, ent, ht, hXt, ha20, C.exte.anz _ hxe _ _ _ _ hc0, hge1.guest, h1, hreach, hge1, hpath _ _ hge1, hp, ⟨es, hk, hes⟩, ?_, s2, hs2, rfl⟩⟩
      refine run_seq_ok ho ?_
      dsimp only
      refine run_seq_ok hslot ?_
      refine run_seq_ok hgE ?_
      dsimp only
      refine run_seq_ok (by
        unfold Fl4Spec.NonDetE.whenE
        rw [if_neg (not_not.mpr hes)]
        rfl) ?_
      rfl
    · have hpb : (L.mem s (eptA t (Fl4Spec.guestIndex g.bv level.val)) &&& 1#u64 != 0#u64) = true := by
        simpa using hp
      have hne : es (Fl4Spec.guestIndex g.bv level.val) &&& 1 ≠ 0 := by
        intro h
        exact hp ((u_and_zero _ _).2 (b1.trans h))
      rw [hpb]
      simp only [↓reduceIte]
      refine ⟨_, rfl, Or.inl ⟨.Sys .DeleteFirst, .deleteFirst, rfl, Or.inl trivial, ?_⟩⟩
      refine run_seq_ok ho ?_
      dsimp only
      refine run_seq_ok hslot ?_
      refine run_seq_ok hgE ?_
      dsimp only
      exact run_seq_err (by
        unfold Fl4Spec.NonDetE.whenE
        rw [if_pos hne]
        rfl) rfl
  · rw [hlr, bind_ok]
    simp only [core.result.Result.map_err, ept.slot.closure.Insts.CoreOpsFunctionFnOnceTupleLookupFaultExc.call_once,
      core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, core.convert.FromSame, lift, bind_tc_ok, bind_ok]
    refine ⟨_, rfl, Or.inl ⟨_, .failedLookup false (.missingCapability sh.val), rfl, Or.inl ⟨rfl, rfl⟩, ?_⟩⟩
    refine run_seq_ok ho ?_
    dsimp only
    refine run_seq_err ?_ rfl
    unfold Fl4Spec.guestSlot
    rw [hrb, runE_handleE_err hlo]
    rfl

end

end

end Fl4Proofs.P3
