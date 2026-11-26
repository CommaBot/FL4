/-
# P2 (line pte, gen 8): the reachability convention for `K.ptes` (`ptesR`)

**The convention.** `K.ptes := ptesR K m` with `m` the epoch-start memory: the leaf entries the x86 walk reaches in
`m`, from a native root named by the ASID table and a pool (`Named`), through the upper three levels (`walk1`,
`walk2`, `walk3`, pure versions of `vspace.lookup_pdpt/pd/pt_slot` on a memory), for a user address; minus every word
such a walk reads before the leaf (`WalkW`: the ASID-table words, the named pools' words, the upper-level entries),
and filtered by the layout facts the serial step asks (`region .none`, aligned, no user word, in no VCPU, outside
the kernel-state block). A function of the layout and the memory only, like nscope's `ptesE`. Unlike `PteConv`, no
bundle state is involved in the choice.

**What it gives** (at a bundle state `σ` of `K.toKLayout`, ghost `Zx`, whose memory agrees with `m` on the gate
words — `region .none`, off `ptesR K m`, not user, aligned (`GateAg`); a start state of the epoch is one: `StartAt`'s
memory link and `exec_epoch`):
* `gateAg_tab` / `gateAg_pool` / **`named_L4`**: the walk's ASID-table and pool words agree, a named root is a PML4 of
  `Zx.L4`; **`walk_agree`**: the three walks answer alike in `m` and at `σ` (by levels: each upper entry read is an
  entry of a table of `Zx.L4` / `L3` / `L2`, region `.none`, a `WalkW` word, so a gate word);
* **`ptesR_sub`**: every word of `ptesR K m` is a leaf entry of `Zx` (`PtW Zx.L1`), so `QPs` at `σ`
  (**`qPs_R`**, nscope's `qPs_of_bundle`);
* **`ptesR_of_run`**: the entry a writing PageMap run writes — `find_vspace_for_asid` at `σ` found the root (the
  decode's `check_vspace`) and `lookup_pt_slot` at `σ` found the entry — is in `ptesR K m` (`PtePlanLocked`'s [J]
  half, weakened to the runs that write).
* By the filters, the serial step's PTE facts hold for any `m`: **`regionOKP_R`**, **`userOKP_R`**.

Why not the union over agreeing bundle states (gen-8 option (a)): the coordinator's counterexample (a page table
retyped into a TCB) changes the layout's heap (`K.heap q` is `.tcb`, `SpecCover.arch` makes every arch object
`.other n`), so no bundle state of the same layout keeps `q` a page table; the residual risk is a retype into
another `.other` object (an ASID pool not yet in the table). Reachability needs no such argument.

The bridges `lookup_pdpt_slot_res` / `lookup_pd_slot_res` / `lookup_pt_slot_res` (the extracted lookups on a store
are the pure walks on its memory) and `find_vspace_for_asid_named` are new. P3 facts used: `VsRel.tmem`, `PoolsIn`,
`lookup_p*_slot_rel` (landing levels), `TopPlaced.pv` / `.disj` / `.pt`, nscope's `region_none_ptw` / `_pool` /
`_tab`, `qPs_of_bundle`. No named premise; no existing statement changed; nscope's `PteConv` / `E2EPJEp*` untouched.
-/
import Fl4Proofs.P2.PteLockRS
open Aeneas Aeneas.Std Result

/-! ## 1. The walks on a memory, and the bridges -/

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P3 Fl4Proofs.P3.Vs

section walk
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

instance instDecEPw (w : U64) : Decidable (eP w) := inferInstanceAs (Decidable ((w &&& 1#u64) ≠ 0#u64))
instance instDecESw (w : U64) : Decidable (eS w) := inferInstanceAs (Decidable ((w &&& 128#u64) ≠ 0#u64))

/-- The PDPT entry the walk from PML4 `r` reaches in `m` (`lookup_pdpt_slot`). -/
def walk1 (m : U64 → U64) (r v : U64) : Option U64 :=
  if eP (m (peA r (vIdx v 39))) then some (peA (eT (m (peA r (vIdx v 39)))) (vIdx v 30)) else none

/-- One more level: a present, non-large entry at `x` names the next table. -/
def walkStep (m : U64 → U64) (v : U64) (sh : Nat) : Option U64 → Option U64
  | none => none
  | some x => if eP (m x) ∧ ¬ eS (m x) then some (peA (eT (m x)) (vIdx v sh)) else none

/-- The PD entry (`lookup_pd_slot`). -/
def walk2 (m : U64 → U64) (r v : U64) : Option U64 := walkStep m v 21 (walk1 m r v)

/-- The PT entry (`lookup_pt_slot`). -/
def walk3 (m : U64 → U64) (r v : U64) : Option U64 := walkStep m v 12 (walk2 m r v)

/-- `lookup_pdpt_slot`'s result on memory `m`. -/
def res1 (m : U64 → U64) (r v : U64) : core.result.Result U64 error.LookupFault :=
  match walk1 m r v with
  | some x => .Ok x
  | none => .Err (.MissingCapability vspace.PML4_INDEX_OFFSET)

/-- One more level's result. -/
def resStep (m : U64 → U64) (v : U64) (sh : Nat) (off : U64) :
    core.result.Result U64 error.LookupFault → core.result.Result U64 error.LookupFault
  | .Err e => .Err e
  | .Ok x => if eP (m x) ∧ ¬ eS (m x) then .Ok (peA (eT (m x)) (vIdx v sh)) else .Err (.MissingCapability off)

def res2 (m : U64 → U64) (r v : U64) : core.result.Result U64 error.LookupFault :=
  resStep m v 21 vspace.PDPT_INDEX_OFFSET (res1 m r v)

def res3 (m : U64 → U64) (r v : U64) : core.result.Result U64 error.LookupFault :=
  resStep m v 12 vspace.PD_INDEX_OFFSET (res2 m r v)

theorem res1_ok {m : U64 → U64} {r v x : U64} : res1 m r v = .Ok x ↔ walk1 m r v = some x := by
  unfold res1
  cases walk1 m r v <;> simp

theorem resStep_ok {m : U64 → U64} {v : U64} {sh : Nat} {off x : U64}
    {a : core.result.Result U64 error.LookupFault} {w : Option U64} (h : ∀ y, a = .Ok y ↔ w = some y) :
    resStep m v sh off a = .Ok x ↔ walkStep m v sh w = some x := by
  cases a with
  | Err e =>
    have hw : w = none := by
      cases w with
      | none => rfl
      | some y => exact absurd ((h y).2 rfl) (by simp)
    subst hw
    simp [resStep, walkStep]
  | Ok y =>
    have hw : w = some y := (h y).1 rfl
    subst hw
    unfold resStep walkStep
    by_cases hc : eP (m y) ∧ ¬ eS (m y)
    · simp [hc]
    · simp [hc]

theorem res2_ok {m : U64 → U64} {r v x : U64} : res2 m r v = .Ok x ↔ walk2 m r v = some x :=
  resStep_ok (fun _ => res1_ok)

theorem res3_ok {m : U64 → U64} {r v x : U64} : res3 m r v = .Ok x ↔ walk3 m r v = some x :=
  resStep_ok (fun _ => res2_ok)

/-- **`lookup_pdpt_slot` is `walk1` on the store's memory.** -/
theorem lookup_pdpt_slot_res (s : S) (r v : U64) :
    vspace.lookup_pdpt_slot st s r v = ok (res1 (L.mem s) r v) := by
  unfold vspace.lookup_pdpt_slot res1 walk1
  rw [show vspace.idx v 39#u64 = ok (vIdx v 39) from idx_eq _ _ (by decide)]
  simp only [bind_ok]
  rw [entry_eq s r _ (vIdx_lt _ _), P_PRESENT_eq]
  simp only [bind_ok, lift]
  by_cases hp : eP (L.mem s (peA r (vIdx v 39)))
  · have h0 : ¬ (L.mem s (peA r (vIdx v 39)) &&& 1#u64) = 0#u64 := hp
    rw [if_neg h0, if_pos hp, table_of_eq]
    simp only [bind_ok]
    rw [show vspace.idx v 30#u64 = ok (vIdx v 30) from idx_eq _ _ (by decide)]
    simp only [bind_ok]
    rw [entry_addr_eq _ _ (vIdx_lt _ _)]
    simp only [bind_ok, bind_tc_ok]
  · have h0 := (eP_iff _).2 hp
    rw [if_pos h0, if_neg hp]

/-- One level of the bridge. -/
theorem lookup_step_res (s : S) (v : U64) (sh : U64) (hsh : sh.val < 64) (off : U64)
    (a : core.result.Result U64 error.LookupFault) :
    (do
      let cf ← core.result.Result.Insts.CoreOpsTry.branch a
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let e ← st.read s val
        let i ← vspace.P_PRESENT
        let i1 ← lift (e &&& i)
        if i1 = 0#u64
        then ok (core.result.Result.Err (error.LookupFault.MissingCapability off))
        else
          let i2 ← vspace.P_PS
          let i3 ← lift (e &&& i2)
          if i3 != 0#u64
          then ok (core.result.Result.Err (error.LookupFault.MissingCapability off))
          else
            let i4 ← vspace.table_of e
            let i5 ← vspace.idx v sh
            let i6 ← vspace.entry_addr i4 i5
            ok (core.result.Result.Ok i6)
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          U64 (core.convert.FromSame error.LookupFault) residual) =
      ok (resStep (L.mem s) v sh.val off a) := by
  cases a with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
      core.convert.FromSame.from, resStep, bind_tc_ok]
  | Ok x =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, resStep]
    rw [L.read_eq, P_PRESENT_eq]
    simp only [bind_ok, lift]
    by_cases hp : eP (L.mem s x)
    · have h0 : ¬ (L.mem s x &&& 1#u64) = 0#u64 := hp
      rw [if_neg h0, P_PS_eq]
      simp only [bind_ok, lift]
      by_cases hs : eS (L.mem s x)
      · have h1 : ((L.mem s x &&& 128#u64) != 0#u64) = true := (eS_iff _).2 hs
        rw [if_pos h1, if_neg (show ¬ (eP (L.mem s x) ∧ ¬ eS (L.mem s x)) from fun hc => hc.2 hs)]
      · have h1 : ¬ ((L.mem s x &&& 128#u64) != 0#u64) = true := fun hc => hs ((eS_iff _).1 hc)
        rw [if_neg h1, if_pos (show eP (L.mem s x) ∧ ¬ eS (L.mem s x) from ⟨hp, hs⟩), table_of_eq]
        simp only [bind_ok]
        rw [idx_eq _ _ hsh]
        simp only [bind_ok]
        rw [entry_addr_eq _ _ (vIdx_lt _ _)]
        simp only [bind_ok, bind_tc_ok]
    · have h0 := (eP_iff _).2 hp
      rw [if_pos h0, if_neg (show ¬ (eP (L.mem s x) ∧ ¬ eS (L.mem s x)) from fun hc => hp hc.1)]

/-- **`lookup_pd_slot` is `walk2` on the store's memory.** -/
theorem lookup_pd_slot_res (s : S) (r v : U64) :
    vspace.lookup_pd_slot st s r v = ok (res2 (L.mem s) r v) := by
  unfold vspace.lookup_pd_slot res2
  rw [lookup_pdpt_slot_res]
  simp only [bind_ok]
  exact lookup_step_res s v 21#u64 (by decide) _ _

/-- **`lookup_pt_slot` is `walk3` on the store's memory.** -/
theorem lookup_pt_slot_res (s : S) (r v : U64) :
    vspace.lookup_pt_slot st s r v = ok (res3 (L.mem s) r v) := by
  unfold vspace.lookup_pt_slot res3
  rw [lookup_pd_slot_res]
  simp only [bind_ok]
  exact lookup_step_res s v 12#u64 (by decide) _ _

/-- A root `find_vspace_for_asid` finds at `s`, by the ASID table and a pool of `s`'s memory. -/
def NamedM (m : U64 → U64) (ksb r : U64) : Prop :=
  ∃ hi : U64, hi.val < 2048 ∧ m (atA ksb hi) ≠ 0#u64 ∧ ∃ lo : U64, lo.val < 512 ∧
    r = m (peA (m (atA ksb hi)) lo) ∧ r ≠ 0#u64 ∧ r &&& 1#u64 = 0#u64

/-- **The roots `find_asid` finds are named by the table and a pool** (without the native-root check). -/
theorem find_asid_named (s : S) (asid r : U64) (h : vspace.find_asid st s asid = ok (.Ok r)) :
    ∃ hi : U64, hi.val < 2048 ∧ L.mem s (atA (L.ksb s) hi) ≠ 0#u64 ∧ ∃ lo : U64, lo.val < 512 ∧
      r = L.mem s (peA (L.mem s (atA (L.ksb s) hi)) lo) ∧ r ≠ 0#u64 := by
  unfold vspace.find_asid at h
  obtain ⟨i, hi⟩ : ∃ i, asid >>> vspace.ASID_LOW_BITS = ok i := by
    have hL : vspace.ASID_LOW_BITS = 9#u64 := by unfold vspace.ASID_LOW_BITS; rfl
    rw [hL]; exact ⟨_, shr_u64_eq asid 9#u64 (by decide)⟩
  rw [hi] at h
  simp only [bind_ok] at h
  obtain ⟨pool, ep, h⟩ := bind_eq_ok h
  obtain ⟨pv, hpv, ep'⟩ := spec_ex_fd (asid_table_spec (st := st) s i)
  rw [hpv] at ep
  have hpool := ok_inj_ff ep
  subst hpool
  subst ep'
  have hlt := and_lt i 11 2047#u64 rfl (by decide)
  have hlo := and_lt asid 9 511#u64 rfl (by decide)
  by_cases hp0 : L.mem s (atA (L.ksb s) (i &&& 2047#u64)) = 0#u64
  · rw [if_pos hp0] at h
    simp at h
  rw [if_neg hp0] at h
  simp only [lift, bind_ok] at h
  rw [L.read_eq] at h
  simp only [bind_ok] at h
  by_cases hr0 : L.mem s (core.num.U64.wrapping_add (L.mem s (atA (L.ksb s) (i &&& 2047#u64)))
      (core.num.U64.wrapping_mul (asid &&& 511#u64) 8#u64)) = 0#u64
  · rw [if_pos hr0] at h
    simp at h
  rw [if_neg hr0] at h
  have hr := ok_inj_ff h
  simp only [core.result.Result.Ok.injEq] at hr
  exact ⟨_, hlt, hp0, _, hlo, hr.symm, by rw [← hr]; exact hr0⟩

/-- **The roots `find_vspace_for_asid` finds are named by the table and a pool.** -/
theorem find_vspace_for_asid_named (s : S) (asid r : U64)
    (h : vspace.find_vspace_for_asid st s asid = ok (.Ok r)) : NamedM (L.mem s) (L.ksb s) r := by
  unfold vspace.find_vspace_for_asid at h
  obtain ⟨x, ex, h⟩ := bind_eq_ok h
  cases x with
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame, core.convert.FromSame.from] at h
  | Ok w =>
    obtain ⟨hi, hhi, hne, lo, hlo, hw, hw0⟩ := find_asid_named s asid w ex
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, lift] at h
    by_cases h1 : (w &&& 1#u64) = 0#u64
    · rw [if_neg (show ¬ ((w &&& 1#u64) != 0#u64) = true by rw [h1]; simp)] at h
      have hr := ok_inj_ff h
      simp only [core.result.Result.Ok.injEq] at hr
      subst hr
      exact ⟨hi, hhi, hne, lo, hlo, hw, hw0, h1⟩
    · rw [if_pos (show ((w &&& 1#u64) != 0#u64) = true from bne_iff_ne.mpr h1)] at h
      simp at h

end walk

end Fl4Proofs.P2.PathObl

/-! ## 2. The convention -/

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P3.Vs (PtW PtWAll peA atA PtRel PtPlaced UserV VsWrite)

section conv
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The words a walk reads before the leaf**, in memory `m` at kernel base `ksb`. -/
def WalkW (ksb : U64) (m : U64 → U64) (b : U64) : Prop :=
  (∃ hi : U64, hi.val < 2048 ∧ b = atA ksb hi) ∨
  (∃ hi : U64, hi.val < 2048 ∧ m (atA ksb hi) ≠ 0#u64 ∧ ∃ lo : U64, lo.val < 512 ∧ b = peA (m (atA ksb hi)) lo) ∨
  (∃ r, NamedM m ksb r ∧ ∃ v, UserV v ∧
    (b = peA r (Fl4Proofs.P3.Vs.vIdx v 39) ∨ walk1 m r v = some b ∨ walk2 m r v = some b))

/-- **The reachability convention** (module docstring). -/
def ptesR (K : KLayoutP) (m : U64 → U64) : Set U64 :=
  {e | (∃ r, NamedM m K.ksb r ∧ ∃ v, UserV v ∧ walk3 m r v = some e) ∧ ¬ WalkW K.ksb m e ∧
    OwnMap.region K.toKLayout e = .none ∧ Aligned e ∧ e ∉ K.user ∧ (¬ ∃ v, InVcpu K.toKLayoutV v e) ∧
    ∀ o : U64, o.val < 13568 → e ≠ core.num.U64.wrapping_add K.ksb o}

/-- **The serial step's region facts hold for the convention, at any memory.** -/
theorem regionOKP_R {K : KLayoutP} {m : U64 → U64} (hK : RegionOKV K.toKLayoutV) (he : K.ptes = ptesR K m) :
    RegionOKP K :=
  ⟨hK, fun e h => by rw [he] at h; exact h.2.2.1, fun e h => by rw [he] at h; exact h.2.2.2.2.2.1⟩

/-- **The serial step's user facts hold for the convention, at any memory.** -/
theorem userOKP_R {K : KLayoutP} {m : U64 → U64} (hU : UserOKV K.toKLayoutV) (he : K.ptes = ptesR K m) :
    UserOKP K :=
  ⟨hU, fun e h => by rw [he] at h; exact ⟨h.2.2.2.1, h.2.2.2.2.1⟩⟩

theorem ptesR_ks {K : KLayoutP} {m : U64 → U64} : KsNoE (· ∈ ptesR K m) K.toKLayoutV :=
  fun o ho h => h.2.2.2.2.2.2 o ho rfl

end conv

/-! ## 3. At a bundle state agreeing on the gate words -/

section bundle
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A' : Type} {arI : machine.Arch A'}
  {AR : A' → Fl4Spec.Cr3 → Prop} {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64}
  {D : Set U64} {σ : S} {a' : A'} {τ : Fl4Spec.State Unit} {K : KLayoutP} {m : U64 → U64}

variable (st) in
/-- `σ` agrees with `m` on the gate words of the convention. -/
def GateAg (K : KLayoutP) (m : U64 → U64) (σ : S) : Prop :=
  ∀ w, OwnMap.region K.toKLayout w = .none → w ∉ ptesR K m → w ∉ K.user → Aligned w → L.mem σ w = m w

/-- A VSpace-object word is no user word at a bundle state. -/
theorem vobj_not_user (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) {b : U64}
    (hb : Fl4Proofs.P3.Vs.VObj Zx.th Zx.P Zx.L4 Zx.L3 Zx.L2 Zx.L1 (L.ksb σ) b) : b ∉ K.user := by
  have hTP := B.j.xtop.fin.1.2
  intro hu
  have hUs : K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b} := B.user
  rw [hUs] at hu
  obtain ⟨wp, hwp, hwe⟩ := hu
  exact hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hwp, by rw [hwe], by rw [hwe]; omega⟩))))))) hb

theorem ptw_vobj (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) {b : U64}
    (hb : PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 b) : Fl4Proofs.P3.Vs.VObj Zx.th Zx.P Zx.L4 Zx.L3 Zx.L2 Zx.L1 (L.ksb σ) b := by
  have hTP := B.j.xtop.fin.1.2
  obtain ⟨q, hq, i, hi, rfl⟩ := hb
  have hpa : q.val % 4096 = 0 := hTP.pt q hq
  have hv := Fl4Proofs.P3.Vs.peA_val (Fl4Proofs.P3.Vs.tbl_fit hpa) hi
  exact Or.inr (Or.inr (Or.inl ⟨q, Or.inr hq, by omega, by omega⟩))

/-- **The ASID-table words agree.** -/
theorem gateAg_tab (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) {hi : U64}
    (hhi : hi.val < 2048) : L.mem σ (atA K.ksb hi) = m (atA K.ksb hi) := by
  have hk : L.ksb σ = K.ksb := B.ksb
  have hTP := B.j.xtop.fin.1.2
  have hw := Fl4Proofs.P3.Vs.atA_vobj (th := Zx.th) (P := Zx.P) (L4 := Zx.L4) (L3 := Zx.L3) (L2 := Zx.L2)
    (L1 := Zx.L1) hTP.vs.ksb_fit hTP.vs.ksb_al hhi
  rw [hk] at hw
  refine hag _ (region_none_tab B hhi) (fun h => h.2.1 (Or.inl ⟨hi, hhi, rfl⟩)) ?_ hw.2
  have := vobj_not_user B (b := atA K.ksb hi) (by rw [hk]; exact hw.1)
  exact this

/-- **A named pool is a pool of `Zx`, and its words agree.** -/
theorem gateAg_pool (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) {hi : U64}
    (hhi : hi.val < 2048) (hne : m (atA K.ksb hi) ≠ 0#u64) :
    m (atA K.ksb hi) ∈ Zx.P ∧ ∀ lo : U64, lo.val < 512 →
      L.mem σ (peA (m (atA K.ksb hi)) lo) = m (peA (m (atA K.ksb hi)) lo) := by
  have hk : L.ksb σ = K.ksb := B.ksb
  have hTP := B.j.xtop.fin.1.2
  have hVR := B.j.xtop.fin.2.1
  have ht := gateAg_tab B hag hhi
  have hne' : L.mem σ (atA (L.ksb σ) hi) ≠ 0#u64 := by rw [hk, ht]; exact hne
  have hP : L.mem σ (atA (L.ksb σ) hi) ∈ Zx.P := hVR.tmem hi hhi hne'
  rw [hk, ht] at hP
  refine ⟨hP, fun lo hlo => ?_⟩
  have hw := Fl4Proofs.P3.Vs.pool_vobj (th := Zx.th) (L4 := Zx.L4) (L3 := Zx.L3) (L2 := Zx.L2) (L1 := Zx.L1)
    (ksb := L.ksb σ) hP (hTP.vs.pal _ hP).1 (hTP.vs.pal _ hP).2 hlo
  exact hag _ (region_none_pool B hP hlo) (fun h => h.2.1 (Or.inr (Or.inl ⟨hi, hhi, hne, lo, hlo, rfl⟩)))
    (vobj_not_user B hw.1) hw.2

/-- **A named root is a PML4 of `Zx.L4`**, also named at `σ`. -/
theorem named_L4 (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) {r : U64}
    (hr : NamedM m K.ksb r) : r ∈ Zx.L4 ∧ NamedM (L.mem σ) (L.ksb σ) r := by
  have hk : L.ksb σ = K.ksb := B.ksb
  have hPI := B.j.xtop.fin.2.2.2.1
  obtain ⟨hi, hhi, hne, lo, hlo, rfl, hr0, hr1⟩ := hr
  obtain ⟨hP, hpw⟩ := gateAg_pool B hag hhi hne
  have ht := gateAg_tab B hag hhi
  have e1 : L.mem σ (peA (m (atA K.ksb hi)) lo) = m (peA (m (atA K.ksb hi)) lo) := hpw lo hlo
  refine ⟨?_, ?_⟩
  · have := hPI _ hP lo hlo (by rw [e1]; exact hr0) (by rw [e1]; exact hr1)
    rw [e1] at this
    exact this
  · refine ⟨hi, hhi, by rw [hk, ht]; exact hne, lo, hlo, ?_, hr0, hr1⟩
    rw [hk, ht, e1]

/-- An upper-level entry of `Zx` agrees, when the walk reads it. -/
theorem gateAg_up (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) {q i : U64}
    (hq : q ∈ Zx.L4 ∨ q ∈ Zx.L3 ∨ q ∈ Zx.L2) (hi : i.val < 512) (hW : WalkW K.ksb m (peA q i)) :
    L.mem σ (peA q i) = m (peA q i) := by
  have hw : PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 (peA q i) := ⟨q, up_all (L1 := Zx.L1) hq, i, hi, rfl⟩
  have hTP := B.j.xtop.fin.1.2
  exact hag _ (region_none_ptw B hw) (fun h => h.2.1 hW) (vobj_not_user B (ptw_vobj B hw))
    (Fl4Proofs.P3.Vs.PtWAll.aligned hTP.pt hw)

/-- **The three walks answer alike in `m` and at `σ`** from a named root, for a user address. -/
theorem walk_agree (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) {r v : U64}
    (hr : NamedM m K.ksb r) (hv : UserV v) :
    walk1 (L.mem σ) r v = walk1 m r v ∧ walk2 (L.mem σ) r v = walk2 m r v ∧ walk3 (L.mem σ) r v = walk3 m r v := by
  have hPR := B.j.xtop.fin.2.2.1
  have hTP := B.j.xtop.fin.1.2
  obtain ⟨hr4, -⟩ := named_L4 B hag hr
  have e0 := gateAg_up B hag (Or.inl hr4) (Fl4Proofs.P3.Vs.vIdx_lt v 39) (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inl rfl⟩))
  have h1 : walk1 (L.mem σ) r v = walk1 m r v := by unfold walk1; rw [e0]
  -- the PDPT entry lies in a table of L3
  have hl1 : ∀ x, walk1 (L.mem σ) r v = some x → ∃ q ∈ Zx.L3, x = peA q (Fl4Proofs.P3.Vs.vIdx v 30) := by
    intro x hx
    obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pdpt_slot_rel σ τ hPR hTP.pt hr4 v hv)
    rw [lookup_pdpt_slot_res] at hrr
    have := ok_inj_ff hrr
    subst this
    exact hsl x (res1_ok.2 hx)
  have h2 : walk2 (L.mem σ) r v = walk2 m r v := by
    unfold walk2
    rw [← h1]
    cases hx : walk1 (L.mem σ) r v with
    | none => rfl
    | some x =>
      obtain ⟨q, hq, rfl⟩ := hl1 x hx
      have e := gateAg_up B hag (Or.inr (Or.inl hq)) (Fl4Proofs.P3.Vs.vIdx_lt v 30)
        (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inr (Or.inl (h1.symm.trans hx))⟩))
      simp only [walkStep, e]
  have hl2 : ∀ x, walk2 (L.mem σ) r v = some x → ∃ q ∈ Zx.L2, x = peA q (Fl4Proofs.P3.Vs.vIdx v 21) := by
    intro x hx
    obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pd_slot_rel σ τ hPR hTP.pt hr4 v hv)
    rw [lookup_pd_slot_res] at hrr
    have := ok_inj_ff hrr
    subst this
    exact hsl x (res2_ok.2 hx)
  have h3 : walk3 (L.mem σ) r v = walk3 m r v := by
    unfold walk3
    rw [← h2]
    cases hx : walk2 (L.mem σ) r v with
    | none => rfl
    | some x =>
      obtain ⟨q, hq, rfl⟩ := hl2 x hx
      have e := gateAg_up B hag (Or.inr (Or.inr hq)) (Fl4Proofs.P3.Vs.vIdx_lt v 21)
        (Or.inr (Or.inr ⟨r, hr, v, hv, Or.inr (Or.inr (h2.symm.trans hx))⟩))
      simp only [walkStep, e]
  exact ⟨h1, h2, h3⟩

/-- A walk from a PML4 of `Zx.L4` that reaches an entry at `σ` reaches a leaf entry. -/
theorem walk3_leaf (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) {r v e : U64}
    (hr4 : r ∈ Zx.L4) (hv : UserV v) (h : walk3 (L.mem σ) r v = some e) : PtW Zx.L1 e := by
  have hPR := B.j.xtop.fin.2.2.1
  have hTP := B.j.xtop.fin.1.2
  obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pt_slot_rel σ τ hPR hTP.pt hr4 v hv)
  rw [lookup_pt_slot_res] at hrr
  have := ok_inj_ff hrr
  subst this
  obtain ⟨q, hq, rfl⟩ := hsl e (res3_ok.2 h)
  exact ⟨q, hq, _, Fl4Proofs.P3.Vs.vIdx_lt _ _, rfl⟩

/-- **Every word of the convention is a leaf entry of `Zx`.** -/
theorem ptesR_sub (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) :
    ∀ e ∈ ptesR K m, PtW Zx.L1 e := by
  rintro e ⟨⟨r, hr, v, hv, hw⟩, -⟩
  obtain ⟨hr4, -⟩ := named_L4 B hag hr
  obtain ⟨-, -, h3⟩ := walk_agree B hag hr hv
  exact walk3_leaf B hr4 hv (h3.trans hw)

/-- **`QPs` at `σ` for the convention.** -/
theorem qPs_R (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ)
    (he : K.ptes = ptesR K m) (nv : K.vcpus = ∅) : QPs K st σ :=
  qPs_of_bundle B (fun b hb => by rw [he] at hb; exact ptesL1_sub Zx (ptesR_sub B hag b hb)) nv

/-- A leaf entry of `Zx` is no word a walk in `m` reads before the leaf. -/
theorem leaf_not_walkW (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ) {e : U64}
    (hl : PtW Zx.L1 e) : ¬ WalkW K.ksb m e := by
  have hk : L.ksb σ = K.ksb := B.ksb
  have hTP := B.j.xtop.fin.1.2
  have hPR := B.j.xtop.fin.2.2.1
  obtain ⟨q, hq, i, hi, rfl⟩ := hl
  have hall : PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 (peA q i) := ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, rfl⟩
  rintro (⟨hi', hhi, he⟩ | ⟨hi', hhi, hne, lo, hlo, he⟩ | ⟨r, hr, v, hv, he⟩)
  · exact hTP.pv _ hall (Or.inl ⟨hi', hhi, by rw [hk]; exact he⟩)
  · obtain ⟨hP, -⟩ := gateAg_pool B hag hhi hne
    exact hTP.pv _ hall (Or.inr ⟨_, hP, lo, hlo, he⟩)
  · obtain ⟨hr4, -⟩ := named_L4 B hag hr
    obtain ⟨h1, h2, -⟩ := walk_agree B hag hr hv
    rcases he with he | he | he
    · exact ptw_up_ne hPR hTP.pt hq (Or.inl hr4) hi (Fl4Proofs.P3.Vs.vIdx_lt v 39) he
    · obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pdpt_slot_rel σ τ hPR hTP.pt hr4 v hv)
      rw [lookup_pdpt_slot_res] at hrr
      have := ok_inj_ff hrr
      subst this
      obtain ⟨q', hq', he'⟩ := hsl _ (res1_ok.2 (h1.trans he))
      exact ptw_up_ne hPR hTP.pt hq (Or.inr (Or.inl hq')) hi (Fl4Proofs.P3.Vs.vIdx_lt v 30) he'
    · obtain ⟨rr, hrr, -, hsl, -⟩ := spec_ex_fd (Fl4Proofs.P3.Vs.lookup_pd_slot_rel σ τ hPR hTP.pt hr4 v hv)
      rw [lookup_pd_slot_res] at hrr
      have := ok_inj_ff hrr
      subst this
      obtain ⟨q', hq', he'⟩ := hsl _ (res2_ok.2 (h2.trans he))
      exact ptw_up_ne hPR hTP.pt hq (Or.inr (Or.inr hq')) hi (Fl4Proofs.P3.Vs.vIdx_lt v 21) he'

/-- **`PtePlanLocked`'s [J] half for the runs that write** (module docstring): the root `find_vspace_for_asid`
finds at `σ` (the decode's `check_vspace`) and the entry `lookup_pt_slot` finds from it at `σ`, for a user address,
give an entry of the convention. -/
theorem ptesR_of_run (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout σ a' τ) (hag : GateAg st K m σ)
    (nv : K.vcpus = ∅) {asid r v e : U64} (hf : vspace.find_vspace_for_asid st σ asid = ok (.Ok r)) (hv : UserV v)
    (hl : vspace.lookup_pt_slot st σ r v = ok (.Ok e)) : e ∈ ptesR K m := by
  have hk : L.ksb σ = K.ksb := B.ksb
  have hTP := B.j.xtop.fin.1.2
  have hVR := B.j.xtop.fin.2.1
  have hPI := B.j.xtop.fin.2.2.2.1
  -- the root, named at `σ`, is named in `m`
  obtain ⟨hi, hhi, hne, lo, hlo, hre, hr0, hr1⟩ := find_vspace_for_asid_named σ asid r hf
  rw [hk] at hne hre
  have ht := gateAg_tab B hag hhi
  rw [ht] at hne hre
  obtain ⟨-, hpw⟩ := gateAg_pool B hag hhi hne
  rw [hpw lo hlo] at hre
  have hrN : NamedM m K.ksb r := ⟨hi, hhi, hne, lo, hlo, hre, hr0, hr1⟩
  obtain ⟨hr4, -⟩ := named_L4 B hag hrN
  rw [lookup_pt_slot_res] at hl
  have hw : walk3 (L.mem σ) r v = some e := res3_ok.1 (ok_inj_ff hl)
  obtain ⟨-, -, h3⟩ := walk_agree B hag hrN hv
  have hleaf := walk3_leaf B hr4 hv hw
  have hall : PtWAll Zx.L4 Zx.L3 Zx.L2 Zx.L1 e := by
    obtain ⟨q, hq, i, hi, rfl⟩ := hleaf; exact ⟨q, Or.inr (Or.inr (Or.inr hq)), i, hi, rfl⟩
  refine ⟨⟨r, hrN, v, hv, h3.symm.trans hw⟩, leaf_not_walkW B hag hleaf, region_none_ptw B hall,
    Fl4Proofs.P3.Vs.PtWAll.aligned hTP.pt hall, vobj_not_user B (ptw_vobj B hall),
    fun ⟨_, hv'⟩ => not_inVcpu_empty nv hv', fun o ho he => ?_⟩
  have := ptesJ_ks B.j o ho
  rw [hk] at this
  exact this (by rw [← he]; exact ptesL1_sub Zx hleaf)

end bundle

end Fl4Proofs.P2.E2EP
