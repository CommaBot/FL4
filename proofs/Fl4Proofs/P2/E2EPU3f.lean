/-
# P2 (line mmuAD, gen 7): **`serializable_fl4_localU3b`** — the page walker's A/D writes, unconditional over U2's family

gen 6's `serializable_fl4_localU3b_ofAcc` left `hDelA` / `hInvA`: accepted runs of delPte and of the no-PTE-lock
CNodeDelete are `InsT` (paging words of the epoch read only `ADEq`-insensitively, stored only non-present).
Here they are proved, for the two slots **restricted to `QPs (KU K E)`** (as gen 5's W11 slots): at a start state
of the epoch that restriction holds (`qPs_of_convR` + `qPs_ku`), and it is what makes the ASID table and pool
words that `find_vspace_for_asid` reads non-paging words of the epoch (`TabNoE` at `KU K E`; the pool pointer is
the epoch's, so a pool entry is an `AsidW` word of `E`, never in `PWE K E`).

The walk of an accepted run (`R.invBodyG`):
* `¬ InvLen` (decode length < 2): the whole run is reproduced on `guard st (¬ PWE) (¬ PWE)` (`inv_acc_genR` with
  invj's truncated arm `truncAccR` / `truncFinR`; every read is an `IoRSR` or user word, every write an `IoWS` or
  user word), so it touches no paging word (`insT_guardRun`);
* `InvLen`: `MmuADEnt.insT_entR` (entry, checks, IPC buffer, invoked slot) then `MmuADDelP.insT_blkP` /
  `insT_blkN` (the decode: `cnode.decode` → `cdt.delete` → `finalise_cap` → `unmap_page`, whose
  `find_vspace_for_asid` reads ASID words only, whose walk `lookup_pt_slot` and leaf read use the value only through
  `&&& 1`, `&&& 128`, `ADDR_MASK`, and which stores `0`; then `empty_slot`, the reply, `after_invocation`,
  `finish`).

**No real-run read uses bits 5–6**: every paging-word read of these runs is a walk or leaf read of `unmap_page`.

Results: `ioWS_notPWE`, `insT_guardRun`, `trunc_len`, **`accIns_delR`**, **`accIns_invR`**, **`insA_delR`**,
**`insA_invR`**, **`serializable_fl4_localU3b`**.

Premises of `serializable_fl4_localU3b`: exactly U2's (`P`, [P] `hIoa`, `h0`, `hA0`, `hB`, `hc0`, `hM0`, the
execution, `hq`) and [P] `MmuAD` (inside `ExecU3b`). No [W], no new [J]. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU3e
import Fl4Proofs.P2.MmuADDelP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.E2E (StartAt SP LocalPath InsT insT_of_within)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll InsA)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

section gen
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **A run reproduced on a store guarded off `G` is `InsT`.** -/
theorem insT_guardRun (P : LocalPath own cls ko User) {G R W : U64 → Prop} {Q : U64 → U64 → Prop}
    {NP : U64 → Prop} (hR : ∀ q, R q → ¬ G q) (hW : ∀ q, W q → ¬ G q) {s : P.S} {a : P.A}
    {r : P.X × P.S × P.A} (hs : P.Pre s) (h : P.F P.ar (@guard P.S P.st R W) s a = ok r) :
    InsT P.st P.ar G Q NP User P.p s a := by
  letI := P.L
  rw [P.isProg _ (Narrow.guard _ _ _) s (AltOf.pre hs) a] at h
  exact insT_of_within P.p s a (Within.mono (fun b hb => hR b hb) (fun b hb => Or.inr (hW b hb)) P.p s a
    (interp_guard P.p s a r h).2)

end gen

section words
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutP} {E : U64 → U64}

/-- No word an accepted run may write (`IoWS`) is a paging word of the epoch (they are the gate's). -/
theorem ioWS_notPWE (hK : RegionOKP K) {Locks : S → U64 → Prop} {s : S} {x : U64}
    (h : IoWS (st := st) K.toKLayout Locks s x) : ¬ PWE K E x := by
  intro hp
  have hw := h.2
  unfold WPerm at hw
  rw [own_pwe_gate hK hp] at hw
  exact hw

/-- A message length below 2 gives a decode length below 2 (`Result` form of the clamp). -/
theorem trunc_len {info : msginfo.MessageInfo} {buf length : U64} (hil : info.length < 2#u64)
    (hl : (if info.length > msg.N_MSG_REGISTERS then (if buf = 0#u64 then ok msg.N_MSG_REGISTERS else ok info.length)
      else ok info.length) = ok length) : length < 2#u64 := by
  have ht := len_trunc (buf := buf) hil
  by_cases c1 : info.length > msg.N_MSG_REGISTERS
  · rw [if_pos c1] at hl ht
    by_cases c2 : buf = 0#u64
    · rw [if_pos c2] at hl ht; rw [← ok_inj_ff hl]; exact ht
    · rw [if_neg c2] at hl ht; rw [← ok_inj_ff hl]; exact ht
  · rw [if_neg c1] at hl ht; rw [← ok_inj_ff hl]; exact ht

/-- `¬ InvLen` gives a message length below 2. -/
theorem len_lt2 {s : S} {info : msginfo.MessageInfo} (hL : ¬ InvLen st s)
    (emi : msg.msg_info st s (L.curW s) = ok info) : info.length < 2#u64 := by
  by_contra hc
  apply hL
  intro t info' ht hi'
  have et : t = L.curW s := ok_inj_ff (ht.symm.trans (cur_thread_ok s))
  subst et
  rw [emi] at hi'
  have ei : info = info' := ok_inj_ff hi'
  subst ei
  have : ¬ info.length.val < 2 := fun h' => hc (by scalar_tac)
  omega

/-- The ASID words of a `QPs (KU K E)` bundle state as a `find_vspace_for_asid` read set off `PWE K E`. -/
theorem rdTab_ku {s : S} (hT : RdTab (L := L) (VsW K.toKLayout) s) (hq : QPs (KU K E) st s) :
    RdTab (L := L) (fun q => VsW K.toKLayout q ∧ q ∉ (KU K E).ptes) s := fun hi hhi =>
  ⟨⟨(hT hi hhi).1, (hq.tab hi hhi).1⟩, fun lo hlo h0 => ⟨(hT hi hhi).2 lo hlo h0, (hq.tab hi hhi).2 lo hlo h0⟩⟩

theorem rf_notPWE {q : U64} (h : VsW K.toKLayout q ∧ q ∉ (KU K E).ptes) : ¬ PWE K E q :=
  fun hp => h.2 ⟨hp, h.1.1⟩

end words

/-! ## delPte -/

section del
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- delPte's path restricted to `QPs (KU K E)` states. -/
noncomputable abbrev delPteR (j : InvArg S) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (h : DelPtePrem st j K) :
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  (delPtePath st ar hA hm j K m hK hU h).restrQ (QPt (KU K E) (delPtePath st ar hA hm j K m hK hU h))
    (qPt_stab (KU K E) _ (fun b hb => Or.inl hb))

set_option maxHeartbeats 4000000 in
/-- **delPte's accepted runs are `InsT` at the epoch's paging words** (module docstring). -/
theorem accIns_delR (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : DelPtePrem st j K) : AccIns (delPteR st ar hA hm j K E m hK hU h) (PWE K E) := by
  intro (s : S) (a : A) (r : Bool × S × A) hs hr hacc
  obtain ⟨hE0, hqE0⟩ := hs
  have hE : PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s := hE0
  have hqE : QPs (KU K E) st s := hqE0
  have nv := h.nv
  have hks := ksNoE_conv hE.2.2.choose_spec.1
  have PE := hE.2.1.1.1.1
  have hr0 : syscall.handle_invocation_local st ar s a j.number j.p = ok r := hr
  have h0 : syscall.handle_invocation_local st ar s a j.number j.p = ok (true, r.2.1, r.2.2) := by
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc
    subst hb
    exact hr0
  by_cases hL : InvLen st s
  · -- the decode arm: the entry walk, then the decode block
    have hp := inv_isProgOnP (st := st) (Cs := j.Cs) (Ω := j.Ω) (Sg := j.Sg) (Ac := j.Ac) (Locks := j.Locks)
      (number := j.number) (p := j.p) (m := m) hA hK
    have hr' : interp st ar (R.invBodyG j.number j.p) s a = ok r := by
      rw [← inv_hp hp (Narrow.self st) (AltOf.pre hE) a]; exact hr0
    show InsT st ar (PWE K E) ADEq NotPresent (· ∈ K.user) (R.invBodyG j.number j.p) s a
    refine insT_entR hA (P := fun s => PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K m s ∧ QPs (KU K E) st s ∧
        InvLen st s) (Locks := j.Locks) (fun s h => h.1.2.1.1.1.1)
      (fun s h q hq => hq.elim (ioRSR_notPWE hK (ksNoE_conv h.1.2.2.choose_spec.1)) (ioWS_notPWE hK))
      (fun s h => invSeenR_of h.1.1 h.1.2.1) (fun s h => invPsR_of h.1.2.1) ?_ s a r ⟨hE, hqE, hL⟩
      ⟨_, _, h0⟩ hr'
    intro s a info nx s1 s2 a1 buf length cap r' hs _ emi C ebuf ecap hl hR
    obtain ⟨⟨hJ, hq, m1, hc, hag⟩, hqs, hLs⟩ := hs
    have PE := hq.1.1.1
    have hks := ksNoE_conv hc
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    have hlen : ¬ length < 2#u64 := len_ge2 (hLs (L.curW s) info (cur_thread_ok s) emi) hl
    have Ed := delEntP_of (P := fun s => SlJAt (L := L) K.toKLayout s) hJ hq (invCdtJ_of (fun _ h => h))
      (hz_of _ s hJ)
    have hvs := invVsJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h)
    have hlf := invLeafJ_of (st := st) (P := fun s => SlJAt (L := L) K.toKLayout s) (fun _ h => h) s hJ
    have hJ' := hJ
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
      ptesR_sub B hag b (by rw [← hc]; exact hb)
    exact insT_blkP hA (fun q h => ioRSR_notPWE hK hks h) (fun q h => ioWS_notPWE hK h)
      (fun q h => rf_notPWE h) (rdTab_ku B.rdTab hqs) B.rdTab PE Ed hsK hlen (B.vsJX hsub)
      (fun sl fp rt asid va hsl hc' hA' => hvs s sl fp rt asid va hJ' hsl hc' hA') hlf C ecap hlbl hR
  · -- the truncated arm: the whole run on `guard st (¬ PWE) (¬ PWE)`
    haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    have hW : IoWr st (fun b => ¬ PWE K E b) K.heap.scBits s := (PE.ioWr (Locks := j.Locks)).mono (fun _ h => ioWS_notPWE hK h)
    have hg := inv_acc_genR (W := fun b => ¬ PWE K E b)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW (invSeenR_of hE.1 hE.2.1) (invPsR_of hE.2.1)
      (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => ?_) h0
    · have hg' : (delPteR st ar hA hm j K E m hK hU h).F (delPteR st ar hA hm j K E m hK hU h).ar
          (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s a = ok r := by
        obtain ⟨b, s1, a1⟩ := r
        have hb : b = true := hacc
        subst hb
        exact hg
      exact insT_guardRun _ (fun _ h => h) (fun _ h => h) ⟨hE0, hqE0⟩ hg'
    have hq := hE.2.1
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_coreP hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    rw [hlbl] at hy ⊢
    have hlen : length < 2#u64 := trunc_len (len_lt2 hL emi) hl
    clear this
    obtain ⟨hdec, hrep⟩ := truncAccR (R := fun b => ¬ PWE K E b) (Locks := j.Locks)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE
      (fun _ h => ioRSR_notPWE hK hks h) (fun _ h hp => pwe_user hU hp h.2) hW
      (fun _ h hp => pwe_user hU hp h.2) hcs hsK (invBufJ8_of hE.1) hc hk hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    obtain ⟨h1, h2⟩ := truncFinR (Locks := j.Locks) (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW
      (SWr.of_W (ioWS_notPWE hK (PE.stw (Locks := j.Locks)).2)) hcs hsK (invBufJ8_of hE.1) hc hk hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- **`hIns` for delPte** (module docstring): the slot started at an epoch state is the restricted path's start. -/
theorem insA_delR (j : InvArg S) {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe) (J : EpochJ K E s) (hM : MapsP K s)
    (h : StartAt (delPteSlot st ar hA hm j K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  by_cases hp : DelPtePrem st j K
  · rw [delPteSlot_pos st ar hA hm hp] at h
    obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
    have hpre' : PreP st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K s.mem σ := hpre
    obtain ⟨s1, ⟨nv, he⟩, hkeep⟩ := epoch_start J
    have hq0 : QPs K st σ := qPs_of_convR he nv hb hkeep hpre'.2.1.1.1.1.kb.symm hμ
    have hqK : QPs (KU K E) st σ := qPs_ku L J hb hq0 hμ
    have h' : StartAt (delPteR st ar hA hm j K E s.mem hK hU hp) c hs s.mem
        ((delPtePath st ar hA hm j K s.mem hK hU hp).body σ a) :=
      ⟨σ, a, ⟨hpre, hqK⟩, hc, hl, hμ, rfl⟩
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQ _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (accIns_delR st ar hA hm j hK hU hp)
      (fun s1 s2 a r hs1 hr hn Al => delPte_dec st ar hA hm j hK hU hp s1 s2 a r hs1.1 hr hn Al) h'
  · unfold delPteSlot at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end del

/-! ## CNodeDelete without a PTE lock -/

section inv
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- The no-PTE CNodeDelete path restricted to `QPs (KU K E)` states. -/
noncomputable abbrev invR (j : InvArg S) (K : KLayoutP) (E m : U64 → U64) (hK : RegionOKP K)
    (hU : UserOKP K) (h : InvPremW st j K.toKLayoutV m) :
    LocalPath (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) :=
  (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvU st ar hA hm j K m hK hU h)).restrQ
    (QPt (KU K E) (LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (invAvU st ar hA hm j K m hK hU h)))
    (qPt_stab (KU K E) _ (fun b hb => Or.inl hb))

set_option maxHeartbeats 4000000 in
/-- **The no-PTE CNodeDelete's accepted runs are `InsT` at the epoch's paging words** (module docstring). -/
theorem accIns_invR (j : InvArg S) {K : KLayoutP} {E m : U64 → U64} (hK : RegionOKP K) (hU : UserOKP K)
    (h : InvPremW st j K.toKLayoutV m) : AccIns (invR st ar hA hm j K E m hK hU h) (PWE K E) := by
  intro (s : S) (a : A) (r : Bool × S × A) hs hr hacc
  have hs' := hs
  obtain ⟨hE0, hqE0⟩ := hs
  have hE : (SlJAt (L := L) K.toKLayout s ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧
      QU st K s := hE0
  have hqE : QPs (KU K E) st s := hqE0
  have hks := hE.2.1.ks
  have PE := hE.1.2.1.1.1
  have hr0 : syscall.handle_invocation_local st ar s a j.number j.p = ok r := hr
  have h0 : syscall.handle_invocation_local st ar s a j.number j.p = ok (true, r.2.1, r.2.2) := by
    obtain ⟨b, s1, a1⟩ := r
    have hb : b = true := hacc
    subst hb
    exact hr0
  by_cases hL : InvLen st s
  · letI := (invR st ar hA hm j K E m hK hU h).L
    have hr' : interp st ar (R.invBodyG j.number j.p) s a = ok r :=
      ((invR st ar hA hm j K E m hK hU h).isProg _ (Narrow.self st) s (AltOf.pre hs') a).symm.trans hr
    show InsT st ar (PWE K E) ADEq NotPresent (· ∈ K.user) (R.invBodyG j.number j.p) s a
    refine insT_entR hA (P := fun s => ((SlJAt (L := L) K.toKLayout s ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s) ∧ QU st K s) ∧ QPs (KU K E) st s ∧
        InvLen st s) (Locks := j.Locks) (fun s h => h.1.1.2.1.1.1)
      (fun s h q hq => hq.elim (ioRSR_notPWE hK h.1.2.1.ks) (ioWS_notPWE hK))
      (fun s h => invSeenRN h.1.1.1 h.1.1.2) (fun s h => invPsRN h.1.1.2) ?_ s a r ⟨hE, hqE, hL⟩
      ⟨_, _, h0⟩ hr'
    intro s a info nx s1 s2 a1 buf length cap r' hs _ emi C ebuf ecap hl hR
    obtain ⟨⟨⟨hJ, hq⟩, hqU, m1, hconv, hag⟩, hqs, hLs⟩ := hs
    have PE := hq.1.1.1
    have hks := hqU.ks
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    have hlen : ¬ length < 2#u64 := len_ge2 (hLs (L.curW s) info (cur_thread_ok s) emi) hl
    have hvsP := invVsJ_of (st := st)
      (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s)
      (fun _ h => h.1)
    have Ed := delEnt_of
      (P := fun s => SlJAt (L := L) K.toKLayout s ∧ InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout m s)
      ⟨hJ, hq⟩ hq hvsP (invCdtJ_of (fun _ h => h.1)) (hz_of _ s hJ)
    have hJ' := hJ
    obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
    have hsub : ∀ b, b ∈ K.ptes → Fl4Proofs.P3.Vs.PtW Zx.L1 b := fun b hb =>
      ptesR_sub B hag b (by rw [← hconv]; exact hb)
    exact insT_blkN hA (fun q h => ioRSR_notPWE hK hks h) (fun q h => ioWS_notPWE hK h)
      (fun q h => rf_notPWE h) (rdTab_ku B.rdTab hqs) B.rdTab PE Ed hsK hlen (B.vsJX hsub)
      (fun sl fp rt asid va hsl hc' hA' => hvsP s sl fp rt asid va ⟨hJ', hq⟩ hsl hc' hA') C ecap hlbl hR
  · haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    have hW : IoWr st (fun b => ¬ PWE K E b) K.heap.scBits s := (PE.ioWr (Locks := j.Locks)).mono (fun _ h => ioWS_notPWE hK h)
    have hg := inv_acc_genR (W := fun b => ¬ PWE K E b)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW (invSeenRN hE.1.1 hE.1.2) (invPsRN hE.1.2)
      (fun info nx s1 s2 a1 buf length cap emi hc hl hk y hy => ?_) h0
    · have hg' : (invR st ar hA hm j K E m hK hU h).F (invR st ar hA hm j K E m hK hU h).ar
          (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) s a = ok r := by
        obtain ⟨b, s1, a1⟩ := r
        have hb : b = true := hacc
        subst hb
        exact hg
      exact insT_guardRun _ (fun _ h => h) (fun _ h => h) hs' hg'
    have hq := hE.1.2
    obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, hcs, hsK, -⟩ := del_core hq
    have hlbl := (hq.1.2.2.1 (L.curW s) info (cur_thread_ok s) emi).1
    rw [hlbl] at hy ⊢
    have hlen : length < 2#u64 := trunc_len (len_lt2 hL emi) hl
    clear this
    obtain ⟨hdec, hrep⟩ := truncAccR (R := fun b => ¬ PWE K E b) (Locks := j.Locks)
      (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE
      (fun _ h => ioRSR_notPWE hK hks h) (fun _ h hp => pwe_user hU hp h.2) hW
      (fun _ h hp => pwe_user hU hp h.2) hcs hsK (invBufJ8_of hE.1.1) hc hk hlen hy
    refine ⟨hdec, fun z hz' => ?_⟩
    haveI : GRd (guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) st (IoRSR st K.toKLayout j.Locks s) :=
      grd_sub (fun _ h => ioRSR_notPWE hK hks h)
    obtain ⟨h1, h2⟩ := truncFinR (Locks := j.Locks) (gS := guard st (fun b => ¬ PWE K E b) (fun b => ¬ PWE K E b)) hA PE hW
      (SWr.of_W (ioWS_notPWE hK (PE.stw (Locks := j.Locks)).2)) hcs hsK (invBufJ8_of hE.1.1) hc hk hlen hy hz'
    exact ⟨hrep z hz', h1, h2⟩

/-- **`hIns` for the no-PTE CNodeDelete** (module docstring). -/
theorem insA_invR (j : InvArg S) {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64}
    {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {hs : U64 → Prop} {q : SP}
    (hb : ∃ σe, SlJAt (L := L) K.toKLayout σe) (J : EpochJ K E s) (hM : MapsP K s)
    (h : StartAt (invSlotU st ar hA hm j K s.mem hK hU) c hs s.mem q) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c hs s.mem q := by
  by_cases hp : InvPremW st j K.toKLayoutV s.mem
  · rw [invSlotU_pos st ar hA hm hp] at h
    obtain ⟨σ, a, hpre, hc, hl, hμ, rfl⟩ := h
    have hpre' : (SlJAt (L := L) K.toKLayout σ ∧
        InvQF st j.Cs j.Ω j.Sg j.Ac j.Locks j.p K.toKLayout s.mem σ) ∧ QU st K σ := hpre
    have hqK : QPs (KU K E) st σ := qPs_ku L J hb hpre'.2.1 hμ
    have h' : StartAt (invR st ar hA hm j K E s.mem hK hU hp) c hs s.mem
        ((LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx s.mem) _
          (invAvU st ar hA hm j K s.mem hK hU hp)).body σ a) :=
      ⟨σ, a, ⟨hpre, hqK⟩, hc, hl, hμ, rfl⟩
    rw [hM.own, hM.cls, hM.ko]
    exact LocalPath.insAQ _ adEq_equiv (moveHeldP hK) (ownDepP hK hU) (pwe_own hK) (fun x hx => pwe_ko hK _ hx)
      (fun x hx => pwe_user hU hx) (accIns_invR st ar hA hm j hK hU hp)
      (fun s1 s2 a r hs1 hr hn Al => inv_dec st ar hA hm j hK hU hp s1 s2 a r hs1.1 hr hn Al) h'
  · unfold invSlotU at h
    rw [dif_neg hp] at h
    obtain ⟨σ, a, hpre, -⟩ := h
    exact (hpre : False).elim

end inv

/-! ## The top -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

end top

end
end Fl4Proofs.P2.E2EP
