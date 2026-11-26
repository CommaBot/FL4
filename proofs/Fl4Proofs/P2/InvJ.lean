/-
# P2 (line invj, generation 1): the CNodeDelete arm of the frame-cap invocation path, premises closed

stpost gen 14's paths (`inv_pathsKF2` at `Q := InvQL`, P2/InvMove.lean; `inv_pathsKFU` at `Q := InvQF`,
P2/InvDelU.lean) with hpzg's program and layout premises (gen 6–9) and this line's `InvVsJ` (P2/InvVsJ.lean):

* `invPlanD_wrF`, **`hufQF_of2`**: hpzg gen 9's `invPlanD_wr` / `hufQL_of2` at `InvQF` (no length clause), for
  `inv_pathsKFU`'s `huf`;
* `once_agreeJ`: slhuf gen 10's `once_agree` (par/slhuf3 `P2/SlOnceL.lean`, not on this base), copied under a new
  name (`Once` carried to a state agreeing on a guarded run's read set);
* **`invURoAccW_of`**: `InvURoAccW` (ReadOnce of accepted runs over `InvCMRS`) split on `InvLen`. A run with
  `length ≥ 2` is accepted on `guard st (IoRS s) (IoWS s)` (`InvAccW` at `InvQL`, stpost's `invAccW_of2` +
  `invBlkW2_of`), so it reads no user word: `once_of_guardG` gives `Once` at the entry, `once_agreeJ` carries it to
  every alternative (they agree on `IoRS s ⊆ InvCMRS s`), `onceU_monoR` widens the read set. The truncated half
  is the premise **`InvURoTrW`** [W];
* **`inv_pathsKF3`** (and `_startAt`): `inv_pathsKF2` with `hvs := invVsJ_of`, `hcdt := invCdtJ_of`,
  `hz := hz_of`, `huf := hufQL_of2 hIw hlk`, `hpz := inv_hpz …` (`hSC := invSlotCNK_of`, `hSeen := invSeen_of`).
  Premises: `hA`, [P] `hm`, [J] `hIw`, [P] `hlk`;
* **`inv_pathsKFU2`**: `inv_pathsKFU8` (P2/InvTrunc8.lean: `inv_pathsKFU` with stpost's false `InvBufJ` replaced
  by its true 128-word form `InvBufJ8`) likewise, `hbuf := invBufJ8_of` (P3's `JAtZ.bufOK`),
  `huf := hufQF_of2 hIw hlk`, `hpz`'s `InvURoAccW` from `invURoAccW_of`. Premises: `hA`, [P] `hm`, [J] `hIw`,
  [P] `hlk`, [W] `htr : InvURoTrW`.

No existing statement changes; no `kernel_entry_reach*` is touched.
-/
import Fl4Proofs.P2.InvVsJ
import Fl4Proofs.P2.InvSC
import Fl4Proofs.P2.InvDelU
import Fl4Proofs.P2.InvTrunc8
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout fld RegionOK)
open Fl4Proofs.P2.E2E (Once ReadOnce)

/-! ## `huf` at `InvQF` -/

section huf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {Cs Ω Sg Ac : Set U64}

/-- `invPlanD_wr` (hpzg gen 9) at `InvQF`: the plan survives a user write at a bundle state. -/
theorem invPlanD_wrF {Locks : S → U64 → Prop} {p : localinv.Plan} :
    ∀ K m s b v, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      InvPlanD st p (L.wr s b v) := by
  intro K m s b v hJ hqf hb hba
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, C, hcap, hsK, -, -, hC, hcl, hCs, -⟩ := del_core hqf
  obtain ⟨⟨hio, ⟨t, info, ex, ht, hi, hpw⟩, harm, -⟩, -⟩ := hqf
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have et : t = L.curW s := by rw [cur_thread_ok] at ht; exact (ok_inj_ff ht).symm
  subst et
  have hlbl := (harm _ info (cur_thread_ok s) hi).1
  rw [hlbl] at hpw
  refine ⟨L.curW s, info, ex, ?_, ?_, ?_⟩
  · rw [cur_thread_ok, hJ.curW_wr hb hba v]
  · rw [msgInfo_wr hJ hb hba v hT P.tA]; exact hi
  · rw [hlbl, planDel_userWr hJ P hb hba v hsK hcap hC hcl (fun p r m y hp hm => (hCs p r m y hp hm).1) ex]
    exact hpw

/-- (invj gen 1) **`inv_pathsKFU`'s `huf`** at `Pre := SlJAt K ∧ InvQF …`, from [J] `hIw` (`IoPre` survives a user
write at a bundle state) and [P] `hlk` (the locks are kept). -/
theorem hufQF_of2 {Locks : S → U64 → Prop} {p : localinv.Plan}
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    ∀ K m s b v, SlJAt (L := L) K s → InvQF st Cs Ω Sg Ac Locks p K m s → b ∈ K.user → Aligned b →
      (SlJAt (L := L) K (L.wr s b v) ∧ InvQF st Cs Ω Sg Ac Locks p K m (L.wr s b v)) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s := by
  intro K m s b v hJ hq hb hba
  have hq0 := hq
  obtain ⟨⟨hio, hpd, harm, hlks⟩, hlk0⟩ := hq
  have P := hio.1
  have hT : K.heap (L.curW s) = some .tcb := P.cT
  have el := hlk K s b v hJ hb hba
  have ecur := hJ.curW_wr hb hba v
  have emsg := msgInfo_wr hJ hb hba v hT P.tA
  have hct : ∀ t, sched.cur_thread st (L.wr s b v) = ok t → t = L.curW s := by
    intro t ht
    rw [cur_thread_ok, ecur] at ht
    exact (ok_inj_ff ht).symm
  refine ⟨⟨hJ.userWr hb v, ⟨ioQ_wr hIw K m s b v hJ hio hb hba, invPlanD_wrF K m s b v hJ hq0 hb hba, ?_, ?_⟩,
    invLk_wr hJ P hlk0 hb hba v⟩, el, hJ.ioRWDS_wrSt hb hba v el⟩
  · intro t info ht hi
    obtain rfl := hct t ht
    rw [emsg] at hi
    exact harm _ info (cur_thread_ok s) hi
  · intro i x hi hx
    rw [el]
    exact hlks i x hi hx

end huf

/-! ## `Once` at an agreeing state (slhuf gen 10's `once_agree`) -/

section agree
open Classical
variable {S A : Type} {st : machine.Store S} [L : LawfulStore st] {ar : machine.Arch A} {Rd User : U64 → Prop}

/-- **`Once` at an agreeing state** (copy of slhuf's `once_agree`, par/slhuf3 30ee9eec `P2/SlOnceL.lean`): if `p`
runs from `s` on `guard st R0 W0` (aligned sets) and `s'` agrees with `s` on `R0`, kernel base, core and masks,
then `Once` of `p` from `s` gives `Once` from `s'`. -/
theorem once_agreeJ (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s) {R0 W0 : U64 → Prop}
    (hRal : ∀ w, R0 w → Aligned w) (hWal : ∀ w, W0 w → Aligned w) {X : Type} (p : SProg X) (hz : NoZero p) :
    ∀ (s s' : S) (a : A) (r : X × S × A) (Wd T : Set U64), L.ksb s' = L.ksb s → L.cpu s' = L.cpu s →
      st.frame_masks s' = st.frame_masks s → (∀ w, R0 w → L.mem s' w = L.mem s w) →
      interp (guard st R0 W0) ar p s a = ok r →
      Once st ar Rd User Wd T p s a → Once st ar Rd User Wd T p s' a := by
  induction p with
  | ret x => intros; simp only [Once]
  | err e => intros; simp only [Once]
  | rd q k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R0 q
    · rw [guard_read hq] at hv
      simp only [Once] at ho ⊢
      refine ⟨ho.1, fun v' hv' => ?_⟩
      have ev : v' = v := by
        rw [L.read_eq] at hv hv'
        rw [← ok_inj_ff hv', ← ok_inj_ff hv, e4 q hq]
      subst ev
      exact ih v' (hz v') s s' a r _ _ e1 e2 e3 e4 hk (ho.2 v' hv)
    · rw [guard_read_out hq] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    by_cases hq : R0 q ∧ R0 (core.num.U64.wrapping_add q 8#u64)
    · rw [guard_read_pair hq.1 hq.2] at hv
      simp only [Once] at ho ⊢
      refine ⟨ho.1, ho.2.1, fun v' hv' => ?_⟩
      have ev : v' = v := by
        rw [L.read_pair_eq] at hv hv'
        rw [← ok_inj_ff hv', ← ok_inj_ff hv, e4 q hq.1, e4 _ hq.2]
      subst ev
      exact ih v' (hz v') s s' a r _ _ e1 e2 e3 e4 hk (ho.2.2 v' hv)
    · have : (guard st R0 W0).read_pair s q = fail .panic := by
        show (if R0 q ∧ R0 (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨s2, hv, hk⟩ := bok.mp h
    by_cases hq : W0 q
    · rw [guard_write hq, L.write_eq] at hv
      obtain rfl := Result.ok_injective hv
      simp only [Once] at ho ⊢
      intro s2' hs2'
      rw [L.write_eq] at hs2'
      obtain rfl := Result.ok_injective hs2'
      exact ih hz (L.wr s q v) (L.wr s' q v) a r _ _ (by rw [L.ksb_wr, L.ksb_wr, e1])
        (by rw [L.cpu_wr, L.cpu_wr, e2]) (by rw [hm, hm, e3])
        (fun w hw => by
          rw [L.mem_wr _ _ _ _ (hWal q hq) (hRal w hw), L.mem_wr _ _ _ _ (hWal q hq) (hRal w hw), e4 w hw]) hk
        (ho _ (L.write_eq _ _ _))
    · rw [guard_write_out hq] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.ks_base s = ok v := hv
    simp only [Once] at ho ⊢
    intro v' hv'
    have ev : v' = v := by
      rw [L.ks_base_eq] at hv2 hv'
      rw [← ok_inj_ff hv', ← ok_inj_ff hv2, e1]
    subst ev
    exact ih v' (hz v') s s' a r _ _ e1 e2 e3 e4 hk (ho v' hv2)
  | cpu k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.cur_cpu s = ok v := hv
    simp only [Once] at ho ⊢
    intro v' hv'
    have ev : v' = v := by
      rw [L.cur_cpu_eq] at hv2 hv'
      rw [← ok_inj_ff hv', ← ok_inj_ff hv2, e2]
    subst ev
    exact ih v' (hz v') s s' a r _ _ e1 e2 e3 e4 hk (ho v' hv2)
  | masks k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨v, hv, hk⟩ := bok.mp h
    have hv2 : st.frame_masks s = ok v := hv
    simp only [Once] at ho ⊢
    intro v' hv'
    have ev : v' = v := by
      rw [e3] at hv'
      exact ok_inj_ff (hv'.symm.trans hv2)
    subst ev
    exact ih v' (hz v') s s' a r _ _ e1 e2 e3 e4 hk (ho v' hv2)
  | arch op k ih =>
    intro s s' a r Wd T e1 e2 e3 e4 h ho
    simp only [interp] at h
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h
    simp only [Once] at ho ⊢
    intro v' a'' hv'
    rw [hv] at hv'
    obtain ⟨e5, e6⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e5
    subst e6
    exact ih _ (hz _) s s' _ r _ _ e1 e2 e3 e4 hk (ho _ _ hv)

end agree

/-! ## `InvURoAccW`: the `length ≥ 2` half -/

section ro
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- [W] **`ReadOnce` of an accepted truncated Delete** (`length < 2`, i.e. `¬ InvLen`), of the tree `q`, for
`InvCMRS`: the only user word such a run reads is word 7 of the caller's IPC buffer (`reply_error`'s
`DEBUG_MESSAGE_START + 1` read, then its write). Proving it needs the `once_gstep` walk of `R.invBodyG` from the
entry (as slhuf's `invCM_entOnce`) and of the truncated decode / reply (`decCNG` at `length < 2`, `invPostG`). -/
def InvURoTrW {A : Type} (ar : machine.Arch A) (number : I64) (p : localinv.Plan) (K : KLayout)
    (Locks : S → U64 → Prop) (m0 : U64 → U64) (q : SProg Bool) (P : S → Prop) : Prop :=
  ∀ s s' a r, P s → ¬ InvLen st s → (∃ s1 a1, syscall.handle_invocation_local st ar s a number p = ok (true, s1, a1)) →
    Alt st (InvCMRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
    interp st ar q s' a = ok r → Once st ar (InvCMRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ q s' a

/-- (invj gen 1) **`InvURoAccW` from its truncated half** (module docstring): for `P` states with `InvLen` (where
`PL` holds) the accepted run reads only `IoRS s` words (`hacc : InvAccW` at `PL`). Premise [W] `htr`. -/
theorem invURoAccW_of {A : Type} {ar : machine.Arch A} (hm : E2E.MasksWr st) {number : I64}
    {p : localinv.Plan} {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {q : SProg Bool}
    {P PL : S → Prop} (hPL : ∀ s, P s → InvLen st s → PL s)
    (hp : IsProgOn (fun m s a => syscall.handle_invocation_local m ar s a number p) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) q) (hz : NoZero q)
    (hacc : InvAccW st ar number p K Locks PL) (htr : InvURoTrW st ar number p K Locks m0 q P) :
    InvURoAccW st ar number p K Locks m0 q P := by
  intro s s' a r hE hac Al hr
  by_cases hL : InvLen st s
  · obtain ⟨s1, a1, h0⟩ := hac
    have hg := hacc s a s1 a1 (hPL s hE hL) h0
    rw [inv_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
    have o1 : Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ q s a :=
      once_of_guardG (fun w hw => hw.2.1) q hz ∅ ∅ s a _ hg
    have o2 := once_agreeJ hm (fun w hw => hw.1) (fun w hw => hw.1) q hz s s' a _ ∅ ∅ Al.ksb Al.cpu Al.masks
      (fun w hw => Al.read w (ioRS_cm hw)) hg o1
    exact onceU_monoR (fun _ h => ioRS_cm h) q ∅ ∅ ∅ s' a o2 (fun _ h => h)
  · exact htr s s' a r hE hL hac Al hr

end ro

/-! ## The paths -/

section paths
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}
variable {A : Type}

/-- (invj gen 1) **The CNodeDelete-no-PTE local path at `Q := InvQL`, premises closed**: `inv_pathsKF2` with
`hvs := invVsJ_of`, `hcdt := invCdtJ_of`, `hz := hz_of`, `huf := hufQL_of2 hIw hlk`, `hpz := inv_hpz …`. Premises:
`hA`, [P] `hm`, [J] `hIw` (`IoPre` survives a user write at a bundle state; iolay line), [P] `hlk` (the locks are
kept by a user write). -/
noncomputable def inv_pathsKF3 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s) :
    E2E.Paths Unit :=
  inv_pathsKF2 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p hm
    (fun _ _ => invVsJ_of (fun _ h => h.1))
    (fun _ _ => invCdtJ_of (fun _ h => h.1))
    hz_of
    (hufQL_of2 hIw hlk)
    (fun K m => inv_hpz hA (fun _ h => h.2.1.1.1.1)
      (invSlotCNK_of (Q := InvQL st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq.1) K m)
      (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2.1))

/-- (invj gen 1) **`StartAt` of `inv_pathsKF3` at a chain state** (as `inv_pathsKF2_startAt`). -/
theorem inv_pathsKF3_startAt (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : E2E.UserOK K)
    {A3 : Type} {Rc : S → A3 → Fl4Spec.State Unit → Prop}
    (h7 : ∀ (σ : S) (a : A3) (τ : Fl4Spec.State Unit), Rc σ a τ → SlJAt (L := L) K σ)
    {σ : S} {a3 : A3} {τ : Fl4Spec.State Unit} (hR : Rc σ a3 τ) (a : A) (hq : InvQL st Cs Ω Sg Ac Locks p K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    E2E.StartAt (inv_pathsKF3 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) ar hA number p hm hIw hlk () K m hK hU)
      c hs μ ((inv_pathsKF3 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) ar hA number p hm hIw hlk () K m hK hU).body
        σ a) :=
  ⟨σ, a, ⟨h7 σ a3 τ hR, hq⟩, hc, hl, hμ, rfl⟩

/-- (invj gen 1) **The uncut CNodeDelete local path at `Q := InvQF`, premises closed but two**: `inv_pathsKFU` with
`hvs`, `hcdt`, `hz` as `inv_pathsKF3`, `huf := hufQF_of2 hIw hlk`, and `hpz` for the tree `R.invBodyG number p`
(`inv_isProgOn` with `hSC := invSlotCNK_of`, `inv_noZero`, `invRoW_of` with `hSeen := invSeen_of`,
`invURoAccW_of` with `hacc` from stpost's `invAccW_of2` + `invBlkW2_of` at `InvQL`), on `inv_pathsKFU8` with
`hbuf := invBufJ8_of`. Premises: `hA`, [P] `hm`, [J] `hIw`, [P] `hlk`, [W] `htr : InvURoTrW` (ReadOnce of accepted
truncated runs). -/
noncomputable def inv_pathsKFU2 (ar : machine.Arch A) (hA : P0.ArchTotal ar) (number : I64) (p : localinv.Plan)
    (hm : E2E.MasksWr st)
    (hIw : ∀ K s b v, SlJAt (L := L) K s →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s →
      b ∈ K.user → Aligned b →
      IoPre st K K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac (L.wr s b v))
    (hlk : ∀ K s b v, SlJAt (L := L) K s → b ∈ K.user → Aligned b → Locks (L.wr s b v) = Locks s)
    (htr : ∀ K m, InvURoTrW st ar number p K Locks m (R.invBodyG number p)
      (fun s => SlJAt (L := L) K s ∧ InvQF st Cs Ω Sg Ac Locks p K m s)) :
    E2E.Paths Unit :=
  inv_pathsKFU8 (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (Locks := Locks) ar hA number p hm
    (fun _ _ => invVsJ_of (fun _ h => h.1))
    (fun _ _ => invCdtJ_of (fun _ h => h.1))
    hz_of (fun _ _ _ hJ _ => invBufJ8_of hJ) (hufQF_of2 hIw hlk)
    (fun K m =>
      have hp := inv_isProgOn (Locks := Locks) (m0 := m) hA (P := fun s => SlJAt (L := L) K s ∧
        InvQF st Cs Ω Sg Ac Locks p K m s) (fun _ h => h.2.1.1.1)
        (invSlotCNK_of (Q := InvQF st Cs Ω Sg Ac Locks p) (fun _ _ _ _ hq => hq) K m)
        (inv_isProg S number p)
      ⟨R.invBodyG number p, hp, inv_noZero number p,
        invRoW_of hA (fun _ h => h.2.1.1.1)
          (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2) hp (inv_noZero number p),
        invURoAccW_of hm (PL := fun s => SlJAt (L := L) K s ∧ InvQL st Cs Ω Sg Ac Locks p K m s)
          (fun _ h hL => ⟨h.1, h.2, hL⟩) hp (inv_noZero number p)
          (invAccW_of2 hA (fun _ h => h.2.1.1.1.1)
            (fun s h => invSeen_of (fun K _ s hJ _ => hz_of K s hJ) K m s h.1 h.2.1)
            (fun s h => invPs_of K m s h.1 h.2.1)
            (invBlkW2_of hA (invVsJ_of (fun _ h => h.1)) (invCdtJ_of (fun _ h => h.1)) (hz_of K)))
          (htr K m)⟩)

end paths

end Fl4Proofs.P2.PathObl
