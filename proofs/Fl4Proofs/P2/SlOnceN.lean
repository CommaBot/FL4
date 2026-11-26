/-
# P2 (line slhuf, gen 7): the syscall entry's runs on its read set without user words

`ReadOnce` asks `Once` for the read set `SlRS s`, which holds the user words; user words are racy whatever the
read set. A run guarded on `SlRS s ∧ NU K` (`NU K`: aligned, not a user word) makes no racy read
(`once_of_guardG`, then `once_monoR`). Guarded runs on two sets combine (`interp_guard_meet`), so it is enough
to run the arm's existing guard lemma once more at `R := NU K`, `W := ⊤`.

* `SlOF`, `slOF_of`: every entry fact of the syscall path at a bundle state with the canonical `Q`
  (`SlPre`, `SlEnt`, `SlHere`, `SlAccIn`, `SlThrIn`, `SlDecIn`), as `sl_localPathK` builds them.
* `interp_guard_meet`: a run on `guard st R1 W1` and on `guard st R2 W2` is a run on the meet.
* `scAccNU`, `rdHead_hereN`, `SlJAt.tabNU` (P3's VSpace placement: no ASID-table or pool word is a user word,
  vlift's `SlJAtZ.vsU`), `rdTabN`, `nuReg`, **`fltAcc_nuT`**: the trap arm's access facts at `NU K`.
* **`sl_trap_acc_guardN`**: an accepted trap arm runs on `guard st (NU K) ⊤`.
* **`sl_once_accN`**: an entry whose run is guarded on `SlRS s ∧ NU K` gives `Once` at every alternative.

No premises beyond the entry facts.
-/
import Fl4Proofs.P2.SlOnceL
import Fl4Proofs.P2.SlJLk2
import Fl4Proofs.P2.ProgGenWire
import Fl4Proofs.P2.FootTimerIrqJC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once)

/-! ## Guarded runs meet -/

section meet
open Classical
variable {S A : Type} {st : machine.Store S} {ar : machine.Arch A}

theorem interp_guard_meet {R1 W1 R2 W2 : U64 → Prop} {X : Type} (p : SProg X) (hz : NoZero p) :
    ∀ (s : S) (a : A) (r : X × S × A), interp (guard st R1 W1) ar p s a = ok r →
      interp (guard st R2 W2) ar p s a = ok r →
      interp (guard st (fun q => R1 q ∧ R2 q) (fun q => W1 q ∧ W2 q)) ar p s a = ok r := by
  induction p with
  | ret x => intro s a r h1 _; exact h1
  | err e => intro s a r h1; exact absurd h1 fail_not_ok
  | rd q k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h1
    obtain ⟨v', hv', hk'⟩ := bok.mp h2
    by_cases hq1 : R1 q
    · by_cases hq2 : R2 q
      · rw [guard_read hq1] at hv
        rw [guard_read hq2, hv] at hv'
        cases ok_inj_ff hv'
        exact bok.mpr ⟨v, by rw [guard_read (R := fun q => R1 q ∧ R2 q) ⟨hq1, hq2⟩]; exact hv,
          ih v (hz v) s a r hk hk'⟩
      · rw [guard_read_out hq2] at hv'; exact absurd hv' fail_not_ok
    · rw [guard_read_out hq1] at hv; exact absurd hv fail_not_ok
  | rdp q k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h1
    obtain ⟨v', hv', hk'⟩ := bok.mp h2
    by_cases hq1 : R1 q ∧ R1 (core.num.U64.wrapping_add q 8#u64)
    · by_cases hq2 : R2 q ∧ R2 (core.num.U64.wrapping_add q 8#u64)
      · rw [guard_read_pair hq1.1 hq1.2] at hv
        rw [guard_read_pair hq2.1 hq2.2, hv] at hv'
        cases ok_inj_ff hv'
        exact bok.mpr ⟨v, by
          rw [guard_read_pair (R := fun q => R1 q ∧ R2 q) ⟨hq1.1, hq2.1⟩ ⟨hq1.2, hq2.2⟩]; exact hv,
          ih v (hz v) s a r hk hk'⟩
      · have : (guard st R2 W2).read_pair s q = fail .panic := by
          show (if R2 q ∧ R2 (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
          rw [if_neg hq2]
        rw [this] at hv'; exact absurd hv' fail_not_ok
    · have : (guard st R1 W1).read_pair s q = fail .panic := by
        show (if R1 q ∧ R1 (core.num.U64.wrapping_add q 8#u64) then st.read_pair s q else fail .panic) = _
        rw [if_neg hq1]
      rw [this] at hv; exact absurd hv fail_not_ok
  | wr q v k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨s1, hv, hk⟩ := bok.mp h1
    obtain ⟨s2, hv', hk'⟩ := bok.mp h2
    by_cases hq1 : W1 q
    · by_cases hq2 : W2 q
      · rw [guard_write hq1] at hv
        rw [guard_write hq2, hv] at hv'
        cases ok_inj_ff hv'
        exact bok.mpr ⟨s1, by rw [guard_write (W := fun q => W1 q ∧ W2 q) ⟨hq1, hq2⟩]; exact hv,
          ih hz s1 a r hk hk'⟩
      · rw [guard_write_out hq2] at hv'; exact absurd hv' fail_not_ok
    · rw [guard_write_out hq1] at hv; exact absurd hv fail_not_ok
  | zero q n k ih => exact absurd hz id
  | clr q n k ih => exact absurd hz id
  | ksb k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h1
    obtain ⟨v', hv', hk'⟩ := bok.mp h2
    have e : v' = v := ok_inj_ff (hv'.symm.trans hv)
    subst e
    exact bok.mpr ⟨v', hv, ih v' (hz v') s a r hk hk'⟩
  | cpu k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h1
    obtain ⟨v', hv', hk'⟩ := bok.mp h2
    have e : v' = v := ok_inj_ff (hv'.symm.trans hv)
    subst e
    exact bok.mpr ⟨v', hv, ih v' (hz v') s a r hk hk'⟩
  | masks k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨v, hv, hk⟩ := bok.mp h1
    obtain ⟨v', hv', hk'⟩ := bok.mp h2
    have e : v' = v := ok_inj_ff (hv'.symm.trans hv)
    subst e
    exact bok.mpr ⟨v', hv, ih v' (hz v') s a r hk hk'⟩
  | arch op k ih =>
    intro s a r h1 h2
    simp only [interp] at h1 h2 ⊢
    obtain ⟨⟨v, a'⟩, hv, hk⟩ := bok.mp h1
    obtain ⟨⟨v', a''⟩, hv', hk'⟩ := bok.mp h2
    rw [hv] at hv'
    obtain ⟨e1, e2⟩ := Prod.mk.inj (ok_inj_ff hv')
    subst e1
    subst e2
    exact bok.mpr ⟨_, hv, ih _ (hz _) s _ r hk hk'⟩

end meet

section N
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-! ## The entry facts -/

/-- **Every entry fact of the syscall path at a bundle state with the canonical `Q`.** -/
structure SlOF (K : KLayout) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64) (found : U64 × U64)
    (Cs Ω Sg Ac : Set U64) (s : S) : Prop where
  B : SlJAt (L := L) K s
  E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
    K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s
  C : SlSyncC st n found s
  N : SlEnt (st := st) K Locks found s
  Hh : SlHere (st := st) K K.heap.scBits K.heap.scs found s
  Ai : SlAccIn (st := st) ar K Locks K.heap.scBits K.heap.scs found s
  P : SlPre (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
    K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s
  I : SlThrIn (st := st) K Locks found.1 s
  D : SlDecIn (st := st) ar K Locks found s

theorem slOF_of (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (a0 : A) {s : S} (hJ : SlJAt (L := L) K s)
    (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m0 s) : SlOF ar K Locks m0 n found Cs Ω Sg Ac s := by
  obtain ⟨E, El, C, Ar⟩ := hq
  have hK := hJ.regionOK
  have hX := hJ.regionOKX
  have N := slEnt_of ar hSt hA hX (slSets_conv K) a0 E (hJ.entJ E.hN (hJ.entR C El))
  have Hj := hJ.hereJ (hJ.hereR C)
  have Hh := slHere_of ar hSt hA hX (slSets_conv K) a0 E N Hj
  have Aj := slAccJ_of ar hA hK hX (fun _ h => h) E Hj (hJ.accK Ar)
  have Ai := slAccIn_of ar hA hK hX (slSets_conv K) E N Hh Aj
  have P := slPre_of ar hA hK hX E N Hh Ai
  exact ⟨hJ, E, C, N, Hh, Ai, P, slThrIn_of hK hX P.preG E.hSt.1 N, slDecIn_of ar hA hK hX E N Hh⟩

/-! ## Words that are no user words -/

theorem scAccNU (hX : RegionOKX K) {sc : U64} {z : Nat} (hz : K.heap sc = some (.sc z)) :
    ScAcc (NU K) (fun _ => True) sc z :=
  ⟨fun b ha hb => nu_sc hX hz ha hb, fun _ _ _ => trivial, trivial⟩

theorem nuReg (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) {r : U64} (hr : r.val < 384) :
    NU K (regA t r) := by
  obtain ⟨o, ho, e⟩ := regA_eq' (t := t) hr
  rw [e]
  exact nu_tcb hX ht (by omega) (by omega) (by omega)

theorem nuRegs (hX : RegionOKX K) {t : U64} (ht : K.heap t = some .tcb) : Regs (NU K) t :=
  fun _ hr => nuReg hX ht hr

/-- The head refill of an SC homed here is `NU` at the prefix state. -/
theorem rdHead_hereN (hA : P0.ArchTotal ar) (hX : RegionOKX K) {s : S}
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (Hh : SlHere (st := st) K K.heap.scBits K.heap.scs found s) {a X a1}
    (LP : LocalPre (st := st) ar s a (X, a1))
    {sc : U64} (hs : ScHere (st := st) K K.heap.scBits K.heap.scs s sc) : RdHead (L := L) (NU K) X sc := by
  obtain ⟨hz, hin, hmx, -⟩ := hs
  obtain ⟨-, am, -, rm⟩ := sc_off hX hz (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
    (by simp [layout.sc.REFILL_MAX])
  have em : L.mem X (maxA sc) = L.mem s (maxA sc) :=
    lp_mem ar hA E.hT E.hN E.hcT LP am (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by unfold maxA; rw [rm]; intro c h; cases h) (by unfold maxA; rw [rm]; intro h; cases h))
  have hW : RefillsWF st X sc (K.heap.scBits sc) :=
    ((E.hI a X a1 LP).2.2.2.2.all sc hin).1 (by show L.mem X (maxA sc) ≠ 0#u64; rw [em]; exact hmx)
  exact ScAcc.head (scAccNU hX hz) hW

/-- **No ASID-table or ASID-pool word is a user word** at a bundle state (vlift's `SlJAtZ.vsU`). -/
theorem SlJAt.tabNU {s : S} (hJ : SlJAt (L := L) K s) {hi : U64} (hhi : hi.val < 2048) :
    NU K (atAF (L.ksb s) hi) ∧ ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
      NU K (peAF (L.mem s (atAF (L.ksb s) hi)) lo) := by
  refine ⟨hJ.nuAsid rfl hhi, fun lo hlo h0 => ?_⟩
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  have hk := B.ksb
  refine ⟨?_, ?_⟩
  · have h0' : L.mem s (atAF K.ksb hi) ≠ 0#u64 := by rw [← hk]; exact h0
    have := B.pool hi hhi h0' lo hlo
    rw [hk]
    exact this.1
  · have e : atAF (L.ksb s) hi = Fl4Proofs.P3.Vs.atA (L.ksb s) hi := rfl
    rw [e] at h0 ⊢
    have hP := B.j.xtop.fin.2.1.tmem hi hhi h0
    exact B.vsU (Or.inr ⟨_, hP, lo, hlo, rfl⟩)

/-- The ASID table and pools read by `set_vm_root`, at the prefix state, are `NU`. -/
theorem rdTabN (hA : P0.ArchTotal ar) {s : S} (hJ : SlJAt (L := L) K s)
    (E : SlPreB (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (Hh : SlHere (st := st) K K.heap.scBits K.heap.scs found s) {a X a1}
    (LP : LocalPre (st := st) ar s a (X, a1)) : RdTab (L := L) (NU K) X := by
  have hX := hJ.regionOKX
  obtain ⟨kX, -, -, -, -, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  intro hi hhi
  rw [kX]
  have e0 : L.mem X (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := by
    rw [Hh.ksb]
    obtain ⟨r0, a0⟩ := hX.asidT hi hhi
    exact lp_mem ar hA E.hT E.hN E.hcT LP a0 (not_slDS_reg hX E.hN E.hT E.hcT E.hSt.1 Hh.ksb Hh.cpu
      (by rw [r0]; intro c h; cases h) (by rw [r0]; intro h; cases h))
  obtain ⟨n1, n2⟩ := hJ.tabNU hhi
  exact ⟨n1, fun lo hlo hne => by rw [e0] at hne ⊢; exact n2 lo hlo hne⟩

set_option maxHeartbeats 4000000 in
/-- **The trap arm's access facts at `NU K`** (`fltAcc_wn` with every read word shown not a user word;
writes unconstrained). -/
theorem fltAcc_nuT (hA : P0.ArchTotal ar) {s : S} (F : SlOF ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    FltAcc (L := L) K.heap.scBits (NU K) (fun _ => True) X (L.curW s) ptr dest r := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have hK := B.regionOK
  have hX := B.regionOKX
  have C := slCom_nu ar hA B E LP
  obtain ⟨kX, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  obtain ⟨hep, -⟩ := trap_ep ar hA E F.N F.I hS LP hc
  obtain ⟨hdt, -, -, -⟩ := E.hSd hS a X a1 LP hc
  have nT : ∀ {t o : U64}, K.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  obtain ⟨hz, -, -, -⟩ := F.Ai.dsc hS a X a1 LP hc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hdt (by simp) (by simp) (by simp) (by simp))
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have tw : ∀ y, K.heap y = some .tcb → ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      NU K (core.num.U64.wrapping_add y o) := fun y hy o h1 h2 h3 => nu_tcb hX hy h1 h2 h3
  exact
  { nd := fun o h1 h2 => ⟨C.nd o h1 h2, trivial⟩
    dt := C.dt
    cd := C.cd
    kr := by
      show NU K (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
      rw [kX]
      exact B.nuKs E.hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := rdTabN ar hA B E Hh LP
    fh := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact nu_tslot hK hX hc0 (by simp [layout.tcb.SLOT_FAULT_HANDLER])
    eph := ⟨nu_ep hX hep (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD]), trivial⟩
    ept := ⟨nu_ep hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE]), trivial⟩
    tf := fun o ho => ⟨tw _ hc0 o (by rcases ho with h | h | h | h <;> omega)
      (by rcases ho with h | h | h | h <;> omega) (by rcases ho with h | h | h | h <;> omega), trivial⟩
    treg := nuRegs hX hc0
    trp := trivial
    drp := tw _ hdt 3360#u64 (by simp) (by simp) (by simp)
    daf := tw _ hdt 3520#u64 (by simp) (by simp) (by simp)
    ddo := tw _ hdt 3432#u64 (by simp) (by simp) (by simp)
    dsc0 := tw _ hdt 3464#u64 (by simp) (by simp) (by simp)
    diq := tw _ hdt 3592#u64 (by simp) (by simp) (by simp)
    dpr := tw _ hdt 3448#u64 (by simp) (by simp) (by simp)
    dyt := tw _ hdt 3472#u64 (by simp) (by simp) (by simp)
    dst := by rw [stA_eq]; exact tw _ hdt 3328#u64 (by simp) (by simp) (by simp)
    dfi := nuReg hX hdt (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    den := tw _ hdt 3496#u64 (by simp) (by simp) (by simp)
    dib := tw _ hdt 3512#u64 (by simp) (by simp) (by simp)
    dvt := by
      rw [vtA_slot]
      exact nu_tslot hK hX hdt (by simp [layout.tcb.SLOT_VTABLE])
    dbs := fun sl hsl => by
      rw [tcb_slot_val] at hsl
      obtain rfl := ok_inj_ff hsl
      exact nu_tslot hK hX hdt (by simp [layout.tcb.SLOT_BUFFER])
    dw := ⟨trivial, trivial, trivial, trivial⟩
    dreg := fun _ _ => trivial
    nxt := fun _ => trivial
    buf := fun _ _ _ _ _ => trivial
    rt := trivial
    spo := by
      rw [eSc]
      obtain ⟨-, am, hin, -⟩ := sc_off hX hz (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
        (by simp [layout.sc.SPORADIC])
      exact nu_sc hX hz am hin
    dsc := by rw [eSc]; exact scAccNU hX hz
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, -⟩ := Hh.cs
      exact scAccNU hX hz'
    tm := C.tm
    rh := fun h => by
      refine ⟨(C.rh h).1, ?_, (C.rh h).2⟩
      rw [eRh] at h ⊢
      obtain ⟨ht, hs⟩ := Hh.rh h
      have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      rw [eS]
      obtain ⟨hz', -, -, -⟩ := hs
      exact fun b ha hb => nu_sc hX hz' ha hb }

/-- **An accepted trap arm runs on `guard st (NU K) ⊤`** (`guard_acc` at `R := NU K`, `W := ⊤`). -/
theorem sl_trap_acc_guardN (hA : P0.ArchTotal ar) {s : S} (F : SlOF ar K Locks m0 n found Cs Ω Sg Ac s)
    (hS : SlTrap st s) {a : A} {s1 : S} {a1 : A}
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) :
    syscall.handle_syscall_local (guard st (NU K) (fun _ => True)) ar s a n found = ok (true, s1, a1) := by
  have E := F.E
  have hX := F.B.regionOKX
  have hpre : PreAcc (L := L) (NU K) (fun _ => True) s :=
    ⟨fun o h1 h2 => ⟨F.B.nuNode E.hN h1 h2, trivial⟩,
      nu_tcb hX E.hSt.1 (o := 3456#u64) (by simp) (by simp) (by simp),
      nuReg hX E.hSt.1 (r := layout.reg.NEXT_IP) (by simp [layout.reg.NEXT_IP]), trivial⟩
  have hhd : ∀ X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (NU K) X csc := by
    intro X a1 csc LP hcs
    obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have e : csc = L.cscW s := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
      rw [← ok_inj_ff hcs]; exact ecs
    subst e
    exact rdHead_hereN ar hA hX E F.Hh LP F.Hh.cs
  exact syscall.handle_syscall_local.guard_acc (gS := guard st (NU K) (fun _ => True))
    (R := NU K) (W := fun _ => True) ar hA E.hT E.hN E.hcT hpre hhd (E.hI a) (E.hAs a)
    (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
    (fun _ X a1 LP {_p _b _d _r} hc => fltAcc_nuT ar hA F hS LP hc)
    (fun _ _ _ _ {_p _b _d _r} _ => ⟨SWr.of_W (W := fun _ => True) trivial,
      fun _ _ => SWr.of_W (W := fun _ => True) trivial⟩)
    (fun h' => absurd hS h') (fun h' => absurd hS h') (fun h' => absurd hS h') (fun h' => absurd hS h')
    (fun h' => absurd hS h') h

/-- **`Once` at every alternative of an entry whose run is guarded on `SlRS s ∧ NU K`** (`interp_agree`,
`once_of_guardG`, `once_monoR`). -/
theorem sl_once_accN (hm : E2E.MasksWr st) {s s' : S} {a : A} {W0 : U64 → Prop}
    (hW0 : ∀ w, W0 w → Aligned w)
    (Al : Alt st (SlRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s') {r : Bool × S × A}
    (hg : interp (guard st (fun q => SlRS (st := st) K Locks s q ∧ NU K q) W0) ar
      (R.syscall.handle_syscall_local n found) s a = ok r) :
    Once st ar (SlRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ (R.syscall.handle_syscall_local n found) s' a := by
  obtain ⟨b, s1, a1⟩ := r
  obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1.1) hW0 _ (sl_noZero n found) s s' a b s1 a1
    Al.ksb Al.cpu Al.masks (fun w hw => Al.read w hw.1) hg
  exact once_monoR (fun b hb => hb.1) _ ∅ ∅ ∅ s' a
    (once_of_guardG (fun q hq => hq.2.2) _ (sl_noZero n found) ∅ ∅ s' a _ hg') subset_rfl

end N

end Fl4Proofs.P2.PathObl
