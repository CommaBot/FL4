/-
P2 (sib): **`VcpuUsr` from the VCPU objects' placement at the entry**.

`AllCores.tail` / the exit wrappers (`P2/EntryTail.lean`, `P2/EntryExit.lean`)
assume `VcpuUsr` (`hVW` [P]): a TCB's bound VCPU's `PENDING` word is a
user-class word (`UsrW`). Here it is derived from P3's placement facts at the
entry state `s0` and P1's invariants at the state `vcpu::check` reads:

* `usrW_vcpu`: a word of a VCPU object (`.other 15`) at offset `PENDING`
  (20520) is a `UsrW` word over P1's heap sets (`T = H.tcbs`, `Ω = H.omega`,
  `Sg = H.frame`): in `Ω` (so outside the TCBs and nodes, `omega`, and apart
  from the endpoints and notifications, `EpsWit`), off the frame words and
  the SCs (`HeapOK.disj`), and off the kernel-global block (`VcpuEnt.ksIn`:
  `H`'s `other` objects lie off the block or inside it, and a 2^15-byte VCPU
  does not fit inside the 13568-byte block).
* `VcpuUsr.of_ent`: P1's `VcpuPl.bound` (the bound VCPU is a VCPU object)
  at any state reached from `s0` within `Cur0W` (`Fr0`) with `BXI` there.
* `cur0w_*`: the entry's writes lie in `Cur0W s0`: the body's `FootB`
  (`allCoresB` now exports it), `timer::fire`'s `FootDU` (its user words are
  `UsrW`), the rest of `schedule` (`SFootB`, `P1/SchedFootB.lean`), and
  `activate_thread`'s `TW` (outside words are in `Ω`, user words or endpoint
  words).
* **`AllCores.tailV`**, **`AllCores.exitV`**,
  **`timer_irq_local.allCoresExitV`**, **`set_timer_local.allCoresExitV`**:
  the exit wrappers with `hVW` replaced by `VcpuEnt` at the entry.
* **`Fl4Proofs.P1.vcpu.check.entryV`**: P1's `vcpu.check.entry` with its
  `hpw` [P] replaced by `VcpuEnt` at an earlier state and `Fr0` from it.

Named premise: `VcpuEnt` **[P]** at the entry state, P3's facts over P1's
heap: `HeapOK H` (`JPlaced.heap`), P1's sets convention (`T = H.tcbs`,
`Ω = H.omega`, `Sg = H.frame`, the SCs `H`'s with their sizes, as
`UtRetypeP3.sets` / `SlSets`), `H`'s `other` objects off or inside the
kernel-global block (`JPlaced.ksIn`), and `VcpuPl` (`VcpuPlace.pl`).
-/
import Fl4Proofs.P2.EntryExit
import Fl4Proofs.P1.QueueVcpu
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}
variable {A : Type _} {ar : machine.Arch A}

/-- **[P] The VCPU objects' placement at the entry state `s0`** (module
docstring). -/
structure VcpuEnt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (s0 : S) : Prop where
  heap : HeapOK H
  sets : T = H.tcbs ∧ Ω = H.omega ∧ Sg = H.frame
  scs : ∀ c ∈ Scs, H c = some (.sc (Z c))
  ksIn : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s0).val ∨ (L.ksb s0).val + 13568 ≤ p.val ∨
    ((L.ksb s0).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s0).val + 13568)
  pl : VcpuPl st H Cs Rp Scs Nt Z s0

/-- A VCPU object's `PENDING` word is a user-class word (module docstring). -/
theorem usrW_vcpu {X : Set U64} {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} (hH : HeapOK H)
    (hScs : ∀ c ∈ Scs, H c = some (.sc (Z c)))
    (hKI : ∀ p z, H p = some (.other z) → p.val + 2 ^ z ≤ (L.ksb s).val ∨ (L.ksb s).val + 13568 ≤ p.val ∨
      ((L.ksb s).val ≤ p.val ∧ p.val + 2 ^ z ≤ (L.ksb s).val + 13568))
    (hq : SchedQueuesInvX st H.tcbs Cs H.omega H X s Q R) {v : U64} (hv : H v = some (.other 15)) :
    UsrW st H.tcbs Cs H H.frame Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING) := by
  have hal := hH.align v _ hv
  have hfit := hH.fits v _ hv
  have e15 : (HKind.other 15).bits = 15 := rfl
  have p15 : (2 : ℕ) ^ 15 = 32768 := by norm_num
  rw [e15, p15] at hal hfit
  obtain ⟨o, eo⟩ : ∃ o : U64, o = vcpu.PENDING := ⟨_, rfl⟩
  have hP : o.val = 20520 := by rw [eo]; simp [vcpu.PENDING]
  rw [← eo]
  have hb : (core.num.U64.wrapping_add v o).val = v.val + 20520 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  generalize core.num.U64.wrapping_add v o = b at hb ⊢
  have hbal : Aligned b := by unfold Aligned; rw [hb]; omega
  have hbΩ : b ∈ H.omega := ⟨hbal, v, .other 15, hv, Or.inr (Or.inr (Or.inl ⟨15, rfl⟩)),
    by unfold InObj; rw [e15, p15, hb]; omega⟩
  obtain ⟨E, EQ, -, -, w3, -, -, ty⟩ := hq.eps
  refine ⟨hq.omega _ hbΩ, fun e he => w3 e ((ty.2.2.1 e).2 he) _ hbΩ, ?_, ?_, ?_⟩
  · rintro ⟨-, p, k, hp, hk, hin⟩
    have hne : p ≠ v := by
      rintro rfl; rw [hv] at hp; cases hp
      rcases hk with h | ⟨z, h⟩ | ⟨h, -⟩ <;> cases h
    have := hH.disj v (.other 15) p k hv hp hne.symm
    rw [e15, p15] at this
    unfold InObj at hin
    omega
  · intro o' ho h8 e
    have hk := ks_val hq ho
    have e' := congrArg UScalar.val e
    rw [hk, hb] at e'
    rcases hKI v 15 hv with h | h | h
    all_goals (try rw [p15] at h)
    all_goals omega
  · intro c hc hin
    have hcH := hScs c hc
    have hne : c ≠ v := by rintro rfl; rw [hv] at hcH; cases hcH
    have := hH.disj v (.other 15) c _ hv hcH hne.symm
    rw [e15, p15] at this
    simp only [HKind.bits] at this
    unfold InSC at hin
    rw [hb] at hin
    omega

/-- **`VcpuUsr` at a state reached from the entry within `Cur0W`** (module
docstring). -/
theorem VcpuUsr.of_ent {s0 s : S} (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0)
    (F : Fr0 st T Cs Ω H Sg Scs Z s0 s) (hI : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    VcpuUsr st T Cs H Sg Scs Z s := by
  obtain ⟨eT, eΩ, eSg⟩ := V.sets
  subst eT eΩ eSg
  intro t ht hn
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, -⟩ := hI
  have hv := V.pl.bound Ac s t F ⟨⟨Q, R, hq⟩, hB, hX, hS.sg, hS⟩ ht hn
  have hk : L.ksb s = L.ksb s0 := F.1
  exact usrW_vcpu V.heap V.scs (fun p z hp => by rw [hk]; exact V.ksIn p z hp) hq hv

/-! ## The entry's writes in `Cur0W` -/

theorem cw_trans {s₁ s₂ s₃ : S} {C : U64 → Prop} (h₁ : WritesIn st s₁ s₂ C) (h₂ : WritesIn st s₂ s₃ C) :
    WritesIn st s₁ s₃ C :=
  (h₁.trans h₂).mono fun _ hb => hb.elim id id

theorem cur0w_omega {s0 : S} {b : U64} (hb : b ∈ Ω) : Cur0W st T Cs Ω H Sg Scs Z s0 b := by
  by_cases hs : b ∈ Sg
  · exact Or.inl (kw_sg hs)
  · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨hb, hs⟩)))

theorem cur0w_usr {s0 s : S} {b : U64} (hk : L.ksb s = L.ksb s0) (h : UsrW st T Cs H Sg Scs Z s b) :
    Cur0W st T Cs Ω H Sg Scs Z s0 b := by
  by_cases hΩ : b ∈ Ω
  · exact cur0w_omega hΩ
  · exact Or.inr (Or.inr (Or.inr ⟨h.out.ksb hk.symm, hΩ, h.eps⟩))

theorem cur0w_out {X : Set U64} {s0 s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hk : L.ksb s = L.ksb s0) {b : U64}
    (ho : OutsideObjs st T Cs s b) : Cur0W st T Cs Ω H Sg Scs Z s0 b := by
  by_cases hΩ : b ∈ Ω
  · exact cur0w_omega hΩ
  by_cases hap : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val
  · exact Or.inr (Or.inr (Or.inr ⟨ho.ksb hk.symm, hΩ, hap⟩))
  push_neg at hap
  obtain ⟨e, he, h1, h2⟩ := hap
  obtain ⟨E, EQ, w1, -, -, -, -, ty⟩ := hq.eps
  have hP := (w1 e ((ty.2.2.1 e).2 he)).1
  have ha : b.val % 8 = 0 := ho.1
  have hea := hP.align
  have hf := hP.fits
  refine Or.inl (kw_ep (show e ∈ EH H from he) ?_)
  have : b.val = e.val ∨ b.val = e.val + 8 := by omega
  rcases this with e1 | e1
  · left; apply UScalar.eq_of_val_eq; rw [epHeadA_val]; exact e1
  · right; apply UScalar.eq_of_val_eq; rw [epTSA_val hP]; exact e1

theorem cur0w_sb {s0 s : S} {b : U64} (hS : SgOK st Ω Sg s0) (hk : L.ksb s = L.ksb s0)
    (h : SchedWB st T Cs Sg Scs Z H s b) : Cur0W st T Cs Ω H Sg Scs Z s0 b := by
  rcases h with h | ⟨o, ho, h8, e⟩
  · exact Or.inl (KW.ksb hk (KWB.kw h))
  · subst e; rw [hk]; exact cur0w_omega (hS.ksΩ o ho h8)

theorem cur0w_tw {X : Set U64} {s0 s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hk : L.ksb s = L.ksb s0) {y b : U64} (hy : y ∈ T)
    (hc : L.cpu s ∈ Cs) (h : TW st T Cs Scs y s b) : Cur0W st T Cs Ω H Sg Scs Z s0 b := by
  rcases h with ((⟨ho, -⟩ | ⟨K, h1, h2, -, e⟩) | e) | e | e
  · exact cur0w_out hq hk ho
  · subst e
    exact Or.inl (KW.ksb hk (kw_field hy (by omega) (by omega) ⟨by omega, by omega⟩))
  · subst e
    exact Or.inl (KW.ksb hk (kw_field (K := 3472#u64) hy (by simp) (by simp) ⟨by simp, by simp⟩))
  · subst e
    rw [stA_eq]
    exact Or.inl (KW.ksb hk (kw_field (K := 3328#u64) hy (by simp) (by simp) ⟨by simp, by simp⟩))
  · subst e
    exact Or.inl (KW.ksb hk (kw_node hc (by rw [act_val]; omega) (by rw [act_val]; omega)))

/-! ## The tail and the exit wrappers -/

/-- **`AllCores.tail` with `VcpuUsr` asked only at `activate_thread`'s end**
(an `EntryInv` state reached by a `TW` step from `schedule`'s end). -/
theorem AllCores.tailV (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s4 s' : S} {a4 a' : A}
    (h4 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4) (hS0 : (0#u64) ∉ Scs)
    (hI4 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s4) (hBA4 : BufAt st T Cs H Sg Scs Z U s4)
    (hV : ∀ s5 : S, EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s5 →
      WritesIn st s4 s5 (TW st T Cs Scs (L.curW s4) s4) → VcpuUsr st T Cs H Sg Scs Z s5)
    (e : (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨⟨s5, a5⟩, e5, e'⟩ := bind_eq_ok e
  try simp only [uncurry_apply_pair] at e'
  obtain ⟨t, et, e'⟩ := bind_eq_ok e'
  rw [cur_thread_ok] at et
  have ht : L.curW s5 = t := ok_inj_ff et
  subst ht
  obtain ⟨Q4, R4, hq4⟩ := hI4.1
  have hcpu : L.cpu s4 ∈ Cs := hq4.cur
  have A1 := WP.spec_and (sched.activate_thread.entry hA s4 a4 hI4) (sched.activate_thread.tw hA s4 a4 hI4.blkOK)
  rw [e5, WP.spec_ok] at A1
  try simp only [WP.uncurry'_pair] at A1
  obtain ⟨hI5, w5, ea5, st5⟩ := A1
  have h5 := AllCores.twStep h4 hcpu hS0 hI4 w5 hI5 st5 ea5
  have hcpu5 : L.cpu s5 ∈ Cs := by rw [w5.2.1]; exact hcpu
  have hBA5 : BufAt st T Cs H Sg Scs Z U s5 := BufAt.of_fr hBA4 (TW.ibFr hq4 hq4.curT w5)
  obtain ⟨Q5, R5, hq5⟩ := hI5.1
  have hc5 : L.curW s5 ∈ T := hq5.curT
  have C := vcpu.check.tw (U := {b | UsrW st T Cs H Sg Scs Z s5 b}) hA hNt s5 a5 hI5 (fun b hb => hb)
    (WP.spec_mono (hBA5.2 _ hc5) fun b hb h0 i hi => hBA5.1 _ (hb h0 i hi)) (fun hv => hV s5 hI5 w5 _ hc5 hv)
  rw [e', WP.spec_ok] at C
  try simp only [WP.uncurry'_pair] at C
  obtain ⟨hI', w', ea', st'⟩ := C
  exact AllCores.twStep h5 hcpu5 hS0 hI5 w' hI' st' ea'

/-- **From `schedule`'s start to the entry's exit, with `VcpuEnt` at the
entry** (`AllCores.exit` without `hVW`): the body's `FootB` from the entry
`s0` to `schedule`'s start `s3`. -/
theorem AllCores.exitV (hA : P0.ArchTotal ar) (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (hS0 : (0#u64) ∉ Scs) {s0 s3 s4 s' : S} {a3 a4 a' : A}
    (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0) (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (B03 : FootB st T Cs Sg Scs Z ∅ s0 s3)
    (hB3 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s3) (hBA3 : BufAt st T Cs H Sg Scs Z U s3)
    (esc : sched.schedule st ar s3 a3 = ok (s4, a4)) (h4 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s4)
    (E : (do
        let (s5, a5) ← sched.activate_thread st ar s4 a4
        let t ← sched.cur_thread st s5
        vcpu.check st ar s5 a5 t) = ok (s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  have hB3' := hB3
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := hB3'
  have hI := sched.schedule.entry hA IK hNt s3 a3 Q R hq hB hS hX hSg hBA3
  rw [esc, WP.spec_ok] at hI
  try simp only [WP.uncurry'_pair] at hI
  have hBA4 : BufAt st T Cs H Sg Scs Z U s4 := BufAt.of_fr hBA3 (schIb_holds hA IK hNt s3 a3 _ hB3 hBA3 esc)
  -- the entry's writes up to `schedule`'s end, in `Cur0W s0`
  obtain ⟨Q0, R0, hq0⟩ := hI0.1
  have hSg0 : SgOK st Ω Sg s0 := hI0.2.2.2.1.sg
  have Fs := sched.schedule.sfootB hA IK hNt s3 a3 hB3 hBA3
  rw [esc, WP.spec_ok] at Fs
  try simp only [WP.uncurry'_pair] at Fs
  obtain ⟨rf, -, Fd, Fb⟩ := Fs
  have k3 : L.ksb s3 = L.ksb s0 := B03.1
  have kf : L.ksb rf.1 = L.ksb s0 := Fd.1.trans k3
  have k4 : L.ksb s4 = L.ksb s0 := Fb.1.trans kf
  have G03 : Fr0 st T Cs Ω H Sg Scs Z s0 s3 :=
    WritesIn.mono B03 fun b hb => Or.inl (KW.mono (KWB.kw hb) (Set.empty_subset _))
  have G3f : WritesIn st s3 rf.1 (Cur0W st T Cs Ω H Sg Scs Z s0) := Fd.mono fun b hb => by
    rcases hb with (hk | hd) | hu
    · exact Or.inl (KW.ksb k3 hk)
    · exact Or.inr (Or.inl (DbgW.ksb k3 hd))
    · exact cur0w_usr k3 (hBA3.1 b hu)
  have Gf4 : WritesIn st rf.1 s4 (Cur0W st T Cs Ω H Sg Scs Z s0) := Fb.mono fun b hb => cur0w_sb hSg0 kf hb
  have G04 : Fr0 st T Cs Ω H Sg Scs Z s0 s4 := cw_trans (cw_trans G03 G3f) Gf4
  obtain ⟨Q4, R4, hq4⟩ := hI.1
  exact AllCores.tailV hA hNt h4 hS0 hI hBA4
    (fun s5 hI5 w5 => VcpuUsr.of_ent V
      (cw_trans G04 (w5.mono fun b hb => cur0w_tw hq0 k4 hq4.curT hq4.cur hb)) hI5) E

set_option maxHeartbeats 4000000 in
/-- **The timer-interrupt local entry ends in `AllCores`**, with `VcpuEnt`
at the entry for `hVW`. Named premises: `hR` [J], `hS0` [W], `hKS` [W] (as
`timer_irq_local.allCores`), `V` [P] (`VcpuEnt`). -/
theorem timer_irq_local.allCoresExitV (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {irq : U64} {p : localtimer.TimerIrqPlan}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hKS : ScKsOut st Scs Z s0)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0)
    (e : localtimer.handle_timer_irq_local st ar s0 a0 irq p = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, B03, esc, W, E⟩ :=
    timer_irq_local.allCoresB hA IK hNt h0 hcpu hS0 hKS hI0 hBA0 hR e
  exact AllCores.exitV hA IK hNt hS0 V hI0 B03 hB3 hBA3 esc W E

set_option maxHeartbeats 4000000 in
/-- **The `TCB_SetTimer` local entry ends in `AllCores`**, with `VcpuEnt` at
the entry for `hVW`. Named premises: `hR` [J], `hS0` [W] (as
`set_timer_local.allCores`), `V` [P] (`VcpuEnt`). -/
theorem set_timer_local.allCoresExitV (hA : P0.ArchTotal ar) (IK : IbKeep st ar)
    (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 s' : S} {a0 a' : A} {n : I64} {target : U64}
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hI0 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hBA0 : BufAt st T Cs H Sg Scs Z U s0) (htg : target ∈ T)
    (hR : ∀ (s : S) (a : A), EntryEnd st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s →
      ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1)
    (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0)
    (e : localtimer.handle_set_timer_local st ar s0 a0 n target = ok (true, s', a')) :
    AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' := by
  obtain ⟨s3, a3, s4, a4, hB3, hBA3, B03, esc, W, E⟩ :=
    set_timer_local.allCoresB hA IK hNt h0 hcpu hS0 hI0 hBA0 htg hR e
  exact AllCores.exitV hA IK hNt hS0 V hI0 B03 hB3 hBA3 esc W E

/-- **(P1) `vcpu::check` of the current thread keeps `EntryInv`**, with
`vcpu.check.entry`'s `hpw` [P] from `VcpuEnt` at an earlier state `s0` and
the writes since within `Cur0W` (`Fr0`); the user words are the `UsrW`
words. -/
theorem _root_.Fl4Proofs.P1.vcpu.check.entryV (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    {s0 : S} (s : S) (a : A) (V : VcpuEnt st T Cs Ω H Sg Rp Scs Nt Z s0) (F : Fr0 st T Cs Ω H Sg Scs Z s0 s)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {b | UsrW st T Cs H Sg Scs Z s b} b ⦄) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨Q, R, hq⟩ := h.1
  exact vcpu.check.entry hA hNt s a h (fun b hb => hb) hbuf
    (fun hv => VcpuUsr.of_ent V F h _ hq.curT hv)

end

end Fl4Proofs.P2.Stall
