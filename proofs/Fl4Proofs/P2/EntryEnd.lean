/-
P2 (p2je): **the entry-side end facts of `AllCores.schedE`** (`kb`, `hidl`,
`hao`, `hcK`, `hsa`), from one footprint of the entry body.

* `PrW.monoK`, `FootN.monoK`: a `KWN` footprint is antitone in the protected
  set `Kp`.
* **`AllCores.bodyEnd`**: from `AllCores s0` (and P1's `BlkOK` at `s0`), an
  entry body `s0 → s` whose writes are a `FootN` over `KI e s0` (the other
  cores' idle, current and action threads and the executing core's idle
  thread, `e = L.cpu s0`) in no-donation mode (`Nd`: every thread's `SC` and
  `AFFINITY`, every SC's `REPLY`/`TCB`, and the executing core's own
  `CUR_THREAD` are not written) gives at `s`: `kb` (`OKeep2 e s0 s`), the
  same core, `hao` (`ActOut` over `OtherK e s0`: the action at `s0` is no
  thread, `AllCores.actNT`, and `AcK` over `KI` lets no protected thread
  become it), `hcK` (the current thread is the one of `s0`, affinity `e`),
  `hidl` (the executing core's idle thread is in `KI`, so its `STATE` is kept
  `TS_IDLE`).
* **`AllCores.schedB`**: `AllCores.schedE` with those facts supplied: from
  the body's footprint, P1's `BlkOK`/`BufAt` at its end and `ActAff` there
  (`ActAff.nT` when the action is no thread), `schedule` ends in `AllCores`.

Named premises of `AllCores.schedB` (as `AllCores.schedE`): `hR` [J] (with
action `RESUME` at the end of `awaken` the current thread is `SchCur`; the
domain-invariant finding of `P2/FootN10.lean`), `hS0` [W] (`0 ∉ Scs`).
-/
import Fl4Proofs.P2.FootN10
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es U : Set U64}

theorem PrW.monoK {Kp Kp' : Set U64} {Nd : Prop} {s : S} {b : U64} (hsub : ∀ y, y ∈ Kp → y ∈ Kp')
    (h : PrW st Kp Nd T Cs Scs s b) : PrW st Kp' Nd T Cs Scs s b := by
  rcases h with ⟨y, hy, ha, hk, e⟩ | h
  · exact Or.inl ⟨y, hy, ha, hsub _ hk, e⟩
  · exact Or.inr h

/-- A `KWN` footprint is antitone in the protected set. -/
theorem FootN.monoK {Kp Kp' : Set U64} {Nd : Prop} {s s' : S} (hsub : ∀ y, y ∈ Kp → y ∈ Kp')
    (f : FootN st Kp' Nd T Cs Sg Scs Z Es s s') : FootN st Kp Nd T Cs Sg Scs Z Es s s' :=
  ⟨f.1, f.2.1, fun b hb hn => f.2.2.1 b hb fun hk => hn ⟨hk.1, fun hi => hk.2 (hi.imp id (PrW.monoK hsub))⟩,
    fun hT hK => f.2.2.2 hT (hsub _ hK)⟩

/-- **The entry-side end facts from the body's footprint** (module docstring). -/
theorem AllCores.bodyEnd {s0 s : S} (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs)
    (hB0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (f : FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s) :
    OKeep2 st T Cs (L.cpu s0) s0 s ∧ L.cpu s = L.cpu s0 ∧
      ActOut st T (OtherK st T Cs (L.cpu s0) s0) s ∧ L.curW s ∉ OtherK st T Cs (L.cpu s0) s0 ∧
      L.mem s (stA (L.idleW s)) = sched.TS_IDLE ∧ L.curW s = L.curW s0 := by
  obtain ⟨⟨Q, R, hq⟩, -, hX, -, -⟩ := hB0
  have hT := hq.tcbs
  have iT : ∀ c ∈ Cs, idleAt st c s0 ∈ T := fun c hc => (h0.core hc).per.idleT
  have iS : ∀ c ∈ Cs, L.mem s0 (scA (idleAt st c s0)) ∈ Scs := fun c hc =>
    (hX.2.2.bound _ (iT c hc) (h0.core hc).per.idle).1
  have kb : OKeep2 st T Cs (L.cpu s0) s0 s :=
    OKeep2.ofSN hq hX.1 h0.KT iT iS (FootN.sN (FootN.monoK (fun y hy => Or.inl hy) f))
  have hc : L.cpu s = L.cpu s0 := f.2.1
  have hN := hq.nodes _ hq.cur
  have ecur : L.curW s = L.curW s0 := by
    unfold LawfulStore.curW
    rw [nodeAt_of_ksb f.1, f.2.1]
    exact f.idKeep (nodeAt_aligned hN (by rw [curth0]; omega) (by rw [curth0]))
      (Or.inl ⟨_, hq.cur, _, Or.inr (Or.inr (Or.inr ⟨trivial, rfl, by rw [curth0]⟩)), rfl⟩)
  have hiE : idleAt st (L.cpu s0) s0 ∈ T := iT _ hcpu
  have ei : L.idleW s = idleAt st (L.cpu s0) s0 := by
    show idleAt st (L.cpu s) s = _
    rw [hc]; exact kb.idle_eq hcpu
  refine ⟨kb, hc, fun hTa hK => ?_, ?_, ?_, ecur⟩
  · have e := f.2.2.2 hTa (Or.inl hK)
    rw [e] at hTa
    exact h0.actNT _ hcpu hTa
  · rw [ecur]
    exact h0.notK (h0.curAff _ hcpu)
  · rw [ei, f.idKeep (by rw [stA_eq]; exact field_aligned (hT _ hiE) (by simp) (by simp))
      (Or.inr (Or.inl ⟨_, hiE, hT _ hiE, Or.inr rfl, Or.inl rfl⟩))]
    exact h0.idleSt _ hcpu

/-- **`schedule` closes an entry from the body's footprint** (`AllCores.schedE`
with `kb`, `hao`, `hcK`, `hidl` from `AllCores.bodyEnd`). Named premises:
`hR` [J], `hS0` [W] (module docstring). -/
theorem AllCores.schedB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (IK : IbKeep st ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) {s0 s : S} (a : A)
    (h0 : AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s0) (hcpu : L.cpu s0 ∈ Cs) (hS0 : (0#u64) ∉ Scs)
    (hB0 : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s0)
    (f : FootN st (KI st T Cs (L.cpu s0) s0) True T Cs Sg Scs Z (EH H) s0 s)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hBA : BufAt st T Cs H Sg Scs Z U s) (hsa : ActAff st T s)
    (hR : ∀ r : S × A, sched.awaken st ar s a = ok r → L.actionW r.1 = 0#u64 → SchCur st r.1) :
    sched.schedule st ar s a ⦃ s' _ => AllCores st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ := by
  obtain ⟨kb, hc, hao, hcK, hidl, -⟩ := AllCores.bodyEnd h0 hcpu hB0 f
  exact AllCores.schedE hA IK hNt a h0 hcpu hS0 kb hc h hBA hao hcK hsa hR hidl

end

end Fl4Proofs.P2.Stall
