/-
# P2 (line lvm, gen 8): **`local_vm_timer_irq` as an `E2E.LocalPath` under `ownV`**

`vtimer_localPath`: `localvm.handle_vm_timer_irq_local` (fl4-sync's `local_vm_timer_irq`: the timer interrupt
while the current thread runs its guest; the IRQ `irq`, the timer plan `pl`, the glue's notification `n`) for rule
7's map `OwnMapV.ownV K`, the value classes `OwnMap.cls` / `OwnMap.ko` of the base layout and user memory `K.user`,
with `local_vm_exit`'s sets `VexitRS` / `VexitWS` and `DecSet = IrqDec`, `Pre = VtmEnt` (`P2/AccessLvmTo.lean`).
Assembled as `vexit_localPath` (`P2/AccessLvmLP.lean`, itself p2lt's `irq_localPath`):

* `vtimer_alt`: every run at an alternative state is the entry's: an accepted entry run is the same run on
  `guard st VexitRS VexitWS` (`vtimer_acc_own`, the fire case `hF`), a declined one on `guard st VexitRS IrqDec`
  (`hD`); `interp_agree` moves the guarded run to the alternative;
* `vtimer_pathObl`: `acc`, `dec_alt`, `read_own` / `write_own` / `aligned` (gen 5's set lemmas), `move` (declined:
  `dec_alt`; accepted: `vtimer_move`, the fire case `hFm`);
* `vtimer_pathSide`, `vtimer_localPath` (totality from P0).

Premises of `vtimer_localPath`:
* `hp` [P] `IsProg`, `hz` [W] `NoZero`, `hm` [P] `MasksWr`, `hro` [W] `ReadOnce` (as every `LocalPath`);
* `hK` [J] `RegionOKV`, `hU` [J] `UserOKV`; `VtmEnt`'s fields (`P2/AccessLvmTo.lean`); `hEU` [J] (`VtmEnt` survives
  a user write), `hlk` [P] (so do the glue's locks, for an aligned user word: gen 10 added `Aligned b`);
* **`hF` / `hFm` [W]: the fire case** (a due timer whose `fire_ok` holds: the timer interrupt's fire walk,
  p2lf's `FootTimerFire*`, with the VM head and the two `vcpu::check`s; as the old `irq_localPath`'s `hF` / `hFm`);
* `hNt` (P1's notifications typed in its heap `H`; `fun _ h => h` at `Nt = H.ntfns`): declines are discharged
  (gen 9) by `vtimer_dec_own` (`P2/AccessLvmTd.lean`), `vtimer_pathObl` / `vtimer_pathSide` keep `hD` as a
  parameter.
-/
import Fl4Proofs.P2.AccessLvmTd
import Fl4Proofs.P2.AccessLvmLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard mguard RPerm WPerm GateOnly StepOK SProg IsProg NoZero interp interp_agree
  interp_mono interp_guard interp_to_mguard)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV RegionOKV UserOKV stepOKV_of_stepOK ownDepV)
open Classical

/-- The VM-timer body as `E2E.LocalPath.F`. -/
abbrev vtimerBody (S : Type) (irq : U64) (pl : localtimer.TimerIrqPlan) (n : U64) : ∀ {A : Type},
    machine.Arch A → machine.Store S → S → A → Result (Bool × S × A) :=
  fun ar m s a => localvm.handle_vm_timer_irq_local m ar s a irq pl n

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {irq n : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
  {p : SProg Bool} {m : U64 → U64}

variable {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop}

/-- **Every run at an alternative is the entry's** (module docstring), the fire case `hF` and declines `hD`. -/
theorem vtimer_alt (hA : P0.ArchTotal ar) (hK : RegionOKV K)
    (hp : ∀ mm : machine.Store S, vtimerBody S irq pl n ar mm = interp mm ar p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s)
    {s s' : S} {a : A} {r' : Bool × S × A}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (hF : IrqFire st ar s a → ∀ s1 a1, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hD : ∀ s1 a1, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1))
    (hAlt : PathObl.Alt st (VexitRS K st lk s) cls ko User s s')
    (h' : localvm.handle_vm_timer_irq_local st ar s' a irq pl n = ok r') :
    (∃ s1 a1, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) ∧ r'.1 = true ∧
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s' a irq pl n = ok r') ∨
    (∃ s1 a1, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) ∧ r'.1 = false ∧
      localvm.handle_vm_timer_irq_local (guard st Aligned (IrqDec st s)) ar s' a irq pl n = ok r') := by
  have hR1 : ∀ w, VexitRS K st lk s w → Aligned w := fun _ hw => hw.1
  have hW1 : ∀ w, VexitWS K st lk s w → Aligned w := fun _ hw => hw.1
  have hW2 : ∀ w, IrqDec st s w → Aligned w := fun _ hw => (hE.ent.dec hw).1
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp mm) x) a
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) W') ar s a irq pl n = ok (x, s1, a1) →
      r'.1 = x ∧ localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) W') ar s' a irq pl n = ok r' := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa p hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks hAlt.read hg
    have hst := (interp_guard p s' a _ hg').1
    rw [← eP, h'] at hst
    have e := Result.ok_injective hst
    subst e
    exact ⟨rfl, by rw [eP]; exact hg'⟩
  obtain ⟨r, hr⟩ : ∃ r, localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok r := by
    have := P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq pl n LawfulStore.total hA
    obtain ⟨r, e, -⟩ := spec_ex_fd this
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  swap
  · left
    have hacc : localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1) := by
      exact vtimer_acc_own ar hA hK hE (fun hf => hF hf s1 a1 hr) hr
    obtain ⟨h1, h2⟩ := tr hW1 hacc
    exact ⟨s1, a1, hr, h1, h2⟩
  · right
    obtain ⟨h1, h2⟩ := tr hW2 (hD s1 a1 hr)
    refine ⟨s1, a1, hr, h1, ?_⟩
    rw [eP] at h2 ⊢
    exact interp_mono hR1 (fun _ h => h) p hz s' a r' h2

/-- **`PathObl` for `local_vm_timer_irq`** (module docstring), the fire premises `hF` / `hFm`, declines `hD`. -/
theorem vtimer_pathObl (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s)
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s1, a1))
    (hD : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1)) :
    PathObl.PathObl st (fun mm s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n) (fun b => b = true)
      (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) lk
      (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n) (VexitRS K st lk) (VexitWS K st lk) (IrqDec st) := by
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n = interp mm ar p x a :=
    fun mm x a => congrFun (congrFun (hp A ar mm) x) a
  have hQ : ∀ s, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → ∀ (x : S) (q v' : U64), IrqDec st s q →
      StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem (L.wr x q v')) := by
    intro s hE x q v' hq
    obtain ⟨a1, -, c, hc⟩ := hE.ent.dec hq
    refine stepOKV_of_stepOK hK ⟨fun w hw => absurd (own_keep hK.base hU.base a1 (Or.inl ⟨c, hc⟩) x v' w) hw,
      fun w hw _ => ?_⟩
    by_cases hwq : w = q
    · subst hwq; exact Or.inr (Or.inr (by simp only [OwnMap.ko, hc]))
    · by_cases hf : OwnMap.ko K.toKLayout m w = .free
      · exact Or.inr (Or.inr hf)
      · exact absurd (mem_wr_ne' a1 (OwnMap.ko_aligned hK.base hU.base m w hf) (fun e => hwq e.symm)) hw
  have dec : ∀ s a r, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok r → r.1 ≠ true →
      ∀ s' r', PathObl.Alt st (VexitRS K st lk s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' →
      localvm.handle_vm_timer_irq_local st ar s' a irq pl n = ok r' →
      r'.1 ≠ true ∧
      localvm.handle_vm_timer_irq_local (guard st (fun _ => True) (IrqDec st s)) ar s' a irq pl n = ok r' ∧
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s' a irq pl n = ok r' := by
    intro s a r hE hr hn s' r' hAlt h'
    rcases vtimer_alt ar hA hK (fun mm => hp A ar mm) hz hm hE (fun hf s1 a1 => hF s a s1 a1 hE hf)
      (fun s1 a1 => hD s a s1 a1 hE)
      hAlt h' with ⟨s1, a1, e, -, -⟩ | ⟨s1, a1, -, h1, h2⟩
    · rw [hr] at e
      exact absurd (by rw [Result.ok_injective e]) hn
    · rw [eP] at h2
      refine ⟨by rw [h1]; exact Bool.false_ne_true, ?_, ?_⟩
      · rw [eP]; exact interp_mono (fun _ _ => trivial) (fun _ h => h) p hz s' a r' h2
      · rw [eP]; exact interp_to_mguard (fun x q v' hq => hQ s hE x q v' hq) p hz s' a r' h2
  refine ⟨?_, dec, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact vtimer_acc_own ar hA hK hE (fun hf => hF s a s1 a1 hE hf h) h
  · intro s x _ hx hu; exact vexit_read_own hx hu
  · intro s x hE hx hu
    exact vexit_write_own hK (fun q hq => ⟨(hE.ent.dec hq).2.1, (hE.ent.dec hq).2.2⟩) hx hu
  · intro s x hE hx
    exact vexit_aligned (fun q hq => (hE.ent.dec hq).1) hx
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (dec s a _ hE h Bool.false_ne_true s _ (PathObl.Alt.refl s) h).2.2
    · exact vtimer_move ar hA hK hU hp (fun _ => rfl) hE (fun hf => hFm s a s1 a1 hE hf h) h

/-- **`PathSide` for `local_vm_timer_irq`** (module docstring). -/
theorem vtimer_pathSide (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s)
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hD : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (false, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a irq pl n =
        ok (false, s1, a1))
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s) :
    PathObl.PathSide st (fun mm s a => localvm.handle_vm_timer_irq_local mm ar s a irq pl n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user) lk (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n)
      (VexitRS K st lk) (VexitWS K st lk) (IrqDec st) := by
  refine ⟨?_, fun s x _ hx => hx.1, OwnMap.ko_aligned hK.base hU.base m, fun s b v' hE hb hba =>
    ⟨hEU s b v' hE hb hba, hlk s b v' hb hba, vexitRS_wr_user hK hU hb hba (hlk s b v' hb hba),
      vexitWS_wr_user hK hU hb hba (hlk s b v' hb hba), irq_dec_user s b v'⟩⟩
  intro s s' a r hE hAlt h
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vm_timer_irq_local mm ar x a irq pl n = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp A ar mm) x) a
  rcases vtimer_alt ar hA hK (fun mm => hp A ar mm) hz hm hE (fun hf s1 a1 => hF s a s1 a1 hE hf)
      (fun s1 a1 => hD s a s1 a1 hE)
    hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
  · show localvm.handle_vm_timer_irq_local _ ar s' a irq pl n = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a r h2
  · show localvm.handle_vm_timer_irq_local _ ar s' a irq pl n = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2

/-- **`local_vm_timer_irq` is a local path under `ownV`** (module docstring); the fire case is the premise
`hF` / `hFm` [W]; declines by `vtimer_dec_own` (gen 9). -/
noncomputable def vtimer_localPath (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vtimerBody S irq pl n) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n) (VexitRS K st lk))
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s)
    (hF : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a irq pl n =
        ok (true, s1, a1))
    (hFm : ∀ s a s1 a1, VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → IrqFire st ar s a →
      localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1) →
      localvm.handle_vm_timer_irq_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a irq pl n = ok (true, s1, a1))
    (hNt : ∀ q ∈ Nt, H q = some .ntfn) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vtimerBody S irq pl n
  p := p
  Acc := fun b => b = true
  Locks := lk
  Pre := VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n
  RS := VexitRS K st lk
  WS := VexitWS K st lk
  DS := IrqDec st
  isProg := PathObl.IsProg.on hp _ _ _
  obl := vtimer_pathObl ar hA hK hU hp hz hm hF hFm (fun _ _ _ _ hE h => vtimer_dec_own ar hA hK hNt hE h)
  side := vtimer_pathSide ar hA hK hU hp hz hm hF (fun _ _ _ _ hE h => vtimer_dec_own ar hA hK hNt hE h) hEU hlk
  once := hro
  total := fun s a => by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq pl n LawfulStore.total hA)
    exact ⟨r, e⟩
  masks := hm

end

end Fl4Proofs.P2
