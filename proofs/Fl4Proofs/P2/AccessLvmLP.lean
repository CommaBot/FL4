/-
# P2 (line lvm, gen 6): **`local_vm_exit` as an `E2E.LocalPath` under `ownV`**

`vexit_localPath`: `localvm.handle_vcpu_exit_local` (fl4-sync's `local_vm_exit` for an exit with no host
interrupt; the exiting VCPU `v`, the glue's notification `n`) for rule 7's map `OwnMapV.ownV K`, the value classes
`OwnMap.cls` / `OwnMap.ko` of the base layout and user memory `K.user`, with gen 5's sets `VexitRS` / `VexitWS` and
`DecSet = IrqDec` (`update_timestamp`'s node `CUR_TIME` / `CONSUMED`), `Pre = VexitEnt` (`AccessLvmOwn`). Assembled as
p2lt's `irq_localPath` (`P2/FootTimerIrqObl.lean`):

* `vexit_alt`: every run at an alternative state (`PathObl.Alt` for `VexitRS`) is the entry's: an accepted entry run
  is the same run on `guard st VexitRS VexitWS` (`vexit_acc_own_np`, or the pending-exit premise `hP`), a declined
  one on `guard st VexitRS IrqDec` (`vexit_dec_own`); `interp_agree` moves the guarded run to the alternative;
* `vexit_pathObl`: `acc` from the same two; `dec_alt` from `vexit_alt` (the decline words are this core's node
  words: `StepOK` by `own_keep` and `stepOKV_of_stepOK`); `read_own` / `write_own` / `aligned`: gen 5's
  `vexit_read_own` / `vexit_write_own` / `vexit_aligned`; `move`: declined runs by `dec_alt`, accepted ones by
  `vexit_move_np` (or the pending-exit premise `hPm`);
* `vexit_pathSide`: `read_aligned` from `vexit_alt`, `user_free` from gen 5's `vexitRS_wr_user` / `vexitWS_wr_user`
  and `irq_dec_user`;
* `vexit_total`: P0's totality.

Premises of `vexit_localPath`:
* `hp` [P] `IsProg`, `hz` [W] `NoZero`, `hm` [P] `MasksWr`, `hro` [W] `ReadOnce` (as `irq_localPath`);
* `hK` [J] `RegionOKV`, `hU` [J] `UserOKV`; `VexitEnt`'s fields (`AccessLvmOwn`);
* `Px`: an extra entry predicate (gen 7: `Pre = VexitEnt ∧ Px`; `AccessLvmPo` takes `Px = VexitPEnt`, the
  pending case's facts, and discharges `hP` / `hPm` there: `vexit_localPathP`);
* `hEU` [J]: `VexitEnt ∧ Px` survives a user write (as `irq_localPath`'s); `hlk` [P]: so do the glue's locks;
* `hP` / `hPm` [W]: **the pending-exit case** (`PENDING ≠ 0` at the entry: `vcpu.check` runs `vcpu.report`, which
  writes the current thread's registers, its IPC buffer, `v.PENDING` and its `STATE`): an accepted run is the same
  on `guard st VexitRS VexitWS` (`acc`) and on `mguard` for `ownV`'s `StepOK` (`move`), given `Px s`; discharged
  in gen 7 by `AccessLvmPo` (`vexit_acc_own_p` / `vexit_move_p`, `Px = VexitPEnt`).
-/
import Fl4Proofs.P2.AccessLvmOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard mguard RPerm WPerm GateOnly StepOK SProg IsProg NoZero interp interp_agree
  interp_mono interp_guard interp_to_mguard)
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV RegionOKV UserOKV stepOKV_of_stepOK ownDepV)
open Classical

/-- The VM-exit body as `E2E.LocalPath.F`. -/
abbrev vexitBody (S : Type) (v n : U64) : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A →
    Result (Bool × S × A) :=
  fun ar m s a => localvm.handle_vcpu_exit_local m ar s a v n

/-- The pending-exit case: the VCPU's `PENDING` is not 0 at the entry. -/
def VPend {S : Type} (st : machine.Store S) (v : U64) (s : S) : Prop := vcpu.get st s v vcpu.PENDING ≠ ok 0#u64

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} (ar : machine.Arch A) {v n : U64} {lk : S → U64 → Prop} {p : SProg Bool} {m : U64 → U64}

/-- The decline words are this core's node words. -/
theorem VexitEnt.dec {s : S} (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s) {q : U64}
    (hq : IrqDec st s q) :
    Aligned q ∧ own K.toKLayout (L.mem s) q = .core (L.cpu s) ∧ ∃ c, region K.toKLayout q = .node c := by
  have h0 := hE.inv.1.choose_spec.choose_spec
  have hN : NodePlaced st T s (L.cpu s) := h0.nodes _ h0.cur
  rcases hq with rfl | rfl
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]),
      hE.lay.own_node _ (by simp [layout.node.CUR_TIME]), _, hE.lay.nd _ (by simp [layout.node.CUR_TIME])⟩
  · exact ⟨nodeAt_aligned hN (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      hE.lay.own_node _ (by simp [layout.node.CONSUMED]), _, hE.lay.nd _ (by simp [layout.node.CONSUMED])⟩

variable {cls : U64 → U64 → U64} {ko : U64 → Serial.ClsOwner U64} {User : U64 → Prop} {Px : S → Prop}

/-- **Every run at an alternative is the entry's** (module docstring), the pending-exit premise `hP`. -/
theorem vexit_alt (hA : P0.ArchTotal ar) (hK : RegionOKV K)
    (hp : ∀ mm : machine.Store S, vexitBody S v n ar mm = interp mm ar p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s)
    {s s' : S} {a : A} {r' : Bool × S × A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hP : VPend st v s → ∀ s1 a1, localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
        ok (true, s1, a1))
    (hAlt : PathObl.Alt st (VexitRS K st lk s) cls ko User s s')
    (h' : localvm.handle_vcpu_exit_local st ar s' a v n = ok r') :
    (∃ s1 a1, localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) ∧ r'.1 = true ∧
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s' a v n = ok r') ∨
    (∃ s1 a1, localvm.handle_vcpu_exit_local st ar s a v n = ok (false, s1, a1) ∧ r'.1 = false ∧
      localvm.handle_vcpu_exit_local (guard st Aligned (IrqDec st s)) ar s' a v n = ok r') := by
  have hR1 : ∀ w, VexitRS K st lk s w → Aligned w := fun _ hw => hw.1
  have hW1 : ∀ w, VexitWS K st lk s w → Aligned w := fun _ hw => hw.1
  have hW2 : ∀ w, IrqDec st s w → Aligned w := fun _ hw => (hE.dec hw).1
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vcpu_exit_local mm ar x a v n = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp mm) x) a
  have tr : ∀ {W' : U64 → Prop} {x : Bool} {s1 : S} {a1 : A}, (∀ w, W' w → Aligned w) →
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) W') ar s a v n = ok (x, s1, a1) →
      r'.1 = x ∧ localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) W') ar s' a v n = ok r' := by
    intro W' x s1 a1 hWa hg
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm hR1 hWa p hz s s' a x s1 a1 hAlt.ksb hAlt.cpu hAlt.masks hAlt.read hg
    have hst := (interp_guard p s' a _ hg').1
    rw [← eP, h'] at hst
    have e := Result.ok_injective hst
    subst e
    exact ⟨rfl, by rw [eP]; exact hg'⟩
  obtain ⟨r, hr⟩ : ∃ r, localvm.handle_vcpu_exit_local st ar s a v n = ok r := by
    have := P0.localvm.handle_vcpu_exit_local.p0 st ar s a v n LawfulStore.total hA
    obtain ⟨r, e, -⟩ := spec_ex_fd this
    exact ⟨r, e⟩
  obtain ⟨b, s1, a1⟩ := r
  cases b
  swap
  · left
    have hacc : localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
        ok (true, s1, a1) := by
      by_cases hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64
      · exact vexit_acc_own_np ar hA hK hE hp0 hr
      · exact hP hp0 s1 a1 hr
    obtain ⟨h1, h2⟩ := tr hW1 hacc
    exact ⟨s1, a1, hr, h1, h2⟩
  · right
    obtain ⟨h1, h2⟩ := tr hW2 (vexit_dec_own ar hA hK hE hr)
    refine ⟨s1, a1, hr, h1, ?_⟩
    rw [eP] at h2 ⊢
    exact interp_mono hR1 (fun _ h => h) p hz s' a r' h2

/-- **`PathObl` for `local_vm_exit`** (module docstring), the pending-exit premises `hP` / `hPm`. -/
theorem vexit_pathObl (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vexitBody S v n) p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s)
    (hP : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
        ok (true, s1, a1))
    (hPm : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a v n = ok (true, s1, a1)) :
    PathObl.PathObl st (fun mm s a => localvm.handle_vcpu_exit_local mm ar s a v n) (fun b => b = true)
      (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) lk
      (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s) (VexitRS K st lk) (VexitWS K st lk) (IrqDec st) := by
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      localvm.handle_vcpu_exit_local mm ar x a v n = interp mm ar p x a :=
    fun mm x a => congrFun (congrFun (hp A ar mm) x) a
  have hQ : ∀ s, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → ∀ (x : S) (q v' : U64), IrqDec st s q →
      StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem (L.wr x q v')) := by
    intro s hE x q v' hq
    obtain ⟨a1, -, c, hc⟩ := hE.dec hq
    refine stepOKV_of_stepOK hK ⟨fun w hw => absurd (own_keep hK.base hU.base a1 (Or.inl ⟨c, hc⟩) x v' w) hw,
      fun w hw _ => ?_⟩
    by_cases hwq : w = q
    · subst hwq; exact Or.inr (Or.inr (by simp only [OwnMap.ko, hc]))
    · by_cases hf : OwnMap.ko K.toKLayout m w = .free
      · exact Or.inr (Or.inr hf)
      · exact absurd (mem_wr_ne' a1 (OwnMap.ko_aligned hK.base hU.base m w hf) (fun e => hwq e.symm)) hw
  have dec : ∀ s a r, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok r → r.1 ≠ true →
      ∀ s' r', PathObl.Alt st (VexitRS K st lk s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
        (· ∈ K.user) s s' →
      localvm.handle_vcpu_exit_local st ar s' a v n = ok r' →
      r'.1 ≠ true ∧
      localvm.handle_vcpu_exit_local (guard st (fun _ => True) (IrqDec st s)) ar s' a v n = ok r' ∧
      localvm.handle_vcpu_exit_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s' a v n = ok r' := by
    intro s a r hE hr hn s' r' hAlt h'
    rcases vexit_alt ar hA hK (fun mm => hp A ar mm) hz hm hE.1 (fun hpd s1 a1 => hP s a s1 a1 hE.1 hE.2 hpd)
      hAlt h' with ⟨s1, a1, e, -, -⟩ | ⟨s1, a1, -, h1, h2⟩
    · rw [hr] at e
      exact absurd (by rw [Result.ok_injective e]) hn
    · rw [eP] at h2
      refine ⟨by rw [h1]; exact Bool.false_ne_true, ?_, ?_⟩
      · rw [eP]; exact interp_mono (fun _ _ => trivial) (fun _ h => h) p hz s' a r' h2
      · rw [eP]; exact interp_to_mguard (fun x q v' hq => hQ s hE.1 x q v' hq) p hz s' a r' h2
  refine ⟨?_, dec, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    by_cases hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64
    · exact vexit_acc_own_np ar hA hK hE.1 hp0 h
    · exact hP s a s1 a1 hE.1 hE.2 hp0 h
  · intro s x _ hx hu; exact vexit_read_own hx hu
  · intro s x hE hx hu
    exact vexit_write_own hK (fun q hq => ⟨(hE.1.dec hq).2.1, (hE.1.dec hq).2.2⟩) hx hu
  · intro s x hE hx
    exact vexit_aligned (fun q hq => (hE.1.dec hq).1) hx
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (dec s a _ hE h Bool.false_ne_true s _ (PathObl.Alt.refl s) h).2.2
    · by_cases hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64
      · exact vexit_move_np ar hA hK hU hp (fun _ => rfl) hE.1 hp0 h
      · exact hPm s a s1 a1 hE.1 hE.2 hp0 h

/-- **`PathSide` for `local_vm_exit`** (module docstring). -/
theorem vexit_pathSide (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vexitBody S v n) p) (hz : NoZero p)
    (hm : ∀ s a v', st.frame_masks (L.wr s a v') = st.frame_masks s)
    (hP : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
        ok (true, s1, a1))
    (hEU : ∀ s b v', VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s → b ∈ K.user → Aligned b →
      VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n (L.wr s b v') ∧ Px (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s) :
    PathObl.PathSide st (fun mm s a => localvm.handle_vcpu_exit_local mm ar s a v n) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout m) (· ∈ K.user) lk (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s)
      (VexitRS K st lk) (VexitWS K st lk) (IrqDec st) := by
  refine ⟨?_, fun s x _ hx => hx.1, OwnMap.ko_aligned hK.base hU.base m, fun s b v' hE hb hba =>
    ⟨hEU s b v' hE hb hba, hlk s b v' hb, vexitRS_wr_user hK hU hb hba (hlk s b v' hb),
      vexitWS_wr_user hK hU hb hba (hlk s b v' hb), irq_dec_user s b v'⟩⟩
  intro s s' a r hE hAlt h
  have eP : ∀ (mm : machine.Store S) (x : S),
      localvm.handle_vcpu_exit_local mm ar x a v n = interp mm ar p x a :=
    fun mm x => congrFun (congrFun (hp A ar mm) x) a
  rcases vexit_alt ar hA hK (fun mm => hp A ar mm) hz hm hE.1 (fun hpd s1 a1 => hP s a s1 a1 hE.1 hE.2 hpd)
    hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
  · show localvm.handle_vcpu_exit_local _ ar s' a v n = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a r h2
  · show localvm.handle_vcpu_exit_local _ ar s' a v n = ok r
    rw [eP] at h2 ⊢
    exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2

/-- **`local_vm_exit` is a local path under `ownV`** (module docstring); the pending-exit case is the premise
`hP` / `hPm` [W]. -/
noncomputable def vexit_localPath (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hp : IsProg (vexitBody S v n) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
      (fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s) (VexitRS K st lk))
    (hEU : ∀ s b v', VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s → b ∈ K.user → Aligned b →
      VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n (L.wr s b v') ∧ Px (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → lk (L.wr s b v') = lk s)
    (hP : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
        ok (true, s1, a1))
    (hPm : ∀ s a s1 a1, VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s → Px s → VPend st v s →
      localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s1, a1) →
      localvm.handle_vcpu_exit_local (mguard st
        (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
          (lk s) (L.mem x) (L.mem y))) ar s a v n = ok (true, s1, a1)) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vexitBody S v n
  p := p
  Acc := fun b => b = true
  Locks := lk
  Pre := fun s => VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s ∧ Px s
  RS := VexitRS K st lk
  WS := VexitWS K st lk
  DS := IrqDec st
  isProg := hp
  obl := vexit_pathObl ar hA hK hU hp hz hm hP hPm
  side := vexit_pathSide ar hA hK hU hp hz hm hP hEU hlk
  once := hro
  total := fun s a => by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localvm.handle_vcpu_exit_local.p0 st ar s a v n LawfulStore.total hA)
    exact ⟨r, e⟩
  masks := hm

end

end Fl4Proofs.P2
