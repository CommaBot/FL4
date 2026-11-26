/-
# P2 (line p3mc, gen 12): the VM-fault run at a view start with a homed handler, on the view's words (`vmB_run`)

At a VM-fault start state `σ` at core `c`'s view (`VmPre (userV K)`, `QPs`, the view's kernel words), with action
`RESUME_CURRENT` and, wherever the fault-handler slot holds an endpoint cap whose endpoint receives, its head homed
on `c` in `ρ` (`hB`), the run from `σ` is the run on a guarded store `guard st Rd Wr` whose reads are aligned
kernel words the view keeps (`VN`), readable at `σ` or of an unchanged class owner, and whose writes are `VNW`:
* accepted: `vm_accR` (P2/VmAccN) with the record `vm_narA_view` (P2/VmBView), the handler homed by `hB`;
* declined: `vm_local_guard_dec` on `IoRS (userP K) ∧ VN` (the reads are then readable at `σ`), as in
  `vmF_nogo_annV` with the head homed by `hB`.

No premise. No existing statement changed.
-/
import Fl4Proofs.P2.VmBView
import Fl4Proofs.P2.VmDecTop
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_tcb vkc_of not_vdec_node)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 4000000 in
/-- **The run from a view start with a homed handler is a run on the view's words** (module docstring). -/
theorem vmB_run (hA : P0.ArchTotal ar) {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64}
    {addr code : U64} {σ : S} {a : A}
    (hP : VmPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1))
    (hB : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) →
      L.epState s1 ptr = obj.EP_RECV → ρ (affA (L.mem s1 (epHeadA ptr))) = c)
    (hTabR : ∀ hi : U64, hi.val < 2048 → region K.toKLayout (atAF (L.ksb σ) hi) = .none ∧
      (L.mem σ (atAF (L.ksb σ) hi) ≠ 0#u64 → ∀ lo : U64, lo.val < 512 →
        region K.toKLayout (peAF (L.mem σ (atAF (L.ksb σ) hi)) lo) = .none)) :
    ∃ (Rd Wr : U64 → Prop) (r : Bool × S × A),
      (∀ b, Rd b → Aligned b ∧ b ∉ K.user ∧ VN K c ρ b ∧
        (IoRS (st := st) (userP K) Locks σ b ∨ VKc K.toKLayout c ρ b)) ∧
      (∀ b, Wr b → Aligned b ∧ VNW K c ρ b) ∧
      (r.1 ≠ true → ∀ b, Rd b → IoRS (st := st) (userP K) Locks σ b) ∧
      syscall.handle_vm_fault_local st ar σ a addr code = ok r ∧
      syscall.handle_vm_fault_local (PathObl.guard st Rd Wr) ar σ a addr code = ok r := by
  have P' : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ := vmFPre_userP hK hq.ks hP.1
  have B := hP.1.base
  have B' := P'.base
  have hK0 := hK.base.base
  have D' := vm_dfOf hA P' hP.2.1 eu
  have hsc0 : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := B.bxi.2.1.resume hact
  have hcsc : ρ (fld (L.cscW σ) 16#u64) = c := (vm_homes B' hmm).1 hsc0
  obtain ⟨r, hr⟩ := vm_total (st := st) hA addr code σ a
  -- node words are read and written on the view's words
  have ndR : ∀ o : U64, o.val < 4288 → region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node c := fun o ho => by
    rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)
  by_cases hacc : r.1 = true
  · -- accepted
    obtain ⟨b0, s', a'⟩ := r
    change b0 = true at hacc
    subst hacc
    refine ⟨NNv (st := st) K c ρ Locks σ, NWv K c ρ, _, fun b hb => hb, fun b hb => hb,
      fun h => absurd rfl h, hr, ?_⟩
    refine vm_accR hA P' (vm_narA_view hK P' hc hmm hcsc hP.2.2 hTabR) ?_ hr
    intro x1 a1' ptr badge dest rr eu' C
    rw [eu] at eu'
    obtain ⟨e1, -⟩ := Prod.mk.inj (ok_inj_ff eu')
    subst e1
    obtain ⟨sl, x', y, g, gr, hS, hcap, -⟩ := C.cap
    rw [D'.cur] at hS
    have hst : L.epState s1 ptr = obj.EP_RECV := by
      have h1 := C.ep
      rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at h1
      exact ok_inj_ff h1
    have hhd : dest = L.mem s1 (epHeadA ptr) := by
      have h1 := C.head
      rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)] at h1; exact (ok_inj_ff h1).symm
    have h := hB sl ptr badge x' y g gr hS hcap hst
    rw [← hhd] at h
    exact h
  · -- declined: `vmF_nogo_annV`'s certificate at `σ` itself
    let Rd : U64 → Prop := fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b
    have hsc0' := hsc0
    have F : VmFhR st Rd σ s1 := VmFhR.and (VmFhR.ofDF D') (vmFhR_vn hA hK P' hc hmm hsc0' eu)
    have hRal : ∀ b, Rd b → Aligned b := fun b hb => hb.1.1
    have ndRd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
      ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (ndR o ho))⟩
    have rT := ndRd layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
    have rN := ndRd layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    have hdW : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
        obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) → L.epState s1 ptr = obj.EP_RECV →
        ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
          ¬ Fl4Proofs.P2.OwnMap.TimerField off.val → ¬ Fl4Proofs.P2.OwnMap.GField off.val →
          Rd (core.num.U64.wrapping_add (L.mem s1 (epHeadA ptr)) off) := by
      intro sl ptr badge x' y g gr hsl hcap hst off h1 h2 h8 ht hG
      have hd : L.mem s1 (epHeadA ptr) ∈ T := (D'.ep sl ptr badge x' y g gr hsl hcap).2.2 hst
      have hdK : K.heap (L.mem s1 (epHeadA ptr)) = some .tcb := B.hT _ hd
      have hdA' := B.tp _ hd
      have hρh := hB sl ptr badge x' y g gr hsl hcap hst
      have hrA : region K.toKLayout (affA (L.mem s1 (epHeadA ptr))) = .tcb (L.mem s1 (epHeadA ptr)) :=
        B.lay.io.tcbw _ hdK 3520#u64 (by simp) (by simp)
      have hnd : ∀ o : U64, o.val < 4288 → affA (L.mem s1 (epHeadA ptr)) ≠ L.nodeAt σ (L.cpu σ) o := by
        intro o ho e
        have h2' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := B.lay.io.node _ _ (B.inNode o ho)
        rw [← e, hrA] at h2'
        cases h2'
      have hdA : Aligned (affA (L.mem s1 (epHeadA ptr))) := field_aligned hdA' (by simp) (by simp)
      have hAff : IoRS (st := st) (userP K) Locks σ (affA (L.mem s1 (epHeadA ptr))) :=
        D'.gate _ hd 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
      have haff : L.mem s1 (affA (L.mem s1 (epHeadA ptr))) = L.cpu s1 := by
        obtain ⟨now, -, ex⟩ := upd_eq eu
        have hTa : Aligned (ctA (L := L) σ) := rT.1.1
        have hNa : Aligned (cnA (L := L) σ) := rN.1.1
        have key : ∀ b, Aligned b → b ≠ ctA (L := L) σ → b ≠ cnA (L := L) σ → L.mem s1 b = L.mem σ b := by
          intro b hb h1 h2
          rw [ex, L.mem_wr _ _ _ _ hNa hb, if_neg (fun h => h2 h.symm), L.mem_wr _ _ _ _ hTa hb,
            if_neg (fun h => h1 h.symm)]
        have e1 : L.mem s1 (affA (L.mem s1 (epHeadA ptr))) = L.mem σ (affA (L.mem s1 (epHeadA ptr))) :=
          key _ hdA (hnd _ (by simp [layout.node.CUR_TIME])) (hnd _ (by simp [layout.node.CONSUMED]))
        rw [e1, hmm _ hdA (fun hu => hAff.2.1 (Or.inl (Or.inl hu))), D'.c, hc]
        exact Fl4Proofs.P2.CoreView.view_aff hK.base.base hdK c ρ
      refine ⟨?_, vn_of_nf hK (nf_tcb (B.lay.io.tcbw _ hdK off h1 h2) hρh)⟩
      by_cases hg : Fl4Proofs.P2.OwnMap.GateField off.val
      · exact D'.gate _ hd off h1 h2 h8 hg
      · exact D'.home _ hd haff off h1 h2 h8 hg ht hG
    have hn : r.1 ≠ true := hacc
    let Wr : U64 → Prop := fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ
    have hnd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Aligned (L.nodeAt σ (L.cpu σ) o) ∧
        VNW K c ρ (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
      ⟨nodeAt_aligned B.np ho h8, vn_of_nf hK (nf_node (ndR o ho)), vkc_of hK0 (nf_node (ndR o ho)).1,
        not_vdec_node hK0 (ndR o ho)⟩
    refine ⟨Rd, Wr, r, fun b hb => ⟨hb.1.1, fun hu => hb.1.2.1 (Or.inl (Or.inl hu)), hb.2, Or.inl hb.1⟩,
      fun b hb => ?_, fun _ b hb => hb.1, hr, ?_⟩
    · rcases hb with rfl | rfl
      · exact hnd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
      · exact hnd' _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
    refine vm_local_guard_dec (R := Rd) (W := Wr) rT (Or.inl rfl) rN (Or.inr rfl) ?_ hr hn
    intro x1 a1' eu'
    rw [eu] at eu'
    obtain ⟨e1, -⟩ := Prod.mk.inj (ok_inj_ff eu')
    subst e1
    obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := F.alt (Ag.mk rfl rfl fun _ _ => rfl) (fun b hb => hb)
    have ecur1 := F.cur_alt (Ag.mk rfl rfl fun _ _ => rfl)
    have hsh := F.suf
    refine ⟨nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
      nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]), hsh, ?_⟩
    rw [ecur1]
    refine ⟨nd1, dt1, cd1, bm1, tm1, rh1, fun sl hsl => F.sl sl hsl, ?_⟩
    intro sl ptr b x' y g gr hsl hcap
    obtain ⟨rts, rhd⟩ := F.ep sl ptr b x' y g gr hsl hcap
    refine ⟨rts, rhd, fun hst d hd => ?_⟩
    have hst1 : L.epState s1 ptr = obj.EP_RECV := by
      rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at hst
      exact ok_inj_ff hst
    have hdd : d = L.mem s1 (epHeadA ptr) := by
      rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)] at hd
      exact (ok_inj_ff hd).symm
    have W := hdW sl ptr b x' y g gr hsl hcap hst1
    rw [← hdd] at W
    refine ⟨W 3360#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
        (by simp [Fl4Proofs.P2.OwnMap.GField]),
      W 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
        (by simp [Fl4Proofs.P2.OwnMap.GField]), fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
    · exact W 3432#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
        (by simp [Fl4Proofs.P2.OwnMap.GField])
    · exact W 3464#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
        (by simp [Fl4Proofs.P2.OwnMap.GField])
    · exact W 3592#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
        (by simp [Fl4Proofs.P2.OwnMap.GField])
    · exact W 3448#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
        (by simp [Fl4Proofs.P2.OwnMap.GField])

end main

end
end Fl4Proofs.P2.E2EP
