/-
# P2 (line p3mc, gen 8): the VM-fault body is `Safe` at the physical memory when its fault handler is another core's

The decline split for vmF (handoff p3mc §10, step 3), assembled: the translation of the VM-fault tree with a read set
`Ro` and the target's class owner `kt` is `Safe` at the physical memory `μ`, at an entry `σ` (any store state) whose
prefix state finds the fault endpoint in the receive state with a head `d` that the real memory `ρ` homes off `c`:

* **`vm_fh_safe`**: `E2E.safe_tr_of_states` with, for each admissible `ν`, the store state with `σ`'s constants, `ν`
  on the words the certificate run reads and `ρ` elsewhere (`exists_mem_state`). That state agrees with `σ` on `Rd`
  (the words `σ` and `ρ` agree on, all readable at `μ`), and its prefix state sees `d` off its core (`d`'s
  `AFFINITY` is readable at `μ`, so it carries `ρ`'s value). So its run declines and is guarded (`vm_fh_guard`), its
  only writes are the two prefix words with `StepOK` (`vm_dec_m` on `mguard`), and it reads each racy word once
  (`vm_fh_once`).

Gen 49 (in place, statement of `vm_fh_safe` unchanged): **`vm_fh_run`**, the run from one store state, split out of
`vm_fh_safe`'s proof (shared with its `InsA` twin, P2/InsV15Fh).

The facts about `σ`, `Rd`, `Ro`, `ρ` and `μ` are hypotheses (to be supplied at core `c`'s view: `VmFhR` from
`VmDF` and the view's pins; `Ro = RS ∧ VO`; `ρ`, `μ` from `VEq`). No premise. No existing statement changed.
-/
import Fl4Proofs.P2.VmFhOnce
import Fl4Proofs.P2.ViewSafeReal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}

set_option maxHeartbeats 1000000 in
/-- **The VM-fault body's run from one store state whose fault handler is another core's** (split out of
`vm_fh_safe`'s proof in place, gen 49): at a state `s` agreeing with `σ` on `Rd` (core and kernel base included) and
seeing the handler's `AFFINITY` off its core, the run declines on `guard st (Rd ∪ {REPLY, AFFINITY}) {CUR_TIME,
CONSUMED}`, its writes pass `StepOK`, and it reads each racy word once. -/
theorem vm_fh_run {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hA : P0.ArchTotal ar) (addr code : U64) {c : U64}
    {hs : U64 → Prop} {σ : S} {a : A} (hc : L.cpu σ = c)
    {Rd Ro : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (rT : Rd (ctA (L := L) σ)) (rN : Rd (cnA (L := L) σ))
    (rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD))
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1)) (F : VmFhR st Rd σ s1)
    {sl ptr badge : U64} {x' y g gr : Bool}
    (hsl : obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr))
    (hst : L.epState s1 ptr = obj.EP_RECV)
    (hAo : Ro (affA (L.mem s1 (epHeadA ptr))) ∧ ¬ User (affA (L.mem s1 (epHeadA ptr))))
    (hdA : Aligned (affA (L.mem s1 (epHeadA ptr))))
    (hdT : affA (L.mem s1 (epHeadA ptr)) ≠ ctA (L := L) σ ∧ affA (L.mem s1 (epHeadA ptr)) ≠ cnA (L := L) σ)
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v)))
    {s : S} (G : Ag st Rd σ s) (hoff : L.mem s (affA (L.mem s1 (epHeadA ptr))) ≠ c) :
    ∃ r, interp (guard st (fun b => Rd b ∨ b = replyA (L.mem s1 (epHeadA ptr)) ∨ b = affA (L.mem s1 (epHeadA ptr)))
        (fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ)) ar (R.syscall.handle_vm_fault_local addr code) s a = ok r ∧
      WithinM st ar (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))
        (R.syscall.handle_vm_fault_local addr code) s a ∧
      Once st ar Ro User ∅ ∅ (R.syscall.handle_vm_fault_local addr code) s a := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local mm ar x a addr code = interp mm ar (R.syscall.handle_vm_fault_local addr code) x a :=
    fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a
  -- the handler and its endpoint are the ones `σ`'s prefix state finds
  have huniq : ∀ sl' ptr' badge' x'' y' g' gr', obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl' →
      obj.Slot.cap st sl' s1 = ok (capability.Cap.Endpoint ptr' badge' x'' y' g' gr') → ptr' = ptr := by
    intro sl' ptr' badge' x'' y' g' gr' hsl' hcap'
    have e1 : sl' = sl := ok_inj_ff (hsl'.symm.trans hsl)
    subst e1
    have e2 := ok_inj_ff (hcap'.symm.trans hcap)
    cases e2
    rfl
  have sc : L.cpu s = L.cpu σ := G.c
  have ecur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ rC
  -- its prefix state sees the handler off its core
  have hFH : VmFhOff st ar σ s1 s a := by
    intro x1 a1' eu' sl' ptr' badge' x'' y' g' gr' hsl' hcap' _
    rw [huniq sl' ptr' badge' x'' y' g' gr' hsl' hcap']
    obtain ⟨now, -, ex⟩ := upd_eq eu'
    have eT : ctA (L := L) s = ctA (L := L) σ := G.node _
    have eN : cnA (L := L) s = cnA (L := L) σ := G.node _
    rw [ex, L.cpu_wr, L.cpu_wr, sc, hc]
    have hTa : Aligned (ctA (L := L) s) := by rw [eT]; exact hRal _ rT
    have hNa : Aligned (cnA (L := L) s) := by rw [eN]; exact hRal _ rN
    rw [L.mem_wr _ _ _ _ hNa hdA, if_neg (by rw [eN]; exact fun h => hdT.2 h.symm),
      L.mem_wr _ _ _ _ hTa hdA, if_neg (by rw [eT]; exact fun h => hdT.1 h.symm)]
    exact hoff
  -- the run declines, guarded
  obtain ⟨r, hr⟩ := vm_total (st := st) hA addr code s a
  obtain ⟨hn, hg⟩ := vm_fh_guard (R'' := fun b => Rd b ∨ b = replyA (L.mem s1 (epHeadA ptr)) ∨
      b = affA (L.mem s1 (epHeadA ptr))) (W := fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ)
    hRal G rT rN eu F hFH (fun b hb => Or.inl hb)
    (fun sl' ptr' badge' x'' y' g' gr' hsl' hcap' _ => by
      rw [huniq sl' ptr' badge' x'' y' g' gr' hsl' hcap']
      exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩)
    (Or.inl (G.node _)) (Or.inr (G.node _)) hr
  rw [hp] at hg
  -- its writes pass `StepOK`
  have hRq : RdEq st (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) :=
    ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ => rfl⟩
  have hPO : PreOK st (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) s (L.curW s) := by
    intro z b v hb _ _
    rw [L.write_eq]
    refine mguard_write (L.write_eq z b v) (hSO z b v ?_)
    rw [ecur, G.node, G.node] at hb
    exact hb
  have hM := vm_dec_m hRq hPO hr hn
  rw [hp] at hM
  have hWM := (interp_mguard _ s a r hM).2
  have hr' : interp st ar (R.syscall.handle_vm_fault_local addr code) s a = ok r := by rw [← hp]; exact hr
  exact ⟨r, hg, hWM, vm_fh_once hRal hR0 G rT rN eu F hFH hsl hcap hst hAo hr'⟩

set_option maxHeartbeats 1000000 in
/-- **The VM-fault body is `Safe` at an entry whose fault handler is another core's** (module docstring). -/
theorem vm_fh_safe {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hA : P0.ArchTotal ar) (addr code : U64) {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64}
    {σ : S} {a : A} (hc : L.cpu σ = c)
    {Rd Ro : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (rT : Rd (ctA (L := L) σ)) (rN : Rd (cnA (L := L) σ))
    (rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD))
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1)) (F : VmFhR st Rd σ s1)
    {sl ptr badge : U64} {x' y g gr : Bool}
    (hsl : obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl)
    (hcap : obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr))
    (hst : L.epState s1 ptr = obj.EP_RECV)
    (hAo : Ro (affA (L.mem s1 (epHeadA ptr))) ∧ ¬ User (affA (L.mem s1 (epHeadA ptr))))
    (hdA : Aligned (affA (L.mem s1 (epHeadA ptr)))) (hdR : Aligned (replyA (L.mem s1 (epHeadA ptr))))
    (hdT : affA (L.mem s1 (epHeadA ptr)) ≠ ctA (L := L) σ ∧ affA (L.mem s1 (epHeadA ptr)) ≠ cnA (L := L) σ)
    (hρd : ρ (affA (L.mem s1 (epHeadA ptr))) ≠ c)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hAPO : PO c hs (own μ (affA (L.mem s1 (epHeadA ptr)))))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hH : ∀ x, (x = ctA (L := L) σ ∨ x = cnA (L := L) σ) → HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v))) :
    Safe own cls kt c hs μ
      (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_vm_fault_local addr code) ∅ a) := by
  refine safe_tr_of_states hL hO hmk (Hp := fun x => x = ctA (L := L) σ ∨ x = cnA (L := L) σ) _ a hH hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_vm_fault_local addr code) ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  -- `s` agrees with `σ` on `Rd`
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu
    split_ifs
    · exact (hν.1 b (hRPO b hu hb)).trans (hρμ b (hRPO b hu hb)).symm
    · rfl
  have G : Ag st Rd σ s := ⟨sk, sc, fun b hb => by
    rw [hmem b (hRal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]; exact hRdρ b hb⟩
  -- the handler's `AFFINITY` carries `ρ`'s value, off the core
  have hoff : L.mem s (affA (L.mem s1 (epHeadA ptr))) ≠ c := by
    rw [hmem _ hdA]
    have e : (if affA (L.mem s1 (epHeadA ptr)) ∈ reads q ν then ν (affA (L.mem s1 (epHeadA ptr)))
        else ρ (affA (L.mem s1 (epHeadA ptr)))) = ρ (affA (L.mem s1 (epHeadA ptr))) := by
      split_ifs
      · exact (hν.1 _ hAPO).trans (hρμ _ hAPO).symm
      · rfl
    rw [e]; exact hρd
  obtain ⟨r, hg, hWM, hOnce⟩ := vm_fh_run hA addr code hc hRal hR0 rT rN rC eu F hsl hcap hst hAo hdA hdT hSO G hoff
  have hW := (interp_guard _ s a r hg).2
  refine ⟨s, fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => ?_) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨by rcases hx with rfl | rfl; exacts [hRal _ rT, hRal _ rN], fun _ => hx⟩,
    fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu hne hpo => hne ?_⟩
  · rcases hb with hb | rfl | rfl
    · exact hRal b hb
    · exact hdR
    · exact hdA
  · rw [hmem x hxa]
    split_ifs
    · exact hν.1 x hpo
    · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
