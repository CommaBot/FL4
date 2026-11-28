/-
# P2 (line p3mc, gen 13): the VM ReplyRecv body is `Safe` at an entry whose receiver is another core's

The decline split for vmR at the function level (the counterpart of `VmFhSafe.vm_fh_safe`): at an entry `σ` (any
store state; no `Pre` beyond the facts below) whose reply object names a receiver `u ≠ 0` with
`ρ (AFFINITY u) ≠ c`, the translation `tr Ro … (R.syscall.handle_reply_recv_vm_local (rptr, ep)) ∅ a` is `Safe` at
the physical memory `μ`. `ViewSafeReal.safe_tr_of_states`: for each admissible `ν` the certificate state `s` carries
`ν` on the tree's reads and `ρ` elsewhere; it agrees with `σ` on `Rd`, so its dispatch state has `σ`'s `RrDR0`
facts (`RrDR0.alt`) and sees `u` off the core (`u`'s `AFFINITY` is `ρ`'s); then `rr_fh_not_acc` (not accepted),
`rr_local_guard_dec` (the declined run on the guarded store, and on `mguard` for `StepOK` of the three prefix
writes) and `rr_fh_once` (`u`'s `STATE` / `FAULT_TYPE` read once).

* **`rr_fh_safe`**; gen 49 (in place, its statement unchanged): **`rr_fh_run`**, the run from one store state, split
  out of its proof (shared with its `InsA` twin, P2/InsV15Fh).

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.RrFh
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

set_option maxHeartbeats 2000000 in
/-- **The VM ReplyRecv body's run from one store state whose receiver is another core's** (split out of
`rr_fh_safe`'s proof in place, gen 49): at a state `s` agreeing with `σ` on `Rd` (core and kernel base included) and
seeing the receiver's `AFFINITY` off its core, the run declines on the guard of `rr_fh_safe`'s certificate, its
writes pass `StepOK`, and it reads each racy word once. -/
theorem rr_fh_run {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hA : P0.ArchTotal ar) {rptr ep : U64} {c : U64}
    {hs : U64 → Prop} {σ : S} {a : A} (hc : L.cpu σ = c)
    {Rd Ro : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (ndσ : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o))
    (rF : Rd (regA (L.curW σ) layout.reg.FAULT_IP)) (rNI : Rd (regA (L.curW σ) layout.reg.NEXT_IP))
    (rFl : Rd (core.num.U64.wrapping_add (L.curW σ) 3456#u64))
    (hmidσ : ∀ v X a2,
      sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2) →
      RdHead (L := L) Rd X (L.cscW X) ∧ RrDR0 (L := L) Rd X (L.curW σ) rptr ep ∧
        L.mem X (rTcbA rptr) = L.mem σ (rTcbA rptr))
    (hex : ∀ v, ∃ X a2, sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2))
    (hu0 : L.mem σ (rTcbA rptr) ≠ 0#u64)
    (hgo : ∀ b, (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
        b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr))) →
      Ro b ∧ ¬ User b ∧ Aligned b)
    (huW : affA (L.mem σ (rTcbA rptr)) ≠ regA (L.curW σ) layout.reg.FAULT_IP ∧
      affA (L.mem σ (rTcbA rptr)) ≠ ctA (L := L) σ ∧ affA (L.mem σ (rTcbA rptr)) ≠ cnA (L := L) σ)
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v)))
    {s : S} (G : Ag st Rd σ s) (hoff : L.mem s (affA (L.mem σ (rTcbA rptr))) ≠ c) :
    ∃ r, interp (guard st (fun b => (Rd b ∨ (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
          b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr)))) ∨
          b = stA (L.mem σ (rTcbA rptr)) ∨ b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64)
        (fun b => b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ)) ar
        (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s a = ok r ∧
      WithinM st ar (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))
        (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s a ∧
      Once st ar Ro User ∅ ∅ (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s a := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local mm ar x a (rptr, ep) =
        interp mm ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) x a :=
    fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a
  -- the receiver and its words
  generalize hu : L.mem σ (rTcbA rptr) = u at hu0 hgo huW hoff ⊢
  let Wσ : U64 → Prop := fun b => b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ
  let Rd' : U64 → Prop := fun b => Rd b ∨ (b = scA u ∨ b = affA u ∨ b = core.num.U64.wrapping_add u 3432#u64 ∨
    b = prioA u)
  let R'' : U64 → Prop := fun b => Rd' b ∨ b = stA u ∨ b = core.num.U64.wrapping_add u 3376#u64
  have hR0' : ∀ q, Rd' q → Ro q ∧ ¬ User q := by
    intro q hq
    rcases hq with hq | hq
    · exact hR0 q hq
    · exact ⟨(hgo q hq).1, (hgo q hq).2.1⟩
  have rT : Rd (ctA (L := L) σ) := ndσ _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN : Rd (cnA (L := L) σ) := ndσ _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
    ndσ _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have sc : L.cpu s = L.cpu σ := G.c
  have ecur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ rC
  have eT : ctA (L := L) s = ctA (L := L) σ := G.node _
  have eN : cnA (L := L) s = cnA (L := L) σ := G.node _
  have aF : Aligned (regA (L.curW σ) layout.reg.FAULT_IP) := hRal _ rF
  -- the facts at `s`'s dispatch states
  have hmid : ∀ v X2 a2,
      sched.update_timestamp st ar (L.wr s (regA (L.curW s) layout.reg.FAULT_IP) v) a = ok (X2, a2) →
      (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd' (L.nodeAt X2 (L.cpu X2) o)) ∧
        RdHead (L := L) Rd' X2 (L.cscW X2) ∧ RrDR (L := L) Rd' X2 (L.curW s) rptr ep ∧
        L.mem X2 (rTcbA rptr) = u ∧ L.mem X2 (affA u) ≠ L.cpu X2 := by
    intro v X2 a2 eu'
    rw [ecur] at eu' ⊢
    obtain ⟨X, a2', eu⟩ := hex v
    have G0 : Ag st Rd (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v)
        (L.wr s (regA (L.curW σ) layout.reg.FAULT_IP) v) := G.wr hRal aF
    obtain ⟨-, G1⟩ := vm_ag_upd hRal G0 (by rw [ctA_wr]; exact rT) (by rw [cnA_wr]; exact rN) eu eu'
    obtain ⟨hsX, D0, eRt⟩ := hmidσ v X a2' eu
    have eRt2 : L.mem X2 (rTcbA rptr) = u := by rw [G1.m _ D0.rRt, eRt, hu]
    have hoffu : L.mem X2 (affA u) ≠ L.cpu X2 := by
      obtain ⟨now, -, ex⟩ := upd_eq eu'
      have hTa : Aligned (ctA (L := L) (L.wr s (regA (L.curW σ) layout.reg.FAULT_IP) v)) := by
        rw [ctA_wr, eT]; exact hRal _ rT
      have hNa : Aligned (cnA (L := L) (L.wr s (regA (L.curW σ) layout.reg.FAULT_IP) v)) := by
        rw [cnA_wr, eN]; exact hRal _ rN
      have hdA : Aligned (affA u) := (hgo _ (Or.inr (Or.inl rfl))).2.2
      rw [ex, L.cpu_wr, L.cpu_wr, L.cpu_wr, sc, hc]
      rw [L.mem_wr _ _ _ _ hNa hdA, if_neg (by rw [cnA_wr, eN]; exact fun h => huW.2.2 h.symm),
        L.mem_wr _ _ _ _ hTa hdA, if_neg (by rw [ctA_wr, eT]; exact fun h => huW.2.1 h.symm),
        L.mem_wr _ _ _ _ aF hdA, if_neg (fun h => huW.1 h.symm)]
      exact hoff
    have ecsc : L.cscW X2 = L.cscW X := by
      unfold LawfulStore.cscW LawfulStore.nodeA
      rw [G1.node]; exact G1.m _ (D0.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
    refine ⟨fun o ho h8 => by rw [G1.node]; exact Or.inl (D0.nd o ho h8), ?_, ?_, eRt2, hoffu⟩
    · rw [ecsc]
      have h3 := G1.rdHead hsX
      unfold RdHead at h3 ⊢
      exact ⟨Or.inl h3.1, Or.inl h3.2.1, Or.inl h3.2.2⟩
    · refine RrDR.ofOff (D0.alt G1 (fun b hb => Or.inl hb)) (fun u' hu' _ => ?_) (fun u' hu' _ => ?_)
      · rw [eRt2] at hu'; subst hu'
        exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr (Or.inl rfl))),
          Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
      · rw [eRt2] at hu'; subst hu'; exact hoffu
  have hoff : RrOff st ar s a rptr := by
    intro v X2 a2 eu' u' hu' _
    obtain ⟨-, -, -, e1, e2⟩ := hmid v X2 a2 eu'
    rw [e1] at hu'; subst hu'; exact e2
  -- the run declines, guarded
  obtain ⟨r, hr⟩ := rr_total (st := st) hA (rptr, ep) s a
  have hn : r.1 ≠ true := by
    obtain ⟨b0, z, c0⟩ := r
    intro hb
    change b0 = true at hb
    subst hb
    exact rr_fh_not_acc hoff hr
  have hct'' : R'' (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := by rw [G.node]; exact Or.inl (Or.inl rC)
  have hfl'' : R'' (core.num.U64.wrapping_add (L.curW s) 3456#u64) := by rw [ecur]; exact Or.inl (Or.inl rFl)
  have hni'' : R'' (regA (L.curW s) layout.reg.NEXT_IP) := by rw [ecur]; exact Or.inl (Or.inl rNI)
  have hfiW : Wσ (regA (L.curW s) layout.reg.FAULT_IP) := by rw [ecur]; exact Or.inl rfl
  have hg : syscall.handle_reply_recv_vm_local (PathObl.guard st R'' Wσ) ar s a (rptr, ep) = ok r := by
    refine rr_local_guard_dec (gS := PathObl.guard st R'' Wσ) hct'' hfl'' hni'' hfiW
      ⟨by rw [eT]; exact Or.inl (Or.inl rT), by rw [eT]; exact Or.inr (Or.inl rfl),
        by rw [eN]; exact Or.inl (Or.inl rN), by rw [eN]; exact Or.inr (Or.inr rfl)⟩ ?_ hr hn
    intro v X2 a2 eu'
    obtain ⟨nd2, hs2, D2, e1, e2⟩ := hmid v X2 a2 eu'
    refine ⟨Or.inl (nd2 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])),
      Or.inl (nd2 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])), ?_,
      D2.alt (G := ⟨rfl, rfl, fun _ _ => rfl⟩) (fun b hb => Or.inl hb), fun u' hu' _ _ => ?_⟩
    · unfold RdHead at hs2 ⊢
      exact ⟨Or.inl hs2.1, Or.inl hs2.2.1, Or.inl hs2.2.2⟩
    · rw [e1] at hu'; subst hu'
      exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  rw [hp] at hg
  have hW := (interp_guard _ s a r hg).2
  -- its writes pass `StepOK`
  have hM : syscall.handle_reply_recv_vm_local
      (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) ar s a (rptr, ep) = ok r := by
    haveI iR : GRd (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) st (fun _ => True) :=
      { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    haveI iW : GWr (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) st Wσ :=
      { write := fun {b} hb y v => by
          rw [L.write_eq]
          exact mguard_write (L.write_eq y b v) (hSO y b v hb)
        ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    refine rr_local_guard_dec (R := fun _ => True) (W := Wσ) trivial trivial trivial hfiW
      ⟨trivial, by rw [eT]; exact Or.inr (Or.inl rfl), trivial, by rw [eN]; exact Or.inr (Or.inr rfl)⟩ ?_ hr hn
    intro v X2 a2 _
    exact ⟨trivial, trivial, rdHead_top X2 _, RrDR.top X2 _ _ _, fun _ _ _ _ => ⟨trivial, trivial⟩⟩
  rw [hp] at hM
  have hWM := (interp_mguard _ s a r hM).2
  have hr' : interp st ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) s a = ok r := by rw [← hp]; exact hr
  have hOnce := rr_fh_once (Rd := Rd') (Ro := Ro) (User := User) hR0' (x := s) (a := a) (rptr := rptr) (ep := ep)
    (by rw [G.node]; exact Or.inl rC) (by rw [eT]; exact Or.inl rT) (by rw [eN]; exact Or.inl rN)
    (by rw [ecur]; exact Or.inl rF) (by rw [ecur]; exact Or.inl rNI) (by rw [ecur]; exact Or.inl rFl)
    (fun v X2 a2 eu' => by
      obtain ⟨nd2, hs2, D2, e1, e2⟩ := hmid v X2 a2 eu'
      exact ⟨nd2, hs2, D2, fun u' hu' _ => by rw [e1] at hu'; subst hu'; exact e2⟩) hr'
  exact ⟨r, hg, hWM, hOnce⟩

set_option maxHeartbeats 2000000 in
/-- **The VM ReplyRecv body is `Safe` at an entry whose receiver is another core's** (module docstring). -/
theorem rr_fh_safe {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hA : P0.ArchTotal ar) {rptr ep : U64} {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64}
    {σ : S} {a : A} (hc : L.cpu σ = c)
    {Rd Ro : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (ndσ : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o))
    (rF : Rd (regA (L.curW σ) layout.reg.FAULT_IP)) (rNI : Rd (regA (L.curW σ) layout.reg.NEXT_IP))
    (rFl : Rd (core.num.U64.wrapping_add (L.curW σ) 3456#u64))
    (hmidσ : ∀ v X a2,
      sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2) →
      RdHead (L := L) Rd X (L.cscW X) ∧ RrDR0 (L := L) Rd X (L.curW σ) rptr ep ∧
        L.mem X (rTcbA rptr) = L.mem σ (rTcbA rptr))
    (hex : ∀ v, ∃ X a2, sched.update_timestamp st ar (L.wr σ (regA (L.curW σ) layout.reg.FAULT_IP) v) a = ok (X, a2))
    (hu0 : L.mem σ (rTcbA rptr) ≠ 0#u64)
    (hgo : ∀ b, (b = scA (L.mem σ (rTcbA rptr)) ∨ b = affA (L.mem σ (rTcbA rptr)) ∨
        b = core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3432#u64 ∨ b = prioA (L.mem σ (rTcbA rptr))) →
      Ro b ∧ ¬ User b ∧ Aligned b)
    (haS : Aligned (stA (L.mem σ (rTcbA rptr))))
    (haF : Aligned (core.num.U64.wrapping_add (L.mem σ (rTcbA rptr)) 3376#u64))
    (huW : affA (L.mem σ (rTcbA rptr)) ≠ regA (L.curW σ) layout.reg.FAULT_IP ∧
      affA (L.mem σ (rTcbA rptr)) ≠ ctA (L := L) σ ∧ affA (L.mem σ (rTcbA rptr)) ≠ cnA (L := L) σ)
    (hρu : ρ (affA (L.mem σ (rTcbA rptr))) ≠ c)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hH : ∀ x, (x = regA (L.curW σ) layout.reg.FAULT_IP ∨ x = ctA (L := L) σ ∨ x = cnA (L := L) σ) →
      HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v))) :
    Safe own cls kt c hs μ
      (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) ∅ a) := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local mm ar x a (rptr, ep) =
        interp mm ar (R.syscall.handle_reply_recv_vm_local (rptr, ep)) x a :=
    fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a
  -- the receiver and its words
  generalize hu : L.mem σ (rTcbA rptr) = u at hu0 hgo haS haF huW hρu
  let Wσ : U64 → Prop := fun b => b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ
  let Rd' : U64 → Prop := fun b => Rd b ∨ (b = scA u ∨ b = affA u ∨ b = core.num.U64.wrapping_add u 3432#u64 ∨
    b = prioA u)
  let R'' : U64 → Prop := fun b => Rd' b ∨ b = stA u ∨ b = core.num.U64.wrapping_add u 3376#u64
  have hR0' : ∀ q, Rd' q → Ro q ∧ ¬ User q := by
    intro q hq
    rcases hq with hq | hq
    · exact hR0 q hq
    · exact ⟨(hgo q hq).1, (hgo q hq).2.1⟩
  have hR''al : ∀ b, R'' b → Aligned b := by
    intro b hb
    rcases hb with (hb | hb) | rfl | rfl
    · exact hRal b hb
    · exact (hgo b hb).2.2
    · exact haS
    · exact haF
  have rT : Rd (ctA (L := L) σ) := ndσ _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN : Rd (cnA (L := L) σ) := ndσ _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
    ndσ _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  refine safe_tr_of_states hL hO hmk (Hp := Wσ) _ a hH hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar
    (R.syscall.handle_reply_recv_vm_local (rptr, ep)) ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have G : Ag st Rd σ s := ⟨sk, sc, fun b hb => by
    rw [hmem b (hRal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]; exact hRdρ b hb⟩
  have ecur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW; rw [G.node]; exact G.m _ rC
  have eT : ctA (L := L) s = ctA (L := L) σ := G.node _
  have eN : cnA (L := L) s = cnA (L := L) σ := G.node _
  have aF : Aligned (regA (L.curW σ) layout.reg.FAULT_IP) := hRal _ rF
  have hoff : L.mem s (affA u) ≠ c := by
    rw [hmem _ (hgo _ (Or.inr (Or.inl rfl))).2.2]
    rw [eR _ (hgo _ (Or.inr (Or.inl rfl))).1 (hgo _ (Or.inr (Or.inl rfl))).2.1]
    exact hρu
  subst hu
  obtain ⟨r, hg, hWM, hOnce⟩ := rr_fh_run hA hc hRal hR0 ndσ rF rNI rFl hmidσ hex hu0 hgo huW hSO G hoff
  have hW := (interp_guard _ s a r hg).2
  refine ⟨s, Wσ, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hR''al b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨by rcases hx with rfl | rfl | rfl; exacts [aF, hRal _ rT, hRal _ rN], fun _ => hx⟩,
    fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
