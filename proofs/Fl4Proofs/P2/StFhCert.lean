/-
# P2 (line p3mc, gen 18): the st body is `Safe` at an entry whose target is another core's

The decline split for `TCB_SetTimer` beside the gate (st), the counterpart of `SlFhCert.sl_fh_safe` (sl, U16) and
`RrFhSafe.rr_fh_safe` (vmR, U13). `handle_set_timer_local` reads the current thread (`CUR_THREAD`), the core, the
caller's `MSG_INFO` register and `FLAGS`, the current SC (`CUR_SC`), then `set_timer_target_ok` reads the target's
`AFFINITY` first and, when it is not the core, the path declines **having written nothing** (localtimer.rs: the
checks before `FAULT_IP` is written). So at an entry `σ` whose target's `AFFINITY` is, in the real memory `ρ`, not
the core, U9's certificate (`ViewSafeReal.safe_tr_of_states`) runs at a state `s` carrying `ν` on the tree's reads
and `ρ` elsewhere, which agrees with `σ` on the four words `StFhRd σ` and whose target `AFFINITY` is `ρ`'s:

* `stfh_bind`, `stfh_ite`, `stfh_ret`: transfer along a bind / an `if` keeping `r.1 = false`;
* **`st_fh_run`**: at any state where the target's `AFFINITY` is not the core, the run on any store answering the
  reads of `StFhRd`'s words and the target's `AFFINITY` as `st` is the run on `st`, and it declines;
* **`st_fh_safe`**: the function-level certificate (no write: `Hp := ∅`).

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.StFamC
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK)
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

section tools

theorem stfh_bind {α S A : Type} {m : Result α} {k k' : α → Result (Bool × S × A)} {y : Bool × S × A}
    (h2 : ∀ x, m = ok x → k x = ok y → k' x = ok y ∧ y.1 = false) :
    Std.bind m k = ok y → Std.bind m k' = ok y ∧ y.1 = false := fun h => by
  obtain ⟨x, e, hx⟩ := bind_eq_ok h
  rw [e]; simp only [bind_ok, bind_tc_ok]; exact h2 x e hx

theorem stfh_ite {S A : Type} {c : Prop} [Decidable c] {x z x' z' : Result (Bool × S × A)} {y : Bool × S × A}
    (h1 : c → x = ok y → x' = ok y ∧ y.1 = false) (h2 : ¬ c → z = ok y → z' = ok y ∧ y.1 = false) :
    (if c then x else z) = ok y → (if c then x' else z') = ok y ∧ y.1 = false := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]; exact h1 hc
  · rw [if_neg hc, if_neg hc]; exact h2 hc

theorem stfh_ret {S A : Type} {s : S} {a : A} {r : Bool × S × A} :
    ok (false, s, a) = ok r → ok (false, s, a) = ok r ∧ r.1 = false := fun h =>
  ⟨h, by rw [← ok_inj_ff h]⟩

end tools

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

/-- The four words the st body reads before the target's `AFFINITY` (module docstring). -/
def StFhRd (σ : S) (b : U64) : Prop :=
  b = L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD ∨ b = regA (L.curW σ) layout.reg.MSG_INFO ∨
    b = core.num.U64.wrapping_add (L.curW σ) 3456#u64 ∨ b = L.nodeAt σ (L.cpu σ) layout.node.CUR_SC

set_option maxHeartbeats 4000000 in
/-- **A run whose target is off the core declines, on any store answering its reads** (module docstring). -/
theorem st_fh_run {gS : machine.Store S} {R : U64 → Prop} [GRd gS st R] {s : S} {a : A} {n : I64}
    {target : U64} {r : Bool × S × A}
    (h1 : R (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD)) (h2 : R (regA (L.curW s) layout.reg.MSG_INFO))
    (h3 : R (core.num.U64.wrapping_add (L.curW s) 3456#u64)) (h4 : R (L.nodeAt s (L.cpu s) layout.node.CUR_SC))
    (h5 : R (affA target)) (hoff : L.mem s (affA target) ≠ L.cpu s)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok r) :
    localtimer.handle_set_timer_local gS ar s a n target = ok r ∧ r.1 = false := by
  have hne : (L.mem s (affA target) != L.cpu s) = true := by simpa using hoff
  have ht : localtimer.set_timer_target_ok st s (L.cpu s) target = ok false := by
    unfold localtimer.set_timer_target_ok
    rw [aff_ok]
    simp only [bind_ok, bind_tc_ok]
    rw [if_pos hne]
  have ht' : localtimer.set_timer_target_ok gS s (L.cpu s) target = ok false := by
    unfold localtimer.set_timer_target_ok
    rw [PathObl.obj.Tcb.affinity.guard (gS := gS) target s h5, aff_ok]
    simp only [bind_ok, bind_tc_ok]
    rw [if_pos hne]
  revert h
  unfold localtimer.handle_set_timer_local
  rw [PathObl.sched.cur_thread.guard (gS := gS) s h1, cur_thread_ok, gst_cur_cpu (g := gS), L.cur_cpu_eq]
  simp only [bind_ok, lift]
  rw [PathObl.msg.msg_info.guard (gS := gS) s _ h2]
  refine stfh_bind (fun info _ => ?_)
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine stfh_ite (fun _ => stfh_ret) (fun _ => ?_)
  rw [PathObl.obj.Tcb.flags.guard (gS := gS) _ s h3]
  refine stfh_bind (fun i _ => ?_)
  refine stfh_ite (fun _ => stfh_ret) (fun _ => ?_)
  refine stfh_ite (fun _ => stfh_ret) (fun _ => ?_)
  refine stfh_ite (fun _ => stfh_ret) (fun _ => ?_)
  refine stfh_ite (fun _ => stfh_ret) (fun _ => ?_)
  rw [PathObl.sched.cur_sc.guard (gS := gS) s h4]
  refine stfh_bind (fun csc _ => ?_)
  rw [ht, ht']
  simp only [bind_ok, bind_tc_ok, Bool.false_eq_true, ↓reduceIte]
  exact stfh_ret

set_option maxHeartbeats 4000000 in
/-- **The st body is `Safe` at an entry whose target is another core's** (module docstring). -/
theorem st_fh_safe {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hA : P0.ArchTotal ar) {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} {n : I64}
    {target : U64} (hc : L.cpu σ = c) {Ro : U64 → Prop}
    (hal : ∀ b, StFhRd (L := L) σ b → Aligned b) (haA : Aligned (affA target))
    (hR0 : ∀ q, StFhRd (L := L) σ q → Ro q ∧ ¬ User q) (hgo : Ro (affA target) ∧ ¬ User (affA target))
    (hρd : ρ (affA target) ≠ c)
    (hRdρ : ∀ b, StFhRd (L := L) σ b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x) :
    Safe own cls kt c hs μ
      (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.localtimer.handle_set_timer_local n target) ∅ a) := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localtimer.handle_set_timer_local mm ar x a n target =
        interp mm ar (R.localtimer.handle_set_timer_local n target) x a :=
    fun mm x a => congrFun (congrFun (st_isProg S n target A ar mm) x) a
  let R'' : U64 → Prop := fun b => StFhRd (L := L) σ b ∨ b = affA target
  have hR''al : ∀ b, R'' b → Aligned b := by
    rintro b (hb | rfl)
    · exact hal b hb
    · exact haA
  refine safe_tr_of_states hL hO hmk (Hp := fun _ => False) _ a (fun x hx => hx.elim) hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar
    (R.localtimer.handle_set_timer_local n target) ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have hag : ∀ b, StFhRd (L := L) σ b → L.mem s b = L.mem σ b := fun b hb => by
    rw [hmem b (hal b hb), eR b (hR0 b hb).1 (hR0 b hb).2]; exact hRdρ b hb
  have eN : ∀ o, L.nodeAt s (L.cpu s) o = L.nodeAt σ (L.cpu σ) o := fun o => by
    rw [sc]; exact nodeAt_of_ksb sk _ o
  have hcur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW
    rw [eN]
    exact hag _ (Or.inl rfl)
  have hoff : L.mem s (affA target) ≠ L.cpu s := by
    rw [hmem _ haA, eR _ hgo.1 hgo.2, sc, hc]; exact hρd
  have r1 : R'' (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := Or.inl (Or.inl (eN _))
  have r2 : R'' (regA (L.curW s) layout.reg.MSG_INFO) := Or.inl (Or.inr (Or.inl (by rw [hcur])))
  have r3 : R'' (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    Or.inl (Or.inr (Or.inr (Or.inl (by rw [hcur]))))
  have r4 : R'' (L.nodeAt s (L.cpu s) layout.node.CUR_SC) := Or.inl (Or.inr (Or.inr (Or.inr (eN _))))
  have r5 : R'' (affA target) := Or.inr rfl
  obtain ⟨r, hr, -⟩ :=
    spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st ar s a n target LawfulStore.total hA)
  have hg := (st_fh_run ar (gS := PathObl.guard st R'' (fun _ => False)) r1 r2 r3 r4 r5 hoff hr).1
  rw [hp] at hg
  have hW := (interp_guard _ s a r hg).2
  have hM : localtimer.handle_set_timer_local
      (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) ar s a n target = ok r := by
    haveI iR : GRd (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) st (fun _ => True) :=
      { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    exact (st_fh_run ar (R := fun _ => True) trivial trivial trivial trivial trivial hoff hr).1
  rw [hp] at hM
  have hWM := (interp_mguard _ s a r hM).2
  have hO1 := once_of_guardG (R := R'') (W := fun _ => False) (User := User)
    (fun q hq => hq.elim (fun h => (hR0 q h).2) (fun e => by subst e; exact hgo.2)) _
    (st_noZero n target) ∅ ∅ s a r hg
  have hOnce := once_monoR (R := R'') (R' := Ro) (User := User)
    (fun b hb => hb.elim (fun h => (hR0 b h).1) (fun e => by subst e; exact hgo.1)) _ ∅ ∅ ∅ s a hO1
    (fun _ h => h)
  refine ⟨s, fun _ => False, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hR''al b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => hx.elim, fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
