/-
# P2 (line p3mc, gen 47): `InsV15N` [J] at the st starts whose target is another core's

The st slot's armed program at a view start whose target's `AFFINITY` is, in `ρ`, not `c` (U17's `StFhAt`) declines
at `set_timer_target_ok`'s first read, writing nothing (P2/StFhCert `st_fh_run`). So it is `InsA` at the physical
memory by the decline certificate `PathObl.insA_tr_dec` (P2/InsV15Vx), the read set being U17's.

* **`PathObl.st_fh_insA`**: the `InsA` counterpart of `st_fh_safe` (read set: the four `StFhRd` words and the target's
  `AFFINITY`, each off `G`).
* `epochPteN_view_of`: at a view start with no VCPU, the A/D epoch invariant `EpochJV` gives `EpochPteN` of the view
  (as in `execV15_aRunD`: `epoch_start`, `epochPteN_of`, `epochPteN_view`) — `startAt_stC` needs it.
* **`st_fh_insA_annV`**: the read set is P2/StFhView's (`st_fh_rd`, `st_fh_aff`, split out of `st_fh_annV` in place this
  generation, statement unchanged): in `MaxR`, no PTE word, region-tagged, hence no paging word of the epoch.
* **`st_k0_insA`** (glue: P2/E2EPU17's `st_k0_data`, split out of `st_k0_fhC` in place, shared), **`st_insA_annV_fh`**
  (at an `StFhAt` index: `stC_glue` gives no VCPU, so `epochPteN_view_of` and `startAt_stC` apply),
  **`insAP_stF_view`**: `InsV15N`'s obligation of `nativePmKAD B` at those starts (`StFPm c ρ i`).

No named premise. Existing files touched: P2/StFhView (`st_fh_rd`, `st_fh_aff` split out of `st_fh_annV`),
P2/E2EPU17 (`st_k0_data` split out of `st_k0_fhC`); every existing statement byte-identical.
-/
import Fl4Proofs.P2.InsV15Vx
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once tr reads exists_mem_state OwnDep MasksWr masksOf masksOf_eq InsT insT_of_within)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm InsA narrowSP)

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **The declining st body (target off the core) is `InsA` in its re-annotated form** (module docstring). -/
theorem st_fh_insA {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt kv : U64 → ClsOwner U64} {User : U64 → Prop} {G : U64 → Prop} {Q : U64 → U64 → Prop} {NP : U64 → Prop}
    (hQ : Equivalence Q) (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hGo : ∀ m m' : U64 → U64, (∀ x, ¬ G x → m x = m' x) → own m = own m') (hGko : ∀ x, G x → kt x = .free)
    (hGU : ∀ b, G b → ¬ User b) (hA : P0.ArchTotal ar)
    {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} {σ : S} {a : A} {n : I64} {target : U64}
    (hc : L.cpu σ = c) {R0 Qv : U64 → Prop} (hGQ : ∀ b, G b → Qv b)
    (hal : ∀ b, StFhRd (L := L) σ b → Aligned b) (haA : Aligned (affA target))
    (hR0 : ∀ q, StFhRd (L := L) σ q → (R0 q ∧ Qv q) ∧ ¬ User q)
    (hgo : (R0 (affA target) ∧ Qv (affA target)) ∧ ¬ User (affA target))
    (hRdG : ∀ b, StFhRd (L := L) σ b → ¬ G b) (hAG : ¬ G (affA target))
    (hρd : ρ (affA target) ≠ c)
    (hRdρ : ∀ b, StFhRd (L := L) σ b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → (R0 x ∧ Qv x) → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x) :
    InsA G Q NP own cls kt c hs μ
      (narrowSP cls kt c Qv ∅
        (tr R0 User cls kv c (L.ksb σ) (masksOf st σ) ar (R.localtimer.handle_set_timer_local n target) ∅ a)) := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      localtimer.handle_set_timer_local mm ar x a n target =
        interp mm ar (R.localtimer.handle_set_timer_local n target) x a :=
    fun mm x a => congrFun (congrFun (st_isProg S n target A ar mm) x) a
  refine insA_tr_dec ar hQ hL hO hmk hGo hGko hGU _ (st_noZero n target) hc hGQ
    (Rd := fun b => StFhRd (L := L) σ b ∨ b = affA target)
    (by rintro b (hb | rfl); exacts [hal b hb, haA])
    (by rintro q (hq | rfl); exacts [hR0 q hq, hgo])
    (by rintro b (hb | rfl); exacts [hRdG b hb, hAG]) hRPO hρμ ?_
  intro s sc sk hag gS Rg iR hR
  have hag' : ∀ b, StFhRd (L := L) σ b → L.mem s b = L.mem σ b := fun b hb =>
    (hag b (Or.inl hb)).trans (hRdρ b hb)
  have eN : ∀ o, L.nodeAt s (L.cpu s) o = L.nodeAt σ (L.cpu σ) o := fun o => by
    rw [sc]; exact nodeAt_of_ksb sk _ o
  have hcur : L.curW s = L.curW σ := by
    unfold LawfulStore.curW
    rw [eN]
    exact hag' _ (Or.inl rfl)
  have hoff : L.mem s (affA target) ≠ L.cpu s := by
    rw [hag _ (Or.inr rfl), sc, hc]; exact hρd
  have r1 : Rg (L.nodeAt s (L.cpu s) layout.node.CUR_THREAD) := hR _ (Or.inl (Or.inl (eN _)))
  have r2 : Rg (regA (L.curW s) layout.reg.MSG_INFO) := hR _ (Or.inl (Or.inr (Or.inl (by rw [hcur]))))
  have r3 : Rg (core.num.U64.wrapping_add (L.curW s) 3456#u64) :=
    hR _ (Or.inl (Or.inr (Or.inr (Or.inl (by rw [hcur])))))
  have r4 : Rg (L.nodeAt s (L.cpu s) layout.node.CUR_SC) := hR _ (Or.inl (Or.inr (Or.inr (Or.inr (eN _)))))
  have r5 : Rg (affA target) := hR _ (Or.inr rfl)
  obtain ⟨r, hr, -⟩ :=
    spec_ex_fd (P0.localtimer.handle_set_timer_local.p0 st ar s a n target LawfulStore.total hA)
  have hg := (st_fh_run ar (gS := gS) r1 r2 r3 r4 r5 hoff hr).1
  rw [hp] at hg
  exact ⟨r, hg⟩

end

end
end Fl4Proofs.P2.PathObl

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW GateField tcbOwner)
open Fl4Proofs.P2.E2E (StartAt SP LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg VEq Safe narrowSP PO HeldV InsA InsAP insAP_of_insA)
open Fl4Proofs.P2.CoreView (view)
open Fl4Proofs.P2.MmuAD (MmuAD ADEq NotPresent adEq_equiv)

noncomputable section
open Classical

/-- **At a view start with no VCPU, the A/D epoch invariant gives `EpochPteN` of the view** (as in
`execV15_aRunD`). -/
theorem epochPteN_view_of {K : KLayoutP} {E : U64 → U64} {s : Cfg U64 U64 U64 U64} {c : U64} {ρ : U64 → U64}
    (J : EpochJV K E s) (nv : K.vcpus = ∅) (hM : MapsP K s)
    (hVq : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem) :
    EpochPteN K (CoreView.view K.toKLayout c ρ) := by
  obtain ⟨e1, hCe, hk1⟩ := epoch_start (J.toJ nv)
  have hρg : ∀ x, GateW K x → ρ x = e1.mem x := fun x hx =>
    (hVq.2.1 x (by rw [hM.own, hx s.mem]; exact Or.inr rfl)).trans (hk1 x hx)
  exact epochPteN_view c (epochPteN_of ⟨e1, hCe, hρg⟩)

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)

set_option maxHeartbeats 4000000 in
/-- **U9's armed st program is `InsA` at a view start whose target is another core's** (module docstring). -/
theorem st_fh_insA_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) {c : U64} {hs : U64 → Prop} {ρ μ : U64 → U64} (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {lk : S → U64 → Prop} {Cs Ω Sg Ac : Set U64} {n : I64} {target : U64} {σ : S} {a : A}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (E : StEnt (userV K.toKLayoutV) st K.toKLayoutV.heap.tcbs Cs Ω K.toKLayoutV.heap Sg K.toKLayoutV.heap.replies
      K.toKLayoutV.heap.scs K.toKLayoutV.heap.ntfns K.toKLayoutV.heap.scBits Ac target σ)
    (hc : L.cpu σ = c) (hl : lk σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hρ : ρ (affA target) ≠ c) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.localtimer.handle_set_timer_local n target) ∅ a)) := by
  have W0 := st_fh_rd (lk := lk) hK hJ E hc hmm
  have hAf := st_fh_aff (lk := lk) (c := c) (ρ := ρ) hK nv hJ E
  have hR0 : ∀ q, StFhRd (L := L) σ q →
      (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ q ∧ VO K c ρ q) ∧ q ∉ K.user := fun q hq =>
    ⟨⟨⟨(W0 q hq).1.1, (W0 q hq).1.2.2⟩, (W0 q hq).1.2.1.2⟩,
      fun hu => (W0 q hq).1.1.2.2 (mem_userV.2 (Or.inl hu))⟩
  have hRdρ : ∀ b, StFhRd (L := L) σ b → ρ b = L.mem σ b := fun b hb =>
    (W0 b hb).1.2.1.1.symm.trans
      (hmm b (W0 b hb).1.1.2.1 (fun hu => (W0 b hb).1.1.2.2 (mem_userV.2 (Or.inl hu)))).symm
  have hRdG : ∀ b, StFhRd (L := L) σ b → ¬ PWE K E' b := fun b hb hp => by
    rcases hp with hp | hp
    · exact (W0 b hb).1.2.2 hp
    · exact (W0 b hb).2 hp.2.2.1
  have hAG : ¬ PWE K E' (affA target) := fun hp => by
    rcases hp with hp | hp
    · exact hAf.1.2 hp
    · exact hAf.2.2.2 hp.2.2.1
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st lk) σ x ∧ VO K c ρ x) →
      PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm hx.1.1.1
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  exact PathObl.st_fh_insA (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) ar adEq_equiv (moveHeldP hK) (ownDepP hK hU) hmk (pwe_own hK)
    (fun x hx => pwe_ko hK μ hx) (fun b hb => pwe_user hU hb) hA (n := n) (a := a) hc
    (fun b hb => vo_of_pwe hK hb) (fun b hb => (W0 b hb).1.1.2.1) hAf.1.1.2.1 hR0
    ⟨⟨hAf.1, hAf.2.1⟩, hAf.2.2.1⟩ hRdG hAG hρ hRdρ hRPO (fun x hx => hV.2.1 x hx)

end main

section body
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)

/-- **The st body is `InsA` at every view start whose target is another core's** (glue: U17's `st_k0_data`). -/
theorem st_k0_insA (j : StArg S) (K : KLayoutP) (hK : RegionOKP K) (hU : UserOKP K) (c : U64)
    (hs : U64 → Prop) (ρ μ : U64 → U64) (k0 : SP) (E' : U64 → U64)
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    (hF : ρ (fld j.target oAFFINITY) ≠ c)
    (hS : StartAt (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0 (.st j) K (view K.toKLayout c ρ) hK hU)
      c hs (view K.toKLayout c ρ) k0) :
    InsA (PWE K E') ADEq NotPresent (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅ k0) := by
  obtain ⟨σ, a, Cs, Ω, Sg, Ac, nv, hJ', E, hc', hl', hmm, rfl⟩ := st_k0_data st ar hA a0 j K hK hU c hs ρ k0 hS
  exact st_fh_insA_annV ar hA (masksWr_plain st) hK hU nv E' hV (lk := j.lk) (n := j.n) (a := a) hJ' E hc'
    hl' hmm (by rw [OwnMap.affA_fld]; exact hF)

end body

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

set_option maxHeartbeats 4000000 in
/-- **U9's re-annotated body is `InsA` at every st start whose target is another core's** (module docstring). -/
theorem st_insA_annV_fh {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)} (E : U64 → U64)
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : StFhAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    InsA (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with ((j | j | j | j | j | j | j) | j)
  · exact False.elim hf
  · exact False.elim hf
  · exact False.elim hf
  · have h' : StartU2C st ar hA a0 arI AR MR Ch K (view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k
        (.st j) := hsf
    obtain ⟨_, ⟨hR, -⟩, -⟩ := stC_glue st ar hA a0 h'
    have hpr : K.toKLayoutV.vcpus = ∅ ∧ StPremK2B st j K.toKLayoutV (view K.toKLayout c ρ) := hR
    have hE := epochPteN_view_of J hpr.1 hM hV
    have hS := startAt_stC st ar hA a0 (s := { s with mem := CoreView.view K.toKLayout c ρ }) hC hE h'
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    exact st_k0_insA st ar hA a0 j K hK hU c _ ρ s.mem k E hV hf hS
  all_goals exact False.elim hf

end all

section pm
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop}

/-- The st indices of the PageMap index type whose target is, in `ρ`, another core's (U17's `StFhAt`). -/
def StFPm (c : U64) (ρ : U64 → U64) : IxV13Pm S → Prop
  | .inl (.inl (.st j)) => ρ (fld j.target oAFFINITY) ≠ c
  | _ => False

set_option maxHeartbeats 4000000 in
/-- **`InsV15N`'s obligation of `nativePmKAD B` at every st start whose target is another core's** (module
docstring). -/
theorem insAP_stF_view (B : PmObl7 st Cs Ω Sg Ac Locks) {Ch : S → Prop} {s : Cfg U64 U64 U64 U64} {K : KLayoutP}
    (E : U64 → U64) {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k0 : SP} {ρ : U64 → U64} {i : IxV13Pm S}
    (hx : StFPm (S := S) c ρ i) (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (J : EpochJV K E s)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hsf : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).SF Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 i) :
    InsAP (PWE K E) ADEq NotPresent s.own s.cls s.ko c (fun l => s.lk l = some c) ∅ s.mem
      (if (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV i then annV s K c ρ k0 else k0) := by
  rcases i with (((j | j | j | j | j | j | j) | j) | j)
  all_goals try exact False.elim hx
  have hn : (ExecCfg.nativePmKAD st ar hA a0 arI AR MR B).NoV (.inl (.inl (.st j))) := fun h => h
  rw [if_pos hn]
  have hsf0 : StartV13 st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c
      (fun l => s.lk l = some c) k0 (.inl (.st j)) := hsf
  have hsf' := startV2C_of_V13 st ar hA a0 hC hsf0
  exact insAP_of_insA (st_insA_annV_fh st ar hA a0 (i := .inl (.st j)) E hC J hsf' hM hV hx)

end pm

end
end Fl4Proofs.P2.E2EP
