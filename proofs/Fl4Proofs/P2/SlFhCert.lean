/-
# P2 (line p3mc, gen 16): the sl body is `Safe` at an entry whose decided thread is another core's

The decline split for the syscall entry beside the gate (sl), the counterpart of `RrFhSafe.rr_fh_safe`
(vmR, U13) and `VmFhSafe.vm_fh_safe` (vmF, U10). At an entry `σ` with the entry facts `SlOF` whose decided thread
`d = slThr σ` (the trap arm's handler-endpoint head, the ReplyRecv arm's replied thread) is live and whose
`AFFINITY` is, in the real memory `ρ`, not the core, U9's certificate (`ViewSafeReal.safe_tr_of_states`) runs at a
state `s` carrying `ν` on the tree's reads and `ρ` elsewhere. `s` agrees with `σ` only on a read set `Rd`
(`SlFhR`: what the declining arms read before the decided thread, at every dispatch state of `σ`), and `d`'s
`AFFINITY` at `s` is `ρ`'s. So:

* `SlFhW d`: the decided thread's words a declining run reads (`REPLY_OBJ`, `STATE`, `FAULT_TYPE`, `SC`,
  `AFFINITY`);
* `slfh_cur`, `slfh_trap`, **`slfh_lp`**: `s` has `σ`'s current thread and arm, and each dispatch state of `s`
  agrees on `Rd` with one of `σ` (`lp_alt`);
* `slfh_hdT`, `slfh_hdR`: the decided thread is read at `s`'s dispatch states; **`slfh_off`**: there it is off the
  core;
* **`slfh_not_acc`**: so `s`'s run is not accepted (acceptance passed `schedulable_here d`, P1's `here_facts`);
* `slfh_pre`, **`slfh_dec`**: the declined run on any store reading `Rd ∨ SlFhW d` and writing the prefix words
  (`guard_dec`, `DestDec` / `UDec` with their homed parts void);
* **`slfh_once`**: `Once` for any read set holding `Rd` and `d`'s `AFFINITY` (`sl_pre_once`, `fault_away_once`,
  `rr_away_once`);
* **`sl_fh_safe`**: the function-level certificate.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.E2EPU15
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK)
open Fl4Proofs.P2.E2E (Once tr reads safe_tr_of_states exists_mem_state OwnDep MasksWr masksOf masksOf_eq)
open Fl4Proofs.P2.Serial (Owner ClsOwner HeldV PO Safe MoveHeld Adm)

noncomputable section
open Classical

/-- The decided thread's words a declining run reads (module docstring). -/
def SlFhW (d b : U64) : Prop :=
  b = replyA d ∨ b = stA d ∨ b = core.num.U64.wrapping_add d 3376#u64 ∨ b = scA d ∨ b = affA d

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayout} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {Cs Ω Sg Ac : Set U64}

/-- **What the declining arms read before the decided thread, in `Rd`**, at every dispatch state of `σ`. -/
structure SlFhR (found : U64 × U64) (Rd : U64 → Prop) (σ : S) (a : A) : Prop where
  al : ∀ b, Rd b → Aligned b
  pd : PreDec (L := L) Rd (SlDS (L := L) σ) σ
  hd : ∀ X a1 csc, LocalPre (st := st) ar σ a (X, a1) → sched.cur_sc st X = ok csc → RdHead (L := L) Rd X csc
  fT : SlTrap st σ → ∀ X a1, LocalPre (st := st) ar σ a (X, a1) → FltDecT (L := L) Rd X (L.curW σ)
  rT : ¬ SlTrap st σ → ∀ X a1, LocalPre (st := st) ar σ a (X, a1) →
    RrDecT (L := L) Rd X (L.curW σ) found.1 found.2

variable {Rd : U64 → Prop} {σ s : S} {a : A}

theorem slfh_cur (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) : L.curW s = L.curW σ := by
  unfold LawfulStore.curW
  rw [G.node]
  exact G.m _ (D.pd.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))

theorem slfh_trap (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) : SlTrap st s ↔ SlTrap st σ := by
  unfold SlTrap
  rw [slfh_cur ar D G, flags_ok, flags_ok, G.m _ D.pd.fl]

/-- **A dispatch state of `s` agrees on `Rd` with one of `σ`.** -/
theorem slfh_lp (hA : P0.ArchTotal ar) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) {X' : S} {a1' : A}
    (LP' : LocalPre (st := st) ar s a (X', a1')) :
    ∃ X, LocalPre (st := st) ar σ a (X, a1') ∧ (∀ b, Rd b → L.mem X' b = L.mem X b) ∧
      L.ksb X' = L.ksb X ∧ L.cpu X' = L.cpu X := by
  have E := F.E
  have hcur := slfh_cur ar D G
  have hN' : NodePlaced st K.heap.tcbs s (L.cpu s) := by rw [G.c]; exact NodePlaced.of_ksb G.k E.hN
  have hc' : L.curW s ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  have hct : Rd (ctA (L := L) σ) := D.pd.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have hcn : Rd (cnA (L := L) σ) := D.pd.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  obtain ⟨X, LP, hag⟩ := lp_alt ar hA D.al E.hT E.hN E.hcT G.k G.c hcur G.m D.pd.nx hct hcn LP'
  obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  obtain ⟨hkX', hcX', -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP'
  exact ⟨X, LP, hag, by rw [hkX', hkX, G.k], by rw [hcX', hcX, G.c]⟩

/-- The trap arm's receiver at a dispatch state of `s` is the decided thread. -/
theorem slfh_hdT (hA : P0.ArchTotal ar) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) (hS : SlTrap st σ) {X' : S} {a1' : A}
    (LP' : LocalPre (st := st) ar s a (X', a1')) {ptr b : U64} {x y g gr : Bool}
    (hc : obj.Slot.cap st (slotIdx (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER) X' =
      ok (capability.Cap.Endpoint ptr b x y g gr)) :
    L.mem X' (epHeadA ptr) = slThr st found.1 σ := by
  obtain ⟨X, LP, hag, -, -⟩ := slfh_lp ar hA F D G LP'
  have DT := D.fT hS X a1' LP
  have hc0 : obj.Slot.cap st (fhA (L := L) σ) X = ok (capability.Cap.Endpoint ptr b x y g gr) :=
    (cap_congr (hag _ DT.fh.1) (hag _ DT.fh.2)).symm.trans hc
  rw [hag _ (DT.ep ptr b x y g gr hc0).2]
  exact slThr_hd_trap ar hA F.E.hT F.E.hN F.E.hcT F.I hS LP hc0

/-- The ReplyRecv arm's replied thread at a dispatch state of `s` is the decided thread. -/
theorem slfh_hdR (hA : P0.ArchTotal ar) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) (hS : ¬ SlTrap st σ) {X' : S} {a1' : A}
    (LP' : LocalPre (st := st) ar s a (X', a1')) :
    L.mem X' (rTcbA found.1) = slThr st found.1 σ := by
  obtain ⟨X, LP, hag, -, -⟩ := slfh_lp ar hA F D G LP'
  rw [hag _ (D.rT hS X a1' LP).rRt]
  exact slThr_hd_rr ar hA F.E.hT F.E.hN F.E.hcT F.I hS LP

/-- **The decided thread is off the core at every dispatch state of `s`.** -/
theorem slfh_off (hA : P0.ArchTotal ar) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) (lv : SlLive st found.1 σ)
    (hoff : L.mem s (affA (slThr st found.1 σ)) ≠ L.cpu σ) {X' : S} {a1' : A}
    (LP' : LocalPre (st := st) ar s a (X', a1')) :
    L.mem X' (affA (slThr st found.1 σ)) ≠ L.cpu X' := by
  have E := F.E
  have hcur := slfh_cur ar D G
  have hN' : NodePlaced st K.heap.tcbs s (L.cpu s) := by rw [G.c]; exact NodePlaced.of_ksb G.k E.hN
  have hc' : L.curW s ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  have af := F.I.af lv
  rw [lp_mem ar hA E.hT hN' hc' LP' af.1.1 (fun h => af.2 ((slDS_of G.k G.c hcur).1 h)),
    (sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP').2.1, G.c]
  exact hoff

set_option maxHeartbeats 4000000 in
/-- **`s`'s run is not accepted.** -/
theorem slfh_not_acc (hA : P0.ArchTotal ar) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) (lv : SlLive st found.1 σ)
    (hoff : L.mem s (affA (slThr st found.1 σ)) ≠ L.cpu σ) {z : S} {b : A}
    (h : syscall.handle_syscall_local st ar s a n found = ok (true, z, b)) : False := by
  obtain ⟨X', a2, LP', hX⟩ := sl_acc_inv ar h
  have off := slfh_off ar hA F D G lv hoff LP'
  have hcur := slfh_cur ar D G
  have hTr := slfh_trap ar D G
  rcases hX with ⟨hS', n', hf⟩ | ⟨hS', hf⟩
  · have hS := hTr.1 hS'
    obtain ⟨ptr, badge, dest, rr, hc, -⟩ := fault_acc st ar hf
    have HF := (here_facts (L := L) hc.here).aff
    obtain ⟨sl, x, y, g, gr, hsl, hcap, -⟩ := hc.cap
    have esl : sl = slotIdx (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER := by
      rw [tcb_slot_val, hcur] at hsl; exact (ok_inj_ff hsl).symm
    subst esl
    have h1 := obj.Ep.head.spec' (st := st) X' ptr
    rw [hc.head, WP.spec_ok] at h1
    rw [h1, slfh_hdT ar hA F D G hS LP' hcap] at HF
    exact off HF
  · have hS : ¬ SlTrap st σ := fun h' => hS' (hTr.2 h')
    obtain ⟨u, usc, C, -⟩ := reply_recv_found_acc st ar hf
    obtain ⟨bb, hb, hbt⟩ := C.here
    subst hbt
    have HF := (here_facts (L := L) hb).aff
    have h1 := obj.Reply.tcb.blk (st := st) X' found.1
    rw [C.tcb, WP.spec_ok, slfh_hdR ar hA F D G hS LP'] at h1
    rw [h1] at HF
    exact off HF

set_option maxHeartbeats 4000000 in
/-- The prefix facts at `s`, for any read set `R ⊇ Rd` and write set `W ⊇ SlDS σ`. -/
theorem slfh_pre (hA : P0.ArchTotal ar) (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) {R W : U64 → Prop} (hRR : ∀ b, Rd b → R b)
    (hWW : ∀ b, SlDS (L := L) σ b → W b) :
    PreDec (L := L) R W s ∧
      ∀ X' a1 csc, LocalPre (st := st) ar s a (X', a1) → sched.cur_sc st X' = ok csc → RdHead (L := L) R X' csc := by
  have E := F.E
  have hcur := slfh_cur ar D G
  refine ⟨⟨fun o h1 h2 => hRR _ (by rw [G.node]; exact D.pd.nd o h1 h2),
    hWW _ (Or.inr (Or.inl (G.node layout.node.CUR_TIME))), hWW _ (Or.inr (Or.inr (G.node layout.node.CONSUMED))),
    by rw [hcur]; exact hRR _ D.pd.fl, by rw [hcur]; exact hRR _ D.pd.nx, by rw [hcur]; exact hWW _ (Or.inl rfl)⟩,
    fun X' a1' csc LP' ecsc => ?_⟩
  obtain ⟨X, LP, hag, hk, hc⟩ := slfh_lp ar hA F D G LP'
  obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have rcs : Rd (L.nodeA X layout.node.CUR_SC) := by
    unfold LawfulStore.nodeA; rw [hcX, nodeAt_of_ksb hkX]
    exact D.pd.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])
  have en : L.nodeA X' layout.node.CUR_SC = L.nodeA X layout.node.CUR_SC := by
    unfold LawfulStore.nodeA; exact slDS_node hk hc
  have ecsc' : sched.cur_sc st X = ok csc := by
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X')] at ecsc
    rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X), ← hag _ rcs, ← en]
    exact ecsc
  exact RdHead.mono hRR (RdHead.congr hag (D.hd X a1' csc LP ecsc'))

set_option maxHeartbeats 8000000 in
/-- **`s`'s declined run on a store reading `Rd ∨ SlFhW d` and writing the prefix words.** -/
theorem slfh_dec (hA : P0.ArchTotal ar) {R W : U64 → Prop} {gS : machine.Store S} [GRd gS st R] [GWr gS st W]
    (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) (lv : SlLive st found.1 σ)
    (hoff : L.mem s (affA (slThr st found.1 σ)) ≠ L.cpu σ)
    (hRR : ∀ b, (Rd b ∨ SlFhW (slThr st found.1 σ) b) → R b) (hWW : ∀ b, SlDS (L := L) σ b → W b)
    {r : Bool × S × A} (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local gS ar s a n found = ok r := by
  have E := F.E
  have hcur := slfh_cur ar D G
  have hN' : NodePlaced st K.heap.tcbs s (L.cpu s) := by rw [G.c]; exact NodePlaced.of_ksb G.k E.hN
  have hc' : L.curW s ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  have hTr := slfh_trap ar D G
  obtain ⟨hp, hhd⟩ := slfh_pre ar hA F D G (fun b hb => hRR b (Or.inl hb)) hWW
  refine syscall.handle_syscall_local.guard_dec (gS := gS) hA E.hT hN' hc' hp hhd ?_ ?_ h
  · intro hS' X' a1' n' LP' hf
    have hS := hTr.1 hS'
    obtain ⟨X, LP, hag, hk, hc⟩ := slfh_lp ar hA F D G LP'
    rw [hcur] at hf ⊢
    refine fastpath.fault.guard_dec (gS := gS)
      (FltDec.of (FltDecT.mono (fun b hb => hRR b (Or.inl hb)) (FltDecT.congr hk hc hag (D.fT hS X a1' LP))) ?_)
      hf hn
    intro ptr bb x y g gr hcp _ d hd
    have e1 := slfh_hdT ar hA F D G hS LP' hcp
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X' ptr), e1] at hd
    rw [← ok_inj_ff hd]
    exact ⟨hRR _ (Or.inr (Or.inl rfl)), hRR _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),
      fun e => absurd e (slfh_off ar hA F D G lv hoff LP')⟩
  · intro hS' X' a1' LP' hf
    have hS : ¬ SlTrap st σ := fun h' => hS' (hTr.2 h')
    obtain ⟨X, LP, hag, hk, hc⟩ := slfh_lp ar hA F D G LP'
    rw [hcur] at hf ⊢
    refine fastpath.reply_recv_found.guard_dec (gS := gS)
      (RrDec.of (RrDecT.mono (fun b hb => hRR b (Or.inl hb)) (RrDecT.congr hk hc hag (D.rT hS X a1' LP))) ?_)
      hf hn
    intro u hu _
    have h1 := obj.Reply.tcb.blk (st := st) X' found.1
    rw [hu, WP.spec_ok, slfh_hdR ar hA F D G hS LP'] at h1
    rw [h1]
    exact ⟨hRR _ (Or.inr (Or.inr (Or.inl rfl))), hRR _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
      hRR _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))),
      hRR _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),
      fun e => absurd e (slfh_off ar hA F D G lv hoff LP')⟩

set_option maxHeartbeats 8000000 in
/-- **`s`'s run reads each racy word once** (for any read set holding `Rd` and `d`'s `AFFINITY`). -/
theorem slfh_once (hA : P0.ArchTotal ar) {Ro User : U64 → Prop}
    (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ)
    (D : SlFhR (st := st) ar found Rd σ a) (G : Ag st Rd σ s) (lv : SlLive st found.1 σ)
    (hoff : L.mem s (affA (slThr st found.1 σ)) ≠ L.cpu σ)
    (hR0 : ∀ q, (Rd q ∨ q = affA (slThr st found.1 σ)) → Ro q ∧ ¬ User q)
    (hDU : ∀ q, SlDS (L := L) σ q → ¬ User q) {r' : Bool × S × A}
    (h : interp st ar (R.syscall.handle_syscall_local n found) s a = ok r') :
    Once st ar Ro User ∅ ∅ (R.syscall.handle_syscall_local n found) s a := by
  obtain ⟨rp, ep⟩ := found
  have E := F.E
  have hcur := slfh_cur ar D G
  have hN' : NodePlaced st K.heap.tcbs s (L.cpu s) := by rw [G.c]; exact NodePlaced.of_ksb G.k E.hN
  have hc' : L.curW s ∈ K.heap.tcbs := by rw [hcur]; exact E.hcT
  have hTr := slfh_trap ar D G
  obtain ⟨hp, hhd⟩ := slfh_pre ar hA F D G (R := fun q => Rd q ∨ q = affA (slThr st rp σ))
    (W := SlDS (L := L) σ) (fun b hb => Or.inl hb) (fun b hb => hb)
  refine sl_pre_once (R0 := fun q => Rd q ∨ q = affA (slThr st rp σ)) (W0 := SlDS (L := L) σ) hR0 hDU hA E.hT
    hN' hc' hp hhd h ?_ ?_
  · intro hS' X' a1' n' LP' h' Wd
    have hS := hTr.1 hS'
    obtain ⟨X, LP, hag, hk, hc⟩ := slfh_lp ar hA F D G LP'
    rw [hcur] at h' ⊢
    refine fault_away_once hR0
      (FltDecT.mono (fun b hb => Or.inl hb) (FltDecT.congr hk hc hag (D.fT hS X a1' LP))) ?_ h' Wd
    intro ptr bb x y g gr hcp _
    rw [slfh_hdT ar hA F D G hS LP' hcp]
    exact ⟨Or.inr rfl, slfh_off ar hA F D G lv hoff LP'⟩
  · intro hS' X' a1' LP' h' Wd
    have hS : ¬ SlTrap st σ := fun h' => hS' (hTr.2 h')
    obtain ⟨X, LP, hag, hk, hc⟩ := slfh_lp ar hA F D G LP'
    rw [hcur] at h' ⊢
    refine rr_away_once hR0
      (RrDecT.mono (fun b hb => Or.inl hb) (RrDecT.congr hk hc hag (D.rT hS X a1' LP))) ?_ h' Wd
    intro _
    rw [slfh_hdR ar hA F D G hS LP']
    exact ⟨Or.inr rfl, slfh_off ar hA F D G lv hoff LP'⟩

set_option maxHeartbeats 4000000 in
/-- **The sl body is `Safe` at an entry whose decided thread is another core's** (module docstring). -/
theorem sl_fh_safe {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
    {kt : U64 → ClsOwner U64} {User : U64 → Prop} (hL : MoveHeld own) (hO : OwnDep own User) (hmk : MasksWr st)
    (hA : P0.ArchTotal ar) {c : U64} {hs : U64 → Prop} {μ ρ : U64 → U64} (hc : L.cpu σ = c)
    (F : SlOF (st := st) ar K Locks m0 n found Cs Ω Sg Ac σ) {Ro : U64 → Prop}
    (D : SlFhR (st := st) ar found Rd σ a) (hR0 : ∀ q, Rd q → Ro q ∧ ¬ User q)
    (lv : SlLive st found.1 σ)
    (hgo : Ro (affA (slThr st found.1 σ)) ∧ ¬ User (affA (slThr st found.1 σ)))
    (hρd : ρ (affA (slThr st found.1 σ)) ≠ c)
    (hRdρ : ∀ b, Rd b → ρ b = L.mem σ b)
    (hRPO : ∀ x, ¬ User x → Ro x → PO c hs (own μ x))
    (hρμ : ∀ x, PO c hs (own μ x) → ρ x = μ x)
    (hDU : ∀ q, SlDS (L := L) σ q → ¬ User q)
    (hH : ∀ x, SlDS (L := L) σ x → HeldV c hs (own μ x))
    (hSO : ∀ (z : S) b v, SlDS (L := L) σ b → StepOK own cls kt User c hs (L.mem z) (L.mem (L.wr z b v))) :
    Safe own cls kt c hs μ
      (tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar (R.syscall.handle_syscall_local n found) ∅ a) := by
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have ht := F.N.hthr lv
  have hX := F.B.regionOKX
  have aD : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      Aligned (core.num.U64.wrapping_add (slThr st found.1 σ) o) :=
    fun o h1 h2 h3 => (hX.tcbW _ ht o h1 h2 h3).2.2
  let R'' : U64 → Prop := fun b => Rd b ∨ SlFhW (slThr st found.1 σ) b
  have hR''al : ∀ b, R'' b → Aligned b := by
    rintro b (hb | rfl | rfl | rfl | rfl | rfl)
    · exact D.al b hb
    · exact aD 3360#u64 (by simp) (by simp) (by simp)
    · rw [stA_eq]; exact aD 3328#u64 (by simp) (by simp) (by simp)
    · exact aD 3376#u64 (by simp) (by simp) (by simp)
    · exact aD 3464#u64 (by simp) (by simp) (by simp)
    · exact aD 3520#u64 (by simp) (by simp) (by simp)
  refine safe_tr_of_states hL hO hmk (Hp := SlDS (L := L) σ) _ a hH hRPO ?_
  intro ν hν
  generalize hq : tr Ro User cls kt c (L.ksb σ) (masksOf st σ) ar
    (R.syscall.handle_syscall_local n found) ∅ a = q
  obtain ⟨s, sc, sk, sm, hmem0⟩ := exists_mem_state hmk σ (fun x => if x ∈ reads q ν then ν x else ρ x)
  have hmem : ∀ x, Aligned x → L.mem s x = if x ∈ reads q ν then ν x else ρ x := hmem0
  have eR : ∀ b, Ro b → ¬ User b → (if b ∈ reads q ν then ν b else ρ b) = ρ b := by
    intro b hb hu'
    split_ifs
    · exact (hν.1 b (hRPO b hu' hb)).trans (hρμ b (hRPO b hu' hb)).symm
    · rfl
  have G : Ag st Rd σ s := ⟨sk, sc, fun b hb => by
    rw [hmem b (D.al b hb), eR b (hR0 b hb).1 (hR0 b hb).2]; exact hRdρ b hb⟩
  have hoff : L.mem s (affA (slThr st found.1 σ)) ≠ L.cpu σ := by
    rw [hmem (affA (slThr st found.1 σ)) (aD 3520#u64 (by simp) (by simp) (by simp)), eR _ hgo.1 hgo.2, hc]
    exact hρd
  obtain ⟨r, hr⟩ := sl_total (st := st) L.total hA n found s a
  have hn : r.1 ≠ true := by
    obtain ⟨b0, z, c0⟩ := r
    intro hb
    change b0 = true at hb
    subst hb
    exact slfh_not_acc ar hA F D G lv hoff hr
  have hg : syscall.handle_syscall_local (PathObl.guard st R'' (SlDS (L := L) σ)) ar s a n found = ok r :=
    slfh_dec ar hA (R := R'') (W := SlDS (L := L) σ) F D G lv hoff (fun b hb => hb) (fun b hb => hb) hr hn
  rw [hp] at hg
  have hW := (interp_guard _ s a r hg).2
  have hM : syscall.handle_syscall_local
      (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) ar s a n found = ok r := by
    haveI iR : GRd (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) st (fun _ => True) :=
      { read := fun _ _ => rfl, read_pair := fun _ _ _ => rfl, ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    haveI iW : GWr (mguard st (fun x z => StepOK own cls kt User c hs (L.mem x) (L.mem z))) st
        (SlDS (L := L) σ) :=
      { write := fun {b} hb y v => by
          rw [L.write_eq]
          exact mguard_write (L.write_eq y b v) (hSO y b v hb)
        ks_base := rfl, cur_cpu := rfl, frame_masks := rfl }
    exact slfh_dec ar hA (R := fun _ => True) (W := SlDS (L := L) σ) F D G lv hoff (fun _ _ => trivial)
      (fun b hb => hb) hr hn
  rw [hp] at hM
  have hWM := (interp_mguard _ s a r hM).2
  have hr' : interp st ar (R.syscall.handle_syscall_local n found) s a = ok r := by rw [← hp]; exact hr
  have hOnce := slfh_once ar hA (Ro := Ro) (User := User) F D G lv hoff
    (fun q hq => hq.elim (hR0 q) (fun e => by subst e; exact hgo)) hDU hr'
  refine ⟨s, SlDS (L := L) σ, sc.trans hc, sk, sm.trans (masksOf_eq st σ),
    Within.mono (fun b hb => hR''al b hb) (fun b hb => hb) _ s a hW, hWM, hOnce,
    fun x hx => ⟨(SlDS.ws F.P.preG hx).1, fun _ => hx⟩,
    fun x hx hxa => by rw [hmem x hxa, if_pos hx], fun x hxa hu' hne hpo => hne ?_⟩
  rw [hmem x hxa]
  split_ifs
  · exact hν.1 x hpo
  · exact hρμ x hpo

end

end
end Fl4Proofs.P2.PathObl
