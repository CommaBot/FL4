/-
P3 (DESIGN.md §9), untyped: **what creating a TCB writes** (handoff/utj.md
"uttypes", ut37; l4v `retype_region` of `TCBObject`s with `default_tcb`,
`Arch_initContext` = `new_context`, and seL4's `tcbDebugAppend`).

UntypedTcb's `create_tcb_frame` gives `create_object`'s write frame for a
TCB; the J relation also reads values: the new TCB's registers (`TcbRel.regs`
against `new_context`: zero but `CS`, `FLAGS`, `SS`), its domain word (the
current domain, `SchedSpec.tcb`) and the debug links (P1's `DbgLinksOK`).

* `init_context_content`: `regs::init_context` leaves register `i` at
  `ctxW i` (51 for `CS`, 514 = `IF | bit 1` for `FLAGS`, 43 for `SS`, else 0),
  writing only the register words;
* `debug_append_content`: the new TCB's `debug_next` is the old head, its
  `debug_prev` 0, the old head's `debug_prev` the new TCB, the head word the
  new TCB; nothing else written;
* `create_tcb_content`: `create_object` for a TCB, those values with the
  domain word the current domain, writing only the new TCB, the old head's
  `debug_prev` and the head word.
-/
import Fl4Proofs.P3.UntypedTcbLoop
import Fl4Proofs.P3.SchedSwitch
import Fl4Proofs.P3.EpRel
import Fl4Proofs.P1.QueueCancel
import Fl4Proofs.P1.QueueSched
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Endp

noncomputable section

/-- `[t + lo, t + hi)`. -/
def Rg (t : U64) (lo hi : Nat) (w : U64) : Prop := t.val + lo ≤ w.val ∧ w.val < t.val + hi

/-- The register value `init_context` leaves in register `i` (x86-64
`new_context`: `CS` = 51, `FLAGS` = 514, `SS` = 43, else 0). -/
def ctxW (i : Nat) : U64 := if i = 20 then 51#u64 else if i = 13 then 514#u64 else if i = 21 then 43#u64 else 0#u64

theorem regA_v {t i : U64} (ht : TcbOk t) (hi : i.val < 24) : (regA t i).val = t.val + 256 + 8 * i.val := by
  obtain ⟨h1, h2⟩ := ht
  unfold regA layout.tcb.REGS
  addr_tac

theorem regA_al {t i : U64} (ht : TcbOk t) (hi : i.val < 24) : P1.Aligned (regA t i) := by
  have := regA_v ht hi; have := ht.1
  show _ % 8 = 0; omega

theorem regA_eq {t i j : U64} (ht : TcbOk t) (hi : i.val < 24) (hj : j.val < 24) :
    regA t i = regA t j ↔ i.val = j.val := by
  constructor
  · intro e
    have := congrArg UScalar.val e
    rw [regA_v ht hi, regA_v ht hj] at this; omega
  · intro e; rw [UScalar.eq_of_val_eq e]

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

theorem set_reg_eq (s : S) (t r v : U64) : obj.Tcb.set_reg st t s r v ⦃ s' => s' = L.wr s (regA t r) v ⦄ := by
  unfold obj.Tcb.set_reg regA
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok]

theorem set_domain_eq (s : S) (t v : U64) : obj.Tcb.set_domain st t s v ⦃ s' => s' = L.wr s (P1.domA t) v ⦄ := by
  unfold obj.Tcb.set_domain P1.domA
  rw [show layout.tcb.DOMAIN = ok 3432#u64 by unfold layout.tcb.DOMAIN layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok]

theorem init_context_content (s : S) (t : U64) (ht : TcbOk t) :
    regs.init_context st s t ⦃ s' => WFrame (L := L) s s' (Rg t 256 448) ∧
      ∀ i : U64, i.val < 24 → L.mem s' (regA t i) = ctxW i.val ⦄ := by
  unfold regs.init_context regs.init_context_loop
  have hloop : loop (fun (s1, i1) => regs.init_context_loop.body st t s1 i1) (s, 0#u64) ⦃ s' =>
      WFrame (L := L) s s' (Rg t 256 448) ∧ ∀ j : U64, j.val < 24 → L.mem s' (regA t j) = 0#u64 ⦄ := by
    refine loop.spec_decr_nat (measure := fun x => 24 - x.2.val)
      (inv := fun x => x.2.val ≤ 24 ∧ WFrame (L := L) s x.1 (Rg t 256 448) ∧
        ∀ j : U64, j.val < x.2.val → L.mem x.1 (regA t j) = 0#u64) _ _ _ ?_ ?_
    · rintro ⟨s1, i⟩ ⟨hi, hf, hz⟩
      unfold regs.init_context_loop.body
      simp only [layout.reg.COUNT] at hi hf hz ⊢
      by_cases hit : i < 24#u64
      · rw [if_pos hit]
        have hit' : i.val < 24 := hit
        obtain ⟨s2, hs2, e2⟩ := spec_exists (set_reg_eq (L := L) s1 t i 0#u64)
        rw [hs2]; simp only [bind_ok]
        step as ⟨i1, hi1⟩
        subst e2
        refine ⟨by omega, hf.trans (WFrame.wr s1 (regA_al ht hit') (by
          unfold Rg; rw [regA_v ht hit']; omega) _), fun j hj => ?_, by omega⟩
        have hj' : j.val < 24 := by omega
        rw [L.mem_wr _ _ _ _ (regA_al ht hit') (regA_al ht hj')]
        split_ifs with e
        · rfl
        · have : j.val ≠ i.val := fun h => e ((regA_eq ht hit' hj').2 h.symm)
          exact hz j (by omega)
      · rw [if_neg hit, WP.spec_ok]
        have : ¬ i.val < 24 := hit
        exact ⟨hf, fun j hj => hz j (by omega)⟩
    · exact ⟨by simp, WFrame.refl s _, fun j hj => absurd hj (by simp)⟩
  obtain ⟨s1, hs1, hf1, hz1⟩ := spec_exists hloop
  rw [hs1]; simp only [bind_ok]
  rw [show layout.reg.CS = 20#u64 by unfold layout.reg.CS; rfl,
    show layout.reg.FLAGS = 13#u64 by unfold layout.reg.FLAGS; rfl,
    show layout.reg.SS = 21#u64 by unfold layout.reg.SS; rfl,
    show regs.SEL_CS_3 = 51#u64 by unfold regs.SEL_CS_3; rfl,
    show regs.SEL_DS_3 = 43#u64 by unfold regs.SEL_DS_3; rfl]
  obtain ⟨s2, hs2, e2⟩ := spec_exists (set_reg_eq (L := L) s1 t 20#u64 51#u64)
  rw [hs2]; simp only [bind_ok]
  rw [spec_eq_ok Fl4Proofs.P0.Consts.regs.FLAGS_USER_DEFAULT.spec]; simp only [bind_ok]
  obtain ⟨s3, hs3, e3⟩ := spec_exists (set_reg_eq (L := L) s2 t 13#u64 514#u64)
  rw [hs3]; simp only [bind_ok]
  apply WP.spec_mono (set_reg_eq (L := L) s3 t 21#u64 43#u64)
  rintro s4 rfl
  subst e2 e3
  have a20 : (20#u64 : U64).val < 24 := by decide
  have a13 : (13#u64 : U64).val < 24 := by decide
  have a21 : (21#u64 : U64).val < 24 := by decide
  refine ⟨((hf1.trans (WFrame.wr _ (regA_al ht a20) (by unfold Rg; rw [regA_v ht a20]; omega) _)).trans
    (WFrame.wr _ (regA_al ht a13) (by unfold Rg; rw [regA_v ht a13]; omega) _)).trans
    (WFrame.wr _ (regA_al ht a21) (by unfold Rg; rw [regA_v ht a21]; omega) _), fun i hi => ?_⟩
  rw [L.mem_wr _ _ _ _ (regA_al ht a21) (regA_al ht hi), L.mem_wr _ _ _ _ (regA_al ht a13) (regA_al ht hi),
    L.mem_wr _ _ _ _ (regA_al ht a20) (regA_al ht hi)]
  have v20 : (20#u64 : U64).val = 20 := rfl
  have v13 : (13#u64 : U64).val = 13 := rfl
  have v21 : (21#u64 : U64).val = 21 := rfl
  simp only [regA_eq ht a21 hi, regA_eq ht a13 hi, regA_eq ht a20 hi, v20, v13, v21]
  unfold ctxW
  split_ifs <;> first | rfl | omega | exact hz1 i hi

theorem init_fpu_rg (s : S) (t : U64) (ht : TcbOk t) :
    objects.init_fpu st s t ⦃ s' => WFrame (L := L) s s' (Rg t 512 544) ⦄ := by
  unfold objects.init_fpu obj.Tcb.fpu_addr
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, layout.tcb.FPU]
  obtain ⟨h1, h2⟩ := ht
  have hv1 : (core.num.U64.wrapping_add t 512#u64).val = t.val + 512 := by addr_tac
  have hv2 : (core.num.U64.wrapping_add (core.num.U64.wrapping_add t 512#u64) 24#u64).val = t.val + 536 := by addr_tac
  exact (WFrame.wr s (by show _ % 8 = 0; rw [hv1]; omega) (by unfold Rg; rw [hv1]; omega) _).trans
    (WFrame.wr _ (by show _ % 8 = 0; rw [hv2]; omega) (by unfold Rg; rw [hv2]; omega) _)

theorem set_debug_reg_rg (s : S) (t r v : U64) (ht : TcbOk t) (hr : r.val < 8) :
    obj.Tcb.set_debug_reg st t s r v ⦃ s' => WFrame (L := L) s s' (Rg t 448 512) ⦄ := by
  unfold obj.Tcb.set_debug_reg
  simp only [lift, bind_ok, L.write_eq, WP.spec_ok, layout.tcb.DEBUG]
  obtain ⟨h1, h2⟩ := ht
  have hv : (core.num.U64.wrapping_add (core.num.U64.wrapping_add t 448#u64)
      (core.num.U64.wrapping_mul r 8#u64)).val = t.val + 448 + 8 * r.val := by addr_tac
  exact WFrame.wr s (by show _ % 8 = 0; rw [hv]; omega) (by unfold Rg; rw [hv]; omega) v

theorem debug_init_rg (s : S) (t : U64) (ht : TcbOk t) :
    debug.init_context st s t ⦃ s' => WFrame (L := L) s s' (Rg t 448 512) ⦄ := by
  unfold debug.init_context debug.init_context_loop
  have hloop : loop (fun (s1, i1) => debug.init_context_loop.body st t s1 i1) (s, 0#u64) ⦃ s' =>
      WFrame (L := L) s s' (Rg t 448 512) ⦄ := by
    refine loop.spec_decr_nat (measure := fun x => 8 - x.2.val)
      (inv := fun x => x.2.val ≤ 8 ∧ WFrame (L := L) s x.1 (Rg t 448 512)) _ _ _ ?_ ?_
    · rintro ⟨s1, i⟩ ⟨hi, hf⟩
      unfold debug.init_context_loop.body
      simp only at hi hf ⊢
      by_cases hit : i < 8#u64
      · rw [if_pos hit]
        have hit' : i.val < 8 := hit
        obtain ⟨s2, hs2, hf2⟩ := spec_exists (set_debug_reg_rg (L := L) s1 t i 0#u64 ht hit')
        rw [hs2]; simp only [bind_ok]
        step as ⟨i1, hi1⟩
        exact ⟨by omega, hf.trans hf2, by omega⟩
      · rw [if_neg hit, WP.spec_ok]; exact hf
    · exact ⟨by simp, WFrame.refl s _⟩
  obtain ⟨s1, hs1, hf1⟩ := spec_exists hloop
  rw [hs1]; simp only [bind_ok]
  obtain ⟨s2, hs2, hf2⟩ := spec_exists (set_debug_reg_rg (L := L) s1 t debug.DR6 4294905840#u64 ht
    (by simp [debug.DR6]))
  rw [hs2]; simp only [bind_ok]
  exact WP.spec_mono (set_debug_reg_rg (L := L) s2 t debug.DR7 1024#u64 ht (by simp [debug.DR7]))
    (fun s3 hf3 => hf1.trans (hf2.trans hf3))

theorem child_names_rg (s : S) (child parent len : U64) (ht : TcbOk child) :
    objects.set_child_name_loop1 st s child parent len 0#u64 ⦃ s' => WFrame (L := L) s s' (Rg child 3600 3664) ⦄ := by
  unfold objects.set_child_name_loop1
  refine loop.spec_decr_nat (measure := fun x => 8 - x.2.val)
    (inv := fun x => x.2.val ≤ 8 ∧ WFrame (L := L) s x.1 (Rg child 3600 3664)) _ _ _ ?_ ⟨by simp, WFrame.refl s _⟩
  rintro ⟨s1, w⟩ ⟨hw, hf⟩
  unfold objects.set_child_name_loop1.body
  simp only at hw hf ⊢
  by_cases h : w < 8#u64
  · rw [if_pos h]
    have h' : w.val < 8 := h
    obtain ⟨v, hv, -⟩ := spec_exists (child_word_total (L := L) s1 parent len w)
    rw [hv]; simp only [bind_ok, obj.Tcb.name_addr, lift]
    rw [show layout.tcb.NAME = ok 3600#u64 by unfold layout.tcb.NAME layout.tcb.F; rfl]
    simp only [bind_ok, L.write_eq]
    obtain ⟨h1, h2⟩ := ht
    have hv' : (core.num.U64.wrapping_add (core.num.U64.wrapping_add child 3600#u64)
        (core.num.U64.wrapping_mul w 8#u64)).val = child.val + 3600 + 8 * w.val := by addr_tac
    step as ⟨w1, hw1⟩
    exact ⟨by omega, hf.trans (WFrame.wr s1 (by show _ % 8 = 0; rw [hv']; omega) (by unfold Rg; rw [hv']; omega) v),
      by omega⟩
  · rw [if_neg h, WP.spec_ok]; exact hf

theorem set_child_name_rg (s : S) (child parent : U64) (ht : TcbOk child) :
    objects.set_child_name st s child parent ⦃ s' => WFrame (L := L) s s' (Rg child 3600 3664) ⦄ := by
  unfold objects.set_child_name
  simp only [fl4_abi.config.DEBUG_BUILD, ↓reduceIte, obj.Tcb.is_null, bind_ok]
  split
  · rw [WP.spec_ok]; exact WFrame.refl s _
  · obtain ⟨len, hl, -⟩ := spec_exists (child_len_total (L := L) s parent)
    rw [hl]; simp only [bind_ok]
    exact child_names_rg s child parent len ht

/-- The words `debug_append` writes for a new TCB `t`: its links, the old
head's `debug_prev`, the head word. -/
def DbgAW (s : S) (t w : U64) : Prop :=
  w = P1.dnA t ∨ w = P1.dpA t ∨ (L.mem s (dbgW (L := L) s t) ≠ 0#u64 ∧ w = P1.dpA (L.mem s (dbgW (L := L) s t))) ∨
    w = dbgW (L := L) s t

theorem dnA_v {t : U64} (ht : TcbOk t) : (P1.dnA t).val = t.val + 3576 := by
  obtain ⟨h1, h2⟩ := ht; unfold P1.dnA; addr_tac

theorem dpA_v {t : U64} (ht : TcbOk t) : (P1.dpA t).val = t.val + 3584 := by
  obtain ⟨h1, h2⟩ := ht; unfold P1.dpA; addr_tac

theorem domA_v {t : U64} (ht : TcbOk t) : (P1.domA t).val = t.val + 3432 := by
  obtain ⟨h1, h2⟩ := ht; unfold P1.domA; addr_tac

theorem ne_of_val_ne {a b : U64} (h : a.val ≠ b.val) : a ≠ b := fun e => h (by rw [e])

/-- **`debug_append`'s values** (module docstring). -/
theorem debug_append_content (s : S) (t : U64) (ht : TcbOk t) (hna : P1.Aligned (dbgW (L := L) s t))
    (hhd : L.mem s (dbgW (L := L) s t) ≠ 0#u64 → TcbOk (L.mem s (dbgW (L := L) s t)))
    (hsep : L.mem s (dbgW (L := L) s t) ≠ 0#u64 →
      (L.mem s (dbgW (L := L) s t)).val + 4096 ≤ t.val ∨ t.val + 4096 ≤ (L.mem s (dbgW (L := L) s t)).val)
    (hout : ¬ Rg t 0 4096 (dbgW (L := L) s t))
    (hout2 : L.mem s (dbgW (L := L) s t) ≠ 0#u64 → ¬ Rg (L.mem s (dbgW (L := L) s t)) 0 4096 (dbgW (L := L) s t)) :
    objects.debug_append st s t ⦃ s' => WFrame (L := L) s s' (DbgAW (L := L) s t) ∧
      L.mem s' (dbgW (L := L) s t) = t ∧ L.mem s' (P1.dnA t) = L.mem s (dbgW (L := L) s t) ∧
      L.mem s' (P1.dpA t) = 0#u64 ∧
      (L.mem s (dbgW (L := L) s t) ≠ 0#u64 → L.mem s' (P1.dpA (L.mem s (dbgW (L := L) s t))) = t) ⦄ := by
  unfold objects.debug_append obj.Tcb.affinity
  rw [show layout.tcb.AFFINITY = ok 3520#u64 by unfold layout.tcb.AFFINITY layout.tcb.F; rfl]
  simp only [lift, bind_ok, L.read_eq]
  rw [spec_eq_ok (Fl4Proofs.P1.obj.node_get.spec (L := L) s (L.mem s (core.num.U64.wrapping_add t 3520#u64))
    layout.node.DEBUG_TCBS)]
  simp only [bind_ok, obj.Tcb.set_debug_prev, obj.Tcb.set_debug_next, lift, L.write_eq,
    show layout.tcb.DEBUG_PREV = ok 3584#u64 by unfold layout.tcb.DEBUG_PREV layout.tcb.F; rfl,
    show layout.tcb.DEBUG_NEXT = ok 3576#u64 by unfold layout.tcb.DEBUG_NEXT layout.tcb.F; rfl]
  have hdw : L.nodeAt s (L.mem s (core.num.U64.wrapping_add t 3520#u64)) layout.node.DEBUG_TCBS = dbgW (L := L) s t := rfl
  rw [hdw]
  have edp : core.num.U64.wrapping_add t 3584#u64 = P1.dpA t := rfl
  have edn : core.num.U64.wrapping_add t 3576#u64 = P1.dnA t := rfl
  rw [edp, edn]
  set h := L.mem s (dbgW (L := L) s t) with hh
  set DW := dbgW (L := L) s t with hDW
  have alp : P1.Aligned (P1.dpA t) := by have := dpA_v ht; have := ht.1; show _ % 8 = 0; omega
  have aln : P1.Aligned (P1.dnA t) := by have := dnA_v ht; have := ht.1; show _ % 8 = 0; omega
  have npn : P1.dpA t ≠ P1.dnA t := ne_of_val_ne (by rw [dpA_v ht, dnA_v ht]; omega)
  have hWp : DW ≠ P1.dpA t := fun e => hout (by unfold Rg; rw [e, dpA_v ht]; omega)
  have hWn : DW ≠ P1.dnA t := fun e => hout (by unfold Rg; rw [e, dnA_v ht]; omega)
  have hlast : ∀ s3 : S, WFrame (L := L) s s3 (DbgAW (L := L) s t) → L.mem s3 (P1.dnA t) = h →
      L.mem s3 (P1.dpA t) = 0#u64 → (h ≠ 0#u64 → L.mem s3 (P1.dpA h) = t) →
      obj.node_set st s3 (L.mem s (core.num.U64.wrapping_add t 3520#u64)) layout.node.DEBUG_TCBS t ⦃ s' =>
        WFrame (L := L) s s' (DbgAW (L := L) s t) ∧ L.mem s' DW = t ∧ L.mem s' (P1.dnA t) = h ∧
        L.mem s' (P1.dpA t) = 0#u64 ∧ (h ≠ 0#u64 → L.mem s' (P1.dpA h) = t) ⦄ := by
    intro s3 hf3 g1 g2 g3
    apply WP.spec_mono (Fl4Proofs.P1.obj.node_set.spec (L := L) s3 _ _ t)
    rintro s' rfl
    rw [nodeAt_ksb hf3.1]
    have eW : L.nodeAt s (L.mem s (core.num.U64.wrapping_add t 3520#u64)) layout.node.DEBUG_TCBS = DW := rfl
    rw [eW]
    refine ⟨hf3.trans (WFrame.wr s3 hna (Or.inr (Or.inr (Or.inr rfl))) t), L.mem_wr_same hna, ?_, ?_, fun hn => ?_⟩
    · rw [L.mem_wr _ _ _ _ hna aln, if_neg hWn]; exact g1
    · rw [L.mem_wr _ _ _ _ hna alp, if_neg hWp]; exact g2
    · have hhv := hhd hn
      have alq : P1.Aligned (P1.dpA h) := by have := dpA_v hhv; have := hhv.1; show _ % 8 = 0; omega
      have hWq : DW ≠ P1.dpA h := fun e => hout2 hn (by unfold Rg; rw [e, dpA_v hhv]; omega)
      rw [L.mem_wr _ _ _ _ hna alq, if_neg hWq]; exact g3 hn
  have f1 : WFrame (L := L) s (L.wr s (P1.dpA t) 0#u64) (DbgAW (L := L) s t) :=
    WFrame.wr s alp (Or.inr (Or.inl rfl)) _
  set s1 := L.wr s (P1.dpA t) 0#u64 with hs1
  have f2 : WFrame (L := L) s1 (L.wr s1 (P1.dnA t) h) (DbgAW (L := L) s t) :=
    WFrame.wr s1 aln (Or.inl rfl) _
  set s2 := L.wr s1 (P1.dnA t) h with hs2
  have f12 := f1.trans f2
  have m2n : L.mem s2 (P1.dnA t) = h := L.mem_wr_same aln
  have m2p : L.mem s2 (P1.dpA t) = 0#u64 := by
    rw [hs2, L.mem_wr _ _ _ _ aln alp, if_neg (Ne.symm npn), hs1]; exact L.mem_wr_same alp
  by_cases hh0 : h = 0#u64
  · have : (h != 0#u64) = false := by simp [hh0]
    simp only [this, Bool.false_eq_true, ↓reduceIte, bind_ok, uncurry_apply_pair]
    exact hlast s2 f12 m2n m2p (fun hn => absurd hh0 hn)
  · have : (h != 0#u64) = true := by simp [hh0]
    simp only [this, ↓reduceIte, bind_ok, uncurry_apply_pair]
    have hhv := hhd hh0
    have edq : core.num.U64.wrapping_add h 3584#u64 = P1.dpA h := rfl
    rw [edq]
    have alq : P1.Aligned (P1.dpA h) := by have := dpA_v hhv; have := hhv.1; show _ % 8 = 0; omega
    have hsp := hsep hh0
    have qn : P1.dpA h ≠ P1.dnA t := ne_of_val_ne (by rw [dpA_v hhv, dnA_v ht]; omega)
    have qp : P1.dpA h ≠ P1.dpA t := ne_of_val_ne (by rw [dpA_v hhv, dpA_v ht]; omega)
    apply hlast
    · exact f12.trans (WFrame.wr s2 alq (Or.inr (Or.inr (Or.inl ⟨hh0, rfl⟩))) t)
    · rw [L.mem_wr _ _ _ _ alq aln, if_neg qn]; exact m2n
    · rw [L.mem_wr _ _ _ _ alq alp, if_neg qp]; exact m2p
    · intro _; exact L.mem_wr_same alq

/-- The words `create_object` writes for a new TCB `t`, coarsely: the TCB,
the old head's `debug_prev` and the head word. -/
def TcbWC (s : S) (t w : U64) : Prop :=
  Rg t 0 4096 w ∨ (L.mem s (dbgW (L := L) s t) ≠ 0#u64 ∧ w = P1.dpA (L.mem s (dbgW (L := L) s t))) ∨
    w = dbgW (L := L) s t

/-- **`create_object`'s values for a TCB** (module docstring). -/
theorem create_tcb_content {A' : Type} (arI : machine.Arch A') (s : S) (ar : A') (nt base us : U64) (dev : Bool)
    (hnt : nt.val = 1) (ht : TcbOk base) (hna : P1.Aligned (dbgW (L := L) s base))
    (hhd : L.mem s (dbgW (L := L) s base) ≠ 0#u64 → TcbOk (L.mem s (dbgW (L := L) s base)))
    (hsep : L.mem s (dbgW (L := L) s base) ≠ 0#u64 →
      (L.mem s (dbgW (L := L) s base)).val + 4096 ≤ base.val ∨ base.val + 4096 ≤ (L.mem s (dbgW (L := L) s base)).val)
    (hout : ¬ Rg base 0 4096 (dbgW (L := L) s base))
    (hout2 : L.mem s (dbgW (L := L) s base) ≠ 0#u64 →
      ¬ Rg (L.mem s (dbgW (L := L) s base)) 0 4096 (dbgW (L := L) s base))
    (hcd : ¬ Rg base 0 4096 (Sched.curDomA st s)) (hcdal : P1.Aligned (Sched.curDomA st s)) :
    objects.create_object st arI s ar nt base us dev ⦃ res =>
      res.1 = .Thread base ∧ res.2.2 = ar ∧ WFrame (L := L) s res.2.1 (TcbWC (L := L) s base) ∧
      L.mem res.2.1 (dbgW (L := L) s base) = base ∧
      (∀ i : U64, i.val < 24 → L.mem res.2.1 (regA base i) = ctxW i.val) ∧
      L.mem res.2.1 (P1.domA base) = L.mem s (Sched.curDomA st s) ∧
      L.mem res.2.1 (P1.dnA base) = L.mem s (dbgW (L := L) s base) ∧ L.mem res.2.1 (P1.dpA base) = 0#u64 ∧
      (L.mem s (dbgW (L := L) s base) ≠ 0#u64 →
        L.mem res.2.1 (P1.dpA (L.mem s (dbgW (L := L) s base))) = base) ⦄ := by
  have h14 : nt ≠ 14#u64 := by scalar_tac
  have h15 : ¬ nt ≥ 15#u64 := by scalar_tac
  unfold objects.create_object
  have h1 : nt = fl4_abi.consts.object.Tcb := UScalar.eq_of_val_eq (by rw [hnt]; simp [fl4_abi.consts.object.Tcb])
  rw [if_pos h1]
  obtain ⟨s1, hs1, f1, hr1⟩ := spec_exists (init_context_content (L := L) s base ht)
  rw [hs1]; simp only [bind_ok]
  obtain ⟨s2, hs2, f2⟩ := spec_exists (init_fpu_rg (L := L) s1 base ht)
  rw [hs2]; simp only [bind_ok]
  obtain ⟨s3, hs3, f3⟩ := spec_exists (debug_init_rg (L := L) s2 base ht)
  rw [hs3]; simp only [bind_ok]
  rw [spec_eq_ok (Sched.sched.cur_domain.spec' (L := L) s3)]; simp only [bind_ok]
  obtain ⟨s4, hs4, e4⟩ := spec_exists (set_domain_eq (L := L) s3 base (L.mem s3 (Sched.curDomA st s3)))
  rw [hs4]; simp only [bind_ok]
  obtain ⟨ct, hct, -⟩ := spec_exists (cur_thread_spec' (L := L) s4)
  rw [hct]; simp only [bind_ok]
  obtain ⟨s5, hs5, f5⟩ := spec_exists (set_child_name_rg (L := L) s4 base ct ht)
  rw [hs5]; simp only [bind_ok]
  obtain ⟨g1, g2⟩ := ht
  have ald : P1.Aligned (P1.domA base) := by have := domA_v ⟨g1, g2⟩; show _ % 8 = 0; omega
  have f4 : WFrame (L := L) s3 s4 (Rg base 3432 3440) := by
    rw [e4]; exact WFrame.wr s3 ald (by unfold Rg; rw [domA_v ⟨g1, g2⟩]; omega) _
  -- each step's frame inside `[base + lo, base + hi)`, merged
  have mg : ∀ {sa sb : S} {lo hi : Nat} (P : U64 → Prop), WFrame (L := L) sa sb (Rg base lo hi) →
      (∀ w, Rg base lo hi w → P w) → WFrame (L := L) sa sb P := fun _ hf hp => hf.mono hp
  have fA : WFrame (L := L) s s5 (Rg base 0 4096) :=
    (mg _ f1 (fun w h => by unfold Rg at h ⊢; omega)).trans ((mg _ f2 (fun w h => by unfold Rg at h ⊢; omega)).trans
      ((mg _ f3 (fun w h => by unfold Rg at h ⊢; omega)).trans ((mg _ f4 (fun w h => by unfold Rg at h ⊢; omega)).trans
        (mg _ f5 (fun w h => by unfold Rg at h ⊢; omega)))))
  -- the debug list, as seen from `s5`
  have hcpu : tcbCpu (L := L) s5 base = tcbCpu (L := L) s base := by
    unfold tcbCpu
    have hv : (core.num.U64.wrapping_add base 3520#u64).val = base.val + 3520 := by addr_tac
    let P : U64 → Prop := fun w => Rg base 0 4096 w ∧ w.val ≠ base.val + 3520
    have fP : WFrame (L := L) s s5 P :=
      (mg P f1 (fun w h => by unfold Rg at h; exact ⟨by unfold Rg; omega, by omega⟩)).trans
      ((mg P f2 (fun w h => by unfold Rg at h; exact ⟨by unfold Rg; omega, by omega⟩)).trans
      ((mg P f3 (fun w h => by unfold Rg at h; exact ⟨by unfold Rg; omega, by omega⟩)).trans
      ((mg P f4 (fun w h => by unfold Rg at h; exact ⟨by unfold Rg; omega, by omega⟩)).trans
      (mg P f5 (fun w h => by unfold Rg at h; exact ⟨by unfold Rg; omega, by omega⟩)))))
    exact fP.2.2 _ (by show _ % 8 = 0; rw [hv]; omega) (fun h => h.2 hv)
  have hdw : dbgW (L := L) s5 base = dbgW (L := L) s base := by
    unfold dbgW; rw [hcpu, nodeAt_ksb fA.1]
  have hhv : L.mem s5 (dbgW (L := L) s5 base) = L.mem s (dbgW (L := L) s base) := by
    rw [hdw]; exact fA.2.2 _ hna hout
  -- the values at `s5`
  have hcd3 : L.mem s3 (Sched.curDomA st s3) = L.mem s (Sched.curDomA st s) := by
    have e3 : Sched.curDomA st s3 = Sched.curDomA st s := by
      unfold Sched.curDomA; rw [f3.1, f2.1, f1.1]
    rw [e3]
    have f13 : WFrame (L := L) s s3 (Rg base 0 4096) :=
      (mg _ f1 (fun w h => by unfold Rg at h ⊢; omega)).trans ((mg _ f2 (fun w h => by unfold Rg at h ⊢; omega)).trans
        (mg _ f3 (fun w h => by unfold Rg at h ⊢; omega)))
    exact f13.2.2 _ hcdal hcd
  have r5 : ∀ i : U64, i.val < 24 → L.mem s5 (regA base i) = ctxW i.val := by
    intro i hi
    have hv := regA_v ⟨g1, g2⟩ hi
    rw [← hr1 i hi]
    have f15 : WFrame (L := L) s1 s5 (Rg base 448 4096) :=
      (mg _ f2 (fun w h => by unfold Rg at h ⊢; omega)).trans ((mg _ f3 (fun w h => by unfold Rg at h ⊢; omega)).trans
        ((mg _ f4 (fun w h => by unfold Rg at h ⊢; omega)).trans (mg _ f5 (fun w h => by unfold Rg at h ⊢; omega))))
    exact f15.2.2 _ (regA_al ⟨g1, g2⟩ hi) (by unfold Rg; rw [hv]; omega)
  have d5 : L.mem s5 (P1.domA base) = L.mem s (Sched.curDomA st s) := by
    rw [f5.2.2 _ ald (by unfold Rg; rw [domA_v ⟨g1, g2⟩]; omega), e4, L.mem_wr_same ald, hcd3]
  set h := L.mem s (dbgW (L := L) s base) with hh
  obtain ⟨s6, hs6, f6, k1, k2, k3, k4⟩ := spec_exists (debug_append_content (L := L) s5 base ⟨g1, g2⟩
    (by rw [hdw]; exact hna) (by rw [hhv]; exact hhd) (by rw [hhv]; exact hsep) (by rw [hdw]; exact hout)
    (by rw [hhv, hdw]; exact hout2))
  rw [hs6]; simp only [bind_ok, WP.spec_ok]
  rw [hhv] at k2 k4
  rw [hdw] at k1
  -- what `debug_append` leaves alone
  have hD : ∀ w : U64, P1.Aligned w → Rg base 0 3576 w → L.mem s6 w = L.mem s5 w := by
    intro w hw hr
    refine f6.2.2 w hw ?_
    unfold DbgAW
    rw [hhv, hdw]
    rintro (e | e | ⟨hn, e⟩ | e)
    · unfold Rg at hr; rw [e, dnA_v ⟨g1, g2⟩] at hr; omega
    · unfold Rg at hr; rw [e, dpA_v ⟨g1, g2⟩] at hr; omega
    · have hq := hhd hn
      unfold Rg at hr; rw [e, dpA_v hq] at hr; have := hsep hn; omega
    · exact hout (by rw [← e]; unfold Rg at hr ⊢; omega)
  refine ⟨trivial, trivial, ?_, k1, fun i hi => ?_, ?_, k2, k3, k4⟩
  · refine (fA.mono (fun w h => Or.inl h)).trans (f6.mono (fun w hw => ?_))
    unfold DbgAW at hw
    rw [hhv, hdw] at hw
    rcases hw with e | e | ⟨hn, e⟩ | e
    · left; unfold Rg; rw [e, dnA_v ⟨g1, g2⟩]; omega
    · left; unfold Rg; rw [e, dpA_v ⟨g1, g2⟩]; omega
    · exact Or.inr (Or.inl ⟨hn, e⟩)
    · exact Or.inr (Or.inr e)
  · have hv := regA_v ⟨g1, g2⟩ hi
    rw [hD _ (regA_al ⟨g1, g2⟩ hi) (by unfold Rg; rw [hv]; omega)]; exact r5 i hi
  · rw [hD _ ald (by unfold Rg; rw [domA_v ⟨g1, g2⟩]; omega)]; exact d5

end

end

end Fl4Proofs.P3
