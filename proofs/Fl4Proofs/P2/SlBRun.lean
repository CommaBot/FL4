/-
# P2 (line p3mc, gen 15): the sl run at a view start with a homed decided thread is a run on the view's words

At an sl entry state `s` at core `c`'s view (`SlVC`) whose decided thread (`slThr`), when live, is homed on `c` in
`ρ`:

* `trap_home`, `rr_home`: the trap arm's receiver (the handler endpoint's head) and its SC, the ReplyRecv arm's
  replied thread, are homed (the receiver is the decided thread, `slThr_hd_trap`; its SC's `TCB` back-pointer is it,
  `ScExtra0.bound`, so `SlVC.scb`);
* **`sl_acc_v`**: an accepted run is the run on `guard st (SlRS s ∧ SR) (SlWS s ∧ VNW)` (`guard_acc` at `SR` /
  `VNW` with `fltAcc_v` / `rrAcc_v`, met with `sl_acc` by `interp_guard_meet`);
* `sl_homeL`: `sl_home` with the decided thread's homing asked only when it is live;
* **`sl_dec_v`**: a declined run is the run on `guard st (SlRS s ∧ SR) (SlDS s)` (`guard_dec` at `SR` with
  `fltDec_v` / `rrDec_v`, met with `sl_homeL`).

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.SlVDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf)

noncomputable section
open Classical

section run
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **The trap arm's receiver and its SC are homed.** -/
theorem trap_home (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : SlTrap st s) (hH : SlLive st found.1 s → ρ (fld (slThr st found.1 s) oAFFINITY) = c)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {ptr badge dest r : U64}
    (hc : FaultChecks st X (L.curW s) ptr badge dest r) :
    ρ (fld dest oAFFINITY) = c ∧ ρ (fld (L.mem s (scA dest)) 16#u64) = c := by
  have E := F.E
  have Hh := F.Hh
  have hX := F.B.regionOKX
  have hc0 := E.hSt.1
  obtain ⟨sl, x, y, g, gr, hsl, hcap, -⟩ := hc.cap
  rw [tcb_slot_val] at hsl
  obtain rfl := ok_inj_ff hsl
  have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT F.I hS LP hcap
  have lv := slLive_trap ar hA E.hT E.hN E.hcT F.I hS LP hcap hc.ep
  have hdd : dest = slThr st found.1 s := by
    have hd := hc.head
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X ptr), e1] at hd
    exact (ok_inj_ff hd).symm
  have hdA : ρ (fld dest oAFFINITY) = c := by rw [hdd]; exact hH lv
  refine ⟨hdA, ?_⟩
  obtain ⟨hdt, -, -, -⟩ := E.hSd hS a X a1 LP hc
  have HF := here_facts (L := L) hc.here
  obtain ⟨-, -, hXI, -, -⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have hdT : dest ∈ K.toKLayout.heap.tcbs := hdt
  obtain ⟨hcS, htb, -⟩ := hX0.bound dest hdT HF.sc
  have eSc : L.mem X (scA dest) = L.mem s (scA dest) :=
    lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hdt 3464#u64 (by simp) (by simp) (by simp)).2.2
      (not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu hdt (by simp) (by simp) (by simp) (by simp))
  rw [eSc] at hcS htb
  have hz := scs_heap (K := K.toKLayout) hcS
  obtain ⟨-, aT, -, rT⟩ := sc_off hX hz (o := layout.sc.TCB) (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
  have rT' : region K.toKLayout (scTcbA (L.mem s (scA dest))) = .sc (L.mem s (scA dest)) := rT
  have eT : L.mem X (scTcbA (L.mem s (scA dest))) = L.mem s (scTcbA (L.mem s (scA dest))) :=
    lp_mem ar hA E.hT E.hN E.hcT LP aT (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rT']; intro c h; cases h) (by rw [rT']; intro h; cases h))
  exact V.scb _ hcS (by rw [← eT, htb]; exact fun e => (E.hT _ hdT).ne0 (by rw [e]; rfl))

/-- **The ReplyRecv arm's replied thread is homed.** -/
theorem rr_home (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s)
    (hS : ¬ SlTrap st s) (hH : SlLive st found.1 s → ρ (fld (slThr st found.1 s) oAFFINITY) = c)
    {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) : ρ (fld u oAFFINITY) = c := by
  have E := F.E
  have eu : u = slThr st found.1 s := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT F.I hS LP] at h1
    exact h1
  have lv : SlLive st found.1 s := slLive_rr (st := st) hS (by rw [← eu]; exact u_ne0 hc.u0)
  rw [eu]; exact hH lv

set_option maxHeartbeats 8000000 in
/-- **An accepted run at a view start with a homed decided thread is a run on the view's words**. -/
theorem sl_acc_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hH : SlLive st found.1 s → ρ (fld (slThr st found.1 s) oAFFINITY) = c)
    {a : A} {s1 : S} {a1 : A} (h : syscall.handle_syscall_local st ar s a n found = ok (true, s1, a1)) :
    syscall.handle_syscall_local
      (guard st (fun q => SlRS (st := st) K.toKLayout Locks s q ∧ SR K c ρ q)
        (fun q => SlWS (st := st) K.toKLayout Locks s q ∧ VNW K c ρ q)) ar s a n found = ok (true, s1, a1) := by
  have B := F.B
  have E := F.E
  have hK := V.hK
  have hX := B.regionOKX
  have hc0 := E.hSt.1
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have g1 := sl_acc ar hA F.P h
  have hhd : ∀ X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SR K c ρ) X csc := by
    intro X a1 csc LP hcs
    obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have e : csc = L.cscW s := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
      rw [← ok_inj_ff hcs]; exact ecs
    subst e
    exact rdHead_v ar hA V B E F.Hh LP F.Hh.cs V.csc
  have stW : ∀ t, K.toKLayout.heap t = some .tcb → ρ (fld t oAFFINITY) = c →
      VNW K c ρ (core.num.U64.wrapping_add t layout.tcb.STATE) := fun t ht ha =>
    vnw_tcb hK hX ht ha (o := layout.tcb.STATE) (by rw [st_val]; omega) (by rw [st_val]; omega) (by rw [st_val])
      (by rw [st_val]; omega)
  have g2 : syscall.handle_syscall_local (guard st (SR K c ρ) (VNW K c ρ)) ar s a n found = ok (true, s1, a1) :=
    syscall.handle_syscall_local.guard_acc (gS := guard st (SR K c ρ) (VNW K c ρ))
      (R := SR K c ρ) (W := VNW K c ρ) ar hA E.hT E.hN E.hcT (preAcc_v ar V B E) hhd (E.hI a) (E.hAs a)
      (fun h' => E.hrecv h' a) (fun h' => E.hF h' a) (fun h' => E.hy0f h' a) (fun h' => E.hTm h' a)
      (fun h' X a1 LP {_p _b _d _r} hc =>
        fltAcc_v ar hA F V h' LP hc (trap_home ar hA F V h' hH LP hc).1 (trap_home ar hA F V h' hH LP hc).2)
      (fun h' X a1 LP {_p _b _d _r} hc =>
        ⟨SWr.of_W (W := VNW K c ρ) (stW _ hc0 V.cur),
          fun _ _ => SWr.of_W (W := VNW K c ρ) (stW _ (E.hSd h' a X a1 LP hc).1
            (trap_home ar hA F V h' hH LP hc).1)⟩)
      (fun h' => E.hPl h' a) (fun h' => E.hrz h' a) (fun h' => E.hy0r h' a)
      (fun h' X a1 LP u usc hc => rrAcc_v ar hA F V h' LP hc (rr_home ar hA F h' hH LP hc))
      (fun h' X a1 LP u usc hc =>
        have hu := (E.hSu h' a X a1 LP u usc hc).1
        have hua := rr_home ar hA F h' hH LP hc
        { tR := SWr.of_W (W := VNW K c ρ) (stW _ hc0 V.cur)
          tN := SWr.of_W (W := VNW K c ρ) (stW _ hc0 V.cur)
          tB := fun _ _ => gst_write (W := VNW K c ρ) (stW _ hc0 V.cur)
          bl := fun _ => gst_write (W := VNW K c ρ)
            (vnw_tcb hK hX hc0 V.cur (o := 3336#u64) (by simp) (by simp) (by simp) (by simp))
          uI := SWr.of_W (W := VNW K c ρ) (stW _ hu hua)
          uR := SWr.of_W (W := VNW K c ρ) (stW _ hu hua)
          uN := SWr.of_W (W := VNW K c ρ) (stW _ hu hua) })
      h
  rw [hp] at g1 g2 ⊢
  exact interp_guard_meet _ (sl_noZero n found) s a _ g1 g2

set_option maxHeartbeats 4000000 in
/-- **`sl_home` with the decided thread's homing asked only when it is live.** -/
theorem sl_homeL (hA : P0.ArchTotal ar) {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}
    {Kl : KLayout} {s : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar Kl Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (I : SlThrIn (st := st) Kl Locks found.1 s) (D : SlDecIn (st := st) ar Kl Locks found s)
    (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true)
    (hh : SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s) :
    syscall.handle_syscall_local (guard st (SlRS (st := st) Kl Locks s) (SlDS (L := L) s)) ar s a n found = ok r := by
  have hp : PreDec (L := L) (SlRS (st := st) Kl Locks s) (SlDS (L := L) s) s :=
    ⟨fun o h1 h2 => (E.preG.nd o h1 h2).1, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), E.preG.fl, E.preG.nx,
      Or.inl rfl⟩
  refine syscall.handle_syscall_local.guard_dec (gS := guard st (SlRS (st := st) Kl Locks s) (SlDS (L := L) s))
    hA E.hT E.hN E.hcT hp (fun X a1 csc LP e => E.hhd a X a1 csc LP e) ?_ ?_ h
  · intro hS X a1 n' LP hf
    refine fastpath.fault.guard_dec (gS := guard st (SlRS (st := st) Kl Locks s) (SlDS (L := L) s))
      (FltDec.of (D.fT hS a X a1 LP) ?_) hf hn
    intro ptr bb x y g gr hc hst d hd
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X ptr), e1] at hd
    rw [← ok_inj_ff hd]
    have lv := slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc hst
    exact D.fD hS lv (hh lv) a X a1 LP
  · intro hS X a1 LP hf
    refine fastpath.reply_recv_found.guard_dec (gS := guard st (SlRS (st := st) Kl Locks s) (SlDS (L := L) s))
      (RrDec.of (D.rT hS a X a1 LP) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hu, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    rw [h1]
    exact D.rU hS lv (hh lv) a X a1 LP

set_option maxHeartbeats 8000000 in
/-- **A declined run at a view start with a homed decided thread is a run on the view's readable words**. -/
theorem sl_dec_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hH : SlLive st found.1 s → ρ (fld (slThr st found.1 s) oAFFINITY) = c)
    {a : A} {r : Bool × S × A} (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true) :
    syscall.handle_syscall_local
      (guard st (fun q => SlRS (st := st) K.toKLayout Locks s q ∧ SR K c ρ q)
        (fun q => SlDS (L := L) s q ∧ True)) ar s a n found = ok r := by
  have B := F.B
  have E := F.E
  have hK := V.hK
  have hX := B.regionOKX
  have hK0 := B.regionOK
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have hh : SlLive st found.1 s → L.mem s (affA (slThr st found.1 s)) = L.cpu s := fun lv => by
    have ht := F.N.hthr lv
    obtain ⟨r0, -, a0⟩ := hX.tcbW _ ht 3520#u64 (by simp) (by simp) (by simp)
    have r0' : region K.toKLayout (affA (slThr st found.1 s)) = .tcb (slThr st found.1 s) := r0
    have a0' : Aligned (affA (slThr st found.1 s)) := a0
    rw [V.hm _ a0' (hX.kern _ (by rw [r0']; intro h; cases h)), OwnMap.affA_fld, CoreView.view_aff hK0 ht, V.cpu]
  have g1 := sl_homeL ar hA F.P F.I F.D h hn hh
  have g2 : syscall.handle_syscall_local (guard st (SR K c ρ) (fun _ => True)) ar s a n found = ok r := by
    refine syscall.handle_syscall_local.guard_dec (gS := guard st (SR K c ρ) (fun _ => True)) hA E.hT E.hN E.hcT
      (preDec_v ar V B E) (fun X a1 csc LP hcs => ?_)
      (fun hS X a1 n' LP hf => fastpath.fault.guard_dec (fltDec_v ar hA F V hS hH LP) hf hn)
      (fun hS X a1 LP hf => fastpath.reply_recv_found.guard_dec (rrDec_v ar hA F V hS hH LP) hf hn) h
    obtain ⟨-, -, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have e : csc = L.cscW s := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X)] at hcs
      rw [← ok_inj_ff hcs]; exact ecs
    subst e
    exact rdHead_v ar hA V B E F.Hh LP F.Hh.cs V.csc
  rw [hp] at g1 g2 ⊢
  exact interp_guard_meet _ (sl_noZero n found) s a _ g1 g2

end run

end
end Fl4Proofs.P2.E2EP
