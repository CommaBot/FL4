/-
# P2 (line lvm, gen 6): **`local_vm_exit` under `ownV`: the entry facts, `acc`, the declines and `move`**

For rule 7's map `OwnMapV.ownV K` and gen 5's sets `VexitRS` / `VexitWS` / `VexitDS = IrqDec`:

* `VexitEnt`: the entry facts (P1's invariant and the layout's, below);
* `tmw_ownV`, `vexit_rd`: every `IrqRd` word is readable under `ownV` (as `tmw_own` / `irq_rd_own` for `own`, each
  word in a typed region, hence no VCPU word: `rpV`); the VCPU's `PENDING` is `lock v`'s (`rpermV_vcpu`), the
  bound notification's `TAIL_STATE` its bound thread's home core's (`ntfn_tail_rd`);
* **`vexit_acc_own_np`**: `PathObl.acc` of an accepted run whose VCPU has no pending exit, on
  `guard st (VexitRS …) (VexitWS …)` (`vexit_accG_np`, writes by `irq_wr_own` and `wpermV_of_own'`);
* **`vexit_dec_own`**: a declined run on `guard st (VexitRS …) (IrqDec st s)` (`vexit_decG`);
* **`vexit_move_np`**: `PathObl.move` of an accepted run with no pending exit: the run on the checked store whose
  writes are `ownV`'s `StepOK` (`StWrOKV`) is the real one (`vexit_accG_np`; every write is an `IrqWr` word other than
  the current thread's `STATE`, deciding nothing: `irq_wr_nondec`, `stepOK_nondec`, `stepOKV_of_stepOK`), and
  `interp_gd` turns it into the run on `mguard` (`IsProg` [P]).

Premises (fields of `VexitEnt`):
* `inv` [J]: P1's invariant at the entry (`BXI`, as `IrqEnt.inv`; VT-x entries are outside the P1 top, P3's
  `P3Place.vmchk` [P]);
* `lay`, `ntw`, `cs` [J]: the layout's regions (`StLay`, and `IrqLay`'s notification and slot fields; `cs` over the
  six TCB slots, `k < 192`, as `IrqLay.cs` since p2lf gen14: int13 narrowed it from `k < 256`);
* `aff` [J]: p2j's `AffSc`; `curAff`, `cscCore` [J]: p2j's `OwnJ.curAff` / `EntryInv.cur_sc_core` (as `IoPre`'s);
* `ksv` [J]: no VCPU covers `CUR_DOMAIN` / `DOMAIN_TIME` (the kernel-state block holds no VCPU);
* `vin` [J]: the exiting VCPU `v` is a VCPU of the layout and `PENDING` lies inside it. It stays [J] (lvm gen 8,
  vlift gen 4): P3 covers native threads only (`JExt.nat` / `JExt.vw`), `SpecCover.arch` pins neither the object
  size 15 nor the map `H` → spec, so closing it needs a VT-x joint invariant (line vlift's `vfit_ofK` / `pusr_ofK`
  derive `VexitPEnt.vfit` / `.pusr` from `VcpuHeap` [J] and `vin`);
* `vlk` [P]: fl4-sync's `local_vm_exit` holds `lock v` when it calls the body;
* `vfar`, `nfar` [J]: P1's typed heap: `v`'s `PENDING` word and the bound notification's `TAIL_STATE` lie outside
  every TCB, node and SC (`VFar`).
-/
import Fl4Proofs.P2.AccessLvmWalk
import Fl4Proofs.P2.AccessLvmDw
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap Fl4Proofs.P2.PathObl
open Fl4Proofs.P2.OwnMapV (KLayoutV ownV InVcpu VcpuGate RegionOKV UserOKV rpermV_of_own rpermV_vcpu
  wpermV_of_own' stepOKV_of_stepOK)
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}

/-- **The entry facts of `local_vm_exit`** (module docstring) for the exiting VCPU `v` and the glue's notification
`n`, with the glue's locks `lk`. -/
structure VexitEnt (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (lk : S → U64 → Prop) (v n : U64) (s : S) :
    Prop where
  inv : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  lay : StLay K.toKLayout st T Scs Z s
  ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p
  cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
    region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
      (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16
  aff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t)
  curAff : L.mem s (affA (L.curW s)) = L.cpu s
  cscCore : L.mem s (scCoreA (L.cscW s)) = L.cpu s
  ksv : (¬ ∃ w, InVcpu K w (core.num.U64.wrapping_add (L.ksb s) layout.ks.CUR_DOMAIN)) ∧
    ¬ ∃ w, InVcpu K w (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)
  vin : v ≠ 0#u64 → InVcpu K v (core.num.U64.wrapping_add v vcpu.PENDING)
  vlk : v ≠ 0#u64 → lk s v
  vfar : v ≠ 0#u64 → VFar st T Cs Scs Z s (core.num.U64.wrapping_add v vcpu.PENDING)
  nfar : ∀ n', L.mem s (boundA (L.curW s)) = n' → n' ≠ 0#u64 →
    VFar st T Cs Scs Z s (core.num.U64.wrapping_add n' layout.ntfn.TAIL_STATE)

/-- A word in a typed region is no VCPU word, so `own`'s read permission is `ownV`'s. -/
theorem rpV (hK : RegionOKV K) {m : U64 → U64} {c x : U64} {lk : U64 → Prop}
    (hr : region K.toKLayout x ≠ .none) (h : RPerm (own K.toKLayout) c lk m x) : RPerm (ownV K) c lk m x :=
  rpermV_of_own (fun ⟨w, hw⟩ => hr (hK.none w x hw)) h

/-- **The earliest armed thread's words are readable under `ownV`** (`tmw_own`'s proof, each word in a TCB or
notification region). -/
theorem tmw_ownV (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    {lk : U64 → Prop} {w : U64}
    (hne : L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) ≠ 0#u64)
    (hw : TmWords st s (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) w) :
    RPerm (ownV K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have treg : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 →
      region K.toKLayout (core.num.U64.wrapping_add x k) ≠ .none := fun hx h1 h2 => by
    have e := hL.tcb _ hx _ h1 h2
    unfold fld at e
    rw [e]; simp
  have gate : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → GateField k.val →
      RPerm (ownV K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := fun hx h1 h2 hg =>
    rpV hK (treg hx h1 h2) (Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg]))
  have home : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → L.mem s (affA x) = L.cpu s →
      ¬ TimerField k.val → ¬ GField k.val →
      RPerm (ownV K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := @fun x k hx h1 h2 ha hti hg => by
    refine rpV hK (treg hx h1 h2) ?_
    have e := hL.own_tcb hT (L.mem s) hx h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg hti, if_neg hg]; exact Or.inl ha
  obtain ⟨q1, harm⟩ := tmin_facts (BXI.blk hI) h0.cur hne
  rcases hw with ⟨k, hk, rfl⟩ | ⟨hh, ⟨k, hk, rfl⟩ | ⟨hb, rfl | rfl⟩⟩
  · rcases hk with hk | hk | hk | hk
    · exact gate q1 (by omega) (by omega) (by unfold GateField; omega)
    rotate_left 2
    · exact gate q1 (by omega) (by omega) (by unfold GateField; omega)
    all_goals
      refine rpV hK (treg q1 (by omega) (by omega)) ?_
      have e := hL.own_tcb hT (L.mem s) q1 (k := k) (by omega) (by omega)
      unfold fld at e
      refine Or.inl ?_
      rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
        if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
        if_pos (show (L.mem s (fld (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) oTIMER_DEADLINE)).val ≠ 0
          from fun h => harm.1 (UScalar.eq_of_val_eq h))]
      have e2 := harm.2
      rw [Nat.shiftRight_eq_div_pow] at e2
      exact MoveTimer.treeCore_of (c := L.cpu s) e2
  · have ha : L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = L.cpu s := by
      have e := hh.1
      rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s _)] at e
      exact ok_inj_ff e
    exact home q1 (by omega) (by omega) ha (by unfold TimerField; omega) (by unfold GField; omega)
  all_goals
    have ha : L.mem s (affA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))) = L.cpu s := by
      have e := hh.1
      rw [eq_of_spec_fd (obj.Tcb.affinity.spec (L := L) s _)] at e
      exact ok_inj_ff e
    have hNt := hI.2.2.1.2.2.bnd _ q1 hb
    have hbt := hI.2.2.1.2.2.bs.tb _ q1 hb
    obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
    have nown : ∀ k : U64, k.val < 64 →
        own K.toKLayout (L.mem s) (core.num.U64.wrapping_add
          (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) k) =
        ntfnOwner K.toKLayout (L.mem s) (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN))))
          k.val := by
      intro k hk
      simp only [own, ntw _ hNt k hk]
      rw [ntfn_word_val p1 p2 hk, Nat.add_sub_cancel_left]
  · refine rpV hK (by rw [ntw _ hNt _ (by simp [layout.ntfn.TAIL_STATE])]; simp) ?_
    have e := nown layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
    have eB : L.mem s (fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64) =
        L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN) := by
      have eA : fld (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) 24#u64 =
          ntfnBtA (L.mem s (boundA (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)))) := by
        unfold fld ntfnBtA layout.ntfn.BOUND_TCB
        rfl
      rw [eA]; exact hbt
    have ht : K.heap (L.mem s (L.nodeAt s (L.cpu s) layout.node.TIMER_MIN)) = some .tcb :=
      hK.base.tcbOf _ _ (hL.tcb _ q1 3328#u64 (by simp) (by simp))
    have hv : layout.ntfn.TAIL_STATE.val = 8 := by simp [layout.ntfn.TAIL_STATE]
    refine Or.inl ?_
    rw [e, hv, ntfnOwner, if_neg (by omega), eB, if_pos ht]
    exact ha
  · refine rpV hK (by rw [ntw _ hNt _ (by simp [layout.ntfn.BOUND_TCB])]; simp) ?_
    have e := nown layout.ntfn.BOUND_TCB (by simp [layout.ntfn.BOUND_TCB])
    have hv : layout.ntfn.BOUND_TCB.val = 24 := by simp [layout.ntfn.BOUND_TCB]
    refine Or.inr ?_
    unfold GateOnly
    rw [e, hv, ntfnOwner, if_pos rfl]

/-- **Every word of `IrqRd` is readable under `ownV`** at a `local_vm_exit` entry (`irq_rd_own`'s proof). -/
theorem vexit_rd (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (cs : ∀ k : U64, k.val < 192 → k.val % 32 < 16 → ∃ p,
      region K.toKLayout (core.num.U64.wrapping_add (L.curW s) k) = .slot p ∧ TcbSlot K.toKLayout p ∧
        (core.num.U64.wrapping_add (L.curW s) k).val - p.val < 16)
    (hAff : ∀ t ∈ T, L.mem s (scA t) ≠ 0#u64 → L.mem s (scCoreA (L.mem s (scA t))) = L.mem s (affA t))
    (haff : L.mem s (affA (L.curW s)) = L.cpu s) (hcore : L.mem s (scCoreA (L.cscW s)) = L.cpu s)
    {lk : U64 → Prop} {w : U64} (h : IrqRd st Z s w) :
    RPerm (ownV K) (L.cpu s) lk (L.mem s) w := by
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced T := h0.tcbs
  have hcT : L.curW s ∈ T := h0.curT
  have hcs : L.cscW s ∈ Scs := hI.2.2.1.2.2.cur
  have treg : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 →
      region K.toKLayout (core.num.U64.wrapping_add x k) ≠ .none := fun hx h1 h2 => by
    have e := hL.tcb _ hx _ h1 h2
    unfold fld at e
    rw [e]; simp
  have scw : ∀ {p b : U64}, p ∈ Scs → InSC p (Z p) b → L.mem s (scCoreA p) = L.cpu s →
      RPerm (ownV K) (L.cpu s) lk (L.mem s) b := fun hp hb hc => by
    refine rpV hK (by rw [hL.sc _ hp _ hb]; simp) ?_
    have e := sc_own hL hp hb hc
    split at e
    · exact Or.inr e
    · exact Or.inl (held_core e)
  have gate : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → GateField k.val →
      RPerm (ownV K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := fun hx h1 h2 hg =>
    rpV hK (treg hx h1 h2) (Or.inr (by
      have e := hL.own_tcb hT (L.mem s) hx h1 h2
      unfold fld at e
      unfold GateOnly; rw [e, tcbOwner, if_pos hg]))
  have home : ∀ {x k : U64}, x ∈ T → 256 ≤ k.val → k.val < 4096 → L.mem s (affA x) = L.cpu s →
      ¬ TimerField k.val → ¬ GField k.val →
      RPerm (ownV K) (L.cpu s) lk (L.mem s) (core.num.U64.wrapping_add x k) := @fun x k hx h1 h2 ha hti hg => by
    refine rpV hK (treg hx h1 h2) ?_
    have e := hL.own_tcb hT (L.mem s) hx h1 h2
    unfold fld at e
    unfold RPerm GateOnly
    rw [e]
    unfold tcbOwner
    by_cases hga : GateField k.val
    · rw [if_pos hga]; exact Or.inr rfl
    · rw [if_neg hga, if_neg hti, if_neg hg]; exact Or.inl ha
  rcases h with ⟨o, ho, -, rfl⟩ | ⟨k, h1, h2, -, h4, h5, h6, rfl⟩ | h | ⟨hne, rfl | h⟩ | ⟨hne, hw⟩ |
      ⟨k, hk, hk32, -, rfl⟩
  · exact rpV hK (by rw [hL.nd o ho]; simp) (Or.inl (held_core (hL.own_node _ ho)))
  · exact home hcT h1 h2 haff (by unfold TimerField; omega) (by unfold GField; omega)
  · exact scw hcs h hcore
  · obtain ⟨r1, -, -, -, -⟩ := rel_facts hI hne
    exact gate r1 (by simp) (by simp) (by simp [GateField])
  · obtain ⟨r1, r2, r3, r4, -⟩ := rel_facts hI hne
    exact scw r4 h (by rw [hAff _ r1 r3, r2])
  · exact tmw_ownV hK hI hL ntw hne hw
  · obtain ⟨p, hr, hts, hlt⟩ := cs k hk hk32
    refine rpV hK (by rw [hr]; simp) (Or.inr ?_)
    unfold GateOnly
    simp only [own, hr, slotOwner]
    rw [if_neg (by omega), if_pos hts]

/-- The current thread's bound notification's `TAIL_STATE` is readable: its bound thread's home core's. -/
theorem ntfn_tail_rd (hK : RegionOKV K) {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hL : StLay K.toKLayout st T Scs Z s)
    (ntw : ∀ p ∈ Nt, ∀ k : U64, k.val < 64 → region K.toKLayout (core.num.U64.wrapping_add p k) = .ntfn p)
    (haff : L.mem s (affA (L.curW s)) = L.cpu s) {lk : U64 → Prop}
    (hb : L.mem s (boundA (L.curW s)) ≠ 0#u64) :
    Aligned (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) layout.ntfn.TAIL_STATE) ∧
      RPerm (ownV K) (L.cpu s) lk (L.mem s)
        (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) layout.ntfn.TAIL_STATE) := by
  have h0 := hI.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := h0.curT
  have hNt := hI.2.2.1.2.2.bnd _ hcT hb
  have hbt := hI.2.2.1.2.2.bs.tb _ hcT hb
  obtain ⟨p1, p2⟩ := hI.2.2.1.1.ntP _ hNt
  have hv : layout.ntfn.TAIL_STATE.val = 8 := by simp [layout.ntfn.TAIL_STATE]
  refine ⟨by unfold Aligned; rw [ntfn_word_val p1 p2 (by rw [hv]; omega)]; omega,
    rpV hK (by rw [ntw _ hNt _ (by rw [hv]; omega)]; simp) (Or.inl ?_)⟩
  have e : own K.toKLayout (L.mem s) (core.num.U64.wrapping_add (L.mem s (boundA (L.curW s))) layout.ntfn.TAIL_STATE) =
      ntfnOwner K.toKLayout (L.mem s) (L.mem s (boundA (L.curW s))) layout.ntfn.TAIL_STATE.val := by
    simp only [own, ntw _ hNt _ (by rw [hv]; omega)]
    rw [ntfn_word_val p1 p2 (by rw [hv]; omega), Nat.add_sub_cancel_left]
  have eB : L.mem s (fld (L.mem s (boundA (L.curW s))) 24#u64) = L.curW s := by
    have eA : fld (L.mem s (boundA (L.curW s))) 24#u64 = ntfnBtA (L.mem s (boundA (L.curW s))) := by
      unfold fld ntfnBtA layout.ntfn.BOUND_TCB
      rfl
    rw [eA]; exact hbt
  have ht : K.heap (L.curW s) = some .tcb := hK.base.tcbOf _ _ (hL.tcb _ hcT 3328#u64 (by simp) (by simp))
  rw [e, hv, ntfnOwner, if_neg (by omega), eB, if_pos ht]
  exact haff

/-- `v`'s `PENDING` is readable by the holder of `lock v`. -/
theorem pending_rd (hK : RegionOKV K) {m : U64 → U64} {c v : U64} {lk : U64 → Prop}
    (hin : InVcpu K v (core.num.U64.wrapping_add v vcpu.PENDING)) (hl : lk v) :
    RPerm (ownV K) c lk m (core.num.U64.wrapping_add v vcpu.PENDING) := by
  refine rpermV_vcpu hK hin ?_ hl
  have h1 := hin.2.1
  have h2 := hin.2.2
  have hvb : v.val < 2 ^ 64 := by scalar_tac
  have hv : (core.num.U64.wrapping_add v vcpu.PENDING).val = v.val + 20520 := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits, UScalar.size] at h1 h2 ⊢
    omega
  rw [hv]
  unfold VcpuGate
  omega

variable {A : Type} (ar : machine.Arch A) {lk : S → U64 → Prop} {v n : U64}

/-- **`acc` of an accepted `local_vm_exit` with no pending exit** under `ownV` (module docstring). -/
theorem vexit_acc_own_np (hA : P0.ArchTotal ar) (hK : RegionOKV K) {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (VexitWS K st lk s)) ar s a v n =
      ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -⟩ := vexit_split ar h
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  have hcT : L.curW s ∈ T := hI.1.choose_spec.choose_spec.curT
  refine vexit_accG_np (gS := guard st (VexitRS K st lk s) (VexitWS K st lk s)) (R := VexitRS K st lk s)
    (W := VexitWS K st lk s) ar hA hI
    (fun hok w ha hw => ⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hok.aff hok.core hw)⟩)
    (fun hok w ha hw _ => ⟨ha, Or.inr (wpermV_of_own' hK (irq_wr_own hI hL hok hw))⟩)
    (fun _ => ⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩)
    (fun _ => ⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩)
    ⟨(hE.vfar hv0).1.1, Or.inr (pending_rd hK (hE.vin hv0) (hE.vlk hv0))⟩
    (fun hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨q1, Or.inr q2⟩)
    (hE.vfar hv0) (fun hn => hE.nfar n hbn hn) hp0 h

/-- **A declined `local_vm_exit`** on `guard st (VexitRS …) (IrqDec st s)` (module docstring). -/
theorem vexit_dec_own (hA : P0.ArchTotal ar) (hK : RegionOKV K) {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (false, s', a')) :
    localvm.handle_vcpu_exit_local (guard st (VexitRS K st lk s) (IrqDec st s)) ar s a v n =
      ok (false, s', a') := by
  have hI := hE.inv
  have hL := hE.lay
  exact vexit_decG (gS := guard st (VexitRS K st lk s) (IrqDec st s)) (R := VexitRS K st lk s)
    (W := IrqDec st s) ar hA hI
    (fun w ha hw => ⟨ha, Or.inr (vexit_rd hK hI hL hE.ntw hE.cs hE.aff hE.curAff hE.cscCore hw)⟩)
    ⟨hL.domA, Or.inr (rpermV_of_own hE.ksv.1 (rperm_none hL.dom _))⟩
    ⟨hL.dtmA, Or.inr (rpermV_of_own hE.ksv.2 (rperm_none hL.dtm _))⟩
    (fun hv0 => ⟨(hE.vfar hv0).1.1, Or.inr (pending_rd hK (hE.vin hv0) (hE.vlk hv0))⟩)
    (fun n' hbn hn => by
      rw [← hbn] at hn ⊢
      obtain ⟨q1, q2⟩ := ntfn_tail_rd (lk := lk s) hK hI hL hE.ntw hE.curAff hn
      exact ⟨q1, Or.inr q2⟩)
    (Or.inl rfl) (Or.inr rfl) h

/-- The checked store's per-write test for `ownV`: the write passes `StepOK`. -/
def StWrOKV (st : machine.Store S) [L : LawfulStore st] (K : KLayoutV) (m : U64 → U64) (c : U64)
    (lk : U64 → Prop) (x : S) (q w : U64) : Prop :=
  StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) c lk (L.mem x)
    (L.mem (L.wr x q w))

/-- **`move` of an accepted `local_vm_exit` with no pending exit** under `ownV` (module docstring). -/
theorem vexit_move_np (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K) {m : U64 → U64}
    {F : ∀ {A : Type}, machine.Arch A → machine.Store S → S → A → Result (Bool × S × A)} {p : SProg Bool}
    (hF : IsProg F p) (eF : ∀ mm : machine.Store S, F ar mm = fun s a => localvm.handle_vcpu_exit_local mm ar s a v n)
    {s s' : S} {a a' : A}
    (hE : VexitEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk v n s)
    (hp0 : vcpu.get st s v vcpu.PENDING = ok 0#u64)
    (h : localvm.handle_vcpu_exit_local st ar s a v n = ok (true, s', a')) :
    localvm.handle_vcpu_exit_local (mguard st
      (fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s) (lk s)
        (L.mem x) (L.mem y))) ar s a v n = ok (true, s', a') := by
  obtain ⟨-, -, hv0, -, en, -⟩ := vexit_split ar h
  have hbn : L.mem s (boundA (L.curW s)) = n := by
    rw [eq_of_spec_fd (obj.Tcb.bound_ntfn.val (L := L) s _)] at en; exact ok_inj_ff en
  have hI := hE.inv
  have hL := hE.lay
  have hg : localvm.handle_vcpu_exit_local (gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) ar s a v n =
      ok (true, s', a') :=
    vexit_accG_np (gS := gd st (fun _ => True) (StWrOKV st K m (L.cpu s) (lk s))) (R := fun _ => True)
      (W := WAll (StWrOKV st K m (L.cpu s) (lk s))) ar hA hI (fun _ _ _ _ => trivial)
      (fun _ w ha hw hn x _ => stepOKV_of_stepOK hK
        (stepOK_nondec hK.base hU.base ha (irq_wr_nondec hK.base hI hL hw hn)))
      (fun _ => trivial) (fun _ => trivial) trivial (fun _ => trivial)
      (hE.vfar hv0) (fun hn => hE.nfar n hbn hn) hp0 h
  have eP : ∀ mm : machine.Store S, localvm.handle_vcpu_exit_local mm ar s a v n = interp mm ar p s a := by
    intro mm
    have e1 := congrFun (congrFun (eF mm) s) a
    have e2 := congrFun (congrFun (hF A ar mm) s) a
    try simp only at e1
    rw [← e1]
    exact e2
  rw [eP] at hg
  rw [eP]
  exact interp_gd (R := fun _ => True) (P := StWrOKV st K m (L.cpu s) (lk s))
    (Q := fun x y => StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) (L.cpu s)
      (lk s) (L.mem x) (L.mem y)) (I := fun _ => True)
    (fun x q w x' _ hq hw => by
      rw [L.write_eq] at hw
      have e := ok_inj_ff hw
      subst e
      exact ⟨hq, trivial⟩) p s a _ trivial hg

end

end Fl4Proofs.P2
