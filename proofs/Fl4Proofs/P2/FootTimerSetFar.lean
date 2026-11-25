/-
# P2: `TCB_SetTimer` on a thread of this core armed in another core's tree declines

`set_timer_far`: in any state that has this core's tree, an armed target outside it: the run declines at
`set_timer_target_ok`, whatever deadline it reads, having written nothing and read only aligned words.

No named premises.
-/
import Fl4Proofs.P2.FootTimerSetDec
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1
open Fl4Proofs.P2.Serial (Owner)
open Fl4Proofs.P2.OwnMap
open Fl4Proofs.P2.PathObl (guard RPerm WPerm HeldBy GateOnly ScAcc rhA tmA RdHead tr_bind tr_bind_same tr_ite)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {A : Type} (ar : machine.Arch A)

/-- **A target of this core armed elsewhere: the run declines**, writing nothing (module docstring). -/
theorem set_timer_far {s : S} {a : A} {n : I64} {target : U64} {r : Bool × S × A} {W0 : TRB.RBT}
    (hT : TcbPlaced T) (hN : NodePlaced st T s (L.cpu s)) (hcT : L.curW s ∈ T) (htg : target ∈ T)
    (ct : CoreTree st T s (L.cpu s) W0) (hk : target ∉ W0.keys) (hd : L.mem s (tdA target) ≠ 0#u64)
    (h : localtimer.handle_set_timer_local st ar s a n target = ok r) :
    r.1 = false ∧ localtimer.handle_set_timer_local (guard st Aligned (fun _ => False)) ar s a n target = ok r := by
  have key : localtimer.set_timer_target_ok st s (L.cpu s) target ≠ ok true := by
    intro e
    unfold localtimer.set_timer_target_ok at e
    obtain ⟨i, -, e⟩ := bind_eq_ok e
    split at e
    · simp at e
    obtain ⟨d, ed, e⟩ := bind_eq_ok e
    rw [td_ok] at ed
    have hdv := ok_inj_ff ed
    split at e
    · rename_i h0; exact hd (hdv.trans h0)
    obtain ⟨b, eb, e⟩ := bind_eq_ok e
    cases b
    · simp at e
    · exact hk (in_core_found ct eb)
  have ht' := hT _ hcT
  have nA : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Aligned (L.nodeAt s (L.cpu s) o) := fun o h1 h2 =>
    nodeAt_aligned hN h1 h2
  have fA : ∀ {x k : U64}, x ∈ T → k.val < 4096 → k.val % 8 = 0 → Aligned (core.num.U64.wrapping_add x k) :=
    fun hx h1 h2 => field_aligned (hT _ hx) h1 h2
  have gtgt : ∀ b, localtimer.set_timer_target_ok st s (L.cpu s) target = ok b →
      localtimer.set_timer_target_ok (guard st Aligned (fun _ => False)) s (L.cpu s) target = ok b := fun b eb =>
    set_timer_target_ok.guard ct (fun w hw => by
      rcases hw with rfl | rfl | ⟨y, hy, rfl | rfl | rfl⟩
      · exact nA _ (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])
      · exact nA _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
      · exact fA (ct.inT y hy) (by simp) (by simp)
      · exact fA (ct.inT y hy) (by simp) (by simp)
      · exact fA (ct.inT y hy) (by simp) (by simp)) (fA htg (by simp) (by simp)) (fA htg (by simp) (by simp))
      (fA htg (by simp) (by simp)) eb
  obtain ⟨b0, s0, a0⟩ := r
  have hb : b0 = false := by
    cases b0
    · rfl
    exfalso
    unfold localtimer.handle_set_timer_local at h
    try simp only [lift, bind_ok] at h
    obtain ⟨t, -, h⟩ := bind_eq_ok h
    obtain ⟨cpu, ecpu, h⟩ := bind_eq_ok h
    rw [L.cur_cpu_eq] at ecpu
    have hcpu : cpu = L.cpu s := (ok_inj_ff ecpu).symm
    subst hcpu
    obtain ⟨info, -, h⟩ := bind_eq_ok h
    rw [num_domains_ne_one_false] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    by_cases g1 : (n != fl4_abi.syscall.SysCall) = true
    · rw [if_pos g1] at h; simp at h
    rw [if_neg g1] at h
    obtain ⟨i, -, h⟩ := bind_eq_ok h
    by_cases g2 : (i &&& fl4_abi.consts.tcb_flag.TRAP_SYSCALLS != 0#u64) = true
    · rw [if_pos g2] at h; simp at h
    rw [if_neg g2] at h
    by_cases g3 : (info.label != fl4_abi.label.TCBSetTimer) = true
    · rw [if_pos g3] at h; simp at h
    rw [if_neg g3] at h
    by_cases g4 : (info.extra_caps != 0#u64) = true
    · rw [if_pos g4] at h; simp at h
    rw [if_neg g4] at h
    by_cases g5 : info.length < 2#u64
    · rw [if_pos g5] at h; simp at h
    rw [if_neg g5] at h
    obtain ⟨csc, -, h⟩ := bind_eq_ok h
    obtain ⟨b, eb, h⟩ := bind_eq_ok h
    cases b
    · rw [if_neg Bool.false_ne_true] at h; simp at h
    · exact key eb
  subst hb
  refine ⟨rfl, ?_⟩
  revert h
  unfold localtimer.handle_set_timer_local
  rw [PathObl.sched.cur_thread.guard (gS := guard st Aligned (fun _ => False)) s (nA _ (by rw [curth_val]; omega) (by rw [curth_val])), cur_thread_ok,
    PathObl.guard_cur_cpu, L.cur_cpu_eq]
  simp only [bind_ok, lift]
  rw [PathObl.msg.msg_info.guard (gS := guard st Aligned (fun _ => False)) s _ (by
    obtain ⟨k, hk', e⟩ := regA_eq ht' (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO])
    have : layout.reg.MSG_INFO.val < 384 := by simp [layout.reg.MSG_INFO]
    rw [e]; exact fA hcT (by omega) (by omega))]
  refine tr_bind_same (fun info _ => ?_)
  rw [num_domains_ne_one_false]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.obj.Tcb.flags.guard (gS := guard st Aligned (fun _ => False)) _ s (fA hcT (by simp) (by simp))]
  refine tr_bind_same (fun i _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  refine tr_ite (fun _ h => h) (fun _ => ?_)
  rw [PathObl.sched.cur_sc.guard (gS := guard st Aligned (fun _ => False)) s (nA _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))]
  refine tr_bind_same (fun csc _ => ?_)
  refine tr_bind (fun b eb _ => gtgt b eb) (fun b eb => ?_)
  cases b
  · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]; exact fun h => h
  · exact absurd eb key

end

end Fl4Proofs.P2
