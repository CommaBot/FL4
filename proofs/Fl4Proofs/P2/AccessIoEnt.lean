/-
# P2: the I/O port path's accesses from its entry state (line p2io)

`guard_acc`'s run-relative premises discharged at the entry `s`, from P1's
invariants and the reads and writes the path makes.

* `SwOK.of_bxi`: `SwOK` from P1's `BXI` (`SchedQueuesInv` placement and
  release queue, `SCsOK` / `ObjsOK` SC words, `BoundInv`, `ScExtra.bound`),
  `cscW ∈ Ac` and the bound current SC (`DecPre.csc`, `DecPre.hcsc`);
* `RhSc`, `RhSc.of_bxi`: the release head's SC is well formed, its words among `Ω`;
* `QOK.of_sw`, `SchedOK.of_sw`: `AccessIoKeep`'s premises at the invocation's entry;
* `IoEnt`: the entry facts; `io_hfin`: `guard_acc`'s `hfin` from them;
* `handle_ioport_local.guard_ent`: the accepted path on the guarded store ends as
  the real run, from the entry facts alone.

Premises of `IoEnt` (facts of the entry state, from P1's invariants except as tagged):
* `run` [P]: the current thread is `RUNNING` or `RESTART` (`DecPre.run` without
  `RUNNING_VM`: a thread that runs its guest enters the kernel by a VM exit, not
  by a system call).
-/
import Fl4Proofs.P2.AccessIoSw
import Fl4Proofs.P2.AccessIoMid
import Fl4Proofs.P1.QueueInvAll
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1

section
variable {S : Type} {st : machine.Store S} {R W : U64 → Prop} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {s s2 x y : S} {c : U64} {zc : Nat}

/-- The release head's SC is well formed and its words are among `Ω`. -/
def RhSc (st : machine.Store S) [L : LawfulStore st] (Ω : Set U64) (s : S) : Prop :=
  L.mem s (rhA (L := L) s) ≠ 0#u64 → ∃ zr, SCin st s Ω (L.mem s (scA (L.mem s (rhA (L := L) s)))) zr

theorem bxi_rh (B : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (h0 : L.mem s (rhA (L := L) s) ≠ 0#u64) :
    L.mem s (rhA (L := L) s) ∈ T ∧ L.mem s (scA (L.mem s (rhA (L := L) s))) ∈ Scs ∧
      L.rmax s (L.mem s (scA (L.mem s (rhA (L := L) s)))) ≠ 0#u64 := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B
  have hrel := hq.release _ hq.cur
  have hd : L.mem s (rhA (L := L) s) = (Rq (L.cpu s)).headD 0#u64 := hrel.head
  have hm : L.mem s (rhA (L := L) s) ∈ Rq (L.cpu s) := by
    cases hl : Rq (L.cpu s) with
    | nil => rw [hl] at hd; exact absurd hd h0
    | cons r rs => rw [hl] at hd; rw [hd]; simp
  have hT := hrel.mem _ hm
  have ha := hq.inR _ hq.cur _ hm
  have hfl := (hq.released _ hT).2 (by rw [ha]; exact hm)
  have hne := hb.r _ hT hfl
  have hsc := (hX.bound _ hT hne).1
  exact ⟨hT, hsc, (hS.act _ hsc).1 (hb.sact _ hT (Or.inr (Or.inl hfl)) hne)⟩

theorem bxi_scin (B : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) {c : U64} (hc : c ∈ Scs) (ha : L.rmax s c ≠ 0#u64) :
    SCin st s Ω c (Z c) := by
  obtain ⟨-, -, -, -, hS⟩ := B
  exact ⟨(hS.all _ hc).1 ha, fun b hb hi => hS.sub _ ((hS.all _ hc).2.2 b hb hi)⟩

theorem RhSc.of_bxi (B : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) : RhSc st Ω s := fun h0 => by
  obtain ⟨-, hc, ha⟩ := bxi_rh B h0
  exact ⟨_, bxi_scin B hc ha⟩

/-- The reads and writes of the path that do not go through the invariants'
objects: the node, the current SC, the current thread, the kernel-global
words, the earliest timer's deadline, the release head's SC. -/
structure IoAcc (st : machine.Store S) [L : LawfulStore st] (R W : U64 → Prop) (s : S) (c : U64) (zc : Nat) : Prop where
  acc : ScAcc R W c zc
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R (L.nodeAt s (L.cpu s) o) ∧ W (L.nodeAt s (L.cpu s) o)
  sc : R (scA (L.curW s))
  dt : R (core.num.U64.wrapping_add (L.ksb s) layout.ks.DOMAIN_TIME)
  td : L.mem s (tmA (L := L) s) ≠ 0#u64 → R (core.num.U64.wrapping_add (L.mem s (tmA (L := L) s)) 3528#u64)
  rs : L.mem s (rhA (L := L) s) ≠ 0#u64 → R (scA (L.mem s (rhA (L := L) s))) ∧
    RdHead (L := L) R s (L.mem s (scA (L.mem s (rhA (L := L) s))))
  ryl : R (yieldA (L.curW s))
  rst : R (stA (L.curW s))
  rfi : R (regA (L.curW s) layout.reg.FAULT_IP)
  wnx : W (regA (L.curW s) layout.reg.NEXT_IP)
  wst : W (stA (L.curW s))
  rin : R (inqA (L.curW s))

theorem SwOK.of_bxi (B : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hcsc : L.cscW s ∈ Ac)
    (hi : L.mem s (scA (L.curW s)) = L.cscW s) (hR : IoAcc st R W s (L.cscW s) (Z (L.cscW s))) :
    SwOK st T Cs Ω R W s (L.cscW s) (Z (L.cscW s)) := by
  have B' := B
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B'
  have hcs : L.cscW s ∈ Scs := hX.cur
  obtain ⟨hP, hz⟩ := hO.sc _ hcs
  obtain ⟨h8, h128, -⟩ := sc_lo hP hz
  have hv := sc_word_val hP hz (o := layout.sc.CONSUMED) (by simp [layout.sc.CONSUMED])
  have hcv : layout.sc.CONSUMED.val = 8 := by simp [layout.sc.CONSUMED]
  obtain ⟨a1, a2, a3⟩ := maxA_facts hO hcs
  refine ⟨hq.tcbs, hq.cur, hq.nodes _ hq.cur, hq.omega, hq.curT, rfl, hi,
    ⟨(hS.all _ hcs).1, fun b hb hi => hS.sub _ ((hS.all _ hcs).2.2 b hb hi),
      ⟨⟨by rw [hv]; omega, by rw [hv, hcv]; omega⟩, by unfold Aligned; rw [hv, hcv]; omega⟩, ⟨a2, a3⟩, a1⟩,
    (hS.act _ hcs).1 hcsc, hR.acc, hR.nd, hR.sc, hR.dt, hR.td, hR.rs, ?_⟩
  intro h0
  obtain ⟨hT, hsc, ha⟩ := bxi_rh B h0
  refine ⟨hT, ?_⟩
  by_cases e : L.mem s (scA (L.mem s (rhA (L := L) s))) = L.cscW s
  · exact Or.inl e
  · obtain ⟨hP', hz'⟩ := hO.sc _ hsc
    obtain ⟨h8', h128', -⟩ := sc_lo hP' hz'
    have hh := headA_val' hP' hz'
    have hin : InSC (L.mem s (scA (L.mem s (rhA (L := L) s)))) (Z (L.mem s (scA (L.mem s (rhA (L := L) s)))))
        (headA (L.mem s (scA (L.mem s (rhA (L := L) s))))) := ⟨by omega, by omega⟩
    have hne : L.mem s (scA (L.mem s (rhA (L := L) s))) ≠ 0#u64 := by
      intro e0
      have hfl := hb.r _ hT
      have hrel := hq.release _ hq.cur
      have hd : L.mem s (rhA (L := L) s) = (Rq (L.cpu s)).headD 0#u64 := hrel.head
      have hm : L.mem s (rhA (L := L) s) ∈ Rq (L.cpu s) := by
        cases hl : Rq (L.cpu s) with
        | nil => rw [hl] at hd; exact absurd hd h0
        | cons r rs => rw [hl] at hd; rw [hd]; simp
      exact hfl ((hq.released _ hT).2 (by rw [hq.inR _ hq.cur _ hm]; exact hm)) e0
    exact Or.inr ⟨hS.sub _ ((hS.all _ hsc).2.2 _ (by unfold Aligned; omega) hin), hS.disj _ hT hne e _ hin⟩

theorem SwOK.omT {b : U64} (F : SwOK st T Cs Ω R W x c zc) (hb : b ∈ Ω) : Aligned b ∧ ¬ IoTW (L.curW x) b := by
  refine ⟨(F.om b hb).1, ?_⟩
  have ht := F.tp _ F.cT
  have h1 := (F.om b hb).2.1 _ F.cT
  rintro (⟨r, hr, e⟩ | e)
  · have hv := congrArg UScalar.val e
    rw [regA_val ht hr] at hv; omega
  · have hv := congrArg UScalar.val e
    unfold stA at hv
    rw [tcb_wadd_val ht (by rw [st_val]; omega), st_val] at hv; omega

theorem SwOK.ndT (F : SwOK st T Cs Ω R W x c zc) (o : U64) (ho : o.val < 4288) (h8 : o.val % 8 = 0) :
    Aligned (L.nodeAt x (L.cpu x) o) ∧ ¬ IoTW (L.curW x) (L.nodeAt x (L.cpu x) o) := by
  refine ⟨nodeAt_aligned F.np ho h8, ?_⟩
  have ht := F.tp _ F.cT
  rintro (⟨r, hr, e⟩ | e)
  · have hv := congrArg UScalar.val e
    rw [regA_val ht hr, nodeAt_val F.np ho] at hv
    have := F.np.disj _ F.cT; omega
  · exact node_ne_field F.np ho F.cT ht (by rw [st_val]; omega) e

theorem SchedOK.of_sw (F : SwOK st T Cs Ω R W x c zc) (hsc : L.mem x (scA (L.curW x)) ≠ 0#u64)
    (hnr : (L.mem x (inqA (L.curW x)) &&& sched.Q_RELEASE) = 0#u64) : SchedOK (L := L) x (L.curW x) := by
  refine ⟨F.tp _ F.cT, rfl, hsc, ?_, hnr, F.ndT, ?_⟩
  · rw [F.i]; exact F.act
  · rw [F.i]; exact F.omT (F.q.2.1 _ F.q.2.2.2.2 F.q.2.2.2.1)

theorem RhSc.frame (F : SwOK st T Cs Ω R W x c zc) (w : WritesIn st x y (IoPW st x)) (h : RhSc st Ω x) :
    RhSc st Ω y := by
  have hrh : L.mem y (rhA (L := L) y) = L.mem x (rhA (L := L) x) :=
    F.nodeP w _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])
  unfold RhSc
  rw [hrh]
  intro h0
  have e : L.mem y (scA (L.mem x (rhA (L := L) x))) = L.mem x (scA (L.mem x (rhA (L := L) x))) :=
    F.tcbP w (F.rh h0).1 (K := 3464#u64) (by simp) (by simp) (by simp)
  rw [e]
  obtain ⟨zr, hW, hΩ⟩ := h h0
  exact ⟨zr, hW.agree fun b hb hin => F.omP w (hΩ b hb hin), hΩ⟩

theorem QOK.of_sw (F : SwOK st T Cs Ω R W x c zc) (h : RhSc st Ω x)
    (htm : L.mem x (tmA (L := L) x) ≠ 0#u64 → L.mem x (tmA (L := L) x) ∈ T) : QOK (L := L) x (L.curW x) := by
  refine ⟨fun h0 => F.tp _ (htm h0), fun h0 => F.tp _ (F.rh h0).1, fun h0 => ?_⟩
  obtain ⟨zr, hW, hΩ⟩ := h h0
  obtain ⟨h8, hm, hfit⟩ := hW.bounds
  obtain ⟨h96, -, -, hhd, -, hrt⟩ := hW.inside
  obtain ⟨e1, e2, e3⟩ := hrt _ hW.head_lt
  have g1 := F.omT (hΩ (headA (L.mem x (scA (L.mem x (rhA (L := L) x))))) (by unfold Aligned; omega)
    ⟨by omega, by omega⟩)
  have g2 := F.omT (hΩ (rtA (L.mem x (scA (L.mem x (rhA (L := L) x))))
      (L.rhead x (L.mem x (scA (L.mem x (rhA (L := L) x)))))) (by unfold Aligned; omega) ⟨by omega, by omega⟩)
  exact ⟨g1.1, g1.2, g2.1, g2.2⟩

/-- **The entry facts of the I/O port path**: P1's invariants (`BXI`, the
active current SC, `DecPre.hcsc`), the current thread `RUNNING` or `RESTART`
([P]), the accesses. -/
structure IoEnt (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac : Set U64) (R W : U64 → Prop) (s : S) : Prop where
  bxi : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s
  csc : L.cscW s ∈ Ac
  hcsc : L.mem s (scA (L.curW s)) ≠ 0#u64 → L.cscW s = L.mem s (scA (L.curW s))
  run : L.mem s (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s (stA (L.curW s)) = sched.TS_RUNNING
  acc : IoAcc st R W s (L.cscW s) (Z (L.cscW s))

theorem preW_ioPW (hT : TcbAddr (L.curW s)) {b : U64} (h : PreW (L := L) s (L.curW s) b) : IoPW st s b := by
  rcases h with ⟨K, hK, e⟩ | e | e
  · refine Or.inr (Or.inl ⟨17#u64, by simp, ?_⟩)
    subst e
    apply UScalar.eq_of_val_eq
    rw [tcb_wadd_val hT (by omega), regA_val hT (by simp), hK]; simp
  · exact Or.inl ⟨_, by simp [layout.node.CUR_TIME], e⟩
  · exact Or.inl ⟨_, by simp [layout.node.CONSUMED], e⟩

theorem preW_tcb {t K : U64} (hT : TcbAddr t) (hN : NodePlaced st T s (L.cpu s)) (ht : t ∈ T) (hK : K.val < 4096)
    (h : K.val ≠ 392) : ¬ PreW (L := L) s t (core.num.U64.wrapping_add t K) := by
  rintro (⟨K', hK', e⟩ | e | e)
  · have hv := congrArg UScalar.val e
    rw [tcb_wadd_val hT hK, tcb_wadd_val hT (by omega)] at hv; omega
  · exact node_ne_field hN (by simp [layout.node.CUR_TIME]) ht hT hK e.symm
  · exact node_ne_field hN (by simp [layout.node.CONSUMED]) ht hT hK e.symm

/-- The path's state `s2` before the invocation, from the entry. -/
structure IoS2 (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (R W : U64 → Prop) (Z : U64 → Nat)
    (s s2 : S) : Prop where
  k : L.ksb s2 = L.ksb s
  cp : L.cpu s2 = L.cpu s
  cur : L.curW s2 = L.curW s
  F0 : SwOK st T Cs Ω R W s (L.cscW s) (Z (L.cscW s))
  w : WritesIn st s s2 (IoPW st s)
  F : SwOK st T Cs Ω R W s2 (L.cscW s) (Z (L.cscW s))
  rh : RhSc st Ω s2
  tm : L.mem s2 (tmA (L := L) s2) ≠ 0#u64 → L.mem s2 (tmA (L := L) s2) ∈ T
  st : L.mem s2 (stA (L.curW s)) = L.mem s (stA (L.curW s))

theorem IoS2.of_ent {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac R W s) {s1 : S} {a a1 : A} {v : U64}
    (es1 : obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP v = ok s1)
    (eu : sched.update_timestamp st ar s1 a = ok (s2, a1))
    (hsc : L.mem s2 (scA (L.curW s)) ≠ 0#u64) : IoS2 st T Cs Ω R W Z s s2 := by
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := E.bxi
  have hT := hq.tcbs _ hq.curT
  have hN := hq.nodes _ hq.cur
  have w0 : WritesIn st s s2 (PreW (L := L) s (L.curW s)) := prefix_writes ar hA hq.tcbs hN hq.curT es1 eu
  have w : WritesIn st s s2 (IoPW st s) := w0.mono fun b h => preW_ioPW hT h
  have tk : ∀ K : U64, K.val < 4096 → K.val % 8 = 0 → K.val ≠ 392 →
      L.mem s2 (core.num.U64.wrapping_add (L.curW s) K) = L.mem s (core.num.U64.wrapping_add (L.curW s) K) :=
    fun K h1 h2 h3 => w0.2.2 _ (field_aligned hT h1 h2) (preW_tcb hT hN hq.curT h1 h3)
  have e1 : L.mem s2 (scA (L.curW s)) = L.mem s (scA (L.curW s)) := tk 3464#u64 (by simp) (by simp) (by simp)
  have F0 : SwOK st T Cs Ω R W s (L.cscW s) (Z (L.cscW s)) :=
    SwOK.of_bxi E.bxi E.csc (E.hcsc (by rw [← e1]; exact hsc)).symm E.acc
  have htm : L.mem s2 (tmA (L := L) s2) = L.mem s (tmA (L := L) s) :=
    F0.nodeP w _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])
  refine ⟨w.1, w.2.1, ?_, F0, w, F0.frame w, (RhSc.of_bxi E.bxi).frame F0 w, ?_,
    tk _ (by rw [st_val]; omega) (by rw [st_val]) (by rw [st_val]; omega)⟩
  · exact F0.nodeP w _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
      (by simp [layout.node.CUR_THREAD])
  · rw [htm]
    exact fun h0 => (hX.tm.min _ hq.cur).resolve_left h0

/-- **`guard_acc`'s `hfin` from the entry.** -/
theorem io_hfin {A : Type} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (E : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac R W s) {a : A} {number : I64}
    (hmi2 : ∀ info nx s1 s2 a1, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) → msg.msg_info st s2 (L.curW s) = ok info) :
    ∀ info nx s1 s2 a1 r s3 a2, msg.msg_info st s (L.curW s) = ok info →
      obj.Tcb.reg st (L.curW s) s layout.reg.NEXT_IP = ok nx →
      obj.Tcb.set_reg st (L.curW s) s layout.reg.FAULT_IP (core.num.U64.wrapping_sub nx 2#u64) = ok s1 →
      sched.update_timestamp st ar s1 a = ok (s2, a1) →
      sched.action st s2 = ok sched.ACTION_RESUME_CURRENT → obj.Tcb.yield_to st (L.curW s) s2 = ok 0#u64 →
      info.extra_caps = 0#u64 →
      ioport.invocation_ok st s2 (L.curW s) (L.mem s2 (regA (L.curW s) layout.reg.CAP)) info = ok true →
      fastpath.schedulable_here st s2 (L.curW s) = ok true →
      syscall.handle_invocation st ar s2 a1 (decide (number = fl4_abi.syscall.SysCall))
      true (decide (number = fl4_abi.syscall.SysCall)) false (L.mem s2 (regA (L.curW s) layout.reg.CAP)) =
        ok (r, s3, a2) → FinOK (L := L) R W ar s s3 a2 := by
  intro info nx s1 s2 a1 r s3 a2 emi enx es1 eu eac ey hx einv ehere eh
  have Hf := here_facts ehere
  have I := IoS2.of_ent hA E es1 eu Hf.sc
  have ha2 : L.actionW s2 = sched.ACTION_RESUME_CURRENT := by
    rw [eq_of_spec_fd (sched.action.spec (L := L) s2)] at eac; exact ok_inj_ff eac
  have hy2 : L.mem s2 (yieldA (L.curW s)) = 0#u64 := by
    rw [eq_ok_of_spec (obj.Tcb.yield_to.spec (L := L) s2 (L.curW s))] at ey; exact ok_inj_ff ey
  have hmi := hmi2 info nx s1 s2 a1 emi enx es1 eu
  have hrun : L.mem s2 (stA (L.curW s)) = sched.TS_RESTART ∨ L.mem s2 (stA (L.curW s)) = sched.TS_RUNNING := by
    rw [I.st]; exact E.run
  have hsc := Hf.sc
  have hnr := Hf.nr
  have A0 := E.acc
  rw [← I.cur] at hy2 hmi hrun hsc hnr einv eh
  have hK := SchedOK.of_sw I.F hsc hnr
  have K : KeepA (L := L) s2 (L.curW s2) s3 := io_inv_keep ar hK ha2 hrun hmi hx einv eh
  have hcur3 : L.curW s3 = L.curW s2 := K.cur hK
  have w3 : WritesIn st s2 s3 (IoPW st s2) := K.1.mono fun b h => Or.inr h
  have hnd := (K.fin hK (QOK.of_sw I.F I.rh I.tm) Hf.nd I.F.td I.F.rs).1
  have hcs : L.curW s3 = L.curW s := hcur3.trans I.cur
  refine FinOK.of_sw hA (K.1.1.trans I.k) (K.1.2.1.trans I.cp) hnd K.2.1 (I.F.frame w3) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcur3]
    exact (I.F.tcbP w3 I.F.cT (K := 3472#u64) (by simp) (by simp) (by simp)).trans hy2
  · rw [hcur3]; exact K.2.2
  · rw [hcs]; exact A0.ryl
  · rw [hcs]; exact A0.rst
  · rw [hcs]; exact A0.rfi
  · rw [hcs]; exact A0.wnx
  · rw [hcs]; exact A0.wst
  · rw [hcs]; exact A0.rin

/-- **The accepted I/O port path on the guarded store ends as the real run**,
from the entry facts (`IoEnt`) and the walk's facts `M` (`IoMid` at the entry). -/
theorem syscall.handle_ioport_local.guard_ent {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) {s' : S} {a a' : A}
    {number : I64} {C : U64 → U64 → Prop} {sl : U64} (E : IoEnt st T Cs Ω H Sg Rp Scs Nt Z Ac R W s)
    (M : ∀ info, msg.msg_info st s (L.curW s) = ok info →
      IoMid (L := L) R W s s (L.curW s) info (L.mem s (regA (L.curW s) layout.reg.CAP)) C sl)
    (hCo : ∀ p r m y, C p r → cspace.mask r = ok m → OutsideObjs st T Cs s (cnSlot p (y &&& m)) ∧
      OutsideObjs st T Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64))
    (hLo : ∀ x, cspace.lookup_slot st s (L.curW s) (L.mem s (regA (L.curW s) layout.reg.CAP)) = ok (.Ok x) →
      OutsideObjs st T Cs s x.slot ∧ OutsideObjs st T Cs s (core.num.U64.wrapping_add x.slot 8#u64))
    (hmi : R (regA (L.curW s) layout.reg.MSG_INFO))
    (hfl : R (core.num.U64.wrapping_add (L.curW s) 3456#u64))
    (hnx : R (regA (L.curW s) layout.reg.NEXT_IP)) (hfi : W (regA (L.curW s) layout.reg.FAULT_IP))
    (h : syscall.handle_ioport_local st ar s a number = ok (true, s', a')) :
    syscall.handle_ioport_local (PathObl.guard st R W) ar s a number = ok (true, s', a') := by
  have B' := E.bxi
  obtain ⟨⟨Q, Rq, hq⟩, hb, ⟨hO, -, hX⟩, -, hS⟩ := B'
  have hd : ∀ {c : U64}, c ∈ Scs → OutsideObjs st T Cs s (headA c) := fun {c} hc => by
    obtain ⟨hP, hz⟩ := hO.sc _ hc
    obtain ⟨h8, h128, -⟩ := sc_lo hP hz
    have hh := headA_val' hP hz
    exact hq.omega _ (hS.sub _ ((hS.all _ hc).2.2 _ (by unfold Aligned; omega) ⟨by omega, by omega⟩))
  have hmid := io_hmid (a := a) ar hA hq.tcbs (hq.nodes _ hq.cur) hq.cur hq.curT M hCo hLo (hd hX.cur)
    (fun h0 => ⟨(bxi_rh E.bxi h0).1, hd (bxi_rh E.bxi h0).2.1⟩)
  refine syscall.handle_ioport_local.guard_acc ar E.acc.nd hmi hfl hnx hfi hmid ?_ h
  refine io_hfin hA E fun info nx s1 s2 a1 h1 h2 h3 h4 => ?_
  obtain ⟨C', sl', M'⟩ := hmid info nx s1 s2 a1 h1 h2 h3 h4
  exact M'.mi

end

end Fl4Proofs.P2.PathObl
