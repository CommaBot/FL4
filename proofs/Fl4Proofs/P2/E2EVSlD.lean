/-
P2 (line vlift, gen 4): **`AvoidV` for syscall_local** (`sl_avoidV`), so `sl_localPath` lifts to `ownV` through
`LocalPath.cutV` / `cutLiftV` / `PathsV.ofPathsCut` (`P2/E2EVCutP.lean`).

* `sl_homeV` / `sl_awayV`: p2sl's `sl_home` / `sl_away` (`P2/SlHome.lean`) for the cut read set `SlRV K Locks s`
  (`P2/E2EVSlW.lean`): a declining run whose decided thread is homed here is the same run on
  `guard st (SlRV s) (SlDS s)`; homed elsewhere, a run at an alternative is the same run on
  `guard st (SlRV s ∪ (live ∧ slTW (slThr s))) ⊤` (the `slTW` words only once the decided thread is live, so they
  are words of a heap TCB).
* **`sl_avDec`** (`AvoidV.dec`): from every alternative of a declining entry the run reads no `VData` word (homed
  here: `interp_agree` from the entry's guarded run, as p2sl's `sl_dec_alt_run`; elsewhere: `sl_awayV`).
* **`sl_avoidV`**: `AvoidV K (sl_localPath …)`: `acc` by `sl_accV` (`P2/E2EVSlA.lean`), `dec` by `sl_avDec`,
  `prog` by `IsProg.on` (the path's program premise `hpz` is an unrelativised `IsProg`).

Premises of `sl_avoidV`: `sl_localPath`'s own (unchanged; its `RegionOK` is `RegionOKV.base`), and
* `hK : RegionOKV K` [J] (as everywhere in `E2EV`);
* `hks : VcpuKs K` (derived: `vcpuKs_of` from `VcpuHeap` [J] and P3's `JKern.hksIn`), `hf : K.ksb + 13568 ≤ 2^64`
  (P3 `JKern.ksbFit`);
* `hTN : ∀ s, P s → TabNoV K s` (derived: `tabNoV_of` from `VcpuTabOff` [J], `PoolObj` [J]);
* `hH : HeapOK K.heap` (P1), `hV : VcpuHeap K` [J], `hUo : UserObj K` [J] (the ReplyRecv arm reads the caller's
  IPC-buffer words, user words).
-/
import Fl4Proofs.P2.E2EVSlA
import Fl4Proofs.P2.E2EVCutP
import Fl4Proofs.P2.SlJLay
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Locks : S → U64 → Prop}

/-- The words `slTW t` of a heap TCB are no VCPU data words. -/
theorem nv_tw (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) {t b : U64} (ht : K.heap t = some .tcb)
    (hb : slTW t b) : ¬ VData K b := by
  obtain ⟨-, h⟩ := hb
  rcases h with rfl | rfl | rfl | rfl
  · exact nv_tcb hK hX ht (o := 3360#u64) (by simp) (by simp) (by simp)
  · rw [stA_eq]; exact nv_tcb hK hX ht (o := 3328#u64) (by simp) (by simp) (by simp)
  · exact nv_tcb hK hX ht (o := 3376#u64) (by simp) (by simp) (by simp)
  · exact nv_tcb hK hX ht (o := 3464#u64) (by simp) (by simp) (by simp)

variable {A : Type} (ar : machine.Arch A)
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64}
  {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat}

set_option maxHeartbeats 4000000 in
/-- `sl_home` for the cut read set. -/
theorem sl_homeV (hA : P0.ArchTotal ar) {s : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hpre : PreAcc (L := L) (SlRV (st := st) K Locks s) (SlWS (st := st) K.toKLayout Locks s) s)
    (hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SlRV (st := st) K Locks s) X csc)
    (I : SlThrIn (st := st) K.toKLayout Locks found.1 s)
    (D : SlDecInR (st := st) ar (SlRV (st := st) K Locks s) found s)
    (h : syscall.handle_syscall_local st ar s a n found = ok r) (hn : r.1 ≠ true)
    (hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s) :
    syscall.handle_syscall_local (guard st (SlRV (st := st) K Locks s) (SlDS (L := L) s)) ar s a n found = ok r := by
  have hp : PreDec (L := L) (SlRV (st := st) K Locks s) (SlDS (L := L) s) s :=
    ⟨fun o h1 h2 => (hpre.nd o h1 h2).1, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), hpre.fl, hpre.nx,
      Or.inl rfl⟩
  refine syscall.handle_syscall_local.guard_dec (gS := guard st (SlRV (st := st) K Locks s) (SlDS (L := L) s))
    hA E.hT E.hN E.hcT hp (fun X a1 csc LP e => hhd a X a1 csc LP e) ?_ ?_ h
  · intro hS X a1 n' LP hf
    refine fastpath.fault.guard_dec (gS := guard st (SlRV (st := st) K Locks s) (SlDS (L := L) s))
      (FltDec.of (D.fT hS a X a1 LP) ?_) hf hn
    intro ptr bb x y g gr hc hst d hd
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X ptr), e1] at hd
    rw [← ok_inj_ff hd]
    exact D.fD hS (slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc hst) hh a X a1 LP
  · intro hS X a1 LP hf
    refine fastpath.reply_recv_found.guard_dec (gS := guard st (SlRV (st := st) K Locks s) (SlDS (L := L) s))
      (RrDec.of (D.rT hS a X a1 LP) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hu, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    rw [h1]
    exact D.rU hS lv hh a X a1 LP

set_option maxHeartbeats 8000000 in
/-- `sl_away` for the cut read set (the decided thread's `slTW` words only once it is live). -/
theorem sl_awayV (hA : P0.ArchTotal ar) {s s' : S} {a : A} {r : Bool × S × A}
    (E : SlPre (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hpre : PreAcc (L := L) (SlRV (st := st) K Locks s) (SlWS (st := st) K.toKLayout Locks s) s)
    (hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SlRV (st := st) K Locks s) X csc)
    (I : SlThrIn (st := st) K.toKLayout Locks found.1 s)
    (D : SlDecInR (st := st) ar (SlRV (st := st) K Locks s) found s)
    (hafV : SlLive st found.1 s → ¬ VData K (affA (slThr st found.1 s)))
    (Al : Alt st (SlRS (st := st) K.toKLayout Locks s) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0)
      (· ∈ K.user) s s')
    (hh : L.mem s (affA (slThr st found.1 s)) ≠ L.cpu s)
    (h : syscall.handle_syscall_local st ar s' a n found = ok r) :
    syscall.handle_syscall_local
      (guard st (fun b => SlRV (st := st) K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
        (fun _ => True))
      ar s' a n found = ok r := by
  have hn : r.1 ≠ true := fun e => hh (slThr_acc ar hA E I Al h e)
  have hcur := sl_alt_cur E.preG Al
  have hTr := slTrap_alt E.preG.fl Al hcur
  have hN' : NodePlaced st T s' (L.cpu s') := by rw [Al.cpu]; exact NodePlaced.of_ksb Al.ksb E.hN
  have hc' : L.curW s' ∈ T := by rw [hcur]; exact E.hcT
  have hp : PreDec (L := L)
      (fun b => SlRV (st := st) K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
      (fun _ => True) s' :=
    ⟨fun o h1 h2 => Or.inl (by rw [slDS_node Al.ksb Al.cpu]; exact (hpre.nd o h1 h2).1), trivial, trivial,
      Or.inl (by rw [hcur]; exact hpre.fl), Or.inl (by rw [hcur]; exact hpre.nx), trivial⟩
  have hct : SlRS (st := st) K.toKLayout Locks s (ctA (L := L) s) :=
    (E.preG.nd _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])).1
  have hcn : SlRS (st := st) K.toKLayout Locks s (cnA (L := L) s) :=
    (E.preG.nd _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])).1
  have PA : ∀ X' a1', LocalPre (st := st) ar s' a (X', a1') → ∃ X, LocalPre (st := st) ar s a (X, a1') ∧
      (∀ b, SlRS (st := st) K.toKLayout Locks s b → L.mem X' b = L.mem X b) ∧ L.ksb X' = L.ksb X ∧
        L.cpu X' = L.cpu X := by
    intro X' a1' LP'
    obtain ⟨X, LP, hag⟩ := lp_alt ar hA (fun b hb => hb.1) E.hT E.hN E.hcT Al.ksb Al.cpu hcur Al.read
      E.preG.nx hct hcn LP'
    obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    obtain ⟨hkX', hcX', -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT hN' hc' LP'
    exact ⟨X, LP, hag, by rw [hkX', hkX, Al.ksb], by rw [hcX', hcX, Al.cpu]⟩
  have hrest : SlLive st found.1 s → ∀ X X' a1', LocalPre (st := st) ar s a (X, a1') →
      (∀ b, SlRS (st := st) K.toKLayout Locks s b → L.mem X' b = L.mem X b) → L.cpu X' = L.cpu X →
      L.mem X' (affA (slThr st found.1 s)) ≠ L.cpu X' := by
    intro lv X X' a1' LP hag hcX e
    have af := I.af lv
    apply hh
    obtain ⟨-, hcX0, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    rw [← lp_mem ar hA E.hT E.hN E.hcT LP af.1.1 af.2, ← hag _ af.1, e, hcX, hcX0]
  refine syscall.handle_syscall_local.guard_dec
    (gS := guard st (fun b => SlRV (st := st) K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
      (fun _ => True))
    hA E.hT hN' hc' hp ?_ ?_ ?_ h
  · intro X' a1' csc LP' ecsc
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    obtain ⟨hkX, hcX, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
    have rcs : SlRS (st := st) K.toKLayout Locks s (L.nodeA X layout.node.CUR_SC) := by
      unfold LawfulStore.nodeA; rw [hcX, nodeAt_of_ksb hkX]
      exact (E.preG.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1
    have en : L.nodeA X' layout.node.CUR_SC = L.nodeA X layout.node.CUR_SC := by
      unfold LawfulStore.nodeA; exact slDS_node hk hc
    have ecsc' : sched.cur_sc st X = ok csc := by
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X')] at ecsc
      rw [eq_of_spec_fd (sched.cur_sc.spec (L := L) X), ← hag _ rcs, ← en]
      exact ecsc
    exact RdHead.mono (fun b hb => Or.inl hb) (RdHead.congr (fun b hb => hag b hb.1) (hhd a X a1' csc LP ecsc'))
  · intro hS' X' a1' n' LP' hf
    have hS := hTr.1 hS'
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    have DT := FltDecT.congr hk hc (fun b hb => hag b hb.1) (D.fT hS a X a1' LP)
    rw [hcur] at hf ⊢
    refine fastpath.fault.guard_dec
      (gS := guard st (fun b => SlRV (st := st) K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
        (fun _ => True))
      (FltDec.of (FltDecT.mono (fun b hb => Or.inl hb) DT) ?_) hf hn
    intro ptr bb x y g gr hcp hst' d hd
    have hc0 : obj.Slot.cap st (fhA (L := L) s) X = ok (capability.Cap.Endpoint ptr bb x y g gr) :=
      (cap_congr (hag _ DT.fh.1.1) (hag _ DT.fh.2.1)).symm.trans hcp
    have hst : obj.Ep.state st ptr X = ok obj.EP_RECV :=
      (ep_state_congr (hag _ (DT.ep ptr bb x y g gr hcp).1.1)).symm.trans hst'
    have lv := slLive_trap ar hA E.hT E.hN E.hcT I hS LP hc0 hst
    have af := I.af lv
    have aA : Aligned (affA (slThr st found.1 s)) := af.1.1
    have e1 := slThr_hd_trap ar hA E.hT E.hN E.hcT I hS LP hc0
    rw [eq_of_spec_fd (obj.Ep.head.spec' (st := st) X' ptr), hag _ (DT.ep ptr bb x y g gr hcp).2.1, e1] at hd
    rw [← ok_inj_ff hd]
    exact ⟨Or.inr ⟨lv, by unfold replyA; exact tw_al aA (by simp), Or.inl rfl⟩, Or.inl ⟨af.1, hafV lv⟩,
      fun e => absurd e (hrest lv X X' a1' LP hag hc)⟩
  · intro hS' X' a1' LP' hf
    have hS : ¬ SlTrap st s := fun h' => hS' (hTr.2 h')
    obtain ⟨X, LP, hag, hk, hc⟩ := PA X' a1' LP'
    have DT := RrDecT.congr hk hc (fun b hb => hag b hb.1) (D.rT hS a X a1' LP)
    rw [hcur] at hf ⊢
    refine fastpath.reply_recv_found.guard_dec
      (gS := guard st (fun b => SlRV (st := st) K Locks s b ∨ (SlLive st found.1 s ∧ slTW (slThr st found.1 s) b))
        (fun _ => True))
      (RrDec.of (RrDecT.mono (fun b hb => Or.inl hb) DT) ?_) hf hn
    intro u hu hu0
    have h1 := obj.Reply.tcb.blk (st := st) X' found.1
    rw [hu, WP.spec_ok, hag _ DT.rRt.1, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    have lv := slLive_rr (st := st) hS (by rw [← h1]; exact hu0)
    have af := I.af lv
    have aA : Aligned (affA (slThr st found.1 s)) := af.1.1
    rw [h1]
    exact ⟨Or.inr ⟨lv, by rw [stA_eq]; exact tw_al aA (by simp), Or.inr (Or.inl rfl)⟩,
      Or.inr ⟨lv, tw_al aA (by simp), Or.inr (Or.inr (Or.inl rfl))⟩,
      Or.inr ⟨lv, by unfold scA; exact tw_al aA (by simp), Or.inr (Or.inr (Or.inr rfl))⟩,
      Or.inl ⟨af.1, hafV lv⟩, fun e => absurd e (hrest lv X X' a1' LP hag hc)⟩

end

/-! ## `AvoidV` for syscall_local -/

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {Locks : S → U64 → Prop}
variable {T Rp Scs Nt : Set U64} {H : Heap} {Z : U64 → Nat}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω U Sg Ac : Set U64}

/-- The entry facts p2sl derives at a `P` state (`slEnt_of`, `slHere_of`, `slAccIn_of`). -/
def SlEntAll (ar : machine.Arch A) (K : KLayoutV) (Locks : S → U64 → Prop) (m0 : U64 → U64) (n : I64)
    (found : U64 × U64) (T Cs Ω U Sg Rp Scs Nt Ac : Set U64) (H : Heap) (Z : U64 → Nat) (s : S) : Prop :=
  SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s ∧
    SlEnt (st := st) K.toKLayout Locks found s ∧ SlHere (st := st) K.toKLayout Z Scs found s ∧
    SlAccIn (st := st) ar K.toKLayout Locks Z Scs found s

/-- **`AvoidV.acc` for syscall_local.** -/
theorem sl_avAcc (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKV K) {P : S → Prop}
    (hX : ∀ s, P s → RegionOKX K.toKLayout)
    (hent : ∀ s, P s → SlEntAll (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hks : ∀ s, P s → VcpuKs K) (hf : ∀ s, P s → K.ksb.val + 13568 ≤ 2 ^ 64)
    (hTN : ∀ s, P s → TabNoV (L := L) K s)
    (hH : ∀ s, P s → HeapOK K.heap) (hV : VcpuHeap K) (hUo : UserObj K) :
    AvAcc K st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true) P
      (SlRS (st := st) K.toKLayout Locks) (SlWS (st := st) K.toKLayout Locks) := by
  rintro s a ⟨b, s1, a1⟩ hP h hb
  beta_reduce at h ⊢
  obtain ⟨E0, N, Hh, Ai⟩ := hent s hP
  have hb' : b = true := hb
  subst hb'
  exact sl_accV ar hA hK (hX s hP) (hks s hP) (hf s hP) (hH s hP) hV hUo E0 N Hh Ai (hTN s hP) h

/-- **`AvoidV.dec` for syscall_local.** -/
theorem sl_avDec (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKV K)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) {p : SProg Bool} (hFp : IsProg (slBody S n found) p) (hz : NoZero p)
    {P : S → Prop} (hX' : ∀ s, P s → RegionOKX K.toKLayout)
    (hent : ∀ s, P s → SlEntAll (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hks' : ∀ s, P s → VcpuKs K) (hf' : ∀ s, P s → K.ksb.val + 13568 ≤ 2 ^ 64) :
    AvDec K st (fun m s a => syscall.handle_syscall_local m ar s a n found) (fun b => b = true)
      (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P (SlRS (st := st) K.toKLayout Locks) := by
  have hKb := hK.base
  have eP : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar p x a :=
    fun mm x a => congrFun (congrFun (hFp A ar mm) x) a
  intro s a r hP h hn s' r' Al h'
  beta_reduce at h h' ⊢
  obtain ⟨E0, N, Hh, Ai⟩ := hent s hP
  have hX := hX' s hP
  have hks := hks' s hP
  have hf := hf' s hP
  have E := slPre_of ar hA hKb hX E0 N Hh Ai
  have I : SlThrIn (st := st) K.toKLayout Locks found.1 s := slThrIn_of hKb hX E.preG E0.hSt.1 N
  have D := slDecInV ar hA hK hX hks hf E0 N Hh
  have hpre := preAccV ar hK hX E0 Hh
  have hhd : ∀ a X a1 csc, LocalPre (st := st) ar s a (X, a1) → sched.cur_sc st X = ok csc →
      RdHead (L := L) (SlRV (st := st) K Locks s) X csc := fun a X a1 csc LP e => hhdV ar hA hK hX E0 Hh LP e
  have hn' : r.1 ≠ true := hn
  by_cases hh : L.mem s (affA (slThr st found.1 s)) = L.cpu s
  · obtain ⟨b, s1, a1⟩ := r
    have hg := sl_homeV ar hA E hpre hhd I D h hn' hh
    rw [eP] at hg
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1.1) (fun w hw => (SlDS.ws E.preG hw).1) _ hz s s' a b
      s1 a1 Al.ksb Al.cpu Al.masks (fun w hw => Al.read w hw.1) hg
    have h2 := interp_to (st := st) (st' := st) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
      rfl rfl rfl _ hz s' a _ hg'
    rw [eP] at h' ⊢
    rw [h2] at h'
    rw [← h']
    exact interp_mono (fun _ hq => hq.2) (fun _ _ => trivial) _ hz s' a _ hg'
  · have hg := sl_awayV ar hA E hpre hhd I D
      (fun lv => nv_tcb hK hX (N.hthr lv) (o := 3520#u64) (by simp) (by simp) (by simp)) Al hh h'
    rw [eP] at hg ⊢
    exact interp_mono (fun q hq => hq.elim (fun h1 => h1.2) (fun h2 => nv_tw hK hX (N.hthr h2.1) h2.2))
      (fun _ _ => trivial) _ hz s' a _ hg

/-- **`AvoidV` for syscall_local** (module docstring). -/
theorem sl_avoidV (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hK : RegionOKV K) (hX : RegionOKX K.toKLayout) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    (hm : Fl4Proofs.P2.E2E.MasksWr st)
    (hSe : SlSets K.toKLayout T Rp Scs Nt H Z) (hUu : ∀ b ∈ U, b ∈ K.user) (a0 : A)
    {P : S → Prop}
    (hPE : ∀ s, P s → SlPreB (st := st) ar K.toKLayout Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s)
    (hEj : ∀ s, P s → SlEntJ (st := st) K.toKLayout Locks found s)
    (hHj : ∀ s, P s → SlHereJ (st := st) K.toKLayout Z Scs found s)
    (hAk : ∀ s, P s → SlAccK (st := st) ar K.toKLayout Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hks : VcpuKs K) (hf : K.ksb.val + 13568 ≤ 2 ^ 64) (hTN : ∀ s, P s → TabNoV (L := L) K s)
    (hH : HeapOK K.heap) (hV : VcpuHeap K) (hUo : UserObj K) :
    AvoidV K (sl_localPath ar hSt hA hK.base hX hU hm hSe hUu a0 hPE hEj hHj hAk huf hpz) := by
  have hKb := hK.base
  have hent : ∀ s, P s → SlEntAll (st := st) ar K Locks m0 n found T Cs Ω U Sg Rp Scs Nt Ac H Z s := by
    intro s hP
    have E0 := hPE s hP
    have N := slEnt_of ar hSt hA hX hSe a0 E0 (hEj s hP)
    have Hh := slHere_of ar hSt hA hX hSe a0 E0 N (hHj s hP)
    exact ⟨E0, N, Hh, slAccIn_of ar hA hKb hX hSe E0 N Hh (slAccJ_of ar hA hKb hX hUu E0 (hHj s hP) (hAk s hP))⟩
  letI : LawfulStore (sl_localPath ar hSt hA hK.base hX hU hm hSe hUu a0 hPE hEj hHj hAk huf hpz).st := L
  exact ⟨sl_avAcc ar hA hK (fun _ _ => hX) hent (fun _ _ => hks) (fun _ _ => hf) hTN (fun _ _ => hH) hV hUo,
    sl_avDec ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 (fun _ _ => hX) hent (fun _ _ => hks) (fun _ _ => hf),
    IsProg.on hpz.choose_spec.1 _ _ _⟩

/-- The VCPU facts at a P3-related entry (`SlJAt`): `VcpuKs` (from `JKern.hksIn` and `VcpuHeap` [J]), the block's
fit (`JKern.ksbFit`), `HeapOK` (P3's placement `LayP.heap`) and `TabNoV` (from `VcpuTabOff` [J] / `PoolObj` [J]). -/
theorem slJAt_vfacts {s : S} (h : SlJAt (L := L) K.toKLayout s) (hV : VcpuHeap K) (hT : VcpuTabOff K)
    (hPo : PoolObj (L := L) K s) :
    VcpuKs K ∧ K.ksb.val + 13568 ≤ 2 ^ 64 ∧ HeapOK K.heap ∧ TabNoV (L := L) K s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := h
  have hk : K.ksb = L.ksb s := B.ksb.symm
  have hH : HeapOK K.heap := B.layP.heap
  have hf := B.j.kern.ksbFit
  rw [← hk] at hf
  exact ⟨vcpuKs_of_jkern B.j.kern rfl hk hV, hf, hH, tabNoV_of hH hV hT hPo hk⟩

/-- **`AvoidV` for syscall_local in the form the path families use** (`sl_localPathK`, `P2/SlJLay.lean`: P3's
bundle `SlJAt K s` at its start states): `sl_avoidV`'s VCPU premises from `SlJAt` (`slJAt_vfacts`), leaving
`RegionOKV` [J], `VcpuHeap` [J], `VcpuTabOff` [J], `PoolObj` [J] (per state) and `UserObj` [J]. -/
theorem sl_avoidVK (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKV K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlJAt (L := L) K.toKLayout s)
    (hPE : ∀ s, P s → SlPreB (st := st) ar K.toKLayout Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ s, P s → SlEntR (st := st) K.toKLayout Locks found s)
    (hHr : ∀ s, P s → SlHereR (st := st) K.toKLayout found s)
    (hAr : ∀ s, P s → SlAccR (st := st) ar K.toKLayout Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (hV : VcpuHeap K) (hT : VcpuTabOff K) (hPo : ∀ s, P s → PoolObj (L := L) K s) (hUo : UserObj K) :
    AvoidV K (sl_localPathK ar hSt hA hm a0 hK.base hU hJ hPE hEr hHr hAr huf hpz) := by
  have hKb := hK.base
  have hX : ∀ s, P s → RegionOKX K.toKLayout := fun s hP => (hJ s hP).regionOKX
  have VF : ∀ s, P s → VcpuKs K ∧ K.ksb.val + 13568 ≤ 2 ^ 64 ∧ HeapOK K.heap ∧ TabNoV (L := L) K s :=
    fun s hP => slJAt_vfacts (hJ s hP) hV hT (hPo s hP)
  have hent : ∀ s, P s → SlEntAll (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s := by
    intro s hP
    have E0 := hPE s hP
    have hSe := slSets_conv K.toKLayout
    have N := slEnt_of ar hSt hA (hX s hP) hSe a0 E0 ((hJ s hP).entJ E0.hN (hEr s hP))
    have Hh := slHere_of ar hSt hA (hX s hP) hSe a0 E0 N ((hJ s hP).hereJ (hHr s hP))
    exact ⟨E0, N, Hh, slAccIn_of ar hA hKb (hX s hP) hSe E0 N Hh
      (slAccJ_of ar hA hKb (hX s hP) (fun _ h => h) E0 ((hJ s hP).hereJ (hHr s hP)) ((hJ s hP).accK (hAr s hP)))⟩
  letI : LawfulStore (sl_localPathK ar hSt hA hm a0 hK.base hU hJ hPE hEr hHr hAr huf hpz).st := L
  exact ⟨sl_avAcc ar hA hK hX hent (fun s hP => (VF s hP).1) (fun s hP => (VF s hP).2.1)
      (fun s hP => (VF s hP).2.2.2) (fun s hP => (VF s hP).2.2.1) hV hUo,
    sl_avDec ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 hX hent (fun s hP => (VF s hP).1)
      (fun s hP => (VF s hP).2.1),
    IsProg.on hpz.choose_spec.1 _ _ _⟩

end av

end
end Fl4Proofs.P2.E2EV
