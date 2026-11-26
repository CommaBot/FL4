/-
# P2 (line p3mc, gen 15): the ReplyRecv arm's words at a view start (`rrDR_v`, `rrAcc_v`)

At an sl entry state `s` at core `c`'s view (`SlVC`), ReplyRecv arm, with the replied thread `u` (the reply object's
`TCB` word) homed on `c` in `ρ`:

* `nf_ntfn`, `sr_scw`: a notification word whose `BOUND_TCB` is a homed thread, an SC's first words;
* **`rrDR_v`**: `RrDR (SR K c ρ)` (the words a declining ReplyRecv arm reads, `rrDR_nu`'s walk);
* **`rrAcc_v`**: `RrAcc Z (SR K c ρ) (VNW K c ρ)` under the checks (`rrAccNB_nu`'s walk, with the caller's IPC
  buffer words: user words, region `.none`, kept by the view).

**The caller's message registers and IPC buffer** (the words this arm reads that the VM arm does not): the
registers are TCB words of the current thread (homed on `c`, `SlVC.cur`), so `NotForeign`; the IPC buffer words are
user words (`SlAccIn.rbuf`), in no region, so the view keeps them (`view` rewrites only TCB / SC / node words) and
their owner (`.gate` at every memory). Nothing about them depends on which core is looking.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.SlVAcc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE InW)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec NotForeign vn_of_nf nf_node nf_sc nf_slot nf_none nf_tcb vn_td
  view_keep_tcb vkc_of not_vdec_node not_vdec_sc not_vdec_tcb TZero decOff_list)

noncomputable section
open Classical

theorem nf_ntfn {Kl : KLayout} {c : U64} {ρ : U64 → U64} {b p : U64} (hr : region Kl b = .ntfn p)
    (hn : Kl.heap (ρ (fld p 24#u64)) = some .tcb → ρ (fld (ρ (fld p 24#u64)) oAFFINITY) = c) :
    NotForeign Kl c ρ b := by
  unfold NotForeign
  refine ⟨fun t h => ?_, fun p' h => ?_, fun d h => ?_, fun p' h => ?_⟩ <;> rw [hr] at h <;> cases h
  exact hn

theorem sr_scw {K : KLayoutP} {c : U64} {ρ : U64 → U64} (hK : RegionOKP K) (hX : RegionOKX K.toKLayout)
    {p : U64} {z : Nat} (hz : K.toKLayout.heap p = some (.sc z)) (hc : ρ (fld p 16#u64) = c) {o : U64}
    (ho : o.val < 128) (h8 : o.val % 8 = 0) : SR K c ρ (core.num.U64.wrapping_add p o) := by
  obtain ⟨-, -, hin, -⟩ := sc_off hX hz ho h8
  exact (srw_sc hK hX hz hc hin).1

section rec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {K : KLayoutP} {c : U64} {ρ : U64 → U64} {Locks : S → U64 → Prop} {m0 : U64 → U64} {n : I64}
  {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 8000000 in
/-- **The ReplyRecv checks' read words are `SR`** (module docstring), the replied thread homed on `c`. -/
theorem rrDR_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1))
    (hU : ∀ u, L.mem X (rTcbA found.1) = u → u ≠ 0#u64 → ρ (fld u oAFFINITY) = c) :
    RrDR (L := L) (SR K c ρ) X (L.curW s) found.1 found.2 := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have hK := V.hK
  have hX := B.regionOKX
  obtain ⟨hk, hcp⟩ := B.kc
  have C := slCom_v ar hA V B E LP
  have hcH := E.hSt.1
  obtain ⟨hrp, hep⟩ := B.rrG F.C.fd hS (F.C.arm hS)
  obtain ⟨⟨Q, Rq, hq⟩, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have tw : ∀ y, K.toKLayout.heap y = some .tcb → ρ (fld y oAFFINITY) = c → ∀ o : U64, 192 ≤ o.val →
      o.val < 4096 → o.val % 8 = 0 → SR K c ρ (core.num.U64.wrapping_add y o) :=
    fun y hy hya o h1 h2 h3 => sr_tcb hK hX hy hya h1 h2 h3
  have uT : ∀ u, L.mem X (rTcbA found.1) = u → u ≠ 0#u64 → K.toKLayout.heap u = some .tcb := fun u hu hu0 => by
    obtain ⟨-, hT', -, -⟩ := hXI.2.1.back _ hrp (by rw [hu]; exact hu0)
    rw [hu] at hT'; exact hT'
  have eM : ∀ w, Aligned w → (∀ d, region K.toKLayout w ≠ .node d) →
      region K.toKLayout w ≠ .tcb (L.curW s) → L.mem X w = L.mem s w := fun w aw r1 r2 =>
    lp_mem ar hA E.hT E.hN E.hcT LP aw (not_slDS_reg hX E.hN E.hT E.hcT hcH hk hcp r1 r2)
  obtain ⟨KM, hKM, eKM⟩ := regA_eq (E.hT _ E.hcT) (r := layout.reg.MSG_INFO)
    (by simp [layout.reg.MSG_INFO])
  refine ⟨C.nd, C.dt, C.cd, C.tm, C.rh, tw _ hcH V.cur layout.tcb.STATE (by rw [st_val]; omega)
    (by rw [st_val]; omega) (by rw [st_val]), tw _ hcH V.cur 3464#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    tw _ hcH V.cur 3592#u64 (by simp) (by simp) (by simp), ?_, tw _ hcH V.cur 3368#u64 (by simp) (by simp) (by simp),
    tw _ hcH V.cur 3448#u64 (by simp) (by simp) (by simp), fun h0 => ?_,
    (srw_rp hK hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])).1,
    (srw_rp hK hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])).1,
    (srw_ep hK hX hep (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])).1,
    fun u hu hu0 => ?_, fun u hu hu0 _ => ?_, fun u hu hu0 _ hst hsc => ?_⟩
  · -- the current SC's `REFILL_MAX` (homed: its `TCB` back-pointer is the current thread)
    obtain ⟨hcS, htb, -⟩ := hX0.bound _ hcH h0
    have hz := scs_heap (K := K.toKLayout) hcS
    generalize L.mem X (scA (L.curW s)) = p at hcS htb hz
    obtain ⟨-, aT, -, rT⟩ := sc_off hX hz (o := layout.sc.TCB) (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
    have rT' : region K.toKLayout (scTcbA p) = .sc p := rT
    have eT : L.mem X (scTcbA p) = L.mem s (scTcbA p) :=
      eM _ aT (fun d => by rw [rT']; intro h; cases h) (by rw [rT']; intro h; cases h)
    have hpc : ρ (fld p 16#u64) = c :=
      V.scb p hcS (by rw [← eT, htb]; exact fun e => (E.hT _ E.hcT).ne0 (by rw [e]; rfl))
    exact sr_scw hK hX hz hpc (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
  · have hKM' : KM.val = 256 + 8 * layout.reg.MSG_INFO.val := hKM
    rw [eKM]
    exact tw _ hcH V.cur KM (by rw [hKM']; simp [layout.reg.MSG_INFO]) (by rw [hKM']; simp [layout.reg.MSG_INFO])
      (by rw [hKM']; simp [layout.reg.MSG_INFO])
  · -- the bound notification
    have eB : L.mem X (boundA (L.curW s)) = L.mem s (boundA (L.curW s)) :=
      lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hcH 3368#u64 (by simp) (by simp) (by simp)).2.2
        (not_slDS_tcb hX E.hN E.hT E.hcT hcH hk hcp hcH (by simp) (by simp) (by simp) (by simp))
    obtain ⟨hn, hbk⟩ := ntf_of ar hA hX (slSets_conv K.toKLayout) E hk hcp LP (by rw [← eB]; exact h0)
    rw [eB]
    generalize L.mem s (boundA (L.curW s)) = p at hn hbk
    obtain ⟨r24, -, a24⟩ := hX.ntW _ hn 24#u64 (by simp) (by simp)
    have hb : ρ (fld p 24#u64) = L.curW s := by
      have r24' : region K.toKLayout (fld p 24#u64) = .ntfn p := r24
      have e1 : view K.toKLayout c ρ (fld p 24#u64) = ρ (fld p 24#u64) := view_ntfn r24'
      have e2 : L.mem s (fld p 24#u64) = view K.toKLayout c ρ (fld p 24#u64) :=
        V.hm (fld p 24#u64) a24 (hX.kern _ (by rw [r24']; intro h; cases h))
      rw [← e1, ← e2]; exact hbk
    have hnf : ∀ b, region K.toKLayout b = .ntfn p → NotForeign K.toKLayout c ρ b := fun b hr =>
      nf_ntfn hr (fun _ => by rw [hb]; exact V.cur)
    obtain ⟨r1, -, -⟩ := hX.ntW _ hn layout.ntfn.TAIL_STATE (by simp [layout.ntfn.TAIL_STATE])
      (by simp [layout.ntfn.TAIL_STATE])
    obtain ⟨r2, -, -⟩ := hX.ntW _ hn layout.ntfn.SC (by simp [layout.ntfn.SC]) (by simp [layout.ntfn.SC])
    exact ⟨sr_nf hK (by rw [r1]; intro h; cases h) (hnf _ r1), sr_nf hK (by rw [r2]; intro h; cases h) (hnf _ r2)⟩
  · have hu' := uT u hu hu0
    have ha := hU u hu hu0
    exact ⟨tw _ hu' ha 3464#u64 (by simp) (by simp) (by simp), tw _ hu' ha 3520#u64 (by simp) (by simp) (by simp),
      tw _ hu' ha 3432#u64 (by simp) (by simp) (by simp), tw _ hu' ha 3448#u64 (by simp) (by simp) (by simp)⟩
  · have hu' := uT u hu hu0
    have ha := hU u hu hu0
    exact ⟨tw _ hu' ha layout.tcb.STATE (by rw [st_val]; omega) (by rw [st_val]; omega) (by rw [st_val]),
      tw _ hu' ha 3376#u64 (by simp) (by simp) (by simp), tw _ hu' ha 3592#u64 (by simp) (by simp) (by simp)⟩
  · have huT : u ∈ K.toKLayout.heap.tcbs := uT u hu hu0
    obtain ⟨hcS, htb, -⟩ := hX0.bound u huT hsc
    have hact := hB.sact u huT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst)))))) hsc
    have hWF := (hSC.all _ hcS).1 ((hSC.act _ hcS).1 hact)
    have hz := scs_heap (K := K.toKLayout) hcS
    generalize L.mem X (scA u) = p at hcS htb hWF hz
    obtain ⟨-, aT, -, rT⟩ := sc_off hX hz (o := layout.sc.TCB) (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
    have rT' : region K.toKLayout (scTcbA p) = .sc p := rT
    have eT : L.mem X (scTcbA p) = L.mem s (scTcbA p) :=
      eM _ aT (fun d => by rw [rT']; intro h; cases h) (by rw [rT']; intro h; cases h)
    have hpc : ρ (fld p 16#u64) = c := V.scb p hcS (by rw [← eT, htb]; exact hu0)
    exact ScAcc.head (scAcc_v hK hX hz hpc) hWF

set_option maxHeartbeats 8000000 in
/-- **The accepted ReplyRecv arm's words are kept by the view** (module docstring), the replied thread homed. -/
theorem rrAcc_v (hA : P0.ArchTotal ar) {s : S}
    (F : SlOF (st := st) ar K.toKLayout Locks m0 n found Cs Ω Sg Ac s) (V : SlVC (L := L) K c ρ s)
    (hS : ¬ SlTrap st s) {a X a1} (LP : LocalPre (st := st) ar s a (X, a1)) {u usc : U64}
    (hc : RRChecks st ar X a1 (L.curW s) found.1 found.2 u usc) (hUa : ρ (fld u oAFFINITY) = c) :
    RrAcc (L := L) K.toKLayout.heap.scBits (SR K c ρ) (VNW K c ρ) X (L.curW s) found.1 found.2 u usc := by
  have B := F.B
  have E := F.E
  have Hh := F.Hh
  have N := F.N
  have I := F.I
  have hK := V.hK
  have hX := B.regionOKX
  have C := slCom_v ar hA V B E LP
  obtain ⟨kX, cX, -, -, ecs, -⟩ := sl_pre_agree (Cs := ∅) ar hA E.hT E.hN E.hcT LP
  have hc0 := E.hSt.1
  obtain ⟨hut, hus, -, -, -⟩ := E.hSu hS a X a1 LP u usc hc
  have nT : ∀ {t o : U64}, K.toKLayout.heap t = some .tcb → 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      o.val ≠ 392 → ¬ SlDS (L := L) s (core.num.U64.wrapping_add t o) := fun ht h1 h2 h3 h4 =>
    not_slDS_tcb hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu ht h1 h2 h3 h4
  have hXu : L.mem X (rTcbA found.1) = u := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok] at h1
    exact h1.symm
  have D' := rrDR_v ar hA F V hS LP (fun u' hu' _ => by rw [← hu', hXu]; exact hUa)
  have eu : u = slThr st found.1 s := by
    have h1 := obj.Reply.tcb.blk (st := st) X found.1
    rw [hc.tcb, WP.spec_ok, slThr_hd_rr ar hA E.hT E.hN E.hcT I hS LP] at h1
    exact h1
  have lv : SlLive st found.1 s := slLive_rr (st := st) hS (by rw [← eu]; exact u_ne0 hc.u0)
  have haf : L.mem s (affA (slThr st found.1 s)) = L.cpu s := by rw [← eu, OwnMap.affA_fld]; exact hus.1
  have eusc : usc = L.mem s (scA u) := by
    have h1 := hc.sc
    rw [tcb_sc_ok] at h1
    rw [← ok_inj_ff h1]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ hut 3464#u64 (by simp) (by simp) (by simp)).2.2
      (nT hut (by simp) (by simp) (by simp) (by simp))
  have eXsc : L.mem X (scA u) = usc := by
    have h1 := hc.sc
    rw [tcb_sc_ok] at h1
    exact ok_inj_ff h1
  have husc0 : usc ≠ 0#u64 := by
    obtain ⟨b, hb, hn⟩ := hc.sc0
    rw [eq_of_spec_fd (obj.Sc.is_null.spec usc)] at hb
    rw [← ok_inj_ff hb] at hn
    simpa using hn
  have Hs := Hh.usc hS lv haf (by rw [← eu, ← eusc]; exact husc0)
  rw [← eu, ← eusc] at Hs
  obtain ⟨hz, hin0, hmx0, hco⟩ := Hs
  -- `usc` is homed in `ρ`: its `TCB` back-pointer is `u`
  obtain ⟨⟨Q, Rq, hq⟩, hB, hXI, -, hSC⟩ := E.hI a X a1 LP
  have hX0 := hXI.2.2.toScExtra0
  have hpc : ρ (fld usc 16#u64) = c := by
    have huT : u ∈ K.toKLayout.heap.tcbs := hut
    obtain ⟨hcS, htb, -⟩ := hX0.bound u huT (by rw [eXsc]; exact husc0)
    rw [eXsc] at hcS htb
    obtain ⟨-, aT, -, rT⟩ := sc_off hX hz (o := layout.sc.TCB) (by simp [layout.sc.TCB]) (by simp [layout.sc.TCB])
    have rT' : region K.toKLayout (scTcbA usc) = .sc usc := rT
    have eT : L.mem X (scTcbA usc) = L.mem s (scTcbA usc) :=
      lp_mem ar hA E.hT E.hN E.hcT LP aT (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
        (by rw [rT']; intro c h; cases h) (by rw [rT']; intro h; cases h))
    exact V.scb usc hcS (by rw [← eT, htb]; exact u_ne0 hc.u0)
  have hrp := N.hrp hS
  have hepH := Hh.ep hS
  obtain ⟨-, aC, hinC, rC⟩ := sc_off hX hz (o := layout.sc.CORE) (by simp [layout.sc.CORE]) (by simp [layout.sc.CORE])
  have eC : L.mem X (core.num.U64.wrapping_add usc layout.sc.CORE) = L.cpu X := by
    rw [lp_mem ar hA E.hT E.hN E.hcT LP aC (not_slDS_reg hX E.hN E.hT E.hcT hc0 Hh.ksb Hh.cpu
      (by rw [rC]; intro c h; cases h) (by rw [rC]; intro h; cases h)), cX]
    have e : core.num.U64.wrapping_add usc layout.sc.CORE = fld usc 16#u64 := by simp [fld, layout.sc.CORE]
    rw [e]
    exact hco
  have hts0 : L.mem X (scA (L.curW s)) ≠ 0#u64 := by
    obtain ⟨b0, hsch0, hb0⟩ := hc.sch
    subst hb0
    have hsp := sched.is_schedulable.spec' (L := L) X (L.curW s)
    rw [hsch0, WP.spec_ok] at hsp
    exact (hsp rfl).2.1
  have nX : ∀ o, L.nodeAt X (L.cpu X) o = L.nodeAt s (L.cpu s) o := fun o => by
    rw [cX, nodeAt_of_ksb kX]
  have eRh : L.mem X (rhA (L := L) X) = L.mem s (rhA (L := L) s) := by
    show L.mem X (L.nodeAt X (L.cpu X) layout.node.RELEASE_HEAD) =
      L.mem s (L.nodeAt s (L.cpu s) layout.node.RELEASE_HEAD)
    rw [nX]
    exact lp_mem ar hA E.hT E.hN E.hcT LP (nodeAt_aligned E.hN (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD])) (not_slDS_node E.hN E.hT E.hcT (by simp [layout.node.RELEASE_HEAD])
      (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  have trc : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add (L.curW s) o) := fun o h1 h2 h3 => sr_tcb hK hX hc0 V.cur h1 h2 h3
  have twc : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → o.val ≠ 3520 →
      VNW K c ρ (core.num.U64.wrapping_add (L.curW s) o) := fun o h1 h2 h3 h4 =>
    vnw_tcb hK hX hc0 V.cur h1 h2 h3 h4
  have tru : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 →
      SR K c ρ (core.num.U64.wrapping_add u o) := fun o h1 h2 h3 => sr_tcb hK hX hut hUa h1 h2 h3
  have twu : ∀ o : U64, 192 ≤ o.val → o.val < 4096 → o.val % 8 = 0 → o.val ≠ 3520 →
      VNW K c ρ (core.num.U64.wrapping_add u o) := fun o h1 h2 h3 h4 =>
    vnw_tcb hK hX hut hUa h1 h2 h3 h4
  exact
  { nd := fun o h1 h2 => by rw [nX]; exact srw_node V B E.hN h1 h2
    dt := C.dt
    cd := C.cd
    kr := by
      show SR K c ρ (core.num.U64.wrapping_add (L.ksb X) layout.ks.KERNEL_ROOT)
      rw [kX]
      exact sr_ks V B E.hN (by simp [layout.ks.KERNEL_ROOT]) (by simp [layout.ks.KERNEL_ROOT])
    tab := rdTab_v ar hA V B E Hh F.Ai LP
    tSt := D'.tSt
    tSc := D'.tSc
    tMx := D'.tMx hts0
    tIq := D'.tIq
    tMi := D'.tMi
    tBn := D'.tBn
    tPr := D'.tPr
    tReg := fun _ hr => sr_reg hK hX hc0 V.cur hr
    tBuf := ⟨_, tcb_slot_val _ _, trc 3512#u64 (by simp) (by simp) (by simp),
      (sr_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).1, (sr_tslot hK hX hc0 (by simp [layout.tcb.SLOT_BUFFER])).2⟩
    tBw := fun buf hb hne i hi => (srw_user hK hX (F.Ai.rbuf hS a X a1 LP buf hb hne i hi).2 V.upte).1
    ntf := fun nt hnt hne => by
      have e1 := (eq_of_spec_fd (obj.Tcb.bound_ntfn.val X (L.curW s))).symm.trans hnt
      have en : nt = L.mem X (boundA (L.curW s)) := (ok_inj_ff e1).symm
      subst en
      exact D'.ntf (fun h0 => by rw [h0] at hne; simp at hne)
    wRp := twc 3360#u64 (by simp) (by simp) (by simp) (by simp)
    wEn := twc 3496#u64 (by simp) (by simp) (by simp) (by simp)
    wEp := twc 3504#u64 (by simp) (by simp) (by simp) (by simp)
    rRt := (srw_rp hK hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])).1
    rNx := (srw_rp hK hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])).1
    rPv := (srw_rp hK hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])).1
    wNx := (srw_rp hK hX hrp (o := layout.reply.NEXT) (by simp [layout.reply.NEXT]) (by simp [layout.reply.NEXT])).2
    wPv := (srw_rp hK hX hrp (o := layout.reply.PREV) (by simp [layout.reply.PREV]) (by simp [layout.reply.PREV])).2
    wRt := (srw_rp hK hX hrp (o := layout.reply.TCB) (by simp [layout.reply.TCB]) (by simp [layout.reply.TCB])).2
    uSt := by rw [stA_eq]; exact tru 3328#u64 (by simp) (by simp) (by simp)
    uFt := ⟨tru 3376#u64 (by simp) (by simp) (by simp), twu 3376#u64 (by simp) (by simp) (by simp) (by simp)⟩
    uSc := tru 3464#u64 (by simp) (by simp) (by simp)
    uPr := tru 3448#u64 (by simp) (by simp) (by simp)
    uAf := tru 3520#u64 (by simp) (by simp) (by simp)
    uDo := tru 3432#u64 (by simp) (by simp) (by simp)
    uIq := tru 3592#u64 (by simp) (by simp) (by simp)
    uMx := sr_scw hK hX hz hpc (o := layout.sc.REFILL_MAX) (by simp [layout.sc.REFILL_MAX])
      (by simp [layout.sc.REFILL_MAX])
    uReg := fun _ hr => vnw_reg hK hX hut hUa hr
    uYt := tru 3472#u64 (by simp) (by simp) (by simp)
    uFi := sr_reg hK hX hut hUa (r := layout.reg.FAULT_IP) (by simp [layout.reg.FAULT_IP])
    uVt := by
      rw [vtA_slot]
      exact sr_tslot hK hX hut (by simp [layout.tcb.SLOT_VTABLE])
    eTS := (srw_ep hK hX hepH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])).1
    wEh := (srw_ep hK hX hepH (o := layout.ep.HEAD) (by simp [layout.ep.HEAD]) (by simp [layout.ep.HEAD])).2
    wEt := (srw_ep hK hX hepH (o := layout.ep.TAIL_STATE) (by simp [layout.ep.TAIL_STATE])
      (by simp [layout.ep.TAIL_STATE])).2
    spo := sr_scw hK hX hz hpc (o := layout.sc.SPORADIC) (by simp [layout.sc.SPORADIC])
      (by simp [layout.sc.SPORADIC])
    cor := (srw_sc hK hX hz hpc hinC).1
    ccs := by
      rw [eC]
      exact (by rw [nX]; exact (srw_node V B E.hN (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC])).1)
    uHd := rdHead_v ar hA V B E Hh LP ⟨hz, hin0, hmx0, hco⟩ hpc
    uscA := scAcc_v hK hX hz hpc
    csc := by
      rw [ecs]
      obtain ⟨hz', -, -, -⟩ := Hh.cs
      exact scAcc_v hK hX hz' V.csc
    tm := C.tm
    rh := fun h => by
      refine ⟨(C.rh h).1, ?_, (C.rh h).2⟩
      rw [eRh] at h ⊢
      obtain ⟨ht, hs⟩ := Hh.rh h
      obtain ⟨-, hrS⟩ := V.rh h
      have eS : L.mem X (scA (L.mem s (rhA (L := L) s))) = L.mem s (scA (L.mem s (rhA (L := L) s))) :=
        lp_mem ar hA E.hT E.hN E.hcT LP (hX.tcbW _ ht 3464#u64 (by simp) (by simp) (by simp)).2.2
          (nT ht (by simp) (by simp) (by simp) (by simp))
      rw [eS]
      obtain ⟨hz', -, -, -⟩ := hs
      exact fun b _ hb => (srw_sc hK hX hz' hrS hb).1 }

end rec

end
end Fl4Proofs.P2.E2EP
