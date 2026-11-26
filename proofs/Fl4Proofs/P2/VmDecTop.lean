/-
# P2 (line p3mc, gen 10): the declining vmF starts at the view (items 1 and 2 of handoff p3mc §12)

* **`vm_view_cert`**: at a vmF start state `σ` at core `c`'s view (`VmPre (userV K)`, `QPs`, `IoLayA`, no VCPU, core
  `c`, locks `hs`, memory the view on aligned kernel words), if the run from every state agreeing with `σ` on
  `Rd := IoRS (userP K) σ ∧ VN K c ρ` declines and runs the same on the store guarded to `Rd` (writes: the two prefix
  words), then U9's armed program `narrowSP cls (ko μ) c (VO K c ρ) ∅ (body σ a)` is `Safe` at the physical memory
  (`PathObl.vm_guard_cert`, the pins of `vmF_fh_annV`, `E2E.safe_narrow_tr`);
* **`vmF_act_annV`** (item 1, the current SC homed): the prefix state's action is not `RESUME_CURRENT` and
  `ρ (CORE csc) = c`: the run stops at the action check (`vm_local_act_guard`);
* **`vmF_nogo_annV`** (item 2): the prefix action is `RESUME_CURRENT` and wherever the fault-handler slot holds an
  endpoint cap whose endpoint receives, the cap grants nothing and the head is homed on `c` in `ρ`: the run is not
  accepted (`FaultChecks.cap` needs a grant) and reads `Rd` only (`vm_local_guard_dec`, the head's words `VN` since
  it is homed).

The vmF starts left after these and `FHStart`: action 0 with a granting endpoint cap, the endpoint receiving and its
head homed (item 3, `vm_accN`), and action ≠ 0 with the current SC another core's (module `E2EPU11`'s docstring).

No premise: every fact is a hypothesis of the theorems. No existing statement changed.
-/
import Fl4Proofs.P2.VmDecView
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (SP tr masksOf)
open Fl4Proofs.P2.Serial (Owner VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN vn_of_nf nf_node nf_tcb)

noncomputable section
open Classical

section main
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {Locks : S → U64 → Prop}

set_option maxHeartbeats 2000000 in
/-- **The re-annotated body at a view start whose runs decline on the view's words** (module docstring). -/
theorem vm_view_cert (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {addr code : U64} {σ : S} {a : A}
    (hP : VmPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (HD : ∀ x : S, Ag st (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) σ x →
      ∀ r, syscall.handle_vm_fault_local st ar x a addr code = ok r →
      r.1 ≠ true ∧ syscall.handle_vm_fault_local
        (PathObl.guard st (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b)
          (fun b => b = ctA (L := L) σ ∨ b = cnA (L := L) σ)) ar x a addr code = ok r) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_vm_fault_local addr code) ∅ a)) := by
  have P' : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ := vmFPre_userP hK hq.ks hP.1
  have B := hP.1.base
  have B' := P'.base
  let Rd : U64 → Prop := fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b
  let Ro : U64 → Prop := fun b => rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ b ∧ VO K c ρ b
  have hR0 : ∀ q, Rd q → Ro q ∧ q ∉ K.user := fun q hq' =>
    ⟨⟨⟨(ioRS_of_userP hq'.1).1, (ioRS_of_userP hq'.1).2⟩, hq'.2.2⟩, fun hu => hq'.1.2.1 (Or.inl (Or.inl hu))⟩
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)))⟩
  have rT : Rd (ctA (L := L) σ) := ndR _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN : Rd (cnA (L := L) σ) := ndR _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have rC : Rd (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
    ndR _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])
  have hRdρ : ∀ b, Rd b → ρ b = L.mem σ b := fun b hb =>
    (hb.2.1.symm.trans (hmm b hb.1.1 (fun hu => hb.1.2.1 (Or.inl (Or.inl hu)))).symm)
  have eown : ownP K (L.mem σ) = ownP K (view K.toKLayout c ρ) :=
    ownDepP hK hU _ _ fun x hx hu => hmm x hx hu
  have hRPO : ∀ x, x ∉ K.user → Ro x → PO c hs (ownP K μ x) := by
    intro x hu hx
    have h1 : PO c hs (ownP K (L.mem σ) x) := by
      rw [ownP_eq_own nv hx.1.2, ← hc, ← hl]
      exact po_of_rperm hx.1.1.2.2
    rw [eown, hx.2] at h1
    rw [hV.1 x h1]
    exact h1
  have hH : ∀ x, (x = ctA (L := L) σ ∨ x = cnA (L := L) σ) → HeldV c hs (ownP K μ x) := by
    intro x hx
    have hnd' : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → x = L.nodeAt σ (L.cpu σ) o →
        HeldV c hs (ownP K μ x) := by
      rintro o ho h8 rfl
      have hp : L.nodeAt σ (L.cpu σ) o ∉ K.ptes := fun hp =>
        (B'.nd (Locks := Locks) o ho h8).1.2.1 (Or.inr hp)
      rw [ownP_eq_own nv hp]
      have e := own_node (m := μ) (K := userV K.toKLayoutV) B.lay.io (B.inNode o ho)
      show HeldV c hs (OwnMap.own (userV K.toKLayoutV) μ _)
      rw [e]
      exact hc
    rcases hx with rfl | rfl
    · exact hnd' _ (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME]) rfl
    · exact hnd' _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]) rfl
  have hSO : ∀ (z : S) b v, (b = regA (L.curW σ) layout.reg.FAULT_IP ∨ b = ctA (L := L) σ ∨ b = cnA (L := L) σ) →
      StepOK (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) (· ∈ K.user) c hs (L.mem z)
        (L.mem (L.wr z b v)) := by
    intro z b v hb
    obtain ⟨ha, hsw⟩ := B.dsSafe (st := st) (b := b) hb
    exact stepOK_safeP hK nv hLA ha hsw
  have h := vm_guard_cert (own := ownP K) (cls := OwnMap.cls K.toKLayout) (kt := OwnMap.ko K.toKLayout μ)
    (User := (· ∈ K.user)) (moveHeldP hK) (ownDepP hK hU) hmk hA addr code (hs := hs) (μ := μ) (ρ := ρ) (a := a) hc
    (Rd := Rd) (Ro := Ro) (fun b hb => hb.1.1) hR0 hRdρ hRPO (fun x hx => hV.2.1 x hx) hH hSO rT rN rC HD
  exact E2E.safe_narrow_tr ar _ ∅ a μ h

set_option maxHeartbeats 2000000 in
/-- **Item 1, the current SC homed: the prefix action is not `RESUME_CURRENT`** (module docstring). -/
theorem vmF_act_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {addr code : U64} {σ : S} {a : A}
    (hP : VmPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hcH : ρ (fld (L.cscW σ) 16#u64) = c)
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1)) (hact : L.actionW s1 ≠ 0#u64) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_vm_fault_local addr code) ∅ a)) := by
  have P' : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ := vmFPre_userP hK hq.ks hP.1
  have B := hP.1.base
  have B' := P'.base
  have D' := vm_dfOf hA P' hP.2.1 eu
  have F : VmFhR st (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) σ s1 :=
    VmFhR.and (VmFhR.ofDF D') (vmFhR_vnH hA hK P' hc hmm hcH eu)
  have hRal : ∀ b, (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) b → Aligned b := fun b hb => hb.1.1
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)))⟩
  have rT := ndR layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN := ndR layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  have eact : ∀ x1 : S, Ag st (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) s1 x1 →
      L.actionW x1 = L.actionW s1 := fun x1 G1 => by
    unfold LawfulStore.actionW; rw [G1.node]
    exact G1.m _ (F.nd _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]))
  refine vm_view_cert hA hmk hK hU nv hLA hV hP hq hc hl hmm ?_
  intro x G r hr
  refine ⟨?_, ?_⟩
  · obtain ⟨b0, z, c0⟩ := r
    intro hb
    change b0 = true at hb
    subst hb
    obtain ⟨x1, a1', eu', ptr, badge, dest, rr, C⟩ := vm_acc_checks hr
    obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
    have h1 := C.act
    rw [eq_of_spec_fd (sched.action.spec (L := L) x1)] at h1
    have e := ok_inj_ff h1
    rw [eact x1 G1] at e
    apply hact
    rw [e]; unfold sched.ACTION_RESUME_CURRENT; rfl
  · have hct : (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) (ctA (L := L) x) := by
      show _ ∧ _
      have e : ctA (L := L) x = ctA (L := L) σ := G.node _
      rw [e]; exact rT
    have hcn : (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) (cnA (L := L) x) := by
      show _ ∧ _
      have e : cnA (L := L) x = cnA (L := L) σ := G.node _
      rw [e]; exact rN
    refine vm_local_act_guard hct (Or.inl (G.node _)) hcn (Or.inr (G.node _)) ?_ hr
    intro X1 a1' eu'
    obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
    obtain ⟨nd1, -, -, -, -, -⟩ := F.alt G1 (fun b hb => hb)
    have ecsc : L.cscW X1 = L.cscW s1 := by
      unfold LawfulStore.cscW LawfulStore.nodeA
      rw [G1.node]; exact G1.m _ (F.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
    have hsh := G1.rdHead F.suf
    rw [← ecsc] at hsh
    exact ⟨nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
      nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
      nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]), hsh,
      nd1 _ (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION]),
      by rw [eact X1 G1]; exact hact⟩

set_option maxHeartbeats 4000000 in
/-- **Item 2: action `RESUME_CURRENT`, the handler not reached or the cap granting nothing** (module docstring). -/
theorem vmF_nogo_annV (hA : P0.ArchTotal ar) (hmk : E2E.MasksWr st) {K : KLayoutP} (hK : RegionOKP K)
    (hU : UserOKP K) (nv : K.vcpus = ∅) (hLA : IoLayA K.toKLayout) {c : U64} {hs : U64 → Prop}
    {ρ μ : U64 → U64}
    (hV : VEq (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs ρ μ)
    {addr code : U64} {σ : S} {a : A}
    (hP : VmPre st ar (userV K.toKLayoutV) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ) (hq : QPs K st σ)
    (hc : L.cpu σ = c) (hl : Locks σ = hs)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hact : L.actionW σ = 0#u64)
    {s1 : S} {a1 : A} (eu : sched.update_timestamp st ar σ a = ok (s1, a1))
    (hno : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) →
      L.epState s1 ptr = obj.EP_RECV → (g = false ∧ gr = false) ∧ ρ (affA (L.mem s1 (epHeadA ptr))) = c) :
    Safe (ownP K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c hs μ
      (narrowSP (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout μ) c (VO K c ρ) ∅
        (tr (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) Locks) σ) (· ∈ K.user)
          (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
          (R.syscall.handle_vm_fault_local addr code) ∅ a)) := by
  have P' : VmFPre st ar (userP K) T Cs Ω U H Sg Rp Scs Nt Z Ac Locks σ := vmFPre_userP hK hq.ks hP.1
  have B := hP.1.base
  have B' := P'.base
  have D' := vm_dfOf hA P' hP.2.1 eu
  have hsc0 : L.mem σ (scA (L.curW σ)) ≠ 0#u64 := B.bxi.2.1.resume hact
  have F : VmFhR st (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) σ s1 :=
    VmFhR.and (VmFhR.ofDF D') (vmFhR_vn hA hK P' hc hmm hsc0 eu)
  have hRal : ∀ b, (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) b → Aligned b := fun b hb => hb.1.1
  have ndR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
      (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) (L.nodeAt σ (L.cpu σ) o) := fun o ho h8 =>
    ⟨(B'.nd (Locks := Locks) o ho h8).1, vn_of_nf hK (nf_node (by rw [← hc]; exact B.lay.io.node _ _ (B.inNode o ho)))⟩
  have rT := ndR layout.node.CUR_TIME (by simp [layout.node.CUR_TIME]) (by simp [layout.node.CUR_TIME])
  have rN := ndR layout.node.CONSUMED (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED])
  -- the words of a head homed on `c`
  have hdW : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW σ) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) → L.epState s1 ptr = obj.EP_RECV →
      ∀ off : U64, 192 ≤ off.val → off.val < 4096 → off.val % 8 = 0 →
        ¬ Fl4Proofs.P2.OwnMap.TimerField off.val → ¬ Fl4Proofs.P2.OwnMap.GField off.val →
        (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b)
          (core.num.U64.wrapping_add (L.mem s1 (epHeadA ptr)) off) := by
    intro sl ptr badge x' y g gr hsl hcap hst off h1 h2 h8 ht hG
    have hd : L.mem s1 (epHeadA ptr) ∈ T := (D'.ep sl ptr badge x' y g gr hsl hcap).2.2 hst
    have hdK : K.heap (L.mem s1 (epHeadA ptr)) = some .tcb := B.hT _ hd
    have hdA' := B.tp _ hd
    have hρh := (hno sl ptr badge x' y g gr hsl hcap hst).2
    have hrA : region K.toKLayout (affA (L.mem s1 (epHeadA ptr))) = .tcb (L.mem s1 (epHeadA ptr)) :=
      B.lay.io.tcbw _ hdK 3520#u64 (by simp) (by simp)
    have hnd : ∀ o : U64, o.val < 4288 → affA (L.mem s1 (epHeadA ptr)) ≠ L.nodeAt σ (L.cpu σ) o := by
      intro o ho e
      have h2' : region K.toKLayout (L.nodeAt σ (L.cpu σ) o) = .node (L.cpu σ) := B.lay.io.node _ _ (B.inNode o ho)
      rw [← e, hrA] at h2'
      cases h2'
    have hdA : Aligned (affA (L.mem s1 (epHeadA ptr))) := field_aligned hdA' (by simp) (by simp)
    have hAff : IoRS (st := st) (userP K) Locks σ (affA (L.mem s1 (epHeadA ptr))) :=
      D'.gate _ hd 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.GateField])
    have haff : L.mem s1 (affA (L.mem s1 (epHeadA ptr))) = L.cpu s1 := by
      obtain ⟨now, -, ex⟩ := upd_eq eu
      have hTa : Aligned (ctA (L := L) σ) := rT.1.1
      have hNa : Aligned (cnA (L := L) σ) := rN.1.1
      have key : ∀ b, Aligned b → b ≠ ctA (L := L) σ → b ≠ cnA (L := L) σ → L.mem s1 b = L.mem σ b := by
        intro b hb h1 h2
        rw [ex, L.mem_wr _ _ _ _ hNa hb, if_neg (fun h => h2 h.symm), L.mem_wr _ _ _ _ hTa hb,
          if_neg (fun h => h1 h.symm)]
      have e1 : L.mem s1 (affA (L.mem s1 (epHeadA ptr))) = L.mem σ (affA (L.mem s1 (epHeadA ptr))) :=
        key _ hdA (hnd _ (by simp [layout.node.CUR_TIME])) (hnd _ (by simp [layout.node.CONSUMED]))
      rw [e1, hmm _ hdA (fun hu => hAff.2.1 (Or.inl (Or.inl hu))), D'.c, hc]
      exact Fl4Proofs.P2.CoreView.view_aff hK.base.base hdK c ρ
    refine ⟨?_, vn_of_nf hK (nf_tcb (B.lay.io.tcbw _ hdK off h1 h2) hρh)⟩
    by_cases hg : Fl4Proofs.P2.OwnMap.GateField off.val
    · exact D'.gate _ hd off h1 h2 h8 hg
    · exact D'.home _ hd haff off h1 h2 h8 hg ht hG
  refine vm_view_cert hA hmk hK hU nv hLA hV hP hq hc hl hmm ?_
  intro x G r hr
  have hn : r.1 ≠ true := by
    obtain ⟨b0, z, c0⟩ := r
    intro hb
    change b0 = true at hb
    subst hb
    obtain ⟨x1, a1', eu', ptr, badge, dest, rr, C⟩ := vm_acc_checks hr
    obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
    obtain ⟨sl, x', y, g, gr, hS, hcap, hgr⟩ := C.cap
    rw [F.cur_alt G1] at hS
    obtain ⟨r0, r8⟩ := F.sl sl hS
    rw [cap_congr_ag G1 r0 r8] at hcap
    obtain ⟨rts, -⟩ := F.ep sl ptr badge x' y g gr hS hcap
    have hep := C.ep
    have eep : obj.Ep.state st ptr x1 = obj.Ep.state st ptr s1 := by
      rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) x1 ptr), eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)]
      unfold LawfulStore.epState
      rw [G1.m (epTSA ptr) rts]
    rw [eep, eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at hep
    obtain ⟨⟨hg0, hgr0⟩, -⟩ := hno sl ptr badge x' y g gr hS hcap (ok_inj_ff hep)
    subst hg0 hgr0
    rcases hgr with h | h <;> exact Bool.false_ne_true h
  refine ⟨hn, ?_⟩
  have hct : (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) (ctA (L := L) x) := by
    show _ ∧ _
    have e : ctA (L := L) x = ctA (L := L) σ := G.node _
    rw [e]; exact rT
  have hcn : (fun b => IoRS (st := st) (userP K) Locks σ b ∧ VN K c ρ b) (cnA (L := L) x) := by
    show _ ∧ _
    have e : cnA (L := L) x = cnA (L := L) σ := G.node _
    rw [e]; exact rN
  refine vm_local_guard_dec hct (Or.inl (G.node _)) hcn (Or.inr (G.node _)) ?_ hr hn
  intro x1 a1' eu'
  obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
  obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := F.alt G1 (fun b hb => hb)
  have ecur1 := F.cur_alt G1
  have ecsc : L.cscW x1 = L.cscW s1 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [G1.node]; exact G1.m _ (F.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  have hsh := G1.rdHead F.suf
  rw [← ecsc] at hsh
  refine ⟨nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
    nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]), hsh, ?_⟩
  rw [ecur1]
  refine ⟨nd1, dt1, cd1, bm1, tm1, rh1, fun sl hsl => F.sl sl hsl, ?_⟩
  intro sl ptr b x' y g gr hsl hcap
  obtain ⟨r0, r8⟩ := F.sl sl hsl
  rw [cap_congr_ag G1 r0 r8] at hcap
  obtain ⟨rts, rhd⟩ := F.ep sl ptr b x' y g gr hsl hcap
  refine ⟨rts, rhd, fun hst d hd => ?_⟩
  have hst1 : L.epState s1 ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) x1 ptr)] at hst
    rw [← ok_inj_ff hst]
    unfold LawfulStore.epState
    rw [G1.m (epTSA ptr) rts]
  have hdd : d = L.mem s1 (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr)] at hd
    rw [← ok_inj_ff hd]; exact G1.m (epHeadA ptr) rhd
  have W := hdW sl ptr b x' y g gr hsl hcap hst1
  rw [← hdd] at W
  refine ⟨W 3360#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
      (by simp [Fl4Proofs.P2.OwnMap.GField]),
    W 3520#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
      (by simp [Fl4Proofs.P2.OwnMap.GField]), fun _ => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact W 3432#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
      (by simp [Fl4Proofs.P2.OwnMap.GField])
  · exact W 3464#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
      (by simp [Fl4Proofs.P2.OwnMap.GField])
  · exact W 3592#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
      (by simp [Fl4Proofs.P2.OwnMap.GField])
  · exact W 3448#u64 (by simp) (by simp) (by simp) (by simp [Fl4Proofs.P2.OwnMap.TimerField])
      (by simp [Fl4Proofs.P2.OwnMap.GField])

end main

end
end Fl4Proofs.P2.E2EP
