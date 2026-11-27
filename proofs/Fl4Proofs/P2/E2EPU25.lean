/-
# P2 (line p3mc, gen 27): U25, the CNodeDelete `VSafe9` discharged at the starts whose message has length ≥ 2

## The CNodeDelete starts discharged
`InvDelAt`: a CNodeDelete start (`invSlotU`, the summand `.inr (.inl (.inr j))`) where, in `ρ`, the message-info
register of core `c`'s current thread (the word `curThW K.ksb c`) decodes to a message of length at least 2
(`DelLenR`). Its certificate is `inv_del_annV` (P2/InvDelAnn); at the view start the view keeps the current thread
word (a node word of `c`) and its `MSG_INFO` register (the current thread is homed), so `InvLen` holds there
(`invLen_of_view`).

* `curThW`, `curThW_eq`, `DelLenR`, **`invLen_of_view`**;
* **`inv_annV_del`** (glue as `irq_annV_wh`: the start fact `StartV2C` at `.inr (.inl (.inr j))` gives the glue's
  state with `InvQF` and, by `qU_startN`, `QU`; the armed program is `cutP` of the path's body, `tr_cut`);
* `U25At := U24At ∨ InvDelAt`, **`serializable_fl4_localU25`**, **`serializable_fl4_localU24of25`**.

## Premises of `serializable_fl4_localU25` vs `serializable_fl4_localU24`
* **Removed: `VSafe9` [J] at every CNodeDelete (`invSlotU`) start whose caller's message has, in `ρ`, length at
  least 2.** Nothing added; family and start facts unchanged (`fl4LocW11JC` ⊕ invocations / `StartV2C` [P]).
* Open: `VSafe9` [J] at the truncated CNodeDelete starts (length < 2: the error reply reads the caller's IPC buffer,
  a user word, which `safe_tr_wr`'s read set may not hold), at the PTE-delete and Copy / Mint starts; `VSafe` [J].

No existing statement changed except the root import list.
-/
import Fl4Proofs.P2.E2EPU24
import Fl4Proofs.P2.InvDelAnn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW)
open Fl4Proofs.P2.E2E (StartAt SP SerStep LocalPath tr masksOf)
open Fl4Proofs.P2.Serial (Owner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg NextH VEq Safe narrowSP PO HeldV)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDD VDec nf_node)

noncomputable section
open Classical

/-- The word of core `c`'s node holding its current thread, from the kernel-global base `kb`. -/
def curThW (kb c : U64) : U64 :=
  core.num.U64.wrapping_add
    (core.num.U64.wrapping_add (core.num.U64.wrapping_add kb 13568#u64) (core.num.U64.wrapping_mul c 4288#u64))
    layout.node.CUR_THREAD

theorem curThW_eq {S : Type} {st : machine.Store S} [L : LawfulStore st] {σ : S} {kb c : U64}
    (hk : L.ksb σ = kb) (hc : L.cpu σ = c) : L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD = curThW kb c := by
  unfold LawfulStore.nodeAt curThW
  rw [hk, hc]

/-- **In `ρ`, core `c`'s current thread's message has length at least 2** (module docstring). -/
def DelLenR (ρ : U64 → U64) (kb c : U64) : Prop :=
  ∀ info, msginfo.MessageInfo.from_word_clamped (ρ (regA (ρ (curThW kb c)) layout.reg.MSG_INFO)) = ok info →
    2 ≤ info.length.val

section len
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`InvLen` at a view start from `DelLenR`** (module docstring). -/
theorem invLen_of_view {K : KLayoutP} (hK : RegionOKP K) {c : U64} {ρ : U64 → U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ) (hq : QPs K st σ) (hc : L.cpu σ = c)
    (hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x)
    (hf : DelLenR ρ K.ksb c) : InvLen st σ := by
  have hX := hJ.regionOKX
  obtain ⟨Ac', B⟩ := bunIx_of hJ
  have hI := B.bxi
  have hL := B.stLay
  have h0 := hI.1.choose_spec.choose_spec
  have hT : TcbPlaced K.toKLayout.heap.tcbs := h0.tcbs
  have hN : NodePlaced st K.toKLayout.heap.tcbs σ (L.cpu σ) := h0.nodes _ h0.cur
  have hcT : L.curW σ ∈ K.toKLayout.heap.tcbs := h0.curT
  have htH : K.toKLayout.heap (L.curW σ) = some .tcb := hcT
  have hcur := vx_cur_home hJ hmm
  have eC : L.curW σ = ρ (curThW K.ksb c) := by
    have ho : layout.node.CUR_THREAD.val < 4288 := by rw [curth_val]; omega
    have hr : region K.toKLayout (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) = .node c := by
      rw [hL.nd _ ho, hc]
    have sr : SR K c ρ (L.nodeAt σ (L.cpu σ) layout.node.CUR_THREAD) :=
      sr_nf hK (by rw [hr]; intro h; cases h) (nf_node hr)
    unfold LawfulStore.curW
    rw [hmm _ (nodeAt_aligned hN ho (by rw [curth_val])) (hL.nu_node ho), sr.1.1, curThW_eq hq.ksb hc]
  have eM : L.mem σ (regA (L.curW σ) layout.reg.MSG_INFO) =
      ρ (regA (L.curW σ) layout.reg.MSG_INFO) := by
    obtain ⟨o, ho, e⟩ := regA_eq' (t := L.curW σ) (r := layout.reg.MSG_INFO) (by simp [layout.reg.MSG_INFO])
    rw [e]
    have hs := sr_tcb hK hX htH hcur (o := o) (by omega) (by simp [layout.reg.MSG_INFO] at ho; omega)
      (by simp [layout.reg.MSG_INFO] at ho; omega)
    rw [hmm _ (field_aligned (hT _ hcT) (by simp [layout.reg.MSG_INFO] at ho; omega)
      (by simp [layout.reg.MSG_INFO] at ho; omega))
      (hL.nu_tcb hcT (k := o) (by omega) (by simp [layout.reg.MSG_INFO] at ho; omega)), hs.1.1]
  intro t info ht hi
  rw [cur_thread_ok] at ht
  obtain rfl := ok_inj_ff ht
  unfold msg.msg_info at hi
  rw [reg_ok] at hi
  simp only [bind_ok] at hi
  rw [eM, eC] at hi
  exact hf info hi

end len

section all
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A) (hA : P0.ArchTotal ar) (a0 : A)
variable {A3 : Type} {arI : machine.Arch A3} {AR : A3 → Fl4Spec.Cr3 → Prop} {MR : A3 → Fl4Spec.MachineState → Prop}

/-- **The CNodeDelete starts whose caller's message has length at least 2 in `ρ`** (module docstring). -/
def InvDelAt (K : KLayoutP) (c : U64) (_hs : U64 → Prop) (ρ : U64 → U64) (_k0 : SP) :
    (Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) → Prop
  | .inr (.inl (.inr _)) => DelLenR ρ K.ksb c
  | _ => False

/-- **The exempt starts of U25**: U24's and the CNodeDelete starts of length at least 2. -/
def U25At (K : KLayoutP) (c : U64) (hs : U64 → Prop) (ρ : U64 → U64) (k0 : SP)
    (i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)) : Prop :=
  U24At (S := S) K c hs ρ k0 i ∨ InvDelAt (S := S) K c hs ρ k0 i

set_option maxHeartbeats 8000000 in
/-- **U9's re-annotated body is `Safe` at every CNodeDelete start of length at least 2** (module docstring). -/
theorem inv_annV_del {Ch : S → Prop}
    {s : Cfg U64 U64 U64 U64} {K : KLayoutP} {hK : RegionOKP K} {hU : UserOKP K} {c : U64} {k : SP}
    {ρ : U64 → U64} {i : Fl4IxW (S := S) ⊕ ((InvArg S ⊕ InvArg S) ⊕ InvArg S)}
    (hC : ∃ σe, ChainOf (L := L) arI AR MR σe K.toKLayout Ch) (hE : EpochPteN K (CoreView.view K.toKLayout c ρ))
    (hsf : StartV2C st ar hA a0 arI AR MR Ch K (CoreView.view K.toKLayout c ρ) hK hU c (fun l => s.lk l = some c) k i)
    (hM : MapsP K s) (hV : VEq s.own s.cls s.ko c (fun l => s.lk l = some c) ρ s.mem)
    (hf : InvDelAt (S := S) K c (fun l => s.lk l = some c) ρ k i) :
    Safe s.own s.cls s.ko c (fun l => s.lk l = some c) s.mem (annV s K c ρ k) := by
  rcases i with (j | ((j | j) | j))
  · exact False.elim hf
  · exact False.elim hf
  · obtain ⟨σe, hC'⟩ := hC
    have hσe : Ch σe := by
      obtain ⟨_, _, _, _, _, _, _, _, h'⟩ := hC'
      exact h'
    have hsf' := hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v
    obtain ⟨q0, ⟨h, σ, a, he, hc, hl, hμ, e⟩, rfl⟩ := hsf'
    subst e
    have hJ : SlJAt (L := L) K.toKLayout σ := ChainOf.bun hC' σ he.1
    have hmm : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = view K.toKLayout c ρ x := hμ
    have hqu : QU st K σ :=
      qU_startN st ⟨σe, ChainOf.bun hC' σe hσe⟩ hJ hE (fun x hx hu => hμ x hx hu)
    have hc' : L.cpu σ = c := hc
    have hl' : j.Locks σ = (fun l => s.lk l = some c) := hl
    have hlen : InvLen st σ := invLen_of_view hK hJ hqu.1 hc' hmm hf
    unfold annV
    rw [hM.own, hM.cls, hM.ko] at hV ⊢
    have h1 := inv_del_annV ar hA hK hU h.nv hV (number := j.number) (a := a) hJ he.2 hqu hc' hl' hmm hlen
    rw [tr_cut (InvCMRS (st := st) K.toKLayout j.Locks σ) (· ∈ K.ptes) (· ∈ K.user) (OwnMap.cls K.toKLayout)
      (OwnMap.ko K.toKLayout (view K.toKLayout c ρ)) c (L.ksb σ) (masksOf st σ) ar
      (R.invBodyG j.number j.p) ∅ a] at h1
    have eRS : (invPathVU st ar hA (masksWr_plain st) j K (view K.toKLayout c ρ) hK hU h).RS σ =
        InvCMRS (st := st) K.toKLayout j.Locks σ :=
      funext fun x => propext ⟨fun h' => h'.1, fun h' => ⟨h', not_vData_empty h.nv⟩⟩
    convert h1 using 3
    unfold LocalPath.body
    rw [hc, eRS]
    all_goals rfl
  · exact False.elim hf

/-- **FL4 end to end with CNodeDelete's `VSafe9` discharged at the starts of length at least 2** (module
docstring), over U18's family. The conclusion is about the physical memory. -/
theorem serializable_fl4_localU25 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U25At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem := by
  obtain ⟨hK0, hU0⟩ := okP_R (hB 0#u64) hc0
  refine serializable_e2ePV9 _ h0 hA0 hK0 hU0 hM0 (execPV9_of_WPRV10S ?_ ?_ ?_ P h0 hA0 hB hc0 hM0 h).1 hq
  · intro Ch K s hK hU c hs q i hC hE hsf
    rcases i with i | ((j | j) | j)
    · exact startAt_UNC st ar hA a0 P hIoa hC hE hsf
    · exact delPteStart_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact invStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
    · exact cmStartU2_atN st ar hA (masksWr_plain st) hC hE (hsf.2 fun _ s b v _ _ _ => hsf.1.wr s b v)
  · intro s K hK hU c k ρ i hM hV hn
    exact vSafe_ioC st ar hA a0 hM hV (not_not.mp hn)
  · intro Ch s K hK hU c k ρ i hC hE hsf hM hV hf
    rcases hf with (((((((((((hf | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf) | hf)
    · exact vmF_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact vmR_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact sl_annV_allC st ar hA a0 P hIoa hC hE hsf hM hV hf
    · exact st_annV_fh st ar hA a0 hC hE hsf hM hV hf
    · exact st_annV_h st ar hA a0 hC hE hsf hM hV hf
    · exact vx_annV st ar hA a0 hsf hM hV hf
    · exact vt_annV st ar hA a0 hE hsf hM hV hf
    · exact irq_annV_fh st ar hA a0 hC hE hsf hM hV hf
    · exact irq_annV_hn st ar hA a0 hC hE hsf hM hV hf
    · exact irq_annV_wf st ar hA a0 hC hE hsf hM hV hf
    · exact irq_annV_wh st ar hA a0 hC hE hsf hM hV hf
    · exact inv_annV_del st ar hA a0 hC hE hsf hM hV hf

/-- **U24's statement follows from U25** (every U24 execution is a U25 one). -/
theorem serializable_fl4_localU24of25 (P : LocPlat st arI AR MR) (hIoa : Fl4Proofs.P3.MRKeepIoapic arI MR)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP} {Ch0 Ch : U64 → S → Prop} (h0 : Init s0)
    (hA0 : ArmInv s0) (hB : ∀ e, SerExitW P K0.toKLayoutV (Ch0 e)) (hc0 : K0.vcpus = ∅ ∧ K0.ptes = ptesR K0 s0.mem)
    (hM0 : MapsP K0 s0)
    (h : ExecWPRV10 (PathsP.sum (fl4LocW11JC st ar hA (masksWr_plain st) L.total a0)
        (PathsP.sum (PathsP.sum (delPteSlot st ar hA (masksWr_plain st)) (invSlotU st ar hA (masksWr_plain st)))
          (cmSlotU st ar hA (masksWr_plain st))))
      (fun i => ¬ IoIx (S := S) i) (U24At (S := S)) (StartV2C st ar hA a0 arI AR MR) P s0 K0 Ch0 s K Ch)
    (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_fl4_localU25 st ar hA a0 P hIoa h0 hA0 hB hc0 hM0
    (execWPRV10_mono (fun _ _ _ _ _ _ hf => Or.inl hf) h) hq

end all

end
end Fl4Proofs.P2.E2EP
