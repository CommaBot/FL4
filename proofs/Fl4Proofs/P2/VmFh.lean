/-
# P2 (line p3mc, gen 8): the VM-fault body at a store state whose fault handler is another core's (the decline split)

At core `c`'s view every thread looks homed on `c`; the real memory says the fault handler `d` (the head of the
fault endpoint) is homed on another core. U9's certificate runs at a store state `x` carrying the real values
(`ViewSafeReal.safe_tr_of_states`), which is no alternative of the view's entry state `s`: it agrees with `s` only on
a read set `Rd` (the words the view keeps), and its `AFFINITY` of `d` is not `c`. This module gives the run at such
an `x`, for **any** read set `Rd` holding the words below (`VmFhR`), from the entry facts at `s` only through `Rd`:

* `VmFhR Rd s s1`: `VmDF` (`P2/AccessVmDec.lean`) restricted to what the declining fast path reads up to the
  handler's `AFFINITY` (node words, `DOMAIN_TIME` / `CUR_DOMAIN`, the current thread's fault-handler slot, the
  endpoint's state and head, the `TIMER_MIN` deadline, the release head, the current SC's refill head), with `Rd`
  for `IoRS`; `VmFhR.alt` moves it to `x`'s prefix state;
* **`vm_fh_not_acc`**: if `x`'s prefix state sees the handler off its core, `x`'s run is not accepted
  (acceptance needs `schedulable_here d`, which needs `d`'s `AFFINITY` to be the core: `here_facts`);
* **`vm_fh_guard`**: so `x`'s run declines and runs the same on `PathObl.guard st R'' W`, `R''` holding `Rd`, the
  handler's `REPLY_OBJ` and `AFFINITY`, `W` the two prefix words (`vm_local_guard_dec`: the fast path stops right
  after `AFFINITY`, `vm_here_guard`).

No premise: every fact about the state is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.VmOnce
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts
open Fl4Proofs.P2.OwnMap (KLayout fld own GateField TimerField GField RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} {ar : machine.Arch A}

/-- **What the declining fast path reads up to the handler's `AFFINITY`, in `Rd`** (module docstring); `s` the
entry, `s1` the state after its `update_timestamp`. -/
structure VmFhR (st : machine.Store S) [L : LawfulStore st] (Rd : U64 → Prop) (s s1 : S) : Prop where
  k : L.ksb s1 = L.ksb s
  c : L.cpu s1 = L.cpu s
  nd : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → Rd (L.nodeAt s1 (L.cpu s1) o)
  dt : Rd (core.num.U64.wrapping_add (L.ksb s1) layout.ks.DOMAIN_TIME)
  cd : Rd (core.num.U64.wrapping_add (L.ksb s1) layout.ks.CUR_DOMAIN)
  cur : L.curW s1 = L.curW s
  sl : ∀ sl, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
    Rd sl ∧ Rd (core.num.U64.wrapping_add sl 8#u64)
  ep : ∀ sl ptr badge x y g gr, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
    obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x y g gr) →
    Rd (epTSA ptr) ∧ Rd (epHeadA ptr)
  td : L.mem s1 (tmA (L := L) s1) ≠ 0#u64 →
    Rd (core.num.U64.wrapping_add (L.mem s1 (tmA (L := L) s1)) 3528#u64)
  rs : L.mem s1 (rhA (L := L) s1) ≠ 0#u64 → Rd (scA (L.mem s1 (rhA (L := L) s1))) ∧
    RdHead (L := L) Rd s1 (L.mem s1 (scA (L.mem s1 (rhA (L := L) s1))))
  suf : RdHead (L := L) Rd s1 (L.cscW s1)

/-- **`VmFhR` at the prefix state of a state agreeing on `Rd`** (`VmDF.alt`). -/
theorem VmFhR.alt {Rd R'' : U64 → Prop} {s s1 x1 : S} (D : VmFhR st Rd s s1) (G1 : Ag st Rd s1 x1)
    (hRR : ∀ b, Rd b → R'' b) :
    (∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R'' (L.nodeAt x1 (L.cpu x1) o)) ∧
    R'' (core.num.U64.wrapping_add (L.ksb x1) layout.ks.DOMAIN_TIME) ∧
    R'' (core.num.U64.wrapping_add (L.ksb x1) layout.ks.CUR_DOMAIN) ∧
    RdBitmap (L := L) R'' x1 ∧
    (L.mem x1 (tmA (L := L) x1) ≠ 0#u64 → R'' (core.num.U64.wrapping_add (L.mem x1 (tmA (L := L) x1)) 3528#u64)) ∧
    (L.mem x1 (rhA (L := L) x1) ≠ 0#u64 → R'' (scA (L.mem x1 (rhA (L := L) x1))) ∧
      RdHead (L := L) R'' x1 (L.mem x1 (scA (L.mem x1 (rhA (L := L) x1))))) := by
  have nd1 : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 → R'' (L.nodeAt x1 (L.cpu x1) o) := fun o ho h8 => by
    rw [G1.node]; exact hRR _ (D.nd o ho h8)
  have etm : L.mem x1 (tmA (L := L) x1) = L.mem s1 (tmA (L := L) s1) := by
    show L.mem x1 (L.nodeAt x1 (L.cpu x1) layout.node.TIMER_MIN) = L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.TIMER_MIN)
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN]))
  have erh : L.mem x1 (rhA (L := L) x1) = L.mem s1 (rhA (L := L) s1) := by
    show L.mem x1 (L.nodeAt x1 (L.cpu x1) layout.node.RELEASE_HEAD) =
      L.mem s1 (L.nodeAt s1 (L.cpu s1) layout.node.RELEASE_HEAD)
    rw [G1.node]; exact G1.m _ (D.nd _ (by simp [layout.node.RELEASE_HEAD]) (by simp [layout.node.RELEASE_HEAD]))
  refine ⟨nd1, ?_, ?_, ⟨nd1 l1Off (by rw [l1Off_val]; omega) (by rw [l1Off_val]),
    fun inv hinv => nd1 _ (by simp only [w64_val]; omega) (by simp only [w64_val]; omega)⟩, ?_, ?_⟩
  · rw [G1.k]; exact hRR _ D.dt
  · rw [G1.k]; exact hRR _ D.cd
  · intro h0
    rw [etm] at h0 ⊢
    exact hRR _ (D.td h0)
  · intro h0
    rw [erh] at h0 ⊢
    obtain ⟨h1, h2⟩ := D.rs h0
    rw [G1.m _ h1]
    have h3 := G1.rdHead h2
    refine ⟨hRR _ h1, ?_⟩
    unfold RdHead at h3 ⊢
    exact ⟨hRR _ h3.1, hRR _ h3.2.1, hRR _ h3.2.2⟩

/-- The current thread at the prefix state of a state agreeing on `Rd`. -/
theorem VmFhR.cur_alt {Rd : U64 → Prop} {s s1 x1 : S} (D : VmFhR st Rd s s1) (G1 : Ag st Rd s1 x1) :
    L.curW x1 = L.curW s := by
  have e : L.curW x1 = L.curW s1 := by
    unfold LawfulStore.curW; rw [G1.node]
    exact G1.m _ (D.nd _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]))
  rw [e]; exact D.cur

/-- **The fault handler off the core**, at `x`'s prefix state, for the endpoint the entry's prefix state finds. -/
def VmFhOff (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (s s1 x : S) (a : A) : Prop :=
  ∀ x1 a1', sched.update_timestamp st ar x a = ok (x1, a1') →
    ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) → L.epState s1 ptr = obj.EP_RECV →
      L.mem x1 (affA (L.mem s1 (epHeadA ptr))) ≠ L.cpu x1

set_option maxHeartbeats 1000000 in
/-- **A state whose prefix state sees the handler off its core is not accepted** (module docstring). -/
theorem vm_fh_not_acc {Rd : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) {s x : S} (G : Ag st Rd s x)
    (rT : Rd (ctA (L := L) s)) (rN : Rd (cnA (L := L) s)) {a : A} {s1 : S} {a1 : A}
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (F : VmFhR st Rd s s1) (hFH : VmFhOff st ar s s1 x a)
    {addr code : U64} {z : S} {b : A}
    (h' : syscall.handle_vm_fault_local st ar x a addr code = ok (true, z, b)) : False := by
  unfold syscall.handle_vm_fault_local at h'
  rw [if_neg vm_nd_ne] at h'
  obtain ⟨⟨x1, a1'⟩, eu', h'⟩ := bind_eq_ok h'
  simp only [uncurry_apply_pair] at h'
  obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
  obtain ⟨csc', -, h'⟩ := bind_eq_ok h'
  obtain ⟨u', -, h'⟩ := bind_eq_ok h'
  obtain ⟨bb', -, h'⟩ := bind_eq_ok h'
  by_cases hb : bb' = true
  swap
  · rw [if_neg hb] at h'; exact Bool.false_ne_true (congrArg Prod.fst (ok_inj_ff h'))
  rw [if_pos hb] at h'
  rw [cur_thread_ok] at h'
  simp only [bind_ok] at h'
  rw [F.cur_alt G1] at h'
  obtain ⟨j1, -, h'⟩ := bind_eq_ok h'
  obtain ⟨j2, -, h'⟩ := bind_eq_ok h'
  obtain ⟨f, -, h'⟩ := bind_eq_ok h'
  obtain ⟨ptr, badge, dest, rr, C', -⟩ := vm_fault_acc st ar h'
  obtain ⟨-, ⟨sl, x', y, g, gr, hS, hcap, -⟩, hep, hh, -, -, hhe, -⟩ := C'
  obtain ⟨r0, r8⟩ := F.sl sl hS
  rw [cap_congr_ag G1 r0 r8] at hcap
  obtain ⟨rts, rhd⟩ := F.ep sl ptr badge x' y g gr hS hcap
  have eep : obj.Ep.state st ptr x1 = obj.Ep.state st ptr s1 := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) x1 ptr), eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)]
    unfold LawfulStore.epState
    rw [G1.m (epTSA ptr) rts]
  rw [eep] at hep
  have hst : L.epState s1 ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) s1 ptr)] at hep; exact ok_inj_ff hep
  have ehd : obj.Ep.head st ptr x1 = obj.Ep.head st ptr s1 := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr), eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)]
    exact congrArg ok (G1.m (epHeadA ptr) rhd)
  rw [ehd] at hh
  have hdd : dest = L.mem s1 (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) s1 ptr)] at hh; exact (ok_inj_ff hh).symm
  have HF := here_facts (L := L) hhe
  rw [hdd] at HF
  exact hFH x1 a1' eu' sl ptr badge x' y g gr hS hcap hst HF.aff

/-- **The run at such a state declines and runs the same on the guarded store** (module docstring). -/
theorem vm_fh_guard {Rd R'' W : U64 → Prop} (hRal : ∀ b, Rd b → Aligned b) {s x : S} (G : Ag st Rd s x)
    (rT : Rd (ctA (L := L) s)) (rN : Rd (cnA (L := L) s)) {a : A} {s1 : S} {a1 : A}
    (eu : sched.update_timestamp st ar s a = ok (s1, a1)) (F : VmFhR st Rd s s1) (hFH : VmFhOff st ar s s1 x a)
    (hRR : ∀ b, Rd b → R'' b)
    (hD : ∀ sl ptr badge x' y g gr, obj.Tcb.slot (L.curW s) layout.tcb.SLOT_FAULT_HANDLER = ok sl →
      obj.Slot.cap st sl s1 = ok (capability.Cap.Endpoint ptr badge x' y g gr) → L.epState s1 ptr = obj.EP_RECV →
      R'' (replyA (L.mem s1 (epHeadA ptr))) ∧ R'' (affA (L.mem s1 (epHeadA ptr))))
    (hWT : W (ctA (L := L) x)) (hWN : W (cnA (L := L) x))
    {addr code : U64} {r : Bool × S × A} (h : syscall.handle_vm_fault_local st ar x a addr code = ok r) :
    r.1 ≠ true ∧ syscall.handle_vm_fault_local (PathObl.guard st R'' W) ar x a addr code = ok r := by
  have hn : r.1 ≠ true := by
    obtain ⟨b0, z, c0⟩ := r
    intro hb
    change b0 = true at hb
    subst hb
    exact vm_fh_not_acc hRal G rT rN eu F hFH h
  refine ⟨hn, ?_⟩
  have hct : R'' (ctA (L := L) x) := by
    show R'' (L.nodeAt x (L.cpu x) layout.node.CUR_TIME); rw [G.node]; exact hRR _ rT
  have hcn : R'' (cnA (L := L) x) := by
    show R'' (L.nodeAt x (L.cpu x) layout.node.CONSUMED); rw [G.node]; exact hRR _ rN
  refine vm_local_guard_dec (gS := PathObl.guard st R'' W) hct hWT hcn hWN ?_ h hn
  intro x1 a1' eu'
  obtain ⟨-, G1⟩ := vm_ag_upd hRal G rT rN eu eu'
  obtain ⟨nd1, dt1, cd1, bm1, tm1, rh1⟩ := F.alt G1 hRR
  have ecur1 := F.cur_alt G1
  have ecsc : L.cscW x1 = L.cscW s1 := by
    unfold LawfulStore.cscW LawfulStore.nodeA
    rw [G1.node]; exact G1.m _ (F.nd _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]))
  have hs := G1.rdHead F.suf
  rw [← ecsc] at hs
  refine ⟨nd1 _ (by simp [layout.node.CUR_SC]) (by simp [layout.node.CUR_SC]),
    nd1 _ (by simp [layout.node.CONSUMED]) (by simp [layout.node.CONSUMED]),
    nd1 _ (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD]), ?_, ?_⟩
  · unfold RdHead at hs ⊢
    exact ⟨hRR _ hs.1, hRR _ hs.2.1, hRR _ hs.2.2⟩
  rw [ecur1]
  refine ⟨nd1, dt1, cd1, bm1, tm1, rh1, fun sl hsl => ⟨hRR _ (F.sl sl hsl).1, hRR _ (F.sl sl hsl).2⟩, ?_⟩
  intro sl ptr b x' y g gr hsl hcap
  obtain ⟨r0, r8⟩ := F.sl sl hsl
  rw [cap_congr_ag G1 r0 r8] at hcap
  obtain ⟨rts, rhd⟩ := F.ep sl ptr b x' y g gr hsl hcap
  refine ⟨hRR _ rts, hRR _ rhd, fun hst d hd => ?_⟩
  have hst1 : L.epState s1 ptr = obj.EP_RECV := by
    rw [eq_of_spec_fd (obj.Ep.state.spec (L := L) x1 ptr)] at hst
    rw [← ok_inj_ff hst]
    unfold LawfulStore.epState
    rw [G1.m (epTSA ptr) rts]
  have hdd : d = L.mem s1 (epHeadA ptr) := by
    rw [eq_of_spec_fd (obj.Ep.head.spec' (L := L) x1 ptr)] at hd
    rw [← ok_inj_ff hd]; exact G1.m (epHeadA ptr) rhd
  obtain ⟨hrp, haf⟩ := hD sl ptr b x' y g gr hsl hcap hst1
  rw [← hdd] at hrp haf
  have hoff := hFH x1 a1' eu' sl ptr b x' y g gr hsl hcap hst1
  rw [← hdd] at hoff
  exact ⟨hrp, haf, fun hl => absurd hl hoff⟩

end

end Fl4Proofs.P2.PathObl
