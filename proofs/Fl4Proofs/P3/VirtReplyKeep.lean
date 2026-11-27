/-
P3x for virtualization (line virt, gen 16, item 1–2a): **WriteMSR's reply premise narrowed, then discharged.**

Reviewer's finding on gen 15: `wrmsrTail_vmx/svm` (P3/VirtMsrStore) take
`hK : ∀ x : U64, x.bv.toNat % 8 = 0 → ReplyKeepsV st s1 x value call v`, i.e. `ReplyKeepsV` for **every** aligned
address `x`. Read literally this is false on reachable states: extracted `vcpu.reply` (Funs.lean `vcpu.reply`)
starts with `sched.cur_thread`, which reads the current core's node word `CUR_THREAD` (`curA st s`); take `x :=
curA st s1` and the user's MSR value `value := v` (any value with `v ≤ value + 3328 < v + 0x8000`): after
`L.wr s1 x value` the "current thread" is `value`, and `set_thread_state` writes `value + 3328` — a word of the VCPU
object at `v` — to `TS_RUNNING` (with `call` also `value + 256 + 8 r` for MR0 / BADGE / MSG_INFO). So the quantified
premise fails whenever that VCPU word is not already `TS_RUNNING`. The old statements are left unchanged; the
premise is replaced here.

A second gap: `ReplyKeepsV` asks `AgreeAt` (every offset `< 0x8000`, unaligned ones included) on `memW`. A
`LawfulStore` says nothing about an unaligned word after a write (`mem_wr` is for aligned addresses only), so
`ReplyKeepsV` cannot be derived from any footprint, however small. The relations only read aligned words, so the
derived route uses the aligned agreement `AgreeAtA`.

* **`ReplyKeepsVN st s1 v f value call amd`** [J] (the narrowed form): `ReplyKeepsV st s1 x value call v` only for
  the address WriteMSR writes, `x.bv = v.bv + o` with `msrOff amd f.bv = some o`. **`wrmsrTail_vmxN` /
  `wrmsrTail_svmN`**: gen 15's tails with `hK` narrowed to it (same conclusion).
* `AgreeAtA` (aligned words of the object), `VcpuRelVmx.congrA`, `VcpuRelSvm.congrA`, `ReplyKeepsA` (`ReplyKeepsV`
  with `AgreeAtA`), **`wrmsrTail_genA`** (the tail over `ReplyKeepsA` at WriteMSR's address only).
* `vcpu.reply`'s footprint, **`reply_w`**: it writes only words `ct + K` (`K < 4096`, `ct` the current thread: MR0
  = R10, BADGE, MSG_INFO registers, the state word) and the current core's `SCHED_ACTION` word (`set_mr_0`,
  `set_msg_info_w`, mmuAD's `sts_w`).
* **`ReplyPl st v s`**: the placement facts that keep WriteMSR's word and the reply's footprint apart (all state
  facts, no premise): `VFits v`, the kernel-global block aligned / fitting, the core index `< 64`, the VCPU off
  `[ksb, ksb + 304384)` (`JVm.ks`), the current thread a `TcbAddr`, off the node and off the VCPU (`JVLay.vap`).
  **`JAtZ.replyPl`**: derived from P3's `JAtZ` + `JVm` (`JVLay` via `JAtZ.jvLay`, `JKern`). `ReplyPl.wr` /
  `ReplyPl.stall`: kept by WriteMSR's own store and by the stall's `IPI_PENDING` write.
* **`replyKeepsA_of`**: `ReplyPl st v s1` ⇒ `ReplyKeepsA st s1 x value call v` for every `x` inside the object at
  an aligned offset (so for WriteMSR's address). **`wrmsrTail_vmxP` / `wrmsrTail_svmP`**: WriteMSR's tail with
  **no reply premise** (only `CapAgree` [P] and the state fact `ReplyPl`).

Named premises: `CapAgree ar a` [P] (gen 11, unchanged); **`ReplyKeepsVN`** [J] (new, only in the `…N` variants;
true on real stores: `reply` writes only the current thread's TCB words and `SCHED_ACTION`, `replyKeepsA_of`, and
an unaligned word of a real memory is made of aligned ones). The `…P` variants have no [J]. New file only; no
existing statement changed.
-/
import Fl4Proofs.P3.VirtMsrStore
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3.VirtReplyKeep
open fl4_core Fl4Spec Fl4Proofs.P3 Fl4Proofs.P3.VirtSanEq Fl4Proofs.P3.VirtSanRel Fl4Proofs.P3.VirtVcpuRel
open Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtMsrDec Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit
open Fl4Proofs.P3.VirtMsrStore

noncomputable section

/-! ## The narrowed premise -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **`ReplyKeepsVN` [J]** (module docstring): gen 15's `ReplyKeepsV` only at the address WriteMSR writes. -/
def ReplyKeepsVN (st : machine.Store S) [L : P1.LawfulStore st] (s1 : S) (v f value : U64) (call amd : Bool) :
    Prop :=
  ∀ o, msrOff amd f.bv = some o → ∀ x : U64, x.bv = v.bv + o → ReplyKeepsV st s1 x value call v

/-- The tail with an arbitrary agreement notion `Ag` and reply-keeping `RK` at WriteMSR's address only. -/
theorem wrmsrTail_genAg {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (hv : VFits v) (f value : U64)
    (amd call : Bool) (R : (Word → Word) → Word → VcpuState → Prop) (k : VirtKind) (vs : VcpuState)
    (Ag : (Word → Word) → (Word → Word) → Word → Prop)
    (hR : ∀ o, msrOff amd f.bv = some o → ∀ mem', WrAt (memW st s1) mem' v.bv o value.bv →
      R mem' v.bv (vs.set k (.msr f.bv) value.bv))
    (hRc : ∀ mem mem', Ag mem mem' v.bv → R mem v.bv (vs.set k (.msr f.bv) value.bv) →
      R mem' v.bv (vs.set k (.msr f.bv) value.bv))
    (hK : ∀ o, msrOff amd f.bv = some o → ∀ x : U64, x.bv = v.bv + o →
      vcpu.reply st (L.wr s1 x value) call value ⦃ s' => Ag (memW st (L.wr s1 x value)) (memW st s') v.bv ⦄) :
    wrmsrTail st ar s1 a1 v f value amd call ⦃ r => TailPost R k st s1 v f value vs r ⦄ := by
  obtain ⟨r, hr, hrel, haddr⟩ := fl4WriteMsr_rel hc v f value amd
  unfold wrmsrTail
  rw [hr, bind_ok]
  cases r with
  | Ok x =>
    rcases hcm : checkMsrWrite f.bv value.bv with e' | u
    · rw [hcm] at hrel; exact hrel.elim
    cases u
    obtain ⟨o, ho, hox⟩ := Option.map_eq_some_iff.1 (haddr x rfl)
    obtain ⟨-, h1, h2, -⟩ := msrOff_cases ho
    have hw := memW_wr (st := st) hv h1 h2 hox.symm s1 value
    have hxa : P1.Aligned x := by
      have e : x = ⟨v.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hox.symm
      unfold P1.Aligned; rw [e, vo_val hv h1]; have := hv.1; omega
    dsimp only
    rw [L.write_eq, bind_ok, L.read_eq, bind_ok, L.mem_wr _ _ _ _ hxa hxa, if_pos rfl]
    refine WP.spec_bind (hK o ho x hox.symm) fun s3 hag => (WP.spec_ok _).2 (Or.inl ⟨hcm, rfl, ?_⟩)
    exact hRc _ _ hag (hR o ho _ hw)
  | Err e =>
    rcases hcm : checkMsrWrite f.bv value.bv with e' | u
    · rw [hcm] at hrel
      exact (WP.spec_ok _).2 (Or.inr ⟨e, e', hcm, hrel, rfl, rfl⟩)
    · rw [hcm] at hrel; exact hrel.elim

/-- **WriteMSR's tail on VMX, narrowed premise** (premises `CapAgree` [P], `ReplyKeepsVN` [J]). -/
theorem wrmsrTail_vmxN {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (hv : VFits v) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelVmx (memW st s1) v.bv vs)
    (hK : ReplyKeepsVN st s1 v f value call false) :
    wrmsrTail st ar s1 a1 v f value false call ⦃ r => TailPost VcpuRelVmx .vmx st s1 v f value vs r ⦄ :=
  wrmsrTail_genAg hc hv f value false call VcpuRelVmx .vmx vs AgreeAt (fun _ ho _ hw => msrStore_vmx h ho hw)
    (fun _ _ hag h' => VcpuRelVmx.congr hag h') hK

/-- **WriteMSR's tail on SVM, narrowed premise** (premises `CapAgree` [P], `ReplyKeepsVN` [J]). -/
theorem wrmsrTail_svmN {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (hv : VFits v) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelSvm (memW st s1) v.bv vs)
    (hK : ReplyKeepsVN st s1 v f value call true) :
    wrmsrTail st ar s1 a1 v f value true call ⦃ r => TailPost VcpuRelSvm .svm st s1 v f value vs r ⦄ :=
  wrmsrTail_genAg hc hv f value true call VcpuRelSvm .svm vs AgreeAt (fun _ ho _ hw => msrStore_svm h ho hw)
    (fun _ _ hag h' => VcpuRelSvm.congr hag h') hK

end

/-! ## Aligned agreement -/

/-- Agreement on the aligned words of the VCPU object at `v`. -/
def AgreeAtA (mem mem' : Word → Word) (v : Word) : Prop :=
  ∀ o, o < VcpuLay.SIZE → o.toNat % 8 = 0 → mem' (v + o) = mem (v + o)

theorem agA {mem mem' : Word → Word} {v o : Word} (hm : AgreeAtA mem mem' v) (h1 : o < VcpuLay.SIZE)
    (h2 : o.toNat % 8 = 0) : mem' (v + o) = mem (v + o) := hm o h1 h2

theorem AgreeAtA.trans {m1 m2 m3 : Word → Word} {v : Word} (h1 : AgreeAtA m1 m2 v) (h2 : AgreeAtA m2 m3 v) :
    AgreeAtA m1 m3 v := fun o a b => (h2 o a b).trans (h1 o a b)

theorem VcpuRelCommon.congrA {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtA mem mem' v)
    (h : VcpuRelCommon mem v vs) : VcpuRelCommon mem' v vs where
  tcb := by rw [agA hm tcb_lt (by decide)]; exact h.tcb
  valid := by rw [agA hm valid_lt (by decide)]; exact h.valid
  pending := by rw [agA hm pending_lt (by decide)]; exact h.pending
  mrs i := by
    have := exitOff_nat i
    rw [agA hm (exitOff_lt i) (by omega)]; exact h.mrs i
  gpr i := by
    have := gprOff_nat i
    rw [agA hm (gprOff_lt i) (by omega)]; exact h.gpr i
  xcr0 := by rw [agA hm xcr0_lt (by decide)]; exact h.xcr0
  ibpb := by rw [agA hm ibpb_lt (by decide)]; exact h.ibpb

/-- **Aligned frame for VMX**: the relation reads aligned words only. -/
theorem VcpuRelVmx.congrA {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtA mem mem' v)
    (h : VcpuRelVmx mem v vs) : VcpuRelVmx mem' v vs :=
  { VcpuRelCommon.congrA hm h.toVcpuRelCommon with
    vmcs := fun f hf => by
      rw [agA hm (vmcsOff_lt hf) (vmcsOff_nat f).2]; exact h.vmcs f hf
    msr := fun m i hi => by
      rw [agA hm (msrOff_lt hi) (msrOff_cases (msrOff_of_slot hi)).2.2.1]; exact h.msr m i hi
    cr2 := by rw [agA hm cr2_lt (by decide)]; exact h.cr2
    io := fun p => by rw [agA hm (ioOff_lt p) (ioOff_nat p).2.2]; exact h.io p }

/-- **Aligned frame for SVM**. -/
theorem VcpuRelSvm.congrA {mem mem' : Word → Word} {v : Word} {vs : VcpuState} (hm : AgreeAtA mem mem' v)
    (h : VcpuRelSvm mem v vs) : VcpuRelSvm mem' v vs :=
  { VcpuRelCommon.congrA hm h.toVcpuRelCommon with
    vmcb := fun off hr hh hx => by
      rw [agA hm (svmOff_lt hr) (readable_nat hr).1]; exact h.vmcb off hr hh hx }

theorem VRelInit.congrA {mem mem' : Word → Word} {v : Word} (hm : AgreeAtA mem mem' v) (h : VRelInit mem v) :
    VRelInit mem' v :=
  ⟨fun e => VcpuRelSvm.congrA hm (h.1 e), fun e => VcpuRelVmx.congrA hm (h.2 e)⟩

/-! ## `vcpu.reply`'s footprint -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- `ReplyKeepsV` with the aligned agreement. -/
def ReplyKeepsA (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (x value : U64) (call : Bool) (v : U64) :
    Prop :=
  vcpu.reply st (L.wr s x value) call value ⦃ s' =>
    AgreeAtA (memW st (L.wr s x value)) (memW st s') v.bv ⦄

/-- A word of the TCB at `t` (offset `< 4096`). -/
def TW (t b : U64) : Prop := ∃ K : U64, K.val < 4096 ∧ b = core.num.U64.wrapping_add t K

/-- The reply's footprint: the current thread's TCB words and the current core's `SCHED_ACTION` word. -/
def RW (t : U64) (aw : U64) (b : U64) : Prop := TW t b ∨ b = aw

theorem set_reg_tw (s : S) {t r v : U64} (ht : P1.TcbAddr t) (hr : r.val < 384) :
    obj.Tcb.set_reg st t s r v ⦃ s' => P1.WritesIn st s s' (TW t) ⦄ :=
  WP.spec_mono (P1.obj.Tcb.set_reg.wrS s t r v ht hr) fun s' ⟨K, hK, e⟩ => by
    subst e
    exact (P1.writesIn_wr (P1.field_aligned ht (by omega) (by omega))).mono fun b e => ⟨K, by omega, e⟩

theorem set_mr_0 (s : S) {t buf v : U64} (ht : P1.TcbAddr t) :
    msg.set_mr st s t buf 0#u64 v ⦃ r => P1.WritesIn st s r.2 (TW t) ⦄ := by
  unfold msg.set_mr
  split
  · refine WP.spec_bind (P1.msg.msg_register.lt _) fun r hr => ?_
    refine WP.spec_bind (set_reg_tw s ht hr) fun s1 hs1 => ?_
    simp only [lift, bind_ok]
    exact (WP.spec_ok _).2 hs1
  · rename_i hn
    exfalso; apply hn
    simp [msg.N_MSG_REGISTERS]

theorem set_msg_info_w (s : S) {t : U64} (ht : P1.TcbAddr t) (m : msginfo.MessageInfo) :
    msg.set_msg_info st s t m ⦃ s' => P1.WritesIn st s s' (TW t) ⦄ := by
  unfold msg.set_msg_info
  refine WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 m) fun i _ => ?_
  exact set_reg_tw s ht (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

/-- **`vcpu.reply`'s footprint** (module docstring). -/
theorem reply_w (s : S) (call : Bool) (value : U64) (hta : P1.TcbAddr (L.mem s (curA st s)))
    (haa : P1.Aligned (actA st s)) (hne : actA st s ≠ P1.stA (L.mem s (curA st s))) :
    vcpu.reply st s call value ⦃ s' => P1.WritesIn st s s' (RW (L.mem s (curA st s)) (actA st s)) ⦄ := by
  unfold vcpu.reply
  refine WP.spec_bind (P1.sched.cur_thread.spec s) fun ct hct => ?_
  have hct' : ct = L.mem s (curA st s) := hct
  subst hct'
  have hsa : P1.Aligned (P1.stA (L.mem s (curA st s))) := by
    rw [P1.stA_eq]; exact P1.field_aligned hta (by simp) (by simp)
  have hst : TW (L.mem s (curA st s)) (P1.stA (L.mem s (curA st s))) := ⟨3328#u64, by simp, P1.stA_eq _⟩
  refine WP.spec_bind (Pₘ := fun s1 => P1.WritesIn st s s1 (TW (L.mem s (curA st s)))) ?_ fun s1 h1 => ?_
  · split
    · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s true _ L.total) fun b _ => ?_
      refine WP.spec_bind (set_mr_0 s hta) fun r hr => ?_
      obtain ⟨_, s2⟩ := r
      simp only at hr ⊢
      refine WP.spec_bind (set_reg_tw s2 hta (by simp [layout.reg.BADGE, layout.reg.RDI])) fun s3 h3 => ?_
      refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun mi _ => ?_
      exact WP.spec_mono (set_msg_info_w s3 hta mi) fun s4 h4 =>
        ((hr.trans h3).trans h4).mono fun b hb => hb.elim (fun h => h.elim id id) id
    · exact (WP.spec_ok _).2 (P1.WritesIn.refl _ _)
  · refine WP.spec_mono (sts_w s1 _ sched.TS_RUNNING hsa (by rw [actA_of h1]; exact haa)
      (by rw [actA_of h1]; exact hne)) fun s' hw => ?_
    have w := hw.1
    rw [actA_of h1] at w
    exact (h1.trans w).mono fun b hb => hb.elim (fun h => Or.inl h)
      fun h => h.elim (fun e => Or.inl (e ▸ hst)) Or.inr

end

/-! ## The placement facts -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {ar : machine.Arch A}

/-- **The placement WriteMSR's store and reply need** (module docstring; state facts, not premises). -/
structure ReplyPl (st : machine.Store S) [L : P1.LawfulStore st] (v : U64) (s : S) : Prop where
  fit : VFits v
  ksA : (L.ksb s).val % 8 = 0
  nF : (L.ksb s).val + 13568 + ((L.cpu s).val + 1) * 4288 ≤ 2 ^ 64
  cpu : (L.cpu s).val < 64
  ks : v.val + 32768 ≤ (L.ksb s).val ∨ (L.ksb s).val + 304384 ≤ v.val
  ctA : P1.TcbAddr (L.mem s (curA st s))
  ctN : (L.mem s (curA st s)).val + 4096 ≤ L.nodeBase s (L.cpu s) ∨
    L.nodeBase s (L.cpu s) + 4288 ≤ (L.mem s (curA st s)).val
  ctV : (L.mem s (curA st s)).val + 4096 ≤ v.val ∨ v.val + 32768 ≤ (L.mem s (curA st s)).val

theorem ReplyPl.nodePl {v : U64} {s : S} (P : ReplyPl st v s) : P1.NodePlaced st ∅ s (L.cpu s) where
  align := by unfold P1.LawfulStore.nodeBase; have := P.ksA; omega
  fits := by unfold P1.LawfulStore.nodeBase; have := P.nF; omega
  disj t ht := ht.elim

/-- A word of the current core's node: its value and its distance from the VCPU. -/
theorem ReplyPl.node {v : U64} {s : S} (P : ReplyPl st v s) {off : U64} (ho : off.val < 4288) :
    (L.nodeAt s (L.cpu s) off).val = L.nodeBase s (L.cpu s) + off.val ∧
      ((L.nodeAt s (L.cpu s) off).val + 8 ≤ v.val ∨ v.val + 32768 ≤ (L.nodeAt s (L.cpu s) off).val) := by
  have e := P1.nodeAt_val P.nodePl ho
  refine ⟨e, ?_⟩
  rw [e]; unfold P1.LawfulStore.nodeBase
  have := P.ks; have := P.cpu
  have : (L.cpu s).val * 4288 ≤ 63 * 4288 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem ReplyPl.actA_al {v : U64} {s : S} (P : ReplyPl st v s) : P1.Aligned (actA st s) :=
  P1.nodeAt_aligned P.nodePl (by simp [layout.node.SCHED_ACTION]) (by simp [layout.node.SCHED_ACTION])

theorem ReplyPl.curA_al {v : U64} {s : S} (P : ReplyPl st v s) : P1.Aligned (curA st s) :=
  P1.nodeAt_aligned P.nodePl (by simp [layout.node.CUR_THREAD]) (by simp [layout.node.CUR_THREAD])

theorem ReplyPl.ipiA_al {v : U64} {s : S} (P : ReplyPl st v s) : P1.Aligned (ipiA st s) :=
  P1.nodeAt_aligned P.nodePl (by simp [layout.node.IPI_PENDING]) (by simp [layout.node.IPI_PENDING])

theorem ReplyPl.act_ne_st {v : U64} {s : S} (P : ReplyPl st v s) :
    actA st s ≠ P1.stA (L.mem s (curA st s)) := by
  intro e
  have h1 := (P.node (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])).1
  have h2 := lay_stA_val P.ctA
  have h3 := P.ctN
  have hv : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
  unfold actA at e
  rw [e] at h1
  omega

/-- A word inside the VCPU object (aligned offset `o`) is none of the node words. -/
theorem ReplyPl.vo_ne_node {v : U64} {s : S} (P : ReplyPl st v s) {o : Word} (ho : o.toNat < 32768)
    {off : U64} (hoff : off.val < 4288) : (⟨v.bv + o⟩ : U64) ≠ L.nodeAt s (L.cpu s) off := by
  intro e
  have h1 := vo_val P.fit ho
  have h2 := (P.node hoff).2
  rw [e] at h1
  omega

/-- **Kept by a write inside the VCPU object** (WriteMSR's store). -/
theorem ReplyPl.wr {v : U64} {s : S} (P : ReplyPl st v s) {o : Word} (ho : o.toNat < 32768) (h8 : o.toNat % 8 = 0)
    (x : U64) (hx : x.bv = v.bv + o) (y : U64) : ReplyPl st v (L.wr s x y) := by
  have ex : x = ⟨v.bv + o⟩ := by rcases x with ⟨b⟩; exact congrArg (fun b => (⟨b⟩ : U64)) hx
  have hxa : P1.Aligned x := by unfold P1.Aligned; rw [ex, vo_val P.fit ho]; have := P.fit.1; omega
  have ec : curA st (L.wr s x y) = curA st s := by
    unfold curA; rw [L.cpu_wr, P1.nodeAt_of_ksb (L.ksb_wr s x y)]
  have ne : x ≠ curA st s := by rw [ex]; exact P.vo_ne_node ho (by simp [layout.node.CUR_THREAD])
  have em : L.mem (L.wr s x y) (curA st (L.wr s x y)) = L.mem s (curA st s) := by
    rw [ec, L.mem_wr _ _ _ _ hxa P.curA_al, if_neg ne]
  have eb : L.nodeBase (L.wr s x y) (L.cpu s) = L.nodeBase s (L.cpu s) := by
    simp [P1.LawfulStore.nodeBase]
  refine ⟨P.fit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [L.ksb_wr, L.cpu_wr, em, eb]
  exacts [P.ksA, P.nF, P.cpu, P.ks, P.ctA, P.ctN, P.ctV]

/-- **Kept by a footprint missing the current-thread word** (e.g. the stall's `IPI_PENDING` write). -/
theorem ReplyPl.of_writes {v : U64} {s s' : S} (P : ReplyPl st v s) {W : U64 → Prop} (h : P1.WritesIn st s s' W)
    (hc : ¬ W (curA st s)) : ReplyPl st v s' := by
  have ec : curA st s' = curA st s := curA_of h
  have em : L.mem s' (curA st s') = L.mem s (curA st s) := by rw [ec, h.2.2 _ P.curA_al hc]
  have eb : L.nodeBase s' (L.cpu s) = L.nodeBase s (L.cpu s) := by
    simp [P1.LawfulStore.nodeBase, h.1]
  refine ⟨P.fit, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [h.1, h.2.1, em, eb]
  exacts [P.ksA, P.nF, P.cpu, P.ks, P.ctA, P.ctN, P.ctV]

theorem ReplyPl.ipi_ne_cur {v : U64} {s : S} (P : ReplyPl st v s) : ipiA st s ≠ curA st s := by
  intro e
  have h1 := (P.node (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])).1
  have h2 := (P.node (off := layout.node.CUR_THREAD) (by simp [layout.node.CUR_THREAD])).1
  unfold ipiA curA at e
  rw [e, h2] at h1
  simp [layout.node.IPI_PENDING, layout.node.CUR_THREAD] at h1

/-- **The reply keeps the VCPU's aligned words** from a `ReplyPl` state (no premise). -/
theorem reply_keepsA {v : U64} {s : S} (P : ReplyPl st v s) (call : Bool) (value : U64) :
    vcpu.reply st s call value ⦃ s' => AgreeAtA (memW st s) (memW st s') v.bv ⦄ := by
  refine WP.spec_mono (reply_w s call value P.ctA P.actA_al P.act_ne_st) fun s' h => ?_
  intro o h1 h2
  have ho : o.toNat < 32768 := by
    have : VcpuLay.SIZE.toNat = 32768 := rfl
    rw [BitVec.lt_def, this] at h1; exact h1
  have hval := vo_val P.fit ho
  have hal : P1.Aligned (⟨v.bv + o⟩ : U64) := by unfold P1.Aligned; rw [hval]; have := P.fit.1; omega
  unfold memW
  congr 1
  refine h.2.2 _ hal ?_
  rintro (⟨K, hK, e⟩ | e)
  · have := lay_tw_val P.ctA hK
    rw [← e, hval] at this
    have := P.ctV
    omega
  · exact P.vo_ne_node ho (by simp [layout.node.SCHED_ACTION]) e

/-- **`ReplyKeepsA` discharged** at every aligned address inside the VCPU object (so at WriteMSR's). -/
theorem replyKeepsA_of {v : U64} {s1 : S} (P : ReplyPl st v s1) {o : Word} (ho : o.toNat < 32768)
    (h8 : o.toNat % 8 = 0) (x : U64) (hx : x.bv = v.bv + o) (value : U64) (call : Bool) :
    ReplyKeepsA st s1 x value call v :=
  reply_keepsA (P.wr ho h8 x hx value) call value

/-- **WriteMSR's tail, aligned agreement, general relation.** -/
theorem wrmsrTail_genA {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (P : ReplyPl st v s1) (f value : U64)
    (amd call : Bool) (R : (Word → Word) → Word → VcpuState → Prop) (k : VirtKind) (vs : VcpuState)
    (hR : ∀ o, msrOff amd f.bv = some o → ∀ mem', WrAt (memW st s1) mem' v.bv o value.bv →
      R mem' v.bv (vs.set k (.msr f.bv) value.bv))
    (hRc : ∀ mem mem', AgreeAtA mem mem' v.bv → R mem v.bv (vs.set k (.msr f.bv) value.bv) →
      R mem' v.bv (vs.set k (.msr f.bv) value.bv)) :
    wrmsrTail st ar s1 a1 v f value amd call ⦃ r => TailPost R k st s1 v f value vs r ⦄ :=
  wrmsrTail_genAg hc P.fit f value amd call R k vs AgreeAtA hR hRc fun o ho x hx => by
    obtain ⟨-, h1, h2, -⟩ := msrOff_cases ho
    exact replyKeepsA_of P h1 h2 x hx value call

/-- **WriteMSR's tail on VMX, no reply premise** (premise `CapAgree` [P]; state fact `ReplyPl`). -/
theorem wrmsrTail_vmxP {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (P : ReplyPl st v s1) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelVmx (memW st s1) v.bv vs) :
    wrmsrTail st ar s1 a1 v f value false call ⦃ r => TailPost VcpuRelVmx .vmx st s1 v f value vs r ⦄ :=
  wrmsrTail_genA hc P f value false call VcpuRelVmx .vmx vs (fun _ ho _ hw => msrStore_vmx h ho hw)
    (fun _ _ hag h' => VcpuRelVmx.congrA hag h')

/-- **WriteMSR's tail on SVM, no reply premise** (premise `CapAgree` [P]; state fact `ReplyPl`). -/
theorem wrmsrTail_svmP {a1 : A} (hc : CapAgree ar a1) {s1 : S} {v : U64} (P : ReplyPl st v s1) (f value : U64)
    (call : Bool) {vs : VcpuState} (h : VcpuRelSvm (memW st s1) v.bv vs) :
    wrmsrTail st ar s1 a1 v f value true call ⦃ r => TailPost VcpuRelSvm .svm st s1 v f value vs r ⦄ :=
  wrmsrTail_genA hc P f value true call VcpuRelSvm .svm vs (fun _ ho _ hw => msrStore_svm h ho hw)
    (fun _ _ hag h' => VcpuRelSvm.congrA hag h')

end

/-! ## `ReplyPl` at a joint state -/

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V : Set U64}

/-- **`ReplyPl` from P3's joint invariant and the VCPU placement** (`JAtZ` + `JVm`, via `JVLay`). -/
theorem JAtZ.replyPl (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {v : U64}
    (hv : v ∈ V) : ReplyPl st v s := by
  have Ly := J.jvLay Jv
  have ht : Z.th (L.mem s (curA st s)) = some .tcb := J.hct
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have nodeT := J.nodePl.disj _ ((hJ.tcb _).1 ht)
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  rw [h12] at nodeT
  have hvap := Ly.vap v hv _ _ ht
  simp only [objSize] at hvap
  exact ⟨Ly.vfit v hv, J.kern.ksbAl, J.kern.nodeFit, J.kern.csLt _ J.kern.cpuCs, Jv.ks v hv, Ly.tA _ ht,
    nodeT, hvap⟩

end

end
end Fl4Proofs.P3.VirtReplyKeep
