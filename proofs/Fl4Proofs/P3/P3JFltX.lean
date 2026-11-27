/-
P3 (p3J gen 27), P1/P2-level (FL4 only): **the message transfer with no receive buffer, and the fault IPC's
footprint at `U = ∅`** — P2's `XferOKRS` / `XferFootOKC` [J] discharged for an `RS` that carries "no frame cap in
an IPC-buffer slot" from a fixed state `sE`.

P2 (FootN5 / XferN) states the transfer hypotheses `XferOKRS` and `XferFootOKC` at the states with `RS s s`, `RS`
being the caller's relation kept along `KW` writes (`hRSK`), and names their discharge: an `RS` carrying the
typing of the caps the transfer reads. With `U = ∅` the only cap the transfer needs is the receiver's IPC-buffer
cap: if it is no frame cap, `lookup_ipc_buffer` is `0`, and then FL4's `transfer_caps` returns at once
(`recv_buf = 0`), `copy_mrs` / the fault messages touch only registers (`buf_set` is guarded by `buf ≠ 0`). So:

* `NoBufCap T sE`: at `sE` the buffer slot of every TCB of `T` holds no `Frame` cap (as FL4 decodes it);
  `BufK T sE s`: `s` has `sE`'s key-space base and the two buffer-slot words of every TCB of `T`;
  `BufApart … sE`: those words are aligned and no `KW` word at `sE` (from `BlkOK` by P1's `capw_not_kw`).
* `bufK_kw`: `BufK` is kept by `KW` writes (P2's `hRSK` shape); `bufK_xr`: and by the transfer's register / SC
  writes (`XSFC.start`'s closure). `lookup_ipc_buffer_noBuf`: `NoBufCap` gives the buffer `0`.
* `transfer_caps_rb0`, `do_normal_transfer_rb0`, **`do_ipc_transfer.nbX`** (an `XSFC` step from any `BufK` state),
  **`xferOKRS_nb`**, **`xferFootOKC_nb`**: P2's two [J] transfer hypotheses at `U = ∅`,
  `RS := fun _ s => BufK T sE s`, for every guard (`XG` for `XferOKRS`).
* **`faults.handle_fault.footNB`**: P2's `handle_timeout.footN` for `handle_fault` (the no-handler branch by
  `set_thread_state.kwNP`), at `Kp = ∅`, `Nd = False`, `U = ∅`: a fault IPC from a `BufK` state writes only
  `IpcWN … ∅` words (`KW` minus node identity words, the TCBs' user context, cap-slot and debug words).

No premise; no sorry. New module; no existing statement changed.
-/
import Fl4Proofs.P2.FootN5
import Fl4Proofs.P2.FootN8
import Fl4Proofs.P3.Lookup
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

/-- A cap that is not a frame cap (FL4's `lookup_ipc_buffer` returns `0` for it). -/
def notFrameCap : capability.Cap → Prop
  | .Frame _ _ _ _ _ _ _ _ => False
  | _ => True

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {Es : Set U64}

/-- No TCB of `T` holds a frame cap in its IPC-buffer slot at `s`. -/
def NoBufCap (T : Set U64) (s : S) : Prop :=
  ∀ y ∈ T, ∃ c, Fl4Proofs.P3.capAt (L.mem s) (sbWordA y) = ok c ∧ notFrameCap c

/-- `s` has `sE`'s key-space base and the buffer-slot words of every TCB of `T`. -/
def BufK (T : Set U64) (sE s : S) : Prop :=
  L.ksb s = L.ksb sE ∧ ∀ y ∈ T, L.mem s (sbWordA y) = L.mem sE (sbWordA y) ∧
    L.mem s (core.num.U64.wrapping_add (sbWordA y) 8#u64) =
      L.mem sE (core.num.U64.wrapping_add (sbWordA y) 8#u64)

/-- The buffer-slot words of every TCB of `T` are aligned and no `KW` word at `sE`. -/
def BufApart (T Cs Sg Scs : Set U64) (Z : U64 → Nat) (Es : Set U64) (sE : S) : Prop :=
  ∀ y ∈ T, ∀ b, (b = sbWordA y ∨ b = core.num.U64.wrapping_add (sbWordA y) 8#u64) →
    Aligned b ∧ ¬ KW st T Cs Sg Scs Z Es sE b

theorem BufK.refl (s : S) : BufK (L := L) T s s := ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem NoBufCap.of_bufK {sE s : S} (hN : NoBufCap (L := L) T sE) (hK : BufK (L := L) T sE s) :
    NoBufCap (L := L) T s := by
  intro y hy
  obtain ⟨c, hc, hn⟩ := hN y hy
  refine ⟨c, ?_, hn⟩
  obtain ⟨e1, e2⟩ := hK.2 y hy
  unfold Fl4Proofs.P3.capAt at hc ⊢
  rw [e1, e2]; exact hc

/-- **With no frame cap in its buffer slot, a TCB's IPC-buffer lookup is `0`.** -/
theorem lookup_ipc_buffer_noBuf {s : S} (hN : NoBufCap (L := L) T s) {y : U64} (hy : y ∈ T) (rcv : Bool) :
    msg.lookup_ipc_buffer st s rcv y = ok 0#u64 := by
  obtain ⟨c, hc, hn⟩ := hN y hy
  have hs : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by simp [obj.Tcb.slot, lift, sbWordA]
  unfold msg.lookup_ipc_buffer
  rw [ipc_buffer_word]; simp only [bind_ok]
  rw [hs]; simp only [bind_ok]
  rw [Fl4Proofs.P3.slot_cap_eq, hc]; simp only [bind_ok]
  cases c <;> first | rfl | exact absurd hn id

/-- **`BufK` is kept by `KW` writes** (P2's `hRSK` shape). -/
theorem bufK_kw {sE s1 s2 : S} (hP : BufApart (L := L) T Cs Sg Scs Z Es sE) (h1 : BufK (L := L) T sE s1)
    (w : WritesIn st s1 s2 (KW st T Cs Sg Scs Z Es s1)) : BufK (L := L) T sE s2 := by
  refine ⟨w.1.trans h1.1, fun y hy => ?_⟩
  have k : ∀ b, (b = sbWordA y ∨ b = core.num.U64.wrapping_add (sbWordA y) 8#u64) → L.mem s2 b = L.mem s1 b :=
    fun b hb => w.2.2 b (hP y hy b hb).1 fun hk => (hP y hy b hb).2 (KW.ksb h1.1 hk)
  exact ⟨(k _ (Or.inl rfl)).trans (h1.2 y hy).1, (k _ (Or.inr rfl)).trans (h1.2 y hy).2⟩

/-- **`BufK` is kept by the transfer's register and SC writes** (`XSFC.start`'s closure). -/
theorem bufK_xr {sE s1 s2 : S} (hP : BufApart (L := L) T Cs Sg Scs Z Es sE) (h1 : BufK (L := L) T sE s1)
    (w : WritesIn st s1 s2 (fun b => XferRegW T ∅ b ∨ ∃ c ∈ Scs, InSC c (Z c) b)) : BufK (L := L) T sE s2 := by
  have hk : ∀ b, (XferRegW T ∅ b ∨ ∃ c ∈ Scs, InSC c (Z c) b) → KW st T Cs Sg Scs Z Es sE b := by
    rintro b ((⟨y, hy, K, k1, k2, -, rfl⟩ | hb) | hb)
    · exact Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, rfl⟩
    · exact absurd hb (Set.notMem_empty _)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
  refine ⟨w.1.trans h1.1, fun y hy => ?_⟩
  have k : ∀ b, (b = sbWordA y ∨ b = core.num.U64.wrapping_add (sbWordA y) 8#u64) → L.mem s2 b = L.mem s1 b :=
    fun b hb => w.2.2 b (hP y hy b hb).1 fun hw => (hP y hy b hb).2 (hk b hw)
  exact ⟨(k _ (Or.inl rfl)).trans (h1.2 y hy).1, (k _ (Or.inr rfl)).trans (h1.2 y hy).2⟩

/-- `transfer_caps` with no receive buffer returns at once. -/
theorem transfer_caps_rb0 (s : S) (info : msginfo.MessageInfo) (extra : Aeneas.Std.Array obj.Slot 3#usize)
    (ep rcv : U64) : ipc.transfer_caps st s info extra ep rcv 0#u64 ⦃ r => r.2 = s ⦄ := by
  unfold ipc.transfer_caps
  refine WP.spec_bind (P0.msginfo.MessageInfo.new.p0 _ _ _ _) fun out _ => ?_
  have hl0 : (0#usize).val < extra.val.length := by rw [extra.property]; simp
  refine WP.spec_bind (Aeneas.Std.Array.index_usize_spec extra 0#usize hl0) fun s1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  split
  all_goals first | exact (WP.spec_ok _).2 rfl | (rw [if_pos rfl]; exact (WP.spec_ok _).2 rfl) | simp

variable {U : Set U64} {RS : S → S → Prop} {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64}

/-- A normal transfer to a receiver with no IPC buffer (any sender buffer): an `XSFC` step. -/
theorem do_normal_transfer_rb0 {s0 : S} {snd sb ep badge rcv : U64} {grant : Bool}
    (h : XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s0) (hr : rcv ∈ T) (hb : BufOK U 0#u64) :
    ipc.do_normal_transfer st s0 snd sb ep badge grant rcv 0#u64 ⦃ s' =>
      XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold ipc.do_normal_transfer
  refine WP.spec_bind (P0.msg.msg_info.p0 st s0 snd hS) fun tag _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun extra _ => ?_
  · split
    · refine WP.spec_bind (P0.ipc.lookup_extra_caps.p0 st s0 snd sb tag hS) fun r _ => ?_
      rcases r with e | _ <;> exact (WP.spec_ok _).2 trivial
    · exact (WP.spec_ok _).2 trivial
  refine WP.spec_bind (msg.copy_mrs.xsfc (snd := snd) (sb := sb) (n := tag.length) h hr hb) ?_
  rintro ⟨n, s1⟩ h1
  simp only at h1
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (transfer_caps_rb0 s1 tag extra ep rcv) ?_
  rintro ⟨out, s2⟩ e2
  simp only at e2
  subst e2
  try simp only [WP.uncurry'_pair]
  refine WP.spec_bind (Pₘ := fun s3 => XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0 s3) ?_
    fun s3 h3 => obj.Tcb.set_reg.xsfc h3 hr (by simp [layout.reg.BADGE, layout.reg.RDI])
  unfold msg.set_msg_info
  exact WP.spec_bind (P0.msginfo.MessageInfo.to_word.p0 _) fun w _ =>
    obj.Tcb.set_reg.xsfc (v := w) h1 hr (by simp [layout.reg.MSG_INFO, layout.reg.RSI])

/-- **The message transfer from a `BufK` state is an `XSFC` step at `U = ∅`** (module docstring). -/
theorem ipc.do_ipc_transfer.nbX {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z Es sE) {s : S} {a : A}
    {snd ep badge rcv : U64} {grant : Bool} (hs : snd ∈ T) (hr : rcv ∈ T)
    (hI : XI st T Cs Ω H Sg Rp Scs Nt Z ∅ Ac X Q R s) (hrs : BufK (L := L) T sE s) :
    ipc.do_ipc_transfer st ar s a snd ep badge grant rcv ⦃ s' =>
      XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ (fun _ s => BufK (L := L) T sE s) Ac X Q R s s' ⦄ := by
  have hP0 : P0.StoreTotal st := L.total
  have h0 : XSFC st T Cs Ω H Sg Rp Scs Nt Z ∅ (fun _ s => BufK (L := L) T sE s) Ac X Q R s s :=
    XSFC.start hI hrs fun _ _ r w => bufK_xr hP r w
  have hl := lookup_ipc_buffer_noBuf (hN.of_bufK hrs) hr true
  have hb0 : BufOK ∅ 0#u64 := fun h => (h rfl).elim
  unfold ipc.do_ipc_transfer
  rw [hl, bind_ok]
  refine WP.spec_bind (P0.obj.Tcb.fault_type.p0 st snd s hP0) fun ft _ => ?_
  split
  · refine WP.spec_bind (P0.msg.lookup_ipc_buffer.p0 st s false snd hP0) fun sb _ => ?_
    exact do_normal_transfer_rb0 h0 hr hb0
  · exact ipc.do_fault_transfer.xsfc hA h0 hs hr hb0

/-- **P2's `XferOKRS` [J] at `U = ∅` with `RS := BufK sE`** (module docstring). -/
theorem xferOKRS_nb {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z Es sE) {P3Ok : S → Prop} :
    XferOKRS st ar T Cs Ω H Sg Rp Scs Nt Z ∅ (fun _ s => BufK (L := L) T sE s) (XG st T Cs Ω H Sg Scs Z P3Ok) := by
  intro Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hrs hG0
  refine WP.spec_mono (ipc.do_ipc_transfer.nbX (grant := grant) (ep := ep) (badge := badge) (a := a) hA hN hP hs hr
    ⟨h, hB, hX, hS, hSg, hU⟩ hrs) fun s' h' => ?_
  have h'' := h'.xs
  exact ⟨h''.1.1, h''.1.2.1, h''.1.2.2.1, h''.1.2.2.2.1, h''.1.2.2.2.2.1, h''.fr, XG.xs hG0 h'' hU⟩

/-- **P2's `XferFootOKC` [J] at `U = ∅` with `RS := BufK sE`** (module docstring). -/
theorem xferFootOKC_nb {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {sE : S}
    (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z Es sE) {G : S → Prop} :
    XferFootOKC st ar T Cs Ω H Sg Rp Scs Nt Z ∅ (fun _ s => BufK (L := L) T sE s) G := by
  intro Ac X Q R s a snd ep badge grant rcv hs hr h hB hX hS hSg hU hrs _
  exact WP.spec_mono (ipc.do_ipc_transfer.nbX (grant := grant) (ep := ep) (badge := badge) (a := a) hA hN hP hs hr
    ⟨h, hB, hX, hS, hSg, hU⟩ hrs) fun s' h' => ⟨h'.2.2.1, h'.rs⟩

/-- **A fault IPC from a `BufK` state writes only `IpcWN … ∅` words** (module docstring). -/
theorem faults.handle_fault.footNB {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {P3Ok : S → Prop}
    {sE : S} (hN : NoBufCap (L := L) T sE) (hP : BufApart (L := L) T Cs Sg Scs Z (EH H) sE)
    (s : S) (a : A) (t : obj.Tcb) (f : error.Fault)
    (h : BlkOK st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hc : CanBlock st T Ac s t)
    (hcap : obj.Tcb.slot t layout.tcb.SLOT_FAULT_HANDLER ⦃ sl =>
      obj.Slot.cap st sl s ⦃ c => CapTyped H Rp Nt c ⦄ ⦄)
    (hK0 : BufK (L := L) T sE s) (hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :
    faults.handle_fault st ar s a t f ⦃ s' _ => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s s' ⦄ := by
  have ht := hc.mem
  have hU : UserOK st T Cs Ω H ∅ s := fun b hb => absurd hb (Set.notMem_empty b)
  have hxf := xferOKRS_nb (Ω := Ω) (H := H) (Rp := Rp) (Nt := Nt) (P3Ok := P3Ok) hA hN hP
  have hxw := xferFootOKC_nb (Ω := Ω) (H := H) (Rp := Rp) (Nt := Nt) (G := XG st T Cs Ω H Sg Scs Z P3Ok) hA hN hP
  have q0 := h.1.choose_spec.choose_spec
  unfold faults.handle_fault
  refine WP.spec_bind hcap fun sl hsl => ?_
  refine WP.spec_bind hsl fun c hct => ?_
  step with obj.Tcb.sc.spec as ⟨i, ei⟩
  unfold faults.send_fault_ipc
  refine WP.spec_bind (Pₘ := fun r : Bool × S × A => IpcFootN st ∅ False T Cs Ω Sg Scs Z (EH H) ∅ s r.2.1 ∧
      (r.1 = false → r.2.1 = s)) ?_ ?_
  · split
    all_goals first | exact (WP.spec_ok _).2 ⟨IpcFootN.refl s, fun _ => rfl⟩ | skip
    rename_i p b x y g gr
    have hpH := hct.1 p b x y g gr rfl
    refine WP.spec_bind (WP.spec_and (WP.spec_and (faults.set_fault.blk s t f h ht hU hc)
      (faults.set_fault.sc s t f q0.tcbs ht))
      (faults.set_fault.kwN (Cs := Cs) (Sg := Sg) (Kp := ∅) (Nd := False) (Scs := Scs) (Z := Z) (Es := EH H)
        s t f q0.tcbs q0.nodes q0.cur ht)) ?_
    rintro s1 ⟨⟨⟨h1, hU1, hc1⟩, sc1⟩, F1⟩
    obtain ⟨⟨Q1, R1, q1⟩, hB1, hX1, hS1, hSg1⟩ := h1
    refine WP.spec_bind (endpoint.send_ipc.footN (Nd := False) (Kp := ∅) hA hxf hxw s1 a true false b g gr
      (i != 0#u64) t p Q1 R1 q1 hB1 hX1 hS1 hSg1 hU1 hc1 (fun e => ?_) hpH
      (fun _ _ _ h1 w => bufK_kw hP h1 w) (bufK_kw hP hK0 F1.foot) (hG.foot F1.foot)
      (Set.notMem_empty t) (fun y hy => absurd hy (Set.notMem_empty y)) (fun _ h => h)
      (F1.out (fun _ => Set.notMem_empty _))) ?_
    · have hi : i ≠ 0#u64 := by simpa using e
      rw [sc1, ← ei]; exact hi
    rintro ⟨s2, a1⟩ h2
    try simp only [WP.uncurry'_pair] at h2
    exact (WP.spec_ok _).2 ⟨(FootN.ipc F1).trans h2.1, fun e => by cases e⟩
  · rintro ⟨b, s2, a2⟩ ⟨g2, e2⟩
    try simp only [WP.uncurry'_pair] at e2
    simp only [uncurry_apply_pair]
    split
    · exact (WP.spec_ok _).2 g2
    · rename_i hb
      have e2' : s2 = s := e2 (by simpa using hb)
      rw [e2'] at g2 ⊢
      refine WP.spec_bind (Fl4Proofs.P2.Stall.sched.set_thread_state.kwNP (Kp := ∅) (Nd := False) (Sg := Sg) (Scs := Scs) (Z := Z)
        (Es := EH H) s t _ q0.tcbs q0.nodes q0.cur ht (Set.notMem_empty t)) ?_
      intro s4 f4
      exact (WP.spec_ok _).2 (g2.trans (FootN.ipc f4))

end

end Fl4Proofs.P1
