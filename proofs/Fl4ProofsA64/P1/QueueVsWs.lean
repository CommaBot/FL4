/-
P1 (aarch64, gen 37): **write sets of the Zombie loop's steps**, so that the VSpace typing `VsTy` (QueueVsTy) is
kept along the loop.

Gen 32–36's thread / VCPU walks (`vcpu.complete_run.ubV`, `unbind.ubV`, `detach.ubV`, the `.sck` texts of
QueueScKeep) export `DS` / `JV` / `ScK`, not the words they write. Here **one write-set version** of them:

* **`DW T Ω Vc Ub`** (the VCPU walks' words): a word outside `Ω` that is no thread's `SC` field, a VCPU word, or a
  word of the ghost user-frame set `Ub`. `smp.remote_tcb_stall.dw` (the stall keeps every TCB field and every `Ω`
  word), **`vcpu.complete_run.dw`**, **`vcpu.unbind.dw`**, **`vcpu.detach.dw`**, **`vcpu.finalise.dw`** (the
  `.sck` texts with the write set carried instead of `ScK`); **`ScK.of_dw`** gives back the `SC`-field frame.
* **`TW Ω Sg Scs Z Vc Ub`** (every finaliser of the loop): outside `Ω`, `Sg`, an SC object word, a VCPU word or a
  `Ub` word. `dw_tw`; `kw7_tw` / `kw8_tw` (QueueFoot7 / QueueFoot8's footprints: TCB fields and node words are
  outside `Ω`, endpoint words too — `EpsWit`); **`fin_thread.tw`**, `fin_vcpu.tw`, `finL.tw` (leaves),
  `fin_sc.tw`.
* cap-slot writes: QueueSlots7's `W7.obj.Slot.*.capw` instantiated with the word set `{b | InOS OS b}` and an empty
  `Sg` (`osw`), so `W7.CapW T {b | InOS OS b} ∅` = TCB low words or `OS` slot words: **`cdt.empty_slot.os`**
  (QueueZombieS's `empty_slot.gw` text), `SwO` / **`cdt.swap.jvo`** (QueueZombieT's `swap.jvw` text with that
  write set carried), `cdt.delete_one.tw`, `finalise_cap.irq_tw`.
* **`VrOK`** (state-free placement of the `VsR kb Pt` words, below) and the `VsZ` steps it gives: `vsz_tw`,
  `vsz_cw`, `vsz_irq`, `vsz_pp` (the preemption point's `PPW`), `VrOK.pt` (QueueVsPt's `PtOK`).

**`VrOK Ω Sg Scs Z OS Vc Ub kb Pt`** (a case hypothesis on ghost sets, the fixed `ks` base `kb` and nothing of the
state): every `VsR kb Pt` word (`PtW Pt` or an ASID-table word `ks + 772352 + 8·i`, `i < 128`) is aligned, in `Ω`,
off `Sg`, off every SC object, in no `OS` slot, no VCPU word, no `Ub` word, and no `ks + o` word with
`o < 223488` (the scalar area, IRQ states and IRQ node below the nodes, layout.rs `ks::NODES` = 223488). Source
(objects.rs `create_new_objects`, vspace.rs): page tables, VSpace roots and ASID pools are retyped from untyped
memory as objects of their own, disjoint from CNodes, TCBs, SCs, VCPUs and frames; the ASID table lies in the
kernel-global area after the 128 nodes (layout.rs:167). `Ω`'s other placements (`SchedQueuesInvX.omega`: words
of `Ω` are outside the TCBs and the nodes; `EpsWit`: apart from the endpoints) hold for these words. No named
premise; new definitions and theorems only.
-/
import Fl4ProofsA64.P1.QueueVsTy
open Aeneas Aeneas.Std Result

namespace Fl4ProofsA64.P1
open fl4_core_a64 Fl4ProofsA64.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {P3Ok : S → Prop} {U : Set U64}

namespace W7
namespace R
namespace ST

local notation "wa" => core.num.U64.wrapping_add

variable {A : Type _} {ar : machine.Arch A}

/-! ## The word classes -/

/-- **The VCPU walks' words** (module docstring). -/
def DW (T Ω Vc Ub : Set U64) (b : U64) : Prop := (b ∉ Ω ∧ ∀ z ∈ T, b ≠ scA z) ∨ VcW Vc b ∨ b ∈ Ub

/-- **The finalisers' words** (module docstring). -/
def TW (Ω Sg Scs : Set U64) (Z : U64 → Nat) (Vc Ub : Set U64) (b : U64) : Prop :=
  b ∉ Ω ∨ b ∈ Sg ∨ (∃ c ∈ Scs, InSC c (Z c) b) ∨ VcW Vc b ∨ b ∈ Ub

theorem dw_tw {Vc Ub : Set U64} {b : U64} (h : DW T Ω Vc Ub b) : TW Ω Sg Scs Z Vc Ub b := by
  rcases h with ⟨h1, -⟩ | h | h
  · exact Or.inl h1
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

section cls
variable {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {Vc Ub : Set U64}

theorem dw_fld {s0 : S} (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) {y K : U64} (hy : y ∈ T) (hK : K.val < 4096)
    (hne : K.val ≠ 3464) : DW T Ω Vc Ub (wa y K) :=
  Or.inl ⟨fun hΩ => out_ne_field (q.omega _ hΩ) hy (q.tcbs y hy) hK rfl, fun z hz e =>
    field_ne (q.tcbs z hz) (q.tcbs y hy) (K1 := 3464#u64) (by simp) hK (fun _ h => hne (by simp at h; omega))
      (by rw [← scA_eq]; exact e.symm)⟩

theorem dw_node {s0 : S} (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) {c o : U64} (hc : c ∈ Cs) (ho : o.val < 4288) :
    DW T Ω Vc Ub (L.nodeAt s0 c o) :=
  Or.inl ⟨fun hΩ => out_ne_node (q.omega _ hΩ) hc (q.nodes c hc) ho rfl, fun z hz e =>
    node_ne_field (q.nodes c hc) ho hz (q.tcbs z hz) (K := 3464#u64) (by simp) (by rw [← scA_eq]; exact e)⟩

theorem dw_wr_fld {s0 : S} (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) {s : S} {y K v : U64} (hy : y ∈ T)
    (hK : K.val < 4096) (h8 : K.val % 8 = 0) (hne : K.val ≠ 3464) :
    WritesIn st s (L.wr s (wa y K) v) (DW T Ω Vc Ub) :=
  (writesIn_wr (field_aligned (q.tcbs y hy) hK h8)).mono fun b e => by rw [e]; exact dw_fld q hy hK hne

theorem dw_wr_vc {s : S} {v0 o val : U64} (hv : v0 ∈ Vc) (ho : o.val < 4096) (h8 : o.val % 8 = 0)
    (hal : Aligned (wa v0 o)) : WritesIn st s (L.wr s (wa v0 o) val) (DW T Ω Vc Ub) :=
  (writesIn_wr hal).mono fun b e => by rw [e]; exact Or.inr (Or.inl (vcw_of hv ho h8))

/-- **`ScK` from a `DW` write set.** -/
theorem ScK.of_dw {s0 s s' : S} (q : SchedQueuesInvX st T Cs Ω H X s0 Q R)
    (hW : ∀ b, VcW Vc b → b ∈ Ω) (hU : ∀ b ∈ Ub, b ∈ Ω) (hw : WritesIn st s s' (DW T Ω Vc Ub)) :
    ScK st T s s' :=
  ScK.of_w q.tcbs hw fun z hz hb => by
    have hΩ : scA z ∉ Ω := fun hΩ => out_ne_field (q.omega _ hΩ) hz (q.tcbs z hz) (K := 3464#u64) (by simp) rfl
    rcases hb with ⟨-, h2⟩ | h | h
    · exact h2 z hz rfl
    · exact hΩ (hW _ h)
    · exact hΩ (hU _ h)

theorem kw7_tw {s0 : S} (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) {Es : Set U64}
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) {b : U64}
    (h : K7.KW st T Cs Sg Scs Z Es s0 b ∨ DbgW st T Cs s0 b) : TW Ω Sg Scs Z Vc Ub b := by
  by_cases hΩ : b ∈ Ω
  swap
  · exact Or.inl hΩ
  have ho := q.omega _ hΩ
  rcases h with (⟨y, hy, K, k1, k2, -, -, e⟩ | ⟨c, hc, o, ho', -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e', he', hb'⟩) |
    (⟨y, hy, e | e⟩ | ⟨c, hc, e⟩)
  · exact (out_ne_field ho hy (q.tcbs y hy) k2 (by rw [e])).elim
  · exact (out_ne_node ho hc (q.nodes c hc) ho' (by rw [e])).elim
  · exact Or.inr (Or.inl hm)
  · exact Or.inr (Or.inr (Or.inl ⟨c, hc, hin⟩))
  · exfalso
    obtain ⟨E, EQ, w1, -, wΩ, -, -, ty⟩ := q.eps
    have heE : e' ∈ E := (ty.2.2.1 e').2 (hE e' he')
    obtain ⟨hE', -, -⟩ := w1 e' heE
    have := wΩ e' heE b hΩ
    rcases hb' with rfl | rfl
    · rw [epHeadA_val] at this; omega
    · rw [epTSA_val hE'] at this; omega
  · exact (out_ne_field ho hy (q.tcbs y hy) (K := 3576#u64) (by simp) (by rw [e]; try rfl)).elim
  · exact (out_ne_field ho hy (q.tcbs y hy) (K := 3584#u64) (by simp) (by rw [e]; try rfl)).elim
  · exact (out_ne_node ho hc (q.nodes c hc) (by rw [debug_val]; omega) (by rw [e])).elim

theorem kw8_tw {s0 : S} (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) {Es : Set U64}
    (hE : ∀ e ∈ Es, H e = some .ep ∨ H e = some .ntfn) {b : U64}
    (h : K8.KW st T Cs Sg Scs Z Es s0 b ∨ DbgW st T Cs s0 b) : TW Ω Sg Scs Z Vc Ub b :=
  kw7_tw q hE (h.imp K8.KW.to7 id)

end cls

/-! ## The VCPU walks with their write set -/

/-- **The stall's write set** (it keeps every TCB field and every `Ω` word). -/
theorem smp.remote_tcb_stall.dw (hA : P0.ArchTotal ar) {Vc Ub : Set U64} {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (a : A) (y : U64) :
    smp.remote_tcb_stall st ar s a y ⦃ s' _ => WritesIn st s s' (DW T Ω Vc Ub) ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have hb := hb1.blk
  obtain ⟨⟨Q0, R0, hq0⟩, hb0, hx0, hs0, hg0⟩ := hb1.blk
  refine WP.spec_mono (WP.spec_and (smp.remote_tcb_stall.blk hA s a y hb)
    (smp.remote_tcb_stall.all hA s a y hq0 hb0 hx0 hs0 hg0)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨-, f1, -⟩, _, _, _, _, _, _, _, _, _, keep, kΩ⟩
  refine ⟨f1.1, f1.2.1, fun b hal hn => ?_⟩
  by_cases hΩ : b ∈ Ω
  · exact kΩ b hΩ
  · have hz : ¬ ∀ z ∈ T, b ≠ scA z := fun hz => hn (Or.inl ⟨hΩ, hz⟩)
    push_neg at hz
    obtain ⟨z, hz, rfl⟩ := hz
    rw [scA_eq]; exact keep z hz _ (by simp) (by simp)

section walk
variable {OS Vc Ub : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`complete_run`'s write set** (gen 36's `complete_run.sck` text). -/
theorem vcpu.complete_run.dw (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub)
    {s0 s : S} (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A)
    (y stop m1 m2 m3 : U64) (hy : y ∈ T) (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM) :
    vcpu.complete_run st ar s a y stop m1 m2 m3 ⦃ s' _ => WritesIn st s s' (DW T Ω Vc Ub) ⦄ := by
  obtain ⟨Ac1, hb1⟩ := h.bxi
  have q := hb1.1.choose_spec.choose_spec
  have hT := q.tcbs
  have hta := hT y hy
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  have hU := hv.usr
  have hal : ∀ b ∈ Ub, Aligned b := fun b hb => (hU b hb).out.1
  unfold vcpu.complete_run
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  by_cases hv0 : L.mem s (core.num.U64.wrapping_add y 3672#u64) = 0#u64
  · rw [if_pos hv0]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rw [if_neg hv0]
  have hvc : L.mem s (wa y 3672#u64) ∈ Vc := (hv.run y hy).resolve_left hv0
  have hbuf : RunBuf st Ub s y := hv.buf y hy hv0
  refine WP.spec_bind (hA.vcpu_flush_state _ _ _) fun a1 _ => ?_
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (· ∈ Ub)) ?_ fun s2 w2 => ?_
  · split
    · have hs : obj.Tcb.slot y layout.tcb.SLOT_BUFFER = ok (sbWordA y) := by
        simp [obj.Tcb.slot, lift, sbWordA]
      rw [hs, bind_ok]
      refine WP.spec_bind (spec_eq' (P0.obj.Slot.cap.p0 st (sbWordA y) s L.total)) fun c hc0 => ?_
      obtain ⟨hc, -⟩ := hc0
      cases c
      all_goals try exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rename_i ptr size rights dev c1 c2 c3 c4
      refine WP.spec_bind (spec_eq' (P0.capability.FrameSize.bits.p0 size)) fun bits ⟨hbits, _⟩ => ?_
      have h63 : (bits &&& 63#u64).val < 64 := by
        rw [UScalar.val_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by simp)
      refine WP.spec_bind (spec_eq' (P0.one_shift_positive _ h63)) fun sz ⟨hsz, _⟩ => ?_
      by_cases hd : dev = true
      · rw [if_pos hd]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      rw [if_neg hd]
      split
      · rename_i hrw
        split
        · rename_i ho
          split
          · rename_i hlt
            have hlt' : (L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3672#u64))
                vcpu.RUN_OFFSET)).val < sz.val := hlt
            step as ⟨i7, hi7⟩
            split
            · rename_i hge
              have hge' : 1024 ≤ i7.val := by scalar_tac
              have hF := hbuf ptr size rights dev c1 c2 c3 c4 bits sz hc (by simpa using hd) hrw hbits hsz
                ho hlt' (by unfold runOffA runVcpuA; omega)
              exact vcpu.read_state_to_frame.fw hA s a1 _ _ _ hF hal
            · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
          · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
        · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
      · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  have K2 : WritesIn st s s2 (DW T Ω Vc Ub) := w2.mono fun b hb => Or.inr (Or.inr hb)
  obtain ⟨F2, B2, S2⟩ := UbF.usr h hU w2
  have hw : VcWords Ω Sg (L.mem s (core.num.U64.wrapping_add y 3672#u64)) := hW _ hvc
  have hx := hw vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
  have K3 := dw_wr_vc (st := st) (T := T) (Ω := Ω) (Ub := Ub) (s := s2) (val := 0#u64) hvc
    (o := vcpu.RUN_CALLER) (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER]) hx.1
  obtain ⟨F3, B3, S3⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
  have K4 := dw_wr_fld (Vc := Vc) (Ub := Ub)
    (s := L.wr s2 (wa (L.mem s (wa y 3672#u64)) vcpu.RUN_CALLER) 0#u64) (v := 0#u64) (K := 3672#u64) q hy
    (by simp) (by simp) (by simp)
  obtain ⟨F4, B4, S4, rv4⟩ := UbF.rv0w F3.cur hy
  refine vck_regs _ y stop m1 m2 m3 hta fun s10 w10 => ?_
  have K10 := WritesIn.mono (B := DW T Ω Vc Ub) w10 fun b hb => by
    obtain ⟨K, h1, h2, h3, e⟩ := hb
    rw [e]; exact dw_fld q hy (by omega) (by omega)
  obtain ⟨F10, B10, S10⟩ := UbF.regs F4.cur hy w10
  have F := ((F2.trans F3).trans F4).trans F10
  obtain ⟨_, _, _, q10⟩ := Cur0.q F.cur
  refine WP.spec_bind (sts_fine s10 y sched.TS_RUNNING (q10.nodes _ q10.cur) (q10.tcbs y hy)) fun s11 w11 => ?_
  have K11 := WritesIn.mono (B := DW T Ω Vc Ub) w11 fun b hb => by
    rcases hb with e | e
    · rw [e, stA_eq]; exact dw_fld q hy (by simp) (by simp)
    · rw [e]
      exact dw_node q10 q10.cur (by first | (rw [act_val]; omega) | decide | (simp [layout.node.SCHED_ACTION]; done))
  exact vck_vm_tail hA s11 a1 y (K2.trans1 (K3.trans1 (K4.trans1 (K10.trans1 K11))))

set_option maxHeartbeats 4000000 in
/-- **`vcpu::unbind`'s write set** (gen 36's `unbind.sck` text). -/
theorem vcpu.unbind.dw (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64)
    (hvV : v ∈ Vc) :
    vcpu.unbind st ar s a v ⦃ s' _ => WritesIn st s s' (DW T Ω Vc Ub) ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  have V0 := hv.obj v hvV
  obtain ⟨_, _, _, q0⟩ := Cur0.q h
  have hT := q0.tcbs
  unfold vcpu.unbind vcpu.set_bound
  rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec, eq_of_spec_fd P0.Consts.layout.tcb.VCPU.spec]
  simp only [lift, bind_ok, L.read_eq, L.write_eq]
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    WritesIn st s r.1 (DW T Ω Vc Ub) ∧ DS st T OS Vc s r.1) ?_ ?_
  · split
    · rename_i hne
      have hc0 : L.mem s (core.num.U64.wrapping_add v vcpu.RUN_CALLER) ≠ 0#u64 := by simpa using hne
      have hcT := V0.2.2.resolve_left hc0
      refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.ub hA h a _)
        (smp.remote_tcb_stall.ds hA hO hV hW h a _)) (smp.remote_tcb_stall.dw (Vc := Vc) (Ub := Ub) hA h a _)) ?_
      rintro ⟨s2, a2⟩ ⟨⟨⟨F2, B2, -⟩, D2⟩, K2⟩
      try simp only [uncurry_apply_pair, WP.uncurry'_pair]
      step with obj.Tcb.state.spec as ⟨i1, ei1⟩
      split
      · rename_i hvm
        refine WP.spec_mono (WP.spec_and (vcpu.complete_run.ubV hA hO hV F2.cur (hv.keepZ D2.2) a2 _ _ _ _ _ hcT
          (by rw [← ei1]; exact hvm)) (vcpu.complete_run.dw hA hO hV F2.cur (hv.keepZ D2.2) a2 _ _ _ _ _ hcT
          (by rw [← ei1]; exact hvm))) ?_
        rintro ⟨s3, a3⟩ ⟨⟨F3, B3, D3⟩, K3⟩
        exact ⟨F2.trans F3, B2.trans B3, K2.trans1 K3, DS.trans D2 D3⟩
      · have hx := V0.1 vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
        obtain ⟨F3, B3, -⟩ := UbF.omega (v := 0#u64) F2.cur hx.1 hx.2.1 hx.2.2
        obtain ⟨_, _, _, q2⟩ := Cur0.q F2.cur
        have D3 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q2 hW hvV (by simp [vcpu.RUN_CALLER])
          (by simp [vcpu.RUN_CALLER])
        have K3 := dw_wr_vc (st := st) (T := T) (Ω := Ω) (Ub := Ub) (s := s2) (val := 0#u64) hvV
          (o := vcpu.RUN_CALLER) (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER]) hx.1
        obtain ⟨F4, B4, -, -⟩ := UbF.rv0w F3.cur hcT
        obtain ⟨_, _, _, q3⟩ := Cur0.q F3.cur
        have D4 := DS.lnk0 (K := 3672#u64) hO hV q3 hW hcT (Or.inr (by simp))
        have K4 := dw_wr_fld (Vc := Vc) (Ub := Ub) (s := L.wr s2 (wa v vcpu.RUN_CALLER) 0#u64) (v := 0#u64)
          (K := 3672#u64) q0 hcT (by simp) (by simp) (by simp)
        exact (WP.spec_ok _).2 ⟨(F2.trans F3).trans F4, (B2.trans B3).trans B4, K2.trans1 (K3.trans1 K4),
          D2.trans (D3.trans D4)⟩
    · exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, WritesIn.refl _ _, DS.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, K1, D1⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  have V1 := (hv.keepZ D1.2).obj v hvV
  split
  · exact (WP.spec_ok _).2 K1
  rename_i ht0
  have htT := V1.2.1.resolve_left ht0
  refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.ub hA F1.cur a1 _)
    (smp.remote_tcb_stall.ds hA hO hV hW F1.cur a1 _)) (smp.remote_tcb_stall.dw (Vc := Vc) (Ub := Ub) hA F1.cur a1 _)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨⟨F2, -, -⟩, D2⟩, K2⟩
  try simp only [uncurry_apply_pair, WP.uncurry'_pair]
  refine WP.spec_bind (hA.vcpu_flush a2 v) fun a3 _ => ?_
  have hx0 := V1.1 vcpu.TCB (by simp [vcpu.TCB]) (by simp [vcpu.TCB])
  have hx8 := V1.1 vcpu.OWNER_CPU (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU])
  have K3 := dw_wr_vc (st := st) (T := T) (Ω := Ω) (Ub := Ub) (s := s2) (val := 0#u64) hvV
    (o := vcpu.TCB) (by simp [vcpu.TCB]) (by simp [vcpu.TCB]) hx0.1
  have K4 := dw_wr_vc (st := st) (T := T) (Ω := Ω) (Ub := Ub) (s := L.wr s2 (wa v vcpu.TCB) 0#u64) (val := 0#u64)
    hvV (o := vcpu.OWNER_CPU) (by simp [vcpu.OWNER_CPU]) (by simp [vcpu.OWNER_CPU]) hx8.1
  obtain ⟨F3, -, -⟩ := UbF.omega (v := 0#u64) F2.cur hx0.1 hx0.2.1 hx0.2.2
  obtain ⟨F4, -, -⟩ := UbF.omega (v := 0#u64) F3.cur hx8.1 hx8.2.1 hx8.2.2
  have K5 := dw_wr_fld (Vc := Vc) (Ub := Ub)
    (s := L.wr (L.wr s2 (wa v vcpu.TCB) 0#u64) (wa v vcpu.OWNER_CPU) 0#u64) (v := 0#u64)
    (K := 3664#u64) q0 htT (by simp) (by simp) (by simp)
  obtain ⟨F5, -⟩ := UbF.bnd0 (v := 0#u64) F4.cur htT
  obtain ⟨Ac5, hb5⟩ := F5.cur.bxi
  have hT5 := hb5.1.choose_spec.choose_spec.tcbs
  refine WP.spec_bind (P0.obj.Tcb.reg.p0 st _ _ _ L.total) fun old _ => ?_
  refine WP.spec_bind (P0.regs.sanitise.p0 _ _) fun i4 _ => ?_
  refine WP.spec_bind (obj.Tcb.set_reg.regW _ (hT5 _ htT) (by simp [layout.reg.SPSR_EL1]) (WritesIn.refl _ _))
    fun s6 w6 => ?_
  have K6 := WritesIn.mono (B := DW T Ω Vc Ub) w6 fun b hb => by
    obtain ⟨K, h1, h2, h3, e⟩ := hb
    rw [e]; exact dw_fld q0 htT (by omega) (by omega)
  exact vck_vm_tail hA s6 a3 _ (K1.trans1 (K2.trans1 (K3.trans1 (K4.trans1 (K5.trans1 K6)))))

set_option maxHeartbeats 2000000 in
/-- **`vcpu::detach`'s write set** (gen 36's `detach.sck` text). -/
theorem vcpu.detach.dw (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64)
    (hp : p ∈ T) :
    vcpu.detach st ar s a p ⦃ s' _ => WritesIn st s s' (DW T Ω Vc Ub) ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  obtain ⟨_, _, _, q⟩ := Cur0.q h
  have hT := q.tcbs
  unfold vcpu.detach
  refine WP.spec_bind (Pₘ := fun r : S × A => UbF st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s r.1 ∧ BndK st T s r.1 ∧
    L.mem r.1 (runVcpuA p) = 0#u64 ∧ WritesIn st s r.1 (DW T Ω Vc Ub) ∧ DS st T OS Vc s r.1) ?_ ?_
  · unfold vcpu.cancel_run
    rw [eq_of_spec_fd P0.Consts.layout.tcb.RUN_VCPU.spec]
    simp only [lift, bind_ok, L.read_eq, L.write_eq]
    split
    · rename_i hne
      have hv' : L.mem s (runVcpuA p) ≠ 0#u64 := by simpa [runVcpuA] using hne
      have hvc : L.mem s (runVcpuA p) ∈ Vc := (hv.run p hp).resolve_left hv'
      have hx := hW _ hvc vcpu.RUN_CALLER (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER])
      obtain ⟨F1, B1, -⟩ := UbF.omega (v := 0#u64) h hx.1 hx.2.1 hx.2.2
      have D1 := DS.vc0 (o := vcpu.RUN_CALLER) hO hV q hW hvc (by simp [vcpu.RUN_CALLER])
        (by simp [vcpu.RUN_CALLER])
      have K1 := dw_wr_vc (st := st) (T := T) (Ω := Ω) (Ub := Ub) (s := s) (val := 0#u64) hvc
        (o := vcpu.RUN_CALLER) (by simp [vcpu.RUN_CALLER]) (by simp [vcpu.RUN_CALLER]) hx.1
      obtain ⟨F2, B2, -, e2⟩ := UbF.rv0w F1.cur hp
      obtain ⟨_, _, _, q1⟩ := Cur0.q F1.cur
      have D2 := DS.lnk0 (K := 3672#u64) hO hV q1 hW hp (Or.inr (by simp))
      have K2 := dw_wr_fld (Vc := Vc) (Ub := Ub)
        (s := L.wr s (wa (L.mem s (runVcpuA p)) vcpu.RUN_CALLER) 0#u64) (v := 0#u64)
        (K := 3672#u64) q hp (by simp) (by simp) (by simp)
      exact (WP.spec_ok _).2 ⟨F1.trans F2, B1.trans B2, e2, K1.trans1 K2, D1.trans D2⟩
    · rename_i heq
      exact (WP.spec_ok _).2 ⟨UbF.refl h, BndK.refl s, UScalar.eq_of_val_eq (by simpa [runVcpuA] using heq),
        WritesIn.refl _ _, DS.refl s⟩
  rintro ⟨s1, a1⟩ ⟨F1, B1, rv1, K1, D1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have hv1 := hv.keepZ D1.2
  step with vcpu.bound.spec as ⟨v, ev⟩
  split
  · rename_i hne
    have hv0 : v ≠ 0#u64 := by simpa using hne
    have hvV : v ∈ Vc := by
      rcases hv1.bnd p hp with e | e
      · exact absurd (ev.trans e) hv0
      · rw [ev]; exact e
    refine WP.spec_mono (vcpu.unbind.dw hA hO hV F1.cur hv1 a1 v hvV) ?_
    rintro ⟨s2, a2⟩ K2
    exact K1.trans1 K2
  · exact (WP.spec_ok _).2 K1

/-- **`vcpu::finalise`'s write set.** -/
theorem vcpu.finalise.dw (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64)
    (hvV : v ∈ Vc) :
    vcpu.finalise st ar s a v ⦃ s' _ => WritesIn st s s' (DW T Ω Vc Ub) ⦄ := by
  unfold vcpu.finalise
  refine WP.spec_bind (vcpu.unbind.dw hP hO hV h hv a v hvV) ?_
  rintro ⟨s1, a1⟩ K1
  try simp only [WP.uncurry'_pair, uncurry_apply_pair] at K1 ⊢
  refine WP.spec_bind (hP.vcpu_flush_spec a1 v) fun a2 _ => ?_
  exact (WP.spec_ok _).2 K1

set_option maxHeartbeats 2000000 in
/-- **The thread finaliser's write set** (any finality, a bound VCPU or a run in flight included): the stall and
`detach` write `DW` words, QueueFinThr7's `finThrRest` its `K8.FootD` words. -/
theorem fin_thread.tw (hA : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (p : U64)
    (fin : Bool) (hp : p ∈ T) (hid : p ≠ L.idleW s) :
    objects.finalise_cap_object st ar s a (.Thread p) fin ⦃ r =>
      WritesIn st s r.2.1 (TW Ω Sg Scs Z Vc Ub) ⦄ := by
  have hW : ∀ v ∈ Vc, VcWords Ω Sg v := fun v hv' => (hv.obj v hv').1
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  rw [fin_thread_split]
  refine WP.spec_bind (WP.spec_and (WP.spec_and (smp.remote_tcb_stall.ub hA h a p)
    (smp.remote_tcb_stall.ds hA hO hV hW h a p)) (smp.remote_tcb_stall.dw (Vc := Vc) (Ub := Ub) hA h a p)) ?_
  rintro ⟨s1, a1⟩ ⟨⟨⟨F1, -, -⟩, D1⟩, K1⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  refine WP.spec_bind (WP.spec_and (vcpu.detach.ubV hA hO hV F1.cur (hv.keepZ D1.2) a1 p hp)
    (vcpu.detach.dw hA hO hV F1.cur (hv.keepZ D1.2) a1 p hp)) ?_
  rintro ⟨s2, a2⟩ ⟨⟨F2, rv2, D2⟩, K2⟩
  try simp only [WP.uncurry'_pair, uncurry_apply_pair]
  have F12 := F1.trans F2
  obtain ⟨Ac2, hb2⟩ := F12.cur.bxi
  have q2 := hb2.1.choose_spec.choose_spec
  have hna : L.actionW s2 ≠ p := F12.cur.na p hp
  have hidle : L.idleW s2 ≠ p := by rw [F12.idle]; exact Ne.symm hid
  refine WP.spec_mono (K8.finThrRest.blk hA s2 a2 p hb2.blk hp hna hidle rv2) ?_
  rintro ⟨r1, s3, a3⟩ ⟨-, f8⟩
  exact (WritesIn.mono (B := TW Ω Sg Scs Z Vc Ub) (K1.trans1 K2) fun b hb => dw_tw hb).trans1
    (WritesIn.mono f8 fun b hb => kw8_tw q2 (fun e he => he) hb)

/-- **The VCPU finaliser's write set** (any finality). -/
theorem fin_vcpu.tw (hP : P0.ArchTotal ar) (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VcTy st T Cs Ω H Sg Scs Z Vc Ub s) (a : A) (v : U64)
    (fin : Bool) (hvV : v ∈ Vc) :
    objects.finalise_cap_object st ar s a (.Vcpu v) fin ⦃ r => WritesIn st s r.2.1 (TW Ω Sg Scs Z Vc Ub) ⦄ := by
  cases fin
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · rename_i hf; exact absurd hf (by simp)
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  · unfold objects.finalise_cap_object
    dsimp only
    split
    · refine WP.spec_bind (vcpu.finalise.dw hP hO hV h hv a v hvV) ?_
      rintro ⟨s1, a1⟩ K1
      try simp only [WP.uncurry'_pair, uncurry_apply_pair] at K1 ⊢
      exact (WP.spec_ok _).2 (WritesIn.mono K1 fun b hb => dw_tw hb)
    · rename_i hf; exact absurd rfl hf

end walk

/-! ## The leaf and SC finalisers -/

section leaf
variable {OS Vc Ub : Set U64}

set_option maxHeartbeats 2000000 in
/-- **A leaf cap's finalisation writes only `TW` words.** -/
theorem finL.tw (hP : P0.ArchTotal ar) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64}
    (hx : x ∈ OS) {c : capability.Cap} (hc : obj.Slot.cap st x s = ok c) (hk : ZL c) (a : A) (fin : Bool) :
    objects.finalise_cap st ar s a c fin false ⦃ r => WritesIn st s r.2.1 (TW Ω Sg Scs Z Vc Ub) ⦄ := by
  rcases hk with ht | he
  · rw [finalise_cap.triv ar s a ht fin]; exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  have hty := (h.1.2 x hx).1 _ (by rw [DPF.slot_cap_dec] at hc; exact hc)
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  rcases he with ⟨ep, b0, b1, b2, b3, b4, rfl⟩ | ⟨n, b0, b1, b2, rfl⟩ | ⟨p, g, rfl⟩
  · have hH : H ep = some .ep := hty.1.1.1 ep b0 b1 b2 b3 b4 rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K7.fin_endpoint.blk (ar := ar) s a ep b0 b1 b2 b3 b4 fin hb.blk hH) fun r hr =>
      WritesIn.mono hr.2.2.2 fun b hb' =>
        kw7_tw q (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inl hH) (Or.inl hb')
  · obtain ⟨hn, hH⟩ := hty.1.1.2.1 n b0 b1 b2 rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K7.fin_ntfn.blk (ar := ar) s a n b0 b1 b2 fin hb.blk hn hH) fun r hr =>
      WritesIn.mono hr.2.2.2 fun b hb' =>
        kw7_tw q (fun e he => by rw [Set.mem_singleton_iff.1 he]; exact Or.inr hH) (Or.inl hb')
  · have hp : p ∈ Rp := hty.1.1.2.2 p g rfl
    rw [fin_cap_eq_obj (by simp)]
    exact WP.spec_mono (K7.fin_reply.blk (ar := ar) hP s a p g fin hb.blk hp h.1.1.2) fun r hr =>
      WritesIn.mono hr.2.2 fun b hb' => kw7_tw q (fun e he => he) hb'

/-- **An SC cap's finalisation writes only `TW` words** (at an `ScPlAt` state). -/
theorem fin_sc.tw (hP : P0.ArchTotal ar) {s0 s : S} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x : U64}
    (a : A) (fin : Bool) (hk : ScPlAt st Scs x s) {p b : U64}
    (hc : obj.Slot.cap st x s = ok (.SchedContext p b)) :
    objects.finalise_cap st ar s a (.SchedContext p b) fin false ⦃ r =>
      WritesIn st s r.2.1 (TW Ω Sg Scs Z Vc Ub) ⦄ := by
  obtain ⟨-, hpl⟩ := hk _ hc
  obtain ⟨hpS, hp0, hid⟩ := hpl.2 p b rfl
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hna : L.mem s (scTcbA p) ≠ 0#u64 → L.actionW s ≠ L.mem s (scTcbA p) := fun h0 =>
    h.1.1.1.na _ (hb.2.2.1.2.2.yt.1 p hpS h0)
  rw [fin_cap_eq_obj (by simp)]
  refine WP.spec_mono (K7.fin_sc.blk (ar := ar) hP s a p b fin hb.blk hpS hp0 hna hid) ?_
  rintro r ⟨_, _, _, f⟩
  exact WritesIn.mono f fun b' hb' => kw7_tw q (fun e he => absurd he (Set.notMem_empty e)) (Or.inl hb')

end leaf

/-! ## Cap-slot writes as `OS` slot words -/

section os
variable {OS Vc Ub : Set U64}

/-- An `OS` slot is a `W7.SlotW` slot of the word set `{b | InOS OS b}` with an empty `Sg`. -/
theorem osw (hO : OSOK T Ω Sg OS) {x : U64} (hx : x ∈ OS) : W7.SlotW T {b | InOS OS b} ∅ x :=
  ⟨hO.al0 hx, fun o ho h8 => Or.inr ⟨⟨x, hx, by rw [wv (hO.fit x hx) ho]; omega,
    by rw [wv (hO.fit x hx) ho]; omega⟩, Set.notMem_empty _⟩⟩

set_option maxHeartbeats 4000000 in
/-- **`empty_slot` of a slot of `OS` with a cleanup whose `post_cap_deletion` writes `P` words** writes `OS` slot
words (or TCB low words) and `P` words (QueueZombieS's `empty_slot.gw` text). -/
theorem cdt.empty_slot.os (hO : OSOK T Ω Sg OS) {s : S} {a : A} {x : U64}
    {cl : capability.Cap} {P : U64 → Prop} (hT : SlotTy st T Ω Sg H Rp Nt OS s) (hx : x ∈ OS)
    (hpcd : ∀ (s1 : S) (a1 : A), L.ksb s1 = L.ksb s →
      objects.post_cap_deletion st ar s1 a1 cl ⦃ r => WritesIn st s1 r.1 P ⦄) :
    cdt.empty_slot st ar s a x cl ⦃ r => WritesIn st s r.1 (fun b => W7.CapW T {b | InOS OS b} ∅ b ∨ P b) ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold cdt.empty_slot
  refine WP.spec_bind (P0.obj.Slot.cap.p0 st x s hS) fun c0 _ => ?_
  refine WP.spec_bind (P0.capability.Cap.is_null.p0 c0) fun bn _ => ?_
  split
  · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
  have hxo := hT x hx
  obtain ⟨nx, hnx⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s (wa x 24#u64)))
  have hnl : LinkOK OS nx := hxo.2.2 nx hnx
  have hpv : LinkOK OS (L.mem s (wa x 16#u64)) := hxo.2.1
  rw [slot_prev_eq, bind_ok, slot_next_of hnx, bind_ok]
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x s hS) fun fb _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s1 => WritesIn st s s1 (W7.CapW T {b | InOS OS b} ∅)) ?_ fun s1 h1 => ?_
  · split
    · exact (WP.spec_ok _).2 (WritesIn.refl _ _)
    · rename_i hp0
      have hpO : L.mem s (wa x 16#u64) ∈ OS := hpv.resolve_left (by simpa using hp0)
      exact W7.obj.Slot.set_next.capw (osw hO hpO)
  refine WP.spec_bind (Pₘ := fun s2 => WritesIn st s s2 (W7.CapW T {b | InOS OS b} ∅)) ?_ fun s2 h2 => ?_
  · split
    · exact (WP.spec_ok _).2 h1
    · rename_i hn0
      have hnO : nx ∈ OS := hnl.resolve_left (by simpa using hn0)
      refine WP.spec_bind (W7.obj.Slot.set_prev.capw (osw hO hnO)) fun s3 w3 => ?_
      refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st nx s3 hS) fun nfb _ => ?_
      split <;> exact WP.spec_mono (W7.obj.Slot.set_first_badged.capw (osw hO hnO)) fun s' w =>
        (h1.trans1 w3).trans1 w
  refine WP.spec_bind (W7.obj.Slot.clear.capw (osw hO hx)) fun s3 w3 => ?_
  exact WP.spec_mono (hpcd s3 _ (h2.trans1 w3).1) fun r hr => (h2.trans1 w3).trans hr

/-- `SwW` and the swap's writes as `OS` slot words. -/
def SwO (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap) (Sg Rp Scs Nt : Set U64)
    (Z : U64 → Nat) (Ac OS Vc Ub : Set U64) (s0 s : S) (x1 x2 : U64) (c1 c2 : capability.Cap) (s' : S) : Prop :=
  SwW st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s' ∧ WritesIn st s s' (W7.CapW T {b | InOS OS b} ∅)

theorem SwO.lnk (hO : OSOK T Ω Sg OS) {s0 s s' : S} {x1 x2 : U64} {c1 c2 : capability.Cap}
    (h : SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s') {p k v : U64} (hp : p ∈ OS)
    (hk : k.val = 16 ∨ k.val = 24) (hj : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 (L.wr s' (wa p k) v))
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) :
    SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 (L.wr s' (wa p k) v) := by
  have k32 : k.val < 32 := by rcases hk with e | e <;> omega
  have k8 : k.val % 8 = 0 := by rcases hk with e | e <;> omega
  exact ⟨h.1.lnk hO hp hk hj hx1 hx2, h.2.trans1 ((writesIn_wr (v := v) (hO.al hp k32 k8)).mono fun b e => by
    subst e; exact (osw hO hp).2 k k32 k8)⟩

set_option maxHeartbeats 4000000 in
/-- **`cdt.swap.jvw` with the write set as `OS` slot words** (QueueZombieT's text). -/
theorem cdt.swap.jvo (hO : OSOK T Ω Sg OS) (hV : VcOK T Scs Z OS Vc Ub) {s0 s : S}
    (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) {x1 x2 : U64} {c1 c2 : capability.Cap}
    (hx1 : x1 ∈ OS) (hx2 : x2 ∈ OS) (hne : x1 ≠ x2) (hs1 : obj.sext48 x1 = ok x1) (hs2 : obj.sext48 x2 = ok x2)
    (hc1 : obj.Slot.cap st x1 s = ok c1) (hc2 : obj.Slot.cap st x2 s = ok c2) (hf1 : NoFrame c1)
    (hf2 : NoFrame c2) :
    cdt.swap st s c1 x1 c2 x2 ⦃ s' => SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have hd1 : capability.Cap.decode (L.mem s x1) (L.mem s (wa x1 8#u64)) = ok c1 := by
    rw [DPF.slot_cap_dec] at hc1; exact hc1
  have hd2 : capability.Cap.decode (L.mem s x2) (L.mem s (wa x2 8#u64)) = ok c2 := by
    rw [DPF.slot_cap_dec] at hc2; exact hc2
  have ht1 : CapTy T Ω Sg H Rp Nt OS c1 := (h.1.2 x1 hx1).1 _ hd1
  have ht2 : CapTy T Ω Sg H Rp Nt OS c2 := (h.1.2 x2 hx2).1 _ hd2
  obtain ⟨a1, b1, he1, hr1⟩ := CapRt.dec_rt hd1
  obtain ⟨a2, b2, he2, hr2⟩ := CapRt.dec_rt hd2
  unfold cdt.swap
  refine WP.spec_bind (WP.spec_and (WP.spec_and (JV.setc hO hV h hx1 he2 hr2 ht2 hf2)
    (W7.obj.Slot.set_cap.capw (hO.slot _ hx1))) (W7.obj.Slot.set_cap.capw (osw hO hx1))) ?_
  rintro s1 ⟨⟨⟨h1, k1, e1⟩, w1⟩, o1⟩
  refine WP.spec_bind (WP.spec_and (WP.spec_and (JV.setc hO hV h1 hx2 he1 hr1 ht1 hf1)
    (W7.obj.Slot.set_cap.capw (hO.slot _ hx2))) (W7.obj.Slot.set_cap.capw (osw hO hx2))) ?_
  rintro s2 ⟨⟨⟨h2, k2, e2⟩, w2⟩, o2⟩
  have P2 : SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s2 :=
    ⟨⟨⟨h2, by rw [capk4 k2 hx1 hne]; exact e1, e2, fun y hy n1 n2 => by
      rw [capk4 k2 hy n2, capk4 k1 hy n1]⟩, w1.trans1 w2⟩, o1.trans1 o2⟩
  have l1 := h2.1.2 x1 hx1
  rw [slot_prev_eq s2 x1, bind_ok]
  obtain ⟨n1, hn1⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s2 (wa x1 24#u64)))
  rw [slot_next_of hn1, bind_ok]
  have lp1 : LinkOK OS (L.mem s2 (wa x1 16#u64)) := l1.2.1
  have ln1 : LinkOK OS n1 := l1.2.2 n1 hn1
  have in1 : obj.sext48 n1 = ok n1 := sx_idem _ _ hn1
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x1 s2 hS) fun r1 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x1 s2 hS) fun f1 _ => ?_
  simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s3 => SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s3) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P2
    · rename_i hp0
      have hpO : L.mem s2 (wa x1 16#u64) ∈ OS := lp1.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact P2.lnk hO hpO (k := 24#u64) (by simp)
        (JV.nextw hO hV h2 hpO (Or.inr hx2) hs2 (link_bits _ _)) hx1 hx2
  intro s3 P3
  refine WP.spec_bind (Pₘ := fun s4 => SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s4) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P3
    · rename_i hn0
      have hnO : n1 ∈ OS := ln1.resolve_left (by simpa using hn0)
      rw [set_prev_eq, WP.spec_ok]
      exact P3.lnk hO hnO (k := 16#u64) (by simp) (JV.prev hO hV P3.1.1.1 hnO (Or.inr hx2)) hx1 hx2
  intro s4 P4
  have l2 := P4.1.1.1.1.2 x2 hx2
  rw [slot_prev_eq s4 x2, bind_ok]
  obtain ⟨n2, hn2⟩ := DPF.spec_tot (P0.obj.sext48.p0 (L.mem s4 (wa x2 24#u64)))
  rw [slot_next_of hn2, bind_ok]
  have lp2 : LinkOK OS (L.mem s4 (wa x2 16#u64)) := l2.2.1
  have ln2 : LinkOK OS n2 := l2.2.2 n2 hn2
  have in2 : obj.sext48 n2 = ok n2 := sx_idem _ _ hn2
  refine WP.spec_bind (P0.obj.Slot.revocable.p0 st x2 s4 hS) fun r2 _ => ?_
  refine WP.spec_bind (P0.obj.Slot.first_badged.p0 st x2 s4 hS) fun f2 _ => ?_
  rw [set_prev_eq s4 x1 _, bind_ok]
  have P5 := P4.lnk hO hx1 (k := 16#u64) (by simp) (JV.prev hO hV P4.1.1.1 hx1 lp2) hx1 hx2
  refine WP.spec_bind (set_nf_spec _ x1 n2 r2 f2) ?_
  rintro s6 ⟨w6, rfl, hw6⟩
  have P6 := P5.lnk hO hx1 (k := 24#u64) (by simp) (JV.nextw hO hV P5.1.1.1 hx1 ln2 in2 hw6) hx1 hx2
  rw [set_prev_eq _ x2 _, bind_ok]
  have P7 := P6.lnk hO hx2 (k := 16#u64) (by simp) (JV.prev hO hV P6.1.1.1 hx2 lp1) hx1 hx2
  refine WP.spec_bind (set_nf_spec _ x2 n1 r1 f1) ?_
  rintro s8 ⟨w8, rfl, hw8⟩
  have P8 := P7.lnk hO hx2 (k := 24#u64) (by simp) (JV.nextw hO hV P7.1.1.1 hx2 ln1 in1 hw8) hx1 hx2
  try simp only [obj.Slot.is_null, bind_ok]
  refine WP.spec_bind (Pₘ := fun s9 => SwO st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s x1 x2 c1 c2 s9) ?_ ?_
  · split
    · exact (WP.spec_ok _).2 P8
    · rename_i hp0
      have hpO : L.mem s4 (wa x2 16#u64) ∈ OS := lp2.resolve_left (by simpa using hp0)
      rw [set_next_eq, WP.spec_ok]
      exact P8.lnk hO hpO (k := 24#u64) (by simp)
        (JV.nextw hO hV P8.1.1.1 hpO (Or.inr hx1) hs1 (link_bits _ _)) hx1 hx2
  intro s9 P9
  split
  · exact (WP.spec_ok _).2 P9
  · rename_i hn0
    have hnO : n2 ∈ OS := ln2.resolve_left (by simpa using hn0)
    rw [set_prev_eq, WP.spec_ok]
    exact P9.lnk hO hnO (k := 16#u64) (by simp) (JV.prev hO hV P9.1.1.1 hnO (Or.inr hx1)) hx1 hx2

end os

/-! ## The `VsR` placement and the `VsZ` steps -/

/-- **The `VsR` words' placement** (state-free; module docstring). -/
structure VrOK (Ω Sg Scs : Set U64) (Z : U64 → Nat) (OS Vc Ub : Set U64) (kb : U64) (Pt : Set U64) : Prop where
  al : ∀ b, VsR kb Pt b → Aligned b
  om : ∀ b, VsR kb Pt b → b ∈ Ω
  sg : ∀ b, VsR kb Pt b → b ∉ Sg
  sc : ∀ b, VsR kb Pt b → ∀ c ∈ Scs, ¬ InSC c (Z c) b
  os : ∀ b, VsR kb Pt b → ¬ InOS OS b
  vc : ∀ b, VsR kb Pt b → ¬ VcW Vc b
  ub : ∀ b, VsR kb Pt b → b ∉ Ub
  ks : ∀ b, VsR kb Pt b → ∀ o : U64, o.val < 223488 → wa kb o ≠ b

section vz
variable {OS Vc Ub : Set U64} {kb : U64} {Pt : Set U64}

/-- `VrOK` gives QueueVsPt's `PtOK`. -/
theorem VrOK.pt (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) : PtOK T Ω Sg OS Vc Pt :=
  ⟨fun b hb => ⟨hR.al b (Or.inl hb), hR.om b (Or.inl hb), hR.sg b (Or.inl hb)⟩,
    fun b hb y hy hin => hR.os b (Or.inl hb) ⟨y, hy, hin.1, hin.2⟩, fun b hb => hR.vc b (Or.inl hb)⟩

theorem vsr_not_tw (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {b : U64} (hb : VsR kb Pt b) :
    ¬ TW Ω Sg Scs Z Vc Ub b := by
  rintro (h | h | ⟨c, hc, hin⟩ | h | h)
  · exact h (hR.om b hb)
  · exact hR.sg b hb h
  · exact hR.sc b hb c hc hin
  · exact hR.vc b hb h
  · exact hR.ub b hb h

/-- **A `TW` write set is a `VsZ` step.** -/
theorem vsz_tw (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s s' : S} (hw : WritesIn st s s' (TW Ω Sg Scs Z Vc Ub)) :
    VsZ st kb Pt s s' :=
  VsZ.of_w hR.al hw fun b hb => vsr_not_tw hR hb

theorem vsr_not_cw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {b : U64}
    (hb : VsR kb Pt b) : ¬ W7.CapW T {b | InOS OS b} ∅ b := by
  rintro (hl | ⟨hin, -⟩)
  · exact W7.tlow_ne_out q.tcbs (q.omega _ (hR.om b hb)) hl
  · exact hR.os b hb hin

/-- **An `OS`-slot write set is a `VsZ` step.** -/
theorem vsz_cw {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s s' : S}
    (hw : WritesIn st s s' (W7.CapW T {b | InOS OS b} ∅)) : VsZ st kb Pt s s' :=
  VsZ.of_w hR.al hw fun b hb => vsr_not_cw q hR hb

/-- **An `OS`-slot and IRQ-state write set is a `VsZ` step.** -/
theorem vsz_irq {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {irq : U64}
    (hi : irq.val < 5376) {s s' : S}
    (hw : WritesIn st s s' (fun b => W7.CapW T {b | InOS OS b} ∅ b ∨ IrqStW kb irq b)) : VsZ st kb Pt s s' :=
  VsZ.of_w hR.al hw fun b hb h => h.elim (vsr_not_cw q hR hb) fun ⟨o, ho, e⟩ =>
    hR.ks b hb o (by omega) e.symm

/-- **A `TW` or `OS`-slot write set is a `VsZ` step.** -/
theorem vsz_twc {X : Set U64} {Q : U64 → U64 → List U64} {R : U64 → List U64} {s0 : S}
    (q : SchedQueuesInvX st T Cs Ω H X s0 Q R) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s s' : S}
    (hw : WritesIn st s s' (fun b => TW Ω Sg Scs Z Vc Ub b ∨ W7.CapW T {b | InOS OS b} ∅ b)) :
    VsZ st kb Pt s s' :=
  VsZ.of_w hR.al hw fun b hb h => h.elim (vsr_not_tw hR hb) (vsr_not_cw q hR hb)

set_option maxHeartbeats 2000000 in
/-- **The preemption point is a `VsZ` step** (its `PPW` words: `WORK_UNITS` and two node words). -/
theorem sched.preemption_point.vz (hP : P0.ArchTotal ar) (hR : VrOK Ω Sg Scs Z OS Vc Ub kb Pt) {s0 s : S}
    {a : A} (h : JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0 s) (hk : L.ksb s = kb) :
    sched.preemption_point st ar s a ⦃ r => VsZ st kb Pt s r.2.1 ⦄ := by
  obtain ⟨Ac', hb⟩ := h.1.parts
  have q := hb.1.choose_spec.choose_spec
  have hN := q.nodes _ q.cur
  refine WP.spec_mono (sched.preemption_point.pp (Ac := Ac') hP s a hb.blk) ?_
  rintro r ⟨-, w⟩
  refine VsZ.of_w hR.al w fun b hb' hp => ?_
  have ho := q.omega _ (hR.om b hb')
  rcases hp with e | e | e
  · exact hR.ks b hb' layout.ks.WORK_UNITS (by simp [layout.ks.WORK_UNITS]) (by rw [e, hk])
  · unfold LawfulStore.nodeA at e
    exact out_ne_node ho q.cur hN (o := layout.node.CUR_TIME) (by simp [layout.node.CUR_TIME]) (by rw [e])
  · unfold LawfulStore.nodeA at e
    exact out_ne_node ho q.cur hN (o := layout.node.CONSUMED) (by simp [layout.node.CONSUMED]) (by rw [e])

end vz

end ST
end R
end W7

end

end Fl4ProofsA64.P1
