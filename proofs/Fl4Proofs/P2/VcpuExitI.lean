/-
# P2 (vexit gen 4): the IRQ slots through `vexit_pre` (`hI` discharged)

`syscall.handle_vcpu_exit.entryV` / `entryJ2` (P2/VcpuExitV, VcpuExitJ) take
`hI` [P]: after `vexit_pre`, when an IRQ came, the IRQ handler slots of the
kernel-global IRQ node name heap notifications (`IrqNtAt`). Here:

* **at the entry** (`irqNtAt_of_JAtZ`): at a P3 `JAtZ` state, IRQ `i`'s slot
  (`nodeA kb i`, a one-slot CNode of the typed heap, `IntLayout.node`) is
  related to the spec's IRQ node slot (the CNode relation), so its cap
  decodes, and a notification cap there names one of `Z.N` (`JAtZ.slotN`),
  hence a heap notification (`JAtZ.zH`). This is all of `hI` when
  `stalled = true` (`vexit_pre` is the identity).
* **across `vexit_pre`** (`stalled = false`, `vexit_pre.irq`): the two words of
  every IRQ slot (`IrqW`) are kept (`IrqFr`):
  - `update_timestamp` writes current-node words only (`irqFr_footB0`);
  - `vcpu.check` writes, by the new narrower **`VckN`** (`vcpu.check.vckN`),
    only the thread's register words, user words `U`, the bound notification's
    state word, the thread's state word and the core's action word (`VckW`
    admitted every word outside the TCBs and nodes); none is an IRQ slot word
    (`irqFr_vckN`; the user words by `UsrW.ks`);
  - `check_budget`: `check_budget.allGB` with `G := IrqFr` from the entry,
    every `FootB` step missing the IRQ words (`KgW.not_kwB`); its timeout
    fault in the pinned premise **`TmoIbVI`** [P] (`TmoIbV` plus `IrqFr` across
    the fault: a statement about the timeout fault only).
  The IRQ words are apart from P1's objects (`IrqOff`, `KgW`: outside TCBs and
  nodes, the endpoints and notifications, the frame words and the SC objects),
  which `irqOff_of_JAtZ` derives from P3 `JKern.hks` (every non-`other` heap
  object lies outside the kernel-global block).

**`syscall.handle_vcpu_exit.entryI`**: `entryV` with `hI` replaced by
`IrqOff`/`IrqNtAt` at the entry and `htk` with `TmoIbVI`.
**`syscall.handle_vcpu_exit.entryJ3`** (also `vm_timer_local.entryJ3`): from
every reachable entry state (`JReachU17`), premises `kernel_entry_domInvU29`'s
and `htk` [P] (`TmoIbVI`) only; `hI` gone. **`syscall.handle_vcpu_exit.entryJ3s`**:
the stalled run, `kernel_entry_domInvU29`'s premises only.
-/
import Fl4Proofs.P2.VcpuExitJ
import Fl4Proofs.P3.JProducers
import Fl4Proofs.P3.Lookup
open Aeneas Aeneas.Std Result

set_option autoImplicit false

namespace Fl4Proofs.P2.Stall
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1

attribute [local instance] atCpuI

/-! ## The IRQ slot words and their frame -/

/-- The two words of each IRQ handler slot's cap in the kernel-global IRQ node at `kb`. -/
def IrqW (kb b : U64) : Prop :=
  ∃ i : U64, i.val < 128 ∧ (b = irqSlotA kb i ∨ b = core.num.U64.wrapping_add (irqSlotA kb i) 8#u64)

/-- An IRQ slot word is a kernel-global word: `kb + o` with `o` aligned below `13568`. -/
theorem irqW_off {kb b : U64} (h : IrqW kb b) :
    ∃ o : U64, o.val < 13568 ∧ o.val % 8 = 0 ∧ b = core.num.U64.wrapping_add kb o := by
  obtain ⟨i, hi, hb | hb⟩ := h
  · refine ⟨core.num.U64.wrapping_add 1248#u64 (core.num.U64.wrapping_mul i 32#u64), ?_, ?_, ?_⟩
    · simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
      simp [U64.size, U64.numBits]; omega
    · simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
      simp [U64.size, U64.numBits]; omega
    · subst hb; unfold irqSlotA; apply UScalar.eq_of_val_eq
      simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
      simp [U64.size, U64.numBits]; omega
  · refine ⟨core.num.U64.wrapping_add (core.num.U64.wrapping_add 1248#u64 (core.num.U64.wrapping_mul i 32#u64))
      8#u64, ?_, ?_, ?_⟩
    · simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
      simp [U64.size, U64.numBits]; omega
    · simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
      simp [U64.size, U64.numBits]; omega
    · subst hb; unfold irqSlotA; apply UScalar.eq_of_val_eq
      simp only [core.num.U64.wrapping_add_val_eq, core.num.U64.wrapping_mul_val_eq]
      simp [U64.size, U64.numBits]; omega

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st] {T : Set U64} {Ω : Set U64} {H : Heap}
variable {Cs Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64} {U : Set U64}

/-- The IRQ slot words of `s0` are kept at `s` (and the kernel-global base). -/
def IrqFr (st : machine.Store S) [L : LawfulStore st] (s0 s : S) : Prop :=
  L.ksb s = L.ksb s0 ∧ ∀ b, IrqW (L.ksb s0) b → L.mem s b = L.mem s0 b

theorem IrqFr.refl (s : S) : IrqFr st s s := ⟨rfl, fun _ _ => rfl⟩

theorem IrqFr.trans {s0 s1 s2 : S} (h1 : IrqFr st s0 s1) (h2 : IrqFr st s1 s2) : IrqFr st s0 s2 :=
  ⟨h2.1.trans h1.1, fun b hb => (h2.2 b (by rw [h1.1]; exact hb)).trans (h1.2 b hb)⟩

/-- A write missing every IRQ slot word keeps them. -/
theorem irqFr_step {s0 s1 s2 : S} {B : U64 → Prop} (g : IrqFr st s0 s1) (w : WritesIn st s1 s2 B)
    (hB : ∀ b, IrqW (L.ksb s0) b → Aligned b ∧ ¬ B b) : IrqFr st s0 s2 :=
  ⟨w.1.trans g.1, fun b hb => (w.mem_eq (hB b hb).1 (hB b hb).2).trans (g.2 b hb)⟩

theorem slot_cap_dec (sl : obj.Slot) (s : S) :
    obj.Slot.cap st sl s = capability.Cap.decode (L.mem s sl) (L.mem s (core.num.U64.wrapping_add sl 8#u64)) := by
  unfold obj.Slot.cap
  simp [L.read_pair_eq, lift]

/-- The IRQ slots' caps are kept along `IrqFr`. -/
theorem irqNtAt_fr {s0 s : S} (h : IrqNtAt st Nt s0) (g : IrqFr st s0 s) : IrqNtAt st Nt s := by
  intro i hi
  have e1 := g.2 _ ⟨i, hi, Or.inl rfl⟩
  have e2 := g.2 _ ⟨i, hi, Or.inr rfl⟩
  have h0 := h i hi
  rw [slot_cap_dec] at h0 ⊢
  rw [g.1, e1, e2]
  exact h0

/-- A kernel-global word apart from P1's objects (`UsrW` without its
kernel-global clause): outside the TCBs and nodes, the endpoints and
notifications, the frame words and the SC objects. -/
structure KgW (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (s : S) (b : U64) : Prop where
  out : OutsideObjs st T Cs s b
  eps : ∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val
  sg : b ∉ Sg
  sc : ∀ c ∈ Scs, ¬ InSC c (Z c) b

/-- The IRQ slot words are kernel-global words apart from P1's objects (at `s`). -/
def IrqOff (st : machine.Store S) [L : LawfulStore st] (T Cs : Set U64) (H : Heap) (Sg Scs : Set U64)
    (Z : U64 → Nat) (s : S) : Prop :=
  ∀ b, IrqW (L.ksb s) b → KgW st T Cs H Sg Scs Z s b

theorem IrqOff.ksb {s0 s : S} (h : IrqOff st T Cs H Sg Scs Z s0) (hk : L.ksb s = L.ksb s0) :
    IrqOff st T Cs H Sg Scs Z s := fun b hb => by
  rw [hk] at hb
  obtain ⟨o, e, g, c⟩ := h b hb
  exact ⟨o.ksb hk, e, g, c⟩

/-- A `KgW` word is no `KWB` word. -/
theorem KgW.not_kwB {s : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {b : U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (hw : KgW st T Cs H Sg Scs Z s b) :
    ¬ KWB st T Cs Sg Scs Z (EH H) s b := by
  rintro (⟨y, hy, K, -, h2, -, -, -, e⟩ | ⟨c, hc, o, ho, -, e⟩ | hm | ⟨c, hc, hin⟩ | ⟨e, he, hb⟩)
  · exact out_ne_field hw.out hy (hq.tcbs y hy) h2 (by rw [e])
  · exact out_ne_node hw.out hc (hq.nodes c hc) ho (by rw [e])
  · exact hw.sg hm
  · exact hw.sc c hc hin
  · obtain ⟨E, EQ, hEW⟩ := hq.eps
    have heE : e ∈ E := (hEW.2.2.2.2.2.2.2.1 e).2 he
    obtain ⟨hE, -, -⟩ := hEW.1 e heE
    have hv : b.val = e.val ∨ b.val = e.val + 8 := by
      rcases hb with rfl | rfl
      · exact Or.inl epHeadA_val
      · exact Or.inr (epTSA_val hE)
    have := hw.eps e he
    omega

/-- A `FootB` step (from a state with the entry's kernel-global base) keeps the IRQ slot words. -/
theorem irqFr_footB {s0 s1 s2 : S} {Q : U64 → U64 → List U64} {R : U64 → List U64}
    (hq : SchedQueuesInv st T Cs Ω H s1 Q R) (hO : IrqOff st T Cs H Sg Scs Z s0) (g : IrqFr st s0 s1)
    (f : FootB st T Cs Sg Scs Z (EH H) s1 s2) : IrqFr st s0 s2 :=
  irqFr_step g f fun b hb => by
    have k := (hO.ksb g.1) b (by rw [g.1]; exact hb)
    exact ⟨k.out.1, k.not_kwB hq⟩

/-- A node-words-only step (`update_timestamp`) keeps the IRQ slot words. -/
theorem irqFr_footB0 {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {Z' : U64 → Nat}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (hO : IrqOff st T Cs H Sg Scs Z s)
    (f : FootB st ∅ Cs ∅ ∅ Z' ∅ s s') : IrqFr st s s' :=
  irqFr_step (IrqFr.refl s) f fun b hb => ⟨(hO b hb).out.1, by
    rintro (⟨y, hy, -⟩ | ⟨c, hc, o, ho, -, e⟩ | hm | ⟨c, hc, -⟩ | ⟨e', he', -⟩)
    · exact absurd hy (Set.notMem_empty _)
    · exact out_ne_node (hO b hb).out hc (hq.nodes c hc) ho (by rw [e])
    · exact absurd hm (Set.notMem_empty _)
    · exact absurd hc (Set.notMem_empty _)
    · exact absurd he' (Set.notMem_empty _)⟩

/-! ## `vcpu::check`'s words, narrowed (`VckN`) -/

/-- **The words `vcpu::check` of `y` writes** (narrower than `VckW`, whose
`VckR` admits every word outside the TCBs and nodes): `y`'s register words and
the user words `U` (the report, `RepW`), a notification's state word (the
bound notification, set idle), `y`'s state word and the core's action word. -/
def VckN (st : machine.Store S) [L : LawfulStore st] (U Nt : Set U64) (y : U64) (s0 : S) (b : U64) : Prop :=
  RepW y U b ∨ (∃ n ∈ Nt, b = epTSA n) ∨ b = stA y ∨ b = L.nodeAt s0 (L.cpu s0) layout.node.SCHED_ACTION

theorem VckN.ksb {y : U64} {s0 s1 : S} {b : U64} (hk : L.ksb s1 = L.ksb s0) (hc : L.cpu s1 = L.cpu s0)
    (h : VckN st U Nt y s1 b) : VckN st U Nt y s0 b := by
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by rw [h, hc, nodeAt_of_ksb hk])))

variable {A : Type _} {ar : machine.Arch A}

/-- **The current thread's report writes `VckN` words** (`vcpu.report.xfV`,
then `set_thread_state`'s state and action words). -/
theorem vcpu.report.vckN (hA : P0.ArchTotal ar) {s : S} (a : A) (y badge : U64)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hy : y = L.curW s)
    (hvm : L.mem s (stA y) = sched.TS_RUNNING_VM)
    (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b) (hbuf : msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add y 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3664#u64)) vcpu.PENDING) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add y 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.report st ar s a y badge ⦃ s' => WritesIn st s s' (VckN st U Nt y s) ⦄ := by
  subst hy
  have hb := EntryInv.vckBlk h
  obtain ⟨⟨Q, R, hq⟩, -, -, -, -⟩ := EntryInv.vckBlk h
  have hcT : L.curW s ∈ T := hq.curT
  refine WP.spec_mono (vcpu.report.xfV hA s a _ badge hb hcT hvm hU hbuf hpw) ?_
  rintro s' ⟨s2, h2, -, w2, e⟩
  obtain ⟨⟨Q2, R2, q2⟩, -, -, -, -⟩ := h2
  have hw := sched.set_thread_state.vckW2 s2 (L.curW s) sched.TS_RUNNING q2.tcbs (q2.nodes _ q2.cur) hcT
  rw [e, WP.spec_ok] at hw
  refine (w2.trans hw.1).mono fun b hb => ?_
  rcases hb with hb | hb | hb
  · exact Or.inl hb
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr (by rw [hb, w2.2.1, nodeAt_of_ksb w2.1])))

/-- **`vcpu::check` of the current thread writes only `VckN` words** (the walk
of `vcpu.check.vck`, with the narrower footprint). Premises as `vcpu.check.vck`. -/
theorem vcpu.check.vckN (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hU : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s b)
    (hbuf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK U b ⦄)
    (hpw : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING ∈ U) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ := by
  obtain ⟨⟨Q, R, hq⟩, hB, hX, hS, hSg⟩ := (EntryInv.vckBlk h)
  have hT := hq.tcbs
  have hcT : L.curW s ∈ T := hq.curT
  have OK0 : (ok (s, a) : Result (S × A)) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ :=
    (WP.spec_ok _).2 (WritesIn.refl _ _)
  unfold vcpu.check
  step with obj.Tcb.state.spec as ⟨i, ei⟩
  split
  · exact OK0
  rename_i hvm0
  have hvm : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM := by
    rw [← ei]; by_contra hne; exact hvm0 (bne_iff_ne.mpr hne)
  have REP0 : ∀ bd : U64, (do
      let s1 ← vcpu.report st ar s a (L.curW s) bd
      ok (s1, a)) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ := fun bd =>
    WP.spec_bind (vcpu.report.vckN hA a _ bd h rfl hvm hU hbuf (fun h0 _ => hpw h0)) fun s1 hs1 =>
      (WP.spec_ok _).2 hs1
  -- the bound notification's badge (the VCPU, if any, has no pending exit)
  have NT : (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
      L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64)) vcpu.PENDING) =
        0#u64) → ∀ n : U64, n = L.mem s (boundA (L.curW s)) → n ≠ 0#u64 → L.epState s n = obj.NTFN_ACTIVE →
      (do
        let badge ← obj.Ntfn.badge st n s
        let s1 ← obj.Ntfn.set_state st n s obj.NTFN_IDLE
        let s2 ← vcpu.report st ar s1 a (L.curW s) badge
        ok (s2, a)) ⦃ s' _ => WritesIn st s s' (VckN st U Nt (L.curW s) s) ⦄ := by
    intro hP0 n en hn0 hact
    have hnN : n ∈ Nt := by rw [en]; exact hX.2.2.bnd _ hcT (by rw [← en]; exact hn0)
    have hnH := hNt n hnN
    obtain ⟨E, EQ, hEW⟩ := hq.eps
    have he : n ∈ E := (hEW.2.2.2.2.2.2.2.1 n).2 (Or.inr hnH)
    obtain ⟨hE, hEN, -⟩ := hEW.1 n he
    have hEΩ : ∀ x ∈ Ω, x.val + 8 ≤ n.val ∨ n.val + 16 ≤ x.val := hEW.2.2.1 n he
    have hTS := epTSA_val hE
    have a2 : Aligned (epTSA n) := (ep_aligned hE).2
    refine WP.spec_bind (obj.Ntfn.badge.any s n) fun bd _ => ?_
    refine WP.spec_bind (obj.Ntfn.set_state.val s n _) fun s1 e1 => ?_
    subst e1
    obtain ⟨h2, hB2, hX2, hS2, hSg2, f2, -, ea2, -, ec2⟩ :=
      ntfn_idle_all hq hB hX hS hSg hnH (by rw [hact, ntfn_active_val])
    set s1 := L.wr s (epTSA n) ((L.mem s (epTSA n) &&& ~~~3#u64) ||| (obj.NTFN_IDLE &&& 3#u64)) with hs1
    have hout : OutsideObjs st T Cs s (epTSA n) := by
      refine ⟨a2, fun t ht => ?_, fun c hc => ?_⟩
      · have := hE.disj t ht; rw [hTS]; omega
      · have := hEN.1 c hc; rw [hTS]; omega
    have hnh : ∀ c ∈ Scs, epTSA n ≠ scReplyA c ∧ epTSA n ≠ scTcbA c := by
      intro c hc
      obtain ⟨⟨a1, i1⟩, ⟨a3, i3⟩⟩ := vck_sclink_in hX.1 hc
      have r1 := hEΩ _ (hX.1.scW c hc _ a1 i1)
      have r3 := hEΩ _ (hX.1.scW c hc _ a3 i3)
      refine ⟨fun e => ?_, fun e => ?_⟩
      · have := congrArg UScalar.val e; rw [hTS] at this; omega
      · have := congrArg UScalar.val e; rw [hTS] at this; omega
    have w1 : WritesIn st s s1 (VckW st T Cs Scs (L.curW s) s) :=
      (writesIn_wr a2).mono fun b e => Or.inl (Or.inl (by rw [e]; exact ⟨hout, hnh⟩))
    have w1n : WritesIn st s s1 (fun b => b = epTSA n) := writesIn_wr a2
    obtain ⟨-, eC1, ec1, -, fld1, -⟩ := VckW.frames hq hcT w1
    have h1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 :=
      EntryInv.vckStep h ⟨⟨Q, R, h2⟩, hB2, hX2, hS2, hSg2⟩ ec1 eC1 (Or.inl ea2) fun z hz => by
        rw [scA_eq]; exact fld1 z hz _ (by simp) (by simp) (fun _ => Or.inr (by simp))
    have st1 : L.mem s1 (stA (L.curW s)) = sched.TS_RUNNING_VM := by
      rw [stA_eq, f2 _ hcT _ (by simp) (by simp) (by simp) (by simp), ← stA_eq]; exact hvm
    have hU1 : ∀ b ∈ U, UsrW st T Cs H Sg Scs Z s1 b := fun b hb => (hU b hb).ksb w1.1
    have hbuf1 : msg.lookup_ipc_buffer st s1 true (L.curW s) ⦃ b => BufOK U b ⦄ := by
      rw [lookup_ipc_buffer_same ((VckW.ibFr hq hcT w1).2 _ hcT)]; exact hbuf
    have ev1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
        L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
      f2 _ hcT _ (by simp) (by simp) (by simp) (by simp)
    have hp1 : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
        L.mem s1 (core.num.U64.wrapping_add (L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64))
          vcpu.PENDING) = 0#u64 := by
      intro hv0
      rw [ev1] at hv0 ⊢
      have hu := hU _ (hpw hv0)
      have hne := hu.eps n (Or.inr hnH)
      rw [hs1, L.mem_wr_ne a2 hu.out.1 (by rw [hTS]; omega)]
      exact hP0 hv0
    refine WP.spec_bind (vcpu.report.vckN hA a _ bd h1 eC1.symm st1 hU1 hbuf1 (fun h0 hp => absurd (hp1 h0) hp))
      fun s2 hs2 => (WP.spec_ok _).2 ?_
    exact (w1n.trans hs2).mono fun b hb => hb.elim (fun e => Or.inr (Or.inl ⟨n, hnN, e⟩))
      (fun hb => VckN.ksb w1n.1 w1n.2.1 hb)
  unfold vcpu.bound
  step as ⟨o, ho⟩
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun v ev => ?_
  subst ho
  split
  · rename_i hv0
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s _) fun i1 ei1 => ?_
    split
    · exact REP0 0#u64
    · rename_i hi1
      have hP0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
          L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64))
            vcpu.PENDING) = 0#u64 := fun _ => by
              rw [← ev, ← ei1]; by_contra hne; exact hi1 (bne_iff_ne.mpr hne)
      refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
      split
      · rename_i hi2
        refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
        split
        · rename_i hi3
          exact NT hP0 i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
        · split
          · exact REP0 0#u64
          · exact OK0
      · split
        · exact REP0 0#u64
        · exact OK0
  · rename_i hv0
    have hP0 : L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) ≠ 0#u64 →
        L.mem s (core.num.U64.wrapping_add (L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64))
          vcpu.PENDING) = 0#u64 := fun hne => absurd (by rw [← ev]; by_contra hne'; exact hv0 (bne_iff_ne.mpr hne')) hne
    refine WP.spec_bind (obj.Tcb.bound_ntfn.val s _) fun i2 ei2 => ?_
    split
    · rename_i hi2
      refine WP.spec_bind (obj.Ntfn.state.spec s i2) fun i3 ei3 => ?_
      split
      · rename_i hi3
        exact NT hP0 i2 ei2 (by simpa using hi2) (by rw [← ei3]; exact hi3)
      · split
        · exact REP0 0#u64
        · exact OK0
    · split
      · exact REP0 0#u64
      · exact OK0

/-- A `VckN` write of the current thread keeps the IRQ slot words. -/
theorem irqFr_vckN {s s' : S} {Q : U64 → U64 → List U64} {R : U64 → List U64} {y : U64}
    (hq : SchedQueuesInv st T Cs Ω H s Q R) (hO : IrqOff st T Cs H Sg Scs Z s)
    (hU : ∀ u ∈ U, UsrW st T Cs H Sg Scs Z s u) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (hy : y ∈ T)
    (w : WritesIn st s s' (VckN st U Nt y s)) : IrqFr st s s' :=
  irqFr_step (IrqFr.refl s) w fun b hb => ⟨(hO b hb).out.1, by
    have nk := (hO b hb).not_kwB hq
    rintro ((⟨K, h1, h2, -, e⟩ | hu) | ⟨n, hn, e⟩ | e | e)
    · exact nk (Or.inl ⟨y, hy, K, by omega, by omega, by omega, by omega, by omega, e⟩)
    · obtain ⟨o, ho, h8, e⟩ := irqW_off hb
      exact (hU b hu).ks o ho h8 e.symm
    · exact nk (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, Or.inr (hNt n hn), Or.inr e⟩))))
    · exact nk (Or.inl ⟨y, hy, 3328#u64, by simp, by simp, by simp, by simp, by simp, by rw [e, stA_eq]⟩)
    · exact nk (Or.inr (Or.inl ⟨L.cpu s, hq.cur, layout.node.SCHED_ACTION, by rw [act_val]; omega,
        by rw [act_val]; omega, e⟩))⟩

/-- `vcpu.check` of the current thread (from the `VmPl` placement) keeps the IRQ slot words. -/
theorem vexit_checkQ (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn) (s : S) (a : A)
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hV : VmPl st T Cs H Sg Scs Z U s)
    (hO : IrqOff st T Cs H Sg Scs Z s) :
    vcpu.check st ar s a (L.curW s) ⦃ s' _ => IrqFr st s s' ⦄ := by
  have hq := h.1.choose_spec.choose_spec
  have hcT : L.curW s ∈ T := hq.curT
  by_cases hv : L.mem s (stA (L.curW s)) = sched.TS_RUNNING_VM
  · obtain ⟨hBA, hpw⟩ := hV hv
    refine WP.spec_mono (vcpu.check.vckN hA hNt s a h hBA.1 (hBA.2 _ hcT) hpw) ?_
    rintro ⟨s', a'⟩ hh
    simp only [WP.uncurry'_pair] at hh ⊢
    exact irqFr_vckN hq hO hBA.1 hNt hcT hh
  · rw [check_of_ne ar s a _ hv, WP.spec_ok]
    exact IrqFr.refl s

/-! ## The budget check -/

/-- **[P] The timeout fault of a budget check from `s0` keeps the
buffer-lookup words, every TCB's VCPU word and the IRQ slot words** (and the
invariants), at the states `TmoGB` names (`TmoIbV` with the IRQ slots: a
statement about the timeout fault only). (tmofr: over `Timeout` faults only, the fault `end_timeslice` raises; a non-timeout fault
would take the cap-transferring normal transfer.) -/
def TmoIbVI (st : machine.Store S) [L : LawfulStore st] {A : Type _} (ar : machine.Arch A) (T Cs Ω : Set U64)
    (H : Heap) (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) (Ac : Set U64) (s0 : S) : Prop :=
  ∀ (s : S) (a : A) (f : U64) (Q : U64 → U64 → List U64) (R : U64 → List U64),
    SchedQueuesInv st T Cs Ω H s Q R → BoundInv st T Ac s → XInv st T Cs Ω Sg Rp Scs Nt Z s → SgOK st Ω Sg s →
    SCsOK st T Ω Sg Scs Z Ac s → WritesIn st s0 s (ChgW st Scs Z s0) → CurOK st T s →
    faults.handle_timeout st ar s a (L.curW s) (error.Fault.Timeout f) ⦃ s' _ => BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s' ∧
      IbFr (L := L) T s s' ∧ VcpuWK st T s s' ∧ IrqFr st s s' ⦄

theorem TmoIbVI.v {s0 : S} (hT : TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0) :
    TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 :=
  fun s a f Q R h hB hX hSg hS w hc => WP.spec_mono (hT s a f Q R h hB hX hSg hS w hc) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hr.2.1, hr.2.2.1⟩

theorem TmoIbVI.gb {s0 : S} (hT : TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0) (sA : S) :
    TmoGB st ar T Cs Ω H Sg Rp Scs Nt Z Ac s0 (fun s' => IrqFr st sA s') :=
  fun s a f Q R h hB hX hSg hS w hc hG => WP.spec_mono (hT s a f Q R h hB hX hSg hS w hc) fun r hr => by
    obtain ⟨s', a'⟩ := r
    simp only [WP.uncurry'_pair] at hr ⊢
    exact ⟨hr.1, hG.trans hr.2.2.2⟩

/-- **`check_budget` keeps the IRQ slot words of `s0`** (`check_budget.allGB`
with `G := IrqFr s0`), when its timeout fault does (`TmoIbVI` at its start). -/
theorem sched.check_budget.irq (hA : P0.ArchTotal ar) (s : S) (a : A) {s0 : S}
    (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s) (hO : IrqOff st T Cs H Sg Scs Z s0) (g : IrqFr st s0 s)
    (htmo : TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    sched.check_budget st ar s a ⦃ r s' _ => IrqFr st s0 s' ⦄ := by
  obtain ⟨⟨Q, R, h0⟩, hB, hX, hS, -, hcA, hna, hcsc⟩ := h
  refine WP.spec_mono (sched.check_budget.allGB hA s a Q R h0 hB hX hS.sg hS hcsc hna hcA
    (G := fun s' => IrqFr st s0 s') (fun _ _ b g1 f => by
      obtain ⟨⟨Q1, R1, q1⟩, -⟩ := b
      exact irqFr_footB q1 hO g1 f) g (htmo.gb s0)) ?_
  rintro ⟨r, s', a'⟩ ⟨⟨-, g1⟩, -⟩
  exact g1

/-- **The prefix of `handle_vcpu_exit` keeps the IRQ slot words** (from the
`IrqOff` placement at the entry; `TmoIbVI` for the timeout fault). -/
theorem vexit_pre.irq (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hPd : PendAt st U s) (hO : IrqOff st T Cs H Sg Scs Z s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    vexit_pre st ar s a stalled ⦃ s' _ => IrqFr st s s' ⦄ := by
  unfold vexit_pre
  cases stalled with
  | true => exact (WP.spec_ok _).2 (IrqFr.refl s)
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hq := h.1.choose_spec.choose_spec
    refine WP.spec_bind (WP.spec_and (WP.spec_and (Fl4Proofs.P1.sched.update_timestamp.bxc hA s a (EntryInv.bxi h))
      (Fl4Proofs.P2.Stall.sched.update_timestamp.kwB (T := ∅) (Sg := ∅) (Scs := ∅) (Es := ∅)
        (Z := fun _ => 0) hA s a (nodePlaced0 (hq.nodes _ hq.cur)) hq.cur)) (htk rfl)) ?_
    rintro ⟨s1, a1⟩ ⟨⟨⟨⟨hb1, c1, k1⟩, n1, f1⟩, F1⟩, T1⟩
    have E1 : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s1 := EntryInv.of_step h hb1.blk c1 n1.2.2 (Or.inl n1.1) f1
    have I1 : IbFr (L := L) T s s1 := ibFr_footB0 hq F1
    have G1 : IrqFr st s s1 := irqFr_footB0 hq hO F1
    have hcur : L.curW s1 = L.curW s := k1.1
    have hcT : L.curW s ∈ T := hq.curT
    have V1 : VmPl st T Cs H Sg Scs Z U s1 := fun hv => by
      rw [hcur] at hv ⊢
      have est : L.mem s1 (stA (L.curW s)) = L.mem s (stA (L.curW s)) :=
        footB0_fld hq hcT (by simp [layout.tcb.STATE]) (by simp [layout.tcb.STATE]) F1
      have evc : L.mem s1 (core.num.U64.wrapping_add (L.curW s) 3664#u64) =
          L.mem s (core.num.U64.wrapping_add (L.curW s) 3664#u64) :=
        footB0_fld hq hcT (by simp) (by simp) F1
      refine ⟨hBA.of_fr I1, fun hw => ?_⟩
      rw [evc] at hw ⊢
      exact hPd (est ▸ hv) hw
    show (do
      let ct ← sched.cur_thread st s1
      let (s3, a3) ← vcpu.check st ar s1 a1 ct
      let (_, s4, a4) ← sched.check_budget st ar s3 a3
      ok (s4, a4)) ⦃ s' _ => IrqFr st s s' ⦄
    rw [cur_thread_ok]; simp only [bind_ok]
    refine WP.spec_bind (WP.spec_and (WP.spec_and (vexit_checkV hA hNt s1 a1 E1 V1)
      (vexit_checkQ hA hNt s1 a1 E1 V1 (hO.ksb G1.1))) T1) ?_
    rintro ⟨s2, a2⟩ ⟨⟨⟨E2, -, -⟩, G2⟩, T2⟩
    refine WP.spec_bind (sched.check_budget.irq hA s2 a2 E2 hO (G1.trans G2) T2) ?_
    rintro ⟨r, s3, a3⟩ G3
    exact (WP.spec_ok _).2 G3

/-- **`hI` from the entry**: the IRQ slots name heap notifications at the
entry (`IrqNtAt`), and `vexit_pre` keeps their words. -/
theorem vexit_hI (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s) (hO : IrqOff st T Cs H Sg Scs Z s)
    (hIN : IrqNtAt st Nt s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    vexit_pre st ar s a stalled ⦃ s1 _ => (irq != syscall.NO_IRQ) = true → IrqNtAt st Nt s1 ⦄ :=
  WP.spec_mono (vexit_pre.irq hA hNt s a stalled h hBA (pendAt_of_vcpuZ hz h.1.choose_spec.choose_spec.curT) hO htk)
    fun r g => by
      obtain ⟨s1, a1⟩ := r
      simp only [WP.uncurry'_pair] at g ⊢
      exact fun _ => irqNtAt_fr hIN g

/-- `htk` with `TmoIbVI` gives `entryV`'s `htk` (`TmoIbV`). -/
theorem tmoIbV_tk {s : S} {a : A} {stalled : Bool}
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbV st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄ := fun e =>
  WP.spec_mono (htk e) fun r hr => by
    obtain ⟨s1, a1⟩ := r
    try simp only [WP.uncurry'_pair] at hr ⊢
    exact WP.spec_mono hr fun r2 hr2 => by
      obtain ⟨s2, a2⟩ := r2
      try simp only [WP.uncurry'_pair] at hr2 ⊢
      exact hr2.v

/-- **(vexit gen 4) The serial VM exit keeps `EntryInv`, `hI` discharged**:
`entryV` with `hI` from `IrqOff` and `IrqNtAt` at the entry. Named premises:
`hBA` [P] (`BufAt` at the entry), `hO` [P] (`IrqOff` at the entry), `hIN` [P]
(`IrqNtAt` at the entry), `htk` [P] (`TmoIbVI`). -/
theorem syscall.handle_vcpu_exit.entryI (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq : U64) (stalled : Bool) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s) (hO : IrqOff st T Cs H Sg Scs Z s)
    (hIN : IrqNtAt st Nt s)
    (htk : stalled = false → sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    syscall.handle_vcpu_exit st ar s a irq stalled ⦃ s' _ => EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s' ⦄ :=
  syscall.handle_vcpu_exit.entryV hA hNt s a irq stalled h hBA hz (tmoIbV_tk htk)
    (vexit_hI hA hNt s a irq stalled h hBA hz hO hIN htk)

/-- **The x86 local VM timer exit keeps `EntryInv`, `hI` discharged** (`vm_timer_local.entryV`). -/
theorem vm_timer_local.entryI (hA : P0.ArchTotal ar) (hNt : ∀ n ∈ Nt, H n = some .ntfn)
    (s : S) (a : A) (irq n : U64) (p : localtimer.TimerIrqPlan) (h : EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hBA : BufAt st T Cs H Sg Scs Z U s) (hz : VcpuZ st T s) (hO : IrqOff st T Cs H Sg Scs Z s)
    (hIN : IrqNtAt st Nt s)
    (htk : sched.update_timestamp st ar s a ⦃ s1 a1 =>
      vcpu.check st ar s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st ar T Cs Ω H Sg Rp Scs Nt Z Ac s2 ⦄ ⦄) :
    localvm.handle_vm_timer_irq_local st ar s a irq p n ⦃ r => r.1 = true →
      EntryInv st T Cs Ω H Sg Rp Scs Nt Z Ac r.2.1 ⦄ :=
  vm_timer_local.entryV hA hNt s a irq n p h hBA hz (tmoIbV_tk (stalled := false) (fun _ => htk) rfl)
    (vexit_hI hA hNt s a irq false h hBA hz hO hIN (fun _ => htk))

end

/-! ## From a reachable entry state -/

open Fl4Proofs.P3 Fl4Proofs.P3.Sched Fl4Proofs.P3.Vs Fl4Proofs.P3.SInvR.G4 Fl4Proofs.P3.SInvR.G5

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The IRQ slots name heap notifications at a `JAtZ` state** (as P3
`JAtZ.handleIrqJIN`'s signal case: `J.intL`, the CNode relation, `J.slotN`,
`J.zH`). -/
theorem irqNtAt_of_JAtZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : IrqNtAt st (Heap.ntfns H) s := by
  intro i hi
  have hnode := J.intL.node i hi
  obtain ⟨cs, hkc, hwf, hsl⟩ := J.xtop.rel.2.1.1.cnode _ 0 hnode
  obtain ⟨c, ac, hcap, -, -⟩ := hsl [] rfl
  rw [show slotAddr (nodeA (L.ksb s) i).bv (Fl4Spec.ofBl []) = nodeA (L.ksb s) i from
    cslotAddr_nil _] at hcap
  rw [slot_cap_eq, show irqSlotA (L.ksb s) i = nodeA (L.ksb s) i from rfl, hcap, WP.spec_ok]
  rintro p b0 b1 b2 rfl
  have hA : AbsSlot Z.th ((nodeA (L.ksb s) i).bv, []) := ⟨_, rfl, Or.inl hnode⟩
  exact J.zH.2.2.2 _ (J.slotN hA (by rw [cslotAddr_nil]; exact hcap)).1

/-- **The IRQ slot words are apart from P1's objects at a `JAtZ` state**
(`JKern.hks`: every heap object other than `other` lies outside the
kernel-global block; the nodes follow it). -/
theorem irqOff_of_JAtZ {A : Type} {arI : machine.Arch A} {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : Heap}
    {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    IrqOff st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) s := by
  intro b hb
  obtain ⟨o, ho, h8, e⟩ := irqW_off hb
  have hks := J.kern.hks
  have hf := J.kern.ksbFit
  have hal := J.kern.ksbAl
  have hv : b.val = (L.ksb s).val + o.val := by
    rw [e]
    simp only [core.num.U64.wrapping_add_val_eq]
    simp [U64.size, U64.numBits]; omega
  -- every non-`other` heap object lies outside the block
  have hobj : ∀ p k, H p = some k → (∀ z, k ≠ .other z) → p.val + 2 ^ k.bits ≤ b.val ∨ b.val + 8 ≤ p.val := by
    intro p k hp hk
    have := hks p k hp hk
    omega
  refine ⟨⟨?_, fun t ht => ?_, fun c _ => ?_⟩, fun e' he' => ?_, fun hm => ?_, fun c hc hin => ?_⟩
  · show b.val % 8 = 0
    omega
  · have := hobj t .tcb ht (fun z h => by cases h)
    simp only [HKind.bits, Nat.reducePow] at this
    omega
  · have : L.nodeBase s c = (L.ksb s).val + 13568 + c.val * 4288 := rfl
    omega
  · rcases he' with he' | he'
    · have := hobj e' .ep he' (fun z h => by cases h)
      simp only [HKind.bits, Nat.reducePow] at this
      omega
    · have := hobj e' .ntfn he' (fun z h => by cases h)
      simp only [HKind.bits, Nat.reducePow] at this
      omega
  · obtain ⟨-, p, k, hp, hk, hin⟩ := hm
    have hk' : ∀ z, k ≠ .other z := by
      rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z' h <;> cases h
    have := hobj p k hp hk'
    unfold InObj at hin
    omega
  · obtain ⟨z, hz⟩ := hc
    rw [Heap.scBits_eq hz] at hin
    have := hobj c _ hz (fun z' h => by cases h)
    simp only [HKind.bits] at this
    unfold InSC at hin
    omega

set_option maxHeartbeats 4000000 in
/-- **The vexit entry facts at every reachable entry state, with the IRQ
slots** (`vexitEnt_of_reachU17` plus `IrqOff` and `IrqNtAt`). Premises:
`kernel_entry_domInvU29`'s. -/
theorem vexitEntI_of_reachU17 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac U : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      BufAt st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) U s ∧
      VcpuZ st (Heap.tcbs H) s ∧
      IrqOff st (Heap.tcbs H) Cs H (Heap.frame H) (Heap.scs H) (Heap.scBits H) s ∧
      IrqNtAt st (Heap.ntfns H) s := by
  obtain ⟨Z, H, Cs, Ac, Lst, D, J, ⟨hI, -⟩, -⟩ :=
    kernel_entry_domInvU29 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  obtain ⟨hc, -, hz⟩ := ventS_of_JAtZ J
  exact ⟨H, Cs, Ac, BufU Z σ, hc, hI, J.bufAtJ, hz, irqOff_of_JAtZ J, irqNtAt_of_JAtZ J⟩

set_option maxHeartbeats 4000000 in
/-- **(vexit gen 4) The serial VM exit from every reachable entry state keeps
`EntryInv`, `hI` discharged** (`entryI`). Premises:
`kernel_entry_domInvU29`'s, and the run premise `htk` [P] (`TmoIbVI`: the
timeout fault keeps the buffer-lookup, VCPU and IRQ slot words; only when
`stalled = false`). -/
theorem syscall.handle_vcpu_exit.entryJ3 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq : U64) (stalled : Bool),
      (stalled = false → sched.update_timestamp st arI s a0 ⦃ s1 a1 =>
        vcpu.check st arI s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st arI (Heap.tcbs H) Cs (Heap.omega H) H
          (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s2 ⦄ ⦄) →
      syscall.handle_vcpu_exit st arI s a0 irq stalled ⦃ s' _ => EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H
        (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ⦄ := by
  obtain ⟨H, Cs, Ac, U, hc, hI, hBA, hz, hO, hIN⟩ :=
    vexitEntI_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq stalled htk =>
    syscall.handle_vcpu_exit.entryI hA (fun _ hn => hn) s a0 irq stalled hI hBA hz hO hIN htk⟩

set_option maxHeartbeats 4000000 in
/-- **(vexit gen 4) A stalled VM exit from every reachable entry state keeps
`EntryInv`, with no run premise** (`entryJ3` at `stalled = true`). Premises:
`kernel_entry_domInvU29`'s only. -/
theorem syscall.handle_vcpu_exit.entryJ3s {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq : U64),
      syscall.handle_vcpu_exit st arI s a0 irq true ⦃ s' _ => EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H
        (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s' ⦄ := by
  obtain ⟨H, Cs, Ac, hc, hI, hR⟩ :=
    syscall.handle_vcpu_exit.entryJ3 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq => hR a0 irq true (fun e => absurd e (by simp))⟩

set_option maxHeartbeats 4000000 in
/-- **The x86 local VM timer exit from every reachable entry state keeps
`EntryInv`, `hI` discharged** (`vm_timer_local.entryI`). Premises:
`kernel_entry_domInvU29`'s and `htk` [P] (`TmoIbVI`). -/
theorem vm_timer_local.entryJ3 {A : Type} (arI : machine.Arch A) (AR : A → Fl4Spec.Cr3 → Prop)
    (MR : A → Fl4Spec.MachineState → Prop) [Fl4Proofs.P1.PlainStore st] (hARI : ARIface arI AR)
    (hA : P0.ArchTotal arI) (hnd : Fl4Spec.numDomains = 1) (hM : MachPlat arI MR)
    (hKD : MRKeepD arI MR) (hIo : MRKeepIo arI MR) (hIoa : MRKeepIoapic arI MR)
    (hPA : PPPlatA arI AR) (hIA : IrqPlatA arI AR)
    (hT : TimeAgree arI)
    (hmax : Fl4Spec.maxTicksToUs = core.num.U64.MAX.bv)
    (htu : ∀ a v, arI.ticks_to_us a v ⦃ r => r.bv = Fl4Spec.ticksToUs v.bv ⦄)
    (hRef : ArchRefines arI AR) (hPI : PortInValMR arI MR) (hSX : P1.StoreExt st) (hDR : SetDlDetR (A := A) MR)
    {s : S} {a : A} {σ : Fl4Spec.State Unit} (hJ : JReachU17 (L := L) arI AR MR s a σ) :
    ∃ (H : Heap) (Cs Ac : Set U64), L.cpu s ∈ Cs ∧
      EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
        (Heap.scBits H) Ac s ∧
      ∀ (a0 : A) (irq n : U64) (p : localtimer.TimerIrqPlan),
      sched.update_timestamp st arI s a0 ⦃ s1 a1 =>
        vcpu.check st arI s1 a1 (L.curW s1) ⦃ s2 _ => TmoIbVI st arI (Heap.tcbs H) Cs (Heap.omega H) H
          (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H) (Heap.scBits H) Ac s2 ⦄ ⦄ →
      localvm.handle_vm_timer_irq_local st arI s a0 irq p n ⦃ r => r.1 = true →
        EntryInv st (Heap.tcbs H) Cs (Heap.omega H) H (Heap.frame H) (Heap.replies H) (Heap.scs H) (Heap.ntfns H)
          (Heap.scBits H) Ac r.2.1 ⦄ := by
  obtain ⟨H, Cs, Ac, U, hc, hI, hBA, hz, hO, hIN⟩ :=
    vexitEntI_of_reachU17 arI AR MR hARI hA hnd hM hKD hIo hIoa hPA hIA hT hmax htu hRef hPI hSX hDR hJ
  exact ⟨H, Cs, Ac, hc, hI, fun a0 irq n p htk =>
    vm_timer_local.entryI hA (fun _ hn => hn) s a0 irq n p hI hBA hz hO hIN htk⟩

end

end Fl4Proofs.P2.Stall
