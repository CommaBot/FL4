/-
P3 (int6, route A): **BufAtJ at `JAtZR`** (scripted copies, as
XTopJointJAtZRA: `JAtZ` -> `JAtZR`, the proofs the originals'; none reads
`cur`): `JAtZR.thTcb`, `JAtZR.bufWordG`, `JAtZR.rbufU`, `JAtZR.bufU_B`,
`JAtZR.bufU_rbuf`, `JAtZR.bufOK`, `JAtZR.usrWJ`, `JAtZR.bufAtJ`,
`JAtZR.bufU_noSlot`. No premise.
-/
import Fl4Proofs.P3.BufAtJ
import Fl4Proofs.P3.XTopJointJAtZR
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}

/-- A thread of `Z.T` is a TCB of the typed heap. -/
theorem JAtZR.thTcb (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    Z.th t = some .tcb := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact (hJ.tcb t).2 (J.zH.1 t ht)

set_option maxHeartbeats 8000000 in
/-- **A word of a TCB's IPC buffer at `J`** (for `JAtZR.userWrJ`): apart from
every non-`other` object of `H` (the TCB's IPC-frame slot holds a frame cap,
`StateRel.bufCap`, whose range meets no such object, `JPlaced.cobj`'s
`FrApartH`) and inside a spec object (the frame's data page, `IpcBufCapOK`). -/
theorem JAtZR.bufWordG (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) (hOK : Endp.IpcBufCapOK σ) {t : U64}
    (ht : Z.th t = some .tcb) {x : Fl4Spec.Tcb} (hk : σ.kheap t.bv = some (.tcb x)) {q : Fl4Spec.ObjRef}
    {isR : Bool} (hq : Endp.ipcBufOf isR x = some q) (k : Nat) (hk128 : k < 128) {b : U64}
    (hb : b.bv = Endp.bufAddr q k) :
    (∀ p k', H p = some k' → (∀ z, k' ≠ .other z) → b.val + 8 ≤ p.val ∨ p.val + 2 ^ k'.bits ≤ b.val) ∧
      ∃ o ko, σ.kheap o = some ko ∧ o.toNat ≤ b.val ∧ b.val < o.toNat + 2 ^ Fl4Spec.objBits ko := by
  have hbv : b.val = (Endp.bufAddr q k).toNat := by rw [← hb]; rfl
  unfold Endp.ipcBufOf at hq
  split at hq
  · rename_i dev pb R mt vms md he
    split_ifs at hq with hc
    cases hq
    have hro : Fl4Spec.vmReadOnly ⊆ R := by
      rcases hc with h | ⟨h, -⟩
      · exact fun z hz => h (by unfold Fl4Spec.vmReadOnly Fl4Spec.vmReadWrite at *; simp at hz ⊢; simp [hz])
      · exact h
    obtain ⟨-, -, hd, ha, hpa⟩ := hOK t.bv x hk dev pb R mt vms md he hro
    obtain ⟨r1, r2, r3⟩ := buf_frame_rng vms pb x.tcbIpcBuffer k hk128 hpa ha
    rw [← hbv] at r1 r2
    refine ⟨?_, ?_⟩
    swap
    · obtain ⟨sz', hsz'⟩ := hd k hk128
      have hn := Endp.and_not_mask_toNat (Endp.bufAddr (pb + (x.tcbIpcBuffer &&&
        Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k) _ (Endp.pageBits_mem sz')
      have hpos : 0 < 2 ^ Fl4Spec.pageBitsForSize sz' := by positivity
      have hlo := Nat.div_mul_le_self (Endp.bufAddr (pb + (x.tcbIpcBuffer &&&
        Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat (2 ^ Fl4Spec.pageBitsForSize sz')
      have hhi := Nat.lt_div_mul_add (a := (Endp.bufAddr (pb + (x.tcbIpcBuffer &&&
        Fl4Spec.mask (Fl4Spec.pageBitsForSize vms))) k).toNat) hpos
      refine ⟨_, _, hsz', ?_, ?_⟩
      · rw [hn, hbv]; exact hlo
      · show b.val < _ + 2 ^ Fl4Spec.pageBitsForSize sz'
        rw [hn, hbv]; exact hhi
    intro p k' hp hk'
    obtain ⟨x', c, hkx, hcap, hcr⟩ := J.xtop.rel.2.1.1.bufCap ht
    rw [hk] at hkx; cases hkx
    rw [he] at hcr
    obtain ⟨-, h2⟩ := hcr
    cases c <;> try (simp [absCap] at h2; done)
    case Frame p0 sz r0 d0 m0 ep0 as0 va0 =>
      simp only [absCap] at h2
      injection h2 with h2
      injection h2 with _ hp0 _ _ hsz _
      have hsl : IsSlot Z.th (slotOf t 2) := ⟨t, 2, Or.inr ⟨ht, by simp [tcbSlots]⟩, rfl⟩
      obtain ⟨Tr, Cq, hJ⟩ := J.jpl
      have hcv : capV (L.mem s) (slotOf t 2) = .Frame p0 sz r0 d0 m0 ep0 as0 va0 := capV_of_capAt hcap
      have hFA : Sched.FrApartH H (.Frame p0 sz r0 d0 m0 ep0 as0 va0) := by
        have := hJ.cobj _ hsl; rw [hcv] at this; exact this
      obtain ⟨bs, ts⟩ := frame_range p0 sz r0 d0 m0 as0 va0 ep0
      have hm := Endp.pageBits_mem vms
      have hbits : (fbitsF sz).val = Fl4Spec.pageBitsForSize vms := by rw [fbitsF_val, hsz]
      have hmk : (maskF (fbitsF sz)).val = 2 ^ Fl4Spec.pageBitsForSize vms - 1 := by
        rw [maskF_val (by rw [hbits]; simp at hm; omega), hbits]
      have hpv : p0.val = pb.toNat := by rw [← hp0]; rfl
      have hpos : 0 < 2 ^ Fl4Spec.pageBitsForSize vms := by positivity
      have htop : topF (.Frame p0 sz r0 d0 m0 ep0 as0 va0) = p0.val + 2 ^ Fl4Spec.pageBitsForSize vms - 1 := by
        rw [ts]
        simp [core.num.U64.wrapping_add_val_eq, U64.size_def, UScalarTy.U64_numBits_eq, U64.numBits, hmk]
        omega
      rcases hFA p k' hp hk' with e | e
      · rw [bs] at e; right; omega
      · rw [htop] at e; left; omega
  · cases hq

set_option maxHeartbeats 8000000 in
/-- The receiver's buffer words at `J` are untracked for P1 (`JAtZR.bufWord`,
`JAtZR`'s `nodeB`). -/
theorem JAtZR.rbufU (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) {d : U64}
    (hdT : d ∈ Z.T) (hdth : Z.th d = some .tcb) {xd : Fl4Spec.Tcb} (hkd : σ.kheap d.bv = some (.tcb xd)) :
    ∀ b, RcvBufW xd b → P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b ∧
      (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧ b ∉ P1.Heap.frame H := by
  rintro b ⟨rp, hrp, i, hi, rfl⟩
  have hOK := J.bok
  have hBC := bufCover_of_frameCover (T := Z.T) J.bok J.fcov
  have hwB := hBC d hdT xd true rp hkd hrp ⟨rp⟩ rfl i hi
  have hal := (J.xtop.fin.1.2.ep.balign _ hwB).1
  obtain ⟨hAp, -⟩ := J.bufWordG hOK hdth hkd hrp i.val hi (b := Endp.fl4BufA ⟨rp⟩ i) (by rw [fl4BufA_bv])
  refine ⟨⟨hal, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, fun hf => ?_⟩
  · rcases hAp t .tcb ht (fun _ e => by cases e) with e | e
    · left; omega
    · right; simpa [P1.HKind.bits] using e
  · have e := J.nodeB _ hwB c (J.kern.csLt c hc)
    dsimp only at e
    rcases e with e | e <;> omega
  · rcases he with he | he
    · rcases hAp e _ he (fun _ e => by cases e) with e | e
      · left; omega
      · right; simp only [P1.HKind.bits] at e; omega
    · rcases hAp e _ he (fun _ e => by cases e) with e | e
      · left; omega
      · right; simp only [P1.HKind.bits] at e; omega
  · obtain ⟨-, p, k, hp, hk, hin⟩ := hf
    have hko : ∀ z, k ≠ .other z := by
      rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩ <;> intro z e <;> cases e
    obtain ⟨g1, g2⟩ := hin
    rcases hAp p k hp hko with e | e <;> omega

theorem JAtZR.bufU_B {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ BufU Z σ) : ∃ wp ∈ Z.B, wp.1 = b := by
  obtain ⟨y, hy, xd, hk, rp, hrp, i, hi, rfl⟩ := hb
  have hBC := bufCover_of_frameCover (T := Z.T) J.bok J.fcov
  exact ⟨_, hBC y hy xd true rp hk hrp ⟨rp⟩ rfl i hi, rfl⟩

theorem JAtZR.bufU_rbuf {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ BufU Z σ) : P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b ∧
      (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧
      b ∉ P1.Heap.frame H := by
  obtain ⟨y, hy, xd, hk, hb'⟩ := hb
  exact J.rbufU hy (J.thTcb hy) hk b hb'

/-- **Every TCB's receive buffer in `BufU`** (module docstring). -/
theorem JAtZR.bufOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {y : U64} (hy : y ∈ P1.Heap.tcbs H) :
    msg.lookup_ipc_buffer st s true y ⦃ w => P1.BufOK (BufU Z σ) w ⦄ := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hth : Z.th y = some .tcb := (hJ.tcb y).2 hy
  have hyT := J.thT y hth
  obtain ⟨xd, hk, hws⟩ := J.buf y hyT
  refine WP.spec_mono (lookup_buf_full s σ J.xtop.rel.2.1.1 J.xtop.rel.2.1.2.1 hth hk J.bok true) ?_
  rintro w ⟨h0, hp⟩ hw0 i hi
  cases hb : Endp.ipcBufOf true xd with
  | none => exact absurd (h0.2 hb) hw0
  | some p' =>
    have e := hp hws p' hb
    subst e
    exact ⟨y, hyT, xd, hk, _, hb, i, hi, rfl⟩

/-- **An IPC-buffer word is a user word** (`P1.UsrW`, int6): outside the
TCBs and nodes, the endpoints and notifications and the frame words
(`JAtZR.bufU_rbuf`), off the kernel-state block (`KsApart.buf`), in no SC. -/
theorem JAtZR.usrWJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ BufU Z σ) :
    P1.UsrW st (P1.Heap.tcbs H) Cs H (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) s b := by
  obtain ⟨ho, he, hf⟩ := J.bufU_rbuf hb
  refine ⟨ho, he, hf, fun o h1 h2 e => ?_, fun c hc hin => ?_⟩
  · obtain ⟨wp, hwp, e'⟩ := J.bufU_B hb
    have h0 := J.ks.buf wp hwp
    have hv : (core.num.U64.wrapping_add (L.ksb s) o).val = (L.ksb s).val + o.val := by
      have := J.kern.ksbFit
      simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
    rw [e', ← e, hv] at h0; omega
  · obtain ⟨z, hz⟩ := hc
    have hz' : P1.Heap.scBits H c = z := by simp [P1.Heap.scBits, hz]
    rw [hz'] at hin
    exact hf ⟨ho.1, c, .sc z, hz, Or.inr (Or.inl ⟨z, rfl⟩), hin⟩

/-- **The int6 core's placement carrier at `J`** (`P1.BufAt`): the IPC-buffer
words `BufU Z σ` are user words and every TCB's buffer is among them. -/
theorem JAtZR.bufAtJ {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.BufAt st (P1.Heap.tcbs H) Cs H (P1.Heap.frame H) (P1.Heap.scs H) (P1.Heap.scBits H) (BufU Z σ) s :=
  ⟨fun _ hb => J.usrWJ hb, fun _ hy => J.bufOK hy⟩

/-- **No IPC-buffer word in a slot** (`BufPlaced.slot`). -/
theorem JAtZR.bufU_noSlot {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZR (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ x, IsSlot Z.th x → ∀ b ∈ BufU Z σ, ¬ (x.val ≤ b.val ∧ b.val < x.val + 32) := by
  intro x hx b hb
  obtain ⟨wp, hwp, e⟩ := J.bufU_B hb
  subst e
  exact BufPlaced.slot J.xtop.fin.1.2 hwp hx

end

end

end Fl4Proofs.P3
