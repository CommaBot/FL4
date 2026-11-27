/-
P3 (line mmuAD, gen 24): **the VT-x step theorems at a VM-epoch joint state `JAtZV`** (any `V`, `X`).

Gens 21–23 derived the layout / placement premises of the VT-x step theorems (`JVLay`, `DetAtB`, `FinPl`, `hnd`,
`hhv`, `hhc`, …) from `JAtZ`. `JAtZ` carries `ext : JExt` (every slot cap native, every TCB VCPU word 0), false in
every state where a VCPU is bound or a Vcpu cap exists, so those derivations only applied to degenerate VM
states. None of them reads `ext`: this module re-states each over `JAtZB` (= `JAtZ` without `ext`, P3/JAtZV), proofs
copied verbatim from P3/BufAtJ, P3/JExtVLay, P3/JExtVFin, P3/JExtVList, P3/JExtVListSteps with `JAtZ` → `JAtZB`
(names `JAtZB.<same name>`: `bufWordG`, `rbufU`, `thTcb`, `bufU_rbuf`, `bufU_B`, `bufU_noSlot`, `thH`, `jvLay`,
`nodePl`, `nodeW`, `tw_nBC`, `bufOK`, `detAtB`, `hnd`, `hhv`, `hhc`, `finPl`, `finPlV`, `jwPl`, `detPl`, `hact`,
`hct`, `thrCap`, `hTt`).

New:
* **`JAtZB.hU`** / **`JAtZ.hU`**: the VCPU list head word is no IPC-buffer word (`P1.vHeadA st s ∉ BufU Z σ`) —
  gen 23's last [J] of `vcpu_finalise_vlJ`. Proof: an IPC-buffer word is a `Z.B` word (`bufU_B`: `IpcBufCapOK` +
  `FrameCover`), `KsApart.buf` puts every `Z.B` word off `[ksb, ksb + 13568)`, and the head word is `ksb + 80`
  (`vHead_val`). **`vcpu_finalise_vlJ'`**: `vcpu_finalise_vlJ` with no premise beyond its state facts.
* At `J : JAtZV V X …` (all placement premises discharged):
  **`JAtZV.finalise`** (`vcpu.finalise v`, `v ∈ V`: `JExtV`, `RunVmB`, `v.TCB = 0`, `VList (V \ {v})`; no premise),
  **`JAtZV.detach`** (`DetPost`; no premise), **`JAtZV.settcb`** (`vcpu.decode … X86VCPUSetTCB`; `hexs` [J]: the
  extra cap slots are slots of the typed heap, a syscall front-end fact, P1 `DecPre.extra`),
  **`JAtZV.enterU`** (unbound thread; no premise), **`JAtZV.enter`** (bound thread, every branch incl. the
  signalled one; `hRt` [J]: the entering thread's state word is not `BlockedR` — a fact of the call site, the
  current thread at kernel exit), **`JAtZV.sts`** (`set_thread_state`).
  These give the extension half (`JExtV`, `RunVmB`, `VList`) of `JAtZV` after each VT-x step from a VM-epoch
  state; the `JAtZB` half after these steps is not proved here (open: needs `xtop.rel` over the extended spec).

Named premises: `hexs` [J], `hRt` [J] (both stated where used). No [P] / [W] / [S]. No existing statement changed.
-/
import Fl4Proofs.P3.JAtZV
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit} {V X : Set U64}

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- **A word of a TCB's IPC buffer at `J`** (for `JAtZ.userWrJ`): apart from
every non-`other` object of `H` (the TCB's IPC-frame slot holds a frame cap,
`StateRel.bufCap`, whose range meets no such object, `JPlaced.cobj`'s
`FrApartH`) and inside a spec object (the frame's data page, `IpcBufCapOK`). -/
theorem JAtZB.bufWordG (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (hOK : Endp.IpcBufCapOK σ) {t : U64}
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

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

set_option maxHeartbeats 8000000 in
/-- The receiver's buffer words at `J` are untracked for P1 (`JAtZ.bufWord`,
`JAtZ`'s `nodeB`). -/
theorem JAtZB.rbufU (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {d : U64}
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

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- A thread of `Z.T` is a TCB of the typed heap. -/
theorem JAtZB.thTcb (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {t : U64} (ht : t ∈ Z.T) :
    Z.th t = some .tcb := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  exact (hJ.tcb t).2 (J.zH.1 t ht)

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

theorem JAtZB.bufU_rbuf {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ BufU Z σ) : P1.OutsideObjs st (P1.Heap.tcbs H) Cs s b ∧
      (∀ e, (H e = some .ep ∨ H e = some .ntfn) → b.val + 8 ≤ e.val ∨ e.val + 16 ≤ b.val) ∧
      b ∉ P1.Heap.frame H := by
  obtain ⟨y, hy, xd, hk, hb'⟩ := hb
  exact J.rbufU hy (J.thTcb hy) hk b hb'

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

theorem JAtZB.bufU_B {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
    {b : U64} (hb : b ∈ BufU Z σ) : ∃ wp ∈ Z.B, wp.1 = b := by
  obtain ⟨y, hy, xd, hk, rp, hrp, i, hi, rfl⟩ := hb
  have hBC := bufCover_of_frameCover (T := Z.T) J.bok J.fcov
  exact ⟨_, hBC y hy xd true rp hk hrp ⟨rp⟩ rfl i hi, rfl⟩

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **No IPC-buffer word in a slot** (`BufPlaced.slot`). -/
theorem JAtZB.bufU_noSlot {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ x, IsSlot Z.th x → ∀ b ∈ BufU Z σ, ¬ (x.val ≤ b.val ∧ b.val < x.val + 32) := by
  intro x hx b hb
  obtain ⟨wp, hwp, e⟩ := J.bufU_B hb
  subst e
  exact BufPlaced.slot J.xtop.fin.1.2 hwp hx

end

section
open fl4_core Classical

/-- A typed-heap object is an `H` object of the same size. -/
theorem JAtZB.thH (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ p k, Z.th p = some k → ∃ hk, H p = some hk ∧ 2 ^ hk.bits = objSize k := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  intro p k hp
  rcases J.thk p k hp with rfl | ⟨r, rfl⟩
  · exact ⟨_, (hJ.tcb p).1 hp, by simp [P1.HKind.bits, objSize]⟩
  · exact ⟨_, hJ.cnode p r hp, by simp only [P1.HKind.bits, objSize]; rw [pow_add]; ring⟩

end

section
open fl4_core Classical

/-- **The layout record at a joint state** (module docstring). -/
theorem JAtZB.jvLay (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    JVLay V Z.th (BufU Z σ) := by
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have hH := J.kern.heap
  have hSR := J.xtop.rel.2.1.1
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hvn : ∀ v ∈ V, Z.th v = none := by
    intro v hv
    obtain ⟨x, hx⟩ := Jv.spec v hv
    cases h : Z.th v with
    | none => rfl
    | some k =>
      exfalso
      rcases J.thk v k h with rfl | ⟨r, rfl⟩
      · obtain ⟨c, hc, -⟩ := hSR.tcb v h
        rw [hc] at hx; cases hx
      · obtain ⟨c, hc, -⟩ := hSR.cnode v r h
        rw [hc] at hx; cases hx
  refine ⟨J.xtop.rel.1, J.thk, fun t ht => J.ip.e.tcb t (J.thT t ht), fun v hv => ?_, fun v hv p k hp => ?_,
    fun v hv w hw hne => ?_, fun b hb => (J.bufU_rbuf hb).1.1, fun b hb y hy => J.bufU_noSlot y hy b hb,
    fun b hb t ht => ?_, fun b hb v hv => ?_⟩
  · have h1 := hH.align v _ (Jv.heap v hv); have h2 := hH.fits v _ (Jv.heap v hv)
    simp only [P1.HKind.bits, h15] at h1 h2; exact ⟨h1, h2⟩
  · obtain ⟨hk, hpk, he⟩ := J.thH p k hp
    have hne : p ≠ v := fun e => by rw [e, hvn v hv] at hp; cases hp
    rcases hH.disj p hk v _ hpk (Jv.heap v hv) hne with e | e
    · left; rw [← he]; exact e
    · right; simpa [P1.HKind.bits, h15] using e
  · rcases hH.disj v _ w _ (Jv.heap v hv) (Jv.heap w hw) hne with e | e <;>
      simp only [P1.HKind.bits, h15] at e
    · exact Or.inl e
    · exact Or.inr e
  · have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
    have := (J.bufU_rbuf hb).1.2.1 t ((hJ.tcb t).1 ht)
    rw [h12] at this; exact this
  · obtain ⟨wp, hwp, rfl⟩ := J.bufU_B hb
    obtain ⟨q, vms, hq, g1, g2⟩ := J.carry.bufPg wp hwp
    obtain ⟨x, hx⟩ := Jv.spec v hv
    have hne : q ≠ v.bv := fun e => by rw [e, hx] at hq; cases hq
    rcases Jv.sep v hv q _ hq hne with e | e
    · left
      have eb : Fl4Spec.objBits (.archObj (.dataPage false vms)) = Fl4Spec.pageBitsForSize vms := by
        simp [Fl4Spec.objBits, Fl4Spec.archKobjSize]
      rw [eb] at e; omega
    · right; omega

end

section
open fl4_core Classical

/-- The current core's node is placed (`JKern`'s `ksbAl` / `nodeFit` / `hnd`). -/
theorem JAtZB.nodePl (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    P1.NodePlaced st (P1.Heap.tcbs H) s (L.cpu s) where
  align := by unfold P1.LawfulStore.nodeBase; have := J.kern.ksbAl; omega
  fits := by unfold P1.LawfulStore.nodeBase; have := J.kern.nodeFit; omega
  disj t ht := by
    have := J.kern.hnd t .tcb ht (L.cpu s) J.kern.cpuCs
    simpa [P1.HKind.bits] using this

end

section
open fl4_core Classical

/-- A word of the current core's node is none of `JW` / `SW`. -/
theorem JAtZB.nodeW (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {b : U64}
    (h1 : L.nodeBase s (L.cpu s) ≤ b.val) (h2 : b.val < L.nodeBase s (L.cpu s) + 4288) :
    ¬ JW V Z.th b ∧ ¬ SW Z.th b := by
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  refine (J.jvLay Jv).nJS (fun p k hp g1 g2 => ?_) (fun v hv => ?_)
  · exfalso
    obtain ⟨hk, hpk, he⟩ := J.thH p k hp
    rcases J.kern.hnd p hk hpk (L.cpu s) J.kern.cpuCs with e | e <;> (try rw [he] at e) <;> omega
  · have := ((J.jvLay Jv).vfit v hv).2
    rcases J.kern.hnd v _ (Jv.heap v hv) (L.cpu s) J.kern.cpuCs with e | e <;>
      (try simp only [P1.HKind.bits, h15] at e) <;> omega

end

section
open fl4_core Classical

/-- A TCB word at an offset outside the register range, other than the VCPU / state words, is no binding word
and no detach word `CW` (what the IPC-buffer lookup's three words need). -/
theorem JAtZB.tw_nBC (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {t : U64}
    (ht : Z.th t = some .tcb) {w : U64} {K : Nat} (hw : w.val = t.val + K) (hK : K < 4096)
    (hK2 : K < 256 ∨ 3328 < K) (hK3 : K ≠ 3664) (hK8 : K % 8 = 0) :
    P1.Aligned w ∧ ¬ (BW V Z.th w ∨ CW st V Z.th (fun _ => BufU Z σ) s w) := by
  have Ly := J.jvLay Jv
  have hta := Ly.tA t ht
  have ha := hta.align
  have dT : ∀ t', Z.th t' = some .tcb → t' ≠ t → t'.val + 4096 ≤ t.val ∨ t.val + 4096 ≤ t'.val := by
    intro t' ht' hne
    have h1 := (Ly.tA t' ht').align
    have : t'.val ≠ t.val := fun e => hne (UScalar.eq_of_val_eq e)
    omega
  have hN := J.nodePl
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  have nodeT := hN.disj t ((hJ.tcb t).1 ht)
  have h12 : (2 : Nat) ^ 12 = 4096 := by norm_num
  rw [h12] at nodeT
  refine ⟨by unfold P1.Aligned; rw [hw]; omega, ?_⟩
  rintro ((⟨t', ht', rfl⟩ | ⟨v, hv, rfl⟩) | (e | e | ⟨t', ht', h | e⟩ | ⟨v, hv, e | e⟩))
  · rw [lay_tVcpu_val (Ly.tA t' ht')] at hw
    by_cases e : t' = t
    · subst e; omega
    · rcases dT t' ht' e with e' | e' <;> omega
  · rw [lay_vTcb_val (Ly.vfit v hv).2] at hw
    rcases Ly.vap v hv t .tcb ht with e | e <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e) <;> omega
  · rw [e] at hw
    have := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
    have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
    unfold ipiA at hw; rw [this] at hw
    rcases nodeT with e' | e' <;> omega
  · rw [e] at hw
    have := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
    unfold actA at hw; rw [this] at hw
    rcases nodeT with e' | e' <;> omega
  · rcases h with ⟨K', g1, g2, g3, rfl⟩ | hb
    · rw [lay_tw_val (Ly.tA t' ht') (by omega)] at hw
      by_cases e : t' = t
      · subst e; omega
      · rcases dT t' ht' e with e' | e' <;> omega
    · rcases Ly.ut w hb t ht with e' | e' <;> omega
  · rw [e, lay_stA_val (Ly.tA t' ht')] at hw
    by_cases e' : t' = t
    · subst e'; omega
    · rcases dT t' ht' e' with e'' | e'' <;> omega
  · rw [e, lay_pend_val (Ly.vfit v hv).2] at hw
    rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega
  · rw [e, lay_svm_val (Ly.vfit v hv).2] at hw
    rcases Ly.vap v hv t .tcb ht with e' | e' <;> (try rw [show objSize ObjKind.tcb = 4096 from rfl] at e') <;> omega

end

section
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched

/-- **Every TCB's receive buffer in `BufU`** (module docstring). -/
theorem JAtZB.bufOK {s : S} {a : A} {σ : Fl4Spec.State Unit} (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ)
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

end

section
open fl4_core Classical

/-- **`DetAtB` at a joint state** (P3/JExtVStepsB): the node placed (`JAtZ.nodePl`), its IPI / action words
outside the extension (`JAtZ.nodeW`), and the buffer lookup kept along binding / `CW` writes (it reads only the
TCB's `IPC_BUFFER` word and buffer-slot words, `P1.lookup_ipc_buffer_same`), landing in `BufU` (`JAtZ.bufOK`). -/
theorem JAtZB.detAtB (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    DetAtB st V Z.th (fun _ => BufU Z σ) s where
  node := ⟨_, J.nodePl⟩
  nd b hb := by
    have hN := J.nodePl
    rcases hb with rfl | rfl
    · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
      have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
      unfold ipiA; exact J.nodeW Jv (by rw [e]; omega) (by rw [e]; omega)
    · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
      have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
      unfold actA; exact J.nodeW Jv (by rw [e]; omega) (by rw [e]; omega)
  buf s1 h t ht := by
    obtain ⟨Tr, Cq, hJ⟩ := J.jpl
    have hta := (J.jvLay Jv).tA t ht
    have e1 : (P1.ibWordA t).val = t.val + 3512 := by
      unfold P1.ibWordA; rw [lay_tw_val hta (by simp)]; simp
    have e2 : (P1.sbWordA t).val = t.val + 64 := by
      rw [P1.sbWordA_eq, lay_tw_val hta (by simp)]; simp
    have e3 : (core.num.U64.wrapping_add (P1.sbWordA t) 8#u64).val = t.val + 72 := by
      rw [P1.sbWordA8_eq, lay_tw_val hta (by simp)]; simp
    have k1 := J.tw_nBC Jv ht e1 (by omega) (by omega) (by omega) (by omega)
    have k2 := J.tw_nBC Jv ht e2 (by omega) (by omega) (by omega) (by omega)
    have k3 := J.tw_nBC Jv ht e3 (by omega) (by omega) (by omega) (by omega)
    have hI : P1.IbSame (L := L) s s1 t := ⟨h.mem_eq k1.1 k1.2, h.mem_eq k2.1 k2.2, h.mem_eq k3.1 k3.2⟩
    rw [P1.lookup_ipc_buffer_same hI]
    exact J.bufOK ((hJ.tcb t).1 ht)

end

section
open fl4_core Classical Fl4Proofs.P0.Consts

/-- The current core's node words lie outside every VCPU of `V` (as in `JAtZ.finPl`). -/
theorem JAtZB.hnd (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    ∀ b, (b = ipiA st s ∨ b = actA st s) → ∀ w ∈ V, b.val < w.val ∨ w.val + 32768 ≤ b.val := by
  intro b hb w hw
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hN := J.nodePl
  have hb' : L.nodeBase s (L.cpu s) ≤ b.val ∧ b.val < L.nodeBase s (L.cpu s) + 4288 := by
    rcases hb with rfl | rfl
    · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
      have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
      unfold ipiA; rw [e]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
      have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
      unfold actA; rw [e]; omega
  rcases J.kern.hnd w _ (Jv.heap w hw) (L.cpu s) J.kern.cpuCs with e | e <;>
    (try simp only [P1.HKind.bits, h15] at e) <;> omega

end

section
open fl4_core Classical Fl4Proofs.P0.Consts

/-- The head word lies in no VCPU of `V` (`JVm.ks`: VCPUs off the kernel-global area). -/
theorem JAtZB.hhv (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    ∀ w ∈ V, (P1.vHeadA st s).val < w.val ∨ w.val + 32768 ≤ (P1.vHeadA st s).val := by
  intro w hw
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  rcases Jv.ks w hw with e | e <;> omega

end

section
open fl4_core Classical Fl4Proofs.P0.Consts

/-- **`hhc` at a joint state** from the one missing fact `hU` [J] (no IPC-buffer word is the head word): the
node words (`JKern.nodeFit` / base), the TCB words (`JKern.hks`: TCBs off the kernel-global area), the state words
(`VList.hd`) and the VCPU words (`JVm.ks`) are no head word. -/
theorem JAtZB.hhc (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    (Vl : VList st V Z.th s) (hU : P1.vHeadA st s ∉ BufU Z σ) :
    ¬ CW st V Z.th (fun _ => BufU Z σ) s (P1.vHeadA st s) := by
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  have hN := J.nodePl
  have hnb : L.nodeBase s (L.cpu s) = (L.ksb s).val + 13568 + (L.cpu s).val * 4288 := rfl
  rintro (e | e | ⟨t, ht, hr | e⟩ | ⟨w, hw, e | e⟩)
  · have n1 := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
    have n2 := congrArg UScalar.val e
    unfold ipiA at n2
    omega
  · have n1 := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
    have n2 := congrArg UScalar.val e
    unfold actA at n2
    omega
  · rcases hr with ⟨K, k1, k2, k3, e⟩ | hu
    · have Ly := J.jvLay Jv
      have e1 := congrArg UScalar.val e
      rw [lay_tw_val (Ly.tA t ht) (K := K) (by omega)] at e1
      have hT := J.kern.hks t .tcb (J.zH.1 t (J.thT t ht)) (fun _ h => by cases h)
      simp only [P1.HKind.bits, Nat.reducePow] at hT
      omega
    · exact hU hu
  · exact Vl.hd.2.2 ⟨t, ht, e⟩
  · have e1 := congrArg UScalar.val e
    rw [lay_pend_val ((J.jvLay Jv).vfit w hw).2] at e1
    rcases Jv.ks w hw with h | h <;> omega
  · have e1 := congrArg UScalar.val e
    rw [lay_svm_val ((J.jvLay Jv).vfit w hw).2] at e1
    rcases Jv.ks w hw with h | h <;> omega

end

section
open fl4_core Classical

/-- **`FinPl` at a joint state** (module docstring): `hnd` from `JKern.hnd` + `JVm.heap`; `hL`, `hP`, `hhd` [J]. -/
theorem JAtZB.finPl (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) {v : U64}
    (hv : v ∈ V) (hL : ∀ w, P1.VListed st s w ↔ w ∈ V)
    (hP : ∀ w ∈ V, L.mem s (vPrevA w) ≠ 0#u64 → L.mem s (vPrevA w) ∈ V)
    (hhd : P1.Aligned (P1.vHeadA st s) ∧ ¬ JW V Z.th (P1.vHeadA st s) ∧ ¬ SW Z.th (P1.vHeadA st s)) :
    FinPl st V Z.th (fun _ => BufU Z σ) s v := by
  refine (J.jvLay Jv).finPl hv hL hP hhd fun b hb w hw => ?_
  have h15 : (2 : Nat) ^ 15 = 32768 := by norm_num
  have hN := J.nodePl
  have hb' : L.nodeBase s (L.cpu s) ≤ b.val ∧ b.val < L.nodeBase s (L.cpu s) + 4288 := by
    rcases hb with rfl | rfl
    · have e := P1.nodeAt_val hN (off := layout.node.IPI_PENDING) (by simp [layout.node.IPI_PENDING])
      have h4 : layout.node.IPI_PENDING.val < 4288 := by simp [layout.node.IPI_PENDING]
      unfold ipiA; rw [e]; omega
    · have e := P1.nodeAt_val hN (off := layout.node.SCHED_ACTION) (by simp [layout.node.SCHED_ACTION])
      have h4 : layout.node.SCHED_ACTION.val < 4288 := by simp [layout.node.SCHED_ACTION]
      unfold actA; rw [e]; omega
  rcases J.kern.hnd w _ (Jv.heap w hw) (L.cpu s) J.kern.cpuCs with e | e <;>
    (try simp only [P1.HKind.bits, h15] at e) <;> omega

end

section
open fl4_core Classical

/-- **`JAtZ.finPl` over `VList`**: no list [J] left. -/
theorem JAtZB.finPlV (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ)
    (Vl : VList st V Z.th s) {v : U64} (hv : v ∈ V) : FinPl st V Z.th (fun _ => BufU Z σ) s v :=
  J.finPl Jv hv Vl.hL Vl.hP Vl.hd

end

section
open fl4_core Classical

/-- **`JWPl` at a joint state.** -/
theorem JAtZB.jwPl (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    JWPl V Z.th := (J.jvLay Jv).jwPl

end

section
open fl4_core Classical

/-- **`DetPl` at a joint state**, at the IPC-buffer words `BufU Z σ`. -/
theorem JAtZB.detPl (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    DetPl V Z.th (fun _ => BufU Z σ) := (J.jvLay Jv).detPl

end

section
open fl4_core Classical

/-- `sts_jv`'s `hact` at a joint state. -/
theorem JAtZB.hact (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) (Jv : JVm (L := L) V H s σ) :
    P1.Aligned (actA st s) ∧ ¬ JW V Z.th (actA st s) ∧ ¬ SW Z.th (actA st s) :=
  ⟨(J.detAtB Jv).actA_al, ((J.detAtB Jv).nd _ (Or.inr rfl)).1, ((J.detAtB Jv).nd _ (Or.inr rfl)).2⟩

end

section
open fl4_core Classical

/-- `vcpu_decode_settcb_jv`'s `hct` at a joint state (`JKern.curT`). -/
theorem JAtZB.hct (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) : Z.th (L.mem s (curA st s)) = some .tcb :=
  J.kern.curT

end

section
open fl4_core Classical

/-- The `Thread` half of `hex` at a joint state: a slot's `Thread` cap names a TCB (`SlotsValid`). -/
theorem JAtZB.thrCap (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) {x : U64} (hx : IsSlot Z.th x) :
    ∀ p, capV (L.mem s) x = .Thread p → Z.th p = some .tcb := by
  intro p hp
  have hV := J.xtop.rel.2.1.2.1
  obtain ⟨q, i, hi, rfl⟩ := hx
  have hc : CapValid Z.th (capV (L.mem s) (slotOf q i)) := by
    rcases hi with ⟨r, hq, hi⟩ | ⟨hq, hi⟩
    · exact hV.cnode q r hq i hi _ (capAt_capV _ _)
    · exact hV.tcb q hq i hi _ (capAt_capV _ _)
  rw [hp] at hc; exact hc

end

section
open fl4_core Classical

theorem JAtZB.hTt (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) :
    ∀ y, Z.th y = some .tcb → y ∈ P1.Heap.tcbs H := fun y hy => J.zH.1 y (J.thT y hy)

end

section
open fl4_core Classical

/-- **The head word is no IPC-buffer word** (module docstring; gen 23's `hU` [J], discharged). -/
theorem JAtZB.hU (J : JAtZB (L := L) arI AR Z H Cs Ac Lst D s a σ) : P1.vHeadA st s ∉ BufU Z σ := by
  intro hu
  obtain ⟨wp, hwp, he⟩ := J.bufU_B hu
  have hv : (P1.vHeadA st s).val = (L.ksb s).val + 80 := vHead_val J.kern.ksbFit
  have hb := J.ks.buf wp hwp
  rw [he, hv] at hb
  omega

/-- `JAtZB.hU` at a native joint state. -/
theorem JAtZ.hU (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) : P1.vHeadA st s ∉ BufU Z σ := J.toB.hU

/-- **`vcpu_finalise_vlJ` without `hU`.** -/
theorem vcpu_finalise_vlJ' {ar : machine.Arch A} (hA : P0.ArchTotal ar) (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ)
    (Jv : JVm (L := L) V H s σ) (E : JExtV (L := L) V X Z.th s) (R : RunVmB (L := L) Z.th s)
    (Vl : VList st V Z.th s) (a' : A) {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) Z.th r.1 ⦄ :=
  vcpu_finalise_vlJ hA J Jv E R Vl J.hU a' hvV

variable {ar : machine.Arch A}

/-- **`vcpu.finalise` at a VM-epoch joint state** (no premise). -/
theorem JAtZV.finalise (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {v : U64} (hvV : v ∈ V) :
    vcpu.finalise st ar s a' v ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ∧
      L.mem r.1 (vTcbA v) = 0#u64 ∧ VList st (V \ {v}) Z.th r.1 ⦄ :=
  vcpu_finalise_vl hA (J.base.jvLay J.vm) (J.base.detAtB J.vm) J.extv J.rvm J.vl (J.base.hnd J.vm)
    (J.base.hhv J.vm) (J.base.hhc J.vm J.vl J.base.hU) a' hvV

/-- **`vcpu.detach` at a VM-epoch joint state** (no premise). -/
theorem JAtZV.detach (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) :
    vcpu.detach st ar s a' t ⦃ r => DetPost st V X Z.th (fun _ => BufU Z σ) t s r.1 ⦄ :=
  vcpu_detach_jvB hA (J.base.detPl J.vm) (J.base.detAtB J.vm) J.extv J.rvm a' ht

/-- **`X86VCPUSetTCB` at a VM-epoch joint state**; `hexs` [J]: every nonzero extra cap slot is a slot of the typed
heap (the syscall front end's `lookup_extra_caps`, P1 `DecPre.extra`). -/
theorem JAtZV.settcb (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {len v buf : U64} {call : Bool} {extra : Aeneas.Std.Array obj.Slot 3#usize} (hvV : v ∈ V)
    (hexs : ∀ x ∈ extra.val, x ≠ 0#u64 → IsSlot Z.th x) :
    vcpu.decode st ar s a' fl4_abi.label.X86VCPUSetTCB len v call buf extra ⦃ r s' _ =>
      JExtV (L := L) V X Z.th s' ∧ RunVmB (L := L) Z.th s' ⦄ :=
  vcpu_decode_settcb_jvB hA (J.base.detPl J.vm) (J.base.detAtB J.vm) J.extv J.rvm a' hvV
    (fun x hx h0 => ⟨hexs x hx h0, J.base.thrCap (hexs x hx h0)⟩) J.base.hct

/-- **`vcpu.enter` of an unbound thread at a VM-epoch joint state** (no premise). -/
theorem JAtZV.enterU (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) (h0 : L.mem s (tVcpuA t) = 0#u64) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ :=
  vcpu_enter_unbound hA (J.base.detPl J.vm) J.extv J.rvm a' ht h0

set_option maxHeartbeats 4000000 in
/-- **`vcpu.enter` of a bound thread at a VM-epoch joint state** (every branch, the signalled one included);
`hRt` [J]: the entering thread's state word is not `BlockedR` (the call site's fact: `vcpu::enter` runs for the
current thread at kernel exit). -/
theorem JAtZV.enter (hA : P0.ArchTotal ar) (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) (a' : A)
    {t : U64} (ht : Z.th t = some .tcb) (hv0 : L.mem s (tVcpuA t) ≠ 0#u64)
    (hRt : ¬ P1.BlockedR (L.mem s (P1.stA t))) :
    vcpu.enter st ar s a' t ⦃ r => JExtV (L := L) V X Z.th r.1 ∧ RunVmB (L := L) Z.th r.1 ⦄ := by
  obtain ⟨_, _, hJ⟩ := J.base.jpl
  exact vcpu_enter_boundL hA (J.base.jvLay J.vm) (J.base.detAtB J.vm) J.extv J.rvm a' ht hv0 J.base.blk
    J.base.kern.heap J.vm.heap J.base.hTt (hJ.slotCapW (Sched.tLowSlots_all _)) hRt

/-- **`set_thread_state` at a VM-epoch joint state** (`sts_jv`; to `TS_RUNNING_VM` only for a bound thread). -/
theorem JAtZV.sts (J : JAtZV (L := L) arI V X AR Z H Cs Ac Lst D s a σ) {t x : U64} (ht : Z.th t = some .tcb)
    (hx : x ≠ 8#u64 ∨ L.mem s (tVcpuA t) ≠ 0#u64) :
    sched.set_thread_state st s t x ⦃ s' => JExtV (L := L) V X Z.th s' ∧ RunVmB (L := L) Z.th s' ⦄ :=
  sts_jv (J.base.jwPl J.vm) J.extv J.rvm ht (J.base.hact J.vm) hx

end

end

end

end Fl4Proofs.P3
