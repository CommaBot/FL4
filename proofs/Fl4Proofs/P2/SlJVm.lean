/-
# P2 (line slhuf, gen 3): the VM ReplyRecv local path with the bundle `SlJAt` in its `Pre`

`rr_localPath` (P2/AccessVmLP.lean) has `Pre = VmRRPre`, which asks, besides `VmRPre`'s other
fields and `RdTab`, three facts about fl4-sync's `found = (rptr, ep)`: `rptr ∈ Rp` [P],
`H ep = some .ep` [P] and `VmRPre.hEp` [P] (`K.heap ep = some .ep`). This file adds the variant
`rr_localPathJ` beside it, at `H = K.heap`, `Rp = Heap.replies K.heap`, with

  `VmRRPreJ s := SlJAt K s ∧ (K.heap ep = some .ep → VmRPre … s) ∧ RdTab … s ∧ VmFoundC s`

where `VmFoundC` [P] is `P1.rr_vm_local_same`'s `hfd`, word for word (fl4-sync's contract:
`found` is what `reply_caps` returns for the current thread at the entry state). The three
found-object facts are derived (`SlJAt.vmFound`, gen 2): `VmRRPreJ.pre : VmRRPreJ s → VmRRPre … s`.

* `vmFoundC_wr`: `VmFoundC` is kept by a user-word write at a bundle state
  (`SlJAt.curW_wr`, `SlJAt.replyCaps_wr`, P2/SlJQ.lean).
* `rr_pathOblJ`, `rr_pathSideJ`, `rr_readOnceJ`: `rr_pathObl` / `rr_pathSide` / `rr_readOnce`
  (P2/AccessVmRRO.lean) at `Pre = VmRRPreJ`, by the same proofs through `VmRRPreJ.pre`. They are
  restated rather than derived because the old statements quantify their premises (`hmA`,
  `huf`, `hro`) over every `VmRRPre` state.
* `rr_localPathJ`: the local path.

## Premises of `rr_localPathJ`
As `rr_localPath`, with `hmA` / `hpz` (`hro` [W]) quantified over `VmRRPreJ` states, and with
`huf` [J] replaced by `hufR` [J]: at a `VmRRPreJ` state a user-word write keeps the `VmRPre`
part and `RdTab`, the locks, `IoRS`, `IoWS`, `IoDS`. Neither `SlJAt` (`SlJAt.userWr`) nor
`VmFoundC` (`vmFoundC_wr`) is part of it. `VmFoundC` [P] is fl4-sync's contract, in `Pre`.
-/
import Fl4Proofs.P2.SlJQ
import Fl4Proofs.P2.AccessVmLP
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- [P] **fl4-sync's `found` contract of the VM ReplyRecv local path** (`P1.rr_vm_local_same`'s
`hfd`, verbatim: crates/fl4-sync/src/lib.rs `local_syscall` passes `reply_caps`'s result). -/
def VmFoundC (rptr ep : U64) (s : S) : Prop :=
  ∀ t, sched.cur_thread st s = ok t → fastpath.reply_caps st s t = ok (some (rptr, ep))

/-- **`VmFoundC` is kept by a user-word write** at a bundle state. -/
theorem vmFoundC_wr {K : KLayout} {s : S} (hJ : SlJAt (L := L) K s) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) {rptr ep : U64} (hf : VmFoundC st rptr ep s) :
    VmFoundC st rptr ep (L.wr s b v) := by
  intro t et
  rw [cur_thread_ok, hJ.curW_wr hb hba v] at et
  obtain rfl := ok_inj_ff et
  exact hJ.replyCaps_wr hb hba v (hf _ (cur_thread_ok (L := L) s))

variable {A : Type}

variable (st) in
/-- **The VM ReplyRecv entry facts with the bundle** (module docstring), at `H = K.heap`,
`Rp = Heap.replies K.heap`. -/
def VmRRPreJ (ar : machine.Arch A) (K : KLayout) (T Cs Ω Sg Scs Nt : Set U64) (Z : U64 → Nat)
    (Ac : Set U64) (Locks : S → U64 → Prop) (rptr ep : U64) (s : S) : Prop :=
  SlJAt (L := L) K s ∧
    (K.heap ep = some .ep → VmRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks s rptr ep) ∧
    RdTab (L := L) (IoRS (st := st) K Locks s) s ∧ VmFoundC st rptr ep s

/-- **`VmRRPre` from `VmRRPreJ`**: `rptr ∈ Rp`, `H ep = some .ep`, `VmRPre.hEp` by
`SlJAt.vmFound`. -/
theorem VmRRPreJ.pre {ar : machine.Arch A} {K : KLayout} {T Cs Ω Sg Scs Nt : Set U64} {Z : U64 → Nat}
    {Ac : Set U64} {Locks : S → U64 → Prop} {rptr ep : U64} {s : S}
    (h : VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s) :
    VmRRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks rptr ep s := by
  obtain ⟨hJ, hV, hT, hf⟩ := h
  have hfo := hJ.vmFound hf
  exact ⟨hV hfo.2, hfo.1, hfo.2, hT⟩

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Scs Nt Ac : Set U64} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`PathObl` for the VM ReplyRecv local path at `Pre = VmRRPreJ`** (`rr_pathObl`'s proof). -/
theorem rr_pathOblJ (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {rptr ep : U64}
    (hmA : ∀ s, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep)) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE' h hb
    have hE := VmRRPreJ.pre hE'
    subst hb
    exact rr_vm_acc hA hE.1 hE.2.2.2 h
  · intro s a r hE' h hn s' r' Al h'
    exact rr_dec_alt hA hK hLA (VmRRPreJ.pre hE') h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE' hx _
    have hE := VmRRPreJ.pre hE'
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact (hE.1.base.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE' hx
    have hE := VmRRPreJ.pre hE'
    rcases hx with hx | hx
    · exact hx.1
    · exact (hE.1.base.dsSafe hx).1
  · rintro s a ⟨b, s1, a1⟩ hE' h
    have hE := VmRRPreJ.pre hE'
    cases b
    · exact (rr_dec_alt hA hK hLA hE h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact rr_move hA hK hU hE.1 hE.2.2.2 (hmA s hE') hp h

/-- **`PathSide` for the VM ReplyRecv local path at `Pre = VmRRPreJ`** (`rr_pathSide`'s proof;
`user_free` from `hufR` [J], `SlJAt.userWr` and `vmFoundC_wr`). -/
theorem rr_pathSideJ (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {rptr ep : U64}
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hufR : ∀ s b v, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      ((K.heap ep = some .ep →
          VmRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks (L.wr s b v) rptr ep) ∧
        RdTab (L := L) (IoRS (st := st) K Locks (L.wr s b v)) (L.wr s b v)) ∧
      Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep))
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1, fun x hx => ?_, ?_⟩
  · intro s s' a r hE' Al h
    have hE := VmRRPreJ.pre hE'
    obtain ⟨⟨b0, z0, c0⟩, h0⟩ := rr_total (st := st) hA (rptr, ep) s a
    cases b0
    · have hn := (rr_dec_alt (m0 := m0) hA hK hLA hE h0 Bool.false_ne_true Al h).1
      have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
      have hg := rr_dec_tr hA hE G
        (R'' := fun b => IoRS (st := st) K Locks s b ∨ RrRep st rptr s b) (fun b hb => Or.inl hb)
        (fun b hb => Or.inr hb) h hn
      show syscall.handle_reply_recv_vm_local _ ar s' a (rptr, ep) = ok r
      rw [hp] at hg ⊢
      refine interp_mono (fun q hq => ?_) (fun _ _ => trivial) p hz s' a r hg
      rcases hq with hq | hq
      · exact hq.1
      · exact RrRep.aligned hE.1.base hE.2.1 hq
    · have hacc := rr_vm_acc (Locks := Locks) hA hE.1 hE.2.2.2 h0
      rw [hp] at hacc
      obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true z0 c0
        Al.ksb Al.cpu Al.masks Al.read hacc
      have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        rfl rfl rfl p hz s' a _ hg'
      show syscall.handle_reply_recv_vm_local _ ar s' a (rptr, ep) = ok r
      rw [hp] at h ⊢
      rw [hs] at h
      rw [← h]
      exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a _ hg'
  · by_contra hn
    exact hx (ko_unaligned hK hLA hn)
  · intro s b v hE hb hba
    have h := hufR s b v hE hb hba
    exact ⟨⟨hE.1.userWr hb v, h.1.1, h.1.2, vmFoundC_wr hE.1 hb hba v hE.2.2.2⟩, h.2⟩

/-- **`ReadOnce` for the VM ReplyRecv local path at `Pre = VmRRPreJ`** (`rr_readOnce`'s proof;
`hro` [W] over `VmRRPreJ` states). -/
theorem rr_readOnceJ (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {rptr ep : U64}
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hro : ∀ s s' a r, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)
      (VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep) (IoRS (st := st) K Locks) := by
  intro s s' a r hE' Al h
  have hE := VmRRPreJ.pre hE'
  have hU : ∀ q, IoRS (st := st) K Locks s q → ¬ q ∈ K.user := fun q hq => hq.2.1
  obtain ⟨⟨b0, z0, c0⟩, h0⟩ := rr_total (st := st) hA (rptr, ep) s a
  cases b0
  · by_cases hrem : ∃ b, RrRep st rptr s b
    · exact hro s s' a r hE' hrem Al h
    · have h' : syscall.handle_reply_recv_vm_local st ar s' a (rptr, ep) = ok r := by rw [hp]; exact h
      have hn := (rr_dec_alt (m0 := m0) hA hK hLA hE h0 Bool.false_ne_true Al h').1
      have G : Ag st (IoRS (st := st) K Locks s) s s' := ⟨Al.ksb, Al.cpu, Al.read⟩
      have hg := rr_dec_tr hA hE G (R'' := IoRS (st := st) K Locks s) (fun b hb => hb)
        (fun b hb => (hrem ⟨b, hb⟩).elim) h' hn
      rw [hp] at hg
      exact once_of_guard hU p hz ∅ ∅ s' a r hg
  · have hacc := rr_vm_acc (Locks := Locks) hA hE.1 hE.2.2.2 h0
    rw [hp] at hacc
    obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true z0 c0
      Al.ksb Al.cpu Al.masks Al.read hacc
    exact once_of_guard hU p hz ∅ ∅ s' a _ hg'

end

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Scs Nt Ac : Set U64} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} (ar : machine.Arch A)

/-- **The VM ReplyRecv local path with the bundle in its `Pre`** (module docstring):
`rr_localPath` at `Pre = VmRRPreJ`; `rptr ∈ Rp`, `H ep = some .ep`, `VmRPre.hEp` derived from
`SlJAt` and fl4-sync's contract `VmFoundC` [P]; `huf` replaced by `hufR` [J]. -/
noncomputable def rr_localPathJ (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st)
    (hmA : ∀ s, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (hufR : ∀ s b v, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      ((K.heap ep = some .ep →
          VmRPre st ar K T Cs Ω K.heap Sg (Heap.replies K.heap) Scs Nt Z Ac Locks (L.wr s b v) rptr ep) ∧
        RdTab (L := L) (IoRS (st := st) K Locks (L.wr s b v)) (L.wr s b v)) ∧
      Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (rrBody S rptr ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
        Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
        interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := rrBody S rptr ep
  p := hpz.choose
  Acc := fun b => b = true
  Locks := Locks
  Pre := VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := hpz.choose_spec.1
  obl := rr_pathOblJ hA hK hU hLA hmA
    (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
  side := rr_pathSideJ hA hK hLA (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm hufR
  once := rr_readOnceJ hA hK hLA (fun mm x a => congrFun (congrFun (hpz.choose_spec.1 A ar mm) x) a)
    hpz.choose_spec.2.1 hm hpz.choose_spec.2.2
  total := fun s a => rr_total hA (rptr, ep) s a
  masks := hm

end

end Fl4Proofs.P2.PathObl
