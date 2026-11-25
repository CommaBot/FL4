/-
# P2: `PathObl`, `PathSide`, `ReadOnce` of the VM ReplyRecv local path (line p2e, VM paths)

`rr_pathObl` / `rr_pathSide` / `rr_readOnce`: the per-path obligations of
`syscall.handle_reply_recv_vm_local` (`found = (rptr, ep)`) with the maximal sets `IoRS` / `IoWS` and
`DecSet = IoDS`, for `OwnMap.own K`, the class maps `OwnMap.cls K` / `OwnMap.ko K m0` and user memory
`K.user`, under `VmRRPre` (`P2/AccessVmRRD.lean`), as `vm_pathObl_mv` / `vm_pathSide` / `vm_readOnce`
for the VM-fault path (`P2/AccessVmObl.lean`, `P2/AccessVmMv.lean`).

* `acc`: `rr_vm_acc`; `dec_alt`: `rr_dec_alt`; `read_own` / `write_own` / `aligned`: the sets'
  definitions and `VmBase.dsSafe`; `move`: declined runs by `rr_dec_alt`, accepted runs by `rr_move`;
* `PathSide.read_aligned`: an accepting entry by `rr_vm_acc` and `interp_agree`; a declining one by
  `rr_dec_tr` on `IoRS s ∪ RrRep` (all aligned words); `ko_aligned` by `ko_unaligned`;
* `rr_readOnce`: from the guarded runs (accepting entry: `rr_vm_acc`, `interp_agree`; declining entry
  whose receiver is homed here or not reached: `rr_dec_tr` on `IoRS s`, `once_of_guard`), except a
  declining entry whose receiver is homed on another core (`hro`).

Premises:
* `VmRRPre`'s: `VmRPre`'s (`P2/AccessVmRRA.lean`), `hrR` / `hpE` [P], `RdTab` [J];
* `hK` [J] (`RegionOK`), `hU` [J] (`UserOK`), `hLA` [J] (`IoLayA`), `hmA` [J] (`ko`'s memory agrees with
  the entry on every TCB's `AFFINITY`, as `vm_pathObl_mv`);
* `hp` [P] (`IsProg`: the body is the tree `p`), `hz` [P] (`NoZero p`), `hm` [P] (writes leave
  `frame_masks`);
* `hro` [W]: `ReadOnce` at an entry whose receiver (the reply's `TCB`) is homed on another core: the
  declined run reads two words outside `IoRS s`, the receiver's home-owned `STATE` and `FAULT_TYPE`
  (`RrRep`), and the extracted text (`fastpath_vm::reply_recv_vm_found`, `proofs/Fl4Core/Funs.lean`)
  reads each once: it reads `STATE`, `FAULT_TYPE` and the `SC` word (a gate word) before
  `fastpath::schedulable_here` checks the receiver's `AFFINITY`, and the receiver's `SC` again, its
  refills (`sporadic::ready` / `sporadic::sufficient`), domain and queue words only after that check
  passed; no store instance can count reads (`P2/ReadGap.lean`), so this is a fact about `p`, like
  `IsProg` (the same shape as `vm_readOnce`'s `hro`);
* `huf` [J] (`PathSide.user_free`).
-/
import Fl4Proofs.P2.AccessVmRRD
import Fl4Proofs.P2.AccessVmObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK fld oAFFINITY)
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`PathObl` for the VM ReplyRecv local path** (module docstring). -/
theorem rr_pathObl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {rptr ep : U64}
    (hmA : ∀ s, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s →
      ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep)) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact rr_vm_acc hA hE.1 hE.2.2.2 h
  · intro s a r hE h hn s' r' Al h'
    exact rr_dec_alt hA hK hLA hE h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact (hE.1.base.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.1
    · exact (hE.1.base.dsSafe hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (rr_dec_alt hA hK hLA hE h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact rr_move hA hK hU hE.1 hE.2.2.2 (hmA s hE) hp h

/-- **`PathSide` for the VM ReplyRecv local path** (module docstring). -/
theorem rr_pathSide (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {rptr ep : U64}
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (huf : ∀ s b v, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → b ∈ K.user → Aligned b →
      VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep))
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1, fun x hx => ?_, huf⟩
  · intro s s' a r hE Al h
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

/-- **`ReadOnce` for the VM ReplyRecv local path** (module docstring), the entries with a receiver homed
on another core a premise (`hro` [W]). -/
theorem rr_readOnce (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K) {rptr ep : U64}
    {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (hro : ∀ s s' a r, VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep s → (∃ b, RrRep st rptr s b) →
      Alt st (IoRS (st := st) K Locks s) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) s s' →
      interp st ar p s' a = ok r → Once st ar (IoRS (st := st) K Locks s) (· ∈ K.user) ∅ ∅ p s' a) :
    ReadOnce st ar p (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)
      (VmRRPre st ar K T Cs Ω H Sg Rp Scs Nt Z Ac Locks rptr ep) (IoRS (st := st) K Locks) := by
  intro s s' a r hE Al h
  have hU : ∀ q, IoRS (st := st) K Locks s q → ¬ q ∈ K.user := fun q hq => hq.2.1
  obtain ⟨⟨b0, z0, c0⟩, h0⟩ := rr_total (st := st) hA (rptr, ep) s a
  cases b0
  · by_cases hrem : ∃ b, RrRep st rptr s b
    · exact hro s s' a r hE hrem Al h
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

end Fl4Proofs.P2.PathObl
