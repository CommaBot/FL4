/-
# P2: `PathObl` and `PathSide` for the I/O port local path (line p2io)

`io_pathObl` / `io_pathSide`: the per-path obligation of `syscall.handle_ioport_local` with the
maximal sets `IoRS` / `IoWS` (the aligned words the path may read / write by `OwnMap.own` at the
entry state) and `DecSet = IoDS` (`FAULT_IP`, `CUR_TIME`, `CONSUMED`), for the ownership map
`OwnMap.own K`, the class map `OwnMap.cls K` / `OwnMap.ko K m0` and user memory `K.user`.

* `acc`: `io_acc` (guarded run from the entry facts `IoPre`);
* `dec_alt`: `io_dec_alt` (a declined run is accepted at no alternative, and runs the same on
  the store guarded to `IoDS` and on `mguard`: its writes are safe words);
* `read_own` / `write_own` / `aligned`: by the sets' definitions and `IoDS.safe`;
* `move`: declined runs by `io_dec_alt`, accepted runs a premise;
* `PathSide.read_aligned`: an accepting entry by `io_acc` and agreement of the guarded tree
  (`interp_agree`); otherwise the entry run declines (`P0` totality) and `io_ra_dec`.

Premises:
* those of `IoPre` (`hPE`: `Pre` gives the entry facts), `hK` [J] (`RegionOK`), `hLA` [J] (`IoLayA`);
* `hp` [P] (`IsProgOn`: the body is the tree `p` on the stores narrowing `st`, from the entry states and their
  alternatives; `P2/IoPrune.lean` gives it from a tree of the pruned body), `hz` [W] (`NoZero p`), `hm` [P] (writes leave
  `frame_masks`), as in `P2/PathBridge` / E2E;
* `hmv` [W]: `move` of accepted runs (every write of an accepted run passes `StepOK`: the
  prefix's and the registers' are safe words, the thread state goes `RESTART` / `RUNNING` only);
* `huf` [J] (`PathSide.user_free`).
-/
import Fl4Proofs.P2.AccessIoRa
import Fl4Proofs.P2.PathAgree
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A} {number : I64} {p : SProg (Bool)}

/-- `IsProgOn` of the I/O port body, beta-reduced (for `rw`). -/
theorem io_hp {G : S → Prop}
    (hp : IsProgOn (fun m s a => syscall.handle_ioport_local m ar s a number) ar st G p)
    {m : machine.Store S} (N : Narrow st m) {s : S} (hG : G s) (a : A) :
    syscall.handle_ioport_local m ar s a number = interp m ar p s a := hp m N s hG a

/-- **`PathObl` for the I/O port path** (module docstring), `move` of accepted runs a premise. -/
theorem io_pathObl (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hmv : ∀ s a s1 a1, P s →
      syscall.handle_ioport_local st ar s a number = ok (true, s1, a1) →
      syscall.handle_ioport_local (mguard st (fun x y => StepOK (own K) (OwnMap.cls K) (OwnMap.ko K m0)
        (· ∈ K.user) (L.cpu s) (Locks s) (L.mem x) (L.mem y))) ar s a number = ok (true, s1, a1)) :
    PathObl st (fun m s a => syscall.handle_ioport_local m ar s a number) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact io_acc hA (hPE s hE) h
  · intro s a r hE h hn s' r' Al h'
    exact io_dec_alt hA hK hLA (hPE s hE) h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact ((hPE s hE).reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact ((hPE s hE).nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact ((hPE s hE).nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.1
    · exact (IoDS.safe (hPE s hE) hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (io_dec_alt hA hK hLA (hPE s hE) h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact hmv s a s1 a1 hE h

/-- **`PathSide` for the I/O port path** (module docstring). -/
theorem io_pathSide (hA : P0.ArchTotal ar) (hK : RegionOK K) (hLA : IoLayA K)
    {P : S → Prop} (hPE : ∀ s, P s → IoPre st K T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hp : IsProgOn (fun m s a => syscall.handle_ioport_local m ar s a number) ar st
      (AltOf st P (IoRS (st := st) K Locks) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user)) p) (hz : NoZero p)
    (hm : ∀ s a v, st.frame_masks (L.wr s a v) = st.frame_masks s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    PathSide st (fun m s a => syscall.handle_ioport_local m ar s a number)
      (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks P
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, fun s x _ hx => hx.1, fun x hx => ?_, huf⟩
  · intro s s' a r hE Al h
    by_cases hac : ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)
    · obtain ⟨s1, a1, h0⟩ := hac
      have hg := io_acc (Locks := Locks) hA (hPE s hE) h0
      rw [io_hp hp (Narrow.guard _ _ _) (AltOf.pre hE) a] at hg
      obtain ⟨s1', hg'⟩ := interp_agree hm (fun w hw => hw.1) (fun w hw => hw.1) p hz s s' a true s1 a1
        Al.ksb Al.cpu Al.masks Al.read hg
      have hs := interp_to (st := st) (st' := st) (fun _ _ _ => rfl)
        (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
        rfl rfl rfl p hz s' a _ hg'
      show syscall.handle_ioport_local _ ar s' a number = ok r
      rw [io_hp hp (Narrow.self st) ⟨s, hE, Al⟩ a] at h
      rw [io_hp hp (Narrow.guard _ _ _) ⟨s, hE, Al⟩ a]
      rw [hs] at h
      rw [← h]
      exact interp_mono (fun _ hw => hw.1) (fun _ _ => trivial) p hz s' a _ hg'
    · obtain ⟨r0, h0, -⟩ := spec_ex_fd (P0.syscall.handle_ioport_local.p0 st ar s a number L.total hA)
      have hr0 : r0.1 ≠ true := by
        obtain ⟨b, z, c⟩ := r0
        intro e
        change b = true at e
        subst e
        exact hac ⟨z, c, h0⟩
      exact io_ra_dec hA (hPE s hE) Al h0 hr0 h
  · by_contra hn
    exact hx (ko_unaligned hK hLA hn)

end

end Fl4Proofs.P2.PathObl
