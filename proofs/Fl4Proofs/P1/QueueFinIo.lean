/-
P1: the finalisation of an I/O-port cap (`IoPort first last owner`): with an
owner, `vcpu.revoke_ports` walks the VCPU list from the kernel-global head
`VCPU_HEAD` along the VCPUs' `NEXT` words, and at the owner stalls the
VCPU's thread (`smp.remote_tcb_stall`) and sets the ports' bits in its I/O
bitmap.  From P3's placement of the listed VCPUs (`IoPortPlace`: their
bitmap words are untracked object words, their `NEXT` words object words,
and neither the list's `NEXT` words nor its head among the bitmap words) the
finalisation keeps `Cur0` (`finGap_ioPort`).
-/
import Fl4Proofs.P1.QueueFinThr
import Fl4Proofs.P1.QueueDecSc
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]

/-- Word `k` of the VCPU `v`'s I/O bitmap. -/
def ioW (v k : U64) : U64 := core.num.U64.wrapping_add (core.num.U64.wrapping_add v vcpu.IO) k
/-- The VCPU `v`'s `NEXT` word. -/
def vNextA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.NEXT
/-- The VCPU list's head word (kernel-global `VCPU_HEAD`). -/
def vHeadA (st : machine.Store S) [L : LawfulStore st] (s : S) : U64 :=
  core.num.U64.wrapping_add (L.ksb s) layout.ks.VCPU_HEAD

/-- The VCPUs on the list at `s`. -/
inductive VListed (st : machine.Store S) [L : LawfulStore st] (s : S) : U64 → Prop
  | head : L.mem s (vHeadA st s) ≠ 0#u64 → VListed st s (L.mem s (vHeadA st s))
  | next {v : U64} : VListed st s v → L.mem s (vNextA v) ≠ 0#u64 → VListed st s (L.mem s (vNextA v))

/-- The list is kept by states agreeing on its head and `NEXT` words. -/
theorem VListed.keep {s s' : S} {v : U64} (hk : L.ksb s' = L.ksb s)
    (hh : L.mem s' (vHeadA st s) = L.mem s (vHeadA st s))
    (hn : ∀ w, VListed st s w → L.mem s' (vNextA w) = L.mem s (vNextA w)) (h : VListed st s v) :
    VListed st s' v := by
  have ea : vHeadA st s' = vHeadA st s := by unfold vHeadA; rw [hk]
  induction h with
  | head h0 =>
    rw [← hh, ← ea]; exact VListed.head (by rw [ea, hh]; exact h0)
  | next hv h0 ih =>
    rename_i w
    rw [← hn w hv]; exact VListed.next ih (by rw [hn w hv]; exact h0)

variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat}

/-- **The VCPU list's placement** (P3's, for the I/O-port caps'
finalisation): a listed VCPU's I/O bitmap words are aligned untracked object
words (`Ω` but not `Sg`), its `NEXT` word an object word, and no bitmap word
of a listed VCPU is a listed VCPU's `NEXT` word or the list's head. -/
structure IoPortPlace (st : machine.Store S) [L : LawfulStore st] (T Cs Ω : Set U64) (H : Heap)
    (Sg Rp Scs Nt : Set U64) (Z : U64 → Nat) : Prop where
  io : ∀ (Ac : Set U64) (s : S) (v k : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → VListed st s v →
    k.val < 8192 → k.val % 8 = 0 → Aligned (ioW v k) ∧ ioW v k ∈ Ω ∧ ioW v k ∉ Sg
  nxt : ∀ (Ac : Set U64) (s : S) (v : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → VListed st s v → vNextA v ∈ Ω
  disj : ∀ (Ac : Set U64) (s : S) (v w k : U64), BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s → VListed st s v →
    VListed st s w → k.val < 8192 → k.val % 8 = 0 → ioW v k ≠ vNextA w ∧ ioW v k ≠ vHeadA st s

variable {Ac : Set U64}

/-- `Cur0` across a remote stall. -/
theorem smp.remote_tcb_stall.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A)
    (t : obj.Tcb) (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    smp.remote_tcb_stall st ar s a t ⦃ s1 _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1 ∧
      L.ksb s1 = L.ksb s ∧ ∀ x ∈ Ω, L.mem s1 x = L.mem s x ⦄ := by
  obtain ⟨hc0, Ac', hX, ec, ecs, esc, na, nb⟩ := h
  have hct : L.curW s ∈ T := hX.1.choose_spec.choose_spec.curT
  refine WP.spec_mono (smp.remote_tcb_stall.bxi hA s a t hX) ?_
  rintro ⟨s1, a1⟩ ⟨hX1, ea, ec1, -, ecs1, fld, hΩ, wn⟩
  refine ⟨⟨hc0, Ac', hX1, ec1.trans ec, ecs1.trans ecs, ?_, fun y hy => by rw [ea]; exact na y hy, ?_⟩,
    wn.1, hΩ⟩
  · rw [← ec] at esc ⊢; rw [scA_eq, fld _ hct _ (by simp) (by simp), ← scA_eq]; exact esc
  · rw [← ec] at nb ⊢; rw [stA_eq, fld _ hct _ (by simp) (by simp), ← stA_eq]; exact nb

/-- The ports loop: bitmap writes of a listed VCPU. -/
theorem vcpu.ports_loop.cur0 (P : IoPortPlace st T Cs Ω H Sg Rp Scs Nt Z) {s0 s : S} {v high : U64} {port : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : VListed st s v) :
    vcpu.ports_loop st s v high true port ⦃ s' => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ∧
      VListed st s' v ∧ L.ksb s' = L.ksb s ∧ ∀ w, VListed st s w → VListed st s' w ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.ports_loop
  apply loop.spec_decr_nat (measure := fun y => 65536 - y.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1 ∧ VListed st y.1 v ∧ L.ksb y.1 = L.ksb s ∧
      ∀ w, VListed st s w → VListed st y.1 w)
  · rintro ⟨s1, p⟩ ⟨h1, hv1, hk1, hw1⟩
    simp only
    unfold vcpu.ports_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, hv1, hk1, hw1⟩
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h1, hv1, hk1, hw1⟩
    rename_i _ hp
    have hp' : p.val < 65536 := by simpa using hp
    obtain ⟨-, Ac1, hX1, -⟩ := id h1
    simp only [lift, bind_ok]
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hk8 : i2.val < 8192 ∧ i2.val % 8 = 0 := by
      have : i1.val = p.val >>> 6 := by simpa using hi1
      rw [hi2, this, Nat.shiftRight_eq_div_pow]; omega
    obtain ⟨al, hΩ, hSg⟩ := P.io Ac1 s1 v i2 hX1 hv1 hk8.1 hk8.2
    step as ⟨bit, _⟩
    refine WP.spec_bind (LawfulStore.read_spec s1 _) fun old _ => ?_
    simp only [if_true]
    refine WP.spec_bind (LawfulStore.write_spec s1 _ _) fun s2 e2 => ?_
    subst e2
    have hw := writesIn_wr (st := st) (s := s1) (v := old ||| bit) al
    have keepL : ∀ w, VListed st s1 w → VListed st (L.wr s1 (ioW v i2) (old ||| bit)) w := fun w hw' =>
      VListed.keep hw.1
        (L.mem_wr_ne al (hX1.2.2.2.1.ksΩ _ (by simp [layout.ks.VCPU_HEAD]) (by simp [layout.ks.VCPU_HEAD]) |>
          fun hm => (hX1.1.choose_spec.choose_spec.omega _ hm).1) (fun e => (P.disj Ac1 s1 v v i2 hX1 hv1 hv1 hk8.1 hk8.2).2 (UScalar.eq_of_val_eq e)))
        (fun u hu => L.mem_wr_ne al (hX1.1.choose_spec.choose_spec.omega _ (P.nxt Ac1 s1 u hX1 hu)).1
          (fun e => (P.disj Ac1 s1 v u i2 hX1 hv1 hu hk8.1 hk8.2).1 (UScalar.eq_of_val_eq e))) hw'
    step as ⟨p1, hp1⟩
    have c' := Cur0.capw h1 hw fun b hb => Or.inr (hb ▸ ⟨hΩ, hSg⟩)
    exact ⟨c', keepL v hv1, hw.1.trans hk1, fun w hw0 => keepL w (hw1 w hw0), by omega⟩
  · exact ⟨h, hv, rfl, fun w hw => hw⟩

end


section
variable {S : Type _} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}

theorem vcpu.stall.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar) {s0 s : S} (a : A) (v : U64)
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    vcpu.stall st ar s a v ⦃ s1 _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s1 ∧
      L.ksb s1 = L.ksb s ∧ ∀ x ∈ Ω, L.mem s1 x = L.mem s x ⦄ := by
  unfold vcpu.stall
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun t _ => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec t) fun b _ => ?_
  split
  · exact (WP.spec_ok _).2 ⟨h, rfl, fun _ _ => rfl⟩
  · exact smp.remote_tcb_stall.cur0 hA a1 t h

/-- The list walk. -/
theorem vcpu.revoke_ports_loop.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPortPlace st T Cs Ω H Sg Rp Scs Nt Z) {s0 s : S} {a : A} {owner low high v fuel : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) (hv : v = 0#u64 ∨ VListed st s v) :
    vcpu.revoke_ports_loop st ar s a owner low high v fuel ⦃ s' _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.revoke_ports_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.2.val)
    (inv := fun y => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 y.1 ∧ (y.2.2.1 = 0#u64 ∨ VListed st y.1 y.2.2.1))
  · rintro ⟨s1, a1, v1, f1⟩ ⟨h1, hv1⟩
    simp only
    unfold vcpu.revoke_ports_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hne
    have hv0 : v1 ≠ 0#u64 := by simpa using hne
    have hl : VListed st s1 v1 := hv1.resolve_left hv0
    split
    swap
    · exact (WP.spec_ok _).2 h1
    rename_i hf
    step as ⟨f2, hf2⟩
    refine WP.spec_bind (Pₘ := fun r : S × A => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 r.1 ∧ VListed st r.1 v1)
      ?_ ?_
    · split
      · refine WP.spec_bind (vcpu.stall.cur0 hA a1 v1 h1) ?_
        rintro ⟨s2, a2⟩ ⟨h2, k2, o2⟩
        try simp only [uncurry_apply_pair]
        obtain ⟨-, Ac1, hX1, -⟩ := id h1
        have hl2 : VListed st s2 v1 := VListed.keep k2
          (o2 _ (hX1.2.2.2.1.ksΩ _ (by simp [layout.ks.VCPU_HEAD]) (by simp [layout.ks.VCPU_HEAD])))
          (fun w hw => o2 _ (P.nxt Ac1 s1 w hX1 hw)) hl
        unfold vcpu.ports
        refine WP.spec_bind (vcpu.ports_loop.cur0 (port := low) (high := high) P h2 hl2) ?_
        rintro s3 ⟨h3, hl3, -, -⟩
        exact (WP.spec_ok _).2 ⟨h3, hl3⟩
      · exact (WP.spec_ok _).2 ⟨h1, hl⟩
    rintro ⟨s3, a3⟩ ⟨h3, hl3⟩
    try simp only [uncurry_apply_pair]
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s3 _) fun v2 e2 => ?_
    have hd : v2 = 0#u64 ∨ VListed st s3 v2 := by
      by_cases z : v2 = 0#u64
      · exact Or.inl z
      · right
        have e2' : v2 = L.mem s3 (vNextA v1) := e2
        rw [e2']; exact VListed.next hl3 (e2' ▸ z)
    have hf' : 0 < f1.val := by
      have := hf; simp only [gt_iff_lt] at this; scalar_tac
    exact (WP.spec_ok _).2 ⟨h3, hd, by dsimp only; scalar_tac⟩
  · exact ⟨h, hv⟩

theorem vcpu.revoke_ports.cur0 {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPortPlace st T Cs Ω H Sg Rp Scs Nt Z) {s0 s : S} {a : A} {owner low high : U64}
    (h : Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s) :
    vcpu.revoke_ports st ar s a owner low high ⦃ s' _ => Cur0 st T Cs Ω H Sg Rp Scs Nt Z Ac s0 s' ⦄ := by
  unfold vcpu.revoke_ports
  split
  · exact (WP.spec_ok _).2 h
  refine WP.spec_bind (hA.vcpu_barrier a) fun a1 _ => ?_
  refine WP.spec_bind (obj.ks_get.spec s _) fun v ev => ?_
  refine vcpu.revoke_ports_loop.cur0 hA P h ?_
  by_cases z : v = 0#u64
  · exact Or.inl z
  · right
    have ev' : v = L.mem s (vHeadA st s) := ev
    rw [ev']; exact VListed.head (ev' ▸ z)

/-- **The I/O-port caps' finalisation**, from the VCPU list's placement. -/
theorem finGap_ioPort {A : Type _} {ar : machine.Arch A} (hA : P0.ArchTotal ar)
    (P : IoPortPlace st T Cs Ω H Sg Rp Scs Nt Z) :
    FinGap st ar T Cs Ω H Sg Rp Scs Nt Z fun c => ∃ x1 x2 x3, c = .IoPort x1 x2 x3 := by
  rintro Ac s0 s a c fin h hc - ⟨f, l, o, rfl⟩
  simp only [objects.finalise_cap, objects.finalise_cap_object, bind_ok]
  refine WP.spec_bind (vcpu.revoke_ports.cur0 hA P h) ?_
  rintro ⟨s1, a1⟩ h1
  try simp only [uncurry_apply_pair]
  split
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, hc⟩
  · exact (WP.spec_ok _).2 ⟨h1, DelCapOK.null, DelCapOK.null⟩

end


end Fl4Proofs.P1
