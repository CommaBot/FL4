/-
P3 (DESIGN.md §9), VT-x: **the VT-x finalisation steps at `J`** (FL4's
`vcpu::revoke_ports` of an IO port cap with an owner, `ept::unmap` of an
EPT-mapped frame cap), each writing only VT-x words (`VtOut`,
XTopJointFinVt), the spec state kept (the spec does not model the VT-x
objects' contents, DESIGN §5).

* `ept_invalidate_ar`, `ept_unmap_vt`: `ept::unmap` writes at most the EPT
  entry an EPT walk from the ASID's found EPT root reaches (P1's
  `ept.unmap.cur0` shape), the arch relation kept (`ArchRefines.invEpt` [P]).
* `vcpu_stall_id`: a VCPU's stall is the identity on the store when its
  thread is none or a thread of the sets (one core, `remote_tcb_stall_id`),
  the arch relation kept (`ARKeep.vcpu_barrier` [P]).
* `ports_loop_vt`, `revoke_loop_vt`, `revoke_ports_vt`: the IO bitmap words
  of the listed VCPUs (`VIoW`, P1's `ioW` along `VListed`) the only writes
  (P1's `vcpu.revoke_ports.cur0` shape), the list kept (`VtIoPlace.disj`).
* `vcpu_finalise_vt`: `vcpu::finalise` of a VCPU bound to no thread writes
  at most its list neighbours' `NEXT`/`PREV` words and the list's head word.
* `VtIoPlace` [J]: the VCPU list's placement at a `JAtZ` state (as P1's
  `IoPortPlaceAt`, P3's): the listed VCPUs' IO bitmap words VT-x words,
  their `NEXT` and `TCB` words aligned and none of them, the list's head
  none of them, and a listed VCPU's thread none or a thread of `Z.T`
  (l4v `sym_refs` of the VCPU's TCB link).
* `VtEptPlace` [J]: an EPT walk from the found EPT root of any ASID reaches
  a VT-x word (P1's `EptPlace.find` / `EptTbl`, P3's).
-/
import Fl4Proofs.P3.XTopJointFinVt
import Fl4Proofs.P1.QueueFinIo
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3
open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1

noncomputable section

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st]

/-- A VCPU's `TCB` word (its bound thread). -/
def vTcbA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.TCB

/-- The IO bitmap words of the VCPUs listed at `s`. -/
def VIoW (st : machine.Store S) [L : P1.LawfulStore st] (s : S) (b : U64) : Prop :=
  ∃ v k : U64, P1.VListed st s v ∧ k.val < 8192 ∧ k.val % 8 = 0 ∧ b = P1.ioW v k

/-- **The VCPU list's placement at a `JAtZ` state** [J] (module docstring). -/
structure VtIoPlace (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) : Prop where
  io : ∀ v k : U64, P1.VListed st s v → k.val < 8192 → k.val % 8 = 0 → VtOut (L := L) Z H Cs s σ (P1.ioW v k)
  nal : ∀ w, P1.VListed st s w → P1.Aligned (P1.vNextA w) ∧ P1.Aligned (vTcbA w)
  disj : ∀ v w k : U64, P1.VListed st s v → P1.VListed st s w → k.val < 8192 → k.val % 8 = 0 →
    P1.ioW v k ≠ P1.vNextA w ∧ P1.ioW v k ≠ vTcbA w ∧ P1.ioW v k ≠ P1.vHeadA st s
  tcb : ∀ w, P1.VListed st s w → L.mem s (vTcbA w) = 0#u64 ∨ L.mem s (vTcbA w) ∈ Z.T

/-- **The EPT walks' placement at a `JAtZ` state** [J] (module docstring). -/
def VtEptPlace (Z : XSets) (H : P1.Heap) (Cs : Set U64) (s : S) (σ : Fl4Spec.State Unit) : Prop :=
  ∀ asid, ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → ∀ gpa level,
    ept.lookup st s r1 gpa level ⦃ o => ∀ x, o = .Ok x → VtOut (L := L) Z H Cs s σ x ⦄ ⦄

end

section
variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
  {AR : A → Fl4Spec.Cr3 → Prop}

/-- `ept::invalidate` keeps the store and the arch relation. -/
theorem ept_invalidate_ar (hA : ArchRefines arI AR) (s : S) (a : A) (root : U64) {c : Fl4Spec.Cr3}
    (h : AR a c) : ept.invalidate st arI s a root ⦃ r => r.1 = s ∧ AR r.2 c ⦄ := by
  have hC : ept.CORES = ok 4080#u64 := by unfold ept.CORES; rfl
  unfold ept.invalidate
  simp only [hC, lift, bind_ok,
    shr_eq _ 32#i32 (by decide) (by decide),
    show (4080#u64 + 8#u64 : Result U64) = ok 4088#u64 from rfl]
  step with LawfulStore.read_spec
  step with LawfulStore.read_spec
  refine WP.spec_bind (hA.invEpt a c _ _ h) ?_
  intro a' h'
  exact (WP.spec_ok _).2 ⟨rfl, h'⟩

/-- **`ept::unmap`** writes at most the entry an EPT walk from the found
root reaches (`X`), the arch relation kept. -/
theorem ept_unmap_vt (hA : ArchRefines arI AR) {s : S} (a : A) {c : Fl4Spec.Cr3} (hAR : AR a c)
    (asid gpa ptr level : U64) (table : Bool) {X : U64 → Prop} (hX : ∀ x, X x → P1.Aligned x)
    (hf : ept.find st s asid ⦃ r => ∀ r1, r = .Ok r1 → ∀ gpa level,
      ept.lookup st s r1 gpa level ⦃ o => ∀ x, o = .Ok x → X x ⦄ ⦄) :
    ept.unmap st arI s a asid gpa ptr level table ⦃ r => P1.WritesIn st s r.1 X ∧ AR r.2 c ⦄ := by
  have hS : P0.StoreTotal st := L.total
  have h0 : P1.WritesIn st s s X ∧ AR a c := ⟨P1.WritesIn.refl _ _, hAR⟩
  unfold ept.unmap
  refine WP.spec_bind hf ?_
  rintro (r1 | e) hr
  swap
  · exact (WP.spec_ok _).2 h0
  refine WP.spec_bind (hr r1 rfl gpa level) ?_
  rintro (x | e) hx
  swap
  · exact (WP.spec_ok _).2 h0
  have hxX := hx x rfl
  try dsimp only
  refine WP.spec_bind (LawfulStore.read_spec s x) fun e _ => ?_
  have fin : (do
      let s1 ← st.write s x 0#u64
      ept.invalidate st arI s1 a r1) ⦃ r => P1.WritesIn st s r.1 X ∧ AR r.2 c ⦄ := by
    refine WP.spec_bind (LawfulStore.write_spec s x 0#u64) fun s1 e1 => ?_
    subst e1
    refine WP.spec_mono (ept_invalidate_ar hA _ a r1 hAR) fun r ⟨er, har⟩ => ?_
    rw [er]
    exact ⟨(P1.writesIn_wr (hX x hxX)).mono fun b hb => by subst hb; exact hxX, har⟩
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · exact (WP.spec_ok _).2 trivial
    split <;> exact (WP.spec_ok _).2 trivial) fun large _ => ?_
  refine WP.spec_bind (Pₘ := fun _ => True) (by
    split
    · simp only [lift, bind_ok]
      step*
    · exact (WP.spec_ok _).2 trivial) fun mask _ => ?_
  simp only [lift, bind_ok, layout.paddr]
  split
  · exact (WP.spec_ok _).2 h0
  split
  · split
    · exact (WP.spec_ok _).2 h0
    split
    · exact (WP.spec_ok _).2 h0
    · exact fin
  · split
    · exact (WP.spec_ok _).2 h0
    · exact fin

/-- **A VCPU's stall** keeps the store when its thread is none or a thread
of `T` (one core), the arch relation kept. -/
theorem vcpu_stall_id (hK : ARKeep arI AR) {N T C : Set U64} {c : U64} {s : S} {σ : Fl4Spec.State Unit}
    (hS : SchedRel st N T C c s σ) (v : U64) (a : A) {cr : Fl4Spec.Cr3} (har : AR a cr)
    (ht : L.mem s (vTcbA v) = 0#u64 ∨ L.mem s (vTcbA v) ∈ T) :
    vcpu.stall st arI s a v ⦃ r => r.1 = s ∧ AR r.2 cr ⦄ := by
  unfold vcpu.stall
  refine WP.spec_bind (hK.vcpu_barrier a cr har) fun a1 har1 => ?_
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun t et => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec t) fun b eb => ?_
  split
  · exact (WP.spec_ok _).2 ⟨rfl, har1⟩
  · rename_i hb
    have ht0 : t ≠ 0#u64 := fun e => hb (by simp [eb, e])
    have et' : t = L.mem s (vTcbA v) := et
    have htT : t ∈ T := by
      rw [et'] at ht0 ⊢
      exact ht.resolve_left ht0
    exact WP.spec_mono (remote_tcb_stall_id (ar := arI) a1 hS htT) fun r e => by rw [e]; exact ⟨rfl, har1⟩

/-- **The ports loop** writes only the IO bitmap words of `v`. -/
theorem ports_loop_vt {X : U64 → Prop} {s : S} {v high port : U64}
    (hio : ∀ k : U64, k.val < 8192 → k.val % 8 = 0 → X (P1.ioW v k) ∧ P1.Aligned (P1.ioW v k)) {s1 : S}
    (h1 : P1.WritesIn st s s1 X) :
    vcpu.ports_loop st s1 v high true port ⦃ s' => P1.WritesIn st s s' X ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.ports_loop
  apply loop.spec_decr_nat (measure := fun y => 65536 - y.2.val) (inv := fun y => P1.WritesIn st s y.1 X)
  · rintro ⟨s2, p⟩ h2
    simp only
    unfold vcpu.ports_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 h2
    split
    swap
    · exact (WP.spec_ok _).2 h2
    rename_i _ hp
    have hp' : p.val < 65536 := by simpa using hp
    simp only [lift, bind_ok]
    step as ⟨i1, hi1⟩
    step as ⟨i2, hi2⟩
    have hk8 : i2.val < 8192 ∧ i2.val % 8 = 0 := by
      have : i1.val = p.val >>> 6 := by simpa using hi1
      rw [hi2, this, Nat.shiftRight_eq_div_pow]; omega
    obtain ⟨hX, al⟩ := hio i2 hk8.1 hk8.2
    step as ⟨bit, _⟩
    refine WP.spec_bind (LawfulStore.read_spec s2 _) fun old _ => ?_
    simp only [if_true]
    refine WP.spec_bind (LawfulStore.write_spec s2 _ _) fun s3 e3 => ?_
    subst e3
    have hw := P1.writesIn_wr (st := st) (s := s2) (v := old ||| bit) al
    step as ⟨p1, hp1⟩
    exact ⟨(h2.trans hw).mono fun b hb => hb.elim id (fun e => by subst e; exact hX), by omega⟩
  · exact h1

/-- A VCPU's `PREV` word. -/
def vPrevA (v : U64) : U64 := core.num.U64.wrapping_add v vcpu.PREV

/-- **`vcpu::finalise` of a VCPU bound to no thread** (its `TCB` word zero:
the stall and the detach do nothing) writes at most its neighbours' links
(`X`: the previous VCPU's `NEXT` word, the next VCPU's `PREV` word) and the
list's head word, the arch relation kept. -/
theorem vcpu_finalise_vt (hK : ARKeep arI AR) {s : S} (v : U64) (a : A) {cr : Fl4Spec.Cr3} (har : AR a cr)
    (h0 : L.mem s (vTcbA v) = 0#u64) (hha : P1.Aligned (P1.vHeadA st s)) {X : U64 → Prop}
    (hp : L.mem s (vPrevA v) ≠ 0#u64 →
      X (P1.vNextA (L.mem s (vPrevA v))) ∧ P1.Aligned (P1.vNextA (L.mem s (vPrevA v))))
    (hn : L.mem s (P1.vNextA v) ≠ 0#u64 →
      X (vPrevA (L.mem s (P1.vNextA v))) ∧ P1.Aligned (vPrevA (L.mem s (P1.vNextA v)))) :
    vcpu.finalise st arI s a v ⦃ r => P1.WritesIn st s r.1 (fun b => X b ∨ b = P1.vHeadA st s) ∧ AR r.2 cr ⦄ := by
  unfold vcpu.finalise
  refine WP.spec_bind (Pₘ := fun r : S × A => r.1 = s ∧ AR r.2 cr) ?_ ?_
  · unfold vcpu.stall vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (hK.vcpu_barrier a cr har) fun a1 har1 => ?_
    refine WP.spec_bind (LawfulStore.read_spec s _) fun t et => ?_
    refine WP.spec_bind (obj.Tcb.is_null.spec t) fun b eb => ?_
    have et' : t = L.mem s (vTcbA v) := et
    have hb : b = true := by simp [eb, et', h0]
    rw [hb, if_pos rfl]
    exact (WP.spec_ok _).2 ⟨rfl, har1⟩
  rintro ⟨s1, a1⟩ ⟨e1, har1⟩
  try simp only at e1 har1
  subst s1
  try dsimp only
  unfold vcpu.get
  simp only [lift, bind_ok]
  refine WP.spec_bind (LawfulStore.read_spec s _) fun t et => ?_
  refine WP.spec_bind (obj.Tcb.is_null.spec t) fun b eb => ?_
  have et' : t = L.mem s (vTcbA v) := et
  have hb : b = true := by simp [eb, et', h0]
  rw [hb, if_pos rfl]
  simp only [bind_ok]
  try dsimp only
  refine WP.spec_bind (LawfulStore.read_spec s _) fun pv ep => ?_
  refine WP.spec_bind (LawfulStore.read_spec s _) fun nx en => ?_
  have ep' : pv = L.mem s (vPrevA v) := ep
  have en' : nx = L.mem s (P1.vNextA v) := en
  refine WP.spec_bind (Pₘ := fun s3 => P1.WritesIn st s s3 (fun b => X b ∨ b = P1.vHeadA st s)) ?_
    fun s3 h3 => ?_
  · by_cases hp0 : pv = 0#u64
    · rw [if_pos hp0]
      refine WP.spec_mono (obj.ks_set.spec s _ _) fun s3 e3 => ?_
      subst e3
      exact (P1.writesIn_wr (a := P1.vHeadA st s) (v := nx) hha).mono fun b hb => Or.inr hb
    · rw [if_neg hp0]
      unfold vcpu.set
      simp only [lift, bind_ok]
      refine WP.spec_mono (LawfulStore.write_spec s _ _) fun s3 e3 => ?_
      subst e3
      obtain ⟨hXp, hap⟩ := hp (by rw [← ep']; exact hp0)
      rw [← ep'] at hXp hap
      exact (P1.writesIn_wr (a := P1.vNextA pv) (v := nx) hap).mono fun b hb => Or.inl (by
        have e' : b = P1.vNextA pv := hb
        rw [e']; exact hXp)
  split
  · rename_i hne
    have hn0 : nx ≠ 0#u64 := by simpa using hne
    unfold vcpu.set
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.write_spec s3 _ _) fun s4 e4 => ?_
    subst e4
    obtain ⟨hXn, han⟩ := hn (by rw [← en']; exact hn0)
    rw [← en'] at hXn han
    exact (WP.spec_ok _).2 ⟨(h3.trans (P1.writesIn_wr (a := vPrevA nx) (v := pv) han)).mono fun b hb =>
      Or.elim hb id fun e => Or.inl (by
        have e' : b = vPrevA nx := e
        rw [e']; exact hXn), har1⟩
  · exact (WP.spec_ok _).2 ⟨h3, har1⟩

variable {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64} {Lst : U64 → List U64} {D : Set U64}

theorem VIoW.vt {s : S} {σ : Fl4Spec.State Unit} (P : VtIoPlace (L := L) Z H Cs s σ) {b : U64} (h : VIoW st s b) :
    VtOut (L := L) Z H Cs s σ b := by
  obtain ⟨v, k, hv, h1, h2, rfl⟩ := h
  exact P.io v k hv h1 h2

/-- The list's words kept across `VIoW` writes. -/
theorem VIoW.keep {s s1 : S} {σ : Fl4Spec.State Unit} (P : VtIoPlace (L := L) Z H Cs s σ)
    (h : P1.WritesIn st s s1 (VIoW st s)) {w : U64} (hw : P1.VListed st s w) :
    L.mem s1 (P1.vNextA w) = L.mem s (P1.vNextA w) ∧ L.mem s1 (vTcbA w) = L.mem s (vTcbA w) :=
  ⟨h.mem_eq (P.nal w hw).1 fun ⟨v, k, hv, k1, k2, e⟩ => (P.disj v w k hv hw k1 k2).1 e.symm,
    h.mem_eq (P.nal w hw).2 fun ⟨v, k, hv, k1, k2, e⟩ => (P.disj v w k hv hw k1 k2).2.1 e.symm⟩

/-- **The VCPU list walk of `revoke_ports`** writes only `VIoW` words. -/
theorem revoke_loop_vt (hK : ARKeep arI AR) {s : S} {a0 : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a0 σ) (P : VtIoPlace (L := L) Z H Cs s σ)
    {owner low high : U64} {s1 : S} {a1 : A} {v fuel : U64}
    (h1 : P1.WritesIn st s s1 (VIoW st s)) (har : AR a1 σ.archState.x64CurrentCr3)
    (hv : v = 0#u64 ∨ P1.VListed st s v) :
    vcpu.revoke_ports_loop st arI s1 a1 owner low high v fuel ⦃ r =>
      P1.WritesIn st s r.1 (VIoW st s) ∧ AR r.2 σ.archState.x64CurrentCr3 ⦄ := by
  have hS : P0.StoreTotal st := L.total
  unfold vcpu.revoke_ports_loop
  apply loop.spec_decr_nat (measure := fun y => y.2.2.2.val)
    (inv := fun y => P1.WritesIn st s y.1 (VIoW st s) ∧ AR y.2.1 σ.archState.x64CurrentCr3 ∧
      (y.2.2.1 = 0#u64 ∨ P1.VListed st s y.2.2.1))
  · rintro ⟨s2, a2, v1, f1⟩ ⟨h2, har2, hv1⟩
    simp only
    unfold vcpu.revoke_ports_loop.body
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h2, har2⟩
    rename_i hne
    have hv0 : v1 ≠ 0#u64 := by simpa using hne
    have hl : P1.VListed st s v1 := hv1.resolve_left hv0
    split
    swap
    · exact (WP.spec_ok _).2 ⟨h2, har2⟩
    rename_i hf
    step as ⟨f2, hf2⟩
    refine WP.spec_bind (Pₘ := fun r : S × A => P1.WritesIn st s r.1 (VIoW st s) ∧ AR r.2 σ.archState.x64CurrentCr3)
      ?_ ?_
    · split
      · have J2 := (J.vtJ (h2.mono fun b hb => VIoW.vt P hb) har2).1
        have ht : L.mem s2 (vTcbA v1) = 0#u64 ∨ L.mem s2 (vTcbA v1) ∈ Z.T := by
          rw [(VIoW.keep P h2 hl).2]; exact P.tcb v1 hl
        refine WP.spec_bind (vcpu_stall_id hK J2.xtop.fin.1.1.1 v1 a2 har2 ht) ?_
        rintro ⟨s3, a3⟩ ⟨e3, har3⟩
        try simp only at e3
        try simp only at har3
        subst e3
        try simp only [uncurry_apply_pair]
        unfold vcpu.ports
        refine WP.spec_bind (ports_loop_vt (port := low) (high := high)
          (fun k k1 k2 => ⟨⟨v1, k, hl, k1, k2, rfl⟩, (P.io v1 k hl k1 k2).al⟩) h2) ?_
        intro s4 h4
        exact (WP.spec_ok _).2 ⟨h4, har3⟩
      · exact (WP.spec_ok _).2 ⟨h2, har2⟩
    rintro ⟨s3, a3⟩ ⟨h3, har3⟩
    try simp only [uncurry_apply_pair]
    unfold vcpu.get
    simp only [lift, bind_ok]
    refine WP.spec_bind (LawfulStore.read_spec s3 _) fun v2 e2 => ?_
    have hd : v2 = 0#u64 ∨ P1.VListed st s v2 := by
      by_cases z : v2 = 0#u64
      · exact Or.inl z
      · right
        have e2' : v2 = L.mem s (P1.vNextA v1) := by rw [← (VIoW.keep P h3 hl).1]; exact e2
        rw [e2']; exact P1.VListed.next hl (e2' ▸ z)
    have hf' : 0 < f1.val := by
      have := hf; simp only [gt_iff_lt] at this; scalar_tac
    exact (WP.spec_ok _).2 ⟨h3, har3, hd, by dsimp only; scalar_tac⟩
  · exact ⟨h1, har, hv⟩

/-- **`revoke_ports`** writes only `VIoW` words, the arch relation kept. -/
theorem revoke_ports_vt (hK : ARKeep arI AR) {s : S} {a : A} {σ : Fl4Spec.State Unit}
    (J : JAtZ (L := L) arI AR Z H Cs Ac Lst D s a σ) (P : VtIoPlace (L := L) Z H Cs s σ)
    (owner low high : U64) :
    vcpu.revoke_ports st arI s a owner low high ⦃ r =>
      P1.WritesIn st s r.1 (VIoW st s) ∧ AR r.2 σ.archState.x64CurrentCr3 ⦄ := by
  have har := J.xtop.fin.1.1.2.2.2.2.2.2
  unfold vcpu.revoke_ports
  split
  · exact (WP.spec_ok _).2 ⟨P1.WritesIn.refl _ _, har⟩
  refine WP.spec_bind (hK.vcpu_barrier a _ har) fun a1 har1 => ?_
  refine WP.spec_bind (obj.ks_get.spec s _) fun v ev => ?_
  refine revoke_loop_vt hK J P (P1.WritesIn.refl _ _) har1 ?_
  by_cases z : v = 0#u64
  · exact Or.inl z
  · right
    have ev' : v = L.mem s (P1.vHeadA st s) := ev
    rw [ev']; exact P1.VListed.head (ev' ▸ z)

end

end

end Fl4Proofs.P3
