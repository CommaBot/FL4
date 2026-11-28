/-
P2 (line jsweep, gen 1): **four slot [J]s of `serializable_fl4_localW11PJ3` discharged** —
`serializable_fl4_localW11PJ4`.

* **st `StPremW3.nu`** (node words of the current core are no user words, at every `StEnt` state): a projection of
  `StEnt.lay` (`StLay.nu_node`). **`StPremW3A`** = `StPremW3` minus `nu`, `StPremW3A.toW3`.
* **vt `VtPremP7.OL`** (`ObjLay`: endpoints / replies in their object regions) and **vt `VtPremP7.SL`**
  (`SlotLayV` at every `VtPre` state): layout facts. `OL` by `objLay_of_layP` at the record's bundle state with
  the index's `H = K.heap`, `Rp = K.heap.replies`; `SL` by **`slotLayV_all`** (state-free version of
  `slotLayV_of_JAtZ`: `SlotLayV` reads the state only through `LocT`'s `y ∈ T`) with `T = K.heap.tcbs`. The index
  equalities are the start state's `BunIxU` (`VtEntJ8.ix`). **`VtPremP7N`** = `VtPremP7` minus `OL` / `SL`,
  `VtPremP7N.toP7`.
* **vx `VxEntJ8.usr`** (every aligned user word is a P1 `UsrW` word at the start state): **`usrW_bunIx`** from the
  start state's `BunIx` (the bundle: `SlJAt.userObj` / `userNode64` / `userKs`, `LayP.heap.align`, P3's `csLt`).
  **`VxEntJ8N`** = `VxEntJ8` minus `usr`, `VxEntJ8N.toJ8`.

The start fact **`StartP3W11S`** is `StartP3W11L` with these records. For vt the start state is named before the
record's two layout fields (`∃ σ, (Ch σ ∧ VtEntJ8 σ) ∧ ∀ X, GlueAt … (· = σ)`): the glue is asked the `GlueAt` for
every proof of the two fields (proof-irrelevant, so for the one there is). **`startP3W11L_of_S`**: `StartP3W11S` ⇒
`StartP3W11L`. **`serializable_fl4_localW11PJ4`**: `serializable_fl4_localW11PJ3` with `StartP3W11JS` starts.

Satisfiability: every new record / entry fact is implied by the old one (`StPremW3A.ofW3`, `VtPremP7N.ofP7`,
`VxEntJ8N.ofJ8`), so it is satisfiable wherever the old one is; the start fact asks strictly less.

No new premise. Remaining [J]s of the touched records: st `eu`; vt `tp`, `eu`, `M`, `UB`, `pSg`; vx `eu`
(handoff jsweep.md). No existing statement changed.
-/
import Fl4Proofs.P2.E2EPW11J3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY InW TcbSlot LayP layoutJ layP_of_JAtZ)
open Fl4Proofs.P2.E2E (StartAt SP SerStep)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

section lay
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **`SlotLayV` at every state** from one bundle state of the layout, for threads of the layout's heap. -/
theorem slotLayV_all {K : KLayout} {σb : S} (B : SlJAt (L := L) K σb) {T : Set U64}
    (hTH : ∀ y ∈ T, K.heap y = some .tcb) (s : S) : SlotLayV K st T s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := B
  suffices h : SlotLayV (layoutJ Zx K.heap (L.ksb σb) K.ncores) st T s by rwa [B.lay] at h
  have J := B.j
  have hP := layP_of_JAtZ J (n := K.ncores) fun c hc => (B.cs c).2 hc
  obtain ⟨Tr, Cq, hJ⟩ := J.jpl
  intro y hy k hk
  have hyH := hTH y hy.1
  have hth : Zx.th y = some .tcb := (hJ.tcb y).2 hyH
  have hf := hJ.heap.fits y _ hyH
  simp only [HKind.bits] at hf
  have hsa : Fl4Proofs.P3.IsSlotAt Zx.th y 1 := Or.inr ⟨hth, by unfold Fl4Proofs.P3.tcbSlots; omega⟩
  have hpv : (Fl4Proofs.P3.slotOf y 1).val = y.val + 32 := by have := hsa.val hJ.pl; omega
  have hps : Fl4Proofs.P3.slotOf y 1 ∈ (layoutJ Zx K.heap (L.ksb σb) K.ncores).slots := by
    show Fl4Proofs.P3.IsSlot Zx.th _
    exact ⟨y, 1, hsa, rfl⟩
  have hkv : (core.num.U64.wrapping_add y k).val = y.val + k.val := by
    simp [core.num.U64.wrapping_add_val_eq, U64.size_def, U64.numBits]; omega
  have hin : InW (Fl4Proofs.P3.slotOf y 1) 32 (core.num.U64.wrapping_add y k) := by
    unfold InW; rw [hpv, hkv]; omega
  refine ⟨_, hP.region_slotW hps hin, ⟨y, hyH, ?_⟩, by rw [hpv, hkv]; omega⟩
  unfold InW; rw [hpv]
  constructor <;> omega

variable {Kl : KLayout} {T Cs Ω : Set U64} {H : Heap} {Sg Rp Scs Nt : Set U64} {Z : U64 → Nat} {Ac : Set U64}
  {s : S}

/-- **Every aligned user word is a P1 `UsrW` word at a `BunIx` state** (module docstring). -/
theorem usrW_bunIx (BI : BunIx (L := L) Kl T Cs Ω H Sg Rp Scs Nt Z Ac s) :
    ∀ x ∈ Kl.user, Aligned x → UsrW st T Cs H Sg Scs Z s x := by
  obtain ⟨hKH, hT, -, hSg, -, hScs, -, hZ, hS⟩ := BI
  subst hKH hT hSg hScs hZ
  have B := hS.slJAt
  have hCs : ∀ c ∈ Cs, c.val < 64 := by
    obtain ⟨A', arI, AR, Zx, Lst, D, a', τ, Bz⟩ := hS
    exact fun c hc => Bz.j.kern.csLt c hc
  intro x hx ha
  have hH := B.layP.heap
  refine ⟨⟨ha, fun t ht => ?_, fun c hc => ?_⟩, fun e he => ?_, ?_, fun o h1 _ e => ?_, fun c hc hin => ?_⟩
  · have := B.userObj hx (k := .tcb) ht (fun z e => by cases e)
    simp only [InW, HKind.bits] at this
    omega
  · have h := B.userNode64 hx (hCs c hc)
    omega
  · rcases he with he | he
    · have := B.userObj hx he (fun z e => by cases e)
      have hal : e.val % 16 = 0 := by simpa [HKind.bits] using hH.align e _ he
      simp only [InW, HKind.bits] at this
      unfold Aligned at ha
      omega
    · have := B.userObj hx he (fun z e => by cases e)
      have hal : e.val % 64 = 0 := by simpa [HKind.bits] using hH.align e _ he
      simp only [InW, HKind.bits] at this
      unfold Aligned at ha
      omega
  · rintro ⟨-, p, k, hp, hk, hin⟩
    rcases hk with rfl | ⟨z, rfl⟩ | ⟨rfl, -⟩
    · exact B.userObj hx hp (fun z e => by cases e) hin
    · exact B.userObj hx hp (fun z' e => by cases e) hin
    · exact B.userObj hx hp (fun z e => by cases e) hin
  · exact B.userKs hx h1 (by rw [← B.kc.1]; exact e.symm)
  · exact B.userObj hx (scs_heap hc) (fun z e => by cases e) hin

end lay

section prem
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **`StPremW3` without `nu`** (module docstring). -/
structure StPremW3A (i : StArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (as `stSlotP3W`). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- Index convention: the index's `Q` is `StEntK` (stpost's `StEntKK`). -/
  hQ : i.Q = fun K' m' s => StEntK K'.toKLayout st K'.heap.tcbs i.Cs i.Ω K'.heap i.Sg K'.heap.replies
    K'.heap.scs K'.heap.ntfns K'.heap.scBits i.Ac i.target m' s
  /-- [J] the entry facts kept by aligned user writes. -/
  eu : ∀ s b v, StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
      K.heap.scBits i.Ac i.target s → b ∈ (userV K).user → Aligned b →
    StEnt (userV K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits i.Ac
      i.target (L.wr s b v)
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s

variable {st} in
theorem StPremW3A.toW3 {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremW3A st i K m) :
    StPremW3 st i K m :=
  ⟨h.nv, h.bun, h.hQ, h.eu, h.kd, fun _ hE _ ho => hE.lay.nu_node ho⟩

variable {st} in
theorem StPremW3A.ofW3 {i : StArg S} {K : KLayoutV} {m : U64 → U64} (h : StPremW3 st i K m) :
    StPremW3A st i K m :=
  ⟨h.nv, h.bun, h.hQ, h.eu, h.kd⟩

/-- **`VtPremP7` without `OL` / `SL`** (module docstring). -/
structure VtPremP7N (i : VtArg S) (K : KLayoutV) (m : U64 → U64) : Prop where
  /-- No VCPU in the layout (the glue's layout choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [J] at every `VtPre` state the ASID pool words are no user words. -/
  tp : ∀ s, VtPre st i K s → ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 →
    L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 → peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user
  /-- [J] the entry facts kept by aligned user writes. -/
  eu : ∀ s b v', VtPre st i K s → b ∈ K.user → Aligned b → VtPre st i K (L.wr s b v')
  /-- [P] -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn
  /-- [J] the map memory agrees with every `VtPre` state on every thread's `AFFINITY`. -/
  M : ∀ s, VtPre st i K s → ∀ y ∈ i.T, m (fld y oAFFINITY) = L.mem s (affA y)
  /-- [P] -/
  PL : PlanLk i.lk i.pl
  /-- [J] -/
  UB : ∀ s, VtPre st i K s → ∃ U : Set U64, Fl4Proofs.P1.UserOK st i.T i.Cs i.Ω i.H U s ∧
    ∀ y ∈ i.T, msg.lookup_ipc_buffer st s true y ⦃ b => BufOK U b ⦄
  /-- [J] -/
  pSg : ∀ s, VtPre st i K s → core.num.U64.wrapping_add (vOf st s) vcpu.PENDING ∉ i.Sg

/-- vt's two layout fields (`VtPremP7.OL`, `.SL`). -/
def VtLayX (i : VtArg S) (K : KLayoutV) : Prop :=
  ObjLay K.toKLayout i.H i.Rp ∧ ∀ s, VtPre st i K s → SlotLayV K.toKLayout st i.T s

variable {st} in
theorem VtPremP7N.toP7 {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (h : VtPremP7N st i K m)
    (X : VtLayX st i K) : VtPremP7 st i K m :=
  ⟨h.nv, h.bun, h.tp, h.eu, h.kd, h.Nt, h.M, X.1, h.PL, h.UB, X.2, h.pSg⟩

variable {st} in
theorem VtPremP7N.ofP7 {i : VtArg S} {K : KLayoutV} {m : U64 → U64} (h : VtPremP7 st i K m) :
    VtPremP7N st i K m ∧ VtLayX st i K :=
  ⟨⟨h.nv, h.bun, h.tp, h.eu, h.kd, h.Nt, h.M, h.PL, h.UB, h.pSg⟩, h.OL, h.SL⟩

variable {st} in
/-- **vt's layout fields from the start state's `BunIxU`** (module docstring). -/
theorem vtLayX_of {i : VtArg S} {K : KLayoutV} {σ : S} (E : VtEntJ8 st i K σ) : VtLayX st i K := by
  have B : SlJAt (L := L) K.toKLayout σ := E.ix.slJAtS.slJAt
  have hKH := E.ix.hKH
  have hT := E.ix.hT
  have hRp := E.ix.hRp
  refine ⟨?_, fun s _ => ?_⟩
  · rw [hRp, ← hKH]
    exact objLay_of_layP B.layP (fun r hr => hr)
  · rw [hT, ← hKH]
    exact slotLayV_all B (fun y hy => hy) s

/-- **vx's start entry facts without `usr`** (module docstring). -/
structure VxEntJ8N (i : VxArg S) (K : KLayoutV) (s : S) : Prop where
  /-- Index convention. -/
  ix : BunIx (L := L) K.toKLayout i.T i.Cs i.Ω i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac s
  /-- [P] the glue's `v` is the current thread's bound VCPU (fl4-sync's `local_vm_exit`). -/
  hv : i.v = vOf st s
  /-- [P] -/
  buf : msg.lookup_ipc_buffer st s true (L.curW s) ⦃ b => BufOK {x | x ∈ K.user ∧ Aligned x} b ⦄

variable {st} in
theorem VxEntJ8N.toJ8 {i : VxArg S} {K : KLayoutV} {s : S} (E : VxEntJ8N st i K s) : VxEntJ8 st i K s :=
  ⟨E.ix, E.hv, usrW_bunIx E.ix, E.buf⟩

variable {st} in
theorem VxEntJ8N.ofJ8 {i : VxArg S} {K : KLayoutV} {s : S} (E : VxEntJ8 st i K s) : VxEntJ8N st i K s :=
  ⟨E.ix, E.hv, E.buf⟩

end prem

section start
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st] {A : Type}
  (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

/-- **`StartP3W11L` with st / vt / vx at the shrunk records** (module docstring). -/
def StartP3W11S (Ch : S → Prop) (K : KLayoutV) (m : U64 → U64) (hK : RegionOKV K) (hU : UserOKV K) (c : U64)
    (hs : U64 → Prop) (q : SP) : Fl4IxW (S := S) → Prop
  | .st j => ∃ h : StPremW3A st j K m, GlueAt ((stSlotP3W st ar hA hm).liftAt j K m hK hU h.toW3.toP3)
      (fun σ : S => Ch σ ∧ StEntJ7 st j K σ) c hs m q
  | .vq (.inl j) => ∃ h : VxPremP3 st j K m, GlueAt ((vxSlotP3 st ar hA hm).path j K m hK hU h)
      (fun σ : S => Ch σ ∧ VxEntJ8N st j K σ) c hs m q
  | .vq (.inr j) => ∃ h : VtPremP7N st j K m, ∃ σ : S, (Ch σ ∧ VtEntJ8 st j K σ) ∧
      ∀ X : VtLayX st j K, GlueAt ((vtSlotP3W5 st ar hA hm).path j K m hK hU (h.toP7 X).toP5)
        (fun σ' : S => σ' = σ) c hs m q
  | i => StartP3W11L st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i

variable {arI AR MR}

/-- **`StartP3W11S` gives `StartP3W11L`.** -/
theorem startP3W11L_of_S {Ch : S → Prop} {K : KLayoutV} {m : U64 → U64} {hK : RegionOKV K} {hU : UserOKV K}
    {c : U64} {hs : U64 → Prop} {q : SP} {i : Fl4IxW (S := S)}
    (h : StartP3W11S st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i) :
    StartP3W11L st ar hA hm hSt a0 arI AR MR Ch K m hK hU c hs q i := by
  cases i with
  | st j =>
    obtain ⟨h1, hG⟩ := h
    exact ⟨h1.toW3, hG⟩
  | vq j =>
    cases j with
    | inl j =>
      obtain ⟨h1, hG⟩ := h
      exact ⟨h1, hG.mono fun σ he _ => ⟨he.1, he.2.toJ8⟩⟩
    | inr j =>
      obtain ⟨h1, σ, ⟨hC, hE⟩, hG⟩ := h
      have X := vtLayX_of hE
      exact ⟨h1.toP7 X, (hG X).mono fun σ' e _ => by subst e; exact ⟨hC, hE⟩⟩
  | vmF j => exact h
  | vmR j => exact h
  | io j => exact h
  | irq j => exact h
  | sl j => exact h

end start

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)
variable {A3 : Type} (arI : machine.Arch A3) (AR : A3 → Fl4Spec.Cr3 → Prop) (MR : A3 → Fl4Spec.MachineState → Prop)

variable {arI AR MR}

end top

end
end Fl4Proofs.P2.E2EP
