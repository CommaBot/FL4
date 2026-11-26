/-
P2 (line jsweep, gen 2): **the affinity agreement in the path's `Pre`** — vmF / vmR / vt paths with no `mA` / `M`
record field, and the family `fl4LocW11JA` beside `fl4LocW11J`.

**Why the old records are vacuous on SMP** (handoff jsweep.md, gen 2, item 1). `VmFPrem.mA` (vmF),
`VmRPremP3.mA` (vmR) and `VtPremP7*.M` (vt) say: one fixed memory `m` agrees with *every* `Pre` state of the
index on every TCB's `AFFINITY` word. Two `Pre` states that differ only in a non-current, SC-less thread's
`AFFINITY` (P1 constrains it only to lie in `Cs`) cannot both agree with `m`, so the record is false as soon as the
index has two such states (`vmRPremP3_false`, `vmFPremNL_false`): on every layout with ≥ 2 cores and such a thread.

**The fix** (as io's `IoQ`): the agreement is a conjunct of the path's `Pre` (**`AffAg`**). It survives an aligned
user write (`AFFINITY` words are aligned non-user TCB words, `affAg_wr`) and holds at a start by the glue's memory
link (`affAg_of_link`). The obligation proofs use the agreement only at the entry state (`vm_move` / `rr_move`), so
`PathObl` is re-proved pointwise (`vm_pathOblA`, `rr_pathOblA`); `PathSide` / `ReadOnce` / `IsProgOn` restrict.

* **vmF** `vm_localPathA`: `Pre = VmPre ∧ AffAg`; record **`VmFPremA`** = `nv`, `bun` (no premise: the start
  state), `uf` [J] (unchanged `VmFPrem.uf`, see the handoff for its status).
* **vmR** `rr_localPathA`: `Pre = VmRRPreJ ∧ AffAg`; record **`VmRPremA`** = `nv`, `bun`, `cs` [P], `kd` [P].
* **vt** `vtimer_localPathA`: `Pre = VtmEnt ∧ VtTP` (**`VtTP`**: the ASID-pool entries are no user words, gen 1's
  `tp`, kept by user writes: the table words are `NU`, `vtTP_wr`). At P3 scope (`K.vcpus = ∅`) an accepted VM-timer
  run is impossible (`vt_noAcc`: acceptance needs a bound VCPU, `VexitEnt.vin` puts it in `K.vcpus`), so the fire
  case's `M`, `UB`, `SL`, `OL`, `PL` and `pSg` are **not needed at all** (in particular `pSg` stated only under
  `vOf ≠ 0` is vacuous here). Record **`VtPremA`** = `nv`, `bun`, `kd` [P], `Nt` (P1 typing), `eu` (from the start
  state, `vtEu_of`).
* Slots `vmFSlotA`, `vmRSlotA`, `vtSlotA`, the family `fl4LocA` (the other five slots as `fl4LocP3W6`), its PTE
  avoidance under `QPs` **`allA`** (the three new paths: copies of `vmF_avoidPJ_path` / `vmR_avoidPJ_path` /
  `vt_avoidPJ_path` with the bigger `Pre`), **`fl4LocW11JA`** (restricted, PTE-cut, lifted to `ownP`) and
  **`pre_ksbA`**.

No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPW11J7
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout own RegionOK region fld oAFFINITY)
open Fl4Proofs.P2.E2E (StartAt SP SerStep Once ReadOnce)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll Step PureGlue hwCfg)

noncomputable section
open Classical

/-! ## Restricting `PathObl` / `PathSide` -/

section restr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {A X : Type}
variable {f : machine.Store S → S → A → Result (X × S × A)} {Acc : X → Prop}
  {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop} {Locks : S → U64 → Prop} {Pre : S → Prop} {RS WS DS : S → U64 → Prop}

theorem _root_.Fl4Proofs.P2.PathObl.PathObl.restrA (O : PathObl st f Acc own cls ko User Locks Pre RS WS DS)
    (Q : S → Prop) : PathObl st f Acc own cls ko User Locks (fun s => Pre s ∧ Q s) RS WS DS :=
  ⟨fun s a r h => O.acc s a r h.1, fun s a r h => O.dec_alt s a r h.1, fun s x h => O.read_own s x h.1,
    fun s x h => O.write_own s x h.1, fun s x h => O.aligned s x h.1, fun s a r h => O.move s a r h.1⟩

theorem _root_.Fl4Proofs.P2.PathObl.PathSide.restrA (Sd : PathSide st f cls ko User Locks Pre RS WS DS)
    {Q : S → Prop} (hQ : ∀ s b v, Pre s → Q s → User b → Aligned b → Q (L.wr s b v)) :
    PathSide st f cls ko User Locks (fun s => Pre s ∧ Q s) RS WS DS :=
  ⟨fun s s' a r h => Sd.read_aligned s s' a r h.1, fun s x h => Sd.rs_aligned s x h.1, Sd.ko_aligned,
    fun s b v h hb ha => by
      obtain ⟨h1, h2⟩ := Sd.user_free s b v h.1 hb ha
      exact ⟨⟨h1, hQ s b v h.1 h.2 hb ha⟩, h2⟩⟩

end restr

/-! ## The agreement on `AFFINITY` words -/

section aff
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]

/-- **The memory parameter agrees with the state on every TCB's `AFFINITY` word** (io's `IoQ` second half). -/
def AffAg (K : KLayout) (m0 : U64 → U64) (s : S) : Prop :=
  ∀ d, K.heap d = some .tcb → m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY)

variable {st}

/-- **`AffAg` survives an aligned user write** (`AFFINITY` words are aligned non-user words, `UserOK.tcb`). -/
theorem affAg_wr {K : KLayout} {m0 : U64 → U64} (hU : E2E.UserOK K) {s : S} {b v : U64}
    (h : AffAg st K m0 s) (hb : b ∈ K.user) (ha : Aligned b) : AffAg st K m0 (L.wr s b v) := by
  intro d hd
  obtain ⟨h1, h2⟩ := hU.tcb d hd oAFFINITY (Or.inl rfl)
  rw [h d hd]
  exact (wr_nu ha hb v ⟨h1, h2⟩).symm

/-- **`AffAg` at a start state** from the glue's memory link (agreement off the user words of `K`). -/
theorem affAg_of_link {K : KLayoutV} {m0 : U64 → U64} (hK : RegionOKV K) (hU : UserOKV K) {s : S}
    (hμ : ∀ x, Aligned x → ¬ x ∈ K.user → L.mem s x = m0 x) : AffAg st (userV K) m0 s := by
  intro d hd
  obtain ⟨h1, h2⟩ := (userOK_userV hK hU).tcb d hd oAFFINITY (Or.inl rfl)
  exact (hμ _ h1 (fun hu => h2 (mem_userV.2 (Or.inl hu)))).symm

/-- **Finding 1, vmR**: no record `VmRPremP3` exists once two `Pre` states of the index differ on one TCB's
`AFFINITY` word. -/
theorem vmRPremP3_false {A : Type} {ar : machine.Arch A} {i : VmRArg S} {K : KLayoutV} {m : U64 → U64}
    {s1 s2 : S} {d : U64}
    (h1 : VmRRPreJ st ar (userV K) (userV K).heap.tcbs i.Cs i.Ω i.Sg (userV K).heap.scs (userV K).heap.ntfns
      (userV K).heap.scBits i.Ac i.Locks i.rptr i.ep s1)
    (h2 : VmRRPreJ st ar (userV K) (userV K).heap.tcbs i.Cs i.Ω i.Sg (userV K).heap.scs (userV K).heap.ntfns
      (userV K).heap.scBits i.Ac i.Locks i.rptr i.ep s2)
    (hd : (userV K).heap d = some .tcb) (hne : L.mem s1 (fld d oAFFINITY) ≠ L.mem s2 (fld d oAFFINITY)) :
    ¬ VmRPremP3 st ar i K m :=
  fun h => hne ((h.mA s1 h1 d hd).symm.trans (h.mA s2 h2 d hd))

/-- **Finding 1, vmF**: likewise for `VmFPremNL` (the vmF record of the current tops). -/
theorem vmFPremNL_false {A : Type} {ar : machine.Arch A} {i : VmFArg S} {K : KLayoutV} {m : U64 → U64}
    {s1 s2 : S} {d : U64}
    (h1 : VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s1)
    (h2 : VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s2)
    (hd : (userV K).heap d = some .tcb) (hne : L.mem s1 (fld d oAFFINITY) ≠ L.mem s2 (fld d oAFFINITY)) :
    ¬ VmFPremNL st ar i K m :=
  fun h => hne ((h.mA s1 h1 d hd).symm.trans (h.mA s2 h2 d hd))

/-- **Finding 1, vt**: likewise for `VtPremP7M` (`M` over every `VtPre` state). -/
theorem vtPremP7M_false {i : VtArg S} {K : KLayoutV} {m : U64 → U64} {s1 s2 : S} {d : U64}
    (h1 : VtPre st i K s1) (h2 : VtPre st i K s2) (hd : d ∈ i.T)
    (hne : L.mem s1 (affA d) ≠ L.mem s2 (affA d)) : ¬ VtPremP7M st i K m :=
  fun h => hne ((h.M s1 h1 d hd).symm.trans (h.M s2 h2 d hd))

end aff

/-! ## vmF: `Pre = VmPre ∧ AffAg` -/

section vmf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω U Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`PathObl` of the VM-fault path at `VmPre ∧ AffAg`** (`vm_pathObl` / `vm_move` with the agreement read from
the state's `Pre`). -/
theorem vm_pathOblA (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {addr code : U64} {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_vm_fault_local m ar x a addr code = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_vm_fault_local m ar s a addr code) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (fun s => VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s ∧ AffAg st K m0 s)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE h hb
    subst hb
    exact vm_acc hA hE.1.1 hE.1.2.2 h
  · intro s a r hE h hn s' r' Al h'
    exact vm_dec_alt hA hK hLA hE.1.1 hE.1.2.1 h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE hx _
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact (hE.1.1.base.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact (hE.1.1.base.nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact (hE.1.1.base.nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE hx
    rcases hx with hx | hx
    · exact hx.1
    · exact (hE.1.1.base.dsSafe hx).1
  · rintro s a ⟨b, s1, a1⟩ hE h
    cases b
    · exact (vm_dec_alt hA hK hLA hE.1.1 hE.1.2.1 h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact vm_move hA hK hU hE.1.1 hE.1.2.2 hE.2 hp h

variable (ar) in
/-- **The VM-fault local path with the agreement in its `Pre`** (module docstring). `huf` [J] is `VmFPrem.uf`. -/
noncomputable def vm_localPathA (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {addr code : U64} (hm : E2E.MasksWr st)
    (huf : ∀ s b v, VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s → b ∈ K.user → Aligned b →
      VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) K Locks (L.wr s b v) = IoRS (st := st) K Locks s ∧
        IoWS (st := st) K Locks (L.wr s b v) = IoWS (st := st) K Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vmBody S addr code
  p := R.syscall.handle_vm_fault_local addr code
  Acc := fun b => b = true
  Locks := Locks
  Pre := fun s => VmPre st ar K T Cs Ω U H Sg Rp Scs Nt Z Ac Locks s ∧ AffAg st K m0 s
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := IsProg.on (vm_isProg S addr code) _ _ _
  obl := vm_pathOblA hA hK hU hLA (fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a)
  side := (vm_pathSide (m0 := m0) hA hK hLA
    (fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a) (vm_noZero addr code) hm huf).restrA
    (fun _ _ _ _ hq hb ha => affAg_wr hU hq hb ha)
  once := fun s s' a r h => vm_readOnce (m0 := m0) hA hK hLA
    (fun mm x a => congrFun (congrFun (vm_isProg S addr code A ar mm) x) a) (vm_noZero addr code) hm
    (vm_hro hA hK hLA hm) s s' a r h.1
  total := fun s a => vm_total hA addr code s a
  masks := hm

end vmf

/-! ## vmR: `Pre = VmRRPreJ ∧ AffAg` -/

section vmr
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Scs Nt Ac : Set U64} {Z : U64 → Nat} {K : KLayout}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type} {ar : machine.Arch A}

/-- **`PathObl` of the VM ReplyRecv path at `VmRRPreJ ∧ AffAg`** (`rr_pathOblJ`, agreement from `Pre`). -/
theorem rr_pathOblA (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K) (hLA : IoLayA K)
    {rptr ep : U64} {p : SProg Bool}
    (hp : ∀ (m : machine.Store S) (x : S) (a : A),
      syscall.handle_reply_recv_vm_local m ar x a (rptr, ep) = interp m ar p x a) :
    PathObl st (fun m s a => syscall.handle_reply_recv_vm_local m ar s a (rptr, ep)) (fun b => b = true)
      (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) Locks
      (fun s => VmRRPreJ st ar K T Cs Ω Sg Scs Nt Z Ac Locks rptr ep s ∧ AffAg st K m0 s)
      (IoRS (st := st) K Locks) (IoWS (st := st) K Locks) (IoDS (st := st)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro s a ⟨b, s1, a1⟩ hE' h hb
    have hE := VmRRPreJ.pre hE'.1
    subst hb
    exact rr_vm_acc hA hE.1 hE.2.2.2 h
  · intro s a r hE' h hn s' r' Al h'
    exact rr_dec_alt hA hK hLA (VmRRPreJ.pre hE'.1) h hn Al h'
  · intro s x _ hx _; exact hx.2.2
  · intro s x hE' hx _
    have hE := VmRRPreJ.pre hE'.1
    rcases hx with hx | hx
    · exact hx.2
    · rcases hx with rfl | rfl | rfl
      · exact (hE.1.base.reg (Locks := Locks) (by simp [layout.reg.FAULT_IP])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CUR_TIME])
          (by simp [layout.node.CUR_TIME])).2.2
      · exact (hE.1.base.nd (Locks := Locks) _ (by simp [layout.node.CONSUMED])
          (by simp [layout.node.CONSUMED])).2.2
  · intro s x hE' hx
    have hE := VmRRPreJ.pre hE'.1
    rcases hx with hx | hx
    · exact hx.1
    · exact (hE.1.base.dsSafe hx).1
  · rintro s a ⟨b, s1, a1⟩ hE' h
    have hE := VmRRPreJ.pre hE'.1
    cases b
    · exact (rr_dec_alt hA hK hLA hE h Bool.false_ne_true (Alt.refl s) h).2.2
    · exact rr_move hA hK hU hE.1 hE.2.2.2 hE'.2 hp h

variable (ar) in
/-- **The VM ReplyRecv local path with the agreement in its `Pre`** (`rr_localPathJK2` without `hmA`). -/
noncomputable def rr_localPathA (hA : P0.ArchTotal ar) (hK : RegionOK K) (hU : E2E.UserOK K)
    (hLA : IoLayA K) {rptr ep : U64} (hm : E2E.MasksWr st) (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ s : S, SlJAt (L := L) K s → KernDetAt (L := L) K Locks s) :
    E2E.LocalPath (own K) (OwnMap.cls K) (OwnMap.ko K m0) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := rrBody S rptr ep
  p := R.syscall.handle_reply_recv_vm_local (rptr, ep)
  Acc := fun b => b = true
  Locks := Locks
  Pre := fun s => VmRRPreJ st ar K K.heap.tcbs Cs Ω Sg K.heap.scs K.heap.ntfns K.heap.scBits Ac Locks rptr ep s ∧
    AffAg st K m0 s
  RS := IoRS (st := st) K Locks
  WS := IoWS (st := st) K Locks
  DS := IoDS (st := st)
  isProg := IsProg.on (rr_isProg S rptr ep) _ _ _
  obl := rr_pathOblA hA hK hU hLA (fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a)
  side := (rr_pathSideJ (m0 := m0) hA hK hLA (fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a)
    (rr_noZero rptr ep) hm (vm_hufRK hA hCs (hlk_of_kernelDetK hKD))).restrA
    (fun _ _ _ _ hq hb ha => affAg_wr hU hq hb ha)
  once := fun s s' a r h => rr_readOnceJ (m0 := m0) hA hK hLA
    (fun mm x a => congrFun (congrFun (rr_isProg S rptr ep A ar mm) x) a) (rr_noZero rptr ep) hm
    (rr_hroJ hA) s s' a r h.1
  total := fun s a => rr_total hA (rptr, ep) s a
  masks := hm

end vmr

/-! ## vt: `Pre = VtmEnt ∧ VtTP`, no accepted run at P3 scope -/

/-- **The ASID-pool entries are no user words** (gen 1's vt `tp`, now a conjunct of the path's `Pre`). -/
def VtTP {S : Type} (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop :=
  ∀ hi : U64, hi.val < 2048 → ∀ lo : U64, lo.val < 512 → L.mem s (atAF (L.ksb s) hi) ≠ 0#u64 →
    peAF (L.mem s (atAF (L.ksb s) hi)) lo ∉ K.user

section vt
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {A : Type} {ar : machine.Arch A} {irq n : U64} {pl : localtimer.TimerIrqPlan} {lk : S → U64 → Prop}
  {m : U64 → U64}

/-- **`VtTP` survives an aligned user write at a `VtmEnt` state** (the table words are `NU`: `SlJAt.nuAsid`). -/
theorem vtTP_wr {σb X : S} (B : SlJAt (L := L) K.toKLayout σb)
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n X) (h : VtTP K st X) {b : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (v : U64) : VtTP K st (L.wr X b v) := by
  intro hi hhi lo hlo hne
  have hk : L.ksb X = L.ksb σb := by rw [ksb_pin hE.ent.inv hE.ent.lay, slJAt_ksb B]
  have eA : L.mem (L.wr X b v) (atAF (L.ksb X) hi) = L.mem X (atAF (L.ksb X) hi) :=
    wr_nu hba hb v (B.nuAsid hk hhi)
  rw [L.ksb_wr, eA] at hne ⊢
  exact h hi hhi lo hlo hne

/-- **`VtTP` at a bundle state** (`irqLayK_of_slJAt`'s `tabU`). -/
theorem vtTP_of_bun {s : S} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s) (B : SlJAt (L := L) K.toKLayout s) :
    VtTP K st s :=
  fun hi hhi lo hlo hne => ((irqLayK_of_slJAt hI B).tabU hi hhi).2 lo hlo hne

variable (ar) in
/-- **No accepted VM-timer run at P3 scope**: acceptance needs a bound VCPU (`vtimer_bnd`), which `VexitEnt.vin`
places in `K.vcpus = ∅`. -/
theorem vt_noAcc (nv : K.vcpus = ∅) {s s1 : S} {a a1 : A}
    (hE : VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s)
    (h : localvm.handle_vm_timer_irq_local st ar s a irq pl n = ok (true, s1, a1)) : False :=
  not_inVcpu_empty nv (hE.ent.vin (vtimer_bnd ar h).2.1)

variable (ar) in
/-- **The VM-timer local path at P3 scope** (module docstring): `vtimer_localPath`'s data with `Pre = VtmEnt ∧
VtTP`; the fire case is vacuous (`vt_noAcc`). Premises: `hA`, `hK` [J], `hU` [J], `hm` [P], `nv`, a bundle state
`B` (no premise: the start state), `hEU` (vt's `eu`, discharged from the start state: `vtEu_of`), `hlk` [P], `hNt`. -/
noncomputable def vtimer_localPathA (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (hm : E2E.MasksWr st) (nv : K.vcpus = ∅) {σb : S} (B : SlJAt (L := L) K.toKLayout σb)
    (hEU : ∀ s b v', VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s → b ∈ K.user → Aligned b →
      VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n (L.wr s b v'))
    (hlk : ∀ s b v', b ∈ K.user → Aligned b → lk (L.wr s b v') = lk s)
    (hNt : ∀ q ∈ Nt, H q = some .ntfn) :
    E2E.LocalPath (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user) where
  S := S
  A := A
  X := Bool
  st := st
  L := L
  ar := ar
  F := vtimerBody S irq pl n
  p := R.localvm.handle_vm_timer_irq_local irq pl n
  Acc := fun b => b = true
  Locks := lk
  Pre := fun s => VtmEnt K st T Cs Ω H Sg Rp Scs Nt Z Ac lk irq n s ∧ VtTP K st s
  RS := VexitRS K st lk
  WS := VexitWS K st lk
  DS := IrqDec st
  isProg := PathObl.IsProg.on (vtimer_isProg S irq pl n) _ _ _
  obl := (vtimer_pathObl (m := m) ar hA hK hU (vtimer_isProg S irq pl n) (vtimer_noZero irq pl n) hm
    (fun _ _ _ _ hE _ h => (vt_noAcc ar nv hE h).elim) (fun _ _ _ _ hE _ h => (vt_noAcc ar nv hE h).elim)
    (fun _ _ _ _ hE h => vtimer_dec_own ar hA hK hNt hE h)).restrA _
  side := (vtimer_pathSide (m := m) ar hA hK hU (vtimer_isProg S irq pl n) (vtimer_noZero irq pl n) hm
    (fun _ _ _ _ hE _ h => (vt_noAcc ar nv hE h).elim)
    (fun _ _ _ _ hE h => vtimer_dec_own ar hA hK hNt hE h) hEU hlk).restrA
    (fun _ b v hE hq hb ha => vtTP_wr B hE hq hb ha v)
  once := fun s _ a _ hE hAlt _ =>
    vtimer_once_alt ar hA hK (vcpuNU_empty nv) hm hE.1 (vtmU_of hE.1 B hE.2)
      (fun _ _ _ h => (vt_noAcc ar nv hE.1 h).elim)
      (fun _ _ h => vtimer_dec_ownU ar hA hK (vcpuNU_empty nv) hNt hE.1 (vtmU_of hE.1 B hE.2) h) hAlt
  total := fun s a => by
    obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localvm.handle_vm_timer_irq_local.p0 st ar s a irq pl n LawfulStore.total hA)
    exact ⟨r, e⟩
  masks := hm

end vt

/-! ## The records and slots -/

section slots
variable {S : Type} (st : machine.Store S) [L : LawfulStore st] {A : Type} (ar : machine.Arch A)

/-- **vmF's record without `mA`** (module docstring). -/
structure VmFPremA (i : VmFArg S) (K : KLayoutV) : Prop where
  /-- No VCPU in the layout (the glue's choice at P3 scope). -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [J] `VmPre`, locks and sets kept by user writes (`VmFPrem.uf`). -/
  uf : ∀ s b v, VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s →
    b ∈ (userV K).user → Aligned b →
    VmPre st ar (userV K) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks (L.wr s b v) ∧
      i.Locks (L.wr s b v) = i.Locks s ∧
      IoRS (st := st) (userV K) i.Locks (L.wr s b v) = IoRS (st := st) (userV K) i.Locks s ∧
      IoWS (st := st) (userV K) i.Locks (L.wr s b v) = IoWS (st := st) (userV K) i.Locks s ∧
      IoDS (st := st) (L.wr s b v) = IoDS (st := st) s

variable {st ar} in
theorem VmFPremA.lay {i : VmFArg S} {K : KLayoutV} (h : VmFPremA st ar i K) : IoLayA (userV K) :=
  ioLayA_userV (SlJAt.ioLayA h.bun.choose_spec)

/-- **vmR's record without `mA`** (`VmRPremP3` minus `mA`). -/
structure VmRPremA (i : VmRArg S) (K : KLayoutV) : Prop where
  /-- No VCPU in the layout. -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) (userV K) σ
  /-- [P] the glue's core set is below 64. -/
  cs : ∀ c ∈ i.Cs, c.val < 64
  /-- [P] at bundle states the locks are determined by kernel words. -/
  kd : ∀ s : S, SlJAt (L := L) (userV K) s → KernDetAt (L := L) (userV K) i.Locks s

/-- **vt's record at P3 scope, `eu` not yet given** (module docstring). -/
structure VtPremA0 (i : VtArg S) (K : KLayoutV) : Prop where
  /-- No VCPU in the layout. -/
  nv : K.vcpus = ∅
  /-- Some bundle state of the layout (no premise: the start state). -/
  bun : ∃ σ : S, SlJAt (L := L) K.toKLayout σ
  /-- [P] the locks are determined by the core, the kernel base and the aligned words off `(userV K).user`. -/
  kd : ∀ s, KernDetS (L := L) (userV K).user i.lk s
  /-- P1's notifications typed in the heap. -/
  Nt : ∀ q ∈ i.Nt, i.H q = some .ntfn

/-- **vt's record at P3 scope**: `VtPremA0` and `eu` (`VtEuX`, from the start state). -/
structure VtPremA (i : VtArg S) (K : KLayoutV) : Prop where
  base : VtPremA0 st i K
  eu : VtEuX st i K

variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **VM fault slot, the agreement in `Pre`.** -/
def vmFSlotA : SlotU (VmFArg S) where
  Prem i K _ := VmFPremA st ar i K
  path i K m hK hU h :=
    vm_localPathA (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (U := i.U) (H := i.H) (Sg := i.Sg) (Rp := i.Rp)
      (Scs := i.Scs) (Nt := i.Nt) (Z := i.Z) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) h.lay (addr := i.addr) (code := i.code) hm h.uf
  W _ _ _ _ _ h := noVcpuRW_empty h.nv _

/-- **VM ReplyRecv slot, the agreement in `Pre`.** -/
def vmRSlotA : SlotU (VmRArg S) where
  Prem i K _ := VmRPremA st i K
  path i K m hK hU h :=
    rr_localPathA (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Ac := i.Ac) (Locks := i.Locks) (m0 := m)
      ar hA (regionOK_userV hK) (userOK_userV hK hU) h.bun.choose_spec.ioLayA (rptr := i.rptr) (ep := i.ep) hm
      h.cs h.kd
  W _ _ _ _ _ h := noVcpuRW_empty h.nv _

/-- **VM-timer slot at P3 scope, `VtTP` in `Pre`.** -/
def vtSlotA : SlotN (VtArg S) where
  Prem i K _ := VtPremA st i K
  path i K m hK hU h :=
    vtimer_localPathA (T := i.T) (Cs := i.Cs) (Ω := i.Ω) (Sg := i.Sg) (Rp := i.Rp) (Scs := i.Scs) (Nt := i.Nt)
      (Ac := i.Ac) (H := i.H) (Z := i.Z) (lk := i.lk) (irq := i.irq) (n := i.n) (pl := i.pl) (m := m) ar hA hK hU hm
      h.base.nv h.base.bun.choose_spec h.eu
      (fun s b v' hb hba => hlk_of_kernelDetU (P := fun _ => True) (fun s _ => h.base.kd s) s b v' trivial
        (mem_userV.2 (Or.inl hb)) hba)
      h.base.Nt

variable (hSt : P0.StoreTotal st) (a0 : A)

/-- **The family with the agreement in `Pre`**: `fl4LocP3W6` with vmF, vmR and vt replaced. -/
def fl4LocA : Fl4Loc (VmFArg S) (VmRArg S) (IoArg S) (StArg S) (IrqArg S) (SlArg S) (VxArg S ⊕ VtArg S) where
  vmF := vmFSlotA st ar hA hm
  vmR := vmRSlotA st ar hA hm
  io := ioSlotP3W st ar hA hm
  st := stSlotP3W st ar hA hm
  irq := irqSlotP3W st ar hA hm
  sl := slSlotP3W6 st ar hA hm hSt a0
  vq := PathsV.sum ((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm)) ((vtSlotA st ar hA hm).fam (fl4Dflt st ar hm))

end slots

/-! ## PTE avoidance of the three new paths under `QPs` -/

section av
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st)

/-- **The VM-fault path with the agreement in `Pre` reads no PTE word** under `QPs` (`vmF_avoidPJ_path`). -/
theorem vmF_avoidPJ_pathA (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmFSlotA st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((vmFSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_vm_fault_local mm ar x a i.addr i.code =
      interp mm ar (R.syscall.handle_vm_fault_local i.addr i.code) x a :=
    fun a mm x => congrFun (congrFun (vm_isProg S i.addr i.code A ar mm) x) a
  refine ⟨?_, ?_, IsProg.on (vm_isProg S i.addr i.code) _ _ _⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs1.1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok (true, s1, a1) := hr
    have g1 := vm_acc (Locks := i.Locks) hA hs'.1 hs'.2.2 hr'
    have g2 := vm_acc (Locks := i.Locks) hA (vmFPre_userP hK hq.ks hs'.1) (rdTab_userP hs'.2.2 hq.tab) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_vm_fault_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a i.addr i.code = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks s := hs1.1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_vm_fault_local st ar s a i.addr i.code = ok r := hr
    have h'' : syscall.handle_vm_fault_local st ar s' a i.addr i.code = ok r' := h'
    have hP := vmFPre_userP hK hq.ks hs'.1
    have hn0 : r.1 ≠ true := hn
    have hn' : r'.1 ≠ true :=
      (vm_dec_alt (m0 := m) hA (regionOK_userV hK.base) h.lay hs'.1 hs'.2.1 hr' hn0 hAl h'').1
    have hg := vm_dec_tr hA hP hs'.2.1 (ag_userP hAl)
      (R'' := fun b => IoRS (st := st) (userP K) i.Locks s b ∨ VmRep st ar s a b) (fun b hb => Or.inl hb)
      (fun s1 a1 sl ptr badge x y g gr eu hsl hcap hst hne =>
        Or.inr ⟨s1, a1, sl, ptr, badge, x, y, g, gr, eu, hsl, hcap, hst, hne, rfl⟩) h'' hn'
    show syscall.handle_vm_fault_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.addr i.code
      = ok r'
    exact (eP a _ s').trans (interp_mono (st := st)
      (fun q hq => Or.elim hq (fun h1 => (ioRS_of_userP h1).2) (fun h2 => VmRep.notPte hA hK hP hs'.2.1 h2))
      (fun _ _ => trivial) _ (vm_noZero i.addr i.code) s' a r' ((eP a _ s').symm.trans hg))


/-- **The VM ReplyRecv path with the agreement in `Pre` reads no PTE word** under `QPs` (`vmR_avoidPJ_path`). -/
theorem vmR_avoidPJ_pathA (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmRSlotA st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((vmRSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have eP : ∀ (a : A) (mm : machine.Store S) (x : S), syscall.handle_reply_recv_vm_local mm ar x a (i.rptr, i.ep) =
      interp mm ar (R.syscall.handle_reply_recv_vm_local (i.rptr, i.ep)) x a :=
    fun a mm x => congrFun (congrFun (rr_isProg S i.rptr i.ep A ar mm) x) a
  have hex : ∃ p : SProg Bool, IsProg (rrBody S i.rptr i.ep) p ∧ NoZero p ∧
      ∀ s s' a r, VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
          (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
          i.rptr i.ep s →
        (∃ b, RrRep st i.rptr s b) →
        PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' →
        interp st ar p s' a = ok r →
        E2E.Once st ar (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (· ∈ (userV K.toKLayoutV).user) ∅ ∅ p s' a :=
    ⟨_, rr_isProg S i.rptr i.ep, rr_noZero i.rptr i.ep, rr_hroJ hA⟩
  have bun : ∀ s, SlJAt (L := L) (userV K.toKLayoutV) s → SlJAt (L := L) K.toKLayout s := by
    intro s hJ; rw [← userV_empty h.nv]; exact hJ
  refine ⟨?_, ?_, IsProg.on (rr_isProg S i.rptr i.ep) _ _ _⟩
  · intro s a r hs hr hb
    have hs' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s := hs.1.1
    have hq : QPs K st s := hs.2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok (true, s1, a1) := hr
    have hE := VmRRPreJ.pre hs'
    have g1 := rr_vm_acc (Locks := i.Locks) hA hE.1 hE.2.2.2 hr'
    have g2 := rr_vm_acc (Locks := i.Locks) hA (vmRPre_userP hK hq.ks hE.1)
      (rdTab_userP hE.2.2.2 hq.tab) hr'
    have w1 := (interp_guard _ s a _ ((eP a _ s).symm.trans g1)).2
    have w2 := (interp_guard _ s a _ ((eP a _ s).symm.trans g2)).2
    show syscall.handle_reply_recv_vm_local
      (guard st (rsE (· ∈ K.ptes) (IoRS (st := st) (userV K.toKLayoutV) i.Locks) s)
        (IoWS (st := st) (userV K.toKLayoutV) i.Locks s)) ar s a (i.rptr, i.ep) = ok (true, s1, a1)
    exact (eP a _ s).trans (guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP a st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.1 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2)))
  · intro s a r hs hr hn s' r' hA' h'
    have hs' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s := hs.1.1
    have hq : QPs K st s := hs.2
    have hAl : PathObl.Alt st (IoRS (st := st) (userV K.toKLayoutV) i.Locks s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have hr' : syscall.handle_reply_recv_vm_local st ar s a (i.rptr, i.ep) = ok r := hr
    have h'' : syscall.handle_reply_recv_vm_local st ar s' a (i.rptr, i.ep) = ok r' := h'
    have hE := VmRRPreJ.pre hs'
    have hEP : VmRRPre st ar (userP K) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω K.heap i.Sg (Heap.replies K.heap)
        (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac i.Locks
        i.rptr i.ep s :=
      ⟨vmRPre_userP hK hq.ks hE.1, hE.2.1, hE.2.2.1, rdTab_userP hE.2.2.2 hq.tab⟩
    have hn0 : r.1 ≠ true := hn
    have hn' : r'.1 ≠ true :=
      (rr_dec_alt (m0 := m) hA (regionOK_userV hK.base) h.bun.choose_spec.ioLayA hE hr' hn0 hAl h'').1
    have hg := rr_dec_tr hA hEP (ag_userP hAl)
      (R'' := fun b => IoRS (st := st) (userP K) i.Locks s b ∨ RrRep st i.rptr s b) (fun b hb => Or.inl hb)
      (fun b hb => Or.inr hb) h'' hn'
    show syscall.handle_reply_recv_vm_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a
      (i.rptr, i.ep) = ok r'
    exact (eP a _ s').trans (interp_mono (st := st)
      (fun q hq => Or.elim hq (fun h1 => (ioRS_of_userP h1).2) (fun h2 => RrRep.notPte hK hEP.1.base hE.2.1 h2))
      (fun _ _ => trivial) _ (rr_noZero i.rptr i.ep) s' a r' ((eP a _ s').symm.trans hg))


/-- **The VM-timer path under `QPs`** (`vt_avoidPJ_path`; the accepted case by `vt_noAcc`). -/
theorem vt_avoidPJ_pathA (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotA st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vtSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb)) := by
  have hK' := regionOKV_pteU hK
  have hVU := vcpuNU_pteU hK
  have hP : ∀ s, QPs K st s → VtmP K st i.irq s := fun s hq => vtmP_of_ksb i.irq hq.ks hq.ksb hq.tab
  refine avoidE_of_entry (P := ((vtSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb))
    (E := (· ∈ K.ptes)) (vtimer_noZero i.irq i.pl i.n) (IsProg.on (vtimer_isProg S i.irq i.pl i.n) _ _ _)
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => VexitWS (L := L) K.pteU st i.lk s)
    (fun s x _ hx => (vexitRSU_pteU (L := L) hx).2.2) ?_
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => vexitRSU_pteU (L := L) hx)
    (fun s x hs hx => by
      obtain ⟨hs1, -⟩ := hs
      exact ((show VtPre st i K.toKLayoutV s from hs1.1).ent.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, -⟩ := hs
    have hs' : VtPre st i K.toKLayoutV s := hs1.1
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) := hr
    exact (vt_noAcc ar h.base.nv hs' hr').elim
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VtPre st i K.toKLayoutV s := hs1.1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (false, s1, a1) := hr
      have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl i.n = ok (false, s1, a1) :=
        vtimer_dec_ownU ar hA hK' hVU h.base.Nt (vtmEnt_pteU hK hs' (hP s hq)) (vtmU_pteU (hP s hq)) hr'
      exact g
    · exact absurd rfl hb

/-- **vmF slot under `QPs`** (slot lift). -/
theorem vmF_avoidPJA (i : VmFArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmFSlotA st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vmFSlotA st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (vmFSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (vmF_avoidPJ_pathA st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **vmR slot under `QPs`** (slot lift). -/
theorem vmR_avoidPJA (i : VmRArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vmRSlotA st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vmRSlotA st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (vmRSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (vmR_avoidPJ_pathA st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **vt slot under `QPs`.** -/
theorem vt_avoidPJA (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotA st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vtSlotA st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ P, P = (vtSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (P.rJ K (fun b hb => Or.inl hb)) := by
    rintro P rfl
    exact vt_avoidPJ_pathA st ar hA hm i K m hK hU h
  exact key _ (SlotN.fam_pos _ _ h)

variable (hSt : P0.StoreTotal st) (a0 : A)

/-- **Every path of `fl4LocA`, restricted to `QPs` states, reads no PTE word** (`allW11J` for the new family). -/
theorem allA :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      AvoidP K ((((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm)) i K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb)) := by
  intro i K m hK hU
  by_cases he : K.ptes = ∅
  · exact avoidP_empty he _
  cases i with
  | vmF i =>
    by_cases hp : (fl4LocA st ar hA hm hSt a0).vmF.Prem i K.toKLayoutV m
    · exact vmF_avoidPJA st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | vmR i =>
    by_cases hp : (fl4LocA st ar hA hm hSt a0).vmR.Prem i K.toKLayoutV m
    · exact vmR_avoidPJA st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | io i =>
    by_cases hp : (fl4LocA st ar hA hm hSt a0).io.Prem i K.toKLayoutV m
    · exact io_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | st i =>
    by_cases hp : (fl4LocA st ar hA hm hSt a0).st.Prem i K.toKLayoutV m
    · exact stm_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | irq i =>
    by_cases hp : (fl4LocA st ar hA hm hSt a0).irq.Prem i K.toKLayoutV m
    · exact irq_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | sl i =>
    by_cases hp : (fl4LocA st ar hA hm hSt a0).sl.Prem i K.toKLayoutV m
    · exact sl_avoidPJ_W6 st ar hA hm hSt a0 i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotC.noPre (fl4Dflt st ar hm) _ hp)
  | vq j =>
    cases j with
    | inl i =>
      by_cases hp : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · exact vx_avoidPJ st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)
    | inr i =>
      by_cases hp : (vtSlotA st ar hA hm).Prem i K.toKLayoutV m
      · exact vt_avoidPJA st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)

/-- **`fl4LocA`'s eight paths, each restricted to `QPs` states, PTE-cut and lifted to `ownP`.** -/
def fl4LocW11JA : PathsP (Fl4IxW (S := S)) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _
    (allA st ar hA hm hSt a0 i K m hK hU)

end av

/-! ## The kernel base at every start state of the new family -/

section pre
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (hSt : P0.StoreTotal st) (a0 : A)

/-- **Every start state of `fl4LocA` has the layout's kernel base** (`pre_ksbW6` for the unchanged slots). -/
theorem pre_ksbA (i : Fl4IxW (S := S)) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (σ : ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).S)
    (hσ : ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).Pre σ) :
    @LawfulStore.ksb _ _
      ((fl4LocA st ar hA hm hSt a0).paths (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).L σ = K.ksb := by
  cases i with
  | vmF i =>
    by_cases hp : (vmFSlotA st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (vmFSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : VmPre st ar (userV K.toKLayoutV) i.T i.Cs i.Ω i.U i.H i.Sg i.Rp i.Scs i.Nt i.Z i.Ac i.Locks σ ∧
            AffAg st (userV K.toKLayoutV) m σ := hσ
        exact hs'.1.1.base.kb.symm
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | vmR i =>
    by_cases hp : (vmRSlotA st ar hA hm).Prem i K.toKLayoutV m
    · have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
          (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
          P = (vmRSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
          ∀ σ, (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).Pre σ →
            @LawfulStore.ksb _ _ (LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).L σ
              = K.ksb := by
        rintro P W rfl σ hσ
        have hs' : VmRRPreJ st ar (userV K.toKLayoutV) (userV K.toKLayoutV).heap.tcbs i.Cs i.Ω i.Sg
            (userV K.toKLayoutV).heap.scs (userV K.toKLayoutV).heap.ntfns (userV K.toKLayoutV).heap.scBits i.Ac
            i.Locks i.rptr i.ep σ ∧ AffAg st (userV K.toKLayoutV) m σ := hσ
        exact (VmRRPreJ.pre hs'.1).1.base.kb.symm
      exact key _ _ (SlotU.fam_pos _ _ hp) σ hσ
    · exact absurd hσ (SlotU.noPre (fl4Dflt st ar hm) _ hp σ)
  | io i => exact pre_ksbW6 st ar hA hm hSt a0 (.io i) K m hK hU σ hσ
  | st i => exact pre_ksbW6 st ar hA hm hSt a0 (.st i) K m hK hU σ hσ
  | irq i => exact pre_ksbW6 st ar hA hm hSt a0 (.irq i) K m hK hU σ hσ
  | sl i => exact pre_ksbW6 st ar hA hm hSt a0 (.sl i) K m hK hU σ hσ
  | vq j =>
    cases j with
    | inl i => exact pre_ksbW6 st ar hA hm hSt a0 (.vq (.inl i)) K m hK hU σ hσ
    | inr i =>
      by_cases hp : (vtSlotA st ar hA hm).Prem i K.toKLayoutV m
      · have key : ∀ P, P = (vtSlotA st ar hA hm).path i K.toKLayoutV m hK.base hU.base hp →
            ∀ σ, P.Pre σ → @LawfulStore.ksb _ _ P.L σ = K.ksb := by
          rintro P rfl σ hσ
          have hs' : VtPre st i K.toKLayoutV σ ∧ VtTP K.toKLayoutV st σ := hσ
          exact (ksb_of_stLay (L := L) hs'.1.ent.lay (nodePlaced_of_bxi (L := L) hs'.1.ent.inv) : L.ksb σ = K.ksb)
        exact key _ (SlotN.fam_pos _ _ hp) σ hσ
      · exact absurd hσ (SlotN.noPre (fl4Dflt st ar hm) _ hp σ)

end pre

end
end Fl4Proofs.P2.E2EP
