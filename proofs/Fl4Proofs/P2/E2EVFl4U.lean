/-
P2 (line vlift, gen 5): **the `SlJAt`-based local paths at `userV K` with a `Pre` about the real layout**.

Route U builds a path at `userV K`. For the paths whose `Pre` is P3's bundle `SlJAt K` (the I/O port `io_pathsK`, the
`TCB_SetTimer` path `tm_pathsK`, the timer interrupt `irq_pathsJ3`), taking the existing family member at `userV K`
gives `Pre := SlJAt (userV K)`, false once `K` has a VCPU (`SlJAtZ.lay` pins `user` to the IPC-buffer words). So here
the same bodies are built at `userV K` with `Pre := SlJAt K.toKLayout ∧ …`:

* `VFacts K` [J]: the layout's VCPU facts (`VcpuHeap`, `VcpuTabOff`, `UserObj`, `PoolObj` at every `SlJAt` state; all
  [J] since gen 2, see `P2/E2EVHeap.lean`) and **`wr`** [J] (new): a write to a VCPU data word keeps P3's bundle
  `SlJAt K.toKLayout` (the analogue of slhuf's `SlJAt.userWr` for user words; a VCPU's guest-state words are words of
  an `other 15` heap object that P3's joint invariant, native-scoped (`JExt.nat`), does not read). `slJAt_wrV`: the
  bundle is kept by every write to a `userV K` user word.
* `io_localPathV`: `io_localPathK` (the `ioBodyP` path, `Pre` generic) at `userV K` with `P := SlJAt K.toKLayout ∧ Q`;
  `IoLayA` by `SlJAt.ioLayA` (no `user` field), `IoPre (userV K)` from the `K` one (`ioPre_userV`, `VcpuKs` from
  `slJAt_vfacts`). **`io_noVcpuRWV`**.
* `tm_localPathV`: `set_timer_localPathM` at `userV K` narrowed (`lpRestrict`) to `SlJAt K.toKLayout ∧ Q`, its
  `StEntK (userV K)` from the `K` one (`stEntK_userV`). **`tm_noVcpuRWV`**.
* `IrqPreV K st m := SlJAt K.toKLayout ∧` memory agreement off `userV K`'s user words (closed under those writes),
  `IrqPreV.entM` (`IrqEntM (userV K)` from `SlJAt` via p2lf's `IrqPreJ3.entM` at the state's own memory and
  `irqEnt_userV`; needs `irq < 128`), `irq_pathObl_V` / `irq_pathSide_V` / **`irq_localPathV`** (p2lf gen17's
  `irq_pathObl_J3` / `irq_pathSide_J3` / `irq_localPathJ3`, same proof, at `userV K`), **`irq_noVcpuRWV`**.

Premises: `VFacts` [J]; the paths' own premises, unchanged in kind, now stated at `userV K` where they are about the
path's obligations (`huf` [J], `hro` [W], `hlk` [P], `hEU` / `hNU` [J]) and at `K.toKLayout` where they are about
the start (`hPE`, `hmA` [J]).
-/
import Fl4Proofs.P2.E2EVFam
import Fl4Proofs.P2.E2EVSlD
import Fl4Proofs.P2.E2EVTimerLay
import Fl4Proofs.P2.E2EVUserIo
import Fl4Proofs.P2.SlJStLocTop
import Fl4Proofs.P2.FootTimerIrqJ3
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap (fld oAFFINITY)
open Fl4Proofs.P2.Serial (Owner ClsOwner)

noncomputable section
open Classical

section facts
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- **The layout's VCPU facts** [J] (module docstring). -/
structure VFacts (L : LawfulStore st) (K : KLayoutV) : Prop where
  /-- [J] `VcpuHeap`: the layout's VCPUs are `other 15` heap objects (gen 2; `K.vcpus` is free in P3). -/
  heap : VcpuHeap K
  /-- [J] `VcpuTabOff`: no VCPU meets the ASID-table area (P3 fact that would close it: every heap object lies in
  an untyped). -/
  tab : VcpuTabOff K
  /-- [J] `UserObj`: user words lie in non-VCPU heap objects. -/
  user : UserObj K
  /-- [J] `PoolObj` at every bundle state: ASID pools are non-VCPU heap objects. -/
  pool : ∀ s, SlJAt (L := L) K.toKLayout s → PoolObj (L := L) K s
  /-- [J] a write to a VCPU data word keeps P3's bundle (module docstring). -/
  wr : ∀ s b v, SlJAt (L := L) K.toKLayout s → VData K b → Aligned b → SlJAt (L := L) K.toKLayout (L.wr s b v)

theorem slJAt_ksb {K : OwnMap.KLayout} {s : S} (h : SlJAt (L := L) K s) : L.ksb s = K.ksb := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, B⟩ := h
  exact B.ksb

/-- The bundle is kept by a write to a user word of `userV K`. -/
theorem slJAt_wrV (vf : VFacts L K) {s : S} (h : SlJAt (L := L) K.toKLayout s) {b : U64}
    (hb : b ∈ (userV K).user) (hba : Aligned b) (v : U64) : SlJAt (L := L) K.toKLayout (L.wr s b v) := by
  rcases hb with hb | hb
  · exact h.userWr hb v
  · exact vf.wr s b v h hb hba

theorem VFacts.v (vf : VFacts L K) {s : S} (h : SlJAt (L := L) K.toKLayout s) :
    VcpuKs K ∧ K.ksb.val + 13568 ≤ 2 ^ 64 ∧ HeapOK K.heap ∧ TabNoV (L := L) K s :=
  slJAt_vfacts h vf.heap vf.tab (vf.pool s h)

end facts

/-! ## The I/O port path -/

section io
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {T Cs Ω Sg Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} {K : KLayoutV}
variable {Locks : S → U64 → Prop} {m0 : U64 → U64}
variable {A : Type}

theorem ioLayA_userV (h : IoLayA K.toKLayout) : IoLayA (userV K) := ⟨h.slot8, h.tcb, h.ntfn8, h.sc8⟩

theorem ioPre_userV (hK : RegionOKV K) (hks : VcpuKs K) {s : S}
    (h : IoPre st K.toKLayout T Cs Ω H Sg Rp Scs Nt Z Ac s) : IoPre st (userV K) T Cs Ω H Sg Rp Scs Nt Z Ac s :=
  { h with lay := ioLay_userV hK hks h.lay }

/-- **The I/O port path at `userV K` with `Pre := SlJAt K.toKLayout ∧ Q`** (module docstring). -/
noncomputable def io_localPathV (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (vf : VFacts L K) {number : I64} (hm : E2E.MasksWr st) (Q : S → Prop)
    (hPE : ∀ s, SlJAt (L := L) K.toKLayout s → Q s →
      IoPre st K.toKLayout K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac s)
    (hmA : ∀ s, SlJAt (L := L) K.toKLayout s → Q s → ∀ d, K.heap d = some .tcb →
      m0 (fld d oAFFINITY) = L.mem s (fld d oAFFINITY))
    (huf : ∀ s b v, SlJAt (L := L) K.toKLayout s → Q s → b ∈ (userV K).user → Aligned b →
      Q (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        IoRS (st := st) (userV K) Locks (L.wr s b v) = IoRS (st := st) (userV K) Locks s ∧
        IoWS (st := st) (userV K) Locks (L.wr s b v) = IoWS (st := st) (userV K) Locks s ∧
        IoDS (st := st) (L.wr s b v) = IoDS (st := st) s)
    (hpz : ∃ p : SProg Bool, IsProg (ioBodyP S number) p ∧ NoZero p ∧
      ∀ s s' a r, (SlJAt (L := L) K.toKLayout s ∧ Q s) →
        (¬ ∃ s1 a1, syscall.handle_ioport_local st ar s a number = ok (true, s1, a1)) →
        Alt st (IoRS (st := st) (userV K) Locks s) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m0)
          (· ∈ (userV K).user) s s' →
        interp st ar p s' a = ok r →
        E2E.Once st ar (IoRS (st := st) (userV K) Locks s) (· ∈ (userV K).user) ∅ ∅ p s' a) :
    E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m0) (· ∈ (userV K).user) :=
  io_localPathK (K := userV K) (m0 := m0) (Locks := Locks) ar hA (regionOK_userV hK) (userOK_userV hK hU) hm
    (P := fun s => SlJAt (L := L) K.toKLayout s ∧ Q s) (fun _ h => ioLayA_userV h.1.ioLayA)
    (fun s h => ioPre_userV hK (vf.v h.1).1 (hPE s h.1 h.2)) (fun s h => hmA s h.1 h.2)
    (fun s b v h hb hba => by
      obtain ⟨h1, h2⟩ := huf s b v h.1 h.2 hb hba
      exact ⟨⟨slJAt_wrV vf h.1 hb hba v, h1⟩, h2⟩) hpz

/-- **`NoVcpuRW` of `io_localPathV`.** -/
theorem io_noVcpuRWV (ar : machine.Arch A) (hA : P0.ArchTotal ar) (hK : RegionOKV K) (hU : UserOKV K)
    (vf : VFacts L K) {number : I64} (hm : E2E.MasksWr st) (Q : S → Prop) (hPE) (hmA) (huf) (hpz) :
    NoVcpuRW K (io_localPathV (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (m0 := m0) (Locks := Locks) ar hA hK hU vf
      (number := number) hm Q hPE hmA huf hpz) where
  rd _ _ _ hr := ioRS_noV hr
  wr s _ hp hw := hw.elim (ioWS_noV hK) fun hd =>
    Or.inl (safeW_noV hK (IoDS.safe (ioPre_userV hK (vf.v hp.1).1 (hPE s hp.1 hp.2)) hd).2)

end io

/-! ## The `TCB_SetTimer` path -/

section tm
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {K : KLayoutV} {lk : S → U64 → Prop} {m : U64 → U64}
variable {A : Type}

/-- `StEntK` at `userV K` with the layout's typed heap as P1's ghosts. -/
abbrev StEntV (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (Cs Ω Sg Ac : Set U64) (target : U64)
    (m : U64 → U64) (s : S) : Prop :=
  StEntK (userV K) st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac target m s

/-- **The `TCB_SetTimer` path at `userV K` with `Pre := SlJAt K.toKLayout ∧ Q`** (module docstring). -/
noncomputable def tm_localPathV (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hK : RegionOKV K) (hU : UserOKV K) (vf : VFacts L K) (hm : E2E.MasksWr st) (Q : S → Prop)
    (hPE : ∀ s, SlJAt (L := L) K.toKLayout s → Q s →
      StEntK K.toKLayout st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac
        target m s)
    (hpz : ∃ p : SProg Bool, IsProg (stBody S n target) p ∧ NoZero p ∧
      E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
        (StEntV K st Cs Ω Sg Ac target m) (MaxR (userV K) st lk))
    (hEU : ∀ s b v, StEnt (userV K) st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → b ∈ (userV K).user → Aligned b →
      StEnt (userV K) st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns K.heap.scBits Ac target
        (L.wr s b v))
    (hlk : ∀ s b v, b ∈ (userV K).user → lk (L.wr s b v) = lk s)
    (hNU : ∀ s, StEnt (userV K) st K.heap.tcbs Cs Ω K.heap Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits Ac target s → ∀ o : U64, o.val < 4288 → L.nodeAt s (L.cpu s) o ∉ (userV K).user)
    (huf : ∀ s b v, SlJAt (L := L) K.toKLayout s → Q s → b ∈ (userV K).user → Aligned b → Q (L.wr s b v)) :
    E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user) :=
  lpRestrict
    (set_timer_localPathM (K := userV K) (m := m) (lk := lk) ar n hA (regionOK_userV hK) (userOK_userV hK hU)
      hpz.choose_spec.1 hpz.choose_spec.2.1 hm hpz.choose_spec.2.2 hEU hlk hNU)
    (fun s => SlJAt (L := L) K.toKLayout s ∧ Q s)
    (fun s h => stEntK_userV hK (vf.v h.1).1 (vf.v h.1).2.1 (slJAt_ksb h.1) (hPE s h.1 h.2))
    (fun s b v h hb hba => ⟨slJAt_wrV vf h.1 hb hba v, huf s b v h.1 h.2 hb hba⟩)

/-- **`NoVcpuRW` of `tm_localPathV`.** -/
theorem tm_noVcpuRWV (ar : machine.Arch A) (hA : P0.ArchTotal ar) (n : I64) (target : U64)
    (hK : RegionOKV K) (hU : UserOKV K) (vf : VFacts L K) (hm : E2E.MasksWr st) (Q : S → Prop)
    (hPE) (hpz) (hEU) (hlk) (hNU) (huf) :
    NoVcpuRW K (tm_localPathV (Cs := Cs) (Ω := Ω) (Sg := Sg) (Ac := Ac) (lk := lk) (m := m) ar hA n target hK hU vf
      hm Q hPE hpz hEU hlk hNU huf) where
  rd _ _ _ hr := maxR_noV hr
  wr s _ hp hw := hw.elim (maxW_noV hK) fun hd =>
    Or.inl (stDec_noV hK (stEntK_userV hK (vf.v hp.1).1 (vf.v hp.1).2.1 (slJAt_ksb hp.1) (hPE s hp.1 hp.2)).ent hd)

end tm

/-! ## The timer interrupt path -/

section irqpre
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- The timer interrupt's `Pre` at `userV K`: P3's bundle for the real layout and the store agreeing with the model
memory `m` on aligned words that are not `userV K` user words. -/
def IrqPreV (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (m : U64 → U64) (s : S) : Prop :=
  SlJAt (L := L) K.toKLayout s ∧ ∀ x, Aligned x → x ∉ (userV K).user → L.mem s x = m x

/-- `IrqEntM (userV K)` at an `IrqPreV` state (word sets chosen per state). -/
theorem IrqPreV.entM (hK : RegionOKV K) (vf : VFacts L K) {m : U64 → U64} {s : S} {irq : U64}
    (hirq : irq.val < 128) (h : IrqPreV K st m s) :
    ∃ Ω Ac : Set U64, IrqEntM (userV K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap
      (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac
      irq m s := by
  obtain ⟨Ω, Ac, hE⟩ := IrqPreJ3.entM (st := st) (m := L.mem s) (irq := irq) ⟨h.1, fun _ _ _ => rfl⟩
  obtain ⟨hks, hf, -, hT⟩ := vf.v h.1
  exact ⟨Ω, Ac, irqEnt_userV hK hks hf (slJAt_ksb h.1) hirq hT hE.ent, h.2⟩

end irqpre

section irq
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {K : KLayoutV} {irq : U64} {m : U64 → U64}
variable {A : Type} (ar : machine.Arch A) {pl : localtimer.TimerIrqPlan}
variable {lk : S → U64 → Prop} {p : PathObl.SProg Bool}

/-- **`PathObl` of the timer interrupt at one `IrqPreV` state** (`irq_pathObl_J3`'s proof at `userV K`). -/
theorem irq_pathObl_V (hA : P0.ArchTotal ar) (hKV : RegionOKV K) (hUV : UserOKV K) (vf : VFacts L K)
    (hirq : irq.val < 128) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hPL : PlanLk lk pl) {s0 : S} (h0 : IrqPreV K st m s0) :
    PathObl.PathObl st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a irq pl) (fun b => b = true)
      (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user) lk
      (fun s => s = s0) (MaxR (userV K) st lk) (MaxW (userV K) st lk) (IrqDec st) := by
  have hK := regionOK_userV hKV
  have hUO := userOK_userV hKV hUV
  obtain ⟨Ω, Ac, hE⟩ := h0.entM hKV vf hirq
  have hQ := slJAt_slotJC (st := st) h0.1
  have hOL : ObjLay (userV K) K.heap (Heap.replies K.heap) := hQ.slotJ.objLay (fun r hr => hr)
  have hSL : SlotLayV (userV K) st (Heap.tcbs K.heap) s0 := hQ.slotJ.slotLayV (fun y hy => hy)
  refine irq_pathObl ar hA hK hUO (P := fun s => s = s0) (fun s e => by subst e; exact hE.ent)
    (fun mm => hp A ar mm) hz hm (fun s e q hq => by subst e; exact irq_koF hE.ent hq)
    (Fl4Proofs.P2.ko_aligned hK hUO) ?_ ?_
  · rintro s a s1 a1 rfl hf h
    by_cases hnw : NoWake st s
    · exact irq_acc_fire_nw ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := hQ.bufAt
      exact irq_acc_fire_wk2 ar hA hK hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        hOL hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h) hSL hf hnw h
  · rintro s a s1 a1 rfl h
    refine irq_move_acc ar hA hK hUO hp hE.k (fun hf => ?_) h
    by_cases hnw : NoWake st s
    · exact irq_move_fire_nw ar hA hK hUO hp hE.k hE.ent.ly hE.ent.nth hf hnw h
    · obtain ⟨U, hB⟩ := hQ.bufAt
      exact irq_move_fire_wk2 ar hA hK hUO hp hE.k hE.ent.ly hE.ent.aff hE.ent.nth
        hOL hPL (irq_bufAt_runB ar hA hE.ent.inv hB hf h) hf hnw h

/-- **`PathSide` of the timer interrupt under `IrqPreV`** (`irq_pathSide_J3`'s proof at `userV K`; `user_free`
from `slJAt_wrV`). -/
theorem irq_pathSide_V (hA : P0.ArchTotal ar) (hKV : RegionOKV K) (hUV : UserOKV K) (vf : VFacts L K)
    (hirq : irq.val < 128) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hlk : ∀ s b v, SlJAt (L := L) K.toKLayout s → b ∈ (userV K).user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) :
    PathObl.PathSide st (fun mm s a => localtimer.handle_timer_irq_local mm ar s a irq pl) (OwnMap.cls (userV K))
      (OwnMap.ko (userV K) m) (· ∈ (userV K).user) lk (IrqPreV K st m) (MaxR (userV K) st lk)
      (MaxW (userV K) st lk) (IrqDec st) := by
  have hK := regionOK_userV hKV
  have hUO := userOK_userV hKV hUV
  refine ⟨?_, fun s x _ hx => hx.2.1, Fl4Proofs.P2.ko_aligned hK hUO, ?_⟩
  · intro s s' a r hP hAlt h
    obtain ⟨Ω, Ac, hE⟩ := hP.entM hKV vf hirq
    have O := irq_pathObl_V ar hA hKV hUV vf hirq hp hz hm hPL hP
    have eP : ∀ (mm : machine.Store S) (x : S),
        localtimer.handle_timer_irq_local mm ar x a irq pl = interp mm ar p x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    rcases irq_alt ar hA hK (fun mm => hp A ar mm) hz hm hE.ent
      (fun s1 a1 _ h1 => O.acc s a (true, s1, a1) rfl h1 rfl) hAlt h with ⟨_, _, -, -, h2⟩ | ⟨_, _, -, -, h2⟩
    · show localtimer.handle_timer_irq_local _ ar s' a irq pl = ok r
      rw [eP] at h2 ⊢
      exact interp_mono (fun _ hw => hw.2.1) (fun _ _ => trivial) p hz s' a r h2
    · show localtimer.handle_timer_irq_local _ ar s' a irq pl = ok r
      rw [eP] at h2 ⊢
      exact interp_mono (fun _ hw => hw) (fun _ _ => trivial) p hz s' a r h2
  · intro s b v h hb hba
    have keep : ∀ x, Aligned x → x ∉ (userV K).user → L.mem (L.wr s b v) x = L.mem s x :=
      fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (e ▸ hb))
    have eo : OwnMap.own (userV K) (L.mem (L.wr s b v)) = OwnMap.own (userV K) (L.mem s) :=
      E2E.ownDep hK hUO _ _ (fun x hx hxu => keep x hx hxu)
    have hl := hlk s b v h.1 hb hba
    refine ⟨⟨slJAt_wrV vf h.1 hb hba v, fun x hx hxu => by rw [keep x hx hxu]; exact h.2 x hx hxu⟩,
      hl, ?_, ?_, irq_dec_user s b v⟩
    · funext w; simp only [MaxR, RPerm, GateOnly, eo, hl, L.cpu_wr]
    · funext w; simp only [MaxW, WPerm, eo, hl, L.cpu_wr]

/-- **The timer interrupt local path at `userV K` with `Pre := IrqPreV K st m`** (module docstring). Premises:
`hA`, `vf` [J], `hirq` (the timer IRQ is 2), `hp` [P], `hz` [W], `hm` [P], `hro` [W] (`ReadOnce` under `IrqPreV`),
`hlk` [P] (guarded lock contract, for `userV K`'s user words), `hPL` [P]. -/
noncomputable def irq_localPathV (hA : P0.ArchTotal ar) (hKV : RegionOKV K) (hUV : UserOKV K) (vf : VFacts L K)
    (hirq : irq.val < 128) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro : E2E.ReadOnce st ar p (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
      (IrqPreV K st m) (MaxR (userV K) st lk))
    (hlk : ∀ s b v, SlJAt (L := L) K.toKLayout s → b ∈ (userV K).user → Aligned b → lk (L.wr s b v) = lk s)
    (hPL : PlanLk lk pl) :
    E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user) :=
  { S := S
    A := A
    X := Bool
    st := st
    L := L
    ar := ar
    F := irqBody S irq pl
    p := p
    Acc := fun b => b = true
    Locks := lk
    Pre := IrqPreV K st m
    RS := MaxR (userV K) st lk
    WS := MaxW (userV K) st lk
    DS := IrqDec st
    isProg := PathObl.IsProg.on hp _ _ _
    obl := irq_obl_of_pt fun _ h0 => irq_pathObl_V ar hA hKV hUV vf hirq hp hz hm hPL h0
    side := irq_pathSide_V ar hA hKV hUV vf hirq hp hz hm hlk hPL
    once := hro
    total := fun s a => by
      obtain ⟨r, e, -⟩ := spec_ex_fd (P0.localtimer.handle_timer_irq_local.p0 st ar s a irq pl LawfulStore.total hA)
      exact ⟨r, e⟩
    masks := hm }

/-- **`NoVcpuRW` of `irq_localPathV`.** -/
theorem irq_noVcpuRWV (hA : P0.ArchTotal ar) (hKV : RegionOKV K) (hUV : UserOKV K) (vf : VFacts L K)
    (hirq : irq.val < 128) (hp : IsProg (irqBody S irq pl) p) (hz : NoZero p) (hm : E2E.MasksWr st)
    (hro) (hlk) (hPL : PlanLk lk pl) :
    NoVcpuRW K (irq_localPathV (m := m) ar hA hKV hUV vf hirq hp hz hm hro hlk hPL) where
  rd _ _ _ hr := maxR_noV hr
  wr s _ hP hw := hw.elim (maxW_noV hKV) fun hd => by
    obtain ⟨Ω, Ac, hE⟩ := IrqPreV.entM (irq := irq) hKV vf hirq hP
    exact Or.inl (irqDec_noV hKV hE.ent hd)

end irq

end
end Fl4Proofs.P2.E2EV
