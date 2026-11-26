/-
P2 (line vlift, gen 5): **the shape of FL4's local-path family under rule 7**, over per-path `LocalPath` values.

`E2E.Paths ι` asks a path for *every* layout `K`, so a path's own premises had to hold for every `K` (false in general
for layout facts such as `VcpuHeap K`), and route U (`PathsV.ofPathsU`) evaluates the family at `userV K`, a
`KLayout` that no longer knows `K`: a path whose `Pre` is P3's bundle `SlJAt K` is then asked `SlJAt (userV K)`,
which is false as soon as `K` has a VCPU (`SlJAtZ.lay` pins the layout's `user` to the IPC-buffer words). This module
fixes both:

* `PathsUV ι` (route U) and `PathsCV ι` (route C): the paths per **`KLayoutV`** `K`, at `userV K` resp. at
  `K.toKLayout`; a route-U path can thus keep a `Pre` about the real layout `K.toKLayout` (e.g. `SlJAt K.toKLayout`)
  while its obligations are at `userV K`. `PathsV.ofU` / `PathsV.ofC` lift them (`LocalPath.atV` + `liftV`, resp.
  `LocalPath.cutLiftV`); `PathsV.ofPathsU` / `ofPathsCut` are the special cases `ofU_paths` / `ofC_paths` (`rfl`).
* **Conditional slots** `SlotU ι` / `SlotC ι`: a path given only where its premises `Prem i K m` hold, with its lift
  premise (`NoVcpuRW` [W] resp. `AvoidV` [W]) under the same condition. `SlotU.fam` / `SlotC.fam` complete it to every
  layout with the empty path `LocalPath.void` (`Pre := False`, so it is never started). The premises are thus asked
  only at the layouts and memories where the glue starts the path (`Fl4StepV.start` [P] has to produce
  `StartAt` of the slot's path, which for `void` is impossible): `SlotU.startAt` / `SlotC.startAt`.
* **`Fl4Loc`**: FL4's local paths, one slot each: VM fault (`vmF`), VM ReplyRecv (`vmR`), I/O port (`io`),
  `TCB_SetTimer` (`st`), timer interrupt (`irq`) by route U; syscall_local (`sl`) by route C; and `vq : PathsV ν`, the
  paths stated directly for `ownV` (lvm's `vexit_localPath` / `vexit_localPathP`, the coming `vtimer_localPath`).
  `Fl4Ix` indexes the union; `Fl4Loc.paths : PathsV (Fl4Ix …)`.
* **`serializable_fl4_localG`**: every `ExecV` over `Fl4Loc.paths` that reaches a state with no local path in progress
  is serializable (`RunAll`). The concrete slots are built in `P2/E2EVFl4.lean` (the top theorem
  `serializable_fl4_local` and its premise table are there).

Premises: `serializable_e2eV`'s; per slot, its `Prem` (asked only where the slot's path starts) and the lift premise
under it.
-/
import Fl4Proofs.P2.E2EVAll
import Fl4Proofs.P2.MoveOwn
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.PathObl Fl4Proofs.P2.E2E Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## Families per `KLayoutV` -/

/-- Route-U paths: per `KLayoutV` `K`, a path at `userV K` (its `Pre` may speak of `K` itself). -/
abbrev PathsUV (ι : Type) : Type 1 :=
  ι → ∀ (K : KLayoutV) (m : U64 → U64), RegionOKV K → UserOKV K →
    LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)

/-- Route-C paths: per `KLayoutV` `K`, a path at `K.toKLayout`. -/
abbrev PathsCV (ι : Type) : Type 1 :=
  ι → ∀ (K : KLayoutV) (m : U64 → U64), RegionOKV K → UserOKV K →
    LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)

/-- **Route U, per `KLayoutV`**: each path un-usered (`LocalPath.atV`) and lifted (`liftV`), given `NoVcpuRW` [W]. -/
def PathsV.ofU {ι : Type} (LU : PathsUV ι)
    (hW : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K), NoVcpuRW K (LU i K m hK hU)) : PathsV ι :=
  fun i K m hK hU =>
    LocalPath.liftV hK (LocalPath.atV hK _ (hW i K m hK hU)) (noVcpuRd_atV hK _ (hW i K m hK hU))

/-- **Route C, per `KLayoutV`**: each path cut to `rsV` and lifted, given `AvoidV` [W]. -/
def PathsV.ofC {ι : Type} (LC : PathsCV ι)
    (hAv : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K), AvoidV K (LC i K m hK hU)) : PathsV ι :=
  fun i K m hK hU => LocalPath.cutLiftV hK hU (fun x ⟨_, hv, _⟩ => ko_vcpu hK hv m) _ (hAv i K m hK hU)

theorem ofU_paths {ι : Type} (LP : Paths ι)
    (hW : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      NoVcpuRW K (LP i (userV K) m (regionOK_userV hK) (userOK_userV hK hU))) :
    PathsV.ofPathsU LP hW =
      PathsV.ofU (fun i K m hK hU => LP i (userV K) m (regionOK_userV hK) (userOK_userV hK hU)) hW := rfl

theorem ofC_paths {ι : Type} (LP : Paths ι)
    (hAv : ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K),
      AvoidV K (LP i K.toKLayout m hK.base hU.base)) :
    PathsV.ofPathsCut LP hAv = PathsV.ofC (fun i K m hK hU => LP i K.toKLayout m hK.base hU.base) hAv := rfl

/-! ## The empty path -/

/-- A store and an Arch instance to build the empty path on (FL4's own: any `LawfulStore` with `MasksWr` [P]). -/
structure Dflt : Type 1 where
  S : Type
  A : Type
  st : machine.Store S
  L : LawfulStore st
  ar : machine.Arch A
  masks : @MasksWr S st L

section void
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64}
  {ko : U64 → ClsOwner U64} {User : U64 → Prop}

/-- **The empty path**: `Pre := False`, so it is never started (`StartAt` asks `Pre`); every obligation is vacuous
but `ko_aligned`, a fact about the layout. -/
def LocalPath.void (D : Dflt) (hko : ∀ x, ko x ≠ .free → Aligned x) : LocalPath own cls ko User where
  S := D.S
  A := D.A
  X := Unit
  st := D.st
  L := D.L
  ar := D.ar
  F := fun _ _ s a => ok ((), s, a)
  p := .ret ()
  Acc := fun _ => False
  Locks := fun _ _ => False
  Pre := fun _ => False
  RS := fun _ _ => False
  WS := fun _ _ => False
  DS := fun _ _ => False
  isProg := fun _ _ _ h _ => by obtain ⟨_, h0, _⟩ := h; exact h0.elim
  obl := by
    letI := D.L
    exact { acc := fun _ _ _ h => h.elim
            dec_alt := fun _ _ _ h => h.elim
            read_own := fun _ _ h => h.elim
            write_own := fun _ _ h => h.elim
            aligned := fun _ _ h => h.elim
            move := fun _ _ _ h => h.elim }
  side := by
    letI := D.L
    exact { read_aligned := fun _ _ _ _ h => h.elim
            rs_aligned := fun _ _ h => h.elim
            ko_aligned := hko
            user_free := fun _ _ _ h => h.elim }
  once := fun _ _ _ _ h => h.elim
  total := fun _ _ => ⟨_, rfl⟩
  masks := D.masks

theorem LocalPath.void_pre (D : Dflt) (hko : ∀ x, ko x ≠ .free → Aligned x) {σ : D.S} :
    ¬ (LocalPath.void (own := own) (cls := cls) (User := User) D hko).Pre σ := id

end void

theorem noVcpuRW_void {K : KLayoutV} {m : U64 → U64} (D : Dflt) (hko) :
    NoVcpuRW K (m := m) (LocalPath.void D hko) where
  rd _ _ h := h.elim
  wr _ _ h := h.elim

theorem avoidV_void {K : KLayoutV} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}
    (D : Dflt) (hko) : AvoidV K (LocalPath.void (own := OwnMap.own K.toKLayout) (cls := cls) (ko := ko)
      (User := User) D hko) where
  acc _ _ _ h := h.elim
  dec _ _ _ h := h.elim
  prog _ _ _ h _ := by obtain ⟨_, h0, _⟩ := h; exact h0.elim

/-! ## Conditional slots -/

/-- **A route-U slot**: a path at `userV K` where `Prem i K m` holds, with `NoVcpuRW` [W] there. -/
structure SlotU (ι : Type) : Type 1 where
  Prem : ι → KLayoutV → (U64 → U64) → Prop
  path : ∀ i (K : KLayoutV) m, RegionOKV K → UserOKV K → Prem i K m →
    LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)
  W : ∀ i K m hK hU h, NoVcpuRW K (path i K m hK hU h)

/-- **A route-C slot**: a path at `K.toKLayout` where `Prem i K m` holds, with `AvoidV` [W] there. -/
structure SlotC (ι : Type) : Type 1 where
  Prem : ι → KLayoutV → (U64 → U64) → Prop
  path : ∀ i (K : KLayoutV) m, RegionOKV K → UserOKV K → Prem i K m →
    LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m) (· ∈ K.user)
  Av : ∀ i K m hK hU h, AvoidV K (path i K m hK hU h)

/-- The slot completed to every layout by the empty path. -/
def SlotU.fam {ι : Type} (D : Dflt) (X : SlotU ι) : PathsUV ι :=
  fun i K m hK hU => if h : X.Prem i K m then X.path i K m hK hU h else
    LocalPath.void D (OwnMap.ko_aligned (regionOK_userV hK) (userOK_userV hK hU) m)

def SlotC.fam {ι : Type} (D : Dflt) (X : SlotC ι) : PathsCV ι :=
  fun i K m hK hU => if h : X.Prem i K m then X.path i K m hK hU h else
    LocalPath.void D (OwnMap.ko_aligned hK.base hU.base m)

theorem SlotU.famW {ι : Type} (D : Dflt) (X : SlotU ι) :
    ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K), NoVcpuRW K (X.fam D i K m hK hU) := by
  intro i K m hK hU
  unfold SlotU.fam
  split
  · exact X.W _ _ _ _ _ _
  · exact noVcpuRW_void _ _

theorem SlotC.famAv {ι : Type} (D : Dflt) (X : SlotC ι) :
    ∀ i (K : KLayoutV) m (hK : RegionOKV K) (hU : UserOKV K), AvoidV K (X.fam D i K m hK hU) := by
  intro i K m hK hU
  unfold SlotC.fam
  split
  · exact X.Av _ _ _ _ _ _
  · exact avoidV_void _ _

/-- The slot lifted to `ownV`. -/
def SlotU.lift {ι : Type} (D : Dflt) (X : SlotU ι) : PathsV ι := PathsV.ofU (X.fam D) (X.famW D)

def SlotC.lift {ι : Type} (D : Dflt) (X : SlotC ι) : PathsV ι := PathsV.ofC (X.fam D) (X.famAv D)

theorem SlotU.fam_pos {ι : Type} (D : Dflt) (X : SlotU ι) {i : ι} {K : KLayoutV} {m : U64 → U64}
    {hK : RegionOKV K} {hU : UserOKV K} (h : X.Prem i K m) : X.fam D i K m hK hU = X.path i K m hK hU h :=
  dif_pos h

theorem SlotC.fam_pos {ι : Type} (D : Dflt) (X : SlotC ι) {i : ι} {K : KLayoutV} {m : U64 → U64}
    {hK : RegionOKV K} {hU : UserOKV K} (h : X.Prem i K m) : X.fam D i K m hK hU = X.path i K m hK hU h :=
  dif_pos h

/-- **Starting a route-U slot**: where its premises hold, a start state of the slot's path (its `Pre`, core, locks,
memory link) is a start of the lifted slot (the glue's `Fl4StepV.start` [P] for this slot). -/
theorem SlotU.startAt {ι : Type} (D : Dflt) (X : SlotU ι) {i : ι} {K : KLayoutV} {m : U64 → U64}
    {hK : RegionOKV K} {hU : UserOKV K} (h : X.Prem i K m) {c : U64} {hs : U64 → Prop} {μ : U64 → U64}
    (σ : (X.path i K m hK hU h).S) (a : (X.path i K m hK hU h).A) (hP : (X.path i K m hK hU h).Pre σ)
    (hc : (X.path i K m hK hU h).L.cpu σ = c) (hl : (X.path i K m hK hU h).Locks σ = hs)
    (hμ : ∀ x, Aligned x → x ∉ K.user → (X.path i K m hK hU h).L.mem σ x = μ x) :
    ∃ q, StartAt (X.lift D i K m hK hU) c hs μ q := by
  have key : ∀ P (W : NoVcpuRW K P), P = X.path i K m hK hU h →
      ∃ q, StartAt (LocalPath.liftV hK (LocalPath.atV hK P W) (noVcpuRd_atV hK P W)) c hs μ q := by
    rintro P W rfl
    exact ⟨_, σ, a, hP, hc, hl, hμ, rfl⟩
  exact key _ _ (X.fam_pos D h)

theorem SlotC.startAt {ι : Type} (D : Dflt) (X : SlotC ι) {i : ι} {K : KLayoutV} {m : U64 → U64}
    {hK : RegionOKV K} {hU : UserOKV K} (h : X.Prem i K m) {c : U64} {hs : U64 → Prop} {μ : U64 → U64}
    (σ : (X.path i K m hK hU h).S) (a : (X.path i K m hK hU h).A) (hP : (X.path i K m hK hU h).Pre σ)
    (hc : (X.path i K m hK hU h).L.cpu σ = c) (hl : (X.path i K m hK hU h).Locks σ = hs)
    (hμ : ∀ x, Aligned x → x ∉ K.user → (X.path i K m hK hU h).L.mem σ x = μ x) :
    ∃ q, StartAt (X.lift D i K m hK hU) c hs μ q := by
  have key : ∀ P (W : AvoidV K P), P = X.path i K m hK hU h →
      ∃ q, StartAt (LocalPath.cutLiftV hK hU (fun x ⟨_, hv, _⟩ => ko_vcpu hK hv m) P W) c hs μ q := by
    rintro P W rfl
    exact ⟨_, σ, a, hP, hc, hl, hμ, rfl⟩
  exact key _ _ (X.fam_pos D h)

/-! ## FL4's local paths -/

/-- **FL4's local-path family under rule 7** (module docstring): five route-U slots, one route-C slot, and the
paths stated directly for `ownV`. -/
structure Fl4Loc (ιF ιR ιI ιS ιT ιL ν : Type) : Type 1 where
  /-- VM fault (`handle_vm_fault_local`). -/
  vmF : SlotU ιF
  /-- VM ReplyRecv (`handle_vm_reply_recv_local`). -/
  vmR : SlotU ιR
  /-- I/O port (`handle_ioport_local`). -/
  io : SlotU ιI
  /-- `TCB_SetTimer` (`handle_set_timer_local`). -/
  st : SlotU ιS
  /-- The timer interrupt (`handle_timer_irq_local`). -/
  irq : SlotU ιT
  /-- syscall_local (`handle_syscall_local`: trap arm and ReplyRecv fast path). -/
  sl : SlotC ιL
  /-- Paths stated for `ownV` (lvm: `vexit_localPath`, `vexit_localPathP`, `vtimer_localPath`). -/
  vq : PathsV ν

/-- Which local path, with which arguments. -/
inductive Fl4Ix (ιF ιR ιI ιS ιT ιL ν : Type) : Type where
  | vmF (i : ιF) | vmR (i : ιR) | io (i : ιI) | st (i : ιS) | irq (i : ιT) | sl (i : ιL) | vq (j : ν)

/-- **The family**: every slot lifted to `ownV`. -/
def Fl4Loc.paths {ιF ιR ιI ιS ιT ιL ν : Type} (D : Dflt) (F : Fl4Loc ιF ιR ιI ιS ιT ιL ν) :
    PathsV (Fl4Ix ιF ιR ιI ιS ιT ιL ν)
  | .vmF i => F.vmF.lift D i
  | .vmR i => F.vmR.lift D i
  | .io i => F.io.lift D i
  | .st i => F.st.lift D i
  | .irq i => F.irq.lift D i
  | .sl i => F.sl.lift D i
  | .vq j => F.vq j

/-- **End to end over FL4's local-path family** (module docstring; generic in the slots). -/
theorem serializable_fl4_localG {ιF ιR ιI ιS ιT ιL ν : Type} (D : Dflt) (F : Fl4Loc ιF ιR ιI ιS ιT ιL ν)
    {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutV} (h0 : Init s0) (hA0 : ArmInv s0)
    (hK0 : RegionOKV K0) (hU0 : UserOKV K0) (hM0 : MapsV K0 s0)
    (h : ExecV (F.paths D) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eV _ h0 hA0 hK0 hU0 hM0 h hq

end
end Fl4Proofs.P2.E2EV
