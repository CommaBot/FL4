/-
P2 (line nscope, gen 3): **the PTE layout facts as start-state facts**: `P3AvJ` and **`serializable_fl4_localP3J`**.

**Why not a layout-level choice of `K.ptes`** (gen 2's gap 3, settled). `K.toKLayout` is `layoutJ Zx H ksb n`
(P2/OwnJAtZ.lean): heap, kernel base, cores, slot addresses, IPC-buffer words. It does not see the VSpace ghost sets
(`Zx.L4 … Zx.L1`, `Zx.P`), and `H` records a page table and an ASID pool alike as `.other 12` (P3 `SpecCover.arch`).
So two reachable bundle states can share `K.toKLayout` while the 4 KiB object at `q` is a page table at one (in
`Zx.L1`, written by PageMap) and an ASID pool named by the ASID table at the other (delete the table, retype the
same untyped region into a pool via ASIDControl: `H`, the slot addresses and the IPC-buffer words are unchanged).
Then:
* `PteSl` (all bundle states of `K.toKLayout`) forbids `q`'s words in `K.ptes` (they are pool words at the second
  state), so `PtePlanLocked`'s [J] half (the planned leaf entry is in `K.ptes`) fails for PageMap into `q` at the
  first; in particular **`ptesK` (gen 2) is too small**: it drops every such table.
* Any `K.ptes` containing `q`'s words falsifies `PteSl` (and `VtmP` / `VxP`' table half) at the second state.
No set-valued choice satisfies both halves; the existing statements' all-states quantifier is the obstacle.
(A ghost witness can also omit a mapped table, P3 `PtRel` being one-directional, which shrinks `ptesK` further.)

**The per-state restatement.** The facts are true at the states that matter: the starts of local paths in one
serial epoch (between two serial steps `K` is fixed, `Fl4StepP.keep`). With the glue's choice at the serial exit
state `s'` (bundle ghost `Zx'`), **`K.ptes ⊆ ptesJ Zx'`** [P]:
* `KsNoE` and the user-word facts are layout facts, proved at `s'` (`qPs_of_bundle`);
* `L.ksb s = K.ksb` at every state (`ksb_wr`);
* `TabNoE` at a start `s` of the epoch reads only the 2048 ASID-table words; they are region `.none`, no PTE and
  no user words, so gate-owned under `ownP`: no local path writes them, and hardware writes only VCPU words. So
  they equal their values at `s'`, where `TabNoE` holds (`pteSlAt_of`).
* PageMap's walk from a valid ASID runs through `Zx'.P → Zx'.L4 → … → Zx'.L1` for every witness at `s'`
  (`VsRel`, `PoolsIn`, the `PxERel`s), and the upper levels and ASID words are gate-owned in the epoch: the planned
  entry is in `ptesJ Zx'` (`PtePlanLocked`'s [J] half, for the PageMap path still to be written, pte gap 2).

So the facts move from the layout into each path's `Pre`:
* `QPs K st s` (state predicate): `KsNoE`, `L.ksb s = K.ksb`, `TabNoE` at `s`, the ASID-table words aligned, and no
  user (or VCPU-data) word is an ASID-table word. Kept by aligned user writes (`QPs.wr`).
* `LocalPath.restrQ P Q hQ` (generic): `P` with `Pre ∧ Q`; every obligation is inherited. `LocalPath.rJ K P` =
  `restrQ` by `QPs`. `avoidE_restrQ`, `avoidV_restrQ`, `noVcpuRW_restrQ` (monotonicity), and the two commuting
  steps through the slot lifts (`avoidE_cutLiftV_rJ`, `avoidE_liftAtV_rJ`, by `rfl` on the lifted paths).
* The five slots that read the layout facts, re-proved under `Pre ∧ QPs` (copies of pte's proofs with `PteSl` /
  `VtmP` / `VxP` replaced by the state's `QPs`): `sl_avoidPJ` (`sl_avoidVKE_rQ`), `stm_avoidPJ`, `irq_avoidPJ`,
  `vt_avoidPJ`, `vx_avoidPJ`. The other three (vmF, vmR, io) by `avoidE_restrQ` from their [W].
* **`P3AvJ`** = `P3AvP4` − `pteSl` − `vtP` − `vxP` (3 [W] left: vmF, vmR, io; `P3AvJ.ofP4`), the family
  **`fl4LocP3J`** (every `fl4LocP3W` path restricted by `QPs`, PTE-cut, lifted to `ownP`), and
  **`serializable_fl4_localP3J`**.

Glue obligation ([P], inside `ExecP`'s `Fl4StepP.start`): a local path is started at a state satisfying its `Pre`
and `QPs K st s` for the epoch's `K`; satisfiable with `K.ptes ⊆ ptesJ Zx'` by the argument above
(`qPs_of_bundle` at bundle states with that ghost). No existing statement or file changed.
-/
import Fl4Proofs.P2.E2EPStm
import Fl4Proofs.P2.E2EPJ
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

/-! ## The state predicate -/

section qps
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

/-- **The PTE facts at one state** (module docstring). -/
structure QPs (K : KLayoutP) (st : machine.Store S) [L : LawfulStore st] (s : S) : Prop where
  ks : KsNoE (· ∈ K.ptes) K.toKLayoutV
  ksb : L.ksb s = K.ksb
  tab : TabNoE (L := L) (· ∈ K.ptes) s
  al : ∀ hi : U64, hi.val < 2048 → Aligned (atAF K.ksb hi)
  uoff : ∀ b, (b ∈ K.user ∨ VData K.toKLayoutV b) → ∀ hi : U64, hi.val < 2048 → b ≠ atAF K.ksb hi

theorem QPs.ksw {K : KLayoutP} {s : S} (h : QPs K st s) {o : U64} (ho : o.val < 13568) :
    core.num.U64.wrapping_add (L.ksb s) o ∉ K.ptes := by
  rw [h.ksb]; exact h.ks o ho

/-- **`QPs` is kept by an aligned user (or VCPU-data) write.** -/
theorem QPs.wr {K : KLayoutP} {s : S} {b v : U64} (h : QPs K st s) (hb : b ∈ K.user ∨ VData K.toKLayoutV b)
    (ha : Aligned b) : QPs K st (L.wr s b v) := by
  have hk : L.ksb (L.wr s b v) = L.ksb s := L.ksb_wr s b v
  have hm : ∀ hi : U64, hi.val < 2048 →
      L.mem (L.wr s b v) (atAF (L.ksb s) hi) = L.mem s (atAF (L.ksb s) hi) := by
    intro hi hhi
    rw [h.ksb]
    exact Fl4Proofs.P3.Notif.rd_wr_ne ha (h.al hi hhi) (h.uoff b hb hi hhi)
  refine ⟨h.ks, hk.trans h.ksb, ?_, h.al, h.uoff⟩
  intro hi hhi
  rw [hk]
  obtain ⟨t1, t2⟩ := h.tab hi hhi
  refine ⟨t1, fun lo hlo hne => ?_⟩
  rw [hm hi hhi] at hne ⊢
  exact t2 lo hlo hne

/-- **`QPs` at a bundle state** whose ghost's page-table words contain `K.ptes` (the glue's choice; P3 scope:
no VCPU). -/
theorem qPs_of_bundle {K : KLayoutP} {s : S} {A' : Type} {arI : machine.Arch A'} {AR : A' → Fl4Spec.Cr3 → Prop}
    {Zx : Fl4Proofs.P3.XSets} {Cx Ax : Set U64} {Lst : U64 → List U64} {D : Set U64} {a' : A'}
    {σ : Fl4Spec.State Unit} (B : SlJAtZ (L := L) arI AR Zx Cx Ax Lst D K.toKLayout s a' σ)
    (hsub : K.ptes ⊆ ptesJ Zx) (nv : K.vcpus = ∅) : QPs K st s := by
  obtain ⟨hks, htab⟩ := pteSlAt_of B hsub
  have hk : L.ksb s = K.ksb := B.ksb
  have hTP := B.j.xtop.fin.1.2
  have hfit : (L.ksb s).val + 288000 + 16384 ≤ 2 ^ 64 := hTP.vs.ksb_fit
  have hal8 : (L.ksb s).val % 8 = 0 := hTP.vs.ksb_al
  have hv : ∀ hi : U64, hi.val < 2048 → (atAF (L.ksb s) hi).val = (L.ksb s).val + 288000 + 8 * hi.val :=
    fun hi hhi => Fl4Proofs.P3.Vs.atA_val hfit hhi
  refine ⟨hks, hk, htab, fun hi hhi => ?_, fun b hb hi hhi hbe => ?_⟩
  · rw [← hk]; show (atAF (L.ksb s) hi).val % 8 = 0; rw [hv hi hhi]; omega
  · rcases hb with hb | hb
    · have hU : K.user = {b | ∃ wp ∈ Zx.B, wp.1 = b} := B.user
      rw [hU] at hb
      obtain ⟨wp, hwp, hwb⟩ := hb
      rw [← hk] at hbe
      have hbv := hv hi hhi
      rw [← hbe] at hbv
      apply hTP.disj b (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨wp, hwp, by rw [hwb], by rw [hwb]; omega⟩)))))))
      exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
    · exact not_vData_empty nv hb

end qps

/-! ## Restricting a path's `Pre` -/

section restr
variable {own : (U64 → U64) → U64 → Owner U64 U64} {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64}
  {User : U64 → Prop}

/-- **`P` with `Pre ∧ Q`** (`Q` kept by aligned user writes): every obligation is inherited. -/
def _root_.Fl4Proofs.P2.E2E.LocalPath.restrQ (P : E2E.LocalPath own cls ko User) (Q : P.S → Prop)
    (hQ : ∀ s b v, P.Pre s → Q s → User b → Aligned b → Q (@LawfulStore.wr P.S P.st P.L s b v)) :
    E2E.LocalPath own cls ko User where
  S := P.S
  A := P.A
  X := P.X
  st := P.st
  L := P.L
  ar := P.ar
  F := P.F
  p := P.p
  Acc := P.Acc
  Locks := P.Locks
  Pre := fun s => P.Pre s ∧ Q s
  RS := P.RS
  WS := P.WS
  DS := P.DS
  isProg := fun st' N σ g a => P.isProg st' N σ (by obtain ⟨s, hs, hA⟩ := g; exact ⟨s, hs.1, hA⟩) a
  obl := by
    letI := P.L
    exact
    { acc := fun s a r h => P.obl.acc s a r h.1
      dec_alt := fun s a r h => P.obl.dec_alt s a r h.1
      read_own := fun s x h => P.obl.read_own s x h.1
      write_own := fun s x h => P.obl.write_own s x h.1
      aligned := fun s x h => P.obl.aligned s x h.1
      move := fun s a r h => P.obl.move s a r h.1 }
  side := by
    letI := P.L
    exact
    { read_aligned := fun s s' a r h => P.side.read_aligned s s' a r h.1
      rs_aligned := fun s x h => P.side.rs_aligned s x h.1
      ko_aligned := P.side.ko_aligned
      user_free := fun s b v h hb ha => by
        obtain ⟨h1, h2⟩ := P.side.user_free s b v h.1 hb ha
        exact ⟨⟨h1, hQ s b v h.1 h.2 hb ha⟩, h2⟩ }
  once := fun s s' a r h => P.once s s' a r h.1
  total := P.total
  masks := P.masks

theorem avoidE_restrQ {E : U64 → Prop} {P : E2E.LocalPath own cls ko User} {Q : P.S → Prop} {hQ}
    (h : AvoidE E P) : AvoidE E (P.restrQ Q hQ) := by
  letI := P.L
  exact ⟨fun s a r hs => h.acc s a r hs.1, fun s a r hs => h.dec s a r hs.1,
    fun st' N σ g a => h.prog st' N σ (by obtain ⟨s, hs, hA⟩ := g; exact ⟨s, hs.1, hA⟩) a⟩

theorem avoidE_restrQ_noPre {E : U64 → Prop} {P : E2E.LocalPath own cls ko User} {Q : P.S → Prop} {hQ}
    (h : ∀ s, ¬ P.Pre s) : AvoidE E (P.restrQ Q hQ) :=
  avoidE_of_noPre (fun s hs => h s hs.1)

/-- `QPs` for a path's states. -/
abbrev QPt (K : KLayoutP) (P : E2E.LocalPath own cls ko User) (s : P.S) : Prop := @QPs P.S K P.st P.L s

theorem qPt_stab (K : KLayoutP) (P : E2E.LocalPath own cls ko User)
    (hU : ∀ b, User b → b ∈ K.user ∨ VData K.toKLayoutV b) :
    ∀ s b v, P.Pre s → QPt K P s → User b → Aligned b → QPt K P (@LawfulStore.wr P.S P.st P.L s b v) :=
  fun _ _ _ _ hq hb ha => @QPs.wr P.S P.st P.L K _ _ _ hq (hU _ hb) ha

/-- **`P` restricted to `QPs` states.** -/
abbrev _root_.Fl4Proofs.P2.E2E.LocalPath.rJ (P : E2E.LocalPath own cls ko User) (K : KLayoutP)
    (hU : ∀ b, User b → b ∈ K.user ∨ VData K.toKLayoutV b) : E2E.LocalPath own cls ko User :=
  P.restrQ (QPt K P) (qPt_stab K P hU)

end restr

section lifts
variable {cls : U64 → U64 → U64} {ko : U64 → ClsOwner U64} {User : U64 → Prop}

theorem avoidV_restrQ {K : KLayoutV} {P : E2E.LocalPath (OwnMap.own K.toKLayout) cls ko User} {Q : P.S → Prop} {hQ}
    (h : AvoidV K P) : AvoidV K (P.restrQ Q hQ) := by
  letI := P.L
  exact ⟨fun s a r hs => h.acc s a r hs.1, fun s a r hs => h.dec s a r hs.1,
    fun st' N σ g a => h.prog st' N σ (by obtain ⟨s, hs, hA⟩ := g; exact ⟨s, hs.1, hA⟩) a⟩

theorem noVcpuRW_restrQ {K : KLayoutV} {m : U64 → U64}
    {P : E2E.LocalPath (OwnMap.own (userV K)) (OwnMap.cls (userV K)) (OwnMap.ko (userV K) m) (· ∈ (userV K).user)}
    {Q : P.S → Prop} {hQ} (h : NoVcpuRW K P) : NoVcpuRW K (P.restrQ Q hQ) :=
  ⟨fun s x hs => h.rd s x hs.1, fun s x hs => h.wr s x hs.1⟩

/-- **Route C: `AvoidE` of the restricted path gives `AvoidE` of the restricted cut lift.** -/
theorem avoidE_cutLiftV_rJ {Kp : KLayoutP} {Ex : U64 → Prop} (hK : RegionOKV Kp.toKLayoutV)
    (hU : UserOKV Kp.toKLayoutV) (nv : Kp.vcpus = ∅) (hko : ∀ x, VData Kp.toKLayoutV x → ko x = .free)
    (P : E2E.LocalPath (OwnMap.own Kp.toKLayout) cls ko (· ∈ Kp.user)) (W : AvoidV Kp.toKLayoutV P)
    (h : AvoidE Ex (P.rJ Kp (fun b hb => Or.inl hb))) :
    AvoidE Ex ((LocalPath.cutLiftV hK hU hko P W).rJ Kp (fun b hb => Or.inl hb)) := by
  have e : (LocalPath.cutLiftV hK hU hko P W).rJ Kp (fun b hb => Or.inl hb) =
      LocalPath.cutLiftV hK hU hko (P.rJ Kp (fun b hb => Or.inl hb)) (avoidV_restrQ W) := rfl
  rw [e]
  exact avoidE_cutLiftV_empty hK hU nv hko _ _ h

/-- **Route U: `AvoidE` of the restricted path gives `AvoidE` of the restricted slot lift.** -/
theorem avoidE_liftAtV_rJ {Kp : KLayoutP} {m : U64 → U64} {E : U64 → Prop} (hK : RegionOKV Kp.toKLayoutV)
    (P : E2E.LocalPath (OwnMap.own (userV Kp.toKLayoutV)) (OwnMap.cls (userV Kp.toKLayoutV))
      (OwnMap.ko (userV Kp.toKLayoutV) m) (· ∈ (userV Kp.toKLayoutV).user)) (W : NoVcpuRW Kp.toKLayoutV P)
    (h : AvoidE E (P.rJ Kp (fun b hb => hb))) :
    AvoidE E ((LocalPath.liftV hK (LocalPath.atV hK P W) (noVcpuRd_atV hK P W)).rJ Kp (fun b hb => Or.inl hb)) := by
  have e : (LocalPath.liftV hK (LocalPath.atV hK P W) (noVcpuRd_atV hK P W)).rJ Kp (fun b hb => Or.inl hb) =
      LocalPath.liftV hK (LocalPath.atV hK (P.rJ Kp (fun b hb => hb)) (noVcpuRW_restrQ W))
        (noVcpuRd_atV hK _ (noVcpuRW_restrQ W)) := rfl
  rw [e]
  exact avoidE_liftAtV hK _ _ h

end lifts

end

end Fl4Proofs.P2.E2EP

/-! ## syscall_local under `Pre ∧ Q` -/

namespace Fl4Proofs.P2.E2EV
open fl4_core Fl4Proofs.P1 Fl4Proofs.P0.Consts Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.OwnMap

noncomputable section
open Classical

section av
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Ex : U64 → Prop} {K : KLayoutV} {Locks : S → U64 → Prop}
variable {A : Type}
variable {m0 : U64 → U64} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

/-- **`sl_avoidVKE` for the path restricted by `Q`**, the PTE facts asked at `P ∧ Q` states only. -/
theorem sl_avoidVKE_rQ (ar : machine.Arch A) (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A) (hK : RegionOKE Ex K) (hU : Fl4Proofs.P2.E2E.UserOK K.toKLayout)
    {P : S → Prop}
    (hJ : ∀ s, P s → SlJAt (L := L) K.toKLayout s)
    (hPE : ∀ s, P s → SlPreB (st := st) ar K.toKLayout Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s)
    (hEr : ∀ s, P s → SlEntR (st := st) K.toKLayout Locks found s)
    (hHr : ∀ s, P s → SlHereR (st := st) K.toKLayout found s)
    (hAr : ∀ s, P s → SlAccR (st := st) ar K.toKLayout Locks found s)
    (huf : ∀ s b v, P s → b ∈ K.user → Aligned b →
      P (L.wr s b v) ∧ Locks (L.wr s b v) = Locks s ∧
        SlRS (st := st) K.toKLayout Locks (L.wr s b v) = SlRS (st := st) K.toKLayout Locks s ∧
        SlWS (st := st) K.toKLayout Locks (L.wr s b v) = SlWS (st := st) K.toKLayout Locks s ∧
        SlDS (L := L) (L.wr s b v) = SlDS (L := L) s)
    (hpz : ∃ p : SProg Bool, IsProg (slBody S n found) p ∧ NoZero p ∧
      Fl4Proofs.P2.E2E.ReadOnce st ar p (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) (· ∈ K.user) P
        (SlRS (st := st) K.toKLayout Locks))
    (Q : S → Prop) (hQ : ∀ s b v, P s → Q s → b ∈ K.user → Aligned b → Q (L.wr s b v))
    (hks : ∀ s, P s → Q s → KsNoE Ex K) (hTN : ∀ s, P s → Q s → TabNoE (L := L) Ex s) (hUo : UserNoE Ex K) :
    Fl4Proofs.P2.E2EP.AvoidE Ex
      ((sl_localPathK ar hSt hA hm a0 hK.base hU hJ hPE hEr hHr hAr huf hpz).restrQ Q hQ) := by
  have hKb := hK.base
  have hX : ∀ s, P s → RegionOKX K.toKLayout := fun s hP => (hJ s hP).regionOKX
  have hent : ∀ s, P s → SlEntAllE (st := st) ar K Locks m0 n found K.heap.tcbs Cs Ω K.user Sg K.heap.replies
      K.heap.scs K.heap.ntfns Ac K.heap K.heap.scBits s := by
    intro s hP
    have E0 := hPE s hP
    have hSe := slSets_conv K.toKLayout
    have N := slEnt_of ar hSt hA (hX s hP) hSe a0 E0 ((hJ s hP).entJ E0.hN (hEr s hP))
    have Hh := slHere_of ar hSt hA (hX s hP) hSe a0 E0 N ((hJ s hP).hereJ (hHr s hP))
    exact ⟨E0, N, Hh, slAccIn_of ar hA hKb (hX s hP) hSe E0 N Hh
      (slAccJ_of ar hA hKb (hX s hP) (fun _ h => h) E0 ((hJ s hP).hereJ (hHr s hP)) ((hJ s hP).accK (hAr s hP)))⟩
  exact ⟨sl_avAccE (L := L) ar hA hK (P := fun s => P s ∧ Q s) (fun s h => hX s h.1) (fun s h => hent s h.1)
      (fun s h => hks s h.1 h.2) (fun s h => (slJAt_fitE (hJ s h.1)).1) (fun s h => hTN s h.1 h.2)
      (fun s h => (slJAt_fitE (hJ s h.1)).2) trivial hUo,
    sl_avDecE (L := L) ar hA hK hm hpz.choose_spec.1 hpz.choose_spec.2.1 (P := fun s => P s ∧ Q s) (fun s h => hX s h.1)
      (fun s h => hent s h.1) (fun s h => hks s h.1 h.2) (fun s h => (slJAt_fitE (hJ s h.1)).1),
    IsProg.on hpz.choose_spec.1 _ _ _⟩

end av

end

end Fl4Proofs.P2.E2EV

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oTIMER_DEADLINE GateField TimerField tcbOwner tOwner)
open Fl4Proofs.P2.E2E (StartAt SP)
open Fl4Proofs.P2.Serial (Owner ClsOwner Cfg Init ArmInv NoLoc RunAll)

noncomputable section
open Classical

section slots
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **syscall_local under `QPs`** (`sl_avoidP` with `PteSl` replaced by the state's `QPs`). -/
theorem sl_avoidPJ (i : SlArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (slSlotP3 st ar hA hSt hm a0).Prem i K.toKLayoutV m) :
    AvoidP K (((slSlotP3 st ar hA hSt hm a0).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m)
      (· ∈ K.user)) (W : AvoidV K.toKLayoutV P),
      P = (slSlotP3 st ar hA hSt hm a0).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.cutLiftV hK.base hU.base (fun x ⟨_, hv, _⟩ => ko_vcpu hK.base hv m) P W).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    apply avoidE_cutLiftV_rJ hK.base hU.base h.1
    dsimp only [slSlotP3, SlotC.ofP3, SlotC.pull, slSlotK]
    dsimp only [sl_pathsKC5, sl_pathsKC4, sl_pathsKF, sl_pathsKU, sl_pathsK]
    exact sl_avoidVKE_rQ ar hSt hA hm a0 (regionOKE_pte hK) hU.base.base (fun _ h' => h'.1) _ _ _ _ _ _ _ _
      (fun s _ hq => QPs.ks (L := L) hq) (fun s _ hq => QPs.tab (L := L) hq) (userNoE_pte hU)
  exact key _ _ (SlotC.fam_pos _ _ h)

/-- **The timer interrupt's route-U path under `QPs`** (`irq_avoidP_path` with `PteSl` replaced by `QPs`). -/
theorem irq_avoidPJ_path (i : IrqArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (irqSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  have hKr := regionOK_userP hK.base
  have facts : ∀ s, IrqPreV K.toKLayoutV st m s → QPs K st s →
      ∃ Ω Ac : Set U64, IrqEnt (userP K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap
        (Heap.frame K.heap) (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac
        i.irq s := by
    intro s hs hq
    obtain ⟨Ω, Ac, hE⟩ := hs.entM hK.base vf h.2.lt
    exact ⟨Ω, Ac, irqEnt_userP hK hE.ent (fun hb j hj => hq.ksw (state_off_lt hb hj))
      (hq.ksw (by simp [layout.ks.KERNEL_ROOT])) hq.tab
      (hq.ksw (by simp [layout.ks.CUR_DOMAIN]))
      (hq.ksw (by simp [layout.ks.DOMAIN_TIME]))⟩
  refine avoidE_of_entry (P := ((irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => hb))
    (E := (· ∈ K.ptes)) (irq_noZero i.irq i.pl) (IsProg.on (irq_isProg S i.irq i.pl) _ _ _)
    (fun s => MaxR (L := L) (userP K) st i.lk s) (fun s => MaxW (L := L) (userP K) st i.lk s)
    (fun s x _ hx hp => hx.2.2 (Or.inr hp)) ?_
    (fun s => MaxR (L := L) (userP K) st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => ⟨hx.2.1, ⟨hx.1, hx.2.1, fun hu => hx.2.2 (Or.inl hu)⟩, fun hp => hx.2.2 (Or.inr hp)⟩)
    (fun s x hs hx => by
      obtain ⟨hs1, hs2⟩ := hs
      obtain ⟨Ω, Ac, hE⟩ := facts s hs1 hs2
      exact (hE.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IrqPreV K.toKLayoutV st m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localtimer.handle_timer_irq_local st ar s a i.irq i.pl = ok (true, s1, a1) := hr
    obtain ⟨Ω, Ac, hE⟩ := facts s hs' hq
    have hEK : IrqEntK (userP K) st (Heap.tcbs K.heap) {c : U64 | c.val < K.ncores} Ω K.heap (Heap.frame K.heap)
        (Heap.replies K.heap) (Heap.scs K.heap) (Heap.ntfns K.heap) (Heap.scBits K.heap) Ac (L.mem s) s :=
      ⟨hE.inv, hE.lay, fun _ _ _ => rfl, hE.asid⟩
    have hQ := slJAt_slotJC (st := st) hs'.1
    have hOL : ObjLay (userP K) K.heap (Heap.replies K.heap) := hQ.slotJ.objLay (fun r hr => hr)
    have hSL : SlotLayV (userP K) st (Heap.tcbs K.heap) s := hQ.slotJ.slotLayV (fun y hy => hy)
    have g : localtimer.handle_timer_irq_local (guard st (MaxR (userP K) st i.lk s) (MaxW (userP K) st i.lk s))
        ar s a i.irq i.pl = ok (true, s1, a1) :=
      irq_acc_own ar hA hKr hEK hE.ly hE.aff (fun hf => by
        by_cases hnw : NoWake st s
        · exact irq_acc_fire_nw ar hA hKr hEK hE.ly hE.aff hE.nth hf hnw hr'
        · obtain ⟨U, hB⟩ := hQ.bufAt
          exact irq_acc_fire_wk2 ar hA hKr hEK hE.ly hE.aff hE.nth hOL h.2.pl
            (irq_bufAt_runB ar hA hE.inv hB hf hr') hSL hf hnw hr') hr'
    exact g
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : IrqPreV K.toKLayoutV st m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localtimer.handle_timer_irq_local st ar s a i.irq i.pl = ok (false, s1, a1) := hr
      obtain ⟨Ω, Ac, hE⟩ := facts s hs' hq
      have g : localtimer.handle_timer_irq_local (guard st (MaxR (userP K) st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl = ok (false, s1, a1) :=
        irq_dec_guard ar hA hKr hE.inv hE.lay hE.ly hE.aff hE.nth hr'
      exact g
    · exact absurd rfl hb

/-- **The timer interrupt under `QPs`.** -/
theorem irq_avoidPJ (i : IrqArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (irqSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((irqSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (irqSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (irq_avoidPJ_path st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **`TCB_SetTimer`'s route-U path under `QPs`** (`stm_avoidP_path` with `PteSl` replaced by `QPs`). -/
theorem stm_avoidPJ_path (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (stSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidE (· ∈ K.ptes) (((stSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => hb)) := by
  have vf : VFacts L K.toKLayoutV := VFacts.ofEmpty h.1 h.2.bun.choose_spec
  have hKu := regionOK_userV hK.base
  have hUOu := userOK_userV hK.base hU.base
  have hp := st_isProg S i.n i.target
  have hz := st_noZero i.n i.target
  have ent : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s →
      StEntK (userV K.toKLayoutV) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac i.target m s :=
    fun s hs => stEntK_userV hK.base (vf.v hs.1).1 (vf.v hs.1).2.1 (slJAt_ksb hs.1) (h.2.pe s hs.1 hs.2)
  have entP : ∀ s, SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s → QPs K st s →
      StEnt (userP K) st K.heap.tcbs i.Cs i.Ω K.heap i.Sg K.heap.replies K.heap.scs K.heap.ntfns
        K.heap.scBits i.Ac i.target s :=
    fun s hs hq => ⟨(ent s hs).ent.inv, stLay_userP hK (ent s hs).ent.lay
      (hq.ksw (by simp [layout.ks.CUR_DOMAIN])) (hq.ksw (by simp [layout.ks.DOMAIN_TIME])),
      (ent s hs).ent.pre, (ent s hs).ent.aff, (ent s hs).ent.tg⟩
  have hex : ∃ p : SProg Bool, IsProg (stBody S i.n i.target) p ∧ NoZero p ∧
      E2E.ReadOnce st ar p (OwnMap.cls (userV K.toKLayoutV)) (OwnMap.ko (userV K.toKLayoutV) m)
        (· ∈ (userV K.toKLayoutV).user) (StEntV K.toKLayoutV st i.Cs i.Ω i.Sg i.Ac i.target m)
        (MaxR (userV K.toKLayoutV) st i.lk) :=
    ⟨_, hp, hz, st_hro ar i.n hA hKu hUOu hm⟩
  refine ⟨?_, ?_, IsProg.on (Classical.choose_spec hex).1 _ _ _⟩
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localtimer.handle_set_timer_local st ar s a i.n i.target = ok (true, s1, a1) := hr
    have eP : ∀ (mm : machine.Store S) (x : S), localtimer.handle_set_timer_local mm ar x a i.n i.target =
        interp mm ar (R.localtimer.handle_set_timer_local i.n i.target) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    have hE := (ent s hs').ent
    have hEP := entP s hs' hq
    have g1 := set_timer_acc_own ar hA (lk := i.lk) hE.inv hE.tg hE.lay hE.aff hr'
    have g2 := set_timer_acc_own ar hA (lk := i.lk) hEP.inv hEP.tg hEP.lay hEP.aff hr'
    replace g1 := (eP _ s).symm.trans g1
    replace g2 := (eP _ s).symm.trans g2
    have w1 := (interp_guard _ s a _ g1).2
    have w2 := (interp_guard _ s a _ g2).2
    show localtimer.handle_set_timer_local
      (guard st (rsE (· ∈ K.ptes) (MaxR (userV K.toKLayoutV) st i.lk) s) (MaxW (userV K.toKLayoutV) st i.lk s))
      ar s a i.n i.target = ok (true, s1, a1)
    refine (eP _ s).trans ?_
    exact guard_of_within (st := st) (L := L) (ar := ar) _ s a _ ((eP st s).symm.trans hr')
      (Within.mono (fun b hb => ⟨hb.1, fun hq => hb.2.2.2 (Or.inr hq)⟩) (fun b hb => hb.1) _ s a
        (Fl4Proofs.P2.E2E.within_and _ s a w1 w2))
  · intro s a r hs hr hn s' r' hA' h'
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : SlJAt (L := L) K.toKLayout s ∧ i.Q K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    have hAl : PathObl.Alt st (MaxR (userV K.toKLayoutV) st i.lk s) (OwnMap.cls (userV K.toKLayoutV))
        (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user) s s' := hA'
    have h'' : localtimer.handle_set_timer_local st ar s' a i.n i.target = ok r' := h'
    have eP : ∀ (mm : machine.Store S) (x : S), localtimer.handle_set_timer_local mm ar x a i.n i.target =
        interp mm ar (R.localtimer.handle_set_timer_local i.n i.target) x a :=
      fun mm x => congrFun (congrFun (hp A ar mm) x) a
    have hEK := ent s hs'
    have hE := hEK.ent
    have hEP := entP s hs' hq
    have hko : L.mem s (affA i.target) = L.cpu s →
        OwnMap.ko (userV K.toKLayoutV) m (tdA i.target) = .core (L.cpu s) := set_timer_ko hKu hUOu hEK
    have hcls := set_timer_cls hE
    have hU := set_timer_user hKu hUOu hE
    show localtimer.handle_set_timer_local (guard st (fun b => ¬ b ∈ K.ptes) (fun _ => True)) ar s' a i.n i.target
      = ok r'
    obtain ⟨b, s1, a1⟩ := r
    cases b
    swap
    · exact absurd rfl hn
    have hr' : localtimer.handle_set_timer_local st ar s a i.n i.target = ok (false, s1, a1) := hr
    by_cases hfar : L.mem s (affA i.target) ≠ L.cpu s ∨ L.mem s (tdA i.target) = 0#u64 ∨
        (L.mem s (thA i.target)).val >>> 8 = (L.cpu s).val
    · have g := set_timer_dec_guard ar hA (lk := i.lk) hEP.inv hEP.tg hEP.lay hEP.pre hEP.aff hfar hr'
      replace g := (eP _ s).symm.trans g
      obtain ⟨s1', g'⟩ := interp_agree hm (fun w hw => hw.2.1) (fun w hw => (hE.dec hw).1) _ hz s s' a false s1 a1
        hAl.ksb hAl.cpu hAl.masks (fun w hw => hAl.read w ⟨hw.1, hw.2.1, fun hu => hw.2.2 (Or.inl hu)⟩) g
      obtain ⟨hst, w⟩ := interp_guard _ s' a _ g'
      have e : r' = (false, s1', a1) := Result.ok_injective (((eP st s').symm.trans h'').symm.trans hst)
      subst e
      refine (eP _ s').trans ?_
      exact guard_of_within (st := st) (L := L) (ar := ar) _ s' a _ hst
        (Within.mono (fun b hb hq => hb.2.2 (Or.inr hq)) (fun _ _ => trivial) _ s' a w)
    · rw [not_or, not_or, not_not] at hfar
      obtain ⟨hat, hd, hh⟩ := hfar
      have h0 := hE.inv.1.choose_spec.choose_spec
      have hT : TcbPlaced (Heap.tcbs K.heap) := h0.tcbs
      have hN : NodePlaced st (Heap.tcbs K.heap) s (L.cpu s) := h0.nodes _ h0.cur
      obtain ⟨W0, ct⟩ := (TInv.rb (BXI.blk hE.inv)).tree _ h0.cur
      have eN : ∀ o, L.nodeAt s' (L.cpu s) o = L.nodeAt s (L.cpu s) o := fun o => nodeAt_of_ksb hAl.ksb _ o
      have keyR : ∀ y ∈ W0.keys, ∀ k : U64, 3528 ≤ k.val → k.val < 3576 → k.val % 8 = 0 →
          L.mem s' (core.num.U64.wrapping_add y k) = L.mem s (core.num.U64.wrapping_add y k) := by
        intro y hy k h1 h2 h3
        refine hAl.read _ ⟨Or.inl (held_core ?_), field_aligned (hT y (ct.inT y hy)) (by omega) h3,
          hE.lay.nu_tcb (ct.inT y hy) (by omega) (by omega)⟩
        have e := hE.lay.own_tcb hT (L.mem s) (ct.inT y hy) (k := k) (by omega) (by omega)
        unfold fld at e
        rw [e, tcbOwner, if_neg (show ¬ GateField k.val by unfold GateField; omega),
          if_pos (show TimerField k.val by unfold TimerField; omega), tOwner,
          if_pos (show (L.mem s (fld y oTIMER_DEADLINE)).val ≠ 0 from
            fun h => ct.armed y hy (UScalar.eq_of_val_eq h))]
        have e2 := ct.core y hy
        rw [Nat.shiftRight_eq_div_pow] at e2
        exact congrArg Owner.core (MoveTimer.treeCore_of (c := L.cpu s) e2)
      have ct' : CoreTree st (Heap.tcbs K.heap) s' (L.cpu s) W0 := CoreTree.agree ct eN
        (hAl.read _ (nodeR hE (by simp [layout.node.TIMER_ROOT]) (by simp [layout.node.TIMER_ROOT])))
        (hAl.read _ (nodeR hE (by simp [layout.node.TIMER_MIN]) (by simp [layout.node.TIMER_MIN])))
        (fun y hy => ⟨keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
          keyR y hy _ (by simp) (by simp) (by simp), keyR y hy _ (by simp) (by simp) (by simp),
          keyR y hy _ (by simp) (by simp) (by simp)⟩)
      have hd' : L.mem s' (tdA i.target) ≠ 0#u64 := by
        by_cases hin : MaxR (userV K.toKLayoutV) st i.lk s (tdA i.target)
        · rw [hAl.read _ hin]; exact hd
        · have e := hAl.clsEq _ hin hU (Or.inr (hko hat))
          exact fun h => hd ((hcls _ _ e).1 h)
      have hcur : L.curW s' = L.curW s := by
        unfold LawfulStore.curW
        rw [hAl.cpu, eN]
        exact hAl.read _ (nodeR hE (by rw [curth_val]; omega) (by rw [curth_val]))
      have hk : i.target ∉ W0.keys := fun h => hh (ct.core i.target h)
      rw [← hAl.cpu] at ct'
      have hN' : NodePlaced st (Heap.tcbs K.heap) s' (L.cpu s') := by rw [hAl.cpu]; exact hN.ksb hAl.ksb
      have hnR : ∀ o : U64, o.val < 4288 → o.val % 8 = 0 →
          Aligned (L.nodeAt s' (L.cpu s') o) ∧ L.nodeAt s' (L.cpu s') o ∉ K.ptes := by
        intro o h1 h2
        refine ⟨nodeAt_aligned hN' h1 h2, ?_⟩
        have e : L.nodeAt s' (L.cpu s') o = L.nodeAt s (L.cpu s) o := by rw [hAl.cpu]; exact eN o
        rw [e]
        intro hq
        have h3 : region K.toKLayout (L.nodeAt s (L.cpu s) o) = .node (L.cpu s) := hE.lay.nd o h1
        rw [hK.none _ hq] at h3
        cases h3
      have hfR : ∀ {x k : U64}, x ∈ Heap.tcbs K.heap → k.val < 4096 → k.val % 8 = 0 →
          Aligned (core.num.U64.wrapping_add x k) ∧ core.num.U64.wrapping_add x k ∉ K.ptes :=
        fun {x k} hx h1 h2 => ⟨field_aligned (hT _ hx) h1 h2,
          fun hq => region_tcb_ne_none (K := K.toKLayout) hx (tcb_wadd_val (hT _ hx) h1) h1 (hK.none _ hq)⟩
      obtain ⟨-, h2⟩ := set_timer_farR (R := fun w => Aligned w ∧ w ∉ K.ptes) ar hT hN'
        (by rw [hcur]; exact h0.curT) hE.tg ct' hk hd' hnR hfR h''
      replace h2 := (eP _ s').symm.trans h2
      refine (eP _ s').trans ?_
      exact interp_mono (fun _ hq => hq.2) (fun _ hq => hq.elim) _ hz s' a r' h2

/-- **`TCB_SetTimer` under `QPs`.** -/
theorem stm_avoidPJ (i : StArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (stSlotP3W st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((stSlotP3W st ar hA hm).lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ (P : E2E.LocalPath (OwnMap.own (userV K.toKLayoutV)) (OwnMap.cls (userV K.toKLayoutV))
      (OwnMap.ko (userV K.toKLayoutV) m) (· ∈ (userV K.toKLayoutV).user)) (W : NoVcpuRW K.toKLayoutV P),
      P = (stSlotP3W st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K ((LocalPath.liftV hK.base (LocalPath.atV hK.base P W) (noVcpuRd_atV hK.base P W)).rJ K
        (fun b hb => Or.inl hb)) := by
    rintro P W rfl
    exact avoidE_liftAtV_rJ hK.base _ W (stm_avoidPJ_path st ar hA hm i K m hK hU h)
  exact key _ _ (SlotU.fam_pos _ _ h)

/-- **The VM-timer path under `QPs`** (`vt_avoidP_path` with `VtmP` from the state's `QPs`). -/
theorem vt_avoidPJ_path (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vtSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb)) := by
  have hK' := regionOKV_pteU hK
  have hVU := vcpuNU_pteU hK
  have hP : ∀ s, QPs K st s → VtmP K st i.irq s := fun s hq => vtmP_of_ksb i.irq hq.ks hq.ksb hq.tab
  refine avoidE_of_entry (P := ((vtSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb))
    (E := (· ∈ K.ptes)) (vtimer_noZero i.irq i.pl i.n) (IsProg.on (vtimer_isProg S i.irq i.pl i.n) _ _ _)
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => VexitWS (L := L) K.pteU st i.lk s)
    (fun s x _ hx => (vexitRSU_pteU (L := L) hx).2.2) ?_
    (fun s => VexitRSU (L := L) K.pteU st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => vexitRSU_pteU (L := L) hx)
    (fun s x hs hx => by
      obtain ⟨hs1, -⟩ := hs
      exact ((show VtPre st i K.toKLayoutV s from hs1).ent.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VtPre st i K.toKLayoutV s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (true, s1, a1) := hr
    have hE' := vtmEnt_pteU hK hs' (hP s hq)
    have hTU := vtmU_pteU (hP s hq)
    have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (VexitWS K.pteU st i.lk s))
        ar s a i.irq i.pl i.n = ok (true, s1, a1) :=
      vtimer_acc_ownU ar hA hK' hVU hE' hTU (fun hq => by
        by_cases hNW : NoWake st s
        · exact vtimer_acc_fnw_ownU ar hA hK' hVU h.Nt hE' hTU hq hNW hr'
        · obtain ⟨U, hUs, hbU⟩ := h.UB s hs'
          exact vtimer_acc_fwk_ownU ar hA hK' hVU h.Nt hE' hTU h.OL h.PL hUs hbU (h.SL s hs') (h.pSg s hs') hq hNW
            hr') hr'
    exact g
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VtPre st i K.toKLayoutV s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vm_timer_irq_local st ar s a i.irq i.pl i.n = ok (false, s1, a1) := hr
      have g : localvm.handle_vm_timer_irq_local (guard st (VexitRSU K.pteU st i.lk s) (IrqDec st s))
          ar s a i.irq i.pl i.n = ok (false, s1, a1) :=
        vtimer_dec_ownU ar hA hK' hVU h.Nt (vtmEnt_pteU hK hs' (hP s hq)) (vtmU_pteU (hP s hq)) hr'
      exact g
    · exact absurd rfl hb

/-- **The VM-timer slot under `QPs`.** -/
theorem vt_avoidPJ (i : VtArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vtSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ P, P = (vtSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (P.rJ K (fun b hb => Or.inl hb)) := by
    rintro P rfl
    exact vt_avoidPJ_path st ar hA hm i K m hK hU h
  exact key _ (SlotN.fam_pos _ _ h)

/-- **The VM-exit path under `QPs`** (`vx_avoidP_path` with `VxP` from the state's `QPs`). -/
theorem vx_avoidPJ_path (i : VxArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vxSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K (fun b hb => Or.inl hb)) := by
  have hVU := vcpuNU_pteU hK
  have hP : ∀ s, QPs K st s → VxP (L := L) K s := fun s hq => vxP_of_ksb hq.ks hq.ksb
  refine avoidE_of_entry (P := ((vxSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h).rJ K
      (fun b hb => Or.inl hb))
    (E := (· ∈ K.ptes)) (vexit_noZero i.v i.n) (IsProg.on (vexit_isProg S i.v i.n) _ _ _)
    (fun s => VexitRSP (L := L) K st i.lk s) (fun s => VexitWS (L := L) K.toKLayoutV st i.lk s)
    (fun s x _ hx => hx.2) ?_
    (fun s => VexitRSP (L := L) K st i.lk s) (fun s => IrqDec (L := L) st s)
    (fun s x _ hx => ⟨hx.1.1, hx.1, hx.2⟩)
    (fun s x hs hx => by
      obtain ⟨hs1, -⟩ := hs
      exact ((show VxPre st i K.toKLayoutV m s from hs1).1.dec hx).1) ?_
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VxPre st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    have hb' : b = true := hb
    subst hb'
    have hr' : localvm.handle_vcpu_exit_local st ar s a i.v i.n = ok (true, s1, a1) := hr
    have hd := hP s hq
    have g : localvm.handle_vcpu_exit_local (guard st (VexitRSP K st i.lk s) (VexitWS K.toKLayoutV st i.lk s))
        ar s a i.v i.n = ok (true, s1, a1) := by
      by_cases hp0 : vcpu.get st s i.v vcpu.PENDING = ok 0#u64
      · exact vexit_acc_own_npP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hp0 hr'
      · exact vexit_acc_own_pP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hs'.2 hp0 hr'
    exact g
  · intro s a r hs hr hb
    obtain ⟨hs1, hs2⟩ := hs
    have hs' : VxPre st i K.toKLayoutV m s := hs1
    have hq : QPs K st s := hs2
    obtain ⟨b, s1, a1⟩ := r
    cases b
    · have hr' : localvm.handle_vcpu_exit_local st ar s a i.v i.n = ok (false, s1, a1) := hr
      have hd := hP s hq
      have g : localvm.handle_vcpu_exit_local (guard st (VexitRSP K st i.lk s) (IrqDec st s))
          ar s a i.v i.n = ok (false, s1, a1) :=
        vexit_dec_ownP ar hA hK hK.base hVU hs'.1 hd.1 hd.2 hr'
      exact g
    · exact absurd rfl hb

/-- **The VM-exit slot under `QPs`.** -/
theorem vx_avoidPJ (i : VxArg S) (K : KLayoutP) (m : U64 → U64) (hK : RegionOKP K) (hU : UserOKP K)
    (h : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m) :
    AvoidP K (((vxSlotP3 st ar hA hm).fam (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base).rJ K
      (fun b hb => Or.inl hb)) := by
  have key : ∀ P, P = (vxSlotP3 st ar hA hm).path i K.toKLayoutV m hK.base hU.base h →
      AvoidP K (P.rJ K (fun b hb => Or.inl hb)) := by
    rintro P rfl
    exact vx_avoidPJ_path st ar hA hm i K m hK hU h
  exact key _ (SlotN.fam_pos _ _ h)

end slots

/-! ## The family and the top theorem -/

section top
variable {S : Type} (st : machine.Store S) [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable (hA : P0.ArchTotal ar) (hSt : P0.StoreTotal st) (hm : E2E.MasksWr st) (a0 : A)

/-- **`P3AvP4` without its three layout fields** (`pteSl`, `vtP`, `vxP`: now start-state facts in every path's
`Pre`, module docstring). The three fields left are [W] (as in `P3AvP4`). -/
structure P3AvJ : Prop where
  /-- [W] -/
  vmF : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmF.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  /-- [W] -/
  vmR : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).vmR.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)
  /-- [W] -/
  io : ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K), K.ptes ≠ ∅ →
    (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m →
    AvoidP K ((fl4LocP3W st ar hA hSt hm a0).io.lift (fl4Dflt st ar hm) i K.toKLayoutV m hK.base hU.base)

/-- `P3AvJ` asks no more than `P3AvP4`. -/
theorem P3AvJ.ofP4 (h : P3AvP4 st ar hA hSt hm a0) : P3AvJ st ar hA hSt hm a0 := ⟨h.vmF, h.vmR, h.io⟩

/-- **Every path of `fl4LocP3W`, restricted to `QPs` states, reads no PTE word.** -/
theorem P3AvJ.all (h : P3AvJ st ar hA hSt hm a0) :
    ∀ i (K : KLayoutP) m (hK : RegionOKP K) (hU : UserOKP K),
      AvoidP K ((((fl4LocP3W st ar hA hSt hm a0).paths (fl4Dflt st ar hm)) i K.toKLayoutV m hK.base hU.base).rJ K
        (fun b hb => Or.inl hb)) := by
  intro i K m hK hU
  by_cases he : K.ptes = ∅
  · exact avoidP_empty he _
  cases i with
  | vmF i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).vmF.Prem i K.toKLayoutV m
    · exact avoidE_restrQ (h.vmF i K m hK hU he hp)
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | vmR i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).vmR.Prem i K.toKLayoutV m
    · exact avoidE_restrQ (h.vmR i K m hK hU he hp)
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | io i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).io.Prem i K.toKLayoutV m
    · exact avoidE_restrQ (h.io i K m hK hU he hp)
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | st i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).st.Prem i K.toKLayoutV m
    · exact stm_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | irq i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).irq.Prem i K.toKLayoutV m
    · exact irq_avoidPJ st ar hA hm i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotU.noPre (fl4Dflt st ar hm) _ hp)
  | sl i =>
    by_cases hp : (fl4LocP3W st ar hA hSt hm a0).sl.Prem i K.toKLayoutV m
    · exact sl_avoidPJ st ar hA hSt hm a0 i K m hK hU hp
    · exact avoidE_restrQ_noPre (SlotC.noPre (fl4Dflt st ar hm) _ hp)
  | vq j =>
    cases j with
    | inl i =>
      by_cases hp : (vxSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · exact vx_avoidPJ st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)
    | inr i =>
      by_cases hp : (vtSlotP3 st ar hA hm).Prem i K.toKLayoutV m
      · exact vt_avoidPJ st ar hA hm i K m hK hU hp
      · exact avoidE_restrQ_noPre (SlotN.noPre (fl4Dflt st ar hm) _ hp)

/-- **FL4's eight local paths, each restricted to `QPs` states, PTE-cut and lifted to `ownP`** (module docstring). -/
def fl4LocP3J (hAv : P3AvJ st ar hA hSt hm a0) : PathsP (E2EV.Fl4IxW (S := S)) :=
  fun i K m hK hU => LocalPath.cutLiftP hK hU (fun x hx => ko_pte hK hx m) _ (P3AvJ.all st ar hA hSt hm a0 hAv i K m hK hU)

/-- **FL4 end to end with rules 7 and 8, `K.ptes` arbitrary, the PTE layout facts as start-state facts**
(module docstring): every execution `ExecP` over `fl4LocP3J` from a start with `Init`, `ArmInv`, `RegionOKP` /
`UserOKP` [J] and the maps, at a state with no local path in progress, ran exactly as some serial order of its
completed entries. Premises: `hAv` (3 [W]: vmF, vmR, io); `ExecP`'s glue (`Fl4StepP`: `arm` [P]; `start` [P], whose
`Pre` now includes `QPs K st s` — the glue's choice **`K.ptes ⊆ ptesJ Zx'`** of the bundle ghost at the serial exit
makes it true at every start of the epoch, module docstring; `ser` with the layout choice [P] / [J]; `HwStepP` [P]).
`PteSl` / `VtmP` / `VxP` are gone. -/
theorem serializable_fl4_localP3J (hAv : P3AvJ st ar hA hSt hm a0) {s0 s : Cfg U64 U64 U64 U64} {K0 K : KLayoutP}
    (h0 : Init s0) (hA0 : ArmInv s0) (hK0 : RegionOKP K0) (hU0 : UserOKP K0) (hM0 : MapsP K0 s0)
    (h : ExecP (fl4LocP3J st ar hA hSt hm a0 hAv) s0 K0 s K) (hq : NoLoc s) :
    RunAll s.log s0.mem s.mem :=
  serializable_e2eP _ h0 hA0 hK0 hU0 hM0 h hq

end top

end

end Fl4Proofs.P2.E2EP
