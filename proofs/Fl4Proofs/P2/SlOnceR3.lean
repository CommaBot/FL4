/-
# P2 (line slhuf, gen 8): `hRR` discharged — the syscall local path with `ReadOnce` proved

* **`sl_rr_once`**: `SlRROnce` (P2/SlOnce.lean) at every layout: the prefix by `sl_pre_once` at the entry state
  itself (`Alt.refl`), the accepted ReplyRecv fast path by `rr_acc_once` (P2/SlOnceR2.lean) on
  `SlRS s ∧ NU K` / `SlWS s ∧ NU K`, its facts the meet of `SlPre`'s `RrAcc` (`toNB`) and `rrAccNB_nu`.
* **`sl_hro2`**: `hro` of `sl_pathsKCG` / `sl_pathsKC5` with no premise but `hSt`, `hA`, `hm`, `a0`.
* **`sl_pathsKC7`**, `sl_pathsKC7_startAt`: `sl_pathsKC6` with `hRR` discharged. Premises: `hSt`, `hA`, `hm`, `a0`,
  `hCs` [P], `hKD` [P]; no [W].
-/
import Fl4Proofs.P2.SlOnceR2
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1 Fl4Proofs.P2.OwnMap Fl4Proofs.P0.Consts
open Fl4Proofs.P2.E2E (Once ReadOnce)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {A : Type} (ar : machine.Arch A)
variable {Locks : S → U64 → Prop} {n : I64} {found : U64 × U64} {Cs Ω Sg Ac : Set U64}

set_option maxHeartbeats 4000000 in
/-- **`hRR` holds** (module docstring). -/
theorem sl_rr_once (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (a0 : A) :
    ∀ K m, SlRROnce st ar Locks n found Cs Ω Sg Ac K m := by
  intro K m s a s1 a1 hJ hq hS h0
  have F := slOF_of ar hSt hA a0 hJ hq
  have E := F.E
  have hX := F.B.regionOKX
  have hp : ∀ (mm : machine.Store S) (x : S) (a : A),
      syscall.handle_syscall_local mm ar x a n found = interp mm ar (R.syscall.handle_syscall_local n found) x a :=
    fun mm x a => congrFun (congrFun (sl_isProg S n found A ar mm) x) a
  have h := h0
  rw [hp] at h
  obtain ⟨rp, ep⟩ := found
  refine sl_pre_once (R0 := SlRN (st := st) K Locks s) (W0 := NU K) (fun q hq => ⟨hq.1, hq.2.2⟩)
    (fun q hq => hq.2) hA E.hT E.hN E.hcT (sl_alt_preDec ar F (Alt.refl s)) (sl_alt_hhd ar hA F (Alt.refl s)) h
    (fun hS' => absurd hS' hS) ?_
  intro _ X a1' LP h' Wd
  have hf : fastpath.reply_recv_found st ar X a1' (L.curW s) rp ep = ok (true, s1, a1) := by
    have h'' := h'
    rw [R.fastpath.reply_recv_found_eq] at h''
    obtain ⟨⟨b', s', a'⟩, hv, e⟩ := bind_shape h''
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl⟩ := e
    exact hv
  have hc0 := E.hSt.1
  refine rr_acc_once ar (R := SlRN (st := st) K Locks s) (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q)
    (fun q hq => ⟨hq.1, hq.2.2⟩) (fun q hq => hq.2.2) hA (E.hI a X a1' LP) (E.hPl hS a X a1' LP)
    (E.hrz hS a X a1' LP) (E.hy0r hS a X a1' LP) (E.hAs a X a1' LP)
    (fun u usc C => (F.P.hRWrG hS a X a1' LP u usc C).toNB.meet (rrAccNB_nu ar hA F hS LP C))
    (fun u usc C => ?_) hf h' Wd
  have hw := E.hSu hS a X a1' LP u usc C
  have nSt : NU K (stA (L.curW s)) := by rw [stA_eq]; exact nu_tcb hX hc0 (o := 3328#u64) (by simp) (by simp) (by simp)
  have nBl : NU K (blockA (L.curW s)) := nu_tcb hX hc0 (o := 3336#u64) (by simp) (by simp) (by simp)
  have nSu : NU K (stA u) := by rw [stA_eq]; exact nu_tcb hX hw.1 (o := 3328#u64) (by simp) (by simp) (by simp)
  exact
    { tR := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.1, nSt⟩
      tN := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.1, nSt⟩
      tB := fun _ _ => gst_write (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.1, nSt⟩
      bl := fun _ => gst_write (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.1, nBl⟩
      uI := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.2, nSu⟩
      uR := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.2, nSu⟩
      uN := SWr.of_W (W := fun q => SlWS (st := st) K Locks s q ∧ NU K q) ⟨hw.2.2.2.2, nSu⟩ }

/-- **`hro` of `sl_pathsKCG` / `sl_pathsKC5`, no program premise left.** -/
theorem sl_hro2 (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar) (hm : E2E.MasksWr st) (a0 : A) :
    ∀ K m, ReadOnce st ar (R.syscall.handle_syscall_local n found) (OwnMap.cls K) (OwnMap.ko K m)
      (· ∈ K.user) (fun s => SlJAt (L := L) K s ∧ SlQ st ar Locks n found Cs Ω Sg Ac K m s)
      (SlRS (st := st) K Locks) :=
  sl_hro ar hSt hA hm a0 (sl_rr_once ar hSt hA a0)

/-- **The syscall local path with `IsProg`, `NoZero` and `ReadOnce` all discharged** (`sl_pathsKC6` with
`hRR := sl_rr_once`). Premises: `hSt`, `hA`, `hm`, `a0`, `hCs` [P], `hKD` [P]. -/
noncomputable def sl_pathsKC7 (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s) :
    Fl4Proofs.P2.E2E.Paths Unit :=
  sl_pathsKC6 (Locks := Locks) (n := n) (found := found) ar hSt hA hm a0 hCs hKD (sl_rr_once ar hSt hA a0)

/-- **`StartAt` for `sl_pathsKC7`**. -/
theorem sl_pathsKC7_startAt (hSt : P0.StoreTotal st) (hA : P0.ArchTotal ar)
    (hm : Fl4Proofs.P2.E2E.MasksWr st) (a0 : A)
    (hCs : ∀ c ∈ Cs, c.val < 64)
    (hKD : ∀ (K : KLayout) (s : S), SlJAt (L := L) K s → KernDetAt (L := L) K Locks s)
    (K : KLayout) (m : U64 → U64) (hK : RegionOK K) (hU : Fl4Proofs.P2.E2E.UserOK K)
    {σ : S} (a : A) (hJ : SlJAt (L := L) K σ) (hq : SlQ st ar Locks n found Cs Ω Sg Ac K m σ)
    {c : U64} {hs : U64 → Prop} (hc : L.cpu σ = c) (hl : Locks σ = hs) {μ : U64 → U64}
    (hμ : ∀ x, Aligned x → x ∉ K.user → L.mem σ x = μ x) :
    Fl4Proofs.P2.E2E.StartAt
      (sl_pathsKC7 (Locks := Locks) (n := n) (found := found) ar hSt hA hm a0 hCs hKD () K m hK hU) c hs μ
      ((sl_pathsKC7 (Locks := Locks) (n := n) (found := found) ar hSt hA hm a0 hCs hKD () K m hK hU).body σ a) :=
  sl_pathsKC6_startAt ar hSt hA hm a0 hCs hKD _ K m hK hU a hJ hq hc hl hμ

end

end Fl4Proofs.P2.PathObl
