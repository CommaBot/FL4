/-
# P2 (line slhuf, gen 12): the Copy / Mint arm's entry facts from `InvQCMF`

The `del_core` / `delEnt_of` / `invSeen_of` / `invPs_of` analogues (P2/InvSeen.lean) for CNodeCopy / CNodeMint:

* `LecProv`, `lec_body_prov`, `lec_loop_prov`, **`lec_slot0`**: a non-null first extra cap of `lookup_extra_caps` is
  the slot of a successful `lookup_slot` from the thread (the cap lookups it makes);
* `lss_root` (a successful `lookup_source_slot` walks from a CNode cap), `lss_cn` (`lts_cn` for the source);
* **`cm_core`** (no premise): from `InvQCMF` — `plan_with_cmF` on `InvEx`'s plan, `InvCMArm` for the label,
  `IoPre.walk`'s closure `C`: the invoked CNode, the first extra cap (in `C` by `lec_slot0` and the closure), the
  target and the source as capability slots outside the objects, the locks the plan took, the seen words `CMW`;
* **`cmEnt_of`** (`CMEnt` from [J] `InvCdtJ` and [J] `hz : 0 ∉ K.slots`), `cmSl_of`, `cmPs_of` (the invoked slot's
  cap words in `IoRS`), **`cmSeen_of`** (`InvSeenRS` for `Q := InvQCMF`, from [J] `hz`).

Named premises: [J] `InvCdtJ` (`cmEnt_of`), [J] `hz` (`cmEnt_of`, `cmSeen_of`). No existing statement changes.
-/
import Fl4Proofs.P2.InvCMEnt
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout InNode InW fld own region RegionOK GateField TimerField NullOrFrame TcbSlot)

/-! ## The extra caps' provenance -/

section lec
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- A slot word `lookup_extra_caps` may return: null, or a successful lookup's slot. -/
def LecProv (s : S) (t : obj.Tcb) (w : U64) : Prop :=
  w = 0#u64 ∨ ∃ c r, cspace.lookup_slot st s t c = ok (core.result.Result.Ok r) ∧ r.slot = w

theorem lec_body_prov {s : S} {t : obj.Tcb} {buf n i : U64} {caps : Array obj.Slot 3#usize}
    {y : ControlFlow (Array obj.Slot 3#usize × U64) (core.result.Result (Array obj.Slot 3#usize) error.Fault)}
    (hy : ipc.lookup_extra_caps_loop.body st s t buf n caps i = ok y) (hc : ∀ w ∈ caps.val, LecProv st s t w) :
    (∀ x, y = ControlFlow.cont x → ∀ w ∈ x.1.val, LecProv st s t w) ∧
      (∀ z, y = ControlFlow.done (core.result.Result.Ok z) → z = caps) := by
  unfold ipc.lookup_extra_caps_loop.body at hy
  by_cases c1 : i < n
  · rw [if_pos c1] at hy
    by_cases c2 : i < 3#u64
    · rw [if_pos c2] at hy
      obtain ⟨i1, -, hy⟩ := bind_eq_ok hy
      obtain ⟨i2, -, hy⟩ := bind_eq_ok hy
      obtain ⟨cp, -, hy⟩ := bind_eq_ok hy
      obtain ⟨r, er, hy⟩ := bind_eq_ok hy
      cases r with
      | Err lf =>
        try dsimp only at hy
        have e := ok_inj_ff hy
        subst e
        exact ⟨fun x hx => (by cases hx), fun z hz => (by cases hz)⟩
      | Ok r1 =>
        try dsimp only at hy
        obtain ⟨i3, -, hy2⟩ := bind_eq_ok hy
        obtain ⟨a', ea, hy2⟩ := bind_eq_ok hy2
        obtain ⟨i4, -, hy2⟩ := bind_eq_ok hy2
        have e := ok_inj_ff hy2
        subst e
        refine ⟨fun x hx w hw => ?_, fun z hz => (by cases hz)⟩
        injection hx with hx
        subst hx
        unfold Aeneas.Std.Array.update at ea
        split at ea
        · simp at ea
        · have e := ok_inj_ff ea
          subst e
          have hw' : w ∈ caps.val.set i3.val r1.slot := by first | exact hw | simpa using hw
          rcases List.mem_or_eq_of_mem_set hw' with h | h
          · exact hc w h
          · exact Or.inr ⟨cp, r1, er, h.symm⟩
    · rw [if_neg c2] at hy
      have e := ok_inj_ff hy
      subst e
      refine ⟨fun x hx => (by cases hx), fun z hz => ?_⟩
      injection hz with hz
      injection hz with hz
      exact hz.symm
  · rw [if_neg c1] at hy
    have e := ok_inj_ff hy
    subst e
    refine ⟨fun x hx => (by cases hx), fun z hz => ?_⟩
    injection hz with hz
    injection hz with hz
    exact hz.symm

theorem lec_loop_prov {s : S} {t : obj.Tcb} {buf n : U64} :
    ∀ (N : Nat) (caps : Array obj.Slot 3#usize) (i : U64) (e : Array obj.Slot 3#usize),
      3 - i.val < N → (∀ w ∈ caps.val, LecProv st s t w) →
      ipc.lookup_extra_caps_loop st s t buf caps n i = ok (core.result.Result.Ok e) →
      ∀ w ∈ e.val, LecProv st s t w := by
  intro N
  induction N with
  | zero => intro _ _ _ hN; omega
  | succ N ih =>
    intro caps i e hN hc h
    rw [lecLoop_unfold] at h
    obtain ⟨y, hy, hk⟩ := bind_eq_ok h
    have hne : ∀ f, y ≠ ControlFlow.done (core.result.Result.Err f) := by
      rintro f rfl; simp at hk
    obtain ⟨-, hmeas⟩ := lec_body_keep (s' := s) (fun _ _ => rfl) (fun _ _ h => h) hy hne
    obtain ⟨hcont, hdone⟩ := lec_body_prov hy hc
    cases y with
    | done z =>
      have ez : z = core.result.Result.Ok e := ok_inj_ff hk
      subst ez
      rw [hdone e rfl]; exact hc
    | cont x =>
      obtain ⟨h3, hx⟩ := hmeas x rfl
      exact ih x.1 x.2 e (by omega) (hcont x rfl) hk

/-- (slhuf gen 12) **A non-null first extra cap is a lookup's slot.** -/
theorem lec_slot0 {s : S} {t : obj.Tcb} {buf : U64} {info : msginfo.MessageInfo}
    {e : Array obj.Slot 3#usize} {s1 : obj.Slot}
    (h : ipc.lookup_extra_caps st s t buf info = ok (core.result.Result.Ok e))
    (h0 : Aeneas.Std.Array.index_usize e 0#usize = ok s1) (hs : s1 ≠ 0#u64) :
    ∃ c r, cspace.lookup_slot st s t c = ok (core.result.Result.Ok r) ∧ r.slot = s1 := by
  have hlen : e.val.length = 3 := by have hp := e.property; simpa using hp
  have hl : (0#usize).val < e.length := by
    first | (simp only [Aeneas.Std.Array.length]; simp; omega) | (simp only [Aeneas.Std.Array.length]; simp [hlen]) | simp [Aeneas.Std.Array.length, hlen] | (simp; omega)
  rw [eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec e 0#usize hl)] at h0
  have hm : s1 ∈ e.val := by rw [← ok_inj_ff h0]; exact List.getElem_mem _
  have h0s : ∀ w ∈ ipc.NO_EXTRA_CAPS.val, LecProv st s t w := fun w hw => Or.inl (by
    first
    | simpa [ipc.NO_EXTRA_CAPS] using hw
    | (simp [ipc.NO_EXTRA_CAPS, Aeneas.Std.Array.make] at hw; exact hw))
  unfold ipc.lookup_extra_caps at h
  by_cases hb : buf = 0#u64
  · rw [if_pos hb] at h
    have he := ok_inj_ff h
    injection he with he
    subst he
    exact ((h0s s1 hm).resolve_left hs)
  · rw [if_neg hb] at h
    exact (lec_loop_prov 4 _ _ e (by simp) h0s h s1 hm).resolve_left hs

/-- A successful `lookup_source_slot` walks from a CNode cap. -/
theorem lss_root {s : S} {root : capability.Cap} {cptr depth : U64} {src : obj.Slot}
    (h : cspace.lookup_source_slot st s root cptr depth = ok (.Ok src)) : ∃ p r g k, root = .CNode p r g k := by
  unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at h
  obtain ⟨b, eb, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  cases root <;> simp at eb ⊢

/-- `lookup_source_slot`'s slot is a radix-masked slot of a CNode of a closed set containing the root's CNode. -/
theorem lss_cn {s : S} {root : capability.Cap} {cptr depth : U64} {src : obj.Slot} {C : U64 → U64 → Prop}
    (hroot : ∀ p r gs g, root = .CNode p r gs g → C p r) (hcl : WalkCl (st := st) s C)
    (h : cspace.lookup_source_slot st s root cptr depth = ok (.Ok src)) :
    ∃ q r m y, C q r ∧ cspace.mask r = ok m ∧ src = cnSlot q (y &&& m) := by
  unfold cspace.lookup_source_slot cspace.lookup_slot_for_cnode_op at h
  obtain ⟨b, -, h⟩ := bind_eq_ok h
  cases b
  · simp at h
  rw [if_pos rfl] at h
  split at h
  · simp at h
  split at h
  · simp at h
  obtain ⟨r, er, h⟩ := bind_eq_ok h
  cases r with
  | Err lf => simp at h
  | Ok r1 =>
    simp only at h
    split at h
    · simp at h
    · have e := ok_inj_ff h
      simp only [core.result.Result.Ok.injEq] at e
      obtain ⟨q, r, m, y, hq, hm, hs⟩ := rab_loop_slot st C hcl 66 root _ 65#u64 r1 (by simp) hroot er
      exact ⟨q, r, m, y, hq, hm, by rw [← e, hs]⟩

end lec

/-! ## From `InvQCMF` at the entry -/

section ent
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]
variable {Cs Ω Sg Ac : Set U64} {Locks : S → U64 → Prop} {p : localinv.Plan} {K : KLayout} {μ : U64 → U64}
  {s : S}

/-- (slhuf gen 12) **The Copy / Mint arm's facts at the entry from `InvQCMF`** (no premise; `del_core`'s analogue):
the invoked slot a capability slot holding a CNode cap; the first extra cap a non-null capability slot holding a
CNode cap; the target and the source capability slots outside the objects, the source a non-EPT Frame cap, the
target's first word `Null`; both CNodes in the walk closure `C`; the locks the plan took (as `Locks`); the seen
words `CMW dest src`. -/
theorem cm_core (hq : InvQCMF st Cs Ω Sg Ac Locks p K μ s) :
    ∃ (cp cr cg cgb dest s1 rp rr rg rgb src fp rt asid va : U64) (sz : capability.FrameSize) (d mp : Bool)
      (c1 : capability.Cap) (C : U64 → U64 → Prop),
      obj.Slot.cap st p.slot s = ok (.CNode cp cr cg cgb) ∧ p.slot ∈ K.slots ∧
      Aeneas.Std.Array.index_usize p.extra 0#usize = ok s1 ∧ s1 ≠ 0#u64 ∧
      cspace.lookup_target_slot st s (.CNode cp cr cg cgb) (L.mem s (regA (L.curW s) layout.reg.R10))
        (L.mem s (regA (L.curW s) layout.reg.R8)) = ok (.Ok dest) ∧
      obj.Slot.cap st s1 s = ok (.CNode rp rr rg rgb) ∧
      cspace.lookup_source_slot st s (.CNode rp rr rg rgb) (L.mem s (regA (L.curW s) layout.reg.R9))
        (L.mem s (regA (L.curW s) layout.reg.R15)) = ok (.Ok src) ∧
      obj.Slot.cap st src s = ok (.Frame fp sz rt d mp false asid va) ∧
      capability.Cap.decode (L.mem s (core.num.U64.wrapping_add dest layout.cte.CAP0)) 0#u64 = ok c1 ∧
      capability.Cap.is_null c1 = ok true ∧
      C cp cr ∧ C rp rr ∧ WalkCl (st := st) s C ∧
      (∀ p r m y, C p r → cspace.mask r = ok m → cnSlot p (y &&& m) ∈ K.slots ∧
        OutsideObjs st K.heap.tcbs Cs s (cnSlot p (y &&& m)) ∧
        OutsideObjs st K.heap.tcbs Cs s (core.num.U64.wrapping_add (cnSlot p (y &&& m)) 8#u64)) ∧
      s1 ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s s1 ∧
      dest ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s dest ∧ (dest ≠ 0#u64 → Locks s dest) ∧
      src ∈ K.slots ∧ OutsideObjs st K.heap.tcbs Cs s src ∧ (src ≠ 0#u64 → Locks s src) ∧
      (∀ nx, obj.Slot.next st src s = ok nx → nx ≠ 0#u64 → Locks s nx) ∧
      (∀ x, SeenW p x → CMW dest src x) := by
  obtain ⟨⟨⟨PE, -⟩, -, harm, hlk⟩, ⟨x, hx, hxs⟩, ⟨info, buf, ei, eb, ee, hpw⟩⟩ := hq
  have hl := harm _ _ (cur_thread_ok s) ei
  obtain ⟨cp, cr, cg, cgb, dest, s1, src, fp, rt, asid, va, sz, d, mp, rc, c1, hcap, hex, hs10, htg, erc, er1,
    hsc, ec1, eb1, hHd, hHs, hHn, hSn⟩ := plan_with_cmF hl hpw
  obtain ⟨rp, rr, rg, rgb, hrc⟩ := lss_root er1
  subst hrc
  obtain ⟨C, hroot, hcl, hC⟩ := PE.walk
  -- the invoked slot
  obtain ⟨q0, r0, m0, y0, hq0, hm0, hs0⟩ := lookup_slot_cn hroot hcl hx
  rw [hxs] at hs0
  have hCc : C cp cr := hcl q0 r0 m0 y0 cp cr cg cgb hq0 hm0 (by rw [← hs0]; exact hcap)
  -- the first extra cap
  obtain ⟨c2, x2, hx2, hxs2⟩ := lec_slot0 ee hex hs10
  obtain ⟨q2, r2, m2, y2, hq2, hm2, hs2⟩ := lookup_slot_cn hroot hcl hx2
  rw [hxs2] at hs2
  have hCr : C rp rr := hcl q2 r2 m2 y2 rp rr rg rgb hq2 hm2 (by rw [← hs2]; exact erc)
  have hS1 := hC q2 r2 m2 y2 hq2 hm2
  rw [← hs2] at hS1
  -- the target and the source
  obtain ⟨q1, r1, m1, y1, hq1, hm1, hs1⟩ := lts_cn (fun p r gs g e => by cases e; exact hCc) hcl htg
  have hD := hC q1 r1 m1 y1 hq1 hm1
  rw [← hs1] at hD
  obtain ⟨q3, r3, m3, y3, hq3, hm3, hs3⟩ := lss_cn (fun p r gs g e => by cases e; exact hCr) hcl er1
  have hR := hC q3 r3 m3 y3 hq3 hm3
  rw [← hs3] at hR
  have held : ∀ y, PHeld p y → Locks s y := fun y ⟨j, hj, hy⟩ => hlk j y hj hy
  refine ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, hcap, ?_, hex,
    hs10, htg, erc, er1, hsc, ec1, eb1, hCc, hCr, hcl, hC, hS1.1, hS1.2.1, hD.1, hD.2.1,
    fun hd => held _ (hHd hd), hR.1, hR.2.1, fun hd => held _ (hHs hd), fun nx e hne => held _ (hHn nx e hne), ?_⟩
  · rw [hs0]; exact (hC q0 r0 m0 y0 hq0 hm0).1
  · intro w ⟨i, q, hi, hiM, hidx, hq⟩
    have hM : localinv.MAX_LOCKS.val = 4 := maxLocks_val
    have hiv : i.val < 4 := by have : i.val < localinv.MAX_LOCKS.val := hiM; omega
    have hlen : p.seen.val.length = 4 := by have hp := p.seen.property; simpa using hp
    have hl : i.val < p.seen.length := by simp only [Aeneas.Std.Array.length]; omega
    rw [eq_of_spec_fd (Aeneas.Std.Array.index_usize_spec p.seen i hl)] at hidx
    have e := ok_inj_ff hidx
    subst e hq
    exact hSn i.val (by omega) hi

/-- (slhuf gen 12) **`CMEnt` at the entry** from `InvQCMF` and the [J] facts at `s` (`InvCdtJ` for some `P` with
`P s`; `hz`: `0` is no capability slot). -/
theorem cmEnt_of {P : S → Prop} (hPs : P s) (hq : InvQCMF st Cs Ω Sg Ac Locks p K μ s)
    (hcdt : InvCdtJ st K P) (hz : (0#u64) ∉ K.slots) : CMEnt st K Cs Locks p s := by
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, hcap, -, hex,
    hs10, htg, erc, er1, hsc, ec1, eb1, hCc, hCr, hcl, hC, hs1K, hs1O, hdK, hdO, hLd, hsK, hsO, hLs, hLn, -⟩ :=
    cm_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hz (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hz (e ▸ hsK)
  obtain ⟨-, hcN⟩ := hcdt s src hPs hsK
  exact ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, hcap, hex, hs10,
    htg, erc, er1, hsc, ec1, eb1, hCc, hCr, hcl, hC, hs1K, hs1O, hdK, hdO, hLd hd0, hsK, hsO, hLs hsr0,
    fun nx e hne => ⟨hcN nx e hne, hLn nx e hne⟩⟩

/-- (slhuf gen 12) The invoked slot is a capability slot (no premise). -/
theorem cmSl_of (hq : InvQCMF st Cs Ω Sg Ac Locks p K μ s) : p.slot ∈ K.slots := by
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsK, -⟩ := cm_core hq
  exact hsK

/-- (slhuf gen 12) **`hps` for `Q := InvQCMF`** (no premise): the invoked slot holds a CNode cap, so both cap words
are the gate's (`IoPre.slot`). -/
theorem cmPs_of :
    ∀ K μ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s →
      IoRS (st := st) K Locks s p.slot ∧ IoRS (st := st) K Locks s (core.num.U64.wrapping_add p.slot 8#u64) := by
  intro K μ s _ hq
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcap, hsK, -⟩ := cm_core hq
  exact PE.slot hsK (Or.inr (cap_not_nof hcap (Or.inl ⟨_, _, _, _, rfl⟩)))

/-- (slhuf gen 12) **`hSeen` for `Q := InvQCMF`**: the seen words are the target's `CAP0` and the source's `CAP0`,
`CAP1`, `NEXT`, words of capability slots whose locks the glue holds ([J] `hz`: both are not `0`, so `Plan.add`
took them). -/
theorem cmSeen_of
    (hz : ∀ K μ s, SlJAt (L := L) K s → InvQCMF st Cs Ω Sg Ac Locks p K μ s → (0#u64) ∉ K.slots) :
    InvSeenRS st Locks p (InvQCMF st Cs Ω Sg Ac Locks p) := by
  intro K μ s hJ hq x hx
  have PE := hq.1.1.1
  obtain ⟨cp, cr, cg, cgb, dest, s1, rp, rr, rg, rgb, src, fp, rt, asid, va, sz, d, mp, c1, C, -, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, -, hdK, -, hLd, hsK, -, hLs, -, hSn⟩ := cm_core hq
  have hd0 : dest ≠ 0#u64 := fun e => hz K μ s hJ hq (e ▸ hdK)
  have hsr0 : src ≠ 0#u64 := fun e => hz K μ s hJ hq (e ▸ hsK)
  rcases hSn x hx with rfl | rfl | rfl | rfl
  · exact (PE.lockSlot hdK (hLd hd0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.CAP0]) (by simp [layout.cte.CAP0])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.CAP1]) (by simp [layout.cte.CAP1])).1
  · exact (PE.lockSlot hsK (hLs hsr0) (by simp [layout.cte.NEXT]) (by simp [layout.cte.NEXT])).1

end ent

end Fl4Proofs.P2.PathObl
