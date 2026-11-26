/-
# P2 (line p3mc, gen 19): st view pins (first part of `st_acc_v`)

At an st entry state `s` at core `c`'s view of `ρ` (a bundle state `SlJAt`, `QPs`, the view's kernel words, core `c`)
whose current thread is running (the accepted run's `StOk.run`) with a nonzero `SC` word (`StPre.sct` and the
current SC a typed SC, `st_scn`):

* **`stVC_of`**: sl's view context `SlVC` (P2/SlVPin) holds at `s` (`sl_vmBase` from `SlJAt` and the running current
  thread, then `vm_cur_home` / `vm_homes` / `vm_sc_home_of_tcb` as `slVC_of`): the current thread, the current SC, the
  release head and its SC are homed on `c`; so the pins of P2/SlVPin (`sr_tcb`, `sr_reg`, `sr_scw`, `sr_ks`,
  `vnw_tcb`, …) apply to st's read and write words;
* **`sr_timer`**: a timer word (offset 3528 … 3568) of a thread armed in `ρ` is `SR` (kept by the view, value and owner,
  no PTE word), whoever's thread (`vn_timer`);
* **`vkc_timer`**: a TCB word off `STATE` / `TIMER_DEADLINE` keeps its class owner (`ko` is `.free` there);
* **`vdec_decW`**: a word deciding a `VDD` owner (`VDec`) is a deciding word (`DecW`), so `st_wr_nondec` gives `¬ VDec`.

No premise: every fact is a hypothesis. No existing statement changed.
-/
import Fl4Proofs.P2.StAccVW
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.E2EP
open fl4_core Fl4Proofs.P0.Consts Fl4Proofs.P1 Fl4Proofs.P2 Fl4Proofs.P2.PathObl Fl4Proofs.P2.OwnMapV
  Fl4Proofs.P2.OwnMapP
open Fl4Proofs.P2.E2EV
open Fl4Proofs.P2.OwnMap (KLayout region fld oAFFINITY oTIMER_DEADLINE oTIMER_HEIGHT InW DecW ko)
open Fl4Proofs.P2.CoreView (view VN VKc VNW VDec)

noncomputable section
open Classical

section gen

/-- **Timer words of an armed thread are `SR`** (module docstring). -/
theorem sr_timer {K : KLayoutP} (hK : RegionOKP K) (hX : RegionOKX K.toKLayout) {c : U64} {ρ : U64 → U64}
    {t o : U64} (ht : K.heap t = some .tcb) (h1 : 3528 ≤ o.val) (h2 : o.val ≤ 3568) (h3 : o.val % 8 = 0)
    (h0 : ρ (fld t oTIMER_DEADLINE) ≠ 0#u64) : SR K c ρ (fld t o) := by
  obtain ⟨hr, -, -⟩ := hX.tcbW t ht o (by omega) (by omega) h3
  have hr0 : region K.toKLayout (fld t o) = .tcb t := hr
  exact ⟨CoreView.vn_timer hK hX ht h1 h2 h3 h0, fun h => by rw [hK.none _ h] at hr0; cases hr0⟩

/-- **A TCB word off `STATE` / `TIMER_DEADLINE` keeps its class owner** (module docstring). -/
theorem vkc_timer {K : KLayout} {c : U64} {ρ : U64 → U64} {x t : U64} (hr : region K x = .tcb t)
    (h1 : x.val - t.val ≠ 3328) (h2 : x.val - t.val ≠ 3528) : VKc K c ρ x := by
  have hn : ¬ (x.val - t.val = 3328 ∨ x.val - t.val = 3528) := fun h => h.elim h1 h2
  unfold VKc
  simp only [ko, hr, if_neg hn]

/-- **`VDec` words are deciding words** (module docstring). -/
theorem vdec_decW {K : KLayout} {c : U64} {ρ : U64 → U64} {q : U64} (h : VDec K c ρ q) : DecW K q := by
  rcases h with ⟨t, off, ht, -, ho, rfl⟩ | ⟨p, hp, rfl⟩ | ⟨t, ht, rfl⟩ | ⟨p, b, hb, -, rfl⟩
  · exact Or.inl ⟨t, off, ht, ho, rfl⟩
  · exact Or.inr (Or.inr (Or.inl ⟨p, hp, rfl⟩))
  · exact Or.inl ⟨t, oAFFINITY, ht, Or.inl rfl, rfl⟩
  · exact Or.inr (Or.inr (Or.inr ⟨p, b, hb, rfl⟩))

end gen

section ctx
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] [Fl4Proofs.P1.PlainStore st]

/-- The current thread's `SC` word is nonzero at an st entry (`StPre.sct`, the current SC typed, heap 0 empty). -/
theorem st_scn {K : KLayoutP} {Cs Ω Sg Ac : Set U64} {target : U64} {σ : S}
    (hJ : SlJAt (L := L) K.toKLayout σ)
    (E : StEnt (userV K.toKLayoutV) st K.toKLayoutV.heap.tcbs Cs Ω K.toKLayoutV.heap Sg K.toKLayoutV.heap.replies
      K.toKLayoutV.heap.scs K.toKLayoutV.heap.ntfns K.toKLayoutV.heap.scBits Ac target σ) :
    L.mem σ (scA (L.curW σ)) ≠ 0#u64 := by
  have hz := slJAt_heap0 hJ
  rw [E.pre.sct]
  intro e
  obtain ⟨z, hz'⟩ := E.pre.csc
  rw [e] at hz'
  have hz2 : K.toKLayout.heap 0#u64 = some (.sc z) := hz'
  rw [hz] at hz2
  cases hz2

/-- **sl's view context at an st entry with a running current thread** (module docstring). -/
theorem stVC_of {K : KLayoutP} (nv : K.vcpus = ∅) (hK : RegionOKP K) (hU : UserOKP K) {c : U64}
    {ρ : U64 → U64} {s : S} (hJ : SlJAt (L := L) K.toKLayout s) (hq : QPs K st s) (hc : L.cpu s = c)
    (hm : ∀ x, Aligned x → x ∉ K.user → L.mem s x = view K.toKLayout c ρ x)
    (hrun : L.mem s (stA (L.curW s)) = sched.TS_RUNNING) (scn : L.mem s (scA (L.curW s)) ≠ 0#u64) :
    SlVC (L := L) K c ρ s := by
  obtain ⟨Cs', Ac', Ω', BV, BP⟩ := sl_vmBase (st := st) nv hK hq.ks hJ (Or.inr hrun)
  exact
  { hK := hK
    cpu := hc
    hm := hm
    cur := vm_cur_home hK BV hm
    csc := (vm_homes BP hm).1 scn
    rh := (vm_homes BP hm).2
    scb := fun p hp h0 => vm_sc_home_of_tcb BP hm hp h0
    ks := hq.ks
    ksb := hq.ksb
    tab := hq.tab
    upte := userNoE_pte hU
    scn := scn }

end ctx

end
end Fl4Proofs.P2.E2EP
