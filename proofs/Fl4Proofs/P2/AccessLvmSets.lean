/-
# P2 (line lvm, gen 5): **`local_vm_exit`'s read / write / decline sets** for `ownV` and the per-write check

The concrete sets of `PathObl` for `handle_vcpu_exit_local` under rule 7 (`OwnMapV.ownV`), maximal as the
existing paths' (`SlRS` / `SlWS`: aligned user words and the words the path may read / write by the map):

* `VexitRS` / `VexitWS`: aligned words that are user words or `RPerm` / `WPerm` for `ownV` at the entry state,
  with the glue's locks (`lock v` among them, so `v`'s non-binding words are in both); `VexitDS` = `IrqDec`
  (`update_timestamp`'s node `CUR_TIME` / `CONSUMED`: a decline after the timestamp update writes only these).
  Because the sets are stated for `ownV`, `NoVcpuRd`'s problem (`E2EVTop.not_noVcpuRd`) does not arise: a
  non-binding word of a VCPU other than `v` is in neither.
* `vexit_read_own`, `vexit_write_own`, `vexit_aligned`: `PathObl.read_own` / `write_own` / `aligned` for these
  sets (the decline words are this core's node words: `IrqEnt.dec`'s facts, `ownV_off` as a node word is no VCPU
  word).
* `vexitRS_wr_user` / `vexitWS_wr_user` / `vexitDS_wr_user`: `PathSide.user_free`'s set equations (a user write
  moves no owner, `OwnMapV.ownDepV`).
* **`stepOKV_one`**: the per-write check (`move`'s `mguard`) of a one-word write under `ownV`: a VCPU word
  (rule 7: no owner moves, class free, `stepOKV_vcpu`), or a write `own`'s check accepts (`stepOKV_of_stepOK`).
  The exit path's writes are `ct`'s registers / `STATE`, the buffer, this core's node words, the current SC's
  `CONSUMED` (`own`'s checks, as in `FootTimerSetObl` / `FootTimerIrqObl`) and `v.PENDING` (rule 7).

No named premises.
-/
import Fl4Proofs.P2.AccessLvmFin
import Fl4Proofs.P2.FootTimerIrqObl
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMapV
open Fl4Proofs.P2.PathObl (RPerm WPerm StepOK)

section
variable {S : Type} {st : machine.Store S} [L : LawfulStore st] {K : KLayoutV}

/-- What `local_vm_exit` may read: aligned user words and the words it may read by `ownV`. -/
def VexitRS (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (lk : S → U64 → Prop) (s : S) (x : U64) :
    Prop :=
  Aligned x ∧ (x ∈ K.user ∨ RPerm (ownV K) (L.cpu s) (lk s) (L.mem s) x)

/-- What an accepted `local_vm_exit` may write. -/
def VexitWS (K : KLayoutV) (st : machine.Store S) [L : LawfulStore st] (lk : S → U64 → Prop) (s : S) (x : U64) :
    Prop :=
  Aligned x ∧ (x ∈ K.user ∨ WPerm (ownV K) (L.cpu s) (lk s) (L.mem s) x)

/-- What a declined `local_vm_exit` may write (`update_timestamp`'s node words). -/
abbrev VexitDS (st : machine.Store S) [L : LawfulStore st] (s : S) (x : U64) : Prop := IrqDec st s x

variable {lk : S → U64 → Prop}

theorem vexit_read_own {s : S} {x : U64} (h : VexitRS K st lk s x) (hu : x ∉ K.user) :
    RPerm (ownV K) (L.cpu s) (lk s) (L.mem s) x :=
  h.2.resolve_left hu

/-- A node word of the core is held by it under `ownV`. -/
theorem ownV_node (hK : RegionOKV K) {m : U64 → U64} {q c : U64}
    (hq : OwnMap.own K.toKLayout m q = .core c) (hr : ∃ d, OwnMap.region K.toKLayout q = .node d) :
    ownV K m q = .core c := by
  have hn : ¬ ∃ w, InVcpu K w q := by
    rintro ⟨w, hw⟩
    obtain ⟨d, hd⟩ := hr
    rw [hK.none w q hw] at hd; cases hd
  rw [ownV_off hn]; exact hq

theorem vexit_write_own (hK : RegionOKV K) {s : S} {x : U64}
    (hD : ∀ q, IrqDec st s q → OwnMap.own K.toKLayout (L.mem s) q = .core (L.cpu s) ∧
      ∃ d, OwnMap.region K.toKLayout q = .node d)
    (h : VexitWS K st lk s x ∨ VexitDS st s x) (hu : x ∉ K.user) :
    WPerm (ownV K) (L.cpu s) (lk s) (L.mem s) x := by
  rcases h with h | h
  · exact h.2.resolve_left hu
  · obtain ⟨e1, e2⟩ := hD x h
    unfold WPerm; rw [ownV_node hK e1 e2]; rfl

theorem vexit_aligned {s : S} {x : U64} (hDa : ∀ q, IrqDec st s q → Aligned q)
    (h : VexitWS K st lk s x ∨ VexitDS st s x) : Aligned x := by
  rcases h with h | h
  · exact h.1
  · exact hDa x h

/-- A user write keeps the read set (`PathSide.user_free`). -/
theorem vexitRS_wr_user (hK : RegionOKV K) (hU : UserOKV K) {s : S} {b v : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (hlk : lk (L.wr s b v) = lk s) :
    VexitRS K st lk (L.wr s b v) = VexitRS K st lk s := by
  have eo : ownV K (L.mem (L.wr s b v)) = ownV K (L.mem s) :=
    ownDepV hK hU _ _ fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (by subst e; exact hb))
  funext x
  simp only [VexitRS, RPerm, PathObl.GateOnly, eo, hlk, L.cpu_wr]

theorem vexitWS_wr_user (hK : RegionOKV K) (hU : UserOKV K) {s : S} {b v : U64} (hb : b ∈ K.user)
    (hba : Aligned b) (hlk : lk (L.wr s b v) = lk s) :
    VexitWS K st lk (L.wr s b v) = VexitWS K st lk s := by
  have eo : ownV K (L.mem (L.wr s b v)) = ownV K (L.mem s) :=
    ownDepV hK hU _ _ fun x hx hxu => mem_wr_ne' hba hx (fun e => hxu (by subst e; exact hb))
  funext x
  simp only [VexitWS, WPerm, eo, hlk, L.cpu_wr]

theorem vexitDS_wr_user (s : S) (b v : U64) : VexitDS st (L.wr s b v) = VexitDS st s :=
  irq_dec_user s b v

end

/-- **The per-write check of a one-word write under `ownV`** (module docstring). -/
theorem stepOKV_one {K : KLayoutV} (hK : RegionOKV K) {m m' : U64 → U64} {a : U64}
    (hone : ∀ y, m' y ≠ m y → y = a) (m0 : U64 → U64) (User : U64 → Prop) (c : U64) (lk : U64 → Prop)
    (h : (∃ w, InVcpu K w a) ∨
      StepOK (OwnMap.own K.toKLayout) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) User c lk m m') :
    StepOK (ownV K) (OwnMap.cls K.toKLayout) (OwnMap.ko K.toKLayout m0) User c lk m m' := by
  rcases h with h | h
  · exact stepOKV_vcpu hK (fun y hy => by rw [hone y hy]; exact h) m0 User c lk
  · exact stepOKV_of_stepOK hK h

end Fl4Proofs.P2
