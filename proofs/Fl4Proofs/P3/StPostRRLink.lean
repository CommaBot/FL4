/-
P1 side of line stpost (generation 2): **the general ReplyRecv path decodes the fast path's caps**.

P3 proves the ReplyRecv entry only through the general path, whose dispatch invokes the cap the
`REPLY` register names over every cap type (an Untyped there retypes and grows the ghosts). On
the local path's accepted ReplyRecv arm, fl4-sync's `found` is `reply_caps` at the entry state
(`syscall_local_same`'s contract `hfd`); `local_prefix_keep` carries it to the general path's
dispatch state (after the `FAULT_IP` write and a passing `budget_ok`). Here:

* `rr_front_rcaps`: at that dispatch state the current thread is the same and `RCaps` holds
  (`reply_caps_some`): the `REPLY` register resolves to a Reply cap of `found.1`, the `CAP`
  register to a receive-capable Endpoint cap of `found.2`;
* `RCaps.replyLookup` / `RCaps.capLookup`: the same through `cspace.lookup_slot` (the lookup
  `handle_invocation` / `handle_recv` make).

No premise beyond `syscall_local_same`'s (`BXI`, `CnOff` at the entry state).
-/
import Fl4Proofs.P1.FastSysLocal
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P1
open fl4_core Fl4Proofs.P0.Consts

section
variable {S : Type _} {A : Type _} {st : machine.Store S} (ar : machine.Arch A) [L : LawfulStore st]

/-- **The fast path's caps at the general path's dispatch state** (module docstring). -/
theorem rr_front_rcaps (hA : P0.ArchTotal ar) {T Cs Sg : Set U64} {s s1 s2 : S} {a a2 : A}
    {Ω Rp Scs Nt Ac : Set U64} {H : Heap} {Z : U64 → Nat} (hI : BXI st T Cs Ω H Sg Rp Scs Nt Z Ac s)
    (hCn : ∀ t, sched.cur_thread st s = ok t → CnOff (L := L) T Cs Sg s t) {t v rptr ep : U64}
    (et : sched.cur_thread st s = ok t)
    (es1 : obj.Tcb.set_reg st t s layout.reg.FAULT_IP v = ok s1)
    (hb : syscall.budget_ok st ar s1 a = ok (true, s2, a2))
    (hrc : fastpath.reply_caps st s t = ok (some (rptr, ep))) :
    sched.cur_thread st s2 = ok t ∧ RCaps st s2 t rptr ep := by
  obtain ⟨⟨Q, R, hSQ⟩, -, -, -, -⟩ := hI
  have hT : TcbPlaced T := hSQ.tcbs
  have hcC : L.cpu s ∈ Cs := hSQ.cur
  have hN : NodePlaced st T s (L.cpu s) := hSQ.nodes _ hcC
  have hcT : L.curW s ∈ T := hSQ.curT
  have htT : t ∈ T := by
    have et' := et
    rw [cur_thread_ok] at et'; rw [← ok_inj_ff et']; exact hcT
  obtain ⟨et2, hrcK⟩ := local_prefix_keep ar hT hN hcC et htT (hCn t et) es1 hb hA
  exact ⟨et2, reply_caps_some st (hrcK rptr ep hrc)⟩

omit L in
/-- `RCaps`'s Reply cap through `cspace.lookup_slot`. -/
theorem RCaps.replyLookup {s : S} {t rptr ep : U64} (h : RCaps st s t rptr ep) :
    ∃ i found g, obj.Tcb.reg st t s layout.reg.REPLY = ok i ∧
      cspace.lookup_slot st s t i = ok (core.result.Result.Ok found) ∧
      obj.Slot.cap st found.slot s = ok (capability.Cap.Reply rptr g) := by
  obtain ⟨sl, root, hsl, hroot, ⟨i, found, g, hi, hr, hc⟩, -⟩ := h.root
  refine ⟨i, found, g, hi, ?_, hc⟩
  unfold cspace.lookup_slot
  rw [hsl]; simp only [bind_ok]
  rw [hroot]; simp only [bind_ok]
  exact hr

omit L in
/-- `RCaps`'s Endpoint cap through `cspace.lookup_slot`. -/
theorem RCaps.capLookup {s : S} {t rptr ep : U64} (h : RCaps st s t rptr ep) :
    ∃ i1 found1 b0 b1 b3 b4, obj.Tcb.reg st t s layout.reg.CAP = ok i1 ∧
      cspace.lookup_slot st s t i1 = ok (core.result.Result.Ok found1) ∧
      obj.Slot.cap st found1.slot s = ok (capability.Cap.Endpoint ep b0 b1 true b3 b4) := by
  obtain ⟨sl, root, hsl, hroot, -, ⟨i1, found1, b0, b1, b3, b4, hi, hr, hc⟩⟩ := h.root
  refine ⟨i1, found1, b0, b1, b3, b4, hi, ?_, hc⟩
  unfold cspace.lookup_slot
  rw [hsl]; simp only [bind_ok]
  rw [hroot]; simp only [bind_ok]
  exact hr

end

end Fl4Proofs.P1
