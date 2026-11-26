/-
# P2 (line slhuf, generation 13): the sender-side IPC buffer premise, 128 words (`InvBufSJ8`)

The Copy / Mint decode reads arguments 4 / 5 (`copied_cap`: `buf + 40`, `buf + 48`) through the buffer the
send-side lookup `msg.lookup_ipc_buffer st s false t` returns (it also accepts a read-only frame,
crates/fl4-core/src/msg.rs l.28). As invj's `InvBufJ8` (receive side), only the 128 buffer words are claimed.

* `InvBufSJ8`, **`invBufSJ8_of`**: proved at every `SlJAt` state from P3 (`JAtZ.xferH`'s `BufCover`: for either
  side, every TCB's buffer words are `Z.B` words; `EPlaced.balign`; `K.user = Z.B`'s addresses, `B.user`), as
  `invBufJ8_of` and `JAtZ.sbufOK`. No premise.

No existing statement changes.
-/
import Fl4Proofs.P2.InvTrunc8
import Fl4Proofs.P3.BufJ
import Fl4Proofs.P3.IpcBuf
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P2.PathObl
open fl4_core Fl4Proofs.P1
open Fl4Proofs.P2.OwnMap (KLayout)

section buf
variable {S : Type} {st : machine.Store S} [L : LawfulStore st]

variable (st) in
/-- (slhuf gen 13) **The caller's send-side IPC-buffer words are aligned user words**, for the 128 words of the
buffer (`InvBufJ8` for the lookup `msg.lookup_ipc_buffer st s false`). -/
def InvBufSJ8 (K : KLayout) (s : S) : Prop :=
  ∀ b, msg.lookup_ipc_buffer st s false (L.curW s) = ok b → b ≠ 0#u64 → ∀ i : U64, i.val < 128 →
    UserW K (core.num.U64.wrapping_add b (core.num.U64.wrapping_mul i 8#u64))

/-- (slhuf gen 13) **`InvBufSJ8` at every bundle state** (`JAtZ.xferH`'s `BufCover` for the send side,
`EPlaced.balign`, `B.user`). No premise. -/
theorem invBufSJ8_of {K : KLayout} {s : S} (hJ : SlJAt (L := L) K s) : InvBufSJ8 st K s := by
  obtain ⟨A', arI, AR, Zx, Cx, Ax, Lst, D, a', σ, B⟩ := hJ
  intro b hb hb0 i hi
  have hcur : L.curW s ∈ Heap.tcbs K.heap := B.j.kern.curH
  obtain ⟨Tr, Cq, hJp⟩ := B.j.jpl
  have hth : Zx.th (L.curW s) = some .tcb := (hJp.tcb _).2 hcur
  have hyT := B.j.thT _ hth
  obtain ⟨xd, hk, hws⟩ := B.j.buf _ hyT
  obtain ⟨hOK, hBC, -⟩ := B.j.xferH
  obtain ⟨w, hw', hP⟩ := spec_ex_fd (Fl4Proofs.P3.Endp.lookup_buf_full s σ B.j.xtop.rel.2.1.1
    B.j.xtop.rel.2.1.2.1 hth hk hOK false)
  rw [hb] at hw'
  have e0 : b = w := ok_inj_ff hw'
  subst e0
  obtain ⟨h0, hp⟩ := hP
  cases hbo : Fl4Proofs.P3.Endp.ipcBufOf false xd with
  | none => exact absurd (h0.2 hbo) hb0
  | some p' =>
    have e := hp hws p' hbo
    have hwB := hBC _ hyT xd false p' hk hbo b e i hi
    refine ⟨(B.j.xtop.fin.1.2.ep.balign _ hwB).1, ?_⟩
    rw [B.user]; exact ⟨_, hwB, rfl⟩

end buf

end Fl4Proofs.P2.PathObl
