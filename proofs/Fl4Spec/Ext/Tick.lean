/-
FL4 differences (PORTING.md, "FL4 differences"): **one clock reading as an
environment step** (FL4 #71 / PR #66, the fl4-sync local entries; KENTRY-PLAN
`lcd`).

l4v's clock is the machine state's time oracle: `getCurrentTime` (MachineOps,
rt RISCV64 / X64 gap) advances the oracle position `time_state` by one,
reads `time_oracle` there (the time passed since the previous reading) and
records the new value in `last_machine_time`. Every kernel entry reads it once,
in `updateTimeStamp`.

FL4's fl4-sync tries a syscall or a VM fault first on a path beside its serial
gate (`fl4_core::syscall::*_local`); such a path reads the clock
(`update_timestamp`) and may then decline, after which the general entry runs
and reads the clock again. The second reading supersedes the first in every
kernel word (two timestamp updates leave what the later one alone leaves), so
the only trace of the declined attempt in the spec's terms is one consumed
oracle reading: the hardware clock advanced between the two reads.

* `clockTickMs ms`: the machine state after one `getCurrentTime` (its state
  change, without the returned value).
* `fl4ClockTick σ`: an environment step that only consumes one clock-oracle
  reading (the hardware clock advancing); nothing else of `σ` changes. l4v
  counterpart: the machine state's time oracle (`time_oracle`, `time_state`,
  `last_machine_time`) as `getCurrentTime` moves it.

The ported modules are not changed.
-/
import Fl4Spec.Structures

namespace Fl4Spec

/-- The machine state after one reading of the clock: `getCurrentTime`'s
state change (`time_state + 1`, `last_machine_time` the value read). -/
def clockTickMs (ms : MachineState) : MachineState :=
  { ms with
    timeState := ms.timeState + 1,
    lastMachineTime := BitVec.ofNat 64 (min (unat (-(getCurrentTimeBuffer + 1)))
      (unat ms.lastMachineTime + timeOracle (ms.timeState + 1))) }

/-- **One clock reading as an environment step**: the hardware clock advanced
by one oracle reading (module docstring); nothing else changes. -/
def fl4ClockTick {Z : Type} (σ : State Z) : State Z :=
  { σ with machineState := clockTickMs σ.machineState }

end Fl4Spec
