# p3J gen 24: NoSig family, scripted copy of irqfix's GKB family (SpecInvIrqBoundKit / Gen / Bound) without sisB.
import re
P='Fl4Proofs/P3/'
def ren(s):
    s=s.replace('GKB','GKN').replace('gkb','gkn').replace('WLB','WLN').replace('wlb','wln')
    s=s.replace('namespace Fl4Proofs.P3.SInvIB','namespace Fl4Proofs.P3.SInvNs').replace('end Fl4Proofs.P3.SInvIB','end Fl4Proofs.P3.SInvNs')
    return s
def cut(s,a,b):
    i=s.index(a); j=s.index(b,i); return s[:i]+s[j:]
# ---- Kit
k=open(P+'SpecInvIrqBoundKit.lean').read()
body=k[k.index('import'):]
body=cut(body,'/-! ## The invariants -/','/-! ## The leaves -/')
body=body.replace('  sisB : ∀ st i, i ≤ maxIRQ → IK P (setIrqState (Z := Unit) st i)\n','')
body=cut(body,'theorem gkb_setIrqState_le','theorem gkb_ack')
body=body.replace('  | ((with_reducible refine gkb_setIrqState_le _ _ ?_); assumption)\n','')
i=body.index('/-! ## `IrqStB` has the leaves -/'); j=body.index('end\n\nend Fl4Proofs.P3.SInvIB')
ns='''/-! ## No signal line -/

/-- **No IRQ line is `IRQSignal`** (module docstring). -/
def NoSig (σ : State Unit) : Prop := ∀ irq : Irq, σ.interruptStates irq ≠ .irqSignal

theorem ik_dmo_noSig {α : Type} (mop : NonDet MachineState α) : IK NoSig (doMachineOp (Z := Unit) mop) := by
  intro σ h x hx
  unfold doMachineOp at hx
  obtain ⟨⟨ms0, s1⟩, h1, ⟨⟨r, ms'⟩, s2⟩, h2, ⟨u, s3⟩, h3, hx⟩ := hx
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h1)
  obtain ⟨-, e2⟩ := h2
  dsimp only at e2
  subst e2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.1 h3)
  rw [Set.mem_singleton_iff.1 hx]
  exact h

theorem ik_sis_noSig (i : Irq) : IK NoSig (setIrqState (Z := Unit) .irqInactive i) := by
  intro σ h x hx
  unfold setIrqState at hx
  obtain ⟨y, hy, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hy] at hx
  refine ik_dmo_noSig _ _ ?_ x hx
  intro irq
  show Function.update σ.interruptStates i .irqInactive irq ≠ .irqSignal
  by_cases e : irq = i
  · subst e
    rw [Function.update_self]
    exact fun h' => by cases h'
  · rw [Function.update_of_ne e]; exact h irq

/-- **`NoSig` has the leaves** (`set_irq_state` of `IRQInactive` only). -/
theorem wln_noSig : WLN NoSig where
  view σ σ' e h := by
    unfold vw at e; simp only [Prod.mk.injEq] at e
    intro irq; rw [e.2.2.1]; exact h irq
  uts σ h x hx := by
    obtain ⟨-, -, e, -⟩ := uts_out hx
    intro irq; rw [e]; exact h irq
  sisI i := ik_sis_noSig i
  msk mop _ := ik_dmo_noSig mop
  ack i := ik_dmo_noSig _

'''
body=body[:i]+ns+body[j:]
hdr='''/-
P3 (p3J gen 24): **the "no signal line" invariant's kit** (spec side only; outside the `JAtZ` cone), a scripted
copy of irqfix's SpecInvIrqBoundKit (`scratch/p3J/genNs.py`: `GKB` ↦ `GKN`, `WLB` ↦ `WLN`) **without** the
bounded `set_irq_state` leaf `sisB`: `WLN P` asks `set_irq_state` only of `IRQInactive`.

* **`NoSig σ`**: no IRQ line is `IRQSignal`. Only `set_irq_state` writes the IRQ states, and only the IRQ-control
  issues (`invoke_irq_control`, `arch_invoke_irq_control`, FL4's remapped IOAPIC issue) write `IRQSignal`; every
  other writer (`deleting_irq_handler`) writes `IRQInactive`. **`wln_noSig`**: `NoSig` has the leaves.
* `GKN m := ∀ P, WLN P → IK P m` and its combinators / leaves (the Kit's, renamed).

No premise; no sorry. New module; no existing statement changed.
-/
'''
open(P+'P3JNsKit.lean','w').write(hdr+ren(body))
# ---- Gen
g=open(P+'SpecInvIrqBoundGen.lean').read()
body=g[g.index('import'):]
body=body.replace('import Fl4Proofs.P3.SpecInvIrqBoundKit','import Fl4Proofs.P3.P3JNsKit\nimport Fl4Proofs.P3.P3JCkS')
body=cut(body,'/-- The arch IRQ control issue','set_option maxRecDepth')
body=cut(body,'theorem gkb_archInvokeIrqControl','theorem gkb_archInvokeIrqHandler')
body=cut(body,'theorem gkb_invokeIrqControl','theorem gkb_setFlags')
i=body.index('/-- **The perform keeps every `GKB` predicate'); j=body.index('theorem gkb_fl4ReplyFromKernelError')
perf='''/-- **The perform keeps every `GKN` predicate when the decode's carry `InvK` holds** (P3JCkS: from a `CKI`
state the decode returns no untyped, SchedControl, IRQ-control or arch invocation). -/
theorem gkb_fl4PerformInvocation (x0 : Bool) (x1 : Bool) (x2 : Bool) (x3 : Fl4Invocation) (hb : SInvCk.InvK x3) :
    GKBE (fl4PerformInvocation (Z := Unit) x0 x1 x2 x3) := by
  cases x3 with
  | invokeUntyped _ => exact hb.elim
  | invokeSchedControl _ => exact hb.elim
  | invokeIRQControl _ => exact hb.elim
  | invokeArchObject _ => exact hb.elim
  | _ => simp only [fl4PerformInvocation]; gkb_auto

'''
body=body[:i]+perf+body[j:]
hdr='''/-
P3 (p3J gen 24): **`GKN` for the spec functions of the kernel entry below the invocation shell**, a scripted copy
of irqfix's SpecInvIrqBoundGen (`scratch/p3J/genNs.py`: `GKB` ↦ `GKN`), without the IRQ-control issues (which
write `IRQSignal`); the perform takes P3JCkS's `InvK` (no IRQ-control invocation) in place of `InvB`.

No premise; no sorry. New module; no existing statement changed.
-/
'''
open(P+'P3JNsGen.lean','w').write(hdr+ren(body))
# ---- Sys (part of Bound: the syscalls above the shell, events)
b=open(P+'SpecInvIrqBound.lean').read()
i=b.index('theorem gkb_getCapReg'); j=b.index('theorem gkb_fl4HandleSyscall')
part1=b[i:j]
i2=b.index('theorem gkb_fl4SyscallFaultIP'); j2=b.index('/-- The syscall event of FL4')
part2=b[i2:j2]
i3=b.index('/-- The VM fault handler'); j3=b.index('theorem gkb_fl4HandleEvent (rep')
part3=b[i3:j3]
open('scratch/p3J/ns_sys_parts.lean','w').write(ren(part1+part2+part3))
