#!/usr/bin/env python3
"""p3J gen 25: the SC-period frame family RQ (FK rpV) as a scripted copy of gen 21's heap-type family KQ
(P3JKtF / P3JKtG / P3JKtE, themselves copies of SpecInvDomF/G/E). Run from proofs/: python3 scratch/p3J/genRr.py
`set_object` does not keep `rpV` generically, so the generic leaf is replaced by `rq_setObject_nsc` (a written
object whose `a_type` is neither an SC's nor garbage) and hand proofs of `set_cap`, `set_simple_ko` and
`update_sched_context` (with a period-keeping update). Skip list: scratch/p3J/rr/skip.txt."""
import re
P = 'Fl4Proofs/P3/'
skip = {l.strip() for l in open('scratch/p3J/rr/skip.txt') if l.strip() and not l.startswith('#')}

def ren(t):
    t = re.sub(r'\bKQE\b', 'RQE', t)
    t = re.sub(r'\bKQ\b', 'RQ', t)
    t = re.sub(r'\bktV\b', 'rpV', t)
    t = re.sub(r'\bkqe_', 'rqe_', t)
    t = re.sub(r'\bkq_', 'rq_', t)
    t = re.sub(r'\brq_(leaf|auto0|auto|sf_unfold)\b', r'zq_\1', t)
    t = t.replace('namespace Fl4Proofs.P3.SInvKt\n', 'namespace Fl4Proofs.P3.SInvRr\n')
    t = t.replace('end Fl4Proofs.P3.SInvKt\n', 'end Fl4Proofs.P3.SInvRr\n')
    t = t.replace('import Fl4Proofs.P3.P3JKtF\n', 'import Fl4Proofs.P3.P3JRrF\n')
    t = t.replace('import Fl4Proofs.P3.P3JKtG\n', 'import Fl4Proofs.P3.P3JRrG\n')
    return t

def drop(t):
    lines = t.split('\n')
    out = []; i = 0
    while i < len(lines):
        m = re.match(r'theorem (\S+)', lines[i])
        if m and m.group(1) in skip:
            while out and (out[-1].startswith('set_option') and out[-1].endswith(' in')):
                out.pop()
            if out and out[-1].rstrip().endswith('-/'):
                j = len(out) - 1
                while not out[j].startswith('/--'):
                    j -= 1
                del out[j:]
            i += 1
            while i < len(lines) and not re.match(r'(theorem|macro_rules|/--|set_option|end|section|def|abbrev|macro|syntax|open|elab|instance|lemma)\b', lines[i]) and not lines[i].startswith('/-'):
                i += 1
            if i < len(lines) and lines[i].startswith('macro_rules') and m.group(1) in lines[i]:
                i += 1
            continue
        out.append(lines[i]); i += 1
    return '\n'.join(out)

HDR = {
 'P3JRrF': '''/-
P3 (line p3J, gen 25): **the SC-period frame** (spec side only; outside the `JAtZ` cone), a scripted copy of gen 21's
heap-type frame P3JKtF (`scratch/p3J/genRr.py`: `KQ` ↦ `RQ`, `ktV` ↦ `rpV`).

* `rpV σ o`: the period of the SC at `o` (`0` at every other object and at a free address). `RQ m := FK rpV m`.
* `set_object` checks only the `a_type`, so it does not keep `rpV` by itself. Leaves instead:
  `rq_setObject_nsc` (the new object's `a_type` is neither an SC's nor a garbage one: then neither is the old
  object's, both periods read `0`; every literal TCB / endpoint / notification / reply / arch-object write),
  `rq_setCap` (the CNode / TCB slot write), `rq_setSimpleKo'` (endpoint / notification / reply),
  `rq_updateSchedContext'` (an SC update `f` with `(f sc).scPeriod = sc.scPeriod`: every SC update of the spec but
  `refill_new` / `refill_update`'s `sc_period_update`, reached only from `SchedControl_Configure`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
''',
 'P3JRrG': '''/-
P3 (line p3J, gen 25): **`RQ` leaves of the spec functions** (P3JRrF's SC-period frame), a scripted copy of gen 21's
P3JKtG (`scratch/p3J/genRr.py`), without the heap writers `retype_region` / `delete_objects` and their callers and
without the period writers `refill_new` / `refill_update` and their caller `invoke_sched_control_configure_flags`
(`scratch/p3J/rr/skip.txt`); `set_cap` / `set_simple_ko` / `update_sched_context` are P3JRrF's hand leaves.

Named premises: none. No sorry. New module; no existing statement changed.
-/
''',
 'P3JRrE': '''/-
P3 (line p3J, gen 25): **the SC-period frame of the kernel entry's pieces** (P3JRrF's `RQ` over P3JRrG's leaves), a
scripted copy of gen 21's P3JKtE (`scratch/p3J/genRr.py`). Every non-syscall event's `handle_event` keeps `rpV`
(`rqe_handleEvent_other`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
''',
}
SRC = {'P3JRrF': 'P3JKtF', 'P3JRrG': 'P3JKtG', 'P3JRrE': 'P3JKtE'}

DEF_OLD = '''/-- The type of every heap object (UtRetResetJ's `khT`). -/
def rpV (σ : State Unit) : ObjRef → Option AType := fun o => (σ.kheap o).map aType
'''
DEF_NEW = '''/-- The period of an SC object (`0` for every other object). -/
def pv1 (k : KernelObject) : Ticks :=
  match k with
  | .schedContext sc _ => sc.scPeriod
  | _ => 0

/-- The period of the SC at every address (`0` where there is no SC). -/
def rpV (σ : State Unit) : ObjRef → Ticks := fun o =>
  match σ.kheap o with
  | some k => pv1 k
  | none => 0
'''
SETOBJ_RE = re.compile(r'theorem rq_setObject \(p : ObjRef\).*?macro_rules \| `\(tactic\| zq_leaf\) => `\(tactic\| with_reducible exact rq_setObject _ _\)\n', re.S)
SETOBJ_NEW = open('scratch/p3J/rr/leaves.lean').read()

for out, src in SRC.items():
    t = open(P + src + '.lean').read()
    t = re.sub(r'\A/-.*?-/\n', '', t, count=1, flags=re.S)
    t = ren(t)
    if out == 'P3JRrF':
        assert DEF_OLD in t, 'def'
        t = t.replace(DEF_OLD, DEF_NEW)
        t2 = SETOBJ_RE.sub(lambda m: SETOBJ_NEW, t, count=1)
        assert t2 != t, 'setObject'
        t = t2
        t = t.replace('Every outcome of `m` keeps the type of every heap object.', 'Every outcome of `m` keeps the period of every SC.')
    if out != "P3JRrF":
        t = drop(t)
    open(P + out + '.lean', 'w').write(HDR[out] + t)
    print(out, len(t.split('\n')))
