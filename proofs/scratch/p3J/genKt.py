#!/usr/bin/env python3
"""p3J gen 21: the heap-type frame family KQ (FK ktV) as a scripted copy of the domain-list family DL
(SpecInvDomF / SpecInvDomG / SpecInvDomE). Run from proofs/: python3 scratch/p3J/genKt.py
Skip list: scratch/p3J/kt/skip.txt (theorem names in the *output*, one per line): those theorems and their
macro_rules line are dropped (the heap writers retype / detype and their callers)."""
import re, os
P = 'Fl4Proofs/P3/'
skip = set()
if os.path.exists('scratch/p3J/kt/skip.txt'):
    skip = {l.strip() for l in open('scratch/p3J/kt/skip.txt') if l.strip() and not l.startswith('#')}

def ren(t):
    t = re.sub(r'\bDLE\b', 'KQE', t)
    t = re.sub(r'\bDL\b', 'KQ', t)
    t = re.sub(r'\bdlV\b', 'ktV', t)
    t = re.sub(r'\bdle_', 'kqe_', t)
    t = re.sub(r'\bdl_', 'kq_', t)
    t = re.sub(r"\bsf_unfold\b", "kq_sf_unfold", t)
    t = t.replace('namespace Fl4Proofs.P3.SInvDom\n', 'namespace Fl4Proofs.P3.SInvKt\n')
    t = t.replace('end Fl4Proofs.P3.SInvDom\n', 'end Fl4Proofs.P3.SInvKt\n')
    t = t.replace('import Fl4Proofs.P3.SpecInvDomF\n', 'import Fl4Proofs.P3.P3JKtF\n')
    t = t.replace('import Fl4Proofs.P3.SpecInvDomG\n', 'import Fl4Proofs.P3.P3JKtG\n')
    return t

def drop(t):
    # split into blocks at top-level theorem starts (with preceding docstring / set_option lines)
    lines = t.split('\n')
    out = []; i = 0
    while i < len(lines):
        m = re.match(r'theorem (\S+)', lines[i])
        if m and m.group(1) in skip:
            # remove preceding doc comment / set_option lines already emitted
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
 'P3JKtF': '''/-
P3 (line p3J, gen 21): **the heap-type frame** (spec side only; outside the `JAtZ` cone), a scripted copy of
SpecInvDomF (`scratch/p3J/genKt.py`: `DL` ↦ `KQ`, `dlV` ↦ `ktV`).

* `ktV σ := fun o => (σ.kheap o).map aType`: the type of every heap object (UtRetResetJ's `khT`). `KQ m := FK ktV m`.
* `set_object` asserts that the new object has the old one's `a_type` (`kq_setObject`), so every spec function that
  writes the heap only through `set_object` keeps `ktV`; the only other heap writers are `retype_region` and
  `detype` (`delete_objects`), reached only from untyped invocations (P3JKtG leaves them out).

Named premises: none. No sorry. New module; no existing statement changed.
-/
''',
 'P3JKtG': '''/-
P3 (line p3J, gen 21): **`KQ` leaves of the spec functions** (P3JKtF's heap-type frame), a scripted copy of
SpecInvDomG (`scratch/p3J/genKt.py`), without the heap writers `retype_region` / `delete_objects` and their
callers (the untyped invocation and reset; `scratch/p3J/kt/skip.txt`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
''',
 'P3JKtE': '''/-
P3 (line p3J, gen 21): **the heap-type frame of the kernel entry's pieces** (P3JKtF's `KQ` over P3JKtG's leaves),
a scripted copy of SpecInvDomE (`scratch/p3J/genKt.py`); the domain writers (`next_domain`, ...) need no exception
here (they write no heap). Every non-syscall event's `handle_event` keeps `ktV` (`kqe_handleEvent_other`).

Named premises: none. No sorry. New module; no existing statement changed.
-/
''',
}
SRC = {'P3JKtF': 'SpecInvDomF', 'P3JKtG': 'SpecInvDomG', 'P3JKtE': 'SpecInvDomE'}

SETOBJ_OLD = '''theorem kq_setObject (p : ObjRef) (o : KernelObject) : KQ (setObject (Z := Unit) p o) := by
  unfold setObject; dk_auto0'''
SETOBJ_NEW = '''theorem kq_setObject (p : ObjRef) (o : KernelObject) : KQ (setObject (Z := Unit) p o) := by
  intro σ x ⟨y, hy, hx⟩
  obtain ⟨k, hk⟩ : ∃ k, σ.kheap p = some k ∧ y = (k, σ) := by
    unfold getObject NonDet.getsThe readObject at hy
    cases h : σ.kheap p with
    | none => rw [h] at hy; exact hy.elim
    | some k => rw [h] at hy; exact ⟨k, rfl, Set.mem_singleton_iff.1 hy⟩
  obtain ⟨hk, rfl⟩ := hk
  obtain ⟨z, hz, hx⟩ := hx
  obtain ⟨hty, rfl⟩ := hz
  obtain ⟨w, hw, hx⟩ := hx
  rw [Set.mem_singleton_iff.1 hw] at hx
  rw [Set.mem_singleton_iff.1 hx]
  funext o'
  unfold ktV
  by_cases e : o' = p
  · subst e; simp only [Function.update_self, hk, Option.map_some]; exact congrArg some hty.symm
  · simp only [Function.update_of_ne e]'''
DEF_OLD_RE = re.compile(r'/-- The fields `DomListOK` reads. -/\ndef ktV.*?\n\n', re.S)
DEF_NEW = '''/-- The type of every heap object (UtRetResetJ's `khT`). -/
def ktV (σ : State Unit) : ObjRef → Option AType := fun o => (σ.kheap o).map aType

'''
for out, src in SRC.items():
    t = open(P + src + '.lean').read()
    t = re.sub(r'\A/-.*?-/\n', '', t, count=1, flags=re.S)
    t = ren(t)
    if out == 'P3JKtF':
        t2 = DEF_OLD_RE.sub(DEF_NEW, t, count=1)
        assert t2 != t, 'ktV def'
        t = t2
        assert SETOBJ_OLD in t, 'setObject'
        t = t.replace(SETOBJ_OLD, SETOBJ_NEW)
        t = t.replace('Every outcome of `m` keeps the domain list, its start and its index.', 'Every outcome of `m` keeps the type of every heap object.')
    t = drop(t)
    open(P + out + '.lean', 'w').write(HDR[out] + t)
    print(out, len(t.split('\n')))
