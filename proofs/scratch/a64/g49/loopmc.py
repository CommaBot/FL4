#!/usr/bin/env python3
"""Gen 49: the scripted in-place QueueZombieQ edit (kept for review).

LoopMC (obligations see a context predicate C, the loops' own JV; swap also sees the Zombie in its second slot);
the four loop proofs move from zqGM / zqGTM / zqIGTM into new ...C declarations taking LoopMC at C := JV s0;
the old declarations keep their statements byte-identical and become `hM.toC _` instances.
usage: loopmc.py <QueueZombieQ.lean>
"""
import re, sys
p = sys.argv[1]
t = open(p).read()

def once(old, new):
    global t
    assert t.count(old) == 1, old[:80]
    t = t.replace(old, new)

JV = 'JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0'

# 1. the structure, after LoopM.and
once('''theorem FinK.toT {kb : U64}''', '''/-- **A loop-invariant field with context** (gen 49): `LoopM`'s obligations, each also given `C s` (the loops
instantiate `C` with their own `JV` at `s0`, which carries `ks` base and the slot typing), `swap` also given the
`Zombie` its second slot holds (cdt.rs:257–262: `slot` was just rewritten to the `Zombie`). `LoopM.toC`: every
`LoopM` field is one. -/
structure LoopMC (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (OS D : Set U64)
    (C M : S → Prop) : Prop where
  fin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool), C s → M s → x ∈ OS →
    obj.Slot.cap st x s = ok c → objects.finalise_cap st ar s a c f false ⦃ r => M r.2.1 ⦄
  setz : ∀ (s : S) (x p t n : U64), C s → M s → x ∈ OS → obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => M s' ⦄
  swap : ∀ (s : S) (p y : U64), C s → M s → p ∈ D → y ∈ D → p ≠ y →
    (∃ p' t n, obj.Slot.cap st y s = ok (.Zombie p' t n)) → cdt.cap_swap_for_delete st s p y ⦃ s' => M s' ⦄
  pre : ∀ (s : S) (a : A), C s → M s → sched.preemption_point st ar s a ⦃ r => M r.2.1 ⦄
  emp : ∀ (s : S) (a : A) (x : U64) (cl : capability.Cap), C s → M s → x ∈ OS → ClOK cl →
    cdt.empty_slot st ar s a x cl ⦃ r => M r.1 ⦄

/-- A context-free field is a field with any context. -/
theorem LoopM.toC {M : S → Prop} (h : LoopM st ar OS D M) (C : S → Prop) : LoopMC st ar OS D C M where
  fin s a x c f _ m hx hc := h.fin s a x c f m hx hc
  setz s x p t n _ m hx := h.setz s x p t n m hx
  swap s p y _ m hp hy hne _ := h.swap s p y m hp hy hne
  pre s a _ m := h.pre s a m
  emp s a x cl _ m hx hc := h.emp s a x cl m hx hc

theorem FinK.toT {kb : U64}''')

# 2. obligation sites (inside the moved proofs)
once('(hM.fin s1 a1 y c fin m1 (hDO hy) hc)', '(hM.fin s1 a1 y c fin h1 m1 (hDO hy) hc)')
once('(hM.setz s2 y p t n m2 (hDO hy))', '(hM.setz s2 y p t n h2 m2 (hDO hy))')
once('(hM.swap s3 p y m3 hp0 hy hpy)', '(hM.swap s3 p y h3 m3 hp0 hy hpy ⟨p, _, n, c3⟩)')
once('(hM.pre s4 _ m4)', '(hM.pre s4 _ h4 m4)')
once('(hM.emp s1 a1 y _ m1 (hDO hy) (hv1 v rfl))', '(hM.emp s1 a1 y _ h1 m1 (hDO hy) (hv1 v rfl))')
once('(hM.pre s5 _ m5)', '(hM.pre s5 _ h5 m5)')
once('(hM.fin s1 a1 x c fin m1 hx hc)', '(hM.fin s1 a1 x c fin h1 m1 hx hc)')
once('(hM.setz s2 x p t n m2 hx)', '(hM.setz s2 x p t n h2 m2 hx)')
once('(hM.setz s4 x _ _ _ m4 hx)', '(hM.setz s4 x _ _ _ h4 m4 hx)')
once('(hM.emp s1 a1 x _ m1 hx (hv1 v rfl))', '(hM.emp s1 a1 x _ h1 m1 hx (hv1 v rfl))')
# internal calls go to the C versions
once('refine WP.spec_bind (cdt.finalise_slot_deferred.zqGM (a := a)', 'refine WP.spec_bind (cdt.finalise_slot_deferred.zqGMC (a := a)')
once('refine WP.spec_bind (cdt.delete_deferred.zqGM (a := a2)', 'refine WP.spec_bind (cdt.delete_deferred.zqGMC (a := a2)')
once('refine WP.spec_bind (cdt.finalise_slot_immediate.zqGTM (a := a)', 'refine WP.spec_bind (cdt.finalise_slot_immediate.zqGTMC (a := a)')

# 3. each moved theorem: header renamed to ...C with LoopMC; the original header re-added as an instance
inst = {
 'cdt.finalise_slot_deferred.zqGM': 'hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs hN hY',
 'cdt.delete_deferred.zqGM': 'hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY',
 'cdt.finalise_slot_immediate.zqGTM': 'hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY',
 'cdt.delete.zqIGTM': 'hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY',
}
for name, args in inst.items():
    m = re.search(r'(set_option maxHeartbeats 4000000 in\n/--(?:(?!-/)[\s\S])*?-/\n)theorem ' + re.escape(name) + r' ([\s\S]*?) := by\n', t)
    assert m, name
    doc = m.group(1)
    sig = m.group(2)
    assert '(hM : LoopM st ar OS D M)' in sig
    hdr_old = 'theorem ' + name + ' ' + sig + ' :='
    sigC = sig.replace('(hM : LoopM st ar OS D M)', '(hM : LoopMC st ar OS D (' + JV + ') M)')
    docC = doc.replace('with a loop-invariant field `M`** (gen 48, `LoopM`)', 'with a context field `M`** (gen 49, `LoopMC` at `C := JV s0`)')
    assert docC != doc
    newC = docC + 'theorem ' + name + 'C ' + sigC + ' := by\n'
    t = t[:m.start()] + newC + t[m.end():]
    # end of the moved proof: the next blank line followed by set_option / doc / theorem
    start = m.start() + len(newC)
    end = t.index('\n\n', start)
    inst_txt = ('\n\n' + doc + hdr_old + '\n  ' + name + 'C (a := a) ' + args + ' (hM.toC _) hm')
    t = t[:end] + inst_txt + t[end:]

# 4. docstring
once('''their obligations are listed in the a64 handoff (gen 48).
-/''', '''their obligations are listed in the a64 handoff (gen 48).

**Gen 49: the field with context.** `LoopMC st ar OS D C M`: `LoopM`'s obligations each also given `C s` (and `swap`
the `Zombie` in its second slot); the loop proofs moved (not copied) into **`cdt.finalise_slot_deferred.zqGMC`**,
**`cdt.delete_deferred.zqGMC`**, **`cdt.finalise_slot_immediate.zqGTMC`**, **`cdt.delete.zqIGTMC`** at
`C := JV s0`; gen 48's `zqGM` / `zqGTM` / `zqIGTM` are their `LoopM.toC` instances, statements unchanged
(script-checked). The MDB obligations need `JV` (`pre`: `OSKeep`; `emp`: `ks` base), hence the context.
-/''')
open(p, 'w').write(t)
