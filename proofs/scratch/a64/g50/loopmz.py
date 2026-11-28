#!/usr/bin/env python3
"""Gen 50: the scripted in-place QueueZombieQ edit (kept for review).

LoopMZ (LoopMC whose `fin` also sees the loop's facts on the finalised cap, `X`, and the finality `is_final` computed
just before, and returns a predicate `Zr` on the slot for a `Zombie` remainder; `setz` sees `Canon p` and `Zr`;
`zz`: a slot holding a `Zombie` satisfies `Zr`); the four loop proofs move from zqGMC / zqGTMC / zqIGTMC into new
...MZ declarations; the ...MC declarations keep their statements byte-identical and become `hM.toZ _` instances.
usage: loopmz.py <QueueZombieQ.lean>
"""
import re, sys
p = sys.argv[1]
t = open(p).read()

def once(old, new, n=1):
    global t
    assert t.count(old) == n, (t.count(old), old[:80])
    t = t.replace(old, new)

JV = 'JV st T Cs Ω H Sg Rp Scs Nt Z Ac OS Vc Ub s0'

# 1. the structure, after LoopM.toC
once('''theorem FinK.toT {kb : U64}''', '''/-- **The loop's facts on the cap it finalises** (gen 50; `LoopMZ`'s `X` in the loops below): a `ZQ` cap at the
round's idle word and idle `SC` field, `Ty` and `IrqN` at the round's state. -/
abbrev XQF (st : machine.Store S) [L : LawfulStore st] (K : capability.Cap → Prop) (Vc D Scs Fp : Set U64)
    (Ty : S → Prop) (kb : U64) (s : S) (x : U64) (c : capability.Cap) : Prop :=
  ZQ K Vc D Scs Fp (L.idleW s) (L.mem s (scA (L.idleW s))) x c ∧ Ty s ∧ IrqN st kb s

/-- **A loop-invariant field with the finalisation's facts** (gen 50): `LoopMC`'s obligations, `fin` also given the
loop's facts `X s x c` on the cap and the finality just computed (cdt.rs: `is_final_capability_with_cap` before
`finalise_cap`), and returning, for a `Zombie p t _` remainder, `Zr` of the slot at the end state; `setz` (the
`Zombie` write right after, or the shrunk `Zombie` of the immediate loop) given `Canon p` and `Zr`; `zz`: a slot
holding `Zombie p t _` satisfies `Zr` (the immediate loop's second write, cdt.rs: only when the slot still holds the
same `Zombie`). `LoopMC.toZ`: every `LoopMC` field is one (`Zr := True`). -/
structure LoopMZ (st : machine.Store S) [L : LawfulStore st] (ar : machine.Arch A) (OS D : Set U64)
    (C : S → Prop) (X : S → U64 → capability.Cap → Prop) (Zr : S → U64 → U64 → U64 → Prop) (M : S → Prop) :
    Prop where
  fin : ∀ (s : S) (a : A) (x : U64) (c : capability.Cap) (f : Bool), C s → M s → x ∈ OS →
    obj.Slot.cap st x s = ok c → X s x c → cdt.is_final_capability_with_cap st s x c = ok f →
    objects.finalise_cap st ar s a c f false ⦃ r => M r.2.1 ∧ ∀ p t n, r.1.1 = .Zombie p t n → Zr r.2.1 x p t ⦄
  zz : ∀ (s : S) (x p t n : U64), obj.Slot.cap st x s = ok (.Zombie p t n) → Zr s x p t
  setz : ∀ (s : S) (x p t n : U64), C s → M s → x ∈ OS → Canon p → Zr s x p t →
    obj.Slot.set_cap st x s (.Zombie p t n) ⦃ s' => M s' ⦄
  swap : ∀ (s : S) (p y : U64), C s → M s → p ∈ D → y ∈ D → p ≠ y →
    (∃ p' t n, obj.Slot.cap st y s = ok (.Zombie p' t n)) → cdt.cap_swap_for_delete st s p y ⦃ s' => M s' ⦄
  pre : ∀ (s : S) (a : A), C s → M s → sched.preemption_point st ar s a ⦃ r => M r.2.1 ⦄
  emp : ∀ (s : S) (a : A) (x : U64) (cl : capability.Cap), C s → M s → x ∈ OS → ClOK cl →
    cdt.empty_slot st ar s a x cl ⦃ r => M r.1 ⦄

/-- A `LoopMC` field is a `LoopMZ` field with any `X` and `Zr := True`. -/
theorem LoopMC.toZ {C M : S → Prop} (h : LoopMC st ar OS D C M) (X : S → U64 → capability.Cap → Prop) :
    LoopMZ st ar OS D C X (fun _ _ _ _ => True) M where
  fin s a x c f hC m hx hc _ _ := WP.spec_mono (h.fin s a x c f hC m hx hc) fun _ m' => ⟨m', fun _ _ _ _ => trivial⟩
  zz _ _ _ _ _ _ := trivial
  setz s x p t n hC m hx _ _ := h.setz s x p t n hC m hx
  swap s p y hC m hp hy hne hz := h.swap s p y hC m hp hy hne hz
  pre s a hC m := h.pre s a hC m
  emp s a x cl hC m hx hc := h.emp s a x cl hC m hx hc

theorem FinK.toT {kb : U64}''')

# 2. obligation sites (inside the moved proofs)
once('refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS) fun fin _ => ?_',
     'refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s1 y c hS)) fun fin hfe => ?_')
once('(hM.fin s1 a1 y c fin h1 m1 (hDO hy) hc)',
     '(hM.fin s1 a1 y c fin h1 m1 (hDO hy) hc ⟨(by rw [i1, j1]; exact d1 y hy c hc), y1, hN1⟩ hfe.1)')
once('rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2, sc2, v2⟩, m2⟩\n    simp only at hcl hrem j2 sc2 v2 m2',
     'rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2, sc2, v2⟩, m2, z2⟩\n    simp only at hcl hrem j2 sc2 v2 m2 z2')
once('(hM.setz s2 y p t n h2 m2 (hDO hy))', '(hM.setz s2 y p t n h2 m2 (hDO hy) hcp (z2 p t n rfl))')
once('refine WP.spec_bind (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS) fun fin _ => ?_',
     'refine WP.spec_bind (spec_eqv (P0.cdt.is_final_capability_with_cap.p0 st s1 x c hS)) fun fin hfe => ?_')
once('(hM.fin s1 a1 x c fin h1 m1 hx hc)',
     '(hM.fin s1 a1 x c fin h1 m1 hx hc ⟨(by rw [j1, js1]; exact x1 c hc), y1, N1⟩ hfe.1)')
once("rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2', sc2, v2⟩, m2⟩\n    simp only at hcl hrem j2' sc2 v2 m2",
     "rintro ⟨⟨rem, cl⟩, s2, a2⟩ ⟨⟨hcl, h2, k2, hrem, j2', sc2, v2⟩, m2, z2⟩\n    simp only at hcl hrem j2' sc2 v2 m2 z2")
once('(hM.setz s2 x p t n h2 m2 hx)', '(hM.setz s2 x p t n h2 m2 hx hcp (z2 p t n rfl))')
once('(hM.setz s4 x _ _ _ h4 m4 hx)',
     '(hM.setz s4 x p _ _ h4 m4 hx hcp (hM.zz s4 x p _ _ (by subst_vars; exact hc4)))')
# internal calls go to the Z versions
once('refine WP.spec_bind (cdt.finalise_slot_deferred.zqGMC (a := a)', 'refine WP.spec_bind (cdt.finalise_slot_deferred.zqGMZ (a := a)')
once('refine WP.spec_bind (cdt.delete_deferred.zqGMC (a := a2)', 'refine WP.spec_bind (cdt.delete_deferred.zqGMZ (a := a2)')
once('refine WP.spec_bind (cdt.finalise_slot_immediate.zqGTMC (a := a)', 'refine WP.spec_bind (cdt.finalise_slot_immediate.zqGTMZ (a := a)')

# 3. each moved theorem: header renamed to ...Z with LoopMZ; the original header re-added as an instance
inst = {
 'cdt.finalise_slot_deferred.zqGMC': 'hP hO hA hV hDO hDC hR hK hTy hW hIO h hy hD hI hIs hN hY',
 'cdt.delete_deferred.zqGMC': 'hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hy hD hI hIs hN hY',
 'cdt.finalise_slot_immediate.zqGTMC': 'hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY',
 'cdt.delete.zqIGTMC': 'hP hO hA hV hDO hDC hR hK hTy hW hIO hap h hx hxI hD hX hI hIs hN hY',
}
oldH = '{M : S → Prop} (hM : LoopMC st ar OS D (' + JV + ') M)'
newH = ('{M : S → Prop} {Zr : S → U64 → U64 → U64 → Prop}\n    (hM : LoopMZ st ar OS D (' + JV +
        ') (XQF st K Vc D Scs Fp Ty (L.ksb s0)) Zr M)')
for name, args in inst.items():
    m = re.search(r'(set_option maxHeartbeats 4000000 in\n/--(?:(?!-/)[\s\S])*?-/\n)theorem ' + re.escape(name) + r' ([\s\S]*?) := by\n', t)
    assert m, name
    doc = m.group(1)
    sig = m.group(2)
    assert oldH in sig, name
    hdr_old = 'theorem ' + name + ' ' + sig + ' :='
    sigZ = sig.replace(oldH, newH)
    docZ = doc.replace('with a context field `M`** (gen 49, `LoopMC` at `C := JV s0`)',
                       'with a field `M` seeing the finalisation** (gen 50, `LoopMZ` at `C := JV s0`, `X := XQF`)')
    assert docZ != doc
    nameZ = name[:-1] + 'Z'
    newZ = docZ + 'theorem ' + nameZ + ' ' + sigZ + ' := by\n'
    t = t[:m.start()] + newZ + t[m.end():]
    start = m.start() + len(newZ)
    end = t.index('\n\n', start)
    inst_txt = ('\n\n' + doc + hdr_old + '\n  ' + nameZ + ' (a := a) ' + args + ' (hM.toZ _) hm')
    t = t[:end] + inst_txt + t[end:]

# 4. docstring
once('''(script-checked). The MDB obligations need `JV` (`pre`: `OSKeep`; `emp`: `ks` base), hence the context.
-/''', '''(script-checked). The MDB obligations need `JV` (`pre`: `OSKeep`; `emp`: `ks` base), hence the context.

**Gen 50: the field seeing the finalisation.** `LoopMZ st ar OS D C X Zr M`: `LoopMC`'s obligations, `fin` also given
the loop's facts on the finalised cap (`X`, here `XQF`: `ZQ`, `Ty`, `IrqN` at the round's state) and the finality the
loop computed just before (`is_final_capability_with_cap … = ok f`), returning `Zr` of the slot for a `Zombie`
remainder; `setz` given `Canon p` and `Zr`; `zz` (a `Zombie` already in the slot gives `Zr`). The loop proofs moved
(not copied) into **`cdt.finalise_slot_deferred.zqGMZ`**, **`cdt.delete_deferred.zqGMZ`**,
**`cdt.finalise_slot_immediate.zqGTMZ`**, **`cdt.delete.zqIGTMZ`**; gen 49's `zqGMC` / `zqGTMC` / `zqIGTMC` are
their `LoopMC.toZ` instances, statements unchanged (script-checked, `scratch/a64/g50/loopmz.py`). The MDB field's
`fin` / `setz` need exactly this (MdbFin): the finaliser class to know which caps change `OS` words, the finality to
rule out a second cap of the object being turned into a `Zombie`.
-/''')
open(p, 'w').write(t)
