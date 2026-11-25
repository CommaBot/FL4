# stpost gen 3: the body of `handle_invocation_refinesMXPF` (StPostInv.lean) from XTopJointEntry's
# `handle_invocation_refinesMXP`, the lookup fixed by `hls`. Prints the lemma to stdout.
import sys
P = sys.argv[1]
src = open(P + '/XTopJointEntry.lean').read().split('\n')
i = next(k for k, l in enumerate(src) if l.startswith('theorem handle_invocation_refinesMXP '))
j = next(k for k in range(i, len(src)) if src[k] == 'end')
L = src[i:j]
while L[-1].strip() == '':
    L.pop()
t = '\n'.join(L)
def rep(a, b):
    global t
    assert t.count(a) == 1, a
    t = t.replace(a, b)
rep('theorem handle_invocation_refinesMXP ', 'theorem handle_invocation_refinesMXPF ')
rep('(is_call blocking can_donate first_phase : Bool) (cptr : U64)\n',
    '(is_call blocking can_donate first_phase : Bool) (cptr : U64)\n'
    '    (found : cspace.Resolved) (hls : cspace.lookup_slot st s ct cptr = ok (.Ok found))\n')
a = t.index('    -- the fault of a failed lookup\n')
b = t.index('    -- the success tail')
t = t[:a] + t[b:]
rep("(exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ th p = some (.cnode sl.2.length)) →\n",
    "(exs : List (Fl4Spec.Cap × Fl4Spec.CslotPtr)), (∃ p, sl.1 = p.bv ∧ th p = some (.cnode sl.2.length)) →\n"
    "      found.slot = cslotAddr sl →\n")
a = t.index('  refine WP.spec_bind (lookup_slot_refines')
b = t.index('    | ok v =>\n')
t = t[:a] + '''  have hLR := lookup_slot_refines (Z := Unit) th s σ hCR.1 hCR.2.1 ct htcb cptr
  rw [hls, WP.spec_ok] at hLR
  obtain ⟨e, he, hrel, hok⟩ := hLR
  rw [hls]; simp only [bind_ok]
  cases e with
    | error lf' => exact hrel.elim
''' + t[b:]
rep('      simp only\n      rw [slot_cap_eq, hsl, hc]', '      try simp only\n      rw [slot_cap_eq, hsl, hc]')
rep('hDec sl c ex exs ⟨p, hp, hth⟩ hc hget rfl rfl', 'hDec sl c ex exs ⟨p, hp, hth⟩ hsl hc hget rfl rfl')
print(t)
