#!/usr/bin/env python3
"""p3J gen 52 (batch 1, faults): generalise the mid-state fault leaves over their post, in place.

For each listed theorem T (post `... JAtR ...` / `... JAt ...`): the existing proof moves to a new theorem `TQ`
whose post has `Pq` in place of `JAtR` / `JAt`, with `hPq` (every `JAtZR` resp. `JAtZ` at `Z.mv G V` with the
entry's `H`, `Cs` gives `Pq`) as its last explicit argument; T keeps its exact statement (header text
byte-identical up to `:=`) and is the one-line instance `TQ … (fun … J' => ⟨…, J', inferInstance⟩)`.
The exits of the moved bodies are then edited by hand (`hPq … J'` in place of the existential packaging).
Run once from proofs/: python3 scratch/p3J/g52/gen.py
"""
import re, sys
sys.path.insert(0, 'scratch/p3J/g46')
from gen import header_split, find_theorem, explicit_args

def hpq(kind):
    return ('{Pq : S → A → Fl4Spec.State Unit → Prop}\n'
            '    (hPq : ∀ (G : MdbGhost) (V : XVs) (Ac\' : Set U64) (Lst\' : U64 → List U64) (D\' : Set U64) (s\' : S)\n'
            '      (a\' : A) (σ\' : Fl4Spec.State Unit), ' + kind +
            ' (L := L) arI AR (Z.mv G V) H Cs Ac\' Lst\' D\' s\' a\' σ\' → Pq s\' a\' σ\')')

def concl_colon(header):
    # index of the depth-0 ':' ending the binders
    i = header.index(' ', len('theorem '))
    depth = 0
    while i < len(header):
        c = header[i]
        if c in '([{⟨⦃':
            depth += 1
        elif c in ')]}⟩⦄':
            depth -= 1
        elif c == ':' and depth == 0 and header[i + 1] != '=':
            return i
        i += 1
    raise ValueError

POSTS = [('JAtR (L := L) arI AR r.1 r.2 z.2', 'JAtZR'), ('JAt (L := L) arI AR r.1 r.2 z.2', 'JAtZ')]

def gen(path, names):
    text = open(path).read()
    for name in names:
        pre, th, end = find_theorem(text, name)
        block_pre = text[pre:th]
        decl = text[th:end]
        header, proof = header_split(decl)
        kind = None
        for p, k in POSTS:
            if p in header:
                kind = k; post = p
        assert kind, name
        args = explicit_args(header)
        qn = name + 'Q'
        h = header.replace('theorem ' + name + ' ', 'theorem ' + qn + ' ', 1)
        c = concl_colon(h)
        # binders end just before c (strip trailing whitespace)
        b = h[:c].rstrip()
        h = b + '\n    ' + hpq(kind) + ' :' + h[c + 1:]
        h = h.replace(post, 'Pq r.1 r.2 z.2')
        body = proof
        body = body.replace('JAtR (L := L) arI AR r.2.1 r.2.2 z.2', 'Pq r.2.1 r.2.2 z.2')
        body = body.replace('JAt (L := L) arI AR r.2.1 r.2.2 z.2', 'Pq r.2.1 r.2.2 z.2')
        hbs = [l for l in block_pre.split('\n') if l.startswith('set_option')]
        doc = block_pre[block_pre.index('/--'):] if '/--' in block_pre else ''
        newdoc = ('/-- (p3J gen 52) **`' + name + '` with its post as a parameter** (module docstring: `Pq` from every `'
                  + kind + '` at `Z.mv G V` with the entry\'s `H`, `Cs`; `' + name + '` is its instance at `'
                  + ('JAtR' if kind == 'JAtZR' else 'JAt') + '`). -/\n')
        q = ('\n'.join(hbs) + '\n' if hbs else '') + newdoc + h + body
        q = q.rstrip('\n') + '\n\n'
        call = '\n  JAtZ.' + qn.split('.', 1)[1] + ' ' + ' '.join(args) + \
            ' (fun _ _ _ _ _ _ _ _ J\' => ⟨_, _, _, _, _, _, J\', inferInstance⟩)\n\n' if name.startswith('JAtZ.') else None
        assert call
        orig = block_pre + header + call
        text = text[:pre] + q + orig + text[end:].lstrip('\n')
    open(path, 'w').write(text)

F = 'Fl4Proofs/P3/'
gen(F + 'XTopJointFaultM.lean', ['JAtZ.noFaultJM', 'JAtZ.faultBlockJM', 'JAtZ.faultHypJZM'])
gen(F + 'XTopJointFaultC.lean', ['JAtZ.noFaultJC', 'JAtZ.faultBlockJC', 'JAtZ.faultHypJZC'])
gen(F + 'XTopJointFaultN.lean', ['JAtZ.noFaultJN', 'JAtZ.faultBlockJN', 'JAtZ.sendFaultIJN', 'JAtZ.sendFaultPJN',
                                 'JAtZ.faultRecvJN', 'JAtZ.faultHypJZN'])
gen(F + 'XTopJointFaultRecvM.lean', ['JAtZ.sendFaultIJM', 'JAtZ.sendFaultPJM', 'JAtZ.faultRecvJM', 'JAtZ.faultHypJZM2'])
gen(F + 'XTopJointFaultRecvC.lean', ['JAtZ.sendFaultIJC', 'JAtZ.sendFaultPJC', 'JAtZ.sendFaultPDJC', 'JAtZ.faultRecvJC',
                                     'JAtZ.faultHypJZC2'])
gen(F + 'XTopJointFaultDonM.lean', ['JAtZ.sendFaultPDJM', 'JAtZ.faultRecvJM2', 'JAtZ.faultHypJZM3'])
