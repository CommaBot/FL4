#!/usr/bin/env python3
"""p3J gen 53: generalise mid-state receive leaves over their post, in place (gen 52's `…Q` pattern).

For each listed theorem T (post `RJR …` / `RJ …`, i.e. `RelTopM ∧ JAtR` / `RelTopM ∧ JAt`): the existing proof moves
to `TQ` whose post is `RelTopM ∧ Pq`, with `hPq` (every `JAtZR` resp. `JAtZ` at `Z.mv G V` with the entry's `H`,
`Cs` gives `Pq`) as its last explicit argument; T keeps its exact statement (header text byte-identical up to `:=`)
and is the one-line instance `TQ … (fun … J' => ⟨…, J', inferInstance⟩)`.
The exits of the moved bodies are then rewritten (perl / by hand): `hPq … J'` in place of the existential packaging.
Usage, from proofs/: python3 scratch/p3J/g53/gen.py <file> <name>...
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


POSTS = [('RJR (L := L) arI AR r.1 r.2 z.2', 'JAtZR', 'RJR'), ('RJ (L := L) arI AR r.1 r.2 z.2', 'JAtZ', 'RJ'),
         ('RelTopM (L := L) r.1 z.2 ∧ JAtR (L := L) arI AR r.1 r.2 z.2', 'JAtZR', 'RelTopM ∧ JAtR'),
         ('RelTopM (L := L) r.1 z.2 ∧ JAt (L := L) arI AR r.1 r.2 z.2', 'JAtZ', 'RelTopM ∧ JAt')]
NEWPOST = 'RelTopM (L := L) r.1 z.2 ∧ Pq r.1 r.2 z.2'


def gen(path, names):
    text = open(path).read()
    for name in names:
        pre, th, end = find_theorem(text, name)
        block_pre = text[pre:th]
        decl = text[th:end]
        header, proof = header_split(decl)
        kind = None
        for p, k, d in POSTS:
            if p in header and kind is None:
                kind = k; post = p; desc = d
        assert kind, name
        args = explicit_args(header)
        qn = name + 'Q'
        h = header.replace('theorem ' + name + ' ', 'theorem ' + qn + ' ', 1)
        h = h.replace('theorem ' + name + '\n', 'theorem ' + qn + '\n', 1)
        c = concl_colon(h)
        b = h[:c].rstrip()
        h = b + '\n    ' + hpq(kind) + ' :' + h[c + 1:]
        assert h.count(post) == 1, name
        h = h.replace(post, NEWPOST)
        hbs = [l for l in block_pre.split('\n') if l.startswith('set_option')]
        newdoc = ('/-- (p3J gen 53) **`' + name + '` with its post as a parameter** (module docstring: `Pq` from every `'
                  + kind + '` at `Z.mv G V` with the entry\'s `H`, `Cs`; `' + name + '` is its instance at `'
                  + desc + '`). -/\n')
        q = ('\n'.join(hbs) + '\n' if hbs else '') + newdoc + h + proof
        q = q.rstrip('\n') + '\n\n'
        if name.startswith('JAtZ.'):
            head = 'JAtZ.' + qn.split('.', 1)[1]
        else:
            head = qn
        call = ('\n  ' + head + ' (Pq := fun s\' a\' σ\' => ∃ (Z : XSets) (H : P1.Heap) (Cs Ac : Set U64) '
                '(Lst : U64 → List U64) (D : Set U64),\n    ' + kind + ' (L := L) arI AR Z H Cs Ac Lst D s\' a\' σ\' ∧ VxE Z)'
                '\n    ' + ' '.join(args) +
                ' (fun _ _ _ _ _ _ _ _ J\' => ⟨_, _, _, _, _, _, J\', inferInstance⟩)\n\n')
        orig = block_pre + header + call
        text = text[:pre] + q + orig + text[end:].lstrip('\n')
    open(path, 'w').write(text)


if __name__ == '__main__':
    gen(sys.argv[1], sys.argv[2:])
