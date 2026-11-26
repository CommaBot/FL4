#!/usr/bin/env python3
"""Port x86_64 proof modules (Fl4Proofs.*) to the AArch64 extraction (Fl4ProofsA64.*).

The two extractions cannot share a Lean module: Fl4Core/FunsExternal.lean and
Fl4CoreA64/FunsExternal.lean define the same root-level library models. So an x86
proof is reused for AArch64 by re-elaborating its text against Fl4CoreA64: rename
`fl4_core` -> `fl4_core_a64`, `Fl4Core.` -> `Fl4CoreA64.`, `Fl4Proofs.` -> `Fl4ProofsA64.`
(imports and namespaces). Lean then re-checks every proof over the AArch64 definitions;
a proof that goes through verbatim is a proof about the AArch64 function.

usage: port.py PROOFS_DIR MODULE [MODULE ...]   (MODULE like Fl4Proofs.P1.Queue)
  --drop IMPORT   leave out an x86-only import (repeatable)
  --sub X=Y       replace the numeral X by Y (a layout constant that differs, e.g. ks::NODES
                  13568=223488); each replaced line is marked `-- a64: X->Y` (repeatable;
                  all applied in one pass, so 128=136 136=144 shifts a range)
Writes Fl4ProofsA64/<path>.lean with a header naming its x86 source.
"""
import re, sys, os

def port(text, drops, subs=()):
    out = []
    for l in text.splitlines(True):
        m = re.match(r'^import\s+(\S+)\s*$', l)
        if m and m.group(1) in drops:
            continue
        if subs:
            # all substitutions in one pass, so 128=136 136=144 shifts a range
            table = dict(subs)
            pat = r'(?<![\w.])(' + '|'.join(re.escape(x) for x, _ in subs) + r')(?![\w.])'
            hits = re.findall(pat, l)
            if hits:
                l = re.sub(pat, lambda m: table[m.group(1)], l)
                if '-/' not in l and not l.lstrip().startswith('/-'):
                    l = l.rstrip('\n') + '  -- a64: ' + ', '.join('%s->%s' % (h, table[h]) for h in hits) + '\n'
        out.append(l)
    t = ''.join(out)
    t = re.sub(r'\bfl4_core\b(?!_a64)', 'fl4_core_a64', t)
    t = re.sub(r'\bFl4Core\.', 'Fl4CoreA64.', t)
    t = re.sub(r'\bFl4Proofs\.', 'Fl4ProofsA64.', t)
    return t

def main():
    args = sys.argv[1:]
    drops = set()
    subs = []
    mods = []
    root = args.pop(0)
    while args:
        a = args.pop(0)
        if a == '--drop':
            drops.add(args.pop(0))
        elif a == '--sub':
            x, y = args.pop(0).split('=')
            subs.append((x, y))
        else:
            mods.append(a)
    for m in mods:
        src = os.path.join(root, *m.split('.')) + '.lean'
        dst_mod = re.sub(r'^Fl4Proofs\.', 'Fl4ProofsA64.', m)
        dst = os.path.join(root, *dst_mod.split('.')) + '.lean'
        t = port(open(src).read(), drops, subs)
        hdr = ('-- AArch64 port of %s (proofs/scratch/a64/port.py): the x86_64 text, re-checked\n'
               '-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.\n') % m
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w').write(hdr + t)
        print(src, '->', dst)

main()
