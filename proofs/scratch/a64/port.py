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
Writes Fl4ProofsA64/<path>.lean with a header naming its x86 source.
"""
import re, sys, os

def port(text, drops):
    out = []
    for l in text.splitlines(True):
        m = re.match(r'^import\s+(\S+)\s*$', l)
        if m and m.group(1) in drops:
            continue
        out.append(l)
    t = ''.join(out)
    t = re.sub(r'\bfl4_core\b(?!_a64)', 'fl4_core_a64', t)
    t = re.sub(r'\bFl4Core\.', 'Fl4CoreA64.', t)
    t = re.sub(r'\bFl4Proofs\.', 'Fl4ProofsA64.', t)
    return t

def main():
    args = sys.argv[1:]
    drops = set()
    mods = []
    root = args.pop(0)
    while args:
        a = args.pop(0)
        if a == '--drop':
            drops.add(args.pop(0))
        else:
            mods.append(a)
    for m in mods:
        src = os.path.join(root, *m.split('.')) + '.lean'
        dst_mod = re.sub(r'^Fl4Proofs\.', 'Fl4ProofsA64.', m)
        dst = os.path.join(root, *dst_mod.split('.')) + '.lean'
        t = port(open(src).read(), drops)
        hdr = ('-- AArch64 port of %s (proofs/scratch/a64/port.py): the x86_64 text, re-checked\n'
               '-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.\n') % m
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        open(dst, 'w').write(hdr + t)
        print(src, '->', dst)

main()
