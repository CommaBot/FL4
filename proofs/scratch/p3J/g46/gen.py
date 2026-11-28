#!/usr/bin/env python3
"""p3J gen 46: generalise XTopJointMRTcb / XTopJointMRTcbM in place (one proof per lemma).

For each listed theorem T: the existing proof moves to a new theorem T' (preempted invariant / exits as
parameters); T keeps its exact statement (header text byte-identical up to `:=`) and is proved by T'.
Run once from proofs/: python3 scratch/p3J/g46/gen.py
"""
import re, sys

WJPM = '(WJPM (L := L) arI AR MR Z H Cs kb)'
WPB = '{Wp : S → A → Fl4Spec.State Unit → MdbGhost → Prop}'


def split_decls(text):
    """Return list of (start, end) of top-level chunks beginning at `set_option`/`/--`/`theorem` lines."""
    return text


def find_theorem(text, name):
    m = re.search(r'^theorem ' + re.escape(name) + r'[ \n]', text, re.M)
    assert m, name
    th = m.start()
    # prefix: docstring and set_option lines directly above
    pre = th
    lines_above = text[:th].split('\n')
    # walk back over docstring + set_option
    i = len(lines_above) - 1  # last element is '' (text before th ends with \n)
    j = i - 1
    # docstring ends with '-/' line
    if lines_above[j].rstrip().endswith('-/'):
        while not lines_above[j].lstrip().startswith('/--'):
            j -= 1
        j -= 1
    while j >= 0 and lines_above[j].startswith('set_option'):
        j -= 1
    pre = len('\n'.join(lines_above[:j + 1])) + 1
    # end: next top-level decl start
    m2 = re.compile(r'^(set_option|/--|theorem |def |structure |abbrev |end\b|section\b|variable )', re.M).search(text, th + 1)
    end = m2.start() if m2 else len(text)
    return pre, th, end


def header_split(decl):
    """decl starts at `theorem`. Return (header up to and incl. ':=' , rest)."""
    depth = 0
    i = 0
    while i < len(decl):
        c = decl[i]
        if c in '([{⟨⦃':
            depth += 1
        elif c in ')]}⟩⦄':
            depth -= 1
        elif decl.startswith(':=', i) and depth == 0:
            return decl[:i + 2], decl[i + 2:]
        i += 1
    raise ValueError('no :=')


def explicit_args(header):
    """Names of the explicit binders of the header (after the theorem name, before the top-level ':')."""
    body = header[len('theorem '):]
    body = body.split(None, 1)[1]
    names = []
    depth = 0
    i = 0
    cur = None
    while i < len(body):
        c = body[i]
        if depth == 0 and c == ':':
            break
        if c in '([{⟨⦃':
            if depth == 0:
                cur = (c, i)
            depth += 1
        elif c in ')]}⟩⦄':
            depth -= 1
            if depth == 0 and cur[0] == '(':
                inner = body[cur[1] + 1:i]
                d2 = 0
                k = 0
                while k < len(inner):
                    if inner[k] in '([{':
                        d2 += 1
                    elif inner[k] in ')]}':
                        d2 -= 1
                    elif inner[k] == ':' and d2 == 0:
                        break
                    k += 1
                names += inner[:k].split()
        i += 1
    return names


def gen_file(path, specs, extra_after=None):
    text = open(path).read()
    for name, newname, fsig, fbody, fcall, newdoc, hb in specs:
        pre, th, end = find_theorem(text, name)
        block_pre = text[pre:th]
        decl = text[th:end]
        header, proof = header_split(decl)
        args = explicit_args(header)
        ghead = fsig(header.replace('theorem ' + name, 'theorem ' + newname, 1))
        gproof = fbody(proof)
        gen = ''
        hbs = [l for l in block_pre.split('\n') if l.startswith('set_option')]
        if hbs:
            gen += '\n'.join(hbs) + '\n'
        gen += '/-- (p3J gen 46) ' + newdoc + ' -/\n' + ghead + gproof
        if not gen.endswith('\n\n'):
            gen = gen.rstrip('\n') + '\n\n'
        # corollary: the original docstring, no heartbeat option
        doc = '\n'.join(l for l in block_pre.split('\n') if not l.startswith('set_option'))
        cor = doc + header + '\n  ' + fcall(newname, args) + '\n\n'
        text = text[:pre] + gen + cor + text[end:]
    if extra_after:
        for anchor, add in extra_after:
            i = text.index(anchor)
            text = text[:i] + add + text[i:]
    open(path, 'w').write(text)


# ---------- XTopJointMRTcb: the installs, preempted invariant `Wp` ----------
MRT = ['install_tcb_capJM', 'install_okJM', 'install_bufferJM', 'thread_control_capsJM', 'install_fhJM',
       'install_fhOkJM']


def rn_mrt(s):
    for n in MRT:
        s = re.sub(r'\b' + n + r'\b', n + 'p', s)
    return s


def sig_mrt(h):
    assert WJPM in h, h[:80]
    h = h.replace(WJPM, 'Wp')
    h = h.replace('{W : S → A → Fl4Spec.State Unit → MdbGhost → Prop}',
                  '{W : S → A → Fl4Spec.State Unit → MdbGhost → Prop} ' + WPB, 1)
    return h


def body_mrt(p):
    assert 'WJPM' not in p or True
    p = p.replace(WJPM, 'Wp')
    return rn_mrt(p)


def call_mrt(newname, args):
    return newname + ' arI ' + ' '.join(args)


specs1 = []
for n in MRT:
    specs1.append((n, n + 'p', sig_mrt, body_mrt, call_mrt,
                   '**`' + n + '` with the preempted invariant a parameter `Wp`** (`' + n + '` is the `WJPM` '
                   'instance).', None))

# ---------- XTopJointMRTcbM: the labels, exits `Xo` / `Xp` and `Wp` ----------
LBL = ['tcb_set_timeoutJMM', 'tcb_set_spaceJMM', 'tcb_set_ipcJMM', 'tcb_configureJMM']
OLDH = ('(hHp : TcbInsWM (L := L) arI AR MR Z H Cs W Rd Rz)\n'
        '    (hmR : MR ar σ.machineState) (hWM : ∀ kb s a σ G, W kb s a σ G → MR a σ.machineState)\n'
        '    (hMP : MachPlat arI MR) (hKD : MRKeepD arI MR) (hR : ')
NEWH = ('{Wp : U64 → S → A → Fl4Spec.State Unit → MdbGhost → Prop}\n'
        '    {Xo Xp : S → A → Fl4Spec.State Unit → Prop} (hHp : TcbInsWG (L := L) arI AR Z H Cs W Wp Rd Rz)\n'
        '    (hX0 : Xo s ar σ) (hwx : ∀ kb s a σ G, W kb s a σ G → Xo s a σ)\n'
        '    (hwp : ∀ kb s a σ G, Wp kb s a σ G → WJP (L := L) arI AR Z H Cs kb s a σ G ∧ Xp s a σ)\n'
        '    (hR : ')
EXJ = '(JAtM (L := L) arI AR MR)'
EXP = '(JAtPreMV (L := L) arI AR MR)'


def ex_sub(s):
    s = re.sub(re.escape(EXJ) + r'(\s*)' + re.escape(EXP), r'Xo\1Xp', s)
    return s


def sig_lbl(h):
    assert OLDH in h, h[:100]
    h = h.replace(OLDH, NEWH)
    h2 = ex_sub(h)
    assert h2 != h
    return h2


def body_lbl(p):
    p = re.sub(r'have hJ0 : JAtM \(L := L\) arI AR MR s ar σ := ⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hmR⟩',
               'have hJ0 : Xo s ar σ := hX0', p)
    p = p.replace('top_of_instJMM arI (hHp.ins _).wjr (hWM _)', 'top_of_instJMG arI (hHp.ins _).wjr (hwx _) (hwp _)')
    p = p.replace('.restartWM arI', '.restartWG arI')
    p = ex_sub(p)
    p = rn_mrt(p)
    for bad in ['hmR', 'hWM', 'hMP', 'hKD', 'JAtM', 'JAtPreMV', 'top_of_instJMM', 'restartWM']:
        assert not re.search(r'\b' + bad + r'\b', p), bad
    return p


def call_lbl(newname, args):
    out = []
    for a in args:
        if a == 'hHp':
            out.append('hHp.toG')
        elif a == 'hmR':
            out.append('⟨⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩, hmR⟩')
        elif a == 'hWM':
            out.append('(hHp.jAtM hWM) (fun _ _ _ _ _ h => h)')
        elif a in ('hMP', 'hKD'):
            continue
        else:
            out.append(a)
    return newname + ' arI ' + ' '.join(out)


specs2 = []
for n in LBL:
    nn = n[:-3] + 'JMG'
    specs2.append((n, nn, sig_lbl, body_lbl, call_lbl,
                   '**`' + n + '` with the preempted invariant `Wp` and the exits `Xo` (start, Ok) / `Xp` '
                   '(preempted) as parameters** (`' + n + '` is the `WJPM` / `JAtM` / `JAtPreMV` instance).',
                   None))

if __name__ == '__main__':
    which = sys.argv[1]
    if which == 'mrt':
        gen_file('Fl4Proofs/P3/XTopJointMRTcb.lean', specs1)
    elif which == 'mrtm':
        gen_file('Fl4Proofs/P3/XTopJointMRTcbM.lean', specs2)
