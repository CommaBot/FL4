#!/usr/bin/env python3
"""Generate `SProg` program trees for the extracted local-path bodies (P2 `hpz`, line hpzg).

For every Store/Arch-generic function in the call closure of the given roots (`proofs/Fl4Core/Funs.lean`),
bottom-up, emit
  * `R.<f> args : SProg V` -- the body with the store / Arch threading removed: store calls become
    `SProg.read` / `SProg.write` / ..., Arch calls `AR.<m>`, callees `R.<g>`, `lift e` `pure e`, other pure
    `Result` steps `SProg.liftR e`; `ok (v, s', a')` becomes `pure v`;
  * `R.<f>_eq` : `interp st ar (R.<f> args) s a = f st ar s a args >>= fun r => ok (v r, s' r, a' r)`
    (projection form), proved by `unfold R.<f>; simp only [reif_simps, f]; reif_loop`;
  * `R.<f>_nz` : `NoZero (R.<f> args)`;
  * loops: `R.<L>.body` with its equation, the measure lemma `R.<L>.dec` and the wrapper through
    `interp_iterS`.
Pure heads used by `SProg.liftR` get `nd.<g>` (never `div`, from P0's `<g>.p0`).

Usage: python3 xtask/scripts/gen_prog.py <Prefix> <root> [<root> ...]
  writes proofs/Fl4Proofs/P2/ProgGen<Prefix><n>.lean (split by dependency level / size) and prints the
  module list. Run from the repository root.
"""
import re, sys, os, collections

FUNS = 'proofs/Fl4Core/Funs.lean'
P0AUTO = 'proofs/Fl4Proofs/P0/Auto.lean'
OUTDIR = 'proofs/Fl4Proofs/P2'

src = open(FUNS).read()
p0src = open(P0AUTO).read()
P0NAMES = set(re.findall(r'theorem ([\w.]+)\.p0\b', p0src))

# ---------------------------------------------------------------- definitions
DEFRE = re.compile(r'^def ([\w.]+)\b(.*?)(?=^(?:def |/--|@\[|theorem |end |noncomputable |instance |structure |inductive |impl_def |/-|$))',
                   re.S | re.M)


class Fn:
    pass


def split_top(s, sep):
    """Split at top-level occurrences of sep (outside brackets)."""
    out, depth, cur, i = [], 0, '', 0
    while i < len(s):
        c = s[i]
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur)
            cur = ''
            i += len(sep)
            continue
        cur += c
        i += 1
    out.append(cur)
    return [x.strip() for x in out]


def strip_parens(s):
    s = s.strip()
    while s.startswith('(') and s.endswith(')'):
        d = 0
        ok = True
        for i, c in enumerate(s):
            if c in '([{':
                d += 1
            elif c in ')]}':
                d -= 1
            if d == 0 and i < len(s) - 1:
                ok = False
                break
        if not ok:
            break
        s = s[1:-1].strip()
    return s


def parse_header(name, text):
    # header: up to the first top-level ':=' ; params are bracket groups, then ':' ret
    depth = 0
    i = 0
    while i < len(text):
        c = text[i]
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and text.startswith(':=', i):
            break
        i += 1
    hdr, body = text[:i], text[i + 2:]
    params = []
    j = 0
    while True:
        while j < len(hdr) and hdr[j].isspace():
            j += 1
        if j < len(hdr) and hdr[j] in '({':
            close = ')' if hdr[j] == '(' else '}'
            d = 0
            k = j
            while True:
                if hdr[k] in '({':
                    d += 1
                elif hdr[k] in ')}':
                    d -= 1
                    if d == 0:
                        break
                k += 1
            grp = hdr[j + 1:k]
            names, ty = grp.split(':', 1)
            for n in names.split():
                params.append((n, ' '.join(ty.split()), hdr[j] == '{'))
            j = k + 1
        else:
            break
    rest = hdr[j:].strip()
    assert rest.startswith(':'), (name, rest)
    ret = ' '.join(rest[1:].split())
    body = body.strip()
    if body.startswith('do'):
        body = body[2:]
    f = Fn()
    f.name, f.params, f.ret, f.body = name, [p for p in params if not p[2]], ret, body
    f.raw = text
    tys = [p[1] for p in f.params]
    f.eff = 'machine.Store S' in tys or 'machine.Arch A' in tys
    return f


FUNCS = {}
for m in DEFRE.finditer(src):
    name = m.group(1)
    try:
        FUNCS[name] = parse_header(name, m.group(2))
    except Exception:
        pass


def ret_kinds(ret):
    """Flat components of `Result T` as [(kind, type)]; kind S/A/V. No S/A: one V component."""
    assert ret.startswith('Result'), ret
    t = strip_parens(ret[len('Result'):].strip())
    comps = split_top(t, '×')
    if len(comps) > 1 and any(c in ('S', 'A') for c in comps):
        return [('S' if c == 'S' else 'A' if c == 'A' else 'V', c) for c in comps]
    if t in ('S', 'A'):
        return [(t, t)]
    return [('V', t)]


def vtype(K):
    vs = [t for k, t in K if k == 'V']
    if not vs:
        return 'Unit'
    if len(vs) == 1:
        v = vs[0]
        return v if ' ' not in v or strip_parens(v) != v else '(' + v + ')'
    return '(' + ' × '.join(vs) + ')'


# ---------------------------------------------------------------- tokens / parser
TOKRE = re.compile(r'\s+|[()\[\]{},]|[^\s()\[\]{},]+')


class Tok:
    __slots__ = ('t', 'line', 'col', 'start', 'end', 'first', 'depth')


def tokenize(text):
    toks = []
    line, col0 = 0, 0
    pos = 0
    lastline = -1
    depth = 0
    for m in TOKRE.finditer(text):
        s = m.group(0)
        if s.isspace():
            continue
        t = Tok()
        t.t = s
        t.start, t.end = m.start(), m.end()
        t.line = text.count('\n', 0, m.start())
        ls = text.rfind('\n', 0, m.start()) + 1
        t.col = m.start() - ls
        t.first = t.line != lastline
        lastline = t.line
        if s in ')]}':
            depth -= 1
        t.depth = depth
        if s in '([{':
            depth += 1
        toks.append(t)
    return toks


class G:
    text = ''


def ttext(toks):
    if not toks:
        return ''
    return ' '.join(G.text[toks[0].start:toks[-1].end].split())


def rel_depth(toks):
    base = toks[0].depth if toks else 0
    return base


def parse_seq(toks):
    """A do-sequence: items at the column of its first token."""
    assert toks
    if toks[0].t == 'do':
        return [('tail', ('seq', parse_seq(toks[1:])))]
    c = toks[0].col
    d0 = toks[0].depth
    items, cur = [], []
    for t in toks:
        if cur and t.first and t.col == c and t.depth == d0 and t.t not in ('then', 'else', '|'):
            items.append(cur)
            cur = []
        cur.append(t)
    items.append(cur)
    out = []
    for i, it in enumerate(items):
        if it[0].t == 'let':
            d = it[0].depth
            k = next(j for j, t in enumerate(it) if t.depth == d and t.t in ('←', ':='))
            out.append(('let', it[1:k], it[k].t, parse_expr(it[k + 1:])))
        else:
            assert i == len(items) - 1, ('non-let item not last', ttext(it))
            out.append(('tail', parse_expr(it)))
    return out


def parse_expr(toks):
    d = toks[0].depth
    h = toks[0].t
    if h == 'if':
        ti = next(j for j, t in enumerate(toks) if t.depth == d and t.t == 'then')
        nest = 0
        ej = None
        for j in range(ti + 1, len(toks)):
            t = toks[j]
            if t.depth != d:
                continue
            if t.t == 'if':
                nest += 1
            elif t.t == 'else':
                if nest == 0:
                    ej = j
                    break
                nest -= 1
        assert ej is not None, ttext(toks)
        return ('if', toks[1:ti], parse_seq(toks[ti + 1:ej]), parse_seq(toks[ej + 1:]))
    if h == 'match':
        wi = next(j for j, t in enumerate(toks) if t.depth == d and t.t == 'with')
        bars = [j for j, t in enumerate(toks) if j > wi and t.depth == d and t.t == '|']
        c = toks[bars[0]].col
        bars = [j for j in bars if toks[j].col == c and (toks[j].first or j == bars[0])]
        arms = []
        for k, b in enumerate(bars):
            e = bars[k + 1] if k + 1 < len(bars) else len(toks)
            arm = toks[b + 1:e]
            ai = next(j for j, t in enumerate(arm) if t.depth == d and t.t == '=>')
            arms.append((arm[:ai], parse_seq(arm[ai + 1:])))
        return ('match', toks[1:wi], arms)
    if h == 'do':
        return ('seq', parse_seq(toks[1:]))
    return ('term', toks)


def call_args(toks):
    """Split application argument tokens into argument texts (bracket groups or single tokens)."""
    args = []
    i = 0
    while i < len(toks):
        t = toks[i]
        if t.t in '([{':
            d = t.depth
            j = i + 1
            while not (toks[j].t in ')]}' and toks[j].depth == d):
                j += 1
            args.append(ttext(toks[i:j + 1]))
            i = j + 1
        else:
            args.append(t.t)
            i += 1
    return args


# ---------------------------------------------------------------- translation
STORE_LEAF = {
    'read': ('SProg.read', [('V', 'U64')]),
    'read_pair': ('SProg.readPair', [('V', '(U64 × U64)')]),
    'write': ('SProg.write', [('S', 'S')]),
    'ks_base': ('SProg.ksBase', [('V', 'U64')]),
    'cur_cpu': ('SProg.curCpu', [('V', 'U64')]),
    'frame_masks': ('SProg.frameMasks', [('V', '(U64 × U64)')]),
}
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_arch_leaves  # noqa: E402
ARCH_K = {m: ([('A', 'A')] if k == 'A' else [('V', vt)] if k == 'V' else [('V', vt), ('A', 'A')])
          for (m, _, k, _, vt) in gen_arch_leaves.ARCH}


class Ctx:
    def __init__(self, fn):
        self.fn = fn
        self.callees = set()
        self.arch = set()
        self.pure = set()
        self.loops = set()
        self.blks = []


def is_eff(name):
    return name in FUNCS and FUNCS[name].eff


def callee_kinds(name):
    f = FUNCS[name]
    if name.endswith('_loop') or re.search(r'_loop\d*$', name):
        pass
    return ret_kinds(f.ret)


def dropped(ty):
    return ty in ('machine.Store S', 'machine.Arch A', 'S', 'A')


def tr_call(toks, ctx):
    """An effectful call term -> (tree text, kinds)."""
    head = toks[0].t
    args = call_args(toks[1:])
    if head.startswith('machineStoreInst.'):
        m = head.split('.', 1)[1]
        assert m in STORE_LEAF, ('store op', m)
        leaf, K = STORE_LEAF[m]
        return (' '.join([leaf] + args[1:]), K)
    if head.startswith('machineArchInst.'):
        m = head.split('.', 1)[1]
        assert m in ARCH_K, ('arch op', m)
        ctx.arch.add(m)
        return (' '.join(['AR.' + m] + args[1:]), ARCH_K[m])
    f = FUNCS[head]
    assert len(args) == len(f.params), ('arity', head, args, f.params)
    kept = [a for a, (n, ty, _) in zip(args, f.params) if not dropped(ty)]
    ctx.callees.add(head)
    return (' '.join(['R.' + head] + kept), ret_kinds(f.ret))


def is_call(toks):
    h = toks[0].t
    return h.startswith('machineStoreInst.') or h.startswith('machineArchInst.') or is_eff(h)


def pat_comps(ptoks):
    p = ttext(ptoks)
    q = strip_parens(p)
    if p.startswith('(') and len(split_top(q, ',')) > 1:
        return split_top(q, ',')
    return [p]


def pat_names(ptoks):
    return [t.t for t in ptoks if re.match(r'^[\w«»]', t.t)]


def bind_pat(ptoks, K, env):
    """Pattern of a bind with result kinds K -> (tree pattern, new env)."""
    comps = pat_comps(ptoks)
    env = dict(env)
    if len(K) == 1:
        if K[0][0] == 'V':
            for c in pat_names(ptoks):
                env.pop(c, None)
            return ttext(ptoks), env
        if comps[0] != '_':
            env[comps[0]] = K[0][0]
        return '_', env
    assert len(comps) == len(K), ('pattern arity', comps, K)
    vs = []
    for c, (k, _) in zip(comps, K):
        if k == 'V':
            vs.append(c)
            env.pop(c, None)
        elif c != '_':
            env[c] = k
    if not vs:
        return '_', env
    if len(vs) == 1:
        return vs[0], env
    return '(' + ', '.join(vs) + ')', env


def vals_of(xtext, K, env):
    """`ok X` with expected kinds K -> the tree's value text."""
    if K == 'CF':
        raise AssertionError
    if len(K) == 1:
        if K[0][0] == 'V':
            return xtext
        return '()'
    comps = split_top(strip_parens(xtext), ',')
    assert len(comps) == len(K), ('ok arity', xtext, K)
    vs = [c for c, (k, _) in zip(comps, K) if k == 'V']
    if not vs:
        return '()'
    if len(vs) == 1:
        return vs[0]
    return '(' + ', '.join(vs) + ')'


def infer_kinds(node, env):
    """Kinds of a compound sub-block's result, from its tails."""
    def tails(n, env):
        if n[0] == 'if':
            yield from seq_tails(n[2], env)
            yield from seq_tails(n[3], env)
        elif n[0] == 'match':
            for _, s in n[2]:
                yield from seq_tails(s, env)
        elif n[0] == 'seq':
            yield from seq_tails(n[1], env)
        else:
            yield n, env

    def seq_tails(seq, env):
        e = dict(env)
        for it in seq:
            if it[0] == 'let':
                rhs = it[3]
                if rhs[0] == 'term' and is_call(rhs[1]):
                    _, K = tr_call(rhs[1], Ctx(None))
                    _, e = bind_pat(it[1], K, e)
                elif rhs[0] != 'term':
                    Kb = infer_kinds(rhs, e)
                    _, e = bind_pat(it[1], Kb, e)
            else:
                yield from tails(it[1], e)

    best = None
    for t, e in seq_tails([('tail', node)], env):
        toks = t[1]
        if toks[0].t == 'ok':
            x = strip_parens(ttext(toks[1:]))
            comps = split_top(x, ',')
            if len(comps) == 1:
                k = e.get(comps[0], 'V')
                return [(k, '?')]
            return [(e.get(c, 'V'), '?') for c in comps]
        if is_call(toks):
            return tr_call(toks, Ctx(None))[1]
    raise AssertionError('cannot infer kinds')


IND = '  '


def ind(lines, n=1):
    return [IND * n + l for l in lines]


def tr_seq(seq, env, K, ctx):
    out = []
    for it in seq:
        if it[0] == 'let':
            _, ptoks, op, rhs = it
            if op == ':=' or (rhs[0] == 'term' and not is_call(rhs[1])):
                env = {k: v for k, v in env.items() if k not in pat_names(ptoks)}
            if op == ':=':
                assert rhs[0] == 'term'
                out.append(f'let {ttext(ptoks)} := {ttext(rhs[1])}')
                continue
            if rhs[0] == 'term':
                toks = rhs[1]
                if toks[0].t == 'lift':
                    out.append(f'let {ttext(ptoks)} ← pure ({ttext(toks[1:])})')
                elif is_call(toks):
                    call, Kc = tr_call(toks, ctx)
                    pat, env = bind_pat(ptoks, Kc, env)
                    out.append(f'let {pat} ← {call}')
                else:
                    for t in toks:
                        assert t.t not in env, ('state var in pure step', ttext(toks))
                    ctx.pure.add(ttext(toks))
                    out.append(f'let {ttext(ptoks)} ← SProg.liftR ({ttext(toks)})')
            else:
                Kb = infer_kinds(rhs, env)
                sub = tr_expr(rhs, env, Kb, ctx)
                pat, env = bind_pat(ptoks, Kb, env)
                k = len(ctx.blks)
                ctx.blks.append(Kb)
                out.append(f'let {pat} ← SProg.blk {k} (')
                sub = ind(sub, 2)
                sub[-1] += ')'
                out.extend(sub)
        else:
            out.extend(tr_expr(it[1], env, K, ctx))
    return out


def tr_expr(node, env, K, ctx):
    if node[0] == 'if':
        return ([f'if {ttext(node[1])} then do'] + ind(tr_seq(node[2], env, K, ctx)) +
                ['else do'] + ind(tr_seq(node[3], env, K, ctx)))
    if node[0] == 'match':
        out = [f'match {ttext(node[1])} with']
        for p, s in node[2]:
            out.append(f'| {ttext(p)} => do')
            out.extend(ind(tr_seq(s, env, K, ctx), 2))
        return out
    if node[0] == 'seq':
        return ['do'] + ind(tr_seq(node[1], env, K, ctx))
    toks = node[1]
    h = toks[0].t
    if h == 'ok':
        x = ttext(toks[1:])
        if isinstance(K, tuple) and K[0] == 'CF':
            _, Kc, Kd = K
            y = strip_parens(x)
            ctor, rest = y.split(None, 1) if ' ' in y else (y, '')
            assert ctor in ('cont', 'done', 'ControlFlow.cont', 'ControlFlow.done'), y
            Kx = Kc if ctor.endswith('cont') else Kd
            v = vals_of(rest, Kx, env)
            return [f'pure (.{ctor.split(".")[-1]} {v})']
        return [f'pure {"(" + vals_of(x, K, env) + ")"}']
    if h == 'fail':
        return [f'SProg.err ({ttext(toks[1:])})']
    if is_call(toks):
        call, Kc = tr_call(toks, ctx)
        assert [k for k, _ in Kc] == [k for k, _ in K], ('tail kinds', ttext(toks), Kc, K)
        return [call]
    assert not isinstance(K, tuple) and len(K) == 1 and K[0][0] == 'V', ('pure tail', ttext(toks), K)
    ctx.pure.add(ttext(toks))
    return [f'SProg.liftR ({ttext(toks)})']


# ---------------------------------------------------------------- loops
LOOPRE = re.compile(r'^\s*loop\s*\(fun\s*(\(.*?\)|\w+)\s*=>\s*([\w.]+)(.*)\)\s*(\(.*\)|\w+)\s*$', re.S)


def is_loop(f):
    return f.body.strip().startswith('loop')


def cf_kinds(ret):
    t = strip_parens(ret[len('Result'):].strip())
    assert t.startswith('ControlFlow'), t
    old = G.text
    G.text = t[len('ControlFlow'):]
    a = call_args(tokenize(G.text))
    G.text = old
    return ret_kinds('Result ' + a[0]), ret_kinds('Result ' + a[1])


# ---------------------------------------------------------------- emission
def binders(f):
    return ' '.join(f'({n} : {ty})' for n, ty, _ in f.params if not dropped(ty))


def argnames(f):
    return ' '.join(n for n, ty, _ in f.params if not dropped(ty))


def aeneas_call(f, own=False):
    xs = []
    for n, ty, _ in f.params:
        xs.append({'machine.Store S': 'mS', 'machine.Arch A': 'mA'}.get(ty) or
                  (n if own else {'S': 'sS', 'A': 'aA'}.get(ty, n)))
    return 'fl4_core.' + f.name + ' ' + ' '.join(xs)


def proj(i, n, r='r'):
    if n == 1:
        return r
    return r + '.2' * i + ('.1' if i < n - 1 else '')


def blk_shape(K):
    if all(k == 'V' for k, _ in K):
        return '(fun r sB aB => (r, sB, aB))'
    n = len(K)
    vs = [proj(i, n) for i, (k, _) in enumerate(K) if k == 'V']
    ss = [proj(i, n) for i, (k, _) in enumerate(K) if k == 'S']
    as_ = [proj(i, n) for i, (k, _) in enumerate(K) if k == 'A']
    v = '()' if not vs else vs[0] if len(vs) == 1 else '(' + ', '.join(vs) + ')'
    return f'(fun r sB aB => ({v}, {ss[0] if ss else "sB"}, {as_[0] if as_ else "aB"}))'


def proof_loop(ctx):
    if not ctx.blks:
        return ['  reif_loop']
    shs = [f'((refine (show BlkShape S A {k} _ _ from ?_)); exact {blk_shape(K)})' for k, K in enumerate(ctx.blks)]
    return (['  repeat\' (first', '    | (with_reducible apply bind_congr_r; intro)',
             '    | (with_reducible refine ite_congr\' (fun _ => ?_) (fun _ => ?_))',
             '    | (with_reducible refine ite_bind_congr\' (fun _ => ?_) (fun _ => ?_))',
             '    | (simp only [reif_simps])',
             '    | ((with_reducible refine bind_cut mS mA ?sh ?_ (fun _ => ?_)); (case sh => first'] +
            [f'      | {x}' for x in shs] + ['      ))', '    | reif_step)'])


def shape(K):
    n = len(K)
    vs = [proj(i, n) for i, (k, _) in enumerate(K) if k == 'V']
    ss = [proj(i, n) for i, (k, _) in enumerate(K) if k == 'S']
    as_ = [proj(i, n) for i, (k, _) in enumerate(K) if k == 'A']
    v = '()' if not vs else vs[0] if len(vs) == 1 else '(' + ', '.join(vs) + ')'
    return f'fun r => ok ({v}, {ss[0] if ss else "sS"}, {as_[0] if as_ else "aA"})'


def gen_fn(f, out):
    """Emit def / _eq / _nz for a non-loop effectful function."""
    K = ret_kinds(f.ret)
    G.text = f.body
    toks = tokenize(f.body)
    seq = parse_seq(toks)
    env = {n: ty for n, ty, _ in f.params if ty in ('S', 'A')}
    ctx = Ctx(f)
    body = tr_seq(seq, env, K, ctx)
    vt = vtype(K)
    out.append(f'@[irreducible] noncomputable def R.{f.name} {binders(f)} : SProg {vt} := do')
    out.extend(ind(body))
    out.append('')
    out.append(f'@[reif_simps] theorem R.{f.name}_eq {binders(f)} (sS : S) (aA : A) :')
    out.append(f'    interp mS mA (R.{f.name} {argnames(f)}) sS aA =')
    out.append(f'      ({aeneas_call(f)} >>= {shape(K)}) := by')
    out.append(f'  unfold R.{f.name}')
    out.append(f'  simp only [reif_simps, fl4_core.{f.name}]')
    out.extend(proof_loop(ctx))
    out.append('')
    emit_nz(f, ctx, out)
    return ctx


def emit_nz(f, ctx, out, name=None):
    name = name or f.name
    alts = ['(with_reducible apply NoZero.sbind)', '(with_reducible apply NoZero.blk)',
            "(with_reducible apply NoZero.ite')", '(with_reducible exact NoZero.liftR _)',
            '(with_reducible exact NoZero.read _)', '(with_reducible exact NoZero.readPair _)',
            '(with_reducible exact NoZero.write _ _)', '(with_reducible exact NoZero.ksBase)',
            '(with_reducible exact NoZero.curCpu)', '(with_reducible exact NoZero.frameMasks)',
            '(intro; try dsimp only)']
    alts += [f'(with_reducible apply R.{g}_nz)' for g in sorted(ctx.callees)]
    alts += [f'(with_reducible apply AR.{m}_nz)' for m in sorted(ctx.arch)]
    alts += ['(simp only [reif_nz])', 'split', '(exact trivial)', '(dsimp only)']
    out.append(f'@[reif_nz] theorem R.{name}_nz {binders(f)} : NoZero (R.{name} {argnames(f)}) := by')
    out.append(f'  unfold R.{name}')
    out.append(f'  try simp only [SProg.bind_eq_sbind, SProg.pure_eq_ret]')
    out.append('  repeat\' (first')
    for x in alts:
        out.append(f'    | {x}')
    out[-1] += ')'
    out.append('')


MEASURE = {}  # loop name -> (measure on loop vars text using x, on σ0 text)


def projs(v, n):
    if n == 1:
        return [v]
    return [v + '.2' * i + ('.1' if i < n - 1 else '') for i in range(n)]


def tup(xs):
    return '()' if not xs else xs[0] if len(xs) == 1 else '(' + ', '.join(xs) + ')'


def gen_loop(L, out):
    """Emit the loop body tree, its equation, the measure lemma and the wrapper."""
    B = FUNCS[L.name + '.body']
    Kc, Kd = cf_kinds(B.ret)
    kc = [k for k, _ in Kc]
    kd = [k for k, _ in Kd]
    mode = 'R' if not ({'S', 'A'} & set(kc + kd)) else 'SA' if 'A' in kc else 'S'
    if mode == 'R':
        Kc, Kd = [('V', ' × '.join(t for _, t in Kc))], [('V', ' × '.join(t for _, t in Kd))]
        Kc2 = split_top(strip_parens(Kc[0][1]), '×')
    G.text = B.body
    seq = parse_seq(tokenize(B.body))
    env = {n: ty for n, ty, _ in B.params if ty in ('S', 'A')}
    ctx = Ctx(B)
    body = tr_seq(seq, env, ('CF', Kc, Kd), ctx)
    vx, vy = vtype(Kc), vtype(Kd)
    out.append(f'@[irreducible] noncomputable def R.{B.name} {binders(B)} : SProg (ControlFlow {vx} {vy}) := do')
    out.extend(ind(body))
    out.append('')
    tc = ' × '.join(t for _, t in Kc)
    td = ' × '.join(t for _, t in Kd)
    # loop variables: the last nx non-state params of B
    bps = [(n, ty) for n, ty, _ in B.params if ty not in ('machine.Store S', 'machine.Arch A')]
    nonst = [(n, ty) for n, ty in bps if ty not in ('S', 'A')]
    if mode == 'R':
        nx = len(Kc2)
    else:
        nx = kc.count('V')
    lvars = nonst[len(nonst) - nx:] if nx else []
    lvn = [n for n, _ in lvars]
    xp = projs('xL', nx) if nx else []
    hasA = any(ty == 'machine.Arch A' for _, ty, _ in B.params)
    sta = 'mS mA' if hasA else 'mS'
    if mode == 'R':
        shapeB = 'fun r => ok (r, sS, aA)'
        unmk = unfin = None
    else:
        sp = projs('σ0', len(Kc))
        xs = [p for p, k in zip(sp, kc) if k == 'V']
        S_ = [p for p, k in zip(sp, kc) if k == 'S'][0]
        A_ = [p for p, k in zip(sp, kc) if k == 'A']
        bp = projs('b', len(Kd))
        ys = [p for p, k in zip(bp, kd) if k == 'V']
        Sb = [p for p, k in zip(bp, kd) if k == 'S'][0]
        Ab = [p for p, k in zip(bp, kd) if k == 'A']
        if mode == 'S':
            unmk = f'(fun (σ0 : {tc}) => ({tup(xs)}, {S_}))'
            unfin = f'(fun (b : {td}) => ({tup(ys)}, {Sb}))'
            shapeB = f'cfIn {unmk} {unfin} aA'
        else:
            unmk = f'(fun (σ0 : {tc}) => ({tup(xs)}, {S_}, {A_[0]}))'
            unfin = f'(fun (b : {td}) => ({tup(ys)}, {Sb}, {Ab[0]}))'
            shapeB = f'cfInA {unmk} {unfin}'
    out.append(f'@[reif_simps] theorem R.{B.name}_eq {binders(B)} (sS : S) (aA : A) :')
    out.append(f'    interp mS mA (R.{B.name} {argnames(B)}) sS aA =')
    out.append(f'      ({aeneas_call(B)} >>= {shapeB}) := by')
    out.append(f'  unfold R.{B.name}')
    out.append(f'  simp only [reif_simps, fl4_core.{B.name}]')
    out.extend(proof_loop(ctx))
    out.append('')
    emit_nz(B, ctx, out)
    # measure
    mu, dec_proof = MEASURE.get(L.name) or default_measure([p for p in nonst if p not in lvars], lvars)
    mfun = f'(fun xL => {mu})'
    decb = ' '.join(f'({n} : {ty})' for n, ty in bps)
    out.append(f'/-- The measure of `{L.name}` drops at every `cont` step, on every store. -/')
    out.append(f'theorem R.{B.name}_dec {decb} {{σ0}}')
    out.append(f'    (h : {aeneas_call(B, own=True)} = ok (.cont σ0)) :')
    lhs = f'{mfun} σ0' if mode == 'R' else f'{mfun} ({unmk} σ0).1'
    out.append(f'    {lhs} < {mfun} {tup(lvn)} := by')
    out.append(f'  simp only [fl4_core.{B.name}] at h')
    out.extend('  ' + l for l in dec_proof.strip('\n').split('\n'))
    out.append('')
    # tree loop
    xmap = dict(zip(lvn, xp))
    treeargs = ' '.join(xmap.get(n, n) for n, ty, _ in B.params if not dropped(ty))
    bodyP = f'(fun xL => R.{B.name} {treeargs})'
    G.text = L.body
    ltoks = tokenize(L.body)
    assert ltoks[0].t == 'loop', L.name
    lgroups = call_args(ltoks[1:])
    assert len(lgroups) == 2, lgroups
    icomps = split_top(strip_parens(lgroups[1]), ',')
    if mode == 'R':
        init = icomps
    else:
        assert len(icomps) == len(kc), (icomps, kc)
        init = [c for c, k in zip(icomps, kc) if k == 'V']
    assert len(init) == nx, (init, nx)
    x0 = tup(init)
    out.append(f'@[irreducible] noncomputable def R.{L.name} {binders(L)} : SProg {vy} :=')
    out.append(f'  SProg.iter {bodyP} ({mfun} {x0} + 1) {x0}')
    out.append('')
    K = ret_kinds(L.ret)
    out.append(f'@[reif_simps] theorem R.{L.name}_eq {binders(L)} (sS : S) (aA : A) :')
    out.append(f'    interp mS mA (R.{L.name} {argnames(L)}) sS aA =')
    out.append(f'      ({aeneas_call(L)} >>= {shape(K)}) := by')
    out.append(f'  unfold R.{L.name} fl4_core.{L.name}')
    decargs = lambda sv, av: ' '.join(xmap.get(n, sv if ty == 'S' else av if ty == 'A' else n) for n, ty in bps)
    if mode == 'R':
        sp = projs('σ0', nx)
        smap = dict(zip(lvn, sp))
        aargs = ' '.join({'machine.Store S': 'mS', 'machine.Arch A': 'mA', 'S': 'sS', 'A': 'aA'}.get(ty, smap.get(n, n))
                         for n, ty, _ in B.params)
        bodyA = f'(fun (σ0 : {tc}) => fl4_core.{B.name} {aargs})'
        out.append(f'  exact interp_iterR mS mA {bodyA} {bodyP} {mfun} sS')
        out.append(f'    (fun xL aL => R.{B.name}_eq mS mA {treeargs} sS aL)')
        out.append(f'    (fun xL cL h => R.{B.name}_dec {sta} {decargs("sS", "aA")} h) _ _ _ (Nat.lt_succ_self _)')
    else:
        smap = {}
        vi = iter(xs)
        sp_all = projs('σ0', len(Kc))
        for (n, ty) in bps:
            pass
        # Aeneas body args from σ0: S param -> S_, A param -> A_, loop vars -> V projections
        vproj = dict(zip(lvn, [p for p, k in zip(sp_all, kc) if k == 'V']))
        aargs = ' '.join({'machine.Store S': 'mS', 'machine.Arch A': 'mA', 'S': S_, 'A': (A_[0] if A_ else 'a')}.get(ty, vproj.get(n, n))
                         for n, ty, _ in B.params)
        bodyA = f'(fun (σ0 : {tc}) => fl4_core.{B.name} {aargs})'
        mkt = [('sL' if k == 'S' else 'aL' if k == 'A' else None) for k in kc]
        xi = iter(xp)
        mkt = [m if m else next(xi) for m in mkt]
        if mode == 'S':
            mk = f'(fun (xL : {vx}) (sL : S) => {tup(mkt)})'
            out.append(f'  exact interp_iterS mS mA {bodyA} {bodyP} {mk} {unmk} {unfin} {mfun} (fun _ => rfl)')
            out.append(f'    (fun xL sL aL => R.{B.name}_eq mS mA {treeargs} sL aL)')
            out.append(f'    (fun xL sL cL h => R.{B.name}_dec {sta} {decargs("sL", "aL")} h) _ _ _ _ (Nat.lt_succ_self _)')
        else:
            mk = f'(fun (xL : {vx}) (sL : S) (aL : A) => {tup(mkt)})'
            out.append(f'  exact interp_iterSA mS mA {bodyA} {bodyP} {mk} {unmk} {unfin} {mfun} (fun _ => rfl)')
            out.append(f'    (fun xL sL aL => R.{B.name}_eq mS mA {treeargs} sL aL)')
            out.append(f'    (fun xL sL aL cL h => R.{B.name}_dec {sta} {decargs("sL", "aL")} h) _ _ _ _ (Nat.lt_succ_self _)')
    out.append('')
    out.append(f'@[reif_nz] theorem R.{L.name}_nz {binders(L)} : NoZero (R.{L.name} {argnames(L)}) := by')
    out.append(f'  unfold R.{L.name}')
    nb = len([1 for n, ty, _ in B.params if not dropped(ty)])
    out.append(f'  exact NoZero.iter (fun x => R.{B.name}_nz {" ".join("_" for _ in range(nb))}) _ _')
    out.append('')
    ctx.callees.add(B.name)
    return ctx


def x0b(lvars):
    return ', '.join(n for n, _ in lvars)


# ---------------------------------------------------------------- closure / order
def deps(name):
    f = FUNCS[name]
    toks = set(re.findall(r'[\w.]+', f.body))
    ds = {t for t in toks if t in FUNCS and FUNCS[t].eff and t != name}
    if is_loop(f):
        ds.add(name + '.body')
    return ds


def closure(roots):
    seen = set()
    st = list(roots)
    while st:
        n = st.pop()
        if n in seen:
            continue
        seen.add(n)
        st.extend(deps(n))
    return seen


def levels(names):
    lv = {}

    def ds(n):
        d = set(deps(n))
        if is_loop(FUNCS[n]):
            d |= deps(n + '.body')
        return {x for x in d if x in names}

    def L(n):
        if n not in lv:
            lv[n] = 0
            lv[n] = 1 + max([L(d) for d in ds(n)] or [-1])
        return lv[n]
    for n in names:
        L(n)
    return lv


def pure_heads(texts):
    heads = set()
    for t in texts:
        w = t.split()[0]
        if w in FUNCS and not FUNCS[w].eff:
            heads.add(w)
    return heads


DEC_DEFAULT = """dec_peel
all_goals (try simp only at *)
all_goals first
  | (apply ge_sub1_lt <;> assumption)
  | (apply ge_sub1_lt' <;> assumption)
  | (apply uadd_lt <;> first | assumption | scalar_tac)"""

SCALAR_BITS = {'Std.U64': '2 ^ UScalarTy.U64.numBits', 'U64': '2 ^ UScalarTy.U64.numBits',
               'Std.Usize': '2 ^ UScalarTy.Usize.numBits', 'Usize': '2 ^ UScalarTy.Usize.numBits',
               'Std.U32': '2 ^ UScalarTy.U32.numBits'}


def default_measure(fixed, lvars):
    n = len(lvars)
    xp = projs('xL', n)
    for (v, ty), x in zip(lvars, xp):
        if 'fuel' in v:
            return f'{x}.val', DEC_DEFAULT
    for (v, ty), x in zip(lvars, xp):
        if v in ('i', 'j', 'visits', 'idx', 'k') and ty in SCALAR_BITS:
            return f'{SCALAR_BITS[ty]} - {x}.val', DEC_DEFAULT
    return 'MISSING_MEASURE', 'sorry_missing'


PRELUDE = """/-
# P2: generated program trees, part {part} of `{prefix}` (line hpzg)

GENERATED by `xtask/scripts/gen_prog.py {args}`; do not edit. For each Store/Arch-generic function `f` of
the call closure: the tree `R.f` (the body with the store / Arch threading removed), its equation `R.f_eq`
(`interp` of the tree is `f` followed by `ok` of the threaded state, on every store and Arch instance) and
`R.f_nz` (`NoZero`). Loops: `R.<loop>.body` with its equation, the measure lemma `_dec`, the wrapper through
`interp_iterS`. No premises.
-/
{imports}
open Aeneas Aeneas.Std Result

set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Fl4Proofs.P2.PathObl
open fl4_core

section
variable {{S : Type}} {{A : Type}} (mS : machine.Store S) (mA : machine.Arch A)

"""
POST = """end

end Fl4Proofs.P2.PathObl
"""


def nd_lemmas(heads):
    out = []
    for h in sorted(heads):
        if h not in P0NAMES:
            out.append(f'-- no P0 lemma for {h}')
            continue
        f = FUNCS[h]
        b = ' '.join(f'({n} : {ty})' for n, ty, _ in f.params)
        a = ' '.join(n for n, _, _ in f.params)
        out.append(f'@[reif_simps] theorem nd.{h} {b} : fl4_core.{h} {a} ≠ div :=')
        out.append(f'  ne_div_of_spec (Fl4Proofs.P0.{h}.p0 {a})')
        out.append('')
    return out


INSTRE = re.compile(r'core\.cmp\.PartialEq\.ne\.trait_default\s+([\w.]+)')


def inst_lemmas(insts):
    out = []
    for i in sorted(insts):
        typ = i.split('.Insts.')[0]
        out.append(f'@[reif_simps] theorem nd.{i}.ne (x y : {typ}) :')
        out.append(f'    core.cmp.PartialEq.ne.trait_default {i} x y ≠ div :=')
        out.append(f'  nd_ne_default _ x y (fun x y => ne_div_of_spec (Fl4Proofs.P0.{i}.eq.p0 x y))')
        out.append('')
    return out


def main():
    prefix = sys.argv[1]
    roots = sys.argv[2:]
    names = closure(roots)
    names = {n for n in names if not n.endswith('.body')}
    lv = levels(names)
    order = sorted(names, key=lambda n: (lv[n], n))
    # generate per function
    chunks = []  # (name, level, lines, purestrings)
    for n in order:
        f = FUNCS[n]
        out = []
        ctx = gen_loop(f, out) if is_loop(f) else gen_fn(f, out)
        chunks.append((n, lv[n], out, ctx.pure))
    # nd lemmas: all pure heads in all chunks
    heads, insts = set(), set()
    for _, _, _, pure in chunks:
        heads |= pure_heads(pure)
        for t in pure:
            insts |= set(INSTRE.findall(t))
    ndl = nd_lemmas(heads) + inst_lemmas(insts)
    # split into files of ~LIMIT lines, respecting level order
    LIMIT = int(os.environ.get('GEN_LIMIT', '400'))
    files = [[]]
    size = 0
    for c in chunks:
        big = len(c[2]) > LIMIT // 2
        if files[-1] and (size > LIMIT or big):
            files.append([])
            size = 0
        files[-1].append(c)
        size += len(c[2])
        if big:
            size = LIMIT + 1
    import glob
    for old in glob.glob(os.path.join(OUTDIR, f'ProgGen{prefix}[0-9]*.lean')):
        os.remove(old)
    mods = []
    base = 'Fl4Proofs.P2.ProgGenBase'
    prev = None
    for k, fl in enumerate(files):
        mod = f'ProgGen{prefix}{k}'
        imports = f'import {prev}' if prev else f'import {base}'
        body = []
        if k == 0:
            body += ['/-! ## Pure steps never diverge (from P0) -/', ''] + ndl
        for n, _, out, _ in fl:
            body += out
        txt = PRELUDE.format(part=k, prefix=prefix, args=' '.join(sys.argv[1:]), imports=imports) + \
            '\n'.join(body) + '\n' + POST
        open(os.path.join(OUTDIR, mod + '.lean'), 'w').write(txt)
        mods.append(mod)
        prev = f'Fl4Proofs.P2.{mod}'
    top = f'ProgGen{prefix}Top'
    open(os.path.join(OUTDIR, top + '.lean'), 'w').write(
        f'/- GENERATED by `xtask/scripts/gen_prog.py {" ".join(sys.argv[1:])}`: all generated trees of `{prefix}`. -/\n'
        + ''.join(f'import Fl4Proofs.P2.{m}\n' for m in mods))
    mods.append(top)
    print(' '.join(f'Fl4Proofs.P2.{m}' for m in mods))
    print(len(order), 'functions,', sum(len(c[2]) for c in chunks), 'lines', file=sys.stderr)


if __name__ == '__main__':
    main()
