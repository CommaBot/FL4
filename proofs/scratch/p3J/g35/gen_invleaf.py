# p3J gen 35: P3/P3JInvLeaf.lean body: the mid decode leaves (gen 34's midDecEasy_of, midDecReply_ofE; gen 35's
# midDecEp_of) re-run for the invoking class (`InvDecStW`, flags `bl call don false` in place of
# `false false true true`). Usage: gen_invleaf.py <proofs dir>
import sys, re
P = sys.argv[1] + '/Fl4Proofs/P3/'
def grab(f, name):
    src = open(P + f).read().split('\n')
    i = next(k for k, l in enumerate(src) if l.startswith('theorem ' + name + ' '))
    j = i
    while not src[j].startswith('set_option'):
        j -= 1
    k = next(k for k in range(i + 1, len(src)) if src[k].startswith(('set_option', '/--', 'theorem ', 'end', 'def ')))
    while src[k - 1].strip() == '':
        k -= 1
    return '\n'.join(src[j:k])
def common(t, old, new):
    t = t.replace('theorem ' + old + ' ', 'theorem ' + new + ' ')
    t = t.replace('/-- (p3J gen 34)', '/-- (p3J gen 35; gen 34\'s `%s` for the invoking class)' % old)
    t = t.replace('/-- (p3J gen 35)', '/-- (p3J gen 35; `%s` for the invoking class)' % old)
    n0 = t.count('MidDecStW (L := L) arI AR MR')
    assert n0 == 1, (old, n0)
    t = t.replace('MidDecStW (L := L) arI AR MR', 'InvDecStW (L := L) arI AR MR')
    assert t.count('{c : Fl4Spec.Syscall}') == 1, old
    t = t.replace('{c : Fl4Spec.Syscall}', '{call bl don : Bool}')
    assert t.count(' Z H Cs s a σ n c := by') == 1, old
    t = t.replace(' Z H Cs s a σ n c := by', ' Z H Cs s a σ n call bl don := by')
    assert t.count('hRRb ct rg sr cr hct hn info') == 1, old
    t = t.replace('hRRb ct rg sr cr hct hn info', 'hRRb ct hct hn info')
    return t
out = []
out.append(common(grab('P3JMidNtfn.lean', 'midDecEasy_of'), 'midDecEasy_of', 'invDecEasy_of'))
out.append(common(grab('P3JReplyFtTop.lean', 'midDecReply_ofE'), 'midDecReply_ofE', 'invDecReply_of'))
ep = common(grab('P3JMidEp.lean', 'midDecEp_of'), 'midDecEp_of', 'invDecEp_of')
for a, b in [
    ('endpoint.send_ipc st arI s1 a\' false false b g gr true ct p', 'endpoint.send_ipc st arI s1 a\' bl call b g gr don ct p'),
    ('(Fl4Spec.sendIpc (Z := Unit) false false b.bv g gr true σ1.curThread', '(Fl4Spec.sendIpc (Z := Unit) bl call b.bv g gr don σ1.curThread'),
    ('have hdon : true = true →', 'have hdon : don = true →'),
    ('s1 a\' false false b g gr\n      true ct p', 's1 a\' bl call b g gr\n      don ct p'),
    ('hst1 hs1 false false g gr true)', 'hst1 hs1 bl call g gr don)')]:
    assert ep.count(a) == 1, a
    ep = ep.replace(a, b)
assert 'false false' not in ep and ' true ct p' not in ep, 'left flags'
out.append(ep)
tmpl = open(sys.argv[1] + '/scratch/p3J/g35/P3JInvLeaf.tmpl').read()
open(P + 'P3JInvLeaf.lean', 'w').write(tmpl.replace('@@LEAVES@@', '\n\n'.join(out)))
