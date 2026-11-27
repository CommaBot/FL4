# p3J gen 31: XTopJointRecvIpcLink's jRecvIpcU_of / jRecvIpcLink_of at stable ghosts (bodies of P3/P3JRecvSt.lean;
# the file's hand-written part holds `-- GENERATED --`). Usage: gen_recvst2.py <proofs dir> <target>
import re, sys
P = sys.argv[1] + '/Fl4Proofs/P3/'
sys.path.insert(0, sys.argv[1] + '/scratch/p3J')
STOP = ('set_option', '/--', 'theorem ', 'def ', 'end', 'section', 'variable', 'abbrev', 'lemma', 'private',
        'open', 'namespace', 'noncomputable', '@[', 'macro', 'instance', 'structure')
SUB = ['recvIpcActJ', 'recvIpcBlockJG', 'recvIpcBlockJ', 'recvIpcRetJ', 'recvIpcBlockNJG', 'recvIpcBlockNJ', 'recvSendFJG', 'recvSendJG',
       'recvSendJX', 'recvSendJ0X', 'recvSendRetJ', 'recvSendFPJG', 'recvSendPJG', 'recvSendP0X', 'recvSendRetPJ',
       'recvSendFPDJ', 'recvSendPDJ', 'recvSendRetPDJ', 'recvSendFTJ', 'recvSendFPTJ', 'recvSendT0X', 'recvSendRetTJ',
       'recvIpcPollJR', 'recvIpcPollJ', 'recvIpcPollNJ', 'jRecvIpcU_of', 'jRecvIpcLink_of']
RJ = 'RJ (L := L) arI AR r.1 r.2 z.2'
ST = 'RelTopM (L := L) r.1 z.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 z.2'
src = open(P + 'XTopJointRecvIpcLink.lean').read().split('\n')
def block(start):
    i = next(k for k, l in enumerate(src) if l.startswith(start))
    j = i
    while src[j - 1].strip() != '':
        j -= 1
    k = i + 1
    while k < len(src) and not src[k].startswith(STOP):
        k += 1
    while src[k - 1].strip() == '':
        k -= 1
    return '\n'.join(src[j:k])
out = []
for n in ['jRecvIpcU_of', 'jRecvIpcLink_of']:
    b = block('theorem ' + n + ' ')
    b = b.replace('theorem ' + n + ' ', 'theorem ' + n + 'St ')
    for m in SUB:
        b = re.sub(r'(?<=[.\s(])' + m + r'\b(?!St)', m + 'St', b)
    b = re.sub(r'theorem (\w+)StSt ', r'theorem \1St ', b)
    assert b.count(RJ) == 1, n
    b = b.replace(RJ, ST)
    b = b.replace('/-- ', '/-- (p3J gen 31; stable ghosts, `JStab`) ', 1)
    if n == 'jRecvIpcLink_of':
        old = '  exact jRecvIpcU_ofSt (Z := Z.mv Z.G V) '
        assert b.count(old) == 1
        b = b.replace(old, '  refine WP.spec_mono (jRecvIpcU_ofSt (Z := Z.mv Z.G V) ')
        assert b.endswith('(Or.inr ⟨q, g\', rfl, h0\'⟩)'), b[-60:]
        b = b + ') fun r ⟨z, hz, h1, h2⟩ => ⟨z, hz, h1, JStab.mv h2⟩'
    out.append(b)
t = open(sys.argv[2]).read()
assert '-- GENERATED --' in t
open(sys.argv[2], 'w').write(t.replace('-- GENERATED --', '\n\n'.join(out)))
