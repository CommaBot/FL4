# p3J gen 30: the notification receive at a resumed entry, stable ghosts.
# Generates the body of P3/P3JSigSt.lean from XTopJointRecvSig's JAtZ.recvSigPollJ / JAtZ.recvSigActiveJ,
# XTopJointRecvSigBlock's JAtZ.recvSigBlockJ and XTopJointRecvSigRet's JAtZ.recvSigRetJ
# (proofs verbatim, post RelTopM ∧ JStab Z H Cs, final packaging adjusted).
import re, sys
P = sys.argv[1]
def block(src, start):
    i = next(k for k, l in enumerate(src) if l.startswith(start))
    j = i
    while src[j - 1].strip() != '':
        j -= 1
    k = i + 1
    while k < len(src) and not src[k].startswith(('set_option', '/--', 'theorem ', 'def ', 'end', 'section', 'variable')):
        k += 1
    while src[k - 1].strip() == '':
        k -= 1
    return '\n'.join(src[j:k])
NAMES = ['recvSigPollJ', 'recvSigActiveJ', 'recvSigBlockJ', 'recvSigRetJ']
def fix(body, n_final):
    for n in NAMES:
        body = re.sub(r'(?<![\w])JAtZ\.' + n + r'\b', 'JAtZ.' + n + 'St', body)
    c = body.count('RJ (L := L) arI AR r.1 r.2 z.2')
    assert c == 1, c
    body = body.replace('RJ (L := L) arI AR r.1 r.2 z.2',
                        'RelTopM (L := L) r.1 z.2 ∧ JStab (L := L) arI AR Z H Cs r.1 r.2 z.2')
    pat = re.compile(r'_, _, _, _, _, _, (J\d), inferInstance⟩')
    assert len(pat.findall(body)) == n_final, pat.findall(body)
    body = pat.sub(r'_, _, _, _, _, \1⟩', body)
    body = body.replace('/-- **', '/-- (p3J gen 30; stable ghosts, `JStab`) **')
    return body
def rd(f): return open(P + '/' + f).read().split('\n')
s1 = rd('XTopJointRecvSig.lean'); s2 = rd('XTopJointRecvSigBlock.lean'); s3 = rd('XTopJointRecvSigRet.lean')
b1 = fix(block(s1, 'theorem JAtZ.recvSigPollJ '), 1) + '\n\n' + fix(block(s1, 'theorem JAtZ.recvSigActiveJ '), 1)
b2 = fix(block(s2, 'theorem JAtZ.recvSigBlockJ '), 1)
b3 = fix(block(s3, 'theorem JAtZ.recvSigRetJ '), 1)
VAR1 = """variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}"""
VAR2 = VAR1 + " {s : S} {a : A} {σ : Fl4Spec.State Unit}"
def sec(opens, var, body):
    return "section\n" + opens + "\n" + var + "\n\n" + body + "\n\nend\n"
out = open(sys.argv[2]).read()
gen = (sec("open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched", VAR1, b1)
  + "\n" + sec("open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched Fl4Proofs.P1", VAR2, b2)
  + "\n" + sec("open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched", VAR2, b3))
assert '-- GENERATED --' in out
open(sys.argv[2], 'w').write(out.replace('-- GENERATED --', gen))
