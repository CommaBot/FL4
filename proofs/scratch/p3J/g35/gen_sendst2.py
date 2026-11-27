# p3J gen 35: P3/P3JSendSt.lean — jSendRest_ofSt (XTopJointSendPushD's jSendRest_of body verbatim, sub-leaves `…St`)
# and the hand-written stable send after the restart. Usage: gen_sendst2.py <proofs dir>
import sys, re
P = sys.argv[1] + '/Fl4Proofs/P3/'
src = open(P + 'XTopJointSendPushD.lean').read().split('\n')
i = next(k for k, l in enumerate(src) if l.startswith('theorem jSendRest_of '))
k = next(k for k in range(i + 1, len(src)) if src[k].startswith(('set_option', '/--', 'theorem ', 'end')))
while src[k - 1].strip() == '':
    k -= 1
body = src[i:k]
head = [l for l in body[:12]]
j = next(n for n, l in enumerate(body) if 'JSendRestHyp (L := L) arI AR s1 ar σ1 blk call b g gr don ct p := by' in l)
stmt = '\n'.join(body[:j]).replace('theorem jSendRest_of ', 'theorem jSendRest_ofSt ')
stmt += ('\n    JSendRestSt (L := L) arI AR Z H Cs s1 ar σ1 blk call b g gr don ct p := by')
rest = '\n'.join(body[j + 1:])
for n in ['sendRecvJ0', 'sendCallIJ', 'sendDonJ', 'sendCallPJ', 'sendCallPDJ']:
    rest = re.sub(r'(?<=\.)' + n + r'\b', n + 'St', rest)
tmpl = open(sys.argv[1] + '/scratch/p3J/g35/P3JSendSt.tmpl').read()
open(P + 'P3JSendSt.lean', 'w').write(tmpl.replace('@@JSENDREST@@', stmt + '\n' + rest))
