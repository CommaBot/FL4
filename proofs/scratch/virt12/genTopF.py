#!/usr/bin/env python3
"""Generate Fl4Spec/Ext/VirtKernelF.lean: the extended kernel's call chain with
FL4's report ops (Ext/VirtReport). Each definition is copied from its source
module with the renames below; run from proofs/."""
import re, sys
SRC = [
  ('Fl4Spec/Ext/VirtVcpu.lean', ['performVcpuInvocation']),
  ('Fl4Spec/Ext/VirtFinalise.lean', ['finaliseCapV', 'recDelFV', 'recDelV', 'capDeleteV', 'capRevokeFV',
      'capRevokeV', 'invokeCnodeV', 'installTcbCapV', 'installTcbFrameCapV', 'invokeTcbV', 'invokeSetEptRoot']),
  ('Fl4Spec/Ext/VirtEntry.lean', ['handleInterruptV', 'maybeHandleInterruptV', 'fl4TimerSignalV',
      'fl4TimerFireV', 'fl4AwakenV']),
  ('Fl4Spec/Ext/VirtDispatch.lean', ['fl4PerformInvocationV', 'fl4HandleInvocationV']),
  ('Fl4Spec/Ext/VirtKernel.lean', ['fl4HandleSyscallV', 'fl4HandleEventV', 'preemptionPathV',
      'fl4KernelExitV', 'fl4CallKernelV', 'fl4KernelEntrySyscallV', 'fl4VcpuExitV']),
]
# already defined in Ext/VirtReport
EXT = ['vcpuDetach', 'associateVcpuTcb', 'vmCheck', 'vmEnter', 'sendSignalV']
NAMES = EXT + [n for _, ns in SRC for n in ns]
ONCORE = set()  # names taking onCore

def extract(text, name):
    lines = text.split('\n')
    i = next(k for k, l in enumerate(lines) if re.match(r'def %s\b' % re.escape(name), l))
    j = i
    while j > 0 and not lines[j].startswith('/--'):
        j -= 1
    assert lines[j].startswith('/--'), name
    k = i + 1
    while k < len(lines) and not (lines[k].startswith('/--') or lines[k].startswith('def ')
                                  or lines[k].startswith('/-!') or lines[k] == 'end'
                                  or lines[k].startswith('structure ')):
        k += 1
    while lines[k - 1].strip() == '':
        k -= 1
    return lines[j:i], lines[i:k]

out = []
for f, ns in SRC:
    text = open(f).read()
    mod = f[len('Fl4Spec/'):-len('.lean')]
    for n in ns:
        doc, body = extract(text, n)
        if 'onCore' in body[0]:
            ONCORE.add(n)
        out.append((n, mod, doc, body))
ONCORE |= {'sendSignalV'}

def rename(s):
    for n in NAMES:
        s = re.sub(r'(?<![\w.])%s(?![\w\'])' % re.escape(n), n + 'F', s)
    s = s.replace('(onCore : ObjRef → Bool)', '(onCore remoteCur : ObjRef → Bool)')
    for n in ONCORE:
        s = re.sub(r'\b%sF onCore\b' % re.escape(n), n + 'F onCore remoteCur', s)
    return s

res = []
for n, mod, doc, body in out:
    d0 = doc[0][len('/--'):].lstrip()
    res.append('/-- `%s` (`%s`) with FL4\'s VMEnter report (`Ext/VirtReport`). Its docstring: %s' % (n, mod, d0))
    res.extend(doc[1:])
    res.extend(rename('\n'.join(body)).split('\n'))
    res.append('')
sys.stdout.write('\n'.join(res))
