# Over-approximate call graph of an extracted function in proofs/Fl4Core/Funs.lean (token matching);
# lists the Store methods reachable. Usage: python3 proofs/scratch/callgraph.py syscall.handle_syscall_local
import re, sys
import os
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'Fl4Core', 'Funs.lean')).read()
defs = {m.group(1): m.start() for m in re.finditer(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|partial def)\s+([\w.]+)', src, re.M)}
names = sorted(defs, key=lambda n: defs[n]); starts = [defs[n] for n in names]
body = {n: src[starts[i]: starts[i + 1] if i + 1 < len(starts) else len(src)] for i, n in enumerate(names)}
seen, stack = set(), [sys.argv[1]]
while stack:
    n = stack.pop()
    if n in seen or n not in body: continue
    seen.add(n)
    stack += [t for t in set(re.findall(r'[\w.]+', body[n])) if t in body and t not in seen]
print(len(seen), 'defs reachable; Store methods:', sorted({m for n in seen for m in re.findall(r'machineStoreInst\.(\w+)', body[n])}))
