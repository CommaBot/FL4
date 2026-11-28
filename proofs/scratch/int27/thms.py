# List fully qualified (non-private) theorem names of the given modules: python3 thms.py [--tops] FILE...
# --tops: only serializable_* / kernel_entry* names (int27: kernel_entry*, so the kernel_entry_runMcWKR_* tops are in). Run in proofs/.
import re,sys
tops='--tops' in sys.argv
for f in [a for a in sys.argv[1:] if a!='--tops']:
  ns=[]
  for l in open(f):
    m=re.match(r'namespace\s+(\S+)',l)
    if m: ns.append(m.group(1)); continue
    m=re.match(r'end\s+(\S+)\s*$',l)
    if m and ns and ns[-1]==m.group(1): ns.pop(); continue
    m=re.match(r'(?:@\[[^\]]*\]\s*)?(?:protected\s+)?theorem\s+(\S+)',l)
    if m:
      n=m.group(1)
      if tops and not re.match(r'(serializable_|kernel_entry)',n.split('.')[-1]): continue
      # int26: a `_root_.` declaration ignores the enclosing namespaces
      print('#print axioms '+(n[7:] if n.startswith('_root_.') else '.'.join(ns+[n])))
