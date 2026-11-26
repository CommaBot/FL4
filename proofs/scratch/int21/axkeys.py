# axkeys.py LOG: print the axiom line of each requested top (int21). Run anywhere.
import re,sys
t=open(sys.argv[1],errors='replace').read(); t=t[t.rfind('\nAX '):] if '\nAX ' in t else t; t=re.sub(r'\n(?=\s)',' ',t)
names=['serializable_fl4_localVX8','serializable_fl4_localVX9','serializable_fl4_localVX10','serializable_fl4_localVX11',
 'serializable_fl4_localU3b','serializable_fl4_localU6','serializable_fl4_localU7','serializable_fl4_localU5Ho',
 'serializable_fl4_localU6of7','serializable_fl4_localU5Ho7','kernel_entry_reachU33','kernel_entry_reachU34',
 'kernel_entry_reachU32_of33','jAtZ_w0','jAt_w0','jReachU17_w0','jReachU34_w0','jReachU34_w0I','u34_w0I',
 'Fl4ProofsQ.P3.SInvR.G5.kernel_entry_reachU32']
for n in names:
  m=re.findall(r"(?m)^'([^']*\.%s)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)"%re.escape(n),t)
  print(n, m if m else 'MISSING')
