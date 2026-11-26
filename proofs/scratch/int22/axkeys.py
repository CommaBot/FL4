# axkeys.py LOG: print the axiom line of each requested top (int22). Run anywhere.
import re,sys
t=open(sys.argv[1],errors='replace').read(); t=re.sub(r'\n(?=\s)',' ',t)
names=['kernel_entry_reachU35','kernel_entry_reachU34_of35','kernel_entry_reachU36','kernel_entry_reachU35_of36',
 'kernel_entry_reachU36I','kernel_entry_reachU34_of36I','serializable_fl4_localU8','serializable_fl4_localU7of8',
 'serializable_fl4_localU9','serializable_fl4_localU8of9','serializable_fl4_localU3c_of','serializable_U3c_of',
 'serializable_safeD','jAtZ_w1','jReachU17_w1','jReachU34_w1','jReachU34_w1I','u34_w1I','w1_nonIdle',
 'wit_U2_uncond','wit_U2_uncond\'','irqStB_false_of_ipiWord','idle2_not_sinvX','view_home_rd_unsafe',
 'u9_home_safe_iff','insTP_write_mapping','ioRSR_ptU_notPWE','fInitIpi_irqCarry',
 'Fl4ProofsJ.P3.SInvR.G5.kernel_entry_reachU35']
for n in names:
  m=re.findall(r"(?m)^'([^']*\.%s)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms)"%re.escape(n),t)
  print(n, m if m else 'MISSING')
