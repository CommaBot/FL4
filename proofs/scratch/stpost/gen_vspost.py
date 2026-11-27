# stpost gen8: JAtZ.vsPostJSt = XTopJointVsMap's JAtZ.vsPostJ with post JStab Z H Cs.
# Writes /tmp/vspost_body.lean: the body of StPostInvLeaf.lean between its header and the decode section.
import re,sys
src=open('Fl4Proofs/P3/XTopJointVsMap.lean').read()
a=src.index('theorem JAtZ.vsPostJ ')
b=src.index('set_option maxHeartbeats 8000000 in\n/-- **`JAt` after a PML4 flush**')
body=src[a:b].rstrip()+'\n'
body=body.replace('theorem JAtZ.vsPostJ ','theorem JAtZ.vsPostJSt ',1)
old="(hV : VsJPost (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.G s ar σ s' a' σ') : JAt (L := L) arI AR s' a' σ' := by"
assert old in body
body=body.replace(old,"(hV : VsJPost (L := L) Z.th Z.P Z.L4 Z.L3 Z.L2 Z.L1 Z.G s ar σ s' a' σ') :\n    JStab (L := L) arI AR Z H Cs s' a' σ' := by")
o1="  · exact ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩\n"
assert body.count(o1)==1
body=body.replace(o1,"  · exact J.stab\n")
o2="  exact ⟨Z, H, Cs, Ac1, Lst1, D1, J', inferInstance⟩\n"
assert body.count(o2)==1
body=body.replace(o2,"  exact J'.stab\n")
open('/tmp/vspost_body.lean','w').write(body)
print(len(body.splitlines()))
