# common substitutions for the VM copies of the PageMap path (gen 17)
import re
NAMES=['pm_decRd','pm_decWalk','pm_s2','pmAccG','pmFinG','pm_blkG','pm_vsRd','pm_vsW_ioRS','pmRSU_ioRS',
       'pm_accU_of_blkG','pmAccG2','pm_mvG','pmAccN','pm_replyOnce','pm_tailOnce','pm_decOnce','pm_entOnce',
       'pm_roAG','pm_hufG','pm_huf','pm_pdwG','pmFinR','pm_accU_of_blk','pm_hufU','pm_pdwF','pmPreG_of',
       'pmEx_wr','pmRoot_wr','planMap_userWr','pageEntry_userWr']
def sub(t, extra=()):
    for a,b in extra: t=t.replace(a,b)
    t=t.replace('PmPreG st Cs Ω Sg Ac Locks','PmPreGX st Cs Ω Sg Ac Locks')
    t=t.replace('PmPreF st Cs Ω Sg Ac Locks','PmPreFX st Cs Ω Sg Ac Locks')
    t=t.replace('K.ptU','K.uV.ptU')
    t=t.replace('.ptU hG','.ptUX hG').replace('.ptU hE','.ptUX hE')
    t=t.replace('(VsW K.toKLayout b ∧ ¬ b ∈ K.ptes)','(VsW K.toKLayout b ∧ ¬ XD K b)')
    t=t.replace('fun b => VsW K.toKLayout b ∧ ¬ b ∈ K.ptes','fun b => VsW K.toKLayout b ∧ ¬ XD K b')
    t=t.replace('slJAt_slot0 hJ','hJ.hz').replace('invBufJ8_of hJ','hJ.here.1.buf8')
    for n in NAMES:
        t=re.sub(r'(?<![\w.])'+n+r'(?![\w\'])', n+'X', t)
    return t
