import re,sys
def cap(s):
    s=s.replace('untypedCap false','untypedCap true')
    s=re.sub(r'\bHU\b','HUD',s); s=re.sub(r'\bUtIn\b','UtInD',s); s=s.replace('utIn_','utInD_')
    s=re.sub(r'\bhu_','hd_',s); s=re.sub(r'\but_side\b','utd_side',s); s=re.sub(r'\bUtSet\b','UtSetD',s)
    s=s.replace('capOpt_default_noUt','capOpt_default_noUtD')
    s=s.replace('rv_fc_pure_ut','rv_fc_pure_utD').replace('rv_auto_ut','rv_auto_utD').replace('rv_finaliseCap_ut','rv_finaliseCap_utD')
    s=re.sub(r'\bzr_leaf\b','zd_leaf',s); s=re.sub(r'\bzr_auto\b','zd_auto',s)
    s=re.sub(r'\bik_zr\b','ik_zd',s); s=re.sub(r'\bike_zr\b','ike_zd',s)
    s=re.sub(r'\byk_leaf\b','ob_leaf',s)
    s=s.replace('(fun _ => ?_) (fun _ _ => ?_)','(fun _ => ?_) (fun _ => ?_)')
    s=s.replace('namespace Fl4Proofs.P3.SInvUZ','namespace Fl4Proofs.P3.SInvDV').replace('end Fl4Proofs.P3.SInvUZ','end Fl4Proofs.P3.SInvDV')
    return s
def full(s):
    s=cap(s)
    s=re.sub(r'fun _ _ => (ike_liftE |ike_liftE \()?yk_',lambda m:'fun _ => '+(m.group(1) or '')+'yk_',s)
    s=re.sub(r'fun D F => yk_','fun _ => yk_',s)
    s=re.sub(r'\bzr_split\b','zd_split',s)
    s=re.sub(r'\bZR\b','ZD',s); s=re.sub(r'\bZS\b','ZSD',s)
    s=re.sub(r'\bzrp_','zdp_',s); s=re.sub(r'\bzr_','zd_',s)
    s=re.sub(r'\byk_auto\b','ob_auto',s); s=re.sub(r'\byk_','ob_',s)
    s=re.sub(r'\bIKZE\b','IKDE',s); s=re.sub(r'\bIKZ\b','IKD',s)
    s=re.sub(r'\bikze_','ikde_',s); s=re.sub(r'\bikz_','ikd_',s)
    s=s.replace('PerfGapZ','PerfGapD').replace('perfGapZ','perfGapD')
    s=re.sub(r'\bkentry_zr','kentry_zd',s); s=re.sub(r'\bkcall_zr','kcall_zd',s)
    return s
