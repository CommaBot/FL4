import gzip,collections,re,sys,json
D='/Users/stillfail/.stillfail/sessions/claude-ember@d70ccd1321eaa3aa3390df77fb901ff2774a7cc3da926c3cf25ca287a3ba5f22/C0AQ0C0KVMH-1794890878-390829/workspace/station-back/col-dump/colback/'
def load(f):
    mod={};kind={};deps={}
    for line in gzip.open(D+f,'rt'):
        p=line.rstrip('\n').split('\t')
        n=p[0];mod[n]=p[1];kind[n]=p[2];deps[n]=p[3].split() if len(p)>3 and p[3] else []
    return mod,kind,deps
