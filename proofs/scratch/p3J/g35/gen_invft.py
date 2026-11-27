# p3J gen 35: P3/P3JInvFt.lean. P1 QueueInvAll's `error_mrs.xs` / `reply_error.xs` re-run over P2 XferN's `XSFC`
# (lemma names `….xs` -> `….xsfc`, `set_mr_last` -> `set_mr_lastFC`, the buffer from `NoBufCap` in place of
# `XferHyps.buf`), then the Mc glue (hand-written tail). Usage: gen_invft.py <proofs dir>
import sys
P = sys.argv[1]
src = open(P + '/Fl4Proofs/P1/QueueInvAll.lean').read().split('\n')
def grab(start, stop):
    i = next(k for k, l in enumerate(src) if l.startswith(start))
    j = next(k for k in range(i + 1, len(src)) if src[k].startswith(stop))
    while src[j - 1].strip() == '' or src[j - 1].startswith('/--'):
        j -= 1
    return '\n'.join(src[i:j])
smr = grab('set_option hygiene false in', 'theorem syscall.error_mrs.xs')
emr = grab('theorem syscall.error_mrs.xs', '/-- **An endpoint send')
rer = grab('theorem syscall.reply_error.xs', '/-- `XS` from `BXI`')
XS = 'XS st T Cs Ω H Sg Rp Scs Nt Z U Ac X Q R s0'
XC = 'XSFC st T Cs Ω H Sg Rp Scs Nt Z U RS Ac X Q R s0'
def sub(t):
    t = t.replace(XS, XC)
    for a in ['msg.set_mr', 'faults.set_mrs_lookup_failure', 'obj.Tcb.set_reg', 'msg.buf_set', 'syscall.error_mrs']:
        t = t.replace(a + '.xs ', a + '.xsfc ')
    t = t.replace('set_mr_last ', 'set_mr_lastFC ')
    return t
smr = sub(smr).replace('local macro "smr"', 'local macro "smrC"')
emr = sub(emr).replace('theorem syscall.error_mrs.xsfc ', 'theorem syscall.error_mrs.xsfc ').replace('  · smr\n', '  · smrC\n').replace('    · smr\n', '    · smrC\n')
emr = emr.replace('theorem syscall.error_mrs.xs ', 'theorem syscall.error_mrs.xsfc ')
assert 'smr\n' not in emr.replace('smrC', ''), 'smr left'
rer = rer.replace('theorem syscall.reply_error.xs (E : XferHyps st T Cs Ω H Sg Rp Scs Nt Z U P3Ok) {s0 s : S} {t : U64}',
                  'theorem syscall.reply_error.xsfc {s0 s : S} {t : U64}')
rer = rer.replace('(hG : XG st T Cs Ω H Sg Scs Z P3Ok s) :', '(hN : NoBufCap (L := L) T s) :')
rer = rer.replace('refine WP.spec_bind (E.buf _ _ _ _ s t hG h.1 ht) fun buf hb => ?_',
                  'refine WP.spec_bind (Pₘ := fun b => BufOK U b) (by rw [lookup_ipc_buffer_noBuf hN ht true, WP.spec_ok]; exact fun h0 => (h0 rfl).elim) fun buf hb => ?_')
rer = sub(rer)
assert '.xs ' not in emr + rer and 'E.buf' not in rer, 'left'
tmpl = open(P + '/scratch/p3J/g35/P3JInvFt.tmpl').read()
open(P + '/Fl4Proofs/P3/P3JInvFt.lean', 'w').write(tmpl.replace('@@SMR@@', smr).replace('@@EMR@@', emr).replace('@@RER@@', rer))
