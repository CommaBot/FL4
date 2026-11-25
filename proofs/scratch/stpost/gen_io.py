# stpost gen 5: the IO port cap's leaves and the reply tails, stable ghosts.
# Generates P3/StPostIoLeaf.lean from XTopJointData / XTopJointReplyTail / XTopJointReply /
# XTopJointPortIn (proofs verbatim, post `JStab Z H Cs` instead of `JAt`, final packings adjusted).
# usage: python3 gen_io.py <proofs/Fl4Proofs/P3> <out.lean>
import re, sys
P = sys.argv[1]

def block(fname, start):
    src = open(P + '/' + fname).read().split('\n')
    i = next(k for k, l in enumerate(src) if l.startswith(start))
    j = i
    while src[j - 1].strip() != '':
        j -= 1
    k = i + 1
    while k < len(src) and not src[k].startswith(('set_option', '/--', 'theorem ', 'def ', 'end', 'section', 'variable', 'open ')):
        k += 1
    while src[k - 1].strip() == '':
        k -= 1
    return '\n'.join(src[j:k])

def rep(body, old, new, n=1):
    c = body.count(old)
    assert c == n, (old, c)
    return body.replace(old, new)

PACK = '(by first | exact {J}.stab | exact {J}.stab.mv | exact {J}.stab.mv.mv | exact {J}.stab.mv.mv.mv)'
def pk(J):
    return PACK.format(J=J)

JAT_POST = 'JAt (L := L) arI AR'
JST_POST = 'JStab (L := L) arI AR Z H Cs'

# --- replyTailJ (XTopJointData)
b1 = block('XTopJointData.lean', 'theorem JAtZ.replyTailJ ')
b1 = rep(b1, 'theorem JAtZ.replyTailJ ', 'theorem JAtZ.replyTailJSt ')
b1 = rep(b1, '∀ z ∈ (specTail true ct.bv ms σ0).1, JAt (L := L) arI AR s5 a z.2 ⦄',
         '∀ z ∈ (specTail true ct.bv ms σ0).1, JStab (L := L) arI AR Z H Cs s5 a z.2 ⦄')
b1 = rep(b1, 'exact ⟨_, _, _, _, _, _, J5, inferInstance⟩', 'exact ' + pk('J5'))

# --- flTailJ / replyErrJ / replyFailJ (XTopJointReplyTail)
b2 = block('XTopJointReplyTail.lean', 'theorem JAtZ.flTailJ ')
b2 = rep(b2, 'theorem JAtZ.flTailJ ', 'theorem JAtZ.flTailJSt ')
b2 = rep(b2, 'RelTopM (L := L) res.2.1 z.2 ∧ JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄',
         'RelTopM (L := L) res.2.1 z.2 ∧ JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 z.2 ⦄')
b2 = rep(b2, 'J2.xtop.relTop, _, _, _, _, _, _, J2, inferInstance⟩', 'J2.xtop.relTop, ' + pk('J2') + '⟩')
b2 = rep(b2, 'J0.replyTailJ ', 'J0.replyTailJSt ')
b2 = rep(b2, 'obtain ⟨Z5, H5, Cs5, Ac5, Lst5, D5, J5, _⟩ := hJ', 'obtain ⟨G5, V5, Ac5, Lst5, D5, J5⟩ := hJ')
b2 = rep(b2, 'J5.xtop.relTop, Z5, H5, Cs5, Ac5, Lst5, D5, J5, inferInstance⟩', 'J5.xtop.relTop, G5, V5, Ac5, Lst5, D5, J5⟩')
b2 = rep(b2, 'J.xtop.relTop, Z, H, Cs, Ac, Lst, D, J, inferInstance⟩', 'J.xtop.relTop, J.stab⟩')

b3 = block('XTopJointReplyTail.lean', 'theorem JAtZ.replyErrJ ')
b3 = rep(b3, 'theorem JAtZ.replyErrJ ', 'theorem JAtZ.replyErrJSt ')
b3 = rep(b3, 'RelTopM (L := L) s2 z.2 ∧ JAt (L := L) arI AR s2 a z.2 ⦄',
         'RelTopM (L := L) s2 z.2 ∧ JStab (L := L) arI AR Z H Cs s2 a z.2 ⦄')
b3 = rep(b3, '        JAt (L := L) arI AR s2 a (replyErrState', '        JStab (L := L) arI AR Z H Cs s2 a (replyErrState')
b3 = rep(b3, 'rintro s2 ⟨Z2, H2, Cs2, Ac2, Lst2, D2, J2, _⟩', 'rintro s2 ⟨G2, V2, Ac2, Lst2, D2, J2⟩')
b3 = rep(b3, 'J2.xtop.relTop, Z2, H2, Cs2, Ac2, Lst2, D2, J2, inferInstance⟩', 'J2.xtop.relTop, G2, V2, Ac2, Lst2, D2, J2⟩')
b3 = rep(b3, 'exact ⟨_, _, _, _, _, _, J4, inferInstance⟩', 'exact ' + pk('J4'))
b3 = rep(b3, 'exact ⟨_, _, _, _, _, _, J5, inferInstance⟩', 'exact ' + pk('J5'))

b4 = block('XTopJointReplyTail.lean', 'theorem JAtZ.replyFailJ ')
b4 = rep(b4, 'theorem JAtZ.replyFailJ ', 'theorem JAtZ.replyFailJSt ')
b4 = rep(b4, 'RelTopM (L := L) res.2.1 z.2 ∧ JAt (L := L) arI AR res.2.1 res.2.2 z.2 ⦄',
         'RelTopM (L := L) res.2.1 z.2 ∧ JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 z.2 ⦄')
b4 = rep(b4, 'J.xtop.relTop, Z, H, Cs, Ac, Lst, D, J, inferInstance⟩', 'J.xtop.relTop, J.stab⟩')
b4 = rep(b4, 'J.replyErrJ ', 'J.replyErrJSt ')

# --- reply1J (XTopJointReply)
b5 = block('XTopJointReply.lean', 'theorem JAtZ.reply1J ')
b5 = rep(b5, 'theorem JAtZ.reply1J ', 'theorem JAtZ.reply1JSt ')
b5 = rep(b5, '∀ z ∈ (specTail call ct.bv [v.bv] σ).1, JAt (L := L) arI AR s2 a z.2 ⦄',
         '∀ z ∈ (specTail call ct.bv [v.bv] σ).1, JStab (L := L) arI AR Z H Cs s2 a z.2 ⦄')
b5 = rep(b5, 'exact ⟨_, _, _, _, _, _, J2, inferInstance⟩', 'exact ' + pk('J2'))
b5 = rep(b5, 'exact ⟨_, _, _, _, _, _, J4, inferInstance⟩', 'exact ' + pk('J4'))

# --- XTopJointPortIn
b6 = block('XTopJointPortIn.lean', 'theorem portInTail_jat ')
b6 = rep(b6, 'theorem portInTail_jat ', 'theorem portInTail_jatSt ')
b6 = rep(b6, '\n    (hRep : JReplyHyp (L := L) arI AR Z.th) {s : S}', '\n    {s : S}')
b6 = rep(b6, '          JAt (L := L) arI AR res.2.1 res.2.2 w.2 ⦄', '          JStab (L := L) arI AR Z H Cs res.2.1 res.2.2 w.2 ⦄')
b6 = rep(b6, '  exact hRep Z\' H Cs Ac\' Lst\' D\' s1 a1 σy rfl J\' ct _ call v hcurY.symm hkY rfl s3 w heq hw hXT',
         '  have hctY : ct ∈ Z\'.T := J\'.thT ct (J\'.xtop.curTcb hcurY.symm).1\n'
         '  have hp := J\'.reply1JSt hctY hkY rfl call v\n'
         '  have heq\' : vspace.reply1 st s1 ct call v = ok s3 := by unfold vspace.reply1; exact heq\n'
         '  rw [heq\', WP.spec_ok] at hp\n'
         '  exact (hp w hw).mv')
b6 = b6.replace('/-- **', '/-- (stable ghosts, `JStab`) **')

b7 = block('XTopJointPortIn.lean', 'theorem decode_invocation_ioport_inJ ')
b7 = rep(b7, 'theorem decode_invocation_ioport_inJ ', 'theorem decode_invocation_ioport_inJSt ')
b7 = rep(b7, '\n    (hRep : JReplyHyp (L := L) arI AR Z.th) (s : S)', '\n    (s : S)')
b7 = rep(b7, 'DecOKRMX (L := L) arI (JAt (L := L) arI AR) s', 'DecOKRMX (L := L) arI (JStab (L := L) arI AR Z H Cs) s')
b7 = rep(b7, 'have hJ0 : JAt (L := L) arI AR s ar σ := ⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩',
         'have hJ0 : JStab (L := L) arI AR Z H Cs s ar σ := J.stab')
b7 = rep(b7, 'portInTail_jat arI hAM hJS hRep J', 'portInTail_jatSt arI hAM hJS J')

b8 = block('XTopJointPortIn.lean', 'theorem decode_invocation_ioportJ_steps ')
b8 = rep(b8, 'theorem decode_invocation_ioportJ_steps ', 'theorem decode_invocation_ioportJ_stepsSt ')
b8 = rep(b8, '\n    (hRep : JReplyHyp (L := L) arI AR Z.th) (hZB', '\n    (hZB')
b8 = rep(b8, 'XCap (L := L) arI (JAt (L := L) arI AR) s', 'XCap (L := L) arI (JStab (L := L) arI AR Z H Cs) s')
b8 = rep(b8, '⟨Z, H, Cs, Ac, Lst, D, J, inferInstance⟩ (fun _ _ _ h => Steps.jat arI hARI.toMask hJ h rfl J hZB) (fun _ _ _ h => JAt.xtop arI h)',
         'J.stab (fun _ _ _ h => by\n'
         '      obtain ⟨G\', V\', Ac\', Lst\', D\', J\', -⟩ := Steps.jatZ arI hARI.toMask hJ h rfl J hZB\n'
         '      exact ⟨G\', V\', Ac\', Lst\', D\', J\'⟩)\n'
         '    (fun _ _ _ h => by obtain ⟨_, _, _, _, _, J\'⟩ := h; exact ⟨_, J\'.xtop⟩)')
b8 = rep(b8, 'decode_invocation_ioport_inJ arI hARI.toMask hJ hRep s', 'decode_invocation_ioport_inJSt arI hARI.toMask hJ s')
b8 = b8.replace('/-- **', '/-- (stable ghosts, `JStab`) **')

for b in (b1, b2, b3, b4, b5, b7):
    pass
def tag(b):
    return b.replace('/-- **', '/-- (stable ghosts, `JStab`) **', 1) if '(stable ghosts' not in b else b
b1, b2, b3, b4, b5, b7 = map(tag, (b1, b2, b3, b4, b5, b7))

VAR_IMPL = """variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} {arI : machine.Arch A}
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64} {s : S} {a : A} {σ : Fl4Spec.State Unit}"""
VAR_EXPL = """variable {S : Type} {st : machine.Store S} [L : P1.LawfulStore st] {A : Type} (arI : machine.Arch A)
variable {AR : A → Fl4Spec.Cr3 → Prop} {Z : XSets} {H : P1.Heap} {Cs Ac : Set U64}
  {Lst : U64 → List U64} {D : Set U64}"""
OPEN_T = 'open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched'
OPEN_R = 'open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P1 Fl4Proofs.P3.Notif Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc Fl4Proofs.P3.Sched'
OPEN_P = 'open fl4_core Classical Fl4Proofs.P3.Vs Fl4Proofs.P3.Endp Fl4Proofs.P3.Ipc'

def sec(name, opn, var, blocks):
    return 'section %s\n%s\n%s\n\n%s\n\nend %s\n' % (name, opn, var, '\n\n'.join(blocks), name)

head = """/-
P3 (line stpost, generation 5): **the IO port cap's leaves and the reply tails with the stable-ghost
post** (generated by `scratch/stpost/gen_io.py`).

XTopJointData's `JAtZ.replyTailJ`, XTopJointReplyTail's `JAtZ.flTailJ` / `replyErrJ` / `replyFailJ`,
XTopJointReply's `JAtZ.reply1J` and XTopJointPortIn's `portInTail_jat` /
`decode_invocation_ioport_inJ` / `decode_invocation_ioportJ_steps` end in `JAt` (existential ghosts),
but every step inside keeps the entry's `H` and `Cs` and moves only the MDB ghost / VSpace sets
(`regWrJ`, `runJ`, `userWrJ`, `setmrJ`: `Z.mv Z.G V`; the primitive steps `Steps.jatZ`: `Z.mv G' V'`).
This file is those proofs verbatim, named `…St`, with the post `JStab Z H Cs` (StPostFault) and the
final packings adjusted (`J.stab` / `JStab.mv`). The IO port chain no longer takes the reply step
`JReplyHyp` as a premise: `portInTail_jatSt` closes it by `JAtZ.reply1JSt`. No premise added.
-/
import Fl4Proofs.P3.StPostInv
import Fl4Proofs.P3.XTopJointReplyTail
open Aeneas Aeneas.Std Result

namespace Fl4Proofs.P3

noncomputable section

"""
tail = """
end

end Fl4Proofs.P3
"""
out = head + sec('StIoA', OPEN_R, VAR_IMPL, [b5]) + '\n' + sec('StIoB', OPEN_T, VAR_IMPL, [b1, b2, b3, b4]) + '\n' + \
    sec('StIoC', OPEN_P, VAR_EXPL, [b6, b7, b8]) + tail
open(sys.argv[2], 'w').write(out)
