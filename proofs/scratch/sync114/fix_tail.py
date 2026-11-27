# s114: add #114's `in_release_queue` guard to the verbatim send_signal RunningVM tail in helper lemmas, and step it.
import sys,re
OLD_LIT = """              if b6 = true then do
                let s5 ← sporadic.unblock_check st s3 i4
                ok (s5, a1)
              else ok (s3, a1)
"""
NEW_LIT = """              if b6 = true then do
                let b7 ← sched.in_release_queue st s3 i
                if b7 = true then ok (s3, a1)
                else do
                  let s5 ← sporadic.unblock_check st s3 i4
                  ok (s5, a1)
              else ok (s3, a1)
"""
OLD_PF = """  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
"""
NEW_PF = """  step with sc_ne.spec as ⟨b6⟩
  refine sig_if _ _ _ _ (fun _ => ?_) (fun _ => ok3)
  refine WP.spec_bind (sched.in_release_queue.spec s3 i) fun b7 _ => ?_
  refine sig_if _ _ _ _ (fun _ => ok3) (fun _ => ?_)
"""
for p in sys.argv[1:]:
  t=open(p).read(); a=t.count(OLD_LIT); b=t.count(OLD_PF)
  t=t.replace(OLD_LIT,NEW_LIT).replace(OLD_PF,NEW_PF); open(p,'w').write(t); print(p,'lit',a,'pf',b)
