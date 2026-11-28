/-
P1 (aarch64): the shared tactic `copT` for the arch-only steps (TLB / cache maintenance and pure steps) before a
descriptor or leaf write: each such step is total. Used by QueueDecVs (`install_page`) and QueueS2Map
(`install_s2_leaf`). Unhygienic: it names `hA : P0.ArchTotal ar` and the lemmas `WP.spec_ok`, `WP.spec_bind`,
`shl_and63u`, `P0.layout.paddr.p0` as resolved at the use site.
-/

namespace Fl4ProofsA64.P1

set_option hygiene false in
/-- The arch-only steps (cache maintenance and pure steps) before a descriptor write are total. -/
macro "copT" : tactic => `(tactic| (repeat' (first
  | exact (WP.spec_ok _).2 trivial
  | exact hA.cache_op _ _ _ _ _ _ _
  | (refine WP.spec_bind (shl_and63u _) fun _ _ => ?_)
  | (refine WP.spec_bind (P0.layout.paddr.p0 _) fun _ _ => ?_)
  | (refine WP.spec_bind (Pₘ := fun _ => True) ?_ fun _ _ => ?_)
  | split)))

end Fl4ProofsA64.P1
