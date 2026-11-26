-- AArch64 port of Fl4Proofs.P2.ProgGenAttr (proofs/scratch/a64/port.py): the x86_64 text, re-checked
-- over Fl4CoreA64. Edits beyond the renaming are marked `-- a64:`.
/-
# P2: the simp set of the generated program trees (line hpzg)

`reif_simps`: the lemmas the generated `<f>_eq` proofs (`P2/ProgGen*.lean`) rewrite with: the `interp` /
`SProg` / `Result` normalisation (`P2/ProgGenBase.lean`), the leaf equations, every generated `_eq`, and the
non-divergence facts of pure steps (`interp_liftR`'s side condition); `reif_nz`: the `NoZero` facts of the
generated trees.
-/
import Fl4ProofsA64.P2.ProgReifyLeaf

register_simp_attr reif_simps

/-- The `NoZero` facts of the generated trees (`R.<f>_nz`, `AR.<m>_nz`). -/
register_simp_attr reif_nz
