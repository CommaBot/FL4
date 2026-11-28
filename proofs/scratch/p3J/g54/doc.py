import sys
P = ("\n(p3J gen 54) Each receive leaf ending in `RJR` / `RJ` here has a post-parametric form `…Q` (post\n"
     "`RelTopM ∧ Pq`, `Pq` from every `JAtZR` / `JAtZ` at `Z.mv G V` with the entry's `H`, `Cs` by `hPq`; the proof moved\n"
     "there); the original statement is unchanged and is its one-line instance. No new premises.\n")
for f in sys.argv[1:]:
    t = open(f).read()
    assert t.startswith('/-')
    i = t.index('\n-/\n')
    t = t[:i] + '\n' + P.rstrip('\n') + t[i:]
    open(f, 'w').write(t)
