# TIMER-RB-PLAN — the per-core timer red-black trees in P1 (jc6d)

Branch `par/jc6d` from 7f6784dd. Feeds KENTRY-PLAN jc6 (d): the `RegionUnrefAt` premise (C16 / C22 / C24) needs
"after `timer::remove(t)` (TCB finalise, objects.rs:341) no timer-tree word names `t`". P1's `TimerOK`
(QueueObjs:42) is typing only. Owner decision: the Rust stays as it is (`TREE_FUEL = 128` cut-offs included);
we prove the full red-black invariant, height bound included, so that no cut-off is ever reached.

## 0. The code (crates/fl4-core/src/timer.rs) and what the fuel needs

| loop | fuel | rounds needed in a red-black tree of height `h` |
|---|---|---|
| `insert` descent | `TREE_FUEL` = 128 | one per node on the root→leaf path: ≤ `h` (exhausted fuel with `cur ≠ 0` overwrites `p`'s child) |
| `insert_fixup` | 128 | each round moves `z` two levels up or ends: ≤ `(h+1)/2` |
| `remove` `TIMER_MIN` successor | 128 | ≤ `h − 2` left steps |
| `remove` successor `y` | 128 | ≤ `h − 2` left steps (exhausted fuel overwrites `y`'s parent's left child) |
| `remove_fixup` | 256 | each round moves `x` one level up or ends: ≤ `h` |

So `h ≤ 128` (nodes on the longest root–leaf path) is enough for every loop, and `h ≤ 128` follows from the
red-black shape alone: with black height `b` (black nodes per root–leaf path) and a black root, `h ≤ 2b`, and
`2^b ≤ n + 1`. **Bound on `n`:** tree nodes are distinct `u64` words, so `n ≤ 2^64`, hence `2^b ≤ 2^64 + 1`,
`b ≤ 64`, `h ≤ 128`. No memory-size argument is needed (with `TcbPlaced`, nodes are distinct non-zero multiples
of 4096, `n < 2^52`, `h ≤ 104`, which is the margin quoted in KENTRY-PLAN jc6; the proof uses the weaker,
assumption-free `2^64`). During `insert_fixup` the tree has one red–red edge at `z` but is otherwise
red-black with `n + 1 ≤ 2^64` nodes, so the same bound gives the depth of `z`.

Ties: `insert` goes left iff `deadline < cur.deadline`, so an equal deadline goes right, after the existing
equal ones. Rotations keep the in-order sequence. The order invariant is therefore **the in-order key list is
sorted non-strictly by deadline** (`List.Pairwise (≤)` on deadlines), not a strict BST.

## 1. The invariant (stage 1, `Fl4Proofs/P1/TimerRB.lean`)

Abstract-tree refinement (Okasaki / CLRS shape):

- `TRB.RBT` — `leaf | node (red : Bool) l (k : U64) r`; `keys` (in-order), `height`, `isRed`, `rootKey`
  (`0` for a leaf), `minKey = keys.headD 0`.
- `TRB.Bal t n` — black height `n`, no red node with a red child (inductive, CLRS properties 4–5).
- `TRB.Links` — the heap's link functions `l r p : U64 → U64` and `red : U64 → Bool`;
  `TRB.Rep k par x t` — the heap rooted at `x` with parent word `par` *is* `t`: `0` is a leaf; a non-zero `x`
  is `node (red x) l x r` with `p x = par`, `Rep x (l x) l`, `Rep x (r x) r`. This gives parent/child
  consistency both ways (a child's parent word is its parent).
- `lk st s` — the links at state `s`: `tlA`/`trA`/`tpA` words, red = `thA &&& 1 ≠ 0` (exactly `is_red`).
- `CoreTree st T s c t` (per core `c`): `Rep (lk s) 0 (TIMER_ROOT c) t`; `t.keys.Nodup`; keys ⊆ `T`; every key
  armed (`tdA ≠ 0`) and of core `c` (`thA >>> 8 = c`); in-order sorted by deadline; `Bal t n` for some `n`;
  black root; `TIMER_MIN c = t.minKey` (the leftmost node, `0` when empty).
- `TimerRB st T Cs s`: every `c ∈ Cs` has a `CoreTree`; every armed `y ∈ T` is a key of the tree of some
  `c ∈ Cs`; every unarmed `y ∈ T` (`tdA y = 0`) has null `tl`/`tr`/`tp` ("a removed TCB has null links").

Stage-1 consequences (proved):
- `TRB.Bal.height_le` (`h ≤ 2n + [red root]`), `TRB.Bal.pow_le` (`2^n ≤ |keys| + 1`),
  `TRB.height_le_128` (black root + `Nodup` keys ⇒ `h ≤ 128`); `CoreTree.height_le`.
- `TRB.Rep.det` (the tree is a function of the heap), `TRB.Rep.links` (every link of a key is `0`, the
  outer parent or a key of the same tree).
- `TimerRB.no_link` — "no link names a TCB outside the tree": for an unarmed `t ∈ T` (in particular `t`
  right after `timer::remove t`), no TCB's `tl`/`tr`/`tp`, no core's `TIMER_ROOT`/`TIMER_MIN` names `t`.
  This is the statement jc6 (d) needs, once `TimerRB` is carried.

## 2. Stages

| # | content | size | status |
|---|---|---|---|
| 1 | definitions above, pure height bound, `Rep` determinism/link lemmas, `TimerRB.no_link` | M | **done** |
| 2 | **done (2a frame `TimerRBFrame`, 2b reads `TimerRBRead`)**; frame: `TimerRB` / `CoreTree` kept by writes outside the timer words (`TW`) and by writes of `tbA` (badge), `REPROGRAM`; read specs: `timer.left/right/parent/root/is_red/core_of` on a key return the abstract child/parent/colour | M | |
| 3 | **3a done (`TimerRBZip`: `Ctx`, `CRep`, `rep_plug`, `rotL/rotR` keep keys); 3b done (`TimerRBWr`: writes as link updates); 3c open (`rotL_rep`, see §6)**; zipper: `Ctx` (path from the root: direction, parent key, colour, sibling subtree); `Rep` of `plug ctx t`; heap-level `rotate_left/right` at a node with context = abstract rotation (`Rep` re-established; keys order kept, so `sorted`, `Nodup`, membership and `minKey` follow from in-order equality); `replace_child`; `set_red` = recolour | L | |
| 4 | `insert` descent: loop invariant = `cur` is the root of the subtree at a context whose in-order position is the insertion point; `fuel ≥ height(subtree)` from `height_le_128` ⇒ the loop exits on `cur = 0`, never on `fuel = 0`; attach `t` red; `first` ⇔ `t` is the new `minKey` (`TIMER_MIN` update) | L | |
| 5 | `insert_fixup`: abstract invariant "red-black except a red–red edge between `z` and its parent" (CLRS 13.3 loop invariant) over the zipper, three cases × two sides; fuel `128 ≥ depth/2`; final root blackening | XL | |
| 6 | `remove` structural part: `TIMER_MIN` successor (in-order successor of the leftmost = next key), one-child splice and two-children successor transplant (`y` takes `t`'s place and colour), loops bounded by `height_le_128`; `t`'s links, height and deadline cleared ⇒ `idle` for `t` | XL | |
| 7 | `remove_fixup`: "doubly black at `x`" invariant (CLRS 13.4) with `x` possibly `0` identified by `p`; four cases × two sides; fuel `256 ≥ depth`; the null-`x` case uses black height (`x = 0` ⇒ sibling non-null) | XL | |
| 8 | composition: `timer.remove.rb`, `timer.insert.rb`, `timer.fire.rb` (loop of removes of `minKey`; `send_signal` frames by stage 2); `TF`-style footprint form so the existing `timer.remove.tf` callers can carry `TimerRB` | L | |
| 9 | plug-in: carry `TimerRB` next to `TimerOK` (`TInv`/`BlkOK` users: QueueTimerSet `timer.insert.tinv`, `thread_unbind_remove.blk`, QueueFire `timer.fire.tinv`, FastFinInv, QueueDecTcb / QueueFinThr finalise, retype of TCBs: new TCBs zeroed ⇒ `idle`); then jc6 (d)'s `DbgTimerKept` timer half from `TimerRB.no_link` | L–XL | |

Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2000, XL > 2000 (one agent-session each, roughly).

## 3. How each operation keeps the invariant (sketch for stages 3–8)

- Rotations: in-order unchanged ⇒ `Nodup`, `sorted`, keys, `minKey` unchanged; `Rep` re-established from the
  six link writes (`rotate_left`: `x.r := y.l`, `y.l.p := x`, `y.p := x.p`, `replace_child(x.p, x, y)`, `y.l := x`,
  `x.p := y`); colours untouched. The rotation is only applied in the fixups, where `Bal` is restated by case.
- Insert: descent places `t` at a leaf position whose in-order neighbours have deadlines `≤ d` on the left and
  `> d` on the right ⇒ sorted. Fixup = CLRS RB-INSERT-FIXUP (cases 1–3 mirrored); code differs only in
  re-checking the loop guard after case 2/3 (the parent is then black, the loop exits without spending fuel).
- Remove: CLRS RB-DELETE with pointer transplant (no key copy): `y` moves into `t`'s place, so other TCBs'
  identities are kept; `removed_red`/`x`/`x_parent` as in CLRS with `x = 0` allowed. `TIMER_MIN` is updated
  before the structural change to the in-order successor of `t` (`t` is the leftmost, so it has no left child;
  successor = leftmost of `t.r`, else `t.p`).
- Fire: each round removes `TIMER_MIN` of the current core (a key of that core's tree, so `core_of = cur_cpu`).

## 4. Existing P1 lemmas it plugs into

- `timer.remove.tf` / `timer.remove.tinv` (QueueTimer:694/792), `timer.remove.tf2`/`.csc` (QueueTimerC),
  `timer.insert.tinv`, `thread_unbind_remove.blk` (QueueTimerSet), `timer.fire.tinv`, `sched.schedule.tinv`,
  `EntryInv` (QueueFire), FastFinInv (fast-path `TIMER_MIN` read): all keep their statements; new `.rb`
  lemmas sit beside them with the same footprint (`TF`), and `TimerRB` is carried as a separate conjunct.
- `TimerOK` stays the typing invariant; `TimerRB` ⇒ the `lt/rt/pt/root/min` parts of `TimerOK` for keys.

## 5. Progress log

- Stage 1: `Fl4Proofs/P1/TimerRB.lean` (definitions, `height_le_128`, `Rep.det/links`, `TimerRB.no_link`,
  `links_tz`).
- Stage 2: `TimerRBFrame.lean` (`Rep.congr`, `TAgree`, `CoreTree.congr`, `TimerRB.congr/of_writesIn`, `root_tz`),
  `TimerRBRead.lean` (`timer.left/right/parent/is_red.links` value specs, `.rep` abstract forms, `timer.root.val`).
- Stage 3a: `TimerRBZip.lean` (`Ctx`, `plug`, `CRep`, `rep_plug`, `rotL`/`rotR`, `plug_rotL_keys`).
- Stage 3b: `TimerRBWr.lean` (`trb_fld_wr`, `trb_node_wr_fld`, `trb_fld_wr_node`, `trb_node_wr_node`, `lk_wr_tl/tr/tp`, `Rep.congr_on`).
- Full build green at the stage-3b commit (7307 jobs; stage-1–3a commit: 7305 jobs, 0 errors, 0 sorry; axioms propext/choice/Quot.sound).

## 6. Next step (exact)

- Stage 3b (`TimerRBWr.lean`, **done**): one-word writes as link updates — `trb_fld_wr`, `trb_node_wr_fld`, `trb_fld_wr_node`,
  `trb_node_wr_node`, `lk_wr_tl/tr/tp` (`LinksEqOn T (setL/R/P z v) (lk s')`), `Rep.congr_on`. Still to add:
  `lk_wr_red` (`set_red`'s `(h &&& ~~~1) ||| r` gives colour `r`, core bits kept by `shr8_red`), and the
  `timer.set_left/right/parent/set_red/set_root/replace_child` specs in this form (null `z` = no write).
- Stage 3c (pure, the core of the refinement): `rotL_rep` — from `Rep k 0 R (ctx.plug (node cx a x (node cy b y g)))`,
  `Nodup` keys, and `k'` = `k` updated exactly as `rotate_left` writes (`x.r := b.root`, `b.root.p := x` if
  non-null, `y.p := ctx.par`, the hole's link in `ctx.par` (or the root word) `:= y`, `y.l := x`, `x.p := y`),
  conclude `Rep k' 0 R' (ctx.plug (rotL …))`. Proof via `rep_plug`: `CRep` of `ctx` transfers by
  `Rep.congr_on` on the siblings (their keys miss `x, y, b.root` by `Nodup`) and by the one changed link at
  `ctx.par`; the rotated subtree is rebuilt with `Rep.node` from `Rep.congr` on `a`, `b` (parent changed only
  at its root), `g`. Mirror for `rotR_rep`. Then `timer.rotate_left.rb` = heap writes (3b) + `rotL_rep`.
  Suggested helpers for 3c: `Ctx.pre`/`Ctx.post` (top: `[]`,`[]`; `lc c k r up`: `up.pre`, `k :: r.keys ++ up.post`;
  `rc c l k up`: `up.pre ++ l.keys ++ [k]`, `up.post`) with `plug_keys_eq : (ctx.plug t).keys = ctx.pre ++ t.keys
  ++ ctx.post` and `ctx ≠ top → ctx.par ∈ ctx.pre ++ ctx.post`; `CRep.congr` (all links of `pre ++ post` equal ⇒
  same `CRep`) and `CRep.hole` (only `ctx.par`'s hole link changed, to `y`; `R' = y` at the top, else `R' = R`);
  disjointness of `t.keys` from `pre ++ post` from `List.nodup_append`.  State `k'` by hypotheses ("`k'` = `k` off
  `{x, y, b.root, ctx.par}`" + the exact values on those four), which is what 3b's `LinksEqOn` chains deliver.
- Then stage 4 (insert descent; uses `CoreTree.height_le` for the fuel).

## 7. Stage 3c progress and exact next step (second session)

- Done (`TimerRBRot.lean`, full build green 7309 jobs, 0 errors, 0 sorry): `Ctx.pre`/`Ctx.post`, `Ctx.plug_keys` (`(ctx.plug t).keys = ctx.pre ++ t.keys ++
  ctx.post`), `Ctx.par_mem`, `nd_sep` (two sides of a `Nodup` append are disjoint), `CRep.congr` (a path reads
  only `pre ++ post`), `HoleUpd` + `CRep.hole` (only the hole's link re-pointed to `y` ⇒ path kept, ending at `y`).
- Next, in this order:
  1. `Rep.keys_ne0 : Rep k p x t → ∀ z ∈ t.keys, z ≠ 0` (induction; needed for `z ≠ ctx.par` at the top, where
     `par = 0`).
  2. `rotL_rep` with hypotheses on `k'`: `ex` (x: `l` kept, `r = b.rootKey`, `p = y`, colour kept), `ey` (y:
     `l = x`, `r` kept, `p = ctx.par`, colour kept), `eb` (`b.rootKey ≠ 0 →` its `p = x`, rest kept), `eo` (any
     `z ≠ x, y`, `(b.rootKey ≠ 0 → z ≠ b.rootKey)`, `z ≠ ctx.par` keeps all four), `hu : HoleUpd k k' R R' ctx y`.
     Proof: `(rep_plug ctx _).1 h` → `hc`, `ht`; `cases ht` / `cases` its right child / `cases hb` (leaf or
     node); goal `show Rep k' 0 R' (ctx.plug (.node cy (.node cx a x b) y g))`, `(rep_plug ctx _).2 ⟨hc.hole …,
     .node …⟩`. Disjointness: rewrite `hd` with `Ctx.plug_keys`, take `hT : M.Nodup` for the middle
     `M = a.keys ++ x :: (b.keys ++ y :: g.keys)` by `hd.sublist ((List.sublist_append_right _ _).trans
     (List.sublist_append_left _ _))`, and get each `≠` from `nd_sep` / `List.nodup_cons` on `M`'s suffixes;
     `M` vs `pre ++ post` from `nd_sep` on `hd`. (Alternative: `List.Nodup` is `Pairwise (· ≠ ·)`; `simp only
     [List.pairwise_append, List.pairwise_cons, List.mem_append, List.mem_cons]` gives all facts as ∀s.)
  3. `rotR_rep` (mirror).
  4. `timer.rotate_left.rb`: walk the 6 writes of `timer.rotate_left` with `timer.left/right/parent.rep`,
     `lk_wr_tl/tr/tp` (3b) and `timer.replace_child` (its spec: `p = 0` writes `TIMER_ROOT` = top case of
     `HoleUpd`; else `left p == old` picks the side — `old = x` is `p`'s child, distinct from the other child by
     `Nodup`), composing the `LinksEqOn` updates into `ex/ey/eb/eo/hu`.
- Stage 3b rest (`lk_wr_red`) is only needed from stage 5 (fixups) on; rotations do not touch colours.

## 8. Third session (jc6d2): stage 3 done, stage 4 part 1 done; exact next step

- `TimerRBRotP.lean`: `Rep.keys_ne0`, `nd_mid`/`nd_out`/`nd_in` (Nodup of `P ++ M ++ Q`), `Rep.reparent` (only the
  root's parent word re-pointed), `Same`, **`rotL_rep`**, **`rotR_rep`** (hypotheses `ex/ey/eb/eo/hu` exactly as in §7).
- `TimerRBRotH.lean`: `@[simp]` projections of `Links.setL/setR/setP`; `LinksEqOn.trans/setL/setR/setP/setP_out`;
  `holeSet ctx y K` / `holeR ctx y R` (the hole's link := `y`, the root word at the top) with `holeSet_l_ne/r_ne/p/red`;
  `HoleL` (`replace_child`'s side test: `lc` ⇒ parent's left = old, `rc` ⇒ ≠ old) + `HoleL.congr`; `Rep.node_inv`;
  `mid_facts` (a subtree at a hole: keys ≠ `ctx.par`, ≠ 0, ⊆ the tree; `ctx ≠ top ⇒ par` a key, ≠ 0; `HoleL`; its `Rep`);
  `lk_wr_node`; **`RW st T s0 s c K R F`** = the walk state (links agree on `T` with the explicit `K`; root word `R`;
  `WritesIn s0 s F`; `NodePlaced`), `RW.init`, `RW.wr_tl/wr_tr/wr_tp/wr_root` (one write = one `Links.set*`);
  **`timer.replace_child.rw`** (= `holeSet`/`holeR`), `RotFoot`, **`timer.rotate_left.rep` / `timer.rotate_right.rep`**:
  from `Rep (lk s) 0 root (ctx.plug (node cx a x (node cy b y g)))` + Nodup + keys ⊆ `T`, the result state has
  `Rep (lk s') 0 root' (ctx.plug (rotL …))` and `WritesIn s s' (RotFoot s c x y b.rootKey ctx.par)` (links of
  `x, y, b.root, ctx.par` and the root word only; so deadlines, heights, `TIMER_MIN`, other trees are framed).
- `TimerRBRed.lean` (stage 3b rest): `Links.setRed` simp lemmas, `LinksEqOn.setRed`, `redW b`, `red_bit`, `red_of`,
  **`timer.set_red.on`** (`s' = wr s (thA z) ((h &&& ~~~1) ||| redW b)`), **`lk_wr_red`**, `core_wr_red` (core bits kept),
  `RW.wr_red`.
- `TimerRBIns.lean` (stage 4 part 1): `Dir`, `sorted_mid`, `DescOut`, `DescInv`, **`timer.insert_loop.desc`** (from
  `Rep (lk s) 0 R t`, sorted deadlines and `t.height ≤ fuel`: the loop returns `(p, go_left, first)` with a leaf
  hole `ctx` of `t`, `p = ctx.par`, `Dir ctx go_left`, `first ↔ ctx.pre = []`, deadlines `≤ d` before and `> d` after;
  the `fuel = 0` exit is shown unreachable), **`attach_rep`** (new red leaf at the hole), `attach_keys`
  (`pre ++ t0 :: post`), `attach_sorted`, `attach_min` (`minKey = if pre = [] then t0 else old minKey`, i.e. the
  `first` / `TIMER_MIN` update is right).
- Full build green at the stage-4-part-1 commit 6e69560b: `Build completed successfully (7317 jobs)`, 0 errors, 0 sorry;
  axioms propext/Classical.choice/Quot.sound for all new tops (axjc6d.lean list, not committed).

Next, in this order:
1. **Stage 4 rest (heap attach)**, as a lemma about `timer.insert` taking `timer.remove`'s spec as a hypothesis
   (`hrem : timer.remove st s t ⦃ s1 => P s1 ⦄`, `P` = `TimerRB` with `t` idle, i.e. not a key, null links) and
   `insert_fixup`'s spec as another hypothesis (stage 5): `cur_cpu`, `timer.root.val`, `timer.insert_loop.desc` with
   `f = layout.TREE_FUEL` (`layout.TREE_FUEL.val_eq : … = 128`, height from `CoreTree.height_le`), `is_null p`,
   `set_root` / `set_left` / `set_right` by `Dir` (= `RW.wr_root/wr_tl/wr_tr`, i.e. `holeSet ctx t K`), then the
   deadline and badge writes (need `lk_wr_td`/`lk_wr_tb`: `tdA`/`tbA` writes keep `lk` on `T`, from `trb_fld_wr`
   with offsets 3528 / badge offset), `set_parent t p`, `set_left t 0`, `set_right t 0` (`RW.wr_*`), height write
   `(cpu <<< 8) ||| 1` (red: `((x ||| 1) &&& 1) != 0`; core: `or1_shr8` + `shl8_shr8`, needs `cpu < 2^56`), then
   `attach_rep` with `k' = K` and `HoleUpd` from `holeSet` (lemma `holeSet_upd` by `cases ctx`), `attach_sorted`
   (deadline of `t` is `d` after the write; others unchanged), `attach_min` with `first`.
2. **Stage 5 (insert_fixup)**, pure first (new file `TimerRBFix.lean`): CLRS 13.3 invariant on the zipper:
   `W = ctx.plug (node true a z b)` with `Bal (node true a z b) n` (z red, children black) and a context predicate
   `IC ctx n` ("plugging a black-height-`n` tree whose root may be red gives a tree that is red-black except that a
   red root may sit under a red hole-parent"; inductive over `Ctx`, mirroring `Bal`), plus `Nodup`/sorted carried by
   in-order equality (`plug_rotL_keys`, recolouring keeps keys).  Cases 1 (uncle red: recolour p, u black, g red,
   `z := g`, ctx shrinks by 2), 2 (z inner child: `rotL` at p then case 3), 3 (`rotR` at g, recolour) × mirror; loop exit
   on black parent / null parent; final root blackening.  Fuel: each case-1 round removes two context levels; the
   context depth is ≤ height(W) ≤ 2·bh(W)+1 with `2^bh ≤ |keys|+1 ≤ 2^64+1` (same argument as `height_le_128`), so
   ≤ 65 rounds < 128 (the `fuel = 0` exit is unreachable).  Heap side: `timer.parent/left/right/is_red.rep` reads,
   `timer.set_red.on` + `RW.wr_red`, `timer.rotate_left/right.rep` (compose `RW` with their `WritesIn`/`Rep` via
   `Rep.det`), loop via `loop.spec_decr_nat` with measure `fuel`.
3. Stages 6–9 as in §2.
