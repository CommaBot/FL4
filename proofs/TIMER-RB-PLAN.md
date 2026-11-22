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
| 4 | **done (`TimerRBIns`, `TimerRBInsH`)**; `insert` descent: loop invariant = `cur` is the root of the subtree at a context whose in-order position is the insertion point; `fuel ≥ height(subtree)` from `height_le_128` ⇒ the loop exits on `cur = 0`, never on `fuel = 0`; attach `t` red; `first` ⇔ `t` is the new `minKey` (`TIMER_MIN` update) | L | |
| 5 | **done (`TimerRBFix`, `TimerRBFixH`, `TimerRBFixL`; composed with 4 in `TimerRBInsC`)**; `insert_fixup`: abstract invariant "red-black except a red–red edge between `z` and its parent" (CLRS 13.3 loop invariant) over the zipper, three cases × two sides; fuel `128 ≥ depth/2`; final root blackening | XL | |
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

## 9. Fourth session (jc6d3 + jc6d4): stages 4 and 5 done

- `TimerRBInsH.lean` (af288688): **`timer.insert.attach`** (heap attach of `t` inside `timer.insert`, `remove`'s and
  `insert_fixup`'s specs as hypotheses `hrem`/`hfix`; result `InsMid` = `t` red at the hole, sorted, `t`'s core
  bits, writes in `InsFoot`; `TIMER_MIN`/`REPROGRAM` written exactly when `ctx.pre = []`); `lk_wr_oth`/`lk_wr_th`,
  `insFoot_not`.
- `TimerRBFix.lean` (pure): `Ctx.parRed`, `Ctx.blk` (black path nodes), **`CtxOK ctx n`** (path red-black for a
  black-height-`n` hole, red–red allowed only at the hole), `RootB`, `BalW`, `plug_balW`, **`plug_bal`**,
  `CtxOK.of_bal`, **`blk_le_64`** (`2^bh ≤ |keys|+1 ≤ 2^64+1`), `Rep.recolor`.
- `TimerRBFixH.lean`: walk state **`FB st T s0 c Ks s W`** (heap = `W` from the root word, keys `Ks` fixed,
  writes in `FixFoot` = links/height words of `Ks ∪ {0}` + root word, core bits kept, `NodePlaced`);
  `FB.set_red` (colour write = abstract recolour), `FB.rotL`/`FB.rotR` (heap rotations on `FB`).
- `TimerRBFixL.lean`: loop invariant `FixInv` = `FixA` (z red at a `CtxOK` hole, `RootB`, `ctx.blk + 1 ≤ fuel`)
  ∨ `FixB` (tree balanced, z's parent black/null, reached after a rotation case); case lemmas
  `fix_case1L/R`, `fix_case3L/R`, `fixA_exit`, `Bal.blacken`; heap rounds `fix_body_exit`, `fix_body_LL/RL/RR/LR`
  (+ shared tails `fix_tailL/R` after the optional inner rotation), `fix_body`; **`timer.insert_fixup_loop.rb`**
  (`loop.spec_decr_nat`, measure = fuel; the `fuel = 0` exit is refuted by `blk + 1 ≤ fuel`, and a recolour
  round removes one black path node, the grandparent); **`timer.insert_fixup.rb`** (from `t` red at a leaf hole
  of a black-root red-black tree: result `FB` with `Bal W n` and black root; initial `blk ≤ 64 < 128`).
- `TimerRBInsC.lean`: `FB.td`/`FB.min` (fixup writes no deadline / `TIMER_MIN`), `InsMid.np1/parT/th_old/min_old/
  keys_iff/nodup/inT`, `CoreTree.of_fix`, **`timer.insert.core`**: after `timer.insert s t d bd` with `d ≠ 0`, the
  current core has `CoreTree s' (cpu s1) W` with `W.keys = ctx.pre ++ t :: ctx.post` (old tree `ctx.plug leaf`).
- Finding: no reachable bad state found; the fuel argument works as planned (fixup rounds ≤ 65; descent ≤ 128).
- Full build green at d6693d4b: `Build completed successfully (7327 jobs)`, 0 errors, 0 sorry; axioms
  propext/Classical.choice/Quot.sound for all new tops (axjc6d.lean, not committed).

Next (exact):
1. Stage 8 for insert (frame part): `timer.insert` touches only `t`'s fields, the hole parent's child links,
   the fixup footprint (links/height words of the current tree's keys) and the current core's
   `TIMER_ROOT`/`TIMER_MIN`/`REPROGRAM`; from that, the other cores' `CoreTree`s are framed
   (`CoreTree.congr`/`TAgree`, they share no key with the current tree since a key's core bits name its core)
   and `TimerRB` after insert follows with `hrem` = `timer.remove`'s `.rb` spec (stage 6/7).  Needs a
   `WritesIn` footprint out of `timer.insert.core` (compose `InsMid.wi` with `FB.wi` and the two node writes).
2. Stages 6–7 (`remove` structural part, `remove_fixup`), then 8 (`fire`), 9 (plug-in), as in §2.

## 10. Fifth session (jc6d5): stage 8 insert part done, stage 6 (remove, structural part) done

- `TimerRBInsF.lean`: `XFoot T s0 X C` (writes in words of `X`-TCBs, the null TCB and core `C`'s node),
  `KeepOut` + `KeepOut.of_wi`, **`CoreTree.keep`** (a core's tree is framed through a step writing only
  `X`-TCBs and another core's node, when its keys miss `X`), `InsX ctx t` (= `t` or an old key),
  **`timer.insert.coreW`** (`timer.insert.core` + `WritesIn s1 s' (XFoot … (InsX ctx t) cpu)`),
  **`timer.insert.rb`**: given `remove`'s spec `hrem` with post `P` and `P s1 → TimerRB s1 ∧ tdA t = 0 ∧
  cpu s1 ∈ Cs ∧ nodes placed`, `insert` ends in `TimerRB` (other cores framed: their keys have other core bits;
  armed TCBs are in some tree; unarmed keep null links).
- `TimerRBDel.lean` (pure + walks): `Ctx.app`/`plug_app`/`app_par`, `LSpine` (+`pre`, `of_pre`, `post_head`,
  `keys`), `Rep.zero`, **`plug_hole`**, `min_head`/`min_ne`, `delKeys ctx a b` (= `pre ++ a ++ b ++ post`),
  `min_is_t`, **`min_new_par`/`min_new_r`/`min_keep`** (the `TIMER_MIN` update names the new leftmost key),
  **`timer.remove_loop0.lm`** (+ `loop1/2/3`, the same loop by `rfl`): leftmost walk from a non-null root of a
  subtree of height ≤ fuel+1 returns `y` with `b = ctx2.plug (node cy leaf y g)`, `LSpine ctx2`; fuel never 0.
- `TimerRBDelH.lean`: `delClr/delOne/delTwoFin/delTwo/delTail` restate one copy of the extraction's
  (triplicated) `remove` tail and are definitionally equal to each copy; `Rep.root_ne0`, `Ctx.height_le`,
  `LSpine.keys_node`, `plug_sub`, **`splice_rep`** (pure: a node with ≤ 1 child replaced by that child),
  `LinkFoot` (link words of the old keys/null + root word) with `linkFoot_fix`/`linkFoot_th`,
  **`DelMid st T s1 c Ks s W`** (heap = `W` from the root word, writes in `FixFoot s1 c Ks`, core bits kept,
  node placed), `clrT` (the five clearing writes of `t`), `delClr.on`, `rr_tail`,
  **`delOne.spec`**, **`delTwoFin.spec`**, **`delTwo.spec`**, `DelShape ctx ct a b ctxX tx rr` (the three cases:
  `a = leaf` → `(ctx, b, ct)`; `b = leaf` → `(ctx, a, ct)`; two children → `(app ctx2 (rc ct a y ctx), g, cy)` with
  `b = ctx2.plug (node cy leaf y g)`), **`delTail.spec`** (fixup spec as hypothesis `hfix`, run iff `rr = false`).
- `TimerRBDelC.lean`: `RBT.mem_split`, **`DelShape.keys`** (`(ctxX.plug tx).keys = delKeys ctx a b`),
  `timer.core_of.rb`, **`timer.remove.struct`**: from `TimerRB s` (+ nodes placed), `remove t` either does nothing
  (`tdA t = 0`) or, with `t` in core `c`'s tree `ctx.plug (node ct a t b)`: one `TIMER_MIN` write to
  `(delKeys ctx a b).headD 0` (state `s1`), `DelShape`, `DelMid … s7 (ctxX.plug tx)` before the fixup, the fixup's
  post `Q s7 s8` iff the removed colour is black (`s8 = s7` otherwise), `s' = clrT s8 t`.
- Findings: no reachable bad state; every leftmost walk has height ≤ 127 < fuel + 1; `x = 0` with `x_parent`
  given is exactly `ctxX.par` with `tx = leaf`.
- Full build green at 2d93b84c: `Build completed successfully (7335 jobs)`, 0 errors, 0 sorry; axioms
  propext/Classical.choice/Quot.sound for all new tops (axjc6d.lean, not committed).
- Lean traps met: `subst h` with `h : a = b` between two local variables may eliminate the wrong one (use
  `subst x` naming the variable, `clear` competing equations first); after `fun s6 e => …; subst e` the name `s6`
  is gone (keep `e`, `rw [← e] at r6`); `plug_sub (fun w hw => …)` with untyped binder makes the unifier unfold
  `RBT.keys`/`Ctx.plug` → whnf heartbeat timeout reported at the theorem head; give the inclusion a typed `have`.

Next (exact):
1. **Stage 7 (`remove_fixup`)**, as `hfix` of `timer.remove.struct`: from `CoreTree s c W` (W balanced, black root),
   `DelShape ctx ct a b ctxX tx rr`, `rr = false`, `DelMid s1 c W.keys s7 (ctxX.plug tx)`: `remove_fixup s7 c
   tx.rootKey ctxX.par` ends in an `FB`-like state (heap = `W'` with `W'.keys = (ctxX.plug tx).keys`, `Bal W' n`,
   black root, writes in `FixFoot`, core bits kept).  Pure invariant ("doubly black at the hole", CLRS 13.4):
   `CtxOK`-like predicate for a hole needing black height `n+1` holding `Bal tx n` (`tx` black or leaf in the loop;
   a red `tx` ends the loop and is blackened).  Initial state from `DelShape` + `CtxOK.of_bal` on `W`
   (case 1/2: `Bal (node ct leaf t b) m` with `ct` black ⇒ `b` has bh `m-1`; case 3 similarly at `y`).
   Fuel 256 ≥ number of rounds: each recolour round moves the hole up one level (≤ `ctx.blk` + red levels ≤ 128).
   Heap side: reuse `FB.set_red`, `FB.rotL/rotR` (keys fixed = `(ctxX.plug tx).keys`), reads by
   `timer.*.rep`; `x == left(p)` decides the side (`HoleL`), `x = 0` handled through `ctxX.par`.
2. **Stage 8 remove**: `timer.remove.rb` = `timer.remove.struct` + stage 7 + the clears: `t ∉ (ctxX.plug tx).keys`
   (`DelShape.keys` + Nodup), so `clrT` keeps the tree (`KeepOut` with `X = (· = t)`), `TIMER_MIN = delKeys.headD`
   = new `minKey` (`DelShape.keys` + fixup keeps keys), other cores framed (`CoreTree.keep`, `X` = old keys),
   `t` idle (all five words 0).  Then `timer.insert.rb` with `hrem := timer.remove.rb`.  Then `fire`.

## 11. Sixth session (jc6d6): stage 7 done, stage 8 remove + insert done, fire modulo `send_signal`'s timer frame

- `TimerRBRfxP.lean` (pure): `Ctx.depth` (+ `depth_le`: depth + subtree height ≤ height, `depth_app`),
  `Ctx.plug_root_mem`, **`x_ne_root`** (away from the top the hole's root word is not the root word, so the loop
  guard `x != root` holds), `plug_isRed_key`; **`DB tx n`** ("doubly black": black/leaf balanced of black height
  `n`, or red with balanced children of black height `n`); **`RfA W x p f`** (`W = ctx.plug tx`, `x = tx.rootKey`,
  `p = ctx.par`, `CtxOK ctx (n+1)`, `DB tx n`, `RootB ctx`, `tx` red or `ctx.depth ≤ f`), `RfB` (balanced, black
  root, `x` the root), `RfR` (red `x` to blacken); `UpC`/**`UpOK up cp n`** (path above the parent: `RootB`, top ⇒
  black parent, `CtxOK up (n+1)` + black grandparent-slot if `cp` red, `CtxOK up (n+2)` if black), `UpOK.of_lc/of_rc`,
  `UpOK.pushL/R` (after case 1); case lemmas `rf_case2L/R`, `rf_top`, `rf_case4L/R`, `rfA_top`, `rfR_fin`;
  **`rf_init`** (from `DelShape … false` on a balanced black-root tree of height ≤ 128: `∃ n, CtxOK ctxX (n+1) ∧
  DB tx n ∧ RootB ctxX ∧ ctxX.depth ≤ 128`).
- `TimerRBRfx.lean`: loop invariant `RfInv` (FB + `RfA ∨ RfB`), `RfOut`, `RfPost`; intermediate states `RfC2L/R`
  (black sibling after the optional case 1), `RfC4L/R` (far nephew red); `rf_c4L/R` (case 4 code ⇒ `RfB`),
  `rf_c3L/R` (case 3 code ⇒ `RfC4`).  NB the extraction's right-side case 3 differs by branch: on the
  `left(w)` black / `right(w)` red path it reuses `t3 = right(w)` (no re-read; `rf_c3R` is that form), on the
  (unreachable) `left(w)` red / not-red-again path it re-reads `right(w)`.
- `TimerRBRfxL.lean`: `rf_tailL/R` (cases 2–4 after the optional case 1, code stated literally), `rf_body_L/R`
  (black `x`, left/right child, incl. case 1; for `x = 0` on the right the sibling is non-null so `x != left(p)`),
  `rf_body_top/B/red` (exits), **`rf_body`**, **`timer.remove_fixup_loop.rb`** (`loop.spec_decr_nat`, measure
  fuel; a fuel-spending round starts with black `x` and `depth ≤ fuel`, and ends in `RfB`, with a red `x`, or with
  the path one shorter), **`timer.remove_fixup.rb`** (result `FB … s c (ctx.plug tx).keys s' W ∧ Bal W m ∧ black`).
- `TimerRBRmv.lean`: `del_red_bal` (red removed ⇒ the spliced tree is balanced with black root), `wi_fix_td`,
  `wi_fix_min`, `clrT_wi`, `clrT_t`, `RmQ` (the fixup post in the core-independent form `remove.struct`'s `Q`
  needs: quantified over the core named by `t`'s core bits and the tree, both determined), `delKeys_sub/mem/not`,
  **`timer.remove.rb`**: from `TimerRB s` and placed nodes, after `remove t`: `TimerRB`, `tdA t = 0` (so null links
  and `TimerRB.no_link` applies), nodes placed, and either nothing changed (`t` unarmed) or the writes are in
  `XFoot s (· ∈ W.keys) c` for `t`'s core `c` and its old tree `W`.  **`timer.insert.rb_full`**: `timer.insert.rb`
  with `remove` discharged (needs `L.cpu s ∈ Cs`).
- `TimerRBFire.lean`: `FireInv` (`TimerRB`, nodes placed, current core in `Cs`), `SigTimerFrame` [P] (send_signal
  keeps `TAgree`, `ksb`, `cpu`), `FireInv.reprogram`, **`timer.fire_loop.rb`**, **`timer.fire.rb`** (given
  `SigTimerFrame`).
- Full build green: `Build completed successfully (7345 jobs)`, 0 errors, 0 sorry; axioms propext/Classical.choice/
  Quot.sound for all new tops (axjc6d.lean, not committed).
- Findings: no reachable bad state; the remove fixup's rounds are bounded by the path length (≤ 128 < 256);
  `x = 0` is always identified correctly by `x == left(p)` (a doubly-black null hole has a non-null sibling).

Next (exact):
1. **`SigTimerFrame`** (M–L): `notification.send_signal` writes no timer word (`TW`) and keeps `ksb`/`cpu`.  QueueSignal
   carries `TmFr` (which is `TAgree` + `ksb` for `T`/`Cs`) through most branches but drops it in
   `TInv.of_tmfr`; restate `notification.send_signal.tinv` as `…tmfr` returning `TmFr s s'` (+ cpu, from the
   WritesIn of each step): needs `TmFr` versions of `notification.set_active.tinv` (easy: `ntfn_state_all`'s and
   `ntfn_badge_all`'s `tm`), `smp.remote_tcb_stall.all`, `vcpu.report.blk`, `signal_vm` (#63 `RunningVM` paths).
   Then `TAgree.of_tmfr` and drop the premise of `timer.fire.rb`.
2. Stage 9 (plug-in), as in §2.
