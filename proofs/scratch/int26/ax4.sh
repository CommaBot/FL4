#!/bin/bash
# int26-ax4 (afkprover): the axiom sweep axint26 alone on the built mirror (no lake build), output in int26back4.tgz.
mkdir -p afklogs int26back4
bash proofs/scratch/int26/axrun.sh scratch/int26/axint26.lean afklogs/int26-ax4.out
cp afklogs/int26-ax4.out int26back4/; tar czf int26back4.tgz int26back4
