#!/bin/bash
# print the error blocks of the last afk-build log (first N lines each)
N=${N:-25}
awk -v N=$N '/^error: Fl4Proofs\//{p=1;c=0} /^(warning|⚠|✖|✔|info|trace)/{p=0} p{if(c<N)print; c++}' afklogs/b-mod.log | head -${MAX:-300}
