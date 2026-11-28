#!/bin/bash
# print only errors (with following context) from afklogs/t-<name>.out
f=afklogs/t-$1.out
awk '/: error/{p=1; n=0} /: warning/{p=0} p{print; n++; if(n>'"${2:-30}"') p=0}' $f | head -${3:-300}
tail -1 $f
