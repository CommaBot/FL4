# usage: p2j5b.sh MOD...   (afkprover; prints errors only)
MODE=mod MODS="$*" bash /data/fl4/afk-build.sh > afklogs/p2j5.out 2>&1
grep -E "^(BUILD|ERRORS|LAKE_RUNNING)" afklogs/p2j5.out
awk '/^error: Fl4|^warning: |^trace|^✔|^⚠|^✖|^ℹ/{p=0} /^error: Fl4/{p=1;n=0} p&&n<38{print;n++}' afklogs/b-mod.log | cut -c1-240 | head -230
