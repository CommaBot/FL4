# print error blocks of the mod build log (until the next warning / build line)
awk '/^error/{p=1} /^(warning|⚠|✔|info)/{p=0} p' afklogs/b-mod.log | head -${1:-120} | cut -c1-240
