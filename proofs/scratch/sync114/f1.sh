#!/bin/bash
# s114-f1 (afkprover2): P0 regen (x86 + A64) then MODE=mod on every module that unfolds a changed function.
mkdir -p afklogs
# orphans of a stopped earlier run in this mirror (lake runs under setsid)
for p in $(pgrep -x lake) $(pgrep -x lean); do c=$(readlink /proc/$p/cwd); case "$c" in "$PWD"/proofs*) echo KILL_ORPHAN $p; kill $p;; esac; done; sleep 2
rm -f s114/f1.tgz
SEED=${SEED:-FL4-int22} bash s114/p0.sh > afklogs/s114-p0.out 2>&1; echo P0_EXIT $?
grep -E '^(GC|GP|STATUS|OLEANS|SEEDED|LAKE|NOT)' afklogs/s114-p0.out
MODE=mod MODS="Fl4Proofs.P2.ProgGenL39 Fl4Proofs.P2.ProgGenL40 Fl4Proofs.P2.ProgGenIo3 Fl4Proofs.P1.QueueFootS Fl4Proofs.P1.QueueSignal Fl4Proofs.P1.TimerRBSig Fl4Proofs.P2.FootN10 Fl4Proofs.P2.FootN11 Fl4Proofs.P2.FootN8 Fl4Proofs.P2.FootTimerFireSig Fl4Proofs.P2.VcpuExitV Fl4Proofs.P3.ArchKeep Fl4Proofs.P3.IpcNtfnSend Fl4Proofs.P3.IpcNtfnWake Fl4Proofs.P3.IpcSignalBound Fl4Proofs.P3.IpcSignalDon Fl4Proofs.P3.IpcSignalWake Fl4Proofs.P3.JAtZV3SigVm Fl4Proofs.P3.JAtZV3SigComp Fl4Proofs.P3.MachKeep Fl4Proofs.P3.MachKeepF Fl4Proofs.P3.NtfnSend Fl4Proofs.P3.NtfnWake" SEED=${SEED:-FL4-int22} bash /data/fl4/afk-build.sh > afklogs/s114-mod.out 2>&1; echo MOD_EXIT $?
grep -E '^(BUILD|ERRORS|SORRY|JOBS|OLEANS)' afklogs/s114-mod.out
grep -E 'Build completed|error: build failed' afklogs/b-mod.log | tail -2
grep -n '^error' -A30 afklogs/b-mod.log | cut -c1-260 | head -250
mkdir -p s114/back; cp afklogs/s114-*.out afklogs/b-mod.log s114/back/; tar czf s114/f1.tgz s114/back s114/p0.tgz
