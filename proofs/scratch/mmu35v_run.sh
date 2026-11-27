#!/bin/bash
# mmu35: build virt gen 15/16 copies, then the five AX chunks, keep each chunk's output.
M="Fl4Proofs.P3.VirtInitIo Fl4Proofs.P3.VirtInitWalk Fl4Proofs.P3.VirtRetypeInit Fl4Proofs.P3.VirtMsrEq Fl4Proofs.P3.VirtMsrDec Fl4Proofs.P3.VirtMsrStore Fl4Proofs.P3.VirtVmcbStore Fl4Proofs.P3.VirtReplyKeep Fl4Proofs.P3.VirtMsrE2E Fl4Proofs.P3.VirtVmcbDec"
mkdir -p afkback
for i in 0 1 2 3 4; do
  AXF=proofs/scratch/mmu35v${i}_ax.lean bash proofs/scratch/mmu35_chk.sh "$M" > afkback/v$i.txt 2>&1
  cp afklogs/mmu35-run.out afkback/vrun$i.txt
done
