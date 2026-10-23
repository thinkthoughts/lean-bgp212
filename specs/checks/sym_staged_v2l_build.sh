#!/usr/bin/env bash
# V2ℓ: build the staged certificates one `lean` process at a time (for machines with about 4 GB of
# memory, where `lake build`'s parallel jobs could run two certificates at once). Each module's
# dependencies are built by the preceding lines, so every `lake build` below runs one `lean`.
set -euo pipefail
lake build Solution.SymStaged Solution.SymPerm Solution.SymReduceDemo1 Solution.SymReduceDemo2 Solution.SymReduceDemo3
for m in \
  Solution.SymStagedCert.DmRun4D \
  Solution.SymStagedCert.DmRun1 \
  Solution.SymStagedCert.DmRun5D \
  Solution.SymStagedCert.DmRun5C0 \
  Solution.SymStagedCert.DmRun5C1 \
  Solution.SymStagedCert.DmRun5C2 \
  Solution.SymStagedCert.DmRun5C3 \
  Solution.SymStagedCert.DmRun5 \
  Solution.SymStagedCert.DmRun6D \
  Solution.SymStagedCert.DmRun6C0 \
  Solution.SymStagedCert.DmRun6C1 \
  Solution.SymStagedCert.DmRun6C2 \
  Solution.SymStagedCert.DmRun6C3 \
  Solution.SymStagedCert.DmRun6C4 \
  Solution.SymStagedCert.DmRun6C5 \
  Solution.SymStagedCert.DmRun6C6 \
  Solution.SymStagedCert.DmRun6C7 \
  Solution.SymStagedCert.DmRun6C8 \
  Solution.SymStagedCert.DmRun6C9 \
  Solution.SymStagedCert.DmRun6C10 \
  Solution.SymStagedCert.DmRun6C11 \
  Solution.SymStagedCert.DmRun6 \
  Solution.SymStagedCert.T3Run4D \
  Solution.SymStagedCert.T3Run1 \
  Solution.SymStagedCert.T3Run5D \
  Solution.SymStagedCert.T3Run5C0 \
  Solution.SymStagedCert.T3Run5C1 \
  Solution.SymStagedCert.T3Run5C2 \
  Solution.SymStagedCert.T3Run5C3 \
  Solution.SymStagedCert.T3Run5 \
  Solution.SymStagedCert.T3Run6D \
  Solution.SymStagedCert.T3Run6C0 \
  Solution.SymStagedCert.T3Run6C1 \
  Solution.SymStagedCert.T3Run6C2 \
  Solution.SymStagedCert.T3Run6C3 \
  Solution.SymStagedCert.T3Run6C4 \
  Solution.SymStagedCert.T3Run6C5 \
  Solution.SymStagedCert.T3Run6C6 \
  Solution.SymStagedCert.T3Run6C7 \
  Solution.SymStagedCert.T3Run6C8 \
  Solution.SymStagedCert.T3Run6C9 \
  Solution.SymStagedCert.T3Run6C10 \
  Solution.SymStagedCert.T3Run6C11 \
  Solution.SymStagedCert.T3Run6 \
  Solution.SymStagedCert.DmVal6G0 \
  Solution.SymStagedCert.DmVal6G1 \
  Solution.SymStagedCert.DmVal6G2 \
  Solution.SymStagedDemo1 \
  Solution.SymStagedDemo2 \
  Solution.SymStagedDemo3 \
  Solution.SymStagedRuns \
  Solution.SymStagedDemo4 \
  Solution.SymStagedDemo5 \
  Solution.SymStagedCert.T3Prof \
  Solution.SymStagedCert.T3Prof6G0 \
  Solution.SymStagedCert.T3Prof6G1 \
  Solution.SymStagedCert.T3Prof6G2 \
  Solution.SymStagedCert.T3Prof6 \
  Solution.SymStagedProfiles \
  Solution.SymStagedDemo6 \
  Solution.SymStagedSuite \
  Challenge.SymStaged \
  ; do
  echo "== $m"
  lake build "$m"
done
