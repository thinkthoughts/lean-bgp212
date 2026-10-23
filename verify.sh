#!/usr/bin/env bash
set -euo pipefail

lake build
lake build Challenge
lake build Solution

COMPARATOR_LANDRUN="${COMPARATOR_LANDRUN:-$HOME/landrun/landrun}"
COMPARATOR_LEAN4EXPORT="${COMPARATOR_LEAN4EXPORT:-$HOME/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export}"
COMPARATOR_BIN="${COMPARATOR_BIN:-$HOME/comparator/.lake/build/bin/comparator}"

for config in Comparator/lemma_12_1.json Comparator/appendix_b.json Comparator/a2_combinatorial.json Comparator/multishift.json Comparator/multishift_b2.json Comparator/packing_a3a.json Comparator/packing_a3b.json Comparator/packing_a3c.json Comparator/theorem_7_11.json Comparator/final_deduction.json Comparator/variational_v0.json Comparator/simplex_moment_v1.json Comparator/gram_entry_v2b.json Comparator/gram_general_v2c.json Comparator/fibre_v2d.json Comparator/aggregate_v2e.json Comparator/capcell_v2eb.json Comparator/marginal_entry_v2f.json Comparator/power_sum_entry_v2g.json Comparator/power_sum_square_v2h.json Comparator/gen_entry_v2i.json Comparator/moment_agg_v2j.json Comparator/sym_reduce_v2k.json Comparator/sym_staged_v2l.json Comparator/sym_trie_v2m.json; do
  echo "== $config"
  COMPARATOR_LANDRUN="$COMPARATOR_LANDRUN" \
  COMPARATOR_LEAN4EXPORT="$COMPARATOR_LEAN4EXPORT" \
  lake env "$COMPARATOR_BIN" "$config"
done
