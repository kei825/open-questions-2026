#!/bin/bash
# Compile every Lean file in this repository against Mathlib v4.33.1 and print its axioms.
# Usage (from the repository root):
#   lake exe cache get      # download the Mathlib build cache once
#   scripts/check_lean.sh
set -u
status=0
for f in $(find . -path ./.lake -prune -o -name '*.lean' -print | sort); do
  echo "=== $f"
  if ! lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false "$f"; then status=1; fi
done
exit $status
