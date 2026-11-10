#!/usr/bin/env bash
# Re-check every module of gc-zk with `leanchecker`, the kernel replay checker shipped with Lean.
#
# Run from the root of the repository, after `lake build`:
#
#     bash scripts/leanchecker.sh
#
# The modules are checked one at a time, each in its own process. Do not run
# `lake env leanchecker GcZk`: leanchecker reads its argument as a prefix, so that command selects
# every module `GcZk.*` and replays all of them in parallel, each with its own copy of the Mathlib
# environment, which needs well over 10 GB of memory. One module at a time needs at most about
# 5 GB. The root module `GcZk` only imports the others and has no declarations of its own, so it
# is not checked separately.
set -u
cd "$(dirname "$0")/.." || exit 1

modules="$(sed -n 's/^import //p' GcZk.lean) GcZk.API"
failed=0
for m in $modules; do
  if lake env leanchecker "$m" > /dev/null 2>&1; then
    echo "ok      $m"
  else
    echo "FAILED  $m"
    failed=1
  fi
done
exit $failed
