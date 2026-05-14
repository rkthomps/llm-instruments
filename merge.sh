#!/bin/bash

set -u

BRANCHES=(4.10.0 4.18.0 4.22.0 4.24.0 4.25.0 4.27.0)
MAIN="main"

if [[ -n "$(git status --porcelain)" ]]; then
  echo "working tree not clean — commit or stash first" >&2
  exit 1
fi

start_branch=$(git rev-parse --abbrev-ref HEAD)
declare -A RESULTS

for b in "${BRANCHES[@]}"; do
  echo "########## $b ##########"
  git checkout "$b" || { RESULTS[$b]="checkout FAIL"; continue; }

  pre=$(git rev-parse HEAD)          # remember pre-merge state

  if ! git merge --no-edit "$MAIN"; then
    git merge --abort
    RESULTS[$b]="CONFLICT (aborted)"
    continue
  fi

  if ./check-versions.sh VERSIONS.txt; then
    RESULTS[$b]="OK (merge kept)"
  else
    git reset --hard "$pre"          # roll the merge back, leave branch untouched
    RESULTS[$b]="TEST FAIL (rolled back)"
  fi
done

git checkout "$start_branch"

echo
echo "########## summary ##########"
fail=0
for b in "${BRANCHES[@]}"; do
  printf "  %-10s %s\n" "$b" "${RESULTS[$b]}"
  [[ "${RESULTS[$b]}" == OK* ]] || fail=1
done
exit $fail