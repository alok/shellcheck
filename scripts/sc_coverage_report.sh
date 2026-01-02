#!/usr/bin/env bash
set -euo pipefail

root="$(git rev-parse --show-toplevel)"
cd "$root"

tmp_dir="$(mktemp -d)"
trap 'rm -rf "$tmp_dir"' EXIT

impl_sc2="$tmp_dir/sc2_impl.txt"
impl_sc3="$tmp_dir/sc3_impl.txt"
cov_sc2="$tmp_dir/sc2_cov.txt"
cov_sc3="$tmp_dir/sc3_cov.txt"

# Extract SC codes from implementation (exclude tests) by matching rule emitters.
rg --no-filename -o "\\b(?:makeComment|makeCommentWithFix|warnCmd|errorCmd|styleCmd|infoCmd|warnArg|errorArg|styleArg|infoArg|pipelineRule|warn|error|info|style)\\b[^\\n]*\\b2[0-9]{3}\\b" \
  ShellCheck --glob '!ShellCheck/Tests/**' \
  | rg -o "2[0-9]{3}" | sort -u | sed 's/^/SC/' > "$impl_sc2"
rg --no-filename -o "\\b(?:makeComment|makeCommentWithFix|warnCmd|errorCmd|styleCmd|infoCmd|warnArg|errorArg|styleArg|infoArg|pipelineRule|warn|error|info|style)\\b[^\\n]*\\b3[0-9]{3}\\b" \
  ShellCheck --glob '!ShellCheck/Tests/**' \
  | rg -o "3[0-9]{3}" | sort -u | sed 's/^/SC/' > "$impl_sc3"

# Extract coverage codes from SCCoverage.
rg --no-filename -o "code := 2[0-9]{3}|mk[A-Za-z]*Case 2[0-9]{3}" ShellCheck/Tests/SCCoverage.lean \
  | rg -o "2[0-9]{3}" | sort -u | sed 's/^/SC/' > "$cov_sc2" || true
rg --no-filename -o "code := 3[0-9]{3}|mk[A-Za-z]*Case 3[0-9]{3}" ShellCheck/Tests/SCCoverage.lean \
  | rg -o "3[0-9]{3}" | sort -u | sed 's/^/SC/' > "$cov_sc3" || true

# Ignore codes that are not user-facing checks (parser diagnostics, etc.).
ignore_sc2=("SC2999")
for code in "${ignore_sc2[@]}"; do
  rg -v --fixed-strings "$code" "$impl_sc2" > "$tmp_dir/sc2_filtered.txt"
  mv "$tmp_dir/sc2_filtered.txt" "$impl_sc2"
done

missing_sc2="$(comm -23 "$impl_sc2" "$cov_sc2")"
missing_sc3="$(comm -23 "$impl_sc3" "$cov_sc3")"
extra_sc2="$(comm -13 "$impl_sc2" "$cov_sc2")"
extra_sc3="$(comm -13 "$impl_sc3" "$cov_sc3")"

echo "SC2xxx coverage missing:"
if [[ -z "$missing_sc2" ]]; then
  echo "  (none)"
else
  echo "$missing_sc2" | sed 's/^/  /'
fi

echo ""
echo "SC3xxx coverage missing:"
if [[ -z "$missing_sc3" ]]; then
  echo "  (none)"
else
  echo "$missing_sc3" | sed 's/^/  /'
fi

echo ""
echo "SC2xxx coverage extra (not found in codebase):"
if [[ -z "$extra_sc2" ]]; then
  echo "  (none)"
else
  echo "$extra_sc2" | sed 's/^/  /'
fi

echo ""
echo "SC3xxx coverage extra (not found in codebase):"
if [[ -z "$extra_sc3" ]]; then
  echo "  (none)"
else
  echo "$extra_sc3" | sed 's/^/  /'
fi
