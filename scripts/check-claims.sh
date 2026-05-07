#!/bin/bash
# Check paper-code-proof traceability
# Verifies that claims-registry.yaml entries have corresponding code and LaTeX references.
set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REGISTRY="$ROOT/claims-registry.yaml"
ERRORS=0

echo "=== Claims Registry Check ==="
echo ""

# 1. Check that every LaTeX label in the registry exists in the paper
echo "Checking LaTeX labels..."
for label in $(grep 'label:' "$REGISTRY" | sed 's/.*label: //' | tr -d '"'); do
  found=$(grep -r "label{$label}" "$ROOT/paper/" 2>/dev/null | wc -l | tr -d ' ')
  if [ "$found" -eq 0 ]; then
    echo "  WARNING: label '$label' not found in paper/"
    ERRORS=$((ERRORS + 1))
  else
    echo "  OK: $label"
  fi
done
echo ""

# 2. Check that verification code files exist
echo "Checking verification code paths..."
for codepath in $(grep '        code:' "$REGISTRY" | sed 's/.*code: //' | cut -d'#' -f1 | tr -d '"'); do
  if [ ! -f "$ROOT/$codepath" ]; then
    echo "  MISSING: $codepath"
    ERRORS=$((ERRORS + 1))
  else
    echo "  OK: $codepath"
  fi
done
echo ""

# 3. Check for DRIFTED status
echo "Checking for drifted claims..."
drifted=$(grep -c 'status: DRIFTED' "$REGISTRY" || true)
needs_verify=$(grep -c 'status: NEEDS_VERIFICATION' "$REGISTRY" || true)
not_in_ci=$(grep -c 'status: NOT_IN_CI' "$REGISTRY" || true)
if [ "$drifted" -gt 0 ]; then
  echo "  WARNING: $drifted claim(s) have DRIFTED status"
  grep -B3 'status: DRIFTED' "$REGISTRY" | grep 'statement:' | sed 's/.*statement: /    /'
  ERRORS=$((ERRORS + drifted))
fi
if [ "$needs_verify" -gt 0 ]; then
  echo "  INFO: $needs_verify claim(s) need verification"
fi
if [ "$not_in_ci" -gt 0 ]; then
  echo "  INFO: $not_in_ci claim(s) not in CI"
fi
echo ""

# 4. Check Lean toolchain version matches paper claim
echo "Checking Lean version..."
if [ -f "$ROOT/lean/lean-toolchain" ]; then
  lean_version=$(cat "$ROOT/lean/lean-toolchain" | tr -d '[:space:]')
  paper_claim=$(grep 'statement.*Lean' "$REGISTRY" | grep -o 'v[0-9.]*' || echo "unknown")
  echo "  Lean toolchain: $lean_version"
  echo "  Paper claims: $paper_claim"
  if ! echo "$lean_version" | grep -q "$paper_claim" 2>/dev/null; then
    echo "  WARNING: Lean version may not match paper claim"
  fi
fi
echo ""

# Summary
echo "=== Summary ==="
if [ "$ERRORS" -eq 0 ]; then
  echo "All checks passed."
else
  echo "$ERRORS issue(s) found. Review claims-registry.yaml and fix drift."
  exit 1
fi
