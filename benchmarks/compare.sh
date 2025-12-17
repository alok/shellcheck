#!/bin/bash
#
# ShellCheck Benchmark: Lean4 vs Haskell comparison
#
# This script compares parsing performance between the Lean4 port
# and the original Haskell ShellCheck.
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"

LEAN_SHELLCHECK="${PROJECT_ROOT}/.lake/build/bin/shellcheck4"
HASKELL_SHELLCHECK="${HASKELL_SHELLCHECK:-shellcheck}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Benchmark configuration
ITERATIONS=${ITERATIONS:-10}
WARMUP=${WARMUP:-2}

print_header() {
    echo -e "${BLUE}╔════════════════════════════════════════════════════════════════════════╗${NC}"
    echo -e "${BLUE}║        ShellCheck Benchmark: Lean4 vs Haskell Comparison              ║${NC}"
    echo -e "${BLUE}╚════════════════════════════════════════════════════════════════════════╝${NC}"
    echo ""
}

check_requirements() {
    local missing=0

    if [[ ! -x "$LEAN_SHELLCHECK" ]]; then
        echo -e "${RED}Error: Lean shellcheck not found at $LEAN_SHELLCHECK${NC}"
        echo "Run 'lake build' first."
        missing=1
    fi

    if ! command -v "$HASKELL_SHELLCHECK" &>/dev/null; then
        echo -e "${YELLOW}Warning: Haskell shellcheck not found${NC}"
        echo "Install with: brew install shellcheck"
        HASKELL_SHELLCHECK=""
    fi

    if [[ $missing -eq 1 ]]; then
        exit 1
    fi
}

# Benchmark a single file with a specific shellcheck implementation
benchmark_file() {
    local shellcheck="$1"
    local file="$2"
    local iterations="$3"

    # Warmup runs
    for ((i=0; i<WARMUP; i++)); do
        "$shellcheck" "$file" &>/dev/null || true
    done

    # Timed runs
    local start end
    start=$(perl -MTime::HiRes=time -e 'print time')

    for ((i=0; i<iterations; i++)); do
        "$shellcheck" "$file" &>/dev/null || true
    done

    end=$(perl -MTime::HiRes=time -e 'print time')

    # Calculate average time in milliseconds
    local total_ms elapsed_ms avg_ms
    elapsed_ms=$(echo "($end - $start) * 1000" | bc -l)
    avg_ms=$(echo "$elapsed_ms / $iterations" | bc -l)

    printf "%.2f" "$avg_ms"
}

# Run comparison on a single file
compare_file() {
    local file="$1"
    local name="$2"
    local lines

    lines=$(wc -l < "$file" | tr -d ' ')

    echo -n "  $name ($lines lines): "

    # Lean benchmark
    local lean_time
    lean_time=$(benchmark_file "$LEAN_SHELLCHECK" "$file" "$ITERATIONS")

    # Haskell benchmark (if available)
    local haskell_time="N/A"
    local speedup="N/A"

    if [[ -n "$HASKELL_SHELLCHECK" ]]; then
        haskell_time=$(benchmark_file "$HASKELL_SHELLCHECK" "$file" "$ITERATIONS")
        speedup=$(echo "scale=1; $haskell_time / $lean_time" | bc -l)
    fi

    # Check parse success
    local lean_ok haskell_ok
    if "$LEAN_SHELLCHECK" "$file" &>/dev/null || [[ $? -eq 1 ]]; then
        lean_ok="${GREEN}✓${NC}"
    else
        lean_ok="${RED}✗${NC}"
    fi

    if [[ -n "$HASKELL_SHELLCHECK" ]]; then
        if "$HASKELL_SHELLCHECK" "$file" &>/dev/null || [[ $? -eq 1 ]]; then
            haskell_ok="${GREEN}✓${NC}"
        else
            haskell_ok="${RED}✗${NC}"
        fi
    else
        haskell_ok="-"
    fi

    # Print results
    printf "\n"
    printf "    %-12s %s  %8s ms\n" "Lean:" "$lean_ok" "$lean_time"

    if [[ -n "$HASKELL_SHELLCHECK" ]]; then
        printf "    %-12s %s  %8s ms\n" "Haskell:" "$haskell_ok" "$haskell_time"

        if (( $(echo "$speedup > 1" | bc -l) )); then
            printf "    ${GREEN}Lean is %.1fx faster${NC}\n" "$speedup"
        else
            local inverse
            inverse=$(echo "scale=1; 1 / $speedup" | bc -l)
            printf "    ${YELLOW}Haskell is %.1fx faster${NC}\n" "$inverse"
        fi
    fi
}

# Test parse equivalence
test_equivalence() {
    local file="$1"

    if [[ -z "$HASKELL_SHELLCHECK" ]]; then
        return 0
    fi

    local lean_out haskell_out
    lean_out=$("$LEAN_SHELLCHECK" "$file" 2>&1 | grep -c "SC[0-9]" || echo 0)
    haskell_out=$("$HASKELL_SHELLCHECK" "$file" 2>&1 | grep -c "SC[0-9]" || echo 0)

    echo "    Warnings: Lean=$lean_out, Haskell=$haskell_out"
}

main() {
    print_header
    check_requirements

    echo -e "${BLUE}Configuration:${NC}"
    echo "  Iterations: $ITERATIONS"
    echo "  Warmup runs: $WARMUP"
    echo "  Lean: $LEAN_SHELLCHECK"
    [[ -n "$HASKELL_SHELLCHECK" ]] && echo "  Haskell: $HASKELL_SHELLCHECK"
    echo ""

    # Test benchmark scripts
    echo -e "${BLUE}Benchmark Scripts:${NC}"
    echo ""

    for script in "$SCRIPT_DIR"/scripts/*.sh; do
        [[ -f "$script" ]] || continue
        local name
        name=$(basename "$script")
        compare_file "$script" "$name"
        echo ""
    done

    # Test real-world scripts if available
    if [[ -d /opt/homebrew/Library/Homebrew ]]; then
        echo -e "${BLUE}Real-World Scripts (Homebrew):${NC}"
        echo ""

        local homebrew_scripts=(
            "/opt/homebrew/Library/Homebrew/brew.sh"
            "/opt/homebrew/Library/Homebrew/cmd/update.sh"
        )

        for script in "${homebrew_scripts[@]}"; do
            if [[ -f "$script" ]]; then
                compare_file "$script" "$(basename "$script")"
                echo ""
            fi
        done
    fi

    echo -e "${BLUE}═══════════════════════════════════════════════════════════════════════${NC}"
    echo -e "${GREEN}Benchmark complete!${NC}"
}

main "$@"
