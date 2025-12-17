# ShellCheck Lean4 Benchmarks

Performance comparison between the Lean4 port and the original Haskell ShellCheck.

## Quick Start

```bash
# Build the benchmark
lake build shellcheck4_bench

# Run the Lean benchmark
.lake/build/bin/shellcheck4_bench

# Run comparison with Haskell ShellCheck
./benchmarks/compare.sh
```

## Benchmark Results

### Lean4 vs Haskell Performance

| Script | Lines | Lean | Haskell | Speedup |
|--------|-------|------|---------|---------|
| simple_commands.sh | 85 | 28ms | 32ms | 1.1x |
| complex_script.sh | 283 | 31ms | 72ms | 2.3x |
| edge_cases.sh | 224 | 27ms | 65ms | 2.3x |
| brew.sh (Homebrew) | 1095 | 38ms | 439ms | **11.6x** |
| update.sh (Homebrew) | 1070 | 165ms | 371ms | 2.2x |

### Pure Parsing Throughput (Lean)

| Script | Avg Time | Lines/sec |
|--------|----------|-----------|
| Simple (8 lines) | 0.07ms | 134,328 |
| Medium (20 lines) | 0.31ms | 73,248 |
| Complex (55 lines) | 0.22ms | 231,818 |

**Average throughput: ~146,000 lines/second**

## Test Scripts

The `scripts/` directory contains test cases:

- `simple_commands.sh` - Basic shell commands, variables, loops
- `complex_script.sh` - Functions, traps, arrays, here-docs
- `edge_cases.sh` - Unusual but valid shell syntax

## Configuration

Environment variables for `compare.sh`:

```bash
ITERATIONS=10      # Number of timed runs
WARMUP=2           # Number of warmup runs
HASKELL_SHELLCHECK=shellcheck  # Path to Haskell binary
```

## Check Coverage

Example warnings comparison on `complex_script.sh`:

| Lean4 | Haskell |
|-------|---------|
| SC2034 (unused variable) | SC2034 (unused variable) |
| SC2154 (unassigned variable) | SC2155 (declare+assign) |
| SC2164 (cd without exit) | SC2030/SC2031 (subshell modification) |
| SC2082 (indirect expansion) | SC2145 (array in string) |

Both detect real issues but may flag different patterns.

## Notes

- Both implementations parse all test scripts successfully
- The Lean port has ~90 implemented checks (Haskell has ~400+)
- Real-world scripts from Homebrew test production-quality parsing
- Parser is equivalent; check coverage is still being expanded
