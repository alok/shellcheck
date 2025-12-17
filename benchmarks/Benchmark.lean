/-
  ShellCheck Lean4 Benchmark Suite

  Measures parsing performance and compares with reference implementations.
-/

import ShellCheck.Parser

namespace ShellCheck.Benchmark

/-- Format a float with fixed decimal places -/
def formatFloat (f : Float) (decimals : Nat := 2) : String :=
  let factor := (10 : Float) ^ decimals.toFloat
  let rounded := (f * factor).round / factor
  let str := toString rounded
  -- Ensure we have decimal point
  if str.contains '.' then str else str ++ ".0"

/-- Right-pad a string to a given width -/
def padRight (s : String) (width : Nat) : String :=
  s ++ String.mk (List.replicate (width - s.length) ' ')

/-- Left-pad a string to a given width -/
def padLeft (s : String) (width : Nat) : String :=
  String.mk (List.replicate (width - s.length) ' ') ++ s

/-- Result of a single benchmark run -/
structure BenchmarkResult where
  name : String
  iterations : Nat
  totalTimeMs : Float
  avgTimeMs : Float
  linesPerSecond : Float
  parseSuccess : Bool
  deriving Repr

/-- Measure time to parse a script multiple times -/
def benchmarkParse (name : String) (script : String) (iterations : Nat := 100) : IO BenchmarkResult := do
  let lines := script.splitOn "\n" |>.length

  -- Warmup
  for _ in [:5] do
    let _ := ShellCheck.Parser.runFullParser script "<bench>"

  -- Timed runs
  let startTime ← IO.monoMsNow
  let mut success := true

  for _ in [:iterations] do
    let (result, _, _) := ShellCheck.Parser.runFullParser script "<bench>"
    if result.isNone then
      success := false

  let endTime ← IO.monoMsNow
  let totalMs := (endTime - startTime).toFloat
  let avgMs := totalMs / iterations.toFloat
  let lps := if avgMs > 0 then lines.toFloat / (avgMs / 1000.0) else 0.0

  return {
    name := name
    iterations := iterations
    totalTimeMs := totalMs
    avgTimeMs := avgMs
    linesPerSecond := lps
    parseSuccess := success
  }

/-- Simple benchmark scripts -/
def simpleScript : String := "#!/bin/bash
echo \"Hello World\"
ls -la /tmp
name=\"John\"
echo \"Name: $name\"
for i in 1 2 3; do
  echo \"$i\"
done
"

def mediumScript : String := "#!/bin/bash
set -euo pipefail

log() {
    echo \"[$(date)] $*\"
}

process_file() {
    local file=\"$1\"
    if [[ -f \"$file\" ]]; then
        cat \"$file\" | grep pattern | sort | uniq
    fi
}

main() {
    local -a files=(one.txt two.txt three.txt)
    for f in \"${files[@]}\"; do
        process_file \"$f\"
    done
}

main \"$@\"
"

def complexScript : String := "#!/bin/bash
set -euo pipefail

readonly SCRIPT_DIR=\"$(cd \"$(dirname \"${BASH_SOURCE[0]}\")\" && pwd)\"
declare -A CONFIG
declare -a PROCESSED

parse_config() {
    local file=\"$1\"
    while IFS='=' read -r key value; do
        [[ \"$key\" =~ ^# ]] && continue
        CONFIG[\"$key\"]=\"$value\"
    done < \"$file\"
}

process() {
    local input=\"$1\" output=\"$2\"
    cat \"$input\" \\
        | sed 's/foo/bar/g' \\
        | tr '[:upper:]' '[:lower:]' \\
        | sort | uniq -c \\
        > \"$output\"
}

cleanup() {
    rm -f /tmp/*.tmp 2>/dev/null || true
}

trap cleanup EXIT
trap 'exit 130' INT

case \"${1:-}\" in
    start) echo \"Starting\" ;;
    stop) echo \"Stopping\" ;;
    *) echo \"Usage: $0 {start|stop}\" ;;
esac

for ((i=0; i<10; i++)); do
    PROCESSED+=(\"item_$i\")
done

cat << 'EOF'
Multi-line
here document
EOF

[[ -f file && -r file ]] && echo \"ok\"
(( x = 5 + 3 * 2 ))

echo \"Done: ${#PROCESSED[@]} items\"
"

/-- Run all benchmarks -/
def runBenchmarks : IO Unit := do
  IO.println "╔═══════════════════════════════════════════════════════════════╗"
  IO.println "║           ShellCheck Lean4 Parser Benchmark Suite             ║"
  IO.println "╠═══════════════════════════════════════════════════════════════╣"
  IO.println "║ Script                    │ OK │    Avg Time │   Lines/sec   ║"
  IO.println "╟───────────────────────────┼────┼─────────────┼───────────────╢"

  let results := #[
    (← benchmarkParse "Simple (8 lines)" simpleScript 1000),
    (← benchmarkParse "Medium (20 lines)" mediumScript 500),
    (← benchmarkParse "Complex (55 lines)" complexScript 200)
  ]

  for r in results do
    let status := if r.parseSuccess then "✓" else "✗"
    let avgStr := formatFloat r.avgTimeMs 3 ++ "ms"
    let lpsStr := formatFloat r.linesPerSecond 0
    IO.println s!"║ {padRight r.name 25} │  {status} │ {padLeft avgStr 11} │ {padLeft lpsStr 13} ║"

  IO.println "╚═══════════════════════════════════════════════════════════════╝"
  IO.println ""

  -- Summary stats
  let avgLps := results.foldl (fun acc r => acc + r.linesPerSecond) 0 / results.size.toFloat
  IO.println s!"Average throughput: {formatFloat avgLps 0} lines/second"

  let allPassed := results.all (·.parseSuccess)
  if allPassed then
    IO.println "All benchmarks passed ✓"
  else
    IO.println "Some benchmarks failed ✗"

end ShellCheck.Benchmark

def main : IO Unit := ShellCheck.Benchmark.runBenchmarks
