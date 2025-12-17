#!/bin/bash
# Complex script benchmark - tests advanced shell features

set -euo pipefail

# Global configuration
readonly SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
readonly LOG_FILE="/tmp/benchmark_$$.log"
declare -A CONFIG
declare -a PROCESSED_FILES

# Logging functions
log_info() {
    local timestamp
    timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    echo "[$timestamp] INFO: $*" | tee -a "$LOG_FILE"
}

log_error() {
    local timestamp
    timestamp=$(date '+%Y-%m-%d %H:%M:%S')
    echo "[$timestamp] ERROR: $*" >&2 | tee -a "$LOG_FILE"
}

log_debug() {
    if [[ "${DEBUG:-0}" == "1" ]]; then
        local timestamp
        timestamp=$(date '+%Y-%m-%d %H:%M:%S')
        echo "[$timestamp] DEBUG: $*" | tee -a "$LOG_FILE"
    fi
}

# Configuration parser
parse_config() {
    local config_file="$1"

    if [[ ! -f "$config_file" ]]; then
        log_error "Config file not found: $config_file"
        return 1
    fi

    while IFS='=' read -r key value; do
        # Skip comments and empty lines
        [[ "$key" =~ ^[[:space:]]*# ]] && continue
        [[ -z "$key" ]] && continue

        # Trim whitespace
        key="${key#"${key%%[![:space:]]*}"}"
        key="${key%"${key##*[![:space:]]}"}"
        value="${value#"${value%%[![:space:]]*}"}"
        value="${value%"${value##*[![:space:]]}"}"

        CONFIG["$key"]="$value"
        log_debug "Config: $key = $value"
    done < "$config_file"
}

# Process files with parallel execution
process_files() {
    local input_dir="$1"
    local output_dir="$2"
    local max_jobs="${3:-4}"
    local job_count=0

    mkdir -p "$output_dir"

    for file in "$input_dir"/*; do
        [[ -f "$file" ]] || continue

        # Wait if max jobs reached
        while (( job_count >= max_jobs )); do
            wait -n 2>/dev/null || true
            ((job_count--)) || true
        done

        # Process in background
        {
            local basename
            basename=$(basename "$file")
            local output_file="$output_dir/$basename.processed"

            log_info "Processing: $basename"

            # Simulate processing
            if process_single_file "$file" "$output_file"; then
                PROCESSED_FILES+=("$basename")
                log_info "Completed: $basename"
            else
                log_error "Failed: $basename"
            fi
        } &

        ((job_count++))
    done

    # Wait for all jobs
    wait
}

process_single_file() {
    local input="$1"
    local output="$2"

    # Various text transformations
    cat "$input" \
        | sed 's/[[:space:]]\+/ /g' \
        | tr '[:upper:]' '[:lower:]' \
        | sort \
        | uniq -c \
        | sort -rn \
        > "$output"

    return $?
}

# Network operations
check_connectivity() {
    local hosts=("google.com" "github.com" "example.com")
    local timeout=5

    for host in "${hosts[@]}"; do
        if ping -c 1 -W "$timeout" "$host" &>/dev/null; then
            log_info "Host reachable: $host"
        else
            log_error "Host unreachable: $host"
        fi
    done
}

# JSON-like output
generate_report() {
    local status="$1"
    local message="$2"
    local processed_count="${#PROCESSED_FILES[@]}"

    cat << EOF
{
    "status": "$status",
    "message": "$message",
    "processed_files": $processed_count,
    "files": [
$(printf '        "%s",\n' "${PROCESSED_FILES[@]}" | sed '$ s/,$//')
    ],
    "timestamp": "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
}
EOF
}

# Cleanup handler
cleanup() {
    local exit_code=$?
    log_info "Cleaning up..."

    # Remove temp files
    rm -f /tmp/benchmark_*.tmp 2>/dev/null || true

    if (( exit_code != 0 )); then
        log_error "Script failed with exit code: $exit_code"
    fi

    exit $exit_code
}

# Signal handlers
trap cleanup EXIT
trap 'log_error "Interrupted"; exit 130' INT
trap 'log_error "Terminated"; exit 143' TERM

# Argument parsing
parse_args() {
    local positional=()

    while [[ $# -gt 0 ]]; do
        case "$1" in
            -c|--config)
                CONFIG_FILE="$2"
                shift 2
                ;;
            -d|--debug)
                DEBUG=1
                shift
                ;;
            -h|--help)
                show_help
                exit 0
                ;;
            -v|--verbose)
                VERBOSE=1
                shift
                ;;
            --)
                shift
                positional+=("$@")
                break
                ;;
            -*)
                log_error "Unknown option: $1"
                exit 1
                ;;
            *)
                positional+=("$1")
                shift
                ;;
        esac
    done

    set -- "${positional[@]}"
}

show_help() {
    cat << 'HELP'
Usage: complex_script.sh [OPTIONS] [ARGS...]

Options:
    -c, --config FILE   Configuration file
    -d, --debug         Enable debug mode
    -h, --help          Show this help
    -v, --verbose       Verbose output

Examples:
    ./complex_script.sh -c config.ini
    ./complex_script.sh --debug -v input/
HELP
}

# Main entry point
main() {
    log_info "Starting benchmark script"

    parse_args "$@"

    if [[ -n "${CONFIG_FILE:-}" ]]; then
        parse_config "$CONFIG_FILE"
    fi

    # Demonstrate various shell features
    local start_time
    start_time=$(date +%s)

    # Brace expansion
    echo {a,b,c}{1,2,3}

    # Process substitution
    diff <(echo "a") <(echo "b") || true

    # Extended globbing (if enabled)
    shopt -s extglob 2>/dev/null || true

    # Parameter expansion
    local str="Hello World"
    echo "${str^^}"           # uppercase
    echo "${str,,}"           # lowercase
    echo "${str:0:5}"         # substring
    echo "${str/World/Bash}"  # replace
    echo "${str:-default}"    # default value
    echo "${#str}"            # length

    # Array operations
    local -a numbers=(1 2 3 4 5)
    echo "Array: ${numbers[*]}"
    echo "Length: ${#numbers[@]}"
    echo "Slice: ${numbers[@]:1:3}"

    # Associative arrays
    local -A map
    map[key1]="value1"
    map[key2]="value2"
    for key in "${!map[@]}"; do
        echo "$key => ${map[$key]}"
    done

    local end_time
    end_time=$(date +%s)
    local duration=$((end_time - start_time))

    generate_report "success" "Completed in ${duration}s"
    log_info "Benchmark complete"
}

# Run if executed directly
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
