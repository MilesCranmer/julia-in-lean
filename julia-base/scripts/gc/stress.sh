#!/usr/bin/env bash
# Seeded runtime stress. Each run retains its command, output and watchdog log.
# Exit 0: all workloads passed; 1: crash/timeout candidate; 2: setup/application error.
# A candidate needs investigation and does not establish a GC bug.
set -euo pipefail

usage() {
    echo "usage: $0 --julia PATH --out NEW_DIRECTORY --seed UINT64 [--rounds N] [--timeout SECONDS] [--threads N] [--case NAME] [--gcthreads N,M]" >&2
    echo "cases: allocation finalizers tasks remembered sweep foreign; repeat --case or --gcthreads to select a matrix" >&2
    exit 2
}

julia= out= seed= rounds=32 seconds=180 threads=4
cases=() collectors=()
while (($#)); do
    (($# >= 2)) || usage
    case "$1" in
        --julia) julia=$2 ;;
        --out) out=$2 ;;
        --seed) seed=$2 ;;
        --rounds) rounds=$2 ;;
        --timeout) seconds=$2 ;;
        --threads) threads=$2 ;;
        --case) cases+=("$2") ;;
        --gcthreads) collectors+=("$2") ;;
        *) usage ;;
    esac
    shift 2
done
[[ -n "$julia" && -n "$out" && "$seed" =~ ^(0|[1-9][0-9]*)$ ]] || usage
[[ ${#seed} -lt 20 || (${#seed} -eq 20 && "$seed" < 18446744073709551616) ]] || usage
for value in "$rounds" "$seconds" "$threads"; do
    [[ "$value" =~ ^[1-9][0-9]*$ && ${#value} -le 7 ]] || usage
done
((threads >= 2)) || usage
if ((${#cases[@]} == 0)); then cases=(allocation finalizers tasks remembered sweep foreign); fi
if ((${#collectors[@]} == 0)); then collectors=(1,0 2,0 2,1 4,1); fi
for workload in "${cases[@]}"; do
    case "$workload" in allocation|finalizers|tasks|remembered|sweep|foreign) ;; *) usage ;; esac
done
for collector in "${collectors[@]}"; do
    [[ "$collector" =~ ^[1-9][0-9]*,[01]$ ]] || usage
done
[[ -x "$julia" && ! -e "$out" ]] || { echo "Julia must be executable and the output directory must be new" >&2; exit 2; }
command -v timeout >/dev/null || { echo "GNU timeout is required" >&2; exit 2; }
julia=$(cd "$(dirname "$julia")" && pwd)/$(basename "$julia")
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
mkdir -p "$out"
out=$(cd "$out" && pwd)
{
    printf 'julia=%s\nseed=%s\nrounds=%s\ntimeout=%s\nthreads=%s\n' "$julia" "$seed" "$rounds" "$seconds" "$threads"
    printf 'gcthreads=%s\ncases=%s\n' "${collectors[*]}" "${cases[*]}"
    uname -a
    printf 'core_limit='; ulimit -c
    if [[ -r /proc/sys/kernel/core_pattern ]]; then
        printf 'core_pattern='; head -1 /proc/sys/kernel/core_pattern
    fi
    for name in JULIA_GC_ALLOC_POOL JULIA_GC_ALLOC_OTHER JULIA_GC_ALLOC_PRINT JULIA_GC_NO_GENERATIONAL JULIA_GC_WAIT_FOR_DEBUGGER; do
        if [[ -n "${!name-}" ]]; then printf '%s=%s\n' "$name" "${!name}"; fi
    done
    sha256sum "$root/repro/gc-stress-runtime.jl" "$root/repro/gc-foreign-thread.c" "$root/scripts/gc/stress.sh"
} > "$out/metadata.txt"
printf 'case\tgcthreads\tstatus\texit\tlog\n' > "$out/summary.tsv"

run_logged() {
    local directory=$1 limit=$2
    shift 2
    mkdir "$directory"
    printf '%q ' "$@" > "$directory/command.txt"
    printf '\n' >> "$directory/command.txt"
    set +e
    LC_ALL=C timeout --verbose --signal=QUIT --kill-after=10s "${limit}s" \
        bash -c 'directory=$1; shift; printf "%s\n" "$$" > "$directory/pid"; cd "$directory"; exec "$@" > output.log 2>&1' \
        _ "$directory" "$@" > "$directory/watchdog.stdout" 2> "$directory/watchdog.log"
    exit_code=$?
    set -e
}

library=$out/gc-foreign-thread.so
for workload in "${cases[@]}"; do
    if [[ "$workload" == foreign ]]; then
        run_logged "$out/foreign-build" 60 "${CC:-cc}" -std=c11 -Wall -Wextra -Werror -O2 -fPIC -shared -pthread \
            "$root/repro/gc-foreign-thread.c" -o "$library"
        if ((exit_code != 0)); then
            echo "Foreign helper build failed; see $out/foreign-build/output.log" >&2
            exit 2
        fi
        break
    fi
done

result=0
for workload in "${cases[@]}"; do
    for collector in "${collectors[@]}"; do
        directory=$out/$workload-gc${collector/,/_}
        run_logged "$directory" "$seconds" "$julia" --project=. --startup-file=no --history-file=no --check-bounds=yes \
            "--threads=$threads" "--gcthreads=$collector" "$root/repro/gc-stress-runtime.jl" \
            "$workload" "$seed" "$rounds" "$library"
        if grep -Eq 'sending signal (QUIT|KILL)' "$directory/watchdog.log"; then
            status=timeout-candidate
        elif ((exit_code == 134)) && grep -Eq 'Assertion .*failed|Assertion failure|assertion .*failed' "$directory/output.log"; then
            status=native-assert-candidate
        elif [[ "$exit_code" =~ ^(132|133|134|135|136|139|159)$ ]] && \
            { grep -Eq '^\[[0-9]+\] signal \((4|5|6|7|8|11|31)\):' "$directory/output.log" || \
              grep -q 'monitored command dumped core' "$directory/watchdog.log"; }; then
            status=crash-candidate
        elif ((exit_code != 0)); then
            status=application-error
        elif ! grep -Eq "^GC_STRESS_OK workload=$workload seed=$seed rounds=$rounds$" "$directory/output.log"; then
            status=incomplete
        else
            status=pass
        fi
        case "$status" in
            *-candidate) if ((result == 0)); then result=1; fi ;;
            application-error|incomplete) result=2 ;;
        esac
        printf '%s\t%s\t%s\t%s\t%s\n' "$workload" "$collector" "$status" "$exit_code" "$directory/output.log" >> "$out/summary.tsv"
        printf '%s gcthreads=%s %s exit=%s\n' "$workload" "$collector" "$status" "$exit_code"
    done
done
echo "Results: $out/summary.tsv"
exit "$result"
