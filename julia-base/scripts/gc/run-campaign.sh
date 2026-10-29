#!/usr/bin/env bash
# Smoke and campaign stress runs for each Julia binary:
#   scripts/gc/run-campaign.sh OUTPUT_ROOT LABEL JULIA [LABEL JULIA ...]
set -uo pipefail
(($# >= 3 && $# % 2 == 1)) || exit 2
base=$1
shift
root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
stamp=$(date -u +%Y%m%dT%H%M%SZ)
result=0
while (($#)); do
    label=$1 binary=$2
    shift 2
    [[ "$label" =~ ^[A-Za-z0-9_-]+$ && -x "$binary" ]] || exit 2
    directory=$base/$label/$stamp
    mkdir -p "$(dirname "$directory")"
    mkdir "$directory" || exit 2
    {
        hostname
        date -u +%FT%TZ
        printf 'binary=%s\n' "$binary"
        timeout --signal=QUIT --kill-after=10s 30s "$binary" --project=. --startup-file=no --history-file=no \
            -e 'println("VERSION=", VERSION); println("COMMIT=", Base.GIT_VERSION_INFO.commit)'
    } > "$directory/version.log" 2>&1
    version_status=$?
    printf 'RUN_DIRECTORY %s\n' "$directory"
    head -10 "$directory/version.log"
    if ((version_status != 0)); then
        result=2
        continue
    fi
    for phase in smoke campaign; do
        rounds=1
        [[ "$phase" == campaign ]] && rounds=16
        bash "$root/scripts/gc/stress.sh" --julia "$binary" --out "$directory/$phase" \
            --seed 20261024 --threads 8 --rounds "$rounds" --timeout 180 \
            > "$directory/$phase.driver.log" 2>&1
        phase_status=$?
        printf 'PHASE %s %s exit=%s\n' "$label" "$phase" "$phase_status"
        tail -30 "$directory/$phase.driver.log"
        if ((phase_status > result)); then result=$phase_status; fi
        if [[ -f "$directory/$phase/summary.tsv" ]]; then
            awk -F '\t' 'NR == 1 || $3 != "pass"' "$directory/$phase/summary.tsv"
            while IFS=$'\t' read -r workload collector status code log; do
                [[ "$workload" == case || "$status" == pass ]] && continue
                printf 'ABNORMAL_LOG %s\n' "$log"
                tail -100 "$log"
            done < "$directory/$phase/summary.tsv"
        fi
    done
done
exit "$result"
