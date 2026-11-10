#!/bin/bash
# Run the compiler-lattice reproducers on the pinned Julia, julia +1.13 and julia +nightly.
cd "$(dirname "$0")/../.."
for f in repro/compiler-al-is-valid-lattice-types.jl repro/compiler-tl-sqsub-transitive.jl \
         repro/compiler-tl-sqsub-widenconst-upper.jl repro/compiler-tl-sqsub-bottom-least-optimizer.jl \
         repro/compiler-tl-widenconditional-extract.jl repro/compiler-tl-sqsub-any-top-optimizer.jl; do
  for j in pinned 1.13 nightly; do
    echo "=== $f [$j]"
    if [ $j = pinned ]; then J=${JULIA:?set JULIA to a Julia built at the pinned commit}; else J="$HOME/.juliaup/bin/julia +$j"; fi
    timeout 300 $J --startup-file=no -e 'println(VERSION, " ", Base.GIT_VERSION_INFO.commit)' 2>&1
    timeout 300 $J --startup-file=no "$f" 2>&1 | tail -8
  done
done
