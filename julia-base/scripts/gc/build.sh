#!/bin/bash
# Builds Julia master (bbfa0ce4150) with assertions and GC verification:
#
#   scripts/gc/build.sh BUILD_DIR
#
#   assert/  FORCE_ASSERTIONS=1 full build
#   verify/  copy of assert/ with GC verification, debug environment and parent checks
#   verify-memfence/  the same diagnostics plus pool-header checks
#   verify-memfence-no-debug-env/  pool-header checks without the GC debug environment
# Run either verifier with --gcthreads=1,0: GC_VERIFY requires single-threaded GC.
# The compiler needs a static libstdc++, which libjulia-internal links.
set -euo pipefail
B=${1:?usage: scripts/gc/build.sh BUILD_DIR}
COMMIT=bbfa0ce4150
mkdir -p "$B"
trap 'printf "%s\n" "$?" > "$B/build.exit"' EXIT
cd "$B"
if [[ ! -d assert/.git ]]; then
    git clone --quiet https://github.com/JuliaLang/julia assert
fi
cd assert
git fetch --quiet origin
git checkout --quiet "$COMMIT"
printf '%s\n' 'FORCE_ASSERTIONS=1' > Make.user
if [[ ! -x usr/bin/julia ]] || [[ ! -s .built-$COMMIT ]]; then
    make -j32 > "$B/assert-build.log" 2>&1
    ./usr/bin/julia --startup-file=no -e 'println(VERSION, " ", Base.GIT_VERSION_INFO.commit_short)' > .built-$COMMIT
fi
cat .built-$COMMIT

for flavor in verify-memfence verify verify-memfence-no-debug-env; do
    cd "$B"
    if [[ ! -s $flavor/.verified-$COMMIT ]]; then
        if [[ ! -d $flavor ]]; then
            cp -a assert "$flavor"
        fi
        cd "$flavor"
        [[ $(git rev-parse --short=11 HEAD) == "$COMMIT" ]]
        extra=
        if [[ $flavor == verify-memfence* ]]; then extra=' -DMEMFENCE'; fi
        {
            printf '%s\n' 'FORCE_ASSERTIONS=1' 'WITH_GC_VERIFY=1'
            if [[ $flavor != verify-memfence-no-debug-env ]]; then
                printf '%s\n' 'WITH_GC_DEBUG_ENV=1'
            fi
            printf 'JL_CFLAGS = -DGC_ASSERT_PARENT_VALIDITY%s\n' "$extra"
            printf 'JL_CXXFLAGS = -DGC_ASSERT_PARENT_VALIDITY%s\n' "$extra"
        } > Make.user
        # The diagnostic flags do not change layouts; rebuild all runtime/codegen objects.
        touch src/*.c src/*.cpp
        make -C src -j32 > "$B/$flavor-build.log" 2>&1
        ./usr/bin/julia --startup-file=no --threads=1 --gcthreads=1,0 \
            -e 'println(VERSION, " ", Base.GIT_VERSION_INFO.commit_short, " ", ARGS[1])' \
            "$flavor" > .verified-$COMMIT
    fi
    cat "$B/$flavor/.verified-$COMMIT"
done
echo BUILD-DONE
