#!/usr/bin/env bash
# The runtime's mem* against libc, byte for byte, on this machine's architecture (a cold machine runs it on x86_64 and aarch64). The native part of scripts/rt/runtime/rt.c (the native mem* and memcmp) is
# compiled alone under other names; libc is the oracle. Real behaviour caught: a wrong copy at some size, alignment or overlap.
set -euo pipefail
here=$(cd "$(dirname "$0")/.." && pwd); t=$(mktemp -d); trap 'rm -rf "$t"' EXIT
cc=${CC:-clang}
{ printf '#include <stddef.h>\n#include <stdint.h>\n'
  sed -n '/^typedef unsigned char v16_t/,/^#endif/p' "$here/scripts/rt/runtime/rt.c" | sed '$d'
  sed -n '/^int memcmp/,/^}/p' "$here/scripts/rt/runtime/rt.c"; } > "$t/mem.c"
grep -q 'memcmp' "$t/mem.c" && grep -q 'memset' "$t/mem.c" && grep -q 'memmove' "$t/mem.c" || { echo "test_mem: cannot extract the mem* functions from rt.c" >&2; exit 1; }
"$cc" -O2 -ffreestanding -fno-builtin -Dmemcpy=rt_memcpy -Dmemmove=rt_memmove -Dmemset=rt_memset -Dmemcmp=rt_memcmp -c "$t/mem.c" -o "$t/mem.o"
"$cc" -O2 -fno-builtin "$here/tests/mem_ref.c" "$t/mem.o" -o "$t/mem_ref"
"$t/mem_ref"
