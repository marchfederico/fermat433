#!/bin/zsh
# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

cd "$(dirname "$0")"
# 1. chunks (each does its own setup)
for c in 0 1 2 3; do lo=$((c*125)); hi=$((c*125+124)); [ $c -eq 3 ] && hi=498
  { printf 'LO = %d; HI = %d; OUT = "step3_out_%d.txt";\n' $lo $hi $c; sed 's/read(CHUNK);//' step3_run.gp; } > step3_run_$c.gp
  rm -f step3_out_$c.txt; gp -q step3_run_$c.gp < /dev/null > step3_run_$c.log 2>&1 &
done
gp -q step4_scan.gp < /dev/null > step4_scan.log 2>&1 &
wait
python3 step3_aggregate.py > step3_aggregate.out 2>&1
python3 - <<'PY'
import re, glob
P = 499
def padic_int(s):
    s = s.strip()
    if s.startswith("O("): return 0
    total = 0
    for m in re.finditer(r"(\d+)(?:\*499\^(\d+)|\*499)?", s.split("+ O(")[0]):
        c = int(m.group(1)); k = int(m.group(2)) if m.group(2) else (1 if "*499" in m.group(0) else 0)
        total += c * P**k
    return total
cands = []
for fn in sorted(glob.glob("step3_out_*.txt")):
    for l in open(fn):
        if not l.startswith(("DISK", "INF")): continue
        x0 = re.search(r"x0=(\w+) sg=(-?\d)", l); roots = l.split("roots=", 1)[1]
        for e in re.finditer(r"\[([^\[\]]*?), ([^\[\]]*?), ([^\[\]]*?), ([01]), (\[[^\]]*\]|0)\]", roots):
            cands.append((x0.group(1), int(x0.group(2)), padic_int(e.group(2)), padic_int(e.group(3)), int(e.group(4))))
open("cands.gp", "w").write("cands = [" + ", ".join('["%s", %d, %d, %d, %d]' % c for c in cands) + "];\n")
print("twist candidates:", len(cands), "rational-looking:", sum(c[4] for c in cands))
PY
gp -q step4_sieve.gp < /dev/null > step4_sieve.out 2>&1
echo TWIST-PIPELINE-DONE >> step4_sieve.out
