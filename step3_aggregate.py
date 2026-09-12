#!/usr/bin/env python3
# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

"""Aggregate the per-disk output of step3_run_*.gp: Strassman indices, Z_p-zeros of rho, rational-looking a(z)."""
import glob
import re
from collections import Counter

lines = []
for fn in sorted(glob.glob("step3_out_*.txt")):
    lines += [l.rstrip("\n") for l in open(fn) if l.startswith(("DISK", "INF"))]

errors = [l for l in lines if " ERROR " in l]
good = [l for l in lines if " ERROR " not in l]
print(f"disks: {len(lines)}  (errors: {len(errors)})")
for l in errors:
    print("  ", l[:200])

strass = Counter()
minval = Counter()
nroots_total = 0
nroots_hist = Counter()
rational = []
for l in good:
    m = re.search(r"strassman=(\d+) minval=(-?\d+) .*? nroots=(\d+) roots=(.*)$", l)
    st, mv, nr, roots = int(m.group(1)), int(m.group(2)), int(m.group(3)), m.group(4)
    strass[st] += 1
    minval[mv] += 1
    nroots_total += nr
    nroots_hist[nr] += 1
    x0 = re.search(r"x0=(\w+) sg=(-?\d)", l)
    # each root entry ends with ", <rat flag>, <rational pair or 0>]"
    for entry in re.finditer(r"\[([^\[\]]*?), ([^\[\]]*?), ([^\[\]]*?), ([01]), (\[[^\]]*\]|0)\]", roots):
        if entry.group(4) == "1":
            rational.append((x0.group(1), x0.group(2), entry.group(5), entry.group(1)[:40]))

print("Strassman index histogram:", dict(sorted(strass.items())))
print("minimal-valuation histogram:", dict(sorted(minval.items())))
print(f"Z_p-zeros of rho found: {nroots_total}  per-disk histogram: {dict(sorted(nroots_hist.items()))}")
print(f"rational-looking a(z) (algdep coefficients < 10^6): {len(rational)}")
for r in rational:
    print(f"   disk x0={r[0]} sg={r[1]}  a(z) = {r[2]}   T = {r[3]}")
