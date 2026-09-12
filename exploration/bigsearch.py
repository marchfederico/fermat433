# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

import math, time
import numpy as np
Bd = 250
def F0(a, b, c): return -4*a**3*c - 6*a**2*b**2 - 24*a*b*c**2 - 8*b**3*c - 4*c**4
def F1(a, b, c): return -4*a**3*b + 4*a**3*c + 6*a**2*b**2 - 12*a**2*c**2 - 24*a*b**2*c + 24*a*b*c**2 - 2*b**4 + 8*b**3*c - 16*b*c**3 + 4*c**4
rng = np.arange(-Bd, Bd + 1, dtype=object)
t0 = time.time()
for name, F in (("C_0", F0), ("C_1", F1)):
    found = []
    bb, cc = np.meshgrid(np.arange(-Bd, Bd + 1, dtype=np.int64), np.arange(-Bd, Bd + 1, dtype=np.int64), indexing="ij")
    for a in range(0, Bd + 1):
        vals = F(np.int64(a), bb, cc)
        for i, j in np.argwhere(vals == 0):
            g = (a, int(bb[i, j]), int(cc[i, j]))
            if g == (0, 0, 0) or math.gcd(math.gcd(g[0], g[1]), g[2]) != 1:
                continue
            if next(v for v in g if v != 0) < 0:
                continue
            assert F(*g) == 0
            found.append(g)
    print(f"{name}: primitive points with max |coordinate| <= {Bd}: {found}  [{time.time() - t0:.0f}s]", flush=True)
