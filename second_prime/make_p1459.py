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

"""Second-prime check of Part C: build copies of the quadratic Chabauty pipeline (step1_character.gp, step2b.gp,
step3_*.gp, step4_*.gp) with p = 1459 in place of 499, for B- and for the twist C+, and a driver run.sh per curve.
1459 is the next prime after 499 that splits completely in the degree-12 field L and at which C3 has no root
(so no Weierstrass disks).  Usage: python3 make_p1459.py <target dir>; then <target>/Bminus/run.sh, <target>/Cplus/run.sh."""
import os, re, sys
SRC = os.path.dirname(os.path.dirname(os.path.abspath(__file__))) + "/"
P = 1459
OUT = sys.argv[1] if len(sys.argv) > 1 else "."
RUN = '''#!/bin/zsh
cd "$(dirname "$0")"
gp -q step1_character.gp < /dev/null > step1.log 2>&1
gp -q step2b.gp < /dev/null > step2b.log 2>&1
for c in 0 1 2 3; do rm -f step3_out_$c.txt; gp -q step3_run_$c.gp < /dev/null > step3_run_$c.log 2>&1 & done
gp -q step4_scan.gp < /dev/null > step4_scan.log 2>&1 &
wait
python3 step3_aggregate.py > step3_aggregate.out 2>&1
python3 mkcands.py > mkcands.out 2>&1
gp -q step4_sieve.gp < /dev/null > step4_sieve.out 2>&1
echo PIPELINE-DONE >> step4_sieve.out
'''
MKC = r'''import re, glob
P = __P__
def padic_int(s):
    s = s.strip()
    if s.startswith("O("): return 0
    total = 0
    for m in re.finditer(r"(\d+)(?:\*__P__\^(\d+)|\*__P__)?", s.split("+ O(")[0]):
        c = int(m.group(1)); k = int(m.group(2)) if m.group(2) else (1 if "*__P__" in m.group(0) else 0)
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
print("candidates:", len(cands), "rational-looking:", sum(c[4] for c in cands))
'''.replace("__P__", str(P))
for curve in ("Bminus", "Cplus"):
    d = os.path.join(OUT, curve); os.makedirs(d, exist_ok=True)
    def sub(text):
        text = text.replace("p = 499;", "p = %d;" % P)
        text = re.sub(r"\b499\b", str(P), text)
        if curve == "Cplus":
            text = text.replace("f1 = -17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40;",
                                "f1 = -2*(-17*x^6 + 72*x^5 - 90*x^4 - 40*x^3 + 180*x^2 - 144*x + 40);")
            text = text.replace("pts = [[1, 1], [-1, 15]];", "pts = [[6/5, 172/125], [2, 12]];")
            text = text.replace("issquare(Mod(-17, p))", "issquare(Mod(34, p))")
            text = text.replace("issquare(Mod(-17, q)), my(s17 = sqrt(Mod(-17, q)))", "issquare(Mod(34, q)), my(s17 = sqrt(Mod(34, q)))")
        return text
    for f in ("step1_character.gp", "step2b.gp", "step3_setup.gp", "step3_disk.gp", "step3_run.gp", "step4_scan.gp", "step4_sieve.gp", "step3_aggregate.py"):
        t = open(SRC + f).read()
        if f == "step4_scan.gp":
            t = t.replace("forprime (q = 5, 300000,", "forprime (q = 5, 1500000,")
        open(os.path.join(d, f), "w").write(sub(t))
    nch = 4; size = (P + nch - 1) // nch
    for c in range(nch):
        lo, hi = c*size, min((c+1)*size - 1, P - 1)
        body = open(os.path.join(d, "step3_run.gp")).read().replace("read(CHUNK);", "")
        open(os.path.join(d, "step3_run_%d.gp" % c), "w").write('LO = %d; HI = %d; OUT = "step3_out_%d.txt";\n' % (lo, hi, c) + body)
    open(os.path.join(d, "mkcands.py"), "w").write(MKC)
    open(os.path.join(d, "run.sh"), "w").write(RUN); os.chmod(os.path.join(d, "run.sh"), 0o755)
print("built", OUT)
