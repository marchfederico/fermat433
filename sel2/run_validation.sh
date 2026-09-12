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
rm -f results2_all.txt
for i in $(seq -f "%02g" 0 23); do
  mkdir -p w$i && cp pipeline2.gp w$i/pipeline2.gp && cp curve_$i.gp w$i/curve_input.gp && rm -f w$i/results2.txt
  (cd w$i && gp -q pipeline2.gp < /dev/null > run.log 2>&1; cat results2.txt >> ../results2_all.txt 2>/dev/null || echo "$(grep -o 'TAG = \"[^\"]*\"' curve_input.gp) FAILED: $(grep -v Warning run.log | grep -m1 -i error | cut -c1-120)" >> ../results2_all.txt) &
  while [ "$(jobs -r | wc -l)" -ge 6 ]; do sleep 5; done
done
wait
echo VALIDATION2-DONE >> results2_all.txt
