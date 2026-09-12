\\ Copyright (C) 2026 Marcello Federico
\\ SPDX-License-Identifier: GPL-3.0-or-later
\\
\\ This file is part of the fermat433 proof record
\\ <https://github.com/marchfederico/fermat433>.  It is free software: you may
\\ redistribute it and modify it under the terms of the GNU General Public
\\ License, either version 3 of the License or (at your option) any later
\\ version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
\\ the repository root, or <https://www.gnu.org/licenses/>.

F0 = -4*aa^3*cc - 6*aa^2*bb^2 - 24*aa*bb*cc^2 - 8*bb^3*cc - 4*cc^4;
AK0 = (0) + (-1/6)*w + (0)*w^2;
QC0 = [(0) + (0)*w + (1/36)*w^2, (0) + (0)*w + (1/9)*w^2, (0) + (0)*w + (-1/3)*w^2, (0) + (0)*w + (1/9)*w^2, (0) + (0)*w + (1/36)*w^2];
F1 = -4*aa^3*bb + 4*aa^3*cc + 6*aa^2*bb^2 - 12*aa^2*cc^2 - 24*aa*bb^2*cc + 24*aa*bb*cc^2 - 2*bb^4 + 8*bb^3*cc - 16*bb*cc^3 + 4*cc^4;
AK1 = (0) + (1/6)*w + (-1/6)*w^2;
QC1 = [(-1/9) + (1/18)*w + (1/36)*w^2, (2/9) + (-4/9)*w + (1/9)*w^2, (1/3) + (1/3)*w + (-1/3)*w^2, (-4/9) + (2/9)*w + (1/9)*w^2, (1/18) + (-1/9)*w + (1/36)*w^2];
KP0 = [[0,1,0],[1,0,-1],[1,0,0]];
KP1 = [[1,-2,0],[1,-1,2],[1,0,0],[1,1,0]];
