# Copyright (C) 2026 Marcello Federico
# SPDX-License-Identifier: GPL-3.0-or-later
#
# This file is part of the fermat433 proof record
# <https://github.com/marchfederico/fermat433>.  It is free software: you may
# redistribute it and modify it under the terms of the GNU General Public
# License, either version 3 of the License or (at your option) any later
# version.  It is distributed WITHOUT ANY WARRANTY.  See the LICENSE file at
# the repository root, or <https://www.gnu.org/licenses/>.

# Reproducible build of the paper.
#
#   make            build fermat433.pdf (does nothing if the source is unchanged)
#   make check      confirm the build is byte-for-byte reproducible
#   make clean      remove build intermediates
#   make distclean  also remove the PDF
#
# Why SOURCE_DATE_EPOCH is pinned: the PDF is tracked in git, and without a
# fixed epoch every rebuild stamps a fresh CreationDate and document /ID into
# the file.  Git then reports the PDF as modified even when nothing about the
# paper changed -- 3 of its 143 streams differ, and all three are
# cross-reference and metadata plumbing rather than content.  With the epoch
# pinned the output depends only on the source, so the PDF shows up in a diff
# exactly when the paper actually changed.
#
# 1789171200 = 2026-09-12T00:00:00Z, the date on the paper.  The value is
# otherwise arbitrary and affects nothing a reader sees; override it with
# `make SOURCE_DATE_EPOCH=<seconds>` if you ever want the internal timestamp
# to move.
#
# Requires tectonic (brew install tectonic).  Any other engine will produce
# different bytes, so rebuild with the same one the tracked PDF was built with.

NAME              := fermat433
TECTONIC          ?= tectonic
SOURCE_DATE_EPOCH ?= 1789171200
export SOURCE_DATE_EPOCH

.PHONY: all check clean distclean

all: $(NAME).pdf

$(NAME).pdf: $(NAME).tex
	$(TECTONIC) -X compile $<

# Build twice into scratch directories and compare.  This uses the same pinned
# epoch as a normal build, so a failure here means genuine non-determinism in
# the toolchain, not merely a difference in wall-clock time between the runs.
check: $(NAME).tex
	@rm -rf .check-a .check-b
	@mkdir -p .check-a .check-b
	@$(TECTONIC) -X compile -o .check-a $(NAME).tex >/dev/null 2>&1
	@$(TECTONIC) -X compile -o .check-b $(NAME).tex >/dev/null 2>&1
	@if cmp -s .check-a/$(NAME).pdf .check-b/$(NAME).pdf; then \
		echo "reproducible: two builds are byte identical"; \
		echo "  sha256  `shasum -a 256 .check-a/$(NAME).pdf | cut -d' ' -f1`"; \
		rm -rf .check-a .check-b; \
	else \
		echo "NOT reproducible: the two builds differ"; \
		echo "  left in .check-a/ and .check-b/ for inspection"; \
		exit 1; \
	fi

clean:
	rm -f $(NAME).aux $(NAME).log $(NAME).out $(NAME).toc \
	      $(NAME).bbl $(NAME).blg $(NAME).synctex.gz
	rm -rf .check-a .check-b

distclean: clean
	rm -f $(NAME).pdf
