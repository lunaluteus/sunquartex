# Live waits: a worked example

An English mathematical note using SunQuarTeX's native theorem, equation, figure,
and table references; a computed Matplotlib figure; bibliography; and annotated
Lean source inclusion. The companion addendum `arbitrary-cap.qmd` extends the
existence interval to every copy cap and gives an explicit three-rank duality.
The third note `three-ranks.qmd` counts all live hands on three ranks by a
disjoint box decomposition and proves the generating polynomial for individual
meld counts. It also identifies the sharp copy cap at which each fixed-meld count
stabilizes. The fourth note `copy-cap-stability.qmd` proves the sharp
stabilization cap at every higher order using a uniform coordinate bound and
an explicit extremal family. The fifth note `triplet-counting.qmd` gives a unique
bounded-core decomposition, an exact finite counting formula, a rational
generating series, and polynomial counts valid from two melds at order one
and from $5n-4$ at higher orders, with exact degree and leading coefficient.
The actual numerator degree determines the exact first polynomial index. It
also proves density one among uniformly sampled uncapped multiplicity vectors
of increasing size. All five sources render to HTML, PDF, and GitHub Markdown.
The PDF overrides the shared theorem counter so its theorem numbers agree with
the other two formats.

From the repository root, with Quarto and `uv` installed:

```sh
uv sync
uv run quarto render examples/live-waits/live-waits.qmd --to all --quiet
uv run quarto render examples/live-waits/arbitrary-cap.qmd --to all --quiet
uv run quarto render examples/live-waits/three-ranks.qmd --to all --quiet
uv run quarto render examples/live-waits/copy-cap-stability.qmd --to all --quiet
uv run quarto render examples/live-waits/triplet-counting.qmd --to all --quiet
```

PDF also needs a TeX installation; `quarto install tinytex` is one option.
Outputs are placed in `_output/examples/live-waits/`. The HTML embeds its visual
assets; keep the adjacent `.lean` files and `check-lean.py` when sharing source links.
When sharing the Markdown, also keep its `live-waits_files/` image directory.
Links between the rendered notes point to their HTML companions.

Rendering includes Lean code as text and does not check it. With a built checkout
of `lunaluteus/ninegates-lean4` at
`7b379afe7f54f34c59c8abdfc8e6fa5f0bee952a` (Lean 4.35.0), run:

```sh
uv run python examples/live-waits/check-lean.py --library /path/to/ninegates-lean4
```

The checker builds all fifteen Lean modules in a temporary directory with strict
linters, then audits ninety-one declarations against the three standard axioms.
Use `--lake /path/to/lake` if the pinned toolchain is not on `PATH`.
In a standalone export, run `python check-lean.py --library /path/to/ninegates-lean4`
from the exported folder instead.

The six-rank diagnostic in `six-rank-cores.cpp` and `six-rank-summary.py`
compares three winning algorithms and records a computed numerator. Its
finite core cardinalities are ordinary computational data, separate from the
Lean audit. See the final counting note for the reproduction commands.

The mathematical reference is Xue and Zhong, *Beyond Nine Gates*,
[arXiv:2611.06944v1](https://arxiv.org/abs/2611.06944v1). The additional Lean
files establish the existence interval and copy-cap corollaries; they are a
separate experiment from the pending upstream formalization PR.
