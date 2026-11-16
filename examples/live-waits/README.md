# Live waits: a worked example

An English mathematical note using SunQuarTeX's native theorem, equation, figure,
and table references; a computed Matplotlib figure; bibliography; and annotated
Lean source inclusion. The companion addendum `arbitrary-cap.qmd` extends the
existence interval to every copy cap. Both sources render to HTML, PDF, and GitHub Markdown.
The PDF overrides the shared theorem counter so its theorem numbers agree with
the other two formats.

From the repository root, with Quarto and `uv` installed:

```sh
uv sync
uv run quarto render examples/live-waits/live-waits.qmd --to all --quiet
uv run quarto render examples/live-waits/arbitrary-cap.qmd --to all --quiet
```

PDF also needs a TeX installation; `quarto install tinytex` is one option.
Outputs are placed in `_output/examples/live-waits/`. The HTML embeds its visual
assets; keep the adjacent `.lean` files and `check-lean.py` when sharing source links.
When sharing the Markdown, also keep its `live-waits_files/` image directory.
Links between the two rendered notes point to their HTML companions.

Rendering includes Lean code as text and does not check it. With a built checkout
of `lunaluteus/ninegates-lean4` at
`7b379afe7f54f34c59c8abdfc8e6fa5f0bee952a` (Lean 4.35.0), run:

```sh
uv run python examples/live-waits/check-lean.py --library /path/to/ninegates-lean4
```

The checker builds all four Lean modules in a temporary directory with strict
linters, then audits seven declarations against the three standard axioms.
Use `--lake /path/to/lake` if the pinned toolchain is not on `PATH`.

The mathematical reference is Xue and Zhong, *Beyond Nine Gates*,
[arXiv:2611.06944v1](https://arxiv.org/abs/2611.06944v1). The additional Lean
files establish the existence interval and copy-cap corollaries; they are a
separate experiment from the pending upstream formalization PR.
