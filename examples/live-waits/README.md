# Live waits: a worked example

An English mathematical note using SunQuarTeX's native theorem, equation, figure,
and table references; a computed Matplotlib figure; bibliography; and annotated
Lean source inclusion. The same source renders to HTML, PDF, and GitHub Markdown.
The PDF overrides the shared theorem counter so its theorem numbers agree with
the other two formats.

From the repository root, with Quarto and `uv` installed:

```sh
uv sync
uv run quarto render examples/live-waits/live-waits.qmd --to html --quiet
uv run quarto render examples/live-waits/live-waits.qmd --to pdf --quiet
uv run quarto render examples/live-waits/live-waits.qmd --to gfm --quiet
```

PDF also needs a TeX installation; `quarto install tinytex` is one option.
Outputs are placed in `_output/examples/live-waits/`. The HTML embeds its visual
assets; keep the three adjacent `.lean` files when sharing its source links.
When sharing the Markdown, also keep its `live-waits_files/` image directory.

Rendering includes Lean code as text and does not check it. To check the three
Lean files, use a built checkout of `lunaluteus/ninegates-lean4` at
`8e374e6fb141c0c6a8f0ac7689652c154739d146` (Lean 4.35.0). From that checkout,
run `lake env lean /absolute/path/to/FILE.lean` for each of `Capacity.lean`,
`LiveMaximum.lean`, and `CopyBound.lean`.

The mathematical reference is Xue and Zhong, *Beyond Nine Gates*,
[arXiv:2611.06944v1](https://arxiv.org/abs/2611.06944v1). The additional Lean
files establish the existence interval and copy-cap corollaries; they are a
separate experiment from the pending upstream formalization PR.
