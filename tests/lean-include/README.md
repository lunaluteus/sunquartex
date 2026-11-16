# `lean-include` regression check

Run from the repository root:

```sh
uv run python tests/lean-include/check.py
```

Use `--quarto /path/to/quarto` to select a specific Quarto installation. The
optional `--lean /path/to/lean` also compiles the fixture; it needs only Lean's
standard library, and was checked with Lean 4.35.0.

The test renders a temporary document through the real shortcode and checks
that declarations and line comments remain inside code blocks. Its fixture
includes delimiter text inside ordinary, escaped, raw, and nested interpolated
strings; a quote character; a quoted identifier; nested documentation; an empty
module comment; and a comment with no whitespace after its opening delimiter.
An unterminated block comment must fail with a diagnostic naming its source.

The original parser misclassified `"/- not documentation -/"` as prose and could
silently discard the remainder of a file after `"/-"`. The fixture compiles in
Lean, so the regression check exercises valid source as well as malformed input.

Tested with Quarto 1.8.27 and the repository CI's pinned Quarto 1.11.9.
