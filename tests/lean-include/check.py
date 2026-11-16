"""Exercise the actual Quarto shortcode; no third-party Python modules needed."""

import argparse
from pathlib import Path
import re
import subprocess
import tempfile


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--quarto', default='quarto')
    parser.add_argument('--lean', help='Optionally check the fixture with this Lean executable')
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    source = (here / 'fixture.lean').read_text()
    if args.lean:
        subprocess.run([args.lean, str(here / 'fixture.lean')], check=True)

    with tempfile.TemporaryDirectory(prefix='sunquartex-lean-include-') as directory:
        root = Path(directory)
        (root / 'include.lua').write_bytes((here.parents[1] / '_assets/lean-include.lua').read_bytes())
        (root / 'fixture.lean').write_text(source)
        (root / 'note.qmd').write_text(
            '---\nformat: gfm\nshortcodes: [include.lua]\n---\n'
            '\n{{< lean-include fixture.lean >}}\n'
        )
        subprocess.run([args.quarto, 'render', 'note.qmd', '--quiet'], cwd=root, check=True)
        markdown = (root / 'note.md').read_text()
        blocks = re.findall(r'```\s*lean\n(.*?)\n```', markdown, flags=re.S)
        code = '\n'.join(blocks)
        prose = re.sub(r'```\s*lean\n.*?\n```', '', markdown, flags=re.S)

        # Every declaration must survive, byte for byte, in a Lean code block.
        for line in source.splitlines():
            if line.startswith(('def ', 'namespace ', 'end ', '-- ')):
                assert line in code, f'Lost or reclassified Lean code: {line}'
        assert 'not documentation' not in prose
        assert 'Outer documentation before the nested comment.' in prose
        assert 'Outer documentation after the nested comment.' in prose
        assert 'Outer documentation' not in code
        assert 'No leading whitespace is required.' in prose
        assert '\n-/\n' not in code

        # An unterminated comment must produce a diagnostic, never a partial document.
        (root / 'fixture.lean').write_text('def before : Nat := 1\n/- Unclosed comment\n')
        result = subprocess.run(
            [args.quarto, 'render', 'note.qmd'], cwd=root,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
        assert result.returncode != 0, 'Unclosed comment was silently truncated'
        assert 'fixture.lean' in result.stdout, result.stdout
    print('lean-include: declarations preserved, comments rendered, malformed input rejected')


if __name__ == '__main__':
    main()
