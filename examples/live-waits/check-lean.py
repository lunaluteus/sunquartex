"""Check the note's Lean sources against a built ninegates-lean4 checkout."""

import argparse
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


SOURCES = ('Capacity.lean', 'LiveMaximum.lean', 'CopyBound.lean', 'CapacitySpectrum.lean',
           'OrderOneDuality.lean', 'OrderOneBoxes.lean', 'OrderOnePolynomial.lean',
           'OrderOneStability.lean', 'CopyCapStability.lean',
           'TripletCore.lean', 'TripletCounting.lean')
AUDITED = ('SunQuarTeX.Examples.live_capacity',) + tuple(
    f'Mahjong.VirtualHand.LiveSpectrum.{name}' for name in
    ('layer_sequential', 'add_layer', 'exists_live_iff', 'maximum', 'extremal_apply', 'extremal_live')
) + tuple(f'Mahjong.VirtualHand.OrderOne.{name}' for name in
          ('fixedClass_dual', 'dual_involutive', 'size_dual', 'dual_live',
           'liveDualEquiv', 'live_card_symmetry')) + tuple(
    f'Mahjong.VirtualHand.OrderOne.Boxes.{name}' for name in
    ('encode_live', 'liveBoxEquiv', 'total_live_card', 'total_live_card_mod_zero',
     'total_live_card_mod_one', 'total_live_card_mod_two')
) + tuple(
    f'Mahjong.VirtualHand.OrderOne.Generating.{name}' for name in
    ('livePolynomial_formula', 'livePolynomial_coeff', 'livePolynomial_eval_one',
     'livePolynomial_seven', 'livePolynomial_coeff_symmetry')
) + tuple(
    f'Mahjong.VirtualHand.OrderOne.Stability.{name}' for name in
    ('full_coordinate_bound', 'live_iff_full', 'live_card_stable', 'extremal_full',
     'all_full_live_iff', 'live_card_lt', 'live_card_stable_iff', 'live_card_top')
)
AUDITED += tuple(f'Mahjong.VirtualHand.CopyCapStability.{name}' for name in
                 ('coordinate_bound', 'live_iff_full', 'live_card_stable',
                  'exists_extremal', 'all_full_live_iff', 'live_card_succ',
                  'live_card_lt', 'live_card_stable_iff'))
AUDITED += tuple(f'Mahjong.VirtualHand.TripletCore.{name}' for name in
                 ('reconstruct', 'core_bounded', 'full_core', 'full_lift',
                  'meldCount_split', 'core_tail_lift', 'coreEquiv',
                  'core_meldCount_bound', 'grade_eq', 'full_grade',
                  'parametersEquiv', 'fixedEquiv', 'row_card', 'full_card_formula',
                  'eventualPolynomial_eval', 'eventualPolynomial_degree',
                  'generatingSeries_coeff', 'generatingSeries_rational'))
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
ENTRY = re.compile(
    r"'([^\n]*?)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)"
)
FORBIDDEN = re.compile(r'\b(?:sorry|axiom|native_decide)\b|\+native')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--library', required=True, type=Path, help='Built ninegates-lean4 checkout')
    parser.add_argument('--lake', default='lake', help='Lake executable; defaults to PATH')
    args = parser.parse_args()
    library = args.library.resolve()
    lake = shutil.which(args.lake)
    if not lake:
        parser.error('Lake was not found; use the pinned Lean toolchain or --lake /path/to/lake')
    source = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix='live-waits-lean-') as directory:
        build = Path(directory)
        env = os.environ.copy()
        env['PATH'] = str(Path(lake).parent) + os.pathsep + env['PATH']
        env['LEAN_PATH'] = str(build) + os.pathsep + env.get('LEAN_PATH', '')
        flags = ['-j2', '-M4096', f'--root={build}', '-DwarningAsError=true',
                 '-Dweak.linter.mathlibStandardSet=true', '-DrelaxedAutoImplicit=false']

        def run(arguments):
            result = subprocess.run(
                [lake, 'env', 'lean', *arguments], cwd=library, env=env,
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            )
            if result.returncode:
                raise SystemExit(result.stdout or f'Lean exited with status {result.returncode}')
            return result.stdout

        for name in SOURCES:
            text = (source / name).read_text()
            if FORBIDDEN.search(text):
                raise SystemExit(f'Forbidden proof token in {name}')
            (build / name).write_text(text)
            output = run([*flags, '-o', str(build / f'{Path(name).stem}.olean'), str(build / name)])
            if output.strip():
                raise SystemExit(f'Unexpected compiler output for {name}:\n{output}')
        audit = build / 'Audit.lean'
        audit.write_text('import Capacity\nimport CapacitySpectrum\nimport OrderOneDuality\n'
                        'import OrderOneBoxes\nimport OrderOnePolynomial\n'
                        'import OrderOneStability\nimport CopyCapStability\n'
                        'import TripletCore\nimport TripletCounting\n\n' + ''.join(
            f'#print axioms {name}\n' for name in AUDITED
        ))
        # The audit deliberately uses #print; apply the strict source linters
        # above to the proof modules, and warnings-as-errors to this query file.
        report = run(['-j2', '-M4096', f'--root={build}', '-DwarningAsError=true', str(audit)])
        entries = list(ENTRY.finditer(report))
        if [entry[1] for entry in entries] != list(AUDITED) or ENTRY.sub('', report).strip():
            raise SystemExit(f'Unexpected axiom report:\n{report}')
        for entry in entries:
            axioms = {item.strip() for item in (entry[2] or '').split(',') if item.strip()}
            if axioms - ALLOWED:
                raise SystemExit(f'{entry[1]} uses forbidden axioms: {sorted(axioms - ALLOWED)}')
    print(f'Checked {len(SOURCES)} Lean modules and {len(AUDITED)} declarations; only standard axioms.')


if __name__ == '__main__':
    main()
