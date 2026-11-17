"""Analyze the ordinary-program core diagnostic with exact rational arithmetic."""
import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path


def analyze(data):
    results = []
    for row in data['orders']:
        degree = row['ranks'] - 1
        coefficients = [Fraction(0)] * (degree + 1)
        for shift, weight in enumerate(row['numerator']):
            term = [Fraction(1)]
            for factor in range(1, degree + 1):
                product = [Fraction(0)] * (len(term) + 1)
                for power, coefficient in enumerate(term):
                    product[power] += coefficient * (factor - shift)
                    product[power + 1] += coefficient
                term = product
            for power, coefficient in enumerate(term):
                coefficients[power] += weight * coefficient / factorial(degree)

        def evaluate(value):
            result = Fraction(0)
            for coefficient in reversed(coefficients):
                result = result * value + coefficient
            return result

        cutoff = max(0, row['numerator_degree'] - row['ranks'] + 1)
        assert coefficients[-1] == Fraction(3 ** degree, factorial(degree))
        assert all(evaluate(m) == row['counts_m_0_to_40'][m]
                   for m in range(cutoff, 41))
        if cutoff:
            assert evaluate(cutoff - 1) != row['counts_m_0_to_40'][cutoff - 1]
        results.append({
            'order': row['order'],
            'candidate_polynomial_cutoff': cutoff,
            'polynomial_coefficients_low_to_high': [str(c) for c in coefficients],
            'comparison_m_0_to_8': [
                {'m': m, 'direct_full_count': row['direct_counts_m_0_to_8'][m],
                 'polynomial': str(evaluate(m))}
                for m in range(9)
            ],
        })
    return {'scope': 'Exact arithmetic applied to a computational core table; '
                     'the core cardinalities are not evaluated in Lean.', 'orders': results}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', nargs='?', type=Path,
                        default=Path(__file__).with_name('six-rank-cores.json'))
    source = parser.parse_args().input
    print(json.dumps(analyze(json.loads(source.read_text())), indent=2))
