"""Cross-check the deficit-two layer; no Lean certification is claimed."""

import functools
import itertools
import json
from pathlib import Path


PROFILE = (2, 4, 6, 6, 4, 2)


def meldable_scan(hand):
    hand = list(hand)
    for i in range(4):
        starts = hand[i] % 3
        hand[i + 1] -= starts
        hand[i + 2] -= starts
        if min(hand[i + 1:i + 3]) < 0:
            return False
    return hand[4] % 3 == hand[5] % 3 == 0


@functools.cache
def meldable_recursive(hand):
    if min(hand) < 0:
        return False
    if not any(hand):
        return True
    first = next(i for i, count in enumerate(hand) if count)

    def minus(places):
        rest = list(hand)
        for rank in places:
            rest[rank] -= 1
        return tuple(rest)

    if hand[first] >= 3 and meldable_recursive(minus((first, first, first))):
        return True
    return (first + 2 < 6 and hand[first + 1] > 0 and hand[first + 2] > 0
            and meldable_recursive(minus((first, first + 1, first + 2))))


def winning(hand, algorithm):
    return any(algorithm(tuple(count - 2 * (i == pair) for i, count in enumerate(hand)))
               for pair in range(6) if hand[pair] >= 2)


def full(hand):
    if min(hand) < 0:
        return False
    results = []
    for draw in range(6):
        next_hand = tuple(count + (i == draw) for i, count in enumerate(hand))
        scan = winning(next_hand, meldable_scan)
        recursive = winning(next_hand, meldable_recursive)
        assert scan == recursive, (hand, draw)
        results.append(scan)
    return all(results)


def main():
    rows = []
    histogram = [0] * 7
    checked = 0
    for first, second in itertools.combinations_with_replacement(range(6), 2):
        deficit = tuple(int(i == first) + int(i == second) for i in range(6))
        flags = {}
        for mask in range(64):
            hand = tuple(PROFILE[i] - 1 + 3 * ((mask >> i) & 1) - deficit[i]
                         for i in range(6))
            flags[mask] = full(hand)
            checked += 1
            if flags[mask]:
                assert sum(hand) == 3 * (5 + mask.bit_count()) + 1
                histogram[mask.bit_count()] += 1
        free = [i for i in range(6)
                if all(flags[mask] == flags[mask ^ (1 << i)] for mask in flags)]
        assert free, deficit
        assert sum((-1) ** (6 - mask.bit_count()) for mask in flags if flags[mask]) == 0
        rows.append({
            'deficit': deficit,
            'free_coordinate': free[0],
            'all_free_coordinates': free,
            'full_masks': [mask for mask in flags if flags[mask]],
        })

    # Compare the independently computed layer with the full C++ core histogram.
    raw = json.loads(Path(__file__).with_name('six-rank-cores.json').read_text())['orders'][1]
    expected = [sum(row['count'] for row in raw['histogram']
                    if row['active'] == active and row['grade'] + 6 - active == 11)
                for active in range(7)]
    assert histogram == expected
    output = {
        'scope': 'Six-rank deficit-two layer; ordinary computation, not a Lean certificate',
        'profile': PROFILE,
        'patterns': len(rows),
        'mask_assignments_checked': checked,
        'algorithms': ['triplet-greedy pair scan', 'literal recursive meld decomposition'],
        'histogram_by_active_count': histogram,
        'signed_sum': sum(count * (-1) ** (6 - active)
                          for active, count in enumerate(histogram)),
        'rows': rows,
    }
    Path(__file__).with_name('top-layer-check.json').write_text(json.dumps(output, indent=2) + '\n')
    print(json.dumps({key: value for key, value in output.items() if key != 'rows'}))


if __name__ == '__main__':
    main()
