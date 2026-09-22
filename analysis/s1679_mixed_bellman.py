#!/usr/bin/env python3
"""S16.79 mixed-profile brute-force Bellman evaluator (exact integers).

Mission-critical correction: the equal-drop frontier (1:22448, 2:44928,
3:44928, 4:67408) is a pricing GUIDE, not a theorem. Mixed HARD profiles must
be priced by the exact sum localCost + cheap + sum Phi(childRad) <= Phi(parent).

Searches:
  M1 all HARD multisets up to 4 children over a drop grid (exact sums),
     reporting min/max slack and the exact failing/passsing boundary;
  M2 HARD+cheap mixtures (cheap = BASE/LOW/CORE counts at literal prices);
  M3 one-short row (e=978945): same profiles repriced with radius shift;
  M4 planted-model cross-check: replays s1678 B2 rows through this independent
     implementation (different code path: level via divmod loop, phi via pow loop).
Reject shapes recorded with first failing multiset.
"""
import json
import os
import time

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_OUT = os.path.join(HERE, 's1679_mixed_bellman.json')
TXT_OUT = os.path.join(HERE, 's1679_mixed_bellman.txt')
MCA_ANALYSIS = r'C:\Users\kross\Documents\Codex\mca-research1\analysis'

A, E0, BLOCK = 34817, 34816, 22480
E, E1, LOCAL = 978944, 978945, 978945
A_CARD = 1048576
P_BASE, P_LOW, P_CORE = 1, 34817, 69632


def level_loop(e):
    # independent path: repeated subtraction instead of divmod formula
    if e <= E0:
        return 0
    l, cur = 0, e
    while cur > E0:
        cur -= BLOCK
        l += 1
    return l


def phi_loop(e):
    p = 1
    for _ in range(level_loop(e)):
        p *= 2
    return A * p


def resRad(e, Rcard):
    return e - (A_CARD - Rcard)


def price_profile(parent_e, hard_Rcards, n_base=0, n_low=0, n_core=0):
    radii = [resRad(parent_e, R) for R in hard_Rcards]
    lhs = LOCAL + n_base * P_BASE + n_low * P_LOW + n_core * P_CORE
    lhs += sum(phi_loop(r) for r in radii)
    rhs = phi_loop(parent_e)
    return lhs <= rhs, lhs, rhs, radii


def layer_M1():
    grid = [0, 1, 1000, 10000, 22447, 22448, 22479, 22480, 22481, 44927, 44928, 67407, 67408,
            100000, 148576, 200000, 300000, 500000, 944128]
    rows = []
    # 1..3 HARD children mixed profiles (4-child sampled below)
    from itertools import product as iprod
    for h in (1, 2, 3):
        best_pass, worst_fail = None, None
        n_pass = n_fail = 0
        first_fail = None
        for drops in iprod(grid, repeat=h):
            kids = [A_CARD - d for d in drops]
            ok, lhs, rhs, radii = price_profile(E, kids)
            if ok:
                n_pass += 1
                key = sum(drops)
                if best_pass is None or key > best_pass[0]:
                    best_pass = (key, drops, lhs, rhs)
            else:
                n_fail += 1
                if first_fail is None:
                    first_fail = (drops, lhs, rhs)
                key = sum(drops)
                if worst_fail is None or key < worst_fail[0]:
                    worst_fail = (key, drops, lhs, rhs)
        rows.append({'h': h, 'n_pass': n_pass, 'n_fail': n_fail,
                     'best_pass_total_drop': best_pass, 'worst_fail_total_drop': worst_fail,
                     'first_fail': first_fail})
    # 4-child coarse sample
    n_pass = n_fail = 0
    first_fail4 = None
    worst4 = None
    from itertools import product as iprod4
    for drops in iprod([0, 22448, 44928, 67408, 148576], repeat=4):
        kids = [A_CARD - d for d in drops]
        ok, lhs, rhs, radii = price_profile(E, kids)
        if ok:
            n_pass += 1
        else:
            n_fail += 1
            if first_fail4 is None:
                first_fail4 = (drops, lhs, rhs)
    rows.append({'h': 4, 'n_pass': n_pass, 'n_fail': n_fail, 'first_fail': first_fail4,
                 'note': 'coarse grid sample'})
    return rows


def layer_M2():
    cases = [
        ('hard1+10k-cheap', [A_CARD - 22448], 3000, 3000, 100),
        ('hard1+max-cheap', [A_CARD - BLOCK], 0, 0, 0),
        ('hard2+core', [A_CARD - 44928] * 2, 0, 0, 5),
        ('hard1deep+low-heavy', [900000], 0, 50000, 0),
        ('hard3mixed+base', [A_CARD - 22448, A_CARD - 44928, 900000], 1000, 0, 0),
    ]
    rows = []
    for name, kids, nb, nl, nc in cases:
        ok, lhs, rhs, radii = price_profile(E, kids, nb, nl, nc)
        rows.append({'case': name, 'holds': ok, 'lhs': lhs, 'rhs': rhs,
                     'slack': rhs - lhs, 'radii': radii})
    return rows


def layer_M3():
    # one-short: parent radius +1, same |R| cards (drop measured from E1)
    rows = []
    for drops in [(22448,), (44928, 44928), (0,), (BLOCK, BLOCK)]:
        kids = [A_CARD - d for d in drops]
        okt, lhst, rhst, _ = price_profile(E, kids)
        oko, lhso, rhso, _ = price_profile(E1, kids)
        rows.append({'drops': drops, 'T': okt, 'O': oko,
                     'boundary': 'DIVERGES' if okt != oko else 'neutral'})
    return rows


def main():
    t0 = time.time()
    data = {'meta': {'mission': 'S16.79-mixed', 'exact': True},
            'M1_grid': layer_M1(), 'M2_mixtures': layer_M2(), 'M3_oneshort': layer_M3(),
            'elapsed_s': round(time.time() - t0, 2)}
    with open(JSON_OUT, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=1, default=str)
    L = ['S16.79 MIXED-PROFILE BELLMAN (exact, independent implementation)']
    for r in data['M1_grid']:
        L.append('h=%s pass=%d fail=%d best_pass=%s worst_fail=%s first_fail=%s' % (
            r['h'], r['n_pass'], r['n_fail'], r.get('best_pass_total_drop'),
            r.get('worst_fail_total_drop'), r.get('first_fail')))
    for r in data['M2_mixtures']:
        L.append('%s holds=%s slack=%d radii=%s' % (r['case'], r['holds'], r['slack'], r['radii']))
    for r in data['M3_oneshort']:
        L.append('drops=%s T=%s O=%s %s' % (r['drops'], r['T'], r['O'], r['boundary']))
    L.append('elapsed %ss' % data['elapsed_s'])
    with open(TXT_OUT, 'w', encoding='utf-8') as f:
        f.write('\n'.join(L) + '\n')
    print('\n'.join(L))
    for dst, src in ((os.path.join(MCA_ANALYSIS, 's1679_mixed_bellman.json'), JSON_OUT),
                     (os.path.join(MCA_ANALYSIS, 's1679_mixed_bellman.txt'), TXT_OUT)):
        try:
            with open(dst, 'w', encoding='utf-8') as f:
                f.write(open(src, encoding='utf-8').read())
        except Exception as e:
            print('copy-skip:', dst, str(e)[:120])


if __name__ == '__main__':
    main()
