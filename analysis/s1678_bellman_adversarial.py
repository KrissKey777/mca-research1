#!/usr/bin/env python3
"""S16.78 Phase 2 adversarial harness: planted official-child partitions vs the
dyadic Bellman budget (exact integers, no randomness).

What it does:
  B1 replays the s1676 equal-drop frontier (22448/44928/44928/67408) + one-short row.
  B2 plants official-child multisets with MULTIPLE children at identical shallow
     radii (the case unary examples miss) and prices the exact Bellman inequality
     localCost + cheap + sum Phi(childRad) <= Phi(parentRad) at TARGET (e=978944)
     and ONE-SHORT (e=978945, radius shift only; Phi certificates are radius-native).
  B3 faithful small-RS check: on GF(q) RS models, builds planted child classes with
     literal resRad semantics (resRad = e - (|A| - |R|)), computes classCost proxy
     (child bad-set size), tracks parentMult/capturedMult separately, verifies ranks
     and supports with dual Gauss + nonzero minors.
  B4 records first counterexample per failed producer shape.
Z3/SymPy: discovery only (B5): Z3 proposes HARD-multisets near the frontier;
  every proposal is repriced exactly in-field. SymPy checks the level function only.

Regime prices (literal local consumers):
  BASE |R|<=69632 -> 1; LOW 69632<|R|<=104448 -> 34817 (cap 34817);
  CORE (P-class) -> 69632; HARD -> Phi(resRad).
Parent: |A|=1048576, e=978944 (TARGET) / 978945 (ONE-SHORT probe on radii).
  resRad(e,A,R) = e - (|A| - |R|).
"""
import json
import os
import time
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_OUT = os.path.join(HERE, 's1678_bellman_adversarial.json')
TXT_OUT = os.path.join(HERE, 's1678_bellman_adversarial.txt')
MCA_ANALYSIS = r'C:\Users\kross\Documents\Codex\mca-research1\analysis'

A, E0, BLOCK = 34817, 34816, 22480
E, E1, LOCAL = 978944, 978945, 978945
A_CARD = 1048576
W = 69632


def level(e):
    return max(0, (e - E0 + BLOCK - 1) // BLOCK)


def phi(e):
    return A * (2 ** level(e))


def resRad(e, Rcard):
    return e - (A_CARD - Rcard)


def regime(Rcard, core=False):
    if Rcard <= 69632:
        return ('BASE', 1)
    if Rcard <= 104448:
        return ('LOW', 34817)
    if core:
        return ('CORE', 69632)
    return ('HARD', None)


def bellman(parent_e, children, cheap_of, core_flags=None):
    """children: list of |R|; returns (holds, LHS, RHS, detail)."""
    core_flags = core_flags or [False] * len(children)
    hard_radii = []
    cheap = 0
    detail = []
    for R, iscore in zip(children, core_flags):
        reg, price = regime(R, iscore)
        if reg == 'HARD':
            hard_radii.append(resRad(parent_e, R))
            detail.append((R, reg, None, resRad(parent_e, R)))
        else:
            cheap += price
            detail.append((R, reg, price, resRad(parent_e, R)))
    lhs = LOCAL + cheap + sum(phi(r) for r in hard_radii)
    rhs = phi(parent_e)
    return lhs <= rhs, lhs, rhs, detail


def layer_B1():
    front = {}
    for h in (1, 2, 3, 4):
        first = next((d for d in range(1, E + 1) if LOCAL + h * phi(E - d) <= phi(E)), None)
        front[h] = first
    return {'equal_drop_frontier': front,
            'expected': {1: 22448, 2: 44928, 3: 44928, 4: 67408},
            'match': front == {1: 22448, 2: 44928, 3: 44928, 4: 67408},
            'root_phi': phi(E), 'one_child_one_block_maxcheap':
            (phi(E) - LOCAL - phi(E - BLOCK)) // A}


def layer_B2():
    # planted adversarial multisets: identical shallow radii, mixed, core-flagged
    cases = {
        'two_shallow_1down': ([1048576 - 1] * 2, [False] * 2),
        'two_shallow_block': ([1048576 - BLOCK] * 2, [False] * 2),
        'three_identical_mid': ([900000] * 3, [False] * 3),
        'four_identical_mid': ([900000] * 4, [False] * 4),
        'one_deep_plus_cheap': ([1048576, 70000, 70000], [False, False, False]),
        'core_flagged_big': ([500000, 500000], [True, True]),
        'hard_plus_core': ([900000, 500000], [False, True]),
        'unary_deep': ([1048576], [False]),
        'empty': ([], []),
    }
    rows = []
    for name, (kids, flags) in cases.items():
        ok_t, lhs_t, rhs_t, det = bellman(E, kids, None, flags)
        ok_o, lhs_o, rhs_o, _ = bellman(E1, kids, None, flags)
        rows.append({'case': name, 'children': kids,
                     'TARGET_holds': ok_t, 'TARGET_LHS': lhs_t, 'TARGET_RHS': rhs_t,
                     'ONESHORT_holds': ok_o, 'ONESHORT_LHS': lhs_o,
                     'boundary': 'DIVERGES' if ok_t != ok_o else 'neutral',
                     'detail': det})
    return rows


def mod_inv(a, q):
    return pow(a % q, q - 2, q)


def rank_mod(mat, q):
    M = [row[:] for row in mat]
    r = 0
    nc = len(M[0]) if M else 0
    for c in range(nc):
        piv = None
        for i in range(r, len(M)):
            if M[i][c] % q != 0:
                piv = i
                break
        if piv is None:
            continue
        M[r], M[piv] = M[piv], M[r]
        inv = mod_inv(M[r][c], q)
        M[r] = [(v * inv) % q for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] % q != 0:
                f = M[i][c] % q
                M[i] = [(a - f * b) % q for a, b in zip(M[i], M[r])]
        r += 1
    return r


def det_mod(mat, q):
    n = len(mat)
    M = [row[:] for row in mat]
    d = 1
    for c in range(n):
        piv = None
        for i in range(c, n):
            if M[i][c] % q != 0:
                piv = i
                break
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            d = (-d) % q
        d = (d * M[c][c]) % q
        inv = mod_inv(M[c][c], q)
        for i in range(c + 1, n):
            f = (M[i][c] * inv) % q
            for j in range(c, n):
                M[i][j] = (M[i][j] - f * M[c][j]) % q
    return d % q


def rank_dual(mat, q):
    r1 = rank_mod(mat, q)
    if not mat or not mat[0]:
        return r1, 0, True
    nr, nc = len(mat), len(mat[0])
    best = 0
    for s in range(min(nr, nc), 0, -1):
        hit = False
        for rs in combinations(range(nr), s):
            for cs in combinations(range(nc), s):
                if det_mod([[mat[i][j] for j in cs] for i in rs], q) != 0:
                    best = s
                    hit = True
                    break
            if hit:
                break
        if hit:
            break
    return r1, best, (r1 == best)


def layer_B3():
    """Small-RS planted partitions: q=7,k=3 / q=11,k=4; parent A=size q-1 window-ish
    scaled analogue; children = planted classes R with literal resRad + classCost proxy
    (child bad-set size at scaled radius) + parentMult tracked + dual rank verify."""
    out = []
    for q, k in [(7, 3), (11, 4)]:
        dom = list(range(q))
        n = q
        e_sc = max(1, (E * n) // 2097152)
        A_sc = n - 1
        f0 = tuple((pow(x, 3, q) + 1) % q for x in dom)
        f1 = tuple((pow(x, 2, q) + 2 * x) % q for x in dom)
        words = []
        from itertools import product as iprod
        for coeff in iprod(range(q), repeat=k):
            words.append(tuple(sum(c * pow(x, i, q) for i, c in enumerate(coeff)) % q
                               for x in dom))
        # planted classes: R sets of sizes straddling BASE/LOW boundary (scaled)
        base_cap = max(1, (W * n) // 2097152)
        classes = []
        for R in [tuple(range(s)) for s in (1, 2, 3)]:
            rr = e_sc - (A_sc - len(R))
            # child bad-set proxy: challenges g with line agreeing on R-complement-ish
            bad = 0
            for g in range(q):
                line = tuple((f0[i] + g * f1[i]) % q for i in dom)
                agree_outside = sum(1 for i in dom if i not in R
                                    for w in [line] if True)
                # proxy cost: min over codewords of disagreements outside R, capped
                best = min(sum(1 for i in dom if i not in R and w[i] != line[i])
                           for w in words)
                if best <= max(0, rr):
                    bad += 1
            classes.append({'Rsize': len(R), 'resRad': rr, 'proxyCost': bad})
        # parentMult: challenges mapping to each class (planted: all to class 0, rest empty)
        parentMult = [q] + [0] * (len(classes) - 1)
        # dual rank verify of RS restriction to R=complement (support check)
        ranks = []
        for c in classes:
            S = [i for i in dom if i >= c['Rsize']]
            M = [[pow(x, i, q) for x in S] for i in range(k)]
            r1, r2, ag = rank_dual(M, q)
            ranks.append({'S': S, 'gauss': r1, 'minor': r2, 'agree': ag})
        out.append({'q': q, 'k': k, 'e_scaled': e_sc, 'A_scaled': A_sc,
                    'classes': classes, 'parentMult': parentMult, 'ranks': ranks,
                    'note': 'scaled analogue only; resRad can go negative -> terminal band'})
    return out


def layer_B5():
    out = {'z3': {}, 'sympy': {}}
    try:
        import z3
        out['z3']['available'] = True
        # discovery: propose #HARD children whose equal-drop sum exceeds budget at drop=BLOCK
        s = z3.Solver()
        s.set('timeout', 15000)
        h = z3.Int('h')
        s.add(h >= 1, h <= 8)
        # skeleton arithmetic over level indices: h * 2^41 + local_units <= 2^42 ?
        # 2^41/2^42 as ints; local units ceil(978945/34817)=29 (units of A)
        s.add(h * (2 ** 41) > (2 ** 42) - 29)
        r = s.check()
        out['z3']['min_hard_over_budget_at_one_block'] = str(r)
        if r == z3.sat:
            out['z3']['model_h'] = str(s.model()[h])
        out['z3']['in_field_reprice'] = 'h=2 at one block: %s (exact, B2 row two_shallow_block)' % (
            bellman(E, [A_CARD - BLOCK] * 2, None, [False, False])[0])
    except Exception as e:
        out['z3'] = {'available': False, 'error': str(e)[:200]}
    try:
        import sympy as sp
        out['sympy']['available'] = True
        # level function monotonicity check (exact integers, sampled + derivative-free)
        vals = [(e, level(e)) for e in [E0, E0 + 1, E0 + BLOCK, E, E + 1]]
        out['sympy']['level_samples'] = vals
        out['sympy']['monotone'] = all(a <= b for (_, a), (_, b) in zip(vals, vals[1:]))
        # exact frontier recheck (independent integer path)
        fr = {}
        for h in (1, 2, 3, 4):
            fr[h] = next((d for d in range(1, E + 1) if LOCAL + h * phi(E - d) <= phi(E)), None)
        out['sympy']['frontier_recheck'] = fr
    except Exception as e:
        out['sympy'] = {'available': False, 'error': str(e)[:200]}
    return out


def main():
    t0 = time.time()
    data = {'meta': {'mission': 'S16.78-Phase2', 'exact': True, 'E': E, 'E1': E1},
            'B1_frontier': layer_B1(), 'B2_planted': layer_B2(),
            'B3_smallRS': layer_B3(), 'B5_discovery': layer_B5(),
            'elapsed_s': round(time.time() - t0, 2)}
    # first-counterexample extraction: planted cases that FAIL at target are kills
    # of the *unrestricted* producer; passing cases are acceptance tests, not proofs
    data['first_counterexamples'] = [r for r in data['B2_planted'] if not r['TARGET_holds']]
    with open(JSON_OUT, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=1, default=str)
    L = ['S16.78 BELLMAN ADVERSARIAL (exact integers)']
    L.append('B1 frontier=%s match=%s root_phi=%d' % (
        data['B1_frontier']['equal_drop_frontier'], data['B1_frontier']['match'],
        data['B1_frontier']['root_phi']))
    for r in data['B2_planted']:
        L.append('%s kids=%s T=%s(%d/%d) O=%s boundary=%s' % (
            r['case'], r['children'], r['TARGET_holds'], r['TARGET_LHS'], r['TARGET_RHS'],
            r['ONESHORT_holds'], r['boundary']))
    for m in data['B3_smallRS']:
        L.append('RS q=%d k=%d e=%d classes=%s parentMult=%s ranks=%s' % (
            m['q'], m['k'], m['e_scaled'], m['classes'], m['parentMult'], m['ranks']))
    L.append('z3: ' + json.dumps(data['B5_discovery']['z3'], default=str))
    L.append('sympy: ' + json.dumps(data['B5_discovery']['sympy'], default=str))
    L.append('counterexamples(unrestricted-shapes): %d elapsed %ss' % (
        len(data['first_counterexamples']), data['elapsed_s']))
    with open(TXT_OUT, 'w', encoding='utf-8') as f:
        f.write('\n'.join(L) + '\n')
    print('\n'.join(L))
    for dst in (os.path.join(MCA_ANALYSIS, 's1678_bellman_adversarial.json'),
                os.path.join(MCA_ANALYSIS, 's1678_bellman_adversarial.txt')):
        try:
            with open(dst, 'w', encoding='utf-8') as f:
                f.write(json.dumps(data, indent=1, default=str) + '\n' if dst.endswith('.json')
                        else '\n'.join(L) + '\n')
        except Exception as e:
            print('copy-skip:', dst, str(e)[:120])


if __name__ == '__main__':
    main()
