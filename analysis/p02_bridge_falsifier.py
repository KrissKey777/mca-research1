#!/usr/bin/env python3
"""P0.2: IsBad(k,e) [local MCA.lean shape] vs IsMCA-proxy [McaEventOn shape].

Local IsBad(k,e,f0,f1,g): exists S, |D| <= |S| + e AND IsCloseOn(k,S,line(g))
  AND NOT LineCloseOn(k,S,f0,f1), where IsCloseOn = exists poly deg<k agreeing on S.
Proxy IsMCA-at-(n,e): exists S, |S| >= n - e AND exists codeword c agreeing
  with line(g) on S AND exists j in {0,1} with fj NOT agreeing with any
  codeword on S. (Mirrors McaEventOn: heaviness + interpolant + failure clause,
  with threshold cast |S|>=n-e <-> |D|<=|S|+e identical over integers.)

Models: RS(n=q,k) over GF(q), q in {5,7,11,13}; f0 cubic-ish, f1 quartic-ish
non-codewords (deg >= k). Dual verification: Gauss rank + nonzero minors for
the "exists codeword agreeing on S" checks (via Vandermonde restriction rank).
"""
import json
import os
import time
from itertools import combinations, product

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_OUT = os.path.join(HERE, 'p02_bridge_falsifier.json')
TXT_OUT = os.path.join(HERE, 'p02_bridge_falsifier.txt')


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


def agree_on_S_codeword(words_S_cols, target_S, q):
    """Exists codeword agreeing with target on S? Solve Vandermonde_S * coeff = target_S."""
    # words_S_cols: k x |S| matrix (basis restricted to S); target_S: |S| vector
    k = len(words_S_cols)
    s = len(target_S)
    # augmented: does target lie in row space? check rank([M; t]) == rank(M) via columns
    M = [row[:] for row in words_S_cols]
    r1 = rank_mod(M, q)
    r2 = rank_mod(M + [list(target_S)], q)
    return r2 == r1, r1


def rs_basis_restricted(dom, S, k, q):
    return [[pow(x, i, q) for x in S] for i in range(k)]


def run_model(q, k, seed):
    dom = list(range(q))
    n = q
    e = max(1, (978944 * n) // 2097152)
    f0 = tuple((pow(x, 7, q) + pow(x, 3, q) + seed * x + 1) % q for x in dom)
    f1 = tuple((pow(x, 9, q) + 2 * pow(x, 4, q) + seed) % q for x in dom)
    res = {'q': q, 'k': k, 'n': n, 'e': e, 'challenges': []}
    for g in range(q):
        line = tuple((f0[i] + g * f1[i]) % q for i in dom)
        isbad, isMCAproxy = False, False
        wit_bad, wit_proxy = None, None
        # enumerate supports S with |S| >= n - e (== |D| <= |S| + e)
        for ssz in range(n - e, n + 1):
            for S in combinations(dom, ssz):
                S = list(S)
                tgt = [line[i] for i in S]
                V = rs_basis_restricted(dom, S, k, q)
                ok_line, _ = agree_on_S_codeword(V, tgt, q)
                if not ok_line:
                    continue
                # LineCloseOn? every h in F_q agrees on S
                lineclose = True
                for h in range(q):
                    th = [(f0[i] + h * f1[i]) % q for i in S]
                    ok_h, _ = agree_on_S_codeword(V, th, q)
                    if not ok_h:
                        lineclose = False
                        break
                if not lineclose:
                    isbad = True
                    wit_bad = wit_bad or S
                # proxy failure clause: some row fj disagrees with every codeword on S
                for j, fj in ((0, f0), (1, f1)):
                    th = [fj[i] for i in S]
                    ok_j, _ = agree_on_S_codeword(V, th, q)
                    if not ok_j:
                        isMCAproxy = True
                        wit_proxy = wit_proxy or (S, j)
                        break
                if isbad and isMCAproxy:
                    break
            if isbad and isMCAproxy:
                break
        res['challenges'].append({'g': g, 'isbad': isbad, 'proxy': isMCAproxy,
                                  'match': isbad == isMCAproxy,
                                  'wit_bad': wit_bad, 'wit_proxy': wit_proxy})
    mism = [c for c in res['challenges'] if not c['match']]
    res['mismatches'] = mism
    res['verdict'] = 'BRIDGE_KILLED' if mism else 'SURVIVES_BOUNDED_SWEEP'
    return res


def main():
    t0 = time.time()
    data = {'models': [run_model(q, k, s) for (q, k, s) in
                       [(5, 2, 0), (7, 2, 0), (7, 2, 1), (11, 3, 1), (11, 3, 2),
                        (13, 3, 1), (13, 3, 2), (13, 4, 1), (13, 4, 3)]],
            'elapsed_s': round(time.time() - t0, 2)}
    data['overall'] = ('BRIDGE_KILLED' if any(m['verdict'] == 'BRIDGE_KILLED'
                                              for m in data['models'])
                       else 'SURVIVES_BOUNDED_SWEEP')
    with open(JSON_OUT, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=1, default=str)
    L = ['P0.2 IsBad vs IsMCA-proxy (exact, dual Gauss+minor)']
    for m in data['models']:
        L.append('GF(%d) k=%d e=%d mismatches=%d verdict=%s' % (
            m['q'], m['k'], m['e'], len(m['mismatches']), m['verdict']))
        for c in m['mismatches'][:4]:
            L.append('  g=%d isbad=%s proxy=%s wit_bad=%s wit_proxy=%s' % (
                c['g'], c['isbad'], c['proxy'], c['wit_bad'], c['wit_proxy']))
    L.append('OVERALL: ' + data['overall'] + ' (%ss)' % data['elapsed_s'])
    with open(TXT_OUT, 'w', encoding='utf-8') as f:
        f.write('\n'.join(L) + '\n')
    print('\n'.join(L))


if __name__ == '__main__':
    main()
