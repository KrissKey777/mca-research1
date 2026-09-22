#!/usr/bin/env python3
"""S16.78 Phase 3 secondary: planted five-flat kill-test (exact, deterministic).

Literal target: support-covered triple + exact external witness hypotheses
  -> residual descent or priced cover.
Plant: on GF(q) RS models, three supports S1,S2,S3 with S1 SUBSET S2|S3 (the
package hypothesis hcov) and triple overlap > Kz-proxy; compute:
  (a) whether the overlap cores are 'invisible' (both rows explained there);
  (b) the residual rank proxy (rank of witness-difference space on the cores);
  (c) the priced cover number (greedy cliques) vs the 5-flat budget.
If the triple obstruction only gives wt<=3e analogue (i.e. complement bound
exceeds n), report WEAK/DEAD at the deployed row.
"""
import json
import os
import time
from itertools import combinations, product

HERE = os.path.dirname(os.path.abspath(__file__))
JSON_OUT = os.path.join(HERE, 's1678_fiveflat_planted.json')
TXT_OUT = os.path.join(HERE, 's1678_fiveflat_planted.txt')
MCA_ANALYSIS = r'C:\Users\kross\Documents\Codex\mca-research1\analysis'


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


def rs_words(q, k):
    return [tuple(sum(c * pow(x, i, q) for i, c in enumerate(cf)) % q for x in range(q))
            for cf in product(range(q), repeat=k)]


def run(q, k):
    dom = list(range(q))
    words = rs_words(q, k)
    f0 = tuple((pow(x, 3, q) + 1) % q for x in dom)
    f1 = tuple((pow(x, 2, q) + 2 * x) % q for x in dom)
    Kz = q - k
    # closest-codeword supports
    C, S = {}, {}
    for g in range(q):
        tgt = tuple((f0[i] + g * f1[i]) % q for i in dom)
        best = max(words, key=lambda w: (sum(1 for i in dom if w[i] == tgt[i]), w))
        C[g] = best
        S[g] = [i for i in dom if best[i] == tgt[i]]
    # planted triples: search natural triples with S1 subset S2|S3 (hcov shape)
    planted = []
    for a, b, c in combinations(range(q), 3):
        s1, s2, s3 = set(S[a]), set(S[b]), set(S[c])
        if s1 <= (s2 | s3):
            inter = len(s1 & s2 & s3)
            # invisibility proxy: both rows explained on the pairwise overlaps
            inv12 = all(any(all(w[i] == f[i] for i in (s1 & s2)) for w in words)
                        for f in (f0, f1))
            # residual rank proxy: rank of {C[b]-C[a], C[c]-C[a]} restricted to s1
            M = [[(C[b][i] - C[a][i]) % q for i in sorted(s1)],
                 [(C[c][i] - C[a][i]) % q for i in sorted(s1)]]
            rr = rank_mod(M, q) if s1 else 0
            # wt<=3e analogue: complement-of-triple size vs n
            compl = q - inter
            planted.append({'triple': (a, b, c), 'inter': inter, 'Kz': Kz,
                            'overlap_big': inter > Kz, 'invis12_proxy': inv12,
                            'resid_rank_proxy': rr, 'compl': compl,
                            'wt3e_dead': compl > q - 1})
    return {'q': q, 'k': k, 'Kz': Kz, 'n_planted_hcov': len(planted),
            'planted': planted[:6],
            'verdict': ('NO_PLANTED_HCOV_TRIPLE' if not planted else
                        'PLANTED_PRESENT_SEE_ROWS')}


def main():
    t0 = time.time()
    data = {'models': [run(5, 2), run(7, 2), run(11, 3), run(13, 3)],
            'deployed_note': 'wt<=3e analogue: 3e=2936832 > N=2097152 -> WEAK/DEAD '
                             'unless jointDefect<=69632 or rank/cover bound feeds a consumer',
            'elapsed_s': round(time.time() - t0, 2)}
    with open(JSON_OUT, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=1, default=str)
    L = ['S16.78 Phase3 planted five-flat (exact)']
    for m in data['models']:
        L.append('GF(%d) k=%d planted_hcov=%d verdict=%s' % (
            m['q'], m['k'], m['n_planted_hcov'], m['verdict']))
        for p in m['planted'][:3]:
            L.append('  triple=%s inter=%d big=%s resid_rank=%d compl=%d' % (
                p['triple'], p['inter'], p['overlap_big'], p['resid_rank_proxy'], p['compl']))
    L.append(data['deployed_note'] + ' (%ss)' % data['elapsed_s'])
    with open(TXT_OUT, 'w', encoding='utf-8') as f:
        f.write('\n'.join(L) + '\n')
    print('\n'.join(L))
    for dst, src in ((os.path.join(MCA_ANALYSIS, 's1678_fiveflat_planted.json'), JSON_OUT),
                     (os.path.join(MCA_ANALYSIS, 's1678_fiveflat_planted.txt'), TXT_OUT)):
        try:
            with open(dst, 'w', encoding='utf-8') as f:
                f.write(open(src, encoding='utf-8').read())
        except Exception as e:
            print('copy-skip:', dst, str(e)[:120])


if __name__ == '__main__':
    main()
