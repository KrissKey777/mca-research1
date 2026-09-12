# CAP-VIOLATION ⇒ QUOTIENT-STRUCTURE: FALSIFICATION REPORT

**Mission.** Falsify (or fail to falsify)

> FULL-MCA + genuine violation of the corrected plain rank cap `Σ_i c_i > 2κ − 1`
> ⇒ generalized grading / quotient structure.

**Verdict: FALSIFIED.** Nongraded, FULL-MCA, pairwise-regular violations of the plain
cap exist, are certified exactly, occur both on and strictly below the Johnson bound,
and are produced by an explicit construction that works at **every** size tested,
`n = 8, 16, 32, 64, 128, 256, 512`, on two compatible primes each.

**Status of everything below.** These are *exact finite-field measurements* (integer
arithmetic mod `q`, no floating point, no sampling error in the verified claims), not
theorems. Nothing here is formalized in Lean; per the mission's stop rule, no Lean was
written. Where a statement is a dimension count or a heuristic it is labelled as such.

Notation follows the project: `D ⊆ F_q^*` the evaluation domain, `|D| = n`, `C = RS_k(D)`,
`κ = n − k`, window `S_i` the maximal agreement set of `f_0 + γ_i f_1` with a degree-`<k`
polynomial, `Z_i = D \ S_i`, `c_i = |S_i| − k`, `A_i = ∏_{z ∈ Z_i}(X − z)`,
`R_i = A_i·F[X]_{<c} ⊆ P = F[X]_{<κ}`, `V_i = R_i^⊥ = span{(1,z,…,z^{κ−1}) : z ∈ Z_i}`.
FULL-MCA = `f_1` itself does not agree with any degree-`<k` polynomial on any `S_i`.
Regular = `|S_i ∩ S_j| ≤ k` for all `i ≠ j`. Plain cap: `Σ_i c_i ≤ 2κ − 1`.

Scripts and data: `analysis/capviol_*.py`, `analysis/capviol_scan.c`,
`analysis/capviol_data/*.jsonl|*.log|*.json`.

---

## THE 13 REQUIRED ITEMS

### 1. CAP-VIOLATING instances tested

| campaign | script | instances | outcome |
|---|---|---|---|
| exhaustive solution-fibre enumeration, `n = 12` | `capviol_exhaust.py` | 305 exact families | 301 nongraded cap violations |
| master sweep, random challenges, ~25 parameter rows | `capviol_sweep.py` | 847 lines | 177 raw, 162 discarded as irregular, 15 regular, 1 nongraded |
| structure-agnostic annealing | `capviol_anneal{,2}.py` | 224 runs | 0 FULL-MCA cap violations (weak null: it could not even rediscover the known graded violation) |
| class-A single-point perturbation of graded violations | `capviol_control.py` | 384 (`n=16`) + 1100 (`n=32`) | all destroy the violation at fixed random `γ` |
| determinant tuning (on-Johnson) | `capviol_tune.py` | 22 hits | all nongraded |
| determinant tuning (37 strictly-below-Johnson rows × 2 primes) | `capviol_tune2.py` | 90 hits | all nongraded |
| determinant tuning + leave-one-out filter (small / big / scaling) | `capviol_tune3.py` | 82 hits | all nongraded |
| explicit quarter-pair construction, `n = 8 … 512` | `capviol_quarters.py` | 14/14 attempts | all nongraded |
| exact maximisation of the bad-set statistics by hill climbing | `capviol_maxbad.py` | 17 rows × 6 restarts × 250–400 moves | measures the true maximum of `Σc_i` and `Σ(c_i−1)` |

636 challenge-tuned window families were examined across 115 (parameter row, prime)
combinations; 495 of the resulting records are **strictly verified** nongraded regular
FULL-MCA plain-cap violations, spread over 32 distinct `(n,k,e)` rows and 56 `(n,k,e,q)`
combinations.

Classes A–F of the mission brief are all represented: A (point perturbations of graded
violations — negative), B (windows from mixed subgroup orders — negative at fixed `γ`),
C (near-coset windows with destroyed periodicity — subsumed by the tuned random windows),
D (quotient lift + asymmetric perturbation — negative), E (saturated pairwise regularity —
**this is where every positive hit lives**, `max_{i<j}|S_i ∩ S_j| = k` exactly), F
(parameters near `mc = 2κ−1, 2κ, 2κ+1` — the observed excesses are `+1 … +4`).

### 2. Nongraded cap violations found: count

**495** strictly verified (`Σc_i > 2κ−1`, regular, FULL-MCA, windows maximal, no common
factor, `min_{h>1} Σ_i d_i(h) > 0`), over 32 parameter rows, plus 14 further witnesses
from the explicit quarter-pair construction at `n = 8 … 512` (recorded separately in
`capviol_data/quarters.json`).

For each hit the following were computed exactly: FULL-MCA; `rank M`; `Σc_i`; `2κ−1`;
the rank defect; pairwise regularity; `Graded(h)` per-window defects for **every** `h | n`;
the common factor `gcd_i A_i`; the common-factor-reduced defects; and the generalized
per-window certificate `Σ_{r<h} min(rows_r, 2κ_r)`. Decisive witnesses were cross-checked
on at least two compatible primes for every `n ≤ 64`.

### 3. Smallest witness

`n = 8`, `k = 4`, `e = 2`, `c = 2`, `κ = 4`, `q = 17`, `D = μ_8 ⊂ F_17^*`, `m = 4`.
Strictly **inside** the Johnson bound (`(n−e)² − nk = 36 − 32 = 4 > 0`) and at the
unique-decoding radius (`e = 2 = ⌊(d−1)/2⌋`, `d = n−k+1 = 5`).

```
D  = μ_8 ⊂ F_17^*  =  [1, 9, 13, 15, 16, 8, 4, 2]   (index i = position in this list)
f0 = [ 3, 14, 10, 12,  7,  1,  4,  0]
f1 = [ 3,  3, 14,  5, 11, 14,  5,  7]
γ  = [14,  1, 11,  7]
S  = [{0,1,4,5,6,7}, {0,1,2,3,5,6}, {0,2,3,4,5,7}, {1,2,3,4,6,7}]     (indices into D)
```

Re-verified from scratch, with no project code, by `analysis/capviol_witness8.py`.

Independently certified (`capviol_certify.py`, independent code path):

| check | value |
|---|---|
| C1 windows distinct, `|S_i| = n − e = 6` | ✔ |
| C2 challenges distinct | ✔ |
| C3 each `f0 + γ_i f1` agrees on `S_i` with a degree-`<4` polynomial | ✔ |
| C4 FULL-MCA (`f1` agrees with no degree-`<4` polynomial on any `S_i`) | ✔ |
| C5 `S_i` is exactly the maximal agreement set | ✔ |
| C6 regularity `max_{i<j}|S_i ∩ S_j| = 4 = k` | ✔ (all six intersections `= 4`, saturated) |
| C7 `Σ c_i = 8 > 7 = 2κ − 1` | **violation, defect +1** |
| C8 `rank M = 7 = 2κ − 1` | ✔ |
| C9 no correlated codeword pair (max pair agreement `= 4 = k`) | ✔ |
| C10 per-window grading defects `d_i(h) = 2` for every `i` and every `h ∈ {2,4,8}` (the maximum possible, `|Z_i| = 2`); common factor degree `0`; generalized certificate `= 8 = Σc_i` at every `h` | **no certificate** |

An exhaustive challenge table over all of `F_17` confirms the family is complete: exactly
the four challenges `1, 7, 11, 14` reach agreement `6 = k + 2`, every other challenge
reaches at most `5`, and `f_1` alone reaches only `5 < 6`.

Smallest witness at the standard rates `ρ = 1/4, δ = 1/2` (on the Johnson boundary):
`n = 8, k = 2, e = 4, q = 17`, `m = 6`, `Σc_i = 12 > 11 = 2κ−1`.

### 4. Scalable witness: **YES**

The **quarter-pair construction** (`capviol_quarters.py`) is explicit and scales:

> Partition `D` (|D| = n, 4 | n) at random into four quarters `Q_1,…,Q_4` of size `n/4`.
> Put `k = n/4`, `e = n/2` and take the `m = 6` windows `S_{ab} = Q_a ∪ Q_b` (`a < b`).
> Then every pairwise intersection is exactly `n/4 = k` (regular, saturated), and
> `Σ_i c_i = 6·(n/2 − n/4) = 3n/2 = 2κ > 2κ − 1`.
> Tune the last challenge to a root of the (degree-`≤ c`) stacked determinant.

Results (all: windows maximal, FULL-MCA, regular with `maxint = k`, common factor `0`,
`min_{h>1} Σ_i d_i(h)` large, so **nongraded**):

| n | q | `Σc_i` | `2κ−1` | rank M | `min_h Σd_i(h)` |
|---:|---:|---:|---:|---:|---:|
| 8 | 17, 41 | 12 | 11 | 10 | 12, 16 |
| 16 | 17, 97 | 24 | 23 | 20 | 24, 32 |
| 32 | 97, 193 | 48 | 47 | 40 | 52, 44 |
| 64 | 193, 257 | 96 | 95 | 80 | 96, 96 |
| 128 | 257, 641 | 192 | 191 | 160 | 176, 188 |
| 256 | 257, 769 | 384 | 383 | 320 | 364, 420 |
| 512 | 7681, 12289 | 768 | 767 | 640 | 772, 796 |

Success rate 14/14. Note the rank defect of this family is not `1` but exactly `k`:
`rank M = 2κ − k` at every size — the quarter-pair partition supports a `k`-dimensional
family of bad lines (modulo codeword pairs) with 6 bad challenges each.

Random (non-quarter) windows give the same phenomenon at
`n = 8,12,14,16,20,22,24,28,30,32,36,40,48,64`, on two primes for most rows.
The excess `Σc_i − (2κ−1)` observed is `+1` to `+4`; it does **not** grow with `n`.
At `n = 12, q = 37` the exhaustive fibre enumeration reaches `m = 7`, `Σc_i = 21` vs cap
`17` (defect `+4`), and all seven 6-element subfamilies are separately deficient.

### 5. Strongest surviving generalized grading certificate: **NONE**

For every witness, all of the following fail:

* **common-factor reduction** — `deg gcd_i A_i = 0` in all 495 records (searched for and
  enforced);
* **plain `Graded(h)`** for every nontrivial `h | n` — the per-window defect sum
  `Σ_i d_i(h)` is bounded below by `20`–`796` in the large witnesses, and by `4` in the
  minimal `n = 8` witness (the theoretical minimum for a nonzero defect there);
* **per-window factorisation `A_i = G_i·B_i(X^h)`** with low-degree `G_i` — this is exactly
  what `d_i(h)` measures: `d_i(h) = deg G_i` for the best `B_i`, and the generalized
  certificate `Σ_{r<h} min(Σ_i #{j < c+d_i : j ≡ r}, 2κ_r)` equals `Σ_i c_i` at every `h`,
  i.e. it explains **no** rank drop at all;
* **character / quotient reformulation** — the sector decomposition of §Phase 4 requires
  `H`-closed `Z_i`; with defects this large no sector system is smaller than the original;
* **correlated pair** — max agreement of a codeword *pair* with `(f_0, f_1)` equals `k`
  exactly (the generic floor; measured against a random-line control,
  `capviol_c9_control.py`) for the high-`q` witnesses, so the earlier suspicion that
  cap-violating families always carry a `k+1` "explaining pair" is **also refuted**;
  the `k+1` values seen at small `q` are the generic noise floor, not structure;
* **low displacement rank / codeword locus / projective residual locus** — all are
  functions of the `Z_i` and inherit the negative verdict: no common factor, no coset
  structure, no shared low-degree annihilator (`∩_i V_i = 0`, `Σ_i R_i = P` in all hits).

**What does survive** (and is the cheapest replacement mechanism, see items 12–13):

1. **The corrected free-challenge cap** `Σ_i (c_i − 1) ≤ 2κ − 1`. Not a single one of the
   495 witnesses, nor any output of the exact hill-climb maximiser (which optimises this
   statistic directly, `capviol_maxbad.py … S1`), violates it. Best measured values:
   `13` vs `17` at `n=12`, `18` vs `23` at `n=16`.
2. **The leave-one-out nondegeneracy dichotomy** (new, and the reason earlier searches
   were blind): if `U_{i_0} = ∩_{j ≠ i_0} V_j ≠ 0`, then for `u ∈ U_{i_0}` the pair
   `(λ, μ) = (−γ_{i_0} u, u)` solves the whole stacked system for **every** value of
   `γ_{i_0}`. Hence the stacked determinant vanishes identically, the corank is a
   *systematic* `≥ 1` (measured mean corank rises from ≈0.4 at `n=12` to ≈1.7 at `n=40`
   at random challenges, independently of `q`), and every such solution fails FULL-MCA on
   `m − 1` windows. Filtering these out (`capviol_tune3.py`) is what unlocked the
   witnesses at `n ≥ 32`.
3. `rank M ≤ 2κ − 1` for FULL-MCA families — observed with equality in every
   minimal-defect witness, never exceeded.

### 6. Exact quotient decomposition: **TRUE**

For an exactly `H`-graded family (`H = μ_h ≤ D`, `h | n`, every `Z_i` a union of
`H`-cosets, hence `h | e`) the decomposition is exact and derived symbolically (Phase 4
below): `P = ⊕_r X^r P_r`, `R_i = ⊕_r X^r R_{i,r}`, `M ≅ ⊕_r M_r`, and
`rank M = Σ_r rank M_r`. Verified numerically on the graded witnesses
(`n=16, h=4`: `Σ_r min(rows_r, 2κ_r − 1) = 20 = rank M`).

### 7. Exact Bad-set descent: **PARTIAL**

* **True, corrected form (challenge level).** For `H`-closed windows `S = π^{-1}(S')`:
  `γ ∈ Bad(D)` with window `S` **⟺** `γ ∈ Bad_r(D/H)` with window `S'` for **every**
  sector `r`. So `Bad_H(D) = ⋂_r Bad_r(D/H)` (matched windows), giving
  `#Bad_H(D) ≤ min_r #Bad_r(D/H)`.
* **True, but a different statement (index level).** `R_i ⊆ K` ⟺ `R_{i,r} ⊆ K_r` for all
  `r`; hence window `i` is FULL-MCA **iff** it is FULL-MCA in *some* sector — a union
  statement over `r`.
* **False as written.** The claim `Bad(D) = ⋃_r Bad_r(D/H)` in
  `GRADING_COMPLETENESS_REPORT.md` conflates the two: the union is over FULL-MCA indices,
  the descent of bad challenges is an intersection. The intersection form is the strong
  one (it is what yields a recursion).
* **Genuine gap.** Different challenges may be FULL-MCA in different sectors, so no single
  sector need be FULL-MCA for all `i`; the descent then bounds the *graded* branch only.

### 8. Parameter transformation under `D → D/H`

`H = μ_h`, `D' = D^h = μ_{n'}`, `π(x) = x^h`, `n' = n/h`. The change of basis is the
`h`-point DFT along each fibre (`h | q−1` automatically, since `h | n | q−1`).

| object | on `D` | on `D' = D/H`, sector `r = 0 … h−1` |
|---|---|---|
| domain size | `n` | `n' = n/h` |
| error count | `e` | `e' = e/h` (**forces `h | e`**) |
| window | `S_i = π^{-1}(S'_i)` | `S'_i`, `|S'_i| = n' − e'` |
| slack | `c` | `c_r = #{j < c : j ≡ r (mod h)} = ⌈(c−r)/h⌉`, `Σ_r c_r = c` |
| residual dim | `κ = c + e` | `κ_r = c_r + e' = ⌈(κ−r)/h⌉`, `Σ_r κ_r = κ` |
| rate parameter | `k = n − κ` | `k_r = n' − κ_r`, `Σ_r k_r = k` |
| vanishing poly | `A_i(X) = A'_i(X^h)` | `A'_i(T) = ∏_{y ∈ Z'_i}(T − y)`, `deg = e'` |
| residual space | `R_i = A_i F[X]_{<c}` | `R_{i,r} = A'_i F[T]_{<c_r}` |
| **challenges** | `γ_1 … γ_m` | **unchanged** — the sector projection is `F`-linear, so `(f_0 + γ f_1)_r = f_{0,r} + γ f_{1,r}` |
| relative radius | `δ = e/n` | `δ' = δ` exactly |
| rate | `ρ = k/n` | `ρ_r = k_r/n' = ρ ± O(h/n)` |
| regularity | `|S_i ∩ S_j| ≤ k` | `|S'_i ∩ S'_j| = |S_i ∩ S_j|/h ≤ k/h`, versus sector budget `k_r ≈ k/h ± 1` — **can degrade by 1** |

Edge cases, all checked:

* `h ∤ e` — impossible for an exactly graded family; the generalized (defect `d_i`) version
  replaces `c_r` by `#{j < c + d_i : j ≡ r}` and the direct sum becomes an inclusion only.
* `h ∤ k` and `h ∤ κ` — harmless for the decomposition (only `c` and `e` are split), but
  the sector rate `k_r = n' − e' − c_r` differs from the naive `#{t < k : t ≡ r}` by an
  offset `k mod h`; the two agree sector-by-sector iff `min(k mod h, c mod h) = 0`, and
  always agree in total (`Σ_r k_r = k`). This ±1 is the only rounding in the descent.
* `c < h` — sectors with `c_r = 0` impose no condition; their solutions are never FULL-MCA
  and must be dropped from the intersection.
* `h ∤ n` — excluded (`H ≤ D` requires `h | n`).

### 9. Derived `#Bad` recurrence

Write `B(n, k, e)` for the maximum number of FULL-MCA bad challenges of a regular family.

* **Base (measured, item 5.1):** `B ≤ (2κ − 1)/(c − 1)` where `c = n − e − k`.
  (The plain `B ≤ (2κ−1)/c` is **false** — this report.)
* **Balanced graded branch (`h = 2`):** `B_graded(n,k,e) ≤ min_{r∈{0,1}} B(n/2, k_r, e/2)`.
* **Arbitrary divisor `h`:** `B_graded ≤ min_{0 ≤ r < h, c_r ≥ 1} B(n/h, k_r, e/h)`;
  since `δ' = δ` and `ρ_r = ρ ± O(h/n)`, the sector problem is the *same* problem up to
  rounding, so the recursion is rate-preserving and contracts `n` by `h`.
* **Generalized grading with defects `d_i`:** `c_r ↦ c_r + ⌈d_r/h⌉` where `d_r` is the
  sector share of `Σ_i d_i`; the sector bound degrades to
  `B ≤ (2κ_r − 1)/(c_r + ⌈d_r/h⌉ − 1)` — never worse than the unsplit bound.
* **Mixture of graded and nongraded branches (the only honest form now that the
  cap-violation ⇒ grading implication is dead):** at each level either the family is
  graded and descends, or it is not and is bounded directly by the free-challenge cap:
  ```
  B(n,k,e) ≤ max{ (2κ−1)/(c−1) ,  min_{h|n, h>1} min_r B(n/h, k_r, e/h) }
  ```
  which telescopes to
  ```
  #Bad ≤ (2κ − 1)/(c − 1) + O(log n)          (levels contribute the ±1 rounding only)
  ```
  and, in the crudest union-bound form one might be forced into if the intersection
  descent is unavailable, `M(n) ≤ h·M(n/h) + (2κ−1)/(c−1)`, i.e. `M(n) = O(n)`.

### 10. Resulting exponent α

* Intersection/min descent: `#Bad = O(κ/c) + O(log n)` ⇒ **α = 0** (constant in `n` at
  fixed rates; `O(log n)` from rounding).
* Union-bound descent (worst admissible): **α = 1**.
* Prize budget at `n = 2^20`, `k = 2^19`: `α < 2.8966054` ⇔
  `#Bad ≤ 2^{57.932} = |F|·2^{-128}` with `log₂|F| = 185.9321` (KoalaBear degree-6
  extension) — i.e. a 128-bit soundness target.

### 11. Prize-sufficient: **YES on the counting side, with ≈ 2^{37.9} of margin**

Even the crudest recurrence (`α = 1`, `#Bad ≤ 2^20`) beats `2^{57.93}` by a factor
`2^{37.9}`. The descent may lose up to `h^{2.8966} ≈ 7.44` per halving (20 levels) and
still fit the budget. **Caveat:** this is the *counting* side only. Since
"cap violation ⇒ grading" is now false, the recursion has **no complete coverage**: the
nongraded branch is bounded by the free-challenge cap, which is a measured regularity, not
a theorem. The prize therefore hinges on item 13, not on the quotient recursion.

### 12. DECISION: **SWITCH TO ALGEBRAIC RESIDUAL LOCUS**

Reasoning:

* *PROVE CAP-VIOLATION STRUCTURE THEOREM* — impossible: the statement is false, with 495
  certified counterexamples and an explicit family up to `n = 512`.
* *PROVE QUOTIENT THEOREM* — the theorem is true and reusable (item 6), and its corrected
  Bad-descent (item 7) is worth having, but it is no longer on the critical path: it only
  covers the graded branch, which is now known not to be all of the cap-violating world.
* *KILL STRUCTURAL ROUTE* — correct as far as the grading hypothesis goes, but throws away
  the one thing that survived every attack.
* *SWITCH TO ALGEBRAIC RESIDUAL LOCUS* — the surviving mechanism is precisely a statement
  about the determinantal locus of the stacked residual system inside challenge space:
  the plain cap counts equations against unknowns **with the challenges frozen**, while
  the challenges are free. Restoring them gives the corrected cap and explains every
  measurement, including the exact maximum `m` observed at `n = 12`.

The dimension count (heuristic, to be proved): a family with slacks `c_i` requires the
`(Σc_i) × 2κ` stacked matrix to have rank `≤ 2κ − 1`, which is a determinantal condition
of codimension `(Σ_i c_i − 2κ + 1)·1` in the space of matrices; the challenges supply `m`
free parameters, so a solution can exist only if
`Σ_i c_i − 2κ + 1 ≤ m`, i.e. `Σ_i (c_i − 1) ≤ 2κ − 1`. At `n = 12, k = 3, e = 6` this
predicts `m ≤ 8` where the plain cap predicts `m ≤ 5`; the exhaustive search attains
`m = 7` and never 9.

### 13. Exactly ONE next big lemma

```
LEMMA (free-challenge residual cap).

Let D ⊆ F_q^*, |D| = n, k < n, κ = n − k, and let (f_0, f_1) be a line in F_q^D.
Let γ_1, …, γ_m ∈ F_q be distinct, let S_i be the maximal agreement set of
f_0 + γ_i f_1 with RS_k(D), c_i = |S_i| − k ≥ 1, and assume FULL-MCA:
f_1 agrees with no degree-<k polynomial on any S_i.  Then

                     Σ_{i=1}^m (c_i − 1)  ≤  2κ − 1 .

Equivalently, in dual coordinates: with R_i = A_i·F[X]_{<c_i} ⊆ P = F[X]_{<κ},
the locus of (γ_1,…,γ_m) for which the stacked map
    P ⊕ P ⟶ ⊕_i (P / R_i^⊥-pairing),   (λ, μ) ↦ (⟨R_i, λ + γ_i μ⟩)_i
is not injective has codimension Σ_i c_i − 2κ + 1 in challenge space, hence is
empty unless that codimension is at most m.
```

Why this one: it is the unique statement that survived the whole falsification campaign
(495 witnesses, an exact maximiser run directly against it, and the leave-one-out
degeneracy analysis); it is *strictly weaker* than the plain cap, which is now known to be
false, yet in the prize regime (`c = Θ(n)`) it still gives `m = O(1)`; and it is a pure
linear-algebra/determinantal statement about the residual spaces `R_i ⊆ P`, with no
grading, no quotient and no genericity assumption. Its proof must supply what the
dimension count only suggests: an actual lower bound on the rank of the stacked system
outside a codimension-`(Σc_i − 2κ + 1)` locus, together with the leave-one-out
nondegeneracy (`∩_{j≠i} V_j = 0`) as the hypothesis that excludes the trivial solutions.

---

## PHASE 4 — SYMBOLIC AUDIT OF QUOTIENT DESCENT (paper-level derivation)

Let `h | n`, `H = μ_h ≤ D = μ_n`, `π : D → D' = μ_{n'}`, `π(x) = x^h`, `n' = n/h`.
Since `n | q − 1` we have `h | q − 1`, so `h` is invertible in `F_q` and `F_q ⊇ μ_h`.

**(4.1) Fibrewise DFT.** For `f : D → F_q` and `y ∈ D'` set
`f_r(y) = h^{-1} Σ_{x : x^h = y} f(x)·x^{-r}` for `r = 0,…,h−1`. This is the `h`-point DFT
along the fibre `π^{-1}(y)` (a coset of `H`), so `f(x) = Σ_r x^r f_r(x^h)` and the map
`f ↦ (f_0,…,f_{h−1})` is an `F_q`-linear isomorphism `F_q^D ≅ ⊕_r F_q^{D'}`.

**(4.2) Splitting of polynomials.** Every `p ∈ F[X]_{<k}` is uniquely
`p = Σ_r X^r p_r(X^h)` with `deg p_r < K_r := #{t < k : t ≡ r (mod h)}`, and
`Σ_r K_r = k`.

**(4.3) Splitting of agreement.** If `S = π^{-1}(S')` is `H`-closed then
`f ≡ p on S ⟺ ∀ r : f_r ≡ p_r on S'`. (On the fibre over `y`, `p(x) = Σ_r x^r p_r(y)`, so
the restriction of `f − p` to the fibre vanishes iff all `h` of its DFT coefficients do.)
This is an **if and only if**, which is what makes the descent exact.

**(4.4) Splitting of the residual data.** If `Z_i = π^{-1}(Z'_i)` then
`A_i(X) = ∏_{y ∈ Z'_i}(X^h − y) = A'_i(X^h)`, `deg A'_i = e' = e/h`, and
`P = F[X]_{<κ} = ⊕_r X^r·F[X^h]_{<κ_r}` with `κ_r = ⌈(κ−r)/h⌉`,
`R_i = A_i·F[X]_{<c} = ⊕_r X^r·A'_i(X^h)·F[X^h]_{<c_r}` with `c_r = ⌈(c−r)/h⌉`.
Because `κ = c + e` and `e = h e'`, we get `κ_r = c_r + e'` **exactly** in every sector:
each sector is literally the residual construction on `D'` with slack `c_r`, error `e'`,
and code parameter `k_r = n' − κ_r`.

**(4.5) Splitting of the stacked matrix.** The stacked map is `F_q`-linear and preserves
the `X`-exponent grading modulo `h`, hence in the DFT basis
`M ≅ ⊕_{r<h} M_r`, `rank M = Σ_r rank M_r`, and the FULL-MCA condition is
`R_i ⊄ K` ⟺ `∃ r : R_{i,r} ⊄ K_r`.

**(4.6) Bad-set descent.** Combining (4.3) with the fact that the challenges are scalars
(so the sector projection commutes with `f_0 + γ f_1`):
`γ` is bad on `D` with `H`-closed maximal window `π^{-1}(S')` **iff** `γ` is bad in every
sector `r` on `D'` with the *same* window `S'`. Hence `Bad_H(D) = ⋂_r Bad_r(D')` with
matched windows, and `#Bad_H(D) ≤ min_r #Bad_r(D')`. The reverse composition also works
(`p = Σ_r X^r p_r(X^h)` has degree `< k` by construction of `K_r`), so no information is
lost in either direction — *provided* the windows are matched. Without matching windows
only the inclusion survives.

**(4.7) Where it stops.** (i) sectors with `c_r = 0` carry no condition; (ii) sector
regularity can be one unit short of the sector budget; (iii) different challenges may be
FULL-MCA in different sectors; (iv) with grading defects `d_i > 0` the direct sum
degenerates to an inclusion `R_i ⊆ ⊕_r X^r B'_i F[X^h]_{<c_r + ⌈d_i/h⌉}` and the
certificate is only an upper bound on the rank. Items (iii)–(iv) are the reason the
descent is rated PARTIAL.

---

## METHODOLOGICAL NOTES (recorded so they are not rediscovered)

1. **Always recompute maximal agreement windows** before judging cap or regularity. An
   early `n = 32, k = 15, e = 11` "hit" was spurious: the true windows had size 27, i.e.
   radius 5, and `max|S_i ∩ S_j| = 26 > k`.
2. **Random challenges cannot find these families.** The cap-violating set is a
   positive-codimension subvariety of challenge space; 224 annealing runs and 847 swept
   lines with random `γ` produced one nongraded witness. Tuning one challenge to a root
   of the stacked determinant produces them at will.
3. **Filter out leave-one-out degeneracy first** (item 5.2). Without it the stacked
   determinant is identically zero at `n ≥ 32` in most families and every kernel vector
   fails FULL-MCA on `m − 1` windows; with it, the hit rate at `n = 32…64` is 25–75%.
4. **Calibrate every "structural" invariant against a random-line control.** The
   apparent `k+1` correlated pair in the small-`q` witnesses is the generic noise floor
   (`capviol_c9_control.py`): at `q = 12289` random lines give exactly `k`, and so do the
   witnesses.
5. **Additive / linearized-polynomial constructions are a dead end** for this question:
   they produce many bad challenges but with `c = |S| − k` tiny, so `Σc_i < 2κ` and there
   is no cap violation.

## CROSS-REFERENCES

* `GRADING_COMPLETENESS_REPORT.md` — its central claim "every observed violation of the
  plain cap was graded" is **refuted** by this report; its
  `Bad(D) = ⋃_r Bad_r(D/H)` should read `Bad_H(D) = ⋂_r Bad_r(D/H)` (matched windows),
  the union statement being about FULL-MCA indices. That file is left unedited.
* `REGULAR_RANK_CAP_KILL_REPORT.md` — the queued lemma `rank M ≤ 2κ − 1` under FULL-MCA is
  untouched by this report and remains true in all 495 witnesses.
* Data: `analysis/capviol_data/{tune,tune_belowJ,tune3_small,tune3_bigJ,tune3_scale,
  exhaust_t1}.jsonl`, `quarters.json`, `maxbad_S1.json`, `c9_control.json`, and the
  matching `.log` files.
