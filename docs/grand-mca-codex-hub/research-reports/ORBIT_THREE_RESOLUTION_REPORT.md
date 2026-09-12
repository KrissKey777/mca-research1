# Resolution of the `d = 3` Frobenius-orbit case

Status legend: **[MC]** machine-checked Lean theorem (no `sorry`, axioms
`propext / Classical.choice / Quot.sound` only), **[EX]** exhaustive computation,
**[SA]** sampled computation, **[CB]** conjectural bridge.

Deployed calibration constants (KoalaBear row):

```
p  = 2130706433 = 2^31 - 2^24 + 1        F = F_{p^6}
n  = 2^21, k = 2^20, e = 981104          a = n - e = 1116048,  t = a - k = 67472
B* = 274980728111395087 = floor(|F| / 2^128)
p^2 + p + 1 = 4539909905758289923        B*/(p^2+p+1) = 0.0605696443...
```

---

## 1. Strongest new result

**`d = 3` is genuinely dangerous, and it is dangerous for a reason that has nothing to do
with linear sets or low-degree loci.**

**[MC] `Root.CodingTheory.card_badSet_ge_curve`** (`OrbitThreeSharpness.lean`).
Let `sigma` be a field automorphism of finite order with distinct iterates, `D` a set of
`sigma`-fixed points, `u_j(x) = x^{j+1}` the rational normal curve of words, `b = (1,0,0)`,
and `A = (A0,A1,A2)` *any* coefficient triple not annihilated by a nonzero fixed covector
(that is: the pencil has Frobenius-orbit dimension exactly three).  On the row `k = 1`,
`e = |D| - 2` the pencil

```
f0(x) = A0 x + A1 x^2 + A2 x^3 ,    f1(x) = x
```

satisfies

```
|D| (|D| - 1)  <=  2 * #Bad .
```

Each unordered pair `{x,y} ⊆ D` contributes the officially bad challenge
`gamma_{x,y} = -(A0 + A1 (x+y) + A2 (x^2 + xy + y^2))`, witnessed by the two-point support
`S = {x,y}` on which the entire rational hyperplane `(u(x) - u(y))^perp` is explained by
*constants* — a different constant for each pair.  Distinct pairs give distinct challenges.
Against the orbit upper bound `1 + q + q^2` this attains the budget up to a factor two.

**[MC] `Root.CodingTheory.KoalaRow.orbitThree_exceeds_prizeThreshold`**
(`KoalaBearOrbitThreeWitness.lean`).  Instantiated **inside the deployed field**
`F = F_{p^6}` with `sigma` the deployed Frobenius, `D = Fix(sigma) = F_p` (so `n = p`),
`A` the first three vectors of an `F_p`-basis of `F_{p^6}` (hence orbit dimension exactly
three), `k = 1`, `e = n - 2`:

```
p^2 - p  <=  2 * #Bad ,      hence      B*  <  #Bad     (by a factor > 8).
```

The witness is non-vacuous: `coeffA` is constructed, and its orbit-dimension hypothesis
`coeffA_independent` is proved from the fact that Frobenius-fixed scalars lie in the prime
field.

**Caveat, stated precisely.**  This is *not* a counterexample to the Prize.  The row is
`k = 1`, relative radius `1 - 2/n`, whereas the deployed row has rate `1/2` and relative
radius `0.4679`.  What it is, is a **barrier**: official badness at orbit dimension three,
in the deployed field and against the deployed threshold constant, can exceed `B*`.

**Second new result — an inverse theorem.**

**[MC] `Root.CodingTheory.card_badSet_le_of_closeDir`** (`RationalDirectionCount.lean`).
With `q = #Fix(sigma)` and

```
closeDirSet = { lambda != 0 : sigma-fixed, the rational word  sum_j lambda_j u_j
                is within Hamming distance e of the code } ,
```

for every orbit-dimension-three pencil

```
(#Bad - 2) * (q - 1) * (q^2 - 1)  <=  #closeDirSet * q^2 .
```

Projectively: **at least `#Bad - 2` of the `q^2 + q + 1` rational directions of the orbit
space carry an `e`-close word.**  The proof is a double count of the incidences
`c ⊥ lambda` between code-good covectors and close directions, using
**[MC] `card_orthFix`**: a nonzero rational covector has exactly `q^2` rational vectors
orthogonal to it.

---

## 2. Exact quantitative consequence for Grand MCA

**[MC] `Root.CodingTheory.KoalaRow.prizeBreaking_forces_closeDirections` /
`prizeBreaking_closeDirection_density`** (`KoalaBearCloseDirections.lean`).  On the deployed
row, if an orbit-dimension-three pencil breaks the Prize threshold at any radius `e`, then

```
B* * (p - 2) = 585903205788011996252704497  <=  #closeDirSet ,
p^3 = 9673215236899702176256884737          <   17 * #closeDirSet .
```

That is: **more than 6.05% of the points of `PG(2,p)` — more than
`2.7498 * 10^17` distinct rational directions — must each carry a word within the deployed
radius `e = 981104` of `RS[F_{p^6}, mu_{2^21}, 2^20]`.**

The `d >= 3` gate therefore stands, unchanged, and is now known to be **final** in the
orbit-dimension parameter: **[MC]** there is no radius-free `d = 3` safety theorem, so
"Prize-breaking implies `d >= 4`" is **false** as a purely Galois-theoretic statement.

Heuristic calibration (**[CB]**, not verified): the per-direction description cost of one
`e`-close word on this row is `log2 C(n, a) ≈ 2.09 * 10^6` bits, against a total budget of
`3 n log2 p ≈ 1.95 * 10^8` bits for the whole 3-space, suggesting an actual maximum of order
`10^2` close directions rather than `10^17`.  If that gap can be made rigorous, `d = 3`
closes with ~50 bits of slack.  This is a counting heuristic only; no Lean artifact backs it.

---

## 3. Routes killed and opened

**Killed.**

* *Rank-3 linear-set intersection* (proposed route 1, target `2p + 2`).  **[MC]**
  `card_badSet_gt_linear`: for any fixed domain with at least six points, the curve pencil
  has more than `2|D| + 2` bad challenges.  Official badness at `d = 3` is not contained in
  the intersection of two distinct rank-3 linear sets; a fortiori no `O(p)` bound holds.
* *Low-degree annihilator locus* (proposed route 2, degree budget `129 056 130`).  The same
  theorem: the bad set has `Theta(q^2)` points, so it is not contained in any projective
  hypersurface of degree `o(q)`; Serre's bound cannot be triggered.
* *Any radius-free `d = 3` safety proof.*  Killed by the deployed-field witness.
* *Pairwise support rigidity* on the deployed row: already **[MC]**
  `deployed_no_pairwise_rigidity`, `n - 2e = 134944 < k`.  Two witness supports overlap in
  too few positions to force a common codeword, and `n < 3e` rules out triples outright.

**Opened.**

* The problem is now a **word-counting** problem, not a challenge-counting problem:
  *how many points of `PG(2,q)` can carry an `e`-close word, for a rational 3-space of words
  on the deployed row?*  Anything better than `6.05%` closes `d = 3`.
* The correct parameter is the **excess** `t = a - k = 67472`, not the orbit dimension: the
  code-good condition says exactly that the syndrome map `U -> F^S / RS_k(S)` has rank at
  most one, i.e. that a 2-dimensional rational subspace of words is *simultaneously*
  correctable with one common erasure pattern of size `<= e`.

---

## 4. Single best next unresolved object

> **The common-support pair count.**  Fix a 3-dimensional `F_q`-space `U` of words on the
> deployed row.  How many 2-dimensional `F_q`-subspaces `W ⊆ U` admit a single set
> `E ⊆ D` with `|E| <= e` such that every word of `W` agrees with a codeword of
> `RS_k` off `E`?

Equivalently (and this is the exact reformulation the machine-checked results give): how
many distinct kernels can the rank-`<= 1` syndrome maps `U -> F^S / RS_k(S)`,
`|S| >= n - e`, have?  A bound of `B* = 2.7498 * 10^17` closes `d = 3` for the deployed row;
by the sharpness family the bound *must* degrade to `Theta(q^2)` as `t = a - k` drops to `1`,
so any proof has to be quantitative in `t`.
