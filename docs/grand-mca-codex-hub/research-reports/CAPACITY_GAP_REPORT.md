# The capacity-gap pencil: the MCA bad set is exponential near capacity

**Files.** `RequestProject/Root/CodingTheory/CapacityGapPencil.lean`,
`RequestProject/Root/CodingTheory/CapacityGapCosets.lean` (both build, no `sorry`, axioms
`propext, Classical.choice, Quot.sound` only).  Independent exact-arithmetic check:
`analysis/capacity_gap_check.py`.

Notation: `n = |D|`, `k` the dimension, `e` the radius, `κ = n − k`, `δ = e/n`, `ρ = k/n`,
and the **capacity gap**

```
c := n − k − e = κ − e   (absolute),        η := 1 − ρ − δ = c/n   (relative).
```

`#Bad = (badSet k e f₀ f₁).card` is the number of bad challenges of one MCA line, in the
project's own definitions (`MCA.lean`).

---

## 1. The construction

Let `D` contain `m` pairwise disjoint blocks `O₁,…,O_m` of size `c` whose vanishing
polynomials are binomials,

```
∏_{x ∈ O_i} (X − x) = X^c − b_i .
```

Put `k = c·s`, `t = s+1`, and take the **power pencil**

```
f₀(x) = x^{k+c},    f₁(x) = x^k .
```

For a set `I` of `t` block indices let `S_I = ⋃_{i∈I} O_i`, of size `k + c = c·t`.  Then

```
∏_{x ∈ S_I}(X − x) = ∏_{i∈I}(X^c − b_i) = X^{k+c} − (Σ_{i∈I} b_i)·X^{k} + R_I ,
                                                              deg R_I ≤ k − c < k
```

(`prod_pow_sub_C_shape`).  Hence at the challenge

```
γ_I = − Σ_{i∈I} b_i
```

the line point `f₀ + γ_I f₁` coincides on `S_I` with the polynomial `−R_I` of degree `< k`,
while the direction `f₁ = x^k` is **not** interpolable on `S_I` (a degree-`k` polynomial
cannot vanish at `|S_I| = k + c > k` points).  So `S_I` witnesses badness of `γ_I`
(`isBad_powerPencil`, `isBad_blocks`), and distinct block-sums give distinct challenges:

> **Theorem (`card_badSet_ge_blocks`).**  If the `t`-subset sums of the `b_i` are pairwise
> distinct then, at radius `e = n − k − c`, i.e. at capacity gap exactly `c`,
> ```
> #Bad ≥ C(m, s+1) = C(n/c, k/c + 1).
> ```

Two families of domains realise the hypotheses **unconditionally**:

* **gap `c = 1`, any dissociated domain.**  Blocks are singletons, `b_i = x_i`; the
  hypothesis is that the `(k+1)`-subset sums of `D` are distinct.  Concretely
  `D = {1, 2, 4, …, 2^{m−1}} ⊆ ZMod p` for any prime `p > 2^m`
  (`twoPowDomain`, `sum_inj_twoPowDomain`).
* **any gap `c ≥ 1`, `μ_c`-coset domains.**  `D = ⋃_{i<m} 2^i·μ_c ⊆ ZMod p` for a prime `p`
  with `c ∣ p − 1` and `p > 2^{c·m}`; blocks are the cosets, `b_i = 2^{c i}` are the powers
  of `2^c`, hence dissociated (`cosetDomain`, `card_badSet_ge_cosets`).  Such primes exist
  for all `c, m` (`exists_prime_coset_parameters`, Dirichlet), giving the fully
  self-contained `exists_capacityGap_counterexample`.

## 2. Gap one is *exactly* solved

At `c = 1` the construction is optimal, because every bad challenge owns a `(k+1)`-window on
which the direction is not interpolable, and two challenges cannot own the same one:

> **Theorem (`card_badSet_le_choose_gapOne`).**  If `n = k + 1 + e` then for **every** line
> `#Bad ≤ C(n, k+1) = C(n, e)`.
>
> **Theorem (`card_badSet_eq_choose_gapOne`, `card_badSet_twoPowDomain`).**  On a domain with
> distinct `(k+1)`-subset sums the power pencil attains it: `#Bad = C(n, k+1)` exactly.

So at capacity gap `1` the maximum of `#Bad` over all Reed–Solomon MCA lines is **exactly**
`C(n, e)`.  In particular the project's window-free binomial bounds
(`card_badSet_le_circuit`, `card_badSet_le_choose_radius`, `#Bad ≤ C(n,e)`) are **tight**, not
merely convenient — they cannot be replaced by any polynomial bound.

Numerically (`analysis/capacity_gap_check.py`, exhaustive over all challenges and all maximal
windows): `#Bad` equals the predicted set exactly for
`(p,c,m,s) = (101,1,6,1), (101,1,6,2), (131,1,7,2), (101,2,3,1), (101,2,4,1), (97,3,4,1),
(97,3,4,2)`.

## 3. Quantitative consequences

Take `n = 2(k+1)`, `e = k+1`, i.e. rate `ρ ≈ 1/2` and radius one coordinate below the
capacity radius `κ`.  Then (`two_pow_card_le_mul_card_badSet_twoPowDomain`)

```
2^n ≤ n · #Bad ,          i.e.   #Bad ≥ 2^n / n ,
ε_mca ≥ C(n, e)/|F|       (choose_div_card_le_epsMCAmax_twoPowDomain).
```

At a general gap `c`, `#Bad ≥ C(n/c, k/c + 1) = exp(Θ((n/c)·H(ρ))) = exp(Θ(H(ρ)/η))`
(`choose_div_card_le_epsMCAmax_cosets`).

**Therefore:**

1. **The Grand-MCA / proximity statement in the form "`ε_mca ≤ poly(n)/|F|` for every
   `δ < 1 − ρ`" is FALSE**, and false already at `δ = 1 − ρ − 1/n`.
2. Any true bound must depend on the gap to capacity at least like `exp(Ω(1/η))`; no bound
   polynomial in `n` *and* in `1/η` can exist.  A `poly(n)` bound is possible only in the
   band `c = Ω(n / log n)`, i.e. `η = Ω(1/log n)`.
3. The refutation costs a large field: it needs `|F| ≳ #Bad`, i.e. `log|F| = Ω(n/c)`.  For a
   fixed field the same construction gives `#Bad = #{distinct block sums} ≤ |F|`; the
   statement it refutes is the *counting* one, `#Bad ≤ poly(n)`.

**What is NOT refuted.**  Nothing in the Johnson regime `δ < 1 − √ρ` (where
`MCAJohnson.lean` etc. give `#Bad ≤ n·Λ`), nothing in unique decoding (there `e ≤ c`, and the
construction only yields `#Bad ≥ C(s+2, s+1) = k/c + 2`, consistent with the known
`e + 1` and `|D|/(κ−2e+1)` behaviour), and nothing at a *constant* gap to capacity: with
`c = Θ(n)` the bound `C(n/c, ·)` is `O(1)`.  Protocol parameter points that keep a constant
`η` (the practically used ones) are untouched.

## 4. Where this leaves the picture

Known, after this work, as a function of the absolute gap `c = κ − e`:

| regime | best upper bound | best lower bound |
|---|---|---|
| `c ≥ 2e+1` (i.e. `3e < κ+1`) | `e+1` (`card_badSet_le_succ_radius`) | `e+1` (common-window pencil) |
| `e ≤ c ≤ 2e` (unique decoding) | `(k+1)e+1` (`card_badSet_le_unconditional`) | `≈ n/e` (fold pencil) |
| `c` small, `δ` beyond Johnson | `C(n, e)` (circuit/binomial) | `C(n/c, k/c+1)` (this work) |
| `c = 1` | `C(n, k+1)` | `C(n, k+1)` — **equal** (this work) |

The natural conjecture suggested by the table is the **gap-layer law**

```
max #Bad = exp(Θ((n/c)·H(k/n)))       for c = o(n / log n),
```

proved here in the `≥` direction for all `c` and in both directions for `c = 1`.

## 5. Main remaining obstruction

Whether `#Bad` can be superpolynomial at a **constant** relative gap `η` (i.e. `c = Θ(n)`).
Combinatorially it is not excluded: the windows of distinct bad challenges only need to
pairwise intersect in `≤ k` positions, and there are `≈ C(n,k+1)/C(k+c,k+1)` such
`(k+c)`-families.  The obstruction is algebraic: for `c ≥ 2` a window `S` supports a bad
challenge only if the two residual vectors of `(f₀, f₁)` in `F^{c}` at `S` are proportional,
which is `c − 1` conditions per window.  The block construction satisfies them by symmetry
(all elementary symmetric functions `e₂,…,e_c` of a block union are forced to sit below
degree `k`), and the analysis in §1 shows that any binomial-block design must use blocks of
size `> c/2`, which caps `m` at `≈ 2n/c` — the exponent `n/c` is intrinsic to *this* method.

### 5.1 The Schubert count, and what it predicts

In the quotient picture of `FREE_CHALLENGE_INCIDENCE_LOCUS_REPORT.md` (`V = F^D/C ≅ F^κ`, an
MCA line is a 2-plane with a marked point, `γ` bad iff the line meets the image `L_Z` of an
`e`-set), `dim L_Z = e = κ − c`, so "the 2-plane meets `L_Z`" is a Schubert condition of
codimension `c − 1`.  Counting `C(n,e)` windows against `q^{c−1}` conditions and against the
trivial cap `#Bad ≤ q` balances at

```
q ≈ C(n,e)^{1/c},        #Bad ≈ C(n,e)^{1/c} = exp(Θ(n·H(δ)/c)) = exp(Θ(H(δ)/η)),
```

the same exponent `n/c` as the block construction of §1 — two independent derivations of the
gap-layer law.  Note that this generic count is *constant* at constant `η`, while the
degenerate families (common-window pencil `e+1`, fold pencil `≈ n/e`) grow polynomially in
`n`; the expected truth is therefore

```
max #Bad  ≍  poly(n)  +  exp(Θ(1/η)) ,
```

with Grand MCA (a `poly(n)` bound) holding exactly in the band `η = Ω(1/log n)`.

## 6. Single best next step

Decide the constant-gap case by a counting (second-moment) construction: for a random domain
`D` and random `f₀, f₁` over `F_q`, estimate the number of `(k+c)`-subsets whose residual
`2 × c` matrix has rank `1`.  The heuristic count is `C(n, k+c)/q^{c−1}`, so balancing
against `#Bad ≤ q` predicts `#Bad ≈ C(n,k+c)^{1/c}`, still exponential at constant `η`.
Making this rigorous (or proving the matching upper bound `#Bad ≤ exp(O(n/c))`) settles the
gap-layer law and therewith the last quantitative form of Grand MCA that is still open.
