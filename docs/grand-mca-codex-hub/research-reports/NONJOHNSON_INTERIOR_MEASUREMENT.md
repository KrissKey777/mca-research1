# Non-Johnson composition — pair/fibre measurement on true UD–Johnson interior instances

**Scope.**  This note reports an exact-arithmetic measurement, not a theorem.  Every number
below comes from one of

* `analysis/nonjohnson_composition_scan.py` — brute-force witness enumeration (reference
  implementation of `Root.CodingTheory.IsBad`, used only to validate the fast one);
* `analysis/nonjohnson_syndrome_scan.py` — the syndrome-parallelism form of the bad set
  (cross-checked against the brute force on 6 parameter rows × 40 lines: exact agreement);
* `analysis/nonjohnson_interior_pairs.py` — exact bad sets + induced pairs + |T| strata;
* `analysis/nonjohnson_rank_cap.py` — rank of the stacked window system, core designs;
* `analysis/nonjohnson_pair_budget.py` — budget-optimal designs, verified constructions.

No Lean theorem is claimed here, and nothing in the Lean development was changed.

---

## 0. The window / syndrome form of badness

For a window `S ⊆ D` with `|S| = n − e` let `σ_S` be the syndrome map of the shortened code
`RS_k|S` (it has `c := n − e − k` components).  Then

```
γ bad   ⟺   ∃ S, |S| = n − e :  σ_S(f₀) + γ·σ_S(f₁) = 0   and   σ_S(f₁) ≠ 0 ,
```

i.e. **badness is the parallelism locus of the two syndrome vectors**.  Equivalently, with a
codeword pair `(q₀,q₁)` and `u_i = f_i − q_i`, the Welch–Berlekamp pencil `u₀ + γ·u₁` acquires
`n − e` roots in `D`.  Immediate consequences used below:

* `#Bad ≤ C(n,e)` (each window certifies at most one `γ`) — the project's circuit bound;
* codeword pairs are always solutions, so the stacked conditions of `m` certified challenges
  live in a space of effective dimension `2(n−k)`;
* the *spurious value* at a position `x ∉ T` is `γ_x = −u₀(x)/u₁(x)`, and a pair explains `γ`
  iff `γ_x = γ` for at least `c_T = n − e − |T|` positions off its common agreement `T`.

---

## 1. Instances tested (all strictly interior)

Interior = `2e ≥ n − k + 2` (strictly above unique decoding) **and** `δ = e/n < 1 − √ρ`
(strictly below Johnson).  Boundary rows such as `(8,4,2)`, `(12,6,3)`, `(16,8,4)`, `(9,3,3)`
(`2e = n − k`) and `(9,3,4)` (above Johnson) are *excluded*.

| n | k | e | δ | ρ | Johnson `1−√ρ` | c = n−e−k | 2e−(n−k) | C(n,e) | exact scan |
|---|---|---|---|---|---|---|---|---|---|
| 16 | 4 | 7 | 0.4375 | 0.250 | 0.5000 | 5 | 2 | 11 440 | full |
| 18 | 6 | 7 | 0.3889 | 0.333 | 0.4226 | 5 | 2 | 31 824 | full |
| 20 | 5 | 9 | 0.4500 | 0.250 | 0.5000 | 6 | 3 | 167 960 | full |
| 24 | 12 | 7 | 0.2917 | 0.500 | 0.29289 | 5 | 2 | 346 104 | full |
| 28 | 14 | 8 | 0.2857 | 0.500 | 0.29289 | 6 | 2 | 3.1·10⁶ | constructions only |
| 32 | 16 | 9 | 0.28125 | 0.500 | 0.29289 | 7 | 2 | 2.8·10⁷ | constructions only |
| 64 | 32 | 17 | 0.2656 | 0.500 | 0.29289 | 15 | 2 | 1.4·10¹⁵ | constructions only |
| 64 | 32 | 18 | 0.28125 | 0.500 | 0.29289 | 14 | 4 | 3.6·10¹⁵ | constructions only |

Field sizes used: `q ∈ {101, 1009, 10007, 2³¹−1}` (the reported maxima are at `q = 10007`;
no dependence on `q` was observed in the interior).

---

## 2. Exact-scan results (full window enumeration)

| n,k,e | max #Bad | P (distinct induced pairs) | max fibre F | max P·F | pairs with \|T\|=k | pairs with \|T\|>k | n² |
|---|---|---|---|---|---|---|---|
| 16,4,7 | 8 | 2 | 8 | 8 | 1 | 1 | 256 |
| 18,6,7 | 8 | 4 | 8 | 8 | 1 | 3 | 324 |
| 20,5,9 | 10 | 6 | 10 | 12 | 4 | 2 | 400 |
| 24,12,7 | 8 | 6 | 8 | 12 | 6 | 1 | 576 |

Random lines in the strict interior are almost always bad-set–free (the `c` conditions per
window are unsatisfiable generically); every large bad set found is *planted*, i.e. carries an
explicit codeword pair.

## 3. Verified constructions (no enumeration needed, valid at every field size)

The **core design** — pin `(f₀,f₁)` to a codeword pair on a core `T`, `|T| = t ≥ k`, and group
the remaining positions into blocks of `n−e−t` equal spurious values — realises fibre
`⌊(n−t)/(n−e−t)⌋`, maximal at `t = n−e−1`:

| n,k,e | best verified fibre | at \|T\| | e+1 |
|---|---|---|---|
| 16,4,7 | 8 | 8 | 8 |
| 18,6,7 | 8 | 10 | 8 |
| 20,5,9 | 10 | 10 | 10 |
| 24,12,7 | 8 | 16 | 8 |
| 28,14,8 | 9 | 19 | 9 |
| 32,16,9 | 10 | 22 | 10 |
| 64,32,17 | 18 | 46 | 18 |
| 64,32,18 | 19 | 45 | 19 |

So a **single pair attains fibre exactly `e+1` in every interior row up to `n = 64`**, and the
best multi-pair design found adds only `+1` (`(24,12,7)`: `P = 2`, cores `16` and `12`, total
`9 = e+2`).  No design produced a bad set of size `ω(n)`.

## 4. The rank cap on the residual (|T| = k) layer

Stacking `m` certified challenges gives `m·c` linear conditions inside the `2(n−k)`-dimensional
syndrome space.  Measured rank, over all interior rows and 8 random trials each:

```
rank( stacked system )  =  min( m·c , 2(n−k) )        in 100 % of trials,
```

both for *regular* window families (pairwise overlap ≤ k−1, i.e. no over-determined pair) and
for unrestricted ones.  Non-codeword — hence genuinely bad — solutions exist **iff**
`m·c < 2(n−k)`:

| n,k,e | c | 2(n−k) | ⌊2(n−k)/c⌋ | largest verified regular family |
|---|---|---|---|---|
| 16,4,7 | 5 | 24 | 4 | 4 (m = 3 regular windows realisable; m = 4 free) |
| 18,6,7 | 5 | 24 | 4 | 4 |
| 20,5,9 | 6 | 30 | 5 | 4 |
| 24,12,7 | 5 | 24 | 4 | 4 |
| 28,14,8 | 6 | 28 | 4 | 4 |
| 32,16,9 | 7 | 32 | 4 | 4 |
| 64,32,17 | 15 | 64 | 4 | 4 |
| 64,32,18 | 14 | 64 | 4 | 4 |

`2(n−k)/c = 2(1−ρ)/(1−δ−ρ)` is a **constant** at fixed rate and radius — 4.27 … 5.00 on every
row tested, with no growth in `n` from 16 to 64.  Independently, a family of windows of size
`n−e` pairwise meeting in ≤ k−1 positions is itself capped by the project's own set-family
Johnson bound `SetFamilyJohnson.card_family_le_of_pairwise_inter`, whose hypothesis
`(n−e)² > n(k−1)` is *exactly* `δ < 1 − √ρ`, the interior condition.

## 5. What the |T| = k pairs have in common

Every pair produced with common agreement exactly `k` satisfies, in all instances:

* it is the plain **interpolation pair**: `(q₀,q₁)` is determined by `(f₀,f₁)|T`, and carries no
  agreement certificate beyond interpolation;
* its bad challenges are exactly the values taken at least `c = n−e−k` times by the spurious
  value function `γ_x = −u₀(x)/u₁(x)` on `D∖T`, i.e. the **Welch–Berlekamp pencil `u₀ + γu₁`
  acquires `c` extra roots in `D`** — a `gcd`/subresultant degeneracy of the pencil, the object
  of `WelchBerlekampPencil.lean`, `GcdPencilEscape.lean`, `SubresultantCore.lean`;
* consequently its fibre is at most `⌊(n−k)/c⌋` (= 2 on the rate-1/2 interior rows), versus
  `e+1` for the large-`|T|` pairs;
* and the stacked conditions of distinct `|T| = k` challenges are linearly independent
  (measured full rank), so at most `⌊2(n−k)/c⌋` of them coexist.

---

## 6. Answers

```
TRUE UD–JOHNSON INTERIOR INSTANCES TESTED:
    (16,4,7) ρ=1/4 ; (18,6,7) ρ=1/3 ; (20,5,9) ρ=1/4 ;
    (24,12,7), (28,14,8), (32,16,9), (64,32,17), (64,32,18) ρ=1/2
    all with 2e ≥ n−k+2 and δ < 1−√ρ ; q ∈ {101, 1009, 10007, 2³¹−1}

MAX #BAD:              exact scans 8, 8, 10, 8 ; verified constructions e+1
                       (10 at n=32, 18 and 19 at n=64), best multi-pair design e+2.
                       No instance exceeded n; ratio #Bad/n² ≤ 0.031 everywhere.

DISTINCT PAIRS P:      ≤ 6 (max at (20,5,9) and (24,12,7)); constructions P = 1–2.

MAX FIBRE F:           e+1, attained by one pair with |T| = n−e−1 in every row up to n = 64.

P·F:                   ≤ 12 measured; the design budget
                       Σ_i [2(|T_i|−k) + F_i·(n−e−|T_i|)] ≤ 2(n−k)
                       caps it at Θ(e) = Θ(δn), i.e. Θ(n), not n².

COUNT WITH |T|=k:      1, 1, 4, 6 on the four fully-scanned rows.
COUNT WITH |T|>k:      1, 3, 2, 1 on the same rows.

COMMON ALGEBRAIC PROPERTY OF T=k PAIRS:
    pure interpolation pairs; their bad challenges are precisely the ≥ c-fold values of the
    spurious-value map γ_x = −u₀(x)/u₁(x), i.e. parameters at which the WB pencil u₀+γu₁
    acquires c extra roots in D (a subresultant/gcd degeneracy).  Fibre ≤ ⌊(n−k)/c⌋, and the
    stacked syndrome conditions of distinct T=k challenges are independent, capping their
    number by ⌊2(n−k)/c⌋ = 2(1−ρ)/(1−δ−ρ) = O(1).

SCALABLE HIGH-PAIR-COUNT EXAMPLE: NO.
    Neither random search, planted-window solving, core designs nor multi-core designs
    produced more than ⌊2(n−k)/c⌋ = 4 regular challenges or more than e+2 bad challenges in
    total, on any interior row from n = 16 to n = 64, at any field size tested.

CAN EXISTING PROJECT LEMMAS BOUND P·F < n^2.89:  UNKNOWN — one gap, and it is a small one.
    `MCAPairCover.card_badSet_le_pairCover` already *is* the composition:
        #Bad ≤ n·Λ(k,τ)² + n(n−e)/((n−e)² − n(τ−1)),   valid when n(τ−1) < (n−e)².
    At τ = k+1 the side condition is exactly δ < 1 − √ρ (the interior), and the second
    (residual) term is O(n) — already proved.  The first term uses the *list size* Λ(k,k+1),
    which is not polynomially bounded: what is needed is the count of pairs that actually
    explain a bad challenge, which the measurement puts at ≤ 6 (and the rank budget at O(1)).
    `AffineFactorSplit.card_badPairSet_le` already gives F ≤ n.

NEXT SINGLE LEMMA (regular-residual rank cap, |T| = k layer):
    Let γ₁,…,γ_m be distinct bad challenges with witness windows S₁,…,S_m of size n−e that
    pairwise meet in at most k positions (no over-determined codeword pair).  Then the stacked
    syndrome conditions are independent modulo codeword pairs, hence
        m · (n − e − k)  ≤  2 (n − k),      i.e.   m ≤ ⌊2(1−ρ)/(1−δ−ρ)⌋ = O(1).
    Combined with `card_badPairSet_le` (F ≤ n) and `card_family_le_of_pairwise_inter`
    (the Johnson set-family bound, available exactly on δ < 1−√ρ), this closes
        #Bad ≤ (#explaining pairs)·n + O(1)
    with the residual layer costing O(1) instead of a list size.
```

*Status of the measurement:* exact arithmetic, verified per challenge; the syndrome form was
cross-validated against brute-force witness enumeration.  It is evidence, not proof.

---

**UPDATE (falsification of §4 / the "NEXT SINGLE LEMMA" above).**  The regular-residual rank cap
`m·(n−e−k) ≤ 2(n−k)` is **false on the smooth (subgroup/coset) evaluation domain**: with windows
whose complements are unions of cosets of a subgroup `H ≤ D`, the stacked syndrome system splits
into `|H|` sectors and its rank drops below both `m·c` and `2(n−k)`.  Explicit FULL-MCA regular
counterexamples (all challenges verified bad against the definition of `IsBad`, strictly above
unique decoding and strictly below the Johnson radius) are recorded in
`REGULAR_RANK_CAP_KILL_REPORT.md`; the smallest is `n = 32, k = 15, e = 10, m = 5`
(`m·c = 35 > 34 = 2(n−k)`).  The excess over the cap was `+1` in every instance found, and the
mechanism is blocked when the symmetry order divides both `n−k` and `c` — which is the case at
`n = 2²⁰, k = 2¹⁹`, where the cap `m ≤ 4` survives.
