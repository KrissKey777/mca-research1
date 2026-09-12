# Grand MCA — subfield descent on the deployed KoalaBear row

**Verdict: `[ENTROPY-REDUCTION]` (structural reduction).**  A machine-checked theorem removes
an entire class of possible extremizers — every pencil that is rational over the base field
`F_p`, and more generally every pencil spanning a base-field-rational *plane* — from the whole
Johnson→capacity corridor of the deployed row, at *every* radius, with 27 bits of slack
against the exact challenge threshold `B*`.

Everything below is `sorry`-free, uses only `propext / Classical.choice / Quot.sound`, and is
stated against the project's own official `IsBad / badSet / epsMCA` predicate (γ-dependent
same support, closed threshold, same-support non-containment, challenge uniform over the whole
field).  Only the two new modules were compiled; no full project build was run.

New files:

* `RequestProject/Root/CodingTheory/SubfieldDescent.lean`
* `RequestProject/Root/CodingTheory/KoalaBearRowDescent.lean`
* `analysis/subfield_descent_check.py`, `analysis/challenge_image_entropy.py`

---

## 1. The theorem

**Descent lemma** (`Root.CodingTheory.isBad_fixed_of_ringHom`).  Let `σ` be a ring
endomorphism of the code field `F` which fixes every evaluation point of `D` and every value
of both words `f₀, f₁`.  Then every officially bad challenge `γ` satisfies `σ γ = γ`.

*Proof (three lines of algebra).*  Let `S` be the witness support and `P` the degree-`<k`
polynomial with `f₀ + γ f₁ = P` on `S`.  Apply `σ`: `f₀ + (σγ) f₁ = P^σ` on `S`.  Subtracting,
`(γ − σγ)·f₁ = P − P^σ` on `S`.  If `σγ ≠ γ` this exhibits `f₁` — and then also `f₀` — as
explained on the *same* support `S` by a degree-`<k` polynomial, i.e. exactly the correlated
agreement event that badness forbids. ∎

Consequences (all in `SubfieldDescent.lean`):

| statement | content |
|---|---|
| `badSet_subset_fixed`, `card_badSet_le_card_fixed` | the bad set lies in the fixed field of `σ` |
| `card_badSet_le_of_baseField_rational` | domain + pencil rational over `F_p` ⟹ `#Bad ≤ p` |
| `card_badSet_le_of_subfield_rational` | rational over `F_{p^t}` ⟹ `#Bad ≤ p^t` |
| `card_badSet_le_of_plane_baseField_rational` | the *plane* rational over `F_p` (arbitrary `F`-linear basis change) ⟹ `#Bad ≤ p+1` |
| `epsMCA_le_of_baseField_rational` | `ε_mca ≤ p / |F|` |
| `eval_fixed_of_coeffs_fixed` | polynomial pencils with `F_p`-coefficients are `F_p`-rational |

The bound is *sharp*: in the exact measurement of §4 base-field pencils attain exactly `q`
distinct challenges.

## 2. The deployed row

`KoalaBearRowDescent.lean` instantiates this at the row of the mission statement, with every
arithmetic fact checked inside Lean:

* `p = 2^31 − 2^24 + 1 = 2130706433` is proved prime; `p − 1 = 2^24·127`, hence `2^21 ∣ p − 1`;
* `F = F_{p^6} = GaloisField p 6`, `Fintype.card F = p^6` (a 186-bit field);
* `H = μ_{2^21}` is realised as `nthRootsFinset (2^21) 1`, of cardinality exactly `n = 2^21`,
  and `H ⊆ F_p` (every `2^21`-th root of unity satisfies `x^p = x`);
* `k = 2^20`, so `2k = |H|` — rate `1/2`;
* the exact Prize threshold `B* = ⌊|F| / 2^128⌋ = 274980728111395087` is verified
  (`prizeThreshold_eq`), `log₂ B* ≈ 57.932108`.

Then, for **every** radius `e` (hence for the whole discrete corridor
`e ≥ 614243` from finite Johnson `J ≈ 0.292893556` up to `δ_min = 1048577/2097152`) and every
pencil whose two words take values in `F_p`:

* `card_badSet_le_p` : `#Bad ≤ p = 2130706433 < 2^31`;
* `card_badSet_lt_prizeThreshold` : `#Bad < B*`, short by a factor `1.29·10^8` (≈ 27 bits);
* `epsMCA_lt_two_pow_neg_128` : `ε_mca ≤ p/|F| = p^{-5} < 2^{-154.94} ≪ 2^{-128}`;
* `plane_baseField_rational_safe` : the same for any pencil spanning a base-field-rational
  plane (`#Bad ≤ p+1`);
* `polynomial_pencil_safe` : in particular every polynomial pencil with base-field
  coefficients — every power pencil `x^a`, hence every coset-union / graded / `HalfGap`-type
  construction and every triangle-type one-hot pencil over `F_p`;
* `prizeBreaking_not_baseField_rational` : the contrapositive, i.e. the mandatory cheap
  rejection test of the mission's §D, now as a theorem;
* packaged as `koalaRow_baseField_rational_safe`.

For proper subfields the descent still bites, quantitatively:

* `prizeBreaking_quadratic_density` : an `F_{p^2}`-rational pencil that broke the threshold
  would need `#Bad ≤ p^2` **and** `#Bad > B*`, i.e. **more than `1/17` of the entire field
  `F_{p^2}`** would have to be bad (`B*/p^2 ≈ 0.0606`);
* `prizeBreaking_cubic_density` : an `F_{p^3}`-rational pencil would need a bad density
  `> 2^{-36}` inside `F_{p^3}`.

So on the deployed row the field of definition of the pencil must be `F_{p^2}` or larger, and
if it is `F_{p^2}` the construction must additionally be a 6 %-dense MCA failure of the *same
row over `F_{p^2}`*.

## 3. Prize-gain scoring (as required by §L)

* **SAFE gain.** Not a field-uniform SAFE endpoint for arbitrary pencils; instead a *class*
  SAFE result covering the entire interval `[0, δ_min]` — the whole Johnson→capacity corridor
  and beyond — for all base-field-rational pencils and planes.  Distance from Johnson: the
  result is uniform in `δ`, so unbounded on that scale; distance from capacity: likewise.
* **UNSAFE gain.** None claimed; the local certified upper endpoint of `δ*` is unchanged.
* **Challenge entropy.** The theorem is an exact challenge-image bound:
  `log₂ #Bad ≤ log₂ p = 30.99` for base-field data, against the required `log₂(B*+1) ≈ 57.93`
  — a deficit of `26.94` bits.  For `F_{p^2}` data the cap is `61.98` bits (not excluded by
  cardinality alone, hence the density gate above); for `F_{p^3}`, `92.97` bits.
* **Transfer.** The statement is about the official predicate at the deployed parameters, not
  a surrogate; nothing outside the corridor was used.

## 4. Cheap gates run before Lean (exact arithmetic, §K)

`analysis/subfield_descent_check.py` — brute-force over `F_{7^2}` with a 6-point rational
domain, `k = 3`, `e = 2`: 30 random base-field pencils, bad sets of size 5–7, **no** bad
challenge ever outside `F_7` (the predicate is evaluated literally, support by support).

`analysis/challenge_image_entropy.py` — a scaled analogue *inside the corridor*:
`q = 97`, `F = F_{q^2}`, `H = μ_16 ⊆ F_q`, `n = 16`, `k = 8` (rate 1/2), radius `e = 7`
(`δ = 0.4375`, above the finite Johnson radius `0.3386`, below `δ_min = 0.5625`).  Measured
challenge-image sizes:

| pencil | #distinct official γ | outside `F_q` |
|---|---|---|
| random base-field words | 97 (`= q`, five trials) | 0 |
| power pencils `x^9,x^8`, `x^10,x^8`, `x^12,x^9` | 97 | 0 |
| random degree-`≤ k+2` pencils with coefficients in `F_{q^2}` | ≈ 5820 of 9409 | ≈ 5760 |

Two readings.  (i) The descent cap is *tight*: base-field mechanisms saturate at exactly `q`.
(ii) The escape route is exactly the one the algebra predicts (see §5): extension-field
coefficients at degree `≥ k+2`.

## 5. Where a Prize counterexample must now live (analysis, not verified)

Write the support-to-challenge map explicitly.  For a support `S` with `|S| = k+1` the
"explained on `S`" condition is a single syndrome functional and

    γ_S = −⟨λ^S, f₀⟩ / ⟨λ^S, f₁⟩ ,

with `λ^S` rational over the base field because `H ⊆ F_p`.  In the `d`-sparse/coset picture
(support = union of `j` cosets of `μ_d`, reduced coordinate `y = x^d`, `m = n/d`, `k' = m/2`)
the reduction mod `Z_T` makes the condition depend on the support only through elementary
symmetric functions `E₁(T), E₂(T), … ∈ F_p`:

* pencils of `y`-degree `≤ j` give `γ = Möbius(E₁)` — a function of **one** `F_p`-coordinate,
  so at most `p ≈ 2^31` challenges *whatever the coefficient field is*.  This is why the
  existing coset/`HalfGap`/power-pencil family is dead on the deployed row, and it is a
  strictly stronger obstruction than base-field rationality alone;
* `y`-degree `j+1` makes the single condition depend on `E₁` and `E₁²−E₂`, so
  `γ = −(a + bE₁ + cE₂')/(a' + b'E₁ + c'E₂')`; if `(b,c)` and `(b',c')` are `F_p`-independent
  in `F_{p^6}` the fibres are cut out by 6 `F_p`-linear equations in 2 unknowns and the map is
  essentially injective, allowing up to `p² ≈ 2^62 > B*` challenges.

So the correct research coordinate is confirmed to be the *number of independent `F_p`
coordinates of the support data that the challenge map sees*: one coordinate caps at `2^31`
(dead), two at `2^62` (live).  At `m = 64` cosets this mechanism sits at
`δ = 1/2 − 1/m = 31/64 = 0.484375`, which is inside the corridor but **above** the externally
reported `0.467826843`, and certifying it would require a lower bound of `≈ 2^58` on the
number of distinct pairs `(E₁(T), E₂(T))` over the `C(64,33)` admissible supports — a genuine
counting problem that is not attempted here.

## 6. Audit note on the external OrbitPencil evidence

The files `ProximityPrize/Audit/ScalarOrbitPencilLift.lean` and
`MCA_SCALAR_ORBIT_PENCIL_LIFT.md` are **not** present in this tree, so nothing about them is
replayed or asserted here.  The descent theorem does, however, provide a sharp and cheap audit
gate for such a claim, which we state conditionally and without prejudice:

> On this row, `#Bad ≥ 2^59 + 1` is **impossible** for any pencil whose two words are
> base-field (`F_p`) valued, and impossible for any pencil spanning a base-field-rational
> plane, at *any* radius, because `#Bad ≤ p + 1 < 2^31 + 1`.  It is also impossible for
> `F_{p^2}`-valued words unless more than `1/17` of `F_{p^2}` is bad — note `2^59+1 > p^2/8`,
> so a `2^59`-size bad set inside `F_{p^2}` would mean over 12 % of that subfield is bad.

Hence, if the reported construction is "scalar" in the sense of base-field data, the first
exact gate to re-check is precisely the challenge-image step: either the words are not
base-field rational, or the reported count is not a count of *distinct official challenges*.
If instead the construction genuinely produces `2^59` distinct challenges, then by the theorem
its pencil must generate at least `F_{p^2}` over `F_p` — a concrete, checkable structural
prediction about it.

## 7. What is *not* claimed

* No new UNSAFE point, and no improvement of the reported `δ ≈ 0.467826843` upper endpoint.
* No SAFE bound for arbitrary (extension-generating) pencils above Johnson; that question is
  untouched and remains the open core of Grand MCA.
* No comparison with any printed definition: no external document is available in this
  environment, so what is certified is the project's own `IsBad/epsMCA`.
