# Split-locator gate — audit and first quantitative attempt

**PRIMARY STATUS: `SPLIT_LOCATOR_QUANTITATIVE_OBSTRUCTION`**

Secondary statuses established on the way:

* Phase 1: `LOCATOR_BRIDGE_PROVED`
* Phase 2: official adapter proved in **both** directions (the gate is an *equality*, not a
  relaxation)
* Phase 3: `SPLIT_LOCATOR_BOUND_PROVED` is **not** claimed; the first exact obstruction of Route A
  and the first exact obstruction of Route C are proved, Route B is only anchored.

Everything below is machine-checked in Lean 4 / Mathlib, with no `sorry`, no `admit`, no
`native_decide` and no new axioms.  All 42 load-bearing declarations were audited with
`#print axioms` (`RequestProject/SplitLocatorGateAxiomAudit.lean`); each depends only on
`propext`, `Classical.choice`, `Quot.sound` (one purely finite check uses `propext`, `Quot.sound`
only).

New modules (all additive; no existing declaration, the toolchain, the lakefile or the manifest
was modified):

| module | content |
|---|---|
| `RequestProject/Root/CodingTheory/LocatorOrientation.lean` | Phase 1, algebraic half |
| `RequestProject/Root/CodingTheory/LocatorSyndromeBridge.lean` | Phase 1, syndrome half |
| `RequestProject/Root/CodingTheory/SplitLocatorOfficialAdapter.lean` | Phase 2, converse adapter |
| `RequestProject/Root/CodingTheory/SplitLocatorChallengeCount.lean` | Phase 3 |
| `RequestProject/SplitLocatorGateAxiomAudit.lean` | `#print axioms` audit |

---

## 0. Deployed parameters

```
p  = 2^31 − 2^24 + 1 = 2130706433      F = 𝔽_{p^6}          |F| = p^6
n  = |D| = 2^21 = 2097152              k  = 2^20 = 1048576
r  = n − k = 1048576                   e  = 978944
t  = n − e = 1118208                   w  = r − e = 69632
B* = 274980728111395087
```

Machine-checked numerical facts (`SplitLocatorChallengeCount.lean`):

```
deployed_target_eq_field_over_two_pow_128 :
    B* · 2^128 ≤ 2130706433^6  ∧  2130706433^6 < B* · 2^128 + 2^128
```

so `B* = ⌊|F| · 2^{−128}⌋` exactly: the trivial bound `#badSet ≤ |F|`
(`card_badSet_le_card_field`) misses the target by exactly the factor `2^128`.

```
deployed_wcube_value    : w^3      = 337618789203968       (< B*)
deployed_n_wsq_value    : n·w^2    = 10168283533672448     (< B*)
deployed_nsq_w_value    : n^2·w    = 306244774661193728    (> B*)
deployed_wcube_lt_target, deployed_n_wsq_lt_target, deployed_nsq_w_gt_target
```

A generic `n²·w` bound is therefore **not** sufficient; `w³` and `n·w²` would be.

---

## 1. PHASE 1 — locator-orientation audit: `LOCATOR_BRIDGE_PROVED`

### 1.1 Conventions (never identified)

For `E ⊆ D` (viewed through the evaluation family `dval D : ↥D → F`, `a ↦ a`):

* **monic split locator** `Q_E(X) = ∏_{x∈E} (X − x)`  — `ErasureSpan.qPoly (dval D) E`;
* **reciprocal locator** `Λ_E(X) = ∏_{x∈E} (1 − x·X)` — `LocatorOrientation.lamPoly (dval D) E`.

They are different polynomials; the explicit witness that they may not be substituted for one
another is proved:

```
qPoly_ne_lamPoly_example : qPoly (fun _ => (2:ℚ)) {0} ≠ lamPoly (fun _ => (2:ℚ)) {0}
```

### 1.2 The exact conversion

```
reverse_qPoly              : (qPoly v A).reverse = lamPoly v A
reverse_lamPoly            : (∀ i ∈ A, v i ≠ 0) → (lamPoly v A).reverse = qPoly v A
lamPoly_eval_of_ne_zero    : y ≠ 0 → (lamPoly v A).eval y = y^{|A|} · (qPoly v A).eval y⁻¹
lamPoly_coeff_of_le        : i ≤ |A| → (lamPoly v A).coeff i = (qPoly v A).coeff (|A| − i)
lamPoly_coeff_of_gt        : |A| < i → (lamPoly v A).coeff i = 0
```

so `Λ_E(X) = X^e·Q_E(1/X)` holds in the coefficient form, in the evaluation form, and as the
`reverse` operation of Mathlib.  Reversal is an involution here **exactly** when no evaluation
point is `0`, which is automatic for `D = μ_n`.

### 1.3 The remaining audit items

1. **reversal identity** — `reverse_qPoly`, above. ✔
2. **scalar factors** — none: both products are taken with the normalisations shown; `Λ_E(0) = 1`
   (`lamPoly_coeff_zero`), `Q_E` is monic (`ErasureSpan.qPoly_monic`).  The audit also records a
   *negative* result on a different convention, see item 8 below. ✔
3. **degree bounds** — `deg Q_E = e` exactly (`qPoly_natDegree`); `deg Λ_E ≤ e` always
   (`lamPoly_natDegree_le`) with equality iff no point is `0` (`lamPoly_natDegree_eq`); the top
   coefficient is `Q_E(0) = ∏(−x)` (`lamPoly_coeff_card`). ✔
4. **modulus** — `keyCongruence_iff_exists_remainder`: the coefficient form
   `∀ j, e ≤ j < r → (Λ·S).coeff j = 0` is equivalent to `∃ Ω, deg Ω < e ∧ X^r ∣ (Λ·S − Ω)`. ✔
5. **monicity** — `Q_E` monic, `Λ_E` normalised at `0` and never monic unless the top coefficient
   happens to be `1`; the two normalisations are recorded separately. ✔
6. **roots and nonzero evaluation points** — `lamPoly_isRoot_iff`: the roots of `Λ_E` are exactly
   the inverses `x⁻¹`, `x ∈ E`, `x ≠ 0`; `lamPoly_eval_zero : Λ_E(0) = 1`, so `0` is never a root
   of `Λ_E` while it is a root of `Q_E` as soon as `0 ∈ E`. ✔
7. **exact relation to `s ∈ V_E`** — in the repository the membership `f ∈ V_E` (i.e.
   `MaxErasure.vSpace k E`, proved equal to closeness on `Eᶜ` by `MaxErasure.mem_vSpace_iff`) is
   handled through the *functional* form, and the bridge to the classical congruence is
   `locatorSystem_iff_keyCongruence` below.  ✔
8. **exact relation to official `IsBad`** — Phase 2. ✔

### 1.4 The syndrome bridge

With `s_j = gsynd f (X^j) = ∑_{a∈D} f a · λ_a · a^j` (`synCoeff`) and
`S(X) = ∑_{j<r} s_j X^j` (`synPoly f r`):

```
coeff_lamPoly_mul_synPoly :
  |E| + d < r →
  (lamPoly (dval D) E * synPoly f r).coeff (|E| + d) = gsynd f (qPoly (dval D) E * X^d)
```

and therefore, for `r = |E| + w`, both directions:

```
locatorSystem_iff_keyCongruence :
  LocatorSystem w f₀ f₁ γ (qPoly (dval D) E)
    ↔ KeyCongruence r |E| (lamPoly (dval D) E) (synPoly (lineComb f₀ f₁ γ) r)
```

i.e. the `w = r − e` repository equations *are* the vanishing of the coefficients `e,…,r−1` of
`Λ_E·S_γ`, that is `Λ_E·S_γ ≡ Ω (mod X^r)`, `deg Ω < e`, in the classical orientation.  The
syndrome polynomial is affine in the challenge, `S_γ = S_{f₀} + γ·S_{f₁}`
(`synPoly_lineComb`).

**Warning proved, not asserted (convention item 2).**  The parity-check window used here is the
GRS window: exponents `0,…,r−1` weighted by the fixed multiplier `λ_a`, whose correctness is
proved from `MaxErasure.sum_lam_eval_eq_zero`.  It may **not** be replaced by the naive "RS
column" window `v_x = (x^k,…,x^{n−1})` when the domain is a group of roots of unity:

```
column_convention_not_parity_check : ∑_{x ∈ {1,2,3,4} ⊂ ZMod 5} x · x^3 = 4 ≠ 0
```

(`D = μ₄ ⊂ ZMod 5`, `k = 2`, codeword `x ↦ x ∈ RS_2(D)`, row `x ↦ x^{n−1}`).  Anyone importing the
`x^{k+j}` convention into a `μ_n` domain changes the object; this repository's statements are
stated exclusively in the `λ`-weighted convention.

### 1.5 Splitness

```
qPoly_dvd_X_pow_sub_one :
  0 < n → Set.InjOn v A → (∀ i ∈ A, (v i)^n = 1) → qPoly v A ∣ X^n − 1
```

so for `E ⊆ D = μ_n` the monic split locator divides `X^n − 1`, as required.

---

## 2. PHASE 2 — the official adapter, replayed in both directions

Official objects: `Root.CodingTheory.IsBad k e f₀ f₁ γ` and `badSet k e f₀ f₁` of `MCA.lean`
(unchanged).  Gate object: `GlobalAnnihilator.locatorChallengeSet k e f₀ f₁`, i.e. the set of
`γ ∈ F` for which there exists `E ⊆ D` with `|E| = e`, `LocatorSystem (n−k−e) f₀ f₁ γ Q_E` and
`LocatorNondeg (n−k−e) f₁ Q_E`.

**Direction A** (already in the repository, replayed and re-audited):
`badSet_subset_locatorChallengeSet` — every officially bad `γ` has an erasure of size *exactly*
`e` whose monic locator satisfies the system, with the projective normalisation
`gsynd f₁ (Q_E·h) = 1`, `gsynd f₀ (Q_E·h) = −γ`.

**Direction B** (new, this session):

```
isCloseOn_of_locatorSystem :
  k ≤ n → |E| ≤ n − k →
  LocatorSystem (n−k−|E|) f₀ f₁ γ Q_E → IsCloseOn k Eᶜ (lineComb f₀ f₁ γ)

not_lineCloseOn_of_locatorNondeg :
  k + |E| + (n−k−|E|) ≤ n →
  LocatorNondeg (n−k−|E|) f₁ Q_E → ¬ LineCloseOn k Eᶜ f₀ f₁

isBad_of_split_locator :
  k ≤ n → e ≤ n − k → |E| = e →
  LocatorSystem (n−k−e) f₀ f₁ γ Q_E → LocatorNondeg (n−k−e) f₁ Q_E → IsBad k e f₀ f₁ γ
```

Proof of the first: `W_E = Ψ(Q_E·F[X]_{<w})` (`MaxErasure.wSpace_eq_wModel`) plus biduality
(`mem_vSpace_iff_pairing`) — the locator equations are exactly the vanishing of the ambient
pairing of `f₀+γf₁` against the generators of `W_E`.  Proof of the second: if the line were close
on `Eᶜ` then `f₁` would be, and `gsynd_locator_eq_zero` would force `gsynd f₁ (Q_E·h) = 0` for all
`deg h < w`.

**Consequence (both directions):**

```
badSet_eq_locatorChallengeSet :
  k ≤ n → e < n − k → e < n → 1 ≤ n − k − e →
  ↑(badSet k e f₀ f₁) = locatorChallengeSet k e f₀ f₁

card_badSet_eq_ncard_locatorChallengeSet : (badSet k e f₀ f₁).card = (locatorChallengeSet …).ncard

deployed_gate_iff (|D| = 2097152) :
  (badSet 1048576 978944 f₀ f₁).card ≤ B* ↔ (locatorChallengeSet 1048576 978944 f₀ f₁).ncard ≤ B*
```

Checked conventions: support/erasure complement (`Eᶜ`, size exactly `n − e`); `|E| = e` exactly
(both directions, using `isBad_iff_exists_exact_erasure` in direction A);
`Q_E` monic of degree `e`; `Q_E ∣ X^n − 1` for `E ⊆ μ_n`; only **finite** `γ ∈ F` occurs on both
sides (no projective point at infinity is in either set), and `γ = 0` is admitted on both sides;
the pencil is the rank-≤2 received pencil `f₀ + γ f₁` of `MCA.lean`, unchanged; the
noncontainment is the same-support noncontainment `¬ LineCloseOn k Eᶜ f₀ f₁`; the only
normalisation used in direction A is the projective label, which is not needed in direction B.

**Adapter status: proved equivalent.**  The split-locator gate is not a relaxation — it is the
official statement.  In particular no counting route may gain anything by passing to locators, and
conversely a proof of `|G| ≤ B*` closes the deployed Grand-MCA row.

---

## 3. PHASE 3 — the quantitative gate: first attempt and obstructions

Object (`G` of the mission statement, now known to equal `badSet`):

```
G(f₀,f₁) = { γ ∈ F : ∃ E, |E| = e, (A + γB) Q_E = 0, Q_E nondegenerate }
```

with `A Q = (gsynd f₀ (Q·X^d))_{d<w}` and `B Q = (gsynd f₁ (Q·X^d))_{d<w}`.

### 3.1 γ versus locators versus supports

```
challenge_unique_of_split_locator : one support E carries at most one finite challenge
card_badSet_le_card_powersetCard  : |G| ≤ #{E ⊆ D : |E| = e} = C(n,e)
```

The map `γ ↦ E_γ` is injective, so counting supports bounds the number of challenges — but the
converse fails: several locators (several supports) may give the *same* `γ`, so counting locators
is **not** the same as counting challenges.  At the deployed row `C(2097152, 978944)` is
astronomically larger than `B*`; this bound is recorded for completeness only, not as progress.

### 3.2 Route A (two-challenge comparison) — first exact obstruction, proved

```
lineCloseOn_inter_of_two_challenges :
  γ ≠ δ → IsCloseOn k S (lineComb f₀ f₁ γ) → IsCloseOn k T (lineComb f₀ f₁ δ) →
  LineCloseOn k (S ∩ T) f₀ f₁

card_compl_inter_compl_ge : |E| = |E'| = e → n − 2e ≤ |Eᶜ ∩ E'ᶜ|
```

so two distinct bad challenges force the whole line to be close on a window of size at least
`n − 2e`.  The exact obstruction is that this conclusion is *vacuous* below the code dimension:

```
isCloseOn_of_card_le_dim  : |S| ≤ k → IsCloseOn k S f       (Lagrange interpolation)
lineCloseOn_of_card_le_dim: |S| ≤ k → LineCloseOn k S f₀ f₁  (for every pair, bad or not)
```

Deployed evaluation:

```
deployed_two_challenge_window      : n − 2e = 139264 = 2w
deployed_window_below_dimension    : 139264 < 1048576 = k
deployed_two_challenge_guarantee   : 139264 ≤ |Eᶜ ∩ E'ᶜ| ∧ 139264 ≤ 1048576
deployed_pairwise_regime_fails     : ¬ (2e ≤ n − k)          (1957888 > 1048576)
deployed_unique_decoding_regime_fails : ¬ (3e < n − k + 1)   (2936832 > 1048576)
```

Route A therefore stops: at the deployed radius the pairwise comparison produces only a window of
guaranteed size `2w = 139264`, far below the code dimension `k`, on which *every* pair of words is
line-close; no relation between `γ` and `δ` can be extracted.  Nothing about disjointness,
sunflower structure, bounded coordinate multiplicity or cumulative rank growth is inferred.

### 3.3 Route B (minimum-weight RS geometry) — anchored only

```
card_nonzero_eval_qPoly : #{a ∈ D : Q_E(a) ≠ 0} = n − |E|
```

so the evaluation vector of a split locator of degree `e` is a word of `RS_{e+1}(D)` of weight
exactly `n − e`, i.e. a minimum-weight word of that MDS code — the exact object Route B needs, with
the exact parameters checked.  No theorem bounding the number of *challenges* `γ` whose kernel
`ker(A+γB)` contains such a word is claimed, and none is proved here; external incidence,
Grassmannian or Chow-form statements were not imported.

### 3.4 Route C (root-set algebra) — first exact obstruction, proved

```
span_splitLocators_eq_degreeLT :
  e + 1 ≤ n → span_F { Q_E : |E| = e } = F[X]_{<e+1}
deployed_splitLocators_span    : the deployed instance (e + 1 = 978945 ≤ 2097152)
linear_functional_vanishing_on_splitLocators :
  (∀ E, |E| = e → φ(Q_E) = 0) → ∀ p ∈ F[X]_{<e+1}, φ(p) = 0
```

The split locators **span** the whole locator space.  Hence the splitting constraint is invisible
to every linear functional on that space: no dimension count, no linear elimination on the locator
system can separate split from non-split locators.  In particular this re-derives, from the
opposite side, why the unconstrained-annihilator route is empty, and it fixes the requirement for
Route C: only a genuinely nonlinear consequence of splitness (elimination with `Q ∣ X^n − 1`,
resultants in `γ − δ`, symmetric-function identities) can produce a bound.  Such a nonlinear
elimination was **not** carried out.

### 3.5 Numerical acceptance test

The only universal bounds proved for `|G|` in this session are `|G| ≤ |F|`
(`card_badSet_le_card_field`) and `|G| ≤ C(n,e)`.  Both exceed `B*`.  No bound of the admissible
scales `w³` or `n·w²` is proved.

---

## 4. The one and only smallest remaining implication

```
deployed_remaining_implication (|D| = 2097152) :
  (locatorChallengeSet 1048576 978944 f₀ f₁).ncard ≤ 274980728111395087
  → (badSet 1048576 978944 f₀ f₁).card ≤ 274980728111395087
```

Equivalently, by `deployed_gate_iff`, the remaining obligation is exactly:

> for every official pair `(f₀,f₁)` on `D = μ_{2^21} ⊂ 𝔽_{p^6}`, the number of **distinct finite
> challenges** `γ` admitting a monic degree-`978944` locator split over `D`, annihilated by
> `A + γB`, and nondegenerate for `f₁`, is at most `B* = 274980728111395087`.

Since Phase 2 proves the gate is an equality, this implication is not a weakening: it *is* the
deployed Grand-MCA row.

## 5. What was deliberately not reopened

The unconstrained annihilator (accepted as a candidate result; no error found in its dimension
argument, and Route C above independently explains why it cannot bite), pivot-depth descent,
support partitions / residual-ledger conservation, generic Johnson / sunflower / second-moment
bounds, local matroid rank accumulation, the separate `m = 8` differential-trade branch, and all
unreplayed external reports.  No finite computation from the construction side is used in any
statement above.
