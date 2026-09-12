# Closing the irreducible-carrier branch, and what it is worth

This note records (i) the shortest bridge that closes the last branch of the carrier
dichotomy, (ii) a quantitative improvement to the carrier architecture itself, and (iii) the
honest accounting of what the whole route can and cannot buy — in particular why it cannot
approach the deployed parameter point.  Every claim marked **[Lean]** is machine-checked,
`sorry`-free, and axiom-audited in `RequestProject/Main.lean`
(`propext`, `Classical.choice`, `Quot.sound` only).  Everything else is explicitly labelled
analysis.

---

## 1.  The state before this note

`CarrierDichotomy.card_badSet_le_or_exists_degenerate_irreducible` reduces the whole
Guruswami–Sudan chain over `F[Z]`, for a line with a far centre, to a single branch:

> some **irreducible** factor `W` of the interpolant `Q`, of **positive `Y`-degree**, is
> *degenerate along the formal line*: `|D| ≤ |lineSupport W| + e + 1`, where
> `lineSupport W = { x ∈ D : W(Z, x, f₀x + Z·f₁x) ≡ 0 }`.

The instruction was: do **not** grind this out one `Y`-degree at a time; reuse the published
BCHKS / BCI+20 treatment of the same branch, whose *conclusion* is that a "useful" irreducible
factor has the affine shape `R(X,Y,Z) = Y − v₀(X) − Z·v₁(X)`.

## 2.  The shortest bridge, and why it is short  **[Lean]**

`RequestProject/Root/CodingTheory/AffineCarrier.lean` (≈ 200 lines).

The decisive observation is that in the *formal-line* setting the output side of the BCHKS
mechanism is almost free, because **degeneracy of an affine carrier is literally correlated
agreement**.  Writing `W = c·(Y − v₀(X) − Z·v₁(X))` with `c ≠ 0`, the line residual at a
position `x` is

```
W(Z, x, f₀x + Z·f₁x) = c · ( (f₀x − v₀(x)) + (f₁x − v₁(x))·Z ),
```

a *linear* polynomial in `Z` whose two coefficients are the two discrepancies.  Hence

* `mem_lineSupport_iff_of_affineCarrier` — `x ∈ lineSupport W ↔ f₀x = v₀(x) ∧ f₁x = v₁(x)`;
* `isFormalRoot_of_affineCarrier` — so `p = v₀ + Z·v₁` is a `FormalRoot` of the line on
  `lineSupport W`, of `Z`-degree `≤ 1`, with codeword coefficients;
* `lineCloseOn_of_affineCarrier`, `correlatedAgreement_of_degenerate_affineCarrier` — so the
  existing `FormalRoot` machinery converts a *degenerate* affine carrier into correlated
  agreement of the whole line at radius `e + 1`;
* `not_degenerate_of_affineCarrier_of_far` — and therefore, if the centre is at distance
  `> e + 1` from the code, an affine carrier **cannot** be degenerate;
* `card_badSet_le_of_affine_carriers` — the branch is closed: under
  `e + 1 < d(f₀, RS[D,k])` and the hypothesis that every degenerate irreducible carrier is
  affine, `#Bad ≤ dZ + L·|D|·(dZ + L)`.

No Hensel lifting, no power series, no specialisation point `x₀`, no `Y`-degree case analysis.
The published Hensel-lifting step enters as the single explicit hypothesis `haffine` — it is
**not** reproved here, and nothing in the repository asserts it.

## 3.  A quantitative improvement inside the architecture  **[Lean]**

`RequestProject/Root/CodingTheory/CarrierBudget.lean`.

The old counting step charged the *global* degree budget `|D|·(dZ + L)` **once per irreducible
factor**, and there can be `L = deg_Y Q` of them; that is a genuine `Y`-degree loss.  Degrees
are additive over a factorisation, so the correct total charge is

```
Σ_W ( deg_Z W + deg_Y W )  =  deg_Z Q + deg_Y Q  =  dZ + L .
```

Formalised as: `zDeg` (total `Z`-degree, via the isomorphism `F[Z][X][Y] ≅ F[X][Y][Z]` built
from Mathlib's `Polynomial.Bivariate.swap` and the project's `swapZX`), `zDegLe_iff` (it agrees
with the project's coefficientwise `GS.ZdegLe`), `zDeg_multiset_prod` (additivity),
`card_le_of_factorisation_budget` (the counting step with a per-factor budget), and

| bound on the close/bad set | source |
|---|---|
| `dZ + L·(\|D\|·(dZ + L))` | `CarrierDichotomy.card_le_or_exists_degenerate_irreducible` (previous) |
| **`dZ + \|D\|·(dZ + L)`** | `CarrierBudget.card_le_or_exists_degenerate_irreducible_sharp` (new) |

— an improvement by a factor of about `L = deg_Y Q`, i.e. by about `1/η` for the usual
Guruswami–Sudan schedule with `η` the gap to the Johnson radius.  The closed form of the branch
inherits it: `CarrierBudget.card_badSet_le_of_affine_carriers_sharp` gives
`#Bad ≤ dZ + |D|·(dZ + L)`.

## 4.  What is still missing for an unconditional theorem (analysis)

Two inputs, both outside this note:

1. **The BCHKS affine-root step** (`haffine`).  Published; not reproved here.
2. **Existence of the formal-line interpolant.**  The repository has *no* theorem producing a
   `Q ∈ F[Z][X][Y]` that every close challenge's witness annihilates, together with explicit
   budgets `(L, dZ)`.  Guruswami–Sudan interpolation over the field `F(Z)` gives `Q` with
   `L = Θ(1/η)`, but the `Z`-degree `dZ` — the degree in the *challenge* variable after
   clearing denominators — is exactly the quantity that a Cramer-type construction does not
   control cheaply.

Consequently the carrier route currently yields **no number at all**: its leading term is
`|D|·(dZ + L)`, and `dZ` is unestablished.  To beat the published strong/list-correlated-
agreement bound of order `n/η⁵` one would need `dZ + L = o(η⁻⁵)`; with `L = Θ(1/η)` this is
entirely a question about `dZ`.  **No improvement over the published quantitative theorem is
claimed here.**

## 5.  Prize accounting (analysis, consistent with `KOALAIRS12_PRIZE_GAP_AUDIT.md`)

At the audited parameter shape the MCA *constant* is worth `0.000000` bits: every bound in the
repository is between `2¹³` and `2³²` while the query term is `2⁻⁶⁷`, so the sum is unchanged to
more than 30 decimal places.  Only the **radius** reaches the score.  The carrier route lives
strictly inside the Johnson regime; therefore, even completed, it moves the score by `0` bits.
This is the reason the improvement of §3 is reported as an architectural sharpening and not as
a prize-relevant gain.

## 6.  The deployed target is out of reach of this whole family  **[Lean]**

`RequestProject/Root/CodingTheory/DeployedTargetGap.lean` pins the deployed point
`ρ = 1/2`, `δ = 0.46782684`:

* `deployedRadius_lt_capacity`, `deployedRadius_capacity_gap` — it is inside capacity, with
  capacity gap `1 − ρ − δ = 0.03217316`;
* `deployedRadius_beyond_johnson` — `(1 − δ)² < ρ`, i.e. `δ > 1 − √ρ = 0.29289…`;
* `johnson_slack` — the Johnson inequality fails by a factor `> 1.76`, not by a constant that a
  sharper argument could absorb;
* `gs_condition_fails` — in the project's own Guruswami–Sudan condition `k·n·(m+1) < m·t²`
  (used by `GS.exists_interpolating_of_johnson` and `GS.gs_list_bound`), at rate `≥ 1/2` and
  agreement `t ≤ 0.53217316·n`, the inequality is false **for every multiplicity `m` and every
  block length `n`**.

So the failure is structural: no multiplicity schedule, no constant-factor sharpening, and no
fixed-step shortening of the kind used in the Johnson regime reaches that row.

## 7.  The next obstruction, stated as concretely as we can (analysis)

Beyond Johnson at constant rate the only lever left is the *domain*.  The deployed domain is
smooth: a coset of a `2`-power multiplicative subgroup.  Two facts already in the repository
frame the problem exactly:

* `FarCenterProximity.badSet_eq_goodZ_of_far` — for a far centre, `#Bad` **is** the number of
  close challenges, so an MCA bound at radius `δ` is a proximity-gap bound at radius `δ`;
* `IndicatorLineList` / `DirectionListReduction` — the close-challenge count of a line and the
  Reed–Solomon *list size* at radius `δ` sandwich each other.

Therefore a beyond-Johnson MCA bound at `(ρ, δ) = (1/2, 0.46782684)` implies a polynomial
list-size bound for the *explicit* Reed–Solomon code of rate `1/2` on a smooth domain at
relative radius `0.4678` — which is not known for any explicit RS code (the known
capacity-approaching list-size results are for random or "most" RS codes, and over large
alphabets).  That is the obstruction, and it is not an artefact of our architecture.

The one smooth-domain-specific asset that no Johnson-type argument uses is the `ℤ/n`-symmetry
of the evaluation domain: `σ : x ↦ ωx` preserves both the domain and the code, so it acts on
instances, carrying the list of `f` bijectively onto the list of `f ∘ σ`.  This is an
equivariance of the problem, **not** a bound — it becomes one only on the `σ`-invariant locus.
The concrete next questions it suggests, in increasing order of value, are: (a) does the
equivariant reduction (quotient by `ℤ/n`) change the extremal instance, i.e. is the worst line
for `#Bad` at rate `1/2` `σ`-invariant?  (b) on the `σ`-invariant locus, where the list *is* a
union of orbits, does the orbit count admit a bound past Johnson?  (c) is there a
smooth-domain analogue of the subspace-pencil family — the repository's only superpolynomial
`#Bad` construction, which lives on an `F_p`-subspace domain and therefore does not transfer to
a multiplicative subgroup?  A positive answer to (c) would settle the deployed row negatively
and is the cheapest of the three to attack numerically.  Nothing in the repository asserts any
of these.  Nothing in the repository asserts either direction.
