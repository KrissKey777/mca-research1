# Constant-gap MCA: audit of the subspace pencil, and an exact reduction to proximity gaps

**New Lean files** (all build, no `sorry`, axioms `propext, Classical.choice, Quot.sound` only):

| file | content |
|---|---|
| `RequestProject/Root/CodingTheory/SubspacePencilAudit.lean` | the required first audit, as certified arithmetic |
| `RequestProject/Root/CodingTheory/FarCenterProximity.lean` | `badSet = goodZ` for far-centred lines; the exact reduction; far centres from high-degree polynomials |
| `RequestProject/Root/CodingTheory/NearDirectionBadSet.lean` | the single-challenge bound `#Bad ≤ d(f₁,C)·|list(f₀, e+d(f₁,C))|`, its Johnson corollary, and the ceiling comparison |
| `RequestProject/Root/CodingTheory/SubspacePencilProximity.lean` | the pencil read as a proximity-gap counterexample |

Documentation corrected: title and §§0, 3 of `SUBSPACE_PENCIL_REPORT.md`, and the docstring of
`exists_superpolynomial_badSet_of_small_relative_gap`.

Notation: `n = |D|`, `k` = dimension, `e` = radius, `c = n − k − e` = absolute capacity gap,
`η = c/n`, `ρ = k/n`, `δ = e/n`, `s = ρ + η = 1 − δ`, `C = RS[D,k]`,
`#Bad = (badSet k e f₀ f₁).card`, `goodZ k e f₀ f₁ = {γ : d(f₀ + γf₁, C) ≤ e}`.

---

## 1. Corrected interpretation of the subspace-pencil result

The Lean statement `exists_superpolynomial_badSet_of_small_relative_gap` is exactly **(A)**:

> for all `d, M` there is `N` such that over any field of characteristic `p` with `> p^N`
> elements there is a parameter point with `η ≤ 1/M` and `#Bad > n^d`.

**(B)** — every `η = o(1)` regime gives a superpolynomial bad set — is *not* justified, and is
in fact false *as a statement about this family*. Four certified facts delimit it
(`SubspacePencilAudit.lean`):

1. `subspacePencil_bound_le_pow_card`: `p^{ℓ(m−ℓ)} ≤ n^{m−ℓ}`. Since `η ≈ p^{ℓ−m}`, the family's
   guarantee never exceeds `n^{log_p(1/η)}`; at any **fixed** `η` it is polynomial.
2. `subspacePencil_superpoly_forces_gap`: `n^d < p^{ℓ(m−ℓ)}` forces `m − ℓ > d`. Beating a
   larger polynomial requires a smaller gap; no single gap value works for all `d`. This is the
   precise separation of (A) from (B).
   `subspacePencil_gap_lt_of_superpoly` restates it as `p^d·c < n`, i.e. `η < p^{−d}`.
3. `subspacePencil_vanishing_gap_linear_bound`: **(B) fails inside the family.** At `ℓ = 1` the
   relative gap is `η ≤ p^{1−m} → 0` — the *smallest* gap the construction reaches — while the
   guarantee is `p^{m−1} < n`, i.e. only linear. The exponent is `ℓ(m−ℓ)/m`, a function of the
   pair `(ℓ, m)`; `η` alone does not control it. It equals `log_p(1/η)` only when `ℓ ≥ m/2`.
4. `subspacePencil_gap_eq_pred_mul`: `c = (p−1)·(k−1)`. The family lives on the curve
   `η ≈ (p−1)ρ`: its relative gap vanishes **only together with its rate**, and `δ → 1`. Nothing
   is proved by it about constant-rate codes at a small gap — the regime that matters for FRI /
   STARK parameters.

Two further caveats, not previously recorded. (i) Only the sparse grid
`n = p^m+1, k = p^{ℓ−1}+1, c = p^ℓ−p^{ℓ−1}` is realised; the project contains no transfer of
bad-set lower bounds to neighbouring `(n,k,e)`. (ii) The construction needs
`|F| > p^m + p^{2ℓ(m−ℓ)+ℓ}`, super-quadratic in the bad-set size, so the soundness error it
certifies is `ε_mca ≥ #Bad/|F| < p^{−ℓ(m−ℓ)}` — a *decreasing* quantity. The result is about
`#Bad` versus `poly(n)`, never about `ε_mca` being large.

What survives unchanged: the refutation of the gap-layer law `poly(n) + exp(Θ(1/η))`, which
only needs (A); and the conclusion that the family does not touch constant `η`.

## 2. Strongest new theorem

### 2a. Constant-gap Grand MCA **is** the constant-gap proximity-gap problem

`FarCenterProximity.lean`. Unconditionally `badSet ⊆ goodZ` (`card_badSet_le_card_goodZ`), and

> **`badSet_eq_goodZ_of_far`.** If `e < d(f₀, C)` then `badSet k e f₀ f₁ = goodZ k e f₀ f₁`.

One line of mathematics: a close point `f₀ + γf₁` owns a window `S` with `|S| ≥ n − e`; if the
whole line were close on `S`, its point at `γ = 0` — namely `f₀` — would be within `e` of the
code. Consequences:

* `grandMCA_iff_proximityGap`: for every bound `B`, "`#Bad ≤ B` for all far-centred lines" ⟺
  "`|goodZ| ≤ B` for all far-centred lines";
* `card_badSet_le_of_forall_card_goodZ_le`: a proximity gap for *all* lines implies MCA for all
  lines, with no hypothesis on the centre;
* `epsMCA_eq_probOf_goodZ_of_far`: for a far centre, `ε_mca` *is* the probability that a random
  point of the line is `e`-close;
* sharpness: with `f₀, f₁ ∈ C` one has `goodZ = F` and `badSet = ∅`
  (`goodZ_eq_univ_of_mem_code`, `badSet_eq_empty_of_mem_code`), so the far-centre hypothesis
  cannot be dropped — and it is the only obstruction, since the two sets always nest.

So constant-gap Grand MCA is neither strictly easier nor strictly harder than the proximity gap
for Reed–Solomon lines at a constant gap to capacity, which is known only up to the Johnson
radius. Any proof of the former yields the latter.

`SubspacePencilProximity.lean` runs the same identification on the counterexample side:
`lt_distToCode_pencil` shows the pencil's centre `x ↦ x^{p^ℓ}` is farther than `e` from the
code (via the general `lt_distToCode_of_le_degree`: a polynomial word of degree `≥ k` is far
whenever `deg + e < n`), so `badSet_eq_goodZ_pencil` gives equality there, and
`exists_superpolynomial_goodZ_of_small_relative_gap` records the (A)-form counterexample for
proximity gaps.

### 2b. A non-pairwise handle: near-direction lines

`NearDirectionBadSet.lean`.

> **`card_badSet_le_mul_card_rsList_direction`.** For every line and every codeword `q₁` of
> degree `< k`, with `t = d(f₁, q₁)`:
> `#Bad ≤ t · #{ codewords within distance e + t of the centre f₀ }`.

Proof: a bad `γ` with window `S` and interpolant `P` yields the codeword `P − γ·q₁`, which
agrees with `f₀` on `S ∩ agree(f₁,q₁)`, a set of size `≥ n − e − t`; and `f₁ ≠ q₁` somewhere on
`S` (else the whole line is close on `S`), at which point `x` one recovers
`γ = (P − γq₁ − f₀)(x)/(f₁ − q₁)(x)`. So `γ ↦ (x, P − γq₁)` is injective.

This is the first bound in the project that charges each bad challenge **individually** while
covering an arbitrary direction word; it therefore escapes `pairwise_route_within_unique_decoding`
and is not confined to unique decoding. It strictly generalises the indicator-line bound
(`t = 1`, `q₁ = 0`), and at `t = 0` it gives `badSet = ∅`.

Johnson corollary (`card_badSet_le_johnson_of_near_direction`, `card_badSet_mul_le_of_near_direction`):
with agreement parameter `a ≤ n − e − t` and `2n(k−1) ≤ a²`, one gets `#Bad · a ≤ 2tn`, hence
`#Bad = O(tn/a)`. In relative terms this is a polynomial bad-set bound whenever

    ρ + η − τ > √ρ,        τ = d(f₁, C)/n,

for an **arbitrarily far centre** — a constant-gap MCA theorem for the class of lines with a
near-codeword direction, valid at every constant `η > √ρ − ρ + τ`.

### 2c. The swap symmetry, and the near-centre twin

Closeness on a window is invariant under scaling (`isCloseOn_smul`) and
`f₀ + γ·f₁ = γ·(f₁ + γ⁻¹·f₀)`; line-closeness is symmetric in the two words
(`lineCloseOn_comm`, via `isCloseOn_sub`). Hence

> **`isBad_swap`.** A nonzero bad challenge `γ` of `(f₀, f₁)` gives the bad challenge `γ⁻¹` of
> `(f₁, f₀)`; consequently `#Bad(f₀,f₁) ≤ 1 + #Bad(f₁,f₀)` (`card_badSet_le_succ_swap`).

Applying §2b to the swapped line gives the mirror bound
(`card_badSet_le_succ_mul_card_rsList_center`)

    #Bad(k, e, f₀, f₁) ≤ 1 + d(f₀,q₀) · #{ codewords within distance e + d(f₀,q₀) of f₁ }

for every codeword `q₀`. So the polynomial regime of §2b holds as soon as **one** of the two
words is near the code and the Johnson condition holds for the other one; and a line whose
centre is a codeword has at most one bad challenge (`card_badSet_le_one_of_center_mem_code`).
Together with §2a this gives a two-parameter picture: inside the Johnson-type regime of §2b the
only lines left uncontrolled are those with *both* words far from the code — and for those,
since the centre is far, `#Bad` equals the number of close challenges exactly.

## 3. Exact hypotheses

* §2a: `F` a finite field, `D ⊆ F`, `k, e` arbitrary; the equality needs `e < distToCode k f₀`
  and nothing else. The inclusion `badSet ⊆ goodZ` needs nothing.
* §2b, main bound: no hypotheses at all beyond `q₁ ∈ RS[D,k]`; likewise for §2c
  (`q₀ ∈ RS[D,k]`).
* §2b, Johnson corollary: `1 ≤ k ≤ |D|`, `e + t + a ≤ |D|`, `|D|(k−1) < a²` (resp. the
  factor-2 version `2|D|(k−1) ≤ a²`, `0 < a`).
* §1: `2 ≤ p`, `1 ≤ ℓ ≤ m`; the underlying construction additionally needs
  `|F| > p^m + p^{2ℓ(m−ℓ)+ℓ}`.

## 4. Quantitative consequence for `#Bad` / `ε_mca`

* Lower-bound side: `max #Bad ≥ p^{ℓ(m−ℓ)}` on the grid of §1, and this is `≤ n^{log_p(1/η)}`,
  polynomial at every fixed `η`. The same numbers now hold for `|goodZ|`. On this family
  `ε_mca ≥ #Bad/|F|` is smaller than `p^{−ℓ(m−ℓ)}`, so nothing is claimed about `ε_mca`.
* Upper-bound side: for a line with `d(f₁, C) = t` and `2n(k−1) ≤ a²`, `a ≤ n − e − t`,

      #Bad ≤ 2tn/a,      hence   ε_mca ≤ 2tn/(a|F|),

  in particular `#Bad = O(n)` when `t = O(1)` — matching, and generalising, the indicator-line
  case that all present counterexample families use.

## 5. Is constant-gap Grand MCA closer, refuted, or unchanged?

**Unchanged in truth value, but relocated, and its difficulty is now pinned.** It is not
refuted: §1 shows the strongest counterexample family is polynomial at every fixed `η`, and
also that it only lives at vanishing rate. It is not proved. What is new is that it is now
*exactly* the constant-gap proximity-gap problem for Reed–Solomon lines (§2a) — an equivalence,
not a one-way bound — so the search for a proof and the search for a counterexample can both be
conducted in whichever of the two languages is more convenient, and any solution must be strong
enough to settle a problem open since BCIKS. Positively, §2b removes the "direction is one
point" restriction from the class of lines for which constant-gap MCA is *known*, up to the
Johnson radius.

## 6. Remaining bottleneck

Two, and they are now visibly the same one.

* The only general mechanisms available for an arbitrary line are (i) pairs of bad challenges —
  confined to unique decoding (`pairwise_route_within_unique_decoding`) — and (ii) the new
  single-challenge charge of §2b, whose Johnson step is applied to the *centre* and therefore
  costs `√ρ`. Certified in `nearDirection_ceiling_le_nearFar_ceiling`: the dichotomy obtained by
  splitting on `d(f₁,C)` has ceiling `δ < (3 − √(5+4√ρ))/2`, never better than the existing
  pair-split ceiling `δ < (3 − √(5+4ρ))/2`. **Splitting on the direction alone cannot improve
  the certified radius**; a gain must come from elsewhere.
* By §2a and §2c the residual case is sharp: both words far from the code, and then the bad set
  *is* the close set. By §2a, any argument reaching a constant gap must in particular prove a Reed–Solomon
  proximity gap beyond the Johnson radius. The missing object is an invariant of the *set of
  close challenges as a whole* that sees `c`; neither pairs nor single-challenge list arguments
  supply one.

## 7. One best next theorem to attack

> **Target.** Let `f₀` be at distance `> e` from `C` and let `L = goodZ k e f₀ f₁`. Prove that
> the map `γ ↦ P_γ` (the closest codeword to `f₀ + γf₁`) has *large image*: `|L| ≤ n·|image|`
> is `card_shiftFibre_le`, so it suffices to bound the number of distinct `P_γ`. Concretely:
> prove that the codewords `{P_γ}` all lie in a single Reed–Solomon list of the *pencil*
> `(f₀, f₁)` at radius `e`, i.e. that the pairs `(q₀, q₁) = (P_γ − γQ, Q)` sweep out a
> **linear system of dimension `≤ n/c`** — the algebraic-geometry statement that the interpolation
> ideal of the `n − e` common agreement positions is generated in degree `< k + c`.

This is the one step that would upgrade §2b from "near direction" to "all directions": it
replaces the Johnson bound on the centre's list by a statement about the *family* of witness
codewords, which is exactly the invariant §6 says is missing. Second choice, and much cheaper:
extend §2b by replacing `d(f₁, C)` with `min over codewords q₁ of |supp(f₁ − q₁) ∩ (union of
badness windows)|`, which is the quantity the proof actually uses.
