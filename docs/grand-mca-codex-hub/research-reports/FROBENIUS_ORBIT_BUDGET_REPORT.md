# The Frobenius-orbit budget: how far Galois-type constraint-rank compression can go

**Verdict: [FROBENIUS-MCA-BRIDGE] + [CONSTRAINT-RANK-INVERSE-THEOREM, Galois part] + [BARRIER].
Grand MCA is not resolved, no better UNSAFE witness is produced, and no beyond-Johnson SAFE
bound is claimed.**

Everything below is machine-checked, `sorry`-free, and uses only
`propext / Classical.choice / Quot.sound` (audited in
`RequestProject/SemilinearDescentAxiomAudit.lean`). All statements are against the project's
own official `IsBad / badSet / IsCloseOn / LineCloseOn / epsMCA` predicates. Nothing existing
was modified or deleted.

New modules:

* `RequestProject/Root/CodingTheory/SemilinearPlaneDescent.lean`
* `RequestProject/Root/CodingTheory/SemilinearPlaneClassification.lean`
* `RequestProject/Root/CodingTheory/FrobeniusOrbitBudget.lean`
* `RequestProject/Root/CodingTheory/KoalaBearSemilinearRow.lean`
* `RequestProject/Root/CodingTheory/KoalaBearOrbitDimension.lean`
* `RequestProject/SemilinearDescentAxiomAudit.lean`

---

## 1. The question this attacks

The mission asks what algebraic structure could collapse the effective `F_p` constraint rank of
extension-field MCA from the generic `6c` to about `c`, and whether such a structure can be
classified or exploited.

There is exactly one mechanism that ties the six base-field coordinates of a `K = F_{p^6}`-valued
pencil to each other *without moving the agreement support*: the Frobenius. It acts pointwise on
values, so it maps a word explained by a degree-`< k` polynomial on a support `S` to another word
explained on the **same** `S`, with the same degree bound. (A domain symmetry such as `x ↦ ζx`
does not: it transports the support, and the official `IsBad` predicate quantifies over one fixed
support, so no contradiction can be extracted from it. This is why Frobenius is special here.)

The results below measure exactly how much challenge budget such a coordinate-tying mechanism can
buy.

## 2. Semilinear descent (the plane version)

`isBad_semilinear_rel`. Let `σ` be a ring endomorphism of the code field fixing the evaluation
domain pointwise, and suppose the `σ`-image of the pencil lies in the plane the pencil spans
**modulo the code**:

```
σ(f₀ x) = a f₀ x + b f₁ x + g₀(x),      σ(f₁ x) = c f₀ x + d f₁ x + g₁(x),   deg g₀, g₁ < k.
```

Then every officially bad challenge satisfies the twisted fixed-point relation

```
b + d·σγ = γ·(a + c·σγ).
```

Proof: badness at `γ` gives one explanation `f₀ + γ f₁ = P` on `S`; applying `σ` gives a second
explanation of `(a + c σγ) f₀ + (b + d σγ) f₁` on the *same* `S`. Two independent combinations
explained on one support force both `f₀` and `f₁` to be explained there — the correlated
agreement that badness forbids. Hence the two combinations are proportional.

For `σ y = y^q` this is a nonzero polynomial equation of degree `≤ q+1`, so
`card_badSet_le_of_semilinear`: `#Bad ≤ q + 1`, at every rate and every radius.

This class is strictly larger than the project's earlier base-field-rational class: it is closed
under multiplying the pencil by any constant of the big field and under adding arbitrary codewords
(`card_badSet_le_of_scaled_baseField`), neither of which the fixed-value descent of
`SubfieldDescent.lean` allows.

## 3. The inverse question: what a Frobenius-stable plane is

`span_fixed_of_stable` is Speiser's theorem, machine-checked: a `K`-subspace of a function space
stable under the coordinatewise action of `σ` (with `σ^m = id` and pairwise distinct iterates) is
spanned by its `σ`-fixed vectors. The proof is the averaging map `t(λ) = Σ_i σ^i(λ)·σ^i(w)` plus
Artin's linear independence of the characters `σ^i`.

Consequence (`KoalaRow.frobenius_stable_plane_is_baseField`): on the deployed row a pencil plane
which is Frobenius-stable *on the nose* is spanned by base-field-valued words. So the Galois
mechanism, taken by itself, produces nothing beyond base-field rationality; the genuinely new
part of the safe class in §2 is stability **modulo the code**.

## 4. The general theorem: the Frobenius-orbit dimension

No hypothesis on the pencil at all. Let `V = span_K {σ^i f₀, σ^i f₁}` be the `σ`-orbit span, and
let `d = dim_K V` (`1 ≤ d ≤ 2m`; on the deployed row `d ≤ 12`). By §3, `V` has a basis
`u₁, …, u_d` of `σ`-fixed words; write `f₀ = Σ a_j u_j`, `f₁ = Σ b_j u_j`.

`exists_orbit_annihilator`: for every officially bad `γ` there is a **nonzero `σ`-fixed covector**
`c` with

```
Σ_j c_j (a_j + γ b_j) = 0.
```

Reason: the `m` words `σ^i(f₀ + γ f₁)` are all explained on the same support `S`; if they spanned
`V` then `f₀` and `f₁` would be explained on `S` too, contradicting badness. So the orbit of the
line point degenerates inside `V`, and the degeneracy is cut out by one `Fix(σ)`-rational
covector (the annihilator of the degenerate span is again `σ`-stable, so Speiser gives it a
rational vector).

`card_badSet_mul_le_of_orbit`: distinct bad challenges give covectors that are not even
proportional, hence

```
#Bad · (q − 1) + 1 ≤ q^d,      q = #Fix(σ),    i.e.   #Bad ≤ 1 + q + ⋯ + q^{d−1}.
```

The projective refinement (the factor `q − 1`) is what makes the statement bite: the crude bound
`#Bad < q^d` would be useless at `d = 2` on the deployed row.

## 5. Deployed numbers (all machine-checked as Lean arithmetic)

Row: `p = 2^31 − 2^24 + 1 = 2130706433`, `K = F_{p^6}`, `H = μ_{2^21}`, `k = 2^20` (rate 1/2),
`B* = ⌊|K|/2^128⌋ = 274980728111395087`, `log₂ B* = 57.9321`.

| orbit dimension `d` | budget `1 + p + ⋯ + p^{d−1}` | `log₂` | vs `B*` |
|---|---|---|---|
| 1 | 1 | 0 | safe |
| 2 | `p + 1 = 2130706434` | 30.989 | **safe**, 26.9 bits of slack |
| 3 | `p² + p + 1 = 4539909905758289923` | 61.977 | above `B*` — undecided |
| ≥ 4 | ≥ `p³` | ≥ 93 | undecided |

Hence:

* `KoalaRow.koalaRow_semiInvariant_safe`: any pencil whose plane is Frobenius-stable modulo the
  code is safe at **every** radius, with `ε_mca ≤ (p+1)/p^6 < 2^{−154.9} ≪ 2^{−128}`.
* `KoalaRow.prizeBreaking_orbit_dim_ge_three`: **any** pencil that breaks the Prize challenge
  threshold at some radius must have Frobenius-orbit dimension `d ≥ 3`.
* `KoalaRow.semilinear_frontier`: `p + 1 < B* < p² + 1` — the frontier of the mechanism, checked
  as an integer inequality.

## 6. What this says about the `6c → c` clue

The Galois direction of the constraint-rank question is now closed quantitatively. Full
coordinate tying — the structure that would let the six `F_p`-coordinate systems impose only `c`
independent scalar conditions instead of `6c` — is exactly `d ≤ 2`, and it caps the challenge set
at `p + 1`, i.e. 31.0 bits, which is 26.9 bits short of the 57.93 bits the Prize needs. Any
Prize-scale extremizer therefore uses a *partially* tied structure, `d ≥ 3`, for which the
Frobenius argument degrades to `≈ p² = 2^{62}` and says nothing.

This is consistent with, and sharpens, the mission's small-model screening: genuine
extension-valued lines (large orbit dimension) behave qualitatively differently from base-field or
rank-one ones (orbit dimension ≤ 2). The transition is not a numerical accident — it is the point
where the rational-covector count `1 + p + ⋯ + p^{d−1}` crosses `B*`.

## 7. Honest scope

* **Theorems.** Everything in §§2–5, `sorry`-free, axioms audited.
* **Not proved.** No new SAFE bound for arbitrary pencils at the deployed radius; no better
  UNSAFE witness; Grand MCA untouched. The `d ≥ 3` statement is a *necessary condition* on a
  hypothetical Prize-breaking pencil, not a proof that none exists.
* **Not formalized.** The "modulo the code" refinement of the classification in §3 (which would
  need the additive Hilbert 90 / descent step in the quotient `K^D / C`). Without it, §3 is stated
  for planes stable on the nose; the safe bound of §2 already covers the mod-code case.
* **External claims.** Nothing about the externally reported ScalarOrbitPencil witness is
  replayed or asserted. The only consequence for it is conditional and cheap: if such a pencil
  exists on this row, its Frobenius-orbit dimension is at least 3.

## 8. Next smallest unresolved object

**Where the method stops, exactly.** The necessary condition extracted from badness is precisely
"the coordinate vector `a + γ b` of the line point lies on a `Fix(σ)`-rational hyperplane of the
orbit span", and that condition is Frobenius-closed: applying `σ^i` to it gives nothing new,
because a rational covector commutes with `σ`. So inside the Galois framework the count
`1 + q + ⋯ + q^{d−1}` is the whole content, and improving it at `d ≥ 3` requires input that the
Frobenius action cannot see (degrees, the evaluation domain, or the deviation-locus geometry).
This is a limitation of the method, not a lower bound on `#Bad`: the challenges satisfying the
condition need not be bad.

Orbit dimension exactly 3: a pencil whose Frobenius orbit spans a 3-dimensional `K`-space with a
base-field basis, and whose bad challenges fill more than `2^{57.93}` of the at most
`p² + p + 1 ≈ 2^{62}` rational covector classes — i.e. more than a `2^{−4.05}` fraction of the
degeneracy locus. Two concrete follow-ups:

1. Show that at `d = 3` the covector attached to a bad challenge cannot be arbitrary — e.g. that
   the map `γ ↦ [c_γ]` lands in a subvariety of the rational projective plane of size `O(p)`,
   which would push the safe range to `d ≤ 3` and beyond.
2. Combine the orbit budget with the Desarguesian-spread rank theorem of
   `SpreadMCA.lean`: both are rank statements, one about the challenge-side covector and one
   about the deviation locus, and they constrain different halves of the same configuration.
