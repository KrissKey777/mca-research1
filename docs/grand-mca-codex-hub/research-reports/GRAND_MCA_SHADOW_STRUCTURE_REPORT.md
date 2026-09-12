# GRAND MCA — structural theory of official families with **many** kernel shadows

New Lean module: `RequestProject/Root/CodingTheory/ShadowDescentSharpBound.lean`
Axiom audit: `RequestProject/ShadowDescentAxiomAudit.lean`
(all declarations: `propext`, `Classical.choice`, `Quot.sound`; no `sorry`).

Notation as in the mission: `C = RS_k(D)`, `n = |D|`, official radius `e`, received pair
`(f₀,f₁)`, `Q_S = Short(C^⊥,S^c) = rsDualOn k S`, `Λ = synMap f₀ f₁`, `K = ker Λ`,
`K_S = Q_S ∩ K = kernelShadow k S f₀ f₁`, `ℓ(S) = [-γ_S : 1]`.

Banked results (fixed shadow, rank-one label, invisible intersections) are used but **not
re-optimised**, exactly as instructed.

---

## 0. Summary of what is new and machine-checked

| # | Statement | Lean name | Hypotheses |
|---|---|---|---|
| 1 | Bad set is an invariant of the coset `(f₀,f₁) + C²` (= of the extended code `C⁺ = C + ⟨f₀,f₁⟩`) | `badSet_sub_polyWord` | none |
| 2 | Every kernel shadow `K_S` is an invariant of `C⁺` | `kernelShadow_sub_polyWord` | none |
| 3 | Unconditional dichotomy: `#Bad ≤ 1` **or** witness-preserving strict descent to a defect pair supported on `≤ 2e` coordinates with *literally the same* bad set | `badSet_descent_dichotomy` | none |
| 4 | Fibre partition ⇒ `#Bad ≤ e + 1` | `card_badSet_le_succ_of_third` | `1 ≤ k`, `k + 3e ≤ n` |
| 5 | `ε_mca ≤ (e+1)/|F|`, also for the max over all lines | `epsMCA_le_succ_of_third`, `epsMCAmax_le_succ_of_third` | as above |
| 6 | **Sharpness**: a pair with exactly `e + 1` bad challenges exists | `exists_badSet_card_succ_of_third`, `exists_badSet_card_eq_succ` | `1 ≤ k`, `1 ≤ e`, `k + 3e ≤ n` |
| 7 | Shadow rigidity **without** the distinct-challenge hypothesis: `K_S = K_T` ⇒ `S ⊆ T` or `|S ∩ T| = |S| − 1` | `card_inter_add_one_eq_of_kernelShadow_eq_of_not_subset`, `card_inter_succ_of_kernelShadow_eq_of_ne` | `k + 2 ≤ |S|`, `S` carries a challenge |

Items 4–6 together give the **exact constant**: below capacity

    max over all received lines of #Bad  =  e + 1 ,

improving the repository's previous `2e + 1` (`CorrelatedAgreementRefined`) and `max(2e,1)`
(`ProjectiveSyndromeDirection.card_badSet_le_two_mul_of_third`), and closing that regime — the
constant can no longer be improved by any method.

---

## 1. Priority 1 — the natural invariant of a changing shadow

**Answer: the shadow is the shortened dual of the *extended code*, and that is the only datum
it depends on.**

For `μ ∈ Q_S` the pairing with a codeword vanishes, so `Λ μ` only depends on `(f₀,f₁)` modulo
`C²`.  Formally (`synMap_sub_polyWord_apply`, `kernelShadow_sub_polyWord`)

    K_S(f₀ - p₀, f₁ - p₁) = K_S(f₀, f₁)      for all deg p₀, p₁ < k,

so the whole shadow family `S ↦ K_S` is a function of `C⁺ = C + ⟨f₀,f₁⟩`.  Dually, `K_S` is the
annihilator inside `F^S` of the punctured extended code `C⁺|_S`; a *change* of shadow
`K_S ≠ K_T` is exactly a change of that punctured code, i.e. of which codeword of `C⁺` is
invisible on the window.  Under the rank-one law `dim K_S = dim Q_S − 1`, so `K_S` is a
hyperplane of `Q_S` and `C⁺|_S` drops exactly one dimension: the window sees exactly one
`C⁺`-codeword vanishing off it, whose class in `C⁺/C ≅ F²` is the projective label `ℓ(S)`.

This identification is what makes the *descent* below legitimate, and it is also what makes the
shadow **rigid**:

**Shadow rigidity (item 7).**  If `S` carries a challenge, `|S| ≥ k + 2` and `K_S = K_T`, then
`S ⊆ T` or `|S ∩ T| = |S| − 1`.  The proof no longer needs two challenges: `K_S = K_T ⊆
Q_S ⊓ Q_T = Q_{S∩T} ⊆ Q_S`, and the banked "nothing strictly between the shadow and the local
dual" lemma forces `Q_{S∩T} ∈ {K_S, Q_S}`; strict monotonicity of the local duals kills the
second option, and a second missing point would force an intermediate dual.

*Structural consequence.*  The shadow map is faithful up to one point: two windows with the
same shadow differ by exactly one element (or are nested with a one-point gap).  A shadow class
is therefore a very thin family of windows — in the banked fixed-shadow theorem, a star or a
clique — so **the product bound `#Bad ≤ #{shadow classes} · max_K #{lifts over K}` cannot be a
shortcut**: bounding the number of shadows is essentially as hard as bounding the number of
windows.  Below capacity this is now moot (item 4 gives the exact answer directly); above
capacity it says the shadow factorisation is not the mechanism to attack.

## 2. Priority 4 (allowed as a first-class outcome) — the descent, unconditional

`badSet_descent_dichotomy`: either `#Bad ≤ 1`, or there are codewords `p₀,p₁` and a set `A`,
`|A| ≤ 2e`, with

* `(f₀,f₁) = (p₀,p₁)` outside `A` (structural separation: one codeword pair explains the pair
  off `2e` coordinates);
* `Bad(f₀ − p₀, f₁ − p₁) = Bad(f₀,f₁)` **as sets**, and by `isBad_sub_polyWord` with the *same*
  official windows, so same-support agreement and exact non-containment are transported
  verbatim;
* every kernel shadow is unchanged (item 2), so the shadow family is transported too;
* the well-founded measure `|supp(f₀,f₁)|` drops from `n` to `≤ 2e` — strictly, whenever
  `2e < n`.

No hypothesis on `k`, `e`, `n`: the descent is available **beyond capacity as well**.  It is
the correct normal form of an official MCA family: *every* official family is the family of a
pair supported on at most `2e` coordinates.

## 3. Priorities 2 and 5 — zero-gain / invisible families, and the composition

After the descent, write `d_i = f_i − p_i` (supported in `A`) and, for a bad challenge `γ`, let
`E_γ = D ∖ S_γ`, `|E_γ| ≤ e`.  Two facts drive everything:

1. the witness window is contained in the agreement set of the descended line
   (`exists_window_subset_agreement_of_isBad`), so the *fibre*
   `Φ_γ := A ∩ {x : d₀(x) + γ d₁(x) = 0}` has `|Φ_γ| ≥ |A| − e`;
2. two distinct challenges cannot share a point of `A` (this is exactly the banked "invisible
   intersection" law in point form), so the fibres are **pairwise disjoint**, and each is
   nonempty because the window is not contained in the common agreement set.

Hence `#Bad · (|A| − e) ≤ |A| ≤ 2e` and `#Bad ≤ |A|`, which forces `#Bad ≤ e + 1`
(worst case `|A| = e + 1`).  So a large official family is *not* limited by a graph/Johnson
bound but by a **partition of the defect support**: challenges are the slopes
`γ_x = −d₀(x)/d₁(x)` of the defect pair, one class of `A` per challenge.

Composition with the fixed-shadow theorem (priority 5) is now trivial and, honestly, no longer
needed below capacity: the direct count already equals the maximum `e + 1`, while
`#{shadows} · max #{lifts}` is `≥ e + 1` by item 7.  We therefore record the composition as a
*consistency check*, not as the route.

## 4. Sharpness (why the theory stops here below capacity)

`exists_badSet_card_succ_of_third`: pick `A ⊆ D` with `|A| = e + 1` and set

    f₁(y) = 1 and f₀(y) = −y   for y ∈ A,      f₀(y) = f₁(y) = 0 otherwise.

For each `x ∈ A` the challenge `γ = x` is official with window `D ∖ (A ∖ {x})` (co-size exactly
`e`): the combination `f₀ + x f₁` vanishes on the window, while `f₁` cannot be explained there
(it would need a nonzero polynomial of degree `< k` with `≥ k` roots).  The `e + 1` points of
`A` are distinct elements of `F`, so `#Bad ≥ e + 1`, and with item 4, `= e + 1`.

Note where each hypothesis is used: `e ≥ 1` for the non-containment (at `e = 0` the bad set is
empty or a point), `k ≥ 1` so that the zero polynomial is admissible, and `k + 3e ≤ n` only for
the upper bound.

## 5. Priority 3 — where RS/evaluation structure is genuinely needed

* Items 1–3 (invariance, descent, dichotomy) use **nothing** beyond linearity of the code: they
  hold verbatim for an arbitrary linear code with `IsCloseOn` read as "agrees with a codeword
  on `S`".
* Item 4 uses the code only through the interpolation lemma
  `eval_eq_of_card_agreement_ge` — i.e. through **MDS-ness** (two codewords agreeing on `k`
  positions are equal).  Any MDS code gives `#Bad ≤ e + 1` by the same proof.
* Item 6 (sharpness) uses the evaluation structure: distinct challenges are produced from
  distinct *domain points*, so it needs `|F| ≥ |D| ≥ e + 1` and the fact that the defect slopes
  are the evaluation points themselves.  This is the only place where "RS" rather than "MDS" is
  visible, and it is visible as a *lower bound*.
* Item 7 uses MDS-ness twice (strict monotonicity of shortened duals, rank-one law).

Coefficient/representation data is preserved throughout: every statement is about the actual
words and windows, never about an abstract matroid.

## 6. Honest status of the beyond-capacity regime (`n < k + 3e`)

The descent (item 3) survives, but the counting step does not, and *that is not a defect of the
proof*: this repository already contains matching lower bounds (`card_badSet_eq_choose_gapOne`
gives `C(n,k+1)` at gap one, `exists_superpolynomial_badSet_of_small_relative_gap` gives
superpolynomial families near capacity).  What the present analysis adds is the exact place
where the argument breaks: after descent, badness of `γ` means

    d₀ + γ d₁  =  c_γ   off  E_γ,   c_γ ∈ C,  supp(c_γ) ⊆ A ∪ E_γ,   |A ∪ E_γ| ≤ 3e,

and below capacity `c_γ = 0` (no codeword of weight `≤ 3e`), which is exactly the fibre
equation.  Beyond capacity `c_γ` may be a nonzero codeword supported in `A ∪ E_γ`; such
codewords are the multiples of the vanishing polynomial of `D ∖ (A ∪ E_γ)`, i.e. they live in a
shortened RS code of length `≤ 3e` and dimension `≤ k + 3e − n`.  The natural continuation is
therefore a *shortening descent* `(n,k) → (|B|, k − (n − |B|))`, which preserves the redundancy
`n − k` and hence is **capacity-neutral**: it cannot convert a beyond-capacity instance into a
sub-capacity one.  This is a structural reason why no descent of this type can close the
beyond-capacity case, and it matches the known lower bounds.  We state it as an observation,
not as a theorem, and we did not formalise it.

## 7. Deployment rows

Nothing here is a claim about the deployed row `e = 978944` or the certified UNSAFE row
`e = 978945`: neither row's parameters occur in this repository (see the previous run's report),
and both sit in regimes decided by `k + 3e ≤ n` — the test to apply is exactly that inequality,
after which item 4 gives `#Bad ≤ e + 1` and item 6 says no better constant exists.
