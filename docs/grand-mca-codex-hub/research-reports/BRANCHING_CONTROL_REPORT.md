# BranchingControl — the canonical family-level residual recursion of the `τ`-window

Lean source: `RequestProject/Root/CodingTheory/BranchingControl.lean`.
Axiom audit: `RequestProject/BranchingControlAxiomAudit.lean` (all declarations depend only on
`propext`, `Classical.choice`, `Quot.sound`; no `sorry`).

## Notation

```
n      = |D|                     evaluation-domain size
k      = RS dimension
e      = decoding radius
t      = n − e                   official support threshold
tauMax = τ = rsTau k f₀ f₁       maximal correlated agreement of the line
s      = τ − k
a      = window mass of a witness
w      = n − k − e               capacity gap
```

The setting is the one classified in `TauWindowClassification`: after gauging, `A` is a normalised
`τ`-window (`|A| = τ`, `f₀ = f₁ = 0` on `A`, no codeword pair correlates with the line on more than
`τ` positions), the window is narrow (`τ + e < n`), and every bad challenge is either *terminal*
(zero witness, `#Bad₀ ≤ e + 1`) or carries a positive-mass official witness `(p, S)`:
`p ≠ 0`, `deg p < k`, `|S| ≥ t`, `f₀ + γ f₁ = p` on `S`.

This report records the object that was missing there: not another `F(n,k,e,s)` bound, but the
**recursion** — how a parent instance decomposes into finitely many children of the same kind.

## The canonical residual child class

For a positive-mass witness `p` put

```
Z = windowZeros A p = {x ∈ A : p(x) = 0} ⊆ A ,   |Z| = τ − a .
```

`Z` is the **canonical child class** of the witness.  It determines the child instance completely:

| object | Lean | value |
|---|---|---|
| residual domain | `resDomain D A` | `D ∖ A`, of size `n₁ = n − τ` |
| residual dimension | `resDim k Z` | `k₁ = k − |Z| = a − s` |
| residual radius | `resRad e A Z` | `e₁ = e − a` |
| vanishing polynomial | `vanishPoly Z` | `V_Z = ∏_{z ∈ Z}(X − z)` |
| residual words | `resWord A Z f_i` | `g_i = f_i / V_Z` on `D ∖ A` |
| child bad set | `resBadSet k e A Z f₀ f₁` | `badSet k₁ e₁ g₀ g₁` over `D ∖ A` |

`V_Z` is nonzero on `D ∖ A` (`eval_vanishPoly_res_ne_zero`), so the division is legitimate and the
shortened code `V_Z · RS_{k₁}` on `D ∖ A` becomes an honest `RS_{k₁}(D ∖ A)`: **the child is again
an instance of the same problem**, which is what makes the recursion possible.

## The six obligations

1. **Exact official witness transport.**  `witness_eq_vanishPoly_mul` factors `p = V_Z · r` with
   `r ≠ 0` and `deg r < k₁`; `resWord_witness` shows the residual line point equals `r` exactly on
   the residual support `resSupport A S`, whose size is exactly `|S ∖ A|`
   (`card_resSupport`).  The official threshold transports exactly: `|S₁| ≥ n₁ − e₁ = t₁`, proved
   inside `mem_resBadSet_of_positiveMass` from `card_sdiff_window_ge`.
2. **The child stays in the class needed downstream.**  The parent witness lies in the shortened
   code `V_Z · RS_{k₁}` (`witness_eq_vanishPoly_mul`); after division the child is the ordinary RS
   instance `(D ∖ A, k₁, e₁)`, and `mem_resBadSet_of_positiveMass` proves that `γ` is **bad** for
   it — including the negative half of `IsBad`: if the child line were closed on `S₁`, the
   codewords `V_Z · q₀`, `V_Z · q₁` would correlate with `(f₀, f₁)` on `(S ∖ A) ∪ Z`, of size
   `≥ n − e > τ`, contradicting maximality of the window.
3. **`w` is preserved.**  `child_capacity_gap`: `n₁ = k₁ + e₁ + w` whenever `n = k + e + w` and
   `τ = k + s`.  The descent runs at constant capacity gap.
4. **Strict descent.**  `child_radius_lt`: `e₁ < e` (the mass is `≥ s + 1 ≥ 1`);
   `child_dim_le`: `k₁ ≤ k`; hence `child_complexity_lt`:
   `instComplexity k₁ e₁ = k₁ + e₁ < k + e`.  The base case is
   `card_badSet_le_one_of_radius_zero`: at radius `0` a line has at most one bad challenge.
5. **Fibring with explicit multiplicity.**  `childClasses k e A` is the explicit finite index set
   `{Z ⊆ A : |Z| < k, |A| ≤ |Z| + e}` — exactly the constraints `a ≥ s + 1` and `a ≤ e`.
   `badSet_subset_terminal_union_children`:

   ```
   Bad(parent) ⊆ Bad₀  ∪  ⋃_{Z ∈ childClasses} Bad(child Z) ,
   ```

   and the multiplicity is bounded explicitly by
   `card_childClasses_le`: `#children ≤ ∑_{j ∈ [τ − e, k)} C(τ, j)`, and
   `card_childClasses_le_pow`: `#children ≤ 2^τ`.
   `child_class_unique_of_uniqueDecoding` shows the assignment `γ ↦ Z` is canonical (independent
   of the choice of official witness) as soon as `k + 2e ≤ n`.
6. **The branching recurrence.**

   ```
   branchingControl           #Bad ≤ #Bad₀ + Σ_{Z ∈ children} #Bad(child Z)
   branchingControl_terminal  #Bad ≤ (e+1) + Σ_{Z ∈ children} #Bad(child Z)
   branchingControl_recurrence  #Bad ≤ (e+1) + Σ_Z G(n₁, k₁(Z), e₁(Z))   for any child bound G
   branchingControl_budget    #Bad ≤ (e+1) + N·L  when #children ≤ N and every child ≤ L
   ```

   and the target trichotomy, `branchingControl_master`:

   ```
   Bad(parent) ≤ (e+1) + Σ_child cost(child)
     ∧ ( #Bad ≤ (e+1) + N·L                       -- bounded branching · bounded fibres
       ∨ N < #children                            -- many children
       ∨ ∃ Z, BranchingCertificate … (L+1) …)     -- one fibre large: certificate
   ```

   The certificate `BranchingCertificate k e w L f₀ f₁ A Z` records exactly what the structural
   branch needs: a single child class `Z ⊆ A` with `|Z| < k`, preserved capacity gap
   `n₁ = k₁ + e₁ + w`, strict descent `e₁ < e` and `k₁ + e₁ < k + e`, and at least `L` bad
   challenges concentrated on that one child.  `exists_large_child` is the pigeonhole that
   produces such a concentration: some child carries a `1/#children` share of the parent bad set.

## The deployed point

`deployed_branchingControl` instantiates the master theorem at `n = 2²¹`, `k = 2²⁰`,
`e = 978944`, `w = 69632`, `τ = k + s`, `s < w`: the parent cost is at most `978945` plus the sum
of the children's costs, and for every budget pair `(N, L)` the trichotomy holds.

Honest reading of the numbers: at the deployed point the *a priori* number of children,
`∑_{j ∈ [τ−e, k)} C(τ, j)`, is astronomically large, so the first branch of the trichotomy is not
the one that fires — the content is the third: either the branching is genuinely bounded (which
must be established by structural information about which `Z` can occur), or a single child class
absorbs a fixed fraction of the bad set, and then the certificate hands the structural branch a
*smaller* instance (`e₁ < e`) with the *same* capacity gap `w` and a large bad set — the hypothesis
those arguments need.  No claim is made here that the recursion by itself bounds `#Bad`.

## Scope and non-claims

* No new `F(n,k,e,s)` bound on the positive-mass branch is claimed, and none is used.
* The recursion is stated as an inequality over the explicit index set `childClasses`; children
  with empty fibres are included, which only weakens the inequality.
* Canonicity of `Z` is proved under `k + 2e ≤ n`; outside that regime the child class is canonical
  relative to the chosen official witness, which is all the recursion uses.
