# Classification of the narrow `τ`-window

**Question.**  The previous reduction left exactly one gate: for a Reed–Solomon line
`γ ↦ f₀ + γ·f₁` (dimension `k`, `n = |D|` points, radius `e`) either correlated agreement holds
outright, or the maximal correlated agreement lies in

```
k ≤ τ = k + s < n − e ,       0 ≤ s < w := n − k − e   (deployed: w = 69632).
```

The task: find the strongest theorem `τ = k + s → #Bad ≤ F(n,k,e,s)` with `F ≤ B*` throughout the
deployed range, or a canonical residual descent.

**Answer delivered.**  A complete structural classification of the window by one new invariant, an
`F` of the requested shape on the branch where it exists (with `F ≤ e + 1 ≪ B*` for *every* `s`),
a well-founded residual descent for the complementary branch, and a machine-checked extremal
example showing both that the bound is attained and that the branch split cannot be avoided.

Lean: `RequestProject/Root/CodingTheory/TauWindowClassification.lean`,
`RequestProject/Root/CodingTheory/TauWindowExtremal.lean`; audit
`RequestProject/TauWindowClassificationAxiomAudit.lean` (only `propext`, `Classical.choice`,
`Quot.sound`; no `sorry`).  Nothing previously banked was rebuilt: the existing `rsTau`/`badSet`
layer is used as it stands.

---

## 1. The gauge: normalising the `τ`-window

`τ` and the bad set are both invariant under subtracting codewords from `f₀` and `f₁`
(`rsTau_sub_poly`, `isBad_sub_poly`).  Subtracting a `τ`-attaining codeword pair therefore costs
nothing and buys everything: after the shift there is a window `A` with

* `f₀ = f₁ = 0` on `A`,
* no codeword pair correlates with `(f₀,f₁)` on more than `|A| = τ` positions

(`NormalisedWindow`, `exists_normalisedWindow`).  Two consequences drive the whole analysis.

* `normalisedWindow_eq_commonZeroSet`: in the gauge `A` **is** the common zero set of `f₀` and
  `f₁`.  Outside `A` the two words never vanish together.
* `subsingleton_challenge_of_notMem`: hence for `x ∉ A` the equation `f₀ x + γ·f₁ x = 0` has **at
  most one** solution `γ`.  Every position outside the window pins at most one challenge.

A second pinning statement, at the level of windows rather than positions:
`eq_of_two_challenges_same_window` — if the line point is explained by a codeword on the *same*
window `S` at two different challenges, then `|S| ≤ τ`.  Inside the `τ`-window distinct bad
challenges therefore have distinct witness windows.

## 2. The invariant: the window mass

A bad challenge comes with a witness codeword `p` explaining the line point on a window `S`,
`|S| ≥ n − e`.  Define its **window mass**

```
a(p) = #{ x ∈ A : p(x) ≠ 0 } .
```

This is exactly the number of errors the challenge must spend *inside* the correlated window, and
it classifies the bad set (`isBad_dichotomy`):

* `a = 0` ⟺ `p = 0` (`eq_zero_of_windowMass_zero`, using `k ≤ τ`): the **zero-witness branch**;
* `p ≠ 0` ⟹ `a ≥ s + 1` (`windowMass_ge_of_ne_zero`), and always `a ≤ e`
  (`windowMass_le_of_witness`): the **positive-mass branch**.

Further exact relations: `card_sdiff_window_ge` (`|S ∖ A| ≥ (w − s) + a`: the agreement outside
the window *grows* with the mass) and `card_inter_sdiff_window_le` (**exact challenge transport**:
for two bad challenges `|(S ∩ S′) ∖ A| ≤ a + a′`).

## 3. The theorem on the zero-witness branch

For a zero-witness challenge the line point itself vanishes on `S`, hence on `≥ n − e − τ = w − s`
positions **outside** `A`; by the pinning statement those zero sets are pairwise **disjoint**.
Counting them inside `Aᶜ` (of size `n − τ = e + w − s`) gives the main theorem
(`card_zeroWitnessBadSet_mul_le`):

```
#Bad₀ · (w − s) + τ ≤ n ,        i.e.   #Bad₀ ≤ (n − k − s)/(w − s) = 1 + e/(w − s) ,
```

`card_zeroWitnessBadSet_le_div`, and, uniformly in `s`, `#Bad₀ ≤ e + 1`
(`card_zeroWitnessBadSet_le_succ`).  So on this branch the requested `F` exists and is small:

| `s` | `F(n,k,e,s) = 1 + e/(w − s)` at the deployed point |
|---|---|
| `0` | `15` (`deployed_zeroWitness_le_fifteen`) |
| any `s < 69632` | `≤ 978945 = e + 1` (`deployed_zeroWitness_le`) |

against the deployed budget `B* ≈ 2⁵⁷·⁹`.  No second-moment, Johnson, or list-decoding input is
used anywhere: the argument is pure disjointness plus maximality of `τ`.

## 4. The residual descent on the complementary branch

A positive-mass challenge vanishes on the `τ − a` window positions off its mass, so its witness is
divisible by their vanishing product (`witness_shortened_factorisation`) and the quotient has
degree `< k − (τ − a) = a − s` (`witness_shortened_degree`): the witness lives in the RS code
shortened at `τ − a` points, of dimension `a − s`.  Restricting the instance to `B = Aᶜ` gives

```
n₁ = n − τ = e + w − s ,     k₁ = a − s ≤ e − s ,     e₁ = e − a ,
```

and `residual_parameters` records the key identity `n₁ = k₁ + e₁ + w`: **the capacity gap is
preserved exactly**, while the dimension drops from `k` to `a − s ≤ e − s < k` whenever `e < k`
(`residual_dim_lt`) — the deployed regime (`e = 978944 < 1048576 = k`).  This is the canonical
residual descent the task allowed as an alternative: it descends in the code dimension at constant
capacity gap, and it is well founded.

`tauWindow_master` packages §§1–4 into one statement about an arbitrary line.

## 5. Sharpness, and why the branch split is not an artefact

`TauWindowExtremal.lean` contains one explicit line, entirely machine-checked (`decide`):
`F = ZMod 5`, `D = F` (`n = 5`), `k = 1`, `e = 2`, so `t = 3`, `w = 2`;

```
f₀ = (0,0,2,1,0) ,   f₁ = (0,1,3,2,0) ,   A = {0,4} ,   τ = 2 = k + 1  (s = 1) ,  τ < t .
```

* `zeroWitnessBadSet_card_eq_three`: the zero-witness bad set is exactly `{0,1,2}`, of size `3` —
  which is exactly the bound `(n − k − s)/(w − s) = 3/1`.  **The bound of §3 is attained.**
* `four_le_card_badSet`: the full bad set contains `{0,1,2,4}`.  The extra challenge `γ = 4` has
  line point `(0,4,4,4,0)`, explained by the *nonzero* constant `4`; its window mass is `2 = s+1`,
  the minimum allowed.  So `#Bad = 4 > 3 = #Bad₀` (`zeroWitness_lt_badSet`).

**Consequence.**  `F(n,k,e,s) = (n−k−s)/(w−s)` is *false* as a bound for the whole bad set; the
zero-witness restriction in §3 is necessary, not a proof artefact, and any theorem covering the
whole window must control the positive-mass branch.

## 5b. Extending the bound from mass zero to bounded mass

The transport theorem of §2 also converts into a cardinality bound beyond `a = 0`.  The *global*
second-moment mechanism is empty in this window (it needs `|D|·τ < t²`, and `k ≤ τ` forces the
Johnson radius); the counting in `card_le_of_massBounded` is a different one, run with the
mass-weighted pairwise bound `|(S ∩ S′) ∖ A| ≤ a + a′` instead of the useless `τ`:

```
#B · (W² − |D|·2a) ≤ |D|·W       for challenges of window mass ≤ a and agreement ≥ W outside A.
```

At the deployed minimal window (`W = w = 69632`, `|D| = 2²¹`) this is non-vacuous up to
`a ≤ 1156`, and `deployed_massBounded_le` gives `#B ≤ 223` for all bad challenges of window mass
`≤ 1000`.  So the classified (bounded) part of the bad set is not just the zero-mass branch.

## 6. Where the frontier now is (honest scope)

The set-system data produced by §2 for the positive-mass branch is: sets `T_γ = S_γ ∖ A` inside a
universe of size `n − τ = e + w − s`, with `|T_γ| ≥ (w − s) + a_γ` and pairwise intersections
`≤ a_γ + a_γ′`.  For `a ≡ 0` this is disjointness and yields §3.  For masses above the threshold of §5b (deployed `a > 1156` with the ambient universe, and
`a > e − √(e² − (w−s)²) ≈ 2481` even with the sharpest possible universe `|Aᶜ|`) these
constraints are satisfiable by families of
arbitrarily large size — the sets are large but their pairwise intersections are correspondingly
large — so *no* bound on the positive-mass branch can follow from the pairwise data alone.  Any
further progress must use the residual RS structure of §4 (the shortened codes carrying the
witnesses), not a counting argument over the windows.

Exploratory numerics (`analysis/tau_window_lines.py`, `analysis/tau_window_growth.py`,
`analysis/tau_window_scan.py`) exhaustively enumerate every line of the residual space for small
`(q,n,k,e)`.  They are *not* part of the formal record; what they indicate is: for `w ≥ 2` the
maximum of `#Bad` over lines in the `τ`-window is bounded independently of the field size and is
small (e.g. `3` and `6` at `w = 2`, `s = 0,1`), while at `w = 1` (exactly at capacity) it grows
with the field up to the number of windows `C(n,t)` — so any true `F` must degrade as `w → 1`,
and the presence of `w − s` in the denominator of §3 is the right shape.
