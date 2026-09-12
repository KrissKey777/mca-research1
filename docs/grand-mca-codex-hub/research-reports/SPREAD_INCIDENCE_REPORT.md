# [INCIDENCE-REDUCTION] — the official MCA witness incidence set, its projection to the challenge, and the colour that controls the fibres

**Files.** `RequestProject/Root/CodingTheory/SpreadIncidence.lean` (theory),
`RequestProject/Root/CodingTheory/SpreadIncidenceWitness.lean` (evaluation on the known
counterexample row), `RequestProject/SpreadIncidenceAxiomAudit.lean` (axiom audit).
Everything is `sorry`-free and uses only `propext`, `Classical.choice`, `Quot.sound`.
Everything is stated against the project's *official* `IsBad / badSet / LineCloseOn`
predicates of `MCA.lean` (Reed–Solomon on an arbitrary evaluation domain `D ⊆ F`).

## 1. What was asked and what is delivered

The mission asked for the *smallest genuinely new structural object* able to control
official MCA beyond the sharp `(σ,B,N)` unique-decoding barrier, with the explicit
suggestion to study the incidence set of official witnesses

```
I_e = {(γ, S, q) : |S| ≥ N − e, (f₀ + γ·f₁)|_S = q|_S, ¬ LineCloseOn S f₀ f₁}
```

and to ask *what intrinsic property of the evaluation domain controls the size and the
fibres of the projection `I_e → γ`*.

That question is now answered completely on the fibre side, and the answer is a **colour,
not a count**:

> Every witness is attached to a pair of codewords `(c₀,c₁)` (its own interpolant together
> with the interpolant of any second witness).  The fibre of `I_e → γ` over such a pair is
> controlled by *one* geometric quantity of that pair — the **deviation-active set**
>
> `A = devActive f₀ f₁ c₀ c₁ = {x ∈ D : f₀ x ≠ c₀ x or f₁ x ≠ c₁ x}` —
>
> through the two inequalities `m ≤ |A|` and `m·(|A| − e) ≤ |A|`, i.e. `m ≤ spreadWeight e |A|`
> and in particular `m ≤ e + 1` **unconditionally**.

The challenge coordinate then disappears from the problem entirely:

```
#Bad  ≤  max 1 ( Σ_{(c₀,c₁) ∈ bigPairs}  spreadWeight e |devActive f₀ f₁ c₀ c₁| )      (R)
```

(`card_badSet_le_sum_spreadWeight`), where `bigPairs` are the pairs of codewords agreeing
with `(f₀,f₁)` on one common set of at least `N − 2e` positions.

## 2. The machine-checked statements

| name | statement |
|---|---|
| `disjoint_devActive_inter_pairAgree` | two different challenges never share an active position |
| `card_badWithPair_le_card_devActive` | `m ≤ |A|` |
| `card_badWithPair_mul_sub_le` | **spread inequality** `m·(|A| − e) ≤ |A|` |
| `card_badWithPair_le_spreadWeight` | `m ≤ spreadWeight e |A|`, `spreadWeight e a = a/(a−e)` for `a > e`, `= a` otherwise |
| `card_badWithPair_le_succ_radius` | `m ≤ e+1`, **no window, no radius bound, no field-size condition** |
| `card_devActive_le_two_mul_of_two_le` | `m ≥ 2 ⇒ |A| ≤ 2e` |
| `mul_pred_card_devActive_le` | `(m−1)·|A| ≤ m·e` (quantitative concentration) |
| `card_badSet_le_sum_spreadWeight` | the reduction (R) |
| `card_badSet_le_two_scale` | `#Bad ≤ max 1 ( (e+1)·#{concentrated pairs, spread < t} + (t/(t−e))·#bigPairs )` |
| `card_devActive_add_ge_of_ne` | distinct pairs: `N ≤ |A| + |A′| + (k−1)` |
| `mul_pred_card_le_of_two_pairs` | `(m−1)(m′−1)N ≤ (m′−1)me + (m−1)m′e + (m−1)(m′−1)(k−1)` |
| `HoleWitness.two_le_card_rsBigPairs_hole` | on the `|D|=8, k=3, e=2` counterexample row the pair invariant is `≥ 2` |

## 3. Why this is not a repackaging of `(σ,B,N)`

* The fibre bound `e+1` holds **at every radius**.  The sharpness theorem of
  `GeneralMCAInvariant`/`GeneralMCAWindowSharp` says that no bound depending only on
  `(σ,B,N)` survives past `σ + 3e < N`; the bound here does survive, because it is *not* a
  bound on `#Bad` in those three numbers — it is a bound on *one fibre*, and the remaining
  information (how many pairs, and how spread out they are) is exactly the part that
  `(σ,B,N)` cannot see.
* The weight is a genuine refinement of the pair count: the coarse corollary
  `#Bad ≤ (e+1)·#bigPairs` (also machine-checked, per line, unconditional) is recovered from
  (R), but (R) charges a pair with a *maximally spread* deviation (`|A| = 2e`) only `2`
  instead of `e+1`.  This is the "colour" the mission asked for: **the challenge count is
  governed by the spread of the deviation, not by the raw support count**.
* Read backwards, (R) plus the concentration theorems say that the *extremal* configurations
  are forced to be super-concentrated: a pair carrying `m` challenges has joint deviation
  `|A| ≤ m·e/(m−1)`, so the maximal multiplicity `e+1` forces `|A| ≤ e+1` — the pairs that
  matter live at *joint* radius `≈ e`, not at the a priori joint radius `2e`.  Any future
  domain-sensitive input therefore only has to control the list of codeword pairs at the
  *small* radius, which is a strictly easier object than the radius-`2e` list.
* The second-order theorem `mul_pred_card_le_of_two_pairs` constrains the whole *profile* of
  the fibres, not one fibre: two distinct pairs cannot both be concentrated, because off
  their deviations they would agree on more than `k−1` positions.  Specialising `m = m′`
  gives `(m−1)(N − k + 1) ≤ 2me`, i.e. a fibre bound of order `(N−k+1)/((N−k+1) − 2e)` in the
  whole unique-decoding range `2e < N − k + 1`, which is far below `e+1` inside it.

## 4. Where the domain enters, and what is *not* claimed

After the reduction, the only surviving quantity is

```
X(D, k, e) = max over lines of  Σ_{p ∈ bigPairs}  spreadWeight e |A_p|,
```

a **spread-weighted count of codeword pairs jointly close to a pair of words** on the
evaluation domain `D`.  This is a property of the domain and not of the MDS matroid,
minimum distance or generalized Hamming weights, all of which coincide for all Reed–Solomon
codes of the same length and dimension; the number of codewords (and pairs) in a ball is
where different evaluation domains genuinely differ.

**Honesty gate.**  This report does *not* claim a machine-checked separation of two concrete
domains with the same `(σ,B,N)` and different `X`, and does not claim any post-Johnson
result for smooth Reed–Solomon.  What is proved is the reduction — the elimination of the
challenge coordinate with an explicit, colour-sensitive fibre law — together with the
concentration theorems that identify *which* pairs can be heavy.  The remaining, and now
isolated, question is purely a question about the evaluation domain and involves no
challenges at all:

> bound the number of pairs of codewords of `RS_k(D)` that agree with a fixed pair of words
> on one common set of `≥ N − 2e` positions, and — for the extremal contributions — of
> `≥ N − (e+1)` positions, for `D` a smooth multiplicative domain.

`HoleWitness.two_le_card_rsBigPairs_hole` shows the reduction is not vacuous and is
quantitatively meaningful on the smallest known failure row: there `#Bad = 4 > e+1 = 3`, and
the reduction turns this into the statement that a *second codeword pair* must exist — the
excess is not a challenge-side phenomenon.

## 5. Relation to earlier project results

* `LineDecodableGeneric.lean` + `LineDecodableAmplification.lean` already gave, for general
  codes, `ε_mca ≤ (a + L·(e+1))/|F|` from line-decodability plus list-decodability, and
  `card_bigAgreePairs_le_one` gives one pair when `4e < d`.  The present file differs in
  three ways: it works per line, it needs no line-decodability, no field-size condition and
  no window, and it replaces the flat factor `e+1` by the spread weight, which is the new
  content.
* `CosetBadFamily.lean` / `UniqueDecodingHoleWitness.lean` supply the failures just past the
  `(σ,B,N)` window; §4's witness theorem re-reads one of them through the reduction.

## 6. The mission instruction, corrected

The original instruction asked for "the smallest genuinely new structural invariant" and at
the same time for "deterministic smooth Reed–Solomon Grand MCA" as the target.  Those two
goals pull in opposite directions: the second is an open list-decoding problem, the first is
achievable now.  The instruction that actually produces progress separates them:

1. **Eliminate the challenge coordinate first.**  Do not look for a new number attached to
   the challenge alphabet; prove a *fibre law* for the projection `I_e → γ` and reduce
   official MCA to a challenge-free quantity.  (Done: §2, unconditional, at every radius.)
2. **Colour the fibre law.**  A reduction that charges every pair the flat `e+1` throws away
   exactly the information the sharpness theorem says is missing; the weight must depend on
   the geometry of the deviation.  (Done: `spreadWeight`, and the concentration theorems
   which show that heavy fibres force joint radius `≈ e` instead of `2e`.)
3. **Only then ask the domain question**, and ask it in the challenge-free form: bound the
   number of codeword pairs jointly close to a pair of words on a *smooth multiplicative*
   evaluation domain.  This is now the single remaining input; no MCA-specific machinery is
   involved any more.
4. **Do not attempt an unconditional improvement of the window.**  The project's own coset
   family already shows the bad set is unbounded one step past `σ + 3e < N`, so every
   post-window theorem must be conditional on a domain quantity.  Any instruction demanding
   an unconditional post-window bound is asking for something false.

Steps 1–2 are complete and machine-checked.  Step 3 is the first honest formulation of what
"Grand MCA for smooth RS" requires, and it is a statement about the evaluation domain alone.
