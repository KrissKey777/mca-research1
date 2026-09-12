# JACKPOT 2w DEPENDENCY GATE — verdict

## OUTCOME

```
RESIDUAL_DEPENDENCY_CLASSIFIED
```

A challenge-compatible dependency **can** exist among official residual split locators.
The first minimal official obstruction has exactly **three** challenges, its exact identity is a
divided-difference (collinearity) relation, and the exceptional predicate is stated below.
The missing implication is therefore **not** available as a structural consequence of the official
residual hypotheses, and

```
#ResidualBad ≤ 2w      is NOT proved,
#Bad ≤ 3w = 208896     is NOT proved.
```

Frozen data (unchanged, replayed only, `REPORTED_NOT_REPLAYED` where indicated):
`n = 2097152, k = 1048576, e = 978944, w = 69632, B* = 274980728111395087`.

New Lean modules (purely additive, nothing existing was modified):

* `RequestProject/Root/CodingTheory/ResidualDependencyGate.lean`
* `RequestProject/ResidualDependencyGateAxiomAudit.lean` — `#print axioms` for all 11 load-bearing
  declarations; every one prints `[propext, Classical.choice, Quot.sound]`. No `sorry`, no
  `native_decide`, no new axiom.

---

## STEP 1 — the existing `2w` theorem, reconstructed exactly

Source: `Root.CodingTheory.SplitPencil.card_le_two_mul_width_of_regular`
(`RequestProject/Root/CodingTheory/SplitLocatorPencilIncidence.lean`, §7 "Route A"):

```lean
theorem card_le_two_mul_width_of_regular {ι : Type u} [Fintype ι] {γ : ι → F}
    {v : ι → (Fin w → F)}
    (hreg : ∀ c : ι → F, (∑ i, c i • v i = 0) → (∑ i, (c i * γ i) • v i = 0) → ∀ i, c i = 0) :
    Fintype.card ι ≤ 2 * w
```

1. **Quantified objects.** A field `F`, a width `w : ℕ`, a *finite index type* `ι`, a family of
   scalars `γ : ι → F`, a family of vectors `v : ι → (Fin w → F)`. Nothing else.
2. **Challenge-compatible dependency** (the negation of `hreg`): a family `c : ι → F`, not
   identically zero, with
   `∑ᵢ cᵢ · vᵢ = 0` **and** `∑ᵢ (cᵢ γᵢ) · vᵢ = 0`.
   Equivalently (proved here, `dependency_iff_common_kernel`): with `vᵢ = B Qᵢ` and
   `(A + γᵢ B) Qᵢ = 0`, the single polynomial `∑ᵢ cᵢ Qᵢ` lies in the **common kernel**
   `ker A ∩ ker B` of the pencil.
3. **Family it applies to.** *Any* family `(γᵢ, vᵢ)`. It is a pure linear-algebra statement:
   splitness, monicity, `Q ∣ Xⁿ − 1`, the domain `D`, the Hankel structure and the words
   `f₀, f₁` do **not** occur in its statement. The deployed link is only through the intended
   reading `vᵢ = B Q_{γᵢ} = synRestrict w e f₁ Q_{γᵢ}` and `A Q_{γᵢ} = −γᵢ vᵢ`.
4. **Does it count distinct finite `γ`?** No. It counts `Fintype.card ι`, i.e. *index* elements.
   Injectivity of `γ` is not a hypothesis (it is a consequence of `hreg` together with
   `joint_pair_independent` only in the sense that repeated `γ` with the same `v` immediately
   violate `hreg`). Turning `Fintype.card ι ≤ 2w` into `#Γ_residual ≤ 2w` for the official
   **set** of challenges needs an adapter (a choice of locator per challenge and a
   `Set.ncard`/`Fintype` transfer) that does **not** exist in the source: the deployed file
   contains only the abstract card bound plus the arithmetic
   `deployed_two_width_below_target : 2 * 69632 = 139264 ≤ B*`.
   Status of "`#ResidualBad ≤ 2w` under the dependency-free hypothesis": `REPORTED_NOT_REPLAYED`
   as a statement about the official set; `PROVED` only in the abstract index form above.
5. **May supports or locators repeat?** The theorem allows arbitrary repetition: `v` need not be
   injective, `γ` need not be injective, and no support/locator condition appears. Under `hreg`
   repetition of an index pair `(γᵢ, vᵢ)` is excluded automatically.
6. **Nondegeneracy.** None is assumed *explicitly*; `hreg` implies `vᵢ ≠ 0` for every `i` (take
   `c` the indicator of `i`). The official nondegeneracy `LocatorNondeg w f₁ Q` (i.e. `B Q ≠ 0`)
   is exactly this consequence, and it is what the deployed adapter supplies.
7. **Divided-difference identity.** `joint_divided_difference`: if
   `∑ᵢ cᵢ (A Qᵢ, B Qᵢ) = 0` then for every base point `j`
   `∑ᵢ cᵢ (γᵢ − γⱼ) · vᵢ = 0` — a dependency of the `f₁`-syndrome vectors, one term shorter.
8. **Conclusion.** `Fintype.card ι ≤ 2 * w`, deployed `2w = 139264 ≤ B*`.

**Applicability verdict.** The theorem *does* apply formally to the official residual object (its
hypotheses are strictly weaker than the official ones, except for `hreg`, which is exactly the
missing implication under test). So the outcome is not `INCIDENCE_HYPOTHESIS_MISMATCH`; the entire
gap sits in `hreg`.

---

## STEP 2 — the official residual object, frozen

Work with challenges `γ` such that

* `rk (A + γB) = w` (no rank drop — the residual branch of
  `PencilRank.ncard_le_drop_add_residual` / `deployed_badSet_decomposition`);
* there is a **monic** degree-`e` locator `Q_γ` in `ker (A + γB)`;
* `Q_γ = Q_E = ∏_{x∈E}(X − x)` with `E ⊆ D`, `|E| = e`, hence `Q_γ ∣ Xⁿ − 1` because `D = μ_n`;
* official nondegeneracy `B Q_γ ≠ 0` (`LocatorNondeg w f₁ Q_γ`).

Because `D = μ_n` and `p ∤ n`, splitness, distinctness of roots and `q₀ ≠ 0` are *not* independent
filters; they are consequences of `Q ∣ Xⁿ − 1` and are used as such. Monicity `q_e = 1` is kept
separate (it is the functional `topCoeffLin e`, `topCoeffLin_locVec`).

Orientation, stated explicitly and unchanged from the source: the pencil acts on the **monic**
locator `Q_E(X) = ∏_{x∈E}(X − x)`; the reciprocal `Λ_E(X) = ∏(1 − xX) = Xᵉ Q_E(1/X)` is used
nowhere. No reversal map is applied anywhere in the new module.

---

## STEP 3 — cheap falsification: the smallest exact official model

`Root.CodingTheory.ResidualDependency.official_residual_dependency` (`PROVED`,
`EXHAUSTIVE_SMALL_MODEL` for the parameter row).

* **Field and domain.** Any field `F` and any official domain `D ⊆ F` with `|D| ≥ 3`; for
  non-vacuity `mu_three_zmod_seven` exhibits `F = ZMod 7`, `D = μ₃ = {1,2,4}`, `n = 3`,
  `char = 7 ∤ 3`, `0 ∉ D` (checked by `decide`).
* **Parameters.** `n = |D|`, `e = 1`, `k = |D| − 2`, hence the official width
  `w = |D| − k − e = 1`, `2w = 2`.
* **Exact syndrome pencil.** The official one: `A = synRestrict 1 1 f₀`, `B = synRestrict 1 1 f₁`,
  built from the official `gsynd`, with
  `f₀ = evalWord c` (global syndrome functional `u ↦ u(c)`) and
  `f₁ = diffWord c d` (`u ↦ u(c) − u(d)`), `c ≠ d ∈ D`.
  These are honest words in `↥D → F`, not an arbitrary linear pencil.
* **Exact split locators.** `Q_i = Q_{E_i}`, `E_i = {a_i}`, `a_i ∈ D` three distinct points;
  monic of degree `e = 1`, split over `D`, distinct roots, `Q_i ∣ X^{|D|} − 1`, `Q_i(0) ≠ 0`.
* **Distinct finite challenges.** `γ_i = (a_i − c)/(c − d)`, pairwise distinct (proved).
* **Official nondegeneracy.** `B Q_i = (c − d) ≠ 0` for every `i` (proved).
* **Rank-drop or residual?** Residual: `rk (A + γ_i B) = 1 = w` and
  `rk ((A + γ_i B)|_{ker topCoeffLin e}) = 1` for every `i` (both proved, witness `Q = 1`),
  so none of the three is a rank-drop challenge and none is killed by the monic hyperplane.
* **Exact dependency identity.** With `v_i = B Q_i = (c − d)` (a nonzero vector of `F¹`),
  `c_i = (γ_{i+1} − γ_{i+2})/(c − d)` gives `c ≠ 0`,
  `∑ᵢ cᵢ vᵢ = 0` and `∑ᵢ (cᵢ γᵢ) vᵢ = 0`.

This model satisfies **every** hypothesis under which the `2w` theorem is invoked — official
pencil, official challenge set membership, official split locators, official nondegeneracy,
residual (full-rank) branch — and it refutes `hreg` with three challenges against `2w = 2`.
It is *not* the deployed parameter row, so the label is `EXHAUSTIVE_SMALL_MODEL`, not
`RESIDUAL_DEPENDENCY_COUNTEREXAMPLE`: it proves that the missing implication cannot be derived
from the official residual hypotheses alone, and can only hold, if at all, through the specific
deployed row.

---

## STEP 4 — the missing implication

> official residual split locators ⇒ no challenge-compatible dependency

**FALSE as a structural implication** (`PROVED`, via Step 3). The smallest obstruction:

* **Minimum number of challenges: 3.** Two challenges never suffice:
  `two_term_dependency_trivial` (from `joint_pair_independent`) — distinct `γ ≠ δ` with
  `v, v' ≠ 0` admit no nonzero pair `(c, c')`.
* **Exact coefficient/dependency identity.** For three challenges with all `cᵢ ≠ 0`,
  the divided difference at base point `2` gives
  `c₀(γ₀ − γ₂)·v₀ + c₁(γ₁ − γ₂)·v₁ = 0`, i.e. **`v₀ ∥ v₁`**
  (`collinear_of_three_dependency`: `v₀ = μ v₁` with `μ = −c₁(γ₁−γ₂)/(c₀(γ₀−γ₂)) ≠ 0`).
  Conversely (`dependency_of_collinear`) if `vᵢ = λᵢ u` with `λᵢ ≠ 0` and the `γᵢ` distinct, then
  `cᵢ = (γ_{i+1} − γ_{i+2})/λᵢ` is a nonzero dependency, because
  `∑ᵢ (γ_{i+1} − γ_{i+2}) = 0` and `∑ᵢ (γ_{i+1} − γ_{i+2}) γᵢ = 0`.
  So for three challenges: **dependency ⇔ the three syndrome vectors are pairwise collinear.**
* **Exact relation among the `Qᵢ` / root sets.** By `dependency_iff_common_kernel`, a dependency
  is precisely `∑ᵢ cᵢ Qᵢ ∈ ker A ∩ ker B`. No relation among the *root sets* `Eᵢ` is forced:
  in the model above the three root sets are pairwise disjoint singletons. The relation is on the
  images of the locators modulo the common kernel, whose codimension is at most `2w`, while
  `dim ker A ∩ ker B ≥ e + 1 − 2w = 839681` at the deployed row.
* **Official nondegeneracy is preserved.** Every challenge in the obstruction keeps `B Qᵢ ≠ 0`,
  full pencil rank `w`, and a monic split locator dividing `Xⁿ − 1`.
* **Deployed or toy-only?** Toy-only as an instance (`EXHAUSTIVE_SMALL_MODEL`); the *implication*
  it refutes was a structural one, so the refutation is decisive for the implication, and
  `CONDITIONAL` for the deployed row: nothing here shows that the deployed pair `(f₀, f₁)` has
  three residual challenges with collinear `w = 69632`-dimensional syndrome vectors, and nothing
  here shows it does not.

---

## STEP 5 — limited salvage check

Split the residual challenge family by

```
Γ_residual = Γ_dependency-free ∪ Γ_exceptional
```

with the **exact exceptional predicate**

```
γ ∈ Γ_exceptional   :⇔   v_γ ∈ span_F { v_δ : δ ∈ Γ_residual, δ ≠ γ },
        where v_γ = B Q_γ = synRestrict w e f₁ Q_γ.
```

On the complement the syndrome vectors are linearly independent, hence
(`dependency_free_subfamily_card_le`, `PROVED`)

```
#Γ_dependency-free ≤ w = 69632 ≤ 2w,
```

and `hreg` holds there trivially (a dependency needs `∑ cᵢ vᵢ = 0`). This is the only salvage that
follows immediately from an already proved statement. **No bound on `Γ_exceptional` is claimed**;
by Step 4 the exceptional set is exactly where the three-term collinear obstruction lives, and
bounding it is outside this mission.

---

## HARD STOP

Not entered, per the mission rule: general dependency classification; Fourier/Plücker/resultant/
Hankel programmes; generic annihilator bounds; support counting; fibre-size bounds; the `m = 8`
branch; constant optimisation; a new residual nonlinear theory.

## Claim labels

| Claim | Label |
| --- | --- |
| Exact restatement of `card_le_two_mul_width_of_regular` (Step 1, items 1–8) | `PROVED` (source replay) |
| `#ResidualBad ≤ 2w` for the official *set* under `hreg` (adapter from index type to `Set.ncard`) | `REPORTED_NOT_REPLAYED` |
| `#RankDrop ≤ w` (`ncard_rank_drop_le_width`, `deployed_rank_drop_le`) | `PROVED` (existing) |
| Dependency ⇔ `∑ cᵢ Qᵢ ∈ ker A ∩ ker B` | `PROVED` |
| No two-challenge dependency | `PROVED` |
| Three-term dependency ⇔ collinear syndrome vectors (both directions) | `PROVED` |
| Exact official residual model with a dependency, `w = 1`, three residual challenges | `PROVED`, `EXHAUSTIVE_SMALL_MODEL` |
| `μ₃ = {1,2,4} ⊂ ZMod 7` is an official root-of-unity domain, `0 ∉ D`, `3 ≤ |D|` | `PROVED` (`decide`) |
| `#Γ_dependency-free ≤ w` | `PROVED` |
| Whether the deployed row itself admits a residual dependency | open, `CONDITIONAL` |
| `#ResidualBad ≤ 2w`, `#Bad ≤ 3w = 208896 < B*` at the deployed row | **not proved** |
