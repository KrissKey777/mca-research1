# The maximal correlated agreement `τ`: the sharp invariant of the second-moment mechanism, and the exact residual gate

Module: `RequestProject/Root/CodingTheory/MaximalCorrelatedAgreement.lean`
Axiom audit: `RequestProject/MaximalCorrelatedAgreementAxiomAudit.lean` (43 declarations; only
`propext`, `Classical.choice`, `Quot.sound`). Sorry-free; the whole project still builds.

## 1. What was asked and what is delivered

The task was to find the strongest *general* theorem turning a large official bad-challenge
family into a **quantitative** global bound, using a canonical structural invariant rather than
raw supports, and — failing that — to isolate the single precise obstruction.

Both halves are delivered.

* A **master counting theorem** for arbitrary linear codes over arbitrary fields and arbitrary
  alphabet modules, with an explicit charging law
  `#Bad · (t² − N·τ) ≤ N·t`, where `τ` is a canonical invariant of the residual plane.
* An identification theorem showing that `τ` **is** the correlated-agreement invariant: the MCA
  conclusion at radius `e` is literally `|D| − e ≤ τ`.
* Consequently a master reduction: *every* line either satisfies the MCA conclusion outright or
  has `k ≤ τ < |D| − e`. At the deployed Grand-MCA point this window is
  `1048576 ≤ τ < 1118208`, of width `69632` — exactly the capacity gap.
* And a machine-checked proof that the second-moment branch is **empty** inside that window, so
  the residual gate is not a Lean-engineering gap but the beyond-Johnson gap itself.

## 2. The invariant

For a line `(f₀,f₁)` and a code `C`,

    τ(f₀,f₁) = max { |{x : f₀ x = q₀ x ∧ f₁ x = q₁ x}| : q₀, q₁ ∈ C }.

`mcaTau` is the general form (arbitrary `C ⊆ (Ω → M)`), `rsTau` the Reed–Solomon form. It is a
canonical invariant of the *residual plane*:

* `mcaTau_add_mem` — `τ(f₀ + c₀, f₁ + c₁) = τ(f₀,f₁)` for codewords `c₀,c₁`: only the class of
  the plane `span(f₀,f₁)` modulo `C` matters;
* `mcaTau_swap` — symmetric in the two words;
* `exists_pair_card_eq_rsTau` — the maximum is attained, so `τ` names an actual window.

## 3. The master counting theorem

`card_le_of_pairAgreement_bound`. Let `B` be any finite family of challenges, each carrying a
window `S γ` of size `≥ t` and a codeword `cw γ` with `f₀ x + γ·f₁ x = cw γ x` on `S γ`. If no
pair of codewords correlates with `(f₀,f₁)` on more than `c` positions, then

    #B · (t² − N·c) ≤ N·t ,      N = |Ω| .

The pairwise input is *forced*, not assumed: two witnesses at `γ ≠ γ'` build the codeword pair
`q₁ = (γ − γ')⁻¹·(cw γ − cw γ')`, `q₀ = cw γ − γ·q₁`, which correlates with `(f₀,f₁)` on the whole
of `S γ ∩ S γ'` (`inter_subset_pairAgree`). Substituting `c = τ` gives `card_le_of_mcaTau`; the
Johnson-regime form `#B ≤ N·t/(t² − N·τ)` is `card_le_of_mcaTau_div`.

No noncontainment, distance, rate or window hypothesis is used, and the alphabet may be any
`F`-module, so interleaved and folded codes are covered.

For the project's official Reed–Solomon `badSet` the same statement is
`card_badSet_le_johnson_of_pairBound` (arbitrary bound `c`) and `card_badSet_le_of_rsTau`
(the sharp `c = τ`), with `epsMCA_le_of_rsTau` the `ε_mca` form.

### Relation to the existing far branch

`NearCodewordLineMCA.card_badSet_le_setFamilyJohnson_of_far` is the special case `c = k + e − 1`
(`card_badSet_le_far_of_rsTau_lt`). Its ceiling is `|D|·(k+e−1) < t²`, i.e. `(1−δ)² > ρ + δ`;
the sharp branch's ceiling is `|D|·τ < t²`, and since `k ≤ τ` always (`rsTau_ge_dim`) the best
possible reach is `(1−δ)² > ρ` — the **full Johnson radius**. The gain is real and is exhibited:
at `ρ = 1/2`, `|D| = 2²⁰`, `e = 300000` (`δ ≈ 0.2861`, well past the old ceiling `0.177124`)
`card_badSet_le_rho_half_example` gives `#Bad ≤ 73` for every line with `τ = k`, while
`rho_half_example_old_branch_fails` records that the old branch has nothing to say there.

## 4. `τ` is the correlated-agreement invariant

For an arbitrary linear code this is `le_mcaTau_iff_exists_window` (a window of size `s` on
which one codeword pair explains the whole line exists iff `s ≤ τ`), and combining it with the
counting theorem gives the general dichotomy `correlatedAgreement_or_card_le_of_mcaTau`: either
correlated agreement on a window of size `≥ t`, or `τ < t` together with
`#B·(t² − N·τ) ≤ N·t`.  In the Reed–Solomon setting the same statement is phrased with the
project's `LineCloseOn`:

`exists_lineCloseOn_iff_le_rsTau`: there is a window of size `s` on which the *whole line*
agrees with one codeword line **iff** `s ≤ τ`. (⇐ uses the maximising pair and `line_closure`;
⇒ takes the interpolants at `γ = 0` and `γ = 1` and subtracts.)

So the MCA conclusion at radius `e` is the single inequality `|D| − e ≤ τ`, and

`correlatedAgreement_or_rsTau_window`: **every** line either satisfies the MCA conclusion, or

    k ≤ τ < |D| − e ,

a window of width exactly the capacity gap `|D| − k − e`.

## 5. The deployed audit, and the exact obstruction

Deployed point: `|D| = 2²¹ = 2097152`, `k = 2²⁰` (`ρ = 1/2`), `e = 978944`
(`δ = 0.466796875`), `t = 1118208`, budget `B* ≈ 2⁵⁷·⁹`.

* `deployed_correlatedAgreement_or_window` — either MCA holds, or `1048576 ≤ τ < 1118208`
  (width `69632`, `deployed_window_width`).
* `deployed_johnson_branch_empty` — `t² < |D|·k`: since `k ≤ τ`, the second-moment branch is
  **vacuous** at the deployed point. The failure is by the exact integer deficit
  `|D|·k − t² = 948634124288` (`deployed_johnson_deficit`).
* `deployed_gate` — the pinning branch still gives `#Bad ≤ e + 1 = 978945 ≪ B*` whenever
  `τ ≥ k + e`; but `k + e > t`, so that branch is subsumed by correlated agreement and adds
  nothing inside the window.

**The single precise obstruction.** The whole deployed Grand-MCA gate is now one statement about
one canonical invariant:

> for lines with `k ≤ τ < |D| − e` (equivalently: not correlated-agreeing, but with the trivial
> interpolation agreement `k`), bound `#Bad` by `B*`.

Inside that window every second-moment/Johnson-type argument is provably out of reach:
`johnson_branch_needs_johnson_radius` shows the mechanism needs `|D|·k < t²`, i.e.
`δ < 1 − √ρ = 0.2929`, while the deployed `δ = 0.4668`. This is the same barrier that
`DeployedTargetGap.lean` records for the Guruswami–Sudan chain, now proved for the *sharp*
invariant rather than for a threshold: it is not a lossy constant, it is the mechanism's ceiling.

## 6. Scope and honesty

* Nothing in the existing witness-semantics / `Res` / duality / descent layers was rebuilt; the
  set-family engine `SetFamilyJohnson.card_family_le_of_pairwise_inter`, the two-witness pair
  construction and the pinning branch are reused as they stand.
* No bound on `#Bad` is claimed inside the residual window; the results there are the
  *reduction* and the *impossibility of the second-moment route*, not a bound.
* The `≤ 73` sharpness statement is conditional on `τ = k` for the line in question; `τ` is a
  computable-in-principle invariant of the input pair, not a parameter of the code.
