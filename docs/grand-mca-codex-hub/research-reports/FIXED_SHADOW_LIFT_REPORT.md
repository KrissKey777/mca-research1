# Grand MCA — projective syndrome directions, the chart question, and the fixed-shadow second factor

**Everything asserted here as a theorem is machine-checked, `sorry`-free, and uses only
`propext`, `Classical.choice`, `Quot.sound`.**  New Lean:

* `RequestProject/Root/CodingTheory/ProjectiveSyndromeDirection.lean` — the basis-free local
  syndrome map `Λ_S`, the projective label, the zero branch, the same/distinct-label laws, the
  descent, and the new counting terminal.
* `RequestProject/Root/CodingTheory/FixedShadowLift.lean` — the shortened dual `Q_S`, the kernel
  shadow `K_S`, and the fixed-shadow lift theorem with its star/clique classification.

Notation as in the repository: `D` the evaluation domain, `n = |D|`, `k` the dimension, `e` the
radius, `IsCloseOn k S f` ("`f` agrees with a codeword of degree `< k` on the window `S`"),
`LineCloseOn`, `IsBad k e f₀ f₁ γ`, `badSet`.  An **official bad window** for `γ` is a window
`S` with `|D| ≤ |S| + e`, `IsCloseOn k S (f₀ + γ f₁)` and `¬ LineCloseOn k S f₀ f₁`.

---

## Scope note (read first)

The names `Rank2ExactSupportLocus`, `Rank2QuotientCertificate`, `RankOneRigidity`, the
three-chart engine `3 L_max² ≤ B*` with `L_max = 302754426`, and the deployed row `e = 978944`
**do not exist anywhere in this repository** (they are also absent from the earlier
`GRAND_MCA_GAP_ANSWER.md`, which already recorded that the mapping to them was made at the level
of statements only).  What *does* exist here and is used below:
`card_badSet_le_of_semilinear` (`SemilinearPlaneDescent.lean`), `FrobeniusOrbitBudget.lean`,
`ShorteningMCA.lean`, `CorrelatedAgreementRefined.lean`, `SyndromeLineIncidence.lean`,
`HigherDividedDifferences.lean`.  Every integration answer below is therefore given against
the objects that are actually present; the adapter to the external Rank2 layer is stated as a
precise interface, not claimed as proved.

---

# A. Required output — FIXED-SHADOW LIFT STRUCTURE

## 1. HIGHERDD–SYNDROME FACTORIZATION

Two descriptions of the same object, both formalised, and they agree.

*Functional form.*  `hddFun j S : (D → F) →ₗ F`, `u ↦ hdd_j(S,u)` (the `j`-th coefficient of the
Lagrange interpolant of `u` on `S`); the **local dual space**
`Q_S = localDual k S = span{hddFun j S : j ≥ k}`; the **local syndrome map**

    Λ_S = localSyndrome k S f₀ f₁ : Q_S →ₗ F²,  q ↦ (q f₀, q f₁).

*Vector form.*  `Q_S = rsDualOn k S = {μ : D → F | supp μ ⊆ S, ⟨μ,p⟩ = 0 ∀ deg p < k}` (the
shortened dual of `RS_k(D)`), `Λ = synMap f₀ f₁ : μ ↦ (⟨μ,f₀⟩, ⟨μ,f₁⟩)`.

The factorization identity linking them is `sum_hddVec_mul`:

    ⟨hddVec j S, u⟩ = hdd_j(S, u),      hddVec j S ∈ rsDualOn k S for j ≥ k
                                        (`hddVec_mem_rsDualOn`, needs k ≤ |S|),

with `hddVec j S x = [x ∈ S] · coeff_j (Lagrange basis polynomial of x on S)`.  So the columns
of the HigherDD matrix `M_S = (hdd_j(S,f₀); hdd_j(S,f₁))_{j≥k}` are exactly the `Λ`-images of the
canonical generators of the shortened dual: `M_S` **is** `Λ|_{Q_S}` written in the
divided-difference basis.  This is the canonical basis-free language of the lift problem.

## 2. FIXED-SHADOW NORMAL FORM

`K_S = kernelShadow k S f₀ f₁ = Q_S ⊓ ker Λ`.  On a bad window `Λ|_{Q_S}` has rank one
(`synMap_apply_of_isCloseOn`: `Λ μ = ⟨μ,f₁⟩ · (−γ_S, 1)` for all `μ ∈ Q_S`), so `K_S` is a
**hyperplane of `Q_S`**; formally, nothing sits strictly between them
(`eq_of_between_kernelShadow`).

Normal form for two windows with `K_S = K_T = K_0` and `γ_S ≠ γ_T`:

    Q_{S∩T} = Q_S ⊓ Q_T = K_0        (`rsDualOn_inter` + the distinct-label law)

i.e. **the two lifts intersect exactly in the shadow, and that intersection is again a
shortened dual — the one of the window `S ∩ T`.**  The distinguishing parameter is therefore
*combinatorial*: `Q_S = Q_{S∩T} ⊕ ⟨λ_S⟩` where `λ_S` is any dual vector supported in `S` but not
in `S ∩ T`; equivalently, by strict monotonicity of `A ↦ Q_A` (`exists_mem_rsDualOn_not_mem`),
the lift is pinned by the *single extra evaluation point* of `S`.

## 3. LIFT PARAMETER

The lift parameter is that extra point.  Formally proved
(`card_inter_add_one_eq_of_kernelShadow_eq`): if `k + 2 ≤ |S|`, `γ_S ≠ γ_T`, `K_S = K_T`, then

    |S ∩ T| = |S| − 1     (and, symmetrically, |S| = |T|, `card_eq_of_kernelShadow_eq`).

So the windows over one shadow are pairwise **Johnson-adjacent**: `S = (S∩T) ∪ {a}`,
`T = (S∩T) ∪ {b}`.  The lift is the choice of `a`.

The hypothesis `k + 2 ≤ |S|` (absolute capacity gap `≥ 2`) is genuinely needed: at gap one,
`|S| = k+1`, the shortened dual is one-dimensional and the shadow is `0` for *every* bad window,
so all `C(n,k+1)` windows of the extremal pencil `(X^{k+1}, X^k)` share one shadow.  (The
`C(n,k+1)` extremal count is the one recorded in `HigherDividedDifferences.lean`; the
one-dimensionality remark itself is not formalised.)

## 4. LIFT–DIRECTION FORMULA

`Λ μ = ⟨μ,f₁⟩ · (−γ_S, 1)` for every `μ ∈ Q_S`, so

    ℓ(S) = im Λ_S = F·(−γ_S, 1) = [−γ_S : 1],

and `ℓ` is **injective in the challenge** (`span_dir_eq_iff`, `syndromeLabel_injective`), while a
window determines its challenge (`eq_of_isBad_window`).  Hence *distinct lifts of a fixed shadow
carry distinct projective directions and conversely*: over a fixed `K_0`,

    #{lifts} = #{directions} = #{challenges}.

The fibre law of §3 of the earlier mission is therefore exact, with no residual multiplicity.

## 5. RS-SPECIFIC RESTRICTIONS

Precisely the three that the proof consumes, all RS/Vandermonde facts, none of them generic
projective counting:

1. **Shortening is intersection**: `Q_{S∩T} = Q_S ⊓ Q_T` (`rsDualOn_inter`).
2. **Strict growth**: for `b ∈ B ∖ A` and `k + 1 ≤ |B|` there is `μ ∈ Q_B ∖ Q_A`, produced
   explicitly as the top divided-difference vector of a `(k+1)`-subset of `B` containing `b`
   — its `b`-coordinate is the leading coefficient of a Lagrange basis polynomial, nonzero
   because the evaluation points are distinct (`hddVec_ne_zero_at`).  This is the MDS/Vandermonde
   input.
3. **Interpolation duality**: `¬ IsCloseOn k S f` produces an explicit `μ ∈ Q_S` with
   `⟨μ,f⟩ ≠ 0` (`exists_mem_rsDualOn_sum_ne_zero`), again through `hddVec`.

## 6. FIXED-SHADOW LIFT BOUND

`star_or_clique_of_pairwise_inter` (a formalised classification of families of `m`-sets meeting
pairwise in `m−1` points: either a common `(m−1)`-core, or containment in a common `(m+1)`-set)
turns §3 into the bound `card_lifts_le_of_kernelShadow_eq`:

> Let `W` be challenges witnessed by official bad windows `win γ` with `|D| ≤ |win γ| + e`,
> `k + 2 ≤ |win γ|`, all with the **same** kernel shadow.  Then
>
>     |W| ≤ e + 1        (star branch: the windows share a core and differ by one point)
>   or
>     ∃ U with win γ ⊆ U for all γ, and |W| ≤ |U|   (clique branch: win γ = U ∖ {y_γ}).

So `L(K_0) ≤ e + 1` unless the whole family is a *co-point family* inside one set `U`; in the
clique branch every window is `U` minus a single point, which is itself a complete structural
description (and gives `|W| ≤ |U| ≤ n`).  In the deployed regime the clique branch is not the
binding one, because §A.7 below caps `#Bad` globally by `2e`.

## 7. RANK2 COROLLARY STATUS

**NO DIRECT IDENTIFICATION** is possible inside this repository: there is no
`Rank2ExactSupportLocus` / `Rank2QuotientCertificate` object here (see the scope note).  What is
available is the exact adapter interface, and it is a one-line one:

    Φ(S) := ℓ(S) = [−γ_S : 1] ∈ PG(1,F) = ℙ(F²),  Φ(S) = ℙ(im Λ_S) = Ψ(M_S)

with `Ψ` the universal algebraic map "column space of the `2 × c` HigherDD matrix"
(`range_localSyndrome_eq_submodule_label`).  `Φ` preserves the official support (it is defined
*from* `S` through `Q_S`, no surrogate), it is computed from official data only, and its fibres
are single challenges.  If the external Rank2 point is the projectivised image of the same
rank-one local map, the adapter is the identity; if it is `[1 : γ]` or `[γ : 1]`, it is the fixed
`PGL₂` transform `[x:y] ↦ [−y:x]` resp. `[x:y] ↦ [−x:y]`.  Which of the three holds cannot be
decided here without the external definition — that is the *only* missing input for the bridge.

Two facts make the bridge cheap once the definition is supplied:

* **all labels lie in one affine chart**: `syndromeLabel_ne_infty` — `[1:0]` is never a label,
  so a three-chart cover is not needed for the label family: a single chart `{[x:1]}` carries
  all of `L(U)`;
* **the chart-fibre requirement `|Φ^{-1}(x)| ≤ 1` is already met**: `Φ` is injective on
  challenges (`range_eq_iff_challenge_eq`), hence `|L(U)| = #Bad` (`card_labelSet`).

## 8. EXCEPTIONAL STRUCTURAL CLASS

Exactly two, and both are structural rather than cardinality-driven:

* **gap-one class** (`|S| = k+1`): shadows are trivial, the lift bound is void, and this class
  really occurs (extremal pencil, `C(n,k+1)` challenges);
* **clique class** of §6: all windows are `U ∖ {point}` for one fixed `U`.

No semilinear/Frobenius structure is invoked, and none is needed: the analysis never used
`|L|` large as a hypothesis, only the syndrome relations.

## 9. SINGLE MISSING THEOREM

> **Shadow-count theorem.**  A bound on the number of *distinct* kernel shadows realised by the
> official bad windows of one line, i.e. on `#{K_S : S ∈ BadSupportFamily}`.

Everything else in the product `#Bad ≤ #{shadows} · max_K #{lifts over K}` is now proved: the
second factor is §6, the fibre law is exact (§4), and the descent/finite-cost terminal is §A.10.
(The other agent's mandate is precisely this first factor.)

## 10. SHORTEST ROUTE FROM FIXED SHADOW TO GRAND MCA

1. `#Bad ≤ #{shadows} · L(K_0)` with `L(K_0) ≤ e + 1` (star) or the clique description — §6.
2. If two challenges are bad at all, the pair descends: one codeword pair explains `(f₀,f₁)` on
   `≥ n − 2e` positions (`exists_global_pair_of_two_bad`) and then *every* bad challenge is
   explained by that same pair (`agreement_global_pair_of_isBad`).
3. Counting the points outside the common agreement set gives the new terminal

       #Bad ≤ max (2e) 1        whenever k + 3e ≤ n   (`card_badSet_le_two_mul_of_third`),
       ε_mca ≤ 2e/|F|           for e ≥ 1             (`epsMCA_le_two_mul_of_third`),

   improving the repository's `2e + 1` (`CorrelatedAgreementRefined.card_badSet_le_third`) and
   obtained from **two** distinct labels instead of `2e + 2` close points on the line.
4. Grand MCA in the regime `k + 3e ≤ n` is then this corollary; outside it, the remaining task is
   the shadow-count theorem of §9.

---

# B. Earlier mission — PROJECTIVE SYNDROME DIRECTION (answers to its ten headings)

1. **PROJECTIVE DIRECTION DEFINITION.**  `ℓ(S) = ℙ(im Λ_S)` with `Λ_S : Q_S → F²` basis-free
   (`localSyndrome`); the zero case is separated by `localSyndrome_eq_zero_iff`.  Invariance
   under change of basis of `Q_S` is automatic (the image of a linear map does not depend on a
   basis).  Under a `GL₂` reparametrisation of the received line the label transforms by the
   corresponding Möbius map — the `#Bad` side of this is the repository's `isBad_reparam` /
   `card_badSet_reparam_le`.
2. **LABEL–CHALLENGE FORMULA.**  `ℓ(S) = [−γ_S : 1]`, proved
   (`range_localSyndrome_eq_of_isBadWindow`).  Dually `(1, γ_S)` spans the annihilator of
   `im Λ_S`; badness is exactly `Λ_S ≠ 0` together with `⟨(1,γ), im Λ_S⟩ = 0`
   (`isBadWindow_iff_pairing_eq_zero`).  The map is injective, so `#Bad = |L|` (`card_labelSet`).
3. **ZERO-MAP BRANCH.**  Closed completely: `Λ_S = 0 ⟺ LineCloseOn k S f₀ f₁`, which contradicts
   official noncontainment; so the branch is **impossible** on official bad supports
   (`localSyndrome_ne_zero_of_isBadWindow`).
4. **SAME-LABEL FIBRE.**  `ℓ(S) = ℓ(T) ⟺ γ_S = γ_T` (`range_eq_iff_challenge_eq`).  Combined with
   "one window has one challenge", the label map is a bijection onto the bad set.
5. **DISTINCT-LABEL RANK LAW.**  Not a raw `|S ∩ T|` estimate: `ℓ(S) ≠ ℓ(T)` forces
   `Λ_{S∩T} = 0` (`localSyndrome_inter_eq_zero_of_challenge_ne`), i.e. `Q_S ⊓ Q_T ⊆ ker Λ`, and
   quantitatively a window of co-size `≤ 2e` on which the whole line is explained
   (`exists_lineCloseOn_of_two_bad`).  Rank one + rank one with distinct images ⇒ rank zero one
   level down; with a fixed shadow this is exactly Johnson adjacency (§A.3).
6. **EXACT RELATION TO `Rank2ExactSupportLocus`.**  `NO DIRECT IDENTIFICATION` inside this
   repository (object absent); the adapter interface and the two candidate `PGL₂` normalisations
   are in §A.7.
7. **THREE-CHART CONSEQUENCE.**  A single chart suffices: no label is `[1:0]`
   (`syndromeLabel_ne_infty`), and `|L ∩ chart| = |L| = #Bad ≤ max(2e,1)` in the regime
   `k + 3e ≤ n`.  Whether that meets an external `L_max` threshold cannot be checked here: the
   deployed row (`e = 978944`, `L_max = 302754426`, `B*`) is not present in this repository.  For
   the record, `k + 3e ≤ n` with `n = 2^20` forces `e < 349526`, so an `e` of that size lies
   outside the regime of the terminal proved here and would need either the shadow-count theorem
   or the folded/list-decoding routes already in the repository.
8. **LARGE-IMAGE STRUCTURE.**  Nothing is inferred from cardinality.  What large `|L|` forces is
   the *descent* of §A.10 (a global codeword pair) and, over a fixed shadow, the star/clique
   dichotomy.  No `F_p`-linear-set or Frobenius structure is claimed.
9. **SINGLE MISSING MATHEMATICAL THEOREM.**  The shadow-count theorem (§A.9).
10. **SHORTEST PATH TO GRAND MCA.**  §A.10.

---

# C. Deployed-safe question at `e = 978944`

Cannot be answered inside this repository, and no claim is made: the parameters of that row
(`n`, `k`, `B*`, the chart constants) are not present in any file here.  What is certain is the
conditional shape: the projective-label layer contributes **no** multiplicity of its own
(`|L| = #Bad`), so any deployed bound reduces to a bound on `#Bad`, for which this session
supplies `#Bad ≤ max(2e,1)` in the regime `k + 3e ≤ n`, and the shadow × lift factorisation
elsewhere.
