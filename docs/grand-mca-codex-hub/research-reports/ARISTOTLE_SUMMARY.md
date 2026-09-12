# Summary of changes for run 9004be44-a678-4d36-9a20-cba58ab6ba9f
STATUS: CONDITIONAL — items 1, 3, 4 of the gate are proved; item 2 is the first failed item, and the inference it relied on is formally refuted.

Work is purely additive (no changes to submission roots, toolchain, lakefile or manifest): new files `RequestProject/Root/CodingTheory/HeavyFibreInvariant.lean`, `RequestProject/HeavyFibreInvariantAxiomAudit.lean`, and the write-up `HEAVY_FIBRE_INVARIANT_GATE_REPORT.md` (full statements, hypotheses, and verdict). All interfaces were audited against the actual source (`badSet`, `erasureSel`, `erasureSel_spec`, `qPoly`, `twistLoc`), not against report prose.

Definitions: `heavyFibre k e f₀ f₁ x` = the official bad challenges whose exact-size official erasure witness contains the fixed point x (equivalently whose locator splits as Q_γ = (X−x)·R_γ); `locInv` = I_x γ := R_γ(0), valued in the deployed field F, normalized as the constant term of the monic cofactor R_γ, i.e. the signed product of the erased points other than x, with Q_γ(0) = −x·I_x γ.

Proved: (1) `heavyFibre_domain` — every γ in G_x lies in the stated domain: the split holds, R_γ is monic of degree e−1, R_γ divides (X^n−1)/(X−x), and I_x γ is a nonzero n-th root of unity, so Y_x = μ_n with at most n = 2097152 values. (3) The bounded-root/fibre lemma with its exact polynomial `annihPoly n u v = u^n − v^n`: `annihPoly_deployed_natDegree_le` gives degree ≤ 2097152·69632 = 146028888064, plus `annihPoly_ne_zero_of_nonconstant`, `subset_annihPoly_roots`, `card_le_of_presentation` — the count is a root count of that explicit polynomial, never an inference from rational-map degree. (4) `deployed_heavy_margin : 146028888064 < 274980728111395087` and `heavyFibre_card_le_Bstar`.

Item 2: only its denominator half is unconditional (`presentation_denominator_ne_zero`, plus `presentation_numerator_ne_zero`). The degree-≤ w claim is not derivable: `no_bounded_presentation_countermodel` is an exact countermodel (field with 3 elements, n = 2, w = 1, 3 challenges) of a μ_n-valued invariant admitting no coprime presentation of degree ≤ w, so item 2 does not follow from item 1; and `deployed_presentation_self_defeat` shows that whenever |G_x| > 146028888064 every coprime degree-≤ 69632 presentation is constant, so the nonconstant branch is unavailable exactly where it is needed. This countermodel refutes the inference pattern, not the deployed configuration; no official deployed countermodel is claimed.

Non-globality is also recorded as theorems: `badSet_subset_biUnion_heavyFibre`, `badSet_card_le_of_uniform_heavyFibre`, and `heavyFibre_bound_not_global` (2097152·146028888064 > B*).

Axiom audit: all 24 load-bearing declarations report exactly [propext, Classical.choice, Quot.sound]; no sorry, no new axiom, no native_decide. Build commands: `lake build RequestProject.Root.CodingTheory.HeavyFibreInvariant` and `lake build RequestProject.HeavyFibreInvariantAxiomAudit`, both clean and warning-free in the new files.

The result does not prove M_C(1118208) ≤ B* and does not give an official counterexample; it leaves the same gate open with its failure point located. Next gate (one only): decide item 2 in its surviving form — from source-level hypotheses at the frozen row, determine whether I_x can be nonconstant on a heavy fibre of size greater than 146028888064 while admitting a coprime degree-≤ 69632 presentation, or prove that no such presentation exists. No second invariant was investigated, since the gate's precondition (a complete proof of items 1–4) is not met.

# Summary of changes for run 7896d576-cefd-4907-b707-153715903b2d
Added the sorry-free module RequestProject/Root/CodingTheory/TwistedLocatorInvariant.lean, its axiom audit RequestProject/TwistedLocatorInvariantAxiomAudit.lean, and the report TWISTED_LOCATOR_INVARIANT_REPORT.md, all purely additive at the frozen deployed row (n = 2097152, k = 1048576, e = 978944, w = 69632, B* = 274980728111395087); the audited declarations depend only on the standard axioms and there is no sorry. Outcome returned: (2). Proved: the exact transformed syndrome equations for the heavy-point split Q = (X − x)·R against the twisted syndrome direction s'_j = s_{j+1} − x·s_j, showing that one fixed point removes exactly one unknown and gains no equation; the transformed divisibility constraint that R divides (X^n − 1)/(X − x); that the locator constant term is itself an n-th root of unity, hence a bounded multiplicative invariant with at most 2097152 values; the resulting deployed criteria, namely that one such invariant with fibres of at most 131121028953 challenges, or two such invariants with common fibres of at most 62523, force at most B* distinct official bad challenges, with the probabilistic form 2^-128, and that the budget is exactly two invariants; unconditionally, that any deployed counterexample must have more than 131121028953 bad challenges sharing one and the same locator constant term, i.e. the same product of erased points; the algebraic dichotomy that a coprime rational presentation of the constant term of degree at most 69632 is either constant or yields at most 146028888064 bad challenges, a factor above 1.8 million below B*; and exact obstructions for the linear part of the twisted data (the twist adds no new multiplicative invariant, and the twisted system keeps a solution space of dimension at least 909312, so no determinantal elimination from it can produce a nonzero annihilator). Every annihilator used is built from bounded invariant data given independently of the unknown challenge set. No unconditional heavy-point fibre bound and no counterexample are claimed; the two explicit routes that would close the row are recorded in the report. The Properties table was updated with the new definitions and nine proved results, and all work is committed.

# Summary of changes for run aac4fdea-c1cc-497d-b566-58abf53ca5f8
STATUS: DECISIVE_REDUCTION. Full report in GRAND_MCA_ROOT_INCIDENCE_REPORT.md. The new sorry-free, axiom-clean module RequestProject/Root/CodingTheory/LocatorRootIncidence.lean (axioms audited in RequestProject/LocatorRootIncidenceAxiomAudit.lean: only propext, Classical.choice, Quot.sound) proves a root-incidence bound on distinct official challenges and derives deployed criteria at n = 2097152, k = 1048576, e = 978944, width 69632: a point-multiplicity bound of 128360144567623878, or a locator selection that is algebraic of degree at most 128360144567623878 in the challenge, implies at most 274980728111395087 distinct official bad challenges together with the corresponding soundness-error bound; an affine locator pencil implies at most two challenges (at most 2097152 in general). Unconditionally, any deployed counterexample must have a single domain point erased by more than 128360144567623878 of the bad challenges. Checked arithmetic also rules the one-point descent to the Johnson regime out quantitatively at this row. The single next theorem to attack is stated explicitly in the report. All work is committed and no pre-existing file was modified.

# Summary of changes for run e3ba3d4a-e3c5-43e7-87c4-18ed9a70f058
Continuing from the HIGHER-ARITY-DEPENDENCY verdict, I studied minimal circuits of the actually deployed joint vectors and settled route (ii) all the way to the deployed parameters, plus a quantitative complement for route (iii). Route (i) is therefore refuted rather than proved, and no Grand MCA claim is made anywhere.

New Lean, all sorry-free and kernel-checked (every load-bearing declaration prints only propext/Classical.choice/Quot.sound; no native_decide, no new axioms):

1. `RequestProject/Root/CodingTheory/OfficialCircuitCosetTransfer.lean` — the transfer theorem `official_arity_four_circuit_of_labels`. Choosing each erasure set as a common part together with full fibres of the d-th power map makes each locator's value on a class depend only on the class label, which collapses the w+1 point conditions of the class equation to twelve scalar label equations, independent of the width, the locator degree, the domain size and the field. Supporting general lemmas: a set of d points with equal d-th powers has product of linear factors exactly X^d − τ (`prod_X_sub_C_eq_X_pow_sub_C`, `qPoly_fibre`), and the coset factorisation of the locator (`qPoly_coset_eval`).

2. Analysis of the transfer condition: solving the twelve label equations is exactly the requirement that four points (b₂,b₃) of F² be collinear with (1,1) on a non-axis-parallel line, i.e. a coincidence of one scalar invariant σ = (b₃−1)/(b₂−1) across the four locators. A degree-one locator factor provably cannot satisfy it. This turns the test into a four-way collision search, carried out in `analysis/official_arity_four_transfer_deployed.py` and `analysis/official_arity_four_deployed_lean_data.py`.

3. `RequestProject/Root/CodingTheory/OfficialCircuitArityDeployed.lean` — the deployed row is reached: `official_arity_four_circuit_deployed` gives an official split-locator circuit of arity exactly four over D = μ_{2^21} in the field with p = 2^31 − 2^24 + 1 elements, with k = 2^20, locator degree e = 978944 and width w = n − k − e = 69632. Four erasure sets of size exactly e produce four monic degree-e locators dividing X^2097152 − 1; there are two words for which the four distinct challenges are official and nondegenerate, the joint syndrome vectors carry a dependency with all four coefficients nonzero, and no three of them are dependent. The domain is built from an explicit primitive 2^21-st root of unity (order proved by a 21-step squaring chain), and fibre sizes come from a general fibre-counting lemma; the twelve label equations are discharged by kernel evaluation. Caveat stated in the module and report: the deployed protocol samples challenges from the degree-six extension while these four challenges lie in the prime subfield, over which the statement is made; all deployed combinatorial parameters are attained exactly.

4. `RequestProject/Root/CodingTheory/OfficialCircuitPencilRank.lean` — route (iii): `pencil_family_card_le_three` shows a challenge-compatible dependency of a pencil-shaped family is exactly the vanishing of three moments, so such a family with no nonzero dependency has at most three members, independently of the width. At the deployed row this improves the earlier dependency-free bound from 69632 to 3, so arity four coexists with a rank-three, hence tiny, challenge count.

5. `RequestProject/OfficialCircuitDeployedAxiomAudit.lean` — `#print axioms` for all sixteen load-bearing declarations of the new modules.

Documentation: `OFFICIAL_CIRCUIT_ARITY_REPORT.md` records the mechanism, a claim ledger, the explicit separation between the older generic linear-algebra arity-4 example (bare vectors, no words/locators/domain) and the official split-locator examples, the derivation and test of the transfer condition, the deployed data, and an explicit list of what is not claimed. `RESULTS.md` gained a corresponding section. The Properties table lists the five deliverables, all marked proved.

Not done, and flagged as such in the report: a general-index version of the master theorem (which would let the rank bound apply directly to official families of arbitrary size rather than through their pencil shape), and any bound for official families outside the pencil shape.

# Summary of changes for run 2d9b3bac-7f96-4315-835e-85ce48296588
**Returned status: `HIGHER-ARITY-DEPENDENCY`.**

STEP 1 (the mandatory arity check) is settled negatively, so per the stop rule STEP 2 (canonical directions) and STEP 3 (cross-adapter) were **not** entered: no direction fibre bound, no boundary claim, no line/direction bridge, and no bound on the bad-challenge count is asserted.

Everything is additive — two new modules, nothing existing modified — and both build cleanly with no `sorry`, no `native_decide` and no new axiom; the audit module prints `[propext, Classical.choice, Quot.sound]` for all nine load-bearing declarations.

**New Lean module `RequestProject/Root/CodingTheory/ResidualDependencyArity.lean`:**

1. *The definitions under test.* `IsChallengeDependency` transcribes the exact hypothesis consumed by the `2w` incidence theorem (coefficients annihilating both the syndrome vectors and their γ-weighted versions), and `IsTripleDependency` is a nonzero dependency of the subfamily indexed by three distinct challenges (injective index map, so distinct challenges are counted — not supports, locators or arbitrary vectors). A dependency is proved equivalent to a linear dependence of the joint vectors `(v γ, γ·v γ)`, so minimal dependencies are the circuits of that matroid.
2. *The exact arity interval.* Arity ≥ 3: a dependency vanishing outside two distinct challenges is identically zero. Arity ≤ `2w+1`: any more than `2w` challenges already carry a dependency. At width one every triple of distinct challenges with nonzero syndrome vectors is dependent, which is why the earlier three-challenge classification looked complete — it is an artefact of width one.
3. *The obstruction.* Over the five element field with width 2, four distinct challenges `(1,2,3,4)` with syndrome vectors `(1,γ⁻¹)` carry a dependency with all four coefficients nonzero, while every dependency of the family that vanishes at some index is identically zero (exhaustive kernel check over all 625 coefficient families). Equivalently: no three of the four challenges are dependent. So a nontrivial dependency need not contain a 3-supported one. Minimality is proved as well: arity 1 and 2 are impossible, width 1 is impossible, and four distinct challenges force a field with at least four elements.
4. *Where the obstruction is provably absent.* At locator degree one the official syndrome vectors are the values of a single affine line; it is proved that the pencil relation at three distinct challenges with nonzero syndrome vectors forces all of them to be nonzero multiples of one vector, hence that **every** triple of official residual challenges at degree one is dependent — arity three is complete there, for any width. Nothing in this transfers to the deployed locator degree, in either direction.

The write-up, with the exact statements, the geometric reason (four points of a Segre quadric lying on a plane conic), the minimality argument, the consequences for the direction route, and per-claim labels, is in `RESIDUAL_DEPENDENCY_ARITY_REPORT.md`; the axiom audit is `RequestProject/ResidualDependencyArityAxiomAudit.lean`. The Properties table lists the six new theorems (all proved) and the two definitions they are stated in terms of. Honest scope note, repeated in the report: the arity-4 example is an exact counterexample to the arity-3 implication *for the gate hypothesis as stated*, not a statement about the deployed parameter row; whether that row admits such a configuration is left open, and no numerical bound is claimed. All work is committed.

# Summary of changes for run cbe10c68-2aec-4bb0-ad1a-ea9635b28960
**Verdict: RESIDUAL_DEPENDENCY_CLASSIFIED.** A challenge-compatible dependency can exist among official residual split locators, so the missing implication needed for `#ResidualBad ≤ 2w` (and hence `#Bad ≤ 3w = 208896 < B*`) is **not** available; those two numerical conclusions remain unproved.

What was done, all machine-checked and sorry-free:

1. **Step 1 — exact reconstruction.** The existing 2w theorem (`card_le_two_mul_width_of_regular`, in `RequestProject/Root/CodingTheory/SplitLocatorPencilIncidence.lean`) was restated item by item in `RESIDUAL_DEPENDENCY_GATE_REPORT.md`: its quantified objects (field, width, finite index type, scalars, vectors — nothing else), the exact "no challenge-compatible dependency" condition, the fact that it is a pure linear-algebra statement in which splitness, monicity, divisibility of the locator by Xⁿ−1 and the domain never appear, that it counts index elements rather than distinct challenges (so an adapter to the official challenge *set* is still missing and is labelled REPORTED_NOT_REPLAYED), that repetition of locators/supports is unrestricted, that nondegeneracy is implied rather than assumed, the divided-difference identity, and the conclusion 2w. It does apply formally to the official residual object, so the outcome is not a hypothesis mismatch: the whole gap sits in the dependency-free condition.

2. **Steps 2–4 — the obstruction, in a new module `RequestProject/Root/CodingTheory/ResidualDependencyGate.lean`.** Proved: a dependency exists exactly when the corresponding combination of locators lies in the common kernel of the two syndrome maps; no dependency can live on two challenges (so the minimum is three); a three-challenge dependency forces the syndrome vectors to be proportional, and conversely three distinct challenges with proportional nonzero syndrome vectors always carry an explicit nonzero dependency with divided-difference coefficients. Finally an **exact official model** was constructed and verified — official syndrome functional, official split-locator challenge set, monic degree-1 split locators with roots in the domain (hence dividing Xⁿ−1, distinct roots, nonzero constant term), official nondegeneracy, and all three challenges *residual* (full pencil rank, no rank lost on the monic hyperplane) — in which three distinct challenges do carry a nonzero dependency while 2w = 2. Non-vacuity is certified with the cube roots of unity {1,2,4} in the field of 7 elements (a genuine root-of-unity domain avoiding 0, characteristic not dividing the order). This refutes the implication as a structural consequence of the official residual hypotheses; it is an exact small model, not the deployed parameter row, and nothing here decides the deployed row either way.

3. **Step 5 — limited salvage only.** The exceptional predicate is stated exactly (a residual challenge is exceptional iff its syndrome vector lies in the span of the others), and the immediate consequence is proved: on the dependency-free complement the syndrome vectors are independent, so it has at most w members. No bound on the exceptional set is claimed, and no further theory was developed.

An audit module (`RequestProject/ResidualDependencyGateAxiomAudit.lean`) prints the axioms of all eleven load-bearing declarations: every one uses only the standard `propext, Classical.choice, Quot.sound`. Only the two new modules were built; nothing existing was modified. All claims are labelled PROVED / EXHAUSTIVE_SMALL_MODEL / CONDITIONAL / REPORTED_NOT_REPLAYED in the report, and work is committed.

# Summary of changes for run 37895103-4da7-45c2-9f36-3e1192a47489
**Primary status returned: HIGHER_ORDER_INCIDENCE_LEMMA.** No bound `#Γ ≤ B*` and no counterexample is claimed; the full write-up is in `SPLIT_LOCATOR_NONLINEAR_INCIDENCE_REPORT.md`. All work is additive — three new Lean files, nothing existing modified — and every one of the 40 audited declarations builds with no `sorry`, no `native_decide` and no new axiom (`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all of them).

**Phase 0 (adapter safety): no OFFICIAL_ADAPTER_GAP.** The new modules act only on the monic locator `Q_E(X)=∏(X−x)`; the reciprocal `Λ_E` is never silently substituted. `locLinRestrict_eq_pencil` proves that the pencil `A + γ·B` built from the two global syndrome maps *is* the repository's official locator map, `pencil_ker_of_locatorSystem` / `locatorSystem_of_pencil_ker` prove kernel-membership and the `w` syndrome equations equivalent in both directions, and every deployed theorem is stated about `#badSet` itself via the two-directional adapter equality.

**New mathematics (`RequestProject/Root/CodingTheory/PencilRankDrop.lean`, `.../SplitLocatorPencilIncidence.lean`).** (i) A general rank-drop theorem for linear pencils over any field: relative to any reference scalar, the set of `γ` where `rank(A+γB)` drops below the reference rank has at most that many elements — proved by building a square window of the pencil that is literally the identity at the reference and counting roots of its determinant. (ii) Its deployed instance: the rank-drop locus of the deployed syndrome pencil has at most `w = 69632 ≤ B*` elements, unconditionally. (iii) An exact characterisation, in both directions: a challenge carries a monic degree-`e` kernel vector iff the pencil restricted to the hyperplane `{coeff e = 0}` keeps the full rank. (iv) The unconditional deployed decomposition `#Bad ≤ 69632 + #(residual bad challenges)`, plus two conditional deployed bounds `#Bad ≤ 69632 ≤ B*` (monic branch and, since `0 ∉ μ_{2^21}`, nonzero-constant-term branch). (v) Route A: two distinct challenges never admit a dependency of their joint syndrome vectors, a new divided-difference identity for three or more challenges (`∑ᵢ cᵢ(γᵢ−γⱼ)·vᵢ = 0`), and the corollary that a challenge family with no challenge-compatible dependency has at most `2w = 139264 ≤ B*` members. (vi) An exact identification of the syndrome maps as the Hankel matrices of the two moment sequences, so the deployed object is the Hankel pencil `H(m⁰+γm¹)` with `69632` rows and `978945` columns.

**Honest limits, as required by the report.** A proved sharpness example shows the residual branch is genuinely possible: there are pencils where the hyperplane restriction never loses rank and the rank-drop locus is empty, so the rank-drop bound alone cannot bound the monic challenge set. The first implication that fails is therefore that monicity and non-vanishing at `0` are single linear conditions while the kernel has dimension at least `e+1−w = 909313`; the smallest next equation is the truncated-Hankel rank gap of the deployed moment pencil, to be attacked with a second, multiplicative consequence of `Q | Xⁿ−1`. This is strictly more than the pairwise route (which was vacuous by interpolation and produced no number at all) and strictly less than the target bound. No do-not-reopen item was reopened, no toy model supports a deployed claim, and the `m = 8` branch was left untouched.

# Summary of changes for run a911a8c3-9c3f-4e94-bcf7-2c2c2b88b326
**Primary status: SPLIT_LOCATOR_QUANTITATIVE_OBSTRUCTION** (Phase 1 = LOCATOR_BRIDGE_PROVED; Phase 2 official adapter proved in *both* directions; Phase 3 first quantitative attempt executed, with two exact obstructions proved and no bound ≤ B* claimed).

Full write-up: `SPLIT_LOCATOR_GATE_AUDIT_REPORT.md`. Four new, purely additive Lean modules plus an axiom-audit file were added and built; nothing existing (declarations, toolchain, lakefile, manifest) was touched. No `sorry`, `admit`, `native_decide` or new axioms: all 42 load-bearing declarations were checked with `#print axioms` (`RequestProject/SplitLocatorGateAxiomAudit.lean`) and depend only on `propext`, `Classical.choice`, `Quot.sound`.

**Phase 1 — locator orientation (`LocatorOrientation.lean`, `LocatorSyndromeBridge.lean`).** The reciprocal locator `Λ_E(X)=∏(1−xX)` and the monic split locator `Q_E(X)=∏(X−x)` are kept strictly apart (with an explicit witness that they differ). Proved: the reversal identity `Λ_E = reverse(Q_E)`, the coefficient dictionary `Λ_E.coeff i = Q_E.coeff(e−i)` for `i ≤ e` and `= 0` above, the evaluation form `Λ_E(y) = y^e·Q_E(1/y)` for `y ≠ 0`, invertibility of the reversal when no evaluation point is `0`, degree bounds (`deg Q_E = e` exactly, `deg Λ_E ≤ e` with equality iff no point is `0`), monicity/normalisation (`Q_E` monic, `Λ_E(0)=1`), the root correspondence (roots of `Λ_E` are the inverses `x⁻¹`; `0` is never one), and `Q_E ∣ X^n−1` for `E ⊆ μ_n`. The syndrome half proves `(Λ_E·S).coeff(e+d) = gsynd f (Q_E·X^d)` for `e+d<r`, the modulus equivalence (`∃Ω, deg Ω<e, X^r ∣ Λ·S−Ω` ⇔ vanishing of the coefficients `e..r−1`) and hence, in both directions, `LocatorSystem w ↔ KeyCongruence` — the `w` locator equations *are* the classical key congruence in the correct orientation. A negative convention result is also proved: over a domain of roots of unity the naive column window `(x^k,…,x^{n−1})` is not a parity check (explicit `μ₄ ⊂ ZMod 5` witness), so it may not be substituted for the multiplier-weighted window `0..r−1` used here.

**Phase 2 — official adapter (`SplitLocatorOfficialAdapter.lean`).** The converse direction was proved (dual Welch–Berlekamp, using the repository's own dual adapter and biduality): a monic split locator of size exactly `e` solving the global system nondegenerately implies official `IsBad`, with window `Eᶜ` of size exactly `n−e`. Combined with the existing forward direction this gives the exact equality `↑(badSet k e f₀ f₁) = locatorChallengeSet k e f₀ f₁`, equality of the two counts, and the deployed equivalence `#badSet ≤ B* ↔ ncard(split-locator set) ≤ B*`. Conventions checked explicitly: exact support size, complement window, monicity and divisibility of `Q_E`, finite `γ` only (no projective infinity), `γ = 0` admitted, unchanged rank-≤2 received pencil, same-support noncontainment. **Consequence: the split-locator gate is not a relaxation — it is the official statement.**

**Phase 3 — quantitative gate (`SplitLocatorChallengeCount.lean`).** Distinct challenges are counted, not locators or supports: each support carries at most one finite challenge (injection `γ ↦ E_γ`, giving the numerically useless `|G| ≤ C(n,e)`), while several supports may share a challenge. Route A (two-challenge comparison) is carried out — two distinct bad challenges force line-closeness on `E_γᶜ ∩ E_δᶜ`, of size ≥ `n−2e` — and its first exact obstruction is proved: by Lagrange interpolation *every* pair is line-close on *every* window of size ≤ `k`, and at the deployed row the guaranteed window is only `n−2e = 139264 = 2w ≤ k = 1048576`, so the conclusion is vacuous; both classical regimes (`2e ≤ n−k`, `3e < n−k+1`) are shown to fail numerically. Route B is anchored only (the evaluation vector of `Q_E` has weight exactly `n−e`, a minimum-weight word of `RS_{e+1}(D)`); no theorem counting challenges is claimed. Route C's first exact obstruction is proved: the split locators of size `e` span the whole locator space `F[X]_{<e+1}`, so splitness is invisible to every linear functional and any bound must be nonlinear. Deployed numerics verified in Lean: `w³ = 337618789203968 < B*`, `n·w² = 10168283533672448 < B*`, `n²·w = 306244774661193728 > B*`, and `B* = ⌊p⁶/2^128⌋`, so the trivial bound `|F|` misses the target by exactly `2^128`.

**Single remaining implication:** for every official pair on `D = μ_{2^21}`, the number of distinct finite challenges admitting a monic degree-`978944` locator split over `D`, annihilated by `A+γB`, and nondegenerate for `f₁`, is at most `B* = 274980728111395087`. The implication from that bound to the deployed Grand-MCA row is proved; its hypothesis is not, and — because the adapter is an equality — it is exactly the deployed statement. The unconstrained-annihilator route, sunflower/Johnson-type arguments, ledger/partition routes and the separate construction-side branch were not reopened or used.

# Summary of changes for run 26978f34-fe00-44ae-9166-b8bf836710e4
**Status returned: `ANNIHILATOR_OBSTRUCTION` + `NEW_SMALLEST_GATE`.** No numerical bound on #Bad is claimed; `GRAND_MCA_SAFE` and `OFFICIAL_COUNTEREXAMPLE` are not claimed. The full write-up is in `ARISTOTLE_PARALLEL_GRAND_MCA_GLOBAL_CHALLENGE_RESULT.md`; all work is additive (no existing file was modified).

New, machine-checked material (`RequestProject/Root/CodingTheory/GlobalChallengeAnnihilator.lean`, `RequestProject/Root/CodingTheory/GrandMcaGlobalGate.lean`, plus the two axiom-audit files):

1. **Global (support-free) certificate.** Two fixed linear functionals `gsynd f₀`, `gsynd f₁` on `F[X]`, attached to the official pair only (they are the source-native pairing against the common dual adapter). `gsynd_locator_eq_zero` proves the key equation elementarily (agreement off `E` plus `k+|E|+w ≤ n` forces the syndrome of `Q_E·h` to vanish for all `deg h < w`), and `isBad_locator_certificate` derives from *official* `IsBad` an erasure of size exactly `e` whose locator satisfies the whole `w`-row global system, with the normalised witness `gsynd f₁(Q_E·h)=1`, `gsynd f₀(Q_E·h)=−γ` (replaying the erasure-normalisation and projective-label results of the source).

2. **The exact obstruction.** With the splitting constraint on the locator dropped, the system is a linear map `F[X]_{<e+1} → F^w`. `finrank_ker_locLin_ge` gives kernel dimension `≥ e+1−w` (deployed: `909313`), `exists_nonzero_locator` / `unconstrainedLocatorSet_eq_univ` show every challenge in `F` admits a nonzero locator, and `deployed_unconstrained_annihilator_degree_ge` concludes that any nonzero annihilator of that locus has degree `≥ |F| > B*`. So the unconstrained eliminant is identically zero — the stop rule triggers. This is the dual form of the repository's primal Welch–Berlekamp statement (the same inequality `n < k+2e+1`), so neither route circumvents the other.

3. **The single smallest remaining implication.** `deployed_card_badSet_le_of_gate` and `deployed_grand_mca_of_gate` / `deployed_epsMCAmax_le_of_gate`: if the *global* split-locator challenge set (challenges carrying a monic degree-`e` polynomial split over `D` — equivalently a minimum-weight codeword of `RS_{e+1}(D)` — in the kernel of `A+γB`, nondegenerately) has at most `B* = 274980728111395087` elements, then `#Bad ≤ B*` and `ε_mca^max ≤ B*/|K|` at `n=2097152, k=1048576, e=978944, w=69632`. Everything left of the gate is proved; the gate itself is not.

4. **Audits.** The `Q_E | Xⁿ−1` convention is verified rather than assumed (`domainVanishing_eq_X_pow_sub_one`, `qPoly_dvd_X_pow_sub_one`: it holds exactly for a domain of `n` distinct `n`-th roots of unity; generally only divisibility of `∏_{a∈D}(X−a)`). A conditional deployed lower bound from the capacity-gap block pencil (`c=2¹⁷, s=8, m=16`) gives `C(16,9)=11440` bad challenges — a factor `>2·10¹³` below `B*`, so the known families cannot falsify the row. `deployed_budget_ledger` confirms `w³` and `n·w²` exactly and corrects the task's `n²w` figure: the true value is `306244774661193728`, not `306244774661193700` (the inequality `n²w > B*` is unaffected).

No pivot-depth recurrence, no m=8 trade identities, no Johnson/sunflower/second-moment/support-counting step, no external census, and no `sorry`, `admit`, `native_decide` or new axiom. All four new targets build under Lean 4.28.0 / Mathlib, and every audited theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

# Summary of changes for run e39d167e-7294-4ffc-b6ff-3d37d4ebda13
**Status returned: `PIVOT_DESCENT_OBSTRUCTION`.**

Phases A–E produced genuine extra structure, so Phase F was run; it terminated with a precise obstruction, which is a decisive outcome under the stop rule. No numerical bound and no global recurrence is claimed; the Grand-MCA gate is untouched. The four existing modules were used as black boxes and are unmodified; all work is additive.

New files: `RequestProject/Root/CodingTheory/PivotFiltration.lean` (Phases A–D), `RequestProject/Root/CodingTheory/PivotResidual.lean` (Phases E–F), `RequestProject/PivotFiltrationAxiomAudit.lean`, and the write-up `PIVOT_FILTRATION_RESIDUAL_AUDIT_REPORT.md`.

1. **Definition of `F_ge(a)`.** `tailFge k w e f₀ f₁ a = {S ∈ supportLocus : ∀ b < a, T₁(S)_b = 0}`, built on a new model-independent `PivotCore.geFiltration`.

2. **Nestedness and successive difference.** `tailFge_zero` (`F_ge(0) = supportLocus`), `tailFge_succ_subset`/`tailFge_antitone`, `mem_tailFge_iff_le_pivot` (`S ∈ F_ge(a) ↔ a ≤ pivot(S)`), `pivotStratum_eq_sdiff` (`L_a = F_ge(a) \ F_ge(a+1)`), `tailFge_width_eq_empty`, `supportLocus_eq_disjoint_iUnion`. The `T₀` prefix vanishing (`tailFge_prefix_eq_zero`) is derived from the existing exact rank-one/challenge relation, not assumed. The pivot is therefore a genuine nested filtration.

3. **First nonzero layer.** `first_nonzero_layer`: on `L_a`, `a < w`, `T₁(S)_a ≠ 0`, both words vanish on the whole earlier prefix, and `(T₀(S)_a, T₁(S)_a) = T₁(S)_a·(−γ_S, 1)`, i.e. `[T₀(S)_a : T₁(S)_a] = [−γ_S : 1]`. Deliberately not called intrinsic.

4. **Quotient formulation — valid.** `prefixSub` gives `⊤ = G_0 ⊇ … ⊇ G_w = ⊥` in `F^w`; `prefixSub_succ_eq_inf_ker` and `layerQuotEquiv` identify the `a`-th successive quotient with the `a`-th coordinate; `pivot_eq_iff_layer` is the exact equivalence "pivot(S) = a iff the pair vanishes in all earlier quotients and has a nonzero rank-one image, proportional to `(−γ_S, 1)`, in quotient `a`".

5. **Interpolation interpretation.** `prefix_eq_zero_iff_coeff_window`: the prefix conditions say exactly that the interpolant has no coefficient in the degree window `[k, k+a)`; coefficients below `k` are unconstrained, so this is not a degree bound and not a shorter code.

6. **Moment interpretation.** With the barycentric power sums `lamPow` (`= 0` below the top degree, `= 1` at it): `moment_eq_sum_tailCoord`, `moment_eq_tailCoord_add_higher` and the inversion `tailCoord_eq_moment_sub` give the exact change of coordinates, which is unitriangular **in the reversed order**. Consequence: `momentPivot_eq_sub_tailTop` (moment pivot `= w − 1 − ` top nonzero tail index) and `momentPivot_eq_pivot_iff` (the two pivots agree iff `pivot + tailTop = w − 1`). The tail pivot must not be identified with the moment pivot; only the challenge value is common.

7. **Cross-pivot compatibility — proved, with two explicit non-consequences.** `pivotStratum_subset_tailFge` (`L_b ⊆ F_ge(a)` for `a ≤ b`), `pivotStratum_prefix_eq_zero` (inheritance of the defining equations), `rho_eq_gammaSupp_of_coord_ne_zero` (every nonvanishing coordinate, not just the pivot, returns the challenge — the level-`b` datum is a deeper coordinate of the same tail object), `rho_eq_rho_iff_gammaSupp_eq` (exact compatibility across strata). Also: `deeper_stratum_layer_a_zero` shows a deeper support carries no level-`a` information, and `PivotFiltrationExample.images_not_disjoint` gives a concrete instance where two strata images coincide — so the union may not be replaced by a maximum, and no bound was inferred from nestedness.

8. **Residual descent — constructed, then obstructed.** Items 1, 2, 3, 5 hold: `residual_tailCoord` (the residual object is literally the shifted tail, i.e. the instance with parameters `(k+a, w−a)`), `tailFge_subset_residual_supportLocus` (map, same erasure budget), `gammaSupp_residual_eq` and `residual_pivot_eq_zero` (challenge preserved, residual pivot `0`), `residual_width_lt`. Item 4 **fails**: `residual_tail_eq_zero_iff_isCloseOn` shows the residual witness predicate is closeness to the code of degree `< k+a`, and `isCloseOn_strict_mono` shows that code is strictly larger whenever `0 < a` and `k < |S|`; `residual_descent_semantics_obstruction` packages this with `(k+a)+(w−a) = k+w`, and `image_rho_subset_residual_image` shows the stratum image lands in the bad set of that weaker instance. Depth buys width exactly at the price of dimension; nothing contracts, so pivot depth has no residual meaning.

9. **Build status.** `RequestProject.Root.CodingTheory.PivotFiltration`, `RequestProject.Root.CodingTheory.PivotResidual`, `RequestProject.PivotFiltrationAxiomAudit` all build with no errors, no warnings and no `sorry`; the full project (`lake build`, 8439 jobs) also completes successfully.

10. **`#print axioms`.** All 76 audited declarations print `[propext, Classical.choice, Quot.sound]` (the purely arithmetic `residual_width_lt` prints `[propext, Quot.sound]`); no other axioms, and no `axiom` or `@[implemented_by]` was added.

Grand MCA is **not** claimed solved: no quantitative bound `|Bad| ≤ B*` was derived.

# Summary of changes for run dc955f5c-cba0-43d7-97a1-bf30bb335347
**Status returned: `PIVOT_STRATIFIED_CHALLENGE_IMAGE`.**

New, additive, `sorry`-free modules (no earlier file modified, no excluded topic reopened):
`RequestProject/Root/CodingTheory/PivotCore.lean` (model-independent pivot machinery),
`RequestProject/Root/CodingTheory/SupportTailPivot.lean` (Phases A–D),
`RequestProject/SupportTailPivotAxiomAudit.lean`, plus the write-up
`PIVOT_STRATIFIED_CHALLENGE_IMAGE_REPORT.md`.

1. **`pivot` definition.** Tail coordinates repackaged with a ℕ index, `tailCoord k w S f a = if a < w then tail k w S f ⟨a,h⟩ else 0`; then `pivot k w f₁ S = PivotCore.pivot w (tailFam k w f₁) S`, i.e. `sInf {a | a < w ∧ T₁(S)_a ≠ 0}` — the minimum, not a choice. `pivot_eq_min'` proves it equals `Finset.min'` of `{a : Fin w | T₁(S)_a ≠ 0}` for the existing finite ordering on `Fin w`.
2. **Existence.** `pivotSet_nonempty_of_mem_supportLocus`, `pivot_lt_width`, `tailCoord_pivot_ne_zero`, `tailCoord_eq_zero_of_lt_pivot`, uniqueness via `pivot_eq_of` / `pivot_eq_iff`.
3. **Partition.** `pivotStratum`, `pivotStratum_disjoint`, `pivotStratum_pairwise_disjoint`, `pivotStratum_eq_empty_of_le`, `iUnion_pivotStratum`, and `biUnion_pivotStratum : ⋃_{a<w} L_a = supportLocus`; `mem_pivotStratum_iff` gives `T₁(S)_a ≠ 0` with vanishing prefix.
4. **Fixed-coordinate ratio.** `gammaSupp_eq_pivot_ratio : γ_supp(S) = −T₀(S)_a / T₁(S)_a` on `L_a`, and the interpolation-coefficient form `gammaSupp_eq_coeff_ratio`.
5. **Exact image union.** `image_gammaSupp_eq_biUnion`, `badSet_eq_biUnion_image_rho`, with cardinality versions `ncard_image_gammaSupp_le_sum`, `badSet_ncard_le_sum_ncard_image_rho`, and `deployed_pivot_stratified_image` for `w = 69632`. The official relation used is the equality already available from the current source; no support-count bound substitutes for an image bound.
6. **Fibres.** `pivotFibre`, `mem_pivotFibre_iff`, `mem_pivotFibre_iff_explicit` (locus + `a < w` + `T₁(S)_a ≠ 0` + prefix vanishing + `T₀(S)_a + γ·T₁(S)_a = 0`), `mem_image_rho_iff`, `pivotFibre_eq_stratum_inter`, and `mem_pivotFibre_iff_isCloseOn` (on a stratum the single pivot equation is *equivalent* to full official closeness of `f₀ + γ·f₁`). Fibres are never identified with supports.
7. **Moment transport.** Both models are instances of the same core: `momentPivot`, `momentStratum`, `rhoMom`, `momentFibre`, `image_gammaMom_eq_biUnion`, `badSet_eq_biUnion_image_rhoMom`, and challenge compatibility `rho_pivot_eq_rhoMom_momentPivot` via the existing locus/challenge equivalences. Caveat recorded: the two pivots are indices in different coordinate systems; only the challenge values and image decompositions are proved equal.
8. **Phase D structure.** Rank-one relation `tailCoord_zero_eq_neg_rho_mul`, induced prefix vanishing for `T₀`, determinantal identity `tailCoord_det_eq_zero`, coordinate-independence `tailCoord_ratio_indep`, polynomial prefix statements `coeff_interpOn_eq_zero_of_lt_pivot` / `coeff_interpOn_pivot_ne_zero`, and projective/fibre-compression invariance. No numerical bound invented; no claim that these imply `|Bad| ≤ B*`.
9. **`lake build`**: `RequestProject.Root.CodingTheory.PivotCore`, `RequestProject.Root.CodingTheory.SupportTailPivot`, `RequestProject.SupportTailPivotAxiomAudit` all build with no errors, no warnings, no `sorry`.
10. **`#print axioms`**: every audited declaration prints `[propext, Classical.choice, Quot.sound]` (the purely definitional `PivotCore.ratio` prints `[propext, Quot.sound]`); no other axioms.

**Remaining mathematical gate:** for each `a < w` (deployed `a < 69632`), prove a useful bound on `|image(rho_a | L_a)|` — the number of distinct values `−T₀(S)_a / T₁(S)_a` over supports with pivot exactly `a` — or exhibit a structural obstruction/counterexample. Equivalently, decide nonemptiness of the fibres characterised above. The Grand MCA theorem is **not** solved by the completion of this pivot theory.

# Summary of changes for run 48533d7a-d77e-4587-8594-a29e9cbf2a51
## Status returned: `EXACT_SUPPORT_TAIL_IMAGE` (with additional exact structure, see 7)

The varying exact-erasure geometry is replaced by a lossless **fixed-codomain** representation of the official challenge map. Everything is additive: no earlier declaration, file or proof was modified or redone; nothing uses `sorry`.

New modules:
* `RequestProject/Root/CodingTheory/SupportTailChallenge.lean` — interpolation tails and the whole challenge chain;
* `RequestProject/Root/CodingTheory/SupportTailMoments.lean` — barycentric moment coordinates (second exact model);
* `RequestProject/SupportTailChallengeAxiomAudit.lean` — `#print axioms` for every user-facing declaration;
* `EXACT_SUPPORT_TAIL_IMAGE_REPORT.md` — full write-up.

`MAXIMAL_ERASURE_NORMALIZATION` and `EXACT_CHALLENGE_IMAGE_THEOREM` are used as black boxes only.

**1. Exact support-side official equivalence.** `isBad_iff_exists_support_tail`: `IsBad k e f₀ f₁ γ ↔ ∃ S, |S| = |D|−e ∧ Tail_S(f₁) ≠ 0 ∧ Tail_S(f₀) + γ·Tail_S(f₁) = 0`. Both directions checked against the official clauses through the exact-window normalization (`S = Eᶜ`); `γ = 0` allowed; no projective convention. The nonzero clause is proved, not assumed: `lineCloseOn_of_tail_one_eq_zero` shows `Tail_S(f₁)=0` plus the agreement equation forces `Tail_S(f₀)=0`, i.e. both coefficient words jointly explained on the same support, contradicting official noncontainment.

**2. Exact fixed-codomain representation.** `interpOn S f = P_{f,S}` with degree bound, interpolation property, uniqueness (`interpOn_unique`, `existsUnique_interpOn`) and linearity in `f`; `tail k w S f ∈ Fin w → F` is the application of a genuine linear map. Load-bearing theorem `tail_eq_zero_iff` (`k+w=|S|`): `Tail_S(f)=0 ↔ f|_S` is explained by a polynomial of degree `< k` — both directions proved, no dimension count.

**3. Exact challenge map.** `supportLocus`, `exists_unique_gammaSupp` (uniqueness from `T₁(S) ≠ 0`), `gammaSupp` as an actual function with spec and functional uniqueness.

**4. Exact image equality.** `exact_support_tail_challenge_image`: `{γ | IsBad …} = γ_supp '' supportLocus`; Grand-MCA target recorded as `ncard_badSet_le_of_ncard_image_gammaSupp_le` (`|im γ_supp| ≤ B*`), not replaced by counting supports.

**5. Relation to the erasure-side `gammaL`.** An actual commuting theorem: `gammaL_compl_eq_gammaSupp` gives `γ_L(Sᶜ) = γ_supp(S)` under `E = D \ S`, with `compl_bijOn_supportLocus` (bijection of the two loci) and `image_gammaSupp_eq_image_gammaL`.

**6. Explicit coordinates actually proved.** Lagrange route: `tail_apply_eq_sum_basis` and `tail_apply_eq_sum_nodal`, `Tail_S(f)_a = ∑_{x∈S} f(x)·λ_x·[X^{k+a}](Q_S(X)/(X−x))` with `λ_x = 1/Q_S′(x)`; `gammaSupp_eq_ratio_coord` (`γ_S = −T₀(S)_a/T₁(S)_a`); `tail_top_eq_moment`. Barycentric moments were carried out as a second exact model: `coeff_top_interpOn`, `sum_lam_eval_eq_coeff_top`, and the kernel identity `moments_eq_zero_iff_tail_eq_zero` (`M_{S,·}(f)=0 ↔ Tail_S(f)=0`, proved by downward induction — the triangularity of the change of coordinates in kernel form), giving the whole chain again in moment coordinates (`isBad_iff_exists_support_moment`, `momentLocus_eq_supportLocus`, `gammaMom_eq_gammaSupp`, `exact_support_moment_challenge_image`) plus `γ_S = −M_b(f₀)/M_b(f₁)` for a coordinate that always exists on the locus.

**7. Stronger image/fibre theorems actually proved.** All pairs `(T₀(S), T₁(S))` live in the same `F^w × F^w` (`tailPair`); the challenge **factors through** that fixed codomain (`gammaSupp_eq_of_tailPair_eq`), whence `|im γ_supp| ≤ |{(T₀(S),T₁(S))}|` (`ncard_image_gammaSupp_le_ncard_image_tailPair`) — a bound inside the fixed codomain, not a support count; and on the locus the pair is rank one, `T₀(S) = −γ_S·T₁(S)`, with the derived determinantal identity `T₀(S)_a·T₁(S)_b = T₀(S)_b·T₁(S)_a`. No numerical bound on `|im γ_supp|` is claimed and no heuristic counting was used; no Newton/symmetric-function/Toeplitz–Hankel/CRT–Fourier structure was assumed or claimed.

**8. Deployed row.** `deployed_support_tail_image` and `deployed_support_moment_image`: `|D| = 2097152`, `k = 1048576`, `e = 978944`, hence `t = 1118208`, `w = 69632`.

**9. `lake build`.** `RequestProject.Root.CodingTheory.SupportTailChallenge`, `RequestProject.Root.CodingTheory.SupportTailMoments` and `RequestProject.SupportTailChallengeAxiomAudit` all build successfully, with no warnings and no `sorry`.

**10. `#print axioms`.** Every declaration in the audit file prints exactly `[propext, Classical.choice, Quot.sound]`.

# Summary of changes for run 981fece4-81a7-493b-add3-69fe772a8965
## Status: `EXACT_CHALLENGE_IMAGE_THEOREM` (plus the optional `EXPLICIT_CHALLENGE_FORMULA` extras)

New, purely additive, `sorry`-free module `RequestProject/Root/CodingTheory/ExactChallengeImage.lean` with axiom audit `RequestProject/ExactChallengeImageAxiomAudit.lean`; a full write-up is in `EXACT_CHALLENGE_IMAGE_REPORT.md`. No existing file was modified, and the normalization proof was not redone — its theorems are reused as-is.

**1. Frozen source types.** `s₀, s₁` are word-space vectors `f₀ f₁ : ↥D → F` (not objects of a separate syndrome space), `V_E = vSpace k E : Submodule F (↥D → F)`, `W_E = wSpace k E = dualCode (vSpace k E)`, `Ψ = psi D : F[X] →ₗ[F] (↥D → F)`, `wModel k E = map (psi D) (qModule (dval D) E (|D|−k−|E|))`, `Λ = lambdaMap f₀ f₁ : (↥D → F) →ₗ[F] F × F`, `lamRestrict k E f₀ f₁ = Λ ∘ (wSpace k E).subtype`, `range_lamRestrict`, `isBad_exact_window`, `isBad_of_exact_window`, `isBad_iff_exists_exact_erasure`, `challenge_unique`. Because `Λ` is the ambient pairing map, no formula of the shape `⟨sᵢ, Ψ(Q_E h)⟩` was assumed; it is derived in step 7 by composing the existing maps.

**2. Candidate locus.** `candidateLocus k e f₀ f₁ = {E | |E| = e ∧ s₁ ∉ V_E ∧ s₀ ∈ V_E ⊔ F·s₁}`, with `mem_candidateLocus_iff` proving equivalence to the source-native pair (exact-size agreement window + noncontainment). It is not identified with official badness by definition.

**3. Unique challenge.** `exists_unique_challenge` (existence from `s₀ ∈ V_E + F·s₁`, uniqueness reusing `challenge_unique`, `γ_E = 0` allowed) and the actual function `gammaL k f₀ f₁ : Finset ↥D → F` with `gammaL_spec`, `gammaL_mem_vSpace`, `gammaL_eq_of_isCloseOn`.

**4. Both inclusions.** `badSet_subset_image_gammaL` (forward, via the exact-erasure normalization) and `image_gammaL_subset_badSet` (reverse: `s₀ + γ_E s₁ ∈ V_E` and `L ⊄ V_E` from `s₁ ∉ V_E`, composed with the existing bridge — official clauses were not rebuilt by hand).

**5. Image equality.** `exact_challenge_image : {γ | IsBad k e f₀ f₁ γ} = gammaL k f₀ f₁ '' candidateLocus k e f₀ f₁`.

**Cardinality.** `|Γ(L)| = |im γ_L| ≤ |E_L|` (`ncard_badSet_le_ncard_candidateLocus`), with the exact target route `|im γ_L| ≤ B*` (`ncard_badSet_le_of_ncard_image_le`) and the stronger sufficient route `|E_L| ≤ B*` (`ncard_badSet_le_of_ncard_candidateLocus_le`) recorded separately; over a finite field also the official finset form. Distinct exact-size erasure sets may share a challenge.

**6. Λ representation.** `range (Λ|W_E) = F·(−γ_E, 1)` in the project's own sign/order convention (`range_lamRestrict_eq_span_gammaL`, via the existing `lamImage_eq_span`), plus `gammaL_eq_of_lamImage_eq`.

**7. Coefficient bridge.** `lamTilde f₀ f₁ E = Λ ∘ Ψ ∘ (Q_E · −)`, with `map_lamTilde_degreeLT` proving `Λ̃_E(F[X]_{<w}) = Λ(W_E)`; the two coordinates are genuine linear functionals with monomial expansions `Λ̃ᵢ(Xᵃ) = Σ_j q_j(E) · Σ_{x∈D} fᵢ(x)·λ_x·x^{j+a}`.

**8. Challenge formula.** `gammaL_eq_ratio`: `γ_E = −λ₀,E(g)/λ₁,E(g)` for any admissible `g` with nonzero second coordinate; `ratio_indep_of_choice` (independence of the index/element) and `exists_model_witness` (such a `g` always exists, realising `(−γ_E, 1)`).

**9. Deployed row.** `deployed_exact_challenge_image` for `r = |D| − k = 1048576`, `e = 978944`, dual width `w = 69632`.

**10. Build and axioms.** `lake build RequestProject.Root.CodingTheory.ExactChallengeImage` and `lake build RequestProject.ExactChallengeImageAxiomAudit` succeed with no warnings; every audited declaration prints exactly `[propext, Classical.choice, Quot.sound]`, and no `sorry` occurs in the new files.

Out of scope, as instructed: no counting of erasure sets, no Plücker minors, no Fourier/CRT decomposition of `W_E`, no Newton/power-sum parametrization, no Toeplitz/Hankel structure, and no claim about the fibres of `E ↦ γ_E`.

# Summary of changes for run 9e81a5a3-0400-4aa2-bdd9-46b8b4be1a95
**Status: `MAXIMAL_ERASURE_NORMALIZATION` — the full official theorem is proved, `sorry`-free and additive.**

All work is new; no existing declaration, file or submission root was modified. The `rsList(f₁,2e)` route is not used or revisited, and no operator `Φ_S(Q₀,Q₁)`, rank `2n−z₁`, or condition `z₁>w` was formalized.

New files:
- `RequestProject/Root/CodingTheory/ErasureSpanPolynomial.lean`
- `RequestProject/Root/CodingTheory/MaximalErasureNormalization.lean`
- `RequestProject/MaximalErasureNormalizationAxiomAudit.lean`
- `MAXIMAL_ERASURE_NORMALIZATION_REPORT.md` (full report, items 1–10)

Reported items:

1. **Exact polynomial span theorem** — `ErasureSpan.span_qPoly_eq_degreeLT`: for injective `v` and `s+1 ≤ |Ω|`, `span{Q_A : A ⊆ Ω, |A| = s} = F[X]_{<s+1}`, by induction on `s` from `Q_{B∪{a}} − Q_{B∪{b}} = (v b − v a)·Q_B`; and `ErasureSpan.iSup_qModule_eq_degreeLT`: for `d ≥ w ≥ 1`, `d−w+1 ≤ |Ω|`, `⨆_{|A|=d−w} Q_A·F[X]_{<w} = F[X]_{<d}`. No dimension argument. Boundary cases `d = w` (hence `d−w = 0`) and `w = 1` recorded separately.
2. **Common ambient dual-polynomial adapter** — one fixed `E`-independent map `Ψ(p)(a) = λ_a·p(a)` with the explicit GRS multiplier `λ_a = (∏_{b≠a}(a−b))⁻¹`, built on the project's existing pairing/`dualCode`. `MaxErasure.wSpace_eq_wModel`: `W_E = Ψ(Q_E·F[X]_{<r−|E|})` for all `E` with `|E| ≤ r`, together with `dualCode_reedSolomon`, `mem_vSpace_iff` (dictionary with official `IsCloseOn`) and biduality.
3. **`W_E = span W_{E'}`** — `MaxErasure.wSpace_eq_iSup_wSpace`: `W_E = ⨆{W_{E∪A} : A ⊆ Eᶜ, |A| = e−|E|}`, an equality of actual project subspaces.
4. **Noncontainment / nonzero restriction** — one common map `Λ`, restrictions `Λ|W_E` (`lamRestrict`, `range_lamRestrict`). `lamImage_eq_bot_iff`: `Λ(W_E) = ⊥ ↔ L = span{f₀,f₁} ⊆ V_E`, proved from the ambient pairing with **no** agreement hypothesis; only then `lamImage_le_line`, `lamImage_eq_span`, `finrank_lamImage` give `rank(Λ|W_E) = 1`.
5. **Same finite label** — `lamImage_eq_span` (image `= F·(−γ,1)` for the extended witness), `lamImage_ne_infinity` (label is finite, not `[1:0]`), `challenge_eq_of_span_eq`; `maximal_erasure_normalization` also returns `Λ(W_{E'}) = Λ(W_E)`.
6. **Official normalization** — `maximal_erasure_normalization` (E ⊆ E′, |E′| = e, agreement, exact same-support noncontainment, same finite label) and, in official semantics, `isBad_exact_window` / `isBad_of_exact_window` / `isBad_iff_exists_exact_erasure`: every officially bad `γ` has a witnessing window of size exactly `|D| − e`. No challenge-count bound is inferred.
7. **Deployed row** — `deployed_maximal_erasure_normalization`: `r = |D| − k = 1048576`, `e = 978944`, `w = r − e = 69632`, `e < |D|`, exact-`e` witness.
8. **Normalized locus** — `normalizedLocus` and `badSet_subset_label_image` (`Γ ⊆ ℓ(E_Λ)` with the finite-label qualification; converse not asserted), plus `challenge_unique` (at most one finite `γ` per `E`).
9. `lake build` completes successfully for the whole project (8428 jobs) and for each new module; no `sorry` in the new sources.
10. `#print axioms` for every user-facing declaration prints exactly `[propext, Classical.choice, Quot.sound]`.

Degenerate-line guard: the normalization theorem needs no hypothesis on `dim span{f₀,f₁}` (the proof never uses one), and `degenerate_line_challenge` shows that for `f₁ = c•f₀` any bad challenge satisfies `1 + γ·c = 0`. Boundary conditions are stated as `e < r` and `e < |D|` (the latter is implied over ℕ by the former, as noted in the docstring).

# Summary of changes for run 158f669b-cf8d-48c6-b795-295f314d6dc6
## FINAL STATUS: `DIRECTION_LIST_GATE_FALSE`

The `rsList` bound required by the direction-list route is **false at the deployed row — for every direction word**, by a large explicit margin. Grand MCA is *not* thereby refuted: the direction-list inequality is one-directional, so only this sufficient route is closed. No `f₀` and no official bad challenge were constructed, so no `DEPLOYED_COUNTEREXAMPLE` is claimed.

### 1. `rsList` frozen from source (no semantics correction needed)
`rsList D k r f` (in `RequestProject/Root/CodingTheory/IndicatorLineList.lean`) is the `Finset` of **words** `g : ↥D → F` with `g ∈ reedSolomonCode F D k` (evaluations of polynomials of degree `< k`) and `hammingDistance f g ≤ r` — a *closed* ball, disagreement-count metric, function equality (no quotient, no duplicates), no extra hypotheses beyond a finite field `F` and `D : Finset F`. The parameter `2e` is a plain radius, passed as the literal `2 * e = 1957888`. Its link to the official bad set is `card_badSet_le_radius_mul_card_rsList : #badSet ≤ 1 + e·#rsList(f₁,2e)` with deployed gate `deployed_mcaMax_le_of_rsListMax`. This matches the interpretation in the task, so no `SOURCE_SEMANTICS_CORRECTION` is raised. Full freeze table in `DIRECTION_LIST_GATE_FALSE_REPORT.md`.

### 2. Threshold arithmetic re-verified in Lean
`deployed_gate_arithmetic`: `⌊(B*−1)/e⌋ = 280895258678`, `1 + 978944·280895258678 = 274980728111276033 < B*`, slack `119054`.

### 3. Why the gate fails (the simultaneous RS algebra)
A list element only has to agree with `f₁` on `|D| − 2e = 139264` positions, while the code dimension is `k = 1048576`. Below dimension the shared equations are underdetermined: interpolate `f₁` on a set `T` of `|D| − 2e` points and prescribe *arbitrary* values on a disjoint set `U` of `k − |T| = k + 2e − |D| = 909312` points. Every data vector yields a distinct ball element.

### 4. New proved results (all in `RequestProject/Root/CodingTheory/DirectionListGateFalse.lean`, additive, `sorry`-free, no new axioms, no `@[implemented_by]`)
* `pow_card_le_card_rsList`, `pow_le_card_rsList_beyond_frontier`: for any finite field and domain, if `|D| ≤ k + r` then every word's radius-`r` list has `≥ |F|^(k+r−|D|)` elements.
* `card_le_rsListMax_beyond_frontier`, `rsListMax_small_forces_unique_decoding`: any list bound below `|F|` forces `k + 2e ≤ |D|` — the route is quantitatively confined to unique decoding (this is the exact form of the previously qualitative barrier).
* `deployed_pow_le_card_rsList`, `deployed_card_rsList_gt_gate`: at `|D| = 2²¹`, `k = 2²⁰`, radius `1957888`, every word has list size `≥ |F|^909312 ≥ |D|² = 4398046511104 > 280895258678` (measured failure: `L_found/L_max > 15` already from the crude step).
* `deployed_gate_false`, and at the literal deployed instance `KoalaRow.deployed_card_rsList_gt_gate_KB`, `KoalaRow.deployed_gate_false_KB` (field `GF((2³¹−2²⁴+1)⁶)`, domain the `2²¹`-th roots of unity).
* `deployed_radius_frontier`: the radius-`e` ball is still inside the frontier (`k + e = 2027520 ≤ 2²¹`, spare `69632`), so the failure is caused precisely by the radius doubling of the pairwise step; a repaired route must deliver radius `e`, not `2e`.

### 5. Adversarial checks
The sharp `F₁₃` witness (`|D| = 8, k = 3, e = 2`) has `k + 2e ≤ |D|`, i.e. inside the frontier — the new bound does not apply there and does not conflict with the existing sharpness results; `DeployedPencilOneShort`, overlap/antichain rigidity and pencil stability are upper bounds on `badSet` and remain untouched. The frontier is proved, not asserted (`≤` version for the ball bound, strict `<` for the `|F|`-ceiling).

### 6. Build and audit
`lake build RequestProject.Root.CodingTheory.DirectionListGateFalse` and `lake build RequestProject.DirectionListGateFalseAxiomAudit` both succeed, and the whole project builds (`lake build`, exit 0). Every listed declaration prints exactly `[propext, Classical.choice, Quot.sound]` (audit file `RequestProject/DirectionListGateFalseAxiomAudit.lean`; transcript in the report). No `sorry`/`admit` in the new files.

### 7. Banked / open
Retained unchanged: the extremal `M_C(t)` bridge, overlap rigidity, antichain theorem, pencil stability and the direction-list reduction itself. `M_C(1118208) ≤ B*` remains open; the useful structural output for the next route is the exact ceiling `rsListMax_small_forces_unique_decoding` — any future step must avoid the radius-`2e` ball, or restore the correlation that the ball around `f₁` alone discards.

Everything is committed; details and the reporting table are in `DIRECTION_LIST_GATE_FALSE_REPORT.md`.

# Summary of changes for run 0cb9f6e2-60d3-47ed-811a-2d57a895f97d
## Status: `RS_STRUCTURE_THEOREM`

A universal, source-exact, quantitative large-Γ rigidity theorem for the **official** MCA challenge set is proved, together with the extremal target and its exact bridge. The deployed inequality `M_C(1118208) ≤ B*` is **not** proved, and no counter-construction was found; the honest quantitative evaluation is in the report.

All work is purely additive (no existing file changed), `sorry`-free, axiom-free (`#print axioms` ⊆ {propext, Classical.choice, Quot.sound}), with no `@[implemented_by]`. Only the new modules were built.

### New Lean modules
* `RequestProject/Root/CodingTheory/ExtremalMCA.lean` (20 declarations)
* `RequestProject/Root/CodingTheory/ExtremalMCASharpness.lean` (2 declarations)
* audits `RequestProject/ExtremalMCAAxiomAudit.lean`, `RequestProject/ExtremalMCASharpnessAxiomAudit.lean` (23 `#print axioms` lines, all standard)
* logs `analysis/extremal_mca/BUILD_AND_AXIOMS.log`, `AXIOMS.txt`
* full write-up `RS_EXTREMAL_UPPER_REPORT.md`

### 1. The extremal target and the exact bridge (task §2)
`mcaMax k e D = M_C(t) = max over all lines of |Γ_C(f₀,f₁;t)|`, `t = |D| − e`, defined on the official `badSet`. Proved: `mcaMax_le_iff` (extremal ↔ universal form), the maximum is attained, and the **exact bridge** `epsMCAmax = M_C(t)/|F|` — the official `ε_mca` is a plain quotient with a closed threshold and no rounding, so `epsMCAmax ≤ B/|F| ↔ M_C(t) ≤ B`. Deployed: `deployed_security_iff` makes the deployed security claim equivalent to `M_C(1118208) ≤ B* = 274980728111395087`. Frozen parameters verified in Lean: `2097152 = 1048576 + 978944 + 69632`, `t = 1118208 = n − e = k + w`, `2t − n = 2w = 139264`.

### 2. Universal large-Γ rigidity (window-overlap ceiling)
`card_badSet_le_of_wide_overlap`: if **any** two distinct official challenges have windows meeting in ≥ `k + e` positions, the affine pencil they span explains every official challenge and `#Γ ≤ e + 1`. Hypotheses are on the witnesses, not the parameters, and quantify over every valid simultaneous selection of windows and degree-<k words. Contrapositive `card_inter_lt_of_card_badSet_gt`: `#Γ > e + 1` forces **all** pairwise official window overlaps `< k + e`; with the trivial lower bound this pins large-Γ witnesses into `2t − n ≤ |S ∩ S'| < k + e`. Specialising to guaranteed window sizes recovers, and strictly generalises, the project's unique-decoding row. Also proved: official windows of distinct bad challenges form an **antichain**.

**Sharpness** (cheap exact test): against the project's existing official `F₁₃` construction (`|D| = 8, k = 3, e = 2`, four bad challenges) two windows meet in exactly `k + e − 1 = 4` while `#Γ = 4 > 3`, so the constant `k + e` cannot be lowered.

### 3. Stability / near-extremiser structure (task §7)
`card_jointAgreement_ge_of_pencil_family`: one pencil explaining `m` challenges forces joint agreement `m·(n − e) ≤ (m − 1)|W| + n`. Deployed and exactly sharp: an extremal class of the maximal size `e + 1 = 978945` forces `|W| ≥ 1118207 = t − 1` — one position short of correlated agreement at `t = 1118208`, exactly correlated agreement at the neighbouring row `t − 1`.

### 4. Sharpened universal reduction
The fibre bound of the direction-list reduction is localised at the anchor, improving the constant from `|D|` to `e`: `#Γ ≤ 1 + e·#rsList(f₁, 2e)`. Deployed effect: the sufficient list bound relaxes from `131121028953` to `280895258678`.

### Quantitative usefulness at n = 2097152, k = 1048576, t = 1118208
1. Proves `M_C(t) ≤ B*`? **No** — the ceiling needs an overlap ≥ 2027520, not forced by the parameters (guaranteed overlap is only 139264).
2. Narrows every hypothetical `M_C(t) > B*` witness? **Yes, unconditionally** — all pairwise window overlaps in `[139264, 2027519]`, windows an antichain, every pencil class ≤ 978945 members with `|W| ≥ (m·1118208 − 2097152)/(m − 1)`.
3. Quantitative descent? **No** — none is claimed.
4. Explains the adjacent-row boundary? **Partially and exactly, at the level of one pencil** (the one-short theorem).
5. Numerically too weak for the deployed upper bound: **yes**, as stated in 1; what is numerically real at the deployed row is the relaxed list gate and the unconditional dichotomy `#Γ ≤ 978945 ∨ all overlaps < 2027520`.

The single remaining exact gate is stated in the report: bounding the number of distinct pencil directions through one challenge by `280895258678`. No residual ledger, classLoad, capturedChildCost, support partitioning, Johnson/sunflower or FFT/M31 machinery was used or extended.


# Summary of changes for run c9ede639-68b7-438b-a5ef-1c36cba6f6a3
## VERDICT: `MISSING_INTERFACE`

Full write-up: `RESIDUAL_LEDGER_AUDIT_VERDICT.md`. All new Lean material: `RequestProject/Root/CodingTheory/ResidualLedgerAudit.lean`, axiom-checked in `RequestProject/ResidualLedgerAuditAxiomAudit.lean` (every statement depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, no new `axiom`; builds clean).

### STEP 0 — interfaces frozen from source
All required notions are source-present and were reconstructed, not invented: `officialWitness`/`IsOfficialWitness`/`officialSupport`, `officialClass` (canonical residual child class) with `officialClass_determines_child`, `chargeSet` and `classChargeSet`, `capturedMult` (μ_R) with `capturedMult_add_anchorMult`, `classCost` (Φ(R) = `(resBadSet …).card`), `capturedChildCost` with `capturedChildCost_eq_sum_capturedMult`, `classLoad`, `AnchorData`/`anchorMass`, `badSet`/`posBadSet`, `residualTransition`. Two named items have **no canonical declaration**: `localCost` exists only as an abstract bound variable in the composition lemmas, and `terminalCost` occurs only as the literal `e + 1` inside `card_badSet_le_terminal_add_totalChildCost`.

Deployed quantity required by the final reduction: `deployed_load_gate` consumes `LoadGate = ∀ i ∈ univ \ an.supp, classLoad … i ≤ 19559298652205332`; `classLoad_le_capturedChildCost` is the unconditional adapter, packaged in `deployed_bound_of_capturedChildCost`. So the remaining target is exactly `capturedChildCost = Σ_R μ_R Φ(R) ≤ T = 19559298652205332`; no further adapter is needed (the reduction strictly needs only the weaker `sup_i classLoad(i) ≤ T`).

### Answer to the research question
No — the official witness semantics plus the canonical residual ledger do **not** imply the required inequality, and this is now a theorem about the interface rather than a report of failure:

1. **Adequacy.** A structure `ResidualLedger` collects exactly the exported facts about the family (charge width ≥ 69632, ground set ≤ 978944 coordinates, μ_R ≥ 1, μ_R ≤ Φ(R), class ⊆ window, geometric-slack domination), with **no disjointness of child supports** and **no support-partition identity**. `officialLedger`, `officialLedger_sum`, `officialLedger_load` prove the deployed official data is such a ledger, with ledger sum = `capturedChildCost` and ledger load = `classLoad`. The abstract `charging`/`load_le_sum` lemmas reproduce `classLoad_charging`/`classLoad_le_capturedChildCost`.
2. **Independence.** `ledger_sum_unbounded`, `ledger_sum_unbounded_with_child_cap` and `ledger_load_unbounded_with_child_cap` exhibit ledgers with the deployed parameters — in the second and third even with every child cost capped by the child list bound `1048576` — with sum `1076360310941548544 > T` and a coordinate of load `> T`. Hence no implication "ledger axioms ⇒ target" exists, for the target sum or for the weaker load gate.
3. **Why the existing route is empty.** `deployed_charging_with_self_load_is_vacuous` / `deployed_self_load_charging`: feeding the only unconditional exported load bound into the charging step gives literally `69632·C ≤ 978944·C`, true for every `C` (an algebraic tautology, not a budget). `deployed_root_not_unique_decoding`: the exported unconditional bad-set row `card_badSet_le` does not apply at the root (`3·978944 > 1048577`).
4. **New positive content.** `deployed_classCost_le_of_small_class`: for every canonical residual child class with `R.card ≤ 104448` the child instance is inside the unique-decoding regime, giving `Φ(R) ≤ 1048576` (threshold exact for that criterion). Larger classes remain unconstrained.
5. **Smallest sufficient missing interface.** `deployed_capturedChildCost_le_of_interfaces` and `deployed_bound_of_interfaces`: a root count bound `N` on the captured challenges plus a uniform child-cost bound `B` with `N·B ≤ 19559298652205332` yields `#Bad ≤ 274980728111395087`. Both inputs are absent from the exported semantics; the strong independence theorem shows the child-cost interface alone can never suffice, so a genuine root-level proximity-gap/list-size statement is indispensable.

### Deployed numerical status
The deployed inequality `Σ_R μ_R Φ(R) ≤ 19559298652205332` at `n=2097152, k=1048576, e=978944, w=69632` is **neither proved nor refuted**: it is not labelled `REFUTED` because no admissible official Reed–Solomon instance realising the counterexample models is constructed (the models satisfy the interface, not necessarily RS semantics). Everything else listed above is proved in Lean.

Forbidden shortcuts were avoided: no `Σ_R μ_R |C_R| = n − r`, no POOL/scalar rearrangement, no use of `Δ ≥ 0` or strict descent as a budget, no disjointness from pairwise intersections, no `rhoSlack`-as-cost, no recursive majorant containing the target, no hidden `#Bad` hypothesis, no Johnson/sunflower/FFT machinery. The Properties table was updated with the seven new deliverables; `ARISTOTLE_SUMMARY.md` was left untouched.


# Summary of changes for run 81ebe879-850f-473c-b264-b9df3fb2ef26
## What was delivered

A new, self-contained composition layer, built and axiom-audited:

* `RequestProject/Root/CodingTheory/GlobalLoadComposition.lean` (new)
* `RequestProject/GlobalLoadCompositionAxiomAudit.lean` (new)
* `GLOBAL_LOAD_COMPOSITION_REPORT.md` — the full theorem table (42 rows: signature, file, assumptions, conditionality, build/axiom status, numerical consequence), the item-by-item audit, and the single obstruction.

Only these two Lean files were built (`lake build` on each module by name); nothing else in the project was touched or rebuilt. Both compile with no warnings, contain no `sorry`/`axiom`/`@[implemented_by]`, and every theorem's axiom list is `⊆ {propext, Classical.choice, Quot.sound}`. Everything is proved from the canonical definitions of the existing recursion layer; earlier reports were treated as reports only and no statement from them was assumed.

## Which alternative was proved: (B)

**(B), the priced high-load descent, is proved — unconditionally in the abstract presentation, with the potential defined independently of the load.**

`fuelMajorant` / `cxMajorant` define the potential by recursion on the presentation alone (child family, multiplicity, child cost); `isExternalMajorant_cxMajorant` proves it satisfies the majorant inequality, and

```
priced_high_load_descent_cxMajorant :
  (∀ X, ∀ Y ∈ children X, cx Y < cx X) → S ⊆ children X → X' ∈ children X → 1 ≤ mult X X' →
  capturedLoadOn mult Φ X S + cxMajorant … X' ≤ cxMajorant … X
```

is exactly `Φ(X) − Φ(X') ≥ capturedLoad(X, i)`, with no hypothesis on costs, multiplicities or the load. At the canonical recursion, `highLoad_selects_child` performs the `highLoad(X,i) → X'` step and `priced_high_load_descent_canonical` gives `classLoad(i) + Ψ(R') ≤ Ψ(X₀)`. `classLoad_le_capturedChildCost` is the unconditional one-step instance.

**(A) is not proved and is not claimed.** `deployed_bound_of_root_majorant` composes the whole chain at `n = 2097152, k = 1048576, e = 978944, w = 69632`: a numeric majorant value at the root gives `#Bad ≤ B* = 274980728111395087`.

## Separation and audit

`ρ_R = (n − |R|) − 1` (`rhoSlack`), `Φ(R)` (`classCost`) and `μ_R` (`capturedMult`) are three separate objects; `ρ` never multiplies a cost — its only relation to the recursion is `deployed_card_classChargeSet_le_rhoSlack` (slack dominates charge width).

1. disjoint distinct child classes — `capturedFibre_disjoint`, `capturedChallenges_eq_biUnion`, `mem_capturedClasses_iff_mult_pos`;
2. `Σ_R μ_R` = captured parent-challenge count — `sum_capturedMult_eq_card_capturedChallenges`;
3. multiplicities separated — `multiplicity_separation` (`μ_R + anchorMult = parentMult`, `anchorMult ≤ 1`);
4. charge-set width explicit — `card_classChargeSet_ge` (`w − s − a₀`) and `deployed_classChargeSet_width` (`≥ 69632`);
5. official witness semantics — `official_anchor_semantics`, `branchAB_official_selection`;
6. branches audited separately — `branchA_audit`, `branchB_audit`, `branchC_audit`, `branchD_audit`;
7. branch C's `m ≤ 6` is proved *equivalent* to `#(posBadSet \ {γ₀}) ≤ 6`, i.e. circular; it is used nowhere in the composition;
8. branch D uses the exact anchor quantifier theorem (every bad challenge is itself an anchor challenge);
9. termination ≠ cost bound — new theorem `descent_does_not_bound_load`: a presentation with a strict complexity drop on every edge whose captured load is unbounded.

Also proved numerically: `2097152 = 1048576 + 978944 + 69632` and `978944 + 1 + 978944·19559298652205332/69632 ≤ 274980728111395087` (slack 4).

## The one smallest remaining obstruction

> Exhibit a numeric value for the external majorant at the deployed root: an independently defined `Ψ` satisfying the root inequality with `Ψ(X₀) ≤ 19559298652205332` — equivalently, prove `capturedChildCost 1048576 978944 A f₀ f₁ an.chal ≤ 19559298652205332`, i.e. bound `Σ_R μ_R·Φ(R)` by that number.

With it, `deployed_bound_of_root_majorant` (or `deployed_bound_of_capturedChildCost`) yields `#Bad ≤ 274980728111395087` immediately. Nothing else is missing in the composition.

Johnson, sunflower, FFT, M31 and generic incidence theory were not reopened.


# Summary of changes for run dcb8e7e4-97ea-4435-a1ec-2590a3f5a7d6
## 1. Artifact delivered (and canonically replayed)

Portable package: `ARISTOTLE_GLOBAL_LOAD_GATE_PACKAGE.zip` (identical plain-text tree in `package/global_load_gate_replay/`, 37 files, 24 Lean modules).

Contents: `COMMIT.txt` (`3ae4247c000b5609ed0f1b8cab1e710423cdc617`); full transitive project-import source closure under `src/` — including `Root/CodingTheory/GlobalAnchorRecursion.lean`, `Root/CodingTheory/GlobalRecursionLoadGate.lean`, `Root/CodingTheory/GlobalRecursionBranchGaps.lean` and all three axiom-audit files (`GlobalAnchorRecursionAxiomAudit`, `GlobalRecursionLoadGateAxiomAudit`, `GlobalRecursionBranchGapsAxiomAudit`); `GLOBAL_LOAD_GATE_REPLAY_REPORT.md`; `GLOBAL_RECURSION_COMPOSITION_REPORT.md`; `REPLAY_BUILD.log`; `REPLAY_AXIOMS.txt`; `MANIFEST.md` (dependency manifest: module, file, line count, full SHA-256); `SHA256SUMS.txt` (digest of every packaged file, verified with `sha256sum -c`); `lakefile.toml` / `lean-toolchain` / `lake-manifest.json`; `README_REPLAY.md` (step-by-step replay instructions).

Canonical replay actually performed in the project (not reused from the earlier report):
`lake build RequestProject.GlobalAnchorRecursionAxiomAudit RequestProject.GlobalRecursionLoadGateAxiomAudit RequestProject.GlobalRecursionBranchGapsAxiomAudit` → success (8049 jobs), 67 `#print axioms` lines, every list ⊆ `{propext, Classical.choice, Quot.sound}`; the source closure contains no `sorry`/`admit`/`axiom`/`implemented_by` in code. Only the audit roots and the one newly added module were built. **Replay: BANKED** — for the Lean statements exactly as written (conditional statements stay conditional; see the table).

## 2. Table

Full per-theorem table (67 rows: name, exact signature, source file, replay result, axioms, hypotheses, status) is in `GLOBAL_LOAD_GATE_REPLAY_TABLE.md`, with a verbatim "Exact signatures" section. `BANKED` = replayed, sorry-free, standard axioms; `CONDITIONAL` = replayed but the statement carries an unproved hypothesis (`hload`/`hgate`, or `m ≤ 6`).

## 3. The four remaining goals, separated (`GLOBAL_LOAD_GATE_REMAINING_GOALS.md`)

| goal | content | status |
|---|---|---|
| A | full class-level recursive load bound (`classLoad … i ≤ 19559298652205332`) or a priced high-load descent | **OPEN** — the single obstruction; `deployed_load_gate` is a reduction only. Available: `classLoad_charging`, `classLoad_bound`, `sum_classLoad_eq`, `heavy_load_yields_class_family`, `loaded_class_is_residual_child`; missing: the paying half |
| B | branch-C cost closure, incl. the missing "total child multiplicity ≤ 6" | **multiplicity theorem settled, negatively**; cost closure **OPEN** |
| C | branch-D quantifier proof | **CLOSED** (`badSet_eq_empty_of_no_anchor` + `anchor_at_every_bad_challenge`) |
| D | exact compatibility of branches A/B with official witness semantics | **CLOSED under `IsOfficialAnchor`**, which is shown to exist at every positive-mass bad challenge; canonical selection of an official minimal-mass anchor remains open |

New sorry-free module `RequestProject/Root/CodingTheory/GlobalRecursionBranchGaps.lean` (11 declarations, all axiom-audited):

- Goal B: `sum_capturedMult_eq_card` proves the total captured child multiplicity equals `#(posBadSet \ {γ₀})`; `totalCapturedMult_le_iff` makes the bound `Σ μ_R ≤ m` *equivalent* to a bad-set cardinality bound, and `branchC_multiplicity_six_forces_tiny_badSet` shows the branch-C hypothesis `m ≤ 6` forces `#posBadSet ≤ 7`. So the requested missing theorem is not a structural branching fact — assuming it assumes a bad-set bound of the kind the recursion is meant to derive, and branch C cannot be closed this way.
- Goal D: `IsOfficialAnchor`, `anchor_isOfficialWitness`, `exists_official_anchor`, `officialClass_eq_of_officialAnchor`, `anchorMass_eq_official_of_officialAnchor`, `supp_eq_officialSupport_of_officialAnchor`, `chargeSet_anchor_eq_of_officialAnchor`.

No broad theory construction was continued; the modular file layout was kept (one new theory module plus its own audit module), and no unmodified module was rebuilt beyond what the audit roots require. All work is committed.


# Summary of changes for run 2eda0e45-f791-4b67-af99-a1a5a3c7b6a7
Done. Work is committed; details are in `GLOBAL_LOAD_GATE_REPLAY_REPORT.md`.

**Phase 0 — export and replay.** The full transitive project-import closure of `GlobalAnchorRecursion` (20 modules), its axiom-audit file, the composition report, `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, the exact commit hash `3ae4247c000b5609ed0f1b8cab1e710423cdc617` and a dependency manifest with per-file line counts and SHA-256 digests were exported to `historical_import/global_anchor_recursion_3ae4247/`. No canonical source was overwritten. In the canonical project the exact modules were rebuilt (`lake build RequestProject.GlobalAnchorRecursionAxiomAudit`, 8045 jobs, clean), `#print axioms` was re-run on all 38 exported theorems (every list a subset of `propext`, `Classical.choice`, `Quot.sound` — logs saved as `REPLAY_BUILD.log` / `REPLAY_AXIOMS.txt`), the closure was scanned for `sorry`/`admit`/`axiom`/`implemented_by` (19 textual hits, all inside doc comments; none in code), theorem signatures were extracted, and the imported interfaces were compared with the canonical Grand MCA definitions (all inherited unchanged, no shadowing). Source-level replay: BANKED.

**Phase 1 — four-branch audit.** New sorry-free file `RequestProject/Root/CodingTheory/GlobalRecursionLoadGate.lean` with its own axiom audit (18 declarations, standard axioms only).
- Branch D: valid — `anchor_at_every_bad_challenge` proves every bad challenge is itself an anchor, so the "no usable anchor" hypothesis is existential over the complete bad family.
- Branch A: the zero-uncaptured lemma's hypothesis is a zero explanation and terminality is proved from official witness semantics — but the branch label `a₀ = 0` is not enough: `anchorMass_eq_zero_iff` and `exists_zero_mass_nonzero_poly` separate mass zero from terminality, and `branchA_massZero_recurrence` keeps the uncaptured term in that case.
- Branch B: `chain_descent_cost_bound` supplies the explicit potential inequality (cost ≤ L·(rad+1)) that the strict child decrease alone does not give.
- Branch C: objection sustained. `radius_drop_not_a_cost_bound` proves a radius inequality alone never bounds cost; `radius_descent_cost_bound` gives its exact price (`cost ≤ L·Σ_{j≤rad/d} m^j`) and `branchC_deployed_bound_of_branching` the deployed terminal bound, valid only for total child multiplicity ≤ 6 (`branchC_deployed_seven_exceeds` shows 7 breaks it). That multiplicity bound is not established, so the branch-C cost clause stays open.

**Phase 2 — the load gate.** The exact canonical load is defined as `classLoad`: a sum over the disjoint family of distinct captured child classes, with a canonical per-class representative fixing the charge set, class-level captured multiplicity μ_R and full recursive child cost Φ(R); no support-, challenge- and class-level multiplicities are mixed. Proved: the double-counting identity, the charging inequality `(w−s−a₀)·Σ_R μ_R·Φ(R) ≤ Σ_{i∉S0} load(i)`, the load bound `≤ e·M`, the recurrence, and the reduction `deployed_load_gate`: `load_X(i) ≤ 19559298652205332` implies `#Bad ≤ 274980728111395087`. No circular `μ_R·C(R) ≤ M` assumption is used, and the threshold theorem is not claimed proved.

**Remaining.** Target A (the unconditional load bound) is open; the structural half of Target B is proved (`heavy_load_yields_class_family`, `loaded_class_is_residual_child`: an over-loaded coordinate is carried by an explicit family of residual child classes of strictly smaller complexity, of total weight exactly the load), the paying half is not. The single minimal obstruction is the class-level spread statement in §5 of the report: for every coordinate outside the anchor support, the total weight `Σ μ_R·Φ(R)` of canonically assigned classes whose representative charge set contains it is at most 19559298652205332. The existing double counting only produces a concentrated coordinate carrying a ≈1/14.06 fraction — a lower bound on the worst load, not an upper bound.

# Summary of changes for run 0eae2a42-da15-4fc2-9864-08b5fbd14d44
Built the global recursion/composition layer requested, on top of the existing local geometry (which was not rebuilt).

**Replay discipline.** Nothing was taken on report. The inherited layer was re-built from source (`lake build` of the mass-descent module), its axiom audit was re-run (only `propext`, `Classical.choice`, `Quot.sound`), and a dependency audit over the full transitive project-import closure (19 modules) confirmed no `sorry`, `admit`, `axiom` or `@[implemented_by]`. Only after that are its interfaces (canonical residual child, exact fibres, official witness transport, strict decrease) reused.

**New Lean file** `RequestProject/Root/CodingTheory/GlobalAnchorRecursion.lean`, with axiom audit `RequestProject/GlobalAnchorRecursionAxiomAudit.lean` (38 declarations, standard axioms only, no `sorry`); build verified.

1. *Global cost and potential, explicit*: `Cost(X) = localCost(X) + Σ_R μ_R·Φ(R)` (`globalCost`), `capturedCost(A) = Σ_{R∈A} μ_R·Φ(R)`, with proved disjointness algebra (`capturedCost_add_uncaptured`, `capturedCost_union_of_disjoint`, and only `≤` without disjointness). Composition happens solely through the quantitative certificate `GlobalCertificate` whose target is the safe local inequality `localCost X + capturedCost(A) + Σ_{R∉A} μ_R·Φ(R) ≤ Φ(X)`; `GlobalCertificate.sound` gives `cost ≤ Φ`.
2. *Descent is not a bound*: `strict_descent_not_a_cost_bound` exhibits an exact one-step recursion with strict decrease along every child edge and unbounded cost — so every branch supplies an explicit numerical decrease.
3. *Anchors of arbitrary mass*: `AnchorData` (challenge + degree-`<k` explanation on a support of size `≥ |D|−e`), mass `a₀` not assumed zero. The charge width is derived, not postulated: `card_chargeSet_ge_anchor` proves `w − s − a₀ ≤ |D_γ|` from the official support definitions plus exact challenge transport; the exact charge set is `(S_γ∖A)∖S0` (`mem_chargeSet_iff`).
4. *Four exhaustive branches* (`anchor_branch_exhaustive`, `globalAnchorMaster`), each with anchor-existence condition, exact charge set, proved width, canonical child classes, exact fibre multiplicities (`capturedMult + anchorMult = parentMult`), full recursive child weight, disjoint captured/uncaptured partition (`totalChildCost = capturedChildCost + uncapturedChildCost`) and recurrence: A (`a₀ = 0`, width `w−s`, uncaptured term proved zero for a terminal anchor, `#Bad ≤ (e+1) + e·M/(w−s)`); B (`0 < a₀ < w−s`, width `w−s−a₀ > 0`, `#Bad ≤ (e+1) + e·M/(w−s−a₀) + uncapturedCost`, the uncaptured child proved strictly smaller); C (`a₀ ≥ w−s`, width provably zero, no concentration applied — instead the independent large-anchor theorem `resRad + (w−s) ≤ e`, globally for all children in the large-mass regime); D (no usable anchor ⇒ bad set empty). Concentration is derived by double counting from the actual weighted charge sets and only under a positive proved width.
5. *Deployed* (`n=2097152, k=1048576, e=978944, w=69632, s=0`): `deployed_safe_local_target` and `deployed_global_budget` — a uniform per-coordinate charge load `M ≤ 19559298652205332` (the exact threshold) forces `#Bad ≤ B* = 274980728111395087`. The number `⌊B*·w/e⌋ = 19559298652274964` is recorded as arithmetic only (`deployed_pure_child_mass_number`) and nothing is derived from it; no circular congestion cap is used, and no separate load term is added on top of `capturedCost(A)`.

**Return: case 2 — exactly one remaining inequality.** All structural work above is closed and sorry-free; the single open obligation is the uniform per-coordinate charge-load bound `M` (equivalently, ruling out the concentration alternative — a spread statement about official supports, fraction `1/14.06` at the deployed point). It appears as an explicit hypothesis everywhere it is used and is claimed nowhere.

Clause-by-clause status marking (BANKED / open) is written up in `GLOBAL_RECURSION_COMPOSITION_REPORT.md`. All work is committed.

# Summary of changes for run d449662a-f61f-4514-be69-1c8bb7bfa745
Continuing from `TauWindowClassification`, I built the two missing objects — the family-level residual recursion (`BranchingControl`) and the mass-descent theory with full recursive child cost and anchor charging (`MassDescentRecursion`). Everything is proved: the whole project builds, no `sorry`, and both new files are axiom-audited (only `propext`, `Classical.choice`, `Quot.sound`).

**1. `RequestProject/Root/CodingTheory/BranchingControl.lean` — the canonical family-level recursion.**
For a positive-mass official witness `p` (deg `< k`, support `≥ t = n−e`), the canonical residual child class is `Z = windowZeros A p = {x ∈ A : p(x)=0}`, `|Z| = tauMax − a`. It determines the child completely: domain `D ∖ A` (`n₁ = n − tauMax`), dimension `k₁ = k − |Z| = a − s`, radius `e₁ = e − a`, words `f_i / V_Z` (`V_Z` the vanishing polynomial of `Z`, nonzero off the window), so the shortened code `V_Z·RS_{k₁}` becomes an ordinary `RS_{k₁}(D∖A)` — the child is an instance of the same problem. Proved: exact witness transport (`p = V_Z·r`, `deg r < k₁`, residual line point `= r` on the exact residual support of size `|S∖A| ≥ n₁−e₁`); the child is again *bad* (`mem_resBadSet_of_positiveMass`, the negative half of badness recovered from window maximality); `w` preserved (`n₁ = k₁+e₁+w`); strict descent (`e₁ < e`, `k₁+e₁ < k+e`) with base case `e = 0 ⇒ #Bad ≤ 1`; fibring with explicit multiplicity (`#children ≤ Σ_{j∈[tauMax−e,k)} C(tauMax,j) ≤ 2^tauMax`); canonicity of `Z` under `k+2e ≤ n`; and the target theorem `branchingControl_master`: `#Bad ≤ (e+1) + Σ_child cost(child)` together with the trichotomy `#Bad ≤ (e+1)+N·L ∨ N < #children ∨ ∃ child certificate` (`BranchingCertificate`: one child, same `w`, strict descent, large fibre), instantiated at the deployed point.

**2. `RequestProject/Root/CodingTheory/MassDescentRecursion.lean` — full recursive child cost, exact multiplicities, charging.**
A choice-fixed `officialWitness` makes the child class a function of the challenge, so multiplicities are exact: the fibres partition the positive-mass bad set, `#Bad⁺ = Σ_R μR`, `totalChildCost = Σ_R μR·C(R)` (`C(R)` = the child's *own* bad-set cardinality, i.e. the full recursive cost), and `μR ≤ C(R)` since each fibre lies in that one child's bad set — no double counting. Hence `#Bad ≤ (e+1) + Σ_R μR·C(R)`, strictly stronger than bounding `Σ μR`.
With an anchor challenge of window mass `0` and support `S0` (`|S0| ≥ t`), each positive-mass challenge charges `D_γ = (S_γ∖A)∖S0` with `|D_γ| ≥ w−s` (from `|S_γ∖A| ≥ (w−s)+a` and exact challenge transport `|(S_γ∩S0)∖A| ≤ a`), all inside a set of at most `e` coordinates. Weighted double counting gives the primary target `(w−s)·Σ_R μR·C(R) ≤ Σ_{i∉S0} load(i) ≤ e·M_X`, hence the closed/potential form `#Bad ≤ Φ = (e+1) + e·M_X/(w−s)`; the abstract amortisation theorem `cost_le_potential` (potential dominating cost along a well-founded complexity) is proved separately. Deployed: `69632·(#Bad − 978945) ≤ 978944·M_X`, and `M_X ≤ 19·10¹⁵` already forces `#Bad ≤ B* = 274980728111395087`.
The `#children × max child cost` route is never used, and `e` is not assumed to drop by `w`.

**The exact minimal obstruction (proved unconditionally).** `exists_concentrated_coordinate`: for `0 < w−s`, either `#Bad ≤ e+1` (terminal), or *some single coordinate outside the anchor support carries a `(w−s)/e` fraction of the entire recursive cost* (deployed: `1/14.06`). Since `load(i) ≤ totalChildCost` holds trivially, the recurrence is summable exactly when the per-coordinate recursive load is bounded away from the total — i.e. what remains is a spread statement for official supports, not a counting statement. All conditional results carry the load bound as an explicit hypothesis; the anchor must be a genuine zero-mass challenge (with mass `a₀` the charge only reaches `(w−s)−a₀`), and this is recorded as a non-claim.

Documentation: `BRANCHING_CONTROL_REPORT.md`, `MASS_DESCENT_RECURSION_REPORT.md`, new sections §137 and §138 in `RESULTS.md`, and audits `RequestProject/BranchingControlAxiomAudit.lean`, `RequestProject/MassDescentRecursionAxiomAudit.lean`. All work is committed.

# Summary of changes for run 1126a0fb-8518-4386-9517-ec64bcefed1b
## What I did

I classified the narrow `τ`-window (`k ≤ τ = k+s < n−e`, width `w = n−k−e = 69632` at the deployed point) by introducing one new invariant, and delivered both halves of what you asked for: an `F(n,k,e,s)` bound where one exists, and a canonical residual descent for the complementary branch. I deviated from the literal instruction in one place, which I think was the bigger win: instead of chasing a single `F` for the whole window (which I show is impossible in that shape), I split the window by a canonical invariant and got a sharp, attained bound on one branch and an exact, dimension-reducing descent on the other. No Johnson/second-moment input is used for the main results.

**New sorry-free Lean** (`RequestProject/Root/CodingTheory/TauWindowClassification.lean`, `TauWindowExtremal.lean`; audit `RequestProject/TauWindowClassificationAxiomAudit.lean` — 33 declarations, only `propext`, `Classical.choice`, `Quot.sound`). The whole project still builds; nothing banked was rebuilt.

**1. The gauge.** `τ` and the bad set are invariant under subtracting codewords (`rsTau_sub_poly`, `isBad_sub_poly`), so every line can be normalised: a window `A` with `f₀ = f₁ = 0` on `A` and `|A| = τ` maximal. Then `A` *is* the common zero set, so every position outside `A` pins at most one challenge, and (`eq_of_two_challenges_same_window`) every witness window pins at most one challenge.

**2. The invariant — window mass** `a(p) = #{x ∈ A : p(x) ≠ 0}`, the errors a challenge must spend inside the correlated window. `isBad_dichotomy`: a bad challenge is either zero-witness (`a = 0`, equivalently the witness codeword is `0`) or has `s+1 ≤ a ≤ e`, with agreement `≥ (w−s)+a` outside the window. Exact challenge transport: `|(S ∩ S′) ∖ A| ≤ a + a′`.

**3. The theorem (zero-witness branch).** Disjointness of the zero sets outside `A` gives `#Bad₀·(w−s) + τ ≤ n`, i.e.

  `F(n,k,e,s) = (n−k−s)/(w−s) = 1 + e/(w−s) ≤ e+1`,

so `F ≤ B*` throughout the deployed range: `≤ 15` at `s = 0`, `≤ 978945` for every `s < 69632`, against `B* ≈ 2⁵⁷·⁹`.

**4. Beyond mass zero.** `card_le_of_massBounded`: a counting on the *residual* window with the mass-weighted transport (not the globally empty second-moment branch) gives `#B·(W² − n·2a) ≤ n·W` for challenges of mass `≤ a`; deployed: `≤ 223` for all bad challenges of window mass `≤ 1000` (method valid up to `a ≤ 1156`).

**5. The residual descent.** A positive-mass witness is divisible by the vanishing product of the `τ−a` window positions off its mass, with quotient of degree `< a−s`. The residual instance on `Aᶜ` is `(n₁,k₁,e₁) = (n−τ, a−s, e−a)` with `n₁ = k₁+e₁+w`: the capacity gap is preserved exactly while the dimension drops to `a−s ≤ e−s < k` (deployed `e < k`) — a well-founded descent in code dimension at constant gap. `tauWindow_master` packages all of this for an arbitrary line.

**6. Sharpness and necessity, machine-checked.** An explicit line over `ZMod 5` (`n=5, k=1, e=2, τ=2, s=1`) has zero-witness bad set of size exactly `3` — the bound `(n−k−s)/(w−s) = 3` is attained — while its full bad set has at least `4`. So `(n−k−s)/(w−s)` is **false** as a bound for the whole bad set: the branch split is necessary, not an artefact.

**Honest scope.** No bound is claimed on the high-mass branch, and I record why: above the stated mass threshold the pairwise data is satisfiable by arbitrarily large families, so any further progress must use the shortened-code structure of the descent rather than counting over windows. Exploratory numerics (`analysis/tau_window_lines.py`, `tau_window_growth.py`, `tau_window_scan.py`, exhaustive over all lines for small parameters, not part of the formal record) indicate the shape is right: for `w ≥ 2` the maximum of `#Bad` in the window is small and field-independent, while at `w = 1` (exactly at capacity) it grows with the field up to the number of windows — so any true `F` must degrade as `w → 1`, exactly as `w−s` in the denominator does.

Narrative: `TAU_WINDOW_CLASSIFICATION_REPORT.md`; `RESULTS.md` §136; `INDEX.md` regenerated with the repository script. The Properties table lists the new deliverables (two definitions, six proved theorems). All work is committed.

# Summary of changes for run cd8c397c-8f78-4f01-8d83-df71feffce92
## What I did

I looked for the strongest *general* theorem turning a large bad-challenge family into a quantitative global bound, and found that the right canonical object is the **maximal correlated agreement** of a line,

  τ(f₀,f₁) = max { |{x : f₀ x = q₀ x ∧ f₁ x = q₁ x}| : q₀, q₁ codewords },

i.e. the largest window on which the *pair* is simultaneously explained by a pair of codewords. All results live in one new sorry-free module, `RequestProject/Root/CodingTheory/MaximalCorrelatedAgreement.lean` (634 lines), with axiom audit `RequestProject/MaximalCorrelatedAgreementAxiomAudit.lean` (46 declarations, only `propext`, `Classical.choice`, `Quot.sound`). The whole project still builds clean; nothing existing was rebuilt — the set-family engine, the two-witness pair construction and the pinning branch are reused as they stand.

**1. Master counting theorem (arbitrary linear code, arbitrary field, arbitrary alphabet module — so interleaved/folded codes are covered).** For any family `B` of challenges each carrying a window of size `≥ t` on which the line point is explained by a codeword, and any bound `c` on the correlated agreement of codeword pairs with the line,

  #B · (t² − N·c) ≤ N·t,  N = |Ω|,

with the instance `c = τ`, the divided form `#B ≤ N·t/(t² − N·τ)`, the Reed–Solomon form for the project's official bad set, and the `ε_mca` form. The pairwise input is *forced*, not assumed: two witnesses at γ ≠ γ′ build the codeword pair that correlates with the line on their whole common window. No noncontainment, distance, rate or window hypothesis is used.

**2. τ is a canonical invariant, and it *is* correlated agreement.** τ is unchanged when codewords are added to f₀ and f₁ (so it depends only on the residual plane), is symmetric, and is attained. Moreover a window of size `s` carrying the whole line exists **iff** `s ≤ τ` — so the mutual-correlated-agreement conclusion at radius `e` is literally `|D| − e ≤ τ`, both for arbitrary linear codes and in the project's Reed–Solomon `LineCloseOn` formulation.

**3. The master reduction.** Since `k ≤ τ` always (interpolate both words on the same `k` positions), *every* line either satisfies the MCA conclusion outright, or has `k ≤ τ < |D| − e` — a window whose width is exactly the capacity gap `|D| − k − e`.

**4. Strictly sharper than the repository's previous far branch,** which is the special case `c = k+e−1`; with the exact invariant the mechanism's ceiling becomes the *full* Johnson condition `(1−δ)² > ρ` instead of `(1−δ)² > ρ + δ`. This is exhibited concretely: at rate 1/2, |D| = 2²⁰, e = 300000 (δ ≈ 0.286, past the old ceiling 0.177), every line with minimal τ = k has at most **73** bad challenges, while the old branch is provably inapplicable there.

**5. The precise obstruction at the deployed point** (|D| = 2²¹, k = 2²⁰, e = 978944, δ = 0.4668). Machine-checked: the second-moment branch is *empty* there, because `k ≤ τ` and `|D|·k − t² = 948634124288 > 0`. So the deployed gate is exactly one statement about one invariant: bound `#Bad` for lines with `1048576 ≤ τ < 1118208` (width 69632 = the capacity gap). The pinning branch still yields `#Bad ≤ e+1 = 978945`, far below the budget, but only for `τ ≥ k+e`, which is above the correlated-agreement threshold and hence adds nothing inside the window. The remaining gap is therefore not proof engineering: any Johnson/second-moment argument needs `δ < 1 − √ρ ≈ 0.2929`, and the deployed radius is 0.4668 — the beyond-Johnson regime.

Narrative: `MAXIMAL_CORRELATED_AGREEMENT_REPORT.md`; `RESULTS.md` §135; `INDEX.md` regenerated with the repository script. The Properties table lists the nine new deliverables (two definitions, seven proved theorems).


# Summary of changes for run 56767b89-59fa-4598-9c36-198b55961fa4
## Result: one unconditional dichotomy, with `B* = e + 1`

New module `RequestProject/Root/CodingTheory/BadSupportCoveringTriple.lean` (sorry-free; audit `RequestProject/BadSupportCoveringTripleAxiomAudit.lean`, 36 declarations, only `propext`, `Classical.choice`, `Quot.sound`; the whole project still builds). Narrative: `SUPPORT_COVERING_TRIPLE_REPORT.md`, `RESULTS.md` §134, `INDEX.md` regenerated with the repository script. Nothing banked was rebuilt or extended: the existing `Res`/shortening/gluing-defect/duality/interleaving layers are used as they stand.

**The object.** A *bad-support family* is a finite set of challenges together with a chosen official bad support for each (`|Sᶜ| ≤ e`, explains its own point of the line, not the whole line); every finite set of officially bad challenges carries one, so results apply to the official `badSet`. A window is *support-covering* when `Short(C, Sᶜ) = ⊥` — no invisible core outside it, equivalently it contains an information set.

**The engine (unconditional).** One codeword line `γ ↦ p₀ + γ·p₁` explains at most `|(supp γ₀)ᶜ| + 1 ≤ e + 1` challenges of the family, for *every* member `γ₀` of that class. A challenge explained by the line must disagree with it somewhere on its own support (else the support would explain the whole line); that position determines the challenge, so the disagreement positions are distinct and all lie outside every other support of the class.

**The dichotomy (unconditional; arbitrary linear code, arbitrary alphabet).** Either `#chal ≤ e + 1`, or three pairwise distinct challenges of the family fail to be support-covering, with an explicitly exhibited nonzero `z ∈ Short(C, (S₁∩S₂∩S₃)ᶜ)` of weight `≤ 3e`. No window condition `e·|B| + k ≤ n`, no rate, distance or non-degeneracy hypothesis, no bound on the family size. Both branches are effective; `z = c₃ − (p₀ + γ₃p₁)` is produced from the pair solve at `γ₁ ≠ γ₂`.

**Finite-cost branch.** `NoCore C (3e)` (no nonzero word of weight `≤ 3e`, in particular `3e < d`) gives `#Bad ≤ e + 1` for the official bad set — strengthening the previously available `#Bad ≤ n` at the same hypothesis and in the same generality, and with no window hypothesis. Consequences: `ε_mca ≤ (e+1)/|F|`, and `≤ 2⁻¹²⁸` once `(e+1)·2¹²⁸ ≤ |F|`. Covering and `NoCore` are interleaving invariants, so the interleaved code `C^⋈κ` (the shape of the deployed extension-field instance) inherits `B* = e+1` from the base code.

**Other readings of the covering condition.** Dual/kernel-shadow via the complementary-window identity (`dim Short(C^⊥,S) = |S| − dim C`); matroid form (a non-covering window contains no information set, two distinct codewords agree on it); `Res` form (the Lost-filtration of `⊥ ≤ C` has not jumped at the complementary window); MDS/RS regime (`k + 3e ≤ n` makes every triple covering).

**Structural branch — "no covering triple" converted into structure.** Strongest parametric statement: either `#chal ≤ e + 1`, or the first jump `δ₁` of the `Res`-filtration of `⊥ ≤ C` (the code's minimum weight) is `≤ 3e`; the minimal window realising it has size `≤ 3e`. Charging: under `NoCore C e` the three complementary windows have exactly additive budgets, `dim Short(C, W₁∪W₂∪W₃) = gluingDefect C W₁ W₂ + gluingDefect C (W₁∪W₂) W₃`, and a failed triple forces that sum `≥ 1`.

**Honest limits.** The structural branch gives no cardinality bound, and none of this shape can hold there: the banked gap witnesses show `2e < d` alone does not give `#Bad ≤ e + 1`. So `NoCore C (3e)` is the exact frontier of the `B* = e+1` branch for this argument, and the returned obstruction is the minimal one — a nonzero codeword of weight `≤ 3e` in the complement of a triple intersection of official bad supports. No list-decoding argument is used; MDS statements assume a one-dimensional alphabet and the dual statements are for `A = F`. All work is committed.

# Summary of changes for run 1b4a44b6-dbf3-4a53-bc32-e7418aaf5ffc
## What was done

I read the attached ArkLib bundle as ground truth (all six files inspected; ArkLib is a separate Lean package and is not importable here, so the declarations that were needed are mirrored, with the source quoted and the correspondence recorded file by file). Then I proved four new sorry-free Lean modules, all building against the existing residual (`Res`) theory, which was reused and not rebuilt. Every headline theorem was axiom-audited: only `propext`, `Classical.choice`, `Quot.sound`. The full project still builds.

**A — `[INTERLEAVING-RES FUNCTORIALITY]`** (`RequestProject/Root/CodingTheory/InterleavedResidual.lean`). Interleaving is an injective lattice map on codes that *fixes* the window subspace; from that single fact: `Short(C^⋈κ,W) = Short(C,W)^⋈κ`, `Lost(C^⋈κ,E^⋈κ,W) = Lost(C,E,W)^⋈κ`, and the top target as a **commuting diagram** — the canonical ambient isomorphism `(ι→κ→A)/C^⋈κ ≃ κ → ((ι→A)/C)` carries `Res(C^⋈κ,E^⋈κ,W)` exactly onto `Res(C,E,W)^⋈κ` (packaged as a linear isomorphism). Consequences proved: the restriction-kernel description is interleaved; `dim Res` and the gluing-defect budget scale by `|κ|` (jump positions unchanged); terminal windows are unchanged; and projection commutes with interleaving, which specialises to ArkLib's `projectedCodeSubmod_moduleInterleavedCode_iff`.

**B — `[EXACT K/F_p CHALLENGE TRANSPORT]`** (`ExtensionChallengeTransport.lean`). For `K/F` of degree `d` (deployed `d = 6`), `Interleave(f₀ + r•f₁) = Interleave(f₀) + M_r · Interleave(f₁)` exactly, with one matrix `M_r` at every symbol; `r ↦ M_r` is an injective algebra map, and for `f₁ ≠ 0` the interleaved challenge line has base-field dimension exactly `d` (so not an `F`-line for `d ≥ 2`): the single `K`-challenge is never six independent base-field challenges. The extension code is identified with ArkLib's interleaving at `κ = Fin d` and is stable under `r • ·` — the stability proof *is* the `M_r` transport. Combining A and B: `Res(C⊗K, E⊗K, W) ≃ Res(C,E,W)^d`.

**C — `[COMPLEMENTARY-WINDOW DUALITY]`** (`ComplementaryWindowDuality.lean`). Dual-code theory built from scratch, then the Wei-type relation in its strongest form, an equality of subspaces with no dimension count: `Lost(C,E,W)^⊥ = Lost(E^⊥,C^⊥,Wᶜ)`. In residual form the dual object on `Wᶜ` is exactly the annihilator, inside `C^⊥`, of the words of `E` supported in `W` (with elementwise mutual annihilation): the pairing between `Res(C,E,W)` and `Res(E^⊥,C^⊥,Wᶜ)` is perfect. Numerical shadow: `dim Res(C,E,W) + dim Res(E^⊥,C^⊥,Wᶜ) = dim E − dim C`; structural corollary: `TerminalWindow C E W ↔ Res(E^⊥,C^⊥,Wᶜ) = ⊥`.

**D — partial, honestly scoped.** `ResidualClass` / `ModularDefect` and their primal/dual pairing are not in this repository and were not among the supplied sources, so no faithful bridge to them could be formalised (inventing a definition under that name would prove nothing about the intended object). What is grounded and proved is the part living on this side: the exact gluing-defect budget of the `Res`-filtration *equals* the dual complementary-window obstruction, and vanishes exactly when the complementary window subspaces distribute over the dual code ("zero class ↔ gluing").

**E — ArkLib final wrapper** (`ArkLibGrandMcaWrapper.lean`). The minimal missing chain in three links: `#Bad ≤ B*` ⟹ error `≤ B*/|F|`; `B*/|F| ≤ 2⁻¹²⁸` whenever `B*·2¹²⁸ ≤ |F|` (with the deployed sextic instance); and the boundary dichotomy `allGood | boundary` with uniqueness of the crossing index, passing to the ArkLib-shaped challenge disjunction. Composite: from `#Bad ≤ B*` to official SAFE. The only ArkLib-internal fact used (the uniform-probability semantics of its `Pr`, whose defining file is not in the bundle) is an explicit hypothesis, never a silent assumption.

A full write-up, including the ArkLib mirror table and the scope limits, is in `GRAND_MCA_INTERLEAVING_DUALITY_REPORT.md`. Strongest single result returned: `[INTERLEAVING-RES FUNCTORIALITY]`, with `[EXACT K/F_p CHALLENGE TRANSPORT]` and `[COMPLEMENTARY-WINDOW DUALITY]` proved alongside it.

# Summary of changes for run 9efe6742-b8a4-4400-82c0-e6b23e3fa69b
## Outcome: a canonical residual object for the Lost-filtration, with the previous rank-two results as corollaries

Four new Lean files (all `sorry`-free, all axiom-audited to only `propext`, `Classical.choice`, `Quot.sound`; the whole project still builds):

- `RequestProject/Root/CodingTheory/LostFiltrationResidual.lean`
- `RequestProject/Root/CodingTheory/LostFiltrationResidualTriple.lean`
- `RequestProject/Root/CodingTheory/LostFiltrationResidualDescent.lean`
- `RequestProject/Root/CodingTheory/LostFiltrationResidualMDS.lean`
- audit: `RequestProject/LostFiltrationResidualAxiomAudit.lean`; narrative: `GRAND_MCA_RESIDUAL_CLASS_REPORT.md`, new section 133 in `RESULTS.md`.

**The object.** For nested codes `C ≤ E` and a window `W`, `Res(C,E,W)` is defined as the image of the Lost stage in the *fixed* ambient quotient `(ι → A)/C` — a submodule, with no absorbed representative chosen; `Lost` is recovered by `comap`.

**A. Canonical quotient theorem.** `Lost(C,E,W)/C ≅ Res(C,E,W)` (unconditional) and `Short(E,W)/Short(C,W) ≅ Res(C,E,W)` (only `C ≤ E`), hence the comparison isomorphism of the universal exact sequence. `Res` is characterised by a universal property: with the canonical surjection it is the cokernel of `Short(C,W) → Short(E,W)`, so every linear invariant of window-supported words of `E` that ignores the invisible cores factors uniquely through it. A third description is proved equal: `Res` is exactly the part of `E/C` killed by restriction to the complement of the window (the lost-direction/restriction-kernel object). The rank-two lost directions are the pullback of `Res` under the pencil map, and the absorbed-core family is nonempty exactly when `Res = E/C` — a torsor presentation of the same invariant, not identified with it.

**B. Functorial filtration.** In the window variable the residual classes are an increasing filtration of `E/C` by submodules of one fixed module (transitions are inclusions, hence injective), from `⊥` to `E/C`, meet-preserving exactly modulo invisible cores. In the code variable, a tower `C ≤ D ≤ E` gives a short exact sequence `0 → Res(C,D,W) → Res(C,E,W) → Res(D,E,W) → 0` with additive dimensions. `dim Res = dim Short(E,W) − dim Short(C,W)`, so the defect spectrum `δ_j` is the jump sequence of `dim Res(C,E,·)`: the relative weight hierarchy is an invariant of the canonical object.

**C. Exact obstruction theory.** With `gluingDefect M W W' = dim Short(M,W∪W') − dim(Short(M,W) ⊔ Short(M,W'))`: the meet side is always exact, the defect vanishes exactly when the gluing is exact, and the budgets add exactly — `dim Res(W) + dim Res(W') + gluingDefect E = dim Res(W∩W') + dim Res(W∪W') + gluingDefect C`. Nothing else contributes to non-modularity of the residual filtration.

**D/E. Canonical residualization.** Terminal windows (`Lost = E`, equivalently `Res = E/C`) are closed under intersection away from the invisible cores; under a no-core hypothesis a smallest terminal window of bounded size exists, is contained in every other one, and carries a *unique* absorbed residual state. Existence and uniqueness of a rank-minimal residual state therefore hold with no choice; strict descent is not needed in that regime.

**F. MDS/RS classification.** For MDS codes the shortening dimension is exactly `|W| + dim E − n`, giving precisely three residual regimes determined by `|W|` alone: zero-loss (`Res = ⊥`), intermediate (`dim Res = |W| + dim E − n`, proper and nonzero), and absorbed (`Res = E/C`, absorbed state exists in rank two), with the Reed–Solomon instance stated explicitly.

**Deliberately not claimed.** No identification of `Res` with a dual-side kernel-shadow object `K_W`: in the dual picture the natural partner involves the complementary window (a Wei-type duality), so literal equality is not available at this generality and was not asserted. No connection was made to any external exceptional-variety classification, since no exact theorem supporting it was obtained.


# Summary of changes for run eb7bfc24-bf7e-42ad-bcd4-eef2a45d6100
## What I built

I developed the algebraic and categorical structure of the Lost-filtration and the absorbed-core torsor, found the universal theorem the earlier rank-two results were shadows of, and classified the regimes for evaluation codes. Six new Lean modules, all building clean and `sorry`-free, with an axiom audit (`RequestProject/LostFiltrationAxiomAudit.lean`, 77 declarations, only `propext`, `Classical.choice`, `Quot.sound`). Nothing existing was modified or deleted. Discussion: `GRAND_MCA_LOST_FILTRATION_REPORT.md`; narrative entry `RESULTS.md` §132; `INDEX.md` regenerated with the repository script.

* `RequestProject/Root/CodingTheory/LostFiltration.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationSpectrum.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationInformationSet.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationMDS.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationRankTwo.lean`
* `RequestProject/Root/CodingTheory/LostFiltrationTorsor.lean`

### The universal object and exact sequence

For an **arbitrary nested pair of linear codes** `C ≤ E` over an arbitrary alphabet and a window `W`, `lostStage C E W = E ⊓ (C ⊔ P_W)` is a monotone exhaustive filtration of the interval `[C,E]` (an order homomorphism on the lattice of windows, functorial in the pair). The universal exact sequence is `Lost(C,E,W) = C ⊔ Short(E,W)`, i.e. `0 → Short(C,W) → Short(E,W) → Lost(C,E,W)/C → 0`: **the invisible cores are literally the kernel of the filtration.** Rank2, the fixed-shadow pencils and residual absorption all become corollaries of this one sequence.

### The lattice law and its exact obstruction

The filtration is meet-preserving as soon as the subcode hides no invisible core in `W ∪ W'`, and this is sharp: an explicit two-position witness (repetition code inside the full space) has both singleton windows at the top while their intersection is at the bottom. So an invisible core is *exactly* the obstruction to the Lost-filtration being a lattice homomorphism.

### The defect spectrum

The jumps `δ_j = min{|W| : dim Lost(C,E,W) ≥ dim C + j}` form the relative weight hierarchy. A deletion bound (one position costs at most `dim A` dimensions) gives **strict monotonicity** `δ_j < δ_{j+1}` over a field alphabet; two Singleton laws bound them, the elementary `δ_j ≤ n − (dim E − dim C) + j` and — after building **information sets** for arbitrary linear codes from scratch — the **sharp relative law `δ_j ≤ n − dim E + j`**. The two ends are the least weight of a word of `E` outside `C`, and the least window into which `E` collapses.

### Evaluation codes, and the classification of regimes

For a nested pair whose big code is MDS (no hypothesis on the subcode) the spectrum is *maximal*: `δ_j = n − dim E + j`; for Reed–Solomon, `δ_j(RS_k, RS_{k'}) = |D| − k' + j`. For a genuinely rank-two state, `pencilDefect = δ_1` and `jointDefect = δ_2`, so over a field alphabet `pencilDefect < jointDefect` **strictly** — sharpening the previously proved non-strict inequality and showing the **fixed-shadow band is never empty**. The trichotomy is recorded quantitatively (`rank_two_regime_classification`): below the first threshold no window loses a direction, below the second none is terminal, a window at the first carries a single projective point of `PG(1,F)`, and a window at the second carries an absorbed residual state. With information sets the whole picture sits in `pencilDefect ≤ n − dim C − 1 < jointDefect ≤ n − dim C` **with no hypothesis on the code at all**.

### The torsor side

The absorbed-core family is nonempty at a window exactly when the filtration reaches its top there, and its translation module `Short(C,W)²` is the kernel of the same exact sequence — the filtration is the obstruction theory of the torsor, recorded with the strict torsor law.

### Scope

Strict monotonicity, the sharp Singleton law and the information-set construction assume a one-dimensional alphabet (which covers all evaluation codes); everything else is stated for arbitrary alphabets. No performance or implementation claim is made. All work is committed and pushed.

# Summary of changes for run 61326f84-2a62-4c92-80a8-e98e94950326
## What I built: the algebraic structure of absorbed-core families

I answered the central question — *what is the intrinsic algebraic structure of a family of absorbed invisible cores inside one residual rank-two state?* — and the answer is **a torsor over a module, not a scalar**. Six new Lean modules, all building clean and `sorry`-free, with an axiom audit (`RequestProject/AbsorbedCoreAxiomAudit.lean`: only `propext`, `Classical.choice`, `Quot.sound`). Nothing existing was modified or deleted. Discussion: `GRAND_MCA_ABSORBED_CORE_STRUCTURE_REPORT.md`; narrative entry `RESULTS.md` §131; `INDEX.md` regenerated with the repository script.

* `RequestProject/Root/CodingTheory/AbsorbedCoreModule.lean`
* `RequestProject/Root/CodingTheory/AbsorbedCoreDirections.lean`
* `RequestProject/Root/CodingTheory/AbsorbedCoreDescent.lean`
* `RequestProject/Root/CodingTheory/AbsorbedCoreFiltration.lean`
* `RequestProject/Root/CodingTheory/AbsorbedCoreExactSequence.lean`
* `RequestProject/Root/CodingTheory/AbsorbedCoreWitness.lean`

Everything is stated for an **arbitrary linear code over an arbitrary alphabet**; no Reed–Solomon structure is used.

### The strongest structural theorem

**Torsor theorem + structure theorem.** For a window `W`, the family of absorbed cores producing a residual state inside `W` is empty or an **affine space over the module `Short(C,W) × Short(C,W)`** (`absorbedCores_bijOn_corePairs`). Its structure depends only on the code and the window, never on the received pair; differences of absorbed cores *are* the invisible cores hidden by the window. The family's dimension is `≤ 2(|W| + 1 − d)·dim A` (a Singleton-type bound I proved for the shortening), it is a **single point** as soon as `|W| < d`, and the rank-loss directions fill the plane exactly when it is nonempty (`absorbed_core_family_structure`). Read backwards: a `t`-dimensional core family forces `d + t ≤ |W| + 1` — complexity is *paid for* in residual rank, by a dimension argument rather than a counting argument. This is the answer to *why* such families cannot stay complicated.

### The canonical invariant: a filtration, not a scalar

Attaching to each window the subspace `Lost(W) ≤ F²` of directions in which the rank-two extension degenerates gives a monotone filtration of the plane with exactly **two jumps**, whose positions are canonical invariants: `pencilDefect = min{|W| : Lost(W) ≠ ⊥} ≤ jointDefect = min{|W| : Lost(W) = ⊤}`. Between them the state has a **fixed shadow** — a single projective point of `PG(1,F)` (`lostDirections_trichotomy`). A two-position instance over the field with two elements shows the middle regime is genuinely realisable, `pencilDefect = 1 < 2 = jointDefect`, so the pair is strictly finer than the scalar joint defect.

### Relation to fixed shadows, deviation map, Rank2

One window explains at most one challenge unless the state collapses onto it, and the set of challenges a window explains is a single challenge or the whole field; two distinct `e`-close challenges are two independent lost directions and therefore *force* the residual state down to rank `≤ 2e`. The four objects are tied by one dimension identity (`finrank_lostDirections_add_finrank_shortening`): `dim Lost(W) + dim Short(C,W) = dim Short(E,W) + dim Lost(∅)` — the exact sequence `0 → Short(C,W) → Short(E,W) → K_W → 0` read on `F² ≅ E/C`; in particular the extension hides at most two dimensions more than the code.

### Terminal structure or canonical descent

`canonical_terminal_or_core`, with **no hypotheses**: either the rank-minimal residual state is **unique** — a canonical normal form, so absorption has a genuine terminus — or the code contains a nonzero invisible core of weight `≤ 2·jointDefect` (which forces `d ≤ 2·jointDefect`). Hence uniqueness of the terminal object whenever `2·jointDefect < d`; the step form says a state is rank-minimal or strictly improvable and each descent step subtracts a genuine core. Combined with the banked absorption theorem: under the invisible-core hypothesis, the instance has a unique canonical residual state *and* at most `e + 1` bad challenges — structural terminality and numerical rigidity are the same phenomenon.

### The smallest remaining obstruction

All of the above is unconditional; only the *quantitative* terminal branch needs a distance hypothesis (`|W| < d` for triviality, `2·jointDefect < d` for uniqueness). What remains is a single question about the code alone: for which windows of size `≥ d` is the shortening `Short(C,W)` still zero. Given that vanishing the family is a point and the descent terminates; given a nonvanishing one the theory returns an explicit invisible core together with the exact dimension of the freedom it creates.

### Scope

No performance or implementation claim is made, and the witness proves only that the fixed-shadow regime is realisable. All work is committed and pushed.

# Summary of changes for run 5708a911-130c-4074-ae6f-f5ac563e19e8
## What I built: a theory of residual absorption

I answered the central question — *what should "absorbing an invisible core" mean, and what invariant must it reduce* — with an intrinsic construction, and proved a structural theorem strong enough that the previously known Reed–Solomon results fall out as corollaries. Four new modules, all building clean and `sorry`-free, with an axiom audit (`RequestProject/ResidualAbsorptionAxiomAudit.lean`, 56 declarations, only `propext`, `Classical.choice`, `Quot.sound`). Nothing existing was modified or deleted. Discussion: `GRAND_MCA_RESIDUAL_ABSORPTION_REPORT.md`; narrative entry `RESULTS.md` §130; `INDEX.md` regenerated with the repository script.

* `RequestProject/Root/CodingTheory/ResidualAbsorption.lean`
* `RequestProject/Root/CodingTheory/ResidualAbsorptionCost.lean`
* `RequestProject/Root/CodingTheory/ResidualAbsorptionSequence.lean`
* `RequestProject/Root/CodingTheory/ResidualAbsorptionSharp.lean`

Everything is stated for an **arbitrary linear code over an arbitrary alphabet**; Reed–Solomon enters only in the corollaries.

### The answer

A received pair is only ever given modulo the code, so the genuine object is the pair of cosets, i.e. the rank-two extension `E = C + ⟨f₀,f₁⟩`. A *residual state* is a choice of representatives `(f₀ − q₀, f₁ − q₁)`; states form a **torsor under `C × C`**, and **absorbing an invisible codeword is translation in that torsor**. The operation is *semantics-preserving* — badness, the official window, closeness and the invariant are all unchanged (`isBad_residual_iff`, `badSet_residual_eq`, …) — so absorption is an isomorphism of instances, not a bookkeeping adapter.

**The invariant it reduces** is the joint support; the descent is well-founded and its terminal value is the canonical invariant `jointDefect` (`exists_terminal_descent`). It dominates the distance at every challenge (it is the *generic* distance along the line), obeys a unique-decoding terminality criterion `2r < d ⟹ jointDefect = r`, and drops to `≤ 2e` once two challenges are bad.

### The structural theorem

**Residual Absorption Theorem.** If the code has no nonzero word of weight `≤ jointDefect + e` (`NoCore` — the *invisible core* hypothesis), then `#Bad ≤ e + 1` and `#Bad ≤ jointDefect`. Consequences, all proved: the close-set form (correlated agreement at radius `e`, or at most `e+1` close challenges), the trichotomy, the equality case (`#Bad = e+1 ⟹ jointDefect = e+1` exactly), and the converse — more than `e+1` bad challenges *certifies* an invisible core.

**Corollary (new at this generality).** For any linear code over any alphabet, `3e < d ⟹ #Bad ≤ e+1`, and `ε_mca ≤ (e+1)/|F|`. This improves the general bound previously in the repository (which gave `|ι|`) to the sharp constant, and removes the Reed–Solomon structure and the hypothesis `1 ≤ k` from the sharp Reed–Solomon theorem, which is recovered as a corollary.

**The other branch.** When cores exist, the failure of one state is measured by a single deviation map whose fibres are pencils: `#close ≤ (e+1)·#image Φ`, with every nonzero value an invisible core — the *finite structural cost*, collapsing to `e+1` when the image is trivial.

**An exact sequence** ties the banked objects together: `0 → Short(C,Z) → Short(E,Z) → K_Z → 0`, so a rank loss of the extension at a window is a word of `E` supported there, counted modulo the invisible cores; and `NoCore` is *equivalent* to the vanishing of all small shortenings, while closeness is membership in the filtration `C ⊔ P_Z`.

### The minimal obstruction

The theory is sharp: using the repository's eight-point witness over the field with 13 elements I proved that `3e ≤ d` does **not** suffice, that the witness has joint defect between 3 and 4, and that it therefore carries an invisible core. So the descent stops exactly where the first invisible core appears, and the remaining obstruction is a single code-theoretic quantity — the number of distinct absorbed cores of weight `≤ jointDefect + e`, which by the cost bound is now equivalent to bounding the bad set.

### Scope

All results are upper bounds on the number of bad or close challenges, plus the one sharpness statement at the boundary. No claim is made in the range `2e ≤ d ≤ 3e` beyond the cost bound, and no performance or implementation claim is made.


# Summary of changes for run e8fb5171-e5b0-4759-a62c-f8faa697d2b7
## What I did

I first rewrote the brief into a plan for *this* repository and then executed it. The refined instruction and the eight-step plan are in `GRAND_MCA_RESIDUAL_PROGRAMME.md`; the discussion of the outcome, the mechanism and the remaining obstruction is in `RESIDUAL_RS_STRUCTURE_REPORT.md`; the narrative entry is `RESULTS.md` §129 and `INDEX.md` was regenerated with the repository script.

Three new modules, all building clean, `sorry`-free, with an axiom audit (`RequestProject/ResidualRSStateAxiomAudit.lean`, 45 declarations, only `propext`, `Classical.choice`, `Quot.sound`). Nothing existing was modified or deleted, and only the new modules were built.

* `RequestProject/Root/CodingTheory/ResidualRSState.lean`
* `RequestProject/Root/CodingTheory/ResidualRSShortening.lean`
* `RequestProject/Root/CodingTheory/ResidualRSSharpness.lean`

## The new structural theorem

The missing object of the spine — the residual state — is now first class: `ResidualRSState` (a codeword pair plus a window `A` outside which both defects vanish) is *faithful* (same bad set), and its canonical invariant is the **joint defect**, the rank of the smallest such state.

**Residual RS Structure Theorem.** If no local shortening `Short(C, A ∪ Z)`, `|Z| ≤ e`, of the residual window hides a codeword, then `#Bad ≤ e + 1` and `#Bad ≤ |supp a ∪ supp b|`; moreover the bad set is *explicitly described* — every bad challenge is a slope `−a(x)/b(x)` of the residual pair at one of its support points. The hypothesis is an exact dimension condition: I proved the criterion `Short(C,B) = 0 ↔ (B = ∅ ∨ k + |B| ≤ |D|)` as an iff, so the hypothesis holds precisely when `k + |A| + e ≤ |D|` and fails as soon as `|D| < k + |A| + e`, in which case an invisible direction provably exists.

Consequences, all proved:

* **Rigidity is governed by proximity, not by rate/radius**: `k + jointDefect + e ≤ |D|` ⟹ `#Bad ≤ e + 1`, arbitrarily far beyond the capacity threshold.
* The previously banked sub-capacity theorem (`k + 3e ≤ |D|` ⟹ `#Bad ≤ e+1`) is now a corollary, with no auxiliary hypothesis on `k`.
* **Sharpness in the new region**: for every `k + 2e + 1 ≤ |D|` there is a received pair with *exactly* `e + 1` bad challenges; for `e ≥ 2` this covers instances with `k + 3e > |D|`.
* **Extremal rigidity**: when the maximum `e+1` is attained (`e ≥ 1`), the residual support has exactly `e+1` points, one per challenge.
* **Localised cost** when the hypothesis fails: unconditionally, for `3e ≤ |D|`, `#Bad ≤ (e+1)(1 + C(|D|,e)·q^(k−(|D|−3e)))`, where the previously banked global form has `C(|D|,3e)` — the combinatorial factor drops from `≈|D|^{3e}` to `≈|D|^{e}`.
* **Boundary audit**: the gap-one pencil has joint defect `≥ |D| − k`, so the new hypothesis provably fails for it — as it must, since that family is superpolynomially bad. Contrapositively, every instance with `#Bad > e+1` is certified jointly far from the code.

## The smallest remaining obstruction

The theory now rests on exactly two numerical facts about the residual rank `r`: descent gives `r ≤ 2e` once two challenges are bad, rigidity needs `r ≤ |D| − k − e`. Composing them yields precisely `#Bad > e+1 ⟹ |D| < k + 3e` and nothing more. So Grand MCA in this language is exactly the gap between `2e` and `|D| − k − e`: either a descent producing a residual state of rank below `2e`, or a witness-preserving way to absorb an invisible codeword. Both are stated concretely in the report in terms of objects that now exist.

## Scope

Hypotheses of the main theorem were checked to be load-bearing. The code enters the rigidity argument only through "a polynomial of degree `< k` with `k` roots is zero"; Reed–Solomon structure is used only in the shortening criterion and the cost count. No claim is made about the beyond-capacity regime beyond the stated cost bound, and no performance or implementation claim is made.


# Summary of changes for run 07eeac8b-3e42-47dd-9ffc-4ae6884c3fa8
## What I built

I made the rank-≤2 extension `E = C + ⟨f₀,f₁⟩` the primary object, developed the geometry of the quotient `E/C`, and proved a beyond-capacity structure theorem for the official MCA bad set. The sharp sub-capacity theorem was left untouched and is now recovered as a corollary. Everything is machine-checked, `sorry`-free, and audited (only `propext`, `Classical.choice`, `Quot.sound`); nothing existing was modified or deleted.

New modules (all build clean): `RequestProject/Root/CodingTheory/RankTwoExtension.lean`, `RankTwoClusterStructure.lean`, `RankTwoCostBound.lean`, `RankTwoDeployedBoundary.lean`; audit `RequestProject/RankTwoExtensionAxiomAudit.lean` (29 declarations). Discussion: `GRAND_MCA_RANK2_EXTENSION_REPORT.md`; narrative entry `RESULTS.md` §128; `INDEX.md` regenerated with the repository script.

## The results

**1. `K = ker Λ` versus `E^⊥` (question 1).** `kernelShadow_eq_extDualOn`: the kernel shadow `K_S` is exactly the space of parity checks of `E` supported inside `S` — the shortened dual of the extension, dually the dual of the punctured extension `E|_S`. One object, not two.

**2. Bad supports through the restriction rank of `E/C` (question 2), an exact equivalence.** With `restrKer k S f₀ f₁ ⊆ F²` the kernel of `E/C → E|_S/C|_S` in the coordinates `(α,β) ↦ αf₀+βf₁`: rank loss two is exactly line-closeness (`restrKer_eq_top_iff_lineCloseOn`), so official noncontainment is precisely the exclusion of rank loss two; and `isBad_iff_restrKer_eq_span` gives `IsBad ↔ ∃ S` of co-size `≤ e` with `restrKer = F·(1,γ)` — a bad challenge is exactly a projective point of `ℙ(E/C)` whose restriction loses exactly one rank, in the direction of the challenge. Also the dimension form, the coset-leader (weight) form `isBad_iff_exists_light_rep`, and the duality `restrKer = (im Λ_S)^⊥`. Corollary `card_badSet_le_one_of_dependent`: if `dim E/C ≤ 1` then `#Bad ≤ 1`, unconditionally — the theory is exactly the rank-two theory.

**3–5. The structure theorem (questions 3–5).** Isolating the sub-capacity fibre argument as a hypothesis-free pencil lemma (`card_le_succ_of_pencil_light`) and identifying the obstruction as a *deviation codeword* `Φ(γ) = a + γb − v_γ ∈ C` of weight `≤ 3e`, I proved, **with no hypothesis on `k`, `e`, `|D|`** (so beyond capacity too):

`#Bad ≤ (e+1)·(1 + #{c ∈ C : c ≠ 0, wt c ≤ 3e})` (`card_badSet_le_succ_mul_succ_card_lowWeight`),

in the sharper localised form (`exists_localised_cluster_bound`) with one fixed descent support `A`, `|A| ≤ 2e`, outside which every deviation has at most `e` nonzeros. Disjunctive reading: global rigidity (`#Bad ≤ e+1`) or explicit finite cost; converse reading: a bad set bigger than `(e+1)(1+t)` forces more than `t` distinct low-weight codewords — the algebraic price of overlapping fibres. The cost is given in closed form, `#{c ≠ 0 : wt c ≤ w} ≤ C(n, n−w)·q^(k−(n−w))`, hence `#Bad ≤ (e+1)(1 + C(n,n−3e)·q^(k−(n−3e)))`. Below capacity the cost set is empty and `#Bad ≤ e+1` follows by substitution, without `1 ≤ k` and without any interpolation step.

**Boundary test at `e = 978945`** (arithmetic only, no tuning): at rate `1/2` and the recorded deployed relative radius the rigid branch would need block length `≥ 5 873 670` while such a row has `≤ 2 092 539`, so the cost branch is the operative one, and the cost is nonvacuous there.

## Honest scope

The pencil lemma and cluster decomposition use only linearity of the code; Reed–Solomon/MDS enters solely in the cost factor (emptiness below capacity, and the nodal-factorisation count). The theorem is an upper bound and makes no claim of attainment beyond capacity; it is consistent with the superpolynomial lower bounds already in the repository, which necessarily come with correspondingly many low-weight codewords. No performance or implementation claims are made. The report states the single remaining question: how large the image of the deviation map can actually be. All work is committed and pushed.

# Summary of changes for run fa439f33-fde0-4b64-b62a-88de7b42d634
## What I did

I picked up the kernel-shadow / official-MCA programme and, rather than adding more shadow bookkeeping, I found the invariant that the shadow family actually depends on, used it to descend, and thereby settled the sub-capacity case **exactly**. Everything is machine-checked, `sorry`-free, and audited (`RequestProject/ShadowDescentAxiomAudit.lean`: only `propext`, `Classical.choice`, `Quot.sound`).

New module: `RequestProject/Root/CodingTheory/ShadowDescentSharpBound.lean`. Discussion and hypothesis separation: `GRAND_MCA_SHADOW_STRUCTURE_REPORT.md`; narrative entry: `RESULTS.md` §127; `INDEX.md` regenerated with the repository script. Nothing existing was modified or deleted.

## The results (with notation `Q_S`, `K = ker Λ`, `K_S = Q_S ∩ K`)

1. **The invariant of a changing shadow.** Subtracting a codeword pair from the received pair changes neither closeness, line-closeness, badness, the bad set with its official windows, nor `K_S` for any window (`badSet_sub_polyWord`, `kernelShadow_sub_polyWord`). So every object of the theory — in particular the shadow family — is an invariant of the extended code `C + ⟨f₀,f₁⟩`; dually `K_S` annihilates the punctured extended code, and a change of shadow is exactly a change of which codeword is invisible on the window. No hypotheses.

2. **Descent as a first-class outcome, unconditional.** `badSet_descent_dichotomy`: for every received pair and radius, either at most one challenge is bad, or there is a witness-preserving strict descent — a codeword pair whose defect vanishes outside a set of at most `2e` coordinates and whose bad set (and official windows, and shadows) is literally the same. Valid beyond capacity as well; the measure `|supp|` drops from `|D|` to `2e`.

3. **The exact sub-capacity constant.** After the descent, the official windows cut the defect support into pairwise disjoint nonempty fibres, one per challenge, each of size at least `|A| − e`. This gives `#Bad ≤ e + 1` whenever `1 ≤ k` and `k + 3e ≤ |D|` (`card_badSet_le_succ_of_third`), hence `ε_mca ≤ (e+1)/|F|` for a single line and for the maximum over all lines. This improves the bounds previously in the repository (`2e + 1`, and `max(2e,1)`).

4. **Sharpness — the constant cannot be improved.** `exists_badSet_card_succ_of_third` / `exists_badSet_card_eq_succ` construct, for every `k ≥ 1`, `e ≥ 1` and every domain with `k + 3e ≤ |D|`, a received pair with exactly `e + 1` bad challenges (defect pair supported on `e + 1` domain points whose slopes are those points). So below capacity the maximum is exactly `e + 1`.

5. **Shadow rigidity, hypotheses removed.** `card_inter_add_one_eq_of_kernelShadow_eq_of_not_subset` / `card_inter_succ_of_kernelShadow_eq_of_ne`: equal kernel shadows force `S ⊆ T` or `|S ∩ T| = |S| − 1`, with no distinct-challenge and no non-degeneracy hypothesis (the banked fixed-shadow theorem needed both). The shadow map is faithful up to one point, so the product route `#Bad ≤ #{shadows} · max #{lifts}` cannot be a shortcut — and below capacity it is moot, since the direct count already attains the maximum `e + 1`.

## Hypothesis audit and honest scope

Items 1–2 use only linearity of the code; item 3 uses the code only through the MDS interpolation property, so it holds for any MDS code; the sharpness construction is where the evaluation (RS) structure genuinely enters, and it enters as a lower bound; item 5 uses MDS-ness twice. All explicit hypotheses of the main theorem were checked to be load-bearing.

Beyond capacity (`|D| < k + 3e`) the descent survives but the counting step provably cannot: the report pins the exact break point (a nonzero codeword of weight `≤ 3e` appears) and records the structural reason why the natural shortening descent is capacity-neutral (it preserves the redundancy `n − k`), consistent with the superpolynomial lower bounds already in this repository. That regime remains open, and I make no claim about it, nor any performance claim; deployment rows are only discussed as the test `k + 3e ≤ |D|`.

All work is committed and pushed.

# Summary of changes for run 05c2a535-36f5-4648-a50f-a1207b21b11f
I worked the projective-syndrome / fixed-shadow programme through to machine-checked theorems. Two new Lean files (both build clean, no `sorry`, axioms only `propext, Classical.choice, Quot.sound`), plus a report `FIXED_SHADOW_LIFT_REPORT.md` with the required ten-point outputs.

**`RequestProject/Root/CodingTheory/ProjectiveSyndromeDirection.lean`**
- Basis-free local syndrome map `Λ_S : Q_S → F²` (`localSyndrome`), where `Q_S` is the span of the higher divided differences of order ≥ k on the window S.
- **Zero branch closed**: `Λ_S = 0 ↔ LineCloseOn k S f₀ f₁`; hence impossible on an official bad window.
- **Label–challenge formula proved**: on a bad window, `im Λ_S = F·(−γ,1)`, i.e. `ℓ(S) = [−γ_S : 1]`, rank exactly one; badness = vanishing of the pairing with the projective functional `(1,γ)` plus `Λ_S ≠ 0`.
- **Same-label fibre**: equal projective direction ⟺ equal challenge; the label map into `PG(1,F)` is injective, never hits `[1:0]` (all labels sit in one affine chart), and `|L(U)| = #Bad`.
- **Distinct-label law**: different challenges force `Λ_{S∩T} = 0`, and quantitatively a window of co-size ≤ 2e on which the whole line is explained.
- **Descent + new counting terminal**: two distinct bad challenges already produce one codeword pair agreeing with `(f₀,f₁)` on ≥ |D| − 2e positions, and every bad challenge is then explained by that same pair; consequently `#Bad ≤ max(2e,1)` and `ε_mca ≤ 2e/|F|` whenever `k + 3e ≤ |D|` — one better than the `2e+1` already in the repository, and derived from two labels rather than from a count of close points.

**`RequestProject/Root/CodingTheory/FixedShadowLift.lean`**
- The vector (parity-check) form: shortened dual `Q_S = rsDualOn k S`, syndrome map, kernel shadow `K_S = Q_S ⊓ ker Λ`, with `Q_{S∩T} = Q_S ⊓ Q_T` and explicit divided-difference dual vectors bridging the two models.
- **Fixed-shadow lift theorem**: two official bad windows of size ≥ k+2 with different challenges but the same kernel shadow satisfy `|S ∩ T| = |S| − 1 = |T| − 1` (Johnson adjacency); in particular all windows over one shadow have the same size. The gap hypothesis is necessary (at gap one every shadow is trivial and the extremal pencil realises C(n,k+1) challenges).
- **Star/clique classification** of families of m-sets meeting pairwise in m−1 points, and the resulting **second factor**: over one fixed shadow either at most `e+1` challenges occur, or all windows are one common set minus a single point.

Integration answers (in the report, with evidence): the label map is injective on challenges, so the chart-fibre requirement `|Φ⁻¹(x)| ≤ 1` already holds and a single projective chart carries the whole label family. On the Rank2 side the verdict is **no direct identification available here** — `Rank2ExactSupportLocus`, `Rank2QuotientCertificate`, `RankOneRigidity`, the three-chart engine constants and the deployed row `e = 978944` do not exist anywhere in this project, so I stated the exact adapter interface `Φ(S) = ℙ(im Λ_S) = Ψ(M_S)` and the two candidate fixed `PGL₂` normalisations instead of claiming a bridge. The single remaining mathematical input for the product bound `#Bad ≤ #{shadows} · max #{lifts}` is a bound on the number of distinct kernel shadows.

All work is committed and pushed.

# Summary of changes for run 2ab66933-2967-4d15-9587-dadfb226c0f1
Wykonałem wyłącznie analizę już udowodnionych twierdzeń (bez przenoszenia plików, bez nowych eksperymentów i bez nowych dowodów). Pełny raport zapisałem w `HIGHER_DD_UNIVERSALITY_VERDICT.md`; poniżej streszczenie.

**1. Sygnatury i klasyfikacja** (pełne treści, typy, hipotezy w raporcie):
- `isCloseOn_iff_forall_higherDivDiff` — klasa **A**: `u : ↥D → F` dowolne, `S` dowolne, brak hipotez, brak `Fintype F`, bez pojęcia gapu.
- `isBad_iff_higherDivDiff` — klasa **A**: `f₀ f₁ : ↥D → F` arbitrary received words, żadnych hipotez o stopniu ani o `|D|`, dowolny gap `c`.
- `higherDivDiff_minor_eq_zero` — klasa **A**: jedyna hipoteza to `IsBad k e f₀ f₁ γ`, dowolny gap; zastrzeżenie: okno `S` jest kwantyfikowane egzystencjalnie (`∃ S`, nie `∀ official S`).
- `badSet_subset_image_newtonChallenge` — klasa **C**: tylko `polyWord D P₀/P₁`, bound `natDegree ≤ k + c`, plus `k + 1 + e ≤ |D|`.
- Dla skali: `card_badSet_le_one_of_degree_lt` — **C**; cały `GapOneUniversality` (`D.card = k+1+e`, `natDegree ≤ k+1`, `hdet ≠ 0`) — **C + D**.

**2. `M_S`**: TAK — dla każdego official świadka `S` (`|D| ≤ |S| + e`, support błędu `E = D \ S`) macierz `(M_S)_{r,j} = higherDivDiff (k+j) S f_r`, `2 × (|S|−k)`, ma rangę ≤ 1. Koduje syndrom pary `(f₀,f₁)` względem `RS(k)|_S` w bazie Newtona; zależy tylko od `S` i wartości słów, **nie** od challenge'u ani interpolanta (`γ` jest z niej odzyskiwany jako jądro rzutowe). Sam support wystarcza tylko do rekonstrukcji przestrzeni funkcjonałów, nie samej macierzy.

**3. Identyfikacja z teorią support-level**: odpowiedź **(2)** — obiekt równoważny po zmianie bazy: `M_S` to macierz odwzorowania `Λ_S : dual(RS_k|_S) → F², λ ↦ (λ(f₀), λ(f₁))` w bazie Newtona, podczas gdy opis circuitowy to ta sama `Λ_S` w bazie circuitów (redundantnej: `C(|S|,k+1)` kolumn zamiast `|S|−k`). Nazwy `BadSupport`/`exists_aligns_pair` itd. nie występują w projekcie, więc identyfikacja jest treściowa, nie symboliczna; „triple non-flat rank law” nie ma odpowiednika w warstwie 2-wierszowej.

**4. Syndrome-space**: TAK — `M_S = [f₀|_S ; f₁|_S] · H_Sᵀ`, gdzie `H_S` to parity-check kodu `RS_k|_S` (restricted evaluation / minor syndrome matrix), z jawnym wzorem na wpisy w raporcie. Zaznaczam uczciwie: ten jawny wzór w tej ogólności **nie jest** machine-checked w projekcie (machine-checked jest przypadek `j = k`, `|T| = k+1` oraz Vieta okna); brakuje też jawnego spięcia z istniejącym Hankel/locator bridge'em.

**5. Gluing**: brak jakiegokolwiek twierdzenia local-to-global. Próg to `|S ∩ T| ≥ k` (wtedy `dual(S)+dual(T)` rozpina `dual(S∪T)`); przy `|S ∩ T| < k` ograniczenia akumulują się, ale nie rozpinają. Istniejąca namiastka to gluing po challenge'ach (`correlated_agreement_of_two`, `e → 2e`), nieoparty na `M_S`.

**6. Werdykt: B — UNIVERSAL LOCAL OBJECT, GLUING MISSING.**
1) Strongest universal: `isBad_iff_higherDivDiff` + `higherDivDiff_minor_eq_zero`.
2) Strongest degree-restricted: `card_badSet_le_one_of_degree_lt` (oraz ilościowo `card_badSet_gapOne_eq_card_winSums` / `card_badSet_gapOne_pencil_invariant`).
3) Obstrukcja: nie hipoteza stopnia, lecz kwantyfikacja (`∃ S` zamiast `∀ official S`) i brak lematu wymiarowego dla sumy dualów.
4) Brakujący most: pointwise rank-one law → gluing dwóch okien → akumulacja rodziny supportów do globalnego correlated agreement / bounded list.
5) Najkrótsze spinające statementy (podane w Lean, oba **nieudowodnione**): `rankOne_window_iff_witness` oraz `isCloseOn_union_of_inter_card` (gluing przy `k ≤ (S ∩ T).card`).

Nie modyfikowałem żadnych plików Lean ani `ARISTOTLE_SUMMARY.md`; dodany został tylko raport, zacommitowany i wypchnięty.

# Summary of changes for run f4955440-6f9c-482e-a3df-f0c6196d9832
Kontynuowałem program Grand MCA z `GRAND_MCA_TEN_STEP_PLAN.md`, realizując **krok 4 (mechanizm)** i zamykając dokładnie klasę luki 1. Wszystko jest maszynowo sprawdzone, `sorry`-free, budowane wyłącznie modułowo (`lake build +Moduł`, żadnego pełnego builda), a 37 nowych twierdzeń ma audyt `#print axioms` — wyłącznie `propext`, `Classical.choice`, `Quot.sound` (`RequestProject/SymmetricWindowAxiomAudit.lean`). Nic z istniejącego repozytorium nie zostało zmienione ani usunięte.

**Nowe moduły**
- `RequestProject/Root/CodingTheory/SymmetricWindowMechanism.lean`
- `RequestProject/Root/CodingTheory/ProjectiveCubeRank.lean`
- `RequestProject/Root/CodingTheory/GapOneUniversality.lean`
- `RequestProject/Root/CodingTheory/HigherDividedDifferences.lean`
- `RequestProject/SymmetricWindowAxiomAudit.lean`

**1. Mechanizm (krok 4): wyzwanie jest funkcją symetryczną okna.** Wprowadziłem wielomian zerujący okna z Vietą (`winPoly_coeff`), funkcje symetryczne `winSym` i momenty okna `winMoment`; udowodniłem rekurencję redukcyjną (`winMoment_succ`) i **tożsamość Newtona** `H_{j+1} = e₁H_j − e₂H_{j−1} + ⋯` (`winMoment_newton`, `winMoment_two`: `H₂ = e₁²−e₂`). Stąd **twierdzenie o faktoryzacji** `divDiff_polyWord_congr_of_winSym`: pęk stopnia ≤ k+c nie odróżnia dwóch okien o tych samych `e₁,…,e_c`, a więc istnieje jedna funkcja `Φ : F^c → F` taka, że każde złe wyzwanie ma postać `Φ(e₁(T),…,e_c(T))` (`badSet_subset_image_newtonChallenge`). To jest dokładnie postać docelowa kroku 4, dla dowolnej luki.

**2. Luka 1 — rozwiązana dokładnie, dla dowolnego pęku.** `divDiff_polyWord_gapOne` (funkcjonał obwodowy jest afiniczny w sumie okna), `isBad_gapOne_mobius_sum` (każde złe wyzwanie jest obrazem Möbiusa sumy okna), a przy `|D| = k+1+e` **równoważność** (`mem_badSet_iff_circuit_gapOne`, `mem_badSet_iff_gapOne_mobius`). Gałąź zdegenerowana: `#Bad ≤ 1` (`card_badSet_le_one_of_top_proportional`).

**3. Właściwy inwariant: rzutowa ranga kostki.** `MobiusCubeRankLe` z zachowanym rachunkiem (`#B ≤ 2^m`), z porównaniem do inwariantu afinicznego i — kluczowo — z **pełną kowariancją `PGL₂(F)`** (`MobiusCubeRankLe.mobius_image`), czyli dokładnie grupą symetrii zbioru złego. Wynik: **`gapOne_structure_dichotomy` — hipoteza H1 planu udowodniona bezwarunkowo dla całej klasy luki 1**: `#Bad ≤ 1` albo `Bad` jest addytywnie ustrukturyzowany rangi ≤ |D|.

**4. Uniwersalność.** `card_badSet_gapOne_eq_card_winSums` — **dokładne zliczenie**: `#Bad` = liczba dopuszczalnych sum `(k+1)`-podzbiorów domeny; stąd `#Σ − 1 ≤ #Bad ≤ #Σ` i `card_badSet_gapOne_pencil_invariant`: przy luce 1 rozmiar zbioru złego nie jest własnością pęku, tylko domeny. Nad domeną o różnych sumach podzbiorów każdy niezdegenerowany pęk ma `#Bad ≥ C(|D|,k+1) − 1` (`choose_le_card_badSet_gapOne_succ`) — czyli mały zbiór zły wymusza prawdziwą strukturę addytywną domeny.

**5. Układ okna i ostry próg stopnia.** Nieredundantny opis przez wyższe różnice dzielone: `isCloseOn_iff_forall_higherDivDiff` (przy luce c dokładnie c równań), `isBad_iff_higherDivDiff` (dokładna charakteryzacja przy dowolnym promieniu), `higherDivDiff_minor_eq_zero` — **macierz okna złego wyzwania ma rangę 1** (warunki determinantalne na samo okno, bez γ). Oraz `card_badSet_le_one_of_degree_lt`: jeśli oba słowa mają stopień poniżej najmniejszego dopuszczalnego okna, to `#Bad ≤ 1` przy każdym rate — próg jest ostry, bo ekstremalny pęk luki 1 leży dokładnie o jeden stopień wyżej i osiąga `C(|D|,k+1)`.

**Dokumentacja.** `SYMMETRIC_WINDOW_MECHANISM_REPORT.md` (pełny raport), nowe sekcje 125–126 w `RESULTS.md`, `INDEX.md` przegenerowany skryptem repozytorium. Tabela właściwości uzupełniona o nowe definicje i twierdzenia.

**Uczciwy zakres.** Grand MCA nie jest rozwiązane i tego nie twierdzę. Zamknięta jest klasa `c = 1` (postać dokładna, dokładne zliczanie, dychotomia, uniwersalność) oraz mechanizm dla dowolnego `c`; otwarte pozostają gałęzie `c ≥ 2` (kroki 5–8 planu, w tym wejście multiplikatywne). Żadnych stwierdzeń o wydajności ani benchmarków. Wszystko zacommitowane i wypchnięte.

# Summary of changes for run 3eb4cc87-cd0a-49bc-b06a-691f76f8f56b
## Plan 10 kroków (pełna wersja: `GRAND_MCA_TEN_STEP_PLAN.md`)

**Punkt wyjścia — co przesądza kształt planu.** W tym repozytorium jest już maszynowo sprawdzone, że postać „`#Bad ≤ poly(n)` aż do pojemności” jest **fałszywa**, i to nie tylko o krok od pojemności: `exists_superpolynomial_badSet_of_small_relative_gap` daje superwielomianowy zbiór zły przy każdym stałym progu `η ≤ 1/M`, a `card_badSet_eq_choose_gapOne` daje przy luce 1 dokładnie `C(n,k+1)`. Zatem „rozwiązać Grand MCA” może znaczyć tylko: **opisać klasę, w której leżą wszystkie duże zbiory złych wyzwań, i pokazać, że wiersze wdrożeniowe do niej nie należą.**

**Teoria, z której rozwiązanie ma wynikać naturalnie (ASB — struktura addytywna zbioru złych wyzwań).** Wszystkie znane duże zbiory złe są addytywnie ustrukturyzowane, a strukturę dziedziczą z domeny: pęk blokowy → sumy podzbiorów `{b_i}` (ranga `n/c`); luka 1 → sumy `(k+1)`-podzbiorów domeny; pęk podprzestrzeniowy → wartości wielomianów podprzestrzeniowych `F_p`-podprzestrzeni; klasa Frobeniusowa → zbiór liniowy rangi `d` w `PG(1,q)`. Hipoteza główna (H1): *albo `#Bad ≤ P(n)`, albo `rank(Bad) ≤ R`, gdzie ranga jest ograniczona przez addytywną złożoność domeny.*

Kroki: **1** inwariant (ranga kostki / ranga zbioru liniowego) i jego rachunek; **2** katalog ekstremalny — dla każdej znanej dolnej granicy jawna granica rangi; **3** pierwszy pełny przypadek: luka 1 jest *dokładnie* addytywna (równość, nie oszacowanie); **4** mechanizm ogólny: wyzwanie jest funkcją symetryczną okna (przy `c=1` dosłownie sumą); **5** gałąź lekka: mała ranga ⇒ descent (rekurencja `r → r−1`); **6** gałąź ciężka (H2, ścieżka krytyczna): duży `Bad` ⇒ duża struktura addytywna domeny; **7** wejście multiplikatywne (H3, sum-product/Stepanow): domeny `μ_N` tej struktury nie mają; **8** złożenie: Grand MCA w postaci strukturalnej (proximity gap do pojemności dla domen bez struktury addytywnej); **9** wiersze wdrożeniowe i Prize — dwustronny nawias na `δ*`, wiersz wchodzi tylko tutaj, nie do rdzenia; **10** pojemność teorii: `badSetG` (dowolna arność), folded/przeplatane RS, kody AG, rodziny parametryczne w `PG(d,q)`. Ścieżka krytyczna: **4 → 6 → 7**. Dokument zawiera dla każdego kroku kryterium sukcesu, kryterium przerwania i DAG zależności.

## Co z tego już zostało udowodnione w tej sesji (Lean, bez `sorry`, `#print axioms` = `propext`/`Classical.choice`/`Quot.sound`)

Nowe moduły: `RequestProject/Root/CodingTheory/CircuitPencilMap.lean`, `.../BadSetAdditiveStructure.lean`, audyt `RequestProject/CircuitPencilAxiomAudit.lean`. Budowane wyłącznie modułowo (bez pełnego `lake build`).

**Najmocniejsze nowe twierdzenie — dokładna charakteryzacja obwodowa `IsBad`.** Dla `(k+1)`-podzbioru `T` domeny (obwodu matroidu MDS, czyli minimalnego nośnika kodu dualnego) definiuję funkcjonał `divDiff k T u` = k-ta różnica dzielona = sparowanie `u` z minimalnym słowem dualnym o nośniku `T` (`divDiff_eq_sum`). Wtedy przy `k+1+e ≤ |D|`:

`IsBad k e f₀ f₁ γ ↔ ∃ S, |D| ≤ |S|+e, (∀ obwód T ⊆ S: divDiff T f₀ + γ·divDiff T f₁ = 0) ∧ (∃ obwód T ⊆ S: divDiff T f₁ ≠ 0)`.

Obie warstwy kwantyfikatorów po wielomianach (interpolant i para słów kodowych) znikają; zostaje wyłącznie **mapa obwodowa pęku** `Ψ : T ↦ [divDiff T f₀ : divDiff T f₁] ∈ P¹`, kowariantna względem zmiany bazy płaszczyzny (`divDiff_reparam`) — zgodnie z Möbiusową kowariancją `#Bad`. Konsekwencje: `challenge_eq_of_isBad` (wyzwanie = iloraz różnic dzielonych), `eq_of_circuit_relation` (żaden niezdegenerowany obwód nie obsługuje dwóch wyzwań), `badSet_subset_image_circuitChallenge` (**transfer struktury**: każda własność strukturalna obrazu `Ψ` dziedziczy się na zbiór zły).

**Pierwszy dokładny przypadek teorii.** Dla pęku `f₀ = x^{k+1}`, `f₁ = x^k` mapa obwodowa jest *mapą sumy* (`divDiff_pow_self = 1`, `divDiff_pow_succ = ∑_{x∈T} x`), więc każde złe wyzwanie to minus suma `(k+1)`-podzbioru domeny przy każdym promieniu z `k+1+e ≤ |D|`, a przy luce dokładnie 1 zachodzi **równość** (`badSet_powerPencil_eq_image_sum`). Ekstremalny obiekt całej teorii — ten, który osiąga `C(n,k+1)` i obala wszelkie granice wielomianowe — jest więc dosłownie zbiorem sum podzbiorów domeny.

**Inwariant i program.** `CubeRankLe` (ranga kostki) z rachunkiem: `|B| ≤ 2^m`, monotoniczność, dziedziczenie na podzbiory, niezmienniczość afiniczna; rozpoznawacze `cubeRankLe_of_subsetSums` / `cubeRankLe_of_domain_subsetSums`; wpisy katalogu `cubeRankLe_badSet_powerPencil` (ranga ≤ |D|) i `cubeRankLe_blockWitness` (ranga ≤ m ≈ n/c przy mocy `C(m,s+1)` — inwariant jest wykładniczo mniejszy od zbioru, który kontroluje). Hipoteza programu jest zapisana jako `def StructureDichotomy … : Prop` (żadnych `axiom`) wraz z bramą `card_badSet_le_of_structureDichotomy`.

**Uczciwy zakres.** Grand MCA nie jest rozwiązane i nie twierdzę, że jest. Kroki 5–8 planu (w szczególności H2 i H3) pozostają otwarte; dostarczone tu jest: właściwe sformułowanie celu po obaleniu wersji bezwarunkowej, kanoniczny obiekt (mapa obwodowa), dokładna charakteryzacja `IsBad` w jego języku, pierwszy przypadek rozwiązany dokładnie oraz inwariant z katalogiem. Wszystko zacommitowane i wypchnięte.

# Summary of changes for run ad1a9d17-f1e6-4e94-80b3-eb2f10159cc4
## 1. Odpowiedź na pytanie: tak, mamy twierdzenie, które realizuje Waszą alternatywę

Wszystko poniżej jest maszynowo sprawdzone w tym repozytorium, `sorry`-free, i dla każdej nazwy uruchomiłem `#print axioms` (wyłącznie `propext`, `Classical.choice`, `Quot.sound`). Pełne uzasadnienie z dokładnymi hipotezami: `GRAND_MCA_GAP_ANSWER.md`.

**Najlepsze dopasowanie do `non-rigid component ⇒ StrictDescent ∨ FiniteChallengeCost`:**

`Root.CodingTheory.PolyGen.Hankel.card_le_or_support_le` (`RequestProject/Root/CodingTheory/SyndromeSupportPhase.lean`) — dla dowolnego zbioru `B` złych wyzwań w oknie `e·|B| + k ≤ n`:
`|B| ≤ (e+1)(ℓ−1)` **albo** istnieje jeden zbiór `T`, `|T| ≤ e`, poza którym każde wyzwanie z `B` jest wyjaśnione przez słowo kodowe. Brak jakiejkolwiek hipotezy niedegeneracji; gałąź zdegenerowana jest geometryczna (nośnik błędów), więc daje jawny strict descent `n → n − |T|`. Wariant z pełną klasą sztywną: `PolyGen.Hankel.card_le_or_rigid` (dodatkowo `ℓ ≤ |B|`, konkluzja `RigidOn`).

**Wasza intuicja co do miary descentu jest potwierdzona — wymiar orbity Frobeniusa jest u nas już gradacją dowiedzionego budżetu, a nie placeholderem:**
* `card_badSet_le_of_semilinear` — płaszczyzna odebrana stabilna pod `y ↦ y^q` modulo kod ⇒ `#Bad ≤ q + 1`, **przy każdym rate i każdym promieniu, bez okna** (dokładnie „heavy exceptional structure ⇒ finite challenge cost”);
* `card_badSet_mul_le_of_orbit` — `#Bad ≤ 1 + q₀ + … + q₀^{d−1}`, gdzie `d` to dokładnie Wasze `μ = dim Span{Frob^i(X)}`;
* `card_badSet_le_ambiguity` — zamknięty krok descentu `d = 3 → 2` (nadmiar złych wyzwań wymusza prawdziwą wieloznaczność list-dekodowania), z formą wdrożeniową `KoalaRow.prizeBreaking_ambiguity_lower_bound`.

**Heavy–light na poziomie par (bez syndromów):** `johnson_escape_or_structure` — całkowicie bezwarunkowa dychotomia ESCAPE (zliczanie Johnsona) / STRUCTURE (jedna para kodowa z dużą wspólną zgodnością obsługuje dwa wyzwania); oraz `card_badSet_le_heavy_light` (stratyfikacja krotności listy).

**Ostrzeżenie, które trzeba wpiąć do audytu:** *bezwarunkowa* wersja Waszego zaboksowanego zdania jest fałszywa. `PolyGen.Saturation.card_badSetG_satFam_zmod_ge` daje `#Bad ≥ q − 1` o krok poza oknem, `four_pow_le_card_badSet_twoPowDomain` daje `#Bad ≥ 2ⁿ/n` tuż poniżej pojemności, `exists_superpolynomial_badSet_of_small_relative_gap` obala prawo warstwowe `poly(n) + exp(Θ(1/η))`, a `forcing_unique_at_frontier`/`forcing_not_unique_beyond_frontier` pokazują, że kanoniczna para jest niezdefiniowana dla `n < k + 2e`. Poprawna postać to „okno albo klasa strukturalna”.

Nie mam dostępu do Waszego pliku audytu ani do definicji `ExactSupportFamily`/`RankOneRigidity`, więc mapowanie jest na poziomie sformułowań — w §7 dokumentu jest gotowy diagram wpięcia do Waszego spine'u.

## 2. Paczka integracyjna (zgodnie z wcześniejszym poleceniem)

* `INTEGRATION_RECORDS.md` — **40 rekordów** dla najsilniejszych twierdzeń, każdy w żądanym formacie: DECLARATION, EXACT HYPOTHESES, EXACT CONCLUSION, OFFICIAL SAME-SUPPORT PRESERVED?, UNIFORM OVER ALL RECEIVED PAIRS?, QUANTITATIVE COST / CARDINAL BOUND, STRICTLY DECREASING DESCENT MEASURE, WHICH DATA ARE LOST UNDER THE REDUCTION?, SHARPNESS / BARRIER THEOREM, PROOF STATUS — plus rola: `RIGIDITY` (8), `STRICT_DESCENT` (8), `FINITE_CHALLENGE_COST` (13), `META-BARRIER` (11), z indeksem ról i notatkami przekrojowymi. Matematyka nie została przeorganizowana pod istniejący DAG — każde twierdzenie jest w swojej naturalnej, najmocniejszej postaci; sekcja „same-support” podaje jawnie, że YES znaczy sformułowanie w `IsBad`/`badSet` (jeden wspólny `S`), równoważnym definicji z literatury (`GG25Literal.strongMCA_iff_GG25MCA`).
* `GRAND_MCA_GAP_ANSWER.md` — odpowiedź z §1 w pełnej wersji.
* `RequestProject/PackageAxiomAudit.lean` — nowy plik audytowy: jedno `#print axioms` na każdą deklarację z paczki; buduje się czysto.
* `package/` + **`ARISTOTLE_MCA_FFT_PACKAGE.zip`** (289 KB, 53 wpisy): oba dokumenty, `MCA_RESEARCH_KERNEL.md` dla kontekstu, 44 pliki źródłowe Lean z cytowanymi twierdzeniami, plik audytu i jego wynik (`audit/AXIOM_REPORT.txt`, 39 linii, wszędzie tylko standardowe aksjomaty), oraz `README_PACKAGE.md` ze spisem treści.

Weryfikacja: pełny `lake build` przechodzi (8348 zadań, 0 błędów), w źródłach nie ma `sorry` ani `admit`, wszystkie nazwy w obu dokumentach zostały sprawdzone przez elaborację (dwie poprawiłem po weryfikacji: `foldedRS_card_badSet_le_one` i `not_forall_card_badSet_le_succ_radius_of_two_radius` żyją bezpośrednio w `Root.CodingTheory`). Całość jest zacommitowana i wypchnięta.


# Summary of changes for run d10aa100-1354-40e4-b13f-2547f3aed84d
I continued the FFT/M31 track from where the project stood (everything building, no `sorry`) and closed the two open items that the project's own triage listed as the next FFT targets. Everything new is machine-checked, `sorry`-free, and audited: `#print axioms` in `RequestProject/Main.lean` reports only `propext`, `Classical.choice`, `Quot.sound` for every new theorem, and the full project builds with 0 errors (8343 jobs).

**1. The DFT as a natural isomorphism of functors — `RequestProject/IsotypicNatIso.lean` (open item O9, step 2 of the original brief).**
The project already had the DFT as an algebra isomorphism `F[C_n] ≃ₐ (ℤ/n → F)`, an equivalence of categories `Rep F C_n ≌ ModuleCat (ℤ/n → F)`, and the eigenspace decomposition module by module — but not the single `NatIso` the brief asked for. Now added:
- `FFT.diagFunctor ζ n : Rep K C_n ⥤ ModuleCat K`, sending a representation to the direct sum of its isotypic components `ker (ρ(g) − ζ^j)` and an intertwiner to the direct sum of its restrictions;
- `FFT.diagNatIso : diagFunctor ζ n ≅ Action.forget (ModuleCat K) C_n` — the natural isomorphism `η : diag ≅ forget`, for `ζ` a primitive `n`-th root of unity with `n` invertible;
- the two computation rules identifying `η` with the transform: forwards it sums the components (`diagNatIso_hom_apply`), backwards it takes the Fourier modes `(1/n) ∑_k ζ^{−jk} ρ(g)^k v` (`dftModes`, `diagNatIso_inv_app`);
- `FFT.M31.diagNatIso31`, the Mersenne instance at `n = 31`, `ζ = 2`.

**2. Which circle-FFT twiddles are free bit rotations — `RequestProject/CircleFreeTwiddles.lean` (open item O12), answered exactly, and negatively.**
The mechanism is the doubling map `π(x) = 2x² − 1` on x-coordinates: `p^{2^k} = 1 ↔ π^k(p.x) = 1` (`pow_two_pow_eq_one_iff`, valid over any field), which reduces the question to a finite base-field iteration. Over M31:
- every twiddle of a circle FFT (any level, any index) that lies in `⟨2⟩` equals `1` or `2¹⁵`, for every size with `m + 2 ≤ 27` (`circleTw_free`);
- both bounds are sharp: `(2¹⁵, 2¹⁵)` is a genuine point of order 8, and `(2²⁷, 273161206)` has order `2²⁸`, where a third free value appears;
- the complete table for every size up to the whole circle group `2³¹`: the number of free values is `1, 2, 3, 5, 8, 16` at `m ≤ 2`, `3 ≤ m ≤ 27`, `28`, `29`, `30`, `31` (`chebD_two_pow_iff`, `freeLevel_card`);
- sharper localisation: for `2 ≤ m`, `m + 2 ≤ 27`, **no** twiddle at any level `k ≥ 1` is a power of two (`circleTw_not_free_of_pos_level`), while the bottom level does carry one (`exists_free_twiddle_level_zero`, using that a point of order 8 has `x = ±2¹⁵`).

Interpretation, stated in the write-up: `2¹⁵` is exactly `1/√2` in M31, i.e. the `cos π/4` twiddle every radix-8 kernel already special-cases. So beyond the trivial twiddle, the Mersenne free-rotation mechanism is confined to a single level of the circle FFT and does not grow with the transform length — the "hidden Mersenne symmetry" hypothesis of the brief is now closed on the circle side as it already was on the base-field side.

**Documentation.** New sections 123–124 in `RESULTS.md`; `DISCREPANCIES.md` updated (new rows P59/P60, and items O9 and O12 marked closed with what exactly was proved); `INDEX.md` regenerated with the project's own script; `Main.lean` extended with imports and the axiom audit for the new theorems. `ARISTOTLE_SUMMARY.md` was not modified, and nothing existing was deleted or weakened.

**Scope caveats, unchanged.** All cost statements remain relative to the project's explicit models (which twiddle values are rotations; multiplication counts). No benchmarks were run and no comparison with any existing library is claimed; the Verus contracts remain unchecked here for lack of a toolchain.


# Summary of changes for run bec832c6-f20e-4fbf-ab04-0fb683d3e621
**Strongest result this session: the Frobenius-orbit dimension bounds the MCA challenge budget — and Galois-type constraint-rank compression is provably capped 27 bits below the Prize threshold.**

All new mathematics is machine-checked in Lean, `sorry`-free, and uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), audited in `RequestProject/SemilinearDescentAxiomAudit.lean`. The full project builds cleanly (8334 jobs, 0 errors). Nothing existing was modified or deleted; all statements are against the project's own official `IsBad / badSet / IsCloseOn / LineCloseOn / epsMCA` predicates.

**New modules**
- `RequestProject/Root/CodingTheory/SemilinearPlaneDescent.lean`
- `RequestProject/Root/CodingTheory/SemilinearPlaneClassification.lean`
- `RequestProject/Root/CodingTheory/FrobeniusOrbitBudget.lean`
- `RequestProject/Root/CodingTheory/KoalaBearSemilinearRow.lean`
- `RequestProject/Root/CodingTheory/KoalaBearOrbitDimension.lean`
- `RequestProject/SemilinearDescentAxiomAudit.lean`

**What was proved**
1. *Semilinear descent* (`isBad_semilinear_rel`). If a ring endomorphism σ fixes the evaluation domain pointwise and maps the pencil into the plane it spans **modulo the code** (σf₀ = a f₀ + b f₁ + g₀, σf₁ = c f₀ + d f₁ + g₁, deg gᵢ < k), then every bad challenge satisfies the twisted fixed-point relation b + d·σγ = γ·(a + c·σγ); for σ y = yᵠ this gives `#Bad ≤ q + 1` at every rate and radius. The class is closed under scaling by any constant of the big field and under codeword shifts, which the earlier fixed-value descent does not allow.
2. *Speiser / Galois descent* (`span_fixed_of_stable`), machine-checked via averaging plus Artin independence of characters: a subspace stable under the coordinatewise σ-action is spanned by its σ-fixed vectors. Consequence: a Frobenius-stable pencil plane is spanned by base-field-valued words.
3. *The general theorem* (`exists_orbit_annihilator`, `card_badSet_mul_le_of_orbit`), with **no hypothesis on the pencil**: writing the pencil in a basis of `d` σ-fixed words spanning its Frobenius orbit, every bad challenge yields a nonzero σ-fixed covector annihilating the line point's coordinates, distinct bad challenges yield non-proportional covectors, hence `#Bad·(q−1) + 1 ≤ q^d`, i.e. `#Bad ≤ 1 + q + ⋯ + q^{d−1}`.
4. *Deployed row* (p = 2³¹−2²⁴+1, K = F_{p⁶}, H = μ_{2²¹}, k = 2²⁰, B* = ⌊|K|/2¹²⁸⌋ = 274980728111395087): `#Fix(Frobenius) = p`; Frobenius-stable-mod-code pencils are safe at every radius with ε_mca < 2^−154.9; `p + 1 < B* < p² + 1` (checked as integer arithmetic); and the audit gate **`prizeBreaking_orbit_dim_ge_three`: any pencil breaking the Prize challenge threshold at any radius must have Frobenius-orbit dimension d ≥ 3.**

**Answer to the central question of the brief.** Frobenius is the only support-preserving mechanism that can tie the six base-field coordinate systems together (a domain symmetry moves the support, so it yields no contradiction). Full Galois tying is exactly orbit dimension d ≤ 2, and it caps the challenge set at p + 1 ≈ 2³¹·⁰ — 26.9 bits below the required 2⁵⁷·⁹³. So a Prize-scale extremizer cannot be Galois-compressed; it must sit at d ≥ 3, where the same argument degrades to ≈ p² ≈ 2⁶² and says nothing. The report also records exactly where the method stops: the necessary condition extracted is "the line point lies on a rational hyperplane of the orbit span", and that condition is Frobenius-closed, so improving it needs input Frobenius cannot see (degrees, domain, deviation geometry).

**Honest scope.** Grand MCA is not resolved. No better UNSAFE witness and no beyond-Johnson SAFE bound are produced; the d ≥ 3 statement is a necessary condition on a hypothetical Prize-breaking pencil. The "modulo the code" refinement of the classification (needing the additive descent step in K^D/C) is stated but not formalized. Nothing about the externally reported ScalarOrbitPencil witness is replayed or asserted; the only consequence for it is conditional (if it exists on this row, its orbit dimension is ≥ 3).

Write-up: `FROBENIUS_ORBIT_BUDGET_REPORT.md`, plus a new section 32 in `RESULTS.md`; `INDEX.md` regenerated with the project's own script. All work is committed and pushed.

# Summary of changes for run e66fa2dd-e382-4931-be56-34e62fe37827
**Verdict: [EXACT-NORMAL-FORM] + [SPREAD-INCIDENCE-DICTIONARY] + [RANK-GATE] + [BARRIER]. Grand MCA is NOT resolved, and I do not claim it is.**

I built the requested field-reduction / multiplication-algebra layer as machine-checked mathematics. Everything below is `sorry`-free, compiled module by module, uses only `propext / Classical.choice / Quot.sound` (audited in `RequestProject/FieldReductionAxiomAudit.lean`), and is stated against the project's official `IsBad / badSet / badWithPair / LineCloseOn / devActive / pairAgree` predicates. Nothing existing was modified or deleted; the certified UNSAFE row at agreement 1,116,048 is used as given, never re-proved or contradicted.

**1. The multiplication algebra is a Desarguesian spread** (`RequestProject/Root/CodingTheory/DesarguesianSpread.lean`). `mulLeft_sub_bijective`: for r ≠ s the difference ρ(r) − ρ(s) = ρ(r−s) of the regular representation of K/F is invertible — the matrix-spread-set property. Its graphs plus the vertical member give `spreadMember : Option K → Submodule F (K × K)`, the field-reduction image of P¹(K): distinct members meet only in 0, **every nonzero vector lies on exactly one member** (`existsUnique_spreadMember`, with slope map `spreadIndex`), each member has F-dimension [K:F], and the family is invariant under K-scaling and projective inversion.

**2. Official MCA is spread incidence** (`SpreadMCA.lean`). With the deviation vector `devVec x = (f₁x−c₁x, f₀x−c₀x)`: agreement of the γ-points at x holds **iff** `devVec x` lies on the spread member indexed by −γ. Consequences: the challenge is the slope (`spreadIndex_devVec`); every challenge explained by a codeword pair is the slope of one of its deviation vectors (`badWithPair_subset_image_challengeAt`) — the challenge coordinate is replaced by the set of spread members met by the deviation locus; and an **exact, iff description of the fibre** (`mem_badWithPair_iff_votes` with `mem_votes_iff`): γ is explained exactly when the member −γ carries all but ≤ e of the deviation vectors and the resulting support is not line-close.

**3. Rank (linear-set) theorem** (`SpreadMCA.lean`). If the deviation locus lies in an F-subspace W ⊆ K × K, then `(|F| − 1)·m + 1 ≤ |F|^{dim_F W}` — m is at most the number of points of a linear set of that rank. Hence a rank-one deviation locus explains **at most one** challenge, and if every big pair of a line has rank-one deviation then #Bad ≤ max 1 (#bigPairs).

**4. The exact normal form** (`FieldReductionNormalForm.lean`). `repr_lineComb`: in coordinates the line is literally U + M(γ)·V with M(γ) the regular-representation matrix. `isCloseOn_iff_forall_coord` / `mem_reedSolomonCode_iff_coord` / `lineCloseOn_iff_coord` / `isBad_iff_coord`: for a domain inside the base field, extension-field RS agreement is exactly the interleaved base-field problem **on one common support**, with the correlated (¬LineCloseOn) clause preserved verbatim — no six independent list-decoding problems anywhere.

**5. Deployed row** (`KoalaBearFieldReduction.lean`), p = 2^31−2^24+1, K = F_{p^6}, H = μ_{2^21}, k = 2^20: every evaluation point is proved base-field rational (`secKB_spec`), giving `isBad_iff_coord_deployed` and `mem_badSet_iff_coord_deployed` (the row's badness in six-coordinate common-support form), plus the deployed rank gate `card_badWithPair_rank_bound_deployed` and `heavy_pair_rank_ge_two_deployed` (any pair explaining ≥ 2 official challenges has F_p-deviation-rank ≥ 2).

**6. Barrier — honest calibration** (`SpreadIncidenceBarrier.lean`). `exists_spread_configuration`: whenever m·(a−e) ≤ a there **is** a spread configuration realising m challenges with a vectors, each member carrying ≥ a−e. So `m·(|A|−e) ≤ |A|` is the *complete* content of the field-reduction picture of the fibre; the rank theorem only bites at rank 1 on the deployed row (rank 2 already permits ≈ 2.1·10^9 challenges per pair, far above the per-pair ceiling e+1 ≈ 9.8·10^5). Any further gain must use information the spread does not see: Reed–Solomon degrees, locator/syndrome geometry, or the evaluation domain.

**Main goal.** Grand MCA is not proved and not disproved here. What the run delivers is a faithful, basis-independent reformulation (the K-line MCA question becomes: how many members of the Desarguesian spread can carry ≥ |A| − e deviation vectors of a Reed–Solomon codeword pair on μ_{2^21}?) together with the exact fibre law, one genuine structural gate, and a proof that the geometry alone cannot do better.

Write-up: `FIELD_REDUCTION_SPREAD_REPORT.md`, plus new section 31 in `RESULTS.md`. The Properties table lists the new declarations. All work is committed and pushed.

# Summary of changes for run 1f0c41db-a885-409a-a811-9e095dd291b3
**Verdict: [WEIGHTED-LIST-REDUCTION]** — the requested weighted interleaved list profile now exists as machine-checked mathematics, together with its multiplicity stratification, the abundance bridge, and the exact deployed numbers. No advance past Johnson and no Grand-MCA resolution is claimed; the precise obstruction is proved instead.

Everything below is `sorry`-free, was compiled module by module, uses only `propext`/`Classical.choice`/`Quot.sound` (audited in `RequestProject/WeightedListAxiomAudit.lean`), and is stated against the project's official `IsBad / badSet / epsMCA / LineCloseOn` predicates.

**Main Question A — the layer cake** (`RequestProject/Root/CodingTheory/WeightedInterleavedList.lean`). With the interleaved pair profile `L₂(r) = #{(c₀,c₁) ∈ RS_k(D)² : |{x : f₀x≠c₀x ∨ f₁x≠c₁x}| ≤ r}` (`pairListProfile`) and the multiplicity radius `pairRadius e m = ⌊m·e/(m−1)⌋` (`= 2e` for `m ≤ 1`):
`#Bad ≤ max 1 (Σ_{m=1}^{e+1} L₂(pairRadius e m))` (`card_badSet_le_sum_pairListProfile`). The layers are evaluated at strictly decreasing radii, from `2e` down to `e+1`; the coarse `(e+1)·#bigPairs` bound is literally this sum with every layer replaced by its largest term. Stratified form for any threshold `M`: `#Bad ≤ max 1 ((M−1)·L₂(2e) + (e+2−M)·L₂(r))`, plus the empty-heavy-sector corollary. The covering step of the earlier spread reduction was factored out (`card_badSet_le_sum_card_badWithPair`), from which the previous spread-weight theorem is now a short corollary.

**Deployed pivot** (`DeployedWeightedList.lean`, on the actual row `D = μ_{2^21} ⊆ F_{p^6}`, `k = 2^20`, `δ = 61319/131072`, `e = 981104`). Proved exactly: for `m ≥ 2`, `pairRadius e m ≤ n − k = n/2 ⟺ m ≥ 16` (`m = 15 : 1051182`, `m = 16 : 1046510`). Hence `#Bad ≤ max 1 (15·L₂(1962208) + 981090·L₂(1046510))`, and the audit gates: `#Bad > B* = 274980728111395087` forces **either** a codeword pair explaining ≥ 16 challenges (block radius `1046510 < n/2`) **or** `L₂(2e) ≥ 18332048540759673 ≈ 1.83·10^16`; at the `2^59+1` scale, `≥ 38430716820228233`. The coarse gates named in the request are reproduced as theorems: `≥ 280276553592 ≈ 2.80·10^11` big pairs (prize) and `≥ 587562750474 ≈ 5.88·10^11` (`2^59+1`).

**Main Question B — abundance bridge: proved, with a sharp obstruction.** `L₂(r)·C(|D|−r,k) ≤ C(|D|,k)`, the MDS `k`-subset double count transported from challenges to codeword pairs (via the new pair agreement bound `card_jointAgree_inter_le`). It is non-vacuous iff `r + k ≤ |D|`, and on the deployed row that happens **exactly at `m = 16`** — the same integer as the heavy/light pivot, because the rate is 1/2. So heavy = abundance-visible, light = abundance-blind: at the joint radius `2e` one has `C(n−2e,k) = 0`, the bridge is empty, and this is the precise obstruction to using the MDS/incidence abundance line in the light sector.

**Heavy sector — reduced, then blocked.** The heavy sector is reduced to interleaved list decoding at relative block radius `0.4990`, but the guaranteed agreement `1050642` satisfies `1050642² < n·k`, strictly below the Johnson agreement `√(n·k) ≈ 1482910` (`heavy_agreement_sq_lt_johnson`), so no Johnson/Fisher pairwise count closes it and the abundance bridge, though non-vacuous, is quantitatively inert there.

**Main Question C.** The candidate `d_r(C²) = N − k + ⌈r/2⌉` is correct, but was deliberately not formalised under the mission's own gate: its decisive reading is `d_2 = d_1`, i.e. rank 2 in the pair code buys nothing over the `k−1` agreement bound already in use, and rank-1 pencils of pairs can be as large as the field, so no usable rank-vs-fibre or rank-vs-abundance consequence exists here. The assessment is written up rather than encoded.

Write-up and novelty gate: `WEIGHTED_INTERLEAVED_LIST_REPORT.md`, plus a new section 30 in `RESULTS.md`. The Properties table lists the new definitions and the nine new proved statements. All work is committed and pushed.

# Summary of changes for run e68110bd-45fa-4ae9-a8fd-e40b69467d95
**Verdict: [INCIDENCE-REDUCTION]** — a machine-checked, `sorry`-free elimination of the challenge coordinate from official MCA, with a *coloured* (spread-sensitive) fibre law. No claim of a post-Johnson or Grand-MCA advance is made.

**What was done.** Following the mission's own suggestion, I studied the incidence set of official badness witnesses `I_e = {(γ,S,q) : |S| ≥ N−e, (f₀+γf₁)|_S = q|_S, ¬LineCloseOn S f₀ f₁}` and its projection to the challenge coordinate, all against the project's official `IsBad / badSet / LineCloseOn` predicates for Reed–Solomon on an arbitrary evaluation domain.

New results (all in `RequestProject/Root/CodingTheory/SpreadIncidence.lean`, axioms audited in `RequestProject/SpreadIncidenceAxiomAudit.lean`: only `propext`, `Classical.choice`, `Quot.sound`):

- **Fibre law.** Every witness is attached to a codeword pair `(c₀,c₁)`; the fibre over it is governed by the *deviation-active set* `A = {x ∈ D : f₀x ≠ c₀x or f₁x ≠ c₁x}` via `m ≤ |A|` and the spread inequality `m·(|A|−e) ≤ |A|`, hence `m ≤ spreadWeight e |A|` and `m ≤ e+1` **unconditionally** — no window, no bound on the radius, no field-size condition.
- **Reduction.** `#Bad ≤ max 1 (Σ over big pairs of spreadWeight e |A_p|)`, with the coarse corollary `#Bad ≤ max 1 ((e+1)·#bigPairs)` per line, and a probability form for `ε_mca`. The challenge coordinate disappears; only a spread-weighted count of codeword pairs jointly close to the line remains — data of the evaluation domain.
- **Colour matters.** A pair whose deviation is spread over `2e` positions contributes at most `2`, not `e+1` (`card_badSet_le_two_scale`), and a pair explaining `m` challenges has joint deviation `|A| ≤ m·e/(m−1) ≤ 2e`; extremal multiplicity `e+1` forces `|A| ≤ e+1`, so heavy fibres live at joint radius ≈ `e`, not `2e`.
- **Second-order geometry.** Two distinct pairs cannot both be concentrated: `N ≤ |A| + |A′| + (k−1)`, giving `(m−1)(m′−1)N ≤ (m′−1)me + (m−1)m′e + (m−1)(m′−1)(k−1)`; for `m = m′` this is `(m−1)(N−k+1) ≤ 2me`, a fibre bound valid throughout `2e < N−k+1` and much smaller than `e+1` inside that range.
- **Non-vacuity on the known failure row** (`RequestProject/Root/CodingTheory/SpreadIncidenceWitness.lean`): on the smallest counterexample (`|D| = 8 ⊆ F₁₃`, `k = 3`, `e = 2`, four bad challenges) the pair invariant is proved to be `≥ 2` — the excess over `e+1` is caused by a second codeword pair, not by freedom in the challenge.

**Honest scope.** I do not claim a machine-checked separation between smooth multiplicative and generic evaluation domains, and I do not claim any result beyond Johnson. What the reduction does is isolate the remaining question in challenge-free form: bound the number of codeword pairs jointly agreeing with a fixed pair of words outside `2e` positions (and, for the heavy contributions, outside `≈ e` positions) on a smooth multiplicative domain. `SPREAD_INCIDENCE_REPORT.md` states this, the novelty gate against the project's existing line-decodability/list-decodability chain, and a corrected version of the mission instruction (eliminate the challenge coordinate → colour the fibre law → only then ask the domain question; and note that no *unconditional* post-window improvement can exist, since the project's coset family already refutes it).

New/updated files: `RequestProject/Root/CodingTheory/SpreadIncidence.lean`, `RequestProject/Root/CodingTheory/SpreadIncidenceWitness.lean`, `RequestProject/SpreadIncidenceAxiomAudit.lean`, `SPREAD_INCIDENCE_REPORT.md`, new section 29 in `RESULTS.md`. All modules build cleanly (verified per module) and contain no `sorry`; everything is committed and pushed.

# Summary of changes for run 48b9efde-1cb1-4a9c-8ce6-f2df23ef7616
**STATUS: [GENERAL-INVARIANT]** (Pytanie B) — z werdyktem **[SUBSUMED-BY-SOTA]** dla proponowanego wariantu ℓ-warstwowego (Pytanie A). Brak postępu w kierunku Grand MCA i tego nie twierdzę.

**Question A — novelty gate (nie formalizowałem słabszego wariantu).** Proponowany licznik `(ℓ+1)e+μ<N ⇒ #Bad ≤ max(ℓ−1,(ℓ−1)ℓe)` jest zdominowany przez wynik, który już jest w projekcie: dla generatora potęgowego nad RS w tym samym oknie zachodzi `#Bad ≤ (ℓ−1)(e+1)` i ta stała jest osiągana (np. ℓ=3, e=10: proponowane 60 wobec faktycznego maksimum 22). Zgodnie z bramką nie formalizowałem go jako słabszego przypadku szczególnego.

**Question B — twierdzenie na poziomie niezmienników (nowe, maszynowo sprawdzone, bez `sorry`, aksjomaty tylko `propext/Classical.choice/Quot.sound`).** MCA w reżimie typu unique-decoding zależy dokładnie od trzech liczb: separacji kodu `σ` (= N − d), liczby „zero-evading” `B` generatora (maks. liczba wyzwań na hiperpłaszczyźnie w `F^ℓ`) i długości `N`:

* `card_badSetAbs_le_of_zeroEvading`: `σ + (B+2)e < N ⇒ #Bad ≤ B(e+1)` — dla **dowolnego kodu liniowego** `C ⊆ (Ω → M)` (alfabet symboli `M` to dowolna przestrzeń liniowa nad `F`, więc kody złożone/folded są objęte), **dowolnego alfabetu wyzwań** `Γ ⊆ F` i **dowolnego generatora** zero-evading; bez zależności od `|F|`. Wersja „łukowa”: `σ+(ℓ+1)e<N ⇒ #Bad ≤ max(ℓ−1, B(e+1))`, oraz postać korelowanej zgodności `allCloseOn_of_card_close_gt`.
* `interp_of_card_gt` (zasada łuku): interpolacja nie jest osobnym założeniem — więcej niż `B` wyzwań generatora zero-evading rozpina `F^ℓ`.
* Instancje generatorów: potęgowy, jednomianowy o różnych wykładnikach, **dowolny generator wielomianowy** o niezależnych składowych stopnia ≤ B, oraz **wymierny (Cauchy'ego)** `1/(γ−a_j)` — ten ostatni nie jest generatorem wielomianowym, więc leży poza zakresem twierdzeń o generatorach wielomianowych, a spełnia tę samą granicę.
* Instancje kodów: dowolny kod liniowy (`σ = N−d`), Reed–Solomon (`σ = k−1`), dowolny kod ewaluacyjny z ograniczeniem liczby zer (dla `C_L(G)` na krzywej hipoteza to klasyczne `σ = deg G`), **Reed–Muller** na siatce `S^n` (`σ = d·|S|^{n−1}`, dowód z Schwartza–Zippela — dziedzina ewaluacji nie jest `P¹`), oraz **kody folded** (`⌊σ/s⌋`).
* Spójność: `card_badSetG_le_via_general` odtwarza konkretne twierdzenie RS z projektu jako instancję abstrakcyjnego.
* Ostrość: `exists_card_badSetAbs_eq_sharp` — granica `B(e+1)` jest osiągana; `exists_badSetAbs_ge_at_window_boundary` — jeden krok za oknem (`σ+(ℓ+1)e = N`) zbiór zły jest nieograniczony (transport istniejącej rodziny kosetowej projektu). Razem: w niezmiennikach `(σ,B,N)` nic więcej wycisnąć się nie da, więc każde przejście poza granicę unique decoding musi użyć struktury, której te niezmienniki nie widzą — to jest bariera, a nie postęp w Grand MCA.

**Zakres i uczciwość.** W tym środowisku nie było dostępu do literatury zewnętrznej, więc porównanie z Bordage–Chiesa–Guan–Manzur robię wobec opisu podanego w zadaniu, nie wobec tekstu; wynik pokrywa się z nim po stronie kodu, a rozszerza po stronie generatora (nie „wielomianowość”, lecz zero-evading/łuk) i alfabetu. Żaden istniejący kontrprzykład ani świadek ostrości nie został usunięty ani zmieniony; rodzina kosetowa została wykorzystana do dowodu optymalności okna.

**Pliki:** `RequestProject/Root/CodingTheory/GeneralMCAInvariant.lean` (niezmienniki i twierdzenia główne), `GeneralMCAInstances.lean` (generatory, kody, odtworzenie RS, ostrość, kody folded), `GeneralMCAReedMuller.lean`, `GeneralMCAWindowSharp.lean`, audyt aksjomatów `RequestProject/GenMCAAxiomAudit.lean`; opis i bramka nowości w `GENERAL_MCA_INVARIANT_REPORT.md`, nowa sekcja 28 w `RESULTS.md`. Wszystkie moduły kompilują się czysto (bez `sorry`, bez ostrzeżeń lintera), a tabela właściwości została uzupełniona o nowe definicje i dwanaście udowodnionych twierdzeń. Całość jest zacommitowana i wypchnięta.

# Summary of changes for run 7e15ab35-eb06-4c62-8e69-ed376e473ab8
**Result: [ENTROPY-REDUCTION] — a machine-checked structural reduction that removes a large class of possible extremizers from the whole Johnson→capacity corridor of the deployed row.**

Everything below is `sorry`-free, uses only `propext / Classical.choice / Quot.sound`, is stated against the project's own official `IsBad / badSet / epsMCA` predicate, and was compiled module-by-module (no full project build).

**1. The descent theorem** (`RequestProject/Root/CodingTheory/SubfieldDescent.lean`).
If a ring endomorphism σ of the code field fixes every evaluation point of the domain and every value of both words of the pencil, then *every* officially bad challenge is fixed by σ (`isBad_fixed_of_ringHom`). Proof: applying σ to the witness equation `f₀+γf₁ = P` on the support S and subtracting gives `(γ−σγ)f₁ = P−P^σ` on S, so if `σγ ≠ γ` both `f₀` and `f₁` are explained on the *same* support — exactly the correlated-agreement event badness forbids. Consequences: a pencil rational over a subfield of size q has `#Bad ≤ q`; a pencil merely *spanning* a base-field-rational plane (arbitrary invertible linear reparametrisation) has `#Bad ≤ p+1`; `ε_mca ≤ p/|F|`.

**2. The deployed row** (`RequestProject/Root/CodingTheory/KoalaBearRowDescent.lean`). All arithmetic is checked inside Lean: `p = 2^31−2^24+1 = 2130706433` proved prime, `2^21 ∣ p−1`, `F = F_{p^6}` (186 bits), `H = μ_{2^21}` realised with cardinality exactly `2^21` and contained in `F_p`, `k = 2^20` (rate 1/2), `B* = ⌊|F|/2^128⌋ = 274980728111395087`. Then for **every** radius e (hence throughout the corridor from finite Johnson `J ≈ 0.2928936` to `δ_min = 1048577/2097152`) and every pencil valued in the base field: `#Bad ≤ p < 2^31`, i.e. `#Bad < B*` with ~27 bits of slack, and `ε_mca ≤ p^{-5} < 2^{-154.9} ≪ 2^{-128}`. This is proved for plain pencils, for base-field-rational *planes*, and for polynomial pencils with base-field coefficients — so every power pencil `x^a`, hence every coset-union / graded / HalfGap-type construction and every one-hot triangle, is safe on that row at every radius. The contrapositive is registered as the mandatory cheap rejection test. For proper subfields the gate is quantitative: an `F_{p^2}`-rational counterexample would need more than 1/17 of the entire subfield `F_{p^2}` to be bad; an `F_{p^3}`-rational one, more than a `2^{-36}` fraction.

**Prize-gain scoring.** SAFE gain: not a field-uniform endpoint, but a *class* SAFE result valid on the entire interval `[0, δ_min]`. UNSAFE gain: none claimed; the reported upper endpoint `δ ≈ 0.467826843` is unchanged. Challenge entropy: the theorem is an exact challenge-image bound, `log₂ #Bad ≤ 30.99` for base-field data against the required `≈ 57.93` — a 26.9-bit deficit (`61.98` bits for `F_{p^2}` data, hence the density gate).

**Measurements before formalization** (`analysis/subfield_descent_check.py`, `analysis/challenge_image_entropy.py`, exact finite-field arithmetic). A brute-force check of the literal predicate found no bad challenge outside the subfield. In a scaled analogue *inside* the corridor (`F_{97^2}`, `μ_16 ⊆ F_97`, n=16, k=8, δ=0.4375 > J=0.3386) base-field and power pencils attain exactly 97 distinct challenges — the cap is tight — while pencils with extension coefficients of degree ≥ k+2 reach ≈ 5820 of 9409. These are labelled measurements, not theorems.

**Audit note on the external evidence.** The referenced OrbitPencil files are not present in this tree, so nothing about them is replayed or asserted. The theorem does give a sharp conditional audit gate, stated in the report: on this row `#Bad ≥ 2^59+1` is impossible for base-field-valued words or base-field-rational planes at any radius, and would require over 12 % of `F_{p^2}` to be bad if the words were `F_{p^2}`-valued — so if that construction is "scalar" in the base-field sense, the challenge-image step is the first gate to re-check; otherwise its pencil must generate at least `F_{p^2}`.

Analysis of where a counterexample must now live is in `GRAND_MCA_SUBFIELD_DESCENT_REPORT.md` §5: in the coset picture the challenge sees the support only through elementary symmetric functions in `F_p`, so any mechanism whose challenge factors through *one* such coordinate caps at `2^31` regardless of its coefficient field; two independent coordinates (degree `j+1` pencils with `F_p`-independent extension coefficients) are needed to reach `2^62`. Full write-up in that report, with a new section 27 of `RESULTS.md`; the Properties table lists the six new proved statements. `ARISTOTLE_SUMMARY.md` was not modified.

# Summary of changes for run a0f42c17-d195-4f22-85d0-af8425ea3cd9
**Verdict: `[GRAND-MCA-EXACT-ROW]` — both sides of the requested row are now machine-checked — together with `[DEFINITION-ENDPOINT]` for the "largest δ*" phrasing.**

Everything below is `sorry`-free, builds with the module targets only (no full project build), and uses no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (no `native_decide`).

**1. The field — with one correction to the submitted certificate** (`RequestProject/Root/CodingTheory/ProthPrimeCertificate.lean`).
`q = 5·2^127 + 1 = 850705917302346158658436518579420528641` is proved prime (`Root.NumberTheory.qProth_prime`). The submitted witness `3` does satisfy `3^((q−1)/2) ≡ −1`, but it is **not** usable with the available Lucas primality test: an exact computation gives `3^((q−1)/5) ≡ 1 (mod q)`, so `3` has order `2^127`, not `q − 1`. The base `17` satisfies both Lucas conditions and is what is certified, via an explicit chain of 127 repeated squarings on 130-bit numerals plus two fifth powers. Also proved: `q − 1 = 5·2^127`, `512 ∣ q − 1`, and `2^129 < q < 3·2^128` (so `⌊q/2^128⌋ = 2`).

**2. The row and both sides** (`RequestProject/Root/CodingTheory/GrandMCAExactThreshold.lean`). `H = μ_512` is identified as exactly the set of 512-th roots of unity in `F_q` (`dom_eq_nthRootsFinset`), rate `1/2`, `C = RS_256(H)`.
- *Safe:* at every integer radius `e ≤ 1`, **every** line satisfies `ε_mca < 2^-128` (`epsMCA_le_of_radius_le_one`, and for the maximum over lines `epsMCAmax_le_of_radius_le_one`). This uses the repository's existing dichotomy `card_badSet_le_succ_radius_of_le` (`k + 3e ≤ |D| → #Bad ≤ e+1`), whose hypotheses I checked against the actual statement: `256 + 3·1 = 259 ≤ 512`.
- *Unsafe:* the explicit triangle pencil `f₀ = 2·1_a + 1_b`, `f₁ = −1_a − 1_b + 1_c` on the domain points `1, θ, θ²` has the three distinct bad challenges `0, 1, 2` at radius `e = 2` (`δ = 1/256`), hence `ε_mca ≥ 3/q > 2^-128`, and likewise at every larger radius.
- *Exact:* at `e = 2` the bad set has **exactly three** elements, so the critical integer radius is `e_crit = 2` (`card_badSet_eq_three`, packaged as `exists_exact_grandMCA_row`).

**3. The endpoint, stated openly.** Reading a real radius `δ` as the integer radius `⌊δ·n⌋`, the set of safe radii is exactly `[0, 1/256)` (`safeRadii_eq`): its supremum is `δ* = 1/256` (`isLUB_safeRadii`) and `1/256` itself is already unsafe (`one_div_256_notMem_safeRadii`). So at finite block length with the closed support threshold the literal "largest δ*" has no solution at this row; the well-posed invariants are `e_crit = 2` and the supremal safe radius `δ* = 1/256`.

**4. Generalisation kept small but sharp.** The unsafe mechanism is proved once, in general form: `not_isCloseOn_oneHot` (a one-hot word is never explained by a degree-`<k` polynomial on a large support), `isBad_of_oneHot_witness`, `triangle_isBad_zero/one/two`, `three_le_card_badSet_triangle` — valid over any field of characteristic ≠ 2 and any domain with `k + 3 ≤ |D|`. Combined with the existing cap this yields `card_badSet_triangle_eq_three`: the `#Bad ≤ e+1` bound is **sharp at `e = 2`**.

**5. Audit and honest scope** (`GRAND_MCA_EXACT_THRESHOLD_REPORT.md`, plus a new section 26 in `RESULTS.md`). There is no network access and no copy of the external literature in the project, so no definition-level comparison with any printed text is claimed; what is certified is the project's own `IsBad`/`epsMCA` (uniform challenge over the whole field, closed threshold, γ-dependent support, same-support noncontainment). The report also compares with the project's earlier rows (the `125/256` seven-witness certificate and the coset variants) and with `HalfGapPencil` — the triangle is not a specialisation of it — and notes explicitly that this row is unsafe only because the field is deliberately tiny relative to `2^-128`; over a 256-bit field the same line gives `3/q ≈ 2^-254`.

Per the priority reset I stopped work on the `δ = 3/8` coset strengthening (that line of work is not part of this delivery); the report records why it is superseded for the threshold question. The Properties table has been updated with the new definitions and the seven new proved statements.


# Summary of changes for run 21a0c3a3-a027-408e-b8fe-2e6bc242b4d1
**Verdict: [GRAND-MCA-UNSAFE-7]** — the requested row is now settled by a machine-checked, `sorry`-free certificate, and it needed no census replay and no Cycle84→116/119 transfer at all.

**The certificate** (`RequestProject/Root/CodingTheory/GrandMCASevenWitness.lean`, builds clean; axioms `propext`, `Classical.choice`, `Quot.sound` only).

For `K = F_17^32`, `H = μ_512 ⊆ K*` (`512 = 2^9`; `v₂(17^32−1) = 9`, so `H` is the full 2-Sylow), `C = RS_256(H)`, radius `e = 250` (`δ = 125/256`, closed agreement threshold `262`), the **single** pencil `f₀(x) = x^264`, `f₁(x) = x^256` has seven pairwise distinct officially bad challenges
`γ_t = −(Σ_{i<32} θ^{8i} + θ^{256+8t})`, `t = 0..6`.
Each is witnessed on the union `S_t` of `33` of the `64` `μ_8`-cosets of `H`: `|S_t| = 264`, the vanishing polynomial of `S_t` is `X^264 − (Σ_{i∈I_t} b_i)X^256 + (degree ≤ 248)`, so `f₀ + γ_t f₁` is explained by the code on `S_t`, while `f₁ = x^256` is not — the same-support non-containment event. Agreement `264` covers both the closed threshold `262` and the strict reading `263`. Since `⌊17^32/2^128⌋ = 6`, seven witnesses suffice: `ε_mca ≥ 7/17^32 > 2^{-128}` (`7·2^128 > 17^32`).

Key proved statements: `isBad_wit` (in fact 32 witnesses, at radius 248), `official_event` (event unfolded, agreement ≥ 264), `card_gammas` (distinctness), `seven_le_card_badSet`, `epsMCA_gt_two_pow_neg_128`, `exists_grandMCA_seven_witness`. Supporting new theory: `μ_d`-coset domains `mulDomain`/`mulCoset` with binomial vanishing polynomials **over an arbitrary field** (the project previously had only the `ZMod p` version), plus radius monotonicity of the official predicate. The construction was independently replayed numerically in a scaled-down analogue (`n=32, d=8, k=16` over `F_97`).

**Source/authority gate — honest scope.** The predicate certified is the project's official `IsBad`/`epsMCA`: closed threshold, same support, non-containment, challenge uniform over the whole field `K`; arbitrary finite field, smooth subgroup domain, rate 1/2. No external document could be consulted in this environment and the referenced Cycle84/116/119/120 packet is not present in the repository, so the file does **not** claim verified agreement with any printed Definition 4.3 — that comparison is flagged in `GRAND_MCA_SEVEN_WITNESS_REPORT.md`, together with the one point that would need re-running if a definition restricted the challenge alphabet.

**Secondary (work done before the reset, now recorded, route paused).** The exact `c = 2` dictionary is validated and formalised informally in `analysis/`: incidence is a single *alternating bilinear* (Plücker) condition `⟨ω_E, f₀∧f₁⟩ = 0` with kernel `(y−x)Λ_E(x)Λ_E(y)/(Z_D'(x)Z_D'(y))`. Exact experiments confirm your warning quantitatively: a plane carrying a weight-1 error meets `C(n−1,e−1)` supports (165 of 495 for `RS[12,6], e=4`; 3003 for `RS[16,8], e=6`) that all collapse to **one** challenge, versus graded optima of 15 and 56 — so support counts cannot support a dichotomy; the coloured map `E ↦ γ(E)` is the right object. An exact Klein-quadric classification at `e = 2` (all planes with ≥4 incidences, no sampling) finds the incidence maximum attained by degenerate planes `W = U_{E₀}` and the challenge maximum equal to the graded optimum, with no non-block extremizer.

Everything is committed and pushed; details in `GRAND_MCA_SEVEN_WITNESS_REPORT.md` and a new section 25 of `RESULTS.md`.

# Summary of changes for run b8336778-11f2-4a8b-969e-3e836b4047cf
## Outcome: **[STRUCTURAL REDUCTION]** — the syndrome-line mechanism is pinned exactly, and its construction side is strengthened

I worked only on the Grand-MCA question as posed (official `IsBad`/`badSet` predicate); I did not touch the unique-decoding-hole, packing, or OrbitPencil material. Full write-up in `GRAND_MCA_SYNDROME_LINE_REPORT.md`.

### 1. The gates you asked for — and why they cannot decide anything
I built an exact syndrome-space computation of the official bad set (`analysis/gr2_syndrome_incidence.py`) and **validated it against a literal implementation of the predicate** (`analysis/gr2_validate.py`, exact agreement on five parameter sets).

Over the stated fields, a *uniformly random* line already has every challenge bad:
`RS[10,5]/F_11` at `e=4` and at `e=3` → `#Bad = 11 = |F|`; `RS[12,6]/F_13` at `e=4` → `#Bad = 13 = |F|`. So the "10 distinct bad challenges" phenomenon is a field-size artefact (`|F| ≈ n`), not a mechanism, and the gate as posed is uninformative. Re-run at `|F| ≈ 10⁶` the picture becomes sharp.

### 2. New machine-checked theory (both modules `sorry`-free; axioms `propext, Classical.choice, Quot.sound` only)

`RequestProject/Root/CodingTheory/SyndromeLineIncidence.lean`
- `lineCloseOn_iff`, `isBad_iff_exists_window` — the predicate in plane/window form.
- `isBad_reparam`, `card_badSet_reparam_le` — a change of basis of the plane transports the bad set through the corresponding Möbius map and changes `#Bad` by at most one. This is the formal justification for using the **unparameterised plane** rather than the pair.
- `card_badSet_le_card_windows` — a FULL-MCA window witnesses at most one challenge, hence `#Bad ≤ |𝒲|` for any covering family of windows.
- `card_badSet_le_two_pow_of_saturated`, `card_badSet_le_choose_of_blockWindows` — **the cap**: if every witness window is a union of parts of a partition into `n/d` blocks then `#Bad ≤ 2^{n/d}`; if the windows use `s+1` of `m` blocks then `#Bad ≤ C(m, s+1)`.

`RequestProject/Root/CodingTheory/HalfGapPencil.lean`
- A sharpened shape lemma and a decoupled power pencil give `#Bad ≥ C(m, s+1)` at dimension `d·s − j` and absolute capacity gap `c = d + j` for **every** `j < d` (`card_badSet_ge_blocks_halfGap`), realised on an explicit coset domain and unconditionally (`card_badSet_ge_cosets_halfGap`, `exists_halfGap_counterexample`).
- Consequence: blocks of size only `d = ⌈(c+1)/2⌉` — **half the gap** — suffice, so at gap `c` the bound improves from `C(n/c, ·)` to `C(≈2n/(c+1), ·)`, roughly squaring the previously available exponential lower bound and removing the divisibility constraint it carried. Exact computations confirm the counts (e.g. `n=24, k=11, e=10, c=3`: `#Bad = 792 = C(12,7)`, computed over all `C(24,10)` supports).

### 3. The quantified verdict
Upper and lower bounds now match: the block/grading mechanism yields exactly `C(m, s+1)` bad challenges with `m = n/d`, and reaches gap `c` only for `d ≥ (c+1)/2`. Hence
`#Bad_graded ≤ 2^{n/d} ≤ 2^{2n/(c+1)} = exp(O(1/η))` in the relative gap `η = c/n`.
So this mechanism is exponential at a constant *absolute* gap (already known here qualitatively, now with a doubled exponent) and **bounded independently of `n` at a constant *relative* gap** — it cannot produce a Grand-MCA counterexample in the FRI/STARK-relevant regime. Local search at `|F| ≈ 10⁶`, seeded at the graded optimum, does not improve on it (apparent improvements at `|F| ≈ 10³` are accidental-incidence noise).

The remaining route is exactly what the cap does not cover: planes meeting error-support subspaces that are **not** orbit-closed for any coarse partition; the master counting principle reduces Grand MCA to how many of the `C(n,e)` subspaces one plane can meet non-degenerately.

All work is committed and pushed; the Properties table lists the nine new results, each marked proved.

# Summary of changes for run 6b53078b-2928-4999-94b2-6ff08383ceb4
## What I worked on

The identifiers in the request (`Q = 147595`, `k = 4981`, the aggregate cap `2157928`, "rank-seven survivor") do not occur anywhere in this repository — I re-checked the live sources rather than inheriting any earlier interpretation. Following the direction agreed earlier in this project, I therefore worked on the strongest *live* obstruction that the repository actually records: the open item **(UD-hole)** in `MCA_ROUTE_DECISION.md` §0 —

> does strict unique decoding `k + 2e < |D|` (together with a totally degenerate Welch–Berlekamp pencil) force the bad set of a line to satisfy `#bad ≤ e + 1`?

I recovered the live definitions (`IsBad`, `badSet`, `LineCloseOn`, `lineComb`) from the current sources and worked directly against them. No full project build was run at any point; only targeted single-module compilations.

## Result: the question is decided, negatively and quantitatively

Everything below is Lean-checked, `sorry`-free, and uses only `propext`, `Classical.choice`, `Quot.sound`.

1. **The bound is false** — `not_forall_card_badSet_le_succ_radius_of_strict_ud` and its pencil-degenerate strengthening (`RequestProject/Root/CodingTheory/UniqueDecodingHoleWitness.lean`): an explicit line over `ZMod 13` with `|D| = 8`, `k = 3`, `e = 2` has four bad parameters.

2. **The failure is unbounded, not an off-by-one** (new this session). `RequestProject/Root/CodingTheory/CosetBadFamilyMul.lean` builds a scalable family: for any field containing a primitive `e·m`-th root of unity, with `D = μ_{e·m}`, blocks the cosets of `μ_e`, and `k = |D| − 3e + 1`,
   - `CosetFamily.card_badSet_mulDomain_ge` : `#bad ≥ m − 1 = |D|/e − 1`;
   - `CosetFamily.exists_strictUD_badSet_ge N` : for every `N` there is a prime `p`, domain `μ_{p−1}`, rate `k = p − 6`, radius fixed at `e = 2`, with `#bad ≥ N`, all inside strict unique decoding (`k + 2e = p − 2 < |D|`). So **no bound `#bad ≤ g(e)` can hold**;
   - `CosetFamily.card_badSet_zmod13_ge` : a concrete instance (`ZMod 13`, `|D| = 12`, `k = 7`, `e = 2`, `#bad ≥ 5`).
   The supporting theory (seed line, per-block bad parameter) is in `RequestProject/Root/CodingTheory/CosetBadFamily.lean`.

3. **The anchor hypothesis is exactly sharp.** `card_badSet_le_or_card_lt` gives unconditionally: `#bad ≤ e + 1` **or** `|D| < k + 3e`. The new family lives precisely at `|D| = k + 3e − 1`, one step past the boundary, so the hypothesis `3e < |D| − k + 1` of `card_badSet_le_succ_radius` cannot be weakened at all.

4. **A new radius-free tool**: `card_le_of_pencil` — if one polynomial pencil explains every parameter of an arbitrary set `B`, then `#B ≤ e + 1`, with no relation between `k`, `e`, `|D|`. This bounds a single "pencil class"; the previous whole-bad-set version is now a corollary.

## Cheap experiments that changed the answer

Before formalising, exact computations (in `analysis/`) validated the family for `|D|` up to 40 and confirmed its fine structure (at most one block index can degenerate — exactly what the Lean proof exploits). A later probe **refuted** the natural matching upper bound: neither `⌊|D|/e⌋` nor `⌈|D|/e⌉` caps the bad set — over `ZMod 13`, `D = {0,…,7}`, `k = 1`, `e = 3` (strict UD) a line has 4 bad parameters, with error sets the four 3-subsets of `{0,3,4,6}` (`analysis/ud_hole_cap_refutation.py`).

## Remaining obstruction and best next step

Written up in `UD_HOLE_REPORT.md` §6–§7: the correct shape appears to be a **class–packing bound** `#bad ≤ (e+1)·M(|D|, e, 3e−c−1)` with `c = |D| − k`, where `M` counts `e`-subsets with pairwise intersections `≤ s`. It reproduces `e+1` when `c ≥ 3e`, gives `⌊|D|/e⌋` blocks at `c = 3e−1` (where the family lives), and explains the refuting example as one maximal pencil class. Step 1 of that programme (the relative pencil bound) is now proved; the two remaining pieces are the class-separation intersection bound and the elementary `s = 0` packing bound.

Measurements are labelled as such throughout and are not presented as verified theorems. The Properties table has been reconciled: the two refutation theorems are marked proved, and the three new results are registered.


# Summary of changes for run 50449b14-4925-4f9c-bb0f-a3520c726792
**Verdict: the requested bound is false as stated — the exact max/average factor is a power of two, and the sharp constant sits either at 8 (below your target) or at 16 and above (a genuine counterexample).**

Because the phrases "boundary-prefix atom", "first-match coherent primitive prefix/image fibre" and "large owner" have no counterpart anywhere in the existing sources, I fixed the one reading that is simultaneously Mersenne-31 specific, deployed and has a finite max/average constant to determine, and documented it openly in `PREFIX_FIBRE_ATOM_REPORT.md`: over `p = 2^s − 1` (`s = 31`), the atom `A_m = {0,…,2^m−1}` (residues whose top `s−m` boundary-prefix bits vanish), the deployed primitive free twiddles `2^k` (powers of the primitive `s`-th root of unity 2 used by the multiplication-free length-31 DFT), image buckets given by the `b` leading bits, and the fibre `{x ∈ A_m : prefix_b(2^k·x mod p) = j}` against the average `2^m/2^b`.

Measurement first, as asked (`analysis/prefix_fibre_atom_measure.py`, exhaustive over Mersenne exponents 5, 7, 13 and all `m,b,k`; 0 mismatches), then formalization in `RequestProject/PrefixFibre.lean` — compiled, no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound` only, and the Lean definitions cross-checked by `#eval` against the independent model.

What is proved:

- **Row-sharp exact law** on the coherent branch (`k+m ≤ s`, `k+b ≤ s`): every fibre count is exact, the largest fibre is bucket 0, and max fibre `= 2^min(s−k−m, b) ×` average — an identity, not an estimate. The factor is exactly `2^t` for the boundary overhang `t = s−k−m`.
- **Counterexample** at the deployed point `s=31, m=20, b=8, k=7`: the bucket-0 fibre has exactly `2^16 = 65536` elements against average `2^12 = 4096`, i.e. exactly `16 > 9.57219783037`. This is an outright refutation on a legitimate coherent (non-periodic) instance, not a surviving obstruction.
- **Proof below your constant where it can hold** (your preference 1): if `s ≤ k+m+3` every fibre is at most `8 ×` average, i.e. below `9.57219783037` with 19.65 % margin.
- **Exact criterion** (your preference 2 — the reduction to one simpler exact statement): for `b ≥ 4`, the requested bound holds for every bucket **iff** `s ≤ k+m+3`. The whole question collapses to a single integer, the boundary overhang; no primality, Sidon or asymptotic input enters. Over all 31 free twiddles at `m=20, b=8` the exact factor is `2^min(11−k,8)`, so the uniform sharp constant is 256 (2048 once `b ≥ 11`), not 9.57.
- **The excluded branches**, for completeness: the quotient/periodic branch (`s ≤ k+m`) is exactly uniform (factor 1); the wide-prefix branch (`m+k ≤ s ≤ k+b`) has singleton fibres and factor exactly `2^(b−m)`. The only unformalised corner is the doubly-wrapped one, which lies inside the excluded periodic branch.
- **Mersenne/KoalaBear consequence**: the law is exact because for `x < 2^s−1` multiplication by `2^k` *is* the cyclic rotation of the `s`-bit word (proved), so image prefixes are bit windows. For KoalaBear `2^31 − 2^24 + 1` no `2^k` with `1 ≤ k ≤ 31` is 1 (proved), so no word length makes the deployed twiddles rotate and the exact power-of-two law does not transfer; a clearly-labelled measurement gives max/average `2.0156` there in the folded regime.

Operationally: a routing/bucketing layer over M31 that twiddles small values by a free `2^k` and routes on the top `b` bits has worst-case bucket load *exactly* `2^min(s−k−m, b)` times average; to stay under a constant of size 9.57 one must take `k ≥ s−m−3` (or let the atom fold, which is perfectly uniform). Any other choice pays a power-of-two imbalance up to `2^(s−m)`.

Also added: `RESULTS.md` section 122 and the report `PREFIX_FIBRE_ATOM_REPORT.md`. Only the new module was compiled; no full project build was run, and `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 5b96108e-6327-46b2-ba0e-b94216a5cdc1
## What I did

I closed the remaining carrier branch by the shortest available route, sharpened the carrier architecture quantitatively, and pinned the deployed target's position exactly. Three new modules, all `sorry`-free; the whole project builds (`lake build`, 8299 jobs, 0 errors) and every new theorem is axiom-audited in `RequestProject/Main.lean` (`propext`, `Classical.choice`, `Quot.sound` only).

**1. The minimal "useful irreducible factor ⇒ affine formal root" step** (`RequestProject/Root/CodingTheory/AffineCarrier.lean`, ~200 lines). I did not rebuild the BCHKS/BCI+20 Hensel-lifting machinery. The decisive observation is that in the formal-line setting the *output* side is nearly free: for a carrier of the published shape `W = c·(Y − v₀(X) − Z·v₁(X))` the line residual at a position `x` is the linear polynomial `c·((f₀x − v₀(x)) + (f₁x − v₁(x))·Z)`, so
- `mem_lineSupport_iff_of_affineCarrier`: degeneracy of an affine carrier *is* simultaneous agreement of `f₀` with `v₀` and `f₁` with `v₁`;
- `isFormalRoot_of_affineCarrier`, `lineCloseOn_of_affineCarrier`, `correlatedAgreement_of_degenerate_affineCarrier`: it yields a `FormalRoot` of `Z`-degree ≤ 1, hence correlated agreement at radius `e+1`;
- `not_degenerate_of_affineCarrier_of_far` and `card_badSet_le_of_affine_carriers`: for a centre at distance `> e+1` from the code the branch is closed. The Hensel step enters only as the explicit hypothesis `haffine`; it is **not** reproved, and nothing in the repository asserts it.

**2. A quantitative improvement inside the architecture** (`CarrierBudget.lean`). The old counting charged the global budget `|D|·(dZ+L)` once per irreducible factor. Degrees are additive over a factorisation, so I introduced the total `Z`-degree `zDeg` (through `F[Z][X][Y] ≅ F[X][Y][Z]`), proved `zDegLe_iff` and `zDeg_multiset_prod` (additivity), and re-did the counting with a per-factor budget. The dichotomy bound improves from `dZ + L·|D|·(dZ+L)` to **`dZ + |D|·(dZ+L)`** — a factor of about `L = deg_Y Q` — and the closed branch inherits it (`card_badSet_le_of_affine_carriers_sharp`). This removes exactly one substantial `Y`-degree loss.

**3. Honest quantitative verdict.** No improvement over the published `n/η⁵` strong-MCA bound is claimed. Reason, recorded in `AFFINE_CARRIER_CLOSURE.md`: the chain still has no existence theorem for the formal-line interpolant with explicit `(L, dZ)`, so its leading term `|D|·(dZ+L)` has no numeric value yet; and by the project's own prize audit the MCA constant is worth 0 bits at the audited shape — only the radius reaches the score, and the carrier route lives strictly inside Johnson. So this branch, once completed, reproves Johnson-regime theory.

**4. The deployed target, machine-checked** (`DeployedTargetGap.lean`). For rate `1/2`, radius `0.46782684`: it is inside capacity (gap `0.03217316`), beyond Johnson (`(1−δ)² < ρ`), and the Johnson inequality fails by a factor `> 1.76`; consequently the project's Guruswami–Sudan condition `k·n·(m+1) < m·t²` is false there **for every multiplicity `m` and every block length**. The failure is structural, not a constant, so no fixed-step Johnson-type shortening reaches that row.

**5. Next obstruction.** Documented in `AFFINE_CARRIER_CLOSURE.md` §7: via the project's own far-centre reduction and indicator-line/list sandwich, a beyond-Johnson MCA bound at that point implies a polynomial list-size bound for an *explicit* rate-1/2 Reed–Solomon code on a smooth domain at radius 0.4678 — not known for any explicit RS code. The one unused smooth-domain asset is the `ℤ/n`-equivariance of the problem (an equivariance, not a bound); I list three concrete follow-ups, the cheapest being the search for a smooth-domain analogue of the repository's subspace-pencil family.

Documentation: `AFFINE_CARRIER_CLOSURE.md` (full write-up), `RESULTS.md` §121, regenerated `INDEX.md`, `Main.lean` axiom checks, and ten new entries in the Properties table. `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.


# Summary of changes for run 9d98047c-49e8-4ce1-931f-ad0834a9da15
## Report

**1. Strongest result added this session.** Two new machine-checked theorems, both of which shrink the open branch of the Reed–Solomon proximity-gap / mutual-correlated-agreement (MCA) chain.

- *Irreducible carrier dichotomy* (`RequestProject/Root/CodingTheory/CarrierDichotomy.lean`, §5): for a far-centred line and any trivariate interpolant `Q ∈ F[Z][X][Y]` killed by every close witness,
  `#badSet ≤ dZ + L·(|D|·(dZ+L))` **or** some *irreducible* factor `W ∣ Q` of *positive* `Y`-degree is degenerate along the formal line (`|D| ≤ |lineSupport W| + e + 1`).
  Declarations: `card_le_or_exists_degenerate_irreducible`, `card_badSet_le_or_exists_degenerate_irreducible`.

- *Gauss descent and the integral pair dichotomy* (new file `RequestProject/Root/CodingTheory/GaussDescent.lean`): the vanishing of the pair resultant is upgraded from a fraction-field statement to a concrete common factor over `F[Z][X]` itself. Key declarations: `dvd_of_map_dvd_map_of_irreducible`, `exists_irreducible_common_factor_descend`, `resultant_dichotomy_pair`, `resultant_dichotomy_descend`/`_trivariate`, and the MCA corollaries `card_goodZ_le_or_exists_common_irreducible`, `card_badSet_le_or_exists_common_irreducible`:
  `#badSet ≤ (bY+bY')·dZ` **or** the two interpolants share an irreducible factor of positive `Y`-degree in `F[Z][X][Y]`.

**2. Machine-checked?** Yes. Full project build: `Build completed successfully (8296 jobs)`, exit 0, no errors. No `sorry` in either file, and every new theorem reports axioms `[propext, Classical.choice, Quot.sound]` via the `#print axioms` block in `RequestProject/Main.lean`.

**3. MCA / Prize consequence.** No change to the achievable radius yet, and therefore no change to the prize row: the results are reductions, not a new bound. Their effect is that the far-centred Guruswami–Sudan route now has a *single* remaining branch, and that branch is a concrete trivariate polynomial (an irreducible factor of positive `Y`-degree) rather than a resultant-vanishing condition over a fraction field. Both prior non-degeneracy hypotheses of the chain (`pairRes ≠ 0` after specialisation, `discBiv ≠ 0`) are subsumed.

**4. Single remaining obstruction.** For a far-centred line, no irreducible `W ∈ F[Z][X][Y]` of `Y`-degree `≥ 2` dividing an interpolant may be degenerate along the formal line (i.e. `|lineSupport W| ≥ |D| − e`). The `Y`-degree-`1` case is already closed in the project; the `Y`-free case is bounded by `dZ` outright; the Gauss-lemma step previously listed alongside this one is now done.

**5. Shortest next attack.** Work over the function field of `W`: the close-challenge witnesses `p_γ` (degree `< k`) give many rational branches `Y − p_γ` of `specZ γ W`; combine the `Z⁰`-coefficient of the degeneracy (`W(0, x, f₀ x) = 0` at `≥ |D| − e` positions) with a degree input forcing the relevant root of `W(0, x, ·)` to be a codeword evaluation, contradicting `e < d(f₀, C)`. Attack `Y`-degree `2` first, where the branch is explicit through the discriminant of `W` in `Y`.

Notes on housekeeping: the report file `PAIR_RESULTANT_BIV_REPORT.md` has an added §6 documenting both new results and the updated obstruction; the new modules are imported and axiom-audited in `RequestProject/Main.lean`; the Properties table lists the five new theorems as proved. A pre-existing build breakage in `QuadraticFactorBranch.lean` had been repaired earlier in this line of work and remains green. All work is committed and pushed.

# Summary of changes for run 933853f4-1c10-4080-8fa9-472b2cb6b726
## What I did

I continued the far-centred Reed–Solomon proximity/MCA line of work and added one new, fully verified module, `RequestProject/Root/CodingTheory/WitnessElimination.lean` (≈780 lines, no `sorry`, no axioms beyond `propext`/`Classical.choice`/`Quot.sound`), together with a companion analysis document `WITNESS_ELIMINATION_REPORT.md`, a new `RESULTS.md` section (§120), `Main.lean` axiom checks, and a regenerated `INDEX.md`.

The module formalises the *algebraic* mechanism attached to each close challenge — the witness polynomial and its behaviour along the line — rather than the combinatorics of agreement sets. Six results, all unconditional:

1. **Elimination of the challenge** (`card_le_natDegree_of_yfree_combination`). Working in `F[Z][X][Y]` with the substitution `Z ↦ γ, Y ↦ p`, if a `Y`-free `R ∈ F[Z][X]` lies in the ideal generated by two trivariate polynomials that every close challenge's witness annihilates, then every `X`-coefficient of `R` vanishes on the whole challenge set, so `#G ≤ deg_Z(R.coeff j)`. No genericity, field-size or radius hypothesis, and no resultant machinery is needed.
2. **Incidence count along the line** (`card_mul_le_of_lineResidual`). For the line residual `Z ↦ W(Z, x, f₀x + Z·f₁x)`, if all residuals have degree `≤ d` and vanish identically at at most `n − e − s` positions, then `#G · s ≤ n · d`.
3. **Dichotomy form** (`card_le_or_lineSupport_large`): either `#G ≤ n·d`, or the polynomial vanishes along the line at all but `≤ e` positions — isolating exactly the degenerate branch.
4. **Polynomial witness families over a far centre** (`card_le_of_polynomial_witness_family` and corollaries for `goodZ`, `badSet`, and finitely many families). If the centre is farther than `e` from the code, at most `n · max(deg_Z P, 1)` challenges can be witnessed by one polynomial family `P(γ,·)`; only the constant `Z`-coefficient needs degree `< k`.
5. **Scaled (rational) witness families** (`card_le_of_scaled_polynomial_witness_family`, `card_goodZ_le_of_scaled_witness_family`). The witness shape that a `Y`-degree-one factor actually produces, `p_γ = a(γ)⁻¹·B(γ,·)`; the far centre pays at the *trailing* coefficient of `a`, giving `#goodZ ≤ deg a + n·max(deg_Z B, deg a + 1)`.

## Honest assessment of the quantitative target

**No new certified radius is claimed.** The certified far-centred frontier in the project is unchanged. The report states precisely why and what remains:

- The Guruswami–Sudan chain over `F[Z]` needs multiplicity `m ≥ 9` at rate `1/2` to pass `δ = 1/4`, and would then give `O(n²)` — well inside the `O(n^2.8966)` budget, so the arithmetic is not the obstruction.
- The obstruction is the degenerate branch (a common factor of the interpolation module). The `Y`-degree-one case is now settled analytically: pseudo-division plus primitivity forces the factor's leading coefficient to be free of `X`, and the scaled-family theorem then bounds the challenge set. What is still open is an irreducible common factor of `Y`-degree `≥ 2`, plus the purely algebraic factorisation bookkeeping.
- A dimension count (recorded as analysis, not as a Lean theorem) shows a common factor of *large* `Y`-degree is impossible, so the open branch is confined to small `Y`-degree.

The report also records a correction that saves future effort: the support-counting idea is **vacuous** when applied to a Guruswami–Sudan interpolant itself, because interpolating the line points makes every line residual vanish; it is usable only on a proper factor or on a witness family. It further lists the approaches ruled out with reasons (higher moments, counting affine witness-pair clusters — which caps at `δ < 0.1464`, dimension counting for small `Y`-degree, and bounds depending on `√|F|`, which are useless in the intended soundness regime).

The Properties table has been updated with the six new theorems (all `proved`) and the three definitions they are stated in terms of.


# Summary of changes for run a144a9c0-641e-4de7-97a1-6dd295a7fe93
## What I did

I attacked the remaining frontier — the set of *close challenges on a Reed–Solomon line whose two words are both far from the code* — and obtained a new, machine-checked theorem that settles it in a strictly larger radius regime than anything previously certified in this project. Everything below builds (`lake build`, 8291 jobs, no errors), contains no `sorry`, and depends only on `propext`, `Classical.choice`, `Quot.sound`. All new results are wired into `RequestProject/Main.lean` with `#print axioms` checks.

## New files

* `RequestProject/Root/CodingTheory/TripleEnergy.lean` — a purely combinatorial engine: for a family of subsets `A γ` of an `n`-point universe, the identities `∑ₓ mult(x)² = ∑_{γ₁γ₂}|A_{γ₁}∩A_{γ₂}|`, `∑ₓ mult(x)³ = ∑_{γ₁γ₂γ₃}|A_{γ₁}∩A_{γ₂}∩A_{γ₃}|`, and the resulting cardinality bounds (`card_mul_pow_two_le`, `card_mul_pow_three_le`). The triple version constrains only *triples* yet bounds the size of the whole family — the global invariant that pairwise methods could not supply.
* `RequestProject/Root/CodingTheory/TripleClusterProximity.lean` — the Reed–Solomon layer.

## Main theorem

With `n = |D|`, `ρ = k/n`, `δ = e/n`, and `HasCorrelatedAgreement` = "two codewords of degree `< k` agree with `f₀` and `f₁` on one and the same window of at least `n − e` positions":

* `card_goodZ_mul_pow_three_le`: for **every** line, if there is no correlated agreement at radius `e`, then `N·(n−e)³ ≤ N·(k−1)·n² + (e+2)·n³`, where `N` is the number of `e`-close challenges.
* `card_goodZ_le_of_gap`: hence `N·c ≤ (e+2)·n` whenever `(k−1)n² + c·n² ≤ (n−e)³`.
* `card_badSet_le_of_far_of_gap`, `epsMCA_le_of_far_of_gap`: for a **far centre** (`e < d(f₀,C)`) correlated agreement is impossible, and by the existing exact reduction the MCA bad set equals the close set, so `#Bad·c ≤ (e+2)n` and `ε_mca ≤ (e+2)n/(c|F|)` — **with no hypothesis whatsoever on the direction `f₁`**, i.e. exactly the far–far case.
* `card_badSet_le_of_far_of_rate_radius`: fully explicit constant-gap form — at rate `k ≤ 3n/10` and radius `e ≤ 3n/10`, `#Bad ≤ 25(e+2) = O(n)`.
* `card_goodZ_pair_dichotomy` / `card_badSet_le_of_far_of_pair_gap`: a second-moment companion giving the sharper `N ≤ max(e+1, n/c)` in the smaller regime `(n−e)² > (k+e−1)n`.

The certified radius is `δ < 1 − ρ^{1/3}`. `gap_of_three_mul_lt` proves this regime strictly contains the previous unique-decoding regime `3e < n−k+1`, and it also contains the pair-split ceiling `(3−√(5+4ρ))/2`; at rate `1/4` the certified radius moves from `0.25`/`0.275` to `≈0.370`. `regime_example_1000_251_300` certifies a concrete parameter point inside the new regime and outside the old one. It is still below the Johnson radius `1 − √ρ`.

## Why it escapes the earlier ceilings

Not a pairwise argument. (i) A *triple* of close challenges whose agreement sets meet in `≥ k` positions forces the **polynomial identity** `p₃ = q₀ + γ₃·q₁` (a degree-`<k` polynomial with `k` roots vanishes) — a global conclusion from a local hypothesis. (ii) `e+2` challenges sharing one affine pair force correlated agreement on a **full** `n − e` window, because the sets `A_γ \ T` are pairwise disjoint — the classical `2e` loss is amortised by the *number* of challenges rather than by the radius. (iii) So without correlated agreement, every pair has `≤ e+1` such partners and almost all triple intersections are `< k`; the third-moment energy inequality converts that into the bound on `N`.

## Consistency and scope

The superpolynomial subspace-pencil family lies exactly outside the new regime (its parameters need `ℓ < m`, the hypothesis needs `ℓ ≥ m`) — as it does outside the Johnson regime — so no known counterexample is contradicted. The far-centre hypothesis is necessary: when both words are codewords, all challenges are close while none is bad. The band `1 − ρ^{1/3} ≤ δ < 1 − ρ` remains open; the report explains why `w = 3` is the optimum for this moment method and what a step reaching `1 − √ρ` would have to do instead.

## Bookkeeping

`TRIPLE_CLUSTER_REPORT.md` (full write-up, including the open questions), `RESULTS.md` §119, regenerated `INDEX.md`, and six entries in the properties table. `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.

# Summary of changes for run 37b0f6a3-0098-4421-affe-31a5fbb5318e
Everything below is Lean-checked: the whole project builds (`lake build`, 8289 jobs, no errors), the four new files contain no `sorry`, and every new theorem depends only on `propext`, `Classical.choice`, `Quot.sound`. Full write-up in `CONSTANT_GAP_MCA_REPORT.md`; `RESULTS.md` §§116–118, `DISCREPANCIES.md` D114.2 and the regenerated `INDEX.md` record the results in the project's own bookkeeping.

**1. Corrected interpretation of the subspace pencil** (`RequestProject/Root/CodingTheory/SubspacePencilAudit.lean`). The existing Lean theorem is exactly (A): for each pair (d, M) *some* parameter point has relative gap η ≤ 1/M and #Bad > n^d. (B) is not justified, and is false for this family. Certified: `subspacePencil_superpoly_forces_gap` (beating n^d forces m − ℓ > d, i.e. η < p^(−d)); `subspacePencil_bound_le_pow_card` (the guarantee never exceeds n^(m−ℓ), so it is polynomial at every fixed η); `subspacePencil_vanishing_gap_linear_bound` (at ℓ = 1 the gap η ≤ p^(1−m) → 0 — the smallest the family reaches — while the guarantee is only p^(m−1) < n, so a vanishing gap alone does not make the family superpolynomial: the exponent is ℓ(m−ℓ)/m, not a function of η); `subspacePencil_gap_eq_pred_mul` (c = (p−1)(k−1), so the family's gap and its rate vanish together and the relative radius tends to 1 — nothing is said about constant-rate codes at a small gap). Two further caveats recorded: only the sparse grid n = p^m+1, k = p^(ℓ−1)+1, c = p^ℓ−p^(ℓ−1) is realised with no transfer to neighbouring parameters, and the field must exceed p^(2ℓ(m−ℓ)+ℓ), so the certified ε_MCA ≥ #Bad/|F| is below p^(−ℓ(m−ℓ)). The over-strong title/claims in `SUBSPACE_PENCIL_REPORT.md`, in `RESULTS.md` §114 and in the theorem's docstring are corrected in place; the refutation of the gap-layer law, which needs only (A), stands.

**2. Strongest new results.**
(a) *Exact reduction* (`FarCenterProximity.lean`): if the centre satisfies e < d(f₀, code) then the MCA bad set equals the set of challenges whose combination is e-close to the code (`badSet_eq_goodZ_of_far`); combined with the unconditional inclusion this gives `grandMCA_iff_proximityGap` — for every bound B, a uniform MCA bound and a uniform proximity gap for far-centred lines are the same statement, and a proximity gap for all lines implies MCA for all lines. The far-centre hypothesis is sharp (two codewords give goodZ = F, badSet = ∅). `SubspacePencilProximity.lean` shows the pencil's centre is far, so its counterexample is literally a proximity-gap counterexample (`exists_superpolynomial_goodZ_of_small_relative_gap`).
(b) *A non-pairwise bound* (`NearDirectionBadSet.lean`): for every line and every codeword q₁, #Bad ≤ d(f₁,q₁)·#{codewords within distance e + d(f₁,q₁) of the centre}. Each bad challenge is charged individually, so this escapes the project's pairwise/unique-decoding barrier; it generalises the previous one-point-direction result, and gives #Bad = 0 when the direction is a codeword. With the project's Johnson bound: #Bad·a ≤ 2·t·|D| whenever 2|D|(k−1) ≤ a² and a ≤ |D| − e − t.
(c) *Swap symmetry* (same file): a nonzero bad challenge of (f₀,f₁) inverts to one of (f₁,f₀), so the two bad sets differ by at most one element, yielding the near-centre twin #Bad ≤ 1 + d(f₀,q₀)·#{codewords within e + d(f₀,q₀) of f₁} and #Bad ≤ 1 when the centre is a codeword.

**3. Hypotheses.** (a) needs only `e < distToCode k f₀`; the inclusion needs nothing. (b), (c) need only that q₁ (resp. q₀) is a codeword of degree < k; the Johnson corollaries add 1 ≤ k ≤ |D|, e + t + a ≤ |D| and the Johnson inequality. The audit statements need 2 ≤ p, 1 ≤ ℓ ≤ m.

**4. Quantitative consequence.** Lower side: max #Bad ≥ p^(ℓ(m−ℓ)) on the pencil grid, never above n^(log_p(1/η)); the same numbers now hold for the number of close challenges; ε_MCA is not shown to be large by that family. Upper side: for a line with one word at distance t from the code, #Bad ≤ 1 + 2tn/a, hence O(n) for t = O(1), valid at every constant gap η > √ρ − ρ + τ with an arbitrarily far other word.

**5. Status of constant-gap Grand MCA.** Neither refuted nor proved — but relocated and pinned: it is now *equivalent* to the constant-gap proximity gap for Reed–Solomon lines, so it is exactly as hard as that open problem; and the class of lines for which it is known has been enlarged from one-point directions to "one of the two words near the code", up to the Johnson radius.

**6. Remaining bottleneck.** Lines with *both* words far from the code, where (by the reduction) #Bad is exactly the number of close challenges. The two available mechanisms are exhausted: the pairwise route is confined to unique decoding (existing result), and the new direction split cannot beat it either — `nearDirection_ceiling_le_nearFar_ceiling` certifies that its ceiling (3 − √(5+4√ρ))/2 is never above the existing pair-split ceiling (3 − √(5+4ρ))/2, because its Johnson step pays √ρ instead of ρ. What is missing is an invariant of the whole set of close challenges that sees the capacity gap.

**7. Best next theorem.** Bound the number of *distinct* witness codewords P_γ for a far-centred line (the fibres already have size ≤ |D|), by showing the pairs (P_γ − γQ, Q) sweep a linear system of dimension O(n/c) — i.e. that the interpolation ideal of the common agreement positions is generated in degree < k + c. A cheaper secondary target: replace d(f₁, code) in the new bound by the number of disagreement positions actually met by badness windows, which is the quantity the proof uses.


# Summary of changes for run 71edb640-6add-417a-9148-8cee7981a180
## What was added

Five new Lean modules, all building and free of `sorry` (axioms: `propext`, `Classical.choice`, `Quot.sound` only). The whole project builds; the new theorems are wired into `RequestProject/Main.lean` with `#print axioms` checks.

* `RequestProject/Root/CodingTheory/AdditivePolynomial.lean` — theory of additive (`p`-)polynomials: spans of dissociated lists, subspace polynomials, the structure theorem.
* `RequestProject/Root/CodingTheory/SubspaceFamily.lean` — the graph family of subspaces and its injectivity.
* `RequestProject/Root/CodingTheory/SubspacePencil.lean` — the new counterexample family.
* `RequestProject/Root/CodingTheory/IndicatorLineList.lean` — the indicator-line ↔ Reed–Solomon list sandwich.
* `RequestProject/Root/CodingTheory/DirectionListReduction.lean` — the same reduction for arbitrary directions, plus a barrier lemma.

Documentation: `SUBSPACE_PENCIL_REPORT.md` (full write-up), `RESULTS.md` §114–§115, `DISCREPANCIES.md` D114.1, regenerated `INDEX.md`, and an exact-arithmetic check `analysis/subspace_pencil_check.py`.

## The five requested points

**1. Strongest new result.** The *subspace pencil*. Over a field of characteristic `p`, take `U` an `F_p`-subspace of dimension `m`, `w ∉ U`, `D = U ∪ {w}` (so `n = p^m + 1`), `k = p^{ℓ−1}+1`, `e = n − p^ℓ − 1` — capacity gap `c = p^ℓ − p^{ℓ−1}` — and the line `f₀(x) = x^{p^ℓ}`, `f₁ = indicator of w`. For each `ℓ`-dimensional `V ≤ U` the challenge `−L_V(w)` (with `L_V` the subspace polynomial of `V`) is bad, with window `V ∪ {w}`. This gives `#Bad ≥ p^{ℓ(m−ℓ)}` (`isBad_subspacePencil`, `card_badSet_ge_twistLists`, `exists_subspacePencil`), and in asymptotic form (`exists_superpolynomial_badSet_of_small_relative_gap`): for every polynomial degree `d` and every `M`, over any large enough field there is a parameter point with relative gap `η = c/n ≤ 1/M` and `#Bad > n^d`.

The companion upper-bound result is `card_badSet_le_mul_card_rsList`: for **every** MCA line, with no hypotheses, `#Bad ≤ 1 + |D| · #{codewords of degree < k within distance 2e of the direction word f₁}`.

**2. Proof or refutation?** It favours **proof** of constant-gap Grand MCA. The family is superpolynomial at every vanishing gap but yields only `n^{O(1)}` at constant `η`, and that is structural, not a tuning artefact: the exponent is exactly `log_p(1/η)`. Two obstruction theorems show the mechanism cannot be pushed to constant gap.

**3. Quantitative consequence.** `max #Bad ≥ n^{Θ(log_p(1/η))}`, hence `ε_mca ≥ n^{Θ(log_p(1/η))}/|F|`. This **refutes the conjectured gap-layer law** `max #Bad ≍ poly(n) + exp(Θ(1/η))`: superpolynomial behaviour is not confined to the boundary layer `c = O(n/log n)` but occurs at every `η = o(1)`. No polynomial bound on `#Bad` can hold under any hypothesis weaker than `η = Ω(1)`. Constant-gap Grand MCA itself is untouched, and the transition is now pinned exactly at constant gap.

**4. Main remaining obstruction.** The same obstruction from two sides. *Constructions*: every counterexample family in the project has a one-point direction, and for those the bad set is sandwiched by Reed–Solomon list sizes at radius `e+1` (`card_badSet_indicator_le_card_rsList`, `image_rsList_sub_badSet_indicator`) — at constant gap that is the open RS list-size-below-capacity problem. The multi-point flat variant was worked out and also caps at `n^{O(1)}`: the count is a Gaussian binomial, and a constant gap forces the codimension to be `O(1)`. *Proofs*: the only general handle on an arbitrary line is the correlated pair, and `pairwise_route_within_unique_decoding` shows that any Johnson-type treatment of the radius-`2e` list already forces `k + 2e < |D|`, i.e. unique decoding.

**5. Single best next step.** Attack the *near* case of the Johnson dichotomy — the single binding constraint. Given that `f₁` agrees with a codeword `q₁` off a small set, bound the number of bad challenges without passing to pairs. `card_shiftFibre_le` already shows that all challenges sharing one codeword pair number at most `|D|`, so what is missing is exactly a bound on the number of distinct `q₀ = P_γ − γ·q₁`.

## On the suggested Hilbert-space/second-moment technique

It was tried in the one form the MCA algebra supports: attach to each bad challenge the indicator of its window and use the window-incidence energy `Σ_{γ,γ'} |S_γ ∩ S_{γ'}|`. Cauchy–Schwarz supplies the Bessel-type lower bound and the pairwise-difference polynomial supplies the off-diagonal upper bound, giving `#Bad < n(n−e)/((n−e)² − A·n)` with `A` the largest agreement of `f₁` with a codeword. This is the Corrádi/set-family-Johnson inequality the project already records, and optimising the resulting dichotomy gives a strictly worse radius than the existing near/far bound. The mechanism transfers, but yields no new information here; it is documented in `SUBSPACE_PENCIL_REPORT.md` §6 rather than pursued.


# Summary of changes for run 7a582721-062e-4431-b68b-b48927ac1975
## 1. Strongest new mathematical result

Write `n = |D|`, `κ = n − k`, and define the **capacity gap** `c = n − k − e = κ − e` (so the relative gap to capacity is `η = 1 − ρ − δ = c/n`). New machine-checked results (files `RequestProject/Root/CodingTheory/CapacityGapPencil.lean` and `CapacityGapCosets.lean`, no `sorry`, axioms `propext, Classical.choice, Quot.sound` only; whole project rebuilds, 0 errors):

* **Capacity-gap pencil (scalable counterexample).** If the evaluation domain contains `m` disjoint blocks of size `c` whose vanishing polynomials are binomials `∏_{x∈O_i}(X−x) = X^c − b_i`, and the `(s+1)`-subset sums of the `b_i` are distinct, then the *power line* `f₀(x) = x^{k+c}`, `f₁(x) = x^k` with `k = c·s` has at least `C(m, s+1) = C(n/c, k/c + 1)` bad challenges at radius `e = n − k − c` (`card_badSet_ge_blocks`). The bad challenge attached to a block set `I` is `−Σ_{i∈I} b_i`; the window is the union of those blocks, and the direction word `x^k` is provably not interpolable on it.
* **Unconditional instances.** At gap `1` on the dissociated domain `{1,2,4,…,2^{m−1}} ⊆ ZMod p` (`2^m < p`), and at **every** gap `c ≥ 1` on `D = ⋃_{i<m} 2^i·μ_c ⊆ ZMod p` with `c ∣ p−1`, `2^{cm} < p` — such primes exist by Dirichlet (`exists_capacityGap_counterexample`). Concretely `2^n ≤ n·#Bad` with `n = |D| = 2(k+1)`, `e = k+1`, and `ε_mca ≥ C(n,e)/|F|`.
* **Matching upper bound and exactness.** For every line and every radius below the capacity radius, `#Bad ≤ C(n, k+1)` (`card_badSet_le_choose_succ_dim`); at gap `1` this is `C(n,e)` and the power pencil attains it, so **the maximum of `#Bad` at capacity gap 1 is exactly `C(n, e)`** (`card_badSet_eq_choose_gapOne`). The project's window-free binomial bounds are therefore sharp, not crude.

Exhaustive exact-arithmetic cross-check (`analysis/capacity_gap_check.py`): for `c = 1, 2, 3` the scanned bad set equals the predicted set exactly in all seven tested parameter rows.

## 2. Direction

It **favours disproving** Grand MCA in its quantitative form.

## 3. Exact consequence for the target regime

The statement "`ε_mca ≤ poly(n)/|F|` for all `δ < 1 − ρ`" is false — already at `δ = 1 − ρ − 1/n`, where `#Bad ≥ 2^n/n`. More precisely, any true bound must satisfy `#Bad ≥ C(n/c, k/c+1) = exp(Ω(1/η))`, so no bound polynomial in `n` *and* `1/η` exists, and a `poly(n)` bound is possible only in the band `c = Ω(n/log n)`. Conversely nothing is contradicted in the Johnson regime, in unique decoding (there the construction only yields `k/c + 2` challenges, consistent with the known `e+1` and `≈|D|/(κ−2e+1)` behaviour), or at a *constant* gap `η` — the practically used parameter points, where the counterexample family gives only `O(1)` bad challenges. So the target proximity regime keeps a possible bound, but it must be stated with an explicit gap-to-capacity hypothesis.

## 4. Main remaining obstruction

Whether `#Bad` can be superpolynomial at a **constant** relative gap `η` (i.e. `c = Θ(n)`). Combinatorially it is not excluded (windows of distinct bad challenges need only pairwise meet in `≤ k` positions); the obstruction is algebraic: for `c ≥ 2` a window supports a bad challenge only if the two residual vectors of the line are proportional — `c − 1` conditions — and every binomial-block design must use blocks of size `> c/2`, which caps the block count at `≈ 2n/c`, making the exponent `n/c` intrinsic to this method. Independently, the Schubert count in the quotient picture (`dim L_Z = κ − c`, codimension `c−1` incidence) balances at the same `exp(Θ(1/η))`, suggesting the law `max #Bad ≍ poly(n) + exp(Θ(1/η))`.

## 5. Single best next step

Settle the constant-gap case by a second-moment construction: for random domain and random line over `F_q`, count the `(k+c)`-subsets whose `2 × c` residual matrix has rank 1 (heuristic `C(n,k+c)/q^{c−1}`, balancing against `#Bad ≤ q` at `#Bad ≈ C(n,k+c)^{1/c}`). Making this rigorous — or proving the matching upper bound `#Bad ≤ exp(O(n/c))` — closes the gap-layer law and decides the last open quantitative form of Grand MCA.

Documentation: `CAPACITY_GAP_REPORT.md` (full write-up), `RESULTS.md` §113, `DISCREPANCIES.md` D113.1, regenerated `INDEX.md`; new modules are imported and axiom-checked in `RequestProject/Main.lean`.

# Summary of changes for run e486688a-6584-4dce-a56a-092aef9135a9
## Mission executed: IRREGULAR CORE/FIBRE DECOMPOSITION

I did **not** work on the regular `Σ(c_i−1) ≤ 2κ−3` bound. I ran the requested phases and the answer is decisive. Full write-up in `IRREGULAR_CORE_FIBRE_REPORT.md`; new Lean in `RequestProject/Root/CodingTheory/FoldPencil.lean` and `CoreFibreCharging.lean` (both build clean, no `sorry`, axioms only `propext, Classical.choice, Quot.sound`; whole project builds, 0 errors).

**Outcome: D — all core/fibre versions killed**, but with a positive replacement: the surviving invariant is a **fold (quotient) of the domain**, not a core.

### 1. Strongest surviving statement (MACHINE-CHECKED)
**Fold pencil.** If `D` contains `t` disjoint blocks `E_i` of size `e` that are the fibres of a degree-`e` fold (`∏_{y∈E_p}(x−y) = u_q − u_p` for `x∈E_q`), put `W = ∏_{x∉E_a∪E_b}(X−x)`, `f₀ = W·1_{E_a}`, `f₁ = W·1_{E_b}`. Then every third block gives a bad challenge `γ_i = (u_a−u_i)/(u_b−u_i)` with window `D∖E_i` and witness `(u_a−u_i)·∏_{x∉E_a∪E_b∪E_i}(X−x)`, so `#Bad ≥ t − 2 ≈ |D|/e`. Valid **exactly** on `2e ≤ κ ≤ 3e−1`. Concrete instances proved: multiplicative model `h = X^e` on a union of `μ_e`-cosets; and unconditionally for `e = 1`, `k = |D|−2` (κ = 2 = 2e) **every** RS code has a line with `|D|−2` bad challenges, hence `ε_mca ≥ (|D|−2)/|F|`.

### 2. Status
Fold theorem, multiplicative instance, `e=1` instance, `ε_mca` bound, component cap, fibre cap: MACHINE-CHECKED. Counterexamples and statistics: EXACT-COMPUTED (exhaustive over the stated prime fields, cross-checked with an independent scanner). The §10 upper-bound conjecture: DERIVED only.

### 3. Smallest exact counterexamples
- "`#Bad ≤ e+1` inside unique decoding": **killed**, smallest `q=11, |D|=8, k=3, e=2` (κ=5), `#Bad=4`, four disjoint error sets tiling `D`.
- **H1** (large literal common core): killed — `⋂S_γ = ∅` there; in the scalable families the core stays `Θ(e)` while `#Bad = Θ(|D|/e)`.
- **H2** (robust core): killed — error sets are pairwise **disjoint** (max coordinate multiplicity 1), i.e. a Δ-system with *empty* core.
- **H3** (low-dimensional codeword container): killed — `dim span{p_γ} = #Bad − 1 = Θ(|D|/e)`.
- **H4** (fibres explained by an existing branch): vacuous — every fibre of `γ ↦ p_γ` is a singleton, so `#Bad ≤ Σ_ξ fibreCap(ξ)` degenerates.

### 4–5. Statistics
Tables in the report: common core `= e` while `#Bad = |D|/e − 1`; min pairwise window overlap `|D| − 2e` (highly irregular); `#distinct codewords = #Bad`, `span dim = affine dim = #Bad − 1`, all fibres singletons.

### 6. Degree-`d` pencil classification
Two families separated. (a) Twisting the common-window pencil (`f₀ = −h(x)1_Y`) is now fully classified: bad challenges = fibres of the twist, `#Bad ≤ e+1`, and with uniform fibres of size `d` only `⌊e/d⌋+1` — so **raising the twist degree strictly hurts**. (b) The fold pencil is a genuinely different construction acting on the *domain*; it is the one that scales. So CommonWindowPencil is *not* the degree-1 member of the useful family.

### 7. Quotient/grading relation
The fold pencil is literally a quotient phenomenon: bad challenges are in bijection with the sectors of `D ↠ D/μ_e`. But the descent does **not** land in the existing correlated-agreement branch — the witnesses live on different subsets and span a growing space.

### 8. VC / sunflower tools
Quantitatively useless here: the extremal family is already a Δ-system with empty core and only `|D|/e` members; any useful bound would have to be stronger than the conclusion. The effective restriction is the RS algebra, not combinatorial complexity.

### 9. Target-row consequence
`ε_mca^max ≥ (|D|/e − 2)/|F|` on the band; `≥ (|D|−2)/|F|` at `e=1, κ=2`. Any row quoting `#Bad ≤ e+1` **must** keep the hypothesis `3e < κ+1` — that threshold is now proved sharp. No prize-row improvement is claimed.

### 10. ONE next lemma
Prove or refute `#Bad ≤ max(e+1, |D|/(κ−2e+1))` in the unique-decoding regime `2e ≤ κ`. It is the matching upper bound: the fold pencil attains it exactly at `|D| = 8, 10, 12` with `e=2, κ=5`, the common-window pencil attains the other branch, and it is consistent with every exhaustive row computed.

Also updated: `RESULTS.md` (§112), `DISCREPANCIES.md` (D112.1), new exact-arithmetic scripts in `analysis/` with raw data in `analysis/corefibre_data/`. `ARISTOTLE_SUMMARY.md` was not modified.


# Summary of changes for run 236974a9-4bdd-4021-8f1f-f464c100c1ae
## What was done

I continued the free-challenge residual incidence mission, completed the outstanding exact searches, finished the report, and — because the mission's stop rule permits Lean once a scalable counterexample exists (outcome D) — turned the counterexample into machine-checked Lean.

### Main deliverable: `FREE_CHALLENGE_INCIDENCE_LOCUS_REPORT.md`
Answers all 17 requested items. Headline findings:

* **Canonical object.** In `V = F^D/C ≅ F^κ` an MCA line is a 2-plane with a marked point; `γ` is bad iff the line point lies in the image `L_Z` of an `e`-set. The locus is an intersection of special Schubert varieties in `Gr(2,κ)`, equivalently the rank-deficiency locus of a linear pencil `N(γ) = Σ γ_i B_i` with `Σ B_i = 0` (the affine gauge).
* **Why `c_i − 1`.** It is exactly the Schubert codimension of "a line meets a codim-`c_i` subspace"; the saved dimension is the free challenge itself. Uniform for unequal `c_i`.
* **The conjectured cap `Σ(c_i−1) ≤ 2κ−1` is FALSE**, by an exact, scalable family (the "common-window pencil"): split `D = T ⊔ Y` with `|Y| = e+1`; the line `u₁ = 1_Y`, `u₀ = −x·1_Y` has `e+1` bad challenges (the points of `Y`) with windows `T ∪ {y}` of size `n−e`, giving `E = Θ(n²)`, strictly inside unique decoding. Smallest instance `n=10, k=1, e=2` (`E = +1`).
* **Why earlier searches missed it:** all counterexamples are *irregular* (`|S_i ∩ S_j| = n−e−1 > k`), and a regular pair forces `κ ≤ 2e`, so the regular branch is empty inside unique decoding.
* **Strongest surviving statement:** on the regular branch `Σ(c_i−1) ≤ 2κ−3`, holding in 913/913 certified regular families (543 stored + 370 newly generated) and attained; the Schubert count `2κ−4` is exceeded, always by exactly `+1`, in 10 of them.
* **Status:** KILL for the conjectured cap; PROMISING for the regular version; prize cash-out shows the radius window, not the constant, is what matters.

### New exact computations (this session)
* `analysis/fcri_exhaust.py` — fixed its evaluation domains and ran 13 **fully exhaustive** sweeps over *every* MCA line (≈4.4·10⁶ lines with a bad challenge): for `κ ≤ 4` the cap is true and attained (`Σ = 2κ−1`), and `Σ_reg ≤ 2κ−4` throughout — explaining why small-scale searches always saw the cap survive.
* `analysis/fcri_frontier.py` campaign completed: 370 certified regular families, best margin `−2` against `2κ−1`.
* `analysis/fcri_lean_bridge_check.py` (new) — rebuilds the Lean instance over GF(q) and re-runs the faithful `IsBad` scan: 6/6 parameter sets reproduce exactly `#Bad = e+1`, all windows maximum-agreement of size `n−e`, `E = +1 … +37`, all with `2e < κ`.

### Lean (builds clean, no `sorry`, only the standard axioms)
`RequestProject/Root/CodingTheory/CommonWindowPencil.lean`, stated with the project's own MCA definitions:
* `isBad_commonWindow`, `card_le_card_badSet_commonWindow` — `e+1` simultaneously bad challenges on one line;
* `succ_div_card_le_epsMCAmax` — `ε_mca(C,e) ≥ (e+1)/|F|` whenever `k + e + 1 ≤ |D|`, strengthening the project's previous `1/|F|` lower bound;
* `free_challenge_cap_fails` — a formal refutation of the free-challenge cap (independent of window maximality, since enlarging windows only increases the sum);
* `card_le_two_mul_of_regular_windows` — a regular pair of windows forces `κ ≤ 2e`.

The file is imported by `RequestProject/Main.lean` and its axiom checks were added there; the whole project builds successfully.

### Next lemma recommended
Exactly one: the **regular charging lemma** in pencil form — for a regular family, `rank N(γ) < κ` implies `Σ(c_i−1) ≤ 2κ−3`. It is the only surviving form, and it is what the pair-cover composition is missing.

All work is committed.

# Summary of changes for run a66a89b0-463f-46e5-825d-0defdc78dc70
Falsification mission complete. No Lean was written (per the stop rule); everything below is exact finite-field measurement (integer arithmetic mod q), not proof. Full write-up: `CAP_VIOLATION_FALSIFICATION_REPORT.md`; tooling and data in `analysis/capviol_*.py`, `analysis/capviol_data/`.

**RESULT: the hypothesis is KILLED.** FULL-MCA + genuine plain-cap violation does NOT imply generalized grading / quotient structure.

1. **Instances tested** — 636 challenge-tuned window families over 115 (parameter row, prime) combinations, plus 305 exhaustively enumerated solution fibres at n=12, 847 randomly-challenged swept lines, 224 annealing runs, 1484 class-A perturbations, and an exact bad-set maximiser over 17 rows. Classes A–F all covered.
2. **Nongraded cap violations found: 495** strictly verified (Σc_i > 2κ−1, regular, FULL-MCA, maximal windows, no common factor, nonzero grading defect at every h|n), over 32 (n,k,e) rows and 56 (n,k,e,q) combinations — plus 14 more from an explicit construction.
3. **Smallest witness** — n=8, k=4, e=2, q=17, D=μ₈, m=4, Σc_i=8 > 7=2κ−1, rank M=7, all six window intersections = 4 = k, per-window grading defect 2 (maximum possible) at every h. Strictly inside Johnson and at the unique-decoding radius. Re-verified from scratch by the standalone `analysis/capviol_witness8.py`.
4. **Scalable: YES** — an explicit "quarter-pair" construction (random partition of D into four quarters, six windows = pairs of quarters, one tuned challenge) succeeded 14/14 at n = 8, 16, 32, 64, 128, 256, 512 on two primes each; random-window witnesses exist at 14 further sizes. Excess over the cap stays +1…+4; it does not grow with n.
5. **Strongest surviving grading certificate: NONE** — common-factor reduction, Graded(h) for all h|n, per-window A_i=G_i·B_i(X^h) with defects, character/quotient reformulations and the correlated-pair invariant all fail (the latter's apparent k+1 signal was shown to be the generic noise floor by a random-line control). What survives is (i) the corrected free-challenge cap Σ_i(c_i−1) ≤ 2κ−1, never violated by any witness nor by a maximiser run directly against it, and (ii) a new leave-one-out nondegeneracy dichotomy that explains the systematic, field-size-independent rank defects that had been masking the real witnesses.
6. **Exact quotient decomposition: TRUE** — P = ⊕ X^r P_r, R_i = ⊕ X^r R_{i,r}, M ≅ ⊕ M_r, rank M = Σ_r rank M_r, derived symbolically via the fibrewise h-point DFT.
7. **Exact Bad-set descent: PARTIAL** — the correct statement is an intersection with matched windows, Bad_H(D) = ⋂_r Bad_r(D/H), giving #Bad ≤ min_r #Bad_r; the previously recorded union form is true only for FULL-MCA indices. Gaps: sectors with c_r = 0, sector regularity can lose 1, and different challenges may be FULL-MCA in different sectors.
8. **Parameter transformation D → D/H** — n→n/h, e→e/h (forces h|e), c→c_r=⌈(c−r)/h⌉, κ→κ_r=c_r+e/h, k→k_r=n/h−κ_r; δ preserved exactly, ρ up to O(h/n); **challenges unchanged**. Edge cases (h∤k, h∤κ, c<h, defect windows) are tabulated.
9. **Recurrence** — B(n,k,e) ≤ max{(2κ−1)/(c−1), min_{h|n} min_r B(n/h, k_r, e/h)}, telescoping to #Bad ≤ (2κ−1)/(c−1) + O(log n); crudest union-bound form M(n) ≤ h·M(n/h) + (2κ−1)/(c−1).
10. **α** — 0 (constant at fixed rates, plus O(log n)) for the min/intersection descent; 1 for the crudest union bound.
11. **Prize-sufficient: YES on the counting side**, with ≈2^37.9 of margin against the 2^57.93 budget at n=2^20, k=2^19 (the descent could lose h^2.8966 ≈ 7.44 per halving and still fit) — but with the caveat that the recursion no longer has complete coverage, since the nongraded branch is now known to exist.
12. **DECISION: SWITCH TO ALGEBRAIC RESIDUAL LOCUS.** The cap-violation structure theorem is false; the quotient theorem is true but only covers the graded branch; the mechanism that actually explains every measurement is determinantal — the plain cap counts equations against unknowns with the challenges frozen, while the challenges are free.
13. **One next big lemma** — *free-challenge residual cap*: for distinct challenges with maximal windows S_i, c_i = |S_i|−k ≥ 1 and FULL-MCA, Σ_i(c_i−1) ≤ 2κ−1; equivalently the singular locus of the stacked residual system has codimension Σc_i−2κ+1 in challenge space and is empty unless that is at most m.

Also appended a short, clearly marked addendum to `GRADING_COMPLETENESS_REPORT.md` recording that its "every cap violation is graded" claim is refuted and correcting its union-vs-intersection descent statement; the rest of that file is untouched, as is `ARISTOTLE_SUMMARY.md`. All work is committed.

# Summary of changes for run 4fcacfe0-face-43c4-967b-3482b50934f1
Per the mission instruction ("do not write Lean yet"), this turn produced no Lean; it is an exact-arithmetic investigation, written up in `GRADING_COMPLETENESS_REPORT.md`, with all scripts and raw data in `analysis/grading_*.py` and `analysis/grading_data/*.jsonl`. All computations are exact integer arithmetic modulo a prime (cross-checked on q = 12289 and q = 40961); they are numerical measurements, not machine-checked proofs.

**EXACT GRADING CONDITION:** since 0 ∉ D, Graded(h) ⟺ supp(A_i) ⊆ hℤ ⟺ A_i ∈ F[X^h] ⟺ each Z_i = D∖S_i is a union of μ_h-cosets. Two strictly weaker conditions also suffice and do occur: (F) reduce by the common factor G = gcd_i A_i, then apply Graded(h); (G′) per-window factorisation A_i = G_i·B_i(X^h), d_i = deg G_i = |Z_i| − |largest μ_h-closed subset of Z_i|.

**SECTOR DECOMPOSITION FORMULA:** P = ⊕_{r<h} X^r F[X^h]_{<κ_r}, R_i = ⊕_r X^r B_i F[X^h]_{<c_r}, M ≃ ⊕_r M_r, rank M = Σ_r rank M_r with rank M_r = min(m c_r, 2 dim W_r − ε_r), ε_r = 1 iff some challenge is bad in sector r. Verified exactly on every graded instance, including the three published counterexamples.

**RANK-DEFICIENT INSTANCES TESTED:** 43,278 measured instances (n = 32 exhaustive, n = 32/48/64 interior) plus ≈600 targeted at n = 64,128; 208 are FULL-MCA realisable, regular and have Δ* > 0; 98 of those violate the plain cap.

**GRADED:** ~60 % naively graded, ~20 % graded after common-factor reduction, ~15 % via per-window factors. All 98 cap violations carry a nontrivial certificate (h ∈ {2,3,4}); of the 48 with stored windows, 47 are numerically exact.

**NONGRADED:** they exist, at saturated regularity max|S_i∩S_j| = k, just inside Johnson (ρ ≈ 0.22, δ ≈ 0.53); no certificate, no common factor, no index-partition explanation, stable across challenge draws and both primes.

**SMALLEST NONGRADED DEFECT:** n = 32, k = 7, e = 17, c = 8, m = 6: mc = 48, 2κ = 50, rank M = 47, Δ = Δ* = 1.

**SCALABLE NONGRADED DEFECT: YES** — Δ = 1, 4, 6…11 at n = 32, 64, 128 in the same rate/radius band.

**WEAKEST GRADING CERTIFICATE:** Graded(h; d_1..d_m) with A_i = G_i·B_i(X^h), giving rank M ≤ CERT(h) = Σ_{r<h} min(Σ_i #{j < c+d_i : j ≡ r mod h}, 2κ_r), minimised over h | n and also applied to the common-factor-reduced system. On the 112 hits with stored windows: exact in 95, off by 1 (the FULL-MCA correction) in 16, off by 4 in one. The more general "nontrivial idempotent in the preserver algebra E" test was measured and is too weak to be useful, though it does recover the true even/odd split on the h = 2 counterexample.

**QUOTIENT DESCENT: EXACT** — sector r of a Graded(h) family is literally the residual system on D/H with (n/h, n/h − κ_r, e/h) and the same challenges; identical rank, dim K and bad-sets verified at n = 32,64,128 and h = 2,4.

**BAD PRESERVED UNDER QUOTIENT: YES** — Bad(D) = ⋃_r Bad_r(D/H); bad challenges spread over 2–14 sectors in 257 measured graded families.

**PREDICTED RECURSIVE #BAD SCALE:** m ≤ max_{h|n, r<h} ⌊(2κ_r − 1)/c_r⌋ (never violated in 257/257 graded families nor in any of the 208 hits; excess over the plain cap ≤ +1, pure rounding). Residual layer O(1), total #Bad = O(n). No configuration approached exponent 2.89.

**EXISTING PROJECT OBJECT COVERING NONGRADED DEFECTS:** partially — they sit exactly one point below the correlated-pair threshold k+1, i.e. the boundary layer of the existing pair-cover object (WB/subresultant unavailable there, annihilator span full, no common codeword pair).

**DECISION: PROVE GRADING-OR-ALGEBRAIC DICHOTOMY** (and KILL the rank route). Grading-completeness for the *rank defect* is killed by scalable nongraded counterexamples; the *cap* survives every observed instance, and every observed cap violation is graded.

**NEXT SINGLE BIG LEMMA:** (a) FULL MCA ⇒ R_i ⊄ K for all i ⇒ dim K ≤ κ−1 ⇒ rank M ≤ 2κ−1; (b) the generalised graded bound rank M ≤ Σ_r min(Σ_i #{j < c+d_i : j ≡ r mod h}, 2κ_r) with (a) applied sector-wise; (c) sector r of Graded(h) = residual system on D/H, Bad(D) = ⋃_r Bad_r.

Work is committed; the existing Properties table and `ARISTOTLE_SUMMARY.md` were left untouched.

# Summary of changes for run 4eaa991f-bb1d-41c8-a423-c7c661fd25c0
Falsify-first investigation of the regular rank cap. No Lean was written (as instructed); everything below comes from exact integer-arithmetic computations, and the full write-up is in `REGULAR_RANK_CAP_KILL_REPORT.md`, reproducible with `analysis/smooth_rank_cap_{kill,search,witness,probe,structure}.py` (witness output in `analysis/smooth_rank_cap_witness_output.txt`). A cross-reference was appended to `NONJOHNSON_INTERIOR_MEASUREMENT.md`, whose §4 / "next lemma" this refutes. These are exact-arithmetic findings, not machine-checked theorems.

EXACT STACKED MATRIX: M ∈ F^{mc×2n}, rows (i,t), i ≤ m, t < c := n−e−k, columns split into an f₀- and an f₁-block: M[(i,t),(0,x)] = 1_{x∈S_i}·w^{S_i}_x·x^t, M[(i,t),(1,x)] = γ_i·1_{x∈S_i}·w^{S_i}_x·x^t, with w^S_x = (∏_{y∈S,y≠x}(x−y))⁻¹; M·(f₀,f₁)ᵀ = 0. Dual form: Row(M) = Σ_i {(g,γ_i g) : g ∈ A_i·F[x]_{<c}} ⊆ (F[x]_{<n−k})², A_i = ∏_{z∈D∖S_i}(x−z).

REQUIRED RANK: rank M = m(n−e−k) (full row rank). ker M ⊇ C×C gives rank M ≤ 2(n−k) always; FULL MCA forces ker M ⊋ C×C, so the corrected consequence is m(n−e−k) ≤ 2(n−k) − 1.

MCA-SPECIFIC HYPOTHESES: σ_{S_i}(f₁) ≠ 0 for every i (the ¬LineCloseOn clause of IsBad) — decisive; plus σ_{S_i}(f₀+γ_i f₁)=0 with |S_i| ≥ n−e, distinct γ_i, f₁ not a codeword. NOT from MCA: regularity |S_i∩S_j| ≤ k, and above all the independence hypothesis itself.

RELATION TO MDS(m): SAME AS HIGHER-ORDER MDS, in twisted/doubled form (the V_i = {(g,γ_i g) : g ∈ R_i} must have generic minimal intersection in C^⊥⊕C^⊥); strictly weaker than plain MDS(m) for the R_i; independent of MCA — hence not MCA-specific, and it fails on structured domains.

SMOOTH COUNTEREXAMPLE FOUND: YES. D = multiplicative subgroup of order 32 in F_12289, k=15, e=10, c=7, five negation-closed windows: m·c = 35 > 34 = 2(n−k), rank M = 33; all five challenges brute-force certified bad, no window carries a correlated pair, pairwise |S_i∩S_j| ≤ k−1, strictly above unique decoding (2e−(n−k)=3) and strictly below Johnson ((n−e)²−nk = +4). Also n=64: (k,e,h,m)=(29,20,4,5) with 75 > 70 and (30,20,4,5) with 70 > 68. Mechanism: when window complements are unions of cosets of a subgroup H, the syndrome space splits into |H| sectors and rank M = Σ_r min(m c_r, 2κ_r), which can fall below both m·c and 2(n−k). Pure coset windows (h=e) are even more deficient but are killed by FULL MCA (proved by hand and measured: every kernel element has σ_{S_i}(f₁)=0).

SCALABLE: YES for the falsification (violating instances at fixed rate/radius for n = 32…4096), NO for growth — the excess over ⌊2(n−k)/c⌋ was exactly +1 everywhere, and the mechanism is blocked when the symmetry order divides n−k and c.

RANK FAILURE ⇒ EXISTING STRUCTURE: NO. WB pencil unavailable past the forcing barrier (k+2e+1 > n); no common codeword pair (all induced |T| = 12,14 < k = 15, ten distinct pairs from ten challenge pairs); span{A_i} full; no codewordLocus/gcd degeneracy. Detected only by a new object: the H-grading of the windows.

RESULTING m CAP AT 1/4: 4. RESULTING m CAP AT SAFE JOHNSON: 4. (At n=2²⁰, k=2¹⁹ the sector-corrected cap, maximised over all window sizes and all symmetry orders, equals the plain cap.)

RESULTING #BAD SCALE: ≤ 4n + 4 = O(n), conditional on O(1) explaining pairs; unconditionally still n·Λ(k,k+1)² + O(n).

DECISION: KILL the rank-cap route as stated → PROVE DICHOTOMY (graded form).

NEXT SINGLE LEMMA: with R_i the shortened dual of S_i, N = {(h_i) : Σ A_i h_i = 0, deg h_i < c} and K = {Σ γ_i A_i h_i : (h_i) ∈ N}: if the γ_i are distinct bad challenges with witness windows S_i and the line satisfies FULL MCA, then R_i ⊄ K for every i, hence rank M ≤ 2(n−k) − 1; and if the twisted family {(g,γ_i g) : g ∈ R_i} is in direct sum, m(n−e−k) ≤ 2(n−k) − 1. Then the unconditional H-grading lemma rank M = Σ_{r<h} rank M_r, which is the counterexample generator and shows the direct-sum hypothesis cannot be dropped.

# Summary of changes for run bbfba5dc-13cd-42af-8e48-19d0de6885d4
Measurement round completed on genuine UD–Johnson **interior** instances (no Lean sources changed, no new theorem proved, as instructed). Two documents and four exact-arithmetic probes were added and committed:

- `MCA_RESEARCH_KERNEL.md` — the 34-entry reusable spine of the coding-theory layer (Lean names verified against the sources), a dependency DAG, and the freeze/kill list.
- `NONJOHNSON_INTERIOR_MEASUREMENT.md` — full data tables for this round.
- `analysis/nonjohnson_composition_scan.py` (brute-force reference), `analysis/nonjohnson_syndrome_scan.py` (fast syndrome-parallelism form, cross-validated against the brute force), `analysis/nonjohnson_interior_pairs.py`, `analysis/nonjohnson_rank_cap.py`, `analysis/nonjohnson_pair_budget.py`.

Correction accepted: the earlier rows (8,4,2), (12,6,3), (16,8,4), (9,3,3) sit on 2e = n−k and (9,3,4) is above Johnson; they are excluded, and no universal "#Bad grows like q immediately above Johnson" claim is made — those were lower-bound families at specific small parameters only.

```
TRUE UD–JOHNSON INSTANCES TESTED (2e ≥ n−k+2 and δ < 1−√ρ):
  (16,4,7) ρ=1/4 δ=0.4375 | (18,6,7) ρ=1/3 δ=0.3889 | (20,5,9) ρ=1/4 δ=0.45
  (24,12,7) δ=0.29167 | (28,14,8) δ=0.2857 | (32,16,9) δ=0.28125
  (64,32,17) δ=0.2656 | (64,32,18) δ=0.28125     (all ρ=1/2 on the last five)
  fields q ∈ {101, 1009, 10007, 2^31−1}; full window enumeration where C(n,e) ≤ 3.5·10^5,
  verified constructions (per-challenge syndrome check) for n = 28, 32, 64.

MAX #BAD: exact scans 8, 8, 10, 8. Verified constructions attain exactly e+1 on every
  interior row (10 at n=32; 18 and 19 at n=64); best multi-pair design e+2 (=9 at (24,12,7)).
  Nothing exceeded n; #Bad/n² ≤ 0.031 everywhere. Random interior lines are usually bad-free.

DISTINCT PAIRS P: ≤ 6 (at (20,5,9) and (24,12,7)); constructions realise P = 1–2.

MAX FIBRE F: e+1, attained by a single pair with |T| = n−e−1 (8/8/10/8/9/10/18/19).
  Measured fibres obey F ≤ ⌊(n−|T|)/(n−e−|T|)⌋; at |T| = k this is ⌊(n−k)/c⌋ = 2 at rate 1/2.

P·F: ≤ 12 measured. Design budget Σ_i [2(|T_i|−k) + F_i(n−e−|T_i|)] ≤ 2(n−k) caps it at Θ(e)=Θ(n).

COUNT WITH |T|=k: 1, 1, 4, 6 on the four fully scanned rows.
COUNT WITH |T|>k: 1, 3, 2, 1 on the same rows.

COMMON ALGEBRAIC PROPERTY OF T=k PAIRS: they are the plain interpolation pairs (determined by
  (f₀,f₁)|T, no certificate beyond interpolation). Their bad challenges are exactly the values
  attained ≥ c = n−e−k times by the spurious-value map γ_x = −u₀(x)/u₁(x) off T, i.e. the
  parameters where the Welch–Berlekamp pencil u₀+γu₁ (u_i = f_i−q_i) picks up c extra roots in D
  — a gcd/subresultant degeneracy of an existing project object (WelchBerlekampPencil,
  GcdPencilEscape, SubresultantCore). Their stacked syndrome conditions were measured to be
  independent (rank = min(m·c, 2(n−k)) in 100% of trials), so at most ⌊2(n−k)/c⌋ coexist.

SCALABLE HIGH-PAIR-COUNT EXAMPLE: NO. Random search, planted-window linear solving, core
  designs and multi-core designs never exceeded ⌊2(n−k)/c⌋ = 4 regular challenges or e+2 total,
  on any row from n=16 to n=64, at any field size. 2(n−k)/c = 2(1−ρ)/(1−δ−ρ) is constant in n
  (4.27–5.00 on the rows tested), and the set-family Johnson bound independently caps families
  of (n−e)-windows with pairwise meets ≤ k−1 exactly when δ < 1−√ρ.

CAN EXISTING PROJECT LEMMAS BOUND P·F < n^2.89: UNKNOWN, with one small gap.
  `MCAPairCover.card_badSet_le_pairCover` already *is* the composition, with free threshold τ:
      #Bad ≤ n·Λ(k,τ)² + n(n−e)/((n−e)² − n(τ−1)),  valid when n(τ−1) < (n−e)².
  At τ = k+1 the side condition is precisely δ < 1−√ρ (the interior) and the residual term is
  O(n) — already proved. `AffineFactorSplit.card_badPairSet_le` already gives F ≤ n. The only
  non-polynomial factor left is Λ(k,k+1), the list size below the Johnson agreement threshold
  √(nk); the measurement replaces it by the count of pairs that actually explain a bad
  challenge, which is ≤ 6 measured and O(1) by the rank budget.

NEXT SINGLE LEMMA (regular-residual rank cap, the |T| = k layer):
  Let γ₁,…,γ_m be distinct bad challenges whose maximal witness windows S₁,…,S_m (|S_i| = n−e)
  pairwise meet in at most k positions (no over-determined codeword pair). Then the stacked
  syndrome conditions σ_{S_i}(f₀) + γ_i σ_{S_i}(f₁) = 0 are independent modulo codeword pairs,
  hence   m·(n−e−k) ≤ 2(n−k),   i.e.  m ≤ ⌊2(1−ρ)/(1−δ−ρ)⌋ = O(1).
  Together with card_badPairSet_le (F ≤ n) and SetFamilyJohnson.card_family_le_of_pairwise_inter
  (available exactly on δ < 1−√ρ) this turns card_badSet_le_pairCover into
      #Bad ≤ (#explaining pairs)·n + O(1),
  removing the list-size factor from the residual layer.
```

All findings above are exact-arithmetic measurements (per-challenge verified), not proofs; they are recorded as evidence in the two markdown reports.


# Summary of changes for run b70ee42a-92e7-4510-8025-ddf3982a3785
## TWO-SYNDROME GATE — result

**TWO NATURAL CHANNELS: YES** (exactly two, provably never more).

**SOURCE:** the RS syndrome map applied to the line `f₀ + γ·f₁` of the existing MCA layer. New machine-checked facts: `channel_affine_combination` (the channel of any challenge is the explicit affine combination `((z₂−z)/(z₂−z₁))·S^{(z₁)} + ((z−z₁)/(z₂−z₁))·S^{(z₂)}`) and `channelSpan_eq_span_pair` (`span{ H(f₀+z f₁) : z } = span{H f₀, H f₁}`). So the whole family of MCA channels *is* the interleaved pair `(f₀,f₁)`: `s = 2` is available and maximal, and a third bad challenge is exactly redundant.

**EXACT FORMULAS:** with dual multipliers `λ_x = ∏_{y≠x}(x−y)⁻¹`, `r = 0…n−k−1`, and the normal form `a = f₀−q₀`, `b = f₁−q₁`:
`S⁽¹⁾_r = ∑_{x∈E} a(x)λ_x xʳ`, `S⁽²⁾_r = ∑_{x∈E} b(x)λ_x xʳ`, `S^{(γ)} = S⁽¹⁾ + γS⁽²⁾`, `E_γ = {x∈E : a(x)+γb(x) ≠ 0}`, `E = E₁ ∪ E₂`.

**COMMON SUPPORT: REDUCIBLE ONLY TO THE UNION — never `E₁ = E₂`.** `badWitness_ne`: two distinct bad challenges can never share a witness set (one line from the project's small-union rigidity). `eq_zero_of_two_cancellations` + `channelSupport_ne_of_cancels`: badness is a cancellation event, cancellation sets of distinct challenges are disjoint, so the two supports always differ and can be disjoint; `jointSupport_eq_union`: only `E₁ ∪ E₂` (size up to `2e`) is common — the radius already delivered for free by the existing two-point result. `exists_correlatedPair_of_commonSupport`: a genuine shared support already yields a correlated pair by inverting a 2×2 system, so the success branch is circular.

**STACKING ADDS RANK: YES, but on the wrong object.** Budget (`twoChannelBudget_iff`): `m+1 ≤ 2(n−k−m) ⟺ 3m+1 ≤ 2(n−k)`. With `m = 2e` at rate 1/2 this forces `6e < n`, i.e. `δ < 1/6` (`twoChannel_rate_half_threshold`) — below the `δ = 1/4` baseline. The pre-screen compared `e` with `⅔(n−k)`; the correct comparison is `2e`. At both schedules the stacked system is **empty**: defect-2 `2e = 524290 > n−k = 524288`; safe Johnson `2e = 612192 > 524288` (`defectTwo_stacked_system_empty`, `safeJohnson_stacked_system_empty`).

**PI SUCCESS RATE IN EXACT TESTS:** 3 364 267 genuine bad-challenge pairs from FULL-MCA instances (exhaustive over all word pairs for GF(3),|D|=3 and GF(5),|D|=4; 4000 random pairs per parameter set for GF(7),GF(11),GF(13); closeness/badness by full enumeration of all degree-<k polynomials). `E₁ = E₂`: **0**; disjoint supports: 1 940 608; channel span equal to `span{Hf₀,Hf₁}`: 3 364 267/3 364 267; empty stacked system: 96.8 %; among the 107 010 nonempty ones stacking adds rank 106 977 and PI succeeds **97 201/107 010 ≈ 90.8 %** (≈ exactly the budget-satisfying pairs).

**PI FAILURE CERTIFICATE:** stacked block-Hankel rank deficiency `rank(H⁽¹⁾;H⁽²⁾) = m−1`, `dim ker = 2` (all maximal `m×m` minors vanish) with error-value rank still 2 — confirming that global row rank is not the certificate. Witness: GF(13), n=7, k=1, e=3, `f₀=(7,9,11,7,10,7,6)`, `f₁=(11,4,8,11,4,11,6)`, γ∈{4,5}.

**PI FAILURE + UNSTRUCTURED FOUND: NO** (6 in-budget failures, all from one word pair at δ≈0.43; not decisive, the route dies earlier).

**SMALLEST EXACT COUNTEREXAMPLE (formalised):** GF(3), n=3, k=1, e=1, `f₀=(0,0,1)`, `f₁=(0,1,0)`: challenges 0 and 1 are both bad (`isBad_zero`, `isBad_one`) with **disjoint** channel supports `{2}`, `{0}`, union `2 = 2e = n−k`, hence zero rows per channel.

**DECISION: KILL.** (1) `E₁ = E₂` is impossible; (2) the union costs a factor 2 in radius and the s=2 budget then caps the route at `δ < 1/6`, with zero equations at both project schedules; (3) the success branch is circular; (4) no third channel exists, so raising `s` cannot repair it. Per the mission's kill instruction, the programme returns to `GapBound`.

**NEXT SINGLE LEMMA:** not the simultaneous-locator lemma. The kill isolates channel-support *overlap* as the real quantity: `|E₁ ∩ E₂|` is empty in 58 % of observed pairs, so the only surviving question is the conditional one — under the existing explaining-pair hypothesis, is `|E₁ ∩ E₂|` forced to be large, or does small overlap already produce a structure certificate? That is a statement about the existing structure branch, not about interleaved decoding.

### Deliverables
- New sorry-free Lean module `RequestProject/Root/CodingTheory/TwoSyndromeGate.lean` (25 declarations), imported and axiom-audited in `RequestProject/Main.lean`; the whole project builds and every new declaration depends only on `propext, Classical.choice, Quot.sound`. No axioms added, no existing declaration modified.
- Exact probes `analysis/two_syndrome_gate_probe.py`, `analysis/two_syndrome_gate_pi_failures.py` with their output files.
- Report `TWO_SYNDROME_GATE_REPORT.md` and `RESULTS.md` §111.


# Summary of changes for run a67548e5-32ff-4f48-9944-aed611219294
## What I did

I attacked the defect-2 kernel question head-on and **settled it, sharply**, in machine-checked Lean. New sorry-free module `RequestProject/Root/CodingTheory/HankelLocatorKernel.lean` (imported and axiom-audited in `RequestProject/Main.lean`; whole project builds, axioms only `propext`, `Classical.choice`, `Quot.sound`). Report: `DEFECT2_KERNEL_REPORT.md`; `RESULTS.md` §110; exact GF(p) probe `analysis/hankel_kernel_defect_probe.py` (+ output file).

Setting: `S r = ∑_{x∈E} a_x x^r` with `a_x ≠ 0`, Hankel matrix `H i j = S(i+j)` of size `rows × cols`, kernel vectors read as polynomials of degree `< cols`, locator `Λ_E = ∏_{x∈E}(X−x)`. In the MCA pencil: `rows = n−k−e`, `cols = e+1`, `d = 2e−(n−k)`.

## Required report block

- **VANDERMONDE LOCATOR LEMMA: PROVED** (`eval_eq_zero_of_hankelRel`, `supportLocator_dvd_of_hankelRel`) — `rows ≥ |E|` forces `Λ(x) = 0` on all of `E`, hence `Λ_E ∣ Λ`.
- **AVAILABLE RECURRENCE EQUATIONS:** `m = rows = n−k−e = e−d`; at `(n,k,e) = (2²⁰, 2¹⁹, 262145)` that is `262143 = e−2` (`defect_two_schedule`), confirmed from the pencil's dimensions.
- **AUTOMATIC SUPPORT RANGE:** `|E| ≤ 262143 = e−2`. **BOUNDARY SUPPORTS:** `|E| ∈ {e−1, e}`.
- **DEFECT-2 KERNEL DIMENSION 3 — explained:** for `rows ≤ |E| ≤ cols` the kernel splits into `cols−|E|` locator directions ⊕ `|E|−rows` non-locator directions, total `cols−rows = d+1 = 3` (`hankelRel_first_boundary` for `|E| = e−1`).
- **TESTED FACTORIZATION `ker H = Λ_E·P_{≤d}`: TRUE iff `rows ≥ |E|`** — `hankelRel_iff_locator_mul` (positive), `hankelKernel_locator_law_iff` (exact iff), and the complete description for any row count `hankelRel_iff_values` / `hankelRel_iff_seed_decomposition`: `ker H = { (R·L₀ mod Λ_E) + Λ_E·G : deg R < |E| − rows }`, `L₀` the interpolant of `x ↦ v_x/a_x`.
- **BOUNDARY `|E| = e−1` and `|E| = e`: KILLED for the kernel-only route** — `exists_hankelRel_nonvanishing` produces a kernel vector vanishing at *no* point of `E`; it has degree `< |E|`, whereas every nonzero locator multiple has degree `≥ |E|`, so the *minimal-degree/primitive* kernel vector is precisely a non-locator (`exists_minimal_hankelRel_not_locator`). Route 3B points the wrong way.
- **CHEAP FALSIFICATION FIRST:** 7920 exact GF(p) instances (`p ∈ {11,…,1009}`, `|E| ≤ 5`, `d = 0…4`, full row reduction, no sampling): `ker H = Λ_E·P_{≤d}` ⟺ `rows ≥ |E|` in 7920/7920; in the 2520 deficient instances, never were all kernel vectors locators, and never was the minimal-degree one.
- **ANNIHILATOR FAMILY SIZE:** unchanged `≈ n·e ≈ 2³⁸`, inside the `2⁵⁷·⁹³` budget — but **not cashed out**, because its validity still needs boundary-layer locator validity.
- **UNCONDITIONAL δ > 1/4: NO.** No new certified radius; the `δ > 1/4` schedule statement remains conditional exactly as before, and I did not weaken or remove any existing declaration.
- **GENERAL DEFECT-d CONJECTURE: settled** — `ker H = Λ_E·F[X]_{≤d}` holds iff `|E| ≤ e−d`; on the top `d` layers the kernel acquires `|E|−rows` genuinely non-locator directions, so multiplicity `d+1` is *not* "locator times arbitrary low-degree factor" there.
- **NEXT SINGLE BOTTLENECK:** extra equations for the top `d` layers. Route 3A is dead inside the syndrome data: the `(n−k−e)×(e+1)` block already consumes all `n−k` syndromes, and the maximal number of consecutive rows for a degree-`≤ e` locator is exactly `(n−k)−(e+1)+1 = n−k−e`. Additional information must come from outside the single syndrome vector (the discarded badness conjunct, a second parity check, or a genuine multi-syndrome block-Hankel system).
- **DECISION: REDUCE, with a KILL of the kernel-only sub-route.**

No novelty is claimed for the moment/Vandermonde mechanism (classical key-equation material); the contribution is the exact iff, the complete kernel description including the deficient case, and their machine-checked proofs. All work is committed and pushed; `ARISTOTLE_SUMMARY.md` was not modified.

# Summary of changes for run ee4096d7-ed46-46d4-826c-f3507b9b638a
**FINAL STATUS: REDUCE** — the Johnson-radius MCA theorem is now reduced to exactly one explicitly named missing lemma; everything else is machine-checked and unconditional. New module `RequestProject/Root/CodingTheory/JohnsonStructuralDichotomy.lean` (sorry-free, audited in `RequestProject/Main.lean`); full account in `JOHNSON_STRUCTURAL_DICHOTOMY_REPORT.md`, plus `RESULTS.md` §109 and `DISCREPANCIES.md` D93.1.

**MAIN THEOREM.** `johnson_escape_or_structure` (unconditional, no budget/schedule/non-degeneracy hypothesis): for every line and every threshold `c`, either **ESCAPE** — the badness witnesses form a Johnson set family, `#Bad·(t² − n·c) ≤ n·t`, informative at `c = k` exactly when `k·n < t²` (the Johnson condition) — or **STRUCTURE** — some codeword pair has common agreement `|T| ≥ c+1` with the line *and* explains two distinct bad challenges. Cashed out by `card_explainedSet_le` (for every pair, `#{explained challenges} + |T| ≤ n`) and `card_badSet_le_of_gapBound`.

**STAGE I STATUS: proved**, in the form above: the alternative is unconditional and its structure branch is usable rather than merely descriptive (the pair produced already explains two bad challenges). A curve line is the extreme case `|T| = n`.

**STAGE II STATUS: proved outside one window.** Above the window (`|T| ≥ k+e`) `unexplainedBadSet_eq_empty_of_large_pair` shows every bad challenge is explained, so `#Bad ≤ n − |T|`; below it the Johnson count applies. Only `c+1 ≤ |T| < k+e` is open.

**EXACT MISSING LEMMA.** `GapBound k e c Bgap D`: for a codeword pair with `c+1 ≤ |T| < k+e`, the number of bad challenges it fails to explain is at most `Bgap`. Two theorems minimise it: `card_inter_lt_of_not_explained` (an unexplained bad challenge meets `T` in `< k` points, with every witness set) and the covering reformulation `exists_pair_explaining_of_isBad` + `card_badSet_le_of_explaining_family` (every bad challenge *is* explained by some pair with `|T| ≥ k`, and `#Bad ≤ Σ_P (n − |T_P|) ≤ (#pairs)·(n − k)`), so the question is exactly *how many codeword pairs are needed to explain one line*; any bound ≤ 2³⁸ suffices at the prize schedule.

**JOHNSON THRESHOLD CONNECTION.** At `c = k` the counting branch switches on literally at `t² = k·n`, and the residual window is non-empty exactly when `t² ≤ n(k+e−1)` — the complement of the regime of the previously certified radius. This is a reformulation of the transition, not a proof that degeneracy is impossible above it.

**CERTIFIED RADIUS.** Unconditional: unchanged, `δ = 0.177124…` at `ρ = 1/2`. Conditional on `GapBound`: `johnson_rho_half_delta_quarter` gives `ε_mca ≤ 2⁻¹²⁸` at `|D| = 2²⁰`, `k = 2¹⁹`, `e = 262145`, i.e. **δ = 0.2500009… > 1/4**, for `|F| ≥ 2¹⁶⁰` and any `Bgap ≤ 2³¹`. Unconditionally at that same schedule the escape branch alone gives `#Bad ≤ 13` (`escape_rho_half_delta_gt_quarter`).

**GAIN OVER 1/4: zero unconditionally** (the `δ > 1/4` statement is conditional). Note at `ρ = 1/2` the frontier `δ = 1/4` is the unique-decoding radius, so any crossing is genuinely past unique decoding: at this schedule `n − 2e = k − 2`, and every elementary argument attempted fails by exactly that two-position margin.

**NOVELTY RISK: high for the mathematics, low for the artefact.** Correlated agreement for lines up to the Johnson bound is a known target, and all counting ingredients used are standard; no novelty is claimed for the mechanisms, and no literature check was made on whether the missing lemma is already implied.

**NEXT PROOF MOVE.** The key-equation / Hankel-pencil route identified this session (recorded in the report, not formalised): every bad challenge is a root of an explicit **degree-one** annihilator `a_B + Z·b_B` built from a single RS parity check on a `(k+1)`-subset, and badness is a rank drop of a Hankel pencil with entries affine in `Z`. If some `(e+1)`-minor is non-zero one gets `#Bad ≤ e+1` immediately; otherwise a primitive kernel vector of the pencil yields an annihilator family of size `≈ n·e ≈ 2³⁸`, provided the specialised kernel vector can be shown to be a valid error locator — the one step where the kernel multiplicity (equal to 3 at this schedule) must be controlled.

No unrelated work was done; no axioms were introduced and no existing declaration was weakened or removed.

# Summary of changes for run c00209c5-0f29-4f54-9b04-56a1ab622264
## JOHNSON DECISIVE GATE — FORCED DEGENERACY ABOVE K\*: resolved, no kill

Deliverable: `FORCED_DEGENERACY_ABOVE_KSTAR_REPORT.md` (project root), backed by exact GF(p)/integer computations in `analysis/` (`forced_degeneracy_above_kstar.py`, `fd_core.py`, `fd_experiments.py`, `fd_sharpness.py`, `fd_adversarial.py`, `fd_kill.py`, `fd_anatomy.py`, `fd_envelope.py`) with all raw logs checked in. No Lean was added, per the mission scope; nothing here is machine-checked.

**SCORE CORRECTION applied throughout:** at ρ=1/2 the frontier is δ=1/4 and the safe Johnson target is worth **+10.620 bits** at 128 queries. The +27.745 figure (relative to the local radius 0.177124) is explicitly flagged as not a frontier gain.

### Required output
- **FORCED DEGENERACY ABOVE K\*: NO** in the operative sense — every forced common factor has curve degree ≤ 740 605 < t = 742 480 (forced factor ≤ 740 857, square ≤ 740 605, cube ≤ 740 354). K\* = 740 604 is the same threshold under a conservative weight convention; "K\*+1" is an indexing artefact. **UNKNOWN** for mechanisms outside the shear criterion.
- **SMALLEST INSTANCE:** M1 (n=9,k=2,e=4,t=5,m=4,L=20,bY=9) over GF(999983), cell K=2, s=6 — a *partial* curve line, in a newly identified **danger window** where the Bezout harmlessness argument is silent (87 904 values of s at ρ=1/2).
- **COMMON MODULE FACTOR / MULTIPLICITY:** (Y − (a+Zb)), multiplicity 2 in the window (3 for full curve lines). Measured module gcd was always exactly this power, in 185 exact cells.
- **STRUCTURAL SOURCE:** line on a low-degree curve at s points; sharp criterion W_K − K_eff·j < s(m−j). **No envelope case exists** (0 found across all tested families).
- **MAX #Bad:** 9 (n=18); growth exactly n/3+3 over n = 9, 12, 15, 18. **SCALABLE as a family but HARMLESS** — and the fatal part is now a *theorem*, not an observation: when the module gcd is a power of (Y−c) one has N_G = S, so every challenge invisible to the repair is rigid and **FATAL ≤ 1** for all n, K, s.
- **ANNIHILATOR FAMILY: YES** (symbolic, unformalized). **EXACT B = 1 386 904 900 024 = 2^40.3350** (ρ=1/2; 2^40.1793 at ρ=1/4). **ACTUAL-FIELD BUDGET** KoalaBear sextic 2^57.9321 → **fits**, ε_mca ≤ 2^−145.5971; under the artificial |F| ≥ 2^160 hypothesis it does not.
- **DICHOTOMY SURVIVES: YES** (candidate, not theorem — one unproved step per branch).
- **JOHNSON CONSEQUENCE:** repair not killed. Stronger: forced degeneracy needs K ≤ k+(nm−L)/bY, and that being < t is *equivalent* to Johnson k·n < t² (margin 2048.2). Degeneracy and Johnson are the same inequality.
- **GAIN OVER δ=1/4: +10.620 bits. DECISION: REDUCE.**
- **NEXT SINGLE BOTTLENECK:** the **converse** of the forcing criterion. This session added a new finding on that point: two counting-based attempts at the converse were carried out and both fail — the box variant is rigorous only for K ≤ k (it over-counts the sheared image above k) and is toothless for s < n (cap 160 737 263 ≫ t); the provably sound sub-box variant is vacuous. So counting alone cannot cap K above k; a genuine non-vanishing argument is required.

New work this session: the counting-cap soundness analysis; two larger scaled models (n = 15, 18) that pin the #Bad scaling law and confirm FATAL = 1 and N_G = S; completion of the GATE 1 envelope taxonomy (0 cases); the FATAL ≤ 1 theorem; and the full report. Honesty caveats (sufficiency-only criterion, 3 boundary cells with multiplicity one above prediction — never at r=1, random Z-specialisations, expected-dimension bound for higher-Y-degree factors, bounded exhaustiveness of the kill search) are recorded in the report.


# Summary of changes for run c278dd7b-1b19-4331-a095-c056b505ea8b
## Johnson bottleneck mining — completed

All seven gates were executed and the required output block is delivered in the new report **`JOHNSON_MIN_J_REPORT.md`**, backed by a new sorry-free Lean module **`RequestProject/Root/CodingTheory/CurveLineDegeneracy.lean`** (builds; axioms `propext`, `Classical.choice`, `Quot.sound` only) and by exact integer computations in `analysis/min_j_budget.py`, `analysis/min_j_adversarial.py`, `analysis/min_j_debug.py`.

### Headline answers

**ND∃ NECESSARY: NO.** Tracing the chain backwards from the conditional ε_MCA theorems, the first downstream consumer needs only `discLine b x₀ Q ≠ 0` at one *free* evaluation point — not full Y-degree (already flexible), not `gcd(Q, ∂_YQ) = 1`, not root distinctness.

**But no weakening inside that paradigm can work.** The consuming lemma destructures `IsBad` and *discards* the `¬ LineCloseOn` conjunct, so the chain bounds the **close** set, not the bad set; on the spike lines the close set is all of `F`. This kills P1–P5 and P7 for every threshold `r`/`s`; only P6 (bounded repeated-factor multiplicity) survives, and only if paired with a new counting step that consumes `¬ LineCloseOn`.

**MIN-J (v1)** — "the repeated part `gcd(Q, ∂_YQ)` of some admissible interpolant does not vanish along a whole witness set" — survives the spike lines but is **scalably FALSE** via a new **curve-line** family (`f₀ = a|_D`, `f₁ = b|_D`, `deg a < k ≤ deg b = K`): *every* admissible interpolant is divisible by `(Y − (a+Z·b))²`. Minimal exact instance, entire 27-dimensional interpolation space enumerated with no sampling: GF(5), D = {0,1,2,3}, k = 1, e = 2, f₁ = X|_D, Bad = {0}.

**As a by-product, (DICH) is dead** — not merely unproven. Curve lines are as far from the codeword-line variety as a line can be, yet admit no separable interpolant (`dichFar_fails`, instantiated at both prize schedules with |D| = 2^20).

**Generic pencil fails structurally**: the square holds on the *whole* interpolation space, so the obstruction polynomial is identically zero in λ. No module bridge was built (no exact identity established; deliberately not constructed by analogy).

**But the killed lines are harmless, and by the same inequality.** `curveLine_card_badSet_le_one`: a curve line with `K + e < |D|` has at most one bad challenge, unconditionally. And the forced-degeneracy threshold satisfies `K* < t ⟺ k·|D| < t² ⟺ t > √(k·|D|)` — exactly the Johnson condition (`degeneracy_threshold_lt_witness_size`); numerically `K* = 740604 < t = 742480` at ρ = 1/2.

**Prize budget (exact):** `B_max = 2^57.93` at the actual KoalaBear sextic field, `2^32` under the repository's `|F| ≥ 2^160` hypothesis. The family-of-annihilators repair (counting step formalised as `card_badSet_le_of_annihilator_family` / `epsMCA_le_of_annihilator_family`) costs `2^40.34` — affordable at the real field, insufficient at `2^160`.

**Frontier (GATE 7):** Δδ = +0.114792 at ρ = 1/2 (+27.745 bits at 128 queries) and +0.211764 at ρ = 1/4 (+65.105 bits); the target does cross δ > 1/4. **No FREEZE.**

**STATUS: REDUCED.** **NEXT SINGLE TEST:** can a shared square factor be forced above `K*`? No forcing mechanism is known there (the double-root lemma runs out of budget), and a proof that none exists is the only remaining obstruction between the family repair and the Johnson radius.

### Honesty caveats (recorded in the report)
No Johnson-radius theorem is proved; the Δδ/bit figures are the target's value, not a certified gain. The exhaustive small-field sweeps sit at parameters where the GS side condition is tight — genuinely admissible instances need matrices ≈ 4818×4758, out of computational reach — but the curve-line mechanism is proved in Lean at arbitrary parameters including the prize schedules, so scalability does not rest on those sweeps. The repair's algebra (constructing the annihilators from `Q`) is not formalised, only its counting step.

Also updated: `RESULTS.md` §108, `DISCREPANCIES.md` D92.1, and regenerated `INDEX.md`. `ARISTOTLE_SUMMARY.md` was not touched. All work is committed and pushed; no unrelated repository tasks were performed.

# Summary of changes for run 797ad1d9-f848-43cd-923c-466caabde951
NEAR-u was killed at Gate 1. No Lean was written (the gate conditions for formalisation are not met). Full account: `NEAR_U_KILL_REPORT.md`; new code `analysis/near_u_adversarial_kill.py`, `analysis/near_u_counterexample.py`, `analysis/near_u_maxbad_search.py`; correction block appended as §9 of `MCA_CONSTITUTION_CHECKPOINT.md`; the earlier random probe `analysis/near_u_window_probe.py` is annotated as superseded (unchanged otherwise).

**NEAR-u STATUS:** KILLED — `#Bad ≤ e+1` is false throughout its own open window `n−k−e < u ≤ n−√(kn)`, at every rate tested and over every field tested.

**STRONGEST ADVERSARIAL TEST:** the line is *solved for*, never sampled. Two badness mechanisms are superimposed at `u = e+1`. (i) Zero-codeword witnesses: each `x ∈ E` gives the bad challenge `γ_x = −a₀(x)/a₁(x)`; the witness sets are disjoint, so this mechanism alone caps at `⌊u/(u−e)⌋`, which equals exactly `e+1` at `u = e+1` — i.e. the conjectured ceiling is just this value, not a barrier. (ii) Maximal root collision: push all `e` errors outside `E`, take `R ⊆ D\E` with `|R| = n−u−e` and `g = Π_{x∈R}(X−x)`; `deg g < k` precisely when `e ≥ (n−k)/2`, and `g` agrees with `a₀+γ*a₁` on `E ∪ R` (size `n−e`) while `a₁` is far there. Setting `a₀|E = g|E − γ*·a₁|E` with the ratios `g(x)/a₁(x)` pairwise distinct makes all `e+2` challenges bad at once. Exact certificates (explicit witness polynomial per challenge) at `(n,k,e) = (7,1,3), (8,2,3), (12,3,5), (24,12,6), (32,16,8), (64,32,16), (128,64,33), (128,64,36)` for `q` from 11 to 2³¹−1; a two-root-set variant certifies `e+3`.

**MAX #Bad / (e+1):** 2.000 — exhaustive enumeration of the complete bad set on the minimal instances gives `#Bad = 2(e+1)`, identical for `q = 11, 13, 17, 23, 101, 1009, 10007`, so the violation is not a small-field artefact. Minimal counterexample: `q=11, n=7, k=1, e=3, u=4`, `Bad = {1,3,8,9,10}`, `#Bad = 5 > 4`.

**SCALABLE COUNTEREXAMPLE:** YES. Defined whenever `(n−k)/2 ≤ e` and `e+1 ≤ n−⌈√(kn)⌉` — the whole window, unique decoding through Johnson, every `n ≥ 24` at `ρ = 1/2`, any field of size ≳ u.

**SYMBOLIC δ_MAX:** `δ_max^{NEAR-u}(ρ) = max{(3−√(5+4ρ))/2, 1−ρ^{1/4}}` (self-consistent branch); at `ρ = 1/2` the second branch is inconsistent, so `δ_max^{NEAR-u}(1/2) = (3−√7)/2 = 0.177124344…` — exactly the radius already certified. **CROSSES 1/4: NO. Δδ = 0.000000. 128-query bit gain: 0.000 bits.**

**MINIMAL SURVIVING LEMMA:** none. No bound `#Bad ≤ B` rescues the route: the ceiling `1−√(τ₀/n)` is fixed by the far half together with the window's own limit `τ₀ ≥ √(kn)`, independently of `B`.

**SCORES:** NEAR-u `P_success 0 · V_radius 0 · V_novelty 0` (the killing family is the already-Lean-verified spike geometry). ND∃/(DICH) `P_success MEDIUM-LOW · V_radius HIGH (Δδ = +0.115769, +27.99 bits over 128 queries at ρ = 1/2) · V_novelty MEDIUM · C_research HIGH`. NEAR-u is strictly dominated.

**DECISION:** KILL NEAR-u; RETURN TO ND∃ (specifically (DICH)). Not formalised — the mechanism adds no mathematics beyond the existing spike family.

**NEXT SINGLE TEST:** run the same adversarial construction against the near half of (DICH): for lines at distance exactly `u` from the codeword-line variety, measure max `#Bad` adversarially as a function of `(u, e, n−k)` and fit the true law (present data: `#Bad ≈ u/(u−e) + O(u/(n−k−e))`, capped by list size). Pursue (DICH) only if that law plus the far half's Johnson condition still admits `δ > 1/4` at `ρ = 1/2`.

Consistency note: no existing Lean theorem is contradicted. The proved near half assumes `k+e ≤ n−u` (i.e. `n−k−2e ≥ 1` at `u = e+1`), while the counterexample family needs `e ≥ (n−k)/2` (i.e. `n−k−2e ≤ 0`) — exact complements, so the counterexamples begin one step past the theorem's hypothesis. All certified radii, `nearFar_ceiling`, the pair-covering results and the ND∃ artefacts are untouched.

# Summary of changes for run b7c3f89e-0869-4717-9a17-d973b1201937
Working under the research constitution (sole objective: raise the certified RS MCA/proximity radius δ; ρ = 1/2 as the primary laboratory; falsify before proving), I closed one branch, opened and formalized a new mechanism, and reduced the remaining obstruction to a single strictly smaller lemma. Everything below builds (full `lake build`, 8271 jobs), is free of `sorry`/`admit`, and uses only the standard axioms `propext`, `Classical.choice`, `Quot.sound`. All work is committed and pushed.

**1. Branch (CL) — KILLED.** `analysis/cl_codeword_line_count_probe.py` computes, exactly and exhaustively per instance, the whole bad set and the whole set of arising codeword lines. At q = n = 11, k = 3, e = 5 (past unique decoding, inside Johnson) the worst instance has #Bad = 6 but C = 14 codeword lines with fibres of size 2, so C tracks binom(#Bad,2) and the intended bound is vacuous. The probe also pins the structural reason: the codeword lines through a fixed bad challenge γ correspond exactly to the degree-<k polynomials agreeing with f₁ on ≥ k points of its witness set — a list-decoding count far below its own Johnson radius, hence unbounded.

**2. New unconditional theorem — the near/far codeword-line dichotomy** (`RequestProject/Root/CodingTheory/NearCodewordLineMCA.lean`):
- *Near half* (`card_badSet_le_succ_radius_of_near_codeword_line`): if **any** pair of degree-<k polynomials agrees with the line's coefficient pair (f₀,f₁) on ≥ k + e common positions, then the line has at most e + 1 bad challenges — **at any radius, with no regime hypothesis**. This strictly generalises the existing unique-decoding count, whose hypothesis 3e < |D| − k + 1 serves only to manufacture such a pair, and it makes the whole "spike line" counterexample family of the earlier separability work provably harmless rather than just the single spike.
- *Far half* (`card_badSet_le_setFamilyJohnson_of_far`): otherwise no two badness witnesses meet in ≥ k + e positions, so they form a Johnson set family.
- *Combination* (`card_badSet_le_of_nearFar`, `epsMCAmax_le_of_nearFar`): #Bad ≤ max(e + 1, n·t/(t² − n(k+e−1))) whenever n(k+e−1) < t², t = n − e.
- *Certificate* (`nearFar_rho_half`): at |D| = 2²⁰, k = 2¹⁹, radius e = 185728 (δ = 0.177124…), #Bad ≤ 456383, hence ε_mca ≤ 2⁻¹²⁸ for every field with |F| ≥ 2¹⁶⁰. **This raises the radius this repository certifies at rate ρ = 1/2 from 0.166666… to 0.177124…, i.e. Δδ = +0.010458** (+0.0182 bits per spot check, ≈ +2.33 bits over 128 queries). It is still below the certified frontier (1−ρ)/2 = 0.25 and below Johnson 1 − √ρ = 0.292893…; no frontier crossing is claimed.
- *Ceiling* (`nearFar_ceiling`): the mechanism's regime is exactly (1−δ)² > ρ + δ, i.e. δ < (3 − √(5+4ρ))/2 = 0.177124 / 0.275255 / 0.327396 / 0.354356. It beats the pair-covering mechanism (ceiling 1 − ρ^{1/4}) precisely at ρ = 1/2 and nowhere else among the four rates, so the current best certified radii are 0.177124 / 0.287258 / 0.398752 / 0.491867 at ρ = 1/2, 1/4, 1/8, 1/16.

**3. The remaining obstruction, reduced and probed.** Both the pair-covering route and this one are endpoints of one threshold interval [√(kn), k+e]; the single statement that would move them is (NEAR-u): bound #Bad for a line whose coefficient words are supported on a set of size u in the window n−k−e < u ≤ n−√(kn). The exact probe `analysis/near_u_window_probe.py` (actual bad set, exhaustive witness enumeration) finds max #Bad = e + 1 exactly, never more, at every tested point of the open window, and shows the bound is attained. So (NEAR-u) survives falsification with the same constant; per the formalisation budget it is queued for external pre-screen rather than formalized, together with the next probe (an adversarial rather than random construction, whose dimension count 2/(1−δ−ρ) suggests #Bad stays O(1) up to Johnson).

**Files.** New: `RequestProject/Root/CodingTheory/NearCodewordLineMCA.lean`, `analysis/near_far_dichotomy_optimiser.py`, `analysis/near_u_window_probe.py`, `analysis/cl_codeword_line_count_probe.py`. Updated: `RequestProject/Main.lean` (imports + axiom audit for the new theorems), `MCA_CONSTITUTION_CHECKPOINT.md` (§6–§8, full checkpoint blocks in the required format), `INDEX.md` (regenerated). `ARISTOTLE_SUMMARY.md` was not modified. No axioms were introduced and no existing declaration was removed or weakened. No novelty is claimed for the mechanisms: both halves are elementary counting, and the contribution is the admit-free hypothesis-form near lemma at arbitrary radius, the closed case distinction, and the exactly located ceiling.

# Summary of changes for run 5428c720-8455-44e2-8803-6c7ef347ad6a
Kontynuowałem projekt od miejsca, w którym się zatrzymał: repozytorium budowało się czysto i nie zawierało `sorry`, więc domknąłem cztery pozycje otwarte z listy zadań FFT. Wszystko buduje się w całości (`lake build`, 8268 celów), bez `sorry`/`admit`, bez nowych aksjomatów — audyt `#print axioms` w `RequestProject/Main.lean` pokazuje wyłącznie `propext`, `Classical.choice`, `Quot.sound` dla każdego nowego twierdzenia.

**1. `RequestProject/Bluestein.lean` — transformata „chirp" Bluesteina (pozycja otwarta O4).** Wszystkie dotychczasowe szybkie algorytmy w projekcie narzucały warunki na długość (potęga dwójki, względnie pierwsze czynniki, pierwszość). Bluestein nie narzuca żadnego:
- `dft_eq_chirp_conv` — dla każdego `n` i każdej długości `L ≥ 2n − 1` transformata długości `n` to **jeden splot cykliczny długości `L`** plus mnożenia przez stałe chirpowe; jedyne założenie to istnienie pierwiastka kwadratowego `ω` z `ζ`;
- `sq_root_of_odd`, `dft_eq_chirp_conv_odd` — dla nieparzystych `n` pierwiastek `ζ^{(n+1)/2}` zawsze istnieje w grupie generowanej przez `ζ`, więc rozszerzenie ciała nie jest potrzebne;
- `M31.dft31_eq_chirp_conv63` — nad `M31` transformata długości 31 to jeden splot długości **63** (63 dzieli `p − 1`, w odróżnieniu od 62 i 64), a wszystkie stałe chirpowe są potęgami dwójki, czyli rotacjami bitowymi (`chirp31_is_rotation`, `chirpKer63_is_rotation`) — narzut Bluesteina nie zawiera tu ani jednego ogólnego mnożenia;
- `M31.dft151_eq_chirp_conv693` — zysk przy „szorstkiej" długości: 151 jest czynnikiem pierwszym `p − 1`, ale nie jest gładka; Bluestein zamienia ją na splot długości `693 = 9·7·11`, gładkiej i dzielącej `p − 1`.

**2. `RequestProject/Radix4.lean` i `RequestProject/Radix8.lean` — brakujące kolumny porównania kosztów (O3).** W tym samym modelu co `SplitRadix.lean` (mnożenia przez pierwiastki czwartego stopnia są darmowe): pełna klasyfikacja darmowych twiddle'i wszystkich gałęzi (`3m − 4` na poziom radix-4 wobec `4m − 4` dla dwóch poziomów radix-2; `7m − 8` plus motylki 8-punktowe dla radix-8), stąd `radix4Cost_lt_radix2Cost` dla `k ≥ 4`, `splitRadixCost_le_radix4Cost` oraz `radix4Cost_le_radix8Cost ≤ radix2Cost`. Wniosek: w tym modelu rodzina jest liniowo uporządkowana `S ≤ R₄ ≤ R₈ ≤ R₂` — **radix 8 nie poprawia radix 4**; zapisałem wprost, że model wycenia każdą stałą spoza `μ₄` na jedną jednostkę i dlatego nie widzi taniości pierwiastków ósmego stopnia, którą wykorzystuje realne jądro radix-8. Ogólne kryterium `four_pow_eq_one_iff` (`ζ^e ∈ μ₄ ↔ N ∣ e`) obsługuje wszystkie te klasyfikacje.

**3. `RequestProject/ExtensionVsCircle.lean` — NTT nad `𝔽_{p²}` kontra circle FFT (O6).** `extRadix2_correct` daje istnienie i poprawność trasy rozszerzeniowej (`k ≤ 32`). Obie trasy wykonują tyle samo motylków, ale mnożenie w `𝔽_{p²}` kosztuje **dokładnie trzy** mnożenia bazowe (udowodnione wcześniej `M31sq_bilinear_complexity`), więc `extBaseMuls = 3 · circleBaseMuls`, `circle_lt_ext_baseMuls` dla `k ≥ 1`, a `circle_lt_ext_packed` utrzymuje przewagę 3/2 nawet wobec sztuczki pakowania dwóch transformat w jedną.

Dokumentacja: nowe sekcje 104–107 w `RESULTS.md`, nowe wiersze P55–P58 oraz zaktualizowane pozycje otwarte O3, O4, O6 w `DISCREPANCIES.md`. Tabela Properties zawiera nowe deklaracje oznaczone jako udowodnione na podstawie czystego builda. `ARISTOTLE_SUMMARY.md` pozostał nietknięty.

Zastrzeżenia bez zmian: wszystkie stwierdzenia o kosztach są względne wobec jawnie zdefiniowanych modeli (liczba mnożeń, darmowe `μ₄`, darmowe rotacje), dla Bluesteina nie sformułowano żadnego twierdzenia o liczbie operacji, kontrakty w `verus/` pozostają niesprawdzone maszynowo (brak toolchainu), i **nie wykonano żadnych benchmarków**, więc nie formułuję porównań wydajności z istniejącymi bibliotekami. Wszystko jest zacommitowane i wypchnięte.

# Summary of changes for run 27aa75ab-9f56-4b07-8fcf-b229ae6f0909
## MISSION OUTCOME: **D — UNIQUE BOTTLENECK IDENTIFIED**

Full decision log: `JOHNSON_BRIDGE_DECISION.md`. Summary in `RESULTS.md` §102–§103; caveats in `DISCREPANCIES.md` D91.1–D91.2.

### CURRENT RADIUS FRONTIER (plain Reed–Solomon)
`δ ≤ (1−ρ)/2` (`k + 2e ≤ n`), `#Bad ≤ (k+1)e + 1`, unconditional and admit-free (`Subresultant.card_badSet_le_unconditional`).

### JOHNSON TARGET
`δ = 1 − √(ρ + 2⁻²⁰) − 2⁻¹⁰`, i.e. `e = 306096` at `ρ = 1/2` and `e = 523263` at `ρ = 1/4`, `n = 2²⁰`.

### MISSING ALGEBRAIC INGREDIENT
Exactly one statement, **(ND∃)**: *for every line with a nonempty bad set, **some** Guruswami–Sudan interpolant `Q` of the formal line `f₀ + Z f₁` inside the budget has, at some `x₀`, `Q(x₀,Y,Z)` of full `Y`-degree `bY` and squarefree in `Y`.* Every other step of the chain — interpolant existence, the double-root/containment lemma, the degree bound, the `ε_mca` conversion, the numeric thresholds — is already admit-free here.

### CHEAP COUNTEREXAMPLE (the main new negative result)
The Johnson-radius certificates in the repository were carrying the **∀-form** hypothesis (ND∀), and **(ND∀) is false**. Three formalized ingredients: interpolation conditions are multiplicative, so `Q₀²` at a halved schedule is an interpolant at the full schedule (`LineInterpolant.sq`); the line discriminant of a square vanishes at *every* point (`discLine_eq_zero_of_isSq`); and lines with a bad point exist at every rate and radius in range (`exists_badSet_nonempty`). The halved schedule still meets the Guruswami–Sudan counting condition at both prize parameter sets — using a sharpened monomial count `2k·#monIdx(k,L) ≥ L² + kL` — with margins ×1.00048 and ×1.0000017. Hence `nd_forall_false`, `nd_forall_false_rho_half`, `nd_forall_false_rho_quarter`: those nine certificates were **vacuous as stated**, worth 0 bits. Nothing was deleted; they stand with the caveat recorded.

### THE REPAIR (same constants, satisfiable hypothesis)
`epsMCAmax_le_of_schedule_exists`, `threshold_rho_half_bchks_exists`, `threshold_rho_quarter_bchks_exists`: `ε_mca ≤ 2⁻¹²⁸` at the Johnson radius for `|F| ≥ 2¹⁶⁰`, under (ND∃), which the square construction does not refute.

### STRUCTURAL KILL OF THE CURRENT MACHINERY
All six unique-decoding mechanisms (Welch–Berlekamp/subresultant pencil, `W_can`, order-`e` syndrome recurrence, top Hankel determinant, cumulative Hankel rank, support/incidence locus) factor through one *forcing* step: extracting a canonical codeword pair on the intersection of two agreement sets, of guaranteed size `n − 2e`. Formalized dichotomy: unique for `k + 2e ≤ n` (`forcing_unique_at_frontier`); and for `n < k + 2e`, on **every** set of the guaranteed size and for **every** data, two distinct degree-`< k` polynomials realise it (`exists_two_interpolants_of_card_lt`, `forcing_not_unique_beyond_frontier`) — the mechanism has no output at all. This is a mechanism barrier, not a refutation of MCA past `(1−ρ)/2`.

### DEGREE / BAD-SET BUDGET AND BIT GAIN
`#Bad ≤ (2bY−1)·dZ` = 3 228 636 701 (`ρ=1/2`) and 3 633 343 112 (`ρ=1/4`), both `≤ 2³²`, so `ε_mca ≤ 2⁻¹²⁸` at `|F| ≥ 2¹⁶⁰`. Proving (ND∃) moves `δ` from 0.25000 to 0.29192 and from 0.37500 to 0.49902, i.e. **+10.6 bits** and **+40.8 bits** at `t = 128` (+16.8 / +64.5 at `t = 202`). Any further `#Bad` improvement inside the current radius is worth 0 bits, confirming the mission's premise.

### ALSO KILLED
Transferring the repository's unconditional folded-RS capacity bound (`δ ≤ 1−ρ−η`) to plain RS by regrouping the smooth domain into blocks of size `s`: folding preserves the rate but multiplies the relative radius by `s`, so it certifies only `δ ≤ (1−ρ−η)/s`, worse than `(1−ρ)/2` for every `s ≥ 2`.

### ARTIFACTS
Two new sorry-free modules — `RequestProject/Root/CodingTheory/NonDegeneracyExists.lean` (13 declarations) and `RequestProject/Root/CodingTheory/ForcingBarrier.lean` (4 declarations) — both imported by `RequestProject/Main.lean`, which builds cleanly; `#print axioms` audits there show only `propext, Classical.choice, Quot.sound` for all 17. `ARISTOTLE_SUMMARY.md` was not modified. All work is committed and pushed.


# Summary of changes for run c8ab21da-dc3e-4b0f-ab82-11d53448a08d
**PRIZE GAP AUDIT delivered — no new mathematics developed, as instructed.**

Written up in `KOALAIRS12_PRIZE_GAP_AUDIT.md`, with all numbers produced in exact/80-digit arithmetic by `analysis/koala_irs_prize_gap_audit.py`, and a short pointer added as `RESULTS.md` §101. No Lean files were changed; the project was rebuilt in full (8257 jobs, success, no `sorry` in the log) and the axiom report re-read.

**What could and could not be traced.** The reduction was read directly from the public ArkLib toy-problem source: `certifiedExtractorError` = `(1−δ)^t + (ε_mca(C,δ) + |Λ(C^⋈2,δ)|/|F|)·(1−(1−δ)^t)`, with the KoalaBear sextic challenge field (`log₂|F| = 185.93`), `n = 2^16`, `k = 2^20`. The concrete "koalaIRS12" numeric profile is explicitly *not* in ArkLib — the source says it lives in a downstream prize-challenge repository — so the exact (ρ, t, δ) triple behind 67.33 was reconstructed from the number itself; every conclusion is stated so it does not depend on which reconstruction is right.

**Findings.**
1. *The MCA constant is worth exactly zero bits.* Every bad-set bound proved in this project lies between 2^13 and 2^32, so ε_mca ≤ 2^−154 against a query term of 2^−67. The certified score is unchanged to 30+ decimal places even at #Bad = 0. This kills, for prize purposes, the sharp value (ℓ−1)(e+1), the support-overlap phase law, the circuit bound (which is additionally vacuous beyond e ≈ 7), the Hankel/locator factorisation, staircase/cumulative-rank refinements, the top-word −1, the two-word #Bad ≤ |T|, the subresultant bound's constant, and every combination of them. A constant improvement first bites at the ceiling −log₂((B+1)/|F|) ≈ 157 bits.
2. *Only the radius reaches the score*, which equals t·log₂(1/(1−δ)). The largest radius certified here for the arity-2 event is δ ≤ (1−ρ)/2 (`Subresultant.card_badSet_le_unconditional`, axiom-clean). ArkLib already proves the same window admit-free with a better constant (`rs_mcaError_le_of_le_relUDR`, ε_mca ≤ n/|F|, plus the sorry-free interleaving transport `mcaError_interleaved_eq`), and its GKL 1.5-Johnson bound exceeds our radius at rate ≤ 1/8. So our radius ties the public admit-free frontier at rates 1/2 and 1/4 and is below it at 1/8 and 1/16.
3. *The "top word within decoding radius" hypothesis is not supplied by the protocol.* Traced to the actual objects: the supremum is over `ViolatingInstance`, whose only hypothesis is that the *pair* violates the relaxed relation, and `mcaError` quantifies over all word stacks. Our own extremal family (codeword in one slot, sharp bad set) shows the configuration is realisable. Refuted, and worth 0 bits even if it applied.

**Required output.** CURRENT RECORD 67.33 bits; OURS 67.33 bits; DELTA BITS +0.000000 from this repository; RECORD BEATEN: **NO**. (Under the two readings that reproduce 67.33 exactly — GKL radius with ρ=1/2, t=202 or ρ=1/4, t=101 — a gain of +16.5 / +1.15 bits is available by selecting a different already-proved ArkLib theorem, i.e. route selection, not our mathematics.)

**Bottleneck.** `B_target` does not exist: any B ≤ 2^98 is sufficient at a 67-bit score, and no B, not even 0, is sufficient without a radius increase. The binding inequality is the radius window (`k + 2e ≤ |D|` / δ ≤ relUDR). Sensitivity at the frontier: d bits/dδ = t/((1−δ)ln2), so +1 bit costs Δδ ≈ 0.0026 at ρ=1/2 — about 170 extra correctable positions at n = 2^16.

**DECISION: C — mathematical gap remains.** The smallest sufficient improvement is any admit-free arity-2 MCA bound with #Bad ≤ 2^98 at a radius strictly above max((1−ρ)/2, 1−ρ^(1/3)). The closest existing mechanism is the Johnson-range route: ArkLib's single external admit on this path is the Johnson-range MCA theorem (δ < 1−√ρ); proving it admit-free is worth +17.2 bits over the frontier at ρ=1/2, t=202 (+33.7 over the reconstructed incumbent). On our side the nearest machinery is the Guruswami–Sudan/Johnson list route, which currently stops at half the Johnson radius, and the subresultant/Welch–Berlekamp pencil, currently tied to the unique-decoding window. As instructed, I stopped at the audit and did not begin work on C.


# Summary of changes for run ae40d725-ab81-4afc-8f7d-f70d6e5fa792
Mission "M = e+1 extremal phase" is complete, with a decisive verdict on every route: two PASSes and three KILLs, all certified in Lean (`sorry`-free, axiom-clean — `propext`, `Classical.choice`, `Quot.sound` — audited from `RequestProject/Main.lean`, which builds in full).

**What was established** (files `RequestProject/Root/CodingTheory/MinimalSupportExtremalPhase.lean`, `MinimalSupportHankelBridge.lean`, `MinimalSupportSlotSharpness.lean`; reconnaissance `analysis/minimal_support_extremal_phase_probe.py`; full write-up `docs/MINIMAL_SUPPORT_EXTREMAL_PHASE_REPORT.md` including the requested DECISION LOG, summarised in `RESULTS.md` §100):

1. PASS — badness is a root locus. With `P_x(X) = ∑_{j<ℓ}(f_j x − q_j(x))X^j`, in the minimal-support phase a challenge is bad iff some `P_x` vanishes at it; `Bad = ⋃_{x∈T} roots(P_x)`. Consequences: the refined count `#Bad ≤ ∑_x deg P_x`, and top-word rigidity (each support coordinate where the last word is uncorrupted removes one bad challenge).
2. PASS — complete classification, stability and inverse theorem. `#Bad = (e+1)(ℓ−1)` iff every `P_x` has exactly `ℓ−1` distinct roots and the root sets are pairwise disjoint; near-extremality `#Bad ≥ sharp − δ` forces *every* row to have ≥ `ℓ−1−δ` distinct roots; the unconditional normal form adds that the top word is corrupted at every coordinate of the support.
3. KILL — no invariant beyond that classification, and no exclusion by the domain. Every prescribed pattern is realised over every Reed–Solomon domain by an explicit family; rank, minor, proportionality and determinant conditions on the error matrix are all broken by extremizers, and the support and the root pattern are independent, so no relation coupling the error matrix to the locator can hold.
4. KILL (new this session) — no exclusion by the challenge set. For every challenge set `C` with `(e+1)(ℓ−1) ≤ |C|` there is an extremal family whose bad set lies entirely inside `C`, and when `|C| = (e+1)(ℓ−1)` *every* challenge of `C` is bad for it. Only cardinality excludes: `|F| < (e+1)(ℓ−1)` ⟹ `#Bad < (e+1)(ℓ−1)`.
5. KILL (new this session) — the surviving protocol-side exclusion is about the *top* slot only. The `±`-pattern family of arity 3 (error-value polynomials `X² − r_x²`) attains the sharp value `2(e+1)` while its slot-1 word is identically zero, i.e. literally a codeword; the configuration is realised over `ZMod p` for every prime `p > 2(e+1)` and every domain in the window, so it is a genuine, non-vacuous counterexample.
6. PASS — Hankel ↔ locator bridge as an exact identity: for the `(e+1)×(e+1)` syndrome/moment matrix, `det H(γ) = (∏_{x∈T} P_x(γ))·det Vandermonde(T)²`, hence a challenge is bad iff that one determinant of size `e+1` vanishes — a badness test whose size depends on the decoding radius, not on the code length.

The one exclusion that survives everything: if the *top* word is itself within the decoding radius of the code, then `#Bad < (ℓ−1)(e+1)` strictly.

Net effect for the programme: the universal constant `(ℓ−1)(e+1)` cannot be lowered by hypotheses on the domain, on the sampling set, or on the linear algebra of the error matrix; only hypotheses on the leading word or on the field size can. All results are registered in the Properties table with status `proved`, and all work is committed and pushed.

# Summary of changes for run 72c73573-2be5-49f1-9176-bdd6d9dadb7c
## Mission: globalise the staircase law — one PASS and one KILL, both certified

I worked entirely inside the MCA/proximity branch, followed the requested workflow (exact finite probe → pattern → minimal Lean theorem), and reused the existing machinery instead of building new abstract theory. The whole project builds cleanly, `sorry`-free, with no new axioms (`propext`, `Classical.choice`, `Quot.sound` only, audited in `RequestProject/Main.lean`).

### First gate — cheap exact falsification
`analysis/support_overlap_staircase_probe.py` enumerates small RS instances in exact modular arithmetic (p ∈ {5,7,11}, |D| ∈ {6,7}, k=2, e ∈ {1,2}, ℓ ∈ {2,3}), computing the bad set *by definition* (brute force over all witness sets) and the canonical support invariant M = minimal joint error support over all codeword families. Observed maxima of #Bad match `min((ℓ−1)M, ⌊(ℓ−1)M/(M−e)⌋)` exactly at every in-window M. Two conclusions: the maximum over M sits at M = e+1 (a large bad set does *not* come with small unions), and there is a genuine phase law in M. Numerical reconnaissance only; the Lean statements below are the certificates.

### PASS — the support-overlap phase law
The incidence count behind the project's `#Bad ≤ (ℓ−1)(e+1)` was internal to a proof; it is now exposed as a law in the joint error support size M:

  **#Bad · (M − e) ≤ M · (ℓ−1)**

worst at M = e+1 and improving as the support grows. Cash-outs: M ≥ e+2 gives `#Bad < (ℓ−1)(e+1)` strictly; **M ≥ 2e gives `#Bad ≤ 2(ℓ−1)`, with no dependence on the decoding radius at all** (and `ε_mca ≤ 2(ℓ−1)/|F|`, strictly better than the previous bound once e ≥ 2).

The law is exact, not merely an upper bound: the new **block-spike family** (g blocks of c positions sharing one root polynomial) has, for e = (g−1)c, joint support M = gc and bad set of size exactly g(ℓ−1), i.e. equality `#Bad·(M−e) = M·(ℓ−1)` along a two-parameter family. c = 1 recovers the known extremizer; g = 2 shows the radius-free bound 2(ℓ−1) is attained too.

### Structure theorem — large Bad forces minimal-union geometry
`#Bad = (ℓ−1)(e+1)` forces M = e+1 *exactly*, giving an unconditional dichotomy in the window k+(ℓ+1)e ≤ |D|: either `#Bad < (ℓ−1)(e+1)`, or the whole family agrees with one codeword family off a common set of exactly e+1 coordinates. So many Bad does force a support-overlap structure — the tightest, low-union one.

### KILL — the staircase cannot be globalised
The staircase charge `(e+1) − |T_0 ∪ … ∪ T_q|` is positive only for unions of size ≤ e, and the forced geometry sits exactly one coordinate above that threshold. This is certified, not incidental: for the extremizer the top word is at distance exactly e+1 from the code, so no admissible support family has a union of size ≤ e, and every staircase charge is identically zero. The certificate is scalable in ℓ, e, k and all large enough domains and fields. Staircase and phase law act in opposite geometric regimes (M ≤ e versus M ≥ e+2) and are complementary; a further improvement of (ℓ−1)(e+1) cannot come from support geometry alone — it must come from excluding the extremal *values*, i.e. the explicit-domain / RS-locator route.

### Where things are
- `RequestProject/Root/CodingTheory/SupportOverlapPhase.lean` — new file with all of the above.
- `RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean` — the defect-form incidence law exposed; the previously proved sharp bound is now derived from it (statement unchanged).
- `docs/SUPPORT_OVERLAP_PHASE_REPORT.md` — full report, including the probe table and the regime map.
- `RESULTS.md` §99, `RequestProject/Main.lean` axiom audit, and the Properties table updated.

No novelty is claimed for the double-counting argument, common agreement sets, or spike-type extremizers, all of which were already in the project. New and formally verified here: the defect-form phase law as a standalone statement with its radius-free regime, the block-spike equality family, the rigidity of the extremal support geometry with its unconditional dichotomy, and the vanishing of the staircase charge on extremizers.

# Summary of changes for run 1f853558-5edf-4076-9cd5-21a146c86377
## Verdict: PASS on simultaneous multi-layer rank charging

The gate you set was staged: first cash out the existing rank-profile results in real RS parameters, and only if that was insufficient, attempt simultaneous charging of rank deficiencies of several words. Both stages were carried out. The answer to the primary question — *can rank deficiencies of more than one word/coefficient layer be charged simultaneously?* — is **yes**: the deficiencies add, the resulting law is sharp, and it strictly improves the multi-word bound already formalised in the repo.

All results are in `RequestProject/Root/CodingTheory/HankelCumulativeRank.lean` (~620 lines), fully proved: no `sorry`, no new axioms, and each theorem is audited by `#print axioms` in `RequestProject/Main.lean`, reporting only `propext`, `Classical.choice`, `Quot.sound`. The full project builds cleanly.

### The general law (additivity of window coranks)
For a matrix polynomial `∑_{j<ℓ} Xʲ·M_j`, with `S_q` the column span of the top `q+1` coefficient matrices:

    deg det(∑ Xʲ M_j) + ∑_{q<ℓ−1} (n − dim S_q) ≤ n(ℓ−1)

(`MatPoly.natDegree_det_matPoly_add_sum_le`). This is read off the multilinear column expansion, not postulated: a nonvanishing term must satisfy the column-count constraint for *every* window at once, and summing the complementary counts reproduces exactly the term's degree deficiency — which is precisely why there is no double counting. Transported to the offset Hankel matrix this gives `#Bad + e|Z| + ∑_{q<ℓ−1}((e+1) − dim S_q) ≤ (e+1)(ℓ−1)`.

### Proximity feeds the coranks: the staircase law
Via the syndrome dictionary, every moment column of a word agreeing with a codeword off `U` lies in the span of the `|U|` Vandermonde vectors of `U`. This upgrades the per-word bound `rank H(u) ≤ d(u,RS)` to a **joint** window statement (`finrank_topColSpan_le_of_window_close`), yielding the staircase law with *unequal* supports:

    #Bad + e|Z| + ∑_{q<s} ((e+1) − |T_0 ∪ … ∪ T_q|) ≤ (e+1)(ℓ−1)

and, in the subtracted shape requested, `#Bad ≤ (e+1)(ℓ−1) − Δ` (`card_badSetG_le_sub_staircase`) with `Δ` explicit. The previously formalised common-support bound is the constant case; pairwise distinct supports pay the common-support charge *plus* a triangular term `s(s−1)/2`.

### Cash-out and comparison
- **Sparse-family regime**: `ℓ−1` words at distance 1 with distinct error locations give `2(#Bad + e|Z|) ≤ ℓ(ℓ−1)` and `ε ≤ ℓ(ℓ−1)/(2|F|)` — the decoding radius disappears entirely. Certified strictly stronger than the previously formalised common-support bound (`s(s+1) < 2s²`): a factor tending to 2, with a gap growing quadratically in the arity.
- **Two-word cash-out**: at `ℓ = 2` the law collapses to `#Bad ≤ |T|` — the bad set of a line is bounded by the error weight of the top word alone, with no dependence on rate or radius.
- **Non-vacuity**: the hypothesis `shiftDet ≠ 0` is certified inhabited — evaluating the Hankel matrix polynomial at `X = 0` returns the bottom word's moment matrix, so one far word plus several single-error words realises the regime.

### Extremizer exclusion and sharpness
An extremizer admits **no window** of top words jointly localised on ≤ e coordinates (`not_window_close_of_extremal`); the earlier single-word statement is the case `q = 0`. Sharpness is certified by an explicit instance: the two-spike extremizer padded by two zero words attains `2 + 0 + 2 + 2 = 6 = (e+1)(ℓ−1)` at `e=1, ℓ=4`, with two windows charged their full corank at once — so no term of the cumulative law can be dropped.

### Bridge test (carried out, cheap version)
Against the project's existing subresultant/`W_can` route, which gives the hypothesis-free `#Bad ≤ (k+1)e + 1`: the Hankel bound `|T|` is strictly smaller whenever the top word's error weight is at most `e` (certified in Lean). Conclusion: the two mechanisms are **complementary, not equivalent** — the subresultant route is unconditional but grows like `ke`, the Hankel route is conditional on proximity and is the error weight itself. No reduction of one to the other was found, and none is claimed.

### Novelty boundary (explicitly respected)
No novelty is claimed for syndromes, Hankel/moment matrices, key equations, or Berlekamp–Massey/Padé structure — all classical for RS decoding. What is new here and formally verified is: the additivity of window coranks in the degree budget of a matrix polynomial determinant, with sharpness; the staircase proximity law with unequal supports; the certified strict improvement over the previously formalised common-support bound; the multi-word extremizer exclusion; and the two-word cash-out with its comparison against the subresultant route.

### Documentation
- `docs/HANKEL_CUMULATIVE_RANK_REPORT.md` — full report, including the explicit four-part answer to the value gate (regime of strict strength, phase vs. reproof, extremizer constraint, asymptotic scaling) and the bridge-test conclusion.
- `RESULTS.md` §97–§98 — summary in the established project style.

The Properties table has been reconciled: every theorem entry is marked proved, the one definition remains a definition.


# Summary of changes for run b04000ad-0c3e-48ae-9759-f12e13a4faa8
I continued the development from where the previous work stopped: the project built cleanly and contained no `sorry`, so I pushed the mathematics forward with a new, fully proved result set, and left the whole project building.

## New file: `RequestProject/Root/CodingTheory/HankelRankProfile.lean` (589 lines, no `sorry`, no new axioms)

The earlier work left the top-degree behaviour of the offset Hankel determinant as a binary alternative: its leading coefficient is the determinant of the moment matrix of the last word of the family, so that matrix is either singular (costing one degree) or not. This file replaces that by a graded statement, first at the level of an arbitrary matrix polynomial and then in the coding-theory setting.

**General linear algebra.** For `matPoly n ℓ M = ∑_{j<ℓ} X^j·M_j` of size `n`, a multilinear column expansion writes the determinant as a sum over choices of one coefficient matrix per column, the term of *deficiency* `q` having degree `n(ℓ−1) − q`. This yields a hypothesis-free vanishing criterion and two consequences:
- **leading corank**: `deg det + (n − rank M_{ℓ−1}) ≤ n(ℓ−1)` — the degree drops by the whole corank of the leading coefficient matrix, not by one;
- **span profile**: if the columns of the top `q+1` coefficient matrices fail to span `Fⁿ` for every `q < c`, then `deg det + c ≤ n(ℓ−1)`.

**Consequences for the budget law.** The offset Hankel matrix is exactly the matrix polynomial of the scalar moment matrices of the family, so the criteria transfer:
- graded budget law `#Bad + e·|Z| + ((e+1) − rank(moment matrix of the top word)) ≤ (e+1)(ℓ−1)`, with a fully graded form also carrying the witness-radius slack;
- the span-profile form `#Bad + e·|Z| + c ≤ (e+1)(ℓ−1)`;
- the corank of the top moment matrix is at most the defect `(e+1)(ℓ−1) − #Bad − e|Z|`;
- an extremizer has a top moment matrix of *full rank* `e+1` (quantitative strengthening of the earlier "determinant nonzero").

**Rank versus distance.** A word agreeing with a codeword off a set of size `m` has moment matrix of rank at most `m` — the rank of the `(e+1)×(e+1)` moment matrix is a lower bound for the distance to the code. Combined with the graded law this recovers the earlier single-word proximity gain `#Bad + e|Z| + (e−m+1) ≤ (e+1)(ℓ−1)` from a purely linear-algebraic hypothesis, so the gain now holds for any source of rank deficiency.

**Sharpness.** Padding an extremizer by a zero top word attains the graded bound with equality; this is certified on the explicit two-spike extremizer (`e = 1`, `ℓ = 3`), where the corank term contributes its maximal value `e+1`. No term of the graded law can be dropped.

## Verification and documentation
- The full project builds successfully (`8252` jobs, zero errors); the new module builds with zero warnings and contains no `sorry`.
- Every new theorem is listed in `RequestProject/Main.lean` with `#print axioms`, and each depends only on `propext`, `Classical.choice`, `Quot.sound`.
- Write-ups added: a new numbered section §96 in `RESULTS.md` and a standalone report `docs/HANKEL_RANK_PROFILE_REPORT.md`.
- The Properties table has been updated with the new definitions and theorems, all marked proved.
- All work is committed and pushed.


# Summary of changes for run cdcf4910-d2d1-4734-a02b-33bad1793437
## RESULT

The mission (accept `(e+1)(ℓ−1)` as sharp; classify equality, then stability, then exclusion) is delivered, with all four requested outcomes reached: an equality classification, a stability theorem, a new strict proximity consequence, and a certified barrier.

Two new Lean files, both fully proved:
- `RequestProject/Root/CodingTheory/HankelExtremal.lean` — mechanism, graded budget law, Gate 2 stability, Gate 1 classification.
- `RequestProject/Root/CodingTheory/HankelExtremalGates.lean` — Gate 3 proximity gains, leading coefficient, falsification target, bridge, exclusion.

**Graded budget law.** With `ρ(γ)` the least witness size of a challenge and `Z` the syndrome-zero locus:
`∑_{γ∈Bad∖Z}(e−ρ(γ)) + #(Bad∪Z) + e·|Z| ≤ deg D_{i₀} ≤ (e+1)(ℓ−1)`.
Uniform corollary: if every bad challenge is witnessed with `≤ e−c` errors, `(c+1)·#Bad ≤ (e+1)(ℓ−1)`.

**Gate 1 — equality classification.** `#Bad + e|Z| = (e+1)(ℓ−1)` forces `Z ⊆ Bad`; every bad challenge outside `Z` at full error weight `ρ(γ)=e`; `deg D_{i₀} = (e+1)(ℓ−1)`; and the complete split
`D_{i₀} = c·∏_{Bad∖Z}(X−γ)·∏_{Z}(X−γ)^{e+1}` — only multiplicities `1` and `e+1`, no other root. Moreover the top coefficient of `D_{i₀}` is the determinant of the scalar syndrome Hankel matrix of the last word, so extremality forces `f_{ℓ−1}` alone to be syndrome-nondegenerate of full Hankel rank, in particular at distance `> e` from the code.

**Gate 2 — stability.** With defect `δ = (e+1)(ℓ−1) − #Bad − e|Z|`: `D_{i₀} = extremalFactor·R` with `deg R ≤ δ`; total error-weight slack `≤ δ`; `#(Z∖Bad) ≤ δ`. Linear stability with constant one.

**Gate 3 — new proximity consequence.** If the top `s` words all agree with codewords off one common set of size `m ≤ e`, then `#Bad + e|Z| + (e−m+1)·s ≤ (e+1)(ℓ−1)` — strictly stronger exactly in the regime a proximity-gap argument needs.

**Gate 3 — exclusion.** Taking `s = ℓ−1` gives: an extremizer is never a rigid family. The extremal class is certified disjoint from the rigid phase (where the strictly better bound `#Bad ≤ e(ℓ−1)` holds and is itself sharp). No counting hypothesis, all `e`, all `|Z|`.

**Bridge.** All offset determinants of an extremizer are proportional, hence `deg gcd(D_{i₀},D_{i₁}) = (e+1)(ℓ−1)` for any two admissible offsets. Flatness of the offset-gcd hierarchy is a necessary condition for extremality — the extremal budget and the flat hierarchy are one phenomenon, a single degree-`(e+1)(ℓ−1)` polynomial dividing every offset determinant.

## STATUS

All statements proved in Lean, no `sorry`, no new axioms. The full project build completes with zero errors and every new declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

## MECHANISM

Unimodular annihilator column operations. For a witness set `T`, `|T| = m ≤ e`, the shifted annihilators `X^{t−m}·∏_{y∈T}(X−y)`, `m ≤ t ≤ e`, form an upper-triangular matrix of determinant 1, so `D_{i₀} = det(hankelShift · annCol)`. The annihilator kills the syndrome of the witnessed word, and this one computation yields both the multiplicity law (a challenge witnessed by `m` errors is a root of multiplicity `≥ e−m+1`) and the degree drop (if the witnessed words are at the top of the family, the transformed columns lose their leading coefficients).

## BARRIER

Extremizers are not unique: the two-spike family attains the bound with `Z = ∅` and a squarefree determinant, the collinear family attains it with `Z = Bad` and determinant `c·L^{e+1}`. Both multiplicity patterns permitted by the normal form occur, on families of opposite syndrome structure. The split factorisation is therefore the *minimal* common structure; no finer universal normal form exists, and the barrier is certified rather than worked around.

## NEXT MOVE

The classification reduces exclusion to a single-word condition. The concrete target is to rule out families whose last word has an invertible `(e+1)×(e+1)` moment matrix while the bad set has `(e+1)(ℓ−1)` elements all at full error weight, using RS-specific structure (the moment matrix of a word at distance exactly `e` is constrained by its error locator). A per-index version of the budget law, grading by the whole Hankel rank profile along the family rather than only at the top word, is the natural generalisation.

## Documentation

Write-up in `docs/HANKEL_EXTREMAL_REPORT.md`, plus a new numbered section §92 in `RESULTS.md` in the established style. The Properties table has been updated: all new theorems registered and marked proved, with the definitions they are stated in terms of registered as definitions.


# Summary of changes for run c8084b80-6061-4794-bc8d-8ea04ed326e3
**PRIORYTET PRZYJĘTY: A = teoria kodów / MCA.** Pracowałem wyłącznie w gałęzi Hankel/MCA; nie dotknąłem FFT/NTT, M31, teorii reprezentacji, Verusa/Rusta, K-teorii ani optymalizacji implementacyjnych, i nie zmieniłem żadnego wcześniej udowodnionego twierdzenia.

## PIERWSZE PYTANIE — WERDYKT: **KILL**

Pytanie: czy dodatkowe dostępne przesunięcia syndromu wymuszają uniwersalną redukcję `deg gcd(H_e^{(0)},…,H_e^{(r)})`? **Nie.** Istnieje próg niezależny od redundancji, i to na maksymalnym możliwym poziomie.

Nowy plik `RequestProject/Root/CodingTheory/HankelRedundancyBarrier.lean` (bez `sorry`, bez nowych aksjomatów), raport `docs/HANKEL_REDUNDANCY_BARRIER_REPORT.md`, wpis §91 w `RESULTS.md`, rekonesans `analysis/hankel_redundancy_barrier_probe.py`.

**Mechanizm (ogólny, bez założeń).** Każdy wpis każdej przesuniętej macierzy Hankela to jeden z tych samych wielomianów momentowych `M_r(X)=∑_j A_r(f_j)X^j`; przesunięcie tylko je przeindeksowuje. Stąd: jeśli `P ∣ M_r` dla wszystkich `r`, to `P^{e+1}` dzieli **każdy** wyznacznik przesunięty (`pow_dvd_shiftDet_of_dvd_momPoly`). Wewnętrznie pierwiastki takiego wspólnego czynnika to dokładnie *locus zerowego syndromu* `Z` — wyzwania, dla których generowane słowo ma zerowe momenty — więc bez żadnych hipotez `(∏_{γ∈Z}(X−γ))^{e+1}` dzieli każdy wyznacznik (`prod_synZero_pow_dvd_shiftDet`), a każdy gcd po dowolnym skończonym zbiorze przesunięć ma stopień `≥ (e+1)|Z|` (`le_natDegree_of_isGcd_shiftDet`).

**Skalowalna przeszkoda (sklasyfikowana).** Rodziny współliniowe `f_j = λ_j·g` (rangi jeden): każdy wyznacznik przesunięty to skalar razy `L^{e+1}`, `L=∑_j λ_j X^j` (`shiftDet_famScaled`), więc dla **każdej** pary przesunięć `deg gcd = (e+1)(ℓ−1)` — dokładnie apriorycznie maksymalny stopień pojedynczego wyznacznika (`natDegree_gcd_shiftDet_famScaled`), podczas gdy zbiór zły to dokładnie pierwiastki `L`, czyli co najwyżej `ℓ−1` elementów (`badSetG_famScaled_eq`, `card_badSetG_famScaled_le`). Konkretna niezdegenerowana instancja (`e=1`, słowo dwupunktowe): `natDegree_gcd_shiftDet_twoSpike`. To druga, mechanicznie różna bariera wobec tej z `RedundancyInvariance.lean`: tam gcd jest płaski, bo oszacowanie jest ciasne; tu jest płaski, bo wyznacznik niesie `(e+1)`-krotny *zmarnowany* stopień.

## CO Z TEGO ZOSTAJE — MOCNIEJSZE TWIERDZENIE

Bariera jest ilościowa, więc daje się **odjąć**: elementy `Z` są pierwiastkami krotności `≥ e+1`, złe wyzwania tylko krotności `1`, a układy pierwiastków są względnie pierwsze, więc wkłady się sumują:

- `#Bad + e·|Z| ≤ deg D_{i₀}` oraz `#Bad + e·|Z| ≤ (e+1)(ℓ−1)` (`card_badSetG_add_mul_card_synZero_le_shiftDet`, `card_badSetG_add_mul_card_synZero_le`);
- `#Bad + e·|Z| ≤ deg gcd(D_{i₀},D_{i₁})` (`card_badSetG_add_mul_card_synZero_le_gcd`).

To ściśle wzmacnia dotychczasowe `card_badSetG_le_hankel_top` i `card_badSetG_le_gcd` dla każdej rodziny z niepustym `Z`, i jest **dokładnie ostre** na rodzinie barierowej (`card_badSetG_add_mul_card_synZero_famScaled_eq`). W drugą stronę: rodzina osiągająca maksimum `#Bad=(e+1)(ℓ−1)` musi mieć `Z=∅` (`synZeroSet_eq_empty_of_card_badSetG_eq`) — maksymalne zbiory złe i degeneracja syndromu wykluczają się.

## STAN GAŁĘZI I NASTĘPNY KROK

Droga gcd/redundancji jest zamknięta z dwóch stron (bariera ciasności + bariera zmarnowanego stopnia), a jedyna informacja, jaką z niej wyciskam, to poprawka `−e|Z|`. Trzeci wariant z misji — ograniczenie wymiarowe/Grassmannowskie — był już wcześniej **obalony** w stanie certyfikowanym (`SupportPhaseSharpness.card_badSetG_famPlane_gr_refutation`, `exists_pencil_card_badSetG_eq_succ`: przy arności 2 zachodzi `#Bad = e+1` dla każdego `e`, wbrew przewidywaniu `≤ 3`). Stąd stała `(e+1)(ℓ−1)` nie da się obniżyć w pełnej ogólności, a żywy front to podział fazowy: gałąź sztywna (`#Bad ≤ e(ℓ−1)`), klasa „pozorna” i nowa klasa syndromowo-zdegenerowana `Z≠∅`, gdzie obowiązuje mocniejsze `#Bad ≤ (e+1)(ℓ−1) − e|Z|`.

**Weryfikacja.** Pełny `lake build` zielony (8243 zadania, 0 błędów), zero `sorry`/`admit`, audyt `#print axioms` w `RequestProject/Main.lean` dla wszystkich 14 nowych twierdzeń pokazuje wyłącznie `propext, Classical.choice, Quot.sound`. Rekonesans numeryczny (eksploracyjny, nie certyfikat) potwierdza obraz: dla rodzin współliniowych łańcuch stopni gcd jest stały i równy `(e+1)(ℓ−1)` przy 4 przesunięciach, dla rodzin generycznych spada do 0 już po jednym dodatkowym przesunięciu — czyli redundancja pomaga generycznie, zawodzi jedynie prawo *uniwersalne*. Wszystko zacommitowane i wypchnięte.

# Summary of changes for run 19fe49d9-e0b9-4133-a077-4a30bb3a34f8
Sesja sprawozdawcza — nie zmieniałem żadnego dowodu. Pełny raport: `docs/RAPORT_STANU_2026-08-30.md` (commit wypchnięty).

**Stan zweryfikowany dziś (nie przepisany z dokumentów):** 216 plików Lean, 66 599 linii, 2 559 twierdzeń/lematów, 700 definicji. **Zero `sorry`, zero `axiom`.** Pełny `lake build` zielony (8 242 zadania, 0 błędów, 29 ostrzeżeń typu „nieużyty argument simp"). Audyt: 1 172 bloki `#print axioms` w `RequestProject/Main.lean`, wszystkie raportują wyłącznie `propext`, `Classical.choice`, `Quot.sound` — bez `native_decide`.

**Co jest zrobione.** Krok 1 (M31, pierwszość jądrem, cykliczność `F_p^*`, `p−1 = 2·3²·7·11·31·151·331`, a stąd udowodniony brak pierwiastków stopnia `2^k`, `k ≥ 2` — czyli brak radix-2 NTT w ciele bazowym). Krok 2 (odwracalność DFT, splot, `F[C_n] ≃ₐ Fⁿ`, równoważność `Rep F C_n ≌ ModuleCat`, rozkład izotypowy; brakuje tylko wersji `NatIso`). Krok 3 (Cooley–Tukey, split-radix, Good–Thomas, Rader, bit-reversal, iteracyjny FFT in-place z niezmiennikami pętli, circle FFT nad M31 do `2^29`, warstwa maszynowa `u32/u64` z dowodem braku przepełnienia; pełna teoria biliniowa: Alder–Strassen, Winograd, dokładna złożoność splotu cyklicznego dla każdej długości, Karatsuba, Toom–Cook). Efekt „mersenne'owski" istnieje, ale skromniejszy niż zakładała hipoteza: darmowe twiddle w podgrupie `⟨2⟩` (rotacje bitowe) i 31-punktowy DFT bez mnożeń.

**Gdzie problem.** (1) Kroki 4–5 (K-teoria, topologia) nie dały wartości — Mathlib nie ma użytecznej K-teorii, `Spec F_p` to punkt, a hipoteza „ukrytych symetrii" nie doczekała się rozstrzygalnego sformułowania; ciężar realnie przeniósł się na teorię reprezentacji i algebrę biliniową. (2) Krok 6 jest zablokowany: w środowisku nie ma Rusta, cargo ani Verusa, więc 577 linii kontraktów pozostaje niezweryfikowanych, benchmarków nie wykonano żadnych i żadne zdanie „szybciej niż SOTA" nie jest dziś uprawnione. (3) Modele kosztu liczą operacje ciała, nie instrukcje/cache/SIMD. (4) Brak porównania kosztów NTT nad `F_{p²}` vs circle FFT — a to jest decyzja architektoniczna o realnej wartości. (5) Projekt prowadzi dwa programy naraz: 145 z 216 plików to dziś teoria kodów (proximity gaps, MCA, folded RS, FRI) — materiał mocny, ale to nie jest cel z pierwotnego zlecenia. (6) Iteracja jest wolna: pełny build ~1 h, pojedyncze pliki kernel-heavy do 975 s.

**Czego potrzebuję, by przyspieszyć (wg zwrotu).** A. Jedna decyzja o priorytecie: tor produktowy (Verus + benchmarki), tor teorii kodów (domknięcie MCA do pojemności), albo tor FFT (porównanie `F_{p²}` vs circle, radix-4/8, charakteryzacja darmowych twiddle). B. Rust + Verus + Z3 w środowisku. C. Operacyjna definicja SOTA: biblioteka odniesienia, rozmiar, CPU, metryka. D. Wybór modelu kosztu, który ma być formalnie optymalizowany. E. PDF-y prac źródłowych w repo (brak ich kosztował kilka sesji korekt i obaleń). F. Zgoda na jednorazową inwestycję w skrócenie czasu buildu. G. Zgoda na domykanie jednego celu zamiast otwierania nowego wątku co sesję.

**Moja rekomendacja:** tor FFT w kolejności — porównanie NTT nad `F_{p²}` z circle FFT, charakteryzacja darmowych twiddle, radix-4/8 — a dopiero po udostępnieniu Verusa przeniesienie tego do kontraktów i benchmark; gałąź teorii kodów zamrozić w obecnym, spójnym stanie.

# Summary of changes for run d25a5802-f4f1-42fa-999e-493dad03cfe9
Worked the Hankel-phase mission: reused the existing syndrome/moment infrastructure, falsified cheaply first, then formalised only the decisive facts. Two new files, `RequestProject/Root/CodingTheory/HankelPhase.lean` and `RequestProject/Root/CodingTheory/HankelPhaseSharpness.lean`, both `sorry`-free, in a clean `lake build`, with an axiom audit in `RequestProject/Main.lean` showing only `propext, Classical.choice, Quot.sound`. Full write-up in `docs/HANKEL_PHASE_REPORT.md`; exploratory scripts in `analysis/hankel_phase_probe.py` and `analysis/hankel_sharpness_design.py`.

FINAL REPORT

DET COMPATIBILITY — the determinants are not independent, and this is the main quantitative gain. A witness of size m ≤ e yields the monic degree-e annihilator X^(e−m)·Z_T (`syndrome_relation_shift`), so it kills the single largest determinant too. Hence, in the regime k+2e+1 ≤ |D| and under the single hypothesis det(H_e) ≠ 0: #Bad ≤ (e+1)(ℓ−1) (`card_badSetG_le_hankel_top`) — a factor (e+2)/2 better than the previous (ℓ−1)(e+1)(e+2)/2, under one of its e+1 hypotheses instead of all. The two previously certified instances improve to #Bad ≤ 2 and #Bad ≤ 4.

SHARPNESS — the improved bound is attained. `card_badSetG_famSharp_eq`: an explicit family built from two indicator words has exactly 2 = (e+1)(ℓ−1) bad challenges at ℓ=2, e=1 on every domain with k+3 ≤ |D|, with non-vanishing determinant. So the old degree-sum value 3 is not attained. Exact (uncertified) search attains the new bound also at (ℓ,e) = (3,1),(4,1),(2,2) and fails at (2,3),(2,4), matching a Grassmannian dimension count — evidence for a second, dimension-limited phase at larger e.

HANKEL RANK STRUCTURE — syndrome dictionary: for a word agreeing with a codeword off an error set T, the moments in the window are a power sum ∑_{y∈T} ε_y·y^r (`mom_eq_power_sum_of_isCloseOn`), the elementary case being that an indicator word has geometric moments with nonzero initial term. Equivalently in recurrence form (`badG_syndrome_recurrence`): MCA badness ⇒ syndrome linear complexity ≤ e.

DEEPER HIERARCHY — yes, indexed by redundancy, as a gcd rather than a new constant: each available offset determinant kills every bad challenge, so #Bad ≤ deg gcd of two offsets (`card_badSetG_le_gcd`) and coprime offsets force Bad = ∅ (`badSetG_eq_empty_of_coprime`). Exact search with one unit of redundancy found gcd degree 0 and empty bad sets throughout.

EXCEPTIONAL CLASS — classified: H_m ≡ 0 iff the challenge-moment sequence has a nonzero polynomial annihilator of length m+1, i.e. generic syndrome Hankel rank ≤ m (`det_hankelShift_eq_zero_iff_kernel`). Combined into the hypothesis-free dichotomy `card_badSetG_le_or_hankel_rank`: #Bad ≤ (e+1)(ℓ−1) or the challenge Hankel matrix has rank ≤ e. Designed families that appear to beat the bound all lie in this class.

PHASE DIAGRAM — `card_badSetG_le_phase`: in the collapse regime the certified value is min((e+1)(ℓ−1), (ℓ−1)·C(|D|,e)); the region table (which mechanism is optimal, and where sharpness is known) is in the report. The new intermediate phase is the redundancy one.

LEAN STATUS — clean build, no sorry/admit, no new axioms.

NEXT SINGLE MOVE (stated, not performed) — turn the Grassmannian count B·e ≤ dim Gr(2,2e+1) into a theorem, bounding #Bad geometrically for ℓ=2, e ≥ 3 and opening the second phase.

# Summary of changes for run 7a5b46da-9c94-4388-9257-b251a35180b0
## Part 1 — Arity-factor sharpness gate (the mission as stated)

This was resolved and is fully certified in `RequestProject/Root/CodingTheory/ArityFactorSharpness.lean`, with a write-up in `docs/ARITY_FACTOR_SHARPNESS_REPORT.md`.

- **SMALL-CASE VERDICT:** exact reconnaissance at ℓ=3 (e=1,2) and ℓ=4 over fields where q is not the bottleneck produces candidates exceeding C(N,e); two of them are now Lean theorems: over ZMod 13 with D={1,3,10,12}, k=2, e=1, ℓ=3 gives exactly #Bad = 8 = 2·C(4,1); with D={1,5,8,12} and ℓ=4, exactly #Bad = 12 = 3·C(4,1).
- **FULL-FIBRE CONSTRUCTION:** found and formalised (`famArity`): f₀ = x^{N−e−1}, f_{ℓ−1} = (−1)^{e+1}x^{N−1}, other components 0. Each rejecting witness T (an e-subset) has challenge polynomial P_T(γ) = 1 − (∏_{t∈T} t)·γ^{ℓ−1}, of degree exactly ℓ−1, whose ℓ−1 roots are distinct, lie in F, and are all bad.
- **GLOBAL COMPATIBILITY:** no obstruction exists. The fibres over distinct witnesses are disjoint and simultaneously full, so per-witness capacity is globally attainable.
- **TRUE ARITY FACTOR:** ℓ−1 — Gate 4 option **A (full arity sharpness)**.
- **UPPER BOUND:** the existing window-free bound #Bad ≤ (ℓ−1)·C(N,e).
- **LOWER WITNESS:** `card_badSetG_famArity_eq` : max_f #Bad = (ℓ−1)·C(N,e) for every ℓ ≥ 2, e ≥ 1, plus the exact e = 1 form and the two concrete instances.
- **REALIZABILITY CONDITIONS (exact):** (i) the top e elementary symmetric functions of D vanish; (ii) the e-subsets of D have distinct products; (iii) each fibre is full, i.e. (ℓ−1) | q−1 and D ⊆ (F*)^{ℓ−1}. Together these force q ≥ (ℓ−1)·C(N,e) + 1 — the hidden field-size assumption, now stated explicitly.
- **SUCCESS: S4.**

## Part 2 — Follow-up work completed in this session: the syndrome–Hankel collapse

New file `RequestProject/Root/CodingTheory/SyndromeHankelCollapse.lean` (688 lines), report `docs/SYNDROME_HANKEL_COLLAPSE_REPORT.md`. Because the factor ℓ−1 and the count C(N,e) are both attained at k = N−e−1, no incidence argument can improve the bound there; this file identifies a different mechanism that takes over strictly below that dimension.

Define the moments A_r(u) = coeff_{N−1}((X^r·P_u) mod Z_D), where P_u interpolates u over D and Z_D is the vanishing polynomial of D, and the challenge polynomials M_r(γ) = ∑_j γ^j A_r(f_j) (degree ≤ ℓ−1).

Proved:
- **Syndrome relation**: if u agrees with a polynomial of degree < k off a set T of size m and i+m+k+1 ≤ N, then ∑_{s≤m} (Z_T).coeff s · A_{s+i}(u) = 0.
- **Collapse**: if k + 2e + 1 ≤ N and none of the e+1 Hankel determinants det(M_{i+s})_{i,s≤m} vanishes identically, then #Bad ≤ ∑_{m=0}^{e}(m+1)(ℓ−1), equivalently 2·#Bad ≤ (ℓ−1)(e+1)(e+2). The bound involves neither the domain size nor the field size.
- **Dichotomy with no hypothesis**: below the threshold, either that bound holds or some determinant is identically zero; and once |F| > (m+1)(ℓ−1) the latter is equivalent to every challenge in F being a root — an explicit, checkable exceptional class.
- **Two certified non-degenerate instances**, so the hypothesis is not vacuous: the top monomial pair (arity 2, e = 1) has #Bad ≤ 3 on every domain; and the top monomial triple at arity 3, e = 1, k = |D|−3 — **strictly outside** the separation window k+4 ≤ |D|, where the only prior bound was the incidence bound 2|D| — has #Bad ≤ 6 on every domain with ∑_{x∈D} x ≠ 0. There the m = 1 determinant equals C(A_{|D|+1} − a²) − C a·X with a = ∑_{x∈D} x, so the first power sum is exactly what governs non-degeneracy.

**LEAN STATUS:** the whole project builds (`lake build`, 8227 jobs, no errors); both files are free of `sorry` and every listed theorem depends only on `propext`, `Classical.choice`, `Quot.sound` (audited by `#print axioms` blocks in `RequestProject/Main.lean`). Supporting brute-force scripts live in `analysis/` and are exploratory only — the theorems are the verified content.

**NEXT SINGLE MOVE (not performed):** decide whether the collapse bound (ℓ−1)(e+1)(e+2)/2 is itself sharp, by searching for a family whose e+1 Hankel determinants have simultaneously full, disjoint root sets — the largest bad set observed inside the regime so far is 2.

All work is committed and pushed.

# Summary of changes for run 5cc558c2-2773-4d7b-b2a0-db01ff8f6e49
Sparse-domain / circuit gate completed. Full `lake build` is green (8225 jobs), no `sorry`, no `admit`, no new axioms; the axiom audit in `RequestProject/Main.lean` reports only `[propext, Classical.choice, Quot.sound]` (some statements need even fewer). No previously proved result was modified.

**A — SPARSE SATURATION: RULED OUT (bounded arity).** The saturating family needs `D = F` in exactly one place: the omitted position `γ⁻¹` must lie in the domain, so the map (bad challenge) ↦ (omitted position) is injective into `D`, not `F`. This is now a theorem in the strongest available form: for *every* arity-`ℓ` family on `D`, `#Bad · C(T−1,a−1) ≤ C(N,a)·(ℓ−1)` with `T = max(N−e, k+1)`, `k+1 ≤ a ≤ T` (`card_badSetG_le_circuit`) — a bound in which `q = |F|` never appears. Hence `#Bad < q` and `ε_mca ≤ (ℓ−1)C(N,e)/q → 0` on sparse domains.

**B — CIRCUIT CEILING.** `B(N,k,e,a) = C(N,a)/C(T−1,a−1) ≈ N^{e+1}/(a(N−a)^e)`, minimised near `a = N/(e+1)` at `≈ 2.72(e+1)`; it degrades to `≈ (N/(e+1))^e` when `k → N` (constraint `a ≥ k+1`). Numerics in `analysis/circuit_ceiling_scan.py`.

**C — INFORMATION LOSS.** The incidence is: left = bad challenges, right = `a`-subsets, left degree `≥ C(T−1,a−1)`, right degree `≤ ℓ−1`. The looseness is entirely on the right-hand *universe* (all `C(N,a)` subsets allowed), not on the multiplicity.

**D — THINNING: NOT NEEDED.** The bound is exactly attained, so thinning cannot gain.

**E — CHALLENGE MULTIPLICITY: proved.** `genCloseOn_of_forall_isCloseOn` (via `exists_lagrange_coeffs`): if `ℓ` distinct challenges are accepted on the same set, the whole generated family is close there — i.e. a rejecting subset is accepted by at most `ℓ−1` challenges. This is the arity-`ℓ` analogue of the line lemma.

**F — NEW BOUND + SHARPNESS.** `#Bad ≤ (ℓ−1)C(N,k+1)`, and `#Bad ≤ (ℓ−1)C(N,e)` when `k+1 ≤ N−e`; at `e = 1`, `#Bad ≤ (ℓ−1)N` for every `k ≤ N−2`. New this session: `RequestProject/Root/CodingTheory/SparseDomainSharpness.lean` proves the matching lower bound at every budget. The monomial pair `f₀ x = x^{N−e−1}`, `f₁ x = x^{N−e}` with challenge `γ_A = −(∑_{x∈A}x)⁻¹` for each `(N−e)`-subset `A` gives `#Bad = C(N,e)` **exactly** (`card_badSetG_famSparse_eq`), under the hypothesis that the `(N−e)`-subsets have distinct nonzero sums; at `e = 1` this reduces to `∑D ∉ D` and reads `#Bad = |D|` (`card_badSetG_famSparse_eq_of_e_one`), with the concrete instance `D = {1,2,3} ⊂ ZMod 11`, `#Bad = 3` (`card_badSetG_sparse_zmod11`).

**G — REGIME.** `k + (ℓ+1)e > N` (outside the old window, `famSparse_outside_window`) together with `#Bad = o(q)` on the scalable family `k = N−e−1`, any `N = o(q)`. The controlling quantity is the *domain size*, not the field size.

**DOMINANCE.** Incomparable with the sharp in-window bound by design; equal to the existing line bound at `ℓ = 2` (recorded honestly as no gain there); strictly better than the trivial `#Bad ≤ q` whenever `(ℓ−1)C(N,e) < q`; consistent with the `D = F` saturation family, where `card_badSetG_famSparse_eq` sits alongside the sandwich `q−1 ≤ #Bad ≤ q` (`card_badSetG_satFam_sandwich`).

**ADVERSARIAL TESTS.** Boundary `k = N−2` (attained), saturation `D = F` (no contradiction, no slack), degenerate `ℓ = 1`, `e = 0`, `k ≈ N`; exact reconnaissance in `analysis/sparse_domain_saturation_probe.py` (e = 1) and the new `analysis/sparse_domain_general_e_probe.py` (ℓ = 2, e ∈ {2,3}, N ∈ {5,6}, q ≤ 23: the maximum climbs with `q` only until it hits `C(N,e)` and then stops). These Python probes are reconnaissance, not certification; the certification is the Lean theorem.

**SUCCESS LEVEL: S2** — a machine-checked regime outside the old window, with the added fact that the bound is exactly tight at `ℓ = 2` for every budget `e`, and is the first window-free bound at arity `ℓ ≥ 3`. Not S3 at `ℓ = 2`, not S4.

**MECHANISM (one sentence).** A rejecting subset is accepted by at most `ℓ−1` challenges (Lagrange/Vandermonde capacity) while each bad challenge owns `C(T−1,a−1)` rejecting subsets, so `#Bad` is bounded by a purely domain-combinatorial ratio in which the field size never appears.

**NEXT SINGLE RESEARCH MOVE (not performed).** Decide whether the factor `ℓ−1` in `#Bad ≤ (ℓ−1)C(N,e)` is attained by a scalable family for `ℓ ≥ 3` — construct and certify a family whose challenge-to-witness map has degree `ℓ−1` with all fibres full — or prove that the true maximum is `C(N,e)` for every arity.

Documentation updated: full report in `docs/SPARSE_DOMAIN_CIRCUIT_REPORT.md`, entry §86 in `RESULTS.md`, `INDEX.md` regenerated. All work is committed and pushed.

# Summary of changes for run 5af01417-dc1f-45fd-a1c1-20caa5f6c0b7
MISSION — GLOBAL AMBIGUITY GATE. Executed the gated funnel; the cheap falsification gate fired, so per the decision tree no further mechanism was pursued. Everything below is machine-checked in `RequestProject/Root/CodingTheory/AmbiguitySaturation.lean`; full `lake build` succeeds (8223 jobs), no `sorry`/`admit`, no new axioms, axiom audit exactly `[propext, Classical.choice, Quot.sound]` via `#print axioms` in `RequestProject/Main.lean`. Nothing frozen was modified. Full report: `docs/AMBIGUITY_SATURATION_REPORT.md`; summary row in `RESULTS.md` §85; exact independent computation in `analysis/ambiguity_saturation_check.py` (+ output file).

G0 CERTIFICATE: PASS (with the obstruction made explicit). Unfolding the decomposition, `A` is any set such that every bad challenge either lies in `A` or has a witness set `S`, `|D| ≤ |S|+e`, with `¬GenCloseOn` and relation value ≡ 0 on `S`. The smallest such set is now a named object, `ambiguousSet ℓ k e f q` (`ambiguousSet_split`, `ambiguousSet_subset_of_split`). Minimal certificate: for every witness set of `γ` the local interpolant differs from the globally forced combination `∑_j γ^j q_j`, i.e. a nonzero discrepancy — an existential over witness sets, not a globally countable object.

G1 SATURATION: KILL. Two machine-checked facts. (i) Sandwich: `card_sub_sharp_le_card_of_split` gives `|A| ≥ #Bad − (ℓ−1)(e+1)` for every admissible `A`, and `card_ambiguousSet_le_card_badSetG` gives `|A| ≤ #Bad`; so global control of the ambiguity is, up to the additive sharp term, the same problem as control of `#Bad` — the decomposition transports no information by itself. (ii) Scalable saturating family, over an arbitrary finite field with `4 ≤ |F|`: `D = F`, `ℓ = 2`, `k = |F|−2`, `e = 1`, `f₀ x = x^{|F|−2}`, `f₁ x = x^{|F|−1}`. These parameters miss the window by exactly one position (`satFam_outside_window`: `k+(ℓ+1)e = |F|+1 > |F| = |D|`), and every nonzero challenge is bad (`isBadG_satFam`), so `#Bad ≥ |F|−1` (`card_badSetG_satFam_ge`) against the sharp term `2`. Hence for every candidate codeword family and every admissible `A`: `|A| ≥ |F|−3` (`card_ambiguous_satFam_ge`, `card_ambiguousSet_satFam_ge`), and over prime fields `|A| ≥ p−3` (`card_ambiguousSet_satFam_zmod_ge`). Mechanism: modulo the codimension-2 code the combination `x^{q−2}+γx^{q−1}` has top pair `(γ,1)`, exactly `γ` times that of the vanishing polynomial of `F∖{γ^{-1}}`, so it agrees with a codeword off the single position `γ^{-1}` — a different position for each challenge — while `f₀` agrees with no codeword on `|F|−1` positions (reuses the existing `not_isCloseOn_powWord`). Non-vacuity is pinned by a concrete instance: over `ZMod 5`, `#Bad ≥ 4` and `|A| ≥ 2`, matching the brute-force computation (bad set `= F∖{0}`, `#Bad = p−1`, for `p = 5,7,11,13`).

G2 BEST MECHANISM: NONE (not executed). The gate stops on falsification, and by the sandwich any global bound on `|A|` is a bound on `#Bad` minus a constant, so it could not beat the already-proved window-free circuit bound, while on the witness family every such bound must exceed `|F|−3`.

G3 BOUND: none beyond `|A| ≤ #Bad`; and `|A| ≥ |F|−3` on an explicit scalable family one position outside the window. G4 PARAMETER GAIN: NO-GAIN — the hybrid `#Bad ≤ (ℓ−1)(e+1)+B_A` degenerates to the trivial `#Bad ≤ |F|` there. G5 GENERALISATION: NOT-JUSTIFIED.

VERDICT: G4 / BARRIER — the ambiguity decomposition cannot by itself cross the gap.

NEXT SINGLE MOVE (not performed): drop the additive `A`-decomposition and attack `#Bad` directly outside the window through the witness-set charging already formalised (`card_badSet_le_circuit`), asking whether the charging family can be thinned when `|D| ≪ |F|`, a regime the saturating family (which needs `|D| = |F|`) does not reach.

New declarations are listed in the Properties table; no earlier results were changed.

# Summary of changes for run 6c392503-7731-4fa9-93da-49e8ccf5f6b5
MISSION REPORT (full version: `docs/AMBIGUITY_BARRIER_REPORT.md`). The frozen sharp theorem was not touched; three new modules were added and the whole project builds (`lake build`, 8222 jobs), sorry-free, axioms exactly `[propext, Classical.choice, Quot.sound]`, all audited by `#print axioms` in `RequestProject/Main.lean`.

LITERATURE COLLISION — no BCHKS/BCGM document is present in the project, so the gate was kept minimal and honest: the only exact datum available is the Theorem-4.6-shaped exceptional-set formula quoted in the request. It is recorded as `BCHKSList.bchks46Bound` and evaluated at the rational point ρ = 1/4, m = 1 (√ρ = 1/2), γ = e/n, M = ℓ−1: machine-checked, |E| ≤ M((81/2+3γ)n+3) and 40·M(e+1) ≤ that bound whenever e+1 ≤ n. So at that point it is of order M·n and ≥ 40× larger than (ℓ−1)(e+1), while its domain (Johnson-type) strictly contains our window — neither subsumes the other. BCGM: text unavailable, unresolved, no claim made.

FIRST BROKEN STEP — exactly one step of the sharp proof uses the window: the identification of a bad challenge's local interpolant with the globally forced combination ∑_j γ^j q_j, which needs |S_γ ∩ T| ≥ k. Equivalently: the discrepancy Δ_γ = p_γ − ∑_j γ^j q_j must vanish. Everything else (Lagrange inversion to a common family, the defect bound, the degree-(ℓ−1) root bound, the bipartite count B(M−e) ≤ zM) is window-free — now a theorem: `card_le_sharp_of_rootWitness` derives #Bad ≤ (ℓ−1)(e+1) from vanishing relation values alone, with no hypothesis relating k, e, |D|.

REPLACEMENT INVARIANT — the deviation (positions of the witness set where the relation value is nonzero). Machine-checked: `card_badSetG_le_of_bounded_deviation` (#Bad ≤ (ℓ−1)(e+a+1) for deviation ≤ a; with L = a+1 the case L = 1 recovers z(e+1)), `card_badSetG_le_sharp_add_card_ambiguous` (window-free #Bad ≤ (ℓ−1)(e+1) + |A|), `card_badSetG_le_sharp_of_bounded_deviation`.

BARRIER (decisive) — `deviation_eq_empty_or_card_ge`: a deviation is either empty or of size ≥ |D| − e − k + 1; since the deviation lies inside the defect (≤ ℓe), a nonzero deviation forces the exact negation of the window. The ambiguity parameter is binary — 0 or huge — so no finite-ambiguity relaxation of uniqueness can enlarge the regime. And list size is the wrong invariant: `not_forall_card_badSetG_le_sharp_of_unique_decoding` shows over ZMod 5, D = {0,1,2,3}, k = 2, e = 1, ℓ = 2 the radius is inside the unique-decoding radius (interpolant unique, L = 1, proved by `unique_interpolant_of_two_radius`) yet #Bad = 4 > 2 = (ℓ−1)(e+1).

REUSED LEMMAS — genComb/gen_closure/commonAgreement/card_fiber_le, the agreement-identification lemma, both bipartite-incidence lemmas, and the existing ZMod 5 gap witness (transported to the arity-2 generator by `badSetG_two_eq_badSet`). No new framework, no refactoring.

RESULT — C (structural barrier) with a partial B (the incidence law now proved without the uniqueness step, plus the ambiguity-tolerant and decomposition forms). No A: no theorem on a strictly larger radius window, and the gap theorem shows precisely why this route cannot yield one.

NEXT SINGLE MOVE (stated only, not performed) — bound |A|, the number of ambiguous challenges in the window-free decomposition, by a list-decoding argument on the challenge variable, instead of weakening the per-challenge uniqueness step again.

# Summary of changes for run bf1ea82a-70b0-4126-a105-4c723c118771
## LEAN

**`Root.CodingTheory.PolyGen.card_badSetG_le_sharp`** (in `RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean`)

hypotheses `1 ≤ k`, `k + (ℓ+1)·e ≤ |D|`, `f : ℕ → ↥D → F`; conclusion `#(badSetG ℓ k e f) ≤ (ℓ−1)·(e+1)`, for the unchanged "same `S`" bad-set definition. Axioms: `[propext, Classical.choice, Quot.sound]`. Full `lake build` succeeds; no `sorry`, no `admit`, no new axioms; `#print axioms` added for every new declaration in `RequestProject/Main.lean`. This replaces the previous machine-checked constant `max(ℓ−1, (ℓ−1)ℓe)` on the same domain (factor `ℓe/(e+1)`), with `epsMCAG_le_sharp : ε_mca ≤ (ℓ−1)(e+1)/|F|`.

New/changed files: `BipartiteIncidence.lean` (counting core), `PolynomialGeneratorSharpness.lean` (lower bound), sharp-numerator section in `WHIRComparison.lean`, report `docs/MCA_CORE_MAP.md`, regenerated `INDEX.md`. No unrelated file was refactored.

## PROOF CORE

`T` = agreement set of the common family forced by ℓ bad challenges, `M = |D∖T|`. (1) `x ∉ T ⟹ R_x ≠ 0`, `deg R_x < ℓ`, so at most ℓ−1 roots. (2) For a bad `γ` the interpolant is forced to be `∑ γ^j q_j` on all of `D`, so `R_x(γ)=0` at **every** `x ∈ S_γ`, hence `|S_γ∖T| ≥ M−e`. (3) Double count: `#Bad·(M−e) ≤ (ℓ−1)·M`. (4) `M > e ⟹ M ≥ e+1 ⟹ #Bad ≤ (ℓ−1)(e+1)` by cross-multiplication (no division). (5) `M ≤ e`: charging bound `#Bad ≤ (ℓ−1)M ≤ (ℓ−1)e`. (6) fewer than ℓ bad challenges: `#Bad ≤ ℓ−1`. All branches are in the Lean proof.

## W1

**W1-PROVED** — symbolic *and* machine-checked. `exists_card_badSetG_ge_sharp` builds the family explicitly (e+1 marked positions carrying monic degree-(ℓ−1) polynomials with pairwise disjoint root sets) under `1 ≤ k`, `1 ≤ ℓ`, `k+e+1 ≤ |D|`, `(e+1)(ℓ−1) ≤ |F|`, `ℓ ≤ |F|`; with the upper bound, `exists_card_badSetG_eq_sharp` gives the exact maximum `max_f #Bad = (ℓ−1)(e+1)`.

## COLLISION

P1 (BCHKS Thm 4.1): event strictly different — proximity of the combined word versus the same-set MCA failure; our theorem does **not** follow immediately, the exact obstruction being the global common agreement set `A` versus the per-challenge witness set `S_γ`. The constants coincide numerically and the extremal family attains both thresholds. P2 (Thm 4.6): same event pointwise under `D=L, M=ℓ−1, γ=e/N, |F| ≥ ℓ`, but its domain (Johnson) strictly contains ours (`δ ≤ (1−ρ)/(ℓ+1)`), and no bound of it in our regime was supplied, so constants are not compared. BCGM: generality over generators/codes not claimable. Yuan–Zhu: not reproduced.

## VERDICT

**D5 — LITERATURE INSUFFICIENT** for a novelty classification.

---

SHARP BOUND: PROVED — `#Bad ≤ (ℓ−1)(e+1)`, machine-checked, axiom-clean
WEAKEST HYPOTHESES: `1 ≤ k` (used only by the codeword-separation lemma) and `k + |D∖T| + e ≤ |D|`; the closed form `k+(ℓ+1)e ≤ |D|` is only its instance at the a priori `|D∖T| ≤ ℓe`; the common family needs no window at all
INCIDENCE CORE: `|L|·a ≤ |R|·b` with `(a,b) = (M−e, ℓ−1)`, plus `B(M−e) ≤ M·z, e<M ⟹ B ≤ z(e+1)`
GENERATOR INPUT: reconstruction number `r = ℓ`, zero capacity `z = ℓ−1`
CODE INPUT: one minimum-distance separation inequality (`m+e < d`; RS: `d = |D|−k+1`)
RS-SPECIFIC RESIDUE: none mathematically — only the polynomial representation of codewords
GENERIC LAW: incidence core PROVED generically; the `(r,z)`-parameterised MCA theorem NOT JUSTIFIED (it would require a new generic bad-set definition — a definitional, not mathematical, obstruction)
POWER INSTANCE: ℓ=3 → `2(e+1)` (dominates `max 2 (6e)`); ℓ=2 → `e+1` in window `k+3e ≤ |D|`, exactly the constant and window of the existing sharp line theorem
MODULE COMPRESSION: CORE (incidence, PolyGen, separation lemma); INSTANCE (ℓ=2, ℓ=3 generators); REFINEMENT (subresultant locus, circuit incidence above unique decoding); BOUNDARY (all counterexample witnesses kept); nothing deleted
SYNDROME RELATION: SAME-INCIDENCE-CORE — the circuit count is the `b = 1` disjoint case, formalised as a lemma; `CircuitIncidence.lean` itself was not rewritten
NOVELTY: D5
NEXT MOVE (not performed): specialise the P2 Johnson-regime bound to `γ = e/N` and compare it with `(ℓ−1)(e+1)` on the same event

# Summary of changes for run 315d32df-cc3b-4aac-ae51-fa06ab726820
MISSION REPORT — LOCATE THE TRUE LOSS IN GENERAL-ℓ MCA

Repository discipline: no Lean file was created or modified in this mission, no report file was added, and no proof was attempted. One single commit was made, and only to preserve the artifact of the previous round (`RequestProject/Root/CodingTheory/WHIRComparison.lean` plus its `#print axioms` lines in `RequestProject/Main.lean`, both already built and sorry-free); it was uncommitted and would otherwise have been lost. All experiments were run outside the repository with exact prime-field arithmetic (no floating point in any decision), and the harness reproduces the source definitions of `genComb`, `IsCloseOn`, `GenCloseOn`, `IsBadG`, `badSetG` verbatim, including the "same S" structure. Status labels below: MACHINE-CHECKED = already in the build; DERIVED = paper argument from machine-checked lemmas, not formalised; EXACT-COMPUTED = exhaustive/exact finite-field enumeration, not a Lean artifact.

1. WHIR EVENT — E-EQUAL (for |F| ≥ ℓ; E-OURS-SUBSET in general)

Our event, unfolded: γ ∈ badSetG ℓ k e f ⟺ ∃S ⊆ D with |S| ≥ |D| − e, ∃ u of degree < k with u|_S = (∑_j γ^j f_j)|_S, and ¬(∀δ ∈ F, ∑_j δ^j f_j is close on S). Def. 4.8, with Gen(ℓ;γ) = (1,γ,…,γ^{ℓ−1}), C = RS[F,L,m], D = L, N = |D| = n, k = m, δ = e/N: identical except that the last clause reads "∃i, no codeword agrees with f_i on S".
(⇒) If every constituent is close on S then every combination is close on S — this is exactly the machine-checked `gen_closure`; contrapositive gives Bad_ours ⊆ Bad_WHIR, unconditionally.
(⇐) If all ℓ-many combinations at ℓ distinct challenges are close on S, Lagrange inversion in the challenge variable (machine-checked `coeff_eq_sum_basis`, applied with S in place of the full domain) writes each f_i|_S as an F-combination of codewords, so every constituent is close on S. This needs ℓ distinct challenges, i.e. |F| ≥ ℓ. Hence equality of the two events whenever |F| ≥ ℓ.
Checklist: challenge set F both; distribution uniform on F both (our ε = |Bad|/|F|); same existential S in both clauses; threshold |S| ≥ (1−δ)n ⟺ |S| ≥ N − e for e = δN (for non-integral δN ours is e = ⌊δN⌋); no exceptional/conditioned challenges on either side; the only genuine modelling input is D = L (our N = |D|; if D ⊊ L the two codes differ and the comparison must be rescaled). EXACT-COMPUTED corroboration: the two readings were evaluated separately on 1320 random instances and on every extremizer below — 0 mismatches.
Consequence: under |F| ≥ ℓ and D = L, ε_ours is literally the WHIR MCA failure probability, so the already machine-checked arithmetic (`epsMCAG_lt_whirErrStar`, `ratio_gt_two`) applies to the same event: ε_ours ≤ max(ℓ−1, ℓ(ℓ−1)e)/|F| < 2(ℓ−1)|L|/|F| throughout k + (ℓ+1)e ≤ N, with quotient 2N/(ℓe) > 2.

2. EXTREMAL TABLE (brute force, exact; τ_min = min over all codeword families of |D∖T|)

(q,N,k,ℓ,e,B,τ_min,r_A,r_B,r_total)
( 5, 5,1,3,1, 4, 2, 0.667, 1.000, 0.667)
(11,11,1,3,2, 6, 3, 0.500, 1.000, 0.500)
(13,13,1,3,3, 8, 4, 0.444, 1.000, 0.444)
(13, 7,1,5,1, 8, 2, 0.400, 1.000, 0.400)
(11,11,1,2,4, 5, 5, 0.625, 1.000, 0.625)
( 5, 5,1,3,1, 3, 3, 1.000, 0.500, 0.500)   ← defect-saturated
(11, 7,1,4,1, 3, 4, 1.000, 0.250, 0.250)   ← defect-saturated
(11,11,1,3,2, 2, 6, 1.000, 0.167, 0.167)   ← defect-saturated
In every row B = (ℓ−1)(e+1) at the maximiser, and r_A·r_B ≤ (e+1)/(ℓe) < 1: the two inequalities are never saturated together.

3. BEST WITNESSES (all brute-verified)

W1 (the parametric family). Normalise by subtracting the common codeword family; put M = e+1 defect positions, position i carrying R_i(Z) = ∏_{r∈V_i}(Z−r) with |V_i| = ℓ−1 and V_1,…,V_{e+1} pairwise disjoint (needs |F| ≥ (ℓ−1)(e+1), N ≥ k + (e+1)). Then Bad = V_1 ∪ … ∪ V_{e+1}, |Bad| = (ℓ−1)(e+1), τ_min = e+1, m_x = ℓ−1 at every position. Verified exactly at (ℓ,e) = (2,1),(2,3),(2,4),(3,1),(3,2),(3,3),(4,1),(5,1).
W2 q=5,N=5,k=1,ℓ=3,e=1, root sets {0,1},{2,3}: B = 4 > ℓe = 3 > (ℓ−1)e = 2. Smallest counterexample to both B ≤ ℓe and B ≤ (ℓ−1)e.
W3 q=5,N=5,k=1,ℓ=3,e=1, root sets {1,4},{1,2},{2,4}: τ_min = 3 = ℓe with B = 3 ≥ ℓ — the union bound |D∖T| ≤ ℓe is attained by a configuration the proof really can produce. Kills τ_min ≤ e, ≤ 2e, ≤ (ℓ−1)e.
W4 q=11,N=7,k=1,ℓ=4,e=1, four root sets of size 3 with heavy overlap: τ_min = 4 = ℓe, B = 3, ∑m_x = 9 < (ℓ−1)τ_min = 12 — defect saturated, incidence collapsed.
W5 q=13,N=13,k=1,ℓ=3,e=3: B = 8 = (ℓ−1)(e+1) against the machine-checked ℓ(ℓ−1)e = 18.

4. LOSS DIAGNOSIS

LOSS A (|D∖T| ≤ ℓe): A-TIGHT. τ_min = ℓe is realised (W3, W4) with ≥ ℓ bad challenges present, so the union bound itself cannot be improved as a statement about τ_min.
LOSS B (#Bad ≤ (ℓ−1)|D∖T|): B-TIGHT. Equality holds exactly in W1/W5 (r_B = 1.000, every m_x = ℓ−1 simultaneously).
The loss is therefore neither factor but their composition: they saturate in mutually exclusive regimes. Mechanism (DERIVED, from lemmas already machine-checked in the file): for a bad γ the witness polynomial must be the common family ∑_j γ^j q_j (this is the `eval_eq_of_card_agreement_ge` step inside `card_badSetG_le_mul_defect`), so at most e positions of D∖T can have R_x(γ) ≠ 0 — every bad challenge is a root of at least M − e of the M polynomials, not just one. Global counting then gives #Bad·max(1, M−e) ≤ ∑_x m_x ≤ (ℓ−1)M, i.e. #Bad ≤ (ℓ−1)M/(M−e) for M > e and ≤ (ℓ−1)e for M ≤ e; maximising over M gives #Bad ≤ (ℓ−1)(e+1), attained at M = e+1. Large defect and many bad challenges are quantitatively incompatible: at M = ℓe the same count caps #Bad by ℓ, matching W3/W4. This derivation does not use LOSS A at all — the ℓe bound becomes irrelevant once the incidence count is global.
Gate 5 statistics: at B-extremizers the m_x are all exactly ℓ−1 and the root sets of distinct positions are disjoint, while all bad challenges share one defect set of size e+1 (each destroys e of its e+1 positions); at A-extremizers the root sets must overlap in ≥ M−e columns per challenge, which is what suppresses #Bad. No new invariant was introduced.

5. SCALING

Lower bound: #Bad ≥ (ℓ−1)(e+1) whenever |F| ≥ (ℓ−1)(e+1) and the window holds (W1, EXACT-COMPUTED at eight (ℓ,e) pairs; the family is symbolic and scales in both ℓ and e). Upper bound: (ℓ−1)(e+1), DERIVED, not machine-checked; the machine-checked upper bound remains max(ℓ−1, ℓ(ℓ−1)e). Matching bounds give TRUE SCALING = Θ(ℓe) — specifically the maximum appears to be exactly (ℓ−1)(e+1) (capped by |F|), not Θ(ℓ²e) and not Θ(e). Θ(ℓ²e) is refuted by the derived upper bound together with the exhaustive scans; Θ(e) alone is refuted by W1 with ℓ growing.
Falsified in Gate 4: τ_min ≤ e, ≤ 2e, ≤ (ℓ−1)e, and τ_min ≤ c·e for any c independent of ℓ (W3, W4); B ≤ (ℓ−1)e (already at ℓ=2,e=1: B=2); B ≤ ℓe (W2). Surviving over the whole tested range: B ≤ (ℓ−1)(e+1), and equivalently B − (ℓ−1)e ≤ ℓ−1 (the excess is independent of e). Exhaustive — not sampled — scans over all normalised instances with defect support ≤ ℓe were run for (q,ℓ,e) = (5,3,1),(7,3,1),(7,2,1),(11,2,1),(13,2,1); randomised exact search elsewhere. These scans are complete for the falsification question, because any instance with B ≥ ℓ has τ_min ≤ ℓe by the machine-checked `card_badSetG_le_mul_defect`.

6. NEXT MOVE — R-C (joint extremal theory)

Neither inequality can be repaired on its own: each is attained, and the product is not. The data show a hard trade-off — a bad challenge consumes M − e of the M defect positions at once — so the object to study is the joint incidence structure (challenges × positions) with the (M − e)-fold consumption, not τ alone; the concrete payoff of that study is the candidate law #Bad ≤ (ℓ−1)(e+1), which matches the lower-bound family exactly and would improve the machine-checked constant by a factor ℓe/(e+1). Abstraction (R-D) is not yet justified, since the current scaling is provably not the truth.

WHIR EVENT: E-EQUAL (|F| ≥ ℓ, D = L, k = m, e = δN; E-OURS-SUBSET unconditionally)
BEST LOWER BOUND FAMILY: e+1 defect positions carrying pairwise-disjoint full root sets of size ℓ−1 ⇒ #Bad = (ℓ−1)(e+1), τ_min = e+1, m_x ≡ ℓ−1
BEST UPPER BOUND: machine-checked max(ℓ−1, ℓ(ℓ−1)e); derived-but-unformalised (ℓ−1)(e+1)
COMMON DEFECT: A-TIGHT
ROOT INCIDENCE: B-TIGHT (pointwise), the product is not
TRUE SCALING: Θ(ℓe), conjecturally exactly (ℓ−1)(e+1) capped by |F|
BEST SURVIVING STRONGER CONJECTURE: #Bad ≤ (ℓ−1)(e+1)
NEXT RESEARCH DIRECTION: R-C

# Summary of changes for run ad1edc1d-12ba-41fa-8488-f12457f66792
## What I completed in this session

**1. Finished and verified the general-arity generator theorem.**

`RequestProject/Root/CodingTheory/PolynomialGeneratorMCA.lean` (in progress at the checkpoint) now **builds cleanly, contains no `sorry`, and is axiom-clean** (only `propext`, `Classical.choice`, `Quot.sound`). It generalises the ℓ = 3 result to the power generator of arbitrary arity, `γ ↦ ∑_{j<ℓ} γ^j · f_j`:

- `Root.CodingTheory.PolyGen.card_badSetG_le` — with **no structural hypothesis**: `1 ≤ k` and `k + (ℓ+1)·e ≤ |D|` ⟹ `#Bad ≤ max (ℓ−1) ((ℓ−1)·(ℓ·e))`.
- `…card_badSetG_le_mul_defect` — the sharper intermediate form `#Bad ≤ (ℓ−1)·|D \ T|`, `T` the common agreement set.
- `…exists_genAgreement_of_good_family` — ℓ distinct good challenges force a single common family `q₀,…,q_{ℓ−1}` of codewords of degree `< k` (Lagrange inversion at each position).
- `…card_fiber_le` — the multiplicity step: at most `ℓ−1` bad challenges charge any one position.
- `…epsMCAG_le` — the probabilistic form, `ε_mca ≤ max(ℓ−1, (ℓ−1)ℓe)/|F|`.
- `…card_badSetG_le_three` (`max 2 (6e)` under `k + 4e ≤ |D|`) and `…card_badSetG_le_two` (`max 1 (2e)` under `k + 3e ≤ |D|`) are now corollaries of the general theorem.

This settles the conceptual question that motivated the ℓ = 3 mission: the resource consumed by bad challenges is an **incidence pair**, support × multiplicity — `ℓ·e` positions missing from the common agreement set, times `ℓ−1` roots of a nonzero polynomial of degree `< ℓ` per position. The `6e` of the ℓ = 3 target is exactly `(ℓ−1)·ℓ·e` at `ℓ = 3`, and the window `4e + μ < N` is `k + (ℓ+1)e ≤ |D|` at `ℓ = 3`, where the `ℓ+1` decomposes as `1` (the challenge's own radius) `+ ℓ` (the witness sets).

**2. Updated the GATE −1 report.** `LITERATURE_DOMINATION_GATE.md` now records the general-ℓ theorem (new §2b), and answers gate item 2 — sharper dependence on `e`, `ℓ`, `μ` — internally.

**3. Full project build verified** (`lake build`, 8216 jobs, success), no `sorry` in the new file, all work committed and pushed. Spec-table entries were added for the new definitions and the two new theorems, both marked proved.

## Honest status of the one open item

The **external literature comparison remains not performed**. This environment has no access to the cited documents, and I deliberately did not reconstruct their hypotheses from memory — an invented specialisation is precisely what that gate exists to prevent. No classification is asserted against them. Against the project's own theory the classification stands at **L-A (new regime)**: every pre-existing bad-set bound here is for the two-word line generator, so the ℓ ≥ 3 statements lie outside their domain. Supplying the external statements closes the gate in one pass; the specialisation to `μ = k`, `N = |D|` is then mechanical against `card_badSetG_le` and the sharper `card_badSetG_le_mul_defect`.

The earlier strength-gate deliverables (`SUBRESULTANT_STRENGTH_GATE.md`, with the exact integers, certified log₂ brackets, field thresholds, and the P-B / M-A decisions, plus its Lean formalisation in `SubresultantStrengthGate.lean`) are unchanged and still build.


# Summary of changes for run 65fc798f-d371-416a-90ce-a54a096c8b17
Closed the last bridge and the full polynomial closure, entirely machine-checked.

**New module** `RequestProject/Root/CodingTheory/SubresultantCorrelatedBridge.lean` (no existing certified file was modified; `RequestProject/Main.lean` only gained the import and `#print axioms` lines).

Main results, all proved without `sorry`/`admit` and with axioms exactly `[propext, Classical.choice, Quot.sound]`:

1. **Gate 0 — semantics of `W_can = 0`.** `W_can` is total; when the Welch–Berlekamp kernel is zero the canonical generating family is empty, the ideal is `⊥`, and `W_can = 0` holds *vacuously* (`W_can_eq_zero_of_kernel_zero`).
2. **T1 — the zero bridge** (`rsCorrelatedAgreement_of_W_can_eq_zero`): with a nonzero kernel, `W_can = 0` implies the exact frozen Reed–Solomon correlated-agreement predicate (one fixed pair of codewords of degree `< k`, common error support), at **radius exactly `e`**, with no hypothesis on `|F|`, on `k` or on the window. Route: all `(k+1)`-minors vanish identically ⇒ column dependence over `F[Z]` ⇒ a bivariate identity `d·Q = −Λ·P`, read off at the trailing degree of `d`.
3. **T2** (`card_badSet_le_of_W_can_eq_zero`): composition with the existing counting theorem gives `#Bad ≤ e` in the zero branch.
4. **Gate 7, negative** (`kernelNonzero_not_automatic`): the nonzero-kernel hypothesis is *not* implied by `k ≥ 1, k + 2e ≤ |D|`; over the two-element field with `k = 1, e = 0` the kernel is zero, `W_can = 0` vacuously, and correlated agreement at radius `e` fails. So the proposed kernel-existence statement in that form is false, and T1 cannot be made unconditional.
5. **Gate 7, positive** (`kernelNonzero_of_forall_wbDet_eq_zero`): if every maximal minor of the Welch–Berlekamp pencil vanishes identically, a determinantal-rank argument over `F[Z]` (fraction field plus denominator clearing) produces a nonzero kernel element.
6. **T4 — final theorems.** `card_badSet_le_dichotomy` gives `#Bad ≤ (k+1)e + 1` under a nonzero kernel, and `card_badSet_le_unconditional` gives `k ≥ 1, k + 2e ≤ |D| ⇒ #Bad ≤ (k+1)e + 1` with **no structural hypothesis at all**, by splitting on the pencil instead of on `W_can`.

**Decision: A — full machine-checked closure**, with the two exact caveats (both proved, not assumed) that the zero bridge itself needs a nonzero kernel and that this hypothesis is discharged by the separate pencil-rank gate.

The mandated report is `SUBRESULTANT_CORRELATED_BRIDGE_REPORT.md` (nine sections, one decision letter). A full `lake build` succeeds; `rg -n "sorry|admit"` on the new module matches only the word inside its header docstring. All work is committed and pushed.

# Summary of changes for run 952e3bea-244c-4492-be04-c13fd81d7d9b
Mission CORRELATED_COMMON_SUPPORT_GATE executed and answered, with every verdict backed by a machine-checked Lean proof rather than a paper argument. Full project build is clean; every new declaration reports only `[propext, Classical.choice, Quot.sound]`; no `sorry`, no new axiom; `ARISTOTLE_SUMMARY.md` untouched.

**Finding first: there is no declaration literally named `CorrelatedAgreementAtRadius`.** The project carries three different correlated-agreement notions, and the common-support question has a different answer for each. The verdicts:

- **A — already in the definition** (Reed–Solomon notion, the one the `W_can = 0` analysis actually uses). The conclusion of the existing correlated-agreement theorems is a bound on a common agreement set; the common error support of size ≤ e is its complement. Formalised as `commonErrorSupport`, `commonErrorSupport_card_le_iff`, and the two-directional normal form `exists_commonErrorSupport_of_correlatedAgreement` / `correlatedAgreement_of_commonErrorSupport`. No new mathematics, no window hypothesis, no subresultant input.
- **B — the blocked item is a consequence of already formalised lemmas.** `#Bad ≤ e` in the correlated branch follows in three lines from the existing `card_badSet_le_card_compl`: `card_badSet_le_card_commonErrorSupport` (`#Bad ≤ |E|`), `card_badSet_le_of_correlatedAgreement` (`#Bad ≤ e`, under `1 ≤ k`, `k + 2e ≤ |D|`) and `card_badSet_le_of_card_goodZ_gt_third`. This is sharper than the existing `2e + 1`, whose constant is paid entirely by the other branch (few good challenges). **So the freeze can be lifted: the bound is now in the build.**
- **C — a small new lemma** for the abstract-alphabet notion: `LineAgreeOn` exhibits a codeword per line point but no pair; `Alphabet.exists_agree_pair_of_lineAgreeOn` extracts one (evaluate at γ = 0 and γ = 1), and `Alphabet.exists_commonErrorSupport_of_lineAgreeOn` converts it to the normal form.
- **D — true only at radius e + θ** for the slack notion: `Alphabet.exists_commonErrorSupport_of_slack`. Any downstream statement quoting radius `e` from the slack notion (the route used by the folded-RS results) is off by θ.
- **E — false** for the reading "each coordinate separately e-close". `separate_closeness_not_common_support` is an exhaustively decided counterexample over the field with five elements: two words each at distance 1 from a constant codeword whose best common agreement with any pair of constants is 3 < n − e = 4.

Deliverables: the report `CORRELATED_COMMON_SUPPORT_GATE.md` (verdict table, per-notion analysis, what remains open) and the new Lean file `RequestProject/Root/CodingTheory/CorrelatedCommonSupport.lean`, imported by `RequestProject/Main.lean` with the project's `#print axioms` audit lines. The Properties table has been updated with the definition and the seven new results.

Still open and explicitly not claimed: the algebraic characterisation `Bad = {−a(x)/b(x) : x ∈ E, b(x) ≠ 0}` (equality, not just the bound) remains a paper result, and the implication `W_can = 0 ⇒ correlated agreement at radius e` is still unformalised — it is the only remaining gap between the subresultant core and the new `#Bad ≤ e`. All work is committed and pushed.

# Summary of changes for run 481f2a89-9cc8-41c2-b776-7cea30e47d24
Mission executed as specified: no Lean files were touched, no broad sweeps were run, and exactly one new artifact was produced — `WCAN_ZERO_GATE_REPORT.md` (3 pages, the six mandated sections) — committed in a single commit.

**Outcome: DECISION B — POLYNOMIAL CLOSURE (in fact linear).**

Starting from the certified equivalence `W_can = 0 ⇔ Close_{F̄} = F̄ ⇔ correlated agreement at radius e`, and keeping `Bad` counted over `F`:

- **Gate A (catastrophe):** no catastrophic family exists in this branch, and this is proved rather than merely unfound — the §5 bound applies to every parameter set in the window `k + 2e ≤ n`, interior and wall alike. The best scalable family (`e_m = Θ(n_m)`, explicit and symbolic) attains `#Bad = e`, i.e. `Θ(e)` — no MCA statement is falsified. Interior and wall are not separated here; the only load-bearing inequality is `k + 2e ≤ n`.
- **Gate B (normal form):** correlated agreement forces `f₀ = p₀ + a`, `f₁ = p₁ + b` with `deg p_i < k` and error support `E`, `|E| ≤ e`, with `(p₀,p₁)` unique. The common locator `Λ_E = ∏_{x∈E}(X−x)` is forced, giving `Λ_E f₀ = Λ_E p₀`, `Λ_E f₁ = Λ_E p₁` on `D` with exact degrees `≤ e` and `< k+e`; consequently `W_can = 0 ⇒ ν = 0`, and the witness locator for each `γ` is a divisor of that one fixed `Λ_E` — the locator cannot vary essentially with `γ`. No new abstract theory was opened.
- **Gate C (characterisation, then counting):** an exact equivalence, not a one-sided criterion — `γ ∈ Bad ⇔ ∃ x ∈ E : a(x) + γ b(x) = 0`, i.e. `Bad = {−a(x)/b(x) : x ∈ E, b(x) ≠ 0}`. Hence `#Bad ≤ |E| ≤ e`, attained; so the maximum in this branch is exactly `e`. A by-product recorded in the report: the kernel is automatically nonzero in the window, so at paper level the hypothesis `W_can ≠ 0` can be dropped from the existing bound, giving `#Bad ≤ (k+1)e + 1` unconditionally for `k ≥ 1`, `k + 2e ≤ n`. A robustness variant under the weaker radius-`2e` correlated agreement gives `#Bad ≤ 2e` when `k + 3e ≤ n`.

Status discipline was kept throughout: the §§3–5 results are PROVED symbolically at paper level (Lean edits were forbidden this round); they are additionally EXACT-CHECKED by exhaustive small computation on 13 explicitly listed instances over `𝔽₁₁` (`n = 9`, interior `(k,e) = (2,3)` and wall `(3,3)`), where the brute-force `Bad` matches the criterion in every case, and where the criterion demonstrably fails once `k + 2e > n` — confirming the window hypothesis is essential. The behaviour beyond unique decoding is left explicitly OPEN. The report also names the next natural machine-checking target (splitting lemma + unique decoder + the exact criterion), which needs no subresultant machinery.

# Summary of changes for run 642f45fe-20e8-470e-a186-4b9aab35cd98
The full subresultant chain is now machine-checked, with no `sorry` and no new axioms.

**File:** `RequestProject/Root/CodingTheory/SubresultantCore.lean` (built with `lake build RequestProject.Root.CodingTheory.SubresultantCore`, then a full project build; `rg -n "sorry|admit"` matches only the word inside the module docstring). Every declaration listed below reports exactly `[propext, Classical.choice, Quot.sound]` via the `#print axioms` lines added to `RequestProject/Main.lean`.

**Setting.** Bivariate model `BiPoly F = (F[X])[Z]`, outer variable = line parameter `Z`. `IsWBKernel k e f₀ f₁ Λ Q` is the Welch–Berlekamp kernel of the line `f₀ + Z·f₁`; `ν` is the least `Z`-degree of a nonzero locator; `W_can` is the monic generator of the ideal spanned by all `(k+1)`-minors of `[T_Λ(Z) | Q(Z)]` over kernel elements of `Z`-degree ≤ ν.

**Gates, all closed:**
- Gate 1 — `minimal_kernel_degree_le`: `1 ≤ k`, nonzero kernel, `k + e ≤ |D|` ⟹ `ν ≤ e`, via the coefficient-independence micro-lemma.
- Gate 2 — `minimal_kernel_vector_primitive`: the specialisation `Λ(γ,·)` of a minimal locator is nonzero for every `γ` **in the base field `F`** (not stated over an algebraic closure).
- Gate 3 forward — `subresDet_eval_eq_zero_of_close` and `close_mem_roots_of_subresultant`.
- Gate 3 backward — `close_of_subresultant_root`. The degenerate cases (`Λ(γ)=0`, degree drops, spurious divisibility, quotient degree `= k`) are all handled: primitivity rules out `Λ(γ)=0`, and the last coordinate of the dependence vector cannot vanish since `F[X]` is a domain.
- Gate 4 — `close_eq_roots_W_can`: full set **equality** `{γ | close} = {γ | W_can(γ)=0}`, established before any cardinality argument.
- Gate 5 — `natDegree_subresDet_le`, `W_can_degree_bound` (`≤ (k+1)ν + 1`), `W_can_degree_poly` (`≤ (k+1)e + 1`).
- Gate 6 — `card_roots_le_degree`: only the rational-point root count is used; vanishing on a finite field is never used to infer `W = 0`.
- Gate 7 — `badSet_card_le_parameterised` (`≤ (k+1)ν + 1`, no kernel hypothesis needed) and the target theorem `badSet_card_le_poly`: with `1 ≤ k`, `k + 2e ≤ |D|`, a nonzero kernel and `W_can ≠ 0`, `#Bad ≤ (k+1)e + 1`.

**Infrastructure built along the way.** Mathlib has no determinantal-rank API, so `exists_nonzero_mulVec_eq_zero_of_forall_det_eq_zero` (all maximal minors of a rectangular matrix over a field vanish ⟹ columns are linearly dependent) is proved here from row rank = column rank; it is what makes the backward direction of Gate 3 possible.

**Frozen items respected.** `k + 3e ≤ n ⟹ ν = 0` was not formalised (it is false for `2 ≤ ν ≤ e`); correlated agreement was not investigated; no new theory was introduced. The three deferred questions (degenerate branch `W_can = 0`, a sharper bound on `ν`, sharpness of the degree bound) are recorded in `SUBRESULTANT_OPEN_QUESTIONS.md`.

No gate failed, so no stop-condition report is needed. `ARISTOTLE_SUMMARY.md` was left untouched. All work is committed and pushed.

# Summary of changes for run bcf07390-d510-43c9-a12b-ae7e8b3fb8ae
Created exactly one new file, `SUBRESULTANT_DEPENDENCY_AUDIT.md` (~2 pages, sections 1–6 as requested), in one commit. No Lean source was modified, no axiom, no `sorry`, no broad computation, no new theory, no API design.

**Decision returned: D — PAPER THEOREM OVERSTATED**, in exactly one item, with the scope of the failure made precise.

1. **NU RANGES.** The three ranges were checked separately with minimal hypotheses. Range 1 (`k+2e ≤ n ⇒ ν ≤ e+1`) and range 2 (wall `k+2e = n ⇒ ν ≤ e`) are true but non-minimal: both follow from a single uniform bound `ν ≤ e` valid under `𝒦 ≠ 0` and `k+e ≤ n` alone, proved in the audit by one classical micro-lemma (a minimal-degree kernel vector of a matrix pencil has linearly independent coefficients; the kernel here is a pencil on `e+1` columns once `Q` is recognised as determined by `Λ`). This removes the interior/wall distinction from the dependency graph. `ν ≤ e−1` is false; smallest witness is the project's `GapWitness` (`F₅, n = 4, k = 2, e = 1`, `ν = 1`), which also attains the degree budget. Range 3 (`k+3e ≤ n ⇒ ν = 0`) is **overstated**: the recorded proof forms the cubic combination using `Q₂ = Λ₁f₁`, an identity valid only when `ν = 1`; for `ν ≥ 2` the correction term leaves the gcd division outside the polynomial ring. What is actually proved is `k+3e ≤ n ⇒ ν ≠ 1`, hence `ν = 0` only for `e ≤ 1`; the case `2 ≤ ν ≤ e` is open (checked only), and a pencil example shows no purely pencil-theoretic argument can close it. The stronger variant `k+3e ≤ n+1 ⇒ ν = 0` is false (`GapWitness` sits at `k+3e = n+1`).

2. **PROOF DAG.** Written out arrow by arrow — common part (kernel → minimal primitive vector → `Close = V(W)` → `W_can`) and the two branches — each with a lemma name, exact hypotheses, the earlier lemmas used, the status label, and whether it assumes `W ≠ 0`, exclusion of correlated agreement, or a ν-bound. Existing kernel-checked project lemmas are cited as anchors where they already carry an arrow.

3. **CYCLES.** No cycle. In particular the feared `W ≠ 0 ⇒ root count ⇒ classification ⇒ W ≠ 0` does not close: the `W = 0` classification uses no root count and no degree bound, only that a nonzero polynomial has finitely many roots over an infinite field. Primitivity does not use `Close ≠ F`, the `Close ⇔ V(W)` equivalence does not use the degree bound (and is also correct in the degenerate case), canonicity is non-circular, and there is no separate wall argument left to depend on the interior inequality. Two hidden hypotheses are recorded: `Close` must be read over the algebraic closure (the direction "correlated agreement ⇒ `W_can = 0`" fails over a finite field), and `k ≥ 1`.

4. **CANONICITY.** The mandated order `W_u → I_can → W_can → V(W_can) = Close` is verified: `W_can` is defined from the kernel module and its minors only, independently of the `Close` theorem; `W_can | W_v` because every minor of the minimal vector lies in `I_can`; the containment `Close ⊆ V(W_can)` comes from the every-kernel-vector arrow and the reverse from that divisibility, giving equality, with degenerate consistency `W_v ≡ 0 ⇔ W_can ≡ 0 ⇔ Close = F̄`.

5. **W = 0 BRANCH.** All four implications of the equivalence `W_can = 0 ⇔ Close = F̄ ⇔ correlated agreement at radius e` are paper-proved (one direction also kernel-checked in the repository), and recorded separately: nothing is known about `Bad` in this branch — the classification of `Close` is explicitly not treated as a bound on `Bad`, and the item is marked OPEN.

6. **LEAN ORDER.** The requested minimal nine-step order is given, noting that steps 1–9 are independent of the overstated ν-range, which must be omitted or formalised only in its proved form.


# Summary of changes for run 13095a54-429a-4023-9b10-6c17029e7901
Delivered the requested four-gate report as the single new file `WB_SUBRESULTANT_GATES.md` (one commit, pushed). No Lean file was created or modified, no axiom, no `sorry`, no broad sweep, `P1/P2` untouched.

**DECISION: A — CANONICAL SUBRESULTANT THEOREM CERTIFIED.** Under the standing hypothesis `k+2e ≤ n` and a nonzero WB kernel module, either `f₀,f₁` have correlated agreement at radius `e` (equivalently `W ≡ 0`, equivalently every parameter is close), or `Bad ⊆ Close = V(W_can)` with `deg W_can ≤ (k+1)ν+1 ≤ (k+1)(e+1)+1 = O(ne)`.

Gate results in the report:

1. **Specialisation — EQUALITY (stronger than the required containment).** Paper proofs of: primitivity of a minimal-degree kernel vector (`Λ(γ,·) ≠ 0` for all `γ`); `γ ∈ Close ⇒ W(γ)=0` via the cross-product argument, which uses `k+2e−1 < n` and nothing else; and the converse `W(γ)=0 ⇒ γ ∈ Close`, where the "spurious zero" and "quotient degree = k" failure modes are excluded because `T_Λ(γ)` stays injective even when the `X`-degree of `Λ(γ,·)` drops. Exact finite-field checks: `Close = V(W)` parameter by parameter in all 56 analysed singular non-correlated-agreement instances; the 35 observed genuine degree drops produced no spurious zero.

2. **`W ≡ 0` — classifications A and B hold simultaneously; no hierarchy needed.** `W ≡ 0` ⟺ every parameter close ⟺ correlated agreement of `f₀,f₁` at radius `e`, proved in both directions (Gauss-type argument for polynomiality of the quotient, plus the `P = p₀ + Z p₁` degree comparison). Options C/D are not required.

3. **Canonicity.** Proved: `Close ⊆ V(W_u)` for *every* nonzero kernel vector, with equality for primitive ones, so the locus and its radical are canonical by theorem; and if the kernel module has rank 1 then it is generated by the minimal vector, so `W` itself is canonical up to a scalar. The canonical object in general is `W_can`, the monic generator of the ideal generated by all relevant `(k+1)`-minors over the whole kernel module; it satisfies `V(W_can) = Close` and divides `W`. Exhaustive check over all `5⁸` lines of one family plus a randomised hunt: every instance with a >1-dimensional minimal space was either correlated-agreeing (all `W = 0`) or gave literally the same monic `W` for all combinations of minimal vectors.

4. **Degree budget — EXACT, `B = (k+1)ν + 1`.** Column-wise `Z`-degrees (`≤ ν` for the `k` multiplication columns, `≤ ν+1` for the `Q` column, the latter proved by interpolation linearity) give `deg_Z` of every `(k+1)`-minor `≤ (k+1)ν+1`; `ν ≤ e+1` by a Cramer argument, `ν ≤ e` at the wall `k+2e = n` by a dimension count, and `ν = 0` deep inside. No violations in any tested instance, and the bound is attained (per-minor degrees `7, 9, 13` matching `(k+1)ν+1`, and `deg W = 4 = #Close` in the tight family). Nothing super-polynomial appears.

The report also records where the mechanism dies (only at `k+2e = n+1`, where the cross-product degree room is lost) and lists the instance families used. All computational statements are labelled as exact small-instance checks, distinct from the paper proofs; nothing was formalised in Lean, per the freeze.

# Summary of changes for run 156cefe8-bc10-4593-b4c8-6c3c5fbc191b
Delivered the requested report as the single new file `BAD_GAMMA_ALGEBRAIC_LOCUS_REPORT.md` (one commit, pushed; no Lean source touched, no axioms, no `sorry`, no sweeps).

**DECISION: B — a canonical subresultant/local divisor suffices.**

Findings (labels used in the report: LEAN = kernel-checked here, PROVED = paper proof, CHECKED = exact finite-field arithmetic on small instances):

1. **Exact relations.** `Bad ⊆ Close`, and — this is the leverage — for `k+2e ≤ n` a parameter is close iff *every* nonzero kernel vector at that parameter has numerator `Λ·p` with `deg p < k` (cross-product lemma already in the project). Closeness is a property of the parameter, not of the chosen kernel vector.
2. **Regular case restated as a locus.** One nonzero maximal minor `P(Z)` of degree `≤ e+1` gives `Close ⊆ V(P)`; the budget is the dimension `e+1` of the locator space.
3. **Rank route (A) is FALSE in the singular branch.** In both project witnesses the specialised kernel has dimension equal to the generic kernel rank at *every* parameter, so the `r`-th determinantal divisor is a unit and its zero set is empty while `#Close = 4`. Bad parameters cost no extra rank.
4. **First true characterisation is a gcd/divisibility condition.** With `(Λ,Q)` a kernel vector of minimal `Z`-degree `ν` (proved primitive: `Λ(γ,·) ≠ 0` for all `γ`), `Close = {γ : Λ(γ,·) ∣ Q(γ,·) with quotient of degree < k} = V(W)`, where `W` is the gcd of the `(k+1)`-minors of `[T_Λ(Z) | Q(Z)]`, a subresultant-type polynomial. `W ≡ 0` holds exactly when the two coordinates have correlated agreement at radius `e`.
5. **Global vs local.** Global data used: one item, the first minimal index `ν ≤ e`. Local data: `ord_{Z=γ} W`. Conservation: `Σ_{γ∈Close} ord_γ W ≤ deg W ≤ (k+1)ν+1`, with the regular branch the special case `deg W ≤ e+1`.
6. **Budget and strength gate.** `#Bad ≤ (k+1)ν + 1 = O(ne)`; no binomial, exponential or list-size factor; at `e = Θ(n)` it is `O(n²)`, so it passes. A new defect theorem is proved: `ν ≥ 1 ⇒ k+3e ≥ n+1`, so in the deep interior `k+3e ≤ n` the singular branch has `ν = 0` and `#Close ≤ 1`, re-deriving the interior `#Bad ≤ e+1` with no pencil hypothesis. The mechanism stays valid up to and including the wall `k+2e = n` and dies only at `k+2e = n+1`, where unique decoding is lost.
7. **Falsification attempts.** No counterexample to the containment or the budget: exact locus equality on both project witnesses and on 97 generated singular lines; 0 violations of the degree budget on 475 instances; `k+3e ≤ n ⇒ ν = 0` on 395 generated lines plus an exhaustive check over all lines of one small configuration; at the wall the maximal non-correlated-agreement `#Close` stayed constant as the field grew (5, 7, 11, 13, 17), so no family with `#Bad = Θ(|F|)` was found. One witness attains the bound exactly.
8. **One next theorem** is stated with a four-step formalisation order.

Caveat recorded in the report: these are paper proofs and exact small-instance checks; nothing here has been formalised, as the mission required.

# Summary of changes for run f1203aaa-3907-4c73-b3e3-d3e42e62c850
Created exactly one new file, `POLYNOMIAL_CORE_BARRIER_REPORT.md` (~2 pages, sections 1–7 as requested). No Lean file was created or modified, no axiom, no `sorry`, no sweep, no refactoring, and none of the excluded routes (projected-Rédei, P1/P2, list-size, binomial occupancy) were touched.

Findings, all sourced from the existing project material and labelled PROVED-IN-LEAN / PROVED-HERE / CONJECTURE:

1. MINIMAL CORE. The strongest `#Bad ≤ e+1` result is *not* the double count. It is determinantal: bad (indeed already *close*) parameters are roots of one maximal minor of the Welch–Berlekamp pencil of the line; that minor is affine-linear in the line parameter on exactly the `e+1` locator columns, so it has degree `≤ e+1`. Object = close parameters; resource = roots of that determinant; injectivity = the degree principle over a field; total resource = `e+1` = dimension of the locator space. The private-position/double-count proof is shown to be a combinatorial shadow of the same resource (its `e+1` is `max_u min(u, u/(u−e))` over a pool `u = n − |T| ≤ 2e`).

2. TRUE BARRIER. The single essential hypothesis is `H` = "the pencil has full column rank over `F(Z)`". `k+2e < n` is a *consequence* of `H`, necessary but not sufficient (a kernel-checked witness with `k+2e = 7 < 8` has `#Bad = 4 > e+1`). At `k+2e ≥ n` the pencil is singular for every word and the bound is outright false (`#Bad = n` attained). The condition `k+3e ≤ n` (`δ ≤ 1/6` at `ρ = ½`) is a proof artifact of the counting route only — it enters solely as a unisolvence inequality — although it is sharp for that route: both existing counterexamples sit exactly at `k+3e = n+1`.

3. NEW RESULT PROVED IN THE REPORT (paper level). Failure of `H` is rigid: a singular pencil forces nonzero `Λ′,Λ″` of degree `≤ e` with `Λ′f₀` and `Λ″f₁` polynomial of degree `< k+e` on `D` — both coordinates are `(k+e,e)`-rational, a codimension `≥ n−k−2e` condition. This yields a dichotomy valid on the whole strip `k+2e < n`: poly-size `Bad` (`≤ e+1`) OR rigid rational structure. Also proved: a padding construction transporting the known counterexamples to arbitrarily large `n` on the wall `k+2e = n` (it fixes `e`, so `ρ → 1`, `δ → 0`; no counterexample with `e ≥ 3` is known).

4. VERDICT: C — structural dichotomy. The wall for the mechanism is `δ = (1−ρ)/2` (= 1/4 at `ρ = ½`), not `δ = 1/6`; the entire target band `δ ∈ (1/6, 1/4]` lies inside the mechanism's reach for every line outside the rational locus. Strongest polynomial-scale candidate: `#Bad ≤ (e+1)(1 + max(0, k+3e−n)) = O(e²)` throughout `k+2e < n`, consistent with all existing witnesses (`#Bad = e+2` is the known lower bound) and giving `≈ 2³⁶ ≪ 2¹²⁸` at `n = 2²⁰`. One next mission: close the singular branch by Kronecker/Padé descent on the pencil's minimal indices.

Committed and pushed.

# Summary of changes for run b290d211-5096-48ab-80cc-c1f9c73d64b1
Created exactly one new file, `STRENGTH_GATE_REPORT.md` (≈2 pages, equations-first, structure TARGET / SUBSTITUTION / PHASE BOUNDARY / TARGET-REGIME RESULT / COMPARISON WITH OLD BOUND / REQUIRED IMPROVEMENT / VERDICT / NEXT MISSION). No Lean file was created or modified, no theorem was formalised or searched for, no parameter sweep, no closed route reopened.

Findings (all parameters recovered from the project sources, not assumed):

1. Exact target. `epsMCA = |badSet|/|F|` and `StrongMCA C δ err ⟺ ∀ e ≤ δn, ∀ lines, |badSet|/|F| ≤ err` (proved equivalent to the GG25 definition in the project). So the conversion is exactly `#Bad ≤ err·|F|`. Target regime: ordinary RS, n = 2²⁰, ρ ∈ {1/2,1/4,1/8,1/16}, err = 2⁻¹²⁸, usable |F| ≤ 2²⁵⁶ (2⁶⁴ already recorded as unsatisfiable). Validity regime of the projected bound: MDS, F prime, non-collinear witness selection, k + 2e ≤ n, i.e. δ ≤ (1−ρ)/2.

2. Substituted inequality: PASS ⟺ `2·C(n−1,2e−1) − 1 ≤ 2⁻¹²⁸·|F|`, i.e. `1 + log₂C(n−1,2e−1) ≤ log₂|F| − 128`.

3. Phase boundary. For e = O(1), `log₂R ≈ (2e−1)log₂ n`, PASS iff `2e−1 ≲ (log₂|F| − 129)/log₂ n`; at n = 2²⁰ the boundary is e* = 1 (|F| = 2¹⁶⁰) and e* = 3 (|F| = 2²⁵⁶), i.e. δ* ≈ 3·10⁻⁶. For e = δn, `log₂R = n·H(2δ) ± O(log n)`, so the required field size is 2^Θ(n).

4. Target-regime result: FAIL in every regime, with deficits of 3.5·10⁵ … 1.05·10⁶ bits (e.g. ρ = 1/2, δ = 1/4: log₂R = 1 048 566 vs budget 128) — "catastrophic deficit". Moreover the bound is logically vacuous (weaker than the free `#Bad ≤ |F|`) for every |F| ≤ 2²⁵⁶ at target parameters. Two structural blocks: its regime δ ≤ (1−ρ)/2 ≤ 1−√ρ can never reach the post-Johnson frontier, and it requires a prime field, excluding the M31-extension flagship field.

5. Comparison with the best already-proved bounds: `#Bad ≤ e+1` (≈18 bits, certifies 2⁻¹²⁸ at |F| ≥ 2¹⁴⁶) beats it by ≈10⁶ bits; against `#Bad ≤ max(C(n,e),e)` the exact crossover is `H(2δ) ≤ H(δ) ⟺ δ ≥ 1/3` (feasible only for ρ < 1/3), so it is worse for all ρ ≥ 1/3 and better only between two bounds that are both Θ(n) bits above budget. It does not improve the relevant exponent.

6. Required improvement: `B_required = 2⁻¹²⁸|F|` (2¹⁸ / 2³² / 2¹²⁸ at |F| = 2¹⁴⁶ / 2¹⁶⁰ / 2²⁵⁶); gap `R/B_req ≈ 2^{1.05·10⁶}` at the flagship point — Θ(n) bits, i.e. an exponential improvement (exp(Θ(n)) → poly(n)). Improving the constant 2, the slack terms, or the Szőnyi direction constant buys ≤ 1 bit. The whole deficit sits in `M*_L ≤ 1 + C(n−1,2e−1)`.

Verdict: C — FUNDAMENTALLY INSUFFICIENT; formalising Rédei–Szőnyi to complete the chain is not recommended. The report names the genuinely open sub-band (δ ∈ (1/6, 1/4] at ρ = 1/2) and the numeric acceptance test (`#Bad ≤ 2¹²⁸` at n = 2²⁰) that any future mechanism must pass before formalisation. Work is committed and pushed.

# Summary of changes for run 4fb5674c-ef3c-468a-87e4-3a748a01c544
## OUTCOME A — both bridges are valid, and both are now machine-checked.

I answered only the two questions asked, formalised only the lemmas needed to certify them, created exactly one new Lean file, and modified no existing file. No `sorry`, `admit`, `native_decide`, or new axiom; every certifying lemma audits to `[propext, Classical.choice, Quot.sound]` and the project builds clean.

### TEST 1 — secant → projected list: PASS
The containment `D_λ ⊆ λ(L(f₁,2e))` reduces to a single algebraic identity,
`projDirection λ c γ γ' = λ((γ−γ')⁻¹ • (c γ − c γ'))`, i.e. **the projected direction *is* λ of the secant slope**. It consumes exactly two properties of `λ`: additivity and `F`-homogeneity for the scalar `(γ−γ')⁻¹`. The existing secant lemmas are strong enough as they stand — `slope_mem` puts the slope in the code, `hammingDistance_slope_le` puts it within `2e` of `f₁` — so the slope is already an element of `L(f₁,2e)`. Certified as `projDirections_subset_image_nearbyList`, with no genericity, no injectivity of `λ`, no primality, no bound on `|B|`, no minimum-distance hypothesis. Recorded scope limit: `F`-homogeneity is indispensable, so the statement is for `F`-linear, `F`-valued functionals; the extension-field variant remains separate and open.

### TEST 2 — coordinate admissibility of `λ_x`: PASS
The three properties are proved separately, not bundled:
- **first-coordinate injectivity** (`projPoint_injective`) — unconditional;
- **no vertical collapse** (`projPoint_fst_ne`) — unconditional;
- **non-collinearity** (`not_collinear_projPoint_of_mem_supp`) — uses exactly `hx : x ∈ supp(V_W)`.

On the critical question — does `hx` really imply non-collinearity? — **yes**, via a two-step chain: (1) `x ∈ supp(V_W)` is inherited by a generator, because otherwise `V_W ≤ ker(ev_x)`, so some slope difference is nonzero at `x`; (2) the collinearity criterion (proved from `collinear_iff_of_mem`) shows that a collinear projected configuration forces the direction vector to have nonzero first coordinate and every projected slope to equal a single constant. The two contradict, so `λ_x` is admissible. No definition was strengthened. Companion fact certified: `V_W ≠ 0 ⟹ supp(V_W) ≠ ∅`, so the hypothesis is non-vacuous and sharp (if `V_W = 0`, *no* functional is admissible).

### Hypotheses the full projected-Rédei theorem would need
(1) `λ` `F`-linear and `F`-valued; (2) a witness selection with agreement sets of size ≥ `|ι| − e` and codewords in `C`; (3) non-collinearity in the usable form `∃ x ∈ supp(V_W)`; (4) for the quoted direction theorem only, `F = F_p` prime with `|B| ≤ p`. Nothing else is missing on the coding-theory side; the only external ingredient left is the Rédei–Megyesi/Szőnyi direction bound, which I did not prove or use.

### Reduction signal
Both bridges collapse to single general mechanisms rather than piles of local lemmas: admissibility is the *linear* condition `λ ∉ Ann(V_W)`, already covered by the coordinate functionals; and Bridge 1 is the statement that projection is a morphism of slope data, not merely of points.

### Files
- `RequestProject/Root/CodingTheory/ProjectedSecantBridges.lean` (new, builds clean)
- `PROJECTED_BRIDGES_VERDICT.md` — the verdict, the exact lemma chains, and the hypothesis list.

All work is committed and pushed.

# Summary of changes for run dd576970-88c2-41f6-8493-fd0c24b2135f
**Mission P2 is complete: `m_x ≤ C(n−1, 2e−1)` is formally proved (Outcome A).**

New module `RequestProject/Root/CodingTheory/MDSOccupancy.lean`, built on the existing support-geometry core and list-size file, which were left untouched. No `sorry`, no `admit`, no new axiom, no `native_decide`.

**Mathematical audit before coding, and the threshold was not inherited.** The pointed argument lives in an `(n−1)`-element universe one size unit lower, so its LYM condition is `2(2e−1) ≤ n−1`, i.e. the sharper split `4e ≤ n+1` versus `4e > n+1` — not the `4e ≤ n` split of the list-size theorem.

**What was proved**

- `coordinateMultiplicity_le_choose` — the main theorem: for an *arbitrary* linear code over an arbitrary field, an *arbitrary* received word, `e ≥ 1` and any coordinate `x`, if `k + 2e ≤ n` and `n + 1 ≤ d(C) + k` then `#{q ∈ L(f₁,2e) : f₁ x ≠ q x} ≤ C(n−1, 2e−1)`. Exactly the hypotheses of the list-size theorem; no dimension hypothesis, no MDS assumption.
- Definitions `occupiedAt` and `coordinateMultiplicity` (`m_x`), with the two equivalent descriptions (`x ∈ E(q)` / disagreement at `x`) recorded.
- `e = 0` handled explicitly, not through truncated subtraction: `occupiedAt_eq_empty_of_e_zero`, `coordinateMultiplicity_zero`, and the hypothesis-free `coordinateMultiplicity_le_choose'`.
- Branch A (`coordinateMultiplicity_le_choose_of_four_mul_le`): pointed LYM on the punctured support family, with the punctured-antichain step proved explicitly and separately as the reusable finite-set lemma `subset_of_erase_subset_erase` (the implication is false without pointedness). The LYM infrastructure of the earlier file is reused, not duplicated; only its *relative* form (`card_le_choose_of_isAntichain_subset`, over an ambient finset `T`) is new.
- Branch B (`coordinateMultiplicity_le_choose_dim`): the pointed information-set injection — since `x` lies outside the agreement set of an occupied list element, the chosen `k`-subset avoids `x`, giving `m_x ≤ C(n−1,k)`; the comparison `C(n−1,k) ≤ C(n−1,2e−1)` is proved, with the required `k ≤ 2e−1` derived (not assumed) from `4e > n+1` and `k + 2e ≤ n`. Neither branch uses the global bound `|L| ≤ C(n,2e)`.
- Branch coverage proved inside Lean; MDS and Reed–Solomon corollaries derived (the latter also shows the hypotheses are satisfiable).
- Extras that were inexpensive: the coordinate-projection corollary `|λ_x(L)| ≤ 1 + m_x ≤ 1 + C(n−1,2e−1)` (no Rédei input), and the double-counting identity `Σ_x m_x = Σ_{q∈L}|E(q)| ≤ 2e·|L|`, used only as a sanity check.

**Quality control.** Single-file build succeeds with zero warnings; the full default build succeeds; `#print axioms` on all nineteen new declarations (added to `RequestProject/Main.lean`) reports only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx` in the build; a search of the new file finds no `sorry`/`admit`/`axiom`/`native_decide`.

**Frozen as instructed:** projected Rédei, `M*_L`, deep-hole sharpness, the strong-MCA definition and numerical experiments were not touched; equality/sharpness is reported as unformalised.

Deliverable report: `MDS_OCCUPANCY_FORMAL_REPORT.md` — exact theorem, both branch proofs, threshold and coverage, generality audit, Lean declaration table with dependencies, build and axiom audit, equality status, projection-corollary status, the explicit boundary before Rédei, and exactly one recommended next mission (a *conditional* formal projected-Rédei bridge, with the Rédei–Szőnyi direction theorem taken as an explicit hypothesis of the statement rather than an axiom).

All work is committed and pushed.

# Summary of changes for run 22bfdca6-a9ba-4e78-b50c-ec312f0d80cd
**Mission P1 is complete: `|L(f₁,2e)| ≤ C(n,2e)` is formally proved.**

New file `RequestProject/Root/CodingTheory/MDSListSize.lean`, built on the existing support-geometry core (`SupportGeometry.lean`) and `Hamming.lean`. No `sorry`, no `admit`, no new axiom, no `native_decide`.

**Mathematical audit first, then Lean.** The two branches and their coverage were worked out before coding, and one implicit assumption in the earlier informal information-set argument was found and corrected (it silently needed `k ≤ 2e`, which does *not* hold throughout `2e ≤ n−k`, but does hold whenever `4e > n` — exactly the branch that uses it). The final theorem therefore carries no hidden dimension assumption.

**What was proved**

- `decodingList_ncard_le_choose` — the theorem in its weakest form: for an *arbitrary* linear code `C ⊆ ι → F` and an *arbitrary* received word `f₁`, if `k + 2e ≤ n` and `n + 1 ≤ d(C) + k` then the radius-`2e` list has at most `C(n,2e)` elements. No dimension hypothesis, no assumption on `f₁` or on the field.
- `mds_decodingList_ncard_le` — the same in the requested `[n,k]` MDS shape (`d = n−k+1`, `dim = k`, `2e ≤ n−k`), plus a `Finset`-cardinality restatement.
- Branch A (`decodingList_ncard_le_choose_of_four_mul_le`): LYM for `4e ≤ n`, using the antichain and injectivity of error supports. This required a lower-half LYM lemma (`ncard_le_choose_of_isAntichain`), since Sperner's `C(n,⌊n/2⌋)` is too weak in the interesting regime, and the binomial comparison `a ≤ b ∧ a+b ≤ n ⟹ C(n,a) ≤ C(n,b)`.
- Branch B (`decodingList_ncard_le_choose_dim`): an information-set injection into `k`-subsets giving `|L| ≤ C(n,k)`, with the final comparison `C(n,k) ≤ C(n,2e)` proved (not assumed) from `k ≤ 2e` and `k + 2e ≤ n`.
- Branch coverage is proved inside the Lean proof: the split is `4e ≤ n` vs `4e > n`, and each branch's extra ingredient is derived from the two stated hypotheses alone.
- `reedSolomon_decodingList_ncard_le` — the theorem instantiated at Reed–Solomon codes via the project's exact minimum-distance result, confirming the hypotheses are satisfiable.

**Hypothesis weakening (checked, small effort).** The proof never uses the dimension and never uses distance *equality*: only `d ≥ n−k+1` together with `k + 2e ≤ n`. The general theorem is stated at that strength; the MDS-shaped corollary is derived from it.

**Quality control.** `lake build` of the new module succeeds with zero warnings; the full default build succeeds; `#print axioms` on all eleven new declarations (added to `RequestProject/Main.lean`) reports only `[propext, Classical.choice, Quot.sound]`; a search of the new file finds no `sorry`/`admit`/`axiom`/`native_decide`.

**Frozen as instructed:** occupancy `m_x`, projected Rédei/MCA, deep-hole sharpness, and any numerical experiment were not touched; the general support-geometry mathematics is unchanged.

Deliverable report: `MDS_LIST_THEOREM_FORMAL_REPORT.md` (statement, both branch proofs, coverage proof, Lean declarations, dependency graph, weakest hypotheses, build result, axiom audit, and status of occupancy / projected-MCA / sharpness). Per the mission's decision tree this is Outcome A, and the single recommended next mission is the formal MDS occupancy theorem `m_x ≤ C(n−1,2e−1)` — with the recorded observation that its Branch-A condition is `4e ≤ n+1`, weaker than the split used here.

All work is committed and pushed.

# Summary of changes for run afe826ad-3657-4c20-96ee-8272ea9425c4
## What was done

The general support-geometry core is now formalised in Lean, exactly at the generality the proofs have, and nothing beyond it was touched.

**New file:** `RequestProject/Root/CodingTheory/SupportGeometry.lean` (namespace `Root.CodingTheory.SupportGeometry`), built on the project's existing `Hamming.lean` (`hammingDistance`, `agreementSet`, `minDistance`) with codes as `Submodule F (ι → F)`. No new axiom, no `sorry`, no `admit`, no `native_decide`.

Definitions: `errorSupport f1 q` (coordinates where `f1` and `q` differ) and `decodingList C f1 e = { q ∈ C : d(f1,q) ≤ 2e }`.

Proved, for an **arbitrary** linear code over an arbitrary field, with `f1` an arbitrary received word (not assumed to be a codeword):

1. **Small-support uniqueness** (`eq_of_errorSupport_subset_of_card_lt_minDistance`) — for any coordinate set `S` with `|S| < d(C)`, at most one codeword has `supp(f1 − q) ⊆ S`. This single lemma is the engine of everything else.
2. **Support injectivity** (`injective_errorSupport`, `injOn_errorSupport`, `subsingleton_of_errorSupport_eq`) — under `2e < d(C)` the support determines the list element, so support ↔ error vector ↔ codeword ↔ list element is a bijection on the radius-`2e` list. No surjectivity onto arbitrary supports is claimed anywhere.
3. **Union law** (`minDistance_le_card_union_errorSupport`, `union_errorSupport_ge_minDist`) plus the intersection form (`card_inter_errorSupport_le`) and the agreement/packing form (`card_inter_agreement_le`).
4. **Antichain** (`errorSupport_antichain`, `eq_of_errorSupport_subset`, `isAntichain_errorSupport`).

`Main.lean` imports the file and runs `#print axioms` on all eleven new declarations; every one reports only `[propext, Classical.choice, Quot.sound]`. `lake build` completes successfully (8207 jobs), the single-file build is warning-free, and a search confirms no `sorry`/`admit` in the new file. Everything is committed and pushed.

**Report:** `MDS_FORMAL_CORE_REPORT.md` contains the ten requested items: exact statements, dependency graph, weakest hypotheses (with the note that the union law does not in fact need `2e < d`), proof status per phase, build status, axiom audit, missing infrastructure, the boundary against external Rédei–Szőnyi input, sharpness status, and one next mission.

## The specific point you asked me to check

`|L| ≤ C(n,2e)` does **not** follow from the antichain property alone. The general implication "antichain of subsets of an `n`-set, all of size `≤ t` ⇒ family size `≤ C(n,t)`" is false: the six 2-subsets of a 4-set form an antichain with all sizes `≤ 3` and `6 > C(4,3) = 4`. Sperner's theorem is also the wrong tool — it yields only the middle binomial `C(n, ⌊n/2⌋)`, which is weaker than `C(n,2e)` precisely in the interesting regime. The correct route is LYM (available in Mathlib) *plus* the extra hypothesis `4e ≤ n`, with the MDS information-set injection covering the complementary branch; the two branches do cover `2e ≤ n−k`, and that coverage argument is written out in the report. So Phase 5 is genuinely not a corollary of the general core, and the missing pieces are three small lemmas (lower-half binomial monotonicity, LYM-with-`t`, and a `Set`→`Finset` adapter for the antichain family), not a combinatorics library.

Per the freeze, the MDS interpolation equivalence, the list-size and occupancy bounds, the projected coordinate functional, the projected MCA corollary and all sharpness/deep-hole statements were **not** introduced into the Lean build.


# Summary of changes for run d477f226-7a4b-4c03-8251-daa73f9c6500
Delivered `MDS_SUPPORT_ANTICHAIN_AUDIT.md` — the support-antichain lemma is now **settled, and settled in a sharper form than claimed before**. No Lean file was created or modified, no axiom, no `sorry`/`admit`, no broad scan; one tiny exact-arithmetic check (`analysis/mds_support_antichain_check.py`, integers mod p only, transcript in `analysis/mds_support_antichain_check_output.txt`) guards the worked examples, and every claim labelled PROVED carries a self-contained proof independent of it.

Main findings:

1. **Threshold.** The three candidates `2e ≤ n−k`, `2e < d`, `2e < n−k+1` are literally the same inequality for MDS codes and integer e. The intrinsic hypothesis is `2e < d`; MDS enters only through `d = n−k+1`. Sharp: at `2e = d` both properties fail (minimal witnesses: [2,1]/F₃ — injectivity and antichain fail; [2,1]/F₂ — only the antichain fails, so the two properties are independent at the boundary). Written as `2e ≤ n−k` the hypothesis is false for non-MDS codes (explicit binary [4,2] counterexample).

2. **Injectivity — PROVED, and stronger.** For any linear code and any `S` with `|S| < d`, at most one codeword q has `supp(f₁−q) ⊆ S`. So supports label list elements injectively *and each support carries multiplicity exactly one* (support / error vector / codeword / list element are in bijection). No MDS property is used.

3. **Antichain — PROVED**, not a consequence of injectivity (independent, as the F₂ example shows) but the same one-line argument; and subsumed by the stronger **union law** `|E(q) ∪ E(q')| ≥ d`, equivalently the packing form: agreement sets have size ≥ n−2e and pairwise intersections ≤ k−1.

4. **Coordinate bound — PROVED.** `m_x ≤ C(n−1, 2e−1)` for every MDS code in the regime, via two complementary branches (LYM on the antichain; injection into k-subsets of an information set) that jointly cover the whole regime. The same argument upgrades the previous list bound `Σ_{i≤2e} C(n,i) ≤ 2ⁿ` to the single binomial `|L| ≤ C(n,2e)` (plus the packing bound `C(n,k)/C(n−2e,k)`).

5. **Exact equality characterisation.** Both bounds are attained **iff `2e = n−k` and f₁ is a deep hole** (`d(f₁,C) = n−k`); then exactly `|L| = C(n,k) = C(n,2e)` and `m_x = C(n−1,k) = C(n−1,2e−1)` uniformly in x. Strictly inside the regime (`2e < n−k`) both bounds are provably never attained. Equality is realised in RS[4,2]/F₅, RS[5,3]/F₅ (exhaustive over all received words), RS[6,2]/F₁₁ and RS[7,3]/F₁₁ with f₁ = (α^k). This turns the previously only-measured saturation (|L| = 15, max m_x = 10 at RS[6,2]) into a theorem with an equality criterion.

6. **MDS vs RS separation** is tabulated: injectivity, antichain, union law and the LYM counting use only `2e < d` (arbitrary linear code); the information-set branch and the exact boundary values use only MDS; Reed–Solomon is used solely to exhibit deep holes, never inside a proof. Existence of deep holes for *all* MDS parameter sets is left explicitly OPEN and is not claimed.

Recorded (not developed, per the freeze): substituting into the already-established support bound gives the p-free `M*_L ≤ 1 + C(n−1,2e−1)` and `|B| ≤ 2·C(n−1,2e−1) − 1`, replacing the earlier `1 + 2^{n−1}` / `2ⁿ − 1` (at RS[6,2], e=2: 11 and 19 instead of 33 and 63); consistent with the RS[4,2]/F₅ sharpness instance.

Exactly one next mission is stated: formalise the settled chain in Lean at the generality the proofs actually have (unique word per small support → injectivity/antichain for arbitrary linear codes under `2e < d` → union law → the exact MDS boundary theorem), leaving the LYM counting for afterwards. All work is committed and pushed.

# Summary of changes for run b54cb6bd-3ae6-4a31-a104-9e12a3ca9e1b
**Mission executed exactly as scoped: no Lean source created or modified, no axiom, no `sorry`/`admit`, no formalisation, no Rédei–Szőnyi proof, no Johnson/κ redevelopment, no broad scan.** The single report deliverable is `PROJECTED_BALL_FIRST_TEST.md`, backed by one small exact-arithmetic check (`analysis/projected_ball_first_test.py`, transcript `analysis/projected_ball_first_test_output.txt`; Python integers mod a prime, no floats, 72 s).

**Answer: CASE A — structural compression exists, and it is exactly the interpolation regime.**

1. **Level 1 (ambient ball), PROVED.** For `C = F_p^n`, `e ≥ 1` and every nonzero `λ`, `λ(L) = F_p`. There is no dependence on `|supp λ|` and no threshold in `p`, so the hoped-for universal `p`-independent bound `|λ(L)| ≤ F(n,e)` for arbitrary `λ` and arbitrary codes is **REFUTED**.
2. **The exact obstruction, PROVED.** If some `q₀ ∈ C`, `0 ≠ v ∈ C` satisfy `d(f₁,q₀) + wt(v) ≤ 2e`, then the codeword line `q₀ + F_p v` lies inside the list, so `λ(L) = F_p` whenever `λ(v) ≠ 0`; and if the span of such `v` contains the witness slope space `V_W`, then **every admissible `λ` is full**, i.e. `M*_L = p`. For Reed–Solomon (proved: min-weight codewords span the code) this triggers unconditionally as soon as `d(f₁,C) + d ≤ 2e`, closing that regime quantitatively.
3. **Compression is nevertheless real, PROVED.** `|λ(L)|` = number of cosets of `ker λ` meeting `L` (so compression comes only from low-weight codewords killed by `λ`), giving `M*_L ≤ min(|L|,p)`, `M*_L ≥ |L|/h`, plus the support bound `M*_L ≤ 1 + min_{x ∈ supp V_W} m_x ≤ 1 + ⌊2e|L|/|supp V_W|⌋` with `m_x = #{q ∈ L : q_x ≠ f₁(x)}` — the admissibility constraint `λ|_{V_W} ≠ 0` costs only a restriction to the coordinates in `supp V_W`.
4. **A `p`-free theorem, PROVED.** In the interpolation regime `2e ≤ n−k` (MDS/RS), the error supports `supp(f₁−q)` label list elements injectively and form an antichain, so `|L|` and `m_x` — hence `M*_L` and, via the quoted Rédei–Szőnyi step, `|B|` — are bounded by functions of `n, k, e` alone, independent of `p`. Measurements at `RS[6,2]`, `e = 2`, `p = 11…29` show saturation at the `p`-free values `|L| = 15`, `max_x m_x = 10`, and the coordinate bound `1 + C(n−1,2e−1) = 11` is attained; coordinate functionals strictly beat general ones (11 vs 15).
5. **Explicit affirmative instance and sharpness, PROVED.** `RS[4,2]/F₅`, `e = 1`, `f₀ = (0,0,1,0)`, `f₁ = (0,0,0,1)`, `B = {0,2,4}`: an admissible coordinate functional gives `λ(L) = {0,2,4}`, `M*_L = 3 < p = 5`, and `|B| = 3 = 2M*_L − 3` — the projected Rédei bound is attained exactly.
6. **Exhaustive measurement.** 81 443 non-collinear witness selections over RS and non-RS random codes (`p ≤ 13`), with the full dual `C^∨` enumerated per selection: 0 violations of any proposed bound and of the Rédei consistency `|B| ≤ 2M*_L − 3`; `M*_L < p` in 993 records, and the split is exactly the regime split — all 993 satisfy `2e ≤ n−k`, and none of the 80 441 records with `2e > n−k` compresses.

The report separates PROVED / REFUTED / EMPIRICALLY SUPPORTED / OPEN throughout, gives the symbolic comparison with the existing MCA bounds (the new bound is `p`-free in the interpolation regime, and improves `|B| ≤ 2|L|−3` by the factor ≈ `2e/|supp V_W|`; e.g. 27 → 19 at `RS[6,2]`, `p ≥ 17`), and selects exactly one next step: prove the exact extremal functions `max |L|` and `max_x m_x` for MDS codes in the regime `2e ≤ n−k` and state the two-arm theorem there, formalising only afterwards. All work is committed and pushed.

# Summary of changes for run a2e6e474-b2f1-41a3-abf0-9c4d6a9d3da4
Created the single required deliverable, `PROJECTED_REDEI_CLAIMS.md`. No Lean source was touched, no script was added, no axiom/`sorry` introduced, no broad scan performed.

Results:

**Claim A — PROVED.** For every witness selection and every functional `λ : C → F` that is additive and `F`-homogeneous, the projected point set `S_λ = {(γ, λ(c_γ))}` has all its secant directions affine (never vertical, since the abscissae are pairwise distinct, which also gives `|S_λ| = |B|` as a set) and `D(S_λ) = λ(D(B)) ⊆ λ(L(f₁,2e))`. The proof uses only linearity plus the project's already-proved secant lemma. The weakest hypotheses are isolated: homogeneity is needed only for the scalars `(γ−γ')⁻¹`, and `λ` must be valued in the same field as the parameters.

**Sharpness of that hypothesis — a counterexample.** Over a non-prime field, a merely `F_p`-linear `λ` breaks Claim A: with `F = F₄`, three points and `λ =` Frobenius, a projected direction lies outside `λ(D(B))`. So the "project `F_p`-linearly into `AG(2,p)` and use the prime-field theorem" route over extension fields is refuted; that case is marked OPEN and kept logically separate.

**Claim B — PROVED**, in the strong form the mission demanded (non-collinearity in the plane, not mere distinctness). The admissible set is exactly `Λ(W_s) = C^∨ ∖ Ann(V_W)`, where `V_W` is the span of the *slope differences*; non-collinearity of `W_s` is equivalent to `V_W ≠ 0`, hence `Λ(W_s) ≠ ∅`, with `|Λ| = p^k − p^{k−r} ≥ p^{k−1}(p−1)`. The argument is pure linear algebra: no primality, no `|B| ≤ p`, no threshold on `p`, no MCA structure — so all the sub-cases listed in the mission have the same answer. A coordinate functional always suffices, giving a canonical finite projection cover. Conversely, a collinear selection admits no admissible `λ` at all, so the two-arm dichotomy is unavoidable.

**Consequences recorded.** The conditional bound `|B| ≤ 2·M*_L − 3` (with `M*_L` the minimum of `|λ(L(f₁,2e))|` over admissible `λ`) is now justified conditional on the quoted Rédei–Szőnyi direction theorem alone; that theorem is cited, not re-proved, as instructed. The report also shows decisively that `M*_L` may **not** be replaced by the unrestricted `min_λ |λ(L)|`: `λ = 0` is inadmissible and makes that minimum `1`, turning the bound into `|B| ≤ −1`. Two honest caveats are stated: `M*_L` depends on the selection, and the bound is vacuous on the previously recorded small-field instances.

**Recommended next step (one):** SUCCESS A — "Projected Hamming-ball geometry", i.e. bound `M*_L` in terms of `n`, `e`, `k` and the support interaction rather than `p`, with the collinear arm's exact zero-count written out as a secondary deliverable and formalisation deferred until then.

All work is committed and pushed.

# Summary of changes for run b03ba07c-fca4-463f-886a-796fa66c663a
**Deliverable: `WITNESS_LOCUS_DIMENSION_PROBE.md`** (the only report created), backed by the new exact-arithmetic measurement `analysis/witness_locus_dimension_probe.py` with transcript `analysis/witness_locus_dimension_probe_output.txt`. Constraints respected: no Lean file written or modified, no axiom, no `sorry`/`admit`, no Johnson/list-size machinery, no reopening of support geometry / occupancy / κ-charging, no broad sweep, exact integer arithmetic mod a prime only (no floats anywhere).

**Decision: OUTCOME A** — a canonical low-dimensional reduction exists, though not the one `R1` asked for.

Main findings (324 instances with `|B| ≥ 3`, witness selections enumerated **exhaustively** in all of them, both witness conventions):

1. `W_full` and `W_s` are kept strictly apart, and the distinction is real: in 6 instances `dim aff(W_full) > max_s dim aff(W_s)` (smallest: `RAND[7,3]/F7`, `e=2`, `|B|=3`), and in 40 instances one selection is collinear while another is not.
2. **Dimension theorems (proved, checked 324/324):** `dim aff(W_s) = 1 + dim aff(Q)` — witness geometry and secant-direction geometry are the same object shifted by one; `dim aff(W_s) ≤ min(|B|−1, k+1)` with `k = dim C` (attained 73 times, so `H1` holds only in the `|B|`-independent form `d₀ = k+1`, and large `|B|` does **not** force collapse); `dim = 1` ⟺ `|D| = 1` ⟺ all witnesses on a single *codeword* line, which additionally forces witness uniqueness (0/113 counterexamples).
3. **`R1` (planar embedding) is refuted**; what works is the canonical dual quotient `π_λ(γ,c) = (γ, λ(c))`: injective on every selection for free (distinct first coordinates), direction-preserving, and it projects the MCA inclusion to `D_λ(B) ⊆ λ(L(f₁,2e))`. A suitable `λ` exists in 211/211 non-collinear instances.
4. **The bridge:** with the Rédei–Megyesi/Szőnyi direction theorem (hypotheses mapped one by one; prime field is essential, extension fields marked INVALID) this yields the dichotomy — either every selection is collinear (the pencil case, controlled by zero-counting: 0/82 violations), or `|B| ≤ 2·min_λ|λ(L)| − 3 ≤ 2|L| − 3`. That is **linear** in the list size against the project's existing **quadratic** capacity-free bound `|B| ≤ κ_max + |L|(|L|−1)`, and capacity-free. Zero violations in 211/211; 14 collinear instances violate it, which is why the first arm cannot be dropped.
5. **Honest limitation, measured not guessed:** on the recorded micro-instances (`p ≤ 19`) `min_λ|λ(L)| ≥ (p+3)/2`, so the new `|B|` bound is true but vacuous there; its content lies in the large-field/short-list regime.
6. **Sharpness:** an actual MCA configuration attains the Rédei–Megyesi extremum — `RS[6,3]/F7`, `e=2`, `|B| = 7 = p`, a planar non-collinear selection with exactly `|D| = 5 = (p+3)/2` (verified by isolated recomputation over all 64 selections). Consequently `|D| ≥ |B|` is refuted (18 instances) and no direction-counting bound better than `|B| ≤ 2|D| − 3` is available.

Every conclusion is classified PROVED / REFUTED / EMPIRICALLY SUPPORTED / OPEN, and the report ends with exactly one recommended next mission — "RÉDEI–SZŐNYI MCA DIRECTION BOUND", sharpened so that the object to bound is the projected ball `min_λ |λ(L)|` rather than `|L|`, plus discharging the collinear arm.


# Summary of changes for run c9ec1ae9-32f7-47ce-b71b-6e7a3030d98a
**Answer: CASE B — the secant directions never leave `L(f₁,2e)`, and cannot.**

Deliverable: `Q_GEOMETRY_MINIMAL_REPORT.md` (the only report created, as requested), backed by the new exact-arithmetic measurement `analysis/q_geometry_minimal_cut.py` with transcript `analysis/q_geometry_minimal_cut_output.txt`. No Lean was written or modified, no axiom, no `sorry`/`admit`, no Johnson/list-size machinery, no broad sweep; the frozen items (support geometry, occupancy, κ-charging, list decoding) were not reopened.

1. **Instances checked: 1247** with `#Bad ≥ 2` (612 under the recorded degeneracy-filtered witness convention, 635 with the unfiltered convention), over the recorded RS families up to `p = 19`, `n = 7`, plus three non-RS controls. Inside each instance the check is exhaustive: every base point `γ₀`, every witness `c₀`, every `γ ≠ γ₀`, every witness `c_γ`.
2. **Exact arithmetic only** — Python integers mod a prime, no floats.
3. **Does `Q` ever leave `L`? No: 0 / 1247.** And this is not luck: the containment is the already-established secant lemma (`(γ−γ₀)(f₁−q)` is the difference of two `e`-close residuals, plus scalar invariance of the weight), so the CASE-A branch is empty a priori. The same one line is symmetric in the two endpoints, so the *full* pairwise direction set satisfies `D(B) ⊆ L` for free — that question needs no separate experiment.
4. **Smallest violating witness: none exists.**
5. **CASE-B follow-up measured (and only that):** for a single base point `Q` never exhausts `L` when `|L| ≥ 2` (0 / 1247); the union over all base points and witness selections *can* exhaust it (22 instances, largest `|L| = 22`, at `RS[4,3]/F5`, `e=1`, `f₀=0`, `f₁=(0,0,0,1)`, `#Bad=5`). Important caveat recorded: `|Q| ≤ |B|−1` holds by definition, so in 1234 of the 1247 instances the observed properness is cardinality-forced and carries no geometric content — substituting `|Q|` for `|L|` in `|B| ≤ κ_max + |L|(|L|−1)` is circular and yields nothing. In the only 13 instances where properness is *not* cardinality-forced, the direction set collapses to `|Q| = 1` (the bad set is one pencil member).

The report separates PROVED / REFUTED / OPEN explicitly and closes with the single best next question: whether `|Q|` admits a bound independent of `|B|` (or, dually, whether `|Q| ≥ 2` is possible when `#Bad − 1 ≥ |L| ≥ 2`) — the fork between a Rédei-type direction-counting gain and moving to the incidence structure `{(γ, q(γ))}`.

All work is committed and pushed.

# Summary of changes for run f9b224c9-f38d-440e-9f4d-fc2761969156
Mission executed under the stated FREEZE: **no Lean source was created or modified, no axiom added, no `sorry`/`admit`, no Johnson/list-size argument, no broad scan, no new file in the repository other than the requested one**. The single deliverable is `MINIMAL_CHARGING_THEOREM.md`. (Small exact finite checks of the *derived* lemmas were run outside the repository; every claim labelled PROVED carries a full human-checkable proof in the document, and no numerical result is used as evidence.)

**Answer to the question that drove the mission — is `Σ_q κ(q)` only a crude union bound?** Yes, and now exactly quantifiably so.

1. **Core structure (proved).** After basing at one point `p₀=(γ₀,c₀)` of the tube `T = {(γ,c) ∈ F×C : wt(f₀+γf₁−c) ≤ e}`, the pencil of affine `C`-lines through `p₀` *partitions* `T` minus its base fibre, and the bad set is the projection of `T`. The "charging map" is precisely this partition followed by projection; injectivity is a tautology, and the real content is membership (secant lemma + two exact affine identities).
2. **T2 is an identity, not an inequality:** `B = ⋃_{q∈L} Γ(u_q,q)`, with `Γ(u_q,q) = {γ₀}` for every `q ∉ L`.
3. **Exact form of T3 (main new theorem):** `Σ_{q∈L}(|Γ(u_q,q)|−1) = Σ_{γ∈B∖{γ₀}} N(γ) = |T| − N(γ₀)`, where `N(γ)` is the local decoding multiplicity; hence `|B| = 1 + Σ_{q∈L}(|Γ(u_q,q)|−1) − Σ_{γ∈B∖{γ₀}}(N(γ)−1)`. So the based capacity sum is literally the fibre-counting bound for the tube, and all non-triviality lies in the capacity estimate and the size of `L`.
4. **Impossibility result:** an unconditional geometric deficit `Δ>0` improving the κ-bound **cannot exist** — the maximal admissible `Δ` equals the excess decoding multiplicity, which vanishes identically whenever `2e < d(C)` (there the bound is an exact equality). Forced pencil overlap is *equivalent* to forced non-unique decoding.
5. **Pairwise intersections:** overlap away from the base point forces both `wt(q−q′) ≤ 2e` and non-unique decoding there; a universal constant `C(e)` is **refuted** by an explicit counterexample where the intersection is all of `F`; and a genuine second-order theorem holds — the intersection of two pencil members is a *first-order* line-in-a-ball set of the doubled configuration in `V⊕V` at radius `2e` (with a `k`-fold generalisation), giving `|Γ_q ∩ Γ_{q′}| ≤ chargeCap(2e, d(f₁,q)+d(f₁,q′))`.
6. **Minimal hypotheses (audited line by line):** the pencil and multiplicity identities need only that `C` is a subspace and hold for an *arbitrary* closeness predicate — no weight at all; the secant lemma needs exactly subadditivity plus invariance under nonzero scalars (true for Hamming and for the rank metric; for genuine norms one gets a scaled version with radius `2e/|γ−γ₀|`); the Hamming/coordinate structure is used **only** in the capacity counting lemma. Reed–Solomon structure is used nowhere; minimum distance only in the unique-decoding corollary.
7. **A new, capacity-free bound (proved, any field, any dimension):** the witness points form a point set in `F×C` all of whose determined directions lie in `L`, giving `|B| ≤ κ_max + |L|(|L|−1)` — incomparable with the κ-bound, and Johnson-free.

The document also contains the T1/T2/T3 comparison chain with each loss named, the modular Lean skeleton with per-file statements and difficulty for a later formalisation round, an explicit PROVED/REFUTED/CHECKED/OPEN separation, the requested 10-point final report, and an honest level assessment (Level 2 attained; Level 3 attained in the form of a full understanding of the union/intersection geometry plus an impossibility proof for the hoped-for improvement; Levels 4–5 not attained, with the precise next question stated).


# Summary of changes for run a6d3c769-03a8-45ef-96e3-4e20702afde3
Wykonałem misję „FIND THE CHARGING MAP" ściśle w zadanym trybie: **żadnego pliku Lean nie ruszyłem**, nic nie formalizowałem, nie dodałem aksjomatów, nie wracałem do Johnsona ani do invariantów rank/kernel/image, nie robiłem szerokiego przeszukiwania invariantów. Arytmetyka wyłącznie dokładna (liczby całkowite mod p), bez floatów; jeden przebieg 1 min 10 s, dane zapisywane po każdej rodzinie. Zacommitowane i wypchnięte artefakty: `KAPPA_CHARGING_MAP.md`, `analysis/kappa_charging_map.py`, `analysis/kappa_charging_map_output.txt` (dane per-rodzina lądują w `analysis/kappa_charging_data/`, nieśledzone przez git).

**Wynik: mechanizm został znaleziony — i to nie jest problem skojarzeń (matching).**

Reguła (kandydat „q wyznaczone przez przesunięcie błędu"): ustal bazowy zły parametr γ₀ z świadkiem c₀; dla każdego innego złego γ ze świadkiem c_γ połóż q(γ) = (c_γ−c₀)/(γ−γ₀) ∈ C, u_q = c₀ − γ₀q, i naładuj γ do slotu „γ" w zbiorze pojemności Γ(u_q,q) = {γ' : wt((f₀−u_q)+γ'(f₁−q)) ≤ e}.

Powód, dla którego slot nie może być użyty dwa razy, jest kanoniczny i geometryczny: **slot to sam parametr γ** — zbiór pojemności jest zbiorem parametrów prostej, więc iniektywność jest tautologią etykiet; dowodu wymaga nie iniektywność, lecz przynależność (q(γ) ∈ L(f₁,2e); γ ∈ Γ(u_q,q); γ₀ ∈ Γ(u_q,q)). Ostatni punkt jest strukturalnym powodem, dlaczego dokładnie **jeden** punkt ucieka ładowaniu: wszystkie realizowane zbiory pojemności tworzą **pęk przechodzący przez (γ₀,c₀)**, więc dostępna pojemność kierunku to κ(q)−1, a nie κ(q). Globalne „+1" i lokalne „−1" to ten sam obiekt liczony dwukrotnie.

Weryfikacja eksperymentalna (Faza 1/3): 3 296 instancji w reżimie luki, w tym rodziny **spoza poprzedniego skanu** (RS[6,2]/F₁₇, RS[6,2]/F₁₉, RS[7,3]/F₁₁ oraz trzy **losowe kody liniowe**, nie-RS — mechanizm nie korzysta ze struktury Reed–Solomona) plus 211 najtrudniejszych instancji z poprzedniej rundy. Sprawdzone jawnie dla **każdego** wyboru punktu bazowego γ₀ ∈ Bad (12 574 wyborów) i dla 2 052 alternatywnych wyborów świadka (świadek nie jest jednoznaczny w 684 instancjach): wszystkie osiem warunków (V1–V8) bez ani jednej awarii. Klasyfikacja: **A = 3296, B = 0, C = 0** — brak kontrprzykładu do nierówności i brak przypadku, w którym kanoniczne ładowanie zawodzi. Raport zawiera jawne ślady ładowania (tabelka γ | c_γ | q | d(f₁,q) | κ(q) | Γ(u_q,q)) dla obu instancji dokumentowanych w poprzedniej rundzie.

Faza 4: dodatkowe dane lokalne κ(q,q') **nie są potrzebne** — mechanizm domyka się na samym κ(q). Ujawniły się natomiast dwa ostrzejsze warianty wewnątrz tego samego mechanizmu: pojemność „bazowa" 1+Σ(|Γ(u_q,q)|−1) (0 naruszeń, równość w 3 221/3 296) oraz **ograniczenie pękowe** #Bad ≤ |⋃_q Γ(u_q,q)| (0 naruszeń, równe #Bad w 3 290/3 296). Jedynym źródłem luzu jest przecinanie się dwóch zbiorów pojemności poza punktem bazowym — to właśnie konkretna treść ewentualnego „κ(q,q')". Porównanie z już udowodnionym w projekcie ograniczeniem pakującym: κ-ładunek jest ostro mniejszy w 3 215 instancjach, równy w 81, nigdy gorszy.

W raporcie zapisałem **schemat twierdzenia** (S1–S5 + T) z najsłabszymi hipotezami, jakich argument faktycznie używa: dowolne ciało, dowolna podprzestrzeń C, dowolny podzbiór B parametrów e-bliskich (więc także `badSet` projektu z filtrem degeneracji), trzy własności wagi Hamminga; **bez** minimalnej odległości, bez struktury RS, bez związku e z n i bez jakiegokolwiek ograniczenia na |L|. Konkluzja: B ≠ ∅ ⇒ |B| ≤ 1 + Σ_{q∈L(f₁,2e)}(κ(q)−1), oraz bezwarunkowo |B| ≤ max(1, 1+Σ_{κ(q)≥2}(κ(q)−1)). Zgodnie z poleceniem zatrzymałem eksperymentowanie na tym etapie — schemat jest gotowy do przyszłej rundy formalizacyjnej w Lean.

Wyraźne zastrzeżenia w §7 raportu: nic tu nie jest twierdzeniem formalnym (dopóki nie zostanie zweryfikowane w Lean, pozostaje hipotezą ze szkicem dowodu), mechanizm nie ogranicza |L|, κ nadal nie jest monotoniczne ani kompletne, wszystkie liczby dotyczą przetestowanych rodzin (e ∈ {1,2}, n ≤ 7, p ≤ 19), i nie stawiam żadnych tez wydajnościowych.

# Summary of changes for run 5c49044c-bd5d-4d9b-bf1b-9924c6f1d1c0
Ran the canonical MCA state probe exactly as specified: a discovery experiment only — no Lean file was touched, no theorem proved, no axiom added, no `sorry`, no Johnson/list-size search, and no rebuild of the project. Exact integer/rational arithmetic throughout (no floats), reusing the existing instance and collision-pair data.

Deliverables (all committed and pushed):
- `CANONICAL_MCA_STATE_PROBE.md` — the report;
- `analysis/canonical_mca_state_probe.py` — the probe (33 s runtime on the existing cache);
- `analysis/canonical_mca_state_probe_output.txt` — the exact saved output.

Method. The strongest collision pairs were re-selected explicitly: the 26 pairs (out of the 291 with first-order vector, A and list-distance multiset pinned) on which the entire slope-indexed second-order sub-vector, support-hypergraph isomorphism type included, is constant while #Bad differs. Candidate canonical objects were inventoried and classified, then tested on those pairs.

Answer to the mission's question: YES — OUTCOME A, with explicit limits.

The surviving object is the canonical slope-capacity profile: for each q in L(f₁,2e), κ(q) = max over codewords u of the number of γ with wt((f₀−u)+γ(f₁−q)) ≤ e, recorded as the multiset {(d(f₁,q), κ(q))}. It selects no witness, no base point, and never consults the bad set. Experimental facts on the tested finite families: it separates 26/26 hard-core pairs (and 268/291 in the strongest regime) with equal profile length in every hard-core pair, so the separation is structural rather than size accounting; it still varies in 34/96 groups once (signature, A, #Bad) is pinned — the property occupancy lacked; the derived witness-free quantity 1 + Σ(κ(q)−1) upper-bounds #Bad with 0 violations on 221 instances and is strictly smaller than the proved (e+1)A+1 on 41 of them (once by exactly 1). It is not complete: 23/291 pairs remain unseparated, with the smallest explicit counterexample recorded; it is also non-monotone in #Bad, and its index set is still L, so |L| has been refined, not eliminated. These caveats are stated in the report.

Strongest negative result of the round, reported alongside: every dimensional canonical invariant — the whole kernel/image/quotient/rank-jump/intersection/joint-constraint-space layer, plus the error-configuration space and its intersection with the code — is blind on all 26 hard-core pairs and constant at fixed (signature, A, #Bad). So the surviving intrinsic state is a capacity (a counting datum per list element), not a rank.

The report labels every statement as EXPERIMENTAL FACT, CONJECTURE (with the argument sketch for the κ-charging inequality, explicitly not proved) or PROVEN THEOREM, and makes no claim beyond the tested families (RS codes over F₅, F₇, F₁₁, F₁₃ with e ∈ {1,2}). No previously established result, definition or theorem was modified.

# Summary of changes for run 9d3d70e6-748b-4810-aaff-2775b01a85b3
Executed the requested occupancy elimination test — an experimental round only: no Lean was touched, no axioms added, no formalisation, exact integer/rational arithmetic throughout (no floats), runtime ~10 s.

New artifacts (committed and pushed):
- `OCCUPANCY_ELIMINATION_REPORT.md`
- `analysis/occupancy_elimination_test.py`
- `analysis/occupancy_elimination_test_output.txt` (saved exact output)

Phase 1/Phase 2 were reused verbatim from the earlier second-order round, so the pairs tested are exactly the previously found collision pairs: 38 084 gap instances, 256 pairs (A free), 291 (A pinned), 291 (A + list-distance multiset pinned), 221 distinct instances.

STEP 1 — definition of c(γ,q). The witness codeword is **not** unique: 481 of the 1 460 bad parameters in these instances have ≥ 2 witnesses (max 3), affecting 151/221 instances. Three conventions were therefore computed: W1 = lex-least witness, slopes against the smallest bad parameter (the object of the earlier §4), an indicator; W2 = all witness pairs against the same base point, a count; W3 = incidence with the base-point-free set of witness lines, a fully convention-free indicator. An unambiguous c(γ,q) does exist (W3), so the test proceeded.

STEP 2/3 — the full occupancy matrix, compared up to row/column permutation, separates **every** collision pair: 256/256, 291/291, 291/291, in all three conventions. But in all 838 comparisons the separation is achieved by matrix **shape** alone (0 pairs of equal shape), because the rows are indexed by the bad set, so #rows = #Bad. Two identities were verified with 0 violations over all 221 instances: #columns(W1) = A and Σ_q |class(q)| = #Bad + A − 1. With A pinned, occupancy and #Bad determine each other by arithmetic.

Reduced statistics (regime II, W1): nonzero entries 291/291 (this is exactly the identity above), row-sum and column-sum multisets 291/291 (length/sum equal #Bad), row concentration 291/291, maximum entry **0/291** — blind. The statistics that are not pure size accounting (max entry; the count-valued conventions W2, W3) are the worst separators.

Size-free converse test: grouping instances by (first-order signature, A, #Bad) gives 96 testable groups; the W1 occupancy matrix is constant on **all 96** — occupancy carries no state beyond #Bad. W2/W3 do vary (56 and 69 groups) but are likewise indexed by the bad set, hence cannot bound it.

Answer to the stop-rule question — Is occupancy the actual missing state variable? **No.** It separates only tautologically (by size), and in the reverse direction it is an exact function of the already-pinned data plus #Bad. The occupancy direction is closed; any bound beyond the proved A − 1 ≤ #Bad ≤ (e+1)·A + 1 must use data not indexed by the bad set. Per the stop rule, nothing was done towards A_E, intrinsic geometry, list decoding or topology. Scope caveats (small RS families over F₅, F₇, F₁₁, F₁₃ with e ∈ {1,2}; no theorem, no claim for larger n or the M31 parameters) are recorded in the report.

# Summary of changes for run 33f7200f-78c3-4ae9-b4f7-4e713cab74de
Ran the requested collision-pair experiment on second-order slope geometry. No Lean file was touched: no new axioms, no `sorry`, no formalisation (the stop condition for formalising — exactly one surviving invariant — was not met).

**Deliverables** (committed and pushed): `SLOPE_GEOMETRY_SECOND_ORDER_REPORT.md`, the script `analysis/second_order_slope_geometry.py` and its full log `analysis/second_order_slope_geometry_output.txt`. All arithmetic is exact over prime fields (integers mod p, exact rationals where a ratio is used); no floats enter any verdict. Phase-1 data is persisted per (family, radius) to `analysis/second_order_phase1/` and regenerated on demand (8.6 MB, not committed).

**Phase 1.** 38 084 gap instances ((d−2e)/2 ≤ w ≤ 2e) over RS[4,2]/F₅ … RS[6,2]/F₁₃, e ∈ {1,2}; 18 473 with #Bad ≥ 2 and A ≥ 2. Max #Bad = 11, max A = 9, max |L| = 136.

**Phase 2.** Collision pairs (identical first-order vector p,n,k,d,e,w,|L|,dim W,maxZeroW,dim Synd; different #Bad): 256 pairs / 21 signatures. Because A and #Bad determine each other up to a factor e+1, a stricter regime with A also pinned was added (291 pairs / 42 signatures), and a third with the list-distance multiset pinned as well (291 pairs).

**Phases 3–4.** For each of three natural readings of the witness support (two indexed by realised slopes, one by bad parameters) the full requested vector was computed — pairwise intersection energies and histogram, degree moments D₁,D₂,D₃, d_max, N_j, incidence rank over F_q and F₂, Gram matrix statistics, pattern multiplicity, interaction-graph components/edges/triangles — plus, as the maximal conceivable second-order invariant, the complete isomorphism type of the support hypergraph.

**Answers to the three success questions.**
1. Second-order invariants separate collision pairs only partially, never completely. Best slope-indexed separator: the full isomorphism type (252/256 and 265/291). The intersection energy E₂ specifically proposed separates at most 229/291 and is non-monotone (188 up / 41 down).
2. There is no weakest separator, since no invariant separates all pairs. No slope-indexed invariant is monotone in #Bad, so none supports a candidate inequality.
3. On the families tested the geometric-interaction route is closed, with explicit evidence: pairs of instances agreeing in all first-order invariants, in A, and in the list-distance multiset, whose slope-support configurations are isomorphic as hypergraphs, yet with different #Bad (4/256 and 26/291 such pairs). Two are quoted in full in the report with their f₀, f₁ data; for one of them the witness codeword is unique for every bad parameter, so the conclusion is independent of the witness-selection convention. The mechanism is identified: the only differing quantity is the per-class occupancy multiset, related to the target by Σ|class(q)| = #Bad + A − 1, and occupancy is exactly what the already-proved packing bound controls.

An appendix records a pairwise-budget probe over all 38 084 instances: passing from A to A(A−1) buys nothing — every right-hand side that fails for A fails for A(A−1) on the same worst instance, and the only unviolated forms are those implied by A ≤ |L|. All negative statements are exact counterexamples on the recorded instances, not general theorems; nothing here bounds |L(f₁,2e)| and no Johnson/capacity statement was used or produced.


# Summary of changes for run a8288a46-0293-4e91-82d4-91d504bb26ae
Wykonałem misję „List Geometry Probe" — ale z jedną korektą, o którą sam Pan prosił („jeśli znajdziesz lepsze rozwiązania, ulepsz instrukcję"): eksperyment rozróżniający nie tylko odrzucił kolejne kandydatury invariantów, lecz doprowadził do **nowego, udowodnionego twierdzenia**, więc nie zatrzymałem się na samym raporcie.

**1. Eksperyment (dokładna arytmetyka, bez floatów, bez losowych werdyktów)**
- `analysis/list_geometry_frontier.py` (+ zapisany output): 34 514 instancji w luce `(d−2e)/2 ≤ w ≤ 2e`, jedenaście rodzin RS nad F₅, F₇, F₁₁, F₁₃ (wyczerpująco po reprezentantach warstw w małych rodzinach).
- `analysis/achieved_slopes_probe.py` (+ output): 2 033 instancje z `#Bad ≥ 2`, pomiar liczby **realizowanych nachyleń** `A`.
- Wynik rozstrzygający: invarianty samej listy (parowe zbiory zer i ich przecięcia, `dim W = dim span(L−q₀)`, `max_{0≠p∈W}|Z(p)|`, wymiar przestrzeni syndromów) są stałe w kubełkach, w których `#Bad` się zmienia — nie niosą informacji. Natomiast **struktura upakowania wewnątrz klasy nachylenia** niesie.

**2. Nowy mechanizm i twierdzenia (Lean, `RequestProject/Root/CodingTheory/ChargingCapacity.lean`)**
Wewnątrz jednej klasy nachylenia świadkowie są afiniczne, więc każdy zły parametr rozwiązuje równanie `f₀+γf₁ = h+γq` na co najmniej `d(f₁,q) − e` z `d(f₁,q)` pozycji, na których `f₁ ≠ q`, a różne parametry nigdy nie robią tego na tej samej pozycji. Klasa jest więc rozłącznym upakowaniem. Udowodnione (build czysty, bez `sorry`, aksjomaty dokładnie `propext, Classical.choice, Quot.sound`, plik ma własny audyt `#print axioms`):
- `card_le_chargeCap` — abstrakcyjny lemat upakowania (bez kodu, bez odległości minimalnej, bez RS): `|klasa| ≤ chargeCap e (d(f₁,q))`, gdzie `chargeCap e m = m` dla `m ≤ e` i `min(m, ⌊m/(m−e)⌋)` dla `m > e`;
- `card_badSet_le_sum_chargeCap` — `#Bad ≤ max(1, Σ_{q∈Q} chargeCap e (d(f₁,q)))`, bezwarunkowo, dla dowolnego kodu liniowego nad alfabetem-modułem;
- `card_badSet_le_succ_mul_card` — `#Bad ≤ max(1, (e+1)·|Q|)`: poprawa poprzedniego czynnika `2e` do `e+1`, i bez założenia, że elementy `Q` są blisko `f₁`;
- `card_badSet_le_two_mul_card_of_two_mul_le` — `#Bad ≤ max(1, 2·|Q|)`, gdy wszystkie bliskie słowa kodowe leżą w odległości `> 3e/2` (m.in. skrajny przypadek `d(f₁,q) = 2e`);
- wersje dla jawnej listy oraz realizacje Reed–Solomona (`rs_card_badSet_le_sum_chargeCap`, `rs_card_badSet_le_succ_mul_card`).
Wszystkie te bounds przeszły 34 514 instancji bez ani jednego naruszenia.

**3. Gdzie argument się zatrzymuje (wynik negatywny, precyzyjny)**
`A ≤ #Bad − 1` oraz `#Bad ≤ (e+1)·A + 1`, więc ograniczanie liczby realizowanych nachyleń jest *tym samym problemem* co ograniczanie `#Bad`. Mechanizm ładowania/upakowania został więc wyczerpany: jedyną pozostałą dźwignią jest ograniczenie `|L(f₁,2e)|` (Johnson / list decoding), którego nie dowodzę. Zmierzone kontrprzykłady: `A ≤ e+1`, `A ≤ 2e`, `A ≤ w+1`, a nawet `A ≤ n` są fałszywe (np. RS[6,3]/F₁₁, `e = 2`, `n = 6`, `A = 9`, `#Bad = 10`).

**4. Dokumentacja i higiena**
Nowy raport `LIST_GEOMETRY_FRONTIER.md` (mechanizm, tabela invariantów, minimalne kontrprzykłady, kurs wymiany „bound na listę → bound na `#Bad`", werdykt), odnośnik dopisany w `LIST_GEOMETRY_PROBE.md`, nowa sekcja §84 w `RESULTS.md` i wpisy D84.1–D84.3 w `DISCREPANCIES.md` (jawnie: brak jakiegokolwiek bound na `|L|`, brak twierdzeń typu Johnson/capacity, brak claimów wydajnościowych; hipotezy nieobalone-lecz-nieudowodnione oznaczone jako hipotezy). `ARISTOTLE_SUMMARY.md` nietknięty, istniejące twierdzenia i definicje niezmienione, żadnych nowych aksjomatów. Pełny `lake build` przechodzi (8 206 zadań), brak `sorry`/`admit`. Wszystko zacommitowane i wypchnięte.

# Summary of changes for run 2c224b6b-8737-4469-9e04-7fd73bba8be7
Mission completed as a diagnostic-then-extension programme. Full `lake build` passes (8204 jobs), no `sorry`/`admit`, no new axioms — every new declaration reports exactly `[propext, Classical.choice, Quot.sound]` (audit block appended to `RequestProject/Main.lean`). `INDEX.md`, `PROJECT_MAP.md` and the existing Circle-FRI results were left untouched.

**Phase 1 — what `ZeroBounded` really is.** New Lean file `RequestProject/Root/CodingTheory/ZeroLocusListSize.lean`:
- `FarFrom C r f` ("d(f, C) > r") and `card_badSet_le_one_of_farFrom` / `epsMCA_le_one_div_of_farFrom`: the whole `#Bad ≤ 1` mechanism follows from that single distance inequality, with no side conditions (`f₁ ∉ C` and `2e < |ι|` are consequences);
- `farFrom_iff_exists_zeroCountLt`: the previous hypothesis package (`ZeroCountLt C t f₁` plus `2e + t ≤ |ι|`) is *equivalent* to `d(f₁,C) > 2e`. So the earlier certificate is a repackaging of the standard unique-decoding argument, and `ZeroBounded` is (as already known) minimum distance. No novelty is claimed for it;
- the implication from the old hypothesis is *strict*: `Separation.farFrom_sepWord` / `card_badSet_le_one_sep` / `no_zeroBounded_ambient` give a five-position instance over the field of 5 elements where the new theorem applies and no ambient zero-bounded code can exist.

**Phases 2–3 — a list-size theorem with L > 1.** `card_badSet_le_hammingDistance`: for any linear code over any module alphabet, `d(C) ≥ d`, `q ∈ C`, `2e + 2·d(f₁,q) < d` ⇒ `#Bad ≤ d(f₁,q)`; equivalently `#Bad ≤ |ι| − |Z|` with `Z` the zero locus of `f₁ − q` (`card_badSet_le_card_compl_zeroLocus`). It covers exactly the regime the old theorem cannot see (second layer close to the code) and is attained at L = 2. Supporting results: `badSet_sub_codeword` (the bad set depends on the second layer only through its coset, i.e. its syndrome) and the hypothesis-free combination `card_badSet_le_two_mul_of_six_mul_lt_minDist` (`6e < d ⇒ #Bad ≤ max(1,2e)`), which improves the project's previous code-generic row `#Bad ≤ |ι|` under `3e < d`. Both regimes remain inside unique decoding; no Johnson or capacity claim is made.

**Phases 4, 5, 8 — experiments (exact integer arithmetic, no floating point).** Four scripts in `analysis/` with saved outputs: `zero_locus_list_size.py`, `zero_locus_list_size_targeted.py`, `zeroBounded_beyond_unique_decoding.py`, `circle_factor_two_check.py`. 783 830 instances over ordinary Reed–Solomon, random linear codes, folded Reed–Solomon and an exhaustive small scan: 0 violations of any proved bound; `#Bad = w = 2` attained (RS [10,4] over the field of 11 elements); the hypothesis `2e + 2w < d` shown necessary; a conjecture `#Bad ≤ max(1, L·2e)` survives all instances (recorded as conjecture only), while the variant `#Bad ≤ L·max(1,2e)` is refuted. The circle factor-2 question is answered B/D, not A: `finrank_le_of_zeroBounded` (Singleton: a zero-bounded code has dimension ≤ t) plus an exhaustive circle scan show the proved circle bound `#zeros ≤ 2t'` is *attained*, so the factor 2 is the dimension of the circle code (two polynomial layers), not a proof artefact; no separate parameter κ is introduced. Syndrome information is shown reducible (`badSet_sub_codeword`), so no syndrome library was built.

**Barrier (stop condition).** The two regimes leave the gap `(d−2e)/2 ≤ w ≤ 2e`, nonempty iff `d ≤ 6e`; inside it `#Bad` reaches `|F| − 1` in explicit instances, so no bound in `(e, w, d, |ι|)` can hold there. Crossing it needs control of the whole list of nearby codewords, not the zero locus of one difference — recorded as the honest entry point for any future Johnson work.

**Documents produced:** `ZEROBOUNDED_STATUS.md`, `ZERO_BOUNDED_FAILURE_MODE.md`, `ZERO_LOCUS_FRONTIER.md` (with the required final report: strongest theorem, strongest conjecture, strongest counterexample, current radius regime, recommended next mission), `ZERO_LOCUS_EXPERIMENTS.md`; plus `RESULTS.md` §82 and `DISCREPANCIES.md` D82.1–D82.3 recording the scope limits. All work is committed and pushed.

# Summary of changes for run b8754d5c-ae16-4e06-ab4d-774489ac38c4
Mission A (Circle-FRI prover-word lemma) plus the mandatory generality-extraction checkpoint are complete. Mission B was not started, per your instruction that it is deferred to a later phase. Full `lake build` passes (8203 jobs), no `sorry`/`admit`, no new axioms — every new declaration reports exactly `[propext, Classical.choice, Quot.sound]`.

**Step 1 — semantics fixed.** `CIRCLE_FOLD_SEMANTICS.md` states the fold map `J(x,y) = (x,−y) = p⁻¹`, the projected domain `π D = D.image (·.x)`, what a fold section is, both layers, the exact `ZeroCountLt` predicate and its instantiation, and — explicitly — that the second layer is `b(x)`, *not* `y·b(x)`. It also settles the `2e + t` vs `2e + 2t + 1` ambiguity with a table: the circle-code statement on `D` uses `2e + 2t + 1 ≤ |D|`, the post-fold statement on `π D` uses `2e + t ≤ |π D|`; `t` is a strict degree bound on the second layer, never an agreement slack.

**Step 2 — exact validation, no counterexample.** `analysis/circle_fold_prover_word_check.py` (exact integer arithmetic in `F_q`, no floats), output saved. 840/840 twin-coset instances and 4080/4080 arbitrary-domain instances confirm both layer identities; 420/420 confirm the layers do not depend on the chosen section; the one-round bad-set scan gives max `#Bad = 1` in the degree window (270 instances) and `#Bad = 0` below it (270 instances). The `y ≠ 0` condition is shown to be sharp. The earlier 172/172 experiment was re-run unchanged.

**Steps 3–4 — the lemma and the certificate.** `RequestProject/Root/CodingTheory/CircleFRIProverWord.lean`:
- `circle_fold_snd_eq_eval_b` — after the inversion fold, the second layer of the circle word `a(x) + y·b(x)` is the evaluation of the ordinary polynomial `b` on the projected domain (companion: `circle_fold_fst_eq_eval_a` gives `a`). Only `2 ≠ 0` and the two section conditions are used;
- `exists_circleFoldSection` — non-vacuity, from `∀ p ∈ D, p.y ≠ 0`;
- `circle_fold_secondLayer_zeroCountLt` / `circle_fold_secondLayer_is_polynomial` — the `ZeroCountLt` instance for the ordinary Reed–Solomon code on `π D`;
- `circle_fri_one_round_badSet_eq_empty` (deg b < k ⇒ empty bad set), `circle_fri_one_round_card_badSet_le_one`, `circle_fri_one_round_epsMCA_le_one_div` (ε_mca ≤ 1/|F|), and the concrete `circle_fri_one_round_epsMCA_le_two_pow_neg_128` (|π D| = 2²⁰, k = 2¹⁹, e = 262143, δ ≈ 0.2499990, deg b = 2¹⁹ ⇒ ε_mca ≤ 2⁻¹²⁸ for |F| ≥ 2¹²⁸).

Scope respected: one round, one line, one prover word of the stated form; no Circle-STARK library, no multi-round or capacity claim (recorded as D80.1/D80.2 in `DISCREPANCIES.md`).

**Step 5 — generality extraction checkpoint.** `GENERALITY_CHECKPOINT.md` classifies every fact used in Steps 3–4 as circle-specific, fold-specific, polynomial-evaluation-specific, zero-locus-general or formalisation artefact. The abstraction succeeded and is now Lean-checked in `RequestProject/Root/CodingTheory/ZeroLocusGeneral.lean`:
- `Alphabet.ZeroBounded V t` ("every nonzero word of V vanishes at fewer than t positions") and `zeroBounded_iff_minDistGe`, which shows this hypothesis *is* the minimum-distance statement `d(V) ≥ |ι| − t + 1`;
- the generic theorems `card_badSet_le_one_of_zeroBounded` / `epsMCA_le_one_div_of_zeroBounded`: `f₁ ∉ C`, `C ≤ V`, `f₁ ∈ V`, `ZeroBounded V t`, `2e + t ≤ |ι|` ⇒ `#Bad ≤ 1`, `ε_mca ≤ 1/|F|` — over an arbitrary linear code and arbitrary module alphabet;
- four instances all factored through it: ordinary Reed–Solomon, the circle code, the post-fold Circle-FRI round, and — as the abstraction test — the folded Reed–Solomon code with block alphabet `Fin s → F`, where `foldedRS_card_badSet_le_one` and `foldedRS_epsMCA_le_one_div` follow from the existing folded minimum-distance bound with no new mathematics;
- one formalisation artefact removed: `badSet_eq_alphabet_badSet` and `epsMCA_eq_alphabet_epsMCA` prove the polynomial-existential bad set of the univariate layer and the submodule-existential bad set of the generic layer are the same finite set and the same probability.

What did *not* generalise is recorded precisely: the zero bound itself is per-code input (root counting vs. norm counting — the factor 2 in `2t + 1` is the sole quantitative circle-specific ingredient), the prover-word lemma is per-fold, and the mechanism is confined to `2e + t ≤ |ι|`, i.e. inside unique decoding, so nothing here bears on capacity.

Documentation updated: `RESULTS.md` §80–§81, `DISCREPANCIES.md` D80.1/D80.2/D81.1, `CIRCLE_FOLD_SEMANTICS.md`, `GENERALITY_CHECKPOINT.md`. `INDEX.md` and `PROJECT_MAP.md` were left untouched as instructed. All work is committed and pushed.

# Summary of changes for run caf73b70-f517-4045-a39b-cd47f583e237
Mission "Circle / structured-layer bridge, falsification first" is complete. Full `lake build` passes (8201 jobs, no warnings), no `sorry`/`admit`, no new axioms — every new declaration reports exactly `[propext, Classical.choice, Quot.sound]`.

**1. Exact bridge theorem proved.** Route **C (abstract zero count)** was chosen and carried out.
- `RequestProject/Root/CodingTheory/ZeroCountSecondLayer.lean` — the strong `Bad` definition is untouched; the polynomial degree window of the earlier structured-second-layer theorem is abstracted into a single hypothesis `Alphabet.ZeroCountLt C t f` ("every codeword agrees with `f` on `< t` positions"). Proved: `Alphabet.card_badSet_le_one_of_zeroCount` (`2e + t ≤ |domain|` ⇒ `#Bad ≤ 1`, nothing assumed about the first layer), `Alphabet.epsMCA_le_one_div_of_zeroCount` (`ε ≤ 1/|F|`, radius-independent), and `Alphabet.badSet_eq_empty_of_snd_mem`.
- `RequestProject/Root/CodingTheory/CircleZeroCount.lean` — the circle instantiation: `circleWord` (restriction of `a(x) + y·b(x)`), `circleCode` (submodule of such words with `deg a, deg b < k`), the norm `a² − (1 − x²)b²`, and the key zero-count `card_circleZeros_le` (fibres of the x-projection matched against root multiplicities of the norm), giving `card_badSet_circle_le_one`, `epsMCA_circle_le_one_div`, and one concrete certificate `circle_epsMCA_le_two_pow_neg_128` (|D| = 2²⁰, k = 2¹⁸, rate 1/2, e = 262142, δ ≈ 0.2499981 ⇒ ε ≤ 2⁻¹²⁸).

**2. First counterexamples to the rejected bridges** (exact integer/Fraction arithmetic, `analysis/circle_bridge_falsification.py`, output saved alongside it):
- *Ordinary-polynomial identification refuted* (172/172 instances): a circle word is not an ordinary polynomial evaluation. First witness: field of 7 elements, D = {(2,2),(5,5),(2,5),(5,2)}, a = 4, b = 6, word (2,6,6,2).
- *Minimum distance alone refuted*: field of 31 elements, |D| = 8, k = 2, d = 4, e = 1 (so 3e < d) already gives `#Bad = 2`.
- *Characteristic 2 refuted*: over F₂, (a,b) = (1+X, 1) is a nonzero word with identically zero norm, so the zero count fails; the Lean theorems accordingly carry `(2 : F) ≠ 0`.
- *Slack necessity*: a reproducible witness (field of 31 elements, twin coset |D| = 8, k = 2, t = 3, e = 1) attains `#Bad = 2` exactly at `2e + 2t = |D|`, so the `+1` in `2e + 2t + 1 ≤ |D|` is not cosmetic.

**3. Comparison of the three formulations.** Ordinary-polynomial: false at the circle level (refuted above). Rank-two module: true but subsumed — the module structure is used only to bound the number of zeros, via the norm. Zero count: the weakest true formulation and the one the existing proof actually supports; it is now the stated general theorem, with the circle code as one instance.

**4. Does the one-round univariate certificate apply to the circle code?** No. The experiment separates the folded univariate instance from the circle instance in both directions (35/80 sampled instances differ), so the existing univariate one-round certificate cannot be transported. A separate circle certificate was proved instead.

**5. Next highest-value target.** A prover-word lemma deriving `f₁ = circleWord D a b` from one Circle-FRI round — the circle analogue of the existing univariate second-layer evaluation lemma. The experiment supports it (after the inversion fold `(x,y) ↦ (x,−y)` the second layer was the ordinary polynomial `b` on the projected domain in 172/172 instances), but it is not yet formalized, and until it is, no Circle-STARK soundness claim is made.

Documentation: `CIRCLE_BRIDGE_OBLIGATIONS.md` (semantic audit plus the phase-4/5 boundary checks), and new sections in `RESULTS.md`, `DISCREPANCIES.md`, and `SOTA_PLAN.md`. No circle-code library and no multi-round statements were built, per the mission's scope limits; the freeze list was respected throughout.

# Summary of changes for run 8c822852-473c-4fd6-b587-bd1604cfb806
Consolidation phase completed as requested — no new large constructions were started, and the freeze list was respected (no circle code committed, no Circle-STARK soundness work, no closed routes reopened, no multi-round FRI claim).

**Verification of the existing state**
- Full `lake build` runs clean: 8199 jobs, no errors.
- `rg` over `RequestProject/**/*.lean` finds no `sorry` and no `admit` in any proof position (all 111 textual hits are prose in docstrings, e.g. "no `sorry`", "admits").
- Working tree clean; everything committed and pushed.

**Documentation updates**
- `RESULTS.md` — new §78 "Session closure": a status table of what stands at the close of the phase (structured second layer §74 proved; FRI fold bridge §75 proved; one-round certificate `ε_mca ≤ 2⁻¹²⁸` at ρ = 1/2, δ ≈ 0.25 proved; coset-count bound `#Bad ≤ s` refuted §77; Circle-STARK an explicit open gap), plus the outcome of the small feasibility probe (§78.2).
- `SOTA_PLAN.md` — the FRI fold bridge is recorded as proved (§5), the one-round certificate as unconditional *given the fold hypothesis* (single-polynomial prover word of the stated degree; one round, one line), the Circle-STARK interface (§6) as the only missing bridge, and a closing "Phase status at session closure" section.
- `DISCREPANCIES.md` — new D78.1 (the circle code exists only as a scratch probe, nothing proved about it; the earlier negative audit D76.1 stands) and D78.2 (exactly what "unconditional" does and does not mean for the one-round certificate). The refutation of `#Bad ≤ s` and its three-coset witness were already recorded as P39 and remain the standing entry.
- `CIRCLE_STARK_INTERFACE_AUDIT.md` — new §7 recording the answer to the one small mission.

**Result of the small mission (circle code in 15–20 lines?)** The *interface* is indeed about a dozen lines: the circle code as the span of restrictions of `a(x) + y·b(x)` with `deg a, deg b < k`, a `Submodule F (↥D → F)` over the existing circle structure. This was elaborated only in a scratch check and deliberately **not** added to the repository, because it proves nothing on its own. The substantive finding recorded for future work is the cheapest entry point: the MCA layer already in the repository (`Root.CodingTheory.Alphabet.card_badSet_le` / `epsMCAmax_le`) is code- and alphabet-generic, so a circle code would inherit `ε_mca ≤ n/|F|` as soon as a minimum-distance bound for it is proved; the sharp `1/|F|` additionally needs identifying the circle fold's second layer with the odd part of the x-projection. Both are left as the open Circle-STARK gap, and no Circle-STARK certificate is claimed.

# Summary of changes for run bd1b936a-61bc-4363-a08a-11b0236f4568
## What I did

### Step 1 — consolidation (done)

* **Slice scan finished.** The scan of the slice `e + 1 > s` (the only regime where the conjectured coset-count bound `#Bad ≤ s` would add anything to the proved `#Bad ≤ e + 1`) now runs to completion for `q ∈ {5,…,29}` — 68 363 instances, exact integer arithmetic. `q = 31` needs far longer and was not run; the script now takes the prime list on the command line and the saved output (`analysis/multicoset_monomial_sharp_slice_output.txt`) is the completed run. The result is **negative for the conjecture**: 18 violations on three cosets, `max #Bad = 4`.
* **`RESULTS.md`**: section numbering fixed (the three sections that restarted at 31 are now 71–73) and four new sections added — §74 structured second layer, §75 the FRI fold bridge, §76 the interface audit result, §77 the refutation of `#Bad ≤ s`.
* **`SOTA_PLAN.md`**: new status sections for the degree trichotomy (with the new `ρ = 1/2` certificate row) and for the FRI fold; the coset-count route moved to the closed list.
* **`DISCREPANCIES.md`**: new entries P37–P39 and D74.1–D76.1, including the explicit note that the degree window is essential and that the three-coset counterexample lies exactly outside it, and the scope caveats (per-line, not over all lines; inside unique decoding; single-polynomial prover).
* Full `lake build` is clean, no `sorry`/`admit` in any changed file, and every new declaration is audited in `RequestProject/Main.lean` with `#print axioms` showing only `propext, Classical.choice, Quot.sound`. No axioms added.

### Step 2 — interface test (done, with new mathematics)

Rather than only recording an answer, I built the missing bridge for the univariate FRI generator, in `RequestProject/Root/CodingTheory/FRIFoldStructured.lean`:

* one FRI round splits the tested word as `f(x) = f_even(x²) + x·f_odd(x²)`; the two layers are defined literally in that form through a square-root section of the folded domain (whose existence is proved for the genuine FRI geometry);
* **`friSnd_eval`**: if the tested word is the evaluation of a single polynomial `P`, the second layer is the evaluation of a single polynomial — the odd part of `P` — so the structural hypothesis is *automatic*, not an extra assumption;
* the exact degree bookkeeping: `deg P = 2m+1 ⇒ deg(oddPart P) = m`, and `deg P < 2n ⇒ deg(oddPart P) < n`;
* consequently the trichotomy becomes a condition on `deg P`: `deg P < 2k` gives an **empty** bad set; `deg P = 2m+1` with `k ≤ m < t` and `2e + t ≤ |D|` gives `#Bad ≤ 1` and `ε_mca ≤ 1/|F|`;
* a concrete round certificate: folded domain `2²⁰`, `k = 2¹⁹`, `e = 262143` (`δ ≈ 0.2499990`), word of degree `2²⁰+1` ⇒ `ε_mca ≤ 2⁻¹²⁸` for `|F| ≥ 2¹²⁸`.

I also closed the first regime of the trichotomy in `StructuredSecondLayer.lean`: `badSet_eq_empty_of_codeword_snd` (`deg g < k ⇒ #Bad = 0`).

**Circle-STARK, explicitly:** the certificate does **not** apply, and the failing condition is not one of the degree inequalities — it is prior to them. The repository defines the circle group, the twin-coset domain and the circle FFT, but no circle code and therefore no circle bad set, so the hypotheses cannot even be stated there. The minimal missing structure (circle code on a twin coset; the 2-to-1 `x`-projection into even/odd univariate parts; identification of the circle fold's second layer with the odd part) is recorded in `CIRCLE_STARK_INTERFACE_AUDIT.md` §6 and `RESULTS.md` §76.

### Extra result

The open conjecture `#Bad ≤ s` is now **refuted and formalized** (`MulticosetSharpSliceWitness.lean`): over `ZMod 17` with `D = H ∪ 2H ∪ 3H` (`H` of order 4, `|D| = 12`), `k = 2`, `e = 3`, monomial packet `f₀ = t⁸`, `f₁ = t⁹`, the bad set is `{6,7,10,11}`, so `#Bad = 4 > 3 = s` inside the regime `3e + k ≤ |D|`. Verified beforehand by two independent exact engines (`analysis/multicoset_sharp_slice_witness.py`). Note `#Bad = 4 = e + 1`, so the proved general bound is untouched and is tight there.

Nothing on the freeze list was touched: the strong MCA definition, the folded-RS capacity results and the binomial fallback are unchanged, no closed route was reopened, and no claim beyond the stated hypotheses is made. All work is committed and pushed.

# Summary of changes for run 977ae616-697d-45c1-a14d-467dd92e1bf5
## What I did

I completed the two open strands of work and left the project building cleanly with no `sorry` and no new axioms.

### 1. Path A (bound the codeword locus by list size) — refuted, path closed

Numerical validation was run first, in exact arithmetic (no floats), as instructed:

- `analysis/codeword_locus_list_size_check.py` (+ saved output) and `analysis/codeword_locus_counterexample_search.py` (+ saved output).
- Result: the hypothesis `|codewordLocus(G)| ≤ listSize · deg_Y G` is **false**. In genuine interpolant instances (q = 101/127, n = 6–8, k = 2, unique-decoding thresholds so the list size is 1) the agreement-carrying codeword locus of the repeated part reaches 3 against a predicted bound of 1; 10 certified counterexamples out of 40 scanned. An explicit family, `G = (X−Z)·Y + (X−Z)(X+Z) + c(Z)`, has a locus of size `deg c` — up to the whole field — with list size 1 and `deg_Y G = 1`. Only the `Z`-degree controls the locus.
- Per the instruction's step 4, the obstruction is recorded, the conditional theorem is kept unchanged, and no Chojecki / subresultant work was started. An audit of the parametric-list machinery is in `analysis/parametric_list_status.md`.

### 2. Unique-decoding correlated agreement via double counting — proved, with a correction

New file `RequestProject/Root/CodingTheory/UniqueDecodingMCA.lean` (imported and audited from `RequestProject/Main.lean`). The argument uses only finite double counting on pairs `(γ, x)`: no parametric list, no interpolant, no multiplicities.

- `exists_correlatedAgreement_of_two_goodZ` — two `e`-close parameters of a line already determine one codeword pair agreeing with `(f₀, f₁)` on at least `|D| − 2e` positions.
- `exists_mem_polyAgreement_sdiff_of_isBad` — every bad parameter owns a position outside that common agreement set.
- `card_badSet_le_succ_radius` — **`#bad ≤ e + 1`** whenever `3e < |D| − k + 1`. This sharpens the previously available count `|D|` in the same regime; the private parts of distinct bad parameters are disjoint, which closes the count.
- `epsMCA_le_succ_radius`, `epsMCAmax_le_succ_radius` — density form, `ε_mca ≤ (e+1)/|F|`.
- `not_forall_card_badSet_le_one` — the **literal** requested claim (`2e < |D| − k ⟹ #bad ≤ 1`) is **false** for the project's strong bad set. Explicit kernel-checked witness over `ZMod 7`: `D = F`, `k = 2`, `e = 1` (so `2e = 2 < 5 = |D| − k`), `f₀ = 1_{1} + 1_{2}`, `f₁ = 1_{1} + 2·1_{2}`, with bad parameters `3` and `6`. Since `e + 1 = 2` there, the same witness shows `card_badSet_le_succ_radius` is sharp.

Validation preceded the proofs: `analysis/unique_decoding_two_good_check.py` (180 instances: 0 failures of the two-point correlated agreement, 0 failures of `#bad ≤ e+1`, 21 violations of `#bad ≤ 1`, the value `e+1` attained 33 times) and `analysis/unique_decoding_two_good_counterexample_search.py` (826 instances: 0 / 112 / 0 / 0). Both saved their outputs alongside the scripts.

### Verification and housekeeping

- Full `lake build` succeeds; `RequestProject/Main.lean` prints the axioms of all eight new declarations, each depending only on `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`admit`, no new axioms, no changes to the strong MCA definition, no weakening to slack MCA, nothing removed from the folded-RS capacity results or the binomial fallback.
- `RESULTS.md` gained section 69 (the full argument, the witness, the validation numbers) and `DISCREPANCIES.md` gained section 8.20 (why the literal claim was corrected, the remaining `2e` vs `3e` regime gap recorded as open, and the reuse audit). `ARISTOTLE_SUMMARY.md`, `INDEX.md` and `PROJECT_MAP.md` were left untouched.
- Everything is committed and pushed.


# Summary of changes for run cedb9e9a-56da-4e26-9a36-08eb96ba2901
## Multiplicity elimination for the non-affine part — completed, with an honest negative finding

The remaining obstruction of the ordinary Reed–Solomon post-Johnson chain was repeated non-affine factors (`e_i > 1`) of the Guruswami–Sudan interpolant. I ran the requested exact-arithmetic validation first, then formalised the outcome. The whole project builds with no errors, no `sorry`/`admit`, and every new declaration is audited in `RequestProject/Main.lean` with `#print axioms`, all reporting only `[propext, Classical.choice, Quot.sound]`.

### Validation first (exact integer/`Fraction` arithmetic, no floats)
`analysis/multiplicity_elimination_check.py` and `analysis/multiplicity_elimination_counterexample_search.py`, with outputs saved alongside them:
- the residual of the concrete minimal interpolant is non-squarefree in **27 of 66** instances;
- the search found **8 counterexamples in 120 scanned instances** to the literal mechanism requested (bad parameters are roots of the discriminant of the reduced part `R/gcd_Y(R, ∂_Y R)`), all of shape `R = c·S²`; a fully explicit one (`q = 101`, `n = 8`, `k = 2`, `m = 2`, bad set `{0,48,50}`) is recorded;
- the line-trace count is vacuous: `|U| = 0` in **66 of 66** instances.

Per the mission's stop rule, the mechanism is reported as incomplete and the conditional frontier is kept. **No unconditional post-Johnson claim is made.**

### What is proved (`RequestProject/Root/CodingTheory/MultiplicityElimination.lean`, `…/MultiplicityEliminationPostJohnson.lean`)
- **T1** `dvd_derivative_of_sq_dvd`, `not_separable_of_sq_dvd`, `sq_dvd_iff_not_separable`. The requested unrestricted iff had to be restricted to perfect fields: it is false over the coefficient field actually in play (`Y^p − Z` is irreducible with vanishing derivative).
- **T2** `sq_dvd_map_of_sq_dvd`, `sq_dvd_specZ_of_sq_dvd` — specialisation preserves a repeated factor.
- **The carrier replacing squarefreeness.** `DoubleRootTransfer k R S` ("`S` carries the double roots of `R`") with `card_badSet_le_affineSplit_transfer`: the affine-split bad-set bound with the discriminant taken of the carrier, allowing *arbitrary* multiplicities in `R`. Lifted to the post-Johnson chain as `TransferInterpolantSplit` and `card_badSet_postJohnson_transfer` (`|bad| ≤ (2a³+2a⁴)·K⁶`, constants unchanged), plus the `∃ C`, `ε_mca` and `2⁻¹²⁸` forms. `transferInterpolantSplit_of_squarefreeInterpolantSplit` proves this is a strict weakening of the previous hypothesis.
- **An unconditional dichotomy.** `card_badSet_le_repeatedPart`: for any split `R = G·S` and with **no** multiplicity hypothesis at all, `|bad| ≤ #Pairs·|D| + (b_S + (b_S−1))·d_S + |codewordLocus k G|`, where `codewordLocus k G` is the set of parameters at which a candidate codeword is a root of the repeated part. `codewordLocus_one` / `card_badSet_le_repeatedPart_one` recover the previous bound when `G = 1`, and `doubleRootTransfer_of_codewordLocus_eq_empty` shows the two formulations coincide.
- **Two refutations.** `doubleRootTransfer_reducedPart_fails` (the squarefree reduced part is not a carrier — witness `(Y − Z²)²`, matching the numerical counterexamples) and `lineTrace_eq_zero_of_lineInterpolant` (the interpolation condition forces the line trace to vanish at *every* position, so `card_badSet_le_lineTrace`, though true and proved, can never be applied).

A further consequence recorded in the notes: no purely algebraic bound on the remaining term can exist — for `G = Y − Z²` the codeword locus is all of `F` — so the missing step must use the agreement/decoding side, not gcd/derivative/resultant/degree data alone. No Hensel lifting, Fitting ideals, subresultants or global squarefree assumptions were used.

### Documentation and bookkeeping
`RESULTS.md` gained §68 (subsections 68.1–68.9) and `DISCREPANCIES.md` gained §8.19 (D68.1–D68.7), stating plainly that D67.4 is weakened rather than closed. The freeze list was respected: no change to the strong MCA definition, no weakening to slack MCA, no removal of the folded-RS capacity results or binomial fallback, no new axioms. All work is committed and pushed.


# Summary of changes for run b0acecc5-dcec-434d-a348-048cc93298c0
## Wynik misji — faktoryzacja separowalna dla konkretnego interpolantu

Cała praca jest w repozytorium (zbudowana, bez `sorry`, tylko aksjomaty `propext`, `Classical.choice`, `Quot.sound`; audyt `#print axioms` w `RequestProject/Main.lean`).

### Co zostało udowodnione (Lean, bez założeń dodatkowych)

**Twierdzenie o faktoryzacji BCHKS25 §3.2** (`RequestProject/Root/CodingTheory/SeparableFactorisation.lean`):
- `exists_irreducible_factorisation` — dla każdego niezerowego `Q ∈ F[Z][X][Y]`: `Q = C(X,Z)·∏ Rᵢ^{eᵢ}`, `Rᵢ` parami niestowarzyszone nierozkładalne dodatniego stopnia w `Y` (jednoznaczność rozkładu; żadnych innych założeń);
- `SeparableInY`, `IsCoprimeInY`, `separableInY_iff_derivative_ne_zero` (kryterium T1), `separableInY_of_irreducible`;
- `no_inseparable_factor_of_natDegree_lt_ringChar` oraz `exists_separable_factorisation` (T4): pełna postać BCHKS25 — `Rᵢ` nierozkładalne, separowalne w `Y` i parami względnie pierwsze w `Y` — przy jedynym założeniu `deg_Y Q < ringChar F`;
- narzędzia: lemat Gaussa nad `F(Z,X)`, certyfikaty `discBiv ≠ 0` i `resBiv ≠ 0`, dziedziczenie budżetów stopni przez dzielniki (`FactorDegreeBounds.lean`);
- `exists_separable_components_of_squarefree` — dla `Q` bezkwadratowego pełna lista komponentów z obydwoma certyfikatami.

**Dla konkretnego interpolantu** (`SlackInterpolantSeparability.lean`):
- `no_inseparable_factor_of_slack` — każdy nierozkładalny czynnik dodatniego stopnia w `Y` interpolantu `LineInterpolant` jest separowalny w `Y`, o ile budżet `bY < ringChar F`;
- `exists_separable_factorisation_of_lineInterpolant`;
- `exists_minimal_lineInterpolant` — brakujące „pole minimalności” jest darmowe (dobre uporządkowanie ℕ), nie trzeba go zakładać.

**Łańcuch post-Johnson** (`SquarefreeInterpolantPostJohnson.lean`, `AffineSquarefreePostJohnson.lean`): hipoteza strukturalna `SeparableComponentSplitBiv` (rozbicie afiniczne + komponenty + dyskryminanty + rezultanty + punkt specjalizacji) została **usunięta**. Zostały: `SquarefreeInterpolantSplit` (jeden bezkwadratowy interpolant w budżetach) albo słabsza `AffineSquarefreeInterpolantSplit` (dowolne krotności czynników afinicznych, bezkwadratowa część nieafiniczna), plus jawne `a·K < ringChar F` i `(2a³+2a⁴)·K⁵ < |F|`. Dowiedzione: `|bad| ≤ C·K⁶`, postać `∃C`, postać `ε_mca`, certyfikat `2⁻¹²⁸`.

### Co zostało obalone (uczciwie, z dowodem w Lean)

Zaproponowana ścieżka „nieseparowalny ⇒ `R = Sᵖ` ⇒ sprzeczność z minimalnością” **nie działa** — z dwóch niezależnych powodów:
- `not_isPow_of_irreducible`: element nierozkładalny nigdy nie jest właściwą potęgą, więc implikacja jest wewnętrznie sprzeczna;
- ciałem współczynników jest **niedoskonałe** `L = F_q(Z)(X)`: zerowa pochodna daje jedynie `R = expand p S` (`exists_expand_of_not_separableInY`), a `Y^p − Z` jest nierozkładalny (Eisenstein w pierwiastku `Z`), nieseparowalny i nie jest potęgą (`inseparableWitness_*`, `exists_irreducible_not_separableInY`, `not_forall_inseparableInY_isPow`).

Dlatego separowalność jest dowodzona z jawnego warunku na charakterystykę — w każdym realnym zakresie parametrów (M31 = 2³¹−1 itd.) spełnionego z ogromnym zapasem — a nie z minimalności.

### Czego NIE udało się usunąć (dokładny brakujący krok)

Pozostaje **bezkwadratowość części nieafinicznej** (przypadek `eᵢ > 1`), czyli dokładnie to, co BCHKS25 deleguje do [BCI⁺20, Dodatek C]. Nie jest to możliwe do „ominięcia”: przy powtórzonym komponencie sumaryczne oszacowanie jest fałszywe, co ten projekt już wcześniej obalił (`sqfreeKernel_bound_fails`, świadek `(Y − Z²)²`). Empirycznie przypadek ten faktycznie występuje dla konkretnego interpolantu minimalnego stopnia (4/185 w nowym teście, 27/96 we wcześniejszym). Zgodnie z instrukcją twierdzenia warunkowe zostały zachowane, a brakujący krok opisany w `DISCREPANCIES.md` (D67.4).

### Walidacja numeryczna (arytmetyka dokładna, bez liczb zmiennoprzecinkowych)

- `analysis/factorisation_slack_Q_check.py` — 185 interpolantów: `deg_Y Q < char` 185/185, brak czynników nieseparowalnych poniżej charakterystyki 0/185, bezkwadratowość 181/185;
- `analysis/inseparable_factor_slack_check.py` — obalenie ścieżki `p`-tej potęgi, przykład interpolantu z czynnikiem nieseparowalnym przy `deg_Y ≥ char`, oraz 172 interpolanty bez nieseparowalności poniżej charakterystyki;
- `analysis/lexicographic_minimality_check.py` — minimalność stopnia w `Y` w 20/20 przypadkach; minimalność nie daje bezkwadratowości.

Wyjścia zapisane obok skryptów; opis wyników w `RESULTS.md` §67, rozbieżności w `DISCREPANCIES.md` D67.1–D67.6. Elementy z listy „freeze” nietknięte, brak nowych aksjomatów.

# Summary of changes for run d2037630-6d3e-47be-94d9-48e7ff5cfa78
Kontynuowałem misję „separable-component route”, domykając jedyny element, który pozostawał założeniem: **istnienie dobrego punktu specjalizacji `x₀`**.

## Co zostało dodane

**Nowy plik `RequestProject/Root/CodingTheory/SeparableComponentSpecialisation.lean` (481 linii, bez `sorry`):**

* `resBiv` — rezultanta dwóch składników *przed* podstawieniem `X := x₀` (odpowiednik istniejącego `discBiv`), wraz z `resLine_eq_eval_resBiv`, `resBiv_ne_zero_of_resLine_ne_zero` (hipoteza „biwariantna” jest *słabsza* od punktowej) i oszacowaniem stopnia `natDegree_resBiv_le : deg_X Res_Y(R₁,R₂) ≤ (b₁+b₂)·d_X`.
* `exists_eval_C_ne_zero_of_sum_natDegree_lt` — lemat zliczający: skończona rodzina niezerowych wielomianów o stopniach `≤ d i` ma wspólny nie-pierwiastek postaci `C x₀`, gdy `∑ d i < |F|`.
* **`exists_good_specialisation`** — jeśli każdy składnik jest separowalny w `Y`, a różne składniki są względnie pierwsze w `Y` nad ciałem funkcji (niezerowe `discBiv`, `resBiv`), oraz zachodzi jawna hipoteza zliczająca `∑_i (2b_i−1)d_X + ∑_{(i,j)} (b_i+b_j)d_X < |F|`, to istnieje *jeden* punkt `x₀`, w którym wszystkie dyskryminanty składników i wszystkie rezultanty par są niezerowe. Konstruktor `SeparableComponents.ofBivariate` pakuje to w rekord listy składników.
* `card_badSet_le_affineSplit_componentsBiv`, `epsMCA_le_affineSplit_componentsBiv` — sumaryczne ograniczenie zbioru złych parametrów **bez żadnego punktu `x₀` w hipotezach** (i nadal bez założenia bezkwadratowości całej reszty).
* `SeparableComponentSplitBiv` + `card_badSet_postJohnson_separableBiv`, `ordinaryRS_badSet_postJohnson_separableBiv` (postać `∃ C`), `ordinaryRS_epsMCAmax_postJohnson_separableBiv`, `separable_prize_certificate_biv` — post-Johnson `|bad| ≤ (a·r + 2a³ + 2a⁴)·K⁶` przy jedynym wejściu rozmiarowym w postaci jawnej hipotezy zliczającej `(2a³+2a⁴)·K⁵ < |F|`. Stała `C` i certyfikat `2⁻¹²⁸` (`|F| ≥ 2²³⁶·C` dla `r=2, K=2¹⁸`) pozostają bez zmian — usunięcie `x₀` nic nie kosztuje w rozmiarze ciała.
* Niepustość pojęcia: `SeparableComponents.discBiv_ne_zero`, `SeparableComponents.resBiv_ne_zero` oraz ich instancje na jawnym świadku `(Y − Z)(Y − Z²)`.

## Walidacja (najpierw, przed dowodami)

`analysis/good_specialisation_check.py` (wynik: `analysis/good_specialisation_check_output.txt`) — wyłącznie arytmetyka całkowita mod q, bez liczb zmiennoprzecinkowych, w pełnym modelu trójzmiennym `F_q[Z][X][Y]`, `F₇ … F₂₃`: 175 zaakceptowanych instancji (65 pominiętych, gdy test zerowości na siatce byłby niepoprawny). We wszystkich: zawieranie złego locus `X` w oszacowaniu stopniowym (w wersji ostrzejszej i w tej faktycznie sformalizowanej), istnienie dobrego `x₀`, oraz kontrola end-to-end (zawieranie złych `z` i oszacowanie stopnia po `Z`). Zły locus `X` jest niepusty w 27/175 instancji, więc test nie jest pusty.

## Weryfikacja i dokumentacja

* Pełne `lake build` przechodzi bez błędów; `rg` nie znajduje żadnego `sorry`/`admit`.
* Wszystkie nowe deklaracje mają `#print axioms` w `RequestProject/Main.lean` i zależą wyłącznie od `[propext, Classical.choice, Quot.sound]`.
* `RESULTS.md` §66 i `DISCREPANCIES.md` §8.18 opisują mechanizm, przeliczone certyfikaty oraz uczciwe zastrzeżenia: pozostaje warunkowa już tylko *strukturalna* połowa hipotezy (że interpolant rzeczywiście rozkłada się na czynniki afiniczne razy bezkrotnościowa lista separowalnych składników); wersja z krotnościami `∏ R_i^{e_i}` z briefu jest fałszywa i nie jest nigdzie zakładana. Przy okazji usunąłem dwa ostrzeżenia lintera (nieużywana hipoteza i nieużywany argument `simp`).
* Lista właściwości została uzupełniona o nowe wyniki (istnienie dobrej specjalizacji, ograniczenie „biwariantne”, post-Johnson i certyfikat) — wszystkie oznaczone jako udowodnione.

Wszystko jest zacommitowane i wypchnięte.


# Summary of changes for run 7b9d957e-e2af-4497-bab8-2d336f081350
Inventory-and-search task only: no Lean source was touched, no proof attempted, no axiom and no `sorry` added. Two documents were produced and pushed.

**1. `INDEX.md` — the index you asked about (it did not exist before; it does now).**
A machine-generated map of the whole Lean development: 156 files, 45 447 lines, 2335 top-level declarations (1818 theorems/lemmas, 517 definitions/structures/instances). It has four sections — a directory overview, a file table (module, size, declaration count, one-line headline), a per-file listing giving each file's namespaces, its project-internal imports, its reverse dependencies ("imported by") and every declaration it introduces, and an alphabetical index of all 2335 declaration names with their module. It is regenerated by `python3 analysis/generate_index.py`, so it stays in step with the sources. `README.md` now opens with a "Where to look first" pointer to it.

**2. `analysis/RESOURCE_INVENTORY.md` — the requested inventory.** (Requested as `ANALYSIS/…`; put inside the existing `analysis/` directory instead, since two top-level directories differing only in case collide on case-insensitive filesystems.) Sections: environment; local Mathlib capabilities; external repositories checked; relevant external witnesses; missing mechanisms; recommendation.

Main findings:

- **Environment.** Lean 4.28.0; Mathlib vendored at commit `8f9d9cff…` (16 Feb 2026); nine local packages, no other Lean library on disk. Python 3.11.14 with *no* `sympy`/`z3`/`sage`/`numpy` installed (PyPI is reachable, so they are installable); `analysis/` is stdlib-only exact arithmetic except `subspace_design_check.py`, which imports `z3` and therefore cannot run here as is. Network access works, including anonymous shallow clones and the GitHub API.
- **Local Mathlib.** Present and usable over `F[Z][X][Y]`: `Polynomial.resultant` with `resultant_eq_zero_iff`, `resultant_ne_zero`, `resultant_map_map`, the Bézout form, the Sylvester matrix, a general-coefficient-ring `Polynomial.discr` with `resultant_deriv`, `hasseDeriv`, `Separable`, `PerfectField.separable_iff_squarefree`, `wronskian`. Absent: subresultants (entirely), multivariate resultants/Gröbner bases, Fitting ideals, and any degree bounds for `discr`/`resultant` — the project's own `Root/MultivariateResultant.lean` and `Root/FittingIdeal.lean` remain the only implementations.
- **External repositories.** ArkLib (upstream, `a96483a`) states the *identical* obstruction — Claim 5.6 of BCIKS'20, `∃ x₀, discY(Rᵢ)(x₀) ≠ 0` — and leaves it `sorry`, together with its input, equation 5.12. Two public forks carry a `sorry`-free version of that file: they prove eq. 5.12 and derive the good specialisation point, but only *conditionally* (a field-size counting hypothesis) and only after replacing the residual by the irreducible **separable** components; the downstream chain in those forks still rests on 6 `axiom`s and dozens of `sorry`s. `iotexproject/rs-proximity-gaps` is `sorry`-free and axiom-free but achieves correlated agreement above Johnson only at *half* the threshold — the same trade this project already owns unconditionally in `MCAPairCover.lean`. `sumcheck-lean4` and `ZkLinalg` contain nothing relevant. The Isabelle AFP `Subresultants` entry is the only formal subresultant development anywhere, and is not importable into Lean.
- **Recommendation.** Nothing found closes the ordinary-RS post-Johnson gap; the conditional frontier already recorded in `DISCREPANCIES.md` §8.16 and `MILESTONE_ORDINARY_RS.md` stands, now corroborated from outside. One mechanism found is genuinely new relative to the routes this project already refuted — the separable-component route — and the report notes that its two ingredients are unusually close to material already in this project (`discRes_ne_zero_of_isCoprime` mirrors the forks' separability-implies-nonzero-discriminant lemma, and `card_badSet_le_affineSplit_twoFactor` is already the two-component reassembly), so what is missing narrows to a list-indexed generalisation of that reassembly plus the characteristic-`p` factorisation, at the price of an explicit field-size hypothesis. The report also advises against the subresultant route until subresultants are built from scratch.

The project's Lean sources are unchanged; the only new files are the two documents, the index generator, and a pointer paragraph in `README.md`. All committed and pushed.

# Summary of changes for run 9abe5d31-be70-4fd6-9f4f-c13d810998c4
Consolidation done — no new proof work, no Lean sources touched, no axioms added.

**1. Frozen and documented (RESULTS.md, new §64).** A dedicated freeze section records the seven Welch–Berlekamp pencil theorems with their Lean names and one-line meanings, all in `RequestProject/Root/CodingTheory/WelchBerlekampPencil.lean`:

- W1 `natDegree_wbDet_le` — every maximal minor has degree ≤ e+1 in the line parameter;
- W2 `card_badSet_le_of_wbDet_ne_zero` — one non-vanishing maximal minor forces `#bad ≤ e+1`;
- W3 `epsMCA_le_of_wbDet_ne_zero` — the same in density form, `ε_mca ≤ (e+1)/|F|`;
- W4 `wbDet_eq_zero_of_correlatedAgreement` — correlated agreement degenerates every minor;
- W5 `wbDet_eq_zero_of_rationalLine` — so does a rational line with denominator degree ≤ e;
- W6 `not_isCloseOn_of_not_dvd` — and then the word need not be e-close at all, so W4 has no converse;
- W7 `exists_nonzero_wbVector_of_card_lt` — above `k+2e < |D|` the test is vacuous for every word.

§64.1/§64.2 state precisely what the pencil changes (the unconditional constant `e+1` now covers the whole unique-decoding regime, replacing the `k+3e ≤ |D|` hypothesis of the earlier syndrome-rigidity bound) and what it leaves untouched.

**2. Frontier recorded (DISCREPANCIES.md, new §8.16, entries D64.1–D64.4).** The improvement from `k+3e ≤ |D|` to `k+2e < |D|` and its explicit checkable rank hypothesis; the single remaining ordinary-RS post-Johnson obstruction (the residual-squarefree hypothesis `discLine bYR x₀ R ≠ 0` of the affine-factor-split route, equivalent to "no repeated factor surviving specialisation"); the fact that the squarefree-kernel route was refuted and the subresultant route remains a probe (9 usable instances of 56); and the statement that all Phase 0 empirical evidence is recorded but carried by no theorem.

**3. New milestone document `MILESTONE_ORDINARY_RS.md`** covering: the unconditional WB pencil result, the unconditional binomial fallback `card_badSet_le_shorten_circuit` (plus the pair-cover bound), the conditional length-based post-Johnson bound `card_badSet_le_affineSplit`/`epsMCA_le_affineSplit`, the exact residual hypothesis, a table of seven formally refuted routes with their Lean witnesses, the open routes, the relation to the Proximity Prize certificates (the original table is vacuous as stated; the corrected length-based one certifies only over fields of size 2²⁶¹–2²⁷³), a freeze list, and the two candidate next phases left explicitly undecided.

**4. Build and audit.** `lake build` completes successfully (8182 jobs). A search for `sorry`/`admit` over all Lean sources finds only occurrences inside docstrings of the form "no `sorry`" — no proof contains either. `#print axioms` in `RequestProject/Main.lean` reports exactly `[propext, Classical.choice, Quot.sound]` for all seven WB declarations, and across the whole project no axiom outside that allowed set appears.

**5. Freeze respected.** No new ordinary-RS post-Johnson proof attempts, no changes to folded-RS results, no change to the strong-MCA definition, no axioms.

All changes are committed and pushed.

# Summary of changes for run a1e0e925-f5c3-474e-ba36-4139f7219e39
Phase 0 is complete, documented, and its recommended route has been formalised in Lean. The whole project builds (`lake build`, 8182 jobs, success) with no `sorry`, no `admit` and no axioms beyond `propext`, `Classical.choice`, `Quot.sound`; every result below has an explicit `#print axioms` line in `RequestProject/Main.lean` confirming this.

**Phase 0 — exact-arithmetic exploration (no floats anywhere).** All three required experiments were run and their raw output archived:

* `analysis/explore_degenerate_residual.py` → `analysis/phase0_experiment1_output.txt`
* `analysis/space_of_interpolants.py` → `analysis/phase0_experiment2_output.txt`
* `analysis/direct_bad_locus_from_syndrome.py` → `analysis/phase0_experiment3_output.txt`

The findings, written up as a new section 63 of `RESULTS.md` and as entries D63.1–D63.5 of `DISCREPANCIES.md`:

1. **Is the separable-kernel hypothesis necessary? No — it is sufficient but not necessary (category 2 of your brief).** Of 96 genuine Guruswami–Sudan instances (GS root property verified in all of them), 27 have a residual that is *not* squarefree in `Y` while the line has *no* correlated agreement, so the hypothesis is not automatic. But in every one of those 27 the bad set has size 0–3, far below the licensed bound (12/18/30/40), and no instance without correlated agreement violates the bound. Its failure destroys the discriminant *certificate*, not the conclusion.
2. **Does a better low-`Z` interpolant exist? Yes.** Where the canonical minimal-`Y`-degree interpolant degenerates, 18–23 of the 19–25 sampled members of the same interpolation module are squarefree, and the module gcd is trivial on every non-correlated-agreement instance. Degeneracy is an artefact of the canonical choice. The price of a squarefree representative is a constant factor in the bad-locus degree (12→15, 18→24, 30→40). This does not *prove* that such a representative always exists — that claim is itself Hilbert-irreducibility-flavoured and is assumed nowhere.
3. **Does syndrome-only detection work? Yes, and it is sharp — but only below unique decoding.** `bad ⊆ rank-drop` in all 150 instances; in the informative regime `2e < n−k` with a non-degenerate pencil the rank test gives `|drop| ≤ e+1` every time and equals the bad set in 34 of 37 cases. For `2e ≥ n−k` the test is vacuous in 84/84 instances.
4. **Recommended route:** the syndrome/pencil route, which needs no interpolation, factorisation or discriminant. That is what I then formalised.

**New Lean file `RequestProject/Root/CodingTheory/WelchBerlekampPencil.lean`** (sorry-free), turning Experiment 3 into theorems:

* the key equation and the classical single-parameter Welch–Berlekamp decoder — `wbPair_cross`, `wbPair_eq_mul_of_isCloseOn` (in the regime `k+2e ≤ |D|` a Welch–Berlekamp pair reads off the codeword), `isCloseOn_of_wbPair_mul` (converse);
* `natDegree_wbDet_le` — every maximal minor of the pencil has degree `≤ e+1` in the line parameter;
* `card_badSet_le_of_wbDet_ne_zero`, `epsMCA_le_of_wbDet_ne_zero` — one nonvanishing maximal minor gives `|bad| ≤ e+1` and `ε_mca ≤ (e+1)/|F|`, under the weaker hypothesis `k+2e < |D|` where the project previously needed `k+3e ≤ |D|`; the hypothesis is now a checkable rank condition on a concrete matrix instead of a statement about factorisations;
* `wbDet_eq_zero_of_correlatedAgreement`, `wbDet_eq_zero_of_rationalLine` — degeneracy is implied by correlated agreement, and more generally by rationality of the line;
* `not_isCloseOn_of_not_dvd` — **the proposed converse is false, and this is now proved, not just observed**: a rational line with `Λ ∤ P₀` degenerates every maximal minor while `f₀` is not even `e`-close to the code. (23 exact counterexamples were also found numerically.) I did not attempt to prove the false version.
* `exists_nonzero_wbVector_of_card_lt` — sharpness: above the unique-decoding threshold the system has a nonzero solution for every word, the formal analogue of the 84/84 vacuous instances.

**What is deliberately left open and marked as such:** in the degenerate branch the bad set was small in every instance tried, but a global kernel vector only yields a bound of order `k+2e`, no better than what the project already has; closing it needs control of the pseudo-remainder and is recorded as an open gap, assumed nowhere. A subresultant probe (`analysis/subresultant_bad_locus_check.py`, output archived) produced only 9 usable instances out of 56 — containment and the degree bound hold on all 9, but that is recorded as a probe, not evidence, and no Lean was built on it.


# Summary of changes for run 5c668835-24e8-4d47-973a-8d71670f841c
## What I did

I worked on the one remaining conditional point of the affine-factor-split chain — the hypothesis that the residual `R` of the split is squarefree in `Y` — and settled the two routes the brief proposed for removing it. Everything new is in the new file `RequestProject/Root/CodingTheory/SquarefreeKernelResidual.lean`, is `sorry`-free, adds no axioms, and uses only `propext`, `Classical.choice`, `Quot.sound` (audited by `#print axioms` in `RequestProject/Main.lean`). The whole project builds.

### The two proposed routes are false — proved, not asserted

The brief itself already flagged the first claim as false; I formalised the refutation of **both**, with one explicit residual `R = (Y − Z²)²`:

* `sqExample_no_affine_factor` — it has **no** affine linear factor `Y − (A + Z·B)`, so it is a legitimate residual of the canonical split;
* `exists_affineFactorFree_not_squarefree` — its `Y`-discriminant vanishes identically ⇒ "no affine factor ⇒ squarefree in `Y`" is refuted;
* `discLine_sqExampleKernel_eq_one` + `sq_dvd_specZ_sqExample` + `sqfreeKernel_bound_fails` — its squarefree kernel `Y − Z²` has discriminant the constant `1` (no roots), so the proposed bound `(2·b_Y(R_sf) − 2)·d_Z(R)` is `0`, while **every** parameter of the field makes the specialised residual acquire a double root. The proposed containment "bad `z` ∈ zeros of `Disc_Y(R_sf)`" therefore fails at every parameter;
* `doubleRootLocus_card_unbounded` — the quantified barrier: over `ZMod p` the kernel degrees stay fixed while the double-root locus has size `p`, so **no** function of the squarefree-kernel degrees can bound that locus.

Exact-arithmetic confirmation (no floats) for `(Y − Z²)²` and `(Y² − Z)²` over `F₅, F₇, F₁₁, F₁₃`: `analysis/sqfree_kernel_check.py`.

Consequently the requested targets T1–T3 cannot hold in the requested form, and T4 (an unconditional `badSet_le_subJohnson_length`) does not follow from them. I did not prove the false version, and nothing in the project assumes it.

### What I delivered in their place

* `sq_dvd_mul_trichotomy`, `resLine` / `eval_resLine` / `natDegree_resLine_le`, `eval_locus_eq_zero_of_sq_dvd_mul` — the correct factorwise mechanism: a double root of a specialised product is a root of one of the two discriminants or of the resultant of the two pieces.
* `card_badSet_le_affineSplit_twoFactor`, `epsMCA_le_affineSplit_twoFactor` — the resulting bad-set and `ε_mca` bounds for a residual written as `R = R₁·R₂` (e.g. squarefree kernel times cofactor): `|bad| ≤ (#pairs)·|D| + (2b₁−1)d + (2b₂−1)d + (b₁+b₂)d`, under `Disc_Y(R₁) ≠ 0`, `Disc_Y(R₂) ≠ 0`, `Res_Y(R₁,R₂) ≠ 0`. The resultant hypothesis is exactly what a repeated factor destroys, which is the precise price of multiplicities.
* `resultant_eq_zero_of_common_factor`, `discRes_eq_zero_of_sq_factor` (over any **domain**), `discLine_eq_zero_of_sq_factor`, `no_sq_factor_of_discLine_ne_zero` — these pin down the remaining hypothesis: `discLine bYR x₀ R ≠ 0` holds precisely when the residual has no repeated factor surviving the specialisation, affine or not.
* `analysis/residual_squarefree_check.py` — exact-arithmetic study of *real* Guruswami–Sudan interpolants (random lines and lines planted with correlated agreement). On all 24 instances tried (`q ∈ {101,127}`, `n ≤ 7`, `k ∈ {2,3}`, `m = 2`) the least-degree interpolant is squarefree in `Y`, so the hypothesis holds there; often it is even linear in `Y`, the already unconditional corner. This is evidence, not a proof, and the script says so.

### Status of the rest

The conditionality is localised and quantified, not eliminated: the length-based sub-Johnson bound still assumes the residual has no repeated non-affine factor. The prize certificates and the unconditional results (pair-cover bound, unique decoding / independent folds, folded-RS capacity, binomial fallback, strong MCA definition) are untouched and still build.

Documentation: `RESULTS.md` §62 and `DISCREPANCIES.md` §8.15 record all of the above, including what was refuted and what remains open. All work is committed and pushed.


# Summary of changes for run 68d03382-1391-4a0c-9419-f3da5a6a2931
## What I did this session

I continued the sub-Johnson / post-Johnson line of the project, following the incoming BCHKS25 "slack interpolant" brief but adapting the route where the brief's mechanism could not be carried through formally.

### The mathematical situation

The brief asked for an *unconditional* length-based bad-set bound. Working through it, I first established (and proved) why the obvious mechanism cannot deliver that:

* **`discLine_eq_zero_of_correlatedAgreement`** — if the line `f₀ + Z·f₁` has correlated agreement with a codeword pair `(A,B)` on enough positions, then `(Y − (A + z·B))²` divides the specialised interpolant at *every* parameter `z`, so the discriminant of the formal line vanishes identically. The non-degeneracy hypothesis of the earlier discriminant bound is therefore unsatisfiable exactly in the regime a proximity-gap theorem has to cover. This is now a proved barrier, alongside the earlier resultant barrier.

### The new mechanism: the affine factor split

New file `RequestProject/Root/CodingTheory/AffineFactorSplit.lean` (sorry-free), which repairs both the mechanism and the *shape* of the bound:

* **`exists_affine_split`** — every nonzero interpolant factors as a product of affine linear factors `Y − (A + Z·B)` times a residual with no affine linear factor. So the factorisation is never an extra assumption.
* **`card_badPairSet_le`** — a fixed codeword pair explains at most `|D|` bad parameters: each such parameter consumes a distinct *spurious agreement* position, which determines it uniquely.
* **`card_badSet_le_affineSplit`** (and `…_ydeg`, `epsMCA_le_affineSplit`) — `|bad| ≤ (#pairs)·|D| + (2·bY(R) − 1)·dZ(R)`: **length-based**, `O(|D|)`, the shape the literature predicts, and not the dimension-based shape that this project had already refuted.
* **`card_badSet_le_affineSplit_linear`** — an unconditional corner: if the residual is linear in `Y`, no non-degeneracy hypothesis is needed at all.
* **`card_badSet_le_affineSplit_discBiv`**, **`epsMCAmax_le_affineSplit_discBiv`**, **`badSet_le_or_residual_degenerate`** — the residual hypothesis restated intrinsically ("squarefree in `Y`", with no chosen specialisation point), a code-level MCA bound, and a dichotomy for an arbitrary interpolant that assumes no factorisation.

Numerical support with exact arithmetic (no floats): `analysis/affine_split_badset_check.py` (24 exhaustive small-field instances confirming the per-pair counting) and `analysis/slack_interpolant_dimension_check.py` (the slack condition verified exactly; at a fixed margin below the Johnson radius the constants `bY = 15`, `dZ = 109` are *independent of the length* for `n = 2¹²…2²²`).

### Honest scope — what was not achieved

The unconditional targets (`badSet_le_subJohnson_length` with no hypothesis, an unconditional post-Johnson chain, and recomputed prize certificates) are **not** claimed. The affine split *weakens* the assumption rather than removing it: after this session the entire conditional content is one statement — the affine-factor-free residual of the canonical split is squarefree in `Y`, i.e. the interpolant has no repeated *non-affine* factor. Repeated affine factors are handled unconditionally. Closing the remaining gap requires a Hilbert-irreducibility/Chebotarev-type transfer for function fields that is not available in the library and was not derived here. This is documented in `DISCREPANCIES.md` §8.14 (D61.1–D61.5), with the positive results in `RESULTS.md` §61.

### Housekeeping

`RequestProject/Main.lean` imports the new module and runs `#print axioms` on all twelve new declarations — every one depends only on `propext`, `Classical.choice`, `Quot.sound`. Full `lake build` succeeds (8179 jobs); no `sorry`/`admit` anywhere in the project; no axioms added. The frozen items (strong MCA definition, folded-RS capacity results, binomial fallback, the existing refutation) are untouched. All work is committed and pushed.


# Summary of changes for run 716a3ef1-597f-481d-b2ef-5c49f8e0e0d4
## What I did with the incoming package

The package's central claim — a deterministic sub-Johnson bad-set bound "with no non-degeneracy hypothesis", provable by pure Guruswami–Sudan degree counting plus resultant elimination — was checked before anything was assumed. Two independent problems were found, and both are now recorded formally.

**1. The proposed proof route does not work (checked in the previous pass, unchanged).** At interpolation multiplicity ≥ 2 the relevant resultant/discriminant vanishes identically on the evaluation domain, exactly where the argument needs it to be non-zero, so resultant elimination alone cannot deliver the bound. What *could* be removed from the earlier non-degeneracy assumption was the specialisation point; that is done (`SubJohnsonBCHKS.lean`), together with the generalised-RS monomial isometry, which is unconditional.

**2. The hypothesis, as it had been isolated in this project, is false — and I proved it.** `Root.CodingTheory.subJohnsonBoundPoly_false` (`SubJohnsonRefutation.lean`) refutes, for every deletion depth `t` and every constant `C`, the statement "the bad set of a shortened generalised line below its own Johnson budget has at most `C·(k+1)⁶` elements". The counterexample is explicit: dimension `k = 1` over a large prime field, line `g₀ = x²·v`, `g₁ = x·v`, budget `e = |Dom| − 2`; every pair of surviving positions `x ≠ ±y` makes `γ = −(x+y)` bad, giving at least `|D| − t − 2` distinct bad parameters against a constant bound. The defect is the *shape*: a bad-set bound must grow with the code **length**, as the literature's `J(N, d, E)` does.

## What replaced it

* `SubJohnsonBoundLen t C` — the corrected hypothesis (bad set `≤ C·(|D|+1)⁶`), which survives the counterexample.
* The whole Jo-style post-Johnson chain rerun with it: `card_badSet_le_shortening_len`, `epsMCAmax_le_two_pow_neg_128_len`, and the asymptotic statements `ordinaryRS_badSet_postJohnson_of_subJohnsonLen` / `ordinaryRS_epsMCA_postJohnson_of_subJohnsonLen`. The `O(K⁶)` shape of the conclusion survives; only the constant grows, by the fixed factor `(2r)⁶`.
* Six explicit `2⁻¹²⁸` certificates (`prize_len_certificate_rate_*`) at `K = 2¹⁸` for rates 1/2, 1/4, 1/8 (steps 1, 2) and 1/16 (steps 1, 2), each with the exact minimal shortening depth and the exact field size it needs: `2²⁷³`, `2²⁶¹`, `2²⁶³`, `2²⁷¹`, `2²⁶⁶`, `2²⁷¹`.
* The negative half: `prize_budget_exceeded_rate_*` prove, by exact integer arithmetic, that with the corrected numerator and sub-Johnson constant `1` every row exceeds the `2¹²⁷` budget imposed by `q < 2²⁵⁶` — by 5 bits (rate 1/4, first step) up to 17 bits (rate 1/2). So the published table is **not** reachable through this chain over the prescribed prime unless the sub-Johnson bound carries an explicitly sub-unit leading constant, which the package does not supply.

## Status of the mission targets

* `badSet_le_subJohnson_bchks` — **not** proved. The sub-Johnson bound itself remains unproved here, in either shape; the claimed no-non-degeneracy route is refuted as a route (its statement is not disproved).
* Generalised-RS transfer — proved unconditionally.
* `ordinaryRS_badSet_postJohnson` — still conditional, now on the corrected hypothesis; the old dimension-based version is vacuous and is annotated as such (kept, not deleted, in `PrizeCertificates.lean` and `PostJohnsonJo.lean`).
* Prize certificates — proved, but only over the larger fields listed above.

## Housekeeping

New: `RequestProject/Root/CodingTheory/SubJohnsonRefutation.lean`, `RequestProject/Root/CodingTheory/PrizeCertificatesLen.lean`, `analysis/prize_certificate_length_check.py` (exact integer/rational arithmetic, no floats). `RESULTS.md` §60 and `DISCREPANCIES.md` §8.13 document the refutation, the correction and the numerical table; `Main.lean` prints axioms for every new declaration. Full project builds (8179 targets), no `sorry`/`admit`, no new axioms — everything depends only on `propext`, `Classical.choice`, `Quot.sound`. The freeze list was respected: the strong MCA definition, the folded-RS capacity results and the binomial fallback are untouched. All work is committed and pushed.


# Summary of changes for run 63e910c8-28e3-44b9-8ed4-3268d590b3a7
The mission is complete; the full build passes (8175 jobs) with no `sorry`/`admit` and no new axioms, and all work is committed and pushed.

**Jo-style post-Johnson chain (T1/T2)** — in `RequestProject/Root/CodingTheory/PostJohnsonJo.lean`:
- The post-Johnson radius `E = ⌊n − √(n(K−1))⌋ + h` and the induced agreement budget are defined and bounded (`postJohnsonRadius`, `agreementBudget`, `agreementBudget_bounds`).
- `SubJohnsonBoundPoly t C` isolates the single external ingredient as an explicit named hypothesis about shortened generalised RS lines, with the constant `C` quantified outside the field, evaluation domain, dimension and line. It is never derived from Fitting ideals or pair resultants.
- `exists_shortening_depth` gives an explicit shortening depth `t = 16·r·h` that pushes the shortened instance strictly below Johnson; the underlying gain inequality (`gain_of_gap`, `subJohnson_of_gap`) is proved purely over the integers, with reals used only for the radius itself.
- `ordinaryRS_badSet_postJohnson_of_subJohnson` and `ordinaryRS_epsMCA_postJohnson_of_subJohnson` are the two target theorems: for `n = rK`, `r ≥ 2`, `h ≥ 1`, under the sub-Johnson hypothesis alone, the bad set has at most `C'·K⁶` elements and `ε_mca ≤ C'·K⁶/|F|`, with `C' = (2r)^t·C` and an explicit dimension threshold `K₀`.

**MDS circuit incidence (§4)** — `card_grsBadSet_le_circuit_div` and `card_grsBadSet_le_circuit_inf` in `RequestProject/Root/CodingTheory/ShorteningMCA.lean` give Jo's Theorem 4.2 in both the single-`a` quotient form `C(n,a)/C(T_eff−1,a−1)` and the min-over-`a` form. Both are unconditional.

**Chojecki extension (§5)** — in `RequestProject/Root/CodingTheory/ChojeckiRadius.lean`:
- `not_constant_shortening_for_positive_slack` **refutes** the requested constant-depth statement: for any rate ρ ∈ (0,1) and any relative radius δ strictly beyond Johnson, every fixed shortening depth `t` fails for all large `n`, because the Johnson deficit grows like `Θ(n²)` while deleting `t` positions moves each side only by `O(t·n)`.
- `exists_linear_shortening_for_positive_slack` is the salvaged correct form: a constant *fraction* `c > 0` of deletions suffices, with threshold `c* = (ρ − (1−δ)²)/(1 + ρ − 2(1−δ))`. It requires the additional necessary hypothesis `ρ < 1 − δ` (otherwise the budget reaches the MDS distance).
- `two_pow_le_choose_div_choose` records the barrier this creates: at linear depth the shortening transfer factor is `2^{Θ(n)}`, so this route cannot yield a polynomial bound at a constant post-Johnson relative radius.

**Validation (§6)** — `analysis/post_johnson_internal_check.py` (90 instances, `r = 2..6`, `h = 1..3`, verifying every implication of the Jo chain including the transfer bound `C(n,t) ≤ (2r)^t·C(S,t)`) and `analysis/chojecki_relative_radius_check.py` (five (ρ,δ) pairs, showing constant depth always fails, `t_min(n)/n → c*`, and linear depth works). Both use exact integer/Fraction arithmetic only and exit 0, as do the pre-existing shortening-transfer and circuit-incidence checks.

**Documentation (§8)** — `RESULTS.md` §58 and `DISCREPANCIES.md` §8.11 record the new results and the discrepancy between the requested constant-depth lemma and what is actually true. `Main.lean` imports both new modules and runs `#print axioms` on every new declaration; each reports exactly `propext, Classical.choice, Quot.sound`.

Nothing on the freeze list was touched: the strong MCA definition, the folded-RS capacity results and the unconditional binomial post-Johnson bound are unchanged.

# Summary of changes for run 1655b228-5013-4717-bcdd-e15d1e904eb1
## Outcome

The dichotomy (mission target T1) is **proved**; the mission's second branch — "degeneracy itself produces a formal witness" — is **false**, and its refutation is now formalised. Consequently the `SubJohnsonBound` hypothesis is *not* eliminated, and the unconditional below-Johnson / polynomial post-Johnson theorems are **not** claimed anywhere in the project.

Everything is in `RequestProject/Root/CodingTheory/ResultantDichotomy.lean`; `lake build` is green, there is no `sorry`/`admit`, no axiom was added, and the axiom audit in `RequestProject/Main.lean` reports only `propext, Classical.choice, Quot.sound` for every new result.

## Proved

- `resultant_dichotomy` (T1) and `resultant_dichotomy_submodule`: for a line-closed set of univariate polynomials over a field containing a nonzero element, *either* two elements have nonzero Y-resultant, *or* one irreducible polynomial divides all of them. No non-degeneracy is assumed. Supporting: `exists_mem_avoiding_irreducibles`, `exists_irreducible_common_factor_of_forall_not_isCoprime`.
- `resultant_eq_zero_of_common_linear_factor_domain`: a common linear factor kills the resultant over any integral domain (the ambient library covers the field case; the interpolation module lives over `F[Z]`), plus `pairRes_eq_zero_of_common_witness`.
- `pairRes_eq_zero_of_mem_domain` (a correction to the earlier route): the specialised pair resultant is identically zero at every point of the evaluation domain `D`, so the non-degeneracy hypothesis can only ever be met at a specialisation point outside `D` — which requires `|F| > |D|`.
- `dvd_lineInterpModule_of_lineOfWitness`: the Guruswami–Sudan root step works already at witness `X`-degree `≤ k` (not just `< k`).
- `degenerate_branch_without_correlatedAgreement`: for every `k, L, e` with `k+1 < L ≤ |D|` and `k+e < |D|` there is a line whose interpolation module has two independent elements, has the common linear factor `Y − U` (so **every** pair resultant vanishes at **every** specialisation point), and yet admits **no** correlated agreement — every codeword of degree `< k` agrees with `f₀` on at most `k` positions (`card_agreement_le_of_degree_eq`). The reason: the common factor's root has `X`-degree exactly `k`, one too large to be a codeword, so the rational-function-witness route does not apply.
- `degenerate_branch_with_correlatedAgreement_of_degree_lt`: the converse side — with witness degree `< k` the module is degenerate in the same way but correlated agreement does hold on all of `D`. Together these pin the boundary exactly at the witness degree; the mission's "delicate case" (common factor of Y-degree ≥ 2) is not the obstruction, which already appears at Y-degree 1.

## Numerical validation (exact integer/`Fraction` arithmetic, no floats)

`analysis/dichotomy_resultant_check.py` (70 instances, no structural violation; nonzero specialised resultants only outside `D`), `analysis/degenerate_case_common_factor_check.py` (210 instances), and `analysis/dichotomy_correlated_agreement_check.py`, which exits with status 2 by design: 12 of 24 degenerate instances have no correlated agreement — the numerical form of the refutation, with the separation `deg_X(U) < k ⟺ correlated agreement` in every degenerate instance tested.

## Documentation and hygiene

`RESULTS.md` §57 and `DISCREPANCIES.md` §8.10 record the proved dichotomy, the domain-point correction, the refutation, and an explicit table of mission-target status. The freeze list was respected: strong MCA definition unchanged, folded-RS results and the binomial unconditional post-Johnson bound untouched, no capacity-ordinary-RS work. All work is committed and pushed.


# Summary of changes for run f7f6ac98-51ae-4e62-ac76-24488eb22d73
## What I did

I verified the proposed "Fitting-ideal root" before building on it, found it false as stated, recorded the correction, and then built the alternative (shortening) route as far as it goes unconditionally. Everything below compiles with no `sorry`, no `admit` and no new `axiom`; every new theorem is listed in `RequestProject/Main.lean` under `#print axioms` and depends only on `propext, Classical.choice, Quot.sound`.

### 1. The Fitting-ideal root — checked, and refuted as stated (`RequestProject/Root/FittingIdeal.lean`)

* Contrary to the brief, Fitting ideals of modules are **not** available in the ambient library (only the unrelated "Fitting decomposition"), so I developed the needed theory from scratch: `fittingIdealZero`, the adjugate/Cramer mechanism `det_smul_eq_zero_of_relations`, and `fittingIdealZero_le_annihilator`.
* Numerical validation with exact integer arithmetic (`analysis/fitting_ideal_root_check.py`) showed, in every trial, that the generalised interpolation module is non-zero **and torsion-free**, and that the bad parameters occur at the *generic* specialised rank.
* Both observations are now formal: `fittingIdealZero_eq_bot_of_torsionFree` proves that a non-zero torsion-free module has vanishing 0-th Fitting ideal. So mission target T2 (`Fitt₀(M) ≠ 0`) is false, and T3 (bad `z` are roots of `Fitt₀`) fails for *every* Fitting ideal of that module — independently of T2.
* The corrected statement that is true: `resultant_mem_fittingIdealZero_bezout` shows the resultant is a Fitting element of the **Bézout quotient**, which is exactly why the existing pair-resultant route works and a module-level replacement cannot.

### 2. Agreement-set shortening (`RequestProject/Root/CodingTheory/ShorteningMCA.lean`, new)

Validated first with exact arithmetic (`analysis/shortening_transfer_check.py`: 0 transfer failures in 371 tests, no double counting), then formalised unconditionally:

* `grsCloseOn_shortWord` (shortening step) and `isCloseOn_of_grsCloseOn_shortWord` (its exact converse, which is what makes the *mutual* formulation transfer);
* `isGrsBad_shorten` — bad-parameter transfer at the same error budget;
* `card_badSet_mul_choose_le` / `card_badSet_le_subJohnson` — the double count `#bad · C(n−e,t) ≤ C(n,t)·B`, and `epsMCA_le_subJohnson` for `ε_mca` (the strong-MCA definition is untouched);
* `belowJohnson_of_shortening` — the Johnson arithmetic of the reduction with no square roots at all, plus the concrete certificate `belowJohnson_2_20_rate_quarter` (`n = 2²⁰`, `k = 2¹⁸`, one unit above Johnson, `t = 5` deletions suffice).

### 3. Circuit incidence for generalised codes, and an unconditional post-Johnson bound

The existing circuit-incidence machinery was extended from ordinary to generalised Reed–Solomon lines: `card_grsBadSet_le_circuit`. This lets `SubJohnsonBound` be discharged with **no** non-degeneracy hypothesis (`subJohnsonBound_of_circuit`), yielding `card_badSet_le_shorten_circuit`, an unconditional post-Johnson bad-parameter bound.

### Honest scope — what was **not** achieved

The unconditional assembled bound is *binomial*, not polynomial. The polynomial `O(K⁶)`-type post-Johnson bound needs a **linear** deterministic bound for generalised lines at the *full* Johnson radius. The project's unconditional linear bound reaches only half the Johnson radius, and shortening does not repair this: the shortened instance stays below half-Johnson only while `2e < (n−t) − √((n−t)(k−t))`, whose maximum over `t` is essentially the unique-decoding radius, still below the Johnson radius at every rate. So the polynomial statement remains available only in the conditional form `epsMCA_le_subJohnson`, and the numerical prize certificates were not produced. This is written up in `RESULTS.md` §§55–56 and `DISCREPANCIES.md` §8.9, together with the refutation evidence.

Nothing on the freeze list was changed or removed.


# Summary of changes for run a0c7322e-da4d-4876-b978-49ea76792bbd
## What was done

I continued the ordinary–Reed–Solomon proximity strand, building the requested **unified algebraic root** and using it as far as it honestly goes. The whole project builds cleanly (`lake build`, 8170 jobs), contains no `sorry`/`admit` and no new `axiom`, and every new theorem is audited in `RequestProject/Main.lean` with `#print axioms`, reporting only `propext`, `Classical.choice`, `Quot.sound`.

### 1. The unified root — `RequestProject/Root/CodingTheory/GeneralizedInterpolationModule.lean`

* `lineInterpModule` — the generalized interpolation module of the formal line `f₀ + Z·f₁` over `F[Z]`, an honest `F[Z]`-submodule of the trivariate polynomial ring.
* `lineInterpModule_eq_inf_ker` — **the duality is a theorem**: the module equals the weighted-degree submodule intersected with the kernel of the (Hasse) syndrome map. The "interpolation module" and "syndrome space" pictures are literally the same object.
* Bad locus via **pair resultants** rather than the discriminant of a single interpolant: `eval_pairRes_eq_zero_of_agreement` (containment, needing **no** squarefreeness or non-degeneracy — the point the brief insisted on), `natDegree_pairRes_le` (degree bound `(bY+bY')·dZ`), and the counting/dichotomy consequences `card_goodZ_le_pairRes`, `epsMCA_le_pairRes`, `epsMCAmax_le_pairRes`.
* The return route from algebra to codewords: `correlatedAgreement_of_formalWitness` (counting form) and the new `correlatedAgreement_of_ratFuncWitness` — a single witness over `F(Z)` of degree `< k` on `k` or more positions is automatically `Z`-affine and yields *exact* correlated agreement, with no counting and no field-size assumption.

### 2. A new unconditional proximity gap — `RequestProject/Root/CodingTheory/OrdinaryRSProximity.lean`

`correlatedAgreement_of_card_goodZ_gt_choose`: if more than `C(n, e)` line parameters `z` make `f₀ + z·f₁` `e`-close to the code, then `f₀` and `f₁` agree with two codewords of degree `< k` on one and the same set of at least `n − e` positions. **No hypothesis at all** on `k, e, n, |F|`; in particular the radius is unrestricted, so this holds at and beyond the Johnson radius. Strong-MCA corollaries `card_badSet_le_choose_radius`, `epsMCA_le_choose_radius`, `epsMCAmax_le_choose_radius` give `ε_mca ≤ max(C(n,e), e)/|F|`, using the project's unchanged strong MCA definition.

### 3. Honest statement of what is *not* proved

The target `ordinaryRS_proximity_gap_johnson` with a threshold **linear in n** is not established unconditionally. Exactly one step is missing and is isolated as the hypothesis `hnd` of `epsMCAmax_le_pairRes`: that two module elements with nonvanishing pair resultant can be chosen. Both remaining sub-cases (a common linear `Y`-factor, where the extra agreement is not automatic from divisibility; and a common factor of `Y`-degree ≥ 2, which appears to need an effective Bertini–Noether statement absent from Mathlib) are written up. Two elementary barriers explaining why no elementary argument passes half the Johnson radius are also recorded. Capacity for ordinary RS was not attempted, per the freeze list.

### 4. Validation and documentation

* `analysis/ordinary_johnson_proximity_check.py` — exact prime-field arithmetic, no floats: 600 instances, 0 failures on the subset dichotomy, the selection map and witness verification. The earlier `fitting_ideal_bad_locus_check.py` and `formal_witness_ca_check.py` also pass.
* `MILESTONE_FOLDED_RS_CAPACITY.md` — consolidates the closed folded-RS strand (threshold `26·2^158`, list size `2^11`, the three refuted lemmas), which is untouched.
* `RESULTS.md` §54 and `DISCREPANCIES.md` §8.8 record the new results, the deviations from the brief (notably D54.1 and the choice of pair resultants over a Fitting-ideal presentation matrix), and the new open problem O54.1.

All work is committed and pushed.


# Summary of changes for run 40b198c4-212d-45fe-96b6-36491ede7d15
## Mission closed: the Weighted Excess Bound is proved, and the chain is unconditional

The whole project builds with `lake build`, contains no `sorry`/`admit` and no new `axiom`, and every new result is audited in `RequestProject/Main.lean` as depending only on `propext`, `Classical.choice`, `Quot.sound`.

### What was proved

**`Root/CodingTheory/Occupancy.lean`** — `occ S W` (the largest number of points of a finite set `S` in one coset of a subspace `W`), its basic bounds, and the two counting lemmas that drive the induction, in particular `occ_sub_one_le_fibres_add_image` (occupancy excess splits over the fibres and the image of a linear map).

**`Root/CodingTheory/WeightedExcessBound.lean`** — `weightedExcessBound`, the target statement, unconditionally and in every dimension:
nonnegative weights `μ` on subspaces `W i ≤ V` that are fractionally independent (`∀ U ≤ V, ∑ μ_i·dim(U ⊓ W i) ≤ lam·dim U`) satisfy `∑ μ_i·(occ S (W i) − 1) ≤ lam·(|S| − 1)` for any `S` in a coset of `V`. Proved by induction on `dim V` with an inner induction on the number of active weights, via a support step, a tight-subspace step (projection with kernel the tight subspace), and an exchange step.

**`Root/CodingTheory/FlagCertificateGeneral.lean`** — `excessBound_layerFamily`, `flagCertificate_of_finrank_le` (a certificate of rank `r` for every finite candidate set inside a coset of a layer `V ≤ C` with `dim V ≤ r`), `flagCertificate_of_card_le`.

**`Root/CodingTheory/ExcessBudgetBounded.lean`** — `HasExcessBudgetUpTo`, `listDecodable_of_hasExcessBudgetUpTo`, `hasExcessBudgetUpTo_of_design`, `listDecodable_of_subspaceDesign_general`.

**`Root/CodingTheory/FoldedRSLinearUnconditional.lean`** — `foldedRS_excessBudget`, `foldedRS_listDecodable_linear_unconditional`, and the mission's final target `foldedRS_threshold_linear_2_158_unconditional`: for folded Reed–Solomon at `n = 2^20`, `η = 2^-10`, list size `2^11`, the mutual-correlated-agreement error is at most `2^-128` once `|F| ≥ 26·2^158` — with **no** excess-budget or excess-bound hypothesis remaining. Everything on the freeze list (the strong MCA definition, the quadratic `2^173` theorem, the earlier conditional `2^158` theorems) is untouched.

### Two things in the brief that are not true, and are now formally refuted

1. **The supplied independence lemma is false.** Over `𝔽₃` take `S = {(0,0),(0,1),(0,2),(1,0),(1,1)}` (affine dimension 2) partitioned as `H₀={(0,0),(0,1)}`, `H₁={(0,2)}`, `H₂={(1,0),(1,1)}`. Every transversal is affinely independent (checked by `decide`), yet `K₀ = span{(0,1)} = K₂`, so the direction subspaces are *not* independent — `flatPartition_directions_not_indepOn` in `Root/CodingTheory/FlatPartitionIndependenceFails.lean`. The informal argument fails structurally: the transversal condition constrains the relative *positions* of the parts, never their internal *directions*.
2. **Route A cannot work anyway**, for a second, independent reason: the certificate constructor also needs each coordinate explained by one part. For `C = {(a,b,a+b)} ⊆ 𝔽₂³`, `y = (0,0,1)`, every flat partition of `S = C` is three singletons, so all occupancy weights vanish and coverage fails — even though a certificate does exist (weight 1 on `C` itself).

The bound was therefore proved by a different route: coset/fibre decomposition plus a tight-subspace step, by induction on the dimension of the layer. Occupancy is still the right measure; the flat partition is not needed.

### Two statement corrections

* `flagCertificate_of_finrank_le` with *no* hypothesis is false already at `r = 0`; the proved statement carries the layer (`V ≤ C`, `dim V ≤ r`, `S` in a coset of `V`).
* `foldedRS_excessBound` is proved in the bounded form `HasExcessBudgetUpTo … (r+1)`. This costs nothing downstream: the list-size argument only ever inspects candidate sets of `L + 2` codewords.

### Validation and documentation

Exact-rational (no floats) checks under `analysis/`: `flat_partition_independence_check.py` (refutes the independence lemma; 5184 violations at `q=3, d=2, |S|≤5`), `correct_flat_partition_check.py` (the occupancy-weight construction fails on genuine instances), `web_general_lp_check.py` (the Weighted Excess Bound verified by exact LP, 0 violations).

`RESULTS.md` has a new §53 and `DISCREPANCIES.md` a new §8.7 recording all of the above, including the status changes: the previously open items O50.1 and O52.1 are closed, and the `26·2^158` threshold is no longer conditional. `ARISTOTLE_SUMMARY.md` was not modified.


# Summary of changes for run dc332f31-b249-4170-a90c-c7b160fc1a79
## What was done

The mission's root — finite linear-programming duality — is now proved in Lean from scratch, and flag certificates are identified with its dual variables. Everything builds with `lake build`, contains no `sorry`/`admit`, adds no axioms, and every new theorem is confirmed by `#print axioms` (block in `RequestProject/Main.lean`) to depend only on `propext`, `Classical.choice`, `Quot.sound`.

**1. `RequestProject/Root/FiniteFarkas.lean` — the root theorem.**
Mathlib's cone-separation Farkas lemma needs a *closed* cone, and the closedness of a finitely generated cone is itself absent, so the finite theory was built by Fourier–Motzkin elimination:
- `exists_solution_or_certificate` — a finite system of real linear inequalities (rows indexed by any finite type, arbitrary universe) either has a solution or has a nonnegative combination of rows equal to the zero row with negative right-hand side. Proved by induction on the number of variables; the two halves of the induction step are a transfer lemma for the lifted weights and the choice of the eliminated coordinate between the largest lower and smallest upper bound.
- `farkas_feasible_iff` — feasibility of `{x ≥ 0, A x ≤ b}` ⟺ no dual certificate of infeasibility.
- `finite_farkas` — the requested LP duality `(∀ x ≥ 0, A x ≤ b → cᵀx ≤ γ) ↔ ∃ y ≥ 0, Aᵀy ≥ c, bᵀy ≤ γ`.

**One correction to the requested statement.** The literal, unconditional version is false: with `A = 0`, `b = −1`, `c = 1`, `γ = 0` (dimension one) the primal is empty, so the bound holds vacuously while no `y ≥ 0` satisfies `Aᵀ y ≥ c`. This is itself a Lean theorem, `finite_farkas_without_feasibility_false`; `finite_farkas` therefore carries a primal-feasibility hypothesis, which is exactly what strong duality needs.

**2. `Root/CodingTheory/FlagCertificateFarkas.lean` — certificates are the Farkas dual.**
- `flagCertificateOn_iff_excessBound` — for a finite candidate family `Λ` of subspaces, a certificate supported on `Λ` exists **iff** the excess bound (`ExcessBound`: every nonnegative coordinate weighting `μ` spending at most `lam·dim U` on each `U ∈ Λ` obeys `∑ᵢ μᵢ(aᵢ−1) ≤ lam(|S|−1)`) holds. At `lam = 1` this is precisely the obstruction family proved earlier, so that necessary condition is now known to be sufficient too.
- `flagCertificate_exists_of_excessBound` (the mission target) and the uniform `hasFlagCertificates_of_excessBound`.
- `excessBound_of_unit` / `flagCertificate_exists_of_excessBoundUnit` — a normalised, practically usable criterion (only the scale `lam = 1` plus a degenerate coordinate condition is needed).

**3. `Root/CodingTheory/FarkasRootChain.lean` — the completed chain.**
`hasExcessBudget_of_excessBound` → `listDecodable_of_excessBound` → `foldedRS_threshold_linear_2_158_of_excessBound`: for folded Reed–Solomon at `n = 2²⁰`, `η = 2⁻¹⁰`, list size `2¹¹`, one gets `ε_mca ≤ 2⁻¹²⁸` whenever `|F| ≥ 26·2¹⁵⁸`. The only remaining hypothesis is the excess bound itself — the LP-duality gap is closed. The unconditional `2¹⁷³` threshold, the quadratic result and the strong-MCA definition are untouched, and no ordinary-RS work was started (freeze list respected).

**4. Exact-arithmetic validation (run before formalisation, `Fraction` only, no floats).**
- `analysis/finite_farkas_check.py`: 400 random instances — 0 weak-duality failures, 0 strong-duality failures on feasible LPs, 10 gaps, all with an infeasible primal, smallest witness identical to the Lean counterexample. PASS.
- `analysis/flag_certificate_farkas_check.py`: 120 genuine subspace instances over `𝔽₂`/`𝔽₃` (real subspaces, real coordinate kernels, real agreement counts) — certificate feasibility matched the dual excess bound in every case, 109 of them feasible. PASS.
- Shared exact polyhedral engine in `analysis/exact_lp.py`.

**5. Documentation.** New §52 in `RESULTS.md` (five subsections: the Fourier–Motzkin root, Farkas/LP duality and the refutation, the certificate identification, the completed chain, the normalised criterion) and §8.6 in `DISCREPANCIES.md` (D52.1–D52.4, P52a–P52g, O52.1). The threshold arithmetic is restated honestly: `26·2¹⁵⁸ = (13/8)·2¹⁶² > 2¹⁶⁰`.

Everything is committed and pushed.


# Summary of changes for run 835e0f63-246c-4526-b7e3-d1b9d5c17b40
I verified the mission instructions first, as asked, and the mandated exact-arithmetic validation step found a counterexample to the proposed mechanism. I therefore executed the mission in corrected form rather than literally. Everything below builds with `lake build`, contains no `sorry`, no `admit` and no new axioms, and every new theorem is confirmed by `#print axioms` (in `RequestProject/Main.lean`) to depend only on `propext`, `Classical.choice`, `Quot.sound`.

**The proposed mechanism is false.** "Chen–Zhang Lemma 2.18" as stated — partition the candidate set into flats and use the *characteristic* weights `w = 1` as the flag certificate — cannot work. `analysis/flat_partition_check.py` (exact rationals) finds 801 covering failures against 0 budget failures. This is now a Lean theorem, not just a script: `flagCertificate_unit_weights_fails` shows that for the five points of an affine line in the plane over the five-element field — a single flat of dimension 1, so the flat partition meets the budget `1 ≤ |S|−1 = 4` — **no** weighting at all with every weight `≤ 1` satisfies the covering constraints, because the coordinate on which the set is constant demands weighted dimension 4 while at most 2 is available (`sum_finrank_inf_coordKer_one_le_two`). Certificate weights must scale with the occupancies.

**What I proved instead**, all in `RequestProject/Root/CodingTheory/FlatPartition.lean`:

- `sum_card_sub_one_le_of_indepOn` — the corrected partition lemma, valid in **every** dimension: if the directions `K_j` are independent submodules and `A_j ⊆ S` has all its differences inside `K_j`, then `∑_j (|A_j| − 1) ≤ |S| − 1`. The proof is exactly the requested inductive partition, done correctly: peel the cosets of one direction, note that every other flat meets each coset in at most one point, recurse in the quotient. Independence is necessary (dependent families violate it).
- `flagCertificate_of_density` — a certificate in every dimension from a single layer, whenever no coordinate is denser than the layer.
- `flagCertificate_of_indep_flats` — a certificate in every dimension from an independent family of flats, weights = occupancy excesses `(|T_j| − 1)/dim K_j`, with the budget supplied by the lemma above.
- `weighted_excess_le_of_flagCertificate` — the exact obstruction family: a certificate implies `∑_i μ_i (a_i − 1) ≤ |S| − 1` for every nonnegative *fractionally independent* coordinate weighting `μ`.

**Status of the mission targets.** Targets A (`flagCertificate_of_finrank_le` for all `r`), B and C remain **open**. The work above pins down precisely why: the general existence statement is the linear-programming dual of the fractional independent-flat budget, whose *integral* case is exactly what I proved; closing it needs LP strong duality (Farkas), which Mathlib does not provide. The LP evidence (`analysis/flag_certificate_general_lp.py`, dimensions 3 and 4) still shows no counterexample, so the conjecture itself stands. Nothing on the freeze list was touched: the strong MCA definition, the quadratic result and the unconditional `2^173` threshold are unchanged, and no ordinary-RS or engineering work was started.

**Target D, honestly recomputed.** `analysis/chenzhang_linear_threshold_check.py` (exact `Fraction` arithmetic) recomputes the field-size requirement at `n = 2^20`, `η = 2^-10`, `ε_mca ≤ 2^-128`. With a linear list size `L = ⌈2/η⌉ = 2^11` the requirement is exactly `26·2^158 = (13/8)·2^162`. So the success criterion "threshold `≤ 2^160`" is **not** met even under a linear list size: `26·2^158 > 2^160`; the correct target constant is `26·2^158` (i.e. `2^163` as a power of two). This matches the already-present conditional theorem `foldedRS_threshold_linear_2_158_of_excessBudget` exactly, which remains conditional on the excess budget.

Documentation was updated as required: a new §51 in `RESULTS.md` (five subsections covering the refutation, the corrected lemma, the two certificate constructions, the reduction to LP duality, and the threshold arithmetic), a new §8.5 in `DISCREPANCIES.md` recording D51.1–D51.4 and P51a–P51e, and the `#print axioms` block in `RequestProject/Main.lean`. All work is committed and pushed.

# Summary of changes for run a0662c60-a23e-4898-a2b3-9491f88d22c8
## What was done this session

Continuing the folded Reed–Solomon list-decoding work, I pushed the linear-list-size ("`L = O(1/η)`") programme to a sharper, coordinate-free form, formalised the new mathematics in Lean with no `sorry` and no new axioms, and completed the documentation duties.

### New Lean file: `RequestProject/Root/CodingTheory/FlagCertificate.lean`

A **fractional flag certificate** for a finite set `S` of words is a family of nonnegative weights `w U` on subspaces of the code (rank `≤ r`) with

* budget `∑_U w U · dim U ≤ |S| − 1`, and
* covering `agree(y,S,i) − 1 ≤ ∑_U w U · dim(U ⊓ Ker_i)` for every coordinate `i`.

Proved (all sorry-free, axioms `propext` / `Classical.choice` / `Quot.sound` only):

* `excess_le_of_flagCertificate` — a certificate implies the excess budget `excess ≤ (|S| − 1)·τ(r)·n`; the dimension factor produced by the subspace design is paid for by the certificate's budget, not by the list size (this is the amortisation).
* `hasExcessBudget_of_flagCertificates`, `listDecodable_of_flagCertificates` — uniform certificates give list size `L + 1` at radius `(L/(L+1))(1 − τ(r))·n`, i.e. `O(1/ε)` at capacity with the sharp constant.
* `flagCertificate_of_finrank_le_one` and `flagCertificate_of_plane_occupancies` / `flagCertificate_of_finrank_le_two` — affine lines and affine **planes** always carry a certificate, the plane one built explicitly from the two largest agreement counts (`w L₁ = P₁ − P₂`, `w V = (|S| − 1 − (P₁ − P₂))/2`, total weighted dimension exactly `|S| − 1`).
* `excess_le_of_finrank_le_two_certificate` — the dimension-two excess budget re-proved through the certificate, now **without** the monotonicity hypothesis `τ(1) ≤ τ(2)` that the earlier direct proof needed.

### Numerical validation (exact rational arithmetic, new script `analysis/fractional_flag_lp.py`)

The certificate is exactly the linear-programming dual of the excess budget quantified over all coordinate families at once. A Bland-rule simplex over the rationals (no floating point) found **0 counterexamples** in 1010 random point sets over `F₂²·³·⁴`, `F₃²·³`, `F₅²`, and in the exhaustive families: all 127 sets of `F₂³` and all 255 of `F₃²` containing `0`, and all 4943 sets of size `≤ 6` in `F₂⁴`. Every instance is tight (LP value `= |S| − 1`). Two natural greedy constructions of the certificate were checked and both overshoot (budgets `25/3` and `22` against the optimum `7`) on an explicit 8-point example of two skew lines in `F₅³`, evidence that no purely local rule builds it.

### Honest status of the mission goals

* The linear list size is proved **unconditionally only for affine layers of dimension ≤ 2** (lines and planes). For general layers it remains an explicit hypothesis (`HasExcessBudget` / `HasFlagCertificates`), never an axiom.
* The target statement as written in the request — list size `≤ L` at radius `(L/(L+1))(1 − τ(L))` — is **false**; the formalised `F₃` repetition-code counterexample shows the sharp shape is `L + 1`, and all statements use that form.
* The `26·2^158` folded-RS threshold is a theorem **conditional** on the excess budget. The repository's **unconditional threshold is unchanged at `2^173`**, as the freeze list requires; the quadratic result is untouched.
* The secondary branch (ordinary RS) was not started, since the primary goal is resolved only in dimension ≤ 2.

### Documentation and audit

`RESULTS.md` gained §50 (the excess reduction, the bridge, the unconditional dimension-1 and dimension-2 budgets, the sharpness counterexample, the conditional threshold, the refuted proof routes) and §50.7 (the certificate route and its LP validation). `DISCREPANCIES.md` gained §8 with proved rows, discrepancy rows against the mission statement, and open rows recording the precise obstruction. `RequestProject/Main.lean` carries `#print axioms` for every new result; `lake build` completes successfully (8158 jobs) with no errors and no warnings from the new file, and no `sorry`/`admit` anywhere. All work is committed and pushed.


# Summary of changes for run 54d9d141-1223-45a1-a4b3-c6ef1e77af51
## Weryfikacja instrukcji

Instrukcja została sprawdzona **przed** pisaniem Lean, za pomocą skryptów walidacyjnych na dokładnej arytmetyce całkowitej/ułamkowej (`analysis/srivastava_line_case_check.py`, `analysis/srivastava_induction_check.py`, `analysis/srivastava_threshold_check.py`).

Wynik weryfikacji: **dosłowny cel instrukcji, `|L_H(y)| ≤ (r−1)² + 1`, jest fałszywy.** Kontrprzykład: kod powtórzeniowy nad `F₃` o długości `n = 3` (jest to subspace design z `τ ≡ 0`), `r = 2`, promień `δ = (r/(r+1))(1−τ) = 2/3`, słowo odebrane `y = (0,1,2)`: prosta zawiera 3 słowa kodowe `000, 111, 222`, podczas gdy `(r−1)²+1 = 2`.

Poprawiona (i udowodniona) wersja, która zachowuje całą intencję instrukcji — amortyzację zamiast czynnika `G` na wymiar — to `M ≤ 1 + d·r` wewnątrz warstwy wymiaru `d ≤ r` przy tym samym promieniu `δ ≤ (r/(r+1))(1 − τ(r))`. Jest ona ciasna dla `d = 1`, zgadza się z żądanym przypadkiem prostej (`≤ 2`) i daje żądane `L ≤ 1 + r² = O(1/ε²)`. Sercem dowodu jest warunek arytmetyczny `n + r·b(d) ≤ (1 + d·r)(n − e)`, w którym składniki zależne od liczby współrzędnych „zdegenerowanych” znoszą się tożsamościowo — to właśnie globalny budżet deficytów rangi zamiast kosztu mnożonego na każdym wymiarze.

## Co zostało sformalizowane (wszystko bez `sorry`, tylko aksjomaty `propext`, `Classical.choice`, `Quot.sound`)

Warstwa abstrakcyjna (nie ruszano `foldedRS_subspaceDesign`, definicji MCA ani starych twierdzeń):
- `RequestProject/Root/CodingTheory/SrivastavaInduction.lean` — `card_le_of_coset_amortised` (indukcja dwubudżetowa z abstrakcyjnym budżetem `b`) oraz `listDecodable_of_design_amortised`.
- `RequestProject/Root/CodingTheory/SrivastavaAbstract.lean` — `card_le_of_coset_design`, `list_bound_two_budget`, `line_case_bound` (przypadek prostej), sformułowane w istniejącym języku `IsSubspaceDesign C τ`.

Instancjacja dla folded Reed–Solomon:
- `RequestProject/Root/CodingTheory/FoldedRSListDecodingImproved.lean` — `capacityListSizeQuad ε := 1 + ⌈2/ε⌉²`, `foldedRS_capacity_listDecodable_quadratic_nat`, `foldedRS_listDecoding_quadratic`, `foldedRS_listDecoding_quadratic_ceil`.
- `RequestProject/Root/CodingTheory/FoldedRSMCAQuadratic.lean` — `foldedRS_epsMCA_unconditional_quadratic`, `..._exists` oraz konkretny próg `foldedRS_threshold_quadratic_2_173`: dla `n = 2²⁰`, `η = 2⁻¹⁰`, `s ≥ 67125251`, `|F| ≥ 2¹⁷³` zachodzi bezwarunkowo `ε_mca ≤ 2⁻¹²⁸` (bez założenia list-dekodowalności — rozmiar listy `L = 1 + 2²⁴` pochodzi z nowego twierdzenia).

Efekt liczbowy: przy tych samych parametrach wymagany rozmiar ciała spada z `2^98305` (dawny rozmiar listy `(1/η)^{O(1/η)}`) do `2^173`.

## Dokumentacja i budowa

`RESULTS.md` §49 (z tabelą progów i nazwami twierdzeń), `DISCREPANCIES.md` (wiersz P49; wiersz O59 oznaczony jako zamknięty na poziomie `O(1/η²)`, wciąż otwarty na `O(1/η)`), `#print axioms` dla wszystkich nowych wyników w `RequestProject/Main.lean`. Pełne `lake build` przechodzi bez błędów (8154 zadania), audyt aksjomatów potwierdza wyłącznie aksjomaty standardowe. Wszystko zacommitowane i wypchnięte.

Otwarte: liniowy rozmiar listy `O(1/η)` (kierunek Chen–Zhang) — zgodnie z instrukcją nie był podejmowany.


# Summary of changes for run 2b8c3eba-e58b-4e1c-81b3-b26fe23ef2f5
## What was done

The last external hypothesis of the folded Reed–Solomon MCA chain — capacity list-decodability — is now **proved unconditionally**, and the capacity-level strong MCA bound is stated and proved with no list-decodability assumption.

### New Lean results (all `sorry`-free, only `propext` / `Classical.choice` / `Quot.sound`)

**`RequestProject/Root/CodingTheory/CapacityListDecoding.lean`** — the abstract combinatorial core, driven entirely by the sharp subspace-design inequality already in the project:
- `card_agree_le_succ_finrank` — pointwise bound: at each coordinate, at most `1 + dim(V ⊓ Ker_x)` members of an affinely independent family of codewords agree with the received word.
- `singleton_bound` — average-radius **relaxed generalized Singleton bound** for affinely independent tuples: `(s−m+1)·(m+1)·(n−e) ≤ (s−m+1)·n + m·K`. This caps the affine dimension of a list at capacity.
- `card_le_of_coset` — coset recursion giving `M ≤ G^d` inside a `d`-dimensional coset.
- `listDecodable_of_design`, `listDecodable_of_design_top` — the assembled machine.

**`RequestProject/Root/CodingTheory/FoldedRSCapacityListDecoding.lean`**
- `foldedRS_capacity_listDecoding` — folded RS is `G^{d₀}`-list-decodable at every radius `e ≤ (1−ρ−ε)·n`, for `8d₀ ≤ εs`, `d₀²+2d₀ ≤ s`, `d₀, G ≥ 2/ε`.
- `foldedRS_capacity_listDecoding_ceil` — canonical form: folding `s ≥ 16/ε² + 8/ε + 3` (i.e. `s = Θ(1/ε²)`, as in the literature), list size `capacityListSize ε = ⌈2/ε⌉^⌈2/ε⌉`.
- `foldedRS_capacity_listDecoding_exists` — the existential form requested.

**`RequestProject/Root/CodingTheory/FoldedRSMCAUnconditional.lean`**
- `amplified_budget_le_listSize`, and `foldedRS_epsMCA_unconditional`: with the GG25 parameters and `s ≥ 64/η² + 16/η + 3`, at every radius `e ≤ (1−ρ−η)·n`, `ε_mca(C, e) ≤ (L·n + 24/η³)/|F|` with `L = ⌈4/η⌉^⌈4/η⌉` — **no list-decodability hypothesis**. Plus `foldedRS_epsMCA_unconditional_exists`.

### Honest accounting

The list size proved is `(1/ε)^{O(1/ε)}` — **not** the `O(1/ε)` of Chen–Zhang 2025 nor the `O(1/ε²)` of Srivastava 2025. The sharp Singleton counting is available only for affinely *independent* tuples (where it is tight); passing from affine dimension to cardinality costs a factor per dimension via the coset recursion, and no constant-factor slack can be absorbed at capacity. This is recorded as a new open item (row O59) rather than glossed over.

Consequently, at `n = 2²⁰`, `η = 2⁻¹⁰`, `ε_mca ≤ 2⁻¹²⁸` the unconditional theorem requires `|F| ≥ 2^98305` (binding constraint is `(L+1)² ≤ |F|`; the error term alone needs `2^49301`), computed in exact integer/rational arithmetic by `analysis/foldedRS_unconditional_threshold.py`. The previously established conditional `26·2¹⁵⁸` threshold and the earlier unconditional `8n/η²` result are untouched and remain the practically relevant statements at these parameters.

### Validation and freeze list

Numerical pre-verification (`analysis/foldedRS_capacity_list_check.py`, exact arithmetic, no floating point) checked the design inequality, the pointwise bound, the Singleton bound, the coset recursion and end-to-end list sizes on explicitly generated small folded RS codes — 124 500+ instances, zero violations.

Nothing on the freeze list was modified: MCA definitions, `foldedRS_epsMCA_literature`, `foldedRS_threshold_2_158` and `GG25FoldedRS.lean` are unchanged; no axioms were added; no Verus/engineering work was done.

### Documentation

`RESULTS.md` gained §48 (mechanism, statements, threshold table, validation); `DISCREPANCIES.md` gained row P48, an updated row O57 (now closed as a finite unconditional list size, still open at `O(1/η)`), and the new row O59; `RequestProject/Main.lean` prints axioms for all eleven new statements.


# Summary of changes for run 5d453e9a-5db3-4976-ab53-5f3ea99e6aa5
## What was delivered

The GG25 Theorem 3.6 chain is now formalized in Lean, and the literature constant for folded Reed–Solomon mutual correlated agreement is proved for the **strong** (no-slack) notion `epsMCAmax` — the same quantity bounded by the previously proved unconditional `8n/η²` result, which is left completely untouched.

**New / completed modules** (all under `RequestProject/Root/CodingTheory/`):

1. `ListDecodable.lean` — `ListDecodable C e L`; monotonicity; `listDecodable_of_minDist` (unconditional `L = 1` when `2e < d`); `bigPairs`; and the **pair-collapse lemma** `card_bigPairs_le_of_listDecodable`: with `L`-list-decodability at radius `e′` and `(L+1)² ≤ |F|`, at most `L` pairs of codewords admit a common agreement set of size `≥ n − e′` with a given pair of words. The proof is the challenge-averaging argument (distinct pairs give distinct `c₀ + γc₁` for one good `γ`).
2. `LineDecodableAmplification.lean` — `lineDecodable_amplification`: from `(1, e, a, t)`-line-decodability with `t ≥ 2`, `e ≤ (t−1)θ`, plus `L`-list-decodability at `e + θ`, one gets `(1, e, a + L·(b−1), b)`-line-decodability for **every** `b` — an additive, not multiplicative, cost in the block length. Plus the composition with the frozen strong bridge.
3. `SharpLineMCAAmplified.lean` — the combined chain for a general code (`epsMCAmax_le_of_subspaceDesign_listDecodable`). The pre-existing `SharpLineMCA.lean` was left intact.
4. `FoldedRSListDecodable.lean` — `foldedRS_listDecodable_johnson`: **unconditional** list-decodability of folded RS in the Johnson regime, by unfolding to the ordinary Reed–Solomon code and applying the project's Guruswami–Sudan bound.
5. `FoldedRSMCAFinal.lean` — `foldedRS_epsMCAmax_amplified`; the pure arithmetic lemma `amplified_budget_le`; **`foldedRS_epsMCA_literature`**: `ε_mca(C, e) ≤ 2n/(η|F|) + 24/(η³|F|)` at every radius `e ≤ (1 − ρ − η)·n`; and **`foldedRS_threshold_2_158`**: `n = 2²⁰`, `η = 2⁻¹⁰`, `|F| ≥ 26·2¹⁵⁸ ⇒ ε_mca ≤ 2⁻¹²⁸`. Two unconditional corollaries of the same mechanism are also proved: `foldedRS_epsMCAmax_amplified_uniqueDecoding` (`L = 1`) and `foldedRS_epsMCAmax_amplified_johnson` (no list-size hypothesis).

**What is conditional, stated plainly.** `foldedRS_epsMCA_literature` and `foldedRS_threshold_2_158` carry exactly one hypothesis that is not proved here: `ListDecodable (foldedRSCode …) (e + ⌊ηn/2⌋) L` with `L ≤ 2/η`, i.e. capacity-approaching list-decoding of folded Reed–Solomon with list size `O(1/η)`. It is a hypothesis of the statement, **never an axiom**, and it is the only external input; every other link (sharp subspace design `τ(r) = sρ/(s−r+1)`, the pruning count, the pair-collapse lemma, the amplification loop, the strong bridge) is proved in the project. The hypothesis set is demonstrably satisfiable — the unique-decoding and Johnson corollaries discharge it from results proved here.

**Validation before Lean.** `analysis/gg25_amplification_check.py` (exact integer / rational arithmetic, no floating point) checks the pair-collapse counting, the counting core with slack, the peeling-loop accounting, and the parameter arithmetic plus the `2⁻¹²⁸` threshold — all four parts pass.

**Freeze respected.** The MCA definitions, `GG25FoldedRS.lean` (the `8n/η²` bound, threshold `2¹⁷²`), `SharpLineMCA.lean` and the ordinary-RS material are unchanged; no axioms were added; no definition was weakened.

**Verification.** `lake build` completes successfully with zero errors; no `sorry`/`admit` occurs anywhere in the Lean sources (the only textual matches are docstring prose). `RequestProject/Main.lean` `#print axioms`-checks all eleven new results; every one depends only on `propext`, `Classical.choice`, `Quot.sound`.

**Documentation.** `RESULTS.md` gained section 47 describing the chain, the constant, the threshold, and the conditional input; `DISCREPANCIES.md` gained row `P47` (what is proved), row `O58` (the gap to the literature constant, now closed modulo the list-decoding input) and row `O57` (the remaining open item: an unconditional `L = O(1/η)` list-size bound for folded RS at capacity). `ARISTOTLE_SUMMARY.md` was not edited. All work is committed and pushed.


# Summary of changes for run 56f43435-1a68-4f16-833a-086b5c59c1d7
Wykonałem wskazany etap GG25 §4.2–4.3 — najpierw walidację numeryczną, potem formalizację. Cały projekt buduje się czysto (`lake build`), bez `sorry` i bez nowych aksjomatów (audyt `#print axioms` w `RequestProject/Main.lean`: tylko `propext`, `Classical.choice`, `Quot.sound`). FREEZE zachowany: definicja MCA, most `card_badSet_lt_of_lineDecodable` i twierdzenie z progiem `2¹⁷²` (`GG25FoldedRS.lean`) pozostały nietknięte.

**1. Walidacja (Python, arytmetyka dokładna, bez zmiennoprzecinkowej)** — `analysis/gg25_random_pruning_check.py`:
* Część A: algorytm PRUNE z wagami `∝ dim H − dim H_i` na 1052 dopuszczalnych instancjach (reżim `ε ≥ 2/r`, `δ = 1 − τ(r) − ε ≥ 0`) — 0 naruszeń Lematu C, najmniejszy stosunek `Pr/(ε/(r+ε))` = 55/14;
* Część B: deterministyczna wersja przycinania — 622 instancje, 0 naruszeń;
* Część C: rdzeń zliczający z luzem — 1267 instancji, 0 naruszeń;
* Część D: stałe i progi.

**2. Nowe moduły Lean (wszystko udowodnione)**
* `Root/CodingTheory/PinnedSubspace.lean` — `pinnedSubspace` (Def. 4.4), Lemat B (`eq_of_agree_on_of_pinned_eq_bot`), krok algorytmu z nierówności subspace-design (`exists_coord_not_le_coordKer`) oraz **deterministyczny rdzeń PRUNE** (`exists_pinning_subset`: każdą podprzestrzeń `H ≤ C` wymiaru `≤ r` można wyzerować `≤ r` współrzędnymi wziętymi z dowolnego zadanego zbioru zgodności, gdy `e ≤ (1 − τ(r) − ε)n` i `r < εn`), a stąd ograniczenie rozmiaru listy `ncard_close_le_of_pinning` (bez argumentu Johnsona).
* `Root/CodingTheory/SharpLineMCA.lean` — rdzeń zliczający z luzem `(b−1)(n − e − |T|) ≤ e`, pojęcie `SlackCorrelatedAgreement` i most: przy luzie `θ` wystarczy `b ≥ 2 + e/θ` zamiast `b ≥ e + 2`.
* `Root/CodingTheory/FoldedRSSharp.lean` — złożenie z folded RS: `ε_err ≤ (8/η² + 1)·b/|F|`, czyli dla `θ = ηn` około `(8/η³ + 16/η²)/|F|` — **długość bloku znika ze stałej**; konkretnie dla `n = 2²⁰`, `η = 2⁻¹⁰`, `θ = 2¹⁰` wystarcza `|F| ≥ 2¹⁶²`, by błąd wynosił `≤ 2⁻¹²⁸`.

**3. Odpowiedź badawcza (uczciwie).** Sam mechanizm losowego przycinania nie może poprawić stałej: jego konkluzją jest dokładnie Tw. 4.7 dla `ℓ = 1` z parametrem `b = ⌈(ε/(r+ε))a⌉`, które projekt już ma. Cała strata siedzi w moście: dla mocnej (zamrożonej) wersji MCA potrzeba `b ≥ e + 2 ≈ n`, co daje `≈ 8n/η²` i próg `2¹⁷²`. Wersja z luzem `θ = ηn` wymaga tylko `b ≈ 1/η` i osiąga skalę literaturową (nasze `2³³ + 2²⁴` wobec `26·2³⁰`, próg `2¹⁶²` wobec `26·2¹⁵⁸ ≈ 2¹⁶²·⁷`) — ale przy słabszej konkluzji (wspólny zbiór zgodności rozmiaru `≥ n − e − θ` zamiast `≥ n − e`). Probabilistycznego Lematu C dla jawnego rozkładu nie twierdzę: nie znalazłem kontrprzykładu w małych przypadkach, ale naturalny dowód indukcyjny dla wag proporcjonalnych do spadku wymiaru się nie domyka (relaksacje Cauchy'ego–Schwarza/Jensena wymaganej nierówności są fałszywe dla małych `ε`); pozycja jest jawnie zapisana jako otwarta i nic się na niej nie opiera.

**4. Dokumentacja:** nowa sekcja 46 w `RESULTS.md`, wiersz P46 oraz nowe pozycje otwarte O55 (lokalizacja luki i jej domknięcie w wersji z luzem) i O56 (probabilistyczny Lemat C) w `DISCREPANCIES.md`, z aktualizacją O54. Tabela Properties zawiera nowe definicje i twierdzenia. Wszystko zacommitowane i wypchnięte. Bez zmian: nie wykonano żadnych benchmarków, więc nie formułuję porównań wydajnościowych, a kontrakty w `verus/` pozostają niesprawdzone maszynowo.

# Summary of changes for run 11dec6b3-fabf-44bf-bb63-7600cc42c206
## What was done

**Step 1 — freeze respected.** `RequestProject/Root/CodingTheory/GG25FoldedRS.lean` was not touched: `foldedRS_epsMCAmax_le_capacity` and `foldedRS_epsMCAmax_le_two_pow_neg_128` keep their exact statements and hypotheses (confirmed by the commit diff), as do all other existing results.

**Step 2 — literal GG25 definition added.** New file `RequestProject/Root/CodingTheory/GG25LiteralMCA.lean` states GG25 Definition 2.8 for ℓ = 1 in its perfect (γ = 0) form — `GG25IsBad`, `gg25BadSet`, `GG25MutualCorrelatedAgreement`, with relative radii `δ' ≤ δ`, the size condition `|S| ≥ (1−δ')n`, and the GG25 failure clause "`u₀|_S ∉ C|_S` or `u₁|_S ∉ C|_S`". The project's existing notion was left untouched and only re-packaged, as `StrongMCA C δ err := ∀ e ≤ δ·n, ε_mca(C,e) ≤ err`, on top of the existing `epsMCA`.

**Step 3 — implication proved (and more).** `strongMCA_implies_GG25MCA` is proved with a real proof, no `sorry`. In the course of proving it, the set-containment argument turned out to be an **equality**, so two further theorems were proved:
* `gg25BadSet_eq_badSet` — the GG25 bad set at radius `δ'` *is* the project's bad set at radius `⌊δ'·n⌋` (with the radius dictionary `card_cond_iff`);
* `not_lineAgreeOn_iff` — the mathematical reason: over a submodule, "some point of the line fails to agree with a codeword on `S`" and "`u₀` or `u₁` fails to agree with a codeword on `S`" are the same condition (line closure one way; the challenges γ = 0 and γ = 1 the other);
* hence `gg25MCA_implies_strongMCA` and `strongMCA_iff_GG25MCA` (for positive block length).

So, honestly reported: the project's notion is **not** strictly stronger than GG25 Def. 2.8 for ℓ = 1 — the two are equivalent. I therefore did not write the (false) claim that GG25 MCA fails to imply the project's notion; the documentation records the equivalence instead. As a payoff, the frozen capacity-level result is restated in GG25 language: `foldedRS_gg25MCA_two_pow_neg_128` gives `(1, 1−ρ−2⁻¹⁰, 2⁻¹²⁸)` mutual correlated agreement for folded Reed–Solomon at `n = 2²⁰`, `|F| ≥ 2¹⁷²`.

**Step 4 — numerical check.** `analysis/gg25_definition_gap_check.py` computes both bad sets exactly (integer/`Fraction`, no floating point) over small fields, random linear codes, random lines and all radii: 1944 instances, 0 mismatches, ratio strong/GG25 always exactly 1 — matching the Lean theorem.

**Step 5 — documentation.** `RESULTS.md` §45 (comparison table, what is proved, honest reading of the constant gap, the numerical check); `DISCREPANCIES.md` rows O52 (definitions compared: equivalent, implication proved), O53 (the literature constant `2n/η + 24/η³` bounds the *same* quantity, so the gap to the proved `≈ 8n/η²` is a difference of proofs — random pruning of GG25 §4.2–4.3 versus the reconstructed rank argument), O54 (the smaller field-size threshold remains open; `2¹⁷²` is what is proved and it cannot be improved by weakening the definition); `README.md` gained a coding-theory paragraph. `ARISTOTLE_SUMMARY.md` was not modified.

**Step 6 — audit.** Full `lake build` succeeds (8139 jobs, no errors); no `sorry`/`admit` anywhere in `RequestProject/` (only docstring text mentioning the word); `#print axioms` on all new theorems reports exactly `propext, Classical.choice, Quot.sound`, and the checks are wired into `RequestProject/Main.lean`. Linter warnings in the new file were fixed at the root (`omit` on genuinely unused section instances). Everything is committed and pushed.


# Summary of changes for run f15de478-b786-45c5-a5af-7a6ac1cab26d
## Wykonano całą poprawioną instrukcję (STEP 1–6). Wszystko kompiluje się bez `sorry` i bez nowych aksjomatów.

### STEP 1 — pre-weryfikacja numeryczna
`analysis/gg25_thm47_line_check.py` (dokładna arytmetyka wymierna, bez zmiennoprzecinkowej) przeszukuje małe losowe kody, generuje wszystkie rodziny „proximates” i sprawdza samo twierdzenie oraz trzy filary dowodu. Wynik: 129 rodzin, 0 naruszeń → **PASS**. Kontrprzykładu nie znaleziono, więc kontynuowano.

### STEP 2–3 — GG25 Thm 4.7 dla prostych (ℓ = 1), **z parametrami z pracy**
`RequestProject/Root/CodingTheory/GG25LineDecodable.lean`:

`subspaceDesign_implies_lineDecodable` : `IsSubspaceDesign C τ → LineDecodable C e a ⌈(ε/(r+ε))·a⌉` dla każdego `r > 0`, **`ε ≥ 2/r`** (ograniczenie dolne) i `e ≤ (1 − τ(r) − ε)·n`. Stara (błędna) wersja z `0 < ε ≤ 1/(2r)` i `b = ⌈εa⌉` nie została użyta.

Dowód z pracy (random pruning) nie był dostępny, więc zrekonstruowano samodzielny argument — **rachunek rangi w przestrzeni konfiguracji** `F × F × (ι → A)`, `ψ(α) = (1, α, f α)`, `defectSpace`, `defectDim`. Rolę lematu o przycinaniu pełnią trzy udowodnione filary:
* `sum_defectDim_le` — nierówność główna `Σᵢ defectDim f Tᵢ ≤ τ(r)·defectDim f T·n`;
* `defectDim_le_two_mul_K` — ograniczenie rangi `defectDim f Z ≤ 2K`, `K = (1−τ(r)−ε)/ε` (jedyne miejsce, gdzie wchodzi `rε ≥ 2`);
* `card_le_one_add_K_mul_defectDim` — indukcja główna `|T| ≤ (1 + K·defectDim f T)·b*(T)`.

### STEP 4 — połączenie z folded RS
* `foldedRS_isSubspaceDesign_gg25` (`FoldedRSSubspaceDesign.lean`) — **ostra** stała GG25 `τ(r) = (k−1)/((s−r+1)|B|) = sρ/(s−r+1)`; wcześniejsza wersja niosła zbędny czynnik `r`, który sam w sobie czynił promień pojemnościowy ujemnym.
* `epsMCAmax_le_of_subspaceDesign` — most subspace-design ⇒ MCA (bez hipotezy list-decodability).
* Nowy plik `RequestProject/Root/CodingTheory/GG25FoldedRS.lean`: `foldedRS_epsMCAmax_le_gg25`, `foldedRS_epsMCAmax_le_capacity` (dla `ε = η/2`, `r = 4/η`: **`ε_mca ≤ (8/η² + 1)(e+2)/|F|` przy każdym promieniu `e ≤ (1 − ρ − η)·n`**) oraz konkretny przypadek `foldedRS_epsMCAmax_le_two_pow_neg_128` (`n = 2²⁰`, `η = 2⁻¹⁰`, `|F| ≥ 2¹⁷²` ⇒ `ε_mca ≤ 2⁻¹²⁸`).

To pierwszy w projekcie **bezwarunkowy, pojemnościowy** wynik MCA.

### Odpowiedzi na dwa pytania badawcze
1. **Czy dla ℓ = 1 potrzebna jest list-decodability?** Nie. `card_badSet_lt_of_lineDecodable` wyprowadza `#badSet < a` wyłącznie z line-decodability i `b ≥ e + 2`, ponieważ używany tu zbiór „zły” jest wersją silną, a dwa punkty prostej afinicznej nad ciałem wyznaczają ją jednoznacznie. Zapisane jako nowy wiersz O51 w `DISCREPANCIES.md`.
2. **Stała końcowa.** Pełna algebra jest w `RESULTS.md` §44 i w wierszu O50. Wynik: `r = 4/η`, `ε = η/2`, `s = Θ(ρ/η²)` z budżetu `ρ(r−1) ≤ (η/2)(s−r+1)`, `δ = 1 − ρ − η`, współczynnik `(r+ε)/ε = 8/η² + 1`. **Stała to ≈ `8n/η²`, a nie `2n/η + 24/η³`**, i próg to `|F| ≥ 2¹⁷²`, a nie `26·2¹⁵⁸` (za mało o ok. `2⁹`). To nie jest luz w rachunkach: most wymaga `b ≥ e + 2`, więc `a ≥ ((r+ε)/ε)(e+2)`, a `(r+ε)/ε ≥ 2/ε² ≥ 2/η²` dla dowolnej dopuszczalnej pary `(r, ε)` z `rε ≥ 2`, `ε ≤ η` — żaden wybór parametrów w tym argumencie nie zejdzie poniżej `≈ 2/η²`.

### STEP 5 — sprawdzenie całego łańcucha
Nowy `analysis/folded_rs_thm47_check.py` (dokładne `Fraction`, brak sympy/z3 w środowisku): część A weryfikuje ostrą stałą projektową na 2 127 446 podprzestrzeniach małych kodów folded RS, część B algebrę budżetów, część C próg `b ≥ e+2`, część D konkretną instancję `2⁻¹²⁸`. Wynik: **PASS**, 0 naruszeń.

### STEP 6 — dokumentacja
`RESULTS.md` §44 (nowa sekcja), `DISCREPANCIES.md`: wiersze O49 i O50 zamknięte z pełnym opisem, dodany wiersz O51. Wszystkie dziewięć nowych twierdzeń ma `#print axioms` w `RequestProject/Main.lean` i zależy wyłącznie od `propext`, `Classical.choice`, `Quot.sound`.

### FREEZE
Przestrzegany: nie wracano do ordinary RS / Fitting / Johnson, nie strojono stałych przed dowodem Thm 4.7, nie dowodzono minimalnej odległości folded RS, nie tworzono osobnego pojęcia MCA dla folded RS.

Uwaga: `ARISTOTLE_SUMMARY.md` nie był modyfikowany. Poprawiono także wszystkie ostrzeżenia lintera w nowych i dotkniętych plikach.

# Summary of changes for run 2ac645a7-6c79-4fda-85be-40bb090ffa3b
## What was completed this session

The main deliverable is **Stage 3 of the GG25 route: the sharp subspace-design constant τ(r) = sρ/(s−r+1) for folded Reed–Solomon codes**, now fully proved in Lean with no `sorry` and depending only on `propext`, `Classical.choice`, `Quot.sound`.

### `RequestProject/Root/CodingTheory/FoldedRSSubspaceDesign.lean`
Completed and building clean. It contains the multiplicity machinery and the two headline results:

* `pow_sub_C_dvd_det` — if `d` columns of a polynomial matrix vanish at `y`, then `(X − y)^d` divides its determinant;
* `exists_adapted_basis` — an invertible change of basis putting `dim U` columns inside a given subspace `U`;
* `pow_dvd_det_of_kernel` — the corank form of the above;
* `sum_rootMultiplicity_le_natDegree`, `sum_rootMultiplicity_comp_le` — distinct points contribute disjointly to the degree;
* **`foldedRS_design_sharp`** — for every subspace `W` of the folded code with `dim W ≤ r ≤ s`,
  `(s − r + 1) · Σ_x dim(W ∩ C_x) ≤ r·(k − 1)`;
* **`foldedRS_isSubspaceDesign_sharp`** — the same, phrased with the project's generic `IsSubspaceDesign` predicate and `τ(r) = r(k−1)/((s−r+1)·|B|)`, i.e. `τ(r) ≤ s·ρ·r/(s−r+1)` — exactly the requested `τ(r) = sρ/(s−r+1)` per unit of `dim W`.

The argument: after an `F`-linear change of basis of `W`, the first `dim(W ∩ C_x)` columns of the folded Wronskian matrix vanish at each of the `s − r + 1` shifted points `γ^u x` (`0 ≤ u ≤ s − r`); the folding-domain hypothesis makes all these points pairwise distinct across `x` and `u`, so the multiplicities add and are capped by the degree bound `r(k−1)` on the folded Wronskian. Hypotheses used: `γ ≠ 0` of multiplicative order at least `k`, `IsFoldingDomain B s γ`, and `r ≤ s`.

This closes the long-standing open row about the `r ≥ 2` cases of the design property (previously only `r = 1` and `r = 2` were available, and only with a much larger constant).

### Verification and housekeeping
* `RequestProject/Main.lean` now imports the two new modules and `#print axioms`-checks the five new results; a full `lake build` completes successfully (8136 jobs) with no errors and no `sorry` anywhere in the project.
* `RESULTS.md` gained three new sections: §41 (Stage 1 — generic line-decodability ⇒ MCA, and the concrete folded threshold), §42 (the general-`r` folded Wronskian), §43 (Stage 3 — the sharp design constant).
* `DISCREPANCIES.md`: the row on the `r ≥ 2` design cases is marked **closed**, and two new rows record what remains open.

### What remains open (honestly recorded, not claimed)
* **GG25 Theorem 4.7 for lines** (subspace design ⇒ line-decodability at the capacity radius `1 − τ(r) − ε` with `b = ⌈εa⌉`) is **not** proved. The purely existential weakening suggested in the instruction is vacuous (`b = 0`, or `a = b = 2`, both already true), so it was deliberately not stated as a theorem. A note explains why the sharp design alone does not close the gap: feeding it into the existing pair-list bridge requires intersecting `t` vanishing sets, which costs `4et` coordinates and makes the resulting condition strongest at `t = 1`, where it is just the minimum-distance condition already in use; GG25 instead uses the design as an *average* via random pruning, and that pruning step is the missing ingredient.
* Consequently the capacity-level bound `ε_mca ≤ 2n/(η|F|) + 24/(η³|F|)` and its threshold at the capacity radius are still open. The concrete `2⁻¹²⁸` threshold that *is* proved (`folded_threshold_2_128`, `|B| = 2²⁰`, `|F| ≥ 26·2¹⁵⁸`) holds at the unique-decoding-type radius `4e < |B| − ⌊(k−1)/s⌋`, and the documentation states explicitly that it must not be read as the capacity-radius statement.

All work is committed and pushed.

# Summary of changes for run f63e7fa4-fd0c-4b68-80a2-8e50f736b34c
## Answers to your eight questions (written up in `FOLDED_RS_DESIGN_NOTES.md`)

1. **Folded word representation** — option B, `D → (Fin s → F)`, i.e. `↥B → Fin s → F` with alphabet `A = Fin s → F`. It reuses the existing Hamming layer with no new code (a distance of 1 is a whole block, exactly the folded metric), gets its module structure from `Pi.addCommGroup`/`Pi.module`, needs no adaptation of `Polynomial.eval`, and makes the line combination `f₀ + γ • f₁` the action of the *scalar* field. `Matrix (Fin s) D F` puts the block index in the wrong slot for Hamming distance; a custom `Alphabet F s` would have to re-derive instances that `Fin s → F` already has.
2. **Generalising the MCA definitions** — option A: one new alphabet-generic file, no refactor. `AlphabetMCA.lean` develops `AgreeOn`, `LineAgreeOn`, `CloseTo`, `IsBad`, `badSet`, `goodZ`, `epsMCA`, `epsMCAmax`, `MinDistGe` for an arbitrary finite `F`-module alphabet, with challenges always drawn from `F`; `AlphabetInstances.lean` bridges it to the existing ordinary-RS definitions (they are proved *equal*, not re-stated), so nothing downstream had to change. No `HammingSpace` class was needed.
3. **Modelling γ** — as a field element together with an explicit distinctness hypothesis `IsFoldingDomain B s γ` (the `s·|B|` unfolded points are pairwise distinct), which is what every counting argument actually uses and is implied by the usual coset construction (`isFoldingDomain_of_cosets`). For the Wronskian/design results one further needs γ to have order at least `k`, and that hypothesis is provably necessary.
4. **Mathlib coverage** — everything needed exists; two names from your checklist do not: use `Module.finrank` (not `Submodule.finrank`) and `Pi.module` (not `Pi.instModule`).
5. **Additive margin law** — reusable unchanged: it only mentions bad-challenge subsets of `F`. This is now recorded as an alphabet-generic theorem covering two different codes with two different alphabets.
6. **Order of work** — your ordering is right; it is the one followed, with the generic layer inserted first so ordinary and folded RS share one proof.
7/8. **Documentation** — `DISCREPANCIES.md` rows **O46** (BCHKS ordinary-RS Johnson path frozen, still conditional) and **O47** (folded GG25 route is the main route) are in place, along with O44/O45/O48 for what remains open.

## New mathematics proved this session

* **General-`r` subspace design** (`SubspaceDesignGeneric.lean`): `dim V < |V|` for finite `F`-spaces, and by a double count `Σ_i dim(W ∩ C_i) ≤ (|W| − 1)·t ≤ (q^r − 1)·t` whenever every nonzero word of `W` vanishes in at most `t` coordinates; instantiated for folded Reed–Solomon as `Σ_x dim(W ∩ C_x) ≤ (q^r − 1)·⌊(k−1)/s⌋`, plus an `IsSubspaceDesign` instance. Unconditional, but with a constant exponential in `r`.
* **Folded Wronskian and the `r = 2` bound** (`FoldedWronskian.lean`): the twist `p(γy)` with its degree and leading coefficient, the folded Wronskian `p(y)q(γy) − q(y)p(γy)`, its top coefficient `lc(p)lc(q)(γ^{deg q} − γ^{deg p})`, and the key nonvanishing theorem for independent polynomials of degree `< k` when γ has order at least `k` (by a degree descent). From it: for `s ≥ 2` and two independent folded codewords, `Σ_x dim(span{c₁,c₂} ∩ C_x) ≤ 4(k−1)` — linear in the degree and independent of the field size.

Both are recorded in `RESULTS.md` §39–§40 and folded into `DISCREPANCIES.md` row O44, which notes that the sharp Guruswami–Kopparty constant and the cases `r ≥ 3` remain open.

## Verification

`lake build` completes successfully (8132 jobs); no `sorry`/`admit` anywhere in the Lean sources; `#print axioms` in `RequestProject/Main.lean` covers all new results and reports only `propext`, `Classical.choice`, `Quot.sound`. All hypotheses of the new `r = 2` theorem were checked to be load-bearing. Everything is committed and pushed.


# Summary of changes for run c85ecad1-f0a4-4003-8922-ab14505562ec
## What I did this session

Continuing the BCHKS25 / ABF work package, I verified the existing state (full `lake build` green, axiom audit clean, no `sorry`) and then added two new unconditional pieces of theory, both fully proved.

### 1. `RequestProject/Root/CodingTheory/MCALowerBound.lean` — a matching **lower** bound on `ε_mca`

Everything previously in the project bounded the mutual-correlated-agreement error from above; this file supplies the complementary lower bound, by an explicit and elementary construction. For a colouring `g : D → F` set `u₁ x = xᵏ` and `u₀ x = −g(x)·xᵏ`; the line point `u₀ + γ·u₁` is `x ↦ (γ − g x)·xᵏ`, which vanishes on the fibre `g⁻¹(γ)`, while on the *same* fibre the neighbouring point is exactly `x ↦ xᵏ` — a word that agrees with no polynomial of degree `< k` on more than `k` positions. So every large fibre yields a bad challenge.

* `not_isCloseOn_powWord` — `x ↦ xᵏ` is a codeword on no set of more than `k` positions;
* `isBad_blockWord`, `card_le_card_badSet_blockWord`, `card_div_card_le_epsMCAmax` — the counting form;
* `one_div_card_le_epsMCAmax` — **`ε_mca(C, e) ≥ 1/|F|` for every `k < |D|` and every radius `e`**;
* `card_le_epsMCAmax_of_blocks` — **`ε_mca(C, e) ≥ r/|F|`** whenever `r ≤ |F|` and `r·max(|D|−e, k+1) ≤ |D|` (so `r ≈ ⌊1/√ρ⌋` in the Johnson regime).

Combined with the previously proved upper bound this pins `ε_mca = Θ_ρ(1/|F|)` on the range covered, and shows the concrete `2⁻¹²⁸` thresholds cannot be improved below `|F| ≥ 2¹²⁸`. All of it is unconditional — no interpolation, no non-degeneracy hypothesis.

### 2. `RequestProject/Root/CodingTheory/FormalRoot.lean` — collinearity of proximates ⟺ a formal root

The concluding step of the BCHKS25/ABF argument, isolated and proved unconditionally. `IsFormalRoot k S u₀ u₁ p` says `p = Σ_j c_j(X)·Z^j`, all `deg c_j < k`, specialises at `X = x` to `u₀ x + Z·u₁ x` for `x ∈ S`.

* `lineCloseOn_of_formalRoot` / `formalRoot_of_lineCloseOn` / `lineCloseOn_iff_formalRoot` — a formal root is *equivalent* to all proximates being collinear on `S`, with `c₀ = p.coeff 0`, `c₁ = p.coeff 1`;
* `formalRoot_of_agreements` — rigidity: a candidate of `Z`-degree `≤ d` (`d ≥ 1`) matching the line at more than `d` distinct challenges is forced to be a formal root (for `d = 1` this is the classical two-challenge argument);
* `correlatedAgreement_of_formalRoot`.

So in the BCHKS25 pipeline, everything *after* "the interpolant has a linear-in-`Y` factor over `F(Z)` agreeing with the line on many positions" is now formalised unconditionally.

### Supporting work

* `analysis/mca_lower_bound_check.py` — brute-force control over `𝔽₅, 𝔽₇, 𝔽₁₁` (308 instances) confirming that each large fibre really witnesses closeness for its own line point and really refutes line-closeness, and that `x ↦ xᵏ` never agrees with a degree-`< k` polynomial on more than `k` points. It runs and passes.
* `RESULTS.md` §36 and §37 document the two new files statement by statement; `DISCREPANCIES.md` gains row O43 recording precisely what the lower bound does *not* give (an `Ω(n/|F|)`-shaped bound below the Johnson radius remains open).
* `RequestProject/Main.lean` imports both new files and runs `#print axioms` on all twelve new results; every one reports only `propext`, `Classical.choice`, `Quot.sound`.

### Honest status of the main target

The Johnson-regime bound `ε_mca ≤ C(ρ,η)/|F|` and the four concrete `2⁻¹²⁸` thresholds (`threshold_rho_{half,quarter,eighth,sixteenth}_bchks`, for `n = 2²⁰`, `η = 2⁻¹⁰`, `|F| ≥ 2¹⁶⁰`) remain **conditional** on the refined non-degeneracy hypothesis (ND′), which appears explicitly as a hypothesis of each statement — they are not claimed unconditional. The unconditional radius for line-decodability is still half the Johnson radius. This is recorded in `DISCREPANCIES.md` rows O40–O43.

The full project builds with `lake build`; nothing uses `sorry`, `admit`, new `axiom` declarations, or `@[implemented_by]`. All changes are committed and pushed.


# Summary of changes for run 903b8636-74de-4e28-9c51-77b5965c33c9
This run continued the syndrome-space work and added the quantitative layer requested, in two new Lean files. Everything builds with `lake build`, contains no `sorry`/`admit`, adds no axioms, and each new result is confirmed by `#print axioms` in `RequestProject/Main.lean` to depend only on `propext`, `Classical.choice`, `Quot.sound`. All work is committed and pushed.

**Target A — rigidity via vanishing differences** (`RequestProject/Root/CodingTheory/SyndromeQuantitative.lean`)

Notation: `n = |D|`, `k` = code dimension, `e` = error budget, strict-gap regime `k + 3e ≤ n` (i.e. `3e < d_min = n − k + 1`).

- `IsErrorFor k e f u` — admissible error vector (weight `≤ e`, `f − u` a codeword) — plus its canonical existence (`exists_isErrorFor`).
- `vanishing_differences_three` — the explicit identity `(z₁−z₂)·u₀ + (z₂−z₀)·u₁ + (z₀−z₁)·u₂ = 0`; equivalently, at each coordinate the error value is an **affine** function of the challenge. `exists_vanishing_combination` gives the requested `λ`-form for `r + 1 ≥ 3` challenges.
- `global_support_bound` — double counting gives `|S|·M ≤ M·e + |S|` for the union `S` of the error supports over `M` successful challenges, i.e. `|S| ≤ M·e/(M−1)`; `card_globalErrorSupport_le` rounds this to `|S| ≤ e` when `M ≥ e + 2`.
- `correlatedAgreement_of_many_challenges` — the rigidity theorem: `M ≥ e + 2` successful challenges force one single set `S` of size `≥ n − e` on which the whole line agrees with codewords. `rigidity_rho_quarter` is the concrete rate-1/4 instance (`n = 2²⁰`, `k = 2¹⁸`, `δ = 1/4`).

Two corrections to the instruction were necessary and are documented (DISCREPANCIES O37–O38): the side condition is on the *error budget* (`3e < m+1`), not on the dimension, and the witness used makes it independent of `r`; and `r − 1 < M` is **not** enough for the rigidity corollary — `M ≥ e + 2` is, and the numerical check finds that every sampled instance with `M = e + 1` violates `|S| ≤ e`. A further strengthening: the three challenges need not be distinct.

**Target B — additive margin law** (`RequestProject/Root/CodingTheory/AdditiveMargin.lean`)

A pure counting model of two independent, domain-separated folds over `s` rounds (`falseAcceptProb`, with `card_rounds_space` justifying the denominator):

- `falseAcceptProb_eq` — `Pr[FA] = ((|B₁|/|F|)·(|B₂|/|F|))^s`;
- `additive_margin_law` — margins add: `Pr[FA] ≤ (1/|F|)^{Δ₁+Δ₂}`, and `additive_margin_law_rounds` gives `(1/|F|)^{(Δ₁+Δ₂)·s}`;
- `soundness_rho_half_two_folds` — the concrete rate-1/2 result: for `n = 2²⁰`, `k = 2¹⁹`, `e = 2¹⁶`, `|F| ≥ 2³²` and `s = 5` rounds of two domain-separated folds, `Pr[FA] ≤ 2^(−128)` (the proved value is `2^(−150)`). This is unconditional: the per-fold input is the already-proved bound `#bad ≤ e + 1`.

Recorded as O39: a per-fold density of exactly `1/|F|` is *not* available at `ρ = 1/2` (the honest density is `(e+1)/|F| ≤ 2^(−15)`), so the concrete theorem uses that density and `s = 5` rather than `s = 32`.

**Numerical checks.** The three requested scripts were written and run: `analysis/syndrome_vanishing_check.py` (identity holds everywhere in the strict-gap regime; explicit counterexamples once `k + 3e > n`), `analysis/syndrome_global_support_check.py` (counting bound, rounding, rigidity, and sharpness of the `M ≥ e + 2` threshold), `analysis/syndrome_additive_margin_check.py` (product formula against exact enumeration, 64 350 instances of the margin law, and the concrete rate-1/2 arithmetic in exact rationals). No counterexample was found to any formalised statement. These scripts are exploratory pre-verification; the verified claims are the Lean theorems.

**Documentation.** `RESULTS.md` gained section 34 (statements, mechanism, parameter table, script table) and `DISCREPANCIES.md` gained items O37–O39 recording the three deviations above honestly.


# Summary of changes for run f7ee8523-1896-4165-9863-0274049b4958
## What was done

### Part A — the discriminant path: the requested theorems are impossible, and this is now formally proved

The requested "final" theorems (`exists_t_with_disc_ne_zero`, `exists_nondegenerate_interpolation`, `epsMCAmax_le_johnson_disc_final`, four concrete 2⁻¹²⁸ thresholds) **cannot be stated truthfully**, because the non-degeneracy hypothesis they were meant to remove is *false*, not merely hard. Rather than assert them, the refutation was formalized in `RequestProject/Root/CodingTheory/DiscriminantDegeneracy.lean`:

- **Structure theorem** (`coeff_eq_zero_of_zeroLine`): for a line lying inside the code, writing an interpolant as `Q = Σ_j c_j(X,Z)·Y^j`, the multiplicity condition forces `(X−x)^{m−j} ∣ c_j` at every `x ∈ D`, so `c_j = 0` whenever `L ≤ (m−j)·n + k·j`.
- Consequently `Y² ∣ Q` (`X_sq_dvd_of_zeroLine`) and the discriminant vanishes identically (`discLine_eq_zero_of_zeroLine`), so non-degeneracy is false (`nondegeneracy_hypothesis_false`).
- **Perturbation cannot help** (`perturbation_does_not_help`): the interpolation conditions are linear and homogeneous, so any interpolation-preserving perturbation `Q₀ + t·M` stays in the same solution space, every member of which is degenerate. The requested non-vanishing lemma `exists_eval_ne_zero` *is* proved and available, but there is nothing for it to act on.
- The hypotheses of the previously conditional theorems are unsatisfiable throughout the Johnson schedule (`johnson_nondegeneracy_false`) and for each of the four concrete parameter sets (forced vanishing orders j₀ = 507, 512, 461, 385).
- **Honest unconditional replacement**: `exists_const_epsMCAmax_le_sq` gives exactly the requested shape `ε_mca ≤ C·n²/|F|`, with no side hypothesis, in the regime `2δ + √ρ < 1`.

Numerical audits `analysis/perturbation_check.py` and `analysis/threshold_discriminant_final_check.py` were run and agree with the formal result.

### Part B — the syndrome-space root (`RequestProject/Root/SyndromeSpace.lean`, new)

- **B1.** An **explicit** parity-check matrix `H i x = v_x · x^i`, `0 ≤ i < n − k`, with the GRS multipliers `v_x = (∏_{y∈D∖{x}}(x−y))⁻¹`. A correction to the instruction: the *plain* Vandermonde matrix is not a parity-check matrix of a Reed–Solomon code (the dual is a *generalised* RS code); the failure is exhibited numerically. Proved: the Lagrange coefficient identity `∑_{x∈D} f(x)·v_x = coeff_{n−1} f`, that `ker H` is **exactly** the code (`ker_rsSyndromeMatrix`), and `proximity_iff_syndrome_matrix`.
- **B2.** The rank margin `Δ = t − k` and all four legs of the trichotomy: `dim U_T = |T|` (codimension exactly Δ) for Δ ≥ 0; `U_T = ⊤` at Δ = 0 (premise carries no information); `U_T` proper at Δ ≥ 1; codimension ≥ 2, equivalently density `|F|^{−Δ} ≤ |F|^{−2}`, at Δ ≥ 2; plus the trapping mechanism `syndromeLine_eq_of_two_mem`. This rests on a new general lemma `finrank_map_of_disjoint_ker`. The capacity-regime Δ ≥ 2 rigidity claimed in the literature is *not* asserted — its published proof needs a side condition confining it to the unique-decoding regime.
- **B3.** `mca_reduces_to_ca_below_capacity`, proved unconditionally. The requested hypothesis `e < n − k` turned out to be unnecessary; it is retained (marked `_he`) only because it was requested, with a docstring note. The requested `C_capacity·n²/|F|` shape is not claimed, and the reason is documented.
- **B4.** `analysis/syndrome_trichotomy_check.py` written and run (plus the existing `analysis/syndrome_space_check.py`): exhaustive checks over 𝔽₅, 𝔽₇, 𝔽₁₁ of the kernel and rank of the GRS matrix, the failure of the plain Vandermonde control, the Lagrange identity, all four trichotomy legs for every support set, the trapping mechanism, and the two-sided vacuity at Δ = 0. All checks pass; no counterexample was found to anything subsequently formalized.

### Part C — documentation and verification

- `RESULTS.md`: new §33 (parity-check matrix, rank margin, MCA below capacity, numerical pre-verification) alongside the existing §32 on the discriminant refutation.
- `DISCREPANCIES.md`: new items O34 (Vandermonde vs GRS multipliers, and `↥D` vs `Fin n` indexing), O35 (B3 delivered in the strongest true form, unused hypothesis, requested shape not claimed), O36 (which legs of the trichotomy are provable and which are not).
- `RequestProject/Main.lean` imports the new module and prints `#print axioms` for all new theorems.

`lake build` completes successfully (8117 jobs); every `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`; there is no `sorry` or `admit` anywhere in the Lean sources (the only matches are the words inside docstrings). All work is committed and pushed.


# Summary of changes for run 8c54b602-6dd6-4d33-aaa9-ba5427f44947
Continued the Reed–Solomon mutual-correlated-agreement (MCA) work along the non-Hensel routes, adding a new module and completing the documentation that was still owed.

**New Lean module `RequestProject/Root/CodingTheory/CircuitIncidence.lean`** (all proofs complete, no `sorry`, only `propext`/`Classical.choice`/`Quot.sound`):

- `GrsCloseOn` — agreement with a *generalised* Reed–Solomon codeword `v·p`, plus interpolation (`grsCloseOn_of_card_le`) and uniqueness (`eq_of_grsCloseOn`).
- `grsCloseOn_insert_iff` — shortening the generalised code at one coordinate (dimension drops by one, multipliers pick up a factor `α − x`).
- `card_rejectingSets_ge` — **rejecting-test abundance**: if `w` is not a generalised codeword on `S`, then for every `k+1 ≤ a ≤ |S|` at least `C(|S|−1, a−1)` of the `a`-subsets of `S` already witness this. Proved from scratch by strong induction on `|S|`, combining the two cases with Pascal's rule.
- `not_isCloseOn_snd_of_witness` — the direction criterion: a witness set of a bad parameter always rejects the direction vector `f₁`.
- `card_badSet_le_circuit` — **circuit-incidence bound**: with `T = max(|D|−e, k+1)`, `#bad · C(T−1, a−1) ≤ C(|D|, a)` for every `k+1 ≤ a ≤ T`. This is *unconditional* — it needs no relation between the error budget and the unique-decoding or Johnson radius.
- `epsMCA_le_circuit`, `epsMCAmax_le_circuit` — the corresponding bounds on `ε_mca`.
- `card_badSet_le_choose`, `epsMCAmax_le_choose` — the clean unconditional corollary `#bad ≤ C(n, k+1)` and `ε_mca ≤ C(n, k+1)/|F|` at *every* error budget.
- `exists_isBad_knife_edge` — the knife-edge leg (`Δ = 1`) of the rank-margin trichotomy: at `e = n − (k+1)` unconditional rigidity fails, with an explicit line and witness set.
- `epsMCAmax_le_circuit_64_16_40` — a concrete instance strictly beyond the Johnson radius: for `n = 64`, `k = 16` (rate 1/4, Johnson radius 1/2) at `δ = 0.625`, `ε_mca ≤ 2³³/|F|`.

**Numerical pre-verification** (`analysis/syndrome_space_check.py`, `analysis/circuit_incidence_check.py`, `analysis/post_johnson_check.py`): exhaustive checks over small fields of the proximity↔syndrome equivalence, the trapped-line dichotomy, the abundance lemma (≈2.5 M instances) and the circuit inequality — no discrepancy, and the bound is tight on those instances; plus an evaluation of the proved bound across rates and budgets.

**Documentation.** `RESULTS.md` gained a new section 29 covering the syndrome-space lens, the strict-gap rigidity, the capacity barrier and the circuit-incidence bound, with a leg-by-leg table for the rank-margin trichotomy and a numerical table. `DISCREPANCIES.md` gained items O23–O28 recording honestly: the gap in the Okamoto claim of a "complete resolution to capacity" (its Δ≥2 theorem holds only in the unique-decoding regime); that Path 2 (resultant/discriminant) and Path 3 (interleaved stability) were not formalised; that of Path 4 the circuit-incidence part is formalised in full while the `O(K⁶)` bound is not, and that **no 2⁻¹²⁸ claim at K = 2¹⁸ is made anywhere in this repository**; and the counting hypothesis of the capacity barrier.

Everything builds (`lake build` clean), no `sorry`/`admit`, no new axioms, and all work is committed and pushed. New results are registered in the Properties table and marked proved.

# Summary of changes for run 614e0be8-8bb3-482a-9de5-99b3b1697472
## What was done

I continued the Johnson-regime MCA work package. Everything below builds in one `lake build` of the whole project, contains no `sorry`/`admit`, adds no axioms, and every new theorem is covered by a `#print axioms` line in `RequestProject/Main.lean` showing only `propext`, `Classical.choice`, `Quot.sound`.

### New Lean results

**`RequestProject/Root/CodingTheory/MultivariateInterpolation.lean`** — Guruswami–Sudan interpolation from scratch. Bivariate polynomials are modelled as `F[X][X]` (inner variable `X`, outer `Y`); weighted degree `GS.WdegLt k L Q` (`∀ j, deg(Q.coeff j) + k·j < L`) and multiplicity `GS.HasMultAt m Q α β` (via the translation `GS.shiftBiv`, equivalent to vanishing of all Hasse derivatives of order `< m`, hence correct in characteristic `p`). Proved: `(X−α)^m ∣ Q(X,p(X))` at a multiplicity-`m` zero, the degree bound on `Q(X,p(X))`, the factorisation step `(Y − p) ∣ Q`, the monomial count `L² ≤ 2k·#{(a,b) : a+kb < L}`, and the interpolation theorems `GS.exists_interpolating_of_card`, `GS.exists_interpolating`, `GS.exists_interpolating_of_johnson`.

**`ListDecodingGS.lean`** — the list-decoding half: `GS.gs_list_bound` (`k·#S < m·t` under `k·n·(m+1) < m·t²`) and `listSizeMax_le_gs` (`k·Λ(k,t) < m·t`). This is the list-size bound at the **full** Johnson radius, with the list size bounded independently of `n`.

**`MCAJohnsonGS.lean`** — feeding that into the MCA machinery: `epsMCAmax_le_gs`, the relative form `epsMCAmax_le_gs_relative` (`ε_mca ≤ n·C(ρ,δ,m)/|F|` when `2δ + (1+1/(2m))√ρ < 1`), the four concrete `2⁻¹²⁸` instances `threshold_rho_half/quarter/eighth/sixteenth` for `n = 2²⁰`, and `exists_const_epsMCAmax_le`.

**`CorrelatedAgreementRefined.lean`** (new mathematical contribution of this session) — a correlated-agreement theorem with **no list-size factor at all**: if `k + 3e ≤ n` and more than `2e+1` points of a line are `e`-close, a single pair of codewords works on `≥ n − e` positions (`correlatedAgreement_of_card_goodZ_gt_third`); consequently `#bad ≤ 2e+1` and `ε_mca ≤ (2e+1)/|F|` (`card_badSet_le_third`, `epsMCAmax_le_third`), with concrete instances `threshold_rho_half_third` (δ = 1/6, |F| ≥ 2¹⁴⁷) and `threshold_rho_quarter_third` (δ = 1/4, |F| ≥ 2¹⁴⁸). For ρ = 1/2 and ρ = 1/4 this beats the list-decoding route in both radius and constant; for ρ = 1/8, 1/16 the list-decoding route reaches a larger radius. The two regimes are incomparable and both are kept.

### Numerical work

`analysis/gs_dimension_check.py`, `analysis/mca_small_field_check.py` (now also brute-force-checking the new `#bad ≤ 2e+1` bound in and outside its regime; no counterexample found), `analysis/mca_constants_check.py` (the radii and field sizes used in the concrete theorems). All scripts run and pass.

### Honest scope, recorded in the documentation

- The **full Johnson radius** `δ < 1 − √ρ` for MCA is **not** proved. What is proved is `δ < max((1−ρ)/3, (1−√ρ)/2)`. The obstruction is not the list size (supplied here at the full Johnson radius) but the two-point extraction of correlated agreement; closing it needs the trivariate/discriminant/Hensel argument. Recorded as open item O20, and the identity `sup{δ : ε_mca ≤ 2⁻¹²⁸} = 1 − √ρ` as O21.
- The external repository named in the task was cloned and read, but it pins a **later Lean release** than this project, so its modules cannot be imported here; independently, its bad-event bound lives in a unique-decoding-type regime, so it offers no shortcut to the Johnson radius. Recorded as O19; the new files are self-contained.
- The requested hypothesis `2⁶⁴ ≤ |F|` for a `2⁻¹²⁸` error at `n = 2²⁰` is **unsatisfiable** (any bound of this shape is at least `n/|F| = 2⁻⁴⁴`); the theorems carry the exact required field sizes (2¹⁴⁷–2¹⁵³). Recorded as O22.

`RESULTS.md` gained a new section 28 with every theorem name and statement; `DISCREPANCIES.md` gained items O19–O22 plus a note on the modelling choices (why `F[X][X]` rather than `MvPolynomial (Fin 2) F`, and the integer form of the list-size bound). The Properties table was reconciled with the final sources.


# Summary of changes for run 5c648b8a-c3c9-438a-b9c8-8ef345ea79c1
## What I added

Two new modules, both `sorry`-free and building as part of the whole project (`lake build` is clean; the `#print axioms` audit in `RequestProject/Main.lean` now covers every new theorem and shows only `propext`, `Classical.choice`, `Quot.sound` — no axioms were added).

**1. `RequestProject/Root/CodingTheory/CorrelatedAgreement.lean` — Theorem CA.**

* `listSizeMax D k t` = `Λ(k,t)`, the largest number of Reed–Solomon codewords of degree `< k` agreeing with one and the same word on at least `t` positions (this is the `Λ(C,e)` of your write-up, for `t = |D| − e`), with `Λ ≥ 1`.
* `exists_line_pair`, `card_inter_polyAgreement_ge_of_pair`: two points `z₀ ≠ z` of the line and their local witnesses determine an explicit pair `q₀, q₁` of degree `< k` with `q₀ + z₀q₁ = p_{z₀}`, `q₀ + zq₁ = p_z`, agreeing with `f₀, f₁` on a common set of `≥ |D| − 2e` positions.
* `correlatedAgreement_of_card_goodZ_gt` (**Theorem CA**): if `2·e·Λ(k, |D| − 2e) + 1 < #{z : Δ(f₀ + z f₁, C) ≤ e}` then a single pair `q₀, q₁` of degree `< k` satisfies `f₀ = q₀` and `f₁ = q₁` on a common set of at least `|D| − e` positions. This carries **no** hypotheses on `k, e, |D|, |F|`. The proof fixes a good `z₀ ≠ 0`, maps every other good `z` to the codeword `Q₀ z` (which lands in a list-decoding list of `f₀` of radius `2e`, hence at most `Λ` values), and shows each fibre of that map has at most `2e` elements unless the common agreement set already reaches `|D| − e`.

**2. `RequestProject/Root/CodingTheory/MCAJohnson.lean` — the MCA bound.**

* `card_badSet_le_listSizeMax`: for `2e + k ≤ |D|`, `#bad(f₀,f₁) ≤ |D|·Λ`; hence `epsMCA_le_listSizeMax`, `epsMCAmax_le_listSizeMax`: **`ε_mca(C,e) ≤ |D|·Λ/|F|`** — the boxed inequality you asked for — and the protocol form `correlatedAgreement_of_prob_gt_johnson` (acceptance probability above `|D|·Λ/|F|` forces one common agreement set of size `≥ |D| − e` for the whole line).
* `listSizeMax_le_johnson` plugs in the already-proved `johnson_list_bound`, and `epsMCAmax_le_johnson` gives the fully explicit estimate `ε_mca ≤ |D|·( |D|t/(t² − |D|(k−1)) )/|F|`, `t = |D| − 2e`, under `2e + √(|D|(k−1)) < |D|`.
* `epsMCAmax_le_relative`: in relative parameters `ρ = (k−1)/|D|`, `δ = e/|D|`, if `2δ + √ρ < 1` then `ε_mca ≤ |D|·C(δ,ρ)/|F|` with `C(δ,ρ) = (1−2δ)/((1−2δ)² − ρ)` independent of `|D|`, so any target error (e.g. `2⁻¹²⁸`) is obtained by enlarging the field.

## Scope — stated honestly

The regime reached is `2δ + √ρ < 1`, i.e. `δ < (1 − √ρ)/2`: **half** the Johnson radius, and with `Λ` taken at radius `2e` rather than `e`. The qualitative row `#bad ≤ |D|·Λ` holds throughout `2e + k ≤ |D|`; the Johnson condition is only needed to make `Λ` explicit. The target threshold `δ = 1 − √ρ` is **not** proved, and neither is Theorem CA with the exact threshold `Λ(C,e) < |G|`. The obstruction is structural for the argument used: correlated agreement is extracted from two good points of the line, whose local witnesses only overlap in `|D| − 2e` positions, which is vacuous once `2e > |D| − k`; reaching `1 − √ρ` needs genuine list-decoding machinery (bivariate interpolation / soft-decision decoding) that is not available in the library and was not built here. Nothing in the repository asserts the full threshold: it is recorded as open items O16–O18 in `DISCREPANCIES.md`, with the new results and their limits documented in `RESULTS.md` §27.10–27.11 and `MCA_ROOT_WITNESSES.md` (Step 8). Also worth noting: the new row is incomparable with the previously proved unique-decoding row (`δ < (1 − ρ)/3`) — the new one is stronger for rates `ρ < 1/4`, the old one for higher rates.

All work is committed and pushed; `ARISTOTLE_SUMMARY.md` was left untouched.

# Summary of changes for run 3064088c-6be4-4325-b627-b66639a27cd4
Kontynuowałem warstwę teorii kodów `RequestProject/Root/CodingTheory/` i domknąłem ją dwoma nowymi modułami. Cały projekt buduje się w całości (`lake build`), bez `sorry`, a audyt `#print axioms` w `RequestProject/Main.lean` pokazuje dla każdego nowego twierdzenia wyłącznie `propext`, `Classical.choice`, `Quot.sound` (żadnych nowych aksjomatów).

Co było już gotowe (i zostało teraz uzupełnione o audyt i dokumentację): metryka Hamminga i kody liniowe (`Hamming.lean`), interpolacja Lagrange'a z jednoznacznością oraz Schwartz–Zippel wyrażony w warstwie probabilistycznej `Root/Prob.lean` (`PolynomialInterpolation.lean`), kod Reeda–Solomona z dokładną odległością minimalną `|D| − k + 1` (`ReedSolomon.lean`), test lokalny na losowych podzbiorach z prawdopodobieństwem akceptacji i proximity gap T1 (`LocalTests.lean`, `ProximityGapSubsets.lean`), proste afiniczne (`AffineSubspaces.lean`) i correlated agreement na prostej słów (`ProximityGapLines.lean`).

Nowe w tej sesji:

1. `MCA.lean` — mutual correlated agreement. Definicje `(S,δ)`-bliskości słowa i całej prostej (`IsCloseOn`, `LineCloseOn`), punktów złych (`IsBad`, `badSet`) oraz `ε_mca` dla prostej i jego maksimum po wszystkich prostych (`epsMCA`, `epsMCAmax`). Udowodnione: lemat L1 o domknięciu prostej (`line_closure`); implikacja „MCA ⇒ correlated agreement” (`correlatedAgreement_of_epsMCA_lt`); oraz — w reżimie jednoznacznego dekodowania `3e < |D| − k + 1` — wiersz tabeli MCA: co najwyżej `|D|` punktów prostej jest złych (`card_badSet_le`), stąd `ε_mca ≤ |D|/|F|` (`epsMCA_le`, `epsMCAmax_le`) i postać wynikowa: prawdopodobieństwo akceptacji większe niż `|D|/|F|` na prostej daje jeden wspólny zbiór zgodności o mocy `≥ |D| − e` dla całej prostej (`correlatedAgreement_of_prob_gt`). Dowód jest samodzielny: albo zbiór dobrych `γ` jest mały, albo dwa dobre punkty wymuszają wspólny zbiór `T`, a argument rozłączności i zliczania podnosi `|T|` do `|D| − e`; każdy zły punkt daje wtedy odrębną pozycję poza `T`.

2. `Johnson.lean` — ograniczenie rozmiaru listy typu Johnsona metodą drugiego momentu: dla listy słów kodowych zgadzających się z `f` na co najmniej `t` pozycjach zachodzi `L·(t² − n(k−1)) ≤ n·t` (`johnson_list_bound`, `n = |D|`, bez żadnego założenia o `t`), stąd `L ≤ n·t/(t² − n(k−1))` gdy `n(k−1) < t²` (`card_decodingList_le`), a w reżimie `n + (k−1) < 2t` lista ma co najwyżej jeden element (`card_decodingList_le_one`). Składniki: `card_agreementSet_le_of_ne`, momenty `sum_passCount`, `sum_passCount_sq`, `sum_passCount_sq_le` i nierówność Cauchy'ego–Schwarza. To nie jest twierdzenie Johnsona z najostrzejszą stałą, ale jawne, udowodnione ograniczenie poza promieniem jednoznacznego dekodowania.

Weryfikacja blueprintu (uczciwie odnotowana, nie „dodana jako prawda”): powstał dokument `MCA_ROOT_WITNESSES.md` mapujący każdy punkt blueprintu na świadka w Lean albo na pozycję otwartą. Nie zostały udowodnione i są zapisane jako otwarte: wiersze tabeli MCA przy promieniu Johnsona (O16) — dołączony szkic dowodu nie domyka się w podanej postaci, bo zakłada tę własność domknięcia prostej, którą ma dopiero uzyskać — oraz próg asymptotyczny `δ* = 1 − √ρ` (O17). Łańcuch `ε_pg ≤ ε_ca ≤ ε_mca` nie jest formułowany jako nierówność trzech osobno definiowanych wielkości; udowodniona jest niosąca treść implikacja. Nadal otwarte pozostaje też T2 (soundness testu na prostej, O14).

Zaktualizowałem `RESULTS.md` (nowe podrozdziały 27.7–27.9) i `DISCREPANCIES.md` (nowe pozycje otwarte O16, O17 oraz notatki o rozbieżnościach blueprintu), a tabela właściwości zawiera zarejestrowane definicje i twierdzenia tej warstwy z aktualnymi statusami. Pliku `ARISTOTLE_SUMMARY.md` nie zmieniałem.

# Summary of changes for run 7595973c-efd2-4c25-a32c-53906b4c104b
Zweryfikowałem dostarczony materiał i dodałem cały brakujący „Rdzeń” jako nową warstwę `RequestProject/Root/`. Cały projekt buduje się czysto (`lake build`), nie zawiera `sorry`/`admit` i nie dodano żadnych aksjomatów — audyt `#print axioms` w `RequestProject/Main.lean` obejmuje teraz również wszystkie nowe twierdzenia i pokazuje wyłącznie `propext`, `Classical.choice`, `Quot.sound` (część twierdzeń modalnych nie zależy od żadnych aksjomatów).

**Weryfikacja szablonów ze zlecenia (wynik: nie kompilują się w podanej postaci).** Zapisałem to jawnie w `DISCREPANCIES.md` (sekcja „Notes on the template code…”) i w nagłówkach plików:
- klasa algebr nie może nazywać się `Algebra` (nazwa zajęta) — jest `Root.SigAlgebra`;
- proponowane `free_alg_fold_unique` jest **fałszywe**: funkcja z wolnej algebry nie jest wyznaczona przez wartości na zmiennych, jeśli nie wymagać, by była homomorfizmem — udowodniona wersja dodaje ten warunek;
- `Prob.bind` na miarach jest miarą probabilistyczną tylko dla mierzalnego jądra, więc bezwarunkowa instancja `Monad` nie istnieje;
- `box_distrib`/`box_trans`/`lob` nie zostały dodane jako aksjomaty (projekt nie dodaje aksjomatów) — są hipotezami struktury `Derivability` oraz udowodnionymi twierdzeniami.

**Rdzeń A — algebra uniwersalna (`Root/Algebra.lean`).** Sygnatury z arnościami będącymi typami, termy, algebry, homomorfizmy, ewaluacja termów i lemat `eval_cong`; uniwersalna własność algebry termów; kongruencja generowana przez aksjomaty, wolna algebra, zasada indukcji, dowód, że wolna algebra jest modelem swoich aksjomatów (dla aksjomatów zamkniętych na podstawienia) oraz **uniwersalna własność wolnej algebry**; kongruencje i algebry ilorazowe z uniwersalną własnością; domknięcie klas równościowych na podalgebry, ilorazy i produkty (HSP).

**Rdzeń A — instancje (`Root/Instances.lean`).** Sygnatury i aksjomaty pierścienia, pierścienia przemiennego i modułu (w postaci zamkniętej na podstawienia) wraz z dowodami, że każdy pierścień/moduł jest modelem; most do biblioteki: `IsSigHom` między pierścieniami ⟺ homomorfizm pierścieni (obie strony, z konstrukcją `RingHom`); wolny pierścień na zbiorze generatorów; R1CS jako pary termów pierścieniowych (spełnialność ⟺ równość wartości termów) plus zachowanie spełnialności przy zmianie bazy; bramki Plonk jako pojedyncze równania; ograniczenia przejścia AIR na kolejnych wierszach śladu wraz z funktorialnością względem homomorfizmu pierścieni; sygnatura słowa maszynowego na `BitVec n`. Dodatkowo udowodnione ograniczenie tej metody: **ciała nie są klasą równościową** (produkt ciał nie musi być ciałem).

**Integracja istniejących modułów (`Root/Bridge.lean`).** Brakujący most `BilinAlg → GenAlg` z zachowaniem poprawności w obie strony i przeniesieniem dolnego ograniczenia Fiducciego–Zalcsteina na model współrzędny; ideał pierścienia przemiennego jako kongruencja sygnatury, kanoniczny izomorfizm ilorazu uniwersalno-algebraicznego z `R ⧸ I` (będący homomorfizmem algebr sygnatury) oraz uniwersalna własność `R ⧸ I` jako instancja własności ogólnej — dokładnie scenariusz opisany w zleceniu.

**Rdzeń B — probabilistyka (`Root/Prob.lean`).** Miary probabilistyczne z `pure`/`bind` (jądro mierzalne) i trzema prawami monady; odległość TV jako supremum po zbiorach mierzalnych z nieujemnością, symetrią, ograniczeniem przez 1 i nierównością trójkąta oraz nierównością przetwarzania danych dla post-processingu deterministycznego; warstwa skończona (`FinProb`) z prawami monady, **pełną nierównością przetwarzania danych dla dowolnych jąder Markowa** (`tv_bind_le`) i nieujemnością dywergencji KL (nierówność Gibbsa).

**Rdzeń C — logika dowodliwości (`Root/Modal.lean`).** Składnia i semantyka Kripkego formuł modalnych; poprawność `K` na wszystkich ramach, `4` na ramach przechodnich i **aksjomatu Löba na ramach przechodnich o odwrotnie dobrze ufundowanej relacji** (indukcja dobrze ufundowana), wraz z kontrmodelem pokazującym, że tego założenia nie można pominąć; warunki wyprowadzalności Hilberta–Bernaysa–Löba jako struktura, **reguła Löba i twierdzenie Löba** z nich wyprowadzone przy hipotezie punktu stałego Gödla, oraz wniosek, że fałszywe zdanie o operatorze spełniającym `Box P → P` punktu stałego nie ma (co pokazuje, że hipoteza nie jest sprzeczna ani pusta).

Dokumentacja: nowa sekcja 25 w `RESULTS.md` (tabele nazw twierdzeń dla każdego rdzenia) oraz wiersze P38–P43 i notatka o szablonach w `DISCREPANCIES.md`. Tabela Properties zawiera nowe pozycje oznaczone jako udowodnione na podstawie czystego, wolnego od `sorry` builda. Wszystko jest zacommitowane i wypchnięte. Bez zmian pozostają dotychczasowe zastrzeżenia projektu: nie wykonano żadnych pomiarów wydajności i nie formułuję porównań z istniejącymi implementacjami.

# Summary of changes for run 0a38ce66-f1cd-4a51-aa20-813a8a330893
## WSAD A — wykonany, zbudowany, wypchnięty

Cały projekt buduje się czysto (`lake build`), nie zawiera `sorry`/`admit`, nie dodano żadnych aksjomatów: audyt `#print axioms` w `RequestProject/Main.lean` obejmuje teraz 137 twierdzeń i dla każdego pokazuje wyłącznie `propext`, `Classical.choice`, `Quot.sound`.

**1. Abstrakcyjny lemat o substytucji (wzmocniony `RequestProject/Substitution.lean`)**
- `FFT.Bilinear.substitution_step` — dla **dowolnej** skończenie wymiarowej unitalnej algebry **łącznej** `R` (bez założenia przemienności) i dowolnego surjektywnego homomorfizmu algebr `pi : R →ₐ[F] S` (równoważnie: `S = R ⧸ I` dla dwustronnego ideału `I`) o niezerowym jądrze: każdy algorytm biliniowy długości `k` dla mnożenia w `R` zawiera algorytm długości `k − 1` dla mnożenia w `S`. Schemat dowodu jest identyczny z dotychczasowym (jądro formy liniowej, spadek wymiaru).
- `FFT.Bilinear.exists_left_ne_of_computes` — każdy niezerowy element jest „widziany” przez którąś formę lewą (bierzemy `x = 1`); to ten krok dostarcza formę liniową do cięcia.
- `FFT.Bilinear.substitution_step_ideal` (w `RadicalLift.lean`) — ta sama teza w sformułowaniu ideałowym: `I ≠ 0` ⇒ algorytm długości `k − 1` dla `A ⧸ I`.
- **Odstępstwo od treści zlecenia, zapisane jawnie w dokumentacji:** krok substytucji indeksuje forma liniowa niezerowa **na dzielonym ideale**, a nie forma z `λ(1) ≠ 0`; samo `λ(1) ≠ 0` certyfikuje tylko trywialny iloraz `A/A = 0`. Forma jest w dowodzie konstruowana z niezerowego elementu ideału.

**2. Spadek wymiaru i liczby `t`**
- `FFT.Bilinear.finrank_quotient_lt` — `dim (A ⧸ I) < dim A` dla `I ≠ 0` (czyli `dim(A/I) ≤ dim A − 1`).
- `FFT.Bilinear.numMaxIdeals_quotient_le` — `t(A ⧸ I) ≤ t(A)`.
- `FFT.Bilinear.bilinRank_quotient_lt` — `R(A ⧸ I) < R(A)`.
- **Punkt 2 zlecenia w wersji „`t(A/I) ≥ t(A) − 1`” jest fałszywy** i to jest maszynowo zweryfikowane: `FFT.Bilinear.numMaxIdeals_quotient_not_ge` podaje kontrprzykład `A = 𝔽₂ × 𝔽₂ × 𝔽₂`, `I = ker(pierwszy rzut)` — `t(A) = 3`, ale `t(A ⧸ I) = 1`. Zamiast tego udowodniono dwie prawdziwe nierówności wymienione wyżej. Nie usunąłem żadnej treści zlecenia — nieprawdziwe stwierdzenie jest opisane w `RESULTS.md` i w `DISCREPANCIES.md` (wiersz P37).

**3. Cztery lematy strukturalne (nowy plik `RequestProject/RadicalLift.lean`, ok. 340 linii)**
- (a) `radical_eq_sInf_maximal` — `rad A` to przecięcie wszystkich ideałów maksymalnych (dla algebry przemiennej: maksymalnych dwustronnych); dodatkowo `isNilpotent_radical`, `radical_isNilpotent_mem`.
- (b) `isSemisimpleRing_quotient_radical` — `A ⧸ rad A` jest półprosta.
- (c) `exists_isIdempotentElem_lift` — idempotenty `A ⧸ rad A` podnoszą się do `A` (w pierścieniu przemiennym każdy idempotent jest centralny, więc jest to żądane podniesienie idempotentów centralnych); dodatkowo `exists_completeOrthogonalIdempotents_lift` — podnosi się całe zupełne ortogonalne układy idempotentów, czyli rozkład `A ⧸ rad A ≅ ∏ Bᵢ` pochodzi z rozkładu samego `A`. Zgodnie z zaleceniem nie dowodziłem twierdzenia Artina–Wedderburna.
- (d) `numMaxIdeals_quotient_radical` — `t(A) = t(A ⧸ rad A)`, przez jawną bijekcję `maximalSpectrumQuotientRadicalEquiv`; wraz z `numMaxIdeals_field` daje „`t(A)` = liczba prostych (tu: ciałowych) czynników `A ⧸ rad A`”.
- Zakres: lematy strukturalne są sformułowane dla przemiennych algebr skończenie wymiarowych (klasa całego projektu); sam krok substytucji — dla dowolnych algebr łącznych.

**4. Przypadek równości**
- `FFT.Bilinear.minimalRank_prod_iff_tight` — precyzyjna, udowodniona postać zdania „A ma rangę minimalną ⟺ każdy krok substytucji jest ciasny i każdy czynnik lokalny ma rangę minimalną”: przy założeniu dolnego ograniczenia Aldera–Strassena dla iloczynu oraz dwóch ograniczeń „obierania” (peeling) czynnika, `A × B` ma rangę minimalną wtedy i tylko wtedy, gdy oba czynniki ją mają, i wówczas krok CRT jest ciasny: `R(A × B) = R(A) + R(B)`.
- Ważna obserwacja zapisana w dokumentacji: **założeń o obieraniu nie da się pominąć** — z samego Aldera–Strassena dla czynników i z `R(A × B) ≤ R(A) + R(B)` implikacja „w prawo” nie wynika. Te założenia dostarczy WSAD B dla klasy algebr projektu (`F[C_n]`, `F[x]/(xⁿ−1)` i ich czynniki).

**Dokumentacja:** nowa sekcja 24 i 24.1 w `RESULTS.md` (pełne tabele nazw twierdzeń, zakres i zastrzeżenia), nowe wiersze P35, P36, P37 w `DISCREPANCIES.md`. Tabela Properties zawiera nowe pozycje oznaczone jako udowodnione na podstawie czystego, wolnego od `sorry` builda. Wszystko zacommitowane i wypchnięte.

**Zweryfikowany plan na WSAD B (do wykonania po Twojej komendzie).** Sprawdziłem, co w repozytorium już jest, i co realnie da się domknąć:
- definicja `MinimalRank` (`R(A) + t(A) = 2·dim A`) oraz kierunek „w lewo” dla algebr półprostych już istnieją (`MinimalRank.lean`, `AlgebraSplit.lean`: `split_algebra_lower_bound` jest bezwarunkowe, `reduced_minimalRank` domyka przypadek zredukowany nad ciałem skończonym); brakuje wersji `t(∏ Kᵢ) = |ι|` dla iloczynów po typie `Pi` i to jest pierwszy krok B;
- kierunek odwrotny („ranga minimalna ⇒ rozkład na czynniki lokalne o randze minimalnej”) planuję przez lemat obierania `R(C × K) ≥ R(C) + 2·dim K − 1` dla `K` będącego ciałem (bezpośrednio z istniejącego `substitution_bound`, z rzutem na `C` i multiplikatywnym rzutem na dziedzinę `K`), a następnie indukcję po liczbie czynników z przenoszeniem wzdłuż izomorfizmów algebr; to dokładnie dostarcza założenia `hpeel` z `minimalRank_prod_iff_tight`;
- ograniczenie zakresu zgodnie ze zleceniem: tylko klasa `F[C_n]`, `F[x]/(xⁿ−1)`, ich czynniki oraz skończone iloczyny/ilorazy — bez klasyfikacji nad dowolnym ciałem i bez przypadku nieprzemiennego.


# Summary of changes for run e719deb7-2084-4ad6-a267-60fa977373de
Zweryfikowałem i dodałem do projektu główną część zgłoszonego pakietu — ogólny, rekurencyjny algorytm Toom–Cooka z dowolnymi całkowitymi punktami ewaluacji — jako w pełni sprawdzony maszynowo moduł `RequestProject/ToomCook.lean`. Cały projekt buduje się czysto (`lake build`), bez `sorry`/`admit` i bez dodanych aksjomatów; audyt `#print axioms` w `RequestProject/Main.lean` pokazuje dla wszystkich nowych twierdzeń wyłącznie `propext`, `Classical.choice`, `Quot.sound`.

**Co zostało udowodnione (nowe):**

1. **Algorytm** `FFT.ToomCook.toomk` — podział operandów na `KX` i `KY` kawałków w bazie `BASE^s`, odczyt kawałków jako współczynników wielomianów, ewaluacja w `KX+KY−1` punktach, **rekurencyjne** mnożenia skalarne, interpolacja Lagrange'a (nad `ℚ`) i złożenie przez ewaluację w promieniu podziału; poniżej progu — mnożenie bezpośrednie. Wejścia użytkowe: `toomkTop` (wartość w `ℚ`) i `toomkZ` (wartość w `ℤ`).

2. **Jawny próg θ niezależny od operandów** — `FFT.ToomCook.tk_THETA BASE KX KY POINTS` (typ nie zawiera `x`, `y`), równy `2c+4`, gdzie `c = log_BASE(k_max · V^{k_max}) + 1`, `V = 1 + Σ|v_i|`, oraz **lemat o kontrakcji rozmiaru** `FFT.ToomCook.tk_contraction`: powyżej θ każdy podproblem ma ściśle mniejszy rozmiar, niezależnie od operandów. Dzięki temu rekurencja jest dobrze ufundowana z konstrukcji (definicja jest totalna — terminacja nie jest założeniem).

3. **Poprawność** w dokładnie żądanej postaci: `FFT.ToomCook.toomk_correctness` (`BASE > 1`, `1 < KX ∧ 1 < KY`, `POINTS : Vector ℤ (KX+KY−1)`, `Function.Injective POINTS.get` ⟹ wynik `= x·y`), wersja całkowitoliczbowa `toomkZ_correctness`, oraz wersja z parametrem rozmiaru `toomk_eq` (niezmiennik `|x|,|y| < BASE^n`). Elementy pomocnicze też są dowiedzione: dokładność podziału na kawałki, oszacowania kawałków i wzrostu przy ewaluacji Hornera, ograniczenie stopnia iloczynu wielomianów kawałków przez liczbę punktów.

4. **Instancje konkretne**: klasyczny Toom-3 z punktami `⟨0,1,−1,2,−2⟩` (`toom3_correctness`) i przypadek niezbalansowany `k_x = 3, k_y = 2` z punktami `⟨0,1,−1,2⟩` (`toom32_correctness`) — pokazują, że twierdzenie obejmuje również `k_x ≠ k_y`.

Sprawdziłem też stwierdzenie o luce: w używanej wersji biblioteki matematycznej nie ma ani Toom–Cooka z uogólnionymi punktami całkowitymi, ani pojęcia partition rank. Warto odnotować relację do wcześniejszej części projektu: jednopoziomowa ewaluacja/interpolacja przy różnych punktach (także nad M31) i jej optymalność w modelu biliniowym były już udowodnione (`PolyMul.lean`, `ConvExact.lean`); nowy moduł dokłada brakującą warstwę rekurencyjną i terminację.

**Czego nie dodałem jako udowodnione:** dodatku o partition rank (`R_{d−2,1,1}(f)/((d+1)2^d(d−1)) ≤ L(f)`). Nie udało mi się go zweryfikować w tym środowisku (nie mam dostępu do wskazanych źródeł, a formalizacja wymagałaby zbudowania od zera teorii partition rank dla `d`-tensorów i dolnych granic w modelu prostoliniowym). Zapisałem go jawnie jako pozycję otwartą i niezweryfikowaną (O13 w `DISCREPANCIES.md`) — nic w repozytorium tej nierówności nie twierdzi. Podobnie nie weryfikowałem samych odnośników bibliograficznych podanych w pakiecie.

Dokumentacja: nowa sekcja 22 w `RESULTS.md` (opis modułu, tabela wyników, jasne zastrzeżenia: brak jakichkolwiek pomiarów wydajności, interpolacja w arytmetyce wymiernej, θ jest progiem wystarczającym, nie najmniejszym) oraz wiersz P33 i pozycja O13 w `DISCREPANCIES.md`. Tabela Properties zawiera nowe deklaracje, twierdzenia oznaczone jako udowodnione na podstawie czystego, wolnego od `sorry` builda. Wszystko jest zacommitowane i wypchnięte.

# Summary of changes for run 0b357630-1f09-49f8-b3de-98ff611fb5f3
## Faza tania (przed Lean)

Zgodnie z poleceniem najpierw przeprowadziłem szybkie badania i weryfikacje, a dopiero potem dowody. Wszystko jest udokumentowane w nowym pliku `BADANIA.md`, z odtwarzalnymi skryptami `analysis/tensor_rank.py` i `analysis/fz_meta.py`.

1. **Sprawdzenie stanu wiedzy** (arXiv, Semantic Scholar, przeszukanie źródeł biblioteki matematycznej): ograniczenie `2n − t` dla algebr jest klasyczne i rozwiązane (Winograd 1977, Alder–Strassen 1981); `Ω(n log n)` dla FFT w modelu obwodów liniowych pozostaje otwarte od ok. 40 lat (znane wyniki tylko w modelach ograniczonych); **nie znalazłem żadnej maszynowej formalizacji nietrywialnego dolnego ograniczenia złożoności biliniowej** — to jest realna luka.
2. **Dokładne rangi tensorowe** małych algebr nad `F_2`, `F_3`, `F_5` (wyczerpujące przeszukiwanie): 7 przypadków, wszystkie zgodne z `2n − t`. Ten eksperyment wymusił dodanie założenia o liczności ciała bazowego do twierdzenia o wartości dokładnej — bez niego byłoby ono fałszywe (`𝔽_8/𝔽_2` ma rangę 6, nie 5).
3. **Dokładne tożsamości tensorowe** (nie próbkowanie losowe) dla algorytmów górnych: Toom mod `Φ₅` (7 iloczynów), długość 5 (8), długość 6 (6), długość 30 przez Agarwala–Cooleya (48).
4. **Symulacja dowodu** Fiducciego–Zalcsteina na 200 losowych algorytmach — zero naruszeń; oraz próby falsyfikacji (poszukiwanie krótszych algorytmów) — bez wyniku.

## Trzy ścieżki i wybór

A) maszynowo zweryfikowana teoria dolnych ograniczeń złożoności biliniowej; B) automatyczne rangi nad małymi ciałami z certyfikatem (odłożone: mała wartość podstawowa, temat już automatyzowany w literaturze); C) `Ω(n log n)` (NO-GO: problem otwarty, brak poszlak). **Wybrałem A.**

## Wyniki formalne (wszystko buduje się czysto, bez `sorry`, bez dodanych aksjomatów)

**`RequestProject/AlgebraRank.lean`** — bezwspółrzędny model algorytmu biliniowego (`GenAlg`) oraz:
* `GenAlg.fiducciaZalcstein` — jeśli `x ↦ φ u x` jest injektywne dla każdego `u ≠ 0`, to algorytm wymaga `≥ dim U + dim V − 1` mnożeń (pierwsze w projekcie ograniczenie inne niż zliczanie wymiarów);
* `domain_bilinear_lower_bound` — mnożenie w `d`-wymiarowej algebrze bez dzielników zera wymaga `≥ 2d − 1`;
* `powerBasisAlg` + `adjoinRoot_bilinear_upper` — algorytm ewaluacyjno-interpolacyjny osiągający `2d − 1`;
* `ext_bilinear_complexity` — **wartość dokładna `2d − 1`** dla rozszerzenia ciała z bazą potęgową i `2d − 1` punktami w ciele bazowym;
* `M31sq_bilinear_complexity` — **`𝔽_{p²}` nad M31: dokładnie 3** (trzymnożeniowe jądro „zespolone”/Karatsuby jest optymalne — dwóch mnożeń nie da się osiągnąć);
* `M31quartic_bilinear_complexity` — **`𝔽_{p⁴}` nad M31: dokładnie 7**.

**`RequestProject/Conv5.lean`** — `ConvAlg.computes_of_tensor` sprowadza poprawność algorytmu splotowego do skończonej tożsamości tensorowej (rozstrzyganej rachunkiem jądra), a na tym:
* `exists_conv5_M31_eight` — **splot cykliczny długości 5 nad M31 w 8 iloczynach** (cel Winograda `2·5 − t(5)`);
* `cyclicConv30_M31_48` — **długość 30 w 48 iloczynach** (poprzednio sformalizowane 54), przy dolnym ograniczeniu 30.

Dokumentację projektu uzupełniłem: `RESULTS.md` (§17–18), `DISCREPANCIES.md` (nowe wiersze P27, P28 i aktualizacja pozycji otwartej O5), `BADANIA.md` (§5 z bilansem).

## Co pozostaje otwarte

Dolne ograniczenie Aldera–Strassena `R(A) ≥ 2·dim A − t(A)` dla algebr przemiennych z `t` ideałami maksymalnymi — jedyny brakujący element, by `c(5) = 8` i `c(30) = 48` stały się wartościami dokładnymi, a nie tylko górnymi granicami (sformalizowany jest przypadek `t = 1`). W `BADANIA.md` §4–5 pokazuję, dlaczego naiwne uogólnienie argumentu FZ daje dla `t = 2` tylko `2n − 3`.

Zastrzeżenia bez zmian: wszystkie stwierdzenia o kosztach dotyczą jawnie zdefiniowanego modelu biliniowego (mnożenia przez stałe i dodawania są darmowe); kontrakty w `verus/m31_fft.rs` pozostają niesprawdzone maszynowo (brak toolchainu); nie wykonano żadnych benchmarków, więc nie formułuję porównań wydajności z istniejącymi bibliotekami.


# Summary of changes for run 78b8e36f-b8f5-4bb9-a382-31d2754c42df
Wykonałem szybki triage badawczy (numerycznie w Pythonie + tanie sprawdzenia jądrem Lean) i zapisałem go w projekcie jako `TRIAGE.md`, ze skryptami odtwarzającymi wszystkie liczby: `analysis/triage_numerics.py` i `analysis/triage_costs.py`. Cały projekt nadal buduje się czysto, bez `sorry` i bez dodanych aksjomatów.

Najważniejsze ustalenia (liczby — obliczone; dowody — tylko tam, gdzie napisano wprost):

1. Struktura przesądza o możliwościach: `p−1 = 2·3²·7·11·31·151·331`, więc w ciele bazowym nie ma żadnego radix-2 NTT (największa gładka długość to 42966). Dla `n = 2^20` pozostają grupa okręgu (już udowodniona w projekcie) albo `F_{p²}`.
2. Nowy, maszynowo sprawdzony moduł `RequestProject/CyclotomicCosets.lean`: liczby p-cyklotomicznych warstw `t(5)=2`, `t(6)=6`, `t(30)=12`, `t(31)=31` (`decide +kernel`) i wynikający z nich cel Winograda `2·30 − t(30) = 48`.
3. Numerycznie (sprawdzone na losowych danych nad M31, nie udowodnione): jawny algorytm długości 5 na 8 iloczynów oraz tensor `6 ⊗ 5` dający splot cykliczny długości 30 na **48** iloczynach — lepiej niż sformalizowane dotąd 54 i dokładnie na granicy Winograda. To wskazuje `c(30) = 48` jako najbardziej opłacalny cel dowodowy.
4. Skala zysków przy `n = 2^20` w modelu kosztów projektu: ciało bazowe/okrąg vs `F_{p²}` to ~3× w mnożeniach i 2× w ruchu pamięci; split-radix to dodatkowe ~32 %. Priorytety inżynierskie ustawiłem według tych liczb.
5. Obalona ilościowo hipoteza „ukrytych symetrii Mersenne'a” przy rozmiarach `2^k`: `|⟨2⟩| = 31`, a wśród twiddle'i circle FFT rzędu `2^m` (m = 8, 12, 16, 18) w `⟨2⟩` leżą dokładnie 3 — mechanizm darmowych rotacji działa tylko dla długości dzielących 31 i nie skaluje się.
6. Rader długości 31 nad M31 jest matematycznie ciekawy, ale inżyniersko gorszy od istniejącego jądra bezpośredniego (0 mnożeń ogólnych, ~930 rotacji/dodawań) — wersja tensorowa to 48 mnożeń plus ~990 dodawań i ~770 mnożeń przez stałe.

`TRIAGE.md` zawiera tabelę decyzyjną GO/NO-GO z kryteriami przerwania oraz scenariusze: realistyczny (domknięcie `c(30) ≤ 48`, split-radix na okręgu, iteracyjny FFT in-place z niezmiennikami, kontrakty Verus) i optymistyczny (pełne twierdzenie Winograda `2n − t(n)`, dolne ograniczenia w modelu prostoliniowym, optymalność Karatsuby). Jako NO-GO odrzucam: K-teorię/topologię poza opisem wyznacznikowym (brak niezmiennika monotonicznego względem długości programu — uzasadnienie w §5), `Ω(n log n)` (otwarte w literaturze) i hipotezę sub-logarytmiczną (brak jakichkolwiek poszlak numerycznych).

`DISCREPANCIES.md` uzupełniłem o wiersz P26 (nowe fakty udowodnione) oraz o aktualizacje pozycji otwartych O5 i O12, wyraźnie oznaczając, co jest numeryką, a co dowodem. Zgodnie z dotychczasową zasadą projektu nie wykonano żadnych benchmarków i nie formułuję porównań wydajności z istniejącymi bibliotekami. Wszystko jest zacommitowane i wypchnięte.

# Summary of changes for run 7da65c8b-695e-423d-abf9-70b0c52777f2
Kontynuowałem projekt zgodnie z planem, dodając trzy nowe, w pełni udowodnione moduły (bez `sorry`, bez dodanych aksjomatów — audyt `#print axioms` w `RequestProject/Main.lean` pokazuje wyłącznie `propext`, `Classical.choice`, `Quot.sound`). Cały projekt buduje się czysto (`lake build`).

**1. `RequestProject/GroupAlgebraDFT.lean` — DFT jako izomorfizm algebr i sformułowanie funktorialne (luka z kroku 2 planu).**
- `FFT.zchar`, `FFT.sum_zchar` — charaktery `ℤ/n` i ich ortogonalność;
- `FFT.dftAlgHom` — DFT jako morfizm `F`-algebr `F[C_n] →ₐ (ℤ/n → F)`, z jawną transformatą odwrotną i dowodami obu złożeń;
- `FFT.dftAlgEquiv` — **`F[C_n] ≃ₐ[F] (ℤ/n → F)`** dla `ζ` pierwotnego rzędu `n` i odwracalnego `n`; stąd twierdzenie o splocie w postaci algebraicznej (`FFT.dftAlgEquiv_mul`) oraz półprostość `F[C_n]` (`FFT.isSemisimpleRing_monoidAlgebra`, rozszczepiona postać twierdzenia Maschkego);
- `FFT.repEquivPi` — **równoważność kategorii `Rep F C_n ≌ ModuleCat (ℤ/n → F)`**: DFT diagonalizuje każdą reprezentację `C_n`, naturalnie względem reprezentacji, a nie tylko regularną;
- `FFT.M31.dftAlgEquiv31`, `FFT.M31.repEquivPi31` — wersje nad `M31` dla długości 31 z `ζ = 2` (wszystkie twiddle to rotacje bitowe).

**2. `RequestProject/IsotypicDecomposition.lean` — rozkład izotypowy, konkretna postać tego samego faktu.**
Dla `T` z `T^n = 1`, `n` odwracalnego i `ζ` pierwotnego: `FFT.isoSum_eigen` (`T∘S_j = ζ^j S_j`), `FFT.sum_isoSum` (`∑_j S_j = n`), `FFT.cyclic_eigenspace_isInternal` (**`V = ⨁_{j<n} ker(T − ζ^j)`** jako wewnętrzna suma prosta), `FFT.mapsTo_eigenspace_of_comm` (naturalność: splatacze przenoszą podprzestrzenie własne), oraz `FFT.M31.cyclic31_eigenspace_isInternal` nad `M31` przy `n = 31`, `ζ = 2`.

**3. `RequestProject/AgarwalCooley.lean` — submultiplikatywność złożoności biliniowej splotu.**
Model biliniowy przeniesiony na dowolną skończoną grupę (`ConvAlg`, `gconv`), z: dolnym ograniczeniem `≥ |G|` (`ConvAlg.card_le_of_computes`), darmowym przeetykietowaniem (`ConvAlg.transport_computes`), **iloczynem tensorowym algorytmów** (`tensor_computes`: `k₁` i `k₂` mnożeń dają `k₁·k₂` dla `G × H`) i wnioskiem **`c(mn) ≤ c(m)·c(n)` dla względnie pierwszych `m, n`** (`agarwalCooley`). Konsekwencja liczbowa nad `M31`: splot cykliczny długości 30 (ten z redukcji Radera dla DFT długości 31) ma algorytm o **54** mnożeniach ogólnych (`30 = 6·5`: długość 6 to 6 mnożeń dzięki pierwotnemu pierwiastkowi 6-tego stopnia, długość 5 to 9 mnożeń metodą Tooma–Cooka), co poprawia wcześniej udowodnione 59; dolne ograniczenie 30 pozostaje (`cyclicConv30_M31_agarwal_cooley`). Dokładna wartość nadal nieustalona: `30 ≤ c ≤ 54`.

`RESULTS.md` (nowe sekcje 14–16) i `DISCREPANCIES.md` (nowe wiersze P25e, P25f, P25g oraz zaktualizowane pozycje otwarte O5, O9) zostały uzupełnione; tabela Properties odzwierciedla nowe wyniki (wszystkie oznaczone jako udowodnione na podstawie czystego, wolnego od `sorry` builda).

Niezmienione zastrzeżenia, powtórzone dla ścisłości: wszystkie stwierdzenia o kosztach są względne wobec jawnie zdefiniowanych modeli (biliniowy, prostoliniowy, liczba operacji); `verus/m31_fft.rs` pozostaje niesprawdzonym maszynowo szkieletem kontraktów, bo w tym środowisku nie ma toolchainu Rust/Verus; nie przeprowadzono żadnych benchmarków, więc nie formułuję żadnych porównań wydajności z istniejącymi bibliotekami. Nie sformalizowano: krótszego algorytmu długości 5 (8 mnożeń przez `x⁵−1 = (x−1)Φ₅`), a więc ani dokładnej wartości dla długości 30, ani spakowania rozkładu izotypowego w pojedynczy `NatIso`, ani K-teorii poza opisem wyznacznikowym.

# Summary of changes for run 66807c70-9f29-4487-a063-dde4b9e970ba
I picked up the project where it stood, repaired the one module that did not compile, and extended the development with new, fully proved complexity results. The whole project builds cleanly (`lake build`), contains no `sorry`/`admit`, and the axiom audit in `RequestProject/Main.lean` shows only `propext`, `Classical.choice`, `Quot.sound` for every headline theorem, including all the new ones.

**1. Repaired module (`RequestProject/BilinearLowerBound.lean`).** This file was left in a non-compiling state (a broken linear-independence step and three failed `ring` closures). It now builds, giving the bilinear-algorithm model (`BilinAlg`, `BilinAlg.out`) together with:
- `bilin_lower_bound` — `p` linearly independent bilinear forms require at least `p` products of linear forms;
- `cyclicConv_bilinear_lower_bound` — length-`n` cyclic convolution needs `≥ n` products;
- `conv3_bilinear_optimal` — over M31 the length-3 cyclic convolution has bilinear complexity exactly 3.

**2. New: exact bilinear complexity of cyclic convolution (same file).** `convAlg` (the DFT algorithm) plus `convAlg_correct` give a matching upper bound, so `cyclicConv_bilinear_complexity`: over any field with a primitive `n`-th root of unity in which `n` is invertible, the bilinear complexity of the length-`n` cyclic convolution is **exactly `n`**. Specialised to M31 in `cyclicConv31_M31_bilinear_complexity`: length 31 is exactly 31, and all linear forms of the optimal algorithm are powers of two, i.e. bit rotations.

**3. New: `RequestProject/RaderThirty.lean`.** The sharp extension degree for the length-30 convolution coming out of Rader's reduction: `p^k ≡ 2^(k mod 4) (mod 5)`, hence `30 ∣ p^k − 1 ↔ 4 ∣ k`, hence `exists_primitiveRoot_thirty_ext_iff` (𝔽_{p^k} has a primitive 30-th root of unity iff `4 ∣ k`) and `min_extension_degree_for_thirty` (degree 4 is minimal — the quadratic extension, which suffices for all radix-2 work, does not suffice here).

**4. New: `RequestProject/PolyMul.lean`.** Polynomial multiplication in the bilinear model:
- `polyMulForm_linearIndependent`, `polyMul_lower_bound` — the `m+n+1` coefficient forms are independent, so `≥ m+n+1` products are needed;
- `toomAlg`, `toomAlg_correct` — evaluation at `m+n+1` distinct points and interpolation by the inverse Vandermonde matrix attains it;
- `polyMul_bilinear_complexity`, `polyMul_M31_bilinear_complexity` — the complexity is **exactly `m+n+1`**, over M31 for all degrees with `m+n+1 ≤ p`;
- `karatsuba_bilinear_optimal` — Karatsuba's three multiplications are optimal for two linear polynomials in this model;
- `cyclicToomAlg`, `cyclicConv_bilinear_bounds` — folding modulo `x^n − 1` gives a cyclic-convolution algorithm needing **no root of unity**, so the complexity lies between `n` and `2n−1`; `cyclicConv30_M31_bounds` records the concrete consequence for Rader's length-30 convolution over M31: 59 general multiplications suffice (schoolbook uses 900), at least 30 are necessary.

`RESULTS.md` and `DISCREPANCIES.md` were updated with new sections and trust-table rows, and the open-question entries were re-stated to say precisely what is now settled and what remains open (the exact value for length 30, length-5 short convolutions, and lower bounds in the general straight-line model). The Properties table lists the new results, all marked proved on the basis of a clean sorry-free build.

Unchanged caveats, restated: all cost statements are relative to their explicitly defined models (bilinear algorithms, or the operation-count/straight-line models of the earlier files); `verus/m31_fft.rs` remains an unchecked contract skeleton since no Rust/Verus toolchain is available here; and no benchmarks were run, so no performance comparison with any existing library is claimed.

# Summary of changes for run b12577e2-d1c6-4964-b629-b8fdec3d18be
I completed the remaining in-flight work and extended the development with a new convolution layer. Everything builds sorry-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only, audited by the `#print axioms` block in `RequestProject/Main.lean`).

New in this session:

* `RequestProject/Convolution.lean`
  - `FFT.cyclicConv` — cyclic convolution of n-periodic sequences.
  - `FFT.dft_cyclicConv` — **convolution theorem**: for any ζ with ζⁿ = 1, `DFT(a ⊛ b)_j = DFT(a)_j · DFT(b)_j` (the coordinate form of the algebra isomorphism `F[ℤ/n] ≅ Fⁿ`).
  - `FFT.dft_inv_pointwise_mul` — algorithmic form: for ζ primitive of order n, the inverse transform of the pointwise product of two transforms equals `n · (a ⊛ b)`, i.e. convolution = three transforms + n pointwise products.
  - `FFT.cyclicConv_reverse` — reversing one argument converts a cyclic correlation into a cyclic convolution.
* `RequestProject/RaderConvolution.lean`
  - `FFT.rader31_conv` / `FFT.rader31_conv_M31` — the length-31 DFT equals `a₀` plus a genuine length-30 cyclic convolution of the permuted data against the kernel `m ↦ ζ^(3^m)`; over M31 that kernel consists of powers of two, i.e. bit rotations.
* `RequestProject/M31Basic.lean`
  - `FFT.M31.no_primitiveRoot_thirty` — a second negative structural fact: 5 ∤ p−1, so M31 has no primitive 30-th root of unity. Consequently the length-30 convolution coming out of Rader's reduction cannot itself be evaluated by length-30 transforms over the base field; another scheme is required. This is a concrete constraint any implementation must respect.
* A shared lemma (`ζ^m = ζ^(m mod n)` when `ζⁿ = 1`) was moved into `DFT.lean` so both the Rader and convolution developments use one copy.
* `RESULTS.md` now documents the convolution layer and the new obstruction, and the Properties table has been reconciled: all listed theorems are marked proved on the basis of a clean, sorry-free build (verified by searching the sources for `sorry`), definitions remain as definitions.

Unchanged caveats, restated for accuracy: `verus/m31_fft.rs` is a contract skeleton whose clauses transliterate the Lean theorems, but no Rust/Verus toolchain is available here, so it has not been machine-checked; no benchmarks were run, so no performance comparison with any existing library is claimed; the speculative topological items (operads/associahedra, spectral sequences, Čech cohomology, K-theory beyond the determinant description, classifying spaces) are explicitly listed in `RESULTS.md` as not formalized. All work is committed and pushed.